MAX_CONSTANTS = 10

def parse(fmla):
    # Check if it's a propositional variable
    if fmla in ['p', 'q', 'r', 's']:
        return 6
    
    # Check for negations
    if fmla.startswith("~"):
        sub_fmla = fmla[1:]
        sub_type = parse(sub_fmla)
        if sub_type in [6, 7, 8]:
            return 7
        elif sub_type in [1, 3, 4, 5]:
            return 2
    
    # Check for binary connectives
    if fmla.startswith("(") and fmla.endswith(")"):
        op_index = find_connective_index(fmla)
        if op_index:
            lhs_formula = fmla[1:op_index]
            rhs_formula = fmla[op_index + 2:-1]
            lhs_type = parse(lhs_formula)
            rhs_type = parse(rhs_formula)
            
            if lhs_type in [6, 7, 8] and rhs_type in [6, 7, 8]:
                return 8
            elif lhs_type != 0 and rhs_type != 0:
                return 5
    
    # Handle quantifiers
    if len(fmla) > 2 and fmla[0] in ['E', 'A']:
        variable = fmla[1]
        if variable in ['x', 'y', 'z', 'w']:
            sub_formula = fmla[2:]
            sub_type = parse(sub_formula)
            if sub_type in [1, 2, 3, 4, 5]:
                return 3 if fmla[0] == 'A' else 4
    
    # Check for atoms
    if (len(fmla) == 6 and fmla[0] in ['P', 'Q', 'R', 'S'] and 
        fmla[1] == '(' and fmla[-1] == ')' and
        fmla[2] in ['x', 'y', 'z', 'w'] and fmla[4] in ['x', 'y', 'z', 'w'] and
        fmla[3] == ','):
        return 1
    
    return 0

def find_connective_index(fmla):
    depth = 0
    for i in range(len(fmla)):
        if fmla[i] == '(':
            depth += 1
        elif fmla[i] == ')':
            depth -= 1
        elif depth == 1 and fmla[i:i+2] in ['/\\', '\\/', '=>']:
            return i
    return None

def lhs(fmla):
    op_index = find_connective_index(fmla)
    return fmla[1:op_index] if op_index else ''

def con(fmla):
    op_index = find_connective_index(fmla)
    return fmla[op_index:op_index + 2] if op_index else ''

def rhs(fmla):
    op_index = find_connective_index(fmla)
    return fmla[op_index + 2:-1] if op_index else ''

def theory(fmla):
    return {fmla}

def has_contradiction(branch):
    # Check direct contradictions
    for formula in branch:
        if formula.startswith('~') and formula[1:] in branch:
            return True
        elif '~' + formula in branch:
            return True
    
    # Check for quantified contradictions
    predicates = {}
    for formula in branch:
        if len(formula) == 6 and formula[0] in ['P', 'Q', 'R', 'S']:
            pred = formula[0]
            args = (formula[2], formula[4])
            if pred not in predicates:
                predicates[pred] = []
            predicates[pred].append((args, True))
        elif len(formula) == 7 and formula[0] == '~' and formula[1] in ['P', 'Q', 'R', 'S']:
            pred = formula[1]
            args = (formula[3], formula[5])
            if pred not in predicates:
                predicates[pred] = []
            predicates[pred].append((args, False))
    
    # Check if same predicate with same arguments has both positive and negative occurrences
    for pred_list in predicates.values():
        for i, (args1, pos1) in enumerate(pred_list):
            for args2, pos2 in pred_list[i+1:]:
                if args1 == args2 and pos1 != pos2:
                    return True
    
    return False

def get_constants(branch):
    constants = set()
    next_const = 0
    for formula in branch:
        for i in range(MAX_CONSTANTS):
            const = f'c{i}'
            if const in formula:
                constants.add(const)
                next_const = max(next_const, i + 1)
    return constants, next_const

def expand_universal(formula, current_branch):
    var = formula[1]
    subformula = formula[2:]
    constants, next_const = get_constants(current_branch)
    
    # If no constants exist, create one
    if not constants:
        new_formula = subformula.replace(var, 'c0')
        return {new_formula}  # Don't keep universal formula to prevent infinite loops
    
    # Apply to all existing constants
    new_formulas = set()
    for const in constants:
        new_formula = subformula.replace(var, const)
        new_formulas.add(new_formula)
    
    # Add one new constant instantiation if needed
    if next_const < MAX_CONSTANTS and len(constants) < MAX_CONSTANTS:
        new_const = f'c{next_const}'
        new_formula = subformula.replace(var, new_const)
        new_formulas.add(new_formula)
    
    return new_formulas

def expand_existential(formula, current_branch):
    var = formula[1]
    subformula = formula[2:]
    _, next_const = get_constants(current_branch)
    
    # Create new constant for existential quantifier if possible
    if next_const < MAX_CONSTANTS:
        new_const = f'c{next_const}'
        new_formula = subformula.replace(var, new_const)
        return {new_formula}
    
    return set()

def sat(tableau):
    visited_states = set()  # Track visited branch states to prevent loops
    
    while tableau:
        current_branch = tableau.pop()
        branch_state = frozenset(current_branch)
        
        # Skip if we've seen this branch state before
        if branch_state in visited_states:
            continue
        visited_states.add(branch_state)
        
        # Check for contradictions
        if has_contradiction(current_branch):
            continue
            
        # Find formulas that need expansion
        expandable = False
        for formula in sorted(current_branch):  # Sort for deterministic processing
            formula_type = parse(formula)
            
            # Handle propositional connectives
            if formula_type == 8:  # Binary connective
                left = lhs(formula)
                right = rhs(formula)
                conn = con(formula)
                
                if conn == '/\\':
                    tableau.append(current_branch - {formula} | {left, right})
                elif conn == '\\/':
                    tableau.append(current_branch - {formula} | {left})
                    tableau.append(current_branch - {formula} | {right})
                elif conn == '=>':
                    tableau.append(current_branch - {formula} | {'~' + left})
                    tableau.append(current_branch - {formula} | {right})
                expandable = True
                break
                
            # Handle negations
            elif formula_type == 7:
                if formula.startswith('~'):
                    subformula = formula[1:]
                    sub_type = parse(subformula)
                    
                    if sub_type == 8:  # Negation of binary connective
                        conn = con(subformula)
                        left = lhs(subformula)
                        right = rhs(subformula)
                        
                        if conn == '=>':  # ~(p => q) ≡ p /\ ~q
                            tableau.append(current_branch - {formula} | {left, '~' + right})
                            expandable = True
                            break
                        elif conn == '/\\':  # ~(p /\ q) ≡ ~p \/ ~q
                            tableau.append(current_branch - {formula} | {'~' + left})
                            tableau.append(current_branch - {formula} | {'~' + right})
                            expandable = True
                            break
                        elif conn == '\\/':  # ~(p \/ q) ≡ ~p /\ ~q
                            tableau.append(current_branch - {formula} | {'~' + left, '~' + right})
                            expandable = True
                            break
            
            # Handle quantifiers
            elif formula_type == 3:  # Universal
                new_formulas = expand_universal(formula, current_branch)
                if new_formulas:  # Only expand if new formulas would be added
                    new_branch = (current_branch - {formula})  # Remove the universal formula
                    if new_formulas - new_branch:  # Only if we have new formulas
                        tableau.append(new_branch | new_formulas)
                        expandable = True
                        break
            
            elif formula_type == 4:  # Existential
                new_formulas = expand_existential(formula, current_branch)
                if new_formulas:
                    tableau.append(current_branch - {formula} | new_formulas)
                    expandable = True
                    break
        
        # If no expansions were possible and no contradictions,
        # we've found a satisfiable branch
        if not expandable and not has_contradiction(current_branch):
            return 1
    
    # If we've exhausted all branches and found no satisfiable ones
    return 0
#------------------------------------------------------------------------------------------------------------------------------:
#                   DO NOT MODIFY THE CODE BELOW. MODIFICATION OF THE CODE BELOW WILL RESULT IN A MARK OF 0!                   :
#------------------------------------------------------------------------------------------------------------------------------:

f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']

firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5, 8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line), rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
