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
        elif depth == 1 and i+1 < len(fmla) and fmla[i:i+2] in ['/\\', '\\/', '=>']:
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

def get_new_constant(branch):
    used_constants = set()
    for formula in branch:
        for i in range(len(formula)-1):
            if formula[i:i+2].startswith('c') and formula[i+1].isdigit():
                used_constants.add(int(formula[i+1]))
    
    for i in range(MAX_CONSTANTS):
        if i not in used_constants:
            return f'c{i}'
    return None

def has_contradiction(branch):
    for formula in branch:
        if formula.startswith('~'):
            if formula[1:] in branch:
                return True
        else:
            if '~' + formula in branch:
                return True
    return False

def theory(fmla):
    return {fmla}

def sat(tableau):
    constants_used = 0
    
    while tableau:
        current_branch = tableau.pop()
        
        if has_contradiction(current_branch):
            continue
            
        expandable = False
        for formula in sorted(current_branch):
            formula_type = parse(formula)
            
            # Handle binary connectives
            if formula_type == 8:  # Binary connective
                left = lhs(formula)
                right = rhs(formula)
                conn = con(formula)
            
                if conn == '/\\':  # Conjunction
                    new_branch = current_branch - {formula} | {left, right}
                    tableau.append(new_branch)
                    expandable = True
                    break
                elif conn == '\\/':  # Disjunction
                    tableau.append(current_branch - {formula} | {left})
                    tableau.append(current_branch - {formula} | {right})
                    expandable = True
                    break
                elif conn == '=>':  # Implication
                    tableau.append(current_branch - {formula} | {'~' + left})
                    tableau.append(current_branch - {formula} | {right})
                    expandable = True
                    break
                
            # Handle negations
            elif formula_type == 7:
                subformula = formula[1:]
                sub_type = parse(subformula)
                
                if sub_type == 8:
                    conn = con(subformula)
                    left = lhs(subformula)
                    right = rhs(subformula)
                    
                    if conn == '/\\':
                        tableau.append(current_branch - {formula} | {'~' + left})
                        tableau.append(current_branch - {formula} | {'~' + right})
                    elif conn == '\\/':
                        tableau.append(current_branch - {formula} | {'~' + left, '~' + right})
                    elif conn == '=>':
                        tableau.append(current_branch - {formula} | {left, '~' + right})
                    expandable = True
                    break
                elif sub_type == 7:  # Double negation
                    tableau.append(current_branch - {formula} | {subformula[1:]})
                    expandable = True
                    break
            
            # Handle existential quantifiers
            # Handle universal quantifier
            elif formula_type == 3:
                var = formula[1]
                subformula = formula[2:]
                new_constant = get_new_constant(current_branch)

                if new_constant and constants_used < MAX_CONSTANTS:
                    if formula[2] == 'A' or formula[2] == 'E':
                        # Handle nested quantifiers
                        var2 = formula[3]
                        new_formula = subformula.replace(var, new_constant)
                        new_formula = new_formula[0] + var2 + new_formula[3:]
                    else:
                        new_formula = subformula.replace(var, new_constant)
                        
                    if new_formula not in current_branch:
                        new_branch = current_branch | {new_formula}
                        tableau.append(new_branch)  # Add the new branch back to tableau
                        constants_used += 1
                        expandable = True
                        break

        # Handle existential quantifier
            elif formula_type == 4:
                var = formula[1]
                subformula = formula[2:]
                new_constant = get_new_constant(current_branch)
                
                if new_constant and constants_used < MAX_CONSTANTS:
                    if formula[2] == 'A' or formula[2] == 'E':
                        # Handle nested quantifiers
                        var2 = formula[3]
                        new_formula = subformula.replace(var, new_constant)
                        new_formula = new_formula[0] + var2 + new_formula[3:]
                    else:
                        new_formula = subformula.replace(var, new_constant)
                        
                    if new_formula not in current_branch:
                        new_branch = current_branch | {new_formula}
                        tableau.append(new_branch)  # Add the new branch back to tableau
                        constants_used += 1
                        expandable = True
                        break
        
        if not expandable:
            if not has_contradiction(current_branch):
                if constants_used >= MAX_CONSTANTS:
                    return 2  # Unknown (too many constants needed)
                return 1  # Satisfiable
            continue
    
    return 0  # Unsatisfiable

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





