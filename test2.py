MAX_CONSTANTS = 10

def parse(fmla):
    # Check if it's a propositional variable
    if fmla in ['p', 'q', 'r', 's']:
        return 6  # 'a proposition'
    
    # Check for negations
    elif fmla.startswith("~"):
        sub_fmla = fmla[1:]
        # Handle double negation
        if sub_fmla.startswith("~"):
            return parse(sub_fmla[1:])
        sub_type = parse(sub_fmla)
        if sub_type in [6, 7, 8]:  # Negation of a propositional formula
            return 7  # 'a negation of a propositional formula'
        elif sub_type in [1, 3, 4, 5]:  # Negation of a FOL formula
            return 2  # 'a negation of a first order logic formula'
    
    # Check for binary connectives
    elif fmla.startswith("(") and fmla.endswith(")"):
        op_index = find_connective_index(fmla)
        if op_index:
            lhs_formula = fmla[1:op_index]
            connective = fmla[op_index:op_index+2]
            rhs_formula = fmla[op_index+2:-1]
            lhs_type = parse(lhs_formula)
            rhs_type = parse(rhs_formula)
            
            if lhs_type in [6, 7, 8] and rhs_type in [6, 7, 8]:
                return 8  # 'a binary connective propositional formula'
            elif lhs_type > 0 and rhs_type > 0:
                return 5  # 'a binary connective first order formula'
    
    # Check for atoms
    elif len(fmla) == 6 and fmla[0] in ['P', 'Q', 'R', 'S'] and fmla[1] == '(' and fmla[-1] == ')':
        if fmla[2] in ['x', 'y', 'z', 'w'] and fmla[4] in ['x', 'y', 'z', 'w']:
            return 1  # 'an atom'

    return 0  # 'not a formula'

def find_connective_index(fmla):
    open_parens = 0
    for i, char in enumerate(fmla):
        if char == '(':
            open_parens += 1
        elif char == ')':
            open_parens -= 1
        elif char in ['/', '\\', '='] and open_parens == 1:
            return i
    return None

def lhs(fmla):
    op_index = find_connective_index(fmla)
    return fmla[1:op_index] if op_index else ''

def con(fmla):
    op_index = find_connective_index(fmla)
    return fmla[op_index:op_index+2] if op_index else ''

def rhs(fmla):
    op_index = find_connective_index(fmla)
    return fmla[op_index+2:-1] if op_index else ''

def theory(fmla):
    return {fmla}

def normalize_formula(fmla):
    """Normalize formula by removing unnecessary parentheses"""
    if fmla.startswith('(') and fmla.endswith(')'):
        # Check if these parentheses are necessary
        open_count = 0
        for i, c in enumerate(fmla[1:-1]):
            if c == '(':
                open_count += 1
            elif c == ')':
                open_count -= 1
            if open_count < 0:  # Found closing parenthesis before matching opening
                return fmla
        if open_count == 0:
            return normalize_formula(fmla[1:-1])
    return fmla

def is_literal(fmla):
    """Check if formula is a literal (proposition or negation of proposition)"""
    if fmla in ['p', 'q', 'r', 's']:
        return True
    if fmla.startswith('~') and fmla[1:] in ['p', 'q', 'r', 's']:
        return True
    return False

def get_complementary(literal):
    """Get the complementary literal"""
    if literal.startswith('~'):
        return literal[1:]
    return f"~{literal}"

def check_contradiction(theory):
    """Check if theory contains complementary literals"""
    normalized_theory = {normalize_formula(f) for f in theory}
    for formula in normalized_theory:
        if is_literal(formula):
            complement = get_complementary(formula)
            if complement in normalized_theory:
                return True
    return False

def expand_formula(formula, theory):
    """Expand a single formula according to tableau rules"""
    formula = normalize_formula(formula)
    if formula.startswith('~'):
        if formula[1:].startswith('~'):
            # Double negation
            return [{normalize_formula(formula[2:])}]
        if formula[1:].startswith('('):
            inner_formula = formula[1:]
            op = con(inner_formula)
            if op == '/\\':  # ~(A ∧ B) → ~A ∨ ~B
                return [{f"~{normalize_formula(lhs(inner_formula))}"}, 
                       {f"~{normalize_formula(rhs(inner_formula))}"}]
            elif op == '\\/':  # ~(A ∨ B) → ~A ∧ ~B
                return [{f"~{normalize_formula(lhs(inner_formula))}", 
                        f"~{normalize_formula(rhs(inner_formula))}"}]
            elif op == '=>':  # ~(A → B) → A ∧ ~B
                return [{normalize_formula(lhs(inner_formula)), 
                        f"~{normalize_formula(rhs(inner_formula))}"}]
    elif formula.startswith('('):
        op = con(formula)
        if op == '/\\':  # A ∧ B
            return [{normalize_formula(lhs(formula)), normalize_formula(rhs(formula))}]
        elif op == '\\/':  # A ∨ B
            return [{normalize_formula(lhs(formula))}, {normalize_formula(rhs(formula))}]
        elif op == '=>':  # A → B
            return [{f"~{normalize_formula(lhs(formula))}"}, {normalize_formula(rhs(formula))}]
    return []

def sat(tableau):
    while tableau:
        current_theory = tableau.pop()
        
        # Check for contradictions
        if check_contradiction(current_theory):
            continue
            
        # Check if all formulas are literals
        all_literals = all(is_literal(normalize_formula(f)) for f in current_theory)
        if all_literals:
            return 1  # Satisfiable
            
        # Expand non-literal formulas
        expanded = False
        for formula in current_theory:
            if not is_literal(normalize_formula(formula)):
                new_branches = expand_formula(formula, current_theory)
                if new_branches:
                    expanded = True
                    remaining_formulas = current_theory - {formula}
                    for branch in new_branches:
                        new_theory = remaining_formulas | branch
                        tableau.append(new_theory)
                break
                
        if not expanded:
            # If we couldn't expand any formula but they're not all literals,
            # something went wrong
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
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line), rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)