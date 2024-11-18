MAX_CONSTANTS = 10

# Parse a formula and return the type of formula based on parseOutputs
def parse(fmla):
    # Check if it's a propositional variable
    if fmla in ['p', 'q', 'r', 's']:
        return 6  # 'a proposition'
    
    # Check for negations
    elif fmla.startswith("~"):
        sub_fmla = fmla[1:]
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
            connective = fmla[op_index:op_index+2]  # account for two-character connectives
            rhs_formula = fmla[op_index + 2:-1]
            lhs_type = parse(lhs_formula)
            rhs_type = parse(rhs_formula)
            
            # Check if it's a propositional binary connective
            if lhs_type in [6, 7, 8] and rhs_type in [6, 7, 8]:  # Propositional binary connective
                return 8  # 'a binary connective propositional formula'
            else:
                return 5  # 'a binary connective first order formula'
    
    # Handle quantifiers for FOL formulas
    elif fmla[0] in ['E', 'A'] and len(fmla) > 2:
        quantifier = fmla[0]
        variable = fmla[1]
        if variable in ['x', 'y', 'z', 'w']:
            sub_formula = fmla[2:]
            if parse(sub_formula) in [1, 2, 3, 4, 5]:  # Valid FOL formula after quantifier
                return 3 if quantifier == 'A' else 4  # Universal or Existential quantification
    
    # Check for atoms in FOL formulas
    elif len(fmla) == 6 and fmla[0] in ['P', 'Q', 'R', 'S'] and fmla[1] == '(' and fmla[-1] == ')':
        if fmla[2] in ['x', 'y', 'z', 'w'] and fmla[4] in ['x', 'y', 'z', 'w']:
            return 1  # 'an atom'

    return 0  # 'not a formula'



# Helper function to find the main connective in a binary formula
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

# Return the LHS of a binary connective formula
def lhs(fmla):
    op_index = find_connective_index(fmla)
    return fmla[1:op_index] if op_index else ''

# Return the connective symbol of a binary connective formula
def con(fmla):
    op_index = find_connective_index(fmla)
    return fmla[op_index:op_index+2] if op_index else ''

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    op_index = find_connective_index(fmla)
    return fmla[op_index + 2:-1] if op_index else ''

# Initialize a theory with a single formula
def theory(fmla):
    return {fmla}

# Check for satisfiability
def sat(tableau):
    constant_count = 0
    while tableau:
        branch = tableau.pop()
        new_formulas = set()
        
        for formula in branch:
            parsed = parse(formula)
            
            if parsed == 7:  # Negation of a propositional formula
                sub_formula = formula[1:]
                if sub_formula in branch:
                    branch.remove(sub_formula)
                    branch.remove(formula)
                    continue
            
            elif parsed == 8:  # Propositional binary connective
                op = con(formula)
                if op == "/\\":
                    new_formulas.add(lhs(formula))
                    new_formulas.add(rhs(formula))
                elif op == "\\/":
                    new_branch1 = branch | {lhs(formula)}
                    new_branch2 = branch | {rhs(formula)}
                    tableau.append(new_branch1)
                    tableau.append(new_branch2)
                    continue
                elif op == "=>":
                    new_branch1 = branch | {f"~{lhs(formula)}"}
                    new_branch2 = branch | {rhs(formula)}
                    tableau.append(new_branch1)
                    tableau.append(new_branch2)
                    continue
            
            elif parsed in [3, 4]:  # Universal or Existential quantification
                if parsed == 4:  # Existential quantifier
                    if constant_count >= MAX_CONSTANTS:
                        return 2
                    constant = f'c{constant_count}'
                    constant_count += 1
                    new_formulas.add(rhs(formula).replace(lhs(formula), constant))
                elif parsed == 3:  # Universal quantifier
                    for i in range(constant_count):
                        constant = f'c{i}'
                        new_formulas.add(rhs(formula).replace(lhs(formula), constant))

        # If no contradictions and new formulas are added, extend the branch
        if new_formulas - branch:
            tableau.append(branch | new_formulas)
        elif not any(parse(f) == 7 and f[1:] in branch for f in branch):
            return 1  # Satisfiable
    
    return 0  # Unsatisfiable

#------------------------------------------------------------------------------------------------------------------------------
#                   DO NOT MODIFY THE CODE BELOW. MODIFICATION OF THE CODE BELOW WILL RESULT IN A MARK OF 0!                   :
#------------------------------------------------------------------------------------------------------------------------------

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
