"""
The password game

You will implement a series of rules that the
password should satisfy. Each rule is a function
    rule_<number>(s)
that takes a Z3 string variable `s` and returns
a Z3 constraint that the password should satisfy.

To run the code, open a terminal and execute
    python3 password.py

At the bottom of the file, all of these rules
are combined for you and passed into the solver.

To simplify the problem, we will assume that the
password is ASCII-only. The rule `rule_0` is written for you,
and enforces this constraint.

We also provide two helper functions:
- `regex_all()` returns a Z3 regex that matches any string.
- `regex_containing(r)` returns a Z3 regex that matches any string containing a match for regex `r` somewhere in the middle.

Stuck?

If you get stuck, take a look at `regex_help.md`
for what RegEx operations are available in Z3.
And take a look at `hints.md` for some hints
on some of the harder rules.
You can always ask on Piazza for help!
"""

import z3

p = z3.String("password")

##########################
###  Helper functions  ###
##########################

def ReFull():
    return z3.Full(z3.ReSort(z3.StringSort()))

def ReContaining(r):
    return z3.Concat(
        ReFull(),
        r,
        ReFull(),
    )

def rule_0():
    # Simplifying assumption: password is ASCII only
    return z3.InRe(p, z3.Star(z3.Range(" ", "~")))

#########################
###   Password Rules  ###
#########################
# Implement the rules for rounds 1 through 10 of the game.
# You will need to play the game to figure out what the rules are!
# https://neal.fun/password-game/

# Similarly to rule 0, your rules will refer
# to the password variable `p` and return a Z3 constraint.

def rule_1():
    # TODO
    raise NotImplementedError

def rule_2():
    # TODO
    raise NotImplementedError

def rule_3():
    # TODO
    raise NotImplementedError

def rule_4():
    # TODO
    raise NotImplementedError

def rule_5():
    # TODO
    raise NotImplementedError

def rule_6():
    # TODO
    raise NotImplementedError

def rule_7():
    # TODO
    raise NotImplementedError

def rule_8():
    # TODO
    raise NotImplementedError

def rule_9():
    # TODO
    raise NotImplementedError

def rule_10():
    # TODO
    raise NotImplementedError

########################
###    Entrypoint    ###
########################
# Combine all the rules and solve the game.
# Uncomment each rule as you implement it.
# To run, run `python password.py` in the terminal.

solver = z3.Solver()
solver.add(rule_0())

# Uncomment each rule as you implement it
# solver.add(rule_1())
# solver.add(rule_2(p))
# solver.add(rule_3(p))
# solver.add(rule_4(p))
# solver.add(rule_5(p))
# solver.add(rule_6(p))
# solver.add(rule_7(p))
# solver.add(rule_8(p))
# solver.add(rule_9(p))
# solver.add(rule_10(p))

# Function to print the result of the solver
def print_result(solver):
    result = solver.check()
    if result == z3.sat:
        print(solver.model())
    elif result == z3.unsat:
        print("No solution found")
    elif result == z3.unknown:
        print("Unknown")
    else:
        assert False, "Unreachable"

# Get the solution
print_result(solver)

# This may be useful for debugging:
# print(solver.assertions())
