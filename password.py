"""
The password game

https://neal.fun/password-game/

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

=== Additional requirements ===

This homework is about trying to encode practical constraints
into precise Z3 formulas.
With the exception of rules 5 and 9,
all of your rules should exactly encode the requirements
given by the password game (and no additional restrictions).
For example, if the password is at least 5 characters long,
you shouldn't say that it is exactly 10 characters long,
and you shouldn't hard-code a specific string like "password"
to satisfy the rule.
We may vet your implemention against a correct implementation
of the rule during grading to see if it matches the right set of
strings.

For rules 5 and 9, you won't be able to encode the exact
requirements, but you should come up with a useful stronger
approximation. For example, if the rule is "contains a number",
you could encode that as "contains between 1 and 3 numbers."
But you still shouldn't hard code a specific string like "123"
to satisfy the rule.

=== Grading notes ===

To ensure you get credit, please check that
- python3 password.py runs without errors
- pytest password_test.py runs without errors (for problem 11)
- You do not rename or change the signature of the variable
    p
  or of any of the functions
    rule_0, rule_1, ..., rule_10.
  During grading, these will be checked against a correct implementation
  to see if they match the right set of strings.
  (You don't have to have the exact same implementation as us, but it should be
  equivalent, aside from rules 5 and 9. See the additional requirements above).
- Your answers to problems 12-13 are filled in only in the designated space,
  and the lines "Answer in the Space Below" are not removed.

=== Getting help ===

If you get stuck, take a look at:
- regex_help.md
- hints.md
- [Z3 python documentation](https://z3prover.github.io/api/html/namespacez3py.html)
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
"""
Implement the rules for rounds 1 through 10 of the game.
You will need to play the game to figure out what the rules are!

Similarly to rule 0, your rules will refer
to the password variable `p` and return a Z3 constraint.
"""

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
"""
Combine all the rules and solve the game.
To run, run `python password.py` in the terminal.

This runs the main() function below.
If you have any unimplemented rules, it
will skip after the first rule that is not implemented.
"""

def main():
    solver = z3.Solver()

    try:
        solver.add(rule_0())
        solver.add(rule_1())
        solver.add(rule_2())
        solver.add(rule_3())
        solver.add(rule_4())
        solver.add(rule_5())
        solver.add(rule_6())
        solver.add(rule_7())
        solver.add(rule_8())
        solver.add(rule_9())
        solver.add(rule_10())

    except NotImplementedError:
        print("(Some rules were not implemented)")

    result = solver.check()
    if result == z3.sat:
        print("Solution found")
        print(solver.model())
    elif result == z3.unsat:
        print("No solution found")
    elif result == z3.unknown:
        print("Unknown")
    else:
        assert False, "Unreachable"

    # Uncomment for debugging:
    # print(solver.assertions())

if __name__ == "__main__":
    main()

########################
###    Discussion    ###
########################
"""
Complete the last few questions after you have finished rules 1-10.

11. Are there any of your rules that are redundant?
If so, use Z3 to prove it: show that each redundant rule
is implied by one of the others.
Fill in the test below; it should have an assertion on the output
of Z3 for each redundant rule.
"""

def test_redundant_rules():
    # TODO
    raise NotImplementedError

"""
12. Which of the rules was hardest to encode?
Why do you think it was difficult?
(Give your best guess -- there is no specific right answer.)

# Do not remove this line:
###### Answer in the Space Below ######

#######################################

13. Which of the rules was hardest for Z3 to solve?
Why do you think it was difficult?
(Give your best guess -- there is no specific right answer.)

# Do not remove this line:
###### Answer in the Space Below ######

#######################################
"""
