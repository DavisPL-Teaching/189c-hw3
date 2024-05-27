"""
The password game

https://neal.fun/password-game/

You will implement a series of rules that the
password should satisfy. Each rule is a function

    rule_<number>(password)

that takes a Z3 string variable `password` and returns
a Z3 formula that the password should satisfy.

To run the code, open a terminal and execute

    python3 password.py

The code should print out a solution like this:

    [password = "abc"]

which you can copy and paste into the password game to
see if it satisfies all the rules so far.

=== Additional requirements ===

To simplify the problem, we will assume that the
password is ASCII-only. The rule `rule_0` is written for you,
and it enforces this constraint.

With the exceptions listed below (in rules 5, 6, 8, and 9),
all of the other rules should exactly encode the requirements
given by the password game -- with no additional restrictions.
For example, if the password is at least 5 characters long,
you shouldn't say that it is exactly 10 characters long,
and you shouldn't hard-code a specific string like "password"
to satisfy the rule.
We will be checking your implemention against a correct implementation
of the rule during grading to see if it matches the right set of
strings.

For rules 5 and 9: you won't be able to encode the exact
requirements, but you should come up with a useful stronger
requirement. For example, if the rule is "contains a number",
you could encode that as "contains exactly 1, 2, or 3 numbers."
But you still shouldn't hard code a specific string like "123"
to satisfy the rule.

For rules 6 and 8: the password game online accepts both case-insensitive
and case-sensitive versions of the rule. You may interpret this rule
however you prefer, but you should be consistent with one of the following
four conventions:
1. All lowercase: Just assume the part of the password that is being checked
   is all lowercase
2. All uppercase: Just assume the part of the password that is being checked
    is all uppercase
3. Case-insensitive: Assume the part of the password that is being checked
    can be any mix of uppercase and lowercase
4. First letter uppercase: Assume the first letter of the part of the password
    being checked is uppercase, and the rest is lowercase.

Finally, Z3 may start to slow down once all the rules are added!
Be patient -- the code may take a couple of minutes to run.

=== Grading notes ===

To ensure you get credit, please be sure that:
- python3 password.py runs without errors
- You do not rename or change the signature of any of the functions
      rule_0, rule_1, ..., rule_10.
  During grading, these will be checked against a correct implementation
  to see if they match the right set of strings.
  (You don't have to have the exact same implementation as us, but it should be
  equivalent, aside from rules 5 and 9. See the additional requirements above).
- pytest password_test.py runs with a single non-skipped test (for problem 11)
- problem 11 has one assertion for every redundant rule (make sure it is exhaustive)
- Your answers to problems 12-13 are filled in only in the designated space,
  between the marker lines "Answer Q" and "End of Answer"
- Running time is at most 10 minutes for python3 password.py
- Running time is at most 5 minutes for pytest password_test.py

=== Getting help ===

If you get stuck, take a look at:
- regex_help.md
- ascii_table.txt
- hints.md
- [Z3 python documentation](https://z3prover.github.io/api/html/namespacez3py.html)
"""

import z3

##########################
###  Helper functions  ###
##########################
# These are provided for you -- you may find them useful.

def ReFull():
    """
    Returns a Z3 regex that matches all strings.
    """
    return z3.Full(z3.ReSort(z3.StringSort()))

def ReContaining(r):
    """
    Returns a Z3 regex that matches any string containing a match for regex `r` somewhere in the middle.
    For example,

        ReContaining(z3.Range("a", "z"))

    will match any string containing a lowercase letter.
    """
    return z3.Concat(
        ReFull(),
        r,
        ReFull(),
    )

#########################
###   Password Rules  ###
#########################
"""
Implement the rules for rounds 1 through 10 of the game.
You will need to play the game to figure out what the rules are!

Similarly to rule 0, your rules will refer
to the password variable `password` and return a Z3 formula.
Rule 1 can be done without regular expressions.
For the rest, you can use `z3.InRe(password, R)` to assert that the
password matches a regular expression `R`.
"""

def rule_0(password):
    """
    password: a `z3.String` variable representing the password
    returns: a Z3 formula that the password should satisfy
    """
    # The password consists of only ASCII characters.
    return z3.InRe(password, z3.Star(z3.Range(" ", "~")))

def rule_1(password):
    # TODO
    raise NotImplementedError

def rule_2(password):
    # TODO
    raise NotImplementedError

def rule_3(password):
    # TODO
    raise NotImplementedError

def rule_4(password):
    # TODO
    raise NotImplementedError

def rule_5(password):
    # TODO
    raise NotImplementedError

def rule_6(password):
    # TODO
    raise NotImplementedError

def rule_7(password):
    # TODO
    raise NotImplementedError

def rule_8(password):
    # TODO
    raise NotImplementedError

def rule_9(password):
    # TODO
    raise NotImplementedError

def rule_10(password):
    # TODO
    raise NotImplementedError

########################
###    Entrypoint    ###
########################
"""
You shouldn't need to modify this part.
It combines all the rules to solve the game.
To run, run `python3 password.py` in the terminal.

If you have any unimplemented rules, it
will skip after the first rule that is not implemented.
"""

def main():
    solver = z3.Solver()

    password = z3.String("password")

    rules = [rule_0, rule_1, rule_2, rule_3, rule_4, rule_5, rule_6, rule_7, rule_8, rule_9, rule_10]
    try:
        for (i, rule) in enumerate(rules):
            solver.add(rule(password))
            print(f"Rule {i}: added")

    except NotImplementedError:
        print(f"Rule {i}: not implemented (additional rules skipped)")

    print("Solving...")
    print("")
    result = solver.check()
    if result == z3.sat:
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
Complete the last three questions after you have finished rules 1-10.

11. How many of your rules are redundant?
By "redundant", we mean that the rule is implied by one of the
other rules.

For each rule that is redundant, use Z3 to prove it:
show that the redundant rule
is implied by one of the others.
Many of these implications are intractable. So, it is enough to show it
for a certain bound on the password length, e.g., 20 characters.
If that's still intractable, you can comment out the case and add
a comment that it's true, but Z3 is not able to prove it.

Fill in the test below; it should have one assertion
for each redundant rule.
Remember to unskip the test to get credit!

Time bound: the test should run in under 5 minutes.
"""

import pytest

@pytest.mark.skip
def test_redundant_rules():
    # TODO
    raise NotImplementedError

"""
12. Which of the rules was hardest to encode?
Why do you think it was difficult?
(Give your best guess -- there is no specific right answer.)

# Do not remove this line:
###### Answer Q12 Below ######

###### End of Answer ######

13. Which of the rules was hardest for Z3 to solve?
Why do you think it was difficult?
(Give your best guess -- there is no specific right answer.)

# Do not remove this line:
###### Answer Q13 Below ######

###### End of Answer ######
"""
