# Hints

## Rule 1

Try using `z3.Length`.
(This can also be done with `z3.Concat` and `z3.AllChar`.)

## Rule 2

Try using `z3.Range`.

## Rule 4

Try using `z3.Union` in addition to some of the constructors
that were used in the previous rules.

## Rule 5

This one is tricky!

I know of at least two ways to do it, but regardless,
you will likely need to make some simplifying assumptions:

- Try limiting the number of digits that occur in the password.
  For example, you could assume the password only contains 3
  characters that are digits.
  Then you can create variables for those digits and add
  specific constraints on them.

- Try limiting the total number of characters in the password.
  For example, you could assume the password is at most 30 characters long.

Either way, you will need to convert either from digits to characters,
or from characters to digits, to get the sum of the digits. Useful functions are `z3.IntToStr`, `z3.CharIsDigit`, and `z3.CharToInt` (see `regex_help.md`).

## Rule 6

Try using `z3.Re`.

## Rule 9

The second tricky one!
As with Rule 5, you will likely need to make some simplifying assumptions:
either limit the number of times a roman numeral occurs in the password,
or limit the total number of characters in the password.

## Rule 10

This one can throw Z3 off if you get unlucky and your Captcha
contains characters which conflict with some of the other rules.
If you run into this issue, try refreshing the Captcha to get an
easier one.
