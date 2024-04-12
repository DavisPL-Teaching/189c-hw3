# RegEx help

The full Z3 Python API documentation can be found
[here](https://z3prover.github.io/api/html/namespacez3py.html).
Here are a few of the key regular expression operators that you will need:

- `z3.Full` - matches any character.
    For technical reasons, it has to be passed a single argument, which is the "sort" (or type) of the characters that it matches. For this reason we provide a helper funcion ReFull which does this for you.

- `z3.Re`

- `z3.InRe`

- `z3.Length`

- `z3.Range`

- `z3.Concat`

- `z3.Union`

- `z3.Star`

- `z3.Plus`

- `z3.IntToStr`
