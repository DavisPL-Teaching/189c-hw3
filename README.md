# Homework 3: The Password Game

## Due date: TBD

## Overview

[The password game](https://neal.fun/password-game/)

In this homework, we will use Z3 -- in particular,
the Z3 API support for regular expressions --
to implement a solver for the first 10 levels of the password game
(link above).

Before you start, try the password game yourself,
to get a sense of how it works.

As with HW2, you will need to have Z3 installed; see [Homework 0](https://github.com/DavisPL-Teaching/189c-hw0).

As with HW1 and HW2, you will submit your homework through GitHub Classroom.
Clone your copy of the repository, then push your changes to GitHub before the deadline.
Please see [this Piazza post](https://piazza.com/class/lt90i40zrot3ue/post/48) for further instructions.

## Task

Your task is to fill in `password.py` with a Z3 program that solves the first 10 levels of the password game -- when run, your file will print out
a password satisfying all the cosntraints for each of the first 10 levels.
The file contains further instructions.

## RegEx Help

A successful solution will rely on the Z3 API support for regular expressions. We have include a file `regex_help.md` that provides some help with some of the available regular expression operators in Z3 that you may need to use.

## Hints

If you get stuck, take a look at the `hints.md` file for some hints on how to proceed.
