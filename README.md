# Mean Fourier Analysis in Lean

[![.github/workflows/push.yml](https://github.com/YaelDillies/mean-fourier/actions/workflows/push.yml/badge.svg)](https://github.com/YaelDillies/mean-fourier/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/YaelDillies/mean-fourier)

This repository aims at formalising the Fourier theory of almost-periodic functions in Lean 4.

## What are almost-periodic functions?

Almost-periodic functions are a generalisation of periodic functions due to H. Bohr in the 1920s.
A typical example would be $\sin x + \sin(\sqrt 2 x)$, which is almost-periodic but not periodic
since $\sqrt 2$ is irrational.

Like periodic functions, an almost-periodic function has a Fourier series which (roughly) encodes
how the function correlates with linear subspaces.
As such, almost-periodic functions form a natural class of solutions to PDEs.
In additive combinatorics too, naturally occurring functions turn out to be almost-periodic.

There are several near-equivalent definitions of almost-periodic functions in the literature.
We choose the one put forward in
[*Almost periodic functions in a group. I*, J. von Neumann](https://doi.org/10.2307/1989792).
This definition states that a complex-valued function $f$ from a group $G$ is almost-periodic if,
for all $\varepsilon > 0$, $G$ can be covered by a finite number of translates of the set of
$t \in G$ such that $|f(xt^{-1}) - f(x)| \le \varepsilon$ for all $x \in G$.
This definition is very general, as it doesn't require $G$ to be either topological or abelian.
Continuous functions from a compact group are automatically almost-periodic,
so we recover the usual Fourier analysis on compact groups by density arguments.

## What is formalisation/Lean?

Formalisation is the process of transforming some source material,
typically a mathematical textbook or article, into definitions in a target system
consisting of a computer implementation of a logical theory (such as set theory or type theory).

The target system here is [Lean 4](https://lean-lang.org/),
a very modern functional programming language.
On top of Lean is built [Mathlib](https://leanprover-community.github.io/),
a monolithic library of formalised mathematics containing a large part of what is covered
in a standard undergraduate curriculum.
MeanFourier is itself built on top of Mathlib. The goal is to eventually incorporate it in Mathlib.

## Relation to other projects

MeanFourier develops the Fourier analysis of almost-periodic functions (aka mean Fourier analysis),
and obtains the Fourier analysis of continuous functions on compact groups
(aka compact Fourier analysis) as a special case.
This is the maximal generality in which the dual space is equipped with the discrete measure,
which is the crucial property powering Fourier-analytic arguments in additive combinatorics.

[APAP](https://github.com/YaelDillies/LeanAPAP/) is my previous project
formalising one such argument, but developing only the Fourier theory of finite abelian groups
(aka finite Fourier analysis).
MeanFourier is meant as a drop-in replacement of this part of APAP.

Adeles of a number field are locally compact and as such the Fourier theory
of locally compact abelian groups is used as an input to algebraic number theory.
Andrew Yang and I will formalise this generality as part of
[the FLT project](https://github.com/ImperialCollegeLondon/FLT).

Although Fourier analysis of compact groups and locally compact abelian groups both exist
in the mathematical literature, their putative common generalisation,
the Fourier analysis of locally compact groups, doesn't.

## Content

The Lean code is located within the `MeanFourier` folder. Within it, one can find:
* A `Mathlib` subfolder for the **prerequisites** to be upstreamed to mathlib.
  Lemmas that belong in an existing mathlib file `Mathlib.X` are located in `MeanFourier.Mathlib.X`.
  We aim to preserve the property that `MeanFourier.Mathlib.X` only imports `Mathlib.X` and
  files of the form `MeanFourier.Mathlib.Y` where `Mathlib.X` (transitively) imports `Mathlib.Y`.
  Prerequisites that do not belong in any existing mathlib file are placed in subtheory folders.
  See below.

See the [upstreaming dashboard](https://yaeldillies.github.io/mean-fourier/upstreaming) for more information.

## Getting the project

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://lean-lang.org/install/).
Alternatively, click on the button below to open an Ona workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/YaelDillies/mean-fourier)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Contributing

This project is currently not open to contribution.
