# The Sharp Finite-Field Nikodym Exponent in Lean

**Authors:** 

Ting-Wei Chao, Zach Hunter, Cosmin Pohoata, Hung-Hsun Yu, Shengtong Zhang.

GPT 5.6 and GPT 6 Astra were used in ideation.

Formalization completed by Fable 5.1 and Grok 4.6 in the Cursor Editor.

This repository is a Lean 4 and Mathlib formalization project for the sharp
power saving in the finite-field Nikodym problem over prime fields.

## The theorems

Let $q$ be a prime power and $d \ge 2$. A set $N \subseteq \mathbb F_q^d$ is a
*Nikodym set* if for every $x \in \mathbb F_q^d$ there is an affine line $\ell$
through $x$ with $\ell \setminus x \subseteq N$. Let $\text{Nik}(d,q)$ be the size of the smallest Nikodym set in $F_q^d$. 

**Lower bound.** For every Nikodym set $N \subseteq \mathbb F_q^d$,

$$
|N| \ge q^d - (8d^2+1) q^{d - 2^{1-d}}.
$$

**Upper bound.** For every $\varepsilon > 0$ and all sufficiently large primes
$q$, there is a Nikodym set $N \subseteq \mathbb F_q^d$ with

$$
|N| \le q^d - q^{d - 2^{1-d} - \varepsilon}.
$$

Together these give $\text{Nik}(d,q) = q^d - q^{d-2^{1-d}+o(1)}$ over all prime fields, resolving the finite field Nikodym problem over prime fields.

## What we are missing

The tight exponent when $q$ is a prime power. Our method could cover the case when the power of $q$ is not too large, but the regime in which the characteristics of $q$ is fixed remains open.

## Writeups

The writeups in docs/ are preliminary and partially AI-generated.

We are currently preparing a detailed, human readable exposition of the proof.

## Lean

For a description of the lean side of the project, see README_lean.md.
