# The Sharp Finite-Field Nikodym Exponent in Lean

**Authors:** 

Ting-Wei Chao, Zach Hunter, Cosmin Pohoata, Hung-Hsun Hans Yu, Shengtong Zhang.

GPT 5.6 and GPT 6 Astra were used in ideation.

Formalization completed by Fable 5.1 and Grok 4.6 in the Cursor Editor.

This repository is a Lean 4 and Mathlib formalization project for the sharp
power saving in the finite-field Nikodym problem over prime fields.

## The theorems

Let $q$ be a prime power and $d \ge 2$. A set $N \subseteq \mathbb F_q^d$ is a
*Nikodym set* if for every $x \in \mathbb F_q^d$ there is an affine line $\ell$
through $x$ with $\ell \setminus \{x\} \subseteq N$. Let $\text{Nik}(d,q)$ be the size of the smallest Nikodym set in $F_q^d$. 

**Lower bound.** For every Nikodym set $N \subseteq \mathbb F_q^d$,

$$
|N| \ge q^d - (8d^2+1) q^{d - 2^{1-d}}.
$$

**Upper bound.** For every $\varepsilon > 0$ and all sufficiently large primes
$q$, there is a Nikodym set $N \subseteq \mathbb F_q^d$ with

$$
|N| \le q^d - q^{d - 2^{1-d} - \varepsilon}.
$$

Together these give $\text{Nik}(d,q) = q^d - q^{d-2^{1-d}+o(1)}$ over all prime fields, resolving the finite field Nikodym problem over prime fields up to a subpolynomial factor.

## Comparison with prior work

The writeups in `docs/` are preprints; the comparison below with the literature known to us as of September 2026 is our basis for the claims of novelty above.

### Lower bounds

Before this work, for general prime powers $q$ and $d \ge 3$ the best lower
bound was the one inherited from the finite-field Kakeya problem,
$\text{Nik}(d,q) \ge q^d/2^{d-1} + O(q^{d-1})$, from Dvir's polynomial method
[[Dvir09]](https://doi.org/10.1090/S0894-0347-08-00607-3) as sharpened by
Dvir–Kopparty–Saraf–Sudan [[DKSS13]](https://doi.org/10.1137/100783704) and Bukh–Chao
[[BC21]](https://doi.org/10.19086/da.30707) (see [[Tao25]](https://arxiv.org/abs/2511.07721)
for the deduction). Lund, Saraf and Wolf
[[LSW18]](https://doi.org/10.1137/17M1146099) proved
$\text{Nik}(3,q) \ge (0.38 - o(1)) q^3$ (Theorem 3), the first separation
between Nikodym and Kakeya sets, and recorded the folklore conjecture
$\text{Nik}(d,q) \ge (1 - o(1)) q^d$ (their Conjecture 2), which was previously
known only in bounded characteristic, where Guo–Kopparty–Sudan
[[GKS13]](https://doi.org/10.1145/2422436.2422494) give
$q^d - O(q^{(1-\varepsilon)d})$ with $\varepsilon = \varepsilon(d, \text{char})$.
In dimension $2$ the sharp exponent was known: Feng–Li–Shen
[[FLS10]](https://doi.org/10.37236/330) proved
$\text{Nik}(2,q) \ge q^2 - q^{3/2} - q$, sharpened to
$q^2 - q^{3/2} - 1 \le \text{Nik}(2,q)$ in [LSW18, Theorem 26]. Most
recently, Chao and Yu [[CY26]](https://arxiv.org/abs/2601.20851) conjectured
$\text{Nik}(d,q) \ge q^d - C_d q^{d-1/d}$ for $d \ge 3$ (Conjecture 1.1) and
proved it for weak Nikodym sets whose associated line set is "algebraically
spread" (Theorem 1.2).

The lower bound formalized here, $|N| \ge q^d - (8d^2+1) q^{d-2^{1-d}}$, holds
for every finite field $\mathbb F_q$ with no restriction on the characteristic.
It settles [LSW18, Conjecture 2] in the strong form
$\text{Nik}(d,q) = q^d - O_d(q^{d-2^{1-d}})$ for all $q$ and $d \ge 2$, and
for $d = 2$ it recovers the known exponent $3/2$ (with a worse constant).

### Upper bounds

For prime $q$, the upper bounds were much weaker. The random construction
gives $\text{Nik}(d,q) \le q^d - (d-1+o(1)) q^{d-1}\log q$; Tao
[[Tao25]](https://arxiv.org/abs/2511.07721), using ideas from AlphaEvolve and
Deep Think, improved the constant to $(d-2)/\log 2 + 1 + o(1)$ for $d \ge 3$ and odd $q$, and observed
the product construction which gives $q^d - \lfloor d/2 \rfloor q^{d-1/2} + O(q^{d-1}\log q)$
when $q$ is a perfect square. Hunter, Pohoata, Verstraete and Zhang
[[HPVZ26]](https://arxiv.org/abs/2601.19879) then obtained the first polynomial
savings for primes: $\text{Nik}(3,q) \le q^3 - \Omega(q^{2.1167})$ and, for
large $d$, $\text{Nik}(d,q) \le q^d - \Omega_d(q^{d-\varepsilon_d})$ with
$\varepsilon_d \ll 1/\log\log d$ (Theorem 1.10), together with
$\text{Nik}(2,q) \le q^2 - q^{1+c}$ (Theorem 1.11). For $q = q_0^k$ with
$q_0$ prime and $d \ge k \ge 2$, their Theorem 1.8 gives induced point-line
matchings of size $\gg_d q^{d-1/k}$ in $\mathbb F_q^d$, equivalently (by their
Proposition 1.5) weak Nikodym sets with complement $\gg_d q^{d-1/k}$; this is
why [CY26] proposed the exponent $d - 1/d$.

The construction formalized here gives, for all sufficiently large primes $q$,
$\text{Nik}(d,q) \le q^d - q^{d-2^{1-d}-\varepsilon}$. For $d = 3$ this is a
complement of size $q^{2.75 - \varepsilon}$ versus $q^{2.1167}$ in [HPVZ26];
for $d = 2$ it gives $q^2 - q^{3/2-\varepsilon}$, matching the lower bound
$q^2 - q^{3/2} - 1$ up to the $\varepsilon$, where previously only
$q^2 - q^{1+c}$ was known for primes. Since $2^{1-d} < 1/d$ for $d \ge 3$, the
construction also shows that the exponent $d - 1/d$ of
[CY26, Conjecture 1.1] is not the truth over prime fields: the sharp exponent
there is $d - 2^{1-d}$.

Our construction is based on ideas in the work [[C26]](https://arxiv.org/abs/2607.20422), which essentially carried out the construction in $d = 2$.

### Summary for prime $q$, $d \ge 3$


|           | lower bound                                                    | upper bound                                                                                                  |
| --------- | -------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------ |
| before    | $q^d/2^{d-1} + O(q^{d-1})$; $(0.38-o(1))q^3$ for $d=3$ [LSW18] | $q^d - \Omega_d(q^{d-\varepsilon_d})$, $\varepsilon_d \ll 1/\log\log d$; $q^3 - \Omega(q^{2.1167})$ [HPVZ26] |
| this work | $q^d - (8d^2+1) q^{d-2^{1-d}}$ (all prime powers $q$)          | $q^d - q^{d-2^{1-d}-\varepsilon}$ (large primes $q$)                                                         |


### References

- [BC21] B. Bukh, T.-W. Chao, *Sharp density bounds on the finite field Kakeya problem*, Discrete Analysis 2021:26. [doi:10.19086/da.30707](https://doi.org/10.19086/da.30707)
- [C26] C. Pohoata, *The sharp exponent for the minimal distance problem*, arXiv:2607.20422 (2026). [arXiv](https://arxiv.org/abs/2607.20422)
- [CY26] T.-W. Chao, H.-H. H. Yu, *Finite field Nikodym problem for spread line sets*, arXiv:2601.20851 (2026). [arXiv](https://arxiv.org/abs/2601.20851)
- [Dvir09] Z. Dvir, *On the size of Kakeya sets in finite fields*, J. Amer. Math. Soc. 22 (2009), 1093–1097. [doi:10.1090/S0894-0347-08-00607-3](https://doi.org/10.1090/S0894-0347-08-00607-3)
- [DKSS13] Z. Dvir, S. Kopparty, S. Saraf, M. Sudan, *Extensions to the method of multiplicities, with applications to Kakeya sets and mergers*, SIAM J. Comput. 42 (2013), 2305–2328. [doi:10.1137/100783704](https://doi.org/10.1137/100783704), [arXiv:0901.2529](https://arxiv.org/abs/0901.2529)
- [FLS10] C. Feng, L. Li, J. Shen, *Some inequalities in functional analysis, combinatorics, and probability theory*, Electron. J. Combin. 17 (2010), R58. [doi:10.37236/330](https://doi.org/10.37236/330)
- [GKS13] A. Guo, S. Kopparty, M. Sudan, *New affine-invariant codes from lifting*, ITCS 2013, 529–539. [doi:10.1145/2422436.2422494](https://doi.org/10.1145/2422436.2422494)
- [HPVZ26] Z. Hunter, C. Pohoata, J. Verstraete, S. Zhang, *Large point-line matchings and small Nikodym sets*, arXiv:2601.19879 (2026). [arXiv](https://arxiv.org/abs/2601.19879)
- [LSW18] B. Lund, S. Saraf, C. Wolf, *Finite field Kakeya and Nikodym sets in three dimensions*, SIAM J. Discrete Math. 32 (2018), 2836–2849. [doi:10.1137/17M1146099](https://doi.org/10.1137/17M1146099), [arXiv:1609.01048](https://arxiv.org/abs/1609.01048)
- [Tao25] T. Tao, *New Nikodym set constructions over finite fields*, arXiv:2511.07721 (2025). [arXiv](https://arxiv.org/abs/2511.07721)

## What we are missing

The tight exponent when $q$ is a prime power. Our method might be able to cover the case when the power of $q$ is not too large, but the regime in which the characteristics of $q$ is fixed remains open.

## Writeups

The writeups in docs/ are preliminary and partially AI-generated.

We are currently preparing a detailed, human readable exposition of the proof.

## Lean

For a description of the lean side of the project, see README_lean.md.
