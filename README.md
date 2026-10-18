# Weil classes on non-split abelian sixfolds: code

Code for the computations in the note *Algebraicity of Weil classes on non-split abelian sixfolds of Weil type over Q(√−3) with Hermitian determinant −2*. The note and its companion are on [hippe.fi/research/ai-driven](https://hippe.fi/research/ai-driven/). Each script reproduces the numbers of the statement listed next to it.

| Script | Reproduces |
|---|---|
| `tuple_in_G32.g` | Section 3: G₃₂, built from four reflections of order 3, has order 155520; the tuple γ of Appendix B lies in it, generates it and has product 1; γ₁, …, γ₁₂ are reflections of order 3 in the two classes of size 40, of determinant ζ² exactly for i ∈ {2, 3, 4, 7, 8, 12}, and γ₁₃ is an involution of determinant 1 with rk(γ₁₃ − 1) = 2 in the class of size 90 (Appendix A) |
| `hermitian_form.g` | Proposition 3.2: the commutant of γ consists of scalars; the parabolic cocycles, the coboundaries and H¹_par have dimensions 10, 4 and 6; the sesquilinear forms invariant under the matrices of 67 braids, each checked to fix γ and each matrix different from 1, form a line over K, spanned by a Hermitian form of signature (3,3) and, in the basis of the script, determinant −128 = −2·8² (Appendix A) |
| `dehn_twists.g` | (6.6): for the four trivial clusters σ_j² fixes γ and acts unipotently on H¹_par; the logarithms N have rank 1 and span a space of dimension 3 over K, with the single relation N₍₆,₇₎ = N₍₈,₉₎ (Appendix A) |
| `cluster_3_4.g` | Sections 6.1 and 6.3: γ₁γ₂ = γ₆γ₇ = γ₈γ₉ = γ₁₁γ₁₂ = 1, γ₃γ₄ has order 6 and the eight monodromies on P₀ commute; rk(γ₃ − 1) = rk(γ₄ − 1) = 1 and dim Fix⟨γ₃, γ₄⟩ = 2, also for the inverse transposes, and Fix(γ₃γ₄) ∩ (Im(γ₃ − 1) + Im(γ₄ − 1)) = 0 (Appendix A) |
| `certificate.py` | Proposition 6.8, (6.9): the 9×9 minor (2.6207710… − 2.9287922… i)·10⁻²⁹ ± 6·10⁻¹⁰⁶ in ball arithmetic, after the 18×18 constraint minors for the two types of forms and the 3×3 minor of the node columns (Appendix A) |
| `subcovers.g` | Section 5.1 and Table 2: Z(G) is cyclic of order 6 and fourteen irreducible characters have the central character of ρ, with their degrees, dim M_{ρ_k} and χ_{ρ_k}(γ₁); the subgroups H ⊇ Z(G) up to conjugacy and the pairs (H, ψ), each with m, r, g(C/H), the exponents and v_{H,ψ}; writes `subcovers.out` (Appendix A) |
| `subcovers_double_cosets.g` | Proposition 5.2: the pairs (H, ψ) with \|H\| among the eleven orders of Table 1, by a second method (ψ from the abelianization of H, v_{H,ψ} from class sums, the exponents and g(C/H) from double cosets); writes `subcovers_double_cosets.out` (Appendix A) |
| `relation.py` | Proposition 5.2, Tables 1 and 2: every entry of Tables 1 and 2, the relation (5.3), the identity (5.4), Σ c_j d_j = 28374 − 28368 = 6 and the full pairing of the exponents of every ψ_j^t; the eleven pairs again in the second enumeration, with the same exponents and the relation; run after the two scripts above (Appendix A) |

The tuple γ = (γ₁, …, γ₁₃) of Appendix B is in `tuple.g`, which the GAP scripts and `certificate.py` read.

The note and this code were produced by large language models; the note's introduction states how, and what has and has not been checked.

## Running

```
git clone https://github.com/ahippelainen/weil-nonsplit-abelian-sixfolds-public
cd weil-nonsplit-abelian-sixfolds-public
```

The `.g` files need [GAP](https://www.gap-system.org) 4.16.1 with its required packages, from the release tarballs `gap-4.16.1-core.tar.gz` and `packages-required-v4.16.1.tar.gz` on the GAP download page. From this directory:

```
gap -A -q tuple_in_G32.g
```

and likewise for the other `.g` files. Each script prints its numbers and asserts the statements listed above; a failed check stops it with `Error, Assertion failure` in GAP and `AssertionError` in Python.

The `.py` files need Python 3.12 with the versions in `requirements.txt`:

```
pip install -r requirements.txt
python certificate.py
python relation.py
```

## Licence

MIT, see `LICENSE`.
