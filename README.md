# OEIS A386235

Define

$$
a(n)=\left|\{(p,q,r)\in\mathbb Z_{>0}^3:p+q+r=n,\ p+11q+13r\text{ is a square}\}\right|.
$$

Let

$$
K=\frac{1-66\sqrt{11}+65\sqrt{13}}{180}.
$$

For every integer $n\ge3$,

$$
|a(n)-Kn^{3/2}|\le20\sqrt n.
$$

Consequently, $a(n)=Kn^{3/2}+O(\sqrt n)$ and $a(n)\sim Kn^{3/2}$.

## Proof

- [Mathematical proof (English)](docs/proof.en.md)
- [Mathematical proof (Chinese)](docs/proof.zh-CN.md)
- [Lean formalization](A386235.lean)
- [Sequence and conjecture](https://oeis.org/A386235)

## Verification

Lean 4.19.0; Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
bash scripts/verify_lean.sh
python3 scripts/check_counts.py
```

The Lean source states and proves the bound for the original set of positive ordered triples in `original_explicit_error_bound`, proves the Big-O error statement in `original_asymptotic`, and proves `K_pos`. The asymptotic equivalence follows from the bound and positivity; it is not a separately stated ratio-limit theorem in the source.

The file contains no `sorry` placeholders or user-declared axioms and includes `#print axioms` dependency-audit commands. This does not assert the absence of Lean/Mathlib foundational axioms. Source inspection, a successful Lean compiler run, and OEIS editorial approval are separate matters.

The Python script compares the exact summation formula with direct enumeration for $3\le n\le300$, then checks selected sequence values. Finite checks do not prove the asymptotic theorem.
