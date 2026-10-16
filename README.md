# OEIS A386235

Define

$$a(n)=\#\{(p,q,r)\in\mathbb Z_{>0}^3:p+q+r=n,\ p+11q+13r\text{ is a square}\}.$$

Let

$$K=\frac{1-66\sqrt{11}+65\sqrt{13}}{180}.$$

For every integer $n\ge3$,

$$|a(n)-Kn^{3/2}|\le20\sqrt n.$$

Consequently, $a(n)=Kn^{3/2}+O(\sqrt n)$ and $a(n)\sim Kn^{3/2}$.

## Proof

- [Mathematical proof](docs/proof.zh-CN.md)
- [Lean formalization](A386235.lean)
- [Sequence and conjecture](https://oeis.org/A386235)

## Verification

Lean 4.19.0; Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
bash scripts/verify_lean.sh
python3 scripts/check_counts.py
```

The Python script compares the exact summation formula with direct enumeration for $3\le n\le300$, then checks selected sequence values. Finite checks do not prove the asymptotic theorem.
