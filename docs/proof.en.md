# A proof of the asymptotic formula for OEIS A386235

This is an English exposition of [the Chinese proof](proof.zh-CN.md).
It uses exact finite sums of squares; an Euler-Maclaurin theorem is not needed.

## 1. Definition and theorem

Let

$$
a(n)=\left|\{(p,q,r)\in\mathbb Z_{>0}^3:p+q+r=n,\ 
p+11q+13r\text{ is a perfect square}\}\right|.
$$

The triples are ordered: no condition such as $p\le q\le r$ is imposed.
Set

$$
K=\frac{1-66\sqrt{11}+65\sqrt{13}}{180}.
$$

**Theorem.** For every integer $n\ge3$,

$$
|a(n)-Kn^{3/2}|\le20\sqrt n.
$$

Consequently, $a(n)=Kn^{3/2}+O(\sqrt n)$ and $a(n)\sim Kn^{3/2}$.

Indeed, $\sqrt{11}<10/3$ and $\sqrt{13}>18/5$, so the numerator of $K$
is greater than $1-220+234=15$. In particular, $K>0$. Dividing the
error bound by $Kn^{3/2}$ gives
$|a(n)/(Kn^{3/2})-1|\le20/(Kn)\to0$.

## 2. Exact counting at each square root

Fix $n\ge3$, and put

$$
N=n-3,\qquad A=n+22,\qquad B=11n-8,\qquad C=13n-14.
$$

Then $1\le A\le B\le C\le13n$ and $A-6B+5C=0$.
Eliminating $p$ and setting $q'=q-1$, $r'=r-1$ gives

$$
m^2=A+10q'+12r',\qquad q',r'\ge0,\qquad q'+r'\le N.
$$

Every counted triple has a unique nonnegative square root $m$. Such a
root belongs to

$$
\mathcal M_n=\{m\in\mathbb Z_{\ge0}:A\le m^2\le C,\ m\equiv n\pmod2\}.
$$

For $m\in\mathcal M_n$, let $s=(m^2-A)/2$. This is an integer with
$0\le s\le6N$. Write $t=q'+r'$. The equation $5q'+6r'=s$ yields

$$
q'=6t-s,\qquad r'=s-5t,\qquad p=N-t+1.
$$

Thus admissible triples with this square root are in bijection with the
integers in the nonempty real interval

$$
s/6\le t\le\min(N,s/5).
$$

It follows that their number is

$$
c_n(m)=1+\min\left(N,\left\lfloor s/5\right\rfloor\right)
-\left\lceil s/6\right\rceil,
\qquad
a(n)=\sum_{m\in\mathcal M_n}c_n(m).
$$

If the interval contains no integer, this expression is zero.

## 3. Rounding error

The length of this interval is

$$
w_n(m)=
\begin{cases}
(m^2-A)/60,&m^2\le B,\\
(C-m^2)/12,&m^2>B.
\end{cases}
$$

For any real $l\le u$, the number of integers in $[l,u]$ differs
from $u-l$ by at most one. In fact, the difference is

$$
1-(u-\lfloor u\rfloor)-(\lceil l\rceil-l).
$$

Therefore $|c_n(m)-w_n(m)|\le1$. If
$S_n=\sum_{m\in\mathcal M_n}w_n(m)$, then

$$
|a(n)-S_n|\le|\mathcal M_n|\le\sqrt{13n}+1. \tag{1}
$$

No equidistribution assumption is involved.

## 4. An elementary summation lemma

For $x\ge1$ and $e\in\{0,1\}$, define

$$
H_e(x)=\sum_{\substack{k\ge0\\(2k+e)^2\le x}}
\bigl(x-(2k+e)^2\bigr).
$$

We claim that

$$
H_e(x)=\frac{x^{3/2}}3+\frac{1-e}{2}x+E_e(x),
\qquad |E_e(x)|\le\sqrt x+1. \tag{2}
$$

To prove this, set

$$
R=\sqrt x,\qquad
L=\left\lfloor(R-e)/2\right\rfloor+1,\qquad
d=2L+e-R.
$$

Since $R\ge1$, we have $L\ge1$ and $0<d\le2$.
The valid indices are $k=0,\ldots,L-1$. The elementary formulas for
$\sum k$ and $\sum k^2$ give

$$
H_e(x)=LR^2-\frac23L(L-1)(2L-1)-2eL(L-1)-Le^2.
$$

Substitution of $2L=R-e+d$ and expansion gives

$$
H_e(x)-\frac{R^3}3-\frac{1-e}{2}R^2
=R\left(-\frac{d^2}2+d-\frac13\right)
-\frac{d(d-1)(d-2)}6.
$$

(The general polynomial expansion also contains
$e(e-1)(e-2)/6$, which vanishes here.)
For $0\le d\le2$,

$$
\left|-\frac{d^2}2+d-\frac13\right|
=\left|\frac16-\frac{(d-1)^2}2\right|\le1,
\qquad |d(d-1)(d-2)|\le4.
$$

The error is at most $R+2/3\le R+1$, proving (2).

## 5. Cancellation of the linear boundary terms

Write $y_+=\max(y,0)$. Extending the weight by zero outside its
root interval gives

$$
T_n(m)=\frac{(A-m^2)_+-6(B-m^2)_++5(C-m^2)_+}{60}.
$$

For $m^2\le A$, the numerator is zero because
$A-6B+5C=0$ and $1-6+5=0$. For $A\le m^2\le B$ it is
$m^2-A$, for $B\le m^2\le C$ it is $5(C-m^2)$, and for
$m^2\ge C$ it is zero. Thus $T_n$ is exactly the extended weight.

Let $e\in\{0,1\}$ be congruent to $n$ modulo $2$. Summing over all
nonnegative roots of this parity gives

$$
S_n=\frac{H_e(A)-6H_e(B)+5H_e(C)}{60}.
$$

Set

$$
J_n=\frac{A^{3/2}-6B^{3/2}+5C^{3/2}}{180}.
$$

On applying (2), the linear contribution is exactly

$$
\frac{1-e}{120}(A-6B+5C)=0.
$$

It follows that

$$
|S_n-J_n|
\le\frac{\sqrt A+6\sqrt B+5\sqrt C+12}{60}
\le\frac{\sqrt{13n}+1}{5}
\le\sqrt{13n}+1.
$$

Combining this with (1) yields

$$
|a(n)-J_n|\le2\sqrt{13n}+2. \tag{3}
$$

## 6. Removing the constant shifts at the endpoints

For $n\ge0$, $0\le x,y\le13n$, and $|x-y|\le D$, we have

$$
|x\sqrt x-y\sqrt y|\le8D\sqrt n. \tag{4}
$$

Indeed, put $u=\sqrt x$, $v=\sqrt y$, and $R=4\sqrt n$.
Then $0\le u,v\le R$ and
$u^2+uv+v^2\le2R(u+v)$. Consequently,

$$
|u^3-v^3|
=|u-v|(u^2+uv+v^2)
\le2R|u-v|(u+v)
=2R|x-y|
\le8D\sqrt n.
$$

Apply (4) to $(A,n)$, $(B,11n)$, and $(C,13n)$, with
$D=22,8,14$, respectively. Since

$$
\frac{n^{3/2}-6(11n)^{3/2}+5(13n)^{3/2}}{180}=Kn^{3/2},
$$

we obtain

$$
|J_n-Kn^{3/2}|
\le\frac{8(22+6\cdot8+5\cdot14)}{180}\sqrt n
=\frac{56}{9}\sqrt n\le7\sqrt n.
$$

Together with (3), $\sqrt{13n}\le4\sqrt n$, and
$1\le\sqrt n$, this gives

$$
|a(n)-Kn^{3/2}|
\le2\sqrt{13n}+2+7\sqrt n
\le17\sqrt n
\le20\sqrt n.
$$

This proves the stated theorem. The constant $20$ is deliberately
generous; no optimality is claimed.

## 7. Scope of the Lean source

The accompanying [Lean source](../A386235.lean) contains proofs with
the following names in the namespace `A386235`:

| Mathematical statement | Lean declaration |
| --- | --- |
| Original triple count equals the sum over roots | `original_count_eq_a` |
| Exact finite sum | `a_eq_exact_sum` |
| Summed rounding error | `total_rounding_error_sqrt` |
| Truncated quadratic summation estimate | `capSum_error` |
| Combination of the three truncated sums | `weight_sum_eq_caps` |
| Error relative to the shifted main term | `a_sub_J_error` |
| Endpoint shift estimate | `power_shift_error` |
| Explicit bound for the original triple count | `original_explicit_error_bound` |
| Big-O statement for the original triple count | `original_asymptotic` |
| Positivity of the leading constant | `K_pos` |

The final asymptotic declaration is an `Asymptotics.IsBigO`
statement for the error, not a separately stated limit of the ratio.
The asymptotic equivalence follows mathematically as explained in Section 1.
The sharper intermediate constant $17$ in the exposition is not the
constant stated in the final Lean theorem; that theorem states $20$.

The source has no `sorry` placeholders or user-declared axioms and
includes `#print axioms` commands for auditing its dependencies.
This does not mean that Lean/Mathlib uses no foundational axioms.
A source inspection is distinct from a successful compiler run.
See the [README](../README.md) for the pinned toolchain and verification
commands. Finite Python checks verify sample counts; they do not prove
the infinite theorem.
