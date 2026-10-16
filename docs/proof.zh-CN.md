# OEIS A386235 的完整数学证明

问题、猜想及常数见 [OEIS A386235](https://oeis.org/A386235)。

以下证明对应仓库中的完整 Lean 形式化。阅读本说明不需要先了解 Lean。

## 1. 定义与主定理

记

$$
a(n)=\operatorname{card}\{(p,q,r)\in\mathbb Z_{>0}^3:p+q+r=n,\ p+11q+13r\text{ 是完全平方数}\}.
$$

三元组有序，不要求 $p\le q\le r$。令

$$
K=\frac{1-66\sqrt{11}+65\sqrt{13}}{180}.
$$

**主定理。** 对所有整数 $n\ge3$，

$$
|a(n)-Kn^{3/2}|\le20\sqrt n.
$$

因此 $a(n)=Kn^{3/2}+O(\sqrt n)$，并且 $a(n)\sim Kn^{3/2}$。

先注意 $\sqrt{11}<10/3$、$\sqrt{13}>18/5$，故

$$
1-66\sqrt{11}+65\sqrt{13}>1-220+234=15>0,
$$

从而 $K>0$。有了显式误差界，再除以 $Kn^{3/2}$ 即得到渐近等价。

## 2. 按平方根精确计数

固定 $n\ge3$，记

$$
N=n-3,\qquad A=n+22,\qquad B=11n-8,\qquad C=13n-14.
$$

这些量满足

$$
1\le A\le B\le C\le13n,\qquad A-6B+5C=0.
$$

由 $p=n-q-r$，平方条件等价于

$$
m^2=n+10q+12r.
$$

取唯一的非负平方根 $m$，令 $q'=q-1$、$r'=r-1$。正整数条件与总和条件成为

$$
q',r'\ge0,\qquad q'+r'\le N,\qquad m^2=A+10q'+12r'.
$$

因此有效平方根必属于有限集合

$$
\mathcal M_n=\{m\in\mathbb Z_{\ge0}:A\le m^2\le C,\ m\equiv n\pmod2\}.
$$

对每个 $m\in\mathcal M_n$，令 $s=(m^2-A)/2$。于是 $s$ 是整数，且 $0\le s\le6N$。要数的是

$$
5q'+6r'=s,\qquad q'+r'\le N.
$$

设 $t=q'+r'$，则反解得到

$$
q'=6t-s,\qquad r'=s-5t,\qquad p=N-t+1.
$$

所以三元组与区间

$$
\frac s6\le t\le\min\left(N,\frac s5\right)
$$

中的整数一一对应。左端不大于右端，因为 $0\le s\le6N$。固定根的精确计数为

$$
c_n(m)=1+\min\left(N,\left\lfloor\frac s5\right\rfloor\right)-\left\lceil\frac s6\right\rceil.
$$

若区间中没有整数，该表达式为零。每个三元组有唯一非负平方根，故不会重复计数，且

$$
a(n)=\sum_{m\in\mathcal M_n}c_n(m).
$$

Lean 中原三元组集合与分层计数的等式由 `original_count_eq_a` 证明；这里不是把某个近似计数当作原序列定义。

## 3. 把计数替换为区间长度

上节实区间的长度为

$$
w_n(m)=\begin{cases}(m^2-A)/60,&m^2\le B,\\(C-m^2)/12,&m^2>B.\end{cases}
$$

对实数 $l\le u$，区间整数个数与长度之差为

$$
\lfloor u\rfloor-\lceil l\rceil+1-(u-l)=1-(u-\lfloor u\rfloor)-(\lceil l\rceil-l).
$$

其绝对值不超过 $1$。因此 $|c_n(m)-w_n(m)|\le1$。记

$$
S_n=\sum_{m\in\mathcal M_n}w_n(m).
$$

因为

$$
\operatorname{card}\mathcal M_n\le\lfloor\sqrt C\rfloor+1\le\sqrt{13n}+1,
$$

求和得到

$$
|a(n)-S_n|\le\sqrt{13n}+1.\tag{1}
$$

这一估计保留了正整数约束和奇偶约束，不需要假设平方根等分布。

## 4. 同奇偶截断二次函数的求和

对 $x\ge1$ 和 $e\in\{0,1\}$，定义

$$
H_e(x)=\sum_{\substack{k\ge0\\(2k+e)^2\le x}}\bigl(x-(2k+e)^2\bigr).
$$

**求和引理。** 有

$$
H_e(x)=\frac{x^{3/2}}3+\frac{1-e}{2}x+E_e(x),\qquad |E_e(x)|\le\sqrt x+1.\tag{2}
$$

**证明。** 令

$$
R=\sqrt x,\qquad L=\left\lfloor\frac{R-e}{2}\right\rfloor+1,\qquad d=2L+e-R.
$$

因 $x\ge1$，有 $L\ge1$；由取整定义，$0<d\le2$。有效指标为 $k=0,\ldots,L-1$，故利用有限平方和公式，

$$
H_e(x)=LR^2-\frac23L(L-1)(2L-1)-2eL(L-1)-Le^2.
$$

将 $2L=R-e+d$ 代入并展开，得到精确恒等式

$$
H_e(x)-\frac{R^3}{3}-\frac{1-e}{2}R^2=R\left(-\frac{d^2}{2}+d-\frac13\right)-\frac{d(d-1)(d-2)}6.
$$

一般展开还出现 $e(e-1)(e-2)/6$，但 $e=0$ 或 $1$，该项为零。在 $0\le d\le2$ 上，

$$
\left|-\frac{d^2}{2}+d-\frac13\right|=\left|\frac16-\frac{(d-1)^2}{2}\right|\le1,
$$

且 $|d(d-1)(d-2)|\le2\cdot1\cdot2=4$。误差因此不超过 $R+2/3\le R+1$，引理得证。

## 5. 边界项的精确抵消

记 $y_+=\max(y,0)$。把 $w_n(m)$ 在根区间外延拓为零，可写为

$$
T_n(m)=\frac{(A-m^2)_+-6(B-m^2)_++5(C-m^2)_+}{60}.
$$

逐段检验：

- $m^2\le A$ 时，常数项由 $A-6B+5C=0$ 抵消，$m^2$ 项由 $1-6+5=0$ 抵消；
- $A\le m^2\le B$ 时，分子为 $m^2-A$；
- $B\le m^2\le C$ 时，分子为 $5(C-m^2)$；
- $m^2\ge C$ 时，三项均为零。

取 $e\equiv n\pmod2$、$e\in\{0,1\}$，在所有非负的同奇偶根 $m=2k+e$ 上求和，得到

$$
S_n=\frac{H_e(A)-6H_e(B)+5H_e(C)}{60}.
$$

令

$$
J_n=\frac{A^{3/2}-6B^{3/2}+5C^{3/2}}{180}.
$$

将式 (2) 代入。潜在的线性边界项恰好为

$$
\frac{1-e}{120}(A-6B+5C)=0.
$$

因此

$$
|S_n-J_n|\le\frac{\sqrt A+6\sqrt B+5\sqrt C+12}{60}\le\frac{\sqrt{13n}+1}{5}\le\sqrt{13n}+1.
$$

结合式 (1)，有

$$
|a(n)-J_n|\le2\sqrt{13n}+2.\tag{3}
$$

这是误差降到 $O(\sqrt n)$ 的关键：三个同奇偶求和的线性边界项精确抵消，而不是分别用 $O(n)$ 估计后再相加。

## 6. 去掉端点的常数平移

先证明一个显式不等式。若 $n\ge0$、$0\le x,y\le13n$ 且 $|x-y|\le D$，则

$$
|x\sqrt x-y\sqrt y|\le8D\sqrt n.\tag{4}
$$

事实上，令 $u=\sqrt x$、$v=\sqrt y$、$R=4\sqrt n$，有 $0\le u,v\le R$，以及

$$
u^2+uv+v^2\le2R(u+v).
$$

利用平方差和立方差的因式分解，

$$
|x\sqrt x-y\sqrt y|=|u-v|(u^2+uv+v^2)\le2R|u-v|(u+v)=2R|x-y|\le8D\sqrt n.
$$

没有用到除法，所以零端点也包括在内。

对 $(A,n)$、$(B,11n)$、$(C,13n)$ 分别使用式 (4)，取 $D=22,8,14$。又

$$
\frac{n^{3/2}-6(11n)^{3/2}+5(13n)^{3/2}}{180}=Kn^{3/2},
$$

因此

$$
|J_n-Kn^{3/2}|\le\frac{8(22+6\cdot8+5\cdot14)}{180}\sqrt n=\frac{56}{9}\sqrt n\le7\sqrt n.
$$

与式 (3) 合并，

$$
|a(n)-Kn^{3/2}|\le2\sqrt{13n}+2+7\sqrt n.
$$

最后用 $\sqrt{13n}\le4\sqrt n$ 和 $1\le\sqrt n$，右端至多为 $17\sqrt n$，当然也不超过 $20\sqrt n$。这证明了所声明的主定理。常数 $20$ 采用了便于形式化的宽松界，不主张最优。

## 7. 与 Lean 结果的对应

所有标识符位于命名空间 `A386235`。

| 数学步骤 | Lean 标识符 |
| --- | --- |
| 原三元组集合等于分层计数 | `original_count_eq_a` |
| 精确根求和公式 | `a_eq_exact_sum` |
| 总取整误差 | `total_rounding_error_sqrt` |
| 截断二次函数求和引理 | `capSum_error` |
| 三个截断二次函数的组合 | `weight_sum_eq_caps` |
| 与平移主项的误差 | `a_sub_J_error` |
| 端点平移不等式 | `power_shift_error` |
| 原序列的显式界 | `original_explicit_error_bound` |
| 原序列的渐近大 O 结论 | `original_asymptotic` |

Lean 验证方法见根目录 README。有限数值检查用于复核计数公式，不承担无限命题的证明。
