# Magic positivity for parking-function polytopes through dimension ten

**25 November 2026.** Srijit Iyer. This work was AI-assisted.

For a positive integer vector $\mathbf b=(b_1,\ldots,b_n)$, let $\mathfrak X_n(\mathbf b)$ be the convex hull of the words of positive integers whose sorted entries are bounded by the partial sums of $\mathbf b$. Hill, Luo, Trinh and Vindas-Meléndez conjectured that its Ehrhart polynomial $E(t)$ has a nonnegative expansion in the basis $t^i(t+1)^{n-i}$ for every $n\ge3$. This is their Conjecture 8.1. Their Theorem 7.2 covers the two-parameter family $\mathbf b=(a,b,\ldots,b)$. [Original paper](https://arxiv.org/html/2607.15503v1#S8)

**Theorem.** For every $3\le n\le10$ and every positive integer parameter vector $\mathbf b$, the polytope $\mathfrak X_n(\mathbf b)$ is magic positive. More strongly, write $b_i=1+x_i$. Each magic coefficient is a polynomial in the $x_i$ with nonnegative rational coefficients.

In every dimension $n\ge3$, the first nonconstant magic coefficient has the following closed form, where $H_s=\sum_{i=1}^s 1/i$.

$$\mu_1=\frac{n(3n-7)}4+n x_1+\sum_{j=2}^n (n-j+1)\bigl(1+H_n-H_{n-j+1}\bigr)x_j.$$

In particular, $\mu_1$ is strictly positive throughout the conjecture's parameter domain. Its sharp minimum is $n(3n-7)/4$, attained only at $\mathbf b=(1,\ldots,1)$.

## Proof through dimension ten

Use the lattice-point polynomial $L_n$ of Proposition 5.4. Begin with $L_1(b_1)=b_1$. Compute $L_n$ from $L_{n-1}$ by the slice recurrence in Theorem 4.1. Its first block contributes $b_1L_{n-1}(b_1+b_2,b_3,\ldots,b_n)$. In each middle block the affected monomial factors have the form $(A+B-r)^a(C+r)^b$, summed over $1\le r\le B$. The last block uses the same form with $b=0$. Expanding the powers and summing powers of $r$ carries out the recurrence over rational polynomials. For every $k\ge0$, the power-sum polynomial $S_k(B)$ is computed by the telescoping relation

$$ (k+1) S_k(B) = (B+1)^{k+1}-1-\sum_{i=0}^{k-1}\binom{k+1}i S_i(B). $$

Corollary 5.6 gives $E(t)=L_n(1+tx_1,t(1+x_2),\ldots,t(1+x_n))$. Replace $t^d$ in this expression by $u^d(1-u)^{n-d}$ to get the magic transform $(1-u)^n E(u/(1-u))$. Exact expansion in $u,x_1,\ldots,x_n$ gives only positive coefficients on its nonzero monomials. [Lattice-slice recurrence](https://arxiv.org/html/2607.15503v1#S4) · [Dilation and polynomiality](https://arxiv.org/html/2607.15503v1#S5.SS1)

| $n$ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Nonzero monomials | 34 | 126 | 462 | 1,716 | 6,435 | 24,310 | 92,378 | 352,716 |

Since the $x_i$ are nonnegative, this gives the desired positivity for all parameter vectors in these dimensions. Each lattice slice and the final polynomial are computed symbolically, so there is no bound on the parameter values. Conjecture 8.1 in arbitrary dimension remains open in this work.

## The first magic coefficient in every dimension

Let $e_1=[t]E(t)$. The constant term in the magic expansion is 1, so $\mu_1=e_1-n$. In the formula of Theorem 5.9, a contribution to $[t]$ can come only from a multiset supported on a single subset. A size-$s$ subset can occur $1,\ldots,s$ times, and its contribution at multiplicity $k$ is $w_s/k$. Thus

$$ e_1=\sum_{s=1}^n \binom ns H_s w_s. $$

The coefficient of $x_1$ is $n$. The constant term comes from $w_2=1$ when all the $x_i$ vanish, and equals $\binom n2 H_2-n=n(3n-7)/4$. For $j\ge2$, the coefficient of $x_j$ is

$$\sum_{r=0}^{n-j}(-1)^r\binom n{j+r}\binom{j+r-2}{j-2} H_{j+r}.$$

The product of binomial coefficients is $\binom nj j(j-1)\binom{n-j}r/((j+r)(j+r-1))$. Define $\Delta f(m)=f(m)-f(m+1)$ and $g(m)=(1+H_{m+1})/(m+1)$. Then $H_s/(s(s-1))=g(s-2)-g(s-1)$ for $s\ge2$. By the binomial expansion of the difference operator, the coefficient of $x_j$ equals $\binom nj j(j-1)\Delta^{n-j+1}g(j-2)$.

The identity

$$\Delta^k g(m)=\frac{m!k!}{(m+k+1)!}\bigl(1+H_{m+k+1}-H_k\bigr)$$

follows by induction on $k$. The base case is the definition of $g$. For the induction step, the factorial ratio at $(m+1,k)$ is $(m+1)/(m+k+2)$ times the ratio at $(m,k)$, and the ratio at $(m,k+1)$ is $(k+1)/(m+k+2)$ times the ratio at $(m,k)$. Use the two harmonic increments $1/(m+k+2)$ and $1/(k+1)$ to complete the subtraction. Substituting $m=j-2$ and $k=n-j+1$ cancels the factorials to give the displayed formula for $\mu_1$. [Theorem 5.9](https://arxiv.org/html/2607.15503v1#S5.SS2)

## Independent calculation in dimensions three through five

By Theorem 5.9 of the paper, the Ehrhart polynomial is a sum over multisets of nonempty subsets of $[n]$ that admit distinct representatives. If a subset of size $s$ occurs $k$ times, it contributes the factor

$$\frac{(t w_s)(t w_s+1)\cdots(t w_s+k-1)}{k!},$$

where $w_1=b_1-1$ and, for $s\ge2$, $w_s=\sum_{j=0}^{s-2}(-1)^j\binom{s-2}{j}b_{s-j}$. A multiset has at most $n$ occurrences. Each factor depends only on the subset size and its multiplicity, so we group the multisets by their sorted lists of size–multiplicity pairs. The product of all factorials in a group's denominator divides $n!$. [Theorem 5.9 and the definition of the weights](https://arxiv.org/html/2607.15503v1#S5.SS2)

Substitute $b_j=1+x_j$ in the exact formula and multiply by $n!$. The resulting polynomial in $t,x_1,\ldots,x_n$ has integer coefficients. Replace each power $t^d$ by $u^d(1-u)^{n-d}$ to obtain $n!(1-u)^nE(u/(1-u))$. This is $n!$ times the polynomial whose coefficients in $u$ are the magic coefficients. Expanding and collecting identical exponent vectors gives the following counts.

| Dimension | Multisets admitting distinct representatives | Size–multiplicity profiles | Nonzero monomials in the scaled transform |
| ---: | ---: | ---: | ---: |
| 3 | 84 | 24 | 34 |
| 4 | 2,726 | 108 | 126 |
| 5 | 289,022 | 510 | 462 |

The two calculations agree on every coefficient in dimensions three through five. Every nonzero coefficient of each scaled transform is strictly positive.

## Verification

- `verify_parking_slices.py` verifies dimensions 3 through 10 and checks the harmonic formula against the computed polynomials. It uses only the Python 3.11+ standard library and exact rational arithmetic. Run `python3 verify_parking_slices.py`.
- `verify_parking_polytope.py` checks distinct representatives by keeping track of possible sets of already used labels. It multiplies sparse integer polynomials indexed by exponent tuples. Run `python3 verify_parking_polytope.py`.
- `ParkingPolytopeCertificate.lean` checks the arithmetic independently using Hall inequalities. For each ambient subset $S$, the number of occurrences whose available representatives are entirely in $S$ must be at most $|S|$. This condition is equivalent to Hall's criterion. To see the reverse implication, take $S$ to be the union of any subcollection of the occurrences. The checker expands integer coefficients using exponent vectors encoded in base $n+1$, where no exponent exceeds $n$. The checks use `native_decide`, with the dependency on `Lean.ofReduceBool` printed by the file.
- `ParkingPolytope3.lean` gives a direct symbolic identity and a Lean proof of the nonnegativity of all three nonconstant magic coefficients in dimension three. It starts from the authors' Example 5.12 and the dilation identity in Corollary 5.6. Its axiom audit reports the standard mathematical axioms. [Example 5.12](https://arxiv.org/html/2607.15503v1#S5.SS2)
- `ParkingMagicFirst.lean` proves the binomial expansion of the difference operator, the harmonic finite-difference identity, the resulting parameter weights, and strict positivity of the closed form in every dimension $n\ge3$. It reports only standard mathematical axioms. The derivation from the Ehrhart formula is the coefficient calculation above.

The connection to the geometric Ehrhart polynomial uses the cited formulas in the paper. The Lean symbolic checks cover dimensions 3 through 5. The slice computation covers dimensions 3 through 10 in Python. All the Lean files use the pinned toolchain and can be replayed with `lake build` after fetching the mathlib cache.

## Reproducing

```sh
python3 verify_parking_slices.py      # dimensions 3-10, about 80 seconds
python3 verify_parking_polytope.py    # independent check, dimensions 3-5
lake exe cache get && lake build      # Lean 4.19.0 with Mathlib v4.19.0
```
