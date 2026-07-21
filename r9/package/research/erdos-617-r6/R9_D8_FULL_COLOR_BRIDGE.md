# The fixed \(r=9\) degree-eight full-color bridge

## Verdict and scope

PROVED LOCALLY. Assume the two terminal inputs

\[
 P_3(26)\ge121
 \qquad\text{and}\qquad
 P_3(27)=\varnothing.
\tag{1}
\]

Then every packing cell in the outer minimum-degree-eight row is strict.
Together with the already strict rows of degree at most seven, this proves
the fixed \(r=9\) case, conditional only on the proof packages establishing
(1).

The new ingredient is a human proof of

\[
 \boxed{P_4(37)\ge192.}
\tag{2}
\]

The argument uses the full-color cap on an 11-set. The previous scalar
recursion did not use this shell inequality and stopped below the required
outer bound.

## 1. The 37-vertex bridge

Let \(H\) be an actual induced target-color graph on 37 vertices with

\[
 \alpha(H)\le4,
 \qquad
 \omega(H)\le8.
\tag{3}
\]

Suppose for contradiction that \(e(H)\le191\). Every vertex has degree at
least ten. Indeed, a vertex of degree at most nine has at least 27
nonneighbors. Any 27 of them induce a target graph with independence number
at most three and clique number at most eight, contrary to the second input
in (1).

On the other hand,

\[
 \frac{2e(H)}{37}\le\frac{382}{37}<11,
\]

so \(H\) has a vertex \(v\) of degree exactly ten. Put

\[
 A=N_H(v),
 \qquad
 B=V(H)\setminus(A\cup\{v\}).
\]

Thus \(|A|=10\) and \(|B|=26\). Write

\[
 F=\overline{H[A]},
 \qquad
 f=e(F),
 \qquad
 D_a=N_H(a)\cap B,
 \qquad
 c=\sum_{a\in A}|D_a|.
\tag{4}
\]

The full-color induced-density cap at order 11 is

\[
 D_9(11)=39.
\]

The set \(\{v\}\cup A\) spans \(10+45-f=55-f\) target edges. Hence

\[
 f\ge16.
\tag{5}
\]

For each \(a\in A\), minimum degree gives

\[
 10\le d_H(a)
 =1+9-d_F(a)+|D_a|,
\]

and therefore \(|D_a|\ge d_F(a)\). Summing over \(A\) gives

\[
 c\ge2f.
\tag{6}
\]

The graph \(H[B]\) has independence number at most three and clique number
at most eight. The first input in (1) gives

\[
 e(H[B])\ge121.
\tag{7}
\]

Equations (4)-(7) now yield

\[
\begin{aligned}
 e(H)
 &=10+(45-f)+e(H[B])+c\\
 &\ge10+45-f+121+2f\\
 &=176+f\\
 &\ge192,
\end{aligned}
\]

contrary to \(e(H)\le191\). This proves (2).

## 2. Propagation through the colored recursion

Insert (1)-(2) into the independently implemented colored recursion. Along
the degree-eight diagonal it gives

\[
\begin{array}{c|ccccc}
(a,n)&(4,37)&(5,46)&(6,55)&(7,64)&(8,73)\\ \hline
B_9(a,n)&192&227&264&301&338.
\end{array}
\tag{8}
\]

For a degree-eight vertex in a least target color on \(K_{82}\), after
deleting \(j\) target copies of \(K_9\), the canonical residual edge upper
bounds are

\[
 333,297,261,225,189
 \qquad(j=0,1,2,3,4).
\tag{9}
\]

Reading (8) in the corresponding reverse order gives the strict margins

\[
 5,4,3,2,3.
\tag{10}
\]

Thus a target \(K_9\) is forced at every one of the five packing steps. The
nonneighbor graph would contain five disjoint target copies of \(K_9\),
contrary to the proved \(r-4\)-block theorem.

The rows with outer minimum degree at most seven were already strict under
the weaker order-26 input. The verifier recomputes all 45 outer cells after
inserting (1)-(2); every cell is strict or already empty.

## 3. Fixed-case consequence

Let the edges of \(K_{82}\) be colored with nine colors and suppose every
ten vertices see every color. Choose a least color graph. Its minimum degree
lies between two and eight. The existing recursion excludes degrees two
through seven, while Sections 1-2 exclude degree eight. This contradiction
proves:

**Theorem.** Every nine-coloring of the edges of \(K_{82}\) contains ten
vertices whose induced edges omit at least one color.

This is a local proof. Its two terminal dependencies are banked and replayed
from committed source. External mathematical review remains pending. It does
not prove Erdős Problem 617 for arbitrary \(r\).

## 4. Replay

Run

~~~sh
python3 research/erdos-617-r6/verify_r9_d8_full_color_bridge.py
python3 research/erdos-617-r6/verify_r9_order26_outer_implication.py
python3 research/erdos-617-r6/verify_colored_core_ladder.py
~~~

The first verifier checks the 37-vertex arithmetic, recomputes the colored
recursion, checks all 45 outer cells, and rejects two deliberate weakened
inputs. The second command preserves the earlier negative audit showing why
the order-26 floor alone was insufficient. The third checks the common
packing and block contradiction.
