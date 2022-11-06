# semprag-ppsp

Code for the paper [Presupposition projection as a scope
phenomenon](https://ling.auf.net/lingbuzz/006801). Examples from the paper
appear in
[Examples.hs](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Examples.hs):
[Figure 5,
p. 18](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Examples.hs#L30-L34),
[Figure 6,
p. 20](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Examples.hs#L36-L43),
[Figure 9,
p. 19](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Examples.hs#L36-L43),
and [Figure 10,
p. 28](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Examples.hs#L61-L67).
There is also an [example involving
reconstruction](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Examples.hs#L45-L52)
mentioned on p. 20. The examples involving *also* are
[here](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Examples.hs#L69-L78).

Figures 5 and 6 and the reconstruction example can be interpreted in the
extensional model found in
[Model.hs](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Model.hs)
by doing, e.g., `interpExpr (\case) figure5` (make sure to turn on LambdaCase
and EmptyCase). All of the examples can be translated into a λ-term representing
an intension by loading
[Translation.hs](https://github.com/juliangrove/semprag-ppsp/blob/main/src/Translation.hs)
and doing the same (and β-reducing, if desired), e.g., `betaReduce $ interpExpr
(\case) figure5`.
