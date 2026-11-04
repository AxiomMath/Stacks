module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion

/-!
# Local description of upper shriek: restriction to an open square

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S`, the category
of schemes separated and of finite type over `S` of [Stacks, Tag 0F42]. Let `j : U ⟶ X` and
`i : V ⟶ Y` be morphisms of `FTS S` whose underlying morphisms of schemes are open immersions, and
let `g : U ⟶ V` be a morphism making the square

```
U --j--> X
|        |
g        f
v        v
V --i--> Y
```

commute. [Stacks, Tag 0BV2] (Remark 48.17.5) asserts two things about this situation, and this
file delivers the **first** of them:

* **(a)** `(f^!E)|_U ≅ g^!(E|_V)` for `E ∈ D⁺_QCoh(𝒪_Y)`;
* **(b)** the affine formula `φ^!(K) = RHom(A, K ⊗^L_R P)[n]` when `U = Spec(A)`, `V = Spec(R)`
  and `A = P/I` with `P = R[x_1, …, x_n]`.

Clause (a) is the content below. Clause (b) is **not** claimed here: its proof factors
`U → 𝔸ⁿ_V → ⋯ → 𝔸¹_V → V` and applies [Stacks, Tag 0AA1] `n` times, and Tag 0AA1 — the
computation `f^! ≅ Lf^*[1]` for the projection `𝔸¹_V → V` — is not available in this repository
in any form. See the implementation notes.

The source's argument for (a) is two sentences: `j^! ∘ f^! ≅ g^! ∘ i^!` by [Stacks, Tag 0ATX]
(Lemma 48.16.3) applied to the two factorisations of the diagonal `U ⟶ Y` of the square, and
`j^!` and `i^!` are restriction by [Stacks, Tag 0AU0] (Lemma 48.17.1). Both instances of Tag 0ATX
are carried here as explicit hypotheses; Tag 0AU0 is *not* carried, it is
`Stacks.Duality.upperShriekIsoDerivedPullbackOfOpenImmersion`, proved in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekAffineComparison/OpenImmersion.lean`.

## Main definitions

* `Stacks.Duality.openImmersionUpperShriek` — `j^!` for an open immersion `j` of `FTS S`,
  computed at the compactification `X̄ = Y` of `Stacks.Duality.openCompactification`.

## Main results

* `Stacks.Duality.restrictedUpperShriekIsoOfOpenSquare` — **[Stacks, Tag 0BV2], clause (a)**:
  `f^! ⋙ Lj^* ≅ Li^* ⋙ g^!`, that is `(f^!E)|_U ≅ g^!(E|_V)` naturally in `E`.
* `Stacks.Duality.restrictedUpperShriekObjIso` — the same read on an object, which is the shape
  the source states.

## Implementation notes

*What is carried and what is proved.* The two hypotheses `h0ATXf` and `h0ATXi` are the two
instances of [Stacks, Tag 0ATX] that the source's proof uses: for the composite `j ≫ f` and for
the composite `g ≫ i`, which the commutativity hypotheses `_hdj` and `_hdi` identify with
one morphism `d : U ⟶ Y`. Those two equations are underscore-prefixed because the proof term does
not consume them: the commutativity of the square is already encoded in `h0ATXf` and `h0ATXi`
being isomorphisms out of the *same* functor `d^!`. They are part of the statement because
without them `d` is an arbitrary morphism `U ⟶ Y` and `h0ATXi` is not an instance of Tag 0ATX
for `g` and `i`. Tag 0ATX is not available in this repository, and its independence-of-
compactification clause is what licenses reading it at the particular compactifications `cd`,
`cf`, `cg` and `Stacks.Duality.openCompactification` chosen here; so the two instances are
hypotheses in the shape the source uses them. Everything else in the proof is Tag 0AU0, which is
proved: the content the conclusion adds to `h0ATXf` and `h0ATXi` is exactly the replacement of
`j^!` by `Lj^*` and of `i^!` by `Li^*`, and that replacement is
`Stacks.Duality.upperShriekIsoDerivedPullbackOfOpenImmersion`. Without it the conclusion would
say nothing beyond its hypotheses; with it the conclusion is a statement about *restriction*,
which is what makes Tag 0BV2 a local description.

*No affineness, and no boundedness.* The source takes `U` and `V` affine, because it wants to
run clause (b) next; clause (a) uses only that `j` and `i` are open immersions, and is
stated at that generality here. Likewise the source works on `D⁺_QCoh`, while
`Stacks.Duality.upperShriek` is defined on the unbounded `D_QCoh`; the isomorphism below is
therefore on all of `D_QCoh` and restricts to the source's.

*Why clause (b) is not here.* Clause (b) needs, beyond clause (a): [Stacks, Tag 0AA1] for
`𝔸¹_V → V` iterated `n` times, [Stacks, Tag 0AA2] for the closed immersion `Spec(A) → 𝔸ⁿ_V` of
the presentation, [Stacks, Tag 0A78] and the comparison `D(R) ≌ D_QCoh(Spec R)` of
[Stacks, Tag 06Z0] to move the answer to modules. Tag 0AA1 is not stated in the library. A
declaration for it would read

  `upperShriekAffineLineIsoDerivedPullbackShift (V : FTS S) :
     Nonempty (upperShriek (𝔸¹_V ⟶ V) c ≅
       quasiCoherentDerivedPullback' _ ⋙ shiftFunctor _ (1 : ℤ))`

and its goal state is that `Nonempty` with nothing to introduce it. Carrying it as a hypothesis
would make clause (b) a restatement of its own inputs, so clause (b) is left unclaimed.

## References

* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-! ### `j^!` of an open immersion, as a functor -/

section OpenImmersionUpperShriek

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y : AlgebraicGeometry.FTS S}
  (j : X ⟶ Y) [IsOpenImmersion j.left]

/-- `j^!` for a morphism `j` of `AlgebraicGeometry.FTS S` whose underlying morphism of schemes is
an open immersion, computed at the compactification `X̄ = Y` of
`Stacks.Duality.openCompactification`. -/
abbrev openImmersionUpperShriek :
    quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left :=
  upperShriek j (openCompactification j)

end OpenImmersionUpperShriek

/-! ### Tag 0BV2, clause (a) -/

section OpenSquare

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  {U X V Y : AlgebraicGeometry.FTS S}
  (f : X ⟶ Y) (g : U ⟶ V) (j : U ⟶ X) (i : V ⟶ Y)
  [IsOpenImmersion j.left] [IsOpenImmersion i.left]
  {d : U ⟶ Y}
  (cf : AlgebraicGeometry.CompactificationOf (Over.mk f.left))
  (cg : AlgebraicGeometry.CompactificationOf (Over.mk g.left))
  (cd : AlgebraicGeometry.CompactificationOf (Over.mk d.left))
  (h0ATXf : upperShriek d cd ≅ upperShriek f cf ⋙ openImmersionUpperShriek j)
  (h0ATXi : upperShriek d cd ≅ openImmersionUpperShriek i ⋙ upperShriek g cg)

/-- **Stacks Project, Tag 0BV2 (Remark 48.17.5), clause (a).** Let `f : X ⟶ Y` and `g : U ⟶ V` be
morphisms of `AlgebraicGeometry.FTS S` and let `j : U ⟶ X`, `i : V ⟶ Y` be morphisms of
`FTS S` whose underlying morphisms of schemes are open immersions, with `j ≫ f = g ≫ i`. Then
restricting an exceptional inverse image to `U` computes the exceptional inverse image of the
restriction to `V`:

  `f^! ⋙ Lj^* ≅ Li^* ⋙ g^!`,

that is `(f^!E)|_U ≅ g^!(E|_V)` naturally in `E ∈ D_QCoh(𝒪_Y)`.

The source's proof is reproduced. The two hypotheses `h0ATXf` and `h0ATXi` are the two instances
of [Stacks, Tag 0ATX] that it cites, for the two factorisations `j ≫ f` and `g ≫ i` of the
diagonal `d : U ⟶ Y` of the square. The passage from `j^!` and `i^!` to the restrictions `Lj^*`
and `Li^*` is [Stacks, Tag 0AU0], which is not assumed here but proved in
`Stacks.Duality.upperShriekIsoDerivedPullbackOfOpenImmersion`; it is the whole of the content
this statement adds to its hypotheses.

Clause (b) of Tag 0BV2, the affine formula `φ^!(K) = RHom(A, K ⊗^L_R P)[n]`, is not claimed: it
needs [Stacks, Tag 0AA1], which this repository does not have. -/
@[stacks 0BV2 "clause (a) only, the restriction formula (f^!E)|_U = g^!(E|_V) for an open \
  square; clause (b), the affine formula phi^!(K) = RHom(A, K ⊗^L_R P)[n], is NOT claimed, \
  because Stacks 0AA1 (f^! = Lf^*[1] for A^1_V -> V) is absent from this repository. Carried: \
  h0ATXf and h0ATXi, the two instances of Stacks 0ATX for the two factorisations of the \
  diagonal of the square. \
  Stacks 0AU0 is NOT carried: it is proved by \
  Stacks.Duality.upperShriekIsoDerivedPullbackOfOpenImmersion, and supplying it is the only \
  content this statement adds to its hypotheses. Stated for open immersions rather than affine \
  opens, and on the unbounded D_QCoh rather than D^+_QCoh"]
def restrictedUpperShriekIsoOfOpenSquare (_hdj : j ≫ f = d) (_hdi : g ≫ i = d) :
    upperShriek f cf ⋙ quasiCoherentDerivedPullback' j.left ≅
      quasiCoherentDerivedPullback' i.left ⋙ upperShriek g cg :=
  Functor.isoWhiskerLeft (upperShriek f cf)
      (upperShriekIsoDerivedPullbackOfOpenImmersion j).symm ≪≫
    h0ATXf.symm ≪≫ h0ATXi ≪≫
      Functor.isoWhiskerRight (upperShriekIsoDerivedPullbackOfOpenImmersion i)
        (upperShriek g cg)

/-- **Stacks Project, Tag 0BV2, clause (a), on an object.** For `E ∈ D_QCoh(𝒪_Y)` the restriction
of `f^!E` to `U` is `g^!` of the restriction of `E` to `V`. This is the shape in which the source
states the assertion; it is `Stacks.Duality.restrictedUpperShriekIsoOfOpenSquare` evaluated at
`E`. -/
def restrictedUpperShriekObjIso (_hdj : j ≫ f = d) (_hdi : g ≫ i = d)
    (E : quasiCoherentDerivedCategory Y.left) :
    (quasiCoherentDerivedPullback' j.left).obj
        ((upperShriek f cf).obj E) ≅
      (upperShriek g cg).obj
        ((quasiCoherentDerivedPullback' i.left).obj E) :=
  (restrictedUpperShriekIsoOfOpenSquare f g j i cf cg cd h0ATXf h0ATXi _hdj _hdi).app E

end OpenSquare

end Stacks.Duality

end
