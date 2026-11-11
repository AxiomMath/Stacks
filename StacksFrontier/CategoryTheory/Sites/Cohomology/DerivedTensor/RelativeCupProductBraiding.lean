module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
import StacksCore.Tactic.StacksAttribute

/-!
# Commutativity of the relative cup product on a ringed topos

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi.  **[Stacks, Tag 0FPM]**
asserts that the relative cup product of [Stacks, Tag 0B6C] is commutative: for all `K, L` in
`D(𝒪)` the square

```
Rf_*K ⊗^L_{𝒪'} Rf_*L --cup--→ Rf_*(K ⊗^L_𝒪 L)
        | ψ                          | Rf_*ψ
        ↓                            ↓
Rf_*L ⊗^L_{𝒪'} Rf_*K --cup--→ Rf_*(L ⊗^L_𝒪 K)
```

commutes in `D(𝒪')`, where `ψ` is the commutativity constraint on the derived category
([Stacks, Tag 0FPT]).

## Main definitions

* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.PullbackTensorComparisonBraided` — the
  proposition that the comparison of [Stacks, Tag 07A4] carries the commutativity constraint of
  `D(𝒪')` to that of `D(𝒪)`, i.e. that `Lf^*` is a *braided* monoidal functor for it and not
  merely a monoidal one.

## Main results

* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.pullbackTensorComparisonBraided` — that
  proposition, **proved**.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct_braiding_unconditional` —
  **[Stacks, Tag 0FPM]** for a morphism of ringed topoi presented by a morphism of sites, with
  `ψ` the genuine constraint of [Stacks, Tag 0FPT] on both edges, for all `K, L` in `D(𝒪)`, and
  with nothing assumed.  The tag for an arbitrary morphism of ringed topoi is registered on
  `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_braiding`.

## Implementation notes

*`ψ` is the constraint the source prescribes, not data.*  It is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`, the braiding of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric` — [Stacks, Tag 0FPT] — which
is stated for an arbitrary ring sheaf on an arbitrary small site and therefore applies to `𝒪_W`
of a ringed topos `W` directly.  Its tensor product is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of [Stacks, Tag 06YU] **on the
nose**: `Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal` is an
equality of bifunctors, not an isomorphism.  So `canonicalBraidingHom 𝒪_W A B` already has the
type `A ⊗^L B ⟶ B ⊗^L A` read on the uncurried bifunctor the relative cup product is stated
over, and no wrapper, ascription or transport appears below.  Its sign convention is the
source's: on K-flat representatives it is the Koszul symmetry of total tensor complexes
(`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding`, whose content is
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` of [Stacks, Tag 06YM]), with sign
`(-1)^{pq}` on the summand of bidegree `(p, q)`, which is what [Stacks, Tag 0FPT] refers to in
More on Algebra, Section 15.74.

*What this removes from `relativeCupProduct_braiding`.*  That statement, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RelativeCupProductCoherence.lean`,
carries four inputs: the two commutativity constraints `sY`, `sX` as arbitrary data, the
naturality `hsX` of one of them, and the braidedness `hcomp` of the comparison of
[Stacks, Tag 07A4].  The first three are gone here — the constraints are the ones
[Stacks, Tag 0FPT] prescribes, and their naturality is `BraidedCategory.braiding_naturality` for
`canonicalDerivedSymmetric`, used inline.  Nothing is added.

*The fourth input is the whole remaining content of the tag, and it is now discharged.*  The
chase reducing the square to it is
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_braiding`, which is
complete and assumes nothing about ringed topoi; so [Stacks, Tag 0FPM] in this development *is*
`PullbackTensorComparisonBraided`, and `pullbackTensorComparisonBraided` proves it.  Nothing is
hypothesised below.

*Where that proof lives, and why it is not the ringed-space one.*  For a morphism of ringed
**spaces** the corresponding statement is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`, whence
[Stacks, Tag 0FP5] in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductCommutativity`.
That proof descends from a pair of K-flat complexes, where it is the braiding clause of a
*monoidal lift of `f^*` to complexes*
(`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_braiding`, resting on
`Stacks.PullbackTensorCoherence.pullbackComparisonBraided`, proved on local pure tensors).  None
of that apparatus exists on the topos side: for a `CategoryTheory.Sheaf.MorphismOfTopoi` there is
no presheaf-level colimit model of the pullback, so the pure-tensor evaluation does not
transport, and there is still no `Monoidal`, `LaxBraided` or `Braided` structure on
`pullbackComplex f` or on `RingedToposSiteHom.pullbackTopos`.  The ringed-topos proof therefore
goes through the three layers below instead, none of which needs such a structure:

* **Modules.**  `Stacks.SheafOfModules.RingedToposPullback.braiding` — the braided clause of
  [Stacks, Tag 03EL] for `Stacks.SheafOfModules.pullbackTensorIso`, the fourth coherence
  alongside the associativity and the two unitalities of
  `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence`.  Like those three it is proved
  on the six-step chain of bijections of Tag 03EL, through
  `Stacks.Sheaves.DerivedPullback.pullbackTensorComparisonHom_comp` and
  `Stacks.SheafOfModules.pairing_ext`, the braiding being read on local pure tensors by
  `Stacks.SheafOfModules.braiding_tensorSectionsAt`.  Transported to the site-presented pullback
  it is `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDeg_braiding`.
* **Complexes.**  `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_braiding` — the
  comparison of total tensor complexes is braided for the Koszul symmetry
  `Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` of [Stacks, Tag 06YM].  It is checked one
  bidegree at a time: `Stacks.Sheaves.DerivedPullback.ι_pullbackToposTensorTotalIso_hom` is the
  summandwise formula for the comparison and
  `Stacks.SheafOfModules.Tensor.ι_tensorComplexFlipIso_hom` the one for the symmetry, carrying
  the sign `(-1)^{pq}`, and the two reduce the square to the module-level clause.
* **The derived category.**
  `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding_app_of_kFlat` at a pair of
  K-flat complexes with flat terms, by the chase
  `CategoryTheory.bifunctor_comparison_braiding_of_models` over
  `Stacks.Sheaves.DerivedPullback.toTensor_square_of_kFlat` and the braiding clause of Tag 0FPT
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding`; then
  `Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat`, which is [Stacks, Tag 06YS] in the
  shape of an extensionality principle for transformations on `D(𝒪') × D(𝒪')`, to reach arbitrary
  objects.  The assembly is
  `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding`.

The statement is about `Lf^*` and `⊗^L` and not about the cup product, so it is proved beside the
comparison of Tag 07A4 rather than here; this file only consumes it.

*No constraint is redefined.*  The commutativity constraint of [Stacks, Tag 0FPT] is
`canonicalBraidingHom`; the associativity constraint, which [Stacks, Tag 0FPL] re-brackets with,
is `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator` together with its
`..._naturality_left`, `..._naturality_middle` and `..._naturality_right`, for an arbitrary
derived tensor product of [Stacks, Tag 06YU] on an arbitrary site.  Both already exist in the
generality a ringed topos needs, and this file introduces no copy of either.

## References

* [Stacks Project, Tag 0FPM](https://stacks.math.columbia.edu/tag/0FPM)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal (canonicalBraidingHom canonicalDerivedMonoidal
  canonicalDerivedSymmetric)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

section Braided

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **`Lf^*` is a braided monoidal functor for the comparison of [Stacks, Tag 07A4]**: the
comparison `Lf^*(P ⊗^L_{𝒪'} Q) ≅ Lf^*P ⊗^L_𝒪 Lf^*Q` carries the commutativity constraint `ψ` of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`, for all `P, Q` in `D(𝒪')`.

This is the entire remaining content of [Stacks, Tag 0FPM] in this development: the chase
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_braiding` is complete and
assumes nothing, so the commutativity square of the relative cup product follows from this
together with the naturality of `ψ`, and the latter is
`CategoryTheory.BraidedCategory.braiding_naturality` for
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`.

It is **proved**, for a morphism of ringed topoi, by `pullbackTensorComparisonBraided` below; the
statement is kept as a named proposition because it is what the diagram chase
`adjunctionCupProduct_braiding` consumes.  For a morphism of ringed **spaces** the counterpart is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`. -/
def PullbackTensorComparisonBraided : Prop :=
  ∀ P Q : DerivedModules Y.O,
    (derivedPullback f).map (canonicalBraidingHom Y.O P Q) ≫
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app (Q, P) =
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app (P, Q) ≫
        canonicalBraidingHom X.O ((derivedPullback f).obj P) ((derivedPullback f).obj Q)

/-- **`Lf^*` is a braided monoidal functor for the comparison of [Stacks, Tag 07A4]**, with
nothing assumed.

On a pair of K-flat complexes with flat terms the comparison of Tag 07A4 is computed by the
ordinary total tensor complex, the commutativity constraint of [Stacks, Tag 0FPT] is computed
there by the Koszul symmetry of complexes, and the comparison of total tensor complexes of
[Stacks, Tag 03EL] is braided for that symmetry — which, for a ringed topos, comes down to the
braided clause of Tag 03EL on modules,
`Stacks.SheafOfModules.RingedToposPullback.braiding`.  The three are fused and descended to all
of `D(𝒪') × D(𝒪')` along [Stacks, Tag 06YS] by
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding`. -/
theorem pullbackTensorComparisonBraided : PullbackTensorComparisonBraided f hmos :=
  fun P Q => Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding f hmos P Q

/-- **[Stacks, Tag 0FPM].**  The relative cup product of [Stacks, Tag 0B6C] is commutative: for
a morphism of ringed topoi `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` and **all** `K, L` in `D(𝒪)` the
square

```
Rf_*K ⊗^L_{𝒪'} Rf_*L --cup--→ Rf_*(K ⊗^L_𝒪 L)
        | ψ                          | Rf_*ψ
        ↓                            ↓
Rf_*L ⊗^L_{𝒪'} Rf_*K --cup--→ Rf_*(L ⊗^L_𝒪 K)
```

commutes in `D(𝒪')`.  The horizontal arrows are the relative cup product, the left edge is `ψ`
at `(Rf_*K, Rf_*L)` and the right edge is `Rf_*` applied to `ψ` at `(K, L)`, exactly as the
source draws them.  `ψ` is the commutativity constraint of [Stacks, Tag 0FPT],
`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`, on each of the two derived
categories — not a symmetry supplied as data — and no hypothesis is placed on `K` or `L`.

Nothing is assumed.  The braidedness of the comparison of [Stacks, Tag 07A4], which is the whole
content of the tag, is `pullbackTensorComparisonBraided` above.

The morphism here is presented by a continuous functor of the underlying sites that is a
morphism of sites (`AlgebraicGeometry.RingedToposSiteHom` with `hmos`), which not every morphism
of ringed topoi is.  The tag, for an arbitrary morphism of ringed topoi, is
`Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_braiding`. -/
theorem relativeCupProduct_braiding_unconditional (K L : DerivedModules X.O) :
    relativeCupProduct f hmos K L ≫
        (derivedPushforward f).map (canonicalBraidingHom X.O K L) =
      canonicalBraidingHom Y.O ((derivedPushforward f).obj K) ((derivedPushforward f).obj L) ≫
        relativeCupProduct f hmos L K :=
  adjunctionCupProduct_braiding (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom
    (canonicalBraidingHom Y.O) (canonicalBraidingHom X.O)
    (fun u v =>
      let := canonicalDerivedMonoidal X.O
      let := canonicalDerivedSymmetric X.O
      BraidedCategory.braiding_naturality u v)
    (pullbackTensorComparisonBraided f hmos) K L

end Braided

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
