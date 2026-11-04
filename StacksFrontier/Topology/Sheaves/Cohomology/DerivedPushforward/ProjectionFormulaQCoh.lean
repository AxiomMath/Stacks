module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDevissage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceModulesAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohDevissage

/-!
# [Stacks, Tag 08EU]: the projection formula on `D_QCoh`

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, let
`E ∈ D_QCoh(𝒪_X)` and let `K ∈ D_QCoh(𝒪_Y)`.  The projection-formula morphism of
[Stacks, Tag 0B53],

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`,

is an isomorphism.  That is the whole of [Stacks, Tag 08EU], at exactly the source's hypotheses.

## Main results

* `isIso_projectionFormulaMap_of_isDQCoh`: **[Stacks, Tag 08EU].**

## The five steps of the source's proof, and where each one lives

* *"To check the map is an isomorphism we may work locally on `Y`.  Hence we reduce to the case
  that `Y` is affine."* —
  `ProjectionFormulaQCohLocalization.isIso_projectionFormulaMap_of_isDQCoh_of_affineBase`.
* *"If the statement holds for each `K_i`, then it holds for `K = ⨁ K_i`"* —
  `Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isIso_projectionFormulaMap_sigma`, which
  rests on [Stacks, Tag 08DZ] for `Rf_*`.
* *"if the statement of the lemma holds for two of `K, L, M`, then it holds for the third"* —
  `Stacks.Cohomology.ProjectionFormulaTriangles.isIso_projectionFormulaMap_triangle`.
* *"The functor `~ : D(A) → D_QCoh(𝒪_Y)` is an equivalence … it suffices to prove `T` holds for
  `A[k]`"* — `Stacks.DerivedQCoh.property_of_isDQCoh_of_isAffine`, from the equivalence of
  [Stacks, Tag 06Z0] and the resolution of [Stacks, Tag 09PB].
* *"the statement of the lemma is clear for shifts of the structure sheaf"* —
  `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitShift_unconditional`,
  which needs no hypothesis at all and holds for an arbitrary morphism of ringed spaces.

`ProjectionFormulaQCohDevissage.isIso_projectionFormulaMap_of_isDQCoh_of_devissage` assembles
the five; this file supplies its last two arguments, so that the theorem below carries no
hypothesis the source does not state.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaQCoh

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

/-- **[Stacks, Tag 08EU].**  For a quasi-compact and quasi-separated morphism of schemes
`f : X ⟶ Y`, an `E` in `D_QCoh(𝒪_X)` and a `K` in `D_QCoh(𝒪_Y)`, the projection-formula morphism
of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism.

The hypotheses are the source's and no others: quasi-compactness and quasi-separatedness of `f`,
and quasi-coherence of the cohomology sheaves of `E` and of `K`.  No boundedness, no flatness,
no perfectness, no affineness, no Noetherian or separatedness assumption, and no choice of model
for either derived category beyond the one the whole file works in. -/
@[stacks 08EU "the whole lemma: for a quasi-compact and quasi-separated morphism of schemes f : X \
⟶ Y, E in D_QCoh(𝒪_X) and K in D_QCoh(𝒪_Y), the projection-formula morphism Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ \
Lf^*K) of Tag 0B53 is invertible. The proof is the source's dévissage: locality on Y, the affine \
equivalence D(A) ≌ D_QCoh(𝒪_Y) of Tag 06Z0 with the resolution of Tag 09PB, direct sums through \
Tag 08DZ, two-out-of-three on distinguished triangles, and the shifts of the structure sheaf as \
the base case"]
theorem isIso_projectionFormulaMap_of_isDQCoh {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E)
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) :=
  ProjectionFormulaQCohDevissage.isIso_projectionFormulaMap_of_isDQCoh_of_devissage
    (by
      intro Y' hY' T hiso hsum htri hunit K' hK'
      exact @Stacks.DerivedQCoh.property_of_isDQCoh_of_isAffine Y' hY' T hiso hsum htri hunit
        K' hK')
    (by
      intro X' Y' f' hqc hqs E' hE' I Z hcop hZ h
      exact @Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isIso_projectionFormulaMap_sigma
        X' Y' f' hqc hqs E' hE' I Z hcop hZ h)
    f E K hE hK

/-- **[Stacks, Tag 08EU] in the `AlgebraicGeometry.Scheme.Modules` spelling**, with
quasi-coherence of the cohomology sheaves written out rather than packaged as
`Stacks.DerivedQCoh.IsDQCoh`.

This is the shape the consumers of the tag ask for, and it is what
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Composition.lean` quotes for the two
projection-formula steps of [Stacks, Tag 0FYS].
`Stacks.DerivedQCoh.IsDQCoh` is by definition the universally quantified form of the two
quasi-coherence conditions, and `X.Modules` is `SheafOfModules.{u} (structureSheafRing
X.toRingedSpace)`, so this is `isIso_projectionFormulaMap_of_isDQCoh` and nothing more. -/
theorem projectionFormulaMap_isIso_of_isQuasicoherent_homology
    {V W : Scheme.{u}} (p : V ⟶ W) (hqc : QuasiCompact p) (hqs : QuasiSeparated p)
    (E : DerivedCategory V.Modules) (A : DerivedCategory W.Modules)
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor V.Modules j).obj E).IsQuasicoherent)
    (hA : ∀ j : ℤ, ((DerivedCategory.homologyFunctor W.Modules j).obj A).IsQuasicoherent) :
    IsIso (projectionFormulaMap p.toLRSHom.toShHom E A) :=
  @isIso_projectionFormulaMap_of_isDQCoh V W p hqc hqs E A hE hA

end Stacks.Cohomology.ProjectionFormulaQCoh

end

end
