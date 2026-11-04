module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeComplexPushforwardQcoh
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedComplexInduction
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.TorDiagonal
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.MorphismTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingObjectTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.LocallyBoundedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.LocallyBoundedIsKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaGeneralBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductComposition
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOpens
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.MorphismTransportWhiskered
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionSingleIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfectConverse
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for a relative complex, conclusions (4) and (5) of Tag 0FML

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `F^•` be a
locally bounded complex of `f^{-1}𝒪_S`-modules whose terms are restrictions of scalars of
quasi-coherent `𝒪_X`-modules. This file proves conclusions (4) and (5) of [Stacks, Tag 0FML]:
the projection formula `Rf_*F^• ⊗^𝐋_{𝒪_S} K ≅ Rf_*(F^• ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)` for `K` in
`D_QCoh(𝒪_S)`, and its form with the ordinary tensor product against a quasi-coherent sheaf.
Conclusion (2), that `Rf_*K` lies in `D_QCoh(𝒪_S)`, is
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeComplexPushforwardQcoh`.

## Main results

* `Stacks.RelativeComplexPushforward.isIso_projectionFormulaMap_of_finite_support`: the
  **dévissage of the projection formula in the source complex**, for an arbitrary morphism of
  ringed spaces and with no hypothesis — invertibility of the morphism of [Stacks, Tag 0B53] at
  each term of a finite-support complex, placed in its own degree and shifted arbitrarily,
  spreads to the complex.
* `Stacks.RelativeComplexPushforward.isIso_projectionFormulaMap_of_isLocallyBounded`: the
  **reduction to an affine base**, for an arbitrary morphism of ringed spaces — the dévissage
  above run at a merely *locally bounded* complex, given a cover of the base by opens with
  quasi-compact preimage.
* `isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded_of_isQuasicoherent` and
  `relativeComplexProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent`:
  **conclusion (5)** with no hypothesis beyond the tag's own, so in particular with `F^•` only
  *locally bounded*, `Rf_*F^• ⊗^𝐋_{𝒪_S} K ≅ Rf_*(F^• ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)` for `K` in
  `D_QCoh(𝒪_S)`, in its invertibility and its isomorphism form.
* `Stacks.RelativeComplexPushforward.isIso_projectionFormulaMap_relativeComplex_of_isQuasicoherent`
  and `Stacks.RelativeComplexPushforward.relativeComplexProjectionFormulaIsoOfIsQuasicoherent`:
  the same two statements for an `F^•` with finitely many nonzero terms. They are untagged,
  being the special case the locally bounded statements are proved from.
* `relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent`:
  **conclusion (4)** with no hypothesis beyond the tag's own, so again with `F^•` only *locally
  bounded*, `Rf_*F^• ⊗^𝐋_{𝒪_S} G ≅ Rf_*(F^• ⊗_{f^{-1}𝒪_S} f^{-1}G)` for a quasi-coherent `G`,
  with the *ordinary* tensor product on the right.
* `Stacks.RelativeComplexPushforward.relativeComplexOrdinaryProjectionFormulaIsoOfIsQuasicoherent`:
  the same for an `F^•` with finitely many nonzero terms. Untagged, being the special case.
* `Stacks.RelativeComplexPushforward.isIso_projectionFormulaMap_relativeComplex`,
  `Stacks.RelativeComplexPushforward.relativeComplexProjectionFormulaIso` and
  `Stacks.RelativeComplexPushforward.relativeComplexOrdinaryProjectionFormulaIso`: the same three
  statements for an arbitrary `K`, respectively an arbitrary `G`, carrying the case of a single
  quasi-coherent sheaf as a hypothesis. They are untagged: being conditional they do not prove
  the tag, and they are kept because that generality is worth having.
* `Stacks.RelativeComplexPushforward.isIso_projectionFormulaMap_single_relativeBase`: **that
  hypothesis, proved** — the crossing from `a'` to `f`.
* `Stacks.RelativeComplexPushforward.isIso_projectionFormulaMap_of_comp`: the morphism of
  [Stacks, Tag 0B53] **for the outer factor of a composite** of morphisms of ringed spaces is
  invertible as soon as it is for the composite and for the inner factor.
* `Stacks.RelativeComplexPushforward.isIso_projectionFormulaMap_toInverseImageBase`: the
  morphism of [Stacks, Tag 0B53] at `(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` is **invertible with no
  hypothesis**, that morphism of ringed spaces being the identity on the underlying space.
* `Stacks.RelativeComplexPushforward.derivedPushforwardToInverseImageBaseSingleShiftIso`:
  `Rb_*` of a module placed in a degree and shifted, for `b : (X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)`.
* `Stacks.RelativeComplexPushforward.derivedCategoryB_isQuasicoherent_single` and
  `derivedCategoryB_isQuasicoherent_single_shift`: a quasi-coherent module on a scheme, placed in
  a degree and shifted, lies in `D_QCoh`.
* `Stacks.RelativeComplexPushforward.adjunctionTensorMap_transport`: the abstract morphism of
  `CategoryTheory.adjunctionTensorMap` is **carried along a transport of its adjunction**, the
  single-tensor analogue of
  `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_transport`.

Both tensor products are written in the order in which the morphism of [Stacks, Tag 0B53]
produces them, which is the opposite of the source's; the two orders are identified by the
symmetry of the two tensor products.

## Implementation notes

Conclusions (4) and (5) use the *unbounded* `Rf_*` of [Stacks, Tag 079W] rather than the right
derived functor on `D⁺` used by conclusion (2) above, because that is the functor the morphism
of [Stacks, Tag 0B53] is built from. The one input beyond the dévissage is the case of a single
quasi-coherent sheaf, which the source settles by citing [Stacks, Tag 08EU], and it is proved
here, so conclusion (5) holds with no hypothesis beyond the tag's own.

*The source's reduction to an affine base.* The dévissage itself asks the complex to have
finitely many nonzero terms, while the tag asks only that it be *locally bounded*, which is
strictly weaker — on `S = ⨆_n Spec k` a complex may be bounded on each member of a cover with no
global bound. The gap is closed by `isIso_projectionFormulaMap_of_isLocallyBounded`: invertibility
in `D(𝒪_S)` is local on an open cover, restriction to an open is the derived pullback along its
inclusion, and the base change of `a'` along that inclusion is an open immersion whose image lies
in the preimage of the open; over an affine — more generally quasi-compact — open that preimage
is quasi-compact because `f` is, so a locally bounded complex is bounded there and the dévissage
applies to its pullback. Conclusion (5) is therefore stated at a locally bounded `F^•`.

Conclusion (4) is too, and needs one thing more. It compares the *ordinary* tensor complex
`F^• ⊗_{a^{-1}𝒪_S} a^{-1}𝒢` with the derived one, which asks `F^•` to be K-flat; for a complex
with finitely many nonzero terms that is [Stacks, Tag 06YQ], bounded above with flat terms, and a
locally bounded complex need not be bounded above. What replaces 06YQ is
`Stacks.Cohomology.LocallyBoundedKFlat.kFlat_of_isLocallyBounded_of_flat`, that same tag with its
boundedness hypothesis localized: acyclicity of a complex of modules is local on an open cover and
the total tensor complex commutes with restriction to an open subspace, so it is enough that the
complex be bounded above after restriction to each member of a cover. Flatness of the terms, which
the source assumes, is exactly what this consumes, and so is kept in conclusion (4) and not in
conclusion (5).

*How that case is settled.* It is the crossing from the morphism of ringed spaces
`a' : (X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)` to the morphism of schemes `f`, and it has three ingredients.
The morphism of ringed spaces underlying `f` factors as `b : (X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` followed
by `a'` (`Stacks.DeRhamDirectImage.toInverseImageBase_comp`), so the compatibility of the morphism
of [Stacks, Tag 0B53] with a composite — `isIso_projectionFormulaMap_of_comp` below, whose
abstract half is `adjunctionTensorMap_transport` and whose geometric inputs are
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp` and
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp` — reduces the morphism
for `a'` at `Rb_*E` to the morphism for `b ≫ a'` together with the morphism for `b`. The first
is [Stacks, Tag 08EU] in full,
`Stacks.Cohomology.ProjectionFormulaGeneralBase.isIso_projectionFormulaMap_of_isQuasicoherent`.
The second is `isIso_projectionFormulaMap_toInverseImageBase`, which needs no hypothesis at all:
`b` is the identity on the underlying space, so it is [Stacks, Tag 0B55]; mathematically this is
the identification of [Stacks, Tag 08DE] that the source cites at this point. The whole crossing
is `isIso_projectionFormulaMap_single_relativeBase`.

Conclusion (5) then carries `K ∈ D_QCoh(𝒪_S)`, which is the tag's own hypothesis on `K`, and
conclusion (4) carries quasi-coherence of `𝒢`, which is the tag's own hypothesis there. The
conditional statements are kept beside the unconditional ones as untagged general lemmas: they
are more general in `K` and in `𝒢`.

## References

* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped CategoryTheory.Prod
open Stacks.DeRhamDirectImage
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.CategoryTheory.ComponentwiseInvertibility
open Stacks.DerivedCategory.BoundedInduction
open Stacks.DerivedTensor.RingedSite

universe v₁ v₂ u₁ u₂ u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

namespace Stacks.RelativeComplexPushforward

/-! Sheaves of modules on a ringed space form an abelian, indeed a Grothendieck abelian,
category. Instance search does not cross the abbreviation, so the two instances are re-seated at
these binders; they are
`Stacks.DeRhamDirectImage.abelian_modules` and
`Stacks.DeRhamDirectImage.isGrothendieckAbelian_modules` of
`StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage`. -/

attribute [local instance] Stacks.DeRhamDirectImage.abelian_modules
  Stacks.DeRhamDirectImage.isGrothendieckAbelian_modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The projection formula in the source complex

Conclusions (4) and (5) of the tag are about the derived projection-formula morphism of
[Stacks, Tag 0B53] at the *flat morphism of ringed spaces* `a' : (X, a^{-1}𝒪_S) ⟶ (S, 𝒪_S)`,
read as a functor of the source complex `F^•`.  The dévissage of the source's proof — the
induction on `b - a` through a distinguished triangle — is carried out here for an arbitrary
morphism of ringed spaces, as the statement that the morphism is invertible at a complex with
finite support as soon as it is invertible at each term of the complex placed in its own degree
and shifted arbitrarily. -/

section SourceComplex

variable {Z W : RingedSpace.{u, u}} (g : Z ⟶ W)

/-- The functor `E ↦ Rg_*E ⊗^𝐋_{𝒪_W} K`, the source of the projection-formula morphism of
[Stacks, Tag 0B53] read in the source complex. -/
abbrev projectionFormulaSourceComplex (K : DerivedCategory (Modules W)) :
    DerivedCategory (Modules Z) ⥤ DerivedCategory (Modules W) :=
  derivedPushforward g ⋙ (derivedTensorProductFunctor W.sheaf).flip.obj K

/-- The functor `E ↦ Rg_*(E ⊗^𝐋_{𝒪_Z} Lg^*K)`, the target of the projection-formula morphism of
[Stacks, Tag 0B53] read in the source complex. -/
abbrev projectionFormulaTargetComplex (K : DerivedCategory (Modules W)) :
    DerivedCategory (Modules Z) ⥤ DerivedCategory (Modules W) :=
  (derivedTensorProductFunctor Z.sheaf).flip.obj ((derivedPullback g).obj K) ⋙
    derivedPushforward g

/-- **The projection-formula morphism of [Stacks, Tag 0B53] as a natural transformation in the
source complex.**  Its component at `E` is
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap g E K` and its naturality is
`projectionFormulaMap_natural_left`. -/
def projectionFormulaComplexTransformation (K : DerivedCategory (Modules W)) :
    projectionFormulaSourceComplex g K ⟶ projectionFormulaTargetComplex g K where
  app E := projectionFormulaMap g E K
  naturality _ _ e := projectionFormulaMap_natural_left g e K

/-- The component of `projectionFormulaComplexTransformation g K` at `E` is
`projectionFormulaMap g E K`. -/
@[simp]
lemma projectionFormulaComplexTransformation_app (K : DerivedCategory (Modules W))
    (E : DerivedCategory (Modules Z)) :
    (projectionFormulaComplexTransformation g K).app E = projectionFormulaMap g E K :=
  rfl

/-- `E ↦ Rg_*E ⊗^𝐋_{𝒪_W} K` commutes with the shift: `Rg_*` does, being the right adjoint of
`Lg^*`, and so does tensoring on the right by a fixed object, by the `commShift_left` datum of
the derived tensor product of [Stacks, Tag 06YU]. -/
@[instance_reducible]
def projectionFormulaSourceComplexCommShift (K : DerivedCategory (Modules W)) :
    (projectionFormulaSourceComplex g K).CommShift ℤ :=
  letI : (derivedPushforward g).CommShift ℤ := (derivedAdjunction g).rightAdjointCommShift ℤ
  letI : ((derivedTensorProductFunctor W.sheaf).flip.obj K).CommShift ℤ :=
    (canonicalDerivedTensorProduct W.sheaf).commShift_left K
  Functor.CommShift.comp _ _

/-- `E ↦ Rg_*(E ⊗^𝐋_{𝒪_Z} Lg^*K)` commutes with the shift. -/
@[instance_reducible]
def projectionFormulaTargetComplexCommShift (K : DerivedCategory (Modules W)) :
    (projectionFormulaTargetComplex g K).CommShift ℤ :=
  letI : (derivedPushforward g).CommShift ℤ := (derivedAdjunction g).rightAdjointCommShift ℤ
  letI : ((derivedTensorProductFunctor Z.sheaf).flip.obj
      ((derivedPullback g).obj K)).CommShift ℤ :=
    (canonicalDerivedTensorProduct Z.sheaf).commShift_left _
  Functor.CommShift.comp _ _

/-- `E ↦ Rg_*E ⊗^𝐋_{𝒪_W} K` is exact: it is the composite of `Rg_*`, the right adjoint of the
exact functor `Lg^*`, with tensoring on the right by a fixed object, which is the `exact_left`
datum of the derived tensor product of [Stacks, Tag 06YU]. -/
theorem projectionFormulaSourceComplex_isTriangulated (K : DerivedCategory (Modules W)) :
    letI := projectionFormulaSourceComplexCommShift g K
    (projectionFormulaSourceComplex g K).IsTriangulated := by
  let : (derivedPushforward g).CommShift ℤ := (derivedAdjunction g).rightAdjointCommShift ℤ
  let : (derivedAdjunction g).CommShift ℤ := (derivedAdjunction g).commShift_of_leftAdjoint ℤ
  have : (derivedPushforward g).IsTriangulated :=
    (derivedAdjunction g).isTriangulated_rightAdjoint
  let : ((derivedTensorProductFunctor W.sheaf).flip.obj K).CommShift ℤ :=
    (canonicalDerivedTensorProduct W.sheaf).commShift_left K
  have : ((derivedTensorProductFunctor W.sheaf).flip.obj K).IsTriangulated :=
    (canonicalDerivedTensorProduct W.sheaf).exact_left K
  exact inferInstance

/-- `E ↦ Rg_*(E ⊗^𝐋_{𝒪_Z} Lg^*K)` is exact. -/
theorem projectionFormulaTargetComplex_isTriangulated (K : DerivedCategory (Modules W)) :
    letI := projectionFormulaTargetComplexCommShift g K
    (projectionFormulaTargetComplex g K).IsTriangulated := by
  let : (derivedPushforward g).CommShift ℤ := (derivedAdjunction g).rightAdjointCommShift ℤ
  let : (derivedAdjunction g).CommShift ℤ := (derivedAdjunction g).commShift_of_leftAdjoint ℤ
  have : (derivedPushforward g).IsTriangulated :=
    (derivedAdjunction g).isTriangulated_rightAdjoint
  let : ((derivedTensorProductFunctor Z.sheaf).flip.obj
      ((derivedPullback g).obj K)).CommShift ℤ :=
    (canonicalDerivedTensorProduct Z.sheaf).commShift_left _
  have : ((derivedTensorProductFunctor Z.sheaf).flip.obj
      ((derivedPullback g).obj K)).IsTriangulated :=
    (canonicalDerivedTensorProduct Z.sheaf).exact_left _
  exact inferInstance

/-- **The dévissage of the projection formula in the source complex.**  Let `g : Z ⟶ W` be an
arbitrary morphism of ringed spaces, `K` an object of `D(𝒪_W)` and `F` a complex of
`𝒪_Z`-modules with only finitely many nonzero terms.  If the projection-formula morphism of
[Stacks, Tag 0B53] is invertible at every shift of every term `F^i` of `F` placed in degree `i`,
then it is invertible at `F`.

This is the induction on the length of the complex of the source's proof of
[Stacks, Tag 0FML] (5), run through the stupid truncations by
`Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex`: both functors of the
source complex are exact, so invertibility at two vertices of a distinguished triangle spreads
to the third by
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts`. -/
theorem isIso_projectionFormulaMap_of_finite_support (K : DerivedCategory (Modules W))
    (F : CochainComplex (Modules Z) ℤ) (hF : {i : ℤ | ¬ IsZero (F.X i)}.Finite)
    (hsingle : ∀ i n : ℤ, IsIso (projectionFormulaMap g
      (((DerivedCategory.singleFunctor (Modules Z) i).obj (F.X i))⟦n⟧) K)) :
    IsIso (projectionFormulaMap g (DerivedCategory.Q.obj F) K) := by
  let := projectionFormulaSourceComplexCommShift g K
  let := projectionFormulaTargetComplexCommShift g K
  have := projectionFormulaSourceComplex_isTriangulated g K
  have := projectionFormulaTargetComplex_isTriangulated g K
  have h : ∀ n : ℤ, IsIso ((projectionFormulaComplexTransformation g K).app
      ((DerivedCategory.Q.obj F)⟦n⟧)) := by
    apply property_of_bounded_complex
      (fun A => ∀ n : ℤ, IsIso ((projectionFormulaComplexTransformation g K).app (A⟦n⟧)))
    · intro A B e hA n
      exact ((projectionFormulaComplexTransformation g K).isIso_app_iff_of_iso
        ((shiftFunctor _ n).mapIso e)).mp (hA n)
    · intro A hA n
      exact IsZero.isIso
        ((projectionFormulaSourceComplex g K).map_isZero ((shiftFunctor _ n).map_isZero hA))
        ((projectionFormulaTargetComplex g K).map_isZero ((shiftFunctor _ n).map_isZero hA)) _
    · intro S hS h₁ h₃
      exact isIso_app_middle_of_all_shifts (projectionFormulaSourceComplex g K)
        (projectionFormulaTargetComplex g K) (projectionFormulaComplexTransformation g K)
        (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃
    · exact hF
    · exact hsingle
  exact ((projectionFormulaComplexTransformation g K).isIso_app_iff_of_iso
    ((shiftFunctorZero _ ℤ).app (DerivedCategory.Q.obj F))).mp (h 0)

open Stacks.Cohomology.ProjectionFormulaPerfect

/-- **The dévissage of the projection formula in the source complex, at a merely *locally
bounded* complex.**  Let `g : Z ⟶ W` be a morphism of ringed spaces, `K` an object of `D(𝒪_W)`
and `F` a locally bounded complex of `𝒪_Z`-modules.  Suppose `W` is covered by opens `V j` whose
preimages in `Z` are quasi-compact.  If the projection-formula morphism of [Stacks, Tag 0B53] is
invertible at every shift of every term `F^i` of `F` placed in degree `i`, then it is invertible
at `F`.

This is the source's reduction to an affine base, carried out.  Invertibility in `D(𝒪_W)` is
local on the cover (`Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map`), and
restriction to `V j` is the derived pullback along the inclusion of that open subspace
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`).  The base change
of `g` along that inclusion, taken as a genuine fibre product of ringed spaces, has its first
projection `g'` an open immersion whose image lies in the preimage of `V j`; so
`Stacks.Cohomology.LocallyBoundedPullback.finite_support_modulePullback_of_isLocallyBounded`
turns the local boundedness of `F` into a global bound on `(g')^*F`, and
`isIso_projectionFormulaMap_of_finite_support` applies to `(g')^*F` over the base change.  The
two passages between the square's two vertical arrows are
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_derivedPullback_map_projectionFormulaMap` and
its converse `…isIso_projectionFormulaMap_of_isIso_derivedPullback_map`, which is what carries
the hypothesis at the terms, proved over the whole of `W`, down to the base change.

No hypothesis is placed on `K` or on the terms of `F`; in particular `g` need not be
quasi-compact — the quasi-compactness of the preimages is asked of the cover instead. -/
theorem isIso_projectionFormulaMap_of_isLocallyBounded (K : DerivedCategory (Modules W))
    (F : CochainComplex (Modules Z) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded Z F)
    {ι : Type*} (V : ι → Opens W.carrier) (hV : iSup V = ⊤)
    (hcpt : ∀ j : ι,
      IsCompact ((((Opens.map g.hom.base).obj (V j)) : Opens Z.carrier) : Set Z.carrier))
    (hsingle : ∀ i n : ℤ, IsIso (projectionFormulaMap g
      (((DerivedCategory.singleFunctor (Modules Z) i).obj (F.X i))⟦n⟧) K)) :
    IsIso (projectionFormulaMap g (DerivedCategory.Q.obj F) K) := by
  refine Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map
    (structureSheafRing W) V hV _ fun j => ?_
  refine (NatIso.isIso_map_iff
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso W (V j))
    (projectionFormulaMap g (DerivedCategory.Q.obj F) K)).mp ?_
  set e := W.ofRestrict (V j).isOpenEmbedding with he
  have sq : IsPullback (pullback.fst g e) (pullback.snd g e) g e :=
    IsPullback.of_hasPullback g e
  have hrange : Set.range (pullback.fst g e).hom.base ⊆
      ((((Opens.map g.hom.base).obj (V j)) : Opens Z.carrier) : Set Z.carrier) := by
    rintro z ⟨p, rfl⟩
    have hmem : (pullback.fst g e ≫ g).hom.base p ∈ ((V j : Opens W.carrier) : Set W.carrier) := by
      rw [sq.w]
      exact (Stacks.DerivedGlueing.range_ofRestrict (V j)).le
        (Stacks.DerivedGlueing.range_comp_subset_range (pullback.snd g e).hom.base e.hom.base
          ⟨p, rfl⟩)
    exact hmem
  refine isIso_derivedPullback_map_projectionFormulaMap
    (pullback.fst g e) (pullback.snd g e) g e sq (DerivedCategory.Q.obj F) K ?_
  refine isIso_projectionFormulaMap_of_iso_left (pullback.snd g e)
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionComplexIso
      (pullback.fst g e) F).symm _ ?_
  refine isIso_projectionFormulaMap_of_finite_support (pullback.snd g e) _
    (((RingedSpaceModuleAdjunction.modulePullback
      (pullback.fst g e)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (Stacks.Cohomology.LocallyBoundedPullback.finite_support_modulePullback_of_isLocallyBounded
      (pullback.fst g e) F hF _ (hcpt j) hrange) fun i n => ?_
  refine isIso_projectionFormulaMap_of_iso_left (pullback.snd g e)
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionSingleShiftIso
      (pullback.fst g e) i n (F.X i)) _ ?_
  exact isIso_projectionFormulaMap_of_isIso_derivedPullback_map
    (pullback.fst g e) (pullback.snd g e) g e sq _ K
    (@Functor.map_isIso _ _ _ _ _ _ _ _ (hsingle i n))

end SourceComplex

/-! ### The projection formula at a single quasi-coherent sheaf

The source settles conclusion (5) for a complex concentrated in one degree by crossing from the
morphism of ringed spaces `a' : (X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)` to the morphism of schemes `f` and
citing [Stacks, Tag 08EU] there.  The crossing is the factorization
`b : (X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` followed by `a'`, which is `f` — the content of
`Stacks.DeRhamDirectImage.toInverseImageBase_comp` — together with the fact that the
projection-formula morphism at `b` is invertible, which is [Stacks, Tag 0B55] because `b` is the
identity on the underlying space.  The three ingredients are assembled here. -/

section SingleSheaf

/-- **The projection-formula morphism of [Stacks, Tag 0B53] at
`b : (X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` is invertible**, for arbitrary complexes on either side.  The
underlying map of spaces of `b` is the identity, hence a homeomorphism onto a closed subset, so
this is [Stacks, Tag 0B55] in the form
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`.

Mathematically this is the identification of [Stacks, Tag 08DE] that the source's proof of
[Stacks, Tag 0FML] (5) uses at a single quasi-coherent sheaf: it says that tensoring over
`f^{-1}𝒪_S` with `f^{-1}K` and tensoring over `𝒪_X` with `Lf^*K` agree. -/
theorem isIso_projectionFormulaMap_toInverseImageBase
    (E : DerivedCategory (Modules X.toRingedSpace))
    (L : DerivedCategory (Modules (inverseImageBase f))) :
    IsIso (projectionFormulaMap (toInverseImageBase f) E L) :=
  isIso_projectionFormulaMap_of_isClosedEmbedding (toInverseImageBase f)
    Topology.IsClosedEmbedding.id E L

/-- The morphism of ringed spaces `(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` is the identity on the underlying
space. -/
theorem isIso_base_toInverseImageBase : IsIso (toInverseImageBase f).hom.base :=
  inferInstanceAs (IsIso (𝟙 X.carrier))

/-- **`Rb_*` of a module placed in degree `i` and shifted by `n`**, for
`b : (X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)`: it is the restriction of scalars of that module along
`f^{-1}𝒪_S ⟶ 𝒪_X`, in the same degree and with the same shift.  Restriction of scalars is exact,
so `Rb_*` is the functor it induces on derived categories, which is
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`; the shift and the degree are
then `CategoryTheory.Functor.commShiftIso` and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
def derivedPushforwardToInverseImageBaseSingleShiftIso (N : X.Modules) (i n : ℤ) :
    (derivedPushforward (toInverseImageBase f)).obj
        (((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N)⟦n⟧) ≅
      ((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
        ((pushforward (toInverseImageBase f)).obj N))⟦n⟧ :=
  haveI := isIso_base_toInverseImageBase f
  (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
        (RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f))).symm.app _ ≪≫
    ((RingedSpaceModuleAdjunction.modulePushforward
      (toInverseImageBase f)).mapDerivedCategory.commShiftIso n).app _ ≪≫
      (shiftFunctor (DerivedCategory (Modules (inverseImageBase f))) n).mapIso
        ((Functor.mapDerivedCategorySingleFunctor
          (RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)) i).app N)

/-- **A quasi-coherent module on a scheme, placed in an arbitrary degree, lies in
`D_QCoh`.**  Its cohomology sheaves are the module itself in that degree and zero in the others,
and the quasi-coherent modules form a weak Serre subcategory, so they contain the zero sheaf. -/
theorem derivedCategoryB_isQuasicoherent_single {Y : Scheme.{u}} (N : Y.Modules)
    (hN : N.IsQuasicoherent) (i : ℤ) :
    DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) i).obj N) := by
  have hB := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre Y
  intro m
  by_cases hm : m = i
  · subst hm
    exact hB.isClosedUnderIsomorphisms.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Y.toRingedSpace) m).app
        N).symm hN
  · have e : (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) m).obj
          ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) i).obj N) ≅
        ((HomologicalComplex.single (Modules Y.toRingedSpace) (ComplexShape.up ℤ) i).obj
          N).homology m :=
      (DerivedCategory.homologyFunctorFactors (Modules Y.toRingedSpace) m).app _
    exact DerivedCategoryB.zero_mem_of_isWeakSerre _ hB _
      (IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology
        (ComplexShape.up ℤ) i N m hm) e)

/-- **A quasi-coherent module on a scheme, placed in an arbitrary degree and shifted
arbitrarily, lies in `D_QCoh`**: `D_QCoh` is stable under the shift, the quasi-coherent modules
being a weak Serre subcategory. -/
theorem derivedCategoryB_isQuasicoherent_single_shift {Y : Scheme.{u}} (N : Y.Modules)
    (hN : N.IsQuasicoherent) (i n : ℤ) :
    DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      (((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) i).obj N)⟦n⟧) :=
  DerivedCategoryB.derivedCategoryB_shift_mem _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre Y) n
    (derivedCategoryB_isQuasicoherent_single N hN i)

end SingleSheaf

/-! ### The projection formula and composition of morphisms of ringed spaces

The crossing from `a'` to `f` is the compatibility of the morphism of [Stacks, Tag 0B53] with a
composite of morphisms of ringed spaces: for `g : Z ⟶ W` and `h : W ⟶ V`, the morphism for
`g ≫ h` is the morphism for `h` at `Rg_*E`, followed by `Rh_*` of the morphism for `g`, read
through the composition isomorphisms of [Stacks, Tag 0D5S] and [Stacks, Tag 0D5T].  That is the
single-tensor analogue of
`Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_comp'`, and it is assembled from
the same two inputs:
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp` and
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp`. -/

section CompositionOfMorphisms

/-- **The abstract projection-formula morphism of `CategoryTheory.adjunctionTensorMap` is carried
along a transport of its adjunction.**  Let `adj'` be `adj` transported along `cl : L ≅ L'` and
`cr : R ≅ R'`, and let the comparison `α'` be `α` conjugated by `cl`.  Then the morphism for
`adj'` is the morphism for `adj` read through `cr` on the source and through `cr` and `cl` on the
target.

This is the single-tensor analogue of
`Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_transport`; the extra `cl` on
the target is there because the second argument of the target bifunctor is `L H`, which moves
with the transport, whereas in the doubled-counit morphism both arguments come from `D`.

Both sides are adjoint transposes under `adj'`, so it suffices to compare the morphisms they
transpose, which is
`Stacks.AlgebraicGeometry.ProjectionFormula.eq_adjunctionTensorMap_of_map_comp_counit`. -/
theorem adjunctionTensorMap_transport {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L L' : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (cl : L ≅ L') (cr : R ≅ R') (A : C × C ⥤ C) (B : D × D ⥤ D)
    (α : A ⋙ L ⟶ L.prod L ⋙ B) (α' : A ⋙ L' ⟶ L'.prod L' ⋙ B)
    (hadj : (adj.ofNatIsoLeft cl).ofNatIsoRight cr = adj')
    (hα : Functor.whiskerLeft A cl.hom ≫ α' =
      α ≫ Functor.whiskerRight (NatTrans.prod cl.hom cl.hom) B)
    (G : D) (H : C) :
    A.map (cr.hom.app G ×ₘ 𝟙 H) ≫ CategoryTheory.adjunctionTensorMap adj' A B α' G H =
      CategoryTheory.adjunctionTensorMap adj A B α G H ≫
        cr.hom.app (B.obj (G, L.obj H)) ≫ R'.map (B.map (𝟙 G ×ₘ cl.hom.app H)) := by
  have hαpt : cl.hom.app (A.obj (R'.obj G, H)) ≫ α'.app (R'.obj G, H) =
      α.app (R'.obj G, H) ≫ B.map (cl.hom.app (R'.obj G) ×ₘ cl.hom.app H) :=
    NatTrans.congr_app hα (R'.obj G, H)
  have ha := α.naturality (cr.hom.app G ×ₘ 𝟙 H)
  change L.map (A.map (cr.hom.app G ×ₘ 𝟙 H)) ≫ α.app (R'.obj G, H) =
    α.app (R.obj G, H) ≫ B.map (L.map (cr.hom.app G) ×ₘ L.map (𝟙 H)) at ha
  have hctr : L.map (cr.hom.app G) ≫ cl.hom.app (R'.obj G) ≫
      ((adj.ofNatIsoLeft cl).ofNatIsoRight cr).counit.app G = adj.counit.app G := by
    rw [NatTrans.naturality_assoc]
    simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  subst hadj
  unfold CategoryTheory.adjunctionTensorMap
  rw [← Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply,
    (cr.hom.naturality (B.map (𝟙 G ×ₘ cl.hom.app H))).symm,
    ← Category.assoc _ (R.map (B.map (𝟙 G ×ₘ cl.hom.app H)))
      (cr.hom.app (B.obj (G, L'.obj H))),
    ← Adjunction.homEquiv_naturality_right]
  refine congrArg (fun z => z ≫ cr.hom.app (B.obj (G, L'.obj H))) ?_
  rw [Equiv.apply_eq_iff_eq,
    ← reassoc_of% (cl.hom.naturality (A.map (cr.hom.app G ×ₘ 𝟙 H))),
    reassoc_of% hαpt, reassoc_of% ha]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 2
  apply Prod.hom_ext
  · simp only [CategoryTheory.prod_comp, hctr, Category.comp_id]
  · simp only [CategoryTheory.prod_comp, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]

/-- **The projection-formula morphism of [Stacks, Tag 0B53] for the outer factor of a composite
is invertible as soon as it is for the composite and for the inner factor.**  For morphisms of
ringed spaces `g : Z ⟶ W` and `h : W ⟶ V`, the morphism for `g ≫ h` at `E` is the morphism for
`h` at `Rg_*E` followed by `Rh_*` of the morphism for `g` at `Lh^*M`, read through the
composition isomorphisms of [Stacks, Tag 0D5S] and [Stacks, Tag 0D5T]; so two of the three being
invertible forces the third.

The composite comparison is written as a whiskering, which is the shape
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp` supplies it in and the
shape `Stacks.AffineProjectionFormula.adjunctionTensorMap_comp_whiskered` consumes; see the
implementation note there for why the `Stacks.AffineProjectionFormula.comparisonComp` spelling
cannot be used at these binders. -/
theorem isIso_projectionFormulaMap_of_comp {Z W V : RingedSpace.{u, u}} (g : Z ⟶ W) (h : W ⟶ V)
    (E : DerivedCategory (Modules Z)) (M : DerivedCategory (Modules V))
    (hcomp : IsIso (projectionFormulaMap (g ≫ h) E M))
    (hinner : IsIso (projectionFormulaMap g E ((derivedPullback h).obj M))) :
    IsIso (projectionFormulaMap h ((derivedPushforward g).obj E) M) := by
  have hα : Functor.whiskerLeft
        (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf))
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g h).hom ≫
      pullbackTensorComparison (g ≫ h) =
    (Functor.whiskerRight (pullbackTensorComparison h) (derivedPullback g) ≫
        Functor.whiskerLeft ((derivedPullback h).prod (derivedPullback h))
          (pullbackTensorComparison g)) ≫
      Functor.whiskerRight
        (NatTrans.prod
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g h).hom
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g h).hom)
        (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)) :=
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp g h).trans
      (Category.assoc _ _ _).symm
  have htr := adjunctionTensorMap_transport
    ((derivedAdjunction h).comp (derivedAdjunction g)) (derivedAdjunction (g ≫ h))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g h)
    (derivedPushforwardCompIso g h)
    (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf))
    (Functor.whiskerRight (pullbackTensorComparison h) (derivedPullback g) ≫
      Functor.whiskerLeft ((derivedPullback h).prod (derivedPullback h))
        (pullbackTensorComparison g))
    (pullbackTensorComparison (g ≫ h)) (derivedAdjunction_comp g h) hα E M
  rw [Stacks.AffineProjectionFormula.adjunctionTensorMap_comp_whiskered] at htr
  have hL : IsIso ((Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf)).map
      ((derivedPushforwardCompIso g h).hom.app E ×ₘ 𝟙 M) ≫
        CategoryTheory.adjunctionTensorMap (derivedAdjunction (g ≫ h))
          (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf))
          (pullbackTensorComparison (g ≫ h)) E M) := by
    refine IsIso.comp_isIso' ?_ hcomp
    exact ((Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf)).mapIso
      (Iso.prod ((derivedPushforwardCompIso g h).app E) (Iso.refl M))).isIso_hom
  rw [htr] at hL
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ ?_
    (@IsIso.of_isIso_comp_right _ _ _ _ _ _ _ ?_ hL)
  · exact ((derivedPushforward h).mapIso (@asIso _ _ _ _ _ hinner)).isIso_hom
  · refine IsIso.comp_isIso' (((derivedPushforwardCompIso g h).app _).isIso_hom) ?_
    exact ((derivedPushforward (g ≫ h)).mapIso
      ((Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).mapIso
        (Iso.prod (Iso.refl E)
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g
            h).app M)))).isIso_hom

end CompositionOfMorphisms

/-! ### The hypothesis at a single quasi-coherent sheaf, discharged -/

/-- **The hypothesis `hprojformula` of conclusions (4) and (5), proved.**  For `f : X ⟶ S`
quasi-compact and quasi-separated, `K` in `D_QCoh(𝒪_S)` and `N` a quasi-coherent `𝒪_X`-module,
the projection-formula morphism of [Stacks, Tag 0B53] at the morphism of ringed spaces
`a' : (X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)` is invertible at `N` placed in an arbitrary degree and shifted
arbitrarily.

This is the crossing from `a'` to `f` that the source's proof performs.  The morphism of ringed
spaces underlying `f` factors as `b : (X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` followed by `a'`, which is
`Stacks.DeRhamDirectImage.toInverseImageBase_comp`, and
`isIso_projectionFormulaMap_of_comp` turns the morphism for that composite into the morphism for
`a'` at `Rb_*` of the source complex, given the morphism for `b`.  The morphism for the composite
is [Stacks, Tag 08EU] in full —
`Stacks.Cohomology.ProjectionFormulaGeneralBase.isIso_projectionFormulaMap_of_isQuasicoherent`,
whose two quasi-coherence hypotheses are `derivedCategoryB_isQuasicoherent_single_shift` and
`hK` — and the morphism for `b` is `isIso_projectionFormulaMap_toInverseImageBase`, which is
[Stacks, Tag 0B55] because `b` is the identity on the underlying space and is the identification
of [Stacks, Tag 08DE] that the source cites here.  Finally `Rb_*(N[i]⟦n⟧)` is `(b_*N)[i]⟦n⟧` by
`derivedPushforwardToInverseImageBaseSingleShiftIso`. -/
@[sga "6 III 3.7" "special case"]
theorem isIso_projectionFormulaMap_single_relativeBase [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Modules S.toRingedSpace))
    (hK : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) K)
    (N : X.Modules) (hN : N.IsQuasicoherent) (i n : ℤ) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
        ((pushforward (toInverseImageBase f)).obj N))⟦n⟧) K) := by
  have h08 :=
    Stacks.Cohomology.ProjectionFormulaGeneralBase.isIso_projectionFormulaMap_of_isQuasicoherent
      f (((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N)⟦n⟧)
      (derivedCategoryB_isQuasicoherent_single_shift N hN i n) K hK
  rw [← toInverseImageBase_comp f] at h08
  refine isIso_projectionFormulaMap_of_iso_left (inverseImageBaseProjection f)
    (derivedPushforwardToInverseImageBaseSingleShiftIso f N i n) K ?_
  exact isIso_projectionFormulaMap_of_comp (toInverseImageBase f)
    (inverseImageBaseProjection f)
    (((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N)⟦n⟧) K h08
    (isIso_projectionFormulaMap_toInverseImageBase f _ _)

/-- If the projection-formula morphism is invertible at every quasi-coherent module `N` placed in
a degree and shifted, then it is so at every term of `F` placed in a degree and shifted, the terms
of `F` being such modules. -/
private theorem isIso_projectionFormulaMap_single_of_iso [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Modules S.toRingedSpace))
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (hprojformula : ∀ N : X.Modules, N.IsQuasicoherent → ∀ i n : ℤ,
      IsIso (projectionFormulaMap (inverseImageBaseProjection f)
        (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
          ((pushforward (toInverseImageBase f)).obj N))⟦n⟧) K)) (i n : ℤ) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj (F.X i))⟦n⟧) K) :=
  isIso_projectionFormulaMap_of_iso_left _
    ((shiftFunctor _ n).mapIso
      ((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).mapIso
        (hFM i))).symm K (hprojformula (M i) (hM i) i n)

/-! ### Conclusion (5) -/

/-- **Stacks Project, Tag 0FML, conclusion (5)**, the dévissage carried out.  Let `f : X ⟶ S` be
a quasi-compact and quasi-separated morphism of schemes, let `K` be an object of `D(𝒪_S)`, and
let `F` be a complex of `f^{-1}𝒪_S`-modules with finitely many nonzero terms, the term in degree
`i` being the restriction of scalars of a quasi-coherent `𝒪_X`-module `M i` — the differentials
being only `f^{-1}𝒪_S`-linear.  Then the projection-formula morphism of [Stacks, Tag 0B53] at
the morphism of ringed spaces `(X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)`,

`Rf_*F ⊗^𝐋_{𝒪_S} K ⟶ Rf_*(F ⊗^𝐋_{f^{-1}𝒪_S} Lf^*K)`,

is an isomorphism, granted that it is so when `F` is a single quasi-coherent sheaf placed in an
arbitrary degree and shifted arbitrarily, which is the hypothesis `hprojformula`.

`hprojformula` is the case of the source's proof that it settles by citing [Stacks, Tag 08EU]:
for a single quasi-coherent `𝒪_X`-module `N`, the direct images of `N` along `(X, f^{-1}𝒪_S) ⟶ S`
and along `f` agree, and the projection-formula morphism becomes the one of that tag.  It is the
only input: everything else is the dévissage, which
`isIso_projectionFormulaMap_of_finite_support` performs with no hypothesis.

The hypothesis is proved, for `K` in `D_QCoh(𝒪_S)`, as
`isIso_projectionFormulaMap_single_relativeBase`; the unconditional form of this statement is
`isIso_projectionFormulaMap_relativeComplex_of_isQuasicoherent` below, which is the one carrying
the tag.  This conditional form is kept, untagged, because it is more general in `K`: it asks
nothing of `K` beyond what the hypothesis supplies. -/
theorem isIso_projectionFormulaMap_relativeComplex [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Modules S.toRingedSpace))
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : {i : ℤ | ¬ IsZero (F.X i)}.Finite)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (hprojformula : ∀ N : X.Modules, N.IsQuasicoherent → ∀ i n : ℤ,
      IsIso (projectionFormulaMap (inverseImageBaseProjection f)
        (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
          ((pushforward (toInverseImageBase f)).obj N))⟦n⟧) K)) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj F) K) := by
  exact isIso_projectionFormulaMap_of_finite_support (inverseImageBaseProjection f) K F hF
    (isIso_projectionFormulaMap_single_of_iso f K F M hM hFM hprojformula)

/-- **Stacks Project, Tag 0FML, conclusion (5)** read as an isomorphism,

`Rf_*F^• ⊗^𝐋_{𝒪_S} K ≅ Rf_*(F^• ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)`,

the two tensor products being written in the order the morphism of [Stacks, Tag 0B53] produces
them, which is the opposite of the source's.  The hypotheses are those of
`isIso_projectionFormulaMap_relativeComplex`. -/
def relativeComplexProjectionFormulaIso [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Modules S.toRingedSpace))
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : {i : ℤ | ¬ IsZero (F.X i)}.Finite)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (hprojformula : ∀ N : X.Modules, N.IsQuasicoherent → ∀ i n : ℤ,
      IsIso (projectionFormulaMap (inverseImageBaseProjection f)
        (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
          ((pushforward (toInverseImageBase f)).obj N))⟦n⟧) K)) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj K ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj F)).obj
          ((derivedPullback (inverseImageBaseProjection f)).obj K)) :=
  have := isIso_projectionFormulaMap_relativeComplex f K F hF M hM hFM hprojformula
  asIso (projectionFormulaMap (inverseImageBaseProjection f) (DerivedCategory.Q.obj F) K)

/-- **Stacks Project, Tag 0FML, conclusion (5)**, with no hypothesis beyond the tag's own.  For
`f : X ⟶ S` quasi-compact and quasi-separated, `K` an object of `D_QCoh(𝒪_S)` and `F` a complex
of `f^{-1}𝒪_S`-modules with finitely many nonzero terms, the term in degree `i` being the
restriction of scalars of a quasi-coherent `𝒪_X`-module `M i`, the projection-formula morphism of
[Stacks, Tag 0B53] at `(X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)` is an isomorphism.

`isIso_projectionFormulaMap_relativeComplex` above with its hypothesis discharged by
`isIso_projectionFormulaMap_single_relativeBase`.  The quasi-coherence of `K` is the tag's own
hypothesis in conclusion (5); the conditional statement above is kept because it is more general
in `K`. -/
theorem isIso_projectionFormulaMap_relativeComplex_of_isQuasicoherent [QuasiCompact f]
    [QuasiSeparated f] (K : DerivedCategory (Modules S.toRingedSpace))
    (hK : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) K)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : {i : ℤ | ¬ IsZero (F.X i)}.Finite)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj F) K) :=
  isIso_projectionFormulaMap_relativeComplex f K F hF M hM hFM
    fun N hN i n => isIso_projectionFormulaMap_single_relativeBase f K hK N hN i n

/-- **Stacks Project, Tag 0FML, conclusion (5)** read as an isomorphism and with no hypothesis
beyond the tag's own,

`Rf_*F^• ⊗^𝐋_{𝒪_S} K ≅ Rf_*(F^• ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)`

for `K` in `D_QCoh(𝒪_S)`, the two tensor products being written in the order the morphism of
[Stacks, Tag 0B53] produces them. -/
def relativeComplexProjectionFormulaIsoOfIsQuasicoherent [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Modules S.toRingedSpace))
    (hK : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) K)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : {i : ℤ | ¬ IsZero (F.X i)}.Finite)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj K ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj F)).obj
          ((derivedPullback (inverseImageBaseProjection f)).obj K)) :=
  relativeComplexProjectionFormulaIso f K F hF M hM hFM
    fun N hN i n => isIso_projectionFormulaMap_single_relativeBase f K hK N hN i n

/-! ### Conclusion (5) at a merely locally bounded complex

The tag's hypothesis on `𝓕^•` is that it be *locally bounded*, which is strictly weaker than
having finitely many nonzero terms: on `Y = ⨆_n Spec k` the complex `⨁_n` of the de Rham
complexes of `𝔸^n_k` is locally bounded with no global bound.  The statements above are
therefore not yet the tag, and the statements here are:
`isIso_projectionFormulaMap_of_isLocallyBounded` carries out the source's reduction to an affine
base, over which the complex acquires a bound
because the preimage of an affine open under a quasi-compact morphism is quasi-compact
(`AlgebraicGeometry.Scheme.Hom.isCompact_preimage`) and a locally bounded complex is bounded on
a compact open
(`Stacks.SheafOfModules.OnSpace.isBoundedOn_of_isLocallyBounded_of_isCompact`). -/

/-- **Stacks Project, Tag 0FML, conclusion (5)** for a *locally bounded* `F`, the dévissage and
the reduction to an affine base both carried out.  Everything is as in
`isIso_projectionFormulaMap_relativeComplex` except that `F` is only assumed locally bounded,
which is the tag's own hypothesis; the hypothesis `hprojformula` is again the only input beyond
the formal argument, and it is proved as
`isIso_projectionFormulaMap_single_relativeBase`.

The affine opens of `S` are the cover fed to
`isIso_projectionFormulaMap_of_isLocallyBounded`: they cover `S`
(`AlgebraicGeometry.iSup_affineOpens_eq_top`), and the preimage of one of them is quasi-compact
because `f` is. -/
theorem isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded [QuasiCompact f]
    [QuasiSeparated f] (K : DerivedCategory (Modules S.toRingedSpace))
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (hprojformula : ∀ N : X.Modules, N.IsQuasicoherent → ∀ i n : ℤ,
      IsIso (projectionFormulaMap (inverseImageBaseProjection f)
        (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
          ((pushforward (toInverseImageBase f)).obj N))⟦n⟧) K)) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj F) K) := by
  refine isIso_projectionFormulaMap_of_isLocallyBounded (inverseImageBaseProjection f) K F hF
    (fun V : S.affineOpens => (V : S.Opens)) (AlgebraicGeometry.iSup_affineOpens_eq_top S)
    (fun V => f.isCompact_preimage V.2.isCompact)
    (isIso_projectionFormulaMap_single_of_iso f K F M hM hFM hprojformula)

/-- **Stacks Project, Tag 0FML, conclusion (5)** for a *locally bounded* `F`, read as an
isomorphism,

`Rf_*F^• ⊗^𝐋_{𝒪_S} K ≅ Rf_*(F^• ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)`,

the two tensor products being written in the order the morphism of [Stacks, Tag 0B53] produces
them.  The hypotheses are those of
`isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded`. -/
def relativeComplexProjectionFormulaIsoOfIsLocallyBounded [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Modules S.toRingedSpace))
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (hprojformula : ∀ N : X.Modules, N.IsQuasicoherent → ∀ i n : ℤ,
      IsIso (projectionFormulaMap (inverseImageBaseProjection f)
        (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
          ((pushforward (toInverseImageBase f)).obj N))⟦n⟧) K)) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj K ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj F)).obj
          ((derivedPullback (inverseImageBaseProjection f)).obj K)) :=
  have := isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded f K F hF M hM hFM
    hprojformula
  asIso (projectionFormulaMap (inverseImageBaseProjection f) (DerivedCategory.Q.obj F) K)

/-- **Stacks Project, Tag 0FML, conclusion (5)**, with no hypothesis beyond the tag's own.  For
`f : X ⟶ S` quasi-compact and quasi-separated, `K` an object of `D_QCoh(𝒪_S)` and `F` a *locally
bounded* complex of `f^{-1}𝒪_S`-modules, the term in degree `i` being the restriction of scalars
of a quasi-coherent `𝒪_X`-module `M i`, the projection-formula morphism of [Stacks, Tag 0B53] at
`(X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)` is an isomorphism.

`isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded` above with its hypothesis
discharged by `isIso_projectionFormulaMap_single_relativeBase`. -/
@[stacks 0FML "conclusion (5), with no hypothesis beyond the tag's own: for a quasi-compact \
quasi-separated morphism of schemes a : X ⟶ S, a LOCALLY BOUNDED complex F^• of a^{-1}O_S-modules \
each of whose terms carries a compatible quasi-coherent O_X-module structure, and K in \
D_QCoh(O_S), the Tag 0B53 map Ra_*F^• ⊗ᴸ_{O_S} K ⟶ Ra_*(F^• ⊗ᴸ_{a^{-1}O_S} L(a')^*K) is \
invertible. One difference from the source's phrasing, not a weakening: flatness of the terms, \
which the source assumes, is not needed for this conclusion and is not assumed. The two tensor \
factors are in the order the Tag 0B53 map produces them, which is the opposite of the source's"]
theorem isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded_of_isQuasicoherent
    [QuasiCompact f] [QuasiSeparated f] (K : DerivedCategory (Modules S.toRingedSpace))
    (hK : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) K)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    IsIso (projectionFormulaMap (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj F) K) :=
  isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded f K F hF M hM hFM
    fun N hN i n => isIso_projectionFormulaMap_single_relativeBase f K hK N hN i n

/-- **Stacks Project, Tag 0FML, conclusion (5)** read as an isomorphism and with no hypothesis
beyond the tag's own,

`Rf_*F^• ⊗^𝐋_{𝒪_S} K ≅ Rf_*(F^• ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}K)`

for `K` in `D_QCoh(𝒪_S)` and `F` locally bounded, the two tensor products being written in the
order the morphism of [Stacks, Tag 0B53] produces them. -/
@[stacks 0FML "conclusion (5) read as an isomorphism, with no hypothesis beyond the tag's own: \
Ra_*F^• ⊗ᴸ_{O_S} K is Ra_*(F^• ⊗ᴸ_{a^{-1}O_S} a^{-1}K) for K in D_QCoh(O_S) and F^• LOCALLY \
BOUNDED. The same single difference from the source's phrasing as in the invertibility form, \
not a weakening: flatness of the terms is not needed for this conclusion and is not assumed"]
def relativeComplexProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent [QuasiCompact f]
    [QuasiSeparated f] (K : DerivedCategory (Modules S.toRingedSpace))
    (hK : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) K)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj K ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj F)).obj
          ((derivedPullback (inverseImageBaseProjection f)).obj K)) :=
  relativeComplexProjectionFormulaIsoOfIsLocallyBounded f K F hF M hM hFM
    fun N hN i n => isIso_projectionFormulaMap_single_relativeBase f K hK N hN i n

/-! ### Conclusion (4) -/

/-- **Stacks Project, Tag 0FML, conclusion (4)**, the dévissage carried out: for `f : X ⟶ S`
quasi-compact and quasi-separated, `G` an `𝒪_S`-module and `F` a complex of `f^{-1}𝒪_S`-modules
with finitely many nonzero terms, each flat over `f^{-1}𝒪_S` and each the restriction of scalars
of a quasi-coherent `𝒪_X`-module,

`Rf_*F^• ⊗^𝐋_{𝒪_S} G ≅ Rf_*(F^• ⊗_{f^{-1}𝒪_S} f^{-1}G)`,

the tensor product on the right being the *ordinary* one.  The same hypothesis `hprojformula`
as in conclusion (5), at `K = G[0]`, is the only input.

The passage from (5) to (4) is the source's: `f^{-1}G` is `Lf^*(G[0])` because the morphism of
ringed spaces `(X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)` is flat — its germ maps are the comparisons
`𝒪_{S, f x} ⟶ (f^{-1}𝒪_S)_x`, which are isomorphisms, so its module pullback is exact and the
derived pullback is the degreewise one — and the ordinary tensor complex computes the derived one
because `F^•` is a bounded above complex of flats, hence K-flat by [Stacks, Tag 06YQ].
Quasi-coherence of `G` is not needed here: it is what makes `G[0]` lie in `D_QCoh(𝒪_S)`, which is
the hypothesis under which `hprojformula` is [Stacks, Tag 08EU]. -/
def relativeComplexOrdinaryProjectionFormulaIso [QuasiCompact f] [QuasiSeparated f]
    (G : Modules S.toRingedSpace)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : {i : ℤ | ¬ IsZero (F.X i)}.Finite)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase f).sheaf) (F.X i))
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (hprojformula : ∀ N : X.Modules, N.IsQuasicoherent → ∀ i n : ℤ,
      IsIso (projectionFormulaMap (inverseImageBaseProjection f)
        (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
          ((pushforward (toInverseImageBase f)).obj N))⟦n⟧)
        ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G))) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj
      ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G) ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj F).obj
            ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)))) :=
  have hbdd : ∃ n : ℤ, F.IsStrictlyLE n := by
    obtain ⟨b, hb⟩ := hF.bddAbove
    refine ⟨b, (CochainComplex.isStrictlyLE_iff F b).2 fun i hi => ?_⟩
    by_contra h
    exact absurd (hb h) (by omega)
  have hkflat : Stacks.SheafOfModules.KFlat.KFlat (inverseImageBase f).sheaf F :=
    Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat (R := (inverseImageBase f).sheaf) F
      hbdd hflat
  haveI : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_inverseImageModulePullback
      S.toRingedSpace f.base
  relativeComplexProjectionFormulaIso f _ F hF M hM hFM hprojformula ≪≫
    (derivedPushforward (inverseImageBaseProjection f)).mapIso
      (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj F)).mapIso
          (Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
              (inverseImageBaseProjection f) G ≪≫
            (DerivedCategory.singleFunctorIsoCompQ (Modules (inverseImageBase f)) 0).app
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)) ≪≫
        (canonicalDerivedTensorProduct (inverseImageBase f).sheaf).comparisonLeft F
          ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
            ((RingedSpaceModuleAdjunction.modulePullback
              (inverseImageBaseProjection f)).obj G)) hkflat)

/-- **Stacks Project, Tag 0FML, conclusion (4)**, with no hypothesis beyond the tag's own.  For
`f : X ⟶ S` quasi-compact and quasi-separated, `G` a *quasi-coherent* `𝒪_S`-module and `F` a
complex of `f^{-1}𝒪_S`-modules with finitely many nonzero terms, each flat over `f^{-1}𝒪_S` and
each the restriction of scalars of a quasi-coherent `𝒪_X`-module,

`Rf_*F^• ⊗^𝐋_{𝒪_S} G ≅ Rf_*(F^• ⊗_{f^{-1}𝒪_S} f^{-1}G)`,

the tensor product on the right being the *ordinary* one.

`relativeComplexOrdinaryProjectionFormulaIso` above with its hypothesis discharged by
`isIso_projectionFormulaMap_single_relativeBase` at `K = G[0]`, which lies in `D_QCoh(𝒪_S)` by
`derivedCategoryB_isQuasicoherent_single`.  Quasi-coherence of `G` is the tag's own hypothesis in
conclusion (4); the conditional statement above is kept because it is more general in `G`. -/
def relativeComplexOrdinaryProjectionFormulaIsoOfIsQuasicoherent [QuasiCompact f]
    [QuasiSeparated f] (G : Modules S.toRingedSpace) (hG : G.IsQuasicoherent)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : {i : ℤ | ¬ IsZero (F.X i)}.Finite)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase f).sheaf) (F.X i))
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj
      ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G) ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj F).obj
            ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)))) :=
  relativeComplexOrdinaryProjectionFormulaIso f G F hF hflat M hM hFM
    fun N hN i n => isIso_projectionFormulaMap_single_relativeBase f
      ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G)
      (derivedCategoryB_isQuasicoherent_single (Y := S) G hG 0) N hN i n

/-! ### Conclusion (4) at a merely locally bounded complex

Conclusion (4) compares the *ordinary* tensor complex `F^• ⊗_{f^{-1}𝒪_S} f^{-1}𝒢` with the
derived one, which asks `F^•` to be K-flat.  For a complex with finitely many nonzero terms that
is [Stacks, Tag 06YQ] — bounded above with flat terms — and a locally bounded complex need not be
bounded above; what replaces 06YQ is
`Stacks.Cohomology.LocallyBoundedKFlat.kFlat_of_isLocallyBounded_of_flat`, which is 06YQ with its
boundedness hypothesis localized.  Everything else is the conclusion-(5) statement at a locally
bounded complex, `relativeComplexProjectionFormulaIsoOfIsLocallyBounded`. -/

/-- **Stacks Project, Tag 0FML, conclusion (4)** for a *locally bounded* `F`, the dévissage, the
reduction to an affine base and the comparison with the ordinary tensor product all carried out.
Everything is as in `relativeComplexOrdinaryProjectionFormulaIso` except that `F` is only
assumed locally bounded, which is the tag's own hypothesis.

Flatness of the terms is the tag's own hypothesis here and is what makes `F^•` K-flat, hence
what makes the ordinary tensor complex compute the derived one; with only local boundedness the
K-flatness is
`Stacks.Cohomology.LocallyBoundedKFlat.kFlat_of_isLocallyBounded_of_flat` rather than
[Stacks, Tag 06YQ]. -/
def relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBounded [QuasiCompact f]
    [QuasiSeparated f] (G : Modules S.toRingedSpace)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase f).sheaf) (F.X i))
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (hprojformula : ∀ N : X.Modules, N.IsQuasicoherent → ∀ i n : ℤ,
      IsIso (projectionFormulaMap (inverseImageBaseProjection f)
        (((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
          ((pushforward (toInverseImageBase f)).obj N))⟦n⟧)
        ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G))) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj
      ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G) ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj F).obj
            ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)))) :=
  have hkflat : Stacks.SheafOfModules.KFlat.KFlat (inverseImageBase f).sheaf F :=
    Stacks.Cohomology.LocallyBoundedKFlat.kFlat_of_isLocallyBounded_of_flat
      (inverseImageBase f) F hF hflat
  haveI : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_inverseImageModulePullback
      S.toRingedSpace f.base
  relativeComplexProjectionFormulaIsoOfIsLocallyBounded f _ F hF M hM hFM hprojformula ≪≫
    (derivedPushforward (inverseImageBaseProjection f)).mapIso
      (((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
            (DerivedCategory.Q.obj F)).mapIso
          (Stacks.Intersection.Diagonal.derivedPullbackSingleIsoOfFlat
              (inverseImageBaseProjection f) G ≪≫
            (DerivedCategory.singleFunctorIsoCompQ (Modules (inverseImageBase f)) 0).app
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)) ≪≫
        (canonicalDerivedTensorProduct (inverseImageBase f).sheaf).comparisonLeft F
          ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
            ((RingedSpaceModuleAdjunction.modulePullback
              (inverseImageBaseProjection f)).obj G)) hkflat)

/-- **Stacks Project, Tag 0FML, conclusion (4)**, with no hypothesis beyond the tag's own.  For
`f : X ⟶ S` quasi-compact and quasi-separated, `G` a *quasi-coherent* `𝒪_S`-module and `F` a
*locally bounded* complex of `f^{-1}𝒪_S`-modules, each term flat over `f^{-1}𝒪_S` and the
restriction of scalars of a quasi-coherent `𝒪_X`-module,

`Rf_*F^• ⊗^𝐋_{𝒪_S} G ≅ Rf_*(F^• ⊗_{f^{-1}𝒪_S} f^{-1}G)`,

the tensor product on the right being the *ordinary* one.

`relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBounded` above with its hypothesis
discharged by `isIso_projectionFormulaMap_single_relativeBase` at `K = G[0]`, which lies in
`D_QCoh(𝒪_S)` by `derivedCategoryB_isQuasicoherent_single`. -/
@[stacks 0FML "conclusion (4), with no hypothesis beyond the tag's own: for a quasi-compact \
quasi-separated morphism of schemes a : X ⟶ S, a LOCALLY BOUNDED complex F^• of a^{-1}O_S-modules \
each of whose terms is flat over a^{-1}O_S and carries a compatible quasi-coherent O_X-module \
structure, and an ORDINARY quasi-coherent O_S-module G, Ra_*F^• ⊗ᴸ_{O_S} G is \
Ra_*(F^• ⊗_{a^{-1}O_S} a^{-1}G) with the ORDINARY tensor product on the right. The two tensor \
factors are in the order the Tag 0B53 map produces them, which is the opposite of the source's"]
def relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent
    [QuasiCompact f] [QuasiSeparated f] (G : Modules S.toRingedSpace) (hG : G.IsQuasicoherent)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase f).sheaf) (F.X i))
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj
      ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G) ≅
      (derivedPushforward (inverseImageBaseProjection f)).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj F).obj
            ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
              ((RingedSpaceModuleAdjunction.modulePullback
                (inverseImageBaseProjection f)).obj G)))) :=
  relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBounded f G F hF hflat M hM hFM
    fun N hN i n => isIso_projectionFormulaMap_single_relativeBase f
      ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G)
      (derivedCategoryB_isQuasicoherent_single (Y := S) G hG 0) N hN i n

end Stacks.RelativeComplexPushforward

end
