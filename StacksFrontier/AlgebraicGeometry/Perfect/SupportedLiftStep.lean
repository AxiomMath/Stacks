module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedLiftAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedLiftTwoOpens
public import StacksFrontier.AlgebraicGeometry.RestrictionAlongHomOfLE
public import StacksFrontier.CategoryTheory.TwoOpenBiprodGlueing

/-!
# The two-open step for perfect objects with prescribed support

Let `X` be a scheme covered by two opens `U` and `V` with `V` affine and `U ⊓ V` quasi-compact,
let `T ⊆ X` be closed with `(X ∖ T) ∩ V` quasi-compact, and let `E` be an object of `D(𝒪_X)` with
quasi-coherent cohomology. A perfect object `A` of `D(𝒪_U)` supported on `T ∩ U`, with a map
`a : A ⟶ E|_U`, is carried to a perfect object `R` of `D(𝒪_X)` supported on `T`, with a map
`ρ : R ⟶ E` and an isomorphism `R|_U ≅ A ⊞ A⟦1⟧` through which `ρ|_U` is the projection onto `A`
followed by `a`.

## Main results

* `Stacks.Perfect.SupportedLiftStep.isPerfect_biprod`: a biproduct of two perfect objects is
  perfect.
* `Stacks.Perfect.SupportedLiftStep.nestedOpenOfLE_sup_nestedOpenOfLE_eq_top`: the copies of two
  opens inside their union cover it.
* `Stacks.Perfect.SupportedLiftStep.cohomologySupportedOn_derivedPullback_homOfLE`: the
  restriction of an object supported on the preimage of `T` to a smaller open is supported on the
  preimage of `T`.
* `Stacks.Perfect.SupportedLiftStep.cohomologySupportedOn_derivedPullback_restrictNested`: the
  same for the comparison of the two presentations of a nested open.
* `Stacks.Perfect.SupportedLiftStep.exists_isPerfect_supported_hom_biprod_shift_of_overlap`: the
  two-open step, with the overlap presented as the apex of a Cartesian square of the inclusions
  and the affine case over `V` taken as a hypothesis.
* `Stacks.Perfect.SupportedLiftStep.affine_hyp_of_isAffine`: the affine case over an affine
  scheme, with perfectness and support bundled into one conjunction.
* `Stacks.Perfect.SupportedLiftStep.class_back_of_restrictNested`: perfectness and support travel
  back along the comparison of the two presentations of a nested open.
* `Stacks.Perfect.SupportedLiftStep.exists_isPerfect_supported_hom_biprod_shift_of_sup_eq_top`:
  the two-open step at the overlap `U ⊓ V`.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.ClosedSupportPerfect (nestedOpenOfLE restrictNestedIsoRestrict)
open Stacks.Cohomology.GlueingComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.SupportedBiprodShift (restrictNestedIsoRestrict_base_val)
open Stacks.Perfect.SupportedLiftTwoOpens (openInclusion)

universe u

namespace Stacks.Perfect.SupportedLiftStep

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Perfectness of a biproduct -/

/-- A biproduct of two perfect objects is perfect. -/
theorem isPerfect_biprod {Y : RingedSpace.{u, u}} [HasDerivedCategory.{u + 1} (OXMod.{u, u} Y)]
    {A B : DerivedCategory (OXMod.{u, u} Y)}
    (hA : IsPerfect.{u, u, u + 1} A) (hB : IsPerfect.{u, u, u + 1} B) :
    IsPerfect.{u, u, u + 1} (A ⊞ B) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    (CategoryTheory.Pretriangulated.binaryBiproductTriangle A B).invRotate
    (CategoryTheory.Pretriangulated.inv_rot_of_distTriang _
      (CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished A B))
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hB (-1)) hA

/-! ### The two copies of a pair of opens inside their union -/

variable (X : Scheme.{u})

/-- For opens `W` and `V` of a scheme, the copies of `W` and of `V` inside `W ⊔ V` cover
`W ⊔ V`. -/
theorem nestedOpenOfLE_sup_nestedOpenOfLE_eq_top (W V : X.Opens) :
    nestedOpenOfLE W (W ⊔ V) ⊔ nestedOpenOfLE V (W ⊔ V) = ⊤ := by
  apply Opens.ext
  apply Set.eq_univ_of_forall
  intro z
  have hz := z.2
  simp only [Opens.coe_sup, Set.mem_union] at hz ⊢
  exact hz

/-! ### Support along the two inclusions of the overlap -/

/-- If the preimage of `Z` under `f` is `Z'`, the derived pullback along `f` of an object supported
on `Z` is supported on `Z'`. -/
private theorem cohomologySupportedOn_derivedPullback_of_preimage_iff
    {Y Y' : RingedSpace.{u, u}} (f : Y' ⟶ Y) {Z : Set Y} {Z' : Set Y'}
    (A : DerivedModules Y) (hA : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing Y) Z A)
    (h : ∀ z, f.hom.base z ∈ Z ↔ z ∈ Z') :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing Y') Z'
      ((derivedPullback f).obj A) := by
  have hset : Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage f Z = Z' :=
    Set.ext h
  exact hset ▸ Stacks.Cohomology.SupportedComplexes.cohomologySupportedOn_derivedPullback f Z A hA

/-- For `U' ≤ U` opens of a scheme and `T` a subset of `X`, an object of `D(𝒪_U)` whose
cohomology is supported on the preimage of `T` restricts along `X.homOfLE` to an object of
`D(𝒪_{U'})` supported on the preimage of `T`. -/
theorem cohomologySupportedOn_derivedPullback_homOfLE {U' U : X.Opens} (h : U' ≤ U) (T : Set X)
    (A : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hAT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) A) :
    AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U'.isOpenEmbedding))
      (Subtype.val ⁻¹' T) ((derivedRestrict (X.homOfLE h).toLRSHom.toShHom).obj A) := by
  refine cohomologySupportedOn_derivedPullback_of_preimage_iff
    (X.homOfLE h).toLRSHom.toShHom A hAT fun z => ?_
  change Subtype.val ((X.homOfLE h).toLRSHom.toShHom.hom.base z) ∈ T ↔ Subtype.val z ∈ T
  rw [show Subtype.val ((X.homOfLE h).toLRSHom.toShHom.hom.base z) = Subtype.val z from
    congrArg (fun φ : X.toRingedSpace.restrict U'.isOpenEmbedding ⟶ X.toRingedSpace =>
      φ.hom.base z) (Stacks.NestedRestrictionOfLE.homOfLE_toShHom_comp_ofRestrict X h)]

/-- For `U ≤ W` opens of a scheme, pulling back along
`Stacks.Cohomology.ClosedSupportPerfect.restrictNestedIsoRestrict` carries an object of `D(𝒪_U)`
supported on the preimage of `T` to an object over the copy of `U` inside `W` supported on the
iterated preimage of `T`. -/
theorem cohomologySupportedOn_derivedPullback_restrictNested {U W : X.Opens} (hUW : U ≤ W)
    (T : Set X) (A : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hAT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) A) :
    AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing ((X.toRingedSpace.restrict W.isOpenEmbedding).restrict
        (nestedOpenOfLE U W).isOpenEmbedding))
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' T :
        Set (X.toRingedSpace.restrict W.isOpenEmbedding)))
      ((derivedPullback (restrictNestedIsoRestrict U W hUW).hom).obj A) := by
  refine cohomologySupportedOn_derivedPullback_of_preimage_iff
    (restrictNestedIsoRestrict U W hUW).hom A hAT fun z => ?_
  change Subtype.val ((restrictNestedIsoRestrict U W hUW).hom.hom.base z) ∈ T ↔
    Subtype.val (Subtype.val z) ∈ T
  rw [restrictNestedIsoRestrict_base_val]

/-! ### The step, with the overlap abstract -/

/-- Let `U ⊔ V = ⊤` in a scheme `X`, let `T ⊆ X`, let `E` be an object of `D(𝒪_X)`, and present
the overlap as the apex `W` of a Cartesian square of the four inclusions. Let `A` over `U` be
perfect and supported on the preimage of `T`, with a map `a : A ⟶ E|_U`, and let `GW` be a class
of objects over `W` containing `A|_W`. Assume the affine case over `V`: every `F` in `GW` with a
map `α : F ⟶ E|_W` comes from a perfect `B` over `V` supported on the preimage of `T`, with a map
`β : B ⟶ E|_V` and an isomorphism `B|_W ≅ F ⊞ F⟦1⟧` through which `β|_W` is the projection onto
`F` followed by `α`. Then there is a perfect `R` over `X` supported on `T`, a map `ρ : R ⟶ E`,
and an isomorphism `R|_U ≅ A ⊞ A⟦1⟧` through which `ρ|_U` is the projection onto `A` followed by
`a`. -/
theorem exists_isPerfect_supported_hom_biprod_shift_of_overlap (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (T : Set X) {W : RingedSpace.{u, u}}
    (iU : W ⟶ X.toRingedSpace.restrict U.isOpenEmbedding)
    (iV : W ⟶ X.toRingedSpace.restrict V.isOpenEmbedding)
    (hpb : IsPullback iU iV (openInclusion X U) (openInclusion X V))
    (GW : DerivedModules W → Prop) (E : DerivedModules X.toRingedSpace)
    (A : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hA : IsPerfect (X := X.toRingedSpace.restrict U.isOpenEmbedding) A)
    (hAT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) A)
    (hAW : GW ((derivedRestrict iU).obj A))
    (a : A ⟶ (derivedRestrict (openInclusion X U)).obj E)
    (affine : ∀ F : DerivedModules W, GW F →
      ∀ α : F ⟶ (derivedRestrict iV).obj ((derivedRestrict (openInclusion X V)).obj E),
        ∃ (B : DerivedModules (X.toRingedSpace.restrict V.isOpenEmbedding))
          (β : B ⟶ (derivedRestrict (openInclusion X V)).obj E)
          (e : (derivedRestrict iV).obj B ≅ F ⊞ F⟦(1 : ℤ)⟧),
          (IsPerfect (X := X.toRingedSpace.restrict V.isOpenEmbedding) B ∧
              AlgebraicGeometry.CohomologySupportedOn
                (structureSheafRing (X.toRingedSpace.restrict V.isOpenEmbedding))
                (Subtype.val ⁻¹' T) B) ∧
            (derivedRestrict iV).map β = e.hom ≫ biprod.fst ≫ α) :
    ∃ (R : DerivedModules X.toRingedSpace) (ρ : R ⟶ E),
      (IsPerfect (X := X.toRingedSpace) R ∧
          AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T R) ∧
        ∃ f : (derivedRestrict (openInclusion X U)).obj R ≅ A ⊞ A⟦(1 : ℤ)⟧,
          (derivedRestrict (openInclusion X U)).map ρ = f.hom ≫ biprod.fst ≫ a :=
  Stacks.LiftingProblem.exists_biprod_iso_hom_of_affine_overlap
    (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive iU)
    (Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift iU)
    (overlapIso (openInclusion X U) (openInclusion X V) iU iV hpb.w)
    (fun R => IsPerfect (X := X.toRingedSpace) R ∧
      AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T R)
    (fun A' => IsPerfect (X := X.toRingedSpace.restrict U.isOpenEmbedding) A' ∧
      AlgebraicGeometry.CohomologySupportedOn
        (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
        (Subtype.val ⁻¹' T) A')
    (fun B => IsPerfect (X := X.toRingedSpace.restrict V.isOpenEmbedding) B ∧
      AlgebraicGeometry.CohomologySupportedOn
        (structureSheafRing (X.toRingedSpace.restrict V.isOpenEmbedding))
        (Subtype.val ⁻¹' T) B)
    GW
    ⟨isPerfect_biprod (Y := X.toRingedSpace.restrict U.isOpenEmbedding) hA
        (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hA 1),
      Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_biprod _ _ _ _ hAT
        (Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_shift _ _ _ hAT)⟩
    hAW a affine
    (fun A' hA' B hB a' b c hc => by
      obtain ⟨R, ρ, hR, hRT, f, g, hρU, -⟩ :=
        Stacks.Perfect.SupportedLiftTwoOpens.exists_isPerfect_supported_hom_of_overlap_iso
          X U V hUV T iU iV hpb E A' B hA'.1 hB.1 hA'.2 hB.2 a' b c hc
      exact ⟨R, ρ, ⟨hR, hRT⟩, f, g, hρU⟩)

/-! ### The affine case, with its two class clauses bundled -/

open Stacks.Perfect.SupportedLiftAffine in
/-- Let `W` be an affine scheme, `T ⊆ W` closed with quasi-compact complement, `O` a quasi-compact
open of `W` and `E` an object of `D(𝒪_W)` with quasi-coherent cohomology. Every `F` in `D(𝒪_O)`
which is perfect and supported on the preimage of `T`, with a map `α : F ⟶ E|_O`, comes from a
`B` in `D(𝒪_W)` which is perfect and supported on `T`, with a map `β : B ⟶ E` and an isomorphism
`B|_O ≅ F ⊞ F⟦1⟧` through which `β|_O` is the projection onto `F` followed by `α`. -/
theorem affine_hyp_of_isAffine (W : Scheme.{u}) [IsAffine W] (T : Set W) (hT : IsClosed T)
    (hTc : IsCompact Tᶜ) (O : W.Opens) (hO : IsCompact ((O : W.Opens) : Set W))
    (E : DerivedCategory (OXMod.{u, u} W.toRingedSpace))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E).IsQuasicoherent)
    (F : DerivedCategory (OXMod.{u, u} (W.toRingedSpace.restrict O.isOpenEmbedding)))
    (hF : IsPerfect (X := W.toRingedSpace.restrict O.isOpenEmbedding) F ∧
      AlgebraicGeometry.CohomologySupportedOn
        (structureSheafRing (W.toRingedSpace.restrict O.isOpenEmbedding))
        (Subtype.val ⁻¹' T) F)
    (α : F ⟶ (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace O).obj E) :
    ∃ (B : DerivedCategory (OXMod.{u, u} W.toRingedSpace)) (β : B ⟶ E)
      (e : (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace O).obj B ≅
        F ⊞ F⟦(1 : ℤ)⟧),
      (IsPerfect (X := W.toRingedSpace) B ∧
          AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toRingedSpace) T B) ∧
        (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace O).map β =
          e.hom ≫ biprod.fst ≫ α :=
  (exists_isPerfect_supported_hom_biprod_shift_iso_restrict_of_isAffine
      W T hT hTc O hO E hE F hF.1 hF.2 α).imp fun _ h => h.imp fun _ h' =>
    h'.2.2.imp fun _ hc => ⟨⟨h'.1, h'.2.1⟩, hc⟩

/-- For `U ≤ W` opens of a scheme, an object of `D(𝒪_U)` perfect and supported on the preimage of
`T` pulls back along `Stacks.Cohomology.ClosedSupportPerfect.restrictNestedIsoRestrict` to an
object over the copy of `U` inside `W` which is perfect and supported on the iterated preimage of
`T`. -/
theorem class_back_of_restrictNested (U W : X.Opens) (hUW : U ≤ W) (T : Set X)
    (F : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hF : IsPerfect (X := X.toRingedSpace.restrict U.isOpenEmbedding) F ∧
      AlgebraicGeometry.CohomologySupportedOn
        (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
        (Subtype.val ⁻¹' T) F) :
    IsPerfect (X := (X.toRingedSpace.restrict W.isOpenEmbedding).restrict
        (nestedOpenOfLE U W).isOpenEmbedding)
      ((derivedPullback (restrictNestedIsoRestrict U W hUW).hom).obj F) ∧
    AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing ((X.toRingedSpace.restrict W.isOpenEmbedding).restrict
        (nestedOpenOfLE U W).isOpenEmbedding))
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' T :
        Set (X.toRingedSpace.restrict W.isOpenEmbedding)))
      ((derivedPullback (restrictNestedIsoRestrict U W hUW).hom).obj F) :=
  ⟨(Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff
      (restrictNestedIsoRestrict U W hUW) F).2 hF.1,
    cohomologySupportedOn_derivedPullback_restrictNested X hUW T F hF.2⟩

/-! ### The two-open step at the overlap `U ⊓ V` -/

open Stacks.Perfect.SupportedLiftAffine in
/-- Let `X` be a scheme covered by two opens `U` and `V` with `V` affine and `U ⊓ V`
quasi-compact, let `T ⊆ X` be closed with `(X ∖ T) ∩ V` quasi-compact, and let `E` be an object
of `D(𝒪_X)` with quasi-coherent cohomology. Then every perfect object `A` of `D(𝒪_U)` supported
on `T ∩ U`, with a map `a : A ⟶ E|_U`, is carried to a perfect object `R` of `D(𝒪_X)` supported
on `T`, a map `ρ : R ⟶ E`, and an isomorphism `R|_U ≅ A ⊞ A⟦1⟧` through which `ρ|_U` is the
projection onto `A` followed by `a`. -/
theorem exists_isPerfect_supported_hom_biprod_shift_of_sup_eq_top (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) [IsAffine V.toScheme]
    (hUVc : IsCompact ((U ⊓ V : X.Opens) : Set X)) (T : Set X) (hT : IsClosed T)
    (hTV : IsCompact ((Subtype.val ⁻¹' T :
      Set (X.toRingedSpace.restrict V.isOpenEmbedding))ᶜ))
    (E : DerivedModules X.toRingedSpace)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (A : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hA : IsPerfect (X := X.toRingedSpace.restrict U.isOpenEmbedding) A)
    (hAT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) A)
    (a : A ⟶ (derivedRestrict (openInclusion X U)).obj E) :
    ∃ (R : DerivedModules X.toRingedSpace) (ρ : R ⟶ E),
      (IsPerfect (X := X.toRingedSpace) R ∧
          AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T R) ∧
        ∃ f : (derivedRestrict (openInclusion X U)).obj R ≅ A ⊞ A⟦(1 : ℤ)⟧,
          (derivedRestrict (openInclusion X U)).map ρ = f.hom ≫ biprod.fst ≫ a := by
  refine exists_isPerfect_supported_hom_biprod_shift_of_overlap X U V hUV T
    (X.homOfLE (inf_le_left : U ⊓ V ≤ U)).toLRSHom.toShHom
    (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).toLRSHom.toShHom
    (Stacks.RestrictionSpellings.isPullback_ofRestrict_inf X U V)
    (fun F => IsPerfect (X := X.toRingedSpace.restrict (U ⊓ V).isOpenEmbedding) F ∧
      AlgebraicGeometry.CohomologySupportedOn
        (structureSheafRing (X.toRingedSpace.restrict (U ⊓ V).isOpenEmbedding))
        (Subtype.val ⁻¹' T) F)
    E A hA hAT ?_ a ?_
  · exact ⟨AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (X.homOfLE (inf_le_left : U ⊓ V ≤ U)).toLRSHom.toShHom A hA,
    cohomologySupportedOn_derivedPullback_homOfLE X (inf_le_left : U ⊓ V ≤ U) T A hAT⟩
  exact Stacks.LiftingProblem.exists_biprod_iso_hom_of_equivalence
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackEquivalence
      (restrictNestedIsoRestrict (U ⊓ V) V inf_le_right)).symm
    (Stacks.NestedRestrictionOfLE.derivedPullbackNestedHomOfLEIso X
      (inf_le_right : U ⊓ V ≤ V))
    (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive
      (restrictNestedIsoRestrict (U ⊓ V) V inf_le_right).inv)
    (Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift
      (restrictNestedIsoRestrict (U ⊓ V) V inf_le_right).inv)
    (fun B => IsPerfect (X := X.toRingedSpace.restrict V.isOpenEmbedding) B ∧
      AlgebraicGeometry.CohomologySupportedOn
        (structureSheafRing (X.toRingedSpace.restrict V.isOpenEmbedding))
        (Subtype.val ⁻¹' T) B)
    (fun F' => IsPerfect (X := (X.toRingedSpace.restrict V.isOpenEmbedding).restrict
        (nestedOpenOfLE (U ⊓ V) V).isOpenEmbedding) F' ∧
      AlgebraicGeometry.CohomologySupportedOn
        (structureSheafRing ((X.toRingedSpace.restrict V.isOpenEmbedding).restrict
          (nestedOpenOfLE (U ⊓ V) V).isOpenEmbedding))
        (Subtype.val ⁻¹' (Subtype.val ⁻¹' T :
          Set (X.toRingedSpace.restrict V.isOpenEmbedding))) F')
    (fun F => IsPerfect (X := X.toRingedSpace.restrict (U ⊓ V).isOpenEmbedding) F ∧
      AlgebraicGeometry.CohomologySupportedOn
        (structureSheafRing (X.toRingedSpace.restrict (U ⊓ V).isOpenEmbedding))
        (Subtype.val ⁻¹' T) F)
    (class_back_of_restrictNested X (U ⊓ V) V inf_le_right T)
    (affine_hyp_of_isAffine V.toScheme (Subtype.val ⁻¹' T)
      (hT.preimage continuous_subtype_val) hTV (nestedOpenOfLE (U ⊓ V) V)
      (Stacks.NestedRestrictionOfLE.isCompact_nestedOpenOfLE (U ⊓ V) V inf_le_right hUVc)
      ((derivedRestrict (openInclusion X V)).obj E)
      (fun i => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel V.ι E hE i))

end Stacks.Perfect.SupportedLiftStep

end
