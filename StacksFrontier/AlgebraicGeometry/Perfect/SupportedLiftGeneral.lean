module

public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.AffineGrowth
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedLiftStep
public import StacksFrontier.CategoryTheory.BiprodLiftComposition
public import StacksFrontier.CategoryTheory.SumOfPositiveShifts

/-!
# [Stacks, Tag 09IM] at a quasi-compact quasi-separated scheme

`StacksFrontier/AlgebraicGeometry/Perfect/SupportedLiftStep.lean` proves the two-open case: a scheme
covered by an open `U` and an affine open `V`. This module runs the affine-cover induction of
`Stacks.AlgebraicGeometry.InductionPrinciple.prop_top_of_affineGrowth` over that case and lands
the statement at an arbitrary quasi-compact quasi-separated scheme, in the strengthened form the
remark [Stacks, Tag 09IN] needs: the complement of `P` in `R|_U` is a finite biproduct of
*positive* shifts of `P`, and the map `R|_U ⟶ E|_U` is the projection onto `P` followed by the
given `α`.

## Main results

* `Stacks.Perfect.SupportedLiftGeneral.exists_isPerfect_supported_hom_biprod_sumShifts`:
  **[Stacks, Tag 09IM], strengthened.** For `X` quasi-compact and quasi-separated, `U` a
  quasi-compact open, `T` closed with `X ∖ T` retrocompact and `E` with quasi-coherent cohomology,
  every perfect `P` over `U` supported on `T ∩ U` with a map `α : P ⟶ E|_U` is carried to a
  perfect `R` over `X` supported on `T` with a map `ρ : R ⟶ E`, an isomorphism `R|_U ≅ P ⊞ J` with
  `J` a finite biproduct of positive shifts of `P`, and `ρ|_U = biprod.fst ≫ α` in those
  coordinates.
* `Stacks.Perfect.SupportedLiftGeneral.isPerfect_of_isSumOfPositiveShifts` and
  `Stacks.Perfect.SupportedLiftGeneral.cohomologySupportedOn_of_isSumOfPositiveShifts`: the
  complement is again perfect and again supported on `T`, so it is a legitimate input to the
  construction — which is what the iteration of [Stacks, Tag 09IN] needs.
* `Stacks.Perfect.SupportedLiftGeneral.exists_biprod_iso_hom_sup_of_homOfLE`: the two-open step
  read along `AlgebraicGeometry.Scheme.homOfLE`, which is the spelling the induction composes in.

## Implementation notes

**The induction carries its compactness as a conjunct.**
`Stacks.AlgebraicGeometry.InductionPrinciple.prop_top_of_affineGrowth` hands the step no
quasi-compactness of the open reached so far, and the two-open step needs it — the overlap
`W ⊓ V` has to be quasi-compact. So the property run through the induction is
`IsCompact W ∧ Stacks.Perfect.SupportedLiftGeneral.LiftOver … W`, not `LiftOver` alone.

**The ambient object is universally quantified in `LiftOver`.** The step applies the induction
hypothesis over `W` with ambient object `E|_{W ⊔ V}` restricted to `W`, which is only isomorphic
to `E|_W` and not equal to it. Quantifying over the ambient object removes that comparison
entirely; the price is carrying its quasi-coherence, which the two-open step needs.

**The biproduct in `LiftOver` is written at an explicitly given category.** The codomain of
`Stacks.Cohomology.GlueingComplexes.derivedRestrict` at `(X.homOfLE h).toLRSHom.toShHom` spells
the smaller open as `(↑U).toSheafedSpace` rather than as
`AlgebraicGeometry.SheafedSpace.restrict`, and instance search does not find
`CategoryTheory.Limits.HasBinaryBiproduct` there — the same failure recorded in the module
docstring of `StacksFrontier/AlgebraicGeometry/Perfect/SupportedLiftStep.lean`. Writing the
isomorphism as `@CategoryTheory.Iso (DerivedModules (X|_U)) _ _ _` fixes the category to the
`restrict` spelling, where the instance is found, and the two sides are then identified in one
defeq check.

**`HasDerivedCategory.standard`** is a local instance at priority `10000`, as in every module
this one consumes.

The registration of [Stacks, Tag 09IM] is on another declaration, so no
tag attribute is placed here; [Stacks, Tag 09IN] is registered on the consumer of this file.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open ZeroObject
open Stacks.Cohomology.ClosedSupportPerfect (nestedOpenOfLE restrictNestedIsoRestrict)
open Stacks.Cohomology.GlueingComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open Stacks.Perfect.SupportedLiftTwoOpens (openInclusion)
open Stacks.SumOfPositiveShifts (IsSumOfPositiveShifts)

universe u

namespace Stacks.Perfect.SupportedLiftGeneral

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Point-set input for the two-open step -/

/-- **The part of the copy of `V` inside `Z` lying off `T` is quasi-compact.** For `V ≤ Z` opens
of a scheme with `V` quasi-compact and `X ∖ T` retrocompact, the complement of the iterated
preimage of `T` inside `(X|_Z)|_{V}` is quasi-compact: the two subtype inclusions are embeddings
carrying it onto `(X ∖ T) ∩ V`.

This is the hypothesis `hTV` of
`Stacks.Perfect.SupportedLiftStep.exists_isPerfect_supported_hom_biprod_shift_of_sup_eq_top`, at
the pair of opens the affine-cover induction presents it with. -/
theorem isCompact_compl_nested (X : Scheme.{u}) (T : Set X)
    (hTc : IsRetrocompact (Tᶜ : Set X)) (V Z : X.Opens) (hVZ : V ≤ Z)
    (hV : IsCompact ((V : X.Opens) : Set X)) :
    IsCompact ((Subtype.val ⁻¹' (Subtype.val ⁻¹' T :
      Set (X.toRingedSpace.restrict Z.isOpenEmbedding)) :
      Set ((X.toRingedSpace.restrict Z.isOpenEmbedding).restrict
        (nestedOpenOfLE V Z).isOpenEmbedding))ᶜ) := by
  change IsCompact (((Subtype.val : ↥(nestedOpenOfLE V Z) → ↥Z) ⁻¹'
    ((Subtype.val : ↥Z → X.carrier) ⁻¹' T))ᶜ)
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have h1 : (Subtype.val : ↥(nestedOpenOfLE V Z) → ↥Z) ''
      ((Subtype.val : ↥(nestedOpenOfLE V Z) → ↥Z) ⁻¹'
        ((Subtype.val : ↥Z → X.carrier) ⁻¹' T))ᶜ =
      (Subtype.val : ↥Z → X.carrier) ⁻¹' ((Tᶜ ∩ (V : Set X)) : Set X) := by
    ext y
    refine ⟨?_, fun hy => ⟨⟨y, hy.2⟩, hy.1, rfl⟩⟩
    rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z.2⟩
  rw [h1]
  change IsCompact ((Subtype.val : ↥Z → X.carrier) ⁻¹' (Tᶜ ∩ (V : Set X)))
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff,
    Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hVZ hx.2⟩, rfl⟩]
  exact hTc hV V.2

/-- **The copies of two opens inside a third meet in the copy of their intersection.** Both sides
are the preimage of the intersection under the subtype inclusion. -/
theorem nestedOpenOfLE_inf (X : Scheme.{u}) (W V Z : X.Opens) :
    nestedOpenOfLE W Z ⊓ nestedOpenOfLE V Z = nestedOpenOfLE (W ⊓ V) Z := by
  apply Opens.ext
  ext z
  simp only [nestedOpenOfLE, Opens.coe_inf, Set.mem_inter_iff]
  rfl

/-! ### The two-open step along `homOfLE` -/

/-- **Restriction to the copy of `W` inside `Z`, followed by the comparison, is restriction along
`AlgebraicGeometry.Scheme.homOfLE`.** This is
`Stacks.NestedRestrictionOfLE.derivedPullbackNestedHomOfLEIso` read at the
`Stacks.Cohomology.GlueingComplexes.derivedRestrict` spelling of the first factor rather than at
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`: the two-open step produces its splitting
along the inclusion of an open subspace, and the induction composes along `homOfLE`. -/
def derivedRestrictNestedHomOfLEIso (X : Scheme.{u}) {W Z : X.Opens} (hWZ : W ≤ Z) :
    derivedRestrict ((X.toRingedSpace.restrict Z.isOpenEmbedding).ofRestrict
          (nestedOpenOfLE W Z).isOpenEmbedding) ⋙
        derivedPullback (restrictNestedIsoRestrict W Z hWZ).inv ≅
      derivedRestrict (X.homOfLE hWZ).toLRSHom.toShHom :=
  Functor.isoWhiskerRight
      (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback
        (X.toRingedSpace.restrict Z.isOpenEmbedding) (nestedOpenOfLE W Z)).symm
      (derivedPullback (restrictNestedIsoRestrict W Z hWZ).inv) ≪≫
    Stacks.NestedRestrictionOfLE.derivedPullbackNestedHomOfLEIso X hWZ

/-- **The two-open step of [Stacks, Tag 09IM], inside `W ⊔ V` and along `homOfLE`.** Let `X` be
quasi-separated, `W` a quasi-compact open, `V` an affine open, `T ⊆ X` closed with `X ∖ T`
retrocompact, and `E` an object over `W ⊔ V` with quasi-coherent cohomology. Then every perfect
`R₁` over `W` supported on `T ∩ W` with a map `b : R₁ ⟶ E|_W` is carried to a perfect `R₂` over
`W ⊔ V` supported on `T ∩ (W ⊔ V)`, a map `ρ : R₂ ⟶ E`, and an isomorphism
`R₂|_W ≅ R₁ ⊞ R₁⟦1⟧` through which `ρ|_W` is the projection onto `R₁` followed by `b`.

This is
`Stacks.Perfect.SupportedLiftStep.exists_isPerfect_supported_hom_biprod_shift_of_sup_eq_top`
inside the scheme `(W ⊔ V).toScheme`, at the copies of `W` and `V` in it, carried back along
`Stacks.Cohomology.ClosedSupportPerfect.restrictNestedIsoRestrict` by
`Stacks.LiftingProblem.exists_biprod_iso_hom_of_equivalence`. The affine input is supplied as a
lambda and rearranged by `Exists.imp` rather than by `obtain`; see the implementation notes of
`Stacks.Perfect.SupportedLiftStep.affine_hyp_of_isAffine` for why. -/
theorem exists_biprod_iso_hom_sup_of_homOfLE (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (T : Set X) (hT : IsClosed T) (hTc : IsRetrocompact (Tᶜ : Set X)) (W V : X.Opens)
    (hW : IsCompact ((W : X.Opens) : Set X)) (hV : IsAffineOpen V)
    (Ez : DerivedModules (X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding))
    (hEz : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing (X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding))) i).obj
      Ez).IsQuasicoherent)
    (R₁ : DerivedModules (X.toRingedSpace.restrict W.isOpenEmbedding))
    (hR₁ : IsPerfect (X := X.toRingedSpace.restrict W.isOpenEmbedding) R₁)
    (hR₁T : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict W.isOpenEmbedding))
      (Subtype.val ⁻¹' T) R₁)
    (b : R₁ ⟶ (derivedRestrict
      (X.homOfLE (le_sup_left : W ≤ W ⊔ V)).toLRSHom.toShHom).obj Ez) :
    ∃ (R₂ : DerivedModules (X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding)) (ρ : R₂ ⟶ Ez)
      (g : @Iso (DerivedModules (X.toRingedSpace.restrict W.isOpenEmbedding)) _
        ((derivedRestrict (X.homOfLE (le_sup_left : W ≤ W ⊔ V)).toLRSHom.toShHom).obj R₂)
        (R₁ ⊞ R₁⟦(1 : ℤ)⟧)),
      (IsPerfect (X := X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding) R₂ ∧
          AlgebraicGeometry.CohomologySupportedOn
            (structureSheafRing (X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding))
            (Subtype.val ⁻¹' T) R₂) ∧
        (derivedRestrict (X.homOfLE (le_sup_left : W ≤ W ⊔ V)).toLRSHom.toShHom).map ρ =
          g.hom ≫ biprod.fst ≫ b := by
  let Zs : Scheme.{u} := (W ⊔ V).toScheme
  let W' : Zs.Opens := nestedOpenOfLE W (W ⊔ V)
  let V' : Zs.Opens := nestedOpenOfLE V (W ⊔ V)
  have : IsAffine V'.toScheme :=
    hV.preimage_of_isOpenImmersion (W ⊔ V).ι
      (by rw [Scheme.Opens.opensRange_ι]; exact le_sup_right)
  have hinf : IsCompact ((W' ⊓ V' : Zs.Opens) : Set Zs) := by
    rw [show (W' ⊓ V' : Zs.Opens) = nestedOpenOfLE (W ⊓ V) (W ⊔ V) from
      nestedOpenOfLE_inf X W V (W ⊔ V)]
    exact Stacks.NestedRestrictionOfLE.isCompact_nestedOpenOfLE (W ⊓ V) (W ⊔ V)
      (inf_le_left.trans le_sup_left)
      (Stacks.NestedRestrictionOfLE.isCompact_inf W V hW hV.isCompact)
  exact
    Stacks.LiftingProblem.exists_biprod_iso_hom_of_equivalence
      (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackEquivalence
        (restrictNestedIsoRestrict W (W ⊔ V) (le_sup_left : W ≤ W ⊔ V))).symm
      (derivedRestrictNestedHomOfLEIso X (le_sup_left : W ≤ W ⊔ V))
      (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive
        (restrictNestedIsoRestrict W (W ⊔ V) (le_sup_left : W ≤ W ⊔ V)).inv)
      (Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift
        (restrictNestedIsoRestrict W (W ⊔ V) (le_sup_left : W ≤ W ⊔ V)).inv)
      (fun R => IsPerfect (X := X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding) R ∧
        AlgebraicGeometry.CohomologySupportedOn
          (structureSheafRing (X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding))
          (Subtype.val ⁻¹' T) R)
      (fun F => IsPerfect (X := (X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding).restrict
          (nestedOpenOfLE W (W ⊔ V)).isOpenEmbedding) F ∧
        AlgebraicGeometry.CohomologySupportedOn
          (structureSheafRing ((X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding).restrict
            (nestedOpenOfLE W (W ⊔ V)).isOpenEmbedding))
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' T :
            Set (X.toRingedSpace.restrict (W ⊔ V).isOpenEmbedding))) F)
      (fun R => IsPerfect (X := X.toRingedSpace.restrict W.isOpenEmbedding) R ∧
        AlgebraicGeometry.CohomologySupportedOn
          (structureSheafRing (X.toRingedSpace.restrict W.isOpenEmbedding))
          (Subtype.val ⁻¹' T) R)
      (Stacks.Perfect.SupportedLiftStep.class_back_of_restrictNested X W (W ⊔ V) le_sup_left T)
      (fun F hF α =>
        (Stacks.Perfect.SupportedLiftStep.exists_isPerfect_supported_hom_biprod_shift_of_sup_eq_top
          Zs W' V'
          (Stacks.Perfect.SupportedLiftStep.nestedOpenOfLE_sup_nestedOpenOfLE_eq_top X W V) hinf
          (Subtype.val ⁻¹' T) (hT.preimage continuous_subtype_val)
          (isCompact_compl_nested X T hTc V (W ⊔ V) le_sup_right hV.isCompact)
          Ez hEz F hF.1 hF.2 α).imp fun _ h => h.imp fun _ h' =>
            h'.2.imp fun _ hc => ⟨h'.1, hc⟩)
      R₁ ⟨hR₁, hR₁T⟩ b

/-! ### The complement is again a legitimate input -/

/-- **A zero object is supported on every subset.** All its cohomology sheaves are zero, hence so
are all their stalks. -/
theorem cohomologySupportedOn_of_isZero {Y : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (T : Set Y)
    {E : DerivedCategory (SheafOfModules.{u} O)} (hE : IsZero E) :
    AlgebraicGeometry.CohomologySupportedOn O T E := fun i x _ =>
  (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mp
    (Functor.map_isZero (SheafOfModules.toSheaf O)
      (Functor.map_isZero (DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i) hE)) x

/-- **A finite biproduct of positive shifts of a perfect object is perfect.** The four closure
rules of `Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts` are matched by the stability of
perfectness under shifts, under binary biproducts and under isomorphism, together with the
perfectness of a zero object — which is the third vertex of the contractible triangle on `P`.

The universes are written out, as in
`Stacks.Perfect.SupportedLiftStep.isPerfect_biprod`: left to elaboration the module universe of
the biproduct is undetermined and the error is a stuck constraint `max ?u ?v =?= u`. -/
theorem isPerfect_of_isSumOfPositiveShifts {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{u + 1} (OXMod.{u, u} Y)] {P Q : DerivedCategory (OXMod.{u, u} Y)}
    (hP : IsPerfect.{u, u, u + 1} P) (h : IsSumOfPositiveShifts P Q) :
    IsPerfect.{u, u, u + 1} Q := by
  induction h with
  | shift j _ => exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hP j
  | zero hQ =>
    exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      ((Limits.isZero_zero _).iso hQ)
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
        (CategoryTheory.Pretriangulated.contractibleTriangle P)
        (CategoryTheory.Pretriangulated.contractible_distinguished P) hP hP)
  | biprod _ _ ih₁ ih₂ => exact Stacks.Perfect.SupportedLiftStep.isPerfect_biprod (Y := Y) ih₁ ih₂
  | of_iso e _ ih => exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso e ih

/-- **A finite biproduct of positive shifts of an object supported on `T` is supported on `T`.**
The four closure rules are matched by
`Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_shift`,
`Stacks.Perfect.SupportedLiftGeneral.cohomologySupportedOn_of_isZero`,
`Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_biprod` and
`Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso`. -/
theorem cohomologySupportedOn_of_isSumOfPositiveShifts {Y : RingedSpace.{u, u}} (T : Set Y)
    {P Q : DerivedModules Y}
    (hP : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing Y) T P)
    (h : IsSumOfPositiveShifts P Q) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing Y) T Q := by
  induction h with
  | shift j _ =>
    exact Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_shift _ T j hP
  | zero hQ => exact cohomologySupportedOn_of_isZero _ T hQ
  | biprod _ _ ih₁ ih₂ =>
    exact Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_biprod _ T _ _ ih₁ ih₂
  | of_iso e _ ih =>
    exact Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ T e ih

/-! ### The lifting problem over an open containing `U` -/

/-- **The lifting problem of [Stacks, Tag 09IM] over an open `W`, in the strengthened form.**
For every ambient object `Ew` over `W` with quasi-coherent cohomology and every map
`a : P ⟶ Ew|_U` there is a perfect `R` over `W` supported on `T ∩ W`, a map `ρ : R ⟶ Ew`, and a
splitting `R|_U ≅ P ⊞ J` with `J` a finite biproduct of positive shifts of `P`, through which
`ρ|_U` is the projection onto `P` followed by `a`.

The ambient object is quantified over rather than fixed as a restriction of one object on `X`;
see the implementation notes. -/
def LiftOver (X : Scheme.{u}) (T : Set X) (U : X.Opens)
    (P : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding)) (W : X.Opens) : Prop :=
  ∀ hUW : U ≤ W, ∀ Ew : DerivedModules (X.toRingedSpace.restrict W.isOpenEmbedding),
    (∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing (X.toRingedSpace.restrict W.isOpenEmbedding))) i).obj
      Ew).IsQuasicoherent) →
    ∀ a : P ⟶ (derivedRestrict (X.homOfLE hUW).toLRSHom.toShHom).obj Ew,
      ∃ (R : DerivedModules (X.toRingedSpace.restrict W.isOpenEmbedding)) (ρ : R ⟶ Ew),
        (IsPerfect (X := X.toRingedSpace.restrict W.isOpenEmbedding) R ∧
            AlgebraicGeometry.CohomologySupportedOn
              (structureSheafRing (X.toRingedSpace.restrict W.isOpenEmbedding))
              (Subtype.val ⁻¹' T) R) ∧
          ∃ (J : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
            (f : @Iso (DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding)) _
              ((derivedRestrict (X.homOfLE hUW).toLRSHom.toShHom).obj R) (P ⊞ J)),
            IsSumOfPositiveShifts P J ∧
              (derivedRestrict (X.homOfLE hUW).toLRSHom.toShHom).map ρ =
                f.hom ≫ biprod.fst ≫ a

/-- Equal morphisms of schemes have equal underlying morphisms of sheafed spaces. -/
private theorem toShHom_congr {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) :
    f.toLRSHom.toShHom = g.toLRSHom.toShHom := by
  rw [h]

/-- Derived pullback along equal morphisms of ringed spaces, as an isomorphism of functors. -/
private def derivedPullbackEqToIso {Y Z : RingedSpace.{u, u}} {f g : Y ⟶ Z} (h : f = g) :
    derivedPullback f ≅ derivedPullback g :=
  eqToIso (by rw [h])

/-- **The base of the induction.** Over `U` itself the lifting problem is solved by `P`, with
zero complement: `AlgebraicGeometry.Scheme.homOfLE` at a reflexive inequality is the identity, so
`Stacks.LiftingProblem.exists_biprod_lift_of_isoId` applies. -/
theorem liftOver_self (X : Scheme.{u}) (T : Set X) (U : X.Opens)
    (P : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hP : IsPerfect (X := X.toRingedSpace.restrict U.isOpenEmbedding) P)
    (hPT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) P) :
    LiftOver X T U P U := by
  intro hUU Ew _ a
  have hid : (X.homOfLE hUU).toLRSHom.toShHom =
      𝟙 (X.toRingedSpace.restrict U.isOpenEmbedding) :=
    toShHom_congr (X.homOfLE_rfl U)
  let θ : derivedRestrict (X.homOfLE hUU).toLRSHom.toShHom ≅
      𝟭 (DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding)) :=
    derivedPullbackEqToIso hid ≪≫
      Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso _
  obtain ⟨β, f, hf⟩ := Stacks.LiftingProblem.exists_biprod_lift_of_isoId
    (derivedRestrict (X.homOfLE hUU).toLRSHom.toShHom) θ P Ew a
  exact ⟨P, β, ⟨hP, hPT⟩, 0, f, .zero (isZero_zero _), hf⟩

/-- **The step of the induction.** A solution of the lifting problem over `W` composes with the
two-open step from `W` to `W ⊔ V` into a solution over `W ⊔ V`, and the new complement
`J ⊞ (P ⊞ J)⟦1⟧` is again a finite biproduct of positive shifts of `P` by
`Stacks.SumOfPositiveShifts.IsSumOfPositiveShifts.biprod_shift_self`.

The comparison of restriction along `U ⟶ W ⊔ V` with restriction along `U ⟶ W` after `W ⟶ W ⊔ V`
is `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` at the factorisation
`AlgebraicGeometry.Scheme.homOfLE_homOfLE`, and the composition itself is
`Stacks.LiftingProblem.exists_biprod_lift_comp`. -/
theorem liftOver_sup (X : Scheme.{u}) [QuasiSeparatedSpace X] (T : Set X) (hT : IsClosed T)
    (hTc : IsRetrocompact (Tᶜ : Set X)) (U : X.Opens)
    (P : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (W V : X.Opens) (hUW : U ≤ W) (hW : IsCompact ((W : X.Opens) : Set X))
    (hV : IsAffineOpen V) (hpW : LiftOver X T U P W) :
    LiftOver X T U P (W ⊔ V) := by
  intro hUZ Ez hEz a
  have hcomp : (X.homOfLE hUW).toLRSHom.toShHom ≫
      (X.homOfLE (le_sup_left : W ≤ W ⊔ V)).toLRSHom.toShHom =
      (X.homOfLE hUZ).toLRSHom.toShHom :=
    toShHom_congr (X.homOfLE_homOfLE hUW (le_sup_left : W ≤ W ⊔ V))
  let e : derivedRestrict (X.homOfLE (le_sup_left : W ≤ W ⊔ V)).toLRSHom.toShHom ⋙
      derivedRestrict (X.homOfLE hUW).toLRSHom.toShHom ≅
      derivedRestrict (X.homOfLE hUZ).toLRSHom.toShHom :=
    derivedPullbackCompIsoCanonical (X.homOfLE hUW).toLRSHom.toShHom
        (X.homOfLE (le_sup_left : W ≤ W ⊔ V)).toLRSHom.toShHom ≪≫
      derivedPullbackEqToIso hcomp
  obtain ⟨R₁, ρ₁, ⟨hR₁, hR₁T⟩, J, f₁, hJ, hc₁⟩ :=
    hpW hUW _ (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
      (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) Ez hEz) (a ≫ (e.app Ez).inv)
  obtain ⟨R₂, ρ₂, g, hR₂, hc₂⟩ :=
    exists_biprod_iso_hom_sup_of_homOfLE X T hT hTc W V hW hV Ez hEz R₁ hR₁ hR₁T ρ₁
  obtain ⟨f', hf'⟩ := Stacks.LiftingProblem.exists_biprod_lift_comp
    (derivedRestrict (X.homOfLE hUW).toLRSHom.toShHom)
    (derivedRestrict (X.homOfLE (le_sup_left : W ≤ W ⊔ V)).toLRSHom.toShHom)
    (derivedRestrict (X.homOfLE hUZ).toLRSHom.toShHom) e
    (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive
      (X.homOfLE hUW).toLRSHom.toShHom)
    (Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift
      (X.homOfLE hUW).toLRSHom.toShHom)
    ρ₂ ρ₁ g hc₂ f₁ a hc₁
  exact ⟨R₂, ρ₂, hR₂, _, f', hJ.biprod_shift_self, hf'⟩

/-! ### From the top open to the scheme -/

/-- **The top open subscheme is the scheme.** `AlgebraicGeometry.Scheme.topIso` read on
underlying ringed spaces; its forward map is the inclusion of the open subspace on the nose. -/
def restrictTopIso (X : Scheme.{u}) :
    X.toRingedSpace.restrict (⊤ : X.Opens).isOpenEmbedding ≅ X.toRingedSpace where
  hom := openInclusion X ⊤
  inv := X.topIso.inv.toLRSHom.toShHom
  hom_inv_id :=
    congrArg (fun k : (⊤ : X.Opens).toScheme ⟶ (⊤ : X.Opens).toScheme => k.toLRSHom.toShHom)
      X.topIso.hom_inv_id
  inv_hom_id := congrArg (fun k : X ⟶ X => k.toLRSHom.toShHom) X.topIso.inv_hom_id

/-- **The inclusion of `U` factors through the top open.** `ofRestrict` at `U` followed by the
inverse of `Stacks.Perfect.SupportedLiftGeneral.restrictTopIso` is restriction along
`X.homOfLE le_top`: both compose with the inclusion of the top open to the inclusion of `U`, and
that inclusion is an isomorphism. -/
theorem ofRestrict_comp_restrictTopIso_inv (X : Scheme.{u}) (U : X.Opens) :
    openInclusion X U ≫ (restrictTopIso X).inv =
      (X.homOfLE (le_top : U ≤ ⊤)).toLRSHom.toShHom :=
  (Iso.comp_inv_eq (restrictTopIso X)).2
    (Stacks.NestedRestrictionOfLE.homOfLE_toShHom_comp_ofRestrict X (le_top : U ≤ ⊤)).symm

/-- **The support of the transport from the top open.** Pulling back along the inverse of
`Stacks.Perfect.SupportedLiftGeneral.restrictTopIso` carries an object supported on the preimage
of `T` to one supported on `T`: the comparison does not move points. -/
theorem cohomologySupportedOn_derivedPullback_restrictTop (X : Scheme.{u}) (T : Set X)
    (R : DerivedModules (X.toRingedSpace.restrict (⊤ : X.Opens).isOpenEmbedding))
    (hRT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict (⊤ : X.Opens).isOpenEmbedding))
      (Subtype.val ⁻¹' T) R) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      ((derivedPullback (restrictTopIso X).inv).obj R) := by
  have hset : Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage
      (restrictTopIso X).inv (Subtype.val ⁻¹' T) = T := by
    ext x
    change Subtype.val ((restrictTopIso X).inv.hom.base x) ∈ T ↔ x ∈ T
    rw [show Subtype.val ((restrictTopIso X).inv.hom.base x) = x from
      congrArg (fun φ : X.toRingedSpace ⟶ X.toRingedSpace => φ.hom.base x)
        (restrictTopIso X).inv_hom_id]
  exact hset ▸ Stacks.Cohomology.SupportedComplexes.cohomologySupportedOn_derivedPullback
    (restrictTopIso X).inv (Subtype.val ⁻¹' T) R hRT

/-- Pullback along the identification of `X` with its top open subscheme. -/
def pullbackToTop (X : Scheme.{u}) :
    DerivedModules X.toRingedSpace ⥤
      DerivedModules (X.toRingedSpace.restrict (⊤ : X.Opens).isOpenEmbedding) :=
  derivedPullback (restrictTopIso X).hom

/-- Pullback along the inverse identification, which carries the lift produced over the top open
back to the scheme. -/
def pullbackFromTop (X : Scheme.{u}) :
    DerivedModules (X.toRingedSpace.restrict (⊤ : X.Opens).isOpenEmbedding) ⥤
      DerivedModules X.toRingedSpace :=
  derivedPullback (restrictTopIso X).inv

/-- The round trip through the top open is the identity. -/
def roundTripTop (X : Scheme.{u}) : pullbackToTop X ⋙ pullbackFromTop X ≅ 𝟭 _ :=
  Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackHomInvIso (restrictTopIso X)

/-- Restriction to `U` after the transport from the top open is restriction along
`X.homOfLE le_top`, by `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` at
`Stacks.Perfect.SupportedLiftGeneral.ofRestrict_comp_restrictTopIso_inv`. -/
def restrictTopCompIso (X : Scheme.{u}) (U : X.Opens) :
    pullbackFromTop X ⋙ derivedRestrict (openInclusion X U) ≅
      derivedRestrict (X.homOfLE (le_top : U ≤ ⊤)).toLRSHom.toShHom :=
  derivedPullbackCompIsoCanonical (openInclusion X U) (restrictTopIso X).inv ≪≫
    eqToIso (congrArg (fun k : X.toRingedSpace.restrict U.isOpenEmbedding ⟶
        X.toRingedSpace.restrict (⊤ : X.Opens).isOpenEmbedding => derivedPullback k)
      (ofRestrict_comp_restrictTopIso_inv X U))

/-- **The splitting transports from the top open to the scheme.** A splitting of `R|_U` over the
top open, compatible with the map read through
`Stacks.Perfect.SupportedLiftGeneral.restrictTopCompIso` and
`Stacks.Perfect.SupportedLiftGeneral.roundTripTop`, becomes a splitting of the transported lift
with the *same* complement.

This is `Stacks.LiftingProblem.exists_biprod_lift_of_transport` at the comparison
`restrictTopCompIso`, isolated so that the kernel checks it against this statement rather than
as one clause of [Stacks, Tag 09IM]. -/
theorem exists_biprod_transport_top (X : Scheme.{u}) (U : X.Opens)
    (E : DerivedModules X.toRingedSpace)
    {P J : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding)}
    (α : P ⟶ (derivedRestrict (openInclusion X U)).obj E)
    {R : DerivedModules (X.toRingedSpace.restrict (⊤ : X.Opens).isOpenEmbedding)}
    (ρ : R ⟶ (pullbackToTop X).obj E)
    (f : @Iso (DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding)) _
      ((derivedRestrict (X.homOfLE (le_top : U ≤ ⊤)).toLRSHom.toShHom).obj R) (P ⊞ J))
    (hc : (derivedRestrict (X.homOfLE (le_top : U ≤ ⊤)).toLRSHom.toShHom).map ρ =
      f.hom ≫ biprod.fst ≫ (α ≫
        ((derivedRestrict (openInclusion X U)).mapIso ((roundTripTop X).app E)).inv ≫
          (restrictTopCompIso X U).hom.app ((pullbackToTop X).obj E))) :
    ∃ f' : (derivedRestrict (openInclusion X U)).obj ((pullbackFromTop X).obj R) ≅ P ⊞ J,
      (derivedRestrict (openInclusion X U)).map
          ((pullbackFromTop X).map ρ ≫ ((roundTripTop X).app E).hom) =
        f'.hom ≫ biprod.fst ≫ α :=
  Stacks.LiftingProblem.exists_biprod_lift_of_transport (pullbackFromTop X)
    (derivedRestrict (X.homOfLE (le_top : U ≤ ⊤)).toLRSHom.toShHom :
      DerivedModules (X.toRingedSpace.restrict (⊤ : X.Opens).isOpenEmbedding) ⥤
        DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (derivedRestrict (openInclusion X U)) (restrictTopCompIso X U) ((roundTripTop X).app E)
    ρ f α hc

/-! ### [Stacks, Tag 09IM] at a quasi-compact quasi-separated scheme -/

/-- **The affine-cover induction, run.** Under the hypotheses of [Stacks, Tag 09IM] the lifting
problem is solved over the top open of `X`.

This is `Stacks.AlgebraicGeometry.InductionPrinciple.prop_top_of_affineGrowth` applied to
`fun W => IsCompact W ∧ Stacks.Perfect.SupportedLiftGeneral.LiftOver X T U P W`, based by
`Stacks.Perfect.SupportedLiftGeneral.liftOver_self` and stepped by
`Stacks.Perfect.SupportedLiftGeneral.liftOver_sup`. The quasi-compactness is a conjunct because
the induction principle hands the step none; see the implementation notes. -/
theorem liftOver_top (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (T : Set X) (hT : IsClosed T) (hTc : IsRetrocompact (Tᶜ : Set X)) (U : X.Opens)
    (hU : IsCompact ((U : X.Opens) : Set X))
    (P : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hP : IsPerfect (X := X.toRingedSpace.restrict U.isOpenEmbedding) P)
    (hPT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) P) :
    LiftOver X T U P ⊤ :=
  (Stacks.AlgebraicGeometry.InductionPrinciple.prop_top_of_affineGrowth
    (fun W => IsCompact ((W : X.Opens) : Set X) ∧ LiftOver X T U P W) U
    ⟨hU, liftOver_self X T U P hP hPT⟩
    (fun W hUW V hV hQW => ⟨hQW.1.union hV.isCompact,
      liftOver_sup X T hT hTc U P W V hUW hQW.1 hV hQW.2⟩)).2

/-- **[Stacks, Tag 09IM], in the strengthened form the remark [Stacks, Tag 09IN] needs.** Let `X`
be a quasi-compact quasi-separated scheme, `U ⊆ X` a quasi-compact open, `T ⊆ X` closed with
`X ∖ T` retrocompact, and `E` an object of `D(𝒪_X)` with quasi-coherent cohomology. Then for every
perfect `P` of `D(𝒪_U)` supported on `T ∩ U` and every `α : P ⟶ E|_U` there is a perfect `R` of
`D(𝒪_X)` supported on `T`, a map `ρ : R ⟶ E`, an object `J` and an isomorphism
`R|_U ≅ P ⊞ J` with `J` a finite biproduct of positive shifts of `P`, through which `ρ|_U` is the
projection onto `P` followed by `α`.

The proof is the affine-cover induction
`Stacks.AlgebraicGeometry.InductionPrinciple.prop_top_of_affineGrowth` over
`Stacks.Perfect.SupportedLiftGeneral.LiftOver`, based at `U` by
`Stacks.Perfect.SupportedLiftGeneral.liftOver_self` and stepped by
`Stacks.Perfect.SupportedLiftGeneral.liftOver_sup`, followed by the transport from the top open
to the scheme by `Stacks.LiftingProblem.exists_biprod_lift_of_transport`.

The registration of [Stacks, Tag 09IM] is on another declaration; this statement
carries the two strengthenings the remark is about, and no tag attribute. -/
theorem exists_isPerfect_supported_hom_biprod_sumShifts (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact ((U : X.Opens) : Set X))
    (T : Set X) (hT : IsClosed T) (hTc : IsRetrocompact (Tᶜ : Set X))
    (E : DerivedModules X.toRingedSpace)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (P : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (hP : IsPerfect (X := X.toRingedSpace.restrict U.isOpenEmbedding) P)
    (hPT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict (openInclusion X U)).obj E) :
    ∃ (R : DerivedModules X.toRingedSpace) (ρ : R ⟶ E),
      (IsPerfect (X := X.toRingedSpace) R ∧
          AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T R) ∧
        ∃ (J : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
          (f : (derivedRestrict (openInclusion X U)).obj R ≅ P ⊞ J),
          IsSumOfPositiveShifts P J ∧
            (derivedRestrict (openInclusion X U)).map ρ = f.hom ≫ biprod.fst ≫ α := by
  refine (liftOver_top X T hT hTc U hU P hP hPT le_top ((pullbackToTop X).obj E)
      (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel (⊤ : X.Opens).ι E hE)
      (α ≫ ((derivedRestrict (openInclusion X U)).mapIso ((roundTripTop X).app E)).inv ≫
        (restrictTopCompIso X U).hom.app ((pullbackToTop X).obj E))).imp'
    (fun R => (pullbackFromTop X).obj R) fun R hR =>
      hR.imp' (fun ρ => (pullbackFromTop X).map ρ ≫ ((roundTripTop X).app E).hom)
        fun ρ hρ => ⟨⟨?_, ?_⟩, ?_⟩
  · exact (Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff
      (restrictTopIso X).symm R).2 hρ.1.1
  · exact cohomologySupportedOn_derivedPullback_restrictTop X T R hρ.1.2
  · exact hρ.2.imp fun J ⟨f, hsum, hc⟩ =>
      (exists_biprod_transport_top X U E α ρ f hc).imp fun _ hf' => ⟨hsum, hf'⟩

end Stacks.Perfect.SupportedLiftGeneral

end
