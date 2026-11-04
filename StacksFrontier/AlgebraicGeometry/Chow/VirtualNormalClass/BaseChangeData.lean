module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.DeformationComplementBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.InfinityPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf

/-!
# The deformation to the normal cone of a base-changed closed immersion

Let `i : Z ⟶ X` be a closed immersion and `h : X' ⟶ X` a morphism, with base change
`i' : Z' = Z ×_X X' ⟶ X'` (any cartesian square of closed immersions). The ideal of `Z'` is the
inverse image of the ideal of `Z`, so there is a morphism of deformation spaces
`φ : D(Z' ⊆ X') ⟶ D(Z ⊆ X)` over `h`. By
`Stacks.Deformation.isClosedImmersion_deformationBaseChangeLift` and
`Stacks.Deformation.isIso_baseChangeLift_restrict_complement`, `D(Z' ⊆ X') ⟶ D(Z ⊆ X) ×_X X'` is a
closed immersion which is an isomorphism away from the special fibres. This file records these
facts in the shape the comparison of classes at infinity
(`Stacks.Chow.GysinAtInfinity.properChowPushforward_infinityCap`) consumes; the hypotheses of that
comparison are `Stacks.Deformation.isProper_testMapOver_deformation`,
`Stacks.Deformation.isIso_openMapOver_deformation` and
`Stacks.Deformation.isPullback_openMapOver_deformation`, in
`StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.BaseChange`.

## Main definitions

* `Stacks.Deformation.deformationMapOver`: the morphism `D(Z' ⊆ X') ⟶ D(Z ⊆ X)` over `h`.
* `Stacks.Deformation.complementMapOver`: its restriction to the complements of the special
  fibres.

## Main results

* `Stacks.Deformation.coborderIdeal_baseChange`: the ideal of `Z'` is the inverse image of that of
  `Z`.
* `Stacks.Deformation.isClosedImmersion_deformationMapOverLift`: `D(Z' ⊆ X') ⟶ D(Z ⊆ X) ×_X X'`
  is a closed immersion.
* `Stacks.Deformation.isIso_complementMapOverLift`: away from the special fibres,
  `D(Z' ⊆ X') ⟶ D(Z ⊆ X) ×_X X'` is an isomorphism.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Conormal (coborderIdeal)

universe u

namespace Stacks.Deformation

section General

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData) (J' : U'.IdealSheafData)
  (hJ : J.comap h = J')

include hJ in
/-- If `J' = h⁻¹ J`, the morphism `D(J') ⟶ D(J) ×_U U'` induced by `deformationMap` is a closed
immersion. -/
theorem isClosedImmersion_deformationMapLift :
    IsClosedImmersion (pullback.lift (deformationMap h J J' hJ.le) (deformationSpaceToBase J')
      (deformationMap_toBase h J J' hJ.le)) := by
  subst hJ
  exact isClosedImmersion_deformationBaseChangeLift h J

include hJ in
/-- If `J' = h⁻¹ J`, the inverse image of `complementOpen J` under `deformationMap` is
`complementOpen J'`. -/
theorem preimage_complementOpen' :
    deformationMap h J J' hJ.le ⁻¹ᵁ complementOpen J = complementOpen J' := by
  subst hJ
  exact preimage_complementOpen h J

include hJ in
/-- If `J' = h⁻¹ J`, the morphism `D(J') ⟶ D(J) ×_U U'` is an isomorphism over the inverse image
of `complementOpen J`. -/
theorem isIso_deformationMapLift_restrict_complement :
    IsIso (pullback.lift (deformationMap h J J' hJ.le) (deformationSpaceToBase J')
      (deformationMap_toBase h J J' hJ.le) ∣_ (pullback.fst (deformationSpaceToBase J) h ⁻¹ᵁ
        complementOpen J)) := by
  subst hJ
  exact isIso_baseChangeLift_restrict_complement h J

end General

section Transport

variable {D D' Xc X'c X X' : Scheme.{u}} (π : D ⟶ Xc) (π' : D' ⟶ X'c) (hc : X'c ⟶ Xc)
  (ιc : Xc ⟶ X) (ι'c : X'c ⟶ X') [IsIso ιc] [IsIso ι'c] (h : X' ⟶ X) (hh : hc ≫ ιc = ι'c ≫ h)
  (φ : D' ⟶ D) (hφ : φ ≫ π = π' ≫ hc)

omit [IsIso ιc] [IsIso ι'c] in
include hh hφ in
/-- A morphism `φ` over `hc` is also a morphism over `h` after composing with the isomorphisms
`ιc` and `ι'c`. -/
theorem comp_comp_eq : φ ≫ (π ≫ ιc) = (π' ≫ ι'c) ≫ h := by
  rw [← Category.assoc, hφ, Category.assoc, hh, Category.assoc]

/-- The comparison `D ×_{Xc} X'c ≅ D ×_X X'` along isomorphisms of the bases. -/
abbrev pullbackBaseIso : pullback π hc ⟶ pullback (π ≫ ιc) h :=
  pullback.map π hc (π ≫ ιc) h (𝟙 D) ι'c ιc (by simp) hh

omit [IsIso ιc] [IsIso ι'c] in
/-- The lift into `D ×_X X'` is the lift into `D ×_{Xc} X'c` followed by `pullbackBaseIso`. -/
theorem lift_eq_lift_comp_pullbackBaseIso :
    pullback.lift φ (π' ≫ ι'c) (comp_comp_eq π π' hc ιc ι'c h hh φ hφ) =
      pullback.lift φ π' hφ ≫ pullbackBaseIso π hc ιc ι'c h hh := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst]
  · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]

/-- If the lift into `D ×_{Xc} X'c` is a closed immersion, so is the lift into `D ×_X X'`. -/
theorem isClosedImmersion_lift_of_base [IsClosedImmersion (pullback.lift φ π' hφ)] :
    IsClosedImmersion (pullback.lift φ (π' ≫ ι'c) (comp_comp_eq π π' hc ιc ι'c h hh φ hφ)) := by
  rw [lift_eq_lift_comp_pullbackBaseIso π π' hc ιc ι'c h hh φ hφ]
  infer_instance

/-- If the lift into `D ×_{Xc} X'c` is an isomorphism, so is the lift into `D ×_X X'`. -/
theorem isIso_lift_of_base [IsIso (pullback.lift φ π' hφ)] :
    IsIso (pullback.lift φ (π' ≫ ι'c) (comp_comp_eq π π' hc ιc ι'c h hh φ hφ)) := by
  rw [lift_eq_lift_comp_pullbackBaseIso π π' hc ιc ι'c h hh φ hφ]
  infer_instance

omit [IsIso ιc] [IsIso ι'c] in
/-- If `f₁ = f₂` and `b₁ = b₂` and `pullback.lift a b₁ w₁` is an isomorphism, then so is
`pullback.lift a b₂ w₂`. -/
theorem isIso_lift_congr {A B C E : Scheme.{u}} {f₁ f₂ : A ⟶ C} (g : B ⟶ C) (hf : f₁ = f₂)
    (a : E ⟶ A) {b₁ b₂ : E ⟶ B} (hb : b₁ = b₂) (w₁ : a ≫ f₁ = b₁ ≫ g) (w₂ : a ≫ f₂ = b₂ ≫ g)
    [IsIso (pullback.lift a b₁ w₁)] : IsIso (pullback.lift a b₂ w₂) := by
  subst hf hb
  infer_instance

end Transport

section ClosedImmersion

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ X')
  [IsClosedImmersion i'] (h : X' ⟶ X)

/-- The coborder of `i'` lies in the inverse image under `h` of the coborder of `i`. -/
theorem coborderRange_baseChange_le :
    i'.coborderRange ≤ h ⁻¹ᵁ i.coborderRange := by
  rw [Stacks.Divisors.coborderRange_eq_top i]
  exact le_top

/-- The morphism `h` restricted to the coborders of `i'` and `i`. -/
abbrev coborderMapOver : i'.coborderRange.toScheme ⟶ i.coborderRange.toScheme :=
  h.resLE i.coborderRange i'.coborderRange (coborderRange_baseChange_le i i' h)

/-- `coborderMapOver i i' h` commutes with the inclusions of the coborders and `h`. -/
theorem coborderMapOver_ι :
    coborderMapOver i i' h ≫ i.coborderRange.ι = i'.coborderRange.ι ≫ h :=
  Scheme.Hom.resLE_comp_ι _ _

variable {i i' h} {g : Z' ⟶ Z} (sq : IsPullback i' g h i)

include sq in
/-- If `Z' = Z ×_X X'`, then `Z'` is also the fibre product of `Z` with the coborder of `i'` over
the coborder of `i`. -/
theorem isPullback_liftCoborder :
    IsPullback i'.liftCoborder g (coborderMapOver i i' h) i.liftCoborder := by
  refine sq.of_iso (Iso.refl _) (asIso i'.coborderRange.ι).symm (Iso.refl _)
    (asIso i.coborderRange.ι).symm ?_ ?_ ?_ ?_
  all_goals simp [Scheme.Hom.liftCoborder_ι, IsIso.comp_inv_eq, ← Category.assoc]

include sq in
/-- **The ideal of `Z'` is the inverse image of the ideal of `Z`.** -/
theorem coborderIdeal_baseChange :
    (coborderIdeal i).comap (coborderMapOver i i' h) = coborderIdeal i' :=
  (ker_eq_comap_ker_of_isPullback (isPullback_liftCoborder sq)).symm

/-- **The morphism of deformation spaces `D(Z' ⊆ X') ⟶ D(Z ⊆ X)` over `h`.** -/
abbrev deformationMapOver :
    deformationSpace (coborderIdeal i') ⟶ deformationSpace (coborderIdeal i) :=
  deformationMap (coborderMapOver i i' h) (coborderIdeal i) (coborderIdeal i')
    (coborderIdeal_baseChange sq).le

/-- `deformationMapOver sq` lies over `coborderMapOver i i' h`. -/
theorem deformationMapOver_toBase :
    deformationMapOver sq ≫ deformationSpaceToBase (coborderIdeal i) =
      deformationSpaceToBase (coborderIdeal i') ≫ coborderMapOver i i' h :=
  deformationMap_toBase _ _ _ _

/-- `deformationMapOver sq` lies over `h` with respect to the projections to `X` and `X'`. -/
theorem deformationMapOver_projection :
    deformationMapOver sq ≫ deformationProjection i = deformationProjection i' ≫ h :=
  comp_comp_eq _ _ _ _ _ h (coborderMapOver_ι i i' h) _ (deformationMapOver_toBase sq)

/-- **`D(Z' ⊆ X') ⟶ D(Z ⊆ X) ×_X X'` is a closed immersion.** -/
instance isClosedImmersion_deformationMapOverLift :
    IsClosedImmersion (pullback.lift (deformationMapOver sq)
      (deformationProjection i') (deformationMapOver_projection sq)) := by
  have := isClosedImmersion_deformationMapLift (coborderMapOver i i' h) (coborderIdeal i)
    (coborderIdeal i') (coborderIdeal_baseChange sq)
  exact isClosedImmersion_lift_of_base _ _ _ _ _ h (coborderMapOver_ι i i' h) _
    (deformationMapOver_toBase sq)

/-- `D(t⁻¹)` of `D(Z' ⊆ X')` is the inverse image of `D(t⁻¹)` of `D(Z ⊆ X)`. -/
theorem preimage_complementOpen_over :
    deformationMapOver sq ⁻¹ᵁ complementOpen (coborderIdeal i) =
      complementOpen (coborderIdeal i') :=
  preimage_complementOpen' _ _ _ (coborderIdeal_baseChange sq)

/-- The morphism of the complements of the special fibres. -/
abbrev complementMapOver :
    (complementOpen (coborderIdeal i')).toScheme ⟶ (complementOpen (coborderIdeal i)).toScheme :=
  (deformationMapOver sq).resLE _ _ (preimage_complementOpen_over sq).ge

/-- `complementMapOver sq` commutes with the inclusions of the complements and
`deformationMapOver sq`. -/
theorem complementMapOver_ι :
    complementMapOver sq ≫ (complementOpen (coborderIdeal i)).ι =
      (complementOpen (coborderIdeal i')).ι ≫ deformationMapOver sq :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The complement of the special fibre of `D(Z' ⊆ X')` is the inverse image of that of
`D(Z ⊆ X)`, as a pullback square. -/
theorem isPullback_complementMapOver :
    IsPullback (complementOpen (coborderIdeal i')).ι (complementMapOver sq)
      (deformationMapOver sq) (complementOpen (coborderIdeal i)).ι :=
  isPullback_resLE_of_preimage _ _ _ (preimage_complementOpen_over sq)

/-- **Away from the special fibres, `D(Z' ⊆ X') ⟶ D(Z ⊆ X) ×_X X'` is an isomorphism.** -/
instance isIso_complementMapOverLift :
    IsIso (pullback.lift (complementMapOver sq)
      ((complementOpen (coborderIdeal i')).ι ≫ deformationProjection i')
      (Stacks.Chow.GysinAtInfinity.openMapOver_eq h (deformationProjection i)
        (complementOpen (coborderIdeal i)).ι (deformationProjection i')
        (complementOpen (coborderIdeal i')).ι (deformationMapOver sq)
        (deformationMapOver_projection sq) (complementMapOver sq)
        (complementMapOver_ι sq)).symm) := by
  have hiso := isIso_deformationMapLift_restrict_complement (coborderMapOver i i' h)
    (coborderIdeal i) (coborderIdeal i') (coborderIdeal_baseChange sq)
  have hc := isIso_lift_resLE (deformationSpaceToBase (coborderIdeal i))
    (deformationSpaceToBase (coborderIdeal i')) (coborderMapOver i i' h)
    (deformationMapOver sq) (deformationMapOver_toBase sq) _ _
    (preimage_complementOpen_over sq) hiso
  have := isIso_lift_of_base ((complementOpen (coborderIdeal i)).ι ≫
      deformationSpaceToBase (coborderIdeal i))
    ((complementOpen (coborderIdeal i')).ι ≫ deformationSpaceToBase (coborderIdeal i'))
    (coborderMapOver i i' h) i.coborderRange.ι i'.coborderRange.ι h
    (coborderMapOver_ι i i' h) (complementMapOver sq)
    (resLE_comp_comp _ _ _ _ (deformationMapOver_toBase sq) _ _
      (preimage_complementOpen_over sq)).symm
  exact isIso_lift_congr h (Category.assoc _ _ _) _ (Category.assoc _ _ _) _ _

end ClosedImmersion

end Stacks.Deformation

end
