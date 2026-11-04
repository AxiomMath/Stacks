module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ConeEmbedding
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Pieces

/-!
# The parameter of the deformation to the normal cone

The section `1` of the degree `-1` piece `𝒪_U` of the extended Rees algebra `𝒪_U[t⁻¹, ℐt]` is
the element `t⁻¹`. This file records it as a section of the algebra sheaf and shows that the
algebra map `Ψ` onto the conormal algebra kills it, so that the normal cone lies in the fibre
`t⁻¹ = 0`.

## Main definitions

* `Stacks.Deformation.paramPiece`: `t⁻¹` as a homogeneous section of degree `-1`.
* `Stacks.Deformation.paramUngraded`: its image in the ungraded realization.

## Main results

* `Stacks.Deformation.toConormalUngradedHom_paramUngraded`: `Ψ(t⁻¹) = 0`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec Stacks.Blowup
  Stacks.Conormal

universe u

namespace Stacks.Deformation

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The parameter `t⁻¹`**, the section `1` of the degree `-1` piece `𝒪_X` of the extended Rees
algebra, over an open `W`. -/
def paramPiece (W : X.Opens) : (extReesPiece I (-1)).val.obj (op W) :=
  (reesUnit I).eval (op W)

/-- The parameter `t⁻¹` has underlying section `1` in `Γ(X, W)`. -/
theorem extReesAmbient_paramPiece (W : X.Opens) : extReesAmbient I (-1) W (paramPiece I W) = 1 :=
  reesUnit_ambient I (op W)

/-- The parameter is compatible with restriction. -/
theorem paramPiece_restrict {W W' : X.Opens} (h : W' ≤ W) :
    (extReesPiece I (-1)).val.map (homOfLE h).op (paramPiece I W) = paramPiece I W' :=
  (reesUnit I).2 (homOfLE h).op

/-- **Multiplication by `t⁻¹` is the inclusion `ℐ^{max(k+1,0)} ⊆ ℐ^{max(k,0)}`**: in `Γ(X, W)`
it does not change the underlying section. -/
theorem extReesAmbient_param_mul (k : ℤ) (W : X.Opens) (x : (extReesPiece I k).val.obj (op W)) :
    extReesAmbient I (-1 + k) W ((extReesMul I (-1) k).app (op W) (paramPiece I W) x) =
      extReesAmbient I k W x := by
  rw [extReesAmbient_extReesMul, extReesAmbient_paramPiece, one_mul]

/-- The parameter `t⁻¹` in the ungraded realization of the extended Rees algebra. -/
def paramUngraded (W : X.Opens) :
    AlgebraSheaf.sections (ungradedAlgebraSheaf X (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I)) W :=
  ungradedAlgebraSheafIncl X (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) (-1) W
    (paramPiece I W)

end Stacks.Deformation

namespace Stacks.Deformation

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **`Ψ` kills the parameter**: `Ψ(t⁻¹) = 0`, as `Ψ` vanishes in negative degrees. -/
theorem toConormalUngradedHom_paramUngraded (W : i.coborderRange.toScheme.Opens) :
    ((toConormalUngradedHom i).right.hom.app (op W)).hom (paramUngraded (coborderIdeal i) W) =
      0 := by
  refine (toConormalUngradedHom_app_incl i (-1) W _).trans ?_
  rw [toConormalExtAdd_of_neg i (by norm_num)]
  rfl

/-- On an affine open `W`, a section of `ℐⁿ` which pulls back to zero in `g^*ℐⁿ` has its image
in `Γ(U, W)` in `ℐ(W)ⁿ⁺¹`. -/
theorem reesPieceAmbient_mem_of_pullbackSection_eq_zero (n : ℕ)
    (W : i.coborderRange.toScheme.affineOpens)
    (x : (reesPiece (coborderIdeal i) (n : ℤ)).val.obj (op W.1))
    (hx : Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ))
      W.1 (i.liftCoborder ⁻¹ᵁ W.1) le_rfl x = 0) :
    reesPieceAmbient (coborderIdeal i) (n : ℤ) W.1 x ∈ (coborderIdeal i).ideal W ^ (n + 1) := by
  have hker : RingHom.ker (i.liftCoborder.app W.1).hom = (coborderIdeal i).ideal W :=
    (coborderIdeal_ideal i W).symm
  have h := (reesPullbackSection_eq_zero_iff (coborderIdeal i) n W i.liftCoborder
    (W.2.preimage i.liftCoborder) hker (i.liftCoborder.app_surjective W.1 W.2)
    (reesAffineLinearEquiv (coborderIdeal i) n W x)).1
    (((congrArg (Scheme.Modules.pullbackSection i.liftCoborder
      (reesPiece (coborderIdeal i) (n : ℤ)) W.1 (i.liftCoborder ⁻¹ᵁ W.1) le_rfl)
      ((reesAffineLinearEquiv (coborderIdeal i) n W).symm_apply_apply x))).trans hx)
  exact (reesPieceAffineEquiv_coe (coborderIdeal i) (n : ℤ) (Int.natCast_nonneg n) W x) ▸ h

/-- **A homogeneous section killed by `Ψ` is divisible by `t⁻¹`.** On an affine open, a section of
degree `k` of the extended Rees algebra whose pullback to the conormal algebra vanishes (no
condition in negative degree) is `t⁻¹` times a section of degree `k + 1`. -/
theorem exists_incl_eq_param_mul (k : ℤ) (W : i.coborderRange.toScheme.affineOpens)
    (t : (extReesPiece (coborderIdeal i) k).val.obj (op W.1))
    (ht : ∀ _hk : 0 ≤ k, Scheme.Modules.pullbackSection i.liftCoborder
      (reesPiece (coborderIdeal i) (k.toNat : ℤ)) W.1 (i.liftCoborder ⁻¹ᵁ W.1) le_rfl t = 0) :
    ∃ y : (extReesPiece (coborderIdeal i) (k + 1)).val.obj (op W.1),
      (extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.incl k t =
        (extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.incl (k + 1) y *
          (extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.incl (-1)
            (paramPiece (coborderIdeal i) W.1) := by
  have hmem : extReesAmbient (coborderIdeal i) k W.1 t ∈
      (coborderIdeal i).ideal W ^ (k + 1).toNat := by
    rcases lt_or_ge k 0 with hk | hk
    · rw [show (k + 1).toNat = 0 by omega, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · have h := reesPieceAmbient_mem_of_pullbackSection_eq_zero i k.toNat W t (ht hk)
      rwa [show k.toNat + 1 = (k + 1).toNat by omega] at h
  let e := reesPieceAffineEquiv (coborderIdeal i) ((k + 1).toNat : ℤ) (Int.natCast_nonneg _) W
  let y : (extReesPiece (coborderIdeal i) (k + 1)).val.obj (op W.1) :=
    e.symm ⟨extReesAmbient (coborderIdeal i) k W.1 t, by rw [Int.toNat_natCast]; exact hmem⟩
  have hy : extReesAmbient (coborderIdeal i) (k + 1) W.1 y =
      extReesAmbient (coborderIdeal i) k W.1 t := by
    have := reesPieceAffineEquiv_coe (coborderIdeal i) ((k + 1).toNat : ℤ)
      (Int.natCast_nonneg _) W y
    refine this.symm.trans ?_
    simp only [y, e, AddEquiv.apply_symm_apply]
  refine ⟨y, ?_⟩
  refine Eq.trans ?_ (Stacks.GradedAlgebra.incl_mul_incl _ _ _ _ _).symm
  refine Stacks.GradedAlgebra.incl_eq_incl_of_heq _ (by ring) ?_
  refine extRees_heq (coborderIdeal i) (by ring) W.1 _ _ ?_
  show extReesAmbient (coborderIdeal i) k W.1 t =
    extReesAmbient (coborderIdeal i) ((k + 1) + -1) W.1
      ((extReesMul (coborderIdeal i) (k + 1) (-1)).app (op W.1) y
        (paramPiece (coborderIdeal i) W.1))
  rw [extReesAmbient_extReesMul, extReesAmbient_paramPiece, mul_one, hy]

/-- Pulling a section of `ℐⁿ` back to the conormal algebra, as an additive map. -/
def pullbackSectionAdd (n : ℕ) (W : i.coborderRange.toScheme.Opens) :
    (reesPiece (coborderIdeal i) (n : ℤ)).val.obj (op W) →+
      ((conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op (i.liftCoborder ⁻¹ᵁ W)) :=
  AddMonoidHom.mk' (Scheme.Modules.pullbackSection i.liftCoborder
    (reesPiece (coborderIdeal i) (n : ℤ)) W (i.liftCoborder ⁻¹ᵁ W) le_rfl) (fun a b => by
      unfold Scheme.Modules.pullbackSection
      rw [map_add]
      exact map_add _ _ _)

/-- The degreewise map of `Ψ` into the homogeneous pieces of the conormal algebra: the pullback in
nonnegative degree, transported along `k = max(k, 0)`, and zero in negative degree. -/
def toConormalPieceAdd (k : ℤ) (W : i.coborderRange.toScheme.Opens) :
    (extReesPiece (coborderIdeal i) k).val.obj (op W) →+
      ((conormalAlgebra i).algebra.piece k).val.obj (op (i.liftCoborder ⁻¹ᵁ W)) :=
  if h : 0 ≤ k then
    (AddEquiv.cast (M := fun d : ℤ =>
        ((conormalAlgebra i).algebra.piece d).val.obj (op (i.liftCoborder ⁻¹ᵁ W)))
      (Int.toNat_of_nonneg h)).toAddMonoidHom.comp (pullbackSectionAdd i k.toNat W)
  else 0

/-- In negative degree the degreewise map of `Ψ` is zero. -/
theorem toConormalPieceAdd_of_neg {k : ℤ} (hk : k < 0) (W : i.coborderRange.toScheme.Opens) :
    toConormalPieceAdd i k W = 0 := dite_eq_right (not_le.mpr hk)

/-- In nonnegative degree the degreewise map of `Ψ` agrees, up to the transport along
`k = max(k, 0)`, with the pullback of sections. -/
theorem toConormalPieceAdd_heq {k : ℤ} (hk : 0 ≤ k) (W : i.coborderRange.toScheme.Opens)
    (x : (extReesPiece (coborderIdeal i) k).val.obj (op W)) :
    HEq (toConormalPieceAdd i k W x) (pullbackSectionAdd i k.toNat W x) := by
  rw [toConormalPieceAdd, dite_eq_left hk]
  exact cast_heq _ _

/-- **`Ψ` on the direct sum of the homogeneous sections**: the degreewise maps
`toConormalPieceAdd`, assembled. -/
def toConormalTotal (W : i.coborderRange.toScheme.Opens) :
    (extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.Total (op W) →+
      (conormalAlgebra i).algebra.toPresheafGradedAlgebra.Total (op (i.liftCoborder ⁻¹ᵁ W)) :=
  DirectSum.map fun k => toConormalPieceAdd i k W

/-- On the direct sum of homogeneous sections, the map induced by `Ψ` into the ungraded conormal
algebra is `toConormalTotal` followed by the comparison map `ungradedCommUnit`. -/
theorem ungradedTotal_eq_unit_toConormalTotal (W : i.coborderRange.toScheme.Opens)
    (T : (extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.Total (op W)) :
    ungradedTotal (extReesGradedAlgebra (coborderIdeal i))
        (conormalPushforwardAlgebra i i.liftCoborder) (toConormalUnitalHom i) (op W) T =
      (ungradedCommUnit Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int
        (i.liftCoborder ⁻¹ᵁ W)).hom (toConormalTotal i W T) := by
  set F := (ungradedCommUnit Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int
    (i.liftCoborder ⁻¹ᵁ W)).hom
  induction T using Stacks.GradedAlgebra.incl_induction with
  | zero => exact (map_zero _).trans ((congrArg F (map_zero _)).trans (map_zero _)).symm
  | incl k x =>
    have hmap : toConormalTotal i W
        ((extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.incl k x) =
        (conormalAlgebra i).algebra.toPresheafGradedAlgebra.incl k (toConormalPieceAdd i k W x) :=
      DirectSum.map_of _ _ _
    rw [hmap]
    refine (ungradedTotal_incl _ _ _ k (op W) x).trans ?_
    show toConormalExtAdd i k (op W) x = _
    rcases lt_or_ge k 0 with hk | hk
    · rw [toConormalExtAdd_of_neg i hk, toConormalPieceAdd_of_neg i hk]
      exact ((congrArg F (Stacks.GradedAlgebra.incl_zero _ _)).trans (map_zero _)).symm
    · rw [toConormalExtAdd_of_nonneg i hk]
      exact congrArg F (Stacks.GradedAlgebra.incl_eq_incl_of_heq _ (Int.toNat_of_nonneg hk)
        (toConormalPieceAdd_heq i hk W x).symm)
  | add T T' hT hT' =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hT hT').trans
      ((map_add _ _ _).symm.trans (congrArg F (map_add _ _ _).symm)))

/-- **The kernel of `Ψ` on the direct sum of homogeneous sections over an affine open is the
ideal generated by `t⁻¹`.** -/
theorem mem_span_param_of_toConormalTotal_eq_zero (W : i.coborderRange.toScheme.affineOpens)
    (T : (extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.Total (op W.1))
    (hT : toConormalTotal i W.1 T = 0) :
    T ∈ Ideal.span {(extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.incl (-1)
      (paramPiece (coborderIdeal i) W.1)} := by
  classical
  let T' : DirectSum ℤ fun k =>
      (((extReesGradedAlgebra (coborderIdeal i)).piece k).val.obj (op W.1) : Type u) := T
  have hT' : DirectSum.map (fun k => toConormalPieceAdd i k W.1) T' = 0 := hT
  have hcomp : ∀ k, toConormalPieceAdd i k W.1 (T' k) = 0 := fun k => by
    exact (DirectSum.map_apply _ _ _).symm.trans (congrArg (fun S => S k) hT')
  have hsum : T = ∑ k ∈ T'.support,
      (extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.incl k (T' k) :=
    (DirectSum.sum_support_of T').symm
  rw [hsum]
  refine Ideal.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy⟩ := exists_incl_eq_param_mul i k W (T' k) (fun hk => by
    have hh := toConormalPieceAdd_heq i hk W.1 (T' k)
    rw [hcomp k] at hh
    have hz : HEq (0 : ((conormalAlgebra i).algebra.piece k).val.obj
        (op (i.liftCoborder ⁻¹ᵁ W.1)))
        (0 : ((conormalAlgebra i).algebra.piece (k.toNat : ℤ)).val.obj
          (op (i.liftCoborder ⁻¹ᵁ W.1))) := by
      have e : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
      generalize (k.toNat : ℤ) = d at e ⊢
      subst e
      rfl
    exact eq_of_heq (hh.symm.trans hz))
  rw [hy]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- **The kernel of `Ψ` over an affine open is generated by `t⁻¹`.** -/
theorem ker_toConormalUngradedHom_app (W : i.coborderRange.toScheme.affineOpens) :
    RingHom.ker ((toConormalUngradedHom i).right.hom.app (op W.1)).hom =
      Ideal.span {paramUngraded (coborderIdeal i) W.1} := by
  apply le_antisymm
  · intro a ha
    obtain ⟨T, rfl⟩ := (bijective_ungradedCommUnit_of_isAffineOpen i.coborderRange.toScheme
      (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _) W.2).2 a
    have h1 : ((toConormalUngradedHom i).right.hom.app (op W.1)).hom
        ((ungradedCommUnit i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
          (extReesGradedAlgebra_mul_comm _) W.1).hom T) =
        ungradedTotal (extReesGradedAlgebra (coborderIdeal i))
          (conormalPushforwardAlgebra i i.liftCoborder) (toConormalUnitalHom i) (op W.1) T :=
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (ungradedCommToSheaf_comp_toConormalUngradedHom i) (op W.1)) T
    rw [RingHom.mem_ker, h1] at ha
    have ha' := (ungradedTotal_eq_unit_toConormalTotal i W.1 T).symm.trans ha
    have hT : toConormalTotal i W.1 T = 0 :=
      (bijective_ungradedCommUnit_of_isAffineOpen Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int (W.2.preimage i.liftCoborder)).1
        (ha'.trans (map_zero _).symm)
    have hspan := mem_span_param_of_toConormalTotal_eq_zero i W T hT
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hspan
    have hc' : T = c * (extReesGradedAlgebra (coborderIdeal i)).toPresheafGradedAlgebra.incl (-1)
        (paramPiece (coborderIdeal i) W.1) := hc.symm
    rw [hc']
    exact (map_mul (ungradedCommUnit i.coborderRange.toScheme
      (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _)
        W.1).hom c _).symm ▸ Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact toConormalUngradedHom_paramUngraded i W.1

end Stacks.Deformation

end
