module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.SpecialFibre
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.LocalEquation
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.UnitBranchGlobalEquation
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# The parameter `t⁻¹` as a global function on the deformation space

Let `ℐ` be a quasi-coherent ideal sheaf on a scheme `X` and `D = Spec_X(𝒪_X[t⁻¹, ℐt])` its
deformation space. Over an open `W ⊆ X` the homogeneous sections of the extended Rees algebra
embed into the Laurent polynomials `Γ(X, W)[T, T⁻¹]`, a section `x` of degree `k` going to
`x T^k`. This embedding is a ring map, injective on the direct sum of the homogeneous pieces.

Consequently the section `t⁻¹` is a nonzerodivisor on every affine chart `π⁻¹(W)`, so its zero
scheme is an effective Cartier divisor on `D`. For an immersion `i : Z ⟶ X` that zero scheme is
the normal cone `C_ZX`, embedded by `Stacks.Deformation.normalConeToDeformation`.

## Main definitions

* `Stacks.Deformation.extReesLaurent`: the embedding into Laurent polynomials.
* `Stacks.Deformation.paramGlobal`: the global function `t⁻¹` on `D`.

## Main results

* `Stacks.Deformation.isEffectiveCartierDivisor_zeroScheme_paramGlobal`: `Z(t⁻¹)` is an
  effective Cartier divisor on `D`.
* `Stacks.Deformation.ker_normalConeToDeformation`: the ideal of `C_ZX ⊆ D` is the ideal of
  `Z(t⁻¹)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec Stacks.Blowup
  Stacks.Conormal

universe u

namespace Stacks.Deformation

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The Laurent embedding -/

/-- The image of a homogeneous section of degree `k` in the Laurent polynomials, as an additive
map: `x ↦ x T^k`. -/
def extReesLaurentPiece (W : X.Opens) (k : ℤ) :
    ((extReesGradedAlgebra I).piece k).val.obj (op W) →+ LaurentPolynomial Γ(X, W) :=
  (AddMonoidHom.mulRight (LaurentPolynomial.T k : LaurentPolynomial Γ(X, W))).comp
    ((LaurentPolynomial.C (R := Γ(X, W))).toAddMonoidHom.comp
      (AddMonoidHom.mk' (extReesAmbient I k W) (extReesAmbient_add I k W)))

/-- The Laurent image of a homogeneous section `x` of degree `k` is `x T^k`. -/
theorem extReesLaurentPiece_apply (W : X.Opens) (k : ℤ)
    (x : ((extReesGradedAlgebra I).piece k).val.obj (op W)) :
    extReesLaurentPiece I W k x =
      LaurentPolynomial.C (extReesAmbient I k W x) * LaurentPolynomial.T k := rfl

/-- The Laurent embedding as an additive map. -/
def extReesLaurentAdd (W : X.Opens) :
    (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W) →+
      LaurentPolynomial Γ(X, W) :=
  DirectSum.toAddMonoid (fun k => extReesLaurentPiece I W k)

/-- On a homogeneous section of degree `k`, the additive Laurent embedding is
`extReesLaurentPiece`. -/
theorem extReesLaurentAdd_incl (W : X.Opens) (k : ℤ)
    (x : ((extReesGradedAlgebra I).piece k).val.obj (op W)) :
    extReesLaurentAdd I W ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl k x) =
      extReesLaurentPiece I W k x :=
  DirectSum.toAddMonoid_of (β := fun k => ((extReesGradedAlgebra I).piece k).val.obj (op W))
    (fun k => extReesLaurentPiece I W k) k x

/-- The additive Laurent embedding is multiplicative. -/
theorem extReesLaurentAdd_mul (W : X.Opens)
    (a b : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W)) :
    extReesLaurentAdd I W (a * b) = extReesLaurentAdd I W a * extReesLaurentAdd I W b := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | incl i x =>
    induction b using Stacks.GradedAlgebra.incl_induction with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | incl j y =>
      refine (congrArg (extReesLaurentAdd I W)
        ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl_mul_incl i j x y)).trans ?_
      refine ((extReesLaurentAdd_incl I W (i + j) _).trans
        (extReesLaurentPiece_apply I W _ _)).trans ?_
      refine Eq.trans (congrArg (fun a => LaurentPolynomial.C a * LaurentPolynomial.T (i + j))
        (extReesAmbient_extReesMul I i j W x y)) ?_
      refine Eq.trans ?_ (congrArg₂ (· * ·)
        ((extReesLaurentAdd_incl I W i x).trans (extReesLaurentPiece_apply I W i x)).symm
        ((extReesLaurentAdd_incl I W j y).trans (extReesLaurentPiece_apply I W j y)).symm)
      rw [map_mul, LaurentPolynomial.T_add]
      ring
    | add b b' hb hb' => rw [mul_add, map_add, map_add, hb, hb', mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, map_add, ha, ha', add_mul]

/-- **The embedding of the homogeneous sections of the extended Rees algebra into the Laurent
polynomials** `Γ(X, W)[T, T⁻¹]`, a ring map. -/
def extReesLaurent (W : X.Opens) :
    (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W) →+*
      LaurentPolynomial Γ(X, W) :=
  { extReesLaurentAdd I W with
    map_one' := by
      refine ((extReesLaurentAdd_incl I W 0 _).trans (extReesLaurentPiece_apply I W 0 _)).trans ?_
      refine (congrArg (fun a => LaurentPolynomial.C a * LaurentPolynomial.T (0 : ℤ))
        (extReesAmbient_extReesOne I (op W))).trans ?_
      simp
    map_mul' := extReesLaurentAdd_mul I W }

/-- The Laurent embedding sends a homogeneous section `x` of degree `k` to `x T^k`. -/
theorem extReesLaurent_incl (W : X.Opens) (k : ℤ)
    (x : ((extReesGradedAlgebra I).piece k).val.obj (op W)) :
    extReesLaurent I W ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl k x) =
      LaurentPolynomial.C (extReesAmbient I k W x) * LaurentPolynomial.T k :=
  (extReesLaurentAdd_incl I W k x).trans (extReesLaurentPiece_apply I W k x)

/-- The image in `Γ(X, W)` of the zero section of degree `k` is zero. -/
theorem extReesAmbient_zero (k : ℤ) (W : X.Opens) :
    extReesAmbient I k W 0 = 0 :=
  map_zero (AddMonoidHom.mk' (extReesAmbient I k W) (extReesAmbient_add I k W))

/-- The coefficient of `T^n` in the Laurent image of a section is the image in `Γ(X, W)` of its
homogeneous component of degree `n`. -/
theorem extReesLaurent_apply_coeff (W : X.Opens)
    (t : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W)) (n : ℤ) :
    (extReesLaurent I W t).coeff n =
      extReesAmbient I n W
        ((show DirectSum ℤ fun k => ((extReesGradedAlgebra I).piece k).val.obj (op W) from t)
          n) := by
  classical
  induction t using Stacks.GradedAlgebra.incl_induction with
  | zero =>
    rw [map_zero]
    exact (extReesAmbient_zero I n W).symm
  | incl k x =>
    rw [extReesLaurent_incl, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
    show (Finsupp.single k (extReesAmbient I k W x)) n = extReesAmbient I n W
      ((DirectSum.of (fun k => ((extReesGradedAlgebra I).piece k).val.obj (op W)) k x) n)
    by_cases h : k = n
    · subst h
      exact Finsupp.single_eq_same.trans (congrArg (extReesAmbient I k W)
        (DirectSum.of_eq_same (β := fun k => ((extReesGradedAlgebra I).piece k).val.obj (op W))
          k x).symm)
    · exact (Finsupp.single_eq_of_ne' h).trans ((extReesAmbient_zero I n W).symm.trans
        (congrArg (extReesAmbient I n W)
          (DirectSum.of_eq_of_ne (β := fun k => ((extReesGradedAlgebra I).piece k).val.obj (op W))
            k n x (Ne.symm h)).symm))
  | add t t' ht ht' =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ht, ht']
    exact (extReesAmbient_add I n W _ _).symm

/-- **The Laurent embedding is injective.** -/
theorem extReesLaurent_injective (W : X.Opens) : Function.Injective (extReesLaurent I W) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  have hc : ∀ n, (show DirectSum ℤ fun k => ((extReesGradedAlgebra I).piece k).val.obj (op W)
      from t) n = 0 := fun n => by
    refine extReesAmbient_injective I n W ((extReesLaurent_apply_coeff I W t n).symm.trans ?_)
    exact (congrArg (fun p : LaurentPolynomial Γ(X, W) => p.coeff n) ht).trans
      (extReesAmbient_zero I n W).symm
  exact DirectSum.ext hc

/-- An element whose image under an injective ring map into a commutative ring is a
nonzerodivisor is a nonzerodivisor. -/
theorem isRegular_of_injective {A B : Type*} [Ring A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {a : A} (ha : IsRegular (f a)) : IsRegular a :=
  ⟨fun x y h => hf (ha.1 (by simpa only [map_mul] using congrArg f h)),
    fun x y h => hf (ha.2 (by simpa only [map_mul] using congrArg f h))⟩

/-- The image of a nonzerodivisor under a ring isomorphism is a nonzerodivisor. -/
theorem isRegular_map_ringEquiv {A B : Type*} [Ring A] [Ring B] (e : A ≃+* B) {a : A}
    (ha : IsRegular a) : IsRegular (e a) := by
  exact ⟨fun x y h => e.symm.injective (ha.1 (e.injective (by simpa using h))),
    fun x y h => e.symm.injective (ha.2 (e.injective (by simpa using h)))⟩

/-- The image of a nonzerodivisor under a bijective ring map is a nonzerodivisor. -/
theorem isRegular_map_of_bijective {A B : Type*} [Ring A] [Ring B] (f : A →+* B)
    (hf : Function.Bijective f) {a : A} (ha : IsRegular a) : IsRegular (f a) :=
  isRegular_map_ringEquiv (RingEquiv.ofBijective f hf) ha

/-- **`t⁻¹` is a nonzerodivisor among the homogeneous sections.** -/
theorem isRegular_incl_paramPiece (W : X.Opens) :
    IsRegular ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl (-1) (paramPiece I W)) := by
  refine isRegular_of_injective _ (extReesLaurent_injective I W) ?_
  have h : extReesLaurent I W ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl (-1)
      (paramPiece I W)) = LaurentPolynomial.T (-1) :=
    (extReesLaurent_incl I W (-1) _).trans
      ((congrArg (fun a => LaurentPolynomial.C a * LaurentPolynomial.T (-1 : ℤ))
        (extReesAmbient_paramPiece I W)).trans (by simp))
  rw [h]
  exact (LaurentPolynomial.isUnit_T (-1)).isRegular

/-! ### The chart rings of the deformation space -/

/-- The relative-spectrum situation of the extended Rees algebra of `ℐ`. -/
abbrev extReesSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} :=
  { base := X, algebra := extReesAlgebraSheaf I }

/-- The sections map of an isomorphism of algebra sheaves over one open is bijective. -/
theorem bijective_algebraSheafIso_app {A B : AlgebraSheaf X} (e : A ≅ B) (W : X.Opens) :
    Function.Bijective (e.hom.right.hom.app (op W)).hom :=
  Function.bijective_iff_has_inverse.2 ⟨(e.inv.right.hom.app (op W)).hom,
    fun c => congrArg (fun k : A ⟶ A => (k.right.hom.app (op W)).hom c) e.hom_inv_id,
    fun c => congrArg (fun k : B ⟶ B => (k.right.hom.app (op W)).hom c) e.inv_hom_id⟩

/-! ### The global function `t⁻¹` -/

/-- `t⁻¹` as a section, over `W`, of the extended Rees algebra sheaf. -/
def paramSectionOf (W : X.Opens) : AlgebraSheaf.sections (extReesAlgebraSheaf I) W :=
  ((ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
    (extReesGradedAlgebra_mul_comm I)).hom.right.hom.app (op W)).hom (paramUngraded I W)

/-- `t⁻¹` as a function on the chart `π⁻¹(W)`. -/
def paramChartOf (W : X.Opens) :
    Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W) :=
  ((universalAlgebraMap (extReesSituation I)).right.app (op W)).hom (paramSectionOf I W)

/-- **`t⁻¹` is a nonzerodivisor on every affine chart of the deformation space.** -/
theorem isRegular_paramChartOf (W : X.affineOpens) : IsRegular (paramChartOf I W.1) := by
  have := isIso_universalAlgebraMap_app (extReesSituation I) W
  refine isRegular_map_of_bijective _ (ConcreteCategory.bijective_of_isIso
    ((universalAlgebraMap (extReesSituation I)).right.app (op W.1))) ?_
  refine isRegular_map_of_bijective _ (bijective_algebraSheafIso_app
    (ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I)) W.1) ?_
  exact isRegular_map_of_bijective _ (bijective_ungradedCommUnit_of_isAffineOpen X
    (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) W.2)
    (isRegular_incl_paramPiece I W.1)

/-- The restriction of the section `t⁻¹` of the ungraded algebra sheaf from `W` to `W' ⊆ W` is the
section `t⁻¹` over `W'`. -/
theorem paramUngraded_restrict {W W' : X.Opens} (h : W' ≤ W) :
    (ungradedAlgebraSheaf X (extReesGradedAlgebra I)
        (extReesGradedAlgebra_mul_comm I)).right.obj.map (homOfLE h).op (paramUngraded I W) =
      paramUngraded I W' := by
  have hnat := ConcreteCategory.congr_hom
    (((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
      CommRingCat.{u}).unit.app (ungradedCommPresheaf X (extReesGradedAlgebra I)
        (extReesGradedAlgebra_mul_comm I))).naturality (homOfLE h).op)
    ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl (-1) (paramPiece I W))
  refine hnat.symm.trans ?_
  show (ungradedCommUnit X (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) W').hom
      ((extReesGradedAlgebra I).toPresheafGradedAlgebra.totalRestrict (homOfLE h).op
        ((extReesGradedAlgebra I).toPresheafGradedAlgebra.incl (-1) (paramPiece I W))) = _
  exact congrArg
    (ungradedCommUnit X (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) W').hom
    (((extReesGradedAlgebra I).toPresheafGradedAlgebra.totalRestrict_incl (homOfLE h).op (-1)
      (paramPiece I W)).trans (congrArg _ (paramPiece_restrict I h)))

/-- The restriction of `paramSectionOf I W` to `W' ⊆ W` is `paramSectionOf I W'`. -/
theorem paramSectionOf_restrict {W W' : X.Opens} (h : W' ≤ W) :
    (extReesAlgebraSheaf I).right.obj.map (homOfLE h).op (paramSectionOf I W) =
      paramSectionOf I W' := by
  have hnat := ConcreteCategory.congr_hom
    ((ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I)).hom.right.hom.naturality (homOfLE h).op)
    (paramUngraded I W)
  refine hnat.symm.trans ?_
  exact congrArg _ (paramUngraded_restrict I h)

/-- The restriction of `paramChartOf I W` from `π⁻¹(W)` to `π⁻¹(W')`, for `W' ⊆ W`, is
`paramChartOf I W'`. -/
theorem paramChartOf_restrict {W W' : X.Opens} (h : W' ≤ W) :
    (deformationSpace I).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono (deformationSpaceToBase I) h)).op
        (paramChartOf I W) = paramChartOf I W' := by
  have hnat := ConcreteCategory.congr_hom
    ((universalAlgebraMap (extReesSituation I)).right.naturality (homOfLE h).op)
    (paramSectionOf I W)
  refine hnat.symm.trans ?_
  exact congrArg _ (paramSectionOf_restrict I h)

/-- **The global function `t⁻¹` on the deformation space.** -/
def paramGlobal : Γ(Scheme.unitModule (deformationSpace I), ⊤) :=
  (deformationSpace I).presheaf.map
    (homOfLE (fun x _ => (trivial : x ∈ (⊤ : Set (deformationSpace I)))) :
      (⊤ : (deformationSpace I).Opens) ⟶ deformationSpaceToBase I ⁻¹ᵁ ⊤).op
    (paramChartOf I ⊤)

/-- **`t⁻¹` restricts to the chart function `paramChartOf` on every chart.** -/
theorem paramGlobal_restrict (W : X.Opens) :
    (deformationSpace I).presheaf.map (homOfLE le_top :
        deformationSpaceToBase I ⁻¹ᵁ W ⟶ ⊤).op (paramGlobal I) = paramChartOf I W := by
  refine Eq.trans ?_ (paramChartOf_restrict I (le_top : W ≤ ⊤))
  show ((deformationSpace I).presheaf.map _ ≫ (deformationSpace I).presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

/-- **The ideal of `Z(t⁻¹)` on the chart `π⁻¹(W)`, `W` affine, is generated by `t⁻¹`.** -/
theorem zeroScheme_paramGlobal_ideal (W : X.affineOpens) :
    (Stacks.Divisors.zeroScheme (deformationSpace I) (Scheme.unitModule (deformationSpace I))
        (paramGlobal I)).ideal
        ⟨deformationSpaceToBase I ⁻¹ᵁ W.1,
          Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation I) W⟩ =
      Ideal.span {paramChartOf I W.1} :=
  Stacks.Divisors.zeroScheme_ideal_of_trivialization _ _ _ _ (LinearEquiv.refl _ _) _
    (paramGlobal_restrict I W.1)

/-- **`Z(t⁻¹)` is an effective Cartier divisor on the deformation space.** -/
theorem isEffectiveCartierDivisor_zeroScheme_paramGlobal :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Divisors.zeroScheme (deformationSpace I) (Scheme.unitModule (deformationSpace I))
        (paramGlobal I)) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  obtain ⟨W, hW⟩ := Stacks.Divisors.exists_affineOpens_mem (deformationSpaceToBase I x)
  exact ⟨_, Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation I) W, hW,
    paramChartOf I W.1, isRegular_paramChartOf I W, zeroScheme_paramGlobal_ideal I W⟩

end Stacks.Deformation

namespace Stacks.Deformation

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The normal cone is the zero scheme of `t⁻¹` in the deformation space**: the ideal of the
closed immersion `κ : C_ZX ⟶ D` is the ideal of `Z(t⁻¹)`. -/
theorem ker_normalConeToDeformation :
    (normalConeToDeformation i).ker =
      Stacks.Divisors.zeroScheme (deformationSpace (coborderIdeal i))
        (Scheme.unitModule (deformationSpace (coborderIdeal i)))
        (paramGlobal (coborderIdeal i)) := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun W : i.coborderRange.toScheme.affineOpens =>
      (⟨deformationSpaceToBase (coborderIdeal i) ⁻¹ᵁ W.1,
        Stacks.RelativeSpec.isAffineOpen_toBase_preimage (deformationSituation i) W⟩ :
          (deformationSpace (coborderIdeal i)).affineOpens)) ?_ fun W => ?_
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · exact (ker_normalConeToDeformation_ideal i W).trans
      (zeroScheme_paramGlobal_ideal (coborderIdeal i) W).symm

end Stacks.Deformation

end
