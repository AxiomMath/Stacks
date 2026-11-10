module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.DeformationBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.DeformationComplement
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The deformation space under base change, away from the special fibre

Let `h : U' ⟶ U` be a morphism of schemes and `ℐ` a quasi-coherent ideal sheaf on `U`. Away from
`t⁻¹ = 0` the deformation space is `U × 𝐆_m`: over an affine open `Spec A` its ring of functions is
`A[T, T⁻¹]` (`Stacks.Deformation.exists_ringEquiv_laurent'`). Hence the closed immersion
`D(h⁻¹ℐ) ⟶ D(ℐ) ×_U U'` (`Stacks.Deformation.isClosedImmersion_deformationBaseChangeLift`) is an
isomorphism away from the special fibres: over affine opens `Spec A' ⊆ h⁻¹(Spec A)` it is
`Spec A'[T, T⁻¹] ⟶ Spec(A[T, T⁻¹] ⊗_A A')`, whose ring map has the left inverse
`T ↦ T ⊗ 1, a' ↦ 1 ⊗ a'`.

## Main results

* `Stacks.Deformation.laurent_ringHom_ext` — ring maps out of `R[T, T⁻¹]` are determined by `C`
  and `T`.
* `Stacks.Deformation.injective_appLE_complementChart` — injectivity of the ring map over the
  charts.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Deformation

/-- **Ring maps out of the Laurent polynomials are determined by the constants and `T`.** -/
theorem laurent_ringHom_ext {R S : Type*} [CommRing R] [CommRing S]
    {f g : LaurentPolynomial R →+* S}
    (hC : ∀ r, f (LaurentPolynomial.C r) = g (LaurentPolynomial.C r))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  have hTn : ∀ n : ℕ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := fun n => by
    have : (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial R) = LaurentPolynomial.T 1 ^ n := by
      rw [LaurentPolynomial.T_pow, mul_one]
    rw [this, map_pow, map_pow, hT]
  have hTz : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := fun n => by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · exact hTn m
    · have h1 : (LaurentPolynomial.T (-(m : ℤ)) : LaurentPolynomial R) *
          LaurentPolynomial.T m = 1 := by
        rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
      have hf := congrArg f h1
      have hg := congrArg g h1
      rw [map_mul, map_one] at hf hg
      rw [hTn m] at hf
      linear_combination g (LaurentPolynomial.T (-(m : ℤ))) * hf -
        f (LaurentPolynomial.T (-(m : ℤ))) * hg
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, hC, hTz]

section Chart

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData)

/-- The morphism `D(h⁻¹ℐ) ⟶ D(ℐ) ×_U U'`. -/
abbrev baseChangeLift : deformationSpace (J.comap h) ⟶ pullback (deformationSpaceToBase J) h :=
  pullback.lift (deformationBaseChangeMap h J) (deformationSpaceToBase (J.comap h))
    (deformationBaseChangeMap_toBase h J)

/-- The affine open `(D(t⁻¹) ∩ π⁻¹W) ×_W W'` of `D(ℐ) ×_U U'`. -/
abbrev complementChart (W : U.affineOpens) (W' : U'.affineOpens) :
    (pullback (deformationSpaceToBase J) h).Opens :=
  pullback.fst _ h ⁻¹ᵁ (deformationSpace J).basicOpen (paramChartOf J W.1) ⊓
    pullback.snd _ h ⁻¹ᵁ W'.1

/-- The restricted pullback square of `complementChart h J W W'`, with its affine corners. -/
private theorem isPullback_complementChart (W : U.affineOpens) (W' : U'.affineOpens)
    (hW' : W'.1 ≤ h ⁻¹ᵁ W.1) :
    IsPullback ((pullback.fst _ h).resLE _ (complementChart h J W W') inf_le_left)
      ((pullback.snd _ h).resLE _ (complementChart h J W W') inf_le_right)
      ((deformationSpaceToBase J).resLE W.1 _ ((deformationSpace J).basicOpen_le _))
      (h.resLE W.1 W'.1 hW') ∧ IsAffine ((deformationSpace J).basicOpen (paramChartOf J W.1)) ∧
      IsAffine W'.1 ∧ IsAffine W.1 :=
  ⟨Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback (deformationSpaceToBase J) h) hW'
    ((deformationSpace J).basicOpen_le (paramChartOf J W.1)) (UY := complementChart h J W W') rfl,
    (Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation J) W).basicOpen _,
    W'.2, W.2⟩

/-- If `W' ⊆ h⁻¹W`, then `complementChart h J W W'` is an affine open. -/
theorem isAffineOpen_complementChart (W : U.affineOpens) (W' : U'.affineOpens)
    (hW' : W'.1 ≤ h ⁻¹ᵁ W.1) : IsAffineOpen (complementChart h J W W') := by
  obtain ⟨hsq, _, _, _⟩ := isPullback_complementChart h J W W' hW'
  exact IsAffine.of_isPullback hsq

/-- If `W' ⊆ h⁻¹W`, the inverse image of `W'` in `D(h⁻¹ℐ)` lies in the inverse image under
`deformationBaseChangeMap h J` of the inverse image of `W` in `D(ℐ)`. -/
private theorem preimage_toBase_le (W : U.affineOpens) (W' : U'.affineOpens)
    (hW' : W'.1 ≤ h ⁻¹ᵁ W.1) :
    deformationSpaceToBase (J.comap h) ⁻¹ᵁ W'.1 ≤
      deformationBaseChangeMap h J ⁻¹ᵁ (deformationSpaceToBase J ⁻¹ᵁ W.1) := by
  rw [← Scheme.Hom.comp_preimage, deformationBaseChangeMap_toBase, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ hW'

/-- If `W' ⊆ h⁻¹W`, the inverse image of `complementChart h J W W'` under `baseChangeLift h J` is
the basic open of `t⁻¹` over `W'` in `D(h⁻¹ℐ)`. -/
theorem preimage_complementChart (W : U.affineOpens) (W' : U'.affineOpens)
    (hW' : W'.1 ≤ h ⁻¹ᵁ W.1) :
    baseChangeLift h J ⁻¹ᵁ complementChart h J W W' =
      (deformationSpace (J.comap h)).basicOpen (paramChartOf (J.comap h) W'.1) := by
  have hle := preimage_toBase_le h J W W' hW'
  simp only [complementChart, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    pullback.lift_fst, pullback.lift_snd]
  rw [Scheme.Hom.preimage_basicOpen, inf_comm,
    ← (deformationSpace (J.comap h)).basicOpen_res _ (homOfLE hle).op]
  congr 1
  rw [← deformationMap_appLE_paramChartOf h J (J.comap h) le_rfl W W'.1 hW' hle, Scheme.Hom.appLE]
  rfl

/-- `appLE` is compatible with the identifications `Γ(X, U) ≃ Γ(U)` of the restricted maps. -/
private theorem appLE_hom_topIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x) : (f.appLE U V e).hom (U.topIso.hom.hom x) =
      V.topIso.hom.hom ((f.resLE U V e).appTop.hom x) :=
  congrArg (fun m => m.hom x) (arrowResLEAppIso f U V e).hom.w

/-- If `W' ⊆ h⁻¹W`, the ring of sections of `complementChart h J W W'` is generated by the images
of the sections of `D(t⁻¹) ∩ π⁻¹W` and of `W'`. -/
theorem closure_complementChart (W : U.affineOpens) (W' : U'.affineOpens)
    (hW' : W'.1 ≤ h ⁻¹ᵁ W.1) :
    Subring.closure (Set.range ((pullback.fst _ h).appLE
        ((deformationSpace J).basicOpen (paramChartOf J W.1)) (complementChart h J W W')
        inf_le_left).hom ∪
      Set.range ((pullback.snd _ h).appLE W'.1 (complementChart h J W W') inf_le_right).hom) =
      ⊤ := by
  obtain ⟨hsq, _, _, _⟩ := isPullback_complementChart h J W W' hW'
  have hpo := isPushout_appTop_of_isPullback hsq
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout hpo
  let e := (complementChart h J W W').topIso
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 y
  have hz : z ∈ Subring.closure (Set.range (((pullback.fst _ h).resLE _
      (complementChart h J W W') inf_le_left).appTop).hom ∪
      Set.range (((pullback.snd _ h).resLE _ (complementChart h J W W')
        inf_le_right).appTop).hom) := by
    rw [hcl]
    trivial
  have hmap : e.hom.hom z ∈ (Subring.closure _).map e.hom.hom := ⟨z, hz, rfl⟩
  rw [RingHom.map_closure] at hmap
  refine Subring.closure_mono ?_ hmap
  rintro _ ⟨w, hw, rfl⟩
  rcases hw with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact Or.inl ⟨_, appLE_hom_topIso _ _ _ _ _⟩
  · exact Or.inr ⟨_, appLE_hom_topIso _ _ _ _ _⟩

end Chart

section Injective

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData)

/-- Two `appLE`s along equal morphisms agree. -/
theorem appLE_congr_hom {Y T : Scheme.{u}} {f g : Y ⟶ T} (hfg : f = g) (A : T.Opens) (B : Y.Opens)
    (e₁ : B ≤ f ⁻¹ᵁ A) (e₂ : B ≤ g ⁻¹ᵁ A) : f.appLE A B e₁ = g.appLE A B e₂ := by
  subst hfg
  rfl

/-- Sections pulled back along `g` and then along `f` are pulled back along `k = f ≫ g`. -/
private theorem appLE_apply_appLE {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    (hk : f ≫ g = k) {U : Z.Opens} {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ k ⁻¹ᵁ U) (a) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = (k.appLE U W e₃).hom a :=
  congrArg (fun m => m.hom a) ((Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂).trans
    (appLE_congr_hom hk _ _ _ _))

variable (W : U.affineOpens) (W' : U'.affineOpens) (hW' : W'.1 ≤ h ⁻¹ᵁ W.1)

include hW' in
/-- If `W' ⊆ h⁻¹W`, the basic open of `t⁻¹` over `W'` in `D(h⁻¹ℐ)` lies in the inverse image under
`deformationBaseChangeMap h J` of the basic open of `t⁻¹` over `W` in `D(ℐ)`. -/
theorem le_preimage_basicOpen_param :
    (deformationSpace (J.comap h)).basicOpen (paramChartOf (J.comap h) W'.1) ≤
      deformationBaseChangeMap h J ⁻¹ᵁ (deformationSpace J).basicOpen (paramChartOf J W.1) := by
  intro x hx
  have hx' : (pullback.fst _ h) ((baseChangeLift h J) x) ∈
      (deformationSpace J).basicOpen (paramChartOf J W.1) :=
    ((preimage_complementChart h J W W' hW').ge hx).1
  rwa [← Scheme.Hom.comp_apply, pullback.lift_fst] at hx'

include hW' in
/-- **Injectivity of the base change map over the charts away from the special fibre**: the ring
map `Γ((D(t⁻¹) ∩ π⁻¹W) ×_W W') ⟶ Γ(D(t⁻¹) ∩ π'⁻¹W')` has a left inverse. -/
theorem injective_appLE_complementChart
    (hε : (deformationSpace (J.comap h)).basicOpen (paramChartOf (J.comap h) W'.1) ≤
      baseChangeLift h J ⁻¹ᵁ complementChart h J W W') :
    Function.Injective ((baseChangeLift h J).appLE (complementChart h J W W')
      ((deformationSpace (J.comap h)).basicOpen (paramChartOf (J.comap h) W'.1)) hε).hom := by
  have hBW : (deformationSpace J).basicOpen (paramChartOf J W.1) ≤
      deformationSpaceToBase J ⁻¹ᵁ W.1 := (deformationSpace J).basicOpen_le _
  have hB'W' : (deformationSpace (J.comap h)).basicOpen (paramChartOf (J.comap h) W'.1) ≤
      deformationSpaceToBase (J.comap h) ⁻¹ᵁ W'.1 := (deformationSpace (J.comap h)).basicOpen_le _
  have hφB := le_preimage_basicOpen_param h J W W' hW'
  let fst := (pullback.fst (deformationSpaceToBase J) h).appLE
    ((deformationSpace J).basicOpen (paramChartOf J W.1)) (complementChart h J W W') inf_le_left
  let snd := (pullback.snd (deformationSpaceToBase J) h).appLE W'.1 (complementChart h J W W')
    inf_le_right
  let ε := (baseChangeLift h J).appLE (complementChart h J W W')
    ((deformationSpace (J.comap h)).basicOpen (paramChartOf (J.comap h) W'.1)) hε
  let B := (deformationSpace J).basicOpen (paramChartOf J W.1)
  let B' := (deformationSpace (J.comap h)).basicOpen (paramChartOf (J.comap h) W'.1)
  let π := deformationSpaceToBase J
  let π' := deformationSpaceToBase (J.comap h)
  let φ := deformationBaseChangeMap h J
  have E1 : ∀ y, ε.hom (fst.hom y) = (φ.appLE B B' hφB).hom y :=
    appLE_apply_appLE (pullback.lift_fst _ _ _) _ _ _
  have E2 : ∀ a, ε.hom (snd.hom a) = (π'.appLE W'.1 B' hB'W').hom a :=
    appLE_apply_appLE (pullback.lift_snd _ _ _) _ _ _
  have E3 : ∀ a, (φ.appLE B B' hφB).hom ((π.appLE W.1 B hBW).hom a) =
      (π'.appLE W'.1 B' hB'W').hom ((h.appLE W.1 W'.1 hW').hom a) := fun a =>
    (appLE_apply_appLE (deformationBaseChangeMap_toBase h J) _ _ (hB'W'.trans
      (π'.preimage_mono hW')) a).trans (appLE_apply_appLE rfl _ _ _ a).symm
  have E5 : ∀ a, fst.hom ((π.appLE W.1 B hBW).hom a) = snd.hom ((h.appLE W.1 W'.1 hW').hom a) :=
    fun a => (appLE_apply_appLE (pullback.condition (f := π) (g := h)) _ _
      (inf_le_right.trans ((pullback.snd π h).preimage_mono hW')) a).trans
      (appLE_apply_appLE rfl _ _ _ a).symm
  have hle := preimage_toBase_le h J W W' hW'
  have E4 : (φ.appLE B B' hφB).hom (paramBasicOpen J W.1) = paramBasicOpen (J.comap h) W'.1 := by
    have m1 := Scheme.Hom.map_appLE φ hφB (homOfLE hBW).op
    have m2 := Scheme.Hom.appLE_map φ hle (homOfLE hB'W').op
    refine (congrArg (fun m => m.hom (paramChartOf J W.1)) (m1.trans m2.symm)).trans ?_
    exact congrArg ((deformationSpace (J.comap h)).presheaf.map (homOfLE hB'W').op).hom
      (deformationMap_appLE_paramChartOf h J (J.comap h) le_rfl W W'.1 hW' hle)
  obtain ⟨θ, hθC, hθT⟩ := exists_ringEquiv_laurent' J W
  obtain ⟨θ', hθ'C, hθ'T⟩ := exists_ringEquiv_laurent' (J.comap h) W'
  have hθC' : ∀ a, θ.symm (LaurentPolynomial.C a) = (π.appLE W.1 B hBW).hom a := fun a => by
    rw [← hθC a, RingEquiv.symm_apply_apply]
  have hx : IsUnit (fst.hom (θ.symm (LaurentPolynomial.T 1))) :=
    ((LaurentPolynomial.isUnit_T 1).map θ.symm.toRingHom).map fst.hom
  let ψ : Γ(deformationSpace (J.comap h), B') →+* Γ(pullback (deformationSpaceToBase J) h,
      complementChart h J W W') :=
    (LaurentPolynomial.eval₂ snd.hom hx.unit).comp θ'.toRingHom
  have hTT : θ' ((φ.appLE B B' hφB).hom (θ.symm (LaurentPolynomial.T 1))) =
      LaurentPolynomial.T 1 := by
    have h1 : θ.symm (LaurentPolynomial.T 1) * paramBasicOpen J W.1 = 1 := by
      have hp : paramBasicOpen J W.1 = θ.symm (LaurentPolynomial.T (-1)) := by
        rw [← hθT, RingEquiv.symm_apply_apply]
      rw [hp, ← map_mul, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
        map_one]
    have h2 := congrArg (fun z => θ' ((φ.appLE B B' hφB).hom z)) h1
    simp only [map_mul, map_one, E4, hθ'T] at h2
    calc θ' ((φ.appLE B B' hφB).hom (θ.symm (LaurentPolynomial.T 1)))
        = θ' ((φ.appLE B B' hφB).hom (θ.symm (LaurentPolynomial.T 1))) *
            (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) := by
          rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, mul_one]
      _ = LaurentPolynomial.T 1 := by rw [← mul_assoc, h2, one_mul]
  have K2 : ∀ a, ψ ((π'.appLE W'.1 B' hB'W').hom a) = snd.hom a := fun a => by
    change LaurentPolynomial.eval₂ snd.hom hx.unit (θ' ((π'.appLE W'.1 B' hB'W').hom a)) = _
    rw [hθ'C, LaurentPolynomial.eval₂_C]
  have K1 : ∀ y, ψ ((φ.appLE B B' hφB).hom y) = fst.hom y := by
    have hext : (ψ.comp (φ.appLE B B' hφB).hom).comp θ.symm.toRingHom =
        fst.hom.comp θ.symm.toRingHom := by
      refine laurent_ringHom_ext (fun a => ?_) ?_
      · change ψ ((φ.appLE B B' hφB).hom (θ.symm (LaurentPolynomial.C a))) =
          fst.hom (θ.symm (LaurentPolynomial.C a))
        rw [hθC' a, E3 a, E5 a, K2]
      · change LaurentPolynomial.eval₂ snd.hom hx.unit
            (θ' ((φ.appLE B B' hφB).hom (θ.symm (LaurentPolynomial.T 1)))) =
          fst.hom (θ.symm (LaurentPolynomial.T 1))
        rw [hTT, LaurentPolynomial.eval₂_T, zpow_one, IsUnit.unit_spec]
    intro y
    obtain ⟨p, rfl⟩ := θ.symm.surjective y
    exact congrArg (fun f => f p) hext
  have K3 : ∀ z, ψ (ε.hom z) = z := by
    have heq : Set.EqOn (ψ.comp ε.hom) (RingHom.id _)
        (Set.range fst.hom ∪ Set.range snd.hom) := by
      rintro _ (⟨y, rfl⟩ | ⟨a, rfl⟩)
      · simp only [RingHom.comp_apply, RingHom.id_apply, E1, K1]
      · simp only [RingHom.comp_apply, RingHom.id_apply, E2, K2]
    intro z
    exact RingHom.eqOn_set_closure heq (show z ∈ Subring.closure
      (Set.range fst.hom ∪ Set.range snd.hom) from closure_complementChart h J W W' hW' ▸ trivial)
  exact Function.LeftInverse.injective K3

end Injective

section Iso

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData)

/-- If `A = V`, `B = f⁻¹A`, `f⁻¹V = V'` and `f.appLE V V'` is bijective, then so is `f.app A`
followed by the restriction `Γ(Y, f⁻¹A) ⟶ Γ(Y, B)`. -/
theorem bijective_app_eqToHom {Y T : Scheme.{u}} (f : Y ⟶ T) (A V : T.Opens) (hA : A = V)
    (B : Y.Opens) (hB : B = f ⁻¹ᵁ A) (V' : Y.Opens) (hV' : f ⁻¹ᵁ V = V')
    (hs : Function.Bijective (f.appLE V V' hV'.ge).hom) :
    Function.Bijective (f.app A ≫ Y.presheaf.map (eqToHom hB).op).hom := by
  subst hA hV' hB
  have : f.appLE A (f ⁻¹ᵁ A) le_rfl = f.app A := (Scheme.Hom.app_eq_appLE f).symm
  rw [this] at hs
  simpa using hs

/-- **Over the charts away from the special fibre, `D(h⁻¹ℐ) ⟶ D(ℐ) ×_U U'` is an isomorphism.** -/
theorem isIso_baseChangeLift_restrict_complementChart (W : U.affineOpens) (W' : U'.affineOpens)
    (hW' : W'.1 ≤ h ⁻¹ᵁ W.1) :
    IsIso (baseChangeLift h J ∣_ complementChart h J W W') := by
  have hpre := preimage_complementChart h J W W' hW'
  have hC := isAffineOpen_complementChart h J W W' hW'
  have : IsAffine (complementChart h J W W') := hC
  have : IsAffine (baseChangeLift h J ⁻¹ᵁ complementChart h J W W') := by
    have : IsAffineOpen (baseChangeLift h J ⁻¹ᵁ complementChart h J W W') := by
      rw [hpre]
      exact (Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation (J.comap h))
        W').basicOpen _
    exact this
  suffices hT : IsIso (baseChangeLift h J ∣_ complementChart h J W W').appTop by
    have := (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (baseChangeLift h J ∣_ complementChart h J W W'))).2
      (show IsIso (Spec.map _) from inferInstance)
    exact this
  rw [morphismRestrict_appTop]
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  refine bijective_app_eqToHom _ _ _ (Scheme.Opens.ι_image_top _) _ _ _ hpre ⟨?_, ?_⟩
  · exact injective_appLE_complementChart h J W W' hW' hpre.ge
  · have hsurj := Scheme.Hom.app_surjective (baseChangeLift h J) (complementChart h J W W') hC
    intro y
    have hiso : IsIso ((deformationSpace (J.comap h)).presheaf.map (homOfLE hpre.ge).op) := by
      have : homOfLE hpre.ge = eqToHom hpre.symm := Subsingleton.elim _ _
      rw [this]
      infer_instance
    obtain ⟨y', hy'⟩ := (ConcreteCategory.bijective_of_isIso
      ((deformationSpace (J.comap h)).presheaf.map (homOfLE hpre.ge).op)).2 y
    obtain ⟨x, hx⟩ := hsurj y'
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.appLE, ← hy', ← hx]
    rfl

/-- The open `(D(ℐ) ∖ Z(t⁻¹)) ×_U U'` of `D(ℐ) ×_U U'`. -/
abbrev complementPullbackOpen : (pullback (deformationSpaceToBase J) h).Opens :=
  pullback.fst _ h ⁻¹ᵁ complementOpen J

/-- Each chart `complementChart h J W W'` is contained in `complementPullbackOpen h J`. -/
theorem complementChart_le (W : U.affineOpens) (W' : U'.affineOpens) :
    complementChart h J W W' ≤ complementPullbackOpen h J := by
  intro z hz
  have h1 : pullback.fst _ h z ∈ (deformationSpace J).basicOpen (paramChartOf J W.1) := hz.1
  rw [← complementOpen_inf_preimage] at h1
  exact h1.1

/-- The inverse images in `complementPullbackOpen h J` of the charts `complementChart h J W W'`,
for affine opens `W' ⊆ h⁻¹W`, cover it. -/
theorem iSup_complementChart :
    ⨆ P : Σ W : U.affineOpens, {W' : U'.affineOpens // W'.1 ≤ h ⁻¹ᵁ W.1},
      (complementPullbackOpen h J).ι ⁻¹ᵁ complementChart h J P.1 P.2.1 = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  set z' := (complementPullbackOpen h J).ι z
  have hz' : pullback.fst _ h z' ∈ complementOpen J := z.2
  obtain ⟨W, hW⟩ := Stacks.Divisors.exists_affineOpens_mem
    (deformationSpaceToBase J (pullback.fst _ h z'))
  have hz : h (pullback.snd _ h z') ∈ W.1 := by
    have := congrArg (fun q : pullback (deformationSpaceToBase J) h ⟶ U => q z')
      (pullback.condition (f := deformationSpaceToBase J) (g := h))
    simp only [Scheme.Hom.comp_apply] at this
    rwa [← this]
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := U'.isBasis_affineOpens.exists_subset_of_mem_open
    (show pullback.snd _ h z' ∈ (h ⁻¹ᵁ W.1 : U'.Opens) from hz) (h ⁻¹ᵁ W.1).isOpen
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, ⟨⟨V, hV⟩, hVle⟩⟩, ?_⟩
  refine ⟨?_, hxV⟩
  change pullback.fst _ h z' ∈ (deformationSpace J).basicOpen (paramChartOf J W.1)
  rw [← complementOpen_inf_preimage]
  exact ⟨hz', hW⟩

/-- **Away from the special fibre, `D(h⁻¹ℐ) ⟶ D(ℐ) ×_U U'` is an isomorphism.** -/
theorem isIso_baseChangeLift_restrict_complement :
    IsIso (baseChangeLift h J ∣_ complementPullbackOpen h J) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
    (iSup_complementChart h J) fun P => ?_
  obtain ⟨W, W', hW'⟩ := P
  have himg : (complementPullbackOpen h J).ι ''ᵁ
      ((complementPullbackOpen h J).ι ⁻¹ᵁ complementChart h J W W') = complementChart h J W W' := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 (complementChart_le h J W W')
  refine (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ himg)).2 ?_
  exact isIso_baseChangeLift_restrict_complementChart h J W W' hW'

end Iso

section Generic

variable {D D' S S' : Scheme.{u}} (π : D ⟶ S) (π' : D' ⟶ S') (h : S' ⟶ S) (φ : D' ⟶ D)
  (hφ : φ ≫ π = π' ≫ h) (U : D.Opens) (U' : D'.Opens) (hUU : φ ⁻¹ᵁ U = U')

include hUU in
/-- **The open `U'` is the inverse image of `U`**, as a pullback square. -/
theorem isPullback_resLE_of_preimage :
    IsPullback U'.ι (φ.resLE U U' hUU.ge) φ U.ι := by
  refine (IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm ?_).flip
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, hUU]

include hφ in
/-- The composites `U' ⟶ D' ⟶ S' ⟶ S` and `U' ⟶ U ⟶ D ⟶ S` agree. -/
theorem resLE_comp_comp :
    (U'.ι ≫ π') ≫ h = φ.resLE U U' hUU.ge ≫ (U.ι ≫ π) := by
  rw [Category.assoc, ← hφ, ← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι]

include hUU in
/-- **If `D' ⟶ D ×_S S'` is an isomorphism over the inverse image of `U`, then
`U' ⟶ U ×_S S'` is an isomorphism.** -/
theorem isIso_lift_resLE
    (hiso : IsIso (pullback.lift φ π' hφ ∣_ (pullback.fst π h ⁻¹ᵁ U))) :
    IsIso (pullback.lift (φ.resLE U U' hUU.ge) (U'.ι ≫ π')
      (resLE_comp_comp π π' h φ hφ U U' hUU).symm) := by
  let f := pullback.lift φ π' hφ
  let ε := pullback.lift (φ.resLE U U' hUU.ge) (U'.ι ≫ π')
    (resLE_comp_comp π π' h φ hφ U U' hUU).symm
  let κ : pullback (U.ι ≫ π) h ⟶ pullback π h :=
    (pullbackRightPullbackFstIso π h U.ι).inv ≫ pullback.snd U.ι (pullback.fst π h)
  have : IsOpenImmersion κ := by
    unfold κ
    infer_instance
  have hrange : Set.range κ = (pullback.fst π h ⁻¹ᵁ U : Set _) := by
    unfold κ
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.2
      (ConcreteCategory.bijective_of_isIso _).2, Set.image_univ, IsOpenImmersion.range_pullbackSnd,
      Scheme.Opens.opensRange_ι]
  let e₀ := IsOpenImmersion.isoOfRangeEq κ (pullback.fst π h ⁻¹ᵁ U).ι
    (by rw [hrange, Scheme.Opens.range_ι])
  have hpre : f ⁻¹ᵁ (pullback.fst π h ⁻¹ᵁ U) = U' := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_fst, hUU]
  have key : ε ≫ e₀.hom = (D'.isoOfEq hpre.symm).hom ≫ (f ∣_ (pullback.fst π h ⁻¹ᵁ U)) := by
    rw [← cancel_mono (pullback.fst π h ⁻¹ᵁ U).ι, Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc, morphismRestrict_ι,
      Scheme.isoOfEq_hom_ι_assoc]
    refine pullback.hom_ext ?_ ?_
    · simp only [κ, Category.assoc, pullback.lift_fst, pullbackRightPullbackFstIso_inv_snd_fst,
        pullback.lift_fst_assoc, f, ε]
      exact Scheme.Hom.resLE_comp_ι _ _
    · simp only [κ, Category.assoc, pullback.lift_snd, pullbackRightPullbackFstIso_inv_snd_snd,
        f, ε]
  have : IsIso (ε ≫ e₀.hom) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right ε e₀.hom

end Generic

end Stacks.Deformation

end
