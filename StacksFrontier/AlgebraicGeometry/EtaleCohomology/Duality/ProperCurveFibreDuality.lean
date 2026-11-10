module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SepClosedPointUnitDetection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurvePoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperLocallyConstantDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.UnitSheafEndomorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactAdjunctionUnboundedSource
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.HomologicalDualityExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RelativeCurveDualityReduction

/-!
# Relative Poincaré duality for a smooth projective curve over an algebraically closed field

Let `k` be algebraically closed, `ℓ` a prime invertible in `k`, `Λ = ℤ/ℓ` and `f : X ⟶ Spec k` a
smooth proper curve. For every `t : Rf_* Λ_X ⟶ Λ[-2]` in `D((Spec k)_ét, Λ)` inducing an
isomorphism on `H²` (a top-degree trace), the trace map `y ↦ t[m] ∘ Rf_*(y)`,
`Hom_X(Λ, Λ[m]) → Hom_{Spec k}(Rf_* Λ, Λ[m - 2])`, is bijective for every integer `m`
(`Stacks.EtaleCohomology.isBijectiveAt_properCurveFibre`). This is the conclusion of
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput` over the base `S = Spec k`.

The proof is `Stacks.RelativeDuality.bijective_traceMap_of_pairing` with `u : Λ ⟶ Rf_* Λ_X` the
unit of `f⁻¹ ⊣ Rf_*`:

* (a) `w ↦ Rf_*(w) ∘ u` is the adjunction `Hom_X(f⁻¹Λ, Λ_X[n]) ≅ Hom(Λ, Rf_* Λ_X[n])` on `D⁺`;
* (b) over the separably closed field `k` every sheaf is projective and injective, and morphisms
  `Rf_* Λ_X ⟶ Λ[c]` are detected by the classes `Λ ⟶ Rf_* Λ_X[-c]`
  (`Stacks.EtaleCohomology.bijective_homCompPairing_unitSheaf_of_isSepClosed`);
* (c) the trace pairing `(y, w) ↦ T(y ∘ w) ∘ u` is Poincaré duality on the curve
  (`Stacks.EtaleCohomology.ExtensionTorsor.isDualityPerfect_unitSheaf`, Tag 095U in degree one),
  read in the transposed variable, for the trace `z ↦ T(z) ∘ u` on `H²(X, Λ)`: it is injective, as
  `#H²(X, Λ) = ℓ` and it does not vanish by (b) and the invertibility of `H²(t)`. Outside degrees
  `0, 1, 2` both sides vanish (Tag 095U, cohomological dimension `2`).

This is the fibre case of relative Poincaré duality for a smooth projective curve, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statement consumes `Rf_*` in the standard model `HasDerivedCategory.standard` of the derived
category, as does `Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`.

## Main results

* `Stacks.EtaleCohomology.bijective_flip_of_isDualityPerfect`.
* `Stacks.EtaleCohomology.bijective_flip_dualityPairing_unitSheaf`.
* `Stacks.EtaleCohomology.bijective_tracePairing_fibre`.
* `Stacks.EtaleCohomology.isBijectiveAt_properCurveFibre_unitSheaf`.
* `Stacks.EtaleCohomology.isBijectiveAt_properCurveFibre`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.EtaleCohomology

open ExtensionTorsor Stacks.RelativeDuality Stacks.HomologicalDuality Stacks.TopTruncationExt

/-- **Transposing a perfect pairing of finite `ℤ/ℓ`-vector spaces**: if `P : V → Hom(W, ℤ/ℓ)` is
bijective and `e : A → ℤ/ℓ` is injective, then `Q : W → Hom(V, A)` with `e (Q w v) = P v w` is
bijective. -/
theorem bijective_flip_of_isDualityPerfect {ℓ : ℕ} [Fact ℓ.Prime] {V W A : Type*} [AddCommGroup V]
    [AddCommGroup W] [AddCommGroup A] [Module (ZMod ℓ) V] [Module (ZMod ℓ) W] [Finite V] [Finite W]
    (e : A →+ ZMod ℓ) (he : Function.Injective e) (P : V →+ (W →+ ZMod ℓ))
    (hP : Function.Bijective P) (Q : W →+ (V →+ A)) (hQ : ∀ v w, e (Q w v) = P v w) :
    Function.Bijective Q := by
  have : Finite (V →+ ZMod ℓ) := Nat.finite_of_card_ne_zero (by
    rw [natCard_addMonoidHom_zmod]; exact Nat.card_pos.ne')
  have hinjA : Function.Injective (fun g : V →+ A => e.comp g) := fun g₁ g₂ hg =>
    AddMonoidHom.ext fun v => he (DFunLike.congr_fun hg v)
  have : Finite (V →+ A) := Finite.of_injective _ hinjA
  have hle : Nat.card (V →+ A) ≤ Nat.card W := by
    calc Nat.card (V →+ A) ≤ Nat.card (V →+ ZMod ℓ) := Nat.card_le_card_of_injective _ hinjA
      _ = Nat.card V := natCard_addMonoidHom_zmod V
      _ = Nat.card (W →+ ZMod ℓ) := Nat.card_congr (Equiv.ofBijective _ hP)
      _ = Nat.card W := natCard_addMonoidHom_zmod W
  refine Function.Injective.bijective_of_nat_card_le ?_ hle
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra hne
  have : Module.Finite (ZMod ℓ) W := Module.Finite.of_finite
  obtain ⟨δ, hδ⟩ : ∃ δ : Module.Dual (ZMod ℓ) W, δ w ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff (ZMod ℓ) w).1 hall)
  obtain ⟨v, hv⟩ := hP.2 δ.toAddMonoidHom
  apply hδ
  have h1 := hQ v w
  rw [hw, AddMonoidHom.zero_apply, map_zero, hv] at h1
  exact h1.symm

/-- **Poincaré duality on a smooth proper curve, transposed**: for an injective trace
`t₀ : H²(X, Λ) → ℤ/ℓ`, an injection `e : A → ℤ/ℓ` and a pairing
`Q : H^i(X, Λ) → Hom(H^j(X, Λ), A)` with `e (Q w v) = t₀ (v ∘ w)`, `i + j = 2`, `Q` is
bijective. -/
theorem bijective_flip_dualityPairing_unitSheaf {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
    (t₀ : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht₀ : Function.Injective t₀)
    {A : Type*} [AddCommGroup A] (e : A →+ ZMod ℓ) (he : Function.Injective e) {i j : ℕ}
    (hji : j + i = 2)
    (Q : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) i →+
      (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) j →+ A))
    (hQ : ∀ v w, e (Q w v) = t₀ (v.comp w hji)) : Function.Bijective Q := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have : ConnectedSpace X := inferInstanceAs (ConnectedSpace X)
  have h2 := natCard_ext_two_unitSheaf f hℓ
  have : Finite (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
  have := finite_ext_one_unitSheaf' f hℓ
  have : Finite (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 0) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr (Ext.homEquiv₀ (X := unitSheaf (X := X) ℓ) (Y := unitSheaf ℓ)),
      natCard_end_unitSheaf (X := X) ℓ]
    exact hp.ne_zero)
  have hfin : ∀ a : ℕ, a ≤ 2 → Finite (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) a) := by
    intro a ha
    obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    all_goals infer_instance
  have := hfin i (by omega)
  have := hfin j (by omega)
  exact bijective_flip_of_isDualityPerfect e he
    (Ext.dualityPairing (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 t₀ (unitSheaf ℓ) hji)
    (isDualityPerfect_unitSheaf f hℓ t₀ ht₀ j i hji) Q hQ

section Fibre

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- `f⁻¹(Λ[0]) ≅ Λ_X[0]` in `D⁺(X)`. -/
def fibreInverseImageUnitIso :
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ) :=
  DerivedCategory.Plus.ι.preimageIso
    (((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) f).app
          (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))))

/-- The adjunction `f⁻¹ ⊣ Rf_*` on `D⁺`. -/
abbrev fibreAdjunction :
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).mapDerivedCategoryPlus ⊣
      etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f :=
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) X
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod ℓ) (Spec (.of k))
  Adjunction.mapDerivedCategoryPlusAdjunction (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) f)

/-- **The unit `Λ ⟶ Rf_* Λ_X`** of the adjunction `f⁻¹ ⊣ Rf_*` on `D⁺`, read in `D(Spec k)`. -/
def fibreUnit : (DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ) ⟶
    (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ)) :=
  ((fibreAdjunction (ℓ := ℓ) f).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) ≫
    (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f).map (fibreInverseImageUnitIso f).hom).hom

omit [IsAlgClosed k] in
/-- **(a) The adjunction**: `w ↦ Rf_*(w) ∘ u`, `Hom_X(Λ, Λ[n]) → Hom(Λ, Rf_* Λ_X[n])`, is
bijective. -/
theorem bijective_unitClassMap_fibreUnit (n : ℤ) :
    Function.Bijective (unitClassMap
      (Φ := etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι)
      (fibreUnit (ℓ := ℓ) f) n) := by
  let adj := fibreAdjunction (ℓ := ℓ) f
  let R := etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f
  let ε := fibreInverseImageUnitIso (ℓ := ℓ) f
  let B' := (DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ)
  let ι := (DerivedCategory.Plus.ι :
    DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))) ⥤ _)
  have hu : fibreUnit (ℓ := ℓ) f = ι.map (adj.unit.app _) ≫ ι.map (R.map ε.hom) := by
    rw [← Functor.map_comp]
    rfl
  have h1 : ⇑(unitClassMap (Φ := R ⋙ DerivedCategory.Plus.ι) (fibreUnit (ℓ := ℓ) f) n) =
      (fun z => z ≫ ((R ⋙ DerivedCategory.Plus.ι).commShiftIso n).hom.app B') ∘
        (fun g => ι.map g) ∘ (adj.homEquiv _ _) ∘ (fun w => ε.hom ≫ w) := by
    funext w
    simp only [unitClassMap, AddMonoidHom.mk'_apply, ShiftedHom.mk₀_comp, ShiftedHom.map,
      Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_map,
      Category.assoc]
    rw [hu]
    exact Category.assoc _ _ _
  rw [h1]
  refine Function.Bijective.comp ⟨fun a b h => (cancel_mono _).1 h,
    fun z => ⟨z ≫ (((R ⋙ DerivedCategory.Plus.ι).commShiftIso n).inv.app B'),
      (Category.assoc _ _ _).trans ((congrArg (z ≫ ·)
        (Iso.inv_hom_id_app ((R ⋙ DerivedCategory.Plus.ι).commShiftIso n) B')).trans
        (Category.comp_id z))⟩⟩
    (Function.Bijective.comp ⟨ι.map_injective, ι.map_surjective⟩
      (Function.Bijective.comp (adj.homEquiv _ _).bijective
        ⟨fun a b h => (cancel_epi ε.hom).1 h, fun w => ⟨ε.inv ≫ w, by simp⟩⟩))

/-- **(b) Detection over `Spec k`**: morphisms `Y ⟶ Λ[c]` of `D(Spec k)` are detected by the
classes `Λ ⟶ Y[-c]`. -/
theorem bijective_compPairing_spec
    (Y : DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))))
    {c n : ℤ} (hn : c + n = 0) :
    Function.Bijective (compPairing ((DerivedCategory.singleFunctor _ 0).obj
      (unitSheaf (X := Spec (.of k)) ℓ)) Y
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) hn) :=
  have := projective_etaleModule_of_isSepClosed k ℓ (unitSheaf (X := Spec (.of k)) ℓ)
  have := injective_etaleModule_of_isSepClosed k ℓ (unitSheaf (X := Spec (.of k)) ℓ)
  bijective_shiftedHom_comp_of_projective_of_injective _ _
    (bijective_homCompPairing_unitSheaf_of_isSepClosed k ℓ) Y hn

/-- A degree-free form of the trace pairing. -/
lemma _root_.Stacks.RelativeDuality.tracePairing_apply_of_eq {C C' : Type*} [Category* C]
    [Category* C'] [Preadditive C] [Preadditive C'] [HasShift C ℤ] [HasShift C' ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive]
    {Φ : C ⥤ C'} [Φ.CommShift ℤ] [Φ.Additive] {B : C} {L : C'} {c₀ : ℤ}
    (t : ShiftedHom (Φ.obj B) L c₀) {E : C'} (u : E ⟶ Φ.obj B) {m n : ℤ} (h : c₀ + (m + n) = 0)
    (y : ShiftedHom B B m) (w : ShiftedHom B B n) {p : ℤ} (hp : m + n = p) (h' : c₀ + p = 0) :
    tracePairing t u h y w =
      (ShiftedHom.mk₀ (0 : ℤ) rfl u).comp (traceMap Φ t B p 0 h' (w.comp y hp)) (add_zero 0) := by
  subst hp
  rfl

/-- An additive map out of a group of prime order is injective as soon as it is nonzero. -/
lemma injective_of_ne_zero_of_natCard_prime {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (hG : (Nat.card G).Prime) (φ : G →+ H) (hφ : φ ≠ 0) : Function.Injective φ := by
  have : Fact (Nat.card G).Prime := ⟨hG⟩
  rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card φ.ker with h | h
  · exact (AddMonoidHom.ker_eq_bot_iff φ).1 h
  · exact absurd (AddMonoidHom.ext fun x => (AddMonoidHom.mem_ker).1 (h ▸ AddSubgroup.mem_top x)) hφ

variable (k ℓ) in
/-- The endomorphisms of `Λ[0]` in `D(Spec k)`, read in `ℤ/ℓ` at the point. -/
def specEndScalar : ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj
      (unitSheaf (X := Spec (.of k)) ℓ)) ((DerivedCategory.singleFunctor _ 0).obj
        (unitSheaf (X := Spec (.of k)) ℓ)) (0 : ℤ) →+ ZMod ℓ :=
  haveI : Nonempty (Spec (.of k)) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  let F := DerivedCategory.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))) 0
  let L := F.obj (unitSheaf (X := Spec (.of k)) ℓ)
  AddMonoidHom.mk' (fun z => (KummerFlag.unitSheafEndEquiv ℓ
      (F.preimage (z ≫ (shiftFunctorZero _ ℤ).hom.app L)) (Classical.arbitrary _)).down)
    (fun z₁ z₂ => by
      have : F.preimage ((z₁ + z₂) ≫ (shiftFunctorZero _ ℤ).hom.app L) =
          F.preimage (z₁ ≫ (shiftFunctorZero _ ℤ).hom.app L) +
            F.preimage (z₂ ≫ (shiftFunctorZero _ ℤ).hom.app L) :=
        F.map_injective (by simp [Preadditive.add_comp])
      rw [this, KummerFlag.unitSheafEndEquiv_add]
      rfl)

omit [IsAlgClosed k] in
/-- The constant sheaf `ℤ/ℓ` on `(Spec k)_ét` is not a zero object. -/
theorem not_isZero_unitSheaf_spec : ¬ IsZero (unitSheaf (X := Spec (.of k)) ℓ) := by
  have hp : ℓ.Prime := Fact.out
  intro hz
  have : Subsingleton (unitSheaf (X := Spec (.of k)) ℓ ⟶ unitSheaf ℓ) :=
    ⟨fun a b => hz.eq_of_src a b⟩
  have h := natCard_end_unitSheaf (X := Spec (.of k)) ℓ
  rw [Nat.card_unique] at h
  exact hp.one_lt.ne h

omit [IsAlgClosed k] in
/-- `specEndScalar k ℓ` is injective. -/
theorem specEndScalar_injective : Function.Injective (specEndScalar k ℓ) := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  intro z₁ z₂ hz
  let F := DerivedCategory.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))) 0
  have h1 := (KummerFlag.unitSheafEndEquiv ℓ).injective (LocallyConstant.ext fun x =>
    ULift.ext ((congrArg (fun y => (KummerFlag.unitSheafEndEquiv ℓ _ y).down)
      (Subsingleton.elim x _)).trans (hz.trans (congrArg (fun y =>
        (KummerFlag.unitSheafEndEquiv ℓ _ y).down) (Subsingleton.elim _ x)))))
  have h2 := congrArg F.map h1
  rw [Functor.map_preimage, Functor.map_preimage] at h2
  exact (cancel_mono _).1 h2

section Curve

variable [IsCurve k f] [Smooth f] [IsProper f]

omit [Smooth f] in
include f in
/-- `H^q(X, Λ) = 0` for `q > 2` on the curve. -/
theorem subsingleton_shiftedHom_unitSheaf_of_two_lt (q : ℕ) (hq : 2 < q) :
    Subsingleton (ShiftedHom ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ))
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ)) (q : ℤ)) := by
  have := subsingleton_ext_unitSheaf_of_proper (ℓ := ℓ) f 1
    (by exact_mod_cast (IsCurve.topologicalKrullDim_eq_one (f := f)).le) (unitSheaf (X := X) ℓ) q
    (by omega)
  exact (extPlus_surjective (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) q).subsingleton

/-- The trace pairing in degrees `(i, j)`, `i + j = 2`, for a trace `t₀` on `H²(X, Λ)` read
through `T` and the unit. -/
theorem bijective_tracePairing_fibre_of_nat (hℓ : IsUnit (ℓ : k))
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ)))
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) (-2))
    (t₀ : Ext (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) 2 →+ ZMod ℓ)
    (ht₀ : Function.Injective t₀)
    (hτ : ∀ z, t₀ z = specEndScalar k ℓ ((ShiftedHom.mk₀ (0 : ℤ) rfl (fibreUnit (ℓ := ℓ) f)).comp
      (traceMap (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι) t
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ)) ((2 : ℕ) : ℤ) 0
          (by norm_num) (extPlus z)) (add_zero 0)))
    (i j : ℕ) (h : -2 + ((i : ℤ) + (j : ℤ)) = 0) :
    Function.Bijective (tracePairing t (fibreUnit (ℓ := ℓ) f) h) := by
  have hji : j + i = 2 := by omega
  let Q := ((tracePairing t (fibreUnit (ℓ := ℓ) f) h).comp
    (extPlusHom (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) i)).compl₂
      (extPlusHom (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) j)
  have hQ : Function.Bijective Q :=
    bijective_flip_dualityPairing_unitSheaf f hℓ t₀ ht₀ (specEndScalar k ℓ)
      specEndScalar_injective hji Q (fun v w => by
        rw [hτ]
        change specEndScalar k ℓ
          (tracePairing t (fibreUnit (ℓ := ℓ) f) h (extPlus w) (extPlus v)) = _
        congr 1
        rw [tracePairing_apply_of_eq t (fibreUnit (ℓ := ℓ) f) h (extPlus w) (extPlus v)
          (p := ((2 : ℕ) : ℤ)) (by omega) (by norm_num), extPlus_comp v w hji])
  refine (bijective_iff_of_comp _ _ extPlus (extPlus_bijective _ _ i) (extPlusHom _ _ j)
    (extPlus_bijective _ _ j) (fun x y => ?_)).1 hQ
  simp only [Q, AddMonoidHom.compl₂_apply, AddMonoidHom.comp_apply]
  rfl

/-- **(c) The trace pairing is perfect**: for a top-degree trace `t`, the pairing
`(y, w) ↦ T(y ∘ w) ∘ u` identifies `H^m(X, Λ)` with the dual of `H^{2-m}(X, Λ)`, in every
degree. -/
theorem bijective_tracePairing_fibre (hℓ : IsUnit (ℓ : k))
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ)))
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) {m n : ℤ} (h : -2 + (m + n) = 0) :
    Function.Bijective (tracePairing t (fibreUnit (ℓ := ℓ) f) h) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  let Λ := unitSheaf (X := X) ℓ
  let B' := (DerivedCategory.Plus.singleFunctor _ 0).obj Λ
  let Φ := etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι
  let u := fibreUnit (ℓ := ℓ) f
  let L := (DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)
  -- the trace on `H²(X, Λ)`
  let τ : Ext Λ Λ 2 →+ ShiftedHom L L (0 : ℤ) := AddMonoidHom.mk'
    (fun z => (ShiftedHom.mk₀ (0 : ℤ) rfl u).comp
      (traceMap Φ t B' ((2 : ℕ) : ℤ) 0 (by norm_num) (extPlus z)) (add_zero 0))
    (fun z₁ z₂ => by rw [extPlus_add, map_add, ShiftedHom.comp_add])
  let t₀ : Ext Λ Λ 2 →+ ZMod ℓ := (specEndScalar k ℓ).comp τ
  have h2 : Nat.card (Ext Λ Λ 2) = ℓ := natCard_ext_two_unitSheaf f hℓ
  have ht₀ : Function.Injective t₀ := by
    refine injective_of_ne_zero_of_natCard_prime (by rw [h2]; exact hp) t₀ fun h0 => ?_
    -- then `t = 0`, by detection over `Spec k`
    have hb := bijective_compPairing_spec (k := k) (ℓ := ℓ) (Φ.obj B') (c := -2) (n := 2)
      (by norm_num)
    have htz : t = 0 := by
      apply hb.1
      rw [map_zero]
      refine AddMonoidHom.ext fun x => ?_
      obtain ⟨w, rfl⟩ := (bijective_unitClassMap_fibreUnit (ℓ := ℓ) f 2).2 x
      obtain ⟨z, rfl⟩ := extPlus_surjective Λ Λ 2 w
      have hz : t₀ z = 0 := by simpa using DFunLike.congr_fun h0 z
      apply specEndScalar_injective
      rw [AddMonoidHom.zero_apply, map_zero]
      refine Eq.trans ?_ hz
      change specEndScalar k ℓ (((ShiftedHom.mk₀ (0 : ℤ) rfl u).comp ((extPlus z).map Φ)
        (add_zero _)).comp t _) = specEndScalar k ℓ ((ShiftedHom.mk₀ (0 : ℤ) rfl u).comp
          (((extPlus z).map Φ).comp t _) (add_zero 0))
      rw [ShiftedHom.comp_assoc _ _ _ (add_zero _) _ (by norm_num)]
    apply (not_isZero_unitSheaf_spec (k := k) (ℓ := ℓ))
    rw [htz, Functor.map_zero] at ht
    have hz : IsZero ((DerivedCategory.homologyFunctor _ 2).obj (L⟦(-2 : ℤ)⟧)) := by
      rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id
        (0 : (DerivedCategory.homologyFunctor _ 2).obj (Φ.obj B') ⟶ _), comp_zero]
    exact hz.of_iso
      ((singleShiftHomologyIso (B := EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))) 2).app
        (unitSheaf (X := Spec (.of k)) ℓ)).symm
  have hsub : ∀ a : ℤ, a < 0 ∨ 2 < a → Subsingleton (ShiftedHom B' B' a) := by
    rintro a (ha | ha)
    · exact subsingleton_hom_single_shift_of_neg Λ Λ ha
    · lift a to ℕ using by omega
      exact subsingleton_shiftedHom_unitSheaf_of_two_lt (ℓ := ℓ) f a (by omega)
  by_cases hv : m < 0 ∨ 2 < m
  · -- `m < 0` or `m > 2`: both sides vanish
    have := hsub m hv
    have := hsub n (by omega)
    exact bijective_of_subsingleton (X := ShiftedHom B' B' m) _ 0
  lift m to ℕ using by omega
  lift n to ℕ using by omega
  exact bijective_tracePairing_fibre_of_nat f hℓ t t₀ ht₀ (fun z => rfl) m n h

/-- **Relative Poincaré duality for a smooth proper curve over an algebraically closed field**,
at `Λ_X`: for a top-degree trace `t : Rf_* Λ_X ⟶ Λ[-2]`, `y ↦ t[m] ∘ Rf_*(y)` is bijective
`Hom_X(Λ_X, Λ_X[m]) → Hom(Rf_* Λ_X, Λ[m - 2])` for every integer `m`. -/
theorem isBijectiveAt_properCurveFibre_unitSheaf (hℓ : IsUnit (ℓ : k))
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ)))
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι) t
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ)) := fun m c h =>
  bijective_traceMap_of_pairing (fibreUnit (ℓ := ℓ) f) h (n := -c) (by omega)
    (bijective_unitClassMap_fibreUnit f (-c)) (bijective_compPairing_spec _ _)
    (bijective_tracePairing_fibre f hℓ t ht _)

/-- **Relative Poincaré duality for a smooth proper curve over an algebraically closed field**:
the conclusion of `Stacks.EtaleCohomology.ProperCurveRelativeDualityInput` over `S = Spec k`. For
`f : X ⟶ Spec k` a smooth proper curve, `ℓ` invertible in `k` and every
`t : Rf_*(f⁻¹ Λ) ⟶ Λ[-2]` inducing an isomorphism on `H²`, the map
`y ↦ t[m] ∘ Rf_*(y)`, `Hom_X(f⁻¹Λ, f⁻¹Λ[m]) → Hom(Rf_*(f⁻¹ Λ), Λ[m - 2])`, is bijective for every
integer `m`. -/
theorem isBijectiveAt_properCurveFibre (hℓ : IsUnit (ℓ : k))
    (t : ShiftedHom ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := Spec (.of k)) ℓ))))
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    IsBijectiveAt (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι) t
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := Spec (.of k)) ℓ))) := by
  let Φ := etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.ι
  let ε : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := Spec (.of k)) ℓ)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := X) ℓ) :=
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) f).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))
  let t' := (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map ε.inv)).comp t (add_zero _)
  have ht' : IsIso ((DerivedCategory.homologyFunctor _ 2).map t') := by
    simp only [t', ShiftedHom.mk₀_comp, CategoryTheory.Functor.map_comp]
    infer_instance
  have htt : t = (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map ε.hom)).comp t' (add_zero _) := by
    rw [← ShiftedHom.comp_assoc _ _ _ (add_zero _) (add_zero _) (by simp), ShiftedHom.mk₀_comp_mk₀,
      ← Φ.map_comp, ε.hom_inv_id, Φ.map_id, ShiftedHom.mk₀_id_comp]
  have H := isBijectiveAt_properCurveFibre_unitSheaf f hℓ t' ht'
  intro m c h
  rw [htt, bijective_traceMap_mk₀_map_comp_iff ε t']
  exact bijective_traceMap_of_iso ε.symm h (H m c h)

end Curve

end Fibre

end Stacks.EtaleCohomology

end
