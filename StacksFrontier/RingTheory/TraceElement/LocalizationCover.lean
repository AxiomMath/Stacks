module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElementUnique
public import StacksFrontier.RingTheory.TraceElement.TargetLocalization

/-!
# Gluing trace elements over a principal open cover

Let `A → B` be a flat quasi-finite map of Noetherian rings and `g₁, …, gₙ` elements of `B`
generating the unit ideal, so that the basic opens `D(gᵢ)` cover `Spec B`. An element of the
relative dualizing module `ω_{B/A}` which is a trace element on every `B_{gᵢ}` is a trace
element.

The proof tests the trace-element condition against a decomposition `A₁ ⊗_A B ≃ C × D` with `C`
finite over `A₁` and compares two functionals on `C`. Two reductions make the comparison local.
First, a functional with values in a Noetherian ring is determined by its images in the Artinian
quotients of that ring, by the Krull intersection theorem; so it suffices to treat an Artinian
base `A₂`. Second, over an Artinian base the localization `C → C_{γ(gᵢ)}` is surjective, hence
split, and the restriction of the dualizing element to a split quotient is computed by the same
trace. Since the images `γ(gᵢ)` again generate the unit ideal of `C`, the two functionals agree
after localization at each of them, therefore agree.

## Main definitions

* `Stacks.Discriminant.localizationDualizingMap` is the localization map on relative dualizing
  modules at the factorization `Stacks.Discriminant.locFact`.
* `Stacks.Discriminant.baseChangeProdEquiv` transports a product decomposition of a scalar
  extension along a further extension of the base.
* `Stacks.Discriminant.baseChangeLocalizationProdEquiv` transports a product decomposition of a
  scalar extension to an away localization of the target.

## Main results

* `Stacks.Discriminant.isTraceElement_of_localization_cover`: Tag 0BTA, a section of the
  relative dualizing module which is a trace element on each member of a finite principal open
  cover of the target is a trace element.
* `Stacks.Discriminant.eq_of_forall_isArtinianRing_quotient_eq`: an element of a Noetherian
  ring is determined by its images in the Artinian quotients.
* `Stacks.Discriminant.finiteProjectiveTrace_eq_of_split`: the projective trace may be computed
  on any finite projective module that the given module splits off.
* `Stacks.Discriminant.eq_of_localized_dualizingModule_eq`: a section of the relative dualizing
  module is determined by its localizations over a principal cover of the target.
* `Stacks.Discriminant.eq_of_isTraceElement_localization`: a section which is locally a trace
  element agrees with any global trace element.
* `Stacks.Discriminant.finiteFactorRestriction_eq_of_artinian_cover`: over an Artinian factor
  the restriction of a dualizing element glued from local trace elements is the trace.

## Implementation notes

The intermediate algebra of a factorization is reachable by two spellings after base change or
localization: `(FiniteOpenFactorization.baseChange F A₁).middle` and `A₁ ⊗[A] F.middle`, or
`(locFact g F).middle` and `F.middle`. These are definitionally equal, but neither `baseChange`
nor `locFact` unfolds at reducible transparency, so instance search distinguishes them while
`exact`, `refine` and `congrArg` identify them. Instances are therefore declared at each
spelling they are searched at, and a step whose statement mentions the other spelling is written
as a fully applied `have` and chained with `Eq.trans` rather than rewritten into place.

## References

* [Stacks Project, Tag 0BTA](https://stacks.math.columbia.edu/tag/0BTA)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
-/

@[expose] public section

open scoped TensorProduct

universe u v w z s t r

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-! ### Separation by Artinian quotients -/

/-- A power of a maximal ideal of a Noetherian ring has Artinian quotient: the quotient has
Krull dimension zero, since its only minimal prime is the maximal ideal itself. -/
theorem isArtinianRing_quotient_pow_of_isMaximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    (m : Ideal R) [m.IsMaximal] (n : ℕ) : IsArtinianRing (R ⧸ m ^ n) := by
  apply isArtinianRing_iff_krullDimLE_zero.mpr
  rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
  intro p hp
  have hle : m ≤ p := fun x hx => hp.1.1.mem_of_pow_mem n (hp.1.2 (Ideal.pow_mem_pow hx n))
  obtain rfl := Ideal.IsMaximal.eq_of_le (inferInstance : m.IsMaximal) hp.1.1.ne_top hle
  infer_instance

/-- An element of a Noetherian ring is determined by its images in the Artinian quotients. If
two elements differ, the annihilator of their difference is contained in a maximal ideal `m`,
and the difference lies in every power of `m`; the Krull intersection theorem then produces a
unit of the form `1 - a` with `a ∈ m` annihilating it, which is absurd. -/
theorem eq_of_forall_isArtinianRing_quotient_eq {R : Type*} [CommRing R] [IsNoetherianRing R]
    (x y : R) (h : ∀ I : Ideal R, IsArtinianRing (R ⧸ I) →
      Ideal.Quotient.mk I x = Ideal.Quotient.mk I y) : x = y := by
  by_contra hne
  set z := x - y
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  set J : Ideal R := (Algebra.lmul R R z).ker with hJdef
  have hJ : J ≠ ⊤ := by
    intro heq
    have h1 : (1 : R) ∈ J := heq.symm ▸ Submodule.mem_top
    exact hz (by simpa [hJdef] using h1)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  have hall : z ∈ ⨅ n : ℕ, m ^ n • (⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro n
    have hz' : z ∈ m ^ n :=
      Ideal.Quotient.eq.mp (h (m ^ n) (isArtinianRing_quotient_pow_of_isMaximal m n))
    simpa only [smul_eq_mul, mul_one] using
      Submodule.smul_mem_smul hz' (show (1 : R) ∈ (⊤ : Submodule R R) from Submodule.mem_top)
  obtain ⟨a, ha⟩ := (m.mem_iInf_smul_pow_eq_bot_iff z).mp hall
  have hsub : 1 - (a : R) ∈ J := by
    show z * (1 - (a : R)) = 0
    change (a : R) * z = z at ha
    rw [mul_sub, mul_one, mul_comm z, ha, sub_self]
  have h1 : (1 : R) ∈ m := by simpa using m.add_mem (hJm hsub) a.2
  exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr h1)

/-! ### Computation rules for the projective trace -/

/-- The projective trace may be computed on any finite projective module that the given module
splits off, not only on a finite free one. -/
theorem finiteProjectiveTrace_eq_of_split {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    {Q : Type w} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
    (p : Q →ₗ[R] P) (i : P →ₗ[R] Q) (hpi : p.comp i = LinearMap.id) (f : Module.End R P) :
    finiteProjectiveTrace R P f = finiteProjectiveTrace R Q (i.comp (f.comp p)) := by
  obtain ⟨n, p₀, i₀, _, _, h₀⟩ := Module.Finite.exists_comp_eq_id_of_projective R Q
  have hi : (p.comp p₀).comp (i₀.comp i) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    show p ((p₀.comp i₀) (i x)) = x
    rw [h₀]
    exact LinearMap.congr_fun hpi x
  rw [finiteProjectiveTrace_eq_trace_of_split R P (Fin n → R) (p.comp p₀) (i₀.comp i) hi,
    finiteProjectiveTrace_eq_trace_of_split R Q (Fin n → R) p₀ i₀ h₀]
  simp only [LinearMap.comp_assoc]

/-- The trace of multiplication by an element of an intermediate algebra `C`, computed on a
scalar extension `T` of `C` along `R → S`, is the image of the trace over `C`. -/
theorem finiteProjectiveTrace_lmul_baseChange
    {R : Type*} {S : Type*} {C : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing C] [CommRing T]
    [Algebra R S] [Algebra R C] [Algebra R T] [Algebra S T] [Algebra C T]
    [IsScalarTower R S T] [IsScalarTower R C T]
    [Module.Finite R C] [Module.Projective R C]
    [Module.Finite S T] [Module.Projective S T]
    (h : IsBaseChange S ((Algebra.linearMap C T).restrictScalars R)) (c : C) :
    finiteProjectiveTrace S T (Algebra.lmul S T (algebraMap C T c)) =
      algebraMap R S (finiteProjectiveTrace R C (Algebra.lmul R C c)) := by
  set e := h.equiv with hedef
  have hval (a : S) (b : C) : e (a ⊗ₜ[R] b) = algebraMap S T a * algebraMap C T b := by
    rw [hedef, IsBaseChange.equiv_tmul]
    simp only [LinearMap.restrictScalars_apply, Algebra.linearMap_apply, Algebra.smul_def]
  have hconj : Algebra.lmul S T (algebraMap C T c) =
      e.toLinearMap.comp (((Algebra.lmul R C c).baseChange S).comp e.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    have key (y : S ⊗[R] C) :
        algebraMap C T c * e y = e ((Algebra.lmul R C c).baseChange S y) := by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
      | tmul a b =>
          rw [LinearMap.baseChange_tmul, hval, hval]
          show algebraMap C T c * (algebraMap S T a * algebraMap C T b) =
            algebraMap S T a * algebraMap C T (c * b)
          rw [map_mul]
          exact mul_left_comm _ _ _
    show algebraMap C T c * x = e ((Algebra.lmul R C c).baseChange S (e.symm x))
    have hx := key (e.symm x)
    rwa [e.apply_symm_apply] at hx
  rw [hconj, finiteProjectiveTrace_conj S (S ⊗[R] C) T e, finiteProjectiveTrace_baseChange]

/-- For a split extension `C → E` of algebras over `R`, the trace of multiplication by `x ∈ E`
is the trace of multiplication by the retraction of `x`. -/
theorem finiteProjectiveTrace_lmul_of_retract
    {R : Type u} {C : Type v} {E : Type w}
    [CommRing R] [CommRing C] [CommRing E]
    [Algebra R C] [Algebra R E] [Algebra C E] [IsScalarTower R C E]
    [Module.Finite R C] [Module.Projective R C]
    [Module.Finite R E] [Module.Projective R E]
    (i : E →ₗ[C] C) (hi : (Algebra.linearMap C E).comp i = LinearMap.id) (x : E) :
    finiteProjectiveTrace R E (Algebra.lmul R E x) =
      finiteProjectiveTrace R C (Algebra.lmul R C (i x)) := by
  rw [finiteProjectiveTrace_eq_of_split
    ((Algebra.linearMap C E).restrictScalars R) (i.restrictScalars R)
    (by ext y; exact LinearMap.congr_fun hi y)]
  apply congrArg (finiteProjectiveTrace R C)
  apply LinearMap.ext
  intro c
  show i (x * algebraMap C E c) = i x * c
  rw [mul_comm x, ← Algebra.smul_def, i.map_smul, smul_eq_mul, mul_comm]

/-! ### Scalar towers through a universe shrinking -/

/-- A scalar tower descends to a universe-shrunk copy of its top ring. -/
theorem isScalarTower_shrink {R S T : Type*} [SMul R S] [SMul R T] [SMul S T]
    [IsScalarTower R S T] [Small.{z} T] : IsScalarTower R S (Shrink.{z} T) := by
  constructor
  intro r s t
  apply (equivShrink T).symm.injective
  simp only [equivShrink_symm_smul, smul_assoc]

/-- A universe-shrunk copy of a ring is a scalar tower over itself. -/
theorem isScalarTower_shrink_self {R T : Type*} [CommRing T] [SMul R T] [IsScalarTower R T T]
    [Small.{z} T] : IsScalarTower R (Shrink.{z} T) (Shrink.{z} T) := by
  constructor
  intro r x y
  apply (equivShrink T).symm.injective
  simp only [smul_eq_mul, equivShrink_symm_mul, equivShrink_symm_smul, smul_mul_assoc]

/-! ### Localizing a product decomposition -/

/-- The product of the away localizations of the two factors of a product ring is the away
localization of the product at the pair. -/
theorem isLocalization_away_prod {C : Type*} {D : Type*} [CommRing C] [CommRing D]
    (c : C) (d : D) :
    letI : Algebra (C × D) (Localization.Away c × Localization.Away d) :=
      ((algebraMap C (Localization.Away c)).prodMap
        (algebraMap D (Localization.Away d))).toAlgebra
    IsLocalization.Away (c, d) (Localization.Away c × Localization.Away d) := by
  let : Algebra (C × D) (Localization.Away c × Localization.Away d) :=
    ((algebraMap C (Localization.Away c)).prodMap
      (algebraMap D (Localization.Away d))).toAlgebra
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨_, n, rfl⟩
    exact Prod.isUnit_iff.mpr
      ⟨IsLocalization.map_units (M := Submonoid.powers c) (Localization.Away c)
        ⟨c ^ n, ⟨n, rfl⟩⟩,
       IsLocalization.map_units (M := Submonoid.powers d) (Localization.Away d)
        ⟨d ^ n, ⟨n, rfl⟩⟩⟩
  · rintro ⟨x, y⟩
    obtain ⟨⟨a, _, k, rfl⟩, hx⟩ := IsLocalization.surj (Submonoid.powers c) x
    obtain ⟨⟨b, _, l, rfl⟩, hy⟩ := IsLocalization.surj (Submonoid.powers d) y
    refine ⟨⟨(a * c ^ l, b * d ^ k), ⟨(c, d) ^ (k + l), ⟨k + l, rfl⟩⟩⟩, ?_⟩
    apply Prod.ext
    · show x * algebraMap C _ (c ^ (k + l)) = algebraMap C _ (a * c ^ l)
      rw [pow_add, map_mul, map_mul, ← mul_assoc, hx]
    · show y * algebraMap D _ (d ^ (k + l)) = algebraMap D _ (b * d ^ k)
      rw [Nat.add_comm k l, pow_add, map_mul, map_mul, ← mul_assoc, hy]
  · intro x y h
    obtain ⟨⟨_, k, rfl⟩, hx⟩ :=
      IsLocalization.exists_of_eq (M := Submonoid.powers c) (congrArg Prod.fst h)
    obtain ⟨⟨_, l, rfl⟩, hy⟩ :=
      IsLocalization.exists_of_eq (M := Submonoid.powers d) (congrArg Prod.snd h)
    change c ^ k * x.1 = c ^ k * y.1 at hx
    change d ^ l * x.2 = d ^ l * y.2 at hy
    refine ⟨⟨(c, d) ^ (k + l), ⟨k + l, rfl⟩⟩, ?_⟩
    apply Prod.ext
    · show c ^ (k + l) * x.1 = c ^ (k + l) * y.1
      rw [Nat.add_comm k l, pow_add, mul_assoc, mul_assoc, hx]
    · show d ^ (k + l) * x.2 = d ^ (k + l) * y.2
      rw [pow_add, mul_assoc, mul_assoc, hy]

/-- A product decomposition `A₁ ⊗_A B ≃ C × D` localizes: `A₁ ⊗_A B_g` decomposes as the product
of the away localizations of `C` and `D` at the two components of the image of `1 ⊗ g`. -/
noncomputable def baseChangeLocalizationProdEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (g : B) (A₁ : Type s) [CommRing A₁] [Algebra A A₁]
    {C : Type t} {D : Type r} [CommRing C] [CommRing D] [Algebra A₁ C] [Algebra A₁ D]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D) :
    (A₁ ⊗[A] Localization.Away g) ≃ₐ[A₁]
      Localization.Away (e ((1 : A₁) ⊗ₜ[A] g)).1 ×
      Localization.Away (e ((1 : A₁) ⊗ₜ[A] g)).2 := by
  let c := (e ((1 : A₁) ⊗ₜ[A] g)).1
  let d := (e ((1 : A₁) ⊗ₜ[A] g)).2
  letI : Algebra (C × D) (Localization.Away c × Localization.Away d) :=
    ((algebraMap C (Localization.Away c)).prodMap
      (algebraMap D (Localization.Away d))).toAlgebra
  letI := isLocalization_away_prod c d
  letI : IsScalarTower A₁ (C × D) (Localization.Away c × Localization.Away d) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (IsLocalization.Away.tensorProductEquivTMulRight (R := A) (S := A₁) g _).trans
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers ((1 : A₁) ⊗ₜ[A] g))
      (T := Submonoid.powers (c, d))
      (Localization.Away ((1 : A₁) ⊗ₜ[A] g))
      (Localization.Away c × Localization.Away d) e (by simp [Submonoid.map_powers, c, d]))

/-- The localized product decomposition on the image of a pure tensor. -/
theorem baseChangeLocalizationProdEquiv_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (g : B) (A₁ : Type s) [CommRing A₁] [Algebra A A₁]
    {C : Type t} {D : Type r} [CommRing C] [CommRing D] [Algebra A₁ C] [Algebra A₁ D]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D) (a : A₁) (b : B) :
    baseChangeLocalizationProdEquiv g A₁ e (a ⊗ₜ[A] algebraMap B _ b) =
      (algebraMap C _ (e (a ⊗ₜ[A] b)).1, algebraMap D _ (e (a ⊗ₜ[A] b)).2) := by
  let c := (e ((1 : A₁) ⊗ₜ[A] g)).1
  let d := (e ((1 : A₁) ⊗ₜ[A] g)).2
  let : Algebra (C × D) (Localization.Away c × Localization.Away d) :=
    ((algebraMap C (Localization.Away c)).prodMap
      (algebraMap D (Localization.Away d))).toAlgebra
  have := isLocalization_away_prod c d
  have : IsScalarTower A₁ (C × D) (Localization.Away c × Localization.Away d) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold baseChangeLocalizationProdEquiv
  rw [AlgEquiv.trans_apply, IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq]
  rfl

/-! ### Extending the base of a product decomposition -/

/-- A product decomposition of `A₁ ⊗_A B` over `A₁` extends along `A₁ → A₂` to a product
decomposition of `A₂ ⊗_A B` over `A₂`. -/
noncomputable def baseChangeProdEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (A₁ : Type s) (A₂ : Type*) [CommRing A₁] [CommRing A₂]
    [Algebra A A₁] [Algebra A A₂] [Algebra A₁ A₂] [IsScalarTower A A₁ A₂]
    {C : Type t} {D : Type r} [CommRing C] [CommRing D] [Algebra A₁ C] [Algebra A₁ D]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D) :
    (A₂ ⊗[A] B) ≃ₐ[A₂] (A₂ ⊗[A₁] C) × (A₂ ⊗[A₁] D) :=
  (Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : A₂ ≃ₐ[A₂] A₂) e).trans
      (Algebra.TensorProduct.prodRight A₁ A₂ A₂ C D))

/-- The extended product decomposition on a pure tensor. -/
theorem baseChangeProdEquiv_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (A₁ : Type s) (A₂ : Type*) [CommRing A₁] [CommRing A₂]
    [Algebra A A₁] [Algebra A A₂] [Algebra A₁ A₂] [IsScalarTower A A₁ A₂]
    {C : Type t} {D : Type r} [CommRing C] [CommRing D] [Algebra A₁ C] [Algebra A₁ D]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D) (a : A₂) (b : B) :
    baseChangeProdEquiv A₁ A₂ e (a ⊗ₜ[A] b) =
      (a ⊗ₜ[A₁] (e ((1 : A₁) ⊗ₜ[A] b)).1, a ⊗ₜ[A₁] (e ((1 : A₁) ⊗ₜ[A] b)).2) := by
  simp only [baseChangeProdEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.prodRight_tmul]
  rfl

/-- The extended product decomposition on the image of `A₁ ⊗_A B`. -/
theorem baseChangeProdEquiv_map
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (A₁ : Type s) (A₂ : Type*) [CommRing A₁] [CommRing A₂]
    [Algebra A A₁] [Algebra A A₂] [Algebra A₁ A₂] [IsScalarTower A A₁ A₂]
    {C : Type t} {D : Type r} [CommRing C] [CommRing D] [Algebra A₁ C] [Algebra A₁ D]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D) (x : A₁ ⊗[A] B) :
    baseChangeProdEquiv A₁ A₂ e
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A₁ A₂) (AlgHom.id A B) x) =
      ((1 : A₂) ⊗ₜ[A₁] (e x).1, (1 : A₂) ⊗ₜ[A₁] (e x).2) := by
  have hmap : Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A₁ A₂) (AlgHom.id A B) x =
      Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B ((1 : A₂) ⊗ₜ[A₁] x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
    | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, IsScalarTower.toAlgHom_apply,
          AlgHom.id_apply, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def,
          mul_one]
  rw [hmap]
  simp only [baseChangeProdEquiv, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.prodRight_tmul]
  rfl

/-! ### Localizing the relative dualizing module -/

/-- The localization map on relative dualizing modules: the image of a section of `ω_{B/A}` in
`ω_{B_g/A}`, through the identification of [Stacks, Tag 0BT2 (2)] taken at the factorization
`Stacks.Discriminant.locFact`, which keeps the intermediate algebra unchanged. -/
noncomputable def localizationDualizingMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (g : B) :
    dualizingModule F →+ dualizingModule (locFact (Bg := Localization.Away g) g F) :=
  (localizedModule_dualizingModule_equiv g F (locFact g F)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) (dualizingModule F))
        inferInstance).toLinearMap.toAddMonoidHom.comp
    (LocalizedModule.mkLinearMap (Submonoid.powers g) (dualizingModule F)).toAddMonoidHom

/-- The localization map on relative dualizing modules is the identification of
[Stacks, Tag 0BT2 (2)] applied to the canonical localization of the module. -/
theorem localizationDualizingMap_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (g : B) (τ : dualizingModule F) :
    localizationDualizingMap F g τ =
      localizedModule_dualizingModule_equiv g F (locFact g F)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) (dualizingModule F)) inferInstance
        (LocalizedModule.mkLinearMap (Submonoid.powers g) (dualizingModule F) τ) := rfl

/-- The localization map on relative dualizing modules localizes the target coefficient of a
pure tensor and leaves the dual factor unchanged, the intermediate algebra being the same. -/
theorem localizationDualizingMap_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (g : B)
    (f : Module.Dual A F.middle) (b : B) :
    localizationDualizingMap F g (dualizingModule.tmul F f b) =
      dualizingModule.tmul (locFact (Bg := Localization.Away g) g F) f
        (algebraMap B (Localization.Away g) b) :=
  localizedModule_dualizingModule_equiv_tmul g F (locFact g F)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) (dualizingModule F)) inferInstance
    (AlgEquiv.refl : (locFact (Bg := Localization.Away g) g F).middle ≃ₐ[A] F.middle)
    (fun _ => rfl) f b

/-- Two functionals on a ring `C` that agree on the image of a retraction of an away
localization `C_g` have the same image in the localization of the dual at `g`. -/
theorem localized_dual_eq_of_retraction
    {R : Type*} {C : Type*} {Cg : Type*} [CommRing R] [CommRing C] [CommRing Cg]
    [Algebra R C] [Algebra C Cg] (g : C) [IsLocalization.Away g Cg]
    (i : Cg →ₗ[C] C) (hi : (Algebra.linearMap C Cg).comp i = LinearMap.id)
    (f h : Module.Dual R C) (heq : ∀ x, f (i x) = h (i x)) :
    LocalizedModule.mkLinearMap (Submonoid.powers g) (Module.Dual R C) f =
      LocalizedModule.mkLinearMap (Submonoid.powers g) (Module.Dual R C) h := by
  set l := LocalizedModule.mkLinearMap (Submonoid.powers g) (Module.Dual R C)
  have hi1 : algebraMap C Cg (i 1) = 1 := LinearMap.congr_fun hi 1
  have hs : i 1 • f = i 1 • h := by
    ext x
    show f (i 1 * x) = h (i 1 * x)
    have hx : i (algebraMap C Cg x) = i 1 * x := by
      simpa [Algebra.smul_def, mul_comm] using i.map_smul x (1 : Cg)
    simpa only [hx] using heq (algebraMap C Cg x)
  have hi1' : algebraMap C (Localization.Away g) (i 1) = 1 := by
    apply (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Cg).injective
    simpa only [AlgEquiv.commutes, map_one] using hi1
  have hs' : algebraMap C (Localization.Away g) (i 1) • l f =
      algebraMap C (Localization.Away g) (i 1) • l h := by
    simpa only [IsScalarTower.algebraMap_smul, ← l.map_smul] using congrArg l hs
  simpa only [hi1', one_smul] using hs'

/-! ### Zariski locality of the relative dualizing module -/

/-- A section of the relative dualizing module is determined by its localizations over a
principal cover of the target: the relative dualizing module is a quasi-coherent sheaf, and the
identification of [Stacks, Tag 0BT2 (2)] is injective. -/
theorem eq_of_localized_dualizingModule_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {ι : Type*} (g : ι → B) (hcover : Ideal.span (Set.range g) = ⊤)
    (G : ∀ i, FiniteOpenFactorization.{u, v, z} A (Localization.Away (g i)))
    (x y : dualizingModule F)
    (h : ∀ i,
      let f := LocalizedModule.mkLinearMap (Submonoid.powers (g i)) (dualizingModule F)
      let q := localizedModule_dualizingModule_equiv (g i) F (G i) f
        (inferInstance : IsLocalizedModule (Submonoid.powers (g i)) f)
      q (f x) = q (f y)) : x = y := by
  apply Module.eq_of_isLocalized_span (Set.range g) hcover
    (fun b => LocalizedModule (Submonoid.powers b.1) (dualizingModule F))
    (fun b => LocalizedModule.mkLinearMap (Submonoid.powers b.1) (dualizingModule F))
  rintro ⟨b, i, rfl⟩
  exact (localizedModule_dualizingModule_equiv (g i) F (G i)
    (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) (dualizingModule F))
    inferInstance).injective (h i)

/-- A section of the relative dualizing module which is a trace element on each member of a
principal cover of the target agrees with any global trace element: both localize to the trace
element of the localized algebra, which is unique. -/
theorem eq_of_isTraceElement_localization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {ι : Type*} (g : ι → B) (hcover : Ideal.span (Set.range g) = ⊤)
    (G : ∀ i, FiniteOpenFactorization.{u, v, z} A (Localization.Away (g i)))
    (x y : dualizingModule F)
    (hx : ∀ i,
      letI : IsNoetherianRing (Localization.Away (g i)) :=
        IsLocalization.isNoetherianRing (Submonoid.powers (g i)) _ inferInstance
      letI : Module.Flat B (Localization.Away (g i)) :=
        IsLocalization.flat _ (Submonoid.powers (g i))
      letI : Module.Flat A (Localization.Away (g i)) := Module.Flat.trans A B _
      letI : Algebra.QuasiFinite A (Localization.Away (g i)) :=
        Algebra.QuasiFinite.of_isLocalization (Submonoid.powers (g i))
      let f := LocalizedModule.mkLinearMap (Submonoid.powers (g i)) (dualizingModule F)
      IsTraceElement.{u, v, z, u, max u v, max u v} (G i)
        (localizedModule_dualizingModule_equiv (g i) F (G i) f
          (inferInstance : IsLocalizedModule (Submonoid.powers (g i)) f) (f x)))
    (hy : IsTraceElement.{u, v, w, u, max u v, max u v} F y) : x = y := by
  apply eq_of_localized_dualizingModule_eq F g hcover G x y
  intro i
  exact isTraceElement_unique (G i) (hx i) (isTraceElement_localization (g i) F (G i)
    (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) (dualizingModule F)) inferInstance hy)

/-! ### Restriction to a finite factor under extension and localization -/

/-- The restriction of a dualizing element to a finite factor commutes with a further extension
of the base: both sides are computed by the trace of multiplication on the factor, and that
trace commutes with scalar extension. -/
theorem finiteFactorRestriction_baseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type s) (A₂ : Type*) [CommRing A₁] [CommRing A₂]
    [Algebra A A₁] [Algebra A A₂] [Algebra A₁ A₂] [IsScalarTower A A₁ A₂]
    {C : Type t} {D : Type r} {C₂ D₂ : Type*}
    [CommRing C] [CommRing D] [CommRing C₂] [CommRing D₂]
    [Algebra A₁ C] [Algebra A₁ D] [Algebra A₂ C₂] [Algebra A₂ D₂]
    [Algebra A₁ C₂] [Algebra C C₂] [IsScalarTower A₁ A₂ C₂] [IsScalarTower A₁ C C₂]
    [Algebra (FiniteOpenFactorization.baseChange F A₁).middle C]
    [Algebra (FiniteOpenFactorization.baseChange F A₂).middle C₂]
    [Algebra (FiniteOpenFactorization.baseChange F A₁).middle
      (FiniteOpenFactorization.baseChange F A₂).middle]
    [Algebra (FiniteOpenFactorization.baseChange F A₁).middle C₂]
    [IsScalarTower (FiniteOpenFactorization.baseChange F A₁).middle
      (FiniteOpenFactorization.baseChange F A₂).middle C₂]
    [IsScalarTower (FiniteOpenFactorization.baseChange F A₁).middle C C₂]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D) (e₂ : (A₂ ⊗[A] B) ≃ₐ[A₂] C₂ × D₂)
    (he : ∀ a : (FiniteOpenFactorization.baseChange F A₁).middle,
      algebraMap _ C a = (e (algebraMap _ (A₁ ⊗[A] B) a)).1)
    (he₂ : ∀ a : (FiniteOpenFactorization.baseChange F A₂).middle,
      algebraMap _ C₂ a = (e₂ (algebraMap _ (A₂ ⊗[A] B) a)).1)
    (hmap : ∀ b : B,
      (e₂ ((1 : A₂) ⊗ₜ[A] b)).1 = algebraMap C C₂ (e ((1 : A₁) ⊗ₜ[A] b)).1)
    (hdual : ∀ (f : Module.Dual A F.middle)
        (x : (FiniteOpenFactorization.baseChange F A₁).middle),
      (f.baseChange A₂)
          (algebraMap _ (FiniteOpenFactorization.baseChange F A₂).middle x) =
        algebraMap A₁ A₂ ((f.baseChange A₁) x))
    (hbase : IsBaseChange (FiniteOpenFactorization.baseChange F A₂).middle
      ((Algebra.linearMap C C₂).restrictScalars
        (FiniteOpenFactorization.baseChange F A₁).middle))
    (hf : Module.Finite A₁ C) (hp : Module.Projective A₁ C)
    (hmf : Module.Finite (FiniteOpenFactorization.baseChange F A₁).middle C)
    (hmp : Module.Projective (FiniteOpenFactorization.baseChange F A₁).middle C)
    (h₂f : Module.Finite A₂ C₂) (h₂p : Module.Projective A₂ C₂)
    (h₂mf : Module.Finite (FiniteOpenFactorization.baseChange F A₂).middle C₂)
    (h₂mp : Module.Projective (FiniteOpenFactorization.baseChange F A₂).middle C₂)
    (τ : dualizingModule F) (c : C) :
    (finiteFactorRestriction F A₂ C₂ D₂ e₂ he₂ h₂f h₂p h₂mf h₂mp).1
        (dualizingModule.baseChange F A₂ τ) (algebraMap C C₂ c) =
      algebraMap A₁ A₂ ((finiteFactorRestriction F A₁ C D e he hf hp hmf hmp).1
        (dualizingModule.baseChange F A₁ τ) c) := by
  have := hmf
  have := hmp
  have := h₂mf
  have := h₂mp
  set ρ := finiteFactorRestriction F A₁ C D e he hf hp hmf hmp
  set ρ₂ := finiteFactorRestriction F A₂ C₂ D₂ e₂ he₂ h₂f h₂p h₂mf h₂mp
  refine dualizingModule.induction_on F (motive := fun τ =>
    ρ₂.1 (dualizingModule.baseChange F A₂ τ) (algebraMap C C₂ c) =
      algebraMap A₁ A₂ (ρ.1 (dualizingModule.baseChange F A₁ τ) c)) τ ?_ ?_ ?_
  · simp
  · intro f b
    rw [dualizingModule.baseChange_tmul F A₂ f b, dualizingModule.baseChange_tmul F A₁ f b]
    refine (ρ₂.2 (f.baseChange A₂) ((1 : A₂) ⊗ₜ[A] b) (algebraMap C C₂ c)).trans ?_
    refine Eq.trans ?_
      (congrArg (algebraMap A₁ A₂) (ρ.2 (f.baseChange A₁) ((1 : A₁) ⊗ₜ[A] b) c)).symm
    show (f.baseChange A₂) (finiteProjectiveTrace
        (FiniteOpenFactorization.baseChange F A₂).middle C₂
        (Algebra.lmul _ C₂ ((e₂ ((1 : A₂) ⊗ₜ[A] b)).1 * algebraMap C C₂ c))) = _
    rw [hmap, ← map_mul, finiteProjectiveTrace_lmul_baseChange hbase, hdual]
    rfl
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The restriction of a dualizing element to a finite factor commutes with localizing the
target, when the localized factor is a split quotient of the original one: the trace of
multiplication on a split quotient is the trace of multiplication by the retracted element. -/
theorem finiteFactorRestriction_localize_of_retract
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (g : B)
    (A₁ : Type s) [CommRing A₁] [Algebra A A₁]
    {C : Type t} {D : Type r} {Cg Dg : Type*}
    [CommRing C] [CommRing D] [CommRing Cg] [CommRing Dg]
    [Algebra A₁ C] [Algebra A₁ D] [Algebra A₁ Cg] [Algebra A₁ Dg]
    [Algebra C Cg] [IsScalarTower A₁ C Cg]
    [Algebra (FiniteOpenFactorization.baseChange F A₁).middle C]
    [Algebra (FiniteOpenFactorization.baseChange F A₁).middle Cg]
    [IsScalarTower (FiniteOpenFactorization.baseChange F A₁).middle C Cg]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D)
    (eg : (A₁ ⊗[A] Localization.Away g) ≃ₐ[A₁] Cg × Dg)
    (he : ∀ a : (FiniteOpenFactorization.baseChange F A₁).middle,
      algebraMap _ C a = (e (algebraMap _ (A₁ ⊗[A] B) a)).1)
    (heg : ∀ a : (FiniteOpenFactorization.baseChange F A₁).middle,
      algebraMap _ Cg a =
        (eg (algebraMap
          (FiniteOpenFactorization.baseChange
            (locFact (Bg := Localization.Away g) g F) A₁).middle
          (A₁ ⊗[A] Localization.Away g) a)).1)
    (hmap : ∀ b : B, (eg ((1 : A₁) ⊗ₜ[A] algebraMap B (Localization.Away g) b)).1 =
      algebraMap C Cg (e ((1 : A₁) ⊗ₜ[A] b)).1)
    (hf : Module.Finite A₁ C) (hp : Module.Projective A₁ C)
    (hmf : Module.Finite (FiniteOpenFactorization.baseChange F A₁).middle C)
    (hmp : Module.Projective (FiniteOpenFactorization.baseChange F A₁).middle C)
    (hgf : Module.Finite A₁ Cg) (hgp : Module.Projective A₁ Cg)
    (hgmf : Module.Finite (FiniteOpenFactorization.baseChange F A₁).middle Cg)
    (hgmp : Module.Projective (FiniteOpenFactorization.baseChange F A₁).middle Cg)
    (i : Cg →ₗ[C] C) (hi : (Algebra.linearMap C Cg).comp i = LinearMap.id)
    (τ : dualizingModule F) (c : Cg) :
    letI : Algebra (FiniteOpenFactorization.baseChange
        (locFact (Bg := Localization.Away g) g F) A₁).middle Cg :=
      inferInstanceAs (Algebra (FiniteOpenFactorization.baseChange F A₁).middle Cg)
    (finiteFactorRestriction (locFact (Bg := Localization.Away g) g F) A₁ Cg Dg eg heg
        hgf hgp hgmf hgmp).1
      (dualizingModule.baseChange (locFact (Bg := Localization.Away g) g F) A₁
        (localizationDualizingMap F g τ)) c =
      (finiteFactorRestriction F A₁ C D e he hf hp hmf hmp).1
        (dualizingModule.baseChange F A₁ τ) (i c) := by
  let : Algebra (FiniteOpenFactorization.baseChange
      (locFact (Bg := Localization.Away g) g F) A₁).middle Cg :=
    inferInstanceAs (Algebra (FiniteOpenFactorization.baseChange F A₁).middle Cg)
  have := hmf
  have := hmp
  have := hgmf
  have := hgmp
  set ρ := finiteFactorRestriction F A₁ C D e he hf hp hmf hmp
  set ρg := finiteFactorRestriction (locFact (Bg := Localization.Away g) g F) A₁ Cg Dg eg heg
    hgf hgp hgmf hgmp
  refine dualizingModule.induction_on F (motive := fun τ =>
    ρg.1 (dualizingModule.baseChange (locFact (Bg := Localization.Away g) g F) A₁
        (localizationDualizingMap F g τ)) c =
      ρ.1 (dualizingModule.baseChange F A₁ τ) (i c)) τ ?_ ?_ ?_
  · simp
  · intro f b
    rw [localizationDualizingMap_tmul,
      dualizingModule.baseChange_tmul (locFact (Bg := Localization.Away g) g F) A₁ f,
      dualizingModule.baseChange_tmul F A₁ f b]
    refine (ρg.2 (f.baseChange A₁)
      ((1 : A₁) ⊗ₜ[A] algebraMap B (Localization.Away g) b) c).trans ?_
    refine Eq.trans ?_ (ρ.2 (f.baseChange A₁) ((1 : A₁) ⊗ₜ[A] b) (i c)).symm
    show (f.baseChange A₁)
        (finiteProjectiveTrace (FiniteOpenFactorization.baseChange F A₁).middle Cg
          (Algebra.lmul _ Cg
            ((eg ((1 : A₁) ⊗ₜ[A] algebraMap B (Localization.Away g) b)).1 * c))) =
      (f.baseChange A₁)
        (finiteProjectiveTrace (FiniteOpenFactorization.baseChange F A₁).middle C
          (Algebra.lmul _ C ((e ((1 : A₁) ⊗ₜ[A] b)).1 * i c)))
    rw [hmap, finiteProjectiveTrace_lmul_of_retract i hi]
    exact congrArg (fun x : C => (f.baseChange A₁)
      (finiteProjectiveTrace (FiniteOpenFactorization.baseChange F A₁).middle C
        (Algebra.lmul _ C x)))
      (by simpa [Algebra.smul_def] using i.map_smul (e ((1 : A₁) ⊗ₜ[A] b)).1 c)
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Two additive maps out of a tensor product that agree on pure tensors are equal. -/
private theorem tensorProduct_apply_eq_of_tmul {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [AddCommMonoid P]
    (f g : M ⊗[R] N →+ P) (h : ∀ m n, f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) (x : M ⊗[R] N) :
    f x = g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n => exact h m n
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The structure map of the base change of the localized factorization, read through the
localized product decomposition. -/
theorem baseChangeLocalizationProdEquiv_algebraMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (g : B)
    (A₁ : Type s) [CommRing A₁] [Algebra A A₁]
    {C : Type t} {D : Type r} [CommRing C] [CommRing D] [Algebra A₁ C] [Algebra A₁ D]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D)
    (x : (FiniteOpenFactorization.baseChange F A₁).middle) :
    baseChangeLocalizationProdEquiv g A₁ e
        (algebraMap (FiniteOpenFactorization.baseChange
          (locFact (Bg := Localization.Away g) g F) A₁).middle
          (A₁ ⊗[A] Localization.Away g) x) =
      (algebraMap C _ (e (algebraMap _ (A₁ ⊗[A] B) x)).1,
        algebraMap D _ (e (algebraMap _ (A₁ ⊗[A] B) x)).2) := by
  set L := (baseChangeLocalizationProdEquiv g A₁ e).toRingHom.comp
    (algebraMap (FiniteOpenFactorization.baseChange
      (locFact (Bg := Localization.Away g) g F) A₁).middle
      (A₁ ⊗[A] Localization.Away g))
  set R := ((algebraMap C (Localization.Away (e ((1 : A₁) ⊗ₜ[A] g)).1)).prodMap
    (algebraMap D (Localization.Away (e ((1 : A₁) ⊗ₜ[A] g)).2))).comp
    (e.toRingHom.comp
      (algebraMap (FiniteOpenFactorization.baseChange F A₁).middle (A₁ ⊗[A] B)))
  change L x = R x
  induction x using TensorProduct.induction_on with
  | zero => exact L.map_zero.trans R.map_zero.symm
  | add x y hx hy =>
      exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)
  | tmul a b => exact baseChangeLocalizationProdEquiv_tmul g A₁ e a (algebraMap F.middle B b)

/-! ### Gluing over a principal open cover -/

section ArtinianCover

-- The scalar action of a ring on an away localization of one of its quotients must be read
-- through the algebra structure, not through the generic action on an Ore localization.
attribute [local instance 0] OreLocalization.instSMulOfIsScalarTower

/-- Over an Artinian finite factor, a section of the relative dualizing module which is a trace
element on each member of a principal open cover of the target restricts to the trace.

The images of the cover in the Artinian ring `C` again generate the unit ideal, and over an
Artinian ring an away localization `C → C_c` is surjective, hence split. So the restriction of
the section to `C` agrees with the trace after localizing at each member of the cover, by the
local hypothesis and the computation of the trace on a split quotient; and a functional is
determined by its images in such a cover. -/
theorem finiteFactorRestriction_eq_of_artinian_cover
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {ι : Type*} (g : ι → B) (hcover : Ideal.span (Set.range g) = ⊤)
    (τ : dualizingModule F)
    (hlocal : ∀ i,
      letI : IsNoetherianRing (Localization.Away (g i)) :=
        IsLocalization.isNoetherianRing (Submonoid.powers (g i)) _ inferInstance
      letI : Module.Flat B (Localization.Away (g i)) :=
        IsLocalization.flat _ (Submonoid.powers (g i))
      letI : Module.Flat A (Localization.Away (g i)) := Module.Flat.trans A B _
      letI : Algebra.QuasiFinite A (Localization.Away (g i)) :=
        Algebra.QuasiFinite.of_isLocalization (Submonoid.powers (g i))
      IsTraceElement.{u, v, w, s, t, r} (locFact (Bg := Localization.Away (g i)) (g i) F)
        (localizationDualizingMap F (g i) τ))
    (A₁ : Type s) [CommRing A₁] [Algebra A A₁] [IsNoetherianRing A₁]
    (C : Type t) (D : Type r) [CommRing C] [CommRing D]
    [Algebra A₁ C] [Algebra A₁ D] [IsArtinianRing C]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] C × D)
    [Algebra (FiniteOpenFactorization.baseChange F A₁).middle C]
    (he : ∀ a : (FiniteOpenFactorization.baseChange F A₁).middle,
      algebraMap _ C a = (e (algebraMap _ (A₁ ⊗[A] B) a)).1)
    (hf : Module.Finite A₁ C) (hp : Module.Projective A₁ C)
    (hmf : Module.Finite (FiniteOpenFactorization.baseChange F A₁).middle C)
    (hmp : Module.Projective (FiniteOpenFactorization.baseChange F A₁).middle C) :
    letI := hp
    (finiteFactorRestriction F A₁ C D e he hf hp hmf hmp).1
        (dualizingModule.baseChange F A₁ τ) =
      (finiteProjectiveTrace A₁ C).comp (Algebra.lmul A₁ C).toLinearMap := by
  have := hf
  have := hp
  let γ : B →+* C :=
    (RingHom.fst C D).comp (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  have hγ : Ideal.span (Set.range (γ ∘ g)) = ⊤ := by
    have h : Ideal.map γ (Ideal.span (Set.range g)) = ⊤ := by rw [hcover, Ideal.map_top]
    simpa only [Ideal.map_span, ← Set.range_comp] using h
  apply Module.eq_of_isLocalized_span (Set.range (γ ∘ g)) hγ
    (fun c => LocalizedModule (Submonoid.powers c.1) (Module.Dual A₁ C))
    (fun c => LocalizedModule.mkLinearMap (Submonoid.powers c.1) (Module.Dual A₁ C))
  rintro ⟨_, j, rfl⟩
  let Cg := Localization.Away (e ((1 : A₁) ⊗ₜ[A] g j)).1
  let Dg := Localization.Away (e ((1 : A₁) ⊗ₜ[A] g j)).2
  let eg := baseChangeLocalizationProdEquiv (g j) A₁ e
  have : IsLocalization.Away (γ (g j)) Cg := by
    show IsLocalization.Away (e ((1 : A₁) ⊗ₜ[A] g j)).1 Cg
    infer_instance
  have hsurj : Function.Surjective (algebraMap C Cg) :=
    IsArtinianRing.localization_surjective (Submonoid.powers (γ (g j))) Cg
  have : Module.Finite C Cg := Module.Finite.of_surjective (Algebra.linearMap C Cg) hsurj
  have : Module.Finite A₁ Cg := Module.Finite.trans C Cg
  let Hg := FiniteOpenFactorization.baseChange
    (locFact (Bg := Localization.Away (g j)) (g j) F) A₁
  let : Algebra (FiniteOpenFactorization.baseChange F A₁).middle Cg :=
    ((RingHom.fst Cg Dg).comp
      (eg.toRingEquiv.toRingHom.comp Hg.algebraTarget.algebraMap)).toAlgebra
  have : IsScalarTower (FiniteOpenFactorization.baseChange F A₁).middle C Cg := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    show (eg (algebraMap Hg.middle (A₁ ⊗[A] Localization.Away (g j)) a)).1 =
      algebraMap C Cg (algebraMap _ C a)
    rw [he]
    exact congrArg Prod.fst (baseChangeLocalizationProdEquiv_algebraMap F (g j) A₁ e a)
  obtain ⟨hgp, hgmf, hgmp, ht⟩ := hlocal j A₁ Cg Dg eg inferInstance
  have := hgp
  have : Module.Flat C Cg := IsLocalization.flat Cg (Submonoid.powers (γ (g j)))
  have : Module.FinitePresentation C Cg := Module.finitePresentation_of_finite C Cg
  have : Module.Projective C Cg := Module.Flat.projective_of_finitePresentation
  obtain ⟨i, hi⟩ := Module.projective_lifting_property
    (Algebra.linearMap C Cg) (LinearMap.id : Cg →ₗ[C] Cg) hsurj
  apply localized_dual_eq_of_retraction (γ (g j)) i hi
  intro c
  rw [← finiteFactorRestriction_localize_of_retract F (g j) A₁ e eg he
    (fun _ => rfl)
    (fun b => congrArg Prod.fst (baseChangeLocalizationProdEquiv_tmul (g j) A₁ e 1 b))
    hf hp hmf hmp inferInstance hgp hgmf hgmp i hi τ c]
  rw [ht]
  exact finiteProjectiveTrace_lmul_of_retract i hi c

end ArtinianCover

/-- **Stacks Project, Tag 0BTA.** A section of the relative dualizing module of a flat
quasi-finite map of Noetherian rings which is a trace element on every member of a finite
principal open cover of the target is a trace element. -/
@[stacks 0BTA]
theorem isTraceElement_of_localization_cover
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {n : ℕ} (g : Fin n → B) (hcover : Ideal.span (Set.range g) = ⊤)
    (τ : dualizingModule F)
    (G : ∀ i : Fin n, FiniteOpenFactorization.{u, v, z} A (Localization.Away (g i)))
    (hlocal : ∀ i : Fin n,
      letI : IsNoetherianRing (Localization.Away (g i)) :=
        IsLocalization.isNoetherianRing (Submonoid.powers (g i))
          (Localization.Away (g i)) inferInstance
      letI : Module.Flat B (Localization.Away (g i)) :=
        IsLocalization.flat (Localization.Away (g i)) (Submonoid.powers (g i))
      letI : Module.Flat A (Localization.Away (g i)) :=
        Module.Flat.trans A B (Localization.Away (g i))
      letI : Algebra.QuasiFinite A (Localization.Away (g i)) :=
        Algebra.QuasiFinite.of_isLocalization (Submonoid.powers (g i))
      IsTraceElement.{u, v, z, s, t, r} (G i)
        (localizedModule_dualizingModule_equiv (g i) F (G i)
          (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) (dualizingModule F))
          (inferInstance : IsLocalizedModule (Submonoid.powers (g i))
            (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) (dualizingModule F)))
          (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) (dualizingModule F) τ))) :
    IsTraceElement.{u, v, w, s, t, r} F τ := by
  have hlocal' (i : Fin n) :
      IsTraceElement.{u, v, w, s, t, r} (locFact (Bg := Localization.Away (g i)) (g i) F)
        (localizationDualizingMap F (g i) τ) := by
    have h := (isTraceElement_congr (G i) (locFact (g i) F) _).mp (hlocal i)
    rwa [localizedModule_dualizingModule_equiv_natural] at h
  unfold IsTraceElement
  intro A₁ _ _ _ C D _ _ _ _ e hfinite F₁
  have : Module.Finite A₁ C := hfinite
  have : Module.Flat A₁ (A₁ ⊗[A] B) := inferInstance
  have : Module.Flat A₁ (C × D) := Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  have : Module.Flat A₁ C :=
    Module.Flat.of_retract (LinearMap.inl A₁ C D) (LinearMap.fst A₁ C D) (by ext; simp)
  have hprojective : Module.Projective A₁ C := by
    have : Module.FinitePresentation A₁ C := Module.finitePresentation_of_finite A₁ C
    exact Module.Flat.projective_of_finitePresentation
  have : Module.Projective A₁ C := hprojective
  let : Algebra F₁.middle C :=
    ((RingHom.fst C D).comp (e.toRingEquiv.toRingHom.comp F₁.algebraTarget.algebraMap)).toAlgebra
  have : IsScalarTower A₁ F₁.middle C := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    show (algebraMap A₁ C) a =
      (RingHom.fst C D) (e (algebraMap F₁.middle (A₁ ⊗[A] B) ((algebraMap A₁ F₁.middle) a)))
    rw [← F₁.scalarTower.algebraMap_apply, e.commutes]
    rfl
  let : Algebra F₁.middle D :=
    ((RingHom.snd C D).comp (e.toRingEquiv.toRingHom.comp F₁.algebraTarget.algebraMap)).toAlgebra
  have : IsScalarTower A₁ F₁.middle D := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    show (algebraMap A₁ D) a =
      (RingHom.snd C D) (e (algebraMap F₁.middle (A₁ ⊗[A] B) ((algebraMap A₁ F₁.middle) a)))
    rw [← F₁.scalarTower.algebraMap_apply, e.commutes]
    rfl
  let : Algebra F₁.middle (C × D) :=
    (e.toRingEquiv.toRingHom.comp F₁.algebraTarget.algebraMap).toAlgebra
  let eLin : (A₁ ⊗[A] B) →ₗ[F₁.middle] C × D :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a x
        show e ((algebraMap F₁.middle (A₁ ⊗[A] B) a) * x) =
          (algebraMap F₁.middle (C × D) a) * e x
        exact e.map_mul _ _ }
  have : Module.Flat F₁.middle (A₁ ⊗[A] B) := flat_of_finiteOpenFactorization F₁
  have : Module.Flat F₁.middle (C × D) :=
    Module.Flat.of_linearEquiv (LinearEquiv.ofBijective eLin e.bijective).symm
  have : Module.Flat F₁.middle C :=
    Module.Flat.of_retract (LinearMap.inl F₁.middle C D) (LinearMap.fst F₁.middle C D)
      (by ext; simp)
  have hmfinite : Module.Finite F₁.middle C :=
    Module.Finite.of_restrictScalars_finite A₁ F₁.middle C
  have hmprojective : Module.Projective F₁.middle C := by
    have : IsNoetherianRing F₁.middle := Algebra.FiniteType.isNoetherianRing A₁ F₁.middle
    have : Module.FinitePresentation F₁.middle C := Module.finitePresentation_of_finite F₁.middle C
    exact Module.Flat.projective_of_finitePresentation
  refine ⟨hprojective, hmfinite, hmprojective, ?_⟩
  apply LinearMap.ext
  intro c
  apply eq_of_forall_isArtinianRing_quotient_eq
  intro I hI
  let A₂ := A₁ ⧸ I
  have : IsArtinianRing A₂ := hI
  have : Small.{t} (A₂ ⊗[A₁] C) := small_of_surjective
    (Algebra.TensorProduct.includeRight_surjective C
      (show Function.Surjective (algebraMap A₁ A₂) from Ideal.Quotient.mk_surjective))
  have : Small.{r} (A₂ ⊗[A₁] D) := small_of_surjective
    (Algebra.TensorProduct.includeRight_surjective D
      (show Function.Surjective (algebraMap A₁ A₂) from Ideal.Quotient.mk_surjective))
  let : Algebra C (A₂ ⊗[A₁] C) := Algebra.TensorProduct.rightAlgebra
  let : Algebra D (A₂ ⊗[A₁] D) := Algebra.TensorProduct.rightAlgebra
  let : Algebra F₁.middle (A₂ ⊗[A₁] C) :=
    ((algebraMap C (A₂ ⊗[A₁] C)).comp (algebraMap F₁.middle C)).toAlgebra
  have : IsScalarTower F₁.middle C (A₂ ⊗[A₁] C) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A₁ F₁.middle (A₂ ⊗[A₁] C) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    show algebraMap A₁ (A₂ ⊗[A₁] C) a =
      algebraMap C (A₂ ⊗[A₁] C) (algebraMap F₁.middle C (algebraMap A₁ F₁.middle a))
    rw [← IsScalarTower.algebraMap_apply A₁ F₁.middle C,
      ← IsScalarTower.algebraMap_apply A₁ C (A₂ ⊗[A₁] C)]
  let C₂ := Shrink.{t} (A₂ ⊗[A₁] C)
  let D₂ := Shrink.{r} (A₂ ⊗[A₁] D)
  let eC : (A₂ ⊗[A₁] C) ≃ₐ[A₂] C₂ := (Shrink.algEquiv A₂ _).symm
  let eD : (A₂ ⊗[A₁] D) ≃ₐ[A₂] D₂ := (Shrink.algEquiv A₂ _).symm
  let e₂ : (A₂ ⊗[A] B) ≃ₐ[A₂] C₂ × D₂ :=
    (baseChangeProdEquiv A₁ A₂ e).trans (AlgEquiv.prodCongr eC eD)
  have hC₂tower : IsScalarTower A₁ A₂ C₂ := isScalarTower_shrink
  have : IsScalarTower A₁ C C₂ := isScalarTower_shrink
  have : IsScalarTower A₁ A₂ D₂ := isScalarTower_shrink
  have hC₂finite : Module.Finite A₂ C₂ := Module.Finite.equiv eC.toLinearEquiv
  have hC₂projective : Module.Projective A₂ C₂ := Module.Projective.of_equiv eC.toLinearEquiv
  have : IsScalarTower A₂ C₂ C₂ := isScalarTower_shrink_self
  have : IsArtinianRing (A₂ ⊗[A₁] C) := IsArtinianRing.of_finite A₂ _
  have : IsArtinianRing C₂ := eC.toRingEquiv.isArtinianRing
  let F₂ := FiniteOpenFactorization.baseChange F A₂
  let : Algebra A F₁.middle := (inferInstance : Algebra A (A₁ ⊗[A] F.middle))
  let : Algebra A F₂.middle := (inferInstance : Algebra A (A₂ ⊗[A] F.middle))
  let : Algebra A₁ F₂.middle := (inferInstance : Algebra A₁ (A₂ ⊗[A] F.middle))
  have : IsScalarTower A₁ A₂ F₂.middle :=
    (inferInstance : IsScalarTower A₁ A₂ (A₂ ⊗[A] F.middle))
  let φ : F₁.middle →ₐ[A] F₂.middle :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A₁ A₂) (AlgHom.id A F.middle)
  let ψ : (A₁ ⊗[A] B) →ₐ[A] (A₂ ⊗[A] B) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A₁ A₂) (AlgHom.id A B)
  let : Algebra F₁.middle F₂.middle := φ.toRingHom.toAlgebra
  let : Algebra F₂.middle C₂ :=
    ((RingHom.fst C₂ D₂).comp (e₂.toRingHom.comp F₂.algebraTarget.algebraMap)).toAlgebra
  have hemap (b : A₁ ⊗[A] B) :
      e₂ (ψ b) = (algebraMap C C₂ (e b).1, algebraMap D D₂ (e b).2) := by
    show (eC ((baseChangeProdEquiv A₁ A₂ e (ψ b)).1),
      eD ((baseChangeProdEquiv A₁ A₂ e (ψ b)).2)) = _
    rw [baseChangeProdEquiv_map]
    rfl
  have hφ (a : F₁.middle) :
      algebraMap F₂.middle (A₂ ⊗[A] B) (φ a) = ψ (algebraMap F₁.middle (A₁ ⊗[A] B) a) := by
    exact tensorProduct_apply_eq_of_tmul (R := A) (M := A₁) (N := F.middle)
      ((algebraMap F₂.middle (A₂ ⊗[A] B)).comp φ.toRingHom).toAddMonoidHom
      (ψ.toRingHom.comp (algebraMap F₁.middle (A₁ ⊗[A] B))).toAddMonoidHom (fun _ _ => rfl) a
  have : IsScalarTower A₁ F₁.middle F₂.middle := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A₁ F₁.middle C₂ := isScalarTower_shrink
  have : IsScalarTower F₁.middle C C₂ := isScalarTower_shrink
  have : IsScalarTower A₂ F₂.middle C₂ := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    show algebraMap A₂ C₂ a =
      (e₂ (algebraMap F₂.middle (A₂ ⊗[A] B) (algebraMap A₂ F₂.middle a))).1
    rw [← IsScalarTower.algebraMap_apply, e₂.commutes]
    rfl
  have : IsScalarTower F₁.middle F₂.middle C₂ := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    show algebraMap F₁.middle C₂ a = (e₂ (algebraMap F₂.middle (A₂ ⊗[A] B) (φ a))).1
    rw [hφ, hemap]
    exact IsScalarTower.algebraMap_apply F₁.middle C C₂ a
  have : IsScalarTower A₁ F₂.middle C₂ := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [IsScalarTower.algebraMap_eq A₁ A₂ C₂, IsScalarTower.algebraMap_eq A₁ A₂ F₂.middle]
    exact IsScalarTower.algebraMap_apply A₂ F₂.middle C₂ (algebraMap A₁ A₂ a)
  have : Algebra.IsPushout A₁ A₂ F₁.middle F₂.middle :=
    Algebra.IsPushout.tensorProduct_tensorProduct A F.middle A₁ A₂ (by ext x; rfl)
  have hpushoutC : Algebra.IsPushout A₁ A₂ C C₂ := Algebra.IsPushout.of_equiv eC (by ext x; rfl)
  have : Algebra.IsPushout A₁ F₁.middle A₂ F₂.middle := Algebra.IsPushout.symm inferInstance
  have : Algebra.IsPushout A₁ C A₂ C₂ := Algebra.IsPushout.symm inferInstance
  have : Algebra.IsPushout F₁.middle C F₂.middle C₂ :=
    (Algebra.IsPushout.comp_iff A₁ F₁.middle A₂ F₂.middle).mp inferInstance
  have : Algebra.IsPushout F₁.middle F₂.middle C C₂ := Algebra.IsPushout.symm inferInstance
  have hbase : IsBaseChange F₂.middle (IsScalarTower.toAlgHom F₁.middle C C₂).toLinearMap :=
    Algebra.IsPushout.out
  have : Module.Finite F₂.middle C₂ := Module.Finite.equiv hbase.equiv
  have : Module.Projective F₂.middle C₂ := Module.Projective.of_equiv hbase.equiv
  have htrace := finiteFactorRestriction_eq_of_artinian_cover F g hcover τ hlocal'
    A₂ C₂ D₂ e₂ (fun _ => rfl) hC₂finite hC₂projective inferInstance inferInstance
  have hdual (f : Module.Dual A F.middle) (x : F₁.middle) :
      (f.baseChange A₂) (algebraMap F₁.middle F₂.middle x) =
        algebraMap A₁ A₂ ((f.baseChange A₁) x) := by
    refine tensorProduct_apply_eq_of_tmul (R := A) (M := A₁) (N := F.middle)
      ((f.baseChange A₂).toAddMonoidHom.comp (algebraMap F₁.middle F₂.middle).toAddMonoidHom)
      ((algebraMap A₁ A₂).toAddMonoidHom.comp (f.baseChange A₁).toAddMonoidHom)
      (fun a b => ?_) x
    change (f.baseChange A₂) (algebraMap A₁ A₂ a ⊗ₜ[A] b) =
      algebraMap A₁ A₂ ((f.baseChange A₁) (a ⊗ₜ[A] b))
    simp only [Module.Dual.baseChange_apply_tmul, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have hrestriction := finiteFactorRestriction_baseChange F A₁ A₂ e e₂ (fun _ => rfl)
    (fun _ => rfl) (fun b => congrArg Prod.fst (hemap ((1 : A₁) ⊗ₜ[A] b)))
    hdual hbase hfinite hprojective hmfinite hmprojective
    hC₂finite hC₂projective inferInstance inferInstance τ c
  show algebraMap A₁ A₂ _ = algebraMap A₁ A₂ _
  rw [← hrestriction, htrace]
  exact @finiteProjectiveTrace_lmul_baseChange A₁ A₂ C C₂
    _ _ _ _ _ _ _ _ _ hC₂tower _ hfinite hprojective hC₂finite hC₂projective hpushoutC.out c

end Stacks.Discriminant

end
