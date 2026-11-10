module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Tactic.LinearCombination

/-!
# Extending derivations

Let `R` be a ring and `D : R → R` a derivation, modelled as `Derivation ℤ R R`. Then `D` extends
to a derivation of the `I`-adic completion of `R`, and extends uniquely to a derivation of any
localization of `R`. If `R'` is a finite type `R`-algebra and `g ∈ R` is a nonzerodivisor in `R'`
such that `R[1/g] → R'[1/g]` is an isomorphism, then `g ^ N • D` extends to a derivation of `R'`
for some `N : ℕ`.

## Main definitions

* `Stacks.DerivationExtension.ExtendsAlong`: a derivation of `R'` extends a derivation of `R` along
  `R →+* R'`.
* `Stacks.DerivationExtension.locDeriv`: the extension of a derivation of `R` to a localization of
  `R`.

## Main results

* `Stacks.DerivationExtension.exists_derivation_adicCompletion`: a derivation extends to the
  `I`-adic completion.
* `Stacks.DerivationExtension.locDeriv_extendsAlong`: `locDeriv` extends the given derivation.
* `Stacks.DerivationExtension.locDeriv_unique`: no other derivation of the localization does.
* `Stacks.DerivationExtension.exists_derivation_clear_denominators`: `g ^ N • D` extends to `R'`.

## References

* [Stacks project, Tag 07PE]
-/

@[expose] public section

namespace Stacks.DerivationExtension

/-- A derivation `D' : R' → R'` *extends* a derivation `D : R → R` along a ring map
`φ : R →+* R'` if `D' (φ r) = φ (D r)` for all `r ∈ R`. -/
def ExtendsAlong {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (D : Derivation ℤ R R) (D' : Derivation ℤ R' R') : Prop :=
  ∀ r : R, D' (φ r) = φ (D r)

/-! ### Extension to a localization -/

section Localization

open TrivSqZeroExt

variable {R : Type*} [CommRing R] (D : Derivation ℤ R R) (S : Submonoid R)
  (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]

/-- The ring hom `R →+* DualNumber L`, `r ↦ (ι r, ι (D r))`, that encodes the
derivation `D` together with the canonical map `R → L`. -/
noncomputable def locDualHom : R →+* DualNumber L where
  toFun r := TrivSqZeroExt.inl (algebraMap R L r) + TrivSqZeroExt.inr (algebraMap R L (D r))
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_mul' := by
    intro a b
    apply TrivSqZeroExt.ext
    · simp [fst_mul, map_mul]
    · simp only [snd_add, snd_inl, snd_inr, snd_mul, fst_add, fst_inl, fst_inr,
        add_zero, zero_add, op_smul_eq_smul, smul_eq_mul]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' := by
    intro a b
    apply TrivSqZeroExt.ext <;>
      simp only [snd_add, snd_inl, snd_inr, fst_add, fst_inl, fst_inr, map_add, add_zero, zero_add]

/-- The first component of `locDualHom D L r` is the image of `r` in `L`. -/
@[simp] lemma fst_locDualHom (r : R) : (locDualHom D L r).fst = algebraMap R L r := by
  simp [locDualHom, fst_add, fst_inl]

/-- The second component of `locDualHom D L r` is the image of `D r` in `L`. -/
@[simp] lemma snd_locDualHom (r : R) : (locDualHom D L r).snd = algebraMap R L (D r) := by
  simp only [locDualHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, snd_add, snd_inl,
    snd_inr, zero_add]

/-- The ring hom `locDualHom D L` sends every element of `S` to a unit. -/
lemma isUnit_locDualHom : ∀ y : S, IsUnit (locDualHom D L y) := fun y => by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_locDualHom]
  exact IsLocalization.map_units L y

/-- The ring hom `L →+* DualNumber L` extending `locDualHom D L` along `R → L`. -/
noncomputable def locDualLift : L →+* DualNumber L :=
  IsLocalization.lift (isUnit_locDualHom D S L)

/-- The ring hom `locDualLift D S L` agrees with `locDualHom D L` on the image of `R`. -/
@[simp] lemma locDualLift_algebraMap (r : R) :
    locDualLift D S L (algebraMap R L r) = locDualHom D L r :=
  IsLocalization.lift_eq (isUnit_locDualHom D S L) r

/-- The first component of `locDualLift D S L x` is `x`. -/
@[simp] lemma fst_locDualLift (x : L) : (locDualLift D S L x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℤ L L).toRingHom.comp (locDualLift D S L) = RingHom.id L := by
    apply IsLocalization.ringHom_ext S
    ext r
    simp
  simpa using RingHom.congr_fun h x

/-- The derivation of the localization `L` extending `D` along `R → L`. -/
@[stacks 07PE "(2): the extension itself"]
noncomputable def locDeriv : Derivation ℤ L L where
  toLinearMap :=
    (((TrivSqZeroExt.sndHom L L).toAddMonoidHom.comp
      (locDualLift D S L).toAddMonoidHom)).toIntLinearMap
  map_one_eq_zero' := by
    change (locDualLift D S L 1).snd = 0
    simp [map_one]
  leibniz' := by
    intro a b
    change (locDualLift D S L (a * b)).snd
      = a • (locDualLift D S L b).snd + b • (locDualLift D S L a).snd
    rw [map_mul, snd_mul, fst_locDualLift, fst_locDualLift]
    simp only [op_smul_eq_smul, smul_eq_mul]

/-- The value of `locDeriv D S L` at `x` is the second component of `locDualLift D S L x`. -/
lemma locDeriv_apply (x : L) : locDeriv D S L x = (locDualLift D S L x).snd := rfl

/-- The derivation `locDeriv D S L` extends `D` along `R → L`. -/
@[simp] lemma locDeriv_algebraMap (r : R) :
    locDeriv D S L (algebraMap R L r) = algebraMap R L (D r) := by
  rw [locDeriv_apply, locDualLift_algebraMap, snd_locDualHom]

include S in
/-- A derivation on a localization is determined by its values on the image of `R`. -/
lemma derivation_ext_of_algebraMap (D₁ D₂ : Derivation ℤ L L)
    (h : ∀ r : R, D₁ (algebraMap R L r) = D₂ (algebraMap R L r)) : D₁ = D₂ := by
  apply Derivation.ext
  intro x
  obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj S x
  have key : ∀ (Dd : Derivation ℤ L L),
      Dd x * algebraMap R L (s:R)
        = Dd (algebraMap R L a) - x * Dd (algebraMap R L (s:R)) := by
    intro Dd
    have e1 : Dd (x * algebraMap R L (s:R)) = Dd (algebraMap R L a) := by rw [hx]
    rw [Derivation.leibniz] at e1
    simp only [smul_eq_mul] at e1
    linear_combination e1
  have hsu : IsUnit (algebraMap R L (s:R)) := IsLocalization.map_units L s
  have heq : D₁ x * algebraMap R L (s:R) = D₂ x * algebraMap R L (s:R) := by
    rw [key D₁, key D₂, h a, h s]
  exact hsu.mul_right_cancel heq

/-- `locDeriv D S L` extends `D` along the canonical map `R → L`. -/
@[stacks 07PE "(2): the extension property of `locDeriv`"]
lemma locDeriv_extendsAlong : ExtendsAlong (algebraMap R L) D (locDeriv D S L) :=
  locDeriv_algebraMap D S L

/-- `locDeriv D S L` is the only derivation of `L` extending `D` along `R → L`. -/
@[stacks 07PE "(2): uniqueness of `locDeriv`"]
lemma locDeriv_unique (Dloc : Derivation ℤ L L)
    (hDloc : ExtendsAlong (algebraMap R L) D Dloc) : Dloc = locDeriv D S L :=
  derivation_ext_of_algebraMap S L Dloc (locDeriv D S L) fun r => by
    rw [hDloc r, locDeriv_algebraMap D S L r]

end Localization

/-! ### Extension to the `I`-adic completion -/

section Adic

variable {R : Type*} [CommRing R] (D : Derivation ℤ R R) (I : Ideal R)

/-- A derivation `D` sends `I ^ (n + 1)` into `I ^ n`. -/
lemma map_mem_pow_of_mem_pow_succ (n : ℕ) {x : R} (hx : x ∈ I ^ (n + 1)) : D x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Submodule.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hb (ih ha)
    · intro y z hy hz
      rw [map_add]
      exact add_mem hy hz

/-- A derivation `D` maps `I ^ (n + 1) • ⊤` into `I ^ n • ⊤`. -/
lemma map_mem_pow_smul_top (n : ℕ) :
    ∀ x ∈ (I ^ (n + 1) • (⊤ : Submodule R R)),
      (D : R →ₗ[ℤ] R) x ∈ (I ^ n • (⊤ : Submodule R R)) := by
  intro x hx
  rw [smul_eq_mul, Ideal.mul_top] at hx ⊢
  exact map_mem_pow_of_mem_pow_succ D I n hx

/-- The ℤ-linear map `R ⧸ I ^ (n + 1) • ⊤ → R ⧸ I ^ n • ⊤` induced by `D`. -/
noncomputable def derivMod (n : ℕ) :
    (R ⧸ (I ^ (n + 1) • (⊤ : Submodule R R))) →ₗ[ℤ] (R ⧸ (I ^ n • (⊤ : Submodule R R))) :=
  Submodule.mapQ ((I ^ (n + 1) • (⊤ : Submodule R R)).restrictScalars ℤ)
    ((I ^ n • (⊤ : Submodule R R)).restrictScalars ℤ) (D : R →ₗ[ℤ] R)
    (map_mem_pow_smul_top D I n)

/-- For `m ≤ n`, the maps `derivMod` commute with the transition maps of the `I`-adic completion
on the class of any `r : R`. -/
lemma transitionMap_derivMod_mk {m n : ℕ} (hmn : m ≤ n) (r : R) :
    AdicCompletion.transitionMap I R hmn
        (derivMod D I n (Submodule.Quotient.mk r))
      = derivMod D I m
          (AdicCompletion.transitionMap I R (Nat.succ_le_succ hmn) (Submodule.Quotient.mk r)) := by
  rfl

/-- The map of `AdicCompletion I R` sending `x` to the compatible family
`n ↦ derivMod D I n (x.val (n + 1))`. -/
noncomputable def adicDerivFun (x : AdicCompletion I R) : AdicCompletion I R :=
  ⟨fun n => derivMod D I n (x.val (n + 1)), by
    intro m n hmn
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
    simp only
    rw [← hr, transitionMap_derivMod_mk D I hmn r, hr,
      x.property (Nat.succ_le_succ hmn)]⟩

/-- The `n`-th component of `adicDerivFun D I x` is `derivMod D I n (x.val (n + 1))`. -/
@[simp] lemma adicDerivFun_val (x : AdicCompletion I R) (n : ℕ) :
    (adicDerivFun D I x).val n = derivMod D I n (x.val (n + 1)) := rfl

end Adic

/-- A derivation `D` on a ring `R` extends, along the canonical map `R → AdicCompletion I R`, to a
derivation of the `I`-adic completion of `R`. -/
@[stacks 07PE "(1)"]
theorem exists_derivation_adicCompletion
    (R : Type*) [CommRing R] (D : Derivation ℤ R R) (I : Ideal R) :
    ∃ Dcompl : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      ExtendsAlong (algebraMap R (AdicCompletion I R)) D Dcompl := by
  let L : AdicCompletion I R →ₗ[ℤ] AdicCompletion I R :=
    { toFun := adicDerivFun D I
      map_add' x y := AdicCompletion.ext fun n => by
        simp only [adicDerivFun_val, AdicCompletion.val_add_apply, map_add]
      map_smul' z x := AdicCompletion.ext fun n => by
        simp only [adicDerivFun_val, AdicCompletion.val_smul_apply, RingHom.id_apply, map_smul] }
  have hleib : ∀ a b : AdicCompletion I R, L (a * b) = a • L b + b • L a := by
    intro a b
    apply AdicCompletion.ext
    intro n
    change (adicDerivFun D I (a * b)).val n
      = (a • adicDerivFun D I b + b • adicDerivFun D I a).val n
    simp only [smul_eq_mul, AdicCompletion.val_add_apply, AdicCompletion.val_mul, adicDerivFun_val]
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (a.val (n + 1))
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (b.val (n + 1))
    have han : a.val n = Submodule.Quotient.mk r := by
      have := a.property (Nat.le_succ n); rw [← this, ← hr]; rfl
    have hbn : b.val n = Submodule.Quotient.mk s := by
      have := b.property (Nat.le_succ n); rw [← this, ← hs]; rfl
    rw [← hr, ← hs, han, hbn]
    have hleib2 : D (r * s) = r * D s + s * D r := by
      rw [Derivation.leibniz]; simp only [smul_eq_mul]
    change Submodule.Quotient.mk (D (r * s))
      = Submodule.Quotient.mk r * Submodule.Quotient.mk (D s)
        + Submodule.Quotient.mk s * Submodule.Quotient.mk (D r)
    rw [hleib2]
    rfl
  exact ⟨Derivation.mk' L hleib, fun r => AdicCompletion.ext fun n => rfl⟩

/-! ### Clearing denominators for a finite type extension -/

section ClearDenominators

variable {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [Algebra.FiniteType R R']
  (D : Derivation ℤ R R) (g : R)
  (Rg : Type*) [CommRing Rg] [Algebra R Rg] [IsLocalization (Submonoid.powers g) Rg]
  (R'g : Type*) [CommRing R'g] [Algebra R' R'g]
  [IsLocalization (Submonoid.powers ((algebraMap R R') g)) R'g]
  (f : Rg →+* R'g)

/-- An injective ring hom out of `Rg` kills `locDeriv D (Submonoid.powers g) Rg` on its kernel. -/
lemma map_locDeriv_eq_zero (hf_inj : Function.Injective f) (y : Rg) (hy : f y = 0) :
    f (locDeriv D (Submonoid.powers g) Rg y) = 0 := by
  obtain rfl : y = 0 := hf_inj (by simpa using hy)
  simp

/-- The derivation of `R'g` obtained by transporting the extension of `D` to `Rg` along the
bijective ring hom `f : Rg →+* R'g`. -/
noncomputable def clearDenomDeriv (hf_iso : Function.Bijective f) : Derivation ℤ R'g R'g :=
  Derivation.liftOfSurjective (f := f.toIntAlgHom) hf_iso.surjective
    (d := locDeriv D (Submonoid.powers g) Rg)
    (map_locDeriv_eq_zero D g Rg R'g f hf_iso.injective)

/-- The derivation `clearDenomDeriv D g Rg R'g f hf_iso` sends `f (algebraMap R Rg r)` to
`f (algebraMap R Rg (D r))`. -/
lemma clearDenomDeriv_apply (hf_iso : Function.Bijective f) (r : R) :
    clearDenomDeriv D g Rg R'g f hf_iso (f (algebraMap R Rg r))
      = f (algebraMap R Rg (D r)) := by
  have key := Derivation.liftOfSurjective_apply (f := f.toIntAlgHom) hf_iso.surjective
    (d := locDeriv D (Submonoid.powers g) Rg)
    (map_locDeriv_eq_zero D g Rg R'g f hf_iso.injective) (algebraMap R Rg r)
  rw [locDeriv_algebraMap D (Submonoid.powers g) Rg r] at key
  exact key

/-- `clearDenomDeriv` sends the image of `r : R` in `R'g` to the image of `D r`. -/
private lemma clearDenomDeriv_algebraMap_algebraMap
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] (D : Derivation ℤ R R) (g : R)
    (Rg : Type*) [CommRing Rg] [Algebra R Rg] [IsLocalization (Submonoid.powers g) Rg]
    (R'g : Type*) [CommRing R'g] [Algebra R' R'g] (f : Rg →+* R'g)
    (hf_comm : f.comp (algebraMap R Rg) = (algebraMap R' R'g).comp (algebraMap R R'))
    (hf_iso : Function.Bijective f) (r : R) :
    clearDenomDeriv D g Rg R'g f hf_iso (algebraMap R' R'g (algebraMap R R' r))
      = algebraMap R' R'g (algebraMap R R' (D r)) := by
  have hcomm : ∀ r, algebraMap R' R'g (algebraMap R R' r) = f (algebraMap R Rg r) := fun r => by
    simpa using (RingHom.congr_fun hf_comm r).symm
  rw [hcomm, clearDenomDeriv_apply, hcomm]

/-- There is `N : ℕ` such that for every `y : R'`, the element
`g ^ N • clearDenomDeriv D g Rg R'g f hf_iso (algebraMap R' R'g y)` lies in the image of `R'`. -/
lemma exists_pow_smul_mem_range
    (hf_comm : f.comp (algebraMap R Rg) = (algebraMap R' R'g).comp (algebraMap R R'))
    (hf_iso : Function.Bijective f) :
    ∃ N : ℕ, ∀ y : R',
      ((algebraMap R R') g) ^ N • clearDenomDeriv D g Rg R'g f hf_iso (algebraMap R' R'g y)
        ∈ Set.range (algebraMap R' R'g) := by
  set Δg := clearDenomDeriv D g Rg R'g f hf_iso with hΔg
  set ιg := algebraMap R' R'g with hιg
  set g' := (algebraMap R R') g
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R R').FG)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers g') s
    (fun x => Δg (ιg x))
  obtain ⟨N, hN⟩ := b.property
  refine ⟨N, fun y => ?_⟩
  have hadd : ∀ a c : R'g, a ∈ Set.range ιg → c ∈ Set.range ιg → a + c ∈ Set.range ιg := by
    rintro a c ⟨a', rfl⟩ ⟨c', rfl⟩; exact ⟨a' + c', by rw [map_add]⟩
  have hsmul_mem : ∀ (w : R') (a : R'g), a ∈ Set.range ιg → ιg w • a ∈ Set.range ιg := by
    rintro w a ⟨a', rfl⟩
    exact ⟨w * a', by rw [map_mul, smul_eq_mul]⟩
  have hgen : y ∈ Algebra.adjoin R (↑s : Set R') := hs ▸ Algebra.mem_top
  induction hgen using Algebra.adjoin_induction with
  | mem x hx =>
      have h2 := hb x hx
      rw [← hN] at h2
      exact RingHom.mem_rangeS.mp h2
  | algebraMap r =>
      rw [hΔg, clearDenomDeriv_algebraMap_algebraMap D g Rg R'g f hf_comm hf_iso r]
      exact ⟨g' ^ N * (algebraMap R R') (D r), by rw [map_mul, Algebra.smul_def]⟩
  | add x z hx hz ih1 ih2 =>
      have he : g' ^ N • Δg (ιg (x + z)) = g' ^ N • Δg (ιg x) + g' ^ N • Δg (ιg z) := by
        rw [map_add, map_add, smul_add]
      rw [he]; exact hadd _ _ ih1 ih2
  | mul x z hx hz ih1 ih2 =>
      have he : g' ^ N • Δg (ιg (x * z))
          = ιg x • (g' ^ N • Δg (ιg z)) + ιg z • (g' ^ N • Δg (ιg x)) := by
        rw [map_mul, Δg.leibniz, smul_add, smul_comm (g' ^ N) (ιg x),
          smul_comm (g' ^ N) (ιg z)]
      rw [he]; exact hadd _ _ (hsmul_mem _ _ ih2) (hsmul_mem _ _ ih1)

end ClearDenominators

/-- Let `R'` be a finite type `R`-algebra and let `g ∈ R` be an element whose image in `R'` is a
nonzerodivisor, such that the induced map `f : R_g → R'_g` between the localizations at the powers
of `g` is bijective. Then for some `N : ℕ` the derivation `g ^ N • D` extends, along
`R → R'`, to a derivation of `R'`. -/
@[stacks 07PE "(3)"]
theorem exists_derivation_clear_denominators
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    [Algebra.FiniteType R R']
    (D : Derivation ℤ R R) (g : R)
    (Rg : Type*) [CommRing Rg] [Algebra R Rg]
    [IsLocalization (Submonoid.powers g) Rg]
    (R'g : Type*) [CommRing R'g] [Algebra R' R'g]
    [IsLocalization (Submonoid.powers ((algebraMap R R') g)) R'g]
    (f : Rg →+* R'g)
    (hf_comm : f.comp (algebraMap R Rg) = (algebraMap R' R'g).comp (algebraMap R R'))
    (hf_iso : Function.Bijective f)
    (hg_nzd : (algebraMap R R') g ∈ nonZeroDivisors R') :
    ∃ (N : ℕ) (Δ : Derivation ℤ R' R'),
      ExtendsAlong (algebraMap R R') (g ^ N • D) Δ := by
  set ιg := algebraMap R' R'g with hιg
  set Δg := clearDenomDeriv D g Rg R'g f hf_iso with hΔg
  set g' := (algebraMap R R') g with hg'
  have hιg_inj : Function.Injective ιg :=
    IsLocalization.injective R'g (Submonoid.powers_le.mpr hg_nzd)
  obtain ⟨N, hN⟩ := exists_pow_smul_mem_range D g Rg R'g f hf_comm hf_iso
  set Δ₀ : R' → R' := fun y => (hN y).choose
  have hspec : ∀ y : R', ιg (Δ₀ y) = g' ^ N • Δg (ιg y) := fun y => (hN y).choose_spec
  have hsmul : ∀ (w : R') (z : R'), (ιg w) • (ιg z) = ιg (w * z) := fun w z => by
    rw [smul_eq_mul, ← map_mul]
  have hadd : ∀ a b : R', Δ₀ (a + b) = Δ₀ a + Δ₀ b := by
    intro a b
    apply hιg_inj
    rw [hspec, map_add, map_add, map_add, smul_add, hspec, hspec]
  have hzsmul : ∀ (n : ℤ) (a : R'), Δ₀ (n • a) = n • Δ₀ a := by
    intro n a
    apply hιg_inj
    rw [hspec, map_zsmul ιg n (Δ₀ a), hspec, map_zsmul, map_zsmul, smul_comm]
  have hleib : ∀ a b : R', Δ₀ (a * b) = a • Δ₀ b + b • Δ₀ a := by
    intro a b
    apply hιg_inj
    rw [hspec, map_mul, map_add, Δg.leibniz, smul_add,
      smul_comm (g' ^ N) (ιg a), smul_comm (g' ^ N) (ιg b),
      ← hspec, ← hspec, hsmul a (Δ₀ b), hsmul b (Δ₀ a), smul_eq_mul, smul_eq_mul]
  let L : R' →ₗ[ℤ] R' :=
    { toFun := Δ₀
      map_add' := hadd
      map_smul' := fun n a => by simpa using hzsmul n a }
  let Δ : Derivation ℤ R' R' := Derivation.mk' L hleib
  refine ⟨N, Δ, fun r => ?_⟩
  have hΔeval : Δ (algebraMap R R' r) = Δ₀ (algebraMap R R' r) := rfl
  apply hιg_inj
  rw [hΔeval, hspec]
  rw [hΔg, clearDenomDeriv_algebraMap_algebraMap D g Rg R'g f hf_comm hf_iso r]
  change g' ^ N • ιg ((algebraMap R R') (D r)) = ιg ((algebraMap R R') ((g ^ N • D) r))
  rw [Algebra.smul_def (g' ^ N) (ιg ((algebraMap R R') (D r))), ← hιg, ← map_mul ιg]
  congr 1
  change g' ^ N * (algebraMap R R') (D r) = (algebraMap R R') ((g ^ N • D) r)
  rw [hg', ← map_pow, ← map_mul]
  congr 1

end Stacks.DerivationExtension
