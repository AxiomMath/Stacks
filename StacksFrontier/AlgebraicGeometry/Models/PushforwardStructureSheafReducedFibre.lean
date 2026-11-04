module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructureDirectImage
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic

/-!
# Direct image of the structure sheaf along an isomorphism off a reduced divisor

Let `f : W ⟶ X` be a quasi-compact quasi-separated surjective morphism of schemes and let
`s ∈ Γ(X, 𝒪_X)` be a global function which is a nonzerodivisor on the sections of `𝒪_X` and whose
pullback is a nonzerodivisor on the sections of `𝒪_W`. Suppose that `f` is an isomorphism over the
locus `D(s)` where `s` is invertible and that the zero scheme `V(s)` of `s` is reduced, in the
sense that `Γ(X, U)/(s)` is reduced for every affine open `U`. Then `𝒪_X = f_*𝒪_W`.

This is the situation of a proper morphism of models over a discrete valuation ring with
uniformizer `π`: an isomorphism over the generic fibre `D(π)`, onto a model whose special fibre
`V(π)` is reduced. The argument is elementary and needs no normality. On an affine open `U` with
`A = Γ(X, U)` and `B = Γ(W, f⁻¹U)`, the map `A ⟶ B` becomes an isomorphism after inverting `s`, so
every `b ∈ B` has `sᵏ b ∈ A`; if `k > 0` then `a = sᵏ b` vanishes wherever `s` does, because `f` is
surjective, so `a` lies in the radical of `(s)`, hence in `(s)` itself since `A/(s)` is reduced,
and `k` can be lowered.

## Main results

* `Stacks.Models.bijective_of_bijective_localization_away`: the ring-theoretic core.
* `Stacks.Models.isIso_unitToPushforwardObjUnit_of_isReduced_quotient`: `𝒪_X = f_*𝒪_W`.

## References

* [Stacks Project, Section 0C2R](https://stacks.math.columbia.edu/tag/0C2R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Models

section Algebra

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A A'] [Algebra B B']

/-- If `s` is a nonzerodivisor, the localization map away from `s` is injective. -/
private theorem injective_algebraMap_away {R : Type u} [CommRing R] (s : R) (R' : Type u)
    [CommRing R'] [Algebra R R'] [IsLocalization.Away s R'] (hs : ∀ a : R, s * a = 0 → a = 0) :
    Function.Injective (algebraMap R R') :=
  IsLocalization.injective R' (M := Submonoid.powers s) (Submonoid.powers_le.mpr
    (mem_nonZeroDivisors_iff.mpr ⟨hs, fun y hy => hs y (by rwa [mul_comm])⟩))

/-- **The ring-theoretic core.** Let `φ : A ⟶ B` and `s ∈ A` with `s` and `φ s` nonzerodivisors,
such that `φ` becomes bijective after inverting `s`, and such that `φ a ∈ (φ s)` forces `a ∈ (s)`.
Then `φ` is bijective. -/
theorem bijective_of_bijective_localization_away (φ : A →+* B) (s : A)
    [IsLocalization.Away s A'] [IsLocalization.Away (φ s) B'] (φ' : A' →+* B')
    (hφ' : Function.Bijective φ')
    (hcomm : ∀ a, φ' (algebraMap A A' a) = algebraMap B B' (φ a))
    (hs : ∀ a : A, s * a = 0 → a = 0) (hφs : ∀ b : B, φ s * b = 0 → b = 0)
    (hdet : ∀ a : A, ∀ b : B, φ a = φ s * b → ∃ a', a = s * a') :
    Function.Bijective φ := by
  have hinjA := injective_algebraMap_away s A' hs
  have hinjB := injective_algebraMap_away (φ s) B' hφs
  refine ⟨fun a₁ a₂ h => hinjA (hφ'.1 (by rw [hcomm, hcomm, h])), fun b => ?_⟩
  -- every element of `B` is `φ a / (φ s)ᵏ`
  obtain ⟨a', ha'⟩ := hφ'.2 (algebraMap B B' b)
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) a'
  have hkey : φ a = φ s ^ k * b := by
    apply hinjB
    have h1 : φ' (IsLocalization.mk' A' a (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)) *
        φ' (algebraMap A A' (s ^ k)) = φ' (algebraMap A A' a) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [ha', hcomm, hcomm] at h1
    rw [map_mul, ← h1, mul_comm, map_pow]
  clear ha'
  induction k generalizing a with
  | zero => exact ⟨a, by simpa using hkey⟩
  | succ k ih =>
    obtain ⟨a', rfl⟩ := hdet a (φ s ^ k * b) (by rw [hkey, pow_succ']; ring)
    refine ih a' ?_
    have h0 : φ s * (φ a' - φ s ^ k * b) = 0 := by
      rw [map_mul] at hkey
      rw [mul_sub, hkey, pow_succ']
      ring
    exact sub_eq_zero.mp (hφs _ h0)

/-- In a ring `A` with `A/(s)` reduced, the radical of `(s)` is `(s)`. -/
theorem mem_span_singleton_of_mem_radical {s a : A} (hred : IsReduced (A ⧸ Ideal.span {s}))
    (ha : a ∈ (Ideal.span {s}).radical) : ∃ a', a = s * a' := by
  obtain ⟨n, hn⟩ := ha
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {s}) a) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
  have h0 := hnil.eq_zero
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨a', ha'⟩ := h0
  exact ⟨a', by rw [← ha', mul_comm]⟩

end Algebra

section Geometry

variable {W X : Scheme.{u}} (f : W ⟶ X)

/-- **`𝒪_X = f_*𝒪_W` for a morphism which is an isomorphism away from a reduced divisor.** Let
`f : W ⟶ X` be quasi-compact, quasi-separated and surjective and `s ∈ Γ(X, 𝒪_X)`, such that `s`
and `f^*s` are nonzerodivisors on all sections, `f` is an isomorphism over `D(s)`, and
`Γ(X, U)/(s)` is reduced for every affine open `U`. Then `𝒪_X ⟶ f_*𝒪_W` is an isomorphism. -/
theorem isIso_unitToPushforwardObjUnit_of_isReduced_quotient [QuasiCompact f] [QuasiSeparated f]
    [Surjective f] (s : Γ(X, ⊤))
    (hX : ∀ (U : X.Opens) (a : Γ(X, U)), X.presheaf.map (homOfLE le_top).op s * a = 0 → a = 0)
    (hW : ∀ (V : W.Opens) (b : Γ(W, V)),
      W.presheaf.map (homOfLE le_top).op (f.appTop s) * b = 0 → b = 0)
    (hiso : IsIso (f ∣_ X.basicOpen s))
    (hred : ∀ U : X.affineOpens,
      IsReduced (Γ(X, U) ⧸ Ideal.span {X.presheaf.map (homOfLE le_top).op s})) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  refine Scheme.Modules.isIso_of_isIso_app_affineOpens _ fun U => ?_
  set sU : Γ(X, U.1) := X.presheaf.map (homOfLE le_top).op s with hsU
  set φ : Γ(X, U.1) →+* Γ(W, f ⁻¹ᵁ U.1) := (f.app U.1).hom with hφ
  have hφs : φ sU = W.presheaf.map (homOfLE le_top).op (f.appTop s) := by
    simp only [hφ, hsU, Scheme.Hom.appTop]
    rw [← CommRingCat.comp_apply, f.naturality]
    rfl
  -- `f` is an isomorphism on sections over every open inside `D(s)`
  have hiso' : ∀ V' : X.Opens, V' ≤ X.basicOpen s → IsIso (f.app V') := fun V' hV' =>
    Stacks.PicFinite.isIso_app_of_le f hV'
  have hle : X.basicOpen sU ≤ X.basicOpen s := by
    rw [hsU, Scheme.basicOpen_res]
    exact inf_le_right
  -- localization on both sides
  have hloc₁ : IsLocalization.Away sU Γ(X, X.basicOpen sU) := U.2.isLocalization_basicOpen sU
  have hcpt : IsCompact (f ⁻¹ᵁ U.1 : Set W) :=
    QuasiCompact.isCompact_preimage (f := f) _ U.1.isOpen U.2.isCompact
  have : IsAffine U.1 := U.2
  have : QuasiSeparatedSpace (f ⁻¹ᵁ U.1) := quasiSeparatedSpace_of_quasiSeparated (f ∣_ U.1)
  have hqs : IsQuasiSeparated (f ⁻¹ᵁ U.1 : Set W) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ U.1).isOpen).mpr (by exact this)
  have hloc₂ : IsLocalization.Away (φ sU) Γ(W, W.basicOpen (φ sU)) :=
    isLocalization_basicOpen_of_qcqs hcpt hqs (φ sU)
  have hpre : f ⁻¹ᵁ X.basicOpen sU = W.basicOpen (φ sU) := Scheme.preimage_basicOpen f sU
  let φ' : Γ(X, X.basicOpen sU) →+* Γ(W, W.basicOpen (φ sU)) :=
    (f.app (X.basicOpen sU) ≫ W.presheaf.map (eqToHom hpre.symm).op).hom
  have hφ' : Function.Bijective φ' := by
    have := hiso' _ hle
    exact ConcreteCategory.bijective_of_isIso (f.app (X.basicOpen sU) ≫
      W.presheaf.map (eqToHom hpre.symm).op)
  have hcomm : ∀ a, φ' (algebraMap Γ(X, U.1) Γ(X, X.basicOpen sU) a) =
      algebraMap Γ(W, f ⁻¹ᵁ U.1) Γ(W, W.basicOpen (φ sU)) (φ a) := by
    intro a
    have key : X.presheaf.map (homOfLE (X.basicOpen_le sU)).op ≫ f.app (X.basicOpen sU) ≫
        W.presheaf.map (eqToHom hpre.symm).op =
        f.app U.1 ≫ W.presheaf.map (homOfLE (W.basicOpen_le (φ sU))).op := by
      rw [f.naturality_assoc, ← Functor.map_comp]
      rfl
    exact congrArg (fun g => g.hom a) key
  have hs : ∀ a : Γ(X, U.1), sU * a = 0 → a = 0 := hX U.1
  have hφs : ∀ b : Γ(W, f ⁻¹ᵁ U.1), φ sU * b = 0 → b = 0 := by
    intro b hb
    rw [hφs] at hb
    exact hW _ b hb
  have hdet : ∀ (a : Γ(X, U.1)) (b : Γ(W, f ⁻¹ᵁ U.1)), φ a = φ sU * b → ∃ a', a = sU * a' := by
    intro a b hab
    refine mem_span_singleton_of_mem_radical (hred U) ?_
    have hbo : X.basicOpen a ≤ X.basicOpen sU := by
      intro x hx
      obtain ⟨w, rfl⟩ := f.surjective x
      have hw : w ∈ f ⁻¹ᵁ X.basicOpen a := hx
      rw [Scheme.preimage_basicOpen] at hw
      change w ∈ W.basicOpen (φ a) at hw
      rw [hab, Scheme.basicOpen_mul] at hw
      have hw' : w ∈ f ⁻¹ᵁ X.basicOpen sU := by rw [hpre]; exact hw.1
      exact hw'
    have h := U.2.fromSpec_preimage_basicOpen a
    have h' := U.2.fromSpec_preimage_basicOpen sU
    have : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen sU := by
      rw [← h, ← h']
      exact Scheme.Hom.preimage_mono _ hbo
    exact (PrimeSpectrum.basicOpen_le_basicOpen_iff a sU).mp this
  have hbij := bijective_of_bijective_localization_away (A' := Γ(X, X.basicOpen sU))
    (B' := Γ(W, W.basicOpen (φ sU))) φ sU φ' hφ' hcomm hs hφs hdet
  have : IsIso (f.app U.1) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have h3 : IsIso ((forget₂ RingCat AddCommGrpCat).map
      ((forget₂ CommRingCat RingCat).map (f.app U.1))) := inferInstance
  exact h3

end Geometry

end Stacks.Models

end
