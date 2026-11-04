module

public import StacksFrontier.RingTheory.Etale.PushoutLift.Section

/-!
# The composition of the lifted Čech groupoid

Given the second projection `s : Γ → Δ` and a copy `σ : Δ ≃+* D` of `Δ` whose `Γ`-algebra
structure is that of `s`, we construct the *composition* `m : Δ → Δ ⊗[Γ] D` with
`m ∘ s = s ⊗ 1` and `m ∘ t = 1 ⊗ σ ∘ t`.

It is the lift, along the nilpotent thickening `Δ ⊗[Γ] D → (Δ ⊗[Γ] D) ⧸ J`, of the map
`Δ₀ = Γ₀ ⊗[B₀] Γ₀ → (Δ ⊗[Γ] D) ⧸ J` sending `x ⊗ y` to the classes of `1 ⊗ σ(t x)` and
`s(y) ⊗ 1`, and it is `Γ`-linear for the structure `x ↦ 1 ⊗ σ(t x)` on the target (carried by a
copy `τ` of `Δ ⊗[Γ] D`), which is the identity `m ∘ t = 1 ⊗ σ ∘ t`.

## Main definitions

* `Stacks.Etale.PushoutLift.compositionBar`: the reduced composition `Δ₀ → T ⧸ J T`,
  `x ⊗ y ↦ ι₃ x · ι₂ y`.
* `Stacks.Etale.PushoutLift.composition`: the composition `Δ → T`, the lift of the reduced
  composition.

## Main results

* `Stacks.Etale.PushoutLift.composition_secondProjection`: the composition followed by the second
  projection is `s ⊗ 1`.

## References

* [Stacks Project, Tag 0ALT](https://stacks.math.columbia.edu/tag/0ALT)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.Etale.PushoutLift

variable {A : Type u} [CommRing A] (I J : Ideal A)
variable {Γ : Type u} [CommRing Γ] [Algebra A Γ]
variable {B₀ : Type u} [CommRing B₀] [Algebra A B₀]
variable {Γ₀ : Type u} [CommRing Γ₀] [Algebra A Γ₀] [Algebra Γ Γ₀] [IsScalarTower A Γ Γ₀]
  [Algebra B₀ Γ₀] [IsScalarTower A B₀ Γ₀]
variable {Δ : Type u} [CommRing Δ] [Algebra Γ Δ] [Algebra A Δ] [IsScalarTower A Γ Δ]
variable (ψ : Δ →ₐ[Γ] Γ₀ ⊗[B₀] Γ₀)
variable (hΓ₀ : Function.Surjective (algebraMap Γ Γ₀))
  (hΓ₀ker : RingHom.ker (algebraMap Γ Γ₀) = J.map (algebraMap A Γ))
variable (s : Γ →ₐ[A] Δ)
variable {D : Type u} [CommRing D] [Algebra Γ D] (σ : Δ ≃+* D)
  (hσ : ∀ x, σ (s x) = algebraMap Γ D x)
variable {T : Type u} [CommRing T] [Algebra Γ T] [Algebra A T] [IsScalarTower A Γ T]
  (τ : Δ ⊗[Γ] D ≃+* T) (hτ : ∀ x, τ (1 ⊗ₜ σ (algebraMap Γ Δ x)) = algebraMap Γ T x)

/-- A ring map out of `Γ` agreeing with `algebraMap Γ T` on `A` carries `J Γ` into the extension
of `J Γ` to `T`. -/
lemma map_le_of_comp_eq {X : Type*} [CommRing X] [Algebra A X] (φ : X →+* T)
    (hφ : ∀ a, φ (algebraMap A X a) = algebraMap A T a) :
    (J.map (algebraMap A X)).map φ ≤ (J.map (algebraMap A Γ)).map (algebraMap Γ T) := by
  rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    show φ.comp (algebraMap A X) = algebraMap A T from RingHom.ext hφ]

omit [IsScalarTower A Γ Δ] in
include hσ in
/-- `t(x) ⊗ 1 = 1 ⊗ σ(s x)` in `Δ ⊗[Γ] D`. -/
lemma algebraMap_tmul_one (x : Γ) :
    algebraMap Γ Δ x ⊗ₜ[Γ] (1 : D) = 1 ⊗ₜ σ (s x) := by
  rw [hσ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- The ring map `Δ → T`, `δ ↦ τ(δ ⊗ 1)`. -/
noncomputable def leftT : Δ →+* T :=
  τ.toRingHom.comp (Algebra.TensorProduct.includeLeft (R := Γ) (S := Γ) (A := Δ) (B := D))

/-- The ring map `Δ → T`, `δ ↦ τ(1 ⊗ σ δ)`. -/
noncomputable def rightT : Δ →+* T :=
  τ.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := Γ) (A := Δ) (B := D)).toRingHom.comp
    σ.toRingHom)

omit [Algebra Γ T] in
/-- `leftT τ d = τ (d ⊗ 1)`. -/
lemma leftT_apply (d : Δ) : leftT τ d = τ (d ⊗ₜ 1) := rfl

omit [Algebra Γ T] in
/-- `rightT σ τ d = τ (1 ⊗ σ d)`. -/
lemma rightT_apply (d : Δ) : rightT σ τ d = τ (1 ⊗ₜ σ d) := rfl

include hσ hτ in
/-- `leftT τ` is compatible with the `A`-algebra structures of `Δ` and `T`. -/
lemma leftT_algebraMap (a : A) : leftT τ (algebraMap A Δ a) = algebraMap A T a := by
  rw [leftT_apply, IsScalarTower.algebraMap_apply A Γ Δ, algebraMap_tmul_one s σ hσ,
    AlgHom.commutes s, IsScalarTower.algebraMap_apply A Γ Δ, hτ,
    ← IsScalarTower.algebraMap_apply]

include hτ in
/-- `rightT σ τ` is compatible with the `A`-algebra structures of `Δ` and `T`. -/
lemma rightT_algebraMap (a : A) : rightT σ τ (algebraMap A Δ a) = algebraMap A T a := by
  rw [rightT_apply, IsScalarTower.algebraMap_apply A Γ Δ, hτ, ← IsScalarTower.algebraMap_apply]

/-- The ring map `ι₂ : Γ → T`, `x ↦ τ(s x ⊗ 1)`. -/
noncomputable def iota2 : Γ →+* T := (leftT τ).comp s.toRingHom

omit [Algebra Γ T] [IsScalarTower A Γ Δ] [Algebra A T] in
/-- `iota2 s τ x = τ (s x ⊗ 1)`. -/
lemma iota2_apply (x : Γ) : iota2 s τ x = τ (s x ⊗ₜ 1) := rfl

include hσ hτ in
/-- `ι₂` is compatible with the `A`-algebra structures of `Γ` and `T`. -/
lemma iota2_algebraMap (a : A) : iota2 s τ (algebraMap A Γ a) = algebraMap A T a := by
  rw [iota2_apply, AlgHom.commutes, ← leftT_apply, leftT_algebraMap s σ hσ τ hτ]

section Composition

variable (hJ : IsNilpotent J)

/-- The ideal `J T`. -/
abbrev idealJT : Ideal T := (J.map (algebraMap A Γ)).map (algebraMap Γ T)

include hJ in
/-- The ideal `J T` is nilpotent when `J` is. -/
lemma isNilpotent_idealJT : IsNilpotent (idealJT (Γ := Γ) J (T := T)) := by
  rw [idealJT, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact isNilpotent_map_algebraMap hJ T

omit [Algebra A Γ₀] [IsScalarTower A Γ Γ₀] [Algebra A T] [IsScalarTower A Γ T] in
include hΓ₀ker in
/-- The kernel of `Γ → Γ₀` is contained in the kernel of `Γ → T → T ⧸ J T`. -/
lemma ker_le_iota3 : RingHom.ker (algebraMap Γ Γ₀) ≤
    RingHom.ker ((Ideal.Quotient.mk (idealJT (Γ := Γ) J (T := T))).comp (algebraMap Γ T)) := by
  rw [hΓ₀ker, ← RingHom.comap_ker, Ideal.mk_ker, ← Ideal.map_le_iff_le_comap]

omit [Algebra A Γ₀] [IsScalarTower A Γ Γ₀] in
include hσ hτ hΓ₀ker in
/-- The kernel of `Γ → Γ₀` is contained in the kernel of `ι₂ : Γ → T` followed by
`T → T ⧸ J T`. -/
lemma ker_le_iota2 : RingHom.ker (algebraMap Γ Γ₀) ≤
    RingHom.ker ((Ideal.Quotient.mk (idealJT (Γ := Γ) J (T := T))).comp (iota2 s τ)) := by
  rw [hΓ₀ker, ← RingHom.comap_ker, Ideal.mk_ker, ← Ideal.map_le_iff_le_comap]
  exact map_le_of_comp_eq J (iota2 s τ) (iota2_algebraMap s σ hσ τ hτ)

/-- `ι₃` reduced: `Γ₀ → T ⧸ J T`. -/
noncomputable def iota3Bar : Γ₀ →+* T ⧸ idealJT (Γ := Γ) J (T := T) :=
  (Ideal.Quotient.lift _ _ fun _ hx ↦ RingHom.mem_ker.mp (ker_le_iota3 J hΓ₀ker (T := T) hx)).comp
    (RingHom.quotientKerEquivOfSurjective hΓ₀).symm.toRingHom

/-- `ι₂` reduced: `Γ₀ → T ⧸ J T`. -/
noncomputable def iota2Bar : Γ₀ →+* T ⧸ idealJT (Γ := Γ) J (T := T) :=
  (Ideal.Quotient.lift _ _ fun _ hx ↦
    RingHom.mem_ker.mp (ker_le_iota2 J hΓ₀ker s σ hσ τ hτ hx)).comp
    (RingHom.quotientKerEquivOfSurjective hΓ₀).symm.toRingHom

omit [Algebra A Γ₀] [IsScalarTower A Γ Γ₀] [Algebra A T] [IsScalarTower A Γ T] in
/-- `iota3Bar` sends the image of `x : Γ` in `Γ₀` to the class of `algebraMap Γ T x`. -/
lemma iota3Bar_apply (x : Γ) :
    iota3Bar J hΓ₀ hΓ₀ker (T := T) (algebraMap Γ Γ₀ x) =
      Ideal.Quotient.mk _ (algebraMap Γ T x) := by
  simp [iota3Bar]

omit [Algebra A Γ₀] [IsScalarTower A Γ Γ₀] in
/-- `iota2Bar` sends the image of `x : Γ` in `Γ₀` to the class of `ι₂ x`. -/
lemma iota2Bar_apply (x : Γ) :
    iota2Bar J hΓ₀ hΓ₀ker s σ hσ τ hτ (algebraMap Γ Γ₀ x) =
      Ideal.Quotient.mk _ (iota2 s τ x) := by
  simp [iota2Bar]

variable [Algebra.FormallySmooth Γ Δ]
variable (hψker : RingHom.ker ψ = J.map (algebraMap A Δ))
  (hsψ : ∀ x, ψ (s x) = Algebra.TensorProduct.includeRight (algebraMap Γ Γ₀ x))

omit [Algebra A B₀] [Algebra A Γ₀] [IsScalarTower A Γ Γ₀] [IsScalarTower A B₀ Γ₀]
  [Algebra.FormallySmooth Γ Δ] in
include hσ hτ hψker hsψ in
/-- On elements of `Γ` reducing into the image of `B₀`, `ι₂` and `ι₃` agree modulo `J`. -/
lemma iota2_sub_iota3_mem (x : Γ) (β : B₀) (hx : algebraMap Γ Γ₀ x = algebraMap B₀ Γ₀ β) :
    iota2 s τ x - algebraMap Γ T x ∈ idealJT (Γ := Γ) J (T := T) := by
  have hst : s x - algebraMap Γ Δ x ∈ J.map (algebraMap A Δ) := by
    rw [← hψker, RingHom.mem_ker, map_sub, hsψ, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply, hx,
      Algebra.algebraMap_eq_smul_one β, TensorProduct.smul_tmul, sub_self]
  have heq : iota2 s τ x - algebraMap Γ T x =
      leftT τ (s x - algebraMap Γ Δ x) + rightT σ τ (s x - algebraMap Γ Δ x) := by
    rw [map_sub, map_sub, leftT_apply, leftT_apply, rightT_apply, rightT_apply, hτ,
      algebraMap_tmul_one s σ hσ, iota2_apply]
    abel
  rw [heq]
  exact add_mem
    (map_le_of_comp_eq J (Γ := Γ) (leftT τ) (leftT_algebraMap s σ hσ τ hτ)
      (Ideal.mem_map_of_mem _ hst))
    (map_le_of_comp_eq J (Γ := Γ) (rightT σ τ) (rightT_algebraMap σ τ hτ)
      (Ideal.mem_map_of_mem _ hst))

omit [Algebra A B₀] [IsScalarTower A B₀ Γ₀] [Algebra.FormallySmooth Γ Δ] [Algebra A Γ₀]
  [IsScalarTower A Γ Γ₀] in
include hσ hτ hψker hsψ in
/-- `iota2Bar` and `iota3Bar` agree on the image of `B₀` in `Γ₀`. -/
lemma iota2Bar_algebraMap (β : B₀) :
    iota2Bar J hΓ₀ hΓ₀ker s σ hσ τ hτ (algebraMap B₀ Γ₀ β) =
      iota3Bar J hΓ₀ hΓ₀ker (T := T) (algebraMap B₀ Γ₀ β) := by
  obtain ⟨x, hx⟩ := hΓ₀ (algebraMap B₀ Γ₀ β)
  rw [← hx, iota2Bar_apply, iota3Bar_apply, Ideal.Quotient.eq]
  exact iota2_sub_iota3_mem J ψ s σ hσ τ hτ hψker hsψ x β hx

/-- The `B₀`-algebra structure on `T ⧸ J T` through `ι₃`. -/
noncomputable abbrev quotAlgebra : Algebra B₀ (T ⧸ idealJT (Γ := Γ) J (T := T)) :=
  ((iota3Bar J hΓ₀ hΓ₀ker (T := T)).comp (algebraMap B₀ Γ₀)).toAlgebra

/-- **The reduced composition** `Δ₀ → T ⧸ J T`, `x ⊗ y ↦ ι₃ x · ι₂ y`. -/
noncomputable def compositionBar : Γ₀ ⊗[B₀] Γ₀ →+* T ⧸ idealJT (Γ := Γ) J (T := T) :=
  letI := quotAlgebra J hΓ₀ hΓ₀ker (T := T) (B₀ := B₀)
  (Algebra.TensorProduct.lift
    ({ iota3Bar J hΓ₀ hΓ₀ker (T := T) with commutes' := fun _ ↦ rfl } :
      Γ₀ →ₐ[B₀] T ⧸ idealJT (Γ := Γ) J (T := T))
    ({ iota2Bar J hΓ₀ hΓ₀ker s σ hσ τ hτ with
      commutes' := fun β ↦ iota2Bar_algebraMap J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hψker hsψ β } :
      Γ₀ →ₐ[B₀] T ⧸ idealJT (Γ := Γ) J (T := T))
    fun _ _ ↦ Commute.all _ _).toRingHom

omit [Algebra A B₀] [IsScalarTower A B₀ Γ₀] [Algebra.FormallySmooth Γ Δ] [Algebra A Γ₀]
  [IsScalarTower A Γ Γ₀] in
/-- The reduced composition sends `y ⊗ y'` to `ι₃ y · ι₂ y'`. -/
lemma compositionBar_tmul (y y' : Γ₀) :
    compositionBar J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hψker hsψ (y ⊗ₜ y') =
      iota3Bar J hΓ₀ hΓ₀ker (T := T) y * iota2Bar J hΓ₀ hΓ₀ker s σ hσ τ hτ y' := rfl

omit [Algebra A B₀] [IsScalarTower A B₀ Γ₀] [Algebra.FormallySmooth Γ Δ] [Algebra A Γ₀]
  [IsScalarTower A Γ Γ₀] in
/-- The reduced composition sends `ψ (algebraMap Γ Δ x)` to the class of `algebraMap Γ T x`. -/
lemma compositionBar_algebraMap (x : Γ) :
    compositionBar J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hψker hsψ (ψ (algebraMap Γ Δ x)) =
      Ideal.Quotient.mk _ (algebraMap Γ T x) := by
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, compositionBar_tmul,
    iota3Bar_apply, map_one, mul_one]

omit [Algebra A B₀] [IsScalarTower A B₀ Γ₀] [Algebra.FormallySmooth Γ Δ] [Algebra A Γ₀]
  [IsScalarTower A Γ Γ₀] in
/-- The reduced composition sends `ψ (s x)` to the class of `ι₂ x`. -/
lemma compositionBar_secondProjection (x : Γ) :
    compositionBar J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hψker hsψ (ψ (s x)) =
      Ideal.Quotient.mk _ (iota2 s τ x) := by
  rw [hsψ, Algebra.TensorProduct.includeRight_apply, compositionBar_tmul, map_one, one_mul,
    iota2Bar_apply]

/-- The reduced composition, as a map of `Γ`-algebras `Δ → T ⧸ J T` (`Γ` acting on `T` through
`ι₃`). -/
noncomputable def compositionBarAlgHom : Δ →ₐ[Γ] T ⧸ idealJT (Γ := Γ) J (T := T) :=
  { (compositionBar J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hψker hsψ).comp ψ.toRingHom with
    commutes' := fun x ↦ by
      change compositionBar J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hψker hsψ (ψ (algebraMap Γ Δ x)) = _
      rw [compositionBar_algebraMap]
      rfl }

/-- **The composition**, as a map of `Γ`-algebras `Δ → T`: the lift of the reduced composition. -/
noncomputable def composition : Δ →ₐ[Γ] T :=
  Algebra.FormallySmooth.lift (idealJT (Γ := Γ) J (T := T))
    (isNilpotent_idealJT J hJ)
    (compositionBarAlgHom J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hψker hsψ)

omit [Algebra A B₀] [IsScalarTower A B₀ Γ₀] [Algebra A Γ₀] [IsScalarTower A Γ Γ₀] in
/-- The composition reduces modulo `J T` to the reduced composition. -/
lemma mk_composition (d : Δ) :
    Ideal.Quotient.mk _ (composition J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hJ hψker hsψ d) =
      compositionBar J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hψker hsψ (ψ d) :=
  Algebra.FormallySmooth.mk_lift _ _ _ d

variable {ε : Δ} (hε : IsIdempotentElem ε) (hs1 : ∀ x, ε * s x = ε * algebraMap Γ Δ x)
  (hone : 1 - ε ∈ I.map (algebraMap A Δ) ⊔ J.map (algebraMap A Δ))
  (hΓU : ∀ (T : Type u) [CommRing T] [Algebra A T], I.map (algebraMap A T) = ⊤ →
    Algebra.FormallyEtale T (T ⊗[A] Γ))

/-- An `A`-algebra map carries `(I + J) X` into `(I + J) Y`. -/
lemma mem_sup_of_algHom {X Y : Type*} [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (f : X →ₐ[A] Y) {x : X} (hx : x ∈ I.map (algebraMap A X) ⊔ J.map (algebraMap A X)) :
    f x ∈ I.map (algebraMap A Y) ⊔ J.map (algebraMap A Y) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem_sup (mem_map_algebraMap_of_algHom I f hy)
    (mem_map_algebraMap_of_algHom J f hz)

/-- An `A`-algebra map carries `1 - x ∈ (I + J) X` to `1 - f x ∈ (I + J) Y`. -/
lemma one_sub_mem_sup_of_algHom {X Y : Type*} [CommRing X] [CommRing Y] [Algebra A X]
    [Algebra A Y] (f : X →ₐ[A] Y) {x : X}
    (hx : 1 - x ∈ I.map (algebraMap A X) ⊔ J.map (algebraMap A X)) :
    1 - f x ∈ I.map (algebraMap A Y) ⊔ J.map (algebraMap A Y) := by
  simpa only [map_sub, map_one] using mem_sup_of_algHom I J f hx

include hJ in
/-- If `1 - η ∈ (I + J) X` with `J` nilpotent, then `I` generates the unit ideal of
`X ⧸ (η)`. -/
lemma map_quotient_span_eq_top {X : Type*} [CommRing X] [Algebra A X] {η : X}
    (h : 1 - η ∈ I.map (algebraMap A X) ⊔ J.map (algebraMap A X)) :
    I.map (algebraMap A (X ⧸ Ideal.span {η})) = ⊤ := by
  have h' := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {η})) h
  have hq : (Ideal.Quotient.mk (Ideal.span {η})).comp (algebraMap A X) =
      algebraMap A (X ⧸ Ideal.span {η}) := rfl
  rw [Ideal.map_sup, Ideal.map_map, Ideal.map_map, hq, map_sub, map_one,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self η), sub_zero] at h'
  exact eq_top_of_sup_eq_top_of_isNilpotent (isNilpotent_map_algebraMap hJ _)
    ((Ideal.eq_top_iff_one _).mpr h')

omit [IsScalarTower A Γ Δ] [Algebra.FormallySmooth Γ Δ] in
include hσ hs1 in
/-- On the piece cut out by `ε ⊗ σ ε`, `s y ⊗ 1` agrees with `1 ⊗ σ (t y)`. -/
lemma tmul_one_mul_tmul_idempotent (y : Γ) :
    (s y ⊗ₜ[Γ] (1 : D)) * (ε ⊗ₜ σ ε) = (1 ⊗ₜ σ (algebraMap Γ Δ y)) * (ε ⊗ₜ σ ε) := by
  have h3 : s y * ε = algebraMap Γ Δ y * ε := by rw [mul_comm, hs1, mul_comm]
  calc (s y ⊗ₜ[Γ] (1 : D)) * (ε ⊗ₜ σ ε)
      = (algebraMap Γ Δ y * ε) ⊗ₜ σ ε := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, h3]
    _ = (algebraMap Γ Δ y ⊗ₜ[Γ] (1 : D)) * (ε ⊗ₜ σ ε) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    _ = (1 ⊗ₜ σ (s y)) * (ε ⊗ₜ σ ε) := by rw [algebraMap_tmul_one s σ hσ]
    _ = ε ⊗ₜ σ (s y * ε) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
    _ = (1 ⊗ₜ σ (algebraMap Γ Δ y)) * (ε ⊗ₜ σ ε) := by
        rw [h3, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]

omit [Algebra A B₀] [IsScalarTower A B₀ Γ₀] [Algebra A Γ₀] [IsScalarTower A Γ Γ₀] in
include hσ hτ hψker hsψ hε hs1 hone hΓU in
/-- **The composition followed by the second projection is `s ⊗ 1`.** -/
theorem composition_secondProjection (x : Γ) :
    composition J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hJ hψker hsψ (s x) = iota2 s τ x := by
  set m := composition J ψ hΓ₀ hΓ₀ker s σ hσ τ hτ hJ hψker hsψ
  set η := m ε * (leftT τ ε * rightT σ τ ε) with hηdef
  have hη : IsIdempotentElem η :=
    (hε.map m).mul ((hε.map (leftT τ)).mul (hε.map (rightT σ τ)))
  have h1 : 1 - η ∈ I.map (algebraMap A T) ⊔ J.map (algebraMap A T) := by
    rw [show 1 - η = (1 - m ε) + m ε * ((1 - leftT τ ε) + leftT τ ε * (1 - rightT σ τ ε)) by
      rw [hηdef]; ring]
    exact add_mem (one_sub_mem_sup_of_algHom I J (m.restrictScalars A) hone)
      (Ideal.mul_mem_left _ _ (add_mem
        (one_sub_mem_sup_of_algHom I J
          ({ leftT τ with commutes' := leftT_algebraMap s σ hσ τ hτ } : Δ →ₐ[A] T) hone)
        (Ideal.mul_mem_left _ _ (one_sub_mem_sup_of_algHom I J
          ({ rightT σ τ with commutes' := rightT_algebraMap σ τ hτ } : Δ →ₐ[A] T) hone))))
  have hext := algHom_ext_of_idempotent hη (hΓU _ (map_quotient_span_eq_top I J hJ h1))
    (idealJT (Γ := Γ) J (T := T)) (isNilpotent_idealJT J hJ)
    (f₁ := (m.restrictScalars A).comp s)
    (f₂ := ({ iota2 s τ with commutes' := iota2_algebraMap s σ hσ τ hτ } : Γ →ₐ[A] T))
    (fun y ↦ by
      rw [← Ideal.Quotient.eq]
      show Ideal.Quotient.mk _ (m (s y)) = Ideal.Quotient.mk _ (iota2 s τ y)
      rw [mk_composition, compositionBar_secondProjection])
    (fun y ↦ by
      show m (s y) * η = iota2 s τ y * η
      have e1 : m (s y) * m ε = algebraMap Γ T y * m ε := by
        rw [← map_mul, mul_comm, hs1, mul_comm, map_mul, AlgHom.commutes]
      have e2 : iota2 s τ y * (leftT τ ε * rightT σ τ ε) =
          algebraMap Γ T y * (leftT τ ε * rightT σ τ ε) := by
        rw [leftT_apply, rightT_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul, ← hτ, iota2_apply, ← map_mul, ← map_mul,
          tmul_one_mul_tmul_idempotent s σ hσ hs1]
      rw [hηdef]
      linear_combination (leftT τ ε * rightT σ τ ε) * e1 - m ε * e2)
  exact AlgHom.congr_fun hext x

end Composition

end Stacks.Etale.PushoutLift

end
