module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.RingTheory.Flat.EqualizerTensorExactNoetherian
public import StacksFrontier.RingTheory.SpreadingOut.AlgHomModel
import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange

/-!
# The equalizer sequence is exact as soon as it is exact on all fibres

Let `p₁ p₂ : C → D` be two maps of flat, finitely presented `A`-algebras. This file proves that
the equalizer sequence `0 → A → C → D` of `AlgHom.EqualizerTensorExact` is exact provided it is
exact after base change to the residue field `κ(𝔭)` of every prime `𝔭` of `A`
(`AlgHom.EqualizerTensorExact.of_residueField`). No Noetherian hypothesis is made on `A`.

For the chart algebras `C = Γ(U, 𝒪)`, `D = Γ(U ×_X U, 𝒪)` of an algebraic space `X` flat and of
finite presentation over `Spec A`, this says: if `κ(𝔭) = H⁰(X_{κ(𝔭)}, 𝒪)` for every `𝔭`, then
`A = H⁰(X, 𝒪)`.

The proof spreads `p₁, p₂` out to flat finite type algebras over a ring `A₀` of finite type over
`ℤ` (`Algebra.exists_flat_finiteType_model_algHom_pair`). Exactness on the fibres forces `C` to be
faithfully flat over `A`, so it suffices to prove exactness for the `C₀`-module `C = A ⊗_{A₀} C₀`;
by `AlgHom.EqualizerTensorExact.of_associatedPrimes` that reduces to the residue fields of the
associated primes of `C` over `C₀`. Each of these lies over an associated prime of the
`A₀`-module `A`, which is the contraction of a prime of `A`, so its residue field is reached from
a fibre of `A` by field extensions.
-/

@[expose] public section

open TensorProduct

universe u

/-! ### Associated primes under flat base change, for arbitrary modules -/

namespace Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
  [IsNoetherianRing S] [Module.Flat R S] {N : Type*} [AddCommGroup N] [Module R N]

/-- Over a Noetherian ring `R` and a flat Noetherian `R`-algebra `S`, every associated prime of
the `S`-module `S ⊗_R N` lies over an associated prime of the `R`-module `N`. No finiteness is
asked of `N`. -/
theorem comap_mem_associatedPrimes_lTensor {Q : Ideal S}
    (hQ : Q ∈ associatedPrimes S (S ⊗[R] N)) :
    Q.comap (algebraMap R S) ∈ associatedPrimes R N := by
  obtain ⟨hQp, z, hz⟩ := (isAssociatedPrime_iff (I := Q) (M := S ⊗[R] N)).mp hQ
  have hann (s : S) : s ∈ Q ↔ s • z = 0 := by
    rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot]
  -- `z` comes from a finitely generated submodule
  obtain ⟨N', hN', z', rfl⟩ : ∃ N' : Submodule R N, N'.FG ∧
      ∃ z' : S ⊗[R] N', N'.subtype.lTensor S z' = z := by
    clear hz hann
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨⊥, Submodule.fg_bot, 0, map_zero _⟩
    | tmul s n =>
      exact ⟨R ∙ n, Submodule.fg_span_singleton n,
        s ⊗ₜ (⟨n, Submodule.mem_span_singleton_self n⟩ : R ∙ n), rfl⟩
    | add x y hx hy =>
      obtain ⟨N₁, h₁, x₁, rfl⟩ := hx
      obtain ⟨N₂, h₂, x₂, rfl⟩ := hy
      refine ⟨N₁ ⊔ N₂, h₁.sup h₂, (Submodule.inclusion le_sup_left).lTensor S x₁ +
        (Submodule.inclusion le_sup_right).lTensor S x₂, ?_⟩
      rw [map_add, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
      rfl
  have : Module.Finite R N' := Module.Finite.iff_fg.mpr hN'
  have hinj : Function.Injective (N'.subtype.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  refine associatedPrimes.subset_of_injective (f := N'.subtype) Subtype.val_injective ?_
  refine Stacks.AssociatedPrimes.FlatBaseChange.associatedPrimes_tensorProduct_subset_of_flat
    (P := S) ?_
  refine (isAssociatedPrime_iff (I := Q.comap (algebraMap R S)) (M := S ⊗[R] N')).mpr
    ⟨Ideal.comap_isPrime _ _, z', ?_⟩
  ext r
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Ideal.mem_comap, hann,
    algebraMap_smul, ← map_smul]
  exact map_eq_zero_iff _ hinj

end Module

/-- An associated prime of the `R`-module underlying an `R`-algebra `A` is the contraction of a
prime of `A`. -/
theorem Ideal.exists_comap_eq_of_mem_associatedPrimes {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {q : Ideal R} (hq : q ∈ associatedPrimes R A) :
    ∃ P : Ideal A, P.IsPrime ∧ P.comap (algebraMap R A) = q := by
  obtain ⟨hqp, a, ha⟩ := hq
  set I : Ideal A := (⊥ : Submodule A A).colon {a}
  have hI : I.comap (algebraMap R A) = (⊥ : Submodule R A).colon {a} := by
    ext r
    simp [I, Submodule.mem_colon_singleton, Algebra.smul_def]
  have hcomap : I.comap (algebraMap R A) ≤ q := by
    rw [hI, ha]
    exact Ideal.le_radical
  have hdisj : Disjoint (I : Set A) (q.primeCompl.map (algebraMap R A)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨r, hr, rfl⟩
    exact hr (hcomap hx)
  obtain ⟨P, hP, hIP, hPdisj⟩ := Ideal.exists_le_prime_disjoint I _ hdisj
  refine ⟨P, hP, le_antisymm ?_ ?_⟩
  · intro r hr
    by_contra hrq
    exact Set.disjoint_left.mp hPdisj hr ⟨r, hrq, rfl⟩
  · rw [ha, ← hI, (Ideal.comap_isPrime _ P).radical_le_iff]
    exact Ideal.comap_mono hIP

namespace AlgHom

/-! ### Transport along a base change of the algebras -/

section Transport

variable {A₀ C₀ D₀ A C D : Type*} [CommRing A₀] [CommRing C₀] [CommRing D₀] [CommRing A]
  [CommRing C] [CommRing D] [Algebra A₀ A] [Algebra A₀ C₀] [Algebra A₀ D₀] [Algebra A C]
  [Algebra A D] [Algebra C₀ C] [Algebra D₀ D] [Algebra A₀ C] [Algebra A₀ D]
  [IsScalarTower A₀ A C] [IsScalarTower A₀ C₀ C] [IsScalarTower A₀ A D] [IsScalarTower A₀ D₀ D]
  [Algebra.IsPushout A₀ A C₀ C] [Algebra.IsPushout A₀ A D₀ D]

variable (A₀ C₀ A C) in
/-- For `C = A ⊗_{A₀} C₀` and an `A`-module `N`, the identification `N ⊗_{A₀} C₀ ≅ N ⊗_A C`,
`n ⊗ c ↦ n ⊗ c`. -/
noncomputable def tensorIsPushoutEquiv (N : Type*) [AddCommGroup N] [Module A N] [Module A₀ N]
    [IsScalarTower A₀ A N] : N ⊗[A₀] C₀ ≃ₗ[A₀] N ⊗[A] C :=
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ A A N C₀).symm ≪≫ₗ
    (Algebra.IsPushout.equiv (R := A₀) (S := A) (R' := C₀) (S' := C)).toLinearEquiv.lTensor
      N).restrictScalars A₀

/-- The equivalence `tensorIsPushoutEquiv` sends `n ⊗ c` to `n ⊗ algebraMap C₀ C c`. -/
@[simp]
theorem tensorIsPushoutEquiv_tmul {N : Type*} [AddCommGroup N] [Module A N] [Module A₀ N]
    [IsScalarTower A₀ A N] (n : N) (c : C₀) :
    tensorIsPushoutEquiv A₀ C₀ A C N (n ⊗ₜ c) = n ⊗ₜ algebraMap C₀ C c := by
  simp [tensorIsPushoutEquiv, Algebra.IsPushout.equiv_tmul]

variable {p₁ p₂ : C →ₐ[A] D} {q₁ q₂ : C₀ →ₐ[A₀] D₀}
  (h₁ : (IsScalarTower.toAlgHom A₀ D₀ D).comp q₁ =
    (p₁.restrictScalars A₀).comp (IsScalarTower.toAlgHom A₀ C₀ C))
  (h₂ : (IsScalarTower.toAlgHom A₀ D₀ D).comp q₂ =
    (p₂.restrictScalars A₀).comp (IsScalarTower.toAlgHom A₀ C₀ C))
include h₁ h₂

/-- **Transport.** If `C = A ⊗_{A₀} C₀`, `D = A ⊗_{A₀} D₀` and `p₁, p₂` are the base changes of
`q₁, q₂`, then for every `A`-module `N` the sequence for `p₁, p₂` is exact exactly when the
sequence for `q₁, q₂` is. -/
theorem equalizerTensorExact_iff_of_isPushout (N : Type*) [AddCommGroup N] [Module A N]
    [Module A₀ N] [IsScalarTower A₀ A N] :
    EqualizerTensorExact p₁ p₂ N ↔ EqualizerTensorExact q₁ q₂ N := by
  set eC := tensorIsPushoutEquiv A₀ C₀ A C N
  set eD := tensorIsPushoutEquiv A₀ D₀ A D N
  have hι (n : N) : eC (tmulOne A₀ C₀ N n) = tmulOne A C N n := by
    simp [eC]
  have hδ (x : N ⊗[A₀] C₀) : eD ((q₁.toLinearMap - q₂.toLinearMap).lTensor N x) =
      (p₁.toLinearMap - p₂.toLinearMap).lTensor N (eC x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul n c =>
      have e₁ := congrArg (fun φ => φ c) h₁
      have e₂ := congrArg (fun φ => φ c) h₂
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgHom.restrictScalars_apply]
        at e₁ e₂
      simp [eC, eD, e₁, e₂, map_sub]
  rw [equalizerTensorExact_iff_tmulOne, equalizerTensorExact_iff_tmulOne]
  refine and_congr ?_ ⟨fun h y hy => ?_, fun h x hx => ?_⟩
  · have : (tmulOne A C N : N → N ⊗[A] C) = eC ∘ tmulOne A₀ C₀ N := funext fun n => (hι n).symm
    rw [this]
    exact (EquivLike.comp_injective _ eC)
  · obtain ⟨n, hn⟩ := h (eC y) (by rw [← hδ, hy, map_zero])
    exact ⟨n, eC.injective (by rw [hι, hn])⟩
  · obtain ⟨y, rfl⟩ := eC.surjective x
    obtain ⟨n, hn⟩ := h y (eD.injective (by rw [hδ, hx, map_zero]))
    exact ⟨n, by rw [← hι, hn]⟩

end Transport

/-! ### Exactness on the fibres -/

section Fibres

/-- The sequence passes from the residue field of a prime `𝔓` of an `A₀`-algebra to the residue
field of its contraction, and from there to the residue field of every prime of another
`A₀`-algebra over that contraction. -/
theorem EqualizerTensorExact.residueField_of_comap_eq {A₀ C₀ D₀ : Type*} [CommRing A₀]
    [CommRing C₀] [CommRing D₀] [Algebra A₀ C₀] [Algebra A₀ D₀] {q₁ q₂ : C₀ →ₐ[A₀] D₀}
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A₀ A] [Algebra A₀ S] (P : Ideal A)
    [P.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hPQ : P.comap (algebraMap A₀ A) = Q.comap (algebraMap A₀ S))
    (h : EqualizerTensorExact q₁ q₂ P.ResidueField) :
    EqualizerTensorExact q₁ q₂ Q.ResidueField := by
  set q := Q.comap (algebraMap A₀ S)
  let : Algebra q.ResidueField P.ResidueField :=
    (Ideal.ResidueField.mapₐ q P (Algebra.ofId A₀ A) hPQ.symm).toRingHom.toAlgebra
  have : IsScalarTower A₀ q.ResidueField P.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((Ideal.ResidueField.mapₐ q P (Algebra.ofId A₀ A) hPQ.symm).commutes a).symm
  let : Algebra q.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.mapₐ q Q (Algebra.ofId A₀ S) rfl).toRingHom.toAlgebra
  have : IsScalarTower A₀ q.ResidueField Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((Ideal.ResidueField.mapₐ q Q (Algebra.ofId A₀ S) rfl).commutes a).symm
  have hq : EqualizerTensorExact q₁ q₂ q.ResidueField := h.of_faithfullyFlat (k := q.ResidueField)
  exact hq.of_flat

/-- **The equalizer sequence is exact as soon as it is exact on the fibres.** Let `p₁ p₂ : C → D`
be two maps of flat, finitely presented `A`-algebras. If the sequence `0 → κ(𝔭) → κ(𝔭) ⊗_A C →
κ(𝔭) ⊗_A D` is exact for every prime `𝔭` of `A`, then `0 → A → C → D` is exact. -/
theorem EqualizerTensorExact.of_residueField {A C D : Type u} [CommRing A] [CommRing C]
    [CommRing D] [Algebra A C] [Algebra A D] [Module.Flat A C] [Module.Flat A D]
    [Algebra.FinitePresentation A C] [Algebra.FinitePresentation A D] {p₁ p₂ : C →ₐ[A] D}
    (h : ∀ (P : Ideal A) [P.IsPrime], EqualizerTensorExact p₁ p₂ P.ResidueField) :
    EqualizerTensorExact p₁ p₂ A := by
  obtain ⟨A₀, C₀, D₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hA₀, hC₀, hD₀, hC₀f, hD₀f,
    hpC, hpD, q₁, q₂, h₁, h₂⟩ := Algebra.exists_flat_finiteType_model_algHom_pair p₁ p₂
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : IsNoetherianRing C₀ := Algebra.FiniteType.isNoetherianRing A₀ C₀
  have : Algebra.FiniteType C₀ (C₀ ⊗[A₀] C₀) := inferInstance
  have : IsNoetherianRing (C₀ ⊗[A₀] C₀) := Algebra.FiniteType.isNoetherianRing C₀ _
  -- the fibres, read over the model
  have hfib (P : Ideal A) [P.IsPrime] : EqualizerTensorExact q₁ q₂ P.ResidueField :=
    (equalizerTensorExact_iff_of_isPushout h₁ h₂ _).mp (h P)
  -- `C` is faithfully flat over `A`
  have : Module.FaithfullyFlat A C := by
    refine Module.FaithfullyFlat.of_comap_surjective fun P => ?_
    refine (PrimeSpectrum.nontrivial_iff_mem_rangeComap P).mp ?_
    have hinj := (h P.asIdeal).1
    refine ⟨⟨1 ⊗ₜ 1, 0, fun h0 => ?_⟩⟩
    have : (Algebra.linearMap A C).lTensor P.asIdeal.ResidueField (1 ⊗ₜ 1) =
        (Algebra.linearMap A C).lTensor P.asIdeal.ResidueField 0 := by
      simpa using h0
    have := hinj this
    have h1 : (TensorProduct.rid A P.asIdeal.ResidueField) (1 ⊗ₜ 1) = 0 := by
      rw [this, map_zero]
    simp at h1
  -- the sequence for the `C₀`-module `C`
  have hC : EqualizerTensorExact q₁ q₂ C := by
    refine EqualizerTensorExact.of_associatedPrimes fun Q _ hQ => ?_
    have : Algebra.IsPushout A₀ C₀ A C := Algebra.IsPushout.symm hpC
    have hQ' : Q ∈ associatedPrimes C₀ (C₀ ⊗[A₀] A) := by
      rwa [LinearEquiv.AssociatedPrimes.eq
        (Algebra.IsPushout.equiv (R := A₀) (S := C₀) (R' := A) (S' := C)).toLinearEquiv]
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_comap_eq_of_mem_associatedPrimes
      (Module.comap_mem_associatedPrimes_lTensor hQ')
    exact (hfib P).residueField_of_comap_eq P Q hPQ
  have hA : EqualizerTensorExact q₁ q₂ A := hC.of_faithfullyFlat (k := A)
  exact (equalizerTensorExact_iff_of_isPushout h₁ h₂ A).mpr hA

end Fibres

end AlgHom
