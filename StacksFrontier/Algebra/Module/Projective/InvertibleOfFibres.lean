module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocalizedFlatness

/-!
# Invertible modules from invertible fibres

Let `R → A` be a ring map, `k` a field over `R` with kernel `p` and `M` a finitely presented
`A`-module which is flat over `R`. If the fibre `(A ⊗_R k) ⊗_A M` is an invertible
`A ⊗_R k`-module, then `M` is free of rank one at every prime of `A` over `p`. A finitely presented
module which is free of rank one at every prime is invertible.

## Main results

* `Module.nontrivial_tensorProduct_of_ker_eq`: `K ⊗_R L ≠ 0` for fields `K`, `L` over `R` with the
  same kernel.
* `Module.nonempty_linearEquiv_of_isLocalRing_of_invertible_baseChange`: the local statement, for
  a local ring `B` over `R` whose closed point lies over the kernel of `R → k`.
* `Module.nonempty_linearEquiv_localizedModule_of_invertible_baseChange`: its form at a prime of
  `A`, for an arbitrary pushout `A' = A ⊗_R k`.
* `Module.invertible_of_forall_nonempty_linearEquiv_localizedModule`: a finitely presented module
  which is free of rank one at every prime is invertible.
-/

@[expose] public section

open TensorProduct IsLocalRing

universe u

namespace Module

/-- **Tensor products of fields with the same kernel do not vanish.** For fields `K` and `L`
which are `R`-algebras with the same kernel, `K ⊗_R L` is not the zero ring. -/
theorem nontrivial_tensorProduct_of_ker_eq {R K L : Type u} [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra R L]
    (h : RingHom.ker (algebraMap R K) = RingHom.ker (algebraMap R L)) :
    Nontrivial (K ⊗[R] L) := by
  let Q := R ⧸ RingHom.ker (algebraMap R K)
  let fK : Q →+* K := RingHom.kerLift (algebraMap R K)
  let fL : Q →+* L := Ideal.Quotient.lift _ (algebraMap R L) (fun a ha => by
    rw [h] at ha; exact ha)
  have hK : Function.Injective fK := RingHom.kerLift_injective _
  have hL : Function.Injective fL := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap R L a = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, h]
    exact hx
  let : Algebra Q K := fK.toAlgebra
  let : Algebra Q L := fL.toAlgebra
  have : IsScalarTower R Q K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R Q L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Nontrivial (K ⊗[Q] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain Q K L hK hL
  let : CompatibleSMul Q R K L := CompatibleSMul.isScalarTower
  exact (Algebra.TensorProduct.mapOfCompatibleSMul Q R R K L).toRingHom.domain_nontrivial

section Local

variable {R B k : Type u} [CommRing R] [CommRing B] [IsLocalRing B] [Algebra R B] [Field k]
  [Algebra R k] (hk : (maximalIdeal B).comap (algebraMap R B) = RingHom.ker (algebraMap R k))
include hk

/-- The tensor product over `R` of the residue field of `B` and `k` is not the zero ring. -/
theorem nontrivial_residueField_tensorProduct_of_comap_eq :
    Nontrivial (ResidueField B ⊗[R] k) := by
  refine nontrivial_tensorProduct_of_ker_eq ?_
  rw [← hk]
  ext r
  rw [RingHom.mem_ker, Ideal.mem_comap, IsScalarTower.algebraMap_apply R B (ResidueField B),
    ResidueField.algebraMap_eq, residue_eq_zero_iff]

/-- **The fibre at the closed point is a line.** If `(B ⊗_R k) ⊗_B M` is invertible over
`B ⊗_R k`, then `κ(B) ⊗_B M` has dimension one over `κ(B)`. -/
theorem finrank_residueField_tensorProduct_eq_one (M : Type u) [AddCommGroup M] [Module B M]
    [Module.Invertible (B ⊗[R] k) ((B ⊗[R] k) ⊗[B] M)] :
    finrank (ResidueField B) (ResidueField B ⊗[B] M) = 1 := by
  have := nontrivial_residueField_tensorProduct_of_comap_eq hk
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (ResidueField B ⊗[R] k)
  let F := (ResidueField B ⊗[R] k) ⧸ m
  let : Field F := Ideal.Quotient.field m
  let iκ : ResidueField B →ₐ[R] F :=
    (Ideal.Quotient.mkₐ R m).comp Algebra.TensorProduct.includeLeft
  let ik : k →ₐ[R] F := (Ideal.Quotient.mkₐ R m).comp Algebra.TensorProduct.includeRight
  let ψ : B ⊗[R] k →ₐ[R] F :=
    Algebra.TensorProduct.lift (iκ.comp (IsScalarTower.toAlgHom R B (ResidueField B))) ik
      (fun _ _ => Commute.all _ _)
  let : Algebra (B ⊗[R] k) F := ψ.toRingHom.toAlgebra
  have : IsScalarTower B (B ⊗[R] k) F := IsScalarTower.of_algebraMap_eq fun b => by
    show _ = ψ (b ⊗ₜ 1)
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  let e₁ : F ⊗[B ⊗[R] k] ((B ⊗[R] k) ⊗[B] M) ≃ₗ[F] F ⊗[B] M :=
    AlgebraTensorModule.cancelBaseChange B (B ⊗[R] k) F F M
  let e₂ : F ⊗[ResidueField B] (ResidueField B ⊗[B] M) ≃ₗ[F] F ⊗[B] M :=
    AlgebraTensorModule.cancelBaseChange B (ResidueField B) F F M
  have h₁ : finrank F (F ⊗[B ⊗[R] k] ((B ⊗[R] k) ⊗[B] M)) = 1 :=
    Module.Invertible.finrank_eq_one _ _
  rw [← Module.finrank_baseChange (R := F), e₂.finrank_eq, ← e₁.finrank_eq, h₁]

/-- **The local statement.** Let `B` be a local ring over `R` whose closed point lies over the
kernel of `R → k`, `k` a field, and `M` a finitely presented `B`-module flat over `R` such that
`(B ⊗_R k) ⊗_B M` is invertible over `B ⊗_R k`. Then `M` is free of rank one over `B`. -/
theorem nonempty_linearEquiv_of_isLocalRing_of_invertible_baseChange (M : Type u)
    [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
    [Module.FinitePresentation B M] [Module.Flat R M]
    [Module.Invertible (B ⊗[R] k) ((B ⊗[R] k) ⊗[B] M)] :
    Nonempty (M ≃ₗ[B] B) := by
  have h₁ := finrank_residueField_tensorProduct_eq_one hk M
  have : Nontrivial (ResidueField B ⊗[B] M) := Module.nontrivial_of_finrank_eq_succ h₁
  obtain ⟨v, hv⟩ := exists_ne (0 : ResidueField B ⊗[B] M)
  obtain ⟨m, rfl⟩ := TensorProduct.mk_surjective B M (ResidueField B)
    Ideal.Quotient.mk_surjective v
  have hspan : Submodule.span B {m} = ⊤ := by
    refine (map_tensorProduct_mk_eq_top (N := Submodule.span B {m})).1 ?_
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 h₁ w
    obtain ⟨b, rfl⟩ := residue_surjective c
    refine ⟨b • m, Submodule.smul_mem _ b (Submodule.mem_span_singleton_self m), ?_⟩
    show (1 : ResidueField B) ⊗ₜ[B] (b • m) = residue B b • ((1 : ResidueField B) ⊗ₜ[B] m)
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (ResidueField B) b, ResidueField.algebraMap_eq]
  let φ : B →ₗ[B] M := LinearMap.toSpanSingleton B M m
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hspan]
  let N := (B ⊗[R] k) ⊗[B] M
  let ψ : (B ⊗[R] k) →ₗ[B ⊗[R] k] N := LinearMap.toSpanSingleton (B ⊗[R] k) N (1 ⊗ₜ m)
  have hψ : Function.Surjective ψ := by
    intro n
    induction n using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero ψ⟩
    | tmul x y =>
      obtain ⟨b, rfl⟩ := hφ y
      refine ⟨x * algebraMap B (B ⊗[R] k) b, ?_⟩
      show (x * algebraMap B (B ⊗[R] k) b) • ((1 : B ⊗[R] k) ⊗ₜ[B] m) = x ⊗ₜ[B] (b • m)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add ψ a b⟩
  have hψinj : Function.Injective ψ := (Module.Invertible.bijective_of_surjective hψ).1
  let e : N ≃ₗ[R] M ⊗[R] k :=
    ((TensorProduct.comm B (B ⊗[R] k) M).restrictScalars R).trans
      ((AlgebraTensorModule.cancelBaseChange R B B M k).restrictScalars R)
  have he : ∀ x : B ⊗[R] k, e (ψ x) = (φ.restrictScalars R).rTensor k x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b c =>
      show e ((b ⊗ₜ[R] c) • ((1 : B ⊗[R] k) ⊗ₜ[B] m)) = (b • m) ⊗ₜ[R] c
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hinj : Function.Injective ((φ.restrictScalars R).rTensor k) := by
    intro x y hxy
    rw [← he, ← he] at hxy
    exact hψinj (e.injective hxy)
  let K := LinearMap.ker φ
  have hK₀ : Function.Injective ((K.subtype.restrictScalars R).rTensor k) := by
    have := LinearMap.lTensor_injective_of_exact_of_flat (φ.restrictScalars R) hφ
      (K.subtype.restrictScalars R) K.injective_subtype
      (LinearMap.exact_subtype_ker_map (φ.restrictScalars R)) k
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact this
  have hKk : Subsingleton (K ⊗[R] k) := by
    refine ⟨fun x y => hK₀ (hinj ?_)⟩
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have : (φ.restrictScalars R).comp (K.subtype.restrictScalars R) = 0 := by
      ext z; exact z.2
    rw [this, LinearMap.rTensor_zero]
    rfl
  have : Module.Finite B K := Module.Finite.iff_fg.2 (Module.FinitePresentation.fg_ker φ hφ)
  have hK : Subsingleton K := by
    by_contra hK
    rw [not_subsingleton_iff_nontrivial, ← not_subsingleton_iff_nontrivial,
      ← subsingleton_tensorProduct (R := B) (M := K), not_subsingleton_iff_nontrivial] at hK
    obtain ⟨w, hw⟩ := exists_ne (0 : ResidueField B ⊗[B] K)
    obtain ⟨f, hf⟩ := Projective.exists_dual_ne_zero (ResidueField B) hw
    have hfs : Function.Surjective f := fun c => ⟨(c / f w) • w, by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hf]⟩
    let g : K →ₗ[R] ResidueField B :=
      (f.restrictScalars R).comp ((TensorProduct.mk B (ResidueField B) K 1).restrictScalars R)
    have hg : Function.Surjective g := hfs.comp
      (TensorProduct.mk_surjective B K (ResidueField B) Ideal.Quotient.mk_surjective)
    have : Subsingleton (ResidueField B ⊗[R] k) :=
      (LinearMap.rTensor_surjective k hg).subsingleton
    have := nontrivial_residueField_tensorProduct_of_comap_eq hk
    exact not_subsingleton _ ‹_›
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  exact ⟨(LinearEquiv.ofBijective φ ⟨hφinj, hφ⟩).symm⟩

end Local

section Global

variable {R A k A' : Type u} [CommRing R] [CommRing A] [Algebra R A] [Field k] [Algebra R k]
  [CommRing A'] [Algebra A A'] [Algebra k A'] [Algebra R A'] [IsScalarTower R A A']
  [IsScalarTower R k A'] [Algebra.IsPushout R A k A']

/-- **The statement at a prime of `A`.** Let `A' = A ⊗_R k` for a field `k` over `R`, and let `M`
be a finitely presented `A`-module flat over `R` such that `A' ⊗_A M` is invertible over `A'`.
Then `M` is free of rank one at every prime `q` of `A` lying over the kernel of `R → k`. -/
theorem nonempty_linearEquiv_localizedModule_of_invertible_baseChange (M : Type u)
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [Module.FinitePresentation A M] [Module.Flat R M] [Module.Invertible A' (A' ⊗[A] M)]
    (q : Ideal A) [q.IsPrime]
    (hq : q.comap (algebraMap R A) = RingHom.ker (algebraMap R k)) :
    Nonempty (LocalizedModule q.primeCompl M ≃ₗ[Localization.AtPrime q]
      Localization.AtPrime q) := by
  let B := Localization.AtPrime q
  let C := B ⊗[R] k
  have hk : (maximalIdeal B).comap (algebraMap R B) = RingHom.ker (algebraMap R k) := by
    rw [IsScalarTower.algebraMap_eq R A B, ← Ideal.comap_comap]
    show Ideal.comap (algebraMap R A) ((maximalIdeal B).under A) = _
    rw [Localization.AtPrime.under_maximalIdeal, hq]
  have : Module.Flat R (LocalizedModule q.primeCompl M) :=
    Module.Flat.localizedModule_of_isScalarTower q.primeCompl
  let f : A →ₐ[R] C :=
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] C).comp (IsScalarTower.toAlgHom R A B)
  let g : k →ₐ[R] C := Algebra.TensorProduct.includeRight
  have H : ∀ x y, f x * g y = g y * f x := fun _ _ => Commute.all _ _
  let ρ : A' →ₐ[R] C := Algebra.pushoutDesc A' f g H
  let : Algebra A' C := ρ.toRingHom.toAlgebra
  have : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq fun a => by
    show _ = ρ (algebraMap A A' a)
    rw [Algebra.pushoutDesc_left A' f g H a]
    simp [f]
    rfl
  let e : C ⊗[A'] (A' ⊗[A] M) ≃ₗ[C] C ⊗[B] LocalizedModule q.primeCompl M :=
    (AlgebraTensorModule.cancelBaseChange A A' C C M).trans
      ((AlgebraTensorModule.cancelBaseChange A B C C M).symm.trans
        (AlgebraTensorModule.congr (LinearEquiv.refl C C)
          (LocalizedModule.equivTensorProduct q.primeCompl M).symm))
  have : Module.Invertible C (C ⊗[B] LocalizedModule q.primeCompl M) := .congr e
  exact nonempty_linearEquiv_of_isLocalRing_of_invertible_baseChange hk _

end Global

/-- **Free of rank one at every prime implies invertible.** A finitely presented module whose
localizations at all primes are free of rank one is invertible. -/
theorem invertible_of_forall_nonempty_linearEquiv_localizedModule {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (h : ∀ (q : Ideal A) [q.IsPrime],
      Nonempty (LocalizedModule q.primeCompl M ≃ₗ[Localization.AtPrime q] Localization.AtPrime q)) :
    Module.Invertible A M := by
  have : Module.Flat A M := Module.flat_of_localized_maximal M fun P _ => by
    obtain ⟨e⟩ := h P
    exact (Module.Flat.equiv_iff (e.restrictScalars A)).2 (IsLocalization.flat _ P.primeCompl)
  have : Module.Projective A M := Module.Flat.projective_of_finitePresentation
  refine invertible_of_finite_projective_rankAtStalk_one ?_
  funext p
  obtain ⟨e⟩ := h p.asIdeal
  rw [Module.rankAtStalk, e.finrank_eq, Module.finrank_self]
  rfl

end Module
