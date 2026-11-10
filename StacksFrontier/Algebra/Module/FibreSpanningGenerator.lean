module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generators of a finite module of rank one

Let `M` be a finite module over a commutative ring `A` and `s ∈ M` an element whose image in
every fibre `κ(p) ⊗ M` spans it. Then `s` generates `M`; if moreover `M` is projective with
one-dimensional fibres, `s` is a free generator.

## Main results

* `Module.subsingleton_of_forall_residueField`: a finite module with zero fibres is zero.
* `Module.isOpen_setOf_span_tmul_eq_top`: the locus where `1 ⊗ s` spans the fibre is open.
* `Module.span_singleton_eq_top_of_fibres`: an element spanning every fibre generates the module.
* `Module.injective_smul_of_fibres`: a generator of a finite projective module with
  one-dimensional fibres is a free generator.
-/

@[expose] public section

open TensorProduct

universe u

namespace Module

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

/-- A finite module all of whose fibres vanish is zero. -/
theorem subsingleton_of_forall_residueField [Module.Finite A M]
    (h : ∀ p : PrimeSpectrum A, Subsingleton (p.asIdeal.ResidueField ⊗[A] M)) :
    Subsingleton M := by
  rw [← Module.support_eq_empty_iff (R := A), Set.eq_empty_iff_forall_notMem]
  exact fun p hp => not_nontrivial_iff_subsingleton.2 (h p)
    ((Module.mem_support_iff_nontrivial_residueField_tensorProduct p).1 hp)

/-- If `1 ⊗ s` spans the fibre of `M` at `p`, the fibre of `M ⧸ A s` at `p` vanishes. -/
theorem subsingleton_tensor_quotient_of_span (s : M) (p : PrimeSpectrum A)
    (h : Submodule.span p.asIdeal.ResidueField {(1 : p.asIdeal.ResidueField) ⊗ₜ[A] s} = ⊤) :
    Subsingleton (p.asIdeal.ResidueField ⊗[A] (M ⧸ Submodule.span A {s})) := by
  set N := Submodule.span A {s}
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective p.asIdeal.ResidueField
    (Submodule.mkQ_surjective N) z
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (Submodule.eq_top_iff'.1 h w)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, LinearMap.lTensor_tmul,
    Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_span_singleton_self s),
    TensorProduct.tmul_zero]

/-- Conversely, if the fibre of `M ⧸ A s` at `p` vanishes, `1 ⊗ s` spans the fibre of `M`. -/
theorem span_of_subsingleton_tensor_quotient (s : M) (p : PrimeSpectrum A)
    (h : Subsingleton (p.asIdeal.ResidueField ⊗[A] (M ⧸ Submodule.span A {s}))) :
    Submodule.span p.asIdeal.ResidueField {(1 : p.asIdeal.ResidueField) ⊗ₜ[A] s} = ⊤ := by
  set N := Submodule.span A {s}
  set κ := p.asIdeal.ResidueField
  have hex := lTensor_exact κ (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)
  refine Submodule.eq_top_iff'.2 fun z => ?_
  obtain ⟨w, rfl⟩ := (hex z).1 (Subsingleton.elim _ _)
  induction w using TensorProduct.inductionOn with
  | tmul c n =>
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 n.2
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← ha, TensorProduct.tmul_smul]
    refine Submodule.smul_of_tower_mem _ a ?_
    rw [show c ⊗ₜ[A] s = c • ((1 : κ) ⊗ₜ[A] s) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- **The locus where `1 ⊗ s` spans the fibre of a finite module is open.** -/
theorem isOpen_setOf_span_tmul_eq_top [Module.Finite A M] (s : M) :
    IsOpen {p : PrimeSpectrum A |
      Submodule.span p.asIdeal.ResidueField {(1 : p.asIdeal.ResidueField) ⊗ₜ[A] s} = ⊤} := by
  have heq : {p : PrimeSpectrum A |
      Submodule.span p.asIdeal.ResidueField {(1 : p.asIdeal.ResidueField) ⊗ₜ[A] s} = ⊤} =
      (Module.support A (M ⧸ Submodule.span A {s}))ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff,
      Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact ⟨subsingleton_tensor_quotient_of_span s p, span_of_subsingleton_tensor_quotient s p⟩
  rw [heq, Module.support_eq_zeroLocus, isOpen_compl_iff]
  exact PrimeSpectrum.isClosed_zeroLocus _

/-- **An element spanning every fibre of a finite module generates it.** -/
theorem span_singleton_eq_top_of_fibres [Module.Finite A M] (s : M)
    (h : ∀ p : PrimeSpectrum A,
      Submodule.span p.asIdeal.ResidueField {(1 : p.asIdeal.ResidueField) ⊗ₜ[A] s} = ⊤) :
    Submodule.span A {s} = ⊤ :=
  Submodule.Quotient.subsingleton_iff.1 <| subsingleton_of_forall_residueField (A := A) fun p =>
    subsingleton_tensor_quotient_of_span s p (h p)

/-- In a one-dimensional vector space a nonzero vector spans. -/
theorem span_singleton_eq_top_of_finrank_eq_one {K V : Type u} [Field K] [AddCommGroup V]
    [Module K V] (h : Module.finrank K V = 1) {v : V} (hv : v ≠ 0) :
    Submodule.span K {v} = ⊤ := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ h
  exact Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hv, h])

/-- **An element of a finite projective module whose fibres are all one-dimensional, and which
generates it, is a free generator**: `a ↦ a • s` is injective. -/
theorem injective_smul_of_fibres [Module.Finite A M] [Module.Projective A M] (s : M)
    (hs : Submodule.span A {s} = ⊤)
    (h1 : ∀ p : PrimeSpectrum A, Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[A] M) = 1) :
    Function.Injective fun a : A => a • s := by
  let φ : A →ₗ[A] M := LinearMap.toSpanSingleton A M s
  have hφ : Function.Surjective φ := by
    rwa [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property φ LinearMap.id hφ
  let K := LinearMap.ker φ
  let ψ : A →ₗ[A] K := LinearMap.codRestrict K (LinearMap.id - σ ∘ₗ φ) fun a => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
      LinearMap.comp_apply, ← LinearMap.comp_apply φ σ, hσ, LinearMap.id_apply, sub_self]
  have hψ : ∀ x : K, ψ x = x := fun x => Subtype.ext (by
    change (x : A) - σ (φ x) = x
    rw [x.2, map_zero, sub_zero])
  have : Module.Finite A K := Module.Finite.of_surjective ψ fun x => ⟨x, hψ x⟩
  have hK : Subsingleton K := by
    refine subsingleton_of_forall_residueField (A := A) fun p => ?_
    let κ := p.asIdeal.ResidueField
    have hA : Module.finrank κ (κ ⊗[A] A) = 1 := by
      rw [(TensorProduct.AlgebraTensorModule.rid A κ κ).finrank_eq, Module.finrank_self]
    have : FiniteDimensional κ (κ ⊗[A] A) := Module.finite_of_finrank_eq_succ hA
    have : FiniteDimensional κ (κ ⊗[A] M) := Module.finite_of_finrank_eq_succ (h1 p)
    have hsurj : Function.Surjective (φ.baseChange κ) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact LinearMap.lTensor_surjective κ hφ
    have hinj : Function.Injective (φ.baseChange κ) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := φ.baseChange κ) (by rw [hA, h1 p])).2 hsurj
    refine subsingleton_of_forall_eq 0 fun z => ?_
    have hret : (ψ.baseChange κ) ((K.subtype.baseChange κ) z) = z := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        show ψ ∘ₗ K.subtype = LinearMap.id from LinearMap.ext hψ, LinearMap.baseChange_id,
        LinearMap.id_apply]
    have hcomp : (φ.baseChange κ) ((K.subtype.baseChange κ) z) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        show φ ∘ₗ K.subtype = 0 from LinearMap.ext fun x => x.2, LinearMap.baseChange_zero,
        LinearMap.zero_apply]
    rw [← hret, hinj (hcomp.trans (map_zero _).symm), map_zero]
  intro a b hab
  have hab' : φ (a - b) = 0 := (sub_smul a b s).trans (sub_eq_zero.2 hab)
  exact sub_eq_zero.1 (congrArg Subtype.val (Subsingleton.elim (⟨a - b, hab'⟩ : K) 0))

/-- A ring map to a field with kernel `P` factors through the residue field of `P`. -/
private theorem exists_residueField_lift {K : Type u} [Field K] (φ : A →+* K)
    {P : Ideal A} [P.IsPrime] (hp : RingHom.ker φ = P) :
    ∃ ψ : P.ResidueField →+* K, ∀ a, ψ (algebraMap A P.ResidueField a) = φ a :=
  ⟨Ideal.ResidueField.lift P φ hp.ge fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun h => hx (hp ▸ RingHom.mem_ker.2 h),
    Ideal.ResidueField.lift_algebraMap P φ _ _⟩

/-- **A vector surviving in the fibre at the kernel of a field point survives at the field
point**: if `φ : A → K` is a ring map to a field with kernel `𝔭`, and `1 ⊗ s ≠ 0` in
`κ(𝔭) ⊗_A M`, then `1 ⊗ s ≠ 0` in `K ⊗_A M`. -/
theorem tmul_ne_zero_of_ker {K : Type u} [Field K] (φ : A →+* K) (s : M) (p : PrimeSpectrum A)
    (hp : RingHom.ker φ = p.asIdeal) (hs : (1 : p.asIdeal.ResidueField) ⊗ₜ[A] s ≠ 0) :
    letI : Algebra A K := φ.toAlgebra
    (1 : K) ⊗ₜ[A] s ≠ 0 := by
  let : Algebra A K := φ.toAlgebra
  set P := p.asIdeal
  obtain ⟨ψ, hψ⟩ := exists_residueField_lift φ hp
  let : Algebra P.ResidueField K := ψ.toAlgebra
  have : IsScalarTower A P.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun a => (hψ a).symm
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A P.ResidueField K K M
  have he : e ((1 : K) ⊗ₜ[P.ResidueField] ((1 : P.ResidueField) ⊗ₜ[A] s)) = (1 : K) ⊗ₜ[A] s := by
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [← he]
  intro h0
  apply hs
  have h1 : ((Algebra.linearMap P.ResidueField K).rTensor (P.ResidueField ⊗[A] M))
      ((1 : P.ResidueField) ⊗ₜ[P.ResidueField] ((1 : P.ResidueField) ⊗ₜ[A] s)) = 0 := by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact e.injective (h0.trans (map_zero e).symm)
  have h3 := congrArg (TensorProduct.lid P.ResidueField (P.ResidueField ⊗[A] M))
    (Module.Flat.rTensor_preserves_injective_linearMap (Algebra.linearMap P.ResidueField K)
      ψ.injective (h1.trans (map_zero _).symm))
  rwa [TensorProduct.lid_tmul, one_smul, map_zero] at h3

/-- **A vector vanishing in the fibre at `𝔭` vanishes at every field point with kernel `𝔭`.** -/
theorem tmul_eq_zero_of_ker {K : Type u} [Field K] (φ : A →+* K) (s : M) (p : PrimeSpectrum A)
    (hp : RingHom.ker φ = p.asIdeal) (hs : (1 : p.asIdeal.ResidueField) ⊗ₜ[A] s = 0) :
    letI : Algebra A K := φ.toAlgebra
    (1 : K) ⊗ₜ[A] s = 0 := by
  let : Algebra A K := φ.toAlgebra
  set P := p.asIdeal
  obtain ⟨ψ, hψ⟩ := exists_residueField_lift φ hp
  let ψA : P.ResidueField →ₗ[A] K :=
    { toFun := ψ
      map_add' := map_add ψ
      map_smul' := fun a x => by
        rw [Algebra.smul_def, RingHom.id_apply, Algebra.smul_def, map_mul]
        rw [hψ]; rfl }
  have h := congrArg (ψA.rTensor M) hs
  rwa [LinearMap.rTensor_tmul, map_zero, show ψA 1 = 1 from map_one ψ] at h

end Module
