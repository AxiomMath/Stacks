module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleTorsionFree
public import StacksFrontier.Algebra.Module.RankOneSurjection
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingConstruction
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
import all StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift

/-!
# A local domain whose dualizing module is a quotient of a module of generic rank one

The last step of the proof of [Stacks, Tag 0BBV]: at a point `x` of the final blowup `X`, the
dualizing module `ω_{X,x}` is a quotient of `ω_A ⊗_A 𝒪_{X,x}`, and the quotient of the latter by
its torsion submodule is free of rank one because `X` dominates a blowup of `Spec A` in an ideal
isomorphic to `ω_A`. Since a dualizing module of a domain is torsion free ([Stacks, Tag 0AWK]),
`ω_{X,x}` is that free module of rank one, so `𝒪_{X,x}` is Gorenstein.

## Main results

* `Dualizing.isGorensteinLocalRing_of_linearEquiv`: a Noetherian local ring with a dualizing
  module isomorphic to the ring is Gorenstein.
* `Dualizing.isGorensteinLocalRing_of_surjective_of_quotient_torsion`: a Noetherian local domain
  with a dualizing module which is a quotient of a module `M` with `M ⧸ torsion ≅ B` is
  Gorenstein.
* `Dualizing.exists_linearEquiv_ideal_of_isDualizingRingModule`: a dualizing module of a
  Noetherian domain is isomorphic to a nonzero ideal (it is torsion free of rank one).
* `Dualizing.isGorensteinLocalRing_of_surjective_tensor_of_linearEquiv_ideal`: the combination.
* `Dualizing.nonempty_quotient_torsion_tensor_ideal`: for an ideal `J ≠ 0` of a domain `A` and an
  injective map of domains `A ⟶ C` along which `J` becomes principal, `(J ⊗_A C) ⧸ torsion ≅ C`.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0AWK](https://stacks.math.columbia.edu/tag/0AWK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance 5000] HasDerivedCategory.standard

universe u

namespace Dualizing

section Gorenstein

variable {B : Type u} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]

/-- A dualizing module, placed in degree zero, is a dualizing complex: it is a dualizing complex
placed in some degree `n`, and the shift by `n` moves it to degree zero. -/
private theorem isDualizingComplex_single_zero {R : Type u} [CommRing R] [IsNoetherianRing R]
    {ω : Type u} [AddCommGroup ω] [Module R ω]
    (hω : Stacks.Duality.IsDualizingRingModule R ω) :
    IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R ω)) := by
  obtain ⟨-, n, hn⟩ := hω
  exact isDualizingComplex_of_iso
    (((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso n 0 n (add_zero n)).app _)
    (isDualizingComplex_shift _ hn n)

/-- **A Noetherian local ring with a dualizing module isomorphic to the ring is Gorenstein.**
The ring placed in the degree of the dualizing module is a dualizing complex, and so is every
shift of it. -/
theorem isGorensteinLocalRing_of_linearEquiv {ω : Type u} [AddCommGroup ω] [Module B ω]
    (hω : Stacks.Duality.IsDualizingRingModule B ω) (e : ω ≃ₗ[B] B) :
    IsGorensteinLocalRing B := by
  exact isDualizingComplex_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso e.toModuleIso)
    (isDualizingComplex_single_zero hω)

/-- **A Noetherian local domain whose dualizing module is a quotient of a module of generic rank
one with free torsion-free part is Gorenstein.** The dualizing module `ω` is torsion free
([Stacks, Tag 0AWK]), so the surjection `M ⟶ ω` factors through `M ⧸ torsion ≅ B`, and a
surjection from a free module of rank one onto a nonzero torsion-free module is an isomorphism. -/
theorem isGorensteinLocalRing_of_surjective_of_quotient_torsion [IsDomain B]
    {M ω : Type u} [AddCommGroup M] [Module B M] [AddCommGroup ω] [Module B ω]
    (hω : Stacks.Duality.IsDualizingRingModule B ω) (π : M →ₗ[B] ω)
    (hπ : Function.Surjective π) (e : (M ⧸ Submodule.torsion B M) ≃ₗ[B] B) :
    IsGorensteinLocalRing B := by
  have : Module.IsTorsionFree B ω := Stacks.Duality.IsDualizingRingModule.isTorsionFree hω
  have : Nontrivial ω :=
    Stacks.Duality.IsDualizingRingModule.nontrivial (M := ModuleCat.of B ω) hω
  have hle : Submodule.torsion B M ≤ LinearMap.ker π := by
    rintro m ⟨⟨r, hr⟩, hrm⟩
    rw [LinearMap.mem_ker]
    refine (smul_eq_zero_iff_right (nonZeroDivisors.ne_zero hr)).1 ?_
    rw [← map_smul]
    exact (congrArg π hrm).trans (map_zero π)
  let πbar : (M ⧸ Submodule.torsion B M) →ₗ[B] ω := (Submodule.torsion B M).liftQ π hle
  let φ : B →ₗ[B] ω := πbar ∘ₗ e.symm.toLinearMap
  have hφ : Function.Surjective φ := by
    intro w
    obtain ⟨m, rfl⟩ := hπ w
    exact ⟨e (Submodule.Quotient.mk m), by simp [φ, πbar]⟩
  have hbij := LinearMap.bijective_of_surjective_of_finrank_eq_one (Module.finrank_self B) φ hφ
  exact isGorensteinLocalRing_of_linearEquiv hω (LinearEquiv.ofBijective φ hbij).symm

end Gorenstein

section Torsion

variable {A C : Type u} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C] [Algebra A C]

/-- The multiplication map `C ⊗_A J ⟶ C`, `c ⊗ j ↦ c j`, for an ideal `J` of `A`. -/
def idealTensorMul (J : Ideal A) : C ⊗[A] J →ₗ[C] C :=
  LinearMap.liftBaseChange C ((Algebra.linearMap A C).comp J.subtype)

omit [IsDomain A] [IsDomain C] in
/-- The map `idealTensorMul J` sends `c ⊗ j` to `c j`. -/
theorem idealTensorMul_tmul (J : Ideal A) (c : C) (j : J) :
    idealTensorMul J (c ⊗ₜ j) = c * algebraMap A C j := by
  simp [idealTensorMul, LinearMap.liftBaseChange_tmul, smul_eq_mul]

omit [IsDomain A] [IsDomain C] in
/-- Multiplying by `j₀ ∈ J` is tensoring the product with `j₀`. -/
theorem algebraMap_smul_eq_idealTensorMul_tmul (J : Ideal A) (j₀ : J) (z : C ⊗[A] J) :
    algebraMap A C j₀ • z = idealTensorMul J z ⊗ₜ j₀ := by
  induction z with
  | tmul c j =>
    rw [idealTensorMul_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    have e1 : (algebraMap A C (j₀ : A) * c) ⊗ₜ[A] j = c ⊗ₜ[A] ((j₀ : A) • j) := by
      rw [← TensorProduct.smul_tmul, Algebra.smul_def]
    have e2 : c ⊗ₜ[A] ((j₀ : A) • j) = (c * algebraMap A C (j : A)) ⊗ₜ[A] j₀ := by
      have : (j₀ : A) • j = (j : A) • j₀ := by
        ext
        simp [mul_comm]
      rw [this, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
    rw [e1, e2]
  | add z w hz hw => rw [smul_add, hz, hw, map_add, TensorProduct.add_tmul]

omit [IsDomain A] in
/-- **The kernel of `C ⊗_A J ⟶ C` is the torsion submodule**, for a nonzero ideal `J` and an
injective map of domains `A ⟶ C`: a nonzero `j₀ ∈ J` kills the kernel. -/
theorem ker_idealTensorMul (hinj : Function.Injective (algebraMap A C)) (J : Ideal A)
    (hJ : J ≠ ⊥) : LinearMap.ker (idealTensorMul (C := C) J) = Submodule.torsion C (C ⊗[A] J) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨j₀, hj₀J, hj₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    have hne : algebraMap A C j₀ ≠ 0 := by
      rw [← map_zero (algebraMap A C)]
      exact fun h => hj₀ (hinj h)
    refine ⟨⟨algebraMap A C j₀, mem_nonZeroDivisors_of_ne_zero hne⟩, ?_⟩
    change algebraMap A C ((⟨j₀, hj₀J⟩ : J) : A) • z = 0
    rw [algebraMap_smul_eq_idealTensorMul_tmul, LinearMap.mem_ker.mp hz, TensorProduct.zero_tmul]
  · intro z hz
    obtain ⟨⟨r, hr⟩, hrz⟩ := hz
    rw [LinearMap.mem_ker]
    refine (smul_eq_zero_iff_right (nonZeroDivisors.ne_zero hr)).1 ?_
    rw [← map_smul]
    exact (congrArg (idealTensorMul J) hrz).trans (map_zero _)

omit [IsDomain A] [IsDomain C] in
/-- The image of `C ⊗_A J ⟶ C` is the extended ideal `J C`. -/
theorem range_idealTensorMul (J : Ideal A) :
    LinearMap.range (idealTensorMul (C := C) J) =
      (Ideal.map (algebraMap A C) J : Submodule C C) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z with
    | tmul c j =>
      rw [idealTensorMul_tmul]
      exact Ideal.mul_mem_left _ c (Ideal.mem_map_of_mem _ j.2)
    | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  · change Ideal.map (algebraMap A C) J ≤ LinearMap.range (idealTensorMul (C := C) J)
    rw [Ideal.map, Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨1 ⊗ₜ ⟨j, hj⟩, by rw [idealTensorMul_tmul, one_mul]⟩

omit [IsDomain A] in
/-- **If a nonzero ideal `J` becomes principal along an injective map of domains `A ⟶ C`, then
`(C ⊗_A J) ⧸ torsion` is free of rank one.** This is how domination of the blowup of `Spec A` in
`J` makes the strict transform of `J` invertible, read at a local ring. -/
theorem nonempty_quotient_torsion_tensor_ideal (hinj : Function.Injective (algebraMap A C))
    (J : Ideal A) (hJ : J ≠ ⊥) (t : C) (ht : Ideal.map (algebraMap A C) J = Ideal.span {t}) :
    Nonempty (((C ⊗[A] J) ⧸ Submodule.torsion C (C ⊗[A] J)) ≃ₗ[C] C) := by
  have ht0 : t ≠ 0 := by
    intro h0
    have hbot : Ideal.map (algebraMap A C) J = ⊥ := by rw [ht, h0, Ideal.span_singleton_eq_bot]
    obtain ⟨j₀, hj₀J, hj₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    have : algebraMap A C j₀ = 0 := by
      rw [← Ideal.mem_bot, ← hbot]; exact Ideal.mem_map_of_mem _ hj₀J
    exact hj₀ (hinj (this.trans (map_zero _).symm))
  have hrange : LinearMap.range (idealTensorMul (C := C) J) = Submodule.span C {t} := by
    rw [range_idealTensorMul, ht]
  let e1 : ((C ⊗[A] J) ⧸ Submodule.torsion C (C ⊗[A] J)) ≃ₗ[C]
      ((C ⊗[A] J) ⧸ LinearMap.ker (idealTensorMul (C := C) J)) :=
    Submodule.quotEquivOfEq _ _ (ker_idealTensorMul hinj J hJ).symm
  let e2 := LinearMap.quotKerEquivRange (idealTensorMul (C := C) J)
  let e3 : LinearMap.range (idealTensorMul (C := C) J) ≃ₗ[C] Submodule.span C {t} :=
    LinearEquiv.ofEq _ _ hrange
  let e4 : Submodule.span C {t} ≃ₗ[C] C := (LinearEquiv.toSpanNonzeroSingleton C C t ht0).symm
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

/-- **The last step of [Stacks, Tag 0BBV] at a local ring.** Let `A ⟶ B` be an injective map from
a domain to a Noetherian local domain, `J ≠ 0` an ideal of `A` with `J B` principal, and `ω` an
`A`-module isomorphic to `J` (the dualizing module of `A`, which has rank one). If a dualizing
module of `B` is a quotient of `B ⊗_A ω`, then `B` is Gorenstein: the torsion-free quotient of
`B ⊗_A ω ≅ B ⊗_A J` is free of rank one. -/
theorem isGorensteinLocalRing_of_surjective_tensor_of_linearEquiv_ideal
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    (J : Ideal A) (hJ : J ≠ ⊥) (t : B) (ht : Ideal.map (algebraMap A B) J = Ideal.span {t})
    {ω : Type u} [AddCommGroup ω] [Module A ω] (eJ : ω ≃ₗ[A] J)
    {ωB : Type u} [AddCommGroup ωB] [Module B ωB]
    (hωB : Stacks.Duality.IsDualizingRingModule B ωB) (π : B ⊗[A] ω →ₗ[B] ωB)
    (hπ : Function.Surjective π) : IsGorensteinLocalRing B := by
  obtain ⟨e⟩ := nonempty_quotient_torsion_tensor_ideal hinj J hJ t ht
  let eT : B ⊗[A] J ≃ₗ[B] B ⊗[A] ω := (LinearEquiv.baseChange A B _ _ eJ).symm
  refine isGorensteinLocalRing_of_surjective_of_quotient_torsion hωB (π ∘ₗ eT.toLinearMap) ?_ e
  intro w
  obtain ⟨z, rfl⟩ := hπ w
  exact ⟨eT.symm z, by simp⟩

end Torsion

section RankOne

/-- **Over a field, a module which in degree zero is a simple object of the derived category is
a line.** A line `W` inside it is a split subobject, so its inclusion stays a nonzero monomorphism
in the derived category, hence an isomorphism; the single-degree functor reflects isomorphisms. -/
theorem finrank_eq_one_of_simple_single {K : Type u} [Field K] (V : ModuleCat.{u} K)
    [Simple ((DerivedCategory.singleFunctor (ModuleCat.{u} K) 0).obj V)] :
    Module.finrank K V = 1 := by
  classical
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} K) 0
  have hnt : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact Simple.not_isZero (F.obj V) (F.map_isZero (ModuleCat.isZero_of_subsingleton V))
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let W : Submodule K V := K ∙ v
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective W.subtype (by simp)
  let ι : ModuleCat.of K W ⟶ V := ModuleCat.ofHom W.subtype
  have hsplit : ι ≫ ModuleCat.ofHom r = 𝟙 _ := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hr x)
  have : IsSplitMono (F.map ι) :=
    ⟨⟨⟨F.map (ModuleCat.ofHom r), by rw [← F.map_comp, hsplit, F.map_id]⟩⟩⟩
  have hne : F.map ι ≠ 0 := by
    intro h
    have h0 : ι = 0 := F.map_injective (by rw [h, F.map_zero])
    have := congrArg (fun f => f.hom ⟨v, Submodule.mem_span_singleton_self v⟩) h0
    exact hv (by simpa [ι] using this)
  have : IsIso (F.map ι) := (Simple.mono_isIso_iff_nonzero (F.map ι)).2 hne
  have : IsIso ι := isIso_of_fully_faithful F ι
  have hsurj : Function.Surjective W.subtype := (ConcreteCategory.bijective_of_isIso ι).2
  have htop : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨w, rfl⟩ := hsurj x
    exact w.2
  rw [← finrank_top K V, ← htop]
  exact finrank_span_singleton hv

/-- **A dualizing module of a Noetherian domain has rank one**: its localization at the generic
point is a dualizing module of the fraction field, hence a simple object of the derived category
of the fraction field, hence a line. -/
theorem finrank_localizedModule_eq_one_of_isDualizingRingModule {A : Type u} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] {ω : Type u} [AddCommGroup ω] [Module A ω]
    (hω : Stacks.Duality.IsDualizingRingModule A ω) :
    Module.finrank (FractionRing A) (LocalizedModule (nonZeroDivisors A) ω) = 1 := by
  let M := ModuleCat.of A ω
  have hM := isDualizingComplex_single_zero hω
  let B := FractionRing A
  have hflat : (algebraMap A B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B (nonZeroDivisors A))
  let : (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).Additive :=
    extendScalars_additive.{u, u} _
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
  let : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} _).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hext := isDualizingComplex_extendScalars_of_isLocalization (B := B) (nonZeroDivisors A) _ hM
  have hMp : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
      (ModuleCat.of B (LocalizedModule (nonZeroDivisors A) ω))) :=
    isDualizingComplex_of_iso
      (Stacks.Duality.mapDerivedCategorySingleZeroIso _ M ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso
          (extensionLocalizationIso.{u, u} (nonZeroDivisors A) M)) hext
  have := simple_of_isDualizingComplex_field.{u, 0} _ hMp
  exact finrank_eq_one_of_simple_single (ModuleCat.of B (LocalizedModule (nonZeroDivisors A) ω))

/-- **A dualizing module of a Noetherian domain is isomorphic to a nonzero ideal.** It is
torsion free ([Stacks, Tag 0AWK]) and of rank one, so it embeds into the fraction field; being
finite, a common denominator moves it into the ring. -/
theorem exists_linearEquiv_ideal_of_isDualizingRingModule {A : Type u} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] {ω : Type u} [AddCommGroup ω] [Module A ω]
    (hω : Stacks.Duality.IsDualizingRingModule A ω) :
    ∃ J : Ideal A, J ≠ ⊥ ∧ Nonempty (ω ≃ₗ[A] J) := by
  classical
  let S := nonZeroDivisors A
  let K := FractionRing A
  have h1 := finrank_localizedModule_eq_one_of_isDualizingRingModule hω
  have : Module.IsTorsionFree A ω := Stacks.Duality.IsDualizingRingModule.isTorsionFree hω
  have : Module.Finite A ω := hω.1
  have : FiniteDimensional K (LocalizedModule S ω) := Module.finite_of_finrank_eq_succ h1
  let e : LocalizedModule S ω ≃ₗ[K] K :=
    LinearEquiv.ofFinrankEq _ _ (h1.trans (Module.finrank_self K).symm)
  let φ : ω →ₗ[A] K := (e.toLinearMap.restrictScalars A) ∘ₗ LocalizedModule.mkLinearMap S ω
  have hmk : Function.Injective (LocalizedModule.mkLinearMap S ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨s, hs⟩, hsx⟩ :=
      (IsLocalizedModule.eq_zero_iff S (LocalizedModule.mkLinearMap S ω)).1 hx
    exact (smul_eq_zero_iff_right (nonZeroDivisors.ne_zero hs)).1 hsx
  have hφ : Function.Injective φ := e.injective.comp hmk
  obtain ⟨gens, hgens⟩ := Module.Finite.fg_top (R := A) (M := ω)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset S (gens.image φ)
  let d : A := b
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b.2
  let R : Submodule A K := LinearMap.range (Algebra.linearMap A K)
  have hint : ∀ x : ω, d • φ x ∈ R := by
    intro x
    have hx : x ∈ Submodule.span A (gens : Set ω) := by rw [hgens]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha⟩ := hb (φ y) (Finset.mem_image_of_mem φ hy)
      exact ⟨a, ha⟩
    | zero => rw [map_zero, smul_zero]; exact R.zero_mem
    | add y z _ _ hy hz => rw [map_add, smul_add]; exact R.add_mem hy hz
    | smul a y _ hy => rw [map_smul, smul_comm]; exact R.smul_mem a hy
  let ψ0 : ω →ₗ[A] R := LinearMap.codRestrict R (d • φ) hint
  have hiA : Function.Injective (Algebra.linearMap A K) := IsFractionRing.injective A K
  let iA : A ≃ₗ[A] R := LinearEquiv.ofInjective (Algebra.linearMap A K) hiA
  let ψ : ω →ₗ[A] A := iA.symm.toLinearMap ∘ₗ ψ0
  have hψ : Function.Injective ψ := by
    refine iA.symm.injective.comp ?_
    intro x y hxy
    have hxy' : d • φ x = d • φ y := congrArg Subtype.val hxy
    have hd : algebraMap A K d ≠ 0 := by
      rw [ne_eq, ← map_zero (algebraMap A K)]
      exact fun h => hd0 (hiA h)
    rw [Algebra.smul_def, Algebra.smul_def] at hxy'
    exact hφ (mul_left_cancel₀ hd hxy')
  refine ⟨LinearMap.range ψ, ?_, ⟨LinearEquiv.ofInjective ψ hψ⟩⟩
  intro hbot
  have hsub : Subsingleton ω := by
    refine ⟨fun x y => hψ ?_⟩
    have hx : ψ x ∈ LinearMap.range ψ := ⟨x, rfl⟩
    have hy : ψ y ∈ LinearMap.range ψ := ⟨y, rfl⟩
    rw [hbot, Submodule.mem_bot] at hx hy
    rw [hx, hy]
  have : Subsingleton (LocalizedModule S ω) := by
    refine ⟨fun y z => ?_⟩
    induction y using LocalizedModule.induction_on with
    | h x s =>
      induction z using LocalizedModule.induction_on with
      | h x' s' =>
        rw [Subsingleton.elim x 0, Subsingleton.elim x' 0, LocalizedModule.zero_mk,
          LocalizedModule.zero_mk]
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

end RankOne

end Dualizing

end
