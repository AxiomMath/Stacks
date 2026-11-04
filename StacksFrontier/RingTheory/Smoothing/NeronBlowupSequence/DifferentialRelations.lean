module

public import StacksFrontier.RingTheory.Smoothing.NeronBlowupSequence.TorsionLength
import all StacksFrontier.RingTheory.Smoothing.NeronBlowupSequence.TorsionLength

/-!
# Lattices of differential relations

Auxiliary results for Néron's desingularization by affine blowups: residue-field linear
independence and the square of an ideal, the lattice of differential relations of a
presentation, and polynomial presentations.

## Implementation notes

The termination measure is the torsion length of `Λ ⊗_{A'} Ω_{A'/R}`, a natural number because
`Λ` is a discrete valuation ring and the module is finite. The strict drop is proved by
comparing the differentials of two polynomial presentations: a surjection `P → A'` with `P` a
polynomial algebra, and the induced surjection `P[𝔭_P/π] → A'[𝔭'/π]`. The short exact sequence
of `affineBlowup_differentials_shortExact` supplies, over the local ring at the distinguished
prime of `P[𝔭_P/π]`, a map backwards which is a section up to the factor `π`; the two lattices
of differential relations are then compared, and the local parameters of
`exists_local_parameters_of_smoothAt` show that the comparison is strict unless the quotient is
already free.
-/

@[expose] public section

namespace Stacks.Smoothing

open CategoryTheory
open scoped TensorProduct

universe uV u v w w'

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## Residue-field linear independence and the square of the ideal -/

/-- Finitely many elements of `V` whose images are a basis of the residue-field span of `f`,
together with the data expressing every element of `V` as a combination of them after
multiplying by something outside `p`. -/
private lemma exists_residue_independent_generators
    {B M : Type*} {V : Type uV} [CommRing B] (p : Ideal B) [p.IsPrime]
    [AddCommGroup V] [Module B V]
    [AddCommGroup M] [Module p.ResidueField M] [Module.Finite p.ResidueField M]
    (f : V →ₛₗ[algebraMap B p.ResidueField] M) :
    ∃ (ι : Type uV) (_ : Fintype ι) (a : ι → V),
      LinearIndependent p.ResidueField (fun i => f (a i)) ∧
      ∀ x : V, ∃ (s : B), s ∉ p ∧ ∃ c : ι → B,
        f (s • x - ∑ i, c i • a i) = 0 := by
  classical
  obtain ⟨ι, a, -, hspan, ha⟩ := exists_linearIndependent' p.ResidueField f
  have : Finite ι := ha.finite
  let : Fintype ι := Fintype.ofFinite ι
  refine ⟨ι, inferInstance, a, ha, ?_⟩
  intro x
  have hx : f x ∈ Submodule.span p.ResidueField (Set.range (fun i => f (a i))) := by
    show f x ∈ Submodule.span p.ResidueField (Set.range (f ∘ a))
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self x)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx
  let C := Localization.AtPrime p
  have hlift (i : ι) : ∃ b : C, algebraMap C p.ResidueField b = c i :=
    IsLocalRing.residue_surjective (c i)
  choose b hb using hlift
  let s := IsLocalization.commonDenom p.primeCompl Finset.univ b
  let d (i : ι) := IsLocalization.integerMultiple p.primeCompl Finset.univ b
    ⟨i, Finset.mem_univ i⟩
  have hd (i : ι) : algebraMap B p.ResidueField (d i) =
      algebraMap B p.ResidueField s * c i := by
    dsimp only [d]
    rw [IsScalarTower.algebraMap_apply B C p.ResidueField,
      IsLocalization.map_integerMultiple]
    show algebraMap C p.ResidueField ((s : B) • b i) = _
    rw [Algebra.smul_def, map_mul, hb, ← IsScalarTower.algebraMap_apply]
  refine ⟨s, s.property, d, ?_⟩
  rw [map_sub, sub_eq_zero, map_smulₛₗ, map_sum]
  simp only [map_smulₛₗ, hd, mul_smul, ← Finset.smul_sum, hc]

/-- A span of elements whose images are linearly independent over `R/(π)` is saturated with
respect to `π`. -/
private lemma span_saturated_of_linearIndependent
    {R k M V ι : Type*} [CommRing R] [CommRing k]
    [AddCommGroup M] [Module R M] [AddCommGroup V] [Module k V] [Finite ι]
    (ρ : R →+* k) (π : R) (hker : RingHom.ker ρ = Ideal.span {π})
    (q : M →ₛₗ[ρ] V) (g : ι → M) (hg : LinearIndependent k (fun i => q (g i)))
    (hπ : IsSMulRegular M π) :
    ∀ x : M, π • x ∈ Submodule.span R (Set.range g) →
      x ∈ Submodule.span R (Set.range g) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  intro x hx
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  have hπ0 : ρ π = 0 := by
    show π ∈ RingHom.ker ρ
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hsum : ∑ i, ρ (a i) • q (g i) = 0 := by
    simpa only [map_sum, map_smulₛₗ, hπ0, zero_smul] using congrArg q ha
  have ha0 (i : ι) : ρ (a i) = 0 :=
    linearIndependent_iff'.mp hg Finset.univ (fun i => ρ (a i))
      hsum i (Finset.mem_univ _)
  have hdiv (i : ι) : ∃ b, a i = π * b := by
    apply Ideal.mem_span_singleton.mp
    rw [← hker]
    exact ha0 i
  choose b hb using hdiv
  apply (Submodule.mem_span_range_iff_exists_fun R).mpr
  refine ⟨b, hπ ?_⟩
  show π • (∑ i, b i • g i) = π • x
  rw [Finset.smul_sum]
  simpa only [hb, mul_smul] using ha

/-- If `N ≤ G ⊔ π • V` with `G ≤ V` and `G` saturated, then `π • x ∈ N` forces `x ∈ V`. -/
private lemma saturated_of_le_sup_smul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (π : R) (N G V : Submodule R M)
    (hNV : N ≤ G ⊔ V.map (π • LinearMap.id)) (hGV : G ≤ V)
    (hG : ∀ x : M, π • x ∈ G → x ∈ G) :
    ∀ x : M, π • x ∈ N → x ∈ V := by
  intro x hx
  obtain ⟨g, hg, y, hy, he⟩ := Submodule.mem_sup.mp (hNV hx)
  obtain ⟨z, hz, rfl⟩ := hy
  change g + π • z = π • x at he
  have hsub : x - z ∈ G := hG _ (by rwa [smul_sub, ← he, add_sub_cancel_right])
  simpa only [sub_add_cancel] using V.add_mem (hGV hsub) hz

/-- The span of the image of a derivation-like map `D` is saturated with respect to `π` relative
to a submodule `N` containing it, provided the elements killed by the residue-field companion
`D₀` land in `π • N`. -/
private lemma span_saturated_of_residue_kernel
    {B Λ K M M₀ M₁ : Type*} {V : Type uV}
    [CommRing B] [CommRing Λ] [Field K] [Algebra B Λ]
    [AddCommGroup V] [Module B V] [AddCommGroup M] [Module B M] [Module Λ M]
    [IsScalarTower B Λ M] (p : Ideal B) [p.IsPrime]
    [AddCommGroup M₀] [Module p.ResidueField M₀] [Module.Finite p.ResidueField M₀]
    [AddCommGroup M₁] [Module K M₁]
    [Algebra p.ResidueField K]
    (D : V →ₗ[B] M) (D₀ : V →ₛₗ[algebraMap B p.ResidueField] M₀)
    (ρ : Λ →+* K) (q : M →ₛₗ[ρ] M₁)
    (e : (K ⊗[p.ResidueField] M₀) ≃ₗ[K] M₁)
    (he : ∀ x, q (D x) = e ((1 : K) ⊗ₜ[p.ResidueField] D₀ x))
    (π : Λ) (hker : RingHom.ker ρ = Ideal.span {π})
    (hπ : IsSMulRegular M π)
    (hunit : ∀ s ∉ p, IsUnit (algebraMap B Λ s))
    (N : Submodule Λ M) (hDN : ∀ x, D x ∈ N)
    (hzero : ∀ x, D₀ x = 0 → D x ∈ N.map (π • LinearMap.id)) :
    ∀ x : M, π • x ∈ Submodule.span Λ (Set.range D) → x ∈ N := by
  classical
  obtain ⟨ι, hι, a, ha, hgen⟩ := exists_residue_independent_generators p D₀
  let : Fintype ι := hι
  let G := Submodule.span Λ (Set.range (fun i => D (a i)))
  have hG : ∀ x : M, π • x ∈ G → x ∈ G := by
    refine span_saturated_of_linearIndependent ρ π hker q (fun i => D (a i)) ?_ hπ
    have hh := (Module.Flat.linearIndependent_one_tmul (S := K) ha).map'
      e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    simpa only [Function.comp_def, LinearEquiv.coe_coe, he] using hh
  apply saturated_of_le_sup_smul π (Submodule.span Λ (Set.range D)) G N ?_ ?_ hG
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    obtain ⟨s, hs, c, hc⟩ := hgen x
    apply (Submodule.smul_mem_iff_of_isUnit (G ⊔ N.map (π • LinearMap.id))
      (hunit s hs)).mp
    have hz := hzero _ hc
    have hg : ∑ i, algebraMap B Λ (c i) • D (a i) ∈ G :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i)))
    have hh := (G ⊔ N.map (π • LinearMap.id)).add_mem
      (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hz)
    simpa only [map_sub, map_smul, map_sum, algebraMap_smul, add_sub_cancel] using hh
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => hDN (a i))

/-- If `𝔭 = (π) + (g₁, …, g_r)` with the `D gᵢ` independent over the residue field, an element
of `𝔭` killed by `B → Λ` and by `D` lies in `𝔭²`. -/
private lemma mem_sq_of_derivation_eq_zero
    {R B Λ k M ι : Type*} [CommRing R] [CommRing B] [CommRing Λ] [IsDomain Λ]
    [CommRing k] [AddCommGroup M] [Module B M] [Module k M]
    [Algebra R B] [Module R M] [IsScalarTower R B M] [Algebra R Λ] [Algebra B Λ]
    [IsScalarTower R B Λ] [Algebra B k] [IsScalarTower B k M] [Finite ι]
    (π : R) (hπ : algebraMap R Λ π ≠ 0) (p : Ideal B)
    (hp : p = Ideal.comap (algebraMap B Λ) (Ideal.span {algebraMap R Λ π}))
    (hk : RingHom.ker (algebraMap B k) = p) (g : ι → B)
    (hgen : p = Ideal.span {algebraMap R B π} ⊔ Ideal.span (Set.range g))
    (D : Derivation R B M) (hg : LinearIndependent k (fun i => D (g i)))
    {z : B} (hz : algebraMap B Λ z = 0) (hDz : D z = 0) : z ∈ p ^ 2 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hzmem : z ∈ p := by
    rw [hp]
    show algebraMap B Λ z ∈ Ideal.span {algebraMap R Λ π}
    rw [hz]
    exact Ideal.zero_mem _
  rw [hgen, Submodule.mem_sup] at hzmem
  obtain ⟨z₀, hz₀, z₁, hz₁, he⟩ := hzmem
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hz₀
  obtain ⟨b, rfl⟩ := Submodule.mem_span_range_iff_exists_fun B |>.mp hz₁
  have hπp : algebraMap R B π ∈ p := by
    rw [hgen]
    exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
  have hgp (i : ι) : g i ∈ p := by
    rw [hgen]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
  have hkill {x : B} (hx : x ∈ p) (m : M) : x • m = 0 := by
    have hx0 : algebraMap B k x = 0 := by rwa [← hk] at hx
    rw [← algebraMap_smul k x m, hx0, zero_smul]
  have hsum : ∑ i, algebraMap B k (b i) • D (g i) = 0 := by
    have hd := congrArg D he
    rw [hDz, map_add, Derivation.leibniz, Derivation.map_algebraMap,
      hkill hπp, smul_zero, zero_add, map_sum] at hd
    simpa only [Derivation.leibniz, hkill (hgp _), add_zero, zero_add,
      algebraMap_smul, smul_eq_mul] using hd
  have hb (i : ι) : b i ∈ p := by
    rw [← hk]
    exact (linearIndependent_iff'.mp hg Finset.univ
      (fun i => algebraMap B k (b i)) hsum i (Finset.mem_univ _))
  have hsum2 : ∑ i, b i * g i ∈ p ^ 2 := by
    rw [pow_two]
    exact Submodule.sum_mem _ (fun i _ => Ideal.mul_mem_mul (hb i) (hgp i))
  have hπa2 : algebraMap R B π * a ∈ p ^ 2 := by
    have heΛ := congrArg (algebraMap B Λ) he
    rw [hz, map_add, map_mul, ← IsScalarTower.algebraMap_apply] at heΛ
    have hmap : Ideal.map (algebraMap B Λ) (p ^ 2) ≤
        Ideal.span {algebraMap R Λ π ^ 2} := by
      rw [Ideal.map_pow, ← Ideal.span_singleton_pow]
      exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hp.le) 2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp
      (hmap (Ideal.mem_map_of_mem _ hsum2))
    have haΛ : algebraMap B Λ a = algebraMap R Λ π * (-c) := by
      apply mul_left_cancel₀ hπ
      have h := eq_neg_of_add_eq_zero_left heΛ
      simp only [smul_eq_mul] at h
      rw [hc, pow_two] at h
      simpa only [mul_neg, mul_assoc] using h
    have ha : a ∈ p := by
      rw [hp]
      exact Ideal.mem_span_singleton.mpr ⟨-c, haΛ⟩
    rw [pow_two]
    exact Ideal.mul_mem_mul hπp ha
  rw [← he]
  exact (p ^ 2).add_mem hπa2 hsum2

/-- The version of `mem_sq_of_derivation_eq_zero` where independence comes from the `g i`
appearing among the members of a basis of `Ω_{B/R}`. -/
private lemma mem_sq_of_tensor_differential_eq_zero
    {R B Λ k ι κ : Type*} [CommRing R] [CommRing B] [CommRing Λ] [IsDomain Λ]
    [CommRing k] [Nontrivial k] [Algebra R B] [Algebra R Λ] [Algebra B Λ]
    [IsScalarTower R B Λ] [Algebra B k] [Algebra R k] [IsScalarTower R B k]
    [Finite ι]
    (π : R) (hπ : algebraMap R Λ π ≠ 0) (p : Ideal B)
    (hp : p = Ideal.comap (algebraMap B Λ) (Ideal.span {algebraMap R Λ π}))
    (hk : RingHom.ker (algebraMap B k) = p) (g : ι → B)
    (hgen : p = Ideal.span {algebraMap R B π} ⊔ Ideal.span (Set.range g))
    (b : Module.Basis κ B Ω[B⁄R]) (e : ι → κ) (he : Function.Injective e)
    (hb : ∀ i, b (e i) = KaehlerDifferential.D R B (g i))
    {z : B} (hz : algebraMap B Λ z = 0)
    (hdz : (1 : k) ⊗ₜ[B] KaehlerDifferential.D R B z = 0) : z ∈ p ^ 2 := by
  let D : Derivation R B (k ⊗[B] Ω[B⁄R]) :=
    (TensorProduct.mk B k Ω[B⁄R] 1).compDer (KaehlerDifferential.D R B)
  have hg : LinearIndependent k (fun i => D (g i)) := by
    have h := (b.baseChange k).linearIndependent.comp e he
    show LinearIndependent k
      (fun i => (1 : k) ⊗ₜ[B] KaehlerDifferential.D R B (g i))
    simpa only [Module.Basis.baseChange_apply, Function.comp_def, hb] using h
  exact mem_sq_of_derivation_eq_zero π hπ p hp hk g hgen D hg hz hdz

/-- The base-change map `Λ ⊗_B Ω_{B/R} → Λ ⊗_{B'} Ω_{B'/R}` induced by `B → B'`. -/
private noncomputable def differentialBaseChangeMap
    (R B B' Λ : Type*) [CommRing R] [CommRing B] [CommRing B'] [CommRing Λ]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra B Λ] [Algebra B' Λ] [IsScalarTower B B' Λ] :
    (Λ ⊗[B] Ω[B⁄R]) →ₗ[Λ] (Λ ⊗[B'] Ω[B'⁄R]) :=
  (LinearMap.baseChange Λ (KaehlerDifferential.mapBaseChange R B B')).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' Λ Λ Ω[B⁄R]).symm.toLinearMap

/-- The base-change map on differentials, evaluated on a tensor. -/
private lemma differentialBaseChangeMap_tmul
    (R B B' Λ : Type*) [CommRing R] [CommRing B] [CommRing B'] [CommRing Λ]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra B Λ] [Algebra B' Λ] [IsScalarTower B B' Λ]
    (c : Λ) (x : Ω[B⁄R]) :
    differentialBaseChangeMap R B B' Λ (c ⊗ₜ[B] x) =
      c ⊗ₜ[B'] KaehlerDifferential.map R R B B' x := by
  simp only [differentialBaseChangeMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, KaehlerDifferential.mapBaseChange_tmul, one_smul]

/-- On a chart `B[1/f]` where the maximal ideal is generated by `π` and local parameters whose
differentials are basis members, an element of `𝔭` killed by `B → Λ` and by the residue-field
differential becomes, after multiplication by something outside `𝔭`, a member of `𝔭²`. -/
private lemma exists_mul_mem_sq_of_residue_differential_eq_zero
    {R B Λ : Type*} [CommRing R] [CommRing B] [CommRing Λ] [IsDomain Λ]
    [Algebra R B] [Algebra R Λ] [Algebra B Λ] [IsScalarTower R B Λ]
    (π : R) (hπ : algebraMap R Λ π ≠ 0) (p : Ideal B) [p.IsPrime]
    (hp : p = Ideal.comap (algebraMap B Λ) (Ideal.span {algebraMap R Λ π}))
    [IsLocalRing Λ]
    (hπmax : IsLocalRing.maximalIdeal Λ = Ideal.span {algebraMap R Λ π})
    (f : B) (hf : f ∉ p)
    {ι κ : Type*} [Finite ι]
    (g : ι → Localization.Away f)
    (hgen : Ideal.map (algebraMap B (Localization.Away f)) p =
      Ideal.span {algebraMap R (Localization.Away f) π} ⊔ Ideal.span (Set.range g))
    (b : Module.Basis κ (Localization.Away f) Ω[Localization.Away f⁄R])
    (e : ι → κ) (he : Function.Injective e)
    (hb : ∀ i, b (e i) = KaehlerDifferential.D R (Localization.Away f) (g i))
    {z : B} (hz : algebraMap B Λ z = 0)
    (hdz : (1 : p.ResidueField) ⊗ₜ[B] KaehlerDifferential.D R B z = 0) :
    ∃ s ∉ p, s * z ∈ p ^ 2 := by
  let C := Localization.Away f
  let k := p.ResidueField
  have hfk : IsUnit (algebraMap B k f) :=
    isUnit_iff_ne_zero.mpr fun h => hf ((Ideal.ker_algebraMap_residueField p) ▸ h)
  have hfΛ : IsUnit (algebraMap B Λ f) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    rw [hπmax]
    show f ∉ Ideal.comap (algebraMap B Λ) (Ideal.span {algebraMap R Λ π})
    rwa [← hp]
  let : Algebra C k := (IsLocalization.Away.lift f hfk).toAlgebra
  let : IsScalarTower B C k := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.Away.lift_comp f hfk).symm
  let : Algebra C Λ := (IsLocalization.Away.lift f hfΛ).toAlgebra
  let : IsScalarTower B C Λ := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.Away.lift_comp f hfΛ).symm
  let : IsScalarTower R C Λ := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B C,
      ← IsScalarTower.algebraMap_apply B C Λ,
      ← IsScalarTower.algebraMap_apply R B Λ]
  let : Algebra R k := ((algebraMap B k).comp (algebraMap R B)).toAlgebra
  let : IsScalarTower R B k := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R C k := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B C,
      ← IsScalarTower.algebraMap_apply B C k,
      ← IsScalarTower.algebraMap_apply R B k]
  let pC := Ideal.map (algebraMap B C) p
  have hpC : pC = Ideal.comap (algebraMap C Λ) (Ideal.span {algebraMap R Λ π}) := by
    have hcomp : Ideal.comap (algebraMap B C)
        (Ideal.comap (algebraMap C Λ) (Ideal.span {algebraMap R Λ π})) = p := by
      ext x
      show algebraMap C Λ (algebraMap B C x) ∈ Ideal.span {algebraMap R Λ π} ↔ x ∈ p
      rw [← IsScalarTower.algebraMap_apply B C Λ, hp]
      rfl
    dsimp only [pC]
    rw [← hcomp]
    exact IsLocalization.map_under (Submonoid.powers f) C _
  have hk : RingHom.ker (algebraMap C k) = pC := by
    have hcomp : Ideal.comap (algebraMap B C) (RingHom.ker (algebraMap C k)) = p := by
      ext x
      show algebraMap C k (algebraMap B C x) = 0 ↔ x ∈ p
      rw [← IsScalarTower.algebraMap_apply B C k]
      show x ∈ RingHom.ker (algebraMap B k) ↔ x ∈ p
      rw [Ideal.ker_algebraMap_residueField p]
    exact (IsLocalization.map_under (Submonoid.powers f) C _).symm.trans
      (congrArg (Ideal.map (algebraMap B C)) hcomp)
  have hzC : algebraMap C Λ (algebraMap B C z) = 0 := by
    rw [← IsScalarTower.algebraMap_apply B C Λ, hz]
  have hdzC : (1 : k) ⊗ₜ[C]
      KaehlerDifferential.D R C (algebraMap B C z) = 0 := by
    have h := congrArg (differentialBaseChangeMap R B C k) hdz
    simpa only [differentialBaseChangeMap_tmul, KaehlerDifferential.map_D,
      map_zero] using h
  have hzsq := mem_sq_of_tensor_differential_eq_zero π hπ pC hpC hk g hgen
    b e he hb hzC hdzC
  rw [← Ideal.map_pow] at hzsq
  obtain ⟨s, hs, hsz⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) C
      (p ^ 2) z).mp hzsq
  refine ⟨s, ?_, hsz⟩
  obtain ⟨n, rfl⟩ := hs
  exact p.primeCompl.pow_mem hf n

/-! ## The lattice of differential relations -/

/-- The `Λ`-submodule of `Λ ⊗_B Ω_{B/R}` spanned by the differentials of the elements of an
ideal `I` of `B`. -/
private noncomputable abbrev differentialRelations (R B Λ : Type*)
    [CommRing R] [CommRing B] [CommRing Λ] [Algebra R B] [Algebra B Λ]
    (I : Ideal B) : Submodule Λ (Λ ⊗[B] Ω[B⁄R]) :=
  Submodule.span Λ
    (Set.range fun x : I => (1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B x)

/-- The relations of an ideal `I` contained in `Ker(B → Λ)` are saturated with respect to a
uniformizer `π` of `Λ` relative to any submodule `N` containing them, provided the elements of
`I` whose residue-field differential vanishes have differential in `π • N`. -/
private lemma differentialRelations_saturated_of_residue_kernel
    {R B Λ : Type*} [CommRing R] [CommRing B] [CommRing Λ] [IsLocalRing Λ]
    [Algebra R B] [Algebra B Λ] [Algebra R Λ] [IsScalarTower R B Λ]
    [Module.Finite B Ω[B⁄R]]
    (p I : Ideal B) [p.IsPrime]
    (hp : p = Ideal.comap (algebraMap B Λ) (IsLocalRing.maximalIdeal Λ))
    (hI : I ≤ RingHom.ker (algebraMap B Λ))
    (π : Λ) (hπ : IsLocalRing.maximalIdeal Λ = Ideal.span {π})
    (hreg : IsSMulRegular (Λ ⊗[B] Ω[B⁄R]) π)
    (N : Submodule Λ (Λ ⊗[B] Ω[B⁄R]))
    (hN : differentialRelations R B Λ I ≤ N)
    (hzero : ∀ z ∈ I,
      (1 : p.ResidueField) ⊗ₜ[B] KaehlerDifferential.D R B z = 0 →
      (1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B z ∈ N.map (π • LinearMap.id)) :
    ∀ x : Λ ⊗[B] Ω[B⁄R], π • x ∈ differentialRelations R B Λ I → x ∈ N := by
  let k := p.ResidueField
  let : Field k := inferInstance
  let m := IsLocalRing.maximalIdeal Λ
  let : m.IsPrime := (IsLocalRing.maximalIdeal.isMaximal Λ).isPrime
  let K := m.ResidueField
  let : Field K := inferInstance
  let : Algebra B K := ((algebraMap Λ K).comp (algebraMap B Λ)).toAlgebra
  let : Module B K := (inferInstance : Algebra B K).toModule
  let : Module Λ K := (inferInstance : Algebra Λ K).toModule
  let : IsScalarTower B Λ K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra k K := (Ideal.ResidueField.map p m (algebraMap B Λ) hp).toAlgebra
  let : Module k K := (inferInstance : Algebra k K).toModule
  let : IsScalarTower B k K := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.map_algebraMap p m (algebraMap B Λ) hp b).symm
  let DΛ : Derivation R B (Λ ⊗[B] Ω[B⁄R]) :=
    (TensorProduct.mk B Λ Ω[B⁄R] 1).compDer (KaehlerDifferential.D R B)
  let Dk : Derivation R B (k ⊗[B] Ω[B⁄R]) :=
    (TensorProduct.mk B k Ω[B⁄R] 1).compDer (KaehlerDifferential.D R B)
  have hkI {z : B} (hz : z ∈ I) : algebraMap B k z = 0 := by
    show z ∈ RingHom.ker (algebraMap B k)
    rw [Ideal.ker_algebraMap_residueField, hp]
    show algebraMap B Λ z ∈ IsLocalRing.maximalIdeal Λ
    rw [show algebraMap B Λ z = 0 from hI hz]
    exact Ideal.zero_mem _
  let D : I →ₗ[B] (Λ ⊗[B] Ω[B⁄R]) := {
    toFun := fun x => DΛ x
    map_add' := fun x y => DΛ.map_add x y
    map_smul' := fun r x => by
      show DΛ (r * (x : B)) = r • DΛ x
      rw [Derivation.leibniz, ← algebraMap_smul Λ (x : B),
        show algebraMap B Λ (x : B) = 0 from hI x.property,
        zero_smul, add_zero] }
  let D₀ : I →ₛₗ[algebraMap B k] (k ⊗[B] Ω[B⁄R]) := {
    toFun := fun x => Dk x
    map_add' := fun x y => Dk.map_add x y
    map_smul' := fun r x => by
      show Dk (r * (x : B)) = algebraMap B k r • Dk x
      rw [Derivation.leibniz, ← algebraMap_smul k (x : B), hkI x.property,
        zero_smul, add_zero, algebraMap_smul] }
  let q : (Λ ⊗[B] Ω[B⁄R]) →ₛₗ[algebraMap Λ K] (K ⊗[Λ] (Λ ⊗[B] Ω[B⁄R])) := {
    toFun := fun x => (1 : K) ⊗ₜ[Λ] x
    map_add' := fun x y => TensorProduct.tmul_add _ _ _
    map_smul' := fun r x => by
      show (1 : K) ⊗ₜ[Λ] (r • x) = (algebraMap Λ K r) • ((1 : K) ⊗ₜ[Λ] x)
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      exact (algebraMap_smul K r (1 : K)).symm }
  have htower : IsScalarTower B k K := inferInstance
  let e : (K ⊗[k] (k ⊗[B] Ω[B⁄R])) ≃ₗ[K] (K ⊗[Λ] (Λ ⊗[B] Ω[B⁄R])) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B k K K Ω[B⁄R]).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B Λ K K Ω[B⁄R]).symm
  have he (x : I) : q (D x) = e ((1 : K) ⊗ₜ[k] D₀ x) := by
    show (1 : K) ⊗ₜ[Λ] ((1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B x) =
      e ((1 : K) ⊗ₜ[k] ((1 : k) ⊗ₜ[B] KaehlerDifferential.D R B x))
    simp only [e, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, one_smul]
  apply span_saturated_of_residue_kernel p D D₀ (algebraMap Λ K) q e he π
    ((Ideal.ker_algebraMap_residueField m).trans hπ) hreg ?_ N ?_ ?_
  · exact fun s hs => IsLocalRing.notMem_maximalIdeal.mp fun h => hs (hp ▸ h)
  · exact fun x => hN (Submodule.subset_span (Set.mem_range_self x))
  · exact fun x hx => hzero x x.property hx

/-- An element of the kernel whose product with something outside `𝔭` lies in `𝔭²` has
differential in `π` times the image of the relations downstairs. -/
private lemma differential_mem_smul_relations_of_mul_mem_sq
    {R B B' C Λ : Type*} [CommRing R] [CommRing B] [CommRing B']
    [CommRing C] [CommRing Λ] [IsLocalRing Λ]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra B Λ] [Algebra B' Λ] [IsScalarTower B B' Λ]
    [Algebra R Λ] [IsScalarTower R B Λ] [IsScalarTower R B' Λ]
    (φ : B' →+* C) (p : Ideal B)
    (hp : p = Ideal.comap (algebraMap B Λ) (IsLocalRing.maximalIdeal Λ))
    (π : R) (hπ : IsRegular (φ (algebraMap R B' π)))
    (hpmap : Ideal.map (algebraMap B B') p ≤ Ideal.span {algebraMap R B' π})
    (u : (Λ ⊗[B] Ω[B⁄R]) →ₗ[Λ] (Λ ⊗[B'] Ω[B'⁄R]))
    (v : (Λ ⊗[B'] Ω[B'⁄R]) →ₗ[Λ] (Λ ⊗[B] Ω[B⁄R]))
    (hinj : Function.Injective u)
    (hu : ∀ x : B, u ((1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B x) =
      (1 : Λ) ⊗ₜ[B'] KaehlerDifferential.D R B' (algebraMap B B' x))
    (huv : ∀ x, u (v x) = algebraMap R Λ π • x)
    (z : B) (hz : algebraMap B Λ z = 0) (hzφ : φ (algebraMap B B' z) = 0)
    (s : B) (hs : s ∉ p) (hsz : s * z ∈ p ^ 2) :
    (1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B z ∈
      ((differentialRelations R B' Λ (RingHom.ker φ)).map v).map
        (algebraMap R Λ π • LinearMap.id) := by
  have hsunit : IsUnit (algebraMap B Λ s) :=
    IsLocalRing.notMem_maximalIdeal.mp (by simpa only [hp, Ideal.mem_comap] using hs)
  obtain ⟨y, hy, he⟩ := exists_tensor_differential_division_of_kernel_mem_pow
    (Λ := Λ) φ p π hπ hpmap 2 hsz (by rw [map_mul, map_mul, hzφ, mul_zero])
  let D : Derivation R B (Λ ⊗[B] Ω[B⁄R]) :=
    (TensorProduct.mk B Λ Ω[B⁄R] 1).compDer (KaehlerDifferential.D R B)
  have hmul : (1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B (s * z) =
      algebraMap B Λ s • ((1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B z) := by
    show D (s * z) = algebraMap B Λ s • D z
    rw [Derivation.leibniz, ← algebraMap_smul Λ z, hz, zero_smul, add_zero,
      algebraMap_smul]
  apply (Submodule.smul_mem_iff_of_isUnit _ hsunit).mp
  let dy := (1 : Λ) ⊗ₜ[B'] KaehlerDifferential.D R B' y
  refine ⟨v dy, ⟨dy, ?_, rfl⟩, ?_⟩
  · exact Submodule.subset_span (Set.mem_range_self (⟨y, hy⟩ : RingHom.ker φ))
  · show algebraMap R Λ π • v dy = _
    apply hinj
    rw [map_smul, huv, ← hmul, hu, he, pow_two, mul_smul]

/-- The range of a base-changed map is the span of the images of a generating family. -/
private lemma range_baseChange_eq_span
    {A Λ M N ι : Type*} [CommRing A] [CommRing Λ] [Algebra A Λ]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (g : ι → M) (hg : Function.Surjective g) :
    LinearMap.range (LinearMap.baseChange Λ f) =
      Submodule.span Λ (Set.range fun i => (1 : Λ) ⊗ₜ[A] f (g i)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Submodule.zero_mem]
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul r m =>
      obtain ⟨i, rfl⟩ := hg m
      rw [LinearMap.baseChange_tmul]
      have hi := (Submodule.span Λ
        (Set.range fun i => (1 : Λ) ⊗ₜ[A] f (g i))).smul_mem r
          (Submodule.subset_span (Set.mem_range_self i))
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hi
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i =>
      ⟨(1 : Λ) ⊗ₜ[A] g i, LinearMap.baseChange_tmul _ _ _⟩)

/-- Under the identification `Λ ⊗_A (A ⊗_B Ω_{B/R}) ≃ Λ ⊗_B Ω_{B/R}`, the range of the
base-changed conormal map is the lattice of differential relations of `Ker(B → A)`. -/
private lemma conormalRange_map_cancelBaseChange
    {R B A Λ : Type*} [CommRing R] [CommRing B] [CommRing A] [CommRing Λ]
    [Algebra R B] [Algebra B A] [Algebra A Λ] [Algebra B Λ]
    [IsScalarTower B A Λ] (hsurj : Function.Surjective (algebraMap B A)) :
    letI := ConormalSeq.cotangentModule hsurj
    (LinearMap.range
        (LinearMap.baseChange Λ (ConormalSeq.conormalMap R hsurj))).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B A Λ Λ Ω[B⁄R]).toLinearMap =
      differentialRelations R B Λ (RingHom.ker (algebraMap B A)) := by
  let := ConormalSeq.cotangentModule hsurj
  rw [range_baseChange_eq_span (ConormalSeq.conormalMap R hsurj)
    (RingHom.ker (algebraMap B A)).toCotangent
    (RingHom.ker (algebraMap B A)).toCotangent_surjective, Submodule.map_span]
  unfold differentialRelations
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext x
  dsimp only [Function.comp_apply]
  rw [ConormalSeq.conormalMap_toCotangent, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- If `x` maps to `π ^ n * y` in `B'`, then `u` sends the differential of `x` to `π ^ n` times
that of `y`. -/
private lemma map_differential_eq_pow_smul
    {R B B' Λ : Type*} [CommRing R] [CommRing B] [CommRing B'] [CommRing Λ]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra B Λ] [Algebra B' Λ] [IsScalarTower B B' Λ]
    [Algebra R Λ] [IsScalarTower R B' Λ] (π : R)
    (u : (Λ ⊗[B] Ω[B⁄R]) →ₗ[Λ] (Λ ⊗[B'] Ω[B'⁄R]))
    (hu : ∀ x : B, u ((1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B x) =
      (1 : Λ) ⊗ₜ[B'] KaehlerDifferential.D R B' (algebraMap B B' x))
    (n : ℕ) (x : B) (y : B') (he : algebraMap B B' x = algebraMap R B' π ^ n * y) :
    u ((1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B x) =
      algebraMap R Λ π ^ n • ((1 : Λ) ⊗ₜ[B'] KaehlerDifferential.D R B' y) := by
  have hd : KaehlerDifferential.D R B' (algebraMap B B' x) =
      algebraMap R B' π ^ n • KaehlerDifferential.D R B' y := by
    rw [he, ← map_pow, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  rw [hu, hd, TensorProduct.tmul_smul]
  simp only [Algebra.smul_def, mul_one, map_pow,
    ← IsScalarTower.algebraMap_apply, TensorProduct.smul_tmul']

/-- If every element of `I` becomes `π` times an element of `I'`, the relations of `I` lie in the
image under `v` of the relations of `I'`. -/
private lemma differentialRelations_le_map_of_division
    {R B B' Λ : Type*} [CommRing R] [CommRing B] [CommRing B'] [CommRing Λ]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra B Λ] [Algebra B' Λ] [IsScalarTower B B' Λ]
    [Algebra R Λ] [IsScalarTower R B' Λ]
    (I : Ideal B) (I' : Ideal B') (π : R)
    (u : (Λ ⊗[B] Ω[B⁄R]) →ₗ[Λ] (Λ ⊗[B'] Ω[B'⁄R]))
    (v : (Λ ⊗[B'] Ω[B'⁄R]) →ₗ[Λ] (Λ ⊗[B] Ω[B⁄R]))
    (hinj : Function.Injective u)
    (hu : ∀ x : B, u ((1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B x) =
      (1 : Λ) ⊗ₜ[B'] KaehlerDifferential.D R B' (algebraMap B B' x))
    (huv : ∀ x, u (v x) = algebraMap R Λ π • x)
    (hdiv : ∀ x ∈ I, ∃ y ∈ I', algebraMap B B' x = algebraMap R B' π * y) :
    differentialRelations R B Λ I ≤ (differentialRelations R B' Λ I').map v := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy, he⟩ := hdiv x x.property
  have ht := map_differential_eq_pow_smul π u hu 1 x y (by rwa [pow_one])
  rw [pow_one] at ht
  have hxv : (1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B x =
      v ((1 : Λ) ⊗ₜ[B'] KaehlerDifferential.D R B' y) :=
    hinj (ht.trans (huv _).symm)
  exact ⟨(1 : Λ) ⊗ₜ[B'] KaehlerDifferential.D R B' y,
    Submodule.subset_span (Set.mem_range_self (⟨y, hy⟩ : I')), hxv.symm⟩

/-- If every element of `I'` has a `π`-power multiple coming from `I`, the relations of `I'` lie
in the saturation of the image under `u` of the relations of `I`. -/
private lemma differentialRelations_le_torsionSaturation_map
    {R B B' Λ : Type*} [CommRing R] [CommRing B] [CommRing B'] [CommRing Λ]
    [IsDomain Λ] [Algebra R B] [Algebra R B'] [Algebra B B']
    [IsScalarTower R B B'] [Algebra B Λ] [Algebra B' Λ]
    [IsScalarTower B B' Λ] [Algebra R Λ] [IsScalarTower R B' Λ]
    (I : Ideal B) (I' : Ideal B') (π : R) (hπ : algebraMap R Λ π ≠ 0)
    (u : (Λ ⊗[B] Ω[B⁄R]) →ₗ[Λ] (Λ ⊗[B'] Ω[B'⁄R]))
    (hu : ∀ x : B, u ((1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B x) =
      (1 : Λ) ⊗ₜ[B'] KaehlerDifferential.D R B' (algebraMap B B' x))
    (hclear : ∀ x ∈ I', ∃ (n : ℕ) (y : B), y ∈ I ∧
      algebraMap B B' y = algebraMap R B' π ^ n * x) :
    differentialRelations R B' Λ I' ≤
      torsionSaturation ((differentialRelations R B Λ I).map u) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  obtain ⟨n, y, hy, he⟩ := hclear x x.property
  apply (mem_torsionSaturation_iff _ _).mpr
  refine ⟨algebraMap R Λ π ^ n, pow_ne_zero n hπ, ?_⟩
  have ht := map_differential_eq_pow_smul π u hu n y x he
  exact ⟨(1 : Λ) ⊗ₜ[B] KaehlerDifferential.D R B y,
    Submodule.subset_span (Set.mem_range_self (⟨y, hy⟩ : I)), ht⟩

/-- The conormal sequence of a surjection `B → A`, base changed to `Λ`, identifies the cokernel
of the conormal map with `Λ ⊗_A Ω_{A/R}`. -/
private noncomputable def quotConormalRangeEquivDifferentials
    {R A Λ B : Type*} [CommRing R] [CommRing A] [CommRing Λ] [CommRing B]
    [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    [Algebra A Λ]
    (hsurj : Function.Surjective (algebraMap B A)) :
    letI := ConormalSeq.cotangentModule hsurj
    ((Λ ⊗[A] (A ⊗[B] Ω[B⁄R])) ⧸
        LinearMap.range
          (LinearMap.baseChange Λ (ConormalSeq.conormalMap R hsurj))) ≃ₗ[Λ]
      Λ ⊗[A] Ω[A⁄R] := by
  letI := ConormalSeq.cotangentModule hsurj
  let g := KaehlerDifferential.mapBaseChange R B A
  obtain ⟨hker, hsur⟩ := ConormalSeq.conormal_exact_sequence R B A hsurj
  have hex : Function.Exact (ConormalSeq.conormalMap R hsurj) g :=
    LinearMap.exact_iff.mpr hker.symm
  have hex' : Function.Exact
      (LinearMap.baseChange Λ (ConormalSeq.conormalMap R hsurj))
      (LinearMap.baseChange Λ g) := lTensor_exact Λ hex hsur
  exact (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hex').symm).trans
    ((LinearMap.baseChange Λ g).quotKerEquivOfSurjective
      (LinearMap.baseChange_surjective Λ hsur))

/-- For a surjection `B → A`, the quotient of `Λ ⊗_B Ω_{B/R}` by the differential relations of
the kernel is `Λ ⊗_A Ω_{A/R}`. -/
private noncomputable def differentialRelationsQuotientEquiv
    {R B A Λ : Type*} [CommRing R] [CommRing B] [CommRing A] [CommRing Λ]
    [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    [Algebra A Λ] [Algebra B Λ] [IsScalarTower B A Λ]
    (hsurj : Function.Surjective (algebraMap B A)) :
    ((Λ ⊗[B] Ω[B⁄R]) ⧸
        differentialRelations R B Λ (RingHom.ker (algebraMap B A))) ≃ₗ[Λ]
      Λ ⊗[A] Ω[A⁄R] := by
  letI := ConormalSeq.cotangentModule hsurj
  let e := Submodule.Quotient.equiv
    (LinearMap.range (LinearMap.baseChange Λ (ConormalSeq.conormalMap R hsurj)))
    (differentialRelations R B Λ (RingHom.ker (algebraMap B A)))
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B A Λ Λ Ω[B⁄R])
    (conormalRange_map_cancelBaseChange hsurj)
  exact e.symm.trans (quotConormalRangeEquivDifferentials hsurj)

/-- The torsion length of `Λ ⊗_A Ω_{A/R}` drops strictly when passing from a presentation
`B → A` to a presentation `B' → A'` whose lattices of differential relations compare as in
`lt_map_of_not_free_quotient`, provided the original length is non-zero. -/
private lemma torsion_length_differentials_lt_of_comparison
    {R B A B' A' Λ : Type*}
    [CommRing R] [CommRing B] [CommRing A] [CommRing B'] [CommRing A']
    [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    [Algebra R B'] [Algebra R A'] [Algebra B' A'] [IsScalarTower R B' A']
    [Algebra A Λ] [Algebra B Λ] [IsScalarTower B A Λ]
    [Algebra A' Λ] [Algebra B' Λ] [IsScalarTower B' A' Λ]
    [Algebra.FiniteType R A] [Algebra.FiniteType R A']
    [Algebra.FiniteType R B]
    (hsurj : Function.Surjective (algebraMap B A))
    (hsurj' : Function.Surjective (algebraMap B' A'))
    [Module.IsTorsionFree Λ (Λ ⊗[B'] Ω[B'⁄R])]
    (π : Λ) (hπ : IsLocalRing.maximalIdeal Λ = Ideal.span ({π} : Set Λ))
    (hπ0 : π ≠ 0)
    (u : (Λ ⊗[B] Ω[B⁄R]) →ₗ[Λ] (Λ ⊗[B'] Ω[B'⁄R]))
    (v : (Λ ⊗[B'] Ω[B'⁄R]) →ₗ[Λ] (Λ ⊗[B] Ω[B⁄R]))
    (hu : Function.Injective u) (huv : ∀ x, u (v x) = π • x)
    (hle : differentialRelations R B Λ (RingHom.ker (algebraMap B A)) ≤
      (differentialRelations R B' Λ (RingHom.ker (algebraMap B' A'))).map v)
    (hgen : differentialRelations R B' Λ (RingHom.ker (algebraMap B' A')) ≤
      torsionSaturation ((differentialRelations R B Λ
        (RingHom.ker (algebraMap B A))).map u))
    (hdiv : ∀ x : Λ ⊗[B] Ω[B⁄R],
      π • x ∈ differentialRelations R B Λ (RingHom.ker (algebraMap B A)) →
        ∃ y ∈ differentialRelations R B' Λ (RingHom.ker (algebraMap B' A')),
          u x = π • y)
    (hpos : (Module.length Λ (Submodule.torsion Λ (Λ ⊗[A] Ω[A⁄R]))).toNat ≠ 0) :
    (Module.length Λ (Submodule.torsion Λ (Λ ⊗[A'] Ω[A'⁄R]))).toNat <
      (Module.length Λ (Submodule.torsion Λ (Λ ⊗[A] Ω[A⁄R]))).toNat := by
  let N := differentialRelations R B Λ (RingHom.ker (algebraMap B A))
  let N' := differentialRelations R B' Λ (RingHom.ker (algebraMap B' A'))
  let e := differentialRelationsQuotientEquiv (R := R) (Λ := Λ) hsurj
  let e' := differentialRelationsQuotientEquiv (R := R) (Λ := Λ) hsurj'
  have : Module.Finite Λ ((Λ ⊗[B] Ω[B⁄R]) ⧸ N) := inferInstance
  have hnfree : ¬ Module.Free Λ ((Λ ⊗[B] Ω[B⁄R]) ⧸ N) := fun _ =>
    hpos (torsion_length_toNat_eq_zero_iff_free.mpr (Module.Free.of_equiv e))
  have hstrict : N < N'.map v :=
    lt_map_of_not_free_quotient u v hu π hπ huv N N' hle hdiv hnfree
  have hfin : IsFiniteLength Λ (Submodule.torsion Λ ((Λ ⊗[B] Ω[B⁄R]) ⧸ N)) :=
    isFiniteLength_of_isTorsion Submodule.torsion_isTorsion
  have hdec := torsion_length_toNat_lt_of_lattice_comparison u v hu π hπ0 huv
    N N' hfin hgen hstrict
  rwa [torsion_length_eq_of_linearEquiv e, torsion_length_eq_of_linearEquiv e'] at hdec

/-! ## Polynomial presentations -/

/-- A finite-type algebra is a quotient of a polynomial algebra in finitely many variables. -/
private lemma exists_finite_polynomial_presentation
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective f :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.mp inferInstance

/-- A map to a local ring factors through the localization at the preimage of the maximal
ideal. -/
private lemma exists_map_localizationAtPrime_to_local
    {A Λ : Type*} [CommRing A] [CommRing Λ] [IsLocalRing Λ]
    (f : A →+* Λ) :
    ∃ g : Localization.AtPrime
        (Ideal.comap f (IsLocalRing.maximalIdeal Λ)) →+* Λ,
      ∀ x : A, g (algebraMap A _ x) = f x := by
  let p := Ideal.comap f (IsLocalRing.maximalIdeal Λ)
  let : p.IsPrime := by
    let : (IsLocalRing.maximalIdeal Λ).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal Λ).isPrime
    exact Ideal.comap_isPrime _ _
  have hunit : ∀ x : p.primeCompl, IsUnit (f x) := fun x =>
    IsLocalRing.notMem_maximalIdeal.mp x.property
  exact ⟨IsLocalization.lift hunit, fun x => IsLocalization.lift_eq hunit x⟩

/-- A finite-type algebra is a quotient of a polynomial algebra, which is smooth over the base
at every prime. -/
lemma exists_smooth_polynomial_presentation
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (q : Ideal A) [q.IsPrime] :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective f ∧
      Algebra.SmoothAt R (MvPolynomial (Fin n) R)
        (Ideal.comap f.toRingHom q) := by
  obtain ⟨n, f, hf⟩ := exists_finite_polynomial_presentation (R := R) (A := A)
  refine ⟨n, f, hf, ?_⟩
  let P := MvPolynomial (Fin n) R
  let : Algebra.Smooth R P := ⟨inferInstance, inferInstance⟩
  refine ⟨1, ?_, ?_⟩
  · let : (Ideal.comap f.toRingHom q).IsPrime := Ideal.comap_isPrime _ _
    exact fun h => ‹(Ideal.comap f.toRingHom q).IsPrime›.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  · let : Algebra.Smooth P (Localization.Away (1 : P)) :=
      Algebra.Smooth.of_isLocalization_Away (R := P) 1
    exact Algebra.Smooth.comp R P _

/-- In a Néron situation, a uniformizer of `R` generates the maximal ideal of `Λ`, since the
ramification index of the extension is one. -/
private lemma maximalIdeal_eq_span_algebraMap (S : NeronSituation.{u, v, w}) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    IsLocalRing.maximalIdeal S.Λ = Ideal.span ({algebraMap S.R S.Λ π} : Set S.Λ) := by
  have _ : IsLocalHom (algebraMap S.R S.Λ) := S.extension.2
  have _ : FaithfulSMul S.R S.Λ :=
    (faithfulSMul_iff_algebraMap_injective S.R S.Λ).mpr S.extension.1
  have hm :=
    DiscreteValuationRing.Ramification.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx
      S.R S.Λ
  rw [S.ramificationIndex_one, pow_one, hπ, Ideal.map_span, Set.image_singleton] at hm
  exact hm.symm

end Stacks.Smoothing

end
