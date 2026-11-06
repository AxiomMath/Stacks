module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.NodalAlgebra
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ClosedFibreDeltaOne
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.GeometricBranches

/-!
# Two geometric branches make the closed fibre separable

Let `A` be a reduced Noetherian local ring with `Ring.deltaInvariant A = 1` and exactly two
geometric branches, and let `A' = integralClosure A (FractionRing A)` be its normalization inside
its total ring of fractions. Then the closed fibre `Stacks.Curves.quadraticAlgebra A = A' ⧸ 𝔪 A'`
is a separable algebra over the residue field `κ`.

## Main results

* `Stacks.Curves.isSeparable_quadraticAlgebra_of_deltaInvariant_eq_one_of_two_branches` — the
  closed fibre of the normalization is separable over the residue field.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C37](https://stacks.math.columbia.edu/tag/0C37)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u

namespace Stacks.Curves

/-! ### Elementary separability facts -/

/-- Two distinct monic linear polynomials over a field are coprime. -/
private theorem isCoprime_X_sub_C_of_ne {κ : Type u} [Field κ] {a b : κ} (hab : a ≠ b) :
    IsCoprime (X - C a) (X - C b) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  refine ⟨C (b - a)⁻¹, -(C (b - a)⁻¹), ?_⟩
  have h : C (b - a)⁻¹ * (X - C a) + -(C (b - a)⁻¹) * (X - C b) = C ((b - a)⁻¹ * (b - a)) := by
    rw [map_mul, map_sub]; ring
  rw [h, inv_mul_cancel₀ hba, map_one]

/-- The square of a field is a separable algebra over it. -/
private theorem isSeparable_prod_self (κ : Type u) [Field κ] :
    Algebra.IsSeparable κ (κ × κ) := by
  refine ⟨fun x => ?_⟩
  have hx1 : Polynomial.aeval x (X - C x.1) = (0, x.2 - x.1) := by
    simp [Prod.ext_iff, Algebra.algebraMap_eq_smul_one]
  have hx2 : Polynomial.aeval x (X - C x.2) = (x.1 - x.2, 0) := by
    simp [Prod.ext_iff, Algebra.algebraMap_eq_smul_one]
  by_cases h : x.1 = x.2
  · have hae : Polynomial.aeval x (X - C x.1) = 0 := by rw [hx1, h]; simp
    exact Polynomial.Separable.of_dvd Polynomial.separable_X_sub_C (minpoly.dvd κ x hae)
  · have hae : Polynomial.aeval x ((X - C x.1) * (X - C x.2)) = 0 := by
      rw [map_mul, hx1, hx2]; simp [Prod.ext_iff]
    exact Polynomial.Separable.of_dvd
      (Polynomial.Separable.mul Polynomial.separable_X_sub_C Polynomial.separable_X_sub_C
        (isCoprime_X_sub_C_of_ne h)) (minpoly.dvd κ x hae)

/-- A nontrivial algebra of rank one over a field is that field. -/
private noncomputable def algEquivOfFinrankEqOne (κ : Type u) [Field κ] (L : Type u) [CommRing L]
    [Nontrivial L] [Algebra κ L] [Module.Finite κ L] (h : Module.finrank κ L = 1) :
    κ ≃ₐ[κ] L := by
  have hinj : Function.Injective (algebraMap κ L) := (algebraMap κ L).injective
  have hrange : LinearMap.range (Algebra.linearMap κ L) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [LinearMap.finrank_range_of_inj hinj, h, Module.finrank_self]
  exact AlgEquiv.ofBijective (Algebra.ofId κ L) ⟨hinj, fun y =>
    (show y ∈ LinearMap.range (Algebra.linearMap κ L) from hrange ▸ Submodule.mem_top)⟩

/-- A surjective linear map from a module spanned by two elements onto a two-dimensional space is
injective. -/
private theorem injective_of_spanning_pair_of_finrank_eq_two {κ : Type u} [Field κ] {M : Type u}
    [AddCommMonoid M] [Module κ M] {N : Type u} [AddCommGroup N] [Module κ N] [Module.Finite κ N]
    (f : M →ₗ[κ] N) (hf : Function.Surjective f) {x : M} {y : M}
    (hspan : ∀ z : M, ∃ a b : κ, z = a • x + b • y) (hrank : Module.finrank κ N = 2) :
    Function.Injective f := by
  have hspanN : ⊤ ≤ Submodule.span κ (Set.range ![f x, f y]) := by
    intro w _
    obtain ⟨z, rfl⟩ := hf w
    obtain ⟨a, b, rfl⟩ := hspan z
    rw [map_add, map_smul, map_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hliN : LinearIndependent κ ![f x, f y] :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanN (by simp [hrank])
  intro z w hzw
  obtain ⟨a, b, rfl⟩ := hspan z
  obtain ⟨c, d, rfl⟩ := hspan w
  simp only [map_add, map_smul] at hzw
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hliN (a - c) (b - d) (by
    rw [sub_smul, sub_smul, sub_add_sub_comm, hzw, sub_self])
  rw [sub_eq_zero] at h1 h2
  rw [h1, h2]

/-! ### Reading the branch count at a single maximal ideal -/

/-- Over a subsingleton index, a dependent sum is its only fibre. -/
private theorem bijective_sigmaMk_of_subsingleton {ι : Type*} [Subsingleton ι] (T : ι → Type*)
    (i₀ : ι) : Function.Bijective (Sigma.mk i₀ : T i₀ → Σ i, T i) := by
  refine ⟨sigma_mk_injective, ?_⟩
  rintro ⟨i, t⟩
  obtain rfl := Subsingleton.elim i i₀
  exact ⟨t, rfl⟩

/-- If the normalization of a reduced Noetherian local ring with two geometric branches has a
single maximal ideal, the residue extension there has separable degree two. -/
private theorem sepDegree_eq_two_of_subsingleton (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsReduced A] (hbr : numberOfGeometricBranchesOfLocalRing A = 2)
    (_hsub : Subsingleton (MaximalSpectrum ↥(integralClosure A (FractionRing A))))
    (m₀ : MaximalSpectrum ↥(integralClosure A (FractionRing A)))
    (hcontract : maximalIdeal A =
      m₀.asIdeal.comap (algebraMap A ↥(integralClosure A (FractionRing A)))) :
    letI : Field (↥(integralClosure A (FractionRing A)) ⧸ m₀.asIdeal) :=
      Ideal.Quotient.field m₀.asIdeal
    letI : Algebra (ResidueField A) (↥(integralClosure A (FractionRing A)) ⧸ m₀.asIdeal) :=
      (Ideal.quotientMap m₀.asIdeal (algebraMap A ↥(integralClosure A (FractionRing A)))
        (le_of_eq hcontract)).toAlgebra
    Field.sepDegree (ResidueField A)
      (↥(integralClosure A (FractionRing A)) ⧸ m₀.asIdeal) = 2 := by
  classical
  let : Field (↥(integralClosure A (FractionRing A)) ⧸ m₀.asIdeal) :=
    Ideal.Quotient.field m₀.asIdeal
  let : Algebra (ResidueField A) (↥(integralClosure A (FractionRing A)) ⧸ m₀.asIdeal) :=
    (Ideal.quotientMap m₀.asIdeal (algebraMap A ↥(integralClosure A (FractionRing A)))
      (le_of_eq hcontract)).toAlgebra
  obtain ⟨-, -, -, hfin⟩ := numberOfBranches_characterizations A
    (henselizationData A).carrier (strictHenselizationData A).carrier
    (SeparableClosure (ResidueField A))
  obtain ⟨-, hcon, hgeo⟩ := hfin (minimalPrimes.finite_of_isNoetherianRing A)
  have hcount : numberOfGeometricBranches A (SeparableClosure (ResidueField A))
      (strictHenselizationData A).carrier = 2 := hbr
  rw [hgeo] at hcount
  let eC := integralClosureQuotNilradicalAlgEquiv A
  let g : ↥(integralClosure A (FractionRing (A ⧸ nilradical A))) →+*
      ↥(integralClosure A (FractionRing A)) := eC.toRingEquiv.toRingHom
  have hgsurj : Function.Surjective g := eC.surjective
  let m₀' : MaximalSpectrum ↥(integralClosure A (FractionRing (A ⧸ nilradical A))) :=
    ⟨m₀.asIdeal.comap g, Ideal.comap_isMaximal_of_surjective g hgsurj⟩
  let : m₀'.asIdeal.IsMaximal := m₀'.isMaximal
  let : Field (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m₀'.asIdeal) :=
    Ideal.Quotient.field m₀'.asIdeal
  let : Algebra (ResidueField A)
      (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m₀'.asIdeal) :=
    (Ideal.quotientMap m₀'.asIdeal
      (algebraMap A ↥(integralClosure A (FractionRing (A ⧸ nilradical A))))
      (le_of_eq (hcon m₀'))).toAlgebra
  let T : MaximalSpectrum ↥(integralClosure A (FractionRing (A ⧸ nilradical A))) → Type u :=
    fun m' =>
      let : Field (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m'.asIdeal) :=
        Ideal.Quotient.field m'.asIdeal
      let : Algebra (ResidueField A)
          (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m'.asIdeal) :=
        (Ideal.quotientMap m'.asIdeal
          (algebraMap A ↥(integralClosure A (FractionRing (A ⧸ nilradical A))))
          (le_of_eq (hcon m'))).toAlgebra
      (Field.sepDegree (ResidueField A)
        (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m'.asIdeal)).ord.ToType
  have hcount' : ENat.card (Σ m', T m') = 2 := hcount
  have hsub' : Subsingleton
      (MaximalSpectrum ↥(integralClosure A (FractionRing (A ⧸ nilradical A)))) :=
    Equiv.subsingleton (maximalSpectrumCongr eC.toRingEquiv)
  have hcard : ENat.card (T m₀') = 2 := by
    rw [← hcount']
    exact ENat.card_congr
      (Equiv.ofBijective (Sigma.mk (β := T) m₀') (bijective_sigmaMk_of_subsingleton T m₀'))
  have hsep' : Field.sepDegree (ResidueField A)
      (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m₀'.asIdeal) = 2 := by
    refine Cardinal.toENat_eq_ofNat.mp ?_
    simpa [T, ENat.card, Cardinal.mk_ord_toType] using hcard
  have hmap : m₀.asIdeal = Ideal.map g m₀'.asIdeal :=
    (Ideal.map_comap_of_surjective g hgsurj m₀.asIdeal).symm
  let ealg : (↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ⧸ m₀'.asIdeal)
      ≃ₐ[ResidueField A] (↥(integralClosure A (FractionRing A)) ⧸ m₀.asIdeal) :=
    { Ideal.quotientEquiv m₀'.asIdeal m₀.asIdeal eC.toRingEquiv hmap with
      commutes' := by
        intro r
        obtain ⟨a, rfl⟩ := residue_surjective r
        show Ideal.quotientEquiv m₀'.asIdeal m₀.asIdeal eC.toRingEquiv hmap
            (Ideal.quotientMap m₀'.asIdeal
              (algebraMap A ↥(integralClosure A (FractionRing (A ⧸ nilradical A))))
              (le_of_eq (hcon m₀')) (Ideal.Quotient.mk (maximalIdeal A) a)) = _
        rw [Ideal.quotientMap_mk]
        show Ideal.Quotient.mk m₀.asIdeal
            (eC (algebraMap A ↥(integralClosure A (FractionRing (A ⧸ nilradical A))) a)) = _
        rw [eC.commutes]
        show _ = Ideal.quotientMap m₀.asIdeal
          (algebraMap A ↥(integralClosure A (FractionRing A))) (le_of_eq hcontract)
          (Ideal.Quotient.mk (maximalIdeal A) a)
        rw [Ideal.quotientMap_mk] }
  rwa [← Field.sepDegree_eq_of_equiv _ _ _ ealg]

/-! ### Two abstract criteria for separability of the fibre -/

/-- A two-dimensional algebra over the residue field surjecting onto a field of separable degree
two over it is separable. -/
private theorem isSeparable_of_surjective_of_sepDegree_eq_two (A : Type u) [CommRing A]
    [IsLocalRing A] (hfinF : Module.Finite (ResidueField A) (quadraticAlgebra A))
    (hrankF : Module.finrank (ResidueField A) (quadraticAlgebra A) = 2)
    {x : quadraticAlgebra A} {y : quadraticAlgebra A}
    (hspan : ∀ z : quadraticAlgebra A, ∃ a b : ResidueField A, z = a • x + b • y)
    {L : Type u} [Field L] [Algebra (ResidueField A) L]
    (φ : quadraticAlgebra A →ₐ[ResidueField A] L)
    (hφ : Function.Surjective φ) (hsep : Field.sepDegree (ResidueField A) L = 2) :
    Algebra.IsSeparable (ResidueField A) (quadraticAlgebra A) := by
  let : Module.Finite (ResidueField A) (quadraticAlgebra A) := hfinF
  have hfinL : Module.Finite (ResidueField A) L :=
    Module.Finite.of_surjective φ.toLinearMap hφ
  have hle2 : Module.finrank (ResidueField A) L ≤ 2 := by
    rw [← hrankF]
    exact LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hφ
  have hfs : Field.finSepDegree (ResidueField A) L = 2 := by
    have halg : Algebra.IsAlgebraic (ResidueField A) L := Algebra.IsAlgebraic.of_finite _ _
    rw [Field.finSepDegree_eq, hsep]
    simp
  have hrankL : Module.finrank (ResidueField A) L = 2 :=
    le_antisymm hle2 (by rw [← hfs]; exact Field.finSepDegree_le_finrank _ _)
  have hsepL : Algebra.IsSeparable (ResidueField A) L :=
    (Field.finSepDegree_eq_finrank_iff _ _).mp (by rw [hfs, hrankL])
  have hinj : Function.Injective φ :=
    injective_of_spanning_pair_of_finrank_eq_two φ.toLinearMap hφ hspan hrankL
  exact (AlgEquiv.Algebra.isSeparable_iff (AlgEquiv.ofBijective φ ⟨hinj, hφ⟩)).mpr hsepL

/-- A two-dimensional algebra over the residue field surjecting onto a product of two fields over
it is separable. -/
private theorem isSeparable_of_surjective_prod (A : Type u) [CommRing A] [IsLocalRing A]
    (hfinF : Module.Finite (ResidueField A) (quadraticAlgebra A))
    (hrankF : Module.finrank (ResidueField A) (quadraticAlgebra A) = 2)
    {x : quadraticAlgebra A} {y : quadraticAlgebra A}
    (hspan : ∀ z : quadraticAlgebra A, ∃ a b : ResidueField A, z = a • x + b • y)
    {L₁ : Type u} {L₂ : Type u} [Field L₁] [Field L₂] [Algebra (ResidueField A) L₁]
    [Algebra (ResidueField A) L₂] (φ : quadraticAlgebra A →ₐ[ResidueField A] L₁ × L₂)
    (hφ : Function.Surjective φ) :
    Algebra.IsSeparable (ResidueField A) (quadraticAlgebra A) := by
  let : Module.Finite (ResidueField A) (quadraticAlgebra A) := hfinF
  have hfinP : Module.Finite (ResidueField A) (L₁ × L₂) :=
    Module.Finite.of_surjective φ.toLinearMap hφ
  have hfin1 : Module.Finite (ResidueField A) L₁ :=
    Module.Finite.of_surjective (LinearMap.fst (ResidueField A) L₁ L₂) Prod.fst_surjective
  have hfin2 : Module.Finite (ResidueField A) L₂ :=
    Module.Finite.of_surjective (LinearMap.snd (ResidueField A) L₁ L₂) Prod.snd_surjective
  have hprod : Module.finrank (ResidueField A) (L₁ × L₂)
      = Module.finrank (ResidueField A) L₁ + Module.finrank (ResidueField A) L₂ :=
    Module.finrank_prod
  have hle2 : Module.finrank (ResidueField A) (L₁ × L₂) ≤ 2 := by
    rw [← hrankF]
    exact LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hφ
  have h1pos : 0 < Module.finrank (ResidueField A) L₁ := Module.finrank_pos
  have h2pos : 0 < Module.finrank (ResidueField A) L₂ := Module.finrank_pos
  have hr1 : Module.finrank (ResidueField A) L₁ = 1 := by omega
  have hr2 : Module.finrank (ResidueField A) L₂ = 1 := by omega
  have hrP : Module.finrank (ResidueField A) (L₁ × L₂) = 2 := by omega
  have hinj : Function.Injective φ :=
    injective_of_spanning_pair_of_finrank_eq_two φ.toLinearMap hφ hspan hrP
  exact (AlgEquiv.Algebra.isSeparable_iff (AlgEquiv.ofBijective φ ⟨hinj, hφ⟩)).mpr
    ((AlgEquiv.Algebra.isSeparable_iff
      (AlgEquiv.prodCongr (algEquivOfFinrankEqOne (ResidueField A) L₁ hr1)
        (algEquivOfFinrankEqOne (ResidueField A) L₂ hr2))).mp
      (isSeparable_prod_self (ResidueField A)))

/-- For an ideal `m` of the normalization lying over `𝔪_A`, the quotient map `A' → A' ⧸ m` factors
through the closed fibre as a residue-field algebra map. -/
private theorem exists_algHom_quadraticAlgebra_quotient (A : Type u) [CommRing A] [IsLocalRing A]
    (m : Ideal ↥(integralClosure A (FractionRing A)))
    (hcontract : maximalIdeal A = m.comap (algebraMap A ↥(integralClosure A (FractionRing A))))
    [Algebra (ResidueField A) (↥(integralClosure A (FractionRing A)) ⧸ m)]
    (hcomm : ∀ a : A, algebraMap (ResidueField A) (↥(integralClosure A (FractionRing A)) ⧸ m)
      (residue A a) = Ideal.Quotient.mk m (algebraMap A ↥(integralClosure A (FractionRing A)) a)) :
    ∃ φ : quadraticAlgebra A →ₐ[ResidueField A] (↥(integralClosure A (FractionRing A)) ⧸ m),
      ∀ x, φ (Ideal.Quotient.mk ((maximalIdeal A).map
        (algebraMap A ↥(integralClosure A (FractionRing A)))) x) = Ideal.Quotient.mk m x := by
  have hJle : (maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A))) ≤ m :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hcontract)
  refine ⟨{ Ideal.Quotient.factor hJle with commutes' := fun r => ?_ }, fun x => rfl⟩
  obtain ⟨a, rfl⟩ := residue_surjective r
  have h1 : algebraMap (ResidueField A) (quadraticAlgebra A) (residue A a)
      = Ideal.Quotient.mk ((maximalIdeal A).map
        (algebraMap A ↥(integralClosure A (FractionRing A))))
          (algebraMap A ↥(integralClosure A (FractionRing A)) a) := by
    rw [quotient_mk_algebraMap_integralClosure, Algebra.smul_def, mul_one]
  exact ((congrArg (Ideal.Quotient.factor hJle) h1).trans
    (Ideal.Quotient.factor_mk hJle _)).trans (hcomm a).symm

/-! ### Separability of the closed fibre -/

/-- The closed fibre of the normalization of a reduced Noetherian local ring of delta invariant
one with two geometric branches is separable over the residue field. -/
public theorem isSeparable_quadraticAlgebra_of_deltaInvariant_eq_one_of_two_branches
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdelta : Ring.deltaInvariant A = 1)
    (hbr : numberOfGeometricBranchesOfLocalRing A = 2) :
    Algebra.IsSeparable (ResidueField A) (quadraticAlgebra A) := by
  classical
  set C := ↥(integralClosure A (FractionRing A)) with hCdef
  set J := (maximalIdeal A).map (algebraMap A C) with hJdef
  let : IsIntegralClosure C A (FractionRing A) := integralClosure.isIntegralClosure A _
  let : Algebra.IsIntegral A C := ⟨fun x => IsIntegralClosure.isIntegral A (FractionRing A) x⟩
  have hcontract : ∀ m : MaximalSpectrum C,
      maximalIdeal A = m.asIdeal.comap (algebraMap A C) := fun m =>
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m.asIdeal)).symm
  obtain ⟨t, -, -, hli, hsp, -⟩ :=
    exists_linearIndependent_quadraticAlgebra_of_deltaInvariant_eq_one A hdelta
  have hfinF : Module.Finite (ResidueField A) (quadraticAlgebra A) :=
    Module.Finite.of_basis (Module.Basis.mk hli hsp)
  have hrankF : Module.finrank (ResidueField A) (quadraticAlgebra A) = 2 :=
    finrank_quadraticAlgebra_eq_two_of_deltaInvariant_eq_one A hdelta
  have hJne : J ≠ ⊤ :=
    map_maximalIdeal_ne_top_of_isSimpleModule A C (Module.length_eq_one_iff.mp hdelta)
  have hFnt : Nontrivial (quadraticAlgebra A) := Ideal.Quotient.nontrivial_iff.mpr hJne
  have hspan : ∀ z : quadraticAlgebra A, ∃ a b : ResidueField A,
      z = a • (1 : quadraticAlgebra A) + b • Ideal.Quotient.mk J t := by
    intro z
    have hz : z ∈ Submodule.span (ResidueField A)
        ({Ideal.Quotient.mk J t, 1} : Set (quadraticAlgebra A)) := by
      simpa [Matrix.range_cons, Matrix.range_empty] using hsp (Submodule.mem_top : z ∈ ⊤)
    obtain ⟨b, a, hab⟩ := Submodule.mem_span_pair.mp hz
    exact ⟨a, b, hab.symm.trans (add_comm _ _)⟩
  rcases encard_maximalSpectrum_integralClosure_eq_one_or_two_of_two_geometricBranches A
      (henselizationData A).carrier (strictHenselizationData A).carrier
      (SeparableClosure (ResidueField A)) hbr with h1 | h2
  · obtain ⟨m₀, hm₀⟩ := Set.encard_eq_one.mp h1
    have hsub : Subsingleton (MaximalSpectrum C) :=
      Set.subsingleton_univ_iff.mp (hm₀ ▸ Set.subsingleton_singleton)
    let : Field (C ⧸ m₀.asIdeal) := Ideal.Quotient.field m₀.asIdeal
    let : Algebra (ResidueField A) (C ⧸ m₀.asIdeal) :=
      (Ideal.quotientMap m₀.asIdeal (algebraMap A C) (le_of_eq (hcontract m₀))).toAlgebra
    obtain ⟨φ, hφ⟩ := exists_algHom_quadraticAlgebra_quotient A m₀.asIdeal (hcontract m₀)
      fun _ => rfl
    have hφsurj : Function.Surjective φ := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := m₀.asIdeal) y
      exact ⟨Ideal.Quotient.mk J x, hφ x⟩
    exact isSeparable_of_surjective_of_sepDegree_eq_two A hfinF hrankF hspan φ hφsurj
      (sepDegree_eq_two_of_subsingleton A hbr hsub m₀ (hcontract m₀))
  · obtain ⟨m₁, m₂, hne, -⟩ := Set.encard_eq_two.mp h2
    have hneI : m₁.asIdeal ≠ m₂.asIdeal := fun h => hne (MaximalSpectrum.ext h)
    have hcop : IsCoprime m₁.asIdeal m₂.asIdeal :=
      Ideal.isCoprime_iff_sup_eq.mpr (m₁.isMaximal.coprime_of_ne m₂.isMaximal hneI)
    let : Field (C ⧸ m₁.asIdeal) := Ideal.Quotient.field m₁.asIdeal
    let : Field (C ⧸ m₂.asIdeal) := Ideal.Quotient.field m₂.asIdeal
    let : Algebra (ResidueField A) (C ⧸ m₁.asIdeal) :=
      (Ideal.quotientMap m₁.asIdeal (algebraMap A C) (le_of_eq (hcontract m₁))).toAlgebra
    let : Algebra (ResidueField A) (C ⧸ m₂.asIdeal) :=
      (Ideal.quotientMap m₂.asIdeal (algebraMap A C) (le_of_eq (hcontract m₂))).toAlgebra
    obtain ⟨φ₁, hφ₁⟩ := exists_algHom_quadraticAlgebra_quotient A m₁.asIdeal (hcontract m₁)
      fun _ => rfl
    obtain ⟨φ₂, hφ₂⟩ := exists_algHom_quadraticAlgebra_quotient A m₂.asIdeal (hcontract m₂)
      fun _ => rfl
    have hφsurj : Function.Surjective (φ₁.prod φ₂) := by
      intro y
      obtain ⟨z, hz⟩ :=
        (Ideal.quotientInfEquivQuotientProd m₁.asIdeal m₂.asIdeal hcop).surjective y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := m₁.asIdeal ⊓ m₂.asIdeal) z
      refine ⟨Ideal.Quotient.mk J x, ?_⟩
      rw [← hz]
      exact Prod.ext (by simpa using hφ₁ x) (by simpa using hφ₂ x)
    exact isSeparable_of_surjective_prod A hfinF hrankF hspan (φ₁.prod φ₂) hφsurj

end Stacks.Curves

end
