module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.Finite.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TwoCocycleInflation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.RegularModuleAcyclic

/-!
# The additive group of an infinite Galois extension, and Artin-Schreier

Let `Ω/K` be a Galois extension, possibly infinite, and let `Gal(Ω/K)` act on the additive group
of `Ω` in the tautological way. This file proves that this Galois module has no continuous
cohomology in degrees one and two, continuity of a cochain being local constancy because `Ω` is a
discrete Galois module.

For a separably closed `Ω` of characteristic `p`, the Artin-Schreier map `℘ x = x ^ p - x` is an
additive, `Gal(Ω/K)`-equivariant, surjective endomorphism of `Ω` whose kernel is the prime field,
and the second cohomology of that kernel vanishes.

## Main definitions

* `Stacks.GaloisCohomology.artinSchreier`: the Artin-Schreier map `x ↦ x ^ p - x` of a ring of
  characteristic `p`, as an additive endomorphism.

## Main results

* `Stacks.GaloisCohomology.exists_dZero_eq_additive` and
  `Stacks.GaloisCohomology.exists_dOne_eq_additive`: the additive group of a Galois extension
  `Ω/K` has vanishing continuous `H ¹` and `H ²`. Every locally constant `1`-cocycle is
  `dZero` of an element of `Ω`, and every locally constant `2`-cocycle is `dOne` of a locally
  constant `1`-cochain.
* `Stacks.GaloisCohomology.artinSchreier_surjective`: the Artin-Schreier map `x ↦ x ^ p - x` is
  surjective on a separably closed field of characteristic `p`.
* `Stacks.GaloisCohomology.exists_dOne_eq_artinSchreier`: the second cohomology of the kernel of
  the Artin-Schreier map vanishes. A locally constant `2`-cocycle whose values satisfy
  `v ^ p = v` is `dOne` of a locally constant `1`-cochain whose values satisfy `v ^ p = v`.
* `Stacks.GaloisCohomology.isLocallyConstant_smul` and
  `Stacks.GaloisCohomology.hasOpenStabilizers`: the additive group of `Ω` is a discrete Galois
  module, i.e. every orbit map is locally constant and every stabilizer is open.
* `Stacks.GaloisCohomology.exists_finiteGaloisIntermediateField_ge`: a finite subextension and a
  finite set of elements are both contained in one finite Galois subextension.

## References

* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the vanishing of the
  Galois cohomology of the additive group of a separably closed field.
* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
-/

@[expose] public noncomputable section

open groupCohomology IntermediateField Polynomial Stacks.GroupCohomology

namespace Stacks.GaloisCohomology

/-! ### Two identities of the inhomogeneous cochain complex -/

section Cochains

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- A `1`-cochain whose coboundary vanishes is a `1`-cocycle. -/
theorem isCocycle₁_of_dOne_eq_zero {z : G → M} (hz : dOne z = 0) : IsCocycle₁ z := by
  intro g h
  have h0 : g • z h - z (g * h) + z g = 0 := congrFun hz (g, h)
  rw [sub_add_eq_add_sub, sub_eq_zero] at h0
  exact h0.symm

/-- The coboundary of a coboundary vanishes: `dOne ∘ dZero = 0`. -/
theorem dOne_dZero (b : M) : dOne (dZero (G := G) b) = 0 := by
  funext ⟨g, h⟩
  simp only [dOne_apply, dZero_apply, Pi.zero_apply, mul_smul, smul_sub]
  abel

end Cochains

/-! ### The Artin-Schreier map of a ring of characteristic `p` -/

section ArtinSchreierMap

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- The **Artin-Schreier map** `℘ x = x ^ p - x` of a commutative ring of characteristic `p`, as
an additive endomorphism. -/
def artinSchreier : R →+ R :=
  AddMonoidHom.mk' (fun x ↦ x ^ p - x) fun x y ↦ by
    rw [add_pow_char]
    abel

@[simp] lemma artinSchreier_apply (x : R) : artinSchreier R p x = x ^ p - x := rfl

end ArtinSchreierMap

/-- Elements with the same restriction to `L` differ by an element of `Gal(Ω/L)`. -/
private theorem inv_mul_mem_fixingSubgroup_of_restrictNormalHom_eq
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : FiniteGaloisIntermediateField K Ω) {g g' : Gal(Ω/K)}
    (h : AlgEquiv.restrictNormalHom ↥L g = AlgEquiv.restrictNormalHom ↥L g') :
    g⁻¹ * g' ∈ L.toIntermediateField.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker L.toIntermediateField]
  simp [MonoidHom.mem_ker, h]

/-- A function on `Gal(L/K)` pulled back along the restriction `Gal(Ω/K) → Gal(L/K)` is locally
constant. -/
private theorem isLocallyConstant_comp_restrictNormalHom {K Ω α : Type*} [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (L : FiniteGaloisIntermediateField K Ω) (f : Gal(↥L/K) → α) :
    IsLocallyConstant fun g : Gal(Ω/K) ↦ f (AlgEquiv.restrictNormalHom ↥L g) :=
  fun s ↦ (isOpen_discrete (f ⁻¹' s)).preimage
    (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField)

/-! ### Locally constant cochains come from a finite Galois level -/

section Reduction

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- A finite subextension `E/K` of `Ω/K` and a finite set of elements of `Ω` are contained in a
single finite Galois subextension. -/
theorem exists_finiteGaloisIntermediateField_ge (E : IntermediateField K Ω)
    [FiniteDimensional K E] {S : Set Ω} (hS : S.Finite) :
    ∃ L : FiniteGaloisIntermediateField K Ω, E ≤ L.toIntermediateField ∧
      ∀ x ∈ S, x ∈ L.toIntermediateField := by
  have : Finite S := hS.to_subtype
  let L₁ : FiniteGaloisIntermediateField K Ω :=
    { normalClosure K E Ω with
      finiteDimensional := normalClosure.is_finiteDimensional K E Ω
      isGalois := IsGalois.normalClosure K E Ω }
  let L₂ : FiniteGaloisIntermediateField K Ω := FiniteGaloisIntermediateField.adjoin K S
  exact ⟨L₁ ⊔ L₂, le_trans (IntermediateField.le_normalClosure E) (by exact le_sup_left),
    fun x hx ↦ (show L₂ ≤ L₁ ⊔ L₂ from le_sup_right)
      (FiniteGaloisIntermediateField.subset_adjoin K S hx)⟩

/-- A locally constant function on `Gal(Ω/K)` is unchanged when its argument is multiplied on the
right by an element of `Gal(Ω/E)`, for a single finite subextension `E/K`. -/
theorem exists_intermediateField_eq_of_isLocallyConstant_one {α : Type*} (c : Gal(Ω/K) → α)
    (hc : IsLocallyConstant c) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ a : Gal(Ω/K), a ∈ E.fixingSubgroup → c (σ * a) = c σ := by
  obtain ⟨E, hEfin, hEprop⟩ := exists_intermediateField_eq_of_isLocallyConstant
    (fun q : Gal(Ω/K) × Gal(Ω/K) ↦ c q.1) (hc.comp_continuous continuous_fst)
  exact ⟨E, hEfin, fun σ a ha ↦ hEprop σ 1 a 1 ha (one_mem _)⟩

/-- A locally constant function `Gal(Ω/K) → Ω` factors through `Gal(L/K)` and takes all its values
in `L`, for one finite Galois subextension `L/K`. -/
theorem exists_finiteGaloisIntermediateField_of_isLocallyConstant_one (c : Gal(Ω/K) → Ω)
    (hc : IsLocallyConstant c) :
    ∃ L : FiniteGaloisIntermediateField K Ω,
      (∀ σ a : Gal(Ω/K), a ∈ L.toIntermediateField.fixingSubgroup → c (σ * a) = c σ) ∧
        ∀ g : Gal(Ω/K), c g ∈ L.toIntermediateField := by
  obtain ⟨E, hEfin, hEprop⟩ := exists_intermediateField_eq_of_isLocallyConstant_one c hc
  obtain ⟨L, hEL, hSL⟩ := exists_finiteGaloisIntermediateField_ge E hc.range_finite
  exact ⟨L, fun σ a ha ↦ hEprop σ a (IntermediateField.fixingSubgroup_antitone hEL ha),
    fun g ↦ hSL _ (Set.mem_range_self g)⟩

/-- A locally constant function `Gal(Ω/K) × Gal(Ω/K) → Ω` factors through
`Gal(L/K) × Gal(L/K)` and takes all its values in `L`, for one finite Galois subextension `L/K`.
-/
theorem exists_finiteGaloisIntermediateField_of_isLocallyConstant_two
    (F : Gal(Ω/K) × Gal(Ω/K) → Ω) (hF : IsLocallyConstant F) :
    ∃ L : FiniteGaloisIntermediateField K Ω,
      (∀ σ τ a b : Gal(Ω/K), a ∈ L.toIntermediateField.fixingSubgroup →
          b ∈ L.toIntermediateField.fixingSubgroup → F (σ * a, τ * b) = F (σ, τ)) ∧
        ∀ q : Gal(Ω/K) × Gal(Ω/K), F q ∈ L.toIntermediateField := by
  obtain ⟨E, hEfin, hEprop⟩ := exists_intermediateField_eq_of_isLocallyConstant F hF
  obtain ⟨L, hEL, hSL⟩ := exists_finiteGaloisIntermediateField_ge E hF.range_finite
  exact ⟨L, fun σ τ a b ha hb ↦ hEprop σ τ a b
      (IntermediateField.fixingSubgroup_antitone hEL ha)
      (IntermediateField.fixingSubgroup_antitone hEL hb),
    fun q ↦ hSL _ (Set.mem_range_self q)⟩

/-- **The additive group of `Ω` is a discrete Galois module**: every orbit map
`g ↦ g • b` is locally constant. -/
theorem isLocallyConstant_smul (b : Ω) : IsLocallyConstant fun g : Gal(Ω/K) ↦ g • b := by
  obtain ⟨L, -, hb⟩ := exists_finiteGaloisIntermediateField_ge (⊥ : IntermediateField K Ω)
    (Set.finite_singleton b)
  have hbL : b ∈ L.toIntermediateField := hb b rfl
  have key : (fun g : Gal(Ω/K) ↦ g • b) =
      fun g ↦ algebraMap ↥L Ω (AlgEquiv.restrictNormalHom ↥L g ⟨b, hbL⟩) :=
    funext fun g ↦ (AlgEquiv.restrictNormal_commutes g ↥L ⟨b, hbL⟩).symm
  rw [key]
  exact isLocallyConstant_comp_restrictNormalHom L fun σ ↦ algebraMap ↥L Ω (σ ⟨b, hbL⟩)

/-- **The additive group of `Ω` has open stabilizers.** -/
theorem hasOpenStabilizers : HasOpenStabilizers Gal(Ω/K) Ω :=
  fun m ↦ isLocallyConstant_smul m {m}

end Reduction

/-! ### Vanishing of the cohomology of the additive group -/

section Vanishing

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- **The additive group of a Galois extension has vanishing continuous `H ¹`.** Every locally
constant `1`-cocycle `Gal(Ω/K) → Ω` is `dZero x` for some `x : Ω`. -/
theorem exists_dZero_eq_additive (c : Gal(Ω/K) → Ω) (hloc : IsLocallyConstant c)
    (hc : IsCocycle₁ c) : ∃ x : Ω, dZero x = c := by
  obtain ⟨L, hfac, hval⟩ :=
    exists_finiteGaloisIntermediateField_of_isLocallyConstant_one c hloc
  set ρ : Gal(Ω/K) →* Gal(↥L/K) := AlgEquiv.restrictNormalHom ↥L with hρ
  set ι : ↥L →+ Ω := (algebraMap ↥L Ω).toAddMonoidHom with hι
  have hιinj : Function.Injective ι := (algebraMap ↥L Ω).injective
  have hιsmul : ∀ (g : Gal(Ω/K)) (v : ↥L), ι (ρ g • v) = g • ι v := fun g v ↦
    AlgEquiv.restrictNormal_commutes g ↥L v
  have hsurj : Function.Surjective ρ := AlgEquiv.restrictNormalHom_surjective Ω
  have hwd : ∀ g g' : Gal(Ω/K), ρ g = ρ g' → c g = c g' := by
    intro g g' hgg'
    rw [show g' = g * (g⁻¹ * g') by group]
    exact (hfac g _ (inv_mul_mem_fixingSubgroup_of_restrictNormalHom_eq L hgg')).symm
  obtain ⟨C, hCe⟩ : ∃ C : Gal(↥L/K) → ↥L, ∀ g : Gal(Ω/K), ι (C (ρ g)) = c g :=
    ⟨fun σ ↦ ⟨c (Function.surjInv hsurj σ), hval _⟩, fun g ↦
      hwd _ _ (Function.surjInv_eq hsurj (ρ g))⟩
  have hCcoc : IsCocycle₁ C := by
    intro σ τ
    obtain ⟨g, rfl⟩ := hsurj σ
    obtain ⟨h, rfl⟩ := hsurj τ
    refine hιinj ?_
    rw [← map_mul ρ, map_add, hιsmul, hCe, hCe, hCe]
    exact hc g h
  obtain ⟨x, hx⟩ := exists_dZero_eq_finiteGalois K ↥L C hCcoc
  refine ⟨ι x, funext fun g ↦ ?_⟩
  have h1 := congrArg ι (congrFun hx (ρ g))
  rwa [dZero_apply, map_sub, hιsmul, hCe] at h1

/-- **The additive group of a Galois extension has vanishing continuous `H ²`.** Every locally
constant `2`-cocycle `Gal(Ω/K) × Gal(Ω/K) → Ω` is `dOne x` for a *locally constant* `1`-cochain
`x : Gal(Ω/K) → Ω`. -/
theorem exists_dOne_eq_additive (F : Gal(Ω/K) × Gal(Ω/K) → Ω) (hloc : IsLocallyConstant F)
    (hF : IsCocycle₂ F) : ∃ x : Gal(Ω/K) → Ω, IsLocallyConstant x ∧ dOne x = F := by
  obtain ⟨L, hfac, hval⟩ :=
    exists_finiteGaloisIntermediateField_of_isLocallyConstant_two F hloc
  set ρ : Gal(Ω/K) →* Gal(↥L/K) := AlgEquiv.restrictNormalHom ↥L with hρ
  set ι : ↥L →+ Ω := (algebraMap ↥L Ω).toAddMonoidHom with hι
  have hιinj : Function.Injective ι := (algebraMap ↥L Ω).injective
  have hιsmul : ∀ (g : Gal(Ω/K)) (v : ↥L), ι (ρ g • v) = g • ι v := fun g v ↦
    AlgEquiv.restrictNormal_commutes g ↥L v
  have hsurj : Function.Surjective ρ := AlgEquiv.restrictNormalHom_surjective Ω
  have hwd : ∀ g g' h h' : Gal(Ω/K), ρ g = ρ g' → ρ h = ρ h' → F (g, h) = F (g', h') := by
    intro g g' h h' hg hh
    rw [show g' = g * (g⁻¹ * g') by group, show h' = h * (h⁻¹ * h') by group]
    exact (hfac g h _ _ (inv_mul_mem_fixingSubgroup_of_restrictNormalHom_eq L hg)
      (inv_mul_mem_fixingSubgroup_of_restrictNormalHom_eq L hh)).symm
  obtain ⟨C, hCe⟩ : ∃ C : Gal(↥L/K) × Gal(↥L/K) → ↥L,
      ∀ g h : Gal(Ω/K), ι (C (ρ g, ρ h)) = F (g, h) :=
    ⟨fun q ↦ ⟨F (Function.surjInv hsurj q.1, Function.surjInv hsurj q.2), hval _⟩, fun g h ↦
      hwd _ _ _ _ (Function.surjInv_eq hsurj (ρ g)) (Function.surjInv_eq hsurj (ρ h))⟩
  have hCcoc : IsCocycle₂ C := by
    intro σ τ υ
    obtain ⟨g, rfl⟩ := hsurj σ
    obtain ⟨h, rfl⟩ := hsurj τ
    obtain ⟨k, rfl⟩ := hsurj υ
    refine hιinj ?_
    rw [map_add, map_add, hιsmul, ← map_mul ρ, ← map_mul ρ, hCe, hCe, hCe, hCe]
    exact hF g h k
  obtain ⟨y, hy⟩ := exists_dOne_eq_finiteGalois K ↥L C hCcoc
  refine ⟨fun g ↦ ι (y (ρ g)), ?_, funext fun q ↦ ?_⟩
  · exact isLocallyConstant_comp_restrictNormalHom L fun σ ↦ ι (y σ)
  · obtain ⟨g, h⟩ := q
    have h1 := congrArg ι (congrFun hy (ρ g, ρ h))
    rwa [dOne_apply, map_add, map_sub, hιsmul, hCe, ← map_mul ρ] at h1

end Vanishing

/-! ### Artin-Schreier theory -/

section ArtinSchreier

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (p : ℕ) [Fact p.Prime] [CharP Ω p]

omit [IsGalois K Ω] in
/-- The Artin-Schreier map is `Gal(Ω/K)`-equivariant. -/
theorem artinSchreier_smul (g : Gal(Ω/K)) (x : Ω) :
    artinSchreier Ω p (g • x) = g • artinSchreier Ω p x := by
  change (g x) ^ p - g x = g (x ^ p - x)
  rw [map_sub, map_pow]

omit [IsGalois K Ω] in
/-- **The kernel of the Artin-Schreier map is fixed by the Galois group**: `dZero x = 0` for every
`x` with `x ^ p - x = 0`. -/
theorem dZero_eq_zero_of_artinSchreier_eq_zero (x : Ω) (hx : x ^ p - x = 0) :
    dZero (G := Gal(Ω/K)) x = 0 := by
  have hpow : x ^ p = x := by linear_combination hx
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p Ω).1 ((Subfield.mem_bot_iff_pow_eq_self Ω p).2 hpow)
  funext g
  rw [dZero_apply, Pi.zero_apply, sub_eq_zero, ← hn]
  exact map_intCast g n

section SepClosed

variable [IsSepClosed Ω]

omit [Field K] [Algebra K Ω] [IsGalois K Ω] in
/-- **The Artin-Schreier map of a separably closed field of characteristic `p` is surjective.** -/
theorem artinSchreier_surjective (a : Ω) : ∃ b : Ω, b ^ p - b = a := by
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' p p
    (1 : Ω) (-1) (-a) dvd_rfl (Fact.out (p := p.Prime)).two_le (neg_ne_zero.2 one_ne_zero)
  exact ⟨x, by linear_combination hx⟩

/-- **The second cohomology of the kernel of the Artin-Schreier map vanishes.** A locally
constant `2`-cocycle `F` of `Gal(Ω/K)` all of whose values `v` satisfy `v ^ p - v = 0` is `dOne x`
for a locally constant `1`-cochain `x` all of whose values satisfy the same condition. -/
theorem exists_dOne_eq_artinSchreier (F : Gal(Ω/K) × Gal(Ω/K) → Ω)
    (hloc : IsLocallyConstant F) (hF : IsCocycle₂ F) (hker : ∀ q, (F q) ^ p - F q = 0) :
    ∃ x : Gal(Ω/K) → Ω, IsLocallyConstant x ∧ (∀ g, (x g) ^ p - x g = 0) ∧ dOne x = F := by
  obtain ⟨φ, hφ, hequiv⟩ : ∃ φ : Ω →+ Ω, (∀ y : Ω, φ y = y ^ p - y) ∧
      ∀ (g : Gal(Ω/K)) (y : Ω), φ (g • y) = g • φ y :=
    ⟨artinSchreier Ω p, fun _ ↦ rfl, artinSchreier_smul p⟩
  obtain ⟨x, hxloc, hx⟩ := exists_dOne_eq_additive F hloc hF
  have hzloc : IsLocallyConstant fun g : Gal(Ω/K) ↦ φ (x g) := hxloc.comp fun y ↦ φ y
  have hz : dOne (fun g : Gal(Ω/K) ↦ φ (x g)) = 0 := by
    rw [← dOne_map φ hequiv x, hx]
    exact funext fun q ↦ (hφ _).trans (hker q)
  obtain ⟨a, ha⟩ := exists_dZero_eq_additive (fun g : Gal(Ω/K) ↦ φ (x g)) hzloc
    (isCocycle₁_of_dOne_eq_zero hz)
  obtain ⟨b, hb⟩ := artinSchreier_surjective p a
  have hφb : φ b = a := by rwa [hφ]
  have hdb : ∀ g : Gal(Ω/K), φ (dZero (G := Gal(Ω/K)) b g) = φ (x g) := by
    intro g
    have h1 := congrFun (dZero_map φ hequiv b) g
    rw [Function.comp_apply, hφb] at h1
    rw [h1, congrFun ha g]
  refine ⟨fun g ↦ x g - dZero (G := Gal(Ω/K)) b g,
    hxloc.comp₂ (isLocallyConstant_dZero hasOpenStabilizers b) (· - ·), fun g ↦ ?_,
    funext fun q ↦ ?_⟩
  · rw [← hφ, map_sub, hdb, sub_self]
  · obtain ⟨g, h⟩ := q
    have h0 := congrFun (dOne_dZero (G := Gal(Ω/K)) b) (g, h)
    have h1 := congrFun hx (g, h)
    simp only [dOne_apply, Pi.zero_apply, smul_sub] at h0 h1 ⊢
    linear_combination h1 - h0

end SepClosed

end ArtinSchreier

end Stacks.GaloisCohomology

end
