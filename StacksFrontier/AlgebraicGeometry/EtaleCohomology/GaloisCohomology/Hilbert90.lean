module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.Topology.LocallyConstant.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hilbert 90 for an infinite Galois extension

For `Ω/K` any Galois extension, a locally constant `1`-cocycle on `Gal(Ω/K)` with values in
`Ωˣ` is a coboundary. This extends Noether's form of Hilbert's theorem 90 for finite extensions,
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`.

Since `Ωˣ` carries the discrete topology as a Galois module, `IsLocallyConstant` is exactly
continuity of the cocycle for the Krull topology on `Gal(Ω/K)`
(`IsLocallyConstant.iff_continuous`), so the statement proved here is the vanishing of the first
*continuous* cohomology group `H¹(Gal(Ω/K), Ωˣ)`.

## Main results

* `Stacks.GaloisCohomology.isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁`: Hilbert 90
  for an arbitrary Galois extension `Ω/K`; `isMulCoboundary₁_of_continuous_of_isMulCocycle₁` is
  the same statement with the cochain condition spelled as continuity.
* `Stacks.GaloisCohomology.isMulCoboundary₁_separableClosure`: the case `Ω = Kˢᵉᵖ`, i.e. the
  vanishing of `H¹(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)` for the absolute Galois group of `K`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
-/

@[expose] public section

open groupCohomology IntermediateField

namespace Stacks.GaloisCohomology

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- A locally constant `1`-cocycle on `Gal(Ω/K)` is trivial on `Gal(Ω/L)` for some finite normal
subextension `L/K`. -/
theorem exists_intermediateField_of_isLocallyConstant (f : Gal(Ω/K) → Ωˣ)
    (hloc : IsLocallyConstant f) (hf : IsMulCocycle₁ f) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧
      ∀ g : Gal(Ω/K), g ∈ L.fixingSubgroup → f g = 1 := by
  have h1 : (1 : Gal(Ω/K)) ∈ f ⁻¹' {1} := by
    simpa using map_one_of_isMulCocycle₁ hf
  obtain ⟨L, hfin, hnor, hsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K Ω _).1 ((hloc {1}).mem_nhds h1)
  exact ⟨L, hfin, hnor, fun g hg ↦ hsub hg⟩

/-- A `1`-cocycle on `Gal(Ω/K)` that is trivial on `Gal(Ω/L)`, for `L/K` a finite normal
subextension, takes its values in `L`. -/
theorem coe_mem_of_isMulCocycle₁ (f : Gal(Ω/K) → Ωˣ) (hf : IsMulCocycle₁ f)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    (hL : ∀ g : Gal(Ω/K), g ∈ L.fixingSubgroup → f g = 1) (g : Gal(Ω/K)) :
    (f g : Ω) ∈ L := by
  have hnormal : (L.fixingSubgroup).Normal := L.restrictNormalHom_ker ▸ MonoidHom.normal_ker _
  have key : ∀ h ∈ L.fixingSubgroup, h (f g : Ω) = (f g : Ω) := by
    intro h hh
    have hconj : g⁻¹ * h * g ∈ L.fixingSubgroup := by
      simpa using hnormal.conj_mem h hh g⁻¹
    have e₁ : f (h * g) = h • f g := by rw [hf h g, hL h hh, mul_one]
    have e₂ : f (h * g) = f g := by
      rw [show h * g = g * (g⁻¹ * h * g) by group, hf g (g⁻¹ * h * g), hL _ hconj]
      simp
    simpa using congrArg Units.val (e₁.symm.trans e₂)
  rwa [← InfiniteGalois.fixedField_fixingSubgroup L, mem_fixedField_iff]

/-- **Hilbert's theorem 90** for an arbitrary Galois extension `Ω/K`: a locally constant
`1`-cocycle `f : Gal(Ω/K) → Ωˣ` is a coboundary, i.e. there is `β : Ωˣ` with `g β / β = f g` for
every `g`. -/
@[sga "4½ Arcata 1.5.3" "more general"]
theorem isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁ (f : Gal(Ω/K) → Ωˣ)
    (hloc : IsLocallyConstant f) (hf : IsMulCocycle₁ f) : IsMulCoboundary₁ f := by
  obtain ⟨L, hfin, hnor, hL⟩ := exists_intermediateField_of_isLocallyConstant f hloc hf
  set ρ : Gal(Ω/K) →* Gal(↥L/K) := AlgEquiv.restrictNormalHom ↥L with hρ
  set ι : Lˣ →* Ωˣ := Units.map (algebraMap ↥L Ω).toMonoidHom with hι
  have hιinj : Function.Injective ι := Units.map_injective (algebraMap ↥L Ω).injective
  have hιsmul : ∀ (g : Gal(Ω/K)) (v : Lˣ), ι (ρ g • v) = g • ι v :=
    fun g v ↦ Units.ext (AlgEquiv.restrictNormal_commutes g ↥L (v : ↥L))
  have hmem : ∀ g : Gal(Ω/K), ∃ v : Lˣ, ι v = f g := by
    intro g
    have hne : (⟨(f g : Ω), coe_mem_of_isMulCocycle₁ f hf L hL g⟩ : ↥L) ≠ 0 := by
      simp only [ne_eq, ← ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true]
    exact ⟨Units.mk0 _ hne, by ext; rfl⟩
  choose u hu using hmem
  have hwd : ∀ g g' : Gal(Ω/K), ρ g = ρ g' → f g = f g' := by
    intro g g' h
    have hker : g⁻¹ * g' ∈ L.fixingSubgroup := by
      rw [← L.restrictNormalHom_ker]
      simp [MonoidHom.mem_ker, ← hρ, h]
    rw [show g' = g * (g⁻¹ * g') by group, hf g (g⁻¹ * g'), hL _ hker]
    simp
  have huwd : ∀ g g' : Gal(Ω/K), ρ g = ρ g' → u g = u g' :=
    fun g g' h ↦ hιinj ((hu g).trans ((hwd g g' h).trans (hu g').symm))
  have hsurj : Function.Surjective ρ := AlgEquiv.restrictNormalHom_surjective Ω
  set F : Gal(↥L/K) → Lˣ := fun σ ↦ u (Function.surjInv hsurj σ) with hF
  have hFρ : ∀ g : Gal(Ω/K), F (ρ g) = u g :=
    fun g ↦ huwd _ _ (Function.surjInv_eq hsurj (ρ g))
  have hFcocycle : IsMulCocycle₁ F := by
    intro σ τ
    obtain ⟨g, rfl⟩ := hsurj σ
    obtain ⟨g', rfl⟩ := hsurj τ
    refine hιinj ?_
    rw [← map_mul ρ, hFρ, hFρ, hFρ, map_mul ι, hιsmul, hu, hu, hu, hf g g']
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units F hFcocycle
  refine ⟨ι β, fun g ↦ ?_⟩
  rw [← hu g, ← hFρ g, ← hβ (ρ g), map_div ι, hιsmul]

/-- **Hilbert's theorem 90** for an arbitrary Galois extension `Ω/K`, with the cochain condition
spelled as continuity rather than local constancy. -/
theorem isMulCoboundary₁_of_continuous_of_isMulCocycle₁ [TopologicalSpace Ωˣ]
    [DiscreteTopology Ωˣ] (f : Gal(Ω/K) → Ωˣ) (hcont : Continuous f) (hf : IsMulCocycle₁ f) :
    IsMulCoboundary₁ f :=
  isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁ f
    ((IsLocallyConstant.iff_continuous f).2 hcont) hf

variable (K) in
/-- **Hilbert's theorem 90** for the absolute Galois group: the first continuous cohomology of
`Gal(Kˢᵉᵖ/K)` acting on `(Kˢᵉᵖ)ˣ` vanishes, i.e. every locally constant `1`-cocycle
`Gal(Kˢᵉᵖ/K) → (Kˢᵉᵖ)ˣ` is a coboundary. -/
theorem isMulCoboundary₁_separableClosure
    (f : Gal(SeparableClosure K/K) → (SeparableClosure K)ˣ) (hloc : IsLocallyConstant f)
    (hf : IsMulCocycle₁ f) : IsMulCoboundary₁ f :=
  isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁ f hloc hf

end Stacks.GaloisCohomology
