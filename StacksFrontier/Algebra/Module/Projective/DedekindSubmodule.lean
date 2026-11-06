module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Examples

/-!
# Submodules of projective modules over a Dedekind domain

Over a Dedekind domain every module has projective dimension at most one (Stacks 0EX0), so a
submodule `B` of a projective module `F` is projective: in the short exact sequence
`0 → B → F → F/B → 0` the quotient has projective dimension at most one and the middle term is
projective.

Consequently an exact sequence `0 → L₀ → L₁ → L₂ → ⋯` of projective modules over a Dedekind
domain is split: every image is a submodule of a projective module, hence projective, so each
short exact sequence `0 → im dₙ₋₁ → Lₙ → im dₙ → 0` splits, and the splittings assemble into a
contracting homotopy.

## Main results

* `Module.projective_submodule_of_isDedekindDomain`: a submodule of a projective module over a
  Dedekind domain is projective.
* `Module.exists_contraction_of_isDedekindDomain`: an exact sequence of projective modules over a
  Dedekind domain, starting with an injective map, has a contracting homotopy.

## References

* [Stacks Project, Tag 0EX0](https://stacks.math.columbia.edu/tag/0EX0)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsDedekindDomain R] [Small.{v} R]

/-- **A submodule of a projective module over a Dedekind domain is projective.** -/
theorem projective_submodule_of_isDedekindDomain {F : Type v} [AddCommGroup F] [Module R F]
    [Module.Projective R F] (B : Submodule R F) : Module.Projective R B := by
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk (ModuleCat.ofHom B.subtype) (ModuleCat.ofHom B.mkQ) (by ext; simp)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
        (LinearMap.exact_subtype_mkQ B)
      mono_f := (ModuleCat.mono_iff_injective _).2 B.injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).2 B.mkQ_surjective }
  have h₂ : CategoryTheory.Projective S.X₂ := (IsProjective.iff_projective F).1 inferInstance
  exact (IsProjective.iff_projective B).2 <| projective_iff_hasProjectiveDimensionLT_one.2 <|
    hS.hasProjectiveDimensionLT_X₁ 1 inferInstance <| .mk fun i hi Y e ↦
      ((StacksDraft.InjectiveDimension.dedekindDomain_ideal_projective_and_bounded_complex_splitting
        R).2.2.2.1 S.X₃ Y i hi).elim e 0

/-- **An exact sequence of projective modules over a Dedekind domain is contractible.** Let
`0 → L₀ → L₁ → L₂ → ⋯` be exact, with every `Lₙ` projective. Then there are maps
`sₙ : Lₙ₊₁ → Lₙ` with `s₀ ∘ d₀ = id` and `dₙ ∘ sₙ + sₙ₊₁ ∘ dₙ₊₁ = id`. -/
theorem exists_contraction_of_isDedekindDomain {L : ℕ → Type v} [∀ n, AddCommGroup (L n)]
    [∀ n, Module R (L n)] [∀ n, Module.Projective R (L n)] (d : ∀ n, L n →ₗ[R] L (n + 1))
    (hdd : ∀ n x, d (n + 1) (d n x) = 0) (h0 : Function.Injective (d 0))
    (hex : ∀ n x, d (n + 1) x = 0 → ∃ y, d n y = x) :
    ∃ s : ∀ n, L (n + 1) →ₗ[R] L n,
      (∀ x, s 0 (d 0 x) = x) ∧ ∀ n x, d n (s n x) + s (n + 1) (d (n + 1) x) = x := by
  -- sections of the corestrictions `Lₙ → im dₙ`, which exist as the images are projective
  have hσ : ∀ n, ∃ σ : LinearMap.range (d n) →ₗ[R] L n,
      (d n).rangeRestrict ∘ₗ σ = LinearMap.id := fun n ↦
    have := projective_submodule_of_isDedekindDomain (d n).range
    Module.projective_lifting_property _ _ (LinearMap.surjective_rangeRestrict _)
  choose σ hσ using hσ
  have hσ' : ∀ n (y : LinearMap.range (d n)), d n (σ n y) = y := fun n y ↦
    congrArg Subtype.val (LinearMap.congr_fun (hσ n) y)
  -- the projection of `Lₙ₊₁` onto `im dₙ` along the image of `σₙ₊₁`
  have hρ : ∀ n (x : L (n + 1)),
      x - σ (n + 1) ((d (n + 1)).rangeRestrict x) ∈ LinearMap.range (d n) := fun n x ↦
    hex n _ (by
      rw [map_sub, hσ' (n + 1)]
      simp)
  let ρ : ∀ n, L (n + 1) →ₗ[R] LinearMap.range (d n) := fun n ↦
    (LinearMap.id - σ (n + 1) ∘ₗ (d (n + 1)).rangeRestrict).codRestrict _ (hρ n)
  have hρ_apply : ∀ n x, (ρ n x : L (n + 1)) =
      x - σ (n + 1) ((d (n + 1)).rangeRestrict x) := fun _ _ ↦ rfl
  -- `ρ` fixes the image of `d`
  have hρd : ∀ n x, ρ n (d n x) = (d n).rangeRestrict x := by
    intro n x
    apply Subtype.ext
    rw [hρ_apply, show (d (n + 1)).rangeRestrict (d n x) = 0 from Subtype.ext (hdd n x),
      map_zero, sub_zero]
    rfl
  refine ⟨fun n ↦ σ n ∘ₗ ρ n, fun x ↦ ?_, fun n x ↦ ?_⟩
  · apply h0
    simp only [LinearMap.coe_comp, Function.comp_apply, hρd, hσ']
    rfl
  · simp only [LinearMap.coe_comp, Function.comp_apply, hσ', hρ_apply, hρd]
    abel

end Module
