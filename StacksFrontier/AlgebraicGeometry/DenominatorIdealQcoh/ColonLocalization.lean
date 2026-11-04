module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The colon ideal of a principal ideal commutes with localization

Let `R` be a commutative ring, let `a b : R` and let `S` be a localization of `R` at a submonoid
`p`.  The colon ideal `(b R : a) = {g | g a ∈ b R}` is the set of denominators of the fraction
`a / b`, and this file proves that it commutes with localization: an element of `S` whose product
with the image of `a` is a multiple of the image of `b` is, up to a factor from `p`, the image of
such an element of `R`.

The second half turns that into a criterion for a localization of modules.  Suppose `M` and `M'`
are `R`-modules embedded `R`-linearly in `R` and in `S` with images the two colon ideals, and
compatibly with a map `φ : M →ₗ[R] M'`.  Then `φ` exhibits `M'` as the localization of `M` at
`p`.  This is the shape in which the denominator ideal of a meromorphic section is presented on
an affine open and on its basic opens, and it is what makes that ideal quasi-coherent.

Nothing here is about schemes.

## Main results

* `Stacks.ColonLocalization.exists_mem_colon`: the colon ideal commutes with localization.
* `Stacks.ColonLocalization.isLocalizedModule_of_range_eq_colon`: a map of modules whose two
  embeddings have the two colon ideals as images is a localization.

## Implementation notes

`Submodule.colon` is Mathlib's colon ideal and `Mathlib.RingTheory.Ideal.Colon` develops its
lattice-theoretic properties, but there is no localization result for it in Mathlib (where
`colon` occurs in four `RingTheory` files, none about localization), and the colon ideal is not
how the geometric statement presents itself either — there it is the set of `g` with
`g a = b u` for some `u`, which is `(Ideal.span {b}).colon {a}` only after unfolding two
definitions.  So the set is written out literally here, in the same shape as
`Stacks.DenominatorColonIdeal.range_denominatorIdealι_app_eq`, and the proof is the direct
element computation: clear the denominators of `g` and of `u`, use that the two sides agree in
`S` to get an equation in `R` up to a factor from `p`, and multiply that factor back in.

The module criterion checks the three fields of `IsLocalizedModule` by hand rather than
transporting `Submodule.isLocalizedModule` across the embeddings: the colon ideal is a
submodule of the ring rather than a submodule of the module being localized, so the transport
would need the embeddings to be isomorphisms onto the two colon ideals as bundled submodules,
which is more data than the images-are-equal hypotheses used here.
-/

@[expose] public section

universe u

namespace Stacks.ColonLocalization

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : Submonoid R)
  [IsLocalization p S]

/-- **The colon ideal of a principal ideal commutes with localization.**  If `g : S` satisfies
`g a = b u` in the localization `S`, then some `t`-multiple of `g`, with `t ∈ p`, is the image of
an element `g₀` of `R` satisfying the same relation `g₀ a = b v` in `R`.

Together with the obvious inclusion in the other direction this says that the colon ideal
`(b S : a)` of the localization is the localization of the colon ideal `(b R : a)`. -/
theorem exists_mem_colon {a b : R} {g : S} (u : S)
    (hu : g * algebraMap R S a = algebraMap R S b * u) :
    ∃ (g₀ : R) (t : p), (∃ v : R, g₀ * a = b * v) ∧
      algebraMap R S g₀ = algebraMap R S (t : R) * g := by
  obtain ⟨⟨g₀, t₁⟩, hg₀⟩ := IsLocalization.surj p g
  obtain ⟨⟨u₀, t₂⟩, hu₀⟩ := IsLocalization.surj p u
  have key : algebraMap R S (g₀ * a * (t₂ : R)) = algebraMap R S (b * u₀ * (t₁ : R)) := by
    simp only [map_mul]
    calc algebraMap R S g₀ * algebraMap R S a * algebraMap R S (t₂ : R)
        = g * algebraMap R S a * (algebraMap R S (t₁ : R) * algebraMap R S (t₂ : R)) := by
          rw [← hg₀]; ring
      _ = algebraMap R S b * u * (algebraMap R S (t₁ : R) * algebraMap R S (t₂ : R)) := by
          rw [hu]
      _ = algebraMap R S b * (u * algebraMap R S (t₂ : R)) * algebraMap R S (t₁ : R) := by ring
      _ = algebraMap R S b * algebraMap R S u₀ * algebraMap R S (t₁ : R) := by rw [hu₀]
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (S := S) (M := p) key
  have hcol : (c : R) * (t₂ : R) * g₀ * a = b * ((c : R) * u₀ * (t₁ : R)) :=
    calc (c : R) * (t₂ : R) * g₀ * a = (c : R) * (g₀ * a * (t₂ : R)) := by ring
      _ = (c : R) * (b * u₀ * (t₁ : R)) := hc
      _ = b * ((c : R) * u₀ * (t₁ : R)) := by ring
  refine ⟨(c : R) * (t₂ : R) * g₀, c * t₂ * t₁, ⟨_, hcol⟩, ?_⟩
  simp only [Submonoid.coe_mul, map_mul]
  rw [← hg₀]
  ring

variable {M M' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- **A map of modules whose two embeddings have the two colon ideals as images is a
localization.**  Let `j : M →ₗ[R] R` and `j' : M' →ₗ[R] S` be injective, compatible with
`φ : M →ₗ[R] M'` over the localization map, and with images the colon ideals `(b R : a)` and
`(b S : a)`.  Then `φ` exhibits `M'` as the localization of `M` at `p`.

The surjectivity field is where `Stacks.ColonLocalization.exists_mem_colon` enters; the other
two fields are formal consequences of the two embeddings and of `S` being a localization. -/
theorem isLocalizedModule_of_range_eq_colon (φ : M →ₗ[R] M') (j : M →ₗ[R] R) (j' : M' →ₗ[R] S)
    (hj : Function.Injective j) (hj' : Function.Injective j')
    (hcomm : ∀ x : M, j' (φ x) = algebraMap R S (j x)) {a b : R}
    (hrange : Set.range j = {g : R | ∃ v : R, g * a = b * v})
    (hrange' : Set.range j' =
      {g : S | ∃ v : S, g * algebraMap R S a = algebraMap R S b * v}) :
    IsLocalizedModule p φ where
  map_units t := by
    rw [Module.End.isUnit_iff]
    obtain ⟨w, hw⟩ := IsLocalization.map_units (M := p) S t
    refine ⟨fun y z hyz => ?_, fun y => ?_⟩
    · simp only [Module.algebraMap_end_apply] at hyz
      refine hj' ((IsLocalization.map_units (M := p) S t).mul_left_cancel ?_)
      have h := congrArg j' hyz
      rwa [map_smul, map_smul, Algebra.smul_def, Algebra.smul_def] at h
    · have hy : j' y ∈ Set.range j' := ⟨y, rfl⟩
      rw [hrange'] at hy
      obtain ⟨v, hv⟩ := hy
      have hmem : ((w⁻¹ : Sˣ) : S) * j' y ∈ Set.range j' := by
        rw [hrange']
        exact ⟨((w⁻¹ : Sˣ) : S) * v, by rw [mul_assoc, hv]; ring⟩
      obtain ⟨z, hz⟩ := hmem
      refine ⟨z, hj' ?_⟩
      rw [Module.algebraMap_end_apply, map_smul, Algebra.smul_def, hz, ← hw, ← mul_assoc,
        Units.mul_inv, one_mul]
  surj y := by
    have hy : j' y ∈ Set.range j' := ⟨y, rfl⟩
    rw [hrange'] at hy
    obtain ⟨v, hv⟩ := hy
    obtain ⟨g₀, t, hcol, hg₀⟩ := exists_mem_colon p v hv
    have hg : g₀ ∈ Set.range j := by rw [hrange]; exact hcol
    obtain ⟨x, hx⟩ := hg
    refine ⟨⟨x, t⟩, hj' ?_⟩
    rw [hcomm x, hx, Submonoid.smul_def, map_smul, Algebra.smul_def]
    exact hg₀.symm
  exists_of_eq {x₁ x₂} h := by
    have h1 : algebraMap R S (j x₁) = algebraMap R S (j x₂) := by
      rw [← hcomm, ← hcomm, h]
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (S := S) (M := p) h1
    refine ⟨c, hj ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    exact hc

end Stacks.ColonLocalization

end
