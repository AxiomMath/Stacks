module

public import Mathlib.FieldTheory.Separable
public import StacksFrontier.Deformation.Basic

/-!
# Consequences of being in the classical case

The base category `𝒞_Λ` is *classical* when `Λ` is a Noetherian complete local ring whose
residue field is identified with `k` as a `Λ`-algebra. This file records the three standing
hypotheses of the chapter that such a `Λ` automatically satisfies: `Λ` is Noetherian, `k` is a
finite `Λ`-module, and `k` is separable over the image field of `Λ` — the last because the
structural map `Λ → k` is then surjective, so the image field is all of `k`.

## Main results

* `Deformation.IsClassical.surjective_algebraMap`: the structural map `Λ → k` is surjective.
* `Deformation.IsClassical.isNoetherianRing`, `Deformation.IsClassical.moduleFinite` and
  `Deformation.IsClassical.isSeparable`: the three standing hypotheses.
* `Deformation.IsClassical.residueImageField_eq_top`: the image field of `Λ` in `k` is all of `k`.

## References

* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
* [Stacks Project, Tag 06S2](https://stacks.math.columbia.edu/tag/06S2)
-/

@[expose] public section

namespace Deformation

universe u w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Over a classical base the structural map `Λ → k` is surjective: it is the residue map of
`Λ` followed by the identification of the residue field with `k`. -/
public theorem IsClassical.surjective_algebraMap (h : IsClassical Λ k) :
    Function.Surjective (algebraMap Λ k) := by
  obtain ⟨hΛ, he⟩ := h
  have : IsLocalRing Λ := hΛ.isLocal
  let e : IsLocalRing.ResidueField Λ ≃ₐ[Λ] k := he.some
  intro y
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := Λ) (e.symm y)
  exact ⟨x, by rw [← e.commutes x, IsLocalRing.ResidueField.algebraMap_eq, hx, e.apply_symm_apply]⟩

/-- A classical base ring is Noetherian. -/
public theorem IsClassical.isNoetherianRing (h : IsClassical Λ k) : IsNoetherianRing Λ :=
  h.choose.isNoetherian

/-- Over a classical base the residue field is a finite `Λ`-module, being a quotient of `Λ`. -/
public theorem IsClassical.moduleFinite (h : IsClassical Λ k) : Module.Finite Λ k :=
  Module.Finite.of_surjective (Algebra.linearMap Λ k) h.surjective_algebraMap

/-- Over a classical base the image field of `Λ` in `k` is all of `k`. -/
public theorem IsClassical.residueImageField_eq_top (h : IsClassical Λ k) :
    residueImageField Λ k = ⊤ := by
  have : IsNoetherianRing Λ := h.isNoetherianRing
  have : Module.Finite Λ k := h.moduleFinite
  refine Subfield.ext fun y => ⟨fun _ => trivial, fun _ => ?_⟩
  change y ∈ (residueImageField Λ k : Set k)
  rw [residueImageField_eq_range]
  exact h.surjective_algebraMap y

/-- Over a classical base `k` is separable over the image field of `Λ`, that image field being
all of `k`. -/
public theorem IsClassical.isSeparable (h : IsClassical Λ k) :
    Algebra.IsSeparable (residueImageField Λ k) k := by
  have : IsNoetherianRing Λ := h.isNoetherianRing
  have : Module.Finite Λ k := h.moduleFinite
  let e : residueImageField Λ k ≃ₐ[residueImageField Λ k] k :=
    AlgEquiv.ofBijective (Algebra.ofId (residueImageField Λ k) k)
      ⟨Subtype.val_injective, fun y => ⟨⟨y, h.residueImageField_eq_top ▸ Subfield.mem_top y⟩,
        rfl⟩⟩
  exact (AlgEquiv.Algebra.isSeparable_iff e).mp inferInstance

end Deformation

end
