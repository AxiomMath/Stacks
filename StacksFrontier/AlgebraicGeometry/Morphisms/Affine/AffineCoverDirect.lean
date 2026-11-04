module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# A direct proof that affineness of a morphism is checked on an affine open covering

Let `f : X ⟶ S` be a morphism of schemes and let `S = ⋃ⱼ Wⱼ` be a covering by affine opens
such that every `f⁻¹(Wⱼ)` is affine. Then `f` is affine. The argument is direct. Let
`V ⊆ S` be affine open, put `R = Γ(S, V)` and `A = Γ(X, f⁻¹(V))`. Every point of `V` lies in a
standard open `D(h)`, `h ∈ R`, which is at the same time a standard open `D(g)` of some
affine `Wⱼ`. The inverse image of a standard open is a standard open, so
`f⁻¹(D(h)) = D(f^♯ h)` is a standard open of the affine scheme `f⁻¹(Wⱼ)` and hence is affine.
These `h` generate the unit ideal of `R`, so their images `f^♯ h` generate the unit ideal of
`A`, and `f⁻¹(V)` is covered by the affine standard opens `D(f^♯ h)`. Since
`Γ(X, D(f^♯ h)) = A_{f^♯ h}`, the canonical morphism `ψ : f⁻¹(V) → Spec(A)` restricts to an
isomorphism `D(f^♯ h) ≅ Spec(A_{f^♯ h})` for each such `h`, hence is an isomorphism, i.e.
`f⁻¹(V)` is affine.

## Main results

* `AlgebraicGeometry.isAffineOpen_preimage_of_le_iSup_affine`: if `V` is an affine open
  contained in the union of affine opens `Wⱼ` with affine inverse images, then `f⁻¹(V)` is
  affine.
* `AlgebraicGeometry.isAffineHom_of_iSup_eq_top_of_isAffineOpen_preimage`: a morphism is
  affine as soon as its target has an affine open covering with affine inverse images.

## Implementation notes

The covering of `V` by standard opens is not made finite: it is indexed by the set of all
`h ∈ Γ(S, V)` whose standard open is also a standard open of some `Wⱼ`. That this set
generates the unit ideal is `AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff`.
The last step, that an open whose global sections are generated, as an ideal, by sections
with affine standard opens is affine (the canonical morphism `ψ` to the spectrum of its
global sections being an isomorphism, since `Γ` of those standard opens is the localization
of `A`), is `AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen` (Stacks, Tag 01QF).
In place of the quasi-coherence of `f_* 𝒪_X` used in the source, the identification
`Γ(X, D(f^♯ h)) = A_{f^♯ h}` comes from the quasi-compactness and quasi-separatedness that
this cover gives `f⁻¹(V)`.

## References

* [Stacks Project, Tag 01S9](https://stacks.math.columbia.edu/tag/01S9)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public section

open TopologicalSpace CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Let `Wⱼ` be affine opens of `S` with affine inverse images under `f : X ⟶ S`. Then the
inverse image of every affine open `V ⊆ ⋃ⱼ Wⱼ` is affine. -/
lemma isAffineOpen_preimage_of_le_iSup_affine {ι : Type*} (W : ι → S.Opens)
    (hW : ∀ j, IsAffineOpen (W j)) (hfW : ∀ j, IsAffineOpen (f ⁻¹ᵁ W j))
    {V : S.Opens} (hV : IsAffineOpen V) (hVW : V ≤ ⨆ j, W j) :
    IsAffineOpen (f ⁻¹ᵁ V) := by
  -- The sections `h ∈ Γ(S, V)` whose standard open is also a standard open of some `Wⱼ`.
  let s : Set Γ(S, V) := {h | ∃ j, ∃ g : Γ(S, W j), S.basicOpen h = S.basicOpen g}
  -- Their standard opens cover `V`, so they generate the unit ideal of `Γ(S, V)`.
  have hs : Ideal.span s = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hVW hx)
    obtain ⟨h, g, e, hxh⟩ := exists_basicOpen_le_affine_inter hV (hW j) x ⟨hx, hj⟩
    exact Opens.mem_iSup.mpr ⟨⟨h, j, g, e⟩, hxh⟩
  -- The inverse image of each such standard open is a standard open of an affine
  -- `f⁻¹(Wⱼ)`, hence affine.
  refine isAffineOpen_of_isAffineOpen_basicOpen (f ⁻¹ᵁ V) (f.app V '' s) ?_ ?_
  · rw [← Ideal.map_span, hs, Ideal.map_top]
  · rintro _ ⟨h, ⟨j, g, e⟩, rfl⟩
    rw [← Scheme.preimage_basicOpen, e, Scheme.preimage_basicOpen]
    exact (hfW j).basicOpen _

/-- **Stacks Project, Tag 01S9.** If `S = ⋃ⱼ Wⱼ` is an affine open covering such that each
`f⁻¹(Wⱼ)` is affine, then `f : X ⟶ S` is affine. -/
@[stacks 01S9]
lemma isAffineHom_of_iSup_eq_top_of_isAffineOpen_preimage {ι : Type*} (W : ι → S.Opens)
    (hW : ∀ j, IsAffineOpen (W j)) (hcov : ⨆ j, W j = ⊤)
    (hfW : ∀ j, IsAffineOpen (f ⁻¹ᵁ W j)) :
    IsAffineHom f :=
  ⟨fun _ hV ↦ isAffineOpen_preimage_of_le_iSup_affine f W hW hfW hV (hcov ▸ le_top)⟩

end AlgebraicGeometry
