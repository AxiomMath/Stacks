module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence

/-!
# Regular immersions are local complete intersection morphisms

A Koszul-regular immersion of schemes, and hence also a regular immersion, is a local complete
intersection morphism in the sense of Stacks 069F: this is **Stacks 069L**.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_isKoszulRegularImmersion` — a
  Koszul-regular immersion is a local complete intersection morphism.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_isRegularImmersion` — a regular
  immersion is a local complete intersection morphism.

## Implementation notes

Being Koszul at a point asks for a factorisation of the morphism, restricted to a neighbourhood
of that point, as a Koszul-regular immersion followed by a smooth morphism. For an immersion the
factorisation is the morphism itself followed by the identity of the target, read as the inclusion
of its top open, which is an isomorphism and hence smooth; Koszul-regularity of that restriction
is `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_resLE`. Finite type at the
point comes from the finite-type ring map an immersion induces on affine opens.

## References

* [Stacks Project, Tag 069L](https://stacks.math.columbia.edu/tag/069L)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Tag 063J](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Tag 063K](https://stacks.math.columbia.edu/tag/063K)
-/

@[expose] public section

open CategoryTheory Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- **Stacks 069L.** A Koszul-regular immersion of schemes is a local complete intersection
morphism. -/
@[stacks 069L "Koszul-regular immersion", sga "5 III 6.8" "Direction"]
theorem isLocalCompleteIntersectionMorphism_of_isKoszulRegularImmersion {X S : Scheme.{u}}
    (i : X ⟶ S) [IsImmersion i] (hi : IsKoszulRegularImmersion i) :
    IsLocalCompleteIntersectionMorphism i := by
  intro x
  refine ⟨?_, ?_⟩
  · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i.base x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU (i ⁻¹ᵁ U).2
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, i.finiteType_appLE hU hV hVU⟩
  refine ⟨i ⁻¹ᵁ ⊤, by simp, _, i.resLE ⊤ (i ⁻¹ᵁ ⊤) le_rfl, (⊤ : S.Opens).ι, by infer_instance,
    ?_, ?_, ?_⟩
  · exact isKoszulRegularImmersion_resLE i hi ⊤
  · infer_instance
  · exact (Scheme.Hom.resLE_comp_ι i le_rfl).symm

/-- **Stacks 069L.** A regular immersion of schemes is a local complete intersection
morphism. -/
@[stacks 069L "regular immersion", sga "5 III 6.8" "Direction"]
theorem isLocalCompleteIntersectionMorphism_of_isRegularImmersion {X S : Scheme.{u}}
    (i : X ⟶ S) [IsImmersion i] (hi : IsRegularImmersion i) :
    IsLocalCompleteIntersectionMorphism i :=
  isLocalCompleteIntersectionMorphism_of_isKoszulRegularImmersion i
    (isKoszulRegularImmersion_of_isRegularImmersion i hi)

end AlgebraicGeometry

end
