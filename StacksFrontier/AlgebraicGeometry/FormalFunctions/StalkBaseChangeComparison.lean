module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalBaseIdealSections
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.PushforwardStalkBaseChange

/-!
# The canonical comparison from the stalk to the base change is an isomorphism

`StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalBaseIdealSections.lean` builds the
canonical ring map

  `Stacks.FormalFunctions.stalkBaseChangeRestrictHom f y : (f_* 𝒪_X)_y ⟶ Γ(X', 𝒪_{X'})`,
  `X' = X ×_Y Spec 𝒪_{Y,y}`,

out of the pullbacks of functions defined near `y`, and shows that every canonical restriction
map `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪)` to an infinitesimal neighbourhood of the fibre factors through it.
`StacksFrontier/AlgebraicGeometry/FormalFunctions/PushforwardStalkBaseChange.lean` proves, for `f`
quasi-compact and quasi-separated, that the two sides are isomorphic by an isomorphism with the
same normalisation on germs.

This file puts the two together: **the canonical map itself is bijective**. Both facts are
needed — an unnamed isomorphism of the two sides would not let a statement about
`stalkBaseChangeRestrictHom` be transported, and the factorization of the restriction maps is
stated in terms of that map and no other.

## Main results

* `Stacks.FormalFunctions.bijective_stalkBaseChangeRestrictHom` — the canonical map
  `(f_* 𝒪_X)_y ⟶ Γ(X ×_Y Spec 𝒪_{Y,y}, 𝒪)` is bijective for `f` quasi-compact and
  quasi-separated. This is [Stacks, Tag 02KH] part (1) at `i = 0` for the flat morphism
  `Spec 𝒪_{Y,y} ⟶ Y`, in the shape the theorem on formal functions consumes it.
* `Stacks.FormalFunctions.isIso_stalkBaseChangeRestrictHom` — the same as an `IsIso` instance.

## Implementation notes

The proof is the only thing a normalisation is for. Writing `e` for the isomorphism of
`PushforwardStalkBaseChange.lean` and `θ` for the canonical map, both normalisations say what
happens to a germ, so `e ∘ θ` is the identity on germs; every element of the stalk is a germ
(`Stacks.FormalFunctions.exists_pushforwardStalkGerm_eq`), so `e ∘ θ = id`, and since `e` is
already bijective so is `θ`.

The two statements of "the base change lies over `f ⁻¹ᵁ U`" —
`Stacks.FormalFunctions.top_le_preimage_stalkBaseChangeι` and
`Stacks.FormalFunctions.top_le_preimage_pullbackFst` — are the same proposition about the same
morphism, proved twice; `Scheme.Hom.appLE` does not depend on which proof is supplied, so the
two spellings of the pullback of a section agree definitionally.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FormalFunctions

variable {X Y : Scheme.{u}}

/-- **The canonical map `(f_* 𝒪_X)_y ⟶ Γ(X ×_Y Spec 𝒪_{Y,y}, 𝒪)` is bijective.** This is
degree-zero flat base change along `Spec 𝒪_{Y,y} ⟶ Y`, [Stacks, Tag 02KH] part (1) at `i = 0`,
for the canonical comparison and not merely as an abstract isomorphism of the two sides. -/
public theorem bijective_stalkBaseChangeRestrictHom (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (y : Y) : Function.Bijective (stalkBaseChangeRestrictHom f y).hom := by
  let := pullbackFromSpecStalkAlgebra f y
  obtain ⟨e, he⟩ := exists_linearEquiv_pushforwardStalk_appTop_pullback f y
  have hcomp : ∀ a : pushforwardStalkModule f y,
      e ((stalkBaseChangeRestrictHom f y).hom a) = a := by
    intro a
    obtain ⟨U, hy, s, rfl⟩ := exists_pushforwardStalkGerm_eq f y a
    rw [stalkBaseChangeRestrictHom_germ]
    exact he U hy s
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [← hcomp a, ← hcomp b, hab]
  · exact ⟨e a, e.injective (hcomp (e a))⟩

/-- `Stacks.FormalFunctions.bijective_stalkBaseChangeRestrictHom`, as an instance. -/
public instance isIso_stalkBaseChangeRestrictHom (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (y : Y) : IsIso (stalkBaseChangeRestrictHom f y) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkBaseChangeRestrictHom f y)

end Stacks.FormalFunctions

end
