module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSectionsSupplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionFieldIso

/-!
# A rational function on an integral étale `X`-scheme is a function on its generic fibre

Let `X` be an integral scheme with generic point `η`, and let `V` be an integral scheme étale over
`X`. The generic fibre `V ×_X η` is a one-point scheme whose local ring is the function field of
`V`, so reading a global function on the generic fibre as a rational function on `V` —
`Stacks.EtaleCohomology.genericFibreToFunctionField` — is not merely injective but **bijective**:
a section of a one-point scheme is its germ, and the germ map at the single point of a one-point
scheme is surjective because the only open neighbourhood of that point is the whole space.

The consequence used by the fundamental exact sequence of Stacks 03RI is that an invertible
rational function on `V` is the restriction to the generic fibre of an invertible global function
there. Surjectivity of the divisor map of Stacks 03RI is proved by exhibiting a rational function
on `X` with a prescribed divisor and pulling it back to `V`; this is what turns the pulled-back
rational function into a section of `j_* 𝐆_{m,η}` over `V`, with no further computation of germs.

## Main results

* `Stacks.EtaleCohomology.surjective_germ_top_of_subsingleton`: on a one-point scheme every
  element of the stalk is the germ of a global section.
* `Stacks.EtaleCohomology.surjective_genericFibreToFunctionField`: **the comparison to the
  function field is surjective.**
* `Stacks.EtaleCohomology.exists_units_genericFibreToFunctionField_eq`: **every invertible
  rational function on `V` comes from an invertible global function on the generic fibre.**

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, whose third map is surjective because a divisor on a nonsingular curve is locally
  principal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **On a one-point scheme every element of a stalk is the germ of a global section.** The only
open neighbourhood of the point is the whole space, so the open on which a representing section
is defined is already everything. -/
theorem surjective_germ_top_of_subsingleton {V : Scheme.{u}} [Subsingleton ↥V] (z : V) :
    Function.Surjective (V.presheaf.germ ⊤ z trivial) := by
  intro t
  obtain ⟨U, hzU, s, hs⟩ := V.presheaf.exists_germ_eq (x := z) t
  have hU : U = ⊤ := Opens.ext (Set.eq_univ_of_forall fun w => by
    rw [show w = z from Subsingleton.elim w z]
    exact hzU)
  subst hU
  exact ⟨s, hs⟩

variable {X V : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral V]
  (g : V ⟶ X) [AlgebraicGeometry.Etale g]

/-- **Every invertible rational function on `V` is a global function on the generic fibre.** The
comparison to the function field is a bijection of rings, so it carries the inverse of a given
invertible rational function to an inverse of the section produced for it. -/
theorem exists_units_genericFibreToFunctionField_eq (c : (↥V.functionField)ˣ) :
    ∃ a : (Γ(pullback g (genericPointInclusion X), ⊤))ˣ,
      genericFibreToFunctionField g (a : Γ(pullback g (genericPointInclusion X), ⊤)) = c := by
  obtain ⟨a, ha⟩ := surjective_genericFibreToFunctionField g (c : ↥V.functionField)
  obtain ⟨b, hb⟩ := surjective_genericFibreToFunctionField g ((c⁻¹ : (↥V.functionField)ˣ) :
    ↥V.functionField)
  have hab : a * b = 1 := by
    refine injective_genericFibreToFunctionField g ?_
    rw [map_mul, ha, hb, map_one]
    exact c.mul_inv
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

end Stacks.EtaleCohomology

end
