module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroPushforwardHom
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroPushforwardSurjective

/-!
# One step of a tower of square-zero extensions, pushed forward

`Stacks.Thickenings.exists_thickening_of_iterate` iterates [Stacks, Tag 05YV] against an
invariant, and at each level it asks for a square-zero extension of the structure sheaf of the
*current* stage.  An argument that realizes a thickening downstairs out of a thickening upstairs
— the essential-surjectivity direction of [Stacks, Tag 0E3X] — holds the extension upstairs
instead, and has to turn it into one downstairs while carrying its hypotheses to the next level.

This file assembles that single step.  Given a morphism `g : Z ⟶ V` whose structure-sheaf
comparison `𝒪_V ⟶ g_*𝒪_Z` is invertible, a square-zero extension `E` of `𝒪_Z` over `S` and a
scheme `Z'` realizing it, there is a square-zero extension of `𝒪_V` over `S`, a scheme `V'`
realizing *that*, and a morphism `Z' ⟶ V'` which again has invertible structure-sheaf comparison,
restricts to `g` on `Z` and `V`, and lies over `S`.

So the data the step consumes is of the same shape as the data it produces, which is what makes
it iterable.

## Main results

* `Stacks.Thickenings.SquareZeroExtension.exists_realization_pushforward`: **the step**, with its
  two hypotheses in the shape the pushforward states them.
* `Stacks.Thickenings.SquareZeroExtension.exists_realization_pushforward_of_isZero_rightDerived`:
  the same step with the local surjectivity replaced by the vanishing of `R¹g_*` on the kernel of
  the extension, which is the hypothesis a geometric consumer actually has.

## Implementation notes

Both hypotheses are genuine input, and neither is a weakening: local surjectivity of the
pushed-forward quotient map is what the vanishing of `R¹g_*` on the kernel provides
(`Stacks.Thickenings.SquareZeroExtension.isLocallySurjective_pushforward_π`), and quasi-coherence
of the pushed-forward kernel is a property of `g` and the kernel that direct image does not
preserve in general.

The morphism `Z' ⟶ V'` is not constructed here by hand.  It is
`Stacks.Thickenings.Realization.map` of
`Stacks.Thickenings.SquareZeroExtension.pushforwardHom`, so its three properties are the three
general statements about that morphism, and in particular the locality of its stalk maps is
already discharged by the functoriality of the realization.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Thickenings

variable {Z V S : Scheme.{u}}

/-- **One step of the tower, pushed forward.** Let `g : Z ⟶ V` have invertible structure-sheaf
comparison, let `k : V ⟶ S`, let `E` be a square-zero extension of `𝒪_Z` over `S` and let `Z'`
realize it.  Then there is a square-zero extension of `𝒪_V` over `S`, a scheme `V'` realizing it,
and a morphism `Z' ⟶ V'` with invertible structure-sheaf comparison which restricts to `g` on the
thickened subschemes and lies over `S`.

The extension is `Stacks.Thickenings.SquareZeroExtension.pushforward`, the realization is the one
[Stacks, Tag 05YV] provides, and the morphism is the realization of
`Stacks.Thickenings.SquareZeroExtension.pushforwardHom`. -/
theorem SquareZeroExtension.exists_realization_pushforward (g : Z ⟶ V) (k : V ⟶ S)
    (E : SquareZeroExtension (g ≫ k)) [IsIso g.c]
    (hπ : TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
        ≫ structureComparisonInv g))
    (hqc : ((Scheme.Modules.pushforward g).obj E.I).IsQuasicoherent)
    (r₁ : Realization E) :
    ∃ (E' : SquareZeroExtension k) (r₂ : Realization E') (g' : r₁.ambient ⟶ r₂.ambient),
      IsIso g'.c ∧ r₁.immersion ≫ g' = g ≫ r₂.immersion ∧ g' ≫ r₂.toBase = r₁.toBase :=
  ⟨E.pushforward g k hπ hqc, realization (E.pushforward g k hπ hqc),
    r₁.map (realization (E.pushforward g k hπ hqc)) (E.pushforwardHom g k hπ hqc),
    isIso_c_map_pushforwardHom g k E hπ hqc r₁ _,
    immersion_comp_map_pushforwardHom g k E hπ hqc r₁ _,
    map_pushforwardHom_comp_toBase g k E hπ hqc r₁ _⟩

/-- **The step, with the vanishing of `R¹g_*` on the kernel as hypothesis.** This is the form a
geometric consumer meets: the local surjectivity the pushforward asks for is exactly what the
vanishing of the first higher direct image of the kernel of the extension provides. -/
theorem SquareZeroExtension.exists_realization_pushforward_of_isZero_rightDerived (g : Z ⟶ V)
    (k : V ⟶ S) (E : SquareZeroExtension (g ≫ k)) [IsIso g.c]
    (hR : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj E.I))
    (hqc : ((Scheme.Modules.pushforward g).obj E.I).IsQuasicoherent)
    (r₁ : Realization E) :
    ∃ (E' : SquareZeroExtension k) (r₂ : Realization E') (g' : r₁.ambient ⟶ r₂.ambient),
      IsIso g'.c ∧ r₁.immersion ≫ g' = g ≫ r₂.immersion ∧ g' ≫ r₂.toBase = r₁.toBase :=
  E.exists_realization_pushforward g k
    (E.isLocallySurjective_pushforward_π_comp_of_isZero_rightDerived g hR) hqc r₁

end Stacks.Thickenings

end
