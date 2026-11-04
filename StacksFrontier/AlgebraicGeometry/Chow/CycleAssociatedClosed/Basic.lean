module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite multiplicity at an irreducible component

Let `X` be locally of finite type over a base in the Chow situation and let `Z` be a closed
subscheme of `X`. At the generic point of an irreducible component of `Z`, the local ring of
`Z` has finite length as a module over the corresponding local ring of `X`. This finiteness is
what makes the multiplicity of a component in a closed subscheme a well-defined integer, so
that the cycle associated to a closed subscheme can be formed.

## Main results

* `AlgebraicGeometry.isFiniteLength_stalk_of_isGenericPoint_component` proves finiteness of
  the multiplicity of an irreducible component in a closed subscheme.

## Implementation notes

A closed subscheme is represented by a closed immersion `i : Z ⟶ X`, and an irreducible
component by a member of `irreducibleComponents Z`. The module structure on the stalk of `Z`
is restriction of scalars along the canonical stalk map induced by `i`.

## References

* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02QT.** At the generic point of an irreducible component of a closed
subscheme, its local ring has finite length over the ambient local ring. -/
@[stacks 02QT "finite_multiplicity"]
lemma isFiniteLength_stalk_of_isGenericPoint_component
    (C : Stacks.Chow.ChowSituation.{u}) {X Z : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (Z' : Set Z) (hZ' : Z' ∈ irreducibleComponents Z)
    (ξ : Z) (hξ : IsGenericPoint ξ Z') :
    letI : Module (X.presheaf.stalk (i ξ)) (Z.presheaf.stalk ξ) :=
      Module.compHom (Z.presheaf.stalk ξ) (i.stalkMap ξ).hom
    IsFiniteLength (X.presheaf.stalk (i ξ)) (Z.presheaf.stalk ξ) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have hmax : IsMax ξ := by
    intro y hξy
    exact Scheme.le_iff_specializes.mpr <| hξ.specializes <|
      hZ'.2 isIrreducible_singleton.closure
        (by simpa only [← hξ.def] using
          (Scheme.le_iff_specializes.mp hξy).closure_subset)
        (subset_closure (Set.mem_singleton y))
  have : Ring.KrullDimLE 0 _ :=
    krullDimLE_of_coheight_le (by simpa using (Order.IsMax.coheight_eq_zero hmax).le)
  have := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := Z.presheaf.stalk ξ)
  let : Module _ (Z.presheaf.stalk ξ) := Module.compHom _ (i.stalkMap ξ).hom
  apply Module.length_ne_top_iff.mp
  rw [length_restrictScalars_eq_of_surjective
    (X.presheaf.stalk (i ξ)) (Z.presheaf.stalk ξ) (i.stalkMap ξ).hom
    (i.stalkMap_surjective ξ) (Z.presheaf.stalk ξ)]
  exact Module.length_ne_top_iff.mpr ((isArtinianRing_iff_isFiniteLength _).mp inferInstance)

end AlgebraicGeometry
