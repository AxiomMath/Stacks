module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibre
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic

/-!
# The local rings of the generic fibre

Let `X` be an irreducible scheme with generic point inclusion `j : Spec K ⟶ X`, and let
`g : U ⟶ X` be a morphism of schemes. The projection `U ×_X Spec K ⟶ U` is injective on points
and induces an isomorphism on every stalk; in particular the generic fibre of an étale `X`-scheme
carries the local ring of that scheme at the generic point of each of its irreducible components.

## Main results

* `AlgebraicGeometry.isIso_stalkMap_of_flat_of_isPreimmersion`: a flat preimmersion induces an
  isomorphism on every stalk.
* `Stacks.EtaleCohomology.flat_genericPointInclusion`: the inclusion of the generic point of an
  irreducible scheme is flat.
* `Stacks.EtaleCohomology.isIso_stalkMap_pullback_fst_genericPointInclusion`: the projection
  from the generic fibre induces an isomorphism on every stalk.
* `Stacks.EtaleCohomology.injective_base_pullback_fst_genericPointInclusion`: that projection is
  injective on points.
* `Stacks.EtaleCohomology.exists_pullback_isIso_stalkMap_of_mem_irreducibleComponents`: the
  generic fibre of an étale `X`-scheme carries the local ring of that scheme at the generic point
  of each of its irreducible components.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

/-- A flat preimmersion induces an isomorphism on every stalk. -/
theorem isIso_stalkMap_of_flat_of_isPreimmersion {X Y : Scheme.{u}} (w : X ⟶ Y) [Flat w]
    [IsPreimmersion w] (x : X) : IsIso (w.stalkMap x) := by
  have hinj : Function.Injective (w.stalkMap x).hom := by
    algebraize [(w.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (w x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap w x) (w.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›.injective
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, w.stalkMap_surjective x⟩

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- The inclusion of the generic point of an irreducible scheme is flat. -/
instance flat_genericPointInclusion : Flat (genericPointInclusion X) :=
  flat_fromSpecStalk X _

variable {U : Scheme.{u}} (g : U ⟶ X)

/-- The projection `U ×_X Spec K ⟶ U` from the generic fibre induces an isomorphism on every
stalk. -/
theorem isIso_stalkMap_pullback_fst_genericPointInclusion
    (z : ↥(pullback g (genericPointInclusion X))) :
    IsIso ((pullback.fst g (genericPointInclusion X)).stalkMap z) :=
  isIso_stalkMap_of_flat_of_isPreimmersion _ z

/-- The projection `U ×_X Spec K ⟶ U` from the generic fibre is injective on points. -/
theorem injective_base_pullback_fst_genericPointInclusion :
    Function.Injective (pullback.fst g (genericPointInclusion X)).base :=
  (pullback.fst g (genericPointInclusion X)).isEmbedding.injective

/-- For an étale `X`-scheme `V` and `u` the generic point of an irreducible component of `V`,
there is a point of the generic fibre `V ×_X Spec K` above `u` at which the projection induces an
isomorphism of local rings. -/
theorem exists_pullback_isIso_stalkMap_of_mem_irreducibleComponents (V : X.Etale) {u : V.left}
    (hu : closure {u} ∈ irreducibleComponents V.left) :
    ∃ z : ↥(pullback V.hom (genericPointInclusion X)),
      (pullback.fst V.hom (genericPointInclusion X)).base z = u ∧
        IsIso ((pullback.fst V.hom (genericPointInclusion X)).stalkMap z) :=
  (exists_pullback_genericPointInclusion_eq_of_mem_irreducibleComponents X V hu).imp
    fun z hz ↦ ⟨hz, isIso_stalkMap_pullback_fst_genericPointInclusion X V.hom z⟩

end Stacks.EtaleCohomology

end
