module

public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exactness of the stalk functor on sheaves of modules

Let `O` be a sheaf of rings on a topological space `X` and `x` a point. The stalk functor
`AlgebraicGeometry.SheafOfModules.stalkFunctor O x`, from sheaves of `O`-modules to modules
over the stalk of `O`, is exact: it preserves finite limits as well as all colimits.

## Main results

* `AlgebraicGeometry.SheafOfModules.instPreservesFiniteColimitsStalkFunctor`: the stalk functor
  preserves finite colimits. Left exactness is *not* proved here: it is
  `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkwiseExactness.lean`, which this file
  imports, and together with it the stalk functor is exact.
* `AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff`: its value is a zero object
  exactly when the stalk of the underlying sheaf of abelian groups is.
* `AlgebraicGeometry.cohomologySupportedOn_obj₂_of_distinguished`: cohomological support on a
  subset is a two-out-of-three property for distinguished triangles in the derived category of
  sheaves of modules.

## Implementation notes

Left exactness of the stalk functor on sheaves of *modules* is imported from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness`, which obtains it by
reflection along `forget₂ (ModuleCat _) AddCommGrpCat`; it is not reproved here. What remains
is `instPreservesFiniteLimitsPresheafStalkFunctor`, the abelian-group statement one level down:
the stalk functor on presheaves of abelian groups preserves finite limits because it is a
colimit over the filtered category of open neighbourhoods of `x`, where `AddCommGrpCat`
satisfies AB5.

The two-out-of-three property for cohomological support is then the exactness of the stalk
functor applied to the three-term exact sequence of cohomology sheaves attached to a
distinguished triangle: the outer stalks vanish, hence so does the middle one.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- The stalk functor on presheaves of abelian groups preserves finite limits: it is a colimit
over the filtered category of open neighbourhoods of `x`. -/
instance instPreservesFiniteLimitsPresheafStalkFunctor :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
  change PreservesFiniteLimits
    ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (OpenNhds.inclusion x).op ⋙ colim)
  infer_instance

/-- The stalk functor on sheaves of modules preserves finite colimits. -/
instance instPreservesFiniteColimitsStalkFunctor :
    PreservesFiniteColimits (stalkFunctor O x) := inferInstance

/-- The stalk of a sheaf of modules vanishes as a module exactly when it vanishes as an
abelian group: the two have the same carrier. -/
theorem isZero_stalkFunctor_obj_iff (M : _root_.SheafOfModules.{u} O) :
    IsZero ((stalkFunctor O x).obj M) ↔
      IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.val.presheaf x) := by
  rw [ModuleCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
  exact Iff.rfl

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **Cohomological support is a two-out-of-three property.** If the first and third vertices
of a distinguished triangle have all their cohomology supported on `T`, so does the second.

The stalk functor at a point outside `T` is exact, so it carries the three-term exact sequence
`H^i(E₁) ⟶ H^i(E₂) ⟶ H^i(E₃)` of cohomology sheaves to an exact sequence of modules whose
outer terms vanish. -/
theorem cohomologySupportedOn_obj₂_of_distinguished {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X)
    (S : Triangle (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (hS : S ∈ distTriang (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (h₁ : CohomologySupportedOn O T S.obj₁) (h₃ : CohomologySupportedOn O T S.obj₃) :
    CohomologySupportedOn O T S.obj₂ := by
  intro i x hx
  rw [← SheafOfModules.isZero_stalkFunctor_obj_iff O x]
  have hex := DerivedCategory.HomologySequence.exact₂ S hS i
  have hmap := hex.map (SheafOfModules.stalkFunctor O x)
  refine hmap.isZero_of_both_isZero ?_ ?_
  · exact (SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h₁ i x hx)
  · exact (SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h₃ i x hx)

end AlgebraicGeometry

end
