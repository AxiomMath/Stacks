module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCoherenceClosed

/-!
# The slice comparison of the canonical side, at the restriction of a module

The coherence owed by the uniqueness clause of [Stacks, Tag 0D68] is an equation between two
canonical comparisons, and on the side of Situation 0D67 the only non-formal ingredient in it is
the value of `Stacks.DerivedGlueing.sliceRestrictOverIsoOpenModule` at the restriction of a
module on the whole space: it is the restriction of the **counit** of extension by zero on the
middle open, which is what the other side's comparison is built from.  This file carries the
identifications of the two spellings of restriction that computing that value needs.

## Main results

* `Stacks.DerivedGlueing.jStar_obj_eq_overMap_obj`,
  `Stacks.DerivedGlueing.sliceRestrict_source_eq` and
  `Stacks.DerivedGlueing.overMap_sliceToSubspace_map_overFunctor_map` — the two spellings of
  restriction to a smaller open, identified on objects and on morphisms by appeal to the
  equalities of functors rather than by definitional unfolding.
* `Stacks.DerivedGlueing.mapDerivedCategoryCongr_hom_app_Q_comp` — the generic companion of
  `Stacks.DerivedGlueing.mapDerivedCategoryCompIso_hom_app_Q_comp`: the lifted comparison of two
  isomorphic exact functors, read at the class of a complex and followed by the canonical
  factorization of the target, is the factorization of the source followed by the comparison
  applied degreewise.

## Implementation notes

Both spellings of restriction to an open occur here, and the identification between them is
*carried* as the transport of an existing proof rather than asked of the unifier.  That is not a
stylistic preference: re-deriving
`SheafOfModules.overFunctor 𝒪_X U ⋙ sliceToSubspace 𝒪_X U = jStar U 𝒪_X` by `rfl` costs about
169000 heartbeats, against a per-declaration ceiling of 200000, while appealing to
`Stacks.DerivedGlueing.overFunctor_comp_sliceToSubspace` costs about 235.  Every identification
below therefore goes through `CategoryTheory.Functor.congr_obj` or
`CategoryTheory.Functor.congr_hom` of a proved equality of functors, and the resulting
`CategoryTheory.eqToHom`s are kept in the statements.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)

Tags covered: none.  Everything here is a step of a proof, not a clause of a tag statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe w₁ w₂ v₁ v₂ u₁ u₂ u

section Generic

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

/-- `Stacks.DerivedGlueing.mapDerivedCategoryCongr`, read at the class of a complex and followed
by the canonical factorization of the target functor: the canonical factorization of the source
functor, followed by the comparison applied degreewise. -/
theorem mapDerivedCategoryCongr_hom_app_Q_comp {F F' : C₁ ⥤ C₂} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F')
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCongr e).hom.app (DerivedCategory.Q.obj P) ≫
        F'.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) := by
  rw [mapDerivedCategoryCongr_hom_app_Q, Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

end Generic

section Concrete

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.DerivedGlueing.preservesFiniteLimitsOverMap
  Stacks.DerivedGlueing.preservesFiniteColimitsOverMap

/-- **The two spellings of the restriction of a module to `T`, for `T ≤ W`.**  Restricting to
the open subspace `T` is restricting to the opens contained in `W`, then along the arrow
`T ⟶ W` of the site, then reading the result in the open-subspace model.  Both halves are
`Stacks.DerivedGlueing.overFunctor_comp_sliceToSubspace` and
`Stacks.DerivedGlueing.overFunctor_comp_overMap` read at an object, so no comparison of the two
spellings is performed. -/
theorem jStar_obj_eq_overMap_obj {T W : Opens X.carrier} (hTW : T ≤ W)
    (A : SheafOfModules.{u} (underlyingRingSheaf X)) :
    (jStar T (underlyingRingSheaf X)).obj A =
      (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom ⋙
        sliceToSubspace (underlyingRingSheaf X) T).obj
          ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).obj A) :=
  (Functor.congr_obj (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) T) A).symm.trans
    (congrArg (sliceToSubspace (underlyingRingSheaf X) T).obj
      (Functor.congr_obj (overFunctor_comp_overMap (underlyingRingSheaf X) hTW) A).symm)

/-- **The source of the slice comparison, spelled through `jStar`.**  Reading the restriction of
a module to the opens contained in `W` in the open-subspace model and then restricting it to `T`
is extending the open-subspace restriction by zero and restricting that to `T`.  This is
`Stacks.DerivedGlueing.overFunctor_comp_sliceToSubspace` at an object, carried under extension by
zero and restriction. -/
theorem sliceRestrict_source_eq {T W : Opens X.carrier} (hTW : T ≤ W)
    (A : SheafOfModules.{u} (underlyingRingSheaf X)) :
    (sliceToSubspace (underlyingRingSheaf X) W ⋙ openModuleRestriction X T W hTW).obj
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).obj A) =
      (jStar T (underlyingRingSheaf X)).obj
        ((jShriek W (underlyingRingSheaf X)).obj
          ((jStar W (underlyingRingSheaf X)).obj A)) :=
  congrArg (fun N => (jStar T (underlyingRingSheaf X)).obj
      ((jShriek W (underlyingRingSheaf X)).obj N))
    (Functor.congr_obj (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) W) A)

/-- **Restriction of a morphism along the arrow `T ⟶ W` of the site, read in the open-subspace
model, is its restriction to `T`,** with the two spellings of source and target carried as the
transports of `Stacks.DerivedGlueing.jStar_obj_eq_overMap_obj`.  The proof is
`Stacks.DerivedGlueing.overFunctor_comp_overMap_comp_sliceToSubspace` read on morphisms by
`CategoryTheory.Functor.congr_hom`. -/
theorem overMap_sliceToSubspace_map_overFunctor_map {T W : Opens X.carrier} (hTW : T ≤ W)
    {A B : SheafOfModules.{u} (underlyingRingSheaf X)} (g : A ⟶ B) :
    (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom ⋙
        sliceToSubspace (underlyingRingSheaf X) T).map
          ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).map g) =
      eqToHom (jStar_obj_eq_overMap_obj hTW A).symm ≫
        (jStar T (underlyingRingSheaf X)).map g ≫
          eqToHom (jStar_obj_eq_overMap_obj hTW B) := by
  rw [← Functor.comp_map (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W)
      (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom ⋙
        sliceToSubspace (underlyingRingSheaf X) T),
    Functor.congr_hom (overFunctor_comp_overMap_comp_sliceToSubspace
      (underlyingRingSheaf X) hTW) g]

end Concrete

end Stacks.DerivedGlueing

end
