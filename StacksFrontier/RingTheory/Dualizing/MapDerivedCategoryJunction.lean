module

public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# The comparison of composite derived functors, read at the class of a complex

`StacksFrontier.RingTheory.Dualizing.MapDerivedCategory` turns an isomorphism `e : F ⋙ G ≅ H` of
exact functors between abelian categories into an isomorphism
`F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory`, by lifting a comparison of
functors out of cochain complexes through the localisation functor. The lift is opaque: nothing
in its construction says what its component at a given object of `DerivedCategory C` is.

This file says what that component is at the class `Q(A)` of a cochain complex `A`, which is the
only place a lifted natural transformation can be computed and the form every consumer needs.
The two lemmas below are what lets an equation written through
`CategoryTheory.Functor.mapDerivedCategoryFactors` of one functor be rewritten into one written
through the `mapDerivedCategoryFactors` of another.

## Main results

* `Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q`: the component of
  `Dualizing.mapDerivedCategoryCompNatIso` at `Q(A)`, as the chain-level comparison conjugated by
  the three `mapDerivedCategoryFactors` involved.
* `Dualizing.mapDerivedCategoryCompNatIso_inv_app_Q`: the same for the inverse.
* `Dualizing.mapDerivedCategoryComp_hom_app_Q`: the special case `H = F ⋙ G`, the shape
  `Dualizing.mapDerivedCategoryComp` is stated in.

## Implementation notes

Both proofs are the same step: `Dualizing.mapDerivedCategoryCompNatIso` is
`CategoryTheory.Localization.liftNatIso`, whose two directions are
`CategoryTheory.Localization.liftNatTrans` of the two directions of the isomorphism it lifts, and
`CategoryTheory.Localization.liftNatTrans_app` evaluates that at the image of an object of the
source. The two `CategoryTheory.Localization.Lifting` instances are the canonical ones at
`Q ⋙ F.mapDerivedCategory`, whose isomorphisms are identities, so nothing is left of them.

`Stacks.DerivedGlueing.mapDerivedCategoryComp_factors` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenOfGlobalObject` is the same
computation for `Stacks.DerivedGlueing.mapDerivedCategoryComp`, which is a *different*
construction of the same comparison in the opposite direction, built from its own lifted
comparison of complex-level functors. Neither lemma is about the other's definition, and the two
definitions are not known to the library to be equal, so neither can be used in place of the
other; this file is the one about the `Dualizing` construction, which is what the slicing squares
of `StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesDerivedCompatibility` are built
from.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- `comp_preservesFiniteLimits` and `comp_preservesFiniteColimits` are lemmas rather than
-- instances, and exactness of `F ⋙ G` is needed to state the lemmas below.
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

namespace Dualizing

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **The component of `Dualizing.mapDerivedCategoryCompNatIso` at the class of a complex.** The
two routes from `Q(A)` to `Q(H(A))` — the comparison of the induced functors followed by the
factorisation of `H`, and the two factorisations of `F` and `G` followed by `e` read degreewise —
agree. -/
theorem mapDerivedCategoryCompNatIso_hom_app_Q (e : F ⋙ G ≅ H) (A : CochainComplex C ℤ) :
    (mapDerivedCategoryCompNatIso F G H e).hom.app (DerivedCategory.Q.obj A) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app A) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app A) ≫
        H.mapDerivedCategoryFactors.inv.app A := by
  simp [mapDerivedCategoryCompNatIso, Localization.liftNatIso, Localization.liftNatTrans_app]

/-- **The component of the inverse of `Dualizing.mapDerivedCategoryCompNatIso` at the class of a
complex.** -/
theorem mapDerivedCategoryCompNatIso_inv_app_Q (e : F ⋙ G ≅ H) (A : CochainComplex C ℤ) :
    (mapDerivedCategoryCompNatIso F G H e).inv.app (DerivedCategory.Q.obj A) =
      H.mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app A) ≫
        G.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app A) := by
  simp [mapDerivedCategoryCompNatIso, Localization.liftNatIso, Localization.liftNatTrans_app]

/-- **The component of `Dualizing.mapDerivedCategoryComp` at the class of a complex.** The
degreewise comparison here is the identity on the nose, the prolongation of a composite being the
composite of the prolongations, so the component is the three factorisations alone. -/
theorem mapDerivedCategoryComp_hom_app_Q (A : CochainComplex C ℤ) :
    (mapDerivedCategoryComp F G).hom.app (DerivedCategory.Q.obj A) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app A ≫
        G.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app A) := by
  have h : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).inv.app A = 𝟙 _ := by
    ext n
    simp
  rw [mapDerivedCategoryComp, Iso.symm_hom,
    mapDerivedCategoryCompNatIso_inv_app_Q F G (F ⋙ G) (Iso.refl _) A, h]
  simp

end Dualizing

end
