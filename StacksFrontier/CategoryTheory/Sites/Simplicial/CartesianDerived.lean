module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem

/-!
# Cartesian objects of the derived category of a simplicial site

Let `S` be a simplicial-site situation. An object `K` of the derived category of abelian sheaves
on its total site has a derived restriction `Kₙ` in every simplicial degree, and an arrow
`φ : [m] ⟶ [n]` of the simplex category induces a transition `f_φ⁻¹ Kₘ ⟶ Kₙ`. The object is
*cartesian* when every one of those transitions is an isomorphism.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.abelianComponent'`: restriction of abelian sheaves
  from the total site to a simplicial degree, as the abelian inverse image of the component
  morphism of topoi.
* `CategoryTheory.SimplicialSiteSituation.derivedComponent'`: its localization to unbounded
  derived categories.
* `CategoryTheory.SimplicialSiteSituation.derivedComponentTransition`: the transition
  `f_φ⁻¹ Kₘ ⟶ Kₙ` on derived categories.
* `CategoryTheory.SimplicialSiteSituation.IsCartesianDerived'`: cartesian objects of the derived
  category, Stacks 07TF (3), for the standard derived categories.

## Main results

* `CategoryTheory.SimplicialSiteSituation.abelianComponent'_exact`: restriction to a simplicial
  degree is exact on abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.derivedComponentTransition_app_Q`: at the image of a
  complex, the derived transition is the transition of Stacks 09WF applied to every term of the
  complex and localized.

## Implementation notes

The unprimed names of `StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves` denote
different terms: there the component restriction is the direct image along the continuous component
inclusion and the derived categories are a hypothesis, here it is the abelian inverse image of the
component morphism of topoi and the derived categories are the standard ones. The two restrictions
agree by Stacks 00XR; that identification is not formalized.

The component restriction is `CategoryTheory.Sites.abelianInverseImage` of the component morphism
of topoi, as are the simplex transitions `abelianTransition` of Stacks 0D9G, so its exactness is
that of an abelian inverse image, Stacks 04JC. The transition on abelian sheaves is
`abelianFiberTransition`, the transition of Stacks 09WF on abelian sheaves.

The derived transition is the natural transformation of localized functors induced by the abelian
transition on complexes, `CategoryTheory.Localization.liftNatTrans`, precomposed with the
comparison `CategoryTheory.derivedCompIso` of the derived functor of a composite with the composite
of the derived functors.

The derived categories are the standard ones, `HasDerivedCategory.standard`, supplied as local
instances.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- Restriction of abelian sheaves from the total site to one simplicial degree, as the abelian
inverse image of the component morphism of topoi. -/
def abelianComponent' (n : SimplexCategory) :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf (S.componentTopology n) Ab.{u} :=
  abelianInverseImage (componentMorphism S n)

/-- **Stacks 04JC.** Restriction to a simplicial degree is exact on abelian sheaves. -/
theorem abelianComponent'_exact (n : SimplexCategory) :
    exactFunctor (Sheaf S.totalTopology Ab.{u})
      (Sheaf (S.componentTopology n) Ab.{u}) (abelianComponent' S n) :=
  abelianInverseImage_exact (componentMorphism S n)

/-- Restriction to a simplicial degree preserves finite limits. -/
instance abelianComponent'_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (abelianComponent' S n) :=
  (abelianComponent'_exact S n).1

/-- Restriction to a simplicial degree preserves finite colimits. -/
instance abelianComponent'_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (abelianComponent' S n) :=
  (abelianComponent'_exact S n).2

/-- Restriction to a simplicial degree is additive. -/
instance abelianComponent'_additive (n : SimplexCategory) :
    (abelianComponent' S n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Stacks 09WF** on abelian sheaves, with the component restriction of this module as its
source and target: the transition `f_φ⁻¹ Fₘ ⟶ Fₙ` of abelian sheaves. -/
abbrev abelianComponentTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianComponent' S m ⋙ abelianTransition S φ ⟶ abelianComponent' S n :=
  abelianFiberTransition S φ

local instance derivedCategoryTotal :
    HasDerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  HasDerivedCategory.standard _

local instance derivedCategoryComponent (n : SimplexCategory) :
    HasDerivedCategory (Sheaf (S.componentTopology n) Ab.{u}) :=
  HasDerivedCategory.standard _

/-- A derived abelian sheaf on the total site, restricted to one simplicial degree. -/
@[implicit_reducible] def derivedComponent' (n : SimplexCategory) :
    DerivedCategory (Sheaf S.totalTopology Ab.{u}) ⥤
      DerivedCategory (Sheaf (S.componentTopology n) Ab.{u}) :=
  (abelianComponent' S n).mapDerivedCategory

/-- The transition of Stacks 09WF applied to every term of a cochain complex and localized at
the quasi-isomorphisms: a natural transformation of the derived functors of the two composites
of abelian functors. This is `CategoryTheory.derivedNatTrans` at the transition of this
module. -/
def derivedComponentTransitionAux {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianComponent' S m ⋙ abelianTransition S φ).mapDerivedCategory ⟶
      (abelianComponent' S n).mapDerivedCategory :=
  derivedNatTrans _ _ (abelianComponentTransition S φ)

/-- At the image of a complex, the localized transition is the abelian transition applied
degreewise, conjugated by the comparisons identifying the derived functors with the localized
functors on complexes. -/
theorem derivedComponentTransitionAux_app_Q {m n : SimplexCategory} (φ : m ⟶ n)
    (A : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (derivedComponentTransitionAux S φ).app (DerivedCategory.Q.obj A) ≫
        (abelianComponent' S n).mapDerivedCategoryFactors.hom.app A =
      (abelianComponent' S m ⋙ abelianTransition S φ).mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (abelianComponentTransition S φ) (ComplexShape.up ℤ)).app A) := by
  simp [derivedComponentTransitionAux, derivedNatTrans, Localization.liftNatTrans_app,
    Localization.Lifting.iso]

/-- The canonical transition `f_φ⁻¹ Kₘ ⟶ Kₙ` on derived categories: the localization of the
transition of Stacks 09WF applied to every term of a complex, compared with the derived functor
of the composite by `derivedCompIso`. -/
def derivedComponentTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedComponent' S m ⋙ derivedInverseImage S φ ⟶ derivedComponent' S n :=
  (derivedCompIso (abelianComponent' S m) (abelianTransition S φ)
      (abelianComponent' S m ⋙ abelianTransition S φ) (Iso.refl _)).inv ≫
    derivedComponentTransitionAux S φ

/-- The derived transition splits as the compositor comparison followed by the localization of
the abelian transition. -/
theorem derivedComponentTransition_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedComponentTransition S φ =
      (derivedCompIso (abelianComponent' S m) (abelianTransition S φ)
          (abelianComponent' S m ⋙ abelianTransition S φ) (Iso.refl _)).inv ≫
        derivedComponentTransitionAux S φ :=
  rfl

attribute [local implicit_reducible] derivedInverseImage in
/-- The derived transition is determined by the abelian transition: at the image of a complex it
is the abelian transition applied degreewise, conjugated by the canonical comparisons. -/
theorem derivedComponentTransition_app_Q {m n : SimplexCategory} (φ : m ⟶ n)
    (A : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (derivedComponentTransition S φ).app (DerivedCategory.Q.obj A) ≫
        (abelianComponent' S n).mapDerivedCategoryFactors.hom.app A =
      (derivedCompIso (abelianComponent' S m) (abelianTransition S φ)
          (abelianComponent' S m ⋙ abelianTransition S φ)
          (Iso.refl _)).inv.app (DerivedCategory.Q.obj A) ≫
        (abelianComponent' S m ⋙ abelianTransition S φ).mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (abelianComponentTransition S φ) (ComplexShape.up ℤ)).app A) := by
  rw [derivedComponentTransition_eq, NatTrans.comp_app, Category.assoc,
    derivedComponentTransitionAux_app_Q]

/-- **Stacks 07TF.** An object of the derived category of abelian sheaves on the total site of a
simplicial site is *cartesian* if the canonical transition along every simplex map is an
isomorphism.

The derived categories are the standard ones and the transition is `derivedComponentTransition`;
`CategoryTheory.SimplicialSiteSituation.IsCartesianDerived` states the condition for an arbitrary
choice of derived categories. -/
@[stacks 07TF "cartesian objects of the derived category"]
abbrev IsCartesianDerived' (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), IsIso ((derivedComponentTransition S φ).app K)

end CategoryTheory.SimplicialSiteSituation

end
