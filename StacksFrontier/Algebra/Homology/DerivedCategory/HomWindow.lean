module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Windows of Hom-vanishing in a derived category

Let `C` be an abelian category, `Q` a property of objects of `C` and `K` an object of `D(C)`.
`K` has a *window of Hom-vanishing* for `Q` if there are integers `a ≤ b` such that every object
`L` of `D(C)` whose cohomology objects all satisfy `Q` and vanish in the degrees `a, …, b` admits
no nonzero morphism `K ⟶ L`.  This is the shape of the conclusion of [Stacks, Tag 09M4] part (1)
for schemes and of [Stacks, Tag 09MB] part (1) for algebraic spaces, `Q` being quasi-coherence.

## Main definitions

* `Stacks.HomWindow.HasHomWindow`: the window property.

## Main results

* `Stacks.HomWindow.HasHomWindow.of_iso`: it is invariant under isomorphism.
* `Stacks.HomWindow.HasHomWindow.of_mapDerivedCategory`: it descends, with the same window, along
  an exact functor `F` carrying `Q`-objects to `Q₂`-objects whose derived functor is faithful.
* `Stacks.HomWindow.faithful_mapDerivedCategory_of_iso`: the derived functor of an exact functor
  with an exact left inverse is faithful.

## References

* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 09MB](https://stacks.math.columbia.edu/tag/09MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.HomWindow

section Abstract

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **A window of Hom-vanishing.**  An object `K` of `D(C)` has a window of Hom-vanishing for the
property `Q` of objects of `C` if there are integers `a ≤ b` such that every object `L` of `D(C)`
whose cohomology objects all satisfy `Q`, and vanish in the degrees `a, a + 1, …, b`, admits no
nonzero morphism `K ⟶ L`. -/
def HasHomWindow (Q : ObjectProperty C) (K : DerivedCategory C) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧ ∀ L : DerivedCategory C,
    (∀ i : ℤ, Q ((DerivedCategory.homologyFunctor C i).obj L)) →
    (∀ i : ℤ, a ≤ i → i ≤ b → IsZero ((DerivedCategory.homologyFunctor C i).obj L)) →
    Subsingleton (K ⟶ L)

/-- The window property is invariant under isomorphism. -/
theorem HasHomWindow.of_iso {Q : ObjectProperty C} {K K' : DerivedCategory C} (e : K ≅ K')
    (h : HasHomWindow Q K) : HasHomWindow Q K' := by
  obtain ⟨a, b, hab, h⟩ := h
  exact ⟨a, b, hab, fun L hL hz => (e.homFromEquiv (Z := L)).subsingleton_congr.1 (h L hL hz)⟩

variable {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]

/-- **The window property descends along an exact functor with faithful derived functor.**  Let
`F : C ⥤ C₂` be exact and additive, carrying objects satisfying `Q` to objects satisfying `Q₂`,
and suppose that `F` induces a faithful functor of derived categories.  If `F K` has a window of
Hom-vanishing for `Q₂`, then `K` has one for `Q`, the same window.

Cohomology commutes with `F` (`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`), so `F L`
inherits the hypotheses on `L`, and a morphism `K ⟶ L` is determined by its image. -/
theorem HasHomWindow.of_mapDerivedCategory (F : C ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {Q : ObjectProperty C} {Q₂ : ObjectProperty C₂}
    [Q₂.IsClosedUnderIsomorphisms] (hQ : ∀ M : C, Q M → Q₂ (F.obj M))
    (hfaith : F.mapDerivedCategory.Faithful) {K : DerivedCategory C}
    (h : HasHomWindow Q₂ (F.mapDerivedCategory.obj K)) : HasHomWindow Q K := by
  obtain ⟨a, b, hab, h⟩ := h
  refine ⟨a, b, hab, fun L hL hz => ?_⟩
  have hsub := h (F.mapDerivedCategory.obj L)
    (fun i => Q₂.prop_of_iso ((F.mapDerivedCategoryHomologyIso i).app L).symm (hQ _ (hL i)))
    (fun i hai hib => (F.map_isZero (hz i hai hib)).of_iso
      ((F.mapDerivedCategoryHomologyIso i).app L))
  exact ⟨fun x y => F.mapDerivedCategory.map_injective (Subsingleton.elim _ _)⟩

/-- **The derived functor of an exact functor with an exact left inverse is faithful.**  If
`F ⋙ G ≅ 𝟭` for exact additive functors `F` and `G`, then the induced functors of derived
categories compose to a functor isomorphic to the identity, so the first is faithful. -/
theorem faithful_mapDerivedCategory_of_iso (F : C ⥤ C₂) (G : C₂ ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ⋙ G ≅ 𝟭 C) :
    F.mapDerivedCategory.Faithful := by
  let i₁ : DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ) ≪≫
          NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ))
        DerivedCategory.Q ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  let i : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 (DerivedCategory C) :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory)
      (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C)) _ _ i₁
  have : (F.mapDerivedCategory ⋙ G.mapDerivedCategory).Faithful :=
    Functor.Faithful.of_iso i.symm
  exact Functor.Faithful.of_comp F.mapDerivedCategory G.mapDerivedCategory

end Abstract

end Stacks.HomWindow

end
