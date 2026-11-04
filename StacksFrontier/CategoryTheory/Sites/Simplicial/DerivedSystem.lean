module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorsTriangle
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Sheaves

/-!
# Simplicial systems in derived categories (Stacks 0D9G)

A simplicial system for a simplicial-site situation `S` consists of an object of the
unbounded derived category of abelian sheaves on each component site, together with a map
from the derived inverse image along every simplex map, compatible with composition. It is
*cartesian* when every one of those transition maps is an isomorphism.

## Main definitions

* `CategoryTheory.SimplicialDerivedSystem`: the simplicial system, with
  `SimplicialDerivedSystem.Cartesian`, the morphisms `SimplicialDerivedSystem.Hom` and the
  category structure `SimplicialDerivedSystem.category`.
* `CategoryTheory.SimplicialDerivedSystem.cartesianInclusion`: the category of simplicial systems
  with its full subcategory of cartesian systems.
* `CategoryTheory.derivedInverseImage`: inverse image on unbounded derived categories, with
  its compositor `derivedInverseImageCompIso` and unit `derivedInverseImageIdIso`.
* `CategoryTheory.DiagramSystem`: the same shape for an arbitrary strict diagram of categories.
  Its category structure `DiagramSystem.category` has degreewise identities and composition,
  `DiagramSystem.evaluation` reads off a fixed simplicial degree, and `DiagramSystem.isoMk`
  assembles an isomorphism of systems from compatible degreewise isomorphisms.
* `CategoryTheory.derivedCompIso`, `derivedNatIso`, `derivedIdIso`: the three comparisons an
  exact-functor compositor, a natural isomorphism and the identity induce on unbounded
  derived categories.

## Main results

* `derivedCompIso_hom_app_Q`, `derivedCompIso_inv_app_Q`, `derivedNatIso_hom_app_Q` and
  `derivedIdIso_hom_app_Q` compute those three comparisons on the image of a complex, with
  `derivedCompIso_refl_inv_app_Q` and `derivedCompIso_refl_inv_app_Q_comp` the specialization
  at the identity comparison and `derivedCompIso_hom_app_Q_trans` plus
  `derivedCompIso_hom_app_map_trans` the compositor followed by the localization of a map of
  complexes.
* `CategoryTheory.derivedTransition_comp_of_app_Q`: the composition law for three
  transformations of derived functors, from the composition law of the abelian transformations
  they localize and the three formulas for them on the image of a complex.

## Implementation notes

`derivedInverseImage` localizes the exact abelian inverse image `abelianTransition` of the
actual geometric transition morphism of `S`. Its compositor and unit come from the canonical
*geometric* comparisons `CategoryTheory.SimplicialSiteSituation.canonicalCompositionComparison`
and `canonicalIdentityComparison`, transported through internal abelian groups and then localized.
The localization universe is independent of the universe of the given topoi; `HasDerivedCategory`
specifies a model of localization.

Internalizing and externalizing abelian sheaves are inverse to each other by
`CategoryTheory.Sites.AbelianSheaf.internalExternalIso` and `externalInternalIso`.

## References

* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
-/

@[expose] public noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe u v w w'

namespace Functor

/-- A functor applied to an identity, composed with a morphism, is that morphism. -/
theorem map_id_comp {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {X : C} {Y : D} (h : F.obj X ⟶ Y) : F.map (𝟙 X) ≫ h = h := by
  rw [F.map_id, Category.id_comp]

/-- A morphism composed with a functor applied to an identity is that morphism. -/
theorem comp_map_id {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {X : D} {Y : C} (h : X ⟶ F.obj Y) : h ≫ F.map (𝟙 Y) = h := by
  rw [F.map_id, Category.comp_id]

end Functor

section Derived

universe v₁ v₂ v₃ u₁ u₂ u₃ w₁ w₂ w₃
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D] [HasDerivedCategory.{w₃} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The hom of the isomorphism of derived functors induced by an isomorphism of their composites
with the localization functor, on the image of a complex. -/
private theorem preimageIso_hom_app_Q {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {E : Type*} [Category E] {F G : DerivedCategory A ⥤ E}
    (e : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G) (X : CochainComplex A ℤ) :
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) E).preimageIso e).hom.app
        (DerivedCategory.Q.obj X) = e.hom.app X :=
  congrArg (fun t => t.app X) ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) E).map_preimage e.hom)

/-- The inverse of the isomorphism of derived functors induced by an isomorphism of their
composites with the localization functor, on the image of a complex. -/
private theorem preimageIso_inv_app_Q {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {E : Type*} [Category E] {F G : DerivedCategory A ⥤ E}
    (e : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G) (X : CochainComplex A ℤ) :
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) E).preimageIso e).inv.app
        (DerivedCategory.Q.obj X) = e.inv.app X :=
  congrArg (fun t => t.app X) ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) E).map_preimage e.inv)

/-- The canonical comparison on derived categories induced by an exact-functor compositor. -/
def derivedCompIso (e : H ≅ F ⋙ G) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory D)).preimageIso
      (H.mapDerivedCategoryFactors ≪≫
        Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
          DerivedCategory.Q ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          G.mapDerivedCategoryFactors.symm ≪≫
        Functor.isoWhiskerRight F.mapDerivedCategoryFactors.symm G.mapDerivedCategory)

/-- On the image of a complex `X`, the hom of `derivedCompIso F G H e` is the composite of the
factorization isomorphisms with the localization of the map `H X ⟶ G (F X)` induced by `e`. -/
theorem derivedCompIso_hom_app_Q (e : H ≅ F ⋙ G) (X : CochainComplex A ℤ) :
    (derivedCompIso F G H e).hom.app (DerivedCategory.Q.obj X) =
      H.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app X) ≫
        G.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
  rw [derivedCompIso, preimageIso_hom_app_Q]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]

/-- On the image of a complex `X`, the inverse of `derivedCompIso F G H e` is the composite of the
factorization isomorphisms with the localization of the map `G (F X) ⟶ H X` induced by `e`. -/
theorem derivedCompIso_inv_app_Q (e : H ≅ F ⋙ G) (X : CochainComplex A ℤ) :
    (derivedCompIso F G H e).inv.app (DerivedCategory.Q.obj X) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app X) ≫
        H.mapDerivedCategoryFactors.inv.app X := by
  rw [derivedCompIso, preimageIso_inv_app_Q]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv,
    Category.assoc]

/-- On the image of a complex `X`, the inverse of `derivedCompIso F G (F ⋙ G) (Iso.refl _)` is
the composite of the factorization isomorphisms of `F`, `G` and `F ⋙ G`. -/
theorem derivedCompIso_refl_inv_app_Q (X : CochainComplex A ℤ) :
    (derivedCompIso F G (F ⋙ G) (Iso.refl _)).inv.app (DerivedCategory.Q.obj X) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        (F ⋙ G).mapDerivedCategoryFactors.inv.app X := by
  have identity : (NatIso.mapHomologicalComplex
      (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app X = 𝟙 _ :=
    HomologicalComplex.hom_ext _ _ (fun _ => rfl)
  rw [derivedCompIso_inv_app_Q, identity]
  exact congrArg
    (fun g => G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫ g)
    (Functor.map_id_comp DerivedCategory.Q _)

/-- `derivedCompIso_refl_inv_app_Q` followed by the factorization isomorphism of `F ⋙ G` and a
further morphism `h`: the factorization isomorphisms of `F ⋙ G` cancel. -/
theorem derivedCompIso_refl_inv_app_Q_comp {Z : DerivedCategory D}
    (X : CochainComplex A ℤ)
    (h : DerivedCategory.Q.obj
      (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ⟶ Z) :
    (derivedCompIso F G (F ⋙ G) (Iso.refl _)).inv.app (DerivedCategory.Q.obj X) ≫
        (F ⋙ G).mapDerivedCategoryFactors.hom.app X ≫ h =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫ h := by
  rw [derivedCompIso_refl_inv_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The compositor of derived functors, applied after the localization of a map of complexes.
Both identifications of the middle derived functor with the localized one cancel, leaving the
compositor's own complex-level comparison followed by `G` applied to the given map. -/
theorem derivedCompIso_hom_app_Q_trans (e : H ≅ F ⋙ G) (Z : CochainComplex A ℤ)
    (V : CochainComplex B ℤ)
    (g : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ⟶ V)
    {W : DerivedCategory D}
    (k : DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj V) ⟶ W) :
    (derivedCompIso F G H e).hom.app (DerivedCategory.Q.obj Z) ≫
        G.mapDerivedCategory.map
          (F.mapDerivedCategoryFactors.hom.app Z ≫ DerivedCategory.Q.map g) ≫
        G.mapDerivedCategoryFactors.hom.app V ≫ k =
      H.mapDerivedCategoryFactors.hom.app Z ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app Z ≫
            (G.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫ k := by
  rw [derivedCompIso_hom_app_Q]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc]

/-- `derivedCompIso_hom_app_Q_trans` with a map `lf : X ⟶ Q Z` from an arbitrary object of the
derived category prepended. -/
theorem derivedCompIso_hom_app_map_trans (e : H ≅ F ⋙ G)
    {X : DerivedCategory A} (Z : CochainComplex A ℤ) (lf : X ⟶ DerivedCategory.Q.obj Z)
    (V : CochainComplex B ℤ)
    (g : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ⟶ V)
    {W : DerivedCategory D}
    (k : DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj V) ⟶ W) :
    (derivedCompIso F G H e).hom.app X ≫
        G.mapDerivedCategory.map (F.mapDerivedCategory.map lf ≫
          F.mapDerivedCategoryFactors.hom.app Z ≫ DerivedCategory.Q.map g) ≫
        G.mapDerivedCategoryFactors.hom.app V ≫ k =
      H.mapDerivedCategory.map lf ≫ H.mapDerivedCategoryFactors.hom.app Z ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app Z ≫
            (G.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫ k := by
  have naturality :
      H.mapDerivedCategory.map lf ≫
          (derivedCompIso F G H e).hom.app (DerivedCategory.Q.obj Z) =
        (derivedCompIso F G H e).hom.app X ≫
          G.mapDerivedCategory.map (F.mapDerivedCategory.map lf) :=
    (derivedCompIso F G H e).hom.naturality lf
  rw [G.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, ← naturality, Category.assoc]
  exact congrArg (fun t => H.mapDerivedCategory.map lf ≫ t)
    (derivedCompIso_hom_app_Q_trans F G H e Z V g k)
end Derived

section DerivedTransitionComp

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  (L : A ⥤ B) (M : A ⥤ C) (N : A ⥤ D) (F : B ⥤ C) (G : C ⥤ D) (H : B ⥤ D)
  [L.Additive] [M.Additive] [N.Additive] [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

variable (e : H ≅ F ⋙ G)
  (first : L ⋙ F ⟶ M) (second : M ⋙ G ⟶ N) (composite : L ⋙ H ⟶ N)
  (firstDerived : L.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶ M.mapDerivedCategory)
  (secondDerived : M.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶ N.mapDerivedCategory)
  (compositeDerived : L.mapDerivedCategory ⋙ H.mapDerivedCategory ⟶ N.mapDerivedCategory)

/-- The composition law for three transformations of derived functors, deduced from the
composition law of the abelian transformations they localize. Only the three formulas for the
transformations on the image of a complex are used, so the lemma applies to any three
transformations satisfying them. -/
theorem derivedTransition_comp_of_app_Q
    (compatibility : ∀ X, composite.app X =
      e.hom.app (L.obj X) ≫ G.map (first.app X) ≫ second.app X)
    (first_Q : ∀ Z : CochainComplex A ℤ,
      firstDerived.app (DerivedCategory.Q.obj Z) ≫ M.mapDerivedCategoryFactors.hom.app Z =
        F.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app Z) ≫
          F.mapDerivedCategoryFactors.hom.app
            ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex first (ComplexShape.up ℤ)).app Z))
    (second_Q : ∀ Z : CochainComplex A ℤ,
      secondDerived.app (DerivedCategory.Q.obj Z) ≫ N.mapDerivedCategoryFactors.hom.app Z =
        G.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app Z) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((M.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex second (ComplexShape.up ℤ)).app Z))
    (composite_Q : ∀ Z : CochainComplex A ℤ,
      compositeDerived.app (DerivedCategory.Q.obj Z) ≫ N.mapDerivedCategoryFactors.hom.app Z =
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app Z) ≫
          H.mapDerivedCategoryFactors.hom.app
            ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex composite (ComplexShape.up ℤ)).app Z)) :
    compositeDerived =
      Functor.whiskerLeft L.mapDerivedCategory (derivedCompIso F G H e).hom ≫
        Functor.whiskerRight firstDerived G.mapDerivedCategory ≫ secondDerived := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  intro Z
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  refine (cancel_mono (N.mapDerivedCategoryFactors.hom.app Z)).1 ?_
  have complexes :
      (NatTrans.mapHomologicalComplex composite (ComplexShape.up ℤ)).app Z =
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
            ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
          (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex first (ComplexShape.up ℤ)).app Z) ≫
          (NatTrans.mapHomologicalComplex second (ComplexShape.up ℤ)).app Z :=
    HomologicalComplex.hom_ext _ _ fun degree => compatibility (Z.X degree)
  rw [composite_Q, Category.assoc, Category.assoc, second_Q, ← Functor.map_comp_assoc,
    first_Q, derivedCompIso_hom_app_map_trans, complexes,
    ← Category.assoc ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)), DerivedCategory.Q.map_comp]

end DerivedTransitionComp

section DerivedNatIso
universe v₁ v₂ u₁ u₂ w₁ w₂
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- A natural isomorphism of exact functors induces one on derived categories. -/
def derivedNatIso (e : F ≅ G) : F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory B)).preimageIso
      (F.mapDerivedCategoryFactors ≪≫
        Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
          DerivedCategory.Q ≪≫ G.mapDerivedCategoryFactors.symm)

/-- On the image of a complex `X`, the hom of `derivedNatIso F G e` is the localization of the
map `F X ⟶ G X` induced by `e`, conjugated by the factorization isomorphisms. -/
theorem derivedNatIso_hom_app_Q (e : F ≅ G) (X : CochainComplex A ℤ) :
    (derivedNatIso F G e).hom.app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app X) ≫
        G.mapDerivedCategoryFactors.inv.app X := by
  rw [derivedNatIso, preimageIso_hom_app_Q]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom]
end DerivedNatIso

section DerivedIdentity
universe v₁ u₁ w₁
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]

/-- The identity exact functor induces the identity on the derived category. -/
def derivedIdIso :
    (𝟭 A).mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory A)).preimageIso
      ((𝟭 A).mapDerivedCategoryFactors ≪≫
        Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
          DerivedCategory.Q ≪≫ Functor.leftUnitor DerivedCategory.Q)

/-- On the image of a complex `X`, the hom of `derivedIdIso` is the factorization isomorphism of
`𝟭 A` followed by the localization of the identification of `(𝟭 A)` applied to `X` with `X`. -/
theorem derivedIdIso_hom_app_Q (X : CochainComplex A ℤ) :
    (derivedIdIso (A := A)).hom.app (DerivedCategory.Q.obj X) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app X) := by
  rw [derivedIdIso, preimageIso_hom_app_Q]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  simp
end DerivedIdentity

variable (S : SimplicialSiteSituation.{u})

/-- The cartesian monoidal structure on sheaves of types on a component site, given by finite
products. -/
local instance componentCartesian (n : SimplexCategory) :
    CartesianMonoidalCategory (Sheaf (S.componentTopology n) (Type u)) :=
  .ofHasFiniteProducts

/-- The braiding on sheaves of types on a component site induced by its cartesian monoidal
structure. -/
local instance componentBraided (n : SimplexCategory) :
    BraidedCategory (Sheaf (S.componentTopology n) (Type u)) :=
  .ofCartesianMonoidalCategory

/-- Inverse image on abelian sheaves along the transition morphism of topoi of a simplex map. -/
def abelianTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf (S.componentTopology m) Ab.{u} ⥤ Sheaf (S.componentTopology n) Ab.{u} :=
  abelianInverseImage (S.transitionMorphism φ)

/-- The transition is exact, being an inverse image of abelian sheaves. -/
theorem abelianTransition_exact {m n : SimplexCategory} (φ : m ⟶ n) :
    exactFunctor (Sheaf (S.componentTopology m) Ab.{u})
      (Sheaf (S.componentTopology n) Ab.{u}) (abelianTransition S φ) :=
  abelianInverseImage_exact (S.transitionMorphism φ)

/-- The abelian transition functor preserves finite limits. -/
instance abelianTransition_preservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits (abelianTransition S φ) :=
  (abelianTransition_exact S φ).1

/-- The abelian transition functor preserves finite colimits. -/
instance abelianTransition_preservesFiniteColimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteColimits (abelianTransition S φ) :=
  (abelianTransition_exact S φ).2

/-- The abelian inverse-image compositor induced by the canonical geometric compositor. -/
def abelianCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    abelianTransition S (ψ ≫ φ) ≅ abelianTransition S ψ ⋙ abelianTransition S φ := by
  let f := S.transitionMorphism ψ
  let g := S.transitionMorphism φ
  let h := S.transitionMorphism (ψ ≫ φ)
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : PreservesFiniteLimits g.inverseImage := g.preservesFiniteLimits
  letI : PreservesFiniteLimits h.inverseImage := h.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : g.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : h.inverseImage.Braided := .ofChosenFiniteProducts _
  let α := Functor.mapCommGrpNatIso
      (SimplicialSiteSituation.canonicalCompositionComparison S ψ φ) ≪≫
    Functor.mapCommGrpCompIso
  exact Functor.isoWhiskerLeft (AbelianSheaf.internalSheaf (S.componentTopology l))
      (Functor.isoWhiskerRight α (AbelianSheaf.externalSheaf (S.componentTopology n))) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (AbelianSheaf.internalSheaf (S.componentTopology l) ⋙ f.inverseImage.mapCommGrp)
        (AbelianSheaf.externalInternalIso (S.componentTopology m)).symm)
      (g.inverseImage.mapCommGrp ⋙ AbelianSheaf.externalSheaf (S.componentTopology n))

/-- The abelian inverse-image unit induced by the canonical geometric unit. -/
def abelianIdIso (n : SimplexCategory) :
    abelianTransition S (𝟙 n) ≅ 𝟭 _ := by
  let f := S.transitionMorphism (𝟙 n)
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  let α := Functor.mapCommGrpNatIso (SimplicialSiteSituation.canonicalIdentityComparison S n) ≪≫
    Functor.mapCommGrpIdIso
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (AbelianSheaf.internalSheaf (S.componentTopology n)) α)
      (AbelianSheaf.externalSheaf (S.componentTopology n)) ≪≫
    Functor.isoWhiskerRight
      (Functor.rightUnitor (AbelianSheaf.internalSheaf (S.componentTopology n)))
      (AbelianSheaf.externalSheaf (S.componentTopology n)) ≪≫
    AbelianSheaf.internalExternalIso (S.componentTopology n)

/-- The abelian transition functor is additive. -/
instance abelianTransition_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianTransition S φ).Additive :=
  Functor.additive_of_preserves_binary_products _

variable [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- Inverse image on unbounded derived categories, obtained by applying exact inverse image
to complexes and localizing at quasi-isomorphisms. -/
def derivedInverseImage {m n : SimplexCategory} (φ : m ⟶ n) :
    DerivedCategory (Sheaf (S.componentTopology m) Ab.{u}) ⥤
      DerivedCategory (Sheaf (S.componentTopology n) Ab.{u}) :=
  (abelianTransition S φ).mapDerivedCategory

/-- The canonical identification of composite and successive derived inverse images. -/
def derivedInverseImageCompIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    derivedInverseImage S (ψ ≫ φ) ≅ derivedInverseImage S ψ ⋙ derivedInverseImage S φ :=
  derivedCompIso _ _ _ (abelianCompIso S ψ φ)

/-- The canonical identification of identity derived inverse image with the identity. -/
def derivedInverseImageIdIso (n : SimplexCategory) :
    derivedInverseImage S (𝟙 n) ≅ 𝟭 _ :=
  derivedNatIso _ _ (abelianIdIso S n) ≪≫ derivedIdIso

/-- A simplicial system of the derived category for `S`: an object `K_n` of the derived category
of abelian sheaves on each component site, and for every simplex map `φ : [m] ⟶ [n]` a map
`K_φ : f_φ⁻¹K_m ⟶ K_n` from the derived inverse image, such that `K_{φ ∘ ψ}` is
`K_φ ∘ f_φ⁻¹K_ψ` under the canonical identification `f_{φ ∘ ψ}⁻¹ ≅ f_φ⁻¹ ∘ f_ψ⁻¹`. As in the
source, no condition is imposed at identities. -/
@[stacks 0D9G "the simplicial system"]
structure SimplicialDerivedSystem where
  /-- An object of the unbounded derived category of abelian sheaves in each degree. -/
  obj : ∀ n, DerivedCategory (Sheaf (S.componentTopology n) Ab.{u})
  /-- The map from the actual derived inverse image along a simplex map. -/
  map : ∀ {m n} (φ : m ⟶ n), (derivedInverseImage S φ).obj (obj m) ⟶ obj n
  /-- Compatibility with composition under the canonical inverse-image identification. -/
  map_comp : ∀ {l m n} (ψ : l ⟶ m) (φ : m ⟶ n),
    map (ψ ≫ φ) = (derivedInverseImageCompIso S ψ φ).hom.app (obj l) ≫
      (derivedInverseImage S φ).map (map ψ) ≫ map φ

namespace SimplicialDerivedSystem

variable {S}

/-- A system is cartesian if all its transition maps are isomorphisms. -/
@[stacks 0D9G "cartesian systems"]
abbrev Cartesian (K : SimplicialDerivedSystem S) : Prop :=
  ∀ {m n} (φ : m ⟶ n), IsIso (K.map φ)

/-- A morphism is a degreewise morphism commuting with every transition map. -/
@[stacks 0D9G "morphisms of simplicial systems"]
structure Hom (K L : SimplicialDerivedSystem S) where
  /-- The morphism in each simplicial degree. -/
  app : ∀ n, K.obj n ⟶ L.obj n
  /-- Compatibility with the actual derived inverse-image transitions. -/
  naturality : ∀ {m n} (φ : m ⟶ n),
    K.map φ ≫ app n = (derivedInverseImage S φ).map (app m) ≫ L.map φ

/-- A morphism of simplicial systems is determined by its degreewise components. -/
@[ext] theorem Hom.ext' {K L : SimplicialDerivedSystem S} (f g : Hom K L)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- Simplicial systems of the derived category form a category, with degreewise identities and
composition. -/
instance category : Category (SimplicialDerivedSystem S) where
  Hom := Hom
  id K := ⟨fun n ↦ 𝟙 (K.obj n), fun φ ↦ by
    rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]⟩
  comp f g := ⟨fun n ↦ f.app n ≫ g.app n, fun φ ↦ by
    rw [← Category.assoc, f.naturality, Category.assoc, g.naturality, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp]⟩
  id_comp _ := Hom.ext' _ _ fun _ ↦ Category.id_comp _
  comp_id _ := Hom.ext' _ _ fun _ ↦ Category.comp_id _
  assoc _ _ _ := Hom.ext' _ _ fun _ ↦ Category.assoc _ _ _

/-- Morphisms of simplicial systems are determined by their degreewise components. -/
@[ext] theorem hom_ext {K L : SimplicialDerivedSystem S} {f g : K ⟶ L}
    (h : ∀ n, Hom.app f n = Hom.app g n) : f = g :=
  Hom.ext' f g h

/-- The identity morphism of a simplicial system is the identity in each degree. -/
@[simp] theorem id_app (K : SimplicialDerivedSystem S) (n : SimplexCategory) :
    Hom.app (𝟙 K) n = 𝟙 (K.obj n) := rfl

/-- Composition of morphisms of simplicial systems is degreewise composition. -/
@[simp] theorem comp_app {K L M : SimplicialDerivedSystem S} (f : K ⟶ L) (g : L ⟶ M)
    (n : SimplexCategory) : Hom.app (f ≫ g) n = Hom.app f n ≫ Hom.app g n := rfl

variable (S) in
/-- The cartesian simplicial systems, as a property of objects of the category of systems. -/
def cartesian : ObjectProperty (SimplicialDerivedSystem S) := fun K ↦ K.Cartesian

variable (S) in
/-- Simplicial systems of the derived category: the category whose objects are the systems
`(K_n, K_φ)` of `SimplicialDerivedSystem S` and whose morphisms are the degreewise maps commuting
with the transitions (`SimplicialDerivedSystem.Hom`), together with its full subcategory of
cartesian systems, those whose transitions `K_φ` are all isomorphisms. -/
@[stacks 0D9G]
def cartesianInclusion : (cartesian S).FullSubcategory ⥤ SimplicialDerivedSystem S :=
  (cartesian S).ι

end SimplicialDerivedSystem

/-- Compatible objects and transition maps for a strict diagram of categories. -/
public structure DiagramSystem (D : SimplexCategory ⥤ Cat.{v, u}) where
  /-- The object in each simplicial degree. -/
  obj : ∀ n, D.obj n
  /-- The transition map associated to a simplex map. -/
  map : ∀ {m n} (φ : m ⟶ n), (D.map φ).toFunctor.obj (obj m) ⟶ obj n
  /-- Compatibility of transition maps with composition. -/
  map_comp : ∀ {l m n} (ψ : l ⟶ m) (φ : m ⟶ n),
    map (ψ ≫ φ) =
      eqToHom (by simp) ≫ (D.map φ).toFunctor.map (map ψ) ≫ map φ

namespace DiagramSystem

/-- A simplicial system is cartesian if every transition map is an isomorphism. -/
public abbrev Cartesian {D : SimplexCategory ⥤ Cat.{v, u}}
    (K : DiagramSystem D) : Prop :=
  ∀ {m n} (φ : m ⟶ n), IsIso (K.map φ)

/-- A morphism of simplicial systems is a degreewise morphism commuting with every transition
map. -/
public structure Hom {D : SimplexCategory ⥤ Cat.{v, u}}
    (K L : DiagramSystem D) where
  /-- The morphism in each simplicial degree. -/
  app : ∀ n, K.obj n ⟶ L.obj n
  /-- Compatibility with transition maps. -/
  naturality : ∀ {m n} (φ : m ⟶ n),
    K.map φ ≫ app n = (D.map φ).toFunctor.map (app m) ≫ L.map φ

variable {D : SimplexCategory ⥤ Cat.{v, u}}

/-- A morphism of simplicial systems is determined by its degreewise components. -/
@[ext] public theorem hom_ext {K L : DiagramSystem D} (f g : Hom K L)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- Simplicial systems for a strict diagram of categories form a category, with degreewise
identities and composition. -/
public instance category : Category (DiagramSystem D) where
  Hom := Hom
  id K := ⟨fun n ↦ 𝟙 (K.obj n), by intros; simp⟩
  comp f g := ⟨fun n ↦ f.app n ≫ g.app n, by
    intro m n φ
    rw [← Category.assoc, f.naturality, Category.assoc, g.naturality, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp]⟩
  id_comp _ := hom_ext _ _ fun _ ↦ Category.id_comp _
  comp_id _ := hom_ext _ _ fun _ ↦ Category.comp_id _
  assoc _ _ _ := hom_ext _ _ fun _ ↦ Category.assoc _ _ _

/-- Evaluation of a simplicial system in a fixed simplicial degree. -/
public def evaluation (n : SimplexCategory) : DiagramSystem D ⥤ D.obj n where
  obj K := K.obj n
  map f := f.app n

/-- Degreewise isomorphisms compatible with the transition maps assemble into an isomorphism of
simplicial systems. -/
public def isoMk (K L : DiagramSystem D) (e : ∀ n, K.obj n ≅ L.obj n)
    (h : ∀ {m n} (φ : m ⟶ n),
      K.map φ ≫ (e n).hom = (D.map φ).toFunctor.map (e m).hom ≫ L.map φ) :
    K ≅ L where
  hom := ⟨fun n ↦ (e n).hom, h⟩
  inv := ⟨fun n ↦ (e n).inv, by
    intro m n φ
    refine (cancel_mono (e n).hom).1 ?_
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h φ, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]⟩
  hom_inv_id := hom_ext _ _ fun _ ↦ Iso.hom_inv_id _
  inv_hom_id := hom_ext _ _ fun _ ↦ Iso.inv_hom_id _

end DiagramSystem

end CategoryTheory
