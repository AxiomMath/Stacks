module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOnRingedTopoi
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of derived base change maps for ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)`, `g : (Sh(D), 𝒪_D) ⟶ (Sh(E), 𝒪_E)` and
`h : (Sh(E), 𝒪_E) ⟶ (Sh(F), 𝒪_F)` be morphisms of ringed topoi.  The composition formula of
Stacks 0D6D compares the composite of two derived pullbacks with the derived pullback along the
composite, and for three composable morphisms there are two ways to compare the threefold
composite `Lh^* ⋙ Lg^* ⋙ Lf^*` with `L(h ∘ g ∘ f)^*`.  This file proves that they agree.

That cocycle identity is the geometric input to the two compatibilities of the derived base
change map of Stacks 07A7 with composition of diagrams, Stacks 0E46 and Stacks 0E47.

## Main results

* `pushforwardToposCompIso_assoc`: the cocycle identity for the direct-image composition
  isomorphism of sheaves of modules on ringed topoi.  Both sides are the identity on sections.
* `pullbackToposCompIso_assoc`: its left-adjoint companion for inverse image, by
  `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`.
* `pullbackOnHomotopyCompIso_assoc`: the same on the unbounded homotopy categories.
* `derivedPullbackCompComparison_assoc`: **the cocycle identity of Stacks 0D6D**, for the
  canonical comparison
  `Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompComparison` on the
  unbounded derived categories.

## Implementation notes

*Composition of morphisms of ringed topoi is strictly associative.*
`AlgebraicGeometry.RingedToposSiteHom.comp` composes the underlying continuous functors, where
associativity is strict, and its structure map involves
`CategoryTheory.Functor.sheafPushforwardContinuousComp`, whose components are identities; so
`(h ∘ g) ∘ f = h ∘ (g ∘ f)` holds by `rfl`.  No transport along an associativity isomorphism
appears below, in contrast with the ringed-space development
`Stacks.Cohomology.DerivedPushforwardAssociativity`.  Instance resolution is still syntactic, so
the `HasLeftDerivedFunctor` hypothesis for the threefold composite is carried in both
bracketings.

*Why the derived step goes through a lemma on abstract functors.*
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback` is a reducible
abbreviation over a total derived functor, and a rewriting step performed at these types forces
the elaborator and then the kernel to unfold the localization construction.
`leftDerived_comparison_assoc` carries out the whole argument with every functor a variable, and
the geometric statement is a single application of it; the same factorization is used by the
ringed-space analogue.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi

namespace Stacks.Cohomology.DerivedBaseChangeComposition

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-! ### Abstract bookkeeping -/

/-- Naturality of a transformation out of a composite functor, with the composite unfolded. -/
theorem natTrans_comp_naturality_assoc {A B A' B' : Type*}
    [Category* A] [Category* B] [Category* A'] [Category* B']
    {P : A ⥤ B} {Q : B ⥤ B'} {R : A ⥤ A'} {S : A' ⥤ B'}
    (α : P ⋙ Q ⟶ R ⋙ S) {M N : A} (p : M ⟶ N) {T : B'}
    (q : S.obj (R.obj N) ⟶ T) :
    Q.map (P.map p) ≫ α.app N ≫ q = α.app M ≫ S.map (R.map p) ≫ q := by
  simpa only [Functor.comp_map] using α.naturality_assoc p q

/-- Associativity of the composition isomorphisms induced on homotopy categories by composition
isomorphisms of additive functors. -/
theorem mapHomotopyCategoryCompIso_assoc {C₀ C₁ C₂ C₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [Preadditive C₀] [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃}
    {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
    [F₀₁.Additive] [F₁₂.Additive] [F₂₃.Additive]
    [F₀₂.Additive] [F₁₃.Additive] [F₀₃.Additive]
    (e₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂) (e₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃)
    (e₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃) (e₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃)
    (h : Functor.whiskerLeft F₀₁ e₁₂₃.hom ≫ e₀₁₃.hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e₀₁₂.hom F₂₃ ≫ e₀₂₃.hom)
    {ι : Type*} (c : ComplexShape ι) :
    Functor.whiskerLeft (F₀₁.mapHomotopyCategory c)
          (Functor.mapHomotopyCategoryCompIso e₁₂₃ c).hom ≫
        (Functor.mapHomotopyCategoryCompIso e₀₁₃ c).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso e₀₁₂ c).hom
          (F₂₃.mapHomotopyCategory c) ≫
        (Functor.mapHomotopyCategoryCompIso e₀₂₃ c).hom := by
  apply NatTrans.ext
  funext K
  rcases K with ⟨K⟩
  change (HomotopyCategory.quotient C₃ c).map
      ((Functor.mapHomologicalComplexCompIso e₁₂₃ c).hom.app
        ((F₀₁.mapHomologicalComplex c).obj K)) ≫
      (HomotopyCategory.quotient C₃ c).map
        ((Functor.mapHomologicalComplexCompIso e₀₁₃ c).hom.app K) =
    𝟙 _ ≫ (HomotopyCategory.quotient C₃ c).map
      ((F₂₃.mapHomologicalComplex c).map
        ((Functor.mapHomologicalComplexCompIso e₀₁₂ c).hom.app K)) ≫
      (HomotopyCategory.quotient C₃ c).map
        ((Functor.mapHomologicalComplexCompIso e₀₂₃ c).hom.app K)
  simp only [Category.id_comp, ← Functor.map_comp]
  apply congrArg (HomotopyCategory.quotient C₃ c).map
  ext i
  simpa using NatTrans.congr_app h (K.X i)

/-- Associativity transported through the universal property of a left derived functor: if the
comparison maps of three composable functors satisfy the expected factorizations, the induced
composition maps of the derived functors are associative. -/
theorem leftDerived_comparison_assoc
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₀] [Category* D₁] [Category* D₂] [Category* D₃]
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {Q₃ : C₃ ⥤ D₃}
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃}
    {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
    {L₀₁ : D₀ ⥤ D₁} {L₁₂ : D₁ ⥤ D₂} {L₂₃ : D₂ ⥤ D₃}
    {L₀₂ : D₀ ⥤ D₂} {L₁₃ : D₁ ⥤ D₃} {L₀₃ : D₀ ⥤ D₃}
    (α₀₁ : Q₀ ⋙ L₀₁ ⟶ F₀₁ ⋙ Q₁) (α₁₂ : Q₁ ⋙ L₁₂ ⟶ F₁₂ ⋙ Q₂)
    (α₂₃ : Q₂ ⋙ L₂₃ ⟶ F₂₃ ⋙ Q₃) (α₀₂ : Q₀ ⋙ L₀₂ ⟶ F₀₂ ⋙ Q₂)
    (α₁₃ : Q₁ ⋙ L₁₃ ⟶ F₁₃ ⋙ Q₃) (α₀₃ : Q₀ ⋙ L₀₃ ⟶ F₀₃ ⋙ Q₃)
    (W : MorphismProperty C₀) [Q₀.IsLocalization W] [L₀₃.IsLeftDerivedFunctor α₀₃ W]
    (c₀₁₂ : F₀₁ ⋙ F₁₂ ⟶ F₀₂) (c₁₂₃ : F₁₂ ⋙ F₂₃ ⟶ F₁₃)
    (c₀₁₃ : F₀₁ ⋙ F₁₃ ⟶ F₀₃) (c₀₂₃ : F₀₂ ⋙ F₂₃ ⟶ F₀₃)
    (d₀₁₂ : L₀₁ ⋙ L₁₂ ⟶ L₀₂) (d₁₂₃ : L₁₂ ⋙ L₂₃ ⟶ L₁₃)
    (d₀₁₃ : L₀₁ ⋙ L₁₃ ⟶ L₀₃) (d₀₂₃ : L₀₂ ⋙ L₂₃ ⟶ L₀₃)
    (fac₀₁₂ : ∀ M, d₀₁₂.app (Q₀.obj M) ≫ α₀₂.app M =
      L₁₂.map (α₀₁.app M) ≫ α₁₂.app (F₀₁.obj M) ≫ Q₂.map (c₀₁₂.app M))
    (fac₁₂₃ : ∀ M, d₁₂₃.app (Q₁.obj M) ≫ α₁₃.app M =
      L₂₃.map (α₁₂.app M) ≫ α₂₃.app (F₁₂.obj M) ≫ Q₃.map (c₁₂₃.app M))
    (fac₀₁₃ : ∀ M, d₀₁₃.app (Q₀.obj M) ≫ α₀₃.app M =
      L₁₃.map (α₀₁.app M) ≫ α₁₃.app (F₀₁.obj M) ≫ Q₃.map (c₀₁₃.app M))
    (fac₀₂₃ : ∀ M, d₀₂₃.app (Q₀.obj M) ≫ α₀₃.app M =
      L₂₃.map (α₀₂.app M) ≫ α₂₃.app (F₀₂.obj M) ≫ Q₃.map (c₀₂₃.app M))
    (hc : Functor.whiskerLeft F₀₁ c₁₂₃ ≫ c₀₁₃ =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight c₀₁₂ F₂₃ ≫ c₀₂₃) :
    Functor.whiskerLeft L₀₁ d₁₂₃ ≫ d₀₁₃ =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight d₀₁₂ L₂₃ ≫ d₀₂₃ := by
  apply L₀₃.leftDerived_ext α₀₃ W
  ext M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app]
  simp only [Category.id_comp, Category.assoc, fac₀₁₃, fac₀₂₃]
  rw [← d₁₂₃.naturality_assoc]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [reassoc_of% (fac₁₂₃ (F₀₁.obj M))]
  rw [← L₂₃.map_comp_assoc (d₀₁₂.app (Q₀.obj M)) (α₀₂.app M), fac₀₁₂]
  simp only [Functor.map_comp, Category.assoc]
  rw [natTrans_comp_naturality_assoc α₂₃]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  have hcM := NatTrans.congr_app hc M
  dsimp at hcM
  simp only [Category.id_comp] at hcM
  rw [← Q₃.map_comp, ← Q₃.map_comp, hcM]

/-! ### The cocycle identity for the composition isomorphisms -/

section Cocycle

variable {X Y Z W : RingedTopos.{u, u, u}}
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z) (h : RingedToposSiteHom Z W)

/-- **The cocycle identity for the direct-image composition isomorphism.**  The two ways of
identifying the direct image of a threefold composite of morphisms of ringed topoi with the
threefold composite of the direct images agree.

Both sides are the identity on sections, by
`AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso_hom_app_val_app`. -/
theorem pushforwardToposCompIso_assoc :
    Functor.isoWhiskerLeft f.pushforwardTopos
          (RingedToposSiteHom.pushforwardToposCompIso g h).symm ≪≫
        (RingedToposSiteHom.pushforwardToposCompIso f (h.comp g)).symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (RingedToposSiteHom.pushforwardToposCompIso f g).symm
          h.pushforwardTopos ≪≫
        (RingedToposSiteHom.pushforwardToposCompIso (g.comp f) h).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rfl

/-- **The cocycle identity for the inverse-image composition isomorphism.**  This is the
left-adjoint companion of `pushforwardToposCompIso_assoc`, by
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`. -/
theorem pullbackToposCompIso_assoc :
    Functor.isoWhiskerLeft h.pullbackTopos (RingedToposSiteHom.pullbackToposCompIso f g) ≪≫
        RingedToposSiteHom.pullbackToposCompIso (g.comp f) h =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (RingedToposSiteHom.pullbackToposCompIso g h) f.pullbackTopos ≪≫
          RingedToposSiteHom.pullbackToposCompIso f (h.comp g) :=
  Adjunction.leftAdjointCompIso_assoc h.pullbackPushforwardAdjunctionTopos
    g.pullbackPushforwardAdjunctionTopos f.pullbackPushforwardAdjunctionTopos
    (h.comp g).pullbackPushforwardAdjunctionTopos (g.comp f).pullbackPushforwardAdjunctionTopos
    (h.comp (g.comp f)).pullbackPushforwardAdjunctionTopos _ _ _ _
    (pushforwardToposCompIso_assoc f g h)

/-- The cocycle identity for the inverse-image composition isomorphism, read on the unbounded
homotopy categories of complexes of sheaves of modules. -/
theorem pullbackOnHomotopyCompIso_assoc :
    Functor.whiskerLeft (h.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
          (pullbackOnHomotopyCompIso f g).hom ≫
        (pullbackOnHomotopyCompIso (g.comp f) h).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pullbackOnHomotopyCompIso g h).hom
          (f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)) ≫
        (pullbackOnHomotopyCompIso f (h.comp g)).hom :=
  mapHomotopyCategoryCompIso_assoc _ _ _ _
    (congrArg Iso.hom (pullbackToposCompIso_assoc f g h)) (ComplexShape.up ℤ)

variable
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy h).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (h.comp g)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (h.comp (g.comp f))).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ((h.comp g).comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O))
      (ComplexShape.up ℤ))]

/-- **The cocycle identity for the composition comparison of Stacks 0D6D.**  For three
composable morphisms of ringed topoi the two ways of comparing the threefold composite of
derived pullbacks with the derived pullback along the composite agree.

The comparison is defined by the universal property of the derived pullback along the threefold
composite, so the identity follows from the cocycle identity on the homotopy categories together
with the factorization `derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app`
characterizing each comparison. -/
theorem derivedPullbackCompComparison_assoc :
    Functor.whiskerLeft (derivedPullback h) (derivedPullbackCompComparison f g) ≫
        derivedPullbackCompComparison (g.comp f) h =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedPullbackCompComparison g h) (derivedPullback f) ≫
          derivedPullbackCompComparison f (h.comp g) :=
  leftDerived_comparison_assoc (derivedPullbackComparison h) (derivedPullbackComparison g)
    (derivedPullbackComparison f) (derivedPullbackComparison (h.comp g))
    (derivedPullbackComparison (g.comp f)) (derivedPullbackComparison (h.comp (g.comp f)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O))
      (ComplexShape.up ℤ))
    (pullbackOnHomotopyCompIso g h).hom (pullbackOnHomotopyCompIso f g).hom
    (pullbackOnHomotopyCompIso (g.comp f) h).hom (pullbackOnHomotopyCompIso f (h.comp g)).hom
    (derivedPullbackCompComparison g h) (derivedPullbackCompComparison f g)
    (derivedPullbackCompComparison (g.comp f) h) (derivedPullbackCompComparison f (h.comp g))
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app g h)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f g)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app (g.comp f) h)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f (h.comp g))
    (pullbackOnHomotopyCompIso_assoc f g h)

end Cocycle

end

end Stacks.Cohomology.DerivedBaseChangeComposition

end
