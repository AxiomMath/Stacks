module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompKunneth
public import StacksFrontier.CategoryTheory.Adjunction.KunnethBaseChangeCompLocal

/-!
# Étale locality on `X` of the Künneth map of Stacks 0DKH

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces, `E ∈ D(𝒪_X)`,
`K' ∈ D(𝒪_{X'})` and `φ : L(g')^*E ⟶ K'`.  The map on `X`

`E ⊗ᴸ Lf^*Rg_*𝒪_{Y'} ⟶ Rg'_*(K' ⊗ᴸ L(f')^*𝒪_{Y'})`

(`AlgebraicGeometry.Space.smallEtaleTensorBaseChangeCompMap`) to which Stacks 0DKH over an affine
`Y'` reduces is invertible as soon as, for every member `u : U ⟶ X` of a covering family of
étale charts and a fibre product `U' = U ×_X X'`, the map attached to the square `U' ⟶ U` over
`Y' ⟶ Y`, to `E|_U`, `K'|_{U'}` and the restriction of `φ`, is invertible.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedSquareComparison_cube`: the comparisons of iterated
  derived pullbacks of two vertically stacked squares and of their outer square agree.
* `AlgebraicGeometry.Space.smallEtaleTensorBaseChangeCompMap_restrict`: restricting the map along
  an étale chart of `X`.
* `AlgebraicGeometry.Space.isIso_map_smallEtaleTensorBaseChangeCompMap_of_isEtale`: the
  restriction along an étale morphism.
* `AlgebraicGeometry.Space.isIso_smallEtaleTensorBaseChangeCompMap_of_coversTop`: étale locality
  on `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)
open Stacks.Cohomology.DerivedBaseChangePasting
open scoped CategoryTheory.Prod

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Cube

variable {X Y : AlgebraicSpaces B S hS}

/-- The forward direction of `smallEtaleDerivedModulePullbackCongr`, componentwise. -/
theorem smallEtaleDerivedModulePullbackCongr_hom_app {p q : X ⟶ Y} (e : p = q)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (smallEtaleDerivedModulePullbackCongr B S hS e).hom.app M =
      (transportNatTrans
        (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) e)).app M := by
  subst e
  simp [smallEtaleDerivedModulePullbackCongr]

variable {X X' Y Y' Z Z' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y')
  (g' : Y' ⟶ Z') (k : X' ⟶ X) (l : Y' ⟶ Y) (m : Z' ⟶ Z)

/-- **The comparisons of iterated derived pullbacks of a vertical stack of squares.**  For
squares `f' ≫ l = k ≫ f` and `l ≫ g = g' ≫ m`, the comparison `L(f' ≫ g')^* Lm^* ⟶ Lk^* L(f ≫ g)^*`
of the outer square is the comparison of the lower square under `Lf'^*`, followed by that of the
upper square, read through the composition laws of `f, g` and of `f', g'`. -/
theorem smallEtaleDerivedSquareComparison_cube (wtop : f' ≫ l = k ≫ f)
    (wbot : l ≫ g = g' ≫ m) (M : _) :
    (smallEtaleDerivedModulePullbackCompIso B S hS (f' ≫ g') m).hom.app M ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS (f ≫ g) m (f' ≫ g') k
          (comp_stack B S hS f g f' g' k l m wtop.symm wbot)).inv.app M =
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g').inv.app
          ((smallEtaleDerivedModulePullback B S hS m).obj M) ≫
        (smallEtaleDerivedModulePullback B S hS f').map
          ((smallEtaleDerivedModulePullbackCompIso B S hS g' m).hom.app M ≫
            (smallEtaleDerivedModulePullbackSquareIso B S hS g m g' l wbot).inv.app M) ≫
        ((smallEtaleDerivedModulePullbackSquareIso B S hS l f k f' wtop).hom.app
            ((smallEtaleDerivedModulePullback B S hS g).obj M) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS k f).inv.app
            ((smallEtaleDerivedModulePullback B S hS g).obj M)) ≫
        (smallEtaleDerivedModulePullback B S hS k).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app M) := by
  rw [smallEtaleDerivedPullbackSquareIso_inv_app, smallEtaleDerivedPullbackSquareIso_inv_app,
    smallEtaleDerivedPullbackSquareIso_hom, NatTrans.comp_app,
    smallEtaleDerivedModulePullbackCongr_hom_app]
  simpa only [Category.assoc] using
    smallEtaleDerivedSquareComparison_vertical B S hS f g f' g' k l m wtop.symm wbot M

end Cube

/-- Tensoring an isomorphism with an identity in the first variable gives an isomorphism. -/
theorem isIso_uncurry_map_id_prod {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) (a : C) {b c : C}
    (x : b ⟶ c) [IsIso x] : IsIso ((Functor.uncurry.obj T).map (𝟙 a ×ₘ x)) := by
  have hc : (Functor.uncurry.obj T).map (𝟙 a ×ₘ x) = (T.obj a).map x := by simp
  rw [hc]
  infer_instance

section Restrict

variable {X Y X' Y' U U' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (u : U ⟶ X) (h : U' ⟶ U) (u' : U' ⟶ X')

/-- **Restriction of the Künneth map along a square over `X`.**  For a commutative square
`u' ≫ g' = h ≫ u`, `Lu^*` of the map attached to `φ`, followed by the base change map of that
square and the comparisons of Stacks 07A4 and 0D6D, is the comparison of Stacks 07A4 followed by
the map attached to the outer square `U' ⟶ U` over `Y' ⟶ Y`, to `Lu^*E`, `L(u')^*K'` and the
restriction of `φ`. -/
theorem smallEtaleTensorBaseChangeCompMap_restrict (w : g' ≫ f = f' ≫ g)
    (wu : u' ≫ g' = h ≫ u)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj E ⟶ K') :
    (smallEtaleDerivedModulePullback B S hS u).map
          (smallEtaleTensorBaseChangeCompMap B S hS f g f' g' w E K' φ) ≫
        smallEtaleDerivedModuleBaseChangeMap B S hS g' u h u' wu
          (((smallEtaleDerivedTensor B S hS X').obj K').obj
            ((smallEtaleDerivedModulePullback B S hS f').obj (structureDerived Y'))) ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
            (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS h)).map
          ((smallEtaleDerivedPullbackTensorIso u').hom.app
              (K', (smallEtaleDerivedModulePullback B S hS f').obj (structureDerived Y')) ≫
            (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS U')).map
              (𝟙 ((smallEtaleDerivedModulePullback B S hS u').obj K') ×ₘ
                (smallEtaleDerivedModulePullbackCompIso B S hS u' f').hom.app
                  (structureDerived Y'))) =
      ((smallEtaleDerivedPullbackTensorIso u).hom.app
            (E, (smallEtaleDerivedModulePullback B S hS f).obj
              ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
                (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS g)).obj
                (structureDerived Y'))) ≫
          (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS U)).map
            (𝟙 ((smallEtaleDerivedModulePullback B S hS u).obj E) ×ₘ
              (smallEtaleDerivedModulePullbackCompIso B S hS u f).hom.app
                ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
                  (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS g)).obj
                  (structureDerived Y')))) ≫
        smallEtaleTensorBaseChangeCompMap B S hS (u ≫ f) g (u' ≫ f') h
          (comp_stack B S hS u f u' f' h g' g wu.symm w)
          ((smallEtaleDerivedModulePullback B S hS u).obj E)
          ((smallEtaleDerivedModulePullback B S hS u').obj K')
          (((smallEtaleDerivedModulePullbackCompIso B S hS h u).hom ≫
              (smallEtaleDerivedModulePullbackSquareIso B S hS g' u h u' wu).inv).app E ≫
            (smallEtaleDerivedModulePullback B S hS u').map φ) :=
  Stacks.CategoryTheory.KunnethBaseChange.map_tensorBaseChangeCompMap_comp_baseChange
    (smallEtaleDerivedModuleAdjunction B S hS g) (smallEtaleDerivedModuleAdjunction B S hS g')
    (smallEtaleDerivedModuleAdjunction B S hS h)
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w)
    (smallEtaleDerivedModulePullbackCompIso B S hS (u' ≫ f') g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS (u ≫ f) g (u' ≫ f') h
      (comp_stack B S hS u f u' f' h g' g wu.symm w))
    (smallEtaleDerivedModulePullbackCompIso B S hS h u)
    (smallEtaleDerivedModulePullbackSquareIso B S hS g' u h u' wu)
    (smallEtaleDerivedModulePullbackCompIso B S hS u f)
    (smallEtaleDerivedModulePullbackCompIso B S hS u' f')
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X'))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS U))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS U'))
    (smallEtaleDerivedPullbackTensorIso g').hom (smallEtaleDerivedPullbackTensorIso h).hom
    (smallEtaleDerivedPullbackTensorIso u).hom (smallEtaleDerivedPullbackTensorIso u').hom
    E (structureDerived Y') φ
    (smallEtaleDerivedSquareComparison_cube B S hS u f u' f' h g' g wu w _)
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso g' u h u' wu _ _)

/-- **The Künneth map restricted along an étale morphism.**  For a cartesian square
`u' ≫ g' = h ≫ u` with `u` étale, `Lu^*` of the map attached to `φ` is invertible as soon as the
map attached to the outer square, to `Lu^*E`, `L(u')^*K'` and the restriction of `φ`, is. -/
theorem isIso_map_smallEtaleTensorBaseChangeCompMap_of_isEtale (w : g' ≫ f = f' ≫ g)
    (squ : IsPullback u' h g' u) (hu : IsEtale B S hS u.hom)
    (hrep : yoneda.relativelyRepresentable u.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj E ⟶ K')
    (hU : IsIso (smallEtaleTensorBaseChangeCompMap B S hS (u ≫ f) g (u' ≫ f') h
      (comp_stack B S hS u f u' f' h g' g squ.w.symm w)
      ((smallEtaleDerivedModulePullback B S hS u).obj E)
      ((smallEtaleDerivedModulePullback B S hS u').obj K')
      (((smallEtaleDerivedModulePullbackCompIso B S hS h u).hom ≫
          (smallEtaleDerivedModulePullbackSquareIso B S hS g' u h u' squ.w).inv).app E ≫
        (smallEtaleDerivedModulePullback B S hS u').map φ))) :
    IsIso ((smallEtaleDerivedModulePullback B S hS u).map
      (smallEtaleTensorBaseChangeCompMap B S hS f g f' g' w E K' φ)) := by
  have e := smallEtaleTensorBaseChangeCompMap_restrict B S hS f g f' g' u h u' w squ.w E K' φ
  have hBC := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS g' u h u' squ hu hrep
    (((smallEtaleDerivedTensor B S hS X').obj K').obj
      ((smallEtaleDerivedModulePullback B S hS f').obj (structureDerived Y')))
  have := isIso_uncurry_map_id_prod (smallEtaleDerivedTensor B S hS U')
    ((smallEtaleDerivedModulePullback B S hS u').obj K')
    ((smallEtaleDerivedModulePullbackCompIso B S hS u' f').hom.app (structureDerived Y'))
  have := isIso_uncurry_map_id_prod (smallEtaleDerivedTensor B S hS U)
    ((smallEtaleDerivedModulePullback B S hS u).obj E)
    ((smallEtaleDerivedModulePullbackCompIso B S hS u f).hom.app
      ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
        (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS g)).obj
        (structureDerived Y')))
  exact IsIso.of_isIso_fac_right e

end Restrict

section Local

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **The Künneth map of Stacks 0DKH is étale local on `X`**, for any covering family of étale
charts `V i` of `X` and any cartesian squares `X'_i ⟶ V i` over `X' ⟶ X`. -/
theorem isIso_smallEtaleTensorBaseChangeCompMap_of_coversTop (w : g' ≫ f = f' ≫ g)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj E ⟶ K')
    {ι : Type*} {V : ι → SmallEtale B S hS X.1}
    (hV : (SmallEtale.topology B S hS X.1).CoversTop V)
    (U' : ι → AlgebraicSpaces B S hS) (p : ∀ i, U' i ⟶ chartSpace B S hS X (V i))
    (q : ∀ i, U' i ⟶ X')
    (sq : ∀ i, IsPullback (q i) (p i) g' (chartToSpace B S hS X (V i)))
    (h : ∀ i, IsIso (smallEtaleTensorBaseChangeCompMap B S hS (chartToSpace B S hS X (V i) ≫ f) g
        (q i ≫ f') (p i) (comp_stack B S hS _ f _ f' _ g' g (sq i).w.symm w)
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (V i))).obj E)
        ((smallEtaleDerivedModulePullback B S hS (q i)).obj K')
        (((smallEtaleDerivedModulePullbackCompIso B S hS (p i) (chartToSpace B S hS X (V i))).hom ≫
            (smallEtaleDerivedModulePullbackSquareIso B S hS g' (chartToSpace B S hS X (V i))
              (p i) (q i) (sq i).w).inv).app E ≫
          (smallEtaleDerivedModulePullback B S hS (q i)).map φ))) :
    IsIso (smallEtaleTensorBaseChangeCompMap B S hS f g f' g' w E K' φ) := by
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS hV _ fun i => ?_
  exact isIso_map_smallEtaleTensorBaseChangeCompMap_of_isEtale B S hS f g f' g'
    (chartToSpace B S hS X (V i)) (p i) (q i) w (sq i)
    (isEtale_chartToSpace B S hS X (V i)) (relativelyRepresentable_chartToSpace B S hS X (V i))
    E K' φ (h i)

end Local

end AlgebraicGeometry.Space

end
