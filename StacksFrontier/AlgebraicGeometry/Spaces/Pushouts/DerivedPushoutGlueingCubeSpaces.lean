module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutGlueingCube
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionAgree

/-!
# The glueing map of Stacks 0DL7 commutes with étale restriction, for algebraic spaces

Let `i, f, f', j` be a commutative square of algebraic spaces and `iW, fW, f'W, jW` its base
change along a morphism `h : W ⟶ Y'`, with vertical edges `h, hY, hX, hX'`. This file proves the
cube condition `hc` of `MilnorPatching.map_glueingMap_comp_baseChange` for the compositors of
Stacks 0D6D (`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`) and their 03G2
transports, and reads the restriction lemma at arbitrary models of the eight derived categories.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullback_cube`: **the cube condition** — the 2-cells of
  the six faces of the cube of derived pullbacks paste to the same 2-cell. It is
  `Stacks.CategoryTheory.BaseChange.compositorCube_paste` applied to the pseudofunctoriality datum.
* `AlgebraicGeometry.Space.isIso_conjSquare_smallEtaleDerivedBaseChangeSquare_app`: the canonical
  form of Stacks 08GE read at arbitrary models.
* `AlgebraicGeometry.Space.pushoutGlueingMap_restrict`: **the glueing map commutes with
  restriction at arbitrary models**, the base change maps being those of Stacks 07A7 read at the
  models. Its statement is the conclusion of `MilnorPatching.map_glueingMap_comp_conjBaseChange`
  at the derived pullbacks of the cube.

## Implementation notes

Every statement about the derived categories of the small étale sites is obtained by
instantiating a lemma whose functors and categories are variables, never by restating a type and
comparing it with the type of a definition elaborated elsewhere. Two elaborations of the same
derived category, of the same base change map, are definitionally equal, but the kernel does not
decide that within its budget: comparing `Stacks.CategoryTheory.BaseChange.map` with the component
of `Stacks.CategoryTheory.BaseChange.twoSquare` makes it reduce the projection of the mate, and
comparing a synthesized instance with one unified from a definition's type makes it unfold the
derived categories. This is also why the category instances of the lemmas of
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/DerivedPushoutGlueingCube.lean` are implicit
arguments, unified from the functors, rather than instance arguments, and why the statement of
`AlgebraicGeometry.Space.pushoutGlueingMap_restrict` is `type_of%` the instantiated lemma.

The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is erased, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/DerivedPushoutEtaleBaseChange.lean`.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- The identification of a factorisation `f ≫ g = k` of the pseudofunctoriality datum is the
compositor of Stacks 0D6D followed by the renaming along `f ≫ g = k`. -/
theorem smallEtaleDerivedPullbackFactorIso_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    smallEtaleDerivedPullbackFactorIso B S hS f g k h =
      smallEtaleDerivedModulePullbackCompIso B S hS f g ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS h := by
  rw [smallEtaleDerivedModulePullbackCompIso_eq B S hS]
  rfl

/-- The renaming along a reflexivity is the identity. -/
theorem smallEtaleDerivedModulePullbackCongr_refl {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    smallEtaleDerivedModulePullbackCongr B S hS (rfl : f = f) = Iso.refl _ :=
  rfl

/-- The cocycle identity of the pseudofunctoriality datum, read on components. -/
theorem smallEtaleDerivedPullbackFactorIso_hom_assoc {V W Y Z : AlgebraicSpaces B S hS}
    (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z) (hb : t ≫ a = b)
    (hq : p ≫ t = q) (hc : q ≫ a = c) (hpb : p ≫ b = c)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedPullbackFactorIso B S hS p t q hq).hom.app
        ((smallEtaleDerivedModulePullback B S hS a).obj M) ≫
      (smallEtaleDerivedPullbackFactorIso B S hS q a c hc).hom.app M =
    (smallEtaleDerivedModulePullback B S hS p).map
        ((smallEtaleDerivedPullbackFactorIso B S hS t a b hb).hom.app M) ≫
      (smallEtaleDerivedPullbackFactorIso B S hS p b c hpb).hom.app M := by
  have h := congrArg Iso.hom
    (smallEtaleDerivedPullbackFactorIso_assoc B S hS p t a b q c hb hq hc hpb M)
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] using h

/-- The 2-cell of the base change map of a commutative square, through the pseudofunctoriality
datum. -/
theorem pullbackComparison_eq_factorIso {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) :
    Stacks.CategoryTheory.BaseChange.pullbackComparison
        (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
        (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w) =
      (smallEtaleDerivedPullbackFactorIso B S hS f' g (f' ≫ g) rfl).hom ≫
        (smallEtaleDerivedPullbackFactorIso B S hS g' f (f' ≫ g) w).inv := by
  rw [smallEtaleDerivedPullbackFactorIso_eq, smallEtaleDerivedPullbackFactorIso_eq,
    smallEtaleDerivedModulePullbackCongr_refl, Iso.trans_refl]
  rfl

/-- The 2-cell of `AlgebraicGeometry.Space.pushoutDerivedPullbackSquareIsoOfModels`, through the
pseudofunctoriality datum. -/
theorem squareIso_hom_eq_factorIso {X X' Y Y' : AlgebraicSpaces B S hS} (i : X ⟶ X')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y') (w : i ≫ f' = f ≫ j) :
    (smallEtaleDerivedModulePullbackCompIso B S hS f j ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS w.symm ≪≫
        (smallEtaleDerivedModulePullbackCompIso B S hS i f').symm).hom =
      (smallEtaleDerivedPullbackFactorIso B S hS f j (i ≫ f') w.symm).hom ≫
        (smallEtaleDerivedPullbackFactorIso B S hS i f' (i ≫ f') rfl).inv := by
  simp only [smallEtaleDerivedPullbackFactorIso_eq, smallEtaleDerivedModulePullbackCongr_refl,
    Iso.trans_refl, Iso.trans_hom, Iso.symm_hom, Category.assoc]

/-- **The cube condition for derived pullbacks along morphisms of algebraic spaces.** For a
commutative cube of algebraic spaces with bottom face `i ≫ f' = f ≫ j`, top face
`iW ≫ f'W = fW ≫ jW` and vertical edges `h, hY, hX, hX'`, the 2-cells of its six faces built from
the compositors of Stacks 0D6D (on the vertical faces, the 2-cells of the base change maps
`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`; on the bottom and top, the 2-cells
of `AlgebraicGeometry.Space.pushoutDerivedPullbackSquareIsoOfModels`) paste to the same 2-cell
`Lh ⋙ LjW ⋙ LfW ⟶ Lf' ⋙ Li ⋙ LhX`. -/
theorem smallEtaleDerivedPullback_cube {Y' Y X X' W YW XW X'W : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y') (iW : XW ⟶ X'W) (fW : XW ⟶ YW)
    (f'W : X'W ⟶ W) (jW : YW ⟶ W) (h : W ⟶ Y') (hY : YW ⟶ Y) (hX : XW ⟶ X) (hX' : X'W ⟶ X')
    (w : i ≫ f' = f ≫ j) (wW : iW ≫ f'W = fW ≫ jW) (hj : hY ≫ j = jW ≫ h)
    (hf : hX ≫ f = fW ≫ hY) (hf' : hX' ≫ f' = f'W ≫ h) (hi : hX ≫ i = iW ≫ hX')
    (N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y'))) :
    (smallEtaleDerivedModulePullback B S hS fW).map
        ((Stacks.CategoryTheory.BaseChange.pullbackComparison
          (smallEtaleDerivedModulePullbackCompIso B S hS jW h)
          (smallEtaleDerivedModulePullbackSquareIso B S hS j h jW hY hj)).app N) ≫
      (Stacks.CategoryTheory.BaseChange.pullbackComparison
          (smallEtaleDerivedModulePullbackCompIso B S hS fW hY)
          (smallEtaleDerivedModulePullbackSquareIso B S hS f hY fW hX hf)).app
        ((smallEtaleDerivedModulePullback B S hS j).obj N) ≫
      (smallEtaleDerivedModulePullback B S hS hX).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS f j ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS w.symm ≪≫
          (smallEtaleDerivedModulePullbackCompIso B S hS i f').symm).hom.app N) =
    (smallEtaleDerivedModulePullbackCompIso B S hS fW jW ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS wW.symm ≪≫
          (smallEtaleDerivedModulePullbackCompIso B S hS iW f'W).symm).hom.app
        ((smallEtaleDerivedModulePullback B S hS h).obj N) ≫
      (smallEtaleDerivedModulePullback B S hS iW).map
        ((Stacks.CategoryTheory.BaseChange.pullbackComparison
          (smallEtaleDerivedModulePullbackCompIso B S hS f'W h)
          (smallEtaleDerivedModulePullbackSquareIso B S hS f' h f'W hX' hf')).app N) ≫
      (Stacks.CategoryTheory.BaseChange.pullbackComparison
          (smallEtaleDerivedModulePullbackCompIso B S hS iW hX')
          (smallEtaleDerivedModulePullbackSquareIso B S hS i hX' iW hX hi)).app
        ((smallEtaleDerivedModulePullback B S hS f').obj N) := by
  have hK₁ : (iW ≫ hX') ≫ f' = (iW ≫ f'W) ≫ h := by
    rw [Category.assoc, hf', Category.assoc]
  have hK₂ : hX ≫ i ≫ f' = (iW ≫ f'W) ≫ h := by rw [← Category.assoc, hi, hK₁]
  have hK₃ : (fW ≫ hY) ≫ j = (iW ≫ f'W) ≫ h := by
    rw [Category.assoc, hj, ← Category.assoc, ← wW]
  have hK₄ : fW ≫ jW ≫ h = (iW ≫ f'W) ≫ h := by rw [← Category.assoc, ← wW]
  have hK₅ : iW ≫ f'W ≫ h = (iW ≫ f'W) ≫ h := (Category.assoc _ _ _).symm
  have key := Stacks.CategoryTheory.BaseChange.compositorCube_paste
    (smallEtaleDerivedPullbackFactorIso B S hS f j (i ≫ f') w.symm)
    (smallEtaleDerivedPullbackFactorIso B S hS i f' (i ≫ f') rfl)
    (smallEtaleDerivedPullbackFactorIso B S hS fW jW (iW ≫ f'W) wW.symm)
    (smallEtaleDerivedPullbackFactorIso B S hS iW f'W (iW ≫ f'W) rfl)
    (smallEtaleDerivedPullbackFactorIso B S hS jW h (jW ≫ h) rfl)
    (smallEtaleDerivedPullbackFactorIso B S hS hY j (jW ≫ h) hj)
    (smallEtaleDerivedPullbackFactorIso B S hS fW hY (fW ≫ hY) rfl)
    (smallEtaleDerivedPullbackFactorIso B S hS hX f (fW ≫ hY) hf)
    (smallEtaleDerivedPullbackFactorIso B S hS f'W h (f'W ≫ h) rfl)
    (smallEtaleDerivedPullbackFactorIso B S hS hX' f' (f'W ≫ h) hf')
    (smallEtaleDerivedPullbackFactorIso B S hS iW hX' (iW ≫ hX') rfl)
    (smallEtaleDerivedPullbackFactorIso B S hS hX i (iW ≫ hX') hi)
    (smallEtaleDerivedPullbackFactorIso B S hS hX (i ≫ f') _ hK₂)
    (smallEtaleDerivedPullbackFactorIso B S hS (iW ≫ hX') f' _ hK₁)
    (smallEtaleDerivedPullbackFactorIso B S hS (fW ≫ hY) j _ hK₃)
    (smallEtaleDerivedPullbackFactorIso B S hS fW (jW ≫ h) _ hK₄)
    (smallEtaleDerivedPullbackFactorIso B S hS (iW ≫ f'W) h _ rfl)
    (smallEtaleDerivedPullbackFactorIso B S hS iW (f'W ≫ h) _ hK₅) N
    (smallEtaleDerivedPullbackFactorIso_hom_assoc hX i f' _ _ _ rfl hi hK₁ hK₂ N)
    (smallEtaleDerivedPullbackFactorIso_hom_assoc hX f j _ _ _ w.symm hf hK₃ hK₂ N)
    (smallEtaleDerivedPullbackFactorIso_hom_assoc fW hY j _ _ _ hj rfl hK₃ hK₄ N)
    (smallEtaleDerivedPullbackFactorIso_hom_assoc fW jW h _ _ _ rfl wW.symm rfl hK₄ N)
    (smallEtaleDerivedPullbackFactorIso_hom_assoc iW hX' f' _ _ _ hf' rfl hK₁ hK₅ N)
    (smallEtaleDerivedPullbackFactorIso_hom_assoc iW f'W h _ _ _ rfl rfl rfl hK₅ N)
  simp only [pullbackComparison_eq_factorIso]
  rw [squareIso_hom_eq_factorIso i f f' j w, squareIso_hom_eq_factorIso iW fW f'W jW wW]
  exact key

end Standard

section Models

open Stacks.CategoryTheory.BaseChange MilnorPatching

universe w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈

attribute [local instance 10000] HasDerivedCategory.standard

/-- The comparison of a model of `D(𝒪_X)` with the standard one, as used by
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackOfModels`. -/
abbrev smallEtaleStdModelEquiv (X : AlgebraicSpaces B S hS)
    (m : HasDerivedCategory.{w₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  StacksDraft.DerivedModel.modelEquiv
    (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) m

/-- The derived pullback read at arbitrary models is additive. -/
instance additive_smallEtaleDerivedModulePullbackOfModels {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y)
    (hX : HasDerivedCategory.{w₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).Additive := by
  have := StacksDraft.DerivedModel.modelEquiv_functor_additive
    (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) hX
  have := StacksDraft.DerivedModel.modelEquiv_functor_additive
    (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) hY
  unfold smallEtaleDerivedModulePullbackOfModels
  infer_instance

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
  (mX : HasDerivedCategory.{w₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (mY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
  (mX' : HasDerivedCategory.{w₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
  (mY' : HasDerivedCategory.{w₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')))

/-- **The base change maps of Stacks 08GE, read at arbitrary models, are invertible**: for a
cartesian square with `g` étale, the base change map
`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`, invertible by
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedModuleBaseChangeMap`, read through the
comparisons of the models with the standard ones
(`Stacks.CategoryTheory.BaseChange.conjSquare`). -/
theorem isIso_conjSquare_smallEtaleDerivedBaseChangeSquare_app (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom) (K : @DerivedCategory _ _ _ mX) :
    @IsIso _ _ _ _ ((Stacks.CategoryTheory.BaseChange.conjSquare (smallEtaleStdModelEquiv X mX)
      (smallEtaleStdModelEquiv Y mY) (smallEtaleStdModelEquiv X' mX')
        (smallEtaleStdModelEquiv Y' mY')
      (Stacks.CategoryTheory.BaseChange.twoSquare (smallEtaleDerivedModuleAdjunction B S hS f)
        (smallEtaleDerivedModuleAdjunction B S hS f')
        (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
        (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w))).app K) :=
  Stacks.CategoryTheory.BaseChange.isIso_conjSquare_twoSquare_app _ _ _ _ _ _ _ _ K
    (isIso_smallEtaleDerivedModuleBaseChangeMap f g f' g' sq hg _)

end Square

variable {Y' Y X X' W YW XW X'W : AlgebraicSpaces B S hS}
  (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y') (iW : XW ⟶ X'W) (fW : XW ⟶ YW)
  (f'W : X'W ⟶ W) (jW : YW ⟶ W) (h : W ⟶ Y') (hY : YW ⟶ Y) (hX : XW ⟶ X) (hX' : X'W ⟶ X')
  (w : i ≫ f' = f ≫ j) (wW : iW ≫ f'W = fW ≫ jW) (hj : hY ≫ j = jW ≫ h)
  (hf : hX ≫ f = fW ≫ hY) (hf' : hX' ≫ f' = f'W ≫ h) (hi : hX ≫ i = iW ≫ hX')
  (mY' : HasDerivedCategory.{w₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')))
  (mY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
  (mX : HasDerivedCategory.{w₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (mX' : HasDerivedCategory.{w₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
  (mW : HasDerivedCategory.{w₅} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
  (mYW : HasDerivedCategory.{w₆} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS YW)))
  (mXW : HasDerivedCategory.{w₇} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS XW)))
  (mX'W : HasDerivedCategory.{w₈} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'W)))


include hf' in
/-- **The glueing map of Stacks 0DL7 commutes with étale restriction, at arbitrary models.** For a
commutative cube of algebraic spaces (the square `i, f, f', j` and its base change
`iW, fW, f'W, jW` along `h`), read at arbitrary models of the eight derived categories: the glueing
map of `(M, K', α)` (in the shape of `AlgebraicGeometry.Space.pushoutGlueingMapOfModels`),
restricted along `h` and followed by the base change maps of Stacks 07A7 read at the models
(`βj`, `βf`, and the 2-cell `θi` of the face of `i`), is on each summand the base change map
followed by the glueing map `gW` of the restricted triple. This is
`MilnorPatching.map_glueingMap_comp_conjBaseChange` with the cube condition
`AlgebraicGeometry.Space.smallEtaleDerivedPullback_cube`. -/
theorem pushoutGlueingMap_restrict
    (M : @DerivedCategory _ _ _ mY) (K' : @DerivedCategory _ _ _ mX')
    (α : ((smallEtaleStdModelEquiv Y mY).inverse ⋙ smallEtaleDerivedModulePullback B S hS f ⋙
        (smallEtaleStdModelEquiv X mX).functor).obj M ⟶
      ((smallEtaleStdModelEquiv X' mX').inverse ⋙ smallEtaleDerivedModulePullback B S hS i ⋙
        (smallEtaleStdModelEquiv X mX).functor).obj K') :
    letI := mY'
    letI := mW
    type_of% (MilnorPatching.map_glueingMap_comp_conjBaseChange
    (smallEtaleStdModelEquiv Y' mY') (smallEtaleStdModelEquiv Y mY)
      (smallEtaleStdModelEquiv X' mX') (smallEtaleStdModelEquiv X mX)
    (smallEtaleStdModelEquiv W mW) (smallEtaleStdModelEquiv YW mYW)
      (smallEtaleStdModelEquiv X'W mX'W) (smallEtaleStdModelEquiv XW mXW)
    (smallEtaleDerivedModuleAdjunction B S hS j) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS i)
    (smallEtaleDerivedModuleAdjunction B S hS jW) (smallEtaleDerivedModuleAdjunction B S hS f'W)
    (smallEtaleDerivedModuleAdjunction B S hS fW) (smallEtaleDerivedModuleAdjunction B S hS iW)
    (smallEtaleDerivedModulePullbackCompIso B S hS f j)
    (smallEtaleDerivedModulePullbackCongr B S hS w.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS i f')
    (smallEtaleDerivedModulePullbackCompIso B S hS fW jW)
    (smallEtaleDerivedModulePullbackCongr B S hS wW.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS iW f'W)
    (smallEtaleDerivedModulePullbackCompIso B S hS jW h)
    (smallEtaleDerivedModulePullbackSquareIso B S hS j h jW hY hj)
    (smallEtaleDerivedModulePullbackCompIso B S hS fW hY)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f hY fW hX hf)
    (smallEtaleDerivedModulePullbackCompIso B S hS f'W h)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f' h f'W hX' hf')
    (smallEtaleDerivedModulePullbackCompIso B S hS iW hX')
    (smallEtaleDerivedModulePullbackSquareIso B S hS i hX' iW hX hi)
    (fun N ↦ smallEtaleDerivedPullback_cube i f f' j iW fW f'W jW h hY hX hX' w wW hj hf hf' hi N)
    M K' α (hΦ := additive_smallEtaleDerivedModulePullbackOfModels h mW mY')) :=
  MilnorPatching.map_glueingMap_comp_conjBaseChange
    (smallEtaleStdModelEquiv Y' mY') (smallEtaleStdModelEquiv Y mY)
      (smallEtaleStdModelEquiv X' mX') (smallEtaleStdModelEquiv X mX)
    (smallEtaleStdModelEquiv W mW) (smallEtaleStdModelEquiv YW mYW)
      (smallEtaleStdModelEquiv X'W mX'W) (smallEtaleStdModelEquiv XW mXW)
    (smallEtaleDerivedModuleAdjunction B S hS j) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS i)
    (smallEtaleDerivedModuleAdjunction B S hS jW) (smallEtaleDerivedModuleAdjunction B S hS f'W)
    (smallEtaleDerivedModuleAdjunction B S hS fW) (smallEtaleDerivedModuleAdjunction B S hS iW)
    (smallEtaleDerivedModulePullbackCompIso B S hS f j)
    (smallEtaleDerivedModulePullbackCongr B S hS w.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS i f')
    (smallEtaleDerivedModulePullbackCompIso B S hS fW jW)
    (smallEtaleDerivedModulePullbackCongr B S hS wW.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS iW f'W)
    (smallEtaleDerivedModulePullbackCompIso B S hS jW h)
    (smallEtaleDerivedModulePullbackSquareIso B S hS j h jW hY hj)
    (smallEtaleDerivedModulePullbackCompIso B S hS fW hY)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f hY fW hX hf)
    (smallEtaleDerivedModulePullbackCompIso B S hS f'W h)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f' h f'W hX' hf')
    (smallEtaleDerivedModulePullbackCompIso B S hS iW hX')
    (smallEtaleDerivedModulePullbackSquareIso B S hS i hX' iW hX hi)
    (fun N ↦ smallEtaleDerivedPullback_cube i f f' j iW fW f'W jW h hY hX hX' w wW hj hf hf' hi N)
    M K' α (hΦ := additive_smallEtaleDerivedModulePullbackOfModels h mW mY')

end Models

end AlgebraicGeometry.Space

end
