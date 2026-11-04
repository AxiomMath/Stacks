module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom

/-!
# Unbounded base change for a 2-commutative square with exact horizontal pullbacks

Let
```
              g'
  (Sh(𝒞'), 𝒪_{𝒞'}) ⟶ (Sh(𝒞), 𝒪_𝒞)
        | f'                | f
        v                   v
  (Sh(𝒟'), 𝒪_{𝒟'}) ⟶ (Sh(𝒟), 𝒪_𝒟)
              g
```
be a square of morphisms of ringed topoi commuting up to a 2-isomorphism
`s : g ∘ f' ≅ f ∘ g'`. Its derived base change map `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` is the mate,
for the derived adjunctions of [Stacks, Tag 07A6], of the identification
`Σ : L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` of the two iterated derived pullbacks around the square.
Its underived counterpart is the base change map `g^* f_* ⟶ f'_* (g')^*` of sheaves of modules,
the mate of the identification `m : (f')^* g^* ≅ (g')^* f^*` of the pullbacks of modules.

This file proves that **the derived base change map is an isomorphism as soon as the module base
change map is, provided the two horizontal pullbacks `g^*` and `(g')^*` of sheaves of modules are
exact and `(g')^*` carries K-injective complexes to K-injective complexes.** This is the shape of
the argument for the compatibility of total direct image with restriction to a localization: one
computes `Rf_*` on a K-injective complex `I`, the exact pullbacks are computed termwise, `(g')^* I`
is again K-injective and so computes `Rf'_*`, and what is left is the module base change map
applied termwise to `I`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.moduleBaseChange`: the base change map
  `f_* ⋙ g^* ⟶ (g')^* ⋙ f'_*` of sheaves of modules.
* `AlgebraicGeometry.RingedToposHom.TwoIso.moduleBaseChangeComplex`: the same, applied termwise
  to a complex.

The derived base change map itself is `Stacks.CategoryTheory.BaseChange.map` for the derived
adjunctions and `Σ = AlgebraicGeometry.RingedToposHom.TwoIso.derivedPullbackSquareIso s`, which
is `Stacks.Cohomology.ProjectionFormulaOfToposHom.squareBaseChangeMap s`.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.derivedBaseChange_fac`: at the image of an arbitrary
  complex `I` of `𝒪_𝒞`-modules, the derived base change map, preceded by `Lg^*` of the unit
  `f_* I ⟶ Rf_* I` and followed by `Rf'_*` of the comparison `L(g')^* I ⟶ (g')^* I`, is the
  comparison `Lg^* f_* I ⟶ g^* f_* I`, followed by the module base change map applied termwise
  and the unit `f'_* (g')^* I ⟶ Rf'_* (g')^* I`.
* `AlgebraicGeometry.RingedToposHom.TwoIso.isIso_derivedBaseChange_of_isIso_moduleBaseChange`:
  the derived base change map is an isomorphism when the module base change map is, the two
  horizontal pullbacks are exact and `(g')^*` preserves K-injectivity.

## Implementation notes

The factorization is proved by comparing adjuncts under `L(f')^* ⊣ Rf'_*`. On each side the
adjunct is rewritten, through the counit factorization of [Stacks, Tag 0FPI]
(`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction_counit_fac`) for `f` and for
`f'`, the characterization of `Σ` by `m`
(`AlgebraicGeometry.RingedToposHom.TwoIso.derivedPullbackSquareIso_hom_app_comp`) and the
naturality of the comparisons `L(-)^* ⟶ (-)^*`, into the same composite; the module input is the
defining property of the module base change map as a mate,
`mateEquiv_counit`. None of this uses K-injectivity, which only enters the invertibility.

## References

* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} (s : TwoIso (g.comp f') (f.comp g'))

/-- **The base change map of a 2-commutative square on sheaves of modules**,
`f_* ⋙ g^* ⟶ (g')^* ⋙ f'_*`: the mate, for the adjunctions `f^* ⊣ f_*` and `(f')^* ⊣ f'_*` of
Stacks 03D7, of the identification `m : (f')^* g^* ≅ (g')^* f^*` of the pullbacks around the
square. -/
def moduleBaseChange :
    pushforwardModules f ⋙ g.toModulesHom.pullbackModules ⟶
      g'.toModulesHom.pullbackModules ⋙ pushforwardModules f' :=
  (mateEquiv (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules f')
    (squarePullbackIso s).hom).natTrans


omit [HasSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y.J (Type u)] in
/-- The defining property of the module base change map: `(f')^*` of it, followed by the counit of
`(f')^* ⊣ f'_*`, is `m` followed by `(g')^*` of the counit of `f^* ⊣ f_*`. -/
theorem pullback_moduleBaseChange_comp_counit (M) :
    f'.toModulesHom.pullbackModules.map ((moduleBaseChange s).app M) ≫
        (pullbackAdjPushforwardModules f').counit.app (g'.toModulesHom.pullbackModules.obj M) =
      (squarePullbackIso s).hom.app ((pushforwardModules f).obj M) ≫
        g'.toModulesHom.pullbackModules.map ((pullbackAdjPushforwardModules f).counit.app M) :=
  mateEquiv_counit _ _ _ M

attribute [local irreducible] moduleBaseChange

/-- The module base change map applied termwise to a complex `I` of `𝒪_𝒞`-modules. -/
def moduleBaseChangeComplex
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ⟶
      ((pushforwardModules f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) where
  f n := (moduleBaseChange s).app (I.X n)
  comm' i j _ := ((moduleBaseChange s).naturality (I.d i j)).symm

omit [HasSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y.J (Type u)] in
/-- The component in degree `n` of the termwise module base change map on a complex `I` is the
module base change map at `I.X n`. -/
@[simp]
theorem moduleBaseChangeComplex_f
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) : (moduleBaseChangeComplex s I).f n = (moduleBaseChange s).app (I.X n) := rfl

omit [HasSheafify X'.J (Type u)] in
/-- The counit of the adjunction `f^* ⊣ f_*` on unbounded homotopy categories, at the class of a
complex, is the class of the termwise counit. -/
theorem
  _root_.Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy_counit_app_quotient
    {Z W : RingedTopos.{u, u, u}}
    [Z.J.HasSheafCompose (forget RingCat.{u})] [W.J.HasSheafCompose (forget RingCat.{u})]
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [W.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [W.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (φ : RingedToposHom Z W)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (pullbackAdjPushforwardMapHomotopy φ).counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (pullbackAdjPushforwardModules φ).counit
          (ComplexShape.up ℤ)).app I) := by
  unfold pullbackAdjPushforwardMapHomotopy
  rfl

omit [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y.J (Type u)] in
/-- The defining property of the module base change map, termwise on a complex. -/
theorem moduleBaseChangeComplex_comp_counit
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (f'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (moduleBaseChangeComplex s I) ≫
      (NatTrans.mapHomologicalComplex (pullbackAdjPushforwardModules f').counit
        (ComplexShape.up ℤ)).app
          ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) =
      (squarePullbackComplexIso s
          (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).hom ≫
        (g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (pullbackAdjPushforwardModules f).counit
            (ComplexShape.up ℤ)).app I) := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, squarePullbackComplexIso_hom_f,
    moduleBaseChangeComplex_f]
  exact pullback_moduleBaseChange_comp_counit s (I.X n)

/-- The defining property of the module base change map, on the class of a complex in the
homotopy category. -/
theorem pullbackMapHomotopy_moduleBaseChangeComplex_comp_counit
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (pullbackMapHomotopy f').map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (moduleBaseChangeComplex s I)) ≫
      (pullbackAdjPushforwardMapHomotopy f').counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) =
    (squarePullbackHomotopyIso s).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
      (pullbackMapHomotopy g').map ((pullbackAdjPushforwardMapHomotopy f).counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  have h2 := congrArg (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    (moduleBaseChangeComplex_comp_counit s I)
  rw [Functor.map_comp, Functor.map_comp,
    ← pullbackAdjPushforwardMapHomotopy_counit_app_quotient f'] at h2
  rw [pullbackAdjPushforwardMapHomotopy_counit_app_quotient f, squarePullbackHomotopyIso_hom_app]
  exact h2

/-- The adjunct under `L(f')^* ⊣ Rf'_*` of the left-hand side of `derivedBaseChange_fac`. -/
theorem derivedBaseChange_adjunct_left
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedPullback f').map
        ((derivedPullback g).map
            (((pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh
              (sourceQuasiIso X)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
          Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
            (derivedPullbackSquareIso s) (Iso.refl _)
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
          (derivedPushforward f').map ((derivedPullbackComparison g').app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      (derivedAdjunction f').counit.app
        (DerivedCategory.Qh.obj ((pullbackMapHomotopy g').obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) =
    (derivedPullback f').map
        ((derivedPullbackComparison g).app ((pushforwardMapHomotopy f).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      (derivedPullbackComparison f').app
        ((pullbackMapHomotopy g).obj ((pushforwardMapHomotopy f).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      DerivedCategory.Qh.map ((squarePullbackHomotopyIso s).hom.app
        ((pushforwardMapHomotopy f).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      DerivedCategory.Qh.map ((pullbackMapHomotopy g').map
        ((pullbackAdjPushforwardMapHomotopy f).counit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have hBC := Stacks.CategoryTheory.BaseChange.homEquiv_symm_map (derivedAdjunction f)
    (derivedAdjunction f') (derivedPullbackSquareIso s) (Iso.refl _)
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
  rw [Adjunction.homEquiv_counit] at hBC
  have hS := (derivedPullbackSquareIso s).hom.naturality
    (((pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh (sourceQuasiIso X)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
  have hFPI := derivedAdjunction_counit_fac f
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  have hc := (derivedPullbackComparison g').naturality
    ((pullbackAdjPushforwardMapHomotopy f).counit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
  have hsq := derivedPullbackSquareIso_hom_app_comp s
    ((pushforwardMapHomotopy f).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
  have hε : (derivedPullback f').map ((derivedPushforward f').map
        ((derivedPullbackComparison g').app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      (derivedAdjunction f').counit.app
        (DerivedCategory.Qh.obj ((pullbackMapHomotopy g').obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) =
      (derivedAdjunction f').counit.app ((derivedPullback g').obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
        (derivedPullbackComparison g').app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) :=
    (derivedAdjunction f').counit_naturality ((derivedPullbackComparison g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
  simp only [Functor.comp_map, Functor.comp_obj] at hS
  simp only [Functor.comp_map, Functor.id_obj] at hc
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp] at hBC
  simp only [Functor.map_comp, Category.assoc]
  rw [hε, reassoc_of% hBC, reassoc_of% hS, ← Functor.map_comp_assoc, hFPI, Functor.map_comp,
    Category.assoc, hc]
  simp only [Functor.comp_obj]
  rw [reassoc_of% hsq]

omit [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The diagram chase behind `derivedBaseChange_adjunct_right`, over variables. -/
private theorem chase_three_aux {𝒞 𝒟 ℋ : Type*} [Category 𝒞] [Category 𝒟]
    [Category ℋ] (L : 𝒞 ⥤ 𝒟) (Q : ℋ ⥤ 𝒟) {a0 a1 a2 a3 : 𝒞} {h1 h2 h4 h5 : ℋ}
    (x : a0 ⟶ a1) (y : a1 ⟶ a2) (z : a2 ⟶ a3) (ε : L.obj a3 ⟶ Q.obj h5)
    (c : L.obj a1 ⟶ Q.obj h1) (c' : L.obj a2 ⟶ Q.obj h2) (w : h1 ⟶ h2)
    (e' : h2 ⟶ h5) (q1 : h1 ⟶ h4) (q2 : h4 ⟶ h5)
    (hFPI : L.map z ≫ ε = c' ≫ Q.map e')
    (hc : L.map y ≫ c' = c ≫ Q.map w)
    (hm : Q.map (w ≫ e') = Q.map (q1 ≫ q2)) :
    L.map (x ≫ y ≫ z) ≫ ε = L.map x ≫ c ≫ Q.map q1 ≫ Q.map q2 := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hFPI,
    reassoc_of% hc, ← Q.map_comp, hm, Q.map_comp]

/-- The adjunct under `L(f')^* ⊣ Rf'_*` of the right-hand side of `derivedBaseChange_fac`. -/
theorem derivedBaseChange_adjunct_right
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedPullback f').map
        ((derivedPullbackComparison g).app ((pushforwardMapHomotopy f).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (moduleBaseChangeComplex s I)) ≫
          ((pushforwardOnHomotopy f').totalRightDerivedUnit DerivedCategory.Qh
            (sourceQuasiIso X')).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                ((g'.toModulesHom.pullbackModules.mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj I))) ≫
      (derivedAdjunction f').counit.app
        (DerivedCategory.Qh.obj ((pullbackMapHomotopy g').obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) =
    (derivedPullback f').map
        ((derivedPullbackComparison g).app ((pushforwardMapHomotopy f).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      (derivedPullbackComparison f').app
        ((pullbackMapHomotopy g).obj ((pushforwardMapHomotopy f).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      DerivedCategory.Qh.map ((squarePullbackHomotopyIso s).hom.app
        ((pushforwardMapHomotopy f).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ≫
      DerivedCategory.Qh.map ((pullbackMapHomotopy g').map
        ((pullbackAdjPushforwardMapHomotopy f).counit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have hFPI := derivedAdjunction_counit_fac f'
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  have hc := (derivedPullbackComparison f').naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (moduleBaseChangeComplex s I))
  have hm := congrArg DerivedCategory.Qh.map
    (pullbackMapHomotopy_moduleBaseChangeComplex_comp_counit s I)
  simp only [Functor.comp_map] at hc
  exact chase_three_aux (derivedPullback f') DerivedCategory.Qh _ _ _ _ _ _ _ _ _ _ hFPI hc hm

/-- **The derived base change map computed by the module base change map.** At the image of a
complex `I` of `𝒪_𝒞`-modules, the derived base change map, preceded by `Lg^*` of the unit
`f_* I ⟶ Rf_* I` and followed by `Rf'_*` of the comparison `L(g')^* I ⟶ (g')^* I`, is the
comparison `Lg^* f_* I ⟶ g^* f_* I`, followed by the module base change map applied termwise
and by the unit `f'_* (g')^* I ⟶ Rf'_* (g')^* I`. -/
theorem derivedBaseChange_fac
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedPullback g).map (((pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh
        (sourceQuasiIso X)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackSquareIso s) (Iso.refl _)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (derivedPushforward f').map ((derivedPullbackComparison g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) =
    (derivedPullbackComparison g).app ((pushforwardMapHomotopy f).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (moduleBaseChangeComplex s I)) ≫
      ((pushforwardOnHomotopy f').totalRightDerivedUnit DerivedCategory.Qh
        (sourceQuasiIso X')).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((g'.toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) := by
  apply ((derivedAdjunction f').homEquiv _ _).symm.injective
  exact ((Adjunction.homEquiv_counit _ _ _ _).trans (derivedBaseChange_adjunct_left s I)).trans
    ((Adjunction.homEquiv_counit _ _ _ _).trans (derivedBaseChange_adjunct_right s I)).symm

/-- **Unbounded base change for a 2-commutative square with exact horizontal pullbacks.** If the
pullbacks of sheaves of modules along `g` and `g'` are exact, `(g')^*` carries K-injective
complexes to K-injective complexes and the module base change map `g^* f_* ⟶ f'_* (g')^*` is an
isomorphism, then the derived base change map `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` is an isomorphism
for every `K`.

Every `K` is the image of a K-injective complex `I`; there the unit `f_* I ⟶ Rf_* I` and the
unit at `(g')^* I` are invertible, and the comparisons `L(-)^* ⟶ (-)^*` along the exact `g` and
`g'` are invertible everywhere, so `derivedBaseChange_fac` exhibits the derived base change map
as a composite of isomorphisms. -/
theorem isIso_derivedBaseChange_of_isIso_moduleBaseChange
    [PreservesFiniteLimits g.toModulesHom.pullbackModules]
    [PreservesFiniteLimits g'.toModulesHom.pullbackModules]
    (hK : ∀ I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective
        ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (hb : ∀ M, IsIso ((moduleBaseChange s).app M))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
      (derivedPullbackSquareIso s) (Iso.refl _) K) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    DerivedCategory.Qh K
  have hI' : IsIso (Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f)
        (derivedAdjunction f') (derivedPullbackSquareIso s) (Iso.refl _)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
    have h1 : IsIso (((pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh
        (sourceQuasiIso X)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
      Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ _ _ _ I hI
    have h2 : IsIso ((derivedPullbackComparison g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
      isIso_derivedPullbackComparison_app g' ⊤ hasResolutions_top
        (pullbackInvertsQuasiIso_top g') _ trivial
    have h3 : IsIso ((derivedPullbackComparison g).app ((pushforwardMapHomotopy f).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
      isIso_derivedPullbackComparison_app g ⊤ hasResolutions_top
        (pullbackInvertsQuasiIso_top g) _ trivial
    have h4 : IsIso (moduleBaseChangeComplex s I) := by
      have : ∀ n, IsIso ((moduleBaseChangeComplex s I).f n) := fun n => by
        rw [moduleBaseChangeComplex_f]; exact hb _
      exact HomologicalComplex.Hom.isIso_of_components _
    have h5 : IsIso (((pushforwardOnHomotopy f').totalRightDerivedUnit DerivedCategory.Qh
        (sourceQuasiIso X')).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((g'.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
      Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ _ _ _ _ (hK I hI)
    have h4' : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (moduleBaseChangeComplex s I))) :=
      Functor.map_isIso _ _
    rw [← isIso_comp_left_iff ((derivedPullback g).map
        (((pushforwardOnHomotopy f).totalRightDerivedUnit DerivedCategory.Qh
          (sourceQuasiIso X)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))),
      ← isIso_comp_right_iff _ ((derivedPushforward f').map ((derivedPullbackComparison g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))), Category.assoc,
      derivedBaseChange_fac s I]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h3 (@IsIso.comp_isIso _ _ _ _ _ _ _ h4' h5)
  have hnat := Stacks.CategoryTheory.BaseChange.map_naturality (derivedAdjunction f)
    (derivedAdjunction f') (derivedPullbackSquareIso s) (Iso.refl _) e.hom
  have : Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
      (derivedPullbackSquareIso s) (Iso.refl _) K =
      (derivedPullback g).map ((derivedPushforward f).map e.inv) ≫
      Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackSquareIso s) (Iso.refl _)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
        (derivedPushforward f').map ((derivedPullback g').map e.hom) := by
    rw [← cancel_epi ((derivedPullback g).map ((derivedPushforward f).map e.hom)),
      ← Functor.map_comp_assoc, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact hnat
  rw [this]
  infer_instance

end AlgebraicGeometry.RingedToposHom.TwoIso

end
