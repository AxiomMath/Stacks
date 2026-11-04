module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.KInjectiveSectionsNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexGlobalNaturality
import StacksCore.Tactic.StacksAttribute

/-! # Naturality of Stacks 08JA and of the tensor-internal-Hom bijection in the source variable

Let `(C, O)` be a ringed site. **Stacks 08JA** identifies the degree-zero global
hypercohomology of the derived internal Hom `RSheafHom(L, M)` with `Hom_{D(O)}(L, M)`, for
arbitrary objects `L`, `M` of `D(O)`; the identification is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`. **Stacks 08J8** is the
resulting bijection `(K ⟶ RSheafHom(L, M)) ≃ (K ⊗^L_O L ⟶ M)`,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`. This file proves that both are **natural
in the source variable**, for an arbitrary morphism of `D(O)`.

The route is the one the source takes. Stacks 08JA is proved at a chosen K-flat representative
of the source and K-injective representative of the target, where it is the composite of three
comparisons: the K-injective model of the derived internal Hom (Stacks 0A97), the fact that
global sections compute derived global sections on a K-injective complex (Stacks 07A5), and the
global computation of derived-category morphisms (Stacks 0A94). Each of the three is natural for
morphisms *of complexes* — the last two by
`AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality` and
`Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso_naturality` — so the composite is.
Naturality for an arbitrary morphism of `D(O)` between classes of K-flat complexes then follows
by the calculus of fractions: the morphism factors through a third complex, which is repaired
into a K-flat one by a K-flat resolution (Stacks 06YS), both legs of the resulting fraction are
classes of morphisms of complexes, and the denominator is invertible. Finally the identification
at arbitrary objects is the identification at the chosen representatives conjugated by the
comparisons, so its naturality is the model-level naturality transported.

Stacks 08J8 is Stacks 08JA applied to both sides of the derived currying isomorphism of
Stacks 08J9, so its source-variable naturality is the source-variable clause of
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural` together with the above.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedHomGlobalMap`: the map induced on degree-zero global
  hypercohomology of the derived internal Hom by a pair of morphisms of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedHomGlobalSectionsComparison`: the identification of that
  hypercohomology with the degree-zero cohomology of the global sections of the internal Hom
  complex, when the latter is K-injective — the first two of the three comparisons above.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_naturality`: Stacks
  08JA at a K-flat source and a K-injective target is natural for morphisms of complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived`:
  the same for an arbitrary morphism of `D(O)` in the source variable.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source`:
  **Stacks 08JA globally is natural in the source variable**, at arbitrary objects of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`: **Stacks 08J8 is
  natural in its source variable.** This is the naturality clause needed in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualIsTheDerivedDual`.

## What this file does not contain

Only the **source** variable is treated. The naturality of Stacks 08JA in its *target* variable,
and the corresponding clauses of Stacks 08J8 in the middle and the target, are not proved here.

The target variable is the covariant one, and the fractions argument used here does not
transfer to it: it reduces the source variable to morphisms of complexes because a morphism of
`D(O)` between classes of complexes factors as a fraction whose apex can be repaired to be
K-flat by Stacks 06YS, whereas in the target variable the apex would have to be repaired to be
K-injective and the leg orientations are the other way round. No fractions argument is needed
there, however: the target representative is already K-injective, so the morphism is the class
of a morphism of complexes outright, by
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective`. The target clauses are proved
on that shorter route in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality`, which
also bundles Stacks 08J8 as an adjunction. Only the **middle** clause of Stacks 08J8 remains
open, and nothing here carries the tag 08J9.

The naturality is stated as an identity of *maps of morphism groups*, as in Stacks 0A94, and not
as a square of natural transformations of functors on `D(O)ᵒᵖ`: a consumer identifying two such
bijections needs the former, and the latter would require the Hom bifunctor of `D(O)` to be
packaged as a functor into `AddCommGrpCat`.

## Implementation notes

The universes are the diagonal `RingedSite.{u, u, u}` of the whole derived-internal-Hom cluster.

Several of the steps are stated and proved at the level of *elements* rather than as equalities
of morphisms of `AddCommGrpCat`. The reason is that the two spellings of the homology of a
complex — `HomologicalComplex.homology` and the value of
`HomologicalComplex.homologyFunctor` — and the two spellings of the lifted Hom complex are only
definitionally equal, so a composite of the comparisons is not type-correct at `implicit`
transparency and `rw` cannot build a motive for it. The squares are therefore established as
morphism identities in the uniform spelling and then applied to an element with
`CategoryTheory.ConcreteCategory.congr_hom`.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The map induced on degree-zero global hypercohomology of the derived internal Hom by a
morphism of `D(O)`. -/
abbrev derivedHomGlobalMap
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : L' ⟶ L) (v : M ⟶ M') :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op L')).obj M')) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
    ((derivedModuleGlobalSections X).map
      (((derivedSheafHomBifunctor X).map u.op).app M ≫
        ((derivedSheafHomBifunctor X).obj (op L')).map v))

/-- The identification of the degree-zero global hypercohomology of `RSheafHom(QA, QI)` with
the degree-zero cohomology of the global sections of the internal Hom complex, when that
complex is K-injective. -/
def derivedHomGlobalSectionsComparison
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
            (DerivedCategory.Q.obj I))) ≅
      (globalSectionsComplex X (sheafHomComplex X A I).obj).homology 0 :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((derivedModuleGlobalSections X).mapIso (derivedSheafHomComparison X A I) ≪≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).symm) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
      (globalSectionsComplex X (sheafHomComplex X A I).obj)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- `derivedHomGlobalSectionsComparison`, spelled out. -/
theorem derivedHomGlobalSectionsComparison_hom
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] :
    (derivedHomGlobalSectionsComparison X A I).hom =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
            (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ≫
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
          (globalSectionsComplex X (sheafHomComplex X A I).obj) := rfl

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The identification of Stacks 08JA at a K-injective internal Hom complex is
`derivedHomGlobalSectionsComparison` followed by the global half of Stacks 0A94. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_eq_comparison
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I x =
      sheafHomGlobalHomologyEquivDerivedCategoryHom X A I
        ((derivedHomGlobalSectionsComparison X A I).hom x) := rfl

/-- An equality `f ≫ g = h ≫ k` in the source of `F` gives the same equality on elements. -/
private theorem functor_map_apply_eq_of_comp_eq {C : Type*} [Category C]
    (F : C ⥤ AddCommGrpCat.{u}) {Y Z W V : C} {f : Y ⟶ Z} {g : Z ⟶ V} {h : Y ⟶ W} {k : W ⟶ V}
    (e : f ≫ g = h ≫ k) (x : (F.obj Y : Type u)) :
    F.map g (F.map f x) = F.map k (F.map h x) :=
  ConcreteCategory.congr_hom
    (show F.map f ≫ F.map g = F.map h ≫ F.map k by
      rw [← Functor.map_comp, ← Functor.map_comp, e]) x

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- `derivedHomGlobalSectionsComparison` is natural for morphisms of complexes. -/
theorem derivedHomGlobalSectionsComparison_naturality
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective]
    (k : A' ⟶ A) (m : I ⟶ I')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    (derivedHomGlobalSectionsComparison X A' I').hom
        (derivedHomGlobalMap X (DerivedCategory.Q.map k) (DerivedCategory.Q.map m) x) =
      HomologicalComplex.homologyMap (globalSectionsComplexMap X (homMap X k m)) 0
        ((derivedHomGlobalSectionsComparison X A I).hom x) := by
  have hcomp : (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
            (DerivedCategory.Q.obj I) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
            (DerivedCategory.Q.map m)) ≫ (derivedSheafHomComparison X A' I').hom =
      (derivedSheafHomComparison X A I).hom ≫ DerivedCategory.Q.map (homMap X k m) := by
    rw [Category.assoc]
    exact derivedSheafHomComparison_naturality X k m
  have hgs : (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv ≫
        DerivedCategory.Q.map (globalSectionsComplexMap X (homMap X k m)) =
      (derivedModuleGlobalSections X).map (DerivedCategory.Q.map (homMap X k m)) ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I').obj)).inv := by
    have h : DerivedCategory.Q.map (globalSectionsComplexMap X (homMap X k m)) ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I').obj)).hom =
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).hom ≫
          (derivedModuleGlobalSections X).map (DerivedCategory.Q.map (homMap X k m)) :=
      globalSectionsKInjectiveIso_naturality X (homMap X k m)
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hD : (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
              (DerivedCategory.Q.obj I) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
              (DerivedCategory.Q.map m)) ≫
        ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A' I').hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I').obj)).inv) =
      ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ≫
        DerivedCategory.Q.map (globalSectionsComplexMap X (homMap X k m)) := by
    rw [Category.assoc, hgs, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hcomp,
      CategoryTheory.Functor.map_comp, Category.assoc]
  have e1 := functor_map_apply_eq_of_comp_eq (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0)
    hD x
  have e2 := ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
      (globalSectionsComplexMap X (homMap X k m)))
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) x)
  rw [derivedHomGlobalSectionsComparison_hom, derivedHomGlobalSectionsComparison_hom]
  exact (congrArg (fun z => (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
    (globalSectionsComplex X (sheafHomComplex X A' I').obj) z) e1).trans e2

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **Stacks 08JA globally, on a K-injective internal Hom complex, is natural for morphisms of
complexes**: the map induced by `k : A' ⟶ A` and `m : I ⟶ I'` on degree-zero global
hypercohomology of the derived internal Hom is pre- and postcomposition with the classes of `k`
and `m`. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality_globalMap
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective]
    (k : A' ⟶ A) (m : I ⟶ I')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A' I'
        (derivedHomGlobalMap X (DerivedCategory.Q.map k) (DerivedCategory.Q.map m) x) =
      DerivedCategory.Q.map k ≫
        derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I x ≫ DerivedCategory.Q.map m := by
  rw [derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_eq_comparison,
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_eq_comparison]
  rw [derivedHomGlobalSectionsComparison_naturality X k m x,
    sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality]


omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- `derivedHomGlobalMap` composes: it is contravariantly functorial in the source variable
and covariantly in the target variable, compatibly. -/
theorem derivedHomGlobalMap_comp
    {L L' L'' M M' M'' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : L' ⟶ L) (u' : L'' ⟶ L') (v : M ⟶ M') (v' : M' ⟶ M'') :
    derivedHomGlobalMap X u v ≫ derivedHomGlobalMap X u' v' =
      derivedHomGlobalMap X (u' ≫ u) (v ≫ v') := by
  dsimp only [derivedHomGlobalMap]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 2
  rw [op_comp, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    NatTrans.comp_app]
  simp only [Category.assoc, NatTrans.naturality_assoc]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- `derivedHomGlobalMap` is contravariantly functorial in the source variable. -/
theorem derivedHomGlobalMap_comp_fst
    {L L' L'' M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : L' ⟶ L) (u' : L'' ⟶ L') :
    derivedHomGlobalMap X (u' ≫ u) (𝟙 M) =
      derivedHomGlobalMap X u (𝟙 M) ≫ derivedHomGlobalMap X u' (𝟙 M) := by
  rw [derivedHomGlobalMap_comp, Category.comp_id]

/-- **Stacks 08JA globally, at a K-flat source and a K-injective target, is natural for
morphisms of complexes.** -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_naturality
    {A A' I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    [I.IsKInjective] [I'.IsKInjective] (k : A' ⟶ A) (m : I ⟶ I')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A' I' hA'
        (derivedHomGlobalMap X (DerivedCategory.Q.map k) (DerivedCategory.Q.map m) x) =
      DerivedCategory.Q.map k ≫
        derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x ≫ DerivedCategory.Q.map m := by
  have := isKInjective_sheafHomComplex_of_isKFlat X A I hA
  have := isKInjective_sheafHomComplex_of_isKFlat X A' I' hA'
  exact derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality_globalMap X k m x

/-- The source-variable half of
`derivedSheafHomGlobalSectionsEquivOfKFlat_naturality`. -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_fst
    {A A' I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    [I.IsKInjective] (k : A' ⟶ A)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A' I hA'
        (derivedHomGlobalMap X (DerivedCategory.Q.map k) (𝟙 (DerivedCategory.Q.obj I)) x) =
      DerivedCategory.Q.map k ≫ derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x := by
  have h := derivedSheafHomGlobalSectionsEquivOfKFlat_naturality X hA hA' k (𝟙 I) x
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- **The identification of Stacks 08JA at a K-flat source and a K-injective target is natural
in the source for an arbitrary morphism of `D(O)`**, not only for a morphism of complexes.
Factoring the morphism as a fraction through a third complex and repairing that complex by a
K-flat resolution (Stacks 06YS) reduces this to the two legs of the fraction, where naturality
is `derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_fst`; the denominator becomes
invertible in `D(O)` and is cancelled. -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived
    {A A' I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hA' : Stacks.SheafOfModules.IsKFlat X.O A')
    [I.IsKInjective] (g : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj A)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A' I hA'
        (derivedHomGlobalMap X g (𝟙 (DerivedCategory.Q.obj I)) x) =
      g ≫ derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x := by
  obtain ⟨B, s, hs, f, hg⟩ := DerivedCategory.right_fac g
  obtain ⟨BF, q, hBF, hq⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X B
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have : IsIso (DerivedCategory.Q.map (q ≫ s)) := by
    rw [CategoryTheory.Functor.map_comp]; infer_instance
  have hfac : DerivedCategory.Q.map (q ≫ s) ≫ g = DerivedCategory.Q.map (q ≫ f) := by
    rw [hg, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      IsIso.hom_inv_id_assoc]
  have hsplit : derivedHomGlobalMap X (DerivedCategory.Q.map (q ≫ f))
        (𝟙 (DerivedCategory.Q.obj I)) =
      derivedHomGlobalMap X g (𝟙 (DerivedCategory.Q.obj I)) ≫
        derivedHomGlobalMap X (DerivedCategory.Q.map (q ≫ s))
          (𝟙 (DerivedCategory.Q.obj I)) := by
    rw [← hfac, derivedHomGlobalMap_comp_fst]
  have hx : derivedHomGlobalMap X (DerivedCategory.Q.map (q ≫ f))
        (𝟙 (DerivedCategory.Q.obj I)) x =
      derivedHomGlobalMap X (DerivedCategory.Q.map (q ≫ s)) (𝟙 (DerivedCategory.Q.obj I))
        (derivedHomGlobalMap X g (𝟙 (DerivedCategory.Q.obj I)) x) :=
    ConcreteCategory.congr_hom hsplit x
  have h1 : derivedSheafHomGlobalSectionsEquivOfKFlat X BF I hBF
        (derivedHomGlobalMap X (DerivedCategory.Q.map (q ≫ f))
          (𝟙 (DerivedCategory.Q.obj I)) x) =
      DerivedCategory.Q.map (q ≫ f) ≫ derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x :=
    derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_fst X hA hBF (q ≫ f) x
  have h2 : derivedSheafHomGlobalSectionsEquivOfKFlat X BF I hBF
        (derivedHomGlobalMap X (DerivedCategory.Q.map (q ≫ s))
          (𝟙 (DerivedCategory.Q.obj I))
          (derivedHomGlobalMap X g (𝟙 (DerivedCategory.Q.obj I)) x)) =
      DerivedCategory.Q.map (q ≫ s) ≫ derivedSheafHomGlobalSectionsEquivOfKFlat X A' I hA'
        (derivedHomGlobalMap X g (𝟙 (DerivedCategory.Q.obj I)) x) :=
    derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_fst X hA' hBF (q ≫ s) _
  rw [← cancel_epi (DerivedCategory.Q.map (q ≫ s)), ← h2, ← hx, h1, ← Category.assoc, hfac]


/-- Stacks 08JA globally is the identification at the chosen representatives, transported along
the comparisons that identify the chosen complexes with the given objects. -/
theorem derivedSheafHomGlobalSectionsEquiv_eq_globalMap
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L M x =
      ((kFlatModelIso X L).inv ≫
        derivedSheafHomGlobalSectionsEquivOfKFlat X (kFlatModel X L) (kInjectiveModel X M)
            (isKFlat_kFlatModel X L)
            (derivedHomGlobalMap X (kFlatModelIso X L).hom (kInjectiveModelIso X M).inv x)) ≫
          (kInjectiveModelIso X M).hom := rfl

/-- **Stacks 08JA globally is natural in the source variable, for an arbitrary morphism of
`D(O)`**: the identification of the degree-zero global hypercohomology of `RSheafHom(L, M)`
with `Hom_{D(O)}(L, M)` carries the map induced by `u : L' ⟶ L` to precomposition with `u`.

This is the global half of the naturality of Stacks 0A94 read at arbitrary objects of `D(O)`:
the two sides are compared at the chosen K-flat representative of the source and the chosen
K-injective representative of the target, where it is
`derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived`. -/
@[stacks 08JA "global sections, naturality in the source variable"]
theorem derivedSheafHomGlobalSectionsEquiv_naturality_source
    {A A' W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : A' ⟶ A)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op A)).obj W)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X A' W (derivedHomGlobalMap X u (𝟙 W) x) =
      u ≫ derivedSheafHomGlobalSectionsEquiv X A W x := by
  have ht : derivedHomGlobalMap X (kFlatModelIso X A').hom (kInjectiveModelIso X W).inv
        (derivedHomGlobalMap X u (𝟙 W) x) =
      derivedHomGlobalMap X ((kFlatModelIso X A').hom ≫ u ≫ (kFlatModelIso X A).inv)
        (𝟙 (DerivedCategory.Q.obj (kInjectiveModel X W)))
        (derivedHomGlobalMap X (kFlatModelIso X A).hom (kInjectiveModelIso X W).inv x) := by
    have h1 := derivedHomGlobalMap_comp X u (kFlatModelIso X A').hom (𝟙 W)
      (kInjectiveModelIso X W).inv
    have h2 := derivedHomGlobalMap_comp X (kFlatModelIso X A).hom
      ((kFlatModelIso X A').hom ≫ u ≫ (kFlatModelIso X A).inv)
      (kInjectiveModelIso X W).inv (𝟙 (DerivedCategory.Q.obj (kInjectiveModel X W)))
    rw [Category.id_comp] at h1
    simp only [Category.assoc, Category.comp_id, Iso.inv_hom_id] at h2
    exact (ConcreteCategory.congr_hom h1 x).trans (ConcreteCategory.congr_hom h2 x).symm
  rw [derivedSheafHomGlobalSectionsEquiv_eq_globalMap,
    derivedSheafHomGlobalSectionsEquiv_eq_globalMap, ht,
    derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_derived X
      (isKFlat_kFlatModel X A) (isKFlat_kFlatModel X A')]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]


omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- With an identity in the target variable, `derivedHomGlobalMap` is the map induced by the
derived internal Hom in the source variable alone. -/
theorem derivedHomGlobalMap_fst_eq
    {L L' M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : L' ⟶ L) :
    derivedHomGlobalMap X u (𝟙 M) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map (((derivedSheafHomBifunctor X).map u.op).app M)) := by
  dsimp only [derivedHomGlobalMap]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Naturality of the derived currying isomorphism in the source variable alone**: the
three-variable square of Stacks 08J9 with identities in the middle and the target. -/
theorem derivedCurryIso_natural_fst
    {A A' B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : A' ⟶ A) :
    ((derivedSheafHomBifunctor X).map u.op).app
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z) ≫
        (derivedCurryIso X A' B Z).hom =
      (derivedCurryIso X A B Z).hom ≫
        ((derivedSheafHomBifunctor X).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app B).op).app Z := by
  have h := derivedCurryIso_natural X u (𝟙 B) (𝟙 Z)
  simp only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id] at h
  exact h

/-- **Naturality of the derived currying equivalence of Stacks 08J9 on degree-zero global
hypercohomology, in the source variable.** -/
theorem derivedCurryGlobalEquiv_naturality_source
    {A A' B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : A' ⟶ A)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op A)).obj
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z))) : Type u)) :
    derivedCurryGlobalEquiv X A' B Z
        (derivedHomGlobalMap X u (𝟙 (((derivedSheafHomBifunctor X).obj (op B)).obj Z)) x) =
      derivedHomGlobalMap X
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app B) (𝟙 Z)
        (derivedCurryGlobalEquiv X A B Z x) := by
  rw [derivedCurryGlobalEquiv_apply, derivedCurryGlobalEquiv_apply, derivedHomGlobalMap_fst_eq,
    derivedHomGlobalMap_fst_eq]
  exact functor_map_apply_eq_of_comp_eq (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0)
    (by rw [← Functor.map_comp, ← Functor.map_comp, derivedCurryIso_natural_fst]) x

/-- **Stacks 08J8 is natural in its source variable.** Precomposing a morphism
`h : A ⟶ RSheafHom(B, Z)` with `u : A' ⟶ A` corresponds, under the tensor-internal-Hom
bijection `derivedCurryHomEquiv`, to precomposing the morphism `A ⊗^L_O B ⟶ Z` matched with
`h` by `u ⊗ 1`.

The bijection is the derived currying isomorphism of Stacks 08J9 read on degree-zero global
hypercohomology with both sides identified with morphism groups by Stacks 08JA, so this is the
object-level naturality `derivedCurryIso_natural` together with the naturality of Stacks 08JA
in its source variable,
`derivedSheafHomGlobalSectionsEquiv_naturality_source`. -/
@[stacks 08J8 "the tensor-internal-Hom bijection is natural in the source variable"]
theorem derivedCurryHomEquiv_naturality_source
    {A A' B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : A' ⟶ A)
    (h : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    derivedCurryHomEquiv X A' B Z (u ≫ h) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app B ≫
        derivedCurryHomEquiv X A B Z h := by
  obtain ⟨x, rfl⟩ : ∃ x, derivedSheafHomGlobalSectionsEquiv X A
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z) x = h :=
    ⟨_, (derivedSheafHomGlobalSectionsEquiv X A
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).apply_symm_apply h⟩
  rw [← derivedSheafHomGlobalSectionsEquiv_naturality_source X u x,
    derivedCurryHomEquiv_globalSections, derivedCurryHomEquiv_globalSections,
    derivedCurryGlobalEquiv_naturality_source,
    derivedSheafHomGlobalSectionsEquiv_naturality_source]

end AlgebraicGeometry.RingedSite

end
