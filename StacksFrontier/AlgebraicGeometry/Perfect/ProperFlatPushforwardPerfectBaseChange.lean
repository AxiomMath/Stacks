module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.QcohPresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect

/-!
# Cohomology and base change for a proper morphism of finite presentation

Let `f : X ⟶ S` be a proper morphism of finite presentation. [Stacks, Tag 0B91] asserts:

1. if `E ∈ D(𝒪_X)` is perfect and `f` is flat, then `Rf_*E` is a perfect object of `D(𝒪_S)` and
   its formation commutes with arbitrary base change;
2. if `𝒢` is an `𝒪_X`-module of finite presentation, flat over `S`, then `Rf_*𝒢` is a perfect
   object of `D(𝒪_S)` and its formation commutes with arbitrary base change.

Both are special cases of [Stacks, Tag 0A1H], clause (1) with `𝒢^• = 𝒪_X` in degree `0` and
clause (2) with `E = 𝒪_X` and `𝒢^• = 𝒢` in degree `0`.

## Main results

* `isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat`: clause (1), whose base
  change is the canonical map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of [Stacks, Tag 08HY],
  `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`.
* `isPerfect_derivedPushforward_module`: the perfectness half of clause (2).
* `isPerfect_derivedPushforward_and_isIso_derivedBaseChangeComp_of_isFlatOver`: clause (2), whose
  base change is the canonical map `Lg^*Rf_*𝒢 ⟶ Rf'_*L(g')^*𝒢 ⟶ Rf'_*(g')^*𝒢`, i.e. the map of
  [Stacks, Tag 08HY] followed by the derived-to-ordinary comparison, which is the sense the source
  gives it (the proof of [Stacks, Tag 0D4E]: "`Rf'_*(g')^*ℱ = Lg^*E`").
* `nonempty_derivedPullback_derivedPushforward_module_iso`: an isomorphism
  `Lg^*Rf_*𝒢 ≅ Rf'_*(g')^*𝒢`.

## Implementation notes

**Clause (1) needs only 0A1H.** At `𝒢^• = 𝒪_X[0]` the map of [Stacks, Tag 0A1H] is the map of
[Stacks, Tag 08HY] at `E ⊗^L 𝒪_X` followed by `Rf'_*` of the comparison
`L(g')^*(E ⊗^L 𝒪_X) ⟶ L(g')^*E ⊗^L (g')^*𝒪_X`. That comparison is invertible: it is the
monoidality isomorphism of [Stacks, Tag 079U] followed by `L(g')^*E ⊗^L` of the
derived-to-ordinary comparison at `𝒪_X[0]`, which is invertible because `𝒪_X[0]` is K-flat
(`Stacks.SheafOfModules.isKFlat_single_unit`). So the map of [Stacks, Tag 08HY] is invertible at
`E ⊗^L 𝒪_X`, and its naturality in the argument
(`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality`) carries that along the
right unit constraint `E ⊗^L 𝒪_X ≅ E` of [Stacks, Tag 0FPT]. No coherence of the unit constraint
is used.

**Clause (2) needs, in addition, the left-unit coherence of [Stacks, Tag 079U].** At `E = 𝒪_X`
the unit sits on the left and the derived-to-ordinary comparison sits at `𝒢`, which is not
K-flat; passing from `𝒪_X ⊗^L 𝒢` to `𝒢` then needs
`L(g')^*(λ_K) = μ_{𝒪,K} ≫ (η ⊗ 1) ≫ λ_{L(g')^*K}`, the left-unitality axiom of `L(g')^*` as a
monoidal functor whose tensorator is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`. That is not proved in this
library; it follows from a `Functor.Monoidal` structure on `Lf^*` for
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` whose tensorator is
`derivedPullbackTensorIso`, together with its unit lemma. Here it is the argument `h079Uunit`,
stated for every morphism of ringed spaces and every object, as the unitality equation itself; its
unit `η` is existentially quantified, and is the inverse of the unit `ε` of that monoidal
structure.

The isomorphism of `nonempty_derivedPullback_derivedPushforward_module_iso` needs no coherence: it
composes the invertible map of [Stacks, Tag 0A1H] with unit constraints and with
`L(g')^*𝒪_X ≅ 𝒪_{X'}`, without asserting anything about the composite.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0D4E](https://stacks.math.columbia.edu/tag/0D4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex derivedPullbackNatTrans
  derivedPullbackTensorIso)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.PerfectPushforward (structureComplex)

universe u

namespace AlgebraicGeometry.ProperFlatBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback StrictlyPerfect.structureSheafOfRings
  StrictlyPerfect.structureModule

/-- **The left unit constraint `𝒪_X ⊗^L E ≅ E`** of [Stacks, Tag 0FPT], with `𝒪_X` spelled as the
complex `Stacks.Cohomology.PerfectPushforward.structureComplex`. -/
def structureComplexTensorIso (X : Scheme.{u}) (E : DerivedCategory X.Modules) :
    ((derivedTensorProductFunctor X.sheaf).obj
      (DerivedCategory.Q.obj (structureComplex X))).obj E ≅ E :=
  ((derivedTensorProductFunctor X.sheaf).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
        (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules)).symm).app E ≪≫
    Stacks.RingedSpace.derivedTensorLeftUnitIso X.toRingedSpace E

/-- **`𝒪_X` in degree zero is a perfect object of `D(𝒪_X)`.** -/
theorem isPerfect_structureComplex (X : Scheme.{u}) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj (structureComplex X)) :=
  RingedSpace.IsPerfectComplex.isPerfect.{u, u + 1} (X := X.toRingedSpace)
    (E := (HomologicalComplex.single (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
      (ComplexShape.up ℤ) 0).obj (StrictlyPerfect.structureModule X.toRingedSpace))
    (RingedSpace.isPerfectComplex_of_isStrictlyPerfect
      (StrictlyPerfect.isStrictlyPerfect_single
        (StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule X.toRingedSpace) 0))

/-- If `e₁.hom ≫ x = y ≫ e₂.hom` for isomorphisms `e₁`, `e₂` and an isomorphism `y`, then `x` is an
isomorphism. -/
private theorem isIso_of_comm_sq {C : Type*} [Category C] {W X Y Z : C} (e₁ : W ≅ X) (e₂ : Y ≅ Z)
    {x : X ⟶ Z} {y : W ⟶ Y} [IsIso y] (w : e₁.hom ≫ x = y ≫ e₂.hom) : IsIso x := by
  have : IsIso (e₁.hom ≫ x) := w ▸ inferInstance
  exact IsIso.of_isIso_comp_left e₁.hom x

/-- **[Stacks, Tag 0B91], clause (1).** Let `f : X ⟶ S` be a proper flat morphism of finite
presentation and let `E ∈ D(𝒪_X)` be perfect. Then `Rf_*E` is a perfect object of `D(𝒪_S)`, and its
formation commutes with arbitrary base change: for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the canonical map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of [Stacks, Tag 08HY] is an isomorphism. -/
theorem isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (hflat : Flat f) (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    RingedSpace.IsPerfect (X := S.toRingedSpace) ((derivedPushforward f.toLRSHom.toShHom).obj E) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (hsq : IsPullback g' f' f g),
        IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
          g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w) E) := by
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have := hproper
  have := hflat
  obtain ⟨hperf, hbc⟩ :=
    isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap f hf E hE _
      (flatProperSupportFinitelyPresented_structure f)
  let ρ := Stacks.Cohomology.PerfectPushforward.tensorStructureComplexIso
    (canonicalDerivedTensorProduct X.sheaf) E
  refine ⟨Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_iso
    ((derivedPushforward f.toLRSHom.toShHom).mapIso (ρ)) hperf, ?_⟩
  intro X' S' g f' g' hsq
  have hT := hbc g f' g' hsq
  have hB : IsIso ((derivedPushforward f'.toLRSHom.toShHom).map
      (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison
        g'.toLRSHom.toShHom E (DerivedCategory.Q.obj (structureComplex X))
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj
          (singleDegreeComplex (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules))))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app
          (singleDegreeComplex (StrictlyPerfect.structureModule X.toRingedSpace :
            X.Modules))))) :=
    ((derivedPushforward f'.toLRSHom.toShHom).mapIso
      ((derivedPullbackTensorIso g'.toLRSHom.toShHom).app
          (E, DerivedCategory.Q.obj (structureComplex X)) ≪≫
        ((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).mapIso
          (@asIso _ _ _ _ ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app
            (singleDegreeComplex (StrictlyPerfect.structureModule X.toRingedSpace :
              X.Modules)))
              (Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app _ _
                (Stacks.SheafOfModules.isKFlat_single_unit X.sheaf))))).isIso_hom
  have hbcT : IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w)
      (((derivedTensorProductFunctor X.sheaf).obj E).obj
        (DerivedCategory.Q.obj (structureComplex X)))) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hB hT
  have nat := Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) (ρ).hom
  have := hbcT
  exact isIso_of_comm_sq ((derivedPullback g.toLRSHom.toShHom).mapIso
    ((derivedPushforward f.toLRSHom.toShHom).mapIso ρ))
    ((derivedPushforward f'.toLRSHom.toShHom).mapIso
      ((derivedPullback g'.toLRSHom.toShHom).mapIso ρ))
    nat

/-- **The perfectness half of [Stacks, Tag 0B91], clause (2).** For a proper morphism `f : X ⟶ S`
of finite presentation and an `𝒪_X`-module `ℱ` of finite presentation, flat over `S`, the object
`Rf_*ℱ` of `D(𝒪_S)` is perfect. -/
theorem isPerfect_derivedPushforward_module
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation) (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have := hproper
  exact Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_iso
    ((derivedPushforward f.toLRSHom.toShHom).mapIso
      (structureComplexTensorIso X (DerivedCategory.Q.obj (singleDegreeComplex F))))
    (isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap f hf
      (DerivedCategory.Q.obj (structureComplex X)) (isPerfect_structureComplex X)
      (singleDegreeComplex F)
      (flatProperSupportFinitelyPresented_singleDegreeComplex f F hfp hflat)).1

/-- **An isomorphism `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ`.** For a cartesian square with `f` proper of finite
presentation and an `𝒪_X`-module `ℱ` of finite presentation, flat over `S`, the objects `Lg^*Rf_*ℱ`
and `Rf'_*(g')^*ℱ` of `D(𝒪_{S'})` are isomorphic. -/
theorem nonempty_derivedPullback_derivedPushforward_module_iso
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation) (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≅
      (derivedPushforward f'.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj
          ((Scheme.Modules.pullback g').obj F))) := by
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have := hproper
  have hT := (isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap f hf
      (DerivedCategory.Q.obj (structureComplex X))
      (isPerfect_structureComplex X) (singleDegreeComplex F)
      (flatProperSupportFinitelyPresented_singleDegreeComplex f F hfp hflat)).2 g f' g' hsq
  exact ⟨(derivedPullback g.toLRSHom.toShHom).mapIso
      ((derivedPushforward f.toLRSHom.toShHom).mapIso
        (structureComplexTensorIso X (DerivedCategory.Q.obj (singleDegreeComplex F))).symm) ≪≫
    @asIso _ _ _ _ _ hT ≪≫
    (derivedPushforward f'.toLRSHom.toShHom).mapIso
      (((derivedTensorProductFunctor X'.sheaf).mapIso
          (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso
            g'.toLRSHom.toShHom)).app _ ≪≫
        structureComplexTensorIso X' _ ≪≫
        DerivedCategory.Q.mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pullback g')
            (ComplexShape.up ℤ) 0).app F))⟩

/-- **The canonical base-change map of [Stacks, Tag 0B91], clause (2), is invertible**, granted the
left-unit coherence of [Stacks, Tag 079U] (`h079Uunit`). For a cartesian square with `f` proper of
finite presentation and an `𝒪_X`-module `ℱ` of finite presentation, flat over `S`, the map
`Lg^*Rf_*ℱ ⟶ Rf'_*L(g')^*ℱ ⟶ Rf'_*(g')^*ℱ` — the map of [Stacks, Tag 08HY] followed by `Rf'_*` of
the derived-to-ordinary comparison — is an isomorphism. -/
theorem isIso_derivedBaseChangeComp_module
    (h079Uunit : ∀ {Y' Y : RingedSpace.{u, u}} (h : Y' ⟶ Y),
      ∃ η : (derivedPullback h).obj (@MonoidalCategoryStruct.tensorUnit _ _
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
            Y.sheaf).toMonoidalCategoryStruct) ≅
        @MonoidalCategoryStruct.tensorUnit _ _
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
            Y'.sheaf).toMonoidalCategoryStruct,
        ∀ K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
          (derivedPullback h).map (@MonoidalCategoryStruct.leftUnitor _ _
              (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
                Y.sheaf).toMonoidalCategoryStruct K).hom =
            (derivedPullbackTensorIso h).hom.app (_, K) ≫
              ((derivedTensorProductFunctor Y'.sheaf).map η.hom).app _ ≫
              (@MonoidalCategoryStruct.leftUnitor _ _
                (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
                  Y'.sheaf).toMonoidalCategoryStruct ((derivedPullback h).obj K)).hom)
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation) (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsIso (derivedBaseChangeComp f g f' g' hsq.w (DerivedCategory.Q.obj (singleDegreeComplex F))
      (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex F)))
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F))) := by
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have := hproper
  let U := @MonoidalCategoryStruct.tensorUnit _ _
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
      X.sheaf).toMonoidalCategoryStruct
  have hU : RingedSpace.IsPerfect (X := X.toRingedSpace) U :=
    Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_iso
      (eqToIso (Stacks.SheafOfModules.DerivedMonoidal.tensorUnit_canonicalDerivedMonoidal
        X.sheaf).symm) (isPerfect_structureComplex X)
  have hT := (isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap f hf U hU
      (singleDegreeComplex F)
      (flatProperSupportFinitelyPresented_singleDegreeComplex f F hfp hflat)).2 g f' g' hsq
  obtain ⟨η, hη⟩ := h079Uunit g'.toLRSHom.toShHom
  have nat := Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) (@MonoidalCategoryStruct.leftUnitor _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
        X.sheaf).toMonoidalCategoryStruct (DerivedCategory.Q.obj (singleDegreeComplex F))).hom
  have hlam := @MonoidalCategory.leftUnitor_naturality _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X'.sheaf) _ _
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F))
  have hnatη := ((derivedTensorProductFunctor X'.sheaf).map η.hom).naturality
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F))
  have aux : (derivedPullback g'.toLRSHom.toShHom).map (@MonoidalCategoryStruct.leftUnitor _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
        X.sheaf).toMonoidalCategoryStruct (DerivedCategory.Q.obj (singleDegreeComplex F))).hom ≫
      (derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F) =
      Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison
        g'.toLRSHom.toShHom U (DerivedCategory.Q.obj (singleDegreeComplex F))
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj
          (singleDegreeComplex F)))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F)) ≫
      ((derivedTensorProductFunctor X'.sheaf).map η.hom).app _ ≫
      (@MonoidalCategoryStruct.leftUnitor _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
          X'.sheaf).toMonoidalCategoryStruct (DerivedCategory.Q.obj
            ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex F)))).hom := by
    refine (congrArg (· ≫ _) (hη _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (_ ≫ ·) ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) hlam.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ _) hnatη.symm
  have key : (derivedPullback g.toLRSHom.toShHom).map
        ((derivedPushforward f.toLRSHom.toShHom).map (@MonoidalCategoryStruct.leftUnitor _ _
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
            X.sheaf).toMonoidalCategoryStruct
              (DerivedCategory.Q.obj (singleDegreeComplex F))).hom) ≫
      derivedBaseChangeComp f g f' g' hsq.w (DerivedCategory.Q.obj (singleDegreeComplex F))
        (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex F)))
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F)) =
      tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) U (singleDegreeComplex F) ≫
        (derivedPushforward f'.toLRSHom.toShHom).map
          (((derivedTensorProductFunctor X'.sheaf).map η.hom).app _ ≫
            (@MonoidalCategoryStruct.leftUnitor _ _
              (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
                X'.sheaf).toMonoidalCategoryStruct (DerivedCategory.Q.obj
                  ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex F)))).hom) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) nat).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (_ ≫ ·) ?_
    refine ((derivedPushforward f'.toLRSHom.toShHom).map_comp _ _).symm.trans ?_
    refine (congrArg (derivedPushforward f'.toLRSHom.toShHom).map aux).trans ?_
    exact (derivedPushforward f'.toLRSHom.toShHom).map_comp _ _
  have := hT
  exact isIso_of_comm_sq
    ((derivedPullback g.toLRSHom.toShHom).mapIso ((derivedPushforward f.toLRSHom.toShHom).mapIso
      (@MonoidalCategoryStruct.leftUnitor _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
          X.sheaf).toMonoidalCategoryStruct (DerivedCategory.Q.obj (singleDegreeComplex F)))))
    ((derivedPushforward f'.toLRSHom.toShHom).mapIso
      (((derivedTensorProductFunctor X'.sheaf).mapIso η).app _ ≪≫
        (@MonoidalCategoryStruct.leftUnitor _ _
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
            X'.sheaf).toMonoidalCategoryStruct (DerivedCategory.Q.obj
              ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex F))))))
    key

/-- **[Stacks, Tag 0B91], clause (2), granted the left-unit coherence of [Stacks, Tag 079U]
(`h079Uunit`).** Let `f : X ⟶ S` be a proper morphism of finite presentation and let `ℱ` be an
`𝒪_X`-module of finite presentation, flat over `S`. Then `Rf_*ℱ` is a perfect object of `D(𝒪_S)`,
and its formation commutes with arbitrary base change: for every cartesian square the canonical map
`Lg^*Rf_*ℱ ⟶ Rf'_*(g')^*ℱ` — the map of [Stacks, Tag 08HY] followed by `Rf'_*` of the
derived-to-ordinary comparison `L(g')^*ℱ ⟶ (g')^*ℱ` — is an isomorphism. -/
theorem isPerfect_derivedPushforward_and_isIso_derivedBaseChangeComp_of_isFlatOver
    (h079Uunit : ∀ {Y' Y : RingedSpace.{u, u}} (h : Y' ⟶ Y),
      ∃ η : (derivedPullback h).obj (@MonoidalCategoryStruct.tensorUnit _ _
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
            Y.sheaf).toMonoidalCategoryStruct) ≅
        @MonoidalCategoryStruct.tensorUnit _ _
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
            Y'.sheaf).toMonoidalCategoryStruct,
        ∀ K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
          (derivedPullback h).map (@MonoidalCategoryStruct.leftUnitor _ _
              (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
                Y.sheaf).toMonoidalCategoryStruct K).hom =
            (derivedPullbackTensorIso h).hom.app (_, K) ≫
              ((derivedTensorProductFunctor Y'.sheaf).map η.hom).app _ ≫
              (@MonoidalCategoryStruct.leftUnitor _ _
                (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
                  Y'.sheaf).toMonoidalCategoryStruct ((derivedPullback h).obj K)).hom)
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation) (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
        ((derivedPushforward f.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (singleDegreeComplex F))) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (hsq : IsPullback g' f' f g),
        IsIso (derivedBaseChangeComp f g f' g' hsq.w (DerivedCategory.Q.obj (singleDegreeComplex F))
          (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj
            (singleDegreeComplex F)))
          ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F))) :=
  ⟨isPerfect_derivedPushforward_module f hf hproper F hfp hflat,
    fun g f' g' hsq =>
      isIso_derivedBaseChangeComp_module h079Uunit f g f' g' hsq hf hproper F hfp hflat⟩

end AlgebraicGeometry.ProperFlatBaseChange

end
