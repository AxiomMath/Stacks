module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.CupWithDerivedClass
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalCupStatements
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapOfSheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedGlobalCupProduct.UnitEvaluation
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupSectionClass
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgePullback
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyPullbackShift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingleUnit
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.TorVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional

/-!
# Classes represented by morphisms out of the shifted structure sheaf

Let `V` be a scheme, `F` an `𝒪_V`-module and `n ≥ 0`. A morphism `t : 𝒪_V[-n] ⟶ F[0]` of
`D(𝒪_V)` induces `Hⁿ(t) : H⁰(V, 𝒪_V) ⟶ Hⁿ(V, F)`, and `Hⁿ(t)(1)` is the class it represents. This
file proves that every class of `Hⁿ(V, F)` is represented in this way, and that the pullback map
`g^* : Hⁿ(V, F) ⟶ Hⁿ(V', g^*F)` of [Stacks, Tag 01F9] along a morphism of schemes `g : V' ⟶ V`
carries the class represented by `t` to the class represented by its derived pullback
`𝒪_{V'}[-n] ≅ Lg^*(𝒪_V[-n]) ⟶ Lg^*(F[0]) ⟶ (g^*F)[0]`.

The first statement is the surjectivity of evaluation at the class of `1`,
`Hom_{D(𝒪_V)}(𝒪_V[-n], K) ⟶ Hⁿ(V, K)`
(`Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit_surjective`), once the class of the section
`1` placed in degree `n` is identified with the class of the cocycle `1` of `Γ(V, 𝒪_V[-n])`
(`hgroupModuleShiftIso_sectionClass_unitSection`); this identification is made by moving the
cocycle to degree `0` through the shift. For the second, the derived `g`-map of
[Stacks, Tag 01F8] attached to `φ : ℳ ⟶ g_*ℳ'` is the transpose along `Lg^* ⊣ Rg_*` of the
derived-to-ordinary comparison followed by the adjoint of `φ`; at `ℳ = F`, `φ` the unit, and at
`ℳ = 𝒪_V`, `φ = g^♯`, this gives a commuting square in `D(𝒪_V)`
(`derivedPushforwardMap_square`), which `cohomologyMapOfSingleHom_pullbackHgroup` turns into the
statement, the pullback of `1` being `1`.

## Main definitions

* `Stacks.WeilDeRham.ClassRepresented`, `Stacks.WeilDeRham.PullbackRepresented`: the two
  statements.
* `Stacks.WeilDeRham.derivedPullbackUnitComparison`: the comparison
  `Lf^*(𝒪_Y[-n]) ⟶ (f^*𝒪_Y)[-n] ≅ 𝒪_X[-n]`, an isomorphism.
* `Stacks.WeilDeRham.unitPullbackComparison`: its inverse, for a morphism of schemes.

## Main results

* `Stacks.WeilDeRham.classRepresented`: every class of `Hⁿ(V, F)` is `Hⁿ(t)(1)`.
* `Stacks.WeilDeRham.pullbackRepresented`: the pullback of the class of `t` is the class of its
  derived pullback.
* `Stacks.WeilDeRham.hgroupModuleShiftIso_sectionClass_unitSection`: the class of `1` placed in
  degree `n` is the class of the cocycle `1`.

## References

* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCupHodge
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-- **Every class of `Hⁿ(V, F)` is represented by a morphism `𝒪_V[-n] ⟶ F[0]`**: for every
`θ ∈ Hⁿ(V, F)` there is `t : 𝒪_V[-n] ⟶ F[0]` in `D(𝒪_V)` with `θ = Hⁿ(t)(1)`, both read through
`hgroupModuleShiftIso`, which absorbs the two spellings `n` and `0 + n` of the degree. -/
def ClassRepresented {V : Scheme.{u}} (F : V.Modules) (n : ℕ) : Prop :=
  ∀ θ : Hgroup (structureSheafRing V.toRingedSpace) ⊤ n F,
    ∃ t : (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
        (n : ℤ)).obj (unitModule V.toRingedSpace) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
        ((0 : ℕ) : ℤ)).obj F,
      (hgroupModuleShiftIso (X := V.toRingedSpace) F 0 n n (by simp)).hom θ =
        (hgroupModuleShiftIso (X := V.toRingedSpace) F 0 (0 + n) n (by simp)).hom
          (cohomologyMapOfSingleHom V.toRingedSpace (unitModule V.toRingedSpace) F n 0 t
            (sectionClass unitSection))

/-- **The pullback of a represented class is represented by the derived pullback**: for
comparisons `cU : 𝒪_{V'}[-n] ⟶ Lg^*(𝒪_V[-n])` and `cF : Lg^*(F[0]) ⟶ (g^*F)[0]`, the pullback map
of [Stacks, Tag 01F9] sends `Hⁿ(t)(1)` to `Hⁿ(cU ≫ Lg^*(t) ≫ cF)(1)` for every
`t : 𝒪_V[-n] ⟶ F[0]`. -/
def PullbackRepresented {V V' : Scheme.{u}} (g : V' ⟶ V) (F : V.Modules) (n : ℕ)
    (cU : (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V'.toRingedSpace))
        (n : ℤ)).obj (unitModule V'.toRingedSpace) ⟶
      (derivedPullback g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
          (n : ℤ)).obj (unitModule V.toRingedSpace)))
    (cF : (derivedPullback g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
          ((0 : ℕ) : ℤ)).obj F) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V'.toRingedSpace))
          ((0 : ℕ) : ℤ)).obj ((Scheme.Modules.pullback g).obj F)) : Prop :=
  ∀ t : (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
        (n : ℤ)).obj (unitModule V.toRingedSpace) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
        ((0 : ℕ) : ℤ)).obj F,
    (unitPullback g F (0 + n)).hom
        (cohomologyMapOfSingleHom V.toRingedSpace (unitModule V.toRingedSpace) F n 0 t
          (sectionClass unitSection)) =
      cohomologyMapOfSingleHom V'.toRingedSpace (unitModule V'.toRingedSpace)
        ((Scheme.Modules.pullback g).obj F) n 0
        (cU ≫ (derivedPullback g.toLRSHom.toShHom).map t ≫ cF) (sectionClass unitSection)

section UnitClass

open Stacks.Cohomology.DerivedGlobalCupProduct (globalSections sectionsComplex shiftCycles
  unitCycleHom)
open Stacks.Cohomology.GlobalKunneth (baseRing)

variable {X : RingedSpace.{u, u}}

/-- The degree-`n` component of the identification `M[-n] ≅ (M[0])[-n]`, read between the two
copies of `M`, is the identity. -/
theorem singleObjXSelf_inv_comp_shiftIso_inv_f {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] (M : C) (n : ℤ) (h : n + -n = 0) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M).inv ≫
        (((CochainComplex.singleFunctors C).shiftIso (-n) n 0 (by omega)).inv.app M).f n ≫
        (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M).XIsoOfEq h).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := by
  simp [CochainComplex.singleFunctors, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.XIsoOfEq]

/-- The identification `𝒪[-n] ≅ (𝒪[0])[-n]` of `singleNatShiftIso`, without its first
factor. -/
abbrev unitShiftMap (n : ℕ) :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) (n : ℤ)).obj (unitModule X) ⟶
      ((singleNat (unitModule X) 0).extend ComplexShape.embeddingUpNat)⟦-(n : ℤ)⟧ :=
  ((CochainComplex.singleFunctors _).shiftIso (-(n : ℤ)) (n : ℤ) 0 (by omega)).inv.app
      (unitModule X) ≫
    (CategoryTheory.shiftFunctor _ (-(n : ℤ))).map
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (unitModule X) 0 0 rfl).inv

/-- `singleNatShiftIso` after the identification of the extension by zero of `𝒪[-n]` with
`𝒪[-n]` is `unitShiftMap`. -/
theorem extendSingleIso_inv_comp_singleNatShiftIso_hom (n : ℕ) :
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (unitModule X) n n rfl).inv ≫
        (singleNatShiftIso (unitModule X) n).hom = unitShiftMap n :=
  Iso.inv_hom_id_assoc _ _

/-- The algebra of `singleObjXSelf_inv_comp_unitShiftMap_f`, at variables. -/
private lemma unitShift_chase {C : Type*} [Category C] {P Q R R' T T' : C} (s : P ⟶ Q)
    (a : Q ⟶ R) (xs : R ⟶ R') (s₀ : P ⟶ R') (b : R ⟶ T) (b₀ : R' ⟶ T') (xe : T ⟶ T')
    (one : R' ⟶ R') (hK : s ≫ a ≫ xs = s₀) (hN : b ≫ xe = xs ≫ b₀) (hone : one = 𝟙 R') :
    s ≫ (a ≫ b) ≫ xe = s₀ ≫ one ≫ b₀ := by
  subst hone
  rw [Category.id_comp, ← hK]
  simp only [Category.assoc]
  rw [hN]

/-- The degree-`n` component of `unitShiftMap`, followed by the degree identification
`n - n = 0`, is the degree-`0` component of the chain map of the section `1`. -/
theorem singleObjXSelf_inv_comp_unitShiftMap_f (n : ℕ) (h : (n : ℤ) + -(n : ℤ) = 0) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (n : ℤ) (unitModule X)).inv ≫
        (unitShiftMap n).f (n : ℤ) ≫
        (((singleNat (unitModule X) 0).extend ComplexShape.embeddingUpNat).XIsoOfEq h).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (unitModule X)).inv ≫
        (unitComplexSectionMap (unitModule X) unitSection).f 0 := by
  have hone : ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      ((unitModule X).unitHomEquiv.symm (unitSection (X := X)))).f 0 = 𝟙 _ := by
    rw [unitSection, Equiv.symm_apply_apply, CategoryTheory.Functor.map_id]
    rfl
  exact unitShift_chase _ _ _ _ _ _ _ _
    (singleObjXSelf_inv_comp_shiftIso_inv_f (unitModule X) (n : ℤ) h)
    (HomologicalComplex.XIsoOfEq_hom_naturality
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (unitModule X) 0 0 rfl).inv h)
    hone

/-- Two cycle maps followed by `iCycles` and a morphism, on an element. At variables. -/
private lemma cycles_chase {R : Type u} [Ring R] {A B C : CochainComplex (ModuleCat.{u} R) ℤ}
    {D : ModuleCat.{u} R} (n : ℤ) (φ : A ⟶ B) (χ : B ⟶ C) (ξ : C.X n ⟶ D) (a : A.cycles n) :
    ξ.hom ((C.iCycles n).hom
        ((HomologicalComplex.cyclesMap φ n ≫ HomologicalComplex.cyclesMap χ n).hom a)) =
      (φ.f n ≫ χ.f n ≫ ξ).hom ((A.iCycles n).hom a) := by
  change ((HomologicalComplex.cyclesMap φ n ≫ HomologicalComplex.cyclesMap χ n) ≫
    C.iCycles n ≫ ξ).hom a = (A.iCycles n ≫ φ.f n ≫ χ.f n ≫ ξ).hom a
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i_assoc]

/-- A functor into modules applied to a commuting square, on an element. At variables. -/
private lemma sections_chase {C : Type*} [Category C] {R : Type u} [Ring R]
    (Γ : C ⥤ ModuleCat.{u} R) {P Q T T₀ P' : C} (s : P ⟶ Q) (ψ : Q ⟶ T) (x : T ⟶ T₀)
    (s₀ : P ⟶ P') (v : P' ⟶ T₀) (cs : Γ.obj T ⟶ Γ.obj T) (ξ : Γ.obj T ⟶ Γ.obj T₀)
    (hcs : cs = 𝟙 _) (hξ : ξ = Γ.map x) (h : s ≫ ψ ≫ x = s₀ ≫ v) (p : Γ.obj P) :
    (Γ.map ψ ≫ cs ≫ ξ).hom ((Γ.map s).hom p) = (Γ.map v).hom ((Γ.map s₀).hom p) := by
  subst hcs hξ
  simpa using congrArg (fun f => (Γ.map f).hom p) h

/-- **The cocycle `1` placed in degree `n`, moved to degree `0` of the shift**, is the cocycle
of the section `1` of `𝒪[0]`. -/
theorem shiftCycles_unitCycle (n : ℕ) :
    shiftCycles (sectionsComplex X ((singleNat (unitModule X) 0).extend
        ComplexShape.embeddingUpNat)) 0 (by simp : -(n : ℤ) + n = 0)
      (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing X) _
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle X n)) ≫
        HomologicalComplex.cyclesMap (((globalSections X).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (unitShiftMap n)) n ≫
        HomologicalComplex.cyclesMap ((((_root_.SheafOfModules.evaluation
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) (op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso (-(n : ℤ))).hom.app
              ((singleNat (unitModule X) 0).extend ComplexShape.embeddingUpNat)) n) =
      unitCycleHom X ≫ HomologicalComplex.cyclesMap (((globalSections X).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (unitComplexSectionMap (unitModule X) unitSection)) 0 := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ 0),
    Stacks.Cohomology.DerivedGlobalCupProduct.shiftCycles_iCycles]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  apply Stacks.Cohomology.DerivedGlobalCupProduct.moduleCat_hom_ext_of_one
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul]
  refine (cycles_chase (n : ℤ) _ _ _ _).trans ?_
  have h1 : (unitCycleHom X).hom 1 = Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle X 0 :=
    one_smul _ _
  refine (congrArg (ModuleCat.Hom.hom _)
    (Stacks.Cohomology.DerivedGlobalCupProduct.iCycles_unitCycle X (n : ℤ))).trans ?_
  refine Eq.trans ?_ (congrArg (ModuleCat.Hom.hom _) ((congrArg (ModuleCat.Hom.hom _) h1).trans
    (Stacks.Cohomology.DerivedGlobalCupProduct.iCycles_unitCycle X 0))).symm
  refine sections_chase (globalSections X) _ _ _ _ _ _ _ rfl ?_
    (singleObjXSelf_inv_comp_unitShiftMap_f n (by omega)) _
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso.hom]
  exact (eqToHom_map (globalSections X) _).symm

/-- The algebra of `globalCycleClass_unitCycle_shift`, at variables. -/
private lemma class_chase {C : Type*} [Category C] {P A B D E : C} (g : P ⟶ A) (a : A ⟶ B)
    (b : B ⟶ D) (ab : A ⟶ D) (c : D ⟶ E) (g' : P ⟶ D) (g'' : P ⟶ E) (hab : a ≫ b = ab)
    (h₁ : g ≫ ab = g') (h₂ : g' ≫ c = g'') : g ≫ a ≫ b ≫ c = g'' := by
  rw [reassoc_of% hab, reassoc_of% h₁, h₂]

open Stacks.Cohomology.DerivedGlobalCupProduct (globalCycleClass shiftCohomologyIsoR) in
/-- The class of the cocycle `1` placed in degree `n`, read on the extension by zero and moved to
degree `0` by the shift, is the class of the cocycle of the section `1` of `𝒪[0]`. -/
theorem globalCycleClass_unitCycle_shift (n : ℕ) :
    globalCycleClass (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing X) _
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle X n))) ≫
      (DerivedCategory.homologyFunctor _ (n : ℤ)).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
        (moduleDerivedSingleIso (X := X) (unitModule X) n).inv) ≫
      (DerivedCategory.homologyFunctor _ (n : ℤ)).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
        (DerivedCategory.Q.map (singleNatShiftIso (unitModule X) n).hom)) ≫
      (shiftCohomologyIsoR (S := X)
        ((singleNat (unitModule X) 0).extend ComplexShape.embeddingUpNat)
        (-(n : ℤ)) n 0 (by simp)).hom =
    globalCycleClass (unitCycleHom X ≫ HomologicalComplex.cyclesMap
      (((globalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (unitComplexSectionMap (unitModule X) unitSection)) 0) := by
  have hab : (DerivedCategory.homologyFunctor _ (n : ℤ)).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
          (moduleDerivedSingleIso (X := X) (unitModule X) n).inv) ≫
      (DerivedCategory.homologyFunctor _ (n : ℤ)).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
          (DerivedCategory.Q.map (singleNatShiftIso (unitModule X) n).hom)) =
      (DerivedCategory.homologyFunctor _ (n : ℤ)).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
          (DerivedCategory.Q.map (unitShiftMap n))) :=
    (Functor.map_comp _ _ _).symm.trans (congrArg (DerivedCategory.homologyFunctor _ (n : ℤ)).map
      ((Functor.map_comp _ _ _).symm.trans
        (congrArg (Stacks.Cohomology.GlobalKunneth.baseSections X).map
          ((DerivedCategory.Q.map_comp _ _).symm.trans
            (congrArg DerivedCategory.Q.map (extendSingleIso_inv_comp_singleNatShiftIso_hom n))))))
  exact class_chase _ _ _ _ _ _ _ hab
    (Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass_map _ (unitShiftMap n))
    ((Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass_shiftCohomologyIsoR
      ((singleNat (unitModule X) 0).extend ComplexShape.embeddingUpNat) (-(n : ℤ)) n 0 (by simp)
      _).trans (congrArg globalCycleClass (shiftCycles_unitCycle n)))

open Stacks.Cohomology.DerivedGlobalCupProduct (globalCycleClass shiftCohomologyIsoR) in
/-- **The bridge carries the class of `1` placed in degree `n` to the class of the cocycle
`1`**: `hgroupModuleShiftIso` in degree `n` sends `1 ∈ H⁰(X, 𝒪_X)` to the image of
`Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleClass` under the identification of the
extension by zero of `𝒪[-n]` with `𝒪[-n]`. -/
theorem hgroupModuleShiftIso_sectionClass_unitSection (n : ℕ) :
    (hgroupModuleShiftIso (X := X) (unitModule X) n 0 n (by simp)).hom (sectionClass unitSection) =
      ((DerivedCategory.homologyFunctor _ (n : ℤ)).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
          (moduleDerivedSingleIso (X := X) (unitModule X) n).inv)).hom
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleClass X n) := by
  have hS := hgroupModuleShiftIso_shift_apply (X := X) (unitModule X) n 0 (n : ℤ) (by simp)
    (by simp) (sectionClass unitSection)
  have h₀ : (hgroupModuleShiftIso (X := X) (unitModule X) 0 0 ((0 : ℕ) : ℤ) (by simp)).hom
      (sectionClass unitSection) =
      (globalCycleClass (unitCycleHom X ≫ HomologicalComplex.cyclesMap
        (((globalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (unitComplexSectionMap (unitModule X) unitSection)) 0)).hom 1 :=
    (hgroupModuleShiftIso_sectionClass X (unitModule X) unitSection).trans
      (ConcreteCategory.congr_hom (Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass_map
        (unitCycleHom X) (unitComplexSectionMap (unitModule X) unitSection)) 1)
  have hc : Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleClass X n =
      (globalCycleClass (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing X) _
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle X n)))).hom 1 :=
    ((Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass_apply _ 1).trans
      (congrArg _ (one_smul _ _))).symm
  have hM' := (ConcreteCategory.congr_hom (globalCycleClass_unitCycle_shift (X := X) n) 1).trans
    h₀.symm
  have hM : (shiftCohomologyIsoR (S := X) ((singleNat (unitModule X) 0).extend
      ComplexShape.embeddingUpNat) (-(n : ℤ)) n 0 (by simp)).hom.hom
      (((DerivedCategory.homologyFunctor _ (n : ℤ)).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
          (DerivedCategory.Q.map (singleNatShiftIso (unitModule X) n).hom))).hom
        (((DerivedCategory.homologyFunctor _ (n : ℤ)).map
          ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
            (moduleDerivedSingleIso (X := X) (unitModule X) n).inv)).hom
          (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleClass X n))) =
      (hgroupModuleShiftIso (X := X) (unitModule X) 0 0 ((0 : ℕ) : ℤ) (by simp)).hom
        (sectionClass unitSection) := by
    rw [hc]
    exact hM'
  refine hS.trans ?_
  refine (congrArg (fun x => ((DerivedCategory.homologyFunctor _ (n : ℤ)).map
    ((Stacks.Cohomology.GlobalKunneth.baseSections X).map
      (DerivedCategory.Q.map (singleNatShiftIso (unitModule X) n).inv))).hom
    ((shiftCohomologyIsoR (S := X) ((singleNat (unitModule X) 0).extend
      ComplexShape.embeddingUpNat) (-(n : ℤ)) n 0 (by simp)).inv.hom x)) hM.symm).trans ?_
  erw [Iso.hom_inv_id_apply]
  exact ConcreteCategory.congr_hom ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
    ((Stacks.Cohomology.GlobalKunneth.baseSections X).mapIso
      (DerivedCategory.Q.mapIso (singleNatShiftIso (unitModule X) n)))).hom_inv_id _

end UnitClass

section Representatives

/-- Cancelling the two identifications around a morphism. At variables. -/
private lemma inv_comp_conj {C : Type*} [Category C] {P Q R S : C} (e : P ≅ Q) (φ : Q ⟶ R)
    (f : R ≅ S) : e.inv ≫ e.hom ≫ (φ ≫ f.hom) ≫ f.inv = φ := by
  simp

/-- A functor applied to two composable morphisms whose composite is given. At variables. -/
private lemma map_comp_apply_of_eq {C : Type*} [Category C] {R : Type u} [Ring R]
    (Φ : C ⥤ ModuleCat.{u} R) {P Q T : C} (a : P ⟶ Q) (b : Q ⟶ T) (c : P ⟶ T) (h : a ≫ b = c)
    (x : Φ.obj P) : (Φ.map b).hom ((Φ.map a).hom x) = (Φ.map c).hom x := by
  rw [← h, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **R1: every class is represented by a morphism out of the shifted structure sheaf.** Every
`θ ∈ Hⁿ(V, F)` is `Hⁿ(t)(1)` for a morphism `t : 𝒪_V[-n] ⟶ F[0]` of `D(𝒪_V)`, both classes read
through `hgroupModuleShiftIso`: evaluation at the class of `1` is surjective onto `Hⁿ(V, F)`. -/
theorem classRepresented {V : Scheme.{u}} (F : V.Modules) (n : ℕ) : ClassRepresented F n := by
  intro θ
  obtain ⟨φ, hφ⟩ := Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit_surjective
    (X := V.toRingedSpace)
    (AlgebraicGeometry.SheafOfModules.moduleDerived (A := V.sheaf) (singleNat F 0)) (n : ℤ)
    ((hgroupModuleShiftIso (X := V.toRingedSpace) F 0 n n (by simp)).hom θ)
  refine ⟨φ ≫ (moduleDerivedSingleIso (X := V.toRingedSpace) F 0).hom, ?_⟩
  have hb := hgroupModuleShiftIso_cohomologyMapOfSingleHom (X := V.toRingedSpace)
    (unitModule V.toRingedSpace) F n 0 (n : ℤ) (by simp) (by simp)
    (φ ≫ (moduleDerivedSingleIso (X := V.toRingedSpace) F 0).hom) (sectionClass unitSection)
  have hu := hgroupModuleShiftIso_sectionClass_unitSection (X := V.toRingedSpace) n
  refine hφ.symm.trans (Eq.trans ?_ hb.symm)
  refine Eq.trans ?_ (congrArg _ hu).symm
  exact (map_comp_apply_of_eq (Stacks.Cohomology.GlobalKunneth.baseSections V.toRingedSpace ⋙
    DerivedCategory.homologyFunctor _ (n : ℤ)) _ _ _
      (inv_comp_conj (moduleDerivedSingleIso (X := V.toRingedSpace) (unitModule V.toRingedSpace) n)
        φ (moduleDerivedSingleIso (X := V.toRingedSpace) F 0)) _).symm

end Representatives

section PullbackComparison

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (derivedToOrdinaryPullbackSingle)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullbackComparison
  derivedAdjunction derivedPushforward)
open Stacks.DeRham.GysinCohomologyBaseChange

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The derived-to-ordinary comparison `Lf^*(𝒪_Y[-n]) ⟶ (f^*𝒪_Y)[-n] ≅ 𝒪_X[-n]`. -/
def derivedPullbackUnitComparison (n : ℤ) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Y)) n).obj
          (SheafOfModules.unit (structureSheafRing Y))) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) n).obj
        (SheafOfModules.unit (structureSheafRing X)) :=
  derivedToOrdinaryPullbackSingle f (SheafOfModules.unit (structureSheafRing Y)) n ≫
    (DerivedCategory.singleFunctor _ n).map (modulePullbackObjUnitIso f).hom

/-- `derivedPullbackUnitComparison` is invertible: the structure sheaf placed in a single degree
is K-flat, so the derived pullback is computed by the degreewise one, and `f^*𝒪_Y ≅ 𝒪_X`. -/
instance isIso_derivedPullbackUnitComparison (n : ℤ) :
    IsIso (derivedPullbackUnitComparison f n) := by
  have h₂ : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor _ n).obj (SheafOfModules.unit (structureSheafRing Y)))) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.RingedSpace.kFlat_shiftedUnitComplex Y n)
  have h₁ : IsIso ((derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing Y)) n).hom.app
        (SheafOfModules.unit (structureSheafRing Y)))) :=
    ((derivedPullback f).mapIso ((DerivedCategory.singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing Y)) n).app
        (SheafOfModules.unit (structureSheafRing Y)))).isIso_hom
  have h₃ : IsIso (DerivedCategory.Qh.map (((modulePullback f).mapHomotopyCategorySingleFunctor
      n).hom.app (SheafOfModules.unit (structureSheafRing Y)))) :=
    (DerivedCategory.Qh.mapIso (((modulePullback f).mapHomotopyCategorySingleFunctor
      n).app (SheafOfModules.unit (structureSheafRing Y)))).isIso_hom
  have h₄ : IsIso ((DerivedCategory.singleFunctorIsoCompQh
      (SheafOfModules.{u} (structureSheafRing X)) n).inv.app
        ((modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y)))) := inferInstance
  have h₅ : IsIso ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X))
      n).map (modulePullbackObjUnitIso f).hom) := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂
      (@IsIso.comp_isIso _ _ _ _ _ _ _ h₃ h₄))) h₅

/-- The `f`-map `𝒪_Y ⟶ f_*𝒪_X` adjoint to `f^*𝒪_Y ≅ 𝒪_X`. -/
abbrev unitToPushforward :
    SheafOfModules.unit (structureSheafRing Y) ⟶
      (modulePushforward f).obj (SheafOfModules.unit (structureSheafRing X)) :=
  (modulePullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackObjUnitIso f).hom

/-- **The derived square of the pullback of a represented class.** For `t : 𝒪_Y[-n] ⟶ F[0]`, the
derived `f`-map of [Stacks, Tag 01F8] attached to the unit `F ⟶ f_*f^*F` after `t` is the one
attached to `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` followed by `Rf_*` of `𝒪_X[-n] ≅ Lf^*(𝒪_Y[-n]) ⟶ Lf^*(F[0]) ⟶
(f^*F)[0]`: both are transposes along `Lf^* ⊣ Rf_*`
(`Stacks.DeRham.GysinCohomologyBaseChange.derivedPushforwardMap_canonical_eq`). -/
theorem derivedPushforwardMap_square (F : SheafOfModules.{u} (structureSheafRing Y)) (n : ℕ)
    (t : (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y))
        (n : ℤ)).obj (SheafOfModules.unit (structureSheafRing Y)) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) (0 : ℤ)).obj F) :
    t ≫ derivedPushforwardMap (CohomologyPullbackComparison.canonical f) (0 : ℤ)
        ((modulePullbackPushforwardAdjunction f).unit.app F) =
      derivedPushforwardMap (CohomologyPullbackComparison.canonical f) (n : ℤ)
          (unitToPushforward f) ≫
        (derivedPushforward f).map (inv (derivedPullbackUnitComparison f n) ≫
          (derivedPullback f).map t ≫ derivedToOrdinaryPullbackSingle f F 0) := by
  rw [derivedPushforwardMap_canonical_eq, derivedPushforwardMap_canonical_eq,
    ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
  congr 1
  have h₁ : ((modulePullbackPushforwardAdjunction f).homEquiv F ((modulePullback f).obj F)).symm
      ((modulePullbackPushforwardAdjunction f).unit.app F) = 𝟙 _ := by
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_id]
  have h₂ : derivedToOrdinaryPullbackSingle f (SheafOfModules.unit (structureSheafRing Y)) n ≫
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) n).map
        (((modulePullbackPushforwardAdjunction f).homEquiv _ _).symm (unitToPushforward f)) =
      derivedPullbackUnitComparison f n := by
    rw [unitToPushforward, Equiv.symm_apply_apply]
    rfl
  rw [h₁, h₂, CategoryTheory.Functor.map_id, Category.comp_id, IsIso.hom_inv_id_assoc]

/-- The comparison `Lf^*(F[0]) ⟶ (f^*F)[0]` built from
`Stacks.Cohomology.GlobalKunneth.pullbackSingleComparison` is
`derivedToOrdinaryPullbackSingle` in degree `0`. -/
theorem pullbackSingleComparison_eq_derivedToOrdinaryPullbackSingle
    (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app F) ≫
        Stacks.Cohomology.GlobalKunneth.pullbackSingleComparison f F ≫
        (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app ((modulePullback f).obj F) =
      derivedToOrdinaryPullbackSingle f F 0 := by
  have h₁ := AlgebraicGeometry.FlatKunneth.pullbackSingleComparison_eq f F
  have hσY : (DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F ≫
      DerivedCategory.Qh.map ((HomotopyCategory.singleFunctorPostcompQuotientIso
        (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F) =
      (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app
          F ≫
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) :=
    ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id DerivedCategory.Qh _)).trans
      (Category.comp_id _)).trans
        ((Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app 0 F).trans
          (Category.id_comp _).symm)
  have hσX : DerivedCategory.Qh.map ((HomotopyCategory.singleFunctorPostcompQuotientIso
        (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app ((modulePullback f).obj F)) ≫
      (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app
        ((modulePullback f).obj F) =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            ((modulePullback f).obj F)) ≫
        (DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app ((modulePullback f).obj F) := by
    have hσ := (Iso.inv_eq_inv ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing X)) 0).app ((modulePullback f).obj F))
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app
        ((CochainComplex.singleFunctor _ 0).obj ((modulePullback f).obj F))).symm).2
      (Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app 0 _)
    exact ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id DerivedCategory.Qh _)).trans
      (Category.id_comp _)).trans (hσ.trans (Category.comp_id _).symm)
  have hhs : ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F) ≫
      ((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor _ 0).obj F) ≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
          (ComplexShape.up ℤ) 0).hom.app F) ≫
      (HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules.{u} (structureSheafRing X)) 0).inv.app ((modulePullback f).obj F) =
      ((modulePullback f).mapHomotopyCategorySingleFunctor 0).hom.app F := by
    have h0 : ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules.{u} (structureSheafRing Y)) 0).hom.app F) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [h0,
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapHomotopyCategorySingleFunctor_hom_app_eq]
    exact (Category.id_comp _).trans ((Category.id_comp _).trans (Category.comp_id _))
  have hν : (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans f).app
        ((CochainComplex.singleFunctor _ 0).obj F) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso _).inv.app
          ((CochainComplex.singleFunctor _ 0).obj F)) ≫
        (derivedPullbackComparison f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj F)) ≫
        DerivedCategory.Qh.map (((modulePullback f).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app ((CochainComplex.singleFunctor _ 0).obj F)) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f).obj
            ((CochainComplex.singleFunctor _ 0).obj F)) := by
    unfold Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rfl
  rw [h₁]
  refine Eq.trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)) ?_
  exact (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.singleComparison_eq_of_fac
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing Y)) 0)
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) 0)
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y)))
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X)))
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) 0)
    (DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) 0)
    (HomotopyCategory.singleFunctorPostcompQuotientIso
      (SheafOfModules.{u} (structureSheafRing Y)) 0).symm
    (HomotopyCategory.singleFunctorPostcompQuotientIso
      (SheafOfModules.{u} (structureSheafRing X)) 0).symm
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans f)
    (derivedPullbackComparison f)
    ((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    (HomologicalComplex.singleMapHomologicalComplex (modulePullback f) (ComplexShape.up ℤ) 0)
    ((modulePullback f).mapHomotopyCategorySingleFunctor 0) F hν hσY hσX hhs)

/-- `unitToPushforward` is Mathlib's `f^♯ : 𝒪_Y ⟶ f_*𝒪_X`. -/
theorem unitToPushforward_eq :
    unitToPushforward f = SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) :=
  Equiv.apply_symm_apply _ _

/-- On global sections, `f^♯` sends `1` to `1`. -/
theorem secF_map_unitToPushforward_apply :
    ((secF (structureSheafRing Y) ⊤).map (unitToPushforward f) ≫
        (pushforwardSectionsIso f).hom.app (SheafOfModules.unit (structureSheafRing X))).hom
      ((unitSection (X := Y)).eval (op ⊤)) = (unitSection (X := X)).eval (op ⊤) := by
  rw [unitToPushforward_eq]
  change (structureSheafHom f).hom.app (op ⊤) 1 = 1
  exact map_one _

/-- **The pullback of the class of `1` is the class of `1`**, whatever the placement degree. -/
theorem pullbackHgroup_unitToPushforward_sectionClass (a m : ℤ) (hn : m - a = (0 : ℕ)) :
    (pullbackHgroup (CohomologyPullbackComparison.canonical f) a m 0 hn
        (unitToPushforward f)).hom (sectionClass (unitSection (X := Y))) =
      sectionClass (unitSection (X := X)) := by
  rw [pullbackHgroup_canonical_eq]
  have key := ConcreteCategory.congr_hom
    (toRightDerivedZero_comp_pullbackHgroup f (unitToPushforward f))
    ((unitSection (X := Y)).eval (op ⊤))
  refine key.trans ?_
  exact congrArg ((secF (structureSheafRing X) ⊤).toRightDerivedZero.app _).hom
    (secF_map_unitToPushforward_apply f)

/-- `pullbackHgroup` does not see the spelling of its cohomological degree. -/
theorem pullbackHgroup_congr_degree {G : X ⟶ Y} (P : CohomologyPullbackComparison G)
    (a m m' : ℤ) (n : ℕ) (hn : m - a = n) (hn' : m' - a = n) (h : m = m')
    {M : RModules Y} {M' : RModules X} (φ : M ⟶ (modulePushforward G).obj M') :
    pullbackHgroup P a m n hn φ = pullbackHgroup P a m' n hn' φ := by
  subst h
  rfl

end PullbackComparison

section Pullback

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (derivedToOrdinaryPullbackSingle)
open Stacks.DeRham.GysinCohomologyBaseChange

variable {V V' : Scheme.{u}} (g : V' ⟶ V)

/-- **The comparison `𝒪_{V'}[-n] ⟶ Lg^*(𝒪_V[-n])`**: the inverse of the derived-to-ordinary
comparison `Lg^*(𝒪_V[-n]) ⟶ (g^*𝒪_V)[-n] ≅ 𝒪_{V'}[-n]`, which is invertible because the
structure sheaf placed in a single degree is K-flat. -/
def unitPullbackComparison (n : ℕ) :
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V'.toRingedSpace))
        (n : ℤ)).obj (unitModule V'.toRingedSpace) ⟶
      (derivedPullback g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
          (n : ℤ)).obj (unitModule V.toRingedSpace)) :=
  @inv _ _ _ _ (derivedPullbackUnitComparison g.toLRSHom.toShHom n)
    (isIso_derivedPullbackUnitComparison g.toLRSHom.toShHom n)

/-- `PullbackRepresented` holds at `unitPullbackComparison` for every comparison `cF` equal to
`derivedToOrdinaryPullbackSingle` in degree `0`. -/
theorem pullbackRepresented_of_eq (F : V.Modules) (n : ℕ)
    (cF : (derivedPullback g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V.toRingedSpace))
          ((0 : ℕ) : ℤ)).obj F) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V'.toRingedSpace))
          ((0 : ℕ) : ℤ)).obj ((Scheme.Modules.pullback g).obj F))
    (hcF : cF = derivedToOrdinaryPullbackSingle g.toLRSHom.toShHom F 0) :
    PullbackRepresented g F n (unitPullbackComparison g n) cF := by
  intro t
  rw [hcF]
  have hc := cohomologyMapOfSingleHom_pullbackHgroup
    (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) n 0
    (unitToPushforward g.toLRSHom.toShHom)
    ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app F) t _
    (derivedPushforwardMap_square g.toLRSHom.toShHom F n t)
  have h₁ := ConcreteCategory.congr_hom hc (sectionClass (unitSection (X := V.toRingedSpace)))
  have e : unitPullback g F (0 + n) =
      pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0
        (((0 : ℕ) : ℤ) + (n : ℤ)) (0 + n) (by omega)
        ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app F) :=
    pullbackHgroup_congr_degree _ _ _ _ _ _ _ (by push_cast; ring) _
  have h₂ : (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) (n : ℤ)
      (((0 : ℕ) : ℤ) + (n : ℤ)) 0 (by omega) (unitToPushforward g.toLRSHom.toShHom)).hom
        (sectionClass (unitSection (X := V.toRingedSpace))) =
      sectionClass (unitSection (X := V'.toRingedSpace)) :=
    pullbackHgroup_unitToPushforward_sectionClass g.toLRSHom.toShHom (n : ℤ)
      (((0 : ℕ) : ℤ) + (n : ℤ)) (by omega)
  rw [e]
  exact h₁.trans (congrArg (cohomologyMapOfSingleHom V'.toRingedSpace (unitModule V'.toRingedSpace)
    ((Scheme.Modules.pullback g).obj F) n 0 _).hom h₂)

/-- **The pullback of the class represented by `t : 𝒪_V[-n] ⟶ F[0]` is represented by its
derived pullback** `𝒪_{V'}[-n] ≅ Lg^*(𝒪_V[-n]) ⟶ Lg^*(F[0]) ⟶ (g^*F)[0]`, the last arrow being the
derived-to-ordinary comparison built from
`Stacks.Cohomology.GlobalKunneth.pullbackSingleComparison`. -/
theorem pullbackRepresented (F : V.Modules) (n : ℕ) :
    PullbackRepresented g F n (unitPullbackComparison g n)
      ((derivedPullback g.toLRSHom.toShHom).map
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app F) ≫
        Stacks.Cohomology.GlobalKunneth.pullbackSingleComparison g.toLRSHom.toShHom F ≫
        (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app ((Scheme.Modules.pullback g).obj F)) :=
  pullbackRepresented_of_eq g F n _
    (pullbackSingleComparison_eq_derivedToOrdinaryPullbackSingle g.toLRSHom.toShHom F)

end Pullback

end Stacks.WeilDeRham
