module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# Solutions of a glueing problem for locally given derived objects

In Situation 0DC9 — a category `B`, a functor `u : B ⥤ C` into a ringed site, objects `E_U` of
`D(O_{u(U)})` and isomorphisms `ρ_a : E_U|_{C/u(V)} ⟶ E_V` satisfying the cocycle condition — a
*solution* (Stacks, Section 0DC8) is a pair `(E, ρ_U)` where `E` is an object of `D(O_C)` and
`ρ_U : E|_{C/u(U)} ⟶ E_U` are isomorphisms such that `ρ_a ∘ ρ_U|_{C/u(V)} = ρ_V` for every arrow
`a : V ⟶ U` of `B`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedOverFunctor`: the restriction `E ↦ E|_{C/U}` from
  `D(O_C)` to `D(O_U)`, the exact functor of restriction to the slice applied to complexes.
* `AlgebraicGeometry.RingedSite.derivedOverFunctorMapIso`: the identification
  `(E|_{C/U})|_{C/V} = E|_{C/V}` along an arrow `V ⟶ U`.
* `AlgebraicGeometry.RingedSite.LocallyGiven.Solution`: a solution of the glueing problem.

## Implementation notes

The restriction `ρ_U|_{C/u(V)}` of the source is the restriction functor
`AlgebraicGeometry.RingedSite.derivedOverMap` of Situation 0DC9 applied to `ρ_U`, and the
identification of its source `(E|_{C/u(U)})|_{C/u(V)}` with `E|_{C/u(V)}` that the source leaves
implicit is `derivedOverFunctorMapIso`, the comparison of restrictions of sheaves of modules
`SheafOfModules.overFunctorMap` applied to complexes.

As for Stacks 0DCA, the ringed site is taken with its objects, arrows and sections in one
universe `u`, and the locally given objects with the additional module universe `0`, so that the
derived categories involved are those of sheaves of modules in the universe `u`.

## References

* [Stacks Project, Section 0DC8](https://stacks.math.columbia.edu/tag/0DC8)
* [Stacks Project, Tag 0DC9](https://stacks.math.columbia.edu/tag/0DC9)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u uB vB

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- Sheafification is available in any module universe containing the site. -/
local instance (priority := 100) solutionModuleSheafification.{uM, w, v}
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{w, uM}] [UnivLE.{v, uM}] : HasSheafify J AddCommGrpCat.{uM} :=
  hasSheafifyEssentiallySmallSite.{v, uM, w, uM + 1, uM} J _

/-- In the module universe, sheafification equivalences are the locally bijective maps. -/
local instance (priority := 100) solutionModuleLocallyBijective.{uM, w, v}
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{w, uM}] [UnivLE.{v, uM}] : J.WEqualsLocallyBijective AddCommGrpCat.{uM} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, uM, w, uM + 1, uM} J

/-- Restriction of sheaves of modules to a slice preserves finite limits: limits of sheaves of
modules are computed objectwise, and restriction reindexes objects. No product in the site is
needed. -/
theorem overFunctor_preservesFiniteLimits' {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (U : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} R U) := by
  refine ⟨fun K _ _ => ⟨fun {F} => ⟨fun {c} hc => ?_⟩⟩⟩
  exact ⟨isLimitOfReflects (SheafOfModules.forget (R.over U)) <|
    PresheafOfModules.evaluationJointlyReflectsLimits (hc := fun W => isLimitOfPreserves
      (SheafOfModules.evaluation R (Opposite.op ((Over.forget U).obj W.unop))) hc)⟩

/-- Restriction of sheaves of modules to a slice preserves finite colimits, being a left
adjoint on underlying abelian sheaves. No product in the site is needed. -/
theorem overFunctor_preservesFiniteColimits' {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (U : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} R U) :=
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.overFunctor.{u} R U) :=
    Stacks.SheafOfModules.overFunctor_preservesColimits.{u, u, u, u} R U
  PreservesColimitsOfSize.preservesFiniteColimits.{u} _

attribute [local instance] overFunctor_preservesFiniteLimits' overFunctor_preservesFiniteColimits'

/-- The restriction `E ↦ E|_{C/U}` of objects of `D(O_C)` to the slice at `U`: the exact functor
of restriction of sheaves of modules to the slice, applied to complexes. -/
def derivedOverFunctor (U : X.C) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      LocalDerivedCategory.{0} X U :=
  (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory

/-- `derivedOverFunctor` is induced by restriction of complexes. -/
def derivedOverFunctorFactors (U : X.C) :
    DerivedCategory.Q ⋙ derivedOverFunctor X U ≅
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    U).mapDerivedCategoryFactors

/-- **`(E|_{C/U})|_{C/V} = E|_{C/V}`** along an arrow `f : V ⟶ U` of the site: the comparison
`SheafOfModules.overFunctorMap` of restrictions of sheaves of modules, applied to complexes. -/
def derivedOverFunctorMapIso {U V : X.C} (f : V ⟶ U) :
    derivedOverFunctor X U ⋙ derivedOverMap.{0} X f ≅ derivedOverFunctor X V :=
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let Ff := SheafOfModules.overFunctor.{u} R U
  let Fg := SheafOfModules.overMap.{u} R f
  let Fh := SheafOfModules.overFunctor.{u} R V
  have := overMap_additive.{u} R f
  have := overMap_preservesFiniteLimits.{u} R f
  have := overMap_preservesFiniteColimits.{u} R f
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      ((Ff.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ Fg.mapDerivedCategory)
      (Ff.mapDerivedCategory ⋙ Fg.mapDerivedCategory) :=
    ⟨Functor.isoWhiskerRight Ff.mapDerivedCategoryFactors Fg.mapDerivedCategory⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (Fh.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) Fh.mapDerivedCategory :=
    ⟨Fh.mapDerivedCategoryFactors⟩
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    ((Ff.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ Fg.mapDerivedCategory)
    (Fh.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (Ff.mapDerivedCategory ⋙ Fg.mapDerivedCategory) Fh.mapDerivedCategory
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ Fg.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (SheafOfModules.overFunctorMap.{u} R f) _)
        DerivedCategory.Q)

namespace LocallyGiven

variable {X} (G : LocallyGiven.{0, u, u, u, uB, vB} X)

/-- **A solution of the glueing problem of Situation 0DC9** (Stacks, Section 0DC8): an object
`E` of `D(O_C)` together with isomorphisms `ρ_U : E|_{C/u(U)} ⟶ E_U` for the objects `U` of `B`,
such that `ρ_a ∘ ρ_U|_{C/u(V)} = ρ_V` for every arrow `a : V ⟶ U` of `B`, the source of
`ρ_U|_{C/u(V)}` being identified with `E|_{C/u(V)}` by `derivedOverFunctorMapIso`. -/
structure Solution where
  /-- The glued object `E` of `D(O_C)`. -/
  obj : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  /-- The identification `ρ_U : E|_{C/u(U)} ⟶ E_U`. -/
  iso : ∀ U : G.B, (derivedOverFunctor X (G.u.obj U)).obj obj ≅ G.obj U
  /-- The compatibility `ρ_a ∘ ρ_U|_{C/u(V)} = ρ_V`. -/
  comm : ∀ {V U : G.B} (a : V ⟶ U),
    (derivedOverFunctorMapIso X (G.u.map a)).inv.app obj ≫
        (derivedOverMap.{0} X (G.u.map a)).map (iso U).hom ≫ (G.rho a).hom = (iso V).hom

/-- An isomorphism of solutions is an isomorphism of the glued objects compatible with the
identifications `ρ_U`. -/
def Solution.IsCompatibleIso {S S' : G.Solution} (e : S.obj ≅ S'.obj) : Prop :=
  ∀ U : G.B, (derivedOverFunctor X (G.u.obj U)).map e.hom ≫ (S'.iso U).hom = (S.iso U).hom

end LocallyGiven

end AlgebraicGeometry.RingedSite
