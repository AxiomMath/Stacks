module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Locally given derived objects on a ringed site

Let `(𝒞, 𝒪_𝒞)` be a ringed site, `B` a category and `u : B ⥤ 𝒞` a functor. The situation of the
source consists of an object `E_U` of `D(𝒪_{u(U)})` for every object `U` of `B` and an isomorphism
`ρ_a : E_U|_{𝒞/u(V)} ⟶ E_V` for every arrow `a : V ⟶ U` of `B`, satisfying the cocycle condition
`ρ_{a ∘ b} = ρ_b ∘ ρ_a|_{𝒞/u(W)}`.

Restriction to a slice site is exact on sheaves of modules, so it acts on derived categories by
applying it to complexes; restricting in two steps agrees with restricting along the composite up
to the canonical comparison, which is the identity on sections. The cocycle condition is read
through this comparison.

## Main definitions

* `AlgebraicGeometry.RingedSite.LocalDerivedCategory`: the unbounded derived category of sheaves
  of modules on a slice site.
* `AlgebraicGeometry.RingedSite.derivedOverMap`: restriction `E ↦ E|_{𝒞/V}` along an arrow
  `V ⟶ U` of the site, on derived categories.
* `AlgebraicGeometry.RingedSite.derivedOverMapComp`: restricting in two steps is restricting
  along the composite.
* `AlgebraicGeometry.RingedSite.LocallyGiven`: the derived objects given locally, with their
  restriction isomorphisms satisfying the cocycle condition.

## Implementation notes

The two-step comparison is stated for arrows `f`, `g`, `h` with `g ≫ f = h`, so that the cocycle
condition is stated at `u.map (b ≫ a)` itself, with the equation `Functor.map_comp`.

The site objects, site morphisms, rings, indexing objects and indexing morphisms have independent
universes. The additional module universe `uM` is arbitrary; module sections lie in
`max u v uM`, so the ambient universe accommodates the site and sheafification without imposing a
size bound on the local derived objects. The two sheafification facts are proved by transport
from a small model of the site and are declared as local instances, since they are needed only to
elaborate the types below; `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`
proves the first of them under the single hypothesis `UnivLE.{max u v, uM}`, which is not the
form the statement below needs.

## References

* [Stacks Project, Tag 0DC9](https://stacks.math.columbia.edu/tag/0DC9)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.RingedSite

/-- Sheafification is available in any module universe containing the site. -/
local instance (priority := 100) moduleSheafification.{uM, u, v}
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{u, uM}] [UnivLE.{v, uM}] : HasSheafify J AddCommGrpCat.{uM} :=
  hasSheafifyEssentiallySmallSite.{v, uM, u, uM + 1, uM} J _

/-- In the module universe, sheafification equivalences are the locally bijective maps. -/
local instance (priority := 100) moduleLocallyBijective.{uM, u, v}
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{u, uM}] [UnivLE.{v, uM}] : J.WEqualsLocallyBijective AddCommGrpCat.{uM} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, uM, u, uM + 1, uM} J

/-- The unbounded derived category of sheaves of modules on the slice site at `U`,
with an arbitrary additional module universe `uM`. -/
abbrev LocalDerivedCategory.{uM, u, v, w} (X : RingedSite.{u, v, w}) (U : X.C) :=
  let A := SheafOfModules.{max u v uM} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
  let _ := HasDerivedCategory.standard A
  DerivedCategory A

section Restriction

/-- Restriction of sheaves of modules along an arrow of the site preserves finite limits:
limits of sheaves of modules are computed objectwise, and restriction reindexes objects. -/
theorem overMap_preservesFiniteLimits.{t, r, v', u'} {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : V ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap.{t} R f) := by
  refine ⟨fun K _ _ => ⟨fun {F} => ⟨fun {c} hc => ?_⟩⟩⟩
  exact ⟨isLimitOfReflects (SheafOfModules.forget (R.over V))
    (PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun W => isLimitOfPreserves
      (SheafOfModules.evaluation (R.over U) (Opposite.op ((Over.map f).obj W.unop))) hc)⟩

/-- Restriction of sheaves of modules along an arrow of the site is additive. -/
theorem overMap_additive.{t, r, v', u'} {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : V ⟶ U) :
    (SheafOfModules.overMap.{t} R f).Additive :=
  ⟨by intros; ext; rfl⟩

/-- Restriction of sheaves of modules along an arrow of the site preserves finite colimits. -/
theorem overMap_preservesFiniteColimits.{t, r, v', u'} {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : V ⟶ U)
    [HasWeakSheafify (J.over V) AddCommGrpCat.{t}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{t}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{t}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{t}] :
    PreservesFiniteColimits (SheafOfModules.overMap.{t} R f) :=
  have : PreservesColimitsOfSize.{t, t} (SheafOfModules.overMap.{t} R f) :=
    Stacks.SheafOfModules.overMap_preservesColimits R f
  PreservesColimitsOfSize.preservesFiniteColimits.{t} _

/-- Restricting sheaves of modules along `f : V ⟶ U` and then along `g : W ⟶ V` is restricting
along `g ≫ f`: the pushforward along `Over.map g ⋙ Over.map f` compared with the pushforward along
`Over.map (g ≫ f)` by `CategoryTheory.Over.mapComp`, which induces the identity on the sections of
the sheaf of rings. -/
def overMapCompIso.{t, r, v', u'} {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    SheafOfModules.overMap.{t} R f ⋙ SheafOfModules.overMap.{t} R g ≅
      SheafOfModules.overMap.{t} R (g ≫ f) := by
  have : (Over.map g ⋙ Over.map f).IsContinuous (J.over W) (J.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over V) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_
  refine SheafOfModules.pushforwardCongr₂ _ (Over.mapComp g f) ?_
  ext A : 3
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have h : ((Functor.sheafPushforwardContinuousNatTrans (Over.mapComp g f).hom RingCat.{r}
      (J.over W) (J.over U)).app (R.over U)).hom.app A = 𝟙 _ := by
    simp
    rfl
  rw [h]
  rfl

/-- Restriction `E ↦ E|_{𝒞/V}` along an arrow `f : V ⟶ U` of the site, on the derived categories
of modules of the slice sites: the exact functor of restriction applied to complexes. -/
def derivedOverMap.{uM, u, v, w} (X : RingedSite.{u, v, w}) {U V : X.C} (f : V ⟶ U) :
    LocalDerivedCategory.{uM} X U ⥤ LocalDerivedCategory.{uM} X V :=
  let _ := HasDerivedCategory.standard (SheafOfModules.{max u v uM}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
  let _ := HasDerivedCategory.standard (SheafOfModules.{max u v uM}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
  have := overMap_additive.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  have := overMap_preservesFiniteLimits.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  have := overMap_preservesFiniteColimits.{max u v uM}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  (SheafOfModules.overMap.{max u v uM}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapDerivedCategory

/-- Restricting along `f : V ⟶ U` and then along `g : W ⟶ V` is restricting along the composite
`h = g ≫ f`, on sheaves of modules: the canonical comparison, the identity on sections. -/
def overMapCompIsoOfEq.{uM, u, v, w} (X : RingedSite.{u, v, w}) {U V W : X.C}
    {f : V ⟶ U} {g : W ⟶ V} {h : W ⟶ U} (e : g ≫ f = h) :
    SheafOfModules.overMap.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f ⋙
        SheafOfModules.overMap.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g ≅
      SheafOfModules.overMap.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h := by
  subst e
  exact overMapCompIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f g

/-- Restricting along `f : V ⟶ U` and then along `g : W ⟶ V` is restricting along the composite
`h = g ≫ f`, on derived categories: the comparison of sheaves of modules applied to complexes. -/
def derivedOverMapComp.{uM, u, v, w} (X : RingedSite.{u, v, w}) {U V W : X.C}
    {f : V ⟶ U} {g : W ⟶ V} {h : W ⟶ U} (e : g ≫ f = h) :
    derivedOverMap.{uM} X h ≅ derivedOverMap.{uM} X f ⋙ derivedOverMap.{uM} X g :=
  let _ := HasDerivedCategory.standard (SheafOfModules.{max u v uM}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
  let _ := HasDerivedCategory.standard (SheafOfModules.{max u v uM}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
  let _ := HasDerivedCategory.standard (SheafOfModules.{max u v uM}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))
  let Ff := SheafOfModules.overMap.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  let Fg := SheafOfModules.overMap.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
  let Fh := SheafOfModules.overMap.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h
  have := overMap_additive.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  have := overMap_preservesFiniteLimits.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  have := overMap_preservesFiniteColimits.{max u v uM}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  have := overMap_additive.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
  have := overMap_preservesFiniteLimits.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
  have := overMap_preservesFiniteColimits.{max u v uM}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
  have := overMap_additive.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h
  have := overMap_preservesFiniteLimits.{max u v uM} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h
  have := overMap_preservesFiniteColimits.{max u v uM}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      ((Ff.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ Fg.mapDerivedCategory)
      (Ff.mapDerivedCategory ⋙ Fg.mapDerivedCategory) :=
    ⟨Functor.isoWhiskerRight Ff.mapDerivedCategoryFactors Fg.mapDerivedCategory⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (Fh.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) Fh.mapDerivedCategory :=
    ⟨Fh.mapDerivedCategoryFactors⟩
  (Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    ((Ff.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ Fg.mapDerivedCategory)
    (Fh.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (Ff.mapDerivedCategory ⋙ Fg.mapDerivedCategory) Fh.mapDerivedCategory
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ Fg.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (overMapCompIsoOfEq.{uM} X e) _)
        DerivedCategory.Q)).symm

end Restriction

/-- Derived objects given locally on a category mapping to a ringed site, with isomorphisms on
restriction satisfying the cocycle condition: a category `B` with a functor `u : B ⥤ 𝒞`, an object
`E_U` of `D(𝒪_{u(U)})` for every object `U` of `B`, and an isomorphism
`ρ_a : E_U|_{𝒞/u(V)} ⟶ E_V` for every arrow `a : V ⟶ U` of `B`, such that
`ρ_{a ∘ b} = ρ_b ∘ ρ_a|_{𝒞/u(W)}` for composable arrows `b : W ⟶ V` and `a : V ⟶ U`. -/
@[stacks 0DC9]
structure LocallyGiven.{uM, u, v, w, uB, vB} (X : RingedSite.{u, v, w}) where
  /-- The indexing category. -/
  B : Type uB
  [category : Category.{vB} B]
  /-- The functor choosing an object of the site for each index. -/
  u : B ⥤ X.C
  /-- The derived object `E_U` given at each index. -/
  obj : ∀ U : B, LocalDerivedCategory.{uM} X (u.obj U)
  /-- The isomorphism `ρ_a : E_U|_{𝒞/u(V)} ⟶ E_V` given for each arrow `a : V ⟶ U`. -/
  rho : ∀ {V U : B} (a : V ⟶ U), (derivedOverMap.{uM} X (u.map a)).obj (obj U) ≅ obj V
  /-- The cocycle condition `ρ_{a ∘ b} = ρ_b ∘ ρ_a|_{𝒞/u(W)}`. -/
  cocycle : ∀ {W V U : B} (b : W ⟶ V) (a : V ⟶ U),
    (rho (b ≫ a)).hom =
      (derivedOverMapComp.{uM} X (u.map_comp b a).symm).hom.app (obj U) ≫
        (derivedOverMap.{uM} X (u.map b)).map (rho a).hom ≫ (rho b).hom

attribute [instance] LocallyGiven.category

end AlgebraicGeometry.RingedSite

end
