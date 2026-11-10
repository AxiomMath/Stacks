module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatExtendScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleRestrictUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.AlgebraPushoutAnyUniverseInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartComparisonTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp

/-!
# The module pullback and the algebra pullback agree on chart sections

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `A` be a sheaf of commutative `𝒪_X`-algebras on the small étale site of `X`.
`AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso` identifies the
`𝒪_Y`-module underlying `f^*A` with the module pullback of the `𝒪_X`-module underlying `A`, but
says nothing about what that identification *does*; and the one thing a consumer of the
sections half of Stacks 03GA for algebra sheaves needs is its value on a chart section.

This file supplies an identification whose value on a chart section is the content, by building
it as an adjunct rather than by reading an existing one.  The comparison
`AlgebraicGeometry.Space.algebraPullbackModuleComparison` is, by definition, the morphism
`f^*M ⟶ f^*A` of `𝒪_Y`-modules adjunct across the Stacks 03D7 adjunction to the composite of
the unit of Stacks 03D3 with the leg `pushout.inl` of the pushout defining `f^*A`; so its value
on the chart section of Stacks 03D7 is the chart projection of that composite, which is exactly
`AlgebraicGeometry.Space.algebraPullbackChartSection`.  That it is an *isomorphism* is then
corepresentability: composition with it is a chain of four bijections ending in
`Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.bijective_pushoutInlModuleMap_comp`.

## Main definitions

* `AlgebraicGeometry.Space.algebraPullbackModuleTranspose`: the morphism of `𝒪_X`-modules from
  the module underlying `A` to the direct image of the module underlying `f^*A` adjunct to
  `pushout.inl`.
* `AlgebraicGeometry.Space.algebraPullbackModuleComparison`: **the comparison**
  `f^*M ⟶ f^*A`, its adjunct across Stacks 03D7, and
  `AlgebraicGeometry.Space.algebraPullbackModuleIso`, the same as an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_algebraPullbackModuleComparison`: **the comparison is an
  isomorphism.**
* `AlgebraicGeometry.Space.algebraPullbackModuleComparison_modulePullbackChartSection`: **the
  comparison carries the module chart section to the algebra chart section.**
* `AlgebraicGeometry.Space.bijective_algebraPullbackChartComparison_affine`: **the sections half
  of Stacks 03GA for algebra sheaves** — over a diagram of affine étale charts the canonical
  `𝒪_Y(d.U)`-algebra homomorphism `𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V) ⟶ (f^*A)(d.U)` is bijective for
  every quasi-coherent `A`.

## Implementation notes

**Why a new comparison rather than the existing isomorphism.**
`AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso` is built from
`Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison_anySite`, which is a transpose across
`Stacks.FlatChangeOfRings.extendScalarsAdjunction` — an adjunction assembled from a
`Classical.choice` of the presheaf-level change-of-rings adjunction, so the unit of that
adjunction has no description on sections and the transpose cannot be evaluated there.  The
adjunction the modules development of Stacks 03D7 is built from,
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`, does have one.  Rather
than bridge the two, the comparison below is taken to be the adjunct across Stacks 03D7
itself: it is then characterised by the one equation a chart computation needs, and
invertibility is re-derived from
`Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.bijective_pushoutInlModuleMap_comp`, which
is a statement about `pushout.inl` and mentions no adjunction at all.

**The identifications of spelling that this crosses**, each isolated in its own declaration and
each holding by `Eq.refl`:

* `AlgebraicGeometry.Space.moduleSetSheaf_underlyingModule`: the sheaf of sets underlying the
  `𝒪_X`-module underlying `A` is the sheaf of sets underlying `A`.  Forgetting from
  `CommRingCat` to `Type` directly and forgetting through `RingCat` and `AddCommGrpCat` agree,
  which is the coincidence the implementation notes of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackModuleRestrictUnit.lean` record for the
  `RingCat` hop.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_inverseImageToAlgebraPullbackModule`: the
  composite of `Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitIso` with the
  semilinear form
  of `pushout.inl` is, on underlying sheaves of sets, `pushout.inl` itself — the first factor
  being the identity there by construction and the second being
  `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.moduleMapOver`, whose action on sections is
  the action of the given morphism of sheaves of rings by `rfl`.

**The two unit computations** are quoted and not redone:
`moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app` in
`Stacks.Sheaves.RingedToposModules` for the module side and
`Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_unit_app` for the ring side.
Both say the same thing — that the unit in question is the unit of `f⁻¹ ⊣ f_*` on sheaves of
sets — and it is their agreement, `AlgebraicGeometry.Space.inverseImageUnit_val_app`, that makes
the module chart section and the ring chart section the same section.

**Every statement about a section is taken at an abstract object of the site** where the chart
diagram is not involved, and instantiated at `op d.V` afterwards; the chart argument is a cost
variable, and a reading proved at `op d.V` from the outset is much more expensive to elaborate than
the same reading proved at an abstract `W` and then instantiated.

**Two further observations, both about where an elaboration is given an expected type.** The
inverse-image sheaf of rings in the statement of
`AlgebraicGeometry.Space.moduleSheafFunctor_map_inverseImageToAlgebraPullbackModule` carries its
universe arguments explicitly: `Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf` has six of
them and none is fixed by the surrounding `CategoryTheory.Sheaf.moduleSheafFunctor`, whose own
module universe is itself free, so left implicit the module universe defaults to `0` and the
statement is about a sheaf of rings at the wrong universe.  This is the spelling
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackChartSection.lean` already uses.
And in `AlgebraicGeometry.Space.val_app_modulePullbackChartSection` the reading of the adjunct
on a section is left with *no* type ascription: writing out the right-hand side as two successive
section applications rather than the one application of a composite asks `isDefEq` to open
`modulePushforward` under a chart projection, which exhausts the deterministic budget — the
budget is not raised, the ascription is dropped, exactly as in
`AlgebraicGeometry.Space.modulePullbackChartSection_map`, which this proof otherwise mirrors.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TensorProduct
open Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.AlgebraPushoutAnyUniverse

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The chart value of a morphism out of a module pullback -/

/-- **The value over the chart of `Y` of a morphism out of a module pullback, on a chart
section, is the chart projection of the adjunct of that morphism.**

The chart section is the unit of Stacks 03D7 followed by the chart projection
`AlgebraicGeometry.Space.moduleChartProjection`, which is a natural transformation of functors
of sheaves of *sets*; so the morphism passes through it, and the unit followed by the direct
image of the morphism is the adjunct, which is
`CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem val_app_modulePullbackChartSection (f : Y ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (ψ : (modulePullback B S hS f).obj M ⟶ N)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) (s : M.val.obj (op d.V)) :
    ψ.val.app (op d.U) (modulePullbackChartSection B S hS f M d s) =
      (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
          (moduleSetSheaf B S hS Y N)
        ((((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).homEquiv
            M N) ψ).val.app (op d.V) s) := by
  have hu := congrArg
    (fun m : M ⟶ (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj N ↦
      m.val.app (op d.V) s)
    ((pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).homEquiv_unit M N ψ)
  refine Eq.trans (Functor.natTrans_app_map_apply
    (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d))
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map ψ)
    (((pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS f)).unit.app M).val.app (op d.V) s)).symm ?_
  exact congrArg
    ((moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
      (moduleSetSheaf B S hS Y N)) hu.symm

/-! ### The inverse image of an algebra sheaf, read through `Under` -/

/-- The inverse image of `A` as a sheaf of commutative `f⁻¹𝒪_X`-algebras, in the shape
`CategoryTheory.Under` that `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse` takes an algebra
sheaf in. -/
def algebraPullbackUnder (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    Under ((ringSheafPullback B S hS f).obj (structureSheaf B S hS X.1 X.2)) :=
  Under.mk ((ringSheafPullback B S hS f).map A.hom)

/-- Small products of presheaves of types (instance search times out without this shortcut). -/
local instance (priority := high)
    hasLimitsOfShape_discrete_presheaf_AlgebraPullbackChartSectionModule
    {C : Type*} [Category.{u} C] (J : Type u) :
    HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u) :=
  @functorCategoryHasLimitsOfShape _ _ _ _ _ _ inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the module categories of the small étale ringed topos is deep
set_option maxHeartbeats 1000000 in
-- elaborating the universe-polymorphic pullback isomorphism at these instances is slow
/-- **The identification of the inverse image of the `𝒪_X`-module underlying `A` with the
`f⁻¹𝒪_X`-module underlying `f⁻¹A`.**  This is
`Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitIso`, which is the identity on the
common underlying sheaf of sets, with its type written in the spelling of the small étale site. -/
def inverseImageUnderlyingModuleIso (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (structureRingSheaf B S hS X)).obj (AlgebraSheaf.underlyingModule A) ≅
      underlyingModule.{u, u, u + 1} (algebraPullbackUnder B S hS f A) :=
  haveI : PreservesFiniteLimits (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage :=
    (smallEtaleRingedToposHom B S hS f).toToposHom.preservesFiniteLimits
  Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitIso.{u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage A.hom

/-- The leg `pushout.inl` of the pushout which defines `f^*A`, read as a morphism of
`f⁻¹𝒪_X`-modules from the module underlying `f⁻¹A` to the module underlying `f^*A`. -/
def algebraPullbackInlModuleMap (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    underlyingModule.{u, u, u + 1} (algebraPullbackUnder B S hS f A) ⟶
      (SheafOfModules.restrictScalars
          (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).obj
        (AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A)) :=
  pushoutInlModuleMap.{u, u, u + 1} (structurePullbackMap B S hS f)
    (algebraPullbackUnder B S hS f A)

/-- The composite of the two: the morphism of `f⁻¹𝒪_X`-modules from the inverse image of the
module underlying `A` to the module underlying `f^*A`, read over `f⁻¹𝒪_X`. -/
def inverseImageToAlgebraPullbackModule (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (structureRingSheaf B S hS X)).obj (AlgebraSheaf.underlyingModule A) ⟶
      (SheafOfModules.restrictScalars
          (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).obj
        (AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A)) :=
  (inverseImageUnderlyingModuleIso B S hS f A).hom ≫ algebraPullbackInlModuleMap B S hS f A

/-! ### The comparison -/

/-- **The chart-section transpose.**  The morphism of `𝒪_X`-modules from the module underlying
`A` to the direct image of the module underlying `f^*A` adjunct, across the Stacks 03D3
adjunction for the inverse image of modules, to
`AlgebraicGeometry.Space.inverseImageToAlgebraPullbackModule`. -/
def algebraPullbackModuleTranspose (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    AlgebraSheaf.underlyingModule A ⟶
      (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj
        (AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A)) :=
  (inverseImageAdjDirectImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS X)).homEquiv _ _
    (inverseImageToAlgebraPullbackModule B S hS f A)

/-- **The canonical comparison of the module pullback of the module underlying `A` with the
`𝒪_Y`-module underlying the algebra pullback `f^*A`**: the morphism adjunct, across the
Stacks 03D7 adjunction, to `AlgebraicGeometry.Space.algebraPullbackModuleTranspose`. -/
def algebraPullbackModuleComparison (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS f).obj (AlgebraSheaf.underlyingModule A) ⟶
      AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A) :=
  ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).homEquiv _ _).symm
    (algebraPullbackModuleTranspose B S hS f A)

/-- The transpose across Stacks 03D7 of the comparison is the chart-section transpose. -/
theorem homEquiv_algebraPullbackModuleComparison (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).homEquiv
        (AlgebraSheaf.underlyingModule A)
        (AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A)))
      (algebraPullbackModuleComparison B S hS f A) =
      algebraPullbackModuleTranspose B S hS f A :=
  Equiv.apply_symm_apply _ _

/-! ### Invertibility of the comparison -/

/-- Precomposition with an isomorphism is a bijection on the morphisms out of it. -/
theorem bijective_iso_hom_comp {C₀ : Type*} [Category C₀] {P Q : C₀} (e : P ≅ Q) (T : C₀) :
    Function.Bijective (fun w : Q ⟶ T ↦ e.hom ≫ w) :=
  ⟨fun _ _ h ↦ (cancel_epi e.hom).mp h, fun u ↦ ⟨e.inv ≫ u, Iso.hom_inv_id_assoc e u⟩⟩

/-- **Composition with the comparison is the chain of four bijections.**  Reading a morphism out
of the module underlying `f^*A` as a morphism out of the module pullback is: restricting it
along `f♯ : f⁻¹𝒪_X ⟶ 𝒪_Y` and composing with `pushout.inl`; composing with the identification of
the inverse image of the module underlying `A` with the module underlying `f⁻¹A`; transposing
across Stacks 03D3; and transposing back across Stacks 03D7.  Each of the two transposes is
natural in the morphism, which is what turns the chain into composition with the comparison. -/
theorem comp_algebraPullbackModuleComparison (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (T : Modules.{u, u} B S hS Y.1 Y.2)
    (v : AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A) ⟶ T) :
    algebraPullbackModuleComparison B S hS f A ≫ v =
      ((pullbackAdjPushforwardModules
            (smallEtaleRingedToposModulesHom B S hS f)).homEquiv _ _).symm
        ((inverseImageAdjDirectImageModules
              (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS X)).homEquiv _ _
          ((inverseImageUnderlyingModuleIso B S hS f A).hom ≫
            (algebraPullbackInlModuleMap B S hS f A ≫
              (SheafOfModules.restrictScalars
                (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map v))) := by
  have hassoc : (inverseImageUnderlyingModuleIso B S hS f A).hom ≫
        (algebraPullbackInlModuleMap B S hS f A ≫
          (SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map v) =
      inverseImageToAlgebraPullbackModule B S hS f A ≫
        (SheafOfModules.restrictScalars
          (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map v :=
    (Category.assoc _ _ _).symm
  have h₁ : (inverseImageAdjDirectImageModules
          (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (structureRingSheaf B S hS X)).homEquiv _ _
        (inverseImageToAlgebraPullbackModule B S hS f A ≫
          (SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map v) =
      algebraPullbackModuleTranspose B S hS f A ≫
        (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).map v :=
    (inverseImageAdjDirectImageModules
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS X)).homEquiv_naturality_right
      (inverseImageToAlgebraPullbackModule B S hS f A)
      ((SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map v)
  refine Eq.trans ?_ (congrArg
    (fun w ↦ ((pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS f)).homEquiv _ _).symm
      ((inverseImageAdjDirectImageModules
          (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (structureRingSheaf B S hS X)).homEquiv _ _ w)) hassoc).symm
  refine Eq.trans ?_ (congrArg
    (fun w ↦ ((pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).homEquiv _ _).symm w) h₁).symm
  exact ((pullbackAdjPushforwardModules
    (smallEtaleRingedToposModulesHom B S hS f)).homEquiv_naturality_right_symm
      (algebraPullbackModuleTranspose B S hS f A) v).symm

/-- **The comparison is an isomorphism.**  Composition with it is bijective for every target, by
`AlgebraicGeometry.Space.comp_algebraPullbackModuleComparison` and the bijectivity of its four
factors: composition with `pushout.inl` is
`Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.bijective_pushoutInlModuleMap_comp`, composition
with the identification of the inverse images is composition with an isomorphism, and the two
transposes are bijections by construction. -/
theorem isIso_algebraPullbackModuleComparison (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    IsIso (algebraPullbackModuleComparison B S hS f A) := by
  refine isIso_of_coyoneda_map_bijective _ fun T ↦ ?_
  have key : (fun v : AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A) ⟶ T ↦
        algebraPullbackModuleComparison B S hS f A ≫ v) =
      (fun w ↦ ((pullbackAdjPushforwardModules
            (smallEtaleRingedToposModulesHom B S hS f)).homEquiv _ _).symm w) ∘
        (fun w ↦ (inverseImageAdjDirectImageModules
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS X)).homEquiv _ _ w) ∘
        (fun w ↦ (inverseImageUnderlyingModuleIso B S hS f A).hom ≫ w) ∘
        (fun v : AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A) ⟶ T ↦
          algebraPullbackInlModuleMap B S hS f A ≫
            (SheafOfModules.restrictScalars
              (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map v) :=
    funext fun v ↦ comp_algebraPullbackModuleComparison B S hS f A T v
  rw [key]
  refine Function.Bijective.comp
    ((pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).homEquiv _ _).symm.bijective ?_
  refine Function.Bijective.comp
    ((inverseImageAdjDirectImageModules
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS X)).homEquiv _ _).bijective ?_
  exact (bijective_iso_hom_comp (inverseImageUnderlyingModuleIso B S hS f A) _).comp
    (bijective_pushoutInlModuleMap_comp.{u, u, u + 1} (structurePullbackMap B S hS f)
      (algebraPullbackUnder B S hS f A) T)

/-- **The comparison, as an isomorphism** of the module pullback of the `𝒪_X`-module underlying
`A` with the `𝒪_Y`-module underlying the algebra pullback `f^*A`. -/
def algebraPullbackModuleIso (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS f).obj (AlgebraSheaf.underlyingModule A) ≅
      AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A) :=
  have := isIso_algebraPullbackModuleComparison B S hS f A
  asIso (algebraPullbackModuleComparison B S hS f A)

/-! ### The identifications of spelling -/

/-- The sheaf of sets underlying the `𝒪_X`-module underlying an algebra sheaf is the sheaf of
sets underlying the algebra sheaf: the module is the algebra's own sections with the scalar
action induced by the structure-algebra maps, so the two differ only in how `Type` is reached
from `CommRingCat`. -/
theorem moduleSetSheaf_underlyingModule (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    moduleSetSheaf B S hS X (AlgebraSheaf.underlyingModule A) =
      commRingSetSheaf B S hS X A.right :=
  rfl

/-- **The composite of the identification of the inverse images with the semilinear form of
`pushout.inl` is, on underlying sheaves of sets, the leg `pushout.inl` itself.**  The first
factor is the identity on the common underlying sheaf of sets by construction, and the second is
the map on sections of `pushout.inl` by
`Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.moduleMapOver`, whose action on sections is
  the action of the given morphism of sheaves of rings by `rfl`. -/
theorem moduleSheafFunctor_map_inverseImageToAlgebraPullbackModule (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS X))).map
        (inverseImageToAlgebraPullbackModule B S hS f A) =
      commRingSetSheafMap B S hS Y ((algebraPullbackMap B S hS f).app A) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-! ### The two units agree -/

/-- Equal morphisms of sheaves of sets have equal components on a section. -/
private theorem hom_app_apply_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type u)} {m m' : F ⟶ G} (h : m = m') (W : Cᵒᵖ) (a : F.obj.obj W) :
    m.hom.app W a = m'.hom.app W a :=
  h ▸ rfl

/-- **The unit of the Stacks 03D3 adjunction for modules and the unit of the Stacks 00YV
adjunction for commutative rings are the same section.**  Both are the unit of `f⁻¹ ⊣ f_*` on
the common underlying sheaf of sets, by
`moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app` in
`Stacks.Sheaves.RingedToposModules` and
`Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_unit_app`.

Stated at an abstract object of the small étale site of `X`: the chart diagram is a cost
variable and nothing here needs it. -/
theorem inverseImageUnit_val_app (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (W : (SmallEtale B S hS X.1)ᵒᵖ) (a : A.right.obj.obj W) :
    (((inverseImageAdjDirectImageModules
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS X)).unit.app
          (AlgebraSheaf.underlyingModule A)).val.app W) a =
      ((((ringSheafPullbackAdjunction B S hS f).unit.app A.right).hom.app W).hom) a := by
  exact (hom_app_apply_congr
    (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS X) (AlgebraSheaf.underlyingModule A)) W a).trans
    (hom_app_apply_congr
      (Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_unit_app
        (smallEtaleRingedToposHom B S hS f).toToposHom A.right) W a).symm

/-! ### The chart-section transpose, read on sections -/

/-- **The chart-section transpose, on a section over an abstract object of the small étale site
of `X`**: the unit of Stacks 00YV for commutative rings, followed by the direct image of the leg
`pushout.inl`.

The transpose is the unit of Stacks 03D3 followed by the direct image of
`AlgebraicGeometry.Space.inverseImageToAlgebraPullbackModule`, by
`CategoryTheory.Adjunction.homEquiv_unit`; the unit is the unit of Stacks 00YV by
`AlgebraicGeometry.Space.inverseImageUnit_val_app`, and the morphism is `pushout.inl` on
underlying sheaves of sets by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_inverseImageToAlgebraPullbackModule`. -/
theorem algebraPullbackModuleTranspose_val_app (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : A.right.obj.obj W) :
    (algebraPullbackModuleTranspose B S hS f A).val.app W a =
      ((smallEtaleDirectImage B S hS f).map
          (commRingSetSheafMap B S hS Y ((algebraPullbackMap B S hS f).app A))).hom.app W
        ((((ringSheafPullbackAdjunction B S hS f).unit.app A.right).hom.app W).hom a) := by
  have h₁ : (algebraPullbackModuleTranspose B S hS f A).val.app W a =
      ((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS X)).map
          (inverseImageToAlgebraPullbackModule B S hS f A)).val.app W
        (((inverseImageAdjDirectImageModules
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS X)).unit.app
          (AlgebraSheaf.underlyingModule A)).val.app W a) :=
    congrArg
      (fun m : AlgebraSheaf.underlyingModule A ⟶
          (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj
            (AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A)) ↦
        m.val.app W a)
      ((inverseImageAdjDirectImageModules
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (structureRingSheaf B S hS X)).homEquiv_unit _ _
        (inverseImageToAlgebraPullbackModule B S hS f A))
  refine h₁.trans ?_
  refine Eq.trans (congrArg
    (fun y ↦ ((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (structureRingSheaf B S hS X)).map
        (inverseImageToAlgebraPullbackModule B S hS f A)).val.app W y)
    (inverseImageUnit_val_app B S hS f A W a)) ?_
  refine Eq.trans (hom_app_apply_congr
    (moduleSheafFunctor_map_directImageModules_map
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS X)
      (inverseImageToAlgebraPullbackModule B S hS f A)) W _) ?_
  exact congrArg
    (fun k : commRingSetSheaf B S hS Y ((ringSheafPullback B S hS f).obj A.right) ⟶
        commRingSetSheaf B S hS Y ((algebraPullback B S hS f).obj A).right ↦
      ((smallEtaleDirectImage B S hS f).map k).hom.app W
        ((((ringSheafPullbackAdjunction B S hS f).unit.app A.right).hom.app W).hom a))
    (moduleSheafFunctor_map_inverseImageToAlgebraPullbackModule B S hS f A)

/-! ### The algebra chart section through the module side -/

/-- **The algebra chart section is the chart projection of the unit of Stacks 00YV followed by
the direct image of `pushout.inl`.**  This is the definition of
`AlgebraicGeometry.Space.algebraPullbackChartSection` — the unit of Stacks 00YV, the chart
projection, then `pushout.inl` — with the chart projection moved past `pushout.inl` by its
naturality in the sheaf of sets. -/
theorem algebraPullbackChartSection_eq (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (a : A.right.obj.obj (op d.V)) :
    algebraPullbackChartSection B S hS f A d a =
      (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
          (commRingSetSheaf B S hS Y ((algebraPullback B S hS f).obj A).right)
        (((smallEtaleDirectImage B S hS f).map
            (commRingSetSheafMap B S hS Y ((algebraPullbackMap B S hS f).app A))).hom.app
          (op d.V)
          ((((ringSheafPullbackAdjunction B S hS f).unit.app A.right).hom.app (op d.V)).hom
            a)) :=
  (Functor.natTrans_app_map_apply
    (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d))
    (commRingSetSheafMap B S hS Y ((algebraPullbackMap B S hS f).app A))
    ((((ringSheafPullbackAdjunction B S hS f).unit.app A.right).hom.app (op d.V)).hom a)).symm

/-- **The comparison carries the module chart section to the algebra chart section.**  This is
the identification the sections half of Stacks 03GA for algebra sheaves was missing.

By `AlgebraicGeometry.Space.val_app_modulePullbackChartSection` the left-hand side is the chart
projection of the transpose of the comparison, which is
`AlgebraicGeometry.Space.algebraPullbackModuleTranspose` by construction; on sections that
transpose is the unit of Stacks 00YV followed by the direct image of `pushout.inl`
(`AlgebraicGeometry.Space.algebraPullbackModuleTranspose_val_app`), and the chart projection of
*that* is the algebra chart section
(`AlgebraicGeometry.Space.algebraPullbackChartSection_eq`). -/
theorem algebraPullbackModuleComparison_modulePullbackChartSection (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (a : A.right.obj.obj (op d.V)) :
    (algebraPullbackModuleComparison B S hS f A).val.app (op d.U)
        (modulePullbackChartSection B S hS f (AlgebraSheaf.underlyingModule A) d a) =
      algebraPullbackChartSection B S hS f A d a := by
  refine Eq.trans (val_app_modulePullbackChartSection B S hS f
    (AlgebraSheaf.underlyingModule A)
    (AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A))
    (algebraPullbackModuleComparison B S hS f A) d a) ?_
  refine Eq.trans (congrArg
    (fun y ↦ (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
      (commRingSetSheaf B S hS Y ((algebraPullback B S hS f).obj A).right) y)
    ((congrArg
        (fun m : AlgebraSheaf.underlyingModule A ⟶
            (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj
              (AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A)) ↦
          m.val.app (op d.V) a)
        (homEquiv_algebraPullbackModuleComparison B S hS f A)).trans
      (algebraPullbackModuleTranspose_val_app B S hS f A (op d.V) a))) ?_
  exact (algebraPullbackChartSection_eq B S hS f A d a).symm

/-! ### The sections half of Stacks 03GA for algebra sheaves -/

/-- **The sections half of [Stacks, Tag 03GA] for algebra sheaves.**  Over a diagram of affine
étale charts over an arbitrary morphism `f : Y ⟶ X` of algebraic spaces, the canonical
`𝒪_Y(d.U)`-algebra homomorphism

`𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V) ⟶ (f^*A)(d.U)`

is bijective for every quasi-coherent sheaf of commutative `𝒪_X`-algebras `A`.

Nothing is assumed beyond quasi-coherence of `A` and affineness of the two charts.  The algebra
comparison is the module comparison of Stacks 083K read through
`AlgebraicGeometry.Space.algebraPullbackModuleIso`, by
`AlgebraicGeometry.Space.algebraPullbackModuleComparison_modulePullbackChartSection`, and the
module comparison is bijective by
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`.

**No `@[stacks 03GA]` attribute is placed here.**  Tag 03GA is registered on the module
statements of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackQuasicoherentFromChartDiagrams.lean`; this
is the sections form for algebra sheaves, read off through an identification, and not a second
proof of the tag. -/
theorem bijective_algebraPullbackChartComparison_affine (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    letI := chartSectionsAlgebra A d.V
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
    Function.Bijective (algebraPullbackChartComparison B S hS f A d) :=
  bijective_algebraPullbackChartComparison_of_iso B S hS f A hA d hU hV
    (algebraPullbackModuleIso B S hS f A)
    fun a ↦ algebraPullbackModuleComparison_modulePullbackChartSection B S hS f A d a

end AlgebraicGeometry.Space

end
