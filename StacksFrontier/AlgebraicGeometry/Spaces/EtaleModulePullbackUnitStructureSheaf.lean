module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpUnit

/-!
# Equation 03LW at the structure sheaf

Let `φ : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Equation 03LW of [Stacks Project, Tag 03LW] identifies the pullback of
`𝒪_X`-modules along `φ` with étale restriction,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`.  At the structure sheaf, read as
a module over itself, étale restriction returns `𝒪_U` on the nose
(`AlgebraicGeometry.Space.etaleModulePullback_obj_unit`), so that component of the comparison is
a morphism

`φ^*𝒪_X ⟶ 𝒪_U`.

This file identifies it with the canonical such morphism
`AlgebraicGeometry.Space.structureModulePullbackMap`, the transpose of pullback of regular
functions along the vertical morphism of a diagram of étale scheme charts.  That identification
is the step the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` record as supplied by
nothing in the development, and it is what Stacks 04G2, part (2) needs in order to compare the
isomorphism of Stacks 04CO with the canonical map of Stacks 04CP at the unit module.

The identification is made in two halves, through the third available morphism
`φ^*𝒪_X ⟶ 𝒪_U`: the comparison
`AlgebraicGeometry.Space.modulePullbackUnitIso` of Stacks 03LU, built by corepresentability.

## Main results

* `AlgebraicGeometry.Space.moduleFMap_unit_ext`: a linear map of sections out of the unit module
  is determined by its value on the unit section.
* `AlgebraicGeometry.Space.structureModulePullbackMap_eq_modulePullbackUnitIso_hom_of_unit`: **the
  canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` defined by pullback of regular functions is the
  corepresentability comparison of [Stacks Project, Tag 03LU]**, for an arbitrary morphism `g` of
  algebraic spaces.  The implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapStructureSheaf.lean` record this
  identification as not carried there; it is carried here.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit`: **Equation 03LW at
  the structure sheaf is that same comparison.**
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit_eq`: **the two
  together** — Equation 03LW at the structure sheaf is
  `AlgebraicGeometry.Space.structureModulePullbackMap`.
* `AlgebraicGeometry.Space.isIso_structureModulePullbackMap_of_unit` and
  `AlgebraicGeometry.Space.mono_structureModulePullbackMap_of_unit`: as a consequence that map is
  an isomorphism, the corepresentability comparison being one.  The second is the hypothesis
  `hθ` of `AlgebraicGeometry.Space.mono_idealSheafMap_of_mono`, which the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/IdealSheafMapStructureSheaf.lean` record as assumed.

## Implementation notes

**Why the comparison of corepresentability is the pivot.**  Each of the two halves compares the
corepresentability comparison with one of the other two morphisms, and each comparison is a
different kind of statement.

* Against `AlgebraicGeometry.Space.structureModulePullbackMap` the comparison is *chartwise*:
  both morphisms are determined by their linear maps of sections along `g`
  (`AlgebraicGeometry.Space.modulePullbackHomFMap`), a linear map of sections out of the unit
  module is determined by its value on the unit section — this is
  `AlgebraicGeometry.Space.moduleFMap_unit_ext`, which is semilinearity over
  `AlgebraicGeometry.Space.chartDiagramPullback` — and on the unit section both are the unit
  section, the corepresentability comparison by
  `AlgebraicGeometry.Space.modulePullbackUnitIso_hom_val_app_modulePullbackChartSection`.  No
  étaleness is used, so this half holds for every morphism of algebraic spaces.
* Against Equation 03LW the comparison is *through the transposes along the extension of scalars
  of Stacks 03CZ*, read on underlying sheaves of sets.  There both transposes are the comparison
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` of Stacks 03LQ: for
  Equation 03LW by `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`
  together with the transport comparison being that comparison on sections
  (`Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleMapOfNatTrans`), and for
  the corepresentability comparison by
  `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_fSharpAdjunction_homEquiv` — which
  gives the inverse-image form of the structure map — together with
  `AlgebraicGeometry.Space.forgetRing_fSharpInverseImage_eq_inverseImageIso`, which is where
  étaleness enters.  A morphism of sheaves of modules is determined by its underlying morphism
  of sheaves of sets, so the two transposes agree and so do the two morphisms.

**Why the second half is not made at the level of morphisms of modules.**  The two transposes
have definitionally equal sources and targets, but the targets of the *morphisms compared inside
them* — `(restrictScalars φ♯).obj (φ^*𝒪_X)` in one spelling and the value of
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` composed with a restriction of scalars along
`AlgebraicGeometry.Space.etaleInverseImageRestrictionRingMap` in the other — are restrictions of
scalars along two *different* maps of sheaves of rings.  So the morphism-level equality of
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` with the transport
comparison is not type-correct, and the statement has to be made after
`CategoryTheory.Sheaf.moduleSheafFunctor`, which forgets the scalar action.  The
morphism-level form is a type mismatch; the sheaf-of-sets form checks in under ten seconds.

**The unit section is written at the ring.**  `(1 : (structureRingSheaf … ).obj.obj (op d.V))`
rather than `1` at the sections of the unit module: the coercion of
`CategoryTheory.SheafOfModules.unit` is not unfolded by instance search, so `OfNat` is not found
at the module spelling even though the two types are definitionally equal.  For the same reason
the identity `s = s * 1` is introduced as a statement quantified over the *ring*, and the
multiplication is then matched against the scalar action of the unit module by unification.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Linear maps of sections out of the unit module -/

section Unit

variable {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')

/-- **A linear map of sections out of the unit module is determined by its value on the unit
section.**  Over a chart diagram `d` every section of `𝒪_{X'}` is its own multiple of the unit
section, and a linear map of sections is semilinear over pullback of regular functions. -/
theorem moduleFMap_unit_ext (F : Modules.{u, u} B S hS X.1 X.2)
    (ξ ζ : ModuleFMap B S hS g F (SheafOfModules.unit (structureRingSheaf B S hS X')))
    (h : ∀ d : ChartDiagram B S hS X.1 X'.1 g.hom,
      ξ.app d (1 : (structureRingSheaf B S hS X').obj.obj (op d.V)) =
        ζ.app d (1 : (structureRingSheaf B S hS X').obj.obj (op d.V))) :
    ξ = ζ := by
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  have hone : ∀ t : (structureRingSheaf B S hS X').obj.obj (op d.V), t = t * 1 := fun t ↦
    (mul_one t).symm
  have key : ∀ θ : ModuleFMap B S hS g F (SheafOfModules.unit (structureRingSheaf B S hS X')),
      θ.app d s = chartDiagramPullback B S hS g d s •
        θ.app d (1 : (structureRingSheaf B S hS X').obj.obj (op d.V)) := fun θ ↦
    (congrArg (θ.app d) (hone s)).trans
      (θ.map_smul d s (1 : (structureRingSheaf B S hS X').obj.obj (op d.V)))
  exact (key ξ).trans ((congrArg (fun y ↦ chartDiagramPullback B S hS g d s • y)
    (h d)).trans (key ζ).symm)

/-- The linear map of sections of the structure map, on a section over a chart diagram, is
pullback of regular functions along the vertical morphism of the diagram. -/
theorem structureModuleFMap_app (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (structureRingSheaf B S hS X').obj.obj (op d.V)) :
    (structureModuleFMap B S hS g).app d s = chartDiagramPullback B S hS g d s :=
  rfl

/-- **The canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` of [Stacks Project, Tag 03LU] is the map defined by
pullback of regular functions.**  The isomorphism
`AlgebraicGeometry.Space.modulePullbackUnitIso`, built by corepresentability, is
`AlgebraicGeometry.Space.structureModulePullbackMap`.

Both are morphisms out of an inverse image, hence determined by their linear maps of sections
along `g`, and a linear map of sections out of the unit module is determined by its value on the
unit section.  There the left-hand side is `1` because pullback of regular functions is a
homomorphism of rings, and the right-hand side is `1` by
`AlgebraicGeometry.Space.modulePullbackUnitIso_hom_val_app_modulePullbackChartSection`, the one
value of the corepresentability comparison that is available — the two spellings of the chart
component of the unit being identified by
`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection`. -/
theorem structureModulePullbackMap_eq_modulePullbackUnitIso_hom_of_unit :
    structureModulePullbackMap B S hS g = (modulePullbackUnitIso B S hS g).hom := by
  refine ((modulePullbackAdjunction B S hS g).homEquiv _ _).injective ?_
  refine (modulePushforwardHomEquiv B S hS g _ _).injective ?_
  rw [structureModulePullbackMap_transpose, Equiv.apply_symm_apply]
  refine moduleFMap_unit_ext B S hS g _ _ _ (fun d ↦ ?_)
  refine Eq.trans (Eq.trans (structureModuleFMap_app B S hS g d _)
    (map_one (chartDiagramPullback B S hS g d).hom)) ?_
  refine Eq.trans ?_ (modulePullbackHomFMap_app B S hS g
    (SheafOfModules.unit (structureRingSheaf B S hS X'))
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (modulePullbackUnitIso B S hS g).hom d
    (1 : (structureRingSheaf B S hS X').obj.obj (op d.V))).symm
  refine Eq.trans ?_ (congrArg ((modulePullbackUnitIso B S hS g).hom.val.app (op d.U))
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X')) d
      (1 : (structureRingSheaf B S hS X').obj.obj (op d.V))).symm)
  exact (modulePullbackUnitIso_hom_val_app_modulePullbackChartSection B S hS g d).symm

/-- **The canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` of pullback of regular functions is an
isomorphism**, being the corepresentability comparison of [Stacks Project, Tag 03LU]. -/
theorem isIso_structureModulePullbackMap_of_unit : IsIso (structureModulePullbackMap B S hS g) := by
  rw [structureModulePullbackMap_eq_modulePullbackUnitIso_hom_of_unit]
  exact Iso.isIso_hom _

/-- The canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` is a monomorphism.  This is the hypothesis `hθ` of
`AlgebraicGeometry.Space.mono_idealSheafMap_of_mono`, whose implementation notes record it as
assumed rather than deduced; it is deduced here. -/
theorem mono_structureModulePullbackMap_of_unit : Mono (structureModulePullbackMap B S hS g) :=
  have := isIso_structureModulePullbackMap_of_unit B S hS g
  IsIso.mono_of_iso (structureModulePullbackMap B S hS g)

end Unit

/-! ### Equation 03LW at the structure sheaf -/

section Etale

variable {U X : AlgebraicSpaces B S hS} (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)

/-- The transport comparison of `AlgebraicGeometry.Space.etaleModuleInverseImage` with étale
restriction acts on underlying sheaves of sets as the comparison of Stacks 03LQ: it is
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` at that comparison, and a
transport along a natural isomorphism of the transporting functors is that isomorphism on the
underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_etaleModuleInverseImageIsoRestrictionTransport
    (G : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS φ).toToposHom (structureRingSheaf B S hS X))).map
        ((etaleModuleInverseImageIsoRestrictionTransport B S hS φ hφ).hom.app G) =
      (smallToposMorphismTypeU_inverseImageIso B S hS φ hφ).hom.app
        (moduleSetSheaf B S hS X G) :=
  rfl

/-- **The transpose of Equation 03LW along the extension of scalars of Stacks 03CZ is the
comparison of Stacks 03LQ**, on underlying sheaves of sets.

The transpose is the unit of Stacks 03CZ followed by the restriction of scalars of the
comparison, which is what
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` describes on sections:
it is the transport comparison, and that is the comparison of Stacks 03LQ on sheaves of sets. -/
theorem moduleSheafFunctor_map_homEquiv_modulePullbackIsoEtaleModulePullback
    (G : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS φ).toToposHom (structureRingSheaf B S hS X))).map
        ((extendScalarsFSharpAdjunction B S hS φ).homEquiv _ _
          ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app G)) =
      (smallToposMorphismTypeU_inverseImageIso B S hS φ hφ).hom.app
        (moduleSetSheaf B S hS X G) := by
  refine Sheaf.hom_ext_sections (fun W m ↦ ?_)
  have h1 : ((extendScalarsFSharpAdjunction B S hS φ).homEquiv _ _
        ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app G)).val.app W m =
      ((etaleModuleInverseImageIsoRestrictionTransport B S hS φ hφ).hom.app G).val.app W m :=
    (congrArg (fun z ↦ z.val.app W m)
        (Adjunction.homEquiv_unit (extendScalarsFSharpAdjunction B S hS φ) _ _
          ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app G))).trans
      (modulePullbackIsoEtaleModulePullback_unit_app B S hS φ hφ G W m)
  exact h1.trans (congrArg (fun z ↦ z.hom.app W m)
    (moduleSheafFunctor_map_etaleModuleInverseImageIsoRestrictionTransport B S hS φ hφ G))

/-- The comparison `φ^*𝒪_X ≅ 𝒪_U` built by corepresentability is the explicit comparison of
`Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso`.  This is
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_eq`, read on the inverse
isomorphism. -/
theorem modulePullbackUnitIso_hom_eq :
    (modulePullbackUnitIso B S hS φ).hom =
      (Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso
        (smallEtaleRingedToposModulesHom B S hS φ)).inv :=
  congrArg Iso.inv (pullbackModulesObjUnitIso_eq (smallEtaleRingedToposModulesHom B S hS φ))

/-- **The transpose of the corepresentability comparison `φ^*𝒪_X ⟶ 𝒪_U` along the extension of
scalars of Stacks 03CZ is the comparison of Stacks 03LQ**, on underlying sheaves of sets.

`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_fSharpAdjunction_homEquiv` gives the
transpose of the explicit comparison — which the corepresentability one is — as the
inverse-image form `φ⁻¹𝒪_X ⟶ 𝒪_U` of the structure map, read in sheaves of not necessarily
commutative rings; and along an étale morphism that is the comparison of Stacks 03LQ at the
structure sheaf, by
`AlgebraicGeometry.Space.forgetRing_fSharpInverseImage_eq_inverseImageIso` with the two
forgetful functors reconciled by
`AlgebraicGeometry.RingedToposHom.forgetRing_map_fSharpInverseImage`. -/
theorem moduleSheafFunctor_map_homEquiv_modulePullbackUnitIso_hom :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS φ).toToposHom (structureRingSheaf B S hS X))).map
        ((extendScalarsFSharpAdjunction B S hS φ).homEquiv _ _
          (modulePullbackUnitIso B S hS φ).hom) =
      (smallToposMorphismTypeU_inverseImageIso B S hS φ hφ).hom.app
        (structureSetSheaf B S hS X) :=
  ((congrArg (fun z ↦ (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS φ).toToposHom
          (structureRingSheaf B S hS X))).map
        ((extendScalarsFSharpAdjunction B S hS φ).homEquiv _ _ z))
        (modulePullbackUnitIso_hom_eq B S hS φ)).trans
      (moduleSheafFunctor_map_fSharpAdjunction_homEquiv
        (smallEtaleRingedToposModulesHom B S hS φ))).trans
    (forgetRing_fSharpInverseImage_eq_inverseImageIso B S hS φ hφ)

/-- **Equation 03LW at the structure sheaf is the comparison `φ^*𝒪_X ≅ 𝒪_U` of
[Stacks Project, Tag 03LU].**  Along an étale morphism the component of Equation 03LW at the
structure sheaf, read as a module over itself, is the corepresentability comparison
`AlgebraicGeometry.Space.modulePullbackUnitIso`.

Both are morphisms out of a pullback of modules which is an extension of scalars of an inverse
image, so each is determined by its transpose along the adjunction of Stacks 03CZ, and a
morphism of sheaves of modules is determined by its underlying morphism of sheaves of sets.
There both transposes are the comparison of Stacks 03LQ at the structure sheaf: the one of
Equation 03LW by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_homEquiv_modulePullbackIsoEtaleModulePullback`,
the one of the corepresentability comparison by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_homEquiv_modulePullbackUnitIso_hom` together
with `AlgebraicGeometry.Space.forgetRing_fSharpInverseImageRing_eq_inverseImageIso`. -/
theorem modulePullbackIsoEtaleModulePullback_hom_app_unit :
    (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      (modulePullbackUnitIso B S hS φ).hom := by
  have key : (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS φ).toToposHom (structureRingSheaf B S hS X))).map
        ((extendScalarsFSharpAdjunction B S hS φ).homEquiv _ _
          ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS X)))) =
      (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS φ).toToposHom (structureRingSheaf B S hS X))).map
        ((extendScalarsFSharpAdjunction B S hS φ).homEquiv _ _
          (modulePullbackUnitIso B S hS φ).hom) :=
    (moduleSheafFunctor_map_homEquiv_modulePullbackIsoEtaleModulePullback B S hS φ hφ
        (SheafOfModules.unit (structureRingSheaf B S hS X))).trans
      (moduleSheafFunctor_map_homEquiv_modulePullbackUnitIso_hom B S hS φ hφ).symm
  have key2 := hom_ext_moduleSheafFunctor
    (R := inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS φ).toToposHom (structureRingSheaf B S hS X)) key
  exact ((extendScalarsFSharpAdjunction B S hS φ).homEquiv _ _).injective key2

/-- **Equation 03LW at the structure sheaf is the canonical map `φ^*𝒪_X ⟶ 𝒪_U` built from
pullback of regular functions.**  This is the step the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` record as supplied by
nothing in this development: it brings the description of
`AlgebraicGeometry.Space.structureModulePullbackMap` after two transposes and the description of
Equation 03LW after the unit of the extension of scalars to a common form.

It is `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_unit` followed by
`AlgebraicGeometry.Space.structureModulePullbackMap_eq_modulePullbackUnitIso_hom_of_unit`. -/
theorem modulePullbackIsoEtaleModulePullback_hom_app_unit_eq :
    (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      structureModulePullbackMap B S hS φ :=
  (modulePullbackIsoEtaleModulePullback_hom_app_unit B S hS φ hφ).trans
    (structureModulePullbackMap_eq_modulePullbackUnitIso_hom_of_unit B S hS φ).symm

end Etale

end AlgebraicGeometry.Space

end
