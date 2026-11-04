module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeEtaleSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# The identification `g^*𝒪_{X'} ≅ 𝒪_X` is pullback of functions, and it composes

`AlgebraicGeometry.Space.modulePullbackUnitIso` is the identification of Stacks 03LU of the
inverse image of the structure sheaf with the structure sheaf.  It is built by
corepresentability, so the only description of it available until now was
`AlgebraicGeometry.Space.modulePullbackUnitIso_inv_val_app_one`, its inverse on the unit
function.

This file identifies it with `AlgebraicGeometry.Space.structureModulePullbackMap`, the canonical
map `g^*𝒪_{X'} ⟶ 𝒪_X` built from pullback of regular functions along the vertical morphism of a
chart diagram.  Two consequences follow at once:

* its value on **every** chart section is pullback of regular functions, not only on the unit
  function;
* it is **compatible with the comparison of iterated inverse images**, because
  `AlgebraicGeometry.Space.structureModulePullbackMap_comp` says that the map built from pullback
  of functions is.

The second is the coherence that the naturality hypotheses `he` and `heT` of the consumers of
Stacks 07SI need: those hypotheses compare the transition map
`Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` of Stacks 07SI at structure-sheaf coefficients — which is read through
`AlgebraicGeometry.Space.modulePullbackCompIso` — with restriction of regular functions, and the
identification of `ℱᵢ` with `𝒪_{Xᵢ}` is `modulePullbackUnitIso`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackHomFMap_modulePullbackUnitIso_hom`: the chartwise
  transpose of `modulePullbackUnitIso` is `AlgebraicGeometry.Space.structureModuleFMap`, that is
  pullback of regular functions along the vertical morphism of a chart diagram.
* `AlgebraicGeometry.Space.modulePullbackUnitIso_hom_eq_structureModulePullbackMap`: **the
  identification of Stacks 03LU is `AlgebraicGeometry.Space.structureModulePullbackMap`.**
* `AlgebraicGeometry.Space.modulePullbackUnitIso_hom_val_app_modulePullbackChartSection`: its
  value on a chart section is pullback of regular functions.
* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_comp_modulePullbackUnitIso_hom`:
  **the identification of Stacks 03LU is compatible with the comparison of iterated inverse
  images of Stacks 03LU.**

## Implementation notes

*Why the chartwise transpose is the right invariant.*  A morphism out of a pullback of modules is
exactly a linear map of sections along the morphism
(`AlgebraicGeometry.Space.modulePullbackFMapEquiv`, a bijection), and the values of that linear
map are the values of the morphism on the unit sections
(`AlgebraicGeometry.Space.modulePullbackHomFMap_app`).  So to identify two morphisms out of
`g^*𝒪_{X'}` it suffices to compute both on the unit sections, and for the unit module the unit
section of an arbitrary regular function is a multiple of the unit section of the unit function
by semilinearity, which is exactly where the one available value of `modulePullbackUnitIso`
enters.

*No new coherence is proved here.*  The composition law is
`AlgebraicGeometry.Space.structureModulePullbackMap_comp`, which is already in the library; what
this file adds is that the morphism it is a law for is the identification built by
corepresentability.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- On the unit module a regular function is its own multiple of the unit function.  The result
type is ascribed so that the scalar action is the module action the chartwise transpose is
semilinear over, and not the ring's own multiplication. -/
private theorem unit_smul_one {Z : AlgebraicSpaces B S hS} (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (r : (structureRingSheaf B S hS Z).obj.obj W) :
    (r • (1 : (structureRingSheaf B S hS Z).obj.obj W) :
        (SheafOfModules.unit (structureRingSheaf B S hS Z)).val.obj W) = r :=
  mul_one r

variable {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')

/-- **The identification `g^*𝒪_{X'} ≅ 𝒪_X` of Stacks 03LU carries a chart section of a regular
function to its pullback.**  This is the value on the unit section of the unit module, computed
from the one value of the identification that corepresentability yields — its inverse on the unit
function, `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_val_app_one` — together with
semilinearity. -/
theorem modulePullbackUnitIso_hom_val_app_modulePullbackUnitSection
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (structureRingSheaf B S hS X').obj.obj (op d.V)) :
    (modulePullbackUnitIso B S hS g).hom.val.app (op d.U)
        (modulePullbackUnitSection B S hS g
          (SheafOfModules.unit (structureRingSheaf B S hS X')) d s)
      = chartDiagramPullback B S hS g d s := by
  have hone : (modulePullbackUnitIso B S hS g).hom.val.app (op d.U)
      (modulePullbackUnitSection B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X')) d
        (1 : (structureRingSheaf B S hS X').obj.obj (op d.V)))
      = (1 : (structureRingSheaf B S hS X).obj.obj (op d.U)) := by
    refine Eq.trans (congrArg
      (fun z ↦ (modulePullbackUnitIso B S hS g).hom.val.app (op d.U) z)
      ((modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g
          (SheafOfModules.unit (structureRingSheaf B S hS X')) d
          (1 : (structureRingSheaf B S hS X').obj.obj (op d.V))).trans
        (modulePullbackUnitIso_inv_val_app_one B S hS g d).symm)) ?_
    exact (comp_val_app_apply B S hS (modulePullbackUnitIso B S hS g).inv
        (modulePullbackUnitIso B S hS g).hom (op d.U) _).symm.trans
      (congrArg
        (fun m : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
            SheafOfModules.unit (structureRingSheaf B S hS X) ↦
          m.val.app (op d.U) (1 : (structureRingSheaf B S hS X).obj.obj (op d.U)))
        (modulePullbackUnitIso B S hS g).inv_hom_id)
  have hone' : (modulePullbackHomFMap B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X'))
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (modulePullbackUnitIso B S hS g).hom).app d
        (1 : (structureRingSheaf B S hS X').obj.obj (op d.V))
      = (1 : (structureRingSheaf B S hS X).obj.obj (op d.U)) :=
    (modulePullbackHomFMap_app B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X'))
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (modulePullbackUnitIso B S hS g).hom d
      (1 : (structureRingSheaf B S hS X').obj.obj (op d.V))).trans hone
  have hsmul := (modulePullbackHomFMap B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X'))
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (modulePullbackUnitIso B S hS g).hom).map_smul d s
    (1 : (structureRingSheaf B S hS X').obj.obj (op d.V))
  rw [hone'] at hsmul
  refine Eq.trans (modulePullbackHomFMap_app B S hS g
    (SheafOfModules.unit (structureRingSheaf B S hS X'))
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (modulePullbackUnitIso B S hS g).hom d s).symm ?_
  exact ((congrArg
        (fun z ↦ (modulePullbackHomFMap B S hS g
          (SheafOfModules.unit (structureRingSheaf B S hS X'))
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (modulePullbackUnitIso B S hS g).hom).app d z)
        (unit_smul_one B S hS (op d.V) s).symm).trans hsmul).trans
    (unit_smul_one B S hS (op d.U) (chartDiagramPullback B S hS g d s))

/-- **The chartwise transpose of the identification `g^*𝒪_{X'} ≅ 𝒪_X` of Stacks 03LU is pullback
of regular functions**, that is `AlgebraicGeometry.Space.structureModuleFMap`. -/
theorem modulePullbackHomFMap_modulePullbackUnitIso_hom :
    modulePullbackHomFMap B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X'))
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (modulePullbackUnitIso B S hS g).hom
      = structureModuleFMap B S hS g :=
  ModuleFMap.ext B S hS
    (a := modulePullbackHomFMap B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X'))
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (modulePullbackUnitIso B S hS g).hom)
    (b := structureModuleFMap B S hS g)
    (funext fun d ↦ funext fun s ↦
      (modulePullbackHomFMap_app B S hS g
          (SheafOfModules.unit (structureRingSheaf B S hS X'))
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (modulePullbackUnitIso B S hS g).hom d s).trans
        (modulePullbackUnitIso_hom_val_app_modulePullbackUnitSection B S hS g d s))

/-- The chartwise transpose of `AlgebraicGeometry.Space.structureModulePullbackMap` is pullback of
regular functions.  This is its characterising property
`AlgebraicGeometry.Space.structureModulePullbackMap_transpose`, read through the bijection
`AlgebraicGeometry.Space.modulePullbackFMapEquiv`. -/
theorem modulePullbackHomFMap_structureModulePullbackMap :
    modulePullbackHomFMap B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X'))
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (structureModulePullbackMap B S hS g)
      = structureModuleFMap B S hS g :=
  (congrArg (modulePushforwardHomEquiv B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (SheafOfModules.unit (structureRingSheaf B S hS X')))
    (structureModulePullbackMap_transpose B S hS g)).trans
    (Equiv.apply_symm_apply _ _)

/-- **The identification `g^*𝒪_{X'} ≅ 𝒪_X` of Stacks 03LU is
`AlgebraicGeometry.Space.structureModulePullbackMap`**, the map that pullback of regular functions
along `g` induces on the inverse image.

Both are morphisms out of `g^*𝒪_{X'}`, hence determined by their chartwise transposes, and both
transposes are pullback of regular functions along the vertical morphism of a chart diagram. -/
theorem modulePullbackUnitIso_hom_eq_structureModulePullbackMap :
    (modulePullbackUnitIso B S hS g).hom = structureModulePullbackMap B S hS g :=
  (modulePullbackFMapEquiv B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (SheafOfModules.unit (structureRingSheaf B S hS X'))).injective
    ((modulePullbackHomFMap_modulePullbackUnitIso_hom B S hS g).trans
      (modulePullbackHomFMap_structureModulePullbackMap B S hS g).symm)

/-- **The identification `g^*𝒪_{X'} ≅ 𝒪_X` of Stacks 03LU carries a chart section of a regular
function to its pullback**, in the `AlgebraicGeometry.Space.modulePullbackChartSection`
spelling.  The library's
`AlgebraicGeometry.Space.modulePullbackUnitIso_hom_val_app_modulePullbackChartSection` is the
special case of the unit function; this is the general one. -/
theorem modulePullbackUnitIso_hom_val_app_chartSection
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (structureRingSheaf B S hS X').obj.obj (op d.V)) :
    (modulePullbackUnitIso B S hS g).hom.val.app (op d.U)
        (modulePullbackChartSection B S hS g
          (SheafOfModules.unit (structureRingSheaf B S hS X')) d s)
      = chartDiagramPullback B S hS g d s :=
  (congrArg (fun z ↦ (modulePullbackUnitIso B S hS g).hom.val.app (op d.U) z)
      (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X')) d s).symm).trans
    (modulePullbackUnitIso_hom_val_app_modulePullbackUnitSection B S hS g d s)

/-- **The identification of Stacks 03LU of the inverse image of the structure sheaf with the
structure sheaf is compatible with the comparison of iterated inverse images of Stacks 03LU.**
For `g : X ⟶ X'` and `g' : X' ⟶ X''` the two routes from `g^*g'^*𝒪_{X''}` to `𝒪_X` — through the
comparison `g^*g'^* ≅ (g ≫ g')^*` and the identification at the composite, or through the inverse
image along `g` of the identification at `g'` followed by the identification at `g` — agree.

This is `AlgebraicGeometry.Space.structureModulePullbackMap_comp` once
`AlgebraicGeometry.Space.modulePullbackUnitIso_hom_eq_structureModulePullbackMap` has identified
the three identifications with the three canonical maps built from pullback of regular
functions. -/
theorem modulePullbackCompIso_hom_app_comp_modulePullbackUnitIso_hom
    {X'' : AlgebraicSpaces B S hS} (g' : X' ⟶ X'') :
    (modulePullbackCompIso B S hS g g').hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'')) ≫
        (modulePullbackUnitIso B S hS (g ≫ g')).hom
      = (modulePullback B S hS g).map (modulePullbackUnitIso B S hS g').hom ≫
        (modulePullbackUnitIso B S hS g).hom :=
  have hcomp : (modulePullbackUnitIso B S hS (g ≫ g')).hom
      = (modulePullbackCompIso B S hS g g').inv.app
            (SheafOfModules.unit (structureRingSheaf B S hS X'')) ≫
          (modulePullback B S hS g).map (modulePullbackUnitIso B S hS g').hom ≫
          (modulePullbackUnitIso B S hS g).hom := by
    rw [modulePullbackUnitIso_hom_eq_structureModulePullbackMap B S hS (g ≫ g'),
      modulePullbackUnitIso_hom_eq_structureModulePullbackMap B S hS g',
      modulePullbackUnitIso_hom_eq_structureModulePullbackMap B S hS g]
    exact structureModulePullbackMap_comp B S hS g g'
  (congrArg (fun z ↦ (modulePullbackCompIso B S hS g g').hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X'')) ≫ z) hcomp).trans
    (Iso.hom_inv_id_app_assoc (modulePullbackCompIso B S hS g g') _ _)

end AlgebraicGeometry.Space

end
