module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Openness of the locus of the fibrewise criterion for flatness

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes with `X ⟶ S` locally of finite
presentation and `Y ⟶ S` locally of finite type, and let `F` be an `𝒪_X`-module of finite
presentation. At a point `x` of the support of `F` the two conditions of the fibrewise criterion
for flatness (Stacks Tag 039C) are equivalent; this file proves the remaining assertion of that
tag, that the set of points of `Supp(F)` at which they hold is open in `Supp(F)`.

## Main results

* `Stacks.Flatness.setOf_isFlatOverBaseAndFiberAt_and_isFlatOverIntermediateAt` identifies that
  set with the trace on `Supp(F)` of the set of points at which `F` is flat over `S` and over
  `Y`, which is the set `U` of Stacks Tag 05VI.
* `Stacks.Flatness.isOpen_isFlatOverBaseAndFiberAt` is openness of that set in `Supp(F)`.

## Implementation notes

The set `U` is open because each of its two halves is: the half over `S` is Tag 0399,
`AlgebraicGeometry.isOpen_setOf_flatOverAt`, applied to `f ≫ g`, and the half over `Y` is Tag
05VJ, `AlgebraicGeometry.isOpen_setOf_isFlatOverAt_of_locallyOfFiniteType`, which supplies
locally-of-finite-presentation for `f` itself out of the two finiteness hypotheses (Tag 02FV).

On `U` the fibre half of condition (1) is automatic: the fibre square of
`Stacks.Flatness.isPullback_fiberHom` lets Tag 01U8,
`AlgebraicGeometry.modulePullback_isFlatOverAt`, carry flatness over `Y` to flatness of the
restriction of `F` to `X_s` over `Y_s`. So condition (1) holds throughout `U ∩ Supp(F)`, and
condition (2) then follows from `Stacks.Flatness.isFlatOverBaseAndFiberAt_iff`. Conversely a
point of the support at which both conditions hold lies in `U`, taking the first half of (1) and
the second half of (2). Openness in the support is then openness of the preimage of `U` under
the inclusion of the subspace `Supp(F)`.

## References

* [Stacks Project, Tag 039C](https://stacks.math.columbia.edu/tag/039C)
* [Stacks Project, Tag 05VI](https://stacks.math.columbia.edu/tag/05VI)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 05VJ](https://stacks.math.columbia.edu/tag/05VJ)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Flatness

/-- The fibre half of condition (1) of the fibrewise criterion follows from flatness of `F` over
the intermediate scheme, by base change along `Y_s ⟶ Y`. -/
private theorem isFlatOverAt_fiber_of_isFlatOverAt {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] (x : X)
    (hf : IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsFlatOverAt (fiberHom f g (g (f x))).toLRSHom.toShHom
      ((modulePullback ((f ≫ g).fiberι (g (f x))).toLRSHom.toShHom).obj F)
      ((f ≫ g).asFiber x) :=
  modulePullback_isFlatOverAt (isPullback_fiberHom f g (g (f x))).flip F ((f ≫ g).asFiber x)
    (((f ≫ g).fiberι_asFiber x).symm ▸ hf)

/-- **Stacks Project, Tag 05VI.** The set of points of the support of `F` at which both
conditions of the fibrewise criterion hold is the trace on the support of the set of points at
which `F` is flat over the base and over the intermediate scheme. -/
public theorem setOf_isFlatOverBaseAndFiberAt_and_isFlatOverIntermediateAt {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [LocallyOfFinitePresentation (f ≫ g)] [F.IsFinitePresentation] [LocallyOfFiniteType g] :
    {x : SheafOfModules.supp F |
        IsFlatOverBaseAndFiberAt f g F x.1 ∧ IsFlatOverIntermediateAt f g F x.1} =
      Subtype.val ⁻¹' ({x : X | IsFlatOverAt (f ≫ g).toLRSHom.toShHom F x} ∩
        {x : X | IsFlatOverAt f.toLRSHom.toShHom F x}) := by
  ext x
  refine ⟨fun h => ⟨h.1.1, h.2.2⟩, fun h => ?_⟩
  have h₁ : IsFlatOverBaseAndFiberAt f g F x.1 :=
    ⟨h.1, isFlatOverAt_fiber_of_isFlatOverAt f g F x.1 h.2⟩
  exact ⟨h₁, (isFlatOverBaseAndFiberAt_iff f g F x.1 x.2).mp h₁⟩

/-- **Stacks Project, Tag 039C.** The set of points of the support of a quasi-coherent module of
finite presentation at which the two equivalent conditions of the fibrewise criterion for
flatness hold is open in the support. -/
@[stacks 039C "openness of the common locus", ega "IV 11.3.10" "2°) open locus"]
public theorem isOpen_isFlatOverBaseAndFiberAt {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [LocallyOfFinitePresentation (f ≫ g)] [F.IsFinitePresentation] [LocallyOfFiniteType g] :
    IsOpen {x : SheafOfModules.supp F |
      IsFlatOverBaseAndFiberAt f g F x.1 ∧ IsFlatOverIntermediateAt f g F x.1} := by
  have hqc : F.IsQuasicoherent := inferInstance
  have hbase : IsOpen {x : X | IsFlatOverAt (f ≫ g).toLRSHom.toShHom F x} := by
    let F₀ : X.Modules := F
    have : F₀.IsQuasicoherent := hqc
    have : F₀.IsFinitePresentation := ‹F.IsFinitePresentation›
    exact isOpen_setOf_flatOverAt (f ≫ g) F₀
  have hinter : IsOpen {x : X | IsFlatOverAt f.toLRSHom.toShHom F x} :=
    isOpen_setOf_isFlatOverAt_of_locallyOfFiniteType f g F
  rw [setOf_isFlatOverBaseAndFiberAt_and_isFlatOverIntermediateAt f g F]
  exact (hbase.inter hinter).preimage continuous_subtype_val

end Stacks.Flatness

end
