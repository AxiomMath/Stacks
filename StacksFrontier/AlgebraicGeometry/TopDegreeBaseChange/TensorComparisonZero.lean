module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.UnitCase
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparison

/-!
# A canonical tensor map for the direct image in degree zero

`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TensorComparison.lean` states the
canonicity condition `IsHigherDirectImageTensorMap` that conclusion (b) of [Stacks, Tag 0EX3]
asks of a map

`R^n f_* F ⊗_{𝒪_Y} G ⟶ R^n f_*(F ⊗_{𝒪_X} f^* G)`,

proves that at most one map satisfies it, and derives the conclusion from a map that does and is
invertible; it does not itself supply such a map.

This file supplies a map **in degree zero**, for an arbitrary morphism of schemes and arbitrary
sheaves of modules. In degree zero the direct image is its own zeroth right derived functor
(`Stacks.RightDerivedPlus.rightDerivedPlusZeroIso`, available because a right adjoint is left
exact), and the underived canonical map
`Stacks.AffineProjectionFormula.projectionFormulaMap` — the adjoint transpose of the pullback
tensor comparison of [Stacks, Tag 01CD] followed by the counit of `f^* ⊣ f_*` — already has
exactly the shape required. Conjugating it by the degree-zero normalisation produces a map of
the type `IsHigherDirectImageTensorMap` consumes, and its invertibility is inherited from the
invertibility of the underived map: unconditionally for a closed immersion, and for an arbitrary
morphism when the module on the target is trivial.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.directImageZeroIso`: the degree-zero
  normalisation `R^0 f_* ≅ f_*`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorMapZero`: **the canonical
  map `R^0 f_* F ⊗_{𝒪_Y} G ⟶ R^0 f_*(F ⊗_{𝒪_X} f^* G)`**, for an arbitrary morphism of schemes
  and arbitrary modules.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorIsoZero`: the resulting
  isomorphism, carrying the identification of its inverse with the canonical map.

## Main results

All of the following live in the namespace
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `higherDirectImageTensorMapZero_comp_directImageZeroIso`: the canonical map read through the
  degree-zero normalisation is the underived canonical map. This pins the map down; without it
  "the canonical map" would be an unspecified morphism.
* `isIso_higherDirectImageTensorMapZero_of_isClosedImmersion`: the degree-zero comparison is
  invertible for a closed immersion, with no hypothesis on either module.
* `isIso_higherDirectImageTensorMapZero_of_iso_structureModule`: and for an arbitrary morphism
  of schemes when the module on the target is isomorphic to the structure sheaf.
* `isIso_projectionFormulaMap_of_isIso_higherDirectImageTensorMapZero`: the converse direction,
  recovering the underived statement from the degree-zero one, so that the degree-zero statement
  is not weaker than the one it is built from.
* `topDirectImageTensorComparisonZero`: conclusion (b) of [Stacks, Tag 0EX3] in degree zero,
  obtained by feeding the canonical map straight into
  `topDirectImageTensorComparisonOfIsIso`, with the canonicity condition as the only hypothesis
  that remains.

## Implementation notes

**What is still open, named precisely.** The canonicity condition
`IsHigherDirectImageTensorMap f F G 0 (higherDirectImageTensorMapZero f F G)` is the hypothesis
`hc` of `topDirectImageTensorComparisonZero` and is not proved here. It is the statement that
the adjoint-transpose description of the map and the local pure-tensor description agree, so the
residue of conclusion (b) in degree zero is now a comparison of two descriptions of one map —
which is exactly what makes `eq_of_isHigherDirectImageTensorMap` applicable — rather than the
absence of a map. Proving it requires the *components* of
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`, for which no
computational lemma exists: the scheme-level restriction comparison is obtained by rewriting
along two equalities of functors, and neither of those equalities holds definitionally, so its
components carry a transport that nothing in the tree unwinds. Its naturality in the module is
a different matter and is available, as
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_hom_naturality`.

**Two obligations, not one.** The implementation note of `TensorComparison.lean` names only the
naturality obligation on a bilinear family. Building the map that way needs a second input as
well: `Stacks.BilinearMap` requires linearity in *each* variable, and linearity in the section of
`G` amounts to `R^n g_*` carrying multiplication by `g^♯ r` to multiplication by `r`, the
`𝒪`-linearity of a right derived functor. That input is supplied by
`rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ` in the namespace
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage`
(`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedPushforwardLinear.lean`). Routing the
map through `projectionFormulaMap` discharges both obligations at once anyway, because an adjoint
transpose is a morphism of sheaves of modules by construction, which is why the degree-zero map
below is built that way and not from a bilinear family.

**Spellings.** `AlgebraicGeometry.Scheme.Modules.pushforward f`, `Scheme.Modules.pullback f` and
`Scheme.Modules.pullbackPushforwardAdjunction f` are definitionally the ringed-space
`Stacks.RingedSpace.pushforwardFunctor`, `pullbackFunctor` and `pullbackAdjunction` at
`f.toLRSHom.toShHom`, and `((0 : ℕ) : ℤ)` is definitionally `(0 : ℤ)`, so `projectionFormulaMap`
is usable here with no bridge. Instance search does *not* cross between `X.Modules` and
`SheafOfModules (structureSheafRing X.toRingedSpace)`,
  however, so the `IsIso`
facts are passed as explicit arguments rather than synthesized, `IsIso.id` is named rather than
inferred, and the reassociation is done in term mode: `rw [Category.assoc]` fails on these goals
with *"not type-correct under the `implicit` transparency level"*. No transparency option and no
option overrides is used.

**No tag attribute.** Conclusion (b) of Tag 0EX3 is about the top degree `d` of a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`; what is proved here is degree zero, and
the two invertibility statements carry hypotheses — a closed immersion, or a trivial module on
the target — which that tag does not. So no Stacks attribute is attached to any declaration
below, and the same holds of Tag 01E8, whose rank-one case
`isIso_projectionFormulaMap_of_iso_structureModule` already is.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AffineProjectionFormula Stacks.RingedSpace
open Stacks.RightDerivedPlus
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- The tensor product of two isomorphisms of sheaves of modules on a ringed space is an
isomorphism. The two `IsIso` facts are explicit arguments because instance search does not find
them across the two spellings of a sheaf of modules on a scheme. -/
theorem isIso_tensorSheafMap {Z : RingedSpace.{u, u}}
    {M M' N N' : SheafOfModules.{u} (structureRingSheaf Z)}
    (φ : M ⟶ M') (ψ : N ⟶ N') (hφ : IsIso φ) (hψ : IsIso ψ) :
    IsIso ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map
        ((φ, ψ) : (_, _) ⟶ (_, _))) :=
  ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).mapIso
      ((@asIso _ _ _ _ φ hφ).prod (@asIso _ _ _ _ ψ hψ))).isIso_hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules)

/-- **The degree-zero normalisation `R^0 f_* ≅ f_*`.** The direct image is a right adjoint, hence
left exact, so `Stacks.RightDerivedPlus.rightDerivedPlusZeroIso` applies to it. The degree is
written `((0 : ℕ) : ℤ)` because that is the shape in which the statements of
`TensorComparison.lean` take it. -/
abbrev directImageZeroIso :
    ((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)) ≅
      Scheme.Modules.pushforward f :=
  rightDerivedPlusZeroIso (Scheme.Modules.pushforward f)

/-- The underived canonical map of
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/Basic.lean`, with the degree-zero
normalisation applied to its source. -/
abbrev tensorMapZeroFactor :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj F)).obj G ⟶
      (Scheme.Modules.pushforward f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
          ((Scheme.Modules.pullback f).obj G)) := by
  let comparison :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
        ((Scheme.Modules.pushforward f).obj F)).obj G ⟶
      (Scheme.Modules.pushforward f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
          ((Scheme.Modules.pullback f).obj G)) :=
    projectionFormulaMap f.toLRSHom.toShHom F G
  let unitIso := (Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).mapIso
      (((directImageZeroIso f).app F).prod (Iso.refl G))
  exact unitIso.hom ≫ comparison

/-- **The canonical map `R^0 f_* F ⊗_{𝒪_Y} G ⟶ R^0 f_*(F ⊗_{𝒪_X} f^* G)`** of conclusion (b) of
[Stacks, Tag 0EX3] in degree zero, for an arbitrary morphism of schemes and arbitrary sheaves of
modules: the adjoint transpose of the pullback tensor comparison, read through the degree-zero
normalisation on both sides. -/
def higherDirectImageTensorMapZero :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj F)).obj G ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
          ((Scheme.Modules.pullback f).obj G)) :=
  tensorMapZeroFactor f F G ≫
    ((directImageZeroIso f).app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
        ((Scheme.Modules.pullback f).obj G))).inv

/-- **The canonical map is the underived one.** Read through the degree-zero normalisation of its
target, `higherDirectImageTensorMapZero` is `projectionFormulaMap` precomposed with the
normalisation of its source. This rules out multiplying the map by an automorphism. -/
theorem higherDirectImageTensorMapZero_comp_directImageZeroIso :
    higherDirectImageTensorMapZero f F G ≫
        ((directImageZeroIso f).app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
            ((Scheme.Modules.pullback f).obj G))).hom =
      tensorMapZeroFactor f F G :=
  (Iso.eq_comp_inv _).mp rfl

/-- The normalised underived map is invertible exactly when the underived map is. -/
private theorem isIso_tensorMapZeroFactor_iff :
    IsIso (tensorMapZeroFactor f F G) ↔ IsIso (projectionFormulaMap f.toLRSHom.toShHom F G) :=
  have e := isIso_tensorSheafMap _ _ (((directImageZeroIso f).app F).isIso_hom) (IsIso.id G)
  ⟨fun h => @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ e h,
    fun h => @IsIso.comp_isIso _ _ _ _ _ _ _ e h⟩

/-- The normalised underived map is invertible as soon as the underived map is. -/
theorem isIso_tensorMapZeroFactor
    (h : IsIso (projectionFormulaMap f.toLRSHom.toShHom F G)) :
    IsIso (tensorMapZeroFactor f F G) :=
  (isIso_tensorMapZeroFactor_iff f F G).2 h

/-- **Invertibility of the degree-zero comparison reduces to the underived projection formula.**
The degree-zero normalisation is an isomorphism, so conjugating by it changes nothing. -/
theorem isIso_higherDirectImageTensorMapZero
    (h : IsIso (projectionFormulaMap f.toLRSHom.toShHom F G)) :
    IsIso (higherDirectImageTensorMapZero f F G) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ (isIso_tensorMapZeroFactor f F G h)
    (Iso.isIso_inv _)

/-- **The converse reduction**: the underived projection formula follows from the degree-zero one.
Together with `isIso_higherDirectImageTensorMapZero` this says the degree-zero statement is
equivalent to the underived one and so does not weaken it. -/
theorem isIso_projectionFormulaMap_of_isIso_higherDirectImageTensorMapZero
    (h : IsIso (higherDirectImageTensorMapZero f F G)) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom F G) := by
  refine (isIso_tensorMapZeroFactor_iff f F G).1 ?_
  rw [← higherDirectImageTensorMapZero_comp_directImageZeroIso f F G]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h
    (Iso.isIso_hom _)

/-- **The degree-zero comparison is invertible for a closed immersion**, with no hypothesis on
either module. The underived statement is
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`, whose forward map is the
canonical one by `closedImmersionProjectionFormulaIso_hom`. -/
theorem isIso_higherDirectImageTensorMapZero_of_isClosedImmersion
    [AlgebraicGeometry.IsClosedImmersion f] :
    IsIso (higherDirectImageTensorMapZero f F G) :=
  isIso_higherDirectImageTensorMapZero f F G
    (closedImmersionProjectionFormulaIso f F G).isIso_hom

/-- **The degree-zero comparison is invertible for an arbitrary morphism of schemes when the
module on the target is trivial.** This is the rank-one case of [Stacks, Tag 01E8] in degree
zero; the underived statement is
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_iso_structureModule`. -/
theorem isIso_higherDirectImageTensorMapZero_of_iso_structureModule
    (e : structureModule Y.toRingedSpace ≅ G) :
    IsIso (higherDirectImageTensorMapZero f F G) :=
  isIso_higherDirectImageTensorMapZero f F G
    (isIso_projectionFormulaMap_of_iso_structureModule f.toLRSHom.toShHom F e)

/-- **The isomorphism `R^0 f_*(F ⊗_{𝒪_X} f^* G) ≅ R^0 f_* F ⊗_{𝒪_Y} G`**, together with the
identification of its inverse with the canonical map, so that the identification is by a named
morphism and not by an unspecified isomorphism of objects. -/
def higherDirectImageTensorIsoZero
    (h : IsIso (projectionFormulaMap f.toLRSHom.toShHom F G)) :
    { e : ((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
            ((Scheme.Modules.pullback f).obj G)) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj F)).obj G //
      e.inv = higherDirectImageTensorMapZero f F G } :=
  haveI : IsIso (higherDirectImageTensorMapZero f F G) :=
    isIso_higherDirectImageTensorMapZero f F G h
  ⟨(asIso (higherDirectImageTensorMapZero f F G)).symm, rfl⟩

/-- **Conclusion (b) of [Stacks, Tag 0EX3] in degree zero.** The canonical map of this file,
granted the canonicity condition of `TensorComparison.lean` and the underived projection formula,
supplies the isomorphism of conclusion (b) together with the characterisation of its inverse.

The canonicity condition is the only hypothesis that is not discharged somewhere in the tree:
`isIso_higherDirectImageTensorMapZero_of_isClosedImmersion` and
`isIso_higherDirectImageTensorMapZero_of_iso_structureModule` supply the other one. -/
def topDirectImageTensorComparisonZero
    (hc : IsHigherDirectImageTensorMap f F G 0 (higherDirectImageTensorMapZero f F G))
    (h : IsIso (projectionFormulaMap f.toLRSHom.toShHom F G)) :
    { e : ((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
            ((Scheme.Modules.pullback f).obj G)) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj F)).obj G //
      IsHigherDirectImageTensorMap f F G 0 e.inv } :=
  haveI : IsIso (higherDirectImageTensorMapZero f F G) :=
    isIso_higherDirectImageTensorMapZero f F G h
  topDirectImageTensorComparisonOfIsIso f F G 0 (higherDirectImageTensorMapZero f F G) hc

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
