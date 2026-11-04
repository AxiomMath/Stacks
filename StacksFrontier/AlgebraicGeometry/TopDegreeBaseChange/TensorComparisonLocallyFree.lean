module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Locality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationInhabitant
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonAffine
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonZero

/-!
# The degree-zero tensor comparison at a finite locally free module on the target

`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TensorComparisonZero.lean` builds the
canonical map of conclusion (b) of [Stacks, Tag 0EX3] in degree zero,

`R^0 f_* F ⊗_{𝒪_Y} G ⟶ R^0 f_*(F ⊗_{𝒪_X} f^* G)`,

for an arbitrary morphism of schemes and arbitrary modules, and reduces its invertibility to the
invertibility of the underived map
`Stacks.AffineProjectionFormula.projectionFormulaMap`. Two hypotheses are then left over: the
canonicity condition `IsHigherDirectImageTensorMap`, and invertibility of the underived map,
which that file could supply only for a closed immersion or for a module on the target isomorphic
to the structure sheaf.

`StacksFrontier/AlgebraicGeometry/ProjectionFormula/Locality.lean` has since proved the underived
map invertible **whenever the module on the target is free of finite rank on each member of an
open covering**, with no hypothesis on the morphism and none on the module upstairs. This file
feeds that into the degree-zero comparison, so the second hypothesis is discharged on a class of
modules that contains every rank and is closed under passing to a covering, and the canonicity
condition is the only hypothesis that remains.

## Main results

All of the following live in the namespace
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isIso_higherDirectImageTensorMapZero_of_cover_restrict_free` and
  `isIso_higherDirectImageTensorMapZero_of_restrict_locally_free`: **the degree-zero comparison is
  invertible when the module on the target is free of finite rank locally**, from a covering or
  from pointwise data, for an arbitrary morphism of schemes and an arbitrary module upstairs.
* `isIso_higherDirectImageTensorMapZero_freeStructureModule`: the same at `G = 𝒪_Y^{⊕ J}` for an
  arbitrary finite `J`, obtained by instantiating the covering hypothesis at the one-member
  covering. This is what shows the hypotheses above are satisfiable at **every** finite rank and
  not only at rank one.
* `higherDirectImageTensorIsoZero_of_cover_restrict_free`: the resulting isomorphism, carrying the
  identification of its inverse with the canonical map.
* `topDirectImageTensorComparisonZeroLocallyFree`: **conclusion (b) of [Stacks, Tag 0EX3] in
  degree zero at a finite locally free module on the target**, with the canonicity condition as
  the only hypothesis left.
* `topDirectImageTensorComparisonAffineLocallyFree`: and in **every** degree along an affine
  morphism with quasi-coherent modules, the canonicity condition being required only in degree
  zero because in positive degree both sheaves vanish
  (`topDirectImageTensorComparisonPos`).
* `topDirectImageTensorComparisonSituationLocallyFree`: the same statement read at the degree `d`
  of a `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` built from an affine morphism with
  `d = 0`, which is the shape conclusion (b) is stated in and the only non-degenerate degree of
  those situations.
* `not_isZero_rightDerivedPlusZero_unit`: **the object being compared is not zero.** For a source
  carrying a nonzero global function, `R^0 f_* 𝒪_X` is nonzero, so none of the statements above is
  a statement about a zero object.

## Implementation notes

*What the hypothesis on the module says.* It is an isomorphism of the restriction of `G` with the
restriction of `𝒪_Y^{⊕ J}` on each member of a covering, with `J` allowed to vary from member to
member — `Stacks.AffineProjectionFormula.openRestrictModule` and `freeStructureModule` are the
spellings of those two restrictions that
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/Locality.lean` fixes. It is stated as data
rather than through a predicate for the reason recorded there: of the several classes of that
name in this repository, the ones phrased through local generators data over the localized site
would have to be bridged to a covering of opens together with a biproduct indexed by a type in
`Type`, and that bridge does not exist.

*Nothing here forces the module on the target to be the unit.* The hypothesis mentions the
structure sheaf only through `𝒪_Y^{⊕ J}` for an index type that is an argument, and
`isIso_higherDirectImageTensorMapZero_freeStructureModule` exhibits the whole hypothesis set
satisfied at an arbitrary finite `J`. Together with `not_isZero_rightDerivedPlusZero_unit` that
locates the statements away from the two degenerate readings a degree-zero tensor comparison
admits: a comparison of two zero sheaves, and a comparison in which the tensor factor is the unit
and the projection formula is an identity.

*The crossing between the two spellings of a sheaf of modules on a scheme happens at argument
positions.* `AlgebraicGeometry.Scheme.Modules` is a `def` for
`SheafOfModules (Stacks.RingedSpace.structureRingSheaf _)` and instance search does not cross
between them, but an application does, because there the elaborator checks against an expected
type. So `G : Y.Modules` is passed to `openRestrictModule` with no cure at all, and only the
reverse direction — a biproduct of structure modules used where a `Y.Modules` is expected — needs
`show Y.Modules from`. No transparency option and no scoped compiler option is used.

*No tag attribute.* Conclusion (b) of [Stacks, Tag 0EX3] is about the top degree `d` of a
situation, with quasi-coherence as the hypothesis on both modules; what is proved here is degree
zero, under a finite-local-freeness hypothesis on the module on the target that the tag does not
carry, and with the canonicity condition as an undischarged hypothesis. Nor does this cover
[Stacks, Tag 01E8], which asks for every `q ≥ 0` and for an isomorphism in `D^+(Y)`. So no
`stacks` attribute is attached to any declaration below, and the withholding of its predecessors
is respected and not removed.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AffineProjectionFormula Stacks.RingedSpace
open Stacks.RightDerivedPlus

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules)

/-! ### Invertibility of the degree-zero comparison -/

/-- **The degree-zero tensor comparison is invertible when the module on the target is free of
finite rank on each member of an open covering**, for an arbitrary morphism of schemes and an
arbitrary module upstairs.

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_higherDirectImageTensorMapZero` reduces this
to the underived projection formula, which is
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_cover_restrict_free`. -/
theorem isIso_higherDirectImageTensorMapZero_of_cover_restrict_free
    {I : Type*} (U : I → Y.Opens) (hU : IsOpenCover U) (J : I → Type) [∀ i, Finite (J i)]
    (e : ∀ i, openRestrictModule (U i) (freeStructureModule Y.toRingedSpace (J i)) ≅
      openRestrictModule (U i) G) :
    IsIso (higherDirectImageTensorMapZero f F G) :=
  isIso_higherDirectImageTensorMapZero f F G
    (isIso_projectionFormulaMap_of_cover_restrict_free f F G U hU J e)

/-- **The degree-zero tensor comparison is invertible at a finite locally free module on the
target**, from the pointwise data: an open neighbourhood of each point of the target on which the
module is isomorphic to the restriction of `𝒪_Y^{⊕ J}` for a finite `J`. -/
theorem isIso_higherDirectImageTensorMapZero_of_restrict_locally_free
    (J : Y.carrier → Type) [∀ y, Finite (J y)] (V : Y.carrier → Y.Opens) (hy : ∀ y, y ∈ V y)
    (e : ∀ y, openRestrictModule (V y) (freeStructureModule Y.toRingedSpace (J y)) ≅
      openRestrictModule (V y) G) :
    IsIso (higherDirectImageTensorMapZero f F G) :=
  isIso_higherDirectImageTensorMapZero f F G
    (isIso_projectionFormulaMap_of_restrict_locally_free f F G J V hy e)

/-- **The hypotheses above are satisfied at every finite rank.** At `G = 𝒪_Y^{⊕ J}` the
one-member covering by `⊤` and the identity isomorphism satisfy them, for an arbitrary finite
index type `J` and an arbitrary morphism of schemes, so nothing in them forces the module on the
target to have rank one or to be the structure sheaf.

The route is deliberately the covering one rather than
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_biproduct_structureModule`, which
would prove the same conclusion without instantiating the hypotheses that are at issue. -/
theorem isIso_higherDirectImageTensorMapZero_freeStructureModule (J : Type) [Finite J] :
    IsIso (higherDirectImageTensorMapZero f F
      (show Y.Modules from freeStructureModule Y.toRingedSpace J)) :=
  isIso_higherDirectImageTensorMapZero_of_cover_restrict_free f F _
    (fun _ : PUnit.{u + 1} => (⊤ : Y.Opens)) (IsOpenCover.mk iSup_const) (fun _ => J)
    (fun _ => Iso.refl _)

/-- **The isomorphism `R^0 f_*(F ⊗_{𝒪_X} f^* G) ≅ R^0 f_* F ⊗_{𝒪_Y} G` at a finite locally free
module on the target**, together with the identification of its inverse with the canonical map, so
that the identification is by a named morphism and not by an unspecified isomorphism of
objects. -/
def higherDirectImageTensorIsoZero_of_cover_restrict_free
    {I : Type*} (U : I → Y.Opens) (hU : IsOpenCover U) (J : I → Type) [∀ i, Finite (J i)]
    (e : ∀ i, openRestrictModule (U i) (freeStructureModule Y.toRingedSpace (J i)) ≅
      openRestrictModule (U i) G) :
    { iso : ((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
            ((Scheme.Modules.pullback f).obj G)) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj F)).obj G //
      iso.inv = higherDirectImageTensorMapZero f F G } :=
  higherDirectImageTensorIsoZero f F G
    (isIso_projectionFormulaMap_of_cover_restrict_free f F G U hU J e)

/-! ### Conclusion (b) of Tag 0EX3 -/

/-- **Conclusion (b) of [Stacks, Tag 0EX3] in degree zero at a finite locally free module on the
target.** For an arbitrary morphism of schemes, an arbitrary module upstairs, and a module on the
target which is free of finite rank on each member of an open covering, the canonical map is an
isomorphism and its inverse satisfies the canonicity condition.

The canonicity condition `hc` is the only hypothesis left. It is the statement that the
adjoint-transpose description of the canonical map and the local pure-tensor description agree;
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.eq_of_isHigherDirectImageTensorMap` shows at most
one map satisfies it, so what the conclusion asserts is a property of the two sheaves. -/
def topDirectImageTensorComparisonZeroLocallyFree
    (hc : IsHigherDirectImageTensorMap f F G 0 (higherDirectImageTensorMapZero f F G))
    {I : Type*} (U : I → Y.Opens) (hU : IsOpenCover U) (J : I → Type) [∀ i, Finite (J i)]
    (e : ∀ i, openRestrictModule (U i) (freeStructureModule Y.toRingedSpace (J i)) ≅
      openRestrictModule (U i) G) :
    { iso : ((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
            ((Scheme.Modules.pullback f).obj G)) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj F)).obj G //
      IsHigherDirectImageTensorMap f F G 0 iso.inv } :=
  topDirectImageTensorComparisonZero f F G hc
    (isIso_projectionFormulaMap_of_cover_restrict_free f F G U hU J e)

/-- **Conclusion (b) of [Stacks, Tag 0EX3] in every degree along an affine morphism of schemes
with quasi-coherent modules and a finite locally free module on the target.**

In positive degree both sheaves vanish by [Stacks, Tag 01XC] and the conclusion is
`topDirectImageTensorComparisonPos`, which needs nothing; in degree zero it is
`topDirectImageTensorComparisonZeroLocallyFree`. The canonicity condition is therefore demanded
only in degree zero, which is why it appears under a hypothesis `n = 0`. For an affine morphism
degree zero is also the only non-degenerate degree, by
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.isZero_topDirectImage_of_pos`. -/
def topDirectImageTensorComparisonAffineLocallyFree (n : ℕ)
    [AlgebraicGeometry.IsAffineHom f] [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hc : n = 0 → IsHigherDirectImageTensorMap f F G 0 (higherDirectImageTensorMapZero f F G))
    {I : Type*} (U : I → Y.Opens) (hU : IsOpenCover U) (J : I → Type) [∀ i, Finite (J i)]
    (e : ∀ i, openRestrictModule (U i) (freeStructureModule Y.toRingedSpace (J i)) ≅
      openRestrictModule (U i) G) :
    { iso : ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
            ((Scheme.Modules.pullback f).obj G)) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)).obj G //
      IsHigherDirectImageTensorMap f F G n iso.inv } :=
  match n with
  | 0 => topDirectImageTensorComparisonZeroLocallyFree f F G (hc rfl) U hU J e
  | (m + 1) => topDirectImageTensorComparisonPos f F G (m + 1) (Nat.succ_pos m)

/-- **Conclusion (b) of [Stacks, Tag 0EX3] at the degree of a top-degree base-change situation.**
The conclusions of that tag are about the degree `d` of a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` and about the base-changed morphism `f'`
of its cartesian square; this states conclusion (b) in exactly that shape, at the situations built
from an affine morphism with `d = 0`.

Those are the only situations anyone has exhibited, and `d = 0` is the only degree at which they
are not degenerate: `isZero_topDirectImage_of_pos` makes the compared object zero for `d > 0`,
while `not_isZero_topDirectImage_unit` makes it nonzero at `d = 0`. No hypothesis on `f'` is
needed — the affineness is used only to build the situation. -/
def topDirectImageTensorComparisonSituationLocallyFree {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsAffineHom f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (F' : X'.Modules) (G' : Y'.Modules)
    (hc : IsHigherDirectImageTensorMap f' F' G' 0 (higherDirectImageTensorMapZero f' F' G'))
    {I : Type*} (U : I → Y'.Opens) (hU : IsOpenCover U) (J : I → Type) [∀ i, Finite (J i)]
    (e : ∀ i, openRestrictModule (U i) (freeStructureModule Y'.toRingedSpace (J i)) ≅
      openRestrictModule (U i) G') :
    { iso : ((Scheme.Modules.pushforward f').rightDerivedPlus
            ((TopDegreeBaseChangeSituation.ofIsAffineHom f 0 g' f' g sq).d : ℤ)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).obj F').obj
            ((Scheme.Modules.pullback f').obj G')) ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.sheaf).obj
          (((Scheme.Modules.pushforward f').rightDerivedPlus
            ((TopDegreeBaseChangeSituation.ofIsAffineHom f 0 g' f' g sq).d : ℤ)).obj F')).obj G' //
      IsHigherDirectImageTensorMap f' F' G'
        (TopDegreeBaseChangeSituation.ofIsAffineHom f 0 g' f' g sq).d iso.inv } :=
  topDirectImageTensorComparisonZeroLocallyFree f' F' G' hc U hU J e

/-! ### The compared object is not zero -/

/-- **The degree-zero direct image of the structure sheaf is nonzero** as soon as the source
carries a nonzero global function. In degree zero the higher direct image is the ordinary one
(`directImageZeroIso`), and
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.not_isZero_pushforward_unit` says that is
nonzero because its sections over the whole target are the functions on the whole source.

This is what keeps the statements of this file away from the degenerate reading in which both
sheaves of conclusion (b) vanish and the isomorphism between them says nothing. -/
theorem not_isZero_rightDerivedPlusZero_unit [Nontrivial Γ(X, (⊤ : X.Opens))] :
    ¬ IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus ((0 : ℕ) : ℤ)).obj
      (show X.Modules from structureModule X.toRingedSpace)) := by
  intro h
  exact TopDegreeBaseChangeSituation.not_isZero_pushforward_unit f
    (h.of_iso ((directImageZeroIso f).app
      (show X.Modules from structureModule X.toRingedSpace)).symm)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
