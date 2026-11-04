module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorAdditive
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The norm of invertible modules, bundled with its Picard-group homomorphism

Let `f : X ⟶ Y` be a finite morphism of schemes carrying a norm `N` of degree `d` on functions
(`Stacks.Norm.MorphismNorm`, Tag 0BD1). This file bundles the object-level norm of
`StacksFrontier/AlgebraicGeometry/NormInvertible/Basic.lean` together with the induced
homomorphism of Picard groups, which is the shape in which
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) states its conclusion: *there
exists a homomorphism of abelian groups* `Norm_f : Pic(X) → Pic(Y)` *such that*
`Norm_f(f^*𝒩) ≅ 𝒩^{⊗ d}` *for every invertible* `𝒪_Y`-*module* `𝒩`.

## Main definitions

* `Stacks.Divisors.NormPicardData`: the norm of invertible modules, its action on local
  generators, and the induced homomorphism `Pic(X) → Pic(Y)` with the law identifying it on
  classes.
* `Stacks.Divisors.normPicardData`: the construction of those data from a norm on functions.
* `Stacks.Divisors.HasNormPullbackPower`: Tag 0BCY's *second* clause, the pullback--power
  formula, as a property of a candidate homomorphism. It is a definition, not a theorem; that it
  holds of `normPicardData`'s homomorphism is proved downstream, in
  `StacksFrontier/AlgebraicGeometry/NormInvertible/PullbackPower.lean`.

## Main results

* `Stacks.Divisors.isInvertible_modulePullback_of_isInvertible`: Tag 0B8L in the spelling the
  Picard group is stated at, with invertibility as a hypothesis rather than an instance.
* `Stacks.Divisors.normPicardData_picardMap_picardClass`: the Picard homomorphism of
  `normPicardData` sends the class of `L` to the class of its norm.

## Where the two clauses of Tag 0BCY are proved

Tag 0BCY has two clauses. The first — *a homomorphism of abelian groups exists* — is
`Stacks.Divisors.exists_normPicardAddMonoidHom`
(`StacksFrontier/AlgebraicGeometry/NormInvertible/TensorAdditive.lean`), which carries the
`@[stacks 0BCY "the homomorphism of abelian groups"]` attribute; `normPicardData` below is that
homomorphism packaged with the object-level data that produced it. The second clause —
`Norm_f(f^*𝒩) ≅ 𝒩^{⊗ d}` — is what `HasNormPullbackPower` states, and it is proved of
`normPicardData`'s homomorphism by `Stacks.Divisors.hasNormPullbackPower_normPicardData`
(`StacksFrontier/AlgebraicGeometry/NormInvertible/PullbackPower.lean`). Its proof takes a generating
section of `f^*𝒩` over the inverse image of a chart from one of `𝒩`, and one of `𝒩^{⊗ d}` by
iterating `Stacks.SheafOfModules.tmulGenerator`; the comparison is then
`Stacks.SheafOfModules.isoOfChartGenerators` with the ratio identity
`Stacks.Divisors.normUnitsMap_pullback`.

## Implementation notes

The Picard group, Picard classes, tensor powers and pullbacks of invertible modules are written
at `Stacks.SheafOfModules.PicardGroup`, `Stacks.SheafOfModules.picardClass`,
`Stacks.SheafOfModules.TensorPower.tensorPower` (with
`Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower`) and
`Stacks.RingedSpace.isInvertible_modulePullback`.

**Which `tensorPower`.** Two declarations named `tensorPower` carry `@[stacks 01CU]` with the
same body in different namespaces, distinguished only by which Tag 01CS invertibility class
their instance argument uses: `Stacks.SheafOfModules.TensorPower.tensorPower` synthesizes from
`Stacks.SheafOfModules.IsInvertible`, and `Stacks.SheafOfModules.Invertible.tensorPower` from
`AlgebraicGeometry.SheafOfModules.IsInvertible`. The Picard group's `InvertibleModules`
subcategory carries the former, so that is the one this file's statements can synthesize and the
one `HasNormPullbackPower` keys on.

`X.picardGroup` is used for the group itself, because
`StacksFrontier/AlgebraicGeometry/PicardGroup/Scheme.lean` fixes there the one spelling of the
sheaf condition through which instance search finds `AddCommGroup`; it unfolds to
`Stacks.SheafOfModules.PicardGroup X.presheaf
(Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf)`. The
characterizing law is stated at `picardClass X.presheaf (structureSheaf X.sheaf).property`, the
spelling `exists_normPicardAddMonoidHom` uses; the two sheaf-condition proofs prove the same
proposition and so are definitionally equal.

The invertibility side condition is the substitution `Basic.lean` already makes:
`Stacks.Divisors.HasTrivializingTargetCover` in place of an invertibility instance, discharged
for a finite morphism by
`Stacks.Divisors.hasTrivializingTargetCover_of_isFinite_of_isInvertible`. So the fields below
take invertibility and convert, rather than taking the cover.

`isInvertible_modulePullback_of_isInvertible` crosses the two Tag 01CS classes once, through
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, because Tag 0B8L is proved for the
`AlgebraicGeometry` class at the scheme-level spelling while the Picard group wants the `Stacks`
one; `Stacks.RingedSpace.isInvertible_modulePullback` applied directly fails to synthesize its
instance at `Y.sheaf.obj`.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0BD1](https://stacks.math.columbia.edu/tag/0BD1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-! ### The bundled data -/

/-- **The data of Stacks Tag 0BCY**: the norm of an invertible module, its action on local
generators, and the induced homomorphism of Picard groups together with the law that identifies
it on classes.

Invertibility of `L` is replaced by the trivializing target cover it is used through. The
pullback--power clause is not a field here; it is `HasNormPullbackPower` below. -/
structure NormPicardData (f : X ⟶ Y) [IsFinite f] (d : ℕ) (N : MorphismNorm f d) extends
    NormInvertibleData f N.toMorphismNormMap where
  /-- The homomorphism of abelian groups `Pic(X) → Pic(Y)` induced by the norm. -/
  picardMap : X.picardGroup →+ Y.picardGroup
  /-- The Picard homomorphism is induced by the object-level norm: it takes the class of an
  invertible module to the class of its norm. -/
  picardMap_picardClass (L : X.Modules)
      (hL : IsInvertible X.presheaf (structureSheaf X.sheaf).property L) :
    picardMap (picardClass X.presheaf (structureSheaf X.sheaf).property L hL) =
      picardClass Y.presheaf (structureSheaf Y.sheaf).property (obj L)
        (obj_invertible L (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL))

/-- **The norm construction of invertible modules and Picard classes induced by a norm on
functions**, in the clauses of Tag 0BCY that are proved: the object-level norm with its action on
local generators, and the homomorphism of Picard groups. -/
@[ega "II 6.5.2"]
noncomputable def normPicardData (f : X ⟶ Y) [IsFinite f] (d : ℕ) (N : MorphismNorm f d) :
    NormPicardData f d N where
  toNormInvertibleData := normInvertibleData f N.toMorphismNormMap
  picardMap := (exists_normPicardAddMonoidHom f N).choose
  picardMap_picardClass L hL := (exists_normPicardAddMonoidHom f N).choose_spec L hL

/-- The norm data underlying `normPicardData f d N` is `normInvertibleData f N.toMorphismNormMap`.
-/
@[simp]
theorem normPicardData_toNormInvertibleData (f : X ⟶ Y) [IsFinite f] (d : ℕ)
    (N : MorphismNorm f d) :
    (normPicardData f d N).toNormInvertibleData = normInvertibleData f N.toMorphismNormMap :=
  rfl

/-- The Picard homomorphism of the norm sends the class of `L` to the class of the norm of `L`,
in the spelling of `Stacks.Divisors.normInvertible`. -/
theorem normPicardData_picardMap_picardClass (f : X ⟶ Y) [IsFinite f] {d : ℕ}
    (N : MorphismNorm f d) (L : X.Modules)
    (hL : IsInvertible X.presheaf (structureSheaf X.sheaf).property L) :
    (normPicardData f d N).picardMap
        (picardClass X.presheaf (structureSheaf X.sheaf).property L hL) =
      picardClass Y.presheaf (structureSheaf Y.sheaf).property
        (normInvertible f N.toMorphismNormMap L)
        (isInvertible_normInvertible f N.toMorphismNormMap L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)) :=
  (normPicardData f d N).picardMap_picardClass L hL

/-! ### The pullback--power clause -/

/-- **Stacks Project, Tag 0B8L** in the spelling the Picard group is stated at: the pullback of
an invertible `𝒪_Y`-module along a morphism of schemes is an invertible `𝒪_X`-module, with
invertibility taken as a hypothesis rather than an instance.

This is `Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback` crossed once through
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
theorem isInvertible_modulePullback_of_isInvertible (f : X ⟶ Y) (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheaf Y.sheaf).property L) :
    IsInvertible X.presheaf (structureSheaf X.sheaf).property
      ((modulePullback f.toLRSHom.toShHom).obj L) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Y.IsSheaf) L :=
    (isInvertible_iff_algebraicGeometry _ _ L).mp hL
  (isInvertible_iff_algebraicGeometry _ _ _).mpr
    (Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback f.toLRSHom.toShHom L)

/-- **Tag 0BCY's pullback--power clause**, as a property of a candidate homomorphism
`F : Pic(X) → Pic(Y)`: the class of the pullback of an invertible `𝒪_Y`-module `L` is sent to the
class of the `d`-fold tensor power of `L`.

It is stated with `Stacks.SheafOfModules.picardClass`,
`Stacks.SheafOfModules.TensorPower.tensorPower` and
`Stacks.Divisors.isInvertible_modulePullback_of_isInvertible`. That it holds of
`normPicardData`'s homomorphism is `Stacks.Divisors.hasNormPullbackPower_normPicardData`. -/
def HasNormPullbackPower (f : X ⟶ Y) (d : ℕ) (F : X.picardGroup →+ Y.picardGroup) : Prop :=
  ∀ (L : Y.Modules) (hL : IsInvertible Y.presheaf (structureSheaf Y.sheaf).property L),
    letI := hL
    letI := TensorPower.isEquivalence_tensorRightFunctor Y.presheaf
      (structureSheaf Y.sheaf).property L
    F (picardClass X.presheaf (structureSheaf X.sheaf).property
        ((modulePullback f.toLRSHom.toShHom).obj L)
        (isInvertible_modulePullback_of_isInvertible f L hL)) =
      picardClass Y.presheaf (structureSheaf Y.sheaf).property
        (TensorPower.tensorPower Y.presheaf (structureSheaf Y.sheaf).property L (d : ℤ))
        (TensorPower.isInvertible_tensorPower Y.presheaf
          (structureSheaf Y.sheaf).property L (d : ℤ))

end Stacks.Divisors

end
