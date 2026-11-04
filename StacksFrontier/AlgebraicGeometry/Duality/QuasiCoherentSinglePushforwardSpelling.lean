module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward

/-!
# `Rf_*` of a module in one degree: the quasi-coherent spelling against the plain one

The derived direct image of a scheme morphism is carried by the tree in two spellings which no
statement relates at the level of *objects*:

* `Stacks.Duality.derivedPushforward f : D(𝒪_X) ⥤ D(𝒪_Y)` together with
  `CategoryTheory.DerivedCategory.singleFunctor`, which is where the computations of the
  higher direct images of a blowup live, and which are written at
  `CategoryTheory.HasDerivedCategory.standard`;
* `Stacks.Duality.quasiCoherentDerivedPushforward f hpush` on `D_QCoh(𝒪_X)` together with
  `Stacks.Duality.singleQuasiCoherent`, which is the spelling the duality adjunction
  ([Stacks, Tag 0A9E]) forces, and which is written at the locally small model
  `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` — the adjunction needs the morphisms to
  live in a fixed universe.

This file supplies the missing object-level bridge, in two independent halves.

**The spelling half is definitional.** `quasiCoherentDerivedPushforward f hpush` is
`CategoryTheory.ObjectProperty.lift` of `ι ⋙ derivedPushforward f`, so the underlying object of
its value at `K` *is* `(derivedPushforward f).obj K.obj`; and `singleQuasiCoherent F hF n` carries
`(DerivedCategory.singleFunctor X.Modules n).obj F` as its underlying object. Both equations hold
by `rfl`. They were already relied on inside proofs — `Stacks.Duality.standardLerayIso`,
`…QuasiAffineQuasiCoherent.isZero_of_isZero_quasiCoherentDerivedPushforward`,
`Stacks.Duality.isLE_derivedPushforwardSections_single` and
`AlgebraicGeometry.Curves.SerreDuality` all cross them by type ascription — but were never
stated, so nothing could be *applied* across the two spellings. Since the inclusion of a full
subcategory is fully faithful, naming them turns an isomorphism of plain derived objects into an
isomorphism in `D_QCoh`, which is the form a consumer meets.

**The model half is not definitional** and is where the work is. It is the comparison
equivalence `StacksDraft.DerivedModel.modelEquiv` of the two models, under which `Rf_*` and the
single functor are both preserved, by
`StacksDraft.DerivedModel.schemeDerivedPushforwardStandardIso` and
`StacksDraft.DerivedModel.modelSingleFunctorIso`.

## Main results

The elided prefix is `Stacks.Duality`.

* `quasiCoherentDerivedPushforward_obj_obj` and
  `quasiCoherentDerivedPushforward_obj_singleQuasiCoherent_obj`: the spelling half, as equations.
* `isoSingleQuasiCoherentOfIsoSingleFunctor`: **an isomorphism
  `Rf_*(F[-n]) ≅ G[-n]` in `D(𝒪_Y)` is an isomorphism
  `Rf_*(F[-n]) ≅ G[-n]` in `D_QCoh(𝒪_Y)`**, at one and the same model.
* `derivedPushforward_eq_schemeDerivedPushforward` and
  `derivedPushforward_eq_derivedPushforwardModules`: the three names the tree uses for `Rf_*` on
  a scheme denote one functor.
* `StandardModel.derivedPushforwardSingleFunctorLocallySmallIso`: **the model half** — the
  computation of `Rf_*(F[-n])` at the standard model, read at the locally small model.
* `StandardModel.isoSingleQuasiCoherentOfStandardIso`: **the bridge** — a computation of
  `Rf_*(F[-n])` performed at the standard model with the plain derived category produces the
  isomorphism in `D_QCoh(𝒪_Y)` at the locally small model.

## Implementation notes

The two models are named by explicit `@`-applications rather than by juggling the priority of
`CategoryTheory.HasDerivedCategory.standard`, so that in the statements below each side's model is
visible in its type. The one exception is the section carrying the two equalities of spellings of
`Rf_*`: `AlgebraicGeometry.schemeDerivedPushforward` and
`AlgebraicGeometry.derivedPushforwardModules` take their model from instance search, so the
locally small instances are erased there and the standard model installed, as in
`StacksFrontier/AlgebraicGeometry/Duality/ProperDualityTransportAffineBase.lean`.

**No Stacks tag is registered here.** Nothing here is the statement of a tag: the content is
that two spellings of one functor agree, and that the comparison of two models of the derived
category carries a computation from one to the other.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

universe w u

open CategoryTheory AlgebraicGeometry

namespace Stacks.Duality

/-! ### The spelling half, at one model -/

section OneModel

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **The underlying object of `Rf_*K` computed in `D_QCoh` is `Rf_*` of the underlying object of
`K`.** `Stacks.Duality.quasiCoherentDerivedPushforward` is
`CategoryTheory.ObjectProperty.lift` of `ι ⋙ Stacks.Duality.derivedPushforward f`, so this is an
unfolding; what it adds is that the two spellings can be *applied* to one another rather than only
composed. -/
theorem quasiCoherentDerivedPushforward_obj_obj
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (K : quasiCoherentDerivedCategory X) :
    ((quasiCoherentDerivedPushforward f hpush).obj K).obj =
      (derivedPushforward f).obj K.obj :=
  rfl

/-- **`Rf_*` of a quasi-coherent module placed in one degree, in the two spellings.** The
underlying object of `Rf_*(F[-n])` computed in `D_QCoh(𝒪_Y)` is `Rf_*` of `F[-n]` computed in
`D(𝒪_Y)`: `quasiCoherentDerivedPushforward_obj_obj` at
`Stacks.Duality.singleQuasiCoherent F hF n`, whose underlying object is
`CategoryTheory.DerivedCategory.singleFunctor` of `F` by
`Stacks.Duality.singleQuasiCoherent_obj`. -/
theorem quasiCoherentDerivedPushforward_obj_singleQuasiCoherent_obj
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℤ) :
    ((quasiCoherentDerivedPushforward f hpush).obj (singleQuasiCoherent F hF n)).obj =
      (derivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules n).obj F) :=
  rfl

/-- **A computation of `Rf_*(F[-n])` in `D(𝒪_Y)` is a computation in `D_QCoh(𝒪_Y)`.** Given an
isomorphism `Rf_*(F[-n]) ≅ G[-n]` of plain derived objects, with `F` and `G` quasi-coherent, the
same isomorphism holds between `Stacks.Duality.quasiCoherentDerivedPushforward f hpush` applied to
`Stacks.Duality.singleQuasiCoherent F hF n` and `singleQuasiCoherent G hG n`.

Both sides of the given isomorphism are the underlying objects of the two sides of the conclusion,
by `quasiCoherentDerivedPushforward_obj_singleQuasiCoherent_obj` and
`Stacks.Duality.singleQuasiCoherent_obj`, and the inclusion of a full subcategory is fully
faithful, so the isomorphism is the image of a unique isomorphism upstairs. -/
def isoSingleQuasiCoherentOfIsoSingleFunctor
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (F : X.Modules) (hF : F.IsQuasicoherent) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℤ)
    (e : (derivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules n).obj F) ≅
      (DerivedCategory.singleFunctor Y.Modules n).obj G) :
    (quasiCoherentDerivedPushforward f hpush).obj (singleQuasiCoherent F hF n) ≅
      singleQuasiCoherent G hG n :=
  (ObjectProperty.ι _).preimageIso e

end OneModel

/-! ### The three names of `Rf_*` on a scheme -/

section Spellings

attribute [-instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- **`Stacks.Duality.derivedPushforward` is `AlgebraicGeometry.schemeDerivedPushforward`.** Both
are the total right derived functor of termwise direct image followed by localization, the one
written at the level of schemes and the other at the level of the underlying ringed spaces, so
they are the same term. -/
theorem derivedPushforward_eq_schemeDerivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPushforward f = AlgebraicGeometry.schemeDerivedPushforward f :=
  rfl

/-- **`Stacks.Duality.derivedPushforward` is `AlgebraicGeometry.derivedPushforwardModules`.** The
same unfolding as `derivedPushforward_eq_schemeDerivedPushforward`, for the third of the tree's
names for `Rf_*` on a scheme; the quasi-compactness and quasi-separatedness carried by that
spelling play no part in the identification. -/
theorem derivedPushforward_eq_derivedPushforwardModules {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    derivedPushforward f = AlgebraicGeometry.derivedPushforwardModules f :=
  rfl

end Spellings

/-! ### The model half -/

namespace StandardModel

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A computation of `Rf_*(F[-n])` at the standard model, read at the locally small model.**

The comparison equivalence `StacksDraft.DerivedModel.modelEquiv` of the two models carries `Rf_*`
to `Rf_*` (`StacksDraft.DerivedModel.schemeDerivedPushforwardStandardIso`) and the single functor
to the single functor (`StacksDraft.DerivedModel.modelSingleFunctorIso`), so an isomorphism
`Rf_*(F[-n]) ≅ G[-n]` at the standard model becomes one at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

This is the half of the bridge that is not an unfolding: the two models have different morphism
universes, and only the comparison equivalence relates them. -/
def derivedPushforwardSingleFunctorLocallySmallIso (F : X.Modules) (G : Y.Modules) (n : ℤ)
    (e : (@derivedPushforward X Y f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _)).obj
        ((@DerivedCategory.singleFunctor X.Modules _ _
          (HasDerivedCategory.standard _) n).obj F) ≅
      (@DerivedCategory.singleFunctor Y.Modules _ _ (HasDerivedCategory.standard _) n).obj G) :
    (@derivedPushforward X Y f (Scheme.Modules.hasDerivedCategory X)
        (Scheme.Modules.hasDerivedCategory Y)).obj
      ((@DerivedCategory.singleFunctor X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) n).obj F) ≅
      (@DerivedCategory.singleFunctor Y.Modules _ _
        (Scheme.Modules.hasDerivedCategory Y) n).obj G :=
  ((@derivedPushforward X Y f (Scheme.Modules.hasDerivedCategory X)
        (Scheme.Modules.hasDerivedCategory Y)).mapIso
      ((StacksDraft.DerivedModel.modelSingleFunctorIso (HasDerivedCategory.standard X.Modules)
        (Scheme.Modules.hasDerivedCategory X) n).app F).symm) ≪≫
    ((StacksDraft.DerivedModel.schemeDerivedPushforwardStandardIso f).app
      ((@DerivedCategory.singleFunctor X.Modules _ _
        (HasDerivedCategory.standard _) n).obj F)).symm ≪≫
    (Scheme.Modules.derivedModelEquiv Y).functor.mapIso e ≪≫
    (StacksDraft.DerivedModel.modelSingleFunctorIso (HasDerivedCategory.standard Y.Modules)
      (Scheme.Modules.hasDerivedCategory Y) n).app G

/-- **The object-level bridge between the two spellings of `Rf_*` of a module in one degree.**
A computation `Rf_*(F[-n]) ≅ G[-n]` carried out at the standard model with the plain derived
category — which is where the computations of the higher direct images of a blowup are written —
yields the isomorphism

`Rf_*(F[-n]) ≅ G[-n]` in `D_QCoh(𝒪_Y)` at the locally small model,

which is the shape the duality adjunction of [Stacks, Tag 0A9E] forces on its consumers.

It is `StandardModel.derivedPushforwardSingleFunctorLocallySmallIso` — the crossing of the two
models — followed by `Stacks.Duality.isoSingleQuasiCoherentOfIsoSingleFunctor` — the crossing of
the two spellings, which is an unfolding and a full faithfulness. -/
def isoSingleQuasiCoherentOfStandardIso
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (F : X.Modules) (hF : F.IsQuasicoherent) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℤ)
    (e : (@derivedPushforward X Y f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _)).obj
        ((@DerivedCategory.singleFunctor X.Modules _ _
          (HasDerivedCategory.standard _) n).obj F) ≅
      (@DerivedCategory.singleFunctor Y.Modules _ _ (HasDerivedCategory.standard _) n).obj G) :
    (quasiCoherentDerivedPushforward f hpush).obj (singleQuasiCoherent F hF n) ≅
      singleQuasiCoherent G hG n :=
  isoSingleQuasiCoherentOfIsoSingleFunctor f hpush F hF G hG n
    (derivedPushforwardSingleFunctorLocallySmallIso f F G n e)

end StandardModel

end Stacks.Duality

end
