module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a derived internal hom

Let `(X, 𝒪_X)` be a ringed space, let `K, M ∈ D(𝒪_X)` and let `x ∈ X`.  Tag 0GM8 is the
assertion that the canonical map

`R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`

is an isomorphism when `K` is perfect, and also when `K` is pseudo-coherent and `M` is locally
bounded below.  The source proves it by presenting the point as the one-point ringed space
`Y = {x}` with structure sheaf `𝒪_{X,x}`: the inclusion `Y ⟶ X` is flat, the derived pullback
along it is the stalk and the derived internal hom of `Y` is `RHom` over the local ring, so
Tag 0GM7 applies verbatim.

This file sets up that presentation, `StalkPresentation`, and defines the displayed map from it as
the canonical map of Tag 08I3 along `Y ⟶ X` read through it.  `isIso_stalkSheafHomMap_iff` says
that for every presentation the displayed map is invertible exactly when the Tag 08I3 comparison
along `Y ⟶ X` is.  A presentation exists for every ringed space and every point:
`Stacks.Cohomology.DerivedInternalHomStalk.pointStalkPresentation` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTensorComparison`.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomStalk.stalkRing`: the local ring `𝒪_{X,x}`, in the
  spelling the stalk functor on sheaves of modules produces.
* `Stacks.Cohomology.DerivedInternalHomStalk.derivedStalk`: the derived stalk functor
  `D(𝒪_X) ⥤ D(𝒪_{X,x})`.
* `Stacks.Cohomology.DerivedInternalHomStalk.stalkDerivedHom`: `RHom_{𝒪_{X,x}}`, the internal
  hom of the canonical tensor–hom adjunction of Tag 0A63 on `D(𝒪_{X,x})`.
* `Stacks.Cohomology.DerivedInternalHomStalk.StalkPresentation`: the point `x` presented as the
  one-point ringed space `Y = {x}` over `X`, together with an identification of `D(𝒪_Y)` with
  `D(𝒪_{X,x})` carrying derived pullback to the derived stalk and the derived internal hom of
  `Y` to `RHom` over `𝒪_{X,x}`.
* `Stacks.Cohomology.DerivedInternalHomStalk.stalkSheafHomMap`: **the displayed map of
  Tag 0GM8**, `R𝓗om(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMap_iff`: the displayed map is
  invertible exactly when the canonical map of Tag 08I3 along `Y ⟶ X` is.
* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMap_of_tensorUnit`: the displayed
  map is invertible at a tensor unit `K`.

## References

* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedInternalHomPullback

namespace Stacks.Cohomology.DerivedInternalHomStalk

universe u

attribute [local instance] HasDerivedCategory.standard

-- The derived pullback and the derived internal hom name the structure sheaf of a ringed space
-- differently, by `structureSheafRing` and by `Stacks.SheafOfModules.Tensor.ringSheaf`; the two
-- are the same sheaf of rings by `rfl`, and the statements below mix them.
-- `structureSheafRing` is `@[instance_reducible]`, so it is already unfolded both by instance
-- search and at `implicit` transparency, but its reduct stops at an explicit-constructor
-- projection while `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`;
-- these two Mathlib definitions are the gap between them.  This is the list
-- `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility`
-- carries, and it is needed here for the same reason: every statement below applies a
-- declaration of that file to objects named at the `Modules` spelling.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (X : RingedSpace.{u, u}) (x : X.carrier)

/-! ### The local ring, the derived stalk and `RHom` over the local ring -/

/-- The local ring `𝒪_{X,x}`, in the spelling the stalk functor on sheaves of modules produces:
the `RingCat`-valued stalk at `x` of the sheaf of rings underlying the structure sheaf. -/
abbrev stalkRing : Type u :=
  ((TopCat.Presheaf.stalk (C := RingCat.{u})
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj x : RingCat.{u}) : Type u)

/-- The local ring `𝒪_{X,x}` is commutative.

This is `StacksDraft.StalkTensor.commRing_stalk_ringSheaf` at the structure sheaf of a ringed
space.  It is registered as a *local* instance only: the implementation notes of
`StacksFrontier.Topology.Sheaves.Modules.StalkTensor` record that a globally registered copy keyed
on a `RingedSpace` cannot coexist with the one keyed on a sheaf of commutative rings on
`Opens X`, the two getting stuck on the universe constraint of `TopCat.Sheaf` rather than
failing. -/
abbrev stalkCommRing : CommRing (stalkRing X x) :=
  StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x

attribute [local instance] stalkCommRing

/-- **The derived stalk functor** `D(𝒪_X) ⥤ D(𝒪_{X,x})`, named at the spelling of the category
of `𝒪_X`-modules that the derived internal hom and the derived pullback are stated at.

It is `AlgebraicGeometry.SheafOfModules.derivedStalkFunctor`, the functor induced on unbounded
derived categories by the exact stalk functor at `x`. -/
abbrev derivedStalk :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ⥤
      DerivedCategory (ModuleCat.{u} (stalkRing X x)) :=
  AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x

/-- `RHom_{𝒪_{X,x}}`, the internal hom of the canonical tensor–hom adjunction of Tag 0A63 on the
derived category of modules over the local ring `𝒪_{X,x}`. -/
abbrev stalkDerivedHom :
    (DerivedCategory (ModuleCat.{u} (stalkRing X x)))ᵒᵖ ×
        DerivedCategory (ModuleCat.{u} (stalkRing X x)) ⥤
      DerivedCategory (ModuleCat.{u} (stalkRing X x)) :=
  (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (stalkRing X x)).hom

/-! ### The point as a one-point ringed space -/

/-- **The point `x` presented as the one-point ringed space `Y = {x}` over `X`**, together with
the identification of `D(𝒪_Y)` with `D(𝒪_{X,x})`.

The underlying space is a single point lying over `x` and the induced map on stalks of the
structure sheaves is invertible, so the structure sheaf of `Y` is `𝒪_{X,x}` and the inclusion is
flat — which is the hypothesis case (2) of Tag 0GM7 uses.  The identification is required to
carry derived pullback along `Y ⟶ X` to the derived stalk and the derived internal hom of `Y` to
`RHom` over `𝒪_{X,x}`. One such
presentation, for every ringed space and every point, is
`Stacks.Cohomology.DerivedInternalHomStalk.pointStalkPresentation`. -/
structure StalkPresentation where
  /-- The one-point ringed space `Y = {x}`. -/
  space : RingedSpace.{u, u}
  /-- Its point. -/
  pt : space.carrier
  /-- The underlying space has no other point. -/
  unique_pt (p : space.carrier) : p = pt
  /-- The morphism `Y ⟶ X`. -/
  hom : space ⟶ X
  /-- It sends the point to `x`. -/
  base_pt : (ConcreteCategory.hom hom.hom.base) pt = x
  /-- The induced map on stalks of structure sheaves is invertible: the structure sheaf of `Y`
  is `𝒪_{X,x}`, and the morphism is flat. -/
  stalkMap_isIso : IsIso (hom.hom.stalkMap pt)
  /-- The identification of `D(𝒪_Y)` with `D(𝒪_{X,x})`. -/
  equiv : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules space) ≌
    DerivedCategory (ModuleCat.{u} (stalkRing X x))
  /-- Derived pullback along `Y ⟶ X`, read through the identification, is the derived stalk
  at `x`. -/
  stalkIso : derivedPullbackFunctor hom ⋙ equiv.functor ≅ derivedStalk X x
  /-- The identification carries the derived internal hom of `Y` to `RHom` over `𝒪_{X,x}`. -/
  homIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.derivedSheafHom space.sheaf) ⋙ equiv.functor ≅
      equiv.functor.op.prod equiv.functor ⋙ stalkDerivedHom X x

variable (P : StalkPresentation X x)
  (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))

/-- **The displayed map of Tag 0GM8**, `R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`.

It is the canonical map of Tag 08I3 along the inclusion `Y = {x} ⟶ X`, read through the
identification of `D(𝒪_Y)` with `D(𝒪_{X,x})`; this is the map the source proof of Tag 0GM8
uses. -/
def stalkSheafHomMap :
    (derivedStalk X x).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).obj M) ⟶
      (stalkDerivedHom X x).obj
        (op ((derivedStalk X x).obj K), (derivedStalk X x).obj M) :=
  (P.stalkIso.app (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op K)).obj M)).inv ≫
    P.equiv.functor.map (derivedPullbackSheafHomMap P.hom K M) ≫
      (P.homIso.app
            (op ((derivedPullbackFunctor P.hom).obj K),
              (derivedPullbackFunctor P.hom).obj M) ≪≫
          (stalkDerivedHom X x).mapIso
            (Iso.prod (P.stalkIso.app K).symm.op (P.stalkIso.app M))).hom

/-- **The displayed map of Tag 0GM8 is invertible exactly when the canonical map of Tag 08I3
along `Y = {x} ⟶ X` is.**

So the content of the two cases below does not depend on the presentation: it is the Tag 08I3
comparison that decides it, and that comparison is pinned where it is declared.  In particular
replacing any of the presentation's isomorphisms by its negative leaves both sides unchanged. -/
theorem isIso_stalkSheafHomMap_iff :
    IsIso (stalkSheafHomMap X x P K M) ↔ IsIso (derivedPullbackSheafHomMap P.hom K M) := by
  rw [stalkSheafHomMap, isIso_comp_left_iff, isIso_comp_right_iff]
  exact isIso_iff_of_reflects_iso _ P.equiv.functor

/-! ### The displayed map at a tensor unit -/

/-- **The displayed map at a tensor unit.**  For `K ∈ D(𝒪_X)` a unit for the derived tensor
product on `X` whose derived pullback to `Y = {x}` is a unit there, compatibly with the
monoidality comparison of Tag 079U, the displayed map

`R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`

is an isomorphism for every `M ∈ D(𝒪_X)`.  This is `isIso_stalkSheafHomMap_iff` together with
`Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_tensorUnit`;
`uX`, `uY` are the two unitors, `huX`, `huY` their naturality and `hcoh` the unitality of the
monoidality comparison. -/
theorem isIso_stalkSheafHomMap_of_tensorUnit
    (uX : ∀ W : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X),
      (internalHomTensorUncurried X).obj (W, K) ≅ W)
    (uY : ∀ W : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules P.space),
      (internalHomTensorUncurried P.space).obj
        (W, (derivedPullbackFunctor P.hom).obj K) ≅ W)
    (huX : ∀ (W W' : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) (g : W ⟶ W'),
      (internalHomTensorUncurried X).map (g ×ₘ 𝟙 K) ≫ (uX W').hom = (uX W).hom ≫ g)
    (huY : ∀ (W W' : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules P.space)) (g : W ⟶ W'),
      (internalHomTensorUncurried P.space).map
          (g ×ₘ 𝟙 ((derivedPullbackFunctor P.hom).obj K)) ≫ (uY W').hom = (uY W).hom ≫ g)
    (hcoh : ∀ W : DerivedCategory
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X),
      (pullbackTensorIso P.hom).hom.app (W, K) ≫
          (uY ((derivedPullbackFunctor P.hom).obj W)).hom =
        (derivedPullbackFunctor P.hom).map (uX W).hom) :
    IsIso (stalkSheafHomMap X x P K M) :=
  (isIso_stalkSheafHomMap_iff X x P K M).2
    (isIso_derivedPullbackSheafHomMap_of_tensorUnit P.hom K uX uY huX huY hcoh M)

end Stacks.Cohomology.DerivedInternalHomStalk

end
