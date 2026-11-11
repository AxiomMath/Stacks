module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived pushforward along a morphism of ringed topoi commutes with derived limits

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi.  Tag 0A07 says that `Rf_*`
commutes with `R\lim`: if a distinguished triangle exhibits `L` as the derived limit of a
countable inverse system `(K_n)` of objects of `D(𝒪)`, then `Rf_* L` is the derived limit of the
system `(Rf_* K_n)`.

## The argument

This is the source's alternate proof, which it gives for a topos with enough points and which is
in fact available in general: the derived limit sits in a distinguished triangle
`R\lim K_n ⟶ ∏ K_n ⟶ ∏ K_n`, and `Rf_*` is exact, so it suffices that `Rf_*` commute with the
countable products of `D(𝒪)`.  Those products are *not* the termwise products of complexes, but
`Rf_*` is a right adjoint — by Tag 07A6, whose pullback side is now unconditional — and a right
adjoint preserves every limit.  The abstract form of this is
`Stacks.Injectives.isDerivedLimit_map_rightAdjoint`, and the whole content of this file is to
supply its three instance hypotheses at `Rf_*`.

The first proof the source gives, through the diagram of topoi over `C × ℕ`, is not used: it
needs the comparison of `R\lim` along the two projections, which is heavier than the adjunction
argument and buys nothing here, since the adjunction is available for every morphism of ringed
topoi.

## Main results

* `Stacks.Cohomology.DerivedPushforwardOnRingedTopoi.isDerivedLimit_map_derivedPushforward`:
  the special case of a morphism of ringed topoi presented by a morphism of ringed sites
  (`RingedToposSiteHom` with `f.u` a morphism of sites).  Tag 0A07 itself, for an arbitrary
  morphism of ringed topoi, is
  `Stacks.Cohomology.DerivedPushforward.isDerivedLimit_map_derivedPushforward` in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/DerivedLimitsOfToposHom.lean`.

## Implementation notes

*The two statements.*  The ringed-site version takes `f : RingedToposSiteHom X Y` together
with `hmos : f.u.IsMorphismOfSites Y.J X.J`, because its adjunction `Lf^* ⊣ Rf_*` is the one of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean`,
built from a continuous functor of sites; it is therefore only the case of Tag 0A07 in which the
morphism of topoi comes from a morphism of sites.  The tagged statement takes an arbitrary
`f : RingedToposHom X Y` (Tag 01D3, part (2)) and gets right adjointness from
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`, which needs no hypothesis on
`f`.  Its only extra hypotheses are the instances making the module categories and their
sheafifications exist, and `UnivLE.{u, w}`, `UnivLE.{v, w}` (site of `X` below its module
universe), under which `Mod(𝒪)` is Grothendieck abelian
(`SheafOfModules.isGrothendieckAbelian_of_univLE`), so that `Rf_*` exists.

*Reuse of the abstract lemma.*  The ringed-*space* analogue, Tag 0BKP
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isDerivedLimit_map_derivedPushforward`),
inlines the product argument rather than calling
`Stacks.Injectives.isDerivedLimit_map_rightAdjoint`; this file calls the abstract lemma, so the
five lines of the argument are not written a second time.  The three instances it asks for are
the commutation with shifts of a right derived functor, triangulatedness
(`Stacks.Injectives.rightDerivedFunctor_isTriangulated`, which needs `Mod(𝒪)` to be Grothendieck
abelian) and right adjointness, which is the adjunction of Tag 07A6 at the K-flat resolving
datum.

## References

* [Stacks Project, Tag 0A07](https://stacks.math.columbia.edu/tag/0A07)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace Stacks.Cohomology.DerivedPushforwardOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

include hmos in
/-- Derived pushforward along a morphism of ringed topoi *presented by a morphism of sites*
(`f : RingedToposSiteHom X Y` with `f.u` a morphism of sites, all universes equal) commutes with
derived limits.  This is the special case of Stacks 0A07 in which the morphism of topoi comes
from a continuous functor of the underlying sites; the statement for an arbitrary morphism of
ringed topoi is `Stacks.Cohomology.DerivedPushforward.isDerivedLimit_map_derivedPushforward`,
which carries the tag. -/
theorem isDerivedLimit_map_derivedPushforward
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ (derivedPushforward f).obj (K.obj ⟨n⟩)),
      @IsDerivedLimit
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        _ _ _ _ _ _
        (K ⋙ derivedPushforward f) h ((derivedPushforward f).obj L) := by
  have _ := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  have _ : (derivedPushforward f).IsRightAdjoint :=
    (derivedPullbackPushforwardAdjunctionOfKFlat f hmos fun _ ↦
      pullbackInvertsQuasiIso_isKFlat f hmos).isRightAdjoint
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) ℤ
  have _ := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have _ : (derivedPushforward f).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated f.pushforwardTopos
      (derivedPushforward f) (derivedPushforwardUnit f)
  exact Stacks.Injectives.isDerivedLimit_map_rightAdjoint (derivedPushforward f) K L hL

end Stacks.Cohomology.DerivedPushforwardOnRingedTopoi

end
