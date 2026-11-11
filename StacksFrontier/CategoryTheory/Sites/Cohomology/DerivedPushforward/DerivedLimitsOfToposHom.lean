module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived pushforward along a morphism of ringed topoi commutes with derived limits

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be an arbitrary morphism of ringed topoi, in the two-field
sense of Tag 01D3, part (2): a morphism of the underlying topoi together with the structure map,
with no functor between the underlying sites.  Tag 0A07 says that `Rf_*` commutes with `R\lim`.

## The argument

The derived limit sits in a distinguished triangle `R\lim K_n ⟶ ∏ K_n ⟶ ∏ K_n`, and `Rf_*` is
exact; it is moreover a right adjoint, by Tag 07A6 in its unconditional form
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`, so it preserves the products of
`D(𝒪)`.  The abstract form of this is `Stacks.Injectives.isDerivedLimit_map_rightAdjoint`; this
file supplies its instance hypotheses at `Rf_*`.

## Main results

* `Stacks.Cohomology.DerivedPushforward.isDerivedLimit_map_derivedPushforward`: **Tag 0A07.**

## Implementation notes

The special case of a morphism of ringed topoi presented by a morphism of ringed sites is
`Stacks.Cohomology.DerivedPushforwardOnRingedTopoi.isDerivedLimit_map_derivedPushforward`, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/DerivedLimits.lean`.

The two `UnivLE` hypotheses place the site of the source below its module universe; under them
`Mod(𝒪)` is a Grothendieck abelian category (`SheafOfModules.isGrothendieckAbelian_of_univLE`),
which is what makes `Rf_*` exist.  They hold in particular when all universes agree.

## References

* [Stacks Project, Tag 0A07](https://stacks.math.columbia.edu/tag/0A07)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.DerivedPushforward

open Stacks.Cohomology.DerivedPullbackOfToposHom

universe v u w v' u' w'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
  SheafOfModules.isGrothendieckAbelian_of_univLE

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  [UnivLE.{u, w}] [UnivLE.{v, w}]

/-- **Stacks Project, Tag 0A07.**  Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed
topoi.  Then `Rf_*` commutes with `R\lim`: if a distinguished triangle
`L ⟶ ∏ K_n ⟶ ∏ K_n ⟶ L[1]` exhibits `L` as the derived limit of a countable inverse system
`(K_n)` of objects of `D(𝒪)`, then the product of the `Rf_* K_n` exists in `D(𝒪')` and `Rf_* L`
is the derived limit of the system `(Rf_* K_n)`.

Here `f` is an arbitrary morphism of ringed topoi in the two-field sense of Tag 01D3 (a morphism
of the underlying topoi together with the structure map), with no functor between the sites.
The proof is the source's adjunction argument: `Rf_*` is exact, and it is a right adjoint by
Tag 07A6 (`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`), so it preserves the
products of `D(𝒪)`; `Stacks.Injectives.isDerivedLimit_map_rightAdjoint` is the abstract form.
The two `UnivLE` hypotheses only place the site of `X` below its module universe, which is what
makes `Mod(𝒪)` a Grothendieck abelian category (`SheafOfModules.isGrothendieckAbelian_of_univLE`)
and hence `Rf_*` exist. -/
@[stacks 0A07 "for a morphism of ringed topoi in the two-field sense of Tag 01D3, part (2) --
a morphism of the underlying topoi together with the structure map, with no continuous functor
between the underlying sites; `R lim` is the derived limit `IsDerivedLimit` of a countable
inverse system, given by its defining distinguished triangle"]
theorem isDerivedLimit_map_derivedPushforward (f : RingedToposHom X Y)
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ (derivedPushforward (X := X) (Y := Y) f).obj (K.obj ⟨n⟩)),
      @IsDerivedLimit
        (DerivedCategory (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        _ _ _ _ _ _
        (K ⋙ derivedPushforward (X := X) (Y := Y) f) h
        ((derivedPushforward (X := X) (Y := Y) f).obj L) := by
  have _ : (derivedPushforward (X := X) (Y := Y) f).IsRightAdjoint :=
    (derivedAdjunction f).isRightAdjoint
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward (X := X) (Y := Y) f)
    ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward (X := X) (Y := Y) f).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated f.pushforwardModules
      (derivedPushforward (X := X) (Y := Y) f)
      ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
  exact Stacks.Injectives.isDerivedLimit_map_rightAdjoint
    (derivedPushforward (X := X) (Y := Y) f) K L hL

end Stacks.Cohomology.DerivedPushforward

end
