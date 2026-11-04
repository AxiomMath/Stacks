module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackEvenDegreeRing
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamFirstChernClassSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingPicardSequence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple

/-!
# The de Rham first Chern class on the Picard group of a scheme

For a morphism of schemes `p : X ⟶ S`, the de Rham first Chern class of Section 50.9
(Tag 0FLE) is an additive map `c₁^{dR} : Pic(X) ⟶ H^2_{dR}(X/S)`. It is formed by logarithmic
differentiation in the abelian-sheaf realization of de Rham cohomology; this file reads it on the
Picard group `Pic(X)` of `AlgebraicGeometry.Scheme.picardGroup` and in the module realization, in
which the cup product lives, and proves that it commutes with pullback along commutative squares
(Tag 0FMD).

## Main definitions

* `Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard`: `c₁^{dR} : Pic(X) →+ H^2_{dR}(X/S)`.

## Main results

* `Stacks.DeRhamBaseChange.deRhamPullbackSquare_deRhamFirstChernClassPicard`: **`c₁^{dR}`
  commutes with pullback**, `g'^*c₁^{dR}(ℒ) = c₁^{dR}(g'^*ℒ)`.

## References

* [Stacks Project, Section 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

universe u

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace Stacks.DeRhamBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The de Rham first Chern class `c₁^{dR} : Pic(X) ⟶ H^2_{dR}(X/S)`** (Section 0FLE), in the
realization of de Rham cohomology by derived global sections of modules: logarithmic
differentiation in the abelian-sheaf realization, read through the comparison of the two
realizations (Tag 01F1). -/
def deRhamFirstChernClassPicard (p : X ⟶ S) :
    X.picardGroup →+ AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) 2 :=
  (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras p)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))
      2).hom.hom.comp
    ((AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian (Scheme.Hom.deRhamAlgebras p)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).comp
      (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).toAddMonoidHom)

/-- **The de Rham first Chern class commutes with pullback** ([Stacks, Tag 0FMD]): for a
commutative square `g' ≫ f = f' ≫ g` of schemes and an invertible `𝒪_X`-module `ℒ`,
`g'^*c₁^{dR}(ℒ) = c₁^{dR}(g'^*ℒ)` in `H^2_{dR}(X'/S')`. -/
theorem deRhamPullbackSquare_deRhamFirstChernClassPicard (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    deRhamPullbackSquare g' f' f g w 2
        (deRhamFirstChernClassPicard f (Stacks.WeilCohomology.picardClassOf X L hL)) =
      deRhamFirstChernClassPicard f' (Stacks.WeilCohomology.picardClassOf X'
        ((Scheme.Modules.pullback g').obj L)
        (Stacks.WeilCohomology.isInvertible_pullback_obj g' L hL)) := by
  have h0 := Scheme.Hom.deRhamFirstChernClassAbelian_schemePullbackClassHom g' f f' g w
    (Stacks.WeilCohomology.picardClassOf X L hL)
  have h1 : Stacks.Picard.schemePullbackClassHom g' (Stacks.WeilCohomology.picardClassOf X L hL) =
      Stacks.WeilCohomology.picardClassOf X' ((Scheme.Modules.pullback g').obj L)
        (Stacks.WeilCohomology.isInvertible_pullback_obj g' L hL) :=
    Stacks.Picard.pullbackClass_classOf g'.toLRSHom.toShHom L _
  rw [deRhamPullbackSquare_apply]
  simp only [deRhamFirstChernClassPicard, AddMonoidHom.comp_apply, AddCommGrpCat.hom_comp,
    Iso.hom_inv_id_apply]
  exact congrArg _ ((congrArg (fun c =>
    AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian (Scheme.Hom.deRhamAlgebras f')
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))
      (Stacks.GluePicard.picardModelAddEquiv X'.toRingedSpace c)) h1).symm.trans h0).symm

end Stacks.DeRhamBaseChange
