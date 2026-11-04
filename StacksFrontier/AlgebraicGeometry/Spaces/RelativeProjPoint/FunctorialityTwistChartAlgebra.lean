module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebraPullbackComp
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlgebraMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistMap

/-!
# The chart maps `θ_n` of Stacks 085F are the components of a map of graded algebras

For a map of graded algebras `θ : r_ψ^*(⨁_n 𝒪(n)) ⟶ ι^*(⨁_n 𝒪(n))` on `U(ψ)` (Tag 07ZG) and a chart
`e : C ⟶ U(ψ)` with morphisms `a`, `b` lying over `r_ψ` and `ι`, the components
`a^*p^*𝒪(n) ⟶ b^*q^*𝒪(n)` of `e^*θ` are the components of one map of sheaves of graded algebras
on `C`; in particular they are multiplicative. This applies to the chart maps `θ_n` of Stacks 085F
on the charts of `U(ψ)`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistAlgebraHom`: `θ` read on a chart, as a map of
  sheaves of graded algebras.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistAlgebraHom_app`: its components are the maps
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_map_mul`: these components preserve
  products of homogeneous local sections.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.chartTwistMap_hom_eq_chartTwistAlgebraHom_app`:
  the chart map `θ_n` on `U(ψ) ×_X T` is the degree-`n` component of a map of sheaves of graded
  algebras, up to the identifications of the modules with the twists.

## References

* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp
open Stacks.RingedSpace (pullbackGradedAlgebra pullbackGradedAlgebraMap)

universe u

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

variable {S₀ : Scheme.{u}} {A B : SheafGradedAlgebra S₀} (ψ : SheafGradedAlgebraHom A B)
  {C P Q : Scheme.{u}} (a : C ⟶ P) (b : C ⟶ Q) (p : P ⟶ (relativeProj A).scheme)
  (q : Q ⟶ (relativeProj B).scheme) (e : C ⟶ ψ.relativeMapDomain.toScheme)
  (ha : a ≫ p = e ≫ relativeMapHom ψ) (hb : b ≫ q = e ≫ ψ.relativeMapDomain.ι)

/-- **A map of graded algebras on the twists over `U(ψ)`, read on a chart, as a map of sheaves of
graded algebras**: for `e : C ⟶ U(ψ)` and `a`, `b` lying over `r_ψ` and `ι` through `p`, `q`, the
map `a^*p^*(⨁_n 𝒪(n)) ⟶ b^*q^*(⨁_n 𝒪(n))` obtained from `e^*θ`. -/
def chartTwistAlgebraHom (θ : SheafOfModules.GradedAlgebra.Hom
      (pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom (twistAlgebra A))
      (pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom (twistAlgebra B))) :
    pullbackGradedAlgebra a.toLRSHom.toShHom
        (pullbackGradedAlgebra p.toLRSHom.toShHom (twistAlgebra A)) ⟶
      pullbackGradedAlgebra b.toLRSHom.toShHom
        (pullbackGradedAlgebra q.toLRSHom.toShHom (twistAlgebra B)) :=
  (pullbackGradedAlgebraCompIso (twistAlgebra A) a p).hom ≫
    (pullbackGradedAlgebraCongrIso (twistAlgebra A) ha).hom ≫
    (pullbackGradedAlgebraCompIso (twistAlgebra A) e (relativeMapHom ψ)).inv ≫
    pullbackGradedAlgebraMap e.toLRSHom.toShHom θ ≫
    (pullbackGradedAlgebraCompIso (twistAlgebra B) e ψ.relativeMapDomain.ι).hom ≫
    (pullbackGradedAlgebraCongrIso (twistAlgebra B) hb).inv ≫
    (pullbackGradedAlgebraCompIso (twistAlgebra B) b q).inv

/-- The components of `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistAlgebraHom` are the maps
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom`. -/
theorem chartTwistAlgebraHom_app (θ : SheafOfModules.GradedAlgebra.Hom
      (pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom (twistAlgebra A))
      (pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom (twistAlgebra B))) (n : ℤ) :
    (chartTwistAlgebraHom ψ a b p q e ha hb θ).app n = chartTwistHom ψ a b p q e ha hb θ n :=
  rfl

/-- **The maps `θ_n` read on a chart are multiplicative**: they preserve products of homogeneous
local sections of `a^*p^*(⨁_n 𝒪(n))`. -/
theorem chartTwistHom_map_mul (θ : SheafOfModules.GradedAlgebra.Hom
      (pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom (twistAlgebra A))
      (pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom (twistAlgebra B)))
    (i j : ℤ) (U : (TopologicalSpace.Opens C.carrier)ᵒᵖ)
    (x : ((pullbackGradedAlgebra a.toLRSHom.toShHom
      (pullbackGradedAlgebra p.toLRSHom.toShHom (twistAlgebra A))).piece i).val.obj U)
    (y : ((pullbackGradedAlgebra a.toLRSHom.toShHom
      (pullbackGradedAlgebra p.toLRSHom.toShHom (twistAlgebra A))).piece j).val.obj U) :
    ((chartTwistAlgebraHom ψ a b p q e ha hb θ).app (i + j)).val.app U
        (((pullbackGradedAlgebra a.toLRSHom.toShHom
          (pullbackGradedAlgebra p.toLRSHom.toShHom (twistAlgebra A))).mul i j).app U x y) =
      ((pullbackGradedAlgebra b.toLRSHom.toShHom
          (pullbackGradedAlgebra q.toLRSHom.toShHom (twistAlgebra B))).mul i j).app U
        (((chartTwistAlgebraHom ψ a b p q e ha hb θ).app i).val.app U x)
        (((chartTwistAlgebraHom ψ a b p q e ha hb θ).app j).val.app U y) :=
  (chartTwistAlgebraHom ψ a b p q e ha hb θ).map_mul i j U x y

end Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace AlgebraicGeometry.Space.RelativeProjHomPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ) (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.obj) (n : ℤ)
  {M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre T f)).ringCatSheaf).FullSubcategory}
  (p : (BigFppfOver.toScheme B S hS).obj (dP.fibre T f) ⟶ (relativeProj (dP.algebra T f)).scheme)
  (hp : p = (dP.fibreIso T f).hom)
  (c₁ : @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj
      (dP.fibre T f)).ringCatSheaf) _ M₁.obj
    ((Scheme.Modules.pullback p).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dP.algebra T f)).piece n)))
  {M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre T f)).ringCatSheaf).FullSubcategory}
  (q : (BigFppfOver.toScheme B S hS).obj (dQ.fibre T f) ⟶ (relativeProj (dQ.algebra T f)).scheme)
  (hq : q = (dQ.fibreIso T f).hom)
  (c₂ : @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj
      (dQ.fibre T f)).ringCatSheaf) _ M₂.obj
    ((Scheme.Modules.pullback q).obj
      ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (dQ.algebra T f)).piece n)))

/-- **The chart map `θ_n` of Stacks 085F is the degree-`n` component of a map of sheaves of graded
algebras**: on `U(ψ) ×_X T`, up to the identifications `c₁`, `c₂` of the modules with the twists,
it is the degree-`n` component of Tag 07ZG's `θ` for `ψ|_T` read on the chart, a map of sheaves of
graded algebras (`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_map_mul`). -/
theorem chartTwistMap_hom_eq_chartTwistAlgebraHom_app :
    (hψ.chartTwistMap T f n p hp c₁ q hq c₂).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))).map
          c₁.hom ≫
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistAlgebraHom (hψ.hom T f)
          ((BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f))
          ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f)) p q (hψ.chartSchemeIso T f).hom
          (hψ.toScheme_map_chartMapHom_comp_of_eq T f p hp)
          (hψ.toScheme_map_chartIncl_comp_of_eq T f q hq)
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom (hψ.hom T f))).app n ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f))).map
          c₂.inv :=
  rfl

end AlgebraicGeometry.Space.RelativeProjHomPoints

end
