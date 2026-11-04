module

public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Basic

/-!
# The chart comparison of two twist data, as an endomorphism of the absolute twists

Tag 01NR's second uniqueness assertion says that an isomorphism of the glued graded algebras
commuting with the homogeneous-section maps already determines every chart identification. Read
on one affine chart, that assertion is a statement about the single endomorphism
`chartEndo`: the chart identification of the first twist datum, followed by the given
isomorphism, followed back along the chart identification of the second. This file builds that
endomorphism and transports the chart data across it on sections.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistRigidity.chartEndo`: the endomorphism of
  `twistingSheaf (A.grading U) n` built from two twist data and an isomorphism between their
  algebras.

## Main results

* `Stacks.AlgebraicGeometry.TwistRigidity.mapSection_chartEndo`: **the bridge.** The section
  comparison of the second twist datum applied to `chartEndo` is the given isomorphism applied
  to the section comparison of the first.
* `Stacks.AlgebraicGeometry.TwistRigidity.mapSection_injective`: the section comparison of a
  chart datum is injective, being a composite of two isomorphisms on sections.
* `Stacks.AlgebraicGeometry.TwistRigidity.iso_inv_app_hom_app` and `iso_hom_app_inv_app`: an
  isomorphism of sheaves of modules cancels on sections, in both orders.
* `Stacks.AlgebraicGeometry.TwistRigidity.app_congr` and `mul_app_congr`: congruence in the
  argument of a morphism of sheaves of modules, and in both arguments of the product of a sheaf
  of graded algebras.
* `Stacks.AlgebraicGeometry.TwistRigidity.app_eq_rec`: a morphism of sheaves of modules commutes
  with transport of a section along an equality of objects of the site.

## Implementation notes

Everything here is definitional. `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is
`Iso.refl`, so the sections of a restriction over an open *are* the sections over the image
open, and `(restrictFunctor f).map φ` acts on sections over `V` as `φ` acts on sections over
`f ''ᵁ V` — both by `rfl`. The only non-`rfl` steps are the two cancellations of an
isomorphism, which come from `Iso.hom_inv_id` and `Iso.inv_hom_id` read on sections.

The five general facts are stated over an arbitrary sheaf of rings on an arbitrary site rather
than at the scheme spelling. That is forced: the homogeneous pieces of a twist datum's algebra
live over the ring sheaf of the ringed site of the relative Proj, while
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is stated over a scheme's `ringCatSheaf`. The
two are the same object, but a rewrite whose statement is pinned at one spelling does not fire
at the other, and the error reports the target as not type-correct at the `implicit`
transparency level rather than as a failed match.

The open immersion instance is a `Prop`-valued class, so the witnesses carried by the two twist
data are interchangeable and the `letI` that brings one into scope can serve the other. That is
why only the first twist datum's witness appears.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistRigidity

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Three general facts -/

section General

universe v t uc vc

variable {C : Type uc} [Category.{vc} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- An isomorphism of sheaves of modules cancels on sections. Stated over an arbitrary sheaf of
rings on an arbitrary site, because the chart identifications of a twist datum live over the
ringed site of the relative Proj while the twists live over the composite of a scheme's
structure sheaf with the forgetful functor; the two are the same object, but a rewrite stated at
one of the spellings does not fire at the other. -/
public theorem iso_inv_app_hom_app {M N : SheafOfModules.{v} R} (ε : M ≅ N) (V : Cᵒᵖ)
    (w : (M.val.obj V : Type v)) : ε.inv.val.app V (ε.hom.val.app V w) = w :=
  calc ε.inv.val.app V (ε.hom.val.app V w) = (ε.hom ≫ ε.inv).val.app V w := rfl
    _ = (𝟙 M : M ⟶ M).val.app V w := by rw [ε.hom_inv_id]
    _ = w := rfl

/-- The other cancellation of an isomorphism on sections. -/
public theorem iso_hom_app_inv_app {M N : SheafOfModules.{v} R} (ε : M ≅ N) (V : Cᵒᵖ)
    (w : (N.val.obj V : Type v)) : ε.hom.val.app V (ε.inv.val.app V w) = w :=
  iso_inv_app_hom_app ε.symm V w

/-- Congruence in the argument of a morphism of sheaves of modules on sections. -/
public theorem app_congr {M N : SheafOfModules.{v} R} (φ : M ⟶ N) (V : Cᵒᵖ)
    {z z' : (M.val.obj V : Type v)} (h : z = z') : φ.val.app V z = φ.val.app V z' := by
  rw [h]

/-- Congruence in both arguments of the product of a sheaf of graded algebras. -/
public theorem mul_app_congr (B : SheafOfModules.GradedAlgebra.{t, v} R) (i j : ℤ) (W : Cᵒᵖ)
    {x x' : (B.piece i).val.obj W} {y y' : (B.piece j).val.obj W} (hx : x = x')
    (hy : y = y') : (B.mul i j).app W x y = (B.mul i j).app W x' y' := by
  rw [hx, hy]

/-- A morphism of sheaves of modules commutes with transport of a section along an equality of
objects of the site. -/
public theorem app_eq_rec {M N : SheafOfModules.{v} R} (φ : M ⟶ N) {W W' : C} (h : W = W')
    (z : (M.val.obj (op W) : Type v)) :
    φ.val.app (op W') (h ▸ z) = h ▸ (φ.val.app (op W) z) := by
  subst h
  rfl

end General

/-! ### The chart comparison -/

section Relative

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}
  {algebra : SchemeGradedAlgebra (relativeProj A).scheme}

/-- The endomorphism of the `n`-th absolute twist on an affine chart cut out by two twist data
and an isomorphism of their glued algebras: undo the first datum's chart identification, apply
the isomorphism, then redo the second datum's. Tag 01NR's second uniqueness assertion is
exactly that this is the identity. -/
public def chartEndo (D E : TwistData A) (e : D.algebra ≅ E.algebra) (U : S.Opens)
    (hU : IsAffineOpen U) (n : ℤ) :
    twistingSheaf (A.grading U) n ⟶ twistingSheaf (A.grading U) n :=
  letI := D.chartData.chart_isOpenImmersion U hU
  (D.chartData.chartIso U hU n).inv ≫
    (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map (e.hom.app n) ≫
      (E.chartData.chartIso U hU n).hom

/-- The section comparison of a chart datum is injective: it is the inverse chart identification
on sections followed by the identity isomorphism `restrictAppIso`. -/
public theorem mapSection_injective (D : ChartData A algebra) (U : S.Opens)
    (hU : IsAffineOpen U) (n : ℤ) (V : (AlgebraicGeometry.Proj (A.grading U)).Opens) :
    Function.Injective (D.mapSection U hU n V) := by
  let := D.chart_isOpenImmersion U hU
  have key : ∀ a, (D.chartIso U hU n).hom.val.app (op V)
      ((Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU)
        (algebra.piece n) V).inv (D.mapSection U hU n V a)) = a :=
    fun a => iso_hom_app_inv_app (D.chartIso U hU n) (op V) a
  intro a b hab
  refine (key a).symm.trans (Eq.trans ?_ (key b))
  exact congrArg (fun z => (D.chartIso U hU n).hom.val.app (op V)
    ((Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU)
      (algebra.piece n) V).inv z)) hab

/-- **The bridge.** Under the section comparisons of the two twist data, `chartEndo` becomes the
given isomorphism of glued algebras. -/
public theorem mapSection_chartEndo (D E : TwistData A) (e : D.algebra ≅ E.algebra)
    (U : S.Opens) (hU : IsAffineOpen U)
    [IsOpenImmersion ((relativeProj A).chart U hU)] (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (a : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    E.chartData.mapSection U hU n V ((chartEndo D E e U hU n).val.app (op V) a) =
      (e.hom.app n).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
        (D.chartData.mapSection U hU n V a) := by
  show (E.chartData.chartIso U hU n).inv.val.app (op V)
      ((E.chartData.chartIso U hU n).hom.val.app (op V)
        (((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
            (e.hom.app n)).val.app (op V)
          ((D.chartData.chartIso U hU n).inv.val.app (op V) a))) =
    ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
        (e.hom.app n)).val.app (op V)
      ((D.chartData.chartIso U hU n).inv.val.app (op V) a)
  exact iso_inv_app_hom_app (E.chartData.chartIso U hU n) (op V) _

end Relative

end Stacks.AlgebraicGeometry.TwistRigidity

end
