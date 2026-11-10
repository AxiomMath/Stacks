module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequencePresheaf

/-!
# A section of the presheaf coproduct of the skyscrapers is its family of components

The coproduct of the underlying presheaves of the skyscrapers `(i_x)_* 𝐙` has, over an étale
`X`-scheme, the finitely supported families of sections of the summands among its sections: the
family is assembled by `DirectSum.toAddMonoid` of the summand inclusions. This file shows that
assembly is injective, so that a family with vanishing assembled section vanishes.

## Main definitions

* `Stacks.EtaleCohomology.closedPointSkyscraperProj`: the projection of the coproduct of the
  underlying presheaves of the skyscrapers onto the summand at a closed point.

## Main results

* `Stacks.EtaleCohomology.toAddMonoid_sigmaι_eq_zero`: **a finitely supported family of sections
  of the skyscrapers whose assembled section of the presheaf coproduct is zero is zero.**

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper_obj

attribute [local instance] Classical.decEq

variable (X : Scheme.{u})

/-- **The projection of the coproduct of the underlying presheaves of the skyscrapers onto the
summand at a closed point.** It is the morphism out of the coproduct given by the identity at that
point and zero elsewhere. -/
def closedPointSkyscraperProj (x : closedPoints X) :
    (∐ fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj) ⟶
      (closedPointSkyscraper.{u, v} X x).obj :=
  Sigma.desc fun y ↦ if h : y = x then
    eqToHom (congrArg (fun z : closedPoints X ↦ (closedPointSkyscraper.{u, v} X z).obj) h) else 0

/-- The inclusion of the summand at `y` followed by the projection onto the summand at `x` is
`eqToHom` when `y = x` and zero otherwise. -/
theorem ι_comp_closedPointSkyscraperProj (x y : closedPoints X) :
    Sigma.ι (fun z : closedPoints X ↦ (closedPointSkyscraper.{u, v} X z).obj) y ≫
        closedPointSkyscraperProj.{u, v} X x =
      if h : y = x then
        eqToHom (congrArg (fun z : closedPoints X =>
          (closedPointSkyscraper.{u, v} X z).obj) h) else 0 :=
  Sigma.ι_comp_desc _ y

/-- **A finitely supported family of sections of the skyscrapers whose assembled section of the
coproduct of the underlying presheaves vanishes is zero.** -/
theorem toAddMonoid_sigmaι_eq_zero (U : X.Etaleᵒᵖ)
    (D : DirectSum ↥(closedPoints X)
      fun y : closedPoints X => ((closedPointSkyscraper.{u, v} X y).obj.obj U : Type _))
    (hD : DirectSum.toAddMonoid (fun y : closedPoints X =>
      ((Sigma.ι (fun z : closedPoints X ↦ (closedPointSkyscraper.{u, v} X z).obj) y).app
        U).hom) D = 0) : D = 0 := by
  refine DFinsupp.ext fun x ↦ ?_
  have hproj : ∀ (y : closedPoints X)
      (b : ((closedPointSkyscraper.{u, v} X y).obj.obj U : Type _)),
      ((closedPointSkyscraperProj.{u, v} X x).app U)
          (((Sigma.ι (fun z : closedPoints X ↦
            (closedPointSkyscraper.{u, v} X z).obj) y).app U) b) =
        DFinsupp.evalAddMonoidHom (β := fun z : closedPoints X ↦
          ((closedPointSkyscraper.{u, v} X z).obj.obj U : Type _)) x
          (DirectSum.of (fun z : closedPoints X ↦
            ((closedPointSkyscraper.{u, v} X z).obj.obj U : Type _)) y b) := by
    intro y b
    refine (ConcreteCategory.congr_hom
      (congr_app (ι_comp_closedPointSkyscraperProj.{u, v} X x y) U) b).trans ?_
    by_cases hy : y = x
    · subst hy
      refine Eq.trans ?_ (DirectSum.of_eq_same (β := fun z : closedPoints X ↦
        ((closedPointSkyscraper.{u, v} X z).obj.obj U : Type _)) y b).symm
      simp
    · simp only [dite_eq_right hy]
      exact (DirectSum.of_eq_of_ne (β := fun z : closedPoints X ↦
        ((closedPointSkyscraper.{u, v} X z).obj.obj U : Type _)) y x b (Ne.symm hy)).symm
  have hcomp : ((closedPointSkyscraperProj.{u, v} X x).app U).hom.comp
      (DirectSum.toAddMonoid fun y : closedPoints X ↦
        ((Sigma.ι (fun z : closedPoints X ↦ (closedPointSkyscraper.{u, v} X z).obj) y).app
          U).hom) =
      DFinsupp.evalAddMonoidHom (β := fun z : closedPoints X ↦
        ((closedPointSkyscraper.{u, v} X z).obj.obj U : Type _)) x :=
    DirectSum.addHom_ext fun y b ↦
      (congrArg (fun c : ((∐ fun z : closedPoints X ↦
          (closedPointSkyscraper.{u, v} X z).obj).obj U : Type _) ↦
        ((closedPointSkyscraperProj.{u, v} X x).app U) c)
        (DirectSum.toAddMonoid_of (fun y' : closedPoints X ↦
          ((Sigma.ι (fun z : closedPoints X ↦
            (closedPointSkyscraper.{u, v} X z).obj) y').app U).hom) y b)).trans (hproj y b)
  have hval := DFunLike.congr_fun hcomp D
  rw [AddMonoidHom.comp_apply, hD, map_zero] at hval
  exact hval.symm.trans (DFinsupp.zero_apply (β := fun z : closedPoints X ↦
    ((closedPointSkyscraper.{u, v} X z).obj.obj U : Type _)) x).symm

end Stacks.EtaleCohomology

end
