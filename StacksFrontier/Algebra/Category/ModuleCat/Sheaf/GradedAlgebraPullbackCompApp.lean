module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackCompEssentiallySmall

/-!
# The degreewise components of the composition comparison for graded pullbacks

`Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPullbackCompIso` compares the pullback of
sheaves of graded algebras along a morphism `h` of ringed topoi playing the role of a composite
with the iterated pullback along `g` and then `f`, by uniqueness of left adjoints, given a
comparison `τ` of the direct images of sheaves of graded algebras.  Its homogeneous components
are morphisms of sheaves of modules between pullbacks of sheaves of modules; this file proves
that **they are the comparison of left adjoints of the Stacks 03D7 adjunctions for sheaves of
modules**, as soon as `τ` is degreewise a comparison `τₘ` of the direct images of sheaves of
modules.

## Main results

* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPullbackCompIso_hom_app_app`: the
  degree-`n` component of the graded comparison at `B` is the module comparison at `B_n`.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v u₁ w

variable {X Y Z : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] [EssentiallySmall.{w} Z.C]

/-- Equal morphisms of sheaves of graded algebras have equal degree-`n` components. -/
private theorem gradedHom_app_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {A A' : SheafOfModules.GradedAlgebra.{w, w} R} {a b : A ⟶ A'}
    (h : a = b) (n : ℤ) : a.app n = b.app n :=
  congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n) h

/-- The inverse of an isomorphism of sheaves of graded algebras, in a degree where its forward
component is the forward map of a given isomorphism of sheaves of modules, is that isomorphism's
inverse. -/
public theorem gradedIso_inv_app_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {A A' : SheafOfModules.GradedAlgebra.{w, w} R} (e : A ≅ A')
    (n : ℤ) (e' : A.piece n ≅ A'.piece n) (he : e.hom.app n = e'.hom) :
    e.inv.app n = e'.inv := by
  have h1 : e.hom.app n ≫ e.inv.app n = 𝟙 _ :=
    (SheafOfModules.GradedAlgebra.categoryStruct_comp_app e.hom e.inv n).symm.trans
      (gradedHom_app_congr e.hom_inv_id n)
  rw [he] at h1
  exact (Iso.hom_comp_eq_id e').mp h1

/-- **The degreewise components of the graded composition comparison are the module
composition comparison.**  If the comparison `τ` of the direct images of sheaves of graded
algebras is, in every degree, the comparison `τₘ` of the direct images of sheaves of modules,
then the degree-`n` component of `gradedPullbackCompIso f g h τ` at `B` is the comparison of
left adjoints of the Stacks 03D7 adjunctions, read through `τₘ`, at `B_n`. -/
public theorem gradedPullbackCompIso_hom_app_app (f : AlgebraicGeometry.RingedToposHom X Y)
    (g : AlgebraicGeometry.RingedToposHom Y Z) (h : AlgebraicGeometry.RingedToposHom X Z)
    (τ : gradedPush f ⋙ gradedPush g ≅ gradedPush h)
    (τm : f.pushforwardModules ⋙ g.pushforwardModules ≅ h.pushforwardModules)
    (hτ : ∀ (A : SheafOfModules.GradedAlgebra.{w, w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ),
      (τ.hom.app A).app n = τm.hom.app (A.piece n))
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (n : ℤ) :
    ((gradedPullbackCompIso f g h τ).hom.app B).app n =
      (Adjunction.leftAdjointUniq
        (h.pullbackAdjPushforwardModulesViaComparison.ofNatIsoRight τm.symm)
        (g.pullbackAdjPushforwardModulesViaComparison.comp
          f.pullbackAdjPushforwardModulesViaComparison)).hom.app (B.piece n) := by
  apply ((h.pullbackAdjPushforwardModulesViaComparison.ofNatIsoRight τm.symm).homEquiv _
    _).injective
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (h.pullbackAdjPushforwardModulesViaComparison.ofNatIsoRight τm.symm)
    (g.pullbackAdjPushforwardModulesViaComparison.comp
      f.pullbackAdjPushforwardModulesViaComparison) (B.piece n)).symm
  have hg := gradedHom_app_congr
    (Adjunction.homEquiv_leftAdjointUniq_hom_app ((gradedAdj h).ofNatIsoRight τ.symm)
      ((gradedAdj g).comp (gradedAdj f)) B) n
  refine Eq.trans ?_ (hg.trans ?_)
  · refine (Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).trans ?_
    refine Eq.trans ?_ (gradedHom_app_congr
      (Adjunction.homEquiv_ofNatIsoRight_apply (gradedAdj h) τ.symm
        ((gradedPullbackCompIso f g h τ).hom.app B)) n).symm
    refine Eq.trans ?_ (SheafOfModules.GradedAlgebra.categoryStruct_comp_app
      (((gradedAdj h).homEquiv B ((gradedPull g ⋙ gradedPull f).obj B))
        ((gradedPullbackCompIso f g h τ).hom.app B))
      (τ.symm.hom.app ((gradedPull g ⋙ gradedPull f).obj B)) n).symm
    refine congrArg₂ (· ≫ ·) ?_ ?_
    · rw [Adjunction.homEquiv_unit]
      exact (Adjunction.homEquiv_unit _ _ _ _).trans rfl
    · exact (gradedIso_inv_app_eq (τ.app ((gradedPull g ⋙ gradedPull f).obj B)) n
        (τm.app (((gradedPull g ⋙ gradedPull f).obj B).piece n)) (hτ _ n)).symm
  · simp only [Adjunction.comp_unit_app]
    rfl

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
