module

public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison

/-!
# Base change of a morphism representable by algebraic spaces (Stacks 0302)

Let `S` be a scheme contained in a big fppf site `B`, let `X`, `Y`, `Z` be categories fibred
in groupoids over the big fppf site of `S`, let `f : X ⟶ Y` be a 1-morphism representable by
algebraic spaces and let `g : Z ⟶ Y` be any 1-morphism. Stacks 0302 says that in a 2-fibre
product square over the cospan `(g, f)` the projection to `Z` is again representable by
algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`: Stacks 0302 for an
  arbitrary 2-fibre product square of the 2-category of categories fibred in groupoids.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

/-- If `(u ≫ v ≫ 𝟙 C₀) ≫ t = 𝟙 A₀`, then `(u ≫ v) ≫ t = 𝟙 A₀`. -/
theorem cancel_inner_id {D : Type*} [Category D] {A₀ B₀ C₀ : D} (u : A₀ ⟶ B₀)
    (v : B₀ ⟶ C₀) (t : C₀ ⟶ A₀) (hyp : (u ≫ v ≫ 𝟙 C₀) ≫ t = 𝟙 A₀) : (u ≫ v) ≫ t = 𝟙 A₀ := by
  rwa [Category.comp_id] at hyp

/-- In a 2-fibre product square over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred
in groupoids over the big fppf site of `S`, the projection to `𝒵` is representable by algebraic
spaces as soon as `f` is. -/
theorem isRepresentableByAlgebraicSpaces_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    IsRepresentableByAlgebraicSpaces B S hS P.fst.hom := by
  classical
  let Q : Bicategory.TwoCommSq g f :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, w} g f
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, v, u + 1, w} g f
  let a : Bicategory.TwoCommSq.PreHom P Q := Quotient.out (hQ.from P)
  let b : Bicategory.TwoCommSq.PreHom Q P := Quotient.out (hP.from Q)
  obtain ⟨e₁, h11, -⟩ :=
    Quotient.exact (hP.hom_ext (Quotient.mk _ (a.comp b)) (𝟙 P))
  obtain ⟨e₂, h21, -⟩ :=
    Quotient.exact (hQ.hom_ext (Quotient.mk _ (b.comp a)) (𝟙 Q))
  have hcomp₁ : ∀ x, ((CatFiberedInGroupoids.underlyingIso a.isoFst).hom.app x ≫
      (CatFiberedInGroupoids.underlyingIso b.isoFst).hom.app (a.hom.hom.toFunctor.obj x)) ≫
      P.fst.hom.toFunctor.map
        ((CatFiberedInGroupoids.underlyingIso e₁).hom.app x) = 𝟙 _ := fun x =>
    cancel_inner_id _ _ _ (congrArg (fun t => t.hom.toNatTrans.app x) h11)
  have hcomp₂ : ∀ x, ((CatFiberedInGroupoids.underlyingIso b.isoFst).hom.app x ≫
      (CatFiberedInGroupoids.underlyingIso a.isoFst).hom.app (b.hom.hom.toFunctor.obj x)) ≫
      Q.fst.hom.toFunctor.map
        ((CatFiberedInGroupoids.underlyingIso e₂).hom.app x) = 𝟙 _ := fun x =>
    cancel_inner_id _ _ _ (congrArg (fun t => t.hom.toNatTrans.app x) h21)
  intro U
  dsimp only
  intro z hz
  obtain ⟨F, hF, ⟨e⟩⟩ := hf U (z ⋙ g.hom.toFunctor) (by rw [Functor.assoc, g.hom.w, hz])
  have E1 : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) P.pt.val.p 𝒵.val.p z P.fst.hom.toFunctor)
      (TwoFibreProductOver.fst (Over.map U.hom) Q.pt.val.p 𝒵.val.p z Q.fst.hom.toFunctor) :=
    TwoFibreProductOver.mapSndEquivalenceOver (Over.map U.hom) P.pt.val.p Q.pt.val.p
      𝒵.val.p z P.fst.hom.toFunctor Q.fst.hom.toFunctor a.hom.hom.toFunctor a.hom.hom.w
      (CatFiberedInGroupoids.underlyingIso a.isoFst) (fun x => a.isoFst.hom.hom.isHomLift' x)
      b.hom.hom.toFunctor b.hom.hom.w (CatFiberedInGroupoids.underlyingIso b.isoFst)
      (fun x => b.isoFst.hom.hom.isHomLift' x)
      (CatFiberedInGroupoids.underlyingIso e₁) (CatFiberedInGroupoids.underlyingIso e₂)
      (fun x => e₁.hom.hom.isHomLift' x) (fun x => e₂.hom.hom.isHomLift' x) hcomp₁ hcomp₂
  have E2 : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) Q.pt.val.p 𝒵.val.p z Q.fst.hom.toFunctor)
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p (z ⋙ g.hom.toFunctor)
        f.hom.toFunctor) :=
    TwoFibreProductOver.cancelMiddleEquivalenceOver (Over.map U.hom) 𝒳.val.p 𝒴.val.p
      𝒵.val.p z f.hom.toFunctor g.hom.toFunctor hz g.hom.w
  exact ⟨F, hF, ⟨E1.trans (E2.trans e)⟩⟩

end AlgebraicGeometry.Stack

end
