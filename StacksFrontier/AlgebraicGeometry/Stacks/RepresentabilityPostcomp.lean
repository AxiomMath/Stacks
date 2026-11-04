module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Slice
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverMiddleFactor

/-!
# Representability by algebraic spaces is cancelled by a representable postcomposition

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳`, `𝒴`, `𝒵` be categories fibred
in groupoids over the big fppf site of `S`. Let `a : 𝒳 ⟶ 𝒵` and `b : 𝒴 ⟶ 𝒵` be 1-morphisms
representable by algebraic spaces and let `c : 𝒴 ⟶ 𝒳` be a 1-morphism with `c ≫ a ≅ b`, i.e. a
1-morphism from `b` to `a` in the categories over `𝒵`. Then `c` is representable by algebraic
spaces.

This is not a tag of the Stacks project, and it is not an instance of the base-change statement
Stacks 0302: a 1-morphism over `𝒵` is not a base change of anything. It is the formal
consequence of Stacks 02X2 — the fibre product of two algebraic spaces over an algebraic space
is an algebraic space — obtained from the identity

```text
U ×_{x, 𝒳, c} 𝒴  ≃  (U ×_{z, 𝒵, b} 𝒴) ×_{U ×_{z, 𝒵, a} 𝒳} U,       z = x ≫ a,
```

the right-hand side being a 2-fibre product in the categories over the big fppf site of `U`,
with `U ⟶ U ×_𝒵 𝒳` the canonical section attached to the point `x` and
`U ×_𝒵 𝒴 ⟶ U ×_𝒵 𝒳` the 1-morphism induced by `c`. The identity itself is
`CategoryTheory.TwoFibreProductOver.isEquivalence_middleComparison`; the two factors of the
right-hand side are algebraic spaces over `U` by the hypotheses, the base is one too, and the
2-fibre product of their categories of elements is the category of elements of the presheaf
fibre product (`CategoryTheory.PresheafOfCategories.isEquivalence_toTwoFibreProduct`), which is
an algebraic space by Stacks 02X2 in the form
`AlgebraicGeometry.isAlgebraicSpace_of_isPullback_isTerminal`.

The intended use is the representability of the relative diagonal and of the inertia
projection of Stacks 050Q: the relative diagonal `𝒳 ⟶ 𝒳 ×_𝒴 𝒳` lies over `𝒳 × 𝒳`, where the
absolute diagonal of `𝒳` and the projection `𝒳 ×_𝒴 𝒳 ⟶ 𝒳 × 𝒳` are both representable, so this
statement makes it representable without any of the equivalences of Stacks 045G.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_postcomp`: the statement above.

## Implementation notes

The three categories fibred in groupoids have independent object and morphism universes. They
need not be objects of one 2-category, because the three 1-morphisms are `BasedFunctor`s and
nothing in the proof forms a 2-fibre product of the three: the 2-fibre products it does form all
live over the big fppf site of the test scheme `U` and are built from the underlying functors.
The statement therefore applies to the factorization `Δ_𝒴 = Δ_{𝒴/𝒱} ≫ ι` of the diagonal of a
2-fibre product (Stacks 07WG), where the self-product `𝒴 ×_𝒱 𝒴` has a *larger* object universe
than `𝒴` and `𝒴 × 𝒴` because its objects carry a morphism of `𝒱`. It also specialises to the
saturated universes `CategoryTheory.CatFiberedInGroupoids.{u, max u v, u + 1,
max (max (u + 1) w) v}` that `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`
(Stacks 0302) is stated at. The 2-isomorphism is given as a `CategoryTheory.BasedNatIso` of
`BasedFunctor`s rather than as a 2-cell of the 2-category, which is the shape
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences` (Stacks 0457)
also uses.

`AlgebraicGeometry.Stack.fst_isFiberedInGroupoids_overMap` is a public form of a lemma that
`StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance` carries privately; that file
should be refactored onto it.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PresheafOfCategories Opposite

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂ v₃ w₃ uC vC

section Fibred

variable {𝒞 : Type uC} [Category.{vC} 𝒞]

/-- The slice `𝒞/U ⟶ 𝒞/S` along `U ⟶ S` is fibred in groupoids. -/
theorem overMap_isFiberedInGroupoids {U S : 𝒞} (f : U ⟶ S) :
    (Over.map f).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.of_comp_over S (Over.forget U) (Over.map f)
    (Over.mapForget_eq f) (Functor.IsFiberedInGroupoids.over_forget U)

/-- The first projection of a 2-fibre product over `𝒞/S` whose first factor is the slice
`𝒞/U` along a morphism `U ⟶ S` is fibred in groupoids over `𝒞/U`. -/
theorem fst_isFiberedInGroupoids_overMap {S U : 𝒞} (f : U ⟶ S)
    {𝒜 : Type*} {𝒟 : Type*} [Category 𝒜] [Category 𝒟]
    (p𝒜 : 𝒜 ⥤ Over S) (p𝒟 : 𝒟 ⥤ Over S) (G : Over U ⥤ 𝒟) (F : 𝒜 ⥤ 𝒟)
    (h𝒜 : p𝒜.IsFiberedInGroupoids) (h𝒟 : p𝒟.IsFiberedInGroupoids)
    (hG : G ⋙ p𝒟 = Over.map f) (hF : F ⋙ p𝒟 = p𝒜) :
    (TwoFibreProductOver.fst (Over.map f) p𝒜 p𝒟 G F).IsFiberedInGroupoids := by
  have hs : (TwoFibreProductOver.structureFunctor (Over.map f) p𝒜 p𝒟 G F).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids (Over.map f) p𝒜 p𝒟 G F
      (overMap_isFiberedInGroupoids f) h𝒜 h𝒟 hG hF
  have hcomp : TwoFibreProductOver.fst (Over.map f) p𝒜 p𝒟 G F ⋙ Over.forget U =
      TwoFibreProductOver.structureFunctor (Over.map f) p𝒜 p𝒟 G F ⋙ Over.forget S := by
    rw [← TwoFibreProductOver.fst_comp_eq, Functor.assoc, Over.mapForget_eq f]
  exact Functor.IsFiberedInGroupoids.of_comp_over U _ _ hcomp
    (Functor.IsFiberedInGroupoids.comp _ _ hs (Functor.IsFiberedInGroupoids.over_forget S))

/-- The first projection of a 2-fibre product over `𝒯` whose first factor is `𝒯` itself, with
the identity as structure functor, is fibred in groupoids over `𝒯`: it is the structure functor
of the 2-fibre product. -/
theorem fst_isFiberedInGroupoids_id {𝒯 : Type*} [Category 𝒯] {𝒜 : Type*} [Category 𝒜]
    {ℬ : Type*} [Category ℬ] (p𝒜 : 𝒜 ⥤ 𝒯) (pℬ : ℬ ⥤ 𝒯) (G : 𝒯 ⥤ ℬ) (F : 𝒜 ⥤ ℬ)
    (h𝒜 : p𝒜.IsFiberedInGroupoids) (hℬ : pℬ.IsFiberedInGroupoids)
    (hG : G ⋙ pℬ = 𝟭 𝒯) (hF : F ⋙ pℬ = p𝒜) :
    (TwoFibreProductOver.fst (𝟭 𝒯) p𝒜 pℬ G F).IsFiberedInGroupoids := by
  have h := TwoFibreProductOver.isFiberedInGroupoids (𝟭 𝒯) p𝒜 pℬ G F
    Functor.isFiberedInGroupoids_id h𝒜 hℬ hG hF
  rwa [← TwoFibreProductOver.fst_comp_eq, Functor.comp_id] at h

end Fibred

/-- **Cancellation of a representable postcomposition.** Let `a : 𝒳 ⟶ 𝒵` and `b : 𝒴 ⟶ 𝒵` be
1-morphisms of categories fibred in groupoids over the big fppf site of `S`, both representable
by algebraic spaces, and let `c : 𝒴 ⟶ 𝒳` be a 1-morphism with a vertical 2-isomorphism
`c ≫ a ≅ b`. Then `c` is representable by algebraic spaces.

For a scheme-valued point `x` of `𝒳` over a scheme `U` over `S`, write `z = x ≫ a` for the
induced point of `𝒵`. The 2-fibre product `U ×_{x, 𝒳, c} 𝒴` is the 2-fibre product, over the
big fppf site of `U`, of `U ×_{z, 𝒵, b} 𝒴` with the canonical section `U ⟶ U ×_{z, 𝒵, a} 𝒳`;
both factors and the base are equivalent over that site to algebraic spaces by the two
hypotheses, so the 2-fibre product is equivalent to the category of elements of the presheaf
fibre product, which is an algebraic space by Stacks 02X2. -/
theorem isRepresentableByAlgebraicSpaces_of_postcomp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    {𝒵 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}
    (a : 𝒳.val ⥤ᵇ 𝒵.val) (b : 𝒴.val ⥤ᵇ 𝒵.val) (c : 𝒴.val ⥤ᵇ 𝒳.val)
    (α : BasedFunctor.comp c a ≅ b)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hb : IsRepresentableByAlgebraicSpaces B S hS b) :
    IsRepresentableByAlgebraicSpaces B S hS c := by
  classical
  intro U
  dsimp only
  intro x hx
  set 𝒰 := BigFppfOver B U.left.1 U.left.2 with h𝒰
  set p𝒰 : 𝒰 ⥤ BigFppfOver B S hS := Over.map U.hom with hp𝒰
  set A₀ := a.toFunctor with hA₀
  set B₀ := b.toFunctor with hB₀
  set C₀ := c.toFunctor with hC₀
  -- the 2-isomorphism, read on the underlying functors
  set α₀ : C₀ ⋙ A₀ ≅ B₀ := (BasedNatTrans.forgetful 𝒴.val 𝒵.val).mapIso α with hα₀
  have hα : ∀ y : 𝒴.val.obj, 𝒵.val.p.IsHomLift (𝟙 (𝒴.val.p.obj y)) (α₀.hom.app y) :=
    fun y => α.hom.isHomLift' y
  have hz : (x ⋙ A₀) ⋙ 𝒵.val.p = p𝒰 := by rw [Functor.assoc, a.w, hx]
  obtain ⟨Fa, hFa, ⟨eA⟩⟩ := ha U (x ⋙ A₀) hz
  obtain ⟨Fb, hFb, ⟨eB⟩⟩ := hb U (x ⋙ A₀) hz
  -- the fibredness facts the comparisons need
  have hp𝒰fib : p𝒰.IsFiberedInGroupoids := overMap_isFiberedInGroupoids U.hom
  have hπA : (TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒵.val.p (x ⋙ A₀) A₀).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_overMap U.hom 𝒳.val.p 𝒵.val.p (x ⋙ A₀) A₀
      𝒳.isFiberedInGroupoids 𝒵.isFiberedInGroupoids hz a.w
  have hπB : (TwoFibreProductOver.fst p𝒰 𝒴.val.p 𝒵.val.p (x ⋙ A₀) B₀).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_overMap U.hom 𝒴.val.p 𝒵.val.p (x ⋙ A₀) B₀
      𝒴.isFiberedInGroupoids 𝒵.isFiberedInGroupoids hz b.w
  have hπD : (TwoFibreProductOver.fst p𝒰 𝒴.val.p 𝒳.val.p x C₀).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_overMap U.hom 𝒴.val.p 𝒳.val.p x C₀
      𝒴.isFiberedInGroupoids 𝒳.isFiberedInGroupoids hx c.w
  have hdpA : (discreteProjection Fa).IsFiberedInGroupoids :=
    (isFiberedInSetoids_discreteProjection Fa).isFiberedInGroupoids
  have hdpB : (discreteProjection Fb).IsFiberedInGroupoids :=
    (isFiberedInSetoids_discreteProjection Fb).isFiberedInGroupoids
  -- the section and the 1-morphism of the decomposition
  set Sec := TwoFibreProductOver.baseChangeSection (pT := p𝒰) (pZ := 𝒵.val.p) x A₀ hx a.w
    with hSec
  set Mid := TwoFibreProductOver.middleMap (pT := p𝒰) x C₀ A₀ c.w α₀ hα with hMid
  have hSecw : Sec ⋙ TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒵.val.p (x ⋙ A₀) A₀ = 𝟭 𝒰 :=
    TwoFibreProductOver.baseChangeSection_comp_fst x A₀ hx a.w
  have hMidw : Mid ⋙ TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒵.val.p (x ⋙ A₀) A₀ =
      TwoFibreProductOver.fst p𝒰 𝒴.val.p 𝒵.val.p (x ⋙ A₀) B₀ := rfl
  have hP₀ : (TwoFibreProductOver.fst (𝟭 𝒰)
      (TwoFibreProductOver.fst p𝒰 𝒴.val.p 𝒵.val.p (x ⋙ A₀) B₀)
      (TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒵.val.p (x ⋙ A₀) A₀) Sec Mid).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_id _ _ _ _ hπB hπA hSecw hMidw
  -- step 1: the decomposition
  have E1 := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hπD hP₀ _
    (TwoFibreProductOver.middleComparison_comp_fst (pT := p𝒰) x C₀ A₀ hx c.w a.w α₀ hα)
    (TwoFibreProductOver.isEquivalence_middleComparison (pT := p𝒰) x C₀ A₀ hx c.w a.w α₀ hα)
  -- step 2: replace the base by the algebraic space representing it
  have heA : Functor.IsEquivalence eA.hom.functor := eA.isEquivalence_hom_functor
  have hσ : (Sec ⋙ eA.hom.functor) ⋙ discreteProjection Fa = 𝟭 𝒰 := by
    rw [Functor.assoc, eA.hom.w, hSecw]
  have hμ : (Mid ⋙ eA.hom.functor) ⋙ discreteProjection Fa =
      TwoFibreProductOver.fst p𝒰 𝒴.val.p 𝒵.val.p (x ⋙ A₀) B₀ := by
    rw [Functor.assoc, eA.hom.w, hMidw]
  have hP₁ : (TwoFibreProductOver.fst (𝟭 𝒰)
      (TwoFibreProductOver.fst p𝒰 𝒴.val.p 𝒵.val.p (x ⋙ A₀) B₀) (discreteProjection Fa)
      (Sec ⋙ eA.hom.functor) (Mid ⋙ eA.hom.functor)).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_id _ _ _ _ hπB hdpA hσ hμ
  have E2 := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hP₀ hP₁ _
    (TwoFibreProductOver.mapBase_comp_fst (pT := 𝟭 𝒰) Sec Mid eA.hom.functor eA.hom.w)
    (TwoFibreProductOver.isEquivalence_mapBase (pT := 𝟭 𝒰) (G := Sec) (F := Mid) eA.hom.w)
  -- step 3: replace the second factor by the algebraic space representing it
  have heB : Functor.IsEquivalence eB.inv.functor := eB.isEquivalence_inv_functor
  have hθ : (eB.inv.functor ⋙ Mid ⋙ eA.hom.functor) ⋙ discreteProjection Fa =
      discreteProjection Fb := by
    rw [Functor.assoc, hμ, eB.inv.w]
  have hP₂ : (TwoFibreProductOver.fst (𝟭 𝒰) (discreteProjection Fb) (discreteProjection Fa)
      (Sec ⋙ eA.hom.functor) (eB.inv.functor ⋙ Mid ⋙ eA.hom.functor)).IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_id _ _ _ _ hdpB hdpA hσ hθ
  have E3 := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hP₂ hP₁ _
    (TwoFibreProductOver.precomposeSnd_comp_fst (pT := 𝟭 𝒰) (pℬ := discreteProjection Fa)
      (Sec ⋙ eA.hom.functor) (Mid ⋙ eA.hom.functor) eB.inv.functor eB.inv.w)
    (TwoFibreProductOver.isEquivalence_precomposeSnd (pT := 𝟭 𝒰)
      (pℬ := discreteProjection Fa) (G := Sec ⋙ eA.hom.functor) (F := Mid ⋙ eA.hom.functor)
      Functor.isFiberedInGroupoids_id hdpB hπB eB.inv.w hμ)
  -- step 4: the 2-fibre product of categories of elements
  set H := twoFibreProductPresheaf (Sec ⋙ eA.hom.functor) hσ
    (eB.inv.functor ⋙ Mid ⋙ eA.hom.functor) hθ with hH
  have hdpH : (discreteProjection H).IsFiberedInGroupoids :=
    (isFiberedInSetoids_discreteProjection H).isFiberedInGroupoids
  have E4 := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hdpH hP₂ _
    (toTwoFibreProduct_comp_fst (Sec ⋙ eA.hom.functor) hσ
      (eB.inv.functor ⋙ Mid ⋙ eA.hom.functor) hθ)
    (isEquivalence_toTwoFibreProduct (Sec ⋙ eA.hom.functor) hσ
      (eB.inv.functor ⋙ Mid ⋙ eA.hom.functor) hθ)
  -- step 5: the presheaf is an algebraic space, by Stacks 02X2
  refine ⟨H, ?_, ?_⟩
  · exact isAlgebraicSpace_of_isPullback_isTerminal hFb hFa Over.mkIdTerminal
      (isPullback_fibrePresheaf (natTransOfBasedFunctor (eB.inv.functor ⋙ Mid ⋙ eA.hom.functor)
        hθ) (sectionOfBasedFunctor (Sec ⋙ eA.hom.functor) hσ) _ Over.mkIdTerminal)
  · obtain ⟨e1⟩ := E1
    obtain ⟨e2⟩ := E2
    obtain ⟨e3⟩ := E3
    obtain ⟨e4⟩ := E4
    exact ⟨e1.trans (e2.trans (e3.symm.trans e4.symm))⟩

end AlgebraicGeometry.Stack

end
