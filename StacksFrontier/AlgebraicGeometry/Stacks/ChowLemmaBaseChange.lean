module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Chow covers are stable under base change of the target

Let `f₀ : 𝒳₀ ⟶ Y₀` be a 1-morphism from an algebraic stack to an algebraic space and
`b : Y ⟶ Y₀` a morphism of algebraic spaces. If the conclusion of Chow's lemma (Stacks 0CQ8)
holds for `f₀`, it holds for the base change `𝒳 = Y ×_{Y₀} 𝒳₀ ⟶ Y`: base change the cover
`X₀ ⟶ 𝒳₀` and the compactification `X₀ ⊆ X̄₀ ⟶ Y₀` along `b`. This is the step of the proof of
Stacks 0CQ8 which passes from a Noetherian approximation `𝒳ᵢ ⟶ Yᵢ` (Stacks 0CN4) back to
`𝒳 ⟶ Y`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_isTwoFibreProduct`: the conclusion of
  Stacks 0CQ8 for `f₀` gives it for the first projection of any 2-fibre product of `(b, f₀)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_equivalence_twoFibreProduct`: the same
  for a 1-morphism `f : 𝒳 ⟶ Y` together with an equivalence of `𝒳` with a 2-fibre product of
  `(f₀, b)` carrying `f` to the second projection, which is the shape of the output of
  Stacks 0CN4.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0CN4](https://stacks.math.columbia.edu/tag/0CN4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Chow covers along a 2-isomorphism.** The conclusion of Stacks 0CQ8 for `f` gives it for any
1-morphism 2-isomorphic to `f`. -/
theorem HasChowCover.of_iso {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f f' : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} (e : f ≅ f')
    (h : HasChowCover.{u, w} B S hS hY f) : HasChowCover.{u, w} B S hS hY f' := by
  obtain ⟨X, Xbar, hX, hXbar, a, i, p, ha, has, hi, hp, ⟨ea⟩⟩ := h
  exact ⟨X, Xbar, hX, hXbar, a, i, p, ha, has, hi, hp,
    ⟨(Bicategory.whiskerLeftIso a e).symm ≪≫ ea⟩⟩

/-- **Chow covers base change along the target (the base-change step of Stacks 0CQ8).** Let
`b : Y ⟶ Y₀` be a morphism of algebraic spaces, `f₀ : 𝒳₀ ⟶ Y₀` a 1-morphism from an algebraic
stack and `P` a 2-fibre product of `(b, f₀)`. If the conclusion of Stacks 0CQ8 holds for `f₀`, it
holds for the first projection `P.pt ⟶ Y`.

With `a₀ : X₀ ⟶ 𝒳₀`, `X₀ ⊆ X̄₀ ⟶ Y₀` the given data, put `X̄ = Y ×_{Y₀} X̄₀` and
`X = X̄ ×_{X̄₀} X₀ = Y ×_{Y₀} X₀`. Then `X ⟶ X̄` is an open immersion and `X̄ ⟶ Y` is proper, as
base changes; the 1-morphism `X ⟶ P.pt` cut out of the 2-fibre product `X = Y ×_{Y₀} X₀` by the
universal property of `P` is a base change of `a₀` (Stacks 003Q), hence proper and surjective. -/
theorem HasChowCover.of_isTwoFibreProduct {Y Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY₀ : IsAlgebraicSpace B S hS Y₀) (b : Y ⟶ Y₀)
    {𝒳₀ : AlgebraicStacks.{u, w} B S hS} (f₀ : 𝒳₀ ⟶ algebraicSpaceStack.{u, w} B S hS Y₀ hY₀)
    (P : Bicategory.TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hY hY₀ b) f₀)
    (hP : Bicategory.IsTwoFibreProduct P) (h₀ : HasChowCover.{u, w} B S hS hY₀ f₀) :
    HasChowCover.{u, w} B S hS hY P.fst := by
  obtain ⟨X₀, Xb₀, hX₀, hXb₀, a₀, i₀, p₀, ha₀, has₀, hi₀, hp₀, ⟨ea⟩⟩ := h₀
  have hXb : IsAlgebraicSpace B S hS (pullback b p₀) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS b p₀ hY hXb₀ hY₀
  have hX : IsAlgebraicSpace B S hS (pullback (pullback.snd b p₀) i₀) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS _ i₀ hXb hX₀ hXb₀
  have sq₁ : IsPullback (pullback.fst b p₀) (pullback.snd b p₀) b p₀ :=
    IsPullback.of_hasPullback b p₀
  have sq₂ : IsPullback (pullback.fst (pullback.snd b p₀) i₀) (pullback.snd (pullback.snd b p₀) i₀)
      (pullback.snd b p₀) i₀ :=
    IsPullback.of_hasPullback _ _
  have sq := sq₂.paste_horiz sq₁
  let R := algebraicSpaceStackSquare.{u, w} B S hS hY hX₀ hY₀ hX sq.w
  have hR : Bicategory.IsTwoFibreProduct R :=
    isTwoFibreProduct_algebraicSpaceStackSquare.{u, w} B S hS hY hX₀ hY₀ hX sq
  let Z := R.reindexSnd ea.symm
  have hZ : Bicategory.IsTwoFibreProduct Z := Bicategory.isTwoFibreProduct_reindexSnd ea.symm hR
  have hI := isTwoFibreProduct_innerSq.{u, w} B S hS hP hZ
  have hbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    ((@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}).inverseImage
      (BigFppfOver.toScheme B S hS))
  exact ⟨pullback (pullback.snd b p₀) i₀, pullback b p₀, hX, hXb, (Bicategory.innerSq hP Z).fst,
    pullback.fst _ i₀, pullback.fst b p₀,
    isProper_baseChange B S hS a₀ P.snd _ hI ha₀,
    isSurjective_of_isTwoFibreProduct B S hS _ (Bicategory.isTwoFibreProduct_swap hI) has₀,
    hbc.of_isPullback sq₂.flip hi₀,
    Space.isProper_of_isPullback B S hS hXb hXb₀ hY hY₀ sq₁.flip hp₀,
    ⟨(Bicategory.canLower hP Z).isoFst.symm⟩⟩

/-- **Chow covers base change along the target, in the shape of Stacks 0CN4.** Let
`b : Y ⟶ Y₀` be a morphism of algebraic spaces, `f₀ : 𝒳₀ ⟶ Y₀` a 1-morphism from an algebraic
stack, `Q` a 2-fibre product of `(f₀, b)`, and `f : 𝒳 ⟶ Y` a 1-morphism with an equivalence
`e : 𝒳 ≃ Q.pt` such that `e ≫ Q.snd ≅ f`. If the conclusion of Stacks 0CQ8 holds for `f₀`, it
holds for `f`: the square on `𝒳` with legs `e ≫ Q.fst`, `e ≫ Q.snd` is again a 2-fibre product,
since `e` has a quasi-inverse, so
`AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_isTwoFibreProduct` applies to it. -/
theorem HasChowCover.of_equivalence_twoFibreProduct {Y Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY₀ : IsAlgebraicSpace B S hS Y₀) (b : Y ⟶ Y₀)
    {𝒳₀ 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f₀ : 𝒳₀ ⟶ algebraicSpaceStack.{u, w} B S hS Y₀ hY₀)
    (Q : Bicategory.TwoCommSq f₀ (algebraicSpaceStackMap.{u, w} B S hS hY hY₀ b))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (e : Bicategory.Equivalence 𝒳 Q.pt)
    (he : e.hom ≫ Q.snd ≅ f) (h₀ : HasChowCover.{u, w} B S hS hY₀ f₀) :
    HasChowCover.{u, w} B S hS hY f := by
  let T : Bicategory.TwoCommSq f₀ (algebraicSpaceStackMap.{u, w} B S hS hY hY₀ b) :=
    { pt := 𝒳
      fst := e.hom ≫ Q.fst
      snd := e.hom ≫ Q.snd
      iso := Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso e.hom Q.iso ≪≫
        (Bicategory.associator _ _ _).symm }
  let a : Bicategory.TwoCommSq.PreHom T Q :=
    { hom := e.hom
      isoFst := Iso.refl _
      isoSnd := Iso.refl _
      compat := by
        simp only [T, Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerLeftIso_hom, Iso.refl_hom,
          Bicategory.id_whiskerRight, Category.id_comp, Category.comp_id, Category.assoc,
          Iso.inv_hom_id, Bicategory.associator] }
  have hT : Bicategory.IsTwoFibreProduct T :=
    Bicategory.isTwoFibreProduct_of_section hQ (a.ofSection e.inv e.counit) e.hom e.unit.symm
  exact HasChowCover.of_iso B S hS hY he
    (HasChowCover.of_isTwoFibreProduct B S hS hY hY₀ b f₀ T.swap
      (Bicategory.isTwoFibreProduct_swap hT) h₀)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
