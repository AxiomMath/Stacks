module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothStrongLift
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleAmbient
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSchemeStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Comparing two smooth lifts along a thickening of algebraic stacks (Stacks 0CJW)

Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over `S` and consider a 2-commutative
diagram
```
W'' ←-i''-- W --i--→ W'
 |x''       |x       |x'
 ↓          ↓        ↓
 𝒳'  ←-ι--  𝒳  --ι-→ 𝒳'
```
with both squares 2-fibre products, `W`, `W'`, `W''` algebraic spaces and the vertical
1-morphisms smooth. Stacks 0CJW asserts that, étale locally on `W'`, the ambient space `W'` maps
étale to `W''` compatibly with everything in sight: there are an étale covering
`{f'_k : W'_k ⟶ W'}`, étale morphisms `f''_k : W'_k ⟶ W''` and 2-morphisms
`γ_k : x'' ∘ f''_k ⟶ x' ∘ f'_k` such that `(f'_k)⁻¹(W) = (f''_k)⁻¹(W)`, the two restrictions to
it agree, and `γ_k` restricted to it is the filler of the given diagram over `W`.

## Main results

* `AlgebraicGeometry.Stack.exists_isEtaleCovering_ambientComparison`: **Stacks 0CJW**.
* `AlgebraicGeometry.Stack.exists_isEtaleCovering_ambientComparison_of_lifting`: the whole of the
  source's argument, from any proof of its last step, Stacks 0CHJ, given as the hypothesis `hlift`
  in exactly the form in which
  `AlgebraicGeometry.Space.exists_isEtaleCovering_lift_of_isSmooth_of_isThickeningHom` states it.
* `AlgebraicGeometry.Stack.isThickeningHom_of_isTwoFibreProduct`,
  `AlgebraicGeometry.Stack.isSmooth_fst_of_isTwoFibreProduct`,
  `AlgebraicGeometry.Stack.exists_comp_eq_of_isTwoFibreProduct`: the three facts about the two
  cartesian squares the argument uses.
* `CategoryTheory.Bicategory.whiskerLeft_comparison_eq`: the 2-cell computation behind clause (c).

## Implementation notes

**The proof is the source's.** `I' = W' ×_{𝒳'} W''` is an algebraic space with projections
`p' : I' ⟶ W'`, `q' : I' ⟶ W''` and universal filler `γ`
(`AlgebraicGeometry.Stack.exists_isTwoFibreProduct_algebraicSpaceStackFunctor`); `p'` is smooth as
a base change of `x''` (**Stacks 075W**). The filler `α'⁻¹ ≫ α''` of the given diagram over `W`
defines a section `δ : W ⟶ I'` of `p'` over `i` with `q' ∘ δ = i''` and `δ^*γ = α'⁻¹ ≫ α''`.
`i : W ⟶ W'` is a thickening of algebraic spaces (**Stacks 0BPR**), so Stacks 0CHJ extends `δ`
over the members `W'_k` of an étale covering of `W'`, by `δ_k : W'_k ⟶ I'`. Then
`f'_k = p' ∘ δ_k`, `f''_k = q' ∘ δ_k` and `γ_k = δ_k^*γ⁻¹`.

* Clause (c) is a 2-cell computation: the restriction of `δ_k` to `W_k = W ×_{W'} W'_k` is
  `δ ∘ (W_k ⟶ W)`, and `δ^*γ` is the filler over `W`.
* Clauses (a) and (b): the square `W_k = W ×_{W''} W'_k` along `f''_k` commutes because `δ_k`
  restricts to `δ`; it is cartesian because a morphism `T ⟶ W'_k` of algebraic spaces whose
  composite with `f''_k` lands in `W` has, through `γ_k` and `α''`, composite with `f'_k ≫ x'`
  factoring through `ι`, hence composite with `f'_k` landing in `W = 𝒳 ×_{𝒳'} W'`; and `i''` is
  a monomorphism.
* `f''_k` is étale by the étale clause of **Stacks 0CJC**
  (`AlgebraicGeometry.Stack.isEtale_of_isTwoFibreProduct_of_isThickening`), applied to the
  morphism of thickenings `(W_k ⊂ W'_k) ⟶ (W ⊂ W'')` over `(𝒳 ⊂ 𝒳')`: `W'_k ⟶ 𝒳'` is smooth
  as `x' ∘ f'_k`, `W_k ⟶ W` is étale as a base change of `f'_k`, `W_k = 𝒳 ×_{𝒳'} W'_k` by
  pasting `W = 𝒳 ×_{𝒳'} W'` with `W_k = W ×_{W'} W'_k`, and the compatibility of the cube is
  clause (c).

**The last step, Stacks 0CHJ.** The argument is written once, in
`exists_isEtaleCovering_ambientComparison_of_lifting`, against the statement of Stacks 0CHJ
(More on Morphisms of Spaces, Lemma 76.19.7) taken as the hypothesis `hlift`. That statement is
proved unconditionally as
`AlgebraicGeometry.Space.exists_isEtaleCovering_lift_of_isSmooth_of_isThickeningHom`, and the
registered `exists_isEtaleCovering_ambientComparison` is the instantiation at it, with no
hypothesis beyond the source's.

**Clauses (a) and (b) as one cartesian square.** "`(f'_k)⁻¹(W) = (f''_k)⁻¹(W)` and the two
restrictions agree" is stated as: one algebraic space `U` with `e : U ⟶ W'_k` and `g : U ⟶ W`
which is at once a pullback of `i` along `f'_k` and of `i''` along `f''_k`.

**Inherited caveat.** Thickenings of algebraic stacks are `AlgebraicGeometry.Stack.IsThickening`
(**Stacks 0BPP**, part (1)), which omits the homeomorphism-of-underlying-spaces clause of the
source for want of a library site for the point topology of Stacks 04XL.

## References

* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0CHJ](https://stacks.math.columbia.edu/tag/0CHJ)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
* [Stacks Project, Tag 0CJW](https://stacks.math.columbia.edu/tag/0CJW)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace CategoryTheory

/-- **A square is cartesian when it factors a cartesian square through a monomorphism.** Let
`(g, e)` be a pullback of `(i, f')`, and let `i''`, `f''` satisfy `g ≫ i'' = e ≫ f''`, with
`i''` cancellable on the right. If every commutative square over `(i'', f'')` produces a
factorisation of its second leg, composed with `f'`, through `i`, then `(g, e)` is also a
pullback of `(i'', f'')`. -/
theorem IsPullback.of_isPullback_of_cancel {C : Type*} [Category C] {U V W W' W'' : C}
    {g : U ⟶ W} {e : U ⟶ V} {i : W ⟶ W'} {f' : V ⟶ W'} {i'' : W ⟶ W''} {f'' : V ⟶ W''}
    (h₁ : IsPullback g e i f') (hw : g ≫ i'' = e ≫ f'')
    (hcancel : ∀ {T : C} (a b : T ⟶ W), a ≫ i'' = b ≫ i'' → a = b)
    (hfac : ∀ {T : C} (a : T ⟶ W) (b : T ⟶ V), a ≫ i'' = b ≫ f'' →
      ∃ v : T ⟶ W, v ≫ i = b ≫ f') :
    IsPullback g e i'' f'' := by
  have hex : ∀ s : PullbackCone i'' f'', ∃ l : s.pt ⟶ U, l ≫ g = s.fst ∧ l ≫ e = s.snd := by
    intro s
    obtain ⟨v, hv⟩ := hfac s.fst s.snd s.condition
    refine ⟨h₁.lift v s.snd hv, ?_, h₁.lift_snd _ _ _⟩
    rw [h₁.lift_fst]
    apply hcancel
    rw [← h₁.lift_fst v s.snd hv, Category.assoc, hw, ← Category.assoc, h₁.lift_snd, s.condition]
  choose l hl₁ hl₂ using hex
  exact ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw l hl₁ hl₂
    fun s m hm₁ hm₂ => h₁.hom_ext (by rw [hm₁, hl₁]) (by rw [hm₂, hl₂])⟩⟩

namespace Bicategory

variable {𝔅 : Type*} [Bicategory 𝔅]

/-- **Whiskering along equal 1-morphisms.** For `h : a = b`, whiskering by `a` is whiskering by
`b` read along the transports that `h` induces. -/
theorem whiskerLeft_eq_eqToHom_comp_whiskerLeft {A B C : 𝔅} {a b : A ⟶ B} (h : a = b)
    {u v : B ⟶ C} (η : u ⟶ v) :
    a ◁ η = eqToHom (congrArg (· ≫ u) h) ≫ b ◁ η ≫ eqToHom (congrArg (· ≫ v) h.symm) := by
  subst h
  simp

variable [Bicategory.Strict 𝔅]

/-- **Double whiskering along equal composites, in a strict bicategory.** If `a ≫ b = c ≫ d`,
then whiskering by `b` and then by `a` is whiskering by `d` and then by `c`, read along
transports. -/
theorem whiskerLeft_whiskerLeft_eq_of_comp_eq {A B B' C D : 𝔅} {a : A ⟶ B} {b : B ⟶ C}
    {c : A ⟶ B'} {d : B' ⟶ C} (h : a ≫ b = c ≫ d) {u v : C ⟶ D} (η : u ⟶ v)
    (h₁ : a ≫ (b ≫ u) = c ≫ (d ≫ u)) (h₂ : c ≫ (d ≫ v) = a ≫ (b ≫ v)) :
    a ◁ (b ◁ η) = eqToHom h₁ ≫ c ◁ (d ◁ η) ≫ eqToHom h₂ := by
  have e₁ := comp_whiskerLeft a b η
  have e₂ := comp_whiskerLeft c d η
  have e₃ := whiskerLeft_eq_eqToHom_comp_whiskerLeft h η
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv] at e₁ e₂
  rw [e₁, e₂] at e₃
  have e₄ : a ◁ (b ◁ η) = eqToHom (Strict.assoc a b u).symm ≫
      (eqToHom (Strict.assoc a b u) ≫ a ◁ (b ◁ η) ≫ eqToHom (Strict.assoc a b v).symm) ≫
        eqToHom (Strict.assoc a b v) := by
    simp
  rw [e₄, e₃]
  simp

/-- **Stacks 0CJW, the 2-cell computation, in a strict bicategory.** Write `i = δ ≫ p` and
`i'' = δ ≫ q`. If the comparison `α'⁻¹ ≫ α''` between the two fillers over `W` is `δ^*γ` read
along transports, and `e ≫ ψ = g ≫ δ`, then the pullback of `ψ^*γ⁻¹` along `e` is the pullback
of `α''⁻¹ ≫ α'` along `g`, read along transports. -/
theorem whiskerLeft_comparison_eq {A V W I W' W'' X' : 𝔅} (e : A ⟶ V) (g : A ⟶ W)
    (ψ : V ⟶ I) (δ : W ⟶ I) (p : I ⟶ W') (q : I ⟶ W'') (x' : W' ⟶ X') (x'' : W'' ⟶ X')
    {L : W ⟶ X'} (α' : L ≅ (δ ≫ p) ≫ x') (α'' : L ≅ (δ ≫ q) ≫ x'') (γ : p ≫ x' ≅ q ≫ x'')
    (he : e ≫ ψ = g ≫ δ) (e₁ : (δ ≫ p) ≫ x' = δ ≫ (p ≫ x'))
    (e₂ : δ ≫ (q ≫ x'') = (δ ≫ q) ≫ x'')
    (hδγ : α'.inv ≫ α''.hom = eqToHom e₁ ≫ δ ◁ γ.hom ≫ eqToHom e₂)
    (c₁ : e ≫ (ψ ≫ (q ≫ x'')) = g ≫ ((δ ≫ q) ≫ x''))
    (c₂ : g ≫ ((δ ≫ p) ≫ x') = e ≫ (ψ ≫ (p ≫ x'))) :
    e ◁ (ψ ◁ γ.inv) = eqToHom c₁ ≫ g ◁ (α''.inv ≫ α'.hom) ≫ eqToHom c₂ := by
  have hinv : α''.inv ≫ α'.hom = eqToHom e₂.symm ≫ δ ◁ γ.inv ≫ eqToHom e₁.symm := by
    calc α''.inv ≫ α'.hom
        = eqToHom e₂.symm ≫ δ ◁ γ.inv ≫ (δ ◁ γ.hom ≫ eqToHom e₂) ≫ α''.inv ≫ α'.hom := by
          simp [← whiskerLeft_comp_assoc]
      _ = eqToHom e₂.symm ≫ δ ◁ γ.inv ≫ (eqToHom e₁.symm ≫ α'.inv ≫ α''.hom) ≫
            α''.inv ≫ α'.hom := by
          rw [hδγ]
          simp
      _ = eqToHom e₂.symm ≫ δ ◁ γ.inv ≫ eqToHom e₁.symm := by simp
  rw [hinv, whiskerLeft_whiskerLeft_eq_of_comp_eq he γ.inv
    (by rw [← Strict.assoc, he, Strict.assoc]) (by rw [← Strict.assoc, ← he, Strict.assoc])]
  simp

/-- **The filler of a pasted rectangle whose inner filler is a transport, in a strict
bicategory.** If the filler of the inner square `T` is the transport along
`T.fst ≫ S.snd = T.snd ≫ k`, then the filler of the pasted rectangle is the filler of `S`
whiskered by `T.fst`, read along transports. -/
theorem TwoCommSq.paste_iso_hom_of_eqToHom {x y z t : 𝔅} {f : x ⟶ z} {g : y ⟶ z} {k : t ⟶ y}
    (S : TwoCommSq f g) (T : TwoCommSq S.snd k) (hT : T.fst ≫ S.snd = T.snd ≫ k)
    (hTiso : T.iso.hom = eqToHom hT) :
    (S.paste T).iso.hom = eqToHom (Strict.assoc T.fst S.fst f) ≫ T.fst ◁ S.iso.hom ≫
      eqToHom (by rw [← Strict.assoc, hT, Strict.assoc]) := by
  rw [TwoCommSq.paste_iso_hom, hTiso]
  simp [Strict.associator_eqToIso, eqToHom_whiskerRight]

end Bicategory

/-- **Inverting a coherence identity between transported isomorphisms.** If `Γ` is `v⁻¹ ≫ u`
read along transports, then `u` followed by `Γ⁻¹` is `v`, read along transports. -/
theorem eqToHom_comp_hom_comp_eqToHom_comp_inv {C : Type*} [Category C]
    {L₀ L₁ P₁ P₂ Q₁ Q₂ : C} (a : L₀ = L₁) (b : P₁ = P₂) (c₁ : Q₂ = Q₁) (c₂ : P₁ = P₂)
    (u : L₁ ≅ P₁) (v : L₁ ≅ Q₁) (Γ : Q₂ ≅ P₂)
    (hΓ : Γ.hom = eqToHom c₁ ≫ v.inv ≫ u.hom ≫ eqToHom c₂) :
    (eqToHom a ≫ u.hom ≫ eqToHom b) ≫ Γ.inv = eqToHom a ≫ v.hom ≫ eqToHom c₁.symm := by
  have hinv : Γ.inv = eqToHom c₂.symm ≫ u.inv ≫ v.hom ≫ eqToHom c₁.symm := by
    apply (cancel_epi Γ.hom).1
    rw [Iso.hom_inv_id, hΓ]
    simp
  rw [hinv]
  subst b
  simp

end CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The inclusion of a 2-fibre product along a thickening is a thickening of algebraic
spaces.** If `W = 𝒳 ×_{𝒳'} W'` along a thickening `ι : 𝒳 ⟶ 𝒳'`, with `W`, `W'` algebraic spaces
and second projection the 1-morphism attached to `i : W ⟶ W'`, then `i` is a thickening of
algebraic spaces: the second projection is a thickening of algebraic stacks by **Stacks 0BPR**,
and the morphism of representing algebraic spaces it induces is `i`. -/
theorem isThickeningHom_of_isTwoFibreProduct {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    {ι : 𝒳 ⟶ 𝒳'} (hι : IsThickening ι) {W W' : AlgebraicSpaces B S hS}
    {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
    {x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳'} {i : W ⟶ W'}
    {α : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'}
    (h : IsTwoFibreProduct
      (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
        (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x')) :
    Space.IsThickeningHom B S hS i := by
  have hth : IsThickening ((algebraicSpaceStackFunctor.{u, w} B S hS).map i) :=
    isThickening_baseChange B S hS ι x' _ h hι
  have key := isThickeningHom_representingMap_of_isThickening B S hS _ hth W.property W'.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have e : (ObjectProperty.homMk (representingMap B S hS _ _ W.obj W'.obj
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map i).hom) : W ⟶ W') = i :=
    ObjectProperty.hom_ext _ (representingMap_associatedMap B S hS W.obj W'.obj i.hom)
  exact e ▸ key

/-- **Smoothness of a morphism of algebraic spaces, read in the 2-category of algebraic
stacks.** A morphism of algebraic spaces over `S` is smooth exactly when the 1-morphism of
algebraic stacks it induces is smooth (**Stacks 075U**); this is
`AlgebraicGeometry.Stack.isSmooth_algebraicSpaceStackMap_iff` for
`AlgebraicGeometry.Stack.algebraicSpaceStackFunctor`. -/
theorem isSmooth_algebraicSpaceStackFunctor_map_iff {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    AlgebraicStacks.IsSmooth B S hS ((algebraicSpaceStackFunctor.{u, w} B S hS).map f) ↔
      Space.IsSmooth B S hS f.hom :=
  isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS X.property Y.property f.hom

/-- **A base change of a smooth 1-morphism to an algebraic space is smooth.** If
`I = W' ×_{𝒳'} W''` is a 2-fibre product of algebraic spaces over an algebraic stack, with
projections attached to `p : I ⟶ W'` and `q : I ⟶ W''`, and `x'' : W'' ⟶ 𝒳'` is smooth, then
`p` is a smooth morphism of algebraic spaces (**Stacks 075W**). -/
theorem isSmooth_fst_of_isTwoFibreProduct {𝒳' : AlgebraicStacks.{u, w} B S hS}
    {W' W'' I : AlgebraicSpaces B S hS}
    {x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳'}
    {x'' : (algebraicSpaceStackFunctor B S hS).obj W'' ⟶ 𝒳'} {p : I ⟶ W'} {q : I ⟶ W''}
    {γ : (algebraicSpaceStackFunctor B S hS).map p ≫ x' ≅
      (algebraicSpaceStackFunctor B S hS).map q ≫ x''}
    (h : IsTwoFibreProduct
      (⟨(algebraicSpaceStackFunctor B S hS).obj I, (algebraicSpaceStackFunctor B S hS).map p,
        (algebraicSpaceStackFunctor B S hS).map q, γ⟩ : TwoCommSq x' x''))
    (hx'' : AlgebraicStacks.IsSmooth B S hS x'') :
    Space.IsSmooth B S hS p.hom :=
  (isSmooth_algebraicSpaceStackFunctor_map_iff.{u, w} p).1
    (AlgebraicStacks.isSmooth_baseChange B S hS x'' x' _ h hx'')

/-- **A morphism into the ambient space factors through a 2-fibre product along the inner
stack.** Let `W = 𝒳 ×_{𝒳'} W'` be a 2-fibre product with `W`, `W'` algebraic spaces and second
projection attached to `i : W ⟶ W'`. A morphism `t : T ⟶ W'` from an algebraic space whose
composite to `𝒳'` factors, up to 2-isomorphism, through `ι : 𝒳 ⟶ 𝒳'` factors through `i`. -/
theorem exists_comp_eq_of_isTwoFibreProduct {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    {ι : 𝒳 ⟶ 𝒳'} {W W' : AlgebraicSpaces B S hS}
    {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
    {x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳'} {i : W ⟶ W'}
    {α : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'}
    (h : IsTwoFibreProduct
      (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
        (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x'))
    {T : AlgebraicSpaces B S hS} (t : T ⟶ W')
    (y : (algebraicSpaceStackFunctor B S hS).obj T ⟶ 𝒳)
    (e₀ : y ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map t ≫ x') :
    ∃ v : T ⟶ W, v ≫ i = t := by
  let d := twoFibreProductPreHom h (⟨_, y, _, e₀⟩ : TwoCommSq ι x')
  let v : T ⟶ W := ObjectProperty.homMk (representingMap B S hS _ _ T.obj W.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) d.hom.hom)
  have hv : (algebraicSpaceStackFunctor B S hS).map v = d.hom :=
    algebraicSpaceStackFunctor_map_homMk_representingMap d.hom
  refine ⟨v, algebraicSpaceStackFunctor_map_injective ?_⟩
  rw [Functor.map_comp, hv]
  exact (eq_of_hom₂_algebraicSpaceStackFunctor_obj d.isoSnd.hom).symm

/-- **Transporting a factorisation through the functor from algebraic spaces.** From
`a ≫ b = c ≫ d` in algebraic spaces, the two composites with a 1-morphism `y` out of the stack of
the common target agree. -/
theorem algebraicSpaceStackFunctor_map_comp_whisker_eq {X Y Y' Z : AlgebraicSpaces B S hS}
    {𝒴 : AlgebraicStacks.{u, w} B S hS} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Y'} {d : Y' ⟶ Z}
    (h : a ≫ b = c ≫ d) (y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Z ⟶ 𝒴) :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map a ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map b ≫ y) =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map c ≫
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map d ≫ y) :=
  congrArg (fun m => (algebraicSpaceStackFunctor.{u, w} B S hS).map m ≫ y) h

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'}

/-- **Stacks 0CJW, from the strong local lifting property of smooth morphisms (Stacks 0CHJ).**
Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over `S` and let `W = 𝒳 ×_{𝒳'} W'` and
`W = 𝒳 ×_{𝒳'} W''` be two 2-fibre products, along `x' : W' ⟶ 𝒳'` and `x'' : W'' ⟶ 𝒳'`, with
`W`, `W'`, `W''` algebraic spaces, inclusions `i : W ⟶ W'`, `i'' : W ⟶ W''`, fillers `α'`, `α''`
and the vertical 1-morphisms `x`, `x'`, `x''` smooth. Then there are an étale covering
`{f'_k : W'_k ⟶ W'}`, étale morphisms `f''_k : W'_k ⟶ W''` and 2-isomorphisms
`γ_k : x'' ∘ f''_k ≅ x' ∘ f'_k` such that, for each `k`, a single algebraic space `U` with
`e : U ⟶ W'_k` and `g : U ⟶ W` is a pullback both of `i` along `f'_k` and of `i''` along `f''_k`
(clauses (a) and (b)), and `γ_k` restricted to `U` is the filler `α''⁻¹ ≫ α'` of the given
diagram over `W`, restricted along `g` (clause (c)).

The last step of the source, Stacks 0CHJ, is the hypothesis `hlift`, in exactly the form of
`AlgebraicGeometry.Space.exists_isEtaleCovering_lift_of_isSmooth_of_isThickeningHom`; see the
module documentation. The smoothness of `x` is part of the source's hypotheses and is not used. -/
theorem exists_isEtaleCovering_ambientComparison_of_lifting
    (hlift : ∀ {X Y T T' : AlgebraicSpaces B S hS} {f : X ⟶ Y},
      Space.IsSmooth B S hS f.hom → ∀ {i : T ⟶ T'}, Space.IsThickeningHom B S hS i →
      ∀ (a : T ⟶ X) (b : T' ⟶ Y), a ≫ f = i ≫ b →
      ∃ (Z : Space.points B S hS T'.obj → BigFppfOver B S hS)
        (q : ∀ p, yoneda.obj (Z p) ⟶ T'.obj),
        (∀ p, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z p))) ∧
        Space.IsEtaleCovering B S hS (fun p ↦ yoneda.obj (Z p)) q ∧
        ∀ p, ∃ ψ : yoneda.obj (Z p) ⟶ X.obj,
          ψ ≫ f.hom = q p ≫ b.hom ∧
          pullback.snd i.hom (q p) ≫ ψ = pullback.fst i.hom (q p) ≫ a.hom)
    (hι : IsThickening ι) {W W' W'' : AlgebraicSpaces B S hS}
    {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
    {x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳'}
    {x'' : (algebraicSpaceStackFunctor B S hS).obj W'' ⟶ 𝒳'}
    (_hx : AlgebraicStacks.IsSmooth B S hS x) (hx' : AlgebraicStacks.IsSmooth B S hS x')
    (hx'' : AlgebraicStacks.IsSmooth B S hS x'')
    {i : W ⟶ W'} {i'' : W ⟶ W''}
    {α' : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'}
    {α'' : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i'' ≫ x''}
    (h' : IsTwoFibreProduct (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
        (algebraicSpaceStackFunctor B S hS).map i, α'⟩ : TwoCommSq ι x'))
    (h'' : IsTwoFibreProduct (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
        (algebraicSpaceStackFunctor B S hS).map i'', α''⟩ : TwoCommSq ι x'')) :
    ∃ (K : Type (u + 1)) (V : K → AlgebraicSpaces B S hS) (f' : ∀ k, V k ⟶ W')
      (f'' : ∀ k, V k ⟶ W'')
      (γ : ∀ k, (algebraicSpaceStackFunctor B S hS).map (f'' k) ≫ x'' ≅
        (algebraicSpaceStackFunctor B S hS).map (f' k) ≫ x'),
      Space.IsEtaleCovering B S hS (fun k => (V k).obj) (fun k => (f' k).hom) ∧
      (∀ k, Space.IsEtale B S hS (f'' k).hom) ∧
      ∀ k, ∃ (U : AlgebraicSpaces B S hS) (e : U ⟶ V k) (g : U ⟶ W)
        (h₁ : IsPullback g e i (f' k)) (h₂ : IsPullback g e i'' (f'' k)),
        (algebraicSpaceStackFunctor B S hS).map e ◁ (γ k).hom =
          eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq h₂.w.symm x'') ≫
            ((algebraicSpaceStackFunctor B S hS).map g ◁ (α''.inv ≫ α'.hom)) ≫
            eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq h₁.w x') := by
  classical
  -- `I' = W' ×_{𝒳'} W''`, with `p' : I' ⟶ W'` smooth as a base change of `x''`.
  obtain ⟨I, p, q, γ, ⟨hI⟩⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor x' x''
  have hp : Space.IsSmooth B S hS p.hom := isSmooth_fst_of_isTwoFibreProduct hI hx''
  have hi : Space.IsThickeningHom B S hS i := isThickeningHom_of_isTwoFibreProduct hι h'
  have hi'' : Space.IsThickeningHom B S hS i'' := isThickeningHom_of_isTwoFibreProduct hι h''
  -- the section `δ : W ⟶ I'` defined by the filler `α'⁻¹ ≫ α''` over `W`
  obtain ⟨δ, hδp, hδq, hδγ⟩ :=
    exists_lift_of_isTwoFibreProduct_algebraicSpaceStackFunctor hI i i'' (α'.symm ≪≫ α'')
  subst hδp hδq
  -- Stacks 0CHJ extends `δ` over an étale covering of `W'`
  obtain ⟨Z, r, -, hcov, hψ⟩ := hlift hp hi δ (𝟙 W') (by rw [Category.comp_id])
  choose ψ hψp hψδ using hψ
  let V : Space.points B S hS W'.obj → AlgebraicSpaces B S hS :=
    fun k => Space.representedAlgebraicSpace B S hS (Z k)
  let ψ' : ∀ k, V k ⟶ I := fun k => ObjectProperty.homMk (ψ k)
  have hr : ∀ k, (ψ' k ≫ p).hom = r k := fun k =>
    (show ψ k ≫ p.hom = r k by simpa using hψp k)
  let γk : ∀ k, (algebraicSpaceStackFunctor B S hS).map (ψ' k ≫ q) ≫ x'' ≅
      (algebraicSpaceStackFunctor B S hS).map (ψ' k ≫ p) ≫ x' := fun k =>
    whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map (ψ' k)) γ.symm
  have hcov' : Space.IsEtaleCovering B S hS (fun k => (V k).obj) (fun k => (ψ' k ≫ p).hom) := by
    rwa [show (fun k => (ψ' k ≫ p).hom) = r from funext hr]
  refine ⟨_, V, fun k => ψ' k ≫ p, fun k => ψ' k ≫ q, γk, hcov', ?_⟩
  have key : ∀ k, Space.IsEtale B S hS (ψ' k ≫ q).hom ∧
      ∃ (U : AlgebraicSpaces B S hS) (e : U ⟶ V k) (g : U ⟶ W)
        (h₁ : IsPullback g e (δ ≫ p) (ψ' k ≫ p)) (h₂ : IsPullback g e (δ ≫ q) (ψ' k ≫ q)),
        (algebraicSpaceStackFunctor B S hS).map e ◁ (γk k).hom =
          eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq h₂.w.symm x'') ≫
            ((algebraicSpaceStackFunctor B S hS).map g ◁ (α''.inv ≫ α'.hom)) ≫
            eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq h₁.w x') := by
    intro k
    -- `W_k = W ×_{W'} W'_k`
    let U := AlgebraicSpaces.fiberProduct B S hS (δ ≫ p) (ψ' k ≫ p)
    let g : U ⟶ W := ObjectProperty.homMk (pullback.fst (δ ≫ p).hom (ψ' k ≫ p).hom)
    let e : U ⟶ V k := ObjectProperty.homMk (pullback.snd (δ ≫ p).hom (ψ' k ≫ p).hom)
    have h₁ : IsPullback g e (δ ≫ p) (ψ' k ≫ p) :=
      AlgebraicSpaces.isPullback_fiberProduct B S hS (δ ≫ p) (ψ' k ≫ p)
    have hψδ' : pullback.snd (δ ≫ p).hom (ψ' k ≫ p).hom ≫ ψ k =
        pullback.fst (δ ≫ p).hom (ψ' k ≫ p).hom ≫ δ.hom := by
      rw [hr k]
      exact hψδ k
    have he : e ≫ ψ' k = g ≫ δ := ObjectProperty.hom_ext _ hψδ'
    have hw₂ : g ≫ (δ ≫ q) = e ≫ (ψ' k ≫ q) := by
      rw [← Category.assoc, ← he, Category.assoc]
    -- (c): the pullback of `γ_k` to `W_k` is the filler of the initial diagram
    have hc : (algebraicSpaceStackFunctor B S hS).map e ◁ (γk k).hom =
        eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq hw₂.symm x'') ≫
          ((algebraicSpaceStackFunctor B S hS).map g ◁ (α''.inv ≫ α'.hom)) ≫
          eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq h₁.w x') :=
      Bicategory.whiskerLeft_comparison_eq ((algebraicSpaceStackFunctor B S hS).map e)
        ((algebraicSpaceStackFunctor B S hS).map g) ((algebraicSpaceStackFunctor B S hS).map (ψ' k))
        ((algebraicSpaceStackFunctor B S hS).map δ) ((algebraicSpaceStackFunctor B S hS).map p)
        ((algebraicSpaceStackFunctor B S hS).map q) x' x'' α' α'' γ
        (congrArg (algebraicSpaceStackFunctor B S hS).map he) rfl rfl (hδγ rfl rfl) _ _
    -- (a) and (b): `W_k` is also `W ×_{W''} W'_k`
    have hcancel : ∀ {T : AlgebraicSpaces B S hS} (a b : T ⟶ W),
        a ≫ (δ ≫ q) = b ≫ (δ ≫ q) → a = b := by
      intro T a b hab
      have := hi''.mono
      exact ObjectProperty.hom_ext _ ((cancel_mono (δ ≫ q).hom).1 (congrArg (fun m => m.hom) hab))
    have hfac : ∀ {T : AlgebraicSpaces B S hS} (a : T ⟶ W) (b : T ⟶ V k),
        a ≫ (δ ≫ q) = b ≫ (ψ' k ≫ q) → ∃ v : T ⟶ W, v ≫ (δ ≫ p) = b ≫ (ψ' k ≫ p) :=
      fun a b hab => exists_comp_eq_of_isTwoFibreProduct h' (b ≫ (ψ' k ≫ p))
        ((algebraicSpaceStackFunctor B S hS).map a ≫ x)
        (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map a) α'' ≪≫
          eqToIso (algebraicSpaceStackFunctor_map_comp_whisker_eq hab x'') ≪≫
          whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map b) (γk k))
    have h₂ : IsPullback g e (δ ≫ q) (ψ' k ≫ q) :=
      IsPullback.of_isPullback_of_cancel h₁ hw₂ hcancel hfac
    refine ⟨?_, U, e, g, h₁, h₂, hc⟩
    -- `f''_k` is étale, by the étale clause of Stacks 0CJC
    have hf'et : Space.IsEtale B S hS (ψ' k ≫ p).hom := hcov'.etale k
    have hget : Space.IsEtale B S hS g.hom :=
      Space.isEtale_of_isPullback B S hS e g (ψ' k ≫ p) (δ ≫ p) h₁.flip hf'et
    -- `W_k = 𝒳 ×_{𝒳'} W'_k`, pasting `W = 𝒳 ×_{𝒳'} W'` with `W_k = W ×_{W'} W'_k`
    let Psq : TwoCommSq ι x' := ⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
      (algebraicSpaceStackFunctor B S hS).map (δ ≫ p), α'⟩
    have hpb := AlgebraicSpaces.isPullback_hom B S hS h₁
    let Tsq : TwoCommSq Psq.snd ((algebraicSpaceStackFunctor B S hS).map (ψ' k ≫ p)) :=
      algebraicSpaceStackSquare.{u, w} B S hS W.property (V k).property W'.property U.property
        hpb.w
    have hT : IsTwoFibreProduct Tsq :=
      isTwoFibreProduct_algebraicSpaceStackSquare.{u, w} B S hS W.property (V k).property
        W'.property U.property hpb
    have hU : IsTwoFibreProduct (Psq.paste Tsq) := isTwoFibreProduct_paste h' hT
    have hTeq : Tsq.fst ≫ Psq.snd = Tsq.snd ≫ (algebraicSpaceStackFunctor B S hS).map (ψ' k ≫ p) :=
      eq_of_hom₂_algebraicSpaceStackFunctor_obj (Y := W') Tsq.iso.hom
    have hα := TwoCommSq.paste_iso_hom_of_eqToHom Psq Tsq hTeq
      ((subsingleton_hom₂_algebraicSpaceStackFunctor_obj (Y := W') _ _).elim _ _)
    have hΓ : (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map e) (γk k)).hom =
        eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq hw₂.symm x'') ≫
          (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map g) α'').inv ≫
          (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map g) α').hom ≫
          eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq h₁.w x') := by
      rwa [whiskerLeft_comp, Category.assoc] at hc
    have hcoh : (Psq.paste Tsq).iso.hom ≫
        ((algebraicSpaceStackFunctor B S hS).map e ◁ (γk k).inv) =
        eqToHom rfl ≫ ((algebraicSpaceStackFunctor B S hS).map g ◁ α''.hom) ≫
          eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq hw₂ x'') := by
      rw [hα]
      exact eqToHom_comp_hom_comp_eqToHom_comp_inv _ _ _ _
        (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map g) α')
        (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map g) α'')
        (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map e) (γk k)) hΓ
    have hsm : AlgebraicStacks.IsSmooth B S hS
        ((algebraicSpaceStackFunctor B S hS).map (ψ' k ≫ p) ≫ x') :=
      AlgebraicStacks.isSmooth_comp B S hS _ _
        ((isSmooth_algebraicSpaceStackFunctor_map_iff _).2
          (Space.isSmooth_of_isEtale B S hS W'.property hf'et)) hx'
    exact isEtale_of_isTwoFibreProduct_of_isThickening (U := U) (U' := V k) (V := W) (V' := W'')
      (i := e) (j := δ ≫ q) (u := (algebraicSpaceStackFunctor B S hS).map g ≫ x) (v := x)
      (x' := (algebraicSpaceStackFunctor B S hS).map (ψ' k ≫ p) ≫ x') (y' := x'')
      (α := (Psq.paste Tsq).iso) (β := α'') hι hU h''
      (AlgebraicStacks.isFlat_of_isSmooth B S hS _ hsm)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _ hsm)
      (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _ hx''))
      (f := g) (f' := ψ' k ≫ q) rfl rfl hw₂.symm (γk k).inv
      (algebraicSpaceStackFunctor_map_comp_whisker_eq hw₂ x'') hcoh hget
  exact ⟨fun k => (key k).1, fun k => (key k).2⟩

/-- **Stacks 0CJW.** Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over `S` and let
`W = 𝒳 ×_{𝒳'} W'` and `W = 𝒳 ×_{𝒳'} W''` be two 2-fibre products, along `x' : W' ⟶ 𝒳'` and
`x'' : W'' ⟶ 𝒳'`, with `W`, `W'`, `W''` algebraic spaces, inclusions `i : W ⟶ W'`,
`i'' : W ⟶ W''`, fillers `α'`, `α''` and the vertical 1-morphisms `x`, `x'`, `x''` smooth. Then
there are an étale covering `{f'_k : W'_k ⟶ W'}`, étale morphisms `f''_k : W'_k ⟶ W''` and
2-isomorphisms `γ_k : x'' ∘ f''_k ≅ x' ∘ f'_k` such that, for each `k`, a single algebraic space
`U` with `e : U ⟶ W'_k` and `g : U ⟶ W` is a pullback both of `i` along `f'_k` and of `i''` along
`f''_k` — that is, `(f'_k)⁻¹(W) = (f''_k)⁻¹(W)` and the two restrictions to it agree — and `γ_k`
restricted to `U` is the filler `α''⁻¹ ≫ α'` of the given diagram over `W`, restricted along `g`.

This is `exists_isEtaleCovering_ambientComparison_of_lifting` at Stacks 0CHJ,
`AlgebraicGeometry.Space.exists_isEtaleCovering_lift_of_isSmooth_of_isThickeningHom`. The
smoothness of `x` is part of the source's hypotheses and is not used. -/
@[stacks 0CJW]
theorem exists_isEtaleCovering_ambientComparison
    (hι : IsThickening ι) {W W' W'' : AlgebraicSpaces B S hS}
    {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
    {x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳'}
    {x'' : (algebraicSpaceStackFunctor B S hS).obj W'' ⟶ 𝒳'}
    (hx : AlgebraicStacks.IsSmooth B S hS x) (hx' : AlgebraicStacks.IsSmooth B S hS x')
    (hx'' : AlgebraicStacks.IsSmooth B S hS x'')
    {i : W ⟶ W'} {i'' : W ⟶ W''}
    {α' : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'}
    {α'' : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i'' ≫ x''}
    (h' : IsTwoFibreProduct (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
        (algebraicSpaceStackFunctor B S hS).map i, α'⟩ : TwoCommSq ι x'))
    (h'' : IsTwoFibreProduct (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
        (algebraicSpaceStackFunctor B S hS).map i'', α''⟩ : TwoCommSq ι x'')) :
    ∃ (K : Type (u + 1)) (V : K → AlgebraicSpaces B S hS) (f' : ∀ k, V k ⟶ W')
      (f'' : ∀ k, V k ⟶ W'')
      (γ : ∀ k, (algebraicSpaceStackFunctor B S hS).map (f'' k) ≫ x'' ≅
        (algebraicSpaceStackFunctor B S hS).map (f' k) ≫ x'),
      Space.IsEtaleCovering B S hS (fun k => (V k).obj) (fun k => (f' k).hom) ∧
      (∀ k, Space.IsEtale B S hS (f'' k).hom) ∧
      ∀ k, ∃ (U : AlgebraicSpaces B S hS) (e : U ⟶ V k) (g : U ⟶ W)
        (h₁ : IsPullback g e i (f' k)) (h₂ : IsPullback g e i'' (f'' k)),
        (algebraicSpaceStackFunctor B S hS).map e ◁ (γ k).hom =
          eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq h₂.w.symm x'') ≫
            ((algebraicSpaceStackFunctor B S hS).map g ◁ (α''.inv ≫ α'.hom)) ≫
            eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq h₁.w x') :=
  exists_isEtaleCovering_ambientComparison_of_lifting
    (fun hf _ hi a b h => Space.exists_isEtaleCovering_lift_of_isSmooth_of_isThickeningHom
      B S hS hf hi a b h) hι hx hx' hx'' h' h''

end AlgebraicGeometry.Stack

end
