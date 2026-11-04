module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory
public import StacksFrontier.CategoryTheory.Bicategory.TwoOneCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid

/-!
# Endomorphisms of a smooth lift as sections of the self-intersection

Fix a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks, an algebraic space `W` with a smooth
1-morphism `x : W ⟶ 𝒳`, and a smooth lift `ξ = (U, U', a, i, x', α)` of an étale open of `W`
(`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP). The proof of Stacks 0CKG describes the
endomorphisms of `ξ` over the identity of `U` through the algebraic space
`I' = U' ×_{x', 𝒳', x'} U'` with projections `p', q'` and universal 2-isomorphism
`γ : x' ∘ p' ≅ x' ∘ q'`: an endomorphism `σ = (id, f', γ_σ)` is the section `δ_σ : U' ⟶ I'` of
`p'` with `q' ∘ δ_σ = f'` and `δ_σ^*γ = γ_σ`. This file sets up that description and proves the
three properties of it that the argument of Stacks 0CKG consumes:

* `AlgebraicGeometry.Stack.EtaleSmoothLift.autLift_injective`: `σ` is determined by `δ_σ` (and
  its base);
* `AlgebraicGeometry.Stack.EtaleSmoothLift.autLift_comp`: `δ_{σ ≫ τ} = R_τ ∘ δ_σ`, where the
  *right translation* `R_τ : I' ⟶ I'` (`AlgebraicGeometry.Stack.EtaleSmoothLift.rightTranslation`)
  sends a point `(a, b, η)` to `(a, f'_τ ∘ b, b^*γ_τ ∘ η)` — composition with `τ` in the groupoid
  `I' ⇉ U'` of Stacks 04T4, which is how the source describes composition in `Aut(ξ)`;
* `AlgebraicGeometry.Stack.EtaleSmoothLift.comp_rightTranslation_of_fst`: for `τ` over the
  identity, `R_τ` fixes every point of `I'` whose first projection lies over `U`.

## Implementation notes

All 2-cell identities are proved in an arbitrary strict bicategory, with every composite
1-morphism of the application a variable carrying its defining equation and every equality along
which a 2-cell is transported quantified over, and only instantiated in
`AlgebraicGeometry.Stack.AlgebraicStacks`. Rewriting is not available there (see
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory`), and the definitional equation
`(algebraicSpaceStackFunctor B S hS).map (h ≫ p) = (algebraicSpaceStackFunctor B S hS).map h ≫ …`
is avoided in statements because checking it is expensive.

## References

* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory.Bicategory

universe w₀ v₀ u₀

variable {𝔅 : Type u₀} [Bicategory.{w₀, v₀} 𝔅] [Bicategory.Strict 𝔅]

/-- If `r^*γ = (q^*c) ∘ γ` along equalities, then `r ◁ γ` is `γ` followed by `q ◁ c`, along
`eqToHom`s. -/
private theorem whiskerLeft_eq_of_translation_aux {A P C : 𝔅} {x : A ⟶ C} {pp qq : P ⟶ A}
    (γ : pp ≫ x ⟶ qq ≫ x) {t : A ⟶ A} {r : P ⟶ P} (hrp : r ≫ pp = pp) (hrq : r ≫ qq = qq ≫ t)
    (cτ : x ⟶ t ≫ x)
    (hr : ∀ (e₀ : qq ≫ t ≫ x = (qq ≫ t) ≫ x) (e₁ : pp ≫ x = r ≫ pp ≫ x)
      (e₂ : r ≫ qq ≫ x = (qq ≫ t) ≫ x),
      γ ≫ (qq ◁ cτ) ≫ eqToHom e₀ = eqToHom e₁ ≫ (r ◁ γ) ≫ eqToHom e₂) :
    r ◁ γ = eqToHom (by simp only [← Strict.assoc, hrp]) ≫ γ ≫ (qq ◁ cτ) ≫
      eqToHom (by simp only [← Strict.assoc, hrq]) := by
  have h := ((eqToHom_comp_iff _ _ _).mp (hr (by simp only [Strict.assoc])
    (by simp only [← Strict.assoc, hrp]) (by simp only [← Strict.assoc, hrq])).symm)
  rw [comp_eqToHom_iff] at h
  simpa only [Category.assoc, eqToHom_trans] using h

/-- **The filler of a 2-fibre product pulled back along a composite with a translation.** In a
strict bicategory let `γ : p ∘ x ⟶ q ∘ x` be a 2-cell over `P ⟶ A ⟶ C`, let `d : A ⟶ P` be a
section of `p` with `d^*γ = c_σ` (where `q ∘ d = s`), let `r : P ⟶ P` satisfy `p ∘ r = p`,
`q ∘ r = t ∘ q` and `r^*γ = (q^*c_τ) ∘ γ`, and let `e : A ⟶ P` be a section of `p` with
`q ∘ e = t ∘ s` and `e^*γ = (s^*c_τ) ∘ c_σ`. Then `e^*γ = (r ∘ d)^*γ`, all read along the
equalities of 1-morphisms. Every 1-morphism that is a composite in the application is a variable
here with its defining equation, and every equality along which a 2-cell is transported is
quantified over, so that the statement is instantiated without unfolding anything. -/
theorem whiskerLeft_eq_of_translation {A P C : 𝔅} {x : A ⟶ C} {pp qq : P ⟶ A}
    (γ : pp ≫ x ⟶ qq ≫ x) {one s t st : A ⟶ A} {m : P ⟶ A} {d e dr : A ⟶ P} {r : P ⟶ P}
    (hone : one = 𝟙 A) (hst : st = s ≫ t) (hm : m = qq ≫ t) (hdr : dr = d ≫ r)
    (hdp : d ≫ pp = one) (hdq : d ≫ qq = s) (hrp : r ≫ pp = pp) (hrq : r ≫ qq = m)
    (hep : e ≫ pp = one) (heq : e ≫ qq = st)
    (cσ : x ⟶ s ≫ x) (cτ : x ⟶ t ≫ x)
    (hd : ∀ (e₀ : one ≫ x = x) (e₁ : one ≫ x = d ≫ pp ≫ x) (e₂ : d ≫ qq ≫ x = s ≫ x),
      eqToHom e₀ ≫ cσ = eqToHom e₁ ≫ (d ◁ γ) ≫ eqToHom e₂)
    (hr : ∀ (e₀ : qq ≫ t ≫ x = m ≫ x) (e₁ : pp ≫ x = r ≫ pp ≫ x) (e₂ : r ≫ qq ≫ x = m ≫ x),
      γ ≫ (qq ◁ cτ) ≫ eqToHom e₀ = eqToHom e₁ ≫ (r ◁ γ) ≫ eqToHom e₂)
    (he : ∀ (e₀ : one ≫ x = x) (e₁ : one ≫ x = e ≫ pp ≫ x) (e₂ : e ≫ qq ≫ x = st ≫ x)
      (e₃ : s ≫ t ≫ x = st ≫ x),
      eqToHom e₀ ≫ cσ ≫ (s ◁ cτ) ≫ eqToHom e₃ = eqToHom e₁ ≫ (e ◁ γ) ≫ eqToHom e₂)
    (e₁ : e ≫ pp ≫ x = dr ≫ pp ≫ x) (e₂ : dr ≫ qq ≫ x = e ≫ qq ≫ x) :
    e ◁ γ = eqToHom e₁ ≫ (dr ◁ γ) ≫ eqToHom e₂ := by
  subst hone hst hm hdr hdq
  have hdγ : d ◁ γ = eqToHom (by simp only [← Strict.assoc, hdp, Category.id_comp]) ≫
      eqToHom (Category.id_comp x) ≫ cσ ≫ eqToHom (by simp only [← Strict.assoc]) := by
    have h := ((eqToHom_comp_iff _ _ _).mp (hd (Category.id_comp x)
      (by simp only [← Strict.assoc, hdp, Category.id_comp]) (by simp only [← Strict.assoc])).symm)
    rw [comp_eqToHom_iff] at h
    simpa only [Category.assoc] using h
  have hrγ := whiskerLeft_eq_of_translation_aux γ hrp hrq cτ hr
  have heγ : e ◁ γ = eqToHom (by simp only [← Strict.assoc, hep, Category.id_comp]) ≫
      eqToHom (Category.id_comp x) ≫ cσ ≫ ((d ≫ qq) ◁ cτ) ≫
        eqToHom (by simp only [← Strict.assoc, heq]) := by
    have h := ((eqToHom_comp_iff _ _ _).mp (he (Category.id_comp x)
      (by simp only [← Strict.assoc, hep, Category.id_comp]) (by simp only [← Strict.assoc, heq])
      (by simp only [← Strict.assoc])).symm)
    rw [comp_eqToHom_iff] at h
    simpa only [Category.assoc, eqToHom_trans] using h
  rw [heγ]
  simp only [hdγ, hrγ, comp_whiskerLeft, whiskerLeft_comp, Strict.associator_eqToIso, eqToIso.hom,
    eqToIso.inv, Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

/-- Whiskering by equal 1-morphisms, along eqToHom. -/
theorem whiskerLeft_eq_eqToHom_comp {A P C : 𝔅} {f f' : A ⟶ P} (h : f = f') {g g' : P ⟶ C}
    (η : g ⟶ g') (e₁ : f ≫ g = f' ≫ g) (e₂ : f' ≫ g' = f ≫ g') :
    f ◁ η = eqToHom e₁ ≫ (f' ◁ η) ≫ eqToHom e₂ := by
  subst h
  simp

/-- **A comparison 2-cell restricting to the identity along a filler.** If `α : L ⟶ j ∘ x` is an
invertible 2-cell and `α ∘ (j^*c) = (one^*α)` along equalities, with `one` an identity, then
`j^*c` is an identity read along an equality. -/
theorem whiskerLeft_eq_eqToHom_of_coherence {U₀ A C : 𝔅} {L : U₀ ⟶ C} {j : U₀ ⟶ A}
    {x : A ⟶ C} {t : A ⟶ A} {one : U₀ ⟶ U₀} (hone : one = 𝟙 U₀) (α : L ⟶ j ≫ x) [IsIso α]
    (c : x ⟶ t ≫ x) (e₁ : L = one ≫ L) (e₂ : one ≫ j ≫ x = j ≫ t ≫ x)
    (hcoh : α ≫ (j ◁ c) = eqToHom e₁ ≫ (one ◁ α) ≫ eqToHom e₂) (e : j ≫ x = j ≫ t ≫ x) :
    j ◁ c = eqToHom e := by
  subst hone
  simp only [id_whiskerLeft, Strict.leftUnitor_eqToIso] at hcoh
  simp only [eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, eqToHom_trans] at hcoh
  exact (cancel_epi α).1 hcoh

/-- **Right translation fixes the points whose second coordinate lies over the closed
substack.** In a strict bicategory let `r : P ⟶ P` satisfy `p ∘ r = p`, `q ∘ r = t ∘ q` and
`r^*γ = (q^*c) ∘ γ`, and let `z : T ⟶ P` have `q ∘ z = j ∘ v` with `j^*c` an identity. Then
`(r ∘ z)^*γ = z^*γ` along equalities. -/
theorem whiskerLeft_comp_eq_of_translation_trivial {T U₀ A P C : 𝔅} {x : A ⟶ C}
    {pp qq : P ⟶ A} (γ : pp ≫ x ⟶ qq ≫ x) {t : A ⟶ A} {m : P ⟶ A} {r : P ⟶ P}
    {z zr : T ⟶ P} {v : T ⟶ U₀} {j : U₀ ⟶ A} (hm : m = qq ≫ t) (hzr : zr = z ≫ r)
    (hrp : r ≫ pp = pp) (hrq : r ≫ qq = m) (hzq : z ≫ qq = v ≫ j) (hjt : j ≫ t = j)
    (cτ : x ⟶ t ≫ x)
    (hr : ∀ (e₀ : qq ≫ t ≫ x = m ≫ x) (e₁ : pp ≫ x = r ≫ pp ≫ x) (e₂ : r ≫ qq ≫ x = m ≫ x),
      γ ≫ (qq ◁ cτ) ≫ eqToHom e₀ = eqToHom e₁ ≫ (r ◁ γ) ≫ eqToHom e₂)
    (hj : ∀ e : j ≫ x = j ≫ t ≫ x, j ◁ cτ = eqToHom e)
    (e₁ : zr ≫ pp ≫ x = z ≫ pp ≫ x) (e₂ : z ≫ qq ≫ x = zr ≫ qq ≫ x) :
    zr ◁ γ = eqToHom e₁ ≫ (z ◁ γ) ≫ eqToHom e₂ := by
  subst hm hzr
  have hrγ := whiskerLeft_eq_of_translation_aux γ hrp hrq cτ hr
  have hjt' : j ≫ t ≫ x = j ≫ x := by rw [← Strict.assoc, hjt]
  have hzq' : ∀ y : A ⟶ C, z ≫ qq ≫ y = v ≫ j ≫ y := fun y => by
    rw [← Strict.assoc, hzq, Strict.assoc]
  have hz : ∀ e : z ≫ qq ≫ x = z ≫ qq ≫ t ≫ x, z ◁ (qq ◁ cτ) = eqToHom e := by
    intro e
    have h₁ : z ◁ (qq ◁ cτ) = (α_ z qq x).inv ≫ ((z ≫ qq) ◁ cτ) ≫ (α_ z qq (t ≫ x)).hom := by
      rw [comp_whiskerLeft]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Iso.inv_hom_id_assoc]
    rw [h₁, whiskerLeft_eq_eqToHom_comp hzq cτ (by rw [hzq]) (by rw [hzq]), comp_whiskerLeft,
      hj (hjt'.symm)]
    simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
      Bicategory.whiskerLeft_eqToHom, eqToHom_trans]
  rw [comp_whiskerLeft, hrγ]
  simp only [whiskerLeft_comp, Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
    hz ((hzq' x).trans ((congrArg (v ≫ ·) hjt'.symm).trans (hzq' (t ≫ x)).symm))]

end CategoryTheory.Bicategory

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

/-- Equal composites `h ≫ k = h' ≫ k` stay equal after a functor and postcomposition. -/
theorem map_comp_map_comp_eq_of_comp_eq {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂}
    [Category.{v₂} 𝒟] (G : 𝒞 ⥤ 𝒟) {T I U : 𝒞} {h h' : T ⟶ I} {k : I ⟶ U}
    (hk : h ≫ k = h' ≫ k) {Z : 𝒟} (z : G.obj U ⟶ Z) :
    G.map h ≫ G.map k ≫ z = G.map h' ≫ G.map k ≫ z := by
  rw [← Category.assoc, ← G.map_comp, hk, G.map_comp, Category.assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A chosen 2-fibre product of two algebraic spaces over an algebraic stack**, as an algebraic
space `I` with morphisms `fst : I ⟶ U`, `snd : I ⟶ V` and the 2-isomorphism `iso` filling the
square, which is a 2-fibre product in the 2-category of algebraic stacks. -/
structure SpaceTwoFibreProduct {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V : AlgebraicSpaces B S hS}
    (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
    (y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒳) where
  /-- The algebraic space `U ×_{x, 𝒳, y} V`. -/
  pt : AlgebraicSpaces B S hS
  /-- The first projection. -/
  fst : pt ⟶ U
  /-- The second projection. -/
  snd : pt ⟶ V
  /-- The universal 2-isomorphism `x ∘ fst ≅ y ∘ snd`. -/
  iso : (algebraicSpaceStackFunctor.{u, w} B S hS).map fst ≫ x ≅
    (algebraicSpaceStackFunctor.{u, w} B S hS).map snd ≫ y
  /-- The square is a 2-fibre product. -/
  isTwoFibreProduct : Nonempty (Bicategory.IsTwoFibreProduct (⟨_, _, _, iso⟩ :
    Bicategory.TwoCommSq x y))

/-- The chosen 2-fibre product of two algebraic spaces over an algebraic stack, from
`AlgebraicGeometry.Stack.exists_isTwoFibreProduct_algebraicSpaceStackFunctor`. -/
def spaceTwoFibreProduct {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V : AlgebraicSpaces B S hS}
    (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
    (y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒳) : SpaceTwoFibreProduct x y :=
  let h := exists_isTwoFibreProduct_algebraicSpaceStackFunctor x y
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec⟩

/-- **Factoring through the second leg of a 2-fibre product with an algebraic-space apex.** Let
the stack of an algebraic space `U₀`, with legs `a : U₀ ⟶ 𝒳₁` and the stack of `j : U₀ ⟶ V`, be a
2-fibre product of `f : 𝒳₁ ⟶ 𝒴` and `g : V ⟶ 𝒴`. A morphism `t : T ⟶ V` of algebraic spaces with
`g ∘ t ≅ f ∘ b` for some `b : T ⟶ 𝒳₁` factors as `t = j ∘ u`. -/
theorem exists_comp_eq_of_isTwoFibreProduct_snd {𝒳₁ 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {V U₀ : AlgebraicSpaces B S hS} {f : 𝒳₁ ⟶ 𝒴}
    {g : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒴}
    {a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U₀ ⟶ 𝒳₁} {j : U₀ ⟶ V}
    {φ : a ≫ f ≅ (algebraicSpaceStackFunctor.{u, w} B S hS).map j ≫ g}
    (hP : Bicategory.IsTwoFibreProduct (⟨_, _, _, φ⟩ : Bicategory.TwoCommSq f g))
    {T : AlgebraicSpaces B S hS} (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒳₁)
    (t : T ⟶ V) (η : b ≫ f ≅ (algebraicSpaceStackFunctor.{u, w} B S hS).map t ≫ g) :
    ∃ v : T ⟶ U₀, v ≫ j = t := by
  obtain ⟨hom, isoFst, isoSnd, compat⟩ :=
    Bicategory.twoFibreProductPreHom hP ⟨_, _, _, η⟩
  obtain ⟨v, rfl⟩ : ∃ v : T ⟶ U₀, (algebraicSpaceStackFunctor.{u, w} B S hS).map v = hom :=
    ⟨_, algebraicSpaceStackFunctor_map_homMk_representingMap hom⟩
  exact ⟨v, algebraicSpaceStackFunctor_map_injective
    (((algebraicSpaceStackFunctor.{u, w} B S hS).map_comp v j).trans
      (eq_of_hom₂_algebraicSpaceStackFunctor_obj isoSnd.hom).symm)⟩

namespace EtaleSmoothLift

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

/-- **The self-intersection `I' = U' ×_{x', 𝒳', x'} U'`** of the smooth 1-morphism `x'` of a
smooth lift, an algebraic space with its two projections `p'`, `q'` and the universal
2-isomorphism `γ : x' ∘ p' ≅ x' ∘ q'`. -/
abbrev selfIntersection (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    SpaceTwoFibreProduct ξ.ambientMap ξ.ambientMap :=
  spaceTwoFibreProduct ξ.ambientMap ξ.ambientMap

/-- The 1-morphism `x'` of a smooth lift is `x' ∘ id_{U'}`, in the shape the lift of an
automorphism needs. -/
theorem map_id_comp_ambientMap (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.ambient) ≫ ξ.ambientMap = ξ.ambientMap :=
  (ambientMap_eq_map_id_comp ξ).symm

/-- **The section of `p'` attached to an endomorphism of a smooth lift over the identity.** For
`σ = (id, f', γ_σ) : ξ ⟶ ξ` it is the morphism `δ_σ : U' ⟶ I'` with `p' ∘ δ_σ = id`,
`q' ∘ δ_σ = f'` and `δ_σ^*γ = γ_σ`, given by the universal property of the 2-fibre product. -/
theorem exists_autLift (ξ : EtaleSmoothLift B S hS ι hι W x hx) (σ : Hom ξ ξ) :
    ∃ h : ξ.ambient ⟶ ξ.selfIntersection.pt, h ≫ ξ.selfIntersection.fst = 𝟙 _ ∧
      h ≫ ξ.selfIntersection.snd = σ.ambient ∧
      ∀ (e₁ : (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.ambient) ≫ ξ.ambientMap =
          (algebraicSpaceStackFunctor B S hS).map h ≫
            (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap)
        (e₂ : (algebraicSpaceStackFunctor B S hS).map h ≫
            (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap =
          (algebraicSpaceStackFunctor B S hS).map σ.ambient ≫ ξ.ambientMap),
        eqToHom (map_id_comp_ambientMap ξ) ≫ σ.comm =
          eqToHom e₁ ≫ ((algebraicSpaceStackFunctor B S hS).map h ◁ ξ.selfIntersection.iso.hom) ≫
            eqToHom e₂ :=
  exists_lift_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ξ.selfIntersection.isTwoFibreProduct.some (𝟙 _) σ.ambient
    (eqToIso (map_id_comp_ambientMap ξ) ≪≫ asIso σ.comm)

/-- **The section `δ_σ : U' ⟶ I'` of `p'` attached to an endomorphism `σ` of a smooth lift**,
`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_autLift`. -/
def autLift (ξ : EtaleSmoothLift B S hS ι hι W x hx) (σ : Hom ξ ξ) :
    ξ.ambient ⟶ ξ.selfIntersection.pt :=
  (exists_autLift ξ σ).choose

/-- The section `δ_σ` is a section of `p'`: `p' ∘ δ_σ = id`. -/
theorem autLift_fst (ξ : EtaleSmoothLift B S hS ι hι W x hx) (σ : Hom ξ ξ) :
    ξ.autLift σ ≫ ξ.selfIntersection.fst = 𝟙 _ :=
  (exists_autLift ξ σ).choose_spec.1

/-- The section `δ_σ` composed with `q'` is `f'`: `q' ∘ δ_σ = f'`. -/
theorem autLift_snd (ξ : EtaleSmoothLift B S hS ι hι W x hx) (σ : Hom ξ ξ) :
    ξ.autLift σ ≫ ξ.selfIntersection.snd = σ.ambient :=
  (exists_autLift ξ σ).choose_spec.2.1

/-- The pullback `δ_σ^*γ` of the universal 2-isomorphism along `δ_σ` is the 2-isomorphism
`γ_σ` of `σ`, along the equalities of its source and target. -/
theorem autLift_spec (ξ : EtaleSmoothLift B S hS ι hι W x hx) (σ : Hom ξ ξ)
    (e₀ : (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.ambient) ≫ ξ.ambientMap = ξ.ambientMap)
    (e₁ : (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.ambient) ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (ξ.autLift σ) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap)
    (e₂ : (algebraicSpaceStackFunctor B S hS).map (ξ.autLift σ) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map σ.ambient ≫ ξ.ambientMap) :
    eqToHom e₀ ≫ σ.comm =
      eqToHom e₁ ≫ ((algebraicSpaceStackFunctor B S hS).map (ξ.autLift σ) ◁
        ξ.selfIntersection.iso.hom) ≫ eqToHom e₂ :=
  (exists_autLift ξ σ).choose_spec.2.2 e₁ e₂

/-- The comparison `q'^*x' ∘ f' = x' ∘ (f' ∘ q')` used by the right translation. -/
theorem map_snd_comp_assoc (ξ : EtaleSmoothLift B S hS ι hι W x hx) (τ : Hom ξ ξ) :
    (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫
        (algebraicSpaceStackFunctor B S hS).map τ.ambient ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (ξ.selfIntersection.snd ≫ τ.ambient) ≫
        ξ.ambientMap :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ξ.ambientMap)
    ((algebraicSpaceStackFunctor B S hS).map_comp _ _).symm)

/-- **Right translation by an endomorphism of a smooth lift, on the self-intersection.** For
`τ = (id, f', γ_τ)` it is the morphism `R_τ : I' ⟶ I'` with `p' ∘ R_τ = p'`,
`q' ∘ R_τ = f' ∘ q'` and `R_τ^*γ = (q'^*γ_τ) ∘ γ`; on points it sends `(a, b, η)` to
`(a, f' ∘ b, b^*γ_τ ∘ η)`, and it is postcomposition with `τ` in the groupoid `I' ⇉ U'`. -/
theorem exists_rightTranslation (ξ : EtaleSmoothLift B S hS ι hι W x hx) (τ : Hom ξ ξ) :
    ∃ h : ξ.selfIntersection.pt ⟶ ξ.selfIntersection.pt,
      h ≫ ξ.selfIntersection.fst = ξ.selfIntersection.fst ∧
      h ≫ ξ.selfIntersection.snd = ξ.selfIntersection.snd ≫ τ.ambient ∧
      ∀ (e₁ : (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap =
          (algebraicSpaceStackFunctor B S hS).map h ≫
            (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap)
        (e₂ : (algebraicSpaceStackFunctor B S hS).map h ≫
            (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap =
          (algebraicSpaceStackFunctor B S hS).map (ξ.selfIntersection.snd ≫ τ.ambient) ≫
            ξ.ambientMap),
        ξ.selfIntersection.iso.hom ≫
            ((algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ◁ τ.comm) ≫
              eqToHom (map_snd_comp_assoc ξ τ) =
          eqToHom e₁ ≫ ((algebraicSpaceStackFunctor B S hS).map h ◁ ξ.selfIntersection.iso.hom) ≫
            eqToHom e₂ :=
  exists_lift_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ξ.selfIntersection.isTwoFibreProduct.some ξ.selfIntersection.fst
    (ξ.selfIntersection.snd ≫ τ.ambient)
    (ξ.selfIntersection.iso ≪≫ whiskerLeftIso _ (asIso τ.comm) ≪≫
      eqToIso (map_snd_comp_assoc ξ τ))

/-- **Right translation `R_τ : I' ⟶ I'`**,
`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_rightTranslation`. -/
def rightTranslation (ξ : EtaleSmoothLift B S hS ι hι W x hx) (τ : Hom ξ ξ) :
    ξ.selfIntersection.pt ⟶ ξ.selfIntersection.pt :=
  (exists_rightTranslation ξ τ).choose

/-- Right translation commutes with `p'`: `p' ∘ R_τ = p'`. -/
theorem rightTranslation_fst (ξ : EtaleSmoothLift B S hS ι hι W x hx) (τ : Hom ξ ξ) :
    ξ.rightTranslation τ ≫ ξ.selfIntersection.fst = ξ.selfIntersection.fst :=
  (exists_rightTranslation ξ τ).choose_spec.1

/-- Right translation composed with `q'` is `f' ∘ q'`. -/
theorem rightTranslation_snd (ξ : EtaleSmoothLift B S hS ι hι W x hx) (τ : Hom ξ ξ) :
    ξ.rightTranslation τ ≫ ξ.selfIntersection.snd = ξ.selfIntersection.snd ≫ τ.ambient :=
  (exists_rightTranslation ξ τ).choose_spec.2.1

/-- The pullback `R_τ^*γ` of the universal 2-isomorphism along `R_τ` is `(q'^*γ_τ) ∘ γ`,
along the equalities of its source and target. -/
theorem rightTranslation_spec (ξ : EtaleSmoothLift B S hS ι hι W x hx) (τ : Hom ξ ξ)
    (e₀ : (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫
        (algebraicSpaceStackFunctor B S hS).map τ.ambient ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (ξ.selfIntersection.snd ≫ τ.ambient) ≫
        ξ.ambientMap)
    (e₁ : (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (ξ.rightTranslation τ) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap)
    (e₂ : (algebraicSpaceStackFunctor B S hS).map (ξ.rightTranslation τ) ≫
        (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (ξ.selfIntersection.snd ≫ τ.ambient) ≫
        ξ.ambientMap) :
    ξ.selfIntersection.iso.hom ≫
        ((algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ◁ τ.comm) ≫ eqToHom e₀ =
      eqToHom e₁ ≫ ((algebraicSpaceStackFunctor B S hS).map (ξ.rightTranslation τ) ◁
        ξ.selfIntersection.iso.hom) ≫ eqToHom e₂ :=
  (exists_rightTranslation ξ τ).choose_spec.2.2 e₁ e₂

/-- **The lift of a composite is the lift of the first factor followed by right translation by
the second**: `δ_{σ ≫ τ} = R_τ ∘ δ_σ`. -/
theorem autLift_comp (ξ : EtaleSmoothLift B S hS ι hι W x hx) (σ τ : Hom ξ ξ) :
    ξ.autLift (σ.comp τ) = ξ.autLift σ ≫ ξ.rightTranslation τ := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have hp : ξ.autLift (σ.comp τ) ≫ ξ.selfIntersection.fst =
      (ξ.autLift σ ≫ ξ.rightTranslation τ) ≫ ξ.selfIntersection.fst := by
    rw [autLift_fst, Category.assoc, rightTranslation_fst, autLift_fst]
  have hq : ξ.autLift (σ.comp τ) ≫ ξ.selfIntersection.snd =
      (ξ.autLift σ ≫ ξ.rightTranslation τ) ≫ ξ.selfIntersection.snd := by
    rw [autLift_snd, Category.assoc, rightTranslation_snd, ← Category.assoc, autLift_snd]
    rfl
  refine hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ξ.selfIntersection.isTwoFibreProduct.some hp hq
    (F.map_comp_map_comp_eq_of_comp_eq hp ξ.ambientMap)
    (F.map_comp_map_comp_eq_of_comp_eq hq ξ.ambientMap).symm ?_
  have he : ∀ (e₀ : F.map (𝟙 ξ.ambient) ≫ ξ.ambientMap = ξ.ambientMap)
      (e₁ : F.map (𝟙 ξ.ambient) ≫ ξ.ambientMap =
        F.map (ξ.autLift (σ.comp τ)) ≫ F.map ξ.selfIntersection.fst ≫ ξ.ambientMap)
      (e₂ : F.map (ξ.autLift (σ.comp τ)) ≫ F.map ξ.selfIntersection.snd ≫ ξ.ambientMap =
        F.map (σ.comp τ).ambient ≫ ξ.ambientMap)
      (e₃ : F.map σ.ambient ≫ F.map τ.ambient ≫ ξ.ambientMap =
        F.map (σ.comp τ).ambient ≫ ξ.ambientMap),
      eqToHom e₀ ≫ σ.comm ≫ (F.map σ.ambient ◁ τ.comm) ≫ eqToHom e₃ =
        eqToHom e₁ ≫ (F.map (ξ.autLift (σ.comp τ)) ◁ ξ.selfIntersection.iso.hom) ≫
          eqToHom e₂ := by
    intro e₀ e₁ e₂ e₃
    refine Eq.trans ?_ (autLift_spec ξ (σ.comp τ) e₀ e₁ e₂)
    have h₃ : eqToHom e₃ = 𝟙 _ := eqToHom_refl _ _
    exact (congrArg (fun t => eqToHom e₀ ≫ σ.comm ≫ (F.map σ.ambient ◁ τ.comm) ≫ t) h₃).trans
      (congrArg (fun t => eqToHom e₀ ≫ σ.comm ≫ t) (Category.comp_id _))
  exact whiskerLeft_eq_of_translation ξ.selfIntersection.iso.hom
    (one := F.map (𝟙 ξ.ambient)) (s := F.map σ.ambient) (t := F.map τ.ambient)
    (st := F.map (σ.comp τ).ambient) (m := F.map (ξ.selfIntersection.snd ≫ τ.ambient))
    (d := F.map (ξ.autLift σ)) (e := F.map (ξ.autLift (σ.comp τ)))
    (dr := F.map (ξ.autLift σ ≫ ξ.rightTranslation τ)) (r := F.map (ξ.rightTranslation τ))
    (F.map_id _) (F.map_comp _ _) (F.map_comp _ _) (F.map_comp _ _)
    ((F.map_comp _ _).symm.trans (congrArg F.map (autLift_fst ξ σ)))
    ((F.map_comp _ _).symm.trans (congrArg F.map (autLift_snd ξ σ)))
    ((F.map_comp _ _).symm.trans (congrArg F.map (rightTranslation_fst ξ τ)))
    ((F.map_comp _ _).symm.trans (congrArg F.map (rightTranslation_snd ξ τ)))
    ((F.map_comp _ _).symm.trans (congrArg F.map (autLift_fst ξ (σ.comp τ))))
    ((F.map_comp _ _).symm.trans (congrArg F.map (autLift_snd ξ (σ.comp τ))))
    σ.comm τ.comm (autLift_spec ξ σ) (rightTranslation_spec ξ τ) he _ _

/-- **The defining property of the section `δ_σ`** of `p'` attached to an endomorphism `σ`:
`p' ∘ d = id`, `q' ∘ d = f'` and `d^*γ = γ_σ` along these equalities. -/
def IsAutLift (ξ : EtaleSmoothLift B S hS ι hι W x hx) (σ : Hom ξ ξ)
    (d : ξ.ambient ⟶ ξ.selfIntersection.pt) : Prop :=
  d ≫ ξ.selfIntersection.fst = 𝟙 _ ∧ d ≫ ξ.selfIntersection.snd = σ.ambient ∧
    ∀ (e₀ : (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.ambient) ≫ ξ.ambientMap = ξ.ambientMap)
      (e₁ : (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.ambient) ≫ ξ.ambientMap =
        (algebraicSpaceStackFunctor B S hS).map d ≫
          (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.fst ≫ ξ.ambientMap)
      (e₂ : (algebraicSpaceStackFunctor B S hS).map d ≫
          (algebraicSpaceStackFunctor B S hS).map ξ.selfIntersection.snd ≫ ξ.ambientMap =
        (algebraicSpaceStackFunctor B S hS).map σ.ambient ≫ ξ.ambientMap),
      eqToHom e₀ ≫ σ.comm =
        eqToHom e₁ ≫ ((algebraicSpaceStackFunctor B S hS).map d ◁ ξ.selfIntersection.iso.hom) ≫
          eqToHom e₂

/-- The section `δ_σ` has the defining property of a section of `p'` attached to `σ`. -/
theorem isAutLift_autLift (ξ : EtaleSmoothLift B S hS ι hι W x hx) (σ : Hom ξ ξ) :
    ξ.IsAutLift σ (ξ.autLift σ) :=
  ⟨autLift_fst ξ σ, autLift_snd ξ σ, autLift_spec ξ σ⟩

/-- **An endomorphism of a smooth lift is determined by its base and its section of `p'`.** -/
theorem eq_of_isAutLift (ξ : EtaleSmoothLift B S hS ι hι W x hx) {σ τ : Hom ξ ξ}
    {d : ξ.ambient ⟶ ξ.selfIntersection.pt} (hσ : ξ.IsAutLift σ d) (hτ : ξ.IsAutLift τ d)
    (hb : σ.base = τ.base) : σ = τ := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  obtain ⟨b₁, a₁, r₁, c₁, k₁⟩ := σ
  obtain ⟨b₂, a₂, r₂, c₂, k₂⟩ := τ
  have ha : a₁ = a₂ := hσ.2.1.symm.trans hτ.2.1
  dsimp only at hb ha
  subst hb ha
  have e₁ : F.map (𝟙 ξ.ambient) ≫ ξ.ambientMap = F.map d ≫ F.map ξ.selfIntersection.fst ≫
      ξ.ambientMap :=
    (congrArg (· ≫ ξ.ambientMap) ((congrArg F.map hσ.1).symm.trans (F.map_comp _ _))).trans
      (Category.assoc _ _ _)
  have e₂ : F.map d ≫ F.map ξ.selfIntersection.snd ≫ ξ.ambientMap = F.map a₁ ≫ ξ.ambientMap :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ ξ.ambientMap) ((F.map_comp _ _).symm.trans (congrArg F.map hσ.2.1)))
  have hc : c₁ = c₂ := (cancel_epi (eqToHom (map_id_comp_ambientMap ξ))).1
    ((hσ.2.2 _ e₁ e₂).trans (hτ.2.2 _ e₁ e₂).symm)
  subst hc
  rfl

/-- **The section `δ_σ` determines `σ`** among the endomorphisms with the same base. -/
theorem autLift_injective (ξ : EtaleSmoothLift B S hS ι hι W x hx) {σ τ : Hom ξ ξ}
    (h : ξ.autLift σ = ξ.autLift τ) (hb : σ.base = τ.base) : σ = τ :=
  ξ.eq_of_isAutLift (ξ.isAutLift_autLift σ) (h ▸ ξ.isAutLift_autLift τ) hb

/-- An endomorphism over the identity restricts to the identity on `U`: `f' ∘ i = i`. -/
theorem inclusion_comp_ambient_of_base_eq_id (ξ : EtaleSmoothLift B S hS ι hι W x hx)
    (τ : Hom ξ ξ) (hτ : τ.base = 𝟙 ξ.base) : ξ.inclusion ≫ τ.ambient = ξ.inclusion := by
  have h := τ.inclusion_comp
  rw [hτ] at h
  exact h.trans (Category.id_comp _)

/-- **Right translation by an endomorphism over the identity fixes the points of `I'` lying over
`U`.** For `τ` over the identity and `z : T ⟶ I'` whose first projection factors through
`i : U ⟶ U'`, `R_τ ∘ z = z`: the second projection of `z` then factors through `i` as well,
because `U = 𝒳 ×_{𝒳'} U'`, and `τ` is the identity over `U`. -/
theorem comp_rightTranslation_of_fst (ξ : EtaleSmoothLift B S hS ι hι W x hx) (τ : Hom ξ ξ)
    (hτ : τ.base = 𝟙 ξ.base) {T : AlgebraicSpaces B S hS} (z : T ⟶ ξ.selfIntersection.pt)
    {u : T ⟶ ξ.base.obj.left} (hz : z ≫ ξ.selfIntersection.fst = u ≫ ξ.inclusion) :
    z ≫ ξ.rightTranslation τ = z := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  have e : F.map u ≫ F.map ξ.inclusion ≫ ξ.ambientMap =
      F.map z ≫ F.map ξ.selfIntersection.fst ≫ ξ.ambientMap :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.ambientMap)
      ((F.map_comp u ξ.inclusion).symm.trans ((congrArg F.map hz.symm).trans
        (F.map_comp z ξ.selfIntersection.fst)))).trans (Category.assoc _ _ _))
  have e' : F.map z ≫ F.map ξ.selfIntersection.snd ≫ ξ.ambientMap =
      F.map (z ≫ ξ.selfIntersection.snd) ≫ ξ.ambientMap :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ ξ.ambientMap) (F.map_comp z ξ.selfIntersection.snd).symm)
  obtain ⟨v, hv⟩ := exists_comp_eq_of_isTwoFibreProduct_snd ξ.isTwoFibreProduct
    (F.map u ≫ F.map ξ.base.obj.hom ≫ x) (z ≫ ξ.selfIntersection.snd)
    (eqToIso (Category.assoc _ _ _) ≪≫ whiskerLeftIso (F.map u) ξ.comm ≪≫ eqToIso e ≪≫
      whiskerLeftIso (F.map z) ξ.selfIntersection.iso ≪≫ eqToIso e')
  have hit := inclusion_comp_ambient_of_base_eq_id ξ τ hτ
  have hp : (z ≫ ξ.rightTranslation τ) ≫ ξ.selfIntersection.fst = z ≫ ξ.selfIntersection.fst := by
    rw [Category.assoc, rightTranslation_fst]
  have hq : (z ≫ ξ.rightTranslation τ) ≫ ξ.selfIntersection.snd = z ≫ ξ.selfIntersection.snd := by
    rw [Category.assoc, rightTranslation_snd, ← Category.assoc, ← hv, Category.assoc, hit]
  refine hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    ξ.selfIntersection.isTwoFibreProduct.some hp hq
    (F.map_comp_map_comp_eq_of_comp_eq hp ξ.ambientMap)
    (F.map_comp_map_comp_eq_of_comp_eq hq ξ.ambientMap).symm ?_
  have hone : F.map τ.base.hom.left = 𝟙 _ :=
    (congrArg (fun b : ξ.base ⟶ ξ.base => F.map b.hom.left) hτ).trans (F.map_id _)
  have hj := whiskerLeft_eq_eqToHom_of_coherence hone ξ.comm.hom τ.comm
    (left_leg ξ ξ τ.base) (right_leg ξ ξ τ.base τ.ambient τ.inclusion_comp) τ.coherence
  exact whiskerLeft_comp_eq_of_translation_trivial ξ.selfIntersection.iso.hom
    (t := F.map τ.ambient) (m := F.map (ξ.selfIntersection.snd ≫ τ.ambient))
    (r := F.map (ξ.rightTranslation τ)) (z := F.map z) (zr := F.map (z ≫ ξ.rightTranslation τ))
    (v := F.map v) (j := F.map ξ.inclusion) (F.map_comp _ _) (F.map_comp _ _)
    ((F.map_comp _ _).symm.trans (congrArg F.map (rightTranslation_fst ξ τ)))
    ((F.map_comp _ _).symm.trans (congrArg F.map (rightTranslation_snd ξ τ)))
    ((F.map_comp _ _).symm.trans ((congrArg F.map hv.symm).trans (F.map_comp _ _)))
    ((F.map_comp _ _).symm.trans (congrArg F.map hit)) τ.comm (rightTranslation_spec ξ τ) hj
    _ _

end EtaleSmoothLift

end AlgebraicGeometry.Stack

end
