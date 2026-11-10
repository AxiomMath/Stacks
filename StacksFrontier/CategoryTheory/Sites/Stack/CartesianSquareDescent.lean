module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Descent across a cartesian square with a monomorphic centre

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a stack for a Grothendieck topology `J` and let

```
  E --d--> X'
  |e       |b
  v        v
  Z --z--> X
```

be a cartesian square of `C` in which `z` is a monomorphism and `{z, b}` covers `X`.  Write
`P = X' ×_X X'` with projections `p₁, p₂`, `δ : X' ⟶ P` for the diagonal and
`r : T = Z ×_X P ⟶ P` for the base change of `z`, and assume that `{r, δ}` covers `P`.  Then the
canonical functor `F(X) ⥤ F(Z) ×_{F(E)} F(X')` onto the two-fibre product is an equivalence of
categories:
`CategoryTheory.Pseudofunctor.CartesianSquareDescent.isEquivalence_comp_restriction`.

This is the categorified form of the gluing statement for an almost blowup square (Stacks 0EVD):
the descent data relative to `{z, b}` carry, besides the two objects and their identification over
`E`, an identification over `P` and a cocycle condition over triple overlaps, and both are forced.
The functor is factored as the descent data functor relative to `{z, b}`, an equivalence because
`F` is a stack, followed by the functor
`CategoryTheory.Pseudofunctor.CartesianSquareDescent.restriction` which keeps the two objects and
the gluing morphism over `E`.  The restriction functor is

* faithful, because a morphism of descent data is its two components;
* full (`full_restriction`): the compatibility of a pair of components with the gluing morphisms
  is checked pair by pair — over `(Z, Z)` it is diagonal because `z` is a monomorphism, over a
  mixed pair it is a base change of the compatibility over `E`, and over `(X', X')` it is checked
  locally on the base change of `{r, δ}`, where it reduces to the previous cases;
* essentially surjective (`essSurj_restriction`): an object `(x₁, x₂, φ)` of the two-fibre product
  defines a descent datum whose identification over `P` is glued along `{r, δ}` from the composite
  through `φ` over `r` and the identity over `δ` (`exists_glue`), and whose cocycle condition is
  checked through `Z` when one of the three morphisms factors through `Z`, and locally on the base
  change of `{r, δ}` otherwise.

Every gluing morphism is written as a base change `pullHom` (Mathlib's
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`) of one of four universal ones, so
that compatibility with base change is `pullHom_pullHom`.

## Main definitions

* `CategoryTheory.Pseudofunctor.CartesianSquareDescent.restriction`: the functor from the descent
  data relative to `{z, b}` to the two-fibre product.
* `CategoryTheory.Pseudofunctor.CartesianSquareDescent.descentData`: the descent datum attached to
  an object of the two-fibre product and to a glued identification over `P`.

## Main results

* `CategoryTheory.Pseudofunctor.exists_pullHom_eq_of_fullyFaithful` and
  `CategoryTheory.Pseudofunctor.eq_of_pullHom_eq_of_isPrestackFor`: descent of morphisms between
  pullbacks, read through base change.
* `CategoryTheory.Pseudofunctor.CartesianSquareDescent.isEquivalence_restriction`: the restriction
  functor is an equivalence.
* `CategoryTheory.Pseudofunctor.CartesianSquareDescent.isEquivalence_comp_restriction`:
  the comparison functor onto the two-fibre product is an equivalence.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 0EVD](https://stacks.math.columbia.edu/tag/0EVD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v' u' v u

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

/-- Base change of a composite is the composite of the base changes. -/
public lemma pullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (φ' : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom φ' g gf₂ gf₃ hgf₂ hgf₃ =
      pullHom (φ ≫ φ') g gf₁ gf₃ hgf₁ hgf₃ := by
  simp [pullHom]

/-- The base change of a morphism does not depend on the proof of the factorization. -/
public lemma pullHom_congr ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    {g g' : Y' ⟶ Y} (h : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) (hgf₁' : g' ≫ f₁ = gf₁) (hgf₂' : g' ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ g' gf₁ gf₂ hgf₁' hgf₂' := by
  subst h
  rfl

/-- The base change of an identity is an identity. -/
@[simp]
public lemma pullHom_id_self ⦃X₁ : C⦄ (M₁ : F.obj (.mk (op X₁))) ⦃Y : C⦄ (f₁ : Y ⟶ X₁) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) (hgf₁' : g ≫ f₁ = gf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ hgf₁ hgf₁' = 𝟙 _ := by
  simp [pullHom, ← Cat.Hom₂.comp_app]

/-- Base change is natural in the two objects. -/
public lemma pullHom_naturality ⦃X₁ X₂ : C⦄ ⦃M₁ M₁' : F.obj (.mk (op X₁))⦄
    ⦃M₂ M₂' : F.obj (.mk (op X₂))⦄ (u : M₁ ⟶ M₁') (v : M₂ ⟶ M₂')
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁' ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂')
    (w : (F.map f₁.op.toLoc).toFunctor.map u ≫ φ' = φ ≫ (F.map f₂.op.toLoc).toFunctor.map v)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map gf₁.op.toLoc).toFunctor.map u ≫ pullHom φ' g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ (F.map gf₂.op.toLoc).toFunctor.map v := by
  simp only [pullHom, Category.assoc, mapComp'_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc, w, Functor.map_comp_assoc, mapComp'_inv_naturality]

/-- Base change of the image of a morphism under a pullback functor. -/
public lemma pullHom_map ⦃X₁ : C⦄ ⦃M₁ M₁' : F.obj (.mk (op X₁))⦄ (u : M₁ ⟶ M₁') ⦃Y : C⦄
    (f₁ : Y ⟶ X₁) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₁' : g ≫ f₁ = gf₁) :
    pullHom ((F.map f₁.op.toLoc).toFunctor.map u) g gf₁ gf₁ hgf₁ hgf₁' =
      (F.map gf₁.op.toLoc).toFunctor.map u := by
  simp only [pullHom]
  exact mapComp'_naturality_2 F _ _ _ _ u

/-- The canonical morphism `f^* M ⟶ f'^* M` attached to an equality `f = f'`, written as a base
change so that the lemmas about `pullHom` apply to it. -/
public def eqHom ⦃X₁ : C⦄ (M₁ : F.obj (.mk (op X₁))) ⦃Y : C⦄ {f f' : Y ⟶ X₁} (h : f = f') :
    (F.map f.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f'.op.toLoc).toFunctor.obj M₁ :=
  pullHom (𝟙 ((F.map (𝟙 X₁).op.toLoc).toFunctor.obj M₁)) f f f' (Category.comp_id f)
    (by rw [Category.comp_id, h])

/-- The canonical morphism of an equality may be computed as a base change along any morphism. -/
public lemma eqHom_eq_pullHom ⦃X₁ : C⦄ (M₁ : F.obj (.mk (op X₁))) ⦃Y : C⦄ {f f' : Y ⟶ X₁}
    (h : f = f') ⦃Y₀ : C⦄ (f₀ : Y₀ ⟶ X₁) (g : Y ⟶ Y₀) (hg : g ≫ f₀ = f) (hg' : g ≫ f₀ = f') :
    eqHom M₁ h = pullHom (𝟙 ((F.map f₀.op.toLoc).toFunctor.obj M₁)) g f f' hg hg' := by
  rw [eqHom, ← pullHom_id_self M₁ (𝟙 X₁) f₀ f₀ (Category.comp_id _) (Category.comp_id _),
    pullHom_pullHom]
  exact pullHom_congr _ hg.symm _ _ _ _ _ _

/-- The canonical morphism of a reflexivity is the identity. -/
@[simp]
public lemma eqHom_rfl ⦃X₁ : C⦄ (M₁ : F.obj (.mk (op X₁))) ⦃Y : C⦄ (f : Y ⟶ X₁) :
    eqHom M₁ (rfl : f = f) = 𝟙 _ :=
  pullHom_id_self _ _ _ _ _ _

/-- The canonical morphisms of equalities compose. -/
@[reassoc (attr := simp)]
public lemma eqHom_trans ⦃X₁ : C⦄ (M₁ : F.obj (.mk (op X₁))) ⦃Y : C⦄ {f f' f'' : Y ⟶ X₁}
    (h : f = f') (h' : f' = f'') :
    eqHom M₁ h ≫ eqHom M₁ h' = eqHom M₁ (h.trans h') := by
  subst h h'
  simp

/-- Base change of a canonical morphism of an equality. -/
@[simp]
public lemma pullHom_eqHom ⦃X₁ : C⦄ (M₁ : F.obj (.mk (op X₁))) ⦃Y : C⦄ {f f' : Y ⟶ X₁}
    (h : f = f') ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf : Y' ⟶ X₁) (gf' : Y' ⟶ X₁) (hgf : g ≫ f = gf)
    (hgf' : g ≫ f' = gf') :
    pullHom (eqHom M₁ h) g gf gf' hgf hgf' = eqHom M₁ (hgf.symm.trans (h ▸ hgf')) := by
  subst h hgf hgf'
  simp

/-- Conjugating a morphism between pullbacks along composites by the compositors. -/
public def conj ⦃X₁ X₂ : C⦄ (M₁ : F.obj (.mk (op X₁))) (M₂ : F.obj (.mk (op X₂))) ⦃Y : C⦄
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) ⦃V : C⦄ (u : V ⟶ Y) (uf₁ : V ⟶ X₁) (uf₂ : V ⟶ X₂)
    (h₁ : u ≫ f₁ = uf₁) (h₂ : u ≫ f₂ = uf₂)
    (s : (F.map uf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map uf₂.op.toLoc).toFunctor.obj M₂) :
    (F.map u.op.toLoc).toFunctor.obj ((F.map f₁.op.toLoc).toFunctor.obj M₁) ⟶
      (F.map u.op.toLoc).toFunctor.obj ((F.map f₂.op.toLoc).toFunctor.obj M₂) :=
  (F.mapComp' f₁.op.toLoc u.op.toLoc uf₁.op.toLoc (by rw [← h₁]; rfl)).inv.toNatTrans.app M₁ ≫
    s ≫ (F.mapComp' f₂.op.toLoc u.op.toLoc uf₂.op.toLoc (by rw [← h₂]; rfl)).hom.toNatTrans.app M₂

/-- Base change commutes with conjugation by the compositors. -/
public lemma pullHom_conj ⦃X₁ X₂ : C⦄ (M₁ : F.obj (.mk (op X₁))) (M₂ : F.obj (.mk (op X₂)))
    ⦃Y : C⦄ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) ⦃V : C⦄ (u : V ⟶ Y) (uf₁ : V ⟶ X₁) (uf₂ : V ⟶ X₂)
    (h₁ : u ≫ f₁ = uf₁) (h₂ : u ≫ f₂ = uf₂)
    (s : (F.map uf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map uf₂.op.toLoc).toFunctor.obj M₂)
    ⦃W : C⦄ (g : W ⟶ V) (gu : W ⟶ Y) (guf₁ : W ⟶ X₁) (guf₂ : W ⟶ X₂) (hgu : g ≫ u = gu)
    (hg₁ : g ≫ uf₁ = guf₁) (hg₂ : g ≫ uf₂ = guf₂) :
    pullHom (conj M₁ M₂ f₁ f₂ u uf₁ uf₂ h₁ h₂ s) g gu gu hgu hgu =
      conj M₁ M₂ f₁ f₂ gu guf₁ guf₂ (by rw [← hgu, Category.assoc, h₁, hg₁])
        (by rw [← hgu, Category.assoc, h₂, hg₂]) (pullHom s g guf₁ guf₂ hg₁ hg₂) := by
  subst hgu hg₁ hg₂ h₁ h₂
  simp only [conj, pullHom, Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc f₁.op.toLoc u.op.toLoc g.op.toLoc
      (u ≫ f₁).op.toLoc (g ≫ u).op.toLoc (g ≫ u ≫ f₁).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]),
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app f₂.op.toLoc u.op.toLoc g.op.toLoc
      (u ≫ f₂).op.toLoc (g ≫ u).op.toLoc (g ≫ u ≫ f₂).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])]

/-- A morphism whose pullback is the conjugate of `s` has base change `s`. -/
public lemma pullHom_eq_of_map_eq_conj ⦃X₁ X₂ : C⦄ (M₁ : F.obj (.mk (op X₁)))
    (M₂ : F.obj (.mk (op X₂))) ⦃Y : C⦄ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) ⦃V : C⦄ (u : V ⟶ Y)
    (uf₁ : V ⟶ X₁) (uf₂ : V ⟶ X₂) (h₁ : u ≫ f₁ = uf₁) (h₂ : u ≫ f₂ = uf₂)
    (s : (F.map uf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map uf₂.op.toLoc).toFunctor.obj M₂)
    (s₀ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (h : (F.map u.op.toLoc).toFunctor.map s₀ = conj M₁ M₂ f₁ f₂ u uf₁ uf₂ h₁ h₂ s) :
    pullHom s₀ u uf₁ uf₂ h₁ h₂ = s := by
  subst h₁ h₂
  rw [pullHom, h, conj]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

end LocallyDiscreteOpToCat

open LocallyDiscreteOpToCat

/-! ### Descent of morphisms, read through base change -/

section Glue

variable {ι : Type t} {Y : C} {V : ι → C} (γ : ∀ i, V i ⟶ Y)

/-- A morphism between the canonical descent data of two objects, from components whose base
changes agree. -/
public def toDescentDataHomOfPullHom {M N : F.obj (.mk (op Y))}
    (ξ : ∀ i, (F.map (γ i).op.toLoc).toFunctor.obj M ⟶ (F.map (γ i).op.toLoc).toFunctor.obj N)
    (h : ∀ ⦃W : C⦄ (q : W ⟶ Y) ⦃i j : ι⦄ (g₁ : W ⟶ V i) (g₂ : W ⟶ V j) (h₁ : g₁ ≫ γ i = q)
      (h₂ : g₂ ≫ γ j = q), pullHom (ξ i) g₁ q q h₁ h₁ = pullHom (ξ j) g₂ q q h₂ h₂) :
    (F.toDescentData γ).obj M ⟶ (F.toDescentData γ).obj N where
  hom := ξ
  comm W q i j g₁ g₂ h₁ h₂ := by
    change (F.map g₁.op.toLoc).toFunctor.map (ξ i) ≫
        ((F.mapComp' (γ i).op.toLoc g₁.op.toLoc q.op.toLoc
            (by rw [← h₁]; rfl)).inv.toNatTrans.app N ≫
          (F.mapComp' (γ j).op.toLoc g₂.op.toLoc q.op.toLoc
            (by rw [← h₂]; rfl)).hom.toNatTrans.app N) =
      ((F.mapComp' (γ i).op.toLoc g₁.op.toLoc q.op.toLoc
            (by rw [← h₁]; rfl)).inv.toNatTrans.app M ≫
          (F.mapComp' (γ j).op.toLoc g₂.op.toLoc q.op.toLoc
            (by rw [← h₂]; rfl)).hom.toNatTrans.app M) ≫
        (F.map g₂.op.toLoc).toFunctor.map (ξ j)
    rw [map_eq_pullHom (ξ i) g₁ q q h₁ h₁, map_eq_pullHom (ξ j) g₂ q q h₂ h₂, h q g₁ g₂ h₁ h₂]
    simp

/-- **Gluing a morphism between pullbacks along a family with fully faithful descent.** -/
public lemma exists_pullHom_eq_of_fullyFaithful (hff : (F.toDescentData γ).FullyFaithful)
    ⦃X₁ X₂ : C⦄ (M₁ : F.obj (.mk (op X₁))) (M₂ : F.obj (.mk (op X₂))) (f₁ : Y ⟶ X₁)
    (f₂ : Y ⟶ X₂)
    (s : ∀ i, (F.map (γ i ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (γ i ≫ f₂).op.toLoc).toFunctor.obj M₂)
    (hs : ∀ ⦃W : C⦄ (q : W ⟶ Y) ⦃i j : ι⦄ (g₁ : W ⟶ V i) (g₂ : W ⟶ V j) (h₁ : g₁ ≫ γ i = q)
      (h₂ : g₂ ≫ γ j = q),
      pullHom (s i) g₁ (q ≫ f₁) (q ≫ f₂) (by rw [← h₁, Category.assoc])
          (by rw [← h₁, Category.assoc]) =
        pullHom (s j) g₂ (q ≫ f₁) (q ≫ f₂) (by rw [← h₂, Category.assoc])
          (by rw [← h₂, Category.assoc])) :
    ∃ s₀ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂,
      ∀ i, pullHom s₀ (γ i) (γ i ≫ f₁) (γ i ≫ f₂) rfl rfl = s i := by
  let ξ : ∀ i, _ := fun i ↦ conj M₁ M₂ f₁ f₂ (γ i) _ _ rfl rfl (s i)
  have hξ : ∀ ⦃W : C⦄ (q : W ⟶ Y) ⦃i j : ι⦄ (g₁ : W ⟶ V i) (g₂ : W ⟶ V j)
      (h₁ : g₁ ≫ γ i = q) (h₂ : g₂ ≫ γ j = q),
      pullHom (ξ i) g₁ q q h₁ h₁ = pullHom (ξ j) g₂ q q h₂ h₂ := by
    intro W q i j g₁ g₂ h₁ h₂
    simp only [ξ]
    rw [pullHom_conj M₁ M₂ f₁ f₂ (γ i) _ _ rfl rfl (s i) g₁ q (q ≫ f₁) (q ≫ f₂) h₁
        (by rw [← h₁, Category.assoc]) (by rw [← h₁, Category.assoc]),
      pullHom_conj M₁ M₂ f₁ f₂ (γ j) _ _ rfl rfl (s j) g₂ q (q ≫ f₁) (q ≫ f₂) h₂
        (by rw [← h₂, Category.assoc]) (by rw [← h₂, Category.assoc]), hs q g₁ g₂ h₁ h₂]
  refine ⟨hff.preimage (toDescentDataHomOfPullHom γ ξ hξ), fun i ↦ ?_⟩
  have hi : (F.map (γ i).op.toLoc).toFunctor.map (hff.preimage (toDescentDataHomOfPullHom γ ξ hξ))
      = ξ i :=
    congrArg (fun η ↦ Pseudofunctor.DescentData.Hom.hom η i) (hff.map_preimage _)
  exact pullHom_eq_of_map_eq_conj _ _ _ _ _ _ _ _ _ _ _ hi

/-- **Separatedness, read through base change.** Two morphisms between pullbacks with the same
base changes along a family with faithful descent are equal. -/
public lemma eq_of_pullHom_eq_of_faithful [(F.toDescentData γ).Faithful]
    ⦃X₁ X₂ : C⦄ {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {f₁ : Y ⟶ X₁}
    {f₂ : Y ⟶ X₂}
    (s s' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (h : ∀ i, pullHom s (γ i) (γ i ≫ f₁) (γ i ≫ f₂) rfl rfl =
      pullHom s' (γ i) (γ i ≫ f₁) (γ i ≫ f₂) rfl rfl) :
    s = s' := by
  refine (F.toDescentData γ).map_injective (Pseudofunctor.DescentData.hom_ext fun i ↦ ?_)
  change (F.map (γ i).op.toLoc).toFunctor.map s = (F.map (γ i).op.toLoc).toFunctor.map s'
  rw [map_eq_pullHom s (γ i) (γ i ≫ f₁) (γ i ≫ f₂) rfl rfl,
    map_eq_pullHom s' (γ i) (γ i ≫ f₁) (γ i ≫ f₂) rfl rfl, h i]

/-- Separatedness along a sieve for which the pseudofunctor is a prestack. -/
public lemma eq_of_pullHom_eq_of_isPrestackFor {R : Sieve Y} (hR : F.IsPrestackFor R.arrows)
    ⦃X₁ X₂ : C⦄ {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {f₁ : Y ⟶ X₁}
    {f₂ : Y ⟶ X₂}
    (s s' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (h : ∀ ⦃W : C⦄ (g : W ⟶ Y), R g → pullHom s g (g ≫ f₁) (g ≫ f₂) rfl rfl =
      pullHom s' g (g ≫ f₁) (g ≫ f₂) rfl rfl) :
    s = s' := by
  have := hR.fullyFaithful.faithful
  exact eq_of_pullHom_eq_of_faithful (fun (g : R.arrows.category) ↦ g.obj.hom) s s'
    (fun g ↦ h g.obj.hom g.property)

end Glue

/-! ### Morphisms of descent data, one pair at a time -/

section Comm

variable {ι : Type t} {S : C} {Xi : ι → C} {f : ∀ i, Xi i ⟶ S}

namespace DescentData

/-- The compatibility condition of a family of morphisms between two descent data, at one pair of
morphisms to members of the family. -/
public def IsComm (D D' : F.DescentData f) (h : ∀ i, D.obj i ⟶ D'.obj i) ⦃Y : C⦄ (q : Y ⟶ S)
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ Xi i₁) (f₂ : Y ⟶ Xi i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) : Prop :=
  (F.map f₁.op.toLoc).toFunctor.map (h i₁) ≫ D'.hom q f₁ f₂ hf₁ hf₂ =
    D.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (h i₂)

variable {D D' : F.DescentData f} {h : ∀ i, D.obj i ⟶ D'.obj i}

/-- The compatibility condition holds on the diagonal. -/
public lemma isComm_of_eq ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (f₁ f₂ : Y ⟶ Xi i) (e : f₁ = f₂)
    (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f i = q) : IsComm D D' h q f₁ f₂ hf₁ hf₂ := by
  subst e
  rw [IsComm, D.hom_self q f₁ hf₁, D'.hom_self q f₁ hf₁]
  simp

/-- The compatibility condition composes. -/
public lemma IsComm.trans ⦃Y : C⦄ {q : Y ⟶ S} ⦃i₁ i₂ i₃ : ι⦄ {f₁ : Y ⟶ Xi i₁}
    {f₂ : Y ⟶ Xi i₂} {f₃ : Y ⟶ Xi i₃} {hf₁ : f₁ ≫ f i₁ = q} {hf₂ : f₂ ≫ f i₂ = q}
    {hf₃ : f₃ ≫ f i₃ = q} (h₁₂ : IsComm D D' h q f₁ f₂ hf₁ hf₂)
    (h₂₃ : IsComm D D' h q f₂ f₃ hf₂ hf₃) : IsComm D D' h q f₁ f₃ hf₁ hf₃ := by
  unfold IsComm at *
  rw [← D'.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃, reassoc_of% h₁₂, h₂₃, D.hom_comp_assoc]

/-- The compatibility condition is symmetric. -/
public lemma IsComm.symm ⦃Y : C⦄ {q : Y ⟶ S} ⦃i₁ i₂ : ι⦄ {f₁ : Y ⟶ Xi i₁}
    {f₂ : Y ⟶ Xi i₂} {hf₁ : f₁ ≫ f i₁ = q} {hf₂ : f₂ ≫ f i₂ = q}
    (h₁₂ : IsComm D D' h q f₁ f₂ hf₁ hf₂) : IsComm D D' h q f₂ f₁ hf₂ hf₁ := by
  unfold IsComm at *
  rw [← cancel_epi (D.hom q f₁ f₂ hf₁ hf₂), ← reassoc_of% h₁₂, D'.hom_comp q f₁ f₂ f₁ hf₁ hf₂ hf₁,
    D'.hom_self q f₁ hf₁, D.hom_comp_assoc q f₁ f₂ f₁ hf₁ hf₂ hf₁, D.hom_self q f₁ hf₁]
  simp

/-- The base changes of the two sides of the compatibility condition agree exactly when the
compatibility condition holds at the base changed data. -/
private lemma pullHom_eq_pullHom_iff_isComm ⦃Y : C⦄ {q : Y ⟶ S} ⦃i₁ i₂ : ι⦄ {f₁ : Y ⟶ Xi i₁}
    {f₂ : Y ⟶ Xi i₂} {hf₁ : f₁ ≫ f i₁ = q} {hf₂ : f₂ ≫ f i₂ = q} ⦃Y' : C⦄ (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ Xi i₁) (gf₂ : Y' ⟶ Xi i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    LocallyDiscreteOpToCat.pullHom ((F.map f₁.op.toLoc).toFunctor.map (h i₁) ≫
        D'.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂ =
      LocallyDiscreteOpToCat.pullHom (D.hom q f₁ f₂ hf₁ hf₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map (h i₂)) g gf₁ gf₂ hgf₁ hgf₂ ↔
      IsComm D D' h (g ≫ q) gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁])
        (by rw [← hgf₂, Category.assoc, hf₂]) := by
  rw [IsComm, ← pullHom_comp _ _ g gf₁ gf₁ gf₂ hgf₁ hgf₁ hgf₂,
    ← pullHom_comp _ _ g gf₁ gf₂ gf₂ hgf₁ hgf₂ hgf₂, pullHom_map, pullHom_map,
    D.pullHom_hom g q _ rfl f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂,
    D'.pullHom_hom g q _ rfl f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]

/-- The compatibility condition is stable under base change. -/
public lemma IsComm.pullHom ⦃Y : C⦄ {q : Y ⟶ S} ⦃i₁ i₂ : ι⦄ {f₁ : Y ⟶ Xi i₁}
    {f₂ : Y ⟶ Xi i₂} {hf₁ : f₁ ≫ f i₁ = q} {hf₂ : f₂ ≫ f i₂ = q}
    (h₁₂ : IsComm D D' h q f₁ f₂ hf₁ hf₂) ⦃Y' : C⦄ (g : Y' ⟶ Y) (q' : Y' ⟶ S)
    (hq : g ≫ q = q') (gf₁ : Y' ⟶ Xi i₁) (gf₂ : Y' ⟶ Xi i₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    IsComm D D' h q' gf₁ gf₂ (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
      (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  subst hq
  exact (pullHom_eq_pullHom_iff_isComm g gf₁ gf₂ hgf₁ hgf₂).1
    (congrArg (fun k ↦ LocallyDiscreteOpToCat.pullHom k g gf₁ gf₂ hgf₁ hgf₂) h₁₂)

/-- The compatibility condition is local for a sieve for which the pseudofunctor is a
prestack. -/
public lemma isComm_of_isPrestackFor ⦃Y : C⦄ {q : Y ⟶ S} ⦃i₁ i₂ : ι⦄ {f₁ : Y ⟶ Xi i₁}
    {f₂ : Y ⟶ Xi i₂} {hf₁ : f₁ ≫ f i₁ = q} {hf₂ : f₂ ≫ f i₂ = q} {R : Sieve Y}
    (hR : F.IsPrestackFor R.arrows)
    (hloc : ∀ ⦃W : C⦄ (g : W ⟶ Y), R g → IsComm D D' h (g ≫ q) (g ≫ f₁) (g ≫ f₂)
      (by rw [Category.assoc, hf₁]) (by rw [Category.assoc, hf₂])) :
    IsComm D D' h q f₁ f₂ hf₁ hf₂ :=
  eq_of_pullHom_eq_of_isPrestackFor hR _ _ fun _ g hg ↦
    (pullHom_eq_pullHom_iff_isComm g _ _ rfl rfl).2 (hloc g hg)

end DescentData

end Comm

/-! ### The two-element family of a cartesian square -/

namespace CartesianSquareDescent

/-- The two-element family of objects with members `A` and `B`. -/
public abbrev pairObj (A B : C) : Bool → C
  | false => A
  | true => B

/-- The two-element family of morphisms to a common target with members `g` and `k`. -/
public abbrev pairHom {A B X : C} (g : A ⟶ X) (k : B ⟶ X) : ∀ i, pairObj A B i ⟶ X
  | false => g
  | true => k

variable {X X' Z E : C} {b : X' ⟶ X} {z : Z ⟶ X} {d : E ⟶ X'} {e : E ⟶ Z}

/-- The functor from the descent data relative to `{z, b}` to the two-fibre product
`F(Z) ×_{F(E)} F(X')`: a descent datum is sent to its two objects and its gluing isomorphism over
the corner `E`. -/
public def restriction (w : e ≫ z = d ≫ b) :
    F.DescentData (pairHom z b) ⥤
      CategoricalPullback (F.map e.op.toLoc).toFunctor (F.map d.op.toLoc).toFunctor where
  obj D := ⟨D.obj false, D.obj true, D.iso (e ≫ z) (i₁ := false) (i₂ := true) e d rfl w.symm⟩
  map φ := ⟨φ.hom false, φ.hom true, φ.comm (e ≫ z) (i₁ := false) (i₂ := true) e d rfl w.symm⟩

/-- The restriction functor is faithful. -/
public instance faithful_restriction (w : e ≫ z = d ≫ b) : (restriction (F := F) w).Faithful where
  map_injective {D D'} φ φ' hφ := by
    refine Pseudofunctor.DescentData.hom_ext fun i ↦ ?_
    cases i
    · exact congrArg CategoricalPullback.Hom.fst hφ
    · exact congrArg CategoricalPullback.Hom.snd hφ

variable (hsq : IsPullback e d z b)
variable {P T : C} {p₁ p₂ : P ⟶ X'} (hP : IsPullback p₁ p₂ b b) {a : T ⟶ Z} {r : T ⟶ P}
  (hT : IsPullback a r z (p₁ ≫ b)) {δ : X' ⟶ P} (hδ₁ : δ ≫ p₁ = 𝟙 X') (hδ₂ : δ ≫ p₂ = 𝟙 X')
  (J : GrothendieckTopology C)

/-- A morphism to `T` over a morphism `g ≫ L` to `P` gives a morphism to `Z` over `g ≫ q`. -/
private lemma comp_a_comp_z_eq (hT : IsPullback a r z (p₁ ≫ b)) ⦃W Y : C⦄ (k : W ⟶ T) (g : W ⟶ Y)
    (L : Y ⟶ P) (q : Y ⟶ X) (hk : g ≫ L = k ≫ r) (hq : L ≫ p₁ ≫ b = q) : (k ≫ a) ≫ z = g ≫ q := by
  rw [Category.assoc, hT.w, ← reassoc_of% hk, hq]

/-- Two projections of `P` agree after composing with a morphism that factors through `δ`. -/
private lemma comp_eq_comp_of_comp_diagonal_eq (hδ₁ : δ ≫ p₁ = 𝟙 X') (hδ₂ : δ ≫ p₂ = 𝟙 X')
    ⦃W Y : C⦄ {L : Y ⟶ P} {f₁ f₂ : Y ⟶ X'}
    (g : W ⟶ Y) (k : W ⟶ X') (hk : g ≫ L = k ≫ δ) (h₁ : L ≫ p₁ = f₁) (h₂ : L ≫ p₂ = f₂) :
    g ≫ f₁ = g ≫ f₂ := by
  rw [← h₁, ← h₂, ← Category.assoc, ← Category.assoc, hk, Category.assoc, Category.assoc, hδ₁,
    hδ₂]

include hP hT hδ₁ hδ₂ in
open Pseudofunctor.DescentData in
/-- **Fullness of the restriction functor.** A pair of morphisms over `Z` and over `X'` agreeing
over `E` is compatible with the gluing morphisms of two descent data at every pair: the mixed pairs
are base changes of the pair `(e, d)`, the pair `(Z, Z)` is diagonal because `z` is a
monomorphism, and the pair `(X', X')` is reduced to the mixed pairs locally on the base change of
the covering `{r, δ}` of `X' ×_X X'`. -/
public theorem full_restriction [Mono z] [F.IsPrestack J]
    (hRδ : Sieve.ofArrows _ (pairHom r δ) ∈ J P) :
    (restriction (F := F) hsq.w).Full where
  map_surjective {D D'} m := by
    let h : ∀ i, D.obj i ⟶ D'.obj i := fun i ↦ match i with
      | false => m.fst
      | true => m.snd
    have hE : IsComm D D' h (e ≫ z) (i₁ := false) (i₂ := true) e d rfl hsq.w.symm := m.w
    have hZX : ∀ ⦃Y : C⦄ (q : Y ⟶ X) (f₁ : Y ⟶ Z) (f₂ : Y ⟶ X') (hf₁ : f₁ ≫ z = q)
        (hf₂ : f₂ ≫ b = q), IsComm D D' h q (i₁ := false) (i₂ := true) f₁ f₂ hf₁ hf₂ :=
      fun Y q f₁ f₂ hf₁ hf₂ ↦ hE.pullHom (hsq.lift f₁ f₂ (hf₁.trans hf₂.symm)) q
        (by rw [IsPullback.lift_fst_assoc, hf₁]) f₁ f₂ (hsq.lift_fst _ _ _)
        (hsq.lift_snd _ _ _)
    refine ⟨{ hom := h, comm := fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ ?_ }, rfl⟩
    change IsComm D D' h q f₁ f₂ hf₁ hf₂
    cases i₁ <;> cases i₂
    · exact isComm_of_eq q f₁ f₂ ((cancel_mono z).1 (hf₁.trans hf₂.symm)) hf₁ hf₂
    · exact hZX q f₁ f₂ hf₁ hf₂
    · exact (hZX q f₂ f₁ hf₂ hf₁).symm
    · let L := hP.lift f₁ f₂ (hf₁.trans hf₂.symm)
      refine isComm_of_isPrestackFor (F.isPrestackFor' _ (J.pullback_stable L hRδ))
        fun W g hg ↦ ?_
      obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
      cases i
      · have hw := comp_a_comp_z_eq hT k g L q hk (by rw [hP.lift_fst_assoc]; exact hf₁)
        exact (hZX (g ≫ q) (k ≫ a) (g ≫ f₁) hw (by rw [Category.assoc, hf₁])).symm.trans
          (hZX (g ≫ q) (k ≫ a) (g ≫ f₂) hw (by rw [Category.assoc, hf₂]))
      · exact isComm_of_eq _ _ _ (comp_eq_comp_of_comp_diagonal_eq hδ₁ hδ₂ g k hk
          (hP.lift_fst _ _ _) (hP.lift_snd _ _ _)) _ _

/-! ### Essential surjectivity: the descent datum attached to an object of the two-fibre product -/

section EssSurj

variable (x : CategoricalPullback (F.map e.op.toLoc).toFunctor (F.map d.op.toLoc).toFunctor)

/-- For `w : Y ⟶ Z` and `f : Y ⟶ X'` agreeing over `X`, the identification of `f^* x₂` with
`w^* x₁` given by the isomorphism of `x` pulled back along the induced morphism to `E`. -/
public def tau ⦃Y : C⦄ (w : Y ⟶ Z) (f : Y ⟶ X') (h : w ≫ z = f ≫ b) :
    (F.map f.op.toLoc).toFunctor.obj x.snd ⟶ (F.map w.op.toLoc).toFunctor.obj x.fst :=
  pullHom x.iso.inv (hsq.lift w f h) f w (hsq.lift_snd _ _ _) (hsq.lift_fst _ _ _)

/-- The inverse of `tau`. -/
public def tau' ⦃Y : C⦄ (w : Y ⟶ Z) (f : Y ⟶ X') (h : w ≫ z = f ≫ b) :
    (F.map w.op.toLoc).toFunctor.obj x.fst ⟶ (F.map f.op.toLoc).toFunctor.obj x.snd :=
  pullHom x.iso.hom (hsq.lift w f h) w f (hsq.lift_fst _ _ _) (hsq.lift_snd _ _ _)

/-- `tau` followed by `tau'`. -/
public lemma tau_tau' ⦃Y : C⦄ (w : Y ⟶ Z) (f f' : Y ⟶ X') (h : w ≫ z = f ≫ b)
    (h' : w ≫ z = f' ≫ b) (hf : f = f') :
    tau hsq x w f h ≫ tau' hsq x w f' h' = eqHom x.snd hf := by
  subst hf
  rw [tau, tau', pullHom_comp, Iso.inv_hom_id, pullHom_id_self, eqHom_rfl]

/-- `tau'` followed by `tau`. -/
public lemma tau'_tau ⦃Y : C⦄ (w w' : Y ⟶ Z) (f : Y ⟶ X') (h : w ≫ z = f ≫ b)
    (h' : w' ≫ z = f ≫ b) (hw : w = w') :
    tau' hsq x w f h ≫ tau hsq x w' f h' = eqHom x.fst hw := by
  subst hw
  rw [tau, tau', pullHom_comp, Iso.hom_inv_id, pullHom_id_self, eqHom_rfl]

/-- The composite `tau ≫ tau'` does not depend on the morphism to `Z` it passes through. -/
public lemma tau_tau'_congr ⦃Y : C⦄ (w w' : Y ⟶ Z) (f f' : Y ⟶ X') (h₁ : w ≫ z = f ≫ b)
    (h₂ : w ≫ z = f' ≫ b) (h₁' : w' ≫ z = f ≫ b) (h₂' : w' ≫ z = f' ≫ b) (hw : w = w') :
    tau hsq x w f h₁ ≫ tau' hsq x w f' h₂ = tau hsq x w' f h₁' ≫ tau' hsq x w' f' h₂' := by
  subst hw
  rfl

/-- Base change of `tau`. -/
public lemma pullHom_tau ⦃Y : C⦄ (w : Y ⟶ Z) (f : Y ⟶ X') (h : w ≫ z = f ≫ b) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X') (gw : Y' ⟶ Z) (hgf : g ≫ f = gf) (hgw : g ≫ w = gw) :
    pullHom (tau hsq x w f h) g gf gw hgf hgw =
      tau hsq x gw gf (by rw [← hgf, ← hgw, Category.assoc, Category.assoc, h]) := by
  rw [tau, tau, pullHom_pullHom]
  exact pullHom_congr _ (hsq.hom_ext (by simp [hgw]) (by simp [hgf])) _ _ _ _ _ _

/-- Base change of `tau'`. -/
public lemma pullHom_tau' ⦃Y : C⦄ (w : Y ⟶ Z) (f : Y ⟶ X') (h : w ≫ z = f ≫ b) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gw : Y' ⟶ Z) (gf : Y' ⟶ X') (hgw : g ≫ w = gw) (hgf : g ≫ f = gf) :
    pullHom (tau' hsq x w f h) g gw gf hgw hgf =
      tau' hsq x gw gf (by rw [← hgf, ← hgw, Category.assoc, Category.assoc, h]) := by
  rw [tau', tau', pullHom_pullHom]
  exact pullHom_congr _ (hsq.hom_ext (by simp [hgw]) (by simp [hgf])) _ _ _ _ _ _

include hP hT hδ₁ hδ₂ in
/-- The local sections over the two members of the covering `{r, δ}` of `X' ×_X X'` that the
gluing isomorphism of the descent datum is glued from. -/
public def localSection : ∀ i, (F.map (pairHom r δ i ≫ p₁).op.toLoc).toFunctor.obj x.snd ⟶
    (F.map (pairHom r δ i ≫ p₂).op.toLoc).toFunctor.obj x.snd
  | false => tau hsq x a (r ≫ p₁) (by rw [hT.w, Category.assoc]) ≫
      tau' hsq x a (r ≫ p₂) (by rw [hT.w, Category.assoc, hP.w])
  | true => eqHom x.snd (by simp only [pairHom]; rw [hδ₁, hδ₂])

include hT in
/-- Base change of the local section over `r`. -/
public lemma pullHom_localSection_false ⦃W : C⦄ (g : W ⟶ T) (gf₁ gf₂ : W ⟶ X') (gw : W ⟶ Z)
    (hg₁ : g ≫ r ≫ p₁ = gf₁) (hg₂ : g ≫ r ≫ p₂ = gf₂) (hgw : g ≫ a = gw) :
    pullHom (localSection hsq hP hT hδ₁ hδ₂ x false) g gf₁ gf₂ hg₁ hg₂ =
      tau hsq x gw gf₁ (by rw [← hgw, ← hg₁, Category.assoc, hT.w]; simp) ≫
        tau' hsq x gw gf₂ (by rw [← hgw, ← hg₂, Category.assoc, hT.w]; simp [hP.w]) := by
  rw [localSection, ← pullHom_comp _ _ g gf₁ gw gf₂ hg₁ hgw hg₂, pullHom_tau, pullHom_tau']

include hT in
/-- The gluing isomorphism over `X' ×_X X'` exists. -/
public lemma exists_glue [Mono z] [F.IsPrestack J]
    (hRδ : Sieve.ofArrows _ (pairHom r δ) ∈ J P) :
    ∃ ψ : (F.map p₁.op.toLoc).toFunctor.obj x.snd ⟶ (F.map p₂.op.toLoc).toFunctor.obj x.snd,
      ∀ i, pullHom ψ (pairHom r δ i) (pairHom r δ i ≫ p₁) (pairHom r δ i ≫ p₂) rfl rfl =
        localSection hsq hP hT hδ₁ hδ₂ x i := by
  refine exists_pullHom_eq_of_fullyFaithful _ (F.fullyFaithfulToDescentData _ hRδ) _ _ _ _ _ ?_
  have hδq : ∀ ⦃W : C⦄ (q : W ⟶ P) (g : W ⟶ X'), g ≫ δ = q → q ≫ p₁ = q ≫ p₂ := by
    intro W q g hg
    rw [← hg, Category.assoc, Category.assoc, hδ₁, hδ₂]
  have hTq : ∀ ⦃W : C⦄ (q : W ⟶ P) (g g' : W ⟶ T), g ≫ r = q → g' ≫ r = q → g ≫ a = g' ≫ a := by
    intro W q g g' hg hg'
    refine (cancel_mono z).1 ?_
    rw [Category.assoc, Category.assoc, hT.w, reassoc_of% hg, reassoc_of% hg']
  intro W q i j g₁ g₂ h₁ h₂
  cases i <;> cases j
  · rw [pullHom_localSection_false hsq hP hT hδ₁ hδ₂ x g₁ _ _ _ _ _ rfl,
      pullHom_localSection_false hsq hP hT hδ₁ hδ₂ x g₂ _ _ _ _ _ rfl]
    exact tau_tau'_congr hsq x _ _ _ _ _ _ _ _ (hTq q g₁ g₂ h₁ h₂)
  · rw [pullHom_localSection_false hsq hP hT hδ₁ hδ₂ x g₁ _ _ _ _ _ rfl, tau_tau' hsq x _ _ _ _ _
      (hδq q g₂ h₂)]
    simp only [localSection, pullHom_eqHom]
  · rw [pullHom_localSection_false hsq hP hT hδ₁ hδ₂ x g₂ _ _ _ _ _ rfl, tau_tau' hsq x _ _ _ _ _
      (hδq q g₁ h₁)]
    simp only [localSection, pullHom_eqHom]
  · simp only [localSection, pullHom_eqHom]

/-- The two objects of the descent datum attached to `x`. -/
public abbrev objFam : ∀ i, F.obj (.mk (op (pairObj Z X' i)))
  | false => x.fst
  | true => x.snd

variable [Mono z]
  (ψ : (F.map p₁.op.toLoc).toFunctor.obj x.snd ⟶ (F.map p₂.op.toLoc).toFunctor.obj x.snd)

/-- The gluing morphisms of the descent datum attached to `x` and to an identification `ψ` over
`X' ×_X X'`: over a pair of morphisms to `Z` it is the canonical one (`z` is a monomorphism), over
a mixed pair it is `tau` or `tau'`, and over a pair of morphisms to `X'` it is the base change of
`ψ`. -/
public def homFun ⦃Y : C⦄ (q : Y ⟶ X) : ∀ ⦃i₁ i₂ : Bool⦄ (f₁ : Y ⟶ pairObj Z X' i₁)
    (f₂ : Y ⟶ pairObj Z X' i₂), f₁ ≫ pairHom z b i₁ = q → f₂ ≫ pairHom z b i₂ = q →
    ((F.map f₁.op.toLoc).toFunctor.obj (objFam x i₁) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj (objFam x i₂))
  | false, false, _, _, hf₁, hf₂ => eqHom x.fst ((cancel_mono z).1 (hf₁.trans hf₂.symm))
  | false, true, f₁, f₂, hf₁, hf₂ => tau' hsq x f₁ f₂ (hf₁.trans hf₂.symm)
  | true, false, f₁, f₂, hf₁, hf₂ => tau hsq x f₂ f₁ (hf₂.trans hf₁.symm)
  | true, true, f₁, f₂, hf₁, hf₂ => pullHom ψ (hP.lift f₁ f₂ (hf₁.trans hf₂.symm)) f₁ f₂
      (hP.lift_fst _ _ _) (hP.lift_snd _ _ _)

/-- The identification of the pullback of an object of the family with the pullback of `x₁` along
a morphism `w` to `Z` over the same morphism to `X`. -/
public def centerTo ⦃Y : C⦄ {q : Y ⟶ X} (w : Y ⟶ Z) (hw : w ≫ z = q) :
    ∀ ⦃i : Bool⦄ (f : Y ⟶ pairObj Z X' i), f ≫ pairHom z b i = q →
      ((F.map f.op.toLoc).toFunctor.obj (objFam x i) ⟶ (F.map w.op.toLoc).toFunctor.obj x.fst)
  | false, _, hf => eqHom x.fst ((cancel_mono z).1 (hf.trans hw.symm))
  | true, f, hf => tau hsq x w f (hw.trans hf.symm)

/-- The inverse of `centerTo`. -/
public def centerFrom ⦃Y : C⦄ {q : Y ⟶ X} (w : Y ⟶ Z) (hw : w ≫ z = q) :
    ∀ ⦃i : Bool⦄ (f : Y ⟶ pairObj Z X' i), f ≫ pairHom z b i = q →
      ((F.map w.op.toLoc).toFunctor.obj x.fst ⟶ (F.map f.op.toLoc).toFunctor.obj (objFam x i))
  | false, _, hf => eqHom x.fst ((cancel_mono z).1 (hw.trans hf.symm))
  | true, f, hf => tau' hsq x w f (hw.trans hf.symm)

omit [Mono z] in
/-- `centerFrom` followed by `centerTo` is the identity. -/
@[reassoc (attr := simp)]
public lemma centerFrom_centerTo [Mono z] ⦃Y : C⦄ {q : Y ⟶ X} (w : Y ⟶ Z) (hw : w ≫ z = q)
    ⦃i : Bool⦄ (f : Y ⟶ pairObj Z X' i) (hf : f ≫ pairHom z b i = q) :
    centerFrom hsq x w hw f hf ≫ centerTo hsq x w hw f hf = 𝟙 _ := by
  cases i
  · simp only [centerFrom, centerTo, eqHom_trans, eqHom_rfl]
  · simp only [centerFrom, centerTo]
    rw [tau'_tau hsq x w w f _ _ rfl, eqHom_rfl]

variable (hψr : pullHom ψ r (r ≫ p₁) (r ≫ p₂) rfl rfl = localSection hsq hP hT hδ₁ hδ₂ x false)
  (hψδ : pullHom ψ δ (δ ≫ p₁) (δ ≫ p₂) rfl rfl = localSection hsq hP hT hδ₁ hδ₂ x true)

include hψr in
/-- **Over a morphism factoring through `Z`, every gluing morphism passes through `w^* x₁`.** -/
public lemma homFun_eq ⦃Y : C⦄ (q : Y ⟶ X) (w : Y ⟶ Z) (hw : w ≫ z = q) ⦃i₁ i₂ : Bool⦄
    (f₁ : Y ⟶ pairObj Z X' i₁) (f₂ : Y ⟶ pairObj Z X' i₂) (hf₁ : f₁ ≫ pairHom z b i₁ = q)
    (hf₂ : f₂ ≫ pairHom z b i₂ = q) :
    homFun hsq hP x ψ q f₁ f₂ hf₁ hf₂ =
      centerTo hsq x w hw f₁ hf₁ ≫ centerFrom hsq x w hw f₂ hf₂ := by
  cases i₁ <;> cases i₂
  · simp only [homFun, centerTo, centerFrom, eqHom_trans]
  · obtain rfl : f₁ = w := (cancel_mono z).1 (hf₁.trans hw.symm)
    simp only [homFun, centerTo, centerFrom, eqHom_rfl, Category.id_comp]
  · obtain rfl : f₂ = w := (cancel_mono z).1 (hf₂.trans hw.symm)
    simp only [homFun, centerTo, centerFrom, eqHom_rfl, Category.comp_id]
  · have hL : w ≫ z = hP.lift f₁ f₂ (hf₁.trans hf₂.symm) ≫ p₁ ≫ b := by
      rw [hP.lift_fst_assoc]
      exact hw.trans hf₁.symm
    let t := hT.lift w (hP.lift f₁ f₂ (hf₁.trans hf₂.symm)) hL
    have htr : t ≫ r = hP.lift f₁ f₂ (hf₁.trans hf₂.symm) := hT.lift_snd _ _ _
    have hta : t ≫ a = w := hT.lift_fst _ _ _
    have h₁ : t ≫ r ≫ p₁ = f₁ := by rw [reassoc_of% htr, hP.lift_fst]
    have h₂ : t ≫ r ≫ p₂ = f₂ := by rw [reassoc_of% htr, hP.lift_snd]
    simp only [homFun, centerTo, centerFrom]
    rw [pullHom_congr ψ htr.symm f₁ f₂ _ _ (by rw [Category.assoc, h₁])
        (by rw [Category.assoc, h₂]),
      ← pullHom_pullHom ψ r (r ≫ p₁) (r ≫ p₂) t f₁ f₂ rfl rfl h₁ h₂, hψr,
      pullHom_localSection_false hsq hP hT hδ₁ hδ₂ x t f₁ f₂ w h₁ h₂ hta]

/-- The gluing morphisms are compatible with base change. -/
public lemma pullHom_homFun ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ X) (q' : Y' ⟶ X)
    (hq : g ≫ q = q') ⦃i₁ i₂ : Bool⦄ (f₁ : Y ⟶ pairObj Z X' i₁) (f₂ : Y ⟶ pairObj Z X' i₂)
    (hf₁ : f₁ ≫ pairHom z b i₁ = q) (hf₂ : f₂ ≫ pairHom z b i₂ = q)
    (gf₁ : Y' ⟶ pairObj Z X' i₁) (gf₂ : Y' ⟶ pairObj Z X' i₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (homFun hsq hP x ψ q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂ =
      homFun hsq hP x ψ q' gf₁ gf₂ (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  cases i₁ <;> cases i₂
  · simp only [homFun, pullHom_eqHom]
  · simp only [homFun]
    rw [pullHom_tau']
  · simp only [homFun]
    rw [pullHom_tau]
  · simp only [homFun]
    rw [pullHom_pullHom]
    exact pullHom_congr _ (hP.hom_ext (by simp [hgf₁]) (by simp [hgf₂])) _ _ _ _ _ _

include hδ₁ hδ₂ hψδ in
/-- The gluing morphism of a morphism with itself is the identity. -/
public lemma homFun_self ⦃Y : C⦄ (q : Y ⟶ X) ⦃i : Bool⦄ (g : Y ⟶ pairObj Z X' i)
    (hg : g ≫ pairHom z b i = q) :
    homFun hsq hP x ψ q g g hg hg = 𝟙 _ := by
  cases i
  · simp only [homFun, eqHom_rfl]
  · simp only [homFun]
    have hgd : g ≫ δ = hP.lift g g (hg.trans hg.symm) :=
      hP.hom_ext (by simp [hδ₁]) (by simp [hδ₂])
    rw [pullHom_congr ψ hgd.symm g g _ _ (by simp [hδ₁]) (by simp [hδ₂]),
      ← pullHom_pullHom ψ δ (δ ≫ p₁) (δ ≫ p₂) g g g rfl rfl (by simp [hδ₁]) (by simp [hδ₂]),
      hψδ]
    simp only [localSection, pullHom_eqHom, eqHom_rfl]

include hψr in
/-- The cocycle condition over a morphism factoring through `Z`. -/
public lemma homFun_comp_of_center ⦃Y : C⦄ (q : Y ⟶ X) (w : Y ⟶ Z) (hw : w ≫ z = q)
    ⦃i₁ i₂ i₃ : Bool⦄ (f₁ : Y ⟶ pairObj Z X' i₁) (f₂ : Y ⟶ pairObj Z X' i₂)
    (f₃ : Y ⟶ pairObj Z X' i₃) (hf₁ : f₁ ≫ pairHom z b i₁ = q)
    (hf₂ : f₂ ≫ pairHom z b i₂ = q) (hf₃ : f₃ ≫ pairHom z b i₃ = q) :
    homFun hsq hP x ψ q f₁ f₂ hf₁ hf₂ ≫ homFun hsq hP x ψ q f₂ f₃ hf₂ hf₃ =
      homFun hsq hP x ψ q f₁ f₃ hf₁ hf₃ := by
  rw [homFun_eq hsq hP hT hδ₁ hδ₂ x ψ hψr q w hw, homFun_eq hsq hP hT hδ₁ hδ₂ x ψ hψr q w hw,
    homFun_eq hsq hP hT hδ₁ hδ₂ x ψ hψr q w hw]
  simp

omit [Mono z] in
/-- The cocycle condition when the first two morphisms agree. -/
public lemma homFun_comp_of_eq [Mono z] (hψδ : pullHom ψ δ (δ ≫ p₁) (δ ≫ p₂) rfl rfl =
      localSection hsq hP hT hδ₁ hδ₂ x true) ⦃Y : C⦄ (q : Y ⟶ X)
    ⦃i₁ i₃ : Bool⦄ (f₁ f₂ : Y ⟶ pairObj Z X' i₁) (f₃ : Y ⟶ pairObj Z X' i₃) (he : f₁ = f₂)
    (hf₁ : f₁ ≫ pairHom z b i₁ = q) (hf₂ : f₂ ≫ pairHom z b i₁ = q)
    (hf₃ : f₃ ≫ pairHom z b i₃ = q) :
    homFun hsq hP x ψ q f₁ f₂ hf₁ hf₂ ≫ homFun hsq hP x ψ q f₂ f₃ hf₂ hf₃ =
      homFun hsq hP x ψ q f₁ f₃ hf₁ hf₃ := by
  subst he
  rw [homFun_self hsq hP hT hδ₁ hδ₂ x ψ hψδ, Category.id_comp]

include hψr hψδ in
/-- The cocycle condition. -/
public lemma homFun_comp [F.IsPrestack J] (hRδ : Sieve.ofArrows _ (pairHom r δ) ∈ J P)
    ⦃Y : C⦄ (q : Y ⟶ X) ⦃i₁ i₂ i₃ : Bool⦄ (f₁ : Y ⟶ pairObj Z X' i₁)
    (f₂ : Y ⟶ pairObj Z X' i₂) (f₃ : Y ⟶ pairObj Z X' i₃) (hf₁ : f₁ ≫ pairHom z b i₁ = q)
    (hf₂ : f₂ ≫ pairHom z b i₂ = q) (hf₃ : f₃ ≫ pairHom z b i₃ = q) :
    homFun hsq hP x ψ q f₁ f₂ hf₁ hf₂ ≫ homFun hsq hP x ψ q f₂ f₃ hf₂ hf₃ =
      homFun hsq hP x ψ q f₁ f₃ hf₁ hf₃ := by
  cases i₁
  · exact homFun_comp_of_center hsq hP hT hδ₁ hδ₂ x ψ hψr q f₁ hf₁ f₁ f₂ f₃ hf₁ hf₂ hf₃
  cases i₂
  · exact homFun_comp_of_center hsq hP hT hδ₁ hδ₂ x ψ hψr q f₂ hf₂ f₁ f₂ f₃ hf₁ hf₂ hf₃
  cases i₃
  · exact homFun_comp_of_center hsq hP hT hδ₁ hδ₂ x ψ hψr q f₃ hf₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
  let L := hP.lift f₁ f₂ (hf₁.trans hf₂.symm)
  refine eq_of_pullHom_eq_of_isPrestackFor (F.isPrestackFor' _ (J.pullback_stable L hRδ)) _ _
    fun W g hg ↦ ?_
  rw [← pullHom_comp _ _ g (g ≫ f₁) (g ≫ f₂) (g ≫ f₃) rfl rfl rfl,
    pullHom_homFun hsq hP x ψ g q (g ≫ q) rfl, pullHom_homFun hsq hP x ψ g q (g ≫ q) rfl,
    pullHom_homFun hsq hP x ψ g q (g ≫ q) rfl]
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  cases i
  · have hw := comp_a_comp_z_eq hT k g L q hk (by rw [hP.lift_fst_assoc]; exact hf₁)
    exact homFun_comp_of_center hsq hP hT hδ₁ hδ₂ x ψ hψr (g ≫ q) (k ≫ a) hw _ _ _ _ _ _
  · exact homFun_comp_of_eq hsq hP hT hδ₁ hδ₂ x ψ hψδ (g ≫ q) _ _ _
      (comp_eq_comp_of_comp_diagonal_eq hδ₁ hδ₂ g k hk (hP.lift_fst _ _ _) (hP.lift_snd _ _ _))
      _ _ _

/-- **The descent datum relative to `{z, b}` attached to an object of the two-fibre product** and
to an identification `ψ` over `X' ×_X X'` restricting to the composite through `x.iso` over `r`
and to the identity over the diagonal. -/
public def descentData [F.IsPrestack J] (hRδ : Sieve.ofArrows _ (pairHom r δ) ∈ J P) :
    F.DescentData (pairHom z b) where
  obj := objFam x
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := homFun hsq hP x ψ q f₁ f₂ hf₁ hf₂
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    pullHom_homFun hsq hP x ψ g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self _ q _ g hg := homFun_self hsq hP hT hδ₁ hδ₂ x ψ hψδ q g hg
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    homFun_comp hsq hP hT hδ₁ hδ₂ J x ψ hψr hψδ hRδ q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- The restriction of the descent datum attached to `x` is `x`. -/
public def restrictionObjDescentDataIso [F.IsPrestack J]
    (hRδ : Sieve.ofArrows _ (pairHom r δ) ∈ J P) :
    (restriction (F := F) hsq.w).obj (descentData hsq hP hT hδ₁ hδ₂ J x ψ hψr hψδ hRδ) ≅ x :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
    change _ ≫ x.iso.hom = tau' hsq x e d hsq.w ≫ _
    have h1 : tau' hsq x e d hsq.w = x.iso.hom := by
      rw [tau', pullHom_congr _ (hsq.hom_ext (by simp) (by simp) : hsq.lift e d hsq.w = 𝟙 E)
        e d _ _ (Category.id_comp _) (Category.id_comp _), pullHom_id]
    rw [h1]
    exact ((congrArg (· ≫ x.iso.hom) (Functor.map_id _ _)).trans (Category.id_comp _)).trans
      ((Category.comp_id _).symm.trans (congrArg (x.iso.hom ≫ ·) (Functor.map_id _ _).symm)))

end EssSurj

include hsq hP hT hδ₁ hδ₂ in
/-- **Essential surjectivity of the restriction functor.** -/
public theorem essSurj_restriction [Mono z] [F.IsPrestack J]
    (hRδ : Sieve.ofArrows _ (pairHom r δ) ∈ J P) :
    (restriction (F := F) hsq.w).EssSurj where
  mem_essImage x := by
    obtain ⟨ψ, hψ⟩ := exists_glue hsq hP hT hδ₁ hδ₂ J x hRδ
    exact ⟨_, ⟨restrictionObjDescentDataIso hsq hP hT hδ₁ hδ₂ J x ψ (hψ false) (hψ true) hRδ⟩⟩

include hsq hP hT hδ₁ hδ₂ in
/-- **The restriction functor from descent data relative to `{z, b}` to the two-fibre product is
an equivalence** for a cartesian square with `z` a monomorphism, as soon as the pseudofunctor is a
prestack for a topology for which the base change of `z` together with the diagonal of `b` cover
`X' ×_X X'`. -/
public theorem isEquivalence_restriction [Mono z] [F.IsPrestack J]
    (hRδ : Sieve.ofArrows _ (pairHom r δ) ∈ J P) :
    (restriction (F := F) hsq.w).IsEquivalence := by
  have := full_restriction (F := F) hsq hP hT hδ₁ hδ₂ J hRδ
  have := essSurj_restriction (F := F) hsq hP hT hδ₁ hδ₂ J hRδ
  exact { }

include hsq hP hT hδ₁ hδ₂ in
/-- **Descent across a cartesian square.** For a stack `F` for `J`, a cartesian square
`E ⟶ Z, E ⟶ X'` over `z : Z ⟶ X`, `b : X' ⟶ X` with `z` a monomorphism, `{z, b}` covering `X`, and
`{r, δ}` covering `X' ×_X X'`, the canonical functor `F(X) ⥤ F(Z) ×_{F(E)} F(X')` (the descent
data functor followed by the restriction) is an equivalence. -/
public theorem isEquivalence_comp_restriction [Mono z] [F.IsStack J]
    (hzb : Sieve.ofArrows _ (pairHom z b) ∈ J X)
    (hRδ : Sieve.ofArrows _ (pairHom r δ) ∈ J P) :
    (F.toDescentData (pairHom z b) ⋙ restriction (F := F) hsq.w).IsEquivalence := by
  have := F.isEquivalence_toDescentData (pairHom z b) hzb
  have := isEquivalence_restriction (F := F) hsq hP hT hδ₁ hδ₂ J hRδ
  infer_instance

end CartesianSquareDescent

end CategoryTheory.Pseudofunctor
