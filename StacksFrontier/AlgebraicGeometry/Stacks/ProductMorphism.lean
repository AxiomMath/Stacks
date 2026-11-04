module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal

/-!
# The product of two 1-morphisms of categories fibred in groupoids (Stacks 0303)

Fix a base category `𝒞`. The product `𝒳₁ × 𝒳₂` of two categories fibred in groupoids over `𝒞`
is their 2-fibre product over the final object `𝟭 𝒞`
(`CategoryTheory.CatFiberedInGroupoids.product`), and a pair of 1-morphisms `f₁ : 𝒳₁ ⟶ 𝒴₁`,
`f₂ : 𝒳₂ ⟶ 𝒴₂` induces `f₁ × f₂ : 𝒳₁ × 𝒳₂ ⟶ 𝒴₁ × 𝒴₂`. Over the big fppf site of a scheme `S`,
Stacks 0303 says that `f₁ × f₂` is representable by algebraic spaces as soon as `f₁` and `f₂`
are.

The proof is the source's: `f₁ × f₂` factors as `(f₁ × id) ∘ (id × f₂)`, so by Stacks 0301 it
is enough to treat a product one factor of which is an identity, and such a product is a base
change of the corresponding factor. The base change is exhibited by *cancelling the middle
factor*: for `f : 𝒳 ⟶ 𝒴` the iterated 2-fibre product `(𝒵 × 𝒴) ×_{pr₂, 𝒴, f} 𝒳` is `𝒵 × 𝒳`
(Stacks 02XD, `CategoryTheory.TwoFibreProductOver.cancelSnd`), compatibly with `id × f` and the
projection to `𝒵 × 𝒴`, so Stacks 0457 carries the representability of that projection — which is
Stacks 0302 — to `id × f`.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.productMap`: the product `f₁ × f₂` of two 1-morphisms.
* `CategoryTheory.CatFiberedInGroupoids.productSwap`: the exchange of the two factors of a
  product.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.productNatIso`: two 1-morphisms into a product which are
  vertically 2-isomorphic on both projections are 2-isomorphic. This is Stacks 0040 for the
  product, and it is what every comparison below is assembled with.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_productMap`: **Stacks 0303**.

## Implementation notes

`CategoryTheory.CatFiberedInGroupoids.productMap` is
`CategoryTheory.TwoFibreProductOver.prodMap` of the two underlying functors, which is already
stated for independent targets; nothing has to be lifted, and the compatibility with both
projections and with the structure functor holds by `rfl`. In particular the comparison
2-isomorphism that the universal property of the target product would require is not formed: the
mediating functor is written down directly.

All three comparisons of 1-morphisms into a product — for the exchange, for the composition
`(f₁ × id) ∘ (id × f₂) = f₁ × f₂`, and for the cancellation — go through
`CategoryTheory.CatFiberedInGroupoids.productNatIso`, whose components are
`CategoryTheory.TwoFibreProductOver.isoMkVertical`. The compatibility field of such a component
is an identity between `eqToHom`s, because the comparison isomorphism of an object of a product
over `𝒞` is forced to be one (`CategoryTheory.TwoFibreProductOver.prodOver_iso_hom`), and it is
exactly `CategoryTheory.TwoFibreProductOver.prodOver_w_eqToHom`. That identity is composed in by
`congrArg` rather than rewritten: a goal mentioning the comparison isomorphism of an object of
the product is not type-correct at `implicit` transparency, so `rw` declines on it after the
first step, while an explicit chain of `Eq.trans` and `congrArg` goes through.

The cancellation is applied with its middle category taken to be the *second* factor `𝒴` of the
target product, so that the leg out of the inner product is its second projection, which is the
shape `CategoryTheory.TwoFibreProductOver.cancelSnd` has. The case where the identity is in the
second slot is then obtained from the first by conjugating with
`CategoryTheory.CatFiberedInGroupoids.productSwap`, rather than by repeating the argument.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 0303](https://stacks.math.columbia.edu/tag/0303)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.CatFiberedInGroupoids

universe u v w v' w'

variable {𝒞 : Type (u + 1)} [Category.{u} 𝒞]

section Defs

variable {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : CatFiberedInGroupoids.{u, v, u + 1, w} 𝒞}

/-- **The product of two 1-morphisms of categories fibred in groupoids over `𝒞`.** On an object
`(U, x₁, x₂)` of `𝒳₁ × 𝒳₂` it is `(U, f₁ x₁, f₂ x₂)`, and on a morphism it is the pair of
images. The two targets are independent; the common-target case is the one the relative
diagonal square uses. This is the 1-morphism Stacks 0303 is about. -/
def productMap (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂) : product 𝒳₁ 𝒳₂ ⟶ product 𝒴₁ 𝒴₂ :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.prodMap (homFunctor f₁) (homFunctor f₂)
        (homFunctor_comp_p f₁) (homFunctor_comp_p f₂)
      w := TwoFibreProductOver.prodMap_comp_structureFunctor _ _ _ _ }

/-- The product of two 1-morphisms commutes with the first projection. -/
theorem productMap_comp_fst (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂) :
    (productMap f₁ f₂).hom.toFunctor ⋙
        TwoFibreProductOver.fst 𝒴₁.val.p 𝒴₂.val.p (𝟭 𝒞) 𝒴₁.val.p 𝒴₂.val.p =
      TwoFibreProductOver.fst 𝒳₁.val.p 𝒳₂.val.p (𝟭 𝒞) 𝒳₁.val.p 𝒳₂.val.p ⋙ homFunctor f₁ :=
  rfl

/-- The product of two 1-morphisms commutes with the second projection. -/
theorem productMap_comp_snd (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂) :
    (productMap f₁ f₂).hom.toFunctor ⋙
        TwoFibreProductOver.snd 𝒴₁.val.p 𝒴₂.val.p (𝟭 𝒞) 𝒴₁.val.p 𝒴₂.val.p =
      TwoFibreProductOver.snd 𝒳₁.val.p 𝒳₂.val.p (𝟭 𝒞) 𝒳₁.val.p 𝒳₂.val.p ⋙ homFunctor f₂ :=
  rfl

/-- **The exchange of the two factors of a product**, as a 1-morphism of categories fibred in
groupoids over `𝒞`: it is `CategoryTheory.TwoFibreProductOver.swap`, which inverts the forced
comparison isomorphism of an object. -/
def productSwap (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} 𝒞) :
    product 𝒳 𝒴 ⟶ product 𝒴 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.swap 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p
      w := TwoFibreProductOver.swap_comp_structureFunctor _ _ _ _ _ }

/-- The exchange of factors is an equivalence of the underlying categories. -/
instance isEquivalence_productSwap (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} 𝒞) :
    Functor.IsEquivalence (productSwap 𝒳 𝒴).hom.toFunctor :=
  inferInstanceAs
    (Functor.IsEquivalence (TwoFibreProductOver.swap 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p))

end Defs

section NatIso

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} 𝒞} {W : BasedCategory.{v', w'} 𝒞}

attribute [local implicit_reducible] product

/-- **Stacks 0040 for a product.** Two 1-morphisms `γ`, `δ` from a category over `𝒞` to a
product `𝒳 × 𝒴` which are 2-isomorphic after composing with each of the two projections, by
2-isomorphisms whose components are vertical, are themselves 2-isomorphic.

The component at `x` is `CategoryTheory.TwoFibreProductOver.isoMkVertical` of the two given
components; its compatibility with the comparison isomorphisms of the two objects is an identity
between `eqToHom`s, since those comparison isomorphisms are forced. -/
noncomputable def productNatIso (γ δ : W ⥤ᵇ (product 𝒳 𝒴).val)
    (i : γ.toFunctor ⋙ TwoFibreProductOver.fst 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p ≅
      δ.toFunctor ⋙ TwoFibreProductOver.fst 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p)
    (j : γ.toFunctor ⋙ TwoFibreProductOver.snd 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p ≅
      δ.toFunctor ⋙ TwoFibreProductOver.snd 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p)
    (hi : ∀ x : W.obj, 𝒳.val.p.IsHomLift (𝟙 (W.p.obj x)) (i.hom.app x))
    (hj : ∀ x : W.obj, 𝒴.val.p.IsHomLift (𝟙 (W.p.obj x)) (j.hom.app x)) :
    γ ≅ δ := by
  refine BasedNatIso.mkNatIso (NatIso.ofComponents (fun x =>
    TwoFibreProductOver.isoMkVertical (i.app x) (j.app x) (hi x) (hj x) ?_) ?_) ?_
  · have hP : (γ.obj x).iso.hom =
        eqToHom ((γ.obj x).hx.trans (γ.obj x).hy.symm) :=
      TwoFibreProductOver.prodOver_iso_hom _
    have hQ : (δ.obj x).iso.hom =
        eqToHom ((δ.obj x).hx.trans (δ.obj x).hy.symm) :=
      TwoFibreProductOver.prodOver_iso_hom _
    have hγb : (γ.obj x).base = W.p.obj x := Functor.congr_obj γ.w x
    have hδb : (δ.obj x).base = W.p.obj x := Functor.congr_obj δ.w x
    have h₁ : 𝒳.val.p.IsHomLift (𝟙 (W.p.obj x)) (i.app x).hom := hi x
    have h₂ : 𝒴.val.p.IsHomLift (𝟙 (W.p.obj x)) (j.app x).hom := hj x
    have key := TwoFibreProductOver.prodOver_w_eqToHom
      ((γ.obj x).hx.trans hγb) ((γ.obj x).hy.trans hγb)
      ((δ.obj x).hx.trans hδb) ((δ.obj x).hy.trans hδb) h₁ h₂
    exact (congrArg (fun t => 𝒳.val.p.map (i.app x).hom ≫ t) hQ).trans
      (key.trans (congrArg (fun t => t ≫ 𝒴.val.p.map (j.app x).hom) hP).symm)
  · exact fun h => TwoFibreProductOver.Hom.ext' (i.hom.naturality h) (j.hom.naturality h)
  · exact fun x => TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 (W.p.obj x)) (hi x)

/-- A based functor into a product, followed by the first projection, lifts identities
vertically. -/
private theorem isHomLift_id_fst (F : W ⥤ᵇ (product 𝒳 𝒴).val) (x : W.obj) :
    𝒳.val.p.IsHomLift (𝟙 (W.p.obj x))
      (𝟙 ((F.toFunctor ⋙ TwoFibreProductOver.fst 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p).obj x)) :=
  IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp F
    ⟨TwoFibreProductOver.fst 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p,
      TwoFibreProductOver.fst_comp_eq⟩) x)

/-- A based functor into a product, followed by the second projection, lifts identities
vertically. -/
private theorem isHomLift_id_snd (F : W ⥤ᵇ (product 𝒳 𝒴).val) (x : W.obj) :
    𝒴.val.p.IsHomLift (𝟙 (W.p.obj x))
      (𝟙 ((F.toFunctor ⋙ TwoFibreProductOver.snd 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p).obj x)) :=
  IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp F
    ⟨TwoFibreProductOver.snd 𝒳.val.p 𝒴.val.p (𝟭 𝒞) 𝒳.val.p 𝒴.val.p,
      TwoFibreProductOver.snd_comp_eq⟩) x)

end NatIso

section Comparisons

variable {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ 𝒵₁ 𝒵₂ : CatFiberedInGroupoids.{u, v, u + 1, w} 𝒞}

/-- **The product of two 1-morphisms is functorial.** The composite of `f₁ × f₂` with `g₁ × g₂`
is `(f₁ ≫ g₁) × (f₂ ≫ g₂)`, up to a 2-isomorphism over `𝒞` which is the identity on both
projections. -/
noncomputable def productMapCompIso (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂) (g₁ : 𝒴₁ ⟶ 𝒵₁)
    (g₂ : 𝒴₂ ⟶ 𝒵₂) :
    BasedFunctor.comp (productMap f₁ f₂).hom (productMap g₁ g₂).hom ≅
      (productMap (f₁ ≫ g₁) (f₂ ≫ g₂)).hom :=
  productNatIso _ _ (Iso.refl _) (Iso.refl _)
    (fun x => IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp
      (BasedFunctor.comp (productMap f₁ f₂).hom (productMap g₁ g₂).hom)
      ⟨TwoFibreProductOver.fst 𝒵₁.val.p 𝒵₂.val.p (𝟭 𝒞) 𝒵₁.val.p 𝒵₂.val.p,
        TwoFibreProductOver.fst_comp_eq⟩) x))
    (fun x => IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp
      (BasedFunctor.comp (productMap f₁ f₂).hom (productMap g₁ g₂).hom)
      ⟨TwoFibreProductOver.snd 𝒵₁.val.p 𝒵₂.val.p (𝟭 𝒞) 𝒵₁.val.p 𝒵₂.val.p,
        TwoFibreProductOver.snd_comp_eq⟩) x))

/-- **The product of two 1-morphisms is compatible with the exchange of factors.** -/
noncomputable def productSwapMapIso (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂) :
    BasedFunctor.comp (productSwap 𝒳₁ 𝒳₂).hom (productMap f₂ f₁).hom ≅
      BasedFunctor.comp (productMap f₁ f₂).hom (productSwap 𝒴₁ 𝒴₂).hom :=
  productNatIso _ _ (Iso.refl _) (Iso.refl _)
    (fun x => IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp
      (BasedFunctor.comp (productSwap 𝒳₁ 𝒳₂).hom (productMap f₂ f₁).hom)
      ⟨TwoFibreProductOver.fst 𝒴₂.val.p 𝒴₁.val.p (𝟭 𝒞) 𝒴₂.val.p 𝒴₁.val.p,
        TwoFibreProductOver.fst_comp_eq⟩) x))
    (fun x => IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp
      (BasedFunctor.comp (productSwap 𝒳₁ 𝒳₂).hom (productMap f₂ f₁).hom)
      ⟨TwoFibreProductOver.snd 𝒴₂.val.p 𝒴₁.val.p (𝟭 𝒞) 𝒴₂.val.p 𝒴₁.val.p,
        TwoFibreProductOver.snd_comp_eq⟩) x))

end Comparisons

end CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

open CategoryTheory.CatFiberedInGroupoids

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Cancel

variable {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- The second projection of the product `𝒵 × 𝒴`, as a 1-morphism of categories over the big
fppf site of `S`. It is a `CategoryTheory.BasedFunctor` rather than a 1-morphism of the
2-category, because the product has a larger morphism and object universe than its factors. -/
def productSnd (𝒵 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    (product 𝒵 𝒴).val ⥤ᵇ 𝒴.val where
  toFunctor := TwoFibreProductOver.snd 𝒵.val.p 𝒴.val.p (𝟭 (BigFppfOver B S hS))
    𝒵.val.p 𝒴.val.p
  w := TwoFibreProductOver.snd_comp_eq

/-- The identity functor of a based category is an equivalence. -/
private instance isEquivalence_basedFunctor_id (X : BasedCategory.{v, w} (BigFppfOver B S hS)) :
    Functor.IsEquivalence (BasedFunctor.id X).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 X.obj))

/-- The 2-cell identifying `f ⋙ p𝒴` with `p𝒳` for a 1-morphism `f` of categories over the site
is vertical: it is an `eqToHom` of the base. -/
theorem isHomLift_eqToIso_hom_app {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
    (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) (x : 𝒳.val.obj) :
    (𝟭 (BigFppfOver B S hS)).IsHomLift (𝟙 (𝒳.val.p.obj x))
      ((eqToIso f.hom.w).hom.app x) := by
  rw [show (eqToIso f.hom.w).hom.app x = eqToHom (Functor.congr_obj f.hom.w x) by simp]
  exact TwoFibreProductOver.isHomLift_id_eqToHom (Functor.congr_obj f.hom.w x) rfl
    (Functor.congr_obj f.hom.w x)

/-- **Cancelling the middle factor, for the base change of a product along its own second
projection.** The iterated 2-fibre product `(𝒵 × 𝒴) ×_{pr₂, 𝒴, f} 𝒳` is the product `𝒵 × 𝒳`:
the `𝒴`-entry of an object is determined by its `𝒳`-entry up to the comparison isomorphism it
carries. This is Stacks 02XD, `CategoryTheory.TwoFibreProductOver.cancelSnd`, instantiated with
the final object `𝟭` of the 2-category as the target of the inner product. -/
def productCancel (f : 𝒳 ⟶ 𝒴) :
    (twoFibreProduct B S hS 𝒴 (product 𝒵 𝒴) 𝒳 (productSnd B S hS 𝒵 𝒴) f.hom).val ⥤ᵇ
      (product 𝒵 𝒳).val where
  toFunctor :=
    TwoFibreProductOver.cancelSnd 𝒵.val.p 𝒴.val.p (𝟭 (BigFppfOver B S hS)) 𝒳.val.p
      𝒵.val.p 𝒴.val.p f.hom.toFunctor 𝒳.val.p (Functor.comp_id _)
      (eqToIso f.hom.w) (isHomLift_eqToIso_hom_app B S hS f)
  w := TwoFibreProductOver.cancelSnd_comp_structureFunctor ..

/-- The cancellation is an equivalence of the underlying categories (Stacks 02XD). -/
instance isEquivalence_productCancel (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (productCancel B S hS (𝒵 := 𝒵) f).toFunctor :=
  TwoFibreProductOver.isEquivalence_cancelSnd 𝒵.val.p 𝒴.val.p (𝟭 (BigFppfOver B S hS))
    𝒳.val.p 𝒵.val.p 𝒴.val.p f.hom.toFunctor 𝒳.val.p (Functor.comp_id _) f.hom.w
    (eqToIso f.hom.w) (isHomLift_eqToIso_hom_app B S hS f)

/-- **The cancellation identifies the base change of `pr₂ : 𝒵 × 𝒴 ⟶ 𝒴` along `f` with
`id × f`.** Composing it with `id_𝒵 × f` is the projection of the iterated 2-fibre product to
`𝒵 × 𝒴`, up to a 2-isomorphism over the site whose first component is the identity and whose
second is the comparison isomorphism of the iterated product. -/
noncomputable def productCancelIso (f : 𝒳 ⟶ 𝒴) :
    BasedFunctor.comp (productCancel B S hS (𝒵 := 𝒵) f) (productMap (𝟙 𝒵) f).hom ≅
      BasedFunctor.comp
        (twoFibreProductFst B S hS 𝒴 (product 𝒵 𝒴) 𝒳 (productSnd B S hS 𝒵 𝒴) f.hom)
        (BasedFunctor.id (product 𝒵 𝒴).val) := by
  refine productNatIso _ _ ?_ ?_ ?_ ?_
  · exact Iso.refl _
  · exact (TwoFibreProductOver.psiIso (product 𝒵 𝒴).val.p 𝒳.val.p 𝒴.val.p
      (productSnd B S hS 𝒵 𝒴).toFunctor f.hom.toFunctor).symm
  · intro x
    exact IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp
      (BasedFunctor.comp (productCancel B S hS (𝒵 := 𝒵) f) (productMap (𝟙 𝒵) f).hom)
      ⟨TwoFibreProductOver.fst 𝒵.val.p 𝒴.val.p (𝟭 (BigFppfOver B S hS)) 𝒵.val.p 𝒴.val.p,
        TwoFibreProductOver.fst_comp_eq⟩) x)
  · intro x
    have hv : 𝒴.val.p.IsHomLift
        (𝟙 ((twoFibreProduct B S hS 𝒴 (product 𝒵 𝒴) 𝒳
          (productSnd B S hS 𝒵 𝒴) f.hom).val.p.obj x))
        ((TwoFibreProductOver.psiIso (product 𝒵 𝒴).val.p 𝒳.val.p 𝒴.val.p
          (productSnd B S hS 𝒵 𝒴).toFunctor f.hom.toFunctor).app x).hom :=
      TwoFibreProductOver.psiIso_hom_vertical x
    exact IsHomLift.lift_id_inv 𝒴.val.p _
      ((TwoFibreProductOver.psiIso (product 𝒵 𝒴).val.p 𝒳.val.p 𝒴.val.p
        (productSnd B S hS 𝒵 𝒴).toFunctor f.hom.toFunctor).app x)

/-- **Stacks 0303 when the first factor is an identity.** `id_𝒵 × f` is a base change of `f`
along the second projection of `𝒵 × 𝒴`, so it is representable by algebraic spaces whenever `f`
is: the base change is Stacks 0302 and the comparison is
`AlgebraicGeometry.Stack.productCancelIso`. -/
theorem isRepresentableByAlgebraicSpaces_productMap_id_left (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    IsRepresentableByAlgebraicSpaces B S hS (productMap (𝟙 𝒵) f).hom := by
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (twoFibreProductFst B S hS 𝒴 (product 𝒵 𝒴) 𝒳 (productSnd B S hS 𝒵 𝒴) f.hom)
    (productMap (𝟙 𝒵) f).hom (productCancel B S hS f)
    (BasedFunctor.id (product 𝒵 𝒴).val) (productCancelIso B S hS f)).mpr
    (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒴 (product 𝒵 𝒴) 𝒳
      (productSnd B S hS 𝒵 𝒴) f.hom hf)

/-- **Stacks 0303 when the second factor is an identity**, obtained from
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_productMap_id_left` by exchanging the
two factors. -/
theorem isRepresentableByAlgebraicSpaces_productMap_id_right (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    IsRepresentableByAlgebraicSpaces B S hS (productMap f (𝟙 𝒵)).hom :=
  (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (productMap f (𝟙 𝒵)).hom (productMap (𝟙 𝒵) f).hom
    (productSwap 𝒳 𝒵).hom (productSwap 𝒴 𝒵).hom
    (productSwapMapIso f (𝟙 𝒵))).mp
    (isRepresentableByAlgebraicSpaces_productMap_id_left B S hS f hf)

end Cancel

section Product

variable {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- **Stacks 0303.** The product `f₁ × f₂` of two 1-morphisms of categories fibred in groupoids
over the big fppf site of `S`, each representable by algebraic spaces, is representable by
algebraic spaces.

It factors as `(id_{𝒴₁} × f₂) ∘ (f₁ × id_{𝒳₂})`, each factor is representable by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_productMap_id_left` resp.
`…_id_right`, and the composite is representable by Stacks 0301. -/
@[stacks 0303]
theorem isRepresentableByAlgebraicSpaces_productMap (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂)
    (hf₁ : IsRepresentableByAlgebraicSpaces B S hS f₁.hom)
    (hf₂ : IsRepresentableByAlgebraicSpaces B S hS f₂.hom) :
    IsRepresentableByAlgebraicSpaces B S hS (productMap f₁ f₂).hom := by
  have hcomp := isRepresentableByAlgebraicSpaces_comp B S hS
    (productMap f₁ (𝟙 𝒳₂)) (productMap (𝟙 𝒴₁) f₂)
    (isRepresentableByAlgebraicSpaces_productMap_id_right B S hS f₁ hf₁)
    (isRepresentableByAlgebraicSpaces_productMap_id_left B S hS f₂ hf₂)
  refine (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (productMap f₁ f₂).hom
    (BasedFunctor.comp (productMap f₁ (𝟙 𝒳₂)).hom (productMap (𝟙 𝒴₁) f₂).hom)
    (BasedFunctor.id (product 𝒳₁ 𝒳₂).val) (BasedFunctor.id (product 𝒴₁ 𝒴₂).val) ?_).mp hcomp
  refine productNatIso _ _ (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact isHomLift_id_fst _
  · exact isHomLift_id_snd _

end Product

end AlgebraicGeometry.Stack

end
