module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange

/-!
# Invariance of the separation conditions under equivalence

The quasi-DM, separated and quasi-separated conditions on a 1-morphism of algebraic stacks are
relative properties of its relative diagonal. For a 1-morphism `c : 𝒰' ⥤ 𝒰` over the base and a
1-morphism `q' ≅ c ⋙ q` to a fixed target `𝒵`, this file constructs the comparison
`c × c : 𝒰' ×_𝒵 𝒰' ⥤ 𝒰 ×_𝒵 𝒰` of self-products, shows that it is an equivalence as soon as `c` is
and that it carries the relative diagonal of `q'` to that of `q`, and deduces that the three
separation conditions are invariant under an equivalence of the source. Consequently the three
conditions are stable under base change along an arbitrary 2-fibre-product square, not only along
the canonical square `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.selfProdMap`: the functor `c × c` on self-products over a
  fixed target, for a 1-morphism `c` over the base.
* `CategoryTheory.TwoFibreProductOver.reindexedSelfProdMap`: the same, read on the self-product of
  a leg only 2-isomorphic to `c ⋙ q`.
* `CategoryTheory.TwoFibreProductOver.diagonalSelfProdIso`: `c × c` carries the relative diagonal
  of `q'` to that of `q`.
* `AlgebraicGeometry.Stack.selfProdComparison` and
  `AlgebraicGeometry.Stack.relativeDiagonalSelfProdIso`: the same two, read in the 2-category of
  categories fibred in groupoids over the big fppf site of `S`.

## Main results

* `CategoryTheory.TwoFibreProductOver.isEquivalence_selfProdMap` and
  `CategoryTheory.TwoFibreProductOver.isEquivalence_reindexedSelfProdMap`: `c × c` is an
  equivalence as soon as `c` is.
* `AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks`: the comparison
  1-morphism between two 2-fibre products of one cospan of algebraic stacks is an equivalence of
  the underlying categories.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_equivalence`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_equivalence` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_equivalence`: the three separation
  conditions are invariant under an equivalence of the source, over a fixed target.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_baseChange_of_isTwoFibreProduct`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_baseChange_of_isTwoFibreProduct` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_baseChange_of_isTwoFibreProduct`: the
  second projection of an arbitrary 2-fibre product of `(f, g)` has the separation condition as
  soon as `f` does.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒰 : Type u₂} [Category.{v₂} 𝒰]
  {𝒰' : Type u₃} [Category.{v₃} 𝒰'] {𝒵 : Type u₄} [Category.{v₄} 𝒵]

/-- The product `c × c` of a 1-morphism over `𝒞` with itself, as a functor
`𝒰' ×_{c ⋙ q, 𝒵, c ⋙ q} 𝒰' ⥤ 𝒰 ×_{q, 𝒵, q} 𝒰`: it applies `c` to both components of an object
and leaves the comparison isomorphism unchanged. It is
`CategoryTheory.TwoFibreProductOver.precomposeSnd` on the second factor followed by
`CategoryTheory.TwoFibreProductOver.precomposeFst` on the first. -/
def selfProdMap (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒰' : 𝒰' ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (q : 𝒰 ⥤ 𝒵) (c : 𝒰' ⥤ 𝒰) (hc : c ⋙ p𝒰 = p𝒰') :
    TwoFibreProductOver p𝒰' p𝒰' p𝒵 (c ⋙ q) (c ⋙ q) ⥤
      TwoFibreProductOver p𝒰 p𝒰 p𝒵 q q :=
  precomposeSnd (pT := p𝒰') (pℬ := p𝒵) (c ⋙ q) q c hc ⋙
    precomposeFst p𝒰' p𝒰 p𝒰 p𝒵 q q c hc

/-- `c × c` is strictly over `𝒞`. -/
@[simp] lemma selfProdMap_comp_structureFunctor (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒰' : 𝒰' ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (q : 𝒰 ⥤ 𝒵) (c : 𝒰' ⥤ 𝒰) (hc : c ⋙ p𝒰 = p𝒰') :
    selfProdMap p𝒰 p𝒰' p𝒵 q c hc ⋙ structureFunctor p𝒰 p𝒰 p𝒵 q q =
      structureFunctor p𝒰' p𝒰' p𝒵 (c ⋙ q) (c ⋙ q) := rfl

/-- `c × c` is an equivalence as soon as `c` is. -/
theorem isEquivalence_selfProdMap (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒰' : 𝒰' ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (q : 𝒰 ⥤ 𝒵) (c : 𝒰' ⥤ 𝒰) (hc : c ⋙ p𝒰 = p𝒰')
    (hp𝒰 : p𝒰.IsFiberedInGroupoids) (hp𝒰' : p𝒰'.IsFiberedInGroupoids)
    (hce : c.IsEquivalence) (hq : q ⋙ p𝒵 = p𝒰) :
    (selfProdMap p𝒰 p𝒰' p𝒵 q c hc).IsEquivalence := by
  have h1 : (precomposeSnd (pT := p𝒰') (pℬ := p𝒵) (c ⋙ q) q c hc).IsEquivalence :=
    isEquivalence_precomposeSnd (pT := p𝒰') (pℬ := p𝒵) (G := c ⋙ q) (F := q) (a := c)
      hp𝒰' hp𝒰' hp𝒰 hc hq
  have h2 : (precomposeFst p𝒰' p𝒰 p𝒰 p𝒵 q q c hc).IsEquivalence :=
    isEquivalence_precomposeFst p𝒰' p𝒰 p𝒰 p𝒵 q q c hc hp𝒰 hp𝒰' hp𝒰 hce hq
  exact inferInstanceAs ((precomposeSnd (pT := p𝒰') (pℬ := p𝒵) (c ⋙ q) q c hc ⋙
    precomposeFst p𝒰' p𝒰 p𝒰 p𝒵 q q c hc).IsEquivalence)

/-- Reindexing the second leg of a 2-fibre product over `𝒞` along a 2-isomorphism is an
equivalence. -/
theorem isEquivalence_reindexSnd {p𝒳 : 𝒰 ⥤ 𝒞} {p𝒴 : 𝒰' ⥤ 𝒞} {p𝒮 : 𝒵 ⥤ 𝒞} {F : 𝒰 ⥤ 𝒵}
    {G G' : 𝒰' ⥤ 𝒵} (β : G ≅ G')
    (hβ : ∀ y : 𝒰', p𝒮.IsHomLift (𝟙 (p𝒴.obj y)) (β.hom.app y)) :
    (reindexSnd (p𝒳 := p𝒳) (F := F) β hβ).IsEquivalence :=
  (Equivalence.mk (reindexSnd (p𝒳 := p𝒳) (F := F) β hβ)
    (reindexSndSymm (p𝒳 := p𝒳) (F := F) β hβ)
    (reindexSndUnit (p𝒳 := p𝒳) (F := F) β hβ)
    (reindexSndCounit (p𝒳 := p𝒳) (F := F) β hβ)).isEquivalence_functor

/-- `c × c`, read on the self-product of a leg `q'` only 2-isomorphic to `c ⋙ q`: the two legs are
first moved to `c ⋙ q` by `CategoryTheory.TwoFibreProductOver.reindex` and
`CategoryTheory.TwoFibreProductOver.reindexSnd` along `γ`. -/
noncomputable def reindexedSelfProdMap (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒰' : 𝒰' ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (q : 𝒰 ⥤ 𝒵) (q' : 𝒰' ⥤ 𝒵) (c : 𝒰' ⥤ 𝒰) (hc : c ⋙ p𝒰 = p𝒰') (γ : q' ≅ c ⋙ q)
    (hγ : ∀ x : 𝒰', p𝒵.IsHomLift (𝟙 (p𝒰'.obj x)) (γ.hom.app x)) :
    TwoFibreProductOver p𝒰' p𝒰' p𝒵 q' q' ⥤ TwoFibreProductOver p𝒰 p𝒰 p𝒵 q q :=
  reindex (p𝒴 := p𝒰') (G := q') γ hγ ⋙
    reindexSnd (p𝒳 := p𝒰') (F := c ⋙ q) γ hγ ⋙ selfProdMap p𝒰 p𝒰' p𝒵 q c hc

/-- The reindexed `c × c` is strictly over `𝒞`. -/
@[simp] lemma reindexedSelfProdMap_comp_structureFunctor (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒰' : 𝒰' ⥤ 𝒞)
    (p𝒵 : 𝒵 ⥤ 𝒞) (q : 𝒰 ⥤ 𝒵) (q' : 𝒰' ⥤ 𝒵) (c : 𝒰' ⥤ 𝒰) (hc : c ⋙ p𝒰 = p𝒰')
    (γ : q' ≅ c ⋙ q)
    (hγ : ∀ x : 𝒰', p𝒵.IsHomLift (𝟙 (p𝒰'.obj x)) (γ.hom.app x)) :
    reindexedSelfProdMap p𝒰 p𝒰' p𝒵 q q' c hc γ hγ ⋙ structureFunctor p𝒰 p𝒰 p𝒵 q q =
      structureFunctor p𝒰' p𝒰' p𝒵 q' q' := rfl

/-- The reindexed `c × c` is an equivalence as soon as `c` is. -/
theorem isEquivalence_reindexedSelfProdMap (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒰' : 𝒰' ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (q : 𝒰 ⥤ 𝒵) (q' : 𝒰' ⥤ 𝒵) (c : 𝒰' ⥤ 𝒰) (hc : c ⋙ p𝒰 = p𝒰') (γ : q' ≅ c ⋙ q)
    (hγ : ∀ x : 𝒰', p𝒵.IsHomLift (𝟙 (p𝒰'.obj x)) (γ.hom.app x))
    (hp𝒰 : p𝒰.IsFiberedInGroupoids) (hp𝒰' : p𝒰'.IsFiberedInGroupoids)
    (hce : c.IsEquivalence) (hq : q ⋙ p𝒵 = p𝒰) :
    (reindexedSelfProdMap p𝒰 p𝒰' p𝒵 q q' c hc γ hγ).IsEquivalence := by
  have h1 : (reindex (p𝒴 := p𝒰') (G := q') γ hγ).IsEquivalence :=
    isEquivalence_reindex (p𝒳 := p𝒰') (p𝒴 := p𝒰') (G := q') γ hγ
  have h2 : (reindexSnd (p𝒳 := p𝒰') (F := c ⋙ q) γ hγ).IsEquivalence :=
    isEquivalence_reindexSnd (p𝒳 := p𝒰') (p𝒴 := p𝒰') (F := c ⋙ q) γ hγ
  have h3 : (selfProdMap p𝒰 p𝒰' p𝒵 q c hc).IsEquivalence :=
    isEquivalence_selfProdMap p𝒰 p𝒰' p𝒵 q c hc hp𝒰 hp𝒰' hce hq
  exact inferInstanceAs ((reindex (p𝒴 := p𝒰') (G := q') γ hγ ⋙
    reindexSnd (p𝒳 := p𝒰') (F := c ⋙ q) γ hγ ⋙ selfProdMap p𝒰 p𝒰' p𝒵 q c hc).IsEquivalence)

/-- `c × c` carries the relative diagonal of `q'` to the relative diagonal of `q`: the
component at `x` is the isomorphism of objects of `𝒰 ×_𝒵 𝒰` with both components `𝟙 (c x)`. -/
noncomputable def diagonalSelfProdIso (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒰' : 𝒰' ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (q : 𝒰 ⥤ 𝒵) (q' : 𝒰' ⥤ 𝒵) (c : 𝒰' ⥤ 𝒰) (hc : c ⋙ p𝒰 = p𝒰')
    (hq : q ⋙ p𝒵 = p𝒰) (hq' : q' ⋙ p𝒵 = p𝒰') (γ : q' ≅ c ⋙ q)
    (hγ : ∀ x : 𝒰', p𝒵.IsHomLift (𝟙 (p𝒰'.obj x)) (γ.hom.app x)) :
    diagonal (p𝒮 := p𝒰') (p𝒮' := p𝒵) (G := q') hq' ⋙
        reindexedSelfProdMap p𝒰 p𝒰' p𝒵 q q' c hc γ hγ ≅
      c ⋙ diagonal (p𝒮 := p𝒰) (p𝒮' := p𝒵) (G := q) hq := by
  refine NatIso.ofComponents (fun x => ?_) (fun {x y} u => ?_)
  · exact isoMkVertical (U := p𝒰'.obj x) (Iso.refl (c.obj x)) (Iso.refl (c.obj x))
      (IsHomLift.id (Functor.congr_obj hc x)) (IsHomLift.id (Functor.congr_obj hc x))
      (by simp [reindexedSelfProdMap, diagonal, reindex, reindexSnd, selfProdMap,
        precomposeSnd, precomposeFst, swap])
  · refine Hom.ext' ?_ ?_ <;>
    · change c.map u ≫ 𝟙 (c.obj y) = 𝟙 (c.obj x) ≫ c.map u
      simp

/-- Every component of `CategoryTheory.TwoFibreProductOver.diagonalSelfProdIso` is vertical. -/
theorem isHomLift_diagonalSelfProdIso (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒰' : 𝒰' ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (q : 𝒰 ⥤ 𝒵) (q' : 𝒰' ⥤ 𝒵) (c : 𝒰' ⥤ 𝒰) (hc : c ⋙ p𝒰 = p𝒰')
    (hq : q ⋙ p𝒵 = p𝒰) (hq' : q' ⋙ p𝒵 = p𝒰') (γ : q' ≅ c ⋙ q)
    (hγ : ∀ x : 𝒰', p𝒵.IsHomLift (𝟙 (p𝒰'.obj x)) (γ.hom.app x)) (x : 𝒰') :
    (structureFunctor p𝒰 p𝒰 p𝒵 q q).IsHomLift (𝟙 (p𝒰'.obj x))
      ((diagonalSelfProdIso p𝒰 p𝒰' p𝒵 q q' c hc hq hq' γ hγ).hom.app x) := by
  exact structureFunctor_isHomLift _ (𝟙 (p𝒰'.obj x)) (IsHomLift.id (Functor.congr_obj hc x))

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section SelfProd

variable {𝒰 𝒰' : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
  {𝒵 : CatFiberedInGroupoids.{u, v', u + 1, w'} (BigFppfOver B S hS)}

/-- The self-product comparison `c × c` of two 1-morphisms to one target whose sources are
identified by an equivalence `c` over the big fppf site of `S`, as a 1-morphism of categories
fibred in groupoids. -/
noncomputable def selfProdComparison (q : 𝒰.val ⥤ᵇ 𝒵.val) (q' : 𝒰'.val ⥤ᵇ 𝒵.val)
    (c : 𝒰'.val ⥤ᵇ 𝒰.val) (γ : BasedFunctor.comp c q ≅ q') :
    (twoFibreProduct B S hS 𝒵 𝒰' 𝒰' q' q').val ⥤ᵇ
      (twoFibreProduct B S hS 𝒵 𝒰 𝒰 q q).val where
  toFunctor := TwoFibreProductOver.reindexedSelfProdMap 𝒰.val.p 𝒰'.val.p 𝒵.val.p
    q.toFunctor q'.toFunctor c.toFunctor c.w
    (((BasedNatTrans.forgetful 𝒰'.val 𝒵.val).mapIso γ).symm) (fun x => γ.inv.isHomLift' x)
  w := by rfl

/-- The self-product comparison is an equivalence as soon as `c` is. -/
theorem isEquivalence_selfProdComparison (q : 𝒰.val ⥤ᵇ 𝒵.val) (q' : 𝒰'.val ⥤ᵇ 𝒵.val)
    (c : 𝒰'.val ⥤ᵇ 𝒰.val) (γ : BasedFunctor.comp c q ≅ q')
    (hc : Functor.IsEquivalence c.toFunctor) :
    Functor.IsEquivalence (selfProdComparison B S hS q q' c γ).toFunctor :=
  TwoFibreProductOver.isEquivalence_reindexedSelfProdMap 𝒰.val.p 𝒰'.val.p 𝒵.val.p
    q.toFunctor q'.toFunctor c.toFunctor c.w
    (((BasedNatTrans.forgetful 𝒰'.val 𝒵.val).mapIso γ).symm) (fun x => γ.inv.isHomLift' x)
    𝒰.isFiberedInGroupoids 𝒰'.isFiberedInGroupoids hc q.w

/-- The 2-commutative square of relative diagonals whose horizontal 1-morphisms are the
equivalence `c` and the self-product comparison `c × c`. -/
noncomputable def relativeDiagonalSelfProdIso (q : 𝒰.val ⥤ᵇ 𝒵.val) (q' : 𝒰'.val ⥤ᵇ 𝒵.val)
    (c : 𝒰'.val ⥤ᵇ 𝒰.val) (γ : BasedFunctor.comp c q ≅ q') :
    BasedFunctor.comp c (relativeDiagonalBasedFunctor B S hS 𝒰 𝒵 q) ≅
      BasedFunctor.comp (relativeDiagonalBasedFunctor B S hS 𝒰' 𝒵 q')
        (selfProdComparison B S hS q q' c γ) :=
  (BasedNatIso.mkNatIso
    (TwoFibreProductOver.diagonalSelfProdIso 𝒰.val.p 𝒰'.val.p 𝒵.val.p q.toFunctor q'.toFunctor
      c.toFunctor c.w q.w q'.w
      (((BasedNatTrans.forgetful 𝒰'.val 𝒵.val).mapIso γ).symm) (fun x => γ.inv.isHomLift' x))
    (TwoFibreProductOver.isHomLift_diagonalSelfProdIso 𝒰.val.p 𝒰'.val.p 𝒵.val.p q.toFunctor
      q'.toFunctor c.toFunctor c.w q.w q'.w
      (((BasedNatTrans.forgetful 𝒰'.val 𝒵.val).mapIso γ).symm)
      (fun x => γ.inv.isHomLift' x))).symm

end SelfProd

section Invariance

variable {𝒰 𝒰' 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- The isomorphism of 1-morphisms of categories fibred in groupoids underlying a 2-isomorphism of
1-morphisms of algebraic stacks. -/
def algStackHomIso {f g : 𝒰 ⟶ 𝒵} (e : f ≅ g) : f.hom ≅ g.hom where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.hom_inv_id
  inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.inv_hom_id

/-- The isomorphism of based functors underlying a 2-isomorphism of 1-morphisms of algebraic
stacks. -/
def algStackHomHomIso {f g : 𝒰 ⟶ 𝒵} (e : f ≅ g) : f.hom.hom ≅ g.hom.hom :=
  twoIsoHomIso B S hS (algStackHomIso B S hS e)

/-- The comparison 1-morphism between two 2-fibre products, in the 2-category of algebraic
stacks, of one cospan is an equivalence of the underlying categories. -/
theorem isEquivalence_of_isTwoFibreProduct_algebraicStacks {f : 𝒰 ⟶ 𝒵} {g : 𝒰' ⟶ 𝒵}
    {P Q : Bicategory.TwoCommSq f g} (hP : Bicategory.IsTwoFibreProduct P)
    (hQ : Bicategory.IsTwoFibreProduct Q) (a : Bicategory.TwoCommSq.PreHom P Q) :
    a.hom.hom.hom.toFunctor.IsEquivalence := by
  let b := _root_.Quotient.out (hP.from Q)
  obtain ⟨e₁, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (a.comp b) (.id P) :=
    _root_.Quotient.exact (hP.hom_ext (_root_.Quotient.mk _ (a.comp b)) (𝟙 P))
  obtain ⟨e₂, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (b.comp a) (.id Q) :=
    _root_.Quotient.exact (hQ.hom_ext (_root_.Quotient.mk _ (b.comp a)) (𝟙 Q))
  exact (CategoryTheory.Equivalence.mk a.hom.hom.hom.toFunctor b.hom.hom.hom.toFunctor
    (CatFiberedInGroupoids.underlyingIso (algStackHomIso B S hS e₁)).symm
    (CatFiberedInGroupoids.underlyingIso (algStackHomIso B S hS e₂))).isEquivalence_functor

namespace AlgebraicStacks

/-- The quasi-DM condition is invariant under an equivalence `c` of the source: if `q` is
quasi-DM and `c ⋙ q ≅ q'`, then `q'` is quasi-DM. -/
theorem isQuasiDM_of_equivalence (q : 𝒰 ⟶ 𝒵) (q' : 𝒰' ⟶ 𝒵)
    (c : 𝒰'.val.val ⥤ᵇ 𝒰.val.val) (γ : BasedFunctor.comp c q.hom.hom ≅ q'.hom.hom)
    (hc : Functor.IsEquivalence c.toFunctor) (h : IsQuasiDM B S hS q) :
    IsQuasiDM B S hS q' := by
  have := isEquivalence_selfProdComparison B S hS q.hom.hom q'.hom.hom c γ hc
  exact relativeProperty_of_equivalences B S hS
    (fun _ _ k => Space.IsLocallyQuasiFinite B S hS k.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰'.val 𝒵.val q'.hom.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰.val 𝒵.val q.hom.hom)
    c (selfProdComparison B S hS q.hom.hom q'.hom.hom c γ)
    (relativeDiagonalSelfProdIso B S hS q.hom.hom q'.hom.hom c γ) h

/-- Separatedness is invariant under an equivalence `c` of the source: if `q` is separated and
`c ⋙ q ≅ q'`, then `q'` is separated. -/
theorem isSeparated_of_equivalence (q : 𝒰 ⟶ 𝒵) (q' : 𝒰' ⟶ 𝒵)
    (c : 𝒰'.val.val ⥤ᵇ 𝒰.val.val) (γ : BasedFunctor.comp c q.hom.hom ≅ q'.hom.hom)
    (hc : Functor.IsEquivalence c.toFunctor) (h : IsSeparated B S hS q) :
    IsSeparated B S hS q' := by
  have := isEquivalence_selfProdComparison B S hS q.hom.hom q'.hom.hom c γ hc
  exact relativeProperty_of_equivalences B S hS
    (fun _ _ k => Space.IsProper B S hS k.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰'.val 𝒵.val q'.hom.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰.val 𝒵.val q.hom.hom)
    c (selfProdComparison B S hS q.hom.hom q'.hom.hom c γ)
    (relativeDiagonalSelfProdIso B S hS q.hom.hom q'.hom.hom c γ) h

/-- Quasi-separatedness is invariant under an equivalence `c` of the source: if `q` is
quasi-separated and `c ⋙ q ≅ q'`, then `q'` is quasi-separated. -/
theorem isQuasiSeparated_of_equivalence (q : 𝒰 ⟶ 𝒵) (q' : 𝒰' ⟶ 𝒵)
    (c : 𝒰'.val.val ⥤ᵇ 𝒰.val.val) (γ : BasedFunctor.comp c q.hom.hom ≅ q'.hom.hom)
    (hc : Functor.IsEquivalence c.toFunctor) (h : IsQuasiSeparated B S hS q) :
    IsQuasiSeparated B S hS q' := by
  obtain ⟨hqc, hqs⟩ := h
  have := isEquivalence_selfProdComparison B S hS q.hom.hom q'.hom.hom c γ hc
  have key := fun P => relativeProperty_of_equivalences B S hS P
    (relativeDiagonalBasedFunctor B S hS 𝒰'.val 𝒵.val q'.hom.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰.val 𝒵.val q.hom.hom)
    c (selfProdComparison B S hS q.hom.hom q'.hom.hom c γ)
    (relativeDiagonalSelfProdIso B S hS q.hom.hom q'.hom.hom c γ)
  exact ⟨key (fun _ _ k => Space.IsQuasiCompact B S hS k.hom) hqc,
    key (fun _ _ k => Space.IsQuasiSeparated B S hS k.hom) hqs⟩

end AlgebraicStacks

end Invariance

section BaseChange

variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

namespace AlgebraicStacks

/-- A property of 1-morphisms invariant under equivalence of the source and holding for the
canonical base change holds for the second projection of any 2-fibre product. -/
private theorem snd_of_isTwoFibreProduct_of_equivalence
    (Pr : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}, (𝒳 ⟶ 𝒴) → Prop)
    (hPr : ∀ {𝒰 𝒰' 𝒵 : AlgebraicStacks.{u, w} B S hS} (q : 𝒰 ⟶ 𝒵) (q' : 𝒰' ⟶ 𝒵)
      (c : 𝒰'.val.val ⥤ᵇ 𝒰.val.val) (_ : BasedFunctor.comp c q.hom.hom ≅ q'.hom.hom),
      Functor.IsEquivalence c.toFunctor → Pr q → Pr q')
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (h : Pr (twoFibreProductSquare B S hS f g).snd) : Pr R.snd := by
  have hQ := isTwoFibreProduct_twoFibreProductSquare B S hS f g
  let d : Bicategory.TwoCommSq.PreHom R (twoFibreProductSquare B S hS f g) :=
    _root_.Quotient.out (hQ.from R)
  exact hPr _ R.snd d.hom.hom.hom (algStackHomHomIso B S hS d.isoSnd.symm)
    (isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hR hQ d) h

/-- The second projection of any 2-fibre product of the cospan `(f, g)` is quasi-DM as soon as
`f` is. -/
theorem isQuasiDM_baseChange_of_isTwoFibreProduct (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsQuasiDM B S hS f) : IsQuasiDM B S hS R.snd :=
  snd_of_isTwoFibreProduct_of_equivalence B S hS (IsQuasiDM B S hS)
    (isQuasiDM_of_equivalence B S hS) f g R hR (isQuasiDM_baseChange B S hS f g hf)

/-- The second projection of any 2-fibre product of the cospan `(f, g)` is separated as soon as
`f` is. -/
theorem isSeparated_baseChange_of_isTwoFibreProduct (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsSeparated B S hS f) : IsSeparated B S hS R.snd :=
  snd_of_isTwoFibreProduct_of_equivalence B S hS (IsSeparated B S hS)
    (isSeparated_of_equivalence B S hS) f g R hR (isSeparated_baseChange B S hS f g hf)

/-- The second projection of any 2-fibre product of the cospan `(f, g)` is quasi-separated as
soon as `f` is. -/
theorem isQuasiSeparated_baseChange_of_isTwoFibreProduct (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsQuasiSeparated B S hS f) : IsQuasiSeparated B S hS R.snd :=
  snd_of_isTwoFibreProduct_of_equivalence B S hS (IsQuasiSeparated B S hS)
    (isQuasiSeparated_of_equivalence B S hS) f g R hR (isQuasiSeparated_baseChange B S hS f g hf)

end AlgebraicStacks

end BaseChange

end AlgebraicGeometry.Stack

end
