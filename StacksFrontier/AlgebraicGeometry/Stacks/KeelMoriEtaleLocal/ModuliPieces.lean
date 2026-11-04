module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.LocalOnTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.GeometricPoints

/-!
# Moduli spaces built from well-nigh affine pieces, and the étale local nature of Stacks 0DUV

The Keel–Mori moduli space `f : 𝒳 ⟶ M` of Stacks 0DUT is built from pieces: étale morphisms
`Mⱼ ⟶ M`, jointly surjective, over which `f` is the moduli space of a well-nigh affine stack `𝒳ⱼ`
(Stacks 0DUP), the squares `𝒳ⱼ ⟶ 𝒳` over `Mⱼ ⟶ M` being cartesian. This file packages that
property as `AlgebraicGeometry.Stack.HasWellNighAffineModuliPieces` and proves the conclusion of
Stacks 0DUV for any `f` with it which is a universal homeomorphism, and any uniform categorical
moduli space `f' : 𝒳' ⟶ M'` which is a universal homeomorphism:

```
𝒳' ---h---> 𝒳
 |f'         |f
 v           v
 M' ---g---> M
```

is cartesian with `g` separated and étale, for `h` étale, separated and stabilizer preserving.

## Main definitions

* `AlgebraicGeometry.Stack.HasWellNighAffineModuliPieces`

## Main results

* `AlgebraicGeometry.Stack.exists_isTwoFibreProduct_of_hasWellNighAffineModuliPieces`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism to an algebraic space which is, étale locally on the target, the moduli space of
well-nigh affine stacks.** `f : 𝒳 ⟶ M` *has well-nigh affine moduli pieces* when there are étale
morphisms `bⱼ : Mⱼ ⟶ M` from objects of the site, jointly surjective on points, well-nigh affine
algebraic stacks `𝒳ⱼ` with 1-morphisms `gⱼ : 𝒳ⱼ ⟶ 𝒳`, and uniform categorical moduli spaces
`fⱼ : 𝒳ⱼ ⟶ Mⱼ`, such that each square `𝒳ⱼ ⟶ 𝒳` over `Mⱼ ⟶ M` commutes and is a 2-fibre product. -/
def HasWellNighAffineModuliPieces {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {M : AlgebraicSpaces B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property) :
    Prop :=
  ∃ (J : Type u) (𝒳j : J → AlgebraicStacks.{u, w} B S hS) (gj : ∀ j, 𝒳j j ⟶ 𝒳)
    (Mj : J → BigFppfOver B S hS)
    (fj : ∀ j, 𝒳j j ⟶
      algebraicSpaceStack.{u, w} B S hS (yoneda.obj (Mj j)) (isAlgebraicSpace_yoneda B S hS (Mj j)))
    (bj : ∀ j, (⟨yoneda.obj (Mj j), isAlgebraicSpace_yoneda B S hS (Mj j)⟩ :
      AlgebraicSpaces B S hS) ⟶ M)
    (hcommj : ∀ j, (fj j).hom ≫ (associatedMap B S hS (bj j).hom).1 = (gj j).hom ≫ f.hom),
    (∀ j, IsWellNighAffine.{u, w} B S hS (𝒳j j)) ∧
    (∀ j, IsUniformCategoricalModuliSpace B S hS
      ⟨yoneda.obj (Mj j), isAlgebraicSpace_yoneda B S hS (Mj j)⟩ (fj j).hom) ∧
    (∀ j, Space.IsEtale B S hS (bj j).hom) ∧
    (⋃ j, Set.range (Space.pointsMap B S hS (yoneda.obj (Mj j)) (bj j).hom)) = Set.univ ∧
    ∀ j, Nonempty (Bicategory.IsTwoFibreProduct
      (spaceModuliSquare B S hS (gj j) f (fj j) (bj j) (hcommj j)))

/-- **The étale local nature of the Keel–Mori moduli space** (Stacks 0DUV). Let
`h : 𝒳' ⟶ 𝒳` be étale, separated, and induce isomorphisms between automorphism groups at every
point (Stacks 0DTW). Let `f : 𝒳 ⟶ M` be a universal homeomorphism with well-nigh affine moduli
pieces, and `f' : 𝒳' ⟶ M'` a uniform categorical moduli space which is a universal homeomorphism.
Then there is a separated étale morphism `g : M' ⟶ M` of algebraic spaces with
`f' ≫ g = h ≫ f`, and the square is a 2-fibre product. -/
theorem exists_isTwoFibreProduct_of_hasWellNighAffineModuliPieces
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
    (he : IsEtale B S hS h) (hsep : AlgebraicStacks.IsSeparated B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q)
    {M M' : AlgebraicSpaces B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS M'.obj M'.property)
    (hf : UniversalHomeomorphism B S hS f) (hfp : HasWellNighAffineModuliPieces B S hS f)
    (hf' : IsUniformCategoricalModuliSpace B S hS M' f'.hom)
    (hf'u : UniversalHomeomorphism B S hS f') :
    ∃ (g : M' ⟶ M) (hcomm : f'.hom ≫ (associatedMap B S hS g.hom).1 = h.hom ≫ f.hom),
      Space.IsEtale B S hS g.hom ∧ Space.IsSeparated B S hS g.hom ∧
        Nonempty (Bicategory.IsTwoFibreProduct (spaceModuliSquare B S hS h f f' g hcomm)) := by
  obtain ⟨g, ⟨e⟩, -⟩ := (isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS hf')
    M (h.hom ≫ f.hom)
  have hcomm : f'.hom ≫ (associatedMap B S hS g.hom).1 = h.hom ≫ f.hom :=
    hom_eq_of_hom₂ B S hS e.hom
  obtain ⟨J, 𝒳j, gj, Mj, fj, bj, hcommj, hwna, hfj, hbj, hcover, hcart⟩ := hfp
  obtain ⟨hgE, hgS⟩ := isEtale_and_isSeparated_of_wellNighAffinePieces B S hS h f f' g hcomm he
    hsep hauto hf' 𝒳j gj hwna Mj fj hfj bj hbj hcover hcommj (fun j => (hcart j).some)
  exact ⟨g, hcomm, hgE, hgS,
    nonempty_isTwoFibreProduct_spaceModuliSquare_of_universalHomeomorphism h f f' g hcomm he
      hauto hgE hf hf'u⟩

end AlgebraicGeometry.Stack

end
