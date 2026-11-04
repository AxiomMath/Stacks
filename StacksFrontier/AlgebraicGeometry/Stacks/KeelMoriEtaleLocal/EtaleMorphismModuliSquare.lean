module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.KeelMoriTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.InertiaFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.ModuliPieces

/-!
# The Keel–Mori moduli space along an étale stabilizer preserving morphism (Stacks 0DUV)

Let `h : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks such that the inertia `I_𝒳 ⟶ 𝒳` is finite,
and `h` is étale, separated and induces isomorphisms between automorphism groups at every point
(Stacks 0DTW). Then the Keel–Mori moduli spaces `f : 𝒳 ⟶ M` and `f' : 𝒳' ⟶ M'` of Stacks 0DUT
exist and fit into a 2-cartesian square

```
𝒳' ---h---> 𝒳
 |f'         |f
 v           v
 M' ---g---> M
```

with `g` a separated étale morphism of algebraic spaces.

The proof follows the source. The inertia of `𝒳'` is finite
(`AlgebraicGeometry.Stack.isFinite_inertiaProjection_of_isEtale_of_inducesIsomorphismAt`, via
Stacks 0DU9), so Stacks 0DUT applies to both stacks; the moduli space of `𝒳` comes with the
well-nigh affine pieces it is built from
(`AlgebraicGeometry.Stack.exists_keelMoriModuliSpace_hasWellNighAffineModuliPieces`), and over
those pieces the square is checked to be cartesian with `g` separated and étale
(`AlgebraicGeometry.Stack.exists_isTwoFibreProduct_of_hasWellNighAffineModuliPieces`).

## Main results

* `AlgebraicGeometry.Stack.exists_isTwoFibreProduct_keelMoriModuliSpace_of_isEtale_of_isSeparated`:
  the Keel–Mori moduli spaces of `𝒳` and `𝒳'` exist and form a 2-cartesian square with `h`,
  whose bottom morphism `g : M' ⟶ M` is separated and étale.

## References

* [Stacks Project, Tag 0DUV](https://stacks.math.columbia.edu/tag/0DUV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DUV.** Let `h : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks. Assume that the
inertia `I_𝒳 ⟶ 𝒳` is finite, and that `h` is étale, separated, and induces isomorphisms between
automorphism groups at every point (Stacks 0DTW). Then there are moduli spaces `f : 𝒳 ⟶ M` and
`f' : 𝒳' ⟶ M'` as in Theorem 0DUT (uniform categorical moduli spaces which are separated,
quasi-compact and universal homeomorphisms) and a separated étale morphism `g : M' ⟶ M` of
algebraic spaces with `f' ≫ g = h ≫ f`, such that the square `𝒳' ⟶ 𝒳` over `g` is a 2-fibre
product. -/
@[stacks 0DUV]
theorem exists_isTwoFibreProduct_keelMoriModuliSpace_of_isEtale_of_isSeparated
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
    (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (he : IsEtale B S hS h) (hsep : AlgebraicStacks.IsSeparated B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q) :
    ∃ (M M' : AlgebraicSpaces B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
      (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS M'.obj M'.property) (g : M' ⟶ M)
      (hcomm : f'.hom ≫ (associatedMap B S hS g.hom).1 = h.hom ≫ f.hom),
      Space.IsEtale B S hS g.hom ∧ Space.IsSeparated B S hS g.hom ∧
      Nonempty (Bicategory.IsTwoFibreProduct
        (⟨𝒳'.val, f'.hom, h.hom, eqToIso hcomm⟩ :
          Bicategory.TwoCommSq (associatedMap B S hS g.hom).1 f.hom)) ∧
      (IsUniformCategoricalModuliSpace B S hS M f.hom ∧ AlgebraicStacks.IsSeparated B S hS f ∧
        IsQuasiCompactMorphism.{u, w} B S hS f ∧ UniversalHomeomorphism B S hS f) ∧
      (IsUniformCategoricalModuliSpace B S hS M' f'.hom ∧ AlgebraicStacks.IsSeparated B S hS f' ∧
        IsQuasiCompactMorphism.{u, w} B S hS f' ∧ UniversalHomeomorphism B S hS f') := by
  obtain ⟨M, f, hfu, hfs, hfq, hfh, hfp⟩ :=
    exists_keelMoriModuliSpace_hasWellNighAffineModuliPieces B S hS 𝒳 hI
  obtain ⟨M', f', hf'u, hf's, hf'q, hf'h⟩ :=
    exists_isUniformCategoricalModuliSpace_of_isFinite_inertia B S hS 𝒳'
      (isFinite_inertiaProjection_of_isEtale_of_inducesIsomorphismAt B S hS h he hauto hI)
  obtain ⟨g, hcomm, hgE, hgS, hcart⟩ :=
    exists_isTwoFibreProduct_of_hasWellNighAffineModuliPieces B S hS h he hsep hauto f f' hfh hfp
      hf'u hf'h
  exact ⟨M, M', f, f', g, hcomm, hgE, hgS, hcart, ⟨hfu, hfs, hfq, hfh⟩, ⟨hf'u, hf's, hf'q, hf'h⟩⟩

end AlgebraicGeometry.Stack

end
