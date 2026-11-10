module

public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance

/-!
# The Deligne–Mumford condition is invariant under equivalence (Stacks 04YW, 050F)

`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_equivalence` and its two siblings transport
the quasi-DM, separated and quasi-separated conditions of **Stacks 04YW** along an equivalence of
the source, and `…isQuasiDM_baseChange_of_isTwoFibreProduct` and its two siblings then state
**Stacks 050F** at an arbitrary 2-fibre-product square rather than at the canonical one. This file
supplies the fourth member of each family, the Deligne–Mumford case.

The DM condition is, like the other three, a relative property of the *relative diagonal* — it is
the relative property of **Stacks 03YK** at unramifiedness of morphisms of algebraic spaces
(**Stacks 03ZH**, part (1)) — so the same comparison of the two self-products `𝒰' ×_𝒵 𝒰'` and
`𝒰 ×_𝒵 𝒰` carries it across, and the proofs are those of the quasi-DM siblings with
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` replaced by
`AlgebraicGeometry.Space.IsUnramified`. Nothing new is constructed here: the self-product
comparison `AlgebraicGeometry.Stack.selfProdComparison`, its equivalence witness and the natural
isomorphism `AlgebraicGeometry.Stack.relativeDiagonalSelfProdIso` identifying the two relative
diagonals are all taken from the module this one imports.

## Main results

* `AlgebraicGeometry.Stack.isDM_of_equivalence`: the DM condition of Stacks 04YW is invariant
  under an equivalence of the source.
* `AlgebraicGeometry.Stack.isDM_baseChange_of_isTwoFibreProduct`: Stacks 050F, the DM case, at an
  arbitrary 2-fibre-product square.

## Implementation notes

Neither declaration carries a `@[stacks]` attribute. The covering set of Stacks 050F is its four
keys at the canonical square — `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_baseChange` and its
three siblings, all registered — and the arbitrary-square forms are generalisations of those
statements rather than further assertions of the source, which is why the three other
arbitrary-square forms are untagged as well. The invariance statement is not an assertion of Stacks
04YW at all;
it is the vocabulary the arbitrary-square form is proved through.

`AlgebraicGeometry.Stack.IsDM` lives in the `AlgebraicGeometry.Stack` namespace rather than in
`AlgebraicGeometry.Stack.AlgebraicStacks`, where the other three conditions of Stacks 04YW live,
so these two declarations sit one namespace up from their siblings.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Invariance

variable {𝒰 𝒰' 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- **The Deligne–Mumford condition of Stacks 04YW is invariant under an equivalence of the
source.** The representability witness is Stacks 04XS part (1), which holds for every 1-morphism
of algebraic stacks and so is not transported; the relative quantifier is carried across by
Stacks 0457 for the relative property of Stacks 03YK at unramifiedness, applied to the
2-commutative square of relative diagonals whose horizontal 1-morphisms are `c` and `c × c`. -/
theorem isDM_of_equivalence (q : 𝒰 ⟶ 𝒵) (q' : 𝒰' ⟶ 𝒵)
    (c : 𝒰'.val.val ⥤ᵇ 𝒰.val.val) (γ : BasedFunctor.comp c q.hom.hom ≅ q'.hom.hom)
    (hc : Functor.IsEquivalence c.toFunctor) (h : IsDM B S hS q) :
    IsDM B S hS q' := by
  obtain ⟨-, hPq⟩ := h
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS q', ?_⟩
  have := isEquivalence_selfProdComparison B S hS q.hom.hom q'.hom.hom c γ hc
  exact relativeProperty_of_equivalences B S hS
    (fun _ _ k => Space.IsUnramified B S hS k.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰'.val 𝒵.val q'.hom.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰.val 𝒵.val q.hom.hom)
    c (selfProdComparison B S hS q.hom.hom q'.hom.hom c γ)
    (relativeDiagonalSelfProdIso B S hS q.hom.hom q'.hom.hom c γ) hPq

end Invariance

section BaseChange

variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 050F, the Deligne–Mumford case, at an arbitrary 2-fibre-product square.** The second
projection of *any* 2-fibre product of the cospan `(f, g)` is Deligne–Mumford as soon as `f` is:
it is compared with the second projection of the canonical square — which is
`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_baseChange` — by an equivalence of apexes, and the
DM condition is invariant under one. -/
theorem isDM_baseChange_of_isTwoFibreProduct (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsDM B S hS f) : IsDM B S hS R.snd := by
  have hQ := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS f g
  let d : Bicategory.TwoCommSq.PreHom R (AlgebraicStacks.twoFibreProductSquare B S hS f g) :=
    _root_.Quotient.out (hQ.from R)
  exact isDM_of_equivalence B S hS
    (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd R.snd d.hom.hom.hom
    (algStackHomHomIso B S hS d.isoSnd.symm)
    (isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hR hQ d)
    (AlgebraicStacks.isDM_baseChange B S hS f g hf)

end BaseChange

end AlgebraicGeometry.Stack

end
