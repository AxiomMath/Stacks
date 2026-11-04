module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The target square of clause (1) of Stacks 0D2Z, read over a second spelling of the site

Clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)` is pasted from three squares;
the third, the **target square**, reads
`(w^*(e ≫ i) ≫ τ ≫ c^*χ ≫ ρ) ≫ (Θ₁^a ≫ Θ₂^a) ≫ T = w^*b`,
where `w^*(e ≫ i) ≫ τ ≫ c^*χ ≫ ρ` is the source identification, `Θ₁`, `Θ₂` are the two factors of
the right-hand side of the middle square (maps of quasi-coherent modules on the scheme `W`, read
as modules on the represented algebraic space through Stacks 03DX (2)) and `T` is the
identification of the target of the chart map.

The square is proved with every functor and comparison over the site of `s`, while the point
identity consumes it over the site of `s.shrink`: the two are the same site by definition but not
syntactically, and the kernel compares two spellings of one morphism by unfolding both.  This file
proves, at variables over two sites `B₁ = B₂`, that the square over `B₁` gives the square over
`B₂` for heterogeneously equal leaves; each leaf is then compared in its own lemma by `subst`.

## Main results

* `…InvertibleTwistingRestriction.targetSquare_of_site_heq`: **the target square, at variables,
  read over a second spelling of the site.**

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

section Generic

/-- **The target square of clause (1) of Stacks 0D2Z, read over a second spelling of the site.**
Over a site `B`, let `W` be an object of the big fppf site, `p : W ⟶ U` and `c : W ⟶ F` morphisms
of algebraic spaces out of the represented space, and
`K = p^*(e ≫ i) ≫ τ ≫ c^*χ ≫ ρ : p^*G ⟶ A^a`, for `A^a` the module attached to a quasi-coherent
module `A` on `W`, let `Θ₁ : A ⟶ C`, `Θ₂ : C ⟶ D` be maps of quasi-coherent modules on `W`,
`T : D^a ⟶ p^*I` and `b : G ⟶ I`.  If the square `K ≫ (Θ₁^a ≫ Θ₂^a) ≫ T = p^*b` holds over
`B₁`, it holds over `B₂ = B₁` for heterogeneously equal leaves. -/
theorem targetSquare_of_site_heq {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {W₁ : BigFppfOver B₁ S₁ hS₁} {U₁ F₁ : AlgebraicSpaces B₁ S₁ hS₁}
    {p₁ : yonedaSpace B₁ S₁ hS₁ W₁ ⟶ U₁}
    {c₁ : (⟨yoneda.obj W₁, isAlgebraicSpace_yoneda B₁ S₁ hS₁ W₁⟩ : AlgebraicSpaces B₁ S₁ hS₁) ⟶ F₁}
    {G₁ M₁ N₁ I₁ : Modules.{u, u} B₁ S₁ hS₁ U₁.1 U₁.2} {Z₁ Z₁' : Modules.{u, u} B₁ S₁ hS₁ F₁.1 F₁.2}
    {A₁ C₁ D₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj W₁).ringCatSheaf).FullSubcategory}
    {e₁ : G₁ ⟶ M₁} {i₁ : M₁ ⟶ N₁}
    {τ₁ : (modulePullback B₁ S₁ hS₁ p₁).obj N₁ ⟶ (modulePullback B₁ S₁ hS₁ c₁).obj Z₁}
    {χ₁ : Z₁ ⟶ Z₁'}
    {ρ₁ : (modulePullback B₁ S₁ hS₁ c₁).obj Z₁' ⟶
      ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ W₁).functor.obj A₁).obj}
    {θ₁ : A₁ ⟶ C₁} {θ₁' : C₁ ⟶ D₁}
    {T₁ : ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ W₁).functor.obj D₁).obj ⟶
      (modulePullback B₁ S₁ hS₁ p₁).obj I₁}
    {b₁ : G₁ ⟶ I₁}
    (H : ((modulePullback B₁ S₁ hS₁ p₁).map (e₁ ≫ i₁) ≫ τ₁ ≫
          (modulePullback B₁ S₁ hS₁ c₁).map χ₁ ≫ ρ₁) ≫
        (((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ W₁).functor.map θ₁).hom ≫
          ((representedQuasicoherentSchemeEquivalence B₁ S₁ hS₁ W₁).functor.map θ₁').hom) ≫
        T₁ = (modulePullback B₁ S₁ hS₁ p₁).map b₁)
    {W₂ : BigFppfOver B₂ S₂ hS₂} {U₂ F₂ : AlgebraicSpaces B₂ S₂ hS₂}
    {p₂ : yonedaSpace B₂ S₂ hS₂ W₂ ⟶ U₂}
    {c₂ : (⟨yoneda.obj W₂, isAlgebraicSpace_yoneda B₂ S₂ hS₂ W₂⟩ : AlgebraicSpaces B₂ S₂ hS₂) ⟶ F₂}
    {G₂ M₂ N₂ I₂ : Modules.{u, u} B₂ S₂ hS₂ U₂.1 U₂.2} {Z₂ Z₂' : Modules.{u, u} B₂ S₂ hS₂ F₂.1 F₂.2}
    {A₂ C₂ D₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj W₂).ringCatSheaf).FullSubcategory}
    {e₂ : G₂ ⟶ M₂} {i₂ : M₂ ⟶ N₂}
    {τ₂ : (modulePullback B₂ S₂ hS₂ p₂).obj N₂ ⟶ (modulePullback B₂ S₂ hS₂ c₂).obj Z₂}
    {χ₂ : Z₂ ⟶ Z₂'}
    {ρ₂ : (modulePullback B₂ S₂ hS₂ c₂).obj Z₂' ⟶
      ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ W₂).functor.obj A₂).obj}
    {θ₂ : A₂ ⟶ C₂} {θ₂' : C₂ ⟶ D₂}
    {T₂ : ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ W₂).functor.obj D₂).obj ⟶
      (modulePullback B₂ S₂ hS₂ p₂).obj I₂}
    {b₂ : G₂ ⟶ I₂}
    (hW : HEq W₁ W₂) (hU : HEq U₁ U₂) (hF : HEq F₁ F₂) (hp : HEq p₁ p₂) (hc : HEq c₁ c₂)
    (hG : HEq G₁ G₂) (hM : HEq M₁ M₂) (hN : HEq N₁ N₂) (hI : HEq I₁ I₂) (hZ : HEq Z₁ Z₂)
    (hZ' : HEq Z₁' Z₂') (hA : HEq A₁ A₂) (hC : HEq C₁ C₂) (hD : HEq D₁ D₂)
    (he : HEq e₁ e₂) (hi : HEq i₁ i₂) (hτ : HEq τ₁ τ₂) (hχ : HEq χ₁ χ₂) (hρ : HEq ρ₁ ρ₂)
    (hθ : HEq θ₁ θ₂) (hθ' : HEq θ₁' θ₂') (hT : HEq T₁ T₂) (hb : HEq b₁ b₂) :
    ((modulePullback B₂ S₂ hS₂ p₂).map (e₂ ≫ i₂) ≫ τ₂ ≫
          (modulePullback B₂ S₂ hS₂ c₂).map χ₂ ≫ ρ₂) ≫
        (((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ W₂).functor.map θ₂).hom ≫
          ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ W₂).functor.map θ₂').hom) ≫
        T₂ = (modulePullback B₂ S₂ hS₂ p₂).map b₂ := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hW hU hF
  subst hp hc hG hM hN hI hZ hZ' hA hC hD
  subst he hi hτ hχ hρ hθ hθ' hT hb
  exact H

end Generic

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction
