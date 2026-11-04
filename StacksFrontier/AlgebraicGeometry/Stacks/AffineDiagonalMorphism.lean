module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineDiagonalPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties

/-!
# 1-morphisms of algebraic stacks with affine relative diagonal

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks *has affine diagonal* when its relative diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is affine in the sense of Properties of Stacks, Section 04XB
(`AlgebraicGeometry.Stack.IsAffineHom`). This file records the permanence of that condition used
by the proof of **Stacks 076Z**: it is invariant under an equivalence of the source, stable under
base change (along an arbitrary 2-fibre product square), and stable under composition.

The proofs are those of the separation axioms of **Stacks 04YW**
(`StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange`,
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance`,
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition`) at the property of being an affine
morphism of algebraic spaces; composition uses **Stacks 0CHS**
(`AlgebraicGeometry.Stack.isAffineHom_comp`) and the affine clause of **Stacks 050H**.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasAffineDiagonal`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasAffineDiagonal_of_equivalence`
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasAffineDiagonal_baseChange_of_isTwoFibreProduct`
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasAffineDiagonal_comp`
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks *has affine diagonal* when its relative diagonal is affine
in the sense of Properties of Stacks, Section 04XB. -/
abbrev HasAffineDiagonal {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  Stack.IsAffineHom B S hS
    (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)

section

variable {𝒰 𝒰' 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- **Affine diagonal is invariant under an equivalence of the source**, over a fixed target. -/
theorem hasAffineDiagonal_of_equivalence (q : 𝒰 ⟶ 𝒵) (q' : 𝒰' ⟶ 𝒵)
    (c : 𝒰'.val.val ⥤ᵇ 𝒰.val.val) (γ : BasedFunctor.comp c q.hom.hom ≅ q'.hom.hom)
    (hc : Functor.IsEquivalence c.toFunctor) (h : HasAffineDiagonal B S hS q) :
    HasAffineDiagonal B S hS q' := by
  have := isEquivalence_selfProdComparison B S hS q.hom.hom q'.hom.hom c γ hc
  exact relativeProperty_of_equivalences B S hS
    (fun _ _ k => Space.IsAffineHom B S hS k.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰'.val 𝒵.val q'.hom.hom)
    (relativeDiagonalBasedFunctor B S hS 𝒰.val 𝒵.val q.hom.hom)
    c (selfProdComparison B S hS q.hom.hom q'.hom.hom c γ)
    (relativeDiagonalSelfProdIso B S hS q.hom.hom q'.hom.hom c γ) h

end

variable {𝒳 𝒴 𝒴' 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- **Affine diagonal is stable under base change**, along the canonical 2-fibre product square:
the relative diagonal of the base change is a base change of `Δ_f` (**Stacks 04YR**). -/
theorem hasAffineDiagonal_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (hf : HasAffineDiagonal B S hS f) :
    HasAffineDiagonal B S hS (twoFibreProductSquare B S hS f g).snd :=
  prop_relativeDiagonal_baseChange B S hS (fun _ _ m => Space.IsAffineHom B S hS m.hom) f g hf

/-- **Affine diagonal is stable under base change**, along an arbitrary 2-fibre product
square. -/
theorem hasAffineDiagonal_baseChange_of_isTwoFibreProduct (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : HasAffineDiagonal B S hS f) : HasAffineDiagonal B S hS R.snd := by
  have hQ := isTwoFibreProduct_twoFibreProductSquare B S hS f g
  let d : Bicategory.TwoCommSq.PreHom R (twoFibreProductSquare B S hS f g) :=
    _root_.Quotient.out (hQ.from R)
  exact hasAffineDiagonal_of_equivalence B S hS
    (twoFibreProductSquare B S hS f g).snd R.snd d.hom.hom.hom
    (algStackHomHomIso B S hS d.isoSnd.symm)
    (isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hR hQ d)
    (hasAffineDiagonal_baseChange B S hS f g hf)

/-- **Affine diagonal is stable under composition.** `Δ_{f ≫ g} = Δ_f ≫ i` with `i` the
comparison 1-morphism `𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳`, a base change of `Δ_g` and so affine
(**Stacks 050H**), and affine 1-morphisms compose (**Stacks 0CHS**). -/
theorem hasAffineDiagonal_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : HasAffineDiagonal B S hS f)
    (hg : HasAffineDiagonal B S hS g) : HasAffineDiagonal B S hS (f ≫ g) := by
  have hfac : _root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val
        (f ≫ g).hom =
      (relativeDiagonal B S hS f).hom ≫ (mapBase B S hS f f g).hom := by
    rw [← Bicategory.InducedBicategory.bicategory_comp_hom]
    exact congrArg (fun q => q.hom) (relativeDiagonal_comp B S hS f g)
  change Stack.IsAffineHom B S hS
    (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val (f ≫ g).hom)
  rw [hfac]
  exact Stack.isAffineHom_comp B S hS _ _
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpaces_mapBase B S hS f f g) hf
    (prop_mapBase_of_prop_relativeDiagonal B S hS f f g
      (fun _ _ m => Space.IsAffineHom B S hS m.hom) hg)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
