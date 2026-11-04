module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TerminalAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE

/-!
# Quasi-coherent modules on the algebraic stack of an affine scheme

Let `U` be a scheme over `S` with an isomorphism `e : U ≅ Spec R`, and let `(Sch/U)_{fppf}` be its
big fppf site, viewed as an algebraic stack over `S`
(`AlgebraicGeometry.Stack.schemeSliceStack`). Its tautological point, the final object
`U → U`, lies over `Spec R`, and the pullback to it
`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback` is a functor of symmetric monoidal
categories `QCoh(𝒪_U) ⥤ Mod_R`. This file proves that it is an equivalence: **`QCoh` of an
affine scheme is the symmetric monoidal category of modules over its ring of functions**, the
identification `QCoh(𝒪_{Spec R}) = Mod_R` of Stacks 0GRR.

More generally the pullback to a point over `Spec R` which is a final object of the algebraic
stack is an equivalence, by
`AlgebraicGeometry.FibredSite.isEquivalence_quasicoherentEvaluation_of_isTerminal`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.preservesColimitsOfSize_pointPullback`: the pullback to
  any point over an affine scheme commutes with colimits.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_pointPullback_of_isTerminal`: the
  pullback to a final point over an affine scheme is an equivalence.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_pointPullback_schemeSliceStack`:
  **`QCoh(𝒪_U) ≌ Mod_R` for `U ≅ Spec R`**, through the pullback to the tautological point, which
  is a braided monoidal functor (`pointPullbackBraided`) and so a symmetric monoidal equivalence.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GRR](https://stacks.math.columbia.edu/tag/0GRR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) {x : 𝒳.val.val.obj} {R : Type u} [CommRing R]
  (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))

/-- The pullback of quasi-coherent modules to a point over `Spec R` commutes with colimits. -/
theorem preservesColimitsOfSize_pointPullback :
    PreservesColimitsOfSize.{u, u} (pointPullback B S hS 𝒳 x e) := by
  have h₁ := FibredSite.preservesColimitsOfSize_quasicoherentEvaluation B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (isAffine_point B S hS 𝒳 x e)
  have h₂ : PreservesColimitsOfSize.{u, u}
      (ModuleCat.restrictScalars.{u} (pointRingHom B S hS 𝒳 x e)) :=
    (ModuleCat.restrictCoextendScalarsAdj (pointRingHom B S hS 𝒳 x e)).leftAdjoint_preservesColimits
  exact @comp_preservesColimits _ _ _ _ _ _ _
    (ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e)) h₁ h₂

/-- The pullback of quasi-coherent modules to a final point over `Spec R` is an equivalence
`QCoh(𝒪_𝒳) ≌ Mod_R`. -/
theorem isEquivalence_pointPullback_of_isTerminal (hx : IsTerminal x) :
    (pointPullback B S hS 𝒳 x e).IsEquivalence := by
  have h₁ := FibredSite.isEquivalence_quasicoherentEvaluation_of_isTerminal B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hx (isAffine_point B S hS 𝒳 x e)
  have h₂ : (ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e)).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (RingEquiv.ofBijective _ (bijective_pointRingHom B S hS 𝒳 x e))).isEquivalence_functor
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _
    (ModuleCat.restrictScalars (pointRingHom B S hS 𝒳 x e)) h₁ h₂

/-- **Quasi-coherent modules on an affine scheme are modules over its ring of functions.** For a
scheme `U` over `S` and an isomorphism `e` of `U` with `Spec R` (written at the image of the
tautological point `U → U`), the pullback to that point of the big fppf site of `U`, viewed as an
algebraic stack, is an equivalence `QCoh(𝒪_U) ≌ Mod_R`; it is a braided monoidal functor
(`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackBraided`), so this is an equivalence of
symmetric monoidal categories. -/
theorem isEquivalence_pointPullback_schemeSliceStack (U : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj
      ((schemeSliceStack.{u, w} B S hS U).val.val.p.obj (Over.mk (𝟙 U.left))) ≅
        Spec (CommRingCat.of R)) :
    (pointPullback B S hS (schemeSliceStack.{u, w} B S hS U) (Over.mk (𝟙 U.left))
      e).IsEquivalence :=
  isEquivalence_pointPullback_of_isTerminal B S hS (schemeSliceStack.{u, w} B S hS U) e
    Over.mkIdTerminal

end AlgebraicGeometry.Stack.AlgebraicStacks
