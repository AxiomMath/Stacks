module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphismSupplement
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
import all StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProduct
import all StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects

/-!
# Supplement to `LimitPreservingProduct`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingProduct`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `isLimitPreservingOverTerminal_of_descentObj`
* `isLimitPreservingOverTerminal_product`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w uC vC vI wI v₂ u₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-! ### The self-product at free universes -/

/-- **Bare descent of objects over every affine inverse limit gives limit preservation over the
terminal object.** The two conditions differ only in that Stacks 06CU asks for a stage dominating
a prescribed index and for a comparison in the target. The first is supplied by cofilteredness of
the index category, through `Deformation.Artin.descentObj_at_stage`; the second is forced, the
target of the structure morphism being the site itself. This is the converse of
`AlgebraicGeometry.Stack.descentObj_of_isLimitPreservingOverTerminal`, and like it leaves the
universes of `𝒴` free, because neither condition names the target as an object of the
2-category. -/
theorem isLimitPreservingOverTerminal_of_descentObj
    (𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, u₂} (BigFppfOver B S hS))
    (h : ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
      (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
      IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      Deformation.Artin.DescentObj 𝒴.val.p (D ⋙ BigAffineFppf.inclusion B S hS)
        ((BigAffineFppf.inclusion B S hS).mapCone c)) :
    IsLimitPreservingOverTerminal.{u, v, w} B S hS 𝒴 := by
  intro I _ _ D c hc i y x γ hγ
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  obtain ⟨k, s, xk, δ, hδ⟩ :=
    Deformation.Artin.descentObj_at_stage 𝒴.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) (h I D c hc) x i
  have hδ' := hδ
  have hδSC : 𝒴.val.p.IsStronglyCartesian
      (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k) δ :=
    𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  have hβ : 𝒴.val.p.IsHomLift
      (𝟙 ((BigAffineFppf.inclusion B S hS).mapCone c).pt) (𝟙 x.1) :=
    IsHomLift.of_fac' 𝒴.val.p _ _ x.2 x.2 (by simp)
  exact exists_descent_datum_of_descent 𝒴.val.p
    (D ⋙ BigAffineFppf.inclusion B S hS)
    ((BigAffineFppf.inclusion B S hS).mapCone c) i y x γ hγ k s xk x δ (𝟙 x.1)
    hδSC hβ inferInstance

/-- **The structure morphism of the self-product of a limit preserving category fibred in
groupoids is limit preserving over the terminal object, at free universes for `𝒴`.**

This is the content of Stacks 07XM, part (1), for `𝒴 × 𝒴`, in the form that does not name the
target as an object of the 2-category.
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_product` states the same thing
through a 1-morphism to `AlgebraicGeometry.Stack.terminalCFG`, which forces `𝒴` into the universes
of the site; the 2-fibre product of `𝒴` with itself over the site is formed from the structure
functor of `𝒴` alone, so no such restriction is needed. An object of `𝒴 × 𝒴` over the cone point is
a pair of objects of `𝒴` there together with a vertical comparison of their bases, and descending
it is descending the two components, which is `Deformation.Artin.descentObj_twoFibreProduct` over
the identity functor of the site. -/
theorem isLimitPreservingOverTerminal_product
    (𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, u₂} (BigFppfOver B S hS))
    (h𝒴 : Deformation.Artin.IsLimitPreserving.{u, v, w, u₂, v₂} B S hS 𝒴) :
    IsLimitPreservingOverTerminal.{u, v, w} B S hS
      (CatFiberedInGroupoids.product 𝒴 𝒴) := by
  apply isLimitPreservingOverTerminal_of_descentObj
  intro I _ _ D c hc
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let : Functor.IsFibered (𝟭 (BigFppfOver B S hS)) :=
    Functor.isFiberedInGroupoids_id.isFibered
  let := h𝒴 I D c hc
  let : (Deformation.Artin.colimitComparison (𝟭 (BigFppfOver B S hS))
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).Full :=
    (isLimitPreserving_terminalCFG.{u, v, w} B S hS I D c hc).full
  have hobj : Deformation.Artin.DescentObj 𝒴.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentObj_of_essSurj 𝒴.val.p _ _
  exact Deformation.Artin.descentObj_twoFibreProduct 𝒴.val.p
    (𝟭 (BigFppfOver B S hS)) 𝒴.val.p Functor.isFiberedInGroupoids_id
    𝒴.val.p 𝒴.val.p (Functor.comp_id _) (Functor.comp_id _)
    (D ⋙ BigAffineFppf.inclusion B S hS)
    ((BigAffineFppf.inclusion B S hS).mapCone c) hobj hobj

end AlgebraicGeometry.Stack

end
