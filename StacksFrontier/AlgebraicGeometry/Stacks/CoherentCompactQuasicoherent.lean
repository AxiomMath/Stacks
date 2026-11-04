module

public import Mathlib.CategoryTheory.Presentable.Finite
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHomQuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianStack
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall

/-!
# Coherent modules are compact objects of `QCoh(𝒪_𝒳)` on a Noetherian algebraic stack

Let `𝒳` be a Noetherian algebraic stack (Stacks 0510). The proof of Stacks 0GRJ observes that
"coherent modules on locally Noetherian algebraic stacks are by definition modules of finite
presentation, see Cohomology of Stacks, Definition 0GR6. Hence a coherent module on `𝒳` is a
categorically compact object of `QCoh(𝒪_𝒳)` by Cohomology of Stacks, Lemma 0GQZ." This file
records that step, in Mathlib's language of finitely presentable objects (Stacks 0FWX).

## Main definitions

* `AlgebraicGeometry.Stack.coherentQuasicoherent`: the coherent `𝒪_𝒳`-modules (Stacks 0GR6) as
  a property of objects of `QCoh(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.isFinitelyPresentable_of_isCoherent`: a coherent module on a
  Noetherian algebraic stack is categorically compact in `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.locallySmall_sheafOfModules_algebraicStack`: the `𝒪_𝒳`-modules form a
  locally small category.

## Implementation notes

The structure sheaf over which `AlgebraicGeometry.Stack.Coh` is formed and the one over which
`QCoh(𝒪_𝒳)` is formed are equal on the nose
(`AlgebraicGeometry.FibredSite.ringStructureSheafCore_fppf_eq_stack`), so a quasi-coherent module
is coherent exactly when its underlying module is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u w w'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The coherent `𝒪_𝒳`-modules (Stacks 0GR6), as a property of quasi-coherent modules. -/
def coherentQuasicoherent :
    ObjectProperty (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :=
  fun M ↦ IsCoherent B S hS 𝒳 M.obj

/-- The `𝒪_𝒳`-modules of an algebraic stack form a locally small category: they are equivalent
to the sheaves of modules on the equi-universe model of the fppf ringed site. -/
instance locallySmall_sheafOfModules_algebraicStack :
    LocallySmall.{u} (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)) :=
  locallySmall_of_faithful.{u} (FibredSite.modulesEquivFppfModelModules B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids).functor

/-- The quasi-coherent `𝒪_𝒳`-modules of an algebraic stack form a locally small category. -/
instance locallySmall_quasicoherentModules_algebraicStack :
    LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :=
  locallySmall_of_faithful.{u} (ObjectProperty.ι _)

/-- The coherent `𝒪_𝒳`-modules of an algebraic stack form a locally small category. -/
instance locallySmall_coherentQuasicoherent :
    LocallySmall.{u} (coherentQuasicoherent B S hS 𝒳).FullSubcategory :=
  locallySmall_of_faithful.{u} (ObjectProperty.ι _)

/-- The hom functor out of a quasi-coherent module agrees with the hom functor out of its
underlying module, restricted to quasi-coherent modules. -/
noncomputable def coyonedaQuasicoherentIso
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι ⋙ coyoneda.obj (op M.obj) ≅ coyoneda.obj (op M) :=
  NatIso.ofComponents (fun N ↦ (ObjectProperty.fullyFaithfulι _).homEquiv.symm.toIso)
    (fun f ↦ by ext; rfl)

/-- **A coherent module on a Noetherian algebraic stack is a categorically compact object of
`QCoh(𝒪_𝒳)`** (the step "a coherent module on `𝒳` is a categorically compact object of
`QCoh(𝒪_𝒳)` by Lemma 0GQZ" of the proof of Stacks 0GRJ). -/
theorem isFinitelyPresentable_of_isCoherent (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)
    (hM : IsCoherent B S hS 𝒳 M.obj) : IsFinitelyPresentable.{u} M := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  refine ⟨fun K _ _ ↦ ⟨fun {D} ↦ ?_⟩⟩
  let := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have := isIso_colimit_post_hom_quasicoherent_of_isQuasiCompactStack B S hS 𝒳 h𝒳.1 h𝒳.2.1
    M.obj hM.2 D
  have := preservesColimit_of_isIso_post (F := D)
    (G := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).ι ⋙ coyoneda.obj (op M.obj))
  exact preservesColimit_of_natIso D (coyonedaQuasicoherentIso B S hS 𝒳 M)

/-- On a Noetherian algebraic stack, every coherent `𝒪_𝒳`-module is a finitely presentable
object of `QCoh(𝒪_𝒳)`. -/
theorem coherentQuasicoherent_le_isFinitelyPresentable
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳) :
    coherentQuasicoherent B S hS 𝒳 ≤ ObjectProperty.isFinitelyPresentable.{u} _ :=
  fun M hM ↦ isFinitelyPresentable_of_isCoherent B S hS 𝒳 h𝒳 M hM

end AlgebraicGeometry.Stack

end
