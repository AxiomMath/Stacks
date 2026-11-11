module

public import Mathlib.CategoryTheory.Sites.Over

/-! # Localizing a special cocontinuous functor

## Main results

* `DenseSubsiteOverSheafEquivalence`: an earlier packaging of the conclusions as a `Prop`,
  with the equivalences only asserted to exist; not a proof of anything.
* `sheafEquivOfIsDenseSubsite`: the right-vertical equivalence
  `Sheaf J A ≌ Sheaf K A` of the diagram of topoi.

The formalization of Stacks 03CH is
`CategoryTheory.Sites.LocalizedToposSquare.isSpecialCocontinuous_overPost_and_isEquivalence`, in
`StacksFrontier.CategoryTheory.Sites.Topos.LocalizedToposSquare`.
-/

@[expose] public section

open CategoryTheory

universe w v u v' u' w'

/-- A proposition packaging conclusions of Stacks 03CH; it is a definition, not a theorem,
and nothing here proves it.  It also only asserts that *some* equivalences of sheaf
categories exist, and says nothing about the square of topoi.  The formalization of
Stacks 03CH is `CategoryTheory.Sites.LocalizedToposSquare.isSpecialCocontinuous_overPost_and_isEquivalence`.

Let `(C, J)` and `(D, K)` be sites and let `u : C ⥤ D` be a *special
cocontinuous functor*, formalized in Mathlib as
`Functor.IsDenseSubsite J K u`.  Fix an object `U : C`.  Then:

1. The square of underlying site functors commutes:
   `Over.post u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u`.

2. The induced functor `Over.post u : Over U ⥤ Over (u.obj U)` is again
   a special cocontinuous functor for the localized topologies
   `J.over U` and `K.over (u.obj U)`.

3. Hence, for any target category `A` with the appropriate limits,
   both vertical arrows in the induced commutative diagram of sheaf
   categories are equivalences:
     `Sheaf J A ≌ Sheaf K A` (right vertical), and
     `Sheaf (J.over U) A ≌ Sheaf (K.over (u.obj U)) A` (left vertical).

The Prop below packages these conclusions. -/
def DenseSubsiteOverSheafEquivalence
    (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) (U : C)
    (A : Type w) [Category.{w'} A] : Prop :=
  Functor.IsDenseSubsite J K u →
    (∀ X : Dᵒᵖ, Limits.HasLimitsOfShape (StructuredArrow X u.op) A) →
    (∀ X : (Over (u.obj U))ᵒᵖ,
       Limits.HasLimitsOfShape (StructuredArrow X (Over.post (X := U) u).op) A) →
    -- (1) commutativity of the underlying site square
    (Over.post (X := U) u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u) ∧
    -- (2) the left vertical arrow is a special cocontinuous functor
    Nonempty
      (Functor.IsDenseSubsite (J.over U) (K.over (u.obj U))
        (Over.post (X := U) u)) ∧
    -- (3a) the right vertical arrow is an equivalence
    Nonempty (Sheaf J A ≌ Sheaf K A) ∧
    -- (3b) the left vertical arrow is an equivalence
    Nonempty (Sheaf (J.over U) A ≌ Sheaf (K.over (u.obj U)) A)

/-- The right-vertical equivalence in the Stacks 03CH diagram of topoi.

This is the direct corollary of Mathlib's
`Functor.IsDenseSubsite.sheafEquiv`: under the dense-subsite assumption on
`u : C ⥤ D` and the standard limit hypothesis on the target category `A`,
the morphism of topoi `Sh(C, J) → Sh(D, K)` is an equivalence. -/
noncomputable def sheafEquivOfIsDenseSubsite
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsDenseSubsite J K u]
    (A : Type w) [Category.{w'} A]
    [∀ X : Dᵒᵖ, Limits.HasLimitsOfShape (StructuredArrow X u.op) A] :
    Sheaf J A ≌ Sheaf K A :=
  Functor.IsDenseSubsite.sheafEquiv J K u A
