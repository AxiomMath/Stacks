module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint

/-!
# Stalks and presheaf pushforward

A *point* of a category `C` is a functor `w : C ⥤ Type`, and the *stalk* of a presheaf of sets `F`
on `C` at `w` is `F_w = colim_{(U, x) ∈ el(w)ᵒᵖ} F(U)`, the colimit over the opposite of the
category of elements of `w` (Stacks 04EH). Stacks 0F4F says that stalks are compatible with the
presheaf pushforward: for a functor `u : C ⥤ D`, a point `v` of `D` and `w = v ∘ u`, one has
`(u_p F)_v = F_w`, functorially in the presheaf `F` on `C`.

The stalk is `PresheafPushforwardStalkAdjunction.presheafStalk`, the source's colimit; the
presheaf pushforward `u_p` is Mathlib's left Kan extension `Functor.lan u.op`, whose value at `V`
is by construction the colimit over `CostructuredArrow u.op (op V)`, i.e. over the pairs
`(W, V ⟶ u W)` — the colimit that the source uses to define `u_p` (see
`CategoryTheory.Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit`).

## Implementation

Rather than flattening an iterated colimit and checking a finality condition (the source's
"simple categorical fact"), the identification here comes from uniqueness of left adjoints. The
stalk functor at `w` has an explicit right adjoint, the pushforward `w^p : X ↦ (U ↦ (w(U) → X))`
(`PresheafPushforwardStalkAdjunction.adjunction`, Stacks 00Y7); `u_p` is left adjoint to
restriction along `u.op` (`Functor.lanAdjunction`); and restricting `v^p` along `u.op` *is*
`(u ⋙ v)^p`, since `(u ⋙ v)(U) = v(u(U))`. So `u_p` followed by the stalk at `v`, and the stalk
at `u ⋙ v`, are left adjoint to the same functor.

Everything is stated for small `C` and `D` and `Type u`-valued presheaves, the setting in which the
defining colimits exist.

## Main results

* `CategoryTheory.Stalk.presheafPushforwardStalkIso` and
  `CategoryTheory.Stalk.presheafPushforward_stalk_iso`: Stacks 0F4F.

Tags covered: 0F4F.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.Stalk

open PresheafPushforwardStalkAdjunction

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]

/-! ### Stacks 0F4F -/

/-- **Stacks 0F4F.** For a functor `u : C ⥤ D`, a point `v : D ⥤ Type u` of `D` and `w = v ∘ u`,
the stalk at `v` of the presheaf pushforward `u_p F` is the stalk of `F` at `w`, functorially in
the presheaf `F` on `C`.

Both functors are left adjoint to the same functor `Type u ⥤ (Cᵒᵖ ⥤ Type u)`, namely
`X ↦ (U ↦ (v(u(U)) → X))`. -/
noncomputable def presheafPushforwardStalkIso (u : C ⥤ D) (v : D ⥤ Type u) :
    u.op.lan ⋙ presheafStalk v ≅ presheafStalk (u ⋙ v) :=
  Adjunction.leftAdjointUniq ((u.op.lanAdjunction _).comp (adjunction v))
    (adjunction (u ⋙ v))

/-- **Stacks 0F4F**, packaged as the existence of the natural isomorphism
`(u_p F)_v ≅ F_{v ∘ u}`. -/
@[stacks 0F4F]
theorem presheafPushforward_stalk_iso (u : C ⥤ D) (v : D ⥤ Type u) :
    Nonempty (u.op.lan ⋙ presheafStalk v ≅ presheafStalk (u ⋙ v)) :=
  ⟨presheafPushforwardStalkIso u v⟩

end CategoryTheory.Stalk
