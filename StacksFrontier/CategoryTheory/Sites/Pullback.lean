module

public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute

/-!
# The presheaf pullback and its compatibility with sheafification

Let `u : C ⥤ D` be a continuous functor between sites, defining a morphism of sites
`f : D → C`. Write `u_p : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` for the left adjoint of restriction along
`u`, i.e. the left Kan extension `u.op.lan`, and `f⁻¹ = u_s = u.sheafPullback` for the
pullback of sheaves. For a presheaf `G` on `C` one has `(u_p G)^# = (u_p (G^#))^#`,
equivalently `(u_p G)^# ≅ f⁻¹(G^#)`, naturally in `G`.

Mathlib has the counterpart for the *restriction* `u^p` along a cocontinuous functor,
`Functor.pushforwardContinuousSheafificationCompatibility`; this is the statement for `u_p`,
which is the one the theory of morphisms of sites uses.

Lower shriek on abelian sheaves, `g_!`, is defined in **Stacks 04BF** by the two steps
`g_{p!}F : V ↦ \colim_{V → u(U)} F(U)` and `g_!F = (g_{p!}F)^#`, the colimit being taken over
the opposite of the index category `I_V^u` of **Stacks 00VC** — the category of pairs
`(U, V → u(U))`. Both steps are already in Mathlib, under other descriptions: `g_{p!}` is the
left Kan extension `u.op.lan`, whose value at `V` is that colimit by
`CategoryTheory.Functor.leftKanExtensionObjIsoColimit` once `(I_V^u)ᵒᵖ` is read through the
equivalence `CategoryTheory.structuredArrowOpEquivalence`, and `g_!` is
`Functor.sheafPullbackConstruction.sheafPullback`. Nothing is restated here; the two Mathlib
definitions carry the tag through the `add_to_stacks` annotations at the end of this file.

## Main results

* `CategoryTheory.Functor.sheafPullbackSheafificationCompatibility` (**Stacks 00WY**):
  `(u_p G)^# ≅ f⁻¹(G^#)`.

## References

* [Stacks Project, Tag 00VC](https://stacks.math.columbia.edu/tag/00VC)
* [Stacks Project, Tag 00WY](https://stacks.math.columbia.edu/tag/00WY)
* [Stacks Project, Tag 04BF](https://stacks.math.columbia.edu/tag/04BF)
* [Stacks Project, Tag 04BG](https://stacks.math.columbia.edu/tag/04BG)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- **Stacks 00WY**.
Sheafification commutes with the presheaf pullback `u_p` along a continuous functor
`u : C ⥤ D`: the composite of `u_p = u.op.lan` with sheafification on `D` is naturally
isomorphic to the composite of sheafification on `C` with the sheaf pullback
`f⁻¹ = u.sheafPullback`. Both composites are left adjoint to the same functor
`Sheaf K A ⥤ Cᵒᵖ ⥤ A`, namely restriction along `u` followed by the inclusion of sheaves
into presheaves, so the isomorphism is uniqueness of left adjoints. -/
@[stacks 00WY]
noncomputable def sheafPullbackSheafificationCompatibility
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (A : Type u₃)
    [Category.{v₃} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [u.IsContinuous J K] [HasWeakSheafify J A] [HasWeakSheafify K A]
    [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F] :
    u.op.lan ⋙ presheafToSheaf K A ≅ presheafToSheaf J A ⋙ u.sheafPullback A J K :=
  Adjunction.leftAdjointUniq
    ((u.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    ((sheafificationAdjunction J A).comp (u.sheafAdjunctionContinuous A J K))

end CategoryTheory.Functor

-- Tag 04BG: for `u` continuous, `g_{p!} = u.op.lan ⊣ u^p` on presheaves and
-- `g_! = (g_{p!} -)^# ⊣ g^{-1}` on sheaves.
add_to_stacks 04BG "(1) g_p! ⊣ u^p" CategoryTheory.Functor.lanAdjunction
add_to_stacks 04BG "(2) g_! ⊣ g^{-1}" CategoryTheory.Functor.sheafAdjunctionContinuous
add_to_stacks 04BG "g_!" CategoryTheory.Functor.sheafPullback
add_to_stacks 04BG "(2) g_! = (g_p! -)^#"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

-- Tag 04BF: the first step of the definition, the colimit formula for `g_{p!}`, is Mathlib's
-- left Kan extension along `u.op`; the second, `g_! F = (g_{p!} F)^#`, is Mathlib's
-- construction of the sheaf pullback.
add_to_stacks 04BF "g_{p!} = u_p, the left Kan extension along `u.op`"
  CategoryTheory.Functor.lan
add_to_stacks 04BF "g_! F = (g_{p!} F)^#"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
