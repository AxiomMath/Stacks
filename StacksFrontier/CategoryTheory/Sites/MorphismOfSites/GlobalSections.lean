module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs

/-!
# Global sections along a morphism of sites

Let `u : C ⥤ D` be a continuous functor of sites defining a morphism of sites, that is, whose
direct image `u^s` on sheaves of sets has a left exact left adjoint `u_s`. Then global sections
are unchanged by the direct image: for every sheaf of sets `F` on `D`, restriction of sections
along `u` is a bijection `Γ(D, F) ≅ Γ(C, u^s F)`. Indeed a global section of a sheaf is a
morphism out of the final sheaf, and `u_s` carries the final sheaf of `C` to that of `D`, being
left exact, so

`Γ(C, u^s F) = Hom(*, u^s F) = Hom(u_s *, F) = Hom(*, F) = Γ(D, F)`.

## Main results

* `CategoryTheory.Functor.bijective_sectionsPrecomp_of_isMorphismOfSites`: restriction of global
  sections along a morphism of sites is a bijection, for sheaves of sets in the universe of the
  morphism of sites.
* `CategoryTheory.Functor.bijective_sectionsPrecomp_of_isMorphismOfSites_ulift`: the same for
  sheaves of sets in a smaller universe.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The sections of a sheaf of sets are the morphisms out of the final sheaf. -/
private def sectionsEquivHomTerminal (L : GrothendieckTopology C) (F : Sheaf L (Type w)) :
    F.obj.sections ≃ (Sheaf.terminal L Types.isTerminalPUnit ⟶ F) :=
  (F.obj.sectionsEquivHom PUnit).trans
    (Sheaf.homEquiv (X := Sheaf.terminal L Types.isTerminalPUnit) (Y := F)).symm

/-- **Restriction of global sections along a morphism of sites is a bijection.** If `u : C ⥤ D`
defines a morphism of sites, then for every sheaf of sets `F` on `D` the restriction
`Γ(D, F) ⟶ Γ(C, u^s F)` of compatible families of sections along `u` is bijective. -/
theorem bijective_sectionsPrecomp_of_isMorphismOfSites (a : C ⥤ D)
    [ha : IsMorphismOfSites.{w} a J K] (F : Sheaf K (Type w)) :
    Function.Bijective (Functor.sectionsPrecomp a.op (P := F.obj)) := by
  obtain ⟨L, ⟨adj⟩, hL⟩ := ha.hasExactLeftAdjoint
  let T := Sheaf.terminal J (Types.isTerminalPUnit.{w})
  let e : L.obj T ≅ Sheaf.terminal K Types.isTerminalPUnit :=
    (IsTerminal.isTerminalObj L T
      (Sheaf.isTerminalTerminal J Types.isTerminalPUnit)).uniqueUpToIso
      (Sheaf.isTerminalTerminal K Types.isTerminalPUnit)
  let E : F.obj.sections ≃ (a.op ⋙ F.obj).sections :=
    (sectionsEquivHomTerminal K F).trans
      ((Iso.homCongr e.symm (Iso.refl F)).trans
        ((adj.homEquiv T F).trans
          (sectionsEquivHomTerminal J ((a.sheafPushforwardContinuous (Type w) J K).obj F)).symm))
  have hE : ⇑E = Functor.sectionsPrecomp a.op := by
    funext s
    apply (sectionsEquivHomTerminal J ((a.sheafPushforwardContinuous (Type w) J K).obj F)).injective
    have ht : adj.homEquiv T _ e.hom = 𝟙 T :=
      (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).hom_ext _ _
    simp only [E, Equiv.trans_apply]
    show adj.homEquiv T F (e.hom ≫ (sectionsEquivHomTerminal K F) s) = _
    rw [adj.homEquiv_naturality_right, ht]
    apply Sheaf.hom_ext
    ext V x
    rfl
  rw [← hE]
  exact E.bijective

/-- **Restriction of global sections along a morphism of sites is a bijection**, for a sheaf of
sets whose values lie in a universe `t` below the universe `max t w` in which the morphism of
sites is one: the sections of the sheaf and of its universe lift correspond. -/
theorem bijective_sectionsPrecomp_of_isMorphismOfSites_ulift (a : C ⥤ D)
    [IsMorphismOfSites.{max t w} a J K] (F : Sheaf K (Type t)) :
    Function.Bijective (Functor.sectionsPrecomp a.op (P := F.obj)) := by
  let F' := (sheafCompose K uliftFunctor.{w, t}).obj F
  let E := Types.sectionsEquiv.{w} F.obj
  let E' := Types.sectionsEquiv.{w} (a.op ⋙ F.obj)
  have he : Functor.sectionsPrecomp a.op (P := F.obj) =
      E'.symm ∘ Functor.sectionsPrecomp a.op (P := F'.obj) ∘ E := rfl
  rw [he]
  exact E'.symm.bijective.comp
    ((bijective_sectionsPrecomp_of_isMorphismOfSites.{max t w} (J := J) a F').comp E.bijective)

end CategoryTheory.Functor

end
