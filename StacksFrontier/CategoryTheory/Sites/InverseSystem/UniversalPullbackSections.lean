module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.UniversalPullbackSystem

/-!
# Sections of the inverse image of a sheaf of sets on a colimit site

Let `D` be an inverse system of sites with finite coverings whose index has a terminal object `t`,
let `F₀` be a sheaf of sets on `C_t`, and let `Fᵢ` be the inverse images of `F₀` on the levels,
characterised by universal arrows `εᵢ : F₀ ⟶ u_{!ᵢ,*}Fᵢ`
(`Stacks.WeakSites.PullbackSystem.IsUniversalArrow`). On a colimit site `C` of the system, let `G`
be a sheaf of sets with a universal arrow `ε_G : F₀ ⟶ u_{t,*}G`, so that `G = f_t⁻¹F₀`.

This file feeds that situation to the weak-system form of Stacks 09YN
(`InverseSystemOfFiniteSites.sections_colimit_pullback_of_colimit`): the transition maps, the
cocycle condition, the structure maps of the colimit and its universal property are all read off
from the universal arrows. The conclusion is that for every object `X` of a level `i`, the
sections of `G` over `u_i(X)` are the filtered colimit of the sections of `F_j` over the
transition images `u_a(X)`.

## Main results

* `Stacks.WeakSites.PullbackSystem.ψ_comp_apply`, `ι_comp_apply`: the cocycle condition and the
  compatibility of the structure maps, elementwise.
* `Stacks.WeakSites.PullbackSystem.sections_colimit_of_universal`: the colimit description of the
  sections of `G`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sites.InverseSystem

universe v u w

namespace Stacks.WeakSites.PullbackSystem

open InverseSystemOfFiniteSites

variable (D : InverseSystemOfFiniteSites.{v, u, w}) {t : D.I} (ht : IsTerminal t)
  {F₀ : Sheaf (D.J t) (Type w)} {F : ∀ i, Sheaf (D.J i) (Type w)}
  (ε : ∀ i, F₀.obj ⟶ (D.u (ht.from i)).op ⋙ (F i).obj)
  (huniv : ∀ i, IsUniversalArrow D ht ε i)

/-- **The cocycle condition of the system of inverse images, elementwise.** -/
theorem ψ_comp_apply {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (V : D.C i)
    (x : (F i).obj.obj (op V)) :
    (ψ D ht ε huniv (b ≫ a)).app (op V) x =
      (F k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) V).symm))
        ((ψ D ht ε huniv b).app (op ((D.u a).obj V)) ((ψ D ht ε huniv a).app (op V) x)) := by
  rw [ψ_comp D ht ε huniv a b]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, eqToHom_map]
  rfl

section Colimit

variable {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (K : GrothendieckTopology C) [∀ i, (uC i).IsContinuous (D.J i) K]
  {G : Sheaf K (Type w)} (εG : F₀.obj ⟶ (uC t).op ⋙ G.obj)

/-- **The structure maps of the colimit are compatible with the transitions, elementwise.** -/
theorem ι_comp_apply {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : (F i).obj.obj (op V)) :
    (ι D ht ε huniv uC hu K εG i).app (op V) x =
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
        ((ι D ht ε huniv uC hu K εG j).app (op ((D.u a).obj V))
          ((ψ D ht ε huniv a).app (op V) x)) := by
  rw [ι_comp D ht ε huniv uC hu K εG a]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, eqToHom_map]
  rfl

end Colimit

section Sections

variable {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (uC i).obj Y = X)
  (hhom :
    ∀ (i : D.I) (X Y : D.C i) (f : (uC i).obj X ⟶ (uC i).obj Y),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
        (uC j).map g =
          eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)
  (hhom_inj :
    ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
      (uC i).map g₁ = (uC i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK :
    ∀ (X : C) (R : Presieve X),
      R ∈ K X ↔
        ∃ (i : D.I) (Y : D.C i) (h : (uC i).obj Y = X) (S : Presieve Y),
          S ∈ (D.J i).toPrecoverage Y ∧ S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (uC i))
  [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  {G : Sheaf K.toGrothendieck (Type w)} (εG : F₀.obj ⟶ (uC t).op ⋙ G.obj)
  (hεG : ∀ (H : Sheaf K.toGrothendieck (Type w)) (g : F₀.obj ⟶ (uC t).op ⋙ H.obj),
      ∃! h : G ⟶ H, εG ≫ Functor.whiskerLeft (uC t).op h.hom = g)

include hobj hhom hhom_inj hK hεG in
/-- **Stacks 09YN for the inverse images of a sheaf of sets on the terminal level.** The sections
of `G = f_t⁻¹F₀` over `u_i(X)` are the filtered colimit of the sections of the inverse images
`F_j` over the transition images `u_a(X)`, the colimit maps being the structure maps `ι` and the
transition maps being the maps `ψ` read off from the universal arrows: every section comes from
some level, and two sections with the same image agree after a further transition. -/
theorem sections_colimit_of_universal (i : D.I) (X : D.C i) :
    (∀ s : G.obj.obj (op ((uC i).obj X)),
        ∃ (j : D.I) (a : j ⟶ i) (t' : (F j).obj.obj (op ((D.u a).obj X))),
          G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))
            ((ι D ht ε huniv uC hu K.toGrothendieck εG j).app (op ((D.u a).obj X)) t') = s) ∧
      ∀ (j : D.I) (a : j ⟶ i) (t₁ t₂ : (F j).obj.obj (op ((D.u a).obj X))),
        G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))
            ((ι D ht ε huniv uC hu K.toGrothendieck εG j).app (op ((D.u a).obj X)) t₁) =
          G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))
            ((ι D ht ε huniv uC hu K.toGrothendieck εG j).app (op ((D.u a).obj X)) t₂) →
          ∃ (k : D.I) (b : k ⟶ j),
            (ψ D ht ε huniv b).app (op ((D.u a).obj X)) t₁ =
              (ψ D ht ε huniv b).app (op ((D.u a).obj X)) t₂ :=
  InverseSystemOfFiniteSites.sections_colimit_pullback_of_colimit D uC hu hobj hhom hhom_inj K hK F
    (fun a => ψ D ht ε huniv a) (fun a b V x => ψ_comp_apply D ht ε huniv a b V x) G
    (fun j => ι D ht ε huniv uC hu K.toGrothendieck εG j)
    (fun a V x => ι_comp_apply D ht ε huniv uC hu K.toGrothendieck εG a V x)
    (fun H g hg => by
      obtain ⟨h, hh, hu'⟩ := existsUnique_of_compatible (D := D) (ht := ht) (ε := ε)
        (huniv := huniv) (uC := uC) (hu := hu) (K := K.toGrothendieck) (εG := εG) hεG H g
        (fun {i j} a => by
          ext V x
          have := hg a V.unop x
          simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, eqToHom_map] at this ⊢
          exact this)
      refine ⟨h, fun i V x => ?_, fun h' hh' => hu' h' (fun i => ?_)⟩
      · rw [← hh i]
        rfl
      · ext V x
        exact (hh' i V.unop x).symm)
    i X (fun a t' => _) (fun _ _ => rfl)

end Sections

end Stacks.WeakSites.PullbackSystem
