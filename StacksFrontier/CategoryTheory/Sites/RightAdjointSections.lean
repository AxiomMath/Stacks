module

public import StacksFrontier.CategoryTheory.Sites.SheafSectionEssentiallySmall

/-!
# Natural maps out of the local sections of a right adjoint between sheaf categories

Let `L ⊣ G` be an adjunction between categories of sheaves of sets on two sites, with `G` going
from sheaves on `(D, K)` to sheaves on `(C, J)`, and let `U` be an object of `C`.  A local section
over `U` of `G F` is the same thing as a morphism `L(h_U) ⟶ F`, where `h_U` is the sheafified
representable of `U`: the functor `F ↦ (G F)(U)` is corepresented by `E = L(h_U)`.

Consequently a family of maps `(G F)(U) ⟶ F(Q)`, natural in the sheaf `F`, is determined by its
value at the universal section of `G E`; and if `E` has at most one section over `Q` — as happens
when `U` has at most one morphism from every object and `L` is left exact, `E` being then a
subobject of the terminal sheaf — any two such families agree.  This is how comparisons of local
sections of direct images along morphisms of topoi are shown to satisfy their coherences: each
side of a coherence is a natural family of that kind.

## Main definitions

* `Stacks.Sites.SheafSection.rightAdjointSectionEquiv`: the corepresentation
  `(G F)(U) ≃ (L(h_U) ⟶ F)`.
* `Stacks.Sites.SheafSection.universalSection`: the section of `G(L(h_U))` corresponding to the
  identity.

## Main results

* `Stacks.Sites.SheafSection.eq_app_universalSection`: a natural family is evaluation of the
  transposed morphism at the image of the universal section.
* `Stacks.Sites.SheafSection.natural_family_ext`: two natural families agree as soon as
  `L(h_U)` has at most one section over the target object.
* `Stacks.Sites.SheafSection.subsingleton_obj_of_subsingleton_hom`: `L(h_U)` has at most one
  section over every object when `L` is left exact and morphisms into `U` are unique.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u' v v' w w'

namespace Stacks.Sites.SheafSection

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [LocallySmall.{w} C] [HasWeakSheafify J (Type w)]
  {L : Sheaf J (Type w) ⥤ Sheaf K (Type w')} {G : Sheaf K (Type w') ⥤ Sheaf J (Type w)}
  (adj : L ⊣ G) (U : Cᵒᵖ)

/-- **Local sections of a right adjoint, transposed.** A section over `U` of `G F` is a morphism
to `F` from the image under the left adjoint of the sheafified small representable of `U`. -/
noncomputable def rightAdjointSectionEquiv (F : Sheaf K (Type w')) :
    (G.obj F).obj.obj U ≃
      (L.obj ((presheafToSheaf J (Type w)).obj (smallYoneda.{w} U.unop)) ⟶ F) :=
  (sectionEquivSmall J U _).trans (adj.homEquiv _ _).symm

/-- The transposition is natural in the sheaf. -/
theorem rightAdjointSectionEquiv_map {F F' : Sheaf K (Type w')} (g : F ⟶ F')
    (x : (G.obj F).obj.obj U) :
    rightAdjointSectionEquiv adj U F' ((G.map g).hom.app U x) =
      rightAdjointSectionEquiv adj U F x ≫ g := by
  dsimp [rightAdjointSectionEquiv]
  rw [sectionEquivSmall_comp, Adjunction.homEquiv_naturality_right_symm]

/-- The universal section: the section of `G(L(h_U))` over `U` corresponding to the identity. -/
noncomputable def universalSection :
    (G.obj (L.obj ((presheafToSheaf J (Type w)).obj (smallYoneda.{w} U.unop)))).obj.obj U :=
  (rightAdjointSectionEquiv adj U _).symm (𝟙 _)

/-- Every section is the image of the universal section along its transpose. -/
theorem map_universalSection {F : Sheaf K (Type w')}
    (g : L.obj ((presheafToSheaf J (Type w)).obj (smallYoneda.{w} U.unop)) ⟶ F) :
    (G.map g).hom.app U (universalSection adj U) =
      (rightAdjointSectionEquiv adj U F).symm g := by
  rw [Equiv.eq_symm_apply, rightAdjointSectionEquiv_map, universalSection,
    Equiv.apply_symm_apply, Category.id_comp]

/-- **A natural family is evaluation at the universal section.** If `η_F : (G F)(U) ⟶ F(Q)` is
natural in `F`, then its value at the section transposed to `g : L(h_U) ⟶ F` is `g` evaluated
at the value of `η` at the universal section. -/
theorem eq_app_universalSection {Q : Dᵒᵖ}
    (η : ∀ F : Sheaf K (Type w'), (G.obj F).obj.obj U → F.obj.obj Q)
    (hη : ∀ {F F' : Sheaf K (Type w')} (g : F ⟶ F') (x : (G.obj F).obj.obj U),
      η F' ((G.map g).hom.app U x) = g.hom.app Q (η F x))
    {F : Sheaf K (Type w')}
    (g : L.obj ((presheafToSheaf J (Type w)).obj (smallYoneda.{w} U.unop)) ⟶ F) :
    η F ((rightAdjointSectionEquiv adj U F).symm g) =
      g.hom.app Q (η _ (universalSection adj U)) := by
  rw [← map_universalSection, hη]

include adj in
/-- **Two natural families agree** as soon as the corepresenting sheaf has at most one section
over the target object. -/
theorem natural_family_ext {Q : Dᵒᵖ}
    [Subsingleton ((L.obj ((presheafToSheaf J (Type w)).obj (smallYoneda.{w} U.unop))).obj.obj Q)]
    (η η' : ∀ F : Sheaf K (Type w'), (G.obj F).obj.obj U → F.obj.obj Q)
    (hη : ∀ {F F' : Sheaf K (Type w')} (g : F ⟶ F') (x : (G.obj F).obj.obj U),
      η F' ((G.map g).hom.app U x) = g.hom.app Q (η F x))
    (hη' : ∀ {F F' : Sheaf K (Type w')} (g : F ⟶ F') (x : (G.obj F).obj.obj U),
      η' F' ((G.map g).hom.app U x) = g.hom.app Q (η' F x))
    (F : Sheaf K (Type w')) (x : (G.obj F).obj.obj U) : η F x = η' F x := by
  obtain ⟨g, rfl⟩ := (rightAdjointSectionEquiv adj U F).symm.surjective x
  rw [eq_app_universalSection adj U η hη, eq_app_universalSection adj U η' hη',
    Subsingleton.elim (η _ (universalSection adj U)) (η' _ (universalSection adj U))]

/-- **The corepresenting sheaf is subterminal** when morphisms into `U` are unique and the left
adjoint is left exact: it has at most one section over every object. -/
theorem subsingleton_obj_of_subsingleton_hom [HasSheafify J (Type w)]
    [LocallySmall.{w'} D] [HasWeakSheafify K (Type w')] [PreservesFiniteLimits L]
    (hU : ∀ W : C, Subsingleton (W ⟶ U.unop)) (Q : Dᵒᵖ) :
    Subsingleton
      ((L.obj ((presheafToSheaf J (Type w)).obj (smallYoneda.{w} U.unop))).obj.obj Q) := by
  refine ⟨fun a b => (sectionEquivSmall K Q _).injective ?_⟩
  have hmono : Mono (terminal.from (smallYoneda.{w} U.unop)) := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun W => ?_)
    rw [mono_iff_injective]
    intro x y _
    have := hU W.unop
    exact (equivShrink (W.unop ⟶ U.unop)).symm.injective (Subsingleton.elim _ _)
  have hterm : IsTerminal (L.obj ((presheafToSheaf J (Type w)).obj (⊤_ (Cᵒᵖ ⥤ Type w)))) :=
    IsTerminal.isTerminalObj L _ (IsTerminal.isTerminalObj _ _ terminalIsTerminal)
  have : Mono (L.map ((presheafToSheaf J (Type w)).map
      (terminal.from (smallYoneda.{w} U.unop)))) := inferInstance
  exact (cancel_mono (L.map ((presheafToSheaf J (Type w)).map
    (terminal.from (smallYoneda.{w} U.unop))))).1 (hterm.hom_ext _ _)

end Stacks.Sites.SheafSection
