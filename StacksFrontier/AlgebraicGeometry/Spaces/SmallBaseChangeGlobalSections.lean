module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleDirectImageGlobalSections

/-!
# Global sections of a direct image along a representable morphism

Let `f : X' ⟶ X` be a representable morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  Base change of étale charts, `V ↦ V ×_X X'`, is the functor
`AlgebraicGeometry.Space.smallBaseChange` from the small étale site of `X` to that of `X'`, and
the direct image of a sheaf `P` on the small étale site of `X'` along it has sections
`P(V ×_X X')` over a chart `V` of `X`.  This file proves that the global sections are
unchanged: restricting a compatible family of sections of `P` over all charts of `X'` to the
base-changed charts `V ×_X X'` is a bijection

`Γ(X', P) ≃ Γ(X, f_* P)`,

and records the same statement for `𝒪_{X'}`-modules and the direct image
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, naturally in the module.

## Main definitions

* `AlgebraicGeometry.Space.sectionsRestrictSmallBaseChange` is the restriction of a compatible
  family of sections to the base-changed charts.
* `AlgebraicGeometry.Space.sectionsSmallBaseChange` is the same map for the global sections of
  an `𝒪_{X'}`-module, with values in the global sections of its direct image.

## Main results

* `AlgebraicGeometry.Space.bijective_sectionsRestrictSmallBaseChange`: for a sheaf of sets on the
  small étale site of `X'` restriction to the base-changed charts is bijective on global sections.
* `AlgebraicGeometry.Space.bijective_sectionsSmallBaseChange` and
  `AlgebraicGeometry.Space.sectionsMap_sectionsSmallBaseChange`: the global sections of an
  `𝒪_{X'}`-module are the global sections of its direct image, naturally in the module.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' : AlgebraicSpaces B S hS} (f : X' ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)

/-- Restriction of a compatible family of sections over the étale charts of `X'` to the
base-changed charts `V ×_X X'`. -/
noncomputable def sectionsRestrictSmallBaseChange (P : (SmallEtale B S hS X'.1)ᵒᵖ ⥤ Type t) :
    P.sections → ((smallBaseChange B S hS f hf).op ⋙ P).sections :=
  fun s => ⟨fun V => s.val (op ((smallBaseChange B S hS f hf).obj V.unop)),
    fun k => s.property ((smallBaseChange B S hS f hf).op.map k)⟩

/-- **Global sections of a spaces-étale sheaf, read on base-changed charts.** For a sheaf `H` on
the spaces-étale site of `X'`, restriction of a global section of its restriction to the
small étale site of `X'` to the base-changed charts `V ×_X X'` is bijective. -/
theorem bijective_sectionsRestrictSmallBaseChange_comparison
    (H : (SpacesEtale B S hS X')ᵒᵖ ⥤ Type t)
    (hH : Presheaf.IsSheaf (SpacesEtale.topology B S hS X') H) :
    Function.Bijective
      (sectionsRestrictSmallBaseChange B S hS f hf ((comparisonFunctor B S hS X').op ⋙ H)) := by
  obtain ⟨U', hU'⟩ := exists_isSurjective_chart B S hS X'
  obtain ⟨U, hU⟩ := exists_isSurjective_chart B S hS X
  have hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X)
      ((spacesBaseChange B S hS f).functor.op ⋙ H) :=
    (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type t)
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X')).obj ⟨H, hH⟩).property
  have hr' := bijective_restrictSectionsToCharts B S hS H hH hU'
  have hr := bijective_restrictSectionsToCharts B S hS
    ((spacesBaseChange B S hS f).functor.op ⋙ H) hP hU
  set c := smallBaseChange_comparison B S hS f hf
  let θ := (Functor.sectionsFunctor _).map
    (Functor.whiskerRight (NatTrans.op c.hom) H)
  have hθ : Function.Bijective θ :=
    (isIso_iff_bijective _).1 inferInstance
  have hφ : Function.Bijective (H.map (spacesBaseChangeIdObjIso B S hS f).hom.op) :=
    (isIso_iff_bijective _).1 inferInstance
  have hcomp : sectionsRestrictSmallBaseChange B S hS f hf ((comparisonFunctor B S hS X').op ⋙ H) ∘
        restrictSectionsToCharts B S hS H =
      θ ∘ restrictSectionsToCharts B S hS ((spacesBaseChange B S hS f).functor.op ⋙ H) ∘
        H.map (spacesBaseChangeIdObjIso B S hS f).hom.op := by
    funext x
    apply Subtype.ext; funext V
    show H.map _ x = H.map (c.hom.app V.unop).op (H.map _ (H.map _ x))
    simp only [← Functor.map_comp_apply]
    exact congrArg (fun g => H.map g x) (Quiver.Hom.unop_inj
      ((SpacesEtale.isTerminal_idObj B S hS X').hom_ext _ _))
  exact (Function.Bijective.of_comp_iff _ hr').1 (hcomp ▸ hθ.comp (hr.comp hφ))

/-- Restriction to the base-changed charts commutes with a morphism of presheaves. -/
theorem sectionsRestrictSmallBaseChange_naturality {P Q : (SmallEtale B S hS X'.1)ᵒᵖ ⥤ Type t}
    (α : P ⟶ Q) (s : P.sections) :
    sectionsRestrictSmallBaseChange B S hS f hf Q ((Functor.sectionsFunctor _).map α s) =
      (Functor.sectionsFunctor _).map (Functor.whiskerLeft (smallBaseChange B S hS f hf).op α)
        (sectionsRestrictSmallBaseChange B S hS f hf P s) :=
  rfl

/-- Bijectivity of restriction to the base-changed charts transports along an isomorphism of
presheaves. -/
theorem bijective_sectionsRestrictSmallBaseChange_of_iso {P Q : (SmallEtale B S hS X'.1)ᵒᵖ ⥤ Type t}
    (α : P ≅ Q) (hP : Function.Bijective (sectionsRestrictSmallBaseChange B S hS f hf P)) :
    Function.Bijective (sectionsRestrictSmallBaseChange B S hS f hf Q) := by
  have h₁ : Function.Bijective ((Functor.sectionsFunctor _).map α.hom) :=
    (isIso_iff_bijective _).1 inferInstance
  have h₂ : Function.Bijective ((Functor.sectionsFunctor _).map
      (Functor.whiskerLeft (smallBaseChange B S hS f hf).op α.hom)) :=
    (isIso_iff_bijective _).1 inferInstance
  exact (Function.Bijective.of_comp_iff _ h₁).1 (h₂.comp hP)

/-- **Global sections are preserved by restriction to the base-changed charts.** For a
representable morphism `f : X' ⟶ X` and a sheaf of sets `P` on the small étale site of `X'`,
restriction of a global section of `P` to the charts `V ×_X X'` is a bijection onto the global
sections of the direct image of `P` along base change of charts. -/
theorem bijective_sectionsRestrictSmallBaseChange
    (P : Sheaf (SmallEtale.topology B S hS X'.1) (Type u)) :
    Function.Bijective (sectionsRestrictSmallBaseChange B S hS f hf P.obj) := by
  let e := (smallEtaleComparisonRestriction B S hS X').asEquivalence
  refine bijective_sectionsRestrictSmallBaseChange_of_iso B S hS f hf
    ((sheafToPresheaf _ _).mapIso (e.counitIso.app P)) ?_
  exact bijective_sectionsRestrictSmallBaseChange_comparison B S hS f hf
    (e.inverse.obj P).obj (e.inverse.obj P).property

/-- Restriction of a global section of an `𝒪_{X'}`-module to the base-changed charts, as a global
section of the direct image. -/
noncomputable def sectionsSmallBaseChange (M : Modules.{u, u} B S hS X'.1 X'.2) :
    M.sections → ((smallBaseChangeModulePushforward B S hS f hf).obj M).sections :=
  sectionsRestrictSmallBaseChange B S hS f hf (M.val.presheaf ⋙ forget _)

/-- **The global sections of an `𝒪_{X'}`-module are those of its direct image.** For a
representable `f : X' ⟶ X`, restriction to the base-changed charts is a bijection from the global
sections of an `𝒪_{X'}`-module onto the global sections of its direct image along base change of
charts. -/
theorem bijective_sectionsSmallBaseChange (M : Modules.{u, u} B S hS X'.1 X'.2) :
    Function.Bijective (sectionsSmallBaseChange B S hS f hf M) :=
  bijective_sectionsRestrictSmallBaseChange B S hS f hf
    (moduleSetSheaf B S hS X' M)

/-- Restriction to the base-changed charts is natural in the module. -/
theorem sectionsMap_sectionsSmallBaseChange {M N : Modules.{u, u} B S hS X'.1 X'.2}
    (g : M ⟶ N) (s : M.sections) :
    SheafOfModules.sectionsMap ((smallBaseChangeModulePushforward B S hS f hf).map g)
        (sectionsSmallBaseChange B S hS f hf M s) =
      sectionsSmallBaseChange B S hS f hf N (SheafOfModules.sectionsMap g s) :=
  rfl

end AlgebraicGeometry.Space

end
