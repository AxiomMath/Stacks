module

public import Mathlib.CategoryTheory.Sites.GlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two presentations of global sections, read against the restriction maps

Mathlib's global sections functor `CategoryTheory.Sheaf.Γ J A` is the right adjoint of the
constant sheaf functor.  It comes with two further presentations:

* `CategoryTheory.Sheaf.ΓNatIsoLim`, the limit of the underlying presheaf, available when `A`
  has limits of shape `Cᵒᵖ`;
* `CategoryTheory.Sheaf.ΓNatIsoSheafSections`, the sections at a terminal object of the site.

Both are produced by `CategoryTheory.Adjunction.rightAdjointUniq` and are therefore opaque: no
lemma in Mathlib evaluates either of them.  This file evaluates both, against the restriction
maps `CategoryTheory.Sheaf.ΓRes` out of global sections, which is the form in which a
comparison of global sections along a morphism of sites is checked.

Both statements say the obvious thing — the comparison is compatible with restriction — and both
proofs run through one transposition lemma: transposing a morphism along one of two adjunctions
with the same left adjoint and then comparing the two right adjoints is transposing it along the
other adjunction.  Applied to the counit of `constantSheaf ⊣ Γ`, whose transpose along that
adjunction is the identity, it says that the comparison is the transpose of that counit along
the other adjunction, and each of the two other adjunctions computes that transpose.

## Main results

* `CategoryTheory.Sheaf.ΓNatIsoLim_hom_app_comp_π` — the comparison of global sections with the
  limit of the underlying presheaf is the one whose composite with the limit projection at `U`
  is the restriction map to `U`.  This is what makes `Sheaf.ΓNatIsoLim` *the* canonical
  comparison, matching `CategoryTheory.Sheaf.isLimitConeΓ`, and not merely some isomorphism; in
  particular a composite of such isomorphisms may be checked projection by projection.
* `CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app_general` — the comparison of global sections
  with the sections at a terminal object `T` is the restriction map to `T`.
-/

@[expose] public section

universe u v u₂ v₂

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u₂} [Category.{v₂} A] [HasWeakSheafify J A]

/-- Transposing a morphism along one of two adjunctions with the same left adjoint and then
comparing the two right adjoints is transposing it along the other adjunction. -/
private theorem homEquiv_comp_rightAdjointUniq_hom_app {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R R' : E ⥤ D} (adj1 : L ⊣ R) (adj2 : L ⊣ R') (X : D) (Y : E)
    (f : L.obj X ⟶ Y) :
    adj1.homEquiv X Y f ≫ (Adjunction.rightAdjointUniq adj1 adj2).hom.app Y =
      adj2.homEquiv X Y f := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (Adjunction.rightAdjointUniq adj1 adj2).hom.naturality f, ← Category.assoc,
    Adjunction.unit_rightAdjointUniq_hom_app]

/-- **A comparison of `Γ` with another right adjoint of the constant sheaf functor is the
transpose, along that other adjunction, of the counit of `constantSheaf ⊣ Γ`.**  This is the
transposition lemma above at the counit, whose transpose along `constantSheaf ⊣ Γ` is the
identity by the triangle identity. -/
private theorem rightAdjointUniq_hom_app_eq_homEquiv
    [HasGlobalSectionsFunctor J A] {R : Sheaf J A ⥤ A}
    (adj : constantSheaf J A ⊣ R) (F : Sheaf J A) :
    (Adjunction.rightAdjointUniq (constantSheafΓAdj J A) adj).hom.app F =
      adj.homEquiv ((Γ J A).obj F) F ((constantSheafΓAdj J A).counit.app F) := by
  have h := homEquiv_comp_rightAdjointUniq_hom_app (constantSheafΓAdj J A) adj
    ((Γ J A).obj F) F ((constantSheafΓAdj J A).counit.app F)
  rwa [Adjunction.homEquiv_unit, Adjunction.right_triangle_components, Category.id_comp] at h

/-- Transposing along the adjunction `const ⊣ lim` and projecting to the component at `U` is
evaluation at `U`.  `CategoryTheory.Limits.constLimAdj` is built by `Adjunction.mk'` from the
hom-set bijection `f ↦ limit.lift _ ⟨c, f⟩`, which `Adjunction.mk'_homEquiv` recovers. -/
@[sga "4 Vbis 2.1.1" "more general"]
private theorem constLimAdj_homEquiv_comp_π {K : Type*} [Category K] {B : Type*} [Category B]
    [HasLimitsOfShape K B] (X : B) (G : K ⥤ B) (g : (Functor.const K).obj X ⟶ G) (U : K) :
    constLimAdj.homEquiv X G g ≫ limit.π G U = g.app U := by
  simp only [constLimAdj, Adjunction.mk'_homEquiv, Equiv.coe_fn_mk, limit.lift_π]

/-- Transposing along `const ⊣ lim` after `presheafToSheaf ⊣ sheafToPresheaf` and projecting at
`U`: the limit half contributes evaluation at `U`, so what is left is the transpose along
sheafification. -/
private theorem comp_homEquiv_comp_π [HasLimitsOfShape Cᵒᵖ A] (X : A) (G : Sheaf J A)
    (f : (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).obj X ⟶ G) (U : Cᵒᵖ) :
    (constLimAdj.comp (sheafificationAdjunction J A)).homEquiv X G f ≫ limit.π G.obj U =
      ((sheafificationAdjunction J A).homEquiv ((Functor.const Cᵒᵖ).obj X) G f).app U := by
  rw [Adjunction.comp_homEquiv]
  exact constLimAdj_homEquiv_comp_π _ _ _ _

/-- Transposing along `const ⊣ evaluation at a terminal object` after
`presheafToSheaf ⊣ sheafToPresheaf`: the first half is evaluation at the terminal object. -/
private theorem comp_homEquiv_terminal [HasTerminal C] {T : C} (hT : IsTerminal T) (X : A)
    (G : Sheaf J A) (f : (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).obj X ⟶ G) :
    ((constantPresheafAdj A hT).comp (sheafificationAdjunction J A)).homEquiv X G f =
      ((sheafificationAdjunction J A).homEquiv ((Functor.const Cᵒᵖ).obj X) G f).app (op T) := by
  rw [Adjunction.comp_homEquiv]
  simp [Adjunction.homEquiv_unit, constantPresheafAdj]

/-- The restriction map out of global sections is the transpose along sheafification of the
counit of `constantSheaf ⊣ Γ`, read at `U`. -/
private theorem ΓRes_eq [HasGlobalSectionsFunctor J A] (F : Sheaf J A) (U : Cᵒᵖ) :
    ΓRes F U =
      ((sheafificationAdjunction J A).homEquiv ((Functor.const Cᵒᵖ).obj ((Γ J A).obj F)) F
        ((constantSheafΓAdj J A).counit.app F)).app U := by
  have hc : ((constantSheafΓAdj J A).homEquiv ((Γ J A).obj F) F).symm (𝟙 _) =
      (constantSheafΓAdj J A).counit.app F := by
    rw [Adjunction.homEquiv_counit, Functor.map_id, Category.id_comp]
  exact congrArg
    (fun z ↦ ((sheafificationAdjunction J A).homEquiv
      ((Functor.const Cᵒᵖ).obj ((Γ J A).obj F)) F z).app U) hc

/-- **The comparison `Γ(F) ≅ lim F` is compatible with restriction.**  Composed with the
projection of the limit of the underlying presheaf at an object `U`, the isomorphism
`CategoryTheory.Sheaf.ΓNatIsoLim` is the restriction map `CategoryTheory.Sheaf.ΓRes` of global
sections to sections over `U`.

This pins `Sheaf.ΓNatIsoLim` down.  `CategoryTheory.Sheaf.isLimitConeΓ` exhibits global sections
as a limit of the underlying presheaf with the restriction maps as its legs, and the statement
says that the isomorphism to `lim` is the comparison of those two limiting cones. -/
@[reassoc (attr := simp)]
theorem ΓNatIsoLim_hom_app_comp_π [HasLimitsOfShape Cᵒᵖ A] (F : Sheaf J A) (U : Cᵒᵖ) :
    (ΓNatIsoLim J A).hom.app F ≫ limit.π F.obj U = ΓRes F U := by
  refine .trans (congrArg (· ≫ limit.π F.obj U) (rightAdjointUniq_hom_app_eq_homEquiv
    (constLimAdj.comp (sheafificationAdjunction J A)) F)) ?_
  exact .trans (comp_homEquiv_comp_π ((Γ J A).obj F) F
    ((constantSheafΓAdj J A).counit.app F) U) (ΓRes_eq F U).symm

/-- **The comparison `Γ(F) ≅ F(T)` at a terminal object `T` of the site is the restriction map.**
`CategoryTheory.Sheaf.ΓNatIsoSheafSections` identifies global sections with sections over a
terminal object; the identification is `CategoryTheory.Sheaf.ΓRes` at that object. -/
@[simp]
theorem ΓNatIsoSheafSections_hom_app_general [HasTerminal C] {T : C} (hT : IsTerminal T)
    (F : Sheaf J A) :
    (ΓNatIsoSheafSections J A hT).hom.app F = ΓRes F (op T) := by
  refine .trans (rightAdjointUniq_hom_app_eq_homEquiv (constantSheafAdj J A hT) F) ?_
  exact .trans (comp_homEquiv_terminal hT ((Γ J A).obj F) F
    ((constantSheafΓAdj J A).counit.app F)) (ΓRes_eq F (op T)).symm

end CategoryTheory.Sheaf

end
