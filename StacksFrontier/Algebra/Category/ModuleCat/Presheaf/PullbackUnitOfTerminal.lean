module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The pullback of the unit module along a functor preserving a terminal object

Let `F : C ⥤ D` be a functor, `φ : S ⟶ F.op ⋙ R` a morphism of presheaves of rings, and suppose
the pushforward of presheaves of modules along `φ` has a left adjoint `pullback φ`. If `C` has a
terminal object `t` whose image `F(t)` is terminal in `D`, then the mate of the canonical map
`unit S ⟶ (pushforward φ).obj (unit R)` (which is `φ` on sections) is an isomorphism
`(pullback φ).obj (unit S) ≅ unit R`.

Both objects corepresent the same functor: `unit R` corepresents the sections of a presheaf of
`R`-modules `M`, which are its value at the terminal object of `D`; and `(pullback φ).obj (unit S)`
corepresents the sections of `(pushforward φ).obj M`, which are the value of `M` at `F(t)`.

## Main results

* `PresheafOfModules.isIso_homEquiv_symm_unit`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- The restriction of sections along `F`, from the sections of `M` to the sections of its
pushforward along `φ`, is a bijection when `F` sends a terminal object to a terminal object. -/
theorem bijective_sectionsRestriction {t : C} (ht : IsTerminal t) (hFt : IsTerminal (F.obj t))
    (M : PresheafOfModules.{v} R) :
    Function.Bijective (fun s : M.sections =>
      (((pushforward.{v} φ).obj M).sectionsMk (fun X => s.1 (op (F.obj X.unop)))
        (fun X Y f => by
          change M.map (F.map f.unop).op (s.1 _) = s.1 _
          exact sections_property s _) : ((pushforward.{v} φ).obj M).sections)) := by
  refine ⟨fun s s' hss' => ?_, fun σ => ?_⟩
  · have h0 : s.1 (op (F.obj t)) = s'.1 (op (F.obj t)) :=
      congrArg (fun σ : ((pushforward.{v} φ).obj M).sections => σ.1 (op t)) hss'
    refine sections_ext _ _ fun Y => ?_
    rw [← sections_property s (hFt.from Y.unop).op, ← sections_property s' (hFt.from Y.unop).op,
      h0]
  · let a : M.obj (op (F.obj t)) := σ.1 (op t)
    let s : M.sections := M.sectionsMk (fun Y => M.map (hFt.from Y.unop).op a)
      (fun Y Y' g => by
        have e : (hFt.from Y.unop).op ≫ g = (hFt.from Y'.unop).op :=
          Quiver.Hom.unop_inj (hFt.hom_ext _ _)
        exact (ConcreteCategory.congr_hom (M.presheaf.map_comp _ g) a).symm.trans
          (by rw [e]))
    refine ⟨s, sections_ext _ _ fun X => ?_⟩
    change M.map (hFt.from (F.obj X.unop)).op a = σ.1 X
    rw [show hFt.from (F.obj X.unop) = F.map (ht.from X.unop) from hFt.hom_ext _ _]
    exact sections_property σ (ht.from X.unop).op

variable [(pushforward.{u} φ).IsRightAdjoint]

/-- **The pullback of the unit module is the unit module**, when `F` sends a terminal object to a
terminal object: the mate of any map `unit S ⟶ (pushforward φ).obj (unit R)` which is `φ` on
sections is an isomorphism. -/
theorem isIso_homEquiv_symm_unit {t : C} (ht : IsTerminal t) (hFt : IsTerminal (F.obj t))
    (ρ : unit S ⟶ (pushforward.{u} φ).obj (unit R))
    (hρ : ∀ X, ρ.app X (show (unit S).obj X from (1 : S.obj X)) =
      (show (unit R).obj (op (F.obj X.unop)) from (1 : R.obj (op (F.obj X.unop))))) :
    IsIso (((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm ρ) := by
  let adj := pullbackPushforwardAdjunction.{u} φ
  refine isIso_of_coyoneda_map_bijective _ fun M => ?_
  refine (Function.Bijective.of_comp_iff'
    (Equiv.bijective ((adj.homEquiv _ M).trans (unitHomEquiv ((pushforward.{u} φ).obj M)))) _).1 ?_
  refine (congrArg Function.Bijective ?_).mpr
    ((bijective_sectionsRestriction φ ht hFt M).comp (unitHomEquiv M).bijective)
  funext x
  refine sections_ext _ _ fun X => ?_
  simp only [Function.comp_apply, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  change ((pushforward.{u} φ).map x).app X (ρ.app X (show (unit S).obj X from (1 : S.obj X))) =
    x.app (op (F.obj X.unop)) (show (unit R).obj (op (F.obj X.unop)) from
      (1 : R.obj (op (F.obj X.unop))))
  rw [hρ X]
  rfl

end PresheafOfModules
