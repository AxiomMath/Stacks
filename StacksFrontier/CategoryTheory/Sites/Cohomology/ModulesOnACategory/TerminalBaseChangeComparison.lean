module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangeDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction

/-!
# The comparison of a presheaf of modules with the base change of its global sections

Let `C` be a category with a terminal object `X` and `O` a presheaf of rings on `C` with
commutative section rings. For a presheaf of `O`-modules `G` the base-change comparisons of the
restriction maps along the morphisms `U ⟶ X` assemble into a morphism of presheaves of modules

`κ_G : (U ↦ O(U) ⊗_{O(X)} G(X)) ⟶ G`,

natural in `G`. It is an isomorphism exactly when `G` is cartesian over every morphism to `X`,
and it is an isomorphism for the base change presheaf of a module, whose restriction maps are all
base changes.

## Main definitions

* `Stacks.TerminalBaseChange.baseChangeComparison`: the morphism `κ_G`.

## Main results

* `Stacks.TerminalBaseChange.isIso_restrictionBaseChange_baseChangePresheaf`: the base change
  presheaf is cartesian over every morphism.
* `Stacks.TerminalBaseChange.baseChangeComparison_naturality`: `κ` is natural.
* `Stacks.TerminalBaseChange.isIso_baseChangeComparison_of_iso`: `κ_G` is an isomorphism when
  `G` is isomorphic to a base change presheaf.
-/

@[expose] public section

universe t v u r

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.PresheafOfModules

namespace Stacks.TerminalBaseChange

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O]
  {X : C} (hX : IsTerminal X)

open scoped ChangeOfRings in
/-- **The base change presheaf is cartesian over every morphism**: its restriction maps are
base changes. -/
theorem isIso_restrictionBaseChange_baseChangePresheaf (M : ModuleCat.{max t r} (O.obj (op X)))
    {T W : C} (g : W ⟶ T) :
    IsIso (restrictionBaseChange.{u, v, r, t} (R := commPresheaf O)
      ((baseChangePresheaf.{t} O hX).obj M) g.op) := by
  obtain ⟨e, he⟩ := exists_baseChangePresheaf_restrictionEquiv.{t} O hX M g
  have key : ∀ z, restrictionBaseChange.{u, v, r, t} (R := commPresheaf O)
      ((baseChangePresheaf.{t} O hX).obj M) g.op z = e z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s n =>
      have h₁ := restrictionBaseChange_tmul.{u, v, r, t} (R := commPresheaf O)
        ((baseChangePresheaf.{t} O hX).obj M) g.op s n
      refine h₁.trans ?_
      let := (O.map g.op).hom.toAlgebra
      let s' : O.obj (op W) := s
      have h₂ : (s' ⊗ₜ[O.obj (op T)] n : O.obj (op W) ⊗[O.obj (op T)]
          ((baseChangePresheaf.{t} O hX).obj M).obj (op T)) =
          s' • ((1 : O.obj (op W)) ⊗ₜ[O.obj (op T)] n) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      refine Eq.trans ?_ (congrArg e h₂).symm
      exact (congrArg (s' • ·) (he n).symm).trans (e.map_smul s' _).symm
    | add x y hx hy =>
      exact ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add e x y).symm
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨fun a b h => e.injective ((key a).symm.trans (h.trans (key b))),
    fun y => ⟨e.symm y, (key _).trans (e.apply_symm_apply y)⟩⟩

/-- **The comparison of a presheaf of modules with the base change of its sections over the
terminal object**: over `U` it is the base-change comparison `O(U) ⊗_{O(X)} G(X) ⟶ G(U)` of the
restriction map along `U ⟶ X`. -/
noncomputable def baseChangeComparison (G : PresheafOfModules.{max t r} O) :
    (baseChangePresheaf.{t} O hX).obj (G.obj (op X)) ⟶ G where
  app U := restrictionBaseChange.{u, v, r, t} (R := commPresheaf O) G (iota hX U)
  naturality {U V} a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
      refine (congrArg (restrictionBaseChange.{u, v, r, t} (R := commPresheaf O) G
        (iota hX V)).hom (Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul (theta O hX)
          (constModObj.{t} O X (G.obj (op X))) a s m)).trans ?_
      refine (restrictionBaseChange_tmul.{u, v, r, t} (R := commPresheaf O) G (iota hX V)
        ((O.map a).hom s) m).trans ?_
      refine Eq.trans ?_ (congrArg (G.map a) (restrictionBaseChange_tmul.{u, v, r, t}
        (R := commPresheaf O) G (iota hX U) s m)).symm
      have hc : G.map (iota hX U ≫ a) m = G.map (iota hX V) m := by rw [iota_comp]
      exact (congrArg (((O.map a).hom s) • ·)
        ((PresheafOfModules.map_comp_apply G (iota hX U) a m).symm.trans hc).symm).trans
          (PresheafOfModules.map_smul G a s _).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-- The component of `κ_G` over `U` is the base-change comparison of the restriction map along
`U ⟶ X`. -/
lemma baseChangeComparison_app (G : PresheafOfModules.{max t r} O) (U : Cᵒᵖ) :
    (baseChangeComparison.{t} O hX G).app U =
      restrictionBaseChange.{u, v, r, t} (R := commPresheaf O) G (iota hX U) := rfl

/-- **The comparison is natural in the presheaf of modules.** -/
theorem baseChangeComparison_naturality {G G' : PresheafOfModules.{max t r} O} (f : G ⟶ G') :
    (baseChangePresheaf.{t} O hX).map (f.app (op X)) ≫ baseChangeComparison.{t} O hX G' =
      baseChangeComparison.{t} O hX G ≫ f :=
  PresheafOfModules.hom_ext fun U =>
    restrictionBaseChange_naturality.{u, v, r, t} (R := commPresheaf O) f (iota hX U)

/-- **The comparison is an isomorphism as soon as `G` is cartesian over every morphism to the
terminal object.** -/
theorem isIso_baseChangeComparison_of_forall (G : PresheafOfModules.{max t r} O)
    (h : ∀ U : Cᵒᵖ, IsIso (restrictionBaseChange.{u, v, r, t} (R := commPresheaf O) G
      (iota hX U))) :
    IsIso (baseChangeComparison.{t} O hX G) := by
  have h' : ∀ U, IsIso ((baseChangeComparison.{t} O hX G).app U) := h
  exact (PresheafOfModules.isoMk (fun U ↦ asIso ((baseChangeComparison.{t} O hX G).app U))
    fun {_ _} g ↦ (baseChangeComparison.{t} O hX G).naturality g).isIso_hom

/-- **The comparison is an isomorphism for the base change presheaf of a module.** -/
instance isIso_baseChangeComparison_baseChangePresheaf (M : ModuleCat.{max t r} (O.obj (op X))) :
    IsIso (baseChangeComparison.{t} O hX ((baseChangePresheaf.{t} O hX).obj M)) :=
  isIso_baseChangeComparison_of_forall.{t} O hX _ fun U =>
    isIso_restrictionBaseChange_baseChangePresheaf.{t} O hX M (hX.from U.unop)

/-- **The comparison is an isomorphism for a presheaf of modules isomorphic to a base change
presheaf.** -/
theorem isIso_baseChangeComparison_of_iso {G : PresheafOfModules.{max t r} O}
    {M : ModuleCat.{max t r} (O.obj (op X))} (e : G ≅ (baseChangePresheaf.{t} O hX).obj M) :
    IsIso (baseChangeComparison.{t} O hX G) := by
  have : IsIso (e.hom.app (op X)) := ((PresheafOfModules.evaluation _ (op X)).mapIso e).isIso_hom
  have : IsIso (baseChangeComparison.{t} O hX G ≫ e.hom) := by
    rw [← baseChangeComparison_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

/-- An isomorphism from `G` to a base change presheaf makes `G` cartesian over every morphism to
the terminal object. -/
theorem isIso_restrictionBaseChange_of_iso_baseChangePresheaf {G : PresheafOfModules.{max t r} O}
    {M : ModuleCat.{max t r} (O.obj (op X))} (e : G ≅ (baseChangePresheaf.{t} O hX).obj M)
    (U : Cᵒᵖ) :
    IsIso (restrictionBaseChange.{u, v, r, t} (R := commPresheaf O) G (iota hX U)) := by
  have := isIso_baseChangeComparison_of_iso.{t} O hX e
  exact inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ U).map
    (baseChangeComparison.{t} O hX G)))

end Stacks.TerminalBaseChange

end
