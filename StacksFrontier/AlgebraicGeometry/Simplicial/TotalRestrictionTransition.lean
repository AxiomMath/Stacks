module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableTransitionSections
public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSimplicialSystem

/-!
# The transitions of a restriction to `(C/K)_total` fix sections

Let `(C, O_C)` be a ringed site and `K` a simplicial semi-representable object of `C`. Restricting
a sheaf of `O_C`-modules `N` along the localization functor `j_total` gives a sheaf of modules on
the total site `(C/K)_total` of Stacks 0D9W, whose sections over an object `V ⟶ U_{n,i}` of
`C/K_n` are the sections of `N` over `V`. Its transitions `f_φ^*(N|)_m ⟶ (N|)_n` of Stacks 09WF,
read through restriction along the relocalization functor `r_φ`, are restrictions along the
cross-fibre arrows `(φ, 𝟙)` of the total category, whose images in `C` are identities. So they
fix sections.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.totalRestriction`: restriction of sheaves of
  `O_C`-modules along `j_total`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.totalRestriction_transition_fixesSections`: the
  transitions of a restriction along `j_total` fix sections.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SemiRepresentable Stacks.Sheaves.ToposPullback

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

/-- In the category of types, a composite of two transports and an identity moves no element. -/
theorem heq_types_eqToHom_id_eqToHom_apply {α β γ : Type u} (h₁ : α = β) (h₂ : β = γ) (x : α) :
    HEq (ConcreteCategory.hom (eqToHom h₁ ≫ 𝟙 β ≫ eqToHom h₂ : α ⟶ γ) x) x := by
  subst h₁
  subst h₂
  rfl

open CategoryTheory.SimplicialSiteSituation

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- **Restriction of sheaves of `O_C`-modules along the localization functor `j_total`**, with
values in the sheaves of modules over the restricted structure sheaf of the total site. -/
abbrev totalRestriction :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} ((situation X.J K).totalRingSheaf (structureSheaf X K)) :=
  @restrictionModules _ _ _ _ (situation X.J K).totalTopology X.J (totalForget K)
    (totalForget_isContinuous X.J K) (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **The transitions of a restriction along `j_total` fix sections.** For a sheaf of
`O_C`-modules `N`, the transition `f_φ^*(N|)_m ⟶ (N|)_n` of Stacks 09WF of its restriction to the
total site, read through the identification of `f_φ^*` with restriction along `r_φ`, is the
identity on sections: on sections it is restriction along the cross-fibre arrow `(φ, 𝟙)`, whose
image under `j_total` is an identity. -/
theorem totalRestriction_transition_fixesSections {m n : SimplexCategory} (φ : m ⟶ n)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.FixesSections
      ((transitionPullbackModulesIso X K φ).inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj
            ((totalRestriction X K).obj N)) ≫
        ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app
          ((totalRestriction X K).obj N)) := by
  intro V x
  have h₁ := congrArg (fun t => t.hom.app V x)
    (moduleSheafFunctor_map_transitionPullbackModulesIso_inv_comp_transition X K φ
      ((totalRestriction X K).obj N))
  have h₂ := congrArg (fun t => t x)
    (transitionSheafAdjunction_homEquiv_symm_restrictTransition_hom_app X K φ
      (Sheaf.moduleSheaf.{u, u, u} ((situation X.J K).totalRingSheaf (structureSheaf X K))
        ((totalRestriction X K).obj N)) V.unop)
  have h₀ : (moduleSheafTransitionRestrictionIso X K φ).hom.app
        (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj
          ((totalRestriction X K).obj N)) ≫
      (componentRing X K n).moduleSheafFunctor.map
        ((transitionPullbackModulesIso X K φ).inv.app
            (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj
              ((totalRestriction X K).obj N)) ≫
          ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app
            ((totalRestriction X K).obj N)) =
      (componentRing X K n).moduleSheafFunctor.map
        ((transitionPullbackModulesIso X K φ).inv.app
            (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj
              ((totalRestriction X K).obj N)) ≫
          ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app
            ((totalRestriction X K).obj N)) :=
    Category.id_comp _
  rw [h₀] at h₁
  have h₅ : (totalForget K).map
      ((Grothendieck.ιNatTrans (F := (simplicialSite X.J K).underlying) φ.op).app V.unop) =
        𝟙 _ :=
    (totalForget_map K _).trans (CategoryTheory.Functor.map_id _ _)
  have e : (Sheaf.moduleSheaf.{u, u, u} ((situation X.J K).totalRingSheaf (structureSheaf X K))
      ((totalRestriction X K).obj N)).obj =
      (totalForget K).op ⋙ (Sheaf.moduleSheaf.{u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N).obj := rfl
  have h₉ := Functor.congr_hom e
    ((Grothendieck.ιNatTrans (F := (simplicialSite X.J K).underlying) φ.op).app (unop V)).op
  refine HEq.trans (heq_of_eq (h₁.trans h₂)) ?_
  have h₁₀ : ((totalForget K).op ⋙ (Sheaf.moduleSheaf.{u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N).obj).map
      ((Grothendieck.ιNatTrans (F := (simplicialSite X.J K).underlying) φ.op).app (unop V)).op =
        𝟙 _ := by
    show (Sheaf.moduleSheaf.{u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N).obj.map
      ((totalForget K).map
        ((Grothendieck.ιNatTrans (F := (simplicialSite X.J K).underlying) φ.op).app
          (unop V))).op = 𝟙 _
    rw [h₅]
    exact CategoryTheory.Functor.map_id _ _
  rw [h₉, h₁₀]
  exact heq_types_eqToHom_id_eqToHom_apply _ _ x

end CategoryTheory.SimplicialSemiRepresentable

end
