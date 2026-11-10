module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangeCorepresentation
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-!
# Flat base change on the sections over a terminal object

Let `ρ : O ⟶ b_* O'` be a morphism of ringed categories along a functor `b : C ⥤ D` carrying a
terminal object `X` to a terminal object, `G`, `H` modules on `C` and `D` and `d : G ⟶ b_* H`.
If the mate `b^* G ⟶ H` of `d` is locally bijective, both modules are locally their base changes
from the terminal objects, `b_*` preserves sheaves and every module over `O'(b X)` is the module
of sections of a sheaf, then the base change `O'(b X) ⊗_{O(X)} G(X) ⟶ H(b X)` of `d` is an
isomorphism. This is the sections-level content of the flat base change property of Stacks 0762
over affine schemes: no description of the presheaf pullback `b^*` is used, only its adjointness.

## Main results

* `Stacks.TerminalBaseChange.isIso_extendScalars_of_isLocallyBijective_pullbackComparison`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v₁ u₁ v₂ u₂ r

namespace Stacks.TerminalBaseChange

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max t r}]
  {O : Cᵒᵖ ⥤ RingCat.{r}} [CommSections O] {O' : Dᵒᵖ ⥤ RingCat.{r}} [CommSections O']
  {X : C} (hX : IsTerminal X) {b : C ⥤ D} (hbX : IsTerminal (b.obj X))
  (ρ : O ⟶ b.op ⋙ O') [(PresheafOfModules.pushforward.{max t r} ρ).IsRightAdjoint]

/-- The sections of a presheaf of rings with commutative sections, restricted along a functor. -/
instance commRing_comp_obj (U : Cᵒᵖ) : CommRing ((b.op ⋙ O').obj U) :=
  commRingObj O' (b.op.obj U)

/-- **Flat base change on the sections over a terminal object.** Let `ρ : O ⟶ b_* O'` be a
morphism of ringed categories along `b : C ⥤ D` carrying the terminal object `X` to a terminal
object, let `G` and `H` be modules on the two sides and `d : G ⟶ b_* H` a morphism, and suppose:

* the mate `c : b^* G ⟶ H` of `d` is locally bijective;
* `G` and `H` are locally their base changes from the terminal objects (the counits of the base
  change adjunctions are locally bijective), and `H` is a sheaf;
* `b_*` carries sheaves to sheaves, and every `O'(b X)`-module is the module of sections over
  `b X` of some sheaf of `O'`-modules.

Then the base change `O'(b X) ⊗_{O(X)} G(X) ⟶ H(b X)` of `d` over `X` is an isomorphism.

Morphisms out of `H` into a sheaf `Q` are on the one hand their components over `b X`, and on
the other hand, through `c` and the adjunction, morphisms `G ⟶ b_* Q`, that is morphisms
`G(X) ⟶ Q(b X)` over `O(X)`. So the base change of `d` induces a bijection on morphisms into
`Q(b X)` for every sheaf `Q`, and every module is such a `Q(b X)`. -/
theorem isIso_extendScalars_of_isLocallyBijective_pullbackComparison
    (G : PresheafOfModules.{max t r} O) (H : PresheafOfModules.{max t r} O')
    (d : G ⟶ (PresheafOfModules.pushforward.{max t r} ρ).obj H)
    [PresheafOfModules.IsLocallySurjective K
      (((PresheafOfModules.pullbackPushforwardAdjunction.{max t r} ρ).homEquiv G H).symm d)]
    [PresheafOfModules.IsLocallyInjective K
      (((PresheafOfModules.pullbackPushforwardAdjunction.{max t r} ρ).homEquiv G H).symm d)]
    [PresheafOfModules.IsLocallySurjective J ((baseChangeAdj.{t} O hX).counit.app G)]
    [PresheafOfModules.IsLocallyInjective J ((baseChangeAdj.{t} O hX).counit.app G)]
    [PresheafOfModules.IsLocallySurjective K ((baseChangeAdj.{t} O' hbX).counit.app H)]
    [PresheafOfModules.IsLocallyInjective K ((baseChangeAdj.{t} O' hbX).counit.app H)]
    (hpush : ∀ Q : PresheafOfModules.{max t r} O', Presheaf.IsSheaf K Q.presheaf →
      Presheaf.IsSheaf J ((PresheafOfModules.pushforward.{max t r} ρ).obj Q).presheaf)
    (htilde : ∀ Y : ModuleCat.{max t r} (O'.obj (Opposite.op (b.obj X))),
      ∃ Q : PresheafOfModules.{max t r} O', Presheaf.IsSheaf K Q.presheaf ∧
        Nonempty (Q.obj (Opposite.op (b.obj X)) ≅ Y)) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj (ρ.app (Opposite.op X)).hom).homEquiv _ _).symm
      (d.app (Opposite.op X))) := by
  set δ := ((ModuleCat.extendRestrictScalarsAdj (ρ.app (Opposite.op X)).hom).homEquiv _ _).symm
      (d.app (Opposite.op X)) with hδ
  -- bijectivity on morphisms into the sections of a sheaf over `b X`
  have key : ∀ Q : PresheafOfModules.{max t r} O', Presheaf.IsSheaf K Q.presheaf →
      Function.Bijective (fun ψ : H.obj (Opposite.op (b.obj X)) ⟶ Q.obj (Opposite.op (b.obj X)) =>
        δ ≫ ψ) := by
    intro Q hQ
    have hΦ := bijective_app_of_isLocallyBijective_counit.{t} O' hbX H Q hQ
    have hG := bijective_app_of_isLocallyBijective_counit.{t} O hX G
      ((PresheafOfModules.pushforward.{max t r} ρ).obj Q) (hpush Q hQ)
    let adj := PresheafOfModules.pullbackPushforwardAdjunction.{max t r} ρ
    let e₁ := PresheafOfModules.homEquivOfIsLocallyBijective
      (f := (adj.homEquiv G H).symm d) hQ
    let e₂ := adj.homEquiv G Q
    -- the composite `h ↦ d_X ≫ h_{b X}`
    let κ : (H.obj (Opposite.op (b.obj X)) ⟶ Q.obj (Opposite.op (b.obj X))) →
        (G.obj (Opposite.op X) ⟶
          (ModuleCat.restrictScalars (ρ.app (Opposite.op X)).hom).obj
            (Q.obj (Opposite.op (b.obj X)))) :=
      fun ψ => d.app (Opposite.op X) ≫ (ModuleCat.restrictScalars (ρ.app (Opposite.op X)).hom).map ψ
    have hΨ : κ ∘ (fun g : H ⟶ Q => g.app (Opposite.op (b.obj X))) =
        (fun g : G ⟶ (PresheafOfModules.pushforward.{max t r} ρ).obj Q => g.app (Opposite.op X))
          ∘ e₂ ∘ e₁ := by
      funext g
      change d.app (Opposite.op X) ≫ _ = (adj.homEquiv G Q ((adj.homEquiv G H).symm d ≫ g)).app _
      rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
      rfl
    have hκ : Function.Bijective κ := by
      have h2 : Function.Bijective (κ ∘ (fun g : H ⟶ Q => g.app (Opposite.op (b.obj X)))) := by
        rw [hΨ]; exact hG.comp (e₂.bijective.comp e₁.bijective)
      exact (Function.Bijective.of_comp_iff κ hΦ).mp h2
    have hcomp : (fun ψ : H.obj (Opposite.op (b.obj X)) ⟶ Q.obj (Opposite.op (b.obj X)) =>
        δ ≫ ψ) =
          ((ModuleCat.extendRestrictScalarsAdj (ρ.app (Opposite.op X)).hom).homEquiv _ _).symm
          ∘ κ := by
      funext ψ
      change δ ≫ ψ = ((ModuleCat.extendRestrictScalarsAdj _).homEquiv _ _).symm
        (d.app (Opposite.op X) ≫ (ModuleCat.restrictScalars _).map ψ)
      rw [hδ]
      exact (Adjunction.homEquiv_naturality_right_symm
        (ModuleCat.extendRestrictScalarsAdj (ρ.app (Opposite.op X)).hom) _ ψ).symm
    rw [hcomp]
    exact (Equiv.bijective _).comp hκ
  refine isIso_of_coyoneda_map_bijective δ (fun Y => ?_)
  obtain ⟨Q, hQ, ⟨e⟩⟩ := htilde Y
  have h := key Q hQ
  have he : (fun ψ : H.obj (Opposite.op (b.obj X)) ⟶ Y => δ ≫ ψ) =
      (Iso.homCongr (Iso.refl _) e) ∘ (fun ψ : H.obj (Opposite.op (b.obj X)) ⟶
        Q.obj (Opposite.op (b.obj X)) => δ ≫ ψ) ∘ (Iso.homCongr (Iso.refl _) e.symm) := by
    funext ψ
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom,
      Category.id_comp]
    ext x
    exact (ConcreteCategory.congr_hom e.inv_hom_id _).symm
  exact (congrArg Function.Bijective he).mpr
    ((Equiv.bijective _).comp (h.comp (Equiv.bijective _)))

end Stacks.TerminalBaseChange
