module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.NiceChart
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Uniqueness
public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.NiceChartSquare
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismGlue

/-!
# Rules of maps of Section 0FL7 and their uniqueness
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict

/-- **A rule of maps of Section 0FL7**: to every locally quasi-finite syntomic morphism of schemes
`f : Y ⟶ X` it assigns maps `c^p_{Y/X} : Ω^p_{Y/ℤ} ⟶ f^*Ω^p_{X/ℤ} ⊗_{𝒪_Y} det(NL_{Y/X})` for
`p ≥ 0`. -/
abbrev GarelRule : Type (u + 1) :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : Y ⟶ X) (hf : Syntomic f), LocallyQuasiFinite f →
    f.GarelMaps (f.detNL hf)

namespace GarelRule

variable (c : GarelRule.{u})

/-- **Condition (0H9C)** on a rule: `c^0_{Y/X}(1) = δ(NL_{Y/X})` for every `Y/X`. -/
def IsNormalized : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : Y ⟶ X) (hf : Syntomic f) (hq : LocallyQuasiFinite f),
    (c f hf hq).IsNormalized (haveI := hq; f.deltaNL hf)

/-- **Condition (0H9D)** on a rule: `c^{q+p}_{Y/X}(ω ∧ η) = ω ∧ c^p_{Y/X}(η)` for every `Y/X`. -/
def IsMultiplicative : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : Y ⟶ X) (hf : Syntomic f) (hq : LocallyQuasiFinite f),
    (c f hf hq).IsMultiplicative

/-- **Condition (0H9E)** on a rule: for every commutative square `b ≫ f = f' ≫ a` of locally
quasi-finite syntomic morphisms which induces an isomorphism of `Y'` with an open subscheme of
`X' ×_X Y`, the maps of `f` and of `f'` are compatible as in Lemma 0H9G, through the
identification `b^*det(NL_{Y/X}) ≅ det(NL_{Y'/X'})` of Discriminants, Section 0FKB. This
includes restriction to opens. -/
def IsCompatible : Prop :=
  ∀ ⦃X Y X' Y' : Scheme.{u}⦄ (f : Y ⟶ X) (f' : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : b ≫ f = f' ≫ a) [IsOpenImmersion (pullback.lift b f' w)] (hf : Syntomic f)
    (hq : LocallyQuasiFinite f) (hf' : Syntomic f') (hq' : LocallyQuasiFinite f'),
    Scheme.Hom.GarelMaps.IsCompatible w (Scheme.Hom.detNLPullbackIso w hf hf').hom
      (c f hf hq) (c f' hf' hq')

end GarelRule

namespace Scheme.Hom

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y}

/-- The base change arrow of Lemma 0H9G is an isomorphism when `a` is étale and `e` is an
isomorphism. -/
instance isIso_twistedPullbackFormsBaseChange (L : Y.Modules) {L' : Y'.Modules}
    (w : b ≫ f = f' ≫ a) (e : (Scheme.Modules.pullback b).obj L ⟶ L') [IsIso e] [Etale a]
    (p : ℕ) : IsIso (twistedPullbackFormsBaseChange L w e p) := by
  have : IsIso (pullbackFormsBaseChange w (p : ℤ)) := by
    unfold pullbackFormsBaseChange
    infer_instance
  have h₁ : IsIso (MonoidalCategoryStruct.tensorHom (C := Y'.Modules)
      (pullbackFormsBaseChange w (p : ℤ)) e) :=
    MonoidalCategory.tensor_isIso (C := Y'.Modules) _ _
  have h₀ := Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison b.toLRSHom.toShHom
    (f.pullbackForms p) L
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₀ h₁

/-- Two families of maps compatible along a square with étale lower edge and invertible `e` with
the same family upstairs agree after pullback along the upper edge. -/
theorem GarelMaps.pullback_map_eq_of_isCompatible {L : Y.Modules} {L' : Y'.Modules}
    (w : b ≫ f = f' ≫ a) (e : (Scheme.Modules.pullback b).obj L ⟶ L') [IsIso e] [Etale a]
    {c₁ c₂ : f.GarelMaps L} {c' : f'.GarelMaps L'} (h₁ : GarelMaps.IsCompatible w e c₁ c')
    (h₂ : GarelMaps.IsCompatible w e c₂ c') (p : ℕ) :
    (Scheme.Modules.pullback b).map (c₁ p) = (Scheme.Modules.pullback b).map (c₂ p) := by
  rw [← cancel_mono (twistedPullbackFormsBaseChange L w e p), h₁ p, h₂ p]

open Stacks.PullbackTensorCoherence in
/-- The inverse right unitor of Tag 01CA on local sections: `m ↦ m ⊗ 1`. -/
theorem _root_.Stacks.PullbackTensorCoherence.rightUnitor_inv_tmul {Z : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z))
    (V : (TopologicalSpace.Opens Z.carrier)ᵒᵖ) (m : M.val.obj V) :
    (ρ_ M).inv.val.app V m =
      tmul Z M (𝟙_ (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z))) V m
        (oneSec Z V) :=
  (congrArg ((ρ_ M).inv.val.app V)
      ((rightUnitor_hom_tmul V m 1).trans (one_smul _ m)).symm).trans
    (Stacks.SheafOfModules.inv_val_app_hom_val_app (ρ_ M) V _)

open Stacks.PullbackTensorCoherence in
/-- **The maps of Section 0FL7 on pulled back forms are multiplication by `δ`** (Stacks Tag 0FLA,
"in particular"): for `c` satisfying (0H9C) and (0H9D), the composite of
`f^*Ω^p_{X/ℤ} ⟶ Ω^p_{Y/ℤ}` with `c^p` is `ω ↦ ω ⊗ δ`. -/
theorem GarelMaps.absoluteFormsMap_comp {L : Y.Modules} {δ : Γ(L, ⊤)} {c : f.GarelMaps L}
    (hn : c.IsNormalized δ) (hm : c.IsMultiplicative) (p : ℕ) :
    f.absoluteFormsMap p ≫ c p =
      (ρ_ (f.pullbackForms p)).inv ≫ (f.pullbackForms p ◁ Scheme.Modules.globalSectionHom L δ) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  ext ω
  change (c p).val.app V ((f.absoluteFormsMap p).val.app V ω) =
    (f.pullbackForms p ◁ Scheme.Modules.globalSectionHom L δ).val.app V
      ((ρ_ (f.pullbackForms p)).inv.val.app V ω)
  rw [GarelMaps.app_absoluteFormsMap hn hm p V.unop ω]
  refine Eq.symm ((congrArg _ (rightUnitor_inv_tmul (f.pullbackForms p) V ω)).trans
    ((whiskerLeft_tmul _ V ω _).trans ?_))
  refine congrArg (tmul Y.toRingedSpace (f.pullbackForms p) L V ω) ?_
  refine Eq.trans ?_ ((PresheafOfModules.naturality_apply
    (Scheme.Modules.globalSectionHom L δ).val (homOfLE (le_top : V.unop ≤ ⊤)).op
    (oneSec Y.toRingedSpace (op ⊤))).trans
      (congrArg _ (Scheme.Modules.globalSectionHom_val_app_oneSec L δ)))
  congr 1
  exact (map_one ((Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.map
    (homOfLE (le_top : V.unop ≤ ⊤)).op).hom).symm

end Scheme.Hom

namespace GarelRule

open Scheme.Hom

/-- **Uniqueness in Stacks Tag 0FLA**: two rules satisfying (0H9C), (0H9D) and (0H9E) agree.

Around every point `y` of `Y` there is a chart `V ⊆ Y`, `U ⊆ X` and a square from `V/U` to a
nice chart `N/M` of the universal family which induces an isomorphism of `V` with an open of
`U ×_M N`. On `N/M` the two rules agree by rigidity; by (0H9E) and Lemma 0H9G they agree on
`V/U`; by (0H9E) for the inclusion of `V/U` into `Y/X` they agree on `V`. -/
theorem eq_of_isNormalized_of_isMultiplicative_of_isCompatible {c c' : GarelRule.{u}}
    (h₁ : c.IsNormalized) (h₂ : c.IsMultiplicative) (h₃ : c.IsCompatible)
    (h₁' : c'.IsNormalized) (h₂' : c'.IsMultiplicative) (h₃' : c'.IsCompatible) : c = c' := by
  funext X Y f hf hq p
  have key (y : Y) : ∃ V : Y.Opens, y ∈ V ∧
      (Scheme.Modules.pullback V.ι).map (c f hf hq p) =
        (Scheme.Modules.pullback V.ι).map (c' f hf hq p) := by
    obtain ⟨U, V, e, σ, B₀, _, _, n, P₀, h, a, b, w, hy, hopen, hdom, hJ, hqf, hsyn⟩ :=
      exists_niceChartSquare f hf y
    refine ⟨V.1, hy, ?_⟩
    have wr : V.1.ι ≫ f = f.resLE U.1 V.1 e ≫ U.1.ι := (resLE_comp_ι f e).symm
    have : IsOpenImmersion (pullback.lift V.1.ι (f.resLE U.1 V.1 e) wr) :=
      isOpenImmersion_lift_resLE f e
    have hg := syntomic_of_isOpenImmersion_lift wr hf
    have hqg := locallyQuasiFinite_of_isOpenImmersion_lift wr
    have hφ := NiceChart.syntomic_hom σ h
    have hqφ := NiceChart.locallyQuasiFinite_hom σ h
    have hN : c (NiceChart.hom σ h) hφ hqφ = c' (NiceChart.hom σ h) hφ hqφ := funext fun q =>
      GarelMaps.eq_of_niceChart (σ := σ) (h := h) (P₀ := P₀) hJ (h₁ _ hφ hqφ) (h₂ _ hφ hqφ)
        (h₁' _ hφ hqφ) (h₂' _ hφ hqφ) q
    have hV : c (f.resLE U.1 V.1 e) hg hqg = c' (f.resLE U.1 V.1 e) hg hqg :=
      GarelMaps.eq_of_isMultiplicative_of_isCompatible w (detNLPullbackIso w hφ hg).hom
        (h₂ _ hg hqg) (h₂' _ hg hqg) (h₃ _ _ a b w hφ hqφ hg hqg)
        (hN ▸ h₃' _ _ a b w hφ hqφ hg hqg)
    exact GarelMaps.pullback_map_eq_of_isCompatible wr (detNLPullbackIso wr hf hg).hom
      (h₃ f _ U.1.ι V.1.ι wr hf hq hg hqg) (hV ▸ h₃' f _ U.1.ι V.1.ι wr hf hq hg hqg) p
  choose W hW heq using key
  exact Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullback_cover W
    (fun y => ⟨y, hW y⟩) heq

end GarelRule

end AlgebraicGeometry

end
