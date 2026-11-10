module

public import StacksFrontier.CategoryTheory.Adjunction.PushedForwardTwistedBaseChange

/-!
# Pasting of base change maps of right adjoints

Consider two squares placed side by side, with pullbacks `G₁, G₂` along the bottom, `H₁, H₂`
along the top and vertical functors `Lf, Lf₁, Lf₂`, each with a right adjoint `Rf, Rf₁, Rf₂`
which in turn has a right adjoint `a, a₁, a₂`, and an outer square with pullbacks `Go`, `Ho`
identified with the composites by `cT : Go ≅ G₁ ⋙ G₂` and `cB : H₁ ⋙ H₂ ≅ Ho`. If the
comparison of the composite pullbacks around the outer square is the pasting of the two inner
ones, then so is the base change map of pushforward along pullback, and so is the base change map
`a ⋙ Ho ⟶ Go ⋙ a₂` of the right adjoints.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_eq_of_pullbackComparison_paste` — pasting of the base
  change maps of pushforward along pullback.
* `Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange_app_eq_of_paste` — pasting of the
  base change maps of the right adjoints.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

variable {S S₁ S₂ T T₁ T₂ : Type*} [Category S] [Category S₁] [Category S₂] [Category T]
  [Category T₁] [Category T₂]
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf₁ : S₁ ⥤ T₁} {Rf₁ : T₁ ⥤ S₁} {Lf₂ : S₂ ⥤ T₂} {Rf₂ : T₂ ⥤ S₂}
  (adjf : Lf ⊣ Rf) (adjf₁ : Lf₁ ⊣ Rf₁) (adjf₂ : Lf₂ ⊣ Rf₂)
  {G₁ : S ⥤ S₁} {G₂ : S₁ ⥤ S₂} {Go : S ⥤ S₂} {H₁ : T ⥤ T₁} {H₂ : T₁ ⥤ T₂} {Ho : T ⥤ T₂}
  {Lc₁ : S ⥤ T₁} {Lc₂ : S₁ ⥤ T₂} {Lco : S ⥤ T₂}
  (eg₁ : G₁ ⋙ Lf₁ ≅ Lc₁) (ef₁ : Lf ⋙ H₁ ≅ Lc₁) (eg₂ : G₂ ⋙ Lf₂ ≅ Lc₂) (ef₂ : Lf₁ ⋙ H₂ ≅ Lc₂)
  (ego : Go ⋙ Lf₂ ≅ Lco) (efo : Lf ⋙ Ho ≅ Lco)
  (cT : Go ≅ G₁ ⋙ G₂) (cB : H₁ ⋙ H₂ ≅ Ho)

/-- The comparison of the composite pullbacks around the outer square is the pasting of the two
inner comparisons, conjugated by `cT` and `cB`. -/
def PullbackComparisonPaste : Prop :=
  ∀ K : S, (ego.hom ≫ efo.inv).app K =
    Lf₂.map (cT.hom.app K) ≫ (eg₂.hom ≫ ef₂.inv).app (G₁.obj K) ≫
      H₂.map ((eg₁.hom ≫ ef₁.inv).app K) ≫ cB.hom.app (Lf.obj K)

/-- **Pasting of the base change maps of pushforward along pullback.** -/
theorem map_eq_of_pullbackComparison_paste
    (hpc : PullbackComparisonPaste eg₁ ef₁ eg₂ ef₂ ego efo cT cB) (M : T) :
    map adjf adjf₂ ego efo M =
      cT.hom.app (Rf.obj M) ≫ G₂.map (map adjf adjf₁ eg₁ ef₁ M) ≫
        map adjf₁ adjf₂ eg₂ ef₂ (H₁.obj M) ≫ Rf₂.map (cB.hom.app M) := by
  apply (adjf₂.homEquiv _ _).symm.injective
  rw [homEquiv_symm_map, Adjunction.homEquiv_counit]
  have h₂ := homEquiv_symm_map adjf₁ adjf₂ eg₂ ef₂ (H₁.obj M)
  rw [Adjunction.homEquiv_counit] at h₂
  have h₁ := homEquiv_symm_map adjf adjf₁ eg₁ ef₁ M
  rw [Adjunction.homEquiv_counit] at h₁
  have hn := (eg₂.hom ≫ ef₂.inv).naturality (map adjf adjf₁ eg₁ ef₁ M)
  simp only [Functor.comp_map, Functor.comp_obj, NatTrans.comp_app, Category.assoc] at hn
  have hcB := cB.hom.naturality (adjf.counit.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hcB
  have hp := hpc (Rf.obj M)
  simp only [NatTrans.comp_app] at hp h₂ hn
  simp only [Functor.map_comp, Category.assoc]
  symm
  calc Lf₂.map (cT.hom.app (Rf.obj M)) ≫ Lf₂.map (G₂.map (map adjf adjf₁ eg₁ ef₁ M)) ≫
        Lf₂.map (map adjf₁ adjf₂ eg₂ ef₂ (H₁.obj M)) ≫ Lf₂.map (Rf₂.map (cB.hom.app M)) ≫
          adjf₂.counit.app (Ho.obj M)
      = Lf₂.map (cT.hom.app (Rf.obj M)) ≫ Lf₂.map (G₂.map (map adjf adjf₁ eg₁ ef₁ M)) ≫
        (Lf₂.map (map adjf₁ adjf₂ eg₂ ef₂ (H₁.obj M)) ≫ adjf₂.counit.app (H₂.obj (H₁.obj M))) ≫
          cB.hom.app M := by
        rw [← Functor.comp_map Rf₂ Lf₂, adjf₂.counit.naturality]
        simp
    _ = Lf₂.map (cT.hom.app (Rf.obj M)) ≫ (Lf₂.map (G₂.map (map adjf adjf₁ eg₁ ef₁ M)) ≫
          eg₂.hom.app (Rf₁.obj (H₁.obj M)) ≫ ef₂.inv.app (Rf₁.obj (H₁.obj M))) ≫
          H₂.map (adjf₁.counit.app (H₁.obj M)) ≫ cB.hom.app M := by
        rw [h₂]; simp
    _ = Lf₂.map (cT.hom.app (Rf.obj M)) ≫ eg₂.hom.app (G₁.obj (Rf.obj M)) ≫
          ef₂.inv.app (G₁.obj (Rf.obj M)) ≫
          H₂.map (Lf₁.map (map adjf adjf₁ eg₁ ef₁ M) ≫ adjf₁.counit.app (H₁.obj M)) ≫
            cB.hom.app M := by
        simp only [Category.assoc]
        rw [reassoc_of% hn]; simp
    _ = Lf₂.map (cT.hom.app (Rf.obj M)) ≫ eg₂.hom.app (G₁.obj (Rf.obj M)) ≫
          ef₂.inv.app (G₁.obj (Rf.obj M)) ≫
          H₂.map (eg₁.hom.app (Rf.obj M) ≫ ef₁.inv.app (Rf.obj M)) ≫
          (H₂.map (H₁.map (adjf.counit.app M)) ≫ cB.hom.app M) := by
        rw [h₁]; simp
    _ = _ := by
        simp only [Functor.id_obj]
        rw [hcB, ← Category.assoc (ego.hom.app _), hp]
        simp

section RightAdjoint

variable {a : S ⥤ T} {a₁ : S₁ ⥤ T₁} {a₂ : S₂ ⥤ T₂} (adja : Rf ⊣ a) (adja₁ : Rf₁ ⊣ a₁)
  (adja₂ : Rf₂ ⊣ a₂)
  {RG₁ : S₁ ⥤ S} {RG₂ : S₂ ⥤ S₁} {RGo : S₂ ⥤ S} {RH₁ : T₁ ⥤ T} {RH₂ : T₂ ⥤ T₁} {RHo : T₂ ⥤ T}
  (adjG₁ : G₁ ⊣ RG₁) (adjG₂ : G₂ ⊣ RG₂) (adjGo : Go ⊣ RGo) (adjH₁ : H₁ ⊣ RH₁)
  (adjH₂ : H₂ ⊣ RH₂) (adjHo : Ho ⊣ RHo)
  [IsIso (twoSquare adjf adjf₁ eg₁ ef₁)] [IsIso (twoSquare adjf₁ adjf₂ eg₂ ef₂)]
  [IsIso (twoSquare adjf adjf₂ ego efo)]

/-- **Pasting of the base change maps of the right adjoints.** If the comparison of the composite
pullbacks around the outer square is the pasting of the two inner ones, the base change map
`a ⋙ Ho ⟶ Go ⋙ a₂` of the outer square at `K` is the base change map of the first square
followed, after `H₂`, by that of the second, conjugated by `cB` and `cT`. -/
theorem rightAdjointBaseChange_app_eq_of_paste
    (hpc : PullbackComparisonPaste eg₁ ef₁ eg₂ ef₂ ego efo cT cB) (K : S) :
    haveI := isIso_rightAdjointSquare adjf adjf₁ adjG₁ adjH₁ eg₁ ef₁ adja adja₁
    haveI := isIso_rightAdjointSquare adjf₁ adjf₂ adjG₂ adjH₂ eg₂ ef₂ adja₁ adja₂
    haveI := isIso_rightAdjointSquare adjf adjf₂ adjGo adjHo ego efo adja adja₂
    (rightAdjointBaseChange adjf adjf₂ adjGo adjHo ego efo adja adja₂).app K =
      cB.inv.app (a.obj K) ≫
        H₂.map ((rightAdjointBaseChange adjf adjf₁ adjG₁ adjH₁ eg₁ ef₁ adja adja₁).app K) ≫
        (rightAdjointBaseChange adjf₁ adjf₂ adjG₂ adjH₂ eg₂ ef₂ adja₁ adja₂).app
          (G₁.obj K) ≫
        a₂.map (cT.inv.app K) := by
  have := isIso_rightAdjointSquare adjf adjf₁ adjG₁ adjH₁ eg₁ ef₁ adja adja₁
  have := isIso_rightAdjointSquare adjf₁ adjf₂ adjG₂ adjH₂ eg₂ ef₂ adja₁ adja₂
  have := isIso_rightAdjointSquare adjf adjf₂ adjGo adjHo ego efo adja adja₂
  apply (adja₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    map_rightAdjointBaseChange_comp_counit]
  have hβ₁ := map_rightAdjointBaseChange_comp_counit adjf adjf₁ adjG₁ adjH₁ eg₁ ef₁ adja adja₁ K
  have hβ₂ := map_rightAdjointBaseChange_comp_counit adjf₁ adjf₂ adjG₂ adjH₂ eg₂ ef₂ adja₁ adja₂
    (G₁.obj K)
  -- the inverse base change map of the outer square, componentwise
  have hbc : ∀ M : T, (inv (twoSquare adjf adjf₂ ego efo)).app M =
      Rf₂.map (cB.inv.app M) ≫ (inv (twoSquare adjf₁ adjf₂ eg₂ ef₂)).app (H₁.obj M) ≫
        G₂.map ((inv (twoSquare adjf adjf₁ eg₁ ef₁)).app M) ≫ cT.inv.app (Rf.obj M) := by
    intro M
    rw [NatIso.isIso_inv_app, NatIso.isIso_inv_app, NatIso.isIso_inv_app]
    apply IsIso.inv_eq_of_hom_inv_id
    change map adjf adjf₂ ego efo M ≫ _ = _
    rw [map_eq_of_pullbackComparison_paste adjf adjf₁ adjf₂ eg₁ ef₁ eg₂ ef₂ ego efo cT cB hpc M]
    simp [map, ← Rf₂.map_comp_assoc]
  have hn₂ := (inv (twoSquare adjf₁ adjf₂ eg₂ ef₂)).naturality
    ((rightAdjointBaseChange adjf adjf₁ adjG₁ adjH₁ eg₁ ef₁ adja adja₁).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn₂
  have hcT := cT.inv.naturality (adja.counit.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hcT
  have he := adja₂.counit.naturality (cT.inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at he
  rw [hbc]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [he, reassoc_of% hβ₂, reassoc_of% hn₂, ← G₂.map_comp_assoc, hβ₁, G₂.map_comp,
    Category.assoc, hcT]

/-- **Two-out-of-three for pasted base change maps of right adjoints.** If the base change map of
the second square is invertible at `G₁ K`, then that of the outer square is invertible at `K`
exactly when `H₂` of that of the first square is. -/
theorem isIso_rightAdjointBaseChange_app_iff_of_paste
    (hpc : PullbackComparisonPaste eg₁ ef₁ eg₂ ef₂ ego efo cT cB) (K : S) :
    haveI := isIso_rightAdjointSquare adjf adjf₁ adjG₁ adjH₁ eg₁ ef₁ adja adja₁
    haveI := isIso_rightAdjointSquare adjf₁ adjf₂ adjG₂ adjH₂ eg₂ ef₂ adja₁ adja₂
    haveI := isIso_rightAdjointSquare adjf adjf₂ adjGo adjHo ego efo adja adja₂
    IsIso ((rightAdjointBaseChange adjf₁ adjf₂ adjG₂ adjH₂ eg₂ ef₂ adja₁ adja₂).app
      (G₁.obj K)) →
    (IsIso ((rightAdjointBaseChange adjf adjf₂ adjGo adjHo ego efo adja adja₂).app K) ↔
      IsIso (H₂.map
        ((rightAdjointBaseChange adjf adjf₁ adjG₁ adjH₁ eg₁ ef₁ adja adja₁).app K))) := by
  have := isIso_rightAdjointSquare adjf adjf₁ adjG₁ adjH₁ eg₁ ef₁ adja adja₁
  have := isIso_rightAdjointSquare adjf₁ adjf₂ adjG₂ adjH₂ eg₂ ef₂ adja₁ adja₂
  have := isIso_rightAdjointSquare adjf adjf₂ adjGo adjHo ego efo adja adja₂
  intro h₂
  rw [rightAdjointBaseChange_app_eq_of_paste adjf adjf₁ adjf₂ eg₁ ef₁ eg₂ ef₂ ego efo cT cB adja
    adja₁ adja₂ adjG₁ adjG₂ adjGo adjH₁ adjH₂ adjHo hpc K]
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

end RightAdjoint

end Stacks.CategoryTheory.BaseChange
