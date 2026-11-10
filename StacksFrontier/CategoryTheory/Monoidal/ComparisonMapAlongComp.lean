module

public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapIdentity

/-!
# The restricted comparison maps and composition

For proper morphisms `P ⟶ Ȳ ⟶ Z` with an open `Y ⊆ Ȳ`, its inverse image `Q ⊆ P` and an open
`X ⊆ Q`, the one-variable comparison maps `Stacks.CategoryTheory.comparisonMapAlong` of `Q ⟶ Y`
along `X ⊆ Q`, of `Ȳ ⟶ Z` along `Y ⊆ Ȳ` and of `P ⟶ Z` along `X ⊆ P` are compatible with the
comparison `a_{P/Z}|_X ⟶ a_{Q/Y}|_X ∘ a_{Ȳ/Z}|_Y`. This is the categorical content of the
compatibility with composition in [Stacks, Tag 0B6T]: [Stacks, Tag 0B6R] for `P ⟶ Ȳ ⟶ Z`,
restricted to `Q` by [Stacks, Tag 0B6P].

## Main results

* `Stacks.CategoryTheory.BaseChange.comparisonMapAlong_comp_pentagon` — the compatibility of the
  restricted comparison maps with composition.
* `Stacks.CategoryTheory.BaseChange.pentagon_core`, `pentagon_coreLift` — its monoidal coherence.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

section Core

variable {B C D E : Type*} [Category B] [Category C] [Category D] [Category E]
  [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  {JY : B ⥤ D} {FQ : D ⥤ E} {Fp : B ⥤ C} {JQ : C ⥤ E} [JY.Monoidal] [FQ.OplaxMonoidal]
  [Fp.OplaxMonoidal] [JQ.Monoidal] {Lc : B ⥤ E} (eg : JY ⋙ FQ ≅ Lc) (ef : Fp ⋙ JQ ≅ Lc)
  (hsq : ∀ K N : B, FQ.map (δ JY K N) ≫ δ FQ (JY.obj K) (JY.obj N) ≫
      ((squareCompositeIso eg ef).hom.app K ⊗ₘ (squareCompositeIso eg ef).hom.app N) =
    (squareCompositeIso eg ef).hom.app (K ⊗ N) ≫ JQ.map (δ Fp K N) ≫
      δ JQ (Fp.obj K) (Fp.obj N))

include hsq in
/-- The monoidal coherence behind the compatibility with composition, inside the restriction to
`Q`. -/
lemma pentagon_core {K N : B} {FPK : C} (eK : Fp.obj K ⟶ FPK) {Y₃ : E} {Z₃ : C}
    (t : Y₃ ⟶ JQ.obj Z₃) :
    FQ.map (μ JY K N) ▷ Y₃ ≫ ((squareCompositeIso eg ef).hom.app (K ⊗ N) ⊗ₘ t) ≫
        μ JQ (Fp.obj (K ⊗ N)) Z₃ ≫
        JQ.map (δ Fp K N ▷ Z₃ ≫ (α_ _ _ _).hom ≫ eK ▷ _) =
      δ FQ (JY.obj K) (JY.obj N) ▷ Y₃ ≫ (α_ _ _ _).hom ≫
        (((squareCompositeIso eg ef).hom.app K ≫ JQ.map eK) ⊗ₘ
          (((squareCompositeIso eg ef).hom.app N ⊗ₘ t) ≫ μ JQ (Fp.obj N) Z₃)) ≫
        μ JQ FPK (Fp.obj N ⊗ Z₃) := by
  set s := squareCompositeIso eg ef
  have h₁ : s.hom.app (K ⊗ N) ≫ JQ.map (δ Fp K N) =
      FQ.map (δ JY K N) ≫ δ FQ (JY.obj K) (JY.obj N) ≫ (s.hom.app K ⊗ₘ s.hom.app N) ≫
        μ JQ (Fp.obj K) (Fp.obj N) := by
    rw [reassoc_of% (hsq K N), Functor.Monoidal.δ_μ, Category.comp_id]
  have h₂ : FQ.map (μ JY K N) ≫ s.hom.app (K ⊗ N) ≫ JQ.map (δ Fp K N) =
      δ FQ (JY.obj K) (JY.obj N) ≫ (s.hom.app K ⊗ₘ s.hom.app N) ≫ μ JQ (Fp.obj K) (Fp.obj N) := by
    rw [h₁, ← FQ.map_comp_assoc, Functor.Monoidal.μ_δ, FQ.map_id, Category.id_comp]
  have h₃ : FQ.map (μ JY K N) ▷ Y₃ ≫ (s.hom.app (K ⊗ N) ⊗ₘ t) ≫
      JQ.map (δ Fp K N) ▷ JQ.obj Z₃ =
      δ FQ (JY.obj K) (JY.obj N) ▷ Y₃ ≫
        (((s.hom.app K ⊗ₘ s.hom.app N) ≫ μ JQ (Fp.obj K) (Fp.obj N)) ⊗ₘ t) := by
    rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_id,
      ← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom, h₂]
    simp
  have h₄ : (((s.hom.app K ⊗ₘ s.hom.app N) ≫ μ JQ (Fp.obj K) (Fp.obj N)) ⊗ₘ t) ≫
      μ JQ (Fp.obj K ⊗ Fp.obj N) Z₃ ≫ JQ.map (α_ (Fp.obj K) (Fp.obj N) Z₃).hom =
      (α_ _ _ _).hom ≫ (s.hom.app K ⊗ₘ ((s.hom.app N ⊗ₘ t) ≫ μ JQ (Fp.obj N) Z₃)) ≫
        μ JQ (Fp.obj K) (Fp.obj N ⊗ Z₃) := by
    have e : (((s.hom.app K ⊗ₘ s.hom.app N) ≫ μ JQ (Fp.obj K) (Fp.obj N)) ⊗ₘ t) =
        ((s.hom.app K ⊗ₘ s.hom.app N) ⊗ₘ t) ≫ μ JQ (Fp.obj K) (Fp.obj N) ▷ JQ.obj Z₃ := by
      rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
        Category.comp_id]
    rw [e, Category.assoc, Functor.LaxMonoidal.associativity]
    dsimp only [Functor.comp_obj]
    rw [MonoidalCategory.associator_naturality_assoc,
      ← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.comp_id]
  have h₅ : (s.hom.app K ⊗ₘ ((s.hom.app N ⊗ₘ t) ≫ μ JQ (Fp.obj N) Z₃)) ≫
      μ JQ (Fp.obj K) (Fp.obj N ⊗ Z₃) ≫ JQ.map (eK ▷ (Fp.obj N ⊗ Z₃)) =
      ((s.hom.app K ≫ JQ.map eK) ⊗ₘ ((s.hom.app N ⊗ₘ t) ≫ μ JQ (Fp.obj N) Z₃)) ≫
        μ JQ FPK (Fp.obj N ⊗ Z₃) := by
    rw [← μ_natural_left, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id]
  simp only [Functor.map_comp]
  rw [← μ_natural_left_assoc, reassoc_of% h₃, reassoc_of% h₄, h₅]

end Core

section Pentagon

variable {A B C D E W : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
  [Category W] [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory W]
  {Fg : A ⥤ B} {Gg : B ⥤ A} {ag : A ⥤ B} [Fg.OplaxMonoidal] (adjg : Fg ⊣ Gg) (bg : Gg ⊣ ag)
  [∀ K M, IsIso (adjg.projectionMap K M)]
  {Fp : B ⥤ C} {Gp : C ⥤ B} {ap : B ⥤ C} [Fp.Monoidal] (adjp : Fp ⊣ Gp) (bp : Gp ⊣ ap)
  [∀ K M, IsIso (adjp.projectionMap K M)]
  {FP : A ⥤ C} {GP : C ⥤ A} {aP : A ⥤ C} [FP.OplaxMonoidal] (adjP : FP ⊣ GP) (bP : GP ⊣ aP)
  [∀ K M, IsIso (adjP.projectionMap K M)]
  (eP : Fg ⋙ Fp ≅ FP) (iP : Gp ⋙ Gg ≅ GP) (jP : ag ⋙ ap ≅ aP)
  (heP : ∀ K N : A, δ (Fg ⋙ Fp) K N ≫ (eP.hom.app K ⊗ₘ eP.hom.app N) =
    eP.hom.app (K ⊗ N) ≫ δ FP K N)
  (hiP : ∀ M : C, FP.map (iP.hom.app M) ≫ adjP.counit.app M =
    eP.inv.app ((Gp ⋙ Gg).obj M) ≫ (adjg.comp adjp).counit.app M)
  (hjP : ∀ L : A, GP.map (jP.hom.app L) ≫ bP.counit.app L =
    iP.inv.app ((ag ⋙ ap).obj L) ≫ (bp.comp bg).counit.app L)
  {JY : B ⥤ D} {RY : D ⥤ B} [JY.Monoidal] (adjJY : JY ⊣ RY)
  {JQ : C ⥤ E} {RQ : E ⥤ C} [JQ.Monoidal] (adjJQ : JQ ⊣ RQ)
  {FQ : D ⥤ E} {GQ : E ⥤ D} {aQ : D ⥤ E} [FQ.OplaxMonoidal] (adjQ : FQ ⊣ GQ) (bQ : GQ ⊣ aQ)
  [∀ K M, IsIso (adjQ.projectionMap K M)]
  {Lc : B ⥤ E} (eg : JY ⋙ FQ ≅ Lc) (ef : Fp ⋙ JQ ≅ Lc)
  (hsq : ∀ K N : B, FQ.map (δ JY K N) ≫ δ FQ (JY.obj K) (JY.obj N) ≫
      ((squareCompositeIso eg ef).hom.app K ⊗ₘ (squareCompositeIso eg ef).hom.app N) =
    (squareCompositeIso eg ef).hom.app (K ⊗ N) ≫ JQ.map (δ Fp K N) ≫
      δ JQ (Fp.obj K) (Fp.obj N))
  [IsIso (twoSquare adjp adjQ eg ef)]
  {JX : E ⥤ W} [JX.Monoidal] {Lι : C ⥤ W} [Lι.Monoidal] (ν : Lι ≅ JQ ⋙ JX)
  (hν : ∀ K N : C, δ Lι K N ≫ (ν.hom.app K ⊗ₘ ν.hom.app N) =
    ν.hom.app (K ⊗ N) ≫ δ (JQ ⋙ JX) K N)
  {Pf : D ⥤ W} [Pf.Monoidal] (κf : FQ ⋙ JX ≅ Pf)
  (hκf : ∀ K N : D, δ (FQ ⋙ JX) K N ≫ (κf.hom.app K ⊗ₘ κf.hom.app N) =
    κf.hom.app (K ⊗ N) ≫ δ Pf K N)
  {Pg : A ⥤ D} (κg : Fg ⋙ JY ≅ Pg) {Pgf : A ⥤ W} (κgf : FP ⋙ Lι ≅ Pgf) (κ : Pg ⋙ Pf ≅ Pgf)
  (hκ : ∀ K : A, κ.hom.app K ≫ κgf.inv.app K ≫ ν.hom.app (FP.obj K) =
    Pf.map (κg.inv.app K) ≫ κf.inv.app (JY.obj (Fg.obj K)) ≫
      JX.map ((squareCompositeIso eg ef).hom.app (Fg.obj K) ≫ JQ.map (eP.hom.app K)))
  {UA : A} (hA : 𝟙_ A = UA) {UB : B} (hB : 𝟙_ B = UB) {UD : D} (hD : 𝟙_ D = UD)
  [IsIso ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app UB)]
  [IsIso ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app (ag.obj UA))]

/-- The comparison `a_P ⟶ a_Q ∘ a_Ȳ` restricted to `X`: `Lι` of `a_P ≅ a_p ∘ a_g`, `Lι ≅ JX ∘ JQ`
and `JX` of the base change map. -/
abbrev compRestrictHom (K : A) : Lι.obj (aP.obj K) ⟶ JX.obj (aQ.obj (JY.obj (ag.obj K))) :=
  Lι.map (jP.inv.app K) ≫ ν.hom.app (ap.obj (ag.obj K)) ≫
    JX.map ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app (ag.obj K))

omit [IsIso
    ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app (ag.obj UA))] in
include hsq in
/-- [Stacks, Tag 0B6P] solved for the comparison map of `Q ⟶ Y`. -/
lemma pentagon_baseChange (N : B) :
    adjQ.comparisonMap bQ (JY.obj N) UD ≫ aQ.map (JY.obj N ◁ eqToHom hD.symm ≫ (ρ_ _).hom) =
      ((squareCompositeIso eg ef).hom.app N ⊗ₘ
          inv ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app UB ≫
            aQ.map (JY.map (eqToHom hB.symm) ≫ η JY ≫ eqToHom hD))) ≫
        μ JQ (Fp.obj N) (ap.obj UB) ≫
        JQ.map (adjp.comparisonMap bp N UB ≫ ap.map (N ◁ eqToHom hB.symm ≫ (ρ_ N).hom)) ≫
        (rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app N := by
  rw [comparisonMap_unit_baseChange adjp adjQ adjJY adjJQ eg ef hsq bp bQ hB hD N,
    Functor.Monoidal.μ_δ_assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Iso.hom_inv_id_app, IsIso.inv_hom_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]

omit [IsIso ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app (ag.obj UA))]
  [IsIso ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app UB)]
  [MonoidalCategory A] [Fg.OplaxMonoidal] [FP.OplaxMonoidal] in
include hsq hκf in
/-- The monoidal coherence of the compatibility with composition, after restriction to `X`. -/
lemma pentagon_coreLift (K : A) (N : B) {Y₃ : E} {Z₃ : C} (t : Y₃ ⟶ JQ.obj Z₃) :
    Pf.map (κg.inv.app K ▷ JY.obj N ≫ μ JY (Fg.obj K) N) ▷ JX.obj Y₃ ≫
        κf.inv.app (JY.obj (Fg.obj K ⊗ N)) ▷ JX.obj Y₃ ≫
        μ JX (FQ.obj (JY.obj (Fg.obj K ⊗ N))) Y₃ ≫
        JX.map (((squareCompositeIso eg ef).hom.app (Fg.obj K ⊗ N) ⊗ₘ t) ≫
          μ JQ (Fp.obj (Fg.obj K ⊗ N)) Z₃ ≫
          JQ.map (δ Fp (Fg.obj K) N ▷ Z₃ ≫ (α_ _ _ _).hom ≫ eP.hom.app K ▷ _)) =
      δ Pf (Pg.obj K) (JY.obj N) ▷ JX.obj Y₃ ≫ (α_ _ _ _).hom ≫
        ((Pf.map (κg.inv.app K) ≫ κf.inv.app (JY.obj (Fg.obj K)) ≫
            JX.map ((squareCompositeIso eg ef).hom.app (Fg.obj K) ≫ JQ.map (eP.hom.app K))) ⊗ₘ
          (κf.inv.app (JY.obj N) ▷ JX.obj Y₃ ≫ μ JX (FQ.obj (JY.obj N)) Y₃ ≫
            JX.map (((squareCompositeIso eg ef).hom.app N ⊗ₘ t) ≫ μ JQ (Fp.obj N) Z₃))) ≫
        μ JX (JQ.obj (FP.obj K)) (JQ.obj (Fp.obj N ⊗ Z₃)) ≫
        JX.map (μ JQ (FP.obj K) (Fp.obj N ⊗ Z₃)) := by
  set u := (squareCompositeIso eg ef).hom.app (Fg.obj K) ≫ JQ.map (eP.hom.app K)
  set v := ((squareCompositeIso eg ef).hom.app N ⊗ₘ t) ≫ μ JQ (Fp.obj N) Z₃
  have core := pentagon_core eg ef hsq (eP.hom.app K) t (K := Fg.obj K) (N := N)
  have n₁ : Pf.map (μ JY (Fg.obj K) N) ≫ κf.inv.app (JY.obj (Fg.obj K ⊗ N)) =
      κf.inv.app (JY.obj (Fg.obj K) ⊗ JY.obj N) ≫ JX.map (FQ.map (μ JY (Fg.obj K) N)) :=
    κf.inv.naturality _
  have l : Pf.map (κg.inv.app K ▷ JY.obj N ≫ μ JY (Fg.obj K) N) ▷ JX.obj Y₃ ≫
        κf.inv.app (JY.obj (Fg.obj K ⊗ N)) ▷ JX.obj Y₃ ≫
        μ JX (FQ.obj (JY.obj (Fg.obj K ⊗ N))) Y₃ ≫
        JX.map (((squareCompositeIso eg ef).hom.app (Fg.obj K ⊗ N) ⊗ₘ t) ≫
          μ JQ (Fp.obj (Fg.obj K ⊗ N)) Z₃ ≫
          JQ.map (δ Fp (Fg.obj K) N ▷ Z₃ ≫ (α_ _ _ _).hom ≫ eP.hom.app K ▷ _)) =
      Pf.map (κg.inv.app K ▷ JY.obj N) ▷ JX.obj Y₃ ≫
        κf.inv.app (JY.obj (Fg.obj K) ⊗ JY.obj N) ▷ JX.obj Y₃ ≫
        μ JX (FQ.obj (JY.obj (Fg.obj K) ⊗ JY.obj N)) Y₃ ≫
        JX.map (δ FQ (JY.obj (Fg.obj K)) (JY.obj N) ▷ Y₃ ≫ (α_ _ _ _).hom ≫ (u ⊗ₘ v) ≫
          μ JQ (FP.obj K) (Fp.obj N ⊗ Z₃)) := by
    rw [Functor.map_comp, MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc (Pf.map (μ JY (Fg.obj K) N)), n₁,
      MonoidalCategory.comp_whiskerRight_assoc, μ_natural_left_assoc, ← JX.map_comp, core]
  rw [l]
  have r3 : δ Pf (Pg.obj K) (JY.obj N) ≫
      ((Pf.map (κg.inv.app K) ≫ κf.inv.app (JY.obj (Fg.obj K))) ⊗ₘ κf.inv.app (JY.obj N)) =
      Pf.map (κg.inv.app K ▷ JY.obj N) ≫ κf.inv.app (JY.obj (Fg.obj K) ⊗ JY.obj N) ≫
        JX.map (δ FQ (JY.obj (Fg.obj K)) (JY.obj N)) ≫
        δ JX (FQ.obj (JY.obj (Fg.obj K))) (FQ.obj (JY.obj N)) := by
    have h := hκf (JY.obj (Fg.obj K)) (JY.obj N)
    have h' : δ Pf (JY.obj (Fg.obj K)) (JY.obj N) ≫
        (κf.inv.app (JY.obj (Fg.obj K)) ⊗ₘ κf.inv.app (JY.obj N)) =
        κf.inv.app (JY.obj (Fg.obj K) ⊗ JY.obj N) ≫ δ (FQ ⋙ JX) (JY.obj (Fg.obj K)) (JY.obj N) := by
      rw [← cancel_epi (κf.hom.app (JY.obj (Fg.obj K) ⊗ JY.obj N)), Iso.hom_inv_id_app_assoc,
        ← reassoc_of% h, MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app,
        Iso.hom_inv_id_app]
      simp
    have e : ((Pf.map (κg.inv.app K) ≫ κf.inv.app (JY.obj (Fg.obj K))) ⊗ₘ
        κf.inv.app (JY.obj N)) = Pf.map (κg.inv.app K) ▷ Pf.obj (JY.obj N) ≫
          (κf.inv.app (JY.obj (Fg.obj K)) ⊗ₘ κf.inv.app (JY.obj N)) := by
      rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp]
    rw [e, Functor.OplaxMonoidal.δ_natural_left_assoc]
    dsimp only [Functor.comp_obj]
    rw [h', Functor.OplaxMonoidal.comp_δ]
  have r2 : ∀ {P₁ P₂ P₃ Q₁ Q₂ T : W} (d : P₁ ⟶ P₂ ⊗ P₃) (x : P₂ ⟶ Q₁) (y : P₃ ⟶ Q₂) (Y : W)
      (h : Q₁ ⊗ (Q₂ ⊗ Y) ⟶ T),
      d ▷ Y ≫ (α_ _ _ _).hom ≫ (x ⊗ₘ y ▷ Y) ≫ h = (d ≫ (x ⊗ₘ y)) ▷ Y ≫ (α_ _ _ _).hom ≫ h := by
    intro P₁ P₂ P₃ Q₁ Q₂ T d x y Y h
    rw [← MonoidalCategory.tensorHom_id y, ← MonoidalCategory.associator_naturality_assoc,
      MonoidalCategory.tensorHom_id, MonoidalCategory.comp_whiskerRight_assoc]
  have r4 : ∀ {A₁ B₁ A₂ B₂ : E} {Y : E} (u' : A₁ ⟶ A₂) (v' : B₁ ⊗ Y ⟶ B₂),
      δ JX A₁ B₁ ▷ JX.obj Y ≫ (α_ _ _ _).hom ≫
        (JX.map u' ⊗ₘ (μ JX B₁ Y ≫ JX.map v')) ≫ μ JX A₂ B₂ =
      μ JX (A₁ ⊗ B₁) Y ≫ JX.map ((α_ _ _ _).hom ≫ (u' ⊗ₘ v')) := by
    intro A₁ B₁ A₂ B₂ Y u' v'
    have hm : (JX.map u' ⊗ₘ (μ JX B₁ Y ≫ JX.map v')) =
        JX.obj A₁ ◁ μ JX B₁ Y ≫ (JX.map u' ⊗ₘ JX.map v') := by
      rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp]
    rw [hm, Category.assoc, μ_natural, ← Functor.LaxMonoidal.associativity_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, Functor.Monoidal.δ_μ,
      MonoidalCategory.id_whiskerRight, Category.id_comp, Functor.map_comp]
  have e1 : ((Pf.map (κg.inv.app K) ≫ κf.inv.app (JY.obj (Fg.obj K)) ≫ JX.map u) ⊗ₘ
      (κf.inv.app (JY.obj N) ▷ JX.obj Y₃ ≫ μ JX (FQ.obj (JY.obj N)) Y₃ ≫ JX.map v)) =
      ((Pf.map (κg.inv.app K) ≫ κf.inv.app (JY.obj (Fg.obj K))) ⊗ₘ
        (κf.inv.app (JY.obj N) ▷ JX.obj Y₃)) ≫
        (JX.map u ⊗ₘ (μ JX (FQ.obj (JY.obj N)) Y₃ ≫ JX.map v)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  rw [e1, Category.assoc, r2, r3]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% r4, μ_natural_left_assoc, ← JX.map_comp, ← JX.map_comp]
  simp only [Category.assoc]

private lemma assemble₁ {C E W : Type*} [Category C] [Category E] [Category W] (F : E ⥤ W)
    (G : C ⥤ E) {Q₀ Q₁ Q₂ : W} {E₀ E₁ : E} {P₀ P₁ P₂ P₃ : C} (a : Q₀ ⟶ Q₁) (b : Q₁ ⟶ Q₂)
    (c : Q₂ ⟶ F.obj E₀) (X₁ : E₀ ⟶ E₁) (X₂ : E₁ ⟶ G.obj P₀) (p : P₀ ⟶ P₁) (p' : P₁ ⟶ P₂)
    (r : P₀ ⟶ P₃) (rest : P₃ ⟶ P₂) {R₁ R₂ : E} (β₁ : G.obj P₁ ⟶ R₁) (q : R₁ ⟶ R₂)
    (β₂ : G.obj P₂ ⟶ R₂) (hn : β₁ ≫ q = G.map p' ≫ β₂) (hR : p ≫ p' = r ≫ rest) :
    a ≫ (b ≫ c ≫ F.map (X₁ ≫ X₂ ≫ G.map p ≫ β₁)) ≫ F.map q =
      (a ≫ b ≫ c ≫ F.map (X₁ ≫ X₂ ≫ G.map r)) ≫ (F.map (G.map rest) ≫ F.map β₂) := by
  simp only [Category.assoc, ← F.map_comp, hn, ← G.map_comp_assoc, hR]

include hν in
private lemma assemble₂ {S A A₁ B B₁ T : W} {E₁ E₂ R₃ R₆ : E} {X₁ P₂ P₃ P₄ P₅ P₆ : C}
    (ψ₁ : S ⟶ T) (ψ₂ : T ⟶ A ⊗ B) (a' : A ⟶ JX.obj (JQ.obj X₁)) (b₁ : B ⟶ B₁)
    (b₂ : B₁ ⟶ JX.obj E₁) (X₂a : E₁ ⟶ E₂) (X₂b : E₂ ⟶ JQ.obj P₂) (cpG : P₂ ⟶ P₃)
    (βG : JQ.obj P₃ ⟶ R₃) (jU : P₃ ⟶ P₄) (jUi : P₄ ⟶ P₃) (hj : jU ≫ jUi = 𝟙 _)
    (_hj' : jUi ≫ jU = 𝟙 _)
    (κ₀ : A ⟶ A₁) (κi : A₁ ⟶ Lι.obj X₁) (hκ' : κ₀ ≫ κi ≫ ν.hom.app X₁ = a')
    (cP' : X₁ ⊗ P₄ ⟶ P₅) (jK : P₅ ⟶ P₆) (βK : JQ.obj P₆ ⟶ R₆)
    [IsIso (Lι.map jUi ≫ ν.hom.app P₃ ≫ JX.map βG)] :
    (ψ₁ ≫ ψ₂ ≫ (a' ⊗ₘ (b₁ ≫ b₂ ≫ JX.map (X₂a ≫ X₂b))) ≫ μ JX (JQ.obj X₁) (JQ.obj P₂) ≫
        JX.map (μ JQ X₁ P₂)) ≫
        JX.map (JQ.map (X₁ ◁ (cpG ≫ jU) ≫ cP' ≫ jK)) ≫ JX.map βK =
      ψ₁ ≫ ψ₂ ≫ A ◁ (b₁ ≫ b₂ ≫ JX.map (X₂a ≫ X₂b ≫ JQ.map cpG ≫ βG)) ≫
        (κ₀ ⊗ₘ inv (Lι.map jUi ≫ ν.hom.app P₃ ≫ JX.map βG)) ≫
        (κi ▷ Lι.obj P₄ ≫ μ Lι X₁ P₄ ≫ Lι.map cP') ≫ Lι.map jK ≫ ν.hom.app P₆ ≫ JX.map βK := by
  have hc : JX.map βG ≫ inv (Lι.map jUi ≫ ν.hom.app P₃ ≫ JX.map βG) =
      ν.inv.app P₃ ≫ Lι.map jU := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← Lι.map_comp_assoc, hj, Lι.map_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc]
  have hν' : μ Lι X₁ P₄ ≫ ν.hom.app (X₁ ⊗ P₄) =
      (ν.hom.app X₁ ⊗ₘ ν.hom.app P₄) ≫ μ JX (JQ.obj X₁) (JQ.obj P₄) ≫ JX.map (μ JQ X₁ P₄) := by
    have h := hν X₁ P₄
    rw [← cancel_epi (δ Lι X₁ P₄), Functor.Monoidal.δ_μ_assoc, reassoc_of% h,
      Functor.OplaxMonoidal.comp_δ, Category.assoc, Functor.Monoidal.δ_μ_assoc, ← JX.map_comp,
      Functor.Monoidal.δ_μ, JX.map_id, Category.comp_id]
  set X₂ := X₂a ≫ X₂b with hX₂
  rw [show X₂a ≫ X₂b ≫ JQ.map cpG ≫ βG = X₂ ≫ JQ.map cpG ≫ βG by simp [hX₂]]
  have h1 : A ◁ (b₁ ≫ b₂ ≫ JX.map (X₂ ≫ JQ.map cpG ≫ βG)) ≫
      (κ₀ ⊗ₘ inv (Lι.map jUi ≫ ν.hom.app P₃ ≫ JX.map βG)) ≫ κi ▷ Lι.obj P₄ =
      ((κ₀ ≫ κi) ⊗ₘ (b₁ ≫ b₂ ≫ JX.map (X₂ ≫ JQ.map cpG) ≫ ν.inv.app P₃ ≫ Lι.map jU)) := by
    rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp, hc]
  have h4 : (b₁ ≫ b₂ ≫ JX.map (X₂ ≫ JQ.map cpG) ≫ ν.inv.app P₃ ≫ Lι.map jU) ≫ ν.hom.app P₄ =
      (b₁ ≫ b₂ ≫ JX.map X₂) ≫ JX.map (JQ.map (cpG ≫ jU)) := by
    simp only [Category.assoc, ν.hom.naturality, Iso.inv_hom_id_app_assoc, Functor.comp_map,
      Functor.map_comp]
  have h5 : ∀ {Y₁ Y₂ : C} {Z : W} (x : Z ⟶ JX.obj (JQ.obj Y₁)) (z : Y₁ ⟶ Y₂),
      (a' ⊗ₘ (x ≫ JX.map (JQ.map z))) ≫ μ JX (JQ.obj X₁) (JQ.obj Y₂) ≫ JX.map (μ JQ X₁ Y₂) =
        (a' ⊗ₘ x) ≫ μ JX (JQ.obj X₁) (JQ.obj Y₁) ≫ JX.map (μ JQ X₁ Y₁) ≫
          JX.map (JQ.map (X₁ ◁ z)) := by
    intro Y₁ Y₂ Z x z
    rw [← Category.comp_id a', ← MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id,
      MonoidalCategory.id_tensorHom, μ_natural_right_assoc, ← JX.map_comp, ← JX.map_comp,
      μ_natural_right]
  simp only [Category.assoc]
  rw [reassoc_of% h1, ← Lι.map_comp_assoc, ν.hom.naturality_assoc, reassoc_of% hν',
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.assoc, hκ', h4, reassoc_of% h5]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

/-- `comparisonMapAlong` for a strong `J`, with the inverse of `δ J` replaced by `μ J`. -/
private lemma comparisonMapAlong_eq_μ {A B C : Type*} [Category A] [Category B] [Category C]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] {F : A ⥤ B} {G : B ⥤ A}
    {a : A ⥤ B} [F.OplaxMonoidal] (adj : F ⊣ G) (b : G ⊣ a)
    [∀ K M, IsIso (adj.projectionMap K M)] (J : B ⥤ C) [J.Monoidal] {P : A ⥤ C}
    (κ : F ⋙ J ≅ P) {U : A} (hU : 𝟙_ A = U) (K : A) :
    comparisonMapAlong adj b J κ hU K = κ.inv.app K ▷ J.obj (a.obj U) ≫ μ J (F.obj K) (a.obj U) ≫
      J.map (adj.comparisonMap b K U ≫ a.map (K ◁ eqToHom hU.symm ≫ (ρ_ K).hom)) := by
  simp only [comparisonMapAlong, Functor.Monoidal.inv_δ]

include heP hiP hjP hsq hν hκf hκ hB in
/-- **The restricted comparison maps are compatible with composition** (the diagram of
[Stacks, Tag 0B6T]): `μ_f` at `Pg K ⊗ g^! U` followed by `f^!` of `μ_g` at `K` is the oplax
structure of `Pf`, the associator, `Pf (Pg K)` tensored with `μ_f` at `g^! U`, the identifications
`Pf ∘ Pg ≅ Pgf` and `f^! g^! U ≅ (g ∘ f)^! U`, `μ_{g ∘ f}` at `K` and `(g ∘ f)^! K ⟶ f^! g^! K`. -/
theorem comparisonMapAlong_comp_pentagon (K : A) :
    comparisonMapAlong adjQ bQ JX κf hD (Pg.obj K ⊗ JY.obj (ag.obj UA)) ≫
        JX.map (aQ.map (comparisonMapAlong adjg bg JY κg hA K)) =
      δ Pf (Pg.obj K) (JY.obj (ag.obj UA)) ▷ JX.obj (aQ.obj UD) ≫ (α_ _ _ _).hom ≫
        Pf.obj (Pg.obj K) ◁ comparisonMapAlong adjQ bQ JX κf hD (JY.obj (ag.obj UA)) ≫
        (κ.hom.app K ⊗ₘ inv (compRestrictHom adjp bp jP adjJY adjJQ adjQ bQ eg ef ν UA)) ≫
        comparisonMapAlong adjP bP Lι κgf hA K ≫
        compRestrictHom adjp bp jP adjJY adjJQ adjQ bQ eg ef ν K := by
  have BC := fun N => pentagon_baseChange adjp bp adjJY adjJQ adjQ bQ eg ef hsq hB hD N
  have R0 := Adjunction.comparisonMap_unit_comp adjg adjp bg bp adjP bP eP iP jP heP hiP hjP hA hB K
  have nβ : (rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app
        (Fg.obj K ⊗ ag.obj UA) ≫
      aQ.map (JY.map (adjg.comparisonMap bg K UA ≫ ag.map (K ◁ eqToHom hA.symm ≫ (ρ_ K).hom))) =
      JQ.map (ap.map (adjg.comparisonMap bg K UA ≫ ag.map (K ◁ eqToHom hA.symm ≫ (ρ_ K).hom))) ≫
        (rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app (ag.obj K) :=
    ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).naturality
      (adjg.comparisonMap bg K UA ≫ ag.map (K ◁ eqToHom hA.symm ≫ (ρ_ K).hom))).symm
  have R1 : (adjp.comparisonMap bp (Fg.obj K ⊗ ag.obj UA) UB ≫
        ap.map ((Fg.obj K ⊗ ag.obj UA) ◁ eqToHom hB.symm ≫ (ρ_ (Fg.obj K ⊗ ag.obj UA)).hom)) ≫
        ap.map (adjg.comparisonMap bg K UA ≫ ag.map (K ◁ eqToHom hA.symm ≫ (ρ_ K).hom)) =
      (δ Fp (Fg.obj K) (ag.obj UA) ▷ ap.obj UB ≫ (α_ _ _ _).hom ≫ eP.hom.app K ▷ _) ≫
        FP.obj K ◁ ((adjp.comparisonMap bp (ag.obj UA) UB ≫
          ap.map ((ag.obj UA) ◁ eqToHom hB.symm ≫ (ρ_ (ag.obj UA)).hom)) ≫ jP.hom.app UA) ≫
        (adjP.comparisonMap bP K UA ≫ aP.map (K ◁ eqToHom hA.symm ≫ (ρ_ K).hom)) ≫
        jP.inv.app K := by
    rw [← cancel_mono (jP.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    simpa only [Category.assoc] using R0
  have key := congrArg (fun t => t ≫ (JX.map (JQ.map (FP.obj K ◁
      ((adjp.comparisonMap bp (ag.obj UA) UB ≫
        ap.map ((ag.obj UA) ◁ eqToHom hB.symm ≫ (ρ_ (ag.obj UA)).hom)) ≫ jP.hom.app UA) ≫
      (adjP.comparisonMap bP K UA ≫ aP.map (K ◁ eqToHom hA.symm ≫ (ρ_ K).hom)) ≫
      jP.inv.app K)) ≫
      JX.map ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app (ag.obj K))))
    (pentagon_coreLift (eg := eg) (ef := ef) (hsq := hsq) (κf := κf) (hκf := hκf) (κg := κg)
      (eP := eP) (K := K) (N := ag.obj UA)
      (t := inv ((rightAdjointBaseChange adjp adjQ adjJY adjJQ eg ef bp bQ).app UB ≫
        aQ.map (JY.map (eqToHom hB.symm) ≫ η JY ≫ eqToHom hD))) (Z₃ := ap.obj UB))
  refine Eq.trans ?_ (key.trans ?_)
  · rw [comparisonMapAlong_eq_μ adjg bg JY κg hA K,
      ← Category.assoc (κg.inv.app K ▷ JY.obj (ag.obj UA)), aQ.map_comp, JX.map_comp,
      ← Stacks.CategoryTheory.comparisonMapAlong_naturality_assoc,
      comparisonMapAlong_eq_μ adjQ bQ JX κf hD, BC]
    exact assemble₁ JX JQ _ _ _ _ _ _ _ _ _ _ _ _ nβ R1
  · rw [comparisonMapAlong_eq_μ adjP bP Lι κgf hA K,
      comparisonMapAlong_eq_μ adjQ bQ JX κf hD, BC]
    simp only [compRestrictHom]
    exact assemble₂ ν hν _ _ _ _ _ _ _ _ _ _ _ (Iso.hom_inv_id_app jP UA)
      (Iso.inv_hom_id_app jP UA) _ _ (hκ K) _ _ _

end Pentagon

end Stacks.CategoryTheory.BaseChange

end
