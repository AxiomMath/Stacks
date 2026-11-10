module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChangeTwoSpaceSource

/-!
# The inverse-line square of the conormal source of Stacks 0B4I over two spaces

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points
and `h : T' ⟶ T` with `v ≫ g = u ∘ h`.  The inverse-line factors of the source readings at
`u ∘ h` on `X` and at `v` on `X'` are intertwined by the comparison of the two inverse-line base
changes of Stacks 0B3V along `h` and by `v^*g^* ≅ (u ∘ h)^*` followed by the inverse image of
tensor powers along `g`.  A map into the tensor inverse of an invertible module is determined by
its evaluation, so the square follows from the evaluations of the four inverse-line
identifications, the monoidality of `v^*g^* ≅ (u ∘ h)^*` and its compatibility with the
identifications of the structure sheaves.

## Main definitions

* `AlgebraicGeometry.Space.inversePointEvaluation`: the evaluation of the inverse-line factor
  of the conormal source read at a scheme point.

## Main results

* `CategoryTheory.Functor.comp_eq_comp_of_evaluation`: two maps into a tensor inverse agree if
  their evaluations do.
* `Stacks.Divisors.inverseQuotientBaseChange_hom_tensor`: the evaluation of the inverse-line
  base change of Stacks 0B3V is the pulled back pairing.
* `AlgebraicGeometry.Space.modulePullbackTensorPowerIso_neg_one_evaluation`: the evaluation of
  the inverse image of tensor inverses along any morphism of algebraic spaces.
* `AlgebraicGeometry.Space.pointPullbackCompIso_hom_app_unit`: `v^*g^* ≅ (u ∘ h)^*` is
  compatible with the identifications of the structure sheaves.
* `AlgebraicGeometry.Space.inverseQuotientBaseChange_inv_comp_hom_evaluation`: the evaluation of
  the comparison of two inverse-line base changes.
* `AlgebraicGeometry.Space.inversePointEvaluation_comp_eq_of_space` and
  `AlgebraicGeometry.Space.inversePointEvaluation_twoSpace_space`: the comparison of the
  evaluations at `u ∘ h` and at `v`, reduced to the spaces and proved there.
* `AlgebraicGeometry.Space.inversePointReadingHom_twoSpace`: the inverse-line square.

## Implementation notes

The squares are stated through the abbreviations `CategoryTheory.Functor.EvaluationSquare`,
`CategoryTheory.Functor.EvaluationEq` and `CategoryTheory.Functor.EvaluationCompSquare`, with
the category instance and the objects given explicitly, and the instances of invertibility are
passed as the terms of the statement rather than found by instance search: the hypotheses of
`CategoryTheory.Functor.comp_eq_comp_of_evaluation` are then matched syntactically, while a
spelling crossing between the readings `R_T(x^*ℒ)` and the invertible modules of the quotients
`q_x`, or between two derivations of an instance, exhausts the recursion depth of the unifier.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

/-- The evaluation square `F(δ, L₁) ≫ ev₁ = F(Λ₀, φ) ≫ ev₀` of a map `δ` between tensor
inverses through `φ : L₁ ⟶ L₀`, as a proposition. -/
abbrev CategoryTheory.Functor.EvaluationSquare {ℬ : Type*} [iℬ : Category ℬ]
    (F : ℬ ⥤ ℬ ⥤ ℬ) {Λ₀ Λ₁ L₀ L₁ U : ℬ} (δ : Λ₀ ⟶ Λ₁) (φ : L₁ ⟶ L₀)
    (ev₀ : (F.obj Λ₀).obj L₀ ⟶ U) (ev₁ : (F.obj Λ₁).obj L₁ ⟶ U) : Prop :=
  (F.map δ).app L₁ ≫ ev₁ = (F.obj Λ₀).map φ ≫ ev₀

/-- The evaluation `F(i, L₀) ≫ ev = e` of a map `i` into a tensor inverse, as a proposition. -/
abbrev CategoryTheory.Functor.EvaluationEq {ℬ : Type*} [iℬ : Category ℬ]
    (F : ℬ ⥤ ℬ ⥤ ℬ) {A Λ₀ L₀ U : ℬ} (i : A ⟶ Λ₀) (ev : (F.obj Λ₀).obj L₀ ⟶ U)
    (e : (F.obj A).obj L₀ ⟶ U) : Prop :=
  (F.map i).app L₀ ≫ ev = e

/-- The comparison `F(A, φ) ≫ e₀ = F(d, L₁) ≫ e₁` of two evaluations, as a proposition. -/
abbrev CategoryTheory.Functor.EvaluationCompSquare {ℬ : Type*} [iℬ : Category ℬ]
    (F : ℬ ⥤ ℬ ⥤ ℬ) {A A' L₀ L₁ U : ℬ} (φ : L₁ ⟶ L₀) (d : A ⟶ A')
    (e₀ : (F.obj A).obj L₀ ⟶ U) (e₁ : (F.obj A').obj L₁ ⟶ U) : Prop :=
  (F.obj A).map φ ≫ e₀ = (F.map d).app L₁ ≫ e₁

/-- **Two maps into a tensor inverse agree if their evaluations do**: if `δ` is evaluated
through `φ`, `i` and `i'` have evaluations `e₀`, `e₁` and `F(A, φ) ≫ e₀ = F(d, L₁) ≫ e₁`, then
`i ≫ δ = d ≫ i'`, as soon as maps into `Λ₁` are determined by their evaluation. -/
theorem CategoryTheory.Functor.comp_eq_comp_of_evaluation {ℬ : Type*} [iℬ : Category ℬ]
    (F : ℬ ⥤ ℬ ⥤ ℬ) {A A' L₀ L₁ Λ₀ Λ₁ U : ℬ} (i : A ⟶ Λ₀) (δ : Λ₀ ⟶ Λ₁) (d : A ⟶ A')
    (i' : A' ⟶ Λ₁) (φ : L₁ ⟶ L₀) (ev₀ : (F.obj Λ₀).obj L₀ ⟶ U) (ev₁ : (F.obj Λ₁).obj L₁ ⟶ U)
    (e₀ : (F.obj A).obj L₀ ⟶ U) (e₁ : (F.obj A').obj L₁ ⟶ U)
    (hδ : EvaluationSquare F δ φ ev₀ ev₁)
    (hi : EvaluationEq F i ev₀ e₀) (hi' : EvaluationEq F i' ev₁ e₁)
    (hm : EvaluationCompSquare F φ d e₀ e₁)
    (huniq : ∀ α β : A ⟶ Λ₁, (F.map α).app L₁ ≫ ev₁ = (F.map β).app L₁ ≫ ev₁ → α = β) :
    i ≫ δ = d ≫ i' := by
  refine huniq _ _ ?_
  calc (F.map (i ≫ δ)).app L₁ ≫ ev₁ = (F.map i).app L₁ ≫ (F.map δ).app L₁ ≫ ev₁ := by simp
    _ = (F.map i).app L₁ ≫ (F.obj Λ₀).map φ ≫ ev₀ := congrArg (_ ≫ ·) hδ
    _ = (F.obj A).map φ ≫ (F.map i).app L₀ ≫ ev₀ := ((F.map i).naturality_assoc φ ev₀).symm
    _ = (F.map d).app L₁ ≫ e₁ := (congrArg (_ ≫ ·) hi).trans hm
    _ = (F.map (d ≫ i')).app L₁ ≫ ev₁ := by
        rw [← (show (F.map i').app L₁ ≫ ev₁ = e₁ from hi')]
        simp

/-- **The comparison of two identifications with tensor inverses of one module**: if
`c₀ : M ≅ Λ₀` and `c₁ : M ≅ Λ₁` evaluate to the pairing `p` through `L₀ ≅ P` and `L₁ ≅ P`, then
`c₀⁻¹ ≫ c₁` evaluates through the induced `φ : L₁ ⟶ L₀`. -/
theorem CategoryTheory.Functor.inv_comp_hom_evaluation {ℬ : Type*} [iℬ : Category ℬ]
    (F : ℬ ⥤ ℬ ⥤ ℬ) {M Λ₀ Λ₁ L₀ L₁ P U : ℬ} (c₀ : M ≅ Λ₀) (c₁ : M ≅ Λ₁) (hL₀ : L₀ ≅ P)
    (hL₁ : L₁ ≅ P) (p : (F.obj M).obj P ⟶ U) (ev₀ : (F.obj Λ₀).obj L₀ ⟶ U)
    (ev₁ : (F.obj Λ₁).obj L₁ ⟶ U)
    (h₀ : (F.map c₀.hom).app L₀ ≫ ev₀ = (F.obj M).map hL₀.hom ≫ p)
    (h₁ : (F.map c₁.hom).app L₁ ≫ ev₁ = (F.obj M).map hL₁.hom ≫ p) (φ : L₁ ⟶ L₀)
    (hφ : φ ≫ hL₀.hom = hL₁.hom) :
    EvaluationSquare F (c₀.inv ≫ c₁.hom) φ ev₀ ev₁ := by
  change (F.map (c₀.inv ≫ c₁.hom)).app L₁ ≫ ev₁ = (F.obj Λ₀).map φ ≫ ev₀
  have e : (F.map c₀.inv).app L₁ ≫ (F.obj M).map φ = (F.obj Λ₀).map φ ≫ (F.map c₀.inv).app L₀ :=
    ((F.map c₀.inv).naturality φ).symm
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc, h₁, ← hφ]
  rw [reassoc_of% e, ← h₀]
  simp only [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, NatTrans.id_app, Category.comp_id]

/-- The reading of one side of the evaluation comparison, written through the natural
comparison `ζ₂ ⟶ ζ` of readings. -/
private theorem reading_inv_comp_eq {𝒳 𝒜 ℬ : Type*} [Category 𝒳] [Category 𝒜] [Category ℬ]
    (R : 𝒜 ⥤ ℬ) (G : 𝒳 ⥤ 𝒜) {P Q U : 𝒳} {Y M M₂ O : 𝒜} {Z Z₂ V : ℬ}
    (t : G.obj P ≅ Y) (z : R.obj Y ≅ Z) (s : P ≅ U) (m : G.obj U ≅ O) (w : R.obj O ≅ V)
    (a : Q ≅ P) (n : G.obj Q ≅ M) (ζ : R.obj M ≅ Z) (ζ₂ : R.obj M₂ ≅ Z₂) (c : M₂ ⟶ M)
    (k : Z₂ ⟶ Z) (hμ : (R.mapIso t ≪≫ z).hom = ((G ⋙ R).mapIso a.symm).hom ≫ R.map n.hom ≫ ζ.hom)
    (h : R.map c ≫ ζ.hom = ζ₂.hom ≫ k) :
    k ≫ (R.mapIso t ≪≫ z).inv ≫ ((G ⋙ R).mapIso s).hom ≫ (R.mapIso m ≪≫ w).hom =
      ζ₂.inv ≫ R.map (c ≫ (G.mapIso a.symm ≪≫ n).inv ≫ G.map s.hom ≫ m.hom) ≫ w.hom := by
  have e : R.mapIso t ≪≫ z = R.mapIso (G.mapIso a.symm ≪≫ n) ≪≫ ζ :=
    Iso.ext (hμ.trans (by simp))
  have j : k ≫ ζ.inv = ζ₂.inv ≫ R.map c := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  rw [e]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc, reassoc_of% j,
    Functor.mapIso_hom, Functor.comp_map, Iso.trans_hom, Functor.map_comp]

/-- **The evaluation of a reading of a map into a tensor inverse, reduced to the space**: the
two evaluations `F(A, φ) ≫ e₀` and `F(d, L₁) ≫ e₁` agree as soon as the tensor comparisons `ζ`
are natural and the corresponding identity holds before the reading `R`. -/
theorem CategoryTheory.Functor.evaluation_comp_eq_of_readings {𝒳₀ 𝒳₁ 𝒜 ℬ : Type*}
    [Category 𝒳₀] [Category 𝒳₁] [Category 𝒜] [iℬ : Category ℬ]
    (F : ℬ ⥤ ℬ ⥤ ℬ) (R : 𝒜 ⥤ ℬ) (G₀ : 𝒳₀ ⥤ 𝒜) (G₁ : 𝒳₁ ⥤ 𝒜)
    {P₀ Q₀ U₀ : 𝒳₀} {P₁ Q₁ U₁ : 𝒳₁} {Y₀ Y₁ M₀ M₁ M₂ O : 𝒜} {a a' l₀ l₁ : 𝒜} {V : ℬ}
    (t₀ : G₀.obj P₀ ≅ Y₀) (z₀ : R.obj Y₀ ≅ (F.obj (R.obj a)).obj (R.obj l₀)) (s₀ : P₀ ≅ U₀)
    (m₀ : G₀.obj U₀ ≅ O)
    (t₁ : G₁.obj P₁ ≅ Y₁) (z₁ : R.obj Y₁ ≅ (F.obj (R.obj a')).obj (R.obj l₁)) (s₁ : P₁ ≅ U₁)
    (m₁ : G₁.obj U₁ ≅ O) (w : R.obj O ≅ V) (φ : l₁ ⟶ l₀) (d : a ⟶ a')
    (a₀ : Q₀ ≅ P₀) (n₀ : G₀.obj Q₀ ≅ M₀) (a₁ : Q₁ ≅ P₁) (n₁ : G₁.obj Q₁ ≅ M₁)
    (ζ₀ : R.obj M₀ ≅ (F.obj (R.obj a)).obj (R.obj l₀))
    (ζ₁ : R.obj M₁ ≅ (F.obj (R.obj a')).obj (R.obj l₁))
    (ζ₂ : R.obj M₂ ≅ (F.obj (R.obj a)).obj (R.obj l₁)) (c₀ : M₂ ⟶ M₀) (c₁ : M₂ ⟶ M₁)
    (hμ₀ : (R.mapIso t₀ ≪≫ z₀).hom = ((G₀ ⋙ R).mapIso a₀.symm).hom ≫ R.map n₀.hom ≫ ζ₀.hom)
    (hμ₁ : (R.mapIso t₁ ≪≫ z₁).hom = ((G₁ ⋙ R).mapIso a₁.symm).hom ≫ R.map n₁.hom ≫ ζ₁.hom)
    (hζ₀ : R.map c₀ ≫ ζ₀.hom = ζ₂.hom ≫ (F.map (R.map (𝟙 a))).app (R.obj l₁) ≫
      (F.obj (R.obj a)).map (R.map φ))
    (hζ₁ : R.map c₁ ≫ ζ₁.hom = ζ₂.hom ≫ (F.map (R.map d)).app (R.obj l₁) ≫
      (F.obj (R.obj a')).map (R.map (𝟙 l₁)))
    (hsp : c₀ ≫ (G₀.mapIso a₀.symm ≪≫ n₀).inv ≫ G₀.map s₀.hom ≫ m₀.hom =
      c₁ ≫ (G₁.mapIso a₁.symm ≪≫ n₁).inv ≫ G₁.map s₁.hom ≫ m₁.hom) :
    (F.obj (R.obj a)).map (R.map φ) ≫ (R.mapIso t₀ ≪≫ z₀).inv ≫ ((G₀ ⋙ R).mapIso s₀).hom ≫
        (R.mapIso m₀ ≪≫ w).hom =
      (F.map (R.map d)).app (R.obj l₁) ≫ (R.mapIso t₁ ≪≫ z₁).inv ≫
        ((G₁ ⋙ R).mapIso s₁).hom ≫ (R.mapIso m₁ ≪≫ w).hom := by
  refine (reading_inv_comp_eq R G₀ t₀ z₀ s₀ m₀ w a₀ n₀ ζ₀ ζ₂ c₀ _ hμ₀ (by simpa using hζ₀)).trans
    (Eq.trans ?_ (reading_inv_comp_eq R G₁ t₁ z₁ s₁ m₁ w a₁ n₁ ζ₁ ζ₂ c₁ _ hμ₁
      (by simpa using hζ₁)).symm)
  simpa only [Functor.map_comp, Category.assoc, Iso.trans_inv, Functor.mapIso_inv] using
    congrArg (fun f => ζ₂.inv ≫ R.map f ≫ w.hom) hsp

/-- **The evaluation of tensor inverses over two spaces**: for `G = g^*`, `V = v^*`,
`W = (u ∘ h)^*` and `η : G ⋙ V ≅ W` monoidal and unital, the inverse image along `V` of the
inverse image of tensor inverses `t` along `G` evaluates as the inverse image along `W` of the
trivialisation of `ℒ^{⊗ -1} ⊗ ℒ`. -/
theorem CategoryTheory.Functor.inverseEvaluation_twoSpace {𝒳 𝒴 𝒯 : Type*} [Category 𝒳]
    [MonoidalCategory 𝒳] [Category 𝒴] [MonoidalCategory 𝒴] [Category 𝒯] [MonoidalCategory 𝒯]
    (G : 𝒳 ⥤ 𝒴) (V : 𝒴 ⥤ 𝒯) (W : 𝒳 ⥤ 𝒯) (η : G ⋙ V ≅ W) (F' : 𝒴 ⥤ 𝒴 ⥤ 𝒴)
    {Λ L FΛL O : 𝒳} {Λ' O' : 𝒴} {O'' : 𝒯}
    (a₀ : Λ ⊗ L ≅ FΛL) (s : FΛL ⟶ O) (a₁ : Λ' ⊗ G.obj L ≅ (F'.obj Λ').obj (G.obj L))
    (s' : (F'.obj Λ').obj (G.obj L) ⟶ O')
    (a₂ : G.obj Λ ⊗ G.obj L ≅ (F'.obj (G.obj Λ)).obj (G.obj L))
    (cG : G.obj FΛL ≅ (F'.obj (G.obj Λ)).obj (G.obj L)) (uG : G.obj O ⟶ O')
    (mG : G.obj (Λ ⊗ L) ≅ G.obj Λ ⊗ G.obj L)
    (mV : V.obj (Λ' ⊗ G.obj L) ≅ V.obj Λ' ⊗ V.obj (G.obj L))
    (mV₂ : V.obj (G.obj Λ ⊗ G.obj L) ≅ V.obj (G.obj Λ) ⊗ V.obj (G.obj L)) (uV : V.obj O' ⟶ O'')
    (mW : W.obj (Λ ⊗ L) ≅ W.obj Λ ⊗ W.obj L) (uW : W.obj O ⟶ O'') (t : G.obj Λ ⟶ Λ')
    (hmG : mG = G.mapIso a₀ ≪≫ cG ≪≫ a₂.symm)
    (ha₁ : (t ⊗ₘ 𝟙 (G.obj L)) ≫ a₁.hom =
      a₂.hom ≫ (F'.map t).app (G.obj L) ≫ (F'.obj Λ').map (𝟙 (G.obj L)))
    (hev : (F'.map t).app (G.obj L) ≫ s' = cG.inv ≫ G.map s ≫ uG)
    (hnat : V.map (t ⊗ₘ 𝟙 (G.obj L)) ≫ mV.hom = mV₂.hom ≫ (V.map t ⊗ₘ V.map (𝟙 (G.obj L))))
    (hmono : η.hom.app (Λ ⊗ L) ≫ mW.hom =
      V.map mG.hom ≫ mV₂.hom ≫ (η.hom.app Λ ⊗ₘ η.hom.app L))
    (hunit : η.hom.app O ≫ uW = V.map uG ≫ uV) :
    (𝟙 (W.obj Λ) ⊗ₘ η.hom.app L) ≫ (W.mapIso a₀.symm ≪≫ mW).inv ≫ W.map s ≫ uW =
      ((η.inv.app Λ ≫ V.map t) ⊗ₘ 𝟙 (V.obj (G.obj L))) ≫ (V.mapIso a₁.symm ≪≫ mV).inv ≫
        V.map s' ≫ uV := by
  have hev' : (t ⊗ₘ 𝟙 (G.obj L)) ≫ a₁.hom ≫ s' = mG.inv ≫ G.map (a₀.hom ≫ s) ≫ uG := by
    rw [reassoc_of% ha₁, Functor.map_id, Category.id_comp, hev, hmG]
    simp
  have hnat' : (V.map t ⊗ₘ 𝟙 (V.obj (G.obj L))) ≫ mV.inv =
      mV₂.inv ≫ V.map (t ⊗ₘ 𝟙 (G.obj L)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hnat, Functor.map_id, Iso.inv_hom_id_assoc]
  have hmono' : mV₂.inv ≫ V.map mG.inv ≫ η.hom.app (Λ ⊗ L) =
      (η.hom.app Λ ⊗ₘ η.hom.app L) ≫ mW.inv := by
    rw [Iso.eq_comp_inv]
    simp only [Category.assoc]
    rw [hmono, ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_assoc]
  have hnatη : V.map (G.map (a₀.hom ≫ s)) ≫ η.hom.app O =
      η.hom.app (Λ ⊗ L) ≫ W.map (a₀.hom ≫ s) :=
    η.hom.naturality (a₀.hom ≫ s)
  have e1 : V.map (t ⊗ₘ 𝟙 (G.obj L)) ≫ V.map a₁.hom ≫ V.map s' ≫ uV =
      V.map mG.inv ≫ V.map (G.map (a₀.hom ≫ s)) ≫ η.hom.app O ≫ uW := by
    rw [hunit]
    simpa only [Functor.map_comp, Category.assoc] using congrArg (fun f => V.map f ≫ uV) hev'
  have hc : (η.inv.app Λ ⊗ₘ 𝟙 (V.obj (G.obj L))) ≫ (η.hom.app Λ ⊗ₘ η.hom.app L) =
      (𝟙 (W.obj Λ) ⊗ₘ η.hom.app L) := by
    rw [tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Category.id_comp]
  symm
  calc ((η.inv.app Λ ≫ V.map t) ⊗ₘ 𝟙 (V.obj (G.obj L))) ≫ (V.mapIso a₁.symm ≪≫ mV).inv ≫
        V.map s' ≫ uV
      = (η.inv.app Λ ⊗ₘ 𝟙 (V.obj (G.obj L))) ≫ ((V.map t ⊗ₘ 𝟙 (V.obj (G.obj L))) ≫ mV.inv) ≫
          V.map a₁.hom ≫ V.map s' ≫ uV := by
        simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
          tensorHom_comp_tensorHom_assoc, Category.comp_id]
    _ = (η.inv.app Λ ⊗ₘ 𝟙 (V.obj (G.obj L))) ≫ mV₂.inv ≫ V.map mG.inv ≫
          (η.hom.app (Λ ⊗ L) ≫ W.map (a₀.hom ≫ s)) ≫ uW := by
        rw [hnat', ← hnatη]
        simp only [Category.assoc, e1]
    _ = ((η.inv.app Λ ⊗ₘ 𝟙 (V.obj (G.obj L))) ≫ (η.hom.app Λ ⊗ₘ η.hom.app L)) ≫ mW.inv ≫
          W.map (a₀.hom ≫ s) ≫ uW := by
        simp only [Category.assoc, reassoc_of% hmono']
    _ = _ := by
        rw [hc]
        simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
          Functor.map_comp]

section Divisors

open AlgebraicGeometry Stacks.SheafOfModules.Invertible

namespace Stacks.Divisors

/-- The tensor product of the identity of `M` with `e`, as the action of `M ⊗ -` on `e`. -/
theorem tensorProductIso_refl_hom {X : Scheme.{u}} (M : X.Modules) {N N' : X.Modules}
    (e : N ≅ N') :
    (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl M) e).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj M).map e.hom :=
  rfl

/-- **The evaluation of the inverse-line base change of Stacks 0B3V**: tensored with `Q'.L` and
followed by the trivialisation, it is the identification `Q'.L ≅ g^*Q.L` followed by the pulled
back pairing. -/
theorem inverseQuotientBaseChange_hom_tensor {X X' : Scheme.{u}} (g : X' ⟶ X)
    (E : X.Modules) (E' : X'.Modules) (Q : InvertibleQuotient X E)
    (Q' : InvertibleQuotient X' E') (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L) :
    letI := Q.invertible
    letI := Q'.invertible
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        (X'.presheaf) (forget₂ CommRingCat RingCat) (X'.ringCatSheaf.2)⟩).map
        (inverseQuotientBaseChange g E E' Q Q' hL).hom).app Q'.L ≫
      (tensorPowerSuccIso X'.presheaf X'.ringCatSheaf.2 Q'.L (-1)).hom =
    (tensorProductIso X'.presheaf X'.ringCatSheaf.2 (Iso.refl _) hL).hom ≫
      (inverseQuotientBaseChangePairing g Q.L).hom := by
  let := Q.invertible
  let := Q'.invertible
  exact congrArg Iso.hom (isoTensorPowerNegOne_mapIso_app_trans X'.presheaf X'.ringCatSheaf.2
    Q'.L _ (tensorProductIso X'.presheaf X'.ringCatSheaf.2 (Iso.refl _) hL ≪≫
      inverseQuotientBaseChangePairing g Q.L))

end Stacks.Divisors

end Divisors

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The inverse image of tensor inverses is normalised by the evaluation**, along any morphism
of algebraic spaces: `(f^*(ℒ^{⊗ -1}) ⊗ 1) ≫ ev = 03EL⁻¹ ≫ f^*(ev) ≫ (f^*𝒪 ≅ 𝒪)`. -/
theorem modulePullbackTensorPowerIso_neg_one_evaluation {Y Y' : AlgebraicSpaces B S hS}
    (f : Y' ⟶ Y) (L : Modules.{u, u} B S hS Y.1 Y.2)
    [hL : IsInvertible (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L] :
    haveI := isInvertible_modulePullback_obj B S hS f L hL
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS Y'.1 Y'.2)).map
        (modulePullbackTensorPowerIso f L (-1)).hom).app ((modulePullback B S hS f).obj L) ≫
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS Y')
        (structureRingSheaf B S hS Y').property ((modulePullback B S hS f).obj L) (-1)).hom =
      (modulePullbackTensorComparison f L
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y)
            (structureRingSheaf B S hS Y).property L (-1))).inv ≫
        (modulePullback B S hS f).map
          (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS Y)
            (structureRingSheaf B S hS Y).property L (-1)).hom ≫
        (modulePullbackUnitIso B S hS f).hom := by
  have hfL := isInvertible_modulePullback_obj B S hS f L hL
  have := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L
  have := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    (structureCommRings B S hS Y') (structureRingSheaf B S hS Y').property
    ((modulePullback B S hS f).obj L)
  have h := Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_tensorPowerSuccIso
    (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property
    (structureCommRings B S hS Y') (structureRingSheaf B S hS Y').property
    (modulePullback B S hS f) L (modulePullbackTensorComparison f L)
    (modulePullbackUnitIso B S hS f) (-1)
  have h0 := Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_zero
    (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property
    (structureCommRings B S hS Y') (structureRingSheaf B S hS Y').property
    (modulePullback B S hS f) L (modulePullbackTensorComparison f L)
    (modulePullbackUnitIso B S hS f)
  have h0' : (Stacks.SheafOfModules.TensorPower.mapTensorPowerIso
      (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property
      (structureCommRings B S hS Y') (structureRingSheaf B S hS Y').property
      (modulePullback B S hS f) L (modulePullbackTensorComparison f L)
      (modulePullbackUnitIso B S hS f) ((-1 : ℤ) + 1)).hom =
      (modulePullbackUnitIso B S hS f).hom := congrArg Iso.hom h0
  exact (Iso.eq_inv_comp _).2 (h.symm.trans (congrArg (_ ≫ ·) h0'))

section Evaluation

variable (Y : AlgebraicSpaces B S hS) (T₁ : BigFppfOver B S hS) (y : yoneda.obj T₁ ⟶ Y.1)
  (L : Modules.{u, u} B S hS Y.1 Y.2)
  [hL : IsInvertible (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L]

/-- **The evaluation of the inverse-line factor at a scheme point**: the Zariski reading of the
pullback of the trivialisation of `ℒ^{⊗ -1} ⊗ ℒ`, through Stacks 03EL for `y`, the Zariski
reading tensor isomorphism and the identifications of the structure sheaves. -/
def inversePointEvaluation :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T₁).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2⟩).obj
        ((zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom y)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y)
            (structureRingSheaf B S hS Y).property L (-1))))).obj
        ((zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom y)).obj L)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2) :=
  haveI hyL := isInvertible_modulePullback_obj B S hS (pointHom y) L hL
  ((zariskiReadingFunctor T₁).mapIso (modulePullbackTensorComparison (pointHom y) L
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y)
        (structureRingSheaf B S hS Y).property L (-1))) ≪≫
    zariskiReadingTensorIso T₁ _ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom y) _
        (isQuasicoherentOnSite_invertibleTensorPower Y L (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _ hyL)).inv ≫
    ((modulePullback B S hS (pointHom y) ⋙ zariskiReadingFunctor T₁).mapIso
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS Y)
        (structureRingSheaf B S hS Y).property L (-1))).hom ≫
    ((zariskiReadingFunctor T₁).mapIso (modulePullbackUnitIso B S hS (pointHom y)) ≪≫
      zariskiReadingUnitIso T₁).hom

/-- **The evaluation of the inverse-line factor `i_y`** is `inversePointEvaluation`. -/
theorem inversePointReadingIso_evaluationEq :
    haveI := isInvertible_zariskiReading T₁ ((modulePullback B S hS (pointHom y)).obj L)
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
        (isInvertible_modulePullback_obj B S hS (pointHom y) L hL))
    CategoryTheory.Functor.EvaluationEq
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T₁).Modules) (iℬ := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T₁).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2⟩)
      (L₀ := (zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom y)).obj L))
      (U := SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2))
      (inversePointReadingIso Y T₁ y L).hom
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2
        ((zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom y)).obj L)) (-1)).hom
      (inversePointEvaluation Y T₁ y L) :=
  CategoryTheory.Functor.mapIso_app_trans_hom_eq _ _ _ _ _ _ _ _ _ _
    (inversePointReadingIso_evaluation Y T₁ y L)

/-- **The comparison of the evaluations at two scheme points, reduced to the spaces**: if the
identity of the space-level evaluations holds after `1 ⊗ φ` and `d ⊗ 1`, then the Zariski
readings of `φ` and `d` intertwine `inversePointEvaluation` at `x` and at `y`. -/
theorem inversePointEvaluation_comp_eq_of_space (Y₀ Y₁ : AlgebraicSpaces B S hS)
    (T₁ : BigFppfOver B S hS) (x : yoneda.obj T₁ ⟶ Y₀.1) (y : yoneda.obj T₁ ⟶ Y₁.1)
    (L : Modules.{u, u} B S hS Y₀.1 Y₀.2)
    [hL : IsInvertible (structureCommRings B S hS Y₀) (structureRingSheaf B S hS Y₀).property L]
    (L' : Modules.{u, u} B S hS Y₁.1 Y₁.2)
    [hL' : IsInvertible (structureCommRings B S hS Y₁) (structureRingSheaf B S hS Y₁).property L']
    (φs : (modulePullback B S hS (pointHom y)).obj L' ⟶ (modulePullback B S hS (pointHom x)).obj L)
    (ds : (modulePullback B S hS (pointHom x)).obj
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₀)
        (structureRingSheaf B S hS Y₀).property L (-1)) ⟶
      (modulePullback B S hS (pointHom y)).obj
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₁)
          (structureRingSheaf B S hS Y₁).property L' (-1)))
    (hsp : MonoidalCategory.tensorHom
      (𝟙 ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₀)
            (structureRingSheaf B S hS Y₀).property L (-1)))) φs ≫
        ((modulePullback B S hS (pointHom x)).mapIso
          (modulesTensorObjIso B S hS Y₀.1 Y₀.2
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₀)
              (structureRingSheaf B S hS Y₀).property L (-1)) L).symm ≪≫
          modulePullbackTensorIso B S hS (pointHom x)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₀)
              (structureRingSheaf B S hS Y₀).property L (-1)) L).inv ≫
        (modulePullback B S hS (pointHom x)).map
          (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS Y₀)
            (structureRingSheaf B S hS Y₀).property L (-1)).hom ≫
        (modulePullbackUnitIso B S hS (pointHom x)).hom =
      MonoidalCategory.tensorHom ds (𝟙 ((modulePullback B S hS (pointHom y)).obj L')) ≫
        ((modulePullback B S hS (pointHom y)).mapIso
          (modulesTensorObjIso B S hS Y₁.1 Y₁.2
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₁)
              (structureRingSheaf B S hS Y₁).property L' (-1)) L').symm ≪≫
          modulePullbackTensorIso B S hS (pointHom y)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₁)
              (structureRingSheaf B S hS Y₁).property L' (-1)) L').inv ≫
        (modulePullback B S hS (pointHom y)).map
          (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS Y₁)
            (structureRingSheaf B S hS Y₁).property L' (-1)).hom ≫
        (modulePullbackUnitIso B S hS (pointHom y)).hom) :
    CategoryTheory.Functor.EvaluationCompSquare
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T₁).Modules) (iℬ := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T₁).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2⟩)
      (U := SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2))
      ((zariskiReadingFunctor T₁).map φs) ((zariskiReadingFunctor T₁).map ds)
      (inversePointEvaluation Y₀ T₁ x L) (inversePointEvaluation Y₁ T₁ y L') := by
  unfold inversePointEvaluation
  exact CategoryTheory.Functor.evaluation_comp_eq_of_readings
    (iℬ := Scheme.Modules.instCategory)
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T₁).presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2⟩)
    (zariskiReadingFunctor T₁) (modulePullback B S hS (pointHom x))
    (modulePullback B S hS (pointHom y)) _ _ _ _ _ _ _ _ _ φs ds
    (modulesTensorObjIso B S hS Y₀.1 Y₀.2
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₀)
        (structureRingSheaf B S hS Y₀).property L (-1)) L)
    (modulePullbackTensorIso B S hS (pointHom x)
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₀)
        (structureRingSheaf B S hS Y₀).property L (-1)) L)
    (modulesTensorObjIso B S hS Y₁.1 Y₁.2
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₁)
        (structureRingSheaf B S hS Y₁).property L' (-1)) L')
    (modulePullbackTensorIso B S hS (pointHom y)
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₁)
        (structureRingSheaf B S hS Y₁).property L' (-1)) L')
    (zariskiReadingTensorObjIso T₁
      ((modulePullback B S hS (pointHom x)).obj
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₀)
          (structureRingSheaf B S hS Y₀).property L (-1)))
      ((modulePullback B S hS (pointHom x)).obj L)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₀ L (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom x) L hL)) ≪≫
      monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T₁) _ _)
    (zariskiReadingTensorObjIso T₁
      ((modulePullback B S hS (pointHom y)).obj
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₁)
          (structureRingSheaf B S hS Y₁).property L' (-1)))
      ((modulePullback B S hS (pointHom y)).obj L')
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom y) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₁ L' (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom y) L' hL')) ≪≫
      monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T₁) _ _)
    (zariskiReadingTensorObjIso T₁
      ((modulePullback B S hS (pointHom x)).obj
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS Y₀)
          (structureRingSheaf B S hS Y₀).property L (-1)))
      ((modulePullback B S hS (pointHom y)).obj L')
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₀ L (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom y) L' hL')) ≪≫
      monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T₁) _ _)
    _ _
    (zariskiReading_mapIso_modulePullbackTensorComparison_trans_hom (pointHom x) _ L
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₀ L (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom x) L hL)))
    (zariskiReading_mapIso_modulePullbackTensorComparison_trans_hom (pointHom y) _ L'
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom y) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₁ L' (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom y) L' hL')))
    (zariskiReadingTensorObjIso_hom_naturality_sheafTensor T₁ (𝟙 _) φs
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₀ L (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom y) L' hL'))
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₀ L (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom x) L hL)))
    (zariskiReadingTensorObjIso_hom_naturality_sheafTensor T₁ ds (𝟙 _)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₀ L (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom y) L' hL'))
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom y) _
        (isQuasicoherentOnSite_invertibleTensorPower Y₁ L' (-1)))
      (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T₁) _
        (isInvertible_modulePullback_obj B S hS (pointHom y) L' hL')))
    hsp

end Evaluation

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  {T T' : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1) (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T)
  (hvh : v ≫ g.hom = yoneda.map h ≫ u)

/-- **`v^*g^* ≅ (u ∘ h)^*` is compatible with the identifications of the structure sheaves**
(Stacks 03LU at `𝒪`). -/
theorem pointPullbackCompIso_hom_app_unit :
    (pointPullbackCompIso X g u v h hvh).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
      (modulePullbackUnitIso B S hS (pointHom (X := X) (yoneda.map h ≫ u))).hom =
    (modulePullback B S hS (pointHom v)).map (modulePullbackUnitIso B S hS g).hom ≫
      (modulePullbackUnitIso B S hS (pointHom v)).hom := by
  rw [pointPullbackCompIso_eq]
  have key : ∀ (φ : yonedaSpace B S hS T' ⟶ X) (p : pointHom v ≫ g = φ),
      (modulePullbackCompIso B S hS (pointHom v) g ≪≫
          eqToIso (congrArg (modulePullback B S hS) p)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
        (modulePullbackUnitIso B S hS φ).hom =
      (modulePullback B S hS (pointHom v)).map (modulePullbackUnitIso B S hS g).hom ≫
        (modulePullbackUnitIso B S hS (pointHom v)).hom := by
    rintro _ rfl
    simp only [eqToIso_refl, Iso.trans_refl]
    exact ((Iso.inv_comp_eq ((modulePullbackCompIso B S hS (pointHom v) g).app _)).mp
      (modulePullbackCompIso_inv_app_unit_comp (pointHom v) g)).symm
  exact key (pointHom (X := X) (yoneda.map h ≫ u)) (ObjectProperty.hom_ext _ hvh)

/-- `Stacks.Divisors.inverseQuotientBaseChange_hom_tensor` at the quotient `q_x` of a scheme
point, with the trivialisation written at the Zariski reading of `x^*ℒ`. -/
theorem inverseQuotientBaseChange_sectionPointQuotient_hom_tensor
    (Q : InvertibleQuotient X E) {T₀ T₁ : BigFppfOver B S hS} (k : T₁ ⟶ T₀)
    {E₀ : ((BigFppfOver.toScheme B S hS).obj T₀).Modules}
    (Q₀ : Stacks.Divisors.InvertibleQuotient ((BigFppfOver.toScheme B S hS).obj T₀) E₀)
    (x : yoneda.obj T₁ ⟶ X.1)
    (hL : (sectionPointQuotient X E hE Q T₁ x).L ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k)).obj Q₀.L) :
    haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
      Q.invertible.toAlgebraicGeometry
    haveI := isInvertible_zariskiReading T₁ ((modulePullback B S hS (pointHom x)).obj Q.L)
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
        (isInvertible_modulePullback_obj B S hS (pointHom x) Q.L
          Q.invertible.toAlgebraicGeometry))
    letI := Q₀.invertible
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T₁).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2⟩).map
        (Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map k) E₀
          (pointZariskiModule X E T₁ x) Q₀ (sectionPointQuotient X E hE Q T₁ x) hL).hom).app
        (sectionPointQuotient X E hE Q T₁ x).L ≫
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2
        ((zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom x)).obj Q.L)) (-1)).hom =
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T₁).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2⟩).obj
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower
            ((BigFppfOver.toScheme B S hS).obj T₀).presheaf
            ((BigFppfOver.toScheme B S hS).obj T₀).ringCatSheaf.2 Q₀.L (-1)))).map hL.hom ≫
      (Stacks.Divisors.inverseQuotientBaseChangePairing ((BigFppfOver.toScheme B S hS).map k)
        Q₀.L).hom :=
  (Stacks.Divisors.inverseQuotientBaseChange_hom_tensor ((BigFppfOver.toScheme B S hS).map k)
    E₀ (pointZariskiModule X E T₁ x) Q₀ (sectionPointQuotient X E hE Q T₁ x) hL).trans
    (congrArg (· ≫ _) (Stacks.Divisors.tensorProductIso_refl_hom _ _))

/-- **The comparison of the inverse-line base changes of Stacks 0B3V at two scheme points**
evaluates through the identification `φ` of the two invertible modules over `τ^*ℒ₀`. -/
theorem inverseQuotientBaseChange_inv_comp_hom_evaluation
    (Q : InvertibleQuotient X E) {Y : AlgebraicSpaces B S hS}
    (EY : SheafOfModules.{u} (structureRingSheaf B S hS Y)) (hEY : EY.IsQuasicoherentOnSite)
    (QY : InvertibleQuotient Y EY) {T₀ T₁ : BigFppfOver B S hS} (k : T₁ ⟶ T₀)
    {E₀ : ((BigFppfOver.toScheme B S hS).obj T₀).Modules}
    (Q₀ : Stacks.Divisors.InvertibleQuotient ((BigFppfOver.toScheme B S hS).obj T₀) E₀)
    (x : yoneda.obj T₁ ⟶ X.1) (y : yoneda.obj T₁ ⟶ Y.1)
    (hL₀ : (sectionPointQuotient X E hE Q T₁ x).L ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k)).obj Q₀.L)
    (hL₁ : (sectionPointQuotient Y EY hEY QY T₁ y).L ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k)).obj Q₀.L)
    (φ : (zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom y)).obj QY.L) ⟶
      (zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom x)).obj Q.L))
    (hφ : φ ≫ hL₀.hom = hL₁.hom) :
    haveI := isInvertible_zariskiReading T₁ ((modulePullback B S hS (pointHom x)).obj Q.L)
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
        (isInvertible_modulePullback_obj B S hS (pointHom x) Q.L
          Q.invertible.toAlgebraicGeometry))
    haveI := isInvertible_zariskiReading T₁ ((modulePullback B S hS (pointHom y)).obj QY.L)
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
        (isInvertible_modulePullback_obj B S hS (pointHom y) QY.L
          QY.invertible.toAlgebraicGeometry))
    CategoryTheory.Functor.EvaluationSquare
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T₁).Modules) (iℬ := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T₁).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2⟩)
      (Λ₀ := Stacks.SheafOfModules.Invertible.tensorPower
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2
        ((zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom x)).obj Q.L)) (-1))
      (Λ₁ := Stacks.SheafOfModules.Invertible.tensorPower
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2
        ((zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom y)).obj QY.L)) (-1))
      (L₀ := (zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom x)).obj Q.L))
      (L₁ := (zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom y)).obj QY.L))
      (U := SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2))
      ((Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map k) E₀
          (pointZariskiModule X E T₁ x) Q₀ (sectionPointQuotient X E hE Q T₁ x) hL₀).inv ≫
        (Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map k) E₀
          (pointZariskiModule Y EY T₁ y) Q₀ (sectionPointQuotient Y EY hEY QY T₁ y) hL₁).hom)
      φ
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2
        ((zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom x)).obj Q.L)) (-1)).hom
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
        ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2
        ((zariskiReadingFunctor T₁).obj ((modulePullback B S hS (pointHom y)).obj QY.L))
        (-1)).hom := by
  let := Q₀.invertible
  exact CategoryTheory.Functor.inv_comp_hom_evaluation
    (ℬ := ((BigFppfOver.toScheme B S hS).obj T₁).Modules) (iℬ := Scheme.Modules.instCategory)
    (U := SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      ((BigFppfOver.toScheme B S hS).obj T₁).presheaf
      ((BigFppfOver.toScheme B S hS).obj T₁).ringCatSheaf.2))
    _ _ _ hL₀ hL₁
    (Stacks.Divisors.inverseQuotientBaseChangePairing ((BigFppfOver.toScheme B S hS).map k)
      Q₀.L).hom _ _
    (inverseQuotientBaseChange_sectionPointQuotient_hom_tensor X E hE Q k Q₀ x hL₀)
    (inverseQuotientBaseChange_sectionPointQuotient_hom_tensor Y EY hEY QY k Q₀ y hL₁) φ hφ

/-- **The space-level evaluation identity over two spaces**: for a monoidal and unital
`η : g^* ⋙ y^* ≅ x^*`, the evaluations of `ℒ^{⊗ -1}` at `x` and of `(g^*ℒ)^{⊗ -1}` at `y` agree
after `1 ⊗ η` and `(η⁻¹ ≫ y^*(g^*(ℒ^{⊗ -1}) ≅ (g^*ℒ)^{⊗ -1})) ⊗ 1`. -/
theorem inversePointEvaluation_twoSpace_space {X X' : AlgebraicSpaces B S hS}
    {E : SheafOfModules.{u} (structureRingSheaf B S hS X)} (Q : InvertibleQuotient X E)
    (g : X' ⟶ X) {T₁ : BigFppfOver B S hS} (x : yoneda.obj T₁ ⟶ X.1) (y : yoneda.obj T₁ ⟶ X'.1)
    (η : modulePullback B S hS g ⋙ modulePullback B S hS (pointHom y) ≅
      modulePullback B S hS (pointHom x))
    (hmono : ∀ K₁ K₂ : Modules.{u, u} B S hS X.1 X.2,
      η.hom.app (K₁ ⊗ K₂) ≫ (modulePullbackTensorIso B S hS (pointHom x) K₁ K₂).hom =
        (modulePullback B S hS (pointHom y)).map (modulePullbackTensorIso B S hS g K₁ K₂).hom ≫
          (modulePullbackTensorIso B S hS (pointHom y) _ _).hom ≫
            (η.hom.app K₁ ⊗ₘ η.hom.app K₂))
    (hunit : η.hom.app (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
        (modulePullbackUnitIso B S hS (pointHom x)).hom =
      (modulePullback B S hS (pointHom y)).map (modulePullbackUnitIso B S hS g).hom ≫
        (modulePullbackUnitIso B S hS (pointHom y)).hom) :
    haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
      Q.invertible.toAlgebraicGeometry
    haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
        (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
    MonoidalCategory.tensorHom
      (𝟙 ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))) (η.hom.app Q.L) ≫
        ((modulePullback B S hS (pointHom x)).mapIso
          (modulesTensorObjIso B S hS X.1 X.2
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1)) Q.L).symm ≪≫
          modulePullbackTensorIso B S hS (pointHom x)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1)) Q.L).inv ≫
        (modulePullback B S hS (pointHom x)).map
          (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)).hom ≫
        (modulePullbackUnitIso B S hS (pointHom x)).hom =
      MonoidalCategory.tensorHom
        (η.inv.app (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)) ≫
          (modulePullback B S hS (pointHom y)).map (modulePullbackTensorPowerIso g Q.L (-1)).hom)
        (𝟙 ((modulePullback B S hS (pointHom y)).obj (Q.baseChange g (Iso.refl _)).L)) ≫
        ((modulePullback B S hS (pointHom y)).mapIso
          (modulesTensorObjIso B S hS X'.1 X'.2
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
              (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
            (Q.baseChange g (Iso.refl _)).L).symm ≪≫
          modulePullbackTensorIso B S hS (pointHom y)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
              (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
            (Q.baseChange g (Iso.refl _)).L).inv ≫
        (modulePullback B S hS (pointHom y)).map
          (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X')
            (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1)).hom ≫
        (modulePullbackUnitIso B S hS (pointHom y)).hom := by
  have hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
    Q.invertible.toAlgebraicGeometry
  exact CategoryTheory.Functor.inverseEvaluation_twoSpace _ _ _ η
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X'.1 X'.2))
    (modulesTensorObjIso B S hS X.1 X.2 _ _) _ (modulesTensorObjIso B S hS X'.1 X'.2 _ _) _
    (modulesTensorObjIso B S hS X'.1 X'.2 _ _)
    (modulePullbackTensorComparison g Q.L _) _
    (modulePullbackTensorIso B S hS g _ _) (modulePullbackTensorIso B S hS (pointHom y) _ _)
    (modulePullbackTensorIso B S hS (pointHom y) _ _) _
    (modulePullbackTensorIso B S hS (pointHom x) _ _) _ _ rfl
    (modulesTensorObjIso_hom_naturality B S hS _ _)
    (modulePullbackTensorPowerIso_neg_one_evaluation g Q.L)
    (modulePullbackTensorIso_hom_naturality B S hS (pointHom y) _ _)
    (hmono _ _) hunit

variable (Q : InvertibleQuotient X E)

/-- **The inverse-line factors of the source readings at `u ∘ h` on `X` and at `v` on `X'` are
intertwined** by the comparison of the two inverse-line base changes of Stacks 0B3V along `h`
and by `(u ∘ h)^* ≅ v^*g^*` followed by the inverse image of tensor inverses along `g`. -/
theorem inversePointReadingHom_twoSpace :
    haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
      Q.invertible.toAlgebraicGeometry
    haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
        (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
    (inversePointReadingIso X T' (yoneda.map h ≫ u) Q.L).hom ≫
      ((Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X E T' (yoneda.map h ≫ u))
        (sectionPointQuotient X E hE Q T u) (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u))
        (sectionPointQuotientBaseChangeL X E hE Q u h)).inv ≫
       (Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)).hom) =
    (zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).inv.app
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)) ≫
        (modulePullback B S hS (pointHom v)).map (modulePullbackTensorPowerIso g Q.L (-1)).hom) ≫
      (inversePointReadingIso X' T' v (Q.baseChange g (Iso.refl _)).L).hom := by
  have hQ' : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
      (Q.baseChange g (Iso.refl _)).L :=
      (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
  have := isInvertible_zariskiReading T' ((modulePullback B S hS (pointHom v)).obj
      (Q.baseChange g (Iso.refl _)).L)
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
      (isInvertible_modulePullback_obj B S hS (pointHom v) _ hQ'))
  -- The instance on `X` is inlined (term-mode `haveI`): bound as a local hypothesis
  -- it makes the kernel check of this proof time out.
  refine
    haveI := isInvertible_zariskiReading T'
        ((modulePullback B S hS (pointHom (yoneda.map h ≫ u))).obj Q.L)
        ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
          (isInvertible_modulePullback_obj B S hS (pointHom (yoneda.map h ≫ u)) Q.L
            Q.invertible.toAlgebraicGeometry))
    CategoryTheory.Functor.comp_eq_comp_of_evaluation
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules) (iℬ := Scheme.Modules.instCategory)
      (U := SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        ((BigFppfOver.toScheme B S hS).obj T').presheaf
        ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2))
      (Λ₀ := Stacks.SheafOfModules.Invertible.tensorPower
          ((BigFppfOver.toScheme B S hS).obj T').presheaf
          ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (pointHom (yoneda.map h ≫ u))).obj Q.L)) (-1))
      (Λ₁ := Stacks.SheafOfModules.Invertible.tensorPower
          ((BigFppfOver.toScheme B S hS).obj T').presheaf
          ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj
            (Q.baseChange g (Iso.refl _)).L)) (-1))
      (L₀ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (pointHom (yoneda.map h ≫ u))).obj Q.L))
      (L₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj
            (Q.baseChange g (Iso.refl _)).L))
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      _ _ _ _
      ((zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).hom.app Q.L))
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        ((BigFppfOver.toScheme B S hS).obj T').presheaf
        ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2
        ((zariskiReadingFunctor T').obj
          ((modulePullback B S hS (pointHom (yoneda.map h ≫ u))).obj Q.L)) (-1)).hom
      (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso
        ((BigFppfOver.toScheme B S hS).obj T').presheaf
        ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2
        ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj
          (Q.baseChange g (Iso.refl _)).L)) (-1)).hom
      (inversePointEvaluation X T' (yoneda.map h ≫ u) Q.L (hL := Q.invertible.toAlgebraicGeometry))
      (inversePointEvaluation X' T' v (Q.baseChange g (Iso.refl _)).L
        (hL := (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry)) ?hδ
      ?hi ?hi' ?hm ?huniq
  case hi =>
    exact inversePointReadingIso_evaluationEq X T' (yoneda.map h ≫ u) Q.L
      (hL := Q.invertible.toAlgebraicGeometry)
  case hi' =>
    exact inversePointReadingIso_evaluationEq X' T' v (Q.baseChange g (Iso.refl _)).L
      (hL := (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry)
  case huniq =>
    exact fun α β hαβ => Stacks.SheafOfModules.Invertible.map_app_injective_of_comp_iso _ _ _
      (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T' v).invertible _ α β hαβ
  case hδ =>
    exact inverseQuotientBaseChange_inv_comp_hom_evaluation X E hE Q
      ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      (Q.baseChange g (Iso.refl _)) h (sectionPointQuotient X E hE Q T u) (yoneda.map h ≫ u) v
      (sectionPointQuotientBaseChangeL X E hE Q u h)
      (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q) _ rfl
  case hm =>
    exact inversePointEvaluation_comp_eq_of_space X X' T' (yoneda.map h ≫ u) v Q.L
      (hL := Q.invertible.toAlgebraicGeometry) (Q.baseChange g (Iso.refl _)).L
      (hL' := (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry) _ _
      (inversePointEvaluation_twoSpace_space Q g (yoneda.map h ≫ u) v
        (pointPullbackCompIso X g u v h hvh) (pointPullbackCompIso_hom_app_tensor X g u v h hvh)
        (pointPullbackCompIso_hom_app_unit X g u v h hvh))


end AlgebraicGeometry.Space

end
