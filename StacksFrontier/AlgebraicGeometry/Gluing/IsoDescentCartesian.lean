module

public import StacksFrontier.AlgebraicGeometry.Gluing.IsoDescent

/-!
# Descending a cartesian comparison through a cofiltered limit, compatibly

Let `D` be a cofiltered inverse system of quasi-compact, quasi-separated schemes with affine
transition morphisms and let `c` be a limit cone over it. Let `pP : P ⟶ D.obj i₁` and
`q : Zy ⟶ D.obj i` be of finite presentation, let `j₁ : i₁ ⟶ i`, and suppose a single scheme
`Plim` presents *both* the base change of `pP` along `c.π.app i₁` and the base change of `q`
along `c.π.app i₁ ≫ D.map j₁`. Then at some stage `i₂` over `i₁` the base change of `pP` along
the transition already presents the base change of `q`, **and the comparison it provides
restricts over the limit to the given one**.

## Main results

* `AlgebraicGeometry.exists_stage_isPullback_of_isPullback_limit`: the statement above, with the
  cartesian square at the final stage universally quantified.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- The content of `AlgebraicGeometry.exists_stage_isPullback_of_isPullback_limit`, with the two
objects over the stage `i₁` abstract and the second of them presented as a base change of `q` by
a hypothesis rather than formed as a chosen fibre product. -/
private theorem exists_stage_isPullback_aux (i₁ i : I) (j₁ : i₁ ⟶ i)
    {Zy : Scheme.{u}} (q : Zy ⟶ D.obj i)
    (X Y : Over (D.obj i₁)) (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (πY : Y.left ⟶ Zy) (hYsq : IsPullback πY Y.hom q (D.map j₁))
    {Plim : Scheme.{u}} {a : Plim ⟶ X.left} {plim : Plim ⟶ c.pt}
    (hP : IsPullback a plim X.hom (c.π.app i₁))
    {glim : Plim ⟶ Zy} (hg : IsPullback glim plim q (c.π.app i₁ ≫ D.map j₁)) :
    ∃ (i₂ : I) (e : i₂ ⟶ i₁),
      ∀ {P₂ : Scheme.{u}} {b : P₂ ⟶ X.left} {p₂ : P₂ ⟶ D.obj i₂}
        (_ : IsPullback b p₂ X.hom (D.map e)) {k : Plim ⟶ P₂}
        (_ : k ≫ b = a) (_ : k ≫ p₂ = plim ≫ c.π.app i₂),
        ∃ h : P₂ ⟶ Zy,
          IsPullback h p₂ q (D.map e ≫ D.map j₁) ∧ k ≫ h = glim := by
  classical
  have hXlim : IsPullback (pullback.fst X.hom (c.π.app i₁)) (pullback.snd X.hom (c.π.app i₁))
      X.hom (c.π.app i₁) := IsPullback.of_hasPullback _ _
  have hYlim : IsPullback (pullback.fst Y.hom (c.π.app i₁)) (pullback.snd Y.hom (c.π.app i₁))
      Y.hom (c.π.app i₁) := IsPullback.of_hasPullback _ _
  have hWsq : IsPullback (pullback.fst Y.hom (c.π.app i₁) ≫ πY)
      (pullback.snd Y.hom (c.π.app i₁)) q (c.π.app i₁ ≫ D.map j₁) := hYlim.paste_horiz hYsq
  obtain ⟨ψ, hψfst, hψsnd⟩ : ∃ ψ : Plim ≅ pullback X.hom (c.π.app i₁),
      ψ.hom ≫ pullback.fst X.hom (c.π.app i₁) = a ∧
        ψ.hom ≫ pullback.snd X.hom (c.π.app i₁) = plim :=
    ⟨hP.isoIsPullback _ _ hXlim, hP.isoIsPullback_hom_fst _ _ hXlim,
      hP.isoIsPullback_hom_snd _ _ hXlim⟩
  obtain ⟨φ, hφfst, hφsnd⟩ : ∃ φ : Plim ≅ pullback Y.hom (c.π.app i₁),
      φ.hom ≫ pullback.fst Y.hom (c.π.app i₁) ≫ πY = glim ∧
        φ.hom ≫ pullback.snd Y.hom (c.π.app i₁) = plim :=
    ⟨hg.isoIsPullback _ _ hWsq, hg.isoIsPullback_hom_fst _ _ hWsq,
      hg.isoIsPullback_hom_snd _ _ hWsq⟩
  have hψinvsnd : ψ.inv ≫ plim = pullback.snd X.hom (c.π.app i₁) := by
    rw [← hψsnd, Iso.inv_hom_id_assoc]
  obtain ⟨fiso, hfisoleft⟩ :
      ∃ fiso : (Over.pullback (c.π.app i₁)).obj X ≅ (Over.pullback (c.π.app i₁)).obj Y,
        fiso.hom.left = ψ.inv ≫ φ.hom :=
    ⟨Over.isoMk (ψ.symm ≪≫ φ) (by
      change (ψ.inv ≫ φ.hom) ≫ pullback.snd Y.hom (c.π.app i₁)
        = pullback.snd X.hom (c.π.app i₁)
      rw [Category.assoc, hφsnd, hψinvsnd]), rfl⟩
  obtain ⟨j, e₀, g, α, β, hα, hβ, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc i₁ X Y hX hY fiso.hom
  have hXjsq : IsPullback (pullback.fst X.hom (D.map e₀)) (pullback.snd X.hom (D.map e₀))
      X.hom (D.map e₀) := IsPullback.of_hasPullback _ _
  have hYjsq : IsPullback (pullback.fst Y.hom (D.map e₀)) (pullback.snd Y.hom (D.map e₀))
      Y.hom (D.map e₀) := IsPullback.of_hasPullback _ _
  have hjsq : IsPullback (pullback.fst Y.hom (D.map e₀) ≫ πY) (pullback.snd Y.hom (D.map e₀))
      q (D.map e₀ ≫ D.map j₁) := hYjsq.paste_horiz hYsq
  have hαid : α.inv.left ≫ α.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, α.inv_hom_id]; rfl
  have hαcancel : ∀ {Z : Scheme.{u}} (t : ((Over.pullback (c.π.app i₁)).obj X).left ⟶ Z),
      α.inv.left ≫ α.hom.left ≫ t = t := by
    intro Z t
    rw [← Category.assoc, hαid, Category.id_comp]
  have hlift : a ≫ X.hom = (plim ≫ c.π.app j) ≫ D.map e₀ := by
    rw [hP.w, Category.assoc, c.w e₀]
  obtain ⟨kj, hkjfst, hkjsnd⟩ : ∃ kj : Plim ⟶ pullback X.hom (D.map e₀),
      kj ≫ pullback.fst X.hom (D.map e₀) = a ∧
        kj ≫ pullback.snd X.hom (D.map e₀) = plim ≫ c.π.app j :=
    ⟨hXjsq.lift a (plim ≫ c.π.app j) hlift, hXjsq.lift_fst _ _ _, hXjsq.lift_snd _ _ _⟩
  have hkjκ : ψ.hom ≫ α.inv.left ≫
      pullback.fst ((Over.pullback (D.map e₀)).obj X).hom (c.π.app j) = kj := by
    refine hXjsq.hom_ext ?_ ?_
    · rw [hkjfst, Category.assoc, Category.assoc, ← hα, hαcancel, hψfst]
    · have hw : α.inv.left ≫ pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (c.π.app j)
          = pullback.snd X.hom (c.π.app i₁) := Over.w α.inv
      have hcond : pullback.fst ((Over.pullback (D.map e₀)).obj X).hom (c.π.app j) ≫
            pullback.snd X.hom (D.map e₀)
          = pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (c.π.app j) ≫ c.π.app j :=
        pullback.condition
      rw [Category.assoc, Category.assoc, hcond, reassoc_of% hw, reassoc_of% hψsnd, hkjsnd]
  have hkjhj : kj ≫ g.left ≫ pullback.fst Y.hom (D.map e₀) ≫ πY = glim := by
    have hcl : α.hom.left ≫ fiso.hom.left
        = ((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left := by
      simpa only [Over.comp_left] using congrArg Over.Hom.left hcomm
    rw [← hkjκ]
    simp only [Category.assoc]
    rw [← overPullback_map_left_fst_assoc, ← reassoc_of% hβ, ← reassoc_of% hcl, hαcancel,
      hfisoleft]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hφfst]
  obtain ⟨hXc, hXq⟩ := compactSpace_and_quasiSeparatedSpace_left X hX
  obtain ⟨hYc, hYq⟩ := compactSpace_and_quasiSeparatedSpace_left Y hY
  have hXjfp : FinitePresentation ((Over.pullback (D.map e₀)).obj X).hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (D.map e₀) X hX
  have hYjfp : FinitePresentation ((Over.pullback (D.map e₀)).obj Y).hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (D.map e₀) Y hY
  obtain ⟨hXjc, hXjq⟩ :=
    compactSpace_and_quasiSeparatedSpace_left ((Over.pullback (D.map e₀)).obj X) hXjfp
  obtain ⟨hYjc, hYjq⟩ :=
    compactSpace_and_quasiSeparatedSpace_left ((Over.pullback (D.map e₀)).obj Y) hYjfp
  have : LocallyOfFinitePresentation ((Over.pullback (D.map e₀)).obj Y).hom := hYjfp.1
  have : LocallyOfFinitePresentation g.left := by
    have : LocallyOfFinitePresentation (g.left ≫ ((Over.pullback (D.map e₀)).obj Y).hom) := by
      rw [Over.w g]; exact hXjfp.1
    exact locallyOfFinitePresentation_of_comp g.left ((Over.pullback (D.map e₀)).obj Y).hom
  have hge : (Over.pullback (c.π.app j)).map g = (α.hom ≫ fiso.hom) ≫ β.inv := by
    rw [hcomm, Category.assoc, β.hom_inv_id, Category.comp_id]
  have hglim : IsIso ((Over.pullback (c.π.app j)).map g) := by rw [hge]; infer_instance
  have : IsIso ((Over.pullback (c.π.app j)).map g).left := by
    simpa only [Over.forget_map] using
      (Over.forget c.pt).map_isIso ((Over.pullback (c.π.app j)).map g)
  obtain ⟨i₂, e₂, hk⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange D c hc j
    ((Over.pullback (D.map e₀)).obj X) ((Over.pullback (D.map e₀)).obj Y) g
  have hgiso : IsIso ((Over.pullback (D.map e₂)).map g).left := hk
  refine ⟨i₂, e₂ ≫ e₀, ?_⟩
  intro P₂ b p₂ hP₂ k hkb hkp
  have hXisq : IsPullback (pullback.fst ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂))
      (pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂))
      ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂) := IsPullback.of_hasPullback _ _
  have hYisq : IsPullback (pullback.fst ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂))
      (pullback.snd ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂))
      ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂) := IsPullback.of_hasPullback _ _
  have hXitot : IsPullback
      (pullback.fst ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂) ≫
        pullback.fst X.hom (D.map e₀))
      (pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂))
      X.hom (D.map (e₂ ≫ e₀)) := by
    rw [D.map_comp]
    exact hXisq.paste_horiz hXjsq
  have hYitot : IsPullback
      (pullback.fst ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂) ≫
        pullback.fst Y.hom (D.map e₀) ≫ πY)
      (pullback.snd ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂))
      q (D.map (e₂ ≫ e₀) ≫ D.map j₁) := by
    rw [D.map_comp, Category.assoc]
    exact hYisq.paste_horiz hjsq
  have hgw : ((Over.pullback (D.map e₂)).map g).left ≫
      ((Over.pullback (D.map e₂)).obj ((Over.pullback (D.map e₀)).obj Y)).hom
      = ((Over.pullback (D.map e₂)).obj ((Over.pullback (D.map e₀)).obj X)).hom :=
    Over.w ((Over.pullback (D.map e₂)).map g)
  have hhisq : IsPullback
      (((Over.pullback (D.map e₂)).map g).left ≫
        pullback.fst ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂) ≫
        pullback.fst Y.hom (D.map e₀) ≫ πY)
      (pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂))
      q (D.map (e₂ ≫ e₀) ≫ D.map j₁) := by
    have hsq : IsPullback (((Over.pullback (D.map e₂)).map g).left)
        (pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂))
        (pullback.snd ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂))
        (𝟙 (D.obj i₂)) :=
      IsPullback.of_horiz_isIso (CommSq.mk (by rw [Category.comp_id]; exact hgw))
    simpa only [Category.id_comp] using hsq.paste_horiz hYitot
  have hitrans : ((Over.pullback (D.map e₂)).map g).left ≫
      pullback.fst ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂) ≫
        pullback.fst Y.hom (D.map e₀) ≫ πY
      = pullback.fst ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂) ≫
        g.left ≫ pullback.fst Y.hom (D.map e₀) ≫ πY := by
    rw [overPullback_map_left_fst_assoc]
  have hlc : kj ≫ ((Over.pullback (D.map e₀)).obj X).hom
      = (plim ≫ c.π.app i₂) ≫ D.map e₂ := by
    change kj ≫ pullback.snd X.hom (D.map e₀) = (plim ≫ c.π.app i₂) ≫ D.map e₂
    rw [hkjsnd, Category.assoc, c.w e₂]
  obtain ⟨ki, hkifst, hkisnd⟩ :
      ∃ ki : Plim ⟶ pullback ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂),
        ki ≫ pullback.fst ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂) = kj ∧
          ki ≫ pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂)
            = plim ≫ c.π.app i₂ :=
    ⟨hXisq.lift kj (plim ≫ c.π.app i₂) hlc, hXisq.lift_fst _ _ _, hXisq.lift_snd _ _ _⟩
  obtain ⟨χ, hχfst, hχsnd⟩ : ∃ χ : P₂ ≅ pullback ((Over.pullback (D.map e₀)).obj X).hom
        (D.map e₂),
      χ.hom ≫ (pullback.fst ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂) ≫
          pullback.fst X.hom (D.map e₀)) = b ∧
        χ.hom ≫ pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂) = p₂ :=
    ⟨hP₂.isoIsPullback _ _ hXitot, hP₂.isoIsPullback_hom_fst _ _ hXitot,
      hP₂.isoIsPullback_hom_snd _ _ hXitot⟩
  refine ⟨χ.hom ≫ (((Over.pullback (D.map e₂)).map g).left ≫
      pullback.fst ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂) ≫
      pullback.fst Y.hom (D.map e₀) ≫ πY), ?_, ?_⟩
  · have hsq : IsPullback χ.hom p₂
        (pullback.snd ((Over.pullback (D.map e₀)).obj X).hom (D.map e₂)) (𝟙 (D.obj i₂)) :=
      IsPullback.of_horiz_isIso (CommSq.mk (by rw [Category.comp_id]; exact hχsnd))
    simpa only [Category.id_comp] using hsq.paste_horiz hhisq
  · have hkχ : k ≫ χ.hom = ki := by
      refine hXitot.hom_ext ?_ ?_
      · rw [Category.assoc, hχfst, hkb, ← Category.assoc, hkifst, hkjfst]
      · rw [Category.assoc, hχsnd, hkp, hkisnd]
    have hkey : (k ≫ χ.hom) ≫ (((Over.pullback (D.map e₂)).map g).left ≫
          pullback.fst ((Over.pullback (D.map e₀)).obj Y).hom (D.map e₂) ≫
          pullback.fst Y.hom (D.map e₀) ≫ πY) = glim := by
      rw [hkχ, hitrans, ← Category.assoc, hkifst, hkjhj]
    rwa [← Category.assoc]

include hc in
/-- **A cartesian comparison between two finitely presented objects over a cofiltered limit
descends to a stage, compatibly with itself.**

The scheme `Plim` is assumed to present both the base change of `pP : P ⟶ D.obj i₁` along
`c.π.app i₁` and the base change of `q : Zy ⟶ D.obj i` along `c.π.app i₁ ≫ D.map j₁`. The
conclusion produces a stage `i₂` over `i₁` and, for *any* base change `p₂ : P₂ ⟶ D.obj i₂` of
`pP` along `D.map e` together with the induced morphism `k` out of `Plim`, a morphism
`h : P₂ ⟶ Zy` presenting `P₂` as the base change of `q` along `D.map e ≫ D.map j₁` whose
restriction along `k` is the given comparison `glim`. -/
theorem exists_stage_isPullback_of_isPullback_limit (i₁ i : I) (j₁ : i₁ ⟶ i)
    {P Zy : Scheme.{u}} (pP : P ⟶ D.obj i₁) (q : Zy ⟶ D.obj i)
    (hpP : FinitePresentation pP) (hq : FinitePresentation q)
    {Plim : Scheme.{u}} {a : Plim ⟶ P} {plim : Plim ⟶ c.pt}
    (hP : IsPullback a plim pP (c.π.app i₁))
    {glim : Plim ⟶ Zy} (hg : IsPullback glim plim q (c.π.app i₁ ≫ D.map j₁)) :
    ∃ (i₂ : I) (e : i₂ ⟶ i₁),
      ∀ {P₂ : Scheme.{u}} {b : P₂ ⟶ P} {p₂ : P₂ ⟶ D.obj i₂}
        (_ : IsPullback b p₂ pP (D.map e)) {k : Plim ⟶ P₂}
        (_ : k ≫ b = a) (_ : k ≫ p₂ = plim ≫ c.π.app i₂),
        ∃ h : P₂ ⟶ Zy,
          IsPullback h p₂ q (D.map e ≫ D.map j₁) ∧ k ≫ h = glim :=
  exists_stage_isPullback_aux D c hc i₁ i j₁ q (Over.mk pP)
    ((Over.pullback (D.map j₁)).obj (Over.mk q)) hpP
    (LimitFPObjectDescent.finitePresentation_overPullback (D.map j₁) (Over.mk q) hq)
    (pullback.fst q (D.map j₁)) (IsPullback.of_hasPullback q (D.map j₁)) hP hg

end AlgebraicGeometry

end
