module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafBaseChange

/-!
# The evaluation morphisms of the sheaf of glueing-data morphisms

In a formal glueing situation write `P = homPresheaf D G` for the sheaf
`W ↦ {(w, φ : Φ(W, w) ⟶ G)}` of glueing-data morphisms into a glueing triple `G`, and
`π : P ⟶ X` for its projection. Evaluating the `U`-component of `φ` at the tautological section
gives a morphism `P ×_X U ⟶ G_U` over `U`, and likewise `P ×_X Y ⟶ G_Y` over `Y`. This module
builds these evaluation morphisms.

## Main definitions

* `AlgebraicGeometry.Space.natTransOfYoneda`: a morphism of presheaves from a family of maps on
  representable sources, natural in the source.
* `AlgebraicGeometry.Space.FormalGlueingSituation.legEval`: the evaluation of one leg.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

/-- A morphism of presheaves from a family of maps on representable sources, natural in the
source. -/
noncomputable def natTransOfYoneda {C : Type w} [Category.{v} C] {F F' : Cᵒᵖ ⥤ Type v}
    (Ψ : ∀ W : C, (yoneda.obj W ⟶ F) → (yoneda.obj W ⟶ F'))
    (hΨ : ∀ {W W' : C} (g : W' ⟶ W) (x : yoneda.obj W ⟶ F),
      Ψ W' (yoneda.map g ≫ x) = yoneda.map g ≫ Ψ W x) : F ⟶ F' where
  app W := ↾fun x => yonedaEquiv (Ψ W.unop (yonedaEquiv.symm x))
  naturality W W' g := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    change yonedaEquiv (Ψ W'.unop (yonedaEquiv.symm (F.map g x))) =
      F'.map g (yonedaEquiv (Ψ W.unop (yonedaEquiv.symm x)))
    rw [yonedaEquiv_naturality', ← hΨ, yonedaEquiv_symm_naturality_left]
    rfl

/-- Precomposing `natTransOfYoneda Ψ hΨ` with a map `x` from a representable gives `Ψ W x`. -/
theorem comp_natTransOfYoneda {C : Type w} [Category.{v} C] {F F' : Cᵒᵖ ⥤ Type v}
    (Ψ : ∀ W : C, (yoneda.obj W ⟶ F) → (yoneda.obj W ⟶ F'))
    (hΨ : ∀ {W W' : C} (g : W' ⟶ W) (x : yoneda.obj W ⟶ F),
      Ψ W' (yoneda.map g ≫ x) = yoneda.map g ≫ Ψ W x) {W : C} (x : yoneda.obj W ⟶ F) :
    x ≫ natTransOfYoneda Ψ hΨ = Ψ W x := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  show yonedaEquiv (Ψ W (yonedaEquiv.symm (yonedaEquiv x))) = _
  rw [Equiv.symm_apply_apply]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {D : FormalGlueingSituation B S hS} {G : glueingData D}

/-- The first component of the pair underlying a section `s` of `homPresheaf D G` corresponds,
under the Yoneda equivalence, to the image of `s` under the projection to `X`. -/
theorem homPresheaf_symm_fst {W : BigFppfOver B S hS} (s : (homPresheaf D G).obj (op W)) :
    ((equivShrink (glueSections D G W)).symm s).1 =
      yonedaEquiv.symm ((homPresheafProjection D G).app (op W) s) := by
  show _ = yonedaEquiv.symm (yonedaEquiv ((equivShrink _).symm s).1)
  rw [Equiv.symm_apply_apply]

/-- The pair underlying the restriction of a section of `homPresheaf D G` along `g` is the
restriction along `g` of the pair underlying the section. -/
theorem homPresheaf_symm_map {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (s : (homPresheaf D G).obj (op W)) :
    (equivShrink (glueSections D G W')).symm ((homPresheaf D G).map g.op s) =
      ((equivShrink (glueSections D G W)).symm s).restrict g := by
  show (equivShrink _).symm (equivShrink _ _) = _
  rw [Equiv.symm_apply_apply]
  rfl

variable {J : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : J ⟶ D.X) (M : Over J)
  (leg : ∀ A : Over D.X, ((restrictionDiagram D).obj A ⟶ G.obj) →
    ((Over.pullback j).obj A ⟶ M))

/-- The value of one leg of a pair at the tautological section. -/
noncomputable def legEval₀ {W : BigFppfOver B S hS} (t : glueSections D G W)
    (b : yoneda.obj W ⟶ J) (h : t.1 = b ≫ j) : yoneda.obj W ⟶ M.left :=
  pullback.lift (f := (Over.mk t.1).hom) (g := j) (𝟙 _) b
    (by rw [Category.id_comp]; exact h) ≫
    (leg _ t.2).left

/-- `legEval₀` commutes with restriction along a morphism `g : W' ⟶ W`. -/
theorem legEval₀_restrict
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)
    {W W' : BigFppfOver B S hS} (g : W' ⟶ W) (t : glueSections D G W)
    (b : yoneda.obj W ⟶ J) (h : t.1 = b ≫ j) (t' : glueSections D G W') (ht' : t' = t.restrict g)
    (h' : t'.1 = (yoneda.map g ≫ b) ≫ j) :
    legEval₀ j M leg t' (yoneda.map g ≫ b) h' = yoneda.map g ≫ legEval₀ j M leg t b h := by
  subst ht'
  obtain ⟨w, φ⟩ := t
  dsimp only [legEval₀, glueSections.restrict] at h h' ⊢
  rw [hleg, Over.comp_left, ← Category.assoc, ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, overPullback_map_left_comp_fst, ← Category.assoc, pullback.lift_fst,
      Category.assoc, pullback.lift_fst]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rw [Category.assoc, overPullback_map_left_comp_snd, pullback.lift_snd, Category.assoc,
      pullback.lift_snd]

/-- For a section `x` of `P ×_X J`, the first component of the pair underlying its `P`-component is
its `J`-component followed by `j`. -/
theorem symm_yonedaEquiv_fst {W : BigFppfOver B S hS}
    (x : yoneda.obj W ⟶ pullback (homPresheafProjection D G) j) :
    ((equivShrink (glueSections D G W)).symm
      (yonedaEquiv (x ≫ pullback.fst (homPresheafProjection D G) j))).1 =
        (x ≫ pullback.snd (homPresheafProjection D G) j) ≫ j := by
  rw [homPresheaf_symm_fst, ← yonedaEquiv_comp, Equiv.symm_apply_apply, Category.assoc,
    pullback.condition, Category.assoc]

/-- The evaluation of a leg on a section of `P ×_X J`. -/
noncomputable def legEvalYoneda {W : BigFppfOver B S hS}
    (x : yoneda.obj W ⟶ pullback (homPresheafProjection D G) j) : yoneda.obj W ⟶ M.left :=
  legEval₀ j M leg ((equivShrink (glueSections D G W)).symm
      (yonedaEquiv (x ≫ pullback.fst (homPresheafProjection D G) j)))
    (x ≫ pullback.snd (homPresheafProjection D G) j) (symm_yonedaEquiv_fst j x)

/-- `legEvalYoneda` is natural in the representable source. -/
theorem legEvalYoneda_naturality
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)
    {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (x : yoneda.obj W ⟶ pullback (homPresheafProjection D G) j) :
    legEvalYoneda j M leg (yoneda.map g ≫ x) = yoneda.map g ≫ legEvalYoneda j M leg x := by
  have key := legEval₀_restrict j M leg hleg g
    ((equivShrink (glueSections D G W)).symm
      (yonedaEquiv (x ≫ pullback.fst (homPresheafProjection D G) j)))
    (x ≫ pullback.snd (homPresheafProjection D G) j) (symm_yonedaEquiv_fst j x)
    ((equivShrink (glueSections D G W')).symm
      (yonedaEquiv ((yoneda.map g ≫ x) ≫ pullback.fst (homPresheafProjection D G) j)))
    (by rw [Category.assoc, ← yonedaEquiv_naturality, homPresheaf_symm_map])
    (by rw [symm_yonedaEquiv_fst]; simp only [Category.assoc])
  refine Eq.trans ?_ key
  dsimp only [legEvalYoneda]
  congr 1

/-- **The evaluation of one leg**: the morphism `P ×_X J ⟶ M` sending `((w, φ), b)` to the
value of the `J`-component of `φ` at the section `(id, b)`. -/
noncomputable def legEval
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ) :
    pullback (homPresheafProjection D G) j ⟶ M.left :=
  natTransOfYoneda (fun _ x => legEvalYoneda j M leg x)
    (by intro W W' g x; exact legEvalYoneda_naturality j M leg hleg g x)

/-- Precomposing `legEval` with a section `x` of `P ×_X J` gives `legEvalYoneda` of `x`. -/
theorem comp_legEval
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)
    {W : BigFppfOver B S hS} (x : yoneda.obj W ⟶ pullback (homPresheafProjection D G) j) :
    x ≫ legEval j M leg hleg = legEvalYoneda j M leg x :=
  comp_natTransOfYoneda (fun _ x => legEvalYoneda j M leg x)
    (by intro W W' g x; exact legEvalYoneda_naturality j M leg hleg g x) x

/-- `legEval` is a morphism over `J`: its composite with `M.hom` is the second projection
of `P ×_X J`. -/
theorem legEval_hom
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ) :
    legEval j M leg hleg ≫ M.hom = pullback.snd (homPresheafProjection D G) j := by
  refine hom_ext_yoneda fun W x => ?_
  rw [← Category.assoc, comp_legEval]
  dsimp only [legEvalYoneda, legEval₀]
  rw [Category.assoc, Over.w]
  exact pullback.lift_snd _ _ _

/-- `legEvalYoneda` computed from any description of the pair underlying a section. -/
theorem legEvalYoneda_eq {W : BigFppfOver B S hS}
    (x : yoneda.obj W ⟶ pullback (homPresheafProjection D G) j) (t : glueSections D G W)
    (ht : (equivShrink (glueSections D G W)).symm
      (yonedaEquiv (x ≫ pullback.fst (homPresheafProjection D G) j)) = t)
    (h : t.1 = (x ≫ pullback.snd (homPresheafProjection D G) j) ≫ j) :
    legEvalYoneda j M leg x = legEval₀ j M leg t _ h := by
  subst ht
  rfl

/-- `legEval₀` on the pair attached to a section `t` of a space `A₀` over `X` and a morphism
`θ₀ : Φ(A₀) ⟶ G`. -/
theorem legEval₀_ofSpace
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)
    {A₀ : Over D.X} (θ₀ : (restrictionDiagram D).obj A₀ ⟶ G.obj) {W : BigFppfOver B S hS}
    (t : yoneda.obj W ⟶ A₀.left) (b : yoneda.obj W ⟶ J) (h : t ≫ A₀.hom = b ≫ j) :
    legEval₀ j M leg ⟨t ≫ A₀.hom, (restrictionDiagram D).map
        (Over.homMk t rfl : Over.mk (t ≫ A₀.hom) ⟶ A₀) ≫ θ₀⟩ b h =
      pullback.lift t b h ≫ (leg A₀ θ₀).left := by
  dsimp only [legEval₀]
  rw [hleg, Over.comp_left, ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, overPullback_map_left_comp_fst, ← Category.assoc, pullback.lift_fst]
    exact (Category.id_comp _).trans (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, overPullback_map_left_comp_snd, pullback.lift_snd, pullback.lift_snd]

/-- The canonical morphism `T ⟶ P` attached to `θ : F(T) ⟶ G`, base changed to `J`. -/
noncomputable def toHomPresheafPullback (T : spacesOverX D)
    (θ : (formalGlueingFunctor D).1.obj T ⟶ G) :
    pullback T.obj.hom j ⟶ pullback (homPresheafProjection D G) j :=
  pullback.lift (pullback.fst T.obj.hom j ≫ toHomPresheaf D T ≫ homPresheafMap D θ)
    (pullback.snd T.obj.hom j) (by
      have h1 : toHomPresheaf D T ≫ homPresheafMap D θ ≫ homPresheafProjection D G =
          T.obj.hom := by
        rw [homPresheafMap_projection, toHomPresheaf_projection]
      rw [Category.assoc, Category.assoc, h1, pullback.condition])

/-- **The evaluation inverts the canonical morphism from a realized triple.** For a space `T`
over `X` and a morphism `θ : F(T) ⟶ G`, evaluating the pair attached to a section of `T` gives
back the corresponding component of `θ`. -/
theorem legEval_toHomPresheaf
    (hleg : ∀ {A A' : Over D.X} (h : A ⟶ A') (φ : (restrictionDiagram D).obj A' ⟶ G.obj),
      leg A ((restrictionDiagram D).map h ≫ φ) = (Over.pullback j).map h ≫ leg A' φ)
    (T : spacesOverX D) (θ : (formalGlueingFunctor D).1.obj T ⟶ G) :
    toHomPresheafPullback j T θ ≫ legEval j M leg hleg = (leg T.obj θ.hom).left := by
  refine hom_ext_yoneda fun W z => ?_
  rw [← Category.assoc, comp_legEval]
  have hsec : (equivShrink (glueSections D G W)).symm (yonedaEquiv ((z ≫
      toHomPresheafPullback j T θ) ≫ pullback.fst (homPresheafProjection D G) j)) =
      (glueSectionsOfSpace D T (z ≫ pullback.fst T.obj.hom j)).postcomp D θ := by
    have e1 : (z ≫ toHomPresheafPullback j T θ) ≫ pullback.fst (homPresheafProjection D G) j =
        (z ≫ pullback.fst T.obj.hom j) ≫ toHomPresheaf D T ≫ homPresheafMap D θ := by
      rw [Category.assoc, toHomPresheafPullback, pullback.lift_fst, Category.assoc]
    rw [e1]
    show (equivShrink _).symm (equivShrink _ (((equivShrink _).symm (equivShrink _
      (glueSectionsOfSpace D T (yonedaEquiv.symm (yonedaEquiv
        (z ≫ pullback.fst T.obj.hom j)))))).postcomp D θ)) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [legEvalYoneda_eq j M leg _ _ hsec (by
    show (z ≫ pullback.fst T.obj.hom j) ≫ T.obj.hom = _
    simp only [toHomPresheafPullback, Category.assoc, pullback.lift_snd_assoc,
      pullback.condition])]
  refine (legEval₀_ofSpace j M leg hleg (A₀ := T.obj) θ.hom (z ≫ pullback.fst T.obj.hom j)
    _ _).trans ?_
  congr 1
  refine pullback.hom_ext ?_ ?_
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans ((Category.assoc _ _ _).trans
      (congrArg (z ≫ ·) (pullback.lift_snd _ _ _)))

end AlgebraicGeometry.Space.FormalGlueingSituation

end
