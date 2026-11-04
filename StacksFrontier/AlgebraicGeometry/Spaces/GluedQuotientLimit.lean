module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedQuotientKernelPairLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximationFromPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafPresentationUniqueness

/-!
# The limit of the glued quotients is the space they approximate

Let `f : V ⟶ X` be an étale chart of an fppf sheaf `X` which is an isomorphism off an open
subspace `U ⊆ X` with inverse image `W ⊆ V` (an `AlgebraicGeometry.Space.ElementaryChart`), and
let `(V_i ⊇ W_i ⟶ U_i)` be a directed system of stages for it, with the extended relations
`R_i = V_i ⊔_{W_i} (W_i ×_{U_i} W_i)` and their quotients `X_i = V_i/R_i`
(`AlgebraicGeometry.Space.OpenKernelPairExtension.quotient`). Suppose the transition morphisms
of the `V_i` compose, are affine, and exhibit `V` as their limit. This file proves, in the order
of the proof of absolute Noetherian approximation, Stacks 07SU:

* the `X_i` form an inverse system,
  `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem.diagram`, and `V` maps to its limit `L`
  (step (a));
* the square formed by `V ⟶ L`, `V ⟶ V_{i₀}`, `L ⟶ X_{i₀}` and `V_{i₀} ⟶ X_{i₀}` is cartesian,
  so `V ⟶ L` is surjective and étale (step (b): the limit of a cartesian natural transformation
  is cartesian);
* the kernel pair of `V ⟶ L` is the kernel pair `R = V ×_X V` of `f` (step (c), from
  `AlgebraicGeometry.Space.ElementaryChart.StageMap.exists_lift_of_eq` and
  `AlgebraicGeometry.Space.ElementaryChart.StageSystem.eq_of_forall_exists_lift`), so that `X ≅ L`
  by the uniqueness of the target of a common presentation (Stacks 0262);
* hence `X` is the limit of the `X_i`, and has a Noetherian approximation as soon as the `X_i`
  are quasi-separated and of finite type over `Spec ℤ`.

Nothing here uses Stacks 07SF: the limit `L` is a limit of presheaves, which always exists, and
it is identified with `X` directly, so no size condition on the index set enters.

## Main definitions

* `CategoryTheory.Limits.isPullback_of_yoneda_lifts`: a commutative square of presheaves is
  cartesian when it has unique lifts against representable presheaves.
* `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem`: a stage system whose ambient
  transition morphisms compose, are affine, and have `V` as limit.
* `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem.diagram` and
  `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem.πV`.

## Main results

* `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem.isPullback_πV`: step (b).
* `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem.isPullback_kernelPair`: step (c).
* `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem.exists_iso_limit`: `X ≅ lim X_i`.
* `AlgebraicGeometry.Space.ElementaryChart.LimitStageSystem.hasNoetherianApproximation`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe v u

namespace CategoryTheory.Limits

/-- **A commutative square of presheaves is cartesian when it has unique lifts against
representable presheaves.** Limits of presheaves are computed objectwise, and an element of a
presheaf at `Y` is a morphism from the presheaf represented by `Y`. -/
theorem isPullback_of_yoneda_lifts {C : Type*} [Category.{v} C] {P Q R T : Cᵒᵖ ⥤ Type v}
    {t : P ⟶ Q} {l : P ⟶ R} {r : Q ⟶ T} {b : R ⟶ T} (w : t ≫ r = l ≫ b)
    (huniq : ∀ (Y : C) (x y : yoneda.obj Y ⟶ P), x ≫ t = y ≫ t → x ≫ l = y ≫ l → x = y)
    (hex : ∀ (Y : C) (a : yoneda.obj Y ⟶ Q) (c : yoneda.obj Y ⟶ R), a ≫ r = c ≫ b →
      ∃ x : yoneda.obj Y ⟶ P, x ≫ t = a ∧ x ≫ l = c) :
    IsPullback t l r b := by
  refine ⟨⟨w⟩, ⟨evaluationJointlyReflectsLimits _ fun Y ↦ ?_⟩⟩
  have hY : IsPullback (t.app Y) (l.app Y) (r.app Y) (b.app Y) := by
    rw [Types.isPullback_iff]
    refine ⟨by rw [← NatTrans.comp_app, w, NatTrans.comp_app], fun x y ⟨h₁, h₂⟩ ↦ ?_,
      fun a c h ↦ ?_⟩
    · have := huniq Y.unop (yonedaEquiv.symm x) (yonedaEquiv.symm y)
        (yonedaEquiv.injective (by simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h₁))
        (yonedaEquiv.injective (by simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h₂))
      simpa using congrArg yonedaEquiv this
    · obtain ⟨x, hx₁, hx₂⟩ := hex Y.unop (yonedaEquiv.symm a) (yonedaEquiv.symm c)
        (yonedaEquiv.injective (by simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h))
      refine ⟨yonedaEquiv x, ?_, ?_⟩
      · simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using congrArg yonedaEquiv hx₁
      · simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using congrArg yonedaEquiv hx₂
  exact (isLimitMapConePullbackConeEquiv _ _).symm hY.isLimit

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "F" => BigFppfOver.toScheme B S hS

attribute [local instance] hasSheafify_bigFppfOver

namespace OpenKernelPairExtension

variable {X X' X'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W V' W' V'' W'' : BigFppfOver B S hS}

/-- The quotient of an extended relation is an fppf sheaf. -/
theorem isSheaf_quotient (E : OpenKernelPairExtension B S hS X V W) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) E.quotient :=
  (quotientSheaf (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (relation B S hS E.s E.t)).property

namespace Transition

variable {E : OpenKernelPairExtension B S hS X V W} {E' : OpenKernelPairExtension B S hS X' V' W'}
  {E'' : OpenKernelPairExtension B S hS X'' V'' W''}

/-- A transition of an extended relation to itself over the identity of `V` induces the identity
of the quotient. -/
theorem φ_eq_id (T : Transition E E) (h : T.v = 𝟙 V) : T.φ = 𝟙 _ := by
  have e := quotientSheafMap_eq_of_obj_eq (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) (relation B S hS E.s E.t) (relation B S hS E.s E.t)
    ((Over.post (X := B.obj hS) B.inclusion).map T.r) (𝟙 _)
    ((Over.post (X := B.obj hS) B.inclusion).map T.v) (𝟙 _) T.post_r_source T.post_r_target
    (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.id_comp, Category.comp_id])
    (by rw [h, CategoryTheory.Functor.map_id])
  unfold φ
  rw [e, quotientSheafMap_id]
  rfl

/-- The morphisms of quotients induced by transitions compose along composable transitions of
the ambient objects. -/
theorem φ_comp (T₁ : Transition E E') (T₂ : Transition E' E'') (T₃ : Transition E E'')
    (h : T₁.v ≫ T₂.v = T₃.v) : T₁.φ ≫ T₂.φ = T₃.φ := by
  unfold φ
  show (quotientSheafMap _ _ _ _ _ _ _ _ ≫ quotientSheafMap _ _ _ _ _ _ _ _).hom = _
  rw [quotientSheafMap_comp]
  exact congrArg InducedCategory.Hom.hom (quotientSheafMap_eq_of_obj_eq _ _ _ _ _ _ _ _ _ _ _ _
    (by rw [← Functor.map_comp, h]))

end Transition

end OpenKernelPairExtension

namespace ElementaryChart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}

/-- **A stage system with `V` as the limit of its ambient objects.** A stage system
(`AlgebraicGeometry.Space.ElementaryChart.StageSystem`) whose transition morphisms of the
ambient objects `V_i` are the identity at `i ≤ i`, compose, are affine morphisms of schemes, and
exhibit `V` as their limit: compatible morphisms to the `V_i` beyond any given stage come from a
morphism to `V`. -/
structure LimitStageSystem (C : ElementaryChart X V) (I : Type u) [Preorder I] extends
    C.StageSystem I where
  v_refl : ∀ i, (T (le_refl i)).v = 𝟙 _
  v_trans : ∀ {i i' i'' : I} (h : i ≤ i') (h' : i' ≤ i''),
    (T h').v ≫ (T h).v = (T (h.trans h')).v
  isAffineHom_v : ∀ {i i' : I} (h : i ≤ i'), _root_.AlgebraicGeometry.IsAffineHom ((F).map (T h).v)
  lift_V : ∀ (i₀ : I) {Y : BigFppfOver B S hS} (x : ∀ i, i₀ ≤ i → (Y ⟶ Vi i)),
    (∀ i i' (hi : i₀ ≤ i) (hi' : i₀ ≤ i') (h : i ≤ i'), x i' hi' ≫ (T h).v = x i hi) →
    ∃ y : Y ⟶ V, ∀ i (hi : i₀ ≤ i), y ≫ (M i).v = x i hi

namespace LimitStageSystem

variable {C : ElementaryChart X V} {I : Type u} [Preorder I] (D : C.LimitStageSystem I)

/-- **Step (a) of Stacks 07SU.** The quotients `X_i = V_i/R_i` form an inverse system. -/
noncomputable def diagram : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj i := (D.E i.unop).quotient
  map f := (D.T (leOfHom f.unop)).φ
  map_id i := OpenKernelPairExtension.Transition.φ_eq_id _ (D.v_refl i.unop)
  map_comp f g := (OpenKernelPairExtension.Transition.φ_comp _ _ _
    (D.v_trans (leOfHom g.unop) (leOfHom f.unop))).symm

/-- The chart `V_i ⟶ X_i`, with target the stage of the system of quotients. -/
noncomputable def stageπ (i : I) : yoneda.obj (D.Vi i) ⟶ D.diagram.obj (op i) := (D.E i).π

/-- The transition morphism `X_{i'} ⟶ X_i` of the system of quotients, for `i ≤ i'`. -/
noncomputable def stageφ {i i' : I} (h : i ≤ i') : D.diagram.obj (op i') ⟶ D.diagram.obj (op i) :=
  D.diagram.map (homOfLE h).op

/-- For `i ≤ i'`, the square formed by the charts `V_{i'} ⟶ X_{i'}` and `V_i ⟶ X_i`, the
transition `V_{i'} ⟶ V_i` and the transition `X_{i'} ⟶ X_i` is cartesian. -/
theorem isPullback_stageπ {i i' : I} (h : i ≤ i') :
    IsPullback (D.stageπ i') (yoneda.map (D.T h).v) (D.stageφ h) (D.stageπ i) :=
  (D.T h).isPullback_π_φ

/-- For `i ≤ i'`, the charts commute with the transition morphisms: `V_{i'} ⟶ X_{i'} ⟶ X_i`
equals `V_{i'} ⟶ V_i ⟶ X_i`. -/
theorem stageπ_stageφ {i i' : I} (h : i ≤ i') :
    D.stageπ i' ≫ D.stageφ h = yoneda.map (D.T h).v ≫ D.stageπ i :=
  (D.isPullback_stageπ h).w

/-- The relation `R_i` with its target and source maps is the kernel pair of the chart
`V_i ⟶ X_i`. -/
theorem isPullback_kernelPair_stageπ (i : I) :
    IsPullback (yoneda.map (D.E i).t) (yoneda.map (D.E i).s) (D.stageπ i) (D.stageπ i) :=
  (D.E i).isPullback_π

/-- The cone over the system of quotients with vertex `V`. -/
noncomputable def coneπ : (Functor.const Iᵒᵖ).obj (yoneda.obj V) ⟶ D.diagram where
  app i := yoneda.map (D.M i.unop).v ≫ D.stageπ i.unop
  naturality i j f := by
    change 𝟙 _ ≫ yoneda.map (D.M j.unop).v ≫ D.stageπ j.unop =
      (yoneda.map (D.M i.unop).v ≫ D.stageπ i.unop) ≫ D.stageφ (leOfHom f.unop)
    rw [Category.id_comp, Category.assoc, stageπ_stageφ, ← Category.assoc, ← Functor.map_comp,
      D.comm_v]

/-- The morphism `V ⟶ lim X_i`. -/
noncomputable def πV : yoneda.obj V ⟶ limit D.diagram :=
  limit.lift D.diagram ⟨yoneda.obj V, D.coneπ⟩

/-- The composite of `V ⟶ lim X_i` with the projection to `X_i` is `V ⟶ V_i ⟶ X_i`. -/
@[reassoc (attr := simp)]
theorem πV_π (i : I) :
    D.πV ≫ limit.π D.diagram (op i) = yoneda.map (D.M i).v ≫ D.stageπ i :=
  limit.lift_π _ _

/-- For `i ≤ i'`, the projection `lim X_i ⟶ X_{i'}` followed by the transition `X_{i'} ⟶ X_i`
is the projection `lim X_i ⟶ X_i`. -/
@[reassoc]
theorem limit_π_stageφ {i i' : I} (h : i ≤ i') :
    limit.π D.diagram (op i') ≫ D.stageφ h = limit.π D.diagram (op i) :=
  limit.w D.diagram (homOfLE h).op

/-- **Step (b) of Stacks 07SU: the limit of a cartesian natural transformation is cartesian.**
The square formed by `V ⟶ lim X_i`, `V ⟶ V_{i₀}`, the projection `lim X_i ⟶ X_{i₀}` and the
chart `V_{i₀} ⟶ X_{i₀}` is cartesian. -/
theorem isPullback_πV [IsDirected I (· ≤ ·)] (i₀ : I) :
    IsPullback D.πV (yoneda.map (D.M i₀).v) (limit.π D.diagram (op i₀)) (D.stageπ i₀) := by
  refine isPullback_of_yoneda_lifts (by rw [πV_π]) ?_ ?_
  · intro Y x y h₁ h₂
    obtain ⟨x, rfl⟩ := yoneda.map_surjective x
    obtain ⟨y, rfl⟩ := yoneda.map_surjective y
    congr 1
    refine D.hom_ext_V i₀ _ _ fun i hi ↦ yoneda.map_injective ?_
    refine (D.isPullback_stageπ hi).hom_ext ?_ ?_
    · simpa only [Category.assoc, πV_π, Functor.map_comp] using
        congrArg (· ≫ limit.π D.diagram (op i)) h₁
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc, D.comm_v,
        Functor.map_comp, Functor.map_comp, h₂]
  · intro Y a c h
    obtain ⟨c, rfl⟩ := yoneda.map_surjective c
    have hl (i : I) (hi : i₀ ≤ i) :
        (a ≫ limit.π D.diagram (op i)) ≫ D.stageφ hi = yoneda.map c ≫ D.stageπ i₀ := by
      rw [Category.assoc, D.limit_π_stageφ hi, h]
    let y (i : I) (hi : i₀ ≤ i) : Y ⟶ D.Vi i :=
      Yoneda.fullyFaithful.preimage ((D.isPullback_stageπ hi).lift _ _ (hl i hi))
    have hy₁ (i : I) (hi : i₀ ≤ i) :
        yoneda.map (y i hi) ≫ D.stageπ i = a ≫ limit.π D.diagram (op i) := by
      simp only [y, Functor.FullyFaithful.map_preimage, IsPullback.lift_fst]
    have hy₂ (i : I) (hi : i₀ ≤ i) : yoneda.map (y i hi ≫ (D.T hi).v) = yoneda.map c := by
      simp only [y, Functor.map_comp, Functor.FullyFaithful.map_preimage, IsPullback.lift_snd]
    obtain ⟨z, hz⟩ := D.lift_V i₀ y fun i i' hi hi' h ↦ yoneda.map_injective (by
      refine (D.isPullback_stageπ hi).hom_ext ?_ ?_
      · rw [Functor.map_comp, Category.assoc, ← stageπ_stageφ, ← Category.assoc, hy₁,
          Category.assoc, D.limit_π_stageφ, hy₁]
      · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, D.v_trans, hy₂, hy₂])
    refine ⟨yoneda.map z, ?_, ?_⟩
    · refine limit.hom_ext fun j ↦ ?_
      obtain ⟨k, hjk, hk⟩ := directed_of (· ≤ ·) j.unop i₀
      show (yoneda.map z ≫ D.πV) ≫ limit.π D.diagram (op j.unop) = _
      rw [Category.assoc, πV_π, ← D.comm_v hjk, Functor.map_comp, Category.assoc,
        ← stageπ_stageφ, ← Category.assoc, ← Functor.map_comp, hz k hk, ← Category.assoc, hy₁,
        Category.assoc, D.limit_π_stageφ]
    · rw [← Functor.map_comp, hz i₀ le_rfl]
      simpa only [D.v_refl, Category.comp_id] using hy₂ i₀ le_rfl

/-- A property of the charts `V_i ⟶ X_i` stable under base change passes to `V ⟶ lim X_i`. -/
private theorem presheaf_πV_of_π [Nonempty I] [IsDirected I (· ≤ ·)]
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (h : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage P (F))) (D.E i).π) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P (F))) D.πV := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage P (F))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.of_isPullback (D.isPullback_πV i₀).flip (h i₀)

/-- For a nonempty directed index set, the morphism `V ⟶ lim X_i` is surjective. -/
theorem πV_surjective [Nonempty I] [IsDirected I (· ≤ ·)] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) D.πV :=
  D.presheaf_πV_of_π _ fun i ↦ (D.E i).π_surjective

/-- For a nonempty directed index set, the morphism `V ⟶ lim X_i` is étale. -/
theorem πV_etale [Nonempty I] [IsDirected I (· ≤ ·)] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (F))) D.πV :=
  D.presheaf_πV_of_π _ fun i ↦ (D.E i).π_etale

/-- **Step (c) of Stacks 07SU.** The kernel pair of `V ⟶ lim X_i` is the kernel pair
`R = V ×_X V` of the chart `f : V ⟶ X`. -/
theorem isPullback_kernelPair [Nonempty I] [IsDirected I (· ≤ ·)]
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    IsPullback (yoneda.map C.s) (yoneda.map C.t) D.πV D.πV := by
  refine isPullback_of_yoneda_lifts ?_ ?_ ?_
  · refine limit.hom_ext fun j ↦ ?_
    obtain ⟨ρ, hρt, hρs⟩ := (D.M j.unop).exists_lift_of_eq C.s C.t C.isPullback.w
    show (yoneda.map C.s ≫ D.πV) ≫ limit.π D.diagram (op j.unop) =
      (yoneda.map C.t ≫ D.πV) ≫ limit.π D.diagram (op j.unop)
    rw [Category.assoc, Category.assoc, πV_π, ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, ← hρt, ← hρs, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, (D.isPullback_kernelPair_stageπ j.unop).w]
  · intro Y x y h₁ h₂
    obtain ⟨x, rfl⟩ := yoneda.map_surjective x
    obtain ⟨y, rfl⟩ := yoneda.map_surjective y
    congr 1
    exact kernelPair_hom_ext B S hS C.isPullback x y
      (yoneda.map_injective (by simpa only [Functor.map_comp] using h₁))
      (yoneda.map_injective (by simpa only [Functor.map_comp] using h₂))
  · intro Y a c h
    obtain ⟨a, rfl⟩ := yoneda.map_surjective a
    obtain ⟨c, rfl⟩ := yoneda.map_surjective c
    have H (i : I) : ∃ ρ : Y ⟶ (D.E i).R, ρ ≫ (D.E i).t = a ≫ (D.M i).v ∧
        ρ ≫ (D.E i).s = c ≫ (D.M i).v := by
      have hi : yoneda.map (a ≫ (D.M i).v) ≫ D.stageπ i =
          yoneda.map (c ≫ (D.M i).v) ≫ D.stageπ i := by
        simpa only [Category.assoc, πV_π, Functor.map_comp] using
          congrArg (· ≫ limit.π D.diagram (op i)) h
      let ρ := Yoneda.fullyFaithful.preimage ((D.isPullback_kernelPair_stageπ i).lift _ _ hi)
      refine ⟨ρ, yoneda.map_injective ?_, yoneda.map_injective ?_⟩ <;>
        simp only [ρ, Functor.map_comp, Functor.FullyFaithful.map_preimage, IsPullback.lift_fst,
          IsPullback.lift_snd]
    exact ⟨yoneda.map
      (kernelPairLift B S hS C.isPullback a c (D.eq_of_forall_exists_lift hX a c H)),
      by rw [← Functor.map_comp, kernelPairLift_fst],
      by rw [← Functor.map_comp, kernelPairLift_snd]⟩

/-- **The end of the proof of Stacks 07SU: `X ≅ lim X_i`.** For a surjective chart `f`, the
fppf sheaf `X` is isomorphic to the limit of the quotients `X_i = V_i/R_i`, compatibly with `f`
and `V ⟶ lim X_i`. -/
theorem exists_iso_limit [Nonempty I] [IsDirected I (· ≤ ·)]
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f) :
    ∃ e : X ≅ limit D.diagram, C.f ≫ e.hom = D.πV :=
  exists_iso_of_common_presentation_of_isSheaf B S hS C.isPullback (D.isPullback_kernelPair hX)
    hX (isSheaf_limit B S hS D.diagram fun i ↦ (D.E i.unop).isSheaf_quotient) hsurj C.etale_f
    D.πV_surjective D.πV_etale

/-- **The conclusion of Stacks 07SU from a limit stage system.** If the chart `f` is surjective
and every quotient `X_i = V_i/R_i` is quasi-separated and of finite type over `Spec ℤ`, then `X`
has a Noetherian approximation, by the system of the `X_i`. -/
theorem hasNoetherianApproximation [Nonempty I] [IsDirected I (· ≤ ·)]
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (F))) C.f)
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.E i).quotient)
    (hft : ∀ i, IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B S hS hZ (D.E i).quotient))) :
    HasNoetherianApproximation B S hS hZ X := by
  obtain ⟨e, -⟩ := D.exists_iso_limit hX hsurj
  refine ⟨(noetherianApproximationLimit B S hS hZ D.diagram
    (fun j ↦ (D.E j.unop).isAlgebraicSpace_quotient) (fun {j j'} g ↦ ?_)
    (fun j ↦ hqs j.unop) (fun j ↦ hft j.unop)).ofIso e.symm⟩
  have := D.isAffineHom_v (leOfHom g.unop)
  exact (D.T (leOfHom g.unop)).isAffineHom_φ

end LimitStageSystem

end ElementaryChart

end AlgebraicGeometry.Space

end
