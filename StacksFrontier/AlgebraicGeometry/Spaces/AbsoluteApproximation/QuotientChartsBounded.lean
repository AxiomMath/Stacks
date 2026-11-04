module

public import StacksFrontier.AlgebraicGeometry.Limits.SmallIndexCountableStages
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientChartLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded

/-!
# The charts of a small system of étale quotients of finite type are bounded

Let `E` be an inverse system of étale equivalence relations `(V_j, R_j)` on objects of the big
fppf site with cartesian source squares and affine transition morphisms
(`AlgebraicGeometry.Space.EtaleRelationSystem`), indexed by the opposite of a directed set `I`.
If every `V_j` is locally of finite type over `Spec ℤ` and `I` is smaller than the size cutoff of
the site, then the system of quotients `V_j / R_j` has bounded charts in the sense of
`AlgebraicGeometry.Space.ChartsBounded`: the base changes of an affine scheme-valued point of a
stage along the transition morphisms into that stage are bounded by one cardinal below the
cutoff.

This is what lets the limit theory of algebraic spaces in this development (Stacks 07SL,
Stacks 07SQ) run on the systems built in the proof of Stacks 07SU, once their index set has been
made small (`AlgebraicGeometry.exists_small_isLimit_whisker_of_countable`).

## Main results

* `AlgebraicGeometry.Space.EtaleRelationSystem.exists_isPullback_quotient_baseChange`: along the
  surjective étale chart `P = U₀ ×_{V_i/R_i} V_i` of a scheme-valued point `U₀ ⟶ V_i/R_i`, the
  base change `U₀ ×_{V_i/R_i} V_j/R_j` becomes `P ×_{V_i} V_j`.
* `AlgebraicGeometry.Space.EtaleRelationSystem.chartsBounded`: the system of quotients has
  bounded charts.

## Implementation notes

The base change `W = U₀ ×_{V_i/R_i} V_j/R_j` receives the surjective étale morphism
`P ×_{V_i} V_j ⟶ W`, and `P ×_{V_i} V_j ⟶ P` is quasi-compact and locally of finite type, being a
base change of the affine morphism `V_j ⟶ V_i` of schemes locally of finite type over `Spec ℤ`.
So the size of `W` is bounded by `2 ^ 2 ^ size(P)` (Stacks 000R), uniformly in `j`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

namespace EtaleRelationSystem

variable {J : Type u} [Category.{u} J] (E : EtaleRelationSystem B S hS J)

/-- **The base change of a stage of a system of étale quotients along the chart of a point.**
Let `q₀ : U₀ ⟶ V_i/R_i` be a scheme-valued point of a stage and `P = U₀ ×_{V_i/R_i} V_i` the
base change of the quotient map, with projections `a : P ⟶ U₀` and `b : P ⟶ V_i`. If
`W = U₀ ×_{V_i/R_i} V_j/R_j` along a transition morphism `g : j ⟶ i`, then the base change of
`W ⟶ U₀` along `a` is `P ×_{V_i} V_j`. -/
theorem exists_isPullback_quotient_baseChange {i j : J} (g : j ⟶ i)
    {U₀ P W : BigFppfOver B S hS} (q₀ : yoneda.obj U₀ ⟶ E.quotient.obj i)
    (a : P ⟶ U₀) (b : P ⟶ E.obj.obj i)
    (hsqP : IsPullback (yoneda.map b) (yoneda.map a) (E.toQuotient.app i) q₀)
    (toStage : yoneda.obj W ⟶ E.quotient.obj j) (w : W ⟶ U₀)
    (h : IsPullback toStage (yoneda.map w) (E.quotient.map g) q₀) :
    ∃ α : pullback (E.obj.map g) b ⟶ W,
      IsPullback α (pullback.snd (E.obj.map g) b) w a ∧
      yoneda.map α ≫ toStage = yoneda.map (pullback.fst (E.obj.map g) b) ≫ E.toQuotient.app j := by
  have hγβ := IsPullback.of_hasPullback (E.obj.map g) b
  have hw : (yoneda.map (pullback.fst (E.obj.map g) b) ≫ E.toQuotient.app j) ≫
      E.quotient.map g = yoneda.map (pullback.snd (E.obj.map g) b ≫ a) ≫ q₀ := by
    rw [Category.assoc, ← E.toQuotient.naturality g, Functor.comp_map, ← Category.assoc,
      ← Functor.map_comp, hγβ.w, Functor.map_comp, Category.assoc, hsqP.w, Functor.map_comp,
      Category.assoc]
  let α : pullback (E.obj.map g) b ⟶ W := yoneda.preimage (h.lift _ _ hw)
  have hα₁ : yoneda.map α ≫ toStage =
      yoneda.map (pullback.fst (E.obj.map g) b) ≫ E.toQuotient.app j := by simp [α]
  have hα₂ : α ≫ w = pullback.snd (E.obj.map g) b ≫ a := yoneda.map_injective (by simp [α])
  refine ⟨α, IsPullback.of_map yoneda (by rw [hα₂]) ?_, hα₁⟩
  refine IsPullback.of_right ?_ (by rw [← yoneda.map_comp, ← yoneda.map_comp, hα₂]) h
  rw [hα₁, ← hsqP.w]
  exact (hγβ.map yoneda).paste_horiz (E.isPullback_toQuotient g)

/-- **The charts of a small system of étale quotients of finite type are bounded.** If the
objects of an inverse system of étale equivalence relations over the opposite of a directed set
smaller than the size cutoff are locally of finite type over a scheme `T`, with affine transition
morphisms, then the system of quotients has bounded charts. -/
theorem chartsBounded {I : Type u} [Preorder I] (E : EtaleRelationSystem B S hS Iᵒᵖ)
    (hI : #I < B.cutoff)
    (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    {T : Scheme.{u}} (τ : ∀ j, (BigFppfOver.toScheme B S hS).obj (E.obj.obj j) ⟶ T)
    (hτ : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), (BigFppfOver.toScheme B S hS).map (E.obj.map g) ≫ τ j = τ i)
    (hlft : ∀ j, LocallyOfFiniteType (τ j)) :
    ChartsBounded B S hS E.quotient := by
  have hIop : #Iᵒᵖ < B.cutoff := by
    rwa [Cardinal.mk_congr (show Iᵒᵖ ≃ I from ⟨unop, op, fun _ ↦ rfl, fun _ ↦ rfl⟩)]
  refine chartsBounded_of_size_le B S hS E.quotient hIop
    (fun i => mk_over_lt_of_mk_lt B.aleph0_lt_cutoff hIop
      (fun _ _ => (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans
        Cardinal.one_le_aleph0) i) ?_
  intro i₀ U₀ q₀
  let Tf := BigFppfOver.toScheme B S hS
  let U' := (BigAffineFppf.inclusion B S hS).obj U₀
  have hrep : yoneda.relativelyRepresentable (E.toQuotient.app i₀) :=
    (E.isAlgebraicSpace_quotient_obj i₀).diagonal_representable.of_diag _
  let P := hrep.pullback q₀
  let a : P ⟶ U' := hrep.snd q₀
  let b : P ⟶ E.obj.obj i₀ := yoneda.preimage (hrep.fst q₀)
  have hb : yoneda.map b = hrep.fst q₀ := Functor.map_preimage _ _
  have hsqP : IsPullback (yoneda.map b) (yoneda.map a) (E.toQuotient.app i₀) q₀ := by
    rw [hb]
    exact hrep.isPullback q₀
  have hsurj : Surjective (Tf.map a) :=
    (quotientMap_surjective_unconditional B S hS (E.s.app i₀) (E.t.app i₀)).property q₀ _ a hsqP
  have : Etale (Tf.map a) :=
    (quotientMap_etale_unconditional B S hS (E.s.app i₀) (E.t.app i₀)).property q₀ _ a hsqP
  have hstrong := B.cutoff_isStrongPrelimit
  refine ⟨2 ^ 2 ^ (Tf.obj P).size, hstrong (hstrong P.left.property), ?_⟩
  intro j g W e
  have h : IsPullback (e.hom ≫ pullback.fst (E.quotient.map g) q₀)
      (yoneda.map (yoneda.preimage (e.hom ≫ pullback.snd (E.quotient.map g) q₀)))
      (E.quotient.map g) q₀ := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ e (by simp) (by simp)
    rw [Functor.map_preimage, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨α, hα, -⟩ := E.exists_isPullback_quotient_baseChange g q₀ a b hsqP _ _ h
  have hαT := hα.map Tf
  have : Surjective (Tf.map α) := MorphismProperty.of_isPullback hαT.flip hsurj
  have : Flat (Tf.map α) := MorphismProperty.of_isPullback hαT.flip inferInstance
  have hβ := (IsPullback.of_hasPullback (E.obj.map g) b).map Tf
  have : LocallyOfFiniteType (Tf.map (E.obj.map g)) :=
    have : LocallyOfFiniteType (Tf.map (E.obj.map g) ≫ τ i₀) := by rw [hτ]; exact hlft j
    LocallyOfFiniteType.of_comp (f := Tf.map (E.obj.map g)) (g := τ i₀) this
  have : LocallyOfFiniteType (Tf.map (pullback.snd (E.obj.map g) b)) :=
    MorphismProperty.of_isPullback hβ inferInstance
  have : QuasiCompact (Tf.map (pullback.snd (E.obj.map g) b)) :=
    MorphismProperty.of_isPullback hβ inferInstance
  refine (Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective (Tf.map α)).trans ?_
  refine Cardinal.power_le_power_left two_ne_zero (Cardinal.power_le_power_left two_ne_zero ?_)
  exact Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
    (Tf.map (pullback.snd (E.obj.map g) b))

/-- The restriction of an inverse system of étale equivalence relations along a functor of index
categories. -/
@[simps]
def reindex {J' : Type u} [Category.{u} J'] (F : J' ⥤ J) : EtaleRelationSystem B S hS J' where
  obj := F ⋙ E.obj
  rel := F ⋙ E.rel
  s := Functor.whiskerLeft F E.s
  t := Functor.whiskerLeft F E.t
  isEtaleEquivalenceRelation j := E.isEtaleEquivalenceRelation (F.obj j)
  isPullback_s g := E.isPullback_s (F.map g)

/-- **A system of étale relations of finite type over `Spec ℤ` has a small subsystem with the
same limits.** If the objects of an inverse system of étale equivalence relations over the
opposite of a directed set are quasi-compact and locally of finite type over `Spec ℤ`, with
affine transition morphisms and quasi-compact relations, and the objects and the relations have
limits in schemes lying in the site, then both stay limits after restriction to a directed subset
smaller than the size cutoff of the site. -/
theorem exists_small_reindex {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (E : EtaleRelationSystem B S hS Iᵒᵖ)
    (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    (hcpt : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.obj.obj j)))
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B S hS).obj (E.obj.obj j))))
    (hrel : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.rel.obj j)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (cR : Cone E.rel) (hR : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cR)) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·)) (e : J →o I),
      #J < B.cutoff ∧
      Nonempty (IsLimit
        ((BigFppfOver.toScheme B S hS).mapCone (cV.whisker e.monotone.functor.op))) ∧
      Nonempty (IsLimit
        ((BigFppfOver.toScheme B S hS).mapCone (cR.whisker e.monotone.functor.op))) := by
  classical
  let Tf := BigFppfOver.toScheme B S hS
  have hrelaff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom (Tf.map (E.rel.map g)) := fun g =>
    MorphismProperty.of_isPullback (E.isPullback_s g).flip (hobj g)
  have hrellft : ∀ j, LocallyOfFiniteType (terminal.from (Tf.obj (E.rel.obj j))) := fun j => by
    have := hlft j
    have : Etale (Tf.map (E.s.app j)) := by
      have h := (E.isEtaleEquivalenceRelation j).etale_source
      rwa [relation_source] at h
    rw [← terminal.comp_from (Tf.map (E.s.app j))]
    infer_instance
  let D : Bool → Iᵒᵖ ⥤ Scheme.{u} := fun b => Bool.rec (E.rel ⋙ Tf) (E.obj ⋙ Tf) b
  let c : ∀ b, Cone (D b) := fun b =>
    Bool.rec (motive := fun b => Cone (D b)) (Tf.mapCone cR) (Tf.mapCone cV) b
  have hc : ∀ b, IsLimit (c b) := fun b => by cases b <;> assumption
  have hDaff : ∀ b {i j : Iᵒᵖ} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom ((D b).map f) :=
    fun b => by cases b <;> assumption
  have hDc : ∀ b i, CompactSpace ((D b).obj i) := fun b => by cases b <;> assumption
  have hlftD : ∀ b i, LocallyOfFiniteType (terminal.from ((D b).obj i)) := fun b => by
    cases b <;> assumption
  have hDqs : ∀ b i, QuasiSeparatedSpace ((D b).obj i) := fun b i => by
    have := hlftD b i
    exact quasiSeparatedSpace_of_locallyOfFiniteType_terminal _
  have hsizeD : ∀ b, (c b).pt.size < B.cutoff := fun b => by
    cases b
    exacts [cR.pt.left.property, cV.pt.left.property]
  obtain ⟨J, hJ, hne, hd, e, hJκ, he⟩ :=
    @exists_small_isLimit_whisker_of_countable _ _ _ _ Bool _ D c hc hDaff hDc hDqs
      (fun b i Y _ f _ => by
        have := hlftD b i
        exact countable_Γ_of_isOpenImmersion_of_locallyOfFiniteType f)
      _ B.aleph0_lt_cutoff
      (fun b Y _ f _ => ((Scheme.mk_sections_le_size Y ⟨⊤, isAffineOpen_top Y⟩).trans
        (Scheme.size_le_of_isOpenImmersion f)).trans_lt (hsizeD b))
  exact ⟨J, hJ, hne, hd, e, hJκ, he true, he false⟩

/-- **A sheaf presented by a system of étale relations of finite type over `Spec ℤ` is the limit
of a small system of quotients with bounded charts.** Under the hypotheses of
`AlgebraicGeometry.Space.EtaleRelationSystem.hasNoetherianApproximation` over `Spec ℤ`, the
system can be restricted to a directed subset of the index smaller than the size cutoff of the
site, so that the system of quotients has bounded charts
(`AlgebraicGeometry.Space.ChartsBounded`) and the sheaf is still its limit. -/
theorem exists_chartsBounded_reindex (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (E : EtaleRelationSystem B (⊤_ Scheme.{u}) hZ Iᵒᵖ)
    (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (E.obj.map g)))
    (hcpt : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j)))
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j))))
    (hrel : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.rel.obj j)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cV))
    (cR : Cone E.rel) (hR : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cR))
    (sL tL : cR.pt ⟶ cV.pt) (hs : ∀ j, sL ≫ cV.π.app j = cR.π.app j ≫ E.s.app j)
    (ht : ∀ j, tL ≫ cV.π.app j = cR.π.app j ≫ E.t.app j)
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) X)
    (f : yoneda.obj cV.pt ⟶ X) (hf : IsPullback (yoneda.map tL) (yoneda.map sL) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·)) (e : J →o I),
      #J < B.cutoff ∧
      ChartsBounded B (⊤_ Scheme.{u}) hZ (E.reindex e.monotone.functor.op).quotient ∧
      ∃ iso : X ≅ limit (E.reindex e.monotone.functor.op).quotient,
        f ≫ iso.hom = (E.reindex e.monotone.functor.op).limitToQuotient
          (cV.whisker e.monotone.functor.op) := by
  obtain ⟨J, hJ, hne, hd, e, hJκ, ⟨hV'⟩, ⟨hR'⟩⟩ :=
    E.exists_small_reindex hobj hcpt hlft hrel cV hV cR hR
  let _ := hJ
  let _ := hne
  let _ := hd
  let F := e.monotone.functor.op
  let E' := E.reindex F
  have hobj' : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (E'.obj.map g)) := fun g => hobj (F.map g)
  refine ⟨J, hJ, hne, hd, e, hJκ,
    E'.chartsBounded hJκ hobj' (fun _ => terminal.from _) (fun _ => terminal.comp_from _)
      (fun j => hlft (F.obj j)), ?_⟩
  have : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  exact E'.exists_iso_limit_quotient (cV.whisker F)
    (BigFppfOver.isLimit_of_isLimit_toScheme B (⊤_ Scheme.{u}) hZ hV') (cR.whisker F)
    (BigFppfOver.isLimit_of_isLimit_toScheme B (⊤_ Scheme.{u}) hZ hR') sL tL
    (fun j => hs (F.obj j)) (fun j => ht (F.obj j)) hX f hf hsurj hetale

end EtaleRelationSystem

end AlgebraicGeometry.Space

end
