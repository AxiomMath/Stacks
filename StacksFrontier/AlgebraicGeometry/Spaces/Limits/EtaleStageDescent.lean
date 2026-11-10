module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleDescentAlongPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PresentedNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientOfCartesianRelation

/-!
# Étale morphisms to the limit of a presented system descend to a stage

Let `U = lim U_i` be the limit of a cofiltered system of algebraic spaces presented by systems
of étale atlases `V_i` and of their kernel pairs `R_i`, with the limits `V` and `R` of these
systems realised in the site. An étale morphism `W ⟶ U` of algebraic spaces whose base change
`W' = W ×_U V` to the limit atlas is an étale, quasi-compact and quasi-separated morphism of
objects of the site is the base change of an étale morphism `W₀ ⟶ U_j` at some stage.

The proof descends the étale scheme `W'` over `V` to an étale scheme `M` over a stage `V_j`
(Stacks 01ZM and 07RP), descends the second projection of the descent datum `W' ×_W W'` of
`W'` to a stage by Stacks 01ZC, arranges the identities expressing that it is an equivalence
relation at a later stage by Stacks 01ZC again, and takes the quotient of `M` by the resulting
étale equivalence relation, which is cartesian over the relation `R_j` (Stacks 02WW).

## Main results

* `AlgebraicGeometry.Space.LimitPresentation.isPullback_limitKernel`: the limit of the kernel
  pairs of a presentation is the kernel pair of the limit atlas.
* `AlgebraicGeometry.Space.LimitPresentation.EtaleStageModel`: a model at a stage of an étale
  morphism to the limit.
* `AlgebraicGeometry.Space.LimitPresentation.exists_etaleStageModel`: the descent statement
  above.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- **The kernel pairs of a cartesian square of atlases form a cartesian square over the first
projections.** If `V' = V ×_F F'` and `R`, `R'` are the kernel pairs of `V ⟶ F` and
`V' ⟶ F'`, then `R' = R ×_V V'` along the first projections. -/
theorem isPullback_kernelPair_map {C : Type*} [Category* C] {V V' F F' R R' : C}
    {a : V ⟶ F} {a' : V' ⟶ F'} {mV : V' ⟶ V} {mF : F' ⟶ F} (hV : IsPullback mV a' a mF)
    {s t : R ⟶ V} (hR : IsPullback s t a a) {s' t' : R' ⟶ V'} (hR' : IsPullback s' t' a' a')
    {mR : R' ⟶ R} (hs : mR ≫ s = s' ≫ mV) (ht : mR ≫ t = t' ≫ mV) :
    IsPullback mR s' s mV := by
  have hbig : IsPullback (mR ≫ t) s' a (mV ≫ a) := by
    rw [ht, hV.w]
    exact hR'.flip.paste_horiz hV
  exact hbig.of_right hs hR.flip

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace LimitPresentation

variable {I : Type u} [Category.{u} I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : Cone D}
  (P : LimitPresentation B S hS D c)

/-- The family of algebraic spaces with atlases underlying a presentation. -/
noncomputable def toAtlasFamily (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) :
    AtlasFamily B S hS I where
  V := P.atlas
  R := P.relation
  s := P.src
  t := P.tgt
  X := D.obj
  isAlgebraicSpace := hD
  v j := P.atlasMap.app j
  surjective := P.surjective_atlasMap
  etale := P.etale_atlasMap
  isPullback := P.isPullback_relation

/-- The transition morphisms of the atlas family of a presentation are those of the presented
system. -/
theorem toAtlasFamily_map (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) {i j : I} (e : i ⟶ j) :
    (P.toAtlasFamily hD).map e = D.map e :=
  (P.toAtlasFamily hD).hom_ext (hD j).isSheaf
    (((P.toAtlasFamily hD).v_map e).trans (P.atlasMap.naturality e))

/-- The system of the atlas family of a presentation is the presented system. -/
noncomputable def diagramIso (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) :
    (P.toAtlasFamily hD).diagram ≅ D :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun e => by
    simp only [toAtlasFamily_map, Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

include P in
/-- **The limit of the kernel pairs is the kernel pair of the limit atlas.** -/
theorem isPullback_limitKernel [IsCofiltered I] (hc : IsLimit c)
    (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) :
    IsPullback (yoneda.map P.srcLim) (yoneda.map P.tgtLim) P.limitAtlas P.limitAtlas :=
  (P.toAtlasFamily hD).isPullback_limit_kernel P.isLimit_atlasCone P.isLimit_relationCone
    P.srcLim P.tgtLim P.srcLim_π P.tgtLim_π ((Cone.postcompose (P.diagramIso hD).inv).obj c)
    ((IsLimit.postcomposeInvEquiv _ _).symm hc) P.limitAtlas (fun i => by
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, diagramIso]
      exact P.limitAtlas_π i)

include P in
/-- The limit of the kernel pairs is the base change of a stage kernel pair along the first
projections. -/
theorem isPullback_src_relationCone [IsCofiltered I] (hc : IsLimit c)
    (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) (j : I) :
    IsPullback (P.relationCone.π.app j) P.srcLim (P.src.app j) (P.atlasCone.π.app j) :=
  IsPullback.of_map yoneda (P.srcLim_π j).symm
    (isPullback_kernelPair_map (P.isPullback_limitAtlas j) (P.isPullback_relation j)
      (P.isPullback_limitKernel hc hD)
      (by rw [← Functor.map_comp, ← Functor.map_comp, P.srcLim_π])
      (by rw [← Functor.map_comp, ← Functor.map_comp, P.tgtLim_π]))

include P in
/-- A transition morphism of the kernel pairs is the base change of the transition morphism of
the atlases along the first projections. -/
theorem isPullback_src_relation_map {i j : I} (e : i ⟶ j) :
    IsPullback (P.relation.map e) (P.src.app i) (P.src.app j) (P.atlas.map e) :=
  IsPullback.of_map yoneda (P.src.naturality e)
    (isPullback_kernelPair_map (P.isPullback_atlas e) (P.isPullback_relation j)
      (P.isPullback_relation i)
      (by rw [← Functor.map_comp, ← Functor.map_comp, P.src.naturality])
      (by rw [← Functor.map_comp, ← Functor.map_comp, P.tgt.naturality]))

include P in
/-- The limit of the kernel pairs is the base change of a stage kernel pair along the second
projections. -/
theorem isPullback_tgt_relationCone [IsCofiltered I] (hc : IsLimit c)
    (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) (j : I) :
    IsPullback (P.relationCone.π.app j) P.tgtLim (P.tgt.app j) (P.atlasCone.π.app j) :=
  IsPullback.of_map yoneda (P.tgtLim_π j).symm
    (isPullback_kernelPair_map (P.isPullback_limitAtlas j) (P.isPullback_relation j).flip
      (P.isPullback_limitKernel hc hD).flip
      (by rw [← Functor.map_comp, ← Functor.map_comp, P.tgtLim_π])
      (by rw [← Functor.map_comp, ← Functor.map_comp, P.srcLim_π]))

include P in
/-- A transition morphism of the kernel pairs is the base change of the transition morphism of
the atlases along the second projections. -/
theorem isPullback_tgt_relation_map {i j : I} (e : i ⟶ j) :
    IsPullback (P.relation.map e) (P.tgt.app i) (P.tgt.app j) (P.atlas.map e) :=
  IsPullback.of_map yoneda (P.tgt.naturality e)
    (isPullback_kernelPair_map (P.isPullback_atlas e) (P.isPullback_relation j).flip
      (P.isPullback_relation i).flip
      (by rw [← Functor.map_comp, ← Functor.map_comp, P.tgt.naturality])
      (by rw [← Functor.map_comp, ← Functor.map_comp, P.src.naturality]))

include P in
/-- Two morphisms into a stage kernel pair agree when their two projections agree. -/
theorem relation_hom_ext (j : I) {Z : BigFppfOver B S hS} {x y : Z ⟶ P.relation.obj j}
    (hs : x ≫ P.src.app j = y ≫ P.src.app j) (ht : x ≫ P.tgt.app j = y ≫ P.tgt.app j) :
    x = y :=
  yoneda.map_injective ((P.isPullback_relation j).hom_ext
    (by rw [← Functor.map_comp, ← Functor.map_comp, hs])
    (by rw [← Functor.map_comp, ← Functor.map_comp, ht]))

/-- A morphism into a stage kernel pair with prescribed projections. -/
noncomputable def relationLift (j : I) {Z : BigFppfOver B S hS} (x y : Z ⟶ P.atlas.obj j)
    (h : yoneda.map x ≫ P.atlasMap.app j = yoneda.map y ≫ P.atlasMap.app j) :
    Z ⟶ P.relation.obj j :=
  yoneda.preimage ((P.isPullback_relation j).lift (yoneda.map x) (yoneda.map y) h)

/-- The first projection of `relationLift j x y h` is `x`. -/
@[reassoc (attr := simp)]
theorem relationLift_src (j : I) {Z : BigFppfOver B S hS} (x y : Z ⟶ P.atlas.obj j)
    (h : yoneda.map x ≫ P.atlasMap.app j = yoneda.map y ≫ P.atlasMap.app j) :
    P.relationLift j x y h ≫ P.src.app j = x :=
  yoneda.map_injective (by simp [relationLift])

/-- The second projection of `relationLift j x y h` is `y`. -/
@[reassoc (attr := simp)]
theorem relationLift_tgt (j : I) {Z : BigFppfOver B S hS} (x y : Z ⟶ P.atlas.obj j)
    (h : yoneda.map x ≫ P.atlasMap.app j = yoneda.map y ≫ P.atlasMap.app j) :
    P.relationLift j x y h ≫ P.tgt.app j = y :=
  yoneda.map_injective (by simp [relationLift])

include P in
/-- The two projections of a morphism into a stage kernel pair agree after composition with the
stage atlas. -/
theorem src_atlasMap (j : I) {Z : BigFppfOver B S hS} (x : Z ⟶ P.relation.obj j) :
    yoneda.map (x ≫ P.src.app j) ≫ P.atlasMap.app j =
      yoneda.map (x ≫ P.tgt.app j) ≫ P.atlasMap.app j := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    (P.isPullback_relation j).w]

include P in
/-- The projections of a stage kernel pair are étale. -/
theorem etale_src (j : I) : Etale ((BigFppfOver.toScheme B S hS).map (P.src.app j)) :=
  (presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mp
    (presheaf_of_isPullback B S hS (P.isPullback_relation j).flip (P.etale_atlasMap j))

include P in
/-- The projections of a stage kernel pair are étale. -/
theorem etale_tgt (j : I) : Etale ((BigFppfOver.toScheme B S hS).map (P.tgt.app j)) :=
  (presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mp
    (presheaf_of_isPullback B S hS (P.isPullback_relation j) (P.etale_atlasMap j))

/-- Two morphisms into an object over a stage kernel pair via the first projection agree when
their first projections and their projections to the stage atlas agree. -/
private theorem hom_ext_of_isPullback_src (j : I) {M Q K : BigFppfOver B S hS} {f₁ : Q ⟶ M}
    {k : Q ⟶ P.relation.obj j} {p : M ⟶ P.atlas.obj j} (H : IsPullback f₁ k p (P.src.app j))
    {x y : K ⟶ Q} (h₁ : x ≫ f₁ = y ≫ f₁) (hs : (x ≫ k) ≫ P.src.app j = (y ≫ k) ≫ P.src.app j)
    (ht : (x ≫ k) ≫ P.tgt.app j = (y ≫ k) ≫ P.tgt.app j) : x = y :=
  H.hom_ext h₁ (P.relation_hom_ext j hs ht)

/-- The scheme underlying a stage atlas is quasi-compact. -/
private theorem compactSpace_atlas_obj (j : I) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (P.atlas.obj j)) :=
  compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS (P.isQuasiCompactSpace_atlas j)

/-- The scheme underlying a stage kernel pair is quasi-compact. -/
private theorem compactSpace_relation_obj (j : I) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (P.relation.obj j)) :=
  compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS (P.isQuasiCompactSpace_relation j)

end LimitPresentation

/-- **The fibre square of a relation over a cartesian square.** Let `f₁, f₂ : Q ⇉ M` and
`f₁', f₂' : Q' ⇉ M'` with `Q' = Q ×_M M'` along the first projections, compatible with the
second projections, and let `M' = M ×_V V'`. Then the induced morphism
`Q' ×_{M'} Q' ⟶ Q ×_M Q` exhibits its source as the base change of its target along
`V' ⟶ V`. -/
theorem isPullback_pullbackMap_of_isPullback {C : Type*} [Category* C] [HasPullbacks C]
    {M M' Q Q' V V' : C} {f₁ f₂ : Q ⟶ M} {f₁' f₂' : Q' ⟶ M'} {mQ : Q' ⟶ Q} {mM : M' ⟶ M}
    {p : M ⟶ V} {p' : M' ⟶ V'} {mV : V' ⟶ V} (H₁ : IsPullback mQ f₁' f₁ mM)
    (h₂ : mQ ≫ f₂ = f₂' ≫ mM) (hm : IsPullback mM p' p mV) :
    IsPullback (pullback.map f₂' f₁' f₂ f₁ mQ mQ mM h₂.symm H₁.w.symm)
      (pullback.fst f₂' f₁' ≫ f₁' ≫ p') (pullback.fst f₂ f₁ ≫ f₁ ≫ p) mV := by
  have hbig : IsPullback (pullback.map f₂' f₁' f₂ f₁ mQ mQ mM h₂.symm H₁.w.symm ≫
      pullback.snd f₂ f₁) (pullback.fst f₂' f₁') f₁ (mQ ≫ f₂) := by
    rw [pullback.lift_snd, h₂]
    exact (IsPullback.of_hasPullback f₂' f₁').flip.paste_horiz H₁
  have hG : IsPullback (pullback.map f₂' f₁' f₂ f₁ mQ mQ mM h₂.symm H₁.w.symm)
      (pullback.fst f₂' f₁') (pullback.fst f₂ f₁) mQ :=
    hbig.of_right (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f₂ f₁).flip
  simpa only [Category.assoc] using (hG.paste_vert H₁).paste_vert hm

namespace LimitPresentation

variable {I : Type u} [Category.{u} I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : Cone D}
  (P : LimitPresentation B S hS D c)

/-- The diagonal of a stage kernel pair. -/
noncomputable def reflRel (j : I) : P.atlas.obj j ⟶ P.relation.obj j :=
  P.relationLift j (𝟙 _) (𝟙 _) rfl

/-- The symmetry of a stage kernel pair. -/
noncomputable def symmRel (j : I) : P.relation.obj j ⟶ P.relation.obj j :=
  P.relationLift j (P.tgt.app j) (P.src.app j) (P.src_atlasMap j (𝟙 _)).symm

/-- The composition of a stage kernel pair. -/
noncomputable def transRel (j : I) : pullback (P.tgt.app j) (P.src.app j) ⟶ P.relation.obj j :=
  P.relationLift j (pullback.fst _ _ ≫ P.src.app j) (pullback.snd _ _ ≫ P.tgt.app j) (by
    rw [P.src_atlasMap j, pullback.condition, P.src_atlasMap j])

/-- The first projection of the diagonal of a stage kernel pair is the identity. -/
@[reassoc (attr := simp)]
theorem reflRel_src (j : I) : P.reflRel j ≫ P.src.app j = 𝟙 _ := P.relationLift_src j _ _ _

/-- The second projection of the diagonal of a stage kernel pair is the identity. -/
@[reassoc (attr := simp)]
theorem reflRel_tgt (j : I) : P.reflRel j ≫ P.tgt.app j = 𝟙 _ := P.relationLift_tgt j _ _ _

/-- The first projection of the symmetry of a stage kernel pair is the second projection. -/
@[reassoc (attr := simp)]
theorem symmRel_src (j : I) : P.symmRel j ≫ P.src.app j = P.tgt.app j :=
  P.relationLift_src j _ _ _

/-- The second projection of the symmetry of a stage kernel pair is the first projection. -/
@[reassoc (attr := simp)]
theorem symmRel_tgt (j : I) : P.symmRel j ≫ P.tgt.app j = P.src.app j :=
  P.relationLift_tgt j _ _ _

/-- The first projection of the composition of a stage kernel pair is the first projection of
the first factor. -/
@[reassoc (attr := simp)]
theorem transRel_src (j : I) : P.transRel j ≫ P.src.app j = pullback.fst _ _ ≫ P.src.app j :=
  P.relationLift_src j _ _ _

/-- The second projection of the composition of a stage kernel pair is the second projection of
the second factor. -/
@[reassoc (attr := simp)]
theorem transRel_tgt (j : I) : P.transRel j ≫ P.tgt.app j = pullback.snd _ _ ≫ P.tgt.app j :=
  P.relationLift_tgt j _ _ _

variable [IsCofiltered I] {W' : BigFppfOver B S hS} (w' : W' ⟶ P.atlasCone.pt)
  {Q' : BigFppfOver B S hS} (f₁' f₂' : Q' ⟶ W') (k' : Q' ⟶ P.relationCone.pt)

/-- A model at the stage `j` of the étale object `W'` over the limit atlas, with the first
projection of a relation on it lying over the kernel pair of the stage atlas: `M` is étale over
`V_j` with `W' = M ×_{V_j} V`, and `Q = M ×_{V_j} R_j` along the first projection of `R_j`,
compatibly with the relation `f₁', k'` at the limit. -/
structure EtaleStage (j : I) where
  /-- The model of `W'`. -/
  M : BigFppfOver B S hS
  /-- Its étale morphism to the stage atlas. -/
  p : M ⟶ P.atlas.obj j
  /-- The projection from `W'`. -/
  m : W' ⟶ M
  isPullback_m : IsPullback m w' p (P.atlasCone.π.app j)
  /-- The morphism to the stage atlas is étale. -/
  etale_p : Etale ((BigFppfOver.toScheme B S hS).map p)
  /-- The morphism to the stage atlas is quasi-compact. -/
  quasiCompact_p : QuasiCompact ((BigFppfOver.toScheme B S hS).map p)
  /-- The morphism to the stage atlas is quasi-separated. -/
  quasiSeparated_p : QuasiSeparated ((BigFppfOver.toScheme B S hS).map p)
  /-- The relation on the model. -/
  Q : BigFppfOver B S hS
  /-- Its morphism to the stage kernel pair. -/
  k : Q ⟶ P.relation.obj j
  /-- The first projection of the relation. -/
  f₁ : Q ⟶ M
  isPullback_f₁ : IsPullback f₁ k p (P.src.app j)
  /-- The projection from the relation at the limit. -/
  mQ : Q' ⟶ Q
  isPullback_mQ : IsPullback mQ k' k (P.relationCone.π.app j)
  mQ_f₁ : mQ ≫ f₁ = f₁' ≫ m

variable {P w' f₁' f₂' k'}

namespace EtaleStage

section Defs

variable {j : I} (d : EtaleStage P w' f₁' k' j)

/-- A second projection of the relation of a model, lying over the second projection of the
stage kernel pair and compatible with the second projection `f₂'` at the limit. -/
structure Second (f₂' : Q' ⟶ W') where
  /-- The second projection. -/
  f₂ : d.Q ⟶ d.M
  f₂_p : f₂ ≫ d.p = d.k ≫ P.tgt.app j
  mQ_f₂ : d.mQ ≫ f₂ = f₂' ≫ d.m

variable (hk₁ : f₁' ≫ w' = k' ≫ P.srcLim) (hk₂ : f₂' ≫ w' = k' ≫ P.tgtLim)

include hk₁ in
/-- The base change of a model to a later stage. -/
@[simps]
noncomputable def restrict {j' : I} (e : j' ⟶ j) : EtaleStage P w' f₁' k' j' where
  M := pullback d.p (P.atlas.map e)
  p := pullback.snd _ _
  m := pullback.lift d.m (w' ≫ P.atlasCone.π.app j') (by
    rw [Category.assoc, P.atlasCone.w e, d.isPullback_m.w])
  isPullback_m := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, P.atlasCone.w e]
    exact d.isPullback_m
  etale_p := by
    have := d.etale_p
    exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback d.p (P.atlas.map e)).map (BigFppfOver.toScheme B S hS)) this
  quasiCompact_p := by
    have := d.quasiCompact_p
    exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback d.p (P.atlas.map e)).map (BigFppfOver.toScheme B S hS)) this
  quasiSeparated_p := by
    have := d.quasiSeparated_p
    exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback d.p (P.atlas.map e)).map (BigFppfOver.toScheme B S hS)) this
  Q := pullback d.k (P.relation.map e)
  k := pullback.snd _ _
  f₁ := pullback.lift (pullback.fst _ _ ≫ d.f₁) (pullback.snd _ _ ≫ P.src.app j') (by
    rw [Category.assoc, d.isPullback_f₁.w, ← Category.assoc, pullback.condition,
      Category.assoc, P.src.naturality, Category.assoc])
  isPullback_f₁ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, ← P.src.naturality]
    exact (IsPullback.of_hasPullback d.k (P.relation.map e)).paste_horiz d.isPullback_f₁
  mQ := pullback.lift d.mQ (k' ≫ P.relationCone.π.app j') (by
    rw [Category.assoc, P.relationCone.w e, d.isPullback_mQ.w])
  isPullback_mQ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, P.relationCone.w e]
    exact d.isPullback_mQ
  mQ_f₁ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, d.mQ_f₁]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [← P.srcLim_π, ← Category.assoc, ← hk₁, Category.assoc]

variable {d}

include hk₂ in
/-- The base change of a second projection to a later stage. -/
@[simps]
noncomputable def Second.restrict (s : d.Second f₂') {j' : I} (e : j' ⟶ j) :
    (d.restrict hk₁ e).Second f₂' where
  f₂ := show pullback d.k (P.relation.map e) ⟶ pullback d.p (P.atlas.map e) from
    pullback.lift (pullback.fst _ _ ≫ s.f₂) (pullback.snd _ _ ≫ P.tgt.app j') (by
      rw [Category.assoc, s.f₂_p, ← Category.assoc, pullback.condition,
        Category.assoc, P.tgt.naturality, Category.assoc])
  f₂_p := pullback.lift_snd _ _ _
  mQ_f₂ := by
    change pullback.lift d.mQ (k' ≫ P.relationCone.π.app j') _ ≫
      pullback.lift (pullback.fst d.k (P.relation.map e) ≫ s.f₂)
        (pullback.snd d.k (P.relation.map e) ≫ P.tgt.app j') _ =
      f₂' ≫ pullback.lift d.m (w' ≫ P.atlasCone.π.app j') _
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, s.mQ_f₂]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [← P.tgtLim_π, ← Category.assoc, ← hk₂, Category.assoc]


end Defs

section Restrict

variable {j : I} (d : EtaleStage P w' f₁' k' j) (hk₁ : f₁' ≫ w' = k' ≫ P.srcLim)
  {j' : I} (e : j' ⟶ j)

/-- The projection from the model at a later stage. -/
noncomputable abbrev restrictFstM : (d.restrict hk₁ e).M ⟶ d.M :=
  pullback.fst d.p (P.atlas.map e)

/-- The projection from the relation at a later stage. -/
noncomputable abbrev restrictFstQ : (d.restrict hk₁ e).Q ⟶ d.Q :=
  pullback.fst d.k (P.relation.map e)

omit [IsCofiltered I] in
/-- The projection from the model at a later stage lies over the transition morphism of the
atlases. -/
@[reassoc]
theorem restrictFstM_p : d.restrictFstM hk₁ e ≫ d.p = (d.restrict hk₁ e).p ≫ P.atlas.map e :=
  pullback.condition

omit [IsCofiltered I] in
/-- The projection from the relation at a later stage lies over the transition morphism of the
kernel pairs. -/
@[reassoc]
theorem restrictFstQ_k : d.restrictFstQ hk₁ e ≫ d.k = (d.restrict hk₁ e).k ≫ P.relation.map e :=
  pullback.condition

omit [IsCofiltered I] in
/-- The projections from the relation and from the model at a later stage commute with the first
projections. -/
@[reassoc]
theorem restrictFstQ_f₁ :
    d.restrictFstQ hk₁ e ≫ d.f₁ = (d.restrict hk₁ e).f₁ ≫ d.restrictFstM hk₁ e :=
  (pullback.lift_fst _ _ _).symm

omit [IsCofiltered I] in
/-- Two morphisms into the model at a later stage agree when their compositions with the
projection to the model and with the morphism to the stage atlas agree. -/
theorem restrict_hom_ext {Z : BigFppfOver B S hS} {x y : Z ⟶ (d.restrict hk₁ e).M}
    (h₁ : x ≫ d.restrictFstM hk₁ e = y ≫ d.restrictFstM hk₁ e)
    (h₂ : x ≫ (d.restrict hk₁ e).p = y ≫ (d.restrict hk₁ e).p) : x = y :=
  pullback.hom_ext h₁ h₂

variable {d} (hk₂ : f₂' ≫ w' = k' ≫ P.tgtLim)

omit [IsCofiltered I] in
/-- The projections from the relation and from the model at a later stage commute with the
second projections. -/
@[reassoc]
theorem restrictFstQ_f₂ (s : d.Second f₂') :
    d.restrictFstQ hk₁ e ≫ s.f₂ = (s.restrict hk₁ hk₂ e).f₂ ≫ d.restrictFstM hk₁ e :=
  (pullback.lift_fst _ _ _).symm

end Restrict

variable {j : I} (d : EtaleStage P w' f₁' k' j)

omit [IsCofiltered I] in
/-- The model is quasi-compact. -/
theorem compactSpace_M : CompactSpace ((BigFppfOver.toScheme B S hS).obj d.M) := by
  have := d.quasiCompact_p
  have := P.compactSpace_atlas_obj j
  exact QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map d.p)

omit [IsCofiltered I] in
/-- The morphism from the relation of a model to the stage kernel pair is quasi-compact. -/
theorem quasiCompact_k : QuasiCompact ((BigFppfOver.toScheme B S hS).map d.k) := by
  have := d.quasiCompact_p
  exact MorphismProperty.of_isPullback (d.isPullback_f₁.map (BigFppfOver.toScheme B S hS)) this

omit [IsCofiltered I] in
/-- The morphism from the relation of a model to the stage kernel pair is étale. -/
theorem etale_k : Etale ((BigFppfOver.toScheme B S hS).map d.k) := by
  have := d.etale_p
  exact MorphismProperty.of_isPullback (d.isPullback_f₁.map (BigFppfOver.toScheme B S hS)) this

omit [IsCofiltered I] in
/-- The relation of a model is quasi-compact. -/
theorem compactSpace_Q : CompactSpace ((BigFppfOver.toScheme B S hS).obj d.Q) := by
  have := d.quasiCompact_k
  have := P.compactSpace_relation_obj j
  exact QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map d.k)

/-- The diagonal of the relation of a model. -/
noncomputable def rho : d.M ⟶ d.Q :=
  d.isPullback_f₁.lift (𝟙 _) (d.p ≫ P.reflRel j) (by
    rw [Category.assoc, reflRel_src, Category.comp_id, Category.id_comp])

omit [IsCofiltered I] in
/-- The first projection of the diagonal of the relation of a model is the identity. -/
@[reassoc (attr := simp)]
theorem rho_f₁ : d.rho ≫ d.f₁ = 𝟙 _ := IsPullback.lift_fst _ _ _ _

omit [IsCofiltered I] in
/-- The diagonal of the relation of a model lies over the diagonal of the stage kernel pair. -/
@[reassoc]
theorem rho_k : d.rho ≫ d.k = d.p ≫ P.reflRel j := IsPullback.lift_snd _ _ _ _

omit [IsCofiltered I] in
/-- The diagonal of the relation of a model lies over the identity of the stage atlas via the
first projection. -/
@[reassoc]
theorem rho_k_src : d.rho ≫ d.k ≫ P.src.app j = d.p := by
  rw [d.rho_k_assoc, reflRel_src, Category.comp_id]

omit [IsCofiltered I] in
/-- The diagonal of the relation of a model lies over the identity of the stage atlas via the
second projection. -/
@[reassoc]
theorem rho_k_tgt : d.rho ≫ d.k ≫ P.tgt.app j = d.p := by
  rw [d.rho_k_assoc, reflRel_tgt, Category.comp_id]

variable {d}

/-- The symmetry of the relation of a model. -/
noncomputable def sigma (s : d.Second f₂') : d.Q ⟶ d.Q :=
  d.isPullback_f₁.lift s.f₂ (d.k ≫ P.symmRel j) (by
    rw [Category.assoc, symmRel_src, s.f₂_p])

omit [IsCofiltered I] in
/-- The first projection of the symmetry of the relation of a model is the second projection. -/
@[reassoc (attr := simp)]
theorem sigma_f₁ (s : d.Second f₂') : d.sigma s ≫ d.f₁ = s.f₂ := IsPullback.lift_fst _ _ _ _

omit [IsCofiltered I] in
/-- The symmetry of the relation of a model lies over the symmetry of the stage kernel pair. -/
@[reassoc]
theorem sigma_k (s : d.Second f₂') : d.sigma s ≫ d.k = d.k ≫ P.symmRel j :=
  IsPullback.lift_snd _ _ _ _

omit [IsCofiltered I] in
/-- The symmetry of the relation of a model exchanges the projections to the stage atlas: the
first becomes the second. -/
@[reassoc]
theorem sigma_k_src (s : d.Second f₂') : d.sigma s ≫ d.k ≫ P.src.app j = d.k ≫ P.tgt.app j := by
  rw [sigma_k_assoc, symmRel_src]

omit [IsCofiltered I] in
/-- The symmetry of the relation of a model exchanges the projections to the stage atlas: the
second becomes the first. -/
@[reassoc]
theorem sigma_k_tgt (s : d.Second f₂') : d.sigma s ≫ d.k ≫ P.tgt.app j = d.k ≫ P.src.app j := by
  rw [sigma_k_assoc, symmRel_tgt]

/-- The pair of morphisms to the stage kernel pair underlying a composable pair of the relation of
a model. -/
noncomputable def tauPair (s : d.Second f₂') :
    pullback s.f₂ d.f₁ ⟶ pullback (P.tgt.app j) (P.src.app j) :=
  pullback.lift (pullback.fst _ _ ≫ d.k) (pullback.snd _ _ ≫ d.k) (by
    rw [Category.assoc, ← s.f₂_p, ← Category.assoc, pullback.condition, Category.assoc,
      d.isPullback_f₁.w, Category.assoc])

/-- The composition of the relation of a model. -/
noncomputable def tau (s : d.Second f₂') : pullback s.f₂ d.f₁ ⟶ d.Q :=
  d.isPullback_f₁.lift (pullback.fst _ _ ≫ d.f₁) (d.tauPair s ≫ P.transRel j) (by
    rw [Category.assoc, Category.assoc, transRel_src, tauPair, pullback.lift_fst_assoc,
      Category.assoc, d.isPullback_f₁.w])

omit [IsCofiltered I] in
/-- The first projection of the composition of the relation of a model is the first projection
of the first factor. -/
@[reassoc (attr := simp)]
theorem tau_f₁ (s : d.Second f₂') : d.tau s ≫ d.f₁ = pullback.fst _ _ ≫ d.f₁ :=
  IsPullback.lift_fst _ _ _ _

omit [IsCofiltered I] in
/-- The composition of the relation of a model lies over the composition of the stage kernel
pair. -/
@[reassoc]
theorem tau_k (s : d.Second f₂') : d.tau s ≫ d.k = d.tauPair s ≫ P.transRel j :=
  IsPullback.lift_snd _ _ _ _

omit [IsCofiltered I] in
/-- The composition of the relation of a model has, over the stage atlas, the first projection
of the first factor. -/
@[reassoc]
theorem tau_k_src (s : d.Second f₂') :
    d.tau s ≫ d.k ≫ P.src.app j = pullback.fst _ _ ≫ d.k ≫ P.src.app j := by
  rw [tau_k_assoc, transRel_src, tauPair, pullback.lift_fst_assoc, Category.assoc]

omit [IsCofiltered I] in
/-- The composition of the relation of a model has, over the stage atlas, the second projection
of the second factor. -/
@[reassoc]
theorem tau_k_tgt (s : d.Second f₂') :
    d.tau s ≫ d.k ≫ P.tgt.app j = pullback.snd _ _ ≫ d.k ≫ P.tgt.app j := by
  rw [tau_k_assoc, transRel_tgt, tauPair, pullback.lift_snd_assoc, Category.assoc]

section Persistence

variable (hk₁ : f₁' ≫ w' = k' ≫ P.srcLim) (hk₂ : f₂' ≫ w' = k' ≫ P.tgtLim) {j' : I} (e : j' ⟶ j)

include hk₂ in
omit [IsCofiltered I] in
/-- **The diagonal identity passes to a later stage** as soon as it holds after base change. -/
theorem rho_f₂_restrict (s : d.Second f₂')
    (h : d.restrictFstM hk₁ e ≫ d.rho ≫ s.f₂ = d.restrictFstM hk₁ e) :
    (d.restrict hk₁ e).rho ≫ (s.restrict hk₁ hk₂ e).f₂ = 𝟙 _ := by
  have hQ : (d.restrict hk₁ e).rho ≫ d.restrictFstQ hk₁ e = d.restrictFstM hk₁ e ≫ d.rho := by
    refine P.hom_ext_of_isPullback_src j d.isPullback_f₁ ?_ ?_ ?_
    · rw [Category.assoc, restrictFstQ_f₁, rho_f₁_assoc, Category.assoc, rho_f₁,
        Category.comp_id]
    · rw [Category.assoc, Category.assoc, restrictFstQ_k_assoc, P.src.naturality,
        rho_k_src_assoc, Category.assoc, Category.assoc, rho_k_src, restrictFstM_p]
    · rw [Category.assoc, Category.assoc, restrictFstQ_k_assoc, P.tgt.naturality,
        rho_k_tgt_assoc, Category.assoc, Category.assoc, rho_k_tgt, restrictFstM_p]
  refine d.restrict_hom_ext hk₁ e ?_ ?_
  · rw [Category.assoc, ← restrictFstQ_f₂ hk₁ e hk₂ s, ← Category.assoc, hQ, Category.assoc, h,
      Category.id_comp]
  · rw [Category.assoc, (s.restrict hk₁ hk₂ e).f₂_p, rho_k_tgt, Category.id_comp]

include hk₂ in
omit [IsCofiltered I] in
/-- **The symmetry identity passes to a later stage** as soon as it holds after base change. -/
theorem sigma_f₂_restrict (s : d.Second f₂')
    (h : d.restrictFstQ hk₁ e ≫ d.sigma s ≫ s.f₂ = d.restrictFstQ hk₁ e ≫ d.f₁) :
    (d.restrict hk₁ e).sigma (s.restrict hk₁ hk₂ e) ≫ (s.restrict hk₁ hk₂ e).f₂ =
      (d.restrict hk₁ e).f₁ := by
  have hQ : (d.restrict hk₁ e).sigma (s.restrict hk₁ hk₂ e) ≫ d.restrictFstQ hk₁ e =
      d.restrictFstQ hk₁ e ≫ d.sigma s := by
    refine P.hom_ext_of_isPullback_src j d.isPullback_f₁ ?_ ?_ ?_
    · rw [Category.assoc, restrictFstQ_f₁, sigma_f₁_assoc, Category.assoc, sigma_f₁,
        restrictFstQ_f₂ hk₁ e hk₂ s]
    · rw [Category.assoc, Category.assoc, restrictFstQ_k_assoc, P.src.naturality,
        sigma_k_src_assoc, Category.assoc, Category.assoc, sigma_k_src, ← P.tgt.naturality,
        restrictFstQ_k_assoc]
    · rw [Category.assoc, Category.assoc, restrictFstQ_k_assoc, P.tgt.naturality,
        sigma_k_tgt_assoc, Category.assoc, Category.assoc, sigma_k_tgt, ← P.src.naturality,
        restrictFstQ_k_assoc]
  refine d.restrict_hom_ext hk₁ e ?_ ?_
  · rw [Category.assoc, ← restrictFstQ_f₂ hk₁ e hk₂ s, ← Category.assoc, hQ, Category.assoc, h,
      restrictFstQ_f₁]
  · rw [Category.assoc, (s.restrict hk₁ hk₂ e).f₂_p, sigma_k_tgt,
      (d.restrict hk₁ e).isPullback_f₁.w]

/-- The morphism of composable pairs of the relations induced by the base change to a later
stage. -/
noncomputable def tauMap (s : d.Second f₂') :
    pullback (s.restrict hk₁ hk₂ e).f₂ (d.restrict hk₁ e).f₁ ⟶ pullback s.f₂ d.f₁ :=
  pullback.map _ _ _ _ (d.restrictFstQ hk₁ e) (d.restrictFstQ hk₁ e) (d.restrictFstM hk₁ e)
    (restrictFstQ_f₂ hk₁ e hk₂ s).symm (restrictFstQ_f₁ d hk₁ e).symm

include hk₂ in
omit [IsCofiltered I] in
/-- **The composition identity passes to a later stage** as soon as it holds after base
change. -/
theorem tau_f₂_restrict (s : d.Second f₂')
    (h : d.tauMap hk₁ hk₂ e s ≫ d.tau s ≫ s.f₂ = d.tauMap hk₁ hk₂ e s ≫ pullback.snd _ _ ≫ s.f₂) :
    (d.restrict hk₁ e).tau (s.restrict hk₁ hk₂ e) ≫ (s.restrict hk₁ hk₂ e).f₂ =
      pullback.snd _ _ ≫ (s.restrict hk₁ hk₂ e).f₂ := by
  have hfst : d.tauMap hk₁ hk₂ e s ≫ pullback.fst s.f₂ d.f₁ =
      pullback.fst _ _ ≫ d.restrictFstQ hk₁ e := pullback.lift_fst _ _ _
  have hsnd : d.tauMap hk₁ hk₂ e s ≫ pullback.snd s.f₂ d.f₁ =
      pullback.snd _ _ ≫ d.restrictFstQ hk₁ e := pullback.lift_snd _ _ _
  have hQ : (d.restrict hk₁ e).tau (s.restrict hk₁ hk₂ e) ≫ d.restrictFstQ hk₁ e =
      d.tauMap hk₁ hk₂ e s ≫ d.tau s := by
    refine P.hom_ext_of_isPullback_src j d.isPullback_f₁ ?_ ?_ ?_
    · rw [Category.assoc, restrictFstQ_f₁, tau_f₁_assoc, Category.assoc, tau_f₁,
        reassoc_of% hfst, restrictFstQ_f₁]
    · rw [Category.assoc, Category.assoc, restrictFstQ_k_assoc, P.src.naturality,
        tau_k_src_assoc, Category.assoc, Category.assoc, tau_k_src, reassoc_of% hfst,
        restrictFstQ_k_assoc, P.src.naturality]
    · rw [Category.assoc, Category.assoc, restrictFstQ_k_assoc, P.tgt.naturality,
        tau_k_tgt_assoc, Category.assoc, Category.assoc, tau_k_tgt, reassoc_of% hsnd,
        restrictFstQ_k_assoc, P.tgt.naturality]
  refine d.restrict_hom_ext hk₁ e ?_ ?_
  · rw [Category.assoc, ← restrictFstQ_f₂ hk₁ e hk₂ s, ← Category.assoc, hQ, Category.assoc, h,
      ← Category.assoc, hsnd, Category.assoc, Category.assoc, restrictFstQ_f₂ hk₁ e hk₂ s]
  · rw [Category.assoc, (s.restrict hk₁ hk₂ e).f₂_p, tau_k_tgt, Category.assoc,
      (s.restrict hk₁ hk₂ e).f₂_p]

end Persistence

section Eventually

variable (hk₁ : f₁' ≫ w' = k' ≫ P.srcLim) (hk₂ : f₂' ≫ w' = k' ≫ P.tgtLim)

include hk₁ in
omit [IsCofiltered I] in
/-- The relation at the limit and the relation of a model have the same first projection to the
stage atlas. -/
@[reassoc]
theorem mQ_k_src : d.mQ ≫ d.k ≫ P.src.app j = f₁' ≫ w' ≫ P.atlasCone.π.app j := by
  rw [← Category.assoc, d.isPullback_mQ.w, Category.assoc, ← P.srcLim_π, ← Category.assoc, ← hk₁,
    Category.assoc]

include hk₂ in
omit [IsCofiltered I] in
/-- The relation at the limit and the relation of a model have the same second projection to the
stage atlas. -/
@[reassoc]
theorem mQ_k_tgt : d.mQ ≫ d.k ≫ P.tgt.app j = f₂' ≫ w' ≫ P.atlasCone.π.app j := by
  rw [← Category.assoc, d.isPullback_mQ.w, Category.assoc, ← P.tgtLim_π, ← Category.assoc, ← hk₂,
    Category.assoc]

include hk₁ hk₂ in
/-- **The diagonal identity holds at a later stage** when it holds at the limit (Stacks 01ZC). -/
theorem exists_rho_f₂ (s : d.Second f₂') (ρ' : W' ⟶ Q') (hρ₁ : ρ' ≫ f₁' = 𝟙 _)
    (hρ₂ : ρ' ≫ f₂' = 𝟙 _) :
    ∃ (j' : I) (e : j' ⟶ j), d.restrictFstM hk₁ e ≫ d.rho ≫ s.f₂ = d.restrictFstM hk₁ e := by
  have hmρ : d.m ≫ d.rho = ρ' ≫ d.mQ := by
    refine P.hom_ext_of_isPullback_src j d.isPullback_f₁ ?_ ?_ ?_
    · rw [Category.assoc, rho_f₁, Category.comp_id, Category.assoc, d.mQ_f₁, reassoc_of% hρ₁]
    · rw [Category.assoc, Category.assoc, rho_k_src, d.isPullback_m.w, Category.assoc,
        Category.assoc, d.mQ_k_src hk₁, reassoc_of% hρ₁]
    · rw [Category.assoc, Category.assoc, rho_k_tgt, d.isPullback_m.w, Category.assoc,
        Category.assoc, d.mQ_k_tgt hk₂, reassoc_of% hρ₂]
  have := d.etale_p
  obtain ⟨j', e, H⟩ := exists_stage_eq_of_isPullback P.atlas P.isAffineHom_atlas
    P.compactSpace_atlas_obj
    P.quasiSeparatedSpace_atlas P.isLimit_atlasCone d.p d.compactSpace_M d.p inferInstance
    (d.rho ≫ s.f₂) (𝟙 _) (by rw [Category.assoc, s.f₂_p, rho_k_tgt]) (Category.id_comp _)
    d.isPullback_m (by rw [reassoc_of% hmρ, s.mQ_f₂, reassoc_of% hρ₂, Category.comp_id])
  exact ⟨j', e, (H (IsPullback.of_hasPullback d.p (P.atlas.map e))).trans (Category.comp_id _)⟩

include hk₁ hk₂ in
/-- **The symmetry identity holds at a later stage** when it holds at the limit (Stacks 01ZC). -/
theorem exists_sigma_f₂ (s : d.Second f₂') (σ' : Q' ⟶ Q') (hσ₁ : σ' ≫ f₁' = f₂')
    (hσ₂ : σ' ≫ f₂' = f₁') :
    ∃ (j' : I) (e : j' ⟶ j),
      d.restrictFstQ hk₁ e ≫ d.sigma s ≫ s.f₂ = d.restrictFstQ hk₁ e ≫ d.f₁ := by
  have hmσ : d.mQ ≫ d.sigma s = σ' ≫ d.mQ := by
    refine P.hom_ext_of_isPullback_src j d.isPullback_f₁ ?_ ?_ ?_
    · rw [Category.assoc, sigma_f₁, s.mQ_f₂, Category.assoc, d.mQ_f₁, reassoc_of% hσ₁]
    · rw [Category.assoc, Category.assoc, sigma_k_src, d.mQ_k_tgt hk₂, Category.assoc,
        Category.assoc, d.mQ_k_src hk₁, reassoc_of% hσ₁]
    · rw [Category.assoc, Category.assoc, sigma_k_tgt, d.mQ_k_src hk₁, Category.assoc,
        Category.assoc, d.mQ_k_tgt hk₂, reassoc_of% hσ₂]
  have := d.etale_k
  let u : d.Q ⟶ d.Q := d.isPullback_f₁.lift (d.sigma s ≫ s.f₂) d.k (by
    rw [Category.assoc, s.f₂_p, sigma_k_tgt])
  have hu₁ : u ≫ d.f₁ = d.sigma s ≫ s.f₂ := IsPullback.lift_fst _ _ _ _
  have hu₂ : u ≫ d.k = d.k := IsPullback.lift_snd _ _ _ _
  obtain ⟨j', e, H⟩ := exists_stage_eq_of_isPullback P.relation P.isAffineHom_relation
    P.compactSpace_relation_obj
    P.quasiSeparatedSpace_relation P.isLimit_relationCone d.k d.compactSpace_Q d.k inferInstance
    u (𝟙 _) hu₂ (Category.id_comp _) d.isPullback_mQ (by
      refine d.isPullback_f₁.hom_ext ?_ ?_
      · rw [Category.assoc, hu₁, reassoc_of% hmσ, s.mQ_f₂, reassoc_of% hσ₂, Category.comp_id,
          d.mQ_f₁]
      · rw [Category.assoc, hu₂, Category.comp_id])
  refine ⟨j', e, ?_⟩
  have h' : d.restrictFstQ hk₁ e ≫ u = d.restrictFstQ hk₁ e ≫ 𝟙 _ :=
    H (IsPullback.of_hasPullback d.k (P.relation.map e))
  rw [Category.comp_id] at h'
  rw [← hu₁, ← Category.assoc, h']

include hk₁ in
omit [IsCofiltered I] in
/-- The relation of a model at the limit is the base change of its relation along the first
projection. -/
theorem isPullback_mQ_f₁ [IsCofiltered I] (hc : IsLimit c)
    (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) : IsPullback d.mQ f₁' d.f₁ d.m := by
  refine IsPullback.of_bot ?_ d.mQ_f₁ d.isPullback_m
  rw [hk₁, d.isPullback_f₁.w]
  exact d.isPullback_mQ.paste_vert (P.isPullback_src_relationCone hc hD j)

include hk₁ in
omit [IsCofiltered I] in
/-- The relation of a model at a later stage is the base change of its relation along the first
projection. -/
theorem isPullback_restrictFstQ_f₁ {j' : I} (e : j' ⟶ j) :
    IsPullback (d.restrictFstQ hk₁ e) (d.restrict hk₁ e).f₁ d.f₁ (d.restrictFstM hk₁ e) := by
  refine IsPullback.of_bot ?_ (restrictFstQ_f₁ d hk₁ e) (IsPullback.of_hasPullback _ _)
  have h := (IsPullback.of_hasPullback d.k (P.relation.map e)).paste_vert
    (P.isPullback_src_relation_map e)
  have e₁ : (d.restrict hk₁ e).f₁ ≫ (d.restrict hk₁ e).p =
      pullback.snd d.k (P.relation.map e) ≫ P.src.app j' := (d.restrict hk₁ e).isPullback_f₁.w
  have e₂ : d.f₁ ≫ d.p = d.k ≫ P.src.app j := d.isPullback_f₁.w
  exact (congrArg (fun z => IsPullback (d.restrictFstQ hk₁ e) z (d.f₁ ≫ d.p) (P.atlas.map e))
    e₁).mpr ((congrArg (fun z => IsPullback (d.restrictFstQ hk₁ e)
      (pullback.snd d.k (P.relation.map e) ≫ P.src.app j') z (P.atlas.map e)) e₂).mpr h)

include hk₁ hk₂ in
omit [IsCofiltered I] in
/-- **The composition identity holds at a later stage** when it holds at the limit
(Stacks 01ZC). -/
theorem exists_tau_f₂ [IsCofiltered I] (hc : IsLimit c)
    (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) (s : d.Second f₂')
    (τ' : pullback f₂' f₁' ⟶ Q') (hτ₁ : τ' ≫ f₁' = pullback.fst _ _ ≫ f₁')
    (hτ₂ : τ' ≫ f₂' = pullback.snd _ _ ≫ f₂') :
    ∃ (j' : I) (e : j' ⟶ j), d.tauMap hk₁ hk₂ e s ≫ d.tau s ≫ s.f₂ =
      d.tauMap hk₁ hk₂ e s ≫ pullback.snd _ _ ≫ s.f₂ := by
  let T := BigFppfOver.toScheme B S hS
  have H₁ := d.isPullback_mQ_f₁ hk₁ hc hD
  let a := pullback.map f₂' f₁' s.f₂ d.f₁ d.mQ d.mQ d.m s.mQ_f₂.symm H₁.w.symm
  have hP := isPullback_pullbackMap_of_isPullback H₁ s.mQ_f₂ d.isPullback_m
  have ha₁ : a ≫ pullback.fst s.f₂ d.f₁ = pullback.fst _ _ ≫ d.mQ := pullback.lift_fst _ _ _
  have ha₂ : a ≫ pullback.snd s.f₂ d.f₁ = pullback.snd _ _ ≫ d.mQ := pullback.lift_snd _ _ _
  have hτ : a ≫ d.tau s = τ' ≫ d.mQ := by
    refine P.hom_ext_of_isPullback_src j d.isPullback_f₁ ?_ ?_ ?_
    · rw [Category.assoc, tau_f₁, reassoc_of% ha₁, Category.assoc, d.mQ_f₁, reassoc_of% hτ₁]
    · rw [Category.assoc, Category.assoc, tau_k_src, reassoc_of% ha₁, d.mQ_k_src hk₁,
        Category.assoc, Category.assoc, d.mQ_k_src hk₁, reassoc_of% hτ₁]
    · rw [Category.assoc, Category.assoc, tau_k_tgt, reassoc_of% ha₂, d.mQ_k_tgt hk₂,
        Category.assoc, Category.assoc, d.mQ_k_tgt hk₂, reassoc_of% hτ₂]
  -- the target of the comparison: pairs of a point of the relation and of the model over it
  let Y := pullback (d.k ≫ P.tgt.app j) d.p
  let y : Y ⟶ P.atlas.obj j := pullback.fst _ _ ≫ d.k ≫ P.src.app j
  let u : pullback s.f₂ d.f₁ ⟶ Y := pullback.lift (d.tau s) (d.tau s ≫ s.f₂) (by
    simp only [Category.assoc, s.f₂_p])
  let v : pullback s.f₂ d.f₁ ⟶ Y := pullback.lift (d.tau s) (pullback.snd _ _ ≫ s.f₂) (by
    simp only [Category.assoc, tau_k_tgt, s.f₂_p])
  have hx : pullback.fst s.f₂ d.f₁ ≫ d.f₁ ≫ d.p = d.tau s ≫ d.k ≫ P.src.app j := by
    rw [tau_k_src, d.isPullback_f₁.w]
  have hu : u ≫ y = pullback.fst s.f₂ d.f₁ ≫ d.f₁ ≫ d.p := by
    rw [hx]; exact pullback.lift_fst_assoc _ _ _ _
  have hv : v ≫ y = pullback.fst s.f₂ d.f₁ ≫ d.f₁ ≫ d.p := by
    rw [hx]; exact pullback.lift_fst_assoc _ _ _ _
  -- finiteness properties
  have := P.compactSpace_atlas_obj j
  have := P.compactSpace_relation_obj j
  have := P.quasiSeparatedSpace_atlas j
  have := d.etale_p
  have := d.etale_k
  have := P.etale_src j
  have hf₁ : QuasiCompact (T.map d.f₁) :=
    MorphismProperty.of_isPullback (d.isPullback_f₁.flip.map T) inferInstance
  have hfst : QuasiCompact (T.map (pullback.fst s.f₂ d.f₁)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback s.f₂ d.f₁).flip.map T) hf₁
  have := d.compactSpace_Q
  have hX : CompactSpace (T.obj (pullback s.f₂ d.f₁)) :=
    QuasiCompact.compactSpace_of_compactSpace (T.map (pullback.fst s.f₂ d.f₁))
  have hYfst : Etale (T.map (pullback.fst (d.k ≫ P.tgt.app j) d.p)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback (d.k ≫ P.tgt.app j) d.p).flip.map T)
      inferInstance
  have hy : LocallyOfFiniteType (T.map y) := by
    simp only [y, T.map_comp]
    infer_instance
  obtain ⟨j', e, H⟩ := exists_stage_eq_of_isPullback P.atlas P.isAffineHom_atlas
    P.compactSpace_atlas_obj P.quasiSeparatedSpace_atlas P.isLimit_atlasCone
    (pullback.fst s.f₂ d.f₁ ≫ d.f₁ ≫ d.p) hX y hy
    u v hu hv hP (by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, reassoc_of% hτ,
          reassoc_of% ha₂]
        simp only [s.mQ_f₂, reassoc_of% hτ₂])
  refine ⟨j', e, ?_⟩
  have h' := H (isPullback_pullbackMap_of_isPullback
    (d.isPullback_restrictFstQ_f₁ hk₁ e)
    (restrictFstQ_f₂ hk₁ e hk₂ s) (IsPullback.of_hasPullback d.p (P.atlas.map e)))
  have h'' := congrArg (· ≫ pullback.snd (d.k ≫ P.tgt.app j) d.p) h'
  simp only [Category.assoc, u, v, pullback.lift_snd] at h''
  exact h''

end Eventually

section Cartesian

variable {j : I} {d : EtaleStage P w' f₁' k' j}

omit [IsCofiltered I] in
/-- The symmetry of a stage kernel pair is an involution. -/
@[reassoc (attr := simp)]
theorem _root_.AlgebraicGeometry.Space.LimitPresentation.symmRel_symmRel (j : I) :
    P.symmRel j ≫ P.symmRel j = 𝟙 _ :=
  P.relation_hom_ext j (by simp) (by simp)

omit [IsCofiltered I] in
/-- The symmetry of the relation of a model is an involution once its symmetry identity holds. -/
theorem sigma_sigma (s : d.Second f₂') (h : d.sigma s ≫ s.f₂ = d.f₁) :
    d.sigma s ≫ d.sigma s = 𝟙 _ := by
  refine P.hom_ext_of_isPullback_src j d.isPullback_f₁ ?_ ?_ ?_
  · rw [Category.assoc, sigma_f₁, h, Category.id_comp]
  · rw [Category.assoc, Category.assoc, sigma_k_src, sigma_k_tgt, Category.id_comp]
  · rw [Category.assoc, Category.assoc, sigma_k_tgt, sigma_k_src, Category.id_comp]

omit [IsCofiltered I] in
/-- **The relation of a model is cartesian over the second projection too**, once its symmetry
identity holds. -/
theorem isPullback_f₂ (s : d.Second f₂') (h : d.sigma s ≫ s.f₂ = d.f₁) :
    IsPullback s.f₂ d.k d.p (P.tgt.app j) :=
  d.isPullback_f₁.of_iso
    ⟨d.sigma s, d.sigma s, sigma_sigma s h, sigma_sigma s h⟩ (Iso.refl _)
    ⟨P.symmRel j, P.symmRel j, P.symmRel_symmRel j, P.symmRel_symmRel j⟩ (Iso.refl _)
    (by simp [h]) (by simp [sigma_k]) (by simp) (by simp)

end Cartesian

end EtaleStage

include P in
omit [IsCofiltered I] in
/-- The kernel pair, at the limit, of the base change `W'` of an étale morphism `W ⟶ U` to the
limit atlas `V`: its first projection, and its morphism to the limit kernel pair `R`, present it
as `W' ×_V R`. -/
theorem isPullback_limitRelation [IsCofiltered I] (hc : IsLimit c)
    (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (w : W ⟶ c.pt) {W' : BigFppfOver B S hS} (w' : W' ⟶ P.atlasCone.pt) (g : yoneda.obj W' ⟶ W)
    (hg : IsPullback g (yoneda.map w') w P.limitAtlas) (f₂' : pullback w' P.srcLim ⟶ W')
    (hf₂g : yoneda.map f₂' ≫ g = yoneda.map (pullback.fst w' P.srcLim) ≫ g)
    (hk₂ : f₂' ≫ w' = pullback.snd w' P.srcLim ≫ P.tgtLim) :
    IsPullback (yoneda.map (pullback.fst w' P.srcLim)) (yoneda.map f₂') g g := by
  have hR := P.isPullback_limitKernel hc hD
  have hQ := (IsPullback.of_hasPullback w' P.srcLim).map yoneda
  have hcomp : ∀ {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x y : T ⟶ yoneda.obj W')
      (_ : x ≫ g = y ≫ g),
      (x ≫ yoneda.map w') ≫ P.limitAtlas = (y ≫ yoneda.map w') ≫ P.limitAtlas := by
    intro T x y hxy
    rw [Category.assoc, Category.assoc, ← hg.w, ← Category.assoc, hxy, Category.assoc]
  refine IsPullback.of_isLimit' ⟨hf₂g.symm⟩ (PullbackCone.IsLimit.mk _
    (fun s => hQ.lift s.fst (hR.lift (s.fst ≫ yoneda.map w') (s.snd ≫ yoneda.map w')
      (hcomp _ _ s.condition)) (hR.lift_fst _ _ _).symm)
    (fun s => hQ.lift_fst _ _ _) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · refine hg.hom_ext ?_ ?_
    · rw [Category.assoc, hf₂g, ← Category.assoc, hQ.lift_fst, s.condition]
    · rw [Category.assoc, ← Functor.map_comp, hk₂, Functor.map_comp, ← Category.assoc,
        hQ.lift_snd, hR.lift_snd]
  · refine hQ.hom_ext ?_ (hR.hom_ext ?_ ?_)
    · rw [hQ.lift_fst]; exact hm₁
    · rw [hQ.lift_snd, hR.lift_fst, Category.assoc, ← hQ.w, ← Category.assoc, hm₁]
    · rw [hQ.lift_snd, hR.lift_snd, Category.assoc, ← Functor.map_comp, ← hk₂,
        Functor.map_comp, ← Category.assoc, hm₂]

variable {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : W ⟶ c.pt) {W' : BigFppfOver B S hS}
  (w' : W' ⟶ P.atlasCone.pt) (g : yoneda.obj W' ⟶ W)

/-- A model at the stage `j` of a morphism `w : W ⟶ U` to the limit of a presented system, given
together with the base change `w' : W' ⟶ V` of `w` to the limit atlas: an étale morphism
`w₀ : W₀ ⟶ U_j` whose base change to `U` is `w`, a surjective étale atlas `M` of `W₀` lying
over the stage atlas `V_j`, with `W' = M ×_{V_j} V`, the kernel pair `Q` of that atlas, cartesian
over both projections of the stage kernel pair `R_j`, and the kernel pair `Q'` of the atlas
`W' ⟶ W` with its morphism to `Q`. -/
structure EtaleStageModel (j : I) where
  /-- The model of `W`. -/
  W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  isAlgebraicSpace : IsAlgebraicSpace B S hS W₀
  /-- The étale morphism to the stage. -/
  w₀ : W₀ ⟶ D.obj j
  isEtale_w₀ : IsEtale B S hS w₀
  /-- The projection from `W`. -/
  v : W ⟶ W₀
  isPullback_v : IsPullback v w w₀ (c.π.app j)
  /-- The atlas of the model. -/
  M : BigFppfOver B S hS
  /-- The kernel pair of the atlas of the model. -/
  Q : BigFppfOver B S hS
  /-- The atlas lies over the stage atlas. -/
  p : M ⟶ P.atlas.obj j
  /-- The projection from `W'`. -/
  m : W' ⟶ M
  /-- The atlas morphism. -/
  q : yoneda.obj M ⟶ W₀
  /-- The first projection of the kernel pair. -/
  f₁ : Q ⟶ M
  /-- The second projection of the kernel pair. -/
  f₂ : Q ⟶ M
  /-- The kernel pair lies over the stage kernel pair. -/
  k : Q ⟶ P.relation.obj j
  /-- The morphism to the stage atlas is étale. -/
  etale_p : Etale ((BigFppfOver.toScheme B S hS).map p)
  /-- The morphism to the stage atlas is quasi-compact. -/
  quasiCompact_p : QuasiCompact ((BigFppfOver.toScheme B S hS).map p)
  /-- The morphism to the stage atlas is quasi-separated. -/
  quasiSeparated_p : QuasiSeparated ((BigFppfOver.toScheme B S hS).map p)
  isPullback_m : IsPullback m w' p (P.atlasCone.π.app j)
  m_q : yoneda.map m ≫ q = g ≫ v
  /-- The atlas morphism is surjective. -/
  surjective_q : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf q
  /-- The atlas morphism is étale. -/
  etale_q : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf q
  isPullback_q : IsPullback (yoneda.map f₁) (yoneda.map f₂) q q
  isPullback_w₀ : IsPullback q (yoneda.map p) w₀ (P.atlasMap.app j)
  isPullback_f₁ : IsPullback f₁ k p (P.src.app j)
  isPullback_f₂ : IsPullback f₂ k p (P.tgt.app j)
  /-- The kernel pair of `W' ⟶ W`. -/
  Q' : BigFppfOver B S hS
  /-- Its first projection. -/
  f₁' : Q' ⟶ W'
  /-- Its second projection. -/
  f₂' : Q' ⟶ W'
  /-- Its morphism to the limit kernel pair. -/
  k' : Q' ⟶ P.relationCone.pt
  /-- Its morphism to the kernel pair of the model. -/
  mQ : Q' ⟶ Q
  isPullback_g : IsPullback (yoneda.map f₁') (yoneda.map f₂') g g
  f₁'_w' : f₁' ≫ w' = k' ≫ P.srcLim
  f₂'_w' : f₂' ≫ w' = k' ≫ P.tgtLim
  isPullback_mQ : IsPullback mQ k' k (P.relationCone.π.app j)
  mQ_f₁ : mQ ≫ f₁ = f₁' ≫ m
  mQ_f₂ : mQ ≫ f₂ = f₂' ≫ m

variable {w w' g}

include P in
omit [IsCofiltered I] in
/-- **An étale morphism to the limit of a presented system descends to a stage.** Let
`U = lim U_i` be presented by systems of étale atlases `V_i` and of their kernel pairs `R_i`,
with the limits realised in the site, let `W ⟶ U` be a morphism of algebraic spaces, and
suppose that its base change `W' = W ×_U V` to the limit atlas is an étale, quasi-compact and
quasi-separated morphism of objects of the site. Then `W ⟶ U` has a model at some stage
(`AlgebraicGeometry.Space.LimitPresentation.EtaleStageModel`): an étale morphism
`W₀ ⟶ U_j` of algebraic spaces whose base change to `U` is `W ⟶ U`, with an étale atlas
lying over the stage atlas `V_j` whose kernel pair is cartesian over that of `V_j`. -/
theorem exists_etaleStageModel [IsCofiltered I] (hc : IsLimit c)
    (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) (hU : IsAlgebraicSpace B S hS c.pt)
    (hW : IsAlgebraicSpace B S hS W)
    (hg : IsPullback g (yoneda.map w') w P.limitAtlas)
    (het : Etale ((BigFppfOver.toScheme B S hS).map w'))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map w'))
    (hqs : QuasiSeparated ((BigFppfOver.toScheme B S hS).map w')) :
    ∃ j, Nonempty (P.EtaleStageModel w w' g j) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  have hR := P.isPullback_limitKernel hc hD
  have : Nonempty I := IsCofiltered.nonempty
  -- the kernel pair of `W'` over `W`, at the limit
  let f₁' := pullback.fst w' P.srcLim
  let k' := pullback.snd w' P.srcLim
  have hk₁ : f₁' ≫ w' = k' ≫ P.srcLim := pullback.condition
  have hQ'₁ : IsPullback f₁' k' w' P.srcLim := IsPullback.of_hasPullback _ _
  let f₂' : pullback w' P.srcLim ⟶ W' := yoneda.preimage (hg.lift (yoneda.map f₁' ≫ g)
    (yoneda.map (k' ≫ P.tgtLim)) (by
      rw [Category.assoc, hg.w, ← Category.assoc, ← Functor.map_comp, hk₁, Functor.map_comp,
        Category.assoc, hR.w, Functor.map_comp, Category.assoc]))
  have hf₂g : yoneda.map f₂' ≫ g = yoneda.map f₁' ≫ g := by
    simp only [f₂', Functor.map_preimage, IsPullback.lift_fst]
  have hk₂ : f₂' ≫ w' = k' ≫ P.tgtLim := yoneda.map_injective (by
    simp only [f₂', Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd])
  have hker' := P.isPullback_limitRelation hc hD w w' g hg f₂' hf₂g hk₂
  -- morphisms into the kernel pair of `W'` over `W` with prescribed projections
  have hlift : ∀ {Z : BigFppfOver B S hS} (x y : Z ⟶ W') (h : yoneda.map x ≫ g = yoneda.map y ≫ g),
      ∃ z : Z ⟶ pullback w' P.srcLim, z ≫ f₁' = x ∧ z ≫ f₂' = y := fun x y h =>
    ⟨yoneda.preimage (hker'.lift (yoneda.map x) (yoneda.map y) h),
      yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_preimage]
        exact hker'.lift_fst _ _ _),
      yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_preimage]
        exact hker'.lift_snd _ _ _)⟩
  obtain ⟨ρ', hρ₁, hρ₂⟩ := hlift (𝟙 _) (𝟙 _) rfl
  obtain ⟨σ', hσ₁, hσ₂⟩ := hlift f₂' f₁' hf₂g
  obtain ⟨τ', hτ₁, hτ₂⟩ := hlift (pullback.fst f₂' f₁' ≫ f₁') (pullback.snd f₂' f₁' ≫ f₂') (by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← hf₂g,
      ← Category.assoc, ← Functor.map_comp, pullback.condition, Functor.map_comp,
      Category.assoc, hf₂g])
  -- a model of `W'` at a stage
  obtain ⟨i₀, M₀, p₀, m₀, hp₀e, hp₀c, hp₀s, hpb₀⟩ := exists_etale_siteModel P.atlas
    P.isAffineHom_atlas P.compactSpace_atlas_obj P.quasiSeparatedSpace_atlas P.isLimit_atlasCone
    w' het hqc hqs
  let d₀ : EtaleStage P w' f₁' k' i₀ :=
    { M := M₀
      p := p₀
      m := m₀
      isPullback_m := hpb₀
      etale_p := hp₀e
      quasiCompact_p := hp₀c
      quasiSeparated_p := hp₀s
      Q := pullback p₀ (P.src.app i₀)
      k := pullback.snd _ _
      f₁ := pullback.fst _ _
      isPullback_f₁ := IsPullback.of_hasPullback _ _
      mQ := pullback.lift (f₁' ≫ m₀) (k' ≫ P.relationCone.π.app i₀) (by
        rw [Category.assoc, hpb₀.w, ← Category.assoc, hk₁, Category.assoc, P.srcLim_π,
          Category.assoc])
      isPullback_mQ := by
        refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
        rw [pullback.lift_fst, ← P.srcLim_π]
        exact hQ'₁.paste_horiz hpb₀
      mQ_f₁ := pullback.lift_fst _ _ _ }
  -- the second projection at a stage (Stacks 01ZC)
  have := hp₀e
  have := P.quasiSeparatedSpace_relation i₀
  have hkqs : QuasiSeparated (T.map d₀.k) :=
    MorphismProperty.of_isPullback (d₀.isPullback_f₁.map T) hp₀s
  have hQ₀qs : QuasiSeparatedSpace (T.obj d₀.Q) :=
    quasiSeparatedSpace_of_quasiSeparated (T.map d₀.k)
  have hYlfp : LocallyOfFinitePresentation (T.map (pullback.snd p₀ (P.tgt.app i₀))) :=
    have : Etale (T.map (pullback.snd p₀ (P.tgt.app i₀))) :=
      MorphismProperty.of_isPullback ((IsPullback.of_hasPullback p₀ (P.tgt.app i₀)).map T) hp₀e
    inferInstance
  let a₂ : pullback w' P.srcLim ⟶ pullback p₀ (P.tgt.app i₀) :=
    pullback.lift (f₂' ≫ m₀) (k' ≫ P.relationCone.π.app i₀) (by
      rw [Category.assoc, hpb₀.w, ← Category.assoc, hk₂, Category.assoc, P.tgtLim_π,
        Category.assoc])
  obtain ⟨i₁, e₁, H₁⟩ := exists_stage_hom_of_isPullback P.relation P.isAffineHom_relation
    P.compactSpace_relation_obj P.quasiSeparatedSpace_relation P.isLimit_relationCone d₀.k
    d₀.compactSpace_Q hQ₀qs
    (pullback.snd p₀ (P.tgt.app i₀)) hYlfp d₀.isPullback_mQ
    a₂ ((pullback.lift_snd _ _ _).trans d₀.isPullback_mQ.w.symm)
  let d₁ := d₀.restrict hk₁ e₁
  obtain ⟨g₁, hg₁, hg₁'⟩ := H₁ (IsPullback.of_hasPullback d₀.k (P.relation.map e₁))
  have hg₁'' : pullback.lift (f := d₀.k) (g := P.relation.map e₁) d₀.mQ
      (k' ≫ P.relationCone.π.app i₁) (by rw [Category.assoc, P.relationCone.w, d₀.isPullback_mQ.w])
      ≫ g₁ = a₂ := by
    refine Eq.trans ?_ hg₁'
    congr 1
    exact (IsPullback.of_hasPullback d₀.k (P.relation.map e₁)).hom_ext
      ((pullback.lift_fst _ _ _).trans (IsPullback.lift_fst _ _ _ _).symm)
      ((pullback.lift_snd _ _ _).trans (IsPullback.lift_snd _ _ _ _).symm)
  let s₁ : d₁.Second f₂' :=
    { f₂ := show pullback d₀.k (P.relation.map e₁) ⟶ pullback p₀ (P.atlas.map e₁) from
        pullback.lift (g₁ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ P.tgt.app i₁) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc, hg₁, Category.assoc,
            ← Category.assoc, pullback.condition, Category.assoc, P.tgt.naturality,
            Category.assoc])
      f₂_p := pullback.lift_snd _ _ _
      mQ_f₂ := by
        change pullback.lift (f := d₀.k) (g := P.relation.map e₁) d₀.mQ
            (k' ≫ P.relationCone.π.app i₁) _ ≫
          pullback.lift (g₁ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ P.tgt.app i₁) _ =
          f₂' ≫ pullback.lift (f := p₀) (g := P.atlas.map e₁) m₀ (w' ≫ P.atlasCone.π.app i₁) _
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hg₁'',
            pullback.lift_fst, Category.assoc, pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
            ← Category.assoc, pullback.lift_snd, Category.assoc, ← P.tgtLim_π,
            ← Category.assoc, ← hk₂, Category.assoc] }
  -- the three identities at later stages
  obtain ⟨i₂, e₂, H₂⟩ := d₁.exists_rho_f₂ hk₁ hk₂ s₁ ρ' hρ₁ hρ₂
  let d₂ := d₁.restrict hk₁ e₂
  let s₂ := s₁.restrict hk₁ hk₂ e₂
  have hρ₂' : d₂.rho ≫ s₂.f₂ = 𝟙 _ := EtaleStage.rho_f₂_restrict hk₁ hk₂ e₂ s₁ H₂
  obtain ⟨i₃, e₃, H₃⟩ := d₂.exists_sigma_f₂ hk₁ hk₂ s₂ σ' hσ₁ hσ₂
  let d₃ := d₂.restrict hk₁ e₃
  let s₃ := s₂.restrict hk₁ hk₂ e₃
  have hρ₃ : d₃.rho ≫ s₃.f₂ = 𝟙 _ := EtaleStage.rho_f₂_restrict hk₁ hk₂ e₃ s₂ (by
    rw [hρ₂', Category.comp_id])
  have hσ₃ : d₃.sigma s₃ ≫ s₃.f₂ = d₃.f₁ := EtaleStage.sigma_f₂_restrict hk₁ hk₂ e₃ s₂ H₃
  obtain ⟨i₄, e₄, H₄⟩ := d₃.exists_tau_f₂ hk₁ hk₂ hc hD s₃ τ' hτ₁ hτ₂
  let d := d₃.restrict hk₁ e₄
  let s := s₃.restrict hk₁ hk₂ e₄
  have hρ : d.rho ≫ s.f₂ = 𝟙 _ := EtaleStage.rho_f₂_restrict hk₁ hk₂ e₄ s₃ (by
    rw [hρ₃, Category.comp_id])
  have hσ : d.sigma s ≫ s.f₂ = d.f₁ := EtaleStage.sigma_f₂_restrict hk₁ hk₂ e₄ s₃ (by
    rw [hσ₃])
  have hτ : d.tau s ≫ s.f₂ = pullback.snd _ _ ≫ s.f₂ :=
    EtaleStage.tau_f₂_restrict hk₁ hk₂ e₄ s₃ H₄
  -- the quotient
  have h₂ := EtaleStage.isPullback_f₂ s hσ
  obtain ⟨W₀, q, w₀, hW₀, hq_surj, hq_et, hker, hcart, hw₀⟩ :=
    exists_quotient_of_isPullback_relation B S hS (hD i₄)
      (P.etale_atlasMap i₄) (P.isPullback_relation i₄) d.etale_p (d.isPullback_f₁.map yoneda)
      (h₂.map yoneda) ⟨d.rho, d.rho_f₁, hρ⟩ ⟨d.sigma s, EtaleStage.sigma_f₁ s, hσ⟩
      ⟨d.tau s, EtaleStage.tau_f₁ s, hτ⟩
  -- the comparison from `W`
  have hg_surj := presheaf_of_isPullback B S hS hg.flip P.surjective_limitAtlas
  have hg_et := presheaf_of_isPullback B S hS hg.flip P.etale_limitAtlas
  obtain ⟨v, hv, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS hW.isSheaf g hker'
    hg_surj hg_et hW₀.isSheaf (yoneda.map d.m ≫ q) (by
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        ← d.mQ_f₁, ← s.mQ_f₂, Functor.map_comp, Functor.map_comp, Category.assoc,
        Category.assoc, hker.w])
  have hcomm : v ≫ w₀ = w ≫ c.π.app i₄ := by
    refine hom_ext_of_etale_atlas B S hS hW.isSheaf (hD i₄).isSheaf g hg_surj hg_et ?_
    rw [← Category.assoc, hv, Category.assoc, hcart.w, ← Category.assoc, ← Functor.map_comp,
      d.isPullback_m.w, Functor.map_comp, Category.assoc, ← P.limitAtlas_π, ← Category.assoc,
      ← hg.w, Category.assoc]
  have hpb : IsPullback v w w₀ (c.π.app i₄) := by
    refine isPullback_right_of_isPullback_of_surjective_etale B S hS
      (isAlgebraicSpace_yoneda B S hS W') (isAlgebraicSpace_yoneda B S hS P.atlasCone.pt)
      hW hU hW₀ (hD i₄) hcomm hg ?_
      (isSurjective_of_presheafSurjective B S hS _ P.surjective_limitAtlas)
      ((isEtale_iff_presheaf_of_yoneda B S hS _).mpr P.etale_limitAtlas)
    rw [hv, P.limitAtlas_π]
    exact (d.isPullback_m.map yoneda).paste_horiz hcart
  exact ⟨i₄, ⟨W₀, hW₀, w₀, hw₀, v, hpb, d.M, d.Q, d.p, d.m, q, d.f₁, s.f₂, d.k, d.etale_p,
    d.quasiCompact_p, d.quasiSeparated_p, d.isPullback_m, hv.symm, hq_surj, hq_et, hker,
    hcart, d.isPullback_f₁, h₂, _, f₁', f₂', k', d.mQ, hker', hk₁, hk₂, d.isPullback_mQ,
    d.mQ_f₁, s.mQ_f₂⟩⟩

end LimitPresentation

end AlgebraicGeometry.Space

end
