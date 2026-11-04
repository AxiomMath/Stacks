module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleStageDescent

/-!
# The system of base changes of a stage model of an étale morphism

Let `U = lim U_i` be the limit of a cofiltered system of algebraic spaces presented by systems
of étale atlases `V_i` and of their kernel pairs `R_i`, with the limits `V` and `R` realised in
the site, and let `W₀ ⟶ U_{i₀}` be a model at the stage `i₀` of an étale morphism `W ⟶ U`
(`AlgebraicGeometry.Space.LimitPresentation.EtaleStageModel`). The base changes
`W_i = W₀ ×_{U_{i₀}} U_i`, for `i` over `i₀`, form a cofiltered system of algebraic spaces with
limit `W`, presented by the base changes of the atlas `M ⟶ V_{i₀}` of `W₀` and of its kernel
pair.

## Main definitions

* `AlgebraicGeometry.Space.siteBaseChangeSystem`: the system of base changes of an object of
  the site over a stage of a system of objects of the site.

## Main results

* `AlgebraicGeometry.Space.isLimit_siteBaseChangeCone`: the base change of a realised limit is
  a realised limit.
* `AlgebraicGeometry.Space.isPullback_of_kernelPair_of_isPullback`: a relation which is
  cartesian over the kernel pair of an atlas, along a base change of the atlas, is the kernel
  pair of the base-changed atlas.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- **A relation cartesian over a kernel pair along a base change of the atlas is the kernel pair
of the base-changed atlas.** Let `V' = V ×_F F'` be a base change of `a : V ⟶ F`, let `R ⇉ V` be
the kernel pair of `a`, and let `s', t' : R' ⇉ V'` be a relation lying over `R` along `mR`, with
`R' = R ×_V V'` along the first projections and with the same image in `F'`. Then `R' ⇉ V'` is
the kernel pair of `V' ⟶ F'`. -/
theorem isPullback_of_kernelPair_of_isPullback {C : Type*} [Category* C] {V V' F F' R R' : C}
    {a : V ⟶ F} {a' : V' ⟶ F'} {mV : V' ⟶ V} {mF : F' ⟶ F} (hV : IsPullback mV a' a mF)
    {s t : R ⟶ V} (hR : IsPullback s t a a) {s' t' : R' ⟶ V'} {mR : R' ⟶ R}
    (hs : IsPullback mR s' s mV) (ht : mR ≫ t = t' ≫ mV) (hw : s' ≫ a' = t' ≫ a') :
    IsPullback s' t' a' a' := by
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk _
    (fun c => hs.lift (hR.lift (c.fst ≫ mV) (c.snd ≫ mV) (by
      rw [Category.assoc, Category.assoc, hV.w, ← Category.assoc, c.condition,
        Category.assoc])) c.fst (hR.lift_fst _ _ _))
    (fun c => hs.lift_snd _ _ _) (fun c => ?_) (fun c m hm₁ hm₂ => ?_))
  · refine hV.hom_ext ?_ ?_
    · rw [Category.assoc, ← ht, ← Category.assoc, hs.lift_fst, hR.lift_snd]
    · rw [Category.assoc, ← hw, ← Category.assoc, hs.lift_snd, c.condition]
  · refine hs.hom_ext (hR.hom_ext ?_ ?_) ?_
    · rw [hs.lift_fst, hR.lift_fst, Category.assoc, hs.w, ← Category.assoc, hm₁]
    · rw [hs.lift_fst, hR.lift_snd, Category.assoc, ht, ← Category.assoc, hm₂]
    · rw [hs.lift_snd]; exact hm₁

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section BaseChange

variable {J : Type u} [Category.{u} J] (F : J ⥤ BigFppfOver B S hS) (j₀ : J)
  {U₀ : BigFppfOver B S hS} (a₀ : U₀ ⟶ F.obj j₀)

/-- The system of base changes `F j ×_{F j₀} U₀` of an object `U₀` over the stage `F j₀` of a
system `F` in a category with fibre products, indexed by the slice over `j₀`. -/
noncomputable abbrev overStageBaseChange {C : Type*} [Category* C] [HasPullbacks C] {J : Type*}
    [Category* J] (F : J ⥤ C) (j₀ : J) {U₀ : C} (a₀ : U₀ ⟶ F.obj j₀) : Over j₀ ⥤ C where
  obj j := pullback (F.map j.hom) a₀
  map {j k} e := pullback.lift (pullback.fst _ _ ≫ F.map e.left) (pullback.snd _ _) (by
    rw [Category.assoc, ← F.map_comp, Over.w e, pullback.condition])
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp e e' := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Over.comp_left, F.map_comp, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- The transition morphisms of the base changes lie over the transition morphisms of `F`. -/
@[reassoc (attr := simp)]
theorem overStageBaseChange_map_fst {C : Type*} [Category* C] [HasPullbacks C] {J : Type*}
    [Category* J] (F : J ⥤ C) (j₀ : J) {U₀ : C} (a₀ : U₀ ⟶ F.obj j₀) {j k : Over j₀}
    (e : j ⟶ k) :
    (overStageBaseChange F j₀ a₀).map e ≫ pullback.fst (F.map k.hom) a₀ =
      pullback.fst (F.map j.hom) a₀ ≫ F.map e.left :=
  pullback.lift_fst _ _ _

/-- The transition morphisms of the base changes commute with the projections to `U₀`. -/
@[reassoc (attr := simp)]
theorem overStageBaseChange_map_snd {C : Type*} [Category* C] [HasPullbacks C] {J : Type*}
    [Category* J] (F : J ⥤ C) (j₀ : J) {U₀ : C} (a₀ : U₀ ⟶ F.obj j₀) {j k : Over j₀}
    (e : j ⟶ k) :
    (overStageBaseChange F j₀ a₀).map e ≫ pullback.snd (F.map k.hom) a₀ =
      pullback.snd (F.map j.hom) a₀ :=
  pullback.lift_snd _ _ _

/-- The system of base changes of an object of the site over a stage. -/
noncomputable abbrev siteBaseChangeSystem : Over j₀ ⥤ BigFppfOver B S hS :=
  overStageBaseChange F j₀ a₀

variable {F j₀ a₀}

end BaseChange

section Generic

variable {C : Type*} [Category* C] [HasPullbacks C] {J : Type*} [Category* J] {F : J ⥤ C}
  {j₀ : J} {U₀ : C} {a₀ : U₀ ⟶ F.obj j₀}

/-- The cone on the system of base changes induced by a commutative square over the limit. -/
@[reducible, simps]
noncomputable def overStageBaseChangeCone (cS : Cone F) {L : C} (pL : L ⟶ cS.pt)
    (qL : L ⟶ U₀) (hL : pL ≫ cS.π.app j₀ = qL ≫ a₀) : Cone (overStageBaseChange F j₀ a₀) where
  pt := L
  π :=
    { app j := pullback.lift (pL ≫ cS.π.app j.left) qL (by
        change (pL ≫ cS.π.app j.left) ≫ F.map j.hom = qL ≫ a₀
        rw [Category.assoc, cS.w, hL])
      naturality j k e := by
        refine (Category.id_comp _).trans ?_
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, cS.w]
        · simp only [Category.assoc, pullback.lift_snd] }

/-- **Base change commutes with cofiltered limits.** -/
noncomputable def isLimit_overStageBaseChangeCone {J : Type u} [Category.{u} J] [IsCofiltered J]
    {F : J ⥤ C} {j₀ : J} {a₀ : U₀ ⟶ F.obj j₀} {cS : Cone F} (hcS : IsLimit cS) {L : C}
    {pL : L ⟶ cS.pt} {qL : L ⟶ U₀} (h : IsPullback pL qL (cS.π.app j₀) a₀) :
    IsLimit (overStageBaseChangeCone cS pL qL h.w) :=
  isLimitOfCartesianCone F cS hcS j₀ U₀ a₀ _ _
    { app := fun j => pullback.fst (F.map j.hom) a₀
      naturality := fun _ _ e => overStageBaseChange_map_fst F j₀ a₀ e }
    { app := fun j => pullback.snd (F.map j.hom) a₀
      naturality := fun _ _ e => (overStageBaseChange_map_snd F j₀ a₀ e).trans
        (Category.comp_id _).symm }
    (fun j => IsPullback.of_hasPullback (F.map j.hom) a₀) pL qL h
    (fun _ => pullback.lift_fst _ _ _) (fun _ => pullback.lift_snd _ _ _)

/-- The base change of a system to a stage is cartesian over the transition morphisms. -/
theorem isPullback_overStageBaseChange_map {j k : Over j₀} (e : j ⟶ k) :
    IsPullback ((overStageBaseChange F j₀ a₀).map e) (pullback.fst (F.map j.hom) a₀)
      (pullback.fst (F.map k.hom) a₀) (F.map e.left) := by
  refine IsPullback.of_right ?_ (overStageBaseChange_map_fst F j₀ a₀ e)
    (IsPullback.of_hasPullback (F.map k.hom) a₀).flip
  rw [overStageBaseChange_map_snd, ← F.map_comp, Over.w e]
  exact (IsPullback.of_hasPullback (F.map j.hom) a₀).flip

/-- **The base change of an atlas is the base change of the atlas of the target.** Let
`V' = V ×_F F'` and `M = V ×_F W` (along `p`, `w₀`), and let `M' = V' ×_V M`. Then `M'` is the
base change of `M ⟶ W` along the projection `F' ×_F W ⟶ W`. -/
theorem isPullback_baseChange_atlas {V' V M F' F W M' : C} {mV : V' ⟶ V} {aV' : V' ⟶ F'}
    {a : V ⟶ F} {mF : F' ⟶ F} (hV : IsPullback mV aV' a mF) {p : M ⟶ V} {q : M ⟶ W}
    {w₀ : W ⟶ F} (hq : IsPullback q p w₀ a) {fM : M' ⟶ V'} {sM : M' ⟶ M}
    (hM : IsPullback fM sM mV p) :
    IsPullback sM (pullback.lift (fM ≫ aV') (sM ≫ q)
      (by rw [Category.assoc, ← hV.w, ← Category.assoc, hM.w, Category.assoc, Category.assoc,
        hq.w])) q (pullback.snd mF w₀) := by
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
    (IsPullback.of_hasPullback mF w₀).flip
  rw [pullback.lift_fst, hq.w]
  exact hM.flip.paste_vert hV

omit [HasPullbacks C] in
/-- Two base changes of one morphism along compatible morphisms are cartesian over each
other. -/
theorem isPullback_of_isPullback_of_isPullback {M M₁ M₂ D₁ D₂ W : C} {q : M ⟶ W}
    {m₁ : M₁ ⟶ M} {a₁ : M₁ ⟶ D₁} {h₁ : D₁ ⟶ W} (H₁ : IsPullback m₁ a₁ q h₁)
    {m₂ : M₂ ⟶ M} {a₂ : M₂ ⟶ D₂} {h₂ : D₂ ⟶ W} (H₂ : IsPullback m₂ a₂ q h₂)
    {φ : M₁ ⟶ M₂} {ψ : D₁ ⟶ D₂} (hφ : φ ≫ m₂ = m₁) (hψ : ψ ≫ h₂ = h₁)
    (hw : φ ≫ a₂ = a₁ ≫ ψ) : IsPullback φ a₁ a₂ ψ := by
  refine IsPullback.of_right ?_ hw H₂
  rw [hφ, hψ]
  exact H₁

end Generic

section BaseChange

variable {J : Type u} [Category.{u} J] {F : J ⥤ BigFppfOver B S hS} {j₀ : J}
  {U₀ : BigFppfOver B S hS} {a₀ : U₀ ⟶ F.obj j₀}

/-- **The base change of a realised limit is a realised limit.** -/
noncomputable def isLimit_siteBaseChangeCone [IsCofiltered J] {cS : Cone F}
    {L : BigFppfOver B S hS} {pL : L ⟶ cS.pt} {qL : L ⟶ U₀}
    (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cS))
    (h : IsPullback pL qL (cS.π.app j₀) a₀) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (overStageBaseChangeCone cS pL qL h.w)) := by
  let G := BigFppfOver.toScheme B S hS
  let pN : (siteBaseChangeSystem F j₀ a₀ ⋙ G) ⟶ Over.forget j₀ ⋙ (F ⋙ G) :=
    { app := fun j => G.map (pullback.fst (F.map j.hom) a₀)
      naturality := fun j k e => by
        change G.map ((overStageBaseChange F j₀ a₀).map e) ≫ G.map (pullback.fst (F.map k.hom) a₀) =
          G.map (pullback.fst (F.map j.hom) a₀) ≫ G.map (F.map e.left)
        rw [← G.map_comp, ← G.map_comp, overStageBaseChange_map_fst] }
  let qN : (siteBaseChangeSystem F j₀ a₀ ⋙ G) ⟶ (Functor.const (Over j₀)).obj (G.obj U₀) :=
    { app := fun j => G.map (pullback.snd (F.map j.hom) a₀)
      naturality := fun j k e => by
        change G.map ((overStageBaseChange F j₀ a₀).map e) ≫ G.map (pullback.snd (F.map k.hom) a₀) =
          G.map (pullback.snd (F.map j.hom) a₀) ≫ 𝟙 _
        rw [← G.map_comp, overStageBaseChange_map_snd, Category.comp_id] }
  exact isLimitOfCartesianCone (F ⋙ G) (G.mapCone cS) hcS j₀ (G.obj U₀) (G.map a₀) _ _ pN qN
    (fun j => (IsPullback.of_hasPullback (F.map j.hom) a₀).map G) (G.map pL) (G.map qL)
    (h.map G) (fun j => by
      change G.map (pullback.lift (pL ≫ cS.π.app j.left) qL _) ≫ G.map _ = G.map pL ≫ G.map _
      rw [← G.map_comp, ← G.map_comp, pullback.lift_fst])
    (fun j => by
      change G.map (pullback.lift (pL ≫ cS.π.app j.left) qL _) ≫ G.map _ = G.map qL
      rw [← G.map_comp, pullback.lift_snd])

end BaseChange

namespace LimitPresentation

variable {J : Type u} [Category.{u} J] {D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : Cone D}
  {P : LimitPresentation B S hS D c} {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {w : W ⟶ c.pt}
  {W' : BigFppfOver B S hS} {w' : W' ⟶ P.atlasCone.pt} {g : yoneda.obj W' ⟶ W} {j₀ : J}

namespace EtaleStageModel

variable (E : P.EtaleStageModel w w' g j₀)

/-- The atlases of the base changes of a stage model. -/
noncomputable abbrev atlasSystem : Over j₀ ⥤ BigFppfOver B S hS :=
  overStageBaseChange P.atlas j₀ E.p

/-- The kernel pairs of the atlases of the base changes of a stage model. -/
noncomputable abbrev relationSystem : Over j₀ ⥤ BigFppfOver B S hS :=
  overStageBaseChange P.relation j₀ E.k

/-- The first projections of the kernel pairs. -/
@[simps]
noncomputable def srcSystem : E.relationSystem ⟶ E.atlasSystem where
  app j := pullback.map _ _ _ _ (P.src.app j.left) E.f₁ (P.src.app j₀) (P.src.naturality j.hom)
    E.isPullback_f₁.w.symm
  naturality j k e := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, P.src.naturality]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

/-- The second projections of the kernel pairs. -/
@[simps]
noncomputable def tgtSystem : E.relationSystem ⟶ E.atlasSystem where
  app j := pullback.map _ _ _ _ (P.tgt.app j.left) E.f₂ (P.tgt.app j₀) (P.tgt.naturality j.hom)
    E.isPullback_f₂.w.symm
  naturality j k e := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, P.tgt.naturality]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

/-- The base changes of the model. -/
noncomputable abbrev spaceSystem : Over j₀ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  overStageBaseChange D j₀ E.w₀

/-- The atlas morphisms of the base changes. -/
noncomputable def atlasMorphism (j : Over j₀) :
    yoneda.obj (E.atlasSystem.obj j) ⟶ E.spaceSystem.obj j :=
  pullback.lift (yoneda.map (pullback.fst _ _) ≫ P.atlasMap.app j.left)
    (yoneda.map (pullback.snd _ _) ≫ E.q) (by
      have hn := P.atlasMap.naturality j.hom
      simp only [Functor.comp_map] at hn
      rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, pullback.condition,
        Functor.map_comp, Category.assoc, Category.assoc, E.isPullback_w₀.w])

/-- The atlas of the base change at `j` is the base change of the atlas `E.q` of the model along
the projection of the base change to the model. -/
theorem isPullback_atlasMorphism (j : Over j₀) :
    IsPullback (yoneda.map (pullback.snd (P.atlas.map j.hom) E.p)) (E.atlasMorphism j) E.q
      (pullback.snd (D.map j.hom) E.w₀) :=
  isPullback_baseChange_atlas (P.isPullback_atlas j.hom) E.isPullback_w₀
    ((IsPullback.of_hasPullback (P.atlas.map j.hom) E.p).map yoneda)

/-- The base change of a morphism `s₀` along a morphism `p` is a base change of the
base change of `s₀` along `v`, if `s₀` is a base change of `s`. -/
private theorem isPullback_snd_pullback_map {C : Type*} [Category* C] [HasPullbacks C]
    {R R₀ V V₀ K M : C} {r : R ⟶ R₀} {v : V ⟶ V₀} {s : R ⟶ V} {s₀ : R₀ ⟶ V₀} {k : K ⟶ R₀}
    {p : M ⟶ V₀} {f : K ⟶ M} (hs : IsPullback r s s₀ v) (hf : IsPullback f k p s₀) :
    IsPullback (pullback.snd r k) (pullback.map r k v p s f s₀ hs.w hf.w.symm) f
      (pullback.snd v p) := by
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
    (IsPullback.of_hasPullback v p).flip
  rw [pullback.lift_fst, hf.w]
  exact (IsPullback.of_hasPullback r k).flip.paste_vert hs

/-- Composing a lift into a pullback with `pullback.map` is lifting into the pullback. -/
private theorem comp_lift_eq_lift_comp_map {C : Type*} [Category* C] [HasPullbacks C]
    {Q W R V K M R₀ V₀ : C} {v : V ⟶ V₀} {p : M ⟶ V₀} {r : R ⟶ R₀} {k : K ⟶ R₀} {s : R ⟶ V}
    {s₀ : R₀ ⟶ V₀} {f : K ⟶ M} (e₁ : r ≫ s₀ = s ≫ v) (e₂ : k ≫ s₀ = f ≫ p) {x : Q ⟶ W}
    {a : W ⟶ V} {m : W ⟶ M} {b : Q ⟶ R} {c : Q ⟶ K} (ha : a ≫ v = m ≫ p) (hb : b ≫ r = c ≫ k)
    (h₁ : x ≫ a = b ≫ s) (h₂ : c ≫ f = x ≫ m) :
    x ≫ pullback.lift a m ha = pullback.lift b c hb ≫ pullback.map r k v p s f s₀ e₁ e₂ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.map_fst,
      pullback.lift_fst_assoc, h₁]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.map_snd,
      pullback.lift_snd_assoc, h₂]

/-- The kernel pair of a base change of the atlas is the base change of the kernel pair, along
the first projections. -/
theorem isPullback_srcSystem (j : Over j₀) :
    IsPullback (pullback.snd (P.relation.map j.hom) E.k) (E.srcSystem.app j) E.f₁
      (pullback.snd (P.atlas.map j.hom) E.p) :=
  isPullback_snd_pullback_map (P.isPullback_src_relation_map j.hom) E.isPullback_f₁

/-- The kernel pair of a base change of the atlas is the base change of the kernel pair, along
the second projections. -/
theorem isPullback_tgtSystem (j : Over j₀) :
    IsPullback (pullback.snd (P.relation.map j.hom) E.k) (E.tgtSystem.app j) E.f₂
      (pullback.snd (P.atlas.map j.hom) E.p) :=
  isPullback_snd_pullback_map (P.isPullback_tgt_relation_map j.hom) E.isPullback_f₂

/-- The family of base changes of a stage model, with their atlases. -/
@[reducible]
noncomputable def atlasFamily (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j)) :
    AtlasFamily B S hS (Over j₀) where
  V := E.atlasSystem
  R := E.relationSystem
  s := E.srcSystem
  t := E.tgtSystem
  X := E.spaceSystem.obj
  isAlgebraicSpace j := isAlgebraicSpace_pullback B S hS _ _ (hD _) E.isAlgebraicSpace (hD j₀)
  v := E.atlasMorphism
  surjective j := presheaf_of_isPullback B S hS (E.isPullback_atlasMorphism j) E.surjective_q
  etale j := presheaf_of_isPullback B S hS (E.isPullback_atlasMorphism j) E.etale_q
  isPullback j := by
    refine isPullback_of_kernelPair_of_isPullback (E.isPullback_atlasMorphism j) E.isPullback_q
      ((E.isPullback_srcSystem j).map yoneda) (by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg yoneda.map (pullback.lift_snd _ _ _).symm) ?_
    apply pullback.hom_ext
    · simp only [atlasMorphism, Category.assoc, pullback.lift_fst, ← Functor.map_comp_assoc,
        srcSystem_app, tgtSystem_app]
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        (P.isPullback_relation j.left).w]
    · simp only [atlasMorphism, Category.assoc, pullback.lift_snd, ← Functor.map_comp_assoc,
        srcSystem_app, tgtSystem_app]
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, E.isPullback_q.w]

/-- The first projections of the kernel pairs are cartesian over the transition morphisms of the
atlases. -/
theorem hcart {i j : Over j₀} (e : i ⟶ j) :
    IsPullback (E.relationSystem.map e) (E.srcSystem.app i) (E.srcSystem.app j)
      (E.atlasSystem.map e) :=
  isPullback_of_isPullback_of_isPullback (E.isPullback_srcSystem i) (E.isPullback_srcSystem j)
    (overStageBaseChange_map_snd _ _ _ e) (overStageBaseChange_map_snd _ _ _ e)
    (E.srcSystem.naturality e)

/-- The cone of atlases with vertex `W'`. -/
noncomputable abbrev atlasLimitCone : Cone E.atlasSystem :=
  overStageBaseChangeCone P.atlasCone w' E.m E.isPullback_m.w.symm

/-- The cone of kernel pairs with vertex `Q'`. -/
noncomputable abbrev relationLimitCone : Cone E.relationSystem :=
  overStageBaseChangeCone P.relationCone E.k' E.mQ E.isPullback_mQ.w.symm

/-- The limit of the atlases is realised. -/
noncomputable def isLimit_atlasLimitCone [IsCofiltered J] :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone E.atlasLimitCone) :=
  isLimit_siteBaseChangeCone P.isLimit_atlasCone E.isPullback_m.flip

/-- The limit of the kernel pairs is realised. -/
noncomputable def isLimit_relationLimitCone [IsCofiltered J] :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone E.relationLimitCone) :=
  isLimit_siteBaseChangeCone P.isLimit_relationCone E.isPullback_mQ.flip

/-- The limit projections intertwine `E.f₁'` with the first projections of the kernel pairs. -/
theorem srcLim_π (j : Over j₀) :
    E.f₁' ≫ E.atlasLimitCone.π.app j = E.relationLimitCone.π.app j ≫ E.srcSystem.app j := by
  refine comp_lift_eq_lift_comp_map (P.src.naturality j.hom) E.isPullback_f₁.w.symm _ _ ?_
    E.mQ_f₁
  rw [← Category.assoc, E.f₁'_w', Category.assoc, Category.assoc, P.srcLim_π]

/-- The limit projections intertwine `E.f₂'` with the second projections of the kernel pairs. -/
theorem tgtLim_π (j : Over j₀) :
    E.f₂' ≫ E.atlasLimitCone.π.app j = E.relationLimitCone.π.app j ≫ E.tgtSystem.app j := by
  refine comp_lift_eq_lift_comp_map (P.tgt.naturality j.hom) E.isPullback_f₂.w.symm _ _ ?_
    E.mQ_f₂
  rw [← Category.assoc, E.f₂'_w', Category.assoc, Category.assoc, P.tgtLim_π]

section Properties

variable {P' : MorphismProperty Scheme.{u}} [P'.IsStableUnderBaseChange]

/-- If a property stable under base change holds for `E.p`, it holds for the projection of the
atlas of each base change to the atlas of the system. -/
theorem baseChange_atlasSystem_fst (h : P' ((BigFppfOver.toScheme B S hS).map E.p))
    (j : Over j₀) :
    P' ((BigFppfOver.toScheme B S hS).map (pullback.fst (P.atlas.map j.hom) E.p)) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (P.atlas.map j.hom) E.p).flip.map (BigFppfOver.toScheme B S hS)) h

/-- If a property stable under base change holds for `E.p`, it holds for `E.k`. -/
theorem baseChange_k (h : P' ((BigFppfOver.toScheme B S hS).map E.p)) :
    P' ((BigFppfOver.toScheme B S hS).map E.k) :=
  MorphismProperty.of_isPullback (E.isPullback_f₁.map (BigFppfOver.toScheme B S hS)) h

/-- If a property stable under base change holds for `E.p`, it holds for the projection of the
kernel pair of each base change to the kernel pair of the system. -/
theorem baseChange_relationSystem_fst (h : P' ((BigFppfOver.toScheme B S hS).map E.p))
    (j : Over j₀) :
    P' ((BigFppfOver.toScheme B S hS).map (pullback.fst (P.relation.map j.hom) E.k)) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (P.relation.map j.hom) E.k).flip.map
      (BigFppfOver.toScheme B S hS)) (E.baseChange_k h)

end Properties

/-- The atlas of each base change is quasi-compact. -/
theorem compactSpace_atlasSystem (j : Over j₀) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.atlasSystem.obj j)) := by
  have := E.baseChange_atlasSystem_fst E.quasiCompact_p j
  have := compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    (P.isQuasiCompactSpace_atlas j.left)
  exact QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B S hS).map (pullback.fst (P.atlas.map j.hom) E.p))

/-- The atlas of each base change is quasi-separated. -/
theorem quasiSeparatedSpace_atlasSystem (j : Over j₀) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (E.atlasSystem.obj j)) := by
  have := E.baseChange_atlasSystem_fst E.quasiSeparated_p j
  have := P.quasiSeparatedSpace_atlas j.left
  exact quasiSeparatedSpace_of_quasiSeparated
    ((BigFppfOver.toScheme B S hS).map (pullback.fst (P.atlas.map j.hom) E.p))

/-- The kernel pair of the atlas of each base change is quasi-compact. -/
theorem compactSpace_relationSystem (j : Over j₀) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.relationSystem.obj j)) := by
  have := E.baseChange_relationSystem_fst E.quasiCompact_p j
  have := compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    (P.isQuasiCompactSpace_relation j.left)
  exact QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B S hS).map (pullback.fst (P.relation.map j.hom) E.k))

/-- The kernel pair of the atlas of each base change is quasi-separated. -/
theorem quasiSeparatedSpace_relationSystem (j : Over j₀) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (E.relationSystem.obj j)) := by
  have := E.baseChange_relationSystem_fst E.quasiSeparated_p j
  have := P.quasiSeparatedSpace_relation j.left
  exact quasiSeparatedSpace_of_quasiSeparated
    ((BigFppfOver.toScheme B S hS).map (pullback.fst (P.relation.map j.hom) E.k))

/-- The transition morphisms of the atlases of the base changes are affine. -/
theorem isAffineHom_atlasSystem_map {i j : Over j₀} (e : i ⟶ j) :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (E.atlasSystem.map e)) :=
  MorphismProperty.of_isPullback
    ((isPullback_overStageBaseChange_map e).flip.map (BigFppfOver.toScheme B S hS))
    (P.isAffineHom_atlas e.left)

/-- The transition morphisms of the kernel pairs of the base changes are affine. -/
theorem isAffineHom_relationSystem_map {i j : Over j₀} (e : i ⟶ j) :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (E.relationSystem.map e)) :=
  MorphismProperty.of_isPullback
    ((isPullback_overStageBaseChange_map e).flip.map (BigFppfOver.toScheme B S hS))
    (P.isAffineHom_relation e.left)

variable [IsCofiltered J] (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j))
  (hW : IsAlgebraicSpace B S hS W) (hg : IsPullback g (yoneda.map w') w P.limitAtlas)
  (hg_surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf g)
  (hg_et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf g)

/-- The cone with vertex `W` over the base changes of a stage model. -/
noncomputable abbrev cone : Cone (E.atlasFamily hD).diagram :=
  (E.atlasFamily hD).limitCone (cV := E.atlasLimitCone) (cR := E.relationLimitCone) E.f₁' E.f₂'
    E.srcLim_π E.tgtLim_π hW g hg_surj hg_et E.isPullback_g

omit [IsCofiltered J] in
/-- The projection of `W` to the base change at `j`, precomposed with the atlas `g`, is the
projection of `W'` to the atlas at `j` followed by the atlas morphism at `j`. -/
theorem a_cone (j : Over j₀) :
    g ≫ (E.cone hD hW hg_surj hg_et).π.app j =
      yoneda.map (E.atlasLimitCone.π.app j) ≫ E.atlasMorphism j :=
  (E.atlasFamily hD).a_limitProj (cV := E.atlasLimitCone) (cR := E.relationLimitCone) E.f₁' E.f₂'
    E.srcLim_π E.tgtLim_π hW g hg_surj hg_et E.isPullback_g j

omit [IsCofiltered J] in
include hg in
/-- The atlas `W'` of `W` is the base change of the atlas `M` of the model `W₀`. -/
theorem isPullback_m_v : IsPullback (yoneda.map E.m) g E.q E.v := by
  refine IsPullback.of_right ?_ E.m_q E.isPullback_w₀.flip
  rw [← Functor.map_comp, E.isPullback_m.w, Functor.map_comp, E.isPullback_v.w]
  exact hg.flip.paste_horiz (P.isPullback_limitAtlas j₀)

omit [IsCofiltered J] in
/-- The projection of `W` to the base change at `j`, followed by the projection to `W₀`, is
`E.v`. -/
theorem cone_π_snd (j : Over j₀) :
    (E.cone hD hW hg_surj hg_et).π.app j ≫ pullback.snd (D.map j.hom) E.w₀ = E.v := by
  refine hom_ext_of_etale_atlas B S hS hW.isSheaf E.isAlgebraicSpace.isSheaf g hg_surj hg_et ?_
  rw [← Category.assoc, E.a_cone, Category.assoc]
  rw [atlasMorphism, pullback.lift_snd, ← Category.assoc, ← Functor.map_comp, ← E.m_q]
  congr 2
  exact pullback.lift_snd _ _ _

omit [IsCofiltered J] in
include hg in
/-- The projection of `W` to the base change at `j`, followed by the projection to `D.obj j.left`,
is `w ≫ c.π.app j.left`. -/
theorem cone_π_fst (j : Over j₀) :
    (E.cone hD hW hg_surj hg_et).π.app j ≫ pullback.fst (D.map j.hom) E.w₀ =
      w ≫ c.π.app j.left := by
  refine hom_ext_of_etale_atlas B S hS hW.isSheaf (hD _).isSheaf g hg_surj hg_et ?_
  rw [← Category.assoc, E.a_cone, Category.assoc]
  rw [atlasMorphism, pullback.lift_fst, ← Category.assoc, ← Functor.map_comp,
    ← Category.assoc, hg.w]
  show yoneda.map (pullback.lift (w' ≫ P.atlasCone.π.app j.left) E.m _ ≫ pullback.fst _ _) ≫ _ = _
  rw [pullback.lift_fst, Functor.map_comp, Category.assoc, ← P.limitAtlas_π, Category.assoc]

omit [IsCofiltered J] in
include hg in
/-- The atlas `g` of `W` is the base change of the atlas at `j` along the projection of `W` to the
base change at `j`. -/
theorem isPullback_cone (j : Over j₀) :
    IsPullback (yoneda.map (E.atlasLimitCone.π.app j)) g ((E.atlasFamily hD).v j)
      ((E.cone hD hW hg_surj hg_et).π.app j) := by
  refine IsPullback.of_right ?_ (E.a_cone hD hW hg_surj hg_et j).symm
    (E.isPullback_atlasMorphism j)
  rw [← Functor.map_comp, E.cone_π_snd hD hW hg_surj hg_et j]
  show IsPullback (yoneda.map (pullback.lift (w' ≫ P.atlasCone.π.app j.left) E.m _ ≫
    pullback.snd _ _)) g E.q E.v
  rw [pullback.lift_snd]
  exact E.isPullback_m_v hg

omit [IsCofiltered J] in
/-- The transition morphisms of the family of base changes are those of
`overStageBaseChange D j₀ E.w₀`. -/
theorem atlasFamily_map {i j : Over j₀} (e : i ⟶ j) :
    (E.atlasFamily hD).map e = (overStageBaseChange D j₀ E.w₀).map e := by
  refine (E.atlasFamily hD).hom_ext ((E.atlasFamily hD).isAlgebraicSpace j).isSheaf ?_
  rw [AtlasFamily.v_map]
  show yoneda.map ((overStageBaseChange P.atlas j₀ E.p).map e) ≫ E.atlasMorphism j =
    E.atlasMorphism i ≫ (overStageBaseChange D j₀ E.w₀).map e
  apply pullback.hom_ext
  · have hn := P.atlasMap.naturality e.left
    simp only [Functor.comp_map] at hn
    simp only [atlasMorphism, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, ← hn, ← Functor.map_comp_assoc]
  · simp only [atlasMorphism, Category.assoc, pullback.lift_snd, ← Functor.map_comp_assoc]

include hg in
/-- The base changes of a stage model have limit `W`. -/
noncomputable def isLimit_cone (hc : IsLimit c) :
    IsLimit (E.cone hD hW hg_surj hg_et) := by
  let e : (E.atlasFamily hD).diagram ≅ overStageBaseChange D j₀ E.w₀ :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      simp only [E.atlasFamily_map hD, Iso.refl_hom]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have h₁ := isLimit_overStageBaseChangeCone hc (IsPullback.of_hasPullback (c.π.app j₀) E.w₀)
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv e _).symm h₁)
    (Cone.ext E.isPullback_v.flip.isoPullback.symm fun j => ?_)
  change pullback.lift (pullback.fst (c.π.app j₀) E.w₀ ≫ c.π.app j.left)
    (pullback.snd (c.π.app j₀) E.w₀) _ ≫ 𝟙 _ =
      E.isPullback_v.flip.isoPullback.inv ≫ (E.cone hD hW hg_surj hg_et).π.app j
  rw [Category.comp_id]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, E.cone_π_fst hD hW hg hg_surj hg_et,
      IsPullback.isoPullback_inv_fst_assoc]
  · rw [pullback.lift_snd, Category.assoc, E.cone_π_snd hD hW hg_surj hg_et,
      IsPullback.isoPullback_inv_snd]

/-- **The base changes of a stage model form a presented system with limit `W`.** -/
noncomputable def presentation :
    LimitPresentation B S hS (E.atlasFamily hD).diagram (E.cone hD hW hg_surj hg_et) where
  atlas := E.atlasSystem
  relation := E.relationSystem
  atlasMap := (E.atlasFamily hD).atlasMap
  src := E.srcSystem
  tgt := E.tgtSystem
  surjective_atlasMap := (E.atlasFamily hD).surjective
  etale_atlasMap := (E.atlasFamily hD).etale
  isPullback_relation := (E.atlasFamily hD).isPullback
  isPullback_atlas e := (E.atlasFamily hD).isPullback_atlas E.hcart e
  isAffineHom_atlas := E.isAffineHom_atlasSystem_map
  isAffineHom_relation := E.isAffineHom_relationSystem_map
  isQuasiCompactSpace_atlas j :=
    isQuasiCompactSpace_yoneda_obj B S hS (E.compactSpace_atlasSystem j)
  quasiSeparatedSpace_atlas := E.quasiSeparatedSpace_atlasSystem
  isQuasiCompactSpace_relation j :=
    isQuasiCompactSpace_yoneda_obj B S hS (E.compactSpace_relationSystem j)
  quasiSeparatedSpace_relation := E.quasiSeparatedSpace_relationSystem
  atlasCone := E.atlasLimitCone
  isLimit_atlasCone := E.isLimit_atlasLimitCone
  relationCone := E.relationLimitCone
  isLimit_relationCone := E.isLimit_relationLimitCone
  srcLim := E.f₁'
  tgtLim := E.f₂'
  srcLim_π := E.srcLim_π
  tgtLim_π := E.tgtLim_π
  limitAtlas := g
  isPullback_limitAtlas := E.isPullback_cone hD hW hg hg_surj hg_et

end EtaleStageModel

end LimitPresentation

end AlgebraicGeometry.Space

end
