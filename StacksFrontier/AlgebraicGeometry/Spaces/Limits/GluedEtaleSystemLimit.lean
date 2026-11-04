module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianStage

/-!
# The limit of a system of glued étale quotients

Let `X_k = V_k / R_k` be a system of glued étale quotients
(`AlgebraicGeometry.Space.GluedEtaleSystem`) whose atlases `V_k`, opens `Y_k ⊆ V_k` and
algebraic spaces `U_k` have limits `V`, `W` and `U` with `W = W_k ×_{V_k} V` and
`W = W_k ×_{U_k} U`, and let `f : V ⟶ X` be an étale surjection which is an isomorphism over the
complement of an open subspace `U ⊆ X` with inverse image `W`. Then `X` is the limit of the
`X_k`: the limit of the glued relations `R_k` is the kernel pair `V ×_X V`, because both are
glued from `V` and `W ×_U W` along `W` (`AlgebraicGeometry.Space.GluedKernelDatum.isPushout`),
and an algebraic space presented by the limits of the atlases and of their kernel pairs is the
limit of the system.

## Main results

* `AlgebraicGeometry.Space.GluedSystemLimit.isLimit_relationCone`: the limit of the glued
  relations is the kernel pair of `f`.
* `AlgebraicGeometry.Space.GluedSystemLimit.isLimit`: `X` is the limit of the glued quotients.
* `AlgebraicGeometry.Space.GluedSystemLimit.presentedNoetherianApproximation`: the glued
  quotients form a presented Noetherian approximation of `X`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A system of glued étale quotients `X_k = V_k / R_k` together with limits `V`, `W` and `U` of
its atlases, its opens `Y_k` and its algebraic spaces `U_k`, with `W = Y_k ×_{V_k} V` and
`W = Y_k ×_{U_k} U` at every stage. -/
structure GluedSystemLimit (K : Type u) [Category.{u} K] where
  /-- The system. -/
  G : GluedEtaleSystem B S hS K
  /-- The limit data. -/
  D : GluedKernelDatum B S hS
  /-- The projections from the limit of the atlases. -/
  πV : (Functor.const K).obj D.V ⟶ G.V
  /-- The limit of the atlases is realised in schemes. -/
  isLimit_V : IsLimit ((BigFppfOver.toScheme B S hS).mapCone (Cone.mk D.V πV))
  /-- The projections from the limit of the opens. -/
  πY : (Functor.const K).obj D.W ⟶ G.Y
  /-- The projections from the limit of the algebraic spaces. -/
  πU : (Functor.const K).obj D.Uo.toFunctor ⟶ G.U
  /-- The projections from `W` commute with the inclusions `W ⟶ V` and `Y_k ⟶ V_k`. -/
  πY_j (k : K) : πY.app k ≫ G.j.app k = D.jW ≫ πV.app k
  /-- The projections from `W` commute with the maps `W ⟶ U` and `Y_k ⟶ U_k`. -/
  πY_y (k : K) : yoneda.map (πY.app k) ≫ G.y.app k = D.wU ≫ πU.app k
  /-- `W = Y_k ×_{V_k} V`. -/
  isPullback_πY_j (k : K) : IsPullback (πY.app k) D.jW (G.j.app k) (πV.app k)
  /-- `W = Y_k ×_{U_k} U`. -/
  isPullback_πY_y (k : K) : IsPullback (yoneda.map (πY.app k)) D.wU (G.y.app k) (πU.app k)

namespace GluedSystemLimit

variable {K : Type u} [Category.{u} K] (L : GluedSystemLimit (B := B) (S := S) (hS := hS) K)

local notation "𝕋" => BigFppfOver.toScheme B S hS

/-- The projection from `W ×_U W` to `Y_k ×_{U_k} Y_k`. -/
noncomputable def qπ (k : K) : L.D.Q ⟶ L.G.Q k :=
  yoneda.preimage ((L.G.isPullback_Q k).lift (yoneda.map (L.D.q₁ ≫ L.πY.app k))
    (yoneda.map (L.D.q₂ ≫ L.πY.app k)) (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, L.πY_y,
        ← Category.assoc, ← Category.assoc, L.D.isPullback_Q.w]))

/-- The first projection of `qπ k` is the first projection of `W ×_U W` followed by the
projection `W ⟶ Y_k`. -/
@[reassoc (attr := simp)]
theorem qπ_p₁ (k : K) : L.qπ k ≫ L.G.p₁ k = L.D.q₁ ≫ L.πY.app k :=
  yoneda.map_injective (by simp [qπ])

/-- The second projection of `qπ k` is the second projection of `W ×_U W` followed by the
projection `W ⟶ Y_k`. -/
@[reassoc (attr := simp)]
theorem qπ_p₂ (k : K) : L.qπ k ≫ L.G.p₂ k = L.D.q₂ ≫ L.πY.app k :=
  yoneda.map_injective (by simp [qπ])

/-- The square formed by `qπ k`, the first projections of `W ×_U W` and of `Y_k ×_{U_k} Y_k`, and
the projection `W ⟶ Y_k` is cartesian. -/
theorem isPullback_qπ (k : K) : IsPullback (L.qπ k) L.D.q₁ (L.G.p₁ k) (L.πY.app k) := by
  refine IsPullback.of_map yoneda (L.qπ_p₁ k) ?_
  refine IsPullback.of_right ?_ (by rw [← Functor.map_comp, ← Functor.map_comp, qπ_p₁])
    (L.G.isPullback_Q k).flip
  rw [← Functor.map_comp, qπ_p₂, Functor.map_comp, L.πY_y]
  exact L.D.isPullback_Q.flip.paste_horiz (L.isPullback_πY_y k)

/-- The diagonal of `W ×_U W` followed by `qπ k` is the projection `W ⟶ Y_k` followed by the
diagonal of `Y_k ×_{U_k} Y_k`. -/
theorem d_qπ (k : K) : L.D.d ≫ L.qπ k = L.πY.app k ≫ (L.G.datum k).d := by
  refine L.G.Q_hom_ext k ?_ ?_
  · rw [Category.assoc, qπ_p₁, ← Category.assoc, L.D.d_q₁, Category.id_comp, Category.assoc,
      (L.G.datum k).d_p₁, Category.comp_id]
  · rw [Category.assoc, qπ_p₂, ← Category.assoc, L.D.d_q₂, Category.id_comp, Category.assoc,
      (L.G.datum k).d_p₂, Category.comp_id]

variable (Tc : Subfunctor L.D.X)
  (hT : ∀ x, x ∉ Set.range (pointsMap B S hS L.D.Uo.toFunctor L.D.Uo.ι) →
    x ∈ Set.range (pointsMap B S hS Tc.toFunctor Tc.ι))
  (hiso : IsIso (pullback.fst Tc.ι L.D.f))

include hT hiso in
/-- The kernel pair `V ×_X V` is glued from `V` and `W ×_U W` along `W`: the square of schemes
formed by `W ⟶ V`, the diagonal of `W ×_U W`, the diagonal of `V ×_X V` and the map
`W ×_U W ⟶ V ×_X V` is a pushout. -/
theorem isPushout_K :
    IsPushout ((𝕋).map L.D.jW) ((𝕋).map L.D.d) ((𝕋).map L.D.Δ) ((𝕋).map L.D.ι) :=
  L.D.isPushout Tc hT hiso

/-- The inclusion `W ⟶ V` followed by the projection `V ⟶ V_k` is the projection `W ⟶ Y_k`
followed by the inclusion `Y_k ⟶ V_k`, as morphisms of schemes. -/
theorem jW_πV (k : K) :
    (𝕋).map L.D.jW ≫ (𝕋).map (L.πV.app k) = (𝕋).map (L.πY.app k) ≫ (𝕋).map (L.G.j.app k) := by
  rw [← Functor.map_comp, ← Functor.map_comp, L.πY_j]

/-- The projection from the kernel pair `V ×_X V` to the glued relation at a stage. -/
noncomputable def rπ₀ (k : K) : (𝕋).obj L.D.K ⟶ (L.G.datum k).relationScheme :=
  (L.isPushout_K Tc hT hiso).desc ((𝕋).map (L.πV.app k) ≫ (L.G.datum k).a)
    ((𝕋).map (L.qπ k) ≫ (L.G.datum k).b) (by
      rw [← Category.assoc, L.jW_πV k, Category.assoc, (L.G.datum k).isPushout.w,
        ← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp, L.d_qπ])

/-- The diagonal of `V ×_X V` followed by `rπ₀ k` is the projection `V ⟶ V_k` followed by the
inclusion of `V_k` into the glued relation. -/
theorem Δ_rπ₀ (k : K) :
    (𝕋).map L.D.Δ ≫ L.rπ₀ Tc hT hiso k = (𝕋).map (L.πV.app k) ≫ (L.G.datum k).a :=
  (L.isPushout_K Tc hT hiso).inl_desc _ _ _

/-- The map `W ×_U W ⟶ V ×_X V` followed by `rπ₀ k` is `qπ k` followed by the inclusion of
`Y_k ×_{U_k} Y_k` into the glued relation. -/
theorem ι_rπ₀ (k : K) :
    (𝕋).map L.D.ι ≫ L.rπ₀ Tc hT hiso k = (𝕋).map (L.qπ k) ≫ (L.G.datum k).b :=
  (L.isPushout_K Tc hT hiso).inr_desc _ _ _

/-- `rπ₀ k` followed by a projection of the glued relation is the corresponding projection of
`V ×_X V` followed by `V ⟶ V_k`, given the compatibilities on the two charts. -/
private theorem rπ₀_comp_eq (k : K)
    {s : (L.G.datum k).relationScheme ⟶ (𝕋).obj (L.G.V.obj k)} {p : L.G.Q k ⟶ L.G.Y.obj k}
    {q : L.D.Q ⟶ L.D.W} {κ : L.D.K ⟶ L.D.V} (ha : (L.G.datum k).a ≫ s = 𝟙 _)
    (hb : (L.G.datum k).b ≫ s = (𝕋).map p ≫ (𝕋).map (L.G.j.app k))
    (hq : L.qπ k ≫ p = q ≫ L.πY.app k)
    (hΔ : L.D.Δ ≫ κ = 𝟙 _) (hι : L.D.ι ≫ κ = q ≫ L.D.jW) :
    L.rπ₀ Tc hT hiso k ≫ s = (𝕋).map κ ≫ (𝕋).map (L.πV.app k) := by
  refine (L.isPushout_K Tc hT hiso).hom_ext ?_ ?_
  · rw [← Category.assoc, Δ_rπ₀, Category.assoc, ha, Category.comp_id, ← Category.assoc,
      ← Functor.map_comp, hΔ, CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [← Category.assoc, ι_rπ₀, Category.assoc, hb, ← Category.assoc, ← Functor.map_comp, hq,
      ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hι,
      Category.assoc, Category.assoc, ← L.πY_j]

/-- `rπ₀ k` is compatible with the first projection of `V ×_X V` and the source morphism of the
glued relation. -/
theorem rπ₀_src₀ (k : K) :
    L.rπ₀ Tc hT hiso k ≫ (L.G.datum k).src₀ = (𝕋).map L.D.k₁ ≫ (𝕋).map (L.πV.app k) :=
  L.rπ₀_comp_eq Tc hT hiso k (GluedRelation.a_src ..) (GluedRelation.b_src ..) (qπ_p₁ ..)
    (GluedKernelDatum.Δ_k₁ _) (GluedKernelDatum.ι_k₁ _)

/-- `rπ₀ k` is compatible with the second projection of `V ×_X V` and the target morphism of the
glued relation. -/
theorem rπ₀_tgt₀ (k : K) :
    L.rπ₀ Tc hT hiso k ≫ (L.G.datum k).tgt₀ = (𝕋).map L.D.k₂ ≫ (𝕋).map (L.πV.app k) :=
  L.rπ₀_comp_eq Tc hT hiso k (GluedRelation.a_tgt ..) (GluedRelation.b_tgt ..) (qπ_p₂ ..)
    (GluedKernelDatum.Δ_k₂ _) (GluedKernelDatum.ι_k₂ _)

/-- **The kernel pair `V ×_X V` is the base change of each glued relation along the first
projections** (Stacks 07SV at the limit). -/
theorem isPullback_rπ₀ (k : K) :
    IsPullback (L.rπ₀ Tc hT hiso k) ((𝕋).map L.D.k₁) (L.G.datum k).src₀
      ((𝕋).map (L.πV.app k)) :=
  isPullback_gluedRelationSource_of_isPullback ((L.isPullback_πY_j k).map (𝕋))
    ((L.isPullback_qπ k).map (𝕋))
    (by rw [← Functor.map_comp, GluedKernelDatum.d_q₁, CategoryTheory.Functor.map_id]; rfl)
    (by rw [← Functor.map_comp, ← Functor.map_comp, L.d_qπ])
    (L.isPushout_K Tc hT hiso) (L.G.datum k).isPushout
    (by rw [← Functor.map_comp, GluedKernelDatum.Δ_k₁, CategoryTheory.Functor.map_id])
    (by rw [← Functor.map_comp, GluedKernelDatum.ι_k₁, Functor.map_comp])
    (GluedRelation.a_src (L.G.datum k).hd₁ _) (GluedRelation.b_src (L.G.datum k).hd₁ _)
    (L.Δ_rπ₀ Tc hT hiso k) (L.ι_rπ₀ Tc hT hiso k)

/-- The projections `qπ` are compatible with the transition morphisms of the system
`Y_k ×_{U_k} Y_k`. -/
theorem qπ_qmap {k l : K} (e : k ⟶ l) : L.qπ k ≫ L.G.qmap e = L.qπ l :=
  L.G.Q_hom_ext l (by
      rw [Category.assoc, GluedEtaleSystem.qmap_p₁, qπ_p₁_assoc, qπ_p₁]
      exact congrArg (L.D.q₁ ≫ ·) (by simpa using (L.πY.naturality e).symm))
    (by
      rw [Category.assoc, GluedEtaleSystem.qmap_p₂, qπ_p₂_assoc, qπ_p₂]
      exact congrArg (L.D.q₂ ≫ ·) (by simpa using (L.πY.naturality e).symm))

/-- The projections `rπ₀` are compatible with the transition morphisms of the glued relations. -/
theorem rπ₀_rmap₀ {k l : K} (e : k ⟶ l) :
    L.rπ₀ Tc hT hiso k ≫ L.G.rmap₀ e = L.rπ₀ Tc hT hiso l := by
  refine (L.isPushout_K Tc hT hiso).hom_ext ?_ ?_
  · rw [← Category.assoc, Δ_rπ₀, Category.assoc, GluedEtaleSystem.a_rmap₀, ← Category.assoc,
      ← Functor.map_comp, Δ_rπ₀]
    exact congrArg (· ≫ (L.G.datum l).a)
      (congrArg (𝕋).map (by simpa using (L.πV.naturality e).symm))
  · rw [← Category.assoc, ι_rπ₀, Category.assoc, GluedEtaleSystem.b_rmap₀, ← Category.assoc,
      ← Functor.map_comp, qπ_qmap, ι_rπ₀]

/-- The cone of glued relations with vertex `V ×_X V`. -/
@[reducible]
noncomputable def relationCone : Cone L.G.R where
  pt := L.D.K
  π :=
    { app k := siteObjectOfLocallyOfFiniteType.lift (L.G.V.obj k) (L.G.datum k).src₀
        (L.rπ₀ Tc hT hiso k) (by
          rw [← Category.assoc, L.rπ₀_src₀, Category.assoc]
          have h₁ : (𝕋).map (L.πV.app k) ≫ (L.G.V.obj k).hom.hom = L.D.V.hom.hom :=
            congrArg (fun f => f.hom) (Over.w (L.πV.app k))
          have h₂ : (𝕋).map L.D.k₁ ≫ L.D.V.hom.hom = L.D.K.hom.hom :=
            congrArg (fun f => f.hom) (Over.w L.D.k₁)
          rw [h₁, h₂]
          rfl)
      naturality k l e := (𝕋).map_injective (by
        rw [Functor.map_comp, Functor.map_comp, Functor.const_obj_map]
        change 𝟙 _ ≫ L.rπ₀ Tc hT hiso l = L.rπ₀ Tc hT hiso k ≫ L.G.rmap₀ e
        rw [Category.id_comp]
        exact (L.rπ₀_rmap₀ Tc hT hiso e).symm) }

/-- The morphism of schemes underlying a projection of `relationCone` is `rπ₀`. -/
theorem toScheme_map_relationCone_π (k : K) :
    (𝕋).map ((L.relationCone Tc hT hiso).π.app k) = L.rπ₀ Tc hT hiso k := rfl

/-- **The limit of the glued relations is the kernel pair `V ×_X V`, realised in the site.** -/
noncomputable def isLimit_relationCone [IsCofiltered K] :
    IsLimit ((𝕋).mapCone (L.relationCone Tc hT hiso)) := by
  let k₀ : K := (IsCofiltered.nonempty (C := K)).some
  refine (Functor.Initial.isLimitWhiskerEquiv (Over.forget k₀) _)
    (isLimitOfCartesianCone (L.G.V ⋙ 𝕋) ((𝕋).mapCone (Cone.mk L.D.V L.πV)) L.isLimit_V k₀
      ((𝕋).obj (L.G.R.obj k₀)) ((𝕋).map (L.G.src.app k₀)) (Over.forget k₀ ⋙ L.G.R ⋙ 𝕋) _
      (Functor.whiskerLeft (Over.forget k₀) (Functor.whiskerRight L.G.src (𝕋)))
      { app := fun j => (𝕋).map (L.G.R.map j.hom)
        naturality := fun j j' φ => by
          change (𝕋).map (L.G.R.map φ.left) ≫ (𝕋).map (L.G.R.map j'.hom) =
            (𝕋).map (L.G.R.map j.hom) ≫ 𝟙 _
          rw [Category.comp_id, ← Functor.map_comp, ← L.G.R.map_comp, Over.w φ] }
      (fun j => ((L.G.hcart j.hom).flip.map (𝕋))) ((𝕋).map L.D.k₁) (L.rπ₀ Tc hT hiso k₀)
      (L.isPullback_rπ₀ Tc hT hiso k₀).flip (fun j => ?_) (fun j => ?_))
  · exact L.rπ₀_src₀ Tc hT hiso j.left
  · exact L.rπ₀_rmap₀ Tc hT hiso j.hom

/-- The first projection of `V ×_X V` is compatible with the projections of `relationCone` and
the source morphisms of the glued relations. -/
theorem srcLim_π (k : K) :
    L.D.k₁ ≫ L.πV.app k = (L.relationCone Tc hT hiso).π.app k ≫ L.G.src.app k :=
  (𝕋).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact (L.rπ₀_src₀ Tc hT hiso k).symm)

/-- The second projection of `V ×_X V` is compatible with the projections of `relationCone` and
the target morphisms of the glued relations. -/
theorem tgtLim_π (k : K) :
    L.D.k₂ ≫ L.πV.app k = (L.relationCone Tc hT hiso).π.app k ≫ L.G.tgt.app k :=
  (𝕋).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact (L.rπ₀_tgt₀ Tc hT hiso k).symm)

variable (hf_surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
  (BigFppfOver.toScheme B S hS)).presheaf L.D.f)

/-- The morphism `f : V ⟶ X` is étale, as a morphism of presheaves. -/
theorem etale_f : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf L.D.f :=
  (isEtale_iff_presheaf_of_yoneda B S hS L.D.f).mp L.D.isEtale_f

/-- The cone with vertex `X` over the glued quotients. -/
noncomputable abbrev cone : Cone L.G.atlasFamily.diagram :=
  L.G.atlasFamily.limitCone (cV := Cone.mk L.D.V L.πV) (cR := L.relationCone Tc hT hiso)
    L.D.k₁ L.D.k₂ (L.srcLim_π Tc hT hiso) (L.tgtLim_π Tc hT hiso) L.D.isAlgebraicSpace_X L.D.f
    hf_surj L.etale_f L.D.isPullback_K

/-- **`X` is the limit of the glued quotients**, for a cofiltered thin index category with a
terminal index. -/
noncomputable def isLimit [IsCofiltered K] (hthin : ∀ k l : K, Subsingleton (k ⟶ l)) (k₀ : K)
    (h₀ : ∀ k, Nonempty (k ⟶ k₀)) : IsLimit (L.cone Tc hT hiso hf_surj) :=
  L.G.atlasFamily.isLimitLimitCone L.G.hcart L.isLimit_V (L.isLimit_relationCone Tc hT hiso)
    L.D.k₁ L.D.k₂ (L.srcLim_π Tc hT hiso) (L.tgtLim_π Tc hT hiso) L.D.isAlgebraicSpace_X L.D.f
    hf_surj L.etale_f L.D.isPullback_K hthin k₀ h₀

/-- The square formed by `f : V ⟶ X`, the atlas `V_k ⟶ X_k` and the projections from `V` and
`X` is cartesian, for a cofiltered thin index category with a terminal index. -/
theorem isPullback_cone [IsCofiltered K] (hthin : ∀ k l : K, Subsingleton (k ⟶ l)) (k₀ : K)
    (h₀ : ∀ k, Nonempty (k ⟶ k₀)) (k : K) :
    IsPullback (yoneda.map (L.πV.app k)) L.D.f (L.G.atlasFamily.v k)
      ((L.cone Tc hT hiso hf_surj).π.app k) := by
  have hc := L.isLimit Tc hT hiso hf_surj hthin k₀ h₀
  have hg : ∀ i, L.D.f ≫ (L.cone Tc hT hiso hf_surj).π.app i =
      yoneda.map (L.πV.app i) ≫ L.G.atlasFamily.v i := fun i =>
    L.G.atlasFamily.a_limitProj (cV := Cone.mk L.D.V L.πV) (cR := L.relationCone Tc hT hiso)
      L.D.k₁ L.D.k₂ (L.srcLim_π Tc hT hiso) (L.tgtLim_π Tc hT hiso) L.D.isAlgebraicSpace_X L.D.f
      hf_surj L.etale_f L.D.isPullback_K i
  have h₀' := L.G.atlasFamily.isPullback_limit_atlas L.G.hcart L.isLimit_V hthin k₀ h₀ _ hc
    L.D.f hg
  refine IsPullback.of_right ?_ (hg k).symm (L.G.atlasFamily.isPullback_atlas L.G.hcart (h₀ k).some)
  have hcw := (L.cone Tc hT hiso hf_surj).w (h₀ k).some
  have hVw : L.πV.app k ≫ L.G.V.map (h₀ k).some = L.πV.app k₀ := by
    simpa using (L.πV.naturality (h₀ k).some).symm
  have e₁ : yoneda.map (L.πV.app k) ≫ yoneda.map (L.G.V.map (h₀ k).some) =
      yoneda.map (L.πV.app k₀) := by rw [← Functor.map_comp, hVw]
  rwa [e₁, hcw]

section Approximation

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [OrderBot I]
  (L : GluedSystemLimit (B := B) (S := ⊤_ Scheme.{u}) (hS := hZ) Iᵒᵖ)
  (Tc : Subfunctor L.D.X)
  (hT : ∀ x, x ∉ Set.range (pointsMap B _ hZ L.D.Uo.toFunctor L.D.Uo.ι) →
    x ∈ Set.range (pointsMap B _ hZ Tc.toFunctor Tc.ι))
  (hiso : IsIso (pullback.fst Tc.ι L.D.f))
  (hf_surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B _ hZ)).presheaf L.D.f)
  (hVaff : ∀ {k l : Iᵒᵖ} (e : k ⟶ l), _root_.AlgebraicGeometry.IsAffineHom
    ((BigFppfOver.toScheme B _ hZ).map (L.G.V.map e)))
  (hVlft : ∀ k,
    LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B _ hZ).obj (L.G.V.obj k))))

omit [IsDirected I (· ≤ ·)] [OrderBot I] in
/-- The opposite of a preorder is thin. -/
theorem thin_op : ∀ k l : Iᵒᵖ, Subsingleton (k ⟶ l) :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

omit [IsDirected I (· ≤ ·)] in
/-- In the opposite of a preorder with a least element, every object maps to `op ⊥`. -/
theorem nonempty_hom_op_bot : ∀ k : Iᵒᵖ, Nonempty (k ⟶ Opposite.op (⊥ : I)) :=
  fun _ => ⟨(homOfLE bot_le).op⟩

omit [IsDirected I (· ≤ ·)] [OrderBot I] in
include hVlft in
/-- The atlases `V_k` are locally Noetherian when they are locally of finite type over
`Spec ℤ`. -/
theorem isLocallyNoetherian_V (k : Iᵒᵖ) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B _ hZ).obj (L.G.V.obj k)) := by
  have := hVlft k
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
    have e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
      (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).symm
    have : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
    exact LocallyOfFiniteType.isLocallyNoetherian e.hom
  exact LocallyOfFiniteType.isLocallyNoetherian (terminal.from _)

omit [IsDirected I (· ≤ ·)] [OrderBot I] in
include hVlft in
/-- The glued relations `R_k` are locally Noetherian when the atlases `V_k` are locally of finite
type over `Spec ℤ`. -/
theorem isLocallyNoetherian_R (k : Iᵒᵖ) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B _ hZ).obj (L.G.R.obj k)) := by
  have := L.isLocallyNoetherian_V hVlft k
  have : LocallyOfFiniteType (L.G.datum k).src₀ := (L.G.datum k).locallyOfFiniteType_src₀
  exact LocallyOfFiniteType.isLocallyNoetherian (L.G.datum k).src₀

/-- **The presented Noetherian approximation of `X` by the glued étale quotients.** -/
noncomputable def presentedNoetherianApproximation :
    PresentedNoetherianApproximation B hZ L.D.X := by
  have hc := L.isLimit Tc hT hiso hf_surj thin_op (Opposite.op ⊥) nonempty_hom_op_bot
  let A := L.G.atlasFamily
  have hV : ∀ k, IsLocallyNoetherian ((BigFppfOver.toScheme B _ hZ).obj (L.G.V.obj k)) :=
    L.isLocallyNoetherian_V hVlft
  have hR : ∀ k, IsLocallyNoetherian ((BigFppfOver.toScheme B _ hZ).obj (L.G.R.obj k)) :=
    L.isLocallyNoetherian_R hVlft
  exact
    { I := I
      diagram := A.diagram
      isAlgebraicSpace := A.isAlgebraicSpace
      isAffineHom_map := fun e => L.G.isAffineHom_atlasFamily_map e (hVaff e)
      isAbsolutelyQuasiSeparated := fun k => by
        have := hV k
        have : CompactSpace ((BigFppfOver.toScheme B _ hZ).obj (L.G.R.obj k)) :=
          (L.G.datum k).compactSpace_relationScheme
        exact isAbsolutelyQuasiSeparated_of_atlas (A.isAlgebraicSpace k) (A.v k) (A.surjective k)
          (A.etale k) (A.isPullback k) inferInstance
      isFiniteTypeOverIntegers := fun k =>
        isFiniteType_viewOverIntegers_of_atlas (A.isAlgebraicSpace k) (A.v k) (A.surjective k)
          (A.etale k) (hVlft k)
      π := (L.cone Tc hT hiso hf_surj).π
      isLimit := hc
      presentation :=
        { atlas := L.G.V
          relation := L.G.R
          atlasMap := A.atlasMap
          src := L.G.src
          tgt := L.G.tgt
          surjective_atlasMap := A.surjective
          etale_atlasMap := A.etale
          isPullback_relation := A.isPullback
          isPullback_atlas := fun e => A.isPullback_atlas L.G.hcart e
          isAffineHom_atlas := hVaff
          isAffineHom_relation := fun e =>
            MorphismProperty.of_isPullback ((L.G.hcart e).flip.map (BigFppfOver.toScheme B _ hZ))
              (hVaff e)
          isQuasiCompactSpace_atlas := fun k => isQuasiCompactSpace_yoneda_obj B _ hZ
            (L.G.compactSpace_V k)
          quasiSeparatedSpace_atlas := fun k => by have := hV k; infer_instance
          isQuasiCompactSpace_relation := fun k => isQuasiCompactSpace_yoneda_obj B _ hZ
            (L.G.datum k).compactSpace_relationScheme
          quasiSeparatedSpace_relation := fun k => by have := hR k; infer_instance
          atlasCone := Cone.mk L.D.V L.πV
          isLimit_atlasCone := L.isLimit_V
          relationCone := L.relationCone Tc hT hiso
          isLimit_relationCone := L.isLimit_relationCone Tc hT hiso
          srcLim := L.D.k₁
          tgtLim := L.D.k₂
          srcLim_π := L.srcLim_π Tc hT hiso
          tgtLim_π := L.tgtLim_π Tc hT hiso
          limitAtlas := L.D.f
          isPullback_limitAtlas := L.isPullback_cone Tc hT hiso hf_surj thin_op (Opposite.op ⊥)
            nonempty_hom_op_bot } }

end Approximation

end GluedSystemLimit

end AlgebraicGeometry.Space

end
