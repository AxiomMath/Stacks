module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.NoetherianStage
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation

/-!
# Noetherian approximation of a proper flat family

Let `V` be an affine scheme, `f : X ⟶ V` a proper morphism of finite presentation and `ℱ` an
`𝒪_X`-module of finite presentation, flat over `V`. Then there are a Noetherian scheme `T`, a
morphism `V ⟶ T`, a proper morphism of finite presentation `f₀ : X₀ ⟶ T` with `X = X₀ ×_T V`,
and an `𝒪_{X₀}`-module `ℱ₀` of finite presentation, flat over `T`, pulling back to `ℱ`.

This is the approximation step of the proof of [Stacks, Tag 0A1H], in the case of
[Stacks, Tag 0B91] (2): write `Γ(V, 𝒪_V)` as the filtered colimit of its finitely generated
subrings ([Stacks, Tag 01ZA] for an affine scheme,
`AlgebraicGeometry.specLimitNoetherianSituation`), descend `X` ([Stacks, Tag 01ZM]), properness
([Stacks, Tag 081F]), `ℱ` ([Stacks, Tag 01ZR]) and flatness ([Stacks, Tag 05LY]).

## Main results

* `AlgebraicGeometry.ProperFlatPerfection.exists_isProper_stage`,
  `AlgebraicGeometry.ProperFlatPerfection.exists_module_stage` and
  `AlgebraicGeometry.ProperFlatPerfection.exists_flat_stage`: the three descent steps, each read
  at a cartesian model `X = Y ×_{S_i} S` of the family.
* `AlgebraicGeometry.ProperFlatPerfection.exists_model_stage`: the three combined, at one stage.
* `AlgebraicGeometry.ProperFlatPerfection.exists_noetherianModel`: the affine statement above.

## Implementation notes

Every stage is presented by a cartesian square `IsPullback g f p (c.π.app i)` rather than by an
object of an over category, and is moved to a later stage by
`AlgebraicGeometry.exists_isPullback_transport`, which keeps the model in the form
`pullback (D.map e) p`. The descent statements of the source are phrased in three different
orderings of the factors of a fibre product; each is brought to this one by
`CategoryTheory.Limits.pullbackSymmetry` or by the isomorphism of the cartesian square, and
flatness crosses those isomorphisms by `isFlatOver_comp_of_iso` and `isFlatOver_comp_iso_iff`.

## References

* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.ProperFlatPerfection

/-- Relative flatness transports along an isomorphism of the source. -/
theorem isFlatOver_comp_of_iso {X X' S : Scheme.{u}} (e : X' ≅ X) (h : X ⟶ S) (M : X.Modules)
    (hM : IsFlatOver h.toLRSHom.toShHom M) (N : X'.Modules)
    (eN : N ≅ (Scheme.Modules.pullback e.hom).obj M) :
    IsFlatOver (e.hom ≫ h).toLRSHom.toShHom N := fun x =>
  (flatOverAt_iff_of_iso (e.hom ≫ h) eN x).2
    ((isFlatOverAt_iff_modulePullback_isFlatOverAt e.hom h M x
      (Flat.stalkMap e.hom x)).1 (hM _))

/-- Relative flatness transports along an isomorphism of the target. -/
theorem isFlatOver_comp_iso_iff {X S S' : Scheme.{u}} (h : X ⟶ S) (e : S ⟶ S') [IsIso e]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsFlatOver (h ≫ e).toLRSHom.toShHom M ↔ IsFlatOver h.toLRSHom.toShHom M :=
  isFlatOver_comp_iff_of_etale h e M

section Stages

/-- Base change of `p` over `S` along `t`, followed by the projection, is the projection of `p`. -/
private theorem overPullback_map_homMk_snd {S Y T : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S) :
    ((Over.pullback t).map (Over.homMk p (by simp) : Over.mk p ⟶ Over.mk (𝟙 S))).left ≫
      pullback.snd (𝟙 S) t = pullback.snd p t := by
  simp only [Over.pullback]
  exact pullback.lift_snd _ _ _

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i : I, CompactSpace (D.obj i)]
  [∀ i : I, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c)
  {X : Scheme.{u}} (f : X ⟶ c.pt)

include hc in
/-- **Properness descends to a stage** (Stacks 081F), read at a cartesian model. -/
theorem exists_isProper_stage [IsProper f] {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    (hp : FinitePresentation p) {g : X ⟶ Y} (hsq : IsPullback g f p (c.π.app i)) :
    ∃ (j : I) (e : j ⟶ i), IsProper (pullback.fst (D.map e) p) := by
  have : LocallyOfFinitePresentation p := hp.1
  have : QuasiCompact p := hp.2.1
  have : QuasiSeparated p := hp.2.2
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  let X₀ : Over (D.obj i) := Over.mk p
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk p (by simp [X₀, Y₀])
  have : CompactSpace X₀.left := ‹CompactSpace Y›
  have : QuasiSeparatedSpace X₀.left := ‹QuasiSeparatedSpace Y›
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType p)
  have key : ∀ {T : Scheme.{u}} (t : T ⟶ D.obj i),
      ((Over.pullback t).map f₀).left ≫ pullback.snd (𝟙 (D.obj i)) t = pullback.snd p t :=
    fun t => overPullback_map_homMk_snd p t
  have hlim : IsProper ((Over.pullback (c.π.app i)).map f₀).left := by
    have h1 : IsProper (pullback.snd p (c.π.app i)) := by
      have : pullback.snd p (c.π.app i) = hsq.isoPullback.inv ≫ f := by simp
      rw [this]; infer_instance
    rw [← key] at h1
    exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).mp h1
  obtain ⟨j, e, hj⟩ := exists_isProper_baseChange_of_isLimit D c i hc X₀ Y₀ f₀
  refine ⟨j, e, ?_⟩
  have h2 : IsProper (pullback.snd p (D.map e)) := by
    rw [← key]; infer_instance
  have : pullback.fst (D.map e) p = (pullbackSymmetry (D.map e) p).hom ≫ pullback.snd p (D.map e) :=
    by simp
  rw [this]; infer_instance

include hc in
/-- **A module of finite presentation descends to a stage** (Stacks 01ZR), read at a cartesian
model: the model of the scheme is advanced along the descent of the module. -/
theorem exists_module_stage {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    (hp : FinitePresentation p) {g : X ⟶ Y} (hsq : IsPullback g f p (c.π.app i))
    (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (j : I) (e : j ⟶ i) (g' : X ⟶ pullback (D.map e) p)
      (Fj : (pullback (D.map e) p).Modules),
      IsPullback g' f (pullback.fst (D.map e) p) (c.π.app j) ∧ Fj.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback g').obj Fj) := by
  have : QuasiCompact p := hp.2.1
  have : QuasiSeparated p := hp.2.2
  let Xp : Over (D.obj i) := Over.mk p
  have : ∀ {j k : Over i} (e : j ⟶ k),
      IsAffineHom ((Scheme.baseChangeDiagram D i Xp).map e) :=
    fun e => Scheme.isAffineHom_baseChangeDiagram_map D i Xp e
  have hqc : ∀ j : Over i, QuasiCompact (pullback.fst (D.map j.hom) p) := fun j =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (D.map j.hom) p).flip inferInstance
  have hqs : ∀ j : Over i, QuasiSeparated (pullback.fst (D.map j.hom) p) := fun j =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (D.map j.hom) p).flip inferInstance
  have : ∀ j : Over i, CompactSpace ((Scheme.baseChangeDiagram D i Xp).obj j) := fun j =>
    @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst (D.map j.hom) p) (hqc j) _
  have : ∀ j : Over i, QuasiSeparatedSpace ((Scheme.baseChangeDiagram D i Xp).obj j) := fun j =>
    @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst (D.map j.hom) p) _ (hqs j)
  let ψ : X ≅ pullback (c.π.app i) p := hsq.flip.isoPullback
  let F' : (Scheme.baseChangeCone D i Xp c).pt.Modules := (Scheme.Modules.pullback ψ.inv).obj F
  have : F'.IsFinitePresentation :=
    Stacks.Modules.isFinitePresentation_pullback ψ.inv F inferInstance
  obtain ⟨j, Fj, hFj, ⟨eF⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      (Scheme.baseChangeDiagram D i Xp) (Scheme.baseChangeCone D i Xp c)
      (Scheme.isLimitBaseChangeCone D i Xp c hc) F'
  let π' : pullback (c.π.app i) p ⟶ pullback (D.map j.hom) p :=
    (Scheme.baseChangeCone D i Xp c).π.app j
  obtain ⟨g'', hg''pb, hg''⟩ :=
    exists_isPullback_transport D c j.hom p f g hsq
  have hfst : π' ≫ pullback.fst (D.map j.hom) p = pullback.fst (c.π.app i) p ≫ c.π.app j.left :=
    Scheme.baseChangeCone_π_fst D i Xp c j
  have hsnd : π' ≫ pullback.snd (D.map j.hom) p = pullback.snd (c.π.app i) p :=
    Scheme.baseChangeCone_π_snd D i Xp c j
  have heq : ψ.hom ≫ π' = g'' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfst, ← Category.assoc]
      simp only [ψ, IsPullback.isoPullback_hom_fst]
      exact hg''pb.w.symm
    · rw [Category.assoc, hsnd, hg'']
      simp [ψ]
  refine ⟨j.left, j.hom, g'', Fj, hg''pb, hFj, ⟨?_⟩⟩
  exact ((Scheme.Modules.pullbackId X).app F).symm ≪≫
    ((Scheme.Modules.pullbackCongr ψ.hom_inv_id).app F).symm ≪≫
    ((Scheme.Modules.pullbackComp ψ.hom ψ.inv).app F).symm ≪≫
    (Scheme.Modules.pullback ψ.hom).mapIso eF ≪≫
    (Scheme.Modules.pullbackComp ψ.hom π').app Fj ≪≫
    (Scheme.Modules.pullbackCongr heq).app Fj

omit [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)] in
/-- The base change of a module along the projection of a fibre product, written for the other
ordering of the factors. -/
theorem key_overPullback_map {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i) {T : Scheme.{u}}
    (t : T ⟶ D.obj i) :
    ((Over.pullback t).map (Over.homMk p (by simp) : Over.mk p ⟶ Over.mk (𝟙 (D.obj i)))).left ≫
      pullback.snd (𝟙 (D.obj i)) t = pullback.snd p t :=
  overPullback_map_homMk_snd p t

include hc in
/-- **Flatness of a module descends to a stage** (Stacks 05LY), read at a cartesian model. -/
theorem exists_flat_stage {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    (hp : FinitePresentation p) {g : X ⟶ Y} (hsq : IsPullback g f p (c.π.app i))
    (G : Y.Modules) [G.IsFinitePresentation] (F : X.Modules)
    (eG : F ≅ (Scheme.Modules.pullback g).obj G)
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    ∃ (j : I) (e : j ⟶ i), IsFlatOver (pullback.fst (D.map e) p).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.snd (D.map e) p)).obj G) := by
  have : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation G
      inferInstance).1
  let X₀ : Over (D.obj i) := Over.mk p
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk p (by simp [X₀, Y₀])
  let ψ : X ≅ pullback p (c.π.app i) := hsq.isoPullback
  have hψ : ψ.inv ≫ g = pullback.fst p (c.π.app i) := by
    rw [Iso.inv_comp_eq]
    simp [ψ]
  have hψ' : ψ.inv ≫ f = pullback.snd p (c.π.app i) := by
    rw [Iso.inv_comp_eq]
    simp [ψ]
  have hlim : IsFlatOver ((Over.pullback (c.π.app i)).map f₀).left.toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst X₀.hom (c.π.app i))).obj G) := by
    have h1 : IsFlatOver (ψ.symm.hom ≫ f).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst p (c.π.app i))).obj G) :=
      isFlatOver_comp_of_iso ψ.symm f F hF _
        (((Scheme.Modules.pullbackCongr hψ).app G).symm ≪≫
          ((Scheme.Modules.pullbackComp ψ.inv g).app G).symm ≪≫
          (Scheme.Modules.pullback ψ.inv).mapIso eG.symm)
    have h2 : ψ.symm.hom ≫ f =
        ((Over.pullback (c.π.app i)).map f₀).left ≫ pullback.snd (𝟙 (D.obj i)) (c.π.app i) := by
      rwa [key_overPullback_map D p (c.π.app i)]
    rw [h2] at h1
    exact (isFlatOver_comp_iso_iff _ _ _).1 h1
  obtain ⟨j, e, hj⟩ := @eventually_isFlatOver_modulePullback _ _ _ _ D c hc _ _ _ i X₀ Y₀ hp
    ⟨inferInstanceAs (LocallyOfFinitePresentation (𝟙 _)),
      inferInstanceAs (QuasiCompact (𝟙 _)), inferInstanceAs (QuasiSeparated (𝟙 _))⟩ f₀ G
    ‹G.IsQuasicoherent› ‹G.IsFinitePresentation› hlim
  refine ⟨j, e, ?_⟩
  have h3 : IsFlatOver (pullback.snd p (D.map e)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst p (D.map e))).obj G) := by
    rw [← key_overPullback_map D p (D.map e)]
    exact (isFlatOver_comp_iso_iff _ _ _).2 hj
  let σ := pullbackSymmetry (D.map e) p
  have hσ : σ.hom ≫ pullback.snd p (D.map e) = pullback.fst (D.map e) p :=
    pullbackSymmetry_hom_comp_snd (D.map e) p
  have hσ' : σ.hom ≫ pullback.fst p (D.map e) = pullback.snd (D.map e) p :=
    pullbackSymmetry_hom_comp_fst (D.map e) p
  have h4 := isFlatOver_comp_of_iso σ (pullback.snd p (D.map e)) _ h3
    ((Scheme.Modules.pullback (pullback.snd (D.map e) p)).obj G)
    (((Scheme.Modules.pullbackCongr hσ').app G).symm ≪≫
      ((Scheme.Modules.pullbackComp σ.hom (pullback.fst p (D.map e))).app G).symm)
  rwa [hσ] at h4

include hc in
/-- **A proper morphism of finite presentation and a module of finite presentation flat over the
base descend together to a stage**, with properness, finite presentation and flatness. -/
theorem exists_model_stage [IsProper f] (hf : FinitePresentation f) (F : X.Modules)
    [F.IsFinitePresentation] (hF : IsFlatOver f.toLRSHom.toShHom F) :
    ∃ (l : I) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ D.obj l) (g' : X ⟶ X₀) (F₀ : X₀.Modules),
      IsProper f₀ ∧ FinitePresentation f₀ ∧ F₀.IsFinitePresentation ∧
        IsFlatOver f₀.toLRSHom.toShHom F₀ ∧ IsPullback g' f f₀ (c.π.app l) ∧
          Nonempty (F ≅ (Scheme.Modules.pullback g').obj F₀) := by
  obtain ⟨i, Y, p, g, hp, hsq⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall D c hc f hf
  obtain ⟨j, e, hprop⟩ := exists_isProper_stage D c hc f p hp hsq
  obtain ⟨g1, hsq1, -⟩ := exists_isPullback_transport D c e p f g hsq
  have hp1 : FinitePresentation (pullback.fst (D.map e) p) :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback (D.map e) p).flip hp
  obtain ⟨k, e2, g2, F2, hsq2, hF2, ⟨eF2⟩⟩ :=
    exists_module_stage D c hc f (pullback.fst (D.map e) p) hp1 hsq1 F
  have hp2 : FinitePresentation (pullback.fst (D.map e2) (pullback.fst (D.map e) p)) :=
    FinitePresentation.of_isPullback
      (IsPullback.of_hasPullback (D.map e2) (pullback.fst (D.map e) p)).flip hp1
  have hprop2 : IsProper (pullback.fst (D.map e2) (pullback.fst (D.map e) p)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (D.map e2) (pullback.fst (D.map e) p)).flip hprop
  obtain ⟨l, e3, hfl⟩ :=
    exists_flat_stage D c hc f (pullback.fst (D.map e2) (pullback.fst (D.map e) p)) hp2 hsq2 F2 F
      eF2 hF
  obtain ⟨g3, hsq3, hg3⟩ := exists_isPullback_transport D c e3
    (pullback.fst (D.map e2) (pullback.fst (D.map e) p)) f g2 hsq2
  refine ⟨l, _, pullback.fst (D.map e3) (pullback.fst (D.map e2) (pullback.fst (D.map e) p)), g3,
    (Scheme.Modules.pullback
      (pullback.snd (D.map e3) (pullback.fst (D.map e2) (pullback.fst (D.map e) p)))).obj F2,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (D.map e3) _).flip hprop2,
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback (D.map e3) _).flip hp2,
    Stacks.Modules.isFinitePresentation_pullback _ F2 hF2, hfl, hsq3, ⟨?_⟩⟩
  exact eF2 ≪≫ (Scheme.Modules.pullbackCongr hg3.symm).app F2 ≪≫
    ((Scheme.Modules.pullbackComp g3 _).app F2).symm

end Stages

/-- **Noetherian approximation of a proper flat family over an affine base.** Let `V` be an
affine scheme, `f : X ⟶ V` proper and of finite presentation and `F` an `𝒪_X`-module of finite
presentation, flat over `V`. Then there is a Noetherian scheme `T`, a morphism `g : V ⟶ T`, a
proper morphism of finite presentation `f₀ : X₀ ⟶ T` with `X = X₀ ×_T V`, and an
`𝒪_{X₀}`-module `F₀` of finite presentation, flat over `T`, whose pullback to `X` is `F`. -/
theorem exists_noetherianModel {V X : Scheme.{u}} [IsAffine V] (f : X ⟶ V) [IsProper f]
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    ∃ (T X₀ : Scheme.{u}) (_ : IsNoetherian T) (g : V ⟶ T) (f₀ : X₀ ⟶ T) (g' : X ⟶ X₀)
      (F₀ : X₀.Modules), IsProper f₀ ∧ FinitePresentation f₀ ∧ F₀.IsFinitePresentation ∧
        IsFlatOver f₀.toLRSHom.toShHom F₀ ∧ IsPullback g' f f₀ g ∧
          Nonempty (F ≅ (Scheme.Modules.pullback g').obj F₀) := by
  let D := specAdjoinFinsetDiagram Γ(V, ⊤)
  let c : Cone D := (specAdjoinFinsetCone Γ(V, ⊤)).extend V.isoSpec.hom
  have hc : IsLimit c := IsLimit.ofIsoLimit (isLimit_specAdjoinFinsetCone Γ(V, ⊤))
    (Cone.extendIso (specAdjoinFinsetCone Γ(V, ⊤)) (V.isoSpec.symm : _ ≅ V))
  have : ∀ i, IsNoetherian (D.obj i) := fun i =>
    isNoetherian_specAdjoinFinsetDiagram_obj Γ(V, ⊤) i
  have : ∀ {i j} (e : i ⟶ j), IsAffineHom (D.map e) := fun e =>
    isAffineHom_specAdjoinFinsetDiagram_map Γ(V, ⊤) e
  obtain ⟨l, X₀, f₀, g', F₀, h⟩ := exists_model_stage D c hc f hf F hF
  exact ⟨D.obj l, X₀, inferInstance, c.π.app l, f₀, g', F₀, h⟩

end AlgebraicGeometry.ProperFlatPerfection
