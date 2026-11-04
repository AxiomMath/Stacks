module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.NormalizedBlowupEtaleBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalized blowup of a scheme at a closed point, read as an algebraic space

Let `W` be a locally Noetherian scheme of the big fppf site over `S` and let `w ∈ W` be a closed
point. The normalized blowing up of the algebraic space `h_W` at the point corresponding to `w`
is represented by the normalized blowup `Stacks.Blowup.normalizedBlowUpScheme W w` of the scheme,
compatibly with the morphisms to `W`. This is the comparison through which a resolution of a
scheme by normalized blowups at closed points (Stacks 0BGL) is read as a resolution of the
algebraic space it represents (Stacks 0BHX).

## Main results

* `AlgebraicGeometry.Space.reesChartIdeal_selfPresentation_closedPointSubspace`: on a scheme the
  defining ideal of the reduced closed subspace on a closed point is the vanishing ideal of the
  point.
* `AlgebraicGeometry.Space.exists_iso_schemeSpace_blowUp_of_isBlowupAtClosedPoint`: the blowing
  up of `h_W` at the point is represented by the blowup of `W` at `w`.
* `AlgebraicGeometry.Space.exists_iso_schemeSpace_normalizedBlowUpScheme`: the normalized blowing
  up of `h_W` at the point is represented by `Stacks.Blowup.normalizedBlowUpScheme W w`.

## References

* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
* [Stacks Project, Tag 0BHX](https://stacks.math.columbia.edu/tag/0BHX)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The points of a represented algebraic space -/

/-- The point of the algebraic space `h_W` corresponding to a point of the scheme `W`. -/
abbrev schemeSpacePoint (W : BigFppfOver B S hS) (w : (BigFppfOver.toScheme B S hS).obj W) :
    points B S hS (schemeSpace W).obj :=
  (pointsEquivScheme B S hS W).symm w

/-- A closed point of a scheme of the site is a closed point of the algebraic space it
represents. -/
theorem isClosed_singleton_schemeSpacePoint (W : BigFppfOver B S hS)
    {w : (BigFppfOver.toScheme B S hS).obj W} (hw : IsClosed ({w} : Set _)) :
    IsClosed ({schemeSpacePoint W w} : Set (points B S hS (schemeSpace W).obj)) := by
  have h := (schemePointsHomeomorph B S hS W).symm.isClosedMap _ hw
  rwa [Set.image_singleton] at h

/-- A point of a scheme of the site is closed if the corresponding point of the algebraic space
it represents is. -/
theorem isClosed_singleton_of_isClosed_schemeSpacePoint (W : BigFppfOver B S hS)
    {w : (BigFppfOver.toScheme B S hS).obj W}
    (hw : IsClosed ({schemeSpacePoint W w} : Set (points B S hS (yoneda.obj W)))) :
    IsClosed ({w} : Set ((BigFppfOver.toScheme B S hS).obj W)) := by
  have h := (schemePointsHomeomorph B S hS W).isClosedMap _ hw
  have he : schemePointsHomeomorph B S hS W (schemeSpacePoint W w) = w :=
    (pointsEquivScheme B S hS W).apply_symm_apply w
  exact (congrArg IsClosed (Set.image_singleton.trans (congrArg ({·}) he))).mp h

/-- An étale-local property of schemes holds on the algebraic space of a scheme with the
property: the identity is a surjective étale chart. -/
theorem hasEtaleLocalProperty_schemeSpace (W : BigFppfOver B S hS) {P : ObjectProperty Scheme.{u}}
    (hP : P ((BigFppfOver.toScheme B S hS).obj W)) :
    HasEtaleLocalProperty B S hS (schemeSpace W).obj P :=
  ⟨W, 𝟙 _, (selfPresentation B S hS W).surjective, (selfPresentation B S hS W).etale, hP⟩

/-! ### The centre of the blowing up at a closed point of a scheme -/

/-- Over the identity chart of a scheme, the first projection of a representing closed immersion
is an isomorphism. -/
private theorem isIso_fst_rep_selfPresentation (W : BigFppfOver B S hS)
    (Z : ClosedSubspaces B S hS (schemeSpace W).obj) :
    IsIso (Z.2.2.rep.fst (selfPresentation B S hS W).toSpace) :=
  have : IsIso (selfPresentation B S hS W).toSpace := IsIso.id _
  (Z.2.2.rep.isPullback _).isIso_fst_of_isIso

/-- On a scheme, the closed immersion representing the reduced closed subspace on a closed point
over the identity chart has image the point. -/
theorem range_base_rep_snd_selfPresentation_closedPointSubspace (W : BigFppfOver B S hS)
    {w : (BigFppfOver.toScheme B S hS).obj W} (hw : IsClosed ({w} : Set _)) :
    Set.range ((BigFppfOver.toScheme B S hS).map
      ((closedPointSubspace B S hS (schemeSpacePoint W w)
        (isClosed_singleton_schemeSpacePoint W hw)).2.2.rep.snd
          (selfPresentation B S hS W).toSpace)).base = {w} := by
  set Z := closedPointSubspace B S hS (schemeSpacePoint W w)
    (isClosed_singleton_schemeSpacePoint W hw)
  set φ := (selfPresentation B S hS W).toSpace with hφdef
  set hrep := Z.2.2.rep
  have hsq : IsPullback (hrep.fst φ) (yoneda.map (hrep.snd φ)) Z.1.ι φ := hrep.isPullback φ
  have hfst : IsIso (hrep.fst φ) := isIso_fst_rep_selfPresentation W Z
  have hpts : ∀ x, pointsMap B S hS _ (yoneda.map (hrep.snd φ)) x = schemeSpacePoint W w := by
    intro x
    have h2 : yoneda.map (hrep.snd φ) ≫ φ = hrep.fst φ ≫ Z.1.ι := hsq.w.symm
    have h3 := congrArg (fun k => pointsMap B S hS _ k x) h2
    simp only [pointsMap_comp_apply] at h3
    have h4 : pointsMap B S hS _ φ = id := by
      rw [hφdef]
      exact pointsMap_id B S hS _
    rw [h4] at h3
    have h5 := Set.mem_range_self (f := pointsMap B S hS Z.1.toFunctor Z.1.ι)
      (pointsMap B S hS _ (hrep.fst φ) x)
    rw [range_pointsMap_ι_closedPointSubspace] at h5
    exact h3.trans h5
  have hmap := pointsMap_yoneda_map_eq B S hS (hrep.snd φ)
  have hconst : ∀ c, ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).base c = w := fun c => by
    have h := congrFun hmap ((pointsEquivScheme B S hS _).symm c)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
    rw [hpts] at h
    exact ((pointsEquivScheme B S hS W).symm.injective h).symm
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, by rintro _ ⟨c, rfl⟩; exact hconst c⟩
  obtain ⟨x⟩ : Nonempty (points B S hS (yoneda.obj (hrep.pullback φ))) := by
    obtain ⟨z, hz⟩ : schemeSpacePoint W w ∈
        Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
      rw [range_pointsMap_ι_closedPointSubspace]
      rfl
    exact (pointsMap_surjective_of_isIso B S hS (hrep.fst φ) z).nonempty
  exact ⟨pointsEquivScheme B S hS _ x, hconst _⟩

/-- **On a scheme, the defining ideal of the reduced closed subspace on a closed point is the
vanishing ideal of the point.** The ideal is the kernel of the closed immersion representing the
subspace on the identity chart, whose source is reduced and whose image is the point; a quasi-
coherent ideal is determined by its support once its closed subscheme is reduced. -/
theorem reesChartIdeal_selfPresentation_closedPointSubspace (W : BigFppfOver B S hS)
    {w : (BigFppfOver.toScheme B S hS).obj W} (hw : IsClosed ({w} : Set _)) :
    reesChartIdeal (centreIdeal (closedPointSubspace B S hS (schemeSpacePoint W w)
        (isClosed_singleton_schemeSpacePoint W hw)))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS W) =
      Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _) := by
  set Z := closedPointSubspace B S hS (schemeSpacePoint W w)
    (isClosed_singleton_schemeSpacePoint W hw)
  rw [← ker_rep_snd_eq_reesChartIdeal B S hS (schemeSpace W) Z (selfPresentation B S hS W)]
  set φ := (selfPresentation B S hS W).toSpace
  set hrep := Z.2.2.rep
  set g := (BigFppfOver.toScheme B S hS).map (hrep.snd φ)
  have hg : AlgebraicGeometry.IsClosedImmersion g := Z.2.2.property_snd φ
  have hfst : IsIso (hrep.fst φ) := isIso_fst_rep_selfPresentation W Z
  have hZred : HasEtaleLocalProperty B S hS Z.1.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS (schemeSpace W).obj
      (schemeSpace W).property _ _
  have hfstet : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (hrep.fst φ) :=
    presheaf_etale_of_isEtale B S hS (isEtale_of_isIso B S hS _)
  have hsrc : IsReduced ((BigFppfOver.toScheme B S hS).obj (hrep.pullback φ)) :=
    (exists_atlas_iff_forall_etale B S hS Z.1.toFunctor (fun Y : Scheme.{u} => IsReduced Y)
      Z.2.1).mp hZred _ _ hfstet
  have hker : IsReduced g.ker.subscheme :=
    ObjectProperty.prop_of_iso (P := fun Y : Scheme.{u} => IsReduced Y) (asIso g.toImage) hsrc
  have hrange : Set.range g.base = {w} :=
    range_base_rep_snd_selfPresentation_closedPointSubspace W hw
  refine Scheme.IdealSheafData.eq_of_isReduced_subscheme_of_support_eq _ _ hker
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _) ?_
  apply SetLike.coe_injective
  rw [Scheme.Hom.support_ker, hrange, hw.closure_eq]
  ext x
  simp

/-! ### The blowing up at a closed point of a scheme -/

/-- The relative `Proj` of the Rees algebra of a quasi-coherent ideal is the blowup of the scheme
in an equal ideal, over the base. -/
@[sga "6 VII 1.8"]
theorem exists_iso_relativeProj_reesSituation_blowUp {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : I = J) :
    ∃ ψ : (Stacks.Blowup.reesSituation I).relativeProj ≅ AlgebraicGeometry.blowUp J,
      ψ.hom ≫ AlgebraicGeometry.blowUpToBase J =
        (Stacks.Blowup.reesSituation I).relativeProjToBase := by
  subst h
  exact ⟨Stacks.Blowup.reesSituationBlowUpIso I,
    Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase I⟩

/-- The identity of the algebraic space of a scheme pulls the reduced closed subspace on a closed
point back to itself. -/
theorem preimageClosedSubspace_id_closedPointSubspace (X : AlgebraicSpaces B S hS)
    {x : points B S hS X.obj} (hx : IsClosed ({x} : Set (points B S hS X.obj))) :
    preimageClosedSubspace (𝟙 X) (closedPointSubspace B S hS x hx) =
      closedPointSubspace B S hS x hx := by
  refine preimageClosedSubspace_closedPointSubspace (𝟙 X) (isEtale_id B S hS X.obj) hx hx ?_
  change pointsMap B S hS X.obj (𝟙 X.obj) ⁻¹' {x} = {x}
  rw [pointsMap_id]
  rfl

/-- **The blowing up of a represented algebraic space at a closed point is represented by the
blowup of the scheme at the point**, compatibly with the morphisms to the scheme. The blowup of
Stacks 085Q of the algebraic space `h_W`, built from its own presentation, is the relative `Proj`
of the Rees algebra of the ideal it induces on `W`, and that ideal is the vanishing ideal of the
point by `AlgebraicGeometry.Space.reesChartIdeal_selfPresentation_closedPointSubspace`. -/
theorem exists_iso_schemeSpace_blowUp_of_isBlowupAtClosedPoint
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (W : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    {w : (BigFppfOver.toScheme B S hS).obj W} (hw : IsClosed ({w} : Set _))
    {X' : AlgebraicSpaces B S hS} {b : X' ⟶ schemeSpace W}
    (hb : IsBlowupAtClosedPoint B S hS (schemeSpacePoint W w)
      (isClosed_singleton_schemeSpacePoint W hw) b) :
    ∃ (N : BigFppfOver B S hS) (q : N ⟶ W) (e : X' ≅ schemeSpace N)
      (ψ : (BigFppfOver.toScheme B S hS).obj N ≅
        AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _))),
      e.hom ≫ schemeSpaceMap q = b ∧
        (BigFppfOver.toScheme B S hS).map q = ψ.hom ≫ AlgebraicGeometry.blowUpToBase _ := by
  set Z := closedPointSubspace B S hS (schemeSpacePoint W w)
    (isClosed_singleton_schemeSpacePoint W hw)
  obtain ⟨hcU, hcR, hcRR⟩ := contains_reesSituations_of_isLocallyNoetherian
    (hasEtaleLocalProperty_schemeSpace W ‹_›) (preimageClosedSubspace (𝟙 (schemeSpace W)) Z)
    (selfPresentation B S hS W)
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb.isBlowupAlong W
    (a := 𝟙 (schemeSpace W)) (isEtale_id B S hS _) hcU hcR hcRR (IsPullback.of_id_snd (f := b))
  have hI : reesChartIdeal (centreIdeal (preimageClosedSubspace (𝟙 (schemeSpace W)) Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS W) =
      Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _) := by
    rw [preimageClosedSubspace_id_closedPointSubspace]
    exact reesChartIdeal_selfPresentation_closedPointSubspace W hw
  obtain ⟨ψ, hψ⟩ := exists_iso_relativeProj_reesSituation_blowUp _ _ hI
  exact ⟨_, _, e, ψ, he, hψ.symm⟩

/-! ### The normalized blowing up at a closed point of a scheme -/

/-- The normalization of a scheme isomorphic to a given one is isomorphic to its normalization,
compatibly with the normalization morphisms: an isomorphism is étale, and normalization commutes
with étale base change. -/
theorem exists_iso_normalizationScheme_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    ∃ ν : X.normalizationScheme hX ≅ Y.normalizationScheme hY,
      ν.hom ≫ Y.normalization hY = X.normalization hX ≫ e.hom := by
  have hpb := isPullback_normalizationSchemeMap_of_etale e.hom hY
  have : IsIso (normalizationSchemeMap e.hom
      (finite_irreducibleComponents_of_smooth e.hom hY) hY) := hpb.isIso_fst_of_isIso
  exact ⟨asIso (normalizationSchemeMap e.hom hX hY),
    normalizationSchemeMap_normalization e.hom hX hY⟩

/-- **The normalized blowing up of a represented algebraic space at a closed point is represented
by the normalized blowup of the scheme at the point** (Stacks 0BBS), compatibly with the morphisms
to the scheme. The blowing up is represented by the blowup of the scheme, by
`AlgebraicGeometry.Space.exists_iso_schemeSpace_blowUp_of_isBlowupAtClosedPoint`, and the
normalization of a represented algebraic space by the normalization of the scheme. -/
theorem exists_iso_schemeSpace_normalizedBlowUpScheme
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (W : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    (hW : ∀ V : ((BigFppfOver.toScheme B S hS).obj W).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj W)) →
        (irreducibleComponents V).Finite)
    {w : (BigFppfOver.toScheme B S hS).obj W} (hw : IsClosed ({w} : Set _))
    {X'' : AlgebraicSpaces B S hS} {g : X'' ⟶ schemeSpace W}
    (hg : IsNormalizationOfBlowupAtClosedPoint B S hS (schemeSpacePoint W w)
      (isClosed_singleton_schemeSpacePoint W hw) g) :
    ∃ (N : BigFppfOver B S hS) (q : N ⟶ W) (e : X'' ≅ schemeSpace N)
      (ψ : (BigFppfOver.toScheme B S hS).obj N ≅
        Stacks.Blowup.normalizedBlowUpScheme _ hW w hw),
      e.hom ≫ schemeSpaceMap q = g ∧
        (BigFppfOver.toScheme B S hS).map q =
          ψ.hom ≫ Stacks.Blowup.normalizedBlowUp _ hW w hw := by
  obtain ⟨X', b, hb, D, e₀, hg₀⟩ := hg
  obtain ⟨N₀, q₀, e₁, ψ₀, he₁, hq₀⟩ :=
    exists_iso_schemeSpace_blowUp_of_isBlowupAtClosedPoint W hw hb
  have hfinBl := Stacks.Blowup.finite_irreducibleComponents_blowUp
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _)) hW
  have hN₀ := finiteIrreducibleComponents_of_etale ψ₀.hom hfinBl
  have hN₀sp : HasLocallyFiniteIrreducibleComponents B S hS (schemeSpace N₀).obj :=
    (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents B S hS
      (schemeSpace N₀).property).mp
      ⟨N₀, 𝟙 _, isSurjective_id B S hS _, isEtale_id B S hS _, hN₀⟩
  obtain ⟨D₁⟩ := nonempty_normalizationData B S hS (schemeSpace N₀).property hN₀sp
  have hinv : IsIso e₁.inv.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map e₁.inv))
  obtain ⟨m, hm⟩ := D.isPullback_hom_of_isEtale D₁ X'.property
    (schemeSpace N₀).property e₁.inv.hom (isEtale_of_isIso B S hS _)
  have hmiso : IsIso m := hm.isIso_fst_of_isIso
  obtain ⟨Nν, p, ε, φ, hp, hφ⟩ := D₁.exists_iso_yoneda_normalizationScheme hN₀
  obtain ⟨ν, hν⟩ := exists_iso_normalizationScheme_of_iso ψ₀.symm hfinBl hN₀
  refine ⟨Nν, p ≫ q₀, ObjectProperty.isoMk _ (e₀ ≪≫ (asIso m).symm ≪≫ φ), ε ≪≫ ν.symm, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    change (e₀.hom ≫ inv m ≫ φ.hom) ≫ yoneda.map (p ≫ q₀) = g.hom
    have hq : (schemeSpaceMap q₀).hom = e₁.inv.hom ≫ b.hom :=
      congrArg (·.hom) (e₁.eq_inv_comp.mpr he₁)
    have key : D₁.hom ≫ (schemeSpaceMap q₀).hom = m ≫ D.hom ≫ b.hom := by
      rw [hq, ← Category.assoc, ← hm.w, Category.assoc]
    have key2 : φ.hom ≫ yoneda.map (p ≫ q₀) = D₁.hom ≫ (schemeSpaceMap q₀).hom := by
      rw [Functor.map_comp, ← Category.assoc, hφ]
      rfl
    rw [hg₀, Category.assoc, Category.assoc, key2, key]
    exact congrArg (e₀.hom ≫ ·) (IsIso.inv_hom_id_assoc m (D.hom ≫ b.hom))
  · rw [Functor.map_comp, hp, hq₀]
    have hν' : ν.inv ≫ Scheme.normalization _ hfinBl =
        Scheme.normalization ((BigFppfOver.toScheme B S hS).obj N₀) hN₀ ≫ ψ₀.hom := by
      rw [Iso.inv_comp_eq, ← Category.assoc, hν]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    have h3 := congrArg (· ≫ AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _))) hν'
    simp only [Category.assoc] at h3
    exact congrArg (ε.hom ≫ ·) h3.symm

end AlgebraicGeometry.Space
