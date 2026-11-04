module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesPushforward.ClosedImmersionCoverings
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartCoverDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartLocalFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardFullyFaithful
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of small étale charts along a closed immersion of algebraic spaces

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`. Base change
of étale scheme charts along `f` is the functor `AlgebraicGeometry.Space.smallBaseChange` of
Stacks 03G2, part (4). This file proves Stacks 04E3 with lifts of bounded size, the transitivity
of chart base change, and that the graph of a morphism of base-changed charts is an étale
section, and deduces the full-faithfulness assertions of Stacks 04E5 for a closed immersion `f`.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeCompIso` is the transitivity isomorphism of chart base
  change.
* `AlgebraicGeometry.Space.chartHomGraph` is the graph of a morphism of base-changed charts: the
  morphism `X ×_Y U ⟶ U ×_Y V` it determines, and
  `AlgebraicGeometry.Space.chartHomGraphSection` the section of
  `(U ×_Y V) ×_U (X ×_Y U) ⟶ X ×_Y U` built from it.

## Main results

* `AlgebraicGeometry.exists_etale_bounded_zariskiCover_baseChange_of_isClosedImmersion` is
  **Stacks 04E3** with each lift additionally of size below the cutoff.
* `AlgebraicGeometry.Space.isPullback_yoneda_pullback_chart`: the fibre product presenting the
  transitivity isomorphism is a base change of `f`.
* `AlgebraicGeometry.Space.chartBaseChangeCompIso_hom_snd` and
  `AlgebraicGeometry.Space.yoneda_chartBaseChangeCompIso_hom_fst`: the transitivity isomorphism
  is compatible with the projection to the factoring chart and with the structure morphism to
  `X`.
* `AlgebraicGeometry.Space.etale_chartHomGraphSection`: the graph section is étale.
* `AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion` and
  `AlgebraicGeometry.Space.smallEtalePullbackPushforwardCounitIso` are **Stacks 04E5, part (1)**:
  the direct image of sheaves of sets along a closed immersion is fully faithful, with the
  inverse image a left inverse of it.
* `AlgebraicGeometry.Space.fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion` and
  `AlgebraicGeometry.Space.smallEtaleAbelianPullbackPushforwardCounitIso` are the
  full-faithfulness and left-inverse assertions of **Stacks 04E5, part (2)**, for sheaves of
  abelian groups.

## References

* [Stacks Project, Tag 04E3](https://stacks.math.columbia.edu/tag/04E3)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

/-! ### Lifting étale schemes across a closed immersion, with bounded lifts -/

/-- **Stacks 04E3 with bounded lifts.** Let `i : Z ⟶ P` be a closed immersion of schemes with
`P` of size below a strong prelimit cardinal `κ > ℵ₀`, and let `p : U ⟶ Z` be étale. Then `U` has
a Zariski covering by base changes along `i` of étale schemes over `P`, each of which is itself
of size below `κ`, so lies in the size-bounded category `Sch_κ`. -/
@[ega "IV 18.1.1" "special case"]
theorem exists_etale_bounded_zariskiCover_baseChange_of_isClosedImmersion
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    {Z P U : Scheme.{u}} (i : Z ⟶ P) (hi : IsClosedImmersion i) (hP : P.size < κ)
    (p : U ⟶ Z) (hp : Etale p) :
    ∃ (J : Type u) (V : J → Scheme.{u}) (q : ∀ j, V j ⟶ P)
      (g : ∀ j, pullback (q j) i ⟶ U),
      (∀ j, Etale (q j)) ∧ (∀ j, (V j).size < κ) ∧
        (∀ j, g j ≫ p = pullback.snd (q j) i) ∧
          Presieve.ofArrows (fun j ↦ pullback (q j) i) g ∈ Scheme.zariskiPrecoverage U := by
  classical
  have : IsClosedImmersion i := hi
  have : Etale p := hp
  obtain ⟨J₀, V₀, q₀, g₀, hq₀, hgp₀, hcov₀⟩ :=
    exists_etale_zariskiCover_baseChange_of_isClosedImmersion i p
  rw [Scheme.ofArrows_mem_precoverage_iff] at hcov₀
  have : ∀ j, Etale (q₀ j) := hq₀
  refine ⟨Σ j : J₀, (V₀ j).affineOpenCover.I₀,
    fun k ↦ Spec ((V₀ k.1).affineOpenCover.X k.2),
    fun k ↦ (V₀ k.1).affineOpenCover.f k.2 ≫ q₀ k.1,
    fun k ↦ (pullbackRightPullbackFstIso (q₀ k.1) i ((V₀ k.1).affineOpenCover.f k.2)).inv ≫
      pullback.snd ((V₀ k.1).affineOpenCover.f k.2) (pullback.fst (q₀ k.1) i) ≫ g₀ k.1,
    fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_, ?_⟩
  · infer_instance
  · have : Etale ((V₀ k.1).affineOpenCover.f k.2 ≫ q₀ k.1) := inferInstance
    exact Scheme.size_lt_of_locallyOfFiniteType_of_affineCover hκ hsl
      ((V₀ k.1).affineOpenCover.f k.2 ≫ q₀ k.1)
      (I := PUnit.{u + 1}) (fun _ ↦ ⟨⊤, isAffineOpen_top _⟩) (by simp)
      ((le_of_eq mk_punit).trans (one_le_aleph0.trans
        (P.aleph0_le_size.trans (self_le_power _ one_le_aleph0)))) hP
  · rw [Category.assoc, Category.assoc, hgp₀ k.1]
    exact pullbackRightPullbackFstIso_inv_snd_snd (q₀ k.1) i ((V₀ k.1).affineOpenCover.f k.2)
  · rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun k ↦ ?_⟩
    · obtain ⟨j, y, hy⟩ := hcov₀.1 x
      obtain ⟨z, hz⟩ := (V₀ j).affineOpenCover.covers (pullback.fst (q₀ j) i y)
      obtain ⟨w, hw⟩ := Scheme.IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
        (P := @IsOpenImmersion)
        ((V₀ j).affineOpenCover.map_prop
          ((V₀ j).affineOpenCover.idx (pullback.fst (q₀ j) i y))) z y hz
      refine ⟨⟨j, (V₀ j).affineOpenCover.idx (pullback.fst (q₀ j) i y)⟩,
        (pullbackRightPullbackFstIso (q₀ j) i
          ((V₀ j).affineOpenCover.f
            ((V₀ j).affineOpenCover.idx (pullback.fst (q₀ j) i y)))).hom w, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
        Scheme.Hom.comp_apply, hw, hy]
    · have : IsOpenImmersion (g₀ k.1) := hcov₀.2 k.1
      have : IsOpenImmersion ((V₀ k.1).affineOpenCover.f k.2) :=
        (V₀ k.1).affineOpenCover.map_prop k.2
      infer_instance

/-! ### Transitivity of chart base change -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- For a representable morphism `f : X ⟶ Y` of algebraic spaces, an étale scheme chart `V` of
`Y` and a morphism `v : V' ⟶ V` of the big fppf site of `S`, the fibre product of `v` with the
cartesian projection `X ×_Y V ⟶ V` of Stacks 03G2, part (4) is a base change of `f` along the
chart `V' ⟶ V ⟶ Y`. -/
theorem isPullback_yoneda_pullback_chart (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    {V' : BigFppfOver B S hS} (v : V' ⟶ V.1.left) :
    IsPullback (yoneda.map (pullback.snd v (hf.snd V.1.hom)) ≫ hf.fst V.1.hom)
      (yoneda.map (pullback.fst v (hf.snd V.1.hom))) f.hom (yoneda.map v ≫ V.1.hom) :=
  ((IsPullback.of_hasPullback v (hf.snd V.1.hom)).flip.map yoneda).paste_horiz
    (hf.isPullback V.1.hom)

/-- **Transitivity of chart base change.** For a representable morphism `f : X ⟶ Y` of algebraic
spaces, an étale scheme chart `V` of `Y` and a morphism `v : V' ⟶ V` of the big fppf site of `S`,
the base change along `f` of the chart `V' ⟶ V ⟶ Y` is the fibre product of `v` with the
cartesian projection `X ×_Y V ⟶ V`. -/
noncomputable def chartBaseChangeCompIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    {V' : BigFppfOver B S hS} (v : V' ⟶ V.1.left) :
    pullback v (hf.snd V.1.hom) ≅ hf.pullback (yoneda.map v ≫ V.1.hom) :=
  yoneda.preimageIso ((isPullback_yoneda_pullback_chart B S hS f hf V v).isoIsPullback _ _
    (hf.isPullback (yoneda.map v ≫ V.1.hom)))

/-- `AlgebraicGeometry.Space.chartBaseChangeCompIso` is compatible with the projections to the
factoring object `V'`. -/
theorem chartBaseChangeCompIso_hom_snd (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    {V' : BigFppfOver B S hS} (v : V' ⟶ V.1.left) :
    (chartBaseChangeCompIso B S hS f hf V v).hom ≫ hf.snd (yoneda.map v ≫ V.1.hom) =
      pullback.fst v (hf.snd V.1.hom) :=
  yoneda.map_injective (by
    rw [Functor.map_comp, chartBaseChangeCompIso, Functor.preimageIso_hom, Functor.map_preimage]
    exact (isPullback_yoneda_pullback_chart B S hS f hf V v).isoIsPullback_hom_snd _ _
      (hf.isPullback (yoneda.map v ≫ V.1.hom)))

/-- `AlgebraicGeometry.Space.chartBaseChangeCompIso` is a morphism over `X`: it identifies the
structure morphism of the fibre product with that of the base-changed chart. -/
theorem yoneda_chartBaseChangeCompIso_hom_fst (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    {V' : BigFppfOver B S hS} (v : V' ⟶ V.1.left) :
    yoneda.map (chartBaseChangeCompIso B S hS f hf V v).hom ≫
        hf.fst (yoneda.map v ≫ V.1.hom) =
      yoneda.map (pullback.snd v (hf.snd V.1.hom)) ≫ hf.fst V.1.hom := by
  rw [chartBaseChangeCompIso, Functor.preimageIso_hom, Functor.map_preimage]
  exact (isPullback_yoneda_pullback_chart B S hS f hf V v).isoIsPullback_hom_fst _ _
    (hf.isPullback (yoneda.map v ≫ V.1.hom))
/-! ### The graph of a morphism of base-changed charts -/

/-- For a morphism `φ` of charts base changed along `f` from two charts `U` and `V` of `Y`,
composing `φ` with the cartesian projection to `V` gives a morphism to `V` agreeing over `Y` with
the cartesian projection to `U`. -/
theorem chartHomGraph_cond (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {U V : SmallEtale B S hS Y.1}
    (φ : (smallBaseChange B S hS f hf).obj U ⟶ (smallBaseChange B S hS f hf).obj V) :
    yoneda.map (φ.1.left ≫ hf.snd V.1.hom) ≫ V.1.hom =
      yoneda.map (hf.snd U.1.hom) ≫ U.1.hom :=
  have hw : yoneda.map φ.1.left ≫ hf.fst V.1.hom = hf.fst U.1.hom := CostructuredArrow.w φ.1
  have e1 : yoneda.map (φ.1.left ≫ hf.snd V.1.hom) =
      yoneda.map φ.1.left ≫ yoneda.map (hf.snd V.1.hom) := Functor.map_comp _ _ _
  ((congrArg (fun t ↦ t ≫ V.1.hom) e1).trans (Category.assoc _ _ _)).trans
    (((congrArg (fun t ↦ yoneda.map φ.1.left ≫ t) (hf.w V.1.hom).symm).trans
      (Category.assoc _ _ _).symm).trans
        ((congrArg (fun t ↦ t ≫ f.hom) hw).trans (hf.w U.1.hom)))

/-- **The graph of a morphism of base-changed charts.** For a representable morphism
`f : X ⟶ Y` of algebraic spaces and two étale scheme charts `U` and `V` of `Y`, a morphism
`φ : X ×_Y U ⟶ X ×_Y V` of the base-changed charts of Stacks 03G2, part (4) determines a
morphism `X ×_Y U ⟶ U ×_Y V` whose two components are the cartesian projection to `U` and the
composite of `φ` with the cartesian projection to `V`. -/
noncomputable def chartHomGraph (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {U V : SmallEtale B S hS Y.1}
    (φ : (smallBaseChange B S hS f hf).obj U ⟶ (smallBaseChange B S hS f hf).obj V) :
    ((smallBaseChange B S hS f hf).obj U).1.left ⟶ V.property.rep.pullback U.1.hom :=
  V.property.rep.lift' (φ.1.left ≫ hf.snd V.1.hom) (hf.snd U.1.hom)
    (chartHomGraph_cond B S hS f hf φ)

/-- The component of `AlgebraicGeometry.Space.chartHomGraph` along the projection of `U ×_Y V`
to `V` is `φ` followed by the cartesian projection of `X ×_Y V` to `V`. -/
theorem chartHomGraph_fst' (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {U V : SmallEtale B S hS Y.1}
    (φ : (smallBaseChange B S hS f hf).obj U ⟶ (smallBaseChange B S hS f hf).obj V) :
    chartHomGraph B S hS f hf φ ≫ V.property.rep.fst' U.1.hom =
      φ.1.left ≫ hf.snd V.1.hom :=
  V.property.rep.lift'_fst _ _ (chartHomGraph_cond B S hS f hf φ)

/-- The component of `AlgebraicGeometry.Space.chartHomGraph` along the projection of `U ×_Y V`
to `U` is the cartesian projection of `X ×_Y U` to `U`. -/
theorem chartHomGraph_snd (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {U V : SmallEtale B S hS Y.1}
    (φ : (smallBaseChange B S hS f hf).obj U ⟶ (smallBaseChange B S hS f hf).obj V) :
    chartHomGraph B S hS f hf φ ≫ V.property.rep.snd U.1.hom = hf.snd U.1.hom :=
  V.property.rep.lift'_snd _ _ (chartHomGraph_cond B S hS f hf φ)

/-- **A morphism of base-changed charts as a section.** The graph of
`φ : X ×_Y U ⟶ X ×_Y V` of `AlgebraicGeometry.Space.chartHomGraph`, paired with the identity,
is a section of the cartesian projection `(U ×_Y V) ×_U (X ×_Y U) ⟶ X ×_Y U`. -/
noncomputable def chartHomGraphSection (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {U V : SmallEtale B S hS Y.1}
    (φ : (smallBaseChange B S hS f hf).obj U ⟶ (smallBaseChange B S hS f hf).obj V) :
    ((smallBaseChange B S hS f hf).obj U).1.left ⟶
      pullback (V.property.rep.snd U.1.hom) (hf.snd U.1.hom) :=
  pullback.lift (chartHomGraph B S hS f hf φ) (𝟙 _)
    ((chartHomGraph_snd B S hS f hf φ).trans (Category.id_comp _).symm)

/-- `AlgebraicGeometry.Space.chartHomGraphSection` has the graph as its component along the
projection to `U ×_Y V`. -/
theorem chartHomGraphSection_fst (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {U V : SmallEtale B S hS Y.1}
    (φ : (smallBaseChange B S hS f hf).obj U ⟶ (smallBaseChange B S hS f hf).obj V) :
    chartHomGraphSection B S hS f hf φ ≫
        pullback.fst (V.property.rep.snd U.1.hom) (hf.snd U.1.hom) =
      chartHomGraph B S hS f hf φ :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.Space.chartHomGraphSection` is a section of the cartesian projection to
`X ×_Y U`. -/
theorem chartHomGraphSection_snd (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {U V : SmallEtale B S hS Y.1}
    (φ : (smallBaseChange B S hS f hf).obj U ⟶ (smallBaseChange B S hS f hf).obj V) :
    chartHomGraphSection B S hS f hf φ ≫
        pullback.snd (V.property.rep.snd U.1.hom) (hf.snd U.1.hom) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The graph section `AlgebraicGeometry.Space.chartHomGraphSection` of a morphism of
base-changed charts is étale. -/
theorem etale_chartHomGraphSection (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {U V : SmallEtale B S hS Y.1}
    (φ : (smallBaseChange B S hS f hf).obj U ⟶ (smallBaseChange B S hS f hf).obj V) :
    Etale ((BigFppfOver.toScheme B S hS).map (chartHomGraphSection B S hS f hf φ)) := by
  have hpb := (IsPullback.of_hasPullback (V.property.rep.snd U.1.hom)
    (hf.snd U.1.hom)).map (BigFppfOver.toScheme B S hS)
  have hsndet : Etale ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (V.property.rep.snd U.1.hom) (hf.snd U.1.hom))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb (V.property.property_snd U.1.hom)
  have hone : Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj
    ((smallBaseChange B S hS f hf).obj U).1.left)) := inferInstance
  refine MorphismProperty.of_postcomp (W := @AlgebraicGeometry.Etale.{u})
    (W' := @AlgebraicGeometry.Etale.{u})
    ((BigFppfOver.toScheme B S hS).map (chartHomGraphSection B S hS f hf φ))
    ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (V.property.rep.snd U.1.hom) (hf.snd U.1.hom))) hsndet ?_
  have hid : (BigFppfOver.toScheme B S hS).map (chartHomGraphSection B S hS f hf φ) ≫
      (BigFppfOver.toScheme B S hS).map
        (pullback.snd (V.property.rep.snd U.1.hom) (hf.snd U.1.hom)) = 𝟙 _ :=
    (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (fun t ↦ (BigFppfOver.toScheme B S hS).map t)
        (chartHomGraphSection_snd B S hS f hf φ))).trans
          ((BigFppfOver.toScheme B S hS).map_id _)
  rw [hid]
  exact hone


/-! ### The full-faithfulness assertions of Stacks 04E5 -/

/-- **Stacks 04E5, part (1).** For a closed immersion `f : X ⟶ Y` of algebraic spaces over `S`,
the direct image of sheaves of sets along the morphism of small étale topoi of Stacks 03G2,
part (3) is fully faithful. -/
@[stacks 04E5 "part (1): full faithfulness on sheaves of sets", sga "4 VIII 6.3" "fully faithful"]
noncomputable def fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    (smallToposMorphismTypeU B S hS f).pushforward.FullyFaithful :=
  fullyFaithfulSmallEtalePushforward B S hS f hf.rep
    (smallBaseChange_isCoverDense_of_isClosedImmersion B S hS f hf)
    (smallBaseChange_isLocallyFull_of_isClosedImmersion B S hS f hf)

/-- **Stacks 04E5, part (1).** For a closed immersion `f : X ⟶ Y` of algebraic spaces over `S`
the inverse image of sheaves of sets is a *left inverse* of the direct image: the counit
`f^{-1}f_*G ⟶ G` of the adjunction of the morphism of small étale topoi of Stacks 03G2, part (3)
is an isomorphism for every sheaf `G` on the small étale site of `X`. -/
@[stacks 04E5 "part (1): inverse image is a left inverse", sga "4 VIII 5.7" "partial"]
noncomputable def smallEtalePullbackPushforwardCounitIso (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    (smallToposMorphismTypeU B S hS f).pushforward ⋙
        (smallToposMorphismTypeU B S hS f).inverseImage ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :=
  have := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS f hf).full
  have := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS f hf).faithful
  asIso (smallToposMorphismTypeU B S hS f).adj.counit

/-- **Stacks 04E5, part (2), full faithfulness.** For a closed immersion `f : X ⟶ Y` of algebraic
spaces over `S`, the direct image of sheaves of *abelian groups* along `f` — restriction along
the chart base-change morphism of small étale sites of Stacks 03G2, part (4) — is fully faithful.
-/
@[stacks 04E5 "part (2): full faithfulness on abelian sheaves"]
noncomputable def fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hf.rep).toIsContinuous
    ((smallBaseChange B S hS f hf.rep).sheafPushforwardContinuous AddCommGrpCat.{w}
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).FullyFaithful :=
  fullyFaithfulSmallEtaleRestriction B S hS AddCommGrpCat.{w} f hf.rep
    (smallBaseChange_isCoverDense_of_isClosedImmersion B S hS f hf)
    (smallBaseChange_isLocallyFull_of_isClosedImmersion B S hS f hf)

/-- **Stacks 04E5, part (2).** For a closed immersion `f : X ⟶ Y` of algebraic spaces over `S`
the inverse image of sheaves of abelian groups is a *left inverse* of the direct image: the
counit of the adjunction of `CategoryTheory.Functor.sheafAdjunctionContinuous` for chart base
change is a natural isomorphism `f_* ⋙ f^{-1} ≅ 𝟭`. The abelian groups are taken at the
universe `u + 1`, at which the small étale site has sheafification. -/
@[stacks 04E5 "part (2): inverse image is a left inverse", sga "4 VIII 5.7" "partial"]
noncomputable def smallEtaleAbelianPullbackPushforwardCounitIso (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hf.rep).toIsContinuous
    letI : ((smallBaseChange B S hS f hf.rep).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).IsRightAdjoint :=
      inferInstance
    (smallBaseChange B S hS f hf.rep).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) ⋙
      (smallBaseChange B S hS f hf.rep).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) := by
  letI := (smallBaseChange_isMorphismOfSites B S hS f hf.rep).toIsContinuous
  letI : ((smallBaseChange B S hS f hf.rep).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).IsRightAdjoint :=
    inferInstance
  have hff := fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS f hf
  have := hff.full
  have := hff.faithful
  exact asIso ((smallBaseChange B S hS f hf.rep).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).counit

end Space

end AlgebraicGeometry

end
