module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Size.DiscreteValuativeCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion

/-!
# The Noetherian valuative criterion for separatedness of a morphism of algebraic spaces

A morphism of algebraic spaces over `S` which is locally of finite type and quasi-separated,
whose target is locally Noetherian, and for which every valuative square over a *discrete*
valuation ring has at most one dotted arrow, is separated.

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_isQuasiSeparated_of_discreteValuativeUniqueness`:
  **Stacks 0ARJ**.

## Implementation notes

Separatedness is the assertion that the relative diagonal is a closed immersion, which by
**Stacks 03M4** may be tested on a single surjective étale chart `h_V ⟶ X ×_Y X`. Writing
`W ⟶ V` for the morphism of the site representing the base change of the diagonal along such a
chart, the scheme morphism underlying it is a monomorphism, separated and locally of finite type
by **Stacks 03HK**, and quasi-compact because the diagonal is quasi-compact (**Stacks 03HD**);
the scheme underlying `V` is locally Noetherian because `X ×_Y X` is locally of finite type over
`Y` (**Stacks 03XG**, **Stacks 03XH**) and so locally Noetherian (**Stacks 04ZK**), a property
tested on every étale chart (**Stacks 03E8**).

A valuative square for that scheme morphism over a discrete valuation ring `A` with fraction
field `K` gives, after composing with the chart, two morphisms `Spec A ⟶ X` agreeing over `Y`
and agreeing on `Spec K`, that is, two dotted arrows of one valuative square for `f`; the
hypothesis identifies them, so the composite `Spec A ⟶ X ×_Y X` factors through the diagonal and
the square acquires a lift, unique because the diagonal is a monomorphism. The spectra of `A` and
of `K` are objects of the site by construction, which is exactly the hypothesis of
`AlgebraicGeometry.universallyClosed_of_contained_discreteValuativeCriterion`; that gives
universal closedness, hence properness, and a proper locally quasi-finite monomorphism of
schemes is a closed immersion.

## References

* [Stacks Project, Tag 0ARJ](https://stacks.math.columbia.edu/tag/0ARJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `a : T ⟶ V` into a chart of `X ×_Y X` whose two projections to `X` agree factors
through the base change `W ⟶ V` of the relative diagonal. -/
theorem exists_comp_eq_of_isPullback_diagonal {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {V W T : BigFppfOver B S hS} {chart : yoneda.obj V ⟶ pullback f f}
    {p : yoneda.obj W ⟶ X} {π : W ⟶ V}
    (hsq : IsPullback p (yoneda.map π) (pullback.diagonal f) chart) (a : T ⟶ V)
    (ha : yoneda.map a ≫ chart ≫ pullback.fst f f = yoneda.map a ≫ chart ≫ pullback.snd f f) :
    ∃ m : T ⟶ W, m ≫ π = a := by
  have hfactor : (yoneda.map a ≫ chart ≫ pullback.fst f f) ≫ pullback.diagonal f =
      yoneda.map a ≫ chart :=
    pullback.hom_ext (by simp) (by simp [ha])
  refine ⟨yoneda.preimage (hsq.lift _ (yoneda.map a) hfactor),
    Yoneda.fullyFaithful.map_injective (F := yoneda) ?_⟩
  rw [yoneda.map_comp, yoneda.map_preimage]
  exact hsq.lift_snd _ _ hfactor

/-- If every valuative square for `f` over a discrete valuation ring has at most one dotted
arrow, then a point of a chart `V` of `X ×_Y X` over a discrete valuation ring whose generic point
lies in the base change `W` of the relative diagonal has equal projections to `X`. -/
theorem chart_comp_fst_eq_snd_of_discreteValuativeUniqueness
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {V W : BigFppfOver B S hS}
    {chart : yoneda.obj V ⟶ pullback f f} {p : yoneda.obj W ⟶ X} {π : W ⟶ V}
    (hsq : IsPullback p (yoneda.map π) (pullback.diagonal f) chart)
    (hu : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R → Subsingleton q.Lift)
    {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hDVR : IsDiscreteValuationRing R) (hR : B.Contains (Spec (.of R)))
    (hK : B.Contains (Spec (.of K))) (base : Spec (.of R) ⟶ S)
    (aV : siteObject B S hS hR base ⟶ V)
    (kW : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶ W)
    (hw : (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
        B.obj hK ⟶ B.obj hR) :
      siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
        siteObject B S hS hR base) ≫ aV = kW ≫ π) :
    yoneda.map aV ≫ chart ≫ pullback.fst f f = yoneda.map aV ≫ chart ≫ pullback.snd f f := by
  have hproj (k : pullback f f ⟶ X) (hk : pullback.diagonal f ≫ k = 𝟙 X) :
      yoneda.map (kW ≫ π) ≫ chart ≫ k = yoneda.map kW ≫ p := by
    rw [Functor.map_comp_assoc, ← reassoc_of% hsq.w, hk, Category.comp_id]
  let q : ValuativeSquare f :=
    { R := R
      K := K
      ring_mem := hR
      field_mem := hK
      base := base
      generic := yoneda.map kW ≫ p
      special := (yoneda.map aV ≫ chart ≫ pullback.fst f f) ≫ f
      comm := by
        rw [← hproj _ (pullback.diagonal_fst f), ← hw]
        simp }
  let hlift (k : pullback f f ⟶ X) (hk : pullback.diagonal f ≫ k = 𝟙 X)
      (hf : k ≫ f = pullback.fst f f ≫ f) : q.Lift :=
    ⟨yoneda.map aV ≫ chart ≫ k, by rw [← Functor.map_comp_assoc, hw]; exact hproj k hk,
      by simp [q, hf]⟩
  exact congrArg ValuativeSquare.Lift.map ((hu q hDVR).allEq
    (hlift _ (pullback.diagonal_fst f) rfl)
    (hlift _ (pullback.diagonal_snd f) pullback.condition.symm))

/-- If every valuative square for `f` over a discrete valuation ring has at most one dotted
arrow, then every valuative square over a discrete valuation ring for the base change of the
relative diagonal of `f` along a chart has a lift. -/
theorem hasLift_of_isPullback_diagonal_of_discreteValuativeUniqueness
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {V W : BigFppfOver B S hS}
    {chart : yoneda.obj V ⟶ pullback f f} {p : yoneda.obj W ⟶ X} {π : W ⟶ V}
    (hsq : IsPullback p (yoneda.map π) (pullback.diagonal f) chart)
    [hπ : Mono ((BigFppfOver.toScheme B S hS).map π)]
    (hu : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R → Subsingleton q.Lift)
    (D : ValuativeCommSq ((BigFppfOver.toScheme B S hS).map π))
    (hDVR : IsDiscreteValuationRing D.R) (hR : B.Contains (Spec (.of D.R)))
    (hK : B.Contains (Spec (.of D.K))) : D.commSq.HasLift := by
  have hWhom : (B.inclusion).map W.hom =
      (BigFppfOver.toScheme B S hS).map π ≫ (B.inclusion).map V.hom := by
    conv_lhs => rw [← Over.w π]
    exact (B.inclusion).map_comp _ _
  let baseR : Spec (.of D.R) ⟶ S := D.i₂ ≫ (B.inclusion).map V.hom
  let aV : siteObject B S hS hR baseR ⟶ V :=
    Over.homMk (ObjectProperty.homMk D.i₂ : B.obj hR ⟶ V.left) rfl
  let kW : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ baseR) ⟶
      W :=
    Over.homMk (ObjectProperty.homMk D.i₁ : B.obj hK ⟶ W.left) (by
      apply ObjectProperty.hom_ext
      show D.i₁ ≫ (B.inclusion).map W.hom =
        Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ baseR
      rw [hWhom, ← Category.assoc, D.commSq.w, Category.assoc])
  obtain ⟨m, hmπ⟩ := exists_comp_eq_of_isPullback_diagonal B S hS hsq aV
    (chart_comp_fst_eq_snd_of_discreteValuativeUniqueness B S hS hsq hu hDVR hR hK baseR aV kW
      (by
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        show Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ =
          D.i₁ ≫ (BigFppfOver.toScheme B S hS).map π
        exact D.commSq.w.symm))
  have hlφ : (BigFppfOver.toScheme B S hS).map m ≫ (BigFppfOver.toScheme B S hS).map π =
      D.i₂ := by
    rw [← (BigFppfOver.toScheme B S hS).map_comp, hmπ]
    rfl
  refine ⟨⟨(BigFppfOver.toScheme B S hS).map m, ?_, hlφ⟩⟩
  rw [← cancel_mono ((BigFppfOver.toScheme B S hS).map π), Category.assoc, hlφ]
  exact D.commSq.w.symm

/-- **Stacks 0ARJ.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` locally
Noetherian. If `f` is locally of finite type and quasi-separated, and every valuative square for
`f` whose valuation ring is a discrete valuation ring admits at most one dotted arrow, then `f`
is separated. -/
@[stacks 0ARJ]
theorem isSeparated_of_isQuasiSeparated_of_discreteValuativeUniqueness
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hft : IsLocallyOfFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (hu : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R → Subsingleton q.Lift) :
    IsSeparated B S hS f := by
  have hdAlg := isAlgebraicSpace_pullback B S hS f f hX hX hY
  have hRep : yoneda.relativelyRepresentable (pullback.diagonal f) :=
    relativelyRepresentable_pullbackDiagonal B S hS f hX
  have hlftFst : IsLocallyOfFiniteType B S hS (pullback.fst f f) :=
    IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f f) hX hY hft
  have hNoethSq := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hdAlg hY
    (pullback.fst f f ≫ f)
    (isLocallyOfFiniteType_comp B S hS hdAlg hX hY _ f hlftFst hft) hNoeth
  obtain ⟨V, chart, hchartSurj, hchartEtale⟩ := hdAlg.exists_atlas
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS (pullback f f)
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) hdAlg).mp hNoethSq V chart hchartEtale
  set W := hRep.pullback chart
  set p : yoneda.obj W ⟶ X := hRep.fst chart
  set π : W ⟶ V := hRep.snd chart
  have hsq : IsPullback p (yoneda.map π) (pullback.diagonal f) chart := hRep.isPullback chart
  set φ : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    (BigFppfOver.toScheme B S hS).map π
  have hmono : Mono φ :=
    (presheaf_monomorphisms_pullbackDiagonal B S hS f hX).property chart p π hsq
  have : _root_.AlgebraicGeometry.IsSeparated φ :=
    (presheaf_isSeparated_pullbackDiagonal B S hS f hX).property chart p π hsq
  have : LocallyOfFiniteType φ :=
    (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS f hX).property chart p π hsq
  have hlqf : LocallyQuasiFinite φ :=
    ((presheaf_locallyQuasiFinite_pullbackDiagonal B S hS f hX).property chart p π hsq).2
  have : QuasiCompact φ :=
    (presheaf_quasiCompact_of_isQuasiCompact B S hS hRep hqs).property chart p π hsq
  have : _root_.AlgebraicGeometry.UniversallyClosed φ :=
    universallyClosed_of_contained_discreteValuativeCriterion B φ W.left.2
      (hasLift_of_isPullback_diagonal_of_discreteValuativeUniqueness B S hS hsq (hπ := hmono) hu)
  have : _root_.AlgebraicGeometry.IsProper φ := _root_.AlgebraicGeometry.IsProper.mk
  have hCI : _root_.AlgebraicGeometry.IsClosedImmersion φ :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono φ).2
      ⟨(_root_.AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite φ).2
        ⟨inferInstance, hlqf⟩, hmono⟩
  refine ((isClosedImmersion_tfae B S hS hX hdAlg (pullback.diagonal f)).out 4 1).mp ?_
  refine ⟨V, chart, hchartSurj, hchartEtale, ?_⟩
  refine (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk hsq.isoPullback (Iso.refl (yoneda.obj V)) ?_)).mp
    ((presheaf_yoneda_map_iff B S hS
      _root_.AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange π).2 hCI)
  exact hsq.isoPullback_hom_snd.trans (Category.comp_id _).symm

end AlgebraicGeometry.Space

end
