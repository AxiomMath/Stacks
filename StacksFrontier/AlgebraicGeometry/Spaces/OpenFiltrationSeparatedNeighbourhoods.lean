module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The open filtration of a quasi-compact algebraic space by fibre degree

A quasi-compact algebraic space `X` over a scheme `S` has an affine étale surjective chart and a
decreasing chain of open subspaces `X = U₀ ⊇ U₁ ⊇ U₂ ⊇ …`, the member of index `d` being the
locus where the fibre of the chart has degree at least `d`, such that every point of `|X|`
represented by a quasi-compact morphism from the spectrum of a field lies in exactly one stratum
`Uₚ \ Uₚ₊₁`.

## Main results

* `AlgebraicGeometry.Space.exists_openFiltration_quasiCompactPoint_mem_stratum`: the chain and
  the fact that every quasi-compact field-valued point lies in exactly one of its strata, under
  hypotheses that finiteness and finite local freeness of a given rank are fpqc local on the
  target and that the fibre-degree filtration exists for morphisms of schemes.
* `AlgebraicGeometry.Space.exists_openFiltration_quasiCompactPoint_mem_stratum'`: the same
  assertion asking only that `X` be a quasi-compact algebraic space.
* `AlgebraicGeometry.Space.exists_comp_ι_iff_class_mem_range`: a field-valued point of an
  algebraic space factors through an open subspace exactly when its class lies in that
  subspace's set of points.

## Implementation notes

Membership of a point of `|X|` in the stratum `Uₚ \ Uₚ₊₁` does not depend on the subspace
structure of the stratum, so it is stated as membership in the set of points of `Uₚ` and not in
that of `Uₚ₊₁`.

Over a quasi-compact field-valued point the fibre of the chart is a finite scheme étale over the
spectrum of a field, hence finite locally free of the single rank `Module.finrank` of its algebra
of global sections. So the condition "not finite, or finite locally free of some rank `≥ d`"
holds exactly when `d` is at most that rank `N`, and the point lies in the stratum between `N`
and `N + 1`.

## References

* [Stacks Project, Tag 0BBN](https://stacks.math.columbia.edu/tag/0BBN)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 0468](https://stacks.math.columbia.edu/tag/0468)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under
Lean v4.35.0: supply them directly. -/
local instance (priority := high) hasLimit_cospan_presheaf_OpenFiltrationSeparatedNeighbourhoods
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    HasLimit (cospan f g) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-! ### Factoring a field-valued point through an arbitrary open subspace -/

/-- An open subspace of an algebraic space over `S` is the open subspace cut out by its own set
of points. -/
theorem eq_openSubspaceOfPoints_range_pointsMap
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (G : Subfunctor X) (hG : IsOpenSubspace B S hS G) :
    G = openSubspaceOfPoints B S hS X (Set.range (pointsMap B S hS G.toFunctor G.ι)) := by
  have hopen : IsOpen (Set.range (pointsMap B S hS G.toFunctor G.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS G.ι hG.2
  have hcut := isOpenSubspace_openSubspaceOfPoints B S hS hX
    (Set.range (pointsMap B S hS G.toFunctor G.ι)) hopen
  have hrange := range_pointsMap_ι_openSubspaceOfPoints B S hS (F := X)
    (Set.range (pointsMap B S hS G.toFunctor G.ι))
  exact le_antisymm (le_of_range_pointsMap_ι_subset B S hS hcut hrange.ge)
    (le_of_range_pointsMap_ι_subset B S hS hG hrange.le)

/-- A field-valued point of an algebraic space factors through an open subspace exactly when
its class lies in that subspace's set of points. -/
theorem exists_comp_ι_iff_class_mem_range
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (G : Subfunctor X) (hG : IsOpenSubspace B S hS G) (p : FieldValuedPoint B S hS X) :
    (∃ g : yoneda.obj (FieldValuedPoint.siteObject B S hS X p) ⟶ G.toFunctor,
        g ≫ G.ι = yonedaEquiv.symm p.value) ↔
      p.class B S hS X ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  set W := Set.range (pointsMap B S hS G.toFunctor G.ι)
  rw [eq_openSubspaceOfPoints_range_pointsMap B S hS hX G hG]
  exact exists_comp_ι_openSubspaceOfPoints_iff B S hS W p

/-! ### The degree of the fibre over a quasi-compact field-valued point -/

/-- The represented fibre of an étale chart with quasi-compact source over a field-valued point
whose presenting morphism is quasi-compact is a finite scheme. -/
private theorem finite_representedFieldFibre
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    {φ : yoneda.obj U ⟶ X} (hφ : IsEtale B S hS φ) (q : FieldValuedPoint B S hS X)
    (hq : IsQuasiCompact B S hS (fieldMorphism B S hS X q)) :
    Finite ((BigFppfOver.toScheme B S hS).obj
      ((presheaf_etale_of_isEtale B S hS hφ).rep.pullback
        (fieldMorphism B S hS X q))) := by
  set hφp := presheaf_etale_of_isEtale B S hS hφ
  have sqW := hφp.rep.isPullback (fieldMorphism B S hS X q)
  have hWet : Etale ((BigFppfOver.toScheme B S hS).map
      (hφp.rep.snd (fieldMorphism B S hS X q))) := hφp.property_snd _
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (FieldValuedPoint.siteObject B S hS X q)) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
  have hqcs : IsQuasiCompactSpace B S hS (pullback φ (fieldMorphism B S hS X q)) :=
    hq (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (isQuasiCompactSpace_yoneda_obj B S hS hU) φ
  have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (hφp.rep.pullback (fieldMorphism B S hS X q))) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (isQuasiCompactSpace_of_iso B S hS
        ((IsPullback.of_hasPullback φ (fieldMorphism B S hS X q)).isoIsPullback _ _ sqW) hqcs)
  exact finite_of_etale_of_subsingleton
    ((BigFppfOver.toScheme B S hS).map (hφp.rep.snd (fieldMorphism B S hS X q)))

/-- Over a quasi-compact field-valued point of an algebraic space with an étale chart of
quasi-compact source, there is a natural number `N` such that the fibre of the chart is "not
finite, or finite locally free of some rank `≥ d`" exactly when `d ≤ N`. -/
private theorem exists_bound_degreeCondition_iff
    (h02LA : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage)
    (h02VO : ∀ r : ℕ, MorphismProperty.IsLocalAtTarget
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) Scheme.fpqcPrecoverage)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    {φ : yoneda.obj U ⟶ X} (hφ : IsEtale B S hS φ) (q : FieldValuedPoint B S hS X)
    (hq : IsQuasiCompact B S hS (fieldMorphism B S hS X q)) :
    ∃ N : ℕ, ∀ d : ℕ,
      (¬ (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf
              (pullback.fst (yonedaEquiv.symm q.value) φ) ∨
        ∃ r : ℕ, d ≤ r ∧
          (MorphismProperty.inverseImage
            (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
            (BigFppfOver.toScheme B S hS)).presheaf
              (pullback.fst (yonedaEquiv.symm q.value) φ)) ↔ d ≤ N := by
  set hφp := presheaf_etale_of_isEtale B S hS hφ
  set g : (BigFppfOver.toScheme B S hS).obj
      (hφp.rep.pullback (fieldMorphism B S hS X q)) ⟶ Spec (.of q.carrier) :=
    (BigFppfOver.toScheme B S hS).map (hφp.rep.snd (fieldMorphism B S hS X q)) with hgdef
  have hget : Etale g := hφp.property_snd _
  have hgfin : Finite ((BigFppfOver.toScheme B S hS).obj
      (hφp.rep.pullback (fieldMorphism B S hS X q))) :=
    finite_representedFieldFibre B S hS hU hφ q hq
  let _ := ((Scheme.ΓSpecIso (.of q.carrier)).inv ≫ g.appTop).hom.toAlgebra
  have hfin : _root_.AlgebraicGeometry.IsFinite g :=
    isFinite_of_etale_of_finite q.carrier g
  have hrk : Stacks.Morphisms.IsFiniteLocallyFreeOfRank g
      (Module.finrank q.carrier Γ((BigFppfOver.toScheme B S hS).obj
        (hφp.rep.pullback (fieldMorphism B S hS X q)), ⊤)) :=
    isFiniteLocallyFreeOfRank_of_etale_of_finite q.carrier g
  have := h02LA
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}))
  have hfinIff := presheafFibreProperty_iff_schemeFibreProperty
    (B := B) (S := S) (hS := hS) (P := @_root_.AlgebraicGeometry.IsFinite.{u}) φ hφp.rep
    (yonedaEquiv.symm q.value)
  have hrankIff (r : ℕ) :
      (MorphismProperty.inverseImage
          (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
          (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.fst (yonedaEquiv.symm q.value) φ) ↔
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r := by
    have := h02VO r
    exact presheafFibreProperty_iff_schemeFibreProperty
      (B := B) (S := S) (hS := hS)
      (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) φ hφp.rep
      (yonedaEquiv.symm q.value)
  refine ⟨Module.finrank q.carrier Γ((BigFppfOver.toScheme B S hS).obj
    (hφp.rep.pullback (fieldMorphism B S hS X q)), ⊤), fun d ↦ ?_⟩
  constructor
  · rintro (hn | ⟨r, hdr, hr⟩)
    · exact absurd (hfinIff.mpr hfin) hn
    · have := (hrankIff r).mp hr
      have he := (finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank g r).2
      omega
  · exact fun hd ↦ Or.inr ⟨_, hd, (hrankIff _).mpr hrk⟩

/-! ### The filtration by fibre degree -/

/-- A quasi-compact algebraic space `X` over `S` has an affine étale surjective chart `φ` and a
decreasing chain of open subspaces `U` starting at `U 0 = ⊤`, the member of index `d` being the
locus where the fibre of `φ` is not finite or finite locally free of some rank `≥ d`, such that
every point of `|X|` represented by a quasi-compact morphism from the spectrum of a field lies
in exactly one stratum of the chain: there is an index `p` with the point in the set of points of
`U p` and not in that of `U (p + 1)`.

The hypotheses `h02LA` and `h02VO` say that finiteness and finite local freeness of rank `r` are
fpqc local on the target, and `h086R` that a flat, locally finitely presented, separated and
locally quasi-finite morphism of schemes has the analogous filtration of its target by fibre
degree. -/
theorem exists_openFiltration_quasiCompactPoint_mem_stratum
    (h02LA : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage)
    (h02VO : ∀ r : ℕ, MorphismProperty.IsLocalAtTarget
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) Scheme.fpqcPrecoverage)
    (h086R : ∀ {Z Y : Scheme.{u}} (g : Z ⟶ Y), Flat g → LocallyOfFinitePresentation g →
      _root_.AlgebraicGeometry.IsSeparated g → LocallyQuasiFinite g →
      ∃ V : ℕ → Y.Opens, V 0 = ⊤ ∧ Antitone V ∧
        ∀ (d : ℕ) (k : Type u) (_ : Field k) (c : Spec (.of k) ⟶ Y),
          (∃ h : Spec (.of k) ⟶ (V d).toScheme, h ≫ (V d).ι = c) ↔
            (¬ _root_.AlgebraicGeometry.IsFinite (pullback.fst c g) ∨
              ∃ r : ℕ, d ≤ r ∧
                Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst c g) r))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) :
    ∃ (A : BigFppfOver B S hS) (φ : yoneda.obj A ⟶ X) (U : ℕ → Subfunctor X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf φ ∧
      IsEtale B S hS φ ∧
      (∀ p, IsOpenSubspace B S hS (U p)) ∧ U 0 = ⊤ ∧ Antitone U ∧
      (∀ (d : ℕ) (q : FieldValuedPoint B S hS X),
        q.class B S hS X ∈ Set.range (pointsMap B S hS (U d).toFunctor (U d).ι) ↔
          (¬ (MorphismProperty.inverseImage
                (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
                (BigFppfOver.toScheme B S hS)).presheaf
                  (pullback.fst (yonedaEquiv.symm q.value) φ) ∨
            ∃ r : ℕ, d ≤ r ∧
              (MorphismProperty.inverseImage
                (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
                (BigFppfOver.toScheme B S hS)).presheaf
                  (pullback.fst (yonedaEquiv.symm q.value) φ))) ∧
      (∀ (x : points B S hS X) (q : FieldValuedPoint B S hS X),
        q.class B S hS X = x → IsQuasiCompact B S hS (fieldMorphism B S hS X q) →
        ∃ p : ℕ,
          x ∈ Set.range (pointsMap B S hS (U p).toFunctor (U p).ι) ∧
          x ∉ Set.range (pointsMap B S hS (U (p + 1)).toFunctor (U (p + 1)).ι)) := by
  obtain ⟨A, φ, hAaff, hAsurj, hAetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).mp hqc
  have hAaff' : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAaff
  have hAcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj A) := inferInstance
  have hsep : IsSeparated B S hS φ :=
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX A inferInstance φ hAetale
  have hlqf : IsLocallyQuasiFinite B S hS φ := by
    intro V W a b h ha hb hcomm
    have : Etale ((BigFppfOver.toScheme B S hS).map h) :=
      etale_of_comp_etale_chart B S hS (hAetale V a ha) hb hcomm
    exact locallyQuasiFinite_of_etale _
  obtain ⟨U, hUopen, hU0, hUanti, hUdeg⟩ :=
    exists_antitone_openSubspaces_iff_fibreDegree_ge B S hS h02LA h02VO h086R hX A φ
      (isFlat_of_isEtale B S hS hAetale)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hAetale)
      hsep hlqf
  have hpoints (d : ℕ) (q : FieldValuedPoint B S hS X) :
      q.class B S hS X ∈ Set.range (pointsMap B S hS (U d).toFunctor (U d).ι) ↔
        (¬ (MorphismProperty.inverseImage
              (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm q.value) φ) ∨
          ∃ r : ℕ, d ≤ r ∧
            (MorphismProperty.inverseImage
              (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf
                (pullback.fst (yonedaEquiv.symm q.value) φ)) :=
    (exists_comp_ι_iff_class_mem_range B S hS hX (U d) (hUopen d) q).symm.trans (hUdeg d q)
  refine ⟨A, φ, U, hAaff, hAsurj, hAetale, hUopen, hU0, hUanti, hpoints,
    fun x q hqx hqqc ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_bound_degreeCondition_iff B S hS h02LA h02VO hAcpt hAetale q hqqc
  have hfactor (d : ℕ) :
      x ∈ Set.range (pointsMap B S hS (U d).toFunctor (U d).ι) ↔ d ≤ N := by
    rw [← hqx]
    exact (hpoints d q).trans (hN d)
  exact ⟨N, (hfactor N).mpr le_rfl, fun hmem ↦ by simpa using (hfactor (N + 1)).mp hmem⟩

/-- A quasi-compact algebraic space `X` over `S` has an affine étale surjective chart and a
decreasing chain of open subspaces starting at `U 0 = ⊤`, the member of index `d` being the
locus where the fibre of the chart has degree at least `d`, such that every point of `|X|`
represented by a quasi-compact morphism from the spectrum of a field lies in exactly one stratum
of that chain. -/
theorem exists_openFiltration_quasiCompactPoint_mem_stratum'
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) :
    ∃ (A : BigFppfOver B S hS) (φ : yoneda.obj A ⟶ X) (U : ℕ → Subfunctor X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf φ ∧
      IsEtale B S hS φ ∧
      (∀ p, IsOpenSubspace B S hS (U p)) ∧ U 0 = ⊤ ∧ Antitone U ∧
      (∀ (d : ℕ) (q : FieldValuedPoint B S hS X),
        q.class B S hS X ∈ Set.range (pointsMap B S hS (U d).toFunctor (U d).ι) ↔
          (¬ (MorphismProperty.inverseImage
                (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
                (BigFppfOver.toScheme B S hS)).presheaf
                  (pullback.fst (yonedaEquiv.symm q.value) φ) ∨
            ∃ r : ℕ, d ≤ r ∧
              (MorphismProperty.inverseImage
                (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
                (BigFppfOver.toScheme B S hS)).presheaf
                  (pullback.fst (yonedaEquiv.symm q.value) φ))) ∧
      (∀ (x : points B S hS X) (q : FieldValuedPoint B S hS X),
        q.class B S hS X = x → IsQuasiCompact B S hS (fieldMorphism B S hS X q) →
        ∃ p : ℕ,
          x ∈ Set.range (pointsMap B S hS (U p).toFunctor (U p).ι) ∧
          x ∉ Set.range (pointsMap B S hS (U (p + 1)).toFunctor (U (p + 1)).ι)) :=
  exists_openFiltration_quasiCompactPoint_mem_stratum B S hS
    _root_.AlgebraicGeometry.isFinite_isLocalAtTarget_fpqc
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc
    (fun g hflat hlfp hsep hlqf ↦
      @_root_.AlgebraicGeometry.exists_antitone_opens_iff_fiber_degree_ge
        _ _ g hflat hlfp hsep hlqf)
    hX hqc

end AlgebraicGeometry.Space

end
