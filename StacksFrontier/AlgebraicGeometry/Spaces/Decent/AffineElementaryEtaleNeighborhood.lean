module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SchemeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Affine elementary étale neighborhoods of a decent algebraic space

Stacks 0BBP says that a point `x` of a decent algebraic space `X` over `S` has an elementary
étale neighborhood `(U, u) → (X, x)` with `U` an *affine* scheme, `u` the *only* point of `U`
above `x`, and the induced homomorphism of residue fields `κ(x) → κ(u)` an *isomorphism*.

## Main results

* `AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood'`: the three conclusions of
  Stacks 0BBP.
* `AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood`: the same three
  conclusions, from Stacks 0BBN taken as the hypothesis `h0BBN`.

## Implementation notes

The hypothesis `h0BBN` asks that every quasi-compact algebraic space over `S` carry
stratification data in the sense of `AlgebraicGeometry.Space.SchemeStratification`, which is
clause (1) of Stacks 0BBN, whose chain also satisfies clause (2): every point represented by a
quasi-compact morphism from the spectrum of a field lies in exactly one stratum. Both clauses
are supplied by
`AlgebraicGeometry.Space.exists_schemeStratification_quasiCompactPoint_mem_stratum`; the
stratification's `range_stratum` identifies the points of the `p`-th stratum with those of the
`p`-th member of the chain that are not points of the next one.

The proof uses only the chain's open subspaces, the closedness of the strata, their
identification on points, the étaleness of the charts and the isomorphism over each stratum;
the remaining fields are part of `h0BBN` so that the hypothesis is exactly Stacks 0BBN.

Affineness comes from passing to a member of the affine open cover of the chart. Uniqueness of
the point above `x` comes from the isomorphism over the stratum: two points of the chart above
`x` lie over one point of the stratum, and a projection of a fibre product being an
isomorphism forces them to agree. The residue-field isomorphism is uniqueness of the
monomorphic field-valued representative (Stacks 0EMW): the residue-field point of the
neighborhood is a monomorphic representative of `x`, so it is uniquely isomorphic over `X` to
the chosen one, and an isomorphism of field spectra is the spectrum of a bijective ring
homomorphism. That homomorphism is returned together with the square over `X` identifying it
as the induced one.

Stacks 0BBN is applied to a quasi-compact open subspace around `x`. The field-valued
representative of `x` supplied by decency is pushed into that open subspace, into a member of
the chain and into a stratum, keeping its monomorphism and quasi-compactness at each step, by
`AlgebraicGeometry.Space.exists_fieldValuedPoint_of_isOpenSubspace` and its closed
counterpart; both reduce to one lemma about a subfunctor whose part over the field spectrum
maps isomorphically to it.

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BBN](https://stacks.math.columbia.edu/tag/0BBN)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_affineElementaryEtale :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_affineElementaryEtale
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Residue-field points of a scheme of the site -/

/-- The field-valued point of a represented presheaf given by the residue field at a point of
the representing scheme. Its class is `AlgebraicGeometry.Space.presheafPoint`, by definition. -/
private def residueFieldPoint (U : BigFppfOver B S hS) (u : U.left.1)
    (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    FieldValuedPoint B S hS (yoneda.obj U) :=
  ⟨U.left.1.residueField u, hu, U.left.1.fromSpecResidueField u ≫ U.hom.1,
    residueFieldMap B S hS U u hu⟩

private theorem class_residueFieldPoint (U : BigFppfOver B S hS) (u : U.left.1)
    (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    (residueFieldPoint B S hS U u hu).class B S hS (yoneda.obj U) =
      presheafPoint B S hS U u hu := rfl

private theorem pointsToScheme_residueFieldPoint (U : BigFppfOver B S hS) (u : U.left.1)
    (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    pointsToScheme B S hS U
        ((residueFieldPoint B S hS U u hu).class B S hS (yoneda.obj U)) = u := by
  show U.left.1.fromSpecResidueField u (IsLocalRing.closedPoint _) = u
  exact Scheme.fromSpecResidueField_apply u _

/-- The morphism of a residue-field point pushed along `α` is the residue-field map followed
by `α`. -/
private theorem fieldMorphism_map_residueFieldPoint {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (u : U.left.1) (hu : B.Contains (Spec (.of (U.left.1.residueField u))))
    (α : yoneda.obj U ⟶ X) :
    fieldMorphism B S hS X (FieldValuedPoint.map B S hS (yoneda.obj U) α
      (residueFieldPoint B S hS U u hu)) = yoneda.map (residueFieldMap B S hS U u hu) ≫ α := by
  rw [fieldMorphism_map]
  rfl

/-! ### Pushing a field-valued point into a subspace -/

/-- The part of a relatively representable subfunctor inclusion lying over a field-valued point
of the ambient presheaf has a point, as soon as some point of the subfunctor represents that
field-valued point: a compatible pair of points of a cartesian square lifts, by Stacks 03H4. -/
private theorem nonempty_toScheme_rep_pullback
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F)
    (hrep : Functor.relativelyRepresentable (yoneda (C := BigFppfOver B S hS)) G.ι)
    (p : FieldValuedPoint B S hS F) (y : points B S hS G.toFunctor)
    (hy : pointsMap B S hS G.toFunctor G.ι y = p.class B S hS F) :
    Nonempty ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (fieldMorphism B S hS F p))) := by
  obtain ⟨w, -, -⟩ := exists_point_of_isPullback_presheaf B S hS
    (hrep.isPullback (fieldMorphism B S hS F p)) y
    ((p.tautologicalPoint B S hS F).class B S hS (yoneda.obj (p.siteObject B S hS F)))
    (by rw [hy, pointsMap_fieldMorphism_tautologicalPoint])
  exact ⟨pointsToScheme B S hS _ w⟩

/-- A field-valued point of `F` whose class lies in a subfunctor `G` is the image of a
field-valued point of `G` over the same field, as soon as the part of `G` lying over its field
spectrum maps isomorphically to that spectrum, which it does once it is surjective on schemes; the
monomorphism and quasi-compactness certificates descend with it.

Cancelling the inclusion of `G`, a monomorphism, is what carries the two certificates down:
`CategoryTheory.mono_of_mono` for the first and
`AlgebraicGeometry.Space.isQuasiCompact_of_comp_mono` for the second. -/
private theorem exists_fieldValuedPoint_of_isIso_rep_snd
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F) [Mono G.ι]
    (hrep : Functor.relativelyRepresentable (yoneda (C := BigFppfOver B S hS)) G.ι)
    (p : FieldValuedPoint B S hS F) (y : points B S hS G.toFunctor)
    (hy : pointsMap B S hS G.toFunctor G.ι y = p.class B S hS F)
    (hiso : _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map
      (hrep.snd (fieldMorphism B S hS F p))) →
        IsIso ((BigFppfOver.toScheme B S hS).map (hrep.snd (fieldMorphism B S hS F p))))
    (hpMono : Mono (fieldMorphism B S hS F p))
    (hpQC : IsQuasiCompact B S hS (fieldMorphism B S hS F p)) :
    ∃ q : FieldValuedPoint B S hS G.toFunctor,
      q.class B S hS G.toFunctor = y ∧
      Mono (fieldMorphism B S hS G.toFunctor q) ∧
      IsQuasiCompact B S hS (fieldMorphism B S hS G.toFunctor q) := by
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS F)) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  obtain ⟨z⟩ := nonempty_toScheme_rep_pullback B S hS G hrep p y hy
  have hiso : IsIso (hrep.snd (fieldMorphism B S hS F p)) :=
    (isIso_iff_of_reflects_iso _ (BigFppfOver.toScheme B S hS)).mp
      (hiso ⟨fun _ ↦ ⟨z, Subsingleton.elim _ _⟩⟩)
  have hpb := hrep.isPullback (fieldMorphism B S hS F p)
  set qMap : yoneda.obj (p.siteObject B S hS F) ⟶ G.toFunctor :=
    yoneda.map (inv (hrep.snd (fieldMorphism B S hS F p))) ≫
      hrep.fst (fieldMorphism B S hS F p) with hqMapDef
  have hfac : qMap ≫ G.ι = fieldMorphism B S hS F p := by
    rw [hqMapDef, Category.assoc, hpb.w, ← Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id]
    simp
  set v : G.toFunctor.obj (Opposite.op (p.siteObject B S hS F)) :=
    qMap.app (Opposite.op (p.siteObject B S hS F)) (𝟙 (p.siteObject B S hS F)) with hvDef
  set q : FieldValuedPoint B S hS G.toFunctor :=
    ⟨p.carrier, p.contained, p.toBase, v⟩ with hqDef
  have hfm : fieldMorphism B S hS G.toFunctor q = qMap := by
    have : yonedaEquiv.symm v = qMap := by
      apply yonedaEquiv.injective
      simp only [Equiv.apply_symm_apply, yonedaEquiv_apply]
      rfl
    exact this
  have hval : G.ι.app (Opposite.op (p.siteObject B S hS F)) q.value = p.value := by
    have hh := congrArg
      (fun k ↦ k.app (Opposite.op (p.siteObject B S hS F)) (𝟙 (p.siteObject B S hS F))) hfac
    simpa [hqDef, hvDef, fieldMorphism] using hh
  have hmono : Mono (fieldMorphism B S hS G.toFunctor q) := by
    have : Mono (fieldMorphism B S hS G.toFunctor q ≫ G.ι) := by
      rw [hfm, hfac]; exact hpMono
    exact mono_of_mono _ G.ι
  have hqc : IsQuasiCompact B S hS (fieldMorphism B S hS G.toFunctor q) := by
    refine isQuasiCompact_of_comp_mono B S hS _ G.ι ?_
    rw [hfm, hfac]; exact hpQC
  refine ⟨q, ?_, hmono, hqc⟩
  refine pointsMap_injective_of_mono B S hS G.ι ?_
  rw [pointsMap_class, hy]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F
    ⟨p, ⟨𝟙 (p.siteObject B S hS F), ?_⟩, FieldValuedPoint.dominates_refl B S hS F p⟩
  show F.map (𝟙 (p.siteObject B S hS F)).op
    ((FieldValuedPoint.map B S hS G.toFunctor G.ι q).value) = p.value
  simpa [hval]

/-- A field-valued point of `F` whose class lies in an **open** subspace comes from a
field-valued point of that subspace, with its monomorphism and quasi-compactness certificates.

The part of the subspace lying over the field spectrum is an open immersion into it and has a
point, so it is surjective — the field spectrum has only one point — hence an isomorphism. -/
private theorem exists_fieldValuedPoint_of_isOpenSubspace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F) (hG : IsOpenSubspace B S hS G)
    (p : FieldValuedPoint B S hS F) (y : points B S hS G.toFunctor)
    (hy : pointsMap B S hS G.toFunctor G.ι y = p.class B S hS F)
    (hpMono : Mono (fieldMorphism B S hS F p))
    (hpQC : IsQuasiCompact B S hS (fieldMorphism B S hS F p)) :
    ∃ q : FieldValuedPoint B S hS G.toFunctor,
      q.class B S hS G.toFunctor = y ∧
      Mono (fieldMorphism B S hS G.toFunctor q) ∧
      IsQuasiCompact B S hS (fieldMorphism B S hS G.toFunctor q) := by
  have : Mono G.ι := mono_of_presheaf_isOpenImmersion hG.2
  have hopen : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (hG.2.rep.snd (fieldMorphism B S hS F p))) := hG.2.property_snd _
  exact exists_fieldValuedPoint_of_isIso_rep_snd B S hS G hG.2.rep p y hy
    (fun hsurj ↦ (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hopen, hsurj⟩) hpMono hpQC

/-- A field-valued point of `F` whose class lies in a **closed** subspace comes from a
field-valued point of that subspace, with its monomorphism and quasi-compactness certificates.

The part of the subspace lying over the field spectrum is a closed immersion into it and has a
point, so it is surjective; a surjective closed immersion into a reduced scheme — and the
spectrum of a field is reduced — is an isomorphism. -/
private theorem exists_fieldValuedPoint_of_isClosedSubspace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F) (hG : IsClosedSubspace B S hS G)
    (p : FieldValuedPoint B S hS F) (y : points B S hS G.toFunctor)
    (hy : pointsMap B S hS G.toFunctor G.ι y = p.class B S hS F)
    (hpMono : Mono (fieldMorphism B S hS F p))
    (hpQC : IsQuasiCompact B S hS (fieldMorphism B S hS F p)) :
    ∃ q : FieldValuedPoint B S hS G.toFunctor,
      q.class B S hS G.toFunctor = y ∧
      Mono (fieldMorphism B S hS G.toFunctor q) ∧
      IsQuasiCompact B S hS (fieldMorphism B S hS G.toFunctor q) := by
  have : Mono G.ι := mono_of_isClosedImmersion B S hS (f := G.ι) hG.2
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map
        (hG.2.rep.snd (fieldMorphism B S hS F p))) := hG.2.property_snd _
  have hred : IsReduced ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS F)) :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of p.carrier)))
  exact exists_fieldValuedPoint_of_isIso_rep_snd B S hS G hG.2.rep p y hy
    (fun _ ↦ _root_.AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective _) hpMono hpQC

/-! ### Points over an isomorphic base change -/

/-- If the first projection of the fibre product of `g` and `f` is an isomorphism, so is the
second projection of the fibre product of `f` and `g`. -/
private theorem isIso_pullback_snd_of_isIso_pullback_fst
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    (h : IsIso (pullback.fst g f)) : IsIso (pullback.snd f g) := by
  have : pullback.snd f g = (pullbackSymmetry f g).hom ≫ pullback.fst g f := by simp
  rw [this]; infer_instance

/-- Two points of `F` with a common image in `H` that is also the image of a point of `G` agree,
as soon as the second projection of the fibre product of `F` and `G` over `H` is an
isomorphism: each of the two points lifts to the fibre product over the point of `G`, the lifts
agree because that projection is monic, and so therefore do the points. -/
private theorem points_eq_of_isIso_pullback_snd
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    [IsIso (pullback.snd f g)] (a b : points B S hS F) (c : points B S hS G)
    (ha : pointsMap B S hS F f a = pointsMap B S hS G g c)
    (hb : pointsMap B S hS F f b = pointsMap B S hS G g c) :
    a = b := by
  have hp := IsPullback.of_hasPullback f g
  obtain ⟨wa, hwa, hwac⟩ := exists_point_of_isPullback_presheaf B S hS hp a c ha
  obtain ⟨wb, hwb, hwbc⟩ := exists_point_of_isPullback_presheaf B S hS hp b c hb
  have hw : wa = wb :=
    @pointsMap_injective_of_mono B S hS _ _ (pullback.snd f g) (IsIso.mono_of_iso _) _ _
      (hwac.trans hwbc.symm)
  rw [← hwa, ← hwb, hw]

/-! ### The residue field of an elementary étale neighborhood -/

/-- **Stacks 0EMW at an elementary étale neighborhood.** The residue field of an elementary
étale neighborhood at its distinguished point is the residue field of the space at the point
below: the residue-field point of the neighborhood is a monomorphic field-valued representative
of that point, hence uniquely isomorphic over the space to the chosen one, and an isomorphism
of field spectra is the spectrum of a bijective ring homomorphism. -/
private theorem exists_bijective_residueFieldHom_of_elementaryEtaleNeighborhood
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hDecent : IsDecentSpace B S hS X) (x : points B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ φ : residueField B S hS X hDecent x →+* E.scheme.left.1.residueField E.point,
      Function.Bijective φ ∧
        ∃ g : residueFieldObject B S hS E.scheme E.point E.residueField_contained ⟶
            (residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X,
          B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) ∧
            yoneda.map g ≫ residueFieldMorphism B S hS X hDecent x =
              yoneda.map (residueFieldMap B S hS E.scheme E.point
                E.residueField_contained) ≫ E.toSpace := by
  have hqclass : (FieldValuedPoint.map B S hS (yoneda.obj E.scheme) E.toSpace
      (residueFieldPoint B S hS E.scheme E.point E.residueField_contained)).class
        B S hS X = x := by
    rw [← pointsMap_class, class_residueFieldPoint]
    exact E.map_point
  have hqm := fieldMorphism_map_residueFieldPoint B S hS E.scheme E.point
    E.residueField_contained E.toSpace
  have hmono : Mono (fieldMorphism B S hS X
      (FieldValuedPoint.map B S hS (yoneda.obj E.scheme) E.toSpace
        (residueFieldPoint B S hS E.scheme E.point E.residueField_contained))) := by
    rw [hqm]; exact E.mono_residueField
  obtain ⟨e, he, -⟩ :=
    residueFieldRepresentative_unique B S hS X hX hDecent x _ hqclass hmono
  set g := yoneda.preimage e.inv with hgDef
  have hg : yoneda.map g = e.inv := yoneda.map_preimage _
  have hgIsoMap : IsIso (yoneda.map g) := by rw [hg]; infer_instance
  have hgIso : IsIso g := isIso_of_fully_faithful yoneda g
  set φ := ((Spec.fullyFaithful.preimage (B.inclusion.map g.left)).unop).hom with hφDef
  have hspec : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) := by
    rw [hφDef]; simp
  have hleftIso : IsIso (B.inclusion.map g.left) := by
    show IsIso ((BigFppfOver.toScheme B S hS).map g)
    infer_instance
  have hφiso : IsIso (Spec.map (CommRingCat.ofHom φ)) := by rw [← hspec]; infer_instance
  have hSpecIso : IsIso (Scheme.Spec.map (CommRingCat.ofHom φ).op) := hφiso
  have hopIso : IsIso (CommRingCat.ofHom φ).op := Spec.fullyFaithful.isIso_of_isIso_map _
  have hofIso : IsIso (CommRingCat.ofHom φ) := isIso_of_op _
  refine ⟨φ, ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom φ), g, hspec, ?_⟩
  have hsquare : yoneda.map g ≫ residueFieldMorphism B S hS X hDecent x =
      fieldMorphism B S hS X (FieldValuedPoint.map B S hS (yoneda.obj E.scheme) E.toSpace
        (residueFieldPoint B S hS E.scheme E.point E.residueField_contained)) := by
    rw [hg, ← he]
    simp
  exact hsquare.trans hqm

/-! ### Lifting a field-valued point of a stratum to a chart -/

/-- A field-valued point of a subfunctor that a chart meets in an isomorphism lifts to a
field-valued point of the chart, over the same field spectrum and above the same point.

The lift is the chart projection of the inverse of that isomorphism, applied to the field
spectrum: the field-valued point presents a morphism into the subfunctor, which is a morphism
into the fibre product because the chart meets the subfunctor isomorphically, and the first
projection of the fibre product carries it into the chart. -/
private theorem exists_fieldValuedPoint_chart_of_isIso_pullback_fst
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Subfunctor Y) [Mono T.ι]
    {V : BigFppfOver B S hS} (f : yoneda.obj V ⟶ Y)
    (hiso : IsIso (pullback.fst T.ι f)) (qT : FieldValuedPoint B S hS T.toFunctor) :
    ∃ r : FieldValuedPoint B S hS (yoneda.obj V),
      pointsMap B S hS (yoneda.obj V) f (r.class B S hS (yoneda.obj V)) =
        pointsMap B S hS T.toFunctor T.ι (qT.class B S hS T.toFunctor) ∧
      ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : Y ⟶ Z),
        Mono (fieldMorphism B S hS T.toFunctor qT ≫ T.ι ≫ k) →
          Mono (fieldMorphism B S hS (yoneda.obj V) r ≫ f ≫ k) := by
  have hsnd := isIso_pullback_snd_of_isIso_pullback_fst B S hS f T.ι hiso
  let m : yoneda.obj (qT.siteObject B S hS T.toFunctor) ⟶ yoneda.obj V :=
    fieldMorphism B S hS T.toFunctor qT ≫ inv (pullback.snd f T.ι) ≫ pullback.fst f T.ι
  have hm : m ≫ f = fieldMorphism B S hS T.toFunctor qT ≫ T.ι := by
    show (fieldMorphism B S hS T.toFunctor qT ≫ inv (pullback.snd f T.ι) ≫
      pullback.fst f T.ι) ≫ f = _
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc (inv (pullback.snd f T.ι)), IsIso.inv_hom_id, Category.id_comp]
  let g : qT.siteObject B S hS T.toFunctor ⟶ V := yoneda.preimage m
  have hg : yoneda.map g = m := yoneda.map_preimage _
  have hfm : fieldMorphism B S hS (yoneda.obj V)
      (FieldValuedPoint.map B S hS (yoneda.obj (qT.siteObject B S hS T.toFunctor))
        (yoneda.map g) (qT.tautologicalPoint B S hS T.toFunctor)) = yoneda.map g := by
    rw [fieldMorphism_map_yoneda]
    show yoneda.map (𝟙 (qT.siteObject B S hS T.toFunctor)) ≫ yoneda.map g = yoneda.map g
    simp
  have hfac : fieldMorphism B S hS (yoneda.obj V)
      (FieldValuedPoint.map B S hS (yoneda.obj (qT.siteObject B S hS T.toFunctor))
        (yoneda.map g) (qT.tautologicalPoint B S hS T.toFunctor)) ≫ f =
      fieldMorphism B S hS T.toFunctor qT ≫ T.ι := by
    rw [hfm, hg]
    exact hm
  refine ⟨FieldValuedPoint.map B S hS (yoneda.obj (qT.siteObject B S hS T.toFunctor))
    (yoneda.map g) (qT.tautologicalPoint B S hS T.toFunctor), ?_, ?_⟩
  · rw [← pointsMap_class, ← pointsMap_comp_apply, hg, hm, pointsMap_comp_apply,
      pointsMap_fieldMorphism_tautologicalPoint]
  · intro Z k hk
    have hcomp : fieldMorphism B S hS (yoneda.obj V)
        (FieldValuedPoint.map B S hS (yoneda.obj (qT.siteObject B S hS T.toFunctor))
          (yoneda.map g) (qT.tautologicalPoint B S hS T.toFunctor)) ≫ f ≫ k =
        fieldMorphism B S hS T.toFunctor qT ≫ T.ι ≫ k :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ k) hfac).trans (Category.assoc _ _ _))
    rw [hcomp]
    exact hk

/-! ### Stacks 0BBP -/

/-- **Stacks 0BBP, conditional on Stacks 0BBN.** Every point `x` of a decent algebraic space `X`
over `S` has an elementary étale neighborhood whose scheme is affine, whose distinguished point
is the only point above `x`, and whose residue field at that point is the residue field of `X`
at `x` through the induced homomorphism.

The hypothesis `h0BBN` is Stacks 0BBN: every quasi-compact algebraic space over `S` carries
stratification data in the sense of `AlgebraicGeometry.Space.SchemeStratification`, which is
clause (1), whose chain also satisfies clause (2), that every point represented by a
quasi-compact morphism from a field spectrum lies in exactly one stratum. -/
theorem exists_affine_elementaryEtaleNeighborhood
    (h0BBN : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      IsQuasiCompactSpace B S hS Y →
      ∃ strat : SchemeStratification B S hS Y,
        ∀ q : FieldValuedPoint B S hS Y,
          IsQuasiCompact B S hS (fieldMorphism B S hS Y q) →
          ∃ p : ℕ,
            q.class B S hS Y ∈ Set.range (pointsMap B S hS
              (strat.openPart p).toFunctor (strat.openPart p).ι) ∧
            q.class B S hS Y ∉ Set.range (pointsMap B S hS
              (strat.openPart (p + 1)).toFunctor (strat.openPart (p + 1)).ι))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hDecent : IsDecentSpace B S hS X) (x : points B S hS X) :
    ∃ E : ElementaryEtaleNeighborhood B S hS X hX x,
      IsAffine E.scheme.left.1 ∧
      (∀ y : points B S hS (yoneda.obj E.scheme),
        pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y = x →
          y = presheafPoint B S hS E.scheme E.point E.residueField_contained) ∧
      ∃ φ : residueField B S hS X hDecent x →+* E.scheme.left.1.residueField E.point,
        Function.Bijective φ ∧
          ∃ g : residueFieldObject B S hS E.scheme E.point E.residueField_contained ⟶
              (residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X,
            B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) ∧
              yoneda.map g ≫ residueFieldMorphism B S hS X hDecent x =
                yoneda.map (residueFieldMap B S hS E.scheme E.point
                  E.residueField_contained) ≫ E.toSpace := by
  classical
  -- A monomorphic quasi-compact field-valued representative of `x`, from decency.
  obtain ⟨p, hpclass, hpmono, hpqc⟩ := hDecent x
  -- A quasi-compact open subspace `G` of `X` whose point set contains `x`.
  obtain ⟨G, hG, hGqc, hxG, -⟩ := exists_isQuasiCompactSpace_isOpenSubspace_range_subset
    B S hS hX Set.univ isOpen_univ x (Set.mem_univ x)
  obtain ⟨y, hy⟩ := hxG
  have hGmono : Mono G.ι := mono_of_presheaf_isOpenImmersion hG.2
  obtain ⟨q, hqclass, hqmono, hqqc⟩ := exists_fieldValuedPoint_of_isOpenSubspace B S hS G hG
    p y (by rw [hy, hpclass]) hpmono hpqc
  -- What the proof uses out of Stacks 0BBN for `G`.
  obtain ⟨U, T, V, f, hUopen, hTclosed, hfetale, hfstIso, zT, hzT⟩ :
      ∃ (U : Subfunctor G.toFunctor) (T : Subfunctor U.toFunctor) (V : BigFppfOver B S hS)
        (f : yoneda.obj V ⟶ U.toFunctor),
        IsOpenSubspace B S hS U ∧ IsClosedSubspace B S hS T ∧ IsEtale B S hS f ∧
        IsIso (pullback.fst T.ι f) ∧
        ∃ zT : points B S hS T.toFunctor,
          pointsMap B S hS T.toFunctor (T.ι ≫ U.ι) zT = q.class B S hS G.toFunctor := by
    obtain ⟨strat, hlast⟩ := h0BBN hG.1 hGqc
    obtain ⟨n, hmem, hnotmem⟩ := hlast q hqqc
    obtain ⟨zT, hzT⟩ : q.class B S hS G.toFunctor ∈ Set.range (pointsMap B S hS
        (strat.stratum n).toFunctor ((strat.stratum n).ι ≫ (strat.openPart n).ι)) := by
      rw [strat.range_stratum n]
      exact ⟨hmem, hnotmem⟩
    exact ⟨strat.openPart n, strat.stratum n, strat.chart n, strat.chartHom n,
      strat.isOpenSubspace_openPart n, strat.isClosedSubspace_stratum n,
      strat.isEtale_chartHom n, strat.isIso_pullback_stratum n, zT, hzT⟩
  have hUmono : Mono U.ι := mono_of_presheaf_isOpenImmersion hUopen.2
  have hTmono : Mono T.ι := mono_of_isClosedImmersion B S hS (f := T.ι) hTclosed.2
  -- Push `q` into `U`, then into `T`.
  have hzU : pointsMap B S hS U.toFunctor U.ι
      (pointsMap B S hS T.toFunctor T.ι zT) = q.class B S hS G.toFunctor := by
    simpa [pointsMap_comp] using hzT
  obtain ⟨qU, hqUclass, hqUmono, hqUqc⟩ := exists_fieldValuedPoint_of_isOpenSubspace B S hS
    U hUopen q _ hzU hqmono hqqc
  obtain ⟨qT, hqTclass, hqTmono, hqTqc⟩ := exists_fieldValuedPoint_of_isClosedSubspace B S hS
    T hTclosed qU zT hqUclass.symm hqUmono hqUqc
  -- The chart meets the stratum isomorphically; move `qT` into the chart.
  have hsndIso := isIso_pullback_snd_of_isIso_pullback_fst B S hS f T.ι hfstIso
  obtain ⟨qV, hqVf, hqVmonoComp⟩ :=
    exists_fieldValuedPoint_chart_of_isIso_pullback_fst B S hS T f hfstIso qT
  have hqTmono' : Mono (fieldMorphism B S hS T.toFunctor qT) := hqTmono
  have hmonoUG : Mono (U.ι ≫ G.ι) := @mono_comp _ _ _ _ _ U.ι hUmono G.ι hGmono
  have hmonoTUG : Mono (T.ι ≫ U.ι ≫ G.ι) := @mono_comp _ _ _ _ _ T.ι hTmono (U.ι ≫ G.ι) hmonoUG
  have hmonoqTUG : Mono (fieldMorphism B S hS T.toFunctor qT ≫ T.ι ≫ U.ι ≫ G.ι) :=
    @mono_comp _ _ _ _ _ (fieldMorphism B S hS T.toFunctor qT) hqTmono'
      (T.ι ≫ U.ι ≫ G.ι) hmonoTUG
  have hqVMonoX : Mono (fieldMorphism B S hS (yoneda.obj V) qV ≫ (f ≫ U.ι ≫ G.ι)) :=
    hqVmonoComp (U.ι ≫ G.ι) hmonoqTUG
  have hqVMono : Mono (fieldMorphism B S hS (yoneda.obj V) qV) :=
    mono_of_mono (fieldMorphism B S hS (yoneda.obj V) qV) (f ≫ U.ι ≫ G.ι)
  -- An affine open of the chart around the image point.
  obtain ⟨W, j, hAff, hjOpen, w₀, hw₀⟩ :
      ∃ (W : BigFppfOver B S hS) (j : W ⟶ V), IsAffine W.left.1 ∧
        IsOpenImmersion B S hS (yoneda.map j) ∧
        ∃ w₀ : W.left.1, (BigFppfOver.toScheme B S hS).map j w₀ =
          pointsToScheme B S hS V (qV.class B S hS (yoneda.obj V)) := by
    set vPt := pointsToScheme B S hS V (qV.class B S hS (yoneda.obj V)) with hvPtDef
    set cover := ((BigFppfOver.toScheme B S hS).obj V).affineOpenCover with hcoverDef
    obtain ⟨c₀, hc₀⟩ := cover.covers vPt
    have hWcontains : B.Contains (Spec (cover.X (cover.idx vPt))) :=
      Scheme.size_lt_of_isOpenImmersion (cover.f (cover.idx vPt)) V.left.property
    let Wleft : B.Schemes := B.obj hWcontains
    let a : Wleft ⟶ V.left := B.inclusion.preimage (cover.f (cover.idx vPt))
    let W : BigFppfOver B S hS := Over.mk (a ≫ V.hom)
    let j : W ⟶ V := Over.homMk a (by rfl)
    have hja : (BigFppfOver.toScheme B S hS).map j = cover.f (cover.idx vPt) := by
      show B.inclusion.map (B.inclusion.preimage (X := Wleft) (Y := V.left)
        (cover.f (cover.idx vPt))) = cover.f (cover.idx vPt)
      exact B.inclusion.map_preimage _
    refine ⟨W, j, ?_, ?_, c₀, ?_⟩
    · show IsAffine (Spec (cover.X (cover.idx vPt)))
      infer_instance
    · refine (presheaf_yoneda_map_iff B S hS
        (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance j).2 ?_
      rw [hja]
      exact cover.map_prop (cover.idx vPt)
    · rw [hja]
      exact hc₀
  have hjMono : Mono (yoneda.map j) := mono_of_presheaf_isOpenImmersion hjOpen
  have huContained : B.Contains (Spec (.of (W.left.1.residueField w₀))) :=
    Scheme.size_lt_of_mono_quasiCompact (W.left.1.fromSpecResidueField w₀) W.left.property
  have hEtaleX : IsEtale B S hS (yoneda.map j ≫ f ≫ U.ι ≫ G.ι) :=
    isEtale_comp B S hS
      (isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hjOpen))
      (isEtale_comp B S hS hfetale
        (isEtale_comp B S hS
          (isEtale_of_presheaf_etale B S hS
            (presheaf_etale_of_isOpenImmersion B S hS hUopen.2))
          (isEtale_of_presheaf_etale B S hS
            (presheaf_etale_of_isOpenImmersion B S hS hG.2))))
  -- The distinguished point of `W` and the image of `qT` agree in the chart.
  have hpWToV : pointsMap B S hS (yoneda.obj W) (yoneda.map j)
      ((residueFieldPoint B S hS W w₀ huContained).class B S hS (yoneda.obj W)) =
        qV.class B S hS (yoneda.obj V) := by
    refine injective_pointsToScheme B S hS V ?_
    rw [pointsToScheme_pointsMap, pointsToScheme_residueFieldPoint]
    exact hw₀
  have hxT : pointsMap B S hS T.toFunctor (T.ι ≫ U.ι ≫ G.ι) zT = x := by
    have h1 : T.ι ≫ U.ι ≫ G.ι = (T.ι ≫ U.ι) ≫ G.ι := by simp
    rw [h1, pointsMap_comp_apply, hzT, hqclass, hy]
  have hqChart : pointsMap B S hS (yoneda.obj V) (f ≫ U.ι ≫ G.ι)
      (qV.class B S hS (yoneda.obj V)) = x := by
    rw [pointsMap_comp_apply, hqVf, hqTclass, ← pointsMap_comp_apply]
    exact hxT
  -- The residue-field point of `W` is monic into `X`.
  have hrMono : Mono (yoneda.map (residueFieldMap B S hS W w₀ huContained)) :=
    mono_yoneda_map_residueFieldMap B S hS W w₀ huContained
  have hpVM := fieldMorphism_map_residueFieldPoint B S hS W w₀ huContained (yoneda.map j)
  have hpVMono : Mono (fieldMorphism B S hS (yoneda.obj V)
      (FieldValuedPoint.map B S hS (yoneda.obj W) (yoneda.map j)
        (residueFieldPoint B S hS W w₀ huContained))) := by
    rw [hpVM]
    exact @mono_comp _ _ _ _ _ (yoneda.map (residueFieldMap B S hS W w₀ huContained)) hrMono
      (yoneda.map j) hjMono
  obtain ⟨e, he⟩ := iso_of_mono_of_point_eq B S hS (yoneda.obj V)
    (isAlgebraicSpace_yoneda B S hS V)
    (FieldValuedPoint.map B S hS (yoneda.obj W) (yoneda.map j)
      (residueFieldPoint B S hS W w₀ huContained)) qV hpWToV
  have heM : yoneda.map e.hom ≫ fieldMorphism B S hS (yoneda.obj V) qV =
      fieldMorphism B S hS (yoneda.obj V)
        (FieldValuedPoint.map B S hS (yoneda.obj W) (yoneda.map j)
          (residueFieldPoint B S hS W w₀ huContained)) := by
    show yoneda.map e.hom ≫ yonedaEquiv.symm (qV.value) = yonedaEquiv.symm _
    rw [yonedaEquiv_symm_naturality_left, he]
  have heMono : Mono (yoneda.map e.hom) := IsIso.mono_of_iso _
  have hmonoW : Mono (yoneda.map (residueFieldMap B S hS W w₀ huContained) ≫
      (yoneda.map j ≫ f ≫ U.ι ≫ G.ι)) := by
    have hcomp : yoneda.map (residueFieldMap B S hS W w₀ huContained) ≫
        (yoneda.map j ≫ f ≫ U.ι ≫ G.ι) =
        yoneda.map e.hom ≫ (fieldMorphism B S hS (yoneda.obj V) qV ≫ (f ≫ U.ι ≫ G.ι)) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t ↦ t ≫ (f ≫ U.ι ≫ G.ι)) (hpVM.symm.trans heM.symm)).trans
          (Category.assoc _ _ _))
    rw [hcomp]
    exact @mono_comp _ _ _ _ _ (yoneda.map e.hom) heMono
      (fieldMorphism B S hS (yoneda.obj V) qV ≫ (f ≫ U.ι ≫ G.ι)) hqVMonoX
  let E : ElementaryEtaleNeighborhood B S hS X hX x :=
    { scheme := W
      point := w₀
      residueField_contained := huContained
      toSpace := yoneda.map j ≫ f ≫ U.ι ≫ G.ι
      etale_toSpace := hEtaleX
      map_point := by
        rw [← class_residueFieldPoint, pointsMap_comp_apply, hpWToV]
        exact hqChart
      mono_residueField := hmonoW }
  refine ⟨E, hAff, ?_, ?_⟩
  · intro z hzFiber
    show z = presheafPoint B S hS W w₀ huContained
    have hz : pointsMap B S hS (yoneda.obj W) (yoneda.map j ≫ f ≫ U.ι ≫ G.ι) z = x := hzFiber
    refine pointsMap_injective_of_mono B S hS (yoneda.map j) ?_
    rw [← class_residueFieldPoint, hpWToV]
    have hb : pointsMap B S hS (yoneda.obj V) f (qV.class B S hS (yoneda.obj V)) =
        pointsMap B S hS T.toFunctor T.ι zT := by
      rw [hqVf, hqTclass]
    refine points_eq_of_isIso_pullback_snd B S hS f T.ι _ _ zT ?_ hb
    refine pointsMap_injective_of_mono B S hS (U.ι ≫ G.ι) ?_
    calc pointsMap B S hS U.toFunctor (U.ι ≫ G.ι)
          (pointsMap B S hS (yoneda.obj V) f
            (pointsMap B S hS (yoneda.obj W) (yoneda.map j) z))
        = pointsMap B S hS (yoneda.obj W) (yoneda.map j ≫ f ≫ U.ι ≫ G.ι) z := by
          simp only [pointsMap_comp_apply]
      _ = x := hz
      _ = pointsMap B S hS T.toFunctor (T.ι ≫ U.ι ≫ G.ι) zT := hxT.symm
      _ = pointsMap B S hS U.toFunctor (U.ι ≫ G.ι)
            (pointsMap B S hS T.toFunctor T.ι zT) := by
          simp only [pointsMap_comp_apply]
  · exact exists_bijective_residueFieldHom_of_elementaryEtaleNeighborhood B S hS hX hDecent x E

/-- **Stacks 0BBP.** Every point `x` of a decent algebraic space `X` over `S` has an elementary
étale neighborhood whose scheme is affine, whose distinguished point is the only point above
`x`, and whose residue field at that point is the residue field of `X` at `x` through the
induced homomorphism. -/
@[stacks 0BBP]
theorem exists_affine_elementaryEtaleNeighborhood'
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hDecent : IsDecentSpace B S hS X) (x : points B S hS X) :
    ∃ E : ElementaryEtaleNeighborhood B S hS X hX x,
      IsAffine E.scheme.left.1 ∧
      (∀ y : points B S hS (yoneda.obj E.scheme),
        pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y = x →
          y = presheafPoint B S hS E.scheme E.point E.residueField_contained) ∧
      ∃ φ : residueField B S hS X hDecent x →+* E.scheme.left.1.residueField E.point,
        Function.Bijective φ ∧
          ∃ g : residueFieldObject B S hS E.scheme E.point E.residueField_contained ⟶
              (residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X,
            B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) ∧
              yoneda.map g ≫ residueFieldMorphism B S hS X hDecent x =
                yoneda.map (residueFieldMap B S hS E.scheme E.point
                  E.residueField_contained) ≫ E.toSpace :=
  exists_affine_elementaryEtaleNeighborhood B S hS
    (fun {Y} hY hYqc => by
      obtain ⟨strat, hstrat⟩ :=
        exists_schemeStratification_quasiCompactPoint_mem_stratum B S hS Y hY hYqc
      refine ⟨strat, fun q hq => ?_⟩
      obtain ⟨p, hp⟩ := hstrat (q.class B S hS Y) q rfl hq
      rw [strat.range_stratum p] at hp
      exact ⟨p, hp.1, hp.2⟩)
    hX hDecent x

end AlgebraicGeometry.Space

end
