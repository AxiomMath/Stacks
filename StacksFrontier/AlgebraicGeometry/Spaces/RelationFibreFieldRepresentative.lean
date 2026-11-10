module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreInducing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fold5.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsInducingTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFibrePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibreMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibreTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# An étale quasi-compact field representative from finite relation fibres

Condition (2) of Stacks 03JU at a point `x` of an algebraic space `F` over `S` is that every
pair of points above `x` in every étale chart of `F` has finite relation fibre; condition (3)
is that `x` has a field-valued representative whose two self-intersection projections are
étale and quasi-compact. This file proves that (2) implies (3), which is the one implication
of Stacks 03JU that the other three sections of the lemma did not reach.

Let `φ : h_U ⟶ F` be a surjective étale chart, which an algebraic space has, and let `a` be a
point of `|U|` above `x`, which surjectivity provides. Write `u` for the point of the scheme
`U` underlying `a` and `P = Spec κ(u)` for the spectrum of its residue field, which is again
an object of the site. The canonical morphism `ν : P ⟶ U` is a monomorphism of schemes, hence
of the site, and `f = h_P ⟶ h_U ⟶ F` presents the same point `x`; it is the representative
condition (3) is proved for.

The self-fibre-product of `f` decomposes as `P ×_U (U ×_F U) ×_U P`, by the same observation
`CategoryTheory.IsPullback.selfPullback_comp` that the equivalence of conditions (1) and (2)
uses. Its middle layer `A = P ×_U (U ×_F U)`, which is `P ×_F U`, is étale over `P` as a base
change of the chart; and the apex `N`, which is `P ×_F P`, maps to `A` by a base change of the
monomorphism `ν`, so monomorphically. Two things follow.

* `N` maps monomorphically to `U ×_F U` as well, and both legs of that map land on `a`,
  because `|P|` is a one-point space. Condition (2) therefore makes `|N|` finite — this is the
  source's remark that condition (2) "really means" the self-fibre-product of the residue-field
  point has finitely many points.
* A monomorphism into a scheme étale over the spectrum of a field is, over that spectrum, the
  inclusion of a subfamily of a disjoint union of spectra of finite separable extensions, by
  Tag 02GL and Tag 03DP. So `N ⟶ P` is étale, with no finiteness needed; and it is
  quasi-compact because `|N|` is finite.

## Main definitions

No new definitions are introduced; the four conditions are those of
`StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers`.

## Main results

* `AlgebraicGeometry.etale_comp_of_mono_of_etale_to_spec_field`: a monomorphism into a scheme
  étale over the spectrum of a field is étale over that spectrum.
* `AlgebraicGeometry.quasiCompact_of_finite_source`: a morphism out of a scheme with finitely
  many points is quasi-compact.
* `HasFiniteRelationFiberAtEveryEtaleChart.hasEtaleQuasiCompactFieldRepresentative`, in the
  namespace `AlgebraicGeometry.Space`: **Stacks 03JU, part (2) implies part (3).**
* `HasFiniteRelationFiberAtEveryEtaleChart.hasMonomorphicFieldRepresentative`, in the same
  namespace: the composite of that implication with the tagged implication part (3) implies part
  (4). It carries no attribute of its own, being a composite of two tagged implications rather than
  a part of the lemma; it is the form the conditional statements of
  `StacksFrontier.AlgebraicGeometry.Spaces.FiniteFibresOneChart` carry as their hypothesis
  `h03JU`.

## Implementation notes

**Why the residue field and not an arbitrary representative.** Condition (3) is existential
over field-valued representatives, and it is false for most of them: for a transcendental
extension `k` of `κ(u)` the scheme `Spec k ×_F Spec k` contains `Spec (k ⊗_{κ(u)} k)`, which
has infinitely many points. The representative must be the residue field itself, and what
makes it work is exactly that `Spec κ(u) ⟶ U` is a monomorphism — Stacks 01L6, which Mathlib
has twice over: in the general form
`AlgebraicGeometry.SurjectiveOnStalks.mono_of_injective`, and for this morphism as the
composite of the `AlgebraicGeometry.IsPreimmersion` instance on
`AlgebraicGeometry.Scheme.fromSpecResidueField` with the instance deducing `Mono` from
`IsPreimmersion`.

**Étaleness needs no finiteness.** The source deduces that the two projections are étale *and*
quasi-compact from one structural statement, that the self-fibre-product is a *finite* disjoint
union of spectra of finite separable extensions. Here the two clauses are separated: Tag 03DP
identifies the monomorphism `N ⟶ A` with the inclusion of a subfamily, which is already enough
for étaleness over the base field by the converse half of Tag 02GL, and finiteness of `|N|` is
used only for quasi-compactness. This is a decomposition of the source's argument, not a
weakening of either clause.

**The second projection.** Only the first projection is computed. The second is obtained from
it by `CategoryTheory.Limits.pullbackSymmetry`, since `CategoryTheory.MorphismProperty.presheaf`
respects isomorphisms of arrows.

**Finiteness is transported through the points of Tag 03BU.** Condition (2) is stated for the
point quotient of Tag 03BU, while quasi-compactness is a statement about the underlying
topological space of a scheme. The comparison bijection
`AlgebraicGeometry.Space.pointsEquivScheme` of Tag 03BX moves finiteness across, and
`AlgebraicGeometry.Space.pointsMap_injective_of_mono` (Tag 06RV) is what makes the map from
the points of `N` to the relation fibre injective.

## References

* [Stacks Project, Tag 01L6](https://stacks.math.columbia.edu/tag/01L6)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03DP](https://stacks.math.columbia.edu/tag/03DP)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Monomorphisms into a scheme étale over a field -/

/-- **A monomorphism into a scheme étale over the spectrum of a field is itself étale over that
spectrum.** By Tag 02GL the target is, over `Spec k`, a disjoint union of spectra of finite
separable extensions of `k`; by Tag 03DP a monomorphism into such a disjoint union is the
inclusion of a subfamily of its components; and the converse half of Tag 02GL turns that
subfamily back into an étale morphism to `Spec k`.

No finiteness of the source is needed: the subfamily may be infinite. -/
theorem etale_comp_of_mono_of_etale_to_spec_field
    (k : Type u) [Field k] {Z V : Scheme.{u}} (h : Z ⟶ V) (hh : Mono h)
    (e : V ⟶ Spec (.of k)) (he : Etale e) : Etale (h ≫ e) := by
  have _ : Mono h := hh
  have _ : Etale e := he
  obtain ⟨I, K, hK, hAlg, hFin, hSep, eV, heV⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k e).mp inferInstance
  let _ (i : I) : Field (K i) := hK i
  let _ (i : I) : Algebra k (K i) := hAlg i
  let _ (i : I) : Module.Finite k (K i) := hFin i
  let _ (i : I) : Algebra.IsSeparable k (K i) := hSep i
  have _ : Mono (h ≫ eV.hom) := mono_comp _ _
  obtain ⟨J, eZ, heZ⟩ := exists_iso_coproduct_spec_of_mono K (h ≫ eV.hom)
  refine (etale_iff_iso_coproduct_spectra_finite_separable k (h ≫ e)).mpr
    ⟨↥J, fun j ↦ K j.1, fun j ↦ hK j.1, fun j ↦ hAlg j.1, fun j ↦ hFin j.1,
      fun j ↦ hSep j.1, eZ, ?_⟩
  have hdesc : Sigma.desc (fun j : J ↦ Sigma.ι (fun i ↦ Spec (.of (K i))) j.1) ≫
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) =
      Sigma.desc (fun j : J ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K j.1)))) := by
    ext j
    simp
  rw [← hdesc, ← Category.assoc, heZ, Category.assoc, heV]

/-- **A morphism out of a scheme with finitely many points is quasi-compact.** Every subset of
a finite topological space is compact, so in particular every preimage of an affine open is. -/
theorem quasiCompact_of_finite_source {Z Y : Scheme.{u}} (hZ : Finite Z) (f : Z ⟶ Y) :
    QuasiCompact f := by
  have _ : Finite Z := hZ
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro V hV
  exact (Set.toFinite (f ⁻¹' (V : Set Y))).isCompact

namespace Space

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` for presheaves on the big fppf site is found only with a larger budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_relationFibreFieldRepresentative
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_relationFibreFieldRepresentative
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Stacks 03JU, part (2) implies part (3) -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site
/-- **Stacks 03JU, part (2) implies part (3).** If every pair of points above a point `x` of an
algebraic space `F` over `S`, in every étale chart of `F`, has finite relation fibre, then `x`
has a field-valued representative whose two self-intersection projections are étale and
quasi-compact.

Take a surjective étale chart `φ : h_U ⟶ F` and a point `a` of `|U|` above `x`, let `u` be the
point of the scheme `U` underlying `a`, and let `ν : P ⟶ U` be the canonical morphism from the
spectrum `P` of the residue field at `u`. It is a monomorphism, by Stacks 01L6, and the
composite `f : h_P ⟶ F` presents `x`. Writing the self-fibre-product of `f` as
`N = P ×_U (U ×_F U) ×_U P`, its first projection factors as the base change of `ν` followed by
the base change of the chart, that is as a monomorphism followed by an étale morphism to `P`;
and `N` maps monomorphically to `U ×_F U` with both legs above `a`, so condition (2) makes
`|N|` finite. The first projection is therefore étale by Tags 02GL and 03DP and quasi-compact
by finiteness, and the second is the first conjugated by the symmetry of the
fibre product. -/
@[stacks 03JU "part (2) implies part (3)"]
theorem HasFiniteRelationFiberAtEveryEtaleChart.hasEtaleQuasiCompactFieldRepresentative
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasFiniteRelationFiberAtEveryEtaleChart B S hS F x) :
    HasEtaleQuasiCompactFieldRepresentative B S hS F x := by
  classical
  obtain ⟨U, φ, hφS, hφE⟩ := hF.exists_atlas
  obtain ⟨a, ha⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U φ).mp hφS x
  -- The residue-field point of the chart at the image of `a`.
  set u : (BigFppfOver.toScheme B S hS).obj U := pointsToScheme B S hS U a with hudef
  have hu : B.Contains (Spec (.of (((BigFppfOver.toScheme B S hS).obj U).residueField u))) :=
    B.residueField_spec_contains U.left.2 u
  have hmonoRes : Mono (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u) :=
    inferInstance
  set P : BigFppfOver B S hS := residueFieldObject B S hS U u hu with hPdef
  set ν : P ⟶ U := residueFieldMap B S hS U u hu with hνdef
  set q : FieldValuedPoint B S hS (yoneda.obj U) :=
    { carrier := ((BigFppfOver.toScheme B S hS).obj U).residueField u
      contained := hu
      toBase := ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u ≫ U.hom.1
      value := ν } with hqdef
  have hschemeν : (BigFppfOver.toScheme B S hS).map ν =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u := rfl
  have hqa : q.class B S hS (yoneda.obj U) = a := by
    refine injective_pointsToScheme B S hS U ?_
    rw [pointsToScheme_class]
    change (BigFppfOver.toScheme B S hS).map ν _ = u
    rw [hschemeν]
    exact Scheme.fromSpecResidueField_apply _ _
  set p : FieldValuedPoint B S hS F :=
    FieldValuedPoint.map B S hS (yoneda.obj U) φ q with hpdef
  have hpx : p.class B S hS F = x := by
    rw [hpdef, ← pointsMap_class, hqa]
    exact ha
  have hfm : fieldMorphism B S hS F p = yoneda.map ν ≫ φ := by
    refine (Equiv.symm_apply_eq yonedaEquiv).2 ?_
    exact ((yonedaEquiv_comp (yoneda.map ν) φ).trans
      (congrArg (φ.app (Opposite.op P)) (yonedaEquiv_yoneda_map ν))).symm
  -- The relation of the chart, as an object of the site.
  set R : BigFppfOver B S hS := hφE.rep.pullback φ with hRdef
  set h₁ : R ⟶ U := hφE.rep.fst' φ with hh1def
  set h₂ : R ⟶ U := hφE.rep.snd φ with hh2def
  have sqR : IsPullback (yoneda.map h₁) (yoneda.map h₂) φ φ := hφE.rep.isPullback' φ
  have hh₁Et : Etale ((BigFppfOver.toScheme B S hS).map h₁) :=
    hφE.property φ (yoneda.map h₂) h₁ sqR.flip
  -- The two-step decomposition of the self-fibre-product of `f`.
  set A : BigFppfOver B S hS := Limits.pullback ν h₁ with hAdef
  set α₁ : A ⟶ P := pullback.fst ν h₁ with hα1def
  set α₂ : A ⟶ R := pullback.snd ν h₁ with hα2def
  have sqA₀ : IsPullback α₁ α₂ ν h₁ := IsPullback.of_hasPullback ν h₁
  have sqA : IsPullback (yoneda.map α₁) (yoneda.map α₂) (yoneda.map ν) (yoneda.map h₁) :=
    sqA₀.map yoneda
  set N : BigFppfOver B S hS := Limits.pullback (α₂ ≫ h₂) ν with hNdef
  set μ₁ : N ⟶ A := pullback.fst (α₂ ≫ h₂) ν with hmu1def
  set μ₂ : N ⟶ P := pullback.snd (α₂ ≫ h₂) ν with hmu2def
  have sqN₀ : IsPullback μ₁ μ₂ (α₂ ≫ h₂) ν := IsPullback.of_hasPullback _ _
  have sqN : IsPullback (yoneda.map μ₁) (yoneda.map μ₂)
      (yoneda.map α₂ ≫ yoneda.map h₂) (yoneda.map ν) := by
    have hsq := sqN₀.map yoneda
    rwa [Functor.map_comp] at hsq
  have sqL : IsPullback (yoneda.map μ₁ ≫ yoneda.map α₁) (yoneda.map μ₂)
      (yoneda.map ν ≫ φ) (yoneda.map ν ≫ φ) :=
    IsPullback.selfPullback_comp sqR sqA sqN
  -- Étaleness of the middle layer, and monomorphy of the two base changes of `ν`.
  have hQEbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  have hα₁Et : Etale ((BigFppfOver.toScheme B S hS).map α₁) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) sqA₀.flip hh₁Et
  have hνMono : Mono ν := by
    refine (BigFppfOver.toScheme B S hS).mono_of_mono_map ?_
    rw [hschemeν]
    exact hmonoRes
  have hμ₁Mono : Mono μ₁ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms (BigFppfOver B S hS)) sqN₀.flip hνMono
  have hα₂Mono : Mono α₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms (BigFppfOver B S hS)) sqA₀ hνMono
  -- Condition (2) bounds the relation of `f`.
  have _ : Mono μ₁ := hμ₁Mono
  have _ : Mono α₂ := hα₂Mono
  set w : N ⟶ R := μ₁ ≫ α₂ with hwdef
  have hwMono : Mono w := by rw [hwdef]; exact mono_comp _ _
  have _ : Mono w := hwMono
  have hwYMono : Mono (yoneda.map w) := inferInstance
  have hνpt : ∀ z : points B S hS (yoneda.obj P),
      pointsMap B S hS (yoneda.obj P) (yoneda.map ν) z = a := by
    intro z
    have hsymm : yonedaEquiv.symm q.value = yoneda.map ν :=
      (Equiv.symm_apply_eq yonedaEquiv).2 (yonedaEquiv_yoneda_map ν).symm
    have hz := FieldValuedPoint.pointsMap_eq_class B S hS q z
    rw [hsymm, hqa] at hz
    exact hz
  have hfinφ : HasFiniteRelationFiber B S hS F U φ a a :=
    h U φ a a (isEtale_of_presheaf_etale B S hS hφE) ha ha
  set ιφ := sqR.isoIsPullback _ _ (IsPullback.of_hasPullback φ φ) with hιφdef
  have hιhom₁ : ιφ.hom ≫ pullback.fst φ φ = yoneda.map h₁ :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hιhom₂ : ιφ.hom ≫ pullback.snd φ φ = yoneda.map h₂ :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hSRfin : {r : points B S hS (yoneda.obj R) |
      pointsMap B S hS (yoneda.obj R) (yoneda.map h₁) r = a ∧
        pointsMap B S hS (yoneda.obj R) (yoneda.map h₂) r = a}.Finite := by
    have hpre : {r : points B S hS (yoneda.obj R) |
        pointsMap B S hS (yoneda.obj R) (yoneda.map h₁) r = a ∧
          pointsMap B S hS (yoneda.obj R) (yoneda.map h₂) r = a} =
        pointsMap B S hS (yoneda.obj R) ιφ.hom ⁻¹'
        {r | pointsMap B S hS (Limits.pullback φ φ) (pullback.fst φ φ) r = a ∧
          pointsMap B S hS (Limits.pullback φ φ) (pullback.snd φ φ) r = a} := by
      ext r
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← pointsMap_comp_apply, hιhom₁, hιhom₂]
    rw [hpre]
    exact hfinφ.preimage ((pointsEquivOfIso B S hS ιφ).injective.injOn)
  have hunivfin : (Set.univ : Set (points B S hS (yoneda.obj N))).Finite := by
    refine Set.Finite.of_finite_image (hSRfin.subset ?_)
      ((pointsMap_injective_of_mono B S hS (yoneda.map w)).injOn)
    rintro r ⟨n, -, rfl⟩
    have key : ∀ (c : N ⟶ P) (i : R ⟶ U), w ≫ i = c ≫ ν → ∀ n,
        pointsMap B S hS (yoneda.obj R) (yoneda.map i)
          (pointsMap B S hS (yoneda.obj N) (yoneda.map w) n) = a := by
      intro c i e n
      rw [← pointsMap_comp_apply, ← Functor.map_comp, e, Functor.map_comp, pointsMap_comp_apply]
      exact hνpt _
    exact ⟨key _ _ (by rw [hwdef, Category.assoc, Category.assoc, ← sqA₀.w]) n,
      key _ _ (by rw [hwdef, Category.assoc]; exact sqN₀.w) n⟩
  have hNfinite : Finite ((BigFppfOver.toScheme B S hS).obj N) := by
    have hpf : Finite (points B S hS (yoneda.obj N)) := Set.finite_univ_iff.mp hunivfin
    exact Finite.of_equiv _ (pointsEquivScheme B S hS N)
  -- The first projection of the self-fibre-product is étale and quasi-compact.
  have hsEt : Etale ((BigFppfOver.toScheme B S hS).map (μ₁ ≫ α₁)) := by
    rw [Functor.map_comp]
    exact etale_comp_of_mono_of_etale_to_spec_field
      (↥(((BigFppfOver.toScheme B S hS).obj U).residueField u))
      ((BigFppfOver.toScheme B S hS).map μ₁) (mono_toScheme_map B S hS μ₁)
      ((BigFppfOver.toScheme B S hS).map α₁) hα₁Et
  have hsQC : QuasiCompact ((BigFppfOver.toScheme B S hS).map (μ₁ ≫ α₁)) :=
    quasiCompact_of_finite_source hNfinite _
  have _ : MorphismProperty.IsStableUnderBaseChange
      ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})) := .inf
  have hsPre := (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
    (μ₁ ≫ α₁)).2 ⟨hsEt, hsQC⟩
  -- The property of being étale and quasi-compact on the site is invariant under isomorphism.
  have transfer : ∀ {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ Y) (f : X ⟶ T)
      (g : Y ⟶ T),
      e.hom ≫ g = f → (MorphismProperty.inverseImage
        ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
          (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
        (BigFppfOver.toScheme B S hS)).presheaf f → (MorphismProperty.inverseImage
        ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
          (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
        (BigFppfOver.toScheme B S hS)).presheaf g := by
    intro X Y T e f g hfg hf
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk e (Iso.refl T) (by simpa using hfg))).1 hf
  have sqLf : IsPullback (yoneda.map μ₁ ≫ yoneda.map α₁) (yoneda.map μ₂)
      (fieldMorphism B S hS F p) (fieldMorphism B S hS F p) := by
    rw [hfm]; exact sqL
  have hfst := transfer
    (sqLf.isoIsPullback _ _
      (IsPullback.of_hasPullback (fieldMorphism B S hS F p) (fieldMorphism B S hS F p)))
    (yoneda.map (μ₁ ≫ α₁)) _
    (by rw [Functor.map_comp]; exact IsPullback.isoIsPullback_hom_fst _ _ _ _) hsPre
  have hsnd := transfer
    (pullbackSymmetry (fieldMorphism B S hS F p) (fieldMorphism B S hS F p)) _ _
    (pullbackSymmetry_hom_comp_snd _ _) hfst
  exact ⟨p, hpx, hfst, hsnd⟩

/-- **Stacks 03JU, condition (2) implies condition (4).** A point of an algebraic space over
`S` at which every pair of points above it in every étale chart has finite relation fibre has
a field-valued representative presenting it by a monomorphism.

This is the composite of
`HasFiniteRelationFiberAtEveryEtaleChart.hasEtaleQuasiCompactFieldRepresentative` above
with part (3) implies part (4),
`AlgebraicGeometry.Space.HasEtaleQuasiCompactFieldRepresentative.hasMonomorphicFieldRepresentative`
(a composite of two implications of a lemma is not one of its parts, so it carries no attribute
of its own and the two tags stay where they are). It is stated because it is exactly the
hypothesis `h03JU` that the two conditional statements of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteFibresOneChart` carry, so those statements become
unconditional by supplying this. -/
theorem HasFiniteRelationFiberAtEveryEtaleChart.hasMonomorphicFieldRepresentative
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasFiniteRelationFiberAtEveryEtaleChart B S hS F x) :
    HasMonomorphicFieldRepresentative B S hS F x :=
  HasEtaleQuasiCompactFieldRepresentative.hasMonomorphicFieldRepresentative B S hS F hF
    (HasFiniteRelationFiberAtEveryEtaleChart.hasEtaleQuasiCompactFieldRepresentative
      B S hS F hF h)

end Space

end AlgebraicGeometry

end
