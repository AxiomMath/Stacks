module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupOfEffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionByNormalizedBlowUps
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.FibreOverClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.NormalizationEtaleBaseChange

/-!
# Normalized blowups at closed points under étale base change

Let `φ : T ⟶ A` be an étale morphism of algebraic spaces over a scheme `S`, let `a ∈ |A|` and
`t ∈ |T|` be closed points with `φ⁻¹{a} = {t}`, and let `g : A' ⟶ A` be the normalization of the
blowing up of `A` at `a`. Then the base change `T ×_A A' ⟶ T` is the normalization of the blowing
up of `T` at `t`: blowing up commutes with flat base change (Stacks 085S), the centre pulls back to
the centre, and normalization commutes with étale base change (Stacks 07U4). If instead no point of
`T` lies over `a` and `T` is normal, the base change is an isomorphism.

These are the two facts behind the proof of Stacks 0BHL: a normalized blowing up at a closed point
of an algebraic space over `X` restricts, over an elementary étale neighbourhood of the image
point, to the normalized blowing up at the corresponding point, and over every other chosen
neighbourhood to an isomorphism.

## Main results

* `AlgebraicGeometry.Space.IsBlowupAtClosedPoint.isBlowupAlong`: the blowing up at a closed point
  is the blowing up in the reduced closed subspace on that point.
* `AlgebraicGeometry.Space.isBlowupAtClosedPoint_of_isPullback_of_isEtale` and
  `AlgebraicGeometry.Space.isIso_of_isPullback_of_isBlowupAtClosedPoint_of_isEtale`: the two cases
  for a blowing up.
* `AlgebraicGeometry.Space.isNormalizationOfBlowupAtClosedPoint_fiberProduct_of_isEtale` and
  `AlgebraicGeometry.Space.isIso_fiberProduct_of_isNormalizationOfBlowupAtClosedPoint`: the two
  cases for a normalized blowing up.
* `AlgebraicGeometry.Space.IsNormalizationOfBlowupAtClosedPoint.exists_iso`: two normalized
  blowings up at the same closed point are isomorphic over the base.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_NormalizedBlowupEtaleBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_NormalizedBlowupEtaleBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The blowing up at a closed point is the blowing up in the reduced closed subspace on the
point: being the blowing up is invariant under isomorphism over the base. -/
theorem IsBlowupAtClosedPoint.isBlowupAlong {X Y : AlgebraicSpaces B S hS}
    {z : points B S hS X.obj} {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsBlowupAtClosedPoint B S hS z hz f) :
    IsBlowupAlong B S hS (closedPointSubspace B S hS z hz) f := by
  obtain ⟨W, b, hb, e, he⟩ := h
  rw [← he]
  exact IsBlowupAlong.of_iso_over hb e

/-- **A blowing up at a closed point base changes, along an étale morphism with a single point
over the centre, to the blowing up at that point.** -/
theorem isBlowupAtClosedPoint_of_isPullback_of_isEtale {T A A' W : AlgebraicSpaces B S hS}
    {φ : T ⟶ A} (hφ : IsEtale B S hS φ.hom) {a : points B S hS A.obj}
    {ha : IsClosed ({a} : Set (points B S hS A.obj))} {t : points B S hS T.obj}
    (ht : IsClosed ({t} : Set (points B S hS T.obj)))
    (hfib : pointsMap B S hS T.obj φ.hom ⁻¹' {a} = {t}) {b : A' ⟶ A}
    (hb : IsBlowupAtClosedPoint B S hS a ha b) {q : W ⟶ T} {r : W ⟶ A'}
    (sq : IsPullback q r φ b) : IsBlowupAtClosedPoint B S hS t ht q := by
  have h := isBlowupAlong_preimage_of_isPullback_of_isFlat (isFlat_of_isEtale B S hS hφ)
    hb.isBlowupAlong sq
  rw [preimageClosedSubspace_closedPointSubspace φ hφ ha ht hfib] at h
  exact isBlowupAtClosedPoint_of_isBlowupAlong h

/-- **A blowing up at a closed point base changes to an isomorphism along a morphism none of
whose points lies over the centre.** The inverse image of the centre has no points, hence is an
effective Cartier divisor, and the blowing up in an effective Cartier divisor is an
isomorphism. -/
theorem isIso_of_isPullback_of_isBlowupAtClosedPoint_of_isEtale {T A A' W : AlgebraicSpaces B S hS}
    {φ : T ⟶ A} (hφ : IsEtale B S hS φ.hom) {a : points B S hS A.obj}
    {ha : IsClosed ({a} : Set (points B S hS A.obj))}
    (hfib : pointsMap B S hS T.obj φ.hom ⁻¹' {a} = ∅) {b : A' ⟶ A}
    (hb : IsBlowupAtClosedPoint B S hS a ha b) {q : W ⟶ T} {r : W ⟶ A'}
    (sq : IsPullback q r φ b) : IsIso q := by
  have h := isBlowupAlong_preimage_of_isPullback_of_isFlat (isFlat_of_isEtale B S hS hφ)
    hb.isBlowupAlong sq
  refine h.isIso_of_isEffectiveCartierDivisor
    (isEffectiveCartierDivisor_of_isEmpty_points B S hS T _ ⟨fun w => ?_⟩)
  have hw := Set.mem_range_self (f := pointsMap B S hS _
    (preimageClosedSubspace φ (closedPointSubspace B S hS a ha)).1.ι) w
  have hrange := subspacePointSet_preimage B S hS φ.hom (closedPointSubspace B S hS a ha).1
  simp only [subspacePointSet] at hrange
  change _ ∈ Set.range (pointsMap B S hS
    ((closedPointSubspace B S hS a ha).1.preimage φ.hom).toFunctor
    ((closedPointSubspace B S hS a ha).1.preimage φ.hom).ι) at hw
  rw [hrange, range_pointsMap_ι_closedPointSubspace a ha, hfib] at hw
  exact hw

/-- A normalization datum forces condition (2) of Stacks 0BB1: the chart condition at a surjective
étale atlas provides one chart with finitely many irreducible components on each quasi-compact
open, and one such chart suffices. -/
theorem NormalizationData.hasLocallyFiniteIrreducibleComponents
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) : HasLocallyFiniteIrreducibleComponents B S hS F := by
  obtain ⟨U, f, hfs, hfe⟩ := hF.exists_atlas
  have hfs' := isSurjective_of_presheafSurjective B S hS f hfs
  have hfe' := isEtale_of_presheaf_etale B S hS hfe
  exact (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents B S hS hF).mp
    ⟨U, f, hfs', hfe', D.finite_irreducibleComponents_of_chart U f hfs' hfe'⟩

/-- The base change along an étale morphism of a normalization of `X'` is, after composing with
an isomorphism, a normalization of the base change of `X'`, compatibly with the projections. -/
private theorem exists_normalizationData_fst_eq_of_isEtale
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {T A A' X' : AlgebraicSpaces B S hS} {φ : T ⟶ A} (hφ : IsEtale B S hS φ.hom)
    {g : A' ⟶ A} {b : X' ⟶ A} (D : NormalizationData B S hS X'.obj) (e : A'.obj ≅ D.space)
    (hge : g.hom = e.hom ≫ D.hom ≫ b.hom) :
    ∃ (D'' : NormalizationData B S hS (AlgebraicSpaces.fiberProduct B S hS φ b).obj)
      (i : (AlgebraicSpaces.fiberProduct B S hS φ g).obj ≅ D''.space),
      pullback.fst φ.hom g.hom = i.hom ≫ D''.hom ≫ pullback.fst φ.hom b.hom := by
  have sqb := AlgebraicSpaces.isPullback_fiberProduct B S hS φ b
  have hrb : IsEtale B S hS (pullback.snd φ.hom b.hom) :=
    isEtale_of_isPullback B S hS _ _ _ _ sqb hφ
  have hX'fin := D.hasLocallyFiniteIrreducibleComponents X'.property
  obtain ⟨D''⟩ := nonempty_normalizationData B S hS
    (AlgebraicSpaces.fiberProduct B S hS φ b).property
    (hasLocallyFiniteIrreducibleComponents_of_isEtale B S hS hX'fin hrb)
  obtain ⟨m, hm⟩ := D.isPullback_hom_of_isEtale D'' X'.property
    (AlgebraicSpaces.fiberProduct B S hS φ b).property _ hrb
  -- paste the normalization square over the blowup square
  have hpaste : IsPullback m (D''.hom ≫ pullback.fst φ.hom b.hom) (D.hom ≫ b.hom) φ.hom :=
    hm.paste_vert (IsPullback.of_hasPullback φ.hom b.hom).flip
  have hpaste' : IsPullback (D''.hom ≫ pullback.fst φ.hom b.hom) (m ≫ e.inv) φ.hom g.hom := by
    refine (IsPullback.of_iso hpaste (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_).flip
    · simp
    · simp
    · simp [hge]
    · simp
  exact ⟨D'', (IsPullback.of_hasPullback φ.hom g.hom).isoIsPullback _ _ hpaste',
    (IsPullback.isoIsPullback_hom_fst ..).symm⟩

/-- **A normalized blowing up at a closed point base changes, along an étale morphism with a
single point over the centre, to the normalized blowing up at that point.** -/
theorem isNormalizationOfBlowupAtClosedPoint_fiberProduct_of_isEtale
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {T A A' : AlgebraicSpaces B S hS}
    {φ : T ⟶ A} (hφ : IsEtale B S hS φ.hom) {a : points B S hS A.obj}
    {ha : IsClosed ({a} : Set (points B S hS A.obj))} {t : points B S hS T.obj}
    (ht : IsClosed ({t} : Set (points B S hS T.obj)))
    (hfib : pointsMap B S hS T.obj φ.hom ⁻¹' {a} = {t}) {g : A' ⟶ A}
    (hg : IsNormalizationOfBlowupAtClosedPoint B S hS a ha g) :
    IsNormalizationOfBlowupAtClosedPoint B S hS t ht
      (ObjectProperty.homMk (pullback.fst φ.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS φ g ⟶ T) := by
  obtain ⟨X', b, hb, D, e, hge⟩ := hg
  obtain ⟨D'', i, hi⟩ := exists_normalizationData_fst_eq_of_isEtale hφ D e hge
  exact ⟨_, _, isBlowupAtClosedPoint_of_isPullback_of_isEtale hφ ht hfib hb
    (AlgebraicSpaces.isPullback_fiberProduct B S hS φ b), D'', i, hi⟩

/-- **A normalized blowing up at a closed point base changes to an isomorphism along an étale
morphism with normal source none of whose points lies over the centre.** The blowing up base
changes to an isomorphism, and the normalization of a normal space is an isomorphism. -/
theorem isIso_fiberProduct_of_isNormalizationOfBlowupAtClosedPoint
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {T A A' : AlgebraicSpaces B S hS}
    {φ : T ⟶ A} (hφ : IsEtale B S hS φ.hom) (hT : Space.IsNormal B S hS T.obj)
    {a : points B S hS A.obj} {ha : IsClosed ({a} : Set (points B S hS A.obj))}
    (hfib : pointsMap B S hS T.obj φ.hom ⁻¹' {a} = ∅) {g : A' ⟶ A}
    (hg : IsNormalizationOfBlowupAtClosedPoint B S hS a ha g) :
    IsIso (pullback.fst φ.hom g.hom) := by
  obtain ⟨X', b, hb, D, e, hge⟩ := hg
  set Wb := AlgebraicSpaces.fiberProduct B S hS φ b
  have hqb : IsIso (ObjectProperty.homMk (pullback.fst φ.hom b.hom) : Wb ⟶ T) :=
    isIso_of_isPullback_of_isBlowupAtClosedPoint_of_isEtale hφ hfib hb
      (AlgebraicSpaces.isPullback_fiberProduct B S hS φ b)
  have hqb' : IsIso (pullback.fst φ.hom b.hom) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map
      (ObjectProperty.homMk (pullback.fst φ.hom b.hom) : Wb ⟶ T)))
  obtain ⟨D'', i, hi⟩ := exists_normalizationData_fst_eq_of_isEtale hφ D e hge
  have hWn : Space.IsNormal B S hS Wb.obj :=
    hasEtaleLocalProperty_of_isEtale B S hS Wb.property T.property
      (isEtale_of_isIso B S hS (pullback.fst φ.hom b.hom)) hT
  have hD'' : IsIso D''.hom := D''.isIso_hom_of_isNormal Wb.property hWn
  rw [hi]
  exact IsIso.comp_isIso' i.isIso_hom (IsIso.comp_isIso' hD'' hqb')

/-- **Two normalized blowings up at the same closed point are isomorphic over the base.** The
blowings up are, by their universal property, and normalizations of isomorphic spaces are,
because normalization commutes with étale base change and an isomorphism is étale. -/
theorem IsNormalizationOfBlowupAtClosedPoint.exists_iso {T W₁ W₂ : AlgebraicSpaces B S hS}
    {t : points B S hS T.obj} {ht : IsClosed ({t} : Set (points B S hS T.obj))}
    {q₁ : W₁ ⟶ T} {q₂ : W₂ ⟶ T}
    (h₁ : IsNormalizationOfBlowupAtClosedPoint B S hS t ht q₁)
    (h₂ : IsNormalizationOfBlowupAtClosedPoint B S hS t ht q₂) :
    ∃ e : W₁ ≅ W₂, e.hom ≫ q₂ = q₁ := by
  obtain ⟨X₁, b₁, hb₁, D₁, e₁, h₁e⟩ := h₁
  obtain ⟨X₂, b₂, hb₂, D₂, e₂, h₂e⟩ := h₂
  obtain ⟨ε, hε⟩ := hb₁.exists_iso_blowup X₂ b₂ hb₂.isBlowupAlong
  obtain ⟨m, hm⟩ := D₂.isPullback_hom_of_isEtale D₁ X₂.property X₁.property ε.hom.hom
    (isEtale_of_isIso B S hS ε.hom.hom)
  have : IsIso ε.hom.hom :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map ε.hom))
  have hmiso : IsIso m := hm.isIso_fst_of_isIso
  let μ : W₁.obj ≅ W₂.obj := e₁ ≪≫ asIso m ≪≫ e₂.symm
  refine ⟨ObjectProperty.isoMk _ μ, ?_⟩
  apply ObjectProperty.hom_ext
  change μ.hom ≫ q₂.hom = q₁.hom
  rw [h₁e, h₂e]
  simp only [μ, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hm.w, ← ObjectProperty.FullSubcategory.comp_hom, hε]

end AlgebraicGeometry.Space
