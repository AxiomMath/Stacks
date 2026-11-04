module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpPointTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageBlowUp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpClosedPointDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpNormal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.RationalStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.RationalSingularPointsResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUpsAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularPointBlowupChainResolution
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.DualizingQuotientBlowupChain
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUpNagataExtra
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormalityExtra

/-!
# The singular part of a chain of normalized blowups

Let `(A, 𝔪)` be a two-dimensional local normal Nagata domain defining a rational singularity and
`Z ⟶ Spec(A)` a chain of normalized blowups at closed points ([Stacks, Tag 0BGL]). This file
extracts from it a finite sequence of blowups in *singular* closed points `X ⟶ Spec(A)`, every
stage normal, whose singular points have the local rings of points of `Z`, compatibly with the
maps from `A`. It is the step of the proof of [Stacks, Tag 0BBV] that passes from the chain given
by [Stacks, Tag 0BBT] to a sequence of blowups in singular points.

Along the chain a normalized blowup is a blowup: at a singular point by [Stacks, Tag 0B4Z], since
the local ring there defines a rational singularity ([Stacks, Tag 0BG0]); at a regular point by
[Stacks, Tag 0AGR]. The steps at regular points are to be left out. Blowing up a regular point of
dimension two gives regular points over it, so leaving such a step out changes nothing near the
singular points. This is made precise by carrying along the chain an open subscheme `W` with open
immersions into `X` and into `Z`, over `Spec(A)`, whose images contain both singular loci
(`AlgebraicGeometry.SingularLociMatch`):

* at a regular centre `z` of `Z` the sequence `X` is kept, and `W` is shrunk to the inverse image
  of `Z ∖ {z}`, over which the blowup is an isomorphism;
* at a singular centre `z = j(w)` the sequence `X` is blown up at `ι(w)`, and `W` is replaced by
  its blowup at `w`, which is the base change of both blowups along the open immersions
  ([Stacks, Tag 0805]).

## Main definitions

* `AlgebraicGeometry.SingularLociMatch`: two schemes over a base share an open subscheme whose
  images contain both singular loci.

## Main results

* `AlgebraicGeometry.isNormal_blowUp_of_isNormal_blowUp_maximalIdealSheaf_stalk`: the blowup of a
  normal scheme at a closed point is normal when the blowup of its local ring is.
* `AlgebraicGeometry.singularLociMatch_blowUp_of_notMem_singularLocus`,
  `AlgebraicGeometry.singularLociMatch_blowUp`: the match survives the two kinds of step.
* `AlgebraicGeometry.exists_map_eq_span_singleton_of_singularLociMatch`: an ideal principal at
  all points of `Z` is principal at the singular points of `X`.
* `AlgebraicGeometry.exists_singularPointBlowupChain_of_normalizedBlowUpChain`: the singular part
  of a chain of normalized blowups of `Spec(A)`.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Local facts about one blowup -/

/-- A point is regular exactly when its image under a morphism inducing an isomorphism of local
rings is. -/
theorem mem_regularLocus_iff_of_isIso_stalkMap {X Y : Scheme.{u}} (φ : X ⟶ Y) (x : X)
    [IsIso (φ.stalkMap x)] : x ∈ regularLocus X ↔ φ x ∈ regularLocus Y := by
  let e := (asIso (φ.stalkMap x)).commRingCatIsoToRingEquiv
  constructor
  · intro h
    have : IsRegularLocalRing (X.presheaf.stalk x) := h
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · intro h
    have : IsRegularLocalRing (Y.presheaf.stalk (φ x)) := h
    exact IsRegularLocalRing.of_ringEquiv e

/-- A point is singular exactly when its image under a morphism inducing an isomorphism of local
rings is. -/
theorem mem_singularLocus_iff_of_isIso_stalkMap {X Y : Scheme.{u}} (φ : X ⟶ Y) (x : X)
    [IsIso (φ.stalkMap x)] : x ∈ singularLocus X ↔ φ x ∈ singularLocus Y :=
  not_congr (mem_regularLocus_iff_of_isIso_stalkMap φ x)

/-- A ring isomorphic to an integrally closed domain is one (as in `isNormal_iff_stalk_normal`). -/
private theorem exists_isDomain_isIntegrallyClosed_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] (e : R ≃+* S) :
    ∃ _ : IsDomain R, IsIntegrallyClosed R :=
  ⟨e.injective.isDomain e.toRingHom, IsIntegrallyClosed.of_equiv e.symm⟩

/-- A closed map sends closed points to closed points. -/
private theorem isClosed_singleton_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsClosedMap f) {x : X} (hx : IsClosed ({x} : Set X)) :
    IsClosed ({f x} : Set Y) := by
  rw [← Set.image_singleton]
  exact hf _ hx

/-- A morphism inducing an isomorphism of local rings at `x` preserves their Krull dimension. -/
private theorem ringKrullDim_stalk_eq_of_isIso_stalkMap {X Y : Scheme.{u}} (φ : X ⟶ Y) (x : X)
    [IsIso (φ.stalkMap x)] :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (φ x)) :=
  (asIso (φ.stalkMap x)).commRingCatIsoToRingEquiv.symm.ringKrullDim

/-- **The inverse image of a reduced closed point along an open immersion** is the reduced point
above it. -/
theorem vanishingIdeal_singleton_comap_of_isOpenImmersion {W X : Scheme.{u}} (ι : W ⟶ X)
    [IsOpenImmersion ι] (w : W) (hx : IsClosed ({ι w} : Set X)) :
    ∃ hw : IsClosed ({w} : Set W),
      (Scheme.IdealSheafData.vanishingIdeal (⟨{ι w}, hx⟩ : Closeds X)).comap ι =
        Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) := by
  let M := Scheme.IdealSheafData.vanishingIdeal (⟨{ι w}, hx⟩ : Closeds X)
  refine vanishingIdeal_singleton_comap ι (ι w) hx ι.isEmbedding.injective ?_ w rfl
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun p => ?_⟩⟩
  have hp : M.subschemeι p ∈ (M.support : Set X) := by
    rw [← M.range_subschemeι]
    exact ⟨p, rfl⟩
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hp
  have : p ∈ Set.range (pullback.snd ι M.subschemeι) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨w, hp.symm⟩
  exact this

/-- **The blowup of a normal scheme at a closed point is normal as soon as the blowup of the local
ring there in its maximal ideal is.** Off the centre the blowup does not change the local rings;
over the centre they are local rings of the blowup of `Spec 𝒪_{X, x}` ([Stacks, Tag 0805]). -/
theorem isNormal_blowUp_of_isNormal_blowUp_maximalIdealSheaf_stalk {X : Scheme.{u}} [IsNormal X]
    (x : X) (hx : IsClosed ({x} : Set X))
    (h : IsNormal (blowUp (maximalIdealSheaf (X.presheaf.stalk x)))) :
    IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))) := by
  rw [isNormal_iff_stalk_normal]
  intro q
  by_cases hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) q = x
  · obtain ⟨z, -, ε, -⟩ := exists_maximalIdealSheaf_point_of_blowUp (X.presheaf.stalk x) x hx
      (RingEquiv.refl _) q hq
    have : IsIntegrallyClosed
        ((blowUp (maximalIdealSheaf (X.presheaf.stalk x))).presheaf.stalk z) :=
      IsNormal.stalk_normal z
    exact exists_isDomain_isIntegrallyClosed_of_ringEquiv ε
  · have := isIso_stalkMap_blowUpToBase_of_ne x hx q hq
    let ε := (asIso ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : Closeds X))).stalkMap q)).commRingCatIsoToRingEquiv
    have : IsIntegrallyClosed (X.presheaf.stalk (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) q)) :=
      IsNormal.stalk_normal _
    exact exists_isDomain_isIntegrallyClosed_of_ringEquiv ε.symm

/-- **The local rings of the blowup over a regular closed point of dimension two are regular**
([Stacks, Tag 0AGR], after the flat base change to the local ring at the point). -/
theorem isRegularLocalRing_stalk_blowUp_of_blowUpToBase_eq {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))
    (hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) q = x) :
    IsRegularLocalRing ((blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).presheaf.stalk q) := by
  obtain ⟨z, -, ε, -⟩ := exists_maximalIdealSheaf_point_of_blowUp (X.presheaf.stalk x) x hx
    (RingEquiv.refl _) q hq
  have := (isRegular_blowUp_maximalIdeal (X.presheaf.stalk x) hdim).isRegularLocalRing_stalk z
  exact IsRegularLocalRing.of_ringEquiv ε.symm

/-- **The blowup of a normal scheme at a regular closed point of dimension two is normal.** -/
theorem isNormal_blowUp_of_isRegularLocalRing {X : Scheme.{u}} [IsNormal X] (x : X)
    (hx : IsClosed ({x} : Set X)) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2) :
    IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))) :=
  isNormal_blowUp_of_isNormal_blowUp_maximalIdealSheaf_stalk x hx
    (isNormal_of_isRegular _ (isRegular_blowUp_maximalIdeal (X.presheaf.stalk x) hdim))

/-- **The blowup of a normal scheme at a closed point whose local ring is a two-dimensional normal
Nagata domain defining a rational singularity is normal** ([Stacks, Tag 0B4Z]). -/
theorem isNormal_blowUp_of_definesRationalSingularity {X : Scheme.{u}} [IsNormal X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hnag : IsNagataRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (hrat : DefinesRationalSingularity (X.presheaf.stalk x)) :
    IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))) := by
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  have : IsNormalDomain (X.presheaf.stalk x) := ⟨inferInstance, inferInstance⟩
  exact isNormal_blowUp_of_isNormal_blowUp_maximalIdealSheaf_stalk x hx
    (isNormal_blowUp_maximalIdeal_of_forall_isIntegrallyClosed_pow _ fun n =>
      isIntegrallyClosed_maximalIdeal_pow_of_definesRationalSingularity _ hnag hdim hrat n)

/-- **The local rings of the blowup at its closed points have dimension two**, if those of the
scheme being blown up do and the local ring at the centre is a normal domain. -/
theorem ringKrullDim_stalk_blowUp_of_isClosed_of_isNormalDomain {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) (hx : IsClosed ({x} : Set X))
    [IsNormalDomain (X.presheaf.stalk x)]
    (hdim : ∀ y : X, IsClosed ({y} : Set X) → ringKrullDim (X.presheaf.stalk y) = 2)
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))
    (hqc : IsClosed ({q} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : Closeds X))))) :
    ringKrullDim
      ((blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).presheaf.stalk q) =
      2 := by
  let M := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  by_cases hq : blowUpToBase M q = x
  · obtain ⟨z, hzc, ⟨e⟩⟩ := exists_isClosed_ringEquiv_stalk_blowUp_maximalIdealSheaf
      (X.presheaf.stalk x) x hx (RingEquiv.refl _) q hq hqc
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact ringKrullDim_stalk_blowUp_maximalIdeal_eq_two_of_isClosed _ (hdim x hx) z hzc
  · have := isIso_stalkMap_blowUpToBase_of_ne x hx q hq
    rw [ringKrullDim_stalk_eq_of_isIso_stalkMap (blowUpToBase M) q]
    exact hdim _ (isClosed_singleton_apply (blowUpToBase M).isClosedMap hqc)

/-! ### Matching the singular points of two schemes over a base -/

/-- Two schemes `X` and `Z` over `S` *match along their singular points* if an open subscheme `W`
embeds into both, compatibly over `S`, with images containing the singular loci. Then every
singular point of either is the image of a point of `W`, at which both open immersions induce
isomorphisms of local rings. -/
def SingularLociMatch {S X Z : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) : Prop :=
  ∃ (W : Scheme.{u}) (ι : W ⟶ X) (j : W ⟶ Z), IsOpenImmersion ι ∧ IsOpenImmersion j ∧
    ι ≫ f = j ≫ g ∧ singularLocus X ⊆ Set.range ι ∧ singularLocus Z ⊆ Set.range j

/-- **Blowing up a regular closed point of `Z` keeps the match**, provided the points of the
blowup over it are regular: the common open subscheme is shrunk to the inverse image of the
complement of the point, over which the blowup is an isomorphism. The blowup is in any ideal
sheaf `M` supported at the point. -/
theorem singularLociMatch_blowUp_of_notMem_singularLocus {S X Z W : Scheme.{u}} {f : X ⟶ S}
    {g : Z ⟶ S} (ι : W ⟶ X) (j : W ⟶ Z) [IsOpenImmersion ι] [IsOpenImmersion j]
    (hιj : ι ≫ f = j ≫ g) (hX : singularLocus X ⊆ Set.range ι)
    (hZ : singularLocus Z ⊆ Set.range j) (z : Z) (M : Z.IdealSheafData)
    (hM : (M.support : Set Z) = {z}) (hzreg : z ∉ singularLocus Z)
    (hfib : ∀ q : blowUp M, blowUpToBase M q = z → q ∉ singularLocus (blowUp M))
    {Z' : Scheme.{u}} (e : Z' ≅ blowUp M) :
    SingularLociMatch f (e.hom ≫ blowUpToBase M ≫ g) := by
  have hU : ∀ y : Z, y ∈ M.support.compl ↔ y ≠ z := by
    intro y
    change y ∉ (M.support : Set Z) ↔ _
    rw [hM]
    rfl
  let j' : (j ⁻¹ᵁ M.support.compl).toScheme ⟶ Z' :=
    (j ∣_ M.support.compl) ≫ inv (blowUpToBase M ∣_ M.support.compl) ≫
      (blowUpToBase M ⁻¹ᵁ M.support.compl).ι ≫ e.inv
  have hj' : j' ≫ e.hom ≫ blowUpToBase M = (j ⁻¹ᵁ M.support.compl).ι ≫ j := by
    calc j' ≫ e.hom ≫ blowUpToBase M = (j ∣_ M.support.compl) ≫
          inv (blowUpToBase M ∣_ M.support.compl) ≫
            ((blowUpToBase M ⁻¹ᵁ M.support.compl).ι ≫ blowUpToBase M) := by
          simp only [j', Category.assoc, Iso.inv_hom_id_assoc]
      _ = (j ∣_ M.support.compl) ≫ Scheme.Opens.ι M.support.compl := by
          rw [← morphismRestrict_ι (blowUpToBase M), IsIso.inv_hom_id_assoc]
      _ = _ := morphismRestrict_ι _ _
  refine ⟨(j ⁻¹ᵁ M.support.compl).toScheme, (j ⁻¹ᵁ M.support.compl).ι ≫ ι, j', inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hιj, ← reassoc_of% hj']
  · intro x hx
    obtain ⟨w, rfl⟩ := hX hx
    have hw : w ∈ singularLocus W := (mem_singularLocus_iff_of_isIso_stalkMap ι w).mpr hx
    have hjw : j w ∈ singularLocus Z := (mem_singularLocus_iff_of_isIso_stalkMap j w).mp hw
    have hwU : w ∈ j ⁻¹ᵁ M.support.compl := (hU (j w)).mpr fun h => hzreg (h ▸ hjw)
    exact ⟨⟨w, hwU⟩, rfl⟩
  · intro q' hq'
    have hq : e.hom q' ∈ singularLocus (blowUp M) :=
      (mem_singularLocus_iff_of_isIso_stalkMap e.hom q').mp hq'
    have hπq : blowUpToBase M (e.hom q') ≠ z := fun h => hfib _ h hq
    have hqU : e.hom q' ∈ blowUpToBase M ⁻¹ᵁ M.support.compl := (hU _).mpr hπq
    have := isIso_stalkMap_of_isIso_morphismRestrict (blowUpToBase M)
      (inferInstance : IsIso (blowUpToBase M ∣_ M.support.compl)) hqU
    have hsing : blowUpToBase M (e.hom q') ∈ singularLocus Z :=
      (mem_singularLocus_iff_of_isIso_stalkMap (blowUpToBase M) (e.hom q')).mp hq
    obtain ⟨w, hw⟩ := hZ hsing
    have hwU : w ∈ j ⁻¹ᵁ M.support.compl := by
      change j w ∈ M.support.compl
      rw [hw]
      exact hqU
    refine ⟨⟨w, hwU⟩, ?_⟩
    have hpt : blowUpToBase M (e.hom (j' ⟨w, hwU⟩)) = blowUpToBase M (e.hom q') := by
      change (j' ≫ e.hom ≫ blowUpToBase M) ⟨w, hwU⟩ = _
      rw [hj']
      exact hw
    have hnot : blowUpToBase M (e.hom (j' ⟨w, hwU⟩)) ∉ (M.support : Set Z) := by
      rw [hpt]
      exact hqU
    have := blowUpToBase_injective_of_notMem_support M hnot hpt
    simpa using congrArg e.inv this

/-- A singular point of the blowup of `Y` at a closed point `y` lies over the singular locus or
over `y`; so if both lie in the range of an open immersion `k : W ⟶ Y`, the singular point lies in
the range of the base change of `k` along the blowup. -/
theorem mem_range_of_mem_singularLocus_blowUp {W Y : Scheme.{u}} (k : W ⟶ Y)
    {N : W.IdealSheafData} (M : Y.IdealSheafData) (h : blowUp N ⟶ blowUp M)
    (hsq : IsPullback (blowUpToBase N) h k (blowUpToBase M)) (y : Y) (hy : IsClosed ({y} : Set Y))
    (hM : M = Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))
    (hyk : y ∈ Set.range k) (hYk : singularLocus Y ⊆ Set.range k) (q : blowUp M)
    (hq : q ∈ singularLocus (blowUp M)) : q ∈ Set.range h := by
  subst hM
  have hqk : blowUpToBase _ q ∈ Set.range k := by
    by_cases hqy : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{y}, hy⟩ : Closeds Y)) q = y
    · rw [hqy]
      exact hyk
    · have := isIso_stalkMap_blowUpToBase_of_ne y hy q hqy
      exact hYk ((mem_singularLocus_iff_of_isIso_stalkMap _ q).mp hq)
  obtain ⟨v, hv⟩ := hqk
  obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback hsq v q hv
  exact ⟨p, hp⟩

/-- **Blowing up corresponding closed points keeps the match.** If `w` is a point of the common
open subscheme with closed images `ι(w)` in `X` and `j(w)` in `Z`, then the blowup of `W` at `w`
is the base change of both blowups along the open immersions ([Stacks, Tag 0805]), and it is a
common open subscheme of the two blowups. -/
theorem singularLociMatch_blowUp {S X Z W : Scheme.{u}} {f : X ⟶ S} {g : Z ⟶ S}
    (ι : W ⟶ X) (j : W ⟶ Z) [IsOpenImmersion ι] [IsOpenImmersion j]
    (hιj : ι ≫ f = j ≫ g) (hX : singularLocus X ⊆ Set.range ι)
    (hZ : singularLocus Z ⊆ Set.range j) (w : W) (hx : IsClosed ({ι w} : Set X))
    (hz : IsClosed ({j w} : Set Z)) {Z' : Scheme.{u}}
    (e : Z' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{j w}, hz⟩ : Closeds Z))) :
    SingularLociMatch
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{ι w}, hx⟩ : Closeds X)) ≫ f)
      (e.hom ≫ blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{j w}, hz⟩ : Closeds Z)) ≫ g) := by
  obtain ⟨hw, hιc⟩ := vanishingIdeal_singleton_comap_of_isOpenImmersion ι w hx
  obtain ⟨hw', hjc⟩ := vanishingIdeal_singleton_comap_of_isOpenImmersion j w hz
  generalize hMx : Scheme.IdealSheafData.vanishingIdeal (⟨{ι w}, hx⟩ : Closeds X) = Mx at hιc ⊢
  generalize hMz : Scheme.IdealSheafData.vanishingIdeal (⟨{j w}, hz⟩ : Closeds Z) = Mz at hjc e ⊢
  generalize hN : Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) = N at hιc
  have key₁ := exists_isPullback_blowUpToBase_comap ι Mx
  rw [hιc] at key₁
  obtain ⟨h₁, hsq₁⟩ := key₁
  have key₂ := exists_isPullback_blowUpToBase_comap j Mz
  rw [hjc.trans hN] at key₂
  obtain ⟨h₂, hsq₂⟩ := key₂
  have : IsOpenImmersion h₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq₁
    inferInstance
  have : IsOpenImmersion h₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq₂
    inferInstance
  refine ⟨blowUp N, h₁, h₂ ≫ e.inv, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [← Category.assoc h₁, ← hsq₁.w, Category.assoc, hιj, ← Category.assoc, hsq₂.w]
    simp
  · exact mem_range_of_mem_singularLocus_blowUp ι Mx h₁ hsq₁ (ι w) hx hMx.symm ⟨w, rfl⟩ hX
  · intro q' hq'
    have hq : e.hom q' ∈ singularLocus (blowUp Mz) :=
      (mem_singularLocus_iff_of_isIso_stalkMap e.hom q').mp hq'
    obtain ⟨p, hp⟩ := mem_range_of_mem_singularLocus_blowUp j Mz h₂ hsq₂ (j w) hz hMz.symm
      ⟨w, rfl⟩ hZ _ hq
    refine ⟨p, ?_⟩
    rw [Scheme.Hom.comp_apply, hp]
    simp

/-- **A scheme matching a normal scheme along the singular loci is normal**: its regular points
are normal, and its singular points have the local rings of points of the normal scheme. -/
theorem isNormal_of_singularLociMatch {S X Z : Scheme.{u}} {f : X ⟶ S} {g : Z ⟶ S}
    (h : SingularLociMatch f g) [IsNormal Z] : IsNormal X := by
  obtain ⟨W, ι, j, hι, hj, -, hX, -⟩ := h
  rw [isNormal_iff_stalk_normal]
  intro x
  by_cases hx : x ∈ singularLocus X
  · obtain ⟨w, rfl⟩ := hX hx
    let ε := (asIso (ι.stalkMap w)).commRingCatIsoToRingEquiv.trans
      (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.symm
    have : IsIntegrallyClosed (Z.presheaf.stalk (j w)) := IsNormal.stalk_normal _
    exact exists_isDomain_isIntegrallyClosed_of_ringEquiv ε
  · have : IsRegularLocalRing (X.presheaf.stalk x) := not_not.mp hx
    exact ⟨(isNormalDomain_of_isRegularLocalRing _).1, (isNormalDomain_of_isRegularLocalRing _).2⟩

/-- **An ideal principal at all points of `Z` is principal at the singular points of a scheme
matching `Z` along the singular loci over `Spec(A)`**: at such a point the local ring is that of
a point of `Z`, compatibly with the maps from `A`. -/
theorem exists_map_eq_span_singleton_of_singularLociMatch {A : Type u} [CommRing A]
    {X Z : Scheme.{u}} {f : X ⟶ Spec (.of A)} {g : Z ⟶ Spec (.of A)} (h : SingularLociMatch f g)
    (J : Ideal A) (hZ : ∀ z : Z, ∃ t, J.map (stalkAlgebraOfSpec A g z) = Ideal.span {t})
    (x : X) (hx : x ∈ singularLocus X) :
    ∃ t, J.map (stalkAlgebraOfSpec A f x) = Ideal.span {t} := by
  obtain ⟨W, ι, j, hι, hj, hιj, hX, -⟩ := h
  obtain ⟨w, rfl⟩ := hX hx
  obtain ⟨t, ht⟩ := hZ (j w)
  let ε := (asIso (ι.stalkMap w)).commRingCatIsoToRingEquiv
  have key : (J.map (stalkAlgebraOfSpec A f (ι w))).map ε.toRingHom =
      Ideal.span {(j.stalkMap w).hom t} := by
    have h1 := stalkAlgebraOfSpec_comp A ι f w
    rw [hιj, stalkAlgebraOfSpec_comp A j g w] at h1
    rw [Ideal.map_map]
    have h3 : ε.toRingHom.comp (stalkAlgebraOfSpec A f (ι w)) =
        (ι.stalkMap w).hom.comp (stalkAlgebraOfSpec A f (ι w)) := by
      ext r
      rfl
    rw [h3, ← h1, ← Ideal.map_map, ht, Ideal.map_span, Set.image_singleton]
  refine ⟨ε.symm.toRingHom ((j.stalkMap w).hom t), ?_⟩
  have := congrArg (Ideal.map ε.symm.toRingHom) key
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton] at this
  rw [← this, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id]

/-! ### The singular part of a chain of normalized blowups -/

/-- **The singular part of a chain of normalized blowups of `Spec(A)`**, for `(A, 𝔪)` a
two-dimensional local normal Nagata domain defining a rational singularity. Every stage `Z` of the
chain is normal, its local rings at closed points have dimension two, and there is a finite
sequence of blowups in singular closed points `X ⟶ Spec(A)` with normal stages matching `Z`
along the singular loci over `Spec(A)`.

Along the chain, a normalized blowup at a point `z` is the blowup: at a singular point by
[Stacks, Tag 0B4Z], the local ring there defining a rational singularity by
[Stacks, Tag 0BG0]; at a regular point by [Stacks, Tag 0AGR]. A regular centre is left out of `X`
(`AlgebraicGeometry.singularLociMatch_blowUp_of_notMem_singularLocus`), and a singular centre is
blown up in `X` too (`AlgebraicGeometry.singularLociMatch_blowUp`). -/
theorem exists_singularPointBlowupChain_of_normalizedBlowUpChain (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A)
    (hS : ∀ U : (Spec (.of A)).Opens, IsCompact (U : Set (Spec (.of A))) →
      (irreducibleComponents U).Finite)
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of A)} (hchain : NormalizedBlowUpChain (Spec (.of A)) hS Z g) :
    IsNormal Z ∧ (∀ z : Z, IsClosed ({z} : Set Z) → ringKrullDim (Z.presheaf.stalk z) = 2) ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) X f ∧ SingularLociMatch f g := by
  have : IsNormal (Spec (.of A)) := isNormal_spec (.of A)
  have hNagata : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A ‹_›
  have hdimS : topologicalKrullDim (Spec (.of A)) = 2 := by
    rw [← hdim]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
  induction hchain with
  | normalization hproper =>
    have := Scheme.isIso_normalization_of_isNormal (Spec (.of A)) hS
    set ν := Scheme.normalization (Spec (.of A)) hS
    refine ⟨Scheme.isNormal_normalizationScheme _ hS, fun z hz => ?_, Spec (.of A), 𝟙 _,
      .refl inferInstance, Scheme.normalizationScheme (Spec (.of A)) hS, ν, 𝟙 _, inferInstance,
      inferInstance, by simp, fun x _ => ?_, fun z _ => ⟨z, rfl⟩⟩
    · have hνz := isClosed_singleton_apply ν.homeomorph.isClosedMap hz
      have hcl : ν z = IsLocalRing.closedPoint A := by
        have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hνz
        exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
      rw [ringKrullDim_stalk_eq_of_isIso_stalkMap ν z, hcl, ringKrullDim_stalk_closedPoint, hdim]
    · obtain ⟨z, hz⟩ := ν.homeomorph.surjective x
      exact ⟨z, hz⟩
  | @blowUp Z g previous hZc c hc hproper ih =>
    obtain ⟨hZn, hdimZ, X, f, hchainX, hmatch⟩ := ih
    have hg : IsModification g := isModification_of_normalizedBlowUpChain hdimS previous
    have : IsProper g := hg.isProper
    have : IsIntegral Z := hg.source_isIntegral
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
    have hdimc : ringKrullDim (Z.presheaf.stalk c) = 2 := hdimZ c hc
    have : IsNormalDomain (Z.presheaf.stalk c) := ⟨inferInstance, IsNormal.stalk_normal c⟩
    set Mc := Scheme.IdealSheafData.vanishingIdeal (⟨{c}, hc⟩ : Closeds Z)
    -- the blowup at `c` is normal
    have hBn : IsNormal (blowUp Mc) := by
      by_cases hsing : c ∈ singularLocus Z
      · have hnag : IsNagataRing (Z.presheaf.stalk c) :=
          isNagataRing_stalk_of_isNagataScheme (isNagataScheme_of_locallyOfFiniteType g hNagata) c
        have hη : c ≠ genericPoint Z := ne_genericPoint_of_ringKrullDim_stalk_eq_two c hdimc
        exact isNormal_blowUp_of_definesRationalSingularity c hc hnag hdimc
          (definesRationalSingularity_stalk_of_isModification A hdim hrat g hg c hc hη)
      · have : IsRegularLocalRing (Z.presheaf.stalk c) := not_not.mp hsing
        exact isNormal_blowUp_of_isRegularLocalRing c hc hdimc
    have := hBn
    let e := Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp hZc c hc
    have he : Stacks.Blowup.normalizedBlowUp Z hZc c hc ≫ g = e.hom ≫ blowUpToBase Mc ≫ g := by
      rw [← Category.assoc,
        Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp_hom_blowUpToBase hZc c hc]
    refine ⟨inferInstance, fun q hq => ?_, ?_⟩
    · rw [ringKrullDim_stalk_eq_of_isIso_stalkMap e.hom q]
      exact ringKrullDim_stalk_blowUp_of_isClosed_of_isNormalDomain c hc hdimZ (e.hom q)
        (isClosed_singleton_apply e.hom.homeomorph.isClosedMap hq)
    rw [he]
    obtain ⟨W, ι, j, hι, hj, hιj, hXs, hZs⟩ := hmatch
    by_cases hsing : c ∈ singularLocus Z
    · -- a singular centre is blown up in `X` too
      obtain ⟨w, rfl⟩ := hZs hsing
      have hxs : ι w ∈ singularLocus X := (mem_singularLocus_iff_of_isIso_stalkMap ι w).mp
        ((mem_singularLocus_iff_of_isIso_stalkMap j w).mpr hsing)
      have : IsNormal X := hchainX.last
      have hf : IsModification f :=
        isModification_of_singularPointBlowupChain (fun _ h => h) hNagata hdimS hchainX
      have : IsProper f := hf.isProper
      have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      have hdimX : topologicalKrullDim X ≤ 2 :=
        (topologicalKrullDim_eq_of_isModification_spec A f hf).trans hdim |>.le
      have hx : IsClosed ({ι w} : Set X) := isClosed_singleton_of_mem_singularLocus X hdimX _ hxs
      have hmatch' := singularLociMatch_blowUp ι j hιj hXs hZs w hx hc e
      have : IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{ι w}, hx⟩ : Closeds X))) := isNormal_of_singularLociMatch hmatch'
      exact ⟨_, _, hchainX.step (ι w) hx hxs inferInstance, hmatch'⟩
    · -- a regular centre is left out
      have : IsRegularLocalRing (Z.presheaf.stalk c) := not_not.mp hsing
      refine ⟨X, f, hchainX, singularLociMatch_blowUp_of_notMem_singularLocus ι j hιj hXs hZs c Mc
        (Scheme.IdealSheafData.coe_support_vanishingIdeal _) hsing (fun q hq hqs => hqs ?_) e⟩
      exact isRegularLocalRing_stalk_blowUp_of_blowUpToBase_eq c hc hdimc q hq

end AlgebraicGeometry

end
