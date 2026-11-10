module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.TerminationOrder
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.SingularPointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularPointBlowupChainResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ResolutionStages
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Blowing up a singular point of a stage of the resolution of a rational double point

A stage of the sequence of blowups of [Stacks, Tag 0BGE] is a normal surface whose singular
points are finitely many, each a rational double point (the local ring is the ring of a
Situation [Stacks, Tag 0BGC]). This file shows that blowing up one of the singular points gives
again such a stage, and describes its singular points: those of the old stage other than the
centre, with the same local rings, together with points over the centre whose local rings are
local rings at singular points of the blowup of the spectrum of the local ring at the centre in
its maximal ideal.

Measuring a stage by the multiset of the completion classes of its singular points, the blowup
replaces the class of the centre by finitely many classes which are smaller for
`AlgebraicGeometry.blowUpSingularRel`. With the well-foundedness of that relation this is the
input of `AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_wellFounded`.

## Main definitions

* `AlgebraicGeometry.IsRationalDoublePointStage`: the conditions on a stage.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le`: the dimension of a
  scheme is bounded by a bound on the dimensions of its local rings.
* `AlgebraicGeometry.IsRationalDoublePointStage.blowUp_of_mem_singularLocus`: the blowup of a
  stage in a singular point is a stage, and the measure decreases.
* `AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_forall_acc`: a stage has a
  finite sequence of blowups in singular closed points ending in a regular scheme, provided the
  completion classes of all Situations 0BGC are accessible.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The dimension of a scheme is the supremum of the dimensions of its local rings**, so it is
bounded by any bound on them. -/
@[ega "IV 5.1.4" "partial"]
theorem topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le (X : Scheme.{u})
    (n : WithBot ℕ∞) (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  exact iSup_le fun x => (ringKrullDim_stalk_eq_coheight x) ▸ h x

/-- Being a normal domain transports along a ring isomorphism. -/
private theorem isDomain_and_isIntegrallyClosed_of_ringEquiv {R R' : Type*} [CommRing R]
    [CommRing R'] (e : R ≃+* R') [IsDomain R] [IsIntegrallyClosed R] :
    ∃ _ : IsDomain R', IsIntegrallyClosed R' :=
  ⟨e.symm.injective.isDomain e.symm.toRingHom, IsIntegrallyClosed.of_equiv e⟩

/-- **The conditions on a stage of the resolution of a rational double point**: a locally
Noetherian normal scheme of dimension at most two with finitely many singular points, the local
ring at each of which is the ring of a Situation [Stacks, Tag 0BGC]. -/
def IsRationalDoublePointStage (W : Scheme.{u}) : Prop :=
  IsLocallyNoetherian W ∧ IsNormal W ∧ topologicalKrullDim W ≤ 2 ∧ (singularLocus W).Finite ∧
    ∀ w ∈ singularLocus W, ∃ S : RationalDoublePointSituation.{u},
      Nonempty (S.A ≃+* W.presheaf.stalk w)

/-- The measure of a stage: the multiset of the completion classes of its singular points. -/
def stageMeasure (W : Scheme.{u}) : Multiset (Quotient (isIsomorphicSetoid CommRingCat.{u})) := by
  classical
  exact if h : (singularLocus W).Finite then
    h.toFinset.val.map fun w => completionClass (W.presheaf.stalk w) else 0

namespace RationalDoublePointSituation

/-- **The blowup of a Situation 0BGC has finitely many singular points.** They correspond to
singular points of the blowup of the completion ([Stacks, Tag 0BG5]), which is of finite type
over a complete local ring and therefore has an open regular locus ([Stacks, Tag 07R5]). -/
theorem finite_singularLocus_blowUp (S : RationalDoublePointSituation.{u}) :
    (singularLocus (blowUp (maximalIdealSheaf S.A))).Finite := by
  obtain ⟨k, hsq⟩ := exists_isPullback_blowUp_adicCompletion S.A
  have := S.isLocallyNoetherian_blowUp
  have : IsLocallyNoetherian (blowUp (maximalIdealSheaf
      (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))) :=
    S.completion.isLocallyNoetherian_blowUp
  have := S.completion.isLocallyNoetherian_blowUp
  have := S.completion.isNormal_blowUp
  have : IsNoetherian (blowUp (maximalIdealSheaf S.completion.A)) := by
    have : CompactSpace (blowUp (maximalIdealSheaf S.completion.A)) :=
      QuasiCompact.compactSpace_of_compactSpace (blowUpToBase (maximalIdealSheaf S.completion.A))
    exact ⟨⟩
  have hfin : (singularLocus (blowUp (maximalIdealSheaf S.completion.A))).Finite := by
    refine finite_singularLocus_of_locallyOfFiniteType_over_completeLocalRing S.completion.A
      (blowUpToBase (maximalIdealSheaf S.completion.A)) ?_
    rw [topologicalKrullDim_eq_of_isModification_spec S.completion.A _
      S.completion.isModification_blowUpToBase, S.completion.dimension_two]
  refine (hfin.image k).subset fun z hz => ?_
  obtain ⟨y, hy1, hy2⟩ := Scheme.exists_preimage_of_isPullback hsq
    (IsLocalRing.closedPoint (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)) z
    (by rw [S.blowUpToBase_eq_closedPoint_of_mem_singularLocus z hz]
        exact specMapAdicCompletion_closedPoint S.A)
  obtain ⟨e, -⟩ := exists_adicCompletion_ringEquiv_stalkMap_of_isPullback S.A
    (IsLocalRing.maximalIdeal S.A).fg_of_isNoetherianRing (blowUpToBase (maximalIdealSheaf S.A)) k
    (blowUpToBase (maximalIdealSheaf (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A)))
    hsq.flip y z hy2
    (by rw [S.blowUpToBase_eq_closedPoint_of_mem_singularLocus z hz]; rfl)
  refine ⟨y, fun hreg => hz ?_, hy2⟩
  exact (isRegularLocalRing_iff_of_completionClass_eq
    (completionClass_eq_of_adicCompletion_ringEquiv e)).mpr hreg

end RationalDoublePointSituation

/-! ### The blowup of a stage in a singular point -/

section BlowUp

variable {W : Scheme.{u}} (w : W) (hw : IsClosed ({w} : Set W))

include hw in
/-- Off the centre the blowup morphism is an isomorphism on local rings. -/
theorem isIso_stalkMap_blowUpToBase_of_ne
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))
    (hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q ≠ w) :
    IsIso ((blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).stalkMap q) :=
  isIso_stalkMap_of_isIso_morphismRestrict _
    (isIso_blowUpToBase_restrict_compl_support _) (by
      change (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) q ∉
        ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).support : Set W)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hq)

include hw in
/-- Off the centre the blowup morphism is injective. -/
theorem blowUpToBase_injOn_of_ne :
    Set.InjOn (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))
      {q | blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q ≠ w} := by
  intro q₁ hq₁ q₂ _ h
  refine blowUpToBase_injective_of_notMem_support _ ?_ h
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hq₁

include hw in
/-- Off the centre the blowup morphism is surjective. -/
theorem exists_blowUpToBase_eq_of_ne (x : W) (hx : x ≠ w) :
    ∃ q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)),
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q = x := by
  refine exists_blowUpToBase_eq_of_notMem_support _ ?_
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hx

/-- **Points of the blowup of a stage over a rational double point**: every point over the centre
has the local ring of a point of the blowup of the spectrum of the ring of the situation, and
every singular point of that blowup comes from a point over the centre. -/
theorem exists_isPullback_blowUp_stage (S : RationalDoublePointSituation.{u})
    (e : S.A ≃+* W.presheaf.stalk w) :
    ∃ h : blowUp (maximalIdealSheaf S.A) ⟶
        blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)),
      Function.Injective h ∧
      (∀ z, IsIso (h.stalkMap z)) ∧
      (∀ q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)),
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q = w →
          ∃ z, h z = q) := by
  obtain ⟨h, hsq, _, _⟩ := exists_isPullback_blowUp_maximalIdealSheaf S.A w hw e
  refine ⟨h, h.isEmbedding.injective, fun z => isIso_stalkMap_of_flat_isPreimmersion h z,
    fun q hq => ?_⟩
  obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback hsq (closedPoint S.A) q
    (by rw [hq]; exact specToOfRingEquivStalk_closedPoint S.A w e)
  exact ⟨z, hz⟩

/-- **Local rings of the blowup of a scheme in a rational double point**: off the centre they are
those of the scheme, and over the centre those of the blowup of the spectrum of the ring of the
situation. -/
theorem exists_stalk_cases_blowUp (S : RationalDoublePointSituation.{u})
    (e : S.A ≃+* W.presheaf.stalk w) :
    ∃ h : blowUp (maximalIdealSheaf S.A) ⟶
        blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)),
      ∀ q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)),
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q ≠ w ∧
          Nonempty ((blowUp
              (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).presheaf.stalk q ≃+*
            W.presheaf.stalk
              (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q))) ∨
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q = w ∧
          ∃ z, h z = q ∧
          Nonempty ((blowUp
              (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).presheaf.stalk q ≃+*
            (blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
  obtain ⟨h, -, hiso, hsurj⟩ := exists_isPullback_blowUp_stage w hw S e
  refine ⟨h, fun q => ?_⟩
  by_cases hq : blowUpToBase I q = w
  · obtain ⟨z, rfl⟩ := hsurj q hq
    have := hiso z
    exact Or.inr ⟨hq, z, rfl, ⟨(asIso (h.stalkMap z)).commRingCatIsoToRingEquiv⟩⟩
  · have := isIso_stalkMap_blowUpToBase_of_ne w hw q hq
    exact Or.inl ⟨hq, ⟨(asIso ((blowUpToBase I).stalkMap q)).commRingCatIsoToRingEquiv.symm⟩⟩

end BlowUp

/-- Singularity of a point only depends on its local ring up to isomorphism. -/
private theorem mem_singularLocus_iff_of_ringEquiv {X Y : Scheme.{u}} {x : X} {y : Y}
    (e : X.presheaf.stalk x ≃+* Y.presheaf.stalk y) : x ∈ singularLocus X ↔ y ∈ singularLocus Y :=
  not_congr
    ⟨fun (_ : IsRegularLocalRing _) => IsRegularLocalRing.of_ringEquiv e,
      fun (_ : IsRegularLocalRing _) => IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- The measure of a scheme with finitely many singular points, one of which is `w`, splits off
the class of `w`. -/
theorem stageMeasure_eq_add_of_mem_singularLocus {W : Scheme.{u}} (hfin : (singularLocus W).Finite)
    {w : W} (hsing : w ∈ singularLocus W) :
    stageMeasure W = (hfin.sdiff (t := {w})).toFinset.val.map
        (fun x => completionClass (W.presheaf.stalk x)) +
      {completionClass (W.presheaf.stalk w)} := by
  classical
  rw [stageMeasure, dite_eq_left hfin]
  have hins : hfin.toFinset = insert w (hfin.sdiff (t := {w})).toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, Set.mem_sdiff,
      Set.mem_singleton_iff]
    by_cases hxw : x = w <;> simp [hxw, hsing]
  rw [hins, Finset.insert_val_of_notMem (by simp), Multiset.map_cons, ← Multiset.singleton_add,
    add_comm]

section StalkCases

variable {Y W Z : Scheme.{u}} {f : Y ⟶ W} {h : Z ⟶ Y} {w : W}

/-- The singular points of `Y` are those off the fibre over `w` together with those on it. -/
theorem singularLocus_eq_union_sep (f : Y ⟶ W) (w : W) :
    singularLocus Y =
      {q | q ∈ singularLocus Y ∧ f q ≠ w} ∪ {q | q ∈ singularLocus Y ∧ f q = w} := by
  ext q
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  tauto

variable (hstalk : ∀ q : Y,
  (f q ≠ w ∧ Nonempty (Y.presheaf.stalk q ≃+* W.presheaf.stalk (f q))) ∨
    (f q = w ∧ ∃ z, h z = q ∧ Nonempty (Y.presheaf.stalk q ≃+* Z.presheaf.stalk z)))
include hstalk

/-- A scheme whose local rings are local rings of two normal schemes is normal. -/
theorem isNormal_of_stalk_cases (hW : IsNormal W) (hZ : IsNormal Z) : IsNormal Y := by
  rw [isNormal_iff_stalk_normal]
  intro q
  rcases hstalk q with ⟨-, ⟨ε⟩⟩ | ⟨-, z, -, ⟨ε⟩⟩
  · have := hW.stalk_normal (f q)
    exact isDomain_and_isIntegrallyClosed_of_ringEquiv ε.symm
  · have := hZ.stalk_normal z
    exact isDomain_and_isIntegrallyClosed_of_ringEquiv ε.symm

/-- A scheme whose local rings are local rings of two schemes of dimension at most `n` has
dimension at most `n`. -/
theorem topologicalKrullDim_le_of_stalk_cases {n : WithBot ℕ∞} (hW : topologicalKrullDim W ≤ n)
    (hZ : topologicalKrullDim Z ≤ n) : topologicalKrullDim Y ≤ n := by
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ n fun q => ?_
  rcases hstalk q with ⟨-, ⟨ε⟩⟩ | ⟨-, z, -, ⟨ε⟩⟩
  · rw [ringKrullDim_eq_of_ringEquiv ε]
    exact (Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim
      W _).trans hW
  · rw [ringKrullDim_eq_of_ringEquiv ε]
    exact (Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim
      _ z).trans hZ

/-- If `f` is bijective off the fibre over `w`, it is a bijection between the singular points of
`Y` off that fibre and the singular points of `W` other than `w`. -/
theorem bijOn_singularLocus_of_stalk_cases (hinj : Set.InjOn f {q | f q ≠ w})
    (hsurj : ∀ x, x ≠ w → ∃ q, f q = x) :
    Set.BijOn f {q | q ∈ singularLocus Y ∧ f q ≠ w} (singularLocus W \ {w}) := by
  refine ⟨fun q hq => ?_, hinj.mono fun q hq => hq.2, fun x hx => ?_⟩
  · rcases hstalk q with ⟨-, ⟨ε⟩⟩ | ⟨hqw, -⟩
    · exact ⟨(mem_singularLocus_iff_of_ringEquiv ε).mp hq.1, hq.2⟩
    · exact absurd hqw hq.2
  · obtain ⟨q, rfl⟩ := hsurj x hx.2
    refine ⟨q, ⟨?_, hx.2⟩, rfl⟩
    rcases hstalk q with ⟨-, ⟨ε⟩⟩ | ⟨hqw, -⟩
    · exact (mem_singularLocus_iff_of_ringEquiv ε).mpr hx.1
    · exact absurd hqw hx.2

/-- The singular points of `Y` over `w` come from singular points of `Z`. -/
theorem subset_image_singularLocus_of_stalk_cases :
    {q | q ∈ singularLocus Y ∧ f q = w} ⊆ h '' singularLocus Z := by
  intro q hq
  rcases hstalk q with ⟨hqw, -⟩ | ⟨-, z, rfl, ⟨ε⟩⟩
  · exact absurd hq.2 hqw
  · exact ⟨z, (mem_singularLocus_iff_of_ringEquiv ε).mp hq.1, rfl⟩

/-- If every singular point of `W` and of `Z` has the local ring of a Situation 0BGC, so does
every singular point of `Y`. -/
theorem forall_exists_situation_of_stalk_cases
    (hW : ∀ x ∈ singularLocus W, ∃ S : RationalDoublePointSituation.{u},
      Nonempty (S.A ≃+* W.presheaf.stalk x))
    (hZ : ∀ z ∈ singularLocus Z, ∃ S : RationalDoublePointSituation.{u},
      Nonempty (S.A ≃+* Z.presheaf.stalk z)) :
    ∀ q ∈ singularLocus Y, ∃ S : RationalDoublePointSituation.{u},
      Nonempty (S.A ≃+* Y.presheaf.stalk q) := by
  intro q hq
  rcases hstalk q with ⟨-, ⟨ε⟩⟩ | ⟨-, z, rfl, ⟨ε⟩⟩
  · obtain ⟨S, ⟨ε'⟩⟩ := hW _ ((mem_singularLocus_iff_of_ringEquiv ε).mp hq)
    exact ⟨S, ⟨ε'.trans ε.symm⟩⟩
  · obtain ⟨S, ⟨ε'⟩⟩ := hZ z ((mem_singularLocus_iff_of_ringEquiv ε).mp hq)
    exact ⟨S, ⟨ε'.trans ε.symm⟩⟩

/-- The measure of `Y` is that of the singular points of `W` other than `w`, plus the classes of
the singular points of `Y` over `w`. -/
theorem stageMeasure_eq_add_of_stalk_cases (hfin : (singularLocus W).Finite)
    (hAimage : Set.BijOn f {q | q ∈ singularLocus Y ∧ f q ≠ w} (singularLocus W \ {w}))
    (hBfin : {q | q ∈ singularLocus Y ∧ f q = w}.Finite) :
    stageMeasure Y = (hfin.sdiff (t := {w})).toFinset.val.map
        (fun x => completionClass (W.presheaf.stalk x)) +
      hBfin.toFinset.val.map fun q => completionClass (Y.presheaf.stalk q) := by
  classical
  have hAfin : {q | q ∈ singularLocus Y ∧ f q ≠ w}.Finite :=
    Set.Finite.of_finite_image (hAimage.image_eq ▸ hfin.sdiff) hAimage.injOn
  have hsingB := singularLocus_eq_union_sep f w
  have hfinB : (singularLocus Y).Finite := hsingB ▸ hAfin.union hBfin
  rw [stageMeasure, dite_eq_left hfinB]
  have hunion : hfinB.toFinset = hAfin.toFinset.disjUnion hBfin.toFinset (by
      rw [Finset.disjoint_left]
      intro q hqA hqB
      simp only [Set.Finite.mem_toFinset] at hqA hqB
      exact hqA.2 hqB.2) := by
    ext q
    simp only [Finset.mem_disjUnion, Set.Finite.mem_toFinset]
    exact Set.ext_iff.mp hsingB q
  rw [hunion, Finset.disjUnion_val, Multiset.map_add]
  congr 1
  have himg : (hfin.sdiff (t := {w})).toFinset = hAfin.toFinset.image f := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_image]
    exact ⟨fun hx => hAimage.surjOn hx, by rintro ⟨q, hq, rfl⟩; exact hAimage.mapsTo hq⟩
  rw [himg, Finset.image_val_of_injOn (fun q₁ hq₁ q₂ hq₂ h12 => hAimage.injOn
    (by simpa using hq₁) (by simpa using hq₂) h12), Multiset.map_map]
  refine Multiset.map_congr rfl fun q hq => ?_
  simp only [Function.comp_apply]
  rcases hstalk q with ⟨-, ⟨ε⟩⟩ | ⟨hqw, -⟩
  · exact completionClass_eq_of_ringEquiv ε
  · simp only [Finset.mem_val, Set.Finite.mem_toFinset] at hq
    exact absurd hqw hq.2

end StalkCases

namespace IsRationalDoublePointStage

/-- A singular point of a stage is closed. -/
theorem isClosed_of_mem_singularLocus {W : Scheme.{u}} (hW : IsRationalDoublePointStage W)
    (w : W) (hsing : w ∈ singularLocus W) : IsClosed ({w} : Set W) := by
  obtain ⟨hloc, hnorm, hdim, -, -⟩ := hW
  exact isClosed_singleton_of_mem_singularLocus W hdim w hsing

/-- **The blowup of a stage in a singular point is a stage, and the measure decreases.** The
points off the centre keep their local rings (Tag 02OS); the points over the centre have the
local rings of the blowup of the spectrum of the local ring at the centre, which is normal of
dimension two with finitely many singular points, each a Situation 0BGC; and the classes of the
new singular points over the centre are `AlgebraicGeometry.blowUpSingularRel`-smaller than the
class of the centre. -/
theorem blowUp_of_mem_singularLocus {W : Scheme.{u}} (hW : IsRationalDoublePointStage W) (w : W)
    (hw : IsClosed ({w} : Set W)) (hsing : w ∈ singularLocus W) :
    IsRationalDoublePointStage
        (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) ∧
      Relation.CutExpand blowUpSingularRel
        (stageMeasure (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))))
        (stageMeasure W) := by
  classical
  obtain ⟨hloc, hnorm, hdim, hfin, hrdp⟩ := hW
  obtain ⟨S, ⟨e⟩⟩ := hrdp w hsing
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
  obtain ⟨h, hstalk⟩ := exists_stalk_cases_blowUp w hw S e
  have := S.isLocallyNoetherian_blowUp
  have := S.isNormal_blowUp
  have hdimS : topologicalKrullDim (blowUp (maximalIdealSheaf S.A)) ≤ 2 := by
    rw [topologicalKrullDim_eq_of_isModification_spec S.A _ S.isModification_blowUpToBase,
      S.dimension_two]
  have : IsLocallyNoetherian (blowUp I) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I)
  let A : Set (blowUp I) := {q | q ∈ singularLocus (blowUp I) ∧ blowUpToBase I q ≠ w}
  let B : Set (blowUp I) := {q | q ∈ singularLocus (blowUp I) ∧ blowUpToBase I q = w}
  have hAimage : Set.BijOn (blowUpToBase I) A (singularLocus W \ {w}) :=
    bijOn_singularLocus_of_stalk_cases hstalk (blowUpToBase_injOn_of_ne w hw)
      (exists_blowUpToBase_eq_of_ne w hw)
  have hAfin : A.Finite := .of_finite_image (hAimage.image_eq ▸ hfin.sdiff) hAimage.injOn
  have hBfin : B.Finite := (S.finite_singularLocus_blowUp.image h).subset
    (subset_image_singularLocus_of_stalk_cases hstalk)
  have hfinB : (singularLocus (blowUp I)).Finite :=
    singularLocus_eq_union_sep (blowUpToBase I) w ▸ hAfin.union hBfin
  refine ⟨⟨inferInstance, isNormal_of_stalk_cases hstalk hnorm S.isNormal_blowUp,
    topologicalKrullDim_le_of_stalk_cases hstalk hdim hdimS, hfinB,
    forall_exists_situation_of_stalk_cases hstalk hrdp
      S.exists_situation_of_mem_singularLocus_blowUp⟩, ?_⟩
  let cls : ∀ {X : Scheme.{u}}, X → Quotient (isIsomorphicSetoid CommRingCat.{u}) :=
    fun {X} x => completionClass (X.presheaf.stalk x)
  have hmW : stageMeasure W = (hfin.sdiff (t := {w})).toFinset.val.map cls + {cls w} :=
    stageMeasure_eq_add_of_mem_singularLocus hfin hsing
  have hmB : stageMeasure (blowUp I) =
      (hfin.sdiff (t := {w})).toFinset.val.map cls + hBfin.toFinset.val.map cls :=
    stageMeasure_eq_add_of_stalk_cases hstalk hfin hAimage hBfin
  refine ⟨hBfin.toFinset.val.map cls, cls w, fun a' ha' => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp ha'
    simp only [Finset.mem_val, Set.Finite.mem_toFinset] at hq
    rcases hstalk q with ⟨hqw, -⟩ | ⟨-, z, rfl, ⟨ε⟩⟩
    · exact absurd hq.2 hqw
    · exact ⟨S, z, completionClass_eq_of_ringEquiv e,
        (mem_singularLocus_iff_of_ringEquiv ε).mp hq.1,
        (completionClass_eq_of_ringEquiv ε).symm⟩
  · rw [hmB, hmW]
    abel

end IsRationalDoublePointStage

/-- **Resolution of a stage, given the termination of the measure.** If the completion classes of
all Situations [Stacks, Tag 0BGC] are accessible for `AlgebraicGeometry.blowUpSingularRel`, every
stage has a finite sequence of blowups in singular closed points, all of whose members are
stages, ending in a regular scheme. -/
theorem exists_singularPointBlowupChain_isRegular_of_forall_acc
    (hacc : ∀ S : RationalDoublePointSituation.{u}, Acc blowUpSingularRel (completionClass S.A))
    (X : Scheme.{u}) (hX : IsRationalDoublePointStage X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      SingularPointBlowupChain IsRationalDoublePointStage X Y f ∧ IsRegular Y := by
  have hwf : WellFounded (@blowUpSingularRel.{u}) := by
    refine ⟨fun a => Acc.intro _ fun a' ha' => ?_⟩
    obtain ⟨S, q, -, hq, rfl⟩ := ha'
    obtain ⟨S', ⟨ε⟩⟩ := S.exists_situation_of_mem_singularLocus_blowUp q hq
    rw [← completionClass_eq_of_ringEquiv ε]
    exact hacc S'
  refine exists_singularPointBlowupChain_isRegular_of_wellFounded hwf _ stageMeasure ?_ ?_ X hX
  · intro W hW hM
    obtain ⟨hloc, -, -, hfin, -⟩ := hW
    refine isRegular_of_singularLocus_eq_empty W ?_
    rwa [stageMeasure, dite_eq_left hfin, Multiset.map_eq_zero, Finset.val_eq_zero,
      Set.Finite.toFinset_eq_empty] at hM
  · intro W hW hM
    obtain ⟨w, hwsing⟩ : (singularLocus W).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun hempty => hM (by
        rw [stageMeasure, dite_eq_left hW.2.2.2.1]
        simp [hempty])
    exact ⟨w, _, hwsing, hW.blowUp_of_mem_singularLocus w
      (hW.isClosed_of_mem_singularLocus w hwsing) hwsing⟩

end AlgebraicGeometry

end
