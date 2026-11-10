module

public import StacksFrontier.AlgebraicGeometry.Flatness.SectionLocusTopology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedGenericFibre
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Noetherian.LocallyConnected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Connected components meeting a section, over a discrete valuation ring

Let `f : X ⟶ Y` be a morphism of schemes with a section `s`, and let `X⁰ ⊆ X` be the union of
the connected components of the fibres of `f` containing the corresponding value of `s`
(Stacks 055L). Stacks 055R asserts that `X⁰` is open when `f` is flat of finite presentation
with geometrically reduced fibres, and Stacks 055Q is the local form of that statement.

This file proves both over a **discrete valuation ring base**, which is the case carrying the
mathematical content: the two reductions in the source — the limit approximation that replaces
the base by the spectrum of a finite type `ℤ`-algebra, and the topological reduction that
produces a discrete valuation ring out of a specialization — are not formalized here. See the
implementation notes.

Over a discrete valuation ring the proof is the one in the source, and its one non-formal input
is `AlgebraicGeometry.connectedSpace_fiber_bot_of_isReduced_fiber_closedPoint` (Stacks 055J): a
flat, connected scheme over a discrete valuation ring with reduced closed fibre has connected
generic fibre. Only reducedness of the *closed* fibre is used, so the hypothesis here is weaker
than the "all fibres geometrically reduced" of the source.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.locus_eq_of_two_point_base` is the topological core:
  over a base with exactly two points it identifies `X⁰` with a single connected component.
* `AlgebraicGeometry.locus_eq_connectedComponentIn_of_isDiscreteValuationRing` identifies `X⁰`
  with the connected component, through the section, of the complement of the discarded part of
  the closed fibre.
* `AlgebraicGeometry.isOpen_locus_of_isDiscreteValuationRing` is Stacks 055R over a discrete
  valuation ring.
* `AlgebraicGeometry.locus_mem_nhds_of_isDiscreteValuationRing` is Stacks 055Q over a discrete
  valuation ring: `X⁰` is a neighbourhood of every point of the component of the closed fibre
  through the section.
* `AlgebraicGeometry.stableUnderGeneralization_locus_of_isDiscreteValuationRing` is the
  consequence the source's reduction of Stacks 055Q to this case actually consumes.

## Implementation notes

The spectrum of a discrete valuation ring has exactly two points, the generic point `⊥` and the
closed point. `AlgebraicGeometry.primeSpectrum_eq_bot_or_closedPoint` records this, and
`AlgebraicGeometry.ConnectedAlongSection.locus_eq_of_two_point_base` is the purely topological
statement that this is all the proof uses about the base: given a continuous `p` with a section
and a base with two points `e` and `m`, and given an auxiliary open `U` which meets the fibre
over `m` exactly in the chosen component and which contains the fibre over `e`, the locus is the
connected component of `U` through the section — provided the generic part `W ∩ p ⁻¹' {e}` is
connected, which is exactly what Stacks 055J supplies.

The auxiliary open is `U = (X_m \ X⁰_m)ᶜ`, which is open because `X⁰_m` is open in the fibre
`X_m`: the fibre is a locally Noetherian scheme, hence a locally connected space. The source
phrases this step as "replace `X` by `X \ (X_s \ X⁰_s)`"; here `U` and the component
`W = connectedComponentIn U (s m)` stay subsets of `X`, and the only place an actual open
subscheme is formed is in the application of Stacks 055J to `W`.

**What is not proved here.** Stacks 055Q and 055R in general need two further reductions, which
are the bulk of the source's proof and are absent from this file:

* the limit approximation (Stacks 01ZM, 04AI, 0384) descending `f` and `s` to a morphism of
  finite presentation over a finite type `ℤ`-algebra, which reduces to a Noetherian base; and
* the topological reduction, using Stacks 0540 in a Noetherian space together with the discrete
  valuation ring produced by Stacks 054F from a specialization, which reduces a Noetherian base
  to the discrete valuation ring case proved here.

Both of those inputs are already in the library; what is missing is the two reduction arguments.

## References

* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- If the connected components of a closed subspace `F` are open in `F`, then removing one of
them from `F` leaves a closed set. -/
theorem isClosed_sdiff_connectedComponentIn {α : Type*} [TopologicalSpace α] {F : Set α}
    (hF : IsClosed F) [LocallyConnectedSpace ↥F] {x : α} (hx : x ∈ F) :
    IsClosed (F \ connectedComponentIn F x) := by
  have h1 : F \ connectedComponentIn F x =
      Subtype.val '' (connectedComponent (⟨x, hx⟩ : ↥F))ᶜ := by
    rw [connectedComponentIn_eq_image hx]
    ext z
    constructor
    · rintro ⟨hzF, hz⟩
      exact ⟨⟨z, hzF⟩, fun hc => hz ⟨⟨z, hzF⟩, hc, rfl⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      rintro ⟨v, hv, hvw⟩
      exact hw (by rwa [Subtype.ext hvw] at hv)
  rw [h1]
  exact hF.isClosedEmbedding_subtypeVal.isClosedMap _
    isOpen_connectedComponent.isClosed_compl

namespace AlgebraicGeometry

/-- Every fibre of a morphism locally of finite type is a locally connected space: it is a
locally Noetherian scheme. -/
theorem locallyConnectedSpace_preimage_singleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (y : Y) :
    LocallyConnectedSpace ↥(f ⁻¹' {y} : Set X) := by
  have h1 : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) inferInstance
  have h2 : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  have h3 : LocallyConnectedSpace (f.fiber y) :=
    (isLocallyNoetherianSpace_of_isLocallyNoetherian (f.fiber y)).locallyConnectedSpace _
  exact Homeomorph.locallyConnectedSpace (f.fiberHomeo y).symm

namespace ConnectedAlongSection

/-- **The topological core of Stacks 055Q and 055R over a two-point base.** Let `p` be a map
with a section `sc`, let the target have exactly the two points `e` and `m`, let `U` be a subset
which meets the fibre over `m` exactly in the connected component of `sc m` and which contains
the fibre over `e`, and let `W` be the connected component of `U` through `sc m`. If `sc e` lies
in `W` and the part of `W` over `e` is connected, then the locus of connected components of
fibres meeting the section is exactly `W`. -/
theorem locus_eq_of_two_point_base {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (p : α → β) (sc : β → α) (hsc : ∀ b, p (sc b) = b)
    (e m : β) (hβ : ∀ b, b = e ∨ b = m) (U W : Set α)
    (hUm : U ∩ p ⁻¹' {m} = connectedComponentIn (p ⁻¹' {m}) (sc m))
    (hUe : p ⁻¹' {e} ⊆ U)
    (hWdef : W = connectedComponentIn U (sc m))
    (hscW : sc e ∈ W)
    (hgen : _root_.IsConnected (W ∩ p ⁻¹' {e})) :
    (⋃ b, connectedComponentIn (p ⁻¹' {b}) (sc b)) = W := by
  have hWU : W ⊆ U := by rw [hWdef]; exact connectedComponentIn_subset _ _
  have hWm : W ∩ p ⁻¹' {m} = connectedComponentIn (p ⁻¹' {m}) (sc m) := by
    refine subset_antisymm ?_ ?_
    · rw [← hUm]; exact Set.inter_subset_inter_left _ hWU
    · refine Set.subset_inter ?_ (connectedComponentIn_subset _ _)
      rw [hWdef]
      refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (by simp [hsc m])) ?_
      rw [← hUm]; exact Set.inter_subset_left
  have hWe : W ∩ p ⁻¹' {e} = connectedComponentIn (p ⁻¹' {e}) (sc e) := by
    refine subset_antisymm ?_ ?_
    · exact hgen.2.subset_connectedComponentIn ⟨hscW, by simp [hsc e]⟩ Set.inter_subset_right
    · refine Set.subset_inter ?_ (connectedComponentIn_subset _ _)
      have hshift : connectedComponentIn U (sc m) = connectedComponentIn U (sc e) :=
        connectedComponentIn_eq (hWdef ▸ hscW)
      rw [hWdef, hshift]
      refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (by simp [hsc e])) ?_
      exact (connectedComponentIn_subset _ _).trans hUe
  have hcover : W = W ∩ p ⁻¹' {m} ∪ W ∩ p ⁻¹' {e} := by
    rw [← Set.inter_union_distrib_left]
    refine (Set.inter_eq_left.mpr ?_).symm
    exact fun x _ => (hβ (p x)).symm
  refine subset_antisymm (Set.iUnion_subset fun b => ?_) ?_
  · rcases hβ b with rfl | rfl
    · rw [← hWe]; exact Set.inter_subset_left
    · rw [← hWm]; exact Set.inter_subset_left
  · rw [hcover, hWm, hWe]
    exact Set.union_subset
      (Set.subset_iUnion (fun b => connectedComponentIn (p ⁻¹' {b}) (sc b)) m)
      (Set.subset_iUnion (fun b => connectedComponentIn (p ⁻¹' {b}) (sc b)) e)

end ConnectedAlongSection

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In a discrete valuation ring the zero ideal is not the maximal ideal. -/
theorem genericPoint_ne_closedPoint :
    (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ≠ IsLocalRing.closedPoint R := fun h =>
  IsDiscreteValuationRing.not_isField R (IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    (congrArg PrimeSpectrum.asIdeal h).symm)

/-- The spectrum of a discrete valuation ring has exactly two points, the generic point and the
closed point. -/
@[ega "0 14.1.12" "partial", ega "IV 5.2.5" "partial"]
theorem primeSpectrum_eq_bot_or_closedPoint (q : PrimeSpectrum R) :
    q = (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∨ q = IsLocalRing.closedPoint R := by
  by_cases h : q.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext h)
  · exact Or.inr (PrimeSpectrum.ext
      (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime h q.isPrime)))

/-- The closed point of the spectrum of a local ring is a closed point. -/
theorem isClosed_singleton_closedPoint :
    IsClosed ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)

/-- Stacks 055J, read as a statement about subsets of the source: the part over the generic
point of an open connected subset of a flat scheme over a discrete valuation ring with reduced
closed fibre is connected. -/
theorem isConnected_inter_preimage_bot_of_isConnected {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Flat f] [IsReduced (f.fiber (IsLocalRing.closedPoint R))]
    (W : Set X) (hWopen : IsOpen W) (hWconn : _root_.IsConnected W) :
    _root_.IsConnected (W ∩ f ⁻¹' {(⟨⊥, inferInstance⟩ : PrimeSpectrum R)}) := by
  let Wo : X.Opens := ⟨W, hWopen⟩
  have hWrange : Set.range ⇑Wo.ι = W := Wo.range_ι
  have hconn : ConnectedSpace ↥Wo.toScheme := isConnected_iff_connectedSpace.mp hWconn
  have hred : IsReduced ((Wo.ι ≫ f).fiber (IsLocalRing.closedPoint R)) :=
    isReduced_fiber_opens_ι_comp Wo f _
  have hgen := connectedSpace_fiber_bot_of_isReduced_fiber_closedPoint (Wo.ι ≫ f)
  have hc := isConnected_range
    (f := ⇑((Wo.ι ≫ f).fiberι (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ≫ Wo.ι))
    (Scheme.Hom.continuous _)
  have h1 : Set.range ⇑((Wo.ι ≫ f).fiberι (⟨⊥, inferInstance⟩ : PrimeSpectrum R))
      = (Wo.ι ≫ f) ⁻¹' {(⟨⊥, inferInstance⟩ : PrimeSpectrum R)} :=
    Scheme.Hom.range_fiberι _ _
  have heq : Set.range ⇑((Wo.ι ≫ f).fiberι (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ≫ Wo.ι)
      = W ∩ f ⁻¹' {(⟨⊥, inferInstance⟩ : PrimeSpectrum R)} := by
    ext x
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_preimage, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨hWrange ▸ Set.mem_range_self _, ?_⟩
      simpa [Scheme.Hom.comp_apply] using h1.subset (Set.mem_range_self z)
    · rintro ⟨hxW, hx⟩
      obtain ⟨w, hw⟩ : x ∈ Set.range ⇑Wo.ι := by rwa [hWrange]
      have hmem : w ∈ (Wo.ι ≫ f) ⁻¹' {(⟨⊥, inferInstance⟩ : PrimeSpectrum R)} := by
        change (Wo.ι ≫ f) w = _
        rw [Scheme.Hom.comp_apply, hw]
        exact hx
      rw [← h1] at hmem
      obtain ⟨z, hz⟩ := hmem
      exact ⟨z, by rw [hz, hw]⟩
  rwa [heq] at hc

/-- The component, through a point `x` of the closed fibre, of the complement of the part of the
closed fibre missed by the component of `x` is open. -/
private theorem isOpen_connectedComponentIn_compl_sdiff_closedFibre {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] {x : X}
    (hx : x ∈ (f ⁻¹' {IsLocalRing.closedPoint R} : Set X)) :
    IsOpen (connectedComponentIn ((f ⁻¹' {IsLocalRing.closedPoint R} \
      connectedComponentIn (f ⁻¹' {IsLocalRing.closedPoint R}) x)ᶜ) x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : LocallyConnectedSpace ↥X :=
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X).locallyConnectedSpace _
  have : LocallyConnectedSpace ↥(f ⁻¹' {IsLocalRing.closedPoint R} : Set X) :=
    locallyConnectedSpace_preimage_singleton f _
  exact (isClosed_sdiff_connectedComponentIn (F := (f ⁻¹' {IsLocalRing.closedPoint R} : Set X))
    ((isClosed_singleton_closedPoint (R := R)).preimage f.continuous)
    hx).isOpen_compl.connectedComponentIn

/-- **Stacks 055Q and 055R over a discrete valuation ring base.** The locus `X⁰` of connected
components of fibres meeting the section is the connected component, through the section, of the
complement of the part of the closed fibre that the section's component misses. -/
theorem locus_eq_connectedComponentIn_of_isDiscreteValuationRing
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (sec : Spec (.of R) ⟶ X)
    (hsec : sec ≫ f = 𝟙 _) [Flat f] [LocallyOfFiniteType f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    ConnectedAlongSection.locus ⟨X, Spec (.of R), f, sec, hsec⟩ =
      connectedComponentIn
        ((f ⁻¹' {IsLocalRing.closedPoint R} \
          connectedComponentIn (f ⁻¹' {IsLocalRing.closedPoint R})
            (sec (IsLocalRing.closedPoint R)))ᶜ)
        (sec (IsLocalRing.closedPoint R)) := by
  have hsm : sec (IsLocalRing.closedPoint R) ∈ (f ⁻¹' {IsLocalRing.closedPoint R} : Set X) :=
    ConnectedAlongSection.section_mem_preimage ⟨X, Spec (.of R), f, sec, hsec⟩ _
  have hscmU : sec (IsLocalRing.closedPoint R) ∈
      ((f ⁻¹' {IsLocalRing.closedPoint R} \
        connectedComponentIn (f ⁻¹' {IsLocalRing.closedPoint R})
          (sec (IsLocalRing.closedPoint R)))ᶜ : Set X) :=
    fun h => h.2 (mem_connectedComponentIn hsm)
  have hUe : (f ⁻¹' {(⟨⊥, inferInstance⟩ : PrimeSpectrum R)} : Set X) ⊆
      ((f ⁻¹' {IsLocalRing.closedPoint R} \
        connectedComponentIn (f ⁻¹' {IsLocalRing.closedPoint R})
          (sec (IsLocalRing.closedPoint R)))ᶜ : Set X) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_sdiff, not_and]
    intro hxm
    simp only [Set.mem_preimage] at hx hxm
    exact absurd (hx.symm.trans hxm) (genericPoint_ne_closedPoint (R := R))
  rw [ConnectedAlongSection.locus_eq_iUnion_connectedComponentIn]
  refine ConnectedAlongSection.locus_eq_of_two_point_base ⇑f ⇑sec
    (fun q => congrArg (fun g : Spec (.of R) ⟶ Spec (.of R) => g q) hsec)
    (⟨⊥, inferInstance⟩ : PrimeSpectrum R) (IsLocalRing.closedPoint R)
    primeSpectrum_eq_bot_or_closedPoint _ _ ?_ hUe rfl ?_
    (isConnected_inter_preimage_bot_of_isConnected f _
      (isOpen_connectedComponentIn_compl_sdiff_closedFibre f hsm)
      (isConnected_connectedComponentIn_iff.mpr hscmU))
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff, not_and, not_not]
    exact ⟨fun h => h.1 h.2, fun h => ⟨fun _ => h, connectedComponentIn_subset _ _ h⟩⟩
  · refine (isConnected_range sec.continuous).2.subset_connectedComponentIn
      (Set.mem_range_self _) ?_ (Set.mem_range_self _)
    rintro x ⟨q, rfl⟩
    rcases primeSpectrum_eq_bot_or_closedPoint q with rfl | rfl
    · exact hUe (ConnectedAlongSection.section_mem_preimage
        ⟨X, Spec (.of R), f, sec, hsec⟩ _)
    · exact hscmU

/-- **Stacks 055R over a discrete valuation ring base.** The locus `X⁰` of connected components
of fibres meeting the section is open. Only reducedness of the closed fibre is needed; the
source's hypothesis that all fibres be geometrically reduced is not used, and the two reductions
of the source that pass from a general base to this one are not proved here. -/
@[stacks 055R "the case of a discrete valuation ring base; the source's reduction to this case,
and hence the statement for a general base, is not proved here", ega "IV 15.6.5" "DVR base"]
theorem isOpen_locus_of_isDiscreteValuationRing
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (sec : Spec (.of R) ⟶ X)
    (hsec : sec ≫ f = 𝟙 _) [Flat f] [LocallyOfFiniteType f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    IsOpen (ConnectedAlongSection.locus ⟨X, Spec (.of R), f, sec, hsec⟩) := by
  rw [locus_eq_connectedComponentIn_of_isDiscreteValuationRing f sec hsec]
  exact isOpen_connectedComponentIn_compl_sdiff_closedFibre f
    (ConnectedAlongSection.section_mem_preimage ⟨X, Spec (.of R), f, sec, hsec⟩ _)

/-- Over a discrete valuation ring base the locus `X⁰` is stable under generalization: if a
point of `X⁰` is a specialization of `x`, then `x` lies in `X⁰` too. This is the form in which
the source's topological reduction of Stacks 055Q to the discrete valuation ring case consumes
this case: it is applied to the base change of `f` along a morphism `Spec R ⟶ Y` out of the
discrete valuation ring supplied by Stacks 054F for a specialization in `X`. -/
theorem stableUnderGeneralization_locus_of_isDiscreteValuationRing
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (sec : Spec (.of R) ⟶ X)
    (hsec : sec ≫ f = 𝟙 _) [Flat f] [LocallyOfFiniteType f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    StableUnderGeneralization
      (ConnectedAlongSection.locus ⟨X, Spec (.of R), f, sec, hsec⟩) :=
  (isOpen_locus_of_isDiscreteValuationRing f sec hsec).stableUnderGeneralization

/-- **Stacks 055Q over a discrete valuation ring base.** The locus `X⁰` is a neighbourhood of
every point of the connected component of the closed fibre containing the section. -/
@[stacks 055Q "the case of a discrete valuation ring base; the source's reduction to this case,
and hence the statement for a general base, is not proved here", ega "IV 15.6.5" "DVR base"]
theorem locus_mem_nhds_of_isDiscreteValuationRing
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (sec : Spec (.of R) ⟶ X)
    (hsec : sec ≫ f = 𝟙 _) [Flat f] [LocallyOfFiniteType f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))]
    {x : X} (hx : x ∈ connectedComponentIn (f ⁻¹' {IsLocalRing.closedPoint R} : Set X)
      (sec (IsLocalRing.closedPoint R))) :
    ConnectedAlongSection.locus ⟨X, Spec (.of R), f, sec, hsec⟩ ∈ nhds x := by
  refine (isOpen_locus_of_isDiscreteValuationRing f sec hsec).mem_nhds ?_
  exact ((ConnectedAlongSection.locus_inter_preimage
    ⟨X, Spec (.of R), f, sec, hsec⟩ (IsLocalRing.closedPoint R)).symm.subset hx).1

end AlgebraicGeometry

end
