module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.AffineFormalOpenBasis

/-!
# The weak affine formal open subschemes form a basis

Let `A` be a weakly admissible topological ring and `f ∈ A`. The open `D(f)` of McQuillan's formal
spectrum `Spfw A` is McQuillan's formal spectrum of the completion `A_{f}` of the localization
`A_f` along the weak ideals of definition of `A`
(`AlgebraicGeometry.SpfwBasicOpen.localizationSpectrumIso`), and `A_{f}` is again weakly
admissible. Since the opens `D(f)` form a basis of `Spfw A`, every neighbourhood of a point of a
weak affine formal open subscheme contains a weak affine formal open neighbourhood of that point.
Consequently the weak affine formal open subschemes of a formal scheme in the sense of McQuillan
form a basis of its topology: these are the opens on which Stacks 0AIV imposes its conditions.

## Main results

* `AlgebraicGeometry.SpfwBasicOpen.isWeaklyAdmissible_localizedCompletion`: the completed
  localization `A_{f}` of a weakly admissible ring is weakly admissible.
* `AlgebraicGeometry.exists_isWeakAffineFormalOpen_le_of_isWeakAffineFormalOpen`: inside a weak
  affine formal open subscheme, every neighbourhood of a point contains a weak affine formal open
  neighbourhood of it.
* `AlgebraicGeometry.exists_isWeakAffineFormalOpen_le` and
  `AlgebraicGeometry.isBasis_isWeakAffineFormalOpen`: the weak affine formal open subschemes of a
  formal scheme in the sense of McQuillan form a basis of its topology.

## References

* [EGA I, 10.1.4]
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopologicalRing
open TopologicalRing.CompletionOver

namespace AlgebraicGeometry

universe u

namespace SpfwBasicOpen

/-- The completion `A_{f}` of the localization `A_f` along the weak ideals of definition of a
weakly admissible ring `A` is weakly admissible. -/
theorem isWeaklyAdmissible_localizedCompletion (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (hA : IsWeaklyAdmissible A) (f : A) :
    IsWeaklyAdmissible (localizedCompletion A f) :=
  completionOver_isWeaklyAdmissible _ hA

end SpfwBasicOpen

open SpfwBasicOpen in
/-- **Inside a weak affine formal open subscheme the weak affine formal open subschemes form a
basis.** If `V ≅ Spfw A` is a weak affine formal open of `X` and `W` is an open neighbourhood of a
point `x ∈ V`, then some weak affine formal open `U ∋ x` lies in `V ⊓ W`: take a basic open
`D(f) ≅ Spfw A_{f}` of `Spfw A` around the point corresponding to `x` inside the preimage of `W`;
the completed localization `A_{f}` is weakly admissible. -/
theorem exists_isWeakAffineFormalOpen_le_of_isWeakAffineFormalOpen {X : LTRS.{u}} {V : Opens X}
    (hV : IsWeakAffineFormalOpen X V) {W : Opens X} {x : X} (hxV : x ∈ V) (hxW : x ∈ W) :
    ∃ U : Opens X, IsWeakAffineFormalOpen X U ∧ x ∈ U ∧ U ≤ V ⊓ W := by
  obtain ⟨A, hlin, hA, ⟨e⟩⟩ := hV
  let := hlin
  let φ : Spfw A.α ⟶ X.toPresheafedSpace :=
    e.inv ≫ X.toPresheafedSpace.ofRestrict V.isOpenEmbedding'
  let hφ : PresheafedSpace.IsOpenImmersion φ :=
    PresheafedSpace.IsOpenImmersion.comp
      (H := PresheafedSpace.IsOpenImmersion.ofIso e.symm)
      (hg := PresheafedSpace.IsOpenImmersion.ofRestrict X.toPresheafedSpace
        V.isOpenEmbedding') _ _
  let ey : V ≃ₜ spfSpace A.α := TopCat.homeoOfIso ((PresheafedSpace.forget _).mapIso e)
  let y : spfSpace A.α := ey ⟨x, hxV⟩
  have hy : φ.base y = x := by
    change (ey.symm (ey ⟨x, hxV⟩)).val = x
    simp
  obtain ⟨f, ⟨z, hz⟩, hf⟩ := exists_localization_range_le A.α hA
    ((Opens.map φ.base).obj W) y (show φ.base y ∈ W by rwa [hy])
  let g : Spfw (localizedCompletion A.α f) ⟶ X.toPresheafedSpace :=
    localizationSpectrumMap A.α hA f ≫ φ
  let hg : PresheafedSpace.IsOpenImmersion g :=
    PresheafedSpace.IsOpenImmersion.comp
      (H := localizationSpectrumMap_isOpenImmersion A.α hA f) (hg := hφ) _ _
  let U : Opens X := ⟨Set.range g.base, hg.base_open.isOpen_range⟩
  refine ⟨U, ?_, ⟨z, ?_⟩, ?_⟩
  · refine ⟨TopCommRingCat.of (localizedCompletion A.α f), inferInstance,
      isWeaklyAdmissible_localizedCompletion A.α hA f, ⟨?_⟩⟩
    let : PresheafedSpace.IsOpenImmersion
        (X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding') :=
      PresheafedSpace.IsOpenImmersion.ofRestrict X.toPresheafedSpace
        (f := U.inclusion') U.isOpenEmbedding'
    exact PresheafedSpace.IsOpenImmersion.isoOfRangeEq
      (X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding') g
      Subtype.range_coe_subtype
  · change φ.base ((localizationSpectrumMap A.α hA f).base z) = x
    rw [hz, hy]
  · rintro t ⟨w, rfl⟩
    exact ⟨(e.inv.base ((localizationSpectrumMap A.α hA f).base w)).2, hf ⟨w, rfl⟩⟩

/-- **The weak affine formal open subschemes of a formal scheme in the sense of McQuillan form a
basis of its topology:** every open neighbourhood of a point contains a weak affine formal open
neighbourhood of it. -/
theorem exists_isWeakAffineFormalOpen_le {X : LTRS.{u}} (hX : IsMcQuillanFormalScheme X)
    {W : Opens X} {x : X} (hx : x ∈ W) :
    ∃ U : Opens X, IsWeakAffineFormalOpen X U ∧ x ∈ U ∧ U ≤ W := by
  obtain ⟨V, hxV, hV⟩ := (isMcQuillanFormalScheme_iff_forall_isWeakAffineFormalOpen X).mp hX x
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isWeakAffineFormalOpen_le_of_isWeakAffineFormalOpen hV hxV hx
  exact ⟨U, hU, hxU, hUW.trans inf_le_right⟩

/-- **The weak affine formal open subschemes of a formal scheme in the sense of McQuillan form a
basis of its topology.** -/
theorem isBasis_isWeakAffineFormalOpen {X : LTRS.{u}} (hX : IsMcQuillanFormalScheme X) :
    Opens.IsBasis {U : Opens X | IsWeakAffineFormalOpen X U} :=
  Opens.isBasis_iff_nbhd.mpr fun hx ↦ exists_isWeakAffineFormalOpen_le hX hx

end AlgebraicGeometry

end
