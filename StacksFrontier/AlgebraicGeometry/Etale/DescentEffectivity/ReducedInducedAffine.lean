module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduced induced scheme on a closed subset of an affine scheme

A closed subset `Z` of `Spec A` is cut out by a radical ideal `I`, and the reduced induced
scheme structure on `Z` is then `Spec (A ⧸ I)`. This file proves that identification *over*
`Spec A`: the isomorphism carries the canonical inclusion
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedInclusion` to
`Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.

The commuting triangle is the whole content. The two halves of the proof of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) speak different languages: the
geometric half produces a descent datum over the reduced induced scheme on the complement of an
already-effective open inside an affine chart, while the henselization half is written in
`Ideal.Quotient.mk` and `PrimeSpectrum.zeroLocus`. An abstract isomorphism of the two schemes
does not let a morphism over one base be read as a morphism over the other; the identification
has to be compatible with the structure morphisms to `Spec A`, and that is what is stated here.

## Main results

* `AlgebraicGeometry.exists_isIso_reducedInducedScheme_of_range_eq`: **recognition of the reduced
  induced scheme up to isomorphism.** A preimmersion from a reduced scheme whose image is exactly
  the locally closed subset `T` *is* the canonical inclusion of the reduced induced scheme on `T`,
  up to a unique isomorphism over the ambient scheme.
* `AlgebraicGeometry.exists_isIso_reducedInducedScheme_specQuotient_of_range_eq`: **the
  identification bridge**, for a closed subset presented as that image.
* `AlgebraicGeometry.exists_isIso_reducedInducedScheme_specQuotient`: the same with the closed
  subset and the equation naming it as the zero locus of `I` as hypotheses, which is the shape a
  caller holding a closed subset of `Spec A` consumes.
* `AlgebraicGeometry.exists_isRadical_zeroLocus_eq_compl`,
  `AlgebraicGeometry.exists_isRadical_zeroLocus_eq_compl_opens` and
  `AlgebraicGeometry.exists_isRadical_fg_zeroLocus_eq_compl_opens`: every open of `Spec A` is the
  complement of the zero locus of a radical ideal, finitely generated when `A` is Noetherian.
  This is the `hU` hypothesis of
  `AlgebraicGeometry.singleton_coprod_desc_specMap_henselization_mem_fpqcPrecoverage`.
* `AlgebraicGeometry.exists_isIso_reducedInducedScheme_of_image_eq`: **change of ambient scheme
  for the reduced induced scheme.** Along a preimmersion `h : X' ⟶ X` carrying a locally closed
  subset `Z'` of `X'` onto a locally closed subset `Z` of `X`, the two reduced induced schemes
  agree, compatibly with their canonical morphisms to `X`.
* `AlgebraicGeometry.exists_isIso_reducedInducedScheme_fromSpec`: the same for the chart
  `hW.fromSpec : Spec Γ(T, W) ⟶ T` of an affine open `W`, which is the change of ambient scheme
  the two halves of Tag 0BTP are separated by.
* `AlgebraicGeometry.exists_isRadical_fg_isIso_reducedInducedScheme_fromSpec`: the chart transport
  and the presentation of the transported subset as a zero locus in one statement, which is the
  shape the henselization half consumes.

## Implementation notes

The recognition statement is proved from the universal property
`AlgebraicGeometry.exists_lift_reducedInduced` exactly as
`AlgebraicGeometry.isAffine_reducedInduced_of_range_eq` is, but keeping the isomorphism instead
of discarding it for affineness: the lift of a preimmersion with the same image is a surjective
closed immersion onto a reduced scheme, hence an isomorphism. Only `IsPreimmersion` is required
of the given morphism — local closedness of its image is supplied by the hypothesis that the
image is `T`.

The closed subset of `Spec A` is a binder throughout, together with the equation naming it.
Writing it out as `PrimeSpectrum.zeroLocus I` gives a term of type `Set (PrimeSpectrum A)`, and
the ambient scheme that the reduced induced scheme is formed in then has to be recovered from
that type by unification — a problem of the shape `↥?X =?= PrimeSpectrum A`, which exhausts the
heartbeat budget rather than failing. So `AlgebraicGeometry.range_spec_map_quotient_mk`, which
already identifies the image of `Spec (A ⧸ I) ⟶ Spec A` as the zero locus of `I`, is the one
declaration mentioning the zero locus, and
`AlgebraicGeometry.exists_isIso_reducedInducedScheme_specQuotient` is its one-line composition
with the bridge.

The same reason keeps `AlgebraicGeometry.exists_isRadical_zeroLocus_eq_compl` stated for a plain
subset of `PrimeSpectrum A`: its proof rewrites complements, and `rw` cannot cross between
`Set (PrimeSpectrum A)` and `Set ↥(Spec (CommRingCat.of A))`, which are equal only
semireducibly. The `Scheme.Opens` form is a separate declaration whose proof crosses once, by
`exact`.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 0F2L](https://stacks.math.columbia.edu/tag/0F2L)
* [Stacks Project, Tag 0F2S](https://stacks.math.columbia.edu/tag/0F2S)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

/-! ### Recognition of the reduced induced scheme up to isomorphism -/

/-- **A preimmersion from a reduced scheme whose image is a locally closed subset `T` is the
canonical inclusion of the reduced induced scheme on `T`, up to isomorphism over the ambient
scheme.**

This is the isomorphism underlying `AlgebraicGeometry.isAffine_reducedInduced_of_range_eq`,
which only records that the reduced induced scheme is affine. Here the isomorphism itself is
kept, together with the commuting triangle over the ambient scheme; without the triangle the
isomorphism cannot be used to move morphisms over one of the two schemes to the other.

See [Stacks, Tag 0F2L](https://stacks.math.columbia.edu/tag/0F2L). -/
theorem exists_isIso_reducedInducedScheme_of_range_eq {X Y : Scheme.{u}} (T : Set X)
    (hT : IsLocallyClosed T) [IsReduced Y] (f : Y ⟶ X) [IsPreimmersion f]
    (hrange : Set.range f = T) :
    ∃ e : reducedInducedScheme T hT ≅ Y, e.hom ≫ f = reducedInducedInclusion T hT := by
  obtain ⟨g, hg⟩ := exists_lift_reducedInduced T hT f hrange.le
  have hinclRange : Set.range (reducedInducedInclusion T hT) = T :=
    range_reducedInducedInclusion T hT
  have hgPre : IsPreimmersion g := by
    have : IsPreimmersion (g ≫ reducedInducedInclusion T hT) := by rw [hg]; infer_instance
    exact IsPreimmersion.of_comp g (reducedInducedInclusion T hT)
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨y, hy⟩ := hrange.ge (hinclRange.le ⟨z, rfl⟩)
    refine ⟨y, (reducedInducedInclusion T hT).isEmbedding.injective ?_⟩
    have heval : reducedInducedInclusion T hT (g y) = f y := by
      simpa only [← Scheme.Hom.comp_apply] using congrArg (fun q : Y ⟶ X => q y) hg
    exact heval.trans hy
  have : IsClosedImmersion g :=
    IsClosedImmersion.of_isPreimmersion g (Set.range_eq_univ.mpr hgsurj ▸ isClosed_univ)
  have : Surjective g := ⟨hgsurj⟩
  have : IsIso g := isIso_of_isClosedImmersion_of_surjective g
  refine ⟨(asIso g).symm, ?_⟩
  change CategoryTheory.inv g ≫ f = reducedInducedInclusion T hT
  rw [← hg, IsIso.inv_hom_id_assoc]

/-! ### The identification bridge over an affine base -/

/-- **The reduced induced scheme on a closed subset of `Spec A` which is the image of
`Spec (A ⧸ I) ⟶ Spec A`, for `I` radical, is `Spec (A ⧸ I)` over `Spec A`.** The isomorphism
carries the canonical inclusion of the reduced induced scheme to
`Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.

Radicality of `I` is what makes `A ⧸ I` reduced, hence `Spec (A ⧸ I)` a *reduced* closed
subscheme with image `Z`, which is what
`AlgebraicGeometry.exists_isIso_reducedInducedScheme_of_range_eq` recognises.

See [Stacks, Tag 0F2S](https://stacks.math.columbia.edu/tag/0F2S). -/
theorem exists_isIso_reducedInducedScheme_specQuotient_of_range_eq (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.IsRadical) {Z : Set (Spec (CommRingCat.of A))}
    (hZ : IsLocallyClosed Z)
    (hrange : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) = Z) :
    ∃ e : reducedInducedScheme Z hZ ≅ Spec (CommRingCat.of (A ⧸ I)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        reducedInducedInclusion Z hZ := by
  have : _root_.IsReduced (A ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  have : _root_.IsReduced (CommRingCat.of (A ⧸ I)) :=
    inferInstanceAs (_root_.IsReduced (A ⧸ I))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact exists_isIso_reducedInducedScheme_of_range_eq Z hZ _ hrange

/-- **The reduced induced scheme on a closed subset of `Spec A` cut out by a radical ideal `I` is
`Spec (A ⧸ I)`, over `Spec A`**, with the closed subset and the equation naming it as
hypotheses.

This is `AlgebraicGeometry.exists_isIso_reducedInducedScheme_specQuotient_of_range_eq` composed
with `AlgebraicGeometry.range_spec_map_quotient_mk`. The closed subset stays a binder: written out
as `PrimeSpectrum.zeroLocus I`, its type is `Set (PrimeSpectrum A)` rather than
`Set ↥(Spec (CommRingCat.of A))`, and recovering the ambient *scheme* from it is not something
unification does. -/
@[ega "I 1.1.11" "special case"]
theorem exists_isIso_reducedInducedScheme_specQuotient (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.IsRadical) {Z : Set (Spec (CommRingCat.of A))} (hZ : IsLocallyClosed Z)
    (hZI : Z = PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ e : reducedInducedScheme Z hZ ≅ Spec (CommRingCat.of (A ⧸ I)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        reducedInducedInclusion Z hZ :=
  exists_isIso_reducedInducedScheme_specQuotient_of_range_eq A I hI hZ
    ((range_spec_map_quotient_mk I).trans hZI.symm)

/-! ### Opens of an affine scheme as complements of zero loci -/

/-- **Every open subset of `Spec A` is the complement of the zero locus of a radical ideal of
`A`.**

The second conclusion is the hypothesis `hU` of
`AlgebraicGeometry.singleton_coprod_desc_specMap_henselization_mem_fpqcPrecoverage`; the first
records the closed complement as the zero locus of the same ideal, which is the subset the
reduced induced scheme of
`AlgebraicGeometry.exists_isIso_reducedInducedScheme_specQuotient` is formed on. -/
theorem exists_isRadical_zeroLocus_eq_compl {A : Type u} [CommRing A]
    {s : Set (PrimeSpectrum A)} (hs : IsOpen s) :
    ∃ I : Ideal A, I.IsRadical ∧ sᶜ = PrimeSpectrum.zeroLocus (I : Set A) ∧
      s = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := by
  obtain ⟨I, hI, hZ⟩ :=
    (PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal sᶜ).mp hs.isClosed_compl
  refine ⟨I, hI, hZ, ?_⟩
  rw [← hZ, compl_compl]

/-- `AlgebraicGeometry.exists_isRadical_zeroLocus_eq_compl` for an open of `Spec A` presented as
an element of `(Spec (CommRingCat.of A)).Opens`, which is the shape a chart of a scheme arrives
in. -/
theorem exists_isRadical_zeroLocus_eq_compl_opens {A : Type u} [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) :
    ∃ I : Ideal A, I.IsRadical ∧
      (U : Set (Spec (CommRingCat.of A)))ᶜ = PrimeSpectrum.zeroLocus (I : Set A) ∧
      (U : Set (Spec (CommRingCat.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ :=
  exists_isRadical_zeroLocus_eq_compl (A := A)
    (s := (U : Set (Spec (CommRingCat.of A)))) U.isOpen

/-- Over a Noetherian ring the ideal of
`AlgebraicGeometry.exists_isRadical_zeroLocus_eq_compl_opens` is finitely generated as well,
which is the remaining hypothesis of
`AlgebraicGeometry.singleton_coprod_desc_specMap_henselization_mem_fpqcPrecoverage`. -/
theorem exists_isRadical_fg_zeroLocus_eq_compl_opens {A : Type u} [CommRing A]
    [IsNoetherianRing A] (U : (Spec (CommRingCat.of A)).Opens) :
    ∃ I : Ideal A, I.IsRadical ∧ I.FG ∧
      (U : Set (Spec (CommRingCat.of A)))ᶜ = PrimeSpectrum.zeroLocus (I : Set A) ∧
      (U : Set (Spec (CommRingCat.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := by
  obtain ⟨I, hI, hzl, hcompl⟩ := exists_isRadical_zeroLocus_eq_compl_opens (A := A) U
  exact ⟨I, hI, IsNoetherian.noetherian I, hzl, hcompl⟩

/-! ### Change of ambient scheme -/

/-- **Change of ambient scheme for the reduced induced scheme.** If a preimmersion
`h : X' ⟶ X` carries a locally closed subset `Z'` of `X'` onto a locally closed subset `Z` of
`X`, then the reduced induced scheme on `Z` is the reduced induced scheme on `Z'`, compatibly
with the two canonical morphisms to `X`.

`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedComparison` compares the
reduced induced schemes of two *nested subsets of one ambient scheme*; this changes the ambient
scheme instead, which is what reading a subset of a scheme inside a chart of it amounts to.

The reduced induced scheme on `Z'` is reduced, and the composite of its canonical inclusion with
`h` is a preimmersion with image exactly `Z`, so
`AlgebraicGeometry.exists_isIso_reducedInducedScheme_of_range_eq` recognises it. -/
theorem exists_isIso_reducedInducedScheme_of_image_eq {X X' : Scheme.{u}} (h : X' ⟶ X)
    [IsPreimmersion h] {Z : Set X} (hZ : IsLocallyClosed Z) {Z' : Set X'}
    (hZ' : IsLocallyClosed Z') (himg : h '' Z' = Z) :
    ∃ e : reducedInducedScheme Z hZ ≅ reducedInducedScheme Z' hZ',
      e.hom ≫ reducedInducedInclusion Z' hZ' ≫ h = reducedInducedInclusion Z hZ := by
  have hrange : Set.range (reducedInducedInclusion Z' hZ' ≫ h) = Z := by
    have hfun : ⇑(reducedInducedInclusion Z' hZ' ≫ h) =
        ⇑h ∘ ⇑(reducedInducedInclusion Z' hZ') := funext fun y ↦ Scheme.Hom.comp_apply _ _ _
    rw [hfun, Set.range_comp, range_inclusion Z' hZ', himg]
  exact exists_isIso_reducedInducedScheme_of_range_eq Z hZ _ hrange

/-- **The reduced induced scheme on a locally closed subset of an affine open chart, read inside
the chart.** For `Z` a locally closed subset of `T` contained in an affine open `W`, the reduced
induced scheme on `Z` is the reduced induced scheme on the preimage of `Z` in `Spec Γ(T, W)`,
compatibly with the canonical morphisms to `T`.

This is the transport the two halves of [Stacks, Tag
0BTP](https://stacks.math.columbia.edu/tag/0BTP) are separated by: the geometric half produces a
reduced induced scheme on a subset of an arbitrary affine Noetherian base, while the
henselization half is written over the spectrum of a ring. The chart morphism
`AlgebraicGeometry.IsAffineOpen.fromSpec` is an open immersion, hence a preimmersion, and its
image is `W`, so
`AlgebraicGeometry.exists_isIso_reducedInducedScheme_of_image_eq` applies. -/
theorem exists_isIso_reducedInducedScheme_fromSpec {T : Scheme.{u}} {W : T.Opens}
    (hW : IsAffineOpen W) {Z : Set T} (hZ : IsLocallyClosed Z) (hZW : Z ⊆ (W : Set T))
    {Z' : Set (Spec Γ(T, W))} (hZ' : IsLocallyClosed Z') (hZ'eq : Z' = hW.fromSpec ⁻¹' Z) :
    ∃ e : reducedInducedScheme Z hZ ≅ reducedInducedScheme Z' hZ',
      e.hom ≫ reducedInducedInclusion Z' hZ' ≫ hW.fromSpec = reducedInducedInclusion Z hZ := by
  refine exists_isIso_reducedInducedScheme_of_image_eq hW.fromSpec hZ hZ' ?_
  rw [hZ'eq, Set.image_preimage_eq_inter_range, hW.range_fromSpec,
    Set.inter_eq_self_of_subset_left hZW]

/-- The preimage, in an affine open chart, of the part of the chart outside an open set is the
complement of an open set of the chart. -/
theorem preimage_fromSpec_inter_compl {T : Scheme.{u}} {W : T.Opens} (hW : IsAffineOpen W)
    (U₀ : T.Opens) :
    hW.fromSpec ⁻¹' ((W : Set T) ∩ (U₀ : Set T)ᶜ) =
      ((hW.fromSpec ⁻¹ᵁ U₀ : (Spec Γ(T, W)).Opens) : Set (Spec Γ(T, W)))ᶜ := by
  have huniv : hW.fromSpec ⁻¹' (W : Set T) = Set.univ :=
    Set.univ_subset_iff.mp fun x _ ↦ hW.range_fromSpec.le ⟨x, rfl⟩
  rw [Set.preimage_inter, Set.preimage_compl, huniv, Set.univ_inter]
  rfl

/-- **The chart transport together with the presentation of the transported subset as a zero
locus.** For `W` an affine open of `T` with Noetherian ring of sections and `U₀` an open of `T`,
the reduced induced scheme on the part of `W` outside `U₀` is, over `T`, the reduced induced
scheme on the zero locus of a radical finitely generated ideal `I` of `Γ(T, W)` inside
`Spec Γ(T, W)`.

This is the shape the henselization half of [Stacks, Tag
0BTP](https://stacks.math.columbia.edu/tag/0BTP) consumes: the ideal `I` is the one whose
henselization the covering
`AlgebraicGeometry.singleton_coprod_desc_specMap_henselization_mem_fpqcPrecoverage` is taken
along, and `AlgebraicGeometry.exists_isIso_reducedInducedScheme_specQuotient` then identifies
the reduced induced scheme on its zero locus with `Spec (Γ(T, W) ⧸ I)`.

The subset is a binder with the equation naming it beside it, both for `Z` upstairs and for the
zero locus downstairs: writing a zero locus into the subset argument of
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedScheme` leaves the ambient
scheme to be recovered from `Set (PrimeSpectrum _)` by unification, which does not terminate. -/
theorem exists_isRadical_fg_isIso_reducedInducedScheme_fromSpec {T : Scheme.{u}} {W : T.Opens}
    (hW : IsAffineOpen W) (hN : IsNoetherianRing Γ(T, W)) (U₀ : T.Opens) {Z : Set T}
    (hZ : IsLocallyClosed Z) (hZeq : Z = (W : Set T) ∩ (U₀ : Set T)ᶜ) :
    ∃ (I : Ideal Γ(T, W)) (Z' : Set (Spec Γ(T, W))) (hZ' : IsLocallyClosed Z')
      (e : reducedInducedScheme Z hZ ≅ reducedInducedScheme Z' hZ'),
      I.IsRadical ∧ I.FG ∧ Z' = PrimeSpectrum.zeroLocus (I : Set Γ(T, W)) ∧
        e.hom ≫ reducedInducedInclusion Z' hZ' ≫ hW.fromSpec = reducedInducedInclusion Z hZ := by
  have _ := hN
  obtain ⟨I, hIrad, hIfg, hzl, -⟩ :=
    exists_isRadical_fg_zeroLocus_eq_compl_opens (A := Γ(T, W)) (hW.fromSpec ⁻¹ᵁ U₀)
  obtain ⟨e, he⟩ := exists_isIso_reducedInducedScheme_fromSpec hW hZ
    (hZeq ▸ Set.inter_subset_left) (hZ.preimage hW.fromSpec.continuous) rfl
  exact ⟨I, _, _, e, hIrad, hIfg, by rw [hZeq, preimage_fromSpec_inter_compl hW U₀, ← hzl], he⟩

end AlgebraicGeometry

end
