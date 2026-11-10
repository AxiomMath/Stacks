module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ReductionToDomainBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Shrinking the base of Stacks Tag 0559 to an affine open

Part of Steps E and F of the proof of Stacks Tag 0559. Step F of that proof clears denominators:
the hypersurface model of the function field of `X` has coefficients in the fraction field of the
base ring `R`, and only after inverting a single nonzero `a : R` does it live over the base. The
assembly of Steps D, E and F
(`AlgebraicGeometry.exists_open_geometricallyIrreducible_of_specModel`) therefore runs over
`Spec (Localization.Away a)`, that is over the basic open `D(a) ⊆ Spec R`, and its conclusion has
to be transported back to `Spec R`.

This module performs that transport in both directions at once. Given a nonempty open
`W ⊆ Spec R` presented as the spectrum of a domain by an isomorphism `e : W ≅ Spec A`, the
morphism `f ∣_ W ≫ e.hom` over `Spec A` inherits every hypothesis of
`AlgebraicGeometry.GeometricallyIrreducibleAfterShrinkingOverDomain`, and a nonempty open of
`Spec A` over which its fibres are geometrically irreducible produces one of `Spec R` over which
the fibres of `f` are.

## The transport

Three things have to move.

* The source. `W` is a nonempty open of the irreducible space `Spec R`, so it contains the
  generic point, and the generic point of `X` lies over the generic point of `Spec R`; hence
  `f ⁻¹ᵁ W` is a nonempty open of the integral scheme `X`, and so is integral.
* The morphism properties. Each of `LocallyOfFiniteType`, `QuasiCompact`, `Flat`,
  `LocallyOfFinitePresentation` and `QuasiSeparated` is Zariski local at the target, giving it
  for `f ∣_ W`, and each is stable under composition with an isomorphism.
* The two fibrewise hypotheses, and the conclusion, which travel along the two reversible
  transports of `AlgebraicGeometry.prop_fiberToSpecResidueField_of_morphismRestrict`, for the
  restriction, and `AlgebraicGeometry.prop_fiberToSpecResidueField_comp_iso_iff`, for the
  isomorphism. The point of `Spec A` to use is the image of the generic point of `W`, which is
  the generic point of `Spec A` because an isomorphism is an open map between irreducible spaces,
  and whose image in `Spec R` is the generic point of `Spec R` for the same reason.

The open of `Spec R` produced at the end is the image under `W.ι` of the preimage under `e.hom`
of the open of `Spec A`; it is open because `W.ι` is an open immersion, and nonempty because
`e.hom` is surjective.

## Main results

* `AlgebraicGeometry.Scheme.Opens.ι_genericPoint`: the generic point of an irreducible open
  subscheme of an irreducible scheme lies over the generic point.
* `AlgebraicGeometry.apply_genericPoint_of_isIso`: an isomorphism matches up generic points.
* `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_opensIsoSpec`: **the base
  restriction**, the statement above.
* `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_basicOpen`: its specialization to
  the basic open `W = D(a)` of a nonzero `a : R`, which is the form Step F produces.

## Implementation notes

`AlgebraicGeometry.FinitePresentation` is a conjunction rather than a class, so it is taken and
produced as an explicit hypothesis, its three conjuncts being reinstalled as instances.

`MorphismProperty.RespectsIso @GeometricallyIrreducible` is not found by instance search even
though `MorphismProperty.IsStableUnderBaseChange @GeometricallyIrreducible` is, so it is supplied
by hand, as in `AlgebraicGeometry.geometricallyIrreducible_morphismRestrict_iff_forall`.

Nonemptiness of `W` is taken as an explicit hypothesis about the underlying set rather than as an
instance, and the instances about the open subscheme `W.toScheme` are derived from it inside the
proof; points of `W` are bound as points of `W.toScheme` throughout, which is the form the
instances about an open subscheme are stated for.

No Stacks tag is attached: Steps E and F are not themselves tags of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Steps E and F of the
  first proof
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The generic point of an irreducible open subscheme of an irreducible scheme lies over the
generic point of the scheme. -/
theorem Scheme.Opens.ι_genericPoint {Y : Scheme.{u}} [IrreducibleSpace Y] (W : Y.Opens)
    [IrreducibleSpace W.toScheme] : W.ι (genericPoint W.toScheme) = genericPoint Y :=
  apply_genericPoint_of_isOpenMap W.ι W.ι.isOpenEmbedding.isOpenMap

/-- An isomorphism of schemes with irreducible source and target matches up the generic
points. -/
theorem apply_genericPoint_of_isIso {Y Z : Scheme.{u}} (e : Y ≅ Z) [IrreducibleSpace Y]
    [IrreducibleSpace Z] : e.hom (genericPoint Y) = genericPoint Z :=
  apply_genericPoint_of_isOpenMap e.hom e.hom.homeomorph.isOpenMap

/-- A morphism with irreducible source whose fibre over a generic point `η` of the target is
geometrically irreducible carries the generic point of the source to `η`. The fibre is then
nonempty, so `η` is in the range of the morphism; the closure of the range is therefore the whole
target, and it is also the closure of the image of the generic point. -/
@[ega "0 2.1.8" "special case"]
theorem map_genericPoint_of_geometricallyIrreducible_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] {η : Y} (hη : IsGenericPoint η Set.univ)
    (hfib : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    f (genericPoint X) = η := by
  have hirr : IrreducibleSpace (f.fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f := f.fiberToSpecResidueField η)
  obtain ⟨z⟩ := hirr.toNonempty
  have hmem : η ∈ Set.range f :=
    ⟨f.fiberι η z, show f.fiberι η z ∈ f ⁻¹' {η} by
      rw [← f.range_fiberι η]; exact Set.mem_range_self z⟩
  have hgp : IsGenericPoint (f (genericPoint X)) (closure (Set.range f)) := by
    have h := (genericPoint_spec X).image f.continuous
    rwa [Set.image_univ] at h
  have hcl : closure (Set.range f) = Set.univ :=
    Set.univ_subset_iff.mp (hη ▸ closure_mono (Set.singleton_subset_iff.mpr hmem))
  exact (hcl ▸ hgp).eq hη

/-- **The base restriction of Stacks Tag 0559.** Let `f : X ⟶ Spec R` satisfy the hypotheses of
`AlgebraicGeometry.GeometricallyIrreducibleAfterShrinkingOverDomain` over a domain `R`, with the
generic point of `X` lying over the generic point of `Spec R`, and let `W` be a nonempty open of
`Spec R` isomorphic to the spectrum of a domain `A`. If the conclusion of Tag 0559 over a domain
base is available for morphisms to `Spec A`, then `f` has geometrically irreducible fibres over a
nonempty open subscheme of `Spec R`. -/
theorem exists_open_geometricallyIrreducible_of_opensIsoSpec {R : CommRingCat.{u}} [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    [Flat f] (hfp : FinitePresentation f) (hgen : f (genericPoint X) = genericPoint (Spec R))
    (hgi : GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec R))))
    (hgr : GeometricallyReduced (f.fiberToSpecResidueField (genericPoint (Spec R))))
    {W : (Spec R).Opens} (hW : (W : Set (Spec R)).Nonempty) {A : CommRingCat.{u}} [IsDomain A]
    (e : W.toScheme ≅ Spec A)
    (H : ∀ {X' : Scheme.{u}} (g : X' ⟶ Spec A), IsIntegral X' → LocallyOfFiniteType g →
      QuasiCompact g → Flat g → FinitePresentation g →
      GeometricallyIrreducible (g.fiberToSpecResidueField (genericPoint (Spec A))) →
      GeometricallyReduced (g.fiberToSpecResidueField (genericPoint (Spec A))) →
      ∃ V : (Spec A).Opens, Nonempty V ∧ GeometricallyIrreducible (g ∣_ V)) :
    ∃ V : (Spec R).Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V) := by
  have hri : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hrr : MorphismProperty.RespectsIso @GeometricallyReduced.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hlfp : LocallyOfFinitePresentation f := hfp.1
  have hqs : QuasiSeparated f := hfp.2.2
  have hWne : Nonempty W.toScheme := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  have hWirr : IrreducibleSpace W.toScheme := W.ι.isOpenEmbedding.irreducibleSpace
  have hgW : W.ι (genericPoint W.toScheme) = genericPoint (Spec R) := W.ι_genericPoint
  have hgA : e.hom (genericPoint W.toScheme) = genericPoint (Spec A) :=
    apply_genericPoint_of_isIso e
  -- The restricted source is a nonempty open of `X`, hence integral.
  have hmem : genericPoint X ∈ f ⁻¹ᵁ W := by
    change f (genericPoint X) ∈ W
    rw [hgen, ← hgW]
    exact (genericPoint W.toScheme).2
  have : Nonempty (f ⁻¹ᵁ W).toScheme := ⟨⟨genericPoint X, hmem⟩⟩
  -- The two fibrewise hypotheses, read at the generic point of `Spec A`.
  have hgi' : GeometricallyIrreducible
      ((f ∣_ W ≫ e.hom).fiberToSpecResidueField (genericPoint (Spec A))) := by
    rw [← hgA]
    refine (prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyIrreducible)
      (f ∣_ W) e _).mpr ((prop_fiberToSpecResidueField_of_morphismRestrict
        (P := @GeometricallyIrreducible) f W _).mpr ?_)
    rwa [hgW]
  have hgr' : GeometricallyReduced
      ((f ∣_ W ≫ e.hom).fiberToSpecResidueField (genericPoint (Spec A))) := by
    rw [← hgA]
    refine (prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyReduced)
      (f ∣_ W) e _).mpr ((prop_fiberToSpecResidueField_of_morphismRestrict
        (P := @GeometricallyReduced) f W _).mpr ?_)
    rwa [hgW]
  obtain ⟨V, hVne, hV⟩ := H (f ∣_ W ≫ e.hom) inferInstance inferInstance inferInstance
    inferInstance ⟨inferInstance, inferInstance, inferInstance⟩ hgi' hgr'
  -- Push the open of `Spec A` forward to `Spec R`.
  have key : ∀ y : W.toScheme, e.hom y ∈ V →
      GeometricallyIrreducible (f.fiberToSpecResidueField (W.ι y)) := by
    intro y hy
    refine (prop_fiberToSpecResidueField_of_morphismRestrict
      (P := @GeometricallyIrreducible) f W y).mp
      ((prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyIrreducible)
        (f ∣_ W) e y).mp ?_)
    simpa using (geometricallyIrreducible_morphismRestrict_iff_forall _ V).mp hV ⟨e.hom y, hy⟩
  obtain ⟨v⟩ := hVne
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : W.toScheme, e.hom y₀ = V.ι v := e.hom.homeomorph.surjective _
  refine ⟨⟨W.ι '' (e.hom ⁻¹' (V : Set (Spec A))),
    W.ι.isOpenEmbedding.isOpenMap _ (V.isOpen.preimage e.hom.continuous)⟩,
    ⟨⟨W.ι y₀, y₀, ?_, rfl⟩⟩, ?_⟩
  · rw [Set.mem_preimage, hy₀]
    exact v.2
  · rw [geometricallyIrreducible_morphismRestrict_iff_forall]
    intro w
    obtain ⟨y, hy, hyeq⟩ : ∃ y : W.toScheme, e.hom y ∈ V ∧ W.ι y = w.1 := w.2
    have hkey := key y hy
    rwa [hyeq] at hkey

/-- The basic open of a nonzero element of a domain contains the generic point of the spectrum;
in particular it is nonempty. -/
theorem genericPoint_mem_basicOpen (R : CommRingCat.{u}) [IsDomain R] {a : R} (ha : a ≠ 0) :
    genericPoint (Spec R) ∈ (PrimeSpectrum.basicOpen a : (Spec R).Opens) := by
  rw [show genericPoint (Spec R) = (⊥ : PrimeSpectrum R) from genericPoint_eq_bot_of_affine R]
  exact (PrimeSpectrum.mem_basicOpen a ⊥).mpr fun h ↦ ha (Ideal.mem_bot.mp h)

/-- **The base restriction of Stacks Tag 0559 along a basic open.** The form in which Step F of
the proof produces the shrunken base: inverting a single nonzero element `a` of the domain `R`
replaces `Spec R` by the basic open `D(a)`, which is the spectrum of the localization of `R` away
from `a` (`AlgebraicGeometry.basicOpenIsoSpecAway`). Nonemptiness of `D(a)`, the only hypothesis
of `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_opensIsoSpec` that is not immediate
in this situation, is what this specialization supplies. -/
theorem exists_open_geometricallyIrreducible_of_basicOpen {R : CommRingCat.{u}} [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    [Flat f] (hfp : FinitePresentation f) (hgen : f (genericPoint X) = genericPoint (Spec R))
    (hgi : GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec R))))
    (hgr : GeometricallyReduced (f.fiberToSpecResidueField (genericPoint (Spec R))))
    {a : R} (ha : a ≠ 0) {A : CommRingCat.{u}} [IsDomain A]
    (e : Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen a) ≅ Spec A)
    (H : ∀ {X' : Scheme.{u}} (g : X' ⟶ Spec A), IsIntegral X' → LocallyOfFiniteType g →
      QuasiCompact g → Flat g → FinitePresentation g →
      GeometricallyIrreducible (g.fiberToSpecResidueField (genericPoint (Spec A))) →
      GeometricallyReduced (g.fiberToSpecResidueField (genericPoint (Spec A))) →
      ∃ V : (Spec A).Opens, Nonempty V ∧ GeometricallyIrreducible (g ∣_ V)) :
    ∃ V : (Spec R).Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V) :=
  exists_open_geometricallyIrreducible_of_opensIsoSpec f hfp hgen hgi hgr
    ⟨genericPoint (Spec R), genericPoint_mem_basicOpen R ha⟩ e H

end AlgebraicGeometry

end
