module

public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeGenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Birationality of the normalization morphism

The normalization morphism of a reduced scheme whose quasi-compact opens have finitely many
irreducible components is birational: it matches up the generic points of the irreducible
components and is an isomorphism on the local rings there.

## Main results

* `AlgebraicGeometry.Scheme.isBirational_normalization`: the normalization morphism of a reduced
  scheme is birational (Tag 0BXC).
* `AlgebraicGeometry.Scheme.genericPointResidueSpectrum_isReduced`: the coproduct of the spectra
  of the residue fields at the generic points of `X` is reduced.
* `AlgebraicGeometry.Scheme.surjectiveOnStalks_fromGenericPointResidueFields`: the canonical
  morphism from that coproduct to `X` is surjective on stalks.
* `AlgebraicGeometry.Scheme.range_fromGenericPointResidueFields` and
  `AlgebraicGeometry.Scheme.fromGenericPointResidueFields_injective`: that morphism is injective
  with image exactly the set of generic points of irreducible components of `X`.
* `AlgebraicGeometry.Scheme.isIso_stalkMap_fromGenericPointResidueFields`: for reduced `X` it is
  an isomorphism on every stalk.

## Implementation notes

Write `f : S ⟶ X` for the canonical morphism from the coproduct `S` of the spectra of the residue
fields at the generic points of `X`, so that the normalization `N` of `X` is the relative
normalization of `X` in `f` and `f = toNormalization ≫ fromNormalization`. Since `f` is injective
with image the generic points of `X`, and every generic point of `N` is in the image of
`toNormalization` (Tag 0AXP), `fromNormalization` is a bijection between generic points. Since
`f` is an isomorphism on stalks and the stalks of the reduced scheme `N` at its generic points are
fields, `fromNormalization` is an isomorphism on the local rings at generic points.

The source states the result for a scheme with globally finitely many irreducible components.
Only the local finiteness condition under which the normalization is defined is used.

## References

* [Stacks Project, Tag 035M](https://stacks.math.columbia.edu/tag/035M)
* [Stacks Project, Tag 0AXP](https://stacks.math.columbia.edu/tag/0AXP)
* [Stacks Project, Tag 0BXC](https://stacks.math.columbia.edu/tag/0BXC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-! ### The coproduct of the generic-point residue spectra -/

/-- The coproduct of the spectra of the residue fields at the generic points of `X` is reduced,
being covered by spectra of fields. -/
instance genericPointResidueSpectrum_isReduced :
    IsReduced (genericPointResidueSpectrum X) := by
  unfold genericPointResidueSpectrum
  have : ∀ i, IsReduced ((sigmaOpenCover
      (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))).X i) := fun η ↦
    inferInstanceAs (IsReduced (Spec (.of (X.residueField η.1))))
  exact IsReduced.of_openCover _
    (sigmaOpenCover (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))))

/-- The canonical morphism from the generic-point residue spectra is surjective on stalks: on each
summand it is `X.fromSpecResidueField`, which is a preimmersion. -/
instance surjectiveOnStalks_fromGenericPointResidueFields :
    SurjectiveOnStalks (fromGenericPointResidueFields X) := by
  unfold fromGenericPointResidueFields
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @SurjectiveOnStalks)
    (sigmaOpenCover (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))))).mpr ?_
  change ∀ η : genericPoints X, SurjectiveOnStalks
    (Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η ≫
      Sigma.desc (fun η : genericPoints X ↦ X.fromSpecResidueField η.1))
  intro η
  rw [Sigma.ι_desc]
  infer_instance

/-- A point of the summand indexed by a generic point `ζ` is sent to `ζ`. -/
private theorem fromGenericPointResidueFields_ι_apply (ζ : genericPoints X)
    (r : Spec (.of (X.residueField ζ.1))) :
    fromGenericPointResidueFields X
      (Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) ζ r) = ζ.1 := by
  show (Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) ζ ≫
    fromGenericPointResidueFields X) r = ζ.1
  rw [genericPointResidueSpectrum_ι_fromGenericPointResidueFields,
    X.fromSpecResidueField_apply]

/-- Every point of the coproduct of the generic-point residue spectra is sent to a generic point
of an irreducible component of `X`. -/
theorem mem_genericPoints_fromGenericPointResidueFields (s : genericPointResidueSpectrum X) :
    fromGenericPointResidueFields X s ∈ genericPoints X := by
  obtain ⟨⟨η, p⟩, rfl⟩ :=
    (sigmaMk (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))).surjective s
  rw [sigmaMk_mk, fromGenericPointResidueFields_ι_apply]
  exact η.2

/-- The canonical morphism from the generic-point residue spectra is injective: each summand is
the spectrum of a field, hence a single point, and distinct summands are indexed by distinct
generic points of `X`. -/
theorem fromGenericPointResidueFields_injective :
    Function.Injective (fromGenericPointResidueFields X) := by
  intro s t hst
  obtain ⟨⟨η, p⟩, rfl⟩ :=
    (sigmaMk (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))).surjective s
  obtain ⟨⟨ξ, q⟩, rfl⟩ :=
    (sigmaMk (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))).surjective t
  simp only [sigmaMk_mk] at hst ⊢
  have hη : η = ξ := Subtype.ext
    (((fromGenericPointResidueFields_ι_apply X η p).symm.trans hst).trans
      (fromGenericPointResidueFields_ι_apply X ξ q))
  subst hη
  congr 1
  exact Subsingleton.elim _ _

/-- The image of the canonical morphism from the generic-point residue spectra is exactly the set
of generic points of the irreducible components of `X`. -/
theorem range_fromGenericPointResidueFields :
    Set.range (fromGenericPointResidueFields X) = genericPoints X := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨s, rfl⟩
    exact mem_genericPoints_fromGenericPointResidueFields X s
  · intro η hη
    refine ⟨sigmaMk (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
      ⟨⟨η, hη⟩, (default : Spec (.of (X.residueField η)))⟩, ?_⟩
    rw [sigmaMk_mk]
    exact fromGenericPointResidueFields_ι_apply X ⟨η, hη⟩ _

variable [IsReduced X]

/-- For a reduced scheme the canonical morphism from the generic-point residue spectra is an
isomorphism on every stalk: it is surjective on stalks, and injective there because the stalk of
a reduced scheme at a generic point of an irreducible component is a field. -/
@[ega "IV 20.1.3.1" "partial"]
theorem isIso_stalkMap_fromGenericPointResidueFields (s : genericPointResidueSpectrum X) :
    IsIso ((fromGenericPointResidueFields X).stalkMap s) := by
  have hfield : IsField (X.presheaf.stalk (fromGenericPointResidueFields X s)) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (mem_genericPoints_fromGenericPointResidueFields X s)
  let : Field (X.presheaf.stalk (fromGenericPointResidueFields X s)) := hfield.toField
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨RingHom.injective _, SurjectiveOnStalks.stalkMap_surjective _ s⟩

/-! ### Birationality of the normalization -/

/-- **Stacks Project, Tag 0BXC.** The normalization morphism of a reduced scheme whose
quasi-compact opens have finitely many irreducible components is birational. -/
@[stacks 0BXC]
theorem isBirational_normalization
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsBirational (X.normalization hX) := by
  let := quasiCompactFromGenericPointResidueFields X hX
  let := quasiSeparatedFromGenericPointResidueFields X
  set f := fromGenericPointResidueFields X with hf
  -- Every generic point of the normalization comes from the coproduct, by Tag 0AXP.
  have hlift : ∀ z : X.normalizationScheme hX, z ∈ genericPoints (X.normalizationScheme hX) →
      ∃ s : genericPointResidueSpectrum X, f.toNormalization s = z := by
    intro z hz
    obtain ⟨s, -, -, -, hs⟩ :=
      exists_genericPoint_irreducibleComponent_mapping_to f (x := z) (Z := closure {z}) hz rfl
    exact ⟨s, hs⟩
  have hfac : ∀ s : genericPointResidueSpectrum X,
      X.normalization hX (f.toNormalization s) = f s := by
    intro s
    show (f.toNormalization ≫ f.fromNormalization) s = f s
    rw [f.toNormalization_fromNormalization]
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨?_, ?_, ?_⟩ ?_
  · exact fun z hz ↦ normalization_mem_genericPoints X hX hz
  · intro z hz w hw hzw
    obtain ⟨s, hs⟩ := hlift z hz
    obtain ⟨t, ht⟩ := hlift w hw
    have : f s = f t := by rw [← hfac s, ← hfac t, hs, ht, hzw]
    rw [← hs, ← ht, fromGenericPointResidueFields_injective X this]
  · intro η hη
    obtain ⟨s, hs⟩ : η ∈ Set.range f := by rwa [hf, range_fromGenericPointResidueFields]
    let Z : irreducibleComponents (X.normalizationScheme hX) :=
      ⟨irreducibleComponent (f.toNormalization s),
        irreducibleComponent_mem_irreducibleComponents _⟩
    let z : genericPoints (X.normalizationScheme hX) := genericPoints.ofComponent Z
    have hzZ : IsGenericPoint z.1 (Z : Set (X.normalizationScheme hX)) :=
      genericPoints.isGenericPoint_ofComponent Z
    have hspec : z.1 ⤳ f.toNormalization s := by
      rw [specializes_iff_mem_closure, hzZ]
      exact mem_irreducibleComponent
    have hηcl : η ∈ closure {X.normalization hX z.1} := by
      have h := (hspec.map (X.normalization hX).continuous).mem_closure
      rwa [hfac s, hs] at h
    have hsub : closure ({η} : Set X) ⊆ closure {X.normalization hX z.1} :=
      closure_minimal (Set.singleton_subset_iff.2 hηcl) isClosed_closure
    have hη' : closure ({η} : Set X) ∈ irreducibleComponents X := hη
    have heq : IsGenericPoint (X.normalization hX z.1) (closure ({η} : Set X)) :=
      (hη'.2 isIrreducible_singleton.closure hsub).antisymm hsub
    exact ⟨z.1, z.2, heq.eq isGenericPoint_closure⟩
  · intro z hz
    obtain ⟨s, rfl⟩ := hlift z hz
    have : IsReduced (X.normalizationScheme hX) := by
      show IsReduced f.normalization
      infer_instance
    have hfield : IsField ((X.normalizationScheme hX).presheaf.stalk (f.toNormalization s)) :=
      isField_stalk_of_closure_mem_irreducibleComponents _ _ hz
    let : Field ((X.normalizationScheme hX).presheaf.stalk (f.toNormalization s)) :=
      hfield.toField
    have htoInj : Function.Injective (f.toNormalization.stalkMap s).hom :=
      RingHom.injective _
    have hcompIso : IsIso
        ((X.normalization hX).stalkMap (f.toNormalization s) ≫
          f.toNormalization.stalkMap s) := by
      rw [← Scheme.Hom.stalkMap_comp,
        Scheme.Hom.stalkMap_congr_hom _ _ f.toNormalization_fromNormalization s]
      have := isIso_stalkMap_fromGenericPointResidueFields X s
      exact IsIso.comp_isIso' (Iso.isIso_hom (X.presheaf.stalkCongr _)) inferInstance
    have hbij : Function.Bijective
        ((X.normalization hX).stalkMap (f.toNormalization s) ≫
          f.toNormalization.stalkMap s).hom :=
      ConcreteCategory.bijective_of_isIso _
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩
    · exact fun a b hab ↦ hbij.1 (by
        simpa only [ConcreteCategory.comp_apply] using
          congrArg (f.toNormalization.stalkMap s).hom hab)
    · intro b
      obtain ⟨a, ha⟩ := hbij.2 ((f.toNormalization.stalkMap s).hom b)
      refine ⟨a, htoInj ?_⟩
      simpa only [ConcreteCategory.comp_apply] using ha

end AlgebraicGeometry.Scheme
