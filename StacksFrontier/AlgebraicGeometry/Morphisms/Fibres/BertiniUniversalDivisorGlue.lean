module

public import Mathlib.Topology.Sets.OpenCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFamilyDivisors

/-!
# Glueing the chart-wise irreducibility of the universal divisor

A scheme lying over an irreducible scheme `X` is irreducible as soon as its part over every
nonempty affine open of `X` is irreducible: the parts over two nonempty affine opens both contain
the part over a nonempty affine open inside their intersection, which is nonempty because `X` is
irreducible. Applied to the universal divisor `H_univ` of a family of divisors, this shows that
`H_univ` is irreducible once `H_univ ∩ 𝔸^r_U` is irreducible for every nonempty affine open
`U ⊂ X`.

## Main results

* `AlgebraicGeometry.AffineSpace.isOpenImmersion_map`,
  `AlgebraicGeometry.AffineSpace.range_map` and `AlgebraicGeometry.AffineSpace.opensRange_map`:
  for `j : S ⟶ T` an open immersion, the induced map `𝔸^r_S ⟶ 𝔸^r_T` is an open immersion with
  image the preimage of the image of `j`.
* `Stacks.Bertini.irreducibleSpace_of_affineCharts`: a scheme lying over an irreducible scheme `X`
  is irreducible as soon as its part over every nonempty affine open of `X` is irreducible.
* `Stacks.Bertini.FamilyDivisors.irreducibleSpace_universalDivisorScheme_of_charts`: if `X` is
  irreducible and `H_univ ∩ 𝔸^r_U` is irreducible for every nonempty affine open `U ⊂ X`, then
  `H_univ` is irreducible. The chart-wise irreducibility is a hypothesis.

## Implementation notes

The cover of `H_univ` is indexed by the *nonempty* affine opens of `X`:
`TopologicalSpace.PreirreducibleSpace.of_isOpenCover` asks for `Pairwise` non-disjointness over
the whole index type, which the empty chart would violate.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.AffineSpace

/-- The map induced on relative affine spaces by an open immersion is an open immersion. -/
theorem isOpenImmersion_map (n : Type u) {S T : Scheme.{u}} (j : S ⟶ T) [IsOpenImmersion j] :
    IsOpenImmersion (AffineSpace.map n j) :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := n) j).flip inferInstance

/-- The image of the map induced on relative affine spaces by an open immersion `j` is the
preimage, under the projection to `T`, of the image of `j`. -/
theorem range_map (n : Type u) {S T : Scheme.{u}} (j : S ⟶ T) [IsOpenImmersion j] :
    Set.range (AffineSpace.map n j).base =
      (((𝔸(n; T) ↘ T) ⁻¹ᵁ j.opensRange : (𝔸(n; T)).Opens) : Set 𝔸(n; T)) := by
  have hsq := AffineSpace.isPullback_map (n := n) j
  have hsurj : Function.Surjective ⇑hsq.isoPullback.hom :=
    (Scheme.homeoOfIso hsq.isoPullback).surjective
  rw [← hsq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst j (𝔸(n; T) ↘ T)

/-- `AlgebraicGeometry.AffineSpace.range_map` as an equality of opens. -/
theorem opensRange_map (n : Type u) {S T : Scheme.{u}} (j : S ⟶ T) [IsOpenImmersion j] :
    haveI := isOpenImmersion_map n j
    (AffineSpace.map n j).opensRange = (𝔸(n; T) ↘ T) ⁻¹ᵁ j.opensRange :=
  have := isOpenImmersion_map n j
  Opens.ext (range_map n j)

end AlgebraicGeometry.AffineSpace

namespace Stacks.Bertini

/-- A scheme `Z` with a morphism to an irreducible scheme `X` is irreducible as soon as the part
of `Z` over every nonempty affine open of `X` is irreducible. -/
theorem irreducibleSpace_of_affineCharts {Z X : Scheme.{u}} (q : Z ⟶ X) [IrreducibleSpace X]
    (hirr : ∀ U : X.affineOpens, (U.1 : Set X).Nonempty →
      IsIrreducible ((q ⁻¹ᵁ U.1 : Z.Opens) : Set Z)) :
    IrreducibleSpace Z := by
  let V : { U : X.affineOpens // (U.1 : Set X).Nonempty } → Z.Opens := fun U => q ⁻¹ᵁ U.1.1
  have hVirr : ∀ U, IsIrreducible ((V U : Z.Opens) : Set Z) := fun U => hirr U.1 U.2
  have hbasis : ∀ (W : X.Opens) (x : X), x ∈ W →
      ∃ U : { U : X.affineOpens // (U.1 : Set X).Nonempty }, x ∈ U.1.1 ∧ U.1.1 ≤ W := by
    intro W x hx
    obtain ⟨U, hUaff, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    exact ⟨⟨⟨U, hUaff⟩, ⟨x, hxU⟩⟩, hxU, hUW⟩
  have hcover : IsOpenCover V := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨U, hzU, -⟩ := hbasis ⊤ (q.base z) trivial
    exact Opens.mem_iSup.mpr ⟨U, hzU⟩
  have hpair : ∀ U₁ U₂ : { U : X.affineOpens // (U.1 : Set X).Nonempty },
      U₁ ≠ U₂ → ¬ Disjoint (V U₁) (V U₂) := by
    intro U₁ U₂ _ hdisj
    obtain ⟨x, hx⟩ := (IrreducibleSpace.isIrreducible_univ X).2 _ _
      (U₁.1.1).isOpen (U₂.1.1).isOpen (by simpa using U₁.2) (by simpa using U₂.2)
    obtain ⟨U₃, -, hU₃⟩ := hbasis (U₁.1.1 ⊓ U₂.1.1) x hx.2
    obtain ⟨z, hz⟩ := (hVirr U₃).1
    exact Set.not_disjoint_iff.mpr ⟨z, le_trans hU₃ inf_le_left (a := U₃.1.1) hz,
      le_trans hU₃ inf_le_right (a := U₃.1.1) hz⟩ (Opens.coe_disjoint.mpr hdisj)
  have hVpre : ∀ U, PreirreducibleSpace (V U) := fun U =>
    isPreirreducible_iff_preirreducibleSpace.mp (hVirr U).2
  have : PreirreducibleSpace Z := PreirreducibleSpace.of_isOpenCover hpair hcover hVpre
  have : Nonempty Z := by
    obtain ⟨U, -⟩ := hbasis ⊤ (Classical.arbitrary X) trivial
    exact ⟨(hVirr U).1.some⟩
  exact { toNonempty := inferInstance }

namespace FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- If `X` is irreducible and the part of the universal divisor `H_univ` over every nonempty
affine open `U ⊂ X`, its preimage under `H_univ ↪ 𝔸^r_X → X`, is irreducible, then `H_univ` is
irreducible. -/
theorem irreducibleSpace_universalDivisorScheme_of_charts [IrreducibleSpace D.X]
    (hirr : ∀ U : D.X.affineOpens, (U.1 : Set D.X).Nonempty →
      IsIrreducible (((D.universalDivisor.subschemeι ≫ D.parameterProjection) ⁻¹ᵁ U.1 :
        D.universalDivisor.subscheme.Opens) : Set D.universalDivisor.subscheme)) :
    IrreducibleSpace D.universalDivisor.subscheme :=
  irreducibleSpace_of_affineCharts (D.universalDivisor.subschemeι ≫ D.parameterProjection) hirr

end FamilyDivisors

end Stacks.Bertini

end
