module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange

/-!
# The smooth locus read on a fibre

Let `g : Y ⟶ S` be a morphism locally of finite type over a locally Noetherian base. Over such a
base local finite type is local finite presentation, so `g` has a smooth locus, and the smooth
locus of a base change of `g` is the inverse image of that of `g` as soon as one of the two
morphisms of the cartesian square is flat. Reading this over a fibre `Y_s`, whose structure
morphism to `Spec κ(s)` is the base change of `g` along `Spec κ(s) ⟶ S`, turns a dense open of
`Y_s` smooth over `κ(s)` into density of the smooth locus of `g` inside `Y_s`.

## Main results

* `AlgebraicGeometry.flat_Spec_map_algebraMap_of_isFractionRing`: the spectrum of a fraction
  field is flat over the spectrum of the domain.
* `AlgebraicGeometry.dense_preimage_smoothLocus_fiber_of_dense_open_smooth`: for a flat morphism
  locally of finite type over a locally Noetherian base, a dense open of a fibre that is smooth
  over the residue field of the base point forces the smooth locus to be dense in that fibre.
* `AlgebraicGeometry.dense_preimage_smoothLocus_of_dense_open_smooth`: the same conclusion for a
  base change along the fraction field of a Noetherian domain, where no flatness of the morphism
  itself is needed because the fraction field is flat over the domain.

## Implementation notes

The flatness side condition of `AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`
is discharged on the morphism of the square that is available: on a fibre it is flatness of `g`,
while on a base change along a fraction field it is flatness of that base change, which holds
unconditionally because a fraction field is a localization. The local finite presentation of the
base-changed morphism is produced from that of `g` by stability under base change rather than
being assumed, so the hypotheses are local finite type and local Noetherianness alone.

## References

* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
* [Stacks Project, Tag 01TX](https://stacks.math.columbia.edu/tag/01TX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **The spectrum of a fraction field is flat over the spectrum of the domain.** -/
theorem flat_Spec_map_algebraMap_of_isFractionRing (B : Type u) [CommRing B] [IsDomain B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap B L))) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat L (nonZeroDivisors B))

/-- **A dense open of a fibre smooth over the residue field makes the smooth locus dense in that
fibre.** Let `g : Y ⟶ S` be flat and locally of finite type over a locally Noetherian base and
let `s` be a point of `S`. If the fibre `Y_s` has a dense open subscheme smooth over the residue
field `κ(s)`, then the inverse image in `Y_s` of the smooth locus of `g` is dense. -/
theorem dense_preimage_smoothLocus_fiber_of_dense_open_smooth {Y S : Scheme.{u}} (g : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType g] [Flat g] (s : S) (U : (g.fiber s).Opens)
    (hU : Dense (U : Set (g.fiber s))) (hsmooth : Smooth (U.ι ≫ g.fiberToSpecResidueField s)) :
    Dense ((g.fiberι s ⁻¹ᵁ g.smoothLocus : (g.fiber s).Opens) : Set (g.fiber s)) := by
  have _ : LocallyOfFinitePresentation g := inferInstance
  have hsq : IsPullback (g.fiberι s) (g.fiberToSpecResidueField s) g (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  have _ : LocallyOfFinitePresentation (g.fiberToSpecResidueField s) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hsq (Or.inl ‹Flat g›)]
  refine hU.mono fun z hz ↦ ?_
  have htop := (U.ι ≫ g.fiberToSpecResidueField s).smoothLocus_eq_top
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at htop
  have hz' : (⟨z, hz⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ (g.fiberToSpecResidueField s).smoothLocus := by
    rw [htop]; trivial
  exact hz'

/-- **A dense open of the base change to the fraction field smooth over it makes the smooth locus
dense there.** Let `g : Y ⟶ Spec B` be locally of finite type over a Noetherian domain `B` with
fraction field `L`, and let `XL` be a base change of `Y` along `Spec L ⟶ Spec B`. If `XL` has a
dense open subscheme smooth over `L`, then the inverse image in `XL` of the smooth locus of `g`
is dense. No flatness of `g` is needed: the base change is flat because `L` is a localization
of `B`. -/
theorem dense_preimage_smoothLocus_of_dense_open_smooth {B : Type u} [CommRing B]
    [IsNoetherianRing B] [IsDomain B] {L : Type u} [Field L] [Algebra B L] [IsFractionRing B L]
    {Y XL : Scheme.{u}} (g : Y ⟶ Spec (.of B)) [LocallyOfFiniteType g]
    {p : XL ⟶ Y} {q : XL ⟶ Spec (.of L)}
    (sq : IsPullback p q g (Spec.map (CommRingCat.ofHom (algebraMap B L))))
    (U : XL.Opens) (hU : Dense (U : Set XL)) (hsmooth : Smooth (U.ι ≫ q)) :
    Dense ((p ⁻¹ᵁ g.smoothLocus : XL.Opens) : Set XL) := by
  have _ : LocallyOfFinitePresentation g := inferInstance
  have _ : LocallyOfFinitePresentation q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_preimage_of_isPullback sq
    (Or.inr (flat_Spec_map_algebraMap_of_isFractionRing B L))]
  refine hU.mono fun z hz ↦ ?_
  have htop := (U.ι ≫ q).smoothLocus_eq_top
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at htop
  have hz' : (⟨z, hz⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ q.smoothLocus := by rw [htop]; trivial
  exact hz'

end AlgebraicGeometry
