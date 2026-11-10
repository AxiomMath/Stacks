module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.AffineZeroScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SlicingHypotheses
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Spreading out a regular sequence of germs to a quasi-regular immersion

Let `Z` be a locally Noetherian scheme, `b` a list of global sections of `Z` and `z` a point at
which the germs of `b` form a regular sequence in the local ring.  Then an affine neighbourhood
of `z` on which the restrictions of `b` are a quasi-regular sequence exists, and over it the zero
scheme of `b` is a quasi-regular immersion.  This is the implication `(1) → (12)` of Stacks tag
063I for the ideal sheaf of such a zero scheme, that is
`Stacks.AlgebraicGeometry.Statement063I`.

## Main results

* `Stacks.AlgebraicGeometry.isQuasiRegular_of_isWeaklyRegular`: a weakly regular sequence is
  quasi-regular, for a list rather than a `List.ofFn` family.
* `Stacks.AlgebraicGeometry.exists_mem_isQuasiRegularImmersion_of_isRegular_germ`: the statement
  itself.
* `Stacks.AlgebraicGeometry.statement063I`: the same, packaged as
  `Stacks.AlgebraicGeometry.Statement063I`, so that it discharges the first hypothesis of
  `Stacks.AlgebraicGeometry.exists_affineOpen_regularImmersion_of_isRegular_fiber`.

## Implementation notes

The regular germs are a quasi-regular sequence in the local ring, which is the localization of
the ring of sections of an affine open `W ∋ z` at the prime of `z`.  That ring is Noetherian
because `Z` is locally Noetherian, so Stacks tag 061Q
(`RingTheory.Sequence.exists_notMem_isQuasiRegular_away_of_isQuasiRegular_atPrime`) produces a
section `g` invertible at `z` such that the restrictions of `b` are quasi-regular over the
localization away from `g`.  That lemma concludes for *every* model of the localization away from
`g`, and `Γ(D(g), ⊤)` is one of them
(`AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen`), so no transport along a chosen
construction is needed.  The passage from the sequence over `Γ(D(g), ⊤)` to the immersion is
`Stacks.AlgebraicGeometry.isQuasiRegularImmersion_comap_ofIdealTop_of_isQuasiRegular`.

Only the weakly regular half of the hypothesis is used:  what Stacks tag 063I asks at the point
is a regular sequence, and quasi-regularity of a weakly regular sequence is Stacks tag 062F
followed by Stacks tag 062I.

## References

* [Stacks Project, Lemma 31.20.6 (Tag 063I)](https://stacks.math.columbia.edu/tag/063I)
* [Stacks Project, Lemma 10.68.10 (Tag 061Q)](https://stacks.math.columbia.edu/tag/061Q)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry RingTheory.Sequence
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

/-- **A weakly regular sequence is quasi-regular**, stated for a list.  This is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegular_ofFn_of_isWeaklyRegular` with the
family replaced by the indexing function of the list. -/
theorem isQuasiRegular_of_isWeaklyRegular {R : Type*} [CommRing R] (l : List R)
    (h : IsWeaklyRegular R l) : IsQuasiRegular R l := by
  simpa using RegularIdealSheaf.isQuasiRegular_ofFn_of_isWeaklyRegular
    (fun i : Fin l.length => l[i]) (by simpa using h)

/-- **The implication `(1) → (12)` of Stacks tag 063I for a zero scheme.**  On a locally
Noetherian scheme, if the germs at `z` of a list `b` of global sections form a regular sequence,
then on some open neighbourhood of `z` the zero scheme of `b` is a quasi-regular immersion. -/
theorem exists_mem_isQuasiRegularImmersion_of_isRegular_germ {Z : Scheme.{u}}
    (hN : IsLocallyNoetherian Z) (b : List Γ(Z, ⊤)) (z : Z)
    (hreg : IsRegular (Z.presheaf.stalk z) (b.map (Z.presheaf.germ ⊤ z trivial).hom)) :
    ∃ V : Z.Opens, z ∈ V ∧ IsQuasiRegularImmersion
      ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList b)).comap V.ι).subschemeι := by
  -- an affine open neighbourhood of `z`, with Noetherian ring of sections
  obtain ⟨W, hW, hzW, -⟩ := Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (show z ∈ (⊤ : Z.Opens) from trivial)
  have hWnoeth : IsNoetherianRing Γ(Z, W) := hN.component_noetherian ⟨W, hW⟩
  -- the local ring at `z` is the localization of `Γ(Z, W)` at the prime of `z`
  let := Z.presheaf.algebra_section_stalk (⟨z, hzW⟩ : W)
  have := hW.isLocalization_stalk (⟨z, hzW⟩ : W)
  have hpp : (hW.primeIdealOf (⟨z, hzW⟩ : W)).asIdeal.IsPrime :=
    (hW.primeIdealOf (⟨z, hzW⟩ : W)).isPrime
  -- the restrictions of `b` to `W`, whose images in the local ring are the germs
  have hfun : (algebraMap Γ(Z, W) (Z.presheaf.stalk z)) ∘
      (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom =
      (Z.presheaf.germ ⊤ z trivial).hom := by
    funext y
    exact TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE (le_top : W ≤ ⊤)) z hzW y
  have hquasi : IsQuasiRegular (Z.presheaf.stalk z)
      ((b.map (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom).map
        (algebraMap Γ(Z, W) (Z.presheaf.stalk z))) := by
    rw [List.map_map, hfun]
    exact isQuasiRegular_of_isWeaklyRegular _ hreg.toIsWeaklyRegular
  -- Stacks 061Q: quasi-regularity spreads out to a standard open
  obtain ⟨g, hg, hqr⟩ :=
    RingTheory.Sequence.exists_notMem_isQuasiRegular_away_of_isQuasiRegular_atPrime
      (hW.primeIdealOf (⟨z, hzW⟩ : W)).asIdeal
      (b.map (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom)
      (Z.presheaf.stalk z) (Z.presheaf.stalk z)
      (Algebra.linearMap Γ(Z, W) (Z.presheaf.stalk z)) hquasi
  -- `g` is invertible at `z`, so `z` lies on the standard open `D(g)`
  have hzV : z ∈ Z.basicOpen g := by
    rw [Z.mem_basicOpen g z hzW]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _
      (hW.primeIdealOf (⟨z, hzW⟩ : W)).asIdeal g).mpr hg
  -- `Γ(D(g), ⊤)` is a model of the localization away from `g`
  have hle : (Z.basicOpen g).ι ''ᵁ ⊤ ≤ W := by
    rw [Scheme.Opens.ι_image_top]; exact Z.basicOpen_le g
  let : Algebra Γ(Z, W) Γ((Z.basicOpen g).toScheme, ⊤) :=
    (Z.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : IsLocalization.Away g Γ((Z.basicOpen g).toScheme, ⊤) :=
    hW.isLocalization_of_eq_basicOpen g (homOfLE hle) (Scheme.Opens.ι_image_top _)
  -- the restrictions of `b` to `D(g)` are quasi-regular there
  have hfun' : (algebraMap Γ(Z, W) Γ((Z.basicOpen g).toScheme, ⊤)) ∘
      (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom =
      ((Z.basicOpen g).ι.appTop).hom := by
    funext y
    change (Z.presheaf.map (homOfLE hle).op).hom
      ((Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom y) = _
    rw [← CommRingCat.comp_apply, ← Z.presheaf.map_comp]
    rfl
  have hqrV := hqr Γ((Z.basicOpen g).toScheme, ⊤) Γ((Z.basicOpen g).toScheme, ⊤)
    (Algebra.linearMap Γ(Z, W) Γ((Z.basicOpen g).toScheme, ⊤))
  rw [List.map_map, hfun'] at hqrV
  exact ⟨Z.basicOpen g, hzV, isQuasiRegularImmersion_comap_ofIdealTop_of_isQuasiRegular b _
    (hW.basicOpen g) hqrV⟩

/-- **`Stacks.AlgebraicGeometry.Statement063I`.**  The first of the two inputs owed to the
assembly of Stacks tag 06LI. -/
theorem statement063I : Statement063I.{u} := fun hN b z hreg =>
  exists_mem_isQuasiRegularImmersion_of_isRegular_germ hN b z hreg

end Stacks.AlgebraicGeometry

end
