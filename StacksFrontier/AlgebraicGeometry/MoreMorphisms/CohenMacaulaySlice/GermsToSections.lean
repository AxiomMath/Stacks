module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.GivenSectionsSlice

/-!
# Realising finitely many germs as sections on one affine open

The slicing lemma **Stacks 06LI** cuts a scheme by *global functions*, while the elements it is
applied to are produced in the *local ring* at a point: Stacks 06LC returns a regular sequence
inside the maximal ideal of `𝒪_{Y, y}`, and the slice is cut out by equations with those germs.
This file performs the exchange in the direction that was missing: a finite family of germs at
`y` is the family of germs of genuine sections on one affine open neighbourhood of `y`.

The opposite exchange — replacing the sections Stacks 06LI chooses for itself by prescribed ones
with the same germs — is `Stacks.AlgebraicGeometry.exists_basicOpen_appTop_eq_of_germ_eq` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/CohenMacaulaySlice/GivenSectionsSlice.lean`.

## Main results

* `Stacks.AlgebraicGeometry.exists_isAffineOpen_germ_eq`: finitely many germs at a point of a
  scheme are the germs of sections on one affine open neighbourhood of that point.

## Implementation notes

The construction is the one of `exists_basicOpen_appTop_eq_of_germ_eq`, run forwards.  On an
affine open neighbourhood `V` of `y` the stalk is the localization of `Γ(Y, V)` at the prime of
`y` (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), so each germ is a fraction
`nᵢ / dᵢ` with `dᵢ` outside that prime.  The product `P` of the denominators is again outside
it, so `y` lies in the basic open `D(P)`, which is again affine
(`AlgebraicGeometry.IsAffineOpen.basicOpen`); there the restriction of `P` is a unit
(`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`), hence so is the restriction of each
`dᵢ`, and `nᵢ · dᵢ⁻¹` is the required section.

The germ of that section is identified with the prescribed one by multiplying through by the
germ of `dᵢ`, which is a unit in the stalk; both sides are then reached from `Γ(Y, V)` by
`TopCat.Presheaf.germ_res_apply`.  Nothing is transported along an equality of opens.

The `Algebra Γ(Y, V) 𝒪_{Y,y}` instance is supplied by hand as
`TopCat.Presheaf.algebra_section_stalk` at the bundled point `⟨y, hyV⟩`, since instance search
cannot guess the open `V` nor the membership proof from the unbundled `y` appearing in the
stalk.

## References

* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.AlgebraicGeometry

universe u

/-- **Finitely many germs at a point are the germs of sections on one affine open
neighbourhood.**  On an affine open neighbourhood the stalk is the localization of the sections
at the prime of the point, so each germ is a fraction; shrinking to the basic open of the product
of the denominators makes every denominator invertible, and the fractions become sections
there. -/
theorem exists_isAffineOpen_germ_eq {Y : Scheme.{u}} (y : Y) {r : ℕ}
    (t : Fin r → Y.presheaf.stalk y) :
    ∃ (V : Y.Opens) (hy : y ∈ V), IsAffineOpen V ∧
      ∃ g : Fin r → Γ(Y, V), ∀ i, Y.presheaf.germ V y hy (g i) = t i := by
  classical
  obtain ⟨V, hV, hyV, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  let : Algebra Γ(Y, V) (Y.presheaf.stalk y) :=
    Y.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)
  have hloc : IsLocalization.AtPrime (Y.presheaf.stalk y)
      (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := hV.isLocalization_stalk ⟨y, hyV⟩
  have halg : ∀ s : Γ(Y, V), algebraMap Γ(Y, V) (Y.presheaf.stalk y) s
      = Y.presheaf.germ V y hyV s := fun _ => rfl
  choose n d hnd using fun i : Fin r => IsLocalization.exists_mk'_eq
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl (t i)
  set P : Γ(Y, V) := ∏ i, (d i : Γ(Y, V)) with hP
  have hPcompl : P ∈ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl :=
    Submonoid.prod_mem _ fun i _ => (d i).2
  have hyP : y ∈ Y.basicOpen P := by
    rw [Y.mem_basicOpen P y hyV, ← halg]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) _ P).2 hPcompl
  have hres : ∀ s : Γ(Y, V),
      Y.presheaf.germ (Y.basicOpen P) y hyP
          (Y.presheaf.map (homOfLE (Y.basicOpen_le P)).op s)
        = Y.presheaf.germ V y hyV s := fun s =>
    Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le P)) y hyP s
  have hPunit : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le P)).op P) :=
    Y.toRingedSpace.isUnit_res_basicOpen P
  have hdunit : ∀ i, IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le P)).op (d i : Γ(Y, V))) := by
    intro i
    refine isUnit_of_mul_isUnit_left
      (y := Y.presheaf.map (homOfLE (Y.basicOpen_le P)).op
        (∏ j ∈ Finset.univ.erase i, (d j : Γ(Y, V)))) ?_
    rw [← map_mul, Finset.mul_prod_erase Finset.univ (fun j => (d j : Γ(Y, V)))
      (Finset.mem_univ i), ← hP]
    exact hPunit
  refine ⟨Y.basicOpen P, hyP, hV.basicOpen P,
    fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le P)).op (n i) *
      ↑((hdunit i).unit⁻¹), fun i => ?_⟩
  have hdU : IsUnit (Y.presheaf.germ V y hyV (d i : Γ(Y, V))) := by
    rw [← halg]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) _ _).2 (d i).2
  refine hdU.mul_right_cancel ?_
  have hspec : t i * Y.presheaf.germ V y hyV (d i : Γ(Y, V))
      = Y.presheaf.germ V y hyV (n i) := by
    rw [← hnd i, ← halg, ← halg]
    exact IsLocalization.mk'_spec _ _ _
  rw [hspec, map_mul, ← hres (d i : Γ(Y, V)), ← hres (n i), mul_assoc, ← map_mul,
    IsUnit.val_inv_mul, map_one, mul_one]

end Stacks.AlgebraicGeometry

end
