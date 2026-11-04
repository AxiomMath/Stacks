module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitOneGeneratorSquare
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidTwoGenerator
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.OneGeneratorSquareShape

/-!
# Condition (3) of Stacks 0EX9 for Tag 0EXE at the squares of Example 0EVG

Condition (3) of Stacks 0EX9 for the shape of Example 0EVG,
`AlgebraicGeometry.BigHOver.IsOneGeneratorAlmostBlowUpStack`, ranges over the squares of
`(Sch/S)_h` whose underlying pair of morphisms of schemes is *isomorphic* to the model pair
`Spec (A ⧸ J) ⟶ Spec A ⟵ V(f)`, for an ideal `J` annihilated by a power of `f`. Stacks Tag 0EXC
for finite locally free `colim_F 𝒪`-modules,
`AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesComparison_oneGeneratorSquare`,
lives on the square of spectra of `A`, `A ⧸ fA`, `A ⧸ J` and `A ⧸ (J + fA)`. This file carries
the second to the first:

* the centre `V(f)` of the model pair, the closed subscheme of `Spec A` cut out by the ideal sheaf
  attached to `f`, is identified with `Spec (A ⧸ fA)` over `Spec A`, both closed immersions having
  the same ideal sheaf (`AlgebraicGeometry.exists_iso_comp_eq_of_ker_eq`);
* the exceptional corner of the square of the site is identified with `Spec (A ⧸ (J + fA))`,
  both being fibre products (`Stacks.AffineClosedUnion.isPullback_specMap_quotientFactor`);
* the comparison functor at the underlying square of schemes is then an equivalence by
  `AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesComparison_of_isIso`;
* and the comparison functor of the category fibred in groupoids is an equivalence by
  `isEquivalence_twoFibreProductComparison_frobeniusVectorBundleGroupoidFibration` in the
  namespace `AlgebraicGeometry`.

## Main results

* `AlgebraicGeometry.isOneGeneratorAlmostBlowUpStack_frobeniusVectorBundleGroupoidFibration`:
  **condition (3) of Stacks 0EX9 for the shape of Example 0EVG holds for the category fibred in
  groupoids of Stacks Tag 0EXE**, unconditionally.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

/-- **The centre of the model pair of Example 0EVG is `Spec (A ⧸ fA)`.** The closed subscheme of
`Spec A` cut out by the ideal sheaf attached to `f` is isomorphic over `Spec A` to
`Spec (A ⧸ fA)`. -/
theorem exists_iso_subschemeι_ofIdealTop_span_singleton (A : Type u) [CommRing A] (f : A) :
    ∃ j : (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f}))).subscheme ≅
        Spec (.of (A ⧸ Ideal.span {f})),
      (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (Ideal.span {f}))).subschemeι =
        j.hom ≫ Spec.map (OneGeneratorSquare.toCtr A f) := by
  have : IsClosedImmersion (Spec.map (OneGeneratorSquare.toCtr A f)) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of A) (Ideal.span {f})
  refine exists_iso_comp_eq_of_ker_eq _ _ (Scheme.IdealSheafData.ext_of_isAffine ?_)
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ofIdealTop_ideal,
    ker_Spec_map_ideal_top]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  rw [← ideal_comap_isoHom_eq_map_isoInv]
  congr 1
  exact (Ideal.mk_ker (I := Ideal.span {f})).symm

/-- **The square of spectra of Example 0EVG is cartesian**: `Spec (A ⧸ (J + fA))` is the fibre
product of `Spec (A ⧸ J)` and `Spec (A ⧸ fA)` over `Spec A`. -/
theorem OneGeneratorSquare.isPullback_specMap (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    IsPullback (Spec.map (OneGeneratorSquare.modToExc A f J))
      (Spec.map (OneGeneratorSquare.ctrToExc A f J)) (Spec.map (OneGeneratorSquare.toMod A J))
      (Spec.map (OneGeneratorSquare.toCtr A f)) :=
  Stacks.AffineClosedUnion.isPullback_specMap_quotientFactor J (Ideal.span {f})

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

/-- **Condition (3) of Stacks 0EX9 for the shape of Example 0EVG, for the category fibred in
groupoids of Stacks Tag 0EXE.** At every almost blowup square of `(Sch/S)_h` with affine base and
the shape of Example 0EVG, the comparison functor `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` is an
equivalence. This is Stacks Tag 0EXC, which the proof of Stacks Tag 0EXE cites for exactly this
condition. -/
theorem isOneGeneratorAlmostBlowUpStack_frobeniusVectorBundleGroupoidFibration :
    BigHOver.IsOneGeneratorAlmostBlowUpStack B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS) := by
  intro X X' Z E b z d e I _ _ _ hsq hpb hshape
  obtain ⟨A, hA, f, J, _, ⟨n, hann⟩, hm⟩ := hshape
  let := hA
  obtain ⟨iX, iX', iZ, hb, hz⟩ := hm
  obtain ⟨j, hj⟩ := exists_iso_subschemeι_ofIdealTop_span_singleton A f
  have hpA : (p : A) = 0 := natCast_eq_zero_of_isInCharacteristic_spec p A
    (isInCharacteristic_of_hom iX.inv p (isInCharacteristic_bigHOver B S hS p hpS X))
  have hz' : (BigHOver.toScheme B S hS).map z ≫ iX.hom =
      (iZ ≪≫ j).hom ≫ Spec.map (OneGeneratorSquare.toCtr A f) := by
    rw [hz, hj, Iso.trans_hom, Category.assoc]
  have hb' : (BigHOver.toScheme B S hS).map b ≫ iX.hom =
      iX'.hom ≫ Spec.map (OneGeneratorSquare.toMod A J) := hb
  -- the exceptional corner of the site square is the exceptional corner of the model
  have h' : IsPullback ((BigHOver.toScheme B S hS).map d ≫ iX'.hom)
      ((BigHOver.toScheme B S hS).map e ≫ (iZ ≪≫ j).hom) (Spec.map (OneGeneratorSquare.toMod A J))
      (Spec.map (OneGeneratorSquare.toCtr A f)) :=
    hpb.flip.of_iso (Iso.refl _) iX' (iZ ≪≫ j) iX (by simp) (by simp) hb' hz'
  let iE := h'.isoIsPullback _ _ (OneGeneratorSquare.isPullback_specMap A f J)
  refine isEquivalence_twoFibreProductComparison_frobeniusVectorBundleGroupoidFibration hpS
    b z d e hsq hpb.w.symm ?_
  exact isEquivalence_frobeniusColimitVectorBundlesComparison_of_isIso p
    ((BigHOver.toScheme B S hS).map b) ((BigHOver.toScheme B S hS).map z)
    ((BigHOver.toScheme B S hS).map d) ((BigHOver.toScheme B S hS).map e)
    (Spec.map (OneGeneratorSquare.toMod A J)) (Spec.map (OneGeneratorSquare.toCtr A f))
    (Spec.map (OneGeneratorSquare.modToExc A f J)) (Spec.map (OneGeneratorSquare.ctrToExc A f J))
    (isInCharacteristic_bigHOver B S hS p hpS X) (isInCharacteristic_bigHOver B S hS p hpS X')
    (isInCharacteristic_bigHOver B S hS p hpS Z) (isInCharacteristic_bigHOver B S hS p hpS E)
    (OneGeneratorSquare.charBase A p hpA) (OneGeneratorSquare.charMod A J p hpA)
    (OneGeneratorSquare.charCtr A f p hpA) (OneGeneratorSquare.charExc A f J p hpA)
    hpb.w.symm (OneGeneratorSquare.specMap_square A f J) iX.hom iX'.hom (iZ ≪≫ j).hom iE.hom
    hb' hz'
    (h'.isoIsPullback_hom_fst _ _ (OneGeneratorSquare.isPullback_specMap A f J)).symm
    (h'.isoIsPullback_hom_snd _ _ (OneGeneratorSquare.isPullback_specMap A f J)).symm
    (isEquivalence_frobeniusColimitVectorBundlesComparison_oneGeneratorSquare p A f J n hann hpA)

end AlgebraicGeometry

end
