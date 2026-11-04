module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalChart
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison

/-!
# The section ring of an affine chart of a blowup

Let `S` be a scheme, `ℐ` a quasi-coherent sheaf of ideals, `U` an affine open of `S` and
`a ∈ ℐ(U)`. The chart `Stacks.Blowup.blowUpAffineChart` identifies `Spec Γ(S, U)[ℐ(U)/a]` with an
affine open of the blowup. This file reads that identification on sections: the section ring of
the blowup over the affine open underlying the chart *is* the affine blowup algebra, as a
`Γ(S, U)`-algebra.

The algebra structure is the content. A bare ring isomorphism would not let a ring-level
statement about `Γ(S, U)[ℐ(U)/a]` be read on the chart: the structure map of the chart over the
base has to be the structure map of the affine blowup algebra, which is the sections-level form
of `Stacks.Blowup.blowUpAffineChart_blowUpToBase`.

Both facts are proved for an arbitrary open immersion of an affine scheme, of which the chart is
an instance; see the implementation notes.

## Main results

* `AlgebraicGeometry.SpecMap_appIso_ΓSpecIso_fromSpec`: for an open immersion `j : Spec T ⟶ Y`,
  the identification of `Γ(Y, j(Spec T))` with `T` carries `Spec` back to `j`.
* `AlgebraicGeometry.appLE_appIso_ΓSpecIso_of_comp`: if moreover `j` composed with a morphism
  `g : Y ⟶ Z` is `Spec φ` followed by the affine identification of an affine open `W` of `Z`,
  then `g`'s map of sections from `W` to `j(Spec T)`, read through that identification, is `φ`.
* `Stacks.Blowup.blowUpAffineChart_image_le_preimage`: the affine open underlying the chart lies
  over `U`, so `blowUpToBase ℐ` has a map of sections from `Γ(S, U)` to it.
* `Stacks.Blowup.chartSectionRingIso`: the section ring of the blowup over that affine open is
  the affine blowup algebra `affineBlowup (ℐ.ideal U) a`.
* `Stacks.Blowup.blowUpToBase_appLE_chartSectionRingIso_hom`: **it is an isomorphism of
  `Γ(S, U)`-algebras.** The structure map of the chart over the base, transported along it, is
  the structure map `Γ(S, U) ⟶ Γ(S, U)[ℐ(U)/a]`.
* `Stacks.Blowup.chartSectionRingIsoBlowup` and
  `Stacks.Blowup.blowUpToBase_appLE_chartSectionRingIsoBlowup_hom`: the same two statements with
  the quotient model `Blowup (ℐ.ideal U) a`, which is the realization the ring-level strict
  transform of [Stacks, Tag 053H] is stated over.
* `Stacks.Blowup.exceptionalChartSection_eq_appLE`: the generator of the exceptional ideal on the
  chart is the restriction of `a` along the blowup morphism.

## Implementation notes

The two statements about an arbitrary open immersion are not a generalisation for its own sake.
Elaborating either of them with the chart written out exhausts the heartbeat budget, as the
implementation notes of `StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalChart.lean` record for
the same area; with the chart behind a variable both cost nothing, and the chart instance is
then one application each.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 052Q](https://stacks.math.columbia.edu/tag/052Q)
* [Stacks Project, Tag 053H](https://stacks.math.columbia.edu/tag/053H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- **The section-ring identification of an open immersion of an affine scheme, read back
through `Spec`, is the immersion.** For `j : Spec T ⟶ Y` an open immersion, the sections of `Y`
over the image of `j` are identified with `T` by `j.appIso` followed by `Scheme.ΓSpecIso`, and
`Spec` of that identification, followed by the affine identification of the image open, is `j`
again. -/
theorem SpecMap_appIso_ΓSpecIso_fromSpec {Y : Scheme.{u}} {T : CommRingCat.{u}} (j : Spec T ⟶ Y)
    [IsOpenImmersion j] :
    Spec.map ((j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso T).hom) ≫
        ((isAffineOpen_top (Spec T)).image_of_isOpenImmersion j).fromSpec = j := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec j
    ((isAffineOpen_top (Spec T)).image_of_isOpenImmersion j) (isAffineOpen_top (Spec T))
    ((j.preimage_image_eq ⊤).ge)
  rw [← Scheme.Hom.appIso_hom', IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [Spec.map_comp, Category.assoc, h, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

/-- **The section-ring identification of an open immersion of an affine scheme is one of algebras
over an affine open it factors through.** Let `j : Spec T ⟶ Y` be an open immersion, `g : Y ⟶ Z`
a morphism and `W` an affine open of `Z` such that `j ≫ g` is `Spec φ` followed by the affine
identification of `W`. Then the map of sections of `g` from `W` to the image of `j`, read through
the identification of those sections with `T`, is `φ`.

Both sides are maps out of `Γ(Z, W)` into `T` and both schemes are affine, so they agree as soon
as their spectra do; and there they agree after composing with the affine identification of `W`,
which is a monomorphism. -/
theorem appLE_appIso_ΓSpecIso_of_comp {Y Z : Scheme.{u}} {T : CommRingCat.{u}} (j : Spec T ⟶ Y)
    [IsOpenImmersion j] (g : Y ⟶ Z) {W : Z.Opens} (hW : IsAffineOpen W)
    (hle : (j ''ᵁ ⊤ : Y.Opens) ≤ g ⁻¹ᵁ W) {φ : Γ(Z, W) ⟶ T}
    (hφ : j ≫ g = Spec.map φ ≫ hW.fromSpec) :
    g.appLE W (j ''ᵁ ⊤) hle ≫ ((j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso T).hom) = φ := by
  have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  refine Spec.map_injective ((cancel_mono hW.fromSpec).mp ?_)
  rw [Spec.map_comp, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec (hV :=
      (isAffineOpen_top (Spec T)).image_of_isOpenImmersion j),
    ← Category.assoc, SpecMap_appIso_ΓSpecIso_fromSpec, hφ]

end AlgebraicGeometry

namespace Stacks.Blowup

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData)

/-- The affine open of the blowup underlying the chart attached to `a ∈ ℐ(U)` lies over `U`: the
chart factors over the base through the affine identification of `U`. -/
theorem blowUpAffineChart_image_le_preimage (U : S.affineOpens) {a : Γ(S, U.1)}
    (ha : a ∈ ℐ.ideal U) :
    (blowUpAffineChart ℐ U ha ''ᵁ ⊤ : (blowUp ℐ).Opens) ≤ blowUpToBase ℐ ⁻¹ᵁ U.1 := by
  rintro x ⟨y, -, rfl⟩
  change (blowUpAffineChart ℐ U ha ≫ blowUpToBase ℐ).base y ∈ (U.1 : Set S)
  rw [blowUpAffineChart_blowUpToBase ℐ U ha]
  exact (Stacks.RelativeProj.isAffineOpen U).range_fromSpec.le (Set.mem_range_self _)

/-- **The section ring of an affine chart of the blowup is the affine blowup algebra.** The chart
`Stacks.Blowup.blowUpAffineChart` is an open immersion of `Spec Γ(S, U)[ℐ(U)/a]`, so it
identifies the sections of the blowup over its image with the global sections of that
spectrum. -/
def chartSectionRingIso (U : S.affineOpens) {a : Γ(S, U.1)} (ha : a ∈ ℐ.ideal U) :
    Γ(blowUp ℐ, blowUpAffineChart ℐ U ha ''ᵁ ⊤) ≅
      CommRingCat.of (affineBlowup (ℐ.ideal U) a) :=
  (blowUpAffineChart ℐ U ha).appIso
      (⊤ : (Spec (CommRingCat.of (affineBlowup (ℐ.ideal U) a))).Opens) ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (affineBlowup (ℐ.ideal U) a))

/-- `Stacks.Blowup.chartSectionRingIso`, read back through `Spec`, is the chart. -/
theorem SpecMap_chartSectionRingIso_hom_fromSpec (U : S.affineOpens) {a : Γ(S, U.1)}
    (ha : a ∈ ℐ.ideal U) :
    Spec.map (chartSectionRingIso ℐ U ha).hom ≫
        ((isAffineOpen_top _).image_of_isOpenImmersion (blowUpAffineChart ℐ U ha)).fromSpec
      = blowUpAffineChart ℐ U ha :=
  SpecMap_appIso_ΓSpecIso_fromSpec (blowUpAffineChart ℐ U ha)

/-- **The section ring of an affine chart of the blowup is the affine blowup algebra as a
`Γ(S, U)`-algebra.** The structure map of the chart over the base, read through
`Stacks.Blowup.chartSectionRingIso`, is the structure map `Γ(S, U) ⟶ Γ(S, U)[ℐ(U)/a]` of the
affine blowup algebra.

This is the sections-level form of `Stacks.Blowup.blowUpAffineChart_blowUpToBase`, and it is what
makes a ring-level statement about `Γ(S, U)[ℐ(U)/a]` readable on the chart. -/
theorem blowUpToBase_appLE_chartSectionRingIso_hom (U : S.affineOpens) {a : Γ(S, U.1)}
    (ha : a ∈ ℐ.ideal U) :
    (blowUpToBase ℐ).appLE U.1 (blowUpAffineChart ℐ U ha ''ᵁ ⊤)
          (blowUpAffineChart_image_le_preimage ℐ U ha) ≫ (chartSectionRingIso ℐ U ha).hom
      = CommRingCat.ofHom (algebraMap Γ(S, U.1) (affineBlowup (ℐ.ideal U) a)) :=
  appLE_appIso_ΓSpecIso_of_comp (blowUpAffineChart ℐ U ha) (blowUpToBase ℐ)
    (Stacks.RelativeProj.isAffineOpen U) (blowUpAffineChart_image_le_preimage ℐ U ha)
    (blowUpAffineChart_blowUpToBase ℐ U ha)

/-- **The section ring of an affine chart of the blowup is the quotient model of the affine
blowup algebra.** Same as `Stacks.Blowup.chartSectionRingIso`, with `Blowup (ℐ.ideal U) a` —
the realization over which the ring-level strict transform of [Stacks, Tag 053H] and the
ring-level flattening theorem of [Stacks, Tag 0810] are stated — in place of `affineBlowup`,
through `Stacks.AffineBlowup.blowupEquivAffineBlowup`. -/
def chartSectionRingIsoBlowup (U : S.affineOpens) {a : Γ(S, U.1)}
    [ha : Fact (a ∈ ℐ.ideal U)] :
    Γ(blowUp ℐ, blowUpAffineChart ℐ U ha.out ''ᵁ ⊤) ≅
      CommRingCat.of (Blowup (ℐ.ideal U) a) :=
  chartSectionRingIso ℐ U ha.out ≪≫
    (Stacks.AffineBlowup.blowupEquivAffineBlowup
      (I := ℐ.ideal U) (a := a)).symm.toRingEquiv.toCommRingCatIso

/-- **The identification with the quotient model is one of `Γ(S, U)`-algebras.** The structure
map of the chart over the base, read through `Stacks.Blowup.chartSectionRingIsoBlowup`, is the
structure map `Γ(S, U) ⟶ Blowup (ℐ.ideal U) a`.

This is what lets a ring-level statement about `Blowup (ℐ.ideal U) a`, such as the strict
transform of [Stacks, Tag 053H], be read on the chart. -/
theorem blowUpToBase_appLE_chartSectionRingIsoBlowup_hom (U : S.affineOpens) {a : Γ(S, U.1)}
    [ha : Fact (a ∈ ℐ.ideal U)] :
    (blowUpToBase ℐ).appLE U.1 (blowUpAffineChart ℐ U ha.out ''ᵁ ⊤)
          (blowUpAffineChart_image_le_preimage ℐ U ha.out) ≫
        (chartSectionRingIsoBlowup ℐ U).hom
      = CommRingCat.ofHom (algebraMap Γ(S, U.1) (Blowup (ℐ.ideal U) a)) := by
  rw [chartSectionRingIsoBlowup, Iso.trans_hom, ← Category.assoc,
    blowUpToBase_appLE_chartSectionRingIso_hom]
  exact CommRingCat.hom_ext (RingHom.ext fun r =>
    (Stacks.AffineBlowup.blowupEquivAffineBlowup (I := ℐ.ideal U) (a := a)).symm.commutes r)

/-- **The generator of the exceptional ideal on a chart is the image of `a` from the base.**
`Stacks.Blowup.exceptionalChartSection` is the image of `a` in the affine blowup algebra read
through the chart, and that is the restriction of `a` along the blowup morphism, by
`Stacks.Blowup.blowUpToBase_appLE_chartSectionRingIso_hom`. -/
theorem exceptionalChartSection_eq_appLE (U : S.affineOpens) {a : Γ(S, U.1)}
    (ha : a ∈ ℐ.ideal U) :
    exceptionalChartSection ℐ U ha =
      ((blowUpToBase ℐ).appLE U.1 (blowUpAffineChart ℐ U ha ''ᵁ ⊤)
        (blowUpAffineChart_image_le_preimage ℐ U ha)).hom a := by
  have h2 := congrArg
    (fun φ : Γ(S, U.1) ⟶ CommRingCat.of (affineBlowup (ℐ.ideal U) a) =>
      φ ≫ (chartSectionRingIso ℐ U ha).inv)
    (blowUpToBase_appLE_chartSectionRingIso_hom ℐ U ha)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
  exact (ConcreteCategory.congr_hom h2 a).symm

end Stacks.Blowup

end
