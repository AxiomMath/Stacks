module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothComp
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothPermanence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalH1Regular
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalKoszulRegular
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalQuasiRegular
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.ZariskiLocal
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regularity of an immersion into a scheme smooth over the base

Let `Y ⟶ X ⟶ S` with `X ⟶ S` smooth and both `Y ⟶ X` and `Y ⟶ S` immersions. Stacks tag 0693
asserts that Koszul-regularity, `H₁`-regularity and quasi-regularity of `Y ⟶ X` are inherited by
`Y ⟶ S`. Its proof is local on the source, which is what this file supplies: each of the three
conditions may be checked on an open neighbourhood of every point of the source.

## Main results

* `isKoszulRegularImmersion_of_forall_exists_opens`, `isH1RegularImmersion_of_forall_exists_opens`
  and `isQuasiRegularImmersion_of_forall_exists_opens`: parts (2), (3) and (4) of Stacks tag 063J
  hold for an immersion as soon as they hold for its restriction to some open neighbourhood of
  each point of the source.
* `isKoszulRegularIdealSheaf_definingIdealOfHom`: for a *closed* immersion, Koszul-regularity may
  be read off the defining ideal sheaf on the target itself rather than on the coborder range,
  which is where `IsKoszulRegularImmersion` states it.  This is the form in which Stacks tag 067N
  consumes it.
* `exists_affineSpace_isRegularImmersion`: near any point of a scheme smooth over `S` there is a
  regular immersion of an affine open into a finite-dimensional affine space over an affine open
  of `S`, compatible with the structure morphisms.
* `exists_affineSpace_isKoszulRegularImmersion` and `exists_affineSpace_isH1RegularImmersion`:
  composing with such a chart turns a Koszul-regular, respectively `H₁`-regular, immersion into
  a smooth scheme into one into a relative affine space.
* `isKoszulRegularImmersion_comp_of_smooth` and `isH1RegularImmersion_comp_of_smooth`: the
  Koszul-regular and `H₁`-regular clauses of Stacks tag 0693, that a Koszul-regular, respectively
  `H₁`-regular, immersion followed by a smooth morphism is an immersion of the same kind.
* `isQuasiRegularImmersion_comp_affineSpace`: the same for a quasi-regular immersion into a
  relative affine space followed by its projection, which is the case of Stacks tag 0693 that the
  étale factorization of a smooth morphism reduces the quasi-regular clause to.

## Implementation notes

An open immersion is an immersion between two schemes smooth over the target, hence regular by
Stacks tag 067U; so restricting the source along an open immersion preserves all three conditions
by Stacks tag 067Q, and Stacks tag 067S removes an open immersion from the target. Given these,
locality on the source follows from gluing along an open cover of the target (Stacks tag 063J):
for a closed immersion `j` and an open `U` of its source the open `X ∖ j(Y ∖ U)` of the target has
preimage inside `U`, and these opens together with the complement of the image cover the target.

Over an affine open `T` of the base on which the source is closed, the chart of Stacks tag 04II
is a Koszul-regular immersion into a relative affine space whose coordinates lift to `T`; those
lifts define a section of the affine space over `T`, retracted by the projection, through which
the chart factors. Stacks tag 068Z for a retracted immersion then descends Koszul-regularity,
respectively `H₁`-regularity, to the structure morphism over `T`.

A general immersion is reduced to a closed one by factoring through its coborder range. The
transfer back is not a composition of immersions — that would need the quasi-regular case of
Stacks tag 067Q in a shape it does not have — but the independence of the chosen open of Stacks
tag 063J: for a closed immersion the coborder range is everything, so the ambient reading of the
condition on it is the condition on the ambient space itself.

## References

* [Stacks Project, Definition 31.21.4 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Lemma 31.21.6 (Tag 067Q)](https://stacks.math.columbia.edu/tag/067Q)
* [Stacks Project, Lemma 31.23.9 (Tag 067S)](https://stacks.math.columbia.edu/tag/067S)
* [Stacks Project, Lemma 31.23.12 (Tag 0693)](https://stacks.math.columbia.edu/tag/0693)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

section SourceLocal

variable {Y X : Scheme.{u}}

/-- An open immersion is an `H₁`-regular immersion. -/
theorem isH1RegularImmersion_of_isOpenImmersion (i : Y ⟶ X) [IsOpenImmersion i] :
    IsH1RegularImmersion i :=
  isH1RegularImmersion_of_isKoszulRegularImmersion i
    (isKoszulRegularImmersion_of_isOpenImmersion i)

/-- An open immersion is a quasi-regular immersion. -/
theorem isQuasiRegularImmersion_of_isOpenImmersion (i : Y ⟶ X) [IsOpenImmersion i] :
    IsQuasiRegularImmersion i :=
  isQuasiRegularImmersion_of_isH1RegularImmersion i
    (isH1RegularImmersion_of_isOpenImmersion i)

/-- The coborder range of a closed immersion is the whole target. -/
private theorem mem_coborderRange_of_isClosedImmersion (g : Y ⟶ X) [IsClosedImmersion g]
    (x : X) : x ∈ g.coborderRange := by
  change x ∈ coborder (Set.range g.base)
  rw [g.isClosedEmbedding.isClosed_range.coborder_eq]
  exact Set.mem_univ x

/-- For a closed immersion the ambient defining ideal sheaf itself satisfies the Koszul-regularity
condition, since the coborder range imposes no constraint on the neighbourhoods. -/
theorem isKoszulRegularIdealSheaf_definingIdealOfHom (g : Y ⟶ X) [IsClosedImmersion g]
    (hg : IsKoszulRegularImmersion g) :
    IsKoszulRegularIdealSheaf X.toLocallyRingedSpace.toRingedSpace (definingIdealOfHom g) := by
  have h1 := (isKoszulRegularIdealSheaf_restrictSubmodule_iff g.coborderRange
      (definingIdealOfHom g)).mp
    ((isKoszulRegularImmersion_iff g _
      (restrictSubmodule_coborderRange_definingIdealOfHom g)).mp hg)
  intro x hx
  obtain ⟨U, hxU, -, r, f, hK, hG⟩ := h1 x (mem_coborderRange_of_isClosedImmersion g x) hx
  exact ⟨U, hxU, r, f, hK, hG⟩

/-- The `H₁`-regular counterpart of `isKoszulRegularIdealSheaf_definingIdealOfHom`. -/
private theorem isH1RegularIdealSheaf_definingIdealOfHom (g : Y ⟶ X) [IsClosedImmersion g]
    (hg : IsH1RegularImmersion g) :
    IsH1RegularIdealSheaf X.toLocallyRingedSpace.toRingedSpace (definingIdealOfHom g) := by
  have h1 := (isH1RegularIdealSheaf_restrictSubmodule_iff g.coborderRange
      (definingIdealOfHom g)).mp
    ((isH1RegularImmersion_iff g _
      (restrictSubmodule_coborderRange_definingIdealOfHom g)).mp hg)
  intro x hx
  obtain ⟨U, hxU, -, r, f, hK, hG⟩ := h1 x (mem_coborderRange_of_isClosedImmersion g x) hx
  exact ⟨U, hxU, r, f, hK, hG⟩

/-- The quasi-regular counterpart of `isKoszulRegularIdealSheaf_definingIdealOfHom`. -/
theorem isQuasiRegularIdealSheaf_definingIdealOfHom (g : Y ⟶ X) [IsClosedImmersion g]
    (hg : IsQuasiRegularImmersion g) :
    IsQuasiRegularIdealSheaf X.toLocallyRingedSpace.toRingedSpace (definingIdealOfHom g) := by
  have h1 := (isQuasiRegularIdealSheaf_restrictSubmodule_iff g.coborderRange
      (definingIdealOfHom g)).mp
    ((isQuasiRegularImmersion_iff g _
      (restrictSubmodule_coborderRange_definingIdealOfHom g)).mp hg)
  intro x hx
  obtain ⟨U, hxU, -, r, f, hQ, hG⟩ := h1 x (mem_coborderRange_of_isClosedImmersion g x) hx
  exact ⟨U, hxU, r, f, hQ, hG⟩

/-- For a closed immersion `j : Y ⟶ X` and an open `U` of `Y`, the complement of `j (Y ∖ U)` is
an open of `X` whose preimage is contained in `U`. -/
private def avoidOpen (j : Y ⟶ X) [IsClosedImmersion j] (U : Y.Opens) : X.Opens :=
  ⟨(j '' (U : Set Y)ᶜ)ᶜ, (j.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

private theorem preimage_avoidOpen_le (j : Y ⟶ X) [IsClosedImmersion j] (U : Y.Opens) :
    j ⁻¹ᵁ avoidOpen j U ≤ U := fun _ hz => by
  by_contra hzU; exact hz ⟨_, hzU, rfl⟩

private theorem mem_avoidOpen (j : Y ⟶ X) [IsClosedImmersion j] {U : Y.Opens} {y : Y}
    (hy : y ∈ U) : j y ∈ avoidOpen j U := by
  rintro ⟨z, hz, he⟩
  rw [j.isClosedEmbedding.injective he] at hz
  exact hz hy

/-- The opens `avoidOpen j (U y)` together with the complement of the image of a closed
immersion `j`. -/
private def coverFamily (j : Y ⟶ X) [IsClosedImmersion j] (U : Y → Y.Opens) :
    Option Y → X.Opens
  | none => ⟨(Set.range j.base)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  | some y => avoidOpen j (U y)

private theorem iSup_coverFamily (j : Y ⟶ X) [IsClosedImmersion j] (U : Y → Y.Opens)
    (hU : ∀ y, y ∈ U y) : iSup (coverFamily j U) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [TopologicalSpace.Opens.mem_iSup]
  by_cases hx : x ∈ Set.range j.base
  · obtain ⟨y, rfl⟩ := hx
    exact ⟨some y, mem_avoidOpen j (hU y)⟩
  · exact ⟨none, hx⟩

private theorem isEmpty_preimage_coverFamily_none (j : Y ⟶ X) [IsClosedImmersion j]
    (U : Y → Y.Opens) : IsEmpty (j ⁻¹ᵁ coverFamily j U none : Y.Opens).toScheme :=
  ⟨fun z => z.2 ⟨z.1, rfl⟩⟩

/-- Koszul-regularity of a closed immersion may be checked near every point of the source. -/
private theorem isKoszulRegularImmersion_of_local_source_of_isClosedImmersion
    (j : Y ⟶ X) [IsClosedImmersion j]
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsKoszulRegularImmersion (U.ι ≫ j)) :
    IsKoszulRegularImmersion j := by
  classical
  choose U hU hUreg using hlocal
  refine isKoszulRegularImmersion_of_resLE j (coverFamily j U) (iSup_coverFamily j U hU) ?_
  rintro (_ | y)
  · have := isEmpty_preimage_coverFamily_none j U
    exact isKoszulRegularImmersion_of_isOpenImmersion _
  · have hle : j ⁻¹ᵁ coverFamily j U (some y) ≤ U y := preimage_avoidOpen_le j (U y)
    have hcomp : IsKoszulRegularImmersion ((j ⁻¹ᵁ coverFamily j U (some y)).ι ≫ j) := by
      have h1 : IsKoszulRegularImmersion (Y.homOfLE hle ≫ ((U y).ι ≫ j)) :=
        Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp _ _
          (isKoszulRegularImmersion_of_isOpenImmersion _) (hUreg y)
      simpa only [← Category.assoc, Scheme.homOfLE_ι] using h1
    refine isKoszulRegularImmersion_of_comp_of_smooth
      (j.resLE (coverFamily j U (some y)) (j ⁻¹ᵁ coverFamily j U (some y)) le_rfl)
      (coverFamily j U (some y)).ι ?_
    simpa only [Scheme.Hom.resLE_comp_ι] using hcomp

/-- `H₁`-regularity of a closed immersion may be checked near every point of the source. -/
private theorem isH1RegularImmersion_of_local_source_of_isClosedImmersion
    (j : Y ⟶ X) [IsClosedImmersion j]
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsH1RegularImmersion (U.ι ≫ j)) :
    IsH1RegularImmersion j := by
  classical
  choose U hU hUreg using hlocal
  refine isH1RegularImmersion_of_resLE j (coverFamily j U) (iSup_coverFamily j U hU) ?_
  rintro (_ | y)
  · have := isEmpty_preimage_coverFamily_none j U
    exact isH1RegularImmersion_of_isOpenImmersion _
  · have hle : j ⁻¹ᵁ coverFamily j U (some y) ≤ U y := preimage_avoidOpen_le j (U y)
    have hcomp : IsH1RegularImmersion ((j ⁻¹ᵁ coverFamily j U (some y)).ι ≫ j) := by
      have h1 : IsH1RegularImmersion (Y.homOfLE hle ≫ ((U y).ι ≫ j)) :=
        Stacks.AlgebraicGeometry.isH1RegularImmersion_comp _ _
          (isH1RegularImmersion_of_isOpenImmersion _) (hUreg y)
      simpa only [← Category.assoc, Scheme.homOfLE_ι] using h1
    refine isH1RegularImmersion_of_comp_of_smooth
      (j.resLE (coverFamily j U (some y)) (j ⁻¹ᵁ coverFamily j U (some y)) le_rfl)
      (coverFamily j U (some y)).ι ?_
    simpa only [Scheme.Hom.resLE_comp_ι] using hcomp

/-- Quasi-regularity of a closed immersion may be checked near every point of the source. -/
private theorem isQuasiRegularImmersion_of_local_source_of_isClosedImmersion
    (j : Y ⟶ X) [IsClosedImmersion j]
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsQuasiRegularImmersion (U.ι ≫ j)) :
    IsQuasiRegularImmersion j := by
  classical
  choose U hU hUreg using hlocal
  refine isQuasiRegularImmersion_of_resLE j (coverFamily j U) (iSup_coverFamily j U hU) ?_
  rintro (_ | y)
  · have := isEmpty_preimage_coverFamily_none j U
    exact isQuasiRegularImmersion_of_isOpenImmersion _
  · have hle : j ⁻¹ᵁ coverFamily j U (some y) ≤ U y := preimage_avoidOpen_le j (U y)
    have hcomp : IsQuasiRegularImmersion ((j ⁻¹ᵁ coverFamily j U (some y)).ι ≫ j) := by
      have h1 : IsQuasiRegularImmersion (Y.homOfLE hle ≫ ((U y).ι ≫ j)) :=
        Stacks.AlgebraicGeometry.isQuasiRegularImmersion_comp_of_isH1RegularImmersion _ _
          (isH1RegularImmersion_of_isOpenImmersion _) (hUreg y)
      simpa only [← Category.assoc, Scheme.homOfLE_ι] using h1
    refine isQuasiRegularImmersion_of_comp_of_smooth
      (j.resLE (coverFamily j U (some y)) (j ⁻¹ᵁ coverFamily j U (some y)) le_rfl)
      (coverFamily j U (some y)).ι ?_
    simpa only [Scheme.Hom.resLE_comp_ι] using hcomp

/-- **Koszul-regularity of an immersion is local on the source.** If every point of `Y` has an
open neighbourhood `U` for which `U ⟶ Y ⟶ X` is a Koszul-regular immersion, then `j : Y ⟶ X`
is a Koszul-regular immersion. -/
theorem isKoszulRegularImmersion_of_forall_exists_opens (j : Y ⟶ X) [IsImmersion j]
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsKoszulRegularImmersion (U.ι ≫ j)) :
    IsKoszulRegularImmersion j := by
  refine (isKoszulRegularImmersion_iff_of_open j j.coborderRange j.liftCoborder
    j.liftCoborder_ι).mpr (isKoszulRegularIdealSheaf_definingIdealOfHom j.liftCoborder ?_)
  refine isKoszulRegularImmersion_of_local_source_of_isClosedImmersion _ fun y => ?_
  obtain ⟨V, hy, hV⟩ := hlocal y
  exact ⟨V, hy, isKoszulRegularImmersion_of_comp_of_smooth (V.ι ≫ j.liftCoborder)
    j.coborderRange.ι (by simpa only [Category.assoc, Scheme.Hom.liftCoborder_ι] using hV)⟩

/-- **`H₁`-regularity of an immersion is local on the source.** -/
theorem isH1RegularImmersion_of_forall_exists_opens (j : Y ⟶ X) [IsImmersion j]
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsH1RegularImmersion (U.ι ≫ j)) :
    IsH1RegularImmersion j := by
  refine (isH1RegularImmersion_iff_of_open j j.coborderRange j.liftCoborder
    j.liftCoborder_ι).mpr (isH1RegularIdealSheaf_definingIdealOfHom j.liftCoborder ?_)
  refine isH1RegularImmersion_of_local_source_of_isClosedImmersion _ fun y => ?_
  obtain ⟨V, hy, hV⟩ := hlocal y
  exact ⟨V, hy, isH1RegularImmersion_of_comp_of_smooth (V.ι ≫ j.liftCoborder)
    j.coborderRange.ι (by simpa only [Category.assoc, Scheme.Hom.liftCoborder_ι] using hV)⟩

/-- **Quasi-regularity of an immersion is local on the source.** -/
theorem isQuasiRegularImmersion_of_forall_exists_opens (j : Y ⟶ X) [IsImmersion j]
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsQuasiRegularImmersion (U.ι ≫ j)) :
    IsQuasiRegularImmersion j := by
  refine (isQuasiRegularImmersion_iff_of_open j j.coborderRange j.liftCoborder
    j.liftCoborder_ι).mpr (isQuasiRegularIdealSheaf_definingIdealOfHom j.liftCoborder ?_)
  refine isQuasiRegularImmersion_of_local_source_of_isClosedImmersion _ fun y => ?_
  obtain ⟨V, hy, hV⟩ := hlocal y
  exact ⟨V, hy, isQuasiRegularImmersion_of_comp_of_smooth (V.ι ≫ j.liftCoborder)
    j.coborderRange.ι (by simpa only [Category.assoc, Scheme.Hom.liftCoborder_ι] using hV)⟩

end SourceLocal

section AffineSpaceChart

variable {Y X S : Scheme.{u}}

/-- **A chart of a smooth morphism inside relative affine space.** Near any point of a scheme `X`
smooth over `S` there are affine opens `V ⊆ S` and `U ⊆ X` with `U` lying over `V` and a regular
immersion of `U` into a finite-dimensional affine space over `V` compatible with the structure
morphisms: `U` and that affine space are both smooth over `V`, so Stacks tag 067U applies to the
immersion of Stacks tag 04II. -/
@[sga "6 VIII 1.1"]
theorem exists_affineSpace_isRegularImmersion (f : X ⟶ S) [Smooth f] (x : X) :
    ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (n : ℕ)
      (h : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme) (hh : IsImmersion h),
      letI := hh
      IsRegularImmersion h ∧
        h ≫ (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) =
          f.resLE V.1 U.1 hUV := by
  obtain ⟨V, hxV⟩ : ∃ V : S.affineOpens, f.base x ∈ V.1 := by
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  obtain ⟨U, hxU, hUV⟩ : ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ f ⁻¹ᵁ V.1 from hxV) (f ⁻¹ᵁ V.1).2
    exact ⟨⟨U, hU⟩, hxU, hUV⟩
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  obtain ⟨n, h, hh, hfac⟩ := exists_immersion_affineSpace (f.resLE V.1 U.1 hUV)
  have := hh
  have : Smooth (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) :=
    smooth_affineSpace_over _ _
  have : Smooth (h ≫ (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme)) := by
    rw [hfac]; infer_instance
  exact ⟨V, U, hxU, hUV, n, h, hh,
    Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth h
      (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme), hfac⟩

/-- **Koszul-regular immersions may be pushed into a relative affine space.** Composing a
Koszul-regular immersion into a scheme smooth over `S` with a chart of
`exists_affineSpace_isRegularImmersion` gives, near any point of the source, a Koszul-regular
immersion into a finite-dimensional affine space over an affine open of `S`. -/
@[sga "6 VIII 1.1", sga "6 VIII 1.5" "partial"]
theorem exists_affineSpace_isKoszulRegularImmersion (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i]
    [Smooth f] (hi : IsKoszulRegularImmersion i) (y : Y) :
    ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : i y ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (n : ℕ)
      (h : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme) (hh : IsImmersion h),
      letI := hh
      IsKoszulRegularImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl ≫ h) ∧
        h ≫ (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) =
          f.resLE V.1 U.1 hUV := by
  obtain ⟨V, U, hyU, hUV, n, h, hh, hreg, hfac⟩ := exists_affineSpace_isRegularImmersion f (i y)
  have := hh
  exact ⟨V, U, hyU, hUV, n, h, hh,
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp _ h
      (isKoszulRegularImmersion_resLE i hi U.1)
      (isKoszulRegularImmersion_of_isRegularImmersion h hreg), hfac⟩

/-- **`H₁`-regular immersions may be pushed into a relative affine space.** -/
theorem exists_affineSpace_isH1RegularImmersion (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i]
    [Smooth f] (hi : IsH1RegularImmersion i) (y : Y) :
    ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : i y ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (n : ℕ)
      (h : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme) (hh : IsImmersion h),
      letI := hh
      IsH1RegularImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl ≫ h) ∧
        h ≫ (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) =
          f.resLE V.1 U.1 hUV := by
  obtain ⟨V, U, hyU, hUV, n, h, hh, hreg, hfac⟩ := exists_affineSpace_isRegularImmersion f (i y)
  have := hh
  exact ⟨V, U, hyU, hUV, n, h, hh,
    Stacks.AlgebraicGeometry.isH1RegularImmersion_comp _ h
      (isH1RegularImmersion_resLE i hi U.1)
      (isH1RegularImmersion_of_isKoszulRegularImmersion h
        (isKoszulRegularImmersion_of_isRegularImmersion h hreg)), hfac⟩

end AffineSpaceChart

section SmoothTarget

variable {Y X S : Scheme.{u}}

/-- Given an immersion `k` of `W` into `𝔸ⁿ_V` whose composite `g` with the projection `π` is an
immersion, near any `w : W` there is an affine open `T ⊆ V` over which `g` is closed, and the
restriction `kT` of `k` over `T` factors through a section `σ` of `π` over `T`. -/
private theorem exists_section_of_comp_affineSpace {W V : Scheme.{u}} (n : ℕ)
    (k : W ⟶ AffineSpace (ULift.{u} (Fin n)) V) [IsImmersion k]
    (π : AffineSpace (ULift.{u} (Fin n)) V ⟶ V) (hπ : π = AffineSpace (ULift.{u} (Fin n)) V ↘ V)
    [IsImmersion (k ≫ π)] (w : W) :
    ∃ (T : V.Opens) (W' : W.Opens) (_ : w ∈ W') (ρ : (π ⁻¹ᵁ T).toScheme ⟶ T.toScheme)
      (kT : W'.toScheme ⟶ (π ⁻¹ᵁ T).toScheme) (σ : T.toScheme ⟶ (π ⁻¹ᵁ T).toScheme)
      (gT : W'.toScheme ⟶ T.toScheme) (_ : IsClosedImmersion gT),
      Smooth ρ ∧ IsImmersion kT ∧ kT ≫ (π ⁻¹ᵁ T).ι = W'.ι ≫ k ∧ σ ≫ ρ = 𝟙 T.toScheme ∧
        gT ≫ σ = kT ∧ gT ≫ T.ι = W'.ι ≫ k ≫ π := by
  classical
  subst hπ
  set π : AffineSpace (ULift.{u} (Fin n)) V ⟶ V :=
    AffineSpace (ULift.{u} (Fin n)) V ↘ V with hπ
  have hπsmooth : Smooth π := smooth_affineSpace_over _ _
  set g : W ⟶ V := k ≫ π with hg
  -- An affine open `T` of `V` over which the immersion `g` is closed.
  obtain ⟨T₁, hwT₁, hT₁⟩ := exists_isClosedImmersion_resLE_comp (𝟙 W) g w
  obtain ⟨T, hTaff, hwT, hTT₁⟩ : ∃ T : V.Opens, IsAffineOpen T ∧ g w ∈ T ∧ T ≤ T₁ := by
    obtain ⟨-, ⟨T, hT, rfl⟩, hwT, hTT₁⟩ :=
      V.isBasis_affineOpens.exists_subset_of_mem_open (show g w ∈ T₁ from hwT₁) T₁.isOpen
    exact ⟨T, hT, hwT, hTT₁⟩
  have : IsAffine T.toScheme := hTaff
  set W' : W.Opens := g ⁻¹ᵁ T with hW'
  have hwW' : w ∈ W' := hwT
  set gT : W'.toScheme ⟶ T.toScheme := g.resLE T W' le_rfl with hgT
  have hgTι : gT ≫ T.ι = W'.ι ≫ g := Scheme.Hom.resLE_comp_ι g le_rfl
  have hgTclosed : IsClosedImmersion gT := (hT₁ T hTT₁).1
  -- The chart, restricted over `T`.
  have hW'le : W' ≤ k ⁻¹ᵁ (π ⁻¹ᵁ T) := by rw [← Scheme.Hom.comp_preimage, ← hg]
  set P : Scheme.{u} := (π ⁻¹ᵁ T).toScheme with hP
  set ρ : P ⟶ T.toScheme := π.resLE T (π ⁻¹ᵁ T) le_rfl with hρ
  have hρι : ρ ≫ T.ι = (π ⁻¹ᵁ T).ι ≫ π := Scheme.Hom.resLE_comp_ι π le_rfl
  have hρsmooth : Smooth ρ := by rw [hρ]; delta Scheme.Hom.resLE; infer_instance
  set kT : W'.toScheme ⟶ P := k.resLE (π ⁻¹ᵁ T) W' hW'le with hkT
  have hkTι : kT ≫ (π ⁻¹ᵁ T).ι = W'.ι ≫ k := Scheme.Hom.resLE_comp_ι k hW'le
  have hkTcompim : IsImmersion (kT ≫ (π ⁻¹ᵁ T).ι) := by rw [hkTι]; infer_instance
  have hkTim : IsImmersion kT := IsImmersion.of_comp kT (π ⁻¹ᵁ T).ι
  -- The section of `π` over `T` cut out by lifts of the coordinates of the chart.
  obtain ⟨-, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine gT
  choose v hv using fun l : ULift.{u} (Fin n) =>
    hsurj ((W'.ι ≫ k).appTop (AffineSpace.coord V l))
  set σ₀ : T.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V :=
    AffineSpace.homOfVector T.ι v with hσ₀
  have hσ₀π : σ₀ ≫ π = T.ι := AffineSpace.homOfVector_over _ _
  have hgσ₀ : gT ≫ σ₀ = W'.ι ≫ k := by
    refine AffineSpace.hom_ext ?_ fun l => ?_
    · rw [← hπ, Category.assoc gT σ₀ π, hσ₀π, Category.assoc W'.ι k π, ← hg]
      exact hgTι
    · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
      change gT.appTop (σ₀.appTop (AffineSpace.coord V l)) = _
      rw [hσ₀, AffineSpace.homOfVector_appTop_coord, hv l, Scheme.Hom.comp_appTop]
  have hrange : Set.range σ₀.base ⊆ Set.range ((π ⁻¹ᵁ T).ι).base := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨t, rfl⟩
    change π (σ₀ t) ∈ T
    rw [← Scheme.Hom.comp_apply, hσ₀π]
    exact t.2
  set σ : T.toScheme ⟶ P := IsOpenImmersion.lift ((π ⁻¹ᵁ T).ι) σ₀ hrange with hσ
  have hσι : σ ≫ (π ⁻¹ᵁ T).ι = σ₀ := IsOpenImmersion.lift_fac _ _ hrange
  have hσρ : σ ≫ ρ = 𝟙 T.toScheme := by
    refine (cancel_mono T.ι).mp ?_
    rw [Category.assoc, hρι, ← Category.assoc, hσι, hσ₀π, Category.id_comp]
  have hgσ : gT ≫ σ = kT := by
    refine (cancel_mono (π ⁻¹ᵁ T).ι).mp ?_
    rw [Category.assoc, hσι, hgσ₀, hkTι]
  exact ⟨T, W', hwW', ρ, kT, σ, gT, hgTclosed, hρsmooth, hkTim, hkTι, hσρ, hgσ, hgTι⟩

/-- **An immersion into a retracted scheme over an affine base.** Let `g : W ⟶ V` be a closed
immersion, let `ρ : P ⟶ V` be smooth and let `σ : V ⟶ P` be a section of `ρ` through which `g`
factors by a Koszul-regular immersion. Then `g` is Koszul-regular: this is Stacks tag 068Z for
the retracted immersion `σ`, whose conormal sequence needs no further argument. -/
@[sga "6 VIII 1.3" "special case"]
private theorem isKoszulRegularImmersion_of_section {V W P : Scheme.{u}} (g : W ⟶ V)
    [IsImmersion g] (ρ : P ⟶ V) [Smooth ρ] (k : W ⟶ P) [IsImmersion k]
    (hk : IsKoszulRegularImmersion k) (σ : V ⟶ P) (hσρ : σ ≫ ρ = 𝟙 V) (hσ : g ≫ σ = k) :
    IsKoszulRegularImmersion g := by
  have hσim : IsImmersion σ := Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id σ ρ hσρ
  have hσreg : IsKoszulRegularImmersion σ :=
    isKoszulRegularImmersion_of_isRegularImmersion σ
      (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section ρ σ hσρ)
  have hgσim : IsImmersion (g ≫ σ) := by rw [hσ]; infer_instance
  exact Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_retraction g σ ρ hσρ hσreg
    (isKoszulRegularImmersion_of_eq hσ.symm hk)

/-- Koszul-regularity descends from a relative affine space to its base. -/
private theorem isKoszulRegularImmersion_comp_affineSpace {W V : Scheme.{u}} (n : ℕ)
    (k : W ⟶ AffineSpace (ULift.{u} (Fin n)) V) [IsImmersion k]
    [IsImmersion (k ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V))]
    (hk : IsKoszulRegularImmersion k) :
    IsKoszulRegularImmersion (k ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V)) := by
  refine isKoszulRegularImmersion_of_forall_exists_opens _ fun w => ?_
  obtain ⟨T, W', hwW', ρ, kT, σ, gT, hgT, hρ, hkT, hkTι, hσρ, hgσ, hgTι⟩ :=
    exists_section_of_comp_affineSpace n k _ rfl w
  exact ⟨W', hwW', isKoszulRegularImmersion_of_eq hgTι
    (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp gT T.ι
      (isKoszulRegularImmersion_of_section gT ρ kT
        (isKoszulRegularImmersion_of_comp_of_smooth kT _
          (isKoszulRegularImmersion_of_eq hkTι.symm
            (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp W'.ι k
              (isKoszulRegularImmersion_of_isOpenImmersion W'.ι) hk))) σ hσρ hgσ)
      (isKoszulRegularImmersion_of_isOpenImmersion T.ι))⟩


/-- **Stacks tag 0693 for Koszul-regular immersions.** In a commutative triangle `Y ⟶ X ⟶ S` with
`X ⟶ S` smooth and both `Y ⟶ X` and `Y ⟶ S` immersions, the composite `Y ⟶ S` of a Koszul-regular
immersion `Y ⟶ X` is a Koszul-regular immersion.

Koszul-regularity is local on the source, and near a point of `Y` the immersion into `X` is pushed
into a relative affine space `𝔸ⁿ_V` over an affine open `V ⊆ S`.  Shrinking `V` to an affine open
`T` over which `Y` is closed, the lifted coordinates of that chart define a section `σ` of
`𝔸ⁿ_V ⟶ V` over `T` through which the chart factors, and Stacks tag 068Z for the retracted
immersion `σ` descends Koszul-regularity to `Y ⟶ T`. -/
@[stacks 0693 "koszul_regular"]
theorem isKoszulRegularImmersion_comp_of_smooth (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i]
    [IsImmersion (i ≫ f)] [Smooth f] (hi : IsKoszulRegularImmersion i) :
    IsKoszulRegularImmersion (i ≫ f) := by
  refine isKoszulRegularImmersion_of_forall_exists_opens (i ≫ f) fun y => ?_
  obtain ⟨V, U, hyU, hUV, n, h, hh, hreg, hfac⟩ :=
    exists_affineSpace_isKoszulRegularImmersion i f hi y
  have := hh
  have : IsAffine V.1.toScheme := V.2
  set π : AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ⟶ V.1.toScheme :=
    AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme with hπ
  have hπsmooth : Smooth π := smooth_affineSpace_over _ _
  set W₀ : Y.Opens := i ⁻¹ᵁ U.1 with hW₀
  set k₀ : W₀.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme :=
    i.resLE U.1 W₀ le_rfl ≫ h with hk₀
  set g₀ : W₀.toScheme ⟶ V.1.toScheme := k₀ ≫ π with hg₀
  have hg₀ι : g₀ ≫ V.1.ι = W₀.ι ≫ (i ≫ f) := by
    rw [hg₀, hk₀, Category.assoc, Category.assoc, ← Category.assoc h π V.1.ι, hfac,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have hg₀im : IsImmersion g₀ := by
    have : IsImmersion (g₀ ≫ V.1.ι) := by rw [hg₀ι]; infer_instance
    exact IsImmersion.of_comp g₀ V.1.ι
  exact ⟨W₀, hyU, isKoszulRegularImmersion_of_eq hg₀ι
    (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp g₀ V.1.ι
      (isKoszulRegularImmersion_comp_affineSpace n k₀ hreg)
      (isKoszulRegularImmersion_of_isOpenImmersion V.1.ι))⟩

private theorem isH1RegularImmersion_of_section {V W P : Scheme.{u}} (g : W ⟶ V)
    [IsImmersion g] (ρ : P ⟶ V) [Smooth ρ] (k : W ⟶ P) [IsImmersion k]
    (hk : IsH1RegularImmersion k) (σ : V ⟶ P) (hσρ : σ ≫ ρ = 𝟙 V) (hσ : g ≫ σ = k) :
    IsH1RegularImmersion g := by
  have hσim : IsImmersion σ := Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id σ ρ hσρ
  have hσreg : IsH1RegularImmersion σ :=
    isH1RegularImmersion_of_isKoszulRegularImmersion σ
      (isKoszulRegularImmersion_of_isRegularImmersion σ
        (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section ρ σ hσρ))
  have hgσim : IsImmersion (g ≫ σ) := by rw [hσ]; infer_instance
  exact Stacks.AlgebraicGeometry.isH1RegularImmersion_of_comp_of_retraction g σ ρ hσρ hσreg
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.isH1RegularImmersion_of_eq hσ.symm hk)

/-- `H₁`-regularity descends from a relative affine space to its base. -/
private theorem isH1RegularImmersion_comp_affineSpace {W V : Scheme.{u}} (n : ℕ)
    (k : W ⟶ AffineSpace (ULift.{u} (Fin n)) V) [IsImmersion k]
    [IsImmersion (k ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V))]
    (hk : IsH1RegularImmersion k) :
    IsH1RegularImmersion (k ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V)) := by
  refine isH1RegularImmersion_of_forall_exists_opens _ fun w => ?_
  obtain ⟨T, W', hwW', ρ, kT, σ, gT, hgT, hρ, hkT, hkTι, hσρ, hgσ, hgTι⟩ :=
    exists_section_of_comp_affineSpace n k _ rfl w
  exact ⟨W', hwW', isH1RegularImmersion_of_eq hgTι
    (Stacks.AlgebraicGeometry.isH1RegularImmersion_comp gT T.ι
      (isH1RegularImmersion_of_section gT ρ kT
        (isH1RegularImmersion_of_comp_of_smooth kT _
          (isH1RegularImmersion_of_eq hkTι.symm
            (Stacks.AlgebraicGeometry.isH1RegularImmersion_comp W'.ι k
              (isH1RegularImmersion_of_isOpenImmersion W'.ι) hk))) σ hσρ hgσ)
      (isH1RegularImmersion_of_isOpenImmersion T.ι))⟩


/-- **Stacks tag 0693 for `H₁`-regular immersions.** In a commutative triangle `Y ⟶ X ⟶ S` with
`X ⟶ S` smooth and both `Y ⟶ X` and `Y ⟶ S` immersions, the composite `Y ⟶ S` of an `H₁`-regular
immersion `Y ⟶ X` is an `H₁`-regular immersion.

`H₁`-regularity is local on the source, and near a point of `Y` the immersion into `X` is pushed
into a relative affine space `𝔸ⁿ_V` over an affine open `V ⊆ S`.  Shrinking `V` to an affine open
`T` over which `Y` is closed, the lifted coordinates of that chart define a section `σ` of
`𝔸ⁿ_V ⟶ V` over `T` through which the chart factors, and Stacks tag 068Z for the retracted
immersion `σ` descends `H₁`-regularity to `Y ⟶ T`. -/
@[stacks 0693 "h1_regular"]
theorem isH1RegularImmersion_comp_of_smooth (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i]
    [IsImmersion (i ≫ f)] [Smooth f] (hi : IsH1RegularImmersion i) :
    IsH1RegularImmersion (i ≫ f) := by
  classical
  refine isH1RegularImmersion_of_forall_exists_opens (i ≫ f) fun y => ?_
  obtain ⟨V, U, hyU, hUV, n, h, hh, hreg, hfac⟩ :=
    exists_affineSpace_isH1RegularImmersion i f hi y
  have := hh
  have : IsAffine V.1.toScheme := V.2
  set π : AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ⟶ V.1.toScheme :=
    AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme with hπ
  have hπsmooth : Smooth π := smooth_affineSpace_over _ _
  set W₀ : Y.Opens := i ⁻¹ᵁ U.1 with hW₀
  set k₀ : W₀.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme :=
    i.resLE U.1 W₀ le_rfl ≫ h with hk₀
  set g₀ : W₀.toScheme ⟶ V.1.toScheme := k₀ ≫ π with hg₀
  have hg₀ι : g₀ ≫ V.1.ι = W₀.ι ≫ (i ≫ f) := by
    rw [hg₀, hk₀, Category.assoc, Category.assoc, ← Category.assoc h π V.1.ι, hfac,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have hg₀im : IsImmersion g₀ := by
    have : IsImmersion (g₀ ≫ V.1.ι) := by rw [hg₀ι]; infer_instance
    exact IsImmersion.of_comp g₀ V.1.ι
  exact ⟨W₀, hyU, isH1RegularImmersion_of_eq hg₀ι
    (Stacks.AlgebraicGeometry.isH1RegularImmersion_comp g₀ V.1.ι
      (isH1RegularImmersion_comp_affineSpace n k₀ hreg)
      (isH1RegularImmersion_of_isOpenImmersion V.1.ι))⟩

/-- Quasi-regularity transports along an equality of immersions. -/
theorem isQuasiRegularImmersion_of_eq_hom {A B : Scheme.{u}} {a b : A ⟶ B}
    [IsImmersion a] [IsImmersion b] (h : a = b) (ha : IsQuasiRegularImmersion a) :
    IsQuasiRegularImmersion b := by
  subst h; exact ha

/-- Composing a quasi-regular closed immersion with the inclusion of an open of the target gives
a quasi-regular immersion. -/
theorem isQuasiRegularImmersion_comp_opensι {V W : Scheme.{u}} (T : V.Opens)
    (g : W ⟶ T.toScheme) [IsClosedImmersion g] (hg : IsQuasiRegularImmersion g) :
    IsQuasiRegularImmersion (g ≫ T.ι) :=
  (isQuasiRegularImmersion_iff_of_open (g ≫ T.ι) T g rfl).mpr
    (isQuasiRegularIdealSheaf_definingIdealOfHom g hg)

/-- **An immersion into a retracted scheme over an affine base.** Let `g : W ⟶ V` be an
immersion, let `ρ : P ⟶ V` be smooth and let `σ : V ⟶ P` be a section of `ρ` through which `g`
factors by a quasi-regular immersion. Then `g` is quasi-regular: this is Stacks tag 068Z for the
retracted immersion `σ`, whose conormal sequence needs no further argument. -/
private theorem isQuasiRegularImmersion_of_section {V W P : Scheme.{u}} (g : W ⟶ V)
    [IsImmersion g] (ρ : P ⟶ V) [Smooth ρ] (k : W ⟶ P) [IsImmersion k]
    (hk : IsQuasiRegularImmersion k) (σ : V ⟶ P) (hσρ : σ ≫ ρ = 𝟙 V) (hσ : g ≫ σ = k) :
    IsQuasiRegularImmersion g := by
  have hσim : IsImmersion σ := Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id σ ρ hσρ
  have hσreg : IsQuasiRegularImmersion σ :=
    isQuasiRegularImmersion_of_isH1RegularImmersion σ
      (isH1RegularImmersion_of_isKoszulRegularImmersion σ
        (isKoszulRegularImmersion_of_isRegularImmersion σ
          (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section ρ σ hσρ)))
  have hgσim : IsImmersion (g ≫ σ) := by rw [hσ]; infer_instance
  exact Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_comp_of_retraction g σ ρ hσρ hσreg
    (isQuasiRegularImmersion_of_eq_hom hσ.symm hk)

/-- **Quasi-regularity descends from a relative affine space to its base.** If an immersion `k`
of `W` into the affine space `𝔸ⁿ_V` is quasi-regular and its composite with the projection to `V`
is an immersion, then that composite is a quasi-regular immersion.

Near a point of `W` an affine open `T ⊆ V` over which the composite is closed carries a section
`σ` of `𝔸ⁿ_V ⟶ V` cut out by lifts of the coordinates of `k`, through which the restriction of
`k` factors, and Stacks tag 068Z for the retracted immersion `σ` descends quasi-regularity. -/
theorem isQuasiRegularImmersion_comp_affineSpace {W V : Scheme.{u}} (n : ℕ)
    (k : W ⟶ AffineSpace (ULift.{u} (Fin n)) V) [IsImmersion k]
    [IsImmersion (k ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V))]
    (hk : IsQuasiRegularImmersion k) :
    IsQuasiRegularImmersion (k ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V)) := by
  refine isQuasiRegularImmersion_of_forall_exists_opens _ fun w => ?_
  obtain ⟨T, W', hwW', ρ, kT, σ, gT, hgT, hρ, hkT, hkTι, hσρ, hgσ, hgTι⟩ :=
    exists_section_of_comp_affineSpace n k _ rfl w
  exact ⟨W', hwW', isQuasiRegularImmersion_of_eq_hom hgTι
    (isQuasiRegularImmersion_comp_opensι T gT
      (isQuasiRegularImmersion_of_section gT ρ kT
        (isQuasiRegularImmersion_of_comp_of_smooth kT _
          (isQuasiRegularImmersion_of_eq_hom hkTι.symm
            (Stacks.AlgebraicGeometry.isQuasiRegularImmersion_comp_of_isH1RegularImmersion
              W'.ι k (isH1RegularImmersion_of_isOpenImmersion W'.ι) hk))) σ hσρ hgσ))⟩

end SmoothTarget

end Stacks.AlgebraicGeometry.RegularIdealSheaf


end
