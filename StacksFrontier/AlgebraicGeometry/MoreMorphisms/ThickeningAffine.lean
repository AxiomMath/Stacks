module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Affineness of a thickening

[Stacks Project, Tag 06AD] says that any thickening of an affine scheme is affine. This file
reduces that statement to a single cohomological assertion: for a thickening `i : X ⟶ X'` with
`X` affine, the ambient scheme `X'` is affine **if and only if** the ring map on global sections
`i.appTop : Γ(X', ⊤) ⟶ Γ(X, ⊤)` is surjective.

## Main results

* `Stacks.Thickenings.isAffine_of_isThickening_of_surjective_appTop`: a thickening of an affine
  scheme whose map on global sections is surjective has affine ambient scheme.
* `Stacks.Thickenings.IsThickening.isAffine_iff_surjective_appTop`: the resulting equivalence,
  which is the precise remaining content of [Stacks Project, Tag 06AD].
* `Stacks.Thickenings.IsThickening.exists_isAffineOpen_preimage_eq_basicOpen`: every point of the
  ambient scheme of a thickening of an affine scheme has an affine open neighbourhood whose
  preimage is a basic open of the closed subscheme. This is the standard-cover input of
  `Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover`, and it needs no
  surjectivity hypothesis.
* `Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop_of_compactSpace`: a global
  section of the ambient scheme that dies on the closed subscheme is nilpotent.

## Implementation notes

The affineness criterion used is `AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`
([Stacks Project, Tag 01QF]): a scheme is affine as soon as some set of global sections
generating the unit ideal has affine basic opens. The set taken here is *all* of
`{b | IsAffineOpen (X'.basicOpen b)}`, so the affineness half of the criterion is true by
definition and the whole work is to see that this set generates the unit ideal.

Two facts about a thickening do that. First, a thickening is surjective on points, so an
inclusion of opens of `X'` may be tested after taking preimages
(`Stacks.Thickenings.IsThickening.le_of_preimage_le`); together with the basis of basic opens of
the affine scheme `X` and the surjectivity hypothesis this produces, for every point of `X'`, a
global section `b` whose basic open is an affine neighbourhood of that point. Hence the chosen
set covers `X'`, and its image under `i.appTop` generates the unit ideal of `Γ(X, ⊤)` because `X`
is affine.

Second, the kernel of `i.appTop` is a nil ideal: the basic open of a section in the kernel has
empty preimage, hence is empty, and a global section of a quasi-compact scheme with empty basic
open is nilpotent. Surjectivity of `i.appTop` turns the first fact into
`Ideal.span s ⊔ RingHom.ker i.appTop.hom = ⊤` by
`Ideal.comap_map_of_surjective`, and the second then removes the kernel summand because
`1 - ε` is a unit for `ε` nilpotent.

Only the kernel being nil uses that `X'` is quasi-compact, which holds because a thickening is a
homeomorphism on points. That generalizes
`Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop` of
`StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout`, which assumes `X'` affine; the two are
kept apart because this module must stay upstream of the pushout material that consumes
[Stacks Project, Tag 06AD].

**The hypothesis carried by [Stacks Project, Tag 06AD].** The `@[stacks 06AD]` attribute is
attached to `Stacks.Thickenings.isAffine_of_isThickening_of_surjective_appTop`, whose single
extra hypothesis beyond the tag is the surjectivity of `i.appTop`, which is the
vanishing of the first cohomology of the kernel ideal sheaf of `i` on `X'`. The source obtains it
as a special case of [Stacks Project, Tag 05YU]; the finite-order case is Serre's criterion. The
algebraic engine for a direct proof is available in this repository as
`Stacks.RingTheory.CechAcyclicity.cech_exact` and
`Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover`
([Stacks Project, Tag 01X9]), applied to the standard cover produced by
`Stacks.Thickenings.IsThickening.exists_isAffineOpen_preimage_eq_basicOpen`; what is still absent
is the presentation of the kernel ideal sheaf as a quasi-coherent module on the *closed
subscheme* `X`, which exists only when the thickening is of first order, plus the reduction of a
general thickening to a finite-order one.

## References

* [Stacks Project, Tag 01QF](https://stacks.math.columbia.edu/tag/01QF)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}}

/-- **A basic open contained in an affine open is affine.** It is the basic open of the affine
open at the restricted section. -/
theorem isAffineOpen_basicOpen_of_le {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V)
    (b : Γ(Z, (⊤ : Z.Opens))) (hb : Z.basicOpen b ≤ V) : IsAffineOpen (Z.basicOpen b) := by
  have h := hV.basicOpen (Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op b)
  rwa [Scheme.basicOpen_res, inf_eq_right.mpr hb] at h

/-- **An inclusion of opens of the ambient scheme of a thickening may be tested on preimages**,
because a thickening is surjective on points. -/
theorem IsThickening.le_of_preimage_le {i : X ⟶ X'} (hi : IsThickening i) {U V : X'.Opens}
    (h : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ V) : U ≤ V := by
  intro x hx
  obtain ⟨y, rfl⟩ := hi.2 x
  exact h hx

/-- **The ambient scheme of a thickening of a quasi-compact scheme is quasi-compact**, since a
thickening is a homeomorphism on points. -/
theorem IsThickening.compactSpace [CompactSpace X] {i : X ⟶ X'} (hi : IsThickening i) :
    CompactSpace X' :=
  have := hi.1
  (IsHomeomorph.homeomorph _
    (isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨i.isClosedEmbedding.isEmbedding, hi.2⟩)).compactSpace

/-- **The ideal of a thickening with quasi-compact ambient scheme is nil.**  A global section of
`X'` that dies on `X` has empty basic open, because its preimage is empty and a thickening is
surjective on points, and a global section of a quasi-compact scheme with empty basic open is
nilpotent.

This is `Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop` with `X'` merely
quasi-compact instead of affine. -/
theorem IsThickening.isNilpotent_of_mem_ker_appTop_of_compactSpace [CompactSpace X']
    {i : X ⟶ X'} (hi : IsThickening i) {b : Γ(X', (⊤ : X'.Opens))}
    (hb : b ∈ RingHom.ker i.appTop.hom) : IsNilpotent b := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot]
  refine le_antisymm (hi.le_of_preimage_le (V := ⊥) ?_) bot_le
  rw [Scheme.preimage_basicOpen_top]
  have h : i.appTop b = 0 := hb
  rw [h]
  simp

/-- Every point of the ambient scheme of a thickening of an affine scheme lies in an affine open
`W` of `X'` whose preimage contains a basic open of `X` containing a point over it. -/
private theorem exists_isAffineOpen_basicOpen_le_preimage [IsAffine X] {i : X ⟶ X'}
    (hi : IsThickening i) (x : X') :
    ∃ (W : X'.Opens) (a : Γ(X, (⊤ : X.Opens))) (y : X),
      IsAffineOpen W ∧ x ∈ W ∧ X.basicOpen a ≤ i ⁻¹ᵁ W ∧ y ∈ X.basicOpen a ∧ i y = x := by
  obtain ⟨-, ⟨W, hWaff, rfl⟩, hxW, -⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨y, hy⟩ := hi.2 x
  have hyW : y ∈ i ⁻¹ᵁ W := by simpa [hy] using hxW
  obtain ⟨a, haW, hya⟩ := (isAffineOpen_top X).exists_basicOpen_le
    (V := i ⁻¹ᵁ W) ⟨y, hyW⟩ (Opens.mem_top y)
  exact ⟨W, a, y, hWaff, hxW, haW, hya, hy⟩

/-- **A thickening of an affine scheme has a standard cover.**  Every point of the ambient scheme
of a thickening `i : X ⟶ X'` with `X` affine lies in an affine open of `X'` whose preimage is a
basic open of `X`.  No surjectivity hypothesis on `i.appTop` is needed: the section cutting out
the basic open is lifted only over one affine open, where a closed immersion is surjective on
sections. -/
theorem IsThickening.exists_isAffineOpen_preimage_eq_basicOpen [IsAffine X] {i : X ⟶ X'}
    (hi : IsThickening i) (x : X') :
    ∃ (V : X'.Opens) (a : Γ(X, (⊤ : X.Opens))),
      IsAffineOpen V ∧ x ∈ V ∧ i ⁻¹ᵁ V = X.basicOpen a := by
  have := hi.1
  obtain ⟨W, a, y, hWaff, hxW, haW, hya, hy⟩ := exists_isAffineOpen_basicOpen_le_preimage hi x
  obtain ⟨b, hb⟩ :=
    i.app_surjective W hWaff (X.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op a)
  have hpre : i ⁻¹ᵁ X'.basicOpen b = X.basicOpen a := by
    rw [Scheme.preimage_basicOpen, hb, Scheme.basicOpen_res, inf_eq_right.mpr haW]
  refine ⟨X'.basicOpen b, a, hWaff.basicOpen b, ?_, hpre⟩
  have hyb : i y ∈ X'.basicOpen b := hpre.ge hya
  rwa [hy] at hyb

/-- **The affine basic opens of the ambient scheme of a thickening cover it**, when the closed
subscheme is affine and the map on global sections is surjective. -/
theorem IsThickening.top_le_iSup_basicOpen [IsAffine X] {i : X ⟶ X'} (hi : IsThickening i)
    (hsurj : Function.Surjective i.appTop.hom) :
    (⊤ : X'.Opens) ≤ ⨆ b : {b : Γ(X', (⊤ : X'.Opens)) | IsAffineOpen (X'.basicOpen b)},
      X'.basicOpen (b : Γ(X', (⊤ : X'.Opens))) := by
  intro x _
  obtain ⟨W, a, y, hWaff, hxW, haW, hya, hy⟩ := exists_isAffineOpen_basicOpen_le_preimage hi x
  obtain ⟨b, hb⟩ := hsurj a
  have hpre : i ⁻¹ᵁ X'.basicOpen b = X.basicOpen a := by
    rw [Scheme.preimage_basicOpen_top]
    exact congrArg X.basicOpen hb
  refine Opens.mem_iSup.mpr
    ⟨⟨b, isAffineOpen_basicOpen_of_le hWaff b (hi.le_of_preimage_le (hpre.trans_le haW))⟩, ?_⟩
  have hyb : i y ∈ X'.basicOpen b := hpre.ge hya
  rwa [hy] at hyb

/-- **A thickening of an affine scheme whose map on global sections is surjective has affine
ambient scheme.**  This is [Stacks Project, Tag 06AD] with its cohomological content — the
surjectivity of `i.appTop` — as the explicit hypothesis `hsurj`, which is the only thing assumed:
everything else in the tag is proved here, through the affineness criterion of
[Stacks Project, Tag 01QF].  The hypothesis is not needed for the tag itself: it is dropped in
`Stacks.Thickenings.isAffine_of_isThickening`, which proves Tag 06AD outright from
[Stacks Project, Tag 01ZT]. -/
@[stacks 06AD]
theorem isAffine_of_isThickening_of_surjective_appTop [IsAffine X] {i : X ⟶ X'}
    (hi : IsThickening i) (hsurj : Function.Surjective i.appTop.hom) : IsAffine X' := by
  have := hi.compactSpace
  refine isAffine_of_isAffineOpen_basicOpen
    {b : Γ(X', (⊤ : X'.Opens)) | IsAffineOpen (X'.basicOpen b)} ?_ fun b hb ↦ hb
  have hcov := hi.top_le_iSup_basicOpen hsurj
  have himg : Ideal.span (i.appTop.hom ''
      {b : Γ(X', (⊤ : X'.Opens)) | IsAffineOpen (X'.basicOpen b)}) = ⊤ := by
    rw [← (isAffineOpen_top X).self_le_iSup_basicOpen_iff]
    intro y _
    obtain ⟨b, hyb⟩ := Opens.mem_iSup.mp (hcov (show i y ∈ (⊤ : X'.Opens) from trivial))
    refine Opens.mem_iSup.mpr ⟨⟨i.appTop.hom (b : Γ(X', (⊤ : X'.Opens))), b, b.2, rfl⟩, ?_⟩
    show y ∈ X.basicOpen (i.appTop (b : Γ(X', (⊤ : X'.Opens))))
    rw [← Scheme.preimage_basicOpen_top]
    exact hyb
  have hsup : Ideal.span {b : Γ(X', (⊤ : X'.Opens)) | IsAffineOpen (X'.basicOpen b)} ⊔
      RingHom.ker i.appTop.hom = ⊤ := by
    rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_map_of_surjective _ hsurj, Ideal.map_span, himg,
      Ideal.comap_top]
  obtain ⟨u, hu, e, he, hue⟩ :=
    Submodule.mem_sup.mp (hsup ▸ (Submodule.mem_top :
      (1 : Γ(X', (⊤ : X'.Opens))) ∈ (⊤ : Ideal Γ(X', (⊤ : X'.Opens)))))
  refine Ideal.eq_top_of_isUnit_mem _ hu ?_
  rw [eq_sub_of_add_eq hue]
  exact (hi.isNilpotent_of_mem_ker_appTop_of_compactSpace he).isUnit_one_sub

/-- **A thickening of an affine scheme is affine exactly when its map on global sections is
surjective.**  The forward direction is that a closed immersion with affine target is surjective
on sections; the backward direction is
`Stacks.Thickenings.isAffine_of_isThickening_of_surjective_appTop`.  So this equivalence isolates
the whole remaining content of [Stacks Project, Tag 06AD]. -/
theorem IsThickening.isAffine_iff_surjective_appTop [IsAffine X] {i : X ⟶ X'}
    (hi : IsThickening i) : IsAffine X' ↔ Function.Surjective i.appTop.hom := by
  have := hi.1
  refine ⟨fun _ ↦ (IsClosedImmersion.isAffine_surjective_of_isAffine i).2, fun h ↦ ?_⟩
  exact isAffine_of_isThickening_of_surjective_appTop hi h

end Stacks.Thickenings

end
