module

public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.Powers
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Consumers
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion

/-!
# Part (3) of Stacks Tag 01ZY: the ample case

A finite subset of a scheme carrying an ample invertible `𝒪_X`-module lies in a single affine
open. This file proves it, with no hypothesis beyond ampleness, and attaches the part (3) label of
Stacks Tag 01ZY.

## The route, and how it differs from the source

The source reduces the ample case to its fourth case: by Stacks Tag 01Q3 an ample `L` presents `X`
as an open subscheme of some `Proj S`, and then part (4) applies. That reduction is not available
here — nothing in this repository builds the morphism to `Proj Γ_*(X, L)` — and this proof does
not use it, nor `Proj`, nor any clause of Tag 01Q3. It goes through part (1) instead:

1. **One `X_a` around the whole finite set.** `Stacks.AmpleFiniteAvoidance`'s graded prime
   avoidance gives a homogeneous `a ∈ Γ_*(X, L)` of degree `d ≥ 1` with `E ⊆ X_a`. This is the
   only place ampleness is used globally, and it needs no hypothesis beyond it.
2. **`X_a` is quasi-affine** (`Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen`). It is
   quasi-compact by Stacks Tag 01PV (`isCompact_nonvanishingOpen`), and Mathlib's criterion
   `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen` asks for an affine basic
   open of a *global function on `X_a`* around each of its points. That is where the two
   ingredients of the sibling files meet: ampleness puts an affine `X_b` through the point; raising
   `a` and `b` to the common degree `d n` (`exists_common_degree`) puts them in one module; the
   ratio `b^d / a^n` is a function on `X_a` whose basic open is `X_a ⊓ X_b`
   (`exists_basicOpen_eq_inf`); and that intersection is affine by Stacks Tag 01PV
   (`isAffineOpen_inf_nvOpen`).
3. **Part (1) finishes.** `Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine`
   — part (1) in its prescribed-open form — produces an affine open of the scheme `X_a`
   containing `E`, and its image in `X` is an affine open of `X`, an open immersion carrying
   affineness both ways.

So the two inputs are **Stacks Tag 01PV** (used twice: for quasi-compactness of `X_a` and
for affineness of `X_a ⊓ X_b`) and **part (1) of Stacks Tag 01ZY**. The
obstruction recorded in
`StacksFrontier/AlgebraicGeometry/NonvanishingAffineIntersection/Consumers.lean` — that
`isAffineOpen_of_le_affineOpen` needs `X_a` inside *one* affine open while ampleness supplies only
a finite cover — is real and is not circumvented: `X_a` genuinely need not be affine (take `L`
trivial on a quasi-affine `X` and `a = 1`, where `X_a = X`). What dissolves is the conclusion drawn
from it. Nothing asks `X_a` to be affine; it only has to be *quasi-affine*, and part (1) then
shrinks it around `E`.

## Main results

* `Stacks.AmpleAffineAvoidance.exists_affine_basicOpen_mem`: an affine basic open of a function on
  `X_a` around each of its points.
* `Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen`: **`X_a` is quasi-affine**, for `L` ample and
  `a` homogeneous of positive degree.
* `Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_le_of_ample`: part (3) with the
  affine open confined to a prescribed open containing `E`. This is the form the source's own proof
  of Stacks Tag 09NV calls part (3) for.
* `Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample`: **part (3) of Stacks
  Tag 01ZY**, carrying the label.
* `Stacks.AmpleAffineAvoidance.exists_affine_nvOpen_containing_finite_le_of_ample`: **Stacks Tag
  09NV reduced to a single named input**, clause (3) of Stacks Tag 01Q3.

## Which definition of ampleness

`Stacks.Ample.IsAmple` of
`StacksFrontier/AlgebraicGeometry/AmpleWire/Basic.lean`, over the integer tensor powers
`Stacks.Ample.tensorPowModule`. There are two definitions in the repository carrying the Tag 01PS
attribute; the other, `AlgebraicGeometry.Scheme.Modules.IsAmple` of
`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean`, is stated over a different construction of the
tensor powers and is not connected to this one by any comparison in the library. The choice is forced:
every ample result in the library — Tag 01QE, the clauses of Tag 01Q3 in
`StacksFrontier/AlgebraicGeometry/AmpleTheory/Basic.lean`, the graded avoidance of
`Stacks.AmpleFiniteAvoidance` — is stated with this one.
`Stacks.Ample.isAmple_iff_isAmpleForPowers` proves that the predicate does not depend on which
construction of the tensor powers is used, so the choice privileges no construction.

## References

* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)

## What is not done

**Stacks Tag 09NV is not proved here, and no 09NV label is attached by this file.** It is proved
elsewhere in the repository, as
`Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite_sections`
(`../AmpleFiniteAffineNonvanishing/Basic.lean`), with ampleness as its only hypothesis, and that
proof calls `exists_affineOpen_containing_finite_le_of_ample` below for its opening step.
What this file leaves as a hypothesis is one named input:
`Stacks.AmpleTheory.IsBasisNonvanishing X L`, clause (3) of Stacks Tag 01Q3 — the opens `X_s`, for
`s` a global section of a positive tensor power, form a basis for the topology.
`exists_affine_nvOpen_containing_finite_le_of_ample` is Tag 09NV on that hypothesis and nothing
else; it improves on
`Stacks.NonvanishingAffineIntersection.exists_affine_nvOpen_containing_finite_le`, which also had
to assume an affine open between `E` and `W`, by supplying that open from part (3). Clause (3)
itself is reduced in `StacksFrontier/AlgebraicGeometry/AmplePullback/Basic.lean` to
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing`, which is Stacks Tag 01PW — a section of `𝒪_X`
over an affine `X_s` extends to a global section of a tensor power after multiplication by a power
of `s`. That hypothesis is no longer a gap:
`Stacks.SectionExtension.isBasisNonvanishing_of_isAmple`
(`../SectionExtension/AmpleConsumers.lean`) proves it from ampleness alone, by way of
`Stacks.SectionExtension.isSectionRatio_of_isAmple`, the surjectivity half of Stacks Tag 01PW for
an ample module. Nothing below applies it, which is why the hypothesis is still written out here.

**No clause of Stacks Tag 01Q3 is proved here.** In particular clause (1) implies clause (2) —
the immersion into `Proj Γ_*(X, L)` that the source's proof of this very part goes through — is
untouched, nowhere in the repository, and nothing here is a statement about `Proj`.

**Nothing is proved about part (4)**, which is proved separately as
`Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_proj`
(`../AmpleCluster/ProjImmersion.lean`), and this file does not use it: the two labels of Stacks
Tag 01ZY are proved by independent routes, part (4) through part (2) and part (3) through part
(1).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.GradedSections Stacks.SectionProduct Stacks.AmpleFiniteAvoidance

universe u

namespace Stacks.AmpleAffineAvoidance

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- Two homogeneous elements with the same nonvanishing locus have the same nonvanishing open. -/
theorem nvOpen_eq_of_nvLocus_eq {n m : ℕ} {s : powSections L n} {t : powSections L m}
    (h : nvLocus L s = nvLocus L t) : nvOpen L s = nvOpen L t :=
  TopologicalSpace.Opens.ext (by rw [coe_nvOpen, coe_nvOpen, h])

/-- **An affine basic open around each point of `X_a`.** For `L` ample and `a` a homogeneous
element of positive degree of the section ring, every point of `X_a` lies in an affine basic open
of a section of `𝒪_X` over `X_a`. -/
theorem exists_affine_basicOpen_mem (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d)
    (a : powSections L d) {x : X} (hx : x ∈ nvOpen L a) :
    ∃ f : Γ(X, nvOpen L a), IsAffineOpen (X.basicOpen f) ∧ x ∈ X.basicOpen f := by
  obtain ⟨n, hn, s, haff, hxs⟩ :=
    Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen X L hL x
  obtain ⟨b, hb⟩ := Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq L n s
  have hbopen : nvOpen L b = Stacks.AmpleTheory.powNonvanishingOpen X L n s :=
    TopologicalSpace.Opens.ext (by rw [coe_nvOpen, hb]; rfl)
  obtain ⟨m, a', b', hm, ha', hb'⟩ := exists_common_degree L hd hn a b
  have hUa : nvOpen L a' = nvOpen L a := nvOpen_eq_of_nvLocus_eq L ha'
  have hUb : nvOpen L b' = nvOpen L b := nvOpen_eq_of_nvLocus_eq L hb'
  obtain ⟨f, hf⟩ := exists_basicOpen_eq_inf
    (M := Stacks.TensorPowers.natTensorPow L m)
    (globalSection X _ a') (globalSection X _ b')
    (U := nvOpen L a) (le_of_eq hUa.symm)
  refine ⟨f, ?_, ?_⟩
  · rw [hf]
    have key : nvOpen L a ⊓ nvOpen L b' = nvOpen L b ⊓ nvOpen L a' := by
      rw [hUb, hUa, inf_comm]
    rw [show (nvOpen L a ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X
        (Stacks.TensorPowers.natTensorPow L m) (globalSection X _ b')) =
        nvOpen L b ⊓ nvOpen L a' from key]
    exact Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nvOpen L a'
      (hbopen ▸ haff)
  · rw [hf]
    refine ⟨hx, ?_⟩
    have : x ∈ nvOpen L b' := by rw [hUb, hbopen]; exact hxs
    exact this

/-- **The nonvanishing locus of a homogeneous section of positive degree is quasi-affine**, for
`L` ample. It is quasi-compact by Stacks Tag 01PV, and the affine basic opens of global functions
on it cover it by `exists_affine_basicOpen_mem`, which is Mathlib's criterion. -/
theorem isQuasiAffine_nvOpen (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d) (a : powSections L d) :
    (nvOpen L a).toScheme.IsQuasiAffine := by
  have hX : CompactSpace X := hL.1
  have hcpt : IsCompact ((nvOpen L a : X.Opens) : Set X) :=
    Stacks.NonvanishingAffineIntersection.isCompact_nonvanishingOpen
      (Stacks.TensorPowers.natTensorPow L d) (globalSection X _ a)
  have hc : CompactSpace (nvOpen L a).toScheme := isCompact_iff_compactSpace.mp hcpt
  refine AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨f, haff, hxf⟩ := exists_affine_basicOpen_mem L hL hd a x.2
  have h1 := Scheme.Opens.ι_image_basicOpen_topIso_inv (nvOpen L a) f
  refine ⟨(nvOpen L a).topIso.inv f, ?_, ?_⟩
  · rwa [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (nvOpen L a).ι, h1]
  · rw [← Scheme.Hom.preimage_image_eq (nvOpen L a).ι
      ((nvOpen L a).toScheme.basicOpen ((nvOpen L a).topIso.inv f)), h1]
    exact hxf

/-- **Part (3) of Stacks Tag 01ZY with the affine open confined to a prescribed open.** A finite
subset `E` of an open `W` of a scheme carrying an ample invertible module lies in an affine open
contained in `W`.

The source's proof of Stacks Tag 09NV uses part (3) in exactly this form, to shrink `W` to an
affine open before running graded prime avoidance inside it. No tag attribute is attached here:
the part (3) label sits on the unconfined statement below, which is what the tag asserts. -/
theorem exists_affineOpen_containing_finite_le_of_ample (hL : IsAmple X L) {E : Set X}
    (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) ∧ U ≤ W := by
  obtain ⟨d, a, hd, hEa⟩ := Stacks.AmpleFiniteAvoidance.exists_nvLocus_containing_finite L hL hE
  have hQA := isQuasiAffine_nvOpen L hL hd a
  have hEU : E ⊆ ((nvOpen L a : X.Opens) : Set X) := by rw [coe_nvOpen]; exact hEa
  have hfin : ((nvOpen L a).ι.base ⁻¹' E).Finite :=
    hE.preimage (nvOpen L a).ι.isOpenEmbedding.injective.injOn
  obtain ⟨g, hg, hEg, hgW⟩ :=
    Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine hfin
      ((nvOpen L a).ι ⁻¹ᵁ W) fun y hy => hEW hy
  refine ⟨(nvOpen L a).ι ''ᵁ (nvOpen L a).toScheme.basicOpen g,
    (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (nvOpen L a).ι).mpr hg, fun e he => ?_,
    (Scheme.Hom.image_mono _ hgW).trans (Scheme.Hom.image_preimage_le _ W)⟩
  have heU : e ∈ (nvOpen L a : X.Opens) := hEU he
  exact ⟨⟨e, heU⟩, hEg (show (nvOpen L a).ι.base ⟨e, heU⟩ ∈ E from he), rfl⟩

/-- **Stacks Tag 01ZY, part (3).** A finite set of points of a scheme carrying an ample invertible
`𝒪_X`-module lies in an affine open. -/
@[stacks 01ZY "part (3)"]
theorem exists_affineOpen_containing_finite_of_ample (hL : IsAmple X L) {E : Set X}
    (hE : E.Finite) : ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) := by
  obtain ⟨U, hU, hEU, -⟩ :=
    exists_affineOpen_containing_finite_le_of_ample L hL hE ⊤ fun _ _ => trivial
  exact ⟨U, hU, hEU⟩

/-- **Stacks Tag 09NV reduced to a single named input.** On the hypothesis that the opens `X_s`
form a basis for the topology — clause (3) of Stacks Tag 01Q3 — a finite subset `E` of an open `W`
of a scheme with an ample invertible module lies in an *affine* `X_a ≤ W` for `a` homogeneous of
positive degree, which is the conclusion of Stacks Tag 09NV.

No tag attribute is attached: this still carries the clause (3) hypothesis, and the Tag 09NV
label sits on the unconditional
`Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite_sections`
(`../AmpleFiniteAffineNonvanishing/Basic.lean`). The affine open between `E` and `W` that
`Stacks.NonvanishingAffineIntersection.exists_affine_nvOpen_containing_finite_le` had to assume is
supplied here by part (3). -/
theorem exists_affine_nvOpen_containing_finite_le_of_ample
    (hb : Stacks.AmpleTheory.IsBasisNonvanishing X L) (hL : IsAmple X L) {E : Set X}
    (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ (d : ℕ) (a : powSections L d), 1 ≤ d ∧ E ⊆ (nvOpen L a : Set X) ∧ nvOpen L a ≤ W ∧
      IsAffineOpen (nvOpen L a) := by
  obtain ⟨U, hU, hEU, hUW⟩ := exists_affineOpen_containing_finite_le_of_ample L hL hE W hEW
  exact Stacks.NonvanishingAffineIntersection.exists_affine_nvOpen_containing_finite_le
    L hb hE hU hEU hUW

end Stacks.AmpleAffineAvoidance

end
