module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTheory.Basic

/-!
# A finite set in one nonvanishing open, from ampleness

`StacksFrontier/AlgebraicGeometry/AmpleFiniteAvoidance/Basic.lean` runs graded prime avoidance in
the section ring `Γ_*(X, L)` and produces one homogeneous section not vanishing at any point of a
finite set, on a covering hypothesis stated in that ring's own vocabulary. This file discharges
that hypothesis from ampleness and states the two consequences used downstream.

## The vocabulary bridge, and why it is needed

Two descriptions of `Γ(X, L ^⊗ n)` meet here and they are not the same term.

* The **ample** side speaks of `Stacks.Ample.tensorPowModule X L (n : ℤ)`, the integer tensor
  powers of Stacks Tag 01CU, and of honest sections `Γ(tensorPowModule X L n, ⊤)`. That is what
  `Stacks.Ample.IsAmple` and `Stacks.AmpleTheory.IsBasisNonvanishing` are stated with.
* The **section ring** side speaks of `Stacks.GradedSections.powSections L n`, a morphism out of
  the monoidal unit into the iterated tensor product `Stacks.TensorPowers.natTensorPow L n`. That
  is what the product `X_{st} = X_s ∩ X_t` and hence the grading are stated with.

`Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow` says the two modules are *equal* in
nonnegative degree, and `Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv` says the two
section groups are additively the same. `Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`
composes them, and is the only place in this directory where a module is transported along an
equality.

## Main results

* `Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq`: the bridge.
* `Stacks.AmpleFiniteAvoidance.exists_nvLocus_containing_finite`: **for `L` ample, a finite set of
  points lies in a single `X_s` with `s` a global section of a positive tensor power.** No
  hypothesis beyond ampleness.
* `Stacks.AmpleFiniteAvoidance.exists_nvOpen_containing_finite_le`: the same with the nonvanishing
  open confined to a prescribed open containing the finite set, on the hypothesis
  `Stacks.AmpleTheory.IsBasisNonvanishing` — clause (3) of Stacks Tag 01Q3. **This is the
  statement of Stacks Tag 09NV with the word "affine" deleted**; restoring the word is what this
  file does not do, and is done elsewhere — see "What is not done".

## Implementation notes

The equality of modules is turned into an isomorphism by `eqToIso`, and the category has to be
pinned: `Stacks.TensorPowers.natTensorPow` is stated for an abstract monoidal category and
`AlgebraicGeometry.Scheme.Modules` is a `def`, so an unpinned `eqToIso` lands in the
`SheafOfModules` category, where the field `app` used by
`Stacks.Ample.nonvanishingLocus_congr` does not resolve (the error is "the environment does not
contain `SheafOfModules.Hom.app`"). Writing `eqToIso (C := X.Modules)` and binding the result
with `let` — not with a type ascription, which does not survive elaboration here — fixes it.

## References

* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)

## What is not done

**Neither Stacks Tag 09NV nor part (3) of Stacks Tag 01ZY is proved here, and no stacks attribute
is attached.** Both conclude that the open produced is *affine*, and the single missing input for
that is **Stacks Tag 01PV**: for every affine open `U` and every global section `s` of an
invertible module, `U ∩ X_s` is affine. Tag 01PV is proved, as
`Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`
(`../NonvanishingAffineIntersection/Basic.lean`), by a short argument over a trivializing cover —
not by the source's own route, an algebra argument about the symmetric algebra of an invertible
module modulo `s - 1`, which has no counterpart here.
`Stacks.AmpleTheory.IsAffineOfLeAffine` is the consequence of it that the ample arguments consume;
`../AmpleTheory/Basic.lean` still writes it as a hypothesis, discharged there only when the module
has a nowhere-vanishing global basis in every degree
(`Stacks.AmpleTheory.isAffineOfLeAffine_of_nonvanishingBasis`), but
`Stacks.NonvanishingAffineIntersection.isAffineOfLeAffine` discharges it for every invertible
module.

So both consumers are closed, neither of them here. Part (3) of Tag 01ZY is
`Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample`
(`../AmpleAffineAvoidance/AmpleFiniteSet.lean`), built on
`Stacks.AmpleFiniteAvoidance.exists_nvLocus_containing_finite` below, and Tag 09NV is
`Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite_sections`
(`../AmpleFiniteAffineNonvanishing/Basic.lean`), with ampleness as its only hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace DirectSum
open Stacks.Ample Stacks.GradedSections Stacks.SectionProduct

universe u

namespace Stacks.AmpleFiniteAvoidance

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

/-- **The vocabulary bridge.** An honest global section of the `n`-th integer tensor power of `L`
is the global section of a homogeneous element of the section ring of degree `n`, with the same
nonvanishing locus. -/
theorem exists_powSections_nvLocus_eq (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) :
    ∃ a : powSections L n, nvLocus L a = nonvanishingLocus (tensorPowModule X L (n : ℤ)) s := by
  have heq : (Stacks.TensorPowers.natTensorPow L n : X.Modules) = tensorPowModule X L (n : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n
  let e : (Stacks.TensorPowers.natTensorPow L n : X.Modules) ≅ tensorPowModule X L (n : ℤ) :=
    eqToIso (C := X.Modules) heq
  obtain ⟨a, ha⟩ := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
    (Stacks.TensorPowers.natTensorPow L n)).surjective (e.inv.app ⊤ s)
  refine ⟨a, ?_⟩
  rw [nvLocus, show globalSection X (Stacks.TensorPowers.natTensorPow L n) a = e.inv.app ⊤ s from
    ha]
  exact nonvanishingLocus_congr e.symm s

/-- **A finite set of points of a scheme with an ample invertible module lies in a single
`X_s`**, for `s` a global section of a positive tensor power of `L`. No hypothesis beyond
ampleness.

This is the conclusion of part (3) of Stacks Tag 01ZY with "affine open" weakened to
"nonvanishing open of a homogeneous section"; the affineness of `X_s` is not available, and the
single reason is recorded in the module documentation. -/
theorem exists_nvLocus_containing_finite (hL : IsAmple X L) {E : Set X} (hE : E.Finite) :
    ∃ (d : ℕ) (a : powSections L d), 1 ≤ d ∧ E ⊆ nvLocus L a := by
  obtain ⟨d, a, hd, hEa, -⟩ :=
    exists_homogeneous_forall_mem_nvLocus L hE Set.univ fun x _ => by
      obtain ⟨n, hn, s, -, hxs⟩ :=
        Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen X L hL x
      obtain ⟨b, hb⟩ := exists_powSections_nvLocus_eq L n s
      exact ⟨n, b, hn, by rw [hb]; exact hxs, Set.subset_univ _⟩
  exact ⟨d, a, hd, hEa⟩

/-- **Stacks Tag 09NV with the word "affine" deleted.** Let `L` be an invertible `𝒪_X`-module for
which the nonvanishing opens of global sections of positive tensor powers form a basis of the
topology — clause (3) of Stacks Tag 01Q3, `Stacks.AmpleTheory.IsBasisNonvanishing`. Then a finite
subset of an open `W` lies in a single nonvanishing open contained in `W`.

Tag 09NV asserts in addition that the open produced is affine. That, and nothing else, is what
Stacks Tag 01PV would supply: the open is `X_s` for a homogeneous `s`, and `01PV` says exactly
that such an open inside an affine open is affine. -/
theorem exists_nvOpen_containing_finite_le (hb : Stacks.AmpleTheory.IsBasisNonvanishing X L)
    {E : Set X} (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ (d : ℕ) (a : powSections L d), 1 ≤ d ∧ E ⊆ (nvOpen L a : Set X) ∧ nvOpen L a ≤ W := by
  obtain ⟨d, a, hd, hEa, haW⟩ :=
    exists_homogeneous_forall_mem_nvLocus L hE (W : Set X) fun x hx => by
      obtain ⟨n, hn, s, hxs, hsW⟩ := hb x W (hEW hx)
      obtain ⟨c, hc⟩ := exists_powSections_nvLocus_eq L n s
      refine ⟨n, c, hn, by rw [hc]; exact hxs, ?_⟩
      rw [hc]
      exact fun y hy => hsW hy
  exact ⟨d, a, hd, by rwa [coe_nvOpen], by rw [← SetLike.coe_subset_coe, coe_nvOpen]; exact haW⟩

end Stacks.AmpleFiniteAvoidance

end
