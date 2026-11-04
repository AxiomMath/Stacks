module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.ChartSaturation

/-!
# The agreement hypothesis of the chart of Tag 0BD7, from a unit on the base

`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartSaturation.lean` builds the chart of
[Stacks, Tag 0BD7] from a family `t` of sections of `ℒ` together with two properties the
penultimate paragraph of that proof establishes: `hex`, that some member of the family generates
at each point of `X`, and `hagree`, that two members generating at a common point of a fibre
generate at the same points of *the whole* fibre.

This file discharges `hagree`. The source's uniqueness sentence is a statement about a *germ* on
the base — "`g` and `g'` differ by an element of `𝒪_{Y, y}^*`" — while
`Stacks.SheafOfModules.mem_generatingLocus_iff_of_restrictₛₗ_eq_smul`, the bridge from a unit
relation to an agreement of loci, asks for a unit *section on a common open of `X`* and concludes
only inside that open. Three steps separate them:

* a germ that is a unit in `𝒪_{Y, y}` is a unit *section* on an open `B ∋ y`
  (`Stacks.InvertiblePullback.exists_le_isUnit_res_of_isUnit_germ`, a repackaging of Mathlib's
  `AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ` with the inclusion written as a
  `homOfLE`, which is the form every consumer below needs);
* the preimage `φ^{-1}(B)` of such an open contains the *entire* fibre over `y`
  (`Stacks.InvertiblePullback.fibre_subset_preimage`) — so a unit obtained on a neighbourhood of
  `y` in the base, and only there, still identifies the two loci along the whole fibre, which is
  the quantifier `hagree` asks for and the reason the source's local statement suffices;
* the relation `t i = φ^*(w) t j` restricts from `φ^{-1}(A)` to `φ^{-1}(B)` with `φ^*(w)` becoming
  `φ^*(w|_B)` (`Stacks.InvertiblePullback.restrictₛₗ_app_smul`).

The family itself is *not* built here: in the source neither `s` nor the multipliers `g_i` are
regular sections, so the family is
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/PullbackMeromorphicFamily.lean`'s
`Stacks.InvertiblePullback.IsPullMeromorphicFamily`, where `s` is a meromorphic section of `ℒ`
and `g_i` a meromorphic function on `A i`. What this file supplies to that one is the last result
below, `hagree` from a unit germ on the base.

## Main results

* `Stacks.InvertiblePullback.forall_mem_generatingLocus_iff_of_exists_fibre_unit`: `hagree` from a
  unit section on an open of `X` containing the fibre.
* `Stacks.InvertiblePullback.forall_mem_generatingLocus_iff_of_exists_base_unit`: `hagree` from a
  unit section on an open of the *base*, where the containment of the fibre is free.
* `Stacks.InvertiblePullback.forall_mem_generatingLocus_iff_of_exists_base_germ_unit`: `hagree`
  from a unit *germ* on the base — the source's own sentence.
* `Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections_of_exists_base_germ_unit`:
  the chart datum of
  `StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartFromGenerators.lean` with `hagree`
  discharged.

## Implementation notes

Every statement takes as hypotheses the family, its existence property `hex`, and the unit
relation between its members; the relation itself is the output of the ring theory of
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/StalkGenerator.lean`
(`Module.FaithfullyFlat.associated_of_algebraMap_eq_isUnit_mul`).

`Stacks.SheafOfModules.generatingLocus` is stated for
`SheafOfModules (structureSheafRing X.toRingedSpace)`, and the module is declared at
that spelling here rather than at `X.Modules`: written as `X.Modules`, the scalar type of the unit
in the hypotheses below has to be spelled out, and `HSMul ↑(X.presheaf.obj (op W))` then fails to
synthesize against `↑(L.val.obj (op W))` — as does `HSMul ↑(X.toRingedSpace.presheaf.obj (op W))`,
so this is not the spelling gap recorded in `ChartFromGenerators.lean` but the one caused by
`X.Modules` being a `def` carrying its own structure. Applications in the other direction are
free: the results below are applied to
`Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections`, whose module is an
`X.Modules`, with no coercion.

The double restriction of a section is written out from `PresheafOfModules.map_comp_apply`, as in
`ChartSaturation.lean` and `ChartFromGenerators.lean`, rather than through the general
`PresheafOfModules.restrictₛₗ_restrictₛₗ`
(`StacksFrontier/AlgebraicGeometry/Meromorphic/DenominatorSupport.lean`), so that this file does not
import the meromorphic tree; that tree is imported by
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/PullbackMeromorphicFamily.lean`, where the
family needs it.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.InvertiblePullback

open Stacks.SheafOfModules

variable {X Y : Scheme.{u}}

/-- **A germ that is a unit is a unit on a neighbourhood, with the inclusion as a `homOfLE`.**
Mathlib's `AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ` produces an arbitrary
morphism of opens; every consumer below restricts along `homOfLE`, and the two agree because
morphisms of `Opens` are a subsingleton. This is the first of the three steps separating the
source's "`g` and `g'` differ by an element of `𝒪_{Y, y}^*`" from an agreement of generating
loci. -/
theorem exists_le_isUnit_res_of_isUnit_germ {A : Y.Opens} (y : Y) (hyA : y ∈ A) (w : Γ(Y, A))
    (hw : IsUnit (Y.presheaf.germ A y hyA w)) :
    ∃ (B : Y.Opens) (hBA : B ≤ A) (_ : y ∈ B), IsUnit (Y.presheaf.map (homOfLE hBA).op w) := by
  obtain ⟨B, i, hyB, hu⟩ := Y.toRingedSpace.isUnit_res_of_isUnit_germ A w y hyA hw
  refine ⟨B, i.le, hyB, ?_⟩
  rwa [show homOfLE i.le = i from Subsingleton.elim _ _]

variable (f : X ⟶ Y)

/-- **The preimage of an open neighbourhood of `φ(x)` contains the whole fibre through `x`.**
This is why a unit found only near `φ(x)` on the base suffices for the agreement hypothesis of
`Stacks.InvertiblePullback.mem_generatingLocus_of_mem_fiber`, which quantifies over every point
of the fibre: the open on which the two sections are related is a preimage, and a preimage is
saturated. -/
theorem fibre_subset_preimage {B : Y.Opens} {x : X.toRingedSpace.carrier} (hx : f.base x ∈ B) :
    f.base ⁻¹' {f.base x} ⊆ ((f ⁻¹ᵁ B : X.Opens) : Set X.toRingedSpace.carrier) :=
  Set.preimage_mono (Set.singleton_subset_iff.mpr hx)

variable (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- Restricting a section along `homOfLE` twice is restricting along the composite `homOfLE`. -/
private theorem restrictₛₗ_restrictₛₗ_homOfLE {U V W : Opens X.toRingedSpace.carrier}
    (hVU : V ≤ U) (hWV : W ≤ V) (u : L.val.obj (op U)) :
    L.val.restrictₛₗ (homOfLE hWV).op (L.val.restrictₛₗ (homOfLE hVU).op u)
      = L.val.restrictₛₗ (homOfLE (hWV.trans hVU)).op u := by
  change L.val.map (homOfLE hWV).op (L.val.map (homOfLE hVU).op u) = _
  rw [← L.val.map_comp_apply]
  congr 1

/-- **Restricting a section scaled by the pullback of a function on the base.** Restricting from
`φ^{-1}(A)` to `φ^{-1}(B)` turns `φ^*(w) u` into `φ^*(w|_B) u`, which is what lets a relation
between two sections stated on one preimage be used on a smaller one. The scalar is identified by
`Stacks.PicFinite.pull_restrict`, the naturality of `φ^*` on the structure sheaf. -/
theorem restrictₛₗ_app_smul {A B : Y.Opens} (hBA : B ≤ A) (w : Γ(Y, A))
    (hpre : ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A : X.Opens))
    {U : Opens X.toRingedSpace.carrier} (hAU : ((f ⁻¹ᵁ A : X.Opens) : Opens _) ≤ U)
    (u : L.val.obj (op U)) :
    L.val.restrictₛₗ (homOfLE hpre).op ((f.app A).hom w • L.val.restrictₛₗ (homOfLE hAU).op u)
      = (f.app B).hom (Y.presheaf.map (homOfLE hBA).op w)
          • L.val.restrictₛₗ (homOfLE (hpre.trans hAU)).op u := by
  have hscalar : (structureSheafRing X.toRingedSpace).obj.map (homOfLE hpre).op
      ((f.app A).hom w) = (f.app B).hom (Y.presheaf.map (homOfLE hBA).op w) := by
    rw [show (homOfLE hpre).op = ((Opens.map f.base).map (homOfLE hBA)).op from
      Subsingleton.elim _ _]
    exact Stacks.PicFinite.pull_restrict f hBA w
  rw [(L.val.restrictₛₗ (homOfLE hpre).op).map_smulₛₗ, hscalar, restrictₛₗ_restrictₛₗ_homOfLE]

variable {ι : Type*} {V : ι → Opens X.toRingedSpace.carrier} (t : ∀ i, L.val.obj (op (V i)))

/-- **The agreement hypothesis of the chart of [Stacks, Tag 0BD7], from a unit on an open of `X`
containing the fibre.** The conclusion is the `hagree` hypothesis of
`Stacks.InvertiblePullback.mem_generatingLocus_of_mem_fiber`, verbatim. The containment of the
whole fibre in the open is what carries
`Stacks.SheafOfModules.mem_generatingLocus_iff_of_restrictₛₗ_eq_smul`, which concludes only
inside the open, to every point of the fibre. -/
theorem forall_mem_generatingLocus_iff_of_exists_fibre_unit
    (hunit : ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∃ (W : Opens X.toRingedSpace.carrier) (hWi : W ≤ V i) (hWj : W ≤ V j)
        (c : X.toRingedSpace.presheaf.obj (op W)),
        f.base ⁻¹' {f.base x} ⊆ (W : Set X.toRingedSpace.carrier) ∧ IsUnit c ∧
          L.val.restrictₛₗ (homOfLE hWi).op (t i)
            = c • L.val.restrictₛₗ (homOfLE hWj).op (t j)) :
    ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∀ z : X.toRingedSpace.carrier, f.base z = f.base x →
        (z ∈ generatingLocus L (t i) ↔ z ∈ generatingLocus L (t j)) := by
  intro i j x hxi hxj z hz
  obtain ⟨W, hWi, hWj, c, hfib, hc, hcc⟩ := hunit i j x hxi hxj
  exact mem_generatingLocus_iff_of_restrictₛₗ_eq_smul L hWi hWj hc hcc (hfib hz)

/-- **The same from a unit section on an open of the base.** Here the containment of the fibre is
free (`Stacks.InvertiblePullback.fibre_subset_preimage`), so the hypothesis is a statement about
the base and about the two sections only. -/
theorem forall_mem_generatingLocus_iff_of_exists_base_unit
    (hunit : ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∃ (B : Y.Opens) (_ : f.base x ∈ B)
        (hBi : ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) ≤ V i)
        (hBj : ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) ≤ V j)
        (w : Γ(Y, B)), IsUnit w ∧
        L.val.restrictₛₗ (homOfLE hBi).op (t i)
          = (f.app B).hom w • L.val.restrictₛₗ (homOfLE hBj).op (t j)) :
    ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∀ z : X.toRingedSpace.carrier, f.base z = f.base x →
        (z ∈ generatingLocus L (t i) ↔ z ∈ generatingLocus L (t j)) := by
  refine forall_mem_generatingLocus_iff_of_exists_fibre_unit f L t fun i j x hxi hxj => ?_
  obtain ⟨B, hxB, hBi, hBj, w, hw, hcc⟩ := hunit i j x hxi hxj
  exact ⟨_, hBi, hBj, (f.app B).hom w, fibre_subset_preimage f hxB, hw.map (f.app B).hom, hcc⟩

/-- **The same from a unit *germ* on the base — the source's own sentence.** The uniqueness
statement of the penultimate paragraph of [Stacks, Tag 0BD7] says that two candidate functions
differ by an element of `𝒪_{Y, y}^*`, a unit of a *stalk*; this turns that into the agreement of
generating loci along the whole fibre over `y`, by shrinking the open on which the relation is
stated to one on which the germ is represented by a unit section. -/
theorem forall_mem_generatingLocus_iff_of_exists_base_germ_unit
    (hunit : ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∃ (A : Y.Opens) (hxA : f.base x ∈ A)
        (hAi : ((f ⁻¹ᵁ A : X.Opens) : Opens X.toRingedSpace.carrier) ≤ V i)
        (hAj : ((f ⁻¹ᵁ A : X.Opens) : Opens X.toRingedSpace.carrier) ≤ V j)
        (w : Γ(Y, A)), IsUnit (Y.presheaf.germ A (f.base x) hxA w) ∧
        L.val.restrictₛₗ (homOfLE hAi).op (t i)
          = (f.app A).hom w • L.val.restrictₛₗ (homOfLE hAj).op (t j)) :
    ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∀ z : X.toRingedSpace.carrier, f.base z = f.base x →
        (z ∈ generatingLocus L (t i) ↔ z ∈ generatingLocus L (t j)) := by
  refine forall_mem_generatingLocus_iff_of_exists_base_unit f L t fun i j x hxi hxj => ?_
  obtain ⟨A, hxA, hAi, hAj, w, hw, hcc⟩ := hunit i j x hxi hxj
  obtain ⟨B, hBA, hxB, hwB⟩ := exists_le_isUnit_res_of_isUnit_germ (f.base x) hxA w hw
  have hpre : ((f ⁻¹ᵁ B : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A : X.Opens) :=
    fun z hz => hBA hz
  refine ⟨B, hxB, hpre.trans hAi, hpre.trans hAj, Y.presheaf.map (homOfLE hBA).op w, hwB, ?_⟩
  have h := congrArg (L.val.restrictₛₗ (homOfLE hpre).op) hcc
  rw [restrictₛₗ_app_smul f L hBA w hpre hAj (t j)] at h
  rwa [restrictₛₗ_restrictₛₗ_homOfLE] at h

/-- **The chart datum of [Stacks, Tag 0BD7] with `hagree` discharged.** This is
`Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections` with its agreement hypothesis
replaced by the source's unit-germ relation on the base. -/
theorem exists_chart_nonempty_generatorSections_of_exists_base_germ_unit
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    [IsLocallyNoetherian Y] [Flat f]
    (hex : ∀ z : X.toRingedSpace.carrier, ∃ i, z ∈ generatingLocus L (t i))
    (hirr : ∀ y : Y, IsIrreducible (f.base ⁻¹' {y}))
    (hunit : ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∃ (A : Y.Opens) (hxA : f.base x ∈ A)
        (hAi : ((f ⁻¹ᵁ A : X.Opens) : Opens X.toRingedSpace.carrier) ≤ V i)
        (hAj : ((f ⁻¹ᵁ A : X.Opens) : Opens X.toRingedSpace.carrier) ≤ V j)
        (w : Γ(Y, A)), IsUnit (Y.presheaf.germ A (f.base x) hxA w) ∧
        L.val.restrictₛₗ (homOfLE hAi).op (t i)
          = (f.app A).hom w • L.val.restrictₛₗ (homOfLE hAj).op (t j))
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    ∃ chart : Y → Y.Opens, (∀ y, y ∈ chart y) ∧
      ∀ y, Nonempty (GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ chart y)) :=
  exists_chart_nonempty_generatorSections f L t hex hirr
    (forall_mem_generatingLocus_iff_of_exists_base_germ_unit f L t hunit) hfiber hfinite

end Stacks.InvertiblePullback

end
