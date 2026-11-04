module

public import StacksFrontier.AlgebraicGeometry.LiftInvertible.DisjointGenerator
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.PuncturedChart
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.StarCover

/-!
# The star-shaped cover of a one-dimensional scheme

The construction of [Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) needs a
star-shaped trivializing cover of `X`. For an **irreducible** `X` the centre can be taken to be
a member of the Tag 0BUT trivializing cover containing the generic point. A reducible `X` has
one generic point per irreducible component and no single member of the trivializing cover need
contain them all, so that choice of centre is unavailable. This file builds the cover with no
irreducibility hypothesis on `X`.

## The centre of a reducible scheme

`Stacks.Topology.Dimension.exists_disjoint_subordinate_opens_of_topologicalKrullDim_le_one`
refines the trivializing cover `W` into a family `A`, one open per irreducible component, with
`A C` dense in `C`, contained in some `W (j C)`, and the `A C` **pairwise disjoint**; the
complement of their union is a finite set of closed points. Take the centre to be

`G = ⨆ C, A C`.

The only thing the centre is asked for is a *generator of `L` over `i⁻¹G`*, and a generator over
a pairwise disjoint union is assembled from generators over the pieces with no compatibility
condition — `Stacks.SheafOfModules.nonempty_generatorSections_of_pairwise_disjoint`. Each piece
has one because `A C ≤ W (j C)`. So the per-component work is confined to the centre's generator,
and the chosen lifts of the transition units stay **per point**.

The rest of the construction never mentions the components: the complement `T = Gᶜ` is a finite set
of closed points, the chart of `x ∈ T` is the punctured affine chart of
`Stacks.LiftInvertible.exists_isAffineOpen_punctured_of_topologicalKrullDim_le_one` inside `W x`,
the chart of `y ∈ G` is an affine open inside `G ⊓ W y`, and `G ⊓ chart x` is the puncture of
`chart x`, hence affine. The point of `T` to which some other point specializes is the generic
point of any irreducible component containing it, which lies in that component's piece of the
centre and so is not the point itself.

## Main results

* `Stacks.LiftInvertible.mem_of_isOpen_of_closure_eq`: a generic point of `S` lies in every open
  subset of `S` with closure `S`.
* `Stacks.LiftInvertible.nonempty_chartData_isAffineOpen_inf_of_topologicalKrullDim_le_one`: the
  star-shaped cover, for a Noetherian scheme of dimension at most one with **no** irreducibility
  hypothesis.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_surjective`: **Tag 09NY for a surjective
  closed immersion**, in Tag 09NY's own spelling and with Tag 09NY's own hypotheses on `X`. Every
  hypothesis is topological.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_ker_le_nilradical` and
  `Stacks.LiftInvertible.exists_modulePullback_iso_of_isNilpotent_ker`: the same with the
  surjectivity written as a bound on the ideal sheaf, and its nilpotent special case.

## Implementation notes

No `@[stacks 09NY]` attribute is attached to anything here. One of Tag 09NY's hypotheses is still
missing from the results below and the restriction is genuine: Tag 09NY asks for **every** closed
immersion into such an `X`, and the results below ask that `i` be **onto**. Without that the
units of `𝒪_X` do not surject onto those of `𝒪_Z` over an affine, so the chosen lifts of
`StacksFrontier/AlgebraicGeometry/LiftInvertible/StarCover.lean` do not exist: for
`Spec k[t]/(t(t-1)) ⟶ Spec k[t]` the map on units is `kˣ → kˣ × kˣ` and `(1, -1)` has no lift in
characteristic `≠ 2`, and that `i` is precisely not onto. A proof of Tag 09NY in that generality
must modify the trivializations themselves rather than lift their transition units.

**What remains of Tag 09NY is exactly the mixed case.** Writing `Z` for the image of `i`, which
is closed: if `Z` contains **no** irreducible component of `X` then `Z` is a finite discrete set
of points, `L` is trivial, and `𝒪_X` lifts it — that is
`Stacks.LiftInvertible.exists_modulePullback_iso_of_not_irreducibleComponent_subset_range` in
`StacksFrontier/AlgebraicGeometry/LiftInvertible/Basic.lean`. If `Z` contains **every**
irreducible component then `Z = X` as a space, `i` is onto, and the theorem below applies. The
open case is `Z` containing some components and not others, where the two halves have to be
glued along their zero-dimensional intersection.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 0BUT](https://stacks.math.columbia.edu/tag/0BUT)
* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Set TopologicalSpace Topology
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules

universe u

namespace Stacks.LiftInvertible

variable {X Z : Scheme.{u}}

/-- **A generic point of `S` lies in every open subset of `S` whose closure is `S`.** If `A` is
open with `closure A = S` and `η` is a generic point of `S`, then `η ∈ A`: otherwise `S`, being
the closure of `{η}`, would lie in the closed set `Aᶜ`, while `A ⊆ closure A = S`, forcing
`A = ∅` and `S = ∅`. -/
theorem mem_of_isOpen_of_closure_eq {T : Type u} [TopologicalSpace T] {A S : Set T}
    (hA : IsOpen A) (hAS : closure A = S) {η : T} (hη : IsGenericPoint η S)
    (hS : S.Nonempty) : η ∈ A := by
  obtain ⟨a, ha⟩ := (closure_nonempty_iff (s := A)).1 (by rwa [hAS])
  exact (hη.mem_open_set_iff hA).2 ⟨a, hAS ▸ subset_closure ha, ha⟩

/-- **The star-shaped trivializing cover of a one-dimensional scheme.** For a finite `i : Z ⟶ X`
and an invertible `L` on `Z`, with the underlying space of `X` Noetherian of Krull dimension at
most one, there is an open `G` of `X`, chart data star-shaped around `G`, a generator of `L` over
`i⁻¹G`, and the affineness of every overlap `G ⊓ chart p`.

The centre is the union of a pairwise disjoint family of opens, one dense in each irreducible
component and each contained in a member of the trivializing cover; its generator is glued from
the pieces by `Stacks.SheafOfModules.nonempty_generatorSections_of_pairwise_disjoint`. The charts
of the finitely many points outside the centre are the punctured affine charts of
`Stacks.LiftInvertible.exists_isAffineOpen_punctured_of_topologicalKrullDim_le_one`, and the
charts of the points inside it are affine opens contained in it.

No irreducibility hypothesis on `X` appears. -/
theorem nonempty_chartData_isAffineOpen_inf_of_topologicalKrullDim_le_one (i : Z ⟶ X)
    [IsFinite i] [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) (L : Z.Modules)
    [IsInvertible Z.presheaf (structureSheafRing
      Z.toRingedSpace).property L] :
    ∃ (G : X.Opens) (C : Stacks.PicFinite.ChartData i G L)
      (_ : GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ G)),
      ∀ p : X, IsAffineOpen (G ⊓ C.chart p) := by
  classical
  choose W hWmem hWtriv using Stacks.Divisors.hasTrivializingTargetCover_of_isFinite i L
  obtain ⟨A, jc, hAo, hAW, hAcl, hAdisj, hTfin0, hTpt0⟩ :=
    Stacks.Topology.Dimension.exists_disjoint_subordinate_opens_of_topologicalKrullDim_le_one
      (X := (X : Type u)) hdim (W := fun y : X => (W y : Set X)) (fun y => (W y).2)
      (fun x => ⟨x, hWmem x⟩)
  -- the pieces of the centre, as opens, and the centre itself
  set AO : irreducibleComponents (X : Type u) → X.Opens := fun C => ⟨A C, hAo C⟩ with hAO
  set G : X.Opens := ⨆ C, AO C with hG
  have hGset : (G : Set X) = ⋃ C, A C := by
    rw [hG, Opens.coe_iSup]
    rfl
  set T : Set X := (G : Set X)ᶜ with hT
  have hTeq : T = (⋃ C, A C)ᶜ := by rw [hT, hGset]
  have hTfin : T.Finite := hTeq ▸ hTfin0
  have hTpt : ∀ p ∈ T, IsClosed ({p} : Set X) := fun p hp => hTpt0 p (hTeq ▸ hp)
  have hAOG : ∀ C, AO C ≤ G := fun C => le_iSup AO C
  have hAsub : ∀ C, A C ⊆ (G : Set X) := by
    intro C
    rw [hGset]
    exact subset_iUnion A C
  -- every point of the complement is specialized to from the generic point of a component
  have hspec : ∀ x ∈ T, ∃ z : X, z ≠ x ∧ x ∈ closure ({z} : Set X) := by
    intro x hx
    set C : irreducibleComponents (X : Type u) :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ with hC
    obtain ⟨η, hη⟩ := QuasiSober.sober (C.2.1)
      (isClosed_of_mem_irreducibleComponents (C : Set X) C.2)
    have hηA : η ∈ A C :=
      mem_of_isOpen_of_closure_eq (hAo C) (hAcl C) hη ⟨x, hC ▸ mem_irreducibleComponent⟩
    refine ⟨η, ?_, ?_⟩
    · intro h
      exact hx (hAsub C (h ▸ hηA))
    · rw [isGenericPoint_def.1 hη]
      exact hC ▸ mem_irreducibleComponent
  -- the punctured affine charts around the points of the complement
  have hVex : ∀ x : X, x ∈ T → ∃ V V' : X.Opens, x ∈ V ∧ V ≤ W x ∧
      ((V : Set X) ∩ T = {x}) ∧ ((V' : Set X) = (V : Set X) \ {x}) ∧ IsAffineOpen V' := by
    intro x hx
    exact exists_isAffineOpen_punctured_of_topologicalKrullDim_le_one hdim hTfin hTpt hx
      (hspec x hx) (W x) (hWmem x)
  choose V V' hVmem hVle hVT hV'eq hV'aff using hVex
  -- affine charts inside the centre around the points of the centre
  have hAex : ∀ y : X, y ∉ T → ∃ B : X.Opens, IsAffineOpen B ∧ y ∈ B ∧ B ≤ G ⊓ W y := by
    intro y hy
    have hyG : y ∈ G := notMem_compl_iff.1 hy
    obtain ⟨_, ⟨B, hB, rfl⟩, hyB, hBle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show y ∈ G ⊓ W y from ⟨hyG, hWmem y⟩) (G ⊓ W y).2
    exact ⟨B, hB, hyB, hBle⟩
  choose B hBaff hBmem hBle using hAex
  -- the chart of a point
  set chart : X → X.Opens := fun p => if hp : p ∈ T then V p hp else B p hp with hchart
  have hchartle : ∀ p : X, chart p ≤ W p := by
    intro p
    by_cases hp : p ∈ T
    · simpa [hchart, hp] using hVle p hp
    · exact le_trans (by simp [hchart, hp]) ((hBle p hp).trans inf_le_right)
  have hchartmem : ∀ p : X, p ∈ chart p := by
    intro p
    by_cases hp : p ∈ T
    · simpa [hchart, hp] using hVmem p hp
    · simpa [hchart, hp] using hBmem p hp
  -- the central overlap of a chart is affine
  have hchartaff : ∀ p : X, IsAffineOpen (G ⊓ chart p) := by
    intro p
    by_cases hp : p ∈ T
    · have hchp : chart p = V p hp := by simp [hchart, hp]
      have hset : G ⊓ V p hp = V' p hp := by
        refine Opens.ext (Subset.antisymm (fun w hw => ?_) (fun w hw => ?_))
        · rw [hV'eq p hp]
          exact ⟨hw.2, fun hwp => hp ((show w = p from hwp) ▸ hw.1)⟩
        · rw [hV'eq p hp] at hw
          refine ⟨?_, hw.1⟩
          by_contra hwG
          exact hw.2 (by
            have : w ∈ (V p hp : Set X) ∩ T := ⟨hw.1, hwG⟩
            rwa [hVT p hp] at this)
      rw [hchp, hset]
      exact hV'aff p hp
    · have hchp : chart p = B p hp := by simp [hchart, hp]
      rw [hchp, inf_of_le_right ((hBle p hp).trans inf_le_left)]
      exact hBaff p hp
  -- the charts of two distinct points meet only inside the centre
  have hchartinf : ∀ p q : X, p ≠ q → chart p ⊓ chart q ≤ G := by
    intro p q hpq
    by_cases hp : p ∈ T
    · by_cases hq : q ∈ T
      · intro w hw
        by_contra hwG
        have hwp : w = p := by
          have hmem : w ∈ (V p hp : Set X) ∩ T :=
            ⟨by simpa [hchart, hp] using hw.1, hwG⟩
          rwa [hVT p hp] at hmem
        have hwq : w = q := by
          have hmem : w ∈ (V q hq : Set X) ∩ T :=
            ⟨by simpa [hchart, hq] using hw.2, hwG⟩
          rwa [hVT q hq] at hmem
        exact hpq (hwp ▸ hwq)
      · refine le_trans inf_le_right ?_
        exact le_trans (by simp [hchart, hq]) ((hBle q hq).trans inf_le_left)
    · refine le_trans inf_le_left ?_
      exact le_trans (by simp [hchart, hp]) ((hBle p hp).trans inf_le_left)
  -- a generator over the inverse image of any open inside a member of the trivializing cover
  have hgen : ∀ (U : X.Opens) (y : X), U ≤ W y →
      GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ U) := fun U y hU =>
    Stacks.Divisors.normChartSourceGenerator i L ⟨U, ⟨restrictIsoUnitOfLE L (P := i ⁻¹ᵁ U)
      (A := i ⁻¹ᵁ W y) (fun _ hx => hU hx) (hWtriv y).some⟩⟩
  -- the pieces of the centre pull back to a pairwise disjoint cover of the inverse image
  have hdisjZ : Pairwise (Function.onFun Disjoint fun C => i ⁻¹ᵁ AO C) := by
    intro C C' h
    have hb : AO C ⊓ AO C' = ⊥ := by
      refine disjoint_iff.1 (disjoint_iff.2 (Opens.ext ?_))
      simpa [hAO] using disjoint_iff_inter_eq_empty.1 (hAdisj h)
    refine disjoint_iff.2 ?_
    have h2 : (i ⁻¹ᵁ AO C) ⊓ (i ⁻¹ᵁ AO C') = i ⁻¹ᵁ (AO C ⊓ AO C') := rfl
    rw [h2, hb]
    rfl
  -- hence a generator over the inverse image of the centre
  obtain ⟨centerGen⟩ := nonempty_generatorSections_of_pairwise_disjoint
    (X := Z.toRingedSpace) L (fun C => i ⁻¹ᵁ AO C) (i ⁻¹ᵁ G)
    (fun C => (Opens.map i.base).map (homOfLE (hAOG C)) |>.le)
    (le_of_eq (Opens.map_iSup i.base AO)) hdisjZ fun C => hgen _ _ (hAW C)
  exact ⟨G, ⟨chart, hchartmem, hchartinf, fun p => hgen _ p (hchartle p)⟩, centerGen, hchartaff⟩

/-- **Tag 09NY for a closed immersion whose ideal sheaf lies in the nilradical.** An invertible
module on a closed subscheme of a scheme with Noetherian underlying space of dimension at most
one, cut out by an ideal sheaf all of whose sections are nilpotent, is the pullback of an
invertible module on the ambient scheme.

No hypothesis on the irreducible components of `X` appears: the star-shaped cover is
`Stacks.LiftInvertible.nonempty_chartData_isAffineOpen_inf_of_topologicalKrullDim_le_one` and the
lifting is
`Stacks.LiftInvertible.exists_modulePullback_iso_of_starChartData_of_ker_le_nilradical`.

The tag is withheld: Tag 09NY has no hypothesis on the ideal sheaf. See
`Stacks.LiftInvertible.exists_modulePullback_iso_of_surjective` for the equivalent topological
form of this hypothesis, and the implementation notes for why it cannot be dropped on this
route. -/
theorem exists_modulePullback_iso_of_ker_le_nilradical (i : Z ⟶ X) [IsClosedImmersion i]
    (hker : i.ker ≤ X.nilradical) [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) := by
  have hL' : IsInvertible Z.presheaf (structureSheafRing Z.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Z.presheaf _ L).mpr hL
  obtain ⟨G, C, centerGen, haff⟩ :=
    nonempty_chartData_isAffineOpen_inf_of_topologicalKrullDim_le_one i hdim L
  exact exists_modulePullback_iso_of_starChartData_of_ker_le_nilradical i hker L C centerGen
    fun p => Or.inr (haff p)

/-- **Tag 09NY for a surjective closed immersion.** An invertible module on a closed subscheme
whose underlying space is the whole of a scheme with Noetherian underlying space of dimension at
most one is the pullback of an invertible module on the ambient scheme.

Every hypothesis here is topological. For a closed immersion, surjectivity of the underlying map
is exactly `i.ker ≤ X.nilradical` (`Stacks.LiftInvertible.ker_le_nilradical_of_surjective`),
which is what makes the transition units lift, and it holds in particular for the inclusion of
the reduction `X_red ⟶ X` of any scheme whatever — the instance of Tag 09NY that
[Stacks, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ) consumes. A morphism carrying
`AlgebraicGeometry.Surjective` supplies the hypothesis as `i.surjective`.

The tag is withheld: Tag 09NY asks for **every** closed immersion into such an `X`, and a closed
immersion that is not onto is a genuinely different problem — see the implementation notes. -/
theorem exists_modulePullback_iso_of_surjective (i : Z ⟶ X) [IsClosedImmersion i]
    (hsurj : Function.Surjective i.base) [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  exists_modulePullback_iso_of_ker_le_nilradical i
    (ker_le_nilradical_of_surjective i hsurj) hdim L hL

/-- **Tag 09NY for a closed immersion with nilpotent ideal sheaf.** The special case of
`Stacks.LiftInvertible.exists_modulePullback_iso_of_ker_le_nilradical` in which the ideal sheaf
has a uniform nilpotency exponent; equivalently, the special case of
`Stacks.LiftInvertible.exists_modulePullback_iso_of_surjective` carrying a hypothesis that
implies surjectivity. The tag is withheld: Tag 09NY has no hypothesis on the ideal sheaf. -/
theorem exists_modulePullback_iso_of_isNilpotent_ker (i : Z ⟶ X) [IsClosedImmersion i]
    (hnil : IsNilpotent i.ker) [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  exists_modulePullback_iso_of_ker_le_nilradical i
    (ker_le_nilradical_of_isNilpotent i hnil) hdim L hL

end Stacks.LiftInvertible

end
