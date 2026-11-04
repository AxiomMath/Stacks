module

public import StacksFrontier.AlgebraicGeometry.AmpleCluster.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import Mathlib.Order.Preorder.Finite

/-!
# One global section of an invertible module nonvanishing on a finite set, quasi-affinely

Stacks Tag 0F20 says that on a quasi-affine scheme `X`, for every invertible `𝒪_X`-module `L` and
every finite `E` inside an open `W`, some global section `s ∈ Γ(X, L)` has `X_s` affine with
`E ⊆ X_s ⊆ W`. This file proves that conclusion from exactly two named inputs, and in particular
removes the source's induction on `#E`, its reduced closed subscheme structure on `X ∖ W`, and its
quasi-coherent ideal sheaf of that complement.

## The two inputs

* **Pointwise global generation**: for every `y ∈ X` some global section of `L` does not vanish at
  `y`. On a quasi-affine scheme this is the source's "quasi-coherent `𝒪_X`-modules are globally
  generated" (Stacks Tags 01QE and 01PZ), which is absent from this repository and from Mathlib.
  It is taken here as the hypothesis `hgen`.
* **Stacks Tag 01PV**: `U ⊓ X_s` is affine for every affine open `U`. Carried as
  `Stacks.QuasiAffineFiniteNonvanishing.IsAffineNonvanishingOfLe`, the degree-free analogue of
  `Stacks.AmpleTheory.IsAffineOfLeAffine`, which is how the ample cluster already carries it.

Everything between them is proved here.

## The route, and why there is no induction

Write `A = Γ(X, 𝒪_X)`. The lemma
`Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine` is prime avoidance in `A`:
a finite `E ⊆ W` lies in `X.basicOpen g` for a single `g : A`, with that basic open affine and
inside `W`. Three uses of it carry the whole argument.

1. **Separation.** A finite set of points no one of which is a specialization of another is
   discrete: for `y` in it, the complement of the closure of the other points is an open
   neighbourhood of `y` meeting the set only in `y`. Avoidance inside that neighbourhood produces
   `g y : A` with `y ∈ X_{g y}` and `z ∉ X_{g y}` for every other `z`.
2. **One section from many.** With `s y` a global section not vanishing at `y`, the single section
   `∑ y, g y • s y` does not vanish at any point of the set: at `z` exactly one summand survives,
   because `X_{r • s} = X.basicOpen r ∩ X_s` (`Stacks.Ample.nonvanishingLocus_smul`) and the other
   germs lie in `𝔪_z · L_z`, a submodule.
3. **Confinement to `W`, and affineness.** For the final section, avoidance gives `g` with
   `E ⊆ X.basicOpen g ≤ W` and `X.basicOpen g` affine; then `X_{g • s} = X.basicOpen g ∩ X_s`
   still contains `E`, lies inside `W`, and lies inside an affine open, so Tag 01PV makes it
   affine.

The specialization hypothesis of step 1 is discharged, not assumed: a scheme is `T0`, so the
specialization relation is a partial order, and replacing `E` by the finitely many points of `E`
maximal for it changes nothing, since `X_s` is open and an open set containing a point contains
every point it specializes from.

## Main definitions

* `Stacks.QuasiAffineFiniteNonvanishing.IsAffineNonvanishingOfLe`: the consequence of Stacks Tag
  01PV consumed below.

## Main results

* `Stacks.QuasiAffineFiniteNonvanishing.exists_nonvanishing_containing_finite`: on a quasi-affine
  scheme, if some global section of an invertible `L` fails to vanish at each prescribed point,
  then **one** global section fails to vanish at every point of a finite set.
* `Stacks.QuasiAffineFiniteNonvanishing.exists_affine_nonvanishingOpen_of_nonvanishing`: given one
  such section, Stacks Tag 0F20's conclusion, on Tag 01PV.
* `Stacks.QuasiAffineFiniteNonvanishing.exists_affine_nonvanishingOpen_containing_finite`: **Stacks
  Tag 0F20 from the two inputs above.**

## Implementation notes

The nonvanishing locus is bundled as an open by `Stacks.NonvanishingOpen.nonvanishingOpen`, whose
openness theorem (Stacks Tag 01CY for a scheme) is proved; by contrast
`Stacks.AmpleCluster.exists_affine_nonvanishingLocus_containing_finite_of_nonvanishingBasis`
(`StacksFrontier/AlgebraicGeometry/AmpleCluster/NonvanishingBasisAffineLocus.lean`) states its
conclusion with an existentially produced open, because it does not use that openness.

`Specializes` is Mathlib's, in Mathlib's direction: `x ⤳ y` is `y ∈ closure {x}`, and
`Specializes.mem_open` reads "if `x ⤳ y` and `y` is in an open set then so is `x`". The partial
order used for the maximality argument is therefore built by hand with `le := (· ⤳ ·)`; Mathlib's
`specializationPreorder` is the opposite one.

## References

* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)

## What is not done

No `stacks` attribute is attached, and Tag 0F20 is not proved outright *here*: `hgen` is a
hypothesis, and so is Tag 01PV. Neither is a gap in the repository. Tag 01PV is proved, as
`Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`
(`../NonvanishingAffineIntersection/Basic.lean`), and Tag 0F20 itself is proved and attached in
`../QuasiAffineGlobalGeneration/Basic.lean`, by a route that needs Tag 01PV not at all. What this
file keeps as hypotheses, it keeps because nothing below applies either result.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.ModuleStalk Stacks.NonvanishingOpen

universe u

namespace Stacks.QuasiAffineFiniteNonvanishing

/-! ### Finite sets and the specialization order -/

section Topology

variable {Y : Type u} [TopologicalSpace Y]

/-- Every point of a finite set lies, in the specialization order, below a point of the set that
specializes to no other point of the set. The order is `x ≤ y ↔ x ⤳ y`, which is antisymmetric
because the space is `T0`. -/
theorem exists_specializes_maximal [T0Space Y] {E : Set Y} (hE : E.Finite) {x : Y} (hx : x ∈ E) :
    ∃ y ∈ E, x ⤳ y ∧ ∀ z ∈ E, y ⤳ z → z = y := by
  let _ : Preorder Y :=
    { le := fun a b => a ⤳ b
      le_refl := fun a => specializes_refl a
      le_trans := fun _ _ _ h₁ h₂ => h₁.trans h₂ }
  obtain ⟨y, hxy, hy⟩ := hE.exists_le_maximal hx
  exact ⟨y, hy.1, hxy, fun z hz hyz => (hyz.antisymm (hy.2 hz hyz)).eq.symm⟩

/-- A point of a finite set which no other point of the set specializes to is outside the closure
of the other points. This is the discreteness that makes the separation step below possible. -/
theorem notMem_closure_sdiff_singleton {E : Set Y} (hE : E.Finite) {y : Y}
    (h : ∀ z ∈ E, z ⤳ y → z = y) : y ∉ closure (E \ {y}) := by
  rw [← Set.biUnion_of_singleton (E \ {y}), (hE.sdiff (t := {y})).closure_biUnion]
  simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
  intro z hz hmem
  exact hz.2 (h z hz.1 (specializes_iff_mem_closure.mpr hmem))

end Topology

/-! ### A sum of global sections at a point where exactly one summand survives -/

variable {X : Scheme.{u}}

/-- **A sum of global sections does not vanish where exactly one summand does not vanish.** The
germs of the other summands lie in the submodule `𝔪_x · M_x`, so they cannot cancel the surviving
one. Together with `Stacks.Ample.nonvanishingLocus_smul` this replaces the source's induction on
the size of the finite set. -/
theorem mem_nonvanishingLocus_sum {M : X.Modules} {ι : Type*} (t : Finset ι) (f : ι → Γ(M, ⊤))
    {x : X} {i : ι} (hi : i ∈ t) (hix : x ∈ nonvanishingLocus M (f i))
    (hother : ∀ j ∈ t, j ≠ i → x ∉ nonvanishingLocus M (f j)) :
    x ∈ nonvanishingLocus M (∑ j ∈ t, f j) := by
  classical
  have hrest : ∑ j ∈ t.erase i, (M.presheaf.Γgerm x).hom (f j) ∈ maximalSmul M x := by
    refine Submodule.sum_mem _ fun j hj => ?_
    have h := hother j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
    rw [mem_nonvanishingLocus_iff, not_not] at h
    exact h
  have hsplit : (M.presheaf.Γgerm x).hom (∑ j ∈ t, f j) =
      (M.presheaf.Γgerm x).hom (f i) + ∑ j ∈ t.erase i, (M.presheaf.Γgerm x).hom (f j) := by
    rw [map_sum]
    exact (Finset.add_sum_erase t _ hi).symm
  rw [mem_nonvanishingLocus_iff]
  intro hmem
  rw [hsplit] at hmem
  refine hix ?_
  simpa using Submodule.sub_mem _ hmem hrest

/-! ### Separating the points of a finite set by basic opens -/

/-- **On a quasi-affine scheme a point of a finite set with no other point of the set specializing
to it is cut out from the set by a basic open.** Prime avoidance in `Γ(X, 𝒪_X)` is applied inside
the complement of the closure of the other points. -/
theorem exists_basicOpen_separating [X.IsQuasiAffine] {E : Set X} (hE : E.Finite) {y : X}
    (hy : ∀ z ∈ E, z ⤳ y → z = y) :
    ∃ g : Γ(X, ⊤), y ∈ X.basicOpen g ∧ ∀ z ∈ E, z ≠ y → z ∉ X.basicOpen g := by
  obtain ⟨g, -, hyg, hgW⟩ :=
    Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine
      (X := X) (Set.finite_singleton y) ⟨(closure (E \ {y}))ᶜ, isClosed_closure.isOpen_compl⟩
      (Set.singleton_subset_iff.mpr (notMem_closure_sdiff_singleton hE hy))
  refine ⟨g, hyg rfl, fun z hz hzy hzg => ?_⟩
  exact hgW hzg (subset_closure ⟨hz, hzy⟩)

/-! ### One section nonvanishing on a whole finite set -/

/-- **One global section not vanishing at any point of a finite set of pairwise non-specializing
points**, from one such section per point. The section produced is `∑ y, g y • s y` with `g y`
separating `y` from the other points. -/
theorem exists_nonvanishing_of_separated [X.IsQuasiAffine] (M : X.Modules) {E : Set X}
    (hE : E.Finite) (hsep : ∀ y ∈ E, ∀ z ∈ E, z ⤳ y → z = y)
    (hgen : ∀ y ∈ E, ∃ s : Γ(M, ⊤), y ∈ nonvanishingLocus M s) :
    ∃ s : Γ(M, ⊤), E ⊆ nonvanishingLocus M s := by
  classical
  have key : ∀ y : X, ∃ p : Γ(X, ⊤) × Γ(M, ⊤), y ∈ E →
      y ∈ X.basicOpen p.1 ∧ (∀ z ∈ E, z ≠ y → z ∉ X.basicOpen p.1) ∧
        y ∈ nonvanishingLocus M p.2 := by
    intro y
    by_cases hy : y ∈ E
    · obtain ⟨sy, hsy⟩ := hgen y hy
      obtain ⟨g, hyg, hzg⟩ := exists_basicOpen_separating hE (hsep y hy)
      exact ⟨(g, sy), fun _ => ⟨hyg, hzg, hsy⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hy⟩
  choose p hp using key
  refine ⟨∑ y ∈ hE.toFinset, (p y).1 • (p y).2, fun x hx => ?_⟩
  refine mem_nonvanishingLocus_sum _ _ (hE.mem_toFinset.mpr hx) ?_ ?_
  · rw [nonvanishingLocus_smul]
    exact ⟨(hp x hx).1, (hp x hx).2.2⟩
  · intro y hy hyx
    rw [nonvanishingLocus_smul]
    intro hcon
    exact (hp y (hE.mem_toFinset.mp hy)).2.1 x hx (Ne.symm hyx) hcon.1

/-- **One global section of an invertible module not vanishing at any point of a finite set**, on a
quasi-affine scheme, from one such section per point of the space. The specialization hypothesis of
`exists_nonvanishing_of_separated` is discharged here: a scheme is `T0`, and a nonvanishing locus is
open, so it suffices to treat the specialization-maximal points of the finite set. -/
theorem exists_nonvanishing_containing_finite [X.IsQuasiAffine] (M : X.Modules)
    [IsInvertibleModule X M] {E : Set X} (hE : E.Finite)
    (hgen : ∀ y ∈ E, ∃ s : Γ(M, ⊤), y ∈ nonvanishingLocus M s) :
    ∃ s : Γ(M, ⊤), E ⊆ nonvanishingLocus M s := by
  classical
  choose! f hfE hxf hfmax using fun x (hx : x ∈ E) => exists_specializes_maximal hE hx
  have hsub : f '' E ⊆ E := by rintro _ ⟨x, hx, rfl⟩; exact hfE x hx
  have hsep : ∀ y ∈ f '' E, ∀ z ∈ f '' E, z ⤳ y → z = y := by
    rintro y hy _ ⟨x, hx, rfl⟩ hzy
    exact (hfmax x hx y (hsub hy) hzy).symm
  obtain ⟨s, hs⟩ := exists_nonvanishing_of_separated M (hE.image f) hsep
    fun y hy => hgen y (hsub hy)
  refine ⟨s, fun x hx => ?_⟩
  exact (hxf x hx).mem_open (isOpen_nonvanishingLocus X M s) (hs ⟨x, hx, rfl⟩)

/-! ### Stacks Tag 0F20 -/

/-- Every nonvanishing locus of a global section of `L` that is contained in an affine open is
itself affine. -/
def IsAffineNonvanishingOfLe (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] : Prop :=
  ∀ (s : Γ(L, ⊤)) (U : X.Opens), IsAffineOpen U → nonvanishingOpen X L s ≤ U →
    IsAffineOpen (nonvanishingOpen X L s)

/-- **Stacks Tag 0F20 from one nonvanishing section**, on Stacks Tag 01PV. Given a global section of
`L` not vanishing anywhere on the finite set `E`, scaling it by the avoidance section `g` of
`Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine` confines its nonvanishing
locus to the affine `X.basicOpen g ≤ W` without losing any point of `E`. -/
theorem exists_affine_nonvanishingOpen_of_nonvanishing [X.IsQuasiAffine] (L : X.Modules)
    [IsInvertibleModule X L] (hPV : IsAffineNonvanishingOfLe X L) {E : Set X} (hE : E.Finite)
    (W : X.Opens) (hEW : E ⊆ (W : Set X)) {s₀ : Γ(L, ⊤)} (hs₀ : E ⊆ nonvanishingLocus L s₀) :
    ∃ s : Γ(L, ⊤), IsAffineOpen (nonvanishingOpen X L s) ∧
      E ⊆ (nonvanishingOpen X L s : Set X) ∧ nonvanishingOpen X L s ≤ W := by
  obtain ⟨g, haff, hEg, hgW⟩ :=
    Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine hE W hEW
  have hle : nonvanishingOpen X L (g • s₀) ≤ X.basicOpen g := fun x hx =>
    ((nonvanishingLocus_smul L g s₀).subset hx).1
  refine ⟨g • s₀, hPV _ _ haff hle, fun x hx => ?_, hle.trans hgW⟩
  exact (nonvanishingLocus_smul L g s₀).ge ⟨hEg hx, hs₀ hx⟩

/-- **Stacks Tag 0F20 on two inputs.** On a quasi-affine scheme, if every point of `X` has a global
section of the invertible module `L` not vanishing there (global generation of `L`, Stacks Tag
01PZ), and Stacks Tag 01PV holds in the form `IsAffineNonvanishingOfLe`, then every finite subset of
an open `W` lies in an affine nonvanishing locus `X_s ≤ W` of a global section of `L`. -/
theorem exists_affine_nonvanishingOpen_containing_finite [X.IsQuasiAffine] (L : X.Modules)
    [IsInvertibleModule X L] (hPV : IsAffineNonvanishingOfLe X L)
    (hgen : ∀ y : X, ∃ s : Γ(L, ⊤), y ∈ nonvanishingLocus L s) {E : Set X} (hE : E.Finite)
    (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ s : Γ(L, ⊤), IsAffineOpen (nonvanishingOpen X L s) ∧
      E ⊆ (nonvanishingOpen X L s : Set X) ∧ nonvanishingOpen X L s ≤ W := by
  obtain ⟨s₀, hs₀⟩ := exists_nonvanishing_containing_finite L hE fun y _ => hgen y
  exact exists_affine_nonvanishingOpen_of_nonvanishing L hPV hE W hEW hs₀

end Stacks.QuasiAffineFiniteNonvanishing

end
