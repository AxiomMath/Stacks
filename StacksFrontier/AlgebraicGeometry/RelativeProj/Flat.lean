module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.LocalAtBase

/-!
# Flatness of `Proj` over the spectrum of its degree-zero part

Let `𝒜` be a nonnegatively graded ring with degree-zero part `𝒜 0`. The scheme `Proj 𝒜` is
covered by the affine opens `D₊(f)` for `f` homogeneous of positive degree, and the chart over
`D₊(f)` is the spectrum of the degree-zero homogeneous localization
`HomogeneousLocalization.Away 𝒜 f`, as an algebra over `𝒜 0`. Since flatness of a morphism of
schemes is Zariski-local at the source, the structure morphism
`AlgebraicGeometry.Proj.toSpecZero` is flat as soon as every one of those algebras is flat.

This is the one input to the geometry of a relative `Proj` that is *not* supplied by a
finite-type hypothesis: Mathlib proves that `Proj.toSpecZero 𝒜` is proper, and in particular
locally of finite type, whenever `𝒜` is a finite-type `𝒜 0`-algebra, but `Proj 𝒜` is of course
not flat over `Spec (𝒜 0)` for a general such `𝒜` — the fibre dimension jumps. Flatness has to
come from the charts, and the criterion below is the reduction.

Combined with `Stacks.RelativeProj.Data.flat_toBase` this reduces flatness of a relative `Proj`
over its base to a statement of commutative algebra about one graded ring per affine open of the
base.

## Main results

* `AlgebraicGeometry.Proj.flat_toSpecZero_of_flat_away`: `Proj 𝒜` is flat over `Spec (𝒜 0)` as
  soon as `Away 𝒜 (g i)` is a flat `𝒜 0`-module for a family `g` of homogeneous elements of
  positive degree generating `𝒜` as an `𝒜 0`-algebra.
* `Stacks.RelativeProj.Data.flat_toBase_of_flat_away`: the same criterion applied chart by chart
  to the structure morphism of a relative `Proj`.

## Implementation notes

The generating family is given as an arbitrary indexed family together with a degree for each
member, rather than as a `Finset`: the covering lemma
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'` asks only that the range generate `𝒜` as an
`𝒜 0`-algebra, and the extra generality costs nothing. The degrees are required to be positive
because `D₊(f)` is affine with ring `Away 𝒜 f` only for `f` of positive degree.

Flatness of the chart is asked for as `Module.Flat (𝒜 0) (Away 𝒜 (g i))`, using the canonical
algebra structure, which is the form in which it will be proved; the bridge to the
`RingHom.Flat` of `HomogeneousLocalization.fromZeroRingHom` that the morphism-property API
produces is `RingHom.flat_algebraMap_iff`, the two ring homomorphisms being the same map.

No `@[stacks]` attribute is attached: nothing here is one of the assertions of a Stacks tag. The
flatness of a projective bundle is part of tag 02TX, whose statement is about the relative `Proj`
of a symmetric algebra; this is one input to it.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **`Proj 𝒜` is flat over `Spec (𝒜 0)` as soon as all of its standard affine charts are.**

If `g` is a family of homogeneous elements of positive degree which generates `𝒜` as an algebra
over its degree-zero part, the standard opens `D₊(g i)` cover `Proj 𝒜`, and the chart over
`D₊(g i)` is `Spec (Away 𝒜 (g i))` over `Spec (𝒜 0)`. Flatness being Zariski-local at the
source, flatness of each `Away 𝒜 (g i)` as an `𝒜 0`-module is enough. -/
theorem flat_toSpecZero_of_flat_away {ι : Type*} (g : ι → A) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hg : ∀ i, g i ∈ 𝒜 (m i))
    (hadj : Algebra.adjoin (𝒜 0) (Set.range g) = ⊤)
    (hflat : ∀ i, Module.Flat (𝒜 0) (Away 𝒜 (g i))) :
    Flat (Proj.toSpecZero 𝒜) := by
  have hsrc : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  have := hsrc.toRespects
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Flat) _
    (Proj.iSup_basicOpen_eq_top' 𝒜 g (fun i ↦ ⟨_, hg i⟩) hadj)]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat)
    (Proj.basicOpenIsoSpec 𝒜 (g i) (hg i) (hm i)).inv, ← Category.assoc,
    ← Proj.awayι, Proj.awayι_toSpecZero, HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr (hflat i)

end AlgebraicGeometry.Proj

namespace Stacks.RelativeProj.Data

variable {S : Scheme.{u}} {A σ : S.affineOpens → Type u} [∀ U, CommRing (A U)]
  [∀ U, SetLike (σ U) (A U)] [∀ U, AddSubgroupClass (σ U) (A U)]
  {𝒜 : ∀ U, ℕ → σ U} [∀ U, GradedRing (𝒜 U)] (d : Data 𝒜)

/-- **The structure morphism of a relative `Proj` is flat as soon as all the standard affine
charts of all the local `Proj`s are.** This is
`Stacks.RelativeProj.Data.flat_toBase` composed with
`AlgebraicGeometry.Proj.flat_toSpecZero_of_flat_away`: flatness over the base is reduced to a
statement of commutative algebra about one graded ring for each affine open of the base. -/
theorem flat_toBase_of_flat_away (hb : ∀ U : S.affineOpens, IsIso (d.base U))
    {ι : S.affineOpens → Type*} (g : ∀ U, ι U → A U) (m : ∀ U, ι U → ℕ)
    (hm : ∀ U i, 0 < m U i) (hg : ∀ U i, g U i ∈ 𝒜 U (m U i))
    (hadj : ∀ U, Algebra.adjoin (𝒜 U 0) (Set.range (g U)) = ⊤)
    (hflat : ∀ U i, Module.Flat (𝒜 U 0) (Away (𝒜 U) (g U i))) :
    Flat d.toBase :=
  d.flat_toBase hb fun U ↦
    Proj.flat_toSpecZero_of_flat_away (𝒜 U) (g U) (m U) (hm U) (hg U) (hadj U) (hflat U)

end Stacks.RelativeProj.Data

end
