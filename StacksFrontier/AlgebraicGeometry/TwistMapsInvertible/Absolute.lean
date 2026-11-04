module

public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Basic
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twists on an absolute `Proj` are invertible when the ring is generated in degree one

Let `S` be a nonnegatively graded commutative ring. The twisting sheaf `𝒪(c)` on `Proj S` is
trivialized on the standard open `D₊(pq)` whenever `p` and `q` are homogeneous with
`deg p = deg q + d` and `c = nd`; that is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioOverIsoUnit`. When the ratio locus `W_d` is all
of `Proj S` — in particular when `S` is generated in degree one over `S₀`, by
`Stacks.AlgebraicGeometry.ProjTwistMono.ratioLocus_eq_top_of_adjoin_coe_degree_one` — those
standard opens cover `Proj S`, so every `𝒪(nd)` is trivial near every point and hence invertible.

## Main results

* `Stacks.AlgebraicGeometry.TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf`: at a
  point of the ratio locus `W_d`, the twist `𝒪(nd)` is trivial on a standard open neighbourhood.
* `exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin`, in the same namespace:
  under generation in degree one, every `𝒪(n)` is trivial near every point, with no restriction on
  the twist index.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin`:
  **every twist on `Proj S` is an invertible `𝒪`-module when `S` is generated in degree one over
  its degree-zero part.** This is Tag 01MW at `d = 1` and `Y = Proj S`, stated on `Proj S` itself
  rather than on the pullback to an open subscheme.

## Overlap with a sibling result

`Stacks.TwistFlatness.isInvertible_twistingSheaf_of_adjoin_degree_one`
(`StacksFrontier/AlgebraicGeometry/TwistFlatness/Basic.lean`) proves the same absolute
conclusion for `Stacks.SheafOfModules.IsInvertible` — the
repository's *other* class carrying the Tag 01CS label — by a different route, namely
`Stacks.SheafDescent.isInvertible_of_trivialization` over the whole family of ratio opens at once.
`isInvertibleModule_twistingSheaf_of_adjoin` below is the same statement for
`AlgebraicGeometry.SheafOfModules.IsInvertible`, which is the class
`Stacks.Ample.IsInvertibleModule` abbreviates and the one Tag 01MW is stated in; the two classes
are distinct constants, so each spelling needs its own declaration. It is **not** what the relative
statement of Tag 01O4 consumes: that consumes the *pointwise, restriction-level* trivialization
`exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin`, because the descent is performed once, on
the relative `Proj`, rather than twice. Should the two be unified, the pointwise form is the one to
keep: global invertibility is recovered from it in one line, while recovering it from global
invertibility costs a round trip through Tag 0B8M.

## Implementation notes

The trivialization is read off the ratio locus pointwise rather than as a covering family, which
is why no descent and no indexing type appears: `ratioOverIsoUnit` lives on the slice site, and
`Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit` moves it to the open
subscheme. `StacksFrontier/AlgebraicGeometry/ProjInvertibleLocus/Trivialization.lean` records that
building the trivialization directly on the open subscheme does not work, so going through the
slice site is not a detour.

The twist index is carried as an independent variable `c` with the hypothesis `c = n * d`, exactly
as `ratioOverIsoUnit` carries it, so that the statement applies to `d * n` and to `n * d` alike.
At `d = 1` the hypothesis is discharged for `c = n` and the twist index is unrestricted; this is
why degree-one generation gives all the twists and not only a divisible subfamily.

The transparency attributes are the ones the absolute-twist files need: the sheaf of rings over
which the twists are modules is `ProjectiveSpectrum.Proj.structureSheaf` composed with the
forgetful functor, while `AlgebraicGeometry.Scheme.Modules` of `Proj S` is indexed by that
scheme's own `ringCatSheaf`, and the two are `rfl`-equal only once those wrappers are reducible.

## References

* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInvertibleLocus

namespace Stacks.AlgebraicGeometry.TwistMapsInvertible

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **At a point of the ratio locus `W_d`, the twist `𝒪(nd)` is trivial on a standard open
neighbourhood.** The point omits a product `pq` with `deg p = deg q + d`, and `𝒪(nd)` is
trivialized on `D₊(pq)` by `(p/q)^n`. -/
theorem exists_mem_restrict_isoUnit_twistingSheaf {d : ℕ} {n c : ℤ} (hc : (n : ℤ) * d = c)
    {x : AlgebraicGeometry.Proj 𝒜} (hx : x ∈ ProjShared.ratioLocus 𝒜 d) :
    ∃ V : (AlgebraicGeometry.Proj 𝒜).Opens, x ∈ V ∧
      Nonempty (Scheme.Modules.restrict (Y := AlgebraicGeometry.Proj 𝒜)
          (twistingSheaf 𝒜 c) V.ι ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  obtain ⟨e, f, g, hf, hg, hfx, hgx⟩ := (ProjShared.mem_ratioLocus_iff 𝒜 d x).mp hx
  exact ⟨ProjectiveSpectrum.basicOpen 𝒜 (f * g),
    fun hmul => (x.isPrime.mem_or_mem hmul).elim hfx hgx,
    ⟨restrictIsoUnitOfOverIsoUnit _ _ (ratioOverIsoUnit 𝒜 hf hg hc)⟩⟩

/-- **Under generation in degree one every twist is trivial near every point**, with no
restriction on the twist index: the degree-one ratio locus is all of `Proj S`, and at `d = 1`
every integer `n` is of the form `nd`. -/
theorem exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) (n : ℤ)
    (x : AlgebraicGeometry.Proj 𝒜) :
    ∃ V : (AlgebraicGeometry.Proj 𝒜).Opens, x ∈ V ∧
      Nonempty (Scheme.Modules.restrict (Y := AlgebraicGeometry.Proj 𝒜)
          (twistingSheaf 𝒜 n) V.ι ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf) :=
  exists_mem_restrict_isoUnit_twistingSheaf 𝒜 (d := 1) (n := n) (c := n) (by simp)
    ((ProjTwistMono.ratioLocus_eq_top_of_adjoin_coe_degree_one 𝒜 hgen 1).ge
      (TopologicalSpace.Opens.mem_top x))

/-- **Every twist on `Proj S` is invertible when `S` is generated in degree one over `S₀`.**
Tag 01MW at `d = 1` and `Y = Proj S`, stated on `Proj S` itself: the standard opens `D₊(f)` for
`f` homogeneous of degree one cover `Proj S` and trivialize every `𝒪(n)`. -/
@[ega "II 2.6.1" "more general", ega "II 3.2.5" "special case"]
theorem isInvertibleModule_twistingSheaf_of_adjoin
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 n) :=
  isInvertibleModule_of_forall_exists_restrict_isoUnit _
    (exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin 𝒜 hgen n)

end Stacks.AlgebraicGeometry.TwistMapsInvertible

end
