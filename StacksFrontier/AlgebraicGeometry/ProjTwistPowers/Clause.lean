module

public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.ChartBasis.Basic
public import StacksFrontier.AlgebraicGeometry.ProjDegreeOneTriv.Basic
public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.AffineSectionBasis
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Reverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 01VN's `ProjOneBasisClause` reduced to one statement about standard opens

`StacksFrontier/AlgebraicGeometry/ChartBasis/Basic.lean` reduces Stacks Tag 01VN to a
single absolute input, `Stacks.Tag01VNChartBasis.ProjOneBasisClause`: for `𝒜` generated in degree
one over `𝒜 0`, the opens `(Proj 𝒜)_s`, for `s` a global section of a positive tensor power of
`𝒪(1)`, form a basis for the topology. Its own documentation lists that input as two halves:

1. `(Proj 𝒜)_{degreeSection 𝒜 d a} = D₊(a)` for `a : 𝒜 d`, and
2. `𝒪(1) ^⊗ d ≅ 𝒪(d)`.

Half 2 is `ProjTwistPowers.tensorPowModuleIsoTwistingSheaf` in the sibling file. This file
performs the assembly, so that `ProjOneBasisClause` follows from half 1 alone
(`projOneBasisClause_of_nonvanishingLocusDegreeSection`), and then **proves half 1**
(`nonvanishingLocusDegreeSection`), so that **`ProjOneBasisClause` is a theorem**
(`projOneBasisClause`) and Stacks Tag 01VN is unconditional.

## Half 1, from Tag 01MV

Half 1 is [Stacks, Tag 01MV] — `Stacks.AlgebraicGeometry.CommonDegreeTwist`
`.mem_nonvanishingLocus_degreeSection_iff'`, which computes the nonvanishing locus of the
degree-`nd` section attached to a homogeneous element at every point of the locus `W_d` where
the `d`-divisible twists are invertible. Taking `d = 1` and `n` the degree of the element, the
only thing to supply is that `W₁` is everything, and *that* is where degree-one generation is
used: every point lies in `D₊(g)` for some `g` of degree one
(`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne`), and `D₊(g · 1)`
is one of the standard opens whose union is `W₁` by [Stacks, Tag 01MU]. The degree index needs
the usual transport, since `d * 1` is not syntactically `d`.

## The assembly, and the step the lists did not name

Half 1 produces the open `D₊(a)`; the clause asks for a basis, so the standard opens have to be a
basis *by homogeneous elements of positive degree*, and that is a third step neither half
supplies. Mathlib's `AlgebraicGeometry.Proj.isBasis_basicOpen` gives `D₊(g)` for an **arbitrary**
`g`, and `AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj` splits that into the standard opens of
the homogeneous components of `g` — but a component can sit in degree **zero**, which the clause's
`1 ≤ n` forbids. `exists_pos_degree_basicOpen` closes that gap with the only extra input
degree-one generation provides: a degree-one `f` with `x ∈ D₊(f)`
(`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne`). Multiplying by it
raises the degree by one and shrinks the open, since `D₊(af) = D₊(a) ⊓ D₊(f)`; the point stays
inside because it lies in both. This is uniform in the degree of the component, so no case split
on whether that degree was already positive is needed.

## Half 1 NEEDS the degree-one hypothesis, and here is why

`NonvanishingLocusDegreeSection` below carries `Algebra.adjoin (𝒜 0) ↑(𝒜 1) = ⊤`, and that is not
bookkeeping: **without it the statement is false.** Take `R = k[u, w]` with `u` in degree `2` and
`w` in degree `3`, `d = 2`, `a = u`, and `x = (u)`, which is homogeneous, prime and relevant
(`w ∉ (u)`), so `x ∉ D₊(u)`. Every homogeneous element outside `(u)` has degree divisible by `3`,
so every fraction in the stalk `𝒪(2)_x` has numerator in a degree `≡ 2 (mod 3)`; every monomial of
such a degree is divisible by `u`; hence `𝒪(2)_x = 𝒪_{X,x} · (u/1)`, and a generator of a module
over a local ring is never in `𝔪_x` times it. So `x ∈ (Proj 𝒜)_{degreeSection 𝒜 2 u}` while
`x ∉ D₊(u)`. The first draft of this file stated half 1 without the hypothesis; the hypothesis is
in the statement of Tag 01VN's clause already, so nothing is lost by carrying it.

## Main definitions

* `NonvanishingLocusDegreeSection`: half 1, as a `Prop` quantified over every graded ring
  generated in degree one, in the universe shape `ProjOneBasisClause` uses.

## Main results

* `exists_pos_degree_basicOpen`: the positive-degree standard opens are a neighbourhood basis.
* `whereInvertible_one_eq_top`: `W₁ = Proj 𝒜` for `𝒜` generated in degree one.
* `nonvanishingLocusDegreeSection`: **half 1.**
* `projOneBasisClause_of_nonvanishingLocusDegreeSection`: **`ProjOneBasisClause` from half 1.**
* `projOneBasisClause`: **`ProjOneBasisClause`, unconditionally.**

## Implementation notes

`Stacks.AmpleTheory.coe_powNonvanishingOpen` is `rfl`, so the carrier of the clause's open **is**
`Stacks.Ample.nonvanishingLocus`; the equality of opens is therefore
`TopologicalSpace.Opens.ext` of an `Eq.trans` and no `rw` through that lemma is used — `rw`
does not fire on it, because the module argument has to be read at `(Proj 𝒜).Modules` while the
twisting sheaf is spelled over `sheafCompose … (structureSheaf 𝒜)` (§8.215's shape). For the same
reason `Stacks.Ample.nonvanishingLocus` and `nonvanishingLocus_congr` are applied with `X`, `M`
and `N` given explicitly: with `X` left implicit it cannot be solved from `M`'s type, since
`AlgebraicGeometry.Scheme.Modules` is a `def`.

## What is not done

No `stacks` attribute is attached here: `ProjOneBasisClause` is clause (3) of [Stacks, Tag 01Q3]
for one module on one scheme, not that tag, and Tag 01VN is the theorem it feeds, stated in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/VeryAmple.lean`.

## References

* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistPowers

/-- The nonvanishing-locus half of Tag 01VN's absolute residue: the locus where the global
section of `𝒪(d)` attached to a homogeneous `a` of degree `d` does not vanish is the standard
open `D₊(a)`. -/
def NonvanishingLocusDegreeSection : Prop :=
  ∀ {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (_hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set R)) = ⊤)
    (d : ℕ) (a : 𝒜 d),
    Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ))
        (degreeSection 𝒜 d a) =
      (AlgebraicGeometry.Proj.basicOpen 𝒜 (a : R) : Set (AlgebraicGeometry.Proj 𝒜))

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every point of an open of `Proj 𝒜` has a standard-open neighbourhood inside it cut out by a
homogeneous element of **positive** degree, when `𝒜` is generated in degree one. -/
theorem exists_pos_degree_basicOpen (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤)
    (x : AlgebraicGeometry.Proj 𝒜) (U : (AlgebraicGeometry.Proj 𝒜).Opens) (hx : x ∈ U) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (a : 𝒜 n),
      x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (a : S) ∧
        AlgebraicGeometry.Proj.basicOpen 𝒜 (a : S) ≤ U := by
  obtain ⟨V, ⟨g, rfl⟩, hxV, hVU⟩ :=
    (Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜)) hx
  rw [AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj] at hxV hVU
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxV
  have hiU : AlgebraicGeometry.Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i g) ≤ U :=
    le_trans (le_iSup (fun j : ℕ =>
      AlgebraicGeometry.Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 j g)) i) hVU
  obtain ⟨f, hxf⟩ := ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne 𝒜 hgen x
  refine ⟨i + 1, Nat.le_add_left 1 i,
    ⟨GradedRing.proj 𝒜 i g * (f : S),
      SetLike.mul_mem_graded (SetLike.coe_mem _) f.2⟩, ?_⟩
  rw [show ((⟨GradedRing.proj 𝒜 i g * (f : S), _⟩ : 𝒜 (i + 1)) : S)
      = GradedRing.proj 𝒜 i g * (f : S) from rfl,
    AlgebraicGeometry.Proj.basicOpen_mul]
  exact ⟨⟨hxi, hxf⟩, inf_le_left.trans hiU⟩

/-! ### Half 1, from Tag 01MV on the invertible locus -/

/-- **The invertible locus `W₁` is all of `Proj 𝒜` when `𝒜` is generated in degree one.** Every
point lies in `D₊(g)` for some `g` of degree one, and `D₊(g) = D₊(g · 1)` is one of the standard
opens `D₊(f h)` with `deg f = deg h + 1` whose union is `W₁` by [Stacks, Tag 01MU]. -/
theorem whereInvertible_one_eq_top (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤) :
    ProjInvertibleLocus.whereInvertible 𝒜 1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨g, hg⟩ := ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne 𝒜 hgen x
  rw [GoodOpenClose.whereInvertible_eq_iSup_basicOpen_mul 𝒜 1]
  refine Opens.mem_iSup.mpr ⟨0, Opens.mem_iSup.mpr
    ⟨⟨(g : S), by simp⟩, Opens.mem_iSup.mpr
      ⟨⟨1, SetLike.one_mem_graded 𝒜⟩, ?_⟩⟩⟩
  simpa using (AlgebraicGeometry.Proj.mem_basicOpen 𝒜 (g : S) x).mp hg

/-- **[Stacks, Tag 01MV] in degree one, with the degree carried by a separate index.** The twist
and the section are indexed by a natural number and `d * 1` is not syntactically `d`, so the
degree is supplied as an index `k` together with the equation `k = d * 1`, exactly as
`Stacks.AlgebraicGeometry.MorphismsIntoProj.mem_nonvanishingLocus_degreeSection_iff` does for
`1 * d`. -/
theorem mem_nonvanishingLocus_degreeSection_iff_of_eq {k d : ℕ} (hk : k = d * 1) (a : 𝒜 k)
    {x : ProjectiveSpectrum.top 𝒜}
    (hx : x ∈ ProjInvertibleLocus.whereInvertible 𝒜 1) :
    x ∈ Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒜)
        (twistingSheaf 𝒜 (k : ℤ)) (degreeSection 𝒜 k a) ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (a : S) := by
  subst hk
  exact CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff' 𝒜 1 d a hx

/-- **Half 1 of Tag 01VN's absolute input.** For a graded ring generated in degree one over its
degree-zero part, the global section of `𝒪(d)` attached to a homogeneous element `a` of degree
`d` is nonvanishing exactly on the standard open `D₊(a)`.

Degree-one generation enters only through `whereInvertible_one_eq_top`: it puts every point of
`Proj 𝒜` on the locus `W₁` where the twists are invertible, which is where
[Stacks, Tag 01MV] computes the nonvanishing locus. The hypothesis cannot be dropped — the module
documentation records a counterexample with generators in degrees `2` and `3`. -/
@[ega "II 2.6.3" "special case", ega "II 3.3.3" "affine base Y = Spec A"]
theorem nonvanishingLocusDegreeSection : NonvanishingLocusDegreeSection.{u, w} := by
  intro R σ' _ _ _ 𝒝 _ hgen d a
  refine Set.ext fun x => ?_
  refine mem_nonvanishingLocus_degreeSection_iff_of_eq 𝒝 (mul_one d).symm a ?_
  rw [whereInvertible_one_eq_top 𝒝 hgen]
  trivial

/-- **Tag 01VN's remaining absolute input reduced to its first half.** -/
theorem projOneBasisClause_of_nonvanishingLocusDegreeSection
    (h : NonvanishingLocusDegreeSection.{u, w}) :
    Stacks.Tag01VNChartBasis.ProjOneBasisClause.{u, w} := by
  intro R σ' _ _ _ 𝒜 _ hgen x U hx
  obtain ⟨n, hn, a, hxa, haU⟩ := exists_pos_degree_basicOpen 𝒜 hgen x U hx
  let _inst := TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin 𝒜 hgen 1
  have key : Stacks.AmpleTheory.powNonvanishingOpen (AlgebraicGeometry.Proj 𝒜)
        (twistingSheaf 𝒜 1) n
        (((tensorPowModuleIsoTwistingSheaf 𝒜 hgen (n : ℤ)).symm.hom.app ⊤)
          (degreeSection 𝒜 n a)) =
      AlgebraicGeometry.Proj.basicOpen 𝒜 (a : R) :=
    TopologicalSpace.Opens.ext
      ((Stacks.Ample.nonvanishingLocus_congr (X := AlgebraicGeometry.Proj 𝒜)
        (M := twistingSheaf 𝒜 (n : ℤ))
        (N := Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n)
        (tensorPowModuleIsoTwistingSheaf 𝒜 hgen (n : ℤ)).symm
        (degreeSection 𝒜 n a)).trans (h 𝒜 hgen n a))
  exact ⟨n, hn,
    ((tensorPowModuleIsoTwistingSheaf 𝒜 hgen (n : ℤ)).symm.hom.app ⊤) (degreeSection 𝒜 n a),
    key ▸ hxa, key ▸ haU⟩

/-- **Tag 01VN's remaining absolute input, unconditionally.** For a graded ring generated in
degree one over its degree-zero part, the opens `(Proj 𝒜)_s`, for `s` a global section of a
positive tensor power of `𝒪(1)`, form a basis for the topology of `Proj 𝒜`. -/
theorem projOneBasisClause : Stacks.Tag01VNChartBasis.ProjOneBasisClause.{u, w} :=
  projOneBasisClause_of_nonvanishingLocusDegreeSection nonvanishingLocusDegreeSection

end Stacks.AlgebraicGeometry.ProjTwistPowers

end
