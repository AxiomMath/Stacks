module

public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# The trivializing section of `𝒪(nd)` is the global section attached to `f ^ n`

Let `S` be a nonnegatively graded ring, `X = Proj(S)` and `f ∈ S` homogeneous of degree `d`.
[Stacks, Tag 01MS] trivializes `𝒪_X(nd)` over the standard open `D₊(f)` by the fraction
`f ^ n / f ^ 0`, and [Stacks, Tag 01MP] attaches to the homogeneous element `f ^ n` of degree
`n d` a *global* section `degreeSection 𝒮 (n * d) (f ^ n)` of `𝒪_X(nd)`. This file identifies
the two in **every** degree `d` and at **every** nonnegative index `n`: the Tag 01MS
trivializing section is the restriction of that global section.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTrivialization.powSection`: the restriction of
  `degreeSection 𝒮 (n * d) (f ^ n)` to an open of `D₊(f)`, in the type the Tag 01MS
  trivialization uses.

## Main results

* `Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun_natCast`: at a nonnegative
  index the trivializing fraction is `f ^ n / 1`.
* `Stacks.AlgebraicGeometry.ProjTrivialization.powSection_eq_trivializingSection`: **the
  trivializing section of `𝒪(nd)` on `D₊(f)` is the restriction of the global section of Tag
  01MP attached to `f ^ n`**, for arbitrary `d` and arbitrary `n : ℕ`.
* `Stacks.AlgebraicGeometry.ProjTrivialization.bijective_smul_powSection` and
  `existsUnique_smul_powSection`: consequently `degreeSection 𝒮 (n * d) (f ^ n)` freely
  generates `𝒪(nd)` on every open of `D₊(f)`.
* `Stacks.AlgebraicGeometry.ProjTrivialization.degreeSectionRestrict_eq_trivializingSection`:
  the case `n = 1`, which says that the global section `f / 1` of `𝒪(d)` is the trivializing
  section of `𝒪(1 * d)`.

## Implementation notes

**Why the degree index needs no transport.** `trivializingSection 𝒮 hf n hW` is a section of
the twist indexed by `n * d` with `n : ℤ` and `d : ℕ`, that is by `(n : ℤ) * ((d : ℕ) : ℤ)`,
whereas the global section of Tag 01MP is indexed by the natural number `n * d` cast to `ℤ`.
Those two indices are definitionally equal — `Int.mul` of two `Int.ofNat`s reduces to the
`Int.ofNat` of the product — so `powSection` may be *stated* at the index the trivialization
writes and *built* from the global section, with no `eqToHom` and no `▸`.

**The fraction is the same object on both sides.** `Localization P` and `LocalizedModule P S`
both unfold to `OreLocalization P S`, so the trivializing fraction `f ^ n / f ^ 0` and the
Tag 01MP fraction `f ^ n / 1` live in one type and differ by `pow_zero`, which
`LocalizedModule.mk_eq` absorbs.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/


@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.AlgebraicGeometry.ProjTrivialization

universe u w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {f : S}

/-- The value of the trivializing section of `𝒪(nd)` on `D₊(f)` at a nonnegative index `n` is
the fraction `f ^ n / 1`: the numerator is `f ^ n` and the denominator `f ^ 0 = 1`. -/
public theorem trivializingFun_natCast (n : ℕ) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W) :
    trivializingFun 𝒮 (n : ℤ) hW x =
      LocalizedModule.mk (f ^ n) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  LocalizedModule.mk_eq.mpr ⟨1, by simp⟩

/-- `f ^ n` is homogeneous of degree `n * d` when `f` is homogeneous of degree `d`. -/
public theorem pow_mem_graded_mul {d : ℕ} (hf : f ∈ 𝒮 d) (n : ℕ) : f ^ n ∈ 𝒮 (n * d) := by
  simpa using SetLike.pow_mem_graded n hf

/-- The restriction of the global section `degreeSection 𝒮 (n * d) (f ^ n)` of `𝒪(nd)` to an
open contained in `D₊(f)`, written with the twist index in the form the Tag 01MS
trivialization uses. -/
public noncomputable def powSection {d : ℕ} (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (_hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    moduleSections 𝒮 (twistGrading (S := S) 𝒮 ((n : ℤ) * ((d : ℕ) : ℤ))) W :=
  (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val.map (homOfLE (le_top : W ≤ ⊤)).op
    (degreeSection 𝒮 (n * d) ⟨f ^ n, pow_mem_graded_mul 𝒮 hf n⟩)

/-- **The trivializing section of Tag 01MS is the global section of Tag 01MP attached to
`f ^ n`.** For `f` homogeneous of degree `d` and any `n : ℕ`, the trivialization of `𝒪(nd)`
over `D₊(f)` is multiplication by the restriction of the global section that `f ^ n`
determines. -/
public theorem powSection_eq_trivializingSection {d : ℕ} (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    powSection 𝒮 hf n hW = trivializingSection 𝒮 hf (n : ℤ) hW :=
  Subtype.ext (funext fun x =>
    (degreeSection_apply 𝒮 (n * d) ⟨f ^ n, pow_mem_graded_mul 𝒮 hf n⟩ _).trans
      (trivializingFun_natCast 𝒮 n hW x).symm)

/-- **`f ^ n` freely generates `𝒪(nd)` on the standard open of `f`.** On every open contained
in `D₊(f)`, multiplication by the restriction of `degreeSection 𝒮 (n * d) (f ^ n)` is a
bijection from the sections of the structure sheaf onto the sections of `𝒪(nd)`. -/
public theorem bijective_smul_powSection {d : ℕ} (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective (fun r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) =>
      r • powSection 𝒮 hf n hW) :=
  powSection_eq_trivializingSection 𝒮 hf n hW ▸ bijective_trivializingHom 𝒮 hf (n : ℤ) hW

/-- Every section of `𝒪(nd)` over an open of `D₊(f)` is a unique multiple of the restriction
of `degreeSection 𝒮 (n * d) (f ^ n)`. -/
public theorem existsUnique_smul_powSection {d : ℕ} (hf : f ∈ 𝒮 d) (n : ℕ)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading (S := S) 𝒮 ((n : ℤ) * ((d : ℕ) : ℤ))) W) :
    ∃! r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W),
      r • powSection 𝒮 hf n hW = a :=
  (bijective_smul_powSection 𝒮 hf n hW).existsUnique a

/-- **At `n = 1`: the global section `f / 1` of `𝒪(d)` is the trivializing section of Tag
01MS**, for `f` homogeneous of *any* degree `d`. -/
public theorem degreeSectionRestrict_eq_trivializingSection {d : ℕ} (hf : f ∈ 𝒮 d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    powSection 𝒮 hf 1 hW = trivializingSection 𝒮 hf (1 : ℤ) hW :=
  powSection_eq_trivializingSection 𝒮 hf 1 hW

end Stacks.AlgebraicGeometry.ProjTrivialization

end
