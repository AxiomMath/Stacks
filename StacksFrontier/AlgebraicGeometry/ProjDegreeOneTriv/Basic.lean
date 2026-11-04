module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A degree-one element freely generates `𝒪(1)` on its own standard open

Let `S` be a nonnegatively graded ring, `X = Proj(S)` and `f ∈ S` homogeneous of degree one.
Tag 01MS trivializes `𝒪_X(1)` over the standard open `D₊(f)`, and Tag 01MP attaches to `f` a
global section `degreeSection 𝒮 1 f` of `𝒪_X(1)`. This file identifies the two: the trivializing
section of Tag 01MS *is* the restriction of `degreeSection 𝒮 1 f`, so on every open of `D₊(f)`
multiplication by that restriction is a bijection from the sections of the structure sheaf onto
the sections of `𝒪(1)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjDegreeOneTriv.degreeOneSection`: the restriction of
  `degreeSection 𝒮 1 f` to an open of `D₊(f)`, in the type the Tag 01MS trivialization uses.

## Main results

* `Stacks.AlgebraicGeometry.ProjDegreeOneTriv.degreeOneSection_eq_trivializingSection`: the
  restriction of `degreeSection 𝒮 1 f` is the trivializing section of Tag 01MS.
* `Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection`: on every open of
  `D₊(f)` the section `degreeSection 𝒮 1 f` is a free generator of `𝒪(1)`.
* `Stacks.AlgebraicGeometry.ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne`: when `S` is
  generated in degree one over its degree-zero part, every point of `Proj(S)` lies in `D₊(g)`
  for some homogeneous `g` of degree one. With the previous result this says that `𝒪(1)` is
  freely generated, near every point, by one of the global sections `degreeSection 𝒮 1 g`.

## Implementation notes

The two sheaf-theoretic halves were already present and only their composition was missing:
`Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection` is the single homogeneous
fraction `f ^ max n 0 / f ^ max (-n) 0`, which at `n = 1` and `deg f = 1` is `f / 1`, and
`Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply` says the value of
`degreeSection 𝒮 1 f` at every point is `f / 1` as well. Both fractions live in one type, because
`Localization P` and `LocalizedModule P S` both unfold to `OreLocalization P S`; the identity of
the denominators is `pow_zero`, which `LocalizedModule.mk_eq` absorbs.

**The degree index forces a typed definition.** `trivializingSection 𝒮 hf n hW` is a section
of the twist indexed by `n * d`, and for `hf : f ∈ 𝒮 1` and `n = 1` that reads
`(1 : ℤ) * ((1 : ℕ) : ℤ)` rather than `(1 : ℤ)`. The two indices are definitionally equal and
the equation between the two sections elaborates directly, but `▸` on it does not: the motive
has to abstract the *type* as well as the section, and that unification exceeded the default
heartbeat budget. `degreeOneSection` is the restriction with the twist index written the way the
trivialization writes it, which makes the rewrite in `bijective_smul_degreeOneSection` an
ordinary one between two elements of a single type.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.AlgebraicGeometry.ProjDegreeOneTriv

universe u w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {f : S}

/-- The value of the trivializing section of `𝒪(d)` on `D₊(f)` at index `1` is the fraction
`f / 1`: the numerator is `f ^ 1` and the denominator `f ^ 0 = 1`. -/
public theorem trivializingFun_one {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W) :
    trivializingFun 𝒮 (1 : ℤ) hW x =
      LocalizedModule.mk f (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  LocalizedModule.mk_eq.mpr ⟨1, by simp⟩

/-- The restriction of the global section `degreeSection 𝒮 1 f` of `𝒪(1)` to an open contained
in `D₊(f)`, written with the twist index in the form the Tag 01MS trivialization uses. -/
public noncomputable def degreeOneSection (hf : f ∈ 𝒮 1) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (_hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    moduleSections 𝒮 (twistGrading (S := S) 𝒮 ((1 : ℤ) * ((1 : ℕ) : ℤ))) W :=
  (twistingSheaf 𝒮 (1 : ℤ)).val.map (homOfLE (le_top : W ≤ ⊤)).op
    (degreeSection 𝒮 1 ⟨f, hf⟩)

/-- **The trivializing section of Tag 01MS is the degree-one section of Tag 01MP.** For `f`
homogeneous of degree one, the trivialization of `𝒪(1)` over `D₊(f)` is multiplication by the
restriction of the global section that `f` itself determines.

Both sides have the value `f / 1` at every point, by `degreeSection_apply` and
`trivializingFun_one`; sections of these sheaves are dependent functions into the local rings and
restriction is restriction of functions, so the two sections agree. -/
public theorem degreeOneSection_eq_trivializingSection (hf : f ∈ 𝒮 1)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    degreeOneSection 𝒮 hf hW = trivializingSection 𝒮 hf (1 : ℤ) hW :=
  Subtype.ext (funext fun x =>
    (degreeSection_apply 𝒮 1 ⟨f, hf⟩ _).trans (trivializingFun_one 𝒮 hW x).symm)

/-- **A degree-one element freely generates `𝒪(1)` on its own standard open.** On every open
contained in `D₊(f)`, multiplication by the restriction of `degreeSection 𝒮 1 f` is a bijection
from the sections of the structure sheaf onto the sections of `𝒪(1)`.

This is `bijective_trivializingHom` of Tag 01MS, transported along
`degreeOneSection_eq_trivializingSection`; what is new is that the generator is the canonical
section attached to `f`, rather than an anonymous trivializing fraction. -/
public theorem bijective_smul_degreeOneSection (hf : f ∈ 𝒮 1)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective (fun r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) =>
      r • degreeOneSection 𝒮 hf hW) :=
  degreeOneSection_eq_trivializingSection 𝒮 hf hW ▸
    bijective_trivializingHom 𝒮 hf (1 : ℤ) hW

/-- Every section of `𝒪(1)` over an open of `D₊(f)` is a unique multiple of the restriction of
`degreeSection 𝒮 1 f`. -/
public theorem existsUnique_smul_degreeOneSection (hf : f ∈ 𝒮 1)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (a : moduleSections 𝒮 (twistGrading (S := S) 𝒮 ((1 : ℤ) * ((1 : ℕ) : ℤ))) W) :
    ∃! r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W),
      r • degreeOneSection 𝒮 hf hW = a :=
  (bijective_smul_degreeOneSection 𝒮 hf hW).existsUnique a

/-- **When `S` is generated in degree one, the degree-one standard opens cover `Proj(S)`,
pointwise.** Every point lies in `D₊(g)` for some homogeneous `g` of degree one, on which
`bijective_smul_degreeOneSection` exhibits `degreeSection 𝒮 1 g` as a free generator of `𝒪(1)`.

The covering family itself is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.iSup_basicOpen_degreeOne_eq_top`. -/
@[ega "II 3.1.6" "special case"]
public theorem exists_mem_basicOpen_degreeOne
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) (x : ProjectiveSpectrum.top 𝒮) :
    ∃ g : 𝒮 1, x ∈ ProjectiveSpectrum.basicOpen 𝒮 (g : S) := by
  have hx : x ∈ (⨆ g : 𝒮 1, AlgebraicGeometry.Proj.basicOpen 𝒮 (g : S)) := by
    rw [Stacks.AlgebraicGeometry.ProjRepresentsF1.iSup_basicOpen_degreeOne_eq_top 𝒮 hgen]
    exact trivial
  obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hx
  exact ⟨g, hg⟩

end Stacks.AlgebraicGeometry.ProjDegreeOneTriv

end
