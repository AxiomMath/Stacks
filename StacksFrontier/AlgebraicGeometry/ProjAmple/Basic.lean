module

public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.NonvanishingEq
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtensionAffineCover.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝒪(1)` is an ample invertible sheaf on `Proj` of a ring generated in degree one

Ampleness of an invertible module asks that the scheme be quasi-compact and that every point lie
in an *affine* nonvanishing locus of a global section of some positive tensor power. On
`Proj 𝒮` with `𝒮` generated in degree one over `𝒮 0` that is immediate at exponent one: a
degree-one element `f` gives the global section `f / 1` of `𝒪(1)`, whose nonvanishing locus is the
standard open `D₊(f)`, and `D₊(f)` is affine.

The consequence over a polynomial ring is unconditional: **`𝒪(1)` is ample on `ℙⁿ_R` for every
commutative ring `R`**. This is the sentence the source's proof of the quotient-of-twists clause
of [Stacks, Tag 01YS] opens with — *"We will use that `𝒪(1)` is an ample invertible sheaf on
`ℙⁿ_R`. This follows directly from the definition since `ℙⁿ_R` is covered by the standard affine
opens `D₊(Tᵢ)`."*

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_affine_nonvanishingOpen`: the
  exponent-one criterion for ampleness — a quasi-compact scheme on which every point has an
  affine nonvanishing locus of a global section of `L` itself carries `L` as an ample sheaf.
* `Stacks.ProjAmple.isAmple_twistingModule_one`: **`𝒪(1)` is ample on `Proj 𝒮`** when `Proj 𝒮` is
  quasi-compact, `𝒪(1)` is invertible, and every point lies in the standard open of a degree-one
  element.
* `Stacks.ProjAmple.compactSpace_proj_polyGrading` and
  `Stacks.ProjAmple.exists_mem_basicOpen_degreeOne_polyGrading`: the two hypotheses discharged
  for a polynomial ring.
* `Stacks.ProjAmple.isAmple_twistingModule_one_polyGrading`: **`𝒪(1)` is ample on `ℙⁿ_R`**, with
  no hypothesis on `R` beyond commutativity, and
  `Stacks.ProjAmple.exists_isAmple_proj_polyGrading` in the existential form that the descent
  results consume.
* `Stacks.ProjAmple.exists_sections_mem_nonvanishingOpen_le_polyGrading`: the affine nonvanishing
  opens of the global sections of the positive tensor powers of `𝒪(1)` form a basis for the
  topology of `ℙⁿ_R`, and `Stacks.ProjAmple.quasiSeparatedSpace_proj_polyGrading`. These are two
  consumers of the inhabitant, included because a hypothesis class with no inhabitant makes every
  theorem over it vacuous and no axiom check sees that: before this file the only ample invertible
  sheaf in the development was the structure sheaf of an *affine* scheme, where the basis
  statement says nothing.

## Implementation notes

**No tag attribute is attached, and that is a judgement about which tag this is.** The definition
of ampleness is the attribute already carried by
`AlgebraicGeometry.Scheme.Modules.IsAmple`; the lemma stating that `𝒪(1)` is ample on `Proj`
in the source is about an arbitrary quasi-compact *open subscheme* of `Proj 𝒮` for an arbitrary
graded ring, and produces a uniform `d ≥ 1` making `𝒪(dn)` invertible with all multiplication
maps isomorphisms — a strictly heavier statement than anything here, of which only the final
basis clause is proved below, and only for a ring generated in degree one. The statements here are
the sentence inside the source's proof of the quotient-of-twists clause of [Stacks, Tag 01YS], to
which the source attaches no label. Putting a tag on them would put one tag on two unidentified
statements.

**What invertibility is assumed, and in which of the two classes.**
`AlgebraicGeometry.Scheme.Modules.IsAmple` takes `AlgebraicGeometry.SheafOfModules.IsInvertible`
as an instance argument while `Stacks.SheafOfModules.nonvanishingOpen` is defined for
`Stacks.SheafOfModules.IsInvertible`; the two are bridged by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, so `isAmple_twistingModule_one`
carries only the first and derives the second. In particular it needs no hypothesis that `𝒮` is
generated in degree one: that hypothesis is what
`AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf` wants in
order to produce the instance, and a caller who has the instance by another route does not owe it.
At a polynomial ring the instance is supplied by name rather than by synthesis:
`AlgebraicGeometry.ProjectiveSpectrum.Proj.projectiveSpace_isInvertible_twistingSheaf` is declared
`instance` but is stated at `(Proj 𝒮).sheaf.obj` and `(Proj 𝒮).ringCatSheaf.property`, and
`inferInstance` does **not** find it at the `(Proj 𝒮).toRingedSpace.presheaf` and
`(structureSheafRing (Proj 𝒮).toRingedSpace).property` spelling that ampleness is stated in,
while the same term is accepted at that spelling when
applied by name.

**The degree-one covering hypothesis is not removable**, and the counterexample is recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/ProjTwistSection/NonvanishingEq.lean`:
for `S = k[u, v]` with `deg u = 1` and `deg v = 2`, the section `u / 1` is nonvanishing at the
point `(u) ∉ D₊(u)`, so its nonvanishing locus is strictly larger than `D₊(u)` and the affineness
of that locus is not what `isAffineOpen_basicOpen_degreeOne` gives.

**Why the exponent-one criterion is a separate declaration.** Ampleness quantifies over sections
of `L^{⊗ n}` with `n ≥ 1` and never over sections of `L`, so a proof branch holding a section of
`L` itself has to transport it across
`Stacks.SheafOfModules.Invertible.tensorPowerOneIso`, and the exponent in the definition is spelled
`((1 : ℕ) : ℤ)` while that isomorphism is stated at `(1 : ℤ)`. The two are the same numeral after
evaluation, but `rw` cannot be used to move between the two sides of the transport equation across
the `X.Modules` seam — it fails with *"not type-correct under the `implicit` transparency
level"* — so the affineness component is closed in term mode, by
`Eq.mp (congrArg IsAffineOpen _)`. The same pattern is written out inline in
`AlgebraicGeometry.Scheme.Modules.isAmple_unit` and in
`Stacks.AmpleReducedDimensionOne.isAmple_of_isAffineOpen_nonvanishingOpen_of_forall_notMem`; this
is the form with no condition on which points the one section misses.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The exponent-one criterion for ampleness.** An invertible module `L` on a quasi-compact
scheme is ample as soon as every point lies in an affine nonvanishing locus of a global section of
`L` itself: the definition asks for a section of a positive tensor power, and the first power is
`L` by `Stacks.SheafOfModules.Invertible.tensorPowerOneIso`, which moves neither the nonvanishing
locus nor its affineness. -/
public theorem isAmple_of_forall_exists_affine_nonvanishingOpen (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hcpt : CompactSpace X)
    (h : ∀ x : X, ∃ s : L.sections,
        x ∈ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s ∧
          IsAffineOpen (Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s)) :
    IsAmple X L := by
  refine ⟨hcpt, fun x => ?_⟩
  obtain ⟨s, hxs, haff⟩ := h x
  have e := Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L
  have hnv : Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
        (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L ((1 : ℕ) : ℤ))
        (_root_.SheafOfModules.sectionsMap e.symm.hom s)
      = Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s :=
    Stacks.SheafOfModules.nonvanishingOpen_sectionsMap (X := X.toRingedSpace) e.symm s
  exact ⟨1, le_refl 1, _root_.SheafOfModules.sectionsMap e.symm.hom s, hnv.ge hxs,
    Eq.mp (congrArg (IsAffineOpen (X := X)) hnv).symm haff⟩

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.ProjAmple

section Graded

variable {S σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [AlgebraicGeometry.SheafOfModules.IsInvertible
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf
    (structureSheafRing (AlgebraicGeometry.Proj 𝒮).toRingedSpace).property
    (Stacks.ProjTwistSection.twistingModule 𝒮 1)]

/-- **`𝒪(1)` is an ample invertible sheaf on `Proj 𝒮`** as soon as `Proj 𝒮` is quasi-compact and
every point of it lies in the standard open of a degree-one element.

At a point `x` choose such an element `g`. Then `g / 1`
(`Stacks.ProjTwistSection.homogeneousSection`) is a global section of `𝒪(1)` whose nonvanishing
locus is exactly `D₊(g)`
(`Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen`, whose covering
hypothesis is the one assumed here), and `D₊(g)` is affine because `g` has degree one
(`Stacks.AlgebraicGeometry.ProjDegreeOne.isAffineOpen_basicOpen_degreeOne`). Ampleness is then
read at exponent one. -/
public theorem isAmple_twistingModule_one
    (hcpt : CompactSpace (AlgebraicGeometry.Proj 𝒮))
    (hcov : ∀ x : ProjectiveSpectrum.top 𝒮,
      ∃ g : S, g ∈ 𝒮 1 ∧ x ∈ ProjectiveSpectrum.basicOpen 𝒮 g) :
    AlgebraicGeometry.Scheme.Modules.IsAmple (AlgebraicGeometry.Proj 𝒮)
      (Stacks.ProjTwistSection.twistingModule 𝒮 1) := by
  have hSt : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj 𝒮).toRingedSpace).property
      (Stacks.ProjTwistSection.twistingModule 𝒮 1) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr inferInstance
  refine AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_affine_nonvanishingOpen
    _ _ hcpt fun x => ?_
  obtain ⟨g, hg, hxg⟩ := hcov x
  have key := Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen
    𝒮 g hg hcov
  exact ⟨Stacks.ProjTwistSection.homogeneousSection 𝒮 g hg, key.ge hxg,
    Eq.mp (congrArg (IsAffineOpen (X := AlgebraicGeometry.Proj 𝒮)) key).symm
      (Stacks.AlgebraicGeometry.ProjDegreeOne.isAffineOpen_basicOpen_degreeOne 𝒮 g hg)⟩

end Graded

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- `ℙⁿ_R` is quasi-compact: its structure morphism to `Spec` of the degree-zero part is
quasi-compact, because a polynomial ring in finitely many variables is of finite type over that
degree-zero part (`MvPolynomial.finiteType_of_homogeneousSubmodule_zero`), and the base is
quasi-compact. -/
public theorem compactSpace_proj_polyGrading :
    CompactSpace (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :=
  AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
    (AlgebraicGeometry.Proj.toSpecZero
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))

/-- Every point of `ℙⁿ_R` lies in the standard open of a degree-one element, namely of one of the
homogeneous coordinates: those standard opens already cover, by [Stacks, Tag 01NG]. -/
@[ega "II 3.1.6" "special case"]
public theorem exists_mem_basicOpen_degreeOne_polyGrading
    (x : ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    ∃ g, g ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 ∧
      x ∈ ProjectiveSpectrum.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) g := by
  have hx : x ∈ (⨆ i : Fin (n + 1),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i)) := by
    rw [Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R n]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨MvPolynomial.X i, Stacks.ProjectiveChart.X_mem_degree_one R i, hi⟩

/-- Invertibility of `𝒪(1)` on `ℙⁿ_R` at the spelling ampleness is stated in. The registered
instance `AlgebraicGeometry.ProjectiveSpectrum.Proj.projectiveSpace_isInvertible_twistingSheaf`
is at `(Proj 𝒮).sheaf.obj` and `(Proj 𝒮).ringCatSheaf.property`, which `inferInstance` does not
cross; applied by name it is accepted here, because at an argument position the elaborator checks
against the expected type. -/
public instance isInvertible_twistingModule_one_polyGrading :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace).property
      (Stacks.ProjTwistSection.twistingModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) 1) :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.projectiveSpace_isInvertible_twistingSheaf
    R (n + 1) 1

/-- **`𝒪(1)` is an ample invertible sheaf on `ℙⁿ_R`, for every commutative ring `R`.** This is
the sentence the source's proof of the quotient-of-twists clause of [Stacks, Tag 01YS] opens
with, and it holds for the reason the source gives: projective space is covered by the standard
affine opens `D₊(Tᵢ)`, which are the nonvanishing loci of the coordinates viewed as global
sections of `𝒪(1)`. -/
public theorem isAmple_twistingModule_one_polyGrading :
    AlgebraicGeometry.Scheme.Modules.IsAmple
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
      (Stacks.ProjTwistSection.twistingModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) 1) :=
  isAmple_twistingModule_one _ (compactSpace_proj_polyGrading R n)
    (exists_mem_basicOpen_degreeOne_polyGrading R n)

/-- **`ℙⁿ_R` carries an ample invertible sheaf**, in the existential form that the descent
results of this development consume. -/
public theorem exists_isAmple_proj_polyGrading :
    ∃ (L : (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
        (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace.presheaf
        (structureSheafRing (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace).property L),
      @AlgebraicGeometry.Scheme.Modules.IsAmple _ L hL :=
  ⟨Stacks.ProjTwistSection.twistingModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) 1, inferInstance,
    isAmple_twistingModule_one_polyGrading R n⟩

/-- **The affine nonvanishing opens of the global sections of the positive tensor powers of
`𝒪(1)` form a basis for the topology of `ℙⁿ_R`** — items (3) and (4) of [Stacks, Tag 01Q3] on
projective space. This is
`Stacks.SheafOfModules.Invertible.exists_sections_mem_nonvanishingOpen_le_of_isAmple` instantiated
at the ample sheaf above; it is recorded because that theorem's only previously available input
was the structure sheaf of an affine scheme, where the conclusion is immediate. -/
public theorem exists_sections_mem_nonvanishingOpen_le_polyGrading
    (W : (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Opens)
    (x : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (hx : x ∈ W) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (gg : (Stacks.SheafOfModules.Invertible.tensorPower
        (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace.presheaf
        (structureSheafRing (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace).property
        (Stacks.ProjTwistSection.twistingModule
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) 1) ((m : ℕ) : ℤ)).sections),
      x ∈ Stacks.SheafOfModules.nonvanishingOpen
          (X := (AlgebraicGeometry.Proj
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace) _ gg ∧
        Stacks.SheafOfModules.nonvanishingOpen
          (X := (AlgebraicGeometry.Proj
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace) _ gg ≤ W ∧
        IsAffineOpen (Stacks.SheafOfModules.nonvanishingOpen
          (X := (AlgebraicGeometry.Proj
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toRingedSpace) _ gg) :=
  Stacks.SheafOfModules.Invertible.exists_sections_mem_nonvanishingOpen_le_of_isAmple _
    (isAmple_twistingModule_one_polyGrading R n) W x hx

/-- `ℙⁿ_R` is a quasi-separated space, from the ample sheaf above through
`AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_isAmple`. A second consumer of the
inhabitant, on the `Proj` model, where the route through separatedness over the base is the only
other one available. -/
public theorem quasiSeparatedSpace_proj_polyGrading :
    QuasiSeparatedSpace (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :=
  AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_isAmple _ _
    (isAmple_twistingModule_one_polyGrading R n)

end ProjectiveSpace

end Stacks.ProjAmple

end
