module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksCore.Tactic.StacksAttribute

/-!
# The naive cotangent complex of a formally smooth morphism is its relative differentials

For a formally smooth morphism of schemes `g : P ⟶ Y` the canonical chain map

`NL_{P/Y} ⟶ Ω_{P/Y}[0]`

onto the sheaf of relative differentials placed in degree `0` is a quasi-isomorphism.

This is the input that the proof of [Stacks Project, Tag 0FV4] extracts from
[Stacks Project, Tag 0D0L] and uses in the form `NL_{P/Y} = Ω_{P/Y}`: an identification of
`NL_{P/Y}` with a complex concentrated in degree `0`, not merely a computation of its cohomology
sheaves.  The two clauses of 0D0L that are available — the vanishing `H⁻¹(NL_{P/Y}) = 0`
(`Stacks.Smooth.isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth`)
and the identification `H⁰(NL_{P/Y}) = Ω_{P/Y}` of [Stacks Project, Tag 0D0J] — are statements
about cohomology sheaves only; no morphism of complexes to `Ω_{P/Y}[0]` was constructed from
them.  That morphism is constructed here and proved to be a quasi-isomorphism.

## Main definitions

* `Stacks.NaiveCotangentFormallySmoothComparison.homToSingleHomology`: for a cochain complex `K`
  with nothing in the degree after `n`, the canonical chain map `K ⟶ H^n(K)[−n]` to its degree
  `n` cohomology object placed in degree `n`, read through a chosen identification of that
  cohomology object.
* `Stacks.NaiveCotangentFormallySmoothComparison.differentialsSingle`: the complex
  `Ω_{P/Y}[0]`, the sheaf of relative differentials of `g` placed in degree `0`.
* `Stacks.NaiveCotangentFormallySmoothComparison.naiveCotangentToDifferentialsSingle`:
  the canonical chain map `NL_{P/Y} ⟶ Ω_{P/Y}[0]`.  It is defined for every morphism of schemes;
  formal smoothness is needed only to make it a quasi-isomorphism.

## Main results

* `Stacks.NaiveCotangentFormallySmoothComparison.quasiIso_homToSingleHomology`: the general
  criterion — the canonical chain map to the degree `n` cohomology object placed in degree `n` is
  a quasi-isomorphism as soon as the cohomology objects of `K` vanish outside degree `n`.
* `Stacks.NaiveCotangentFormallySmoothComparison.quasiIso_naiveCotangentToDifferentialsSingle`:
  **the 0D0L input of [Stacks Project, Tag 0FV4]** — for `g` formally smooth the canonical chain
  map `NL_{P/Y} ⟶ Ω_{P/Y}[0]` is a quasi-isomorphism.
* `Stacks.NaiveCotangentFormallySmoothComparison.isIso_Q_map_naiveCotangentToDifferentialsSingle`:
  the same statement read in the derived category — that chain map is invertible in `D(𝒪_P)`, so
  `NL_{P/Y} ≅ Ω_{P/Y}[0]` there, which is the form 0FV4 states.

## Route

A cochain complex `K` with `K^{n+1} = 0` has `H^n(K)` equal to its degree `n` opcycles, so there
is a canonical map `K^n ⟶ H^n(K)` killing the differential into degree `n`, hence a canonical
chain map `K ⟶ H^n(K)[−n]` by `HomologicalComplex.mkHomToSingle`.  Its degree `n` cohomology map
is the chosen identification followed by `HomologicalComplex.singleObjHomologySelfIso`, which is
computed by comparing both sides against `HomologicalComplex.homologyι`; in every other degree
both cohomology objects are zero.

For `K = NL_{P/Y}` and `n = 0` the hypotheses are: `NL_{P/Y}` has no term in degree `1`
(`AlgebraicGeometry.Scheme.naiveCotangentComplex_isZero_X`), its cohomology sheaves vanish
outside degree `0` for `g` formally smooth
(`Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallySmooth`), and the degree `0`
cohomology sheaf is `Ω_{P/Y}` (`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`,
the degree-zero clause of [Stacks Project, Tag 0D0J]).

## Scope

This is one clause of [Stacks Project, Tag 0FV4] and the tag is **not** proved here.  The tag
asserts, for a morphism factoring as `f = g ∘ i` with `i` an immersion and `g` formally smooth, a
canonical isomorphism `NL_{X/Y} ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})` in `D(𝒪_X)`.  Beyond the clause proved
here its proof needs two further steps.

The step that this section used to list first — that `i^*NL_{P/Y} ⟶ i^*Ω_{P/Y}[0]` is again a
quasi-isomorphism, of which the degree `-1` half, the vanishing `H^{-1}(i^*NL_{P/Y}) = 0`, was
recorded here as missing — is **no longer missing**.  Both halves are proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentPullbackFormallySmooth`: the
vanishing is `isZero_homology_negOne_modulePullbackNaiveCotangentComplex` and the
quasi-isomorphism is `quasiIso_pullbackNaiveCotangentToDifferentialsSingle`, both in the namespace
`Stacks.NaiveCotangentPullbackFormallySmooth` and carrying `@[stacks 0FV4]`.  That file reaches
the vanishing by splitting the one differential of `NL_{P/Y}` at every stalk, using local
projectivity of `Ω_{P/Y}` — the other clause of 0D0L,
`Stacks.Smooth.isLocallyProjective_homology_zero_naiveCotangentComplex_of_formallySmooth` —
rather than through [Stacks Project, Tag 0FUY] as the source does.  The degree `0` half had
already been available as
`Stacks.NaiveCotangentSixTermSequence.modulePullbackNaiveCotangentComplexHomologyZeroIso`.

The two steps that this section used to list as remaining — invertibility in `D(𝒪_X)` of the
canonical map `i^*NL_{P/Y} ⟶ C(NL_{X/Y} ⟶ NL_{X/P})[-1]` of [Stacks Project, Tag 0E1Z], and the
rotation of the resulting triangle read through `NL_{X/P} ≅ 𝒞_{X/P}[1]` of
[Stacks Project, Tag 0FV2] — are **no longer missing**.  Both are proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConeMapInvertible`:
`Stacks.NaiveCotangentConeInvertible.quasiIso_coneMap` and `...isIso_Q_map_coneMap` are the
invertibility, `...cotangentTriangle_distinguished` the distinguished triangle
`i^*NL_{P/Y} ⟶ NL_{X/Y} ⟶ NL_{X/P} ⟶ i^*NL_{P/Y}[1]` it produces, and
`...conormalDifferentialsTriangle_distinguished` the rotation with all three vertices rewritten,
which exhibits `NL_{X/Y}` as the cone of a map `𝒞_{X/P} ⟶ i^*Ω_{P/Y}` in `D(𝒪_X)`.  The
comparison of the two models of the pullback, which this section recorded as undeclared, is
`Stacks.NaiveCotangentSixTermSequence.pullbackComplexIso` and was already available.

One step remains, and it is not one of the two above.  The two-term complex of the tag,
`Stacks.ConormalSequenceRight.conormalDifferentialComplex`, has for its differential the first
arrow of the conormal sequence of [Stacks Project, Tag 01UZ],
`Stacks.ConormalSequenceRight.conormalDifferential`, while the first morphism of the triangle
just described is the connecting morphism of the six-term sequence of
[Stacks Project, Tag 0E44] read through the degree `-1` identification of
[Stacks Project, Tag 0FV2].  The tag's conclusion follows once those two morphisms of sheaves
are identified up to sign, and it does not follow from further manipulation of triangles: a
distinguished triangle pins its first morphism only up to automorphisms of that morphism's
source and target, so the connecting morphism has to be computed.  It is what the source leaves
implicit in the last line of its proof.

The connecting morphism **has** been computed, and it is **minus** the conormal differential:
`Stacks.SheafOfModules.stalk_connecting_cotangent_mk` carries a conormal germ `[f]` to the class
of `-(1 ⊗ d f)` at every point.  Two coordinate changes along that route are still missing — the
stalks of the two comparison isomorphisms
`Stacks.Conormal.Sites.homologyNegOneIsoConormalSheaf` and
`Stacks.NaiveCotangentSixTermSequence.pullbackHomologyZeroIso` — and are listed in the `Scope`
section of `StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConeMapInvertible`.

**[Stacks Project, Tag 0FV4] is proved, by a route that does not pass through the triangle at
all**:
`Stacks.NaiveCotangentImmersionFormallySmooth.naiveCotangentIsoConormalDifferentialComplex`.
There the comparison is an honest chain map, so no connecting morphism and no sign occur: the
structural homomorphism `i^{-1}𝒪_P ⟶ 𝒪_X` is itself a presentation of `𝒪_X` over `f^{-1}𝒪_Y`
whose conormal sequence is the tag's right-hand side, and it is compared with the canonical
presentation through the polynomial presentation on the sections of `i^{-1}𝒪_P`.

The clause proved here is therefore stated for `g` alone: the immersion `i` plays no part in it,
and no hypothesis standing in for any of the missing steps is introduced.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L), formal smoothness read
  on the naive cotangent complex.
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), the cohomology sheaves
  of the naive cotangent complex of a morphism of schemes.
* [Stacks Project, Tag 0FUY](https://stacks.math.columbia.edu/tag/0FUY), the truncation of the
  derived pullback, which is what the pullback step of 0FV4 rests on.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe v u

namespace Stacks.NaiveCotangentFormallySmoothComparison

/-! ### The canonical map to a cohomology object placed in its own degree -/

section General

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [CategoryWithHomology C] {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}

/-- For a cochain complex `K` with nothing in the degree `m` following `n`, the canonical map
`K^n ⟶ H^n(K)`: the differential out of degree `n` is zero, so `H^n(K)` is the degree `n`
opcycles object. -/
noncomputable def toHomologyOfIsZeroNext (K : HomologicalComplex C c) (n m : ι)
    (hnm : c.next n = m) (h : IsZero (K.X m)) : K.X n ⟶ K.homology n :=
  K.pOpcycles n ≫ (K.isoHomologyι n m hnm (h.eq_of_tgt _ _)).inv

/-- For a cochain complex `K` with nothing in the degree following `n`, the canonical chain map
from `K` to its degree `n` cohomology object placed in degree `n`, read through a chosen
identification `e` of that cohomology object. -/
noncomputable def homToSingleHomology (K : HomologicalComplex C c) (n m : ι)
    (hnm : c.next n = m) (h : IsZero (K.X m)) {M : C} (e : K.homology n ≅ M) :
    K ⟶ (HomologicalComplex.single C c n).obj M :=
  HomologicalComplex.mkHomToSingle (toHomologyOfIsZeroNext K n m hnm h ≫ e.hom)
    (fun i _ ↦ by simp [toHomologyOfIsZeroNext])

/-- In degree `n` the canonical chain map induces, up to the canonical identification of the
degree `n` cohomology object of a complex concentrated in degree `n`, exactly the chosen
identification `e`. -/
theorem homologyMap_homToSingleHomology (K : HomologicalComplex C c) (n m : ι)
    (hnm : c.next n = m) (h : IsZero (K.X m)) {M : C} (e : K.homology n ≅ M) :
    HomologicalComplex.homologyMap (homToSingleHomology K n m hnm h e) n =
      e.hom ≫ (HomologicalComplex.singleObjHomologySelfIso c n M).inv := by
  have key : HomologicalComplex.opcyclesMap (homToSingleHomology K n m hnm h e) n ≫
      (HomologicalComplex.singleObjOpcyclesSelfIso c n M).inv =
      (K.isoHomologyι n m hnm (h.eq_of_tgt _ _)).inv ≫ e.hom := by
    rw [← cancel_epi (K.pOpcycles n), HomologicalComplex.p_opcyclesMap_assoc,
      homToSingleHomology, HomologicalComplex.mkHomToSingle_f]
    simp [toHomologyOfIsZeroNext]
  rw [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso c n M).hom, assoc,
    Iso.inv_hom_id, comp_id,
    ← HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv, ← assoc,
    HomologicalComplex.homologyι_naturality, assoc, key, ← assoc,
    HomologicalComplex.isoHomologyι_hom_inv_id, id_comp]

/-- A cochain complex with nothing in the degree following `n` and no cohomology outside degree
`n` is quasi-isomorphic to its degree `n` cohomology object placed in degree `n`, by the
canonical chain map. -/
theorem quasiIso_homToSingleHomology (K : HomologicalComplex C c) (n m : ι)
    (hnm : c.next n = m) (h : IsZero (K.X m)) {M : C} (e : K.homology n ≅ M)
    (hK : ∀ i, i ≠ n → IsZero (K.homology i)) :
    QuasiIso (homToSingleHomology K n m hnm h e) where
  quasiIsoAt i := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hi : i = n
    · subst hi
      rw [homologyMap_homToSingleHomology]
      infer_instance
    · exact ⟨0, (hK i hi).eq_of_src _ _,
        (HomologicalComplex.isZero_single_obj_homology c n M i hi).eq_of_src _ _⟩

end General

/-! ### The comparison for a morphism of schemes -/

variable {P Y : Scheme.{u}} (g : P ⟶ Y)

/-- The complex `Ω_{P/Y}[0]`: the sheaf of relative differentials of `g`, placed in degree `0`.
Its type is spelled at the category of sheaves of `𝒪_P`-modules that `NL_{P/Y}` lives in. -/
noncomputable abbrev differentialsSingle :
    CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology P.toRingedSpace.carrier) P.toRingedSpace.sheaf)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)

/-- The canonical chain map `NL_{P/Y} ⟶ Ω_{P/Y}[0]`.  In degree `0` it is the canonical
surjection of `NL_{P/Y}^0` onto `H⁰(NL_{P/Y})`, read in `Ω_{P/Y}` through the degree-zero clause
of [Stacks Project, Tag 0D0J]; in every other degree the target is a zero object.

No hypothesis on `g` is used: the map exists for every morphism of schemes, and formal
smoothness enters only in `quasiIso_naiveCotangentToDifferentialsSingle`. -/
noncomputable def naiveCotangentToDifferentialsSingle :
    Scheme.naiveCotangentComplex g ⟶ differentialsSingle g :=
  homToSingleHomology (Scheme.naiveCotangentComplex g) 0 1 (by simp)
    (Scheme.naiveCotangentComplex_isZero_X g 1 (by decide) (by decide))
    (Scheme.naiveCotangentComplexHomologyZeroIso g)

/-- **The 0D0L input of [Stacks Project, Tag 0FV4].**  For a formally smooth morphism of schemes
`g : P ⟶ Y` the canonical chain map `NL_{P/Y} ⟶ Ω_{P/Y}[0]` is a quasi-isomorphism: the naive
cotangent complex of `g` is identified with its sheaf of relative differentials placed in degree
`0`.

This is the step the proof of 0FV4 records as `NL_{P/Y} = Ω_{P/Y}`.  Its two ingredients are the
clauses of [Stacks Project, Tag 0D0L] proved for a formally smooth morphism, namely the vanishing
of the cohomology sheaves outside degree `0`
(`Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallySmooth`, which rests on
`Stacks.Smooth.isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth`), together with
the degree-zero identification `H⁰(NL_{P/Y}) = Ω_{P/Y}` of [Stacks Project, Tag 0D0J].  Those are
statements about cohomology sheaves; what is added here is the chain map itself, which is what
0FV4 uses.

As in `Stacks.Conormal.Sites.quasiIso_conormalShiftComparison` — the corresponding step of 0FV4
coming from [Stacks Project, Tag 0FV2] — the conclusion is given as a quasi-isomorphism of
complexes of sheaves of `𝒪_P`-modules, which is the chain-level content of the source's
identification in `D(𝒪_P)`: a map of honest complexes that the localisation functor to the
derived category inverts.

The other three steps of 0FV4's proof are not covered; see the `Scope` section of this file. -/
@[stacks 0FV4 "the 0D0L input NL_{P/Y} = Omega_{P/Y} as a quasi-isomorphism of complexes"]
theorem quasiIso_naiveCotangentToDifferentialsSingle
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    QuasiIso (naiveCotangentToDifferentialsSingle g) :=
  quasiIso_homToSingleHomology _ 0 1 _ _ _
    (Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallySmooth g hg)

/-! ### The identification in the derived category -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The 0D0L input of [Stacks Project, Tag 0FV4], read in `D(𝒪_P)`.**  For a formally smooth
morphism of schemes `g : P ⟶ Y` the canonical chain map `NL_{P/Y} ⟶ Ω_{P/Y}[0]` becomes an
isomorphism in the derived category of sheaves of `𝒪_P`-modules; that is, `NL_{P/Y}` and
`Ω_{P/Y}[0]` are canonically isomorphic objects of `D(𝒪_P)`.

This is the form `NL_{P/Y} = Ω_{P/Y}` in which the proof of 0FV4 uses the step.  Its content is
that of `quasiIso_naiveCotangentToDifferentialsSingle`, the localisation functor to the derived
category inverting exactly the quasi-isomorphisms; what is added is that the two complexes are
compared as objects of `D(𝒪_P)` rather than by their cohomology sheaves.  The derived category is
the one of `HasDerivedCategory.standard`, taken as a local instance.

Only this one step of 0FV4 is covered; see the `Scope` section of this file. -/
@[stacks 0FV4 "the 0D0L input: NL_{P/Y} -> Omega_{P/Y}[0] is invertible in D(O_P)"]
theorem isIso_Q_map_naiveCotangentToDifferentialsSingle
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    IsIso (DerivedCategory.Q.map (naiveCotangentToDifferentialsSingle g)) :=
  have : QuasiIso (naiveCotangentToDifferentialsSingle g) :=
    quasiIso_naiveCotangentToDifferentialsSingle g hg
  inferInstance

end Derived

end Stacks.NaiveCotangentFormallySmoothComparison

end
