module

public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFormallySmoothComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermSequence
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of the naive cotangent complex of a formally smooth morphism

Let `g : P ⟶ Y` be a formally smooth morphism of schemes and `i : X ⟶ P` an arbitrary morphism.
The canonical chain map

`i^*NL_{P/Y} ⟶ i^*Ω_{P/Y}[0]`

onto the pullback of the sheaf of relative differentials, placed in degree `0`, is a
quasi-isomorphism.

This is the **pullback step** in the proof of [Stacks Project, Tag 0FV4].  That tag factors a
morphism `f : X ⟶ Y` as `f = g ∘ i` with `i` an immersion and `g` formally smooth, and compares
`NL_{X/Y}` with the two term complex `(𝒞_{X/P} ⟶ i^*Ω_{P/Y})`; the first thing its proof needs is
`NL_{P/Y} = Ω_{P/Y}` *after pullback along `i`*.  That does **not** follow from the same statement
before pullback — the `quasiIso_naiveCotangentToDifferentialsSingle` of
`Stacks.NaiveCotangentFormallySmoothComparison` — because the pullback of sheaves of modules is
only right exact: what is at stake is the
vanishing `H^{-1}(i^*NL_{P/Y}) = 0`, which the source obtains from local projectivity of
`Ω_{P/Y}` through [Stacks Project, Tag 0FUY] and calls a small detail omitted.  It is proved
here.

## Main definitions

* `Stacks.NaiveCotangentPullbackFormallySmooth.pullbackDifferentialsSingle`: the complex
  `i^*Ω_{P/Y}[0]`.
* `Stacks.NaiveCotangentPullbackFormallySmooth.pullbackNaiveCotangentToDifferentialsSingle`: the
  canonical chain map `i^*NL_{P/Y} ⟶ i^*Ω_{P/Y}[0]`, defined for every pair of morphisms of
  schemes; formal smoothness of `g` is needed only to make it a quasi-isomorphism.

## Main results

* `Stacks.NaiveCotangentPullbackFormallySmooth.isSplitMono_of_projective_cokernel`: the general
  criterion — a monomorphism with projective cokernel in an abelian category is a split
  monomorphism.
* `isSplitMono_modulesStalkFunctor_map_naiveCotangentComplex_d`: for `g` formally smooth the
  stalk at every point of the one nonzero differential of `NL_{P/Y}` is a *split* monomorphism of
  modules over the local ring.
* `isZero_homology_negOne_modulePullbackNaiveCotangentComplex`: the vanishing
  `H^{-1}(i^*NL_{P/Y}) = 0`.
* `quasiIso_pullbackNaiveCotangentToDifferentialsSingle` and
  `isIso_Q_map_pullbackNaiveCotangentToDifferentialsSingle`: the pullback step itself, as a
  quasi-isomorphism of complexes of sheaves of `𝒪_X`-modules and as an isomorphism in `D(𝒪_X)`.

## Route

Everything rests on the observation that a *split* monomorphism is carried to a split
monomorphism by **every** functor, so the failure of the pullback to be exact does not matter
once the differential of `NL_{P/Y}` is split at each stalk.

1. At a point `p` of `P` the stalk of `NL_{P/Y}^{-1} ⟶ NL_{P/Y}^0` is a monomorphism, by
   `Stacks.Smooth.injective_stalkFunctor_map_naiveCotangentComplex_d` — the stalkwise content of
   the vanishing clause of [Stacks Project, Tag 0D0L].
2. Its cokernel is the stalk of `H^0(NL_{P/Y}) = Ω_{P/Y}`: the complex has nothing in degree `1`,
   so `H^0` is the cokernel of its one differential
   (`Stacks.NaiveCotangentSixTermSequence.homologyZeroIsoCokernelOfIsZeroXOne`), the stalk functor
   is a left adjoint and hence commutes with that cokernel
   (`Stacks.NaiveCotangentSixTermSequence.mapHomologyZeroIso`), and `H^0(NL_{P/Y})` is `Ω_{P/Y}` by
   the degree-zero clause of [Stacks Project, Tag 0D0J].
3. That stalk is a projective module: it is `Ω[𝒪_{P,p}⁄𝒪_{Y,g p}]` by
   `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, the stalk map of
   `g` is formally smooth, and projectivity of the module of Kähler differentials is part of
   Mathlib's definition of a formally smooth algebra — which is exactly the content the locally
   projective clause of [Stacks Project, Tag 0D0L]
   (`Stacks.Smooth.isLocallyProjective_homology_zero_naiveCotangentComplex_of_formallySmooth`)
   records on affine charts, read here at a point instead.
4. So the stalk of the differential is a split monomorphism; applying the base change
   `ModuleCat.extendScalars` of the stalk map of `i` keeps it one, and the stalk formula for the
   pullback of sheaves of modules
   (`Stacks.ModuleSkyscraper.pullbackStalkIso`, [Stacks Project, Tag 0098]) identifies the result
   with the stalk of `i^*(NL_{P/Y}^{-1} ⟶ NL_{P/Y}^0)`.  Exactness being stalkwise
   ([Stacks Project, Tag 01AG]), `i^*NL_{P/Y}` is exact in degree `-1`.
5. The degree `0` cohomology sheaf of `i^*NL_{P/Y}` is `i^*Ω_{P/Y}` by
   `Stacks.NaiveCotangentSixTermSequence.modulePullbackNaiveCotangentComplexHomologyZeroIso`, a
   clause of [Stacks Project, Tag 0E44], and outside degrees `-1` and `0` the cohomology sheaves
   vanish by the other 0E44 clause available there.  The general criterion
   `Stacks.NaiveCotangentFormallySmoothComparison.quasiIso_homToSingleHomology` then turns those
   three facts into the quasi-isomorphism.

## Implementation notes

Two spellings of the category of sheaves of `𝒪_P`-modules occur, as in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermSequence`: the one
`AlgebraicGeometry.Scheme.naiveCotangentComplex` is stated at, and
`AlgebraicGeometry.Scheme.Modules`, which is what `AlgebraicGeometry.Scheme.Modules.pullback` and
`Stacks.ModuleSkyscraper.modulesStalkFunctor` are stated at.  They agree definitionally but not
syntactically.  Step 2 above is therefore assembled as a *single* composite of isomorphisms whose
only cross-spelling link is the one the six term sequence file already crosses; comparing the two
spellings inside `cokernel` instead exceeds the heartbeat ceiling.

Likewise the two stalk functors on sheaves of modules — over the `RingCat`-valued stalk of the
sheaf of rings (`AlgebraicGeometry.SheafOfModules.stalkFunctor`, which the stalkwise criterion for
exactness is stated at) and over the `CommRingCat`-valued stalk
(`Stacks.ModuleSkyscraper.modulesStalkFunctor`, which the stalk formula for the pullback is stated
at) — have the same underlying map on stalks of abelian groups, so injectivity is transported
between them through `ModuleCat.mono_iff_injective` rather than through a comparison of the two.

## Scope

This is one step of [Stacks Project, Tag 0FV4] and the tag is **not** proved here.  The
immersion `i` plays no part in it: the statements below hold for an arbitrary morphism
`i : X ⟶ P`, and no hypothesis standing in for a missing step is introduced.

The two steps that this section used to list as still missing are **no longer missing**, and the
vanishing proved here is what discharges the hypothesis of the first of them.  Both are in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConeMapInvertible`:

* invertibility in `D(𝒪_X)` of the canonical map `i^*NL_{P/Y} ⟶ C(NL_{X/Y} ⟶ NL_{X/P})[-1]` of
  [Stacks Project, Tag 0E1Z] is `Stacks.NaiveCotangentConeInvertible.quasiIso_coneMap` and
  `...isIso_Q_map_coneMap`, and `...cotangentTriangle_distinguished` is the distinguished
  triangle `i^*NL_{P/Y} ⟶ NL_{X/Y} ⟶ NL_{X/P} ⟶ i^*NL_{P/Y}[1]` that it produces from
  `Stacks.NaiveCotangentCompositionTriangle.triangle_distinguished` ([Stacks Project, Tag 0FV3]).
  The comparison of the two models of the pullback that this clause recorded as undeclared — the
  vanishing proved here is at the termwise-pullback model
  `Stacks.NaiveCotangentSixTermSequence.modulePullbackNaiveCotangentComplex`, the cone map's
  source is `Stacks.SheafOfModules.pulledNaiveCotangentComplex` — was in fact already declared,
  as `Stacks.NaiveCotangentSixTermSequence.pullbackComplexIso`;
* the rotation of that triangle exhibiting `NL_{X/Y}` as the cone of `NL_{X/P}[-1] ⟶ i^*NL_{P/Y}`,
  read through `NL_{X/P} ≅ 𝒞_{X/P}[1]` of [Stacks Project, Tag 0FV2]
  (`Stacks.Conormal.Sites.quasiIso_conormalShiftComparison`) and `i^*NL_{P/Y} ≅ i^*Ω_{P/Y}[0]`
  of the step proved here, is
  `Stacks.NaiveCotangentConeInvertible.conormalDifferentialsTriangle_distinguished`.

What remains between those and the tag is a comparison of two morphisms of sheaves
`𝒞_{X/P} ⟶ i^*Ω_{P/Y}`: the first morphism of that rotated triangle, which is the connecting
morphism of the six term sequence of [Stacks Project, Tag 0E44] read through the degree `-1`
identification of [Stacks Project, Tag 0FV2], against the first arrow of the conormal sequence
of [Stacks Project, Tag 01UZ], `Stacks.ConormalSequenceRight.conormalDifferential`, which is the
differential of the two term complex
`Stacks.ConormalSequenceRight.conormalDifferentialComplex` the tag names.  The tag follows once
the two are identified up to sign, and a distinguished triangle pins its first morphism only up
to automorphisms of that morphism's source and target, so the connecting morphism has to be
computed.  It has been: `Stacks.SheafOfModules.stalk_connecting_cotangent_mk` computes it at
every stalk and the answer is **minus** the conormal differential.  Two coordinate changes along
that route are still missing, the stalks of the comparison isomorphisms
`Stacks.Conormal.Sites.homologyNegOneIsoConormalSheaf` and
`Stacks.NaiveCotangentSixTermSequence.pullbackHomologyZeroIso`.  See the `Scope` section of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConeMapInvertible`.

The tag itself does **not** wait on them: it is proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentImmersionFormallySmooth`, by a route
that forms no triangle and uses no step of this file — the structural homomorphism
`i^{-1}𝒪_P ⟶ 𝒪_X` is a presentation of `𝒪_X` over `f^{-1}𝒪_Y` whose conormal sequence is the
tag's right-hand side, and comparing it with the canonical presentation through the polynomial
presentation on the sections of `i^{-1}𝒪_P` gives an honest chain map, with no connecting
morphism and no sign.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 0FUY](https://stacks.math.columbia.edu/tag/0FUY), the truncation of the
  derived pullback, which is the route the source takes through this step.
* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L), formal smoothness read on
  the naive cotangent complex.
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), the cohomology sheaves of
  the naive cotangent complex.
* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44), the six term exact
  sequence, whose degree `0` clauses identify `H^0(i^*NL_{P/Y})`.
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098), the stalk of a pullback of
  sheaves of modules.
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG), exactness is stalkwise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.ModuleSkyscraper (modulesStalkFunctor modulesStalkSkyAdjunction pullbackStalkIso)
open Stacks.NaiveCotangentSixTermSequence
open Stacks.NaiveCotangentFormallySmoothComparison

universe u

namespace Stacks.NaiveCotangentPullbackFormallySmooth

/-! ### Monomorphisms with projective cokernel -/

section Abstract

variable {C : Type*} [Category C] [Abelian C]

/-- A monomorphism whose cokernel is a projective object is a split monomorphism: a section of
the cokernel projection exists by projectivity, and the difference of the identity with the
resulting idempotent factors through the monomorphism, which is the kernel of its own cokernel. -/
theorem isSplitMono_of_projective_cokernel {A B : C} (d : A ⟶ B) [Mono d]
    [Projective (cokernel d)] : IsSplitMono d := by
  have he : (𝟙 B - cokernel.π d ≫ Projective.factorThru (𝟙 (cokernel d)) (cokernel.π d)) ≫
      cokernel.π d = 0 := by
    rw [Preadditive.sub_comp, id_comp, assoc, Projective.factorThru_comp, comp_id, sub_self]
  refine IsSplitMono.mk' ⟨Abelian.monoLift d _ he, ?_⟩
  rw [← cancel_mono d, assoc, Abelian.monoLift_comp, Preadditive.comp_sub, comp_id,
    ← assoc, cokernel.condition, zero_comp, sub_zero, id_comp]

end Abstract

/-! ### The differential of `NL_{P/Y}` is split at every stalk -/

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (g : P ⟶ Y)

/-- **The stalk of `Ω_{P/Y}` at a point of a formally smooth morphism is a projective module.**
The stalk is the module of Kähler differentials of the stalk map of `g`
(`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`), the stalk map of a
formally smooth morphism is a formally smooth ring map, and a formally smooth algebra has
projective Kähler differentials.

This is the locally projective clause of [Stacks Project, Tag 0D0L] read at a point rather than on
an affine chart; the chartwise form is
`Stacks.Smooth.isLocallyProjective_homology_zero_naiveCotangentComplex_of_formallySmooth`. -/
theorem projective_stalk_relativeDifferentials
    (hg : Stacks.Smooth.FormallySmoothScheme g) (p : P) :
    Projective ((modulesStalkFunctor P p).obj (Scheme.Hom.relativeDifferentials g)) := by
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds p)) := Classical.decEq _
  let := Stacks.RelativeDifferentialStalkMap.algebraStalkMap g p
  have : Algebra.FormallySmooth (ToType (Y.presheaf.stalk (g.base p)))
      (ToType (P.sheaf.presheaf.stalk p)) :=
    (Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth hg p).toAlgebra
  have : Module.Projective (ToType (P.sheaf.presheaf.stalk p))
      (KaehlerDifferential (ToType (Y.presheaf.stalk (g.base p)))
        (ToType (P.sheaf.presheaf.stalk p))) :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  have hO : Module.Projective (ToType (P.sheaf.presheaf.stalk p))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials g).val.presheaf p)) :=
    Module.Projective.of_equiv'
      (Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv g p).symm
  exact @ModuleCat.projective_of_categoryTheory_projective _ _
    ((modulesStalkFunctor P p).obj (Scheme.Hom.relativeDifferentials g)) hO

/-- **The stalk of the differential of `NL_{P/Y}` is a split monomorphism for `g` formally
smooth.** At every point `p` of `P` the stalk of the one nonzero differential
`NL_{P/Y}^{-1} ⟶ NL_{P/Y}^0` admits an `𝒪_{P,p}`-linear retraction.

It is a monomorphism by the stalkwise vanishing clause of [Stacks Project, Tag 0D0L],
`Stacks.Smooth.injective_stalkFunctor_map_naiveCotangentComplex_d`, and its cokernel is the stalk
of `H^0(NL_{P/Y}) = Ω_{P/Y}`, which is projective by
`Stacks.NaiveCotangentPullbackFormallySmooth.projective_stalk_relativeDifferentials`. -/
theorem isSplitMono_modulesStalkFunctor_map_naiveCotangentComplex_d
    (hg : Stacks.Smooth.FormallySmoothScheme g) (p : P) :
    IsSplitMono ((modulesStalkFunctor P p).map
      ((Scheme.naiveCotangentComplex g).d (-1) 0)) := by
  have : Mono ((modulesStalkFunctor P p).map ((Scheme.naiveCotangentComplex g).d (-1) 0)) :=
    (ModuleCat.mono_iff_injective _).mpr
      (Stacks.Smooth.injective_stalkFunctor_map_naiveCotangentComplex_d g hg p)
  have := (modulesStalkSkyAdjunction P p).leftAdjoint_preservesColimits
  have : (modulesStalkFunctor P p).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (modulesStalkFunctor P p)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have h1 := Scheme.naiveCotangentComplex_isZero_X g 1 (by decide) (by decide)
  have : Projective (cokernel ((modulesStalkFunctor P p).map
      ((Scheme.naiveCotangentComplex g).d (-1) 0))) :=
    Projective.of_iso
      ((modulesStalkFunctor P p).mapIso
            (Scheme.naiveCotangentComplexHomologyZeroIso g).symm ≪≫
          (mapHomologyZeroIso (modulesStalkFunctor P p)
            (Scheme.naiveCotangentComplex g) h1).symm ≪≫
          homologyZeroIsoCokernelOfIsZeroXOne
            (((modulesStalkFunctor P p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (Scheme.naiveCotangentComplex g))
            (Functor.map_isZero (modulesStalkFunctor P p) h1))
      (projective_stalk_relativeDifferentials g hg p)
  exact isSplitMono_of_projective_cokernel _

/-! ### The vanishing of `H^{-1}(i^*NL_{P/Y})` -/

/-- **The stalk of the differential of `i^*NL_{P/Y}` is a monomorphism.** The stalk at `x` of the
pullback along `i` of a sheaf of `𝒪_P`-modules is the base change along the stalk map of `i` of
its stalk at `i x` ([Stacks Project, Tag 0098],
`Stacks.ModuleSkyscraper.pullbackStalkIso`), naturally in the module.  The stalk of the
differential of `NL_{P/Y}` at `i x` is a split monomorphism, base change carries split
monomorphisms to split monomorphisms, and the naturality square transports the conclusion. -/
theorem mono_modulesStalkFunctor_map_pullback_naiveCotangentComplex_d
    (hg : Stacks.Smooth.FormallySmoothScheme g) (x : X) :
    Mono ((modulesStalkFunctor X x).map
      ((Scheme.Modules.pullback i).map ((Scheme.naiveCotangentComplex g).d (-1) 0))) := by
  have := isSplitMono_modulesStalkFunctor_map_naiveCotangentComplex_d g hg (i.base x)
  have : IsSplitMono ((ModuleCat.extendScalars (i.stalkMap x).hom).map
      ((modulesStalkFunctor P (i.base x)).map
        ((Scheme.naiveCotangentComplex g).d (-1) 0))) :=
    IsSplitMono.mk' ⟨(ModuleCat.extendScalars (i.stalkMap x).hom).map
        (retraction ((modulesStalkFunctor P (i.base x)).map
          ((Scheme.naiveCotangentComplex g).d (-1) 0))),
      by rw [← CategoryTheory.Functor.map_comp, IsSplitMono.id,
        CategoryTheory.Functor.map_id]⟩
  have hnat : ((ModuleCat.extendScalars (i.stalkMap x).hom).map
        ((modulesStalkFunctor P (i.base x)).map
          ((Scheme.naiveCotangentComplex g).d (-1) 0))) ≫
      ((pullbackStalkIso i x).app ((Scheme.naiveCotangentComplex g).X 0)).hom =
      ((pullbackStalkIso i x).app ((Scheme.naiveCotangentComplex g).X (-1))).hom ≫
      (modulesStalkFunctor X x).map
        ((Scheme.Modules.pullback i).map ((Scheme.naiveCotangentComplex g).d (-1) 0)) :=
    (pullbackStalkIso i x).hom.naturality _
  rw [← Iso.inv_hom_id_assoc ((pullbackStalkIso i x).app ((Scheme.naiveCotangentComplex g).X (-1)))
    ((modulesStalkFunctor X x).map _), ← hnat]
  infer_instance

/-- **`i^*NL_{P/Y}` is exact in degree `-1` for `g` formally smooth.** Exactness is stalkwise
([Stacks Project, Tag 01AG]); the complex has no term in degree `-2`, so exactness of a stalk
complex in degree `-1` is injectivity of its one nonzero differential. -/
theorem exactAt_negOne_modulePullbackNaiveCotangentComplex
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    (modulePullbackNaiveCotangentComplex i g).ExactAt (-1) := by
  refine (AlgebraicGeometry.SheafOfModules.exactAt_iff_forall_stalk_exactAt X.ringCatSheaf
    (modulePullbackNaiveCotangentComplex i g) (-1)).2 (fun x ↦ ?_)
  refine (HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp)).2 ?_
  refine (ShortComplex.exact_iff_mono _ ?_).2 ?_
  · exact ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map_isZero
      (isZero_modulePullbackNaiveCotangentComplex_X i g (-2)
        (by decide) (by decide))).eq_zero_of_src _
  · exact (ModuleCat.mono_iff_injective _).mpr
      ((ModuleCat.mono_iff_injective
        ((modulesStalkFunctor X x).map
          ((Scheme.Modules.pullback i).map
            ((Scheme.naiveCotangentComplex g).d (-1) 0)))).mp
        (mono_modulesStalkFunctor_map_pullback_naiveCotangentComplex_d i g hg x))

/-- **The pullback step of [Stacks Project, Tag 0FV4]: the vanishing `H^{-1}(i^*NL_{P/Y}) = 0`.**
For a formally smooth morphism of schemes `g : P ⟶ Y` and an arbitrary morphism `i : X ⟶ P` the
degree `-1` cohomology sheaf of the termwise pullback along `i` of `NL_{P/Y}` vanishes.

This is the step the source records as a small detail omitted, and obtains from local projectivity
of `Ω_{P/Y}` — the locally projective clause of [Stacks Project, Tag 0D0L] — through
[Stacks Project, Tag 0FUY].  The pullback of sheaves of modules is only right exact, so this does
not follow from the vanishing `H^{-1}(NL_{P/Y}) = 0` before pullback; what makes it true is that
local projectivity splits the one differential of `NL_{P/Y}` at every stalk, and a split
monomorphism stays one under any functor.  See the `Route` section of this file.

Only this step of 0FV4 is covered; see the `Scope` section of this file. -/
@[stacks 0FV4 "the pullback step: H^{-1}(i^*NL_{P/Y}) = 0, the detail the source omits"]
theorem isZero_homology_negOne_modulePullbackNaiveCotangentComplex
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    IsZero ((modulePullbackNaiveCotangentComplex i g).homology (-1)) :=
  (exactAt_negOne_modulePullbackNaiveCotangentComplex i g hg).isZero_homology

/-! ### The comparison `i^*NL_{P/Y} ⟶ i^*Ω_{P/Y}[0]` -/

/-- The complex `i^*Ω_{P/Y}[0]`: the pullback along `i` of the sheaf of relative differentials of
`g`, placed in degree `0`. -/
noncomputable abbrev pullbackDifferentialsSingle : CochainComplex X.Modules ℤ :=
  (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials g))

/-- The canonical chain map `i^*NL_{P/Y} ⟶ i^*Ω_{P/Y}[0]`.  In degree `0` it is the canonical
surjection of `(i^*NL_{P/Y})^0` onto `H^0(i^*NL_{P/Y})`, read in `i^*Ω_{P/Y}` through the clause
`Stacks.NaiveCotangentSixTermSequence.modulePullbackNaiveCotangentComplexHomologyZeroIso` of
[Stacks Project, Tag 0E44]; in every other degree the target is a zero object.

No hypothesis on `g` or `i` is used: the map exists for every pair of morphisms of schemes, and
formal smoothness enters only in
`quasiIso_pullbackNaiveCotangentToDifferentialsSingle` below. -/
noncomputable def pullbackNaiveCotangentToDifferentialsSingle :
    modulePullbackNaiveCotangentComplex i g ⟶ pullbackDifferentialsSingle i g :=
  homToSingleHomology (modulePullbackNaiveCotangentComplex i g) 0 1 (by simp)
    (isZero_modulePullbackNaiveCotangentComplex_X i g 1 (by decide) (by decide))
    (modulePullbackNaiveCotangentComplexHomologyZeroIso i g)

/-- **The pullback step of [Stacks Project, Tag 0FV4].** For a formally smooth morphism of schemes
`g : P ⟶ Y` and an arbitrary morphism `i : X ⟶ P` the canonical chain map
`i^*NL_{P/Y} ⟶ i^*Ω_{P/Y}[0]` is a quasi-isomorphism: the pullback along `i` of the naive cotangent
complex of `g` is identified with the pullback of its sheaf of relative differentials, placed in
degree `0`.

This is the form `NL_{P/Y} = Ω_{P/Y}` in which the proof of 0FV4 uses the tag *after* pulling back
along `i`, and it is the step that does not follow from
`Stacks.NaiveCotangentFormallySmoothComparison.quasiIso_naiveCotangentToDifferentialsSingle`, the
same statement before pullback, the pullback of sheaves of modules not being exact.  Its three
ingredients are the vanishing
`isZero_homology_negOne_modulePullbackNaiveCotangentComplex` proved above, and the two clauses
of [Stacks Project, Tag 0E44] available in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermSequence`: the identification
`H^0(i^*NL_{P/Y}) = i^*Ω_{P/Y}` and the vanishing of the cohomology sheaves outside degrees `-1`
and `0`.

Only this step of 0FV4 is covered; see the `Scope` section of this file. -/
@[stacks 0FV4 "the pullback step: i^*NL_{P/Y} -> i^*Omega_{P/Y}[0] is a quasi-isomorphism"]
theorem quasiIso_pullbackNaiveCotangentToDifferentialsSingle
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    QuasiIso (pullbackNaiveCotangentToDifferentialsSingle i g) :=
  quasiIso_homToSingleHomology (modulePullbackNaiveCotangentComplex i g) 0 1 (by simp)
    (isZero_modulePullbackNaiveCotangentComplex_X i g 1 (by decide) (by decide))
    (modulePullbackNaiveCotangentComplexHomologyZeroIso i g)
    (fun n hn ↦ by
      obtain rfl | hneg := eq_or_ne n (-1)
      · exact isZero_homology_negOne_modulePullbackNaiveCotangentComplex i g hg
      · exact isZero_homology_modulePullbackNaiveCotangentComplex i g n hneg hn)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The pullback step of [Stacks Project, Tag 0FV4], read in `D(𝒪_X)`.** For a formally smooth
morphism of schemes `g : P ⟶ Y` and an arbitrary morphism `i : X ⟶ P` the canonical chain map
`i^*NL_{P/Y} ⟶ i^*Ω_{P/Y}[0]` becomes an isomorphism in the derived category of sheaves of
`𝒪_X`-modules; that is, `i^*NL_{P/Y}` and `i^*Ω_{P/Y}[0]` are canonically isomorphic objects of
`D(𝒪_X)`.

This is the form in which the proof of 0FV4 uses the step: the first vertex of its distinguished
triangle is `i^*NL_{P/Y}`, and what the proof needs of it is that it is `i^*Ω_{P/Y}` in degree `0`.
Its content is that of
`quasiIso_pullbackNaiveCotangentToDifferentialsSingle`, the localisation functor to the derived
category inverting exactly the quasi-isomorphisms.  The
derived category is the one of `HasDerivedCategory.standard`, taken as a local instance.

Only this step of 0FV4 is covered; see the `Scope` section of this file. -/
@[stacks 0FV4 "the pullback step in D(O_X): i^*NL_{P/Y} = i^*Omega_{P/Y}[0]"]
theorem isIso_Q_map_pullbackNaiveCotangentToDifferentialsSingle
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    IsIso (DerivedCategory.Q.map (pullbackNaiveCotangentToDifferentialsSingle i g)) :=
  have : QuasiIso (pullbackNaiveCotangentToDifferentialsSingle i g) :=
    quasiIso_pullbackNaiveCotangentToDifferentialsSingle i g hg
  inferInstance

end Derived

end Stacks.NaiveCotangentPullbackFormallySmooth

end
