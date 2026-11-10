module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.Sites.Coherent.RegularSheaves
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ProperFinitePresentationRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardPhRefinement
public import StacksFrontier.CategoryTheory.Sites.Descent.SheafForTransArrows
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf criterion for the h topology

Stacks 0EU5 characterizes the sheaves on the big h site over a scheme `S` by two conditions on
a presheaf `𝓕`:

1. `𝓕` satisfies the sheaf condition for Zariski coverings, and
2. for every morphism `f : V ⟶ U` which is proper, surjective and of finite presentation,
   `𝓕(U)` maps bijectively onto the equalizer of the two maps `𝓕(V) ⟶ 𝓕(V ×_U V)`,

and it adds that, in the presence of (1), condition (2) is equivalent to its restriction (2′)
to those `f : V ⟶ U` whose target `U` is affine.

This file states the three conditions and proves all three assertions of the lemma: both
directions of the characterization, and the equivalence of (2) with (2′) under (1).

## Main definitions

* `AlgebraicGeometry.BigHOver.IsZariskiSheaf`: condition (1).
* `AlgebraicGeometry.BigHOver.IsProperFinitePresentationSheaf`: condition (2), in the form of
  the sheaf condition for the one-element family `{f}`.
* `AlgebraicGeometry.BigHOver.IsAffineProperFinitePresentationSheaf`: condition (2′).
* `AlgebraicGeometry.BigHOver.openCoverFamily`: the covering family of the site attached to an
  open covering of the underlying scheme of one of its objects.

## Main results

* `AlgebraicGeometry.isSheafFor_singleton_iff_bijective_mapToEqualizer`: for a morphism `f`
  completed to a cartesian square `W = V ×_U V`, the sheaf condition for the one-element family
  `{f}` is *equivalent* to the bijectivity of the canonical map from `𝓕(U)` to the equalizer of
  `𝓕(V) ⟶ 𝓕(W)`.  This identifies the formulation of condition (2) used here with the
  equalizer statement of the source.
* `AlgebraicGeometry.BigHOver.sieve₀_mem_topology_of_isHCovering`: a family of morphisms of the
  site whose underlying family of morphisms of schemes is an h covering generates a covering
  sieve of the h topology.  This is the transport the necessity direction rests on.
* `AlgebraicGeometry.BigHOver.isSheaf_iff_isZariskiSheaf_and_isProperFinitePresentationSheaf`:
  the characterization — a presheaf of sets on the big h category over `S` is a sheaf if and
  only if it satisfies conditions (1) and (2).
* `AlgebraicGeometry.BigHOver.isProperFinitePresentationSheaf_iff_affine`: the final assertion
  — given condition (1), condition (2) is equivalent to condition (2′).
* `AlgebraicGeometry.BigHOver.openCoverFamily_mem_zariskiPrecoverage` and
  `AlgebraicGeometry.BigHOver.mem_zariskiPrecoverage_pullback₂`: the family attached to an open
  covering is a Zariski covering family of the site, and a Zariski covering family of the site
  stays one after base change.  These two are the Zariski bookkeeping every argument that glues
  over an open covering of the base needs, so they are stated for use outside this file rather
  than only internally to the proof below.

The two directions of the characterization and the two directions of the final assertion are
also available separately:
`AlgebraicGeometry.BigHOver.isZariskiSheaf_of_isSheaf`,
`AlgebraicGeometry.BigHOver.isProperFinitePresentationSheaf_of_isSheaf`,
`AlgebraicGeometry.BigHOver.isSheaf_of_isZariskiSheaf_of_isProperFinitePresentationSheaf`,
`AlgebraicGeometry.BigHOver.IsProperFinitePresentationSheaf.affine` and
`AlgebraicGeometry.BigHOver.isProperFinitePresentationSheaf_of_affine`.  Condition (2) for a
sheaf is also recorded in the source's equalizer form as
`AlgebraicGeometry.BigHOver.bijective_mapToEqualizer_of_isSheaf`.

## Scope

All of Stacks 0EU5 is proved.  The attribute is placed with a scoped clause on each covering
declaration, naming the part it establishes: `"only if, condition (1)"`,
`"only if, condition (2)"`, `"only if, condition (2) in equalizer form"`,
`"if, (1) and (2) imply the sheaf condition"`, `"sheaf characterization"`,
`"(2) implies (2′)"`, `"(1) and (2′) imply (2)"` and
`"given (1), (2) is equivalent to (2′)"`.

As everywhere in this development, the statements are universally quantified over an arbitrary
big h site: the library contains no construction of a term of `AlgebraicGeometry.BigHSite`, so
the set-theoretic existence of a big h site (Stacks 0ETZ, 000X) is not discharged here.

## Implementation notes

This is the h analogue of Stacks 0DBQ for the ph topology, proved in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSheafCriterion`, and it follows the same
plan; the finite presentation hypothesis is carried along throughout, and the refinement step
is different, as explained below.  The pure category theory of that file is reused: the
localized coverage criterion `AlgebraicGeometry.over_le_of_coverage`.

The *necessity* of (1) and (2) rests on a single transport: a family of morphisms of the big h
category over `S` whose underlying family of morphisms of schemes is an h covering generates a
covering sieve of the site, so a sheaf satisfies the sheaf condition for it.  This is proved by
moving the family to the size-bounded category of schemes underlying the site, replacing it by
a combinatorially equivalent *chosen* family via the site's representability axiom — the family
at hand need not be one of the chosen ones — and observing that combinatorially equivalent
families have the same presieve.  The localization of the site's topology at `S` is then
unwound with `CategoryTheory.GrothendieckTopology.mem_over_iff`.  Condition (1) follows because
a Zariski covering is a ph covering by Stacks 0DBH and open immersions are locally of finite
presentation; condition (2) follows because a proper surjective morphism of finite presentation
is an h covering all by itself, by Stacks 0ETW.

For a singleton family the sheaf condition says that a section of `𝓕` over `V` whose two
pullbacks to any common refinement agree extends uniquely to `U`; a cartesian square
`W = V ×_U V` turns that into the equalizer condition, because any two morphisms into `V`
which agree after composing with `f` factor through `W`.  This is what identifies the
formulation of condition (2) used here with the source's.

The *affine reduction* — (1) and (2′) imply (2) — covers the target of a proper surjective
morphism of finite presentation by the affine opens of its underlying scheme, which is a
Zariski covering family of the site; the base change of the morphism over each of them has
affine target, so (2′) applies there, and
`CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_of_pullback` assembles the local
sheaf conditions.  Base change of properness, surjectivity and finite presentation inside the
site goes through the pullback comparison isomorphism, the inclusion of the site into schemes
preserving fibre products.

The *sufficiency* of (1) and (2) is reduced, by the localized coverage criterion and the fact
that the sheaf condition for a sieve may be checked on the pullbacks along morphisms with
affine source, to the sheaf condition for an h covering family of an *affine* object of the
site.  There the ph argument has to be replaced: the big affine h site's families are the
standard h coverings of Stacks 0EUY, which are only *refined* by a standard ph covering and
therefore carry no presentation as the opens of a single proper morphism.  Instead Stacks 0ETU
is used directly — it refines every h covering of an affine scheme by the finite family of
affine opens of a single proper surjective morphism of finite presentation `p : Y ⟶ T`.  A
family of that shape is a Zariski covering family of `Y` composed with `p`, and for such a
family the sheaf condition follows from (1) and (2) by binding the sieve generated by `{p}`
with the pullbacks of the Zariski sieve.  The sheaf condition then passes from the refining
family to the original one by the refinement criterion of Stacks 0G1L, whose injectivity
hypothesis is supplied by the separatedness of the base change of the refining family — and
that base change is a family of the very same shape, because the base change of a Zariski
covering family is one and the base change of `p` is again proper, surjective and of finite
presentation.

The transport of the sheaf condition to an h covering family is stated here in public form for
the first time; its proof repeats the one given for the private `bigH_isSheafFor_of_hCover` of
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpDescent`, which is not visible
outside that module.

## References

* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
* [Stacks Project, Tag 0ETU](https://stacks.math.columbia.edu/tag/0ETU)
* [Stacks Project, Tag 0ETW](https://stacks.math.columbia.edu/tag/0ETW)
* [Stacks Project, Tag 0DBH](https://stacks.math.columbia.edu/tag/0DBH)
* [Stacks Project, Tag 0DBQ](https://stacks.math.columbia.edu/tag/0DBQ)
* [Stacks Project, Tag 0G1L](https://stacks.math.columbia.edu/tag/0G1L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

/-- For a morphism `f : V ⟶ U` completed to a cartesian square by `p₁, p₂ : W ⟶ V`, so that
`W = V ×_U V`, the sheaf condition for the one-element family `{f}` is equivalent to the
bijectivity of the canonical map from the sections over `U` to the equalizer of the two maps
from the sections over `V` to the sections over `W`.

Two morphisms into `V` which agree after composition with `f` factor through the cartesian
square, so the compatibility condition of the one-element family reduces to the equality of
the two restrictions along the square. -/
public theorem isSheafFor_singleton_iff_bijective_mapToEqualizer
    {C : Type w} [Category.{v} C] {F : Cᵒᵖ ⥤ Type u} {V U W : C} (f : V ⟶ U)
    (p₁ p₂ : W ⟶ V) (hW : IsPullback p₁ p₂ f f) :
    Presieve.IsSheafFor F (Presieve.singleton f) ↔
      Function.Bijective (regularTopology.mapToEqualizer F f p₁ p₂ hW.w) := by
  have hcompat : ∀ x : F.obj (op V),
      (∀ {Z : C} (q₁ q₂ : Z ⟶ V), q₁ ≫ f = q₂ ≫ f →
          F.map q₁.op x = F.map q₂.op x) ↔ F.map p₁.op x = F.map p₂.op x := by
    intro x
    refine ⟨fun H ↦ H p₁ p₂ hW.w, fun H Z q₁ q₂ h ↦ ?_⟩
    obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Z ⟶ W, l ≫ p₁ = q₁ ∧ l ≫ p₂ = q₂ :=
      ⟨hW.lift q₁ q₂ h, hW.lift_fst q₁ q₂ h, hW.lift_snd q₁ q₂ h⟩
    rw [← hl₁, ← hl₂]
    simp only [op_comp, Functor.map_comp_apply, H]
  rw [Presieve.isSheafFor_singleton, Function.bijective_iff_existsUnique]
  constructor
  · intro hF
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, huniq⟩ := hF x ((hcompat x).2 (by simpa using hx))
    refine ⟨y, ?_, ?_⟩
    · ext
      simpa [regularTopology.mapToEqualizer] using hy
    · intro z hz
      exact huniq z (by simpa [regularTopology.mapToEqualizer] using Subtype.ext_iff.1 hz)
  · intro hF x hx
    obtain ⟨y, hy, huniq⟩ := hF ⟨x, by simpa using (hcompat x).1 hx⟩
    refine ⟨y, ?_, ?_⟩
    · simpa [regularTopology.mapToEqualizer] using Subtype.ext_iff.1 hy
    · intro z hz
      refine huniq z ?_
      ext
      simpa [regularTopology.mapToEqualizer] using hz

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- **Condition (1) of Stacks 0EU5.** A presheaf on the big h category over `S` satisfies the
sheaf condition for Zariski coverings: for every family of morphisms of the site whose
underlying family of morphisms of schemes is a Zariski covering, every compatible family of
sections has a unique amalgamation. -/
public def IsZariskiSheaf : Prop :=
  ∀ (X : BigHOver B S hS) (E : PreZeroHypercover.{u + 1} X),
    (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X) →
      Presieve.IsSheafFor F E.presieve₀

/-- **Condition (2) of Stacks 0EU5.** A presheaf on the big h category over `S` satisfies the
sheaf condition for the one-element family `{f}` attached to every morphism `f` of the site
whose underlying morphism of schemes is proper, surjective and of finite presentation.

By `AlgebraicGeometry.isSheafFor_singleton_iff_bijective_mapToEqualizer` this is exactly the
source's requirement that the sections over the target map bijectively onto the equalizer of
the two maps from the sections over the source to the sections over `V ×_U V`. -/
public def IsProperFinitePresentationSheaf : Prop :=
  ∀ (X Y : BigHOver B S hS) (f : Y ⟶ X),
    IsProper ((BigHOver.toScheme B S hS).map f) →
    Surjective ((BigHOver.toScheme B S hS).map f) →
    FinitePresentation ((BigHOver.toScheme B S hS).map f) →
    Presieve.IsSheafFor F (Presieve.singleton f)

/-- **Condition (2′) of Stacks 0EU5.** Condition (2) restricted to morphisms whose target has
affine underlying scheme. -/
public def IsAffineProperFinitePresentationSheaf : Prop :=
  ∀ (X Y : BigHOver B S hS) (f : Y ⟶ X),
    IsAffine ((BigHOver.toScheme B S hS).obj X) →
    IsProper ((BigHOver.toScheme B S hS).map f) →
    Surjective ((BigHOver.toScheme B S hS).map f) →
    FinitePresentation ((BigHOver.toScheme B S hS).map f) →
    Presieve.IsSheafFor F (Presieve.singleton f)

/-- **Stacks 0EU5, (2) implies (2′).** Condition (2′) is the restriction of condition (2) to
an affine target, so it is implied by it with no use of condition (1). -/
@[stacks 0EU5 "(2) implies (2′)"]
public theorem IsProperFinitePresentationSheaf.affine
    (hF : BigHOver.IsProperFinitePresentationSheaf B S hS F) :
    BigHOver.IsAffineProperFinitePresentationSheaf B S hS F :=
  fun X Y f _ hproper hsurj hfp ↦ hF X Y f hproper hsurj hfp

/-- A family of morphisms of the site whose underlying family of morphisms of schemes is an h
covering generates a covering sieve of the h topology.

The family itself need not be one of the site's chosen covering families; the site's
representability axiom replaces it by a combinatorially equivalent chosen one, which generates
the same sieve. -/
public theorem sieve₀_mem_topology_of_isHCovering
    {X : BigHOver B S hS} (E : PreZeroHypercover.{u + 1} X)
    (hE : IsHCovering
      (E.map (BigHOver.toScheme B S hS)).X
      (E.map (BigHOver.toScheme B S hS)).f) :
    Sieve.generate E.presieve₀ ∈ BigHOver.topology B S hS X := by
  let K := BigHOver.forget B S hS
  let E' := E.map K
  have hE' : IsHCovering (E'.map B.inclusion).X (E'.map B.inclusion).f := by
    convert hE using 1 <;>
      simp [E', K, BigHOver.toScheme, PreZeroHypercover.map, Functor.comp_map]
  have hW : IsHCoveringInCutoff (κ := B.cutoff) ⟨X.left, E'⟩ := hE'
  obtain ⟨⟨T', V⟩, hV, hT, hcomb⟩ := B.covering_representative ⟨X.left, E'⟩ hW
  cases hT
  have hE'sieve : Sieve.generate E'.presieve₀ ∈ B.topology X.left := by
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb]
    exact B.precoverage.generate_mem_toGrothendieck ⟨V, rfl, hV⟩
  rw [BigHOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  apply B.topology.superset_covering _ hE'sieve
  rw [Sieve.generate_le_iff]
  rintro Y f ⟨i⟩
  exact ⟨E'.X i, 𝟙 _, E'.f i,
    ⟨E.X i, E.f i, 𝟙 _, ⟨i⟩, by simp [E', K, PreZeroHypercover.map]⟩,
    by simp⟩

/-- A sheaf on the big h site over `S` satisfies the sheaf condition for every family of
morphisms of the site whose underlying family of morphisms of schemes is an h covering. -/
public theorem isSheafFor_of_isHCovering
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F)
    {X : BigHOver B S hS} (E : PreZeroHypercover.{u + 1} X)
    (hE : IsHCovering
      (E.map (BigHOver.toScheme B S hS)).X
      (E.map (BigHOver.toScheme B S hS)).f) :
    Presieve.IsSheafFor F E.presieve₀ := by
  rw [Presieve.isSheafFor_iff_generate]
  exact hF.isSheafFor _ (sieve₀_mem_topology_of_isHCovering B S hS E hE)

/-- **Stacks 0EU5, a sheaf satisfies condition (1).** A sheaf on the big h site over `S`
satisfies the sheaf condition for Zariski coverings.

A jointly surjective family of open immersions is a Zariski covering, hence a ph covering by
Stacks 0DBH; its members are locally of finite presentation, so the family is an h
covering. -/
@[stacks 0EU5 "only if, condition (1)"]
public theorem isZariskiSheaf_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F) :
    BigHOver.IsZariskiSheaf B S hS F := by
  intro X E hE
  refine isSheafFor_of_isHCovering B S hS F hF E ?_
  let O : ((BigHOver.toScheme B S hS).obj X).OpenCover.{u + 1} :=
    ⟨E.map (BigHOver.toScheme B S hS), hE⟩
  refine ⟨fun i ↦ ?_, IsPHCovering.of_openCover O⟩
  have := O.map_prop i
  change LocallyOfFinitePresentation (O.f i)
  infer_instance

/-- **Stacks 0EU5, a sheaf satisfies condition (2).** A sheaf on the big h site over `S`
satisfies the sheaf condition for the one-element family attached to a morphism of the site
which is proper, surjective and of finite presentation.

Such a morphism is an h covering all by itself, by Stacks 0ETW. -/
@[stacks 0EU5 "only if, condition (2)"]
public theorem isProperFinitePresentationSheaf_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F) :
    BigHOver.IsProperFinitePresentationSheaf B S hS F := by
  intro X Y f hproper hsurj hfp
  have hE : IsHCovering
      ((PreZeroHypercover.singleton.{u + 1} f).map (BigHOver.toScheme B S hS)).X
      ((PreZeroHypercover.singleton.{u + 1} f).map (BigHOver.toScheme B S hS)).f :=
    (surjective_proper_isHCovering ((BigHOver.toScheme B S hS).map f) hfp).reindex
      (Equiv.ofUnique PUnit.{u + 2} Unit)
  have hFor := isSheafFor_of_isHCovering B S hS F hF
    (PreZeroHypercover.singleton.{u + 1} f) hE
  rwa [PreZeroHypercover.presieve₀_singleton] at hFor

/-- **Stacks 0EU5, condition (2) for a sheaf, in equalizer form.** Let `f : V ⟶ U` be a
morphism of the big h category over `S` whose underlying morphism of schemes is proper,
surjective and of finite presentation, and let `p₁, p₂ : W ⟶ V` complete `f` to a cartesian
square, so that `W = V ×_U V`.  Then a sheaf `F` on the big h site over `S` maps `F(U)`
bijectively onto the equalizer of the two maps `F(V) ⟶ F(W)`.

This is the form in which the source states condition (2).  The case of an affine target `U`
is condition (2′). -/
@[stacks 0EU5 "only if, condition (2) in equalizer form"]
public theorem bijective_mapToEqualizer_of_isSheaf
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F)
    {V U W : BigHOver B S hS} (f : V ⟶ U) (p₁ p₂ : W ⟶ V)
    (hW : IsPullback p₁ p₂ f f)
    (hproper : IsProper ((BigHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map f))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map f)) :
    Function.Bijective (regularTopology.mapToEqualizer F f p₁ p₂ hW.w) :=
  (isSheafFor_singleton_iff_bijective_mapToEqualizer f p₁ p₂ hW).1
    (isProperFinitePresentationSheaf_of_isSheaf B S hS F hF U V f hproper hsurj hfp)

section AffineReduction

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Properness, surjectivity and finite presentation of a morphism of the big h category over
`S` pass to its base change along an arbitrary morphism of the site.

The underlying morphism of schemes of the base change differs from the base change of the
underlying morphisms of schemes by the pullback comparison isomorphism, the inclusion of the
site into schemes preserving fibre products. -/
private theorem properSurjectiveFP_pullback_snd
    {X Y Z : BigHOver B S hS} (f : Y ⟶ X) (g : Z ⟶ X)
    (hproper : IsProper ((BigHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map f))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map f)) :
    IsProper ((BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)) ∧
      Surjective ((BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)) ∧
      FinitePresentation ((BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan (BigHOver.toScheme B S hS) :=
    inferInstance
  let : IsProper ((BigHOver.toScheme B S hS).map f) := hproper
  let : Surjective ((BigHOver.toScheme B S hS).map f) := hsurj
  let : LocallyOfFinitePresentation ((BigHOver.toScheme B S hS).map f) := hfp.1
  let : QuasiCompact ((BigHOver.toScheme B S hS).map f) := hfp.2.1
  let : QuasiSeparated ((BigHOver.toScheme B S hS).map f) := hfp.2.2
  have hcompIso : IsIso (Limits.pullbackComparison (BigHOver.toScheme B S hS) f g) :=
    inferInstance
  let : IsIso (Limits.pullbackComparison (BigHOver.toScheme B S hS) f g) := hcompIso
  have heq : (BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)
      = Limits.pullbackComparison (BigHOver.toScheme B S hS) f g
        ≫ Limits.pullback.snd ((BigHOver.toScheme B S hS).map f)
          ((BigHOver.toScheme B S hS).map g) :=
    (Limits.pullbackComparison_comp_snd _ _ _).symm
  rw [heq]
  exact ⟨inferInstance, inferInstance, ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The family of objects of the big h category over `S` attached to an open covering of the
underlying scheme of one of its objects: an open subscheme of an object of the site is again an
object of the site, by Stacks 000R (3). -/
public noncomputable def preZeroHypercoverOfOpenCover {X : BigHOver B S hS}
    (U : ((BigHOver.toScheme B S hS).obj X).OpenCover.{u + 1}) :
    PreZeroHypercover.{u + 1} X :=
  let T := (BigHOver.forget B S hS).obj X
  { I₀ := U.I₀
    X i := Over.mk
      ((ObjectProperty.homMk (U.f i) :
        (B.obj (U.X i) (Scheme.size_lt_of_isOpenImmersion (U.f i) T.2)) ⟶ T) ≫ X.hom)
    f i := Over.homMk (ObjectProperty.homMk (U.f i)) (by simp) }

/-- The family of the site attached to an open covering of the underlying scheme of an object
is a Zariski covering family. -/
private theorem preZeroHypercoverOfOpenCover_mem_zariskiPrecoverage {X : BigHOver B S hS}
    (U : ((BigHOver.toScheme B S hS).obj X).OpenCover.{u + 1}) :
    (((preZeroHypercoverOfOpenCover U).map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X)) := by
  simpa [preZeroHypercoverOfOpenCover, PreZeroHypercover.presieve₀, PreZeroHypercover.map]
    using U.mem₀

/-- Condition (1) applies to the family of the site attached to an open covering of the
underlying scheme of an object. -/
public theorem preZeroHypercoverOfOpenCover_isSheafFor {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F) (X : BigHOver B S hS)
    (U : ((BigHOver.toScheme B S hS).obj X).OpenCover.{u + 1}) :
    Presieve.IsSheafFor F (preZeroHypercoverOfOpenCover U).presieve₀ := by
  exact hZ X _ (preZeroHypercoverOfOpenCover_mem_zariskiPrecoverage U)

/-- **The family of objects of the big h category over `S` attached to an open covering of the
underlying scheme of one of its objects**: an open subscheme of an object of the site is again an
object of the site, by Stacks 000R (3).

This is the statement of `AlgebraicGeometry.BigHOver.openCoverOver`, which is internal to this
module.  Covering a base by affine opens and arguing over each is the standard move of every
descent argument on this site, so the family is named here for the arguments outside this module
that make it; the body is repeated rather than delegated because the consumers unfold it to read
off the members of the family. -/
public noncomputable def openCoverFamily {X : BigHOver B S hS}
    (U : ((BigHOver.toScheme B S hS).obj X).OpenCover.{u + 1}) :
    PreZeroHypercover.{u + 1} X :=
  let T := (BigHOver.forget B S hS).obj X
  { I₀ := U.I₀
    X i := Over.mk
      ((ObjectProperty.homMk (U.f i) :
        (B.obj (U.X i) (Scheme.size_lt_of_isOpenImmersion (U.f i) T.2)) ⟶ T) ≫ X.hom)
    f i := Over.homMk (ObjectProperty.homMk (U.f i)) (by simp) }

/-- The family of the site attached to an open covering of the underlying scheme of an object is
a Zariski covering family. -/
public theorem openCoverFamily_mem_zariskiPrecoverage {X : BigHOver B S hS}
    (U : ((BigHOver.toScheme B S hS).obj X).OpenCover.{u + 1}) :
    (((openCoverFamily U).map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X)) := by
  exact preZeroHypercoverOfOpenCover_mem_zariskiPrecoverage U

/-- A Zariski covering family of the big h category over `S` stays one after base change along
an arbitrary morphism of the site, the inclusion of the site into schemes preserving fibre
products. -/
private theorem zariskiPrecoverage_pullback₂ {X Y : BigHOver B S hS}
    (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X))
    (g : Y ⟶ X) :
    ((E.pullback₂ g).map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj Y) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan (BigHOver.toScheme B S hS) :=
    inferInstance
  let Eb := E.map (BigHOver.toScheme B S hS)
  let Eb' := Eb.pullback₂ ((BigHOver.toScheme B S hS).map g)
  have hmem : Eb'.presieve₀ ∈ Scheme.zariskiPrecoverage
      ((BigHOver.toScheme B S hS).obj Y) :=
    Scheme.zariskiPrecoverage.mem_coverings_of_isPullback Eb.f (by simpa [Eb] using hE)
      ((BigHOver.toScheme B S hS).map g)
      (fun i => Limits.pullback.snd (Eb.f i) ((BigHOver.toScheme B S hS).map g))
      (fun i => Limits.pullback.fst (Eb.f i) ((BigHOver.toScheme B S hS).map g))
      (fun i => (IsPullback.of_hasPullback (Eb.f i)
        ((BigHOver.toScheme B S hS).map g)).flip)
  have hIso : (E.pullback₂ g).map (BigHOver.toScheme B S hS) ≅ Eb' := by
    refine PreZeroHypercover.isoMk (Equiv.refl (E.pullback₂ g).I₀)
      (fun i => Limits.PreservesPullback.iso (BigHOver.toScheme B S hS) (E.f i) g) ?_
    intro i
    exact Limits.PreservesPullback.iso_hom_snd (BigHOver.toScheme B S hS) (E.f i) g
  exact Eb'.presieve₀_mem_of_iso hIso.symm hmem

/-- **A Zariski covering family of the big h category over `S` stays one after base change along
an arbitrary morphism of the site**, the inclusion of the site into schemes preserving fibre
products.

This is the statement of `AlgebraicGeometry.BigHOver.zariskiPrecoverage_pullback₂`, which is
internal to this module; it is the bookkeeping every argument that glues over a Zariski covering
of the base and then restricts along a further morphism needs, so it is named here for the
arguments outside this module that do so. -/
public alias mem_zariskiPrecoverage_pullback₂ := zariskiPrecoverage_pullback₂

/-- Condition (1) is stable under base change: the pullback of the sieve generated by a Zariski
covering family of the site along any morphism is again a sieve for which `F` satisfies the
sheaf condition, because a Zariski covering stays one after base change. -/
public theorem isSheafFor_pullback_of_zariskiCover {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    {X Y : BigHOver B S hS} (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X))
    (g : Y ⟶ X) :
    Presieve.IsSheafFor F ((Sieve.generate E.presieve₀).pullback g).arrows := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate,
    ← PreZeroHypercover.presieve₀_pullback₁]
  exact hZ Y (E.pullback₂ g) (zariskiPrecoverage_pullback₂ E hE g)

/-- Condition (1) makes the family attached to an open covering of the underlying scheme of an
object strongly sheaf for `F`: the overlaps are covered by the identity. -/
private theorem isStronglySheafFor_preZeroHypercoverOfOpenCover
    {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v} (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (X : BigHOver B S hS) (U : ((BigHOver.toScheme B S hS).obj X).OpenCover.{u + 1}) :
    (preZeroHypercoverOfOpenCover U).toPreOneHypercover.IsStronglySheafFor F := by
  refine ⟨preZeroHypercoverOfOpenCover_isSheafFor hZ X U, ?_⟩
  intro i j W a b hab
  have hid : ((preZeroHypercoverOfOpenCover U).toPreOneHypercover.sieve₁ a b) (𝟙 W) := by
    refine ⟨PUnit.unit, Limits.pullback.lift a b hab, ?_, ?_⟩
    · rw [Category.id_comp]
      exact (Limits.pullback.lift_fst a b hab).symm
    · rw [Category.id_comp]
      exact (Limits.pullback.lift_snd a b hab).symm
  intro x t₁ t₂ ht₁ ht₂
  simpa using (ht₁ (𝟙 W) hid).trans (ht₂ (𝟙 W) hid).symm

/-- Condition (1) is stable under base change: the pullback of the sieve generated by a Zariski
covering family of the site along any morphism is again a sieve for which `F` satisfies the
sheaf condition, because a Zariski covering stays one after base change. -/
private alias zariskiCover_pullback_isSheafFor := isSheafFor_pullback_of_zariskiCover

/-- Condition (2′) applied to the base change of a proper surjective morphism of finite
presentation along a morphism with affine source. -/
private theorem affineProperFP_pullback_isSheafFor {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hA : BigHOver.IsAffineProperFinitePresentationSheaf B S hS F)
    {X Y Z : BigHOver B S hS} (f : Y ⟶ X) (g : Z ⟶ X)
    (hAffine : IsAffine ((BigHOver.toScheme B S hS).obj Z))
    (hproper : IsProper ((BigHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map f))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map f)) :
    Presieve.IsSheafFor F (Presieve.singleton (Limits.pullback.snd f g)) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  obtain ⟨hp, hs, hq⟩ := properSurjectiveFP_pullback_snd f g hproper hsurj hfp
  exact hA Z (Limits.pullback f g) (Limits.pullback.snd f g) hAffine hp hs hq

/-- Under conditions (1) and (2′), the base change of a proper surjective morphism of finite
presentation along an arbitrary morphism of the site is a one-element family for which `F` is
separated: the target is covered by affine opens, over each of which condition (2′) applies to
a further base change. -/
private theorem properFP_pullback_isSeparated {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (hA : BigHOver.IsAffineProperFinitePresentationSheaf B S hS F)
    {X Y Z : BigHOver B S hS} (f : Y ⟶ X) (g : Z ⟶ X)
    (hproper : IsProper ((BigHOver.toScheme B S hS).map f))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map f))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map f)) :
    Presieve.IsSeparatedFor F (Presieve.singleton (Limits.pullback.snd f g)) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let p := Limits.pullback.snd f g
  let U0 := (Scheme.affineOpenCover.{u} ((BigHOver.toScheme B S hS).obj Z)).openCover
  let U : Scheme.OpenCover.{u + 1, u} ((BigHOver.toScheme B S hS).obj Z) :=
    U0.reindex (Equiv.ulift.{u + 1, u})
  let E := preZeroHypercoverOfOpenCover U
  have hE := preZeroHypercoverOfOpenCover_isSheafFor hZ Z U
  intro x t₁ t₂ ht₁ ht₂
  have hxy : F.map p.op t₁ = F.map p.op t₂ :=
    (ht₁ _ (Presieve.singleton_self _)).trans (ht₂ _ (Presieve.singleton_self _)).symm
  apply hE.isSeparatedFor.ext
  rintro W q ⟨i⟩
  let q₁ := E.f i
  let pᵢ := Limits.pullback.snd p q₁
  have hAffine : IsAffine ((BigHOver.toScheme B S hS).obj (E.X i)) :=
    Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
  obtain ⟨hp', hs', hq'⟩ := properSurjectiveFP_pullback_snd f g hproper hsurj hfp
  have hlocal := affineProperFP_pullback_isSheafFor hA p q₁ hAffine hp' hs' hq'
  have hlocalEq : F.map pᵢ.op (F.map q₁.op t₁) = F.map pᵢ.op (F.map q₁.op t₂) := by
    simpa only [pᵢ, ← types_comp_apply, ← F.map_comp, ← op_comp, Limits.pullback.condition]
      using congrArg (F.map (Limits.pullback.fst p q₁).op) hxy
  have hq₁ : F.map q₁.op t₁ = F.map q₁.op t₂ := by
    apply hlocal.isSeparatedFor.ext
    rintro T a ⟨⟩
    exact hlocalEq
  simpa [E, q₁, preZeroHypercoverOfOpenCover] using hq₁

/-- **Stacks 0EU5, (1) and (2′) imply (2).** Given the sheaf condition for Zariski coverings,
the sheaf condition for a proper surjective morphism of finite presentation need only be
checked when its target has affine underlying scheme.

The target `X` is covered by the affine opens of its underlying scheme, a Zariski covering of
the site; the base change of `f` over each of them has affine target, so condition (2′)
applies, and the base change over a fibre product of two of them is separated by
`properFP_pullback_isSeparated`.  The Zariski covering is strongly sheaf for `F` by condition
(1), and `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_of_pullback` assembles
the local sheaf conditions into the sheaf condition for `{f}` itself. -/
@[stacks 0EU5 "(1) and (2′) imply (2)"]
public theorem isProperFinitePresentationSheaf_of_affine
    {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (hA : BigHOver.IsAffineProperFinitePresentationSheaf B S hS F) :
    BigHOver.IsProperFinitePresentationSheaf B S hS F := by
  intro X Y f hproper hsurj hfp
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let Xs := (BigHOver.toScheme B S hS).obj X
  let U0 := (Scheme.affineOpenCover.{u} Xs).openCover
  let U : Scheme.OpenCover.{u + 1, u} Xs := U0.reindex (Equiv.ulift.{u + 1, u})
  let E := preZeroHypercoverOfOpenCover U
  let E₁ := E.toPreOneHypercover
  have hstrong := isStronglySheafFor_preZeroHypercoverOfOpenCover hZ X U
  have h₂ : ∀ ⦃Z : BigHOver B S hS⦄ (g : Z ⟶ X),
      Presieve.IsSeparatedFor F (E₁.sieve₀.pullback g).arrows := by
    intro Z g
    have hlocal := zariskiCover_pullback_isSheafFor hZ E
      (preZeroHypercoverOfOpenCover_mem_zariskiPrecoverage U) g
    simpa [E₁, E] using hlocal.isSeparatedFor
  have hlocal (i : E₁.I₀) :
      Presieve.IsSheafFor F
        ((Sieve.generate (Presieve.singleton f)).pullback (E₁.f i)).arrows := by
    have hAffine : IsAffine ((BigHOver.toScheme B S hS).obj (E₁.X i)) :=
      Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
    rw [← Sieve.pullbackArrows_comm, Presieve.pullback_singleton,
      ← Presieve.isSheafFor_iff_generate]
    exact affineProperFP_pullback_isSheafFor hA f (E₁.f i) hAffine hproper hsurj hfp
  have hlocal' ⦃i j : E₁.I₀⦄ (k : E₁.I₁ i j) :
      Presieve.IsSeparatedFor F
        ((Sieve.generate (Presieve.singleton f)).pullback (E₁.p₁ k ≫ E₁.f i)).arrows := by
    rw [← Sieve.pullbackArrows_comm, Presieve.pullback_singleton,
      ← Presieve.isSeparatedFor_iff_generate]
    exact properFP_pullback_isSeparated hZ hA f (E₁.p₁ k ≫ E₁.f i) hproper hsurj hfp
  exact PreOneHypercover.IsStronglySheafFor.isSheafFor_of_pullback
    hstrong h₂ (R := Presieve.singleton f) hlocal hlocal'

/-- **Stacks 0EU5, the final assertion.** Given the sheaf condition for Zariski coverings,
condition (2) of Stacks 0EU5 is equivalent to its restriction (2′) to morphisms whose target
has affine underlying scheme. -/
@[stacks 0EU5 "given (1), (2) is equivalent to (2′)"]
public theorem isProperFinitePresentationSheaf_iff_affine
    {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F) :
    BigHOver.IsProperFinitePresentationSheaf B S hS F ↔
      BigHOver.IsAffineProperFinitePresentationSheaf B S hS F :=
  ⟨BigHOver.IsProperFinitePresentationSheaf.affine B S hS F,
    isProperFinitePresentationSheaf_of_affine hZ⟩

end AffineReduction

section Sufficiency

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Under condition (2), the pushforward along a proper surjective morphism of finite
presentation of a sieve all of whose base changes `F` is a sheaf for is again a presieve `F`
is a sheaf for.

The sieve generated by the one-element family `{g}` is bound with the pullbacks of the given
sieve along a choice of factorization, and `CategoryTheory.Presieve.isSheafFor_bind`
recognizes the result as the pushforward. -/
private theorem isSheafFor_pushforward_of_properFP {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hP : BigHOver.IsProperFinitePresentationSheaf B S hS F)
    {U X : BigHOver B S hS} (g : U ⟶ X) (O : Sieve U)
    (hO : ∀ ⦃Y : BigHOver B S hS⦄ (a : Y ⟶ U),
      Presieve.IsSheafFor F (O.pullback a).arrows)
    (hproper : IsProper ((BigHOver.toScheme B S hS).map g))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map g))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map g)) :
    Presieve.IsSheafFor F (O.pushforward g : Presieve X) := by
  classical
  let R := Sieve.generateSingleton g
  let lift : ∀ {Y : BigHOver B S hS} (f : Y ⟶ X), R f → (Y ⟶ U) :=
    fun {_} f hf => if hs : O.pushforward g f then Classical.choose hs else Classical.choose hf
  have hlift : ∀ {Y : BigHOver B S hS} (f : Y ⟶ X) (hf : R f), lift f hf ≫ g = f := by
    intro Y f hf
    dsimp [lift]
    split_ifs with hs
    · exact (Classical.choose_spec hs).1
    · exact Classical.choose_spec hf
  have hliftO : ∀ {Y : BigHOver B S hS} (f : Y ⟶ X) (hf : R f),
      O.pushforward g f → O (lift f hf) := by
    intro Y f hf hs
    dsimp [lift]
    simp only [dite_eq_left hs]
    exact (Classical.choose_spec hs).2
  let D : ∀ ⦃Y : BigHOver B S hS⦄ ⦃f : Y ⟶ X⦄, R f → Sieve Y :=
    fun {_} {f} hf => O.pullback (lift f hf)
  have hR : Presieve.IsSheafFor F (R : Presieve X) := by
    have hsing : Presieve.IsSheafFor F (Presieve.singleton g) := hP X U g hproper hsurj hfp
    simpa [R, Sieve.generateSingleton_eq] using
      (Presieve.isSheafFor_iff_generate (Presieve.singleton g)).1 hsing
  have hbind := Presieve.isSheafFor_bind F R D hR
    (fun {_} {_} hf => hO (lift _ hf))
    (by
      intro Y f hf Z q
      simpa [D, Sieve.pullback_comp] using (hO (q ≫ lift f hf)).isSeparatedFor)
  have hEq : Sieve.bind R D = O.pushforward g := by
    ext Y f
    constructor
    · rintro ⟨Z, q, r, hq, hr, rfl⟩
      change ∃ a, a ≫ g = q ≫ r ∧ O a
      exact ⟨q ≫ lift r hq, by rw [Category.assoc, hlift], hr⟩
    · rintro ⟨a, rfl, ha⟩
      refine ⟨Y, 𝟙 Y, a ≫ g, ?_, ?_, by simp⟩
      · exact ⟨a, rfl⟩
      · change O (𝟙 Y ≫ lift (a ≫ g) ⟨a, rfl⟩)
        exact hliftO (a ≫ g) ⟨a, rfl⟩ ⟨a, rfl, ha⟩
  simpa [hEq] using hbind

/-- Under condition (2), a family obtained by composing a family of morphisms into `U` whose
generated sieve `F` is a sheaf for after any base change with a proper surjective morphism of
finite presentation `U ⟶ X` is a family `F` is a sheaf for. -/
private theorem isSheafFor_composite_of_properFP {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hP : BigHOver.IsProperFinitePresentationSheaf B S hS F)
    {U X : BigHOver B S hS} (g : U ⟶ X)
    {I : Type (u + 1)} {V : I → BigHOver B S hS} (j : ∀ i, V i ⟶ U)
    (hO : ∀ ⦃Y : BigHOver B S hS⦄ (a : Y ⟶ U),
      Presieve.IsSheafFor F ((Sieve.generate (Presieve.ofArrows V j)).pullback a).arrows)
    (hproper : IsProper ((BigHOver.toScheme B S hS).map g))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map g))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map g)) :
    Presieve.IsSheafFor F (Presieve.ofArrows V (fun i ↦ j i ≫ g)) := by
  let O : Sieve U := Sieve.generate (Presieve.ofArrows V j)
  have hEq : Sieve.generate (Presieve.ofArrows V (fun i ↦ j i ≫ g)) = O.pushforward g := by
    rw [← Sieve.generate_pushforward, Presieve.pushforward_ofArrows]
  rw [Presieve.isSheafFor_iff_generate, hEq]
  exact isSheafFor_pushforward_of_properFP hP g O hO hproper hsurj hfp

/-- Under conditions (1) and (2), a family of the site of the shape used by the source's proof
satisfies the sheaf condition: a Zariski covering family of an object `Y`, each member composed
with a fixed proper surjective morphism of finite presentation `G : Y ⟶ X`.

This is the only shape of family needed, because Stacks 0ETU refines every h covering of an
affine scheme by one of this shape. -/
private theorem isSheafFor_zariskiComp_properFP {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (hP : BigHOver.IsProperFinitePresentationSheaf B S hS F)
    {X Y : BigHOver B S hS} (G : Y ⟶ X)
    (hproper : IsProper ((BigHOver.toScheme B S hS).map G))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map G))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map G))
    (D : PreZeroHypercover.{u + 1} Y)
    (hD : (D.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj Y)) :
    Presieve.IsSheafFor F (Presieve.ofArrows D.X (fun k ↦ D.f k ≫ G)) :=
  isSheafFor_composite_of_properFP hP G D.f
    (fun {_} a ↦ isSheafFor_pullback_of_zariskiCover hZ D hD a) hproper hsurj hfp

/-- The base change of a family of the previous shape is a family of the same shape: the sieve
generated by the base changed family is the pullback of the sieve generated by the original
one. -/
private theorem generate_ofArrows_zariskiComp_pullback {X Y Z : BigHOver B S hS}
    (G : Y ⟶ X) (D : PreZeroHypercover.{u + 1} Y) (q : Z ⟶ X) :
    Sieve.generate (Presieve.ofArrows
        (fun k : D.I₀ ↦ Limits.pullback (D.f k) (Limits.pullback.fst G q))
        (fun k : D.I₀ ↦ Limits.pullback.snd (D.f k) (Limits.pullback.fst G q)
          ≫ Limits.pullback.snd G q))
      = (Sieve.generate (Presieve.ofArrows D.X (fun k ↦ D.f k ≫ G))).pullback q := by
  ext W h
  constructor
  · rintro ⟨T, a, b, ⟨k⟩, rfl⟩
    refine ⟨D.X k,
      a ≫ Limits.pullback.fst (D.f k) (Limits.pullback.fst G q), D.f k ≫ G,
      Presieve.ofArrows.mk k, ?_⟩
    rw [Category.assoc, Limits.pullback.condition_assoc, Limits.pullback.condition]
    simp only [Category.assoc]
  · rintro ⟨T, a, b, ⟨k⟩, hab⟩
    have hw : (a ≫ D.f k) ≫ G = h ≫ q := (Category.assoc _ _ _).trans hab
    let l : W ⟶ Limits.pullback G q := Limits.pullback.lift (a ≫ D.f k) h hw
    have hl₁ : l ≫ Limits.pullback.fst G q = a ≫ D.f k := Limits.pullback.lift_fst _ _ _
    have hl₂ : l ≫ Limits.pullback.snd G q = h := Limits.pullback.lift_snd _ _ _
    refine ⟨_, Limits.pullback.lift a l hl₁.symm, _, Presieve.ofArrows.mk k, ?_⟩
    rw [← Category.assoc, Limits.pullback.lift_snd, hl₂]

/-- Under conditions (1) and (2), the pullback along an arbitrary morphism of the sieve
generated by a family of the previous shape is a sieve for which `F` is separated: the base
change of the whole configuration is a configuration of the same shape. -/
private theorem isSeparatedFor_pullback_zariskiComp_properFP
    {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (hP : BigHOver.IsProperFinitePresentationSheaf B S hS F)
    {X Y Z : BigHOver B S hS} (G : Y ⟶ X)
    (hproper : IsProper ((BigHOver.toScheme B S hS).map G))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map G))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map G))
    (D : PreZeroHypercover.{u + 1} Y)
    (hD : (D.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj Y))
    (q : Z ⟶ X) :
    Presieve.IsSeparatedFor F
      ((Sieve.generate (Presieve.ofArrows D.X (fun k ↦ D.f k ≫ G))).pullback q).arrows := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  obtain ⟨hp', hs', hq'⟩ := properSurjectiveFP_pullback_snd G q hproper hsurj hfp
  have hD' := zariskiPrecoverage_pullback₂ D hD (Limits.pullback.fst G q)
  have hsheaf := isSheafFor_zariskiComp_properFP hZ hP (Limits.pullback.snd G q)
    hp' hs' hq' (D.pullback₂ (Limits.pullback.fst G q)) hD'
  rw [← generate_ofArrows_zariskiComp_pullback G D q]
  exact ((Presieve.isSheafFor_iff_generate _).1 hsheaf).isSeparatedFor

/-- **The local form of the sufficiency direction of Stacks 0EU5.** Under conditions (1) and
(2), a family of morphisms of the big h category over `S` whose target has affine underlying
scheme and whose underlying family of morphisms of schemes is an h covering satisfies the sheaf
condition.

This is the heart of the source's proof: Stacks 0ETU refines the h covering of the affine
scheme by the finite family of affine opens of a single proper surjective morphism of finite
presentation `p : Y ⟶ T`, which is a family of the shape handled by
`isSheafFor_zariskiComp_properFP`; the sheaf condition passes from the refining family to the
original one by the refinement criterion of Stacks 0G1L, whose injectivity hypothesis is the
separatedness supplied by `isSeparatedFor_pullback_zariskiComp_properFP`. -/
private theorem isSheafFor_hCovering_affine {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (hP : BigHOver.IsProperFinitePresentationSheaf B S hS F)
    {X : BigHOver B S hS} [IsAffine ((BigHOver.toScheme B S hS).obj X)]
    (E : PreZeroHypercover.{u + 1} X)
    (hE : IsHCovering
      (E.map (BigHOver.toScheme B S hS)).X
      (E.map (BigHOver.toScheme B S hS)).f) :
    Presieve.IsSheafFor F E.presieve₀ := by
  classical
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  obtain ⟨J, Y, p, V, j, hfinJ, hproper, hsurj, hfpp, haff, hopen, hcover, hrefine⟩ :=
    exists_finitePresentation_proper_refinement_of_isHCovering
      (E.map (BigHOver.toScheme B S hS)).X (E.map (BigHOver.toScheme B S hS)).f hE
  have hT : ((BigHOver.toScheme B S hS).obj X).size < B.cutoff := X.left.property
  let : IsProper p := hproper
  have hY : Y.size < B.cutoff := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hT
  let Yobj : BigHOver B S hS :=
    Over.mk ((ObjectProperty.homMk p : B.obj Y hY ⟶ (BigHOver.forget B S hS).obj X) ≫ X.hom)
  let G : Yobj ⟶ X := Over.homMk (ObjectProperty.homMk p) (by simp [Yobj])
  have hproperG : IsProper ((BigHOver.toScheme B S hS).map G) := hproper
  have hsurjG : Surjective ((BigHOver.toScheme B S hS).map G) := hsurj
  have hfpG : FinitePresentation ((BigHOver.toScheme B S hS).map G) := hfpp
  let OY : ((BigHOver.toScheme B S hS).obj Yobj).OpenCover.{u + 1} :=
    { I₀ := ULift.{u + 1} J
      X k := V k.down
      f k := j k.down
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, fun k ↦ hopen k.down⟩
        have hx : x ∈ ⋃ k, Set.range (j k) := by
          rw [hcover]
          exact Set.mem_univ x
        obtain ⟨k, y, rfl⟩ := Set.mem_iUnion.mp hx
        exact ⟨ULift.up k, y, rfl⟩ }
  let D : PreZeroHypercover.{u + 1} Yobj := preZeroHypercoverOfOpenCover OY
  have hD := preZeroHypercoverOfOpenCover_mem_zariskiPrecoverage OY
  have hVsheaf := isSheafFor_zariskiComp_properFP hZ hP G hproperG hsurjG hfpG D hD
  -- the refinement data supplied by Stacks 0ETU, read in the site
  choose α h hcomp using fun k : J ↦ hrefine k
  let αD : D.I₀ → E.I₀ := fun k ↦ α k.down
  have hcD : ∀ k : D.I₀,
      (ObjectProperty.homMk (h k.down) : (D.X k).left ⟶ (E.X (αD k)).left)
        ≫ (E.f (αD k)).left = (D.f k).left ≫ G.left := by
    intro k
    apply B.inclusion.map_injective
    exact hcomp k.down
  let fD : ∀ k : D.I₀, D.X k ⟶ E.X (αD k) := fun k ↦
    Over.homMk (ObjectProperty.homMk (h k.down) : (D.X k).left ⟶ (E.X (αD k)).left)
      (by rw [← Over.w (E.f (αD k)), ← Category.assoc, hcD k, Category.assoc, Over.w G,
        Over.w (D.f k)])
  have hfD : ∀ k : D.I₀, fD k ≫ E.f (αD k) = D.f k ≫ G := fun k ↦
    Over.OverMorphism.ext (hcD k)
  let UV : E.I₀ → D.I₀ → BigHOver B S hS :=
    fun i k ↦ Limits.pullback (D.f k ≫ G) (E.f i)
  let uvToV : ∀ i k, UV i k ⟶ D.X k :=
    fun i k ↦ Limits.pullback.fst (D.f k ≫ G) (E.f i)
  let uvToU : ∀ i k, UV i k ⟶ E.X i :=
    fun i k ↦ Limits.pullback.snd (D.f k ≫ G) (E.f i)
  have huv : ∀ i k, uvToV i k ≫ (D.f k ≫ G) = uvToU i k ≫ E.f i :=
    fun i k ↦ Limits.pullback.condition
  have hsep (i : E.I₀) : Presieve.IsSeparatedFor F
      (Presieve.ofArrows (fun k ↦ UV i k) (uvToU i)) := by
    have hs := isSeparatedFor_pullback_zariskiComp_properFP hZ hP G hproperG hsurjG hfpG
      D hD (E.f i)
    intro x t₁ t₂ ht₁ ht₂
    apply hs.ext
    intro Z q hq
    rcases hq with ⟨W, a, b, hb, hab⟩
    rcases hb with ⟨k⟩
    let l : Z ⟶ UV i k := Limits.pullback.lift a q (by simpa using hab)
    have heq := (ht₁ (uvToU i k) (Presieve.ofArrows.mk k)).trans
      (ht₂ (uvToU i k) (Presieve.ofArrows.mk k)).symm
    have hl := congrArg (F.map l.op) heq
    simpa [l, uvToU, ← types_comp_apply, ← F.map_comp, ← op_comp,
      Limits.pullback.lift_snd] using hl
  have hinj (i : E.I₀) : Function.Injective
      (fun s : F.obj (op (E.X i)) ↦ fun k : D.I₀ ↦ F.map (uvToU i k).op s) := by
    intro s t hst
    let x : Presieve.FamilyOfElements F
        (Presieve.ofArrows (fun k ↦ UV i k) (uvToU i)) :=
      fun _ g _ ↦ F.map g.op s
    apply hsep i x s t
    · intro Z g _
      rfl
    · intro Z g hg
      rcases hg with ⟨k⟩
      exact (congrFun hst k).symm
  have hEq : Presieve.ofArrows E.X E.f = E.presieve₀ := rfl
  rw [← hEq]
  exact isSheafFor_ofArrows_of_refinement E.X D.X UV E.f (fun k ↦ D.f k ≫ G) αD fD hfD
    uvToV uvToU huv (fun _ _ ↦ inferInstance)
    (fun _ _ ↦ Limits.pullbackIsPullback _ _) (fun _ _ ↦ inferInstance) F hVsheaf hinj

/-- Under condition (1), separatedness for a sieve follows from the sheaf condition for its
pullbacks along morphisms with affine source: the affine opens of the underlying scheme of the
target form a Zariski covering family of the site. -/
public theorem isSeparatedFor_of_affine_pullbacks {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    {X : BigHOver B S hS} (R : Sieve X)
    (H : ∀ (Y : BigHOver B S hS) (f : Y ⟶ X),
      IsAffine ((BigHOver.toScheme B S hS).obj Y) →
      Presieve.IsSheafFor F (R.pullback f).arrows) :
    Presieve.IsSeparatedFor F R.arrows := by
  let U₀ := (Scheme.affineOpenCover.{u} ((BigHOver.toScheme B S hS).obj X)).openCover
  let U := U₀.reindex (Equiv.ulift.{u + 1, u})
  let E := preZeroHypercoverOfOpenCover U
  intro x s t hs ht
  apply (preZeroHypercoverOfOpenCover_isSheafFor hZ X U).isSeparatedFor.ext
  rintro Y f ⟨i⟩
  have hA : IsAffine ((BigHOver.toScheme B S hS).obj (E.X i)) :=
    Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
  apply (H (E.X i) (E.f i) hA).isSeparatedFor.ext
  intro Z g hg
  simpa only [← types_comp_apply, ← F.map_comp, ← op_comp] using
    (hs (g ≫ E.f i) hg).trans (ht (g ≫ E.f i) hg).symm

/-- Under condition (1), the sheaf condition for a sieve follows from the sheaf condition for
its pullbacks along morphisms with affine source. -/
public theorem isSheafFor_of_affine_pullbacks {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    {X : BigHOver B S hS} (R : Sieve X)
    (H : ∀ (Y : BigHOver B S hS) (f : Y ⟶ X),
      IsAffine ((BigHOver.toScheme B S hS).obj Y) →
      Presieve.IsSheafFor F (R.pullback f).arrows) :
    Presieve.IsSheafFor F R.arrows := by
  let U₀ := (Scheme.affineOpenCover.{u} ((BigHOver.toScheme B S hS).obj X)).openCover
  let U := U₀.reindex (Equiv.ulift.{u + 1, u})
  let E := preZeroHypercoverOfOpenCover U
  let E₁ := E.toPreOneHypercover
  have hstrong := isStronglySheafFor_preZeroHypercoverOfOpenCover hZ X U
  apply hstrong.isSheafFor_sieve_of_pullback
  · intro Y f
    exact (zariskiCover_pullback_isSheafFor hZ E
      (preZeroHypercoverOfOpenCover_mem_zariskiPrecoverage U) f).isSeparatedFor
  · intro i
    exact H (E.X i) (E.f i)
      (Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i))
  · intro i j k
    apply isSeparatedFor_of_affine_pullbacks hZ
    intro Y f hY
    rw [← Sieve.pullback_comp]
    exact H Y _ hY

/-- The chosen covering families of a big h site, packaged as a coverage: the site's base
change axiom provides, for every chosen family and every morphism, a chosen family of the
source refining the base change. -/
private def hCoverage (B : BigHSite.{u}) : Coverage B.Schemes where
  toPrecoverage := B.precoverage
  pullback := by
    intro X Y f R hR
    obtain ⟨E, rfl, hE⟩ := (B.mem_precoverage_iff).mp hR
    obtain ⟨P, p, q, hpq, hP⟩ := B.isSite.2.2 ⟨X, E⟩ hE Y f
    refine ⟨Presieve.ofArrows P q, ⟨⟨E.I₀, P, q⟩, rfl, hP⟩, ?_⟩
    rintro Z g ⟨i⟩
    exact ⟨E.X i, p i, E.f i, ⟨i⟩, (hpq i).w⟩

/-- Under conditions (1) and (2), the pullback along a morphism with affine source of the sieve
of the slice generated by a chosen covering family of the big h site is a sieve `F` is a sheaf
for: the base change axiom of the site turns it into the sieve generated by an h covering
family of an affine object, to which `isSheafFor_hCovering_affine` applies. -/
private theorem isSheafFor_covering_over_affine_pullback
    {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (hP : BigHOver.IsProperFinitePresentationSheaf B S hS F)
    {X Y : BigHOver B S hS}
    (E : PreZeroHypercover.{u + 1} X.left) (hE : B.IsCovering ⟨X.left, E⟩)
    (f : Y ⟶ X) (hY : IsAffine ((BigHOver.toScheme B S hS).obj Y)) :
    Presieve.IsSheafFor F
      (((Sieve.overEquiv X).symm (Sieve.generate E.presieve₀)).pullback f).arrows := by
  obtain ⟨P, p, q, hpq, hPc⟩ := B.isSite.2.2 ⟨X.left, E⟩ hE Y.left f.left
  let D : PreZeroHypercover.{u + 1} Y :=
    { I₀ := E.I₀
      X i := Over.mk (q i ≫ Y.hom)
      f i := Over.homMk (q i) }
  have hD : IsHCovering
      (D.map (BigHOver.toScheme B S hS)).X
      (D.map (BigHOver.toScheme B S hS)).f := hPc.h
  let : IsAffine ((BigHOver.toScheme B S hS).obj Y) := hY
  have hsheaf := (Presieve.isSheafFor_iff_generate D.presieve₀).mp
    (isSheafFor_hCovering_affine hZ hP D hD)
  convert hsheaf using 1
  congr 1
  ext Z g
  rw [Sieve.pullback_apply, Sieve.overEquiv_symm_iff]
  constructor
  · rintro ⟨W, a, b, ⟨i⟩, hab⟩
    have hw : a ≫ E.f i = g.left ≫ f.left := hab
    let l := (hpq i).lift a g.left hw
    have hl : l ≫ q i = g.left := (hpq i).lift_snd _ _ _
    let k : Z ⟶ D.X i := Over.homMk l (by
      dsimp [D]
      rw [← Category.assoc, hl, Over.w])
    exact ⟨D.X i, k, D.f i, ⟨i⟩, Over.OverMorphism.ext hl⟩
  · rintro ⟨W, a, b, ⟨i⟩, hab⟩
    refine ⟨E.X i, a.left ≫ p i, E.f i, ⟨i⟩, ?_⟩
    have hw : a.left ≫ q i = g.left := congrArg Over.Hom.left hab
    rw [Category.assoc, (hpq i).w, ← Category.assoc, hw]
    rfl

/-- **Stacks 0EU5, the sufficiency direction.** Conditions (1) and (2) together force a
presheaf of sets on the big h category over `S` to be a sheaf for the h topology. -/
@[stacks 0EU5 "if, (1) and (2) imply the sheaf condition"]
public theorem isSheaf_of_isZariskiSheaf_of_isProperFinitePresentationSheaf
    {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (hP : BigHOver.IsProperFinitePresentationSheaf B S hS F) :
    Presieve.IsSheaf (BigHOver.topology B S hS) F := by
  have hle : BigHOver.topology B S hS ≤ Sheaf.finestTopologySingle F := by
    change B.precoverage.toGrothendieck.over (B.obj S hS) ≤ _
    change (hCoverage B).toPrecoverage.toGrothendieck.over (B.obj S hS) ≤ _
    rw [Coverage.toGrothendieck_toPrecoverage]
    apply over_le_of_coverage
    intro X R hR
    obtain ⟨E, rfl, hE⟩ := (B.mem_precoverage_iff).mp hR
    intro Y f
    apply isSheafFor_of_affine_pullbacks hZ
    intro Z g hZ'
    rw [← Sieve.pullback_comp]
    exact isSheafFor_covering_over_affine_pullback hZ hP E hE (g ≫ f) hZ'
  intro X R hR
  simpa using hle X hR X (𝟙 X)

end Sufficiency

/-- **Stacks 0EU5, the characterization.** A presheaf of sets on the big h category over `S` is
a sheaf for the h topology if and only if it satisfies condition (1), the sheaf condition for
Zariski coverings, and condition (2), the sheaf condition for every morphism of the site which
is proper, surjective and of finite presentation.

By `AlgebraicGeometry.isSheafFor_singleton_iff_bijective_mapToEqualizer` condition (2) is the
source's requirement that the sections over the target map bijectively onto the equalizer of
the two maps to the sections over `V ×_U V`. -/
@[stacks 0EU5 "sheaf characterization"]
public theorem isSheaf_iff_isZariskiSheaf_and_isProperFinitePresentationSheaf
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (BigHOver.topology B S hS) F ↔
      (BigHOver.IsZariskiSheaf B S hS F ∧
        BigHOver.IsProperFinitePresentationSheaf B S hS F) := by
  refine ⟨fun hF ↦ ⟨isZariskiSheaf_of_isSheaf B S hS F hF,
    isProperFinitePresentationSheaf_of_isSheaf B S hS F hF⟩, fun ⟨hZ, hP⟩ ↦ ?_⟩
  exact (isSheaf_iff_isSheaf_of_type _ _).2
    (isSheaf_of_isZariskiSheaf_of_isProperFinitePresentationSheaf hZ hP)

end BigHOver

end AlgebraicGeometry

end
