module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSpacesEtaleGlobalVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheafCohomologyVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongASliceFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks

/-!
# Stacks 03F9 on the spaces-étale site of an affine algebraic space

Let `Y` be an **affine** algebraic space over a scheme `S` contained in a big fppf site `B`, and
let `F` be an abelian sheaf on the spaces-étale site of `Y` of [Stacks, Tag 03G0], with
coefficients in `AddCommGrpCat.{u + 1}`, the morphism universe of that site.  This file proves
that the positive-degree *global* cohomology of `F` vanishes as soon as the positive-degree Čech
cohomology of the restriction of `F` along the comparison of [Stacks, Tag 03G1] vanishes on the
finite covering families, by affine étale charts, of an affine étale chart.

The proof is the Čech criterion of [Stacks, Tag 03F9] applied on the spaces-étale site, with the
collection `B` of that criterion taken to be the objects isomorphic to the image of an affine
étale chart, and its collection `Cov` the images of the finite affine covering families.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.affineChartImages` — the collection `B` of
  [Stacks, Tag 03F9] used here: the objects of the spaces-étale site isomorphic to the image of
  an affine étale chart under the comparison of [Stacks, Tag 03G1].
* `AlgebraicGeometry.Space.SpacesEtale.comparisonOver` — the comparison of [Stacks, Tag 03G1]
  read on the slice at a chart and composed with the transport along a morphism out of the
  image of that chart.
* `AlgebraicGeometry.Space.SpacesEtale.imageAffineCov` — the collection `Cov` of
  [Stacks, Tag 03F9] used here.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.imageAffineCov_cofinal` — the hypothesis `hCovCofinal`
  of [Stacks, Tag 03F9], and with it the three others: the families it produces are the images
  of finite affine covering families, transported along an isomorphism.
* `AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH'_of_isZero_cechCohomology` —
  [Stacks, Tag 03F9] on the spaces-étale site, at the images of the affine charts.
* `AlgebraicGeometry.Space.subsingleton_sheafH_spacesEtale_of_isZero_cechCohomology` — **the
  positive-degree global cohomology, on the spaces-étale site of an affine algebraic space, of
  an abelian sheaf with vanishing positive-degree Čech cohomology on the small étale site.**

## Implementation notes

*Why the spaces-étale site and not the small étale one.*  The criterion ties three universes
together: the site must have its morphisms in `Type (max v w)` for `w` the universe indexing the
covering families, and the coefficients must be `AddCommGrpCat.{max v w}`.  The Čech input a
companion file discharges is a `CategoryTheory.PreZeroHypercover.{u + 1}` with coefficients in
`AddCommGrpCat.{u + 1}`, so `w = u + 1`; the small étale site has its morphisms in `Type u` and
cannot carry it, while the spaces-étale site has them in `Type (u + 1)` and can.  This is the
same statement as `AlgebraicGeometry.Space.SmallEtale.isZero_sheafH'_of_isZero_cechCohomology`
one universe up, and that file is the model for this one throughout.

*The smallness the tagged criterion asks for is free here.*  The objects of the spaces-étale
site live in `Type (u + 1)`, so `Small.{u + 1}` of it is `Small.self`, and
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero` applies as it stands; the
variant `_of_enoughInjectives`, which the small étale site needs because its objects live one
universe above its morphisms, is not required.  The three universe arguments are given
explicitly, as `.{u + 1, u + 1, u + 1}`, for the reason the model file records: the elaborator
does not read `v` off `max v w`.

*The collection `B` has to be closed under isomorphism*, and the spelling here gives that for
free.  It cannot be the image of the affine charts on the nose: the third clause of
`hCovObjects` is about the iterated fibre products, computed in the spaces-étale site, of the
members of a family, and those are only *isomorphic* to the images of the iterated fibre
products computed in the small étale site — which is all
`AlgebraicGeometry.Space.SmallEtale.isAffine_chartScheme_piObj` speaks about.  The comparison is
`Stacks.CechSite.cechProductMapOfSliceFunctor`, invertible because the comparison functor
preserves fibre products, which is `AlgebraicGeometry.Space.preservesPullbacks_comparisonFunctor`
and condition (2) of [Stacks, Tag 00WV].

*The collection `Cov` carries the conclusions the criterion asks of its members.*  Its
definition is the conjunction of the three clauses of `hCovObjects` and of the Čech vanishing,
so `hProducts`, `hCovObjects` and `hCech` are projections and all the work sits in
`hCovCofinal`, which is where the families are built and where everything about them is known.
The alternative — defining `Cov` as the families that *are* images of finite affine families,
transported along an isomorphism — states the same thing but has to destructure that data again
in three places.

*The Čech transfer is run on the slice.*  What is wanted is the Čech cohomology of the
transported image family `{F(V_j) → U}`, where `U ≅ F(W)`, and no functor of sites carries the
small étale site to the spaces-étale site *over `U`*.  What does exist is the functor
`AlgebraicGeometry.Space.SpacesEtale.comparisonOver` of the slices, `Over W ⥤ Over U`, and
`StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongASliceFunctor` is exactly the
Čech comparison along such a functor: the transported family is
`Stacks.CechSite.sliceImageFamily`, and `Stacks.CechSite.sliceCechCohomologyIsoOfSliceFunctor`
identifies its Čech cohomology with that of the original family with restricted coefficients.
The restriction is the one wanted because
`AlgebraicGeometry.Space.SpacesEtale.comparisonOver_comp_forget` holds by definition.

*The index universe of the covering families is `u + 1`*, that being where the Čech input is
stated.  `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement` produces its
family indexed by a `Type`, so it is reindexed by `ULift.{u + 1}`, exactly as
`AlgebraicGeometry.Space.SmallEtale.affineChartCov_cofinal` reindexes by `ULift.{u}`.  The
affineness of the iterated fibre products, however, is available only at index universe `u`:
`AlgebraicGeometry.Space.SmallEtale.isAffine_chartScheme_piObj` is stated for a
`CategoryTheory.PreZeroHypercover.{u}`.  So the same family is presented twice, at `ULift.{u}`
and at `ULift.{u + 1}`; no transport is needed between them, because a tuple of members is
indexed by `Fin (p + 1)` and the two presentations select the *same* objects of `Over W`, so the
two products are the same object and not merely isomorphic ones.

*Why `HasFiniteLimits (Over U)` is a `local instance`* for both sites, and not registered: the
small étale site has no terminal object in general, so the slices' finite limits do not come
from the site's, and a global instance would oblige every consumer of either site to carry it.
That is the choice `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheafCohomologyVanishing`
makes, and the instances are needed in the *statements* here as well.

*The passage from cohomology over an object to global cohomology* is the one
`AlgebraicGeometry.Space.subsingleton_sheafH_of_isQuasicoherentOnSite` performs on the small
étale site: `Y` being affine, the image under the comparison of the chart presented by a
representing isomorphism is a terminal object of the spaces-étale site, by
`AlgebraicGeometry.Space.isTerminal_comparisonFunctor_representingChart`, and it lies in `B`
because its chart scheme is the representing affine scheme; then
`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'` converts.

No `@[stacks]` attribute is claimed.  [Stacks, Tag 03F9] is registered on
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero`; what is here is its
application on one site.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS)

/-- The slice of the small étale site at a chart has finite limits: the chart is a terminal
object of its own slice, and the site has pullbacks.  Local to this file, as the module
documentation explains; it is the instance
`AlgebraicGeometry.Space.hasFiniteLimits_overChart` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheafCohomologyVanishing`, which is local
there too. -/
local instance hasFiniteLimits_overSmallEtaleChart (W : SmallEtale B S hS Y.1) :
    HasFiniteLimits (Over W) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The slice of the spaces-étale site at an object has finite limits, for the same reason: the
object is terminal in its own slice and the site has pullbacks. -/
local instance hasFiniteLimits_overSpacesEtale (U : SpacesEtale B S hS Y) :
    HasFiniteLimits (Over U) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

namespace SpacesEtale

/-- **The collection `B` of [Stacks, Tag 03F9] on the spaces-étale site of an algebraic
space**: the objects isomorphic to the image, under the comparison of [Stacks, Tag 03G1], of an
étale chart whose underlying scheme is affine.

Closure under isomorphism is not a convenience but what the criterion needs, and the module
documentation explains why the images on the nose will not do. -/
def affineChartImages : Set (SpacesEtale B S hS Y) :=
  {U | ∃ W : SmallEtale B S hS Y.1, IsAffine (chartScheme W) ∧
    Nonempty (U ≅ (comparisonFunctor B S hS Y).obj W)}

/-- The comparison of [Stacks, Tag 03G1] read on the slices: the slice of the small étale site
at a chart `W` is carried to the slice of the spaces-étale site at an object `U` equipped with a
morphism `e` out of the image of `W`, by taking the image of an object over `W` and composing its
structure morphism with `e`.

For `e` an isomorphism this is the functor along which a covering family of `W` is transported
to a covering family of `U`; see the module documentation. -/
def comparisonOver {U : SpacesEtale B S hS Y} {W : SmallEtale B S hS Y.1}
    (e : (comparisonFunctor B S hS Y).obj W ⟶ U) : Over W ⥤ Over U :=
  Over.post (comparisonFunctor B S hS Y) ⋙ Over.map e

/-- Forgetting the structure morphism after `AlgebraicGeometry.Space.SpacesEtale.comparisonOver`
is the comparison functor applied after forgetting it.  This holds by definition, and it is what
makes the Čech comparison on the slice land on the restriction of the coefficients along the
comparison functor rather than on some transport of it. -/
theorem comparisonOver_comp_forget {U : SpacesEtale B S hS Y} {W : SmallEtale B S hS Y.1}
    (e : (comparisonFunctor B S hS Y).obj W ⟶ U) :
    comparisonOver B S hS Y e ⋙ Over.forget U =
      Over.forget W ⋙ comparisonFunctor B S hS Y :=
  rfl

/-- `AlgebraicGeometry.Space.SpacesEtale.comparisonOver` at an isomorphism preserves the
iterated fibre products of a covering family: the comparison functor preserves fibre products,
by `AlgebraicGeometry.Space.preservesPullbacks_comparisonFunctor`, so `CategoryTheory.Over.post`
of it preserves those products of the slice, and transport along an isomorphism is an
equivalence. -/
theorem preservesLimit_comparisonOver {U : SpacesEtale B S hS Y} {W : SmallEtale B S hS Y.1}
    (e : (comparisonFunctor B S hS Y).obj W ⟶ U) [IsIso e]
    (D : PreZeroHypercover.{u + 1} W) (n : ℕ) (i : Fin (n + 1) → D.I₀) :
    PreservesLimit (Discrete.functor (fun a ↦ Over.mk (D.f (i a))))
      (comparisonOver B S hS Y e) := by
  have := preservesPullbacks_comparisonFunctor B S hS Y
  have : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (D.f (i a))))
      (Over.post (comparisonFunctor B S hS Y)) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost (comparisonFunctor B S hS Y) D
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  show PreservesLimit _ (Over.post (comparisonFunctor B S hS Y) ⋙ Over.map e)
  infer_instance

/-- **The collection `Cov` of [Stacks, Tag 03F9] on the spaces-étale site of an algebraic
space**: the covering families of an object of
`AlgebraicGeometry.Space.SpacesEtale.affineChartImages` whose members and iterated fibre
products are again such objects, and whose positive-degree Čech cohomology with coefficients in
`F` vanishes.

That is, `Cov` is defined by the conclusions the criterion asks of its members, so that its
three remaining hypotheses are projections; the content is that these families are cofinal,
which is `AlgebraicGeometry.Space.SpacesEtale.imageAffineCov_cofinal`. -/
def imageAffineCov (F : Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1})
    (U : SpacesEtale B S hS Y) :
    Set { E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ SpacesEtale.topology B S hS Y U } :=
  {E | U ∈ affineChartImages B S hS Y ∧
    (∀ i, E.1.X i ∈ affineChartImages B S hS Y) ∧
    (∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
      (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ affineChartImages B S hS Y) ∧
    ∀ p : ℕ, 0 < p → IsZero (Stacks.CechSite.cechCohomology E.1 F.obj p)}

/-- **The hypothesis `hCovObjects` of [Stacks, Tag 03F9]**, verbatim: the target of a selected
covering family, each of its members and each of its iterated fibre products is an object
isomorphic to the image of an affine chart.  These are three of the four clauses defining
`AlgebraicGeometry.Space.SpacesEtale.imageAffineCov`. -/
theorem imageAffineCov_covObjects
    (F : Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1})
    {U : SpacesEtale B S hS Y}
    (E : { E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ SpacesEtale.topology B S hS Y U })
    (hE : E ∈ imageAffineCov B S hS Y F U) :
    U ∈ affineChartImages B S hS Y ∧
      (∀ i, E.1.X i ∈ affineChartImages B S hS Y) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := fun _ _ ↦ inferInstance
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ affineChartImages B S hS Y :=
  ⟨hE.1, hE.2.1, hE.2.2.1⟩

/-- **The hypothesis `hCovCofinal` of [Stacks, Tag 03F9]**, verbatim, and with it the content of
all four: every covering sieve of an object isomorphic to the image `F(W)` of an affine chart is
refined by a selected covering family.

Given an isomorphism `e : U ≅ F(W)`, the sieve is transported along `e` and pulled back along
the comparison functor — a covering sieve again, the comparison being cocontinuous,
`AlgebraicGeometry.Space.comparisonFunctor_specialCocontinuous` — then refined by a finite
family of affine charts, which is
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`, the sieve-level form of
Stacks 0218 on the small étale site.  The image of that family under
`AlgebraicGeometry.Space.SpacesEtale.comparisonOver` at `e.inv` is the family produced here: it
covers because the comparison is cover preserving, it refines the original sieve because each of
its arrows was chosen in the pullback, its members and iterated fibre products are images of
affine charts up to isomorphism, and its Čech cohomology is that of the original family with
coefficients restricted along the comparison, by
`Stacks.CechSite.sliceCechCohomologyIsoOfSliceFunctor`. -/
theorem imageAffineCov_cofinal
    (F : Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1})
    (hCech : ∀ {W : SmallEtale B S hS Y.1}, IsAffine (chartScheme W) →
      ∀ E : PreZeroHypercover.{u + 1} W, Finite E.I₀ →
        (∀ i, IsAffine (chartScheme (E.X i))) →
        E.sieve₀ ∈ SmallEtale.topology B S hS Y.1 W →
        ∀ p : ℕ, 0 < p →
          IsZero (Stacks.CechSite.cechCohomology E
            ((comparisonFunctor B S hS Y).op ⋙ F.obj) p))
    (U : SpacesEtale B S hS Y) (hU : U ∈ affineChartImages B S hS Y)
    (R : Sieve U) (hR : R ∈ SpacesEtale.topology B S hS Y U) :
    ∃ E : { E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ SpacesEtale.topology B S hS Y U },
      E ∈ imageAffineCov B S hS Y F U ∧ E.1.sieve₀ ≤ R := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hU
  have := (comparisonFunctor_specialCocontinuous B S hS Y).1
  -- The covering sieve `R`, transported to the image chart and pulled back into the small site.
  have hR₂ : Sieve.functorPullback (comparisonFunctor B S hS Y) (Sieve.pullback e.inv R) ∈
      SmallEtale.topology B S hS Y.1 W :=
    (comparisonFunctor B S hS Y).cover_lift (SmallEtale.topology B S hS Y.1)
      (SpacesEtale.topology B S hS Y) ((SpacesEtale.topology B S hS Y).pullback_stable e.inv hR)
  obtain ⟨ι, hfin, V, g, hVaff, hle, hcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS Y.1 W hW _ hR₂
  set D : PreZeroHypercover.{u + 1} W :=
    { I₀ := ULift.{u + 1} ι, X := fun j ↦ V j.down, f := fun j ↦ g j.down }
  have hpre : Presieve.ofArrows (fun j : ULift.{u + 1} ι ↦ V j.down) (fun j ↦ g j.down) =
      Presieve.ofArrows V g := by
    refine le_antisymm ?_ ?_
    · rintro Z k ⟨j⟩; exact ⟨j.down⟩
    · rintro Z k ⟨j⟩; exact ⟨ULift.up j⟩
  have hDsieve : D.sieve₀ = Sieve.ofArrows V g := by
    show Sieve.generate (Presieve.ofArrows _ _) = _
    rw [Sieve.ofArrows, hpre]
  have hDcov : D.sieve₀ ∈ SmallEtale.topology B S hS Y.1 W := hDsieve ▸ hcov
  have hDaff : ∀ j, IsAffine (chartScheme (D.X j)) := fun j ↦ hVaff j.down
  have hDfin : Finite D.I₀ := inferInstance
  -- The same family at the index universe of the schemes, where the affineness of the iterated
  -- fibre products is already available; the two families select the same objects of `Over W`.
  set D' : PreZeroHypercover.{u} W :=
    { I₀ := ULift.{u} ι, X := fun j ↦ V j.down, f := fun j ↦ g j.down }
  have hpi : ∀ (p : ℕ) (i : Fin (p + 1) → D.I₀),
      IsAffine (chartScheme (∏ᶜ (fun a ↦ Over.mk (D.f (i a)))).left) := fun p i ↦
    SmallEtale.isAffine_chartScheme_piObj B S hS Y.1 hW D' (fun j ↦ hVaff j.down) p
      (fun a ↦ ULift.up (i a).down)
  set v := comparisonOver B S hS Y e.inv
  have hpres : ∀ (n : ℕ) (i : Fin (n + 1) → D.I₀),
      PreservesLimit (Discrete.functor (fun a ↦ Over.mk (D.f (i a)))) v :=
    fun n i ↦ preservesLimit_comparisonOver B S hS Y e.inv D n i
  have hiso : ∀ (n : ℕ) (i : Fin (n + 1) → D.I₀),
      IsIso (Stacks.CechSite.cechProductMapOfSliceFunctor D v n i) :=
    fun n i ↦ Stacks.CechSite.isIso_cechProductMapOfSliceFunctor D v n i
  set E : PreZeroHypercover.{u + 1} U := Stacks.CechSite.sliceImageFamily D v
  have hEf : ∀ j, E.f j = (comparisonFunctor B S hS Y).map (D.f j) ≫ e.inv := fun _ ↦ rfl
  -- The image family refines `R`.
  have hER : ∀ j, R.arrows (E.f j) := by
    intro j
    have h₁ : Sieve.functorPullback (comparisonFunctor B S hS Y) (Sieve.pullback e.inv R)
        (D.f j) := hle _ (Sieve.ofArrows_mk V g j.down)
    exact hEf j ▸ h₁
  have hEle : E.sieve₀ ≤ R := by
    intro Z₀ k hk
    obtain ⟨Z₁, a, b, ⟨j⟩, hab⟩ := hk
    exact hab ▸ R.downward_closed (hER j) a
  -- The image family is a covering family: the family `D` is carried to a covering family of
  -- the image chart, the comparison being cover preserving, and transported along `e`.
  have hEcov : E.sieve₀ ∈ SpacesEtale.topology B S hS Y U := by
    have h₂ : Sieve.ofArrows (fun j : D.I₀ ↦ (comparisonFunctor B S hS Y).obj (D.X j))
        (fun j ↦ (comparisonFunctor B S hS Y).map (D.f j)) ∈
        SpacesEtale.topology B S hS Y ((comparisonFunctor B S hS Y).obj W) := by
      have h₃ := (Functor.IsDenseSubsite.coverPreserving (SmallEtale.topology B S hS Y.1)
        (SpacesEtale.topology B S hS Y) (comparisonFunctor B S hS Y)).cover_preserve hDcov
      rw [← PreZeroHypercover.sieve₀_map] at h₃
      exact h₃
    have key : Sieve.pullback e.hom
          (Sieve.ofArrows (fun j : D.I₀ ↦ (comparisonFunctor B S hS Y).obj (D.X j))
            (fun j ↦ (comparisonFunctor B S hS Y).map (D.f j))) ≤
        Sieve.ofArrows (fun j : D.I₀ ↦ (comparisonFunctor B S hS Y).obj (D.X j))
          (fun j ↦ (comparisonFunctor B S hS Y).map (D.f j) ≫ e.inv) := by
      intro Z₀ k hk
      obtain ⟨Z₁, a, b, ⟨j⟩, hab⟩ := hk
      refine ⟨_, a, _, ⟨j⟩, ?_⟩
      rw [← Category.assoc, hab, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (SpacesEtale.topology B S hS Y).superset_covering key
      ((SpacesEtale.topology B S hS Y).pullback_stable e.hom h₂)
  refine ⟨⟨E, hEcov⟩, ⟨⟨W, hW, ⟨e⟩⟩, fun j ↦ ⟨D.X j, hDaff j, ⟨Iso.refl _⟩⟩, ?_, ?_⟩, hEle⟩
  · intro p i
    have := hiso p i
    exact ⟨(∏ᶜ (fun a ↦ Over.mk (D.f (i a)))).left,
      hpi p i,
      ⟨((Over.forget U).mapIso
        (asIso (Stacks.CechSite.cechProductMapOfSliceFunctor D v p i))).symm⟩⟩
  · intro p hp
    refine IsZero.of_iso ?_ (Stacks.CechSite.sliceCechCohomologyIsoOfSliceFunctor D v
      ((Over.forget U).op ⋙ F.obj) hiso p)
    exact hCech hW D hDfin hDaff hDcov p hp

/-- **[Stacks, Tag 03F9] on the spaces-étale site of an algebraic space, at the images of the
affine charts.**  An abelian sheaf whose positive-degree Čech cohomology, read on the small
étale site through the comparison of [Stacks, Tag 03G1], vanishes on every finite covering
family of an affine chart by affine charts has vanishing positive-degree cohomology over every
object isomorphic to the image of an affine chart.

Cohomology is Mathlib's `CategoryTheory.Sheaf.H'`, the `Ext`-group out of the free abelian sheaf
on the object, at the morphism universe `u + 1` of the category of abelian sheaves. -/
theorem isZero_sheafH'_of_isZero_cechCohomology
    (F : Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1})
    (hCech : ∀ {W : SmallEtale B S hS Y.1}, IsAffine (chartScheme W) →
      ∀ E : PreZeroHypercover.{u + 1} W, Finite E.I₀ →
        (∀ i, IsAffine (chartScheme (E.X i))) →
        E.sieve₀ ∈ SmallEtale.topology B S hS Y.1 W →
        ∀ p : ℕ, 0 < p →
          IsZero (Stacks.CechSite.cechCohomology E
            ((comparisonFunctor B S hS Y).op ⋙ F.obj) p))
    (U : SpacesEtale B S hS Y) (hU : U ∈ affineChartImages B S hS Y) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u + 1} F p U) :=
  letI : Small.{u + 1} (SpacesEtale B S hS Y) := small_self _
  Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero.{u + 1, u + 1, u + 1, u + 1}
    (SpacesEtale.topology B S hS Y) (affineChartImages B S hS Y)
    (imageAffineCov B S hS Y F)
    (fun _ _ _ _ ↦ inferInstance)
    (fun E hE ↦ imageAffineCov_covObjects B S hS Y F E hE)
    (fun V hV R hR ↦ imageAffineCov_cofinal B S hS Y F hCech V hV R hR)
    F (fun _ hE q hq ↦ hE.2.2.2 q hq) U hU p hp

end SpacesEtale

variable {B S hS Y}

/-- **The positive-degree global cohomology, on the spaces-étale site of an affine algebraic
space, of an abelian sheaf whose Čech cohomology vanishes on the small étale site.**

Let `Y` be an algebraic space over `S` which is representable by an affine scheme of the ambient
big fppf site, and let `F` be an abelian sheaf on the spaces-étale site of `Y` of
[Stacks, Tag 03G0] with coefficients in `AddCommGrpCat.{u + 1}`.  Suppose that for every étale
chart `W` of `Y` with affine underlying scheme and every finite covering family of `W` by charts
with affine underlying schemes, the positive-degree Čech cohomology of the restriction of `F`
along the comparison of [Stacks, Tag 03G1] vanishes.  Then

  `H^q(Y, F) = 0` for every `q > 0`,

the cohomology being Mathlib's `CategoryTheory.Sheaf.H`, the global cohomology of the
spaces-étale site.

This is `AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH'_of_isZero_cechCohomology` at the
image of the chart presented by the representing isomorphism, which is affine and terminal. -/
theorem subsingleton_sheafH_spacesEtale_of_isZero_cechCohomology
    (hY : IsAffineSpace B S hS Y.1)
    (F : Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1})
    (hCech : ∀ {W : SmallEtale B S hS Y.1}, IsAffine (chartScheme W) →
      ∀ E : PreZeroHypercover.{u + 1} W, Finite E.I₀ →
        (∀ i, IsAffine (chartScheme (E.X i))) →
        E.sieve₀ ∈ SmallEtale.topology B S hS Y.1 W →
        ∀ p : ℕ, 0 < p →
          IsZero (Stacks.CechSite.cechCohomology E
            ((comparisonFunctor B S hS Y).op ⋙ F.obj) p))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hY
  refine (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'
    (SpacesEtale.topology B S hS Y) F q
    ((comparisonFunctor B S hS Y).obj (representingChart B S hS Y T i))
    (isTerminal_comparisonFunctor_representingChart B S hS Y T i)).2 ?_
  refine AddCommGrpCat.isZero_iff_subsingleton.mp ?_
  exact SpacesEtale.isZero_sheafH'_of_isZero_cechCohomology B S hS Y F hCech _
    ⟨representingChart B S hS Y T i, hT, ⟨Iso.refl _⟩⟩ q hq

end AlgebraicGeometry.Space

end
