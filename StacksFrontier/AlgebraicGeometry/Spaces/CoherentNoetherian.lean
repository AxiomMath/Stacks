module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf

/-!
# Coherence of a module on a locally Noetherian algebraic space

Let `F` be an algebraic space over a scheme `S` which is locally Noetherian, in the sense of
Stacks 03E6 for the étale-local scheme property `AlgebraicGeometry.IsLocallyNoetherian`.  A
module on `F` which is *cartesian on affine charts* is then coherent exactly when it is
quasi-coherent and of finite type.  This is the implication (2) ⇒ (1) of Stacks 07UB, with the
remaining input — passing from quasi-coherence to the base change property of the sections over
an affine chart, which is Stacks 03DX(2) — carried as the explicit hypothesis
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`.

What this file adds to `StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules` is the *discharge
of the covering*.  The general forms proved there carry an abstract predicate `Good` on étale
charts together with three hypotheses about it: that the `Good` charts cover, that they are
affine, and that their rings of sections are Noetherian.  Here `Good` is instantiated with
affineness together with Noetherianity of the ring of global sections, which makes the second
and third hypotheses projections of `Good` itself; the covering hypothesis is the one that needs
local Noetherianity of `F`, and it is
`AlgebraicGeometry.Space.exists_covering_through_noetherianAffine`, which lives downstream of
`CoherentModules` and so cannot be used there.  What is left is `IsCartesianOnAffineCharts`.

## Main results

All three live in the namespace `AlgebraicGeometry.Space`, whose name is dropped here because
the third of them is too long to qualify on one line.

* `isFiniteType_relations_of_isCartesian_of_isLocallyNoetherian`: on a locally Noetherian
  algebraic space, the relations among a finite family of sections of a module cartesian on
  affine charts are of finite type on the slice site.
* `isCoherentOnSite_of_isCartesian_of_isLocallyNoetherian`: such a module is coherent on the
  small étale ringed site as soon as it is of finite type.
* `isCoherent_iff_isQuasicoherent_and_isFiniteType_of_isCartesian_of_isLocallyNoetherian` is
  the resulting form of Stacks 07UB(1) ⇔ 07UB(2).

## Implementation notes

The three results carry `IsCartesianOnAffineCharts` and therefore do **not** carry
`@[stacks 07UB]`.  Deriving it from `SheafOfModules.IsQuasicoherentOnSite` is the chart
criterion `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, which is
not imported here; the hypothesis is the same one carried by
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSections` and by the kernel and cokernel results
built on it, and no second spelling of it is introduced.  Its name is part of each name below
for that reason: the three general forms in `CoherentModules` carry it too, so what distinguishes
these is only the discharge of the covering, and both inputs are named.

Two partial discharges of the hypothesis are already in the tree, and between them they say what
is still owed.  A module which is *globally* a coproduct of copies of `𝒪_F` satisfies it
outright, by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isColimit_cofan`; and
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` obtains it from
essential surjectivity of the associated-module functor on the slices at affine charts.  Both of
those are confined to module universe `u`, the first because `SheafOfModules.free` exists only
there.  Neither gets as far as quasi-coherence: `SheafOfModules.IsQuasicoherentOnSite` presents
the module only on the members of *some* covering of an affine chart, and the passage from that
to a presentation over the chart itself is the localization step of Stacks 03DX(2) which neither
lemma performs.

The general forms in `CoherentModules` ask for the base change property only *between the `Good`
charts*, so a module trivialized on each chart of a covering satisfies them with no 03DX input
at all; that is the route of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent`, and it is why the three
results below, which fix `Good` before knowing the module, are the ones that still have to carry
`IsCartesianOnAffineCharts` in full.

The module universe here is free, as it is in Stacks 07UB(2).  Nothing in this file synthesizes
a sheafification, a cokernel or an abelian structure on the ambient category of modules, and
neither `SheafOfModules.IsQuasicoherentOnSite`, `SheafOfModules.IsCoherentOnSite`,
`PresheafOfModules.IsFiniteType` nor `IsCartesianOnAffineCharts` pins it; in particular
Mathlib's universe-pinned `SheafOfModules.IsFiniteType` is deliberately not named, the
sectionwise `PresheafOfModules.IsFiniteType` of Stacks 03DL being used instead.

`AlgebraicGeometry.Space.IsNoetherianAffineChart` exists only so that the `Good`
predicate is written once; each result below is a single application of the corresponding
general form of `CoherentModules`, with no proof duplicated.  The passage between the site's own
`(smallEtaleRingedSite …).C`/`.J` projections and `AlgebraicGeometry.Space.SmallEtale` with
`AlgebraicGeometry.Space.SmallEtale.topology` is definitional, and so is the identification of
the ring of global sections with `AlgebraicGeometry.Space.chartRing`.  The two spellings of the
category of charts carry different `CategoryTheory.Category` instance terms and may not be mixed
under `rw`, so every statement below is phrased with the ringed site's projections, as the
general forms are.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- An étale chart of `F` is a *Noetherian affine chart* when the scheme underlying it is affine
with Noetherian ring of global sections.  Affineness is `AlgebraicGeometry.Space.IsAffineChart`
rather than a second spelling of it.

This is the `Good` predicate with which the general coherence results of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules` are instantiated below.  It is spelled as
in `AlgebraicGeometry.Space.exists_covering_through_noetherianAffine`, which is what supplies the
covering, and its two components discharge the remaining two hypotheses of those results, each
by a projection and each only up to definitional equality: the affineness hypothesis there is
phrased with the composite functor `SmallEtale.toOver ⋙ BigFppfOver.toScheme` and the Noetherian
one with `AlgebraicGeometry.Space.chartRing`. -/
abbrev IsNoetherianAffineChart (A : SmallEtale B S hS F) : Prop :=
  IsAffineChart B S hS F A ∧
    IsNoetherianRing (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj A))))

/-- **The relations clause of coherence on a locally Noetherian algebraic space.**  The
relations among a finite family of sections of a module cartesian on affine charts, over any
étale chart `U` of a locally Noetherian algebraic space, are of finite type on the slice site
at `U`.

This is `AlgebraicGeometry.Space.isFiniteType_relations_of_isCartesian` with its covering
hypotheses discharged at the Noetherian affine charts. -/
theorem isFiniteType_relations_of_isCartesian_of_isLocallyNoetherian
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, m} B S hS F hF) (hcart : IsCartesianOnAffineCharts M)
    (U : (smallEtaleRingedSite B S hS F hF).C) (n : ℕ) (s : Fin n → M.val.obj (op U)) :
    PresheafOfModules.IsFiniteType ((smallEtaleRingedSite B S hS F hF).J.over U)
      (PresheafOfModules.relations M.val s) :=
  isFiniteType_relations_of_isCartesian B S hS F hF M (IsNoetherianAffineChart B S hS F)
    (exists_covering_through_noetherianAffine B S hS F hF Fact.out)
    (fun _ hA => hA.1) (fun _ hA => hA.2)
    (fun _ _ hA hA' f => hcart _ _ hA.1 hA'.1 f) U n s

/-- **Stacks 07UB(2) ⇒ 07UB(1) on the site, modulo Stacks 03DX(2).**  A module of finite type on
a locally Noetherian algebraic space which is cartesian on affine charts is coherent on the
small étale ringed site.

Quasi-coherence of the module is not used: it is the base change criterion `hcart` which
replaces it, and over an affine chart that criterion is what quasi-coherence gives by
Stacks 03DX(2). -/
theorem isCoherentOnSite_of_isCartesian_of_isLocallyNoetherian
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, m} B S hS F hF) (hcart : IsCartesianOnAffineCharts M)
    (hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J M.val) :
    SheafOfModules.IsCoherentOnSite M :=
  { isFiniteType := hft
    kernel_isFiniteType := isFiniteType_relations_of_isCartesian_of_isLocallyNoetherian
      B S hS F hF M hcart }

/-- **Stacks 07UB(1) ⇔ 07UB(2), modulo Stacks 03DX(2).**  A module on a locally Noetherian
algebraic space which is cartesian on affine charts is coherent exactly when it is
quasi-coherent and of finite type.

The forward direction is the two parent projections of `AlgebraicGeometry.Space.IsCoherent` and
needs neither the hypothesis `hcart` nor local Noetherianity; the reverse direction is
`AlgebraicGeometry.Space.isCoherentOnSite_of_isCartesian_of_isLocallyNoetherian`.  The module
universe is free, as it is in Stacks 07UB(2).

The single hypothesis `hcart` is Stacks 03DX(2) for the charts of `F`, so this statement does
not carry `@[stacks 07UB]`. -/
theorem isCoherent_iff_isQuasicoherent_and_isFiniteType_of_isCartesian_of_isLocallyNoetherian
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, m} B S hS F hF) (hcart : IsCartesianOnAffineCharts M) :
    IsCoherent B S hS F hF M ↔
      (M.IsQuasicoherentOnSite ∧
        PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J M.val) :=
  isCoherent_iff_isQuasicoherent_and_isFiniteType_of_isCartesian B S hS F hF M
    (IsNoetherianAffineChart B S hS F)
    (exists_covering_through_noetherianAffine B S hS F hF Fact.out)
    (fun _ hA => hA.1) (fun _ hA => hA.2)
    (fun _ _ hA hA' f => hcart _ _ hA.1 hA'.1 f)

end AlgebraicGeometry.Space

end
