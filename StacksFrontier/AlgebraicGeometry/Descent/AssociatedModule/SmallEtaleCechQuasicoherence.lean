module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianQcoh
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence

/-!
# Quasi-coherence of the cohomology of a complex on the small étale site

Let `S` be a scheme of a big étale site.  The quasi-coherent `𝒪`-modules of the small étale site
of `S` form a weak Serre subcategory, `AlgebraicGeometry.SmallEtale.isWeakSerreClass_qcohOnSite`,
so the cohomology of a cochain complex all of whose terms are quasi-coherent on the site is again
quasi-coherent on the site, and therefore also cartesian on the affine objects.  That is this
file.

## Why this is here

It is the consumer side of the Čech route to the étale half of [Stacks, Tag 071N] above degree
zero, the route recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQcqsPushforward.lean`.  For a
quasi-compact quasi-separated `a : X ⟶ Y` the higher direct image `R ⁱ (ε_a)_*(𝓕ᵃ)` is to be
computed by a Čech complex whose terms are direct images along *affine* morphisms, for which
quasi-coherence on the site is unconditional
(`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward`).  Everything such a
computation feeds into is below: once the comparison is available as an isomorphism of
`𝒪`-modules on `Y_étale` between `R ⁱ (ε_a)_*(𝓕ᵃ)` and the cohomology of that complex,
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_iso_homology` and
`AlgebraicGeometry.SmallEtale.isCartesianOnAffines_of_iso_homology` deliver quasi-coherence on
the site and the cartesian condition in every degree, with no hypothesis on the degree.

**What is still owed is exactly the comparison isomorphism itself** — the Čech- or
Mayer--Vietoris-to-derived-functor comparison for `(ε_a)_*` along a finite affine cover of `X`.
Nothing below supplies it, and nothing below pretends to: the complex and the isomorphism are
both hypotheses.  The development has the Čech-to-derived-functor comparison for *derived
sections* in many forms — `Stacks.CechSite.FinalCover.cechDerivedIso` and
`Stacks.CechSite.Acyclic.cechCohomologyIsoRightDerivedSections` among them — but none for a
*direct image*, i.e. none producing a complex of `𝒪`-modules on the target site rather than a
complex of modules over a ring.

## Main results

* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_homology`: the cohomology of a complex of
  `𝒪`-modules on `S_étale` whose terms are quasi-coherent on the site is quasi-coherent on the
  site.
* `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_homology`: the same cohomology is cartesian
  on the affine objects.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_iso_homology` and
  `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_of_iso_homology`: the two statements above
  transported along an isomorphism, which is the form a Čech comparison is consumed in.

## Implementation notes

No new homological algebra appears here.  `CategoryTheory.ObjectProperty.prop_homology` of
`StacksFrontier/AlgebraicGeometry/Perfect/PseudoCoherentComplex/Coherence.lean` already proves the
statement for an arbitrary weak Serre subcategory of an arbitrary abelian category — the
cohomology at `j` is a cokernel of a map into a kernel of a map between terms — and
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_qcohOnSite` is the instance that applies it to
`AlgebraicGeometry.SmallEtale.qcohOnSite`.  The three closure conditions that instance rests on
are in `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentWeakSerre.lean`.

The index type and the complex shape are arbitrary, so the results apply to a cochain complex
indexed by `ℕ` — the indexing a Čech complex comes in — as well as to one indexed by `ℤ`.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {ι : Type*} {c : ComplexShape ι}

/-- **The cohomology of a complex of quasi-coherent `𝒪`-modules on the small étale site is
quasi-coherent on the site.**  The quasi-coherent `𝒪`-modules of `S_étale` are a weak Serre
subcategory, `AlgebraicGeometry.SmallEtale.isWeakSerreClass_qcohOnSite`, and the cohomology of a
complex with terms in a weak Serre subcategory lies in it, by
`CategoryTheory.ObjectProperty.prop_homology`. -/
theorem isQuasicoherentOnSite_homology
    (C : HomologicalComplex (SheafOfModules.{u} (structureSheaf B S hS)) c)
    (hC : ∀ m, (C.X m).IsQuasicoherentOnSite) (j : ι) [C.HasHomology j] :
    (C.homology j).IsQuasicoherentOnSite :=
  ObjectProperty.prop_homology (qcohOnSite B S hS) C j hC

/-- **The cohomology of a complex of quasi-coherent `𝒪`-modules on the small étale site is
cartesian on the affine objects.**  This is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_homology` read through
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffines`. -/
theorem isCartesianOnAffines_homology
    (C : HomologicalComplex (SheafOfModules.{u} (structureSheaf B S hS)) c)
    (hC : ∀ m, (C.X m).IsQuasicoherentOnSite) (j : ι) [C.HasHomology j] :
    IsCartesianOnAffines B S hS (C.homology j) :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffines B S hS _).1
    (isQuasicoherentOnSite_homology B S hS C hC j)

/-- **An `𝒪`-module on the small étale site isomorphic to the cohomology of a complex of
quasi-coherent `𝒪`-modules is quasi-coherent on the site.**

This is the form in which a Čech-to-derived-functor comparison is consumed: the comparison
supplies the complex `C` and the isomorphism `e`, and quasi-coherence of the terms of `C` comes,
in the intended application, from `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward`
for the direct images along the affine morphisms of a cover. -/
theorem isQuasicoherentOnSite_of_iso_homology
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    (C : HomologicalComplex (SheafOfModules.{u} (structureSheaf B S hS)) c)
    (hC : ∀ m, (C.X m).IsQuasicoherentOnSite) (j : ι) [C.HasHomology j]
    (e : G ≅ C.homology j) : G.IsQuasicoherentOnSite :=
  (qcohOnSite B S hS).prop_of_iso e.symm (isQuasicoherentOnSite_homology B S hS C hC j)

/-- **An `𝒪`-module on the small étale site isomorphic to the cohomology of a complex of
quasi-coherent `𝒪`-modules is cartesian on the affine objects.**  The cartesian form of
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_iso_homology`, which is the shape the
degree-zero argument of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQcqsPushforward.lean`
consumes. -/
theorem isCartesianOnAffines_of_iso_homology
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    (C : HomologicalComplex (SheafOfModules.{u} (structureSheaf B S hS)) c)
    (hC : ∀ m, (C.X m).IsQuasicoherentOnSite) (j : ι) [C.HasHomology j]
    (e : G ≅ C.homology j) : IsCartesianOnAffines B S hS G :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffines B S hS _).1
    (isQuasicoherentOnSite_of_iso_homology B S hS C hC j e)

end AlgebraicGeometry.SmallEtale

end
