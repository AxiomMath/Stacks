module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentSpellings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteCoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedAboveDescent

/-!
# The boundedness step of Stacks 08HE (2) ⇒ (1), with no proviso, on the small étale site

`AlgebraicGeometry.RingedSite.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom` puts an
`m`-pseudo-coherent complex of `O`-modules in `D⁻(O)` provided the covering presieve witnessing
pseudo-coherence at some object has a **finite** subfamily still covering the final object of the
site.  On the small étale site of an affine — indeed of any quasi-compact — scheme that proviso is
a theorem, `AlgebraicGeometry.SmallEtale.exists_finite_subfamily_coversTop`, so the boundedness
step holds there **with no hypothesis beyond `m`-pseudo-coherence**.

This is the composition, and it is where the proviso stops being carried.

## What had to be generalized to state it

Two things, both in
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/BoundedAboveDescent.lean`.

* `exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom` was stated at `RingedSite.{u, u, u}`.  The
  small étale ringed site is `RingedSite.{u + 1, u, u}` — objects in `Type (u + 1)`, morphisms and
  sections in `Type u` — so the theorem did not apply to it at all, and the proviso could not have
  been discharged there however it was proved.  The site universes are now free there; the module
  universe still has to equal the universe of the ring's sections, because
  `Stacks.SheafOfModules.isZero_of_coversTop` is stated that way, and on the small étale site both
  are `u`, so nothing is lost.
* The derived category was the *standard* localization model, declared as a local instance.  That
  model appears in the statement, so it cannot be exchanged for another afterwards, and
  elaborating it at the small étale site does not terminate within the heartbeat budget.  It is
  now a `HasDerivedCategory` hypothesis, which is also the form the obligation file of Stacks
  08HE carries.

A spelling note on top of that: the sheaf of rings is written `structureSheaf B S hS` and not
`(smallEtaleRingedSite B S hS).ringSheaf`, although the two are equal by `rfl`.  Only the first
spelling finds the `CategoryTheory.Abelian` instance that `HasDerivedCategory` needs —
`AlgebraicGeometry.RingedSite.ringSheaf` is a `def` and does not reduce at instance
transparency.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom`: **the
  boundedness step on the small étale site of a quasi-compact scheme**, unconditionally.
* `AlgebraicGeometry.SmallEtale.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom_of_isAffine`: the
  same for an affine scheme, which is the case the locality reduction of the induction delivers.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **The boundedness step of Stacks 08HE (2) ⇒ (1), on the small étale site of a quasi-compact
scheme, with no proviso.**  An `m`-pseudo-coherent complex of modules on the small étale site of
`S` lies in `D⁻`.

The finite-refinement hypothesis of
`AlgebraicGeometry.RingedSite.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom` is discharged at
the final object by `AlgebraicGeometry.SmallEtale.exists_finite_subfamily_coversTop`: the members
of a covering presieve of the small étale site have open images and are jointly surjective, so
over a quasi-compact space finitely many of them already cover. -/
theorem exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom
    (hqc : CompactSpace ((toScheme B S hS).obj (final B S hS)))
    (E : CochainComplex
      (SheafOfModules.{u} (structureSheaf B S hS)) ℤ) (k : ℤ)
    (hE : (smallEtaleRingedSite B S hS).IsPseudoCoherentComplexFrom E k) :
    ∃ b : ℤ, (DerivedCategory.Q.obj E).IsLE b :=
  (smallEtaleRingedSite B S hS).exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom E k hE
    (final B S hS) fun P hP => exists_finite_subfamily_coversTop B S hS hqc P hP

/-- **The boundedness step on the small étale site of an affine scheme**, which is the case the
locality reduction of the induction of Stacks 08HE (2) ⇒ (1) delivers. -/
theorem exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom_of_isAffine
    [_root_.AlgebraicGeometry.IsAffine S]
    (E : CochainComplex
      (SheafOfModules.{u} (structureSheaf B S hS)) ℤ) (k : ℤ)
    (hE : (smallEtaleRingedSite B S hS).IsPseudoCoherentComplexFrom E k) :
    ∃ b : ℤ, (DerivedCategory.Q.obj E).IsLE b :=
  exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom B S hS
    (show CompactSpace ((toScheme B S hS).obj (final B S hS)) from
      inferInstanceAs (CompactSpace S)) E k hE

end AlgebraicGeometry.SmallEtale

end
