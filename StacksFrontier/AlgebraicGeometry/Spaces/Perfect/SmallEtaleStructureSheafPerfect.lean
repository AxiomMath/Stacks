module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart

/-!
# The structure sheaf of an algebraic space is a perfect object

Let `F` be an algebraic space over a scheme `S`.  Its small étale ringed site
`AlgebraicGeometry.Space.smallEtaleRingedSite` is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`:
the objects of the site live one universe above the sections of the structure sheaf.  The
structure sheaf placed in degree zero is a perfect object of `D(𝒪_F)` in the sense of
Stacks 08G5, by `AlgebraicGeometry.RingedSite.isPerfect_derivedStructureSheaf`, which is stated
for a ringed site with independent universes.

**Nothing here is a clause of a Stacks tag and nothing here is tagged.**  These are inhabitants
of the perfectness hypotheses of the tagged statements about an algebraic space — Stacks 08HK,
08HL, 08HM, 09RI, 0CRU, 0DNC and 0DNF all bind
`(AlgebraicGeometry.Space.smallEtaleRingedSite …).IsPerfect` — and not part of any assertion.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over_addCommGrpCat`: presheaves of
  abelian groups with sections in the universe of the schemes sheafify on every slice of the
  small étale ringed site of `F`.
* `AlgebraicGeometry.Space.isPerfect_derivedStructureSheaf`: the structure sheaf in degree zero
  is a perfect object of `D(𝒪_F)`.
* `AlgebraicGeometry.Space.not_isZero_derivedStructureSheaf`: it is not a zero object as soon as
  the structure sheaf is not a zero module.

## Implementation notes

The slice sheafification instance is the one-level form of
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over_over`, proved the same way: a
`change` to the spelling in terms of `AlgebraicGeometry.Space.SmallEtale.topology`, which
instance search does not reach through the projections of the ringed site, followed by instance
search.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Presheaves of abelian groups with sections in the universe of the schemes sheafify on every
slice of the small étale ringed site of the algebraic space `F`, in the `∀`-quantified form that
the sheaves-of-modules API consumes.

This is the one-level form of
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over_over`; the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite` are not unfolded by instance search, so the
instance of `AlgebraicGeometry.Space.SmallEtale` does not fire at a goal phrased in terms of the
ringed site. -/
instance smallEtaleRingedSite_hasSheafify_over_addCommGrpCat :
    ∀ V : (smallEtaleRingedSite B S hS F hF).C,
      HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V) AddCommGrpCat.{u} := by
  change ∀ V : SmallEtale B S hS F,
    HasSheafify ((SmallEtale.topology B S hS F).over V) AddCommGrpCat.{u}
  infer_instance

/-- **The structure sheaf of an algebraic space, in degree zero, is a perfect object of
`D(𝒪_F)`.**  It is represented by the complex `𝒪_F[0]`, which is strictly perfect, and strict
perfectness is inherited by every restriction to a slice of the small étale site. -/
theorem isPerfect_derivedStructureSheaf
    [HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))] :
    (smallEtaleRingedSite B S hS F hF).IsPerfect
      (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF)) :=
  RingedSite.isPerfect_derivedStructureSheaf _

/-- **That perfect object is not a zero object of `D(𝒪_F)`**, as soon as the structure sheaf is
not a zero module.  Its degree-zero cohomology is the structure sheaf. -/
theorem not_isZero_derivedStructureSheaf
    [HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))]
    (h : ¬ IsZero (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) :
    ¬ IsZero (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS F hF)) :=
  RingedSite.not_isZero_derivedStructureSheaf _ h

end AlgebraicGeometry.Space

end
