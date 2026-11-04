module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects

/-!
# One covering family carrying the strictly perfect approximations of a pseudo-coherent complex

Let `(C, O)` be a ringed site, let `E` be a complex of `O`-modules and fix `m : ℤ`. Being
`m`-pseudo-coherent, as Stacks 08FT (1) states it, is a condition on *every* object `U` of `C`:
`U` admits a covering over each member of which `E` is approximated in degrees `≥ m` by a
strictly perfect complex. This file repackages that into a single family of objects covering the
final object of the site which carries all the approximations at once, which is the form a
statement checked locally consumes.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coversTop_isStrictlyPerfect_of_isPseudoCoherentComplexFrom`:
  the per-object local condition produces one family of objects covering the final object, with
  the strictly perfect approximation on each member.

## Implementation notes

The family is indexed by the triples consisting of an object `U`, an object `V` and an arrow
`V ⟶ U` in the chosen covering presieve of `U`, and its value there is the source of the arrow.
That family covers the final object for a direct reason: the chosen presieve of an object already
consists of arrows whose sources are members of the family, so the sieve it generates is contained
in the sieve of arrows factoring through a member; no pullback of sieves and no refinement is
needed. This is the argument of
`AlgebraicGeometry.RingedSite.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex`, which says
the same for perfectness; the two local conditions differ in what is demanded of the
approximation, and that datum is carried through untouched.

The universes of the sections of the structure sheaf and of the sections of the modules are
independent parameters and both stay free, as they do for
`AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` itself.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{m}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **The approximations of an `m`-pseudo-coherent complex are carried by one covering family.**
If `E` is `m`-pseudo-coherent then there is a family `V : κ → C` of objects covering the final
object of the site such that over each `V k` there are a strictly perfect complex `P` of
`O|_{V k}`-modules and a map `P ⟶ E|_{V k}` which is an isomorphism on cohomology in every degree
above `m` and an epimorphism on cohomology in degree `m`. -/
public theorem exists_coversTop_isStrictlyPerfect_of_isPseudoCoherentComplexFrom
    (E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (hE : X.IsPseudoCoherentComplexFrom E m) :
    ∃ (κ : Type (max u v)) (V : κ → X.C), X.J.CoversTop V ∧
      ∀ k, ∃ P : CochainComplex
          (SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V k))) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V k)) P ∧
          ∃ α : P ⟶ X.restrictComplex E (V k),
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
              Epi (HomologicalComplex.homologyMap α m) := by
  classical
  choose S hS hP using hE
  refine ⟨Σ U : X.C, Σ V : X.C, { f : V ⟶ U // S U f }, fun k => k.2.1, ?_, ?_⟩
  · intro W
    refine X.J.superset_covering ?_ (hS W)
    rintro Z g ⟨V, c, f, hf, rfl⟩
    exact ⟨⟨W, V, f, hf⟩, ⟨c⟩⟩
  · intro k
    exact hP k.1 k.2.2.1 k.2.2.2

end AlgebraicGeometry.RingedSite

end
