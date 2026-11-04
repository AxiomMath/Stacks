module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.DerivedQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceInjectives

/-!
# Quasi-coherent cohomology on an algebraic space is local on a covering family

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `E` be
an object of `D(𝒪_F)`.  Then `E` lies in `D_QCoh(𝒪_F)` if and only if its restriction to the
slice at each member of a family covering the final object of the small étale site does.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_of_coversTop`: membership in
  `D_QCoh(𝒪_F)` follows from membership of the restrictions to the members of a covering family.
* `AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_iff_coversTop`: the two-sided
  form.

## Implementation notes

The content is the general site statement
`Stacks.SheafOfModules.derivedCategoryB_isQuasicoherentOnSite_iff_coversTop`, specialised to the
small étale ringed site of `F` with the module sections in the universe `u` of the schemes, which
is the universe at which the module-level clause of Stacks 03DN is unconditional.  This is the
form Stacks 08F2 does not provide: there the tests are over all charts, over one chart, or along
one surjective étale morphism, never over a covering family.

Of the instances the general statement consumes, only the standard derived category is supplied
locally.  Binary products of the small étale site are the fibre products of charts over `F` and
come from the imported instance
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasBinaryProducts`; sheafification of
`AddCommGrpCat.{u}`-valued presheaves on every slice of that site is the global instance
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over`.  Both were once restated here
as local instances, on the ground that instance search does not unfold
`AlgebraicGeometry.Space.smallEtaleRingedSite`; the imported forms are stated for the projection
already, so the restatements were duplicates and have been retired.

## References

* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)


/-- **Quasi-coherent cohomology is local on a covering family of the small étale site.**  If the
restriction of `E : D(𝒪_F)` to the slice at each member of a family covering the final object
has quasi-coherent cohomology, then `E` lies in `D_QCoh(𝒪_F)`. -/
theorem derivedCategoryB_isQuasicoherentOnSite_of_coversTop
    {I : Type (u + 1)} (V : I → (smallEtaleRingedSite B S hS F hF).C)
    (hV : (smallEtaleRingedSite B S hS F hF).J.CoversTop V)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (h : ∀ i, DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).over (V i)))
      ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          (V i)).mapDerivedCategory.obj E)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) E :=
  Stacks.SheafOfModules.derivedCategoryB_isQuasicoherentOnSite_of_coversTop V hV E h

/-- **Membership in `D_QCoh(𝒪_F)` is tested on any covering family of the small étale site.**
An object of `D(𝒪_F)` has quasi-coherent cohomology if and only if its restriction to the slice
at each member of a family covering the final object does. -/
theorem derivedCategoryB_isQuasicoherentOnSite_iff_coversTop
    {I : Type (u + 1)} (V : I → (smallEtaleRingedSite B S hS F hF).C)
    (hV : (smallEtaleRingedSite B S hS F hF).J.CoversTop V)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) E ↔
      ∀ i, DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite
          (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)).over (V i)))
        ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
            (V i)).mapDerivedCategory.obj E) :=
  Stacks.SheafOfModules.derivedCategoryB_isQuasicoherentOnSite_iff_coversTop V hV E

end AlgebraicGeometry.Space

end
