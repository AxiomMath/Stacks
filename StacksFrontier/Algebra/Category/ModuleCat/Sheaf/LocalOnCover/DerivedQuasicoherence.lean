module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-!
# Quasi-coherent cohomology is local on a covering family

Let `R` be a sheaf of rings on a site `C` and let `E` be an object of the derived category
`D(R)` of sheaves of `R`-modules.  If `V : I → C` is a family covering the final object and the
restriction of `E` to the slice at each `V i` lies in `D_QCoh(R.over (V i))`, then `E` lies in
`D_QCoh(R)`.

## Main results

* `Stacks.SheafOfModules.derivedCategoryB_isQuasicoherentOnSite_of_coversTop`: membership in
  `D_QCoh` is implied by membership of the restrictions to the members of a covering family.
* `Stacks.SheafOfModules.derivedCategoryB_isQuasicoherentOnSite_overFunctor`: membership in
  `D_QCoh` is inherited by the restriction to the slice at any object.
* `Stacks.SheafOfModules.derivedCategoryB_isQuasicoherentOnSite_iff_coversTop`: the two-sided
  form, for a covering family all of whose restrictions are tested.

## Implementation notes

`D_QCoh(R)` is `DerivedCategoryB.derivedCategoryB` applied to
`SheafOfModules.isQuasicoherentOnSite`, so membership unfolds to quasi-coherence of every
cohomology sheaf and no new predicate appears.

The universe of the module sections is the universe of the coefficient rings, and the index type
of the covering family lies in the universe of the objects of the site, as in the module-level
statement `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe t₁ t₂ u v w

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} {I : Type u} (V : I → C)
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ i, HasSheafify (J.over (V i)) AddCommGrpCat.{w}]
  [∀ i, (J.over (V i)).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{t₁} (_root_.SheafOfModules.{w} R)]
  [∀ i, HasDerivedCategory.{t₂} (_root_.SheafOfModules.{w} (R.over (V i)))]

/-- The restriction to the slice at `V i` of the `n`-th cohomology sheaf of `E` is
quasi-coherent as soon as the `n`-th cohomology sheaf of the restriction of `E` is. -/
theorem isQuasicoherentOnSite_over_homologyFunctor_obj
    (E : DerivedCategory (_root_.SheafOfModules.{w} R)) (n : ℤ) (i : I)
    (h : ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{w} (R.over (V i))) n).obj
      ((_root_.SheafOfModules.overFunctor.{w} R (V i)).mapDerivedCategory.obj
        E)).IsQuasicoherentOnSite) :
    (((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{w} R) n).obj E).over
      (V i)).IsQuasicoherentOnSite :=
  _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Functor.mapDerivedCategoryHomologyIso
      (_root_.SheafOfModules.overFunctor.{w} R (V i)) n).app E) h

/-- **Quasi-coherent cohomology is local on a covering family.**  If the restriction of
`E : D(R)` to the slice at each member of a family covering the final object has quasi-coherent
cohomology, then so does `E`. -/
theorem derivedCategoryB_isQuasicoherentOnSite_of_coversTop (hV : J.CoversTop V)
    (E : DerivedCategory (_root_.SheafOfModules.{w} R))
    (h : ∀ i, DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherentOnSite (R.over (V i)))
      ((_root_.SheafOfModules.overFunctor.{w} R (V i)).mapDerivedCategory.obj E)) :
    DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherentOnSite R) E :=
  fun n => (isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite
    ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{w} R) n).obj E)).mpr
      ⟨I, V, hV, fun i => isQuasicoherentOnSite_over_homologyFunctor_obj V E n i (h i n)⟩

/-- **Quasi-coherent cohomology is inherited by every restriction to a slice.** If `E : D(R)` has
quasi-coherent cohomology, then so does its restriction to the slice at `V i`. -/
theorem derivedCategoryB_isQuasicoherentOnSite_overFunctor (i : I)
    (E : DerivedCategory (_root_.SheafOfModules.{w} R))
    (h : DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherentOnSite R) E) :
    DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherentOnSite (R.over (V i)))
      ((_root_.SheafOfModules.overFunctor.{w} R (V i)).mapDerivedCategory.obj E) := fun n =>
  _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Functor.mapDerivedCategoryHomologyIso
      (_root_.SheafOfModules.overFunctor.{w} R (V i)) n).app E).symm
    (isQuasicoherent_over _ (h n) (V i))

/-- **Membership in `D_QCoh(R)` is tested on any covering family.**  An object of `D(R)` has
quasi-coherent cohomology if and only if its restriction to the slice at each member of a family
covering the final object does. -/
theorem derivedCategoryB_isQuasicoherentOnSite_iff_coversTop (hV : J.CoversTop V)
    (E : DerivedCategory (_root_.SheafOfModules.{w} R)) :
    DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherentOnSite R) E ↔
      ∀ i, DerivedCategoryB.derivedCategoryB
        (_root_.SheafOfModules.isQuasicoherentOnSite (R.over (V i)))
        ((_root_.SheafOfModules.overFunctor.{w} R (V i)).mapDerivedCategory.obj E) :=
  ⟨fun h i => derivedCategoryB_isQuasicoherentOnSite_overFunctor V i E h,
    derivedCategoryB_isQuasicoherentOnSite_of_coversTop V hV E⟩

end Stacks.SheafOfModules

end
