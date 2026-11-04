module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Restriction of scalars neither creates nor destroys a vanishing cohomology sheaf

Let `α : R ⟶ R'` be a map of sheaves of rings on a site `(C, J)`. Restriction of scalars
`Mod(R') ⥤ Mod(R)` is exact and faithful: it changes neither the underlying sheaf of abelian
groups of a module nor the underlying map of a morphism. So the functor it induces on the
unbounded derived categories commutes with cohomology, and a cohomology sheaf of an object of
`D(R')` vanishes exactly when the corresponding cohomology sheaf of its restriction to `R` does.

## Main results

* `Stacks.SheafOfModules.ChangeOfRings.isZero_of_isZero_restrictScalars`: restriction of
  scalars reflects the zero object.
* `Stacks.SheafOfModules.ChangeOfRings.isZero_homology_mapDerivedCategory_restrictScalars_iff`:
  **the vanishing of a cohomology sheaf is the same question over `R` and over `R'`.**

## Implementation notes

The results are stated for a map of sheaves of not necessarily commutative rings, which is the
generality in which `SheafOfModules.restrictScalars` and its exactness are available.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d v u

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Restriction of scalars reflects the zero object.** If the restriction to `R` of a sheaf of
`R'`-modules is zero then the module itself is zero. -/
theorem isZero_of_isZero_restrictScalars {M : _root_.SheafOfModules.{u} R'}
    (h : IsZero ((_root_.SheafOfModules.restrictScalars.{u} α).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  refine (_root_.SheafOfModules.restrictScalars.{u} α).map_injective ?_
  exact ((_root_.SheafOfModules.restrictScalars.{u} α).map_id M).trans
    (h.trans ((_root_.SheafOfModules.restrictScalars.{u} α).map_zero M M).symm)

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Restriction of scalars preserves and reflects the zero object. -/
theorem isZero_restrictScalars_iff (M : _root_.SheafOfModules.{u} R') :
    IsZero ((_root_.SheafOfModules.restrictScalars.{u} α).obj M) ↔ IsZero M :=
  ⟨isZero_of_isZero_restrictScalars α,
    (_root_.SheafOfModules.restrictScalars.{u} α).map_isZero⟩

section Derived

variable [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} R)]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} R')]

/-- **The vanishing of a cohomology sheaf is the same question over `R` and over `R'`.** For an
object `X` of `D(R')`, the `i`-th cohomology sheaf of the restriction of `X` to `R` vanishes
exactly when that of `X` does. -/
theorem isZero_homology_mapDerivedCategory_restrictScalars_iff
    (X : DerivedCategory (_root_.SheafOfModules.{u} R')) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} R) i).obj
        ((_root_.SheafOfModules.restrictScalars.{u} α).mapDerivedCategory.obj X)) ↔
      IsZero ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} R') i).obj X) :=
  Iff.trans
    (((_root_.SheafOfModules.restrictScalars.{u} α).mapDerivedCategoryHomologyIso i).app
      X).isZero_iff
    (isZero_restrictScalars_iff α _)

end Derived

end Stacks.SheafOfModules.ChangeOfRings

end
