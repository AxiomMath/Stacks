module

public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Cohomology does not change when the sheaf of rings is restricted

Let `ψ : R ⟶ R'` be a morphism of sheaves of rings on a topological space `X` and let `F` be a
sheaf of `R'`-modules. Regarding `F` as a sheaf of `R`-modules along `ψ` changes neither its
underlying sheaf of abelian groups nor its sections, and it changes none of its cohomology
either: `Hⁿ(U, F)` computed in `Mod(R)` is `Hⁿ(U, F)` computed in `Mod(R')`.

The two abelian categories `Mod(R)` and `Mod(R')` are different, so this is not a formality
about one derived functor: the right derived functors of sections are taken in two different
categories. What makes the comparison work is Tag 03FD, which computes either of them from the
underlying sheaf of abelian groups alone —
`Stacks.Cohomology.ModuleComparison.underlyingSectionsIso` identifies `(secF R U).rightDerived n`
with `toSheaf R ⋙ Γ(U, -).rightDerived n`, and the sheaf of abelian groups underlying
`(restrictScalars ψ).obj F` is the one underlying `F`.

## Main definitions

* `Stacks.Cohomology.ModuleComparison.hgroupRestrictScalarsIso`: the comparison
  `Hⁿ(U, restrictScalars ψ F) ≅ Hⁿ(U, F)`.

## Main results

* `Stacks.Cohomology.ModuleComparison.restrictScalars_comp_secF`: restricting the scalars and
  then taking sections over `U` *is* taking sections over `U`; the two functors are equal.
* `Stacks.Cohomology.ModuleComparison.isZero_hgroup_restrictScalars_iff`: the two cohomology
  groups vanish together. This is the form in which a vanishing theorem proved for one sheaf of
  rings — Serre vanishing for `𝒪_X`-modules on an affine scheme, say — is consumed by a
  statement about modules over another, such as the terms of a relative de Rham complex, which
  are modules over the inverse image of the structure sheaf of the base.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ModuleComparison

variable {X : Type u} [TopologicalSpace X]
  {R R' : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (ψ : R ⟶ R') (U : Opens X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)] [EnoughInjectives (SheafOfModules.{u} R')]

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (SheafOfModules R)] [EnoughInjectives (SheafOfModules R')] in
/-- **Restricting the scalars does not change the sections.** Reading a sheaf of `R'`-modules as
a sheaf of `R`-modules along `ψ` and then taking abelian-group-valued sections over `U` is taking
sections over `U`: the two functors are equal, not merely isomorphic, because restriction of
scalars leaves the underlying presheaf of abelian groups untouched. -/
theorem restrictScalars_comp_secF :
    SheafOfModules.restrictScalars.{u} ψ ⋙ secF R U = secF R' U :=
  rfl

/-- **Cohomology over `U` is unchanged by a restriction of the sheaf of rings.** For a sheaf of
`R'`-modules `F` the group `Hⁿ(U, F)` computed in `Mod(R)` after restricting scalars along
`ψ : R ⟶ R'` is the group computed in `Mod(R')`.

Both sides are the sections-over-`U` derived functor applied to the *same* sheaf of abelian
groups by Tag 03FD, in the shape `Stacks.Cohomology.ModuleComparison.underlyingSectionsIso`
records it; the comparison is the composite of one instance of that isomorphism with the inverse
of the other. -/
def hgroupRestrictScalarsIso (n : ℕ) (F : SheafOfModules.{u} R') :
    Hgroup R U n ((SheafOfModules.restrictScalars.{u} ψ).obj F) ≅ Hgroup R' U n F :=
  (underlyingSectionsIso R U n).app _ ≪≫ ((underlyingSectionsIso R' U n).app F).symm

/-- **The two cohomology groups vanish together.** This is the direction in which a vanishing
theorem stated for one sheaf of rings is consumed by a statement about another. -/
theorem isZero_hgroup_restrictScalars_iff (n : ℕ) (F : SheafOfModules.{u} R') :
    IsZero (Hgroup R U n ((SheafOfModules.restrictScalars.{u} ψ).obj F)) ↔
      IsZero (Hgroup R' U n F) :=
  ⟨fun h => h.of_iso (hgroupRestrictScalarsIso ψ U n F).symm,
    fun h => h.of_iso (hgroupRestrictScalarsIso ψ U n F)⟩

end Stacks.Cohomology.ModuleComparison

end
