module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasisDegreeOne

/-!
# The long exact sequence of sheaf cohomology on a ringed space

Stacks 01FF compares the cohomology of a filtered colimit of `O_X`-modules over a quasi-compact
open with the colimit of the cohomologies.  Its proof is an induction on the degree whose
inductive step is the long exact cohomology sequence attached to a short exact sequence of
`O_X`-modules.  Mathlib has no long exact sequence for `CategoryTheory.Functor.rightDerived`, so
that sequence is not available for `Hfunctor` directly; this file supplies it.

The route is corepresentability.  Sections over an open `U` of an *abelian* sheaf are
corepresented by the sheafification of the free abelian presheaf on `yoneda.obj U`
(`ModuleSheafCohomology.evaluationRepresentation`), and morphisms out of the sheafified
extension of scalars of an abelian presheaf are the morphisms out of its sheafification into the
underlying abelian sheaf (`ModuleSheafCohomology.tensorSheafHomIso`).  Composing the two
corepresents `secF R U` on `SheafOfModules R` itself, and
`ModuleSheafCohomology.selfDerivedDeltaFunctor` then transports the `δ`-functor structure of
`Ext` onto the family `fun n => Hfunctor R U n`.  The transported `δ`-functor is universal
(Stacks 010S), because `Ext` out of any object vanishes in positive degree against an injective.

## Main definitions

* `Stacks.Cohomology.ModuleDelta.sectionsCorepresentation`: the corepresentation of `secF R U`
  by the sheafified extension of scalars of the free abelian presheaf on `yoneda.obj U`.
* `Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor`: the `δ`-functor whose degree-`n`
  component is literally `Hfunctor R U n`.

## Main results

* `Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor_functor`: the components are the
  cohomology functors, by definitional equality.
* `Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor_isUniversal`: that `δ`-functor is
  universal, so a morphism out of it is determined by its degree-zero component.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 010S](https://stacks.math.columbia.edu/tag/010S)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ModuleSheafCohomology

universe u

namespace Stacks.Cohomology.ModuleDelta

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (U : Opens X)

/-- The `O_X`-module corepresenting sections over `U`: the sheafification of the extension of
scalars along `O_X` of the free abelian presheaf on `yoneda.obj U`. -/
def sectionsCorepresenting : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (tensorPresheaf R.obj (yoneda.obj U ⋙ AddCommGrpCat.free))

/-- **Sections over `U` of an `O_X`-module are corepresented.**  Composing the corepresentation
of sections of abelian sheaves by the sheafified free abelian presheaf on `yoneda.obj U` with the
identification of morphisms out of a sheafified extension of scalars gives a corepresentation of
`secF R U` inside `SheafOfModules R`. -/
def sectionsCorepresentation :
    secF R U ≅ preadditiveCoyoneda.obj (op (sectionsCorepresenting R U)) :=
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
      (evaluationRepresentation (Opens.grothendieckTopology X) U) ≪≫
    (tensorSheafHomIso _ R (yoneda.obj U ⋙ AddCommGrpCat.free)).symm

/-- **The long exact cohomology sequence over an open of a ringed space.**  The `δ`-functor on
`SheafOfModules R` whose degree-`n` component is the cohomology functor `H^n(U, -)`, obtained by
transporting the `δ`-functor structure of `Ext` along `sectionsCorepresentation`.  Its `δ` is the
connecting map, and `DeltaFunctor.scδ₁_exact`/`scδ₂_exact` are the exactness of the resulting
long sequence. -/
def cohomologyDeltaFunctor : DeltaFunctor (SheafOfModules.{u} R) AddCommGrpCat.{u} :=
  selfDerivedDeltaFunctor (secF R U) _ (sectionsCorepresentation R U)

/-- The components of `cohomologyDeltaFunctor` are the cohomology functors `H^n(U, -)`. -/
theorem cohomologyDeltaFunctor_functor (n : ℕ) :
    (cohomologyDeltaFunctor R U).functor n = Hfunctor R U n :=
  rfl

/-- **`cohomologyDeltaFunctor` is universal** (Stacks 010S): `Ext` out of any object vanishes in
positive degree against an injective object, so the transported `δ`-functor is universal and a
morphism out of it is determined by its degree-zero component. -/
instance cohomologyDeltaFunctor_isUniversal : (cohomologyDeltaFunctor R U).IsUniversal :=
  selfDerivedDeltaFunctor_isUniversal _ _ (sectionsCorepresentation R U)

end Stacks.Cohomology.ModuleDelta

end
