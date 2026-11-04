module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.TricomplexHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor

/-!
# The rows of a Cartan-Eilenberg resolution compute the right derived functors

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, with `𝒜` having enough
injectives, let `K^•` be a bounded below cochain complex of `𝒜` and let `I^{•,•}` be a
Cartan-Eilenberg resolution of `K^•`.  Write `L^{•,•} = F(I^{•,•})`.  Then the complex of the
homologies of the rows of `L^{•,•}`,

`H^q_{II}(L^{•,•}) : p ↦ H^q(L^{p,•})`,

is the complex `p ↦ R^q F(K^p)` of right derived functors, with the differential induced by
that of `K^•`.

`CochainComplex.CartanEilenbergResolution.exists_homologyIso_rightDerivedPlus` already supplies
the components of this isomorphism and the square they make with the differentials; what is
added here is that these assemble into an isomorphism *of complexes*, which is the form the
first page of the spectral sequence of [Stacks, Tag 08BN] is stated in -- see
`Stacks.Cech.cechCartanEilenbergBicomplexHomologyIso`, whose target is
`Tot(Č^•(U, H^q_{II}(L^{•,•})))`.

This is a step in the proof of the second clause of [Stacks, Tag 08BN] and states no clause of
that tag, so it carries no tag attribute.

## Main results

* `CochainComplex.CartanEilenbergResolution.nonempty_rowHomologyIso_rightDerivedPlus`:
  `H^q_{II}(F(I^{•,•})) ≅ R^q F ∘ K^•` as complexes.

## Implementation notes

Assembling the components into a morphism of complexes needs the target to *be* a complex, that
is it needs `(F.rightDerivedPlus q).Additive`, and bare `inferInstance` does not find it.  It is
read off the definition `R^q F = H^q ∘ RF ∘ (·[0])` instead: the single functor and the degree-`q`
homology functor of `D⁺(ℬ)` are additive outright, and `RF` is additive because it is
triangulated ([Stacks, Tag 0159]) -- a fact the library keeps as the *local* instances
`commShiftRightDerivedFunctorPlus`, `natTransCommShiftRightDerivedFunctorPlusUnit` and
`isTriangulated_rightDerivedFunctorPlus`, which this file therefore switches on.

This route puts no constraint on the degree, so `q` ranges over all of `ℤ`, which is the range
[Stacks, Tag 08BN] states its second page over.  Obtaining the instance
instead from part (1) of [Stacks, Tag 05TE]
(`Stacks.Cohomology.CechDelta.rightDerivedPlus_deltaAxioms`) would restrict to `q : ℕ`, that
package being indexed by `ℕ` because `CategoryTheory.DeltaFunctor` is; that restriction is an
artefact of the route and not of the mathematics, the degree playing no part
in the derivation of additivity.  The rows in negative degrees are indeed zero, the resolution
being a resolution, but nothing here needs that: the components of
[Stacks, Tag 015J] are already supplied in every integer degree.

`HasDerivedCategory.standard` is still fixed, as the Čech development that consumes this works
at the standard derived category throughout.

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe v v' u u'

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]

attribute [local instance] HasDerivedCategory.standard

variable (F : A ⥤ B) [F.Additive] [EnoughInjectives A]

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

/-- **The right derived functors of an additive functor are additive, in every integer degree.**
`R^q F` is the composite of the single functor `𝒜 ⥤ D⁺(𝒜)`, the right derived functor
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` and the degree-`q` homology functor of `D⁺(ℬ)`.  The outer two are additive
for every `q`, and `RF` is additive because it is triangulated, [Stacks, Tag 0159]; so the
degree is irrelevant.  Named because instance search does not find it on its own. -/
instance additive_rightDerivedPlus (q : ℤ) : (F.rightDerivedPlus q).Additive := by
  change (DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor B q).Additive
  infer_instance

variable {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K)
  (I : K.CartanEilenbergResolution)

include hK in
/-- **The rows of `F` applied to a Cartan-Eilenberg resolution compute `R^q F`.**  The complex
`p ↦ H^q(F(I^{p,•}))` of the homologies of the rows is the complex `p ↦ R^q F(K^p)`, with the
differential induced by that of `K^•`.

The components and their commutation with the differentials are the first conjunct of
[Stacks, Tag 015J], `exists_homologyIso_rightDerivedPlus`; this packages them as an
isomorphism of complexes, which is the shape
`Stacks.Cech.cechCartanEilenbergBicomplexHomologyIso` consumes.  The degree `q` is an arbitrary
integer: [Stacks, Tag 015J] supplies the components in every degree. -/
theorem nonempty_rowHomologyIso_rightDerivedPlus
    [HomologicalComplex₂.HasTotal
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex) (ComplexShape.up ℤ)] (q : ℤ) :
    Nonempty (HomologicalComplex₃.rowHomology
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.bicomplex) q ≅
      ((F.rightDerivedPlus q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨e, he⟩ := (exists_homologyIso_rightDerivedPlus F hK I).1 q
  exact ⟨HomologicalComplex.Hom.isoOfComponents e fun p p' _ => (he p p').symm⟩

end CochainComplex.CartanEilenbergResolution

end
