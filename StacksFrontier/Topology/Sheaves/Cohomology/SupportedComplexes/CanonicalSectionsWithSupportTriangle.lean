module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupportTriangle
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianSectionsWithSupport

/-!
# The triangle for sections with support, at the derived functors themselves

Let `Z` be a closed subset of a ringed space `X`, and let `U = X ∖ Z`.  This file constructs
the three derived functors

* `RΓ_Z(X, -)`, `canonicalDerivedSectionsWithSupport`,
* `RΓ(X, -)`, `canonicalDerivedGlobalSections`,
* `RΓ(U, -)`, `canonicalDerivedSectionsOnComplement`,

on the *unbounded* derived category `D(O_X)` with values in `D(O_X(X))`, and instantiates the
distinguished triangle of [Stacks, Tag 0G71] at them.  The statement that comes out is free of
parameters: no derived functor and no comparison transformation is quantified over.

## Main definitions

* `canonicalDerivedGlobalSections`, `canonicalDerivedSectionsWithSupport` and
  `canonicalDerivedSectionsOnComplement` are the three total right derived functors, with units
  `canonicalDerivedGlobalSectionsUnit`, `canonicalDerivedSectionsWithSupportUnit` and
  `canonicalDerivedSectionsOnComplementUnit`.
* `canonicalSupportInclusion` and `canonicalRestrictionToComplement` are the two canonical
  arrows `RΓ_Z(X, -) ⟶ RΓ(X, -) ⟶ RΓ(U, -)` at these functors.
* `canonicalSectionsWithSupportBoundary` is the connecting morphism
  `RΓ(U, -) ⟶ RΓ_Z(X, -)[1]`, a natural transformation, and
  `canonicalSectionsWithSupportTriangle` is the triangle at an object of `D(O_X)`.

## Main results

* `canonicalDerivedGlobalSections_isRightDerivedFunctor`,
  `canonicalDerivedSectionsWithSupport_isRightDerivedFunctor` and
  `canonicalDerivedSectionsOnComplement_isRightDerivedFunctor`: each of the three functors,
  together with its unit, is a right derived functor along the quasi-isomorphisms of the
  unbounded homotopy category.
* `canonicalSectionsWithSupportTriangle_distinguished`: the triangle
  `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` is distinguished for every `K`.

## Implementation notes

Existence of the three functors on the whole unbounded derived category is the content of
`hasRightDerivedFunctor_homotopyToDerived`: modules on a ringed space form a Grothendieck
abelian category, so every complex admits a quasi-isomorphism into a K-injective complex
([Stacks, Tag 079P]), and [Stacks, Tag 070K] turns that into a total right derived functor.
Each of the three is then `Functor.totalRightDerived` along `DerivedCategory.Qh`, so the
`IsRightDerivedFunctor` instances are the ones Mathlib already supplies for a total right
derived functor; they are restated here only because a `def` is not unfolded by instance
search.

The distinguishedness is `derivedSectionsWithSupportTriangle` from
`StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupportTriangle`,
which proves it for an arbitrary triple of right derived functors; the content added here is
that the triple exists, so the triangle is a theorem about named objects rather than about
hypothetical ones.

## References

* [Stacks Project, Tag 0G71](https://stacks.math.columbia.edu/tag/0G71)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.SectionsWithSupport

attribute [local instance] HasDerivedCategory.standard

section Existence

variable (X : RingedSpace.{u, u})

/-- Every additive functor from module sheaves on a ringed space to modules over the global
functions, extended degreewise to the homotopy category and followed by the localization to
the derived category, has a right derived functor on the whole unbounded derived category.
Modules on a ringed space are Grothendieck abelian, so K-injective resolutions exist
([Stacks, Tag 079P]) and the criterion of [Stacks, Tag 070K] applies. -/
public instance hasRightDerivedFunctor_homotopyToDerived
    (F : ModuleSheaves X ⥤ GlobalModules X) [F.Additive] :
    (homotopyToDerived X F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.hasRightDerivedFunctor_moduleSheaves
    X _

end Existence

/-! ### The three derived functors -/

section Functors

variable (X : RingedSpace.{u, u})

/-- `RΓ(X, -)`: the total right derived functor of global sections, on the unbounded derived
category `D(O_X)` with values in `D(O_X(X))`. -/
public noncomputable def canonicalDerivedGlobalSections :
    DerivedModuleSheaves X ⥤ DerivedGlobalModules X :=
  (homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))

/-- The unit of `RΓ(X, -)`: the comparison from the degreewise global sections of a complex
to the value of the derived functor. -/
public noncomputable def canonicalDerivedGlobalSectionsUnit :
    homotopyToDerived X (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
      DerivedCategory.Qh ⋙ canonicalDerivedGlobalSections X :=
  (homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))

/-- `RΓ(X, -)`, with its unit, is a right derived functor of global sections along the
quasi-isomorphisms of the unbounded homotopy category. -/
@[stacks 0G71 "RΓ(X, -) on the unbounded derived category D(O_X) exists: the middle term of
the triangle is a genuine right derived functor of global sections"]
public instance canonicalDerivedGlobalSections_isRightDerivedFunctor :
    (canonicalDerivedGlobalSections X).IsRightDerivedFunctor
      (canonicalDerivedGlobalSectionsUnit X)
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
  inferInstanceAs (((homotopyToDerived X
        (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))).totalRightDerived
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleSheaves X)
          (ComplexShape.up ℤ))).IsRightDerivedFunctor
    ((homotopyToDerived X
        (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))).totalRightDerivedUnit
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)))

variable (Z : Set X) (hZ : IsClosed Z)

/-- `RΓ_Z(X, -)`: the total right derived functor of sections with support in the closed
subset `Z`, on the unbounded derived category `D(O_X)`. -/
public noncomputable def canonicalDerivedSectionsWithSupport :
    DerivedModuleSheaves X ⥤ DerivedGlobalModules X :=
  (homotopyToDerived X (sectionsWithSupport X Z hZ)).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))

/-- The unit of `RΓ_Z(X, -)`. -/
public noncomputable def canonicalDerivedSectionsWithSupportUnit :
    homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶
      DerivedCategory.Qh ⋙ canonicalDerivedSectionsWithSupport X Z hZ :=
  (homotopyToDerived X (sectionsWithSupport X Z hZ)).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))

/-- `RΓ_Z(X, -)`, with its unit, is a right derived functor of sections with support along
the quasi-isomorphisms of the unbounded homotopy category. -/
@[stacks 0G71 "RΓ_Z(X, -) on the unbounded derived category D(O_X) exists: the first term of
the triangle is a genuine right derived functor of sections with support in Z"]
public instance canonicalDerivedSectionsWithSupport_isRightDerivedFunctor :
    (canonicalDerivedSectionsWithSupport X Z hZ).IsRightDerivedFunctor
      (canonicalDerivedSectionsWithSupportUnit X Z hZ)
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
  inferInstanceAs (((homotopyToDerived X (sectionsWithSupport X Z hZ)).totalRightDerived
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleSheaves X)
          (ComplexShape.up ℤ))).IsRightDerivedFunctor
    ((homotopyToDerived X (sectionsWithSupport X Z hZ)).totalRightDerivedUnit
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)))

/-- `RΓ(U, -)` for `U = X ∖ Z`: the total right derived functor of sections on the open
complement of `Z`, with their global scalar structure, on the unbounded derived category
`D(O_X)`. -/
public noncomputable def canonicalDerivedSectionsOnComplement :
    DerivedModuleSheaves X ⥤ DerivedGlobalModules X :=
  (homotopyToDerived X (sectionsOnComplement X Z hZ)).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))

/-- The unit of `RΓ(U, -)`. -/
public noncomputable def canonicalDerivedSectionsOnComplementUnit :
    homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶
      DerivedCategory.Qh ⋙ canonicalDerivedSectionsOnComplement X Z hZ :=
  (homotopyToDerived X (sectionsOnComplement X Z hZ)).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))

/-- `RΓ(U, -)`, with its unit, is a right derived functor of sections on the complement
along the quasi-isomorphisms of the unbounded homotopy category. -/
@[stacks 0G71 "RΓ(U, -) for U = X ∖ Z on the unbounded derived category D(O_X) exists: the
third term of the triangle is a genuine right derived functor of sections on the complement"]
public instance canonicalDerivedSectionsOnComplement_isRightDerivedFunctor :
    (canonicalDerivedSectionsOnComplement X Z hZ).IsRightDerivedFunctor
      (canonicalDerivedSectionsOnComplementUnit X Z hZ)
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
  inferInstanceAs (((homotopyToDerived X (sectionsOnComplement X Z hZ)).totalRightDerived
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleSheaves X)
          (ComplexShape.up ℤ))).IsRightDerivedFunctor
    ((homotopyToDerived X (sectionsOnComplement X Z hZ)).totalRightDerivedUnit
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)))

/-! ### The two canonical arrows, at these functors -/

/-- `RΓ_Z(X, -) ⟶ RΓ(X, -)`, the canonical map forgetting the support condition, at the
derived functors constructed above. -/
public noncomputable abbrev canonicalSupportInclusion :
    canonicalDerivedSectionsWithSupport X Z hZ ⟶ canonicalDerivedGlobalSections X :=
  derivedSupportInclusion X Z hZ (canonicalDerivedSectionsWithSupport X Z hZ)
    (canonicalDerivedGlobalSections X) (canonicalDerivedSectionsWithSupportUnit X Z hZ)
    (canonicalDerivedGlobalSectionsUnit X)

/-- `RΓ(X, -) ⟶ RΓ(U, -)`, the canonical restriction map, at the derived functors
constructed above. -/
public noncomputable abbrev canonicalRestrictionToComplement :
    canonicalDerivedGlobalSections X ⟶ canonicalDerivedSectionsOnComplement X Z hZ :=
  derivedRestrictionToComplement X Z hZ (canonicalDerivedGlobalSections X)
    (canonicalDerivedSectionsOnComplement X Z hZ) (canonicalDerivedGlobalSectionsUnit X)
    (canonicalDerivedSectionsOnComplementUnit X Z hZ)

/-! ### The triangle, free of parameters -/

/-- The triangle data of [Stacks, Tag 0G71] at the three derived functors constructed above:
the connecting morphism, and the distinguishedness of the resulting triangle at every object
of `D(O_X)`. -/
public noncomputable def canonicalSectionsWithSupportTriangleData :
    SectionsWithSupportTriangleData X (canonicalDerivedSectionsWithSupport X Z hZ)
      (canonicalDerivedGlobalSections X) (canonicalDerivedSectionsOnComplement X Z hZ)
      (canonicalSupportInclusion X Z hZ) (canonicalRestrictionToComplement X Z hZ) :=
  derivedSectionsWithSupportTriangle X Z hZ (canonicalDerivedSectionsWithSupport X Z hZ)
    (canonicalDerivedGlobalSections X) (canonicalDerivedSectionsOnComplement X Z hZ)
    (canonicalDerivedSectionsWithSupportUnit X Z hZ) (canonicalDerivedGlobalSectionsUnit X)
    (canonicalDerivedSectionsOnComplementUnit X Z hZ)

/-- The connecting morphism `RΓ(U, -) ⟶ RΓ_Z(X, -)[1]` of [Stacks, Tag 0G71], at the derived
functors constructed above.  It is a natural transformation, which is the functoriality in
`K` that the source asserts. -/
public noncomputable abbrev canonicalSectionsWithSupportBoundary :
    canonicalDerivedSectionsOnComplement X Z hZ ⟶
      canonicalDerivedSectionsWithSupport X Z hZ ⋙
        shiftFunctor (DerivedGlobalModules X) (1 : ℤ) :=
  (canonicalSectionsWithSupportTriangleData X Z hZ).boundary

/-- The triangle `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` of [Stacks, Tag 0G71],
evaluated at an object `K` of `D(O_X)`. -/
public noncomputable def canonicalSectionsWithSupportTriangle (K : DerivedModuleSheaves X) :
    Triangle (DerivedGlobalModules X) :=
  Triangle.mk ((canonicalSupportInclusion X Z hZ).app K)
    ((canonicalRestrictionToComplement X Z hZ).app K)
    ((canonicalSectionsWithSupportBoundary X Z hZ).app K)

/-- **Stacks, Tag 0G71.**  Let `Z` be a closed subset of a ringed space `X` and let
`U = X ∖ Z`.  The triangle
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`
is distinguished in `D(O_X(X))`, functorially in `K` in `D(O_X)`.  The three functors are
the total right derived functors constructed above, the two forward arrows are the canonical
ones, and the connecting morphism is a natural transformation independent of `K`; nothing is
quantified over. -/
@[stacks 0G71 "the distinguished triangle RΓ_Z(X,K) → RΓ(X,K) → RΓ(U,K) → RΓ_Z(X,K)[1] in
D(O_X(X)), at the three constructed derived functors, functorial for K in D(O_X)"]
public theorem canonicalSectionsWithSupportTriangle_distinguished
    (K : DerivedModuleSheaves X) :
    canonicalSectionsWithSupportTriangle X Z hZ K ∈ distTriang (DerivedGlobalModules X) :=
  (canonicalSectionsWithSupportTriangleData X Z hZ).distinguished K

end Functors

end Stacks.Cohomology.SectionsWithSupport
