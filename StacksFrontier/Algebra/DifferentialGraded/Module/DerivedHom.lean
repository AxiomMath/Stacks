module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedFunctorCriterion
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomFunctor

/-!
# Derived Hom out of a differential graded bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. The internal Hom functor
`Hom_B(N, -) : K(B) ⥤ K(A)` of Tag 0FQQ, followed by localization of the target at the
quasi-isomorphisms of `A`-modules, is the functor whose *right* derived functor
`RHom(N, -) : D(B, d) ⥤ D(A, d)` is Tag 09LI. (The diagram of homotopy and derived categories
does not commute, which is why a derived functor is needed at all.)

This file fixes the data that such a derived functor consists of and constructs it from the one
input it needs: a supply of resolutions of differential graded `B`-modules by modules orthogonal
on the right to the acyclic ones. That input is Tag 09KU together with Tag 09KS.

**Not to be confused with `StacksDraft.DerivedHom.DerivedHomData`**
(`StacksFrontier/Homology/HomComplex/DerivedAdjunction.lean`), which is an unrelated object
carrying the same name: the derived tensor–Hom adjunction data of Tag 0A63 for the derived
category of modules over a commutative ring. There is no relationship between the two.

## Main definitions

* `DifferentialGradedModule.homToDerivedCategory`: the functor to be right derived, namely
  internal Hom on homotopy categories followed by localization of the target.
* `DifferentialGradedModule.DerivedHomData`: a right derived functor of that functor together
  with its canonical comparison map, recording both everywhere-definedness in the sense of
  Tag 05SV and the universal property that pins the functor down.

## Main results

* `DifferentialGradedModule.DerivedHomData.ofResolutions`: the data exists as soon as every
  differential graded `B`-module admits a quasi-isomorphism into a module whose class in `K(B)`
  is orthogonal on the right to the acyclic modules.

## Implementation notes

*Why two conditions.* `DerivedHomData` carries both `derivable` and `isRightDerived`, and they
are inequivalent. The first is the source's own notion (Tag 05SV, via Tag 05S9): the right
derived functor is *defined at* every object, meaning the ind-object `X/Qis(B) ⥤ D(A, d)` is
essentially constant. The second is Mathlib's `Functor.IsRightDerivedFunctor`, i.e. that the
functor together with its comparison is a left Kan extension along the localization — which is
what makes `RHom(N, -)` a functor on `D(B, d)` at all, something the essential-constancy
condition alone does not provide. Both are recorded so that a consumer may use either without
reproving it, and no bridge between them is claimed. They are supplied by
`DifferentialGradedModule.isRightDerivable_of_exists_quasiIso_rightOrthogonal` and
`hasRightDerivedFunctor_of_exists_quasiIso_rightOrthogonal`, each proved separately from the
same resolution hypothesis.

*Why the derived category is the plain localization.* `D(B, d)` is taken to be
`(DifferentialGradedModule.quasiIsomorphisms' B).Localization`, Mathlib's construction of the
localization, rather than a Verdier quotient; the two agree because the quasi-isomorphisms are
the multiplicative system attached to the acyclic objects
(`DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms'`), and nothing below needs the
identification.

*Universes.* The differential graded algebras and their modules are taken at main's
single-universe encoding `StacksDraft.Ch22.Sec4.Tag09JJ`, in which
`DifferentialGradedAlgebra : Type u → Type u` and a module over it again lies in `Type u`. The
Stacks source, and the statements above this one, are universe-polymorphic in the base ring, each
algebra and each module separately; folding those needs the encoding widened, which is not done
here. Nothing below depends on the universes being equal, so the widening is an addition of
universe parameters rather than a change of content.

## References

* [Stacks Project, Tag 09LI](https://stacks.math.columbia.edu/tag/09LI); the criterion it
  applies is [Tag 06XN](https://stacks.math.columbia.edu/tag/06XN), the resolutions are
  [Tag 09KU](https://stacks.math.columbia.edu/tag/09KU), their orthogonality is
  [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS), and the functor being derived is
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra R)
  (N : DifferentialGradedModule B) (L : BimoduleStructure A B N)

/-- The functor to be right derived: internal Hom out of `N` on homotopy categories, followed by
localization of the target at the quasi-isomorphisms of differential graded `A`-modules. -/
def homToDerivedCategory :
    HomotopyCategory B ⥤ (quasiIsomorphisms' A).Localization :=
  homHomotopyCategoryFunctor A B N L ⋙ (quasiIsomorphisms' A).Q

/-- A right derived functor of `DifferentialGradedModule.homToDerivedCategory`, together with
its canonical comparison map. The functor goes from the derived category of differential graded
`B`-modules to that of differential graded `A`-modules, and is `RHom(N, -)`.

The two conditions are inequivalent and both are recorded: `derivable` is the source's
everywhere-definedness of Tag 05SV, and `isRightDerived` is the universal property — being a
left Kan extension along the localization — that determines the functor. -/
structure DerivedHomData where
  /-- The derived functor `RHom(N, -) : D(B, d) ⥤ D(A, d)`. -/
  functor : (quasiIsomorphisms' B).Localization ⥤ (quasiIsomorphisms' A).Localization
  /-- The canonical comparison, from the functor being derived to the derived functor read on
  `K(B)` through the localization. -/
  comparison : homToDerivedCategory A B N L ⟶ (quasiIsomorphisms' B).Q ⋙ functor
  /-- The right derived functor is defined at every object of `K(B)`, in the sense of
  Tag 05SV. -/
  derivable : (homToDerivedCategory A B N L).IsRightDerivable (quasiIsomorphisms' B)
  /-- The comparison exhibits `functor` as the right derived functor: it is a left Kan extension
  of `homToDerivedCategory` along the localization at the quasi-isomorphisms of `B`-modules. -/
  isRightDerived : functor.IsRightDerivedFunctor comparison (quasiIsomorphisms' B)

namespace DerivedHomData

/-- **Stacks 09LI** from its input. The right derived functor of Hom out of `N` exists as soon
as every differential graded `B`-module admits a quasi-isomorphism into a module whose class in
`K(B)` is orthogonal on the right to the acyclic modules — which is Tag 09KU together with
Tag 09KS. -/
def ofResolutions
    (hres : ∀ M : DifferentialGradedModule B, ∃ (I : DifferentialGradedModule B) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex B).map f) ∧
        (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I)) :
    DerivedHomData A B N L :=
  haveI : (homToDerivedCategory A B N L).HasRightDerivedFunctor (quasiIsomorphisms' B) :=
    hasRightDerivedFunctor_of_exists_quasiIso_rightOrthogonal B _ hres
  { functor := (homToDerivedCategory A B N L).totalRightDerived
      (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
    comparison := (homToDerivedCategory A B N L).totalRightDerivedUnit
      (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
    derivable := isRightDerivable_of_exists_quasiIso_rightOrthogonal B _ hres
    isRightDerived := inferInstance }

end DerivedHomData

end DifferentialGradedModule

end
