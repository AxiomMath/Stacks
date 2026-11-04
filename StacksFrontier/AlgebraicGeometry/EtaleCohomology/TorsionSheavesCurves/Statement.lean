module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The eight assertions of Stacks Tag 03SC

Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k` of
dimension at most one, and `F` a torsion abelian sheaf on `X_étale`. Stacks Project Tag 03SC
asserts:

1. `H^q(X, F) = 0` for `q > 2`;
2. `H^q(X, F) = 0` for `q > 1` if `X` is affine;
3. `H^q(X, F) = 0` for `q > 1` if `p = char(k) > 0` and `F` is `p`-power torsion;
4. `H^q(X, F)` is finite if `F` is constructible and torsion prime to `char(k)`;
5. `H^q(X, F)` is finite if `X` is proper and `F` constructible;
6. `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is an isomorphism for every extension `k'/k` of
   algebraically closed fields if `F` is torsion prime to `char(k)`;
7. the same map is an isomorphism if `X` is proper;
8. `H^2(X, F) → H^2(U, F)` is surjective for every open `U ⊂ X`.

This file states the eight as the fields of `Stacks.EtaleCohomology.TorsionCurveAssertions`.

## Implementation notes

* Étale cohomology is Mathlib's `CategoryTheory.Sheaf.H` on `Scheme.smallEtaleTopology`, with
  coefficients `AddCommGrpCat.{u + 1}` for `X : Scheme.{u}`, the universe of the sets of sections
  of a sheaf on that site, and `Ext` groups in that same universe.
* Constructibility is `Stacks.EtaleCohomology.IsConstructibleSmallEtaleSheaf`, Tag 03RW read on the
  small étale site of Tag 021B.
* "Torsion prime to `char(k)`" is `Stacks.Torsion.IsPrimeToCharacteristicTorsion` at the
  exponential characteristic `ringExpChar k`, which in characteristic zero imposes nothing beyond
  torsion.
* `X_{k'}` is the fibre product of `X ⟶ Spec k` with `Spec k' ⟶ Spec k`, and the comparison maps
  of (6), (7) and (8) are `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` along the
  projection `X_{k'} ⟶ X` and along the inclusion of `U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **The eight assertions of Stacks Tag 03SC** for an abelian sheaf `F` on the small étale site
of a scheme `X` over a field `k`, with structure morphism `f`. -/
structure TorsionCurveAssertions {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop where
  /-- (1) `H^q(X, F) = 0` for `q > 2`. -/
  vanishing : ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{u + 1} F q)
  /-- (2) `H^q(X, F) = 0` for `q > 1` if `X` is affine. -/
  vanishing_of_isAffine : IsAffine X → ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{u + 1} F q)
  /-- (3) `H^q(X, F) = 0` for `q > 1` if `p = char(k) > 0` and `F` is `p`-power torsion. -/
  vanishing_of_isPrimePowerTorsion : ∀ p : ℕ, CharP k p → 0 < p →
    Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p F →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{u + 1} F q)
  /-- (4) `H^q(X, F)` is finite if `F` is constructible and torsion prime to `char(k)`. -/
  finite_of_isPrimeToCharacteristicTorsion : IsConstructibleSmallEtaleSheaf F →
    Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      ∀ q : ℕ, Finite (Sheaf.H.{u + 1} F q)
  /-- (5) `H^q(X, F)` is finite if `X` is proper and `F` constructible. -/
  finite_of_isProper : IsProper f → IsConstructibleSmallEtaleSheaf F →
    ∀ q : ℕ, Finite (Sheaf.H.{u + 1} F q)
  /-- (6) `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is bijective for every extension `k'/k` of
  algebraically closed fields if `F` is torsion prime to `char(k)`. -/
  bijective_of_isPrimeToCharacteristicTorsion :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
        [HasExt.{u + 1}
          (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
        (q : ℕ),
        Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
          (scalarExtensionFst k k' f) F q)
  /-- (7) `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is bijective for every extension `k'/k` of
  algebraically closed fields if `X` is proper. -/
  bijective_of_isProper : IsProper f →
    ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{u + 1}
        (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
      (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' f) F q)
  /-- (8) `H^2(X, F) → H^2(U, F|_U)` is surjective for every open `U ⊂ X`. -/
  surjective_restriction : ∀ (U : X.Opens)
    [HasExt.{u + 1} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1})],
    Function.Surjective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} U.ι F 2)

end Stacks.EtaleCohomology

end
