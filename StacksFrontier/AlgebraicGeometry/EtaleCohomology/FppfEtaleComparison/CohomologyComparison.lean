module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.CohomologicalDescent
public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayPullbackComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Étale cohomology is fppf cohomology of the inverse image

Let `B` be a big fppf site, `X` an object of it, and `a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)` the
composite `π_X ∘ ε_X`. Stacks 0DDU asserts:

1. `H^q(X_étale, F) = H^q_fppf(X, a_X^{-1}F)` for an abelian sheaf `F` on `X_étale`;
2. `H^q(X_étale, K) = H^q_fppf(X, a_X^{-1}K)` for `K` in `D⁺(X_étale)`;

and, as an example, `H^q_étale(X, A) = H^q_fppf(X, A)` for the constant sheaves of an abelian
group `A`.

Cohomology is that of the source: `RΓ` is the right derived functor on `D⁺` of Mathlib's global
sections functor `CategoryTheory.Sheaf.Γ`, `H^q(-, K)` is the degree `q` cohomology of `RΓ(K)`,
and `H^q(-, F)` is `R^qΓ(F)`, `CategoryTheory.Functor.rightDerivedPlus` (Stacks 015A), or Mathlib's
`CategoryTheory.Functor.rightDerived` in degree `q : ℕ`.

## Main definitions

* `AlgebraicGeometry.fppfSmallEtaleGlobalSectionsIso`: `Γ(X_étale, a_{X,*}G) = Γ_fppf(X, G)`,
  both being sections over the final object `X / X`.
* `AlgebraicGeometry.fppfSmallEtaleDerivedSectionsPullback`: the map
  `RΓ(X_étale, K) ⟶ RΓ_fppf(X, a_X^{-1}K)` on `D⁺(X_étale)`.
* `AlgebraicGeometry.fppfSmallEtaleHypercohomologyPullback`,
  `AlgebraicGeometry.fppfSmallEtaleCohomologyPullback` and
  `AlgebraicGeometry.fppfSmallEtaleCohomologyPullbackNat`: the maps of parts (2) and (1).
* `AlgebraicGeometry.fppfSmallEtaleConstantSheafIso`: `a_X^{-1}A = A` for constant sheaves.
* `AlgebraicGeometry.fppfSmallEtaleConstantCohomologyPullback`: the map of the example.

## Main results

* `AlgebraicGeometry.isIso_fppfSmallEtaleDerivedSectionsPullback_of_finite`:
  `RΓ(X_étale, K) = RΓ_fppf(X, a_X^{-1}K)`.
* `AlgebraicGeometry.isIso_fppfSmallEtaleHypercohomologyPullback_of_finite`: Stacks 0DDU (2).
* `AlgebraicGeometry.isIso_fppfSmallEtaleCohomologyPullback_of_finite` and
  `AlgebraicGeometry.isIso_fppfSmallEtaleCohomologyPullbackNat_of_finite`: Stacks 0DDU (1).
* `AlgebraicGeometry.isIso_fppfSmallEtaleConstantCohomologyPullback_of_finite`: the example.

## The proof

As in the source, from Stacks 0DDT by Stacks 08J6. The map `RΓ(X_étale, K) ⟶ RΓ_fppf(X, a_X^{-1}K)`
is `RΓ(X_étale, -)` of the map `K ⟶ Ra_{X,*}a_X^{-1}K` of Stacks 0DDT followed by the inverse of
the factorization `RΓ_fppf(X, -) = RΓ(X_étale, -) ∘ Ra_{X,*}` (Stacks 015M, valid because
`a_{X,*}` preserves injective objects, which is the content of Stacks 08J6 used here), that is
`Stacks.LerayPullbackComparison.lerayPullback` for `a_X^{-1} ⊣ a_{X,*}` and the identification
`Γ(X_étale, -) ∘ a_{X,*} = Γ_fppf(X, -)`. It is invertible wherever the map of Stacks 0DDT is,
`AlgebraicGeometry.isIso_fppfSmallEtaleAdjunctionDerivedUnit_of_finite`. Part (1) is part (2) at
`F` placed in degree zero, read through `a_X^{-1}(F[0]) = (a_X^{-1}F)[0]`. For the example,
`a_X^{-1}` carries the constant sheaf `A` on `X_étale` to the constant fppf sheaf `A`, both
being left adjoint to `Γ_fppf(X, -)`.

## Hypotheses

Stacks 0DDT is proved in this development from Situation 0EZ3 for the fppf and étale topologies,
built from the two facts `hex` and `hbc` about the direct image along a finite morphism of the big
étale sites (exactness, and `f_{big,*}π_X^{-1}F ∈ 𝒜'_Y`) that the proof of Stacks 0DDJ (4)
supplies. The results here take them as arguments in the shape of
`AlgebraicGeometry.isIso_fppfSmallEtaleAdjunctionDerivedUnit_of_finite`, and nothing else; so
the statement of Stacks 0DDU is not registered here. The maps themselves are defined with no
hypothesis.

The derived categories are arbitrary models: the statements carry `HasDerivedCategory`
instances for the two sheaf categories and for abelian groups.

## References

* [Stacks Project, Tag 0DDU](https://stacks.math.columbia.edu/tag/0DDU)
* [Stacks Project, Tag 0DDT](https://stacks.math.columbia.edu/tag/0DDT)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (X : B.Schemes)

/-- Global sections of abelian sheaves on `(Sch/X)_fppf` are additive: the functor is a right
adjoint, so it preserves binary products. -/
instance : (Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `a_{X,*}` preserves injective objects: it is right adjoint to the exact functor
`a_X^{-1}`. -/
instance : (fppfSmallEtaleAbelianPushforward B X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (fppfSmallEtaleAbelianAdjunction B X)

/-- **`Γ(X_étale, a_{X,*}G) = Γ_fppf(X, G)`** for an abelian sheaf `G` on `(Sch/X)_fppf`. Both
are the sections of `G` over the final object `X / X`: `Sheaf.Γ` is sections over a final object
(`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), the object `X / X` of the small étale site is
final (`AlgebraicGeometry.SmallEtale.finalIsTerminal`), and `a_{X,*}G` at it is `G` at `X / X`. -/
def fppfSmallEtaleGlobalSectionsIso :
    fppfSmallEtaleAbelianPushforward B X ⋙
        Sheaf.Γ (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _
      (SmallEtale.finalIsTerminal (associatedBigEtaleSite B) X.1 X.2)) ≪≫
    (Iso.refl _ : _ ≅ (sheafSections (B.topology.over X) AddCommGrpCat.{u + 1}).obj
      (Opposite.op (Over.mk (𝟙 X)))) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ Over.mkIdTerminal).symm

/-- **`a_X^{-1}A = A` for constant sheaves**: the inverse image of the constant sheaf of an
abelian group `A` on `X_étale` is the constant sheaf `A` on `(Sch/X)_fppf`. Both functors
`A ↦ a_X^{-1}A` and `A ↦ A` are left adjoint to `Γ_fppf(X, -)`, the first through
`Γ(X_étale, -) ∘ a_{X,*} = Γ_fppf(X, -)`. -/
def fppfSmallEtaleConstantSheafIso :
    constantSheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1} ⋙ fppfSmallEtaleAbelianPullback B X ≅
      constantSheaf (B.topology.over X) AddCommGrpCat.{u + 1} :=
  (((constantSheafΓAdj _ _).comp (fppfSmallEtaleAbelianAdjunction B X)).ofNatIsoRight
    (fppfSmallEtaleGlobalSectionsIso B X)).leftAdjointUniq (constantSheafΓAdj _ _)

section Derived

variable [HasDerivedCategory
    (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (B.topology.over X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]

/-- **The map `RΓ(X_étale, K) ⟶ RΓ_fppf(X, a_X^{-1}K)`** on `D⁺(X_étale)`: `RΓ(X_étale, -)` of the
map `K ⟶ Ra_{X,*}a_X^{-1}K` of Stacks 0DDT, followed by the inverse of the factorization
`RΓ_fppf(X, -) = RΓ(X_étale, -) ∘ Ra_{X,*}` (Stacks 015M, 08J6). -/
def fppfSmallEtaleDerivedSectionsPullback :
    (Sheaf.Γ (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⟶
      (fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  Stacks.LerayPullbackComparison.lerayPullback (fppfSmallEtaleAbelianAdjunction B X) _ _
    (fppfSmallEtaleGlobalSectionsIso B X)

/-- The map `H^q(X_étale, K) ⟶ H^q_fppf(X, a_X^{-1}K)` of Stacks 0DDU (2), for `K` in
`D⁺(X_étale)`: degree `q` cohomology of `RΓ(X_étale, K) ⟶ RΓ_fppf(X, a_X^{-1}K)`. -/
def fppfSmallEtaleHypercohomologyPullback (q : ℤ)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Sheaf.Γ (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj K) ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
          ((fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlus.obj K)) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).map
    ((fppfSmallEtaleDerivedSectionsPullback B X).app K)

/-- The map `H^q(X_étale, F) ⟶ H^q_fppf(X, a_X^{-1}F)` of Stacks 0DDU (1), for an abelian sheaf `F`
on `X_étale`, with `H^q = R^qΓ` (`CategoryTheory.Functor.rightDerivedPlus`, Stacks 015A): the map
of part (2) at `F[0]`, read through `a_X^{-1}(F[0]) = (a_X^{-1}F)[0]`. -/
def fppfSmallEtaleCohomologyPullback (q : ℤ)
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    ((Sheaf.Γ (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1}).rightDerivedPlus q).obj F ⟶
      ((Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerivedPlus q).obj
        ((fppfSmallEtaleAbelianPullback B X).obj F) :=
  fppfSmallEtaleHypercohomologyPullback B X q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).map
      ((Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlusObjSingleIso F).hom)

/-- The map `H^q(X_étale, F) ⟶ H^q_fppf(X, a_X^{-1}F)` of Stacks 0DDU (1) for Mathlib's right
derived functors `CategoryTheory.Functor.rightDerived` in degree `q : ℕ`: the map
`AlgebraicGeometry.fppfSmallEtaleCohomologyPullback` read through
`Stacks.DerivedIndexing.rightDerivedIso`. -/
def fppfSmallEtaleCohomologyPullbackNat (q : ℕ)
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    ((Sheaf.Γ (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1}).rightDerived q).obj F ⟶
      ((Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerived q).obj
        ((fppfSmallEtaleAbelianPullback B X).obj F) :=
  (Stacks.DerivedIndexing.rightDerivedIso _ q).hom.app F ≫
    fppfSmallEtaleCohomologyPullback B X q F ≫
    (Stacks.DerivedIndexing.rightDerivedIso _ q).inv.app _

/-- The map `H^q_étale(X, A) ⟶ H^q_fppf(X, A)` of the example of Stacks 0DDU, for an abelian group
`A` and its constant sheaves: the map of part (1) at the constant sheaf `A` on `X_étale`, followed
by `a_X^{-1}A = A`. -/
def fppfSmallEtaleConstantCohomologyPullback (q : ℤ) (A : AddCommGrpCat.{u + 1}) :
    ((Sheaf.Γ (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1}).rightDerivedPlus q).obj
        ((constantSheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
          AddCommGrpCat.{u + 1}).obj A) ⟶
      ((Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerivedPlus q).obj
        ((constantSheaf (B.topology.over X) AddCommGrpCat.{u + 1}).obj A) :=
  fppfSmallEtaleCohomologyPullback B X q _ ≫
    ((Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerivedPlus q).map
      ((fppfSmallEtaleConstantSheafIso B X).hom.app A)

variable {B X}
  (hex : ∀ ⦃X Y : B.Schemes⦄ (f : X ⟶ Y), fppfEtaleFinite B f →
    PreservesFiniteColimits ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y)))
  (hbc : ∀ ⦃X Y : B.Schemes⦄ (f : X ⟶ Y), fppfEtaleFinite B f → ∀ A, fppfEtaleWeakSerre B Y
    (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X)
      ((associatedBigEtaleSite B).topology.over Y)).obj ((fppfEtaleProjectionPullback B X).obj A)))

include hex hbc in
/-- **`RΓ(X_étale, K) = RΓ_fppf(X, a_X^{-1}K)`** for `K` in `D⁺(X_étale)`, given the two inputs of
Situation 0EZ3 for the fppf and étale topologies: the map is invertible because the map
`K ⟶ Ra_{X,*}a_X^{-1}K` of Stacks 0DDT is. -/
theorem isIso_fppfSmallEtaleDerivedSectionsPullback_of_finite :
    IsIso (fppfSmallEtaleDerivedSectionsPullback B X) := by
  have := isIso_fppfSmallEtaleAdjunctionDerivedUnit_of_finite (X := X) hex hbc
  have : ∀ K, IsIso ((fppfSmallEtaleDerivedSectionsPullback B X).app K) := fun K ↦
    have : IsIso ((Stacks.LerayPullbackComparison.derivedUnit
        (fppfSmallEtaleAbelianAdjunction B X)).app K) :=
      inferInstanceAs (IsIso ((fppfSmallEtaleAdjunctionDerivedUnit B X).app K))
    Stacks.LerayPullbackComparison.isIso_lerayPullback_app _ _ _ _ K
  exact NatIso.isIso_of_isIso_app _

include hex hbc in
/-- **Stacks 0DDU (2).** `H^q(X_étale, K) = H^q_fppf(X, a_X^{-1}K)` for `K` in `D⁺(X_étale)` and
every `q`, given the two inputs of Situation 0EZ3 for the fppf and étale topologies. -/
theorem isIso_fppfSmallEtaleHypercohomologyPullback_of_finite (q : ℤ)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})) :
    IsIso (fppfSmallEtaleHypercohomologyPullback B X q K) := by
  have := isIso_fppfSmallEtaleDerivedSectionsPullback_of_finite (X := X) hex hbc
  rw [fppfSmallEtaleHypercohomologyPullback]
  infer_instance

include hex hbc in
/-- **Stacks 0DDU (1).** `H^q(X_étale, F) = H^q_fppf(X, a_X^{-1}F)` for an abelian sheaf `F` on
`X_étale` and every `q`, with `H^q = R^qΓ` (`CategoryTheory.Functor.rightDerivedPlus`), given the
two inputs of Situation 0EZ3 for the fppf and étale topologies. -/
theorem isIso_fppfSmallEtaleCohomologyPullback_of_finite (q : ℤ)
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    IsIso (fppfSmallEtaleCohomologyPullback B X q F) := by
  have := isIso_fppfSmallEtaleHypercohomologyPullback_of_finite hex hbc q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  rw [fppfSmallEtaleCohomologyPullback]
  exact IsIso.comp_isIso' this
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
      ((Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.mapIso
        ((fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlusObjSingleIso F))).isIso_hom

include hex hbc in
/-- **Stacks 0DDU (1)** for Mathlib's right derived functors in degree `q : ℕ`:
`H^q(X_étale, F) = H^q_fppf(X, a_X^{-1}F)` for an abelian sheaf `F` on `X_étale`, given the two
inputs of Situation 0EZ3 for the fppf and étale topologies. -/
theorem isIso_fppfSmallEtaleCohomologyPullbackNat_of_finite (q : ℕ)
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    IsIso (fppfSmallEtaleCohomologyPullbackNat B X q F) := by
  have := isIso_fppfSmallEtaleCohomologyPullback_of_finite hex hbc q F
  rw [fppfSmallEtaleCohomologyPullbackNat]
  infer_instance

include hex hbc in
/-- **The example of Stacks 0DDU.** `H^q_étale(X, A) = H^q_fppf(X, A)` for an abelian group `A`
and its constant sheaves, given the two inputs of Situation 0EZ3 for the fppf and étale
topologies. -/
theorem isIso_fppfSmallEtaleConstantCohomologyPullback_of_finite (q : ℤ)
    (A : AddCommGrpCat.{u + 1}) :
    IsIso (fppfSmallEtaleConstantCohomologyPullback B X q A) := by
  have := isIso_fppfSmallEtaleCohomologyPullback_of_finite hex hbc q
    ((constantSheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      AddCommGrpCat.{u + 1}).obj A)
  rw [fppfSmallEtaleConstantCohomologyPullback]
  infer_instance

end Derived

end AlgebraicGeometry
