module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Basic

/-!
# The canonical comparison from the tensor algebra of the degree-one twist

Tag 01O4 pins the universal pair of its representation by requiring a homomorphism from the
pair's tensor algebra to the graded algebra of twists of Tag 01NR that is unital,
generator-compatible, an isomorphism in every nonnegative degree, and carries the pair's graded
map to the homogeneous-section map; that is the predicate `IsCanonicalTwistPair`, which
existentially quantifies over the homomorphism. By the universal property of the tensor algebra
there is exactly one unital homomorphism to the twist algebra extending a given identification of
the pair's invertible sheaf with the degree-one twist, so the homomorphism is forced and
canonicality reduces to two concrete conditions on the pair. The two clauses that become
automatic are the generator clause, by
`SheafOfModules.GradedAlgebra.IsTensorAlgebra.descAny_extends`, and the unit clause, by
`SheafOfModules.GradedAlgebra.UnitalHom.sectionsMap_one`.

## Main definitions

* `twistComparison`: the canonical unital homomorphism from the tensor algebra of the degree-one
  twist to the algebra of twists.
* `pairTwistComparison`: the same for a pair together with an identification of its invertible
  sheaf with the degree-one twist.
* `tensorGeneratorIso`: the degree-one generator of a tensor algebra, as an isomorphism.
* `TwistsAreTensorPowers`: the canonical comparison is an isomorphism in every nonnegative
  degree, i.e. the `n`-th twist is the `n`-th tensor power of the first.

## Main results

* `isCanonicalTwistPair_iff`: a pair is the canonical twist pair of `D` exactly when, for some
  identification `β` of its invertible sheaf with the degree-one twist, the canonical comparison
  is an isomorphism in every nonnegative degree and carries the pair's graded map to the
  homogeneous-section map of `D`.
* `pairTwistComparison_unique`: a unital homomorphism extending `β` on the degree-one generator
  is unique.
* `isIso_pairTwistComparison_app_one`: the comparison is an isomorphism in degree one, with no
  hypothesis on the graded algebra, so `TwistsAreTensorPowers` has content only in degree zero
  and in the degrees at least two. Under generation in degree one the latter follow from degree
  one by induction along multiplication by the degree-one generator
  (`twistsAreTensorPowers_iff_isIso_app_zero`), so the content is degree zero alone.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (TA : TensorAlgebras.{u})
  (D : TwistData A)

/-- The canonical unital homomorphism from the tensor algebra of the degree-one twist to the
graded algebra of twists. -/
public def twistComparison :
    SheafOfModules.GradedAlgebra.UnitalHom
      (TA (relativeProj A).scheme (D.algebra.piece 1)).tensor D.algebra :=
  (TA (relativeProj A).scheme (D.algebra.piece 1)).tensor_isTensorAlgebra.descAny D.algebra (𝟙 _)

/-- The canonical comparison is the identity on the degree-one generator. -/
public theorem twistComparison_extends :
    (TA (relativeProj A).scheme (D.algebra.piece 1)).tensorGenerator ≫
      (twistComparison TA D).app 1 = 𝟙 _ :=
  (TA (relativeProj A).scheme (D.algebra.piece 1)).tensor_isTensorAlgebra.descAny_extends
    D.algebra (𝟙 _)

/-- The canonical comparison carries the unit of the tensor algebra to the unit of the twist
algebra. -/
public theorem twistComparison_sectionsMap_one :
    SheafOfModules.sectionsMap ((twistComparison TA D).app 0)
      (TA (relativeProj A).scheme (D.algebra.piece 1)).tensor.one = D.algebra.one :=
  (twistComparison TA D).sectionsMap_one

/-! ### The degree-one generator is an isomorphism -/

/-- The degree-one generator of a tensor algebra is an isomorphism onto the degree-one piece.

The bundle's `tensorPieceIso_one` says the generator followed by the degree-one identification
with the first tensor power is the identity, and the first tensor power *is* the sheaf itself, so
the generator is the inverse of that identification. -/
public def tensorGeneratorIso (X : Scheme.{u}) (L : X.Modules) :
    L ≅ (TA X L).tensor.piece 1 where
  hom := (TA X L).tensorGenerator
  inv := ((TA X L).tensorPieceIso 1).hom
  hom_inv_id := (TA X L).tensorPieceIso_one
  inv_hom_id :=
    Eq.trans
      (congrArg (fun k => ((TA X L).tensorPieceIso 1).hom ≫ k)
        (Eq.trans ((Iso.eq_comp_inv _).mpr (TA X L).tensorPieceIso_one)
          (Category.id_comp _)))
      ((TA X L).tensorPieceIso 1).hom_inv_id

@[simp]
public theorem tensorGeneratorIso_hom (X : Scheme.{u}) (L : X.Modules) :
    (tensorGeneratorIso TA X L).hom = (TA X L).tensorGenerator :=
  rfl

/-! ### The comparison attached to a module identified with the degree-one twist -/

/-- The canonical comparison attached to a module on relative Proj together with an
identification of it with the degree-one twist. -/
public def twistComparisonOf (L : (relativeProj A).scheme.Modules)
    (β : L ≅ D.algebra.piece 1) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (TA (relativeProj A).scheme L).tensor D.algebra :=
  (TA (relativeProj A).scheme L).tensor_isTensorAlgebra.descAny D.algebra β.hom

/-- The comparison extends the identification on the degree-one generator. -/
public theorem twistComparisonOf_extends (L : (relativeProj A).scheme.Modules)
    (β : L ≅ D.algebra.piece 1) :
    (TA (relativeProj A).scheme L).tensorGenerator ≫
      (twistComparisonOf TA D L β).app 1 = β.hom :=
  (TA (relativeProj A).scheme L).tensor_isTensorAlgebra.descAny_extends D.algebra β.hom

/-- Any unital homomorphism to the twist algebra extending the identification on the degree-one
generator is the canonical comparison. -/
public theorem twistComparisonOf_unique (L : (relativeProj A).scheme.Modules)
    (β : L ≅ D.algebra.piece 1)
    {g : SheafOfModules.GradedAlgebra.UnitalHom
      (TA (relativeProj A).scheme L).tensor D.algebra}
    (hg : (TA (relativeProj A).scheme L).tensorGenerator ≫ g.app 1 = β.hom) :
    g = twistComparisonOf TA D L β :=
  (TA (relativeProj A).scheme L).tensor_isTensorAlgebra.descAny_unique D.algebra β.hom hg

/-- At the degree-one twist itself, taken with the identity identification, the comparison is the
canonical comparison: both sides are `descAny` of the identity. -/
public theorem twistComparisonOf_refl :
    twistComparisonOf TA D (D.algebra.piece 1) (Iso.refl _) = twistComparison TA D :=
  rfl

/-- In degree one the comparison is the identification of the module with the degree-one twist,
read through the generator. -/
public theorem twistComparisonOf_app_one (L : (relativeProj A).scheme.Modules)
    (β : L ≅ D.algebra.piece 1) :
    (twistComparisonOf TA D L β).app 1 =
      ((tensorGeneratorIso TA (relativeProj A).scheme L).symm ≪≫ β).hom :=
  (Iso.eq_inv_comp (tensorGeneratorIso TA (relativeProj A).scheme L)).mpr
    (twistComparisonOf_extends TA D L β)

/-- The comparison is an isomorphism in degree one, with no hypothesis on the graded algebra: the
degree-one generator of a tensor algebra is an isomorphism, and the comparison extends an
isomorphism along it. -/
public instance isIso_twistComparisonOf_app_one (L : (relativeProj A).scheme.Modules)
    (β : L ≅ D.algebra.piece 1) : IsIso ((twistComparisonOf TA D L β).app 1) :=
  Eq.mpr (congrArg IsIso (twistComparisonOf_app_one TA D L β)) (Iso.isIso_hom _)

/-- The canonical comparison out of the tensor algebra of the degree-one twist is an isomorphism
in every nonnegative degree; concretely, the multiplication maps exhibit the `n`-th twist as the
`n`-th tensor power of the first. -/
public def TwistsAreTensorPowersOf (L : (relativeProj A).scheme.Modules)
    (β : L ≅ D.algebra.piece 1) : Prop :=
  ∀ n : ℕ, IsIso ((twistComparisonOf TA D L β).app (n : ℤ))

/-- `TwistsAreTensorPowersOf` needs no input in degree one. -/
public theorem twistsAreTensorPowersOf_iff (L : (relativeProj A).scheme.Modules)
    (β : L ≅ D.algebra.piece 1) :
    TwistsAreTensorPowersOf TA D L β ↔
      ∀ n : ℕ, n ≠ 1 → IsIso ((twistComparisonOf TA D L β).app (n : ℤ)) := by
  refine ⟨fun h n _ => h n, fun h n => ?_⟩
  by_cases hn : n = 1
  · subst hn
    exact Eq.mpr
      (congrArg (fun k : ℤ => IsIso ((twistComparisonOf TA D L β).app k)) Nat.cast_one)
      (isIso_twistComparisonOf_app_one TA D L β)
  · exact h n hn

/-! ### The comparison attached to a pair -/

/-- The canonical comparison attached to a pair on relative Proj together with an
identification of its invertible sheaf with the degree-one twist; the pair enters only through
that sheaf. -/
public def pairTwistComparison (P : F1Pair A TA (relativeProj A).toBase)
    (β : P.L ≅ D.algebra.piece 1) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (TA (relativeProj A).scheme P.L).tensor D.algebra :=
  twistComparisonOf TA D P.L β

/-- The comparison attached to a pair extends the identification on the degree-one generator. -/
public theorem pairTwistComparison_extends (P : F1Pair A TA (relativeProj A).toBase)
    (β : P.L ≅ D.algebra.piece 1) :
    (TA (relativeProj A).scheme P.L).tensorGenerator ≫
      (pairTwistComparison TA D P β).app 1 = β.hom :=
  twistComparisonOf_extends TA D P.L β

/-- Any unital homomorphism to the twist algebra extending the identification on the degree-one
generator is the canonical comparison. -/
public theorem pairTwistComparison_unique (P : F1Pair A TA (relativeProj A).toBase)
    (β : P.L ≅ D.algebra.piece 1)
    {g : SheafOfModules.GradedAlgebra.UnitalHom
      (TA (relativeProj A).scheme P.L).tensor D.algebra}
    (hg : (TA (relativeProj A).scheme P.L).tensorGenerator ≫ g.app 1 = β.hom) :
    g = pairTwistComparison TA D P β :=
  twistComparisonOf_unique TA D P.L β hg

/-- In degree one the comparison attached to a pair is the identification of the invertible
sheaf with the degree-one twist, read through the generator. -/
public theorem pairTwistComparison_app_one (P : F1Pair A TA (relativeProj A).toBase)
    (β : P.L ≅ D.algebra.piece 1) :
    (pairTwistComparison TA D P β).app 1 =
      ((tensorGeneratorIso TA (relativeProj A).scheme P.L).symm ≪≫ β).hom :=
  twistComparisonOf_app_one TA D P.L β

/-- The comparison attached to a pair is an isomorphism in degree one, with no hypothesis on the
graded algebra: the degree-one generator of a tensor algebra is an isomorphism, and the
comparison extends an isomorphism along it. -/
public instance isIso_pairTwistComparison_app_one (P : F1Pair A TA (relativeProj A).toBase)
    (β : P.L ≅ D.algebra.piece 1) : IsIso ((pairTwistComparison TA D P β).app 1) :=
  isIso_twistComparisonOf_app_one TA D P.L β

/-- The canonical comparison out of the tensor algebra of the pair's invertible sheaf is an
isomorphism in every nonnegative degree. -/
public def TwistsAreTensorPowers (P : F1Pair A TA (relativeProj A).toBase)
    (β : P.L ≅ D.algebra.piece 1) : Prop :=
  TwistsAreTensorPowersOf TA D P.L β

/-- `TwistsAreTensorPowers` needs no input in degree one. -/
public theorem twistsAreTensorPowers_iff (P : F1Pair A TA (relativeProj A).toBase)
    (β : P.L ≅ D.algebra.piece 1) :
    TwistsAreTensorPowers TA D P β ↔
      ∀ n : ℕ, n ≠ 1 → IsIso ((pairTwistComparison TA D P β).app (n : ℤ)) :=
  twistsAreTensorPowersOf_iff TA D P.L β

/-- The canonicality clause of Tag 01O4, with the graded-algebra map eliminated: a pair on
relative Proj is the canonical twist pair of `D` exactly when its invertible sheaf is identified
with the degree-one twist in such a way that the canonical comparison out of the tensor algebra
is an isomorphism in every nonnegative degree and carries the pair's graded map to the
homogeneous-section map of `D`. -/
public theorem isCanonicalTwistPair_iff (P : F1Pair A TA (relativeProj A).toBase) :
    IsCanonicalTwistPair A TA D P ↔
      ∃ β : P.L ≅ D.algebra.piece 1,
        TwistsAreTensorPowers TA D P β ∧
        (∀ n : ℕ, P.ψ (n : ℤ) ≫
          (Scheme.Modules.pushforward (relativeProj A).toBase).map
            ((pairTwistComparison TA D P β).app (n : ℤ)) = D.ψ n) := by
  constructor
  · rintro ⟨β, γ, hiso, hgen, hone, hψ⟩
    have hEq : SheafOfModules.GradedAlgebra.UnitalHom.ofHom γ hone =
        pairTwistComparison TA D P β :=
      pairTwistComparison_unique TA D P β hgen
    have happ : ∀ n : ℤ, γ.app n = (pairTwistComparison TA D P β).app n := fun n =>
      congrArg (fun g : SheafOfModules.GradedAlgebra.UnitalHom
        (TA (relativeProj A).scheme P.L).tensor D.algebra => g.app n) hEq
    exact ⟨β, fun n => (happ (n : ℤ)) ▸ hiso n, fun n => (happ (n : ℤ)) ▸ hψ n⟩
  · rintro ⟨β, hiso, hψ⟩
    exact ⟨β, (pairTwistComparison TA D P β).toHom, hiso,
      pairTwistComparison_extends TA D P β,
      (pairTwistComparison TA D P β).sectionsMap_one, hψ⟩

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
