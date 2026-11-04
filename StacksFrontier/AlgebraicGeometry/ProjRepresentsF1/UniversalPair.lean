module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PieceZeroUnit

/-!
# The graded map of the universal pair of Tag 01O4

Tag 01O4 normalises its representing bijections by naming the pair that the identity morphism of
relative `Proj` classifies: the degree-one twist of Tag 01NR together with the
homogeneous-section map. That condition is `IsCanonicalTwistPair`, and
`isCanonicalTwistPair_iff_psi` reduces it to one equation on the pair's graded map. For an
algebra generated in degree one the canonical comparison out of the tensor algebra of the
degree-one twist is an isomorphism in every nonnegative degree, so the equation
`ψ_n ≫ π_*(γ_n) = D.ψ_n` has the unique solution `ψ_n = D.ψ_n ≫ π_*(γ_n⁻¹)`; that formula is
`universalPsi`, the degreewise data of the universal pair.

## Main definitions

* `twistComparisonOfAppIso`: the canonical comparison in a nonnegative degree, as an isomorphism.
* `universalPsi`: the graded map of the universal pair, in each nonnegative degree.

## Main results

* `isIso_twistComparison_app`: the canonical comparison `T(𝒪(1))_n ⟶ 𝒪(n)` is an isomorphism in
  every nonnegative degree, for an algebra generated in degree one.
* `universalPsi_comp_twistComparison`: `universalPsi` becomes the homogeneous-section map of the
  twist datum under the canonical comparison.
* `isCanonicalTwistPair_iff_psi_eq`: a pair on relative `Proj` is the canonical twist pair of `D`
  exactly when, for some identification of its invertible sheaf with the degree-one twist, its
  graded map is the homogeneous-section map of `D` followed by the inverse of the canonical
  comparison.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (TA : TensorAlgebras.{u})
  (D : TwistData A)

/-! ### The canonical comparison is invertible in every nonnegative degree -/

/-- The canonical comparison out of the tensor algebra of the degree-one twist is an isomorphism
in every nonnegative degree, for an algebra generated in degree one. -/
public theorem isIso_twistComparison_app (hgen : IsGeneratedInDegreeOne A) (n : ℕ) :
    IsIso ((twistComparison TA D).app (n : ℤ)) :=
  twistsAreTensorPowersOf TA D hgen (D.algebra.piece 1) (Iso.refl _) n

/-- The canonical comparison attached to a module identified with the degree-one twist, in a
nonnegative degree, as an isomorphism. -/
public def twistComparisonOfAppIso (hgen : IsGeneratedInDegreeOne A)
    (L : (relativeProj A).scheme.Modules) (β : L ≅ D.algebra.piece 1) (n : ℕ) :
    (TA (relativeProj A).scheme L).tensor.piece (n : ℤ) ≅ D.algebra.piece (n : ℤ) :=
  @asIso _ _ _ _ ((twistComparisonOf TA D L β).app (n : ℤ))
    (twistsAreTensorPowersOf TA D hgen L β n)

/-- The underlying morphism of `twistComparisonOfAppIso` is the canonical comparison in that
degree. -/
@[simp]
public theorem twistComparisonOfAppIso_hom (hgen : IsGeneratedInDegreeOne A)
    (L : (relativeProj A).scheme.Modules) (β : L ≅ D.algebra.piece 1) (n : ℕ) :
    (twistComparisonOfAppIso TA D hgen L β n).hom = (twistComparisonOf TA D L β).app (n : ℤ) :=
  rfl

/-- The canonical comparison at the degree-one twist itself, in a nonnegative degree, as an
isomorphism. -/
public def twistComparisonAppIso (hgen : IsGeneratedInDegreeOne A) (n : ℕ) :
    (TA (relativeProj A).scheme (D.algebra.piece 1)).tensor.piece (n : ℤ) ≅
      D.algebra.piece (n : ℤ) :=
  twistComparisonOfAppIso TA D hgen (D.algebra.piece 1) (Iso.refl _) n

/-- The underlying morphism of `twistComparisonAppIso` is the canonical comparison in that
degree. -/
@[simp]
public theorem twistComparisonAppIso_hom (hgen : IsGeneratedInDegreeOne A) (n : ℕ) :
    (twistComparisonAppIso TA D hgen n).hom = (twistComparison TA D).app (n : ℤ) :=
  rfl

/-! ### The graded map of the universal pair -/

/-- The graded map of the universal pair of Tag 01O4, in each nonnegative degree: the
homogeneous-section map of the twist datum, read back through the canonical comparison of the
tensor algebra of the degree-one twist with the algebra of twists. -/
public def universalPsi (hgen : IsGeneratedInDegreeOne A) (n : ℕ) :
    A.piece (n : ℤ) ⟶ (Scheme.Modules.pushforward (relativeProj A).toBase).obj
      ((TA (relativeProj A).scheme (D.algebra.piece 1)).tensor.piece (n : ℤ)) :=
  D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
    (twistComparisonAppIso TA D hgen n).inv

/-- `universalPsi` followed by the canonical comparison is the homogeneous-section map of the
twist datum, which is the canonicality equation of Tag 01O4. -/
public theorem universalPsi_comp_twistComparison (hgen : IsGeneratedInDegreeOne A) (n : ℕ) :
    universalPsi TA D hgen n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
        ((twistComparison TA D).app (n : ℤ)) = D.ψ n :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans
      (congrArg (fun z : (Scheme.Modules.pushforward (relativeProj A).toBase).obj
            (D.algebra.piece (n : ℤ)) ⟶
          (Scheme.Modules.pushforward (relativeProj A).toBase).obj
            (D.algebra.piece (n : ℤ)) => D.ψ n ≫ z)
        (Eq.trans
          ((Scheme.Modules.pushforward (relativeProj A).toBase).map_comp
            (twistComparisonAppIso TA D hgen n).inv
            (twistComparisonAppIso TA D hgen n).hom).symm
          (Eq.trans
            (congrArg (Scheme.Modules.pushforward (relativeProj A).toBase).map
              (twistComparisonAppIso TA D hgen n).inv_hom_id)
            ((Scheme.Modules.pushforward (relativeProj A).toBase).map_id _))))
      (Category.comp_id _))

/-! ### Canonicality forces the graded map -/

/-- Canonicality forces the graded map of a twist pair: a pair on relative `Proj` is the
canonical twist pair of `D` exactly when, for some identification `β` of its invertible sheaf
with the degree-one twist, its graded map is the homogeneous-section map of `D` followed by the
inverse of the canonical comparison — that is, is `universalPsi` read through `β`. -/
public theorem isCanonicalTwistPair_iff_psi_eq (hgen : IsGeneratedInDegreeOne A)
    (P : F1Pair A TA (relativeProj A).toBase) :
    IsCanonicalTwistPair A TA D P ↔
      ∃ β : P.L ≅ D.algebra.piece 1, ∀ n : ℕ, P.ψ (n : ℤ) =
        D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
          (twistComparisonOfAppIso TA D hgen P.L β n).inv :=
  (isCanonicalTwistPair_iff_psi TA D hgen P).trans
    ⟨fun ⟨β, hpsi⟩ => ⟨β, fun n =>
        (Iso.eq_comp_inv ((Scheme.Modules.pushforward (relativeProj A).toBase).mapIso
          (twistComparisonOfAppIso TA D hgen P.L β n))).mpr (hpsi n)⟩,
      fun ⟨β, hpsi⟩ => ⟨β, fun n =>
        (Iso.eq_comp_inv ((Scheme.Modules.pushforward (relativeProj A).toBase).mapIso
          (twistComparisonOfAppIso TA D hgen P.L β n))).mp (hpsi n)⟩⟩

/-- At the degree-one twist itself, with the identity identification, the formula canonicality
forces is `universalPsi`. -/
public theorem universalPsi_eq (hgen : IsGeneratedInDegreeOne A) (n : ℕ) :
    universalPsi TA D hgen n = D.ψ n ≫
      (Scheme.Modules.pushforward (relativeProj A).toBase).map
        (twistComparisonOfAppIso TA D hgen (D.algebra.piece 1) (Iso.refl _) n).inv :=
  rfl

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
