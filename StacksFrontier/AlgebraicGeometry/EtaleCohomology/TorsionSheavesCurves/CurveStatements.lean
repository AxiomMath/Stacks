module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.BaseChangePrimeToCharacteristic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ProperBaseChangeStatement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.AffineVanishingAboveDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DegreeTwoOpenRestrictionSurjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimePowerVanishingStatement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimeToCharacteristicFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.VanishingAboveDegreeTwo

/-!
# "Statements (1) -- (8) hold" for an abelian sheaf on a scheme over a field

Situation 0A52 lists eight statements about an abelian sheaf `F` on the small étale site of a
scheme `X` over an algebraically closed field `k`; "statements (1) -- (8) hold" for `F` when
those of the eight that apply to it are true. This file defines that conjunction.

## Main definitions

* `Stacks.EtaleCohomology.CurveStatements π F`: the conjunction of the eight statements for an
  abelian sheaf `F` on the small étale site of `X`, relative to the structure morphism
  `π : X ⟶ Spec k`: statements (4) and (5) for constructibility with respect to every ambient
  big étale site, statements (6) and (7) over every algebraically closed extension `k'/k`
  through the projection `scalarExtensionFst` of the scalar extension, and statement (8) over
  every open subscheme.

## Main results

* `Stacks.EtaleCohomology.TorsionSheafSituation.isVanishingAboveDegreeTwo_of_curveStatements`
  and its seven siblings: the conjunction gives each of the eight statement predicates for the
  sheaf of a `Stacks.EtaleCohomology.TorsionSheafSituation`.
* `Stacks.EtaleCohomology.TorsionSheafSituation.curveStatements_iff`: for a term of
  `Stacks.EtaleCohomology.TorsionSheafSituation`, the conjunction is equivalent to the eight
  statement predicates.

## References

* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-- **"Statements (1) -- (8) of Situation 0A52 hold" for `F`.** For an abelian sheaf `F` on the
small étale site of a scheme `X` with structure morphism `π : X ⟶ Spec k`, the conjunction of the
eight statements of Situation 0A52. -/
structure CurveStatements {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] : Prop where
  /-- **Statement (1), Tag 0A53.** `H^q(X, F) = 0` for `q > 2`. -/
  vanishing : IsVanishingAboveDegreeTwo.{u, v, w} F
  /-- **Statement (2), Tag 0A54.** `H^q(X, F) = 0` for `q > 1` if `X` is affine. -/
  affineVanishing : IsAffineVanishingAboveDegreeOne.{u, v, w} F
  /-- **Statement (3), Tag 0A55.** `H^q(X, F) = 0` for `q > 1` if `p = char(k) > 0` and `F` is
  `p`-power torsion. -/
  primePowerVanishing : ∀ (p : ℕ) [CharP k p], IsPrimePowerTorsionVanishing.{u, v, w} k p F
  /-- **Statement (4), Tag 0A56.** `H^q(X, F)` is finite if `F` is constructible and torsion
  prime to `char(k)`. -/
  finite_of_isPrimeToCharacteristicTorsion :
    ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{max (u + 1) v}],
      IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F →
        Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
          ∀ q : ℕ, Finite (Sheaf.H.{w} F q)
  /-- **Statement (5), Tag 0A57.** `H^q(X, F)` is finite if `X` is proper and `F` is
  constructible. -/
  finite_of_isProper :
    ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{max (u + 1) v}],
      IsProper π → IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F →
        ∀ q : ℕ, Finite (Sheaf.H.{w} F q)
  /-- **Statement (6), Tag 0A58.** `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is bijective for every
  algebraically closed extension `k'/k` if `F` is torsion prime to `char(k)`. -/
  bijective_of_isPrimeToCharacteristicTorsion :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
        [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
        [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology
          AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
        Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
          (scalarExtensionFst k k' π) F q)
  /-- **Statement (7), Tag 0A59.** `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is bijective for every
  algebraically closed extension `k'/k` if `X` is proper. -/
  bijective_of_isProper :
    IsProper π →
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
        [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
        [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology
          AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
        Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
          (scalarExtensionFst k k' π) F q)
  /-- **Statement (8), Tag 0A5A.** `H²(X, F) → H²(U, F)` is surjective for every open `U ⊆ X`. -/
  surjective : IsDegreeTwoOpenRestrictionSurjective.{u, v, w} F

namespace TorsionSheafSituation

variable (S : TorsionSheafSituation.{u, v})
  [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The bundle gives statement (1), Tag 0A53, for the situation's sheaf. -/
theorem isVanishingAboveDegreeTwo_of_curveStatements
    (h : CurveStatements.{u, v, w} S.structureMorphism S.F) :
    IsVanishingAboveDegreeTwo.{u, v, w} S.F :=
  h.vanishing

/-- The bundle gives statement (2), Tag 0A54, for the situation's sheaf. -/
theorem isAffineVanishingAboveDegreeOne_of_curveStatements
    (h : CurveStatements.{u, v, w} S.structureMorphism S.F) :
    IsAffineVanishingAboveDegreeOne.{u, v, w} S.F :=
  h.affineVanishing

/-- The bundle gives statement (3), Tag 0A55, for the situation's sheaf and the characteristic
`p` of its base field. -/
theorem isPrimePowerTorsionVanishing_of_curveStatements
    (h : CurveStatements.{u, v, w} S.structureMorphism S.F) (p : ℕ) [CharP S.k p] :
    IsPrimePowerTorsionVanishing.{u, v, w} S.k p S.F :=
  h.primePowerVanishing p

/-- The bundle gives statement (4), Tag 0A56, for the situation, for every ambient big étale
site. -/
theorem finiteCohomologyOfPrimeToCharacteristic_of_curveStatements
    (h : CurveStatements.{u, v, w} S.structureMorphism S.F)
    (B : BigEtaleSite.{u}) (hX : B.Contains S.X)
    [∀ (T T' : B.Scheme) (f : T' ⟶ T),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v}
        (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
        (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
      HasWeakSheafify
        ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
        AddCommGrpCat.{max (u + 1) v}] :
    S.FiniteCohomologyOfPrimeToCharacteristic.{u, v, w} B hX :=
  h.finite_of_isPrimeToCharacteristicTorsion B hX

/-- The bundle gives statement (5), Tag 0A57, for the situation, for every ambient big étale
site. -/
theorem finiteCohomologyOfIsProper_of_curveStatements
    (h : CurveStatements.{u, v, w} S.structureMorphism S.F)
    (B : BigEtaleSite.{u}) (hX : B.Contains S.X)
    [∀ (T T' : B.Scheme) (f : T' ⟶ T),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v}
        (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
        (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
      HasWeakSheafify
        ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
        AddCommGrpCat.{max (u + 1) v}] :
    S.FiniteCohomologyOfIsProper.{u, v, w} B hX :=
  h.finite_of_isProper B hX

/-- The bundle gives statement (6), Tag 0A58, for the situation. -/
theorem baseChangePrimeToCharacteristic_of_curveStatements
    (h : CurveStatements.{u, v, w} S.structureMorphism S.F) :
    S.BaseChangePrimeToCharacteristic.{u, v, w} :=
  h.bijective_of_isPrimeToCharacteristicTorsion

/-- The bundle gives statement (7), Tag 0A59, for the situation. -/
theorem properBaseChangeStatement_of_curveStatements
    (h : CurveStatements.{u, v, w} S.structureMorphism S.F) :
    S.ProperBaseChangeStatement.{u, v, w} :=
  h.bijective_of_isProper

/-- The bundle gives statement (8), Tag 0A5A, for the situation's sheaf. -/
theorem isDegreeTwoOpenRestrictionSurjective_of_curveStatements
    (h : CurveStatements.{u, v, w} S.structureMorphism S.F) :
    IsDegreeTwoOpenRestrictionSurjective.{u, v, w} S.F :=
  h.surjective

/-- **The bundle is exactly the eight statement predicates.** For a Situation 0A52, "statements
(1) -- (8) hold" in the sense of `Stacks.EtaleCohomology.CurveStatements` if and only if each of
the library's eight statement predicates, Tags 0A53 to 0A5A, holds for it — statements (4) and
(5) for every ambient big étale site, statement (3) at the characteristic of the base field. -/
theorem curveStatements_iff :
    CurveStatements.{u, v, w} S.structureMorphism S.F ↔
      IsVanishingAboveDegreeTwo.{u, v, w} S.F ∧
      IsAffineVanishingAboveDegreeOne.{u, v, w} S.F ∧
      (∀ (p : ℕ) [CharP S.k p], IsPrimePowerTorsionVanishing.{u, v, w} S.k p S.F) ∧
      (∀ (B : BigEtaleSite.{u}) (hX : B.Contains S.X)
        [∀ (T T' : B.Scheme) (f : T' ⟶ T),
          ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v}
            (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
            (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
        [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
          HasWeakSheafify
            ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
            AddCommGrpCat.{max (u + 1) v}],
        S.FiniteCohomologyOfPrimeToCharacteristic.{u, v, w} B hX) ∧
      (∀ (B : BigEtaleSite.{u}) (hX : B.Contains S.X)
        [∀ (T T' : B.Scheme) (f : T' ⟶ T),
          ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v}
            (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
            (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
        [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
          HasWeakSheafify
            ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
            AddCommGrpCat.{max (u + 1) v}],
        S.FiniteCohomologyOfIsProper.{u, v, w} B hX) ∧
      S.BaseChangePrimeToCharacteristic.{u, v, w} ∧
      S.ProperBaseChangeStatement.{u, v, w} ∧
      IsDegreeTwoOpenRestrictionSurjective.{u, v, w} S.F :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩⟩

end TorsionSheafSituation

end Stacks.EtaleCohomology

end
