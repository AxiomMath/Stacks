module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleCoefficientUniverse

/-!
# The eight statements of Situation 0A52 at every coefficient universe

This file completes the transport of the reduction theorem for Theorem 03SC to the coefficients
`AddCommGrpCat.{max (u + 1) v}` of Situation 0A52. Statements (1), (2), (3), (6), (7), (8) are
`Stacks.EtaleCohomology.curveStatements_partial_of_torsionSheafProperty`; statements (4) and (5),
which assume constructibility, follow from the fact that a constructible sheaf at the large
coefficient universe is the universe lift of a sheaf at `AddCommGrpCat.{u + 1}` constructible on
every big étale
site (`Stacks.EtaleCohomology.exists_etaleUlift_iso_isConstructibleOnEveryBigSite`), to which the
reduction theorem applies, and the lift does not change cohomology.

## Main results

* `Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty_max`: the whole bundle
  `Stacks.EtaleCohomology.CurveStatements` for every torsion sheaf at every coefficient universe
  and every `Ext` universe, granted the base case of Lemma 0A5B.
* `Stacks.EtaleCohomology.TorsionSheafSituation.curveStatements_of_base`: the eight statements
  for every such situation.

**No `@[stacks]` attribute**: the base case of Lemma 0A5B enters as the hypothesis `hbase`; the
tagged statements are in `TorsionSheavesCurves/CurveCohomologyTheorem.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- **Statements (4) and (5) one coefficient universe down.** In Situation 0A52, granted the base
case of Lemma 0A5B, a sheaf at the coefficients `AddCommGrpCat.{max (u + 1) v}` constructible on a
big étale site is the universe lift of a sheaf at `AddCommGrpCat.{u + 1}` whose cohomology is
finite when the torsion of `F` is prime to the characteristic, and when `X` is proper. -/
theorem exists_etaleUlift_iso_finite_sheafH_of_isConstructible {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π]
    [LocallyOfFiniteType π] [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
    (hbase : ∀ ℓ : ℕ, ℓ.Prime →
      CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (B : BigEtaleSite.{u}) (hX : B.Contains X)
    [∀ (T T' : B.Scheme) (f : T' ⟶ T),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v}
        (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
        (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
      HasWeakSheafify
        ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
        AddCommGrpCat.{max (u + 1) v}]
    (hF : IsConstructibleEtaleAbelianSheaf.{u, v} B X hX F) :
    ∃ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Nonempty ((etaleUlift.{v} X).obj G ≅ F) ∧
      (Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
        ∀ q : ℕ, Finite (Sheaf.H.{u + 1} G q)) ∧
      (IsProper π → ∀ q : ℕ, Finite (Sheaf.H.{u + 1} G q)) := by
  obtain ⟨G, ⟨e⟩, hG⟩ := exists_etaleUlift_iso_isConstructibleOnEveryBigSite B hX F hF
  have hGs := curveStatements_of_isConstructible π hdim hbase G hG
  obtain ⟨B', hB'⟩ := BigEtaleSite.exists_contains_of_small ({X} : Set Scheme.{u})
  have hX' : B'.Contains X := hB' X rfl
  exact ⟨G, ⟨e⟩, fun htors q ↦ hGs.finite_of_isPrimeToCharacteristicTorsion B' hX' (hG B' hX')
      (isPrimeToCharacteristicTorsion_of_etaleUlift
        (isPrimeToCharacteristicTorsion_of_mono e.hom htors)) q,
    fun hπ q ↦ hGs.finite_of_isProper B' hX' hπ (hG B' hX') q⟩

/-- **The reduction theorem for Theorem 03SC at every coefficient universe.** In Situation 0A52,
granted Lemma 0A5B for `Z/ℓ` on smooth curves for every prime `ℓ` (at the coefficients
`AddCommGrpCat.{u + 1}`), the eight statements of the list hold for every torsion abelian sheaf at
the coefficients `AddCommGrpCat.{max (u + 1) v}`, with `Ext` in any universe. -/
theorem curveStatements_of_torsionSheafProperty_max {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
    (hbase : ∀ ℓ : ℕ, ℓ.Prime →
      CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    CurveStatements.{u, v, w} π F := by
  obtain ⟨h1, h2, h3, h6, h7, h8⟩ :=
    curveStatements_partial_of_torsionSheafProperty.{w} π hdim hbase F hF
  exact
    { vanishing := h1
      affineVanishing := h2
      primePowerVanishing := h3
      finite_of_isPrimeToCharacteristicTorsion := fun B hX _ _ hc htors q ↦ by
        obtain ⟨G, ⟨e⟩, hG, -⟩ :=
          exists_etaleUlift_iso_finite_sheafH_of_isConstructible π hdim hbase F B hX hc
        exact finite_sheafH_of_etaleUlift_iso e q (hG htors q)
      finite_of_isProper := fun B hX _ _ hπ hc q ↦ by
        obtain ⟨G, ⟨e⟩, -, hG⟩ :=
          exists_etaleUlift_iso_finite_sheafH_of_isConstructible π hdim hbase F B hX hc
        exact finite_sheafH_of_etaleUlift_iso e q (hG hπ q)
      bijective_of_isPrimeToCharacteristicTorsion := h6
      bijective_of_isProper := h7
      surjective := h8 }

namespace TorsionSheafSituation

variable (S : TorsionSheafSituation.{u, v})
  (hbase : ∀ ℓ : ℕ, ℓ.Prime →
    CurveStatementsConstantOnSmoothCurves S.k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))

include hbase

/-- **The eight statements of Situation 0A52 (Theorem 03SC)**, granted the base case `Z/ℓ` on
smooth curves of Lemma 0A5B. -/
theorem curveStatements_of_base
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    CurveStatements.{u, v, w} S.structureMorphism S.F :=
  curveStatements_of_torsionSheafProperty_max S.structureMorphism S.dimension_le_one hbase S.F
    S.isTorsion

end TorsionSheafSituation

end Stacks.EtaleCohomology
