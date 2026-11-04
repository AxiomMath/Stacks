module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetAbelianBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationBaseChangeReduction

/-!
# Base change for a proper direct image of étale sheaves (Stacks 0A3T, 0A3U)

Let `f : X ⟶ Y` be proper and `g : Y' ⟶ Y` arbitrary, with cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
The base change map `g^{-1} f_* F ⟶ f'_* (g')^{-1} F` is an isomorphism for every sheaf `F` on
`X_étale` ([Stacks, Tag 0A3U]), and at a geometric point `x` of the base the stalk `(f_* F)_x` is
the set of sections of `F` over the geometric fibre ([Stacks, Tag 0A3T]).

The proof runs at abelian coefficients and is transported to sheaves of sets.

* At a geometric point, the base change map factors through the strict henselization; the second
  factor lies over the closed point of a strictly henselian local scheme, where
  [Stacks, Tag 0A3S], [Stacks, Tag 09ZH] and [Stacks, Tag 0A3I] apply
  (`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isProper_of_strictHenselization`).
  The first factor becomes invertible after inverse image to the geometric point by
  [Stacks, Tag 03Q9] in degree zero for sheaves of sets, which is transported to abelian sheaves
  by `Stacks.EtaleCohomology.isIso_etaleAbelianInverseImage_map_etaleAbelianBaseChange_app`.
* Base change for abelian sheaves gives base change for sheaves of sets
  (`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isIso_etaleAbelianBaseChange`), and
  Tag 0A3T is Tag 0A3U for the square defining the geometric fibre
  (`Stacks.EtaleCohomology.isIso_properGeometricFibreComparison_of_isIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- Base change for a proper direct image of abelian sheaves, from Tag 03Q9 in degree zero for
sheaves of sets (the hypothesis `hsh`: for `φ : A ⟶ S` proper and `s` a geometric point of `S`,
the set base change map of the square of `φ` over the strict henselization
`π : Spec(O^{sh}_{S,s}) ⟶ S` becomes invertible after inverse image along the canonical lift
`s̃ : Spec Ω ⟶ Spec(O^{sh}_{S,s})` of `s`). -/
theorem isIso_etaleAbelianBaseChange_of_isProper_of_strictHenselizationSet
    (hsh : ∀ ⦃A S : Scheme.{u}⦄ (φ : A ⟶ S), IsProper φ → ∀ (s : GeometricPoint S)
      (F : Sheaf A.smallEtaleTopology (Type (u + 1))),
      IsIso ((smallEtaleInverseImage.{u, 0} (geometricPointToStrictHenselization
          (BigEtaleSite.containing S) S (BigEtaleSite.contains_containing S) s)).map
        ((smallEtaleSetBaseChange.{u, 0}
            (pullback.fst φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s))
            (pullback.snd φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s))
            φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s) pullback.condition).app F)))
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) :
    IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' sq.w) :=
  isIso_etaleAbelianBaseChange_of_isProper_of_strictHenselization
    (fun _ _ φ hφ s K ↦ isIso_etaleAbelianInverseImage_map_etaleAbelianBaseChange_app φ
      (strictHenselizationToBase (BigEtaleSite.containing _) _
        (BigEtaleSite.contains_containing _) s)
      (pullback.fst φ _) (pullback.snd φ _) pullback.condition
      (geometricPointToStrictHenselization (BigEtaleSite.containing _) _
        (BigEtaleSite.contains_containing _) s) K (hsh φ hφ s _))
    f g g' f' sq

/-- Base change for a proper direct image of sheaves of sets, from Tag 03Q9 in degree zero for
sheaves of sets. -/
theorem isIso_smallEtaleSetBaseChange_of_isProper_of_strictHenselizationSet
    (hsh : ∀ ⦃A S : Scheme.{u}⦄ (φ : A ⟶ S), IsProper φ → ∀ (s : GeometricPoint S)
      (F : Sheaf A.smallEtaleTopology (Type (u + 1))),
      IsIso ((smallEtaleInverseImage.{u, 0} (geometricPointToStrictHenselization
          (BigEtaleSite.containing S) S (BigEtaleSite.contains_containing S) s)).map
        ((smallEtaleSetBaseChange.{u, 0}
            (pullback.fst φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s))
            (pullback.snd φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s))
            φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s) pullback.condition).app F)))
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) :
    IsIso (smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w) :=
  isIso_smallEtaleSetBaseChange_of_isIso_etaleAbelianBaseChange f g g' f' sq.w
    (isIso_etaleAbelianBaseChange_of_isProper_of_strictHenselizationSet hsh f g g' f' sq)

/-- The comparison of Tag 0A3T is bijective, from Tag 03Q9 in degree zero for sheaves of
sets. -/
theorem isIso_properGeometricFibreComparison_of_strictHenselizationSet
    (hsh : ∀ ⦃A S : Scheme.{u}⦄ (φ : A ⟶ S), IsProper φ → ∀ (s : GeometricPoint S)
      (F : Sheaf A.smallEtaleTopology (Type (u + 1))),
      IsIso ((smallEtaleInverseImage.{u, 0} (geometricPointToStrictHenselization
          (BigEtaleSite.containing S) S (BigEtaleSite.contains_containing S) s)).map
        ((smallEtaleSetBaseChange.{u, 0}
            (pullback.fst φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s))
            (pullback.snd φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s))
            φ (strictHenselizationToBase (BigEtaleSite.containing S) S
              (BigEtaleSite.contains_containing S) s) pullback.condition).app F)))
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ S) :
    IsIso (properGeometricFibreComparison.{u, 0} f x) :=
  isIso_properGeometricFibreComparison_of_isIso f x
    (isIso_smallEtaleSetBaseChange_of_isProper_of_strictHenselizationSet hsh f x _ _
      (IsPullback.of_hasPullback f x))

end Stacks.EtaleCohomology

end
