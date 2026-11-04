module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelFamilyFinality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelScalars

/-!
# Faithfulness of the functor of [Stacks, Tag 07JG] over the tower of [Stacks, Tag 07JN]

Over the degree-zero member `e ↦ (X, T(0)_e, δ(0))` of `wholeSpaceSystem`, the tower
`T_e = Spec(D_e)` of [Stacks, Proposition 60.20.1, Tag 07JN] fixed in the proof of
[Stacks, Proposition 60.17.4, Tag 07JH], with scalars `wholeSpaceLevelScalars hp 0`, the functor of
[Stacks, Lemma 60.17.3, Tag 07JG] from crystals in quasi-coherent `𝒪_{X/S}`-modules to pairs
`(M, ∇)` is faithful, for any reduction datum.

## Main results

In `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `LevelComparison07JG.faithful_functor_wholeSpaceTower`: the reduction functor of a level
  comparison datum over this tower is faithful.
* `LevelReduction07JG.faithful_functor07JG_wholeSpaceTower`: the functor `functor07JG` of a level
  reduction datum over this tower is faithful.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/



@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u uI

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  {A : Type u} [CommRing A] {g : A →+* (wholeSpaceSystemEnvelope hp 0).ring}
  {Omega : Type u} [AddCommGroup Omega]
  [Module (wholeSpaceSystemEnvelope hp 0).ring Omega]
  [Module ((wholeSpaceSystemEnvelope hp 0).ring)ᵐᵒᵖ Omega]
  [IsCentralScalar (wholeSpaceSystemEnvelope hp 0).ring Omega]
  {d : DividedPowerDerivation A (wholeSpaceSystemEnvelope hp 0).ring g Omega} {p : ℕ}
  {ι : Type uI} {dx : ι → Omega}

/-- The reduction functor of [Stacks, Tag 07JG] of a level comparison datum over the tower
`wholeSpaceLevelScalars hp 0` is faithful. -/
theorem LevelComparison07JG.faithful_functor_wholeSpaceTower
    (C : LevelComparison07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d p dx
      (wholeSpaceLevelScalars hp 0)) :
    Functor.Faithful C.functor :=
  C.faithful_functor_of_wholeSpaceSystem hp rfl

/-- The functor of [Stacks, Lemma 60.17.3, Tag 07JG] from the crystals in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)` to the pairs `(M, ∇)` is faithful, for any level reduction datum
over the degree-zero tower `T_e = Spec(D_e)` of [Stacks, Tag 07JN]. -/
theorem LevelReduction07JG.faithful_functor07JG_wholeSpaceTower
    (R : LevelReduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d p dx
      (wholeSpaceLevelScalars hp 0)) :
    Functor.Faithful (functor07JG (LevelReduction07JG.toReduction07JGWholeSpace hp R)) :=
  R.faithful_functor07JG_of_wholeSpaceSystem hp rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
