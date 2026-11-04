module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RightDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ModuleSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionCoefficientsDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible

/-!
# Proper base change for `Rᵠ f_* 𝐙/ℓ`

For a cartesian square `X' = Y' ×_Y X` with `f : X ⟶ Y` proper and a prime `ℓ`, the higher direct
images of the constant sheaf of `𝔽_ℓ`-modules commute with the base change:
`g⁻¹ Rᵠ f_* 𝐙/ℓ ≅ Rᵠ f'_* 𝐙/ℓ` as sheaves of `𝔽_ℓ`-modules on `Y'_étale`.

## Main definitions

* `Stacks.EtaleCohomology.rightDerivedConstantUnitForgetIso`: the underlying abelian sheaf of
  `Rᵠ f_* 𝐙/ℓ` is `Rᵠ f_*` of the constant abelian sheaf `𝐙/ℓ`.
* `Stacks.EtaleCohomology.rightDerivedConstantUnitProperBaseChangeIso`: the isomorphism
  `g⁻¹ Rᵠ f_* 𝐙/ℓ ≅ Rᵠ f'_* 𝐙/ℓ`.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **The underlying abelian sheaf of `Rᵠ f_* 𝐙/ℓ`** is `Rᵠ f_*` of the constant abelian sheaf on
`𝐙/ℓ`, for any morphism `f : X ⟶ Y` and any commutative ring `Λ` in place of `𝐙/ℓ`. -/
def rightDerivedConstantUnitForgetIso {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) (Λ : Type)
    [CommRing Λ] :
    (etaleModuleForgetAb.{u, 0} Λ Y).obj (rightDerivedConstantUnit f q Λ) ≅
      ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} Λ))) :=
  (rightDerivedEtaleModuleDirectImageForgetIso Λ f q).app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (ULift.{u + 1} Λ))) ≪≫
    ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).mapIso
      ((Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ X.smallEtaleTopology).app
        (ModuleCat.of Λ (ULift.{u + 1} Λ)))

/-- **Proper base change for `Rᵠ f_* 𝐙/ℓ`.** For a cartesian square
`X' = Y' ×_Y X` with `f : X ⟶ Y` proper, projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`, and a
prime `ℓ`, the inverse image along `g : Y' ⟶ Y` of the sheaf of `𝔽_ℓ`-modules `Rᵠ f_* 𝐙/ℓ` is
`Rᵠ f'_* 𝐙/ℓ`. -/
def rightDerivedConstantUnitProperBaseChangeIso {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ) :
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj (rightDerivedConstantUnit f q (ZMod ℓ)) ≅
      rightDerivedConstantUnit f' q (ZMod ℓ) :=
  have : Finite (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) :=
    inferInstanceAs (Finite (ULift.{u + 1} (ZMod ℓ)))
  have hT := Stacks.Torsion.torsionSheafProperty_constantSheaf X.smallEtaleTopology
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))
  (Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful Y' ℓ).preimageIso
    (((etaleModuleForgetInverseImageIso.{u, 0} (ZMod ℓ) g).app
        (rightDerivedConstantUnit f q (ZMod ℓ))).symm ≪≫
      (etaleAbelianInverseImage.{u, 0} g).mapIso (rightDerivedConstantUnitForgetIso f q (ZMod ℓ)) ≪≫
      rightDerivedDirectImageProperBaseChangeIso f g g' f' sq _ hT q ≪≫
      ((etaleAbelianDirectImage.{u, 0} f').rightDerived q).mapIso
        ((etaleAbelianInverseImageConstantIso.{u, 0} g').app _) ≪≫
      (rightDerivedConstantUnitForgetIso f' q (ZMod ℓ)).symm)

end Stacks.EtaleCohomology

end
