module

public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerDeterminant
public import StacksFrontier.AlgebraicGeometry.Conormal.SmoothRank
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback

/-!
# The adjunction formula

Let `i : Z ⟶ P` be an immersion of schemes over `S`, with `P` smooth of relative dimension
`m + 2` and `Z` smooth of relative dimension `m + 1` over `S`. The conormal sequence
`0 ⟶ 𝒞_{Z/P} ⟶ i^*Ω_{P/S} ⟶ Ω_{Z/S} ⟶ 0` of [Stacks, Tag 06AA] is a short exact sequence of
finite locally free modules of ranks `1`, `m + 2` and `m + 1`, so taking determinants
([Stacks, Tag 0B38]) and commuting the pullback with the exterior power ([Stacks, Tag 01CI])
gives the *adjunction formula*

`i^*(⋀^{m+2} Ω_{P/S}) ≅ 𝒞_{Z/P} ⊗ ⋀^{m+1} Ω_{Z/S}`.

## Main definitions

* `Stacks.Conormal.pullbackExteriorPowerIsoConormalTensor`: the adjunction formula.

## References

* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Conormal

/-- **The conormal sheaf of a codimension-one immersion of smooth schemes is invertible**, in
the sectionwise spelling `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf` that is the
first term of the conormal sequence: it has rank `(m + 2) - (m + 1) = 1`. -/
theorem isFiniteLocallyFreeOfRank_conormalShortComplex_X₁ {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S) (m : ℕ) [SmoothOfRelativeDimension (m + 2) p]
    [SmoothOfRelativeDimension (m + 1) (i ≫ p)] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₁ 1 := by
  have h := isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension i p (m + 2) (m + 1)
  rw [show m + 2 - (m + 1) = 1 by omega] at h
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso i).symm (h := h)

/-- **The adjunction formula.** For an immersion `i : Z ⟶ P` over `S` with `P` smooth of
relative dimension `m + 2` and `Z` smooth of relative dimension `m + 1`,

`i^*(⋀^{m+2} Ω_{P/S}) ≅ 𝒞_{Z/P} ⊗ ⋀^{m+1} Ω_{Z/S}`,

the determinant ([Stacks, Tag 0B38]) of the conormal sequence of [Stacks, Tag 06AA], with the
pullback commuted past the exterior power ([Stacks, Tag 01CI]) and `⋀¹ 𝒞 ≅ 𝒞`. -/
def pullbackExteriorPowerIsoConormalTensor {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (p : X ⟶ S) (m : ℕ) [SmoothOfRelativeDimension (m + 2) p]
    [SmoothOfRelativeDimension (m + 1) (i ≫ p)] :
    (Scheme.Modules.pullback i).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials p) ((m + 2 : ℕ) : ℤ)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj
          (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₁).obj
            (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (i ≫ p))
              ((m + 1 : ℕ) : ℤ))) :=
  have : Smooth (i ≫ p) := SmoothOfRelativeDimension.smooth (m + 1) (i ≫ p)
  have hS := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i p inferInstance
  Scheme.Modules.exteriorPowerPullbackIso i _ _ ≪≫
    (eqToIso (by rw [show m + 2 = 1 + (m + 1) by omega])) ≪≫
    (Scheme.Modules.exteriorPowerTensorExteriorPowerIso _ _ _ hS 1 m
      (hE' := isFiniteLocallyFreeOfRank_conormalShortComplex_X₁ i p m)
      (hE'' := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials (i ≫ p)
        (m + 1))).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).mapIso
        (Scheme.Modules.exteriorPowerOneIsoSelf _)).app _

end Stacks.Conormal

end
