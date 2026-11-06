module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AdicFibreIdealPower
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.TowerComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentExistence.Setting
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType

/-!
# The tower of adic fibres of an algebraic space over a Noetherian ring

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `X` an algebraic space locally of finite type
over `Spec A`, with adic fibres `ι_n : X_n = X ×_{Spec A} Spec (A / I ^ (n + 1)) ⟶ X`. This file
assembles the data with which `StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem`
compares the systems of coherent modules on the `X_n` (Stacks 08BF) with the coherent adic systems
along `I 𝒪_X` (Stacks 08BE): the `ι_n` are closed immersions compatible with the transitions,
every `X_n` is locally Noetherian, and the ideal of `ι_n` is `(I 𝒪_X) ^ (n + 1)`.

## Main definitions

* `AlgebraicGeometry.Space.adicFibreRestriction`: `F ↦ (ι_n ^* F)_n`, from coherent
  `𝒪_X`-modules to coherent systems on the adic fibres.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_adicFibreFstHom`: `ι_n` is a closed immersion.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_adicFibre`: `X_n` is
  locally Noetherian.

## References

* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (baseObject A B hA))

/-- The transitions between the adic fibres lie over `X`. -/
@[reassoc (attr := simp)]
theorem adicFibreSuccHom_comp_adicFibreFstHom (n : ℕ) :
    adicFibreSuccHom A I B hA hX f n ≫ adicFibreFstHom A I B hA hX f (n + 1) =
      adicFibreFstHom A I B hA hX f n :=
  ObjectProperty.hom_ext _ ((ObjectProperty.FullSubcategory.comp_hom _ _ _).trans
    (adicFibreSucc_fst A I B hA (contains_adicThickening A I B hA) f n))

/-- **`ι_n : X_n ⟶ X` is a closed immersion**, being the base change of the closed immersion of
`Spec (A / I ^ (n + 1))` into `Spec A`. -/
theorem isClosedImmersion_adicFibreFstHom (n : ℕ) :
    IsClosedImmersion B (Spec (.of A)) hA (adicFibreFstHom A I B hA hX f n).hom :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA))).of_isPullback
    (IsPullback.of_hasPullback f
      (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n))).flip
    (isClosedImmersion_yoneda_map_adicThickeningMap A I B hA n)

/-- **Every adic fibre of an algebraic space locally of finite type over a Noetherian ring is
locally Noetherian.** -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_adicFibre [IsNoetherianRing A]
    (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA f) (n : ℕ) :
    HasEtaleLocalProperty B (Spec (.of A)) hA (adicFibreSpace A I B hA hX f n).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (.of A)) hA
    (adicFibreSpace A I B hA hX f n).2 hX _
    (isLocallyOfFiniteType_of_isClosedImmersion B (Spec (.of A)) hA _
      (isClosedImmersion_adicFibreFstHom A I B hA hX f n))
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isFiniteType_baseObject A B hA hX f hft)

/-- **Restriction to the adic fibres**, `F ↦ (ι_n ^* F)_n`, from coherent `𝒪_X`-modules to
coherent systems `(F_n, φ_n)` on the tower of adic fibres. -/
abbrev adicFibreRestriction [IsNoetherianRing A]
    (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA f) :
    CoherentModules.{u, u} B (Spec (.of A)) hA X hX ⥤
      ThickeningCoherentSystem B (Spec (.of A)) hA (adicFibreSpace A I B hA hX f)
        (adicFibreSuccHom A I B hA hX f) :=
  thickeningRestriction B (Spec (.of A)) hA (X := ⟨X, hX⟩) (adicFibreFstHom A I B hA hX f)
    (adicFibreSuccHom A I B hA hX f) (adicFibreSuccHom_comp_adicFibreFstHom A I B hA hX f)
    (hasEtaleLocalProperty_isLocallyNoetherian_adicFibre A I B hA hX f hft)

end AlgebraicGeometry.Space

end
