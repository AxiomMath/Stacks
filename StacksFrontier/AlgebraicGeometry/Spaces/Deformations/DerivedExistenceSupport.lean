module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence

/-!
# Supports proper over the base along the infinitesimal base changes

Let `(Aₙ)` be an inverse system of rings with surjective transition maps, `A = lim Aₙ`, `X` an
algebraic space over `Spec A` and `Xₙ = X ×_{Spec A} Spec Aₙ`. A closed subset of the points of
`Xₙ` which is proper over `Spec Aₙ` has closed image in the points of `X`, and that image is proper
over `Spec A`: the projection `Xₙ ⟶ X` is a closed immersion, hence universally closed, and
`Spec Aₙ ⟶ Spec A` is a closed immersion, hence proper, so the reduced induced subspace on the
subset is proper over `Spec A` and Stacks 0CZG applies.

This is the step of the generalization of Grothendieck's existence theorem proposed in Stacks
0DIR which produces, from the supports of the `Kₙ`, a closed subset of `X` proper over `A`.

## Main results

* `AlgebraicGeometry.Space.isProperOver_image_of_isClosedImmersion`: the image of a closed subset
  proper over `Y'` under a closed immersion `X' ⟶ X` lying over a proper `Y' ⟶ Y` is closed and
  proper over `Y`.
* `AlgebraicGeometry.Space.isProperOver_image_spaceProjection`: the case of `Xₙ ⟶ X` over
  `Spec Aₙ ⟶ Spec A`.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The image of a closed subset proper over the base under a closed immersion lying over a
proper morphism of bases is closed and proper over the target base.** Let `i : X' ⟶ X` be a
closed immersion, `p' : X' ⟶ Y'` and `p : X ⟶ Y` locally of finite type and `b : Y' ⟶ Y` proper
with `i ≫ p = p' ≫ b`. If `T` is a closed subset of the points of `X'` proper over `Y'`, then its
image in the points of `X` is closed and proper over `Y`. -/
theorem isProperOver_image_of_isClosedImmersion (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hY : IsAlgebraicSpace B S hS Y) (i : X' ⟶ X) (p' : X' ⟶ Y') (p : X ⟶ Y) (b : Y' ⟶ Y)
    (w : i ≫ p = p' ≫ b) (hi : IsClosedImmersion B S hS i) (hb : IsProper B S hS b)
    (hp' : IsLocallyOfFiniteType B S hS p') (hp : IsLocallyOfFiniteType B S hS p)
    (T : Set (points B S hS X')) (hT : IsClosed T)
    (hTp : IsProperOver B S hS hX' hY' p' hp' T hT) :
    ∃ hc : IsClosed (pointsMap B S hS X' i '' T),
      IsProperOver B S hS hX hY p hp (pointsMap B S hS X' i '' T) hc := by
  have hft : IsLocallyOfFiniteType B S hS (i ≫ p) :=
    isLocallyOfFiniteType_comp' B S hS i p hX hY
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS i hi) hp
  have hiuc := universallyClosed_of_isClosedImmersion B S hS hX' hX i hi
  have hTp' : IsProperOver B S hS hX' hY (i ≫ p) hft T hT := by
    change IsProper B S hS _
    rw [w, ← Category.assoc]
    exact isProper_comp' B S hS _ b hY' hY hTp hb
  exact ⟨isClosed_image_of_universallyClosed B S hS hX' hX i hiuc T hT,
    isProperOver_image_of_universallyClosed B S hS hX' hX hY i p hiuc hft hp T hT hTp'⟩

end General

section Stage

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (B : BigFppfSite.{u})
    (hS : B.Contains (limitBase F)) (hSn : ∀ n : ℕ, B.Contains (baseAt F n))
    (X : Over (schemeSpace (limitBaseObject F B hS)))

/-- **A closed subset of `Xₙ` proper over `Spec Aₙ` has closed image in `X`, proper over
`Spec A`**, when the transition maps of the inverse system are surjective: `Xₙ ⟶ X` is a closed
immersion lying over the closed immersion `Spec Aₙ ⟶ Spec A`. -/
theorem isProperOver_image_spaceProjection
    (hFs : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)
    (hXft : IsLocallyOfFiniteType B (limitBase F) hS X.hom.hom) (n : ℕ)
    (T : Set (points B (limitBase F) hS (spaceAt F B hS hSn X n).1)) (hT : IsClosed T)
    (hTp : IsProperOver B (limitBase F) hS (spaceAt F B hS hSn X n).2
      (schemeSpace (baseObjectAt F B hS hSn n)).2 (spaceBaseProjection F B hS hSn X n).hom
      (isLocallyOfFiniteType_spaceBaseProjection F B hS hSn X hXft n) T hT) :
    ∃ hc : IsClosed (pointsMap B (limitBase F) hS _ (spaceProjection F B hS hSn X n).hom '' T),
      IsProperOver B (limitBase F) hS X.left.2 (schemeSpace (limitBaseObject F B hS)).2
        X.hom.hom hXft _ hc :=
  isProperOver_image_of_isClosedImmersion B (limitBase F) hS _ _ _ _
    (spaceProjection F B hS hSn X n).hom (spaceBaseProjection F B hS hSn X n).hom X.hom.hom
    (baseSpaceProjection F B hS hSn n).hom
    (congrArg (fun g => g.hom) (isPullback_spaceAt F B hS hSn X n).w.symm)
    (isClosedImmersion_spaceProjection F B hS hSn X hFs n)
    (isProper_of_isClosedImmersion B (limitBase F) hS (schemeSpace (baseObjectAt F B hS hSn n)).2
      (schemeSpace (limitBaseObject F B hS)).2 _
      (isClosedImmersion_baseSpaceProjection F B hS hSn hFs n))
    _ hXft T hT hTp

end Stage

end AlgebraicGeometry.Space

end
