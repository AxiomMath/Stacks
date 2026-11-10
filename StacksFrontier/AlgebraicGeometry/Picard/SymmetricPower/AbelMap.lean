module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.Geometry.HilbertSchemeGeometry
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# The Abel map at the level of functors

Let `X` be a smooth curve over a field `k`. A degree-`d` Hilbert family `Z ⊆ X_T` is a relative
effective Cartier divisor (Stacks Tag 0B9D), so it has an invertible module `𝒪_{X_T}(Z)`. The
*Abel map* `γ_d : Hilb^d_{X/k} → Pic_{X/k}` of Stacks Tag 0BA0 (4) sends `Z` to the class of
`𝒪_{X_T}(Z)`; this file constructs it on `T`-points and proves that it commutes with base
change, which is what makes it a transformation of functors `T ↦ Hilb^d_{X/k}(T)` to
`T ↦ Pic(X_T)` (and so, after sheafification, to `Pic_{X/k}`).

The first three declarations are the first layer of Stacks Tag 0B9X.

## Main definitions

* `AlgebraicGeometry.RigidifiedPicard.familyClass`: the class `[𝒪_{X_T}(Z)]` of a family.

## Main results

* `Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap`: the class of an effective
  Cartier divisor pulls back to the class of its inverse image (Stacks Tag 0C4U).
* `AlgebraicGeometry.RigidifiedPicard.isRelativeEffectiveCartierDivisor_hilbertFamily`.
* `AlgebraicGeometry.RigidifiedPicard.familyClass_baseChange`: **the Abel map commutes with
  base change.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Divisors

open _root_.AlgebraicGeometry

/-- **The pullback of the class `[𝒪(D)]` is the class of the inverse image** ([Stacks, Tag 0C4U]),
for `D'` an effective Cartier divisor equal to the inverse image of `D`. -/
theorem schemePullbackClass_picardClass_of_eq_comap {Y Y' : Scheme.{u}} (b : Y' ⟶ Y)
    (D : Y.IdealSheafData) (D' : Y'.IdealSheafData) [IsEffectiveCartierDivisor D]
    [IsEffectiveCartierDivisor D'] (h : D' = D.comap b) :
    Stacks.Picard.schemePullbackClass b (picardClass D) = picardClass D' := by
  let : IsPullbackDefined b D := by
    change IsEffectiveCartierDivisor (D.comap b)
    rw [← h]
    infer_instance
  refine (Stacks.Picard.pullbackClass_classOf b.toLRSHom.toShHom (invertibleSheaf' D)
    (isInvertible_invertibleSheaf_picard D)).trans ?_
  refine ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _
    (isInvertible_invertibleSheaf_picard (D.comap b))).2
      ⟨invertibleSheafPullbackIso b D⟩).trans ?_
  exact picardClass_congr h.symm

end Stacks.Divisors

namespace AlgebraicGeometry.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A degree-`d` Hilbert family of a smooth curve is a relative effective Cartier divisor**
([Stacks, Tag 0B9D]). -/
theorem isRelativeEffectiveCartierDivisor_hilbertFamily [IsCurve k f] [Smooth f] {d : ℕ}
    {T : Over (Spec (.of k))} (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor (pullback.snd f T.hom) Z.ideal := by
  let : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve _ f
  let : SmoothOfRelativeDimension 1 (pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) inferInstance
  let : Stacks.Morphisms.IsFiniteLocallyFree (Z.ideal.subschemeι ≫ pullback.snd f T.hom) :=
    @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ d
      Z.isFiniteLocallyFreeOfRank
  exact isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree _ _

/-- The Picard class `[𝒪(Z)]` of a Hilbert family of a smooth curve. -/
def familyClass [IsCurve k f] [Smooth f] {d : ℕ} {T : Over (Spec (.of k))}
    (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) :
    Stacks.Picard.ofScheme (pullback f T.hom) :=
  @Stacks.Divisors.picardClass (pullback f T.hom) Z.ideal
    (isRelativeEffectiveCartierDivisor_hilbertFamily f Z).1

/-- **The Abel map commutes with base change**: the class of the base change of a family along
`g : T' ⟶ T` is the pullback of its class along `X_{T'} ⟶ X_T`. This is the naturality of the
Abel map `γ_d : Hilb^d_{X/k} → Pic_{X/k}`, `Z ↦ [𝒪(Z)]`, of Stacks Tag 0BA0 (4) at the level of
functors. -/
theorem familyClass_baseChange [IsCurve k f] [Smooth f] {d : ℕ} {T T' : Over (Spec (.of k))}
    (g : T' ⟶ T) (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) :
    familyClass f (Stacks.Hilbert.baseChange (Over.mk f) g Z) =
      Stacks.Picard.schemePullbackClass (Stacks.Hilbert.familyBaseChangeMap (Over.mk f) g)
        (familyClass f Z) :=
  (@Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _
    (Stacks.Hilbert.familyBaseChangeMap (Over.mk f) g) Z.ideal
    (Stacks.Hilbert.baseChange (Over.mk f) g Z).ideal
    (isRelativeEffectiveCartierDivisor_hilbertFamily f Z).1
    (isRelativeEffectiveCartierDivisor_hilbertFamily f _).1 rfl).symm

end AlgebraicGeometry.RigidifiedPicard

end
