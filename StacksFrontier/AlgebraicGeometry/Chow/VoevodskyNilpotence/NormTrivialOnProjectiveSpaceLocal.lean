module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormTrivialOnProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceSpecialization

/-!
# The norm sheaf of Stacks 0FH9 is trivial on projective spaces: a family over any base

Let `π : P ⟶ Q` be finite locally free of rank `d > 0` over a field `k`, and let `T` be a scheme
over `k` with two `k`-points `p` and `q` having a common generization `η`, the local rings of `T`
at `p`, at `q` and at `η` being unique factorization domains. Given an invertible module `ℒ'` on
`T ×_k P` whose fibre over `p` is trivial and whose fibre over `q` is `ℒ`, `j^*(Norm_π ℒ)` is
trivial for every `j : ℙᵐ_k ⟶ Q` over `k`. This generalises
`StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormTrivialOnProjectiveSpace`, whose base
is `T = Spec A` with `A` a unique factorization domain.

## Main results

* `Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_family_specializes`: the
  abstract form.
* `Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily_specializes`:
  the form of the source, the family living on `(T ×_k Q) ×_Q P`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.SheafOfModules

universe u

namespace Stacks.Divisors

variable {P Q : Scheme.{u}} {k : Type u} [Field k]

/-- **The norm sheaf is trivial on projective space, abstract form over an arbitrary base.** As
`Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_family`, with the base `Spec A`
replaced by any scheme `T` with two `k`-points `p`, `q` and a common generization `η` of both,
the local rings of `T` at the three points being unique factorization domains. -/
theorem pullbackPicardClass_normInvertible_eq_zero_of_family_specializes {P' Q' T : Scheme.{u}}
    (π : P ⟶ Q) (π' : P' ⟶ Q') (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank π d]
    [Morphisms.IsFiniteLocallyFreeOfRank π' d] (hd : 0 < d) (m : ℕ)
    (p q : Spec (CommRingCat.of k) ⟶ T) (η : T)
    (hpη : η ⤳ p (IsLocalRing.closedPoint (CommRingCat.of k)))
    (hqη : η ⤳ q (IsLocalRing.closedPoint (CommRingCat.of k)))
    [IsDomain (T.presheaf.stalk (p (IsLocalRing.closedPoint (CommRingCat.of k))))]
    [UniqueFactorizationMonoid (T.presheaf.stalk (p (IsLocalRing.closedPoint (CommRingCat.of k))))]
    [IsDomain (T.presheaf.stalk (q (IsLocalRing.closedPoint (CommRingCat.of k))))]
    [UniqueFactorizationMonoid (T.presheaf.stalk (q (IsLocalRing.closedPoint (CommRingCat.of k))))]
    [IsDomain (T.presheaf.stalk η)] [UniqueFactorizationMonoid (T.presheaf.stalk η)]
    (ip iq : Q ⟶ Q') (ip' iq' : P ⟶ P') (sqp : IsPullback ip' π π' ip)
    (sqq : IsPullback iq' π π' iq)
    (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶ Q)
    (J : projectiveSpaceOver m T ⟶ Q')
    (hJp : projectiveSpaceOverMap m p ≫ J = j ≫ ip)
    (hJq : projectiveSpaceOverMap m q ≫ J = j ≫ iq)
    (L' : P'.Modules) (hL' : IsInvertible P'.presheaf P'.ringCatIsSheaf L')
    (hpL' : pullbackPicardClass ip' L' hL' = 0)
    (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (hqL' : pullbackPicardClass iq' L' hL' = P.picardClass L hL) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
    pullbackPicardClass j
        (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap L)
        (isInvertible_normInvertible π _ L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)) = 0 := by
  have := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
  have hinv : ∀ i' : P ⟶ P', IsInvertible P.presheaf P.ringCatIsSheaf
      ((modulePullback i'.toLRSHom.toShHom).obj L') := fun i' => by
    have := hL'; exact Stacks.RingedSpace.modulePullback_isInvertible _ L'
  let x := pullbackPicardHom J (normPicardClass π' d hd L' hL')
  have hfib : ∀ (t : Spec (CommRingCat.of k) ⟶ T) (it : Q ⟶ Q')
      (it' : P ⟶ P') (sq : IsPullback it' π π' it)
      (_ : projectiveSpaceOverMap m t ≫ J = j ≫ it),
      pullbackPicardHom (projectiveSpaceOverMap m t) x =
        pullbackPicardHom j (normPicardClass π d hd _ (hinv it')) := by
    intro t it it' sq ht
    rw [← pullbackPicardHom_comp_apply, ht, pullbackPicardHom_comp_apply,
      pullbackPicardHom_normPicardClass π π' d hd it it' sq L' hL']
  have hp0 : pullbackPicardHom (projectiveSpaceOverMap m p) x = 0 := by
    rw [hfib p ip ip' sqp hJp, normPicardClass_eq_zero π d hd _ _ hpL', map_zero]
  have hq1 : pullbackPicardHom (projectiveSpaceOverMap m q) x = 0 :=
    Stacks.PicardUFD.pullbackPicardHom_eq_zero_of_specializes m p q η hpη hqη x hp0
  have hq0 := hfib q iq iq' sqq hJq
  rw [hq1, normPicardClass_congr π d hd _ L _ hL hqL'] at hq0
  exact (pullbackPicardHom_picardClass j _ _).symm.trans hq0.symm

/-- **The norm sheaf is trivial on projective space, in the form of the source, over an arbitrary
base.** Let `π : P ⟶ Q` be finite locally free of rank `d > 0` over `k`, and let `T` be a scheme
over `k` with two `k`-points `p`, `q` having a common generization `η`, the local rings of `T` at
the three points being unique factorization domains. Let `ℒ'` be an invertible module on
`(T ×_k Q) ×_Q P = T ×_k P` whose fibre over `p` is trivial and whose fibre over `q` is `ℒ`. Then
for every morphism `j : ℙᵐ_k ⟶ Q` over `k`, `j^*(Norm_π ℒ)` is trivial. -/
theorem pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily_specializes {T : Scheme.{u}}
    (π : P ⟶ Q) (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank π d] (hd : 0 < d) (m : ℕ)
    (r : T ⟶ Spec (CommRingCat.of k))
    (p q : Spec (CommRingCat.of k) ⟶ T) (hp : p ≫ r = 𝟙 _) (hq : q ≫ r = 𝟙 _) (η : T)
    (hpη : η ⤳ p (IsLocalRing.closedPoint (CommRingCat.of k)))
    (hqη : η ⤳ q (IsLocalRing.closedPoint (CommRingCat.of k)))
    [IsDomain (T.presheaf.stalk (p (IsLocalRing.closedPoint (CommRingCat.of k))))]
    [UniqueFactorizationMonoid (T.presheaf.stalk (p (IsLocalRing.closedPoint (CommRingCat.of k))))]
    [IsDomain (T.presheaf.stalk (q (IsLocalRing.closedPoint (CommRingCat.of k))))]
    [UniqueFactorizationMonoid (T.presheaf.stalk (q (IsLocalRing.closedPoint (CommRingCat.of k))))]
    [IsDomain (T.presheaf.stalk η)] [UniqueFactorizationMonoid (T.presheaf.stalk η)]
    (sQ : Q ⟶ Spec (CommRingCat.of k))
    (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶ Q)
    (hj : j ≫ sQ = projectiveSpaceStructure m (Spec (CommRingCat.of k)))
    (L' : (pullback (pullback.snd r sQ) π).Modules)
    (hL' : IsInvertible (pullback (pullback.snd r sQ) π).presheaf
      (pullback (pullback.snd r sQ) π).ringCatIsSheaf L')
    (hpL' : pullbackPicardClass (sourceFibreInclusion r sQ π p hp) L' hL' = 0)
    (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (hqL' : pullbackPicardClass (sourceFibreInclusion r sQ π q hq) L' hL' =
      P.picardClass L hL) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
    pullbackPicardClass j
        (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap L)
        (isInvertible_normInvertible π _ L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)) = 0 := by
  have : Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst (pullback.snd r sQ) π) d :=
    Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd r sQ) π).flip
  exact pullbackPicardClass_normInvertible_eq_zero_of_family_specializes π
    (pullback.fst (pullback.snd r sQ) π) d hd m p q η hpη hqη
    (fibreInclusion r sQ p hp) (fibreInclusion r sQ q hq)
    (sourceFibreInclusion r sQ π p hp) (sourceFibreInclusion r sQ π q hq)
    (isPullback_sourceFibreInclusion r sQ π p hp) (isPullback_sourceFibreInclusion r sQ π q hq)
    j (familyMorphism m r sQ j hj)
    (projectiveSpaceOverMap_comp_familyMorphism m r sQ j hj p hp)
    (projectiveSpaceOverMap_comp_familyMorphism m r sQ j hj q hq) L' hL' hpL' L hL hqL'

end Stacks.Divisors

end
