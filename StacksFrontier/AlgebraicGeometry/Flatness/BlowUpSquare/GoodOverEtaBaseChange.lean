module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up complexes, II: base change of the décalage along a morphism to the modification

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be a morphism with the two
properties of Stacks tag 0GTY, and let `Q = Lη_{ℐ'} Lb^*M` be the perfect object of tag 0F8U.
Let `h : Y ⟶ X` be good for the triple, so that `E = h⁻¹D` is defined and `(Y, E, Lh^*M)` is a
good triple.  The last assertion of Stacks tag 0F8V says that the unique `k : Y ⟶ X'` with
`h = b ∘ k` satisfies

`Lη_𝒥 Lh^*M = Lk^* Q`,

where `𝒥 ⊂ 𝒪_Y` is the ideal sheaf of `E`.

That assertion is proved, unconditionally, in `GoodOverEtaBaseChangeGeneral.lean`, as
`ComplexAndDivisorSituation.exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver`.
This file supplies the bookkeeping that the source performs silently: that pulling the triple
back along `b` and then along `k` gives the same object of the derived category as pulling it
back along `b ∘ k` in one step, and that the two resulting divisors are the *same* ideal sheaf,
not merely isomorphic ones.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullbackObject_comp`:
  `L k^*(Lb^*M) ≅ L(b ∘ k)^*M`, i.e. the object of the triple pulled back in two steps agrees
  with the object of the triple pulled back in one.
* `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_etaDerivedPullbackObject_comp`: the
  same for the décalage, `Lη_{(b⁻¹D)⁻¹ along k}(Lk^*Lb^*M) ≅ Lη_{(b ∘ k)⁻¹D}(L(b ∘ k)^*M)`.

## Implementation notes

The two pulled-back objects are compared, not proved equal, because
`AlgebraicGeometry.ComplexAndDivisorSituation.derivedPullbackObject` transports the situation's
object to the standard model of the derived category before pulling it back, so the two-step
pullback applies that transport twice.  The second application is the canonical equivalence
between one localization and itself, which is isomorphic to the identity by
`CategoryTheory.Localization.isoUniqFunctor` at the right unitor; the two pullbacks are then
composed by `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, which holds
for arbitrary composable morphisms of ringed spaces with no K-flatness datum left over.

The divisors, by contrast, are genuinely *equal*: `AlgebraicGeometry.Scheme.IdealSheafData`
`.comap_comp` is an equality of ideal sheaf data, so the two décalage functors in play are the
same functor and the comparison is `subst` followed by the functor's action on the isomorphism
of objects.  `Stacks.Divisors.IsEffectiveCartierDivisor` is a `Prop`, so the two proofs of it
that the two sides carry need no reconciliation.

The lift `k` is produced by condition (2) of tag 0GTY, `IsGoodBlowup.existsUnique_lift`, and is
therefore existentially quantified in the conclusion rather than taken as an argument; its
uniqueness is that same statement and is not restated.

## References

* [Stacks Project, Tag 0F8V](https://stacks.math.columbia.edu/tag/0F8V)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-- The derived décalage of an effective Cartier divisor depends on the divisor only through
the ideal sheaf data, so equal data with isomorphic arguments give isomorphic values.  The two
proofs that the data are effective Cartier need no reconciliation, that being a `Prop`. -/
private theorem nonempty_derivedEtaData_obj_congr {X' : Scheme.{u}}
    {A A' : X'.IdealSheafData} (hA : A = A')
    (iA : Stacks.Divisors.IsEffectiveCartierDivisor A)
    (iA' : Stacks.Divisors.IsEffectiveCartierDivisor A')
    {Z Z' : DerivedCategory X'.Modules} (e : Z ≅ Z') :
    Nonempty ((@Stacks.Divisors.Eta.derivedEtaData X' A iA).functor.obj Z ≅
      (@Stacks.Divisors.Eta.derivedEtaData X' A' iA').functor.obj Z') := by
  subst hA
  exact ⟨(@Stacks.Divisors.Eta.derivedEtaData X' A iA).functor.mapIso e⟩

/-- **Pulling the object of a triple back in two steps agrees with pulling it back in one.**
For `b : X' ⟶ X` along which `b⁻¹D` is defined and `k : Y ⟶ X'`, the object of the triple
`(X', b⁻¹D, Lb^*M)` pulled back along `k` is isomorphic to the object of `(X, D, M)` pulled back
along `b ∘ k`.

The outer transport to the standard model of the derived category is the canonical equivalence
of a localization with itself, hence isomorphic to the identity, and the two derived pullbacks
compose by `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`. -/
theorem nonempty_derivedPullbackObject_comp (S : ComplexAndDivisorSituation.{u, d})
    {X' Y : Scheme.{u}} (b : X' ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined b S.D)
    (k : Y ⟶ X') :
    Nonempty ((S.pullback b hD).derivedPullbackObject k ≅
      S.derivedPullbackObject (k ≫ b)) := by
  have hE : (𝟭 (DerivedCategory (OXMod.{u, u} X'.toRingedSpace))) ≅
      (Localization.uniq (DerivedCategory.Q (C := OXMod.{u, u} X'.toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} X'.toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} X'.toRingedSpace)
          (ComplexShape.up ℤ))).functor :=
    Localization.isoUniqFunctor _ _ _ (𝟭 _) (Functor.rightUnitor _)
  exact ⟨(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      k.toLRSHom.toShHom).mapIso (hE.symm.app (S.derivedPullbackObject b)) ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      k.toLRSHom.toShHom b.toLRSHom.toShHom).app _⟩

/-- **The same, for the décalage.**  The divisor pulled back along `b` and then along `k` is the
divisor pulled back along `b ∘ k` — an equality of ideal sheaf data, by
`AlgebraicGeometry.Scheme.IdealSheafData.comap_comp` — so the two décalages are the same functor
and the comparison is its action on
`AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullbackObject_comp`. -/
theorem nonempty_etaDerivedPullbackObject_comp (S : ComplexAndDivisorSituation.{u, d})
    {X' Y : Scheme.{u}} (b : X' ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined b S.D)
    (k : Y ⟶ X') (hk : Stacks.Divisors.IsPullbackDefined k (S.D.comap b))
    (hkb : Stacks.Divisors.IsPullbackDefined (k ≫ b) S.D) :
    Nonempty ((S.pullback b hD).etaDerivedPullbackObject k hk ≅
      S.etaDerivedPullbackObject (k ≫ b) hkb) :=
  nonempty_derivedEtaData_obj_congr (Scheme.IdealSheafData.comap_comp S.D k b).symm hk hkb
    (S.nonempty_derivedPullbackObject_comp b hD k).some

end AlgebraicGeometry.ComplexAndDivisorSituation

end
