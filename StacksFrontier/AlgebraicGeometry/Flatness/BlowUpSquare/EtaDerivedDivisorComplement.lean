module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedEmptySupport
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.DivisorRankStrata
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ModificationProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up complexes, III: the décalage over the complement of the divisor

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be a morphism along which the
pullback `D' = b⁻¹D` of the effective Cartier divisor is defined, and let
`Q = Lη_{ℐ'}Lb^*M` be the object of Stacks tag 0F8U.  Write `X ∖ D` for the complement of the
support of `D` and `j : b⁻¹(X ∖ D) ⟶ X'` for the inclusion of its preimage.  Then

`Lj^*Q ≅ L(b ∘ j)^*M`,

the restriction of `Q` to `b⁻¹(X ∖ D)` being the pullback of `M` itself.

In the graph construction of Stacks tag 0F90 the scheme is `𝐏¹_X`, the divisor is `(𝐏¹_X)_∞`,
the complement of its support is the chart `𝐀¹_X`, and `M = Lp^*E`; the displayed isomorphism is
clause (2) of that tag.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullback_etaDerivedPullbackObject`:
  **Stacks tag 0F9X at the pulled-back triple, for a flat morphism.**  For flat `k : Y ⟶ X'`
  the derived pullback of `Q` along `k` is the décalage of the twice-pulled-back object.
* `nonempty_etaDerivedPullbackRestrict_divisorComplement`, in the same namespace:
  **clause (2) of Stacks tag 0F90.**  The restriction of `Q` to the preimage of the complement
  of the divisor is the pullback of the object of the triple.

## Implementation notes

The three steps are the ones the source's proof of clause (2) quotes from Section 0F8R.

* Over the preimage of the complement the morphism `j` is an open immersion, hence flat, so the
  flat case of Stacks tag 0F9X applies — that is
  `AlgebraicGeometry.ComplexAndDivisorSituation.derivedEtaPullbackIso`, used here at the triple
  `(X', b⁻¹D, Lb^*M)` rather than at `(X, D, M)`.  Its statement is written at
  `AlgebraicGeometry.ComplexAndDivisorSituation.standardObject`, which transports the object of
  the triple into the standard model of the derived category; that transport is the canonical
  equivalence of a localization with itself and is undone by
  `CategoryTheory.Localization.isoUniqFunctor`, exactly as in
  `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullbackObject_comp`.
* The divisor pulled back to the preimage of the complement has no points, so its ideal
  inclusion is invertible and the décalage by it is the identity functor:
  `Stacks.Divisors.Eta.derivedEtaIsoId_of_supportSet_eq_empty`.
* Pulling back along `j` and then along `b` is pulling back along `b ∘ j`:
  `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullbackObject_comp`.

The conclusions are `Nonempty` of an isomorphism rather than a chosen isomorphism, following
`AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_etaDerivedPullbackObject_comp`: the
presentation of the object by a complex of torsion-free modules that the flat case of tag 0F9X
consumes is produced by an existence statement, so no isomorphism is canonical here.

## References

* [Stacks Project, Tag 0F90](https://stacks.math.columbia.edu/tag/0F90)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F9Y](https://stacks.math.columbia.edu/tag/0F9Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.ComplexAndDivisorSituation.isEffectiveCartierDivisor

/-- **Stacks tag 0F9X at the pulled-back triple, for a flat morphism.**  Let `(X, D, M)` be a
triple as in Situation 0F8S, let `b : X' ⟶ X` be a morphism along which `D' = b⁻¹D` is defined
and let `Q = Lη_{ℐ'}Lb^*M`.  For a flat `k : Y ⟶ X'` along which `D'` pulls back,

`Lk^*Q ≅ Lη_{k⁻¹D'} Lk^* Lb^* M`.

The object of the pulled-back triple and its transport into the standard model of the derived
category differ by the canonical equivalence of a localization with itself, which is undone
here; apart from that this is
`AlgebraicGeometry.ComplexAndDivisorSituation.derivedEtaPullbackIso` at that triple. -/
theorem nonempty_derivedPullback_etaDerivedPullbackObject
    (S : ComplexAndDivisorSituation.{u, d}) {X' Y : Scheme.{u}} (b : X' ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined b S.D) (k : Y ⟶ X') [AlgebraicGeometry.Flat k]
    (hk : Stacks.Divisors.IsPullbackDefined k (S.D.comap b)) :
    Nonempty ((derivedPullback k.toLRSHom.toShHom).obj (S.etaDerivedPullbackObject b hD) ≅
      (S.pullback b hD).etaDerivedPullbackObject k hk) := by
  have hk' : Stacks.Divisors.IsPullbackDefined k (S.pullback b hD).D := hk
  have hflat : AlgebraicGeometry.Flat (show Y ⟶ (S.pullback b hD).X from k) :=
    ‹AlgebraicGeometry.Flat k›
  have hE : (𝟭 (DerivedCategory (OXMod.{u, u} X'.toRingedSpace))) ≅
      (Localization.uniq (DerivedCategory.Q (C := OXMod.{u, u} X'.toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} X'.toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} X'.toRingedSpace)
          (ComplexShape.up ℤ))).functor :=
    Localization.isoUniqFunctor _ _ _ (𝟭 _) (Functor.rightUnitor _)
  obtain ⟨K, ⟨hKM⟩⟩ := Stacks.Divisors.Eta.exists_torsionFreeComplex_iso (S.D.comap b)
    (S.pullback b hD).standardObject
  exact ⟨(derivedPullback k.toLRSHom.toShHom).mapIso
      ((Stacks.Divisors.Eta.derivedEtaData (S.D.comap b)).functor.mapIso
        (hE.app (S.derivedPullbackObject b))) ≪≫
    @AlgebraicGeometry.ComplexAndDivisorSituation.derivedEtaPullbackIso
      (S.pullback b hD) Y k hflat hk' K hKM⟩

/-- **Clause (2) of Stacks tag 0F90.**  Let `(X, D, M)` be a triple as in Situation 0F8S, let
`b : X' ⟶ X` be a morphism along which `D' = b⁻¹D` is defined, and let `Q = Lη_{ℐ'}Lb^*M` be the
object of Stacks tag 0F8U.  The restriction of `Q` to the preimage of the complement `X ∖ D` of
the support of the divisor is the pullback of `M`:

`Lj^*Q ≅ L(b ∘ j)^*M`, where `j : b⁻¹(X ∖ D) ⟶ X'`.

In the graph construction the scheme is `𝐏¹_X`, the divisor is `(𝐏¹_X)_∞`, the complement of its
support is the chart `𝐀¹_X`, and the object of the triple is `Lp^*E`; so the displayed
isomorphism says that the restriction of `Q` to `𝐀¹_X` is the pullback of `E`.  The morphism `b`
is arbitrary: nothing beyond the definedness of `b⁻¹D` is asked of it, so the statement holds
in particular for the morphism of Stacks tag 0GTY, `goodBlowupToBase`; the graph construction
itself is `Stacks.Chow.graphTriple` in `GraphConstructionTriple.lean`. -/
@[stacks 0F90 "clause (2): the restriction of Q to A^1_X is the pullback of E"]
theorem nonempty_etaDerivedPullbackRestrict_divisorComplement
    (S : ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined b S.D) :
    Nonempty (S.etaDerivedPullbackRestrict b hD (b ⁻¹ᵁ S.divisorComplement).ι ≅
      S.derivedPullbackObject ((b ⁻¹ᵁ S.divisorComplement).ι ≫ b)) := by
  have hempty : ((S.D.comap b).comap (b ⁻¹ᵁ S.divisorComplement).ι).supportSet = ∅ := by
    rw [← Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.Eta.supportSet_comap_eq_empty S.D _ fun y =>
      Scheme.IdealSheafData.mem_supportSet_iff_mem_support.not.2 y.2
  have hk : Stacks.Divisors.IsPullbackDefined (b ⁻¹ᵁ S.divisorComplement).ι (S.D.comap b) :=
    Stacks.Divisors.isEffectiveCartierDivisor_of_supportSet_eq_empty _ fun y => by
      rw [hempty]; exact Set.notMem_empty y
  obtain ⟨e₁⟩ := S.nonempty_derivedPullback_etaDerivedPullbackObject b hD
    (b ⁻¹ᵁ S.divisorComplement).ι hk
  obtain ⟨e₃⟩ := S.nonempty_derivedPullbackObject_comp b hD (b ⁻¹ᵁ S.divisorComplement).ι
  exact ⟨e₁ ≪≫ (Stacks.Divisors.Eta.derivedEtaIsoId_of_supportSet_eq_empty
    ((S.D.comap b).comap (b ⁻¹ᵁ S.divisorComplement).ι) hempty).app _ ≪≫ e₃⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
