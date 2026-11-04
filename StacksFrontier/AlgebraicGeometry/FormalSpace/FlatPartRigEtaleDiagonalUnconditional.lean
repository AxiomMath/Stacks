module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartRigEtaleDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartRigEtaleDiagonalDichotomy
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleAdicMonomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocallyNoetherianSource

/-!
# The flat part of a formal algebraic space with rig-étale rig-surjective diagonal (Stacks 0GD9)

Let `A` be a complete discrete valuation ring and let `X` be a locally Noetherian formal algebraic
space which is locally of finite type over `A`, with structure morphism `p : X ⟶ Spf A`. Let
`ι : X' ⟶ X` be the flat part of Stacks 0GD8. **Stacks 0GD9** says that if the relative diagonal
`X ⟶ X ×_{Spf A} X` is rig-étale and rig-surjective then `X' = Spf A` or `X' = ∅`.

The diagonal of `X'` over `A` is a base change of that of `X` along the comparison
`X' ×_{Spf A} X' ⟶ X ×_{Spf A} X`, `ι` being a monomorphism, so it is rig-étale (Stacks 0GD1) and
rig-surjective (Stacks 0AQS). The dichotomy for `X'` is then
`isIso_or_isInitial_of_isFlat_of_isRigEtale_of_isRigSurjective_diagonal`.

## Main results

* `isIso_or_isInitial_flatPart_of_isRigEtale_of_isRigSurjective_diagonal`, in the namespace
  `AlgebraicGeometry.FormalSpace`: **Stacks 0GD9**.

## Implementation notes

The source argues that `U ×_{X'} U ⟶ U ×_{Spf A} U` is a closed immersion for an affine chart `U`
of `X'`, and applies Stacks 0GD6 to it. That step needs `X'` separated over `A`, which is not
available at that point. The proof here replaces it: the kernel of the diagonal of each chart is
idempotent (rig-étaleness of the diagonal gives a conormal module killed by a power of the
uniformizer, rig-surjectivity kills the kernel at every adic point of a complete discrete
valuation ring reducing into the diagonal), so the charts are étale over `Spf A`, the comparison
`U ×_{X'} V ⟶ U ×_{Spf A} V` is representable étale, and rig-surjectivity makes it surjective on
points; see `StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartRigEtaleDiagonalCharts`,
`…Etale`, `…Mono` and `…Dichotomy`.

"`X' = Spf A`" is `IsIso (ι ≫ p)` and "`X' = ∅`" is `Nonempty (IsInitial X')`. The topology of
`A` is its maximal-adic topology. The flat part is quantified over: the statement is made for
every closed immersion `ι : X' ⟶ X` with what Stacks 0GD8 concludes, `X'` locally Noetherian and
flat over `A` with the universal property; the universal property is not used.

## References

* [Stacks Project, Tag 0GD9](https://stacks.math.columbia.edu/tag/0GD9)
* [Stacks Project, Tag 0GD8](https://stacks.math.columbia.edu/tag/0GD8)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map `X' ×_Z Y' ⟶ X ×_Z Y` induced by adic morphisms `X' ⟶ X` and `Y' ⟶ Y` over `Z` is
adic: it is the composite of a base change of each. -/
theorem isAdicMorphism_pullback_map {X Y Z X' Y' : FppfSheaf B S hS} (f : X ⟶ Z) (g : Y ⟶ Z)
    {a : X' ⟶ X} {b : Y' ⟶ Y} (ha : IsAdicMorphism B S hS a) (hb : IsAdicMorphism B S hS b) :
    IsAdicMorphism B S hS
      (pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 Z) (by simp) (by simp)) := by
  let m₁ : pullback (a ≫ f) (b ≫ g) ⟶ pullback f (b ≫ g) :=
    pullback.map (a ≫ f) (b ≫ g) f (b ≫ g) a (𝟙 _) (𝟙 Z) (by simp) (by simp)
  let m₂ : pullback f (b ≫ g) ⟶ pullback f g :=
    pullback.map f (b ≫ g) f g (𝟙 _) b (𝟙 Z) (by simp) (by simp)
  have hm : pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 Z) (by simp) (by simp) = m₁ ≫ m₂ :=
    pullback.hom_ext (by simp [m₁, m₂]) (by simp [m₁, m₂])
  have hsq₁ : IsPullback m₁ (pullback.fst (a ≫ f) (b ≫ g)) (pullback.fst f (b ≫ g)) a := by
    refine IsPullback.of_right ?_ (by simp [m₁]) (IsPullback.of_hasPullback f (b ≫ g)).flip
    rw [show m₁ ≫ pullback.snd f (b ≫ g) = pullback.snd (a ≫ f) (b ≫ g) by simp [m₁]]
    exact (IsPullback.of_hasPullback (a ≫ f) (b ≫ g)).flip
  have hsq₂ : IsPullback (pullback.snd f (b ≫ g)) m₂ b (pullback.snd f g) := by
    refine (IsPullback.of_right ?_ (by simp [m₂]) (IsPullback.of_hasPullback f g)).flip
    rw [show m₂ ≫ pullback.fst f g = pullback.fst f (b ≫ g) by simp [m₂]]
    exact IsPullback.of_hasPullback f (b ≫ g)
  rw [hm]
  exact IsAdicMorphism.comp B S hS _ _ (IsAdicMorphism.of_isPullback B S hS hsq₁ ha)
    (IsAdicMorphism.of_isPullback B S hS hsq₂.flip hb)

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (D : QuotientSystem B S hS A)

/-- **Stacks 0GD9.** Let `A` be a complete discrete valuation ring, carrying its `𝔪`-adic
topology, let `X` be a locally Noetherian formal algebraic space over `S` with a structure
morphism `p : X ⟶ Spf A` locally of finite type, and let `ι : X' ⟶ X` be as in Stacks 0GD8: a
closed immersion with `X'` flat over `A` through which every morphism `Y ⟶ X` from a locally
Noetherian formal algebraic space flat over `A` factors. If the relative diagonal
`X ⟶ X ×_{Spf A} X` is rig-étale and rig-surjective, then `X' = Spf A` or `X' = ∅`: the
structure morphism `ι ≫ p` of `X'` is an isomorphism, or `X'` is initial.

`X'` is locally Noetherian, being locally of finite type over `X` (Stacks 0AQ7). The relative
diagonal of `ι ≫ p` is the base change of that of `p` along the adic comparison
`X' ×_{Spf A} X' ⟶ X ×_{Spf A} X`, `ι` being a monomorphism, so it is rig-étale (Stacks 0GD1) and
rig-surjective (Stacks 0AQS), and
`isIso_or_isInitial_of_isFlat_of_isRigEtale_of_isRigSurjective_diagonal` applies to `ι ≫ p`. -/
@[stacks 0GD9]
theorem isIso_or_isInitial_flatPart_of_isRigEtale_of_isRigSurjective_diagonal
    [IsDomain A] [IsDiscreteValuationRing A]
    (hAadic : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    {X X' : FppfSheaf B S hS} (hX : IsLocallyNoetherian B S hS X) (p : X ⟶ formalSpectrum D)
    (hp : IsLocallyOfFiniteType B S hS p) (ι : X' ⟶ X) (hιclosed : IsClosedImmersion B S hS ι)
    (hX'flat : IsFlat B S hS (ι ≫ p))
    (_hX'univ : ∀ (Y : FppfSheaf B S hS) (q : Y ⟶ X), IsLocallyNoetherian B S hS Y →
      IsFlat B S hS (q ≫ p) → ∃ r : Y ⟶ X', r ≫ ι = q)
    (hdiagE : IsRigEtale B S hS (pullback.diagonal p))
    (hdiagS : IsRigSurjective B S hS (pullback.diagonal p)) :
    IsIso (ι ≫ p) ∨ Nonempty (IsInitial X') := by
  let : IsLinearTopology A A := hAadic ▸ Ideal.isLinearTopology _
  have : Mono ι := mono_of_isClosedImmersion B S hS ι hιclosed
  have hιlft : IsLocallyOfFiniteType B S hS ι :=
    IsLocallyOfFiniteType.of_isClosedImmersion B S hS ι hιclosed
  have hX'fas : IsFormalAlgebraicSpace B S hS X' :=
    isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift B S hS ι hX.1 hιclosed.1
  have hX' : IsLocallyNoetherian B S hS X' :=
    isLocallyNoetherian_source_of_isLocallyOfFiniteType' B S hS ι hX'fas hX hιlft
  have hq : IsLocallyOfFiniteType B S hS (ι ≫ p) := IsLocallyOfFiniteType.comp B S hS ι p hιlft hp
  have hSpf : IsFormalAlgebraicSpace B S hS (formalSpectrum D) :=
    isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS
      (isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS
        (topologicalRingIsAdic_of_isAdic_of_isAdicComplete hAadic hAc) D (Iso.refl _))
  have hXX : IsLocallyNoetherian B S hS (pullback p p) :=
    isLocallyNoetherian_of_isPullback' B S hS (IsPullback.of_hasPullback p p) hX.1 hSpf hX hp
  have hX'X' : IsLocallyNoetherian B S hS (pullback (ι ≫ p) (ι ≫ p)) :=
    isLocallyNoetherian_of_isPullback' B S hS (IsPullback.of_hasPullback (ι ≫ p) (ι ≫ p)) hX'fas
      hSpf hX' hq
  -- the diagonal of `X'` is a base change of that of `X` along an adic morphism
  have sq := isPullback_diagonal_comp_of_mono ι p
  have hsm : IsAdicMorphism B S hS (selfProductMap ι p) :=
    isAdicMorphism_pullback_map B S hS p p hιclosed.1 hιclosed.1
  have hE : IsRigEtale B S hS (pullback.diagonal (ι ≫ p)) := by
    have h := isRigEtale_iso_hom_comp B S hS sq.isoPullback _
      (isRigEtale_pullback_snd_of_isLocallyNoetherian B S hS (pullback.diagonal p)
        (selfProductMap ι p) hX hXX hX'X' hdiagE hsm)
    rwa [sq.isoPullback_hom_snd] at h
  exact isIso_or_isInitial_of_isFlat_of_isRigEtale_of_isRigSurjective_diagonal B S hS D hAadic hAc
    (ι ≫ p) hX' hq hX'flat hE
    (IsRigSurjective.of_isPullback_of_representable B S hS sq.flip hsm hdiagS)

end AlgebraicGeometry.FormalSpace

end
