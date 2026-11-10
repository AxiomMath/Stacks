module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothRigSurjectiveClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveRigEtaleDiagonal

/-!
# Artin's conditions on a formal modification

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0GDL** recalls Artin's
Definition 1.7 of a formal modification — a proper morphism `f : X ⟶ Y` of locally Noetherian
formal algebraic spaces such that (i) the Cramer and the Jacobian ideal of `f` each contain an
ideal of definition of `X`, (ii) the ideal cutting out the relative diagonal
`Δ_f : X ⟶ X ×_Y X` is annihilated by an ideal of definition, and (iii) every adic morphism
`Spf R ⟶ Y` with `R` a complete discrete valuation ring lifts to `X` — and compares those
conditions with the ones of Definition 0GDK
(`AlgebraicGeometry.FormalSpace.IsFormalModification`), namely rig-étaleness of `f`,
rig-surjectivity of `f` and rig-surjectivity of `Δ_f`. The remark's three assertions are that
condition (i) is equivalent to rig-étaleness of `f`, that for rig-étale `f` condition (ii) is
equivalent to rig-surjectivity of `Δ_f`, and that condition (iii), which lifts an adic point
over `R` itself rather than over an extension of `R`, agrees with rig-surjectivity of `f` once
(i) and (ii) hold.

The one implication of the remark that holds with no further input is the comparison in the
direction of Definition 0GDK: a lift over `R` itself is a lift over the trivial extension of
`R`, so Artin's condition (iii) implies rig-surjectivity of `f`, and a proper rig-étale `f`
with rig-surjective relative diagonal satisfying condition (iii) is a formal modification in
the sense of Definition 0GDK. This is
`AlgebraicGeometry.FormalSpace.isFormalModification_of_factorsAdicCompleteDvrPoints`.

Artin's condition (ii) is read here as condition (3) of Stacks 0GD6 for `Δ_f`
(`AlgebraicGeometry.FormalSpace.HasAnnihilatedKerOnPullbackCharts`), that on every affine
representable étale chart of `X ×_Y X` the diagonal is given by a surjection of `WAdm^{Noeth}`
whose kernel is annihilated by an ideal of definition of the source, and his condition (iii) as
`AlgebraicGeometry.FormalSpace.FactorsAdicCompleteDvrPoints`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalModification_of_factorsAdicCompleteDvrPoints`: Artin's
  conditions, in the translated form the remark gives them, imply Definition 0GDK.

## Implementation notes

The remaining statements of the remark appear below in the shape in which the inputs this
library lacks would give them. Each assumes a condition that this library states and does not
prove, so none of them is a formalization of the remark.

* `AlgebraicGeometry.FormalSpace.isRigEtale_diagonal_of_isRigEtale` is the first half of the
  remark's second assertion, that `Δ_f` is rig-étale when `f` is. The two inputs of the
  library's Stacks 0GD3 (`AlgebraicGeometry.FormalSpace.isRigEtale_of_comp`), the form of
  Stacks 0GD1 carried by
  `AlgebraicGeometry.FormalSpace.RigEtaleIsStableUnderRepresentableBaseChange`, and Stacks 0AQ8
  in the form carried by `AlgebraicGeometry.FormalSpace.FibreProductIsLocallyNoetherian`, are
  all hypotheses. Representability by algebraic spaces and local finite typeness of `f` are
  hypotheses too, but these two the properness of Artin's `f` supplies, by
  `AlgebraicGeometry.FormalSpace.IsProper.isRepresentable` and
  `AlgebraicGeometry.FormalSpace.IsProper.isLocallyOfFiniteType`.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_diagonal_iff_hasAnnihilatedKer` is the second
  half of that assertion. It restates the library's Stacks 0GD6
  (`AlgebraicGeometry.FormalSpace.isRigSmooth_and_isRigSurjective_tfae_of_isClosedImmersion'`)
  at `Δ_f`, and so has the hypothesis of Stacks 0GD6 that the morphism be a closed immersion.
  The latter is separatedness of `f`, which for
  a proper morphism of formal algebraic spaces no declaration of this library proves.
* `AlgebraicGeometry.FormalSpace.factorsAdicCompleteDvrPoints_iff_isRigSurjective_of_isProper`
  is the third assertion. It restates the library's Stacks 0GDA
  (`AlgebraicGeometry.FormalSpace.isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_diagonal`)
  for a proper morphism, so it has that lemma's five hypotheses; properness discharges its
  local finite typeness hypothesis.

The remark's first assertion is not treated at all: this library has neither the Cramer nor the
Jacobian ideal of a morphism of formal algebraic spaces, and the equivalence of condition (i)
with rig-étaleness that the remark cites for it — part (7) of Lemma 0AJU, that is Stacks 0AJY —
is not proved here.

## References

* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GD3](https://stacks.math.columbia.edu/tag/0GD3)
* [Stacks Project, Tag 0GD6](https://stacks.math.columbia.edu/tag/0GD6)
* [Stacks Project, Tag 0GDA](https://stacks.math.columbia.edu/tag/0GDA)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
* [Stacks Project, Tag 0GDL](https://stacks.math.columbia.edu/tag/0GDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Artin's conditions imply Definition 0GDK -/

/-- **Stacks 0GDL.** Let `f : X ⟶ Y` be a proper rig-étale morphism of locally Noetherian
formal algebraic spaces over `S` whose relative diagonal `Δ_f : X ⟶ X ×_Y X` is rig-surjective.
If every adic morphism `Spf R ⟶ Y` with `R` a complete discrete valuation ring factors through
`f` over `R` itself, then `f` is a formal modification in the sense of Definition 0GDK: such a
factorisation is in particular one over the trivial extension of `R`, so `f` is
rig-surjective. -/
@[stacks 0GDL "the implication of Ad (iii) that needs no further input: Artin's condition \
(iii), a lift of every adic point over the complete discrete valuation ring itself, implies \
rig-surjectivity, which asks only for a lift over an extension of that ring. Together with \
the remaining conditions of Artin's Definition 1.7 in the translated form the remark gives \
them — properness, rig-étaleness for condition (i) by Ad (i), and rig-surjectivity of the \
relative diagonal for condition (ii) by Ad (ii) — this is the comparison with Definition \
0GDK. Not covered: the converse implication of Ad (iii), which the remark obtains from Stacks \
0GDA; the two implications of Ad (ii), which it obtains from Stacks 0GD1, Stacks 0GD3 and \
Stacks 0GD6; and Ad (i), whose equivalence of condition (i) with rig-étaleness is part (7) of \
Lemma 0AJU, that is Stacks 0AJY, and whose Cramer and Jacobian ideals of a morphism of formal \
algebraic spaces this library does not have"]
theorem isFormalModification_of_factorsAdicCompleteDvrPoints {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hproper : IsProper B S hS f) (hetale : IsRigEtale B S hS f)
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal f))
    (hlift : FactorsAdicCompleteDvrPoints B S hS f) :
    IsFormalModification B S hS f where
  isLocallyNoetherian_source := hX
  isLocallyNoetherian_target := hY
  isProper := hproper
  isRigEtale := hetale
  isRigSurjective := isRigSurjective_of_factorsAdicCompleteDvrPoints B S hS f hlift
  isRigSurjective_diagonal := hdiagSurj

/-! ### Ad (ii): the relative diagonal of a rig-étale morphism -/

/-- The first half of Ad (ii) of Stacks 0GDL, on the hypotheses `hcond`, `htransfer`, `h0AQ8`
and `h0GD1`, which this library states and does not prove. Let `f : X ⟶ Y` be a rig-étale
morphism of locally Noetherian formal algebraic spaces over `S`, representable by algebraic
spaces and locally of finite type. Then the relative diagonal `Δ_f : X ⟶ X ×_Y X` is rig-étale:
both `𝟙 X` and the first projection `pr₁ : X ×_Y X ⟶ X` are rig-étale, the first by cancelling
`f` out of `𝟙 X ≫ f` and the second as a base change of `f`, so rig-étaleness of `Δ_f` is
cancellation of `pr₁` out of `Δ_f ≫ pr₁ = 𝟙 X`. -/
theorem isRigEtale_diagonal_of_isRigEtale
    (hcond : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ))
    (htransfer : TransfersCancellationOnAffineEtaleDiagrams B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hft : IsLocallyOfFiniteType B S hS f)
    (h0AQ8 : FibreProductIsLocallyNoetherian B S hS)
    (h0GD1 : RigEtaleIsStableUnderRepresentableBaseChange B S hS)
    (hf : IsRigEtale B S hS f) :
    IsRigEtale B S hS (pullback.diagonal f) := by
  have sq : IsPullback (pullback.fst f f) (pullback.snd f f) f f := IsPullback.of_hasPullback f f
  have hXX : IsLocallyNoetherian B S hS (pullback f f) := h0AQ8 sq hX hft
  have hid : IsRigEtale B S hS (𝟙 X) :=
    isRigEtale_of_comp B S hS hcond htransfer (𝟙 X) f hX hX hY (by rwa [Category.id_comp]) hf
  have hfst : IsRigEtale B S hS (pullback.fst f f) := h0GD1 sq hrep hX hY hX hf
  refine isRigEtale_of_comp B S hS hcond htransfer (pullback.diagonal f) (pullback.fst f f)
    hX hXX hX ?_ hfst
  rw [pullback.diagonal_fst]
  exact hid

/-- The second half of Ad (ii) of Stacks 0GDL, on the hypothesis `hdiagClosed`, which this
library states and does not prove. Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over
`S` whose relative diagonal `Δ_f : X ⟶ X ×_Y X` is a
rig-étale closed immersion, with `X` and `X ×_Y X` locally Noetherian. Then Artin's
condition (ii), that on every affine representable étale chart of `X ×_Y X` the diagonal be a
surjection of `WAdm^{Noeth}` whose kernel is annihilated by an ideal of definition of the
source, holds if and only if `Δ_f` is rig-surjective. -/
theorem isRigSurjective_diagonal_iff_hasAnnihilatedKer' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X)
    (hXX : IsLocallyNoetherian B S hS (pullback f f))
    (hdiagClosed : IsClosedImmersion B S hS (pullback.diagonal f))
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal f)) :
    HasAnnihilatedKerOnPullbackCharts B S hS (pullback.diagonal f) ↔
      IsRigSurjective B S hS (pullback.diagonal f) := by
  have h0GD6 := isRigSmooth_and_isRigSurjective_tfae_of_isClosedImmersion' B S hS
    (pullback.diagonal f) hX hXX hdiagClosed
  refine ⟨fun hker ↦ ?_, fun hsurj ↦ ?_⟩
  · have h : IsRigEtale B S hS (pullback.diagonal f) ∧
        IsRigSurjective B S hS (pullback.diagonal f) := (h0GD6.out 3 2).mp hker
    exact h.2
  · have h : IsRigEtale B S hS (pullback.diagonal f) ∧
        IsRigSurjective B S hS (pullback.diagonal f) := ⟨hdiagEtale, hsurj⟩
    exact (h0GD6.out 2 3).mp h

/-- The second half of Ad (ii) of Stacks 0GDL. The library's Stacks 0GD6 needs neither the chart
condition of Stacks 0AQI nor Stacks 0AR0, so this has the same hypotheses as
`isRigSurjective_diagonal_iff_hasAnnihilatedKer'`. -/
theorem isRigSurjective_diagonal_iff_hasAnnihilatedKer {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X)
    (hXX : IsLocallyNoetherian B S hS (pullback f f))
    (hdiagClosed : IsClosedImmersion B S hS (pullback.diagonal f))
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal f)) :
    HasAnnihilatedKerOnPullbackCharts B S hS (pullback.diagonal f) ↔
      IsRigSurjective B S hS (pullback.diagonal f) :=
  isRigSurjective_diagonal_iff_hasAnnihilatedKer' B S hS f hX hXX hdiagClosed hdiagEtale

/-! ### Ad (iii): lifting adic points over the ring itself -/

/-- Ad (iii) of Stacks 0GDL, on the hypotheses `h0AQ8`, `h0GD1`, `hSpfNoeth`, `hextFlat` and
`h0GD9`, which this library states and does not prove. Let `f : X ⟶ Y` be a proper morphism of
locally Noetherian formal algebraic spaces over `S` whose relative diagonal `Δ_f : X ⟶ X ×_Y X`
is rig-étale and rig-surjective. Then Artin's condition (iii), that every adic morphism
`Spf R ⟶ Y` with `R` a complete discrete valuation ring factor through `f` over `R` itself,
holds if and only if `f` is rig-surjective, which asks only for a factorisation over an
extension of `R`. -/
theorem factorsAdicCompleteDvrPoints_iff_isRigSurjective_of_isProper
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hproper : IsProper B S hS f)
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal f))
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal f))
    (h0AQ8 : FibreProductIsLocallyNoetherian B S hS)
    (h0GD1 : RigEtaleIsStableUnderRepresentableBaseChange B S hS)
    (hSpfNoeth : FormalSpectrumOfCompleteDvrIsLocallyNoetherian B S hS)
    (hextFlat : FormalSpectrumMapOfDvrExtensionIsFlat B S hS)
    (h0GD9 : FlatPartOfRigEtaleDiagonalIsBaseOrPointless B S hS) :
    FactorsAdicCompleteDvrPoints B S hS f ↔ IsRigSurjective B S hS f :=
  (isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_diagonal B S hS f hX hY
    (IsProper.isLocallyOfFiniteType B S hS hproper) hdiagEtale hdiagSurj h0AQ8 h0GD1
    hSpfNoeth hextFlat h0GD9).symm

end AlgebraicGeometry.FormalSpace

end
