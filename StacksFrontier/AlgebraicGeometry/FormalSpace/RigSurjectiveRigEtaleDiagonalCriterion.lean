module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherianRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvrFull
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartRigEtaleDiagonalUnconditional
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumMapFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumNotInitial
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleAdicMonomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveRigEtaleDiagonal

/-!
# The lifting criterion for rig-surjectivity under a rig-étale, rig-surjective diagonal

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` with `X` and `Y` locally Noetherian, `f` locally of finite
type, and the relative diagonal `Δ_f : X ⟶ X ×_Y X` rig-étale and rig-surjective. **Stacks
0GDA** says that `f` is rig-surjective if and only if every adic morphism `Spf R ⟶ Y`, with `R`
a complete discrete valuation ring, lifts to a morphism `Spf R ⟶ X`.

The right-hand side is `AlgebraicGeometry.FormalSpace.FactorsAdicCompleteDvrPoints`, and the
direction the source calls trivial is
`AlgebraicGeometry.FormalSpace.isRigSurjective_of_factorsAdicCompleteDvrPoints`.

For the other direction let `p : Spf R ⟶ Y` be an adic point. Rig-surjectivity gives an
extension `R ⊂ R'` of complete discrete valuation rings and a lift `Spf R' ⟶ X`. In the fibre
product `W = Spf R ×_Y X` the projection `p₁ : W ⟶ Spf R` is locally of finite type (Stacks
0AQ5) and `W` is locally Noetherian (Stacks 0AQ8, `Spf R` being locally Noetherian by Stacks
0AKY); the relative diagonal `Δ_{p₁}` is a base change of `Δ_f` along the comparison morphism
`W ×_{Spf R} W ⟶ X ×_Y X`, itself a base change of `p` and so adic, hence rig-étale (Stacks
0GD1) and rig-surjective (Stacks 0AQS). By Stacks 0GD8 and Stacks 0GD9 the flat part `W' ⊂ W`
over `R` is `Spf R` or empty. The lift `Spf R' ⟶ W` is flat over `R` (Stacks 0GCD: `R'` is
torsion free over `R`), so it factors through `W'`, which is therefore not empty; thus
`W' ⟶ Spf R` is an isomorphism and `Spf R ≅ W' ⟶ W ⟶ X` is the lift wanted.

## Main results

* `AlgebraicGeometry.FormalSpace.factorsAdicCompleteDvrPoints_of_isRigSurjective_of_diagonal`:
  the substantial direction.
* `isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_rigEtale_diagonal` (in the namespace
  `AlgebraicGeometry.FormalSpace`): **Stacks 0GDA**.

## Implementation notes

"Adic" is Definition 0AQ3, representability by algebraic spaces
(`AlgebraicGeometry.FormalSpace.IsAdicMorphism`), as in Definition 0AQQ of rig-surjectivity.
The alternative "`W' = ∅`" of Stacks 0GD9 is excluded by
`AlgebraicGeometry.FormalSpace.not_isInitial_of_hom_formalSpectrum`: initial objects of a
category of sheaves of sets are strict, and the formal spectrum of `R'` is not initial.

## References

* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
* [Stacks Project, Tag 0AQ8](https://stacks.math.columbia.edu/tag/0AQ8)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GD8](https://stacks.math.columbia.edu/tag/0GD8)
* [Stacks Project, Tag 0GD9](https://stacks.math.columbia.edu/tag/0GD9)
* [Stacks Project, Tag 0GDA](https://stacks.math.columbia.edu/tag/0GDA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GDA**, the substantial direction. Let `f : X ⟶ Y` be a morphism of locally
Noetherian formal algebraic spaces over `S`, locally of finite type, whose relative diagonal
`Δ_f : X ⟶ X ×_Y X` is rig-étale and rig-surjective. If `f` is rig-surjective, then every adic
morphism `Spf R ⟶ Y`, with `R` a complete discrete valuation ring, lifts to `X` over `R`
itself.

Rig-surjectivity gives an extension `R ⊂ R'` and a lift `Spf R' ⟶ X`. In `W = Spf R ×_Y X` the
projection `p₁` is locally of finite type and `W` locally Noetherian; `Δ_{p₁}` is the base
change of `Δ_f` along the adic comparison morphism `W ×_{Spf R} W ⟶ X ×_Y X`, so it is
rig-étale and rig-surjective. The flat part `ι : W' ⟶ W` of Stacks 0GD8 is then `Spf R` or
empty by Stacks 0GD9; the lift `Spf R' ⟶ W` is flat over `R` and so factors through `W'`,
which therefore is not initial. Hence `ι ≫ p₁` is an isomorphism and
`inv (ι ≫ p₁) ≫ ι ≫ p₂` is the lift. -/
theorem factorsAdicCompleteDvrPoints_of_isRigSurjective_of_diagonal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal f))
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal f))
    (hrig : IsRigSurjective B S hS f) :
    FactorsAdicCompleteDvrPoints B S hS f := by
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D pt hpt
  obtain ⟨R', _, _, _, _, _, _, _, _, hR'adic, hR'complete, D', e, x, he, hx⟩ :=
    hrig R hRadic hRcomplete hRweak D pt hpt
  -- The fibre product `W = Spf R ×_Y X` and its two projections.
  have sq : IsPullback (pullback.fst pt f) (pullback.snd pt f) pt f :=
    IsPullback.of_hasPullback pt f
  have hp₁ft : IsLocallyOfFiniteType B S hS (pullback.fst pt f) :=
    IsLocallyOfFiniteType.of_isPullback B S hS sq hft
  have hSpfR : IsLocallyNoetherian B S hS (formalSpectrum D) :=
    isLocallyNoetherian_formalSpectrum_of_isAdicComplete B S hS hRadic hRcomplete D
  have hW : IsLocallyNoetherian B S hS (pullback pt f) :=
    isLocallyNoetherian_of_isPullback' B S hS sq hX.1 hY.1 hSpfR hft
  -- `X ×_Y X` and `W ×_{Spf R} W` are locally Noetherian by Stacks 0AQ8.
  have hfstff : IsLocallyOfFiniteType B S hS (pullback.fst f f) :=
    IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f f) hft
  have hXX : IsLocallyNoetherian B S hS (pullback f f) :=
    isLocallyNoetherian_of_isPullback' B S hS (IsPullback.of_hasPullback f f) hX.1 hY.1 hX hft
  have hWW : IsLocallyNoetherian B S hS (pullback (pullback.fst pt f) (pullback.fst pt f)) :=
    isLocallyNoetherian_of_isPullback' B S hS (isPullback_selfPullbackMap sq).flip hXX.1 hY.1
      hSpfR
      (IsLocallyOfFiniteType.comp B S hS _ _ hfstff hft)
  -- The comparison morphism is a base change of the adic point, hence adic.
  have hmrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (pullback.map (pullback.fst pt f) (pullback.fst pt f) f f (pullback.snd pt f)
        (pullback.snd pt f) pt sq.w sq.w).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      (isPullback_hom_of_isPullback B S hS (isPullback_selfPullbackMap sq)) hpt
  -- `Δ_{p₁}` is a base change of `Δ_f`, hence rig-étale and rig-surjective.
  have sqd := isPullback_diagonal_selfPullbackMap sq
  have hdEtale : IsRigEtale B S hS (pullback.diagonal (pullback.fst pt f)) := by
    rw [← sqd.flip.isoPullback_hom_snd]
    exact isRigEtale_iso_hom_comp B S hS _ _
      (isRigEtale_pullback_snd_of_isLocallyNoetherian B S hS _ _ hX hXX hWW hdiagEtale hmrep)
  have hdSurj : IsRigSurjective B S hS (pullback.diagonal (pullback.fst pt f)) :=
    IsRigSurjective.of_isPullback_of_representable B S hS sqd hmrep hdiagSurj
  -- The flat part of `W` over `R` and the dichotomy of Stacks 0GD9.
  obtain ⟨W', ι, hι, -, hιflat, huniv⟩ :=
    exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete B S hS D hRadic hRcomplete hW
      (pullback.fst pt f)
  have hdich := isIso_or_isInitial_flatPart_of_isRigEtale_of_isRigSurjective_diagonal B S hS D
    hRadic hRcomplete hW (pullback.fst pt f) hp₁ft ι hι hιflat huniv hdEtale hdSurj
  -- The lift of the point to the fibre product is flat over `R`, so factors through `W'`.
  have hliftflat : IsFlat B S hS
      (sq.lift (formalSpectrumMap hRweak e) x hx.symm ≫ pullback.fst pt f) := by
    rw [sq.lift_fst]
    exact isFlat_formalSpectrumMap_of_isExtension B S hS R R' hRadic hRcomplete hR'adic
      hR'complete hRweak D D' e he
  obtain ⟨r, -⟩ := huniv (formalSpectrum D') (sq.lift (formalSpectrumMap hRweak e) x hx.symm)
    (isLocallyNoetherian_formalSpectrum_of_isAdicComplete B S hS hR'adic hR'complete D')
    hliftflat
  -- Hence `W'` is not initial and the dichotomy forces `ι ≫ p₁` to be an isomorphism.
  have : IsIso (ι ≫ pullback.fst pt f) := by
    refine hdich.resolve_right fun ⟨hinit⟩ ↦ not_isInitial_of_hom_formalSpectrum D'
      ⟨IsLocalRing.maximalIdeal R', TopologicalRing.isWeakIdealOfDefinition_of_isAdic hR'adic⟩
      (IsLocalRing.maximalIdeal.isMaximal R').ne_top r hinit
  refine ⟨inv (ι ≫ pullback.fst pt f) ≫ ι ≫ pullback.snd pt f, ?_⟩
  rw [Category.assoc, Category.assoc, ← sq.w, ← Category.assoc ι, IsIso.inv_hom_id_assoc]

/-- **Stacks 0GDA.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` with `X`
and `Y` locally Noetherian, `f` locally of finite type, and the relative diagonal
`Δ_f : X ⟶ X ×_Y X` rig-étale and rig-surjective. Then `f` is rig-surjective if and only if
every adic morphism `Spf R ⟶ Y`, with `R` a complete discrete valuation ring, lifts to a
morphism `Spf R ⟶ X`. -/
@[stacks 0GDA "The whole statement, under exactly the source's hypotheses."]
theorem isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_rigEtale_diagonal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal f))
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal f)) :
    IsRigSurjective B S hS f ↔ FactorsAdicCompleteDvrPoints B S hS f :=
  ⟨factorsAdicCompleteDvrPoints_of_isRigSurjective_of_diagonal B S hS f hX hY hft hdiagEtale
      hdiagSurj,
    isRigSurjective_of_factorsAdicCompleteDvrPoints B S hS f⟩

end AlgebraicGeometry.FormalSpace

end
