module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeGenuine
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk

/-!
# Flat pullback and proper pushforward across a fibre product square, with every side condition
discharged

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let

  `X' --g'--> X`
  `|f'        |f`
  `Y' --g-->  Y`

be a cartesian square of schemes locally of finite type over `S` with `f` proper and `g` flat of
relative dimension `r`. Flat pullback and proper pushforward commute across it on Chow groups.
`Stacks.Chow.flatPullbackChow_properChowPushforward` proves this identity under five side
conditions: the two descent bundles of Stacks 02S1 and 02S2, coherence of two direct images
(Stacks 02O5) and invertibility of the flat base change comparison (Stacks 02KH). This file
discharges all five, so that the identity holds with nothing assumed beyond the properness of
`f`, the flatness of `g` and the cartesian square.

## Main results

* `Stacks.Chow.flatPullbackChow_comp_properChowPushforward_of_isPullback`: for an arbitrary
  cartesian square with `f` proper and `g` flat of relative dimension `r`, the two composite
  homomorphisms `A_k(X) ⟶ A_{k+r}(Y')` are equal.

## Implementation notes

The three conditions that are not descent bundles are stated at the direct image `i_* 𝒪_W` of the
structure sheaf of the integral closed subscheme `W = (integralComponentAt x).subscheme` attached
to a point `x` of `X`. Each is an instance of a general theorem at that module:

* coherence of `f_*(i_* 𝒪_W)`: the structure sheaf of a locally Noetherian scheme is coherent
  (`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`), its direct image along the closed
  immersion `i` is coherent (`AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`),
  and the direct image of a coherent module along a proper morphism onto a locally Noetherian
  base is coherent (Stacks 02O5,
  `AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`);
* coherence of `f'_*(g'^*(i_* 𝒪_W))`: the same, since the pullback of a coherent module along a
  morphism with locally Noetherian source is coherent (`AlgebraicGeometry.isCoherent_pullback`);
* invertibility of the base change comparison at `i_* 𝒪_W`: Stacks 02KH,
  `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`, for an
  arbitrary quasi-coherent module across a cartesian square whose flat leg is flat and whose other
  leg is quasi-compact and quasi-separated. A proper morphism is quasi-compact and
  quasi-separated, and a coherent module is quasi-coherent.

The two descent bundles are `Stacks.Chow.flatPullbackDescends` and
`Stacks.Chow.properPushforwardDescends`.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Coherence of the direct images -/

/-- The direct image along a proper morphism of the direct image of the structure sheaf of the
integral closed subscheme attached to a point is coherent. -/
@[ega "III 4.3.1" "coherence of f_*O_X"]
theorem isCoherent_pushforward_pushforward_unitModule_integralComponentAt {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X) :
    ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
        (Ample.unitModule (integralComponentAt x).subscheme))).IsCoherent :=
  have := isCoherent_pushforward_unitModule_integralComponentAt x
  AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f _

/-- The direct image along a proper morphism of the pullback of the direct image of the structure
sheaf of the integral closed subscheme attached to a point is coherent. -/
theorem isCoherent_pushforward_pullback_pushforward_unitModule_integralComponentAt
    {X X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') [IsProper f'] [IsLocallyNoetherian X]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y'] (x : X) :
    ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
        (Ample.unitModule (integralComponentAt x).subscheme)))).IsCoherent :=
  have := isCoherent_pushforward_unitModule_integralComponentAt x
  have := AlgebraicGeometry.isCoherent_pullback g'
    ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
      (Ample.unitModule (integralComponentAt x).subscheme))
  AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f' _

/-! ### Invertibility of the flat base change comparison -/

/-- Across a cartesian square whose right leg `f` is proper and whose bottom leg `g` is flat, the
base change comparison morphism is an isomorphism at every quasi-coherent module. -/
theorem isIso_baseChange_app_of_isProper_of_flat {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (hsq : IsPullback g' f' f g) [IsProper f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F) :=
  Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat hsq F

/-- Across a cartesian square whose right leg is proper and whose bottom leg is flat, the base
change comparison is an isomorphism at the direct image of the structure sheaf of the integral
closed subscheme attached to a point. -/
theorem isIso_baseChange_app_pushforward_unitModule_integralComponentAt {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (hsq : IsPullback g' f' f g)
    [IsProper f] [Flat g] [IsLocallyNoetherian X] (x : X) :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
      ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
        (Ample.unitModule (integralComponentAt x).subscheme))) :=
  have := isCoherent_pushforward_unitModule_integralComponentAt x
  have := _root_.isQuasicoherent_of_isCoherent
    ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
      (Ample.unitModule (integralComponentAt x).subscheme))
  isIso_baseChange_app_of_isProper_of_flat hsq _

/-! ### Flat pullback and proper pushforward commute on Chow groups -/

/-- Across a cartesian square with `f` proper and `g` flat of relative dimension `r`, the
composite of proper pushforward along `f` and flat pullback along `g` equals the composite of flat
pullback along `g'` and proper pushforward along `f'`, as homomorphisms
`A_k(X) ⟶ A_{k+r}(Y')`. -/
theorem flatPullbackChow_comp_properChowPushforward_of_isPullback
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r) (k : ℤ) :
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    (flatPullbackChow C sY' sY g hg r hgr k
          (flatPullbackDescends C sY' sY g hg r hgr k)).comp
        (properChowPushforward C sX sY f hf k (properPushforwardDescends C sX sY f hf k)) =
      (properChowPushforward C sX' sY' f'
        (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
        (k + (r : ℤ))
        (properPushforwardDescends C sX' sY' f'
          (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
          (k + (r : ℤ)))).comp
        (flatPullbackChow C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k
          (flatPullbackDescends C sX' sX g' hg' r
            (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k)) := by
  have hfp : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  have hg'ft : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hg'fl : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  refine AddMonoidHom.ext fun c ↦ ?_
  exact flatPullbackChow_properChowPushforward_unconditional C sX sY sX' sY' f g g' f' hsq hf hg
    hg' r hgr k c

end Stacks.Chow

end
