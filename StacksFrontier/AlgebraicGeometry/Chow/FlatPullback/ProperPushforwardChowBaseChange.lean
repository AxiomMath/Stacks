module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk

/-!
# Flat pullback and proper pushforward across a fibre product square, on Chow groups

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let

      X' --g'--> X
      |          |
      f'         f
      v          v
      Y' --g-->  Y

be a fibre product diagram of schemes locally of finite type over `S`, with `f` proper and `g`
flat of relative dimension `r`. Then `f'` is proper, `g'` is flat of relative dimension `r`, and
flat pullback commutes with proper pushforward on Chow groups: for a class `c ∈ A_k(X)`

`g^* f_* c = f'_* (g')^* c`  in  `A_{k+r}(Y')`.

The identity is proved assuming the descents `Stacks.Chow.FlatPullbackDescends` and
`Stacks.Chow.ProperPushforwardDescends` and, for the structure sheaf of each integral closed
subscheme of `X`, coherence of its two direct images and the flat base change isomorphism.

## Main results

* `Stacks.Chow.comp_structureMorphism_of_isPullback` — in a cartesian square whose three other
  legs commute over the base, the fourth leg does too: `f' ≫ sY' = sX'`.
* `Stacks.Chow.flatPullbackChow_properChowPushforward` — `g^* f_* c = f'_* (g')^* c` for an
  arbitrary class `c ∈ A_k(X)` and an arbitrary cartesian square, assuming the two descents and
  the three sheaf-level hypotheses above.
* `Stacks.Chow.flatPullbackChow_comp_properChowPushforward` — the same identity as an equality of
  group homomorphisms `A_k(X) ⟶ A_{k+r}(Y')`.
* `Stacks.Chow.isCoherent_pushforward_unitModule_integralComponentAt` — the structure sheaf of an
  integral closed subscheme of a locally Noetherian scheme, pushed forward to the ambient scheme,
  is coherent.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### The fourth leg of the square commutes over the base -/

/-- In a cartesian square `IsPullback g' f' f g`, if `f`, `g` and `g'` commute with the structure
morphisms of their sources and targets over a base scheme `S`, then so does `f'`. -/
theorem comp_structureMorphism_of_isPullback {S X Y X' Y' : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (sX' : X' ⟶ S) (sY' : Y' ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hsq : IsPullback g' f' f g) (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX') :
    f' ≫ sY' = sX' := by
  rw [← hg, ← Category.assoc, ← hsq.w, Category.assoc, hf, hg']

/-! ### Flat pullback and proper pushforward on Chow groups -/

/-- **Flat pullback commutes with proper pushforward on Chow groups.** In a fibre product diagram

      X' --g'--> X
      |          |
      f'         f
      v          v
      Y' --g-->  Y

of schemes locally of finite type over the base of chapter 42, with `f` proper and `g` flat of
relative dimension `r`, let `c ∈ A_k(X)` be a Chow class. Assume the descents
`Stacks.Chow.FlatPullbackDescends` and `Stacks.Chow.ProperPushforwardDescends`, and, for the
structure sheaf of each integral closed subscheme of `X`, that its direct image along `f` and the
direct image along `f'` of its pullback along `g'` are coherent and that the base change comparison
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is an isomorphism at it. Then

`g^* f_* c = f'_* (g')^* c`  in  `A_{k+r}(Y')`. -/
@[stacks 02RG "the identity ON CHOW GROUPS, for an ARBITRARY class and an ARBITRARY cartesian \
square, descended from the cycle identity; unlike the sibling carrier keyed to two isomorphism \
legs it restricts neither leg, but the 02S1/02S2 descents remain bundled HYPOTHESES, as do the \
flat base change isomorphisms (Stacks 02KH) and coherence of the direct images (Stacks 02O5)"]
theorem flatPullbackChow_properChowPushforward
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (hS1 : FlatPullbackDescends C) (hS2 : ProperPushforwardDescends C)
    (k : ℤ) (c : chowGroup C sX k) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    (∀ x : X, ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme))).IsCoherent) →
    (∀ x : X, ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))).IsCoherent) →
    (∀ x : X, IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))) →
    flatPullbackChow C sY' sY g hg r hgr k (hS1 sY' sY g hg r hgr k)
        (properChowPushforward C sX sY f hf k (hS2 sX sY f hf k) c) =
      properChowPushforward C sX' sY' f'
        (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
        (k + (r : ℤ))
        (hS2 sX' sY' f'
          (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
          (k + (r : ℤ)))
        (flatPullbackChow C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k
          (hS1 sX' sX g' hg' r
            (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k) c) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  intro hcoh hcoh' hbc
  induction c using QuotientAddGroup.induction_on with
  | H α =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sY' (k + (r : ℤ))))
      (flatPullback_properPushforward C sX sY sX' sY' f g g' f' hsq hf hg hg' r hgr k α
        hcoh hcoh' hbc)

/-- **Flat pullback commutes with proper pushforward on Chow groups, as an equality of
homomorphisms.** The identity of
`Stacks.Chow.flatPullbackChow_properChowPushforward`, stated for the two composites
`A_k(X) ⟶ A_{k+r}(Y')` rather than for a single class, under the same hypotheses. -/
theorem flatPullbackChow_comp_properChowPushforward
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (hS1 : FlatPullbackDescends C) (hS2 : ProperPushforwardDescends C) (k : ℤ) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    (∀ x : X, ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme))).IsCoherent) →
    (∀ x : X, ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))).IsCoherent) →
    (∀ x : X, IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))) →
    (flatPullbackChow C sY' sY g hg r hgr k (hS1 sY' sY g hg r hgr k)).comp
        (properChowPushforward C sX sY f hf k (hS2 sX sY f hf k)) =
      (properChowPushforward C sX' sY' f'
        (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
        (k + (r : ℤ))
        (hS2 sX' sY' f'
          (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
          (k + (r : ℤ)))).comp
        (flatPullbackChow C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k
          (hS1 sX' sX g' hg' r
            (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  intro hcoh hcoh' hbc
  exact AddMonoidHom.ext fun c ↦ flatPullbackChow_properChowPushforward C sX sY sX' sY' f g g' f'
    hsq hf hg hg' r hgr hS1 hS2 k c hcoh hcoh' hbc

/-! ### Coherence of the pushed-forward structure sheaf of an integral closed subscheme -/

/-- **The structure sheaf of an integral closed subscheme, pushed forward, is coherent.** On a
locally Noetherian scheme `X` and at a point `x`, the direct image of `𝒪_{W_x}` along the closed
immersion of the integral closed subscheme `W_x = ` `Stacks.Chow.integralComponentAt x` is a
coherent `𝒪_X`-module. -/
theorem isCoherent_pushforward_unitModule_integralComponentAt {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) :
    ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
      (Ample.unitModule (integralComponentAt x).subscheme)).IsCoherent :=
  have : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion
      (integralComponentAt x).subschemeι
  have : (Ample.unitModule (integralComponentAt x).subscheme).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion _ _

end Stacks.Chow

end
