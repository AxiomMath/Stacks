module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent

/-!
# Proper pushforward and flat pullback commute on Chow groups

Let
```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```
be a fibre product diagram of schemes locally of finite type over the base of chapter 42, with `f`
proper and `g` flat of relative dimension `r`. The third assertion of [Stacks, Tag 02RG] is
`g^* f_* α = f'_* (g')^* α`. This file proves it for every cycle and every Chow class, without the
hypotheses of `Stacks.Chow.flatPullback_properPushforward` and
`Stacks.Chow.flatPullbackChow_properChowPushforward`:

* the descents Stacks 02S1 and 02S2 are `Stacks.Chow.flatPullbackDescends` and
  `Stacks.Chow.properPushforwardDescends`;
* the structure sheaf of a locally Noetherian scheme is coherent
  (`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`), its pushforward along a closed
  immersion is coherent ([Stacks, Tag 087T]), the direct image along a proper morphism of a
  coherent module is coherent ([Stacks, Tag 02O5]) and the inverse image of a coherent module is
  coherent ([Stacks, Tag 0EBF]);
* Stacks 02KH in degree zero is
  `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`.

## Main results

* `Stacks.Chow.isProper_and_relativeDimension_and_flatPullback_properPushforward`: Stacks 02RG,
  all three assertions.
* `Stacks.Chow.flatPullback_properPushforward_unconditional`: the third assertion of Stacks 02RG on
  cycles, for an arbitrary cycle and an arbitrary cartesian square.
* `Stacks.Chow.flatPullbackChow_properChowPushforward_unconditional`: Stacks 02RG on Chow groups,
  for an arbitrary class and an arbitrary cartesian square.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- The coherence and base change inputs of Stacks 02RG for the pushforward of the structure sheaf
of the integral component at each point. -/
private theorem coherence_and_base_change_of_unit_pushforward
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g) :
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    ∀ x : X, ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme))).IsCoherent ∧
      ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))).IsCoherent ∧
      IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian sY'
  have : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  have : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  intro x
  have : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (integralComponentAt x).subschemeι
  have : (Ample.unitModule (integralComponentAt x).subscheme).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit _
  have := isCoherent_pushforward_of_isClosedImmersion (integralComponentAt x).subschemeι
    (Ample.unitModule (integralComponentAt x).subscheme)
  have := isCoherent_pullback g' ((Scheme.Modules.pushforward
    (integralComponentAt x).subschemeι).obj (Ample.unitModule (integralComponentAt x).subscheme))
  have := isQuasicoherent_of_isCoherent ((Scheme.Modules.pushforward
    (integralComponentAt x).subschemeι).obj (Ample.unitModule (integralComponentAt x).subscheme))
  exact ⟨ProperCoherenceWitness.isCoherent_pushforward f _,
    ProperCoherenceWitness.isCoherent_pushforward f' _,
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat hsq _⟩

/-- **Proper pushforward commutes with flat pullback on cycles.** For a cartesian square

      X' --g'--> X
      |          |
      f'         f
      v          v
      Y' --g-->  Y

of schemes locally of finite type over the base of chapter 42, with `f` proper and `g` flat of
relative dimension `r`, `g^* f_* α = f'_* (g')^* α` in `Z_{k+r}(Y')` for every `α ∈ Z_k(X)`. -/
theorem flatPullback_properPushforward_unconditional
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (k : ℤ) (α : CycleGroup C sX k) :
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k α) =
      properPushforward C sX' sY' f'
        (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
        (k + (r : ℤ))
        (flatPullback C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k α) := by
  have := coherence_and_base_change_of_unit_pushforward C sX sY sX' sY' f g g' f' hsq
  refine flatPullback_properPushforward C sX sY sX' sY' f g g' f' hsq hf hg hg' r hgr k α
    (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · exact (this x).1
  · exact (this x).2.1
  · exact (this x).2.2

/-- **Proper pushforward and flat pullback across a fibre product square.** Let

      X' --g'--> X
      |          |
      f'         f
      v          v
      Y' --g-->  Y

be a fibre product diagram of schemes locally of finite type over the base of chapter 42, with
`f` proper and `g` flat of relative dimension `r`. Then `f'` is proper, `g'` is flat of relative
dimension `r` (flat, locally of finite type, and of relative dimension `r` in the sense of
Stacks 02NJ), and for every `k` and every `α ∈ Z_k(X)`,

`g^* f_* α = f'_* (g')^* α`  in  `Z_{k+r}(Y')`.

The first assertion is stability of properness under base change, the second is Stacks 02NK and
stability of flatness and of local finite type under base change, and the third is
`Stacks.Chow.flatPullback_properPushforward_unconditional`. -/
@[stacks 02RG "all three assertions, under the source's hypotheses: f' is proper, g' is flat of \
relative dimension r, and g^* f_* alpha = f'_* (g')^* alpha in Z_{k+r}(Y') for every k and every \
k-cycle alpha on X"]
theorem isProper_and_relativeDimension_and_flatPullback_properPushforward
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r) :
    IsProper f' ∧ Flat g' ∧ LocallyOfFiniteType g' ∧
      @AlgebraicGeometry.RelativeDimension _ _ g'
        (MorphismProperty.of_isPullback hsq.flip inferInstance) r ∧
      ∀ (k : ℤ) (α : CycleGroup C sX k),
        letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
        letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
        letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
        flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k α) =
          properPushforward C sX' sY' f'
            (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
            (k + (r : ℤ))
            (flatPullback C sX' sX g' hg' r
              (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k α) :=
  ⟨MorphismProperty.of_isPullback hsq inferInstance,
    MorphismProperty.of_isPullback hsq.flip inferInstance,
    MorphismProperty.of_isPullback hsq.flip inferInstance,
    AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr,
    flatPullback_properPushforward_unconditional C sX sY sX' sY' f g g' f' hsq hf hg hg' r hgr⟩

/-- **Stacks 02RG on Chow groups.** For a cartesian square with `f` proper and `g` flat of relative
dimension `r`, `g^* f_* c = f'_* (g')^* c` in `A_{k+r}(Y')` for every `c ∈ A_k(X)`. -/
theorem flatPullbackChow_properChowPushforward_unconditional
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (k : ℤ) (c : chowGroup C sX k) :
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    flatPullbackChow C sY' sY g hg r hgr k (flatPullbackDescends C sY' sY g hg r hgr k)
        (properChowPushforward C sX sY f hf k (properPushforwardDescends C sX sY f hf k) c) =
      properChowPushforward C sX' sY' f'
        (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
        (k + (r : ℤ))
        (properPushforwardDescends C sX' sY' f'
          (comp_structureMorphism_of_isPullback sX sY sX' sY' f g g' f' hsq hf hg hg')
          (k + (r : ℤ)))
        (flatPullbackChow C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k
          (flatPullbackDescends C sX' sX g' hg' r
            (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k) c) := by
  have := coherence_and_base_change_of_unit_pushforward C sX sY sX' sY' f g g' f' hsq
  refine flatPullbackChow_properChowPushforward C sX sY sX' sY' f g g' f' hsq hf hg hg' r hgr
    (flatPullbackDescends C) (properPushforwardDescends C) k c (fun x => ?_) (fun x => ?_)
    (fun x => ?_)
  · exact (this x).1
  · exact (this x).2.1
  · exact (this x).2.2

end Stacks.Chow

end
