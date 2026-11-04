module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoherentColimit

/-!
# Stacks 02RG, with every hypothesis discharged

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let
```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```
be a fibre product diagram of schemes locally of finite type over `S`, with `f` proper and `g`
flat of relative dimension `r`. [Stacks, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
asserts three things: that `f'` is proper, that `g'` is flat of relative dimension `r`, and that

  `g^* f_* α = f'_* (g')^* α`  in  `Z_{k + r}(Y')`

for every `k`-cycle `α` on `X`.

The first two assertions are recorded in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChange` by
`add_to_stacks` on the four stability results they are. The third is proved there, and on Chow
groups in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChange`, but in both
places with the inputs the source's proof defers to left as explicit hypotheses: cohomology and
base change ([Stacks, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)) and coherence of the
two direct images ([Stacks, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)), and at the
Chow level also the two descent bundles for Stacks 02S1 and 02S2.

**This file discharges all of them.** Every input is a theorem of this repository; none is
assumed here, and the statements below are therefore Stacks 02RG outright.

## Where each input comes from

* **Stacks 02KH**, the base-change isomorphism `g^* f_* ℱ ≅ f'_* (g')^* ℱ` in degree zero over an
  arbitrary base, is
  `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`. It is
  stated for `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the comparison
  morphism chapter 42 is phrased with. Its side conditions hold here: `f` proper gives
  `QuasiCompact f` and `QuasiSeparated f`, and the module in question is coherent on a locally
  Noetherian scheme, hence quasi-coherent.
* **Stacks 02O5**, coherence of the direct image along a proper morphism onto a locally
  Noetherian base, is `AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`. For the
  second of the two coherence hypotheses the module pushed forward is an inverse image, coherent
  by `AlgebraicGeometry.isCoherent_pullback` (Stacks 0EBF).
* **Stacks 02S1** and **Stacks 02S2**, bundled over all their inputs, are
  `Stacks.Chow.flatPullbackDescends` and `Stacks.Chow.properPushforwardDescends`.

## Main results

* `Stacks.Chow.isIso_baseChange_app_of_isProper` — Stacks 02KH in the form chapter 42 consumes:
  for a cartesian square with `f` proper and `g` flat, the comparison
  `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is an isomorphism at every
  coherent module.
* `Stacks.Chow.flatPullback_properPushforward_of_isProper` — **Stacks 02RG on cycles**, for an
  arbitrary `k`-cycle and an arbitrary cartesian square, with no hypothesis.
* `Stacks.Chow.flatPullbackChow_properChowPushforward_of_isProper` — **Stacks 02RG on Chow
  groups**, likewise with no hypothesis.

## Implementation notes

Nothing is restated here. Each theorem below is the corresponding theorem of
`ProperPushforwardBaseChange` or `ProperPushforwardChowBaseChange` with its hypotheses supplied,
so the mathematics stays where it was proved and this file only joins it to the inputs it was
waiting for. That is the arrangement
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent` already uses for
Stacks 02S1: proving the discharge in a downstream leaf keeps the heavy base-change and
coherence modules out of the import closure of everything that merely states a cycle identity.

The `@[stacks 02RG]` attributes below are bare. The restriction strings on the conditional
carriers upstream record what those statements assume; these two assume nothing, and together
with the four `add_to_stacks 02RG` lines of `ProperPushforwardBaseChange` — the first two
assertions of the tag — they cover the whole of Stacks 02RG.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Stacks 02KH in the form chapter 42 consumes -/

/-- **Stacks 02KH for the comparison morphism of chapter 42.** For a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```
with `f` proper and `g` flat, and for a coherent module `F` on `X` with `X` locally Noetherian,
the base-change morphism `g^* f_* F ⟶ f'_* (g')^* F` of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is an isomorphism.

This is `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`.
Properness of `f` supplies the quasi-compactness and quasi-separatedness
that flat base change asks for, and coherence of `F` on a locally Noetherian scheme supplies
quasi-coherence. -/
theorem isIso_baseChange_app_of_isProper {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (g : Y' ⟶ Y) [AlgebraicGeometry.Flat g] (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hsq : CategoryTheory.IsPullback g' f' f g) [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F) := by
  have : F.IsQuasicoherent :=
    AlgebraicGeometry.GroupoidScheme.isQuasicoherent_of_isCoherent F inferInstance
  exact Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat hsq F

/-! ### Stacks 02RG on cycles -/

/-- Coherence of the two direct images (Stacks 02O5, Stacks 0EBF) and the base-change
isomorphism (Stacks 02KH) at a coherent module `F`. -/
private theorem isCoherent_and_isIso_of_isProper {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (g : Y' ⟶ Y) [AlgebraicGeometry.Flat g] (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hsq : CategoryTheory.IsPullback g' f' f g) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y'] [IsProper f'] [AlgebraicGeometry.Flat g']
    (F : X.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent ∧
    ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent ∧
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F) := by
  have : ((Scheme.Modules.pullback g').obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback g' _
  exact ⟨AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f _,
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f' _,
    isIso_baseChange_app_of_isProper f g g' f' hsq _⟩

/-- **Stacks 02RG, third assertion, on cycles.** Let `(S, δ)` be as in Situation 02QL, let
```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```
be a fibre product diagram of schemes locally of finite type over `S`, let `f` be proper and let
`g` be flat of relative dimension `r`. Then for every `k`-cycle `α` on `X`,

  `g^* f_* α = f'_* (g')^* α`  in  `Z_{k + r}(Y')`.

That `f'` is proper and `g'` flat of relative dimension `r` — the first two assertions of the tag
— is what makes the right hand side meaningful, and is supplied by the instances the statement
elaborates with.

This is `Stacks.Chow.flatPullback_properPushforward` with its three hypotheses discharged: the
two coherence hypotheses by Stacks 02O5 and Stacks 0EBF, the base-change isomorphism by
`Stacks.Chow.isIso_baseChange_app_of_isProper`. -/
@[stacks 02RG]
theorem flatPullback_properPushforward_of_isProper
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [AlgebraicGeometry.Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : CategoryTheory.IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (k : ℤ) (α : CycleGroup C sX k) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : AlgebraicGeometry.Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k α) =
      properPushforward C sX' sY' f'
        (by rw [← hg, ← Category.assoc, ← hsq.w, Category.assoc, hf, hg']) (k + (r : ℤ))
        (flatPullback C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k α) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian sY'
  let : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : AlgebraicGeometry.Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  exact flatPullback_properPushforward C sX sY sX' sY' f g g' f' hsq hf hg hg' r hgr k α
    (fun _ => (isCoherent_and_isIso_of_isProper f g g' f' hsq _).1)
    (fun _ => (isCoherent_and_isIso_of_isProper f g g' f' hsq _).2.1)
    (fun _ => (isCoherent_and_isIso_of_isProper f g g' f' hsq _).2.2)

/-! ### Stacks 02RG on Chow groups -/

/-- **Stacks 02RG on Chow groups.** In the fibre product diagram above, with `f` proper and `g`
flat of relative dimension `r`, the flat pullback of the proper pushforward of a class agrees
with the proper pushforward of its flat pullback:

  `g^* f_* c = f'_* (g')^* c`  in  `A_{k + r}(Y')`  for every  `c ∈ A_k(X)`.

This is `Stacks.Chow.flatPullbackChow_properChowPushforward` with all five of its hypotheses
discharged: the two descent bundles by `Stacks.Chow.flatPullbackDescends` (Stacks 02S1) and
`Stacks.Chow.properPushforwardDescends` (Stacks 02S2), and the coherence and base-change
hypotheses exactly as for the cycle-level statement above. -/
@[stacks 02RG]
theorem flatPullbackChow_properChowPushforward_of_isProper
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [AlgebraicGeometry.Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : CategoryTheory.IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (k : ℤ) (c : chowGroup C sX k) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : AlgebraicGeometry.Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
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
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian sY'
  let : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : AlgebraicGeometry.Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  exact flatPullbackChow_properChowPushforward C sX sY sX' sY' f g g' f' hsq hf hg hg' r hgr
    (flatPullbackDescends C) (properPushforwardDescends C) k c
    (fun _ => (isCoherent_and_isIso_of_isProper f g g' f' hsq _).1)
    (fun _ => (isCoherent_and_isIso_of_isProper f g g' f' hsq _).2.1)
    (fun _ => (isCoherent_and_isIso_of_isProper f g g' f' hsq _).2.2)

end Stacks.Chow

end
