module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Stacks Tag 0D2R: relative ampleness across a morphism of thickenings

Let `(f, f') : (X ⊆ X') → (S ⊆ S')` be a morphism of thickenings — a commutative square

```
X  --i-->  X'
|          |
f          f'
|          |
v          v
S  --j-->  S'
```

in which `i` and `j` are thickenings ([Stacks, Tag 04EX] part (1)); the square is part (5) of
that tag, which is why no new definition for it is introduced here. Let `ℒ'` be an invertible
`𝒪_{X'}`-module and `ℒ = i^* ℒ'` its restriction to `X`. [Stacks, Tag 0D2R] says that `ℒ'` is
`f'`-ample if and only if `ℒ` is `f`-ample, relative ampleness being [Stacks, Tag 01VH],
`Stacks.RelativeAmple.IsRelativelyAmple`.

## Main definitions

* `Stacks.ThickeningInvertible.AmpleReflectedByThickening`: **[Stacks, Tag 09MW], the implication
  `k^* M` ample `⟹` `M` ample**, as a hypothesis. It is the one input of [Stacks, Tag 0D2R] that
  this repository does not have; see "What is carried" below.

## Main results

* `Stacks.ThickeningInvertible.isRelativelyAmple_pullback`: **the implication `ℒ'` `f'`-ample
  `⟹` `ℒ` `f`-ample of [Stacks, Tag 0D2R]**, with the source's own hypotheses and nothing
  carried.
* `Stacks.ThickeningInvertible.isRelativelyAmple_of_isRelativelyAmple_pullback`: **the
  implication `ℒ` `f`-ample `⟹` `ℒ'` `f'`-ample of [Stacks, Tag 0D2R]**, carrying
  `Stacks.ThickeningInvertible.AmpleReflectedByThickening`.
* `Stacks.ThickeningInvertible.isRelativelyAmple_iff`: the biconditional, on the same one
  hypothesis.
* `Stacks.ThickeningInvertible.quasiCompact_iff`: the quasi-compactness clause of
  [Stacks, Tag 01VH] transfers across a morphism of thickenings, unconditionally.
* `Stacks.ThickeningInvertible.isThickening_id` and
  `Stacks.ThickeningInvertible.isRelativelyAmple_pullback_id`: the trivial thickening `X = X'`,
  recorded because it witnesses that the hypotheses above are satisfiable.
* `Stacks.ThickeningInvertible.isAmple_pullback_restrict` and
  `isAmple_of_isAmple_pullback_restrict`: the two halves over a single open of `X'`, which is
  where the thickening is restricted and where the two pullbacks are compared.
* `Stacks.ThickeningInvertible.restrictPullbackIso`: the comparison
  `(i ∣_ U)^* (U.ι^* ℒ') ≅ (i^{-1}U).ι^* (i^* ℒ')` of the two ways of restricting `ℒ'` to the
  part of `X` over `U`.

## The route

The source reduces to the affine case: relative ampleness is a condition at each affine open of
the base ([Stacks, Tag 01VH]), the affine opens of `S` and `S'` are in bijection
([Stacks, Tag 06AD]), and over an affine base the statement is [Stacks, Tag 09MW].

The reduction here is the same, with one simplification that removes the need for
[Stacks, Tag 06AD] on the easy side. In the direction `ℒ'` `f'`-ample `⟹` `ℒ` `f`-ample the
condition is needed at *every* affine open of `S`, and the opens `j^{-1}V'` for `V'` an affine
open of `S'` are only an affine open *covering* of `S` — affine because `j` is a closed
immersion, and covering because `j` is a homeomorphism on points. That suffices:
[Stacks, Tag 01VJ] is available in this repository as
`Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple`, so relative
ampleness may be checked on that covering. The converse direction needs nothing of the kind: an
affine open `V'` of `S'` is handed to us and `j^{-1}V'` is affine outright. **So
[Stacks, Tag 06AD] is not used in either direction**, and the only affineness transported is the
elementary one, from `S'` down to `S`.

Over a fixed open `U ⊆ X'` the two sides are compared by restricting the thickening: `i ∣_ U` is
again a surjective closed immersion
(`AlgebraicGeometry.IsZariskiLocalAtTarget.restrict` at the Mathlib instances for
`AlgebraicGeometry.IsClosedImmersion` and `AlgebraicGeometry.Surjective`), and
`Stacks.ThickeningInvertible.restrictPullbackIso` identifies `(i ∣_ U)^* (U.ι^* ℒ')` with
`(i^{-1}U).ι^* (i^* ℒ')` by pseudofunctoriality of the module pullback
(`Stacks.PullbackPseudofunctor.modulePullbackCompIso`) along
`AlgebraicGeometry.morphismRestrict_ι`. Ampleness crosses that isomorphism by
`Stacks.RelativeVeryAmple.isAmple_congr`. The open of `X'` taken is `f'^{-1}V'`, and the
commutative square gives `f^{-1}(j^{-1}V') = i^{-1}(f'^{-1}V')`, which is the only place `hsq`
is used.

Quasi-compactness transfers in both directions with no input at all: a thickening is a
homeomorphism on points, so an open of `S'` is quasi-compact exactly when its preimage in `S` is,
and likewise upstairs.

## What is carried

One hypothesis, on one of the two halves: `Stacks.ThickeningInvertible.AmpleReflectedByThickening`,
which is the implication `k^* M` ample `⟹` `M` ample of [Stacks, Tag 09MW] for a thickening `k`,
quantified over the thickening and the module. It is stated with exactly the source's hypotheses
— no Noetherian hypothesis, no cohomological premise — so the biconditional below is
[Stacks, Tag 0D2R] granted [Stacks, Tag 09MW], which is what the source's own proof grants
itself.

The other half, `Stacks.ThickeningInvertible.isRelativelyAmple_pullback`, carries nothing: the
implication `M` ample `⟹` `k^* M` ample of [Stacks, Tag 09MW] is the closed-immersion case of
[Stacks, Tag 0B3E], proved unconditionally in this repository as
`Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion`.

What this repository has towards the carried hypothesis is in
`StacksFrontier/AlgebraicGeometry/AmpleClosedImmersion/Converse.lean`, which proves the same
implication for a *locally Noetherian* target from two further inputs,
`Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion` ([Stacks, Tag 01YQ], Chevalley's
criterion) and `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` (the cohomological lift).
Removing the Noetherian hypothesis from that is the content of [Stacks, Tag 09MW] over
[Stacks, Tag 09MS] and is a limit argument that is not carried out in this repository.

## Which predicates

`Stacks.RelativeAmple.IsRelativelyAmple` for [Stacks, Tag 01VH], `Stacks.Ample.IsAmple` for
[Stacks, Tag 01PS], `Stacks.Ample.IsInvertibleModule` for invertibility, and
`Stacks.Thickenings.IsThickening` for [Stacks, Tag 04EX] part (1). The restriction of `ℒ'` to `X`
is `Stacks.AmpleLocallyClosed.pullbackModule i ℒ'`, that is
`(RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj ℒ'`, which is the spelling
the rest of the 09MS/09MW cluster of this repository uses.

## References

* [Stacks Project, Tag 0D2R](https://stacks.math.columbia.edu/tag/0D2R)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.RelativeAmple (IsRelativelyAmple)
open Stacks.Thickenings (IsThickening)

universe u

namespace Stacks.ThickeningInvertible

/-! ### A thickening is a homeomorphism on points -/

section Topology

variable {X X' : Scheme.{u}} {i : X ⟶ X'}

/-- **A thickening is a homeomorphism on underlying topological spaces**: a closed immersion is a
closed embedding, and a surjective embedding is a homeomorphism. -/
theorem isHomeomorph_base (hi : IsThickening i) : IsHomeomorph i.base :=
  have := hi.1
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, hi.2⟩

/-- **Every open of the closed subscheme of a thickening is the preimage of an open of the
ambient scheme**, namely of its image, which is open because a thickening is an open map. -/
theorem exists_preimage_eq (hi : IsThickening i) (U : X.Opens) :
    ∃ U' : X'.Opens, i ⁻¹ᵁ U' = U :=
  ⟨⟨i.base '' U, (isHomeomorph_base hi).isOpenMap _ U.isOpen⟩,
    Opens.ext (Set.preimage_image_eq _ (isHomeomorph_base hi).injective)⟩

/-- **An open of the ambient scheme of a thickening is quasi-compact exactly when its preimage
is.** -/
theorem isCompact_preimage_iff (hi : IsThickening i) (U : X'.Opens) :
    IsCompact ((i ⁻¹ᵁ U : X.Opens) : Set X) ↔ IsCompact ((U : X'.Opens) : Set X') :=
  (IsHomeomorph.homeomorph _ (isHomeomorph_base hi)).isCompact_preimage

/-- **The identity is a thickening**, the trivial thickening `X = X`. Recorded because it
witnesses that the hypotheses of the results below are satisfiable:
`Stacks.ThickeningInvertible.isRelativelyAmple_pullback_id` instantiates the easy half at it. -/
theorem isThickening_id (Y : Scheme.{u}) : IsThickening (𝟙 Y) :=
  ⟨inferInstance, Scheme.Hom.surjective (𝟙 Y)⟩

/-- **The restriction of a thickening over an open of the ambient scheme is a thickening.** Both
being a closed immersion and being surjective are Zariski-local at the target. -/
theorem isThickening_morphismRestrict (hi : IsThickening i) (U : X'.Opens) :
    IsThickening (i ∣_ U) :=
  have := hi.1
  have : Surjective i := ⟨hi.2⟩
  have hs : Surjective (i ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance U
  ⟨IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance U, hs.surj⟩

end Topology

/-! ### Comparing the two restrictions of `ℒ'` -/

section Comparison

variable {X X' : Scheme.{u}}

/-- **The two ways of restricting `ℒ'` to the part of `X` lying over an open `U` of `X'` agree.**
Pulling back first to `U` and then along the restricted morphism `i ∣_ U` gives the same module
as pulling back first along `i` and then to the open `i^{-1}U` of `X`, because the two composites
`(i ∣_ U) ≫ U.ι` and `(i^{-1}U).ι ≫ i` are the same morphism
(`AlgebraicGeometry.morphismRestrict_ι`) and the module pullback is pseudofunctorial
(`Stacks.PullbackPseudofunctor.modulePullbackCompIso`). -/
def restrictPullbackIso (i : X ⟶ X') (U : X'.Opens) (L' : X'.Modules) :
    (modulePullback (i ∣_ U).toLRSHom.toShHom).obj
        ((modulePullback U.ι.toLRSHom.toShHom).obj L') ≅
      (modulePullback (i ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
        ((modulePullback i.toLRSHom.toShHom).obj L') :=
  have he : ((i ∣_ U) ≫ U.ι).toLRSHom.toShHom = ((i ⁻¹ᵁ U).ι ≫ i).toLRSHom.toShHom :=
    congrArg (fun g : (i ⁻¹ᵁ U).toScheme ⟶ X' => g.toLRSHom.toShHom) (morphismRestrict_ι i U)
  ((Stacks.PullbackPseudofunctor.modulePullbackCompIso U.ι.toLRSHom.toShHom
        (i ∣_ U).toLRSHom.toShHom).app L').symm ≪≫
    eqToIso (congrArg (fun g => (modulePullback g).obj L') he) ≪≫
    (Stacks.PullbackPseudofunctor.modulePullbackCompIso i.toLRSHom.toShHom
      (i ⁻¹ᵁ U).ι.toLRSHom.toShHom).app L'

end Comparison

/-! ### [Stacks, Tag 09MW] as a hypothesis -/

/-- **[Stacks, Tag 09MW], the implication `k^* M` ample `⟹` `M` ample.** For a thickening
`k : Z ⟶ W` and an invertible `𝒪_W`-module `M`, ampleness of `k^* M` gives ampleness of `M`.

This is the source statement, quantified over the thickening and the module: no Noetherian
hypothesis and no cohomological premise, so a proof of [Stacks, Tag 09MW] discharges it and
nothing weaker is being assumed under its name. The reverse implication is *not* part of it; that
one is the closed-immersion case of [Stacks, Tag 0B3E] and is proved in this repository.

`StacksFrontier/AlgebraicGeometry/AmpleClosedImmersion/Converse.lean` proves this implication for a
locally Noetherian `W` from `Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion`
([Stacks, Tag 01YQ]) and `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`; removing the
Noetherian hypothesis is the limit argument of [Stacks, Tag 09MW], which this repository does not
carry out. -/
def AmpleReflectedByThickening : Prop :=
  ∀ (Z W : Scheme.{u}) (k : Z ⟶ W) (M : W.Modules) (_ : IsInvertibleModule W M),
    IsThickening k → IsAmple Z (pullbackModule k M) → IsAmple W M

/-! ### The two halves over a single open of `X'` -/

section Transfer

variable {X X' : Scheme.{u}} {i : X ⟶ X'} (L' : X'.Modules) [IsInvertibleModule X' L']

/-- Ampleness of the two restrictions of `ℒ'` to the part of `X` over `U` is equivalent. -/
private theorem isAmple_restrict_iff (U : X'.Opens) :
    IsAmple (i ⁻¹ᵁ U).toScheme (pullbackModule (i ∣_ U) (pullbackModule U.ι L')) ↔
      IsAmple (i ⁻¹ᵁ U).toScheme (pullbackModule (i ⁻¹ᵁ U).ι (pullbackModule i L')) :=
  have : IsInvertibleModule (i ⁻¹ᵁ U).toScheme
      (pullbackModule (i ∣_ U) (pullbackModule U.ι L')) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (i ∣_ U) _
  Stacks.RelativeVeryAmple.isAmple_congr _ _ (restrictPullbackIso i U L')

/-- **Ampleness of the restriction of `ℒ'` to an open `U` of `X'` gives ampleness of the
restriction of `ℒ = i^* ℒ'` to `i^{-1}U`.** Unconditional: the restricted morphism `i ∣_ U` is a
closed immersion, and ampleness pulls back along a closed immersion by the closed-immersion case
of [Stacks, Tag 0B3E]. -/
theorem isAmple_pullback_restrict (hi : IsThickening i) (U : X'.Opens)
    (h : IsAmple U.toScheme (pullbackModule U.ι L')) :
    IsAmple (i ⁻¹ᵁ U).toScheme (pullbackModule (i ⁻¹ᵁ U).ι (pullbackModule i L')) := by
  have : IsClosedImmersion (i ∣_ U) := (isThickening_morphismRestrict hi U).1
  exact (isAmple_restrict_iff L' U).mp
    (Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion (i ∣_ U) _ h)

/-- **Ampleness of the restriction of `ℒ = i^* ℒ'` to `i^{-1}U` gives ampleness of the
restriction of `ℒ'` to `U`**, granted [Stacks, Tag 09MW] in the form
`Stacks.ThickeningInvertible.AmpleReflectedByThickening`. The restricted morphism `i ∣_ U` is a
thickening, so the hypothesis applies to it directly. -/
theorem isAmple_of_isAmple_pullback_restrict (href : AmpleReflectedByThickening.{u})
    (hi : IsThickening i) (U : X'.Opens)
    (h : IsAmple (i ⁻¹ᵁ U).toScheme (pullbackModule (i ⁻¹ᵁ U).ι (pullbackModule i L'))) :
    IsAmple U.toScheme (pullbackModule U.ι L') := by
  exact href _ _ (i ∣_ U) _ inferInstance (isThickening_morphismRestrict hi U)
    ((isAmple_restrict_iff L' U).mpr h)

/-- `Stacks.ThickeningInvertible.isAmple_pullback_restrict` with the open of `X` given by an
equation rather than on the nose, so that the commutative square may be used to supply it. -/
theorem isAmple_pullback_restrict' (hi : IsThickening i) (U : X'.Opens) (W : X.Opens)
    (hW : W = i ⁻¹ᵁ U) (h : IsAmple U.toScheme (pullbackModule U.ι L')) :
    IsAmple W.toScheme (pullbackModule W.ι (pullbackModule i L')) := by
  subst hW
  exact isAmple_pullback_restrict L' hi U h

/-- `Stacks.ThickeningInvertible.isAmple_of_isAmple_pullback_restrict` with the open of `X` given
by an equation rather than on the nose. -/
theorem isAmple_of_isAmple_pullback_restrict' (href : AmpleReflectedByThickening.{u})
    (hi : IsThickening i) (U : X'.Opens) (W : X.Opens) (hW : W = i ⁻¹ᵁ U)
    (h : IsAmple W.toScheme (pullbackModule W.ι (pullbackModule i L'))) :
    IsAmple U.toScheme (pullbackModule U.ι L') := by
  subst hW
  exact isAmple_of_isAmple_pullback_restrict L' href hi U h

end Transfer

/-! ### Tag 0D2R -/

section Main

variable {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'}
  (L' : X'.Modules) [IsInvertibleModule X' L']

/-- **The commutative square of a morphism of thickenings, read on preimages of opens of `S'`.**
-/
theorem preimage_preimage (hsq : i ≫ f' = f ≫ j) (V' : S'.Opens) :
    f ⁻¹ᵁ (j ⁻¹ᵁ V') = i ⁻¹ᵁ (f' ⁻¹ᵁ V') := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq]

/-- **The quasi-compactness clause of [Stacks, Tag 01VH] transfers across a morphism of
thickenings**, with no further input: a thickening is a homeomorphism on points, so an open
downstairs is quasi-compact exactly when the corresponding open upstairs is, and likewise for
their preimages in `X` and `X'`. -/
theorem quasiCompact_iff (hi : IsThickening i) (hj : IsThickening j) (hsq : i ≫ f' = f ≫ j) :
    QuasiCompact f ↔ QuasiCompact f' := by
  have hjc := hj.1
  constructor
  · intro hf
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro V' hV'
    have h1 : IsCompact ((f ⁻¹ᵁ (j ⁻¹ᵁ V') : X.Opens) : Set X) :=
      f.isCompact_preimage (hV'.preimage j).isCompact
    rw [preimage_preimage hsq] at h1
    exact (isCompact_preimage_iff hi _).mp h1
  · intro hf'
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro V hV
    obtain ⟨V', hVV'⟩ := exists_preimage_eq hj V
    have hV'c : IsCompact ((V' : S'.Opens) : Set S') :=
      (isCompact_preimage_iff hj V').mp (by rw [hVV']; exact hV.isCompact)
    have h3 : IsCompact ((i ⁻¹ᵁ (f' ⁻¹ᵁ V') : X.Opens) : Set X) :=
      (isCompact_preimage_iff hi _).mpr (f'.isCompact_preimage hV'c)
    rw [← preimage_preimage hsq, hVV'] at h3
    exact h3

/-- **[Stacks, Tag 0D2R], the implication `ℒ'` is `f'`-ample `⟹` `ℒ` is `f`-ample.** For a
morphism of thickenings `(f, f') : (X ⊆ X') → (S ⊆ S')` and an invertible `𝒪_{X'}`-module `ℒ'`
with restriction `ℒ = i^* ℒ'` to `X`, relative ampleness of `ℒ'` over `f'` gives relative
ampleness of `ℒ` over `f`.

**Nothing is carried.** The source checks relative ampleness at every affine open of `S` and
gets the correspondence with the affine opens of `S'` from [Stacks, Tag 06AD]; here the opens
`j^{-1}V'`, for `V'` an affine open of `S'`, are an affine open covering of `S` — affine because
`j` is a closed immersion, covering because `j` is surjective — and that is enough by
[Stacks, Tag 01VJ]. Over each member the implication is the closed-immersion case of
[Stacks, Tag 0B3E] applied to `i ∣_ (f'^{-1}V')`. -/
@[stacks 0D2R "the implication `ℒ'` is `f'`-ample ⟹ `ℒ` is `f`-ample, nothing carried"]
theorem isRelativelyAmple_pullback (hi : IsThickening i) (hj : IsThickening j)
    (hsq : i ≫ f' = f ≫ j) (hL' : IsRelativelyAmple f' L') :
    IsRelativelyAmple f (pullbackModule i L') := by
  have hjc := hj.1
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
    ((quasiCompact_iff hi hj hsq).mpr hL'.1) fun x => ?_
  obtain ⟨-, ⟨V', hV', rfl⟩, hxV', -⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (j.base x)) isOpen_univ
  exact ⟨j ⁻¹ᵁ V', hV'.preimage j, hxV',
    isAmple_pullback_restrict' L' hi (f' ⁻¹ᵁ V') _ (preimage_preimage hsq V') (hL'.2 V' hV')⟩

/-- **The trivial thickening is a genuine instance of
`Stacks.ThickeningInvertible.isRelativelyAmple_pullback`.** Taking `X = X'` and `S = S'` with
both thickenings the identity, relative ampleness of `M` over `g` gives relative ampleness of
`𝟙^* M`. Recorded because it witnesses that the hypotheses of the two implications are jointly
satisfiable, so neither is vacuous.

The trivial thickening is strictly degenerate: the two sides of
`Stacks.ThickeningInvertible.isRelativelyAmple_iff` become relative ampleness of `M` and of
`𝟙^* M`, which differ only by the isomorphism `𝟙^* M ≅ M`, so what the biconditional says there
is the isomorphism invariance of relative ampleness and nothing about thickenings. It is not
closed by `Iff.rfl`: the two modules are not definitionally equal. -/
theorem isRelativelyAmple_pullback_id {Y T : Scheme.{u}} (g : Y ⟶ T) (M : Y.Modules)
    [IsInvertibleModule Y M] (hM : IsRelativelyAmple g M) :
    IsRelativelyAmple g (pullbackModule (𝟙 Y) M) :=
  isRelativelyAmple_pullback (i := 𝟙 Y) (j := 𝟙 T) (f := g) (f' := g) M
    (isThickening_id Y) (isThickening_id T) (by simp) hM

/-- **[Stacks, Tag 0D2R], the implication `ℒ` is `f`-ample `⟹` `ℒ'` is `f'`-ample**, granted
[Stacks, Tag 09MW]. For a morphism of thickenings `(f, f') : (X ⊆ X') → (S ⊆ S')` and an
invertible `𝒪_{X'}`-module `ℒ'` with restriction `ℒ = i^* ℒ'` to `X`, relative ampleness of `ℒ`
over `f` gives relative ampleness of `ℒ'` over `f'`.

**One hypothesis is carried**, `href : Stacks.ThickeningInvertible.AmpleReflectedByThickening`,
which is the implication `k^* M` ample `⟹` `M` ample of [Stacks, Tag 09MW] with the source's own
hypotheses. The source's proof of [Stacks, Tag 0D2R] cites [Stacks, Tag 09MW] at exactly this
point. Everything else is proved: an affine open `V'` of `S'` has `j^{-1}V'` affine because `j`
is a closed immersion, the commutative square identifies `f^{-1}(j^{-1}V')` with
`i^{-1}(f'^{-1}V')`, and the restricted morphism `i ∣_ (f'^{-1}V')` is again a thickening. -/
@[stacks 0D2R
  "the implication `ℒ` is `f`-ample ⟹ `ℒ'` is `f'`-ample, carrying `href` = [Tag 09MW] mp"]
theorem isRelativelyAmple_of_isRelativelyAmple_pullback (href : AmpleReflectedByThickening.{u})
    (hi : IsThickening i) (hj : IsThickening j) (hsq : i ≫ f' = f ≫ j)
    (hL : IsRelativelyAmple f (pullbackModule i L')) :
    IsRelativelyAmple f' L' := by
  have hjc := hj.1
  refine ⟨(quasiCompact_iff hi hj hsq).mp hL.1, fun V' hV' => ?_⟩
  exact isAmple_of_isAmple_pullback_restrict' L' href hi (f' ⁻¹ᵁ V') _
    (preimage_preimage hsq V') (hL.2 (j ⁻¹ᵁ V') (hV'.preimage j))

/-- **[Stacks, Tag 0D2R]**, granted [Stacks, Tag 09MW]. For a morphism of thickenings
`(f, f') : (X ⊆ X') → (S ⊆ S')` and an invertible `𝒪_{X'}`-module `ℒ'` with restriction
`ℒ = i^* ℒ'` to `X`, the module `ℒ'` is `f'`-ample if and only if `ℒ` is `f`-ample.

The `mp` half is `Stacks.ThickeningInvertible.isRelativelyAmple_pullback` and uses no hypothesis
beyond the source's; the `mpr` half is
`Stacks.ThickeningInvertible.isRelativelyAmple_of_isRelativelyAmple_pullback` and carries
`href`. -/
@[stacks 0D2R "the biconditional, carrying `href` = the `mp` half of [Tag 09MW]"]
theorem isRelativelyAmple_iff (href : AmpleReflectedByThickening.{u}) (hi : IsThickening i)
    (hj : IsThickening j) (hsq : i ≫ f' = f ≫ j) :
    IsRelativelyAmple f' L' ↔ IsRelativelyAmple f (pullbackModule i L') :=
  ⟨isRelativelyAmple_pullback L' hi hj hsq,
    isRelativelyAmple_of_isRelativelyAmple_pullback L' href hi hj hsq⟩

end Main

end Stacks.ThickeningInvertible

end
