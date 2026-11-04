module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChowGroups
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChowPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback

/-!
# The cycle of a closed subscheme under a flat pullback and under a change of base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `X'` be
locally of finite type over `S` and let `f : X' ⟶ X` be flat of relative dimension `r`. For a
closed subscheme `i : Z ⟶ X` of delta-dimension at most `k` the flat pullback of its fundamental
cycle is the fundamental cycle of its scheme-theoretic inverse image:

`f^*[Z]_k = [X' ×_X Z]_{k+r}`.

This is the cycle identity of Stacks 02RE, part (1), with no integrality hypothesis on `Z` and
with the inequality `dim_δ(Z) ≤ k` rather than equality. It is deduced from part (2) of the same
tag exactly as in the source: by Stacks 02QY the cycle of a closed subscheme is the cycle of the
direct image of its structure sheaf, and the inverse image of `i_* 𝒪_Z` along the flat `f` is the
direct image of the structure sheaf of `X' ×_X Z`.

The same file records the companion identity for a change of the base scheme, Stacks 0FVI,
part (1): in a flat base-change situation `g : S' ⟶ S` with dimension shift `c`, the base change
of `[Z]_k` is the fundamental cycle of the base change of `Z`, presented as `pullback.fst` of the
projection `X' ⟶ X` along `i`, and Stacks 0FVJ, that base change of cycles preserves rational
equivalence, in the membership form that the construction of the induced map on Chow groups
consumes.

## Main results

* `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_snd` — **Stacks 02RE, part (1),
  cycle identity**, with the inverse image presented as `pullback.snd i f`.  The presentation as
  `pullback.fst f i` is `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le` of
  `StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity`, which is what the squares
  of Stacks 0FVK consume.
* `Stacks.Chow.baseChangeCyclePullback_cycleAssociatedToClosedSubscheme_fst` — **Stacks 0FVI,
  part (1), cycle identity**, with the base change presented as
  `pullback.fst (pullback.fst f g) i`.
* `Stacks.Chow.baseChangeFactorsThroughRationalEquivalence` — **Stacks 0FVJ**, that base change
  of cycles preserves rational equivalence, in membership form.

## Implementation notes

The scheme-theoretic inverse image of `i : Z ⟶ X` along `f` admits the two presentations
`pullback.snd i f` and `pullback.fst f i` as a closed subscheme of `X'`; they differ by
`CategoryTheory.Limits.pullbackSymmetry`, and
`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso` says the fundamental cycle does not see
the difference. Both presentations are stated, because the first is the one in which the flat
base change of `i_* 𝒪_Z` is available and the second is the one in which Stacks 02RE, part (1),
dimension bound, `Stacks.Chow.schemeDeltaDimension_pullback_le`, is stated.

The flat base change `f^*(i_* 𝒪_Z) ≅ (pullback.snd i f)_* 𝒪_{Z ×_X X'}` is Stacks 02KH in
degree zero, available here because a closed immersion is quasi-compact and quasi-separated; in
this repository it is `Stacks.Chow.pullbackPushforwardStructureSheafIso_of_flat`. Nothing else
is needed, since `Stacks.Chow.cycleAssociatedToCoherentSheaf_eq_of_iso'` turns an isomorphism of
coherent sheaves into an equality of their cycles.

The base-change identity is `Stacks.Chow.baseChangeCyclePullback_cycleAssociatedToClosedSubscheme`
read through the same symmetry of the pullback, and the last result is
`Stacks.Chow.baseChangeCyclePullback_maps_rationalEquivalences` with its conclusion unfolded from
an inequality of subgroups to a membership.

## References

* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The two presentations of a scheme-theoretic inverse image -/

/-- The scheme-theoretic inverse image of a closed subscheme `i : Z ⟶ X` along `f : X' ⟶ X`,
presented as `pullback.snd i f`, has delta-dimension at most `k + r` when `f` is flat of relative
dimension `r` and `dim_δ(Z) ≤ k`.

This is Stacks 02RE, part (1), dimension bound,
`Stacks.Chow.schemeDeltaDimension_pullback_le`, which presents the inverse image as
`pullback.fst f i`, read through the symmetry of the pullback. -/
theorem schemeDeltaDimension_pullbackSnd_le (C : ChowSituation.{u}) {X' X Z : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (hZ : schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt)) :
    schemeDeltaDimension C (pullback.snd i f ≫ sX') ≤ ((k + (r : ℤ) : ℤ) : EInt) := by
  have hbound := schemeDeltaDimension_pullback_le C sX' sX f hbase r hf i k hZ
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C sX'
    (pullback.snd i f) fun w ↦ ?_
  have hpt : pullback.fst f i ((pullbackSymmetry i f).hom w) = pullback.snd i f w :=
    congrArg (fun m : (pullback i f : Scheme.{u}) ⟶ X' ↦ m w) (pullbackSymmetry_hom_comp_fst i f)
  have h := relativeDimension_le_of_schemeDeltaDimension_le C sX' (pullback.fst f i) hbound
    ((pullbackSymmetry i f).hom w)
  rwa [hpt] at h

/-! ### Stacks 02RE, part (1), cycle identity -/

/-- **Stacks 02RE, part (1), cycle identity.** For `f : X' ⟶ X` flat of relative dimension `r`
between schemes locally of finite type over the base of chapter 42, and `i : Z ⟶ X` a closed
subscheme of delta-dimension at most `k`, the flat pullback of the fundamental `k`-cycle of `Z`
is the fundamental `(k+r)`-cycle of the scheme-theoretic inverse image of `Z`, here presented as
`pullback.snd i f`:

`f^*[Z]_k = [Z ×_X X']_{k+r}`.

Both cycles are cycles of coherent sheaves by Stacks 02QY, namely of `i_* 𝒪_Z` and of the direct
image of the structure sheaf of the inverse image, so Stacks 02RE, part (2), reduces the identity
to the flat base change `f^*(i_* 𝒪_Z) ≅ (pullback.snd i f)_* 𝒪_{Z ×_X X'}`.

The presentation that carries the `@[stacks 02RE "part (1): cycle identity"]` attribute is
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le`, which writes the inverse image
as `pullback.fst f i`, matching the dimension bound of the same part of the tag. -/
theorem flatPullback_cycleAssociatedToClosedSubscheme_snd (C : ChowSituation.{u})
    {X' X Z : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt)) :
    flatPullback C sX' sX f hbase r hf k (cycleAssociatedToClosedSubscheme C sX i k) =
      cycleAssociatedToClosedSubscheme C sX' (pullback.snd i f) (k + (r : ℤ)) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let _ : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
  let _ : ((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback f
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
  rw [cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C sX i k hZ,
    cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C sX'
      (pullback.snd i f) (k + (r : ℤ))
      (schemeDeltaDimension_pullbackSnd_le C sX' sX f hbase r hf i k hZ),
    flatPullback_cycleAssociatedToCoherentSheaf C sX' sX f hbase r hf
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) k
      (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C sX i hZ)]
  exact cycleAssociatedToCoherentSheaf_eq_of_iso' C sX' _ _ (k + (r : ℤ)) _ _
    (pullbackPushforwardStructureSheafIso_of_flat f i)

/-! ### Stacks 0FVI, part (1), cycle identity -/

/-- **Stacks 0FVI, part (1), cycle identity.** In the flat base-change situation of Stacks 0FVG,
the base change of the fundamental `k`-cycle of a closed subscheme `i : Z ⟶ X` of
delta-dimension at most `k` is the fundamental `(k+c)`-cycle of the base change of `Z`, here
presented as `pullback.fst` of the projection `X ×_S S' ⟶ X` along `i`:

`g^*[Z]_k = [Z ×_X X']_{k+c}`.

This is `Stacks.Chow.baseChangeCyclePullback_cycleAssociatedToClosedSubscheme`, which presents
the base change as `pullback.snd i` of that projection, read through the symmetry of the
pullback. -/
theorem baseChangeCyclePullback_cycleAssociatedToClosedSubscheme_fst
    (B : FlatBaseChangeSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (hZ : schemeDeltaDimension B.base (i ≫ f) ≤ (k : EInt)) :
    baseChangeCyclePullback B f k (cycleAssociatedToClosedSubscheme B.base f i k) =
      cycleAssociatedToClosedSubscheme B.baseChange (pullback.snd f B.g)
        (pullback.fst (pullback.fst f B.g) i) (k + B.c) :=
  (baseChangeCyclePullback_cycleAssociatedToClosedSubscheme B f i k hZ).trans
    (cycleAssociatedToClosedSubscheme_eq_of_iso B.baseChange (pullback.snd f B.g)
      (pullback.snd i (pullback.fst f B.g)) (pullback.fst (pullback.fst f B.g) i)
      (pullbackSymmetry i (pullback.fst f B.g))
      (pullbackSymmetry_hom_comp_fst i (pullback.fst f B.g)) (k + B.c))

/-! ### Stacks 0FVJ, as the predicate of `Stacks.Chow.flatBaseChangeChowPullback` -/

/-- **Stacks 0FVJ.** In the flat base-change situation of Stacks 0FVG, base change of `k`-cycles
carries cycles rationally equivalent to zero to cycles rationally equivalent to zero.

This is `Stacks.Chow.baseChangeCyclePullback_maps_rationalEquivalences`, stated as membership of
the image rather than as an inequality of subgroups, which is the form
`Stacks.Chow.flatBaseChangeChowPullback` consumes. -/
theorem baseChangeFactorsThroughRationalEquivalence (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ) :
    BaseChangeFactorsThroughRationalEquivalence B f k :=
  fun _ hα ↦ baseChangeCyclePullback_maps_rationalEquivalences B f k hα

end Stacks.Chow

end
