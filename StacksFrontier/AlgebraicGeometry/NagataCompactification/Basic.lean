module

public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaReduction
public import StacksFrontier.AlgebraicGeometry.Limits.SeparatedFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.NoetherianCase
public import StacksCore.Tactic.StacksAttribute

/-!
# Nagata compactification over a quasi-compact quasi-separated base, by Noetherian approximation

Let `S` be quasi-compact and quasi-separated and let `f : X ⟶ S` be separated and of finite type.
**Nagata's compactification theorem** ([Stacks, Tag 0F41]) says that `X` has a compactification
over `S`: `f` factors as a quasi-compact open immersion into a scheme proper over `S`.

This file carries out the reduction of that statement to the Noetherian case, which is the same
two-step reduction as in the Stacks proof of Chow's lemma over a quasi-compact quasi-separated
base (`AlgebraicGeometry.hasChowModification_of_compactSpace_quasiSeparatedSpace`):

1. replace `X` by a scheme `Y` that is separated and of finite **presentation** over `S` and into
   which `X` closed-immerses ([Stacks, Tag 01ZJ]); compactifiability descends along a closed
   immersion, by `AlgebraicGeometry.HasCompactification.of_isClosedImmersion`;
2. write `S = lim Sᵢ` as a limit of Noetherian schemes with affine transition morphisms
   ([Stacks, Tag 01ZA]), descend `Y` to a scheme `Yᵢ` of finite presentation over some `Sᵢ`
   ([Stacks, Tag 01ZM] part (1)), pass to a later stage at which the descended morphism is
   separated ([Stacks, Tag 01ZQ]), apply the Noetherian case there, and base change the
   compactification back by
   `AlgebraicGeometry.HasCompactification.of_isPullback`.

The Noetherian case is `AlgebraicGeometry.hasCompactification_of_isNoetherian`, whose induction
step is [Stacks, Tag 0F40].

## Main results

* `AlgebraicGeometry.hasCompactification_of_finitePresentation`: a separated morphism of finite
  presentation to a quasi-compact quasi-separated scheme is compactifiable.
* `AlgebraicGeometry.hasCompactification_of_compactSpace_quasiSeparatedSpace`:
  **[Stacks, Tag 0F41]**, Nagata's compactification theorem.

## Implementation notes

The three inputs of step 2 are stated in three different idioms, and the proof spends most of its
length translating between them, exactly as
`AlgebraicGeometry.hasChowModification_of_finitePresentation` does: [Stacks, Tag 01ZA]
(`AlgebraicGeometry.exists_isLimit_finiteType`) produces a diagram indexed by the opposite of a
directed preorder, [Stacks, Tag 01ZM] part (1)
(`AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall`) is
phrased with `CategoryTheory.IsPullback`, and [Stacks, Tag 01ZQ]
(`AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit`) is phrased with
`CategoryTheory.Over.pullback`; the bridge between the last two is
`AlgebraicGeometry.isSeparated_overPullback_map_left_iff`.

Finite type is expressed, as elsewhere in this development, by `LocallyOfFiniteType` together
with `QuasiCompact`, and "quasi-compact and quasi-separated scheme" by `CompactSpace` together
with `QuasiSeparatedSpace`.

## References

* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0F40](https://stacks.math.columbia.edu/tag/0F40)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZJ](https://stacks.math.columbia.edu/tag/01ZJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Nagata compactification for a morphism of finite presentation.** If `S` is quasi-compact
and quasi-separated and `f : X ⟶ S` is separated and of finite presentation, then `X` has a
compactification over `S`.

This is the second of the two reductions in the Stacks proof of [Stacks, Tag 0F41]. Write
`S = lim Sᵢ` as a limit of schemes of finite type over the integers with affine transition
morphisms ([Stacks, Tag 01ZA]); each `Sᵢ` is then Noetherian. Descend `X` to a scheme `Xᵢ` of
finite presentation over some `Sᵢ` ([Stacks, Tag 01ZM] part (1)), and pass to a later stage at
which the descended morphism is separated ([Stacks, Tag 01ZQ]). The Noetherian case applies
there, and `f` is a base change of the morphism it applies to, so
`AlgebraicGeometry.HasCompactification.of_isPullback` transports the conclusion back to `f`. -/
@[sga "4 XVII 3.2.2" "(ii)", sga "7 XIII 2.1.6" "more general"]
theorem hasCompactification_of_finitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] (hf : FinitePresentation f) :
    HasCompactification f := by
  obtain ⟨I, hI, hInonempty, hIdirected, D, c, haffine, hfiniteType, hquasiCompact, ⟨hc⟩, hpt⟩ :=
    exists_isLimit_finiteType S
  subst hpt
  let _ : Preorder I := hI
  have : Nonempty I := hInonempty
  have : IsDirected I (· ≤ ·) := hIdirected
  have : ∀ {i j : Iᵒᵖ} (v : i ⟶ j), IsAffineHom (D.map v) := fun v => haffine v
  have hnoeth : ∀ i : Iᵒᵖ, IsNoetherian (D.obj i) := fun i =>
    isNoetherian_of_locallyOfFiniteType_terminalFrom _ (hfiniteType i) (hquasiCompact i)
  have : ∀ i : Iᵒᵖ, CompactSpace (D.obj i) := fun i => have := hnoeth i; inferInstance
  have : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i => have := hnoeth i; inferInstance
  obtain ⟨i, Y, p, g, hp, hpb⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall D c hc f hf
  have : LocallyOfFinitePresentation p := hp.1
  have : QuasiCompact p := hp.2.1
  have : IsNoetherian (D.obj i) := hnoeth i
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType p
  -- The base change of `p` to the limit is `f`, hence separated.
  have hsep : IsSeparated (pullback.snd p (c.π.app i)) := by
    have e : hpb.isoPullback.inv ≫ f = pullback.snd p (c.π.app i) := by
      rw [Iso.inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    rw [← e]
    infer_instance
  -- Pass to a stage at which the descended morphism is itself separated.
  let q : Over.mk p ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk p (by simp)
  have : IsSeparated ((Over.pullback (c.π.app i)).map q).left :=
    (isSeparated_overPullback_map_left_iff _ p q).mpr hsep
  have : CompactSpace ((Over.mk p).left : Scheme.{u}) := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace ((Over.mk p).left : Scheme.{u}) :=
    inferInstanceAs (QuasiSeparatedSpace Y)
  have : CompactSpace ((Over.mk (𝟙 (D.obj i))).left : Scheme.{u}) :=
    inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace ((Over.mk (𝟙 (D.obj i))).left : Scheme.{u}) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  obtain ⟨j, w, hsepw⟩ :=
    exists_isSeparated_baseChange_of_isLimit D c i (Over.mk p) (Over.mk (𝟙 (D.obj i))) q hc
  have hsepj : IsSeparated (pullback.snd p (D.map w)) :=
    (isSeparated_overPullback_map_left_iff _ p q).mp hsepw
  -- Nagata compactification over the Noetherian base `D.obj j`.
  have hq := FinitePresentation.of_isPullback (IsPullback.of_hasPullback p (D.map w)) hp
  have : LocallyOfFinitePresentation (pullback.snd p (D.map w)) := hq.1
  have : QuasiCompact (pullback.snd p (D.map w)) := hq.2.1
  have : IsSeparated (pullback.snd p (D.map w)) := hsepj
  have : IsNoetherian (D.obj j) := hnoeth j
  have hcpt : HasCompactification (pullback.snd p (D.map w)) :=
    hasCompactification_of_isNoetherian (pullback.snd p (D.map w))
  -- `f` is the base change of that morphism along the `j`-th leg of the cone.
  have hw : c.π.app j ≫ D.map w = c.π.app i := c.w w
  rw [← hw] at hpb
  exact HasCompactification.of_isPullback
    (IsPullback.of_right' hpb (IsPullback.of_hasPullback p (D.map w))) hcpt

/-- **Nagata compactification (Stacks Project, Tag 0F41).** Let `S` be a quasi-compact and
quasi-separated scheme and let `f : X ⟶ S` be a separated morphism of finite type. Then `X` has a
compactification over `S`: `f` factors as a quasi-compact open immersion of `X` into a scheme
proper over `S`.

[Stacks, Tag 01ZJ] factors `f` through a closed immersion into a separated morphism of finite
presentation, and compactifiability descends along a closed immersion. -/
@[stacks 0F41,
  sga "4 XVII 3.2.2" "more general",
  sga "4 XVII 3.2.3" "(iii), special case",
  sga "4½ Th_finitude 2.8" "more general",
  sga "7 XIII 2.1.6" "more general"]
theorem hasCompactification_of_compactSpace_quasiSeparatedSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] : HasCompactification f := by
  obtain ⟨Y, g, i, hsep, hfp, hclosed, hcomm⟩ :=
    exists_isClosedImmersion_into_isSeparated_finitePresentation f
  have : IsSeparated g := hsep
  have : IsClosedImmersion i := hclosed
  have : QuasiCompact g := hfp.2.1
  exact HasCompactification.of_isClosedImmersion' hcomm
    (hasCompactification_of_finitePresentation g hfp)

end AlgebraicGeometry
