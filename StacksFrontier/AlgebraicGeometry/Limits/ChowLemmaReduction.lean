module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Chow's lemma over a quasi-compact quasi-separated base, reduced to the Noetherian case

**Chow's lemma** (Stacks 0202) says that a separated morphism of finite type `f : X ⟶ S` over a
quasi-compact, quasi-separated base admits a Chow modification in the sense of
`AlgebraicGeometry.HasChowModification`. The Stacks proof deduces it from Chow's lemma over a
*Noetherian* base (Stacks 0200) by absolute Noetherian approximation, in two reductions:

1. replace `X` by a scheme `Y` that is separated and of finite **presentation** over `S` and into
   which `X` closed-immerses (Stacks 01ZJ);
2. write `S = lim Sᵢ` as a limit of Noetherian schemes with affine transition morphisms (Stacks
   01ZA), descend `Y` to a scheme `Yᵢ` of finite presentation over some `Sᵢ` (Stacks 01ZM part
   (1)), arrange that `Yᵢ ⟶ Sᵢ` is separated by passing to a later stage (Stacks 01ZQ), and apply
   Chow's lemma over the Noetherian base `Sᵢ`.

This file carries out reduction 2 in full, as `hasChowModification_of_finitePresentation`: Chow's
lemma for a separated morphism of finite presentation over a quasi-compact, quasi-separated base
is a consequence of Chow's lemma over a Noetherian base and nothing else. Reduction 1 is then a
single application of `AlgebraicGeometry.HasChowModification.of_isClosedImmersion`, recorded as
`hasChowModification_of_isClosedImmersion_of_finitePresentation`, which takes the embedding of
Stacks 01ZJ as data.

Chow's lemma over a Noetherian base is not proved here; it is carried as the hypothesis
`AlgebraicGeometry.ChowOverNoetherianBase`, which states exactly Stacks 0200 (without its
supplementary assertion that the modification can be taken to be an isomorphism over a dense
open, which `AlgebraicGeometry.HasChowModification` does not record).

## Main definitions

* `AlgebraicGeometry.ChowOverNoetherianBase` is the statement of Chow's lemma over a Noetherian
  base, Stacks 0200, in the form in which the reductions of Stacks 0202 consume it.

## Main results

* `AlgebraicGeometry.hasChowModification_of_finitePresentation`: Chow's lemma holds for a
  separated morphism of finite presentation over a quasi-compact, quasi-separated base, granted
  Chow's lemma over a Noetherian base.
* `AlgebraicGeometry.hasChowModification_of_isClosedImmersion_of_finitePresentation`: Chow's
  lemma holds for a morphism that closed-immerses into a separated morphism of finite
  presentation over a quasi-compact, quasi-separated base, granted Chow's lemma over a Noetherian
  base. Composed with Stacks 01ZJ this is Stacks 0202.

## Implementation notes

The three inputs used here are stated in three different idioms, and the proof spends most of its
length translating between them. Stacks 01ZA
(`AlgebraicGeometry.exists_isLimit_finiteType`) produces a diagram indexed by the opposite of a
directed preorder; Stacks 01ZM part (1)
(`AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall`)
is phrased with `CategoryTheory.IsPullback`; and Stacks 01ZQ
(`AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit`) is phrased with
`CategoryTheory.Over.pullback`. The bridge between the last two idioms is
`AlgebraicGeometry.isSeparated_overPullback_map_left_iff`: a morphism of schemes over `T`, viewed
as a morphism to the terminal object `CategoryTheory.Over.mk (𝟙 T)` of the over category, has the
projection `pullback.snd` of its base change for underlying morphism, up to the canonical
isomorphism `pullback (𝟙 T) g ≅ T'`.

Finite type is expressed, as elsewhere in this development, by `LocallyOfFiniteType` together
with `QuasiCompact`, and "quasi-compact and quasi-separated scheme" by `CompactSpace` together
with `QuasiSeparatedSpace`.

## References

* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01ZJ](https://stacks.math.columbia.edu/tag/01ZJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Over

/-- The underlying morphism of the base change of a morphism in an over category commutes with
the projections to the new base: this is `CategoryTheory.Over.w` for `Over.pullback g`, with the
structure morphisms of the base-changed objects unfolded to projections. -/
theorem pullback_map_left_comp_snd {C : Type u} [Category.{v} C] {T T' : C} (g : T' ⟶ T)
    [HasPullbacksAlong g] {X Y : Over T} (f : X ⟶ Y) :
    ((Over.pullback g).map f).left ≫ pullback.snd Y.hom g = pullback.snd X.hom g := by
  simp

end CategoryTheory.Over

namespace AlgebraicGeometry

/-- Separatedness of the base change of a morphism of schemes over `T`, as `Over.pullback`
produces it from a morphism to the terminal object `Over.mk (𝟙 T)` of the over category, is
separatedness of the projection `pullback.snd`. The two differ by the canonical isomorphism
`pullback (𝟙 T) g ≅ T'`. -/
theorem isSeparated_overPullback_map_left_iff {T T' : Scheme.{u}} (g : T' ⟶ T) {Y : Scheme.{u}}
    (p : Y ⟶ T) (f : Over.mk p ⟶ Over.mk (𝟙 T)) :
    IsSeparated ((Over.pullback g).map f).left ↔ IsSeparated (pullback.snd p g) := by
  have hw : ((Over.pullback g).map f).left ≫ pullback.snd (𝟙 T) g = pullback.snd p g :=
    Over.pullback_map_left_comp_snd g f
  constructor
  · intro _
    rw [← hw]
    infer_instance
  · intro h
    have h' : IsSeparated (pullback.snd p g ≫ inv (pullback.snd (𝟙 T) g)) := inferInstance
    rwa [← hw, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h'

/-- **Chow's lemma over a Noetherian base**, Stacks 0200: every separated morphism of finite type
to a Noetherian scheme admits a Chow modification.

This is carried as a hypothesis by the results below, which reduce Chow's lemma over a
quasi-compact, quasi-separated base (Stacks 0202) to it. It is weaker than Stacks 0200, which
asserts in addition that the modification can be taken to be an isomorphism over a dense open
subscheme; `AlgebraicGeometry.HasChowModification` does not record that. -/
def ChowOverNoetherianBase : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S), IsNoetherian S → IsSeparated f → LocallyOfFiniteType f →
    QuasiCompact f → HasChowModification f

/-- **Chow's lemma for a morphism of finite presentation**, granted Chow's lemma over a Noetherian
base. If `S` is quasi-compact and quasi-separated and `f : X ⟶ S` is separated and of finite
presentation, then `f` admits a Chow modification.

This is the second of the two reductions in the Stacks proof of 0202. Write `S = lim Sᵢ` as a
limit of schemes of finite type over the integers with affine transition morphisms (Stacks 01ZA);
each `Sᵢ` is then Noetherian. Descend `X` to a scheme `Xᵢ` of finite presentation over some `Sᵢ`
(Stacks 01ZM part (1)), and pass to a later stage at which the descended morphism is separated
(Stacks 01ZQ). Chow's lemma over the Noetherian base `Sⱼ` applies there, and `f` is a base change
of the morphism it applies to, so `AlgebraicGeometry.HasChowModification.of_isPullback`
transports the conclusion back to `f`. -/
theorem hasChowModification_of_finitePresentation (H : ChowOverNoetherianBase.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
    (hf : FinitePresentation f) : HasChowModification f := by
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
    rw [← hpb.isoPullback.inv_comp_eq.mpr hpb.isoPullback_hom_snd.symm]
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
  -- Chow's lemma over the Noetherian base `D.obj j`.
  have hq := FinitePresentation.of_isPullback (IsPullback.of_hasPullback p (D.map w)) hp
  have : LocallyOfFinitePresentation (pullback.snd p (D.map w)) := hq.1
  have hchow : HasChowModification (pullback.snd p (D.map w)) :=
    H (D.obj j) _ _ (hnoeth j) ((isSeparated_overPullback_map_left_iff _ p q).mp hsepw)
      inferInstance hq.2.1
  -- `f` is the base change of that morphism along the `j`-th leg of the cone.
  rw [← c.w w] at hpb
  exact HasChowModification.of_isPullback
    (IsPullback.of_right' hpb (IsPullback.of_hasPullback p (D.map w))) hchow

/-- **Chow's lemma for a morphism closed-immersing into one of finite presentation**, granted
Chow's lemma over a Noetherian base. If `S` is quasi-compact and quasi-separated, `g : Y ⟶ S` is
separated and of finite presentation, and `j : X ⟶ Y` is a closed immersion over `S`, then
`f = j ≫ g` admits a Chow modification.

Together with Stacks 01ZJ, which produces such a `g` and `j` for any separated morphism of finite
type to a quasi-compact, quasi-separated scheme, this is Stacks 0202. -/
theorem hasChowModification_of_isClosedImmersion_of_finitePresentation
    (H : ChowOverNoetherianBase.{u}) {X Y S : Scheme.{u}} {j : X ⟶ Y} {g : Y ⟶ S} {f : X ⟶ S}
    [CompactSpace S] [QuasiSeparatedSpace S] [IsClosedImmersion j] [IsSeparated g]
    (hg : FinitePresentation g) (hf : j ≫ g = f) : HasChowModification f :=
  HasChowModification.of_isClosedImmersion hf (hasChowModification_of_finitePresentation H g hg)

end AlgebraicGeometry

end
