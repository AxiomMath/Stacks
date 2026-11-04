module

public import StacksFrontier.Topology.ExtremallyDisconnected.Characterization
public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.Topology.Spectral.ComponentSpace

/-!
# Extremal disconnectedness passes to retracts

A quasi-compact Hausdorff space that is a retract of an extremally disconnected quasi-compact
Hausdorff space is itself extremally disconnected. Equivalently, a quasi-compact Hausdorff space
is extremally disconnected as soon as *one* extremally disconnected cover of it admits a
continuous section — after which, by Stacks 08YN, every continuous surjection onto it from a
quasi-compact Hausdorff space admits one.

This is the step the source calls "a formal categorical argument" in the proof of Lemma 61.6.7
(Stacks 09AZ): a surjection `T → π₀(Spec A)` from an extremally disconnected quasi-compact
Hausdorff space is produced by Stacks 090D, a section of it is obtained from a retraction of a
ring map, and extremal disconnectedness of `π₀(Spec A)` is concluded. Nothing of Lemma 09AZ
itself is proved here; see the implementation notes.

## Main definitions

No new definitions are introduced.

## Main results

* `extremallyDisconnected_of_retract`: a quasi-compact Hausdorff retract of an extremally
  disconnected quasi-compact Hausdorff space is extremally disconnected.
* `extremallyDisconnected_iff_forall_cover_section`: a quasi-compact Hausdorff space is
  extremally disconnected if and only if every extremally disconnected cover of it admits a
  continuous section.
* `extremallyDisconnected_connectedComponents_of_retract`: the same criterion for the space of
  connected components of a spectral space, which is the shape in which Lemma 09AZ uses it.

## Implementation notes

The proof transfers the lifting property `CompactT2.Projective` of
`StacksFrontier.Topology.ExtremallyDisconnected.Characterization` along the retraction and then
returns to extremal disconnectedness through `extremallyDisconnected_tfae`. Every use of
`List.TFAE.out` is bound to a `have` whose type is written out, so that the elaborator — and not
the reader's count of the one-based indices — decides which implication was extracted.

Surjectivity of the retraction is not assumed in `extremallyDisconnected_of_retract`: a map with
a section is surjective anyway, and leaving it out makes the lemma applicable to a bare retract.

`extremallyDisconnected_connectedComponents_of_retract` is stated for a spectral space because
that is the generality in which `connectedComponents_isProfinite` supplies the Hausdorff
property of `π₀`; quasi-compactness comes from `SpectralSpace` extending `CompactSpace` together
with Mathlib's `CompactSpace (ConnectedComponents _)` instance. For `X = PrimeSpectrum A` the
spectrality instance is Mathlib's, so the `π₀(Spec A)` form that Lemma 09AZ needs is this lemma
applied with no further argument.

This file does **not** prove Lemma 09AZ and carries no `@[stacks 09AZ]` attribute. Lemma 09AZ
cites nine results: `08YN`, `090D` and `096B` are in the library, and the other six — `0975`,
`097A`, `097C`, `097D`, `097E` and `097G` — are absent from it, so not one of the implications
between the three conditions of Lemma 09AZ is available. What this file adds is the only step of
its proof that is not a citation to another lemma.

## References

* [Stacks Project, Tag 08YN](https://stacks.math.columbia.edu/tag/08YN)
* [Stacks Project, Tag 0906](https://stacks.math.columbia.edu/tag/0906)
* [Stacks Project, Tag 090D](https://stacks.math.columbia.edu/tag/090D)
* [Stacks Project, Tag 09AZ](https://stacks.math.columbia.edu/tag/09AZ)
-/

@[expose] public section

universe u

/-- The lifting property against continuous surjections of quasi-compact Hausdorff spaces passes
to a retract: lift the composite with the retraction `r`, then restrict along the section `s`. -/
private theorem compactT2Projective_of_retract {X T : Type u}
    [TopologicalSpace X] [TopologicalSpace T] (hT : CompactT2.Projective T)
    {r : T → X} {s : X → T} (hr : Continuous r) (hs : Continuous s) (hrs : r ∘ s = id) :
    CompactT2.Projective X := by
  intro Y Z _ _ _ _ _ _ g f hg hf hfsurj
  obtain ⟨h, hhcont, hfh⟩ := hT (hg.comp hr) hf hfsurj
  exact ⟨h ∘ s, hhcont.comp hs,
    funext fun x => (congrFun hfh (s x)).trans (congrArg g (congrFun hrs x))⟩

/-- **Extremal disconnectedness passes to retracts.** Let `X` be a quasi-compact Hausdorff space,
let `T` be a quasi-compact Hausdorff extremally disconnected space, and let `s : X → T` and
`r : T → X` be continuous with `r ∘ s = id`. Then `X` is extremally disconnected.

By Stacks 08YN extremal disconnectedness of `T` is the same as `T` lifting against continuous
surjections of quasi-compact Hausdorff spaces; that property passes to the retract `X`; and
Stacks 08YN turns it back into extremal disconnectedness of `X`. -/
theorem extremallyDisconnected_of_retract {X T : Type u} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TopologicalSpace T] [CompactSpace T] [T2Space T] [ExtremallyDisconnected T]
    {r : T → X} {s : X → T} (hr : Continuous r) (hs : Continuous s) (hrs : r ∘ s = id) :
    ExtremallyDisconnected X := by
  have hTiff : ExtremallyDisconnected T ↔ CompactT2.Projective T :=
    (extremallyDisconnected_tfae T).out 1 3
  have hXiff : ExtremallyDisconnected X ↔ CompactT2.Projective X :=
    (extremallyDisconnected_tfae X).out 1 3
  exact hXiff.mpr (compactT2Projective_of_retract (hTiff.mp inferInstance) hr hs hrs)

/-- **A quasi-compact Hausdorff space is extremally disconnected exactly when its extremally
disconnected covers admit continuous sections.** For `X` quasi-compact Hausdorff, `X` is
extremally disconnected if and only if every continuous surjection onto `X` from a quasi-compact
Hausdorff extremally disconnected space has a continuous section.

The forward implication is the restriction of Stacks 08YN to covers that are extremally
disconnected. For the converse, Stacks 090D supplies one such cover, its section exhibits `X` as
a retract of an extremally disconnected space, and `extremallyDisconnected_of_retract` applies;
so a single cover with a section already suffices. -/
theorem extremallyDisconnected_iff_forall_cover_section (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] :
    ExtremallyDisconnected X ↔
      ∀ (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
        [ExtremallyDisconnected T] (π : T → X), Continuous π → Function.Surjective π →
          ∃ σ : X → T, Continuous σ ∧ π ∘ σ = id := by
  have hXiff : ExtremallyDisconnected X ↔ HasContinuousSectionFromCompactT2 X :=
    (extremallyDisconnected_tfae X).out 1 2
  refine ⟨fun hX T _ _ _ _ π hπ hπsurj => hXiff.mp hX π hπ hπsurj, fun hsec => ?_⟩
  obtain ⟨T, _, _, _, _, π, hπ, hπsurj⟩ := exists_extremallyDisconnected_cover X
  obtain ⟨σ, hσ, hπσ⟩ := hsec T π hπ hπsurj
  exact extremallyDisconnected_of_retract hπ hσ hπσ

/-- **The retract criterion for the space of connected components of a spectral space.** Let `X`
be a spectral space and let `T` be a quasi-compact Hausdorff extremally disconnected space. If
there are continuous maps `s : π₀(X) → T` and `r : T → π₀(X)` with `r ∘ s = id`, then `π₀(X)` is
extremally disconnected.

`π₀(X)` is quasi-compact and Hausdorff by `connectedComponents_isProfinite`, so
`extremallyDisconnected_of_retract` applies. Taking `X = PrimeSpectrum A` gives the statement
used in the proof of Lemma 09AZ. -/
theorem extremallyDisconnected_connectedComponents_of_retract (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] {T : Type u} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [ExtremallyDisconnected T] {r : T → ConnectedComponents X} {s : ConnectedComponents X → T}
    (hr : Continuous r) (hs : Continuous s) (hrs : r ∘ s = id) :
    ExtremallyDisconnected (ConnectedComponents X) := by
  have : T2Space (ConnectedComponents X) := (connectedComponents_isProfinite X).1
  exact extremallyDisconnected_of_retract hr hs hrs

end
