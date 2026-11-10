module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete

/-!
# Relative Tag 03JH under a size bound instead of a containment hypothesis

The relative form of Tag 03JH proved in
`StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative` glues a family of charts over a
test object and asks the caller for the containment of the glued scheme in the size-bounded
site, in the shape of a hypothesis quantified over every family of charts the proof might
build:

```
∀ (W : ι → BigFppfOver B S hS) (Z : Scheme) (k : ∀ i, (toScheme).obj (W i) ⟶ Z),
  (∀ i, IsOpenImmersion (k i)) → (∀ z : Z, ∃ i, z ∈ Set.range (k i)) → B.Contains Z
```

That hypothesis is **unsatisfiable** once `ι` is as large as the cofinality of the cutoff, for
the same reason the cofinality route into
`AlgebraicGeometry.BigFppfSite.contains_of_openCover` runs out: nothing bounds the supremum of
`#ι` many sizes below the cutoff, and the cutoff built by
`Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof` — the one every big fppf site produced by
`AlgebraicGeometry.exists_common_bigFppfSite` carries — is `ℶ_(mu.ord + ω₁)`, whose cofinality is
exactly `ℵ₁`. So a family of `ℵ₁` objects of cofinally many sizes glues to a scheme of size at
least the cutoff, and the containment fails.

The hypothesis is nevertheless the wrong *shape* rather than a real obstruction, and this file
replaces it by the pair of bounds that
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le` consumes, exactly as
`StacksFrontier.AlgebraicGeometry.Descent.ZariskiCoverSizeBound` does for the glueing step of
Stacks 02W8. Two observations do it.

*The index type never needs a bound at all.* A family of open immersions covering a test object
`T` may be replaced by the subfamily picking out one member per distinct open image, and the
opens of `T` number fewer than the cutoff: `#T ≤ 2 ^ size T` by
`AlgebraicGeometry.Scheme.mk_le_two_pow_size` and `#T.Opens ≤ 2 ^ #T`, both below the cutoff by
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`. The conclusion of the glueing mentions
neither the index type nor the charts, so passing to the subfamily costs nothing.

*The uniform bound on the charts is free for an algebraic space.* Every chart of the glueing is
a base change of an open immersion of the site, hence an open subspace of the presheaf being
glued, and `AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` bounds every
representable open subspace of a presheaf carrying a surjective étale chart by
`max (2 ^ #U) (2 ^ size U)`, a cardinal mentioning only the chart's source.

Together these discharge the containment outright for a morphism of algebraic spaces, with no
hypothesis on the index type of the covering: see
`AlgebraicGeometry.Space.presheaf_isAffineHom_of_zariskiCover_isAffineHom_of_isAlgebraicSpace`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.BigFppfSite.mk_opens_lt_cutoff`: the opens of a scheme contained in a big
  fppf site number fewer than the site's cutoff.
* `AlgebraicGeometry.Space.exists_representing_over_of_openCover_of_size_le`: **relative Tag
  03JH from an open covering of the test object, under a uniform size bound on the charts and
  no hypothesis whatever on the index type.** This is
  `AlgebraicGeometry.Space.exists_representing_over_of_openCover` with its containment
  hypothesis replaced.
* `AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_size_le`: the
  same for the covering by the affine opens of the test object, the containment hypothesis
  replaced by a uniform bound on the representable open subspaces of the source.
* `AlgebraicGeometry.Space.presheaf_of_zariskiCover_of_size_le`: **descent of relative
  representability with a Zariski-local property along a Zariski covering**, with the
  containment hypothesis of `AlgebraicGeometry.Space.presheaf_of_zariskiCover` replaced by a
  uniform bound and no hypothesis on the index type of the covering.
* `AlgebraicGeometry.Space.exists_size_bound_of_atlas`: that uniform bound, for a presheaf
  carrying a surjective étale chart.
* `AlgebraicGeometry.Space.presheaf_isAffineHom_of_zariskiCover_isAffineHom_of_isAlgebraicSpace`:
  the implication (5) ⇒ (1) of Stacks 03WG with *both* containment hypotheses of
  `AlgebraicGeometry.Space.presheaf_isAffineHom_of_zariskiCover_isAffineHom` discharged.

## Implementation notes

*What this does not supersede.* `AlgebraicGeometry.Space.presheaf_of_zariskiCover_of_lt_cof`
stays: the cofinality bound and the uniform bound are incomparable hypotheses, and the
cofinality form asks nothing of the charts. The statements with containment hypotheses stay too;
they are true, and they are the engines these are proved from.

*Relation to the detour through the affine test objects.*
`AlgebraicGeometry.Space.isAffineHom_of_zariskiCover_isAffineHom` and
`AlgebraicGeometry.Space.presheaf_of_zariskiCover_presheaf_pullback_snd` reach the same
conclusions by gluing over an *affine* test object only, where quasi-compactness cuts the
covering down to a finite subfamily and the cofinality bound of
`AlgebraicGeometry.BigFppfSite.contains_of_openCover` applies to it. That route loses nothing
mathematically — `AlgebraicGeometry.Space.presheaf_of_zariskiCover_of_size_le` composed with
`AlgebraicGeometry.Space.exists_size_bound_of_atlas` proves exactly the statement of
`AlgebraicGeometry.Space.presheaf_of_zariskiCover_presheaf_pullback_snd`, which is therefore
not restated here. What the statements of this file add is that the restriction to affine test
objects is not needed: the index type can be cut down over an arbitrary test object, and the
charts are bounded by the atlas.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- **A scheme contained in a big fppf site has fewer opens than the cutoff.** The opens inject
into the subsets of the carrier, of which there are `2 ^ #X`, and `#X ≤ 2 ^ size X` by
`AlgebraicGeometry.Scheme.mk_le_two_pow_size`; two applications of
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` bring `2 ^ 2 ^ size X` below the cutoff.

This is what makes the index type of an open covering of an object of the site harmless: the
covering may be replaced by the subfamily of its distinct open images, whose index type is a set
of opens of the object. -/
theorem BigFppfSite.mk_opens_lt_cutoff (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) : #X.Opens < B.cutoff :=
  ((Cardinal.mk_le_of_injective (SetLike.coe_injective (A := X.Opens))).trans
      Cardinal.mk_set.le).trans_lt
    (B.cutoff_isStrongPrelimit ((Scheme.mk_le_two_pow_size X).trans_lt
      (B.cutoff_isStrongPrelimit hX)))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Relative Tag 03JH under a uniform size bound -/

/-- **Tag 03JH in relative form over a test object, under a uniform size bound on the charts.**

This is `AlgebraicGeometry.Space.exists_representing_over_of_openCover` with the containment
hypothesis `hcontains` replaced by one cardinal `μ` below the cutoff bounding the sizes of all
the charts — and with **no hypothesis at all on the index type** `ι`.

That `ι` needs no bound is the point. The covering of the test object is replaced by the
subfamily choosing one member for each distinct open image, which still covers and whose index
type is a set of opens of the test object, of cardinality below the cutoff by
`AlgebraicGeometry.BigFppfSite.mk_opens_lt_cutoff`; the glued object is then contained in the
site by `AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le`, or by
`AlgebraicGeometry.BigFppfSite.contains_of_isEmpty` when no open image occurs and the test
object therefore has no points. Since the conclusion mentions neither the index type nor the
charts, passing to the subfamily costs nothing.

The containment hypothesis it replaces is unsatisfiable for an index type as large as the
cofinality of the cutoff, which `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` and
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof` together leave possible at `ℵ₁`; this pair
of hypotheses is the one a geometric construction can meet. -/
theorem exists_representing_over_of_openCover_of_size_le
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj T)
    {ι : Type u} {V W : ι → BigFppfOver B S hS}
    {u : ∀ i, V i ⟶ T} {p : ∀ i, W i ⟶ V i} {q : ∀ i, yoneda.obj (W i) ⟶ F}
    (hu : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (u i)))
    (hucov : ∀ y : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u i)))
    (hpb : ∀ i, IsPullback (q i) (yoneda.map (p i)) π (yoneda.map (u i)))
    (hQp : ∀ i, Q ((BigFppfOver.toScheme B S hS).map (p i)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hW : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ μ) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧ Q ((BigFppfOver.toScheme B S hS).map P) := by
  classical
  set o : ι → ((BigFppfOver.toScheme B S hS).obj T).Opens :=
    fun i => ((BigFppfOver.toScheme B S hS).map (u i)).opensRange with ho
  set s : Set.range o → ι := Set.rangeSplitting o with hsdef
  have hs : ∀ a : Set.range o, o (s a) = (a : _) := Set.apply_rangeSplitting o
  refine exists_representing_over_of_openCover B S hS hQ hF π
    (V := fun a : Set.range o => V (s a)) (W := fun a : Set.range o => W (s a))
    (u := fun a : Set.range o => u (s a)) (p := fun a : Set.range o => p (s a))
    (q := fun a : Set.range o => q (s a)) (fun a => hu (s a)) ?_
    (fun a => hpb (s a)) (fun a => hQp (s a)) ?_
  · intro y
    obtain ⟨i, hi⟩ := hucov y
    refine ⟨⟨o i, ⟨i, rfl⟩⟩, ?_⟩
    change y ∈ o (s ⟨o i, ⟨i, rfl⟩⟩)
    rw [hs ⟨o i, ⟨i, rfl⟩⟩]
    exact hi
  · intro Z k hk hkcov
    rcases isEmpty_or_nonempty (Set.range o) with hemp | hne
    · exact B.contains_of_isEmpty ⟨fun z => hemp.false (hkcov z).choose⟩
    · have := hk
      exact B.contains_of_openCover_of_size_le
        (μ := max #((BigFppfOver.toScheme B S hS).obj T).Opens μ)
        (max_lt (B.mk_opens_lt_cutoff T.left.property) hμ)
        (le_max_of_le_left (Cardinal.mk_set_le _)) k hkcov
        fun a => le_max_of_le_right (hW (s a))

/-- **Tag 03JH in relative form, from the affine base changes, under a uniform size bound.**

This is `AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange` with the
containment hypothesis `hcontains` — which asks for the containment of every scheme glued from
every family of affine objects indexed by the affine opens of the test object — replaced by one
cardinal `μ` below the cutoff bounding the size of every object of the site representing an open
subspace of the source.

The replacement is what the hypothesis should have been. The charts of the glueing are chosen
inside the proof, so `hcontains` had to quantify over the families they might form, and nothing
bounds the sizes of affine objects: an affine morphism to an affine scheme is the spectrum of an
algebra of arbitrary cardinality. But the charts are not arbitrary affine objects — each is a
base change of `π` along an open immersion of the site, hence an open subspace of `F`, which is
what `hbound` speaks about and what
`AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` supplies as soon as `F` has a
surjective étale chart. That instance is
`AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`,
which is accordingly unconditional. -/
theorem exists_representing_over_of_holdsOnAffineBaseChange_of_size_le
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj T)
    (hπ : HoldsOnAffineBaseChange B S hS Q π)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hbound : ∀ (V : BigFppfOver B S hS) (k : yoneda.obj V ⟶ F),
      IsOpenImmersion B S hS k → ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧ Q ((BigFppfOver.toScheme B S hS).map P) := by
  choose V u hu hurange hVaff using
    fun U => BigFppfOver.exists_affineOpen_restrict B S hS T U
  choose W p q hpb hWaff hQp using fun U => hπ (V U) (hVaff U) (yoneda.map (u U))
  refine exists_representing_over_of_openCover_of_size_le B S hS hQ hF π
    (V := V) (W := W) (u := u) (p := p) (q := q) hu ?_ hpb hQp hμ
    fun U => hbound (W U) (q U)
      (isOpenImmersion_of_isPullback_yoneda_map B S hS (hu U) (hpb U))
  intro y
  have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hy
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  exact ⟨U, by rw [hurange U]; exact hU⟩

/-! ### Descent along a Zariski covering under a uniform size bound -/

/-- **Relative representability with a Zariski-local property is Zariski local at the target,
under a uniform size bound.**

This is `AlgebraicGeometry.Space.presheaf_of_zariskiCover` with the containment hypothesis
`hcontains`, indexed by the index type `I` of the covering, replaced by `hbound`: over each test
object there is one cardinal below the cutoff bounding the size of every object of the site
representing an open subspace of the base change of `f` there.

Nothing is asked of `#I`. The charts of the glueing over a test object `T` are base changes of
`Limits.pullback.snd f h` along the open immersions to which the members of the covering pull
back, hence open subspaces of `Limits.pullback f h` by
`AlgebraicGeometry.Space.isOpenImmersion_of_isPullback_yoneda_map`, so `hbound` bounds them; and
`AlgebraicGeometry.Space.exists_representing_over_of_openCover_of_size_le` needs no more than
that.

The hypothesis replaced is unsatisfiable for `#I` at least the cofinality of the cutoff, whereas
`hbound` is a consequence of the other hypotheses when `f` is a morphism of algebraic spaces: the
base change of `f` over a test object is an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_pullback`, so
`AlgebraicGeometry.Space.exists_size_bound_of_atlas` supplies it. Composing the two in that way
proves exactly the statement of
`AlgebraicGeometry.Space.presheaf_of_zariskiCover_presheaf_pullback_snd`. -/
theorem presheaf_of_zariskiCover_of_size_le
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (hres : ∀ i, (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (Limits.pullback.snd f (U i).ι))
    (hbound : ∀ (T : BigFppfOver B S hS) (h : yoneda.obj T ⟶ Y),
      ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ ∀ (V : BigFppfOver B S hS)
        (k : yoneda.obj V ⟶ Limits.pullback f h), IsOpenImmersion B S hS k →
          ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf f := by
  have := hQ
  have hRI : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists ?_
  intro T h
  obtain ⟨μ, hμ, hbd⟩ := hbound T h
  have key : ∀ i, ∃ (W : BigFppfOver B S hS) (p : W ⟶ (hU.1 i).2.rep.pullback h)
      (q : yoneda.obj W ⟶ Limits.pullback f h),
      IsPullback q (yoneda.map p) (Limits.pullback.snd f h)
        (yoneda.map ((hU.1 i).2.rep.snd h)) ∧
      Q ((BigFppfOver.toScheme B S hS).map p) := by
    intro i
    have step := ((hres i).rep.isPullback ((hU.1 i).2.rep.fst h)).paste_horiz
      (IsPullback.of_hasPullback f (U i).ι)
    rw [((hU.1 i).2.rep.isPullback h).w] at step
    exact ⟨_, _, _, IsPullback.of_right' step (IsPullback.of_hasPullback f h),
      (hres i).property_snd _⟩
  choose W p q hpb hQp using key
  obtain ⟨Y', e, P, hP, hQP⟩ := exists_representing_over_of_openCover_of_size_le B S hS hQ
    (BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY) (Limits.pullback.snd f h)
    (V := fun i => (hU.1 i).2.rep.pullback h) (W := W)
    (u := fun i => (hU.1 i).2.rep.snd h) (p := p) (q := q)
    (fun i => (hU.1 i).2.property_snd h)
    (exists_mem_range_snd_of_zariskiCover B S hS hU h) hpb hQp hμ
    fun i => hbd (W i) (q i) (isOpenImmersion_of_isPullback_yoneda_map B S hS
      ((hU.1 i).2.property_snd h) (hpb i))
  exact ⟨Y', e.inv ≫ Limits.pullback.fst f h, P,
    (IsPullback.of_hasPullback f h).of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simpa using hP) (by simp) (by simp), hQP⟩

/-- **A presheaf with a surjective étale chart bounds the size of every object of the site
representing an open subspace of it, uniformly.**

`AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` gives the bound
`max (2 ^ #U) (2 ^ size U)`, which mentions only the chart's source `U` and lies below the
cutoff because `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` is a strong prelimit;
this packages the two as the existential statement which
`AlgebraicGeometry.Space.presheaf_of_zariskiCover_of_size_le` and
`AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_size_le`
consume, in the shape of
`AlgebraicGeometry.Space.exists_size_bound_of_descentDatum`.

Nothing is asked of `X` beyond the chart: not sheafness, not a representable diagonal, not
representability. -/
theorem exists_size_bound_of_atlas {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X}
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ ∀ (V : BigFppfOver B S hS) (k : yoneda.obj V ⟶ X),
      IsOpenImmersion B S hS k → ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ :=
  ⟨max (2 ^ #((BigFppfOver.toScheme B S hS).obj U : Type u))
      (2 ^ ((BigFppfOver.toScheme B S hS).obj U).size),
    Scheme.max_two_pow_mk_two_pow_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      U.left.property,
    fun _ _ hk => size_le_of_isOpenImmersion_of_atlas B S hS hsurj hetale hk⟩

/-! ### Stacks 03WG, (5) implies (1), unconditionally -/

/-- **Stacks 03WG, (5) implies (1)**, unconditionally.

If a morphism `f` of algebraic spaces over `S` is affine in the sense of Stacks 03WF over the
members of some Zariski covering of its target, then `f` is representable with affine
represented base changes.

This is `AlgebraicGeometry.Space.presheaf_isAffineHom_of_zariskiCover_isAffineHom` with **both**
of its containment hypotheses discharged, and in particular with no hypothesis on the index type
of the covering. The one indexed by the affine opens of a test object is discharged by
`AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`, which applies
the implication (2) ⇒ (1) over each member of the covering; the one indexed by the covering
itself is discharged by `AlgebraicGeometry.Space.exists_size_bound_of_atlas` applied to the
base change of `f` over a test object, which is an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_pullback`, feeding
`AlgebraicGeometry.Space.presheaf_of_zariskiCover_of_size_le`.

Unlike (4) ⇒ (1) this needs no effective descent. The same conclusion is also reachable as
(5) ⇒ (2) ⇒ (1) through `AlgebraicGeometry.Space.isAffineHom_of_zariskiCover_isAffineHom`, which
exploits a feature special to affineness — an affine morphism to an affine scheme has affine
source. The route taken here uses nothing of the kind, which is why it is also the route
available for an arbitrary Zariski-local property. -/
theorem presheaf_isAffineHom_of_zariskiCover_isAffineHom_of_isAlgebraicSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h₅ : ∀ i, IsAffineHom B S hS (Limits.pullback.snd f (U i).ι)) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f := by
  have h := presheaf_of_zariskiCover_of_size_le B S hS
    isZariskiLocalAtTarget_isAffineHom hX.isSheaf hY.isSheaf hU
    (fun i => presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS
      isZariskiLocalAtTarget_isAffineHom
      (isAlgebraicSpace_pullback B S hS f (U i).ι hX (hU.1 i).1 hY) (hU.1 i).1
      ((isAffineHom_iff_holdsOnAffineBaseChange _).1 (h₅ i)))
    fun T g => by
      obtain ⟨U₀, a, haS, haE⟩ := (isAlgebraicSpace_pullback B S hS f g hX
        (isAlgebraicSpace_yoneda B S hS T) hY).exists_atlas
      exact exists_size_bound_of_atlas B S hS haS haE
  exact ⟨h.rep, h⟩

end Space

end AlgebraicGeometry

end
