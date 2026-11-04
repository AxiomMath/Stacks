module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local criteria for immersions and for quasi-affine morphisms of algebraic spaces

Stacks 03M4 characterizes each of the three immersion properties of a morphism `f : F ⟶ G` of
algebraic spaces over a scheme `S` by five conditions: `f` has the property, that is, is
representable with the corresponding property of morphisms of schemes on its represented base
changes; every base change of `f` to a representable presheaf has it; every base change of `f`
to an *affine* object of the site has it; the base change of `f` along one surjective étale
scheme chart of `G` has it; and the base changes of `f` along the members of some Zariski
covering of `G` have it. Stacks 03WM characterizes quasi-affineness of `f` by four conditions:
representability with quasi-affine represented base changes; quasi-affineness in the sense of
Stacks 03WL; quasi-affineness on a surjective étale scheme chart of `G`, with an explicit object
of the site representing the base change; and quasi-affineness over the members of a Zariski
covering of `G`.

Both tags share the same two hard steps, and this file proves both of them once, for an
arbitrary property `P` of morphisms of schemes which is Zariski local at the target: the passage
from the *affine* test objects to all test objects, and the passage from a Zariski covering of
the target to the affine test objects. Each is a glueing, and both are unconditional — the
glueing hypothesis `AlgebraicGeometry.HasZariskiGluing` which the corresponding statements of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete` once carried is discharged by
`AlgebraicGeometry.hasZariskiGluing`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_representing_over_of_affineBaseChange` and
  `AlgebraicGeometry.Space.presheaf_of_affineBaseChange`: relative Tag 03JH with no affineness
  asked of the charts and with no glueing hypothesis.
* `AlgebraicGeometry.Space.presheaf_of_affine_presheaf_pullback_snd`: a Zariski-local property
  tested on the base changes to the affine objects of the site holds on all base changes. This
  is the implication (3) ⇒ (1) of Stacks 03M4, for an arbitrary `P`.
* `AlgebraicGeometry.Space.exists_representing_of_zariskiCover_of_isAffine` and
  `AlgebraicGeometry.Space.presheaf_of_zariskiCover_presheaf_pullback_snd`: a Zariski-local
  property holding over the members of a Zariski covering of the target holds everywhere. This
  is the implication (5) ⇒ (1) of Stacks 03M4, for an arbitrary `P`.
* `AlgebraicGeometry.Space.presheaf_tfae`: the five conditions of Stacks 03M4 for an arbitrary
  `P`, equivalent, conditionally on
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` for `P`; and its
  instantiations `AlgebraicGeometry.Space.isOpenImmersion_tfae` and
  `AlgebraicGeometry.Space.isImmersion_tfae`. The closed-immersion instantiation is
  `AlgebraicGeometry.Space.isClosedImmersion_tfae` of
  `StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionLocalCriterion`, which is downstream
  of this file because its descent input is unconditional there.
* `AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace`
  and `AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_zariskiCover`: the implications
  (2) ⇒ (1) and (4) ⇒ (1) of Stacks 03WM, unconditionally.
* `AlgebraicGeometry.Space.isQuasiAffineHom_tfae`: the four conditions of Stacks 03WM,
  equivalent, conditionally on
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` for quasi-affine morphisms of
  schemes.

## Implementation notes

*Why the charts of the glueing must not be required to be affine.* The relative Tag 03JH of
`StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative` comes in two forms: one, taking a
family of open immersions covering the test object, asks nothing of the charts, and one, taking
the affine opens of the test object, asks that the chart over each be *affine*. The second is
what Stacks 03WG uses, because an affine morphism to an affine scheme has affine source. None of
the properties of this file has that feature: an open immersion into an affine scheme is an
arbitrary open subscheme, an immersion is worse, and a quasi-affine morphism to an affine scheme
has only quasi-affine source. So the statement needed here is the first form, specialized to the
affine opens of the test object. Affineness of the charts was never used by the discharge of the
containment hypothesis in
`AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`
— the bound comes from the algebraic space being glued, through
`AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` — so dropping it costs nothing.

*Why the Zariski-covering step goes through the affine test objects.* The index type of a
Zariski covering is an arbitrary type in the working universe, so the sizes of its charts have no
uniform bound below the cutoff and the glueing cannot be performed over an arbitrary test object.
Over an *affine* test object the covering pulls back to an open covering of a quasi-compact
scheme, a finite subcovering suffices, and the containment of the glued object is the cofinality
bound of `AlgebraicGeometry.BigFppfSite.contains_of_openCover` — or
`AlgebraicGeometry.BigFppfSite.contains_of_isEmpty` when the subcovering is empty. This is the
route `AlgebraicGeometry.Space.isAffineHom_of_zariskiCover_isAffineHom` takes for Stacks 03WG,
and it is reproduced here for an arbitrary `P`.

*What is still assumed.* Exactly one hypothesis survives in the equivalences proved here, and no
declaration in this file carries the tag 03M4 or the tag 03WM:
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`, which is Tag 03I2 for the
class in question. It is used only for the implication back from the condition which tests the
property on a single surjective étale chart — condition (4) of Stacks 03M4 and condition (3) of
Stacks 03WM. Every other implication of both tags is proved outright.

For the two classes this file instantiates it that hypothesis is now itself a theorem, so the
equivalences hold unconditionally one import further on, and the tags are carried there:
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion` of
`StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent` for the immersion classes, with
Stacks 03M4 carried in that file; and
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom` of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent`, which is Tag 0247, for the
quasi-affine morphisms. Stacks 03WM is *not* carried anywhere in this development:
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfaeComplete` states the equivalence with a
third condition stronger than the source's, because the source derives that condition from
Stacks 03JH and this development does not prove it; that file records the reason. Neither route
consumes the fppf descent of Tag 02W8.

In particular the second input of
`AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart`, base change
stability of quasi-affineness, is no longer an assumption: it is the instance
`AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange`, Tag 01SO.

## References

* [Stacks Project, Tag 01SO](https://stacks.math.columbia.edu/tag/01SO)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A pullback square transported along an isomorphism from the fibre product. -/
private theorem isPullback_of_iso_pullback_snd {C : Type*} [Category C] {F G T Y : C}
    (f : F ⟶ G) (g : T ⟶ G) [HasPullback f g] (e : pullback f g ≅ Y) {p : Y ⟶ T}
    (hp : e.inv ≫ pullback.snd f g = p) : IsPullback (e.inv ≫ pullback.fst f g) p f g :=
  (IsPullback.of_hasPullback f g).of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using hp) (by simp) (by simp)

/-- **Tag 03JH in relative form over a test object, with no affineness asked of the charts.**

Let `π : F ⟶ yoneda.obj T` be a morphism from an algebraic space over `S` to a representable
presheaf, and let `Q` be a property of morphisms of schemes which is Zariski local at the
target. If the base change of `π` along every morphism from an *affine* object of the site is
represented by an object of the site whose projection to that object has `Q`, then `F` is
representable over `T`, by an object whose projection to `T` has `Q`.

This is
`AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`
with two changes. The representing objects are *not* required to be affine, which is what makes
the statement usable for the immersion properties of Tag 02YU and for quasi-affineness: a closed
immersion into an affine scheme does have affine source, but an open immersion does not, and a
quasi-affine morphism to an affine scheme has only quasi-affine source. Affineness of the charts
was never used: the containment of the glued object comes from the algebraic space `F` being
glued, not from the property being tested.

The charts of the glueing are the base changes of `π` along the affine opens of `T`, which are
objects of the site by `AlgebraicGeometry.BigFppfOver.exists_affineOpen_restrict` and cover `T`
by `AlgebraicGeometry.iSup_affineOpens_eq_top`. Each is an open subspace of `F`, so
`AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` bounds their sizes uniformly by a
cardinal below the cutoff, and the index type — the affine opens of `T` — has cardinality at
most the size of `T`, again below the cutoff. -/
theorem exists_representing_over_of_affineBaseChange
    {Q : MorphismProperty Scheme.{u}} (hQ : IsZariskiLocalAtTarget Q)
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (π : F ⟶ yoneda.obj T)
    (hπ : ∀ Z : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ g : yoneda.obj Z ⟶ yoneda.obj T,
        ∃ (W : BigFppfOver B S hS) (p : W ⟶ Z) (q : yoneda.obj W ⟶ F),
          IsPullback q (yoneda.map p) π g ∧ Q ((BigFppfOver.toScheme B S hS).map p)) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧ Q ((BigFppfOver.toScheme B S hS).map P) := by
  obtain ⟨U₀, a, haS, haE⟩ := hF.exists_atlas
  choose V u hu hurange hVaff using
    fun U => BigFppfOver.exists_affineOpen_restrict B S hS T U
  choose W p q hpb hQp using fun U => hπ (V U) (hVaff U) (yoneda.map (u U))
  refine exists_representing_over_of_openCover B S hS hQ hF.isSheaf π
    (V := V) (W := W) (u := u) (p := p) (q := q) hu ?_ hpb hQp ?_
  · intro y
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨U, by rw [hurange U]; exact hU⟩
  · intro Z k hk hkcov
    have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj T).affineOpens :=
      ⟨⟨⊥, isAffineOpen_bot _⟩⟩
    have hμ : max #((BigFppfOver.toScheme B S hS).obj T).affineOpens
        (max (2 ^ #((BigFppfOver.toScheme B S hS).obj U₀ : Type u))
          (2 ^ ((BigFppfOver.toScheme B S hS).obj U₀).size)) < B.cutoff :=
      max_lt (((BigFppfOver.toScheme B S hS).obj T).mk_affineOpens_le_size.trans_lt
          T.left.property)
        (Scheme.max_two_pow_mk_two_pow_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit
          U₀.left.property)
    have := hk
    refine B.contains_of_openCover_of_size_le hμ (le_max_left _ _) k hkcov fun U => ?_
    exact le_max_of_le_right (size_le_of_isOpenImmersion_of_atlas B S hS haS haE
      (isOpenImmersion_of_isPullback_yoneda_map B S hS (hu U) (hpb U)))

/-- **A property tested on the affine base changes holds on all of them.**

Let `P` be a property of morphisms of schemes which is Zariski local at the target and let
`f : F ⟶ G` be a morphism of algebraic spaces over `S`. If the base change of `f` along every
morphism from an *affine* object of the site is represented by an object of the site whose
projection to that object has `P`, then `f` is relatively representable and every represented
base change of it has `P`.

This is `AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace` with
the affineness of the representing objects dropped; see
`AlgebraicGeometry.Space.exists_representing_over_of_affineBaseChange`, of which it is the
version over every test object at once. Over a test object `T` the base change of `f` is again
an algebraic space, by `AlgebraicGeometry.isAlgebraicSpace_pullback`, and the hypothesis base
changes to it by `CategoryTheory.IsPullback.of_right'`. -/
theorem presheaf_of_affineBaseChange {P : MorphismProperty Scheme.{u}}
    (hP : IsZariskiLocalAtTarget P) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G}
    (h : ∀ Z : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ g : yoneda.obj Z ⟶ G,
        ∃ (W : BigFppfOver B S hS) (p : W ⟶ Z) (q : yoneda.obj W ⟶ F),
          IsPullback q (yoneda.map p) f g ∧ P ((BigFppfOver.toScheme B S hS).map p)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine MorphismProperty.relative.of_exists ?_
  intro T g
  have hpbT : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  have key : ∀ Z : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ g' : yoneda.obj Z ⟶ yoneda.obj T,
        ∃ (W : BigFppfOver B S hS) (p : W ⟶ Z) (m : yoneda.obj W ⟶ pullback f g),
          IsPullback m (yoneda.map p) (pullback.snd f g) g' ∧
            P ((BigFppfOver.toScheme B S hS).map p) := by
    intro Z hZ g'
    obtain ⟨W, p, q, sq, hPp⟩ := h Z hZ (g' ≫ g)
    exact ⟨W, p, _, IsPullback.of_right' sq hpbT, hPp⟩
  obtain ⟨Y, e, p, hp, hPp⟩ :=
    exists_representing_over_of_affineBaseChange B S hS hP
      (isAlgebraicSpace_pullback B S hS f g hF (isAlgebraicSpace_yoneda B S hS T) hG)
      (pullback.snd f g) key
  exact ⟨Y, e.inv ≫ pullback.fst f g, p, isPullback_of_iso_pullback_snd f g e hp, hPp⟩

/-- **A Zariski-local property tested on the affine base changes holds on all of them.**

If the base change of a morphism `f : F ⟶ G` of algebraic spaces over `S` along every morphism
from an *affine* object of the site is representable with `P` on its own represented base
changes, then `f` itself is representable with `P` on all of its represented base changes.

This is `AlgebraicGeometry.Space.presheaf_of_affineBaseChange` fed from the presheaf form of the
hypothesis: the representing object over an affine test object `Z` is the one that
`CategoryTheory.MorphismProperty.presheaf` of the base change supplies at the identity of
`yoneda.obj Z`.

It is the implication (3) ⇒ (1) of Stacks 03M4, for an arbitrary `P`.

Compare `CategoryTheory.MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd`, the same
passage with no restriction on the test objects, which therefore needs neither glueing nor a
locality hypothesis on `P`. -/
theorem presheaf_of_affine_presheaf_pullback_snd {P : MorphismProperty Scheme.{u}}
    (hP : IsZariskiLocalAtTarget P) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G}
    (h : ∀ Z : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ g : yoneda.obj Z ⟶ G,
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine presheaf_of_affineBaseChange B S hS hP hF hG fun Z hZ g => ?_
  have hq := h Z hZ g
  have step := (hq.rep.isPullback (𝟙 (yoneda.obj Z))).paste_horiz
    (IsPullback.of_hasPullback f g)
  rw [Category.id_comp] at step
  exact ⟨_, _, _, step, hq.property_snd _⟩

/-- **A Zariski-local property on the members of a Zariski covering gives it on an affine base
change.**

Let `f : F ⟶ G` be a morphism of algebraic spaces over `S` which is representable with `P` over
the members of some Zariski covering of `G`, for a property `P` of morphisms of schemes which is
Zariski local at the target. Then the base change of `f` along a morphism from an *affine* object
`Z` of the site is represented by an object of the site whose projection to `Z` has `P`.

The members of the covering pull back to open subobjects of `Z` covering it, by
`AlgebraicGeometry.Space.exists_mem_range_snd_of_zariskiCover`, and the base change of `f` over
each of them is represented with `P` by the hypothesis. The scheme under `Z` is affine, hence
quasi-compact, so finitely many of those subobjects already cover it, and
`AlgebraicGeometry.Space.exists_representing_over_of_openCover` glues the corresponding finitely
many charts over `Z`. That the glueing is finite is what makes the containment available: the
index type of the covering is arbitrary, so its charts have no uniform size bound, whereas a
finite family is covered by the cofinality bound of
`AlgebraicGeometry.BigFppfSite.contains_of_openCover` — or by
`AlgebraicGeometry.BigFppfSite.contains_of_isEmpty`, when the finite subcovering is empty and
`Z` therefore has no points. -/
theorem exists_representing_of_zariskiCover_of_isAffine {P : MorphismProperty Scheme.{u}}
    (hP : IsZariskiLocalAtTarget P) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G}
    {I : Type u} {U : I → Subfunctor G} (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.snd f (U i).ι))
    {Z : BigFppfOver B S hS} (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (g : yoneda.obj Z ⟶ G) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ Z) (q : yoneda.obj W ⟶ F),
      IsPullback q (yoneda.map p) f g ∧ P ((BigFppfOver.toScheme B S hS).map p) := by
  have hZ' := hZ
  have hpbT : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  -- the base change of `f` over the test object has a chart with `P` over each member
  have key : ∀ i, ∃ (W : BigFppfOver B S hS) (p : W ⟶ (hU.1 i).2.rep.pullback g)
      (q : yoneda.obj W ⟶ pullback f g),
      IsPullback q (yoneda.map p) (pullback.snd f g)
        (yoneda.map ((hU.1 i).2.rep.snd g)) ∧
      P ((BigFppfOver.toScheme B S hS).map p) := by
    intro i
    have step := ((h i).rep.isPullback ((hU.1 i).2.rep.fst g)).paste_horiz
      (IsPullback.of_hasPullback f (U i).ι)
    rw [((hU.1 i).2.rep.isPullback g).w] at step
    exact ⟨_, _, _, IsPullback.of_right' step hpbT, (h i).property_snd _⟩
  choose W p q hpb hPp using key
  have hu : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map ((hU.1 i).2.rep.snd g)) :=
    fun i => (hU.1 i).2.property_snd g
  -- a finite subcovering of the quasi-compact test object
  obtain ⟨σ, hσ⟩ := (isCompact_univ
      (X := (BigFppfOver.toScheme B S hS).obj Z)).elim_finite_subcover
    (fun i => Set.range ((BigFppfOver.toScheme B S hS).map ((hU.1 i).2.rep.snd g)))
    (fun i => by
      have := hu i
      exact ((BigFppfOver.toScheme B S hS).map
        ((hU.1 i).2.rep.snd g)).isOpenEmbedding.isOpen_range)
    fun y _ => Set.mem_iUnion.2 (exists_mem_range_snd_of_zariskiCover B S hS hU g y)
  have hσcov : ∀ y : (BigFppfOver.toScheme B S hS).obj Z, ∃ i : {i // i ∈ σ},
      y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hU.1 i.1).2.rep.snd g)) := by
    intro y
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (hσ (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, hy⟩
  have hcontains : ∀ (Z' : Scheme.{u}) (k : ∀ i : {i // i ∈ σ},
      (BigFppfOver.toScheme B S hS).obj (W i.1) ⟶ Z'),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (k i)) →
      (∀ z : Z', ∃ i, z ∈ Set.range (k i)) → B.Contains Z' := by
    intro Z' k hk hkcov
    rcases isEmpty_or_nonempty {i // i ∈ σ} with hemp | hne
    · exact B.contains_of_isEmpty ⟨fun z => hemp.false (hkcov z).choose⟩
    · have := hk
      exact B.contains_of_openCover
        (lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite _) B.aleph0_lt_cutoff_cof.le)
        k hkcov fun i => (W i.1).left.property
  obtain ⟨Y₀, e, p₀, hp₀, hPp₀⟩ := exists_representing_over_of_openCover B S hS hP
    (BigFppfOver.isSheaf_pullback_yoneda_obj f g hF.isSheaf hG.isSheaf)
    (pullback.snd f g)
    (V := fun i : {i // i ∈ σ} => (hU.1 i.1).2.rep.pullback g) (W := fun i => W i.1)
    (u := fun i => (hU.1 i.1).2.rep.snd g) (p := fun i => p i.1) (q := fun i => q i.1)
    (fun i => hu i.1) hσcov (fun i => hpb i.1) (fun i => hPp i.1) hcontains
  exact ⟨Y₀, p₀, e.inv ≫ pullback.fst f g, isPullback_of_iso_pullback_snd f g e hp₀, hPp₀⟩

/-- **A Zariski-local property on the members of a Zariski covering holds everywhere.**

If a morphism `f : F ⟶ G` of algebraic spaces over `S` is representable with `P` over the
members of some Zariski covering of `G`, for a property `P` of morphisms of schemes which is
Zariski local at the target, then `f` is representable with `P` on all of its represented base
changes.

This is `AlgebraicGeometry.Space.exists_representing_of_zariskiCover_of_isAffine` fed into
`AlgebraicGeometry.Space.presheaf_of_affineBaseChange`: the Zariski covering is glued over the
affine test objects, and the affine test objects then suffice for all of them.

It is the implication (5) ⇒ (1) of Stacks 03M4, for an arbitrary `P`. -/
@[sga "3 XI 3.4" "special case"]
theorem presheaf_of_zariskiCover_presheaf_pullback_snd {P : MorphismProperty Scheme.{u}}
    (hP : IsZariskiLocalAtTarget P) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G}
    {I : Type u} {U : I → Subfunctor G} (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.snd f (U i).ι)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_of_affineBaseChange B S hS hP hF hG fun _ hZ g =>
    exists_representing_of_zariskiCover_of_isAffine B S hS hP hF hG hU h hZ g

/-! ### Stacks 03M4 -/

/-- **The five local criteria for a representable morphism with a Zariski-local property**, which
is Stacks 03M4 for an arbitrary property `P` of morphisms of schemes which is Zariski local at the
target, conditional on effective descent for `P` along a surjective étale morphism of the site.

For a morphism `f : F ⟶ G` of algebraic spaces over `S` the following are equivalent: `f` is
representable with `P` on its represented base changes; so is every base change of `f` to a
representable presheaf; so is every base change of `f` to an *affine* object of the site; there is
one surjective étale scheme chart of `G` over which the base change of `f` is representable with
`P`; and there is a Zariski covering of `G` over whose members the base changes of `f` are
representable with `P`.

Only the implication out of the fourth condition uses `hdesc`; the cycle
`(1) ⇔ (2) ⇒ (3) ⇒ (1)` and the pair `(1) ⇒ (5) ⇒ (1)` are unconditional. The two
instantiations below are Stacks 03M4 for open immersions and for immersions; the
closed-immersion one is
`AlgebraicGeometry.Space.isClosedImmersion_tfae` of
`StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionLocalCriterion`, where `hdesc` is
discharged. -/
theorem presheaf_tfae (P : MorphismProperty Scheme.{u}) (hP : IsZariskiLocalAtTarget P)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS P)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    List.TFAE [
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f,
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor G),
        IsZariskiCover B S hS I U ∧
        ∀ i, (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.snd f (U i).ι))
    ] := by
  have := hP
  have hRI : (P.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  tfae_have 1 ↔ 2 :=
    MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ f
  tfae_have 2 → 3 := fun h Z g _ => h Z g
  tfae_have 3 → 1 := fun h =>
    presheaf_of_affine_presheaf_pullback_snd B S hS hP hF hG fun Z hZ g => h Z g hZ
  tfae_have 1 → 4 := fun h => exists_surjective_etale_chart_of_presheaf B S hS P hG h
  tfae_have 4 → 1 := fun ⟨_, _, hs, he, hq⟩ =>
    presheaf_of_surjectiveEtaleChart hdesc hF.isSheaf hG.isSheaf hs he hq
  tfae_have 1 → 5 := fun h => exists_isZariskiCover_of_presheaf B S hS P hG h
  tfae_have 5 → 1 := fun ⟨_, _, hU, h⟩ =>
    presheaf_of_zariskiCover_presheaf_pullback_snd B S hS hP hF hG hU h
  tfae_finish

/-- **Stacks 03M4 for open immersions**, conditional on effective descent for open immersions of
schemes along a surjective étale morphism of the site.

A morphism of algebraic spaces over `S` is an open immersion exactly when every one of its base
changes to a representable presheaf is, exactly when every one of its base changes to an affine
object of the site is, exactly when its base change along one surjective étale scheme chart of the
target is, and exactly when its base changes along the members of some Zariski covering of the
target are.

The hypothesis `hdesc` is Stacks 03I2 for the class of open immersions of schemes, and it is used
only for the implication out of the fourth condition; no declaration here carries the tag 03M4. -/
theorem isOpenImmersion_tfae
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    List.TFAE [
      IsOpenImmersion B S hS f,
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsOpenImmersion B S hS (pullback.snd f g)),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsOpenImmersion B S hS (pullback.snd f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsOpenImmersion B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor G),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsOpenImmersion B S hS (pullback.snd f (U i).ι))
    ] :=
  presheaf_tfae B S hS _ _root_.AlgebraicGeometry.isOpenImmersion_isZariskiLocalAtTarget
    hdesc hF hG f

/-- **Stacks 03M4 for immersions**, conditional on effective descent for immersions of schemes
along a surjective étale morphism of the site.

A morphism of algebraic spaces over `S` is an immersion exactly when every one of its base changes
to a representable presheaf is, exactly when every one of its base changes to an affine object of
the site is, exactly when its base change along one surjective étale scheme chart of the target is,
and exactly when its base changes along the members of some Zariski covering of the target are.

The hypothesis `hdesc` is Stacks 03I2 for the class of immersions of schemes, and it is used only
for the implication out of the fourth condition; no declaration here carries the tag 03M4. -/
theorem isImmersion_tfae
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    List.TFAE [
      IsImmersion B S hS f,
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsImmersion B S hS (pullback.snd f g)),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsImmersion B S hS (pullback.snd f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsImmersion B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor G),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsImmersion B S hS (pullback.snd f (U i).ι))
    ] :=
  presheaf_tfae B S hS _ inferInstance hdesc hF hG f

/-! ### Stacks 03WM -/

/-- **Stacks 03WM, (2) implies (1)**, unconditionally.

A quasi-affine morphism of algebraic spaces over `S` in the sense of Stacks 03WL is relatively
representable and all of its represented base changes are quasi-affine morphisms of schemes.

This is `AlgebraicGeometry.Space.presheaf_of_isQuasiAffineHom` with its representability
hypothesis discharged. Quasi-affineness supplies the chart over an affine test object directly:
the representing object has quasi-affine underlying scheme, so its projection to the affine test
object is a quasi-affine morphism by `AlgebraicGeometry.isQuasiAffineHom_of_isQuasiAffine`, and
quasi-affineness of a morphism of schemes is Zariski local at the target, so
`AlgebraicGeometry.Space.presheaf_of_affineBaseChange` glues those charts over an arbitrary test
object. -/
theorem presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsQuasiAffineHom B S hS f) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine presheaf_of_affineBaseChange B S hS inferInstance hX hY fun Z hZ g => ?_
  obtain ⟨W, hWqa, ⟨e⟩⟩ := hf ⟨Z, hZ⟩ g
  refine ⟨W, yoneda.preimage (e.hom ≫ pullback.fst g f), e.hom ≫ pullback.snd g f, ?_, ?_⟩
  · rw [Functor.map_preimage]
    exact (IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e rfl rfl).flip
  · exact isQuasiAffineHom_of_isQuasiAffine _ hWqa hZ

/-- **Stacks 03WM, (4) implies (1)**, unconditionally.

A morphism of algebraic spaces over `S` which is quasi-affine over the members of some Zariski
covering of its target is relatively representable with quasi-affine represented base changes.

The implication (2) ⇒ (1) above turns each member of the covering into the presheaf form, up to
the symmetry of the fibre product, and
`AlgebraicGeometry.Space.presheaf_of_zariskiCover_presheaf_pullback_snd` glues over the
covering. -/
theorem presheaf_isQuasiAffineHom_of_zariskiCover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} {I : Type u} {U : I → Subfunctor Y}
    (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, IsQuasiAffineHom B S hS (pullback.fst (U i).ι f)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso
    (P := @_root_.AlgebraicGeometry.IsQuasiAffineHom.{u})
  have hRI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine presheaf_of_zariskiCover_presheaf_pullback_snd B S hS inferInstance hX hY hU
    fun i => ?_
  have hi := presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace B S hS
    (isAlgebraicSpace_pullback B S hS (U i).ι f (hU.1 i).1 hX hY) (hU.1 i).1 (h i)
  rw [← pullbackSymmetry_hom_comp_fst (f := f) (g := (U i).ι)]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hi

/-- **Stacks 03WM**, conditional on effective descent for quasi-affine morphisms of schemes along
a surjective étale morphism of the site.

For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the following four conditions
are equivalent: `f` is relatively representable and all of its represented base changes are
quasi-affine morphisms of schemes; `f` is quasi-affine in the sense of Stacks 03WL; there is a
surjective étale scheme chart of `Y` over which the base change of `f` is represented by an
object of the site with quasi-affine projection to that chart; and there is a Zariski covering of
`Y` over whose members `f` is quasi-affine.

The only input not supplied is `hdesc`, Stacks 03I2 for the class of quasi-affine morphisms of
schemes, and it is used only for the implication out of the third condition. Base change
stability of quasi-affineness, Stacks 01SO, which the implication (3) ⇒ (1) also consumes, is
available as the instance `AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange`. Since
`hdesc` remains, no declaration here carries the tag 03WM. -/
theorem isQuasiAffineHom_tfae
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f,
      IsQuasiAffineHom B S hS f,
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
          (W : BigFppfOver B S hS)
          (e : yoneda.obj W ≅ pullback g f),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        _root_.AlgebraicGeometry.IsQuasiAffineHom
          ((BigFppfOver.toScheme B S hS).map
            (yoneda.preimage (e.hom ≫ pullback.fst g f)))),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsQuasiAffineHom B S hS (pullback.fst (U i).ι f))
    ] := by
  tfae_have 1 → 2 := fun h => isQuasiAffineHom_of_presheaf h
  tfae_have 2 → 1 := fun h =>
    presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace B S hS hX hY h
  tfae_have 1 → 3 := fun h => exists_etaleChart_isQuasiAffineHom_of_presheaf hY h
  tfae_have 3 → 1 := fun ⟨_, _, _, e, hs, he, hq⟩ =>
    presheaf_isQuasiAffineHom_of_surjectiveEtaleChart inferInstance hdesc hX hY e hs he hq
  tfae_have 2 → 4 := fun h => exists_isZariskiCover_isQuasiAffineHom hY h
  tfae_have 4 → 1 := fun ⟨_, _, hU, h⟩ =>
    presheaf_isQuasiAffineHom_of_zariskiCover B S hS hX hY hU h
  tfae_finish

end AlgebraicGeometry.Space

end
