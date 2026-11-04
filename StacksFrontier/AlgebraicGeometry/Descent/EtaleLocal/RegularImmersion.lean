module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.ZariskiToEtale
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksCore.Tactic.StacksAttribute

/-!
# The regularity conditions on an immersion are étale local on the target

Let `i : Z ⟶ X` be an immersion of schemes.  Stacks tag 0694 asserts that each of the three
conditions Koszul-regular, `H₁`-regular and quasi-regular of Stacks tag 063J is local on the
target for the fpqc topology, with no finiteness hypothesis on `i`.  The formalization of that
tag in `StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc` carries
quasi-compactness of `i` in all three of its clauses.  This file removes that qualifier at the
price of shrinking the topology from fpqc to étale, which is what the applications to algebraic
spaces of Stacks tags 06BM and 06BN need.

The tag as stated — for the fpqc topology, and for an arbitrary morphism — is false; see the
module docstring of
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcOfImmersion` for the
counterexample.  The descent step this file uses, Stacks tag 02YM, is available for the whole
fppf topology and not just the étale one, so the argument below in fact gives the three clauses
for the fppf topology; that stronger statement is
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFppf`, and since an étale
covering is an fppf covering the clauses here are a special case of it.  They are kept as
separate declarations because they are what the algebraic-spaces applications cite, and because
`AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_descendsAlong_fppf` below is used
elsewhere.

The quasi-compactness in the fpqc statements is consumed in exactly one place: descending the
property of *being an immersion* along a surjective flat quasi-compact morphism, which is
Stacks tag 02L8 and is known only for quasi-compact immersions.  Being an immersion with no
finiteness hypothesis descends along a surjective flat morphism *locally of finite presentation*
— that is Stacks tag 02YM, `Stacks.Descent.isImmersion_descendsAlong_fppf` — because such a
morphism is open, so the coborder of the range descends.  Every other ingredient of the fpqc
argument is already free of quasi-compactness: the affine criteria of Stacks tags 063D and 063G
are applied to the canonical closed factor of the immersion, and a closed immersion is affine,
hence quasi-compact, whatever the immersion it factors.

## Main results

* `AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_descendsAlong_fppf`: a property of
  morphisms of schemes which is Zariski local on the target, stable under flat base change and
  descends along surjective flat morphisms locally of finite presentation is étale local on the
  target.
* `AlgebraicGeometry.isLocalAtTarget_immersionProperty_etale`: the uniform form of Stacks tag
  0694 for the étale topology, with no quasi-compactness.
* `AlgebraicGeometry.isLocalAtTarget_koszulRegularImmersion_etale`,
  `AlgebraicGeometry.isLocalAtTarget_h1RegularImmersion_etale` and
  `AlgebraicGeometry.isLocalAtTarget_quasiRegularImmersion_etale`: **Stacks tag 0694** for the
  étale topology, the three clauses, each for the bare regularity condition.

## Implementation notes

The étale criterion is the target half of
`AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_zariski_of_descent` with the descent
hypothesis in cartesian-square form instead of the composite form.  The composite form asks for
`P (f ≫ g)` from `P f` and `g` étale, which no condition on immersions satisfies — composing an
immersion with an étale morphism is not an immersion — so that criterion cannot be applied here;
the descent itself is available, as fppf descent, and is what this version consumes.  The
reduction of an étale covering family to a single surjective étale morphism onto an open of the
target is unchanged and is `AlgebraicGeometry.exists_surjective_etale_onto_openImage`.

The three small `MorphismProperty` manipulations at the start are the ones used by the fpqc
argument, which keeps them private to its own module.

## References

* [Stacks Project, Lemma 35.26.1 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Lemma 35.21.1 (Tag 02L8)](https://stacks.math.columbia.edu/tag/02L8)
* [Stacks Project, Lemma 35.23.6 (Tag 02YM)](https://stacks.math.columbia.edu/tag/02YM)
* [Stacks Project, Lemma 34.2.6 (Tag 02KP)](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Definition 31.21.4 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe u

/-! ### Transport of a property across a cartesian square -/

/-- A property stable under flat base change holds for the projection of a pullback square along
a flat morphism, if it holds for the other side. -/
private theorem of_isPullback_of_flat (P : MorphismProperty Scheme.{u})
    [Stacks.Descent.IsStableUnderFlatBaseChange P] {W X Y Z : Scheme.{u}} {fst : W ⟶ X}
    {snd : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} [Flat g] (h : IsPullback fst snd f g) (hf : P f) :
    P snd :=
  (Stacks.Descent.IsStableUnderFlatBaseChange.isStableUnderBaseChangeAlong
    (P := P) g).of_isPullback h hf

/-! ### Upgrading Zariski locality to étale locality through fppf descent -/

/-- A property of morphisms of schemes which is Zariski local on the target, stable under flat
base change and descends along surjective flat morphisms locally of finite presentation is étale
local on the target.

This is the fppf-descent form of
`AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_zariski_of_descent`:  a member of an étale
covering family factors as a surjective étale morphism onto the open subscheme which is its
image, the opens so obtained cover the target, and over each of them the surjective étale
morphism is removed by the descent hypothesis, an étale morphism being flat and locally of finite
presentation. -/
theorem isLocalAtTarget_etalePrecoverage_of_descendsAlong_fppf (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [Stacks.Descent.IsStableUnderFlatBaseChange P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)] :
    MorphismProperty.IsLocalAtTarget P Scheme.etalePrecoverage := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff fun X Y f R hR =>
    ⟨fun hf U g hg _ => ?_, fun h => ?_⟩
  · have _ : Etale g := hR.2 ‹_›
    exact of_isPullback_of_flat P (IsPullback.of_hasPullback f g) hf
  · obtain ⟨ι, Z, fam, rfl⟩ := R.exists_eq_ofArrows
    have hR' : Presieve.ofArrows Z fam ∈ Scheme.precoverage (@Etale.{u}) Y := hR
    obtain ⟨hjs, het⟩ := (Scheme.ofArrows_mem_precoverage_iff (@Etale.{u})).mp hR'
    choose j hj using hjs
    refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := P) fun y => ?_
    have hEt : Etale (fam (j y)) := het _
    obtain ⟨O, gO, hmem, hsurjO, hEtO, hfac⟩ :=
      exists_surjective_etale_onto_openImage (fam (j y))
    refine ⟨O, hmem y (hj y), ?_⟩
    have _ : Etale gO := hEtO
    have htot : IsPullback (pullback.snd f (fam (j y))) (pullback.fst f (fam (j y)))
        (gO ≫ O.ι) f := by
      rw [hfac]
      exact (IsPullback.of_hasPullback f (fam (j y))).flip
    have hsnd : P (pullback.snd f O.ι) :=
      MorphismProperty.of_isPullback_of_descendsAlong
        (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
        (IsPullback.of_bot' htot (IsPullback.of_hasPullback f O.ι).flip)
        ⟨⟨hsurjO, inferInstance⟩, inferInstance⟩ (h _ ⟨j y⟩)
    have hres : P (f ∣_ O.ι.opensRange) :=
      (MorphismProperty.arrow_mk_iso_iff P (morphismRestrictOpensRange f O.ι)).mpr hsnd
    rwa [Scheme.Opens.opensRange_ι] at hres

/-! ### The regularity conditions, with no quasi-compactness -/

variable {Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop}
variable {Pred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i], Prop}

/-- **The descent step over an affine base, with an affine covering scheme, for an immersion
that is already known to be one.**  This is
`AlgebraicGeometry.immersionProperty_inf_quasiCompact_of_pullbackSnd_of_isAffine` with the
quasi-compactness of `f` replaced by a hypothesis that `f` is an immersion:  that hypothesis is
all the quasi-compact statement extracted from the quasi-compactness, since the affine-open
condition is read off the canonical *closed* factor of `f`, which is quasi-compact of itself. -/
theorem immersionProperty_of_pullbackSnd_of_isAffine
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    [(immersionProperty Pred).RespectsIso]
    [Stacks.Descent.IsStableUnderFlatBaseChange (immersionProperty Pred)]
    {S X Y : Scheme.{u}} [IsAffine S] [IsAffine X] (c : X ⟶ S) (f : Y ⟶ S)
    [Surjective c] [Flat c] (himm : IsImmersion f)
    (hf : immersionProperty Pred (pullback.snd f c)) :
    immersionProperty Pred f := by
  have _ := himm
  refine ⟨himm, (hPred f f.coborderRange f.liftCoborder f.liftCoborder_ι).mpr ?_⟩
  refine kerGeneratedBy_of_forall_affine_pullback hSeq f.liftCoborder fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    f.coborderRange.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  change f.coborderRange.toScheme.Opens at U
  have _ : IsAffine U.toScheme := hU
  refine ⟨⟨U, hU⟩, hxU, ?_⟩
  have hc2 : IsPullback (𝟙 Y) f.liftCoborder f f.coborderRange.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hvsq := (IsPullback.of_hasPullback f.liftCoborder U.ι).paste_horiz hc2
  have _ : IsAffine (pullback c (U.ι ≫ f.coborderRange.ι)) := inferInstance
  have hbase : immersionProperty Pred
      (pullback.snd f (pullback.snd c (U.ι ≫ f.coborderRange.ι) ≫
        (U.ι ≫ f.coborderRange.ι))) := by
    rw [← pullback.condition]
    exact pullbackSnd_of_factor _ f c (pullback.fst c (U.ι ≫ f.coborderRange.ι)) hf
  obtain ⟨_, hireg⟩ := of_pullbackSnd_of_isPullback (immersionProperty Pred)
    ((IsPullback.of_hasPullback (pullback.snd f.liftCoborder U.ι)
      (pullback.snd c (U.ι ≫ f.coborderRange.ι))).paste_horiz hvsq) hbase
  exact kerGeneratedBy_of_faithfullyFlat_cover hSeq hdesc (pullback.snd f.liftCoborder U.ι)
    (pullback.snd c (U.ι ≫ f.coborderRange.ι))
    ((pred_iff_kerGeneratedBy_of_isClosedImmersion hSeq hPred _).mp hireg)

/-- **The descent step over an affine base, for an immersion that is already known to be one.**
The covering scheme may be taken affine:  it is quasi-compact, so some affine scheme maps onto it
by a surjective local isomorphism, and precomposing the covering morphism with that keeps it
surjective and flat while the hypothesis is carried along by flat base change. -/
theorem immersionProperty_of_pullbackFst_of_quasiCompact
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    [(immersionProperty Pred).RespectsIso]
    [Stacks.Descent.IsStableUnderFlatBaseChange (immersionProperty Pred)]
    {R : CommRingCat.{u}} {X Y : Scheme.{u}} (c : X ⟶ Spec R) (f : Y ⟶ Spec R)
    [Surjective c] [Flat c] [QuasiCompact c] (himm : IsImmersion f)
    (hf : immersionProperty Pred (pullback.fst c f)) :
    immersionProperty Pred f := by
  have _ : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have _ := Flat.instIsMultiplicativeScheme.{u}.toContainsIdentities
  have _ := IsLocalIso.instIsMultiplicativeScheme.{u}.toContainsIdentities
  have _ : CompactSpace X := (quasiCompact_iff_compactSpace c).mp ‹QuasiCompact c›
  obtain ⟨T, p, hps, hpl, _⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have _ : Surjective p := hps
  have _ : Flat p := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ p hpl
  exact immersionProperty_of_pullbackSnd_of_isAffine hSeq hdesc hPred (p ≫ c) f himm
    (pullbackSnd_of_factor _ f c p
      (pullbackSnd_of_isPullback _ (IsPullback.of_hasPullback c f).flip hf))

/-- **The descent step over an affine base along a surjective flat covering locally of finite
presentation.**  Such a covering is an open map, so a quasi-compact open of its source already
maps onto the affine base; restricting to one reduces the claim to
`AlgebraicGeometry.immersionProperty_of_pullbackFst_of_quasiCompact`. -/
theorem immersionProperty_of_pullbackFst_fppf
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    [(immersionProperty Pred).RespectsIso]
    [Stacks.Descent.IsStableUnderFlatBaseChange (immersionProperty Pred)]
    {R : CommRingCat.{u}} {X Y : Scheme.{u}} (c : X ⟶ Spec R) (f : Y ⟶ Spec R)
    [Surjective c] [Flat c] [LocallyOfFinitePresentation c] (himm : IsImmersion f)
    (hf : immersionProperty Pred (pullback.fst c f)) :
    immersionProperty Pred f := by
  obtain ⟨V : X.Opens, hV, e⟩ := c.isOpenMap.exists_opens_image_eq_of_prespectralSpace
    c.continuous (by simp) isOpen_univ isCompact_univ
  have _ : Surjective (V.ι ≫ c) :=
    ⟨fun x ↦ have ⟨y, hyV, e⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, e⟩⟩
  have _ : QuasiCompact (V.ι ≫ c) :=
    (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)
  refine immersionProperty_of_pullbackFst_of_quasiCompact hSeq hdesc hPred (V.ι ≫ c) f himm ?_
  rw [← pullbackRightPullbackFstIso_inv_fst c f V.ι,
    (immersionProperty Pred).cancel_left_of_respectsIso]
  exact of_isPullback_of_flat _ (IsPullback.of_hasPullback V.ι (pullback.fst c f)).flip hf

/-- **Descent of the bare regularity condition along a surjective flat morphism locally of finite
presentation.**  Being an immersion descends along such a morphism by Stacks tag 02YM, and the
affine-open condition descends by the affine dictionary of Stacks tag 0694. -/
theorem immersionProperty_descendsAlong_fppf
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] {ι : Type u} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i) :
    MorphismProperty.DescendsAlong (immersionProperty Pred)
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := by
  have _ := immersionProperty_respectsIso hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isStableUnderFlatBaseChange hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isZariskiLocalAtTarget hSeq hPred hglue (Pred := Pred)
  have _ := Stacks.Descent.isImmersion_descendsAlong_fppf.{u}
  have _ : MorphismProperty.IsStableUnderBaseChange
      (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) := .inf
  have _ : MorphismProperty.IsStableUnderBaseChange
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := .inf
  refine IsZariskiLocalAtTarget.descendsAlong (immersionProperty Pred)
    (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) fun c f hc hfst => ?_
  have _ : Surjective c := hc.1.1
  have _ : Flat c := hc.1.2
  have _ : LocallyOfFinitePresentation c := hc.2
  exact immersionProperty_of_pullbackFst_fppf hSeq hdesc hPred c f
    (MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := (@IsImmersion : MorphismProperty Scheme.{u}))
      (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      hc hfst.1) hfst

/-- **The uniform form of Stacks tag 0694 for the étale topology.**  A condition on immersions
that is read off the kernel of a closed factor through any open in which the immersion is closed,
whose family predicate is stable under flat ring maps and whose ideal-theoretic form descends
along faithfully flat ring maps, and which glues along open covers of the target, is étale local
on the target — with no quasi-compactness. -/
theorem isLocalAtTarget_immersionProperty_etale
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] {ι : Type u} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i) :
    MorphismProperty.IsLocalAtTarget (immersionProperty Pred) Scheme.etalePrecoverage := by
  have _ := immersionProperty_respectsIso hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isStableUnderFlatBaseChange hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isZariskiLocalAtTarget hSeq hPred hglue (Pred := Pred)
  have _ := immersionProperty_descendsAlong_fppf hSeq hdesc hPred hglue (Pred := Pred)
  exact isLocalAtTarget_etalePrecoverage_of_descendsAlong_fppf _

/-! ### The three clauses of Stacks tag 0694 for the étale topology -/

/-- **Stacks Project, Tag 0694, the Koszul-regular clause, for the étale topology.** Being a
Koszul-regular immersion of schemes is local on the target for the étale topology. -/
@[stacks 0694 "koszul_regular, étale topology"]
theorem isLocalAtTarget_koszulRegularImmersion_etale :
    MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f, @IsKoszulRegularImmersion _ _ f hf)
      Scheme.etalePrecoverage.{u} :=
  isLocalAtTarget_immersionProperty_etale
    (Seq := fun f => Koszul.IsKoszulRegular f)
    (Pred := fun i => IsKoszulRegularImmersion i)
    isKoszulRegular_of_ringHomFlat
    (fun φ hφ I => (Koszul.regular_ideals_of_faithfullyFlat φ hφ I).1)
    (by
      intro Z X i _ V jV _ hij
      exact (isKoszulRegularImmersion_iff_of_open i V jV hij).trans
        (isKoszulRegularIdealSheaf_iff_kerGeneratedBy jV))
    isKoszulRegularImmersion_of_resLE

/-- **Stacks Project, Tag 0694, the `H₁`-regular clause, for the étale topology.** Being an
`H₁`-regular immersion of schemes is local on the target for the étale topology. -/
@[stacks 0694 "h1_regular, étale topology"]
theorem isLocalAtTarget_h1RegularImmersion_etale :
    MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f, @IsH1RegularImmersion _ _ f hf)
      Scheme.etalePrecoverage.{u} :=
  isLocalAtTarget_immersionProperty_etale
    (Seq := fun f => Koszul.IsH1Regular f)
    (Pred := fun i => IsH1RegularImmersion i)
    isH1Regular_of_ringHomFlat
    (fun φ hφ I => (Koszul.regular_ideals_of_faithfullyFlat φ hφ I).2.1)
    (by
      intro Z X i _ V jV _ hij
      exact (isH1RegularImmersion_iff_of_open i V jV hij).trans
        (isH1RegularIdealSheaf_iff_kerGeneratedBy jV))
    isH1RegularImmersion_of_resLE

/-- **Stacks Project, Tag 0694, the quasi-regular clause, for the étale topology.** Being a
quasi-regular immersion of schemes is local on the target for the étale topology. -/
@[stacks 0694 "quasi_regular, étale topology"]
theorem isLocalAtTarget_quasiRegularImmersion_etale :
    MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f,
        @RegularIdealSheaf.IsQuasiRegularImmersion _ _ f hf)
      Scheme.etalePrecoverage.{u} :=
  isLocalAtTarget_immersionProperty_etale
    (Seq := fun {A} _ _ f => RingTheory.Sequence.IsQuasiRegular A (List.ofFn f))
    (Pred := fun i => RegularIdealSheaf.IsQuasiRegularImmersion i)
    isQuasiRegular_of_ringHomFlat
    (fun φ hφ I h => (Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy I).mp
      ((Koszul.regular_ideals_of_faithfullyFlat φ hφ I).2.2
        ((Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy (I.map φ)).mpr h)))
    (by
      intro Z X i _ V jV _ hij
      exact (RegularIdealSheaf.isQuasiRegularImmersion_iff_of_open i V jV hij).trans
        (isQuasiRegularIdealSheaf_iff_kerGeneratedBy jV))
    RegularIdealSheaf.isQuasiRegularImmersion_of_resLE

end AlgebraicGeometry

end
