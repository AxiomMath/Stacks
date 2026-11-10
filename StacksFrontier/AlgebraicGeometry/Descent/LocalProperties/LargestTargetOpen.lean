module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The largest open of the target on which a morphism has a local property

For a property of morphisms of schemes local on the target in the fppf, syntomic, smooth or
étale topology, there is a largest open of the target over which the morphism has the
property, and it is compatible with base change along a morphism of the corresponding class.

## Main definitions

* `AlgebraicGeometry.IsDescentMorphismClass` names the four classes of covering morphisms.
* `AlgebraicGeometry.largestTargetOpen` is the supremum of the opens of the target over
  which a morphism has the property.

## Main results

* `AlgebraicGeometry.property_largestTargetOpen`: the property holds over the largest open.
* `AlgebraicGeometry.le_largestTargetOpen`: maximality of the largest open.
* `AlgebraicGeometry.range_le_largestTargetOpen`: part (1) of the source.
* `AlgebraicGeometry.largestTargetOpen_baseChange`: part (2) of the source.
* `AlgebraicGeometry.largestTargetOpen_covering`: part (3) of the source.

## Implementation notes

Each topology is represented by the precoverage of its class of covering morphisms; for the
fppf topology this is Mathlib's fppf precoverage. The phrase "flat and locally of finite
presentation, syntomic, smooth, or étale" is read with the chosen topology, as in the cited
base-change lemma. The open is constructed as a supremum rather than as the equivalent union
of images of testing morphisms.

The name distinguishes this open of the *target* from `AlgebraicGeometry.largestOpen`, the
largest open of the *source* on which a source-local property holds (Tag 0CEY).

## References

* [Stacks Project, Tag 06QP](https://stacks.math.columbia.edu/tag/06QP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The class of morphisms defining one of the four topologies of this statement: flat and
locally of finite presentation, syntomic, smooth, or étale. -/
abbrev IsDescentMorphismClass (Q : MorphismProperty Scheme.{u}) : Prop :=
  (Q = ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})) ∨
  (Q = (@Syntomic : MorphismProperty Scheme.{u})) ∨
  (Q = (@Smooth : MorphismProperty Scheme.{u})) ∨
  (Q = (@Etale : MorphismProperty Scheme.{u}))

/-- Every open immersion belongs to each of the four classes. -/
private theorem openImmersion_mem (Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Q f := by
  rcases hQ with hQ | hQ | hQ | hQ <;> rw [hQ]
  · exact ⟨inferInstance, inferInstance⟩
  · exact syntomic_of_isOpenImmersion f
  all_goals infer_instance

/-- Base change along a morphism of the chosen class preserves a property local on the
target for that class. -/
private theorem pullback_property (P Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) [P.IsLocalAtTarget (Scheme.precoverage Q)]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : Q g) (hf : P f) :
    P (pullback.snd f g) := by
  rcases hQ with hQ | hQ | hQ | hQ
  · subst Q
    have : P.IsLocalAtTarget Scheme.fppfPrecoverage := by
      change P.IsLocalAtTarget (Scheme.precoverage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}))
      infer_instance
    exact pullbackSnd_of_flat_locallyOfFinitePresentation P f g hf hg.1 hg.2
  · subst Q
    exact pullbackSnd_of_syntomic P f g hf hg
  · subst Q
    exact pullbackSnd_of_smooth P f g hf hg
  · subst Q
    have : P.IsLocalAtTarget Scheme.etalePrecoverage := by
      change P.IsLocalAtTarget (Scheme.precoverage (@Etale : MorphismProperty Scheme.{u}))
      infer_instance
    exact pullbackSnd_of_etale P f g hf hg

/-- A property that holds over an open holds over the restriction of that open to a larger
one. -/
private theorem restrict_of_subset (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U W : Y.Opens) (hUW : U ≤ W) (hP : P (f ∣_ U)) :
    P ((f ∣_ W) ∣_ (W.ι ⁻¹ᵁ U)) := by
  let fW := f ∣_ W
  let V : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  have hSource : (f ⁻¹ᵁ W).ι ''ᵁ (fW ⁻¹ᵁ V) = f ⁻¹ᵁ U := by
    rw [image_morphismRestrict_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    simp [inf_eq_right.mpr hUW]
  let eX : ((fW ⁻¹ᵁ V).toScheme) ≅ (f ⁻¹ᵁ U).toScheme :=
    (f ⁻¹ᵁ W).ι.isoImage (fW ⁻¹ᵁ V) ≪≫ X.isoOfEq hSource
  let eY : V.toScheme ≅ U.toScheme := Scheme.Opens.isoOfLE hUW
  have hXfac : eX.hom ≫ (f ⁻¹ᵁ U).ι = (fW ⁻¹ᵁ V).ι ≫ (f ⁻¹ᵁ W).ι := by
    dsimp [eX]
    rw [Category.assoc, Scheme.isoOfEq_hom_ι]
    exact Scheme.Hom.isoImage_hom_ι _ _
  have hArr : eX.hom ≫ (f ∣_ U) = (fW ∣_ V) ≫ eY.hom := by
    apply (cancel_mono U.ι).1
    calc
      eX.hom ≫ (f ∣_ U) ≫ U.ι = eX.hom ≫ ((f ⁻¹ᵁ U).ι ≫ f) := by rw [morphismRestrict_ι]
      _ = (fW ⁻¹ᵁ V).ι ≫ ((f ⁻¹ᵁ W).ι ≫ f) := by
        rw [← Category.assoc, hXfac, Category.assoc]
      _ = (fW ⁻¹ᵁ V).ι ≫ (fW ≫ W.ι) := by rw [morphismRestrict_ι f W]
      _ = (fW ∣_ V) ≫ (V.ι ≫ W.ι) := by rw [morphismRestrict_ι_assoc fW V W.ι]
      _ = (fW ∣_ V) ≫ (eY.hom ≫ U.ι) := by rw [Scheme.Opens.isoOfLE_hom_ι hUW]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk eX eY hArr)).mpr hP

/-- Base change of `f ∣_ V` along `g : Z ⟶ V` has the property iff the base change of `f` along
the composite `g ≫ V.ι` does. -/
private theorem pullback_snd_restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (g : Z ⟶ V) (h : Z ⟶ Y)
    (hgh : g ≫ V.ι = h) : P (pullback.snd (f ∣_ V) g) ↔ P (pullback.snd f h) := by
  subst hgh
  have hcomp : IsPullback (pullback.fst (f ∣_ V) g ≫ (f ⁻¹ᵁ V).ι) (pullback.snd (f ∣_ V) g) f
      (g ≫ V.ι) :=
    ((IsPullback.of_hasPullback (f ∣_ V) g).flip.paste_vert
      (isPullback_morphismRestrict f V)).flip
  let hcan := IsPullback.of_hasPullback f (g ≫ V.ι)
  exact P.arrow_mk_iso_iff (Arrow.isoMk (hcomp.isoIsPullback X Z hcan) (Iso.refl _)
    (IsPullback.isoIsPullback_hom_snd X Z hcomp hcan))

/-- A property local on the target holds over an open as soon as it holds after base change
along a surjective morphism of the chosen class onto that open. -/
private theorem property_of_open_factor_cover (P Q : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget (Scheme.precoverage Q)] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (g : Z ⟶ V) (hg : Q g) (hgsurj : Function.Surjective g.base)
    (hP : P (pullback.snd f (g ≫ V.ι))) : P (f ∣_ V) := by
  have hcover : Presieve.singleton g ∈ Scheme.precoverage Q V.toScheme := by
    rw [Scheme.singleton_mem_precoverage_iff]
    exact ⟨hgsurj, hg⟩
  have hPb : P (pullback.snd (f ∣_ V) g) := (pullback_snd_restrict_iff P f V g _ rfl).mpr hP
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hcover ?_
  rintro T k - ⟨⟩
  exact hPb

/-- Each of the four classes is stable under composition. -/
private theorem descentClass_comp (Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Q f) (hg : Q g) : Q (f ≫ g) := by
  rcases hQ with hQ | hQ | hQ | hQ <;> subst Q
  · have : Flat f := hf.1
    have : Flat g := hg.1
    have : LocallyOfFinitePresentation f := hf.2
    have : LocallyOfFinitePresentation g := hg.2
    exact ⟨inferInstance, locallyOfFinitePresentation_comp f g⟩
  · exact MorphismProperty.comp_mem _ f g hf hg
  · have : Smooth f := hf
    have : Smooth g := hg
    exact inferInstance
  · have : Etale f := hf
    have : Etale g := hg
    exact inferInstance

/-- Each of the four classes is stable under base change. -/
private theorem descentClass_baseChange (Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (hpb : IsPullback f' g' g f) (hg : Q g) : Q g' := by
  rcases hQ with hQ | hQ | hQ | hQ <;> subst Q
  · exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hg.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hg.2⟩
  · exact (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@Syntomic : MorphismProperty Scheme.{u})).of_isPullback hpb hg
  · exact (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@Smooth : MorphismProperty Scheme.{u})).of_isPullback hpb hg
  · exact (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u})).of_isPullback hpb hg

/-- Base change along the inclusion of an open of the source of `g`, read as a restriction of
the base change along `g`. -/
private theorem pullback_comp_restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (U : Y'.Opens) :
    P (pullback.snd f (U.ι ≫ g)) ↔ P ((pullback.snd f g) ∣_ U) := by
  let e₁ : Arrow.mk (pullback.snd (pullback.snd f g) U.ι) ≅
      Arrow.mk (pullback.snd f g ∣_ U) :=
    Arrow.isoMk (pullbackRestrictIsoRestrict (pullback.snd f g) U) (Iso.refl _) (by simp)
  let e₂ := pullbackLeftPullbackSndIso f g U.ι
  have he₂ : e₂.hom ≫ pullback.snd f (U.ι ≫ g) = pullback.snd (pullback.snd f g) U.ι := by
    simp [e₂]
  exact (P.arrow_mk_iso_iff (Arrow.isoMk e₂ (Iso.refl _) he₂)).symm.trans
    (P.arrow_mk_iso_iff e₁)

/-- The restriction over the preimage of an open on which the property holds. -/
private theorem pullback_of_restriction (P Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) [P.IsLocalAtTarget (Scheme.precoverage Q)]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : Q g) (W : Y.Opens)
    (hP : P (f ∣_ W)) : P ((pullback.snd f g) ∣_ (g ⁻¹ᵁ W)) := by
  let gW : (g ⁻¹ᵁ W).toScheme ⟶ W := g ∣_ W
  have hgW : Q gW := descentClass_baseChange Q hQ (isPullback_morphismRestrict g W).flip hg
  have hPpb : P (pullback.snd (f ∣_ W) gW) := pullback_property P Q hQ (f ∣_ W) gW hgW hP
  exact (pullback_comp_restrict_iff P f g (g ⁻¹ᵁ W)).mp
    ((pullback_snd_restrict_iff P f W gW _ (morphismRestrict_ι g W)).mp hPpb)

/-- The supremum of the opens of the target over which `f` has the property `P`. -/
@[stacks 06QP "largest open"]
noncomputable def largestTargetOpen (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : Y.Opens :=
  sSup {U : Y.Opens | P (f ∣_ U)}

/-- **Stacks Project, Tag 06QP.** A target-local property holds over the largest open. -/
@[stacks 06QP "existence", sga "3 VIB 2.1" "partial"]
lemma property_largestTargetOpen (P Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) [P.IsLocalAtTarget (Scheme.precoverage Q)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : P (f ∣_ largestTargetOpen P f) := by
  have : IsZariskiLocalAtTarget P :=
    MorphismProperty.IsLocalAtTarget.of_le (P := P) (K := Scheme.zariskiPrecoverage)
      (L := Scheme.precoverage Q)
      (Scheme.precoverage_mono (by
        intro X Y f hf
        have := hf
        exact openImmersion_mem Q hQ f))
  let ι : Type u := {U : Y.Opens | P (f ∣_ U)}
  let V : ι → (largestTargetOpen P f).toScheme.Opens := fun i =>
    (largestTargetOpen P f).ι ⁻¹ᵁ i.1
  have htop : ⨆ i, V i = ⊤ := by
    ext y
    change y ∈ (⨆ i, V i) ↔ True
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨W, hW, hyW⟩ := TopologicalSpace.Opens.mem_sSup.mp y.2
    exact ⟨⟨W, hW⟩, hyW⟩
  exact IsZariskiLocalAtTarget.of_iSup_eq_top V htop fun i =>
    restrict_of_subset P f i.1 (largestTargetOpen P f) (le_sSup i.2) i.2

/-- **Stacks Project, Tag 06QP.** Every open over which the property holds lies in the
largest open. -/
@[stacks 06QP "maximality"]
lemma le_largestTargetOpen (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : P (f ∣_ U)) : U ≤ largestTargetOpen P f := le_sSup hU

/-- **Stacks Project, Tag 06QP.** The image of a morphism of the chosen class whose base
change has the property lies in the largest open. -/
@[stacks 06QP "part (1)"]
lemma range_le_largestTargetOpen (P Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) [P.IsLocalAtTarget (Scheme.precoverage Q)]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : Q g)
    (hfg : P (pullback.snd f g)) : Set.range g ⊆ (largestTargetOpen P f).1 := by
  have hopen : IsOpenMap g := by
    rcases hQ with hQ | hQ | hQ | hQ <;> subst Q
    · have : Flat g := hg.1
      have : LocallyOfFinitePresentation g := hg.2
      exact g.isOpenMap
    · have : Flat g := flat hg
      have : LocallyOfFinitePresentation g := locallyOfFinitePresentation hg
      exact g.isOpenMap
    all_goals exact g.isOpenMap
  let V : Y.Opens := ⟨Set.range g.base, hopen.isOpen_range⟩
  have hrange : Set.range g.base ⊆ Set.range V.ι := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨g.base x, ⟨x, rfl⟩⟩, rfl⟩
  let gV : Y' ⟶ V := IsOpenImmersion.lift V.ι g hrange
  have hfac : gV ≫ V.ι = g := IsOpenImmersion.lift_fac V.ι g hrange
  have hgV : Q gV :=
    descentClass_baseChange Q hQ (IsOpenImmersion.isPullback_lift_id g V.ι hrange).flip hg
  have hgVsurj : Function.Surjective gV.base := by
    rintro ⟨y, ⟨x, rfl⟩⟩
    exact ⟨x, Subtype.ext (congrArg (fun k : Y' ⟶ Y => k.base x) hfac)⟩
  exact le_largestTargetOpen P f V
    (property_of_open_factor_cover P Q f V gV hgV hgVsurj (by rwa [hfac]))

/-- **Stacks Project, Tag 06QP.** The largest open commutes with base change along a
morphism of the chosen class. -/
@[stacks 06QP "part (2)"]
lemma largestTargetOpen_baseChange (P Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) [P.IsLocalAtTarget (Scheme.precoverage Q)]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : Q g) :
    largestTargetOpen P (pullback.snd f g) = g ⁻¹ᵁ largestTargetOpen P f := by
  refine le_antisymm (sSup_le fun U hU => ?_) ?_
  · have hgU : Q (U.ι ≫ g) :=
      descentClass_comp Q hQ U.ι g (openImmersion_mem Q hQ U.ι) hg
    have hrange := range_le_largestTargetOpen P Q hQ f (U.ι ≫ g) hgU
      ((pullback_comp_restrict_iff P f g U).mpr hU)
    intro y hy
    exact hrange (Set.mem_range_self (f := (U.ι ≫ g).base) ⟨y, hy⟩)
  · exact le_largestTargetOpen P (pullback.snd f g) (g ⁻¹ᵁ largestTargetOpen P f)
      (pullback_of_restriction P Q hQ f g hg (largestTargetOpen P f)
        (property_largestTargetOpen P Q hQ f))

/-- **Stacks Project, Tag 06QP.** The largest opens of the members of a covering family are
the inverse images of the largest open downstairs. -/
@[stacks 06QP "part (3)"]
lemma largestTargetOpen_covering (P Q : MorphismProperty Scheme.{u})
    (hQ : IsDescentMorphismClass Q) [P.IsLocalAtTarget (Scheme.precoverage Q)]
    {X Y : Scheme.{u}} {I : Type v} (f : X ⟶ Y) (Y' : I → Scheme.{u})
    (g : ∀ i, Y' i ⟶ Y) (hg : Presieve.ofArrows Y' g ∈ Scheme.precoverage Q Y) (i : I) :
    largestTargetOpen P (pullback.snd f (g i)) = (g i) ⁻¹ᵁ largestTargetOpen P f := by
  rw [Scheme.ofArrows_mem_precoverage_iff] at hg
  exact largestTargetOpen_baseChange P Q hQ f (g i) (hg.2 i)

end AlgebraicGeometry
