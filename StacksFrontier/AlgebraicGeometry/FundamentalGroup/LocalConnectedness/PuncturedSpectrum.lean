module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianSplitting
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Flatness
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite étale covers of a punctured local spectrum

Let `A` be a local ring and let `U = Spec A ∖ {𝔪}` be its punctured spectrum. If some strict
henselization of `A` has connected punctured spectrum, then restricting finite étale covers
from `Spec A` to `U` loses no information: the base-change functor
`FÉt_{Spec A} ⥤ FÉt_U` is fully faithful.

## Main results

* `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_to_puncturedSpectrum`: restriction of
  finite étale covers from `Spec A` to its punctured spectrum is fully faithful.

## Implementation notes

The punctured spectrum is `Stacks.Divisors.puncturedSpectrum`, the open complement of the
closed point. The connectedness hypothesis is stated for the subset `{closedPoint Aˢʰ}ᶜ` of
`PrimeSpectrum Aˢʰ` rather than for the open subscheme. A strict henselization is any `Aˢʰ` with
`Stacks.StrictHenselization.IsStrictHenselization A κ Aˢʰ` for a chosen separable closure `κ` of
the residue field, taken as data.

## References

* [Stacks Project, Tag 0BLQ](https://stacks.math.columbia.edu/tag/0BLQ)
* [Stacks Project, Tag 0BQE](https://stacks.math.columbia.edu/tag/0BQE)
* [Stacks Project, Tag 0BL7](https://stacks.math.columbia.edu/tag/0BL7)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing
open Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- A section descends across an effective epimorphism once its pullbacks agree. -/
private theorem descend_section_of_effectiveEpi
    {X Y Z : Scheme.{u}} (π : X ⟶ Y) [EffectiveEpi π]
    (p : Z ⟶ Y) (s : X ⟶ Z) (hs : s ≫ p = π)
    (hcompat : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ X),
      g₁ ≫ π = g₂ ≫ π → g₁ ≫ s = g₂ ≫ s) :
    ∃ t : Y ⟶ Z, t ≫ p = 𝟙 Y ∧ π ≫ t = s := by
  let t := EffectiveEpi.desc π s hcompat
  refine ⟨t, ?_, EffectiveEpi.fac π s hcompat⟩
  apply (cancel_epi π).mp
  rw [← Category.assoc, EffectiveEpi.fac, hs, Category.comp_id]

/-- A nonempty punctured spectrum of a local ring is dense. -/
private theorem dense_compl_closedPoint (R : Type u) [CommRing R] [IsLocalRing R]
    (hne : Set.Nonempty ({closedPoint R}ᶜ : Set (PrimeSpectrum R))) :
    Dense ({closedPoint R}ᶜ : Set (PrimeSpectrum R)) := by
  obtain ⟨y, hy⟩ := hne
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun x ↦ ?_
  by_cases hx : x = closedPoint R
  · subst x
    exact (closure_mono (Set.singleton_subset_iff.mpr hy))
      ((specializes_closedPoint y).mem_closure)
  · exact subset_closure (by simpa using hx)

/-- The preimage of a nonempty punctured local spectrum under a flat morphism is dense. -/
private theorem isDominant_preimage_puncturedSpectrum_of_flat
    (R : Type u) [CommRing R] [IsLocalRing R]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) [Flat f]
    (hne : Set.Nonempty ({closedPoint R}ᶜ : Set (PrimeSpectrum R))) :
    IsDominant ((f ⁻¹ᵁ puncturedSpectrum R).ι) := by
  apply Opens.isDominant_ι
  obtain ⟨p, hp⟩ := hne
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun q ↦ ?_
  by_cases hq : f q = closedPoint R
  · obtain ⟨q', hspec, hmap⟩ := Flat.generalizingMap f (hq ▸ specializes_closedPoint p)
    have hmem : q' ∈ (f ⁻¹ᵁ puncturedSpectrum R : Set T) := by
      change f q' ≠ closedPoint R
      rw [hmap]
      exact hp
    exact (closure_mono (Set.singleton_subset_iff.mpr hmem)) hspec.mem_closure
  · exact subset_closure hq

/-- The image of a nonclosed point under a ring map that generates the target's maximal ideal
from the source's is nonclosed. -/
private theorem comap_ne_closedPoint
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hmax : Ideal.map f (maximalIdeal A) = maximalIdeal B)
    (p : PrimeSpectrum B) (hp : p ≠ closedPoint B) :
    PrimeSpectrum.comap f p ≠ closedPoint A := by
  refine fun h ↦ hp (PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal p.2.1) ?_))
  change maximalIdeal B ≤ p.asIdeal
  rw [← hmax, Ideal.map_le_iff_le_comap]
  exact le_of_eq (congrArg PrimeSpectrum.asIdeal h).symm

/-- For a local ring map generating the target's maximal ideal, a point of the target is the
closed point exactly when its image is. -/
private theorem comap_ne_closedPoint_iff
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hmax : Ideal.map f (maximalIdeal A) = maximalIdeal B)
    (p : PrimeSpectrum B) :
    PrimeSpectrum.comap f p ≠ closedPoint A ↔ p ≠ closedPoint B := by
  refine ⟨fun hp h ↦ hp ?_, comap_ne_closedPoint f hmax p⟩
  subst h
  exact PrimeSpectrum.ext (maximalIdeal_comap f)

/-- If a local ring map generating the target's maximal ideal has a target with connected
punctured spectrum, then the source has a nonempty punctured spectrum. -/
private theorem nonempty_compl_closedPoint_of_isConnected
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hconnected : _root_.IsConnected ({closedPoint B}ᶜ : Set (PrimeSpectrum B))) :
    Set.Nonempty ({closedPoint A}ᶜ : Set (PrimeSpectrum A)) := by
  obtain ⟨z, hz⟩ := hconnected.nonempty
  exact ⟨PrimeSpectrum.comap (algebraMap A B) z,
    comap_ne_closedPoint (algebraMap A B) hmax z (by simpa using hz)⟩

/-- A local ring map generating the target's maximal ideal pulls the punctured spectrum back to
the punctured spectrum. -/
private theorem preimage_puncturedSpectrum
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hmax : Ideal.map f (maximalIdeal A) = maximalIdeal B) :
    (Spec.map (CommRingCat.ofHom f)) ⁻¹ᵁ (puncturedSpectrum A) = puncturedSpectrum B := by
  ext p
  change PrimeSpectrum.comap f p ≠ closedPoint A ↔ p ≠ closedPoint B
  exact comap_ne_closedPoint_iff f hmax p

/-- Let `R` be a henselian local ring with separably closed residue field and let
`p : Y ⟶ Spec R` be finite étale. A section of `p` over a morphism `j : U ⟶ Spec R` from a
connected scheme is the restriction of a section of `p`. -/
@[sga "3 VIB 5.6.1" "special case"]
private theorem exists_section_of_henselian_hom
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [IsFinite p] [Etale p]
    (U : Scheme.{u}) [ConnectedSpace U] (j : U ⟶ Spec (.of R)) (s : U ⟶ Y)
    (hs : s ≫ p = j) :
    ∃ t : Spec (.of R) ⟶ Y, t ≫ p = 𝟙 _ ∧ j ≫ t = s :=
  exists_section_of_henselian_of_isSepClosed R
    (MorphismProperty.Over.mk ⊤ p ⟨inferInstance, inferInstance⟩) U j s hs

/-- A section of a finite étale cover of `Spec A` over the punctured spectrum extends over the
spectrum of a strict henselization of `A`, compatibly with the original section. -/
private theorem extend_section_after_strictHenselization
    (A : Type u) [CommRing A] [IsLocalRing A]
    (κsep : Type u) [Field κsep]
    [Algebra (maximalIdeal A).ResidueField κsep]
    [IsSepClosure (maximalIdeal A).ResidueField κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    (Y : FiniteEtaleOver (Spec (.of A)))
    (s : (puncturedSpectrum A).toScheme ⟶ Y.left)
    (hs : s ≫ Y.hom = (puncturedSpectrum A).ι) :
    ∃ t : Spec (.of Ash) ⟶ Y.left,
      t ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∧
      ((Spec.map (CommRingCat.ofHom (algebraMap A Ash))) ⁻¹ᵁ (puncturedSpectrum A)).ι ≫ t =
        (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ (puncturedSpectrum A)) ≫ s := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A Ash))
  let U := puncturedSpectrum A
  let V := f ⁻¹ᵁ U
  have : IsLocalHom (algebraMap A Ash) := hAsh.isLocalHom
  have hV : V = puncturedSpectrum Ash :=
    preimage_puncturedSpectrum (algebraMap A Ash) hAsh.maximalIdeal_map
  have : ConnectedSpace V := by
    rw [show V = puncturedSpectrum Ash from hV]
    exact isConnected_iff_connectedSpace.mp hconnected
  have : HenselianLocalRing Ash := hAsh.henselian
  have : IsSepClosed (maximalIdeal Ash).ResidueField := hAsh.sepClosed
  have : IsSepClosed (ResidueField Ash) := isSepClosed_residueField_of_maximalIdeal Ash
  have hpb : finiteEtale (pullback.snd Y.hom f) := MorphismProperty.pullback_snd Y.hom f Y.prop
  have : IsFinite (pullback.snd Y.hom f) := hpb.1
  have : Etale (pullback.snd Y.hom f) := hpb.2
  let ss : V.toScheme ⟶ pullback Y.hom f := pullback.lift ((f ∣_ U) ≫ s) V.ι (by
    rw [Category.assoc, hs]
    exact morphismRestrict_ι f U)
  have hss : ss ≫ pullback.snd Y.hom f = V.ι := pullback.lift_snd _ _ _
  obtain ⟨tz, htz, hvz⟩ :=
    exists_section_of_henselian_hom Ash (pullback.snd Y.hom f) V.toScheme V.ι ss hss
  refine ⟨tz ≫ pullback.fst Y.hom f, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, htz, Category.id_comp]
  · rw [← Category.assoc, hvz]
    exact pullback.lift_fst _ _ _

/-- Two extensions of one section agree on the kernel pair of a morphism when the open they
extend across pulls back to something dominant there. -/
private theorem compatible_extension_on_kernelPair
    {S T Y : Scheme.{u}} (f : T ⟶ S) (p : Y ⟶ S)
    [IsFinite p] [Etale p] (U : S.Opens)
    (s : U.toScheme ⟶ Y) (t : T ⟶ Y)
    (ht : t ≫ p = f)
    (hext : (f ⁻¹ᵁ U).ι ≫ t = (f ∣_ U) ≫ s)
    [IsDominant (((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι)] :
    pullback.fst f f ≫ t = pullback.snd f f ≫ t := by
  let q₁ := pullback.fst f f
  let q₂ := pullback.snd f f
  let r := q₁ ≫ f
  let V := r ⁻¹ᵁ U
  let V₀ := f ⁻¹ᵁ U
  let H := isPullback_morphismRestrict f U
  have key : ∀ q : pullback f f ⟶ T, q ≫ f = r → V.ι ≫ q ≫ t = (r ∣_ U) ≫ s := by
    intro q hq
    let a : V.toScheme ⟶ V₀.toScheme :=
      H.lift (r ∣_ U) (V.ι ≫ q) (by rw [morphismRestrict_ι, Category.assoc, hq])
    calc
      V.ι ≫ q ≫ t = (a ≫ V₀.ι) ≫ t := by rw [H.lift_snd, Category.assoc]
      _ = (r ∣_ U) ≫ s := by rw [Category.assoc, hext, ← Category.assoc, H.lift_fst]
  have hV : V.ι ≫ (q₁ ≫ t) = V.ι ≫ (q₂ ≫ t) :=
    (key q₁ rfl).trans (key q₂ pullback.condition.symm).symm
  have hp : (q₁ ≫ t) ≫ p = (q₂ ≫ t) ≫ p := by
    simpa [q₁, q₂, Category.assoc, ht] using
      (pullback.condition : pullback.fst f f ≫ f = pullback.snd f f ≫ f)
  exact eq_of_isDominant_of_finiteEtale p hp V.ι hV

/-- **Sections of a finite étale cover extend across the puncture.** A section of a finite étale
cover of `Spec A` over the punctured spectrum extends to a section over `Spec A`, provided the
punctured spectrum of a strict henselization of `A` is connected. -/
private theorem extend_section_from_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A]
    (κsep : Type u) [Field κsep]
    [Algebra (maximalIdeal A).ResidueField κsep]
    [IsSepClosure (maximalIdeal A).ResidueField κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    (Y : FiniteEtaleOver (Spec (.of A)))
    (s : (puncturedSpectrum A).toScheme ⟶ Y.left)
    (hs : s ≫ Y.hom = (puncturedSpectrum A).ι) :
    ∃ t : Spec (.of A) ⟶ Y.left,
      t ≫ Y.hom = 𝟙 _ ∧ (puncturedSpectrum A).ι ≫ t = s := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A Ash))
  let U := puncturedSpectrum A
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  obtain ⟨tsh, htsh, hUsh⟩ :=
    extend_section_after_strictHenselization A κsep Ash hAsh hconnected Y s hs
  have : Module.Flat A Ash := hAsh.flat
  have : IsLocalHom (algebraMap A Ash) := hAsh.isLocalHom
  have : Module.FaithfullyFlat A Ash := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hff : (algebraMap A Ash).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hcover : Flat f ∧ Surjective f := (flat_and_surjective_SpecMap_iff _).mpr hff
  have : Flat f := hcover.1
  have : Surjective f := hcover.2
  have : IsRegularEpi f := isRegularEpi_of_flat_of_surjective_of_isAffine f
  have : EffectiveEpi f := inferInstance
  have hne := nonempty_compl_closedPoint_of_isConnected hAsh.maximalIdeal_map hconnected
  let q₁ := pullback.fst f f
  have : Flat q₁ :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f f).flip inferInstance
  have : Flat (q₁ ≫ f) := inferInstance
  have : IsDominant (((q₁ ≫ f) ⁻¹ᵁ U).ι) :=
    isDominant_preimage_puncturedSpectrum_of_flat A (q₁ ≫ f) hne
  have hpair : q₁ ≫ tsh = pullback.snd f f ≫ tsh :=
    compatible_extension_on_kernelPair f Y.hom U s tsh htsh hUsh
  obtain ⟨t, ht, hft⟩ := descend_section_of_effectiveEpi f Y.hom tsh htsh (by
    intro W g₁ g₂ hg
    let w : W ⟶ pullback f f := pullback.lift g₁ g₂ hg
    calc
      g₁ ≫ tsh = (w ≫ q₁) ≫ tsh := by rw [pullback.lift_fst]
      _ = w ≫ (pullback.snd f f ≫ tsh) := by rw [Category.assoc, hpair]
      _ = g₂ ≫ tsh := by rw [← Category.assoc, pullback.lift_snd])
  have : Flat (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip inferInstance
  have : Surjective (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip inferInstance
  have : Epi (f ∣_ U) := Flat.epi_of_flat_of_surjective _
  refine ⟨t, ht, ?_⟩
  apply (cancel_epi (f ∣_ U)).mp
  calc
    (f ∣_ U) ≫ (U.ι ≫ t) = ((f ∣_ U) ≫ U.ι) ≫ t := (Category.assoc ..).symm
    _ = ((f ⁻¹ᵁ U).ι ≫ f) ≫ t := by rw [morphismRestrict_ι]
    _ = (f ⁻¹ᵁ U).ι ≫ tsh := by rw [Category.assoc, hft]
    _ = (f ∣_ U) ≫ s := hUsh

/-- Restriction from the spectrum of a local ring `A` to its punctured spectrum is fully faithful
on finite étale covers, provided the punctured spectrum of a strict henselization of `A` is
connected. -/
@[stacks 0BLQ]
theorem fullyFaithful_finiteEtaleBaseChange_to_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A]
    (κsep : Type u) [Field κsep]
    [Algebra (maximalIdeal A).ResidueField κsep]
    [IsSepClosure (maximalIdeal A).ResidueField κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash))) :
    Nonempty (finiteEtaleBaseChange (puncturedSpectrum A).ι).FullyFaithful := by
  let F := finiteEtaleBaseChange (puncturedSpectrum A).ι
  have : IsDominant (puncturedSpectrum A).ι := by
    apply Opens.isDominant_ι
    exact dense_compl_closedPoint A
      (nonempty_compl_closedPoint_of_isConnected hAsh.maximalIdeal_map hconnected)
  have : F.Faithful := faithful_finiteEtaleBaseChange_of_isDominant _
  have hfull : F.Full := by
    refine ⟨?_⟩
    intro Y Z h
    let X := Spec (.of A)
    let U := puncturedSpectrum A
    let Yo : Over X := Over.mk Y.hom
    let Zo : Over X := Over.mk Z.hom
    have : IsFinite Yo.hom := Y.prop.1
    have : Etale Yo.hom := Y.prop.2
    have : IsFinite Zo.hom := Z.prop.1
    have : Etale Zo.hom := Z.prop.2
    obtain ⟨W, hWfin, hWet, ⟨e⟩⟩ := Stacks.FundamentalGroup.exists_finiteEtale_internalHom X Yo Zo
    let Wfe : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ W.hom ⟨hWfin, hWet⟩
    let B : Over X := Over.mk U.ι
    let T : Over X := Over.mk (𝟙 X)
    let i : B ⟶ T := Over.homMk U.ι
    let P := Yo ⨯ B
    let θ : P.left ⟶ pullback Y.hom U.ι := (Over.prodLeftIsoPullback Yo B).hom
    have hθiso : IsIso θ := by
      change IsIso (Over.prodLeftIsoPullback Yo B).hom
      infer_instance
    have hθfst : θ ≫ pullback.fst Y.hom U.ι = (prod.fst (Y := B)).left :=
      Over.prodLeftIsoPullback_hom_fst Yo B
    have hθsnd : θ ≫ pullback.snd Y.hom U.ι = (prod.snd (X := Yo)).left :=
      Over.prodLeftIsoPullback_hom_snd Yo B
    let hl : pullback Y.hom U.ι ⟶ pullback Z.hom U.ι := h.left
    have hh : hl ≫ pullback.snd Z.hom U.ι = pullback.snd Y.hom U.ι :=
      MorphismProperty.Over.w h
    have hcondZ : pullback.fst Z.hom U.ι ≫ Zo.hom = pullback.snd Z.hom U.ι ≫ U.ι :=
      pullback.condition
    have hsndw : (prod.snd (X := Yo) : P ⟶ B).left ≫ U.ι = P.hom := (prod.snd (X := Yo)).w
    have hmUw : (θ ≫ hl ≫ pullback.fst Z.hom U.ι) ≫ Zo.hom = P.hom := by
      rw [Category.assoc, Category.assoc, hcondZ, ← Category.assoc hl, hh,
        ← Category.assoc, hθsnd]
      exact hsndw
    let mU : P ⟶ Zo := Over.homMk (θ ≫ hl ≫ pullback.fst Z.hom U.ι) hmUw
    let sB : B ⟶ W := (e.app (Opposite.op B)).inv mU
    have hsB : sB.left ≫ W.hom = U.ι := sB.w
    obtain ⟨tW, htW, hUtW⟩ :=
      extend_section_from_puncturedSpectrum A κsep Ash hAsh hconnected Wfe sB.left hsB
    let tB : T ⟶ W := Over.homMk tW htW
    let mT : Yo ⨯ T ⟶ Zo := (e.app (Opposite.op T)).hom tB
    let c : Yo ⟶ T := Over.homMk Y.hom
    let η : Yo ⟶ Yo ⨯ T := prod.lift (𝟙 Yo) c
    let g : Yo ⟶ Zo := η ≫ mT
    let k : Y ⟶ Z := MorphismProperty.Over.homMk g.left g.w
    have hi : i ≫ tB = sB := by
      ext1; exact hUtW
    let mapi : P ⟶ Yo ⨯ T := (prod.functor.obj Yo).map i
    have hm : mapi ≫ mT = mU := by
      have hn := congrArg (fun q => q tB) (e.hom.naturality i.op)
      change (e.app (Opposite.op B)).hom (i ≫ tB) = mapi ≫ mT at hn
      rw [hi] at hn
      have hmU : (e.app (Opposite.op B)).hom sB = mU := by
        simpa only [sB] using (e.app (Opposite.op B)).inv_hom_id_apply mU
      exact hn.symm.trans hmU
    have hci : (prod.fst (Y := B) : P ⟶ Yo) ≫ c = (prod.snd (X := Yo) : P ⟶ B) ≫ i := by
      ext1
      calc
        (prod.fst (Y := B)).left ≫ c.left = P.hom := (prod.fst (Y := B)).w
        _ = (prod.snd (X := Yo)).left ≫ i.left := (prod.snd (X := Yo)).w.symm
    have hmapη : mapi = (prod.fst (Y := B) : P ⟶ Yo) ≫ η := by
      change prod.map (𝟙 Yo) i = (prod.fst (Y := B) : P ⟶ Yo) ≫ η
      apply prod.hom_ext
      · simp only [prod.map_fst, Category.comp_id, η, prod.comp_lift, prod.lift_fst]
      · simp only [prod.map_snd, η, prod.comp_lift, prod.lift_snd]
        exact hci.symm
    have hmg : (prod.fst (Y := B) : P ⟶ Yo) ≫ g = mU := by
      change (prod.fst (Y := B) : P ⟶ Yo) ≫ η ≫ mT = mU
      rw [← Category.assoc, ← hmapη, hm]
    have hmgLeft : (prod.fst (Y := B)).left ≫ k.left = mU.left :=
      congrArg (fun q : P ⟶ Zo => q.left) hmg
    have hπ : pullback.fst Y.hom U.ι ≫ k.left = hl ≫ pullback.fst Z.hom U.ι := by
      rw [← cancel_epi θ, ← Category.assoc, hθfst]
      exact hmgLeft
    refine ⟨k, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change ((finiteEtaleBaseChange (puncturedSpectrum A).ι).map k).left
          ≫ pullback.fst Z.hom U.ι = hl ≫ pullback.fst Z.hom U.ι
      rw [finiteEtaleBaseChange_map_left_fst]
      exact hπ
    · have hwk : ((finiteEtaleBaseChange (puncturedSpectrum A).ι).map k).left
          ≫ pullback.snd Z.hom U.ι = pullback.snd Y.hom U.ι :=
        MorphismProperty.Over.w ((finiteEtaleBaseChange (puncturedSpectrum A).ι).map k)
      change ((finiteEtaleBaseChange (puncturedSpectrum A).ι).map k).left
          ≫ pullback.snd Z.hom U.ι = hl ≫ pullback.snd Z.hom U.ι
      rw [hwk, hh]
  have : F.Full := hfull
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

end AlgebraicGeometry

end
