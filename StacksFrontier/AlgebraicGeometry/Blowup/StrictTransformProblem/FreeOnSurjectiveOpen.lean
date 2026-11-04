module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformProblem.Successive
public import StacksFrontier.AlgebraicGeometry.StrictTransform.OpenSourceFlat

/-!
# Finite local freeness on an open surjecting onto the base

This file studies the property
`AlgebraicGeometry.FreeOnSurjectiveOpen g G`: the morphism `g : Y ⟶ T` is flat and there is an
open `V ⊆ Y` surjecting onto `T` on which the module `G` is finite locally free of some finite
rank near every point. This is the conclusion of [Stacks, Tag 0811] read for a single pair
(morphism, module), and it is the property `P` to which the three reductions of Remark 38.30.1
([Stacks, Tag 080Y]) are applied in the proof of that tag.

Three facts are needed to feed it to `AlgebraicGeometry.StrictTransformProblem`: it is invariant
under isomorphism of pairs, it is local on the base, and it survives the strict transform along
any blowup.

## Main definitions

* `AlgebraicGeometry.FreeOnSurjectiveOpen`: the property above.

## Main results

* `AlgebraicGeometry.FreeOnSurjectiveOpen.map` and
  `AlgebraicGeometry.freeOnSurjectiveOpen_iff_of_iso`: invariance under isomorphism.
* `AlgebraicGeometry.freeOnSurjectiveOpen_of_cover`: locality on the base.
* `AlgebraicGeometry.freeOnSurjectiveOpen_sheaf`: stability under the strict transform, on the
  ambient base change.
* `AlgebraicGeometry.freeOnSurjectiveOpen_strictTransform_iff_sheaf`: the property on the strict
  transform proper is the property on the ambient base change.
* `AlgebraicGeometry.freeOnSurjectiveOpen_strictTransform`: stability in the shape the stability
  field of `AlgebraicGeometry.StrictTransformProblem` asks for.

## Implementation notes

**Why flatness of the morphism belongs to the property.** Without it the property is *not* stable
under strict transform. Take `T` the affine plane, the centre the origin, and `Y` the union of the
double line `x² = 0` and the complement of the origin: the structure sheaf is free of rank one on
all of `Y`, which surjects onto `T`, but the strict transform of the double line meets the
exceptional curve in a single point, so no open of the strict transform surjects onto the blowup.
Flatness of `g` removes exactly this: the strict transform of `Y` is then the whole base change
([Stacks, Tag 080F] part (1)), and a point of the base change above a prescribed point of the
blowup and a prescribed point of `Y` exists by
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`.

**Where the freeness comes from.** On the open `V` the module is finite locally free, hence flat
over `T` because `g` is flat, so there the quotient map defining the strict transform is
invertible and the strict transform is the pullback. That is
`AlgebraicGeometry.freeAtPointOfRank_strictTransformSheaf`, which is [Stacks, Tag 080F] part (2)
localized on the source.

**The two realizations of the blowup.** The stability field of
`AlgebraicGeometry.StrictTransformProblem` is phrased with `Stacks.Blowup.strictTransformMap` and
`Stacks.Blowup.strictTransformModule`, over `Stacks.Blowup.blowUp`, while [Stacks, Tag 080F] is
available over `AlgebraicGeometry.blowUp`. The passage between them is invariance under
isomorphism applied to `Stacks.Blowup.strictTransformIso`, `AlgebraicGeometry.blowUpIso` and
`Stacks.Blowup.pullbackStrictTransformModuleIso`, exactly as in
`AlgebraicGeometry.StrictTransformProblem.p_strictTransform_iff`.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Finite local freeness on an open surjecting onto the base.** The morphism `g : Y ⟶ T` is
flat, and there is an open `V ⊆ Y` which surjects onto `T` and on which `G` is finite locally free
of some finite rank near every point. This is the conclusion of [Stacks, Tag 0811] read for one
pair (morphism, module). -/
def FreeOnSurjectiveOpen {Y T : Scheme.{u}} (g : Y ⟶ T) (G : Y.Modules) : Prop :=
  Flat g ∧ ∃ V : Y.Opens,
    (∀ y : Y, y ∈ V → ∃ r : ℕ, FreeAtPointOfRank G y r) ∧
      Function.Surjective (V.ι ≫ g).base

/-! ### Invariance under isomorphism -/

/-- **`AlgebraicGeometry.FreeOnSurjectiveOpen` is carried along an isomorphism of pairs.** -/
theorem FreeOnSurjectiveOpen.map {Y T Y₂ T₂ : Scheme.{u}} {g : Y ⟶ T} {g₂ : Y₂ ⟶ T₂}
    {G : Y.Modules} {G₂ : Y₂.Modules} (eY : Y ≅ Y₂) (eT : T ≅ T₂)
    (hw : g ≫ eT.hom = eY.hom ≫ g₂) (e : G ≅ (Scheme.Modules.pullback eY.hom).obj G₂)
    (h : FreeOnSurjectiveOpen g G) : FreeOnSurjectiveOpen g₂ G₂ := by
  obtain ⟨hflat, V, hfree, hsurj⟩ := h
  have hri : MorphismProperty.RespectsIso (@Flat) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hinv : ∀ y : Y, eY.inv.base (eY.hom.base y) = y := fun y ↦ by
    show (eY.hom ≫ eY.inv).base y = y
    rw [eY.hom_inv_id]
    rfl
  have hsq : ∀ y : Y, g₂.base (eY.hom.base y) = eT.hom.base (g.base y) := fun y ↦ by
    show (eY.hom ≫ g₂).base y = (g ≫ eT.hom).base y
    rw [hw]
  refine ⟨?_, eY.inv ⁻¹ᵁ V, ?_, ?_⟩
  · exact (MorphismProperty.arrow_mk_iso_iff (P := @Flat) (Arrow.isoMk eY eT hw.symm)).mp hflat
  · intro y₂ hy₂
    obtain ⟨r, hr⟩ := hfree (eY.inv.base y₂) hy₂
    refine ⟨r, ?_⟩
    have h2 := freeAtPointOfRank_of_pullback_isIso eY.hom G₂ (eY.inv.base y₂) r
      (freeAtPointOfRank_of_moduleIso e hr)
    have h3 : eY.hom.base (eY.inv.base y₂) = y₂ := by
      show (eY.inv ≫ eY.hom).base y₂ = y₂
      rw [eY.inv_hom_id]
      rfl
    rwa [h3] at h2
  · intro t₂
    obtain ⟨v, hv⟩ := hsurj (eT.inv.base t₂)
    have hv' : g.base (V.ι.base v) = eT.inv.base t₂ := hv
    have hmem : eY.hom.base (V.ι.base v) ∈ (eY.inv ⁻¹ᵁ V : Y₂.Opens) := by
      show eY.inv.base (eY.hom.base (V.ι.base v)) ∈ V
      rw [hinv]
      exact v.2
    refine ⟨⟨eY.hom.base (V.ι.base v), hmem⟩, ?_⟩
    show g₂.base (eY.hom.base (V.ι.base v)) = t₂
    rw [hsq, hv']
    show (eT.inv ≫ eT.hom).base t₂ = t₂
    rw [eT.inv_hom_id]
    rfl

/-- **`AlgebraicGeometry.FreeOnSurjectiveOpen` depends only on the isomorphism class of the
pair.** This is the shape of the invariance field of
`AlgebraicGeometry.StrictTransformProblem`. -/
theorem freeOnSurjectiveOpen_iff_of_iso {Y T Y₂ T₂ : Scheme.{u}} (g : Y ⟶ T) (g₂ : Y₂ ⟶ T₂)
    (G : Y.Modules) (G₂ : Y₂.Modules) (eY : Y ≅ Y₂) (eT : T ≅ T₂)
    (hw : g ≫ eT.hom = eY.hom ≫ g₂) (e : G ≅ (Scheme.Modules.pullback eY.hom).obj G₂) :
    FreeOnSurjectiveOpen g G ↔ FreeOnSurjectiveOpen g₂ G₂ := by
  refine ⟨FreeOnSurjectiveOpen.map eY eT hw e, ?_⟩
  refine FreeOnSurjectiveOpen.map eY.symm eT.symm ?_ ?_
  · have hgg : eY.hom ≫ g₂ ≫ eT.inv = g := by
      rw [← Category.assoc, ← hw, Category.assoc, eT.hom_inv_id, Category.comp_id]
    show g₂ ≫ eT.inv = eY.inv ≫ g
    rw [← hgg, ← Category.assoc, eY.inv_hom_id, Category.id_comp]
  · exact ((Scheme.Modules.pullback eY.inv).mapIso e ≪≫
      (Scheme.Modules.pullbackComp eY.inv eY.hom).app G₂ ≪≫
      (Scheme.Modules.pullbackCongr eY.inv_hom_id).app G₂ ≪≫
      (Scheme.Modules.pullbackId Y₂).app G₂).symm

/-! ### Locality on the base -/

/-- **`AlgebraicGeometry.FreeOnSurjectiveOpen` is local on the base.** If the base is covered by
opens over each of which the restricted pair has the property, then so does the pair itself: the
open is the union of the images of the local ones, and flatness is local on the target. -/
theorem freeOnSurjectiveOpen_of_cover {Y T : Scheme.{u}} (g : Y ⟶ T) (G : Y.Modules)
    {ι : Type} (W : ι → T.Opens) (hcover : (⋃ i, (W i : Set T)) = Set.univ)
    (h : ∀ i, FreeOnSurjectiveOpen (pullback.snd g (W i).ι)
      ((Scheme.Modules.pullback (pullback.fst g (W i).ι)).obj G)) :
    FreeOnSurjectiveOpen g G := by
  classical
  have hri : MorphismProperty.RespectsIso (@Flat) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hWtop : iSup W = ⊤ := by
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_iSup, hcover]
    rfl
  -- Flatness is local on the target.
  have hzl : IsZariskiLocalAtTarget (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Flat)
  have hflat : Flat g := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Flat) (f := g) W hWtop fun i ↦ ?_
    have hi := (h i).1
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict g (W i),
      MorphismProperty.cancel_left_of_respectsIso (P := @Flat)] at hi
    exact hi
  -- The open is the union of the images of the local ones.
  choose V hVfree hVsurj using fun i ↦ (h i).2
  refine ⟨hflat, ⨆ i, pullback.fst g (W i).ι ''ᵁ V i, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    obtain ⟨v, hvV, rfl⟩ := hyi
    obtain ⟨r, hr⟩ := hVfree i v hvV
    exact ⟨r, freeAtPointOfRank_of_isOpenImmersion (pullback.fst g (W i).ι) G v r hr⟩
  · intro t
    have ht : t ∈ ⋃ i, (W i : Set T) := by rw [hcover]; exact Set.mem_univ t
    obtain ⟨i, hti⟩ := Set.mem_iUnion.mp ht
    obtain ⟨v, hv⟩ := hVsurj i ⟨t, hti⟩
    have hv' : (pullback.snd g (W i).ι).base ((V i).ι.base v) = ⟨t, hti⟩ := hv
    have hmem : (pullback.fst g (W i).ι).base ((V i).ι.base v) ∈
        (⨆ j, pullback.fst g (W j).ι ''ᵁ V j : Y.Opens) :=
      TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨(V i).ι.base v, v.2, rfl⟩⟩
    refine ⟨⟨(pullback.fst g (W i).ι).base ((V i).ι.base v), hmem⟩, ?_⟩
    show g.base ((pullback.fst g (W i).ι).base ((V i).ι.base v)) = t
    have hcond : ∀ z : ↥(Limits.pullback g (W i).ι),
        g.base ((pullback.fst g (W i).ι).base z) =
          (W i).ι.base ((pullback.snd g (W i).ι).base z) := fun z ↦ by
      show (pullback.fst g (W i).ι ≫ g).base z = (pullback.snd g (W i).ι ≫ (W i).ι).base z
      rw [pullback.condition]
    rw [hcond, hv']
    rfl

/-! ### Stability under the strict transform -/

/-- **`AlgebraicGeometry.FreeOnSurjectiveOpen` survives the strict transform**, on the ambient
base change. The open is the inverse image of the given one; freeness there is
[Stacks, Tag 080F] part (2) localized on the source, and surjectivity holds because a point of
the base change lies above any prescribed compatible pair of points. -/
theorem freeOnSurjectiveOpen_sheaf {Y T : Scheme.{u}} (g : Y ⟶ T) (G : Y.Modules)
    [G.IsQuasicoherent] (I : T.IdealSheafData) (h : FreeOnSurjectiveOpen g G) :
    FreeOnSurjectiveOpen (pullback.snd g (blowUpToBase I))
      (Stacks.StrictTransform.sheaf g (blowUpToBase I) (exceptionalIdeal I) G) := by
  obtain ⟨hflat, V, hfree, hsurj⟩ := h
  have _ : Flat g := hflat
  refine ⟨inferInstance, pullback.fst g (blowUpToBase I) ⁻¹ᵁ V, ?_, ?_⟩
  · intro z hz
    obtain ⟨r, hr⟩ := hfree ((pullback.fst g (blowUpToBase I)).base z) hz
    exact ⟨r, freeAtPointOfRank_strictTransformSheaf g I G z r hr⟩
  · intro t'
    obtain ⟨v, hv⟩ := hsurj ((blowUpToBase I).base t')
    have hv' : g.base (V.ι.base v) = (blowUpToBase I).base t' := hv
    obtain ⟨z, hz₁, hz₂⟩ :=
      Scheme.Pullback.exists_preimage_pullback (V.ι.base v) t' hv'
    have hmem : z ∈ (pullback.fst g (blowUpToBase I) ⁻¹ᵁ V :
        (Limits.pullback g (blowUpToBase I)).Opens) := by
      show (pullback.fst g (blowUpToBase I)).base z ∈ V
      rw [hz₁]
      exact v.2
    refine ⟨⟨z, hmem⟩, ?_⟩
    show (pullback.snd g (blowUpToBase I)).base z = t'
    exact hz₂

/-- **The property on the strict transform proper and on the ambient base change agree.** The
structure morphism being flat, the closed immersion of the strict transform into the base change
is invertible ([Stacks, Tag 080F] part (1)); the passage from `AlgebraicGeometry.blowUp` to
`Stacks.Blowup.blowUp` is `Stacks.Blowup.strictTransformIso` with
`Stacks.Blowup.pullbackStrictTransformModuleIso`. -/
theorem freeOnSurjectiveOpen_strictTransform_iff_sheaf {Y T : Scheme.{u}} (g : Y ⟶ T) [Flat g]
    (G : Y.Modules) (I : T.IdealSheafData) :
    FreeOnSurjectiveOpen (Stacks.Blowup.strictTransformMap g I)
        (Stacks.Blowup.strictTransformModule g I G) ↔
      FreeOnSurjectiveOpen (pullback.snd g (blowUpToBase I))
        (Stacks.StrictTransform.sheaf g (blowUpToBase I) (exceptionalIdeal I) G) := by
  -- The strict transform of a flat `Y` is the whole base change.
  have hbot : Stacks.StrictTransform.ideal g (blowUpToBase I) (exceptionalIdeal I) = ⊥ :=
    strictTransformIdeal_eq_bot_of_flat_at_exceptional g I fun x _ ↦ Flat.stalkMap g x
  have hiso : IsIso (Stacks.StrictTransform.ideal g (blowUpToBase I)
      (exceptionalIdeal I)).subschemeι := by
    rw [hbot]
    infer_instance
  have _ := hiso
  set s := (Stacks.StrictTransform.ideal g (blowUpToBase I) (exceptionalIdeal I)).subschemeι
    with hs
  have hw1 : pullback.snd g (blowUpToBase I) ≫ (Iso.refl (blowUp I)).hom =
      (asIso s).symm.hom ≫ strictTransformToBlowUp g I := by
    show pullback.snd g (blowUpToBase I) ≫ 𝟙 _ = inv s ≫ (s ≫ pullback.snd g (blowUpToBase I))
    rw [Category.comp_id, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have he1 : Stacks.StrictTransform.sheaf g (blowUpToBase I) (exceptionalIdeal I) G ≅
      (Scheme.Modules.pullback (asIso s).symm.hom).obj (strictTransformBlowUpModule g I G) :=
    ((Scheme.Modules.pullback (inv s)).mapIso (Iso.refl _) ≪≫
      (Scheme.Modules.pullbackComp (inv s) s).app
        (Stacks.StrictTransform.sheaf g (blowUpToBase I) (exceptionalIdeal I) G) ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id s)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _).symm
  have hw2 : strictTransformToBlowUp g I ≫ (blowUpIso I).hom =
      (Stacks.Blowup.strictTransformIso g I).hom ≫ Stacks.Blowup.strictTransformMap g I := by
    rw [Stacks.Blowup.strictTransformIso_hom_strictTransformMap]
    simp only [strictTransformToBlowUp, Category.assoc]
  exact ((freeOnSurjectiveOpen_iff_of_iso _ _ _ _ (asIso s).symm (Iso.refl (blowUp I))
      hw1 he1).trans
    (freeOnSurjectiveOpen_iff_of_iso _ _ _ _ (Stacks.Blowup.strictTransformIso g I)
      (blowUpIso I) hw2 (Stacks.Blowup.pullbackStrictTransformModuleIso g I G).symm)).symm

/-- **`AlgebraicGeometry.FreeOnSurjectiveOpen` survives the strict transform**, in the shape the
stability field of `AlgebraicGeometry.StrictTransformProblem` asks for. -/
theorem freeOnSurjectiveOpen_strictTransform {Y T : Scheme.{u}} (g : Y ⟶ T) (G : Y.Modules)
    [G.IsQuasicoherent] (I : T.IdealSheafData) (h : FreeOnSurjectiveOpen g G) :
    FreeOnSurjectiveOpen (Stacks.Blowup.strictTransformMap g I)
      (Stacks.Blowup.strictTransformModule g I G) :=
  have : Flat g := h.1
  (freeOnSurjectiveOpen_strictTransform_iff_sheaf g G I).mpr
    (freeOnSurjectiveOpen_sheaf g G I h)

end AlgebraicGeometry

end
