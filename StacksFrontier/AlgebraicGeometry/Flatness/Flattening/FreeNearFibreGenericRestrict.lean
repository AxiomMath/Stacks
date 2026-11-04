module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeNearFibreGeneric
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.FibrePowerBaseChange
public import StacksFrontier.AlgebraicGeometry.StrictTransform.RestrictOpen

/-!
# Freeness near the fibre generic points is local on the base

Let `f : X ⟶ S`, let `I` be a quasi-coherent ideal on `S` and let `F` be a quasi-coherent
`𝒪_X`-module. Over an open `V ⊆ S` the whole situation of [Stacks, Tag 0811] restricts along open
immersions: the blowup of `V` in `I|_V` is the preimage of `V` in `Bl_I(S)` ([Stacks, Tag 0805],
an open immersion being flat), so `X_V ×_V Bl_{I|V}(V)` is an *open subscheme* of `X ×_S Bl_I(S)`,
and the strict transform over `V` is the restriction of the strict transform.

`AlgebraicGeometry.FreeNearFibreGeneric` is a pointwise condition whose two ingredients — being a
generic point of a fibre, and having a free neighbourhood — are both local on the source, so it
both restricts to and descends from the opens of the base.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_strictTransformSheaf_restrict`: the shared geometric
  input — an open immersion `k` of the restricted base change into the base change, with the
  comparison of the two strict transforms along it, the recognition of its image, and the
  comparison of the two fibre-genericity conditions.
* `AlgebraicGeometry.freeNearFibreGeneric_strictTransformSheaf_restrict`: freeness near the fibre
  generic points restricts to an open of the base.
* `AlgebraicGeometry.freeNearFibreGeneric_of_restrict`: it descends from a family of opens of the
  base covering the images of all the points — the shape a gluing argument consumes.

## Implementation notes

The sheaf-level comparison is `Stacks.StrictTransform.pullbackSheafBlowUpIso` at the open
immersion `k`, followed by `Stacks.SupportedQuotient.supportedSectionsCokernelIso`: the two
cokernels are taken over the same subset of the small base change, because `k⁻¹` of the
exceptional preimage upstairs is the exceptional preimage downstairs
(`AlgebraicGeometry.Scheme.IdealSheafData.support_comap` and functoriality of `comap`), and over
isomorphic modules, because both are pullbacks of `F` along the two equal composites out of the
small base change.

Freeness is transported through the `AlgebraicGeometry.Scheme.Modules.pullback` form of
restriction rather than the `SheafOfModules.over` form in which
`AlgebraicGeometry.FreeNearFibreGeneric` is stated: in the pullback form the transport is the
composition isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp` together with
`restrictFunctor_obj_free_iso`, the statement that the restriction of a finite free module along
an open immersion is finite free. The passage between the two forms is
`Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso` one way and
`AlgebraicGeometry.Scheme.Modules.overEquiv`, which is an equivalence, the other way.

Genericity of a point of a fibre is preserved and reflected because `k` is an open immersion whose
image is saturated for the projection to the blowup: the fibre of `k z` is `k` of the fibre of `z`
(the comparison `b` of the two blowups is injective), and it is contained in the image of `k`, so
`closure {k z} ∩ im k = k '' closure {z}` (`Topology.IsInducing.closure_eq_preimage_closure_image`)
decides the inclusion on either side.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### Trivialisations on an open, in pullback form -/

/-- A trivialisation of `G` on an open `U`, read as a trivialisation of the pullback of `G` along
the inclusion of `U`. This is
`Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso` composed with
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
theorem nonempty_pullback_iso_free_of_over {Z : Scheme.{u}} (G : Z.Modules) (U : Z.Opens)
    (ι : Type u) (h : Nonempty (G.over U ≅ SheafOfModules.free.{u} ι)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj G ≅ SheafOfModules.free.{u} ι) :=
  h.elim fun e ↦ ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app G).symm ≪≫
    (_root_.Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso
      U ι G e).symm ≪≫ _root_.restrictFunctor_obj_free_iso U.ι ι⟩

/-- A trivialisation of the pullback of `G` along the inclusion of an open `U`, read as a
trivialisation of `G.over U`. The passage back is possible because
`AlgebraicGeometry.Scheme.Modules.overEquiv` is an equivalence, hence fully faithful, and carries
the free module over the sliced structure sheaf to the free module on the open subscheme
(`Stacks.AlgebraicGeometry.IrreducibleDevissage.freeOverEquivIso`). -/
theorem nonempty_over_iso_free_of_pullback {Z : Scheme.{u}} (G : Z.Modules) (U : Z.Opens)
    (ι : Type u) (h : Nonempty ((Scheme.Modules.pullback U.ι).obj G ≅ SheafOfModules.free.{u} ι)) :
    Nonempty (G.over U ≅ SheafOfModules.free.{u} ι) :=
  h.elim fun e ↦ ⟨(Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app G ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app G ≪≫ e ≪≫
      _root_.Stacks.AlgebraicGeometry.IrreducibleDevissage.freeOverEquivIso Z U ι)⟩

/-- Precomposing with an open immersion preserves a trivialisation of a pullback: the pullback
along `u ≫ v` is the pullback along `u` of the pullback along `v`, and the restriction of a free
module along an open immersion is free of the same index. -/
theorem nonempty_pullback_iso_free_comp {Z A C : Scheme.{u}} (G : Z.Modules) (ι : Type u)
    (u : A ⟶ C) [IsOpenImmersion u] (v : C ⟶ Z)
    (h : Nonempty ((Scheme.Modules.pullback v).obj G ≅ SheafOfModules.free.{u} ι)) :
    Nonempty ((Scheme.Modules.pullback (u ≫ v)).obj G ≅ SheafOfModules.free.{u} ι) :=
  h.elim fun e ↦ ⟨((Scheme.Modules.pullbackComp u v).app G).symm ≪≫
    (Scheme.Modules.pullback u).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback u).app (SheafOfModules.free.{u} ι)).symm ≪≫
      _root_.restrictFunctor_obj_free_iso u ι⟩

/-- **Freeness on an open pulls back along an open immersion.** If `Q'` is the pullback of `Q`
along an open immersion `k` and `Q` is free of rank `n` on `W`, then `Q'` is free of rank `n` on
`k⁻¹(W)`. -/
theorem nonempty_over_iso_free_preimage {B B' : Scheme.{u}} (k : B' ⟶ B) [IsOpenImmersion k]
    {Q : B.Modules} {Q' : B'.Modules} (eQ : (Scheme.Modules.pullback k).obj Q ≅ Q')
    (W : B.Opens) (n : ℕ)
    (h : Nonempty (Q.over W ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)))) :
    Nonempty (Q'.over (k ⁻¹ᵁ W) ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) := by
  have : IsOpenImmersion (k ∣_ W) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_morphismRestrict k W).flip inferInstance
  have h₁ := nonempty_pullback_iso_free_comp Q (ULift.{u} (Fin n)) (k ∣_ W) W.ι
    (nonempty_pullback_iso_free_of_over Q W (ULift.{u} (Fin n)) h)
  rw [morphismRestrict_ι k W] at h₁
  refine nonempty_over_iso_free_of_pullback Q' (k ⁻¹ᵁ W) (ULift.{u} (Fin n)) (h₁.elim fun e ↦ ?_)
  exact ⟨(Scheme.Modules.pullback (k ⁻¹ᵁ W).ι).mapIso eQ.symm ≪≫
    (Scheme.Modules.pullbackComp (k ⁻¹ᵁ W).ι k).app Q ≪≫ e⟩

/-- **Freeness on an open pushes forward along an open immersion.** If `Q'` is the pullback of `Q`
along an open immersion `k` and `Q'` is free of rank `n` on `W'`, then `Q` is free of rank `n` on
the open image `k(W')`. -/
theorem nonempty_over_iso_free_image {B B' : Scheme.{u}} (k : B' ⟶ B) [IsOpenImmersion k]
    {Q : B.Modules} {Q' : B'.Modules} (eQ : (Scheme.Modules.pullback k).obj Q ≅ Q')
    (W' : B'.Opens) (n : ℕ)
    (h : Nonempty (Q'.over W' ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)))) :
    Nonempty (Q.over (k ''ᵁ W') ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) := by
  have h₁ : Nonempty ((Scheme.Modules.pullback (W'.ι ≫ k)).obj Q ≅
      SheafOfModules.free.{u} (ULift.{u} (Fin n))) :=
    (nonempty_pullback_iso_free_of_over Q' W' (ULift.{u} (Fin n)) h).elim fun e ↦
      ⟨((Scheme.Modules.pullbackComp W'.ι k).app Q).symm ≪≫
        (Scheme.Modules.pullback W'.ι).mapIso eQ ≪≫ e⟩
  rw [← Scheme.Hom.isoImage_hom_ι k W'] at h₁
  have h₂ := nonempty_pullback_iso_free_comp Q (ULift.{u} (Fin n)) (k.isoImage W').inv
    ((k.isoImage W').hom ≫ (k ''ᵁ W').ι) h₁
  rw [Iso.inv_hom_id_assoc] at h₂
  exact nonempty_over_iso_free_of_pullback Q (k ''ᵁ W') (ULift.{u} (Fin n)) h₂

/-! ### Genericity in a fibre along an open immersion -/

/-- **Genericity in a fibre is preserved and reflected by an open immersion saturated for the
projection.** Let `k : B' ⟶ B` be an open immersion with `k ≫ q = q' ≫ b` for an injective `b`,
and suppose every `q`-fibre through a point of the image of `k` is contained in that image. Then a
point `z` of `B'` is a generic point of its `q'`-fibre exactly when `k z` is a generic point of
its `q`-fibre. -/
theorem fibre_generic_iff_of_isOpenImmersion {B B' T T' : Scheme.{u}} (q : B ⟶ T) (q' : B' ⟶ T')
    (k : B' ⟶ B) [IsOpenImmersion k] (b : T' ⟶ T) (hb : Function.Injective b.base)
    (hcomm : k ≫ q = q' ≫ b)
    (hsat : ∀ z : B', q.base ⁻¹' {q.base (k.base z)} ⊆ Set.range k.base) (z : B') :
    (q'.base ⁻¹' {q'.base z} ⊆ closure {z}) ↔
      (q.base ⁻¹' {q.base (k.base z)} ⊆ closure {k.base z}) := by
  have hpt : ∀ w : B', q.base (k.base w) = b.base (q'.base w) := fun w ↦
    congrArg (fun a : B' ⟶ T ↦ a.base w) hcomm
  have hpre : q'.base ⁻¹' {q'.base z} = k.base ⁻¹' (q.base ⁻¹' {q.base (k.base z)}) := by
    refine Set.ext fun w ↦ ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hpt]
    exact ⟨fun hw ↦ by rw [hw], fun hw ↦ hb hw⟩
  have hcl : closure ({z} : Set B') = k.base ⁻¹' closure ({k.base z} : Set B) := by
    rw [k.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
  rw [hpre, hcl]
  refine ⟨fun hz x hx ↦ ?_, fun hz ↦ Set.preimage_mono hz⟩
  obtain ⟨w, rfl⟩ := hsat z hx
  exact hz hx

/-! ### The restricted situation as an open subscheme -/

/-- **The strict transform over an open of the base is the restriction of the strict transform.**
For `V : S.Opens` there is an open immersion `k` of the base change `X_V ×_V Bl_{I|V}(V)` into the
base change `X ×_S Bl_I(S)` such that:

* its image is the locus where `X ×_S Bl_I(S)` lies over `V`;
* a point of the small base change is a generic point of its fibre over `Bl_{I|V}(V)` exactly when
  its image is a generic point of its fibre over `Bl_I(S)`;
* the pullback along `k` of the strict transform of `F` in `I` is the strict transform of the
  restriction of `F` in `I|_V`.

This is [Stacks, Tag 0805] for the open immersion `V.ι`, which is flat, together with
[Stacks, Tag 080D] commuting with flat pullback. -/
theorem exists_isOpenImmersion_strictTransformSheaf_restrict (f : X ⟶ S) (I : S.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (V : S.Opens) :
    ∃ k : Stacks.StrictTransform.baseChange (f ∣_ V) (blowUpToBase (I.comap V.ι)) ⟶
        Stacks.StrictTransform.baseChange f (blowUpToBase I),
      IsOpenImmersion k ∧
      (∀ x : Stacks.StrictTransform.baseChange f (blowUpToBase I),
        f.base ((pullback.fst f (blowUpToBase I)).base x) ∈ V → x ∈ Set.range k.base) ∧
      (∀ z : Stacks.StrictTransform.baseChange (f ∣_ V) (blowUpToBase (I.comap V.ι)),
        ((pullback.snd (f ∣_ V) (blowUpToBase (I.comap V.ι))).base ⁻¹'
            {(pullback.snd (f ∣_ V) (blowUpToBase (I.comap V.ι))).base z} ⊆ closure {z}) ↔
          (pullback.snd f (blowUpToBase I)).base ⁻¹'
            {(pullback.snd f (blowUpToBase I)).base (k.base z)} ⊆ closure {k.base z}) ∧
      Nonempty ((Scheme.Modules.pullback k).obj
          (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) ≅
        Stacks.StrictTransform.sheaf (f ∣_ V) (blowUpToBase (I.comap V.ι))
          (exceptionalIdeal (I.comap V.ι)) ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F)) := by
  set bI := blowUpToBase I with hbI
  set bJ := blowUpToBase (I.comap V.ι) with hbJ
  set p := pullback.fst f bI with hp
  set q := pullback.snd f bI with hq
  set p' := pullback.fst (f ∣_ V) bJ with hp'
  set q' := pullback.snd (f ∣_ V) bJ with hq'
  obtain ⟨b, hb⟩ := exists_isPullback_blowUpToBase_comap V.ι I
  have hcomm : (f ⁻¹ᵁ V).ι ≫ f = (f ∣_ V) ≫ V.ι := (morphismRestrict_ι f V).symm
  have hkcomm : (p' ≫ (f ⁻¹ᵁ V).ι) ≫ f = (q' ≫ b) ≫ bI := by
    calc (p' ≫ (f ⁻¹ᵁ V).ι) ≫ f = (p' ≫ (f ∣_ V)) ≫ V.ι := by
          rw [Category.assoc, hcomm, Category.assoc]
      _ = (q' ≫ bJ) ≫ V.ι := by rw [pullback.condition]
      _ = (q' ≫ b) ≫ bI := by rw [Category.assoc, hb.w, Category.assoc]
  set k := pullback.lift (p' ≫ (f ⁻¹ᵁ V).ι) (q' ≫ b) hkcomm with hk
  have hkp : k ≫ p = p' ≫ (f ⁻¹ᵁ V).ι := pullback.lift_fst _ _ _
  have hkq : k ≫ q = q' ≫ b := pullback.lift_snd _ _ _
  have hkqz : ∀ z, q.base (k.base z) = b.base (q'.base z) := fun z ↦
    congrArg (fun a : Stacks.StrictTransform.baseChange (f ∣_ V) bJ ⟶ blowUp I ↦ a.base z) hkq
  have hbw : ∀ y, bI.base (b.base y) = V.ι.base (bJ.base y) := fun y ↦
    (congrArg (fun a : blowUp (I.comap V.ι) ⟶ S ↦ a.base y) hb.w).symm
  have hout : IsPullback p' (k ≫ q) ((f ⁻¹ᵁ V).ι ≫ f) bI := by
    rw [hkq, hcomm]
    exact (IsPullback.of_hasPullback (f ∣_ V) bJ).paste_vert hb
  have hkpb : IsPullback p' k (f ⁻¹ᵁ V).ι p :=
    hout.of_bot hkp.symm (IsPullback.of_hasPullback f bI)
  have hkoi : IsOpenImmersion k :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hkpb inferInstance
  have hboi : IsOpenImmersion b :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hb inferInstance
  -- the image of `k` is the locus over `V`
  have hrange : ∀ x : Stacks.StrictTransform.baseChange f bI,
      f.base (p.base x) ∈ V → x ∈ Set.range k.base := by
    intro x hx
    rw [range_base_of_isPullback hkpb.flip]
    exact ⟨⟨p.base x, hx⟩, rfl⟩
  refine ⟨k, hkoi, hrange, ?_, ?_⟩
  · -- genericity transfers
    refine fibre_generic_iff_of_isOpenImmersion q q' k b hboi.base_open.injective hkq ?_
    intro z x hx
    refine hrange x ?_
    have h₁ : f.base (p.base x) = bI.base (q.base x) :=
      congrArg (fun a : Stacks.StrictTransform.baseChange f bI ⟶ S ↦ a.base x)
        (pullback.condition (f := f) (g := bI))
    rw [h₁, hx.trans (hkqz z), hbw]
    exact (bJ.base (q'.base z)).2
  · -- the two strict transforms agree
    have hZ' : k.base ⁻¹' Stacks.StrictTransform.exceptionalPreimage f bI (exceptionalIdeal I) =
        Stacks.StrictTransform.exceptionalPreimage (f ∣_ V) bJ
          (exceptionalIdeal (I.comap V.ι)) := by
      show k.base ⁻¹' (q.base ⁻¹' ((I.comap bI).support : Set (blowUp I))) =
        q'.base ⁻¹' (((I.comap V.ι).comap bJ).support : Set (blowUp (I.comap V.ι)))
      simp only [Scheme.IdealSheafData.support_comap]
      refine Set.ext fun z ↦ ?_
      show bI.base (q.base (k.base z)) ∈ I.support ↔
        V.ι.base (bJ.base (q'.base z)) ∈ I.support
      rw [hkqz, hbw]
    have eH : (Scheme.Modules.pullback (k ≫ p)).obj F ≅
        (Scheme.Modules.pullback p').obj
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F) :=
      (Scheme.Modules.pullbackCongr hkp).app F ≪≫
        ((Scheme.Modules.pullbackComp p' (f ⁻¹ᵁ V).ι).app F).symm
    refine ⟨Stacks.StrictTransform.pullbackSheafBlowUpIso f I F k ≪≫ ?_⟩
    rw [hZ']
    exact Stacks.SupportedQuotient.supportedSectionsCokernelIso _ eH

/-! ### The two directions -/

/-- **Freeness near the fibre generic points restricts to an open of the base.** If the strict
transform of `F` in `I` is free of finite rank near every generic point of a fibre of
`X ×_S Bl_I(S) ⟶ Bl_I(S)`, then over an open `V ⊆ S` the strict transform of the restriction of
`F` in `I|_V` is free of finite rank near every generic point of a fibre of
`X_V ×_V Bl_{I|V}(V) ⟶ Bl_{I|V}(V)`. -/
theorem freeNearFibreGeneric_strictTransformSheaf_restrict (f : X ⟶ S) (I : S.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (V : S.Opens)
    (h : FreeNearFibreGeneric (Limits.pullback.snd f (blowUpToBase I))
          (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :
    FreeNearFibreGeneric (Limits.pullback.snd (f ∣_ V) (blowUpToBase (I.comap V.ι)))
      (Stacks.StrictTransform.sheaf (f ∣_ V) (blowUpToBase (I.comap V.ι))
        (exceptionalIdeal (I.comap V.ι)) ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F)) := by
  obtain ⟨k, hkoi, -, hgen, ⟨eQ⟩⟩ :=
    exists_isOpenImmersion_strictTransformSheaf_restrict f I F V
  have := hkoi
  intro z hz
  obtain ⟨W, n, hzW, hfree⟩ := h (k.base z) ((hgen z).mp hz)
  exact ⟨k ⁻¹ᵁ W, n, hzW, nonempty_over_iso_free_preimage k eQ W n hfree⟩

/-- **Freeness near the fibre generic points descends from the opens of the base.** If every point
of the base change `X ×_S Bl_I(S)` has an open neighbourhood `V` of its image in `S` over which
the restricted strict transform is free of finite rank near the generic points of its fibres, then
the strict transform of `F` in `I` is free of finite rank near the generic points of the fibres of
`X ×_S Bl_I(S) ⟶ Bl_I(S)`. This is the shape a gluing argument consumes. -/
theorem freeNearFibreGeneric_of_restrict (f : X ⟶ S) (I : S.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ z : Stacks.StrictTransform.baseChange f (blowUpToBase I), ∃ V : S.Opens,
      f.base ((Limits.pullback.fst f (blowUpToBase I)).base z) ∈ V ∧
        FreeNearFibreGeneric (Limits.pullback.snd (f ∣_ V) (blowUpToBase (I.comap V.ι)))
          (Stacks.StrictTransform.sheaf (f ∣_ V) (blowUpToBase (I.comap V.ι))
            (exceptionalIdeal (I.comap V.ι)) ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F))) :
    FreeNearFibreGeneric (Limits.pullback.snd f (blowUpToBase I))
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) := by
  intro x hx
  obtain ⟨V, hxV, hV⟩ := h x
  obtain ⟨k, hkoi, hrange, hgen, ⟨eQ⟩⟩ :=
    exists_isOpenImmersion_strictTransformSheaf_restrict f I F V
  have := hkoi
  obtain ⟨z, rfl⟩ := hrange x hxV
  obtain ⟨W', n, hzW', hfree⟩ := hV z ((hgen z).mpr hx)
  exact ⟨k ''ᵁ W', n, (Scheme.Hom.apply_mem_image_iff k).mpr hzW',
    nonempty_over_iso_free_image k eQ W' n hfree⟩

end AlgebraicGeometry

end
