module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EtaleSliceFromFieldPoint
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.IntegerSlicePoint

/-!
# An étale slice through every point of a smooth groupoid with unramified diagonal

Let `s, t : E ⟶ W` be smooth morphisms of schemes such that `(s, t) : E ⟶ W × W` is unramified
(the product over `Spec ℤ`). Then for every `e ∈ E` there are a monomorphism `ι : Y ⟶ W` and an
open subscheme `P` of `E ×_{s, W, ι} Y` which surjects onto `Y`, is étale over `W` through `t`,
and contains a point lying over `t(e)`.

## Main results

* `Stacks.AlgebraicGeometry.unramifiedAt_of_comp`: if `h ≫ j` is unramified at `x`, so is `h`.
* `Stacks.AlgebraicGeometry.exists_etale_slice_of_unramified_pair`: for smooth `s, t : E ⟶ W`
  with `(s, t)` unramified, every `e ∈ E` gives a monomorphism `ι : Y ⟶ W` and an open
  subscheme of `E ×_{s, W, ι} Y` surjecting onto `Y`, étale over `W` through `t`, and containing
  a point over `t(e)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.AlgebraicGeometry

/-- **Unramifiedness at a point descends to the first factor.** If `h ≫ j` is unramified at
`x`, then so is `h`. -/
theorem unramifiedAt_of_comp {X Y Y' : Scheme.{u}} (h : X ⟶ Y') (j : Y' ⟶ Y)
    [LocallyOfFiniteType (h ≫ j)] (x : X) (hx : UnramifiedAt (h ≫ j) x) :
    UnramifiedAt h x := by
  have : LocallyOfFiniteType h := LocallyOfFiniteType.of_comp (g := j) inferInstance
  rw [unramifiedAt_iff_formallyUnramified_stalkMap] at hx ⊢
  rw [Scheme.Hom.stalkMap_comp] at hx
  exact RingHom.FormallyUnramified.of_comp (f := (j.stalkMap (h x)).hom) hx

/-- A map into a pullback is locally of finite type if its first component is. -/
private theorem locallyOfFiniteType_lift_of_fst {X A B C : Scheme.{u}} (a : X ⟶ A) (b : X ⟶ B)
    {f : A ⟶ C} {g : B ⟶ C} (h : a ≫ f = b ≫ g) [LocallyOfFiniteType a] :
    LocallyOfFiniteType (pullback.lift a b h : X ⟶ pullback f g) :=
  have : LocallyOfFiniteType (pullback.lift a b h ≫ pullback.fst f g) := by
    rw [pullback.lift_fst]; infer_instance
  LocallyOfFiniteType.of_comp (g := pullback.fst f g) inferInstance

/-- **An étale slice through every point of a smooth groupoid with unramified diagonal.** Let
`s, t : E ⟶ W` be smooth with `(s, t) : E ⟶ W × W` unramified. For every `e ∈ E` there are a
monomorphism `ι : Y ⟶ W` and an open immersion `p : P ⟶ E ×_{s, W, ι} Y` such that `P` is étale
over `W` through `t`, surjects onto `Y`, and contains a point lying over `t(e)`. -/
theorem exists_etale_slice_of_unramified_pair {E W : Scheme.{u}} (s t : E ⟶ W) [Smooth s]
    [Smooth t]
    (hDM : ∀ e : E, UnramifiedAt (pullback.lift s t (terminal.hom_ext _ _) :
      E ⟶ pullback (terminal.from W) (terminal.from W)) e) (e : E) :
    ∃ (Y P : Scheme.{u}) (ι : Y ⟶ W) (p : P ⟶ pullback s ι),
      Mono ι ∧ IsOpenImmersion p ∧ Etale (p ≫ pullback.fst s ι ≫ t) ∧
        Function.Surjective (p ≫ pullback.snd s ι).base ∧
        ∃ x : P, (p ≫ pullback.fst s ι ≫ t) x = t e := by
  classical
  obtain ⟨_, ⟨U₀, hU', rfl⟩, he₀U', -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (s e)) isOpen_univ
  set U' : W.Opens := U₀ with hU'def
  have : IsAffine U'.toScheme := hU'
  set E' : E.Opens := s ⁻¹ᵁ U' with hE'
  set s' : E'.toScheme ⟶ U'.toScheme := s ∣_ U' with hs'
  set t' : E'.toScheme ⟶ W := E'.ι ≫ t with ht'
  have : Smooth s' := MorphismProperty.of_isPullback (P := @Smooth)
    (isPullback_morphismRestrict s U').flip inferInstance
  have : Smooth t' := by rw [ht']; infer_instance
  set w := t e with hw
  set K := AlgebraicClosure (W.residueField w)
  set φK : W.residueField w ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (algebraMap (W.residueField w) K) with hφK
  set gV : pullback (t'.fiberToSpecResidueField w) (Spec.map φK) ⟶ Spec (.of K) :=
    pullback.snd _ _ with hgV
  set pV : pullback (t'.fiberToSpecResidueField w) (Spec.map φK) ⟶ E'.toScheme :=
    pullback.fst _ _ ≫ t'.fiberι w with hpV
  set φV := pullback.fst (t'.fiberToSpecResidueField w) (Spec.map φK) ≫ t'.fiberι w ≫ s'
    with hφV
  have : Smooth (t'.fiberToSpecResidueField w) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback t' (W.fromSpecResidueField w)) ‹Smooth t'›
  have : Smooth gV := MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback (t'.fiberToSpecResidueField w) (Spec.map φK)) inferInstance
  set gK : Spec (.of K) ⟶ W := Spec.map φK ≫ W.fromSpecResidueField w with hgK
  have sqA : IsPullback pV gV t' gK :=
    (IsPullback.of_hasPullback (t'.fiberToSpecResidueField w) (Spec.map φK)).paste_horiz
      (IsPullback.of_hasPullback t' (W.fromSpecResidueField w))
  set aU := terminal.from U'.toScheme
  set aW := terminal.from W
  set mZ : pullback aU (gK ≫ aW) ⟶ pullback aU aW :=
    pullback.map aU (gK ≫ aW) aU aW (𝟙 _) gK (𝟙 _) (by simp) (by simp) with hmZ
  set lE : E'.toScheme ⟶ pullback aU aW := pullback.lift s' t' (terminal.hom_ext _ _) with hlE
  set fV : pullback (t'.fiberToSpecResidueField w) (Spec.map φK) ⟶ pullback aU (gK ≫ aW) :=
    pullback.lift φV gV (terminal.hom_ext _ _) with hfV
  have sqB : IsPullback mZ (pullback.snd aU (gK ≫ aW)) (pullback.snd aU aW) gK := by
    refine IsPullback.of_right (h₁₂ := pullback.fst aU aW) (v₁₃ := aU) (h₂₂ := aW) ?_
      (by simp [mZ]) (IsPullback.of_hasPullback aU aW)
    have : mZ ≫ pullback.fst aU aW = pullback.fst aU (gK ≫ aW) := by simp [mZ]
    rw [this]
    exact IsPullback.of_hasPullback aU (gK ≫ aW)
  have sqD : IsPullback pV fV lE mZ := by
    refine (IsPullback.of_right (h₁₂ := pullback.snd aU (gK ≫ aW)) (v₁₃ := gK)
      (h₂₂ := pullback.snd aU aW) ?_ ?_ sqB.flip).flip
    · have h1 : fV ≫ pullback.snd aU (gK ≫ aW) = gV := pullback.lift_snd _ _ _
      have h2 : lE ≫ pullback.snd aU aW = t' := pullback.lift_snd _ _ _
      rw [h1, h2]
      exact sqA.flip
    · have hmf : mZ ≫ pullback.fst aU aW = pullback.fst aU (gK ≫ aW) := by simp [mZ]
      have hms : mZ ≫ pullback.snd aU aW = pullback.snd aU (gK ≫ aW) ≫ gK := by simp [mZ]
      have hff : fV ≫ pullback.fst aU (gK ≫ aW) = φV := pullback.lift_fst _ _ _
      have hfs : fV ≫ pullback.snd aU (gK ≫ aW) = gV := pullback.lift_snd _ _ _
      have hlf : lE ≫ pullback.fst aU aW = s' := pullback.lift_fst _ _ _
      have hls : lE ≫ pullback.snd aU aW = t' := pullback.lift_snd _ _ _
      apply pullback.hom_ext
      · rw [Category.assoc fV, hmf, hff, Category.assoc pV, hlf, hφV, hpV, Category.assoc]
      · rw [Category.assoc fV, hms, ← Category.assoc fV, hfs, Category.assoc pV, hls]
        exact sqA.w.symm
  have : LocallyOfFiniteType lE := locallyOfFiniteType_lift_of_fst s' t' _
  have : LocallyOfFiniteType fV :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqD inferInstance
  have hDM' : ∀ x : E'.toScheme, UnramifiedAt lE x := by
    intro x
    set m : pullback aU aW ⟶ pullback aW aW :=
      pullback.map aU aW aW aW U'.ι (𝟙 W) (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)
    have hcomp : lE ≫ m = E'.ι ≫ pullback.lift s t (terminal.hom_ext _ _) := by
      have hmf : m ≫ pullback.fst aW aW = pullback.fst aU aW ≫ U'.ι := by simp [m]
      have hms : m ≫ pullback.snd aW aW = pullback.snd aU aW := by simp [m]
      have hlf : lE ≫ pullback.fst aU aW = s' := pullback.lift_fst _ _ _
      have hls : lE ≫ pullback.snd aU aW = t' := pullback.lift_snd _ _ _
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hmf, ← Category.assoc, hlf, pullback.lift_fst, hs',
          morphismRestrict_ι]
      · rw [Category.assoc, Category.assoc, hms, hls, pullback.lift_snd, ht']
    have : LocallyOfFiniteType (pullback.lift s t (terminal.hom_ext _ _) :
        E ⟶ pullback aW aW) := locallyOfFiniteType_lift_of_fst s t _
    have : LocallyOfFiniteType (lE ≫ m) := by rw [hcomp]; infer_instance
    refine unramifiedAt_of_comp lE m x ?_
    rw [hcomp]
    exact unramifiedAt_comp_of_isOpenImmersion E'.ι _ x (hDM _)
  have hfVu : ∀ v, UnramifiedAt fV v := fun v => (unramifiedAt_isPullback_iff sqD v).2 (hDM' _)
  have hgen := fun v => maximalIdeal_le_span_closure_of_unramifiedAt_pullback aU (gK ≫ aW) gV φV
    (terminal.hom_ext _ _) v (hfVu v)
  have : Nonempty ((pullback (t'.fiberToSpecResidueField w) (Spec.map φK) : Scheme.{u}) :
      Type u) := by
    obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := t'.fiberToSpecResidueField w) (g := Spec.map φK)
      (show t'.fiber w from t'.asFiber (⟨e, he₀U'⟩ : E'.toScheme))
      (Nonempty.some (inferInstance : Nonempty (Spec (.of K))))
      (Subsingleton.elim _ _)
    exact ⟨y⟩
  obtain ⟨v, hsep, hmap⟩ := exists_point_map_maximalIdeal_eq_of_isAlgClosed gV φV hgen
  obtain ⟨r, f, P, p, hp, het, x, hx⟩ :=
    exists_etale_slice_of_map_maximalIdeal_fieldPoint s' t' w φK v hsep hmap
  revert p hp het hx
  set Iι := (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn f))).subschemeι with hIι
  intro p hp het hx
  have hbig : IsPullback (pullback.fst s' Iι ≫ E'.ι) (pullback.snd s' Iι) s (Iι ≫ U'.ι) :=
    (IsPullback.of_hasPullback s' Iι).paste_horiz (isPullback_morphismRestrict s U').flip
  set p₁ : P ⟶ pullback s (Iι ≫ U'.ι) := p ≫ hbig.isoPullback.hom with hp₁
  have : IsOpenImmersion p := hp
  have : IsOpenImmersion p₁ := by rw [hp₁]; infer_instance
  have hp₁fst : p₁ ≫ pullback.fst s (Iι ≫ U'.ι) = p ≫ pullback.fst s' Iι ≫ E'.ι := by
    rw [hp₁, Category.assoc, hbig.isoPullback_hom_fst]
  obtain ⟨O, p', hp', hsurj, hfac⟩ :=
    exists_isOpenImmersion_surjective_pullback_opens s (Iι ≫ U'.ι) p₁
  have hp'fst : p' ≫ pullback.fst s (O.ι ≫ Iι ≫ U'.ι) = p ≫ pullback.fst s' Iι ≫ E'.ι := by
    rw [← hp₁fst, ← hfac, Category.assoc, pullback.lift_fst]
  refine ⟨O.toScheme, P, O.ι ≫ Iι ≫ U'.ι, p', inferInstance, hp', ?_, hsurj, x, ?_⟩ <;>
    rw [← Category.assoc, hp'fst]
  · simpa only [Category.assoc, ht'] using het
  · simpa only [Category.assoc, ht'] using hx

end Stacks.AlgebraicGeometry

end
