module

public import StacksFrontier.AlgebraicGeometry.Full.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence

/-!
# Sequences of blowups at closed points from their localizations

Let `S` be a scheme, `s 0, …, s (n - 1)` pairwise distinct closed points of `S` whose open
complement `U` has quasi-compact inclusion, and `S_i = Spec 𝒪_{S, s i}`. This file proves the
sufficiency half of [Stacks, Tag 0BFY]: if `f : X ⟶ S` is an isomorphism over `U` and each base
change `X ×_S S_i ⟶ S_i` factors as a finite sequence of blowups at closed points lying over the
closed point of `S_i`, then `f` factors as a finite sequence of blowups at closed points lying
over the `s i`. Together with the necessity half
`AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsPointBlowups_of_corresponds`
this gives the tag.

## Main results

* `AlgebraicGeometry.LocalSchemesCover.nonempty_iso_of_baseChange`: two schemes over `S` which
  are isomorphisms over `U` and whose base changes to every `S_i` are isomorphic over `S_i` are
  isomorphic over `S`.
* `AlgebraicGeometry.isIso_pullback_snd_of_pointBlowupChain`: a sequence of blowups at closed
  points over the `s i` changes nothing over a flat morphism avoiding them, in particular over `U`.
* `AlgebraicGeometry.exists_pointBlowupChain_lift_local`: a sequence of blowups over a single
  `S_i` comes from a sequence of blowups over `S` which changes nothing over the other `S_j`.
* `AlgebraicGeometry.exists_pointBlowupChain_of_local`: local sequences over all the `S_i` at
  once come from one sequence over `S`.
* `AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsPointBlowups_of_forall`:
  the sufficiency half of [Stacks, Tag 0BFY].
* `AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsPointBlowups_iff_forall`:
  **Stacks Tag 0BFY**, both directions.

## Implementation notes

The source's proof constructs, from the local sequences, a global sequence whose localizations
are the given ones, and concludes because the base-change functor of [Stacks, Tag 0BFU] is an
equivalence ([Stacks, Tag 0BFV]). Only the reflection of isomorphisms is needed for that last
step, and it holds without any finiteness: the family `U ⟶ S`, `S_i ⟶ S` is an fpqc covering
(`AlgebraicGeometry.LocalSchemesCover.presieve₀_mem_fpqcPrecoverage`), so morphisms descend along
it. The leg over `U` is forced, both schemes being isomorphic to `U` there, and the overlap of two
distinct local schemes lies over `U`
(`AlgebraicGeometry.LocalSchemesCover.exists_lift_complement_of_ne`), so the family of local
isomorphisms is automatically compatible.

## References

* [Stacks Project, Tag 0BFY](https://stacks.math.columbia.edu/tag/0BFY)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0BFV](https://stacks.math.columbia.edu/tag/0BFV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.ResolutionOfSurfaces

universe u

namespace AlgebraicGeometry

namespace LocalSchemesCover

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- Two morphisms into a scheme over `S` which is an isomorphism over the open complement agree
as soon as they agree over `S` and the common composite lands in the open complement. -/
theorem hom_eq_of_isIso_pullback_snd {X : Scheme.{u}} {p : X ⟶ S}
    (hX : IsIso (pullback.snd p (complementOfClosedPoints s hs).ι)) {W : Scheme.{u}}
    (k₁ k₂ : W ⟶ X) (hk : k₁ ≫ p = k₂ ≫ p)
    (hW : Set.range (k₁ ≫ p).base ⊆ (complementOfClosedPoints s hs : Set S)) : k₁ = k₂ := by
  obtain ⟨c, hc⟩ := exists_lift_complement s hs (k₁ ≫ p) hW
  have h₁ := pullback.lift_fst k₁ c hc.symm
  have h₂ := pullback.lift_fst k₂ c (hc.trans hk).symm
  have hl : pullback.lift k₁ c hc.symm = pullback.lift k₂ c (hc.trans hk).symm :=
    (cancel_mono (pullback.snd p (complementOfClosedPoints s hs).ι)).1
      (by rw [pullback.lift_snd, pullback.lift_snd])
  rw [← h₁, ← h₂, hl]

variable {s hs}

/-- The legs of the descent problem producing a morphism `Z ⟶ X` over `S` from morphisms between
the base changes to the local schemes, when `X` is an isomorphism over the open complement. -/
def isoDescentLeg {Z X : Scheme.{u}} {pZ : Z ⟶ S} {pX : X ⟶ S}
    (hX : IsIso (pullback.snd pX (complementOfClosedPoints s hs).ι))
    (e : ∀ i, pullback pZ (S.fromSpecStalk (s i)) ⟶ pullback pX (S.fromSpecStalk (s i))) :
    (a : Option I) → pullback pZ (map s hs a) ⟶ X
  | none => pullback.snd pZ (complementOfClosedPoints s hs).ι ≫
      inv (pullback.snd pX (complementOfClosedPoints s hs).ι) ≫
        pullback.fst pX (complementOfClosedPoints s hs).ι
  | some i => e i ≫ pullback.fst pX (S.fromSpecStalk (s i))

/-- The legs of `AlgebraicGeometry.LocalSchemesCover.isoDescentLeg` lie over `S`. -/
theorem isoDescentLeg_comp {Z X : Scheme.{u}} {pZ : Z ⟶ S} {pX : X ⟶ S}
    (hX : IsIso (pullback.snd pX (complementOfClosedPoints s hs).ι))
    (e : ∀ i, pullback pZ (S.fromSpecStalk (s i)) ⟶ pullback pX (S.fromSpecStalk (s i)))
    (he : ∀ i, e i ≫ pullback.snd pX (S.fromSpecStalk (s i)) =
      pullback.snd pZ (S.fromSpecStalk (s i))) (a : Option I) :
    isoDescentLeg hX e a ≫ pX = pullback.fst pZ (map s hs a) ≫ pZ := by
  cases a with
  | none =>
    show (pullback.snd pZ (complementOfClosedPoints s hs).ι ≫
      inv (pullback.snd pX (complementOfClosedPoints s hs).ι) ≫
        pullback.fst pX (complementOfClosedPoints s hs).ι) ≫ pX = _
    rw [Category.assoc, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc,
      ← pullback.condition]
    rfl
  | some i =>
    show (e i ≫ pullback.fst pX (S.fromSpecStalk (s i))) ≫ pX = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, he, ← pullback.condition]
    rfl

include hs in
/-- **A morphism over `S` from local data.** Let `X` be an isomorphism over the open complement
`U`. Morphisms over the local schemes from the base changes of `Z` to those of `X` come from a
morphism `Z ⟶ X` over `S`. -/
theorem exists_hom_of_baseChange (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) {Z X : Scheme.{u}}
    {pZ : Z ⟶ S} {pX : X ⟶ S}
    (hX : IsIso (pullback.snd pX (complementOfClosedPoints s hs).ι))
    (e : ∀ i, pullback pZ (S.fromSpecStalk (s i)) ⟶ pullback pX (S.fromSpecStalk (s i)))
    (he : ∀ i, e i ≫ pullback.snd pX (S.fromSpecStalk (s i)) =
      pullback.snd pZ (S.fromSpecStalk (s i))) :
    ∃ t : Z ⟶ X, t ≫ pX = pZ ∧ ∀ i, pullback.fst pZ (S.fromSpecStalk (s i)) ≫ t =
      e i ≫ pullback.fst pX (S.fromSpecStalk (s i)) := by
  have hsf : Presieve.IsSheafFor (yoneda.obj X)
      (Presieve.ofArrows (fun a ↦ pullback pZ (map s hs a))
        (fun a ↦ pullback.fst pZ (map s hs a))) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck
        (presieve_pullback_mem_fpqcPrecoverage s hs hqc pZ))
  have hcomp : Presieve.Arrows.Compatible (yoneda.obj X)
      (fun a ↦ pullback.fst pZ (map s hs a)) (isoDescentLeg hX e) := by
    intro a b W ga gb hab
    show ga ≫ isoDescentLeg hX e a = gb ≫ isoDescentLeg hX e b
    have hover : (ga ≫ isoDescentLeg hX e a) ≫ pX = (gb ≫ isoDescentLeg hX e b) ≫ pX := by
      rw [Category.assoc, Category.assoc, isoDescentLeg_comp hX e he,
        isoDescentLeg_comp hX e he, ← Category.assoc, hab, Category.assoc]
    have hsnd : ∀ c : Option I, ∀ g : W ⟶ pullback pZ (map s hs c),
        (g ≫ pullback.fst pZ (map s hs c)) ≫ pZ =
          (g ≫ pullback.snd pZ (map s hs c)) ≫ map s hs c := fun c g ↦ by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have hrange : ∀ (c : Option I) (g : W ⟶ pullback pZ (map s hs c)),
        c = none → Set.range ((g ≫ pullback.fst pZ (map s hs c)) ≫ pZ).base ⊆
          (complementOfClosedPoints s hs : Set S) := by
      rintro c g rfl _ ⟨w, rfl⟩
      rw [hsnd]
      exact (complementOfClosedPoints s hs).range_ι.le ⟨_, rfl⟩
    have key : Set.range ((ga ≫ pullback.fst pZ (map s hs a)) ≫ pZ).base ⊆
        (complementOfClosedPoints s hs : Set S) → ga ≫ isoDescentLeg hX e a =
          gb ≫ isoDescentLeg hX e b := fun h ↦
      hom_eq_of_isIso_pullback_snd s hs hX _ _ hover (by
        rwa [Category.assoc, isoDescentLeg_comp hX e he, ← Category.assoc])
    match a, b with
    | none, _ => exact key (hrange none ga rfl)
    | some i, none => exact key (by rw [hab]; exact hrange none gb rfl)
    | some i, some j =>
      by_cases hij : i = j
      · subst hij
        exact congrArg (· ≫ isoDescentLeg hX e (some i)) ((cancel_mono _).1 hab)
      · obtain ⟨c, hc⟩ := exists_lift_complement_of_ne s hs hinj hij
          (z := (ga ≫ pullback.fst pZ (S.fromSpecStalk (s i))) ≫ pZ)
          (bi := ga ≫ pullback.snd pZ (S.fromSpecStalk (s i)))
          (bj := gb ≫ pullback.snd pZ (S.fromSpecStalk (s j)))
          (hsnd (some i) ga).symm
          ((hsnd (some j) gb).symm.trans (congrArg (· ≫ pZ) hab).symm)
        refine key ?_
        rintro _ ⟨w, rfl⟩
        show ((ga ≫ pullback.fst pZ (S.fromSpecStalk (s i))) ≫ pZ) w ∈ _
        rw [← hc]
        exact (complementOfClosedPoints s hs).range_ι.le ⟨_, rfl⟩
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf _ hcomp
  have ht' : ∀ a, pullback.fst pZ (map s hs a) ≫ t = isoDescentLeg hX e a := ht
  refine ⟨t, hom_ext_of_baseChange s hs hqc pZ _ _ fun a ↦ ?_, fun i ↦ ht' (some i)⟩
  rw [← Category.assoc, ht', isoDescentLeg_comp hX e he]

include hs in
/-- **Isomorphism over `S` from local isomorphisms.** Two schemes over `S` which are isomorphisms
over the open complement of an injective finite family of closed points, and whose base changes
to the local schemes at those points are isomorphic over the local schemes, are isomorphic over
`S`. -/
theorem nonempty_iso_of_baseChange (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) {Z X : Scheme.{u}}
    {pZ : Z ⟶ S} {pX : X ⟶ S}
    (hZ : IsIso (pullback.snd pZ (complementOfClosedPoints s hs).ι))
    (hX : IsIso (pullback.snd pX (complementOfClosedPoints s hs).ι))
    (e : ∀ i, pullback pZ (S.fromSpecStalk (s i)) ≅ pullback pX (S.fromSpecStalk (s i)))
    (he : ∀ i, (e i).hom ≫ pullback.snd pX (S.fromSpecStalk (s i)) =
      pullback.snd pZ (S.fromSpecStalk (s i))) :
    ∃ t : Z ≅ X, t.hom ≫ pX = pZ := by
  have he' : ∀ i, (e i).inv ≫ pullback.snd pZ (S.fromSpecStalk (s i)) =
      pullback.snd pX (S.fromSpecStalk (s i)) := fun i ↦ by
    rw [Iso.inv_comp_eq, he]
  obtain ⟨φ, hφ, hφi⟩ := exists_hom_of_baseChange hinj hqc hX (fun i ↦ (e i).hom) he
  obtain ⟨ψ, hψ, hψi⟩ := exists_hom_of_baseChange hinj hqc hZ (fun i ↦ (e i).inv) he'
  have hid : ∀ {A B : Scheme.{u}} {pA : A ⟶ S} {pB : B ⟶ S}
      (hA : IsIso (pullback.snd pA (complementOfClosedPoints s hs).ι))
      (e : ∀ i, pullback pA (S.fromSpecStalk (s i)) ≅ pullback pB (S.fromSpecStalk (s i)))
      (α : A ⟶ B) (β : B ⟶ A), α ≫ pB = pA → β ≫ pA = pB →
      (∀ i, pullback.fst pA (S.fromSpecStalk (s i)) ≫ α =
        (e i).hom ≫ pullback.fst pB (S.fromSpecStalk (s i))) →
      (∀ i, pullback.fst pB (S.fromSpecStalk (s i)) ≫ β =
        (e i).inv ≫ pullback.fst pA (S.fromSpecStalk (s i))) → α ≫ β = 𝟙 A := by
    intro A B pA pB hA e α β hα hβ hαi hβi
    refine hom_ext_of_baseChange s hs hqc pA _ _ fun a ↦ ?_
    cases a with
    | none =>
      refine hom_eq_of_isIso_pullback_snd s hs hA _ _ (by simp [hα, hβ]) ?_
      rw [Category.assoc, Category.assoc, hβ, hα]
      rintro _ ⟨w, rfl⟩
      show (pullback.fst pA (complementOfClosedPoints s hs).ι ≫ pA) w ∈ _
      rw [pullback.condition]
      exact (complementOfClosedPoints s hs).range_ι.le ⟨_, rfl⟩
    | some i =>
      show pullback.fst pA (S.fromSpecStalk (s i)) ≫ α ≫ β =
        pullback.fst pA (S.fromSpecStalk (s i)) ≫ 𝟙 A
      rw [reassoc_of% (hαi i), hβi i, Iso.hom_inv_id_assoc, Category.comp_id]
  refine ⟨⟨φ, ψ, hid hZ e φ ψ hφ hψ hφi hψi, ?_⟩, hφ⟩
  exact hid hX (fun i ↦ (e i).symm) ψ φ hψ hφ hψi hφi

end LocalSchemesCover

/-! ### One blowup, read over a flat morphism to the base -/

/-- Isomorphisms compatible with maps to a common target compose. -/
private theorem exists_iso_trans_comp {C : Type*} [Category C] {X Y Z B : C} {x : X ⟶ B}
    {y : Y ⟶ B} {z : Z ⟶ B} (h₁ : ∃ e : X ≅ Y, e.hom ≫ y = x)
    (h₂ : ∃ e : Y ≅ Z, e.hom ≫ z = y) : ∃ e : X ≅ Z, e.hom ≫ z = x := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  exact ⟨e₁ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₁]⟩

/-- **Blowing up a closed point changes nothing over a flat morphism avoiding it.** If `w` is a
closed point of `W` over `S` and `v : V ⟶ S` is flat with image avoiding the image of `w`, then
the base change of `Bl_w W` along `v` is the base change of `W`. -/
theorem exists_pullback_blowUpToBase_comp_iso_of_notMem_range {W S V : Scheme.{u}} (p : W ⟶ S)
    (v : V ⟶ S) [Flat v] (w : W) (hw : IsClosed ({w} : Set W)) (hv : p w ∉ Set.range v) :
    ∃ e : pullback (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : Closeds W)) ≫ p) v ≅ pullback p v,
      e.hom ≫ pullback.snd p v = pullback.snd _ v := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
  have hsupp : ((M.comap (pullback.fst p v)).support : Set ↥(pullback p v)) = ∅ := by
    rw [Scheme.IdealSheafData.support_comap]
    show pullback.fst p v ⁻¹' (M.support : Set W) = ∅
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    refine Set.eq_empty_of_forall_notMem fun y hy => hv ⟨pullback.snd p v y, ?_⟩
    have hy' : pullback.fst p v y = w := hy
    rw [← hy', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have : IsIso (blowUpToBase (M.comap (pullback.fst p v))) :=
    isIso_blowUpToBase_of_support_eq_empty _ hsupp
  obtain ⟨h, hh⟩ := exists_isPullback_blowUpToBase_comap (pullback.fst p v) M
  have : IsIso (pullback.snd (blowUpToBase M) (pullback.fst p v)) := by
    rw [← hh.flip.isoPullback_inv_snd]
    infer_instance
  refine ⟨(pullbackRightPullbackFstIso p v (blowUpToBase M)).symm ≪≫
    asIso (pullback.snd (blowUpToBase M) (pullback.fst p v)), ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_snd]

/-- A closed point of the base change of `W` to the local scheme at a closed point `s`, lying over
the closed point there, maps to a closed point of `W`. -/
theorem isClosed_singleton_pullback_fst_fromSpecStalk {W S : Scheme.{u}} (p : W ⟶ S) (s : S)
    (hs : IsClosed ({s} : Set S)) (y : ↥(pullback p (S.fromSpecStalk s)))
    (hy : IsClosed ({y} : Set ↥(pullback p (S.fromSpecStalk s))))
    (hys : p (pullback.fst p (S.fromSpecStalk s) y) = s) :
    IsClosed ({pullback.fst p (S.fromSpecStalk s) y} : Set W) := by
  set f := pullback.fst p (S.fromSpecStalk s)
  refine isClosed_of_closure_subset fun w' hw' => ?_
  have hsp : f y ⤳ w' := specializes_iff_mem_closure.mpr hw'
  have hpw' : p w' = s := by
    simpa using (hsp.map p.continuous).mem_closed hs (by simpa using hys)
  have hrange : w' ∈ Set.range f := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecStalk]
    show p w' ⤳ s
    rw [hpw']
  obtain ⟨y'', rfl⟩ := hrange
  have hsp' : y ⤳ y'' := f.isEmbedding.isInducing.specializes_iff.mp hsp
  rw [Set.mem_singleton_iff.mp (hsp'.mem_closed hy rfl)]
  exact Set.mem_singleton _

/-- **Blowing up a closed point over `s`, read over the local scheme at `s`.** Let `y` be a closed
point of `W ×_S Spec 𝒪_{S, s}` over the closed point. Its image `w` in `W` is closed, lies over
`s`, and the base change of `Bl_w W` to `Spec 𝒪_{S, s}` is `Bl_y (W ×_S Spec 𝒪_{S, s})`. -/
theorem exists_pullback_blowUpToBase_comp_iso_blowUp {W S : Scheme.{u}} (p : W ⟶ S) (s : S)
    (hs : IsClosed ({s} : Set S)) (y : ↥(pullback p (S.fromSpecStalk s)))
    (hy : IsClosed ({y} : Set ↥(pullback p (S.fromSpecStalk s))))
    (hys : pullback.snd p (S.fromSpecStalk s) y = IsLocalRing.closedPoint (S.presheaf.stalk s)) :
    ∃ (hw : IsClosed ({pullback.fst p (S.fromSpecStalk s) y} : Set W)),
      p (pullback.fst p (S.fromSpecStalk s) y) = s ∧
      ∃ e : pullback (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{pullback.fst p (S.fromSpecStalk s) y}, hw⟩ : Closeds W)) ≫ p) (S.fromSpecStalk s) ≅
          blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{y}, hy⟩ : Closeds ↥(pullback p (S.fromSpecStalk s)))),
        e.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
            (⟨{y}, hy⟩ : Closeds ↥(pullback p (S.fromSpecStalk s)))) ≫
          pullback.snd p (S.fromSpecStalk s) = pullback.snd _ _ := by
  set f := pullback.fst p (S.fromSpecStalk s)
  have hpw : p (f y) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hys,
      Scheme.fromSpecStalk_closedPoint]
  have hw := isClosed_singleton_pullback_fst_fromSpecStalk p s hs y hy hpw
  refine ⟨hw, hpw, ?_⟩
  obtain ⟨_, hideal⟩ := vanishingIdeal_singleton_comap_pullbackFst p (S.fromSpecStalk s) (f y) hw
    (pointToSpecStalk p (f y) hpw) (pointToSpecStalk_comp_fromSpecStalk p (f y) hpw) y rfl
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{f y}, hw⟩ : Closeds W)
  set My := Scheme.IdealSheafData.vanishingIdeal
    (⟨{y}, hy⟩ : Closeds ↥(pullback p (S.fromSpecStalk s)))
  obtain ⟨h, hh⟩ :
      ∃ h : blowUp My ⟶ blowUp M, IsPullback (blowUpToBase My) h f (blowUpToBase M) := by
    rw [show My = M.comap f from hideal.symm]
    exact exists_isPullback_blowUpToBase_comap f M
  refine ⟨(pullbackRightPullbackFstIso p (S.fromSpecStalk s) (blowUpToBase M)).symm ≪≫
    hh.flip.isoPullback.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc,
    reassoc_of% hh.flip.isoPullback_inv_snd, pullbackRightPullbackFstIso_inv_snd_snd]

/-! ### Lifting a sequence of blowups over one local scheme -/

/-- **A sequence of blowups over one local scheme comes from a sequence over the base.** Let
`p₀ : W₀ ⟶ S` be an isomorphism over `Spec 𝒪_{S, s}` for a closed point `s`. A finite sequence of
blowups at closed points over the closed point of `Spec 𝒪_{S, s}` is the base change of a finite
sequence of blowups of `W₀` at closed points over `s`, and that sequence changes nothing over any
flat morphism to `S` whose image avoids `s`. -/
theorem exists_pointBlowupChain_lift_local {S W₀ : Scheme.{u}} (p₀ : W₀ ⟶ S) (s : S)
    (hs : IsClosed ({s} : Set S)) (hiso : IsIso (pullback.snd p₀ (S.fromSpecStalk s)))
    {Y : Scheme.{u}} {q : Y ⟶ Spec (S.presheaf.stalk s)}
    (hc : PointBlowupChain (Spec (S.presheaf.stalk s))
      {IsLocalRing.closedPoint (S.presheaf.stalk s)} Y q) :
    ∃ (W : Scheme.{u}) (g : W ⟶ W₀), PointBlowupChain W₀ (p₀ ⁻¹' {s}) W g ∧
      (∃ e : pullback (g ≫ p₀) (S.fromSpecStalk s) ≅ Y,
        e.hom ≫ q = pullback.snd (g ≫ p₀) (S.fromSpecStalk s)) ∧
      ∀ (V : Scheme.{u}) (v : V ⟶ S), Flat v → s ∉ Set.range v →
        ∃ e : pullback (g ≫ p₀) v ≅ pullback p₀ v,
          e.hom ≫ pullback.snd p₀ v = pullback.snd (g ≫ p₀) v := by
  induction hc with
  | refl =>
    refine ⟨W₀, 𝟙 W₀, .refl, ?_, fun V v _ _ => ?_⟩
    · rw [Category.id_comp]
      exact ⟨asIso (pullback.snd p₀ (S.fromSpecStalk s)), by simp⟩
    · rw [Category.id_comp]
      exact ⟨Iso.refl _, by simp⟩
  | @step Y' q' hc' y hy hyT ih =>
    obtain ⟨W', g', hchain', ⟨e', he'⟩, hoff'⟩ := ih
    obtain ⟨y', hy'def⟩ : ∃ y', y' = e'.inv y := ⟨_, rfl⟩
    have hy' : IsClosed ({y'} : Set ↥(pullback (g' ≫ p₀) (S.fromSpecStalk s))) := by
      have hset : ({y'} : Set ↥(pullback (g' ≫ p₀) (S.fromSpecStalk s))) =
          e'.hom ⁻¹' ({y} : Set Y') := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        refine ⟨fun hz => by rw [hz, hy'def]; simp, fun hz => ?_⟩
        rw [hy'def, ← hz]
        simp
      rw [hset]
      exact hy.preimage e'.hom.continuous
    have hys : pullback.snd (g' ≫ p₀) (S.fromSpecStalk s) y' =
        IsLocalRing.closedPoint (S.presheaf.stalk s) := by
      rw [← he', Scheme.Hom.comp_apply]
      simpa [hy'def] using Set.mem_singleton_iff.mp hyT
    obtain ⟨hw, hpw, e₁, he₁⟩ :=
      exists_pullback_blowUpToBase_comp_iso_blowUp (g' ≫ p₀) s hs y' hy' hys
    obtain ⟨_, hideal⟩ := vanishingIdeal_singleton_comap_of_isIso e'.hom y hy y' (by simp [hy'def])
    obtain ⟨d, hd⟩ : ∃ d : blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{y'}, hy'⟩ : Closeds ↥(pullback (g' ≫ p₀) (S.fromSpecStalk s)))) ≅
          blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y')),
        d.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y')) =
          blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
            (⟨{y'}, hy'⟩ : Closeds ↥(pullback (g' ≫ p₀) (S.fromSpecStalk s)))) ≫ e'.hom := by
      rw [← hideal]
      exact exists_blowUp_iso_comap_of_isIso e'.hom _
    have hwT : g' (pullback.fst (g' ≫ p₀) (S.fromSpecStalk s) y') ∈ p₀ ⁻¹' {s} := by
      show p₀ (g' _) = s
      rw [← Scheme.Hom.comp_apply]
      exact hpw
    refine ⟨_, _, hchain'.step _ hw hwT, ?_, fun V v hv hsv => ?_⟩
    · rw [Category.assoc]
      refine ⟨e₁ ≪≫ d, ?_⟩
      rw [Iso.trans_hom, Category.assoc, reassoc_of% hd, he']
      exact he₁
    · rw [Category.assoc]
      exact exists_iso_trans_comp
        (exists_pullback_blowUpToBase_comp_iso_of_notMem_range (g' ≫ p₀) v _ hw
          (by rw [hpw]; exact hsv)) (hoff' V v hv hsv)

/-- **A sequence of blowups at closed points over `T` changes nothing over a flat morphism whose
image avoids `T`.** In particular it is an isomorphism over the complement of `T`. -/
theorem isIso_pullback_snd_of_pointBlowupChain {S V : Scheme.{u}} (v : V ⟶ S) [Flat v]
    {T : Set S} (hT : ∀ t ∈ T, t ∉ Set.range v) {W : Scheme.{u}} {p : W ⟶ S}
    (hp : PointBlowupChain S T W p) : IsIso (pullback.snd p v) := by
  induction hp with
  | refl => infer_instance
  | @step W' p' hh w hw hwT ih =>
    obtain ⟨e, he⟩ := exists_pullback_blowUpToBase_comp_iso_of_notMem_range p' v w hw (hT _ hwT)
    rw [← he]
    infer_instance

/-- **Local sequences of blowups at closed points come from one sequence over the base.** Let
`s` be an injective family of closed points of `S`. Given, for every `i`, a finite sequence of
blowups `Y i ⟶ Spec 𝒪_{S, s i}` at closed points over the closed point, there is a finite
sequence of blowups `W ⟶ S` at closed points over the `s i` whose base change to every
`Spec 𝒪_{S, s i}` is `Y i`. -/
theorem exists_pointBlowupChain_of_local {S : Scheme.{u}} {n : ℕ} (s : Fin n → S)
    (hinj : Function.Injective s) (hclosed : ∀ j, IsClosed ({s j} : Set S))
    (Y : Fin n → Scheme.{u}) (q : ∀ i, Y i ⟶ Spec (S.presheaf.stalk (s i)))
    (hq : ∀ i, PointBlowupChain (Spec (S.presheaf.stalk (s i)))
      {IsLocalRing.closedPoint (S.presheaf.stalk (s i))} (Y i) (q i)) :
    ∃ (W : Scheme.{u}) (p : W ⟶ S), PointBlowupChain S (Set.range s) W p ∧
      ∀ i, ∃ e : pullback p (S.fromSpecStalk (s i)) ≅ Y i,
        e.hom ≫ q i = pullback.snd p (S.fromSpecStalk (s i)) := by
  have hmiss : ∀ i j, j ≠ i → s i ∉ Set.range (S.fromSpecStalk (s j)) := by
    intro i j hji hmem
    rw [Scheme.range_fromSpecStalk] at hmem
    have : s j ∈ ({s i} : Set S) := (show s i ⤳ s j from hmem).mem_closed (hclosed i) rfl
    exact hji (hinj (Set.mem_singleton_iff.mp this))
  suffices H : ∀ F : Finset (Fin n), ∃ (W : Scheme.{u}) (p : W ⟶ S),
      PointBlowupChain S (Set.range s) W p ∧
      (∀ i ∈ F, ∃ e : pullback p (S.fromSpecStalk (s i)) ≅ Y i,
        e.hom ≫ q i = pullback.snd p (S.fromSpecStalk (s i))) ∧
      ∀ i ∉ F, IsIso (pullback.snd p (S.fromSpecStalk (s i))) by
    obtain ⟨W, p, hp, hF, -⟩ := H Finset.univ
    exact ⟨W, p, hp, fun i => hF i (Finset.mem_univ i)⟩
  intro F
  induction F using Finset.induction_on with
  | empty => exact ⟨S, 𝟙 S, .refl, by simp, fun _ _ => inferInstance⟩
  | @insert i F hiF ih =>
    obtain ⟨W, p, hp, hF, hnF⟩ := ih
    obtain ⟨W', g, hg, ⟨e, he⟩, hoff⟩ :=
      exists_pointBlowupChain_lift_local p (s i) (hclosed i) (hnF i hiF) (hq i)
    have hoff' : ∀ j, j ≠ i → ∃ e : pullback (g ≫ p) (S.fromSpecStalk (s j)) ≅
        pullback p (S.fromSpecStalk (s j)), e.hom ≫ pullback.snd p (S.fromSpecStalk (s j)) =
          pullback.snd (g ≫ p) (S.fromSpecStalk (s j)) := fun j hji ↦
      hoff _ (S.fromSpecStalk (s j)) inferInstance (hmiss i j hji)
    refine ⟨W', g ≫ p, hp.comp hg fun y hy => ⟨i, (Set.mem_singleton_iff.mp hy).symm⟩,
      fun j hj => ?_, fun j hj => ?_⟩
    · rcases Finset.mem_insert.mp hj with rfl | hjF
      · exact ⟨e, he⟩
      · exact exists_iso_trans_comp (hoff' j fun h => hiF (h ▸ hjF)) (hF j hjF)
    · obtain ⟨e₁, he₁⟩ := hoff' j fun h => hj (h ▸ Finset.mem_insert_self _ _)
      have := hnF j fun h => hj (Finset.mem_insert_of_mem h)
      rw [← he₁]
      infer_instance

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u})

/-- **Stacks Project, Tag 0BFY**, sufficiency. If `f : X ⟶ S` corresponds to the local
modifications `g i : Y i ⟶ Spec 𝒪_{S, s i}` under a base-change functor of Tag 0BFU, and every
`g i` factors as a finite sequence of blowups at closed points over the closed point, then `f`
factors as a finite sequence of blowups at closed points over the distinguished points. -/
theorem factorsAsPointBlowups_of_forall (BC : BaseChangeFunctor D) (X : D.globalCategory)
    (Y : ∀ i, D.localCategory i) (hY : BC.functor.obj X ≅ Y)
    (h : ∀ i, FactorsAsPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Y i).obj.left (Y i).obj.hom) :
    FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom := by
  choose Y' f hchain e he using h
  obtain ⟨W, p, hp, hW⟩ := exists_pointBlowupChain_of_local D.points D.points_injective
    D.points_closed Y' f hchain
  have hloc : ∀ i : Fin D.n, ∃ E : pullback p (D.S.fromSpecStalk (D.points i)) ≅
      pullback X.obj.hom (D.S.fromSpecStalk (D.points i)),
      E.hom ≫ pullback.snd X.obj.hom (D.S.fromSpecStalk (D.points i)) =
        pullback.snd p (D.S.fromSpecStalk (D.points i)) := by
    intro i
    let E₂ : (Y i).obj ≅ (Over.pullback (D.S.fromSpecStalk (D.points i))).obj X.obj :=
      (ObjectProperty.ι _).mapIso (Pi.isoApp hY i).symm ≪≫ (BC.pullbackIso i).app X
    have hw : E₂.hom.left ≫ pullback.snd X.obj.hom (D.S.fromSpecStalk (D.points i)) =
        (Y i).obj.hom := Over.w E₂.hom
    have he' : (e i).inv ≫ (Y i).obj.hom = f i := by rw [← he i, Iso.inv_hom_id_assoc]
    exact exists_iso_trans_comp (exists_iso_trans_comp (hW i) ⟨(e i).symm, he'⟩)
      ⟨(Over.forget _).mapIso E₂, hw⟩
  let t : ULift.{u} (Fin D.n) → D.S := fun i ↦ D.points i.down
  have ht : ∀ i, t i ∈ closedPoints D.S := fun i ↦ mem_closedPoints_iff.mpr (D.points_closed i.down)
  have hU : complementOfClosedPoints t ht = D.complement := by
    ext x
    show x ∈ (⋂ i : ULift.{u} (Fin D.n), ({D.points i.down} : Set D.S)ᶜ) ↔
      x ∈ (Set.range D.points)ᶜ
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_range]
    exact ⟨fun h ⟨i, hi⟩ ↦ h (ULift.up i) hi.symm, fun h i hi ↦ h ⟨i.down, hi.symm⟩⟩
  have hinj : Function.Injective t := fun i j hij ↦ ULift.ext (D.points_injective hij)
  have hqc : QuasiCompact (complementOfClosedPoints t ht).ι := by
    rw [hU]
    exact D.complement_quasiCompact
  have hXU : IsIso (pullback.snd X.obj.hom (complementOfClosedPoints t ht).ι) := by
    rw [hU]
    exact X.property.2
  have hWU : IsIso (pullback.snd p (complementOfClosedPoints t ht).ι) := by
    refine isIso_pullback_snd_of_pointBlowupChain _ (T := Set.range D.points) ?_ hp
    rintro _ ⟨i, rfl⟩ hmem
    rw [Scheme.Opens.range_ι, hU] at hmem
    exact hmem ⟨i, rfl⟩
  choose E hE using hloc
  obtain ⟨t, ht⟩ := LocalSchemesCover.nonempty_iso_of_baseChange
    (hs := ht) hinj hqc hWU hXU (fun i ↦ E i.down) (fun i ↦ hE i.down)
  exact ⟨W, p, hp, t.symm, by rw [Iso.symm_hom, Iso.inv_comp_eq, ht]⟩

/-- **Stacks Project, Tag 0BFY.** Let `S` be a scheme with pairwise distinct closed points
`s 0, …, s (n - 1)` whose open complement has quasi-compact inclusion, and let `f : X ⟶ S`, of
finite presentation and an isomorphism over that complement, correspond under a base-change
functor of Tag 0BFU to the local modifications `g i : Y i ⟶ Spec 𝒪_{S, s i}`. Then `f` factors as
a finite sequence of blowups at closed points lying over the `s i` if and only if every `g i`
factors as a finite sequence of blowups at closed points lying over the closed point of
`Spec 𝒪_{S, s i}`. -/
@[stacks 0BFY]
theorem factorsAsPointBlowups_iff_forall (BC : BaseChangeFunctor D) (X : D.globalCategory)
    (Y : ∀ i, D.localCategory i) (hY : BC.functor.obj X ≅ Y) :
    FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom ↔
      ∀ i, FactorsAsPointBlowups (D.localScheme i)
        {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Y i).obj.left
        (Y i).obj.hom :=
  ⟨fun h i ↦ D.factorsAsPointBlowups_of_corresponds BC X i (Y i) (Pi.isoApp hY i) h,
    D.factorsAsPointBlowups_of_forall BC X Y hY⟩

end FinitePresentationAwayPointsSituation

end AlgebraicGeometry

end
