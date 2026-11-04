module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitReduction
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Descent of an étale-chart condition along an étale covering of the target scheme

Let `P` be a property of morphisms of schemes which is étale local on the source and target
(Stacks 04QZ), and let `f : F ⟶ h_T` be a morphism from a presheaf to a scheme of the big fppf
site. If `{Vᵢ ⟶ T}` is a jointly surjective family of étale morphisms and every base change
`F ×_T Vᵢ ⟶ Vᵢ` satisfies `P` on every étale chart (Stacks 03MJ), then so does `f`.

## Main results

* `AlgebraicGeometry.C1590Private.holdsOnEveryEtaleChart_of_etaleCover`.

## References

* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An étale-chart condition descends along an étale covering of the target scheme.** -/
theorem holdsOnEveryEtaleChart_of_etaleCover {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ : BigFppfOver B S hS} (f : F ⟶ yoneda.obj T₀)
    {ι : Type*} (Vi : ι → BigFppfOver B S hS) (vi : ∀ i, Vi i ⟶ T₀)
    (hv : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (vi i)))
    (hsurj : ∀ t : (BigFppfOver.toScheme B S hS).obj T₀,
      ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (vi i)))
    (Fi : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (fi : ∀ i, Fi i ⟶ yoneda.obj (Vi i))
    (ji : ∀ i, Fi i ⟶ F) (hsq : ∀ i, IsPullback (ji i) (fi i) f (yoneda.map (vi i)))
    (hFi : ∀ i, Space.HoldsOnEveryEtaleChart B S hS P (fi i)) :
    Space.HoldsOnEveryEtaleChart B S hS P f := by
  intro U V a b h ha hb hcomm
  let L := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan L :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : V ⟶ T₀, yoneda.map b₀ = b :=
    ⟨_, Yoneda.fullyFaithful.map_preimage b⟩
  have hb₀ : Etale (L.map b₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ b₀).1 hb
  rw [hP.iff_forall_exists_etale_neighborhood]
  intro x
  obtain ⟨i, t, ht⟩ := hsurj (L.map b₀ (L.map h x))
  have hpbV := (IsPullback.of_hasPullback b₀ (vi i)).map L
  have hpbU := (IsPullback.of_hasPullback h (pullback.fst b₀ (vi i))).map L
  have hfst : Etale (L.map (pullback.fst b₀ (vi i))) :=
    MorphismProperty.of_isPullback hpbV.flip (hv i)
  have hsnd : Etale (L.map (pullback.snd b₀ (vi i))) :=
    MorphismProperty.of_isPullback hpbV hb₀
  have hfst' : Etale (L.map (pullback.fst h (pullback.fst b₀ (vi i)))) :=
    MorphismProperty.of_isPullback hpbU.flip hfst
  -- a point over `x`
  obtain ⟨w, hw⟩ := Artin.ContractionSituation.exists_toScheme_map_pullback_fst_eq b₀ (vi i)
    (y := L.map h x) (z := t) ht.symm
  obtain ⟨y, hy⟩ := Artin.ContractionSituation.exists_toScheme_map_pullback_fst_eq h
    (pullback.fst b₀ (vi i)) (y := x) (z := w) hw.symm
  refine ⟨_, _, L.map (pullback.fst h (pullback.fst b₀ (vi i))),
    L.map (pullback.fst b₀ (vi i)), L.map (pullback.snd h (pullback.fst b₀ (vi i))), y,
    hfst', hfst, hy, ?_, ?_⟩
  · rw [← L.map_comp, ← pullback.condition, L.map_comp]
  · -- the chart of `Fᵢ`
    have hbig : IsPullback (yoneda.map (pullback.snd h (pullback.fst b₀ (vi i)) ≫
        pullback.snd b₀ (vi i))) (yoneda.map (pullback.fst h (pullback.fst b₀ (vi i))))
        (yoneda.map (vi i)) (a ≫ f) := by
      rw [← hcomm, ← Functor.map_comp]
      exact (((IsPullback.of_hasPullback h (pullback.fst b₀ (vi i))).flip.paste_horiz
        (IsPullback.of_hasPullback b₀ (vi i)).flip).map yoneda)
    let a'' := (hsq i).lift (yoneda.map (pullback.fst h (pullback.fst b₀ (vi i))) ≫ a)
      (yoneda.map (pullback.snd h (pullback.fst b₀ (vi i)) ≫ pullback.snd b₀ (vi i)))
      (by rw [Category.assoc, ← hbig.w])
    have hsqa : IsPullback a'' (yoneda.map (pullback.fst h (pullback.fst b₀ (vi i)))) (ji i) a :=
      IsPullback.of_right (by rw [(hsq i).lift_snd]; exact hbig) ((hsq i).lift_fst _ _ _)
        (hsq i).flip
    have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    refine hFi i _ _ a'' (yoneda.map (pullback.snd b₀ (vi i))) _
      (MorphismProperty.of_isPullback hsqa.flip ha)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 hsnd) ?_
    rw [← Functor.map_comp]
    exact ((hsq i).lift_snd _ _ _).symm

end AlgebraicGeometry.C1590Private

end
