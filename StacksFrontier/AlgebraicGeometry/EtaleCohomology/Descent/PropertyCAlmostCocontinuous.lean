module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs

/-!
# Property (C), closed morphisms, and almost cocontinuity

A morphism of schemes `f : X ⟶ Y` has *property (C)* when every scheme étale over `X` is
dominated, by a surjection over `X`, by the base change along `f` of a scheme étale over `Y`.
This file proves [Stacks, Tag 04DV]: if every étale base change `X ×_Y V ⟶ V` of `f` has
property (C) and is a closed map, then base change `Y.Etale ⥤ X.Etale`, `V ↦ X ×_Y V`, is
almost cocontinuous in the sense of [Stacks, Tag 04B7].

## The shape of the argument

Let `V` be étale over `Y` and let `{U_i ⟶ X ×_Y V}` be an étale covering. Property (C) for
`X ×_Y V ⟶ V` supplies for each `i` an étale `v_i : V_i ⟶ V` together with a surjection
`X ×_Y V_i ⟶ U_i` over `X ×_Y V`. The images of the `v_i` then cover the image `Z` of
`X ×_Y V ⟶ V`, which is closed by the second hypothesis, so adjoining the open immersion of
`V_0 = V \ Z` to the family `{V_i ⟶ V}` produces an étale covering of `V`. Each member of that
covering satisfies one of the two alternatives in the definition of almost cocontinuity:
`X ×_Y V_0` is empty, hence sheaf theoretically empty, while for `i ≠ 0` the base change
`X ×_Y V_i ⟶ X ×_Y V` factors through `U_i` and so lies in the given sieve.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChange_isAlmostCocontinuous` is
  [Stacks, Tag 04DV]: property (C) and closedness after every étale base change make base
  change between the small étale sites almost cocontinuous.

## Implementation notes

`Stacks.EtaleCohomology.smallEtaleBaseChange f` sends an étale `Y`-scheme `V` to the fibre
product `V ×_Y X`, whose projection to `X` is the second one; the proof therefore moves across
the symmetry isomorphism with `X ×_Y V`, against which property (C) is stated.

The closedness hypothesis is used only through
`Topology.IsClosedMap.isClosed_range`, which turns it into closedness of the image `Z`; it is
the complement of `Z` that supplies the extra member `V_0` of the covering.

## References

* [Stacks Project, Tag 04DV](https://stacks.math.columbia.edu/tag/04DV)
* [Stacks Project, Tag 04B7](https://stacks.math.columbia.edu/tag/04B7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- An object of the small étale site of `X` with empty underlying scheme is sheaf
theoretically empty: the empty family covers it, so the empty sieve on it is covering. -/
lemma isSheafTheoreticallyEmpty_of_isEmpty {X : Scheme.{u}} (U : X.Etale) (hU : IsEmpty U.left) :
    SheafTheoreticallyEmptySite (smallEtaleTopology X) U := by
  have hbot : Sieve.ofArrows (C := X.Etale) (I := PEmpty.{u + 1})
      (fun i ↦ PEmpty.elim i) (fun i ↦ PEmpty.elim i) = (⊥ : Sieve U) := by
    ext V f
    refine ⟨fun hf ↦ ?_, fun hf ↦ hf.elim⟩
    obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff _ _ f).mp hf
    exact PEmpty.elim i
  show (⊥ : Sieve U) ∈ smallEtaleTopology X U
  rw [← hbot, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  exact False.elim (hU.false x)

/-- The two projections of a point of a pullback of schemes have the same image in the base. -/
private theorem pullback_condition_apply {A B C : Scheme.{u}} (a : A ⟶ C) (b : B ⟶ C)
    (z : ↑(pullback a b)) : a (pullback.fst a b z) = b (pullback.snd a b z) := by
  simpa using congrArg (fun k : Scheme.Hom _ _ ↦ k.base z) (pullback.condition (f := a) (g := b))

/-- **Stacks Project, Tag 04DV.** If every étale base change `X ×_Y V ⟶ V` of `f : X ⟶ Y` has
property (C) and is a closed map, then base change `Y.Etale ⥤ X.Etale`, `V ↦ X ×_Y V`, is an
almost cocontinuous functor of small étale sites. -/
@[stacks 04DV]
theorem smallEtaleBaseChange_isAlmostCocontinuous
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hC : ∀ {V : Scheme.{u}} (v : V ⟶ Y), Etale v →
      HasPropertyC (pullback.snd f v))
    (hclosed : ∀ {V : Scheme.{u}} (v : V ⟶ Y), Etale v →
      IsClosedMap (pullback.snd f v).base) :
    IsAlmostCocontinuous (smallEtaleBaseChange f)
      (smallEtaleTopology Y) (smallEtaleTopology X) := by
  let F := smallEtaleBaseChange f
  show ∀ U : Y.Etale, ∀ {S : Sieve (F.obj U)},
    S ∈ smallEtaleTopology X (F.obj U) →
      ∃ T : Sieve U, T ∈ smallEtaleTopology Y U ∧
        ∀ ⦃V : Y.Etale⦄ (g : V ⟶ U), T g →
          SheafTheoreticallyEmptySite (smallEtaleTopology X) (F.obj V) ∨ S (F.map g)
  intro U S hS
  let : Category.{u, u + 1}
      (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ X) :=
    (inferInstance : Category.{u, u + 1} (X.Etale))
  let : Category.{u, u + 1}
      (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ Y) :=
    (inferInstance : Category.{u, u + 1} (Y.Etale))
  let : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : Scheme.IsJointlySurjectivePreserving (@Etale : MorphismProperty Scheme.{u}) :=
    Scheme.isJointlySurjectivePreserving (@Etale : MorphismProperty Scheme.{u})
  obtain ⟨𝒰, h𝒰over, h𝒰et, h𝒰S⟩ :=
    (Scheme.mem_smallGrothendieckTopology (P := @Etale) (S := X)
      (X := F.obj U) S).mp hS
  let (i : 𝒰.I₀) : (𝒰.X i).Over X := h𝒰over.over i
  let (i : 𝒰.I₀) : (𝒰.f i).IsOver X := h𝒰over.isOver_map i
  let q : pullback f U.hom ⟶ U.left := pullback.snd f U.hom
  let e : (F.obj U).left ≅ pullback f U.hom := by
    show pullback U.hom f ≅ pullback f U.hom
    exact pullbackSymmetry U.hom f
  have he : e.hom ≫ q = pullback.fst U.hom f := by
    show (pullbackSymmetry U.hom f).hom ≫ pullback.snd f U.hom = _
    exact pullbackSymmetry_hom_comp_snd U.hom f
  have hPC : HasPropertyC q := hC U.hom U.prop
  have hdata (i : 𝒰.I₀) :
      ∃ (V : Scheme) (v : V ⟶ U.left), Etale v ∧
        ∃ (r : pullback q v ⟶ 𝒰.X i), Surjective r ∧
          r ≫ (𝒰.f i ≫ e.hom) = pullback.fst q v := by
    have hg : Etale (𝒰.f i ≫ e.hom) := by
      have : Etale (𝒰.f i) := 𝒰.map_prop i
      infer_instance
    exact hPC (𝒰.f i ≫ e.hom) hg
  choose V v hV r hr hfac using hdata
  let Vi : 𝒰.I₀ → Y.Etale := fun i ↦ by
    let : Etale (v i) := hV i
    exact Scheme.Etale.mk (v i ≫ U.hom)
  let ai : ∀ i, Vi i ⟶ U := fun i ↦ MorphismProperty.Over.homMk (v i) (by rfl)
  let Wi : 𝒰.I₀ → X.Etale := fun i ↦ by
    let : Etale (𝒰.X i ↘ X) := h𝒰et i
    exact Scheme.Etale.mk (𝒰.X i ↘ X)
  let β : ∀ i, Wi i ⟶ F.obj U := fun i ↦
    (𝒰.f i).asOverProp X (hX := h𝒰et i) (hY := (F.obj U).prop)
  have hβS (i : 𝒰.I₀) : S (β i) := by
    apply h𝒰S
    dsimp only [Scheme.Cover.toPresieveOverProp]
    show Presieve.ofArrows
      (fun j ↦ (𝒰.X j).asOverProp (P := (@Etale : MorphismProperty Scheme.{u})) X (h𝒰et j))
      (fun j ↦ (𝒰.f j).asOverProp (P := (@Etale : MorphismProperty Scheme.{u})) X) (β i)
    exact Presieve.ofArrows.mk i
  let Z : Set U.left := Set.range q
  have hZ : IsClosed Z := by
    dsimp [Z, q]
    exact (hclosed U.hom U.prop).isClosed_range
  let O : U.left.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let V0 : Y.Etale := by
    let : Etale (O.ι ≫ U.hom) := by infer_instance
    exact Scheme.Etale.mk (O.ι ≫ U.hom)
  let a0 : V0 ⟶ U := MorphismProperty.Over.homMk O.ι (by rfl)
  let Idx : Type u := Sum 𝒰.I₀ PUnit.{u + 1}
  let W : Idx → Y.Etale := fun j ↦ match j with
    | .inl i => Vi i
    | .inr _ => V0
  let a : ∀ j, W j ⟶ U := fun j ↦ match j with
    | .inl i => ai i
    | .inr _ => a0
  have hcover : Sieve.ofArrows W a ∈ smallEtaleTopology Y U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    have hpoint : ∀ y : U.left, ∃ j : Idx, y ∈ Set.range (a j).left := by
      intro y
      by_cases hy : y ∈ Z
      · obtain ⟨z, rfl⟩ := hy
        let z' : (F.obj U).left := e.inv z
        have hmem : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.precoverage @Etale (F.obj U).left := by
          simpa using 𝒰.mem₀
        have hcoverPoints := (Scheme.ofArrows_mem_precoverage_iff @Etale).mp hmem
        obtain ⟨i, hw⟩ := hcoverPoints.1 z'
        obtain ⟨w, hw⟩ := hw
        let : Surjective (r i) := hr i
        obtain ⟨t, ht⟩ := (r i).surjective w
        have hfst : pullback.fst q (v i) t = z := by
          calc
            pullback.fst q (v i) t = (r i ≫ (𝒰.f i ≫ e.hom)) t := by
              rw [hfac i]
            _ = e.hom (𝒰.f i w) := by simp [ht]
            _ = e.hom (e.inv z) := by rw [hw]
            _ = z := by simp
        refine ⟨Sum.inl i, ⟨pullback.snd q (v i) t, ?_⟩⟩
        show (v i) (pullback.snd q (v i) t) = q z
        rw [← pullback_condition_apply, hfst]
      · refine ⟨Sum.inr PUnit.unit, ⟨⟨y, hy⟩, ?_⟩⟩
        rfl
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact hpoint y
  have hEmpty0 : IsEmpty (F.obj V0).left := by
    show IsEmpty (Limits.pullback (C := Scheme.{u}) (O.ι ≫ U.hom) f)
    refine ⟨?_⟩
    intro z
    have hf : U.hom (O.ι (pullback.fst (O.ι ≫ U.hom) f z)) ∈ Set.range f :=
      ⟨pullback.snd (O.ι ≫ U.hom) f z, (pullback_condition_apply (O.ι ≫ U.hom) f z).symm⟩
    have hz : O.ι (pullback.fst (O.ι ≫ U.hom) f z) ∈ Z := by
      have hm : O.ι (pullback.fst (O.ι ≫ U.hom) f z) ∈ U.hom ⁻¹' Set.range f := hf
      simpa [Z, q, Scheme.Pullback.range_snd] using hm
    have hnot : O.ι (pullback.fst (O.ι ≫ U.hom) f z) ∉ Z := by
      show (pullback.fst (O.ι ≫ U.hom) f z).val ∉ Z
      exact (pullback.fst (O.ι ≫ U.hom) f z).property
    exact hnot hz
  refine ⟨Sieve.ofArrows W a, hcover, ?_⟩
  intro V g hg
  obtain ⟨j, b, rfl⟩ := (Sieve.mem_ofArrows_iff W a g).mp hg
  cases j with
  | inl i =>
      right
      have hcomm (i : 𝒰.I₀) : ((F.map (ai i)).left ≫ e.hom) ≫ q =
          Limits.pullback.fst (v i ≫ U.hom) f ≫ v i := by
        let : MorphismProperty.HasPullbacksAlong
            (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
        let : MorphismProperty.IsStableUnderBaseChangeAlong
            (@Etale : MorphismProperty Scheme.{u}) f :=
          ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
        let : HasPullback U.hom f :=
          MorphismProperty.HasPullbacksAlong.hasPullback
            (P := @Etale) (f := f) U.hom U.prop
        let : HasPullback (v i ≫ U.hom) f :=
          MorphismProperty.HasPullbacksAlong.hasPullback
            (P := @Etale) (f := f) (v i ≫ U.hom) (by infer_instance)
        dsimp only [F, smallEtaleBaseChange]
        have hU : ((MorphismProperty.Over.pullback
            (@Etale : MorphismProperty Scheme.{u}) ⊤ f).obj U).left =
            pullback U.hom f :=
          MorphismProperty.Over.pullback_obj_left
            (@Etale : MorphismProperty Scheme.{u}) ⊤ f U
        have hV : ((MorphismProperty.Over.pullback
            (@Etale : MorphismProperty Scheme.{u}) ⊤ f).obj (Vi i)).left =
            pullback (v i ≫ U.hom) f :=
          MorphismProperty.Over.pullback_obj_left
            (@Etale : MorphismProperty Scheme.{u}) ⊤ f (Vi i)
        cases hU
        cases hV
        have hformula := MorphismProperty.Over.pullback_map_left
          (@Etale : MorphismProperty Scheme.{u}) ⊤ f (ai i)
        let m := ((MorphismProperty.Over.pullback
          (@Etale : MorphismProperty Scheme.{u}) ⊤ f).map (ai i)).left
        have hstep₁ : (m ≫ e.hom) ≫ q = m ≫ pullback.fst U.hom f := by
          calc
            _ = m ≫ (e.hom ≫ q) := by rfl
            _ = _ := congrArg (fun k ↦ m ≫ k) he
        have hstep₂ : m ≫ pullback.fst U.hom f =
            pullback.fst (v i ≫ U.hom) f ≫ v i := by
          dsimp only [m]
          rw [hformula]
          exact pullback.lift_fst _ _ _
        exact hstep₁.trans hstep₂
      let ei (i : 𝒰.I₀) : (F.obj (Vi i)).left ⟶ pullback q (v i) :=
        Limits.pullback.lift ((F.map (ai i)).left ≫ e.hom)
          (Limits.pullback.fst (v i ≫ U.hom) f) (hcomm i)
      have hmap (i : 𝒰.I₀) : ei i ≫ r i ≫ 𝒰.f i = (F.map (ai i)).left := by
        apply (cancel_mono e.hom).1
        calc
          (ei i ≫ r i ≫ 𝒰.f i) ≫ e.hom =
              ei i ≫ (r i ≫ (𝒰.f i ≫ e.hom)) := by simp [Category.assoc]
          _ = ei i ≫ Limits.pullback.fst q (v i) := by rw [hfac i]
          _ = (F.map (ai i)).left ≫ e.hom := by
            exact pullback.lift_fst _ _ _
      have hdelta (i : 𝒰.I₀) : (ei i ≫ r i) ≫ (Wi i).hom =
          (F.obj (Vi i)).hom := by
        dsimp only [Wi]
        show (ei i ≫ r i) ≫ (𝒰.X i ↘ X) = (F.obj (Vi i)).hom
        calc
          (ei i ≫ r i) ≫ (𝒰.X i ↘ X) =
              ei i ≫ r i ≫ 𝒰.f i ≫ (F.obj U).hom := by
                rw [← (h𝒰over.isOver_map i).comp_over]
                simp [Category.assoc]
          _ = (F.map (ai i)).left ≫ (F.obj U).hom := by
                simpa only [Category.assoc] using congrArg
                  (fun k ↦ k ≫ (F.obj U).hom) (hmap i)
          _ = (F.obj (Vi i)).hom := by
            exact MorphismProperty.Over.w
              (P := (@Etale : MorphismProperty Scheme.{u})) (Q := ⊤) (F.map (ai i))
      let δ (i : 𝒰.I₀) : F.obj (Vi i) ⟶ Wi i :=
        MorphismProperty.Over.homMk (ei i ≫ r i) (hdelta i)
      have hfactor (i : 𝒰.I₀) : F.map (ai i) = δ i ≫ β i := by
        apply MorphismProperty.Over.Hom.ext
        show (F.map (ai i)).left = ei i ≫ r i ≫ 𝒰.f i
        exact (hmap i).symm
      have hAiS : S (F.map (ai i)) := by
        rw [hfactor i]
        exact S.downward_closed (hβS i) (δ i)
      rw [F.map_comp]
      exact S.downward_closed hAiS (F.map b)
  | inr j =>
      left
      have hEmptyV : IsEmpty (F.obj V).left := by
        refine ⟨fun x ↦ ?_⟩
        exact hEmpty0.false ((F.map b).left x)
      exact isSheafTheoreticallyEmpty_of_isEmpty (F.obj V) hEmptyV

end Stacks.EtaleCohomology

end
