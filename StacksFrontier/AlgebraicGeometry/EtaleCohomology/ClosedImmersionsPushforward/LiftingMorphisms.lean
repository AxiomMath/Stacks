module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections

/-!
# Lifting morphisms from a closed subscheme

For a closed immersion `Z ⟶ X`, a morphism over `Z` between the base changes of two schemes
étale over `X` is induced by a span over `X` whose left leg becomes an isomorphism after base
change to `Z`.

## Main results

* `AlgebraicGeometry.exists_span_baseChange_iso` produces the required span and identifies its
  base change with the given morphism.

## Implementation notes

Base changes are represented by chosen categorical pullbacks. The isomorphism `e` records both
that the base change of the left leg is an isomorphism and the choice of its inverse; the two
displayed equalities say that its forward map is the canonical pullback map and that the given
morphism is induced by the right leg. We also record that `W` is étale over `X`; this follows
from the construction as an open subscheme of `U ×_X U'` and is needed when the result is
applied to the category of étale neighbourhoods.

The span is built from the graph of the given morphism: it is a section of an étale morphism,
hence an open immersion, and the corresponding open subscheme of the fibre product over `Z`
extends to an open subscheme of the fibre product over `X`, which is the required `W`.

## References

* [Stacks Project, Tag 04FV](https://stacks.math.columbia.edu/tag/04FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry


/-- An open subset of a closed subscheme is the preimage of an open subset of the ambient
scheme. -/
public lemma exists_open_extension_of_closedImmersion {A B : Scheme.{u}}
    (j : A ⟶ B) [IsClosedImmersion j] (V : A.Opens) :
    ∃ W : B.Opens, j ⁻¹ᵁ W = V := by
  obtain ⟨W, hW, hpre⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp V.2
  refine ⟨⟨W, hW⟩, ?_⟩
  ext x
  exact Set.ext_iff.mp hpre x

private lemma pullback_map_comp_fst {C : Type*} [Category C]
    {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ =
      pullback.fst f₁ f₂ ≫ i₁ := by
  dsimp [pullback.map]
  exact pullback.lift_fst _ _ _

private lemma pullback_map_comp_snd {C : Type*} [Category C]
    {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ =
      pullback.snd f₁ f₂ ≫ i₂ := by
  dsimp [pullback.map]
  exact pullback.lift_snd _ _ _

/-- **Stacks Project, Tag 04FV.** A morphism over a closed subscheme between the
base changes of two étale schemes is induced by a span over the original scheme,
and the left leg of that span becomes an isomorphism after base change. -/
@[stacks 04FV]
theorem exists_span_baseChange_iso
    {X Z U U' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : U ⟶ X) (g : U' ⟶ X) [Etale f] [Etale g]
    (h : pullback f i ⟶ pullback g i)
    (h_over : h ≫ pullback.snd g i = pullback.snd f i) :
    ∃ (W : Scheme.{u}) (a : W ⟶ U) (b : W ⟶ U')
      (hab : a ≫ f = b ≫ g) (_hW : Etale (a ≫ f)),
      let aZ : pullback (a ≫ f) i ⟶ pullback f i :=
        pullback.lift (pullback.fst (a ≫ f) i ≫ a) (pullback.snd (a ≫ f) i) (by
          rw [Category.assoc]
          exact pullback.condition)
      let bZ : pullback (a ≫ f) i ⟶ pullback g i :=
        pullback.lift (pullback.fst (a ≫ f) i ≫ b) (pullback.snd (a ≫ f) i) (by
          rw [Category.assoc, ← hab]
          exact pullback.condition)
      ∃ e : pullback (a ≫ f) i ≅ pullback f i,
        e.hom = aZ ∧ h = e.inv ≫ bZ := by
  -- The graph of `h` over `Z`: an open immersion, a section of the second projection.
  obtain ⟨j, hj, hjq, hjf, hjh⟩ : ∃ j : pullback f i ⟶
      pullback (pullback.fst f g) (pullback.fst f i), IsOpenImmersion j ∧
      j ≫ pullback.snd _ _ = 𝟙 _ ∧
      j ≫ pullback.fst _ _ ≫ pullback.fst f g = pullback.fst f i ∧
      j ≫ pullback.fst _ _ ≫ pullback.snd f g = h ≫ pullback.fst g i := by
    have hm : pullback.fst f i ≫ f = (h ≫ pullback.fst g i) ≫ g := by
      rw [pullback.condition, ← h_over, Category.assoc, Category.assoc, pullback.condition]
    let m : pullback f i ⟶ pullback f g :=
      pullback.lift (pullback.fst f i) (h ≫ pullback.fst g i) hm
    let j : pullback f i ⟶ pullback (pullback.fst f g) (pullback.fst f i) :=
      pullback.lift m (𝟙 _) ((pullback.lift_fst _ _ _).trans (Category.id_comp _).symm)
    have hjq : j ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    exact ⟨j, Unramified.section_isOpenImmersion _ j hjq, hjq,
      (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_fst _ _ _),
      (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)⟩
  let dIso := pullbackRightPullbackFstIso f i (pullback.fst f g)
  have : IsClosedImmersion (dIso.hom ≫ pullback.fst (pullback.fst f g ≫ f) i) := by
    infer_instance
  obtain ⟨O, hO⟩ := exists_open_extension_of_closedImmersion
    (dIso.hom ≫ pullback.fst (pullback.fst f g ≫ f) i) j.opensRange
  -- `O ×_M (M ×_X Z)` is the base change of `O ⟶ X` to `Z`, compatibly with the projections.
  have hbase : ∀ (c : (O : Scheme) ⟶ X), O.ι ≫ pullback.fst f g ≫ f = c →
      ∃ e : pullback O.ι (pullback.fst (pullback.fst f g ≫ f) i) ≅ pullback c i,
        e.inv ≫ pullback.snd _ _ ≫ pullback.fst (pullback.fst f g ≫ f) i =
          pullback.fst c i ≫ O.ι ∧
        e.inv ≫ pullback.snd _ _ ≫ pullback.snd (pullback.fst f g ≫ f) i =
          pullback.snd c i := by
    rintro c rfl
    exact ⟨pullbackRightPullbackFstIso _ i O.ι, pullbackRightPullbackFstIso_inv_snd_fst _ i O.ι,
      pullbackRightPullbackFstIso_inv_snd_snd _ i O.ι⟩
  obtain ⟨eW, heWfst, heWsnd⟩ := hbase ((O.ι ≫ pullback.fst f g) ≫ f) (Category.assoc _ _ _).symm
  refine ⟨O, O.ι ≫ pullback.fst f g, O.ι ≫ pullback.snd f g,
    by rw [Category.assoc, Category.assoc, pullback.condition], inferInstance, ?_⟩
  intro aZ bZ
  let tD := pullback.snd O.ι (pullback.fst (pullback.fst f g ≫ f) i) ≫ dIso.inv
  have hpre : Set.range (pullback.snd O.ι (pullback.fst (pullback.fst f g ≫ f) i) ≫ dIso.inv) =
      (dIso.hom ≫ pullback.fst (pullback.fst f g ≫ f) i) ⁻¹' O := by
    ext d
    constructor
    · rintro ⟨t, rfl⟩
      have ht : pullback.snd O.ι (pullback.fst (pullback.fst f g ≫ f) i) t ∈
          Set.range (pullback.snd O.ι (pullback.fst (pullback.fst f g ≫ f) i)) := ⟨t, rfl⟩
      rw [IsOpenImmersion.range_pullbackSnd] at ht
      simpa [Scheme.Hom.comp_apply, Scheme.Opens.opensRange_ι] using ht
    · intro hd
      have hd' : dIso.hom d ∈
          Set.range (pullback.snd O.ι (pullback.fst (pullback.fst f g ≫ f) i)) := by
        rw [IsOpenImmersion.range_pullbackSnd]
        simpa [Scheme.Hom.comp_apply, Scheme.Opens.opensRange_ι] using hd
      obtain ⟨t, ht⟩ := hd'
      exact ⟨t, by simp [Scheme.Hom.comp_apply, ht]⟩
  have hrange : Set.range tD = Set.range j := hpre.trans (congrArg SetLike.coe hO)
  let e := eW.symm ≪≫ IsOpenImmersion.isoOfRangeEq tD j hrange
  have hfac : e.hom ≫ j = eW.inv ≫ tD := by
    simp [e]
  have hfst : e.hom ≫ j ≫ pullback.fst _ _ =
      pullback.fst ((O.ι ≫ pullback.fst f g) ≫ f) i ≫ O.ι := by
    simp only [reassoc_of% hfac, tD, dIso, Category.assoc,
      pullbackRightPullbackFstIso_inv_fst, heWfst]
  have hsnd : e.hom ≫ pullback.snd f i = pullback.snd ((O.ι ≫ pullback.fst f g) ≫ f) i := by
    rw [← Category.id_comp (pullback.snd f i), ← hjq]
    simp only [Category.assoc, reassoc_of% hfac, tD, dIso,
      pullbackRightPullbackFstIso_inv_snd_snd, heWsnd]
  have h₁ : e.hom ≫ pullback.fst f i =
      pullback.fst ((O.ι ≫ pullback.fst f g) ≫ f) i ≫ O.ι ≫ pullback.fst f g := by
    rw [← hjf, reassoc_of% hfst]
  refine ⟨e, pullback.hom_ext (h₁.trans (pullback.lift_fst _ _ _).symm)
    (hsnd.trans (pullback.lift_snd _ _ _).symm), e.eq_inv_comp.mpr ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc e.hom h, ← hjh, reassoc_of% hfst]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc e.hom h, h_over, hsnd]
      exact (pullback.lift_snd _ _ _).symm

end AlgebraicGeometry
