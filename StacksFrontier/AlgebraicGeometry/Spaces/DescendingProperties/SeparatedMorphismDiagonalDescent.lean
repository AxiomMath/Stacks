module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ClosedImmersionMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed

/-!
# Separatedness of a morphism descends to a stage, through its diagonal

Let `B = lim B_i` be a directed inverse limit of algebraic spaces with affine transition
morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated algebraic spaces
over `B₀`, and let `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` be the base changes of `f₀` to `B_i` and
to `B`. If `f` is separated then `f_i` is separated for some `i ≥ 0`: this is Stacks 0851.

Separatedness of `f_i` is the closed-immersion property of its relative diagonal, and formation of
the relative diagonal commutes with base change, so the relative diagonal `X₀ ⟶ X₀ ×_{Y₀} X₀` of
`f₀` is a morphism of Situation 084W whose base changes to the stages and to the limit are the
relative diagonals of `f_i` and of `f`. The relative diagonal is locally of finite type, so Stacks
0850 applies to it.

## Main results

* `CategoryTheory.Limits.exists_iso_diagonal_comp_eq_pullbackLift_diagonal`: the diagonal of a
  base change is the base change of the diagonal.
* `AlgebraicGeometry.Space.MorphismDescentSituation.diagonal`: Situation 084W for the relative
  diagonal of `f₀`.
* `MorphismDescentSituation.exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits`: Stacks 0851
  under the chapter's standing convention, with no condition on the index.

## Implementation notes

Stacks 0851 is registered on
`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSeparated_mapAt_of_isSeparated_mapLimit`,
which bounds the index; the statement here asks instead only the convention of Section 70.2
(tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` of the system of bases, which
is the hypothesis of Stacks 0850 over `AlgebraicGeometry.Space.MorphismDescentSituation`.

## References

* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 0850](https://stacks.math.columbia.edu/tag/0850)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

/-! ### The relative diagonal of a base change

Formation of the relative diagonal commutes with base change. This is what carries Stacks 0850,
applied to the relative diagonal of `f₀`, to separatedness of `f_i`, which is how Stacks 0851 is
proved. -/

variable {C : Type*} [Category C] [HasPullbacks C]

/-- **Formation of the diagonal commutes with base change.** If
`F : Z₁ ×_{Z₀} X₀ ⟶ Z₁ ×_{Z₀} Y₀` is the base change of `f : X₀ ⟶ Y₀` along `t : Z₁ ⟶ Z₀`,
then the diagonal of `F` is, up to an isomorphism of its target, the base change along `t` of
the diagonal of `f`. -/
theorem exists_iso_diagonal_comp_eq_pullbackLift_diagonal
    {X₀ Y₀ Z₀ Z₁ : C}
    (a : X₀ ⟶ Z₀) (b : Y₀ ⟶ Z₀) (t : Z₁ ⟶ Z₀)
    (f : X₀ ⟶ Y₀) (hfb : f ≫ b = a)
    (F : pullback t a ⟶ pullback t b)
    (hFfst : F ≫ pullback.fst t b = pullback.fst t a)
    (hFsnd : F ≫ pullback.snd t b = pullback.snd t a ≫ f) :
    ∃ e : pullback F F ≅ pullback t (pullback.fst f f ≫ a),
      pullback.diagonal F ≫ e.hom =
        pullback.lift (pullback.fst t a) (pullback.snd t a ≫ pullback.diagonal f) (by
          simpa [Category.assoc] using (pullback.condition (f := t) (g := a))) := by
  have hdiag : pullback.fst f f ≫ a = pullback.snd f f ≫ a := by
    rw [← hfb, ← Category.assoc, pullback.condition, Category.assoc]
  have hq : pullback.fst F F ≫ pullback.fst t a = pullback.snd F F ≫ pullback.fst t a := by
    rw [← hFfst, ← Category.assoc, pullback.condition, Category.assoc]
  have wd : (pullback.fst F F ≫ pullback.snd t a) ≫ f =
      (pullback.snd F F ≫ pullback.snd t a) ≫ f := by
    rw [Category.assoc, Category.assoc, ← hFsnd, ← Category.assoc, pullback.condition,
      Category.assoc]
  let d₀ : pullback F F ⟶ pullback f f :=
    pullback.lift (pullback.fst F F ≫ pullback.snd t a) (pullback.snd F F ≫ pullback.snd t a) wd
  have hd₀₁ : d₀ ≫ pullback.fst f f = pullback.fst F F ≫ pullback.snd t a :=
    pullback.lift_fst _ _ _
  have hd₀₂ : d₀ ≫ pullback.snd f f = pullback.snd F F ≫ pullback.snd t a :=
    pullback.lift_snd _ _ _
  have we : (pullback.fst F F ≫ pullback.fst t a) ≫ t = d₀ ≫ pullback.fst f f ≫ a := by
    rw [← Category.assoc d₀, hd₀₁, Category.assoc, Category.assoc, pullback.condition]
  let e : pullback F F ⟶ pullback t (pullback.fst f f ≫ a) :=
    pullback.lift (pullback.fst F F ≫ pullback.fst t a) d₀ we
  have he₁ : e ≫ pullback.fst t (pullback.fst f f ≫ a) = pullback.fst F F ≫ pullback.fst t a :=
    pullback.lift_fst _ _ _
  have he₂ : e ≫ pullback.snd t (pullback.fst f f ≫ a) = d₀ := pullback.lift_snd _ _ _
  have w₁ : pullback.fst t (pullback.fst f f ≫ a) ≫ t =
      (pullback.snd t (pullback.fst f f ≫ a) ≫ pullback.fst f f) ≫ a := by
    rw [Category.assoc]
    exact pullback.condition
  have w₂ : pullback.fst t (pullback.fst f f ≫ a) ≫ t =
      (pullback.snd t (pullback.fst f f ≫ a) ≫ pullback.snd f f) ≫ a := by
    rw [Category.assoc, ← hdiag]
    exact pullback.condition
  let x₁ : pullback t (pullback.fst f f ≫ a) ⟶ pullback t a :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst f f) w₁
  let x₂ : pullback t (pullback.fst f f ≫ a) ⟶ pullback t a :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd f f) w₂
  have hx₁₁ : x₁ ≫ pullback.fst t a = pullback.fst t (pullback.fst f f ≫ a) :=
    pullback.lift_fst _ _ _
  have hx₁₂ : x₁ ≫ pullback.snd t a =
      pullback.snd t (pullback.fst f f ≫ a) ≫ pullback.fst f f := pullback.lift_snd _ _ _
  have hx₂₁ : x₂ ≫ pullback.fst t a = pullback.fst t (pullback.fst f f ≫ a) :=
    pullback.lift_fst _ _ _
  have hx₂₂ : x₂ ≫ pullback.snd t a =
      pullback.snd t (pullback.fst f f ≫ a) ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have hcomp : x₁ ≫ F = x₂ ≫ F := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hFfst, hx₁₁, hx₂₁]
    · simp only [Category.assoc, hFsnd, reassoc_of% hx₁₂, reassoc_of% hx₂₂, pullback.condition]
  let k : pullback t (pullback.fst f f ≫ a) ⟶ pullback F F := pullback.lift x₁ x₂ hcomp
  have hk₁ : k ≫ pullback.fst F F = x₁ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd F F = x₂ := pullback.lift_snd _ _ _
  have hδ₁ : pullback.diagonal F ≫ pullback.fst F F = 𝟙 _ := pullback.diagonal_fst F
  refine ⟨⟨e, k, ?_, ?_⟩, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, hk₁, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, hx₁₁, he₁]
      · rw [Category.assoc, hx₁₂, ← Category.assoc, he₂, hd₀₁]
    · rw [Category.assoc, hk₂, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, hx₂₁, he₁, hq]
      · rw [Category.assoc, hx₂₂, ← Category.assoc, he₂, hd₀₂]
  · apply pullback.hom_ext
    · rw [Category.assoc, he₁, ← Category.assoc, hk₁, hx₁₁, Category.id_comp]
    · rw [Category.assoc, he₂, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, hd₀₁, ← Category.assoc, hk₁, hx₁₂]
      · rw [Category.assoc, hd₀₂, ← Category.assoc, hk₂, hx₂₂]
  · apply pullback.hom_ext
    · rw [Category.assoc, he₁, ← Category.assoc, hδ₁, Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, he₂, pullback.lift_snd]
      apply pullback.hom_ext
      · rw [Category.assoc, hd₀₁, ← Category.assoc, hδ₁, Category.id_comp, Category.assoc,
          pullback.diagonal_fst f, Category.comp_id]
      · rw [Category.assoc, hd₀₂, ← Category.assoc, pullback.diagonal_snd F, Category.id_comp,
          Category.assoc, pullback.diagonal_snd f, Category.comp_id]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` instance search on presheaves over the big fppf site
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_SeparatedMorphismDiagonalDescent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, found directly. -/
local instance (priority := high) hasPullback_presheaf_SeparatedMorphismDiagonalDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the pullbacks of presheaves over the big fppf site in the statement
/-- **Separatedness of a base change, read on the base change of the diagonal.** If
`F : Z₁ ×_{Z₀} X₀ ⟶ Z₁ ×_{Z₀} Y₀` is the base change of `f : X₀ ⟶ Y₀` along `t : Z₁ ⟶ Z₀`,
then `F` is separated exactly when the base change along `t` of the diagonal of `f` is a closed
immersion. -/
theorem isClosedImmersion_baseChange_diagonal_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X₀ Y₀ Z₀ Z₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : X₀ ⟶ Z₀) (b : Y₀ ⟶ Z₀) (t : Z₁ ⟶ Z₀)
    (f : X₀ ⟶ Y₀) (hfb : f ≫ b = a)
    (F : pullback t a ⟶ pullback t b)
    (hFfst : F ≫ pullback.fst t b = pullback.fst t a)
    (hFsnd : F ≫ pullback.snd t b = pullback.snd t a ≫ f) :
    IsClosedImmersion B S hS
        (pullback.lift (pullback.fst t a) (pullback.snd t a ≫ pullback.diagonal f) (by
          simpa [Category.assoc] using (pullback.condition (f := t) (g := a))) :
            pullback t a ⟶ pullback t (pullback.fst f f ≫ a)) ↔
      IsSeparated B S hS F := by
  obtain ⟨e, he⟩ := exists_iso_diagonal_comp_eq_pullbackLift_diagonal a b t f hfb F hFfst hFsnd
  rw [← he]
  exact MorphismProperty.cancel_right_of_respectsIso _ _ _

/-! ### Stacks 0851 over the chapter's convention -/

namespace MorphismDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

/-- **Situation 084W for the relative diagonal.** The same system of bases and distinguished
stage, with the morphism to be descended replaced by the relative diagonal
`X₀ ⟶ X₀ ×_{Y₀} X₀` of `f₀`. The fibre product is quasi-compact and quasi-separated by
Stacks 073B, part (3). -/
noncomputable def diagonal : MorphismDescentSituation B S hS hZ I where
  base := D.base
  base_isAlgebraicSpace := D.base_isAlgebraicSpace
  transition_affine := D.transition_affine
  limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
  initial := D.initial
  source₀ := D.source₀
  target₀ := pullback D.map₀ D.map₀
  sourceToBase := D.sourceToBase
  targetToBase := pullback.fst D.map₀ D.map₀ ≫ D.sourceToBase
  map₀ := pullback.diagonal D.map₀
  map₀_over := by simp
  source₀_isAlgebraicSpace := D.source₀_isAlgebraicSpace
  target₀_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS D.map₀ D.map₀
    D.source₀_isAlgebraicSpace D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
  base₀_quasiCompact := D.base₀_quasiCompact
  base₀_quasiSeparated := D.base₀_quasiSeparated
  source₀_quasiCompact := D.source₀_quasiCompact
  source₀_quasiSeparated := D.source₀_quasiSeparated
  target₀_quasiCompact := isQuasiCompactSpace_pullback B S hS hZ D.map₀ D.map₀
    D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace D.source₀_quasiCompact
    D.source₀_quasiCompact D.target₀_quasiSeparated
  target₀_quasiSeparated := isAbsolutelyQuasiSeparated_pullback B S hS hZ D.map₀ D.map₀
    D.source₀_isAlgebraicSpace D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
    D.source₀_quasiSeparated D.source₀_quasiSeparated

/-- The system of bases of `D.diagonal` is that of `D`. -/
@[simp] theorem diagonal_base : D.diagonal.base = D.base := rfl

/-- The distinguished stage of `D.diagonal` is that of `D`. -/
@[simp] theorem diagonal_initial : D.diagonal.initial = D.initial := rfl

/-- The morphism of `D.diagonal` at the distinguished stage is the relative diagonal of `f₀`. -/
@[simp] theorem diagonal_map₀ : D.diagonal.map₀ = pullback.diagonal D.map₀ := rfl

/-- At a stage, the base change of the relative diagonal of `f₀` is a closed immersion exactly
when `f_i` is separated. -/
theorem isClosedImmersion_diagonal_mapAt_iff (i : I) (hi : D.initial ≤ i) :
    IsClosedImmersion B S hS (D.diagonal.mapAt i hi) ↔ IsSeparated B S hS (D.mapAt i hi) :=
  isClosedImmersion_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
    (D.baseAtToInitial i hi) D.map₀ D.map₀_over (D.mapAt i hi)
    (D.mapAt_fst i hi) (D.mapAt_snd i hi)

/-- At the limit, the base change of the relative diagonal of `f₀` is a closed immersion exactly
when `f` is separated. -/
theorem isClosedImmersion_diagonal_mapLimit_iff :
    IsClosedImmersion B S hS D.diagonal.mapLimit ↔ IsSeparated B S hS D.mapLimit :=
  isClosedImmersion_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
    (limit.π D.base (op D.initial)) D.map₀ D.map₀_over D.mapLimit
    D.mapLimit_fst D.mapLimit_snd

/-- **Stacks 0851, over the chapter's convention.** In the situation of Stacks 084W, if the base
change `f` of `f₀` to the limit `B` is separated, then the base change `f_i` of `f₀` to some
stage `B_i` is separated.

The proof applies Stacks 0850 to the relative diagonal of `f₀`, which is locally of finite type
(`AlgebraicGeometry.Space.isLocallyOfFiniteType_pullback_diagonal`). The only hypothesis beyond
Situation 084W is the chapter's standing convention of Section 70.2
(tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` of the system of bases;
nothing is asked of the index. -/
theorem exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) (hf : IsSeparated B S hS D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), IsSeparated B S hS (D.mapAt i hi) := by
  obtain ⟨i, hi, h⟩ := D.diagonal.exists_isClosedImmersion_mapAt_of_siteContainsBaseChangeLimits
    hconv (D.isClosedImmersion_diagonal_mapLimit_iff.mpr hf)
    (isLocallyOfFiniteType_pullback_diagonal B S hS D.source₀_isAlgebraicSpace D.map₀)
  exact ⟨i, hi, (D.isClosedImmersion_diagonal_mapAt_iff i hi).mp h⟩

end MorphismDescentSituation

end AlgebraicGeometry.Space

end
