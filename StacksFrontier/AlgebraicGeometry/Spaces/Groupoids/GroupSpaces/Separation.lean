module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Separation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# Separation properties of a group algebraic space

Let `G` be a group algebraic space over an algebraic space `B`. The structure morphism
`G ⟶ B` is separated, quasi-separated, locally separated exactly when the identity section
`e : B ⟶ G` is a closed immersion, quasi-compact, an immersion. All three statements come
from the same pair of cartesian squares: a section of a morphism is a base change of its
relative diagonal, and for a group object the relative diagonal is a base change of the
identity section along `(g, g') ↦ g⁻¹ g'`.

## Main results

* `AlgebraicGeometry.Space.isSeparated_iff_identity_isClosedImmersion`: **Stacks 06P6**, the
  separated case.
* `AlgebraicGeometry.Space.isQuasiSeparated_iff_identity_isQuasiCompact`: **Stacks 06P6**, the
  quasi-separated case.
* `AlgebraicGeometry.Space.isLocallySeparated_iff_identity_isImmersion`: **Stacks 06P6**, the
  locally separated case.
* `CategoryTheory.Limits.isPullback_section_diagonal`: a section of a morphism in a category
  with pullbacks is a base change of its relative diagonal.
* `AlgebraicGeometry.Space.isPullback_diagonal_identity`: for a group object of a slice of
  presheaves, the relative diagonal of the structure morphism is a base change of the identity
  section along `(g, g') ↦ g⁻¹ g'`.

## Implementation notes

A group algebraic space over `B` is a group object of the slice `CategoryTheory.Over B` of
presheaves on the big fppf site whose underlying presheaf is an algebraic space, so its
identity section is the underlying morphism of presheaves of the unit `η[G]` and its fibre
square `G ×_B G` is the monoidal product of the slice. The second cartesian square is
therefore `CategoryTheory.GrpObj.diagonal_isPullback_inv_mul`, pushed forward along
`CategoryTheory.Over.forget`, which preserves connected limits; that lemma is stated for a
group object in an arbitrary cartesian monoidal category, and is reused from
`StacksFrontier/AlgebraicGeometry/GroupScheme/Subgroups/Separation.lean`, where the same two
squares give the scheme-level statements of **Stacks 047G**.

Being a closed immersion and being an immersion are, by **Stacks 02YU**, the relative
properties attached to the corresponding properties of morphisms of schemes, and
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange` makes any relative
property stable under base change. That is used here directly, at the level of presheaves,
rather than through the cartesian-square form of **Stacks 02YW** in
`StacksFrontier/AlgebraicGeometry/Spaces/ImmersionBaseChange.lean`: the latter is stated in the
full subcategory of algebraic spaces, so using it would mean transporting both squares into
that subcategory and carrying algebraicity hypotheses which the base-change argument does not
use. Quasi-compactness is not a relative property and its base-change statement is **Stacks
03HF**, `AlgebraicGeometry.Space.isQuasiCompact_of_isPullback`, which is already phrased for a
cartesian square of presheaves.

## References

* [Stacks Project, Tag 06P6](https://stacks.math.columbia.edu/tag/06P6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

namespace CategoryTheory.Limits

/-- A section `s` of `f : X ⟶ Y` is a base change of the relative diagonal of `f`: the square
with both upper legs `s`, the relative diagonal on the right and `(f ≫ s, 𝟙 X)` along the
bottom is cartesian. -/
theorem isPullback_section_diagonal {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    IsPullback s s (pullback.diagonal f)
      (pullback.lift (f ≫ s) (𝟙 X) (by simp [Category.assoc, hs])) := by
  let q : X ⟶ pullback f f := pullback.lift (f ≫ s) (𝟙 X) (by simp [Category.assoc, hs])
  have hqfst : q ≫ pullback.fst f f = f ≫ s := pullback.lift_fst _ _ _
  have hqsnd : q ≫ pullback.snd f f = 𝟙 X := pullback.lift_snd _ _ _
  have hcomm : s ≫ pullback.diagonal f = s ≫ q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, hqfst]
      rw [← Category.assoc, hs]
      simp
    · simp only [Category.assoc, pullback.diagonal_snd, hqsnd]
  have hfst (t : PullbackCone (pullback.diagonal f) q) : t.fst = t.snd ≫ f ≫ s := by
    have hc := congrArg (fun k ↦ k ≫ pullback.fst f f) t.condition
    simpa [Category.assoc, pullback.diagonal_fst, hqfst] using hc
  refine { w := hcomm, isLimit' := ⟨?_⟩ }
  refine PullbackCone.IsLimit.mk hcomm (lift := fun t ↦ t.snd ≫ f) ?_ ?_ ?_
  · intro t
    exact (Category.assoc _ _ _).trans (hfst t).symm
  · intro t
    have hsnd : t.fst = t.snd := by
      have hc := congrArg (fun k ↦ k ≫ pullback.snd f f) t.condition
      simpa [Category.assoc, pullback.diagonal_snd, hqsnd] using hc
    exact (Category.assoc _ _ _).trans ((hfst t).symm.trans hsnd)
  · intro t m _ hm
    calc
      m = m ≫ s ≫ f := by rw [hs]; simp
      _ = (m ≫ s) ≫ f := (Category.assoc _ _ _).symm
      _ = t.snd ≫ f := by rw [hm]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

/-! ### The identity section and the relative diagonal -/

/-- For a group object of the slice of presheaves over `B`, the relative diagonal of its
structure morphism is a base change of its identity section along `(g, g') ↦ g⁻¹ g'`. -/
theorem isPullback_diagonal_identity
    {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (G : Over B) [GrpObj G] :
    IsPullback (pullback.diagonal G.hom) (toUnit G).left
      (lift (fst G G ≫ ι[G]) (snd G G) ≫ μ[G]).left (η[G]).left := by
  have hd : (lift (𝟙 G) (𝟙 G)).left = pullback.diagonal G.hom := by
    apply pullback.hom_ext <;>
      simp only [Over.lift_left, pullback.lift_fst, pullback.lift_snd,
        pullback.diagonal_fst, pullback.diagonal_snd, Over.id_left]
  have hp := (CategoryTheory.GrpObj.diagonal_isPullback_inv_mul G).map (Over.forget B)
  simpa [hd] using hp

/-! ### The three separation criteria -/

variable {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsAlgebraicSpace 𝒞 S hS B)

/-- The identity section of a group object of the slice over `B` is a section of the structure
morphism. -/
private theorem identity_comp_hom (G : Over B) [GrpObj G] :
    (η[G]).left ≫ G.hom = 𝟙 B := by
  simp

/-- A relative property of morphisms of presheaves holds for the relative diagonal of the
structure morphism of a group object of the slice over `B` exactly when it holds for the
identity section. -/
private theorem presheaf_diagonal_iff_identity (P : MorphismProperty Scheme.{u})
    (G : Over B) [GrpObj G] :
    MorphismProperty.presheaf
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme 𝒞 S hS)) (pullback.diagonal G.hom) ↔
    MorphismProperty.presheaf
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme 𝒞 S hS)) (η[G]).left :=
  ⟨fun h ↦ (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (isPullback_section_diagonal G.hom (η[G]).left (identity_comp_hom 𝒞 S hS G)) h,
    fun he ↦ (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (isPullback_diagonal_identity 𝒞 S hS G).flip he⟩

/-- **Stacks 06P6.** A group algebraic space is separated over its base exactly when its
identity section is a closed immersion. -/
@[stacks 06P6 "separatedness", sga "3 VIB 5.1"]
theorem isSeparated_iff_identity_isClosedImmersion (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    IsSeparated 𝒞 S hS G.obj.X.hom ↔
      IsClosedImmersion 𝒞 S hS (η[G.obj.X]).left :=
  presheaf_diagonal_iff_identity 𝒞 S hS _ G.obj.X

/-- **Stacks 06P6.** A group algebraic space is locally separated over its base exactly when
its identity section is an immersion. -/
@[stacks 06P6 "local separatedness"]
theorem isLocallySeparated_iff_identity_isImmersion (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    IsLocallySeparated 𝒞 S hS G.obj.X.hom ↔
      IsImmersion 𝒞 S hS (η[G.obj.X]).left :=
  presheaf_diagonal_iff_identity 𝒞 S hS _ G.obj.X

/-- **Stacks 06P6.** A group algebraic space is quasi-separated over its base exactly when its
identity section is quasi-compact. -/
@[stacks 06P6 "quasi-separatedness"]
theorem isQuasiSeparated_iff_identity_isQuasiCompact (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    IsQuasiSeparated 𝒞 S hS G.obj.X.hom ↔
      IsQuasiCompact 𝒞 S hS (η[G.obj.X]).left :=
  ⟨fun h ↦ isQuasiCompact_of_isPullback 𝒞 S hS
      (isPullback_section_diagonal G.obj.X.hom (η[G.obj.X]).left
        (identity_comp_hom 𝒞 S hS G.obj.X)) h,
    fun he ↦ isQuasiCompact_of_isPullback 𝒞 S hS
      (isPullback_diagonal_identity 𝒞 S hS G.obj.X).flip he⟩

end AlgebraicGeometry.Space

end
