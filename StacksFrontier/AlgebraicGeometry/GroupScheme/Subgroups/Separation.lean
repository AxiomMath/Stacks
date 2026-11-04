module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# Separatedness of a group scheme and its identity section

A group scheme over a base is separated exactly when its identity section is a closed immersion,
and quasi-separated exactly when its identity section is quasi-compact. Both characterizations come
from one diagram: for a group object, the square whose top map is the diagonal and whose right map
sends `(g, g')` to `g⁻¹ * g'` is a pullback of the identity section.

A group scheme with structure morphism `f : G ⟶ S` is a group-object structure on `Over.mk f` in
the cartesian monoidal category of schemes over `S`, whose tensor product is the fibre product over
`S`; its identity section is `(η[Over.mk f]).left`.

## Main results

* `CategoryTheory.GrpObj.diagonal_isPullback_inv_mul` exhibits the diagonal of a group object as a
  base change of its identity section.
* `AlgebraicGeometry.isSeparated_iff_isClosedImmersion_one` characterizes separated group schemes
  by their identity sections.
* `AlgebraicGeometry.quasiSeparated_iff_quasiCompact_one` characterizes quasi-separated group
  schemes by quasi-compactness of their identity sections.

## References

* [Stacks Project, Tag 047G](https://stacks.math.columbia.edu/tag/047G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

namespace CategoryTheory.GrpObj

/-- If `f : X ⟶ G ⊗ G` composed with `(g, g') ↦ g⁻¹ * g'` is trivial, then its two components
agree. -/
private lemma fst_eq_snd_of_inv_mul_eq_one
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) [GrpObj G] {X : C} (f : X ⟶ G ⊗ G) (g : X ⟶ 𝟙_ C)
    (h : f ≫ (lift (fst G G ≫ ι[G]) (snd G G) ≫ μ[G]) = g ≫ η[G]) :
    f ≫ fst G G = f ≫ snd G G := by
  rw [← Category.assoc, comp_lift] at h
  exact inv_mul_eq_one.mp (by simpa [Hom.inv_def, Hom.mul_def, one_eq_one] using h)

/-- For a group object, the square whose top map is the diagonal and whose right map sends
`(g, g')` to `g⁻¹ * g'` is a pullback of the identity section. -/
@[sga "3 VIB 5.1" "more general", sga "3 VIIA 2.4.1" "more general"]
theorem diagonal_isPullback_inv_mul
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) [GrpObj G] :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G)
      (lift (fst G G ≫ ι[G]) (snd G G) ≫ μ[G]) η[G] := by
  have comm : lift (𝟙 G) (𝟙 G) ≫
      (lift (fst G G ≫ ι[G]) (snd G G) ≫ μ[G]) = toUnit G ≫ η[G] := by
    simp [← Category.assoc, comp_lift, one_eq_one]
  refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm (fun s ↦ s.fst ≫ fst G G) ?_ ?_ ?_⟩⟩
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc, lift_snd, Category.comp_id]
      exact fst_eq_snd_of_inv_mul_eq_one G s.fst s.snd s.condition
  · exact fun s ↦ Subsingleton.elim _ _
  · intro s m h₁ h₂
    simpa using congr($h₁ ≫ fst G G)

end CategoryTheory.GrpObj

namespace AlgebraicGeometry

/-- The identity section of a group scheme is a section of its structure morphism. -/
private lemma one_left_comp_eq_id {S G : Scheme.{u}} (f : G ⟶ S) [GrpObj (Over.mk f)] :
    (η[Over.mk f]).left ≫ f = 𝟙 S := by
  simpa using Over.w (η[Over.mk f])

/-- A group scheme is separated over its base if and only if its identity section is a closed
immersion. -/
@[stacks 047G "separated_iff_identity_closed", sga "3 VIB 5.1"]
theorem isSeparated_iff_isClosedImmersion_one {S G : Scheme.{u}} (f : G ⟶ S)
    [GrpObj (Over.mk f)] :
    IsSeparated f ↔ IsClosedImmersion (η[Over.mk f]).left := by
  refine ⟨fun hf => ?_, fun he => ?_⟩
  · exact @IsClosedImmersion.of_comp S G S _ f ((one_left_comp_eq_id f).symm ▸ inferInstance) hf
  · rw [isSeparated_iff]
    exact MorphismProperty.of_isPullback
      ((CategoryTheory.GrpObj.diagonal_isPullback_inv_mul
        (Over.mk f)).map (Over.forget S)).flip he

/-- A group scheme is quasi-separated over its base if and only if its identity section is
quasi-compact. -/
@[stacks 047G "quasi_separated_iff_identity_quasi_compact"]
theorem quasiSeparated_iff_quasiCompact_one {S G : Scheme.{u}} (f : G ⟶ S)
    [GrpObj (Over.mk f)] :
    QuasiSeparated f ↔ QuasiCompact η[Over.mk f].left := by
  refine ⟨fun h => ?_, fun he => ?_⟩
  · have : QuasiCompact (η[Over.mk f].left ≫ f) := by
      rw [one_left_comp_eq_id f]
      exact ⟨fun U hU hUc => by simpa using hUc⟩
    exact QuasiCompact.of_comp _ f
  · exact ⟨MorphismProperty.of_isPullback
      ((CategoryTheory.GrpObj.diagonal_isPullback_inv_mul
        (Over.mk f)).map (Over.forget S)).flip he⟩

end AlgebraicGeometry
