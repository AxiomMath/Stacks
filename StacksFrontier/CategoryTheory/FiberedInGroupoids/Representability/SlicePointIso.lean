module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Lifts
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePoint

/-!
# Two points of a category fibred in groupoids agreeing at the tautological object

Let `𝒞` be a category, let `X` be an object of it, let `a : A ⟶ X` be a morphism and let
`p𝒴 : 𝒴 ⥤ 𝒞/X` be a category fibred in groupoids over the slice at `X`. A *point of `𝒴` with
values in `A`* is a 1-morphism `u : 𝒞/A ⥤ 𝒴` over `CategoryTheory.Over.map a`; this is the form in
which Stacks 02ZW and Stacks 03YK quantify over scheme-valued points, and
`StacksRepresentableCFG.exists_pointOverMap_of_obj` produces one from an object of `𝒴` lying over
`A → X`.

This file is the companion uniqueness statement, the *fullness* half of the 2-Yoneda lemma in the
same shape: two such points whose values at the tautological object `id_A` of `𝒞/A` are
isomorphic by a vertical isomorphism are 2-isomorphic, by a 2-isomorphism all of whose components
are vertical.

The proof does not go through the 2-Yoneda equivalence. The tautological object is terminal in
`𝒞/A`, so every object `W` carries a unique morphism `W ⟶ id_A`, and its images `u₁(W) ⟶ u₁(id_A)`
and `u₂(W) ⟶ u₂(id_A)` are lifts of one and the same morphism of `𝒞/X`. In a category fibred in
groupoids every lift is strongly cartesian, so the two lifts of that morphism whose targets are
identified by the given isomorphism have canonically isomorphic sources, by Stacks 03WP
(`CategoryTheory.Functor.IsFiberedInGroupoids.twoStepLiftIso`); that isomorphism is the component
at `W`. Naturality is the uniqueness half of the same universal property: both composites are
lifts of one morphism factoring through the cartesian lift at `W`, so both are *the* induced
morphism.

## Main results

* `StacksRepresentableCFG.exists_natIso_of_iso_at_id`: **2-Yoneda fullness in the shape Stacks
  02ZW and 03YK consume.** Two points of `𝒴` with values in `A` which agree, vertically, at the
  tautological object of `𝒞/A` are 2-isomorphic over `𝒞/X`.
* `StacksRepresentableCFG.exists_natIso_of_iso_at_id_app_id`: the same, with the component of
  the 2-isomorphism at the tautological object equal to the given isomorphism.

## Implementation notes

The hypothesis is stated with the verticality of the given isomorphism read at
`(CategoryTheory.Over.map a).obj (CategoryTheory.Over.mk (𝟙 A))`, which is the object of `𝒞/X`
that both values lie over by the two hypotheses `u₁ ⋙ p𝒴 = Over.map a`, `u₂ ⋙ p𝒴 = Over.map a`.
That object is `A → (𝟙 A ≫ a) → X`, equal to `A → a → X` only after
`CategoryTheory.Category.id_comp`; a consumer holding the verticality at the latter has to
transport, exactly as in
`StacksRepresentableCFG.forget_obj_iteratedSliceBackward_id`.

## References

* [Stacks Project, Tag 02Y4](https://stacks.math.columbia.edu/tag/02Y4)
* [Stacks Project, Tag 03WP](https://stacks.math.columbia.edu/tag/03WP)
* [Stacks Project, Tag 04SS](https://stacks.math.columbia.edu/tag/04SS)
-/

@[expose] public section

open CategoryTheory

namespace StacksRepresentableCFG

universe v₁ v₃ u₁ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X A : 𝒞} (a : A ⟶ X)
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {p𝒴 : 𝒴 ⥤ Over X}

/-- The unique morphism from an object of `𝒞/A` to the tautological object `id_A`, which is
terminal. -/
noncomputable def toTautological (W : Over A) : W ⟶ Over.mk (𝟙 A) :=
  Limits.IsTerminal.from Over.mkIdTerminal W

/-- The underlying morphism of `StacksRepresentableCFG.toTautological` is the structure
morphism. -/
@[simp] theorem toTautological_left (W : Over A) : (toTautological W).left = W.hom := by
  have h := Over.w (toTautological W)
  simpa using h

/-- The morphisms to the tautological object are compatible with every morphism of `𝒞/A`, the
tautological object being terminal. -/
theorem comp_toTautological {W' W : Over A} (h : W' ⟶ W) :
    h ≫ toTautological W = toTautological W' :=
  Limits.IsTerminal.hom_ext Over.mkIdTerminal _ _

variable (u₁ u₂ : Over A ⥤ 𝒴) (h₁ : u₁ ⋙ p𝒴 = Over.map a) (h₂ : u₂ ⋙ p𝒴 = Over.map a)

include h₁ in
/-- A point of `𝒴` with values in `A` carries the morphism to the tautological object to a lift
of its image in `𝒞/X`. -/
theorem isHomLift_map_toTautological (W : Over A) :
    p𝒴.IsHomLift ((Over.map a).map (toTautological W)) (u₁.map (toTautological W)) :=
  Functor.isHomLift_map_of_comp_eq h₁ ((Over.map a).map (toTautological W)) (toTautological W)

section

variable (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (θ : u₁.obj (Over.mk (𝟙 A)) ≅ u₂.obj (Over.mk (𝟙 A)))
  (hθ : p𝒴.IsHomLift (𝟙 ((Over.map a).obj (Over.mk (𝟙 A)))) θ.hom)

include h₂ in
/-- The image under the second point of the morphism to the tautological object, read as a lift of
a composite with an identity — the shape Stacks 03WP asks for. -/
private theorem isHomLift_comp_id_map_toTautological (W : Over A) :
    p𝒴.IsHomLift ((Over.map a).map (toTautological W) ≫
        𝟙 ((Over.map a).obj (Over.mk (𝟙 A)))) (u₂.map (toTautological W)) := by
  rw [Category.comp_id]
  exact isHomLift_map_toTautological a u₂ h₂ W

include h₁ hθ in
/-- Composing the first point's morphism to the tautological object with the given isomorphism
gives a second lift of the same morphism of `𝒞/X`, with the same target as the second point's. -/
private theorem isHomLift_map_toTautological_comp (W : Over A) :
    p𝒴.IsHomLift ((Over.map a).map (toTautological W))
      (u₁.map (toTautological W) ≫ θ.hom) := by
  have _ := isHomLift_map_toTautological a u₁ h₁ W
  have _ := hθ
  have hc := IsHomLift.comp p𝒴 ((Over.map a).map (toTautological W))
    (𝟙 ((Over.map a).obj (Over.mk (𝟙 A)))) (u₁.map (toTautological W)) θ.hom
  rwa [Category.comp_id] at hc

include h𝒴 h₁ h₂ hθ in
/-- The comparison isomorphism at `W`: the canonical isomorphism of Stacks 03WP between the
sources of the two strongly cartesian lifts `u₁(W) ⟶ u₁(id_A) ≅ u₂(id_A)` and
`u₂(W) ⟶ u₂(id_A)` of one morphism of `𝒞/X`. -/
private noncomputable def pointIso (W : Over A) : u₁.obj W ≅ u₂.obj W :=
  have _ := isHomLift_map_toTautological a u₁ h₁ W
  have _ := hθ
  have _ := isHomLift_comp_id_map_toTautological a u₂ h₂ W
  h𝒴.twoStepLiftIso ((Over.map a).map (toTautological W))
    (𝟙 ((Over.map a).obj (Over.mk (𝟙 A)))) θ.hom (u₁.map (toTautological W))
    (u₂.map (toTautological W))

include h𝒴 h₁ h₂ hθ in
/-- The comparison isomorphism is vertical. -/
private theorem pointIso_isHomLift (W : Over A) :
    p𝒴.IsHomLift (𝟙 ((Over.map a).obj W)) (pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W).hom := by
  have _ := isHomLift_map_toTautological a u₁ h₁ W
  have _ := hθ
  have _ := isHomLift_comp_id_map_toTautological a u₂ h₂ W
  exact h𝒴.isHomLift_twoStepLiftIso_hom ((Over.map a).map (toTautological W))
    (𝟙 ((Over.map a).obj (Over.mk (𝟙 A)))) θ.hom (u₁.map (toTautological W))
    (u₂.map (toTautological W))

include h𝒴 h₁ h₂ hθ in
/-- The comparison isomorphism fills the diagram of Stacks 03WP. -/
private theorem pointIso_fac (W : Over A) :
    (pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W).hom ≫ u₂.map (toTautological W)
      = u₁.map (toTautological W) ≫ θ.hom := by
  have _ := isHomLift_map_toTautological a u₁ h₁ W
  have _ := hθ
  have _ := isHomLift_comp_id_map_toTautological a u₂ h₂ W
  exact h𝒴.twoStepLiftIso_hom_comp ((Over.map a).map (toTautological W))
    (𝟙 ((Over.map a).obj (Over.mk (𝟙 A)))) θ.hom (u₁.map (toTautological W))
    (u₂.map (toTautological W))

include h𝒴 h₁ h₂ hθ in
/-- The comparison isomorphisms are natural: both composites are lifts of one morphism of `𝒞/X`
factoring through the strongly cartesian lift at `W`, hence both are the morphism that lift
induces. -/
private theorem pointIso_naturality {W' W : Over A} (h : W' ⟶ W) :
    u₁.map h ≫ (pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W).hom
      = (pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W').hom ≫ u₂.map h := by
  have _ := isHomLift_map_toTautological a u₂ h₂ W
  have _ : p𝒴.IsStronglyCartesian ((Over.map a).map (toTautological W))
      (u₂.map (toTautological W)) := h𝒴.isStronglyCartesian_homLift _ _
  have hf' : (Over.map a).map (toTautological W')
      = (Over.map a).map h ≫ (Over.map a).map (toTautological W) := by
    rw [← Functor.map_comp, comp_toTautological]
  have _ := isHomLift_map_toTautological_comp a u₁ u₂ h₁ θ hθ W'
  have _ : p𝒴.IsHomLift ((Over.map a).map h) (u₁.map h) :=
    Functor.isHomLift_map_of_comp_eq h₁ ((Over.map a).map h) h
  have _ : p𝒴.IsHomLift ((Over.map a).map h) (u₂.map h) :=
    Functor.isHomLift_map_of_comp_eq h₂ ((Over.map a).map h) h
  have _ := pointIso_isHomLift a u₁ u₂ h₁ h₂ h𝒴 θ hθ W
  have _ := pointIso_isHomLift a u₁ u₂ h₁ h₂ h𝒴 θ hθ W'
  have _ : p𝒴.IsHomLift ((Over.map a).map h)
      (u₁.map h ≫ (pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W).hom) := by
    have hc := IsHomLift.comp p𝒴 ((Over.map a).map h) (𝟙 ((Over.map a).obj W))
      (u₁.map h) (pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W).hom
    rwa [Category.comp_id] at hc
  have _ : p𝒴.IsHomLift ((Over.map a).map h)
      ((pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W').hom ≫ u₂.map h) := by
    have hc := IsHomLift.comp p𝒴 (𝟙 ((Over.map a).obj W')) ((Over.map a).map h)
      (pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W').hom (u₂.map h)
    rwa [Category.id_comp] at hc
  have hLfac : (u₁.map h ≫ (pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W).hom) ≫
      u₂.map (toTautological W) = u₁.map (toTautological W') ≫ θ.hom := by
    rw [Category.assoc, pointIso_fac, ← Category.assoc, ← u₁.map_comp, comp_toTautological]
  have hRfac : ((pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W').hom ≫ u₂.map h) ≫
      u₂.map (toTautological W) = u₁.map (toTautological W') ≫ θ.hom := by
    rw [Category.assoc, ← u₂.map_comp, comp_toTautological, pointIso_fac]
  rw [Functor.IsStronglyCartesian.map_uniq p𝒴 _ _ hf' _ _ hLfac,
    Functor.IsStronglyCartesian.map_uniq p𝒴 _ _ hf' _ _ hRfac]

include h𝒴 h₁ h₂ hθ in
/-- **2-Yoneda fullness in the shape Stacks 02ZW and 03YK consume.** Two points of a category
fibred in groupoids with values in `A` whose values at the tautological object of `𝒞/A` are
identified by a vertical isomorphism are 2-isomorphic, by a 2-isomorphism all of whose components
are vertical. -/
theorem exists_natIso_of_iso_at_id :
    ∃ α : u₁ ≅ u₂, ∀ W : Over A, p𝒴.IsHomLift (𝟙 ((Over.map a).obj W)) (α.hom.app W) :=
  ⟨NatIso.ofComponents (fun W => pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W)
    (fun {_ _} h => pointIso_naturality a u₁ u₂ h₁ h₂ h𝒴 θ hθ h),
   fun W => pointIso_isHomLift a u₁ u₂ h₁ h₂ h𝒴 θ hθ W⟩

include h𝒴 h₁ h₂ hθ in
/-- **2-Yoneda fullness with the comparison at the tautological object prescribed.** The
2-isomorphism of `StacksRepresentableCFG.exists_natIso_of_iso_at_id` can be chosen so that its
component at the tautological object of `𝒞/A` is the given isomorphism `θ`. -/
theorem exists_natIso_of_iso_at_id_app_id :
    ∃ α : u₁ ≅ u₂, (∀ W : Over A, p𝒴.IsHomLift (𝟙 ((Over.map a).obj W)) (α.hom.app W)) ∧
      α.hom.app (Over.mk (𝟙 A)) = θ.hom := by
  refine ⟨NatIso.ofComponents (fun W => pointIso a u₁ u₂ h₁ h₂ h𝒴 θ hθ W)
    (fun {_ _} h => pointIso_naturality a u₁ u₂ h₁ h₂ h𝒴 θ hθ h),
    fun W => pointIso_isHomLift a u₁ u₂ h₁ h₂ h𝒴 θ hθ W, ?_⟩
  have h := pointIso_fac a u₁ u₂ h₁ h₂ h𝒴 θ hθ (Over.mk (𝟙 A))
  have ht : toTautological (Over.mk (𝟙 A)) = 𝟙 _ :=
    Limits.IsTerminal.hom_ext Over.mkIdTerminal _ _
  rw [ht, u₁.map_id, u₂.map_id, Category.comp_id, Category.id_comp] at h
  exact h

end

end StacksRepresentableCFG

end
