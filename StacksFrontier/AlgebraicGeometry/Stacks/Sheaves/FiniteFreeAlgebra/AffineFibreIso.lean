module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.RelativeCover

/-!
# Isomorphisms of covers over an affine base

Let `W` be an affine scheme and let `m` and `n` be free `d`-dimensional algebra structures on
`Γ(W, 𝒪_W)`. The canonical morphism `W ⟶ Spec Γ(W, 𝒪_W)` is then an isomorphism, so the
projection of `AlgebraicGeometry.FiniteFreeAlgebra.cover` to the spectrum of the algebra of its
structure is an isomorphism too, and conjugation by those projections identifies the morphisms of
covers over `W` with the morphisms of spectra over `Spec Γ(W, 𝒪_W)`. Composing with
`AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivSpecIso` identifies the isomorphisms of
structures with the isomorphisms of covers, and the identification sends an isomorphism of
structures to the morphism of covers that the 1-morphism `Spec` attaches to it. In particular
`Spec` is bijective on the isomorphisms of a fibre over an affine object.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.coverHomOfSpecHom` and
  `AlgebraicGeometry.FiniteFreeAlgebra.specHomOfCoverHom`: the two directions of the conjugation.
* `AlgebraicGeometry.FiniteFreeAlgebra.coverIsoEquivSpecIso`: over an affine base, the
  isomorphisms of covers are the isomorphisms of the spectra of the algebras.
* `AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivCoverIso`: over an affine base, the
  isomorphisms of free `d`-dimensional structures on the global sections are the isomorphisms of
  the covers they attach.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivCoverIso_hom_left`: the identification
  agrees with the value of the 1-morphism `Spec` on morphisms of the fibre, namely with
  `AlgebraicGeometry.FiniteFreeAlgebra.coverMap` of the identity of the base.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

attribute [local implicit_reducible] FiniteFreeAlgebra.map

variable {d : ℕ} [NeZero d]

/-- **Over an affine base the projection of the cover to the spectrum of the algebra of its
structure is an isomorphism.** -/
instance isIso_coverProj (W : Scheme.{u}) [IsAffine W] (m : FiniteFreeAlgebra ↑Γ(W, ⊤) d) :
    IsIso (coverProj W m) :=
  (isPullback_cover W m).isIso_fst_of_isIso

variable (W : Scheme.{u}) [IsAffine W] {m n p : FiniteFreeAlgebra ↑Γ(W, ⊤) d}

/-- Conjugating by the projections to the spectra carries a morphism of spectra over
`Spec Γ(W, 𝒪_W)` to a morphism of covers over `W`. -/
noncomputable def coverHomOfSpecHom (φ : specCover m ⟶ specCover n) : cover W m ⟶ cover W n :=
  Over.homMk (coverProj W m ≫ φ.left ≫ inv (coverProj W n)) (by
    rw [← cancel_mono W.toSpecΓ, Category.assoc, ← (isPullback_cover W n).w, Category.assoc,
      Category.assoc, IsIso.inv_hom_id_assoc, Over.w φ, (isPullback_cover W m).w])

/-- The underlying morphism of `coverHomOfSpecHom W φ` is the conjugate of `φ.left` by the
projections to the spectra. -/
@[simp]
theorem coverHomOfSpecHom_left (φ : specCover m ⟶ specCover n) :
    (coverHomOfSpecHom W φ).left = coverProj W m ≫ φ.left ≫ inv (coverProj W n) := rfl

/-- Conjugating by the projections to the spectra carries a morphism of covers over `W` to a
morphism of spectra over `Spec Γ(W, 𝒪_W)`. -/
noncomputable def specHomOfCoverHom (ψ : cover W m ⟶ cover W n) : specCover m ⟶ specCover n :=
  Over.homMk (inv (coverProj W m) ≫ ψ.left ≫ coverProj W n) (by
    rw [Category.assoc, Category.assoc, (isPullback_cover W n).w, ← Category.assoc ψ.left,
      Over.w ψ, ← (isPullback_cover W m).w, IsIso.inv_hom_id_assoc])

/-- The underlying morphism of `specHomOfCoverHom W ψ` is the conjugate of `ψ.left` by the
projections to the spectra. -/
@[simp]
theorem specHomOfCoverHom_left (ψ : cover W m ⟶ cover W n) :
    (specHomOfCoverHom W ψ).left = inv (coverProj W m) ≫ ψ.left ≫ coverProj W n := rfl

/-- `coverHomOfSpecHom` sends the identity of `specCover m` to the identity of `cover W m`. -/
theorem coverHomOfSpecHom_id : coverHomOfSpecHom W (𝟙 (specCover m)) = 𝟙 (cover W m) := by
  refine Over.OverMorphism.ext ?_
  rw [coverHomOfSpecHom_left, Over.id_left, Over.id_left, Category.id_comp, IsIso.hom_inv_id]

/-- `specHomOfCoverHom` sends the identity of `cover W m` to the identity of `specCover m`. -/
theorem specHomOfCoverHom_id : specHomOfCoverHom W (𝟙 (cover W m)) = 𝟙 (specCover m) := by
  refine Over.OverMorphism.ext ?_
  rw [specHomOfCoverHom_left, Over.id_left, Over.id_left, Category.id_comp, IsIso.inv_hom_id]

/-- `coverHomOfSpecHom` is compatible with composition. -/
theorem coverHomOfSpecHom_comp (φ : specCover m ⟶ specCover n) (φ' : specCover n ⟶ specCover p) :
    coverHomOfSpecHom W (φ ≫ φ') = coverHomOfSpecHom W φ ≫ coverHomOfSpecHom W φ' := by
  refine Over.OverMorphism.ext ?_
  simp only [Over.comp_left, coverHomOfSpecHom_left, Category.assoc, IsIso.inv_hom_id_assoc]

/-- `specHomOfCoverHom` is compatible with composition. -/
theorem specHomOfCoverHom_comp (ψ : cover W m ⟶ cover W n) (ψ' : cover W n ⟶ cover W p) :
    specHomOfCoverHom W (ψ ≫ ψ') = specHomOfCoverHom W ψ ≫ specHomOfCoverHom W ψ' := by
  refine Over.OverMorphism.ext ?_
  simp only [Over.comp_left, specHomOfCoverHom_left, Category.assoc, IsIso.hom_inv_id_assoc]

/-- `specHomOfCoverHom` is a left inverse of `coverHomOfSpecHom`. -/
theorem specHomOfCoverHom_coverHomOfSpecHom (φ : specCover m ⟶ specCover n) :
    specHomOfCoverHom W (coverHomOfSpecHom W φ) = φ := by
  refine Over.OverMorphism.ext ?_
  simp only [specHomOfCoverHom_left, coverHomOfSpecHom_left, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id, IsIso.inv_hom_id_assoc]

/-- `specHomOfCoverHom` is a right inverse of `coverHomOfSpecHom`. -/
theorem coverHomOfSpecHom_specHomOfCoverHom (ψ : cover W m ⟶ cover W n) :
    coverHomOfSpecHom W (specHomOfCoverHom W ψ) = ψ := by
  refine Over.OverMorphism.ext ?_
  simp only [coverHomOfSpecHom_left, specHomOfCoverHom_left, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id, IsIso.hom_inv_id_assoc]

/-- **Over an affine base, the isomorphisms of covers are the isomorphisms of the spectra of the
algebras of their structures.** -/
noncomputable def coverIsoEquivSpecIso (m n : FiniteFreeAlgebra ↑Γ(W, ⊤) d) :
    (specCover m ≅ specCover n) ≃ (cover W m ≅ cover W n) where
  toFun ε :=
    { hom := coverHomOfSpecHom W ε.hom
      inv := coverHomOfSpecHom W ε.inv
      hom_inv_id := by rw [← coverHomOfSpecHom_comp, ε.hom_inv_id, coverHomOfSpecHom_id]
      inv_hom_id := by rw [← coverHomOfSpecHom_comp, ε.inv_hom_id, coverHomOfSpecHom_id] }
  invFun ε :=
    { hom := specHomOfCoverHom W ε.hom
      inv := specHomOfCoverHom W ε.inv
      hom_inv_id := by rw [← specHomOfCoverHom_comp, ε.hom_inv_id, specHomOfCoverHom_id]
      inv_hom_id := by rw [← specHomOfCoverHom_comp, ε.inv_hom_id, specHomOfCoverHom_id] }
  left_inv ε := Iso.ext (specHomOfCoverHom_coverHomOfSpecHom W ε.hom)
  right_inv ε := Iso.ext (coverHomOfSpecHom_specHomOfCoverHom W ε.hom)

/-- **Over an affine base, the isomorphisms of free `d`-dimensional structures on the global
sections are the isomorphisms of the covers they attach.** -/
noncomputable def structureIsoEquivCoverIso (m n : FiniteFreeAlgebra ↑Γ(W, ⊤) d) :
    StructureIso m n ≃ (cover W m ≅ cover W n) :=
  (structureIsoEquivSpecIso m n).trans (coverIsoEquivSpecIso W m n)

/-- Extending the scalars along the identity does not move the canonical morphism to the spectrum
of the global sections. -/
theorem toSpecΓ_id_naturality (T : Scheme.{u}) :
    T.toSpecΓ ≫ Spec.map (ofHom (RingHom.id ↑Γ(T, ⊤))) = 𝟙 T ≫ T.toSpecΓ := by
  rw [ofHom_id, Spec.map_id]
  exact (Category.comp_id T.toSpecΓ).trans (Category.id_comp T.toSpecΓ).symm

/-- **The identification of isomorphisms over an affine base is the 1-morphism `Spec`.** The
identification of isomorphisms of structures with isomorphisms of covers sends an isomorphism of
structures to the morphism of covers that `Spec` attaches to it over the identity of the base. -/
theorem structureIsoEquivCoverIso_hom_left (m n : FiniteFreeAlgebra ↑Γ(W, ⊤) d)
    (e : StructureIso m n) :
    (structureIsoEquivCoverIso W m n e).hom.left =
      coverMap (𝟙 W) (toSpecΓ_id_naturality W) e := by
  have hmap : specMapOf (T := W) (U := W) (ψ := RingHom.id ↑Γ(W, ⊤)) (m := m) (n := n) e =
      (specCoverIso e).hom.left := by
    rw [specMapOf_eq,
      show (Carrier.mapRingHom (RingHom.id ↑Γ(W, ⊤)) n) = RingHom.id (Carrier n) from rfl,
      ofHom_id, Spec.map_id]
    exact Category.comp_id _
  refine (isPullback_cover W n).hom_ext ?_ ?_
  · rw [coverMap_proj, hmap]
    change (coverHomOfSpecHom W ((structureIsoEquivSpecIso m n) e).hom).left ≫ coverProj W n = _
    rw [coverHomOfSpecHom_left, Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, specCoverIso_eq_structureIsoEquivSpecIso]
  · rw [coverMap_hom, Category.comp_id]
    exact Over.w (structureIsoEquivCoverIso W m n e).hom

end AlgebraicGeometry.FiniteFreeAlgebra

end
