module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineFourierKernel

/-!
# The triple product of affine lines is affine three-space

The coordinates `(x, t, u)` of `Q = 𝔸¹_x ×_k 𝔸¹_t ×_k 𝔸¹_u`
(`Stacks.EtaleCohomology.fourierTripleCoords`) are an isomorphism `Q ≅ Spec k[x, t, u]`: its
inverse is the morphism with the three coordinate projections `Spec k[x, t, u] ⟶ 𝔸¹` as
components. Through it the antidiagonal `x + u = 0` and its complement are the spectra of
`k[x, t]` and of `k[x, t, u]_{x + u}`.

## Main definitions

* `Stacks.EtaleCohomology.affineSpaceCoordinate`: the coordinate projection
  `Spec k[X_i] ⟶ 𝔸¹`, `X ↦ X_i`.
* `Stacks.EtaleCohomology.fourierTripleCoordsInv`: `Spec k[x, t, u] ⟶ Q`.
* `Stacks.EtaleCohomology.fourierTripleCoordsIso`: `Q ≅ Spec k[x, t, u]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Blowup

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The ring map of `Spec β` is `β` followed by the ring map of the identity. -/
theorem specHomRingHom_specMap (β : S →+* R) :
    specHomRingHom (Spec.map (CommRingCat.ofHom β)) =
      (specHomRingHom (𝟙 (Spec (CommRingCat.of R)))).comp β := by
  simpa using specHomRingHom_comp_specMap (𝟙 (Spec (CommRingCat.of R))) β

end Stacks.Blowup

namespace Stacks.EtaleCohomology

open Stacks.Blowup Stacks.ArtinSchreier

variable (k : Type u) [Field k]

local notation "𝔸f" => affineLineStructureMap k

/-- The ring map of `h : Y ⟶ 𝔸¹` on constants is the ring map of `h ≫ (𝔸¹ ⟶ Spec k)`. -/
theorem specHomRingHom_C {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of (Polynomial k))) (a : k) :
    specHomRingHom h (Polynomial.C a) = specHomRingHom (h ≫ 𝔸f) a := by
  rw [specHomRingHom_comp_specMap, RingHom.comp_apply, Polynomial.algebraMap_eq]

/-- **The coordinate projection `Spec k[X_i] ⟶ 𝔸¹`**, `X ↦ X_i`. -/
abbrev affineSpaceCoordinate {σ : Type} (i : σ) :
    Spec (CommRingCat.of (MvPolynomial σ k)) ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ k)).toRingHom)

/-- The coordinate projection `Spec k[X_i] ⟶ 𝔸¹` followed by `𝔸¹ ⟶ Spec k` is the structure
morphism `Spec k[X_i] ⟶ Spec k`. -/
theorem affineSpaceCoordinate_comp_structureMap {σ : Type} (i : σ) :
    affineSpaceCoordinate k i ≫ 𝔸f =
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial σ k))) := by
  rw [← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun a => (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ k)).commutes a

/-- The map `Spec k[x, t] ⟶ 𝔸¹ ×_k 𝔸¹` with components the coordinates `i` and `j`. -/
abbrev affineSpaceCoordinatePair {σ : Type} (i j : σ) :
    Spec (CommRingCat.of (MvPolynomial σ k)) ⟶ pullback 𝔸f 𝔸f :=
  pullback.lift (affineSpaceCoordinate k i) (affineSpaceCoordinate k j)
    (by rw [affineSpaceCoordinate_comp_structureMap, affineSpaceCoordinate_comp_structureMap])

/-- **The inverse of the coordinates of the triple product**, `Spec k[x, t, u] ⟶ Q`, with
components the coordinate projections. -/
def fourierTripleCoordsInv : Spec (CommRingCat.of (MvPolynomial (Fin 3) k)) ⟶
    tripleProduct 𝔸f 𝔸f 𝔸f :=
  pullback.lift (affineSpaceCoordinatePair k 0 1) (affineSpaceCoordinatePair k 1 2)
    (by simp only [pullback.lift_snd, pullback.lift_fst])

/-- The `i`-th coordinate of `fourierTripleCoords` is the `i`-th projection `Q ⟶ 𝔸¹`. -/
theorem fourierTripleCoords_comp_affineSpaceCoordinate (i : Fin 3) :
    fourierTripleCoords k ≫ affineSpaceCoordinate k i =
      ![tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _, tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _,
        tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _] i := by
  refine hom_ext_of_specHomRingHom (Polynomial.ringHom_ext (fun a => ?_) ?_)
  · have hc : ∀ j : Fin 3, ![tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _,
        tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _, tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _]
        j ≫ 𝔸f = (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _) ≫ 𝔸f := fun j => by
      fin_cases j
      · rfl
      · change (_ ≫ pullback.snd _ _) ≫ _ = _
        rw [Category.assoc, Category.assoc, pullback.condition]
      · change (_ ≫ pullback.snd _ _) ≫ _ = _
        rw [← structureRingHom_tripleProduct₂₃, Category.assoc, Category.assoc,
          pullback.condition]
    rw [specHomRingHom_C, specHomRingHom_C, Category.assoc,
      affineSpaceCoordinate_comp_structureMap, specHomRingHom_comp_specMap,
      specHomRingHom_fourierTripleCoords, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
      MvPolynomial.eval₂Hom_C, hc i]
  · rw [specHomRingHom_comp_specMap, specHomRingHom_fourierTripleCoords, RingHom.comp_apply]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X,
      MvPolynomial.eval₂Hom_X']
    fin_cases i <;> rfl

/-- `fourierTripleCoords` followed by `fourierTripleCoordsInv` is the identity of `Q`. -/
theorem fourierTripleCoords_comp_inv :
    fourierTripleCoords k ≫ fourierTripleCoordsInv k = 𝟙 _ := by
  have h := fourierTripleCoords_comp_affineSpaceCoordinate k
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
  all_goals simp only [Category.assoc, Category.id_comp, fourierTripleCoordsInv,
    pullback.lift_fst, pullback.lift_snd]
  · exact h 0
  · exact h 1
  · exact (h 1).trans pullback.condition
  · exact h 2

/-- `fourierTripleCoordsInv` followed by `fourierTripleCoords` is the identity of
`Spec k[x, t, u]`. -/
theorem fourierTripleCoordsInv_comp :
    fourierTripleCoordsInv k ≫ fourierTripleCoords k = 𝟙 _ := by
  refine hom_ext_of_specHomRingHom (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · rw [specHomRingHom_comp_apply, specHomRingHom_fourierTripleCoords, MvPolynomial.eval₂Hom_C,
      ← specHomRingHom_comp_apply]
    have h : fourierTripleCoordsInv k ≫ (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _) ≫ 𝔸f =
        Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 3) k))) := by
      simp only [fourierTripleCoordsInv, Category.assoc, pullback.lift_fst_assoc,
        affineSpaceCoordinate_comp_structureMap]
    rw [h, specHomRingHom_specMap, RingHom.comp_apply, MvPolynomial.algebraMap_eq]
  · rw [specHomRingHom_comp_apply, specHomRingHom_fourierTripleCoords, MvPolynomial.eval₂Hom_X']
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        affineLineCoordinate, ← specHomRingHom_comp_apply, fourierTripleCoordsInv,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.lift_fst, pullback.lift_snd,
        specHomRingHom_specMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.aeval_X]

/-- The coordinates `Q ⟶ Spec k[x, t, u]` of the triple product are an isomorphism. -/
instance isIso_fourierTripleCoords : IsIso (fourierTripleCoords k) :=
  ⟨⟨fourierTripleCoordsInv k, fourierTripleCoords_comp_inv k, fourierTripleCoordsInv_comp k⟩⟩

/-- **The triple product of affine lines is affine three-space**,
`𝔸¹ ×_k 𝔸¹ ×_k 𝔸¹ ≅ Spec k[x, t, u]`, through its coordinates. -/
def fourierTripleCoordsIso :
    tripleProduct 𝔸f 𝔸f 𝔸f ≅ Spec (CommRingCat.of (MvPolynomial (Fin 3) k)) :=
  asIso (fourierTripleCoords k)

end Stacks.EtaleCohomology
