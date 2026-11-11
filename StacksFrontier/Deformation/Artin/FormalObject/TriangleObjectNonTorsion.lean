module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.GenericPointNonTorsion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ProjectiveLineOpenConstant
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
public import StacksFrontier.Deformation.Artin.FormalObject.TriangleCechObject

/-!
# The glueing cocycle on the triangle has infinite order

Let `A` be an abelian variety over a field `k`, let `K/k` be a field extension and let `η` be a
`K`-point of `A`. On the reduced triangle `X₀ = Spec K[x, y] ⧸ (xy(x + y - 1))`, covered by the
two opens `U = D(1 - x)` and `W = D(1 - y)`, the glueing cocycle `c`
(`Deformation.Artin.triangleCocycle`) is `η` on the open edge of `U ∩ W` and the unit on its
other piece. This file proves the Čech computation of the source: if `c ^ m` is a coboundary,
that is `c ^ m = s_U⁻¹ s_W` on `U ∩ W` for morphisms `s_U : U ⟶ A`, `s_W : W ⟶ A` over `k`,
then `η ^ m = 1`. For the generic point of a nonzero abelian variety, which has infinite order
(`Stacks.Groupoids.not_isOfFinOrder_genericPointHom`), no power `c ^ m` with `m > 0` is a
coboundary.

The reason is rigidity: `U` is the union of the line `x = 0` and the punctured line
`x + y = 1` minus `(1, 0)`, meeting at the vertex `(0, 1)`, and each of them is an open of the
projective line `ℙ¹_K`, on which every morphism to `A` is constant (Stacks 0BXZ and 0AEN, in
`AlgebraicGeometry.exists_section_eq_comp_of_opens_projectiveLineProj`). So `s_U` takes the same
value at the vertex `(0, 0)` of `U ∩ W` and at the point `(a, 1 - a)` of its open edge; the same
holds for `s_W`, through the line `y = 0` and the vertex `(1, 0)`. Evaluating the coboundary
equation at the two points gives `1 = s_U(0,0)⁻¹ s_W(0,0)` and
`η ^ m = s_U(a,1-a)⁻¹ s_W(a,1-a)`, whence `η ^ m = 1`.

## Main definitions

* `Deformation.Artin.functionFieldAlgebra` and `Deformation.Artin.genericPointOverField`: the
  function field `k(A)` as a `k`-algebra, and the generic point of `A` as a `k(A)`-point.

## Main results

* `AlgebraicGeometry.specOverFieldMap_comp_eq_of_isOpenImmersion`: a morphism to an abelian
  variety from an affine open of `ℙ¹_K` takes the same value at any two `K`-points.
* `Deformation.Artin.pow_eq_one_of_triangleCocycle_pow_eq`: the Čech computation.
* `Deformation.Artin.not_isOfFinOrder_genericPointOverField`: the generic point of a nonzero
  abelian variety has infinite order.
* `Deformation.Artin.triangleCocycle_genericPointOverField_pow_ne`: for the generic point of a
  nonzero abelian variety, no positive power of the cocycle is a coboundary.

## Implementation notes

The coboundary equation is evaluated at `K`-points, so one point `(a, 1 - a)` of the open edge
with `a ≠ 0, 1` is needed; for the generic point it is the image of such an element of `k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- A morphism over `K` from a scheme `Y` with an open immersion into `ℙ¹_K` to a group scheme
which is a proper variety takes the same value at two `K`-points of `Y`. -/
theorem comp_eq_comp_of_isOpenImmersion_projectiveLineProj (G : Over (Spec (.of K)))
    [GrpObj G] [IsProperVariety K G.hom] {Y : Scheme.{u}} (j : Y ⟶ projectiveLineProj K)
    [IsOpenImmersion j] (f : Y ⟶ G.left) (hf : f ≫ G.hom = j ≫ projToSpecCoeff K 1)
    (a b : Spec (.of K) ⟶ Y) (ha : a ≫ j ≫ projToSpecCoeff K 1 = 𝟙 _)
    (hb : b ≫ j ≫ projToSpecCoeff K 1 = 𝟙 _) : a ≫ f = b ≫ f := by
  have hne : (j.opensRange : Set (projectiveLineProj K)).Nonempty :=
    ⟨_, Set.mem_range_self (a (IsLocalRing.closedPoint K))⟩
  have hι : j.isoOpensRange.hom ≫ j.opensRange.ι = j := Scheme.Hom.isoOpensRange_hom_ι j
  obtain ⟨c, -, hc⟩ := exists_section_eq_comp_of_opens_projectiveLineProj G j.opensRange hne
    (j.isoOpensRange.inv ≫ f) (by
      have hinv : j.isoOpensRange.inv ≫ j = j.opensRange.ι := by
        rw [Iso.inv_comp_eq]
        exact hι.symm
      rw [Category.assoc, hf, ← Category.assoc, hinv])
  have hfc : f = j ≫ projToSpecCoeff K 1 ≫ c := by
    have h := congrArg (j.isoOpensRange.hom ≫ ·) hc
    simp only [Iso.hom_inv_id_assoc] at h
    rw [h, reassoc_of% hι]
  rw [hfc, reassoc_of% ha, reassoc_of% hb]

variable {k : Type u} [Field k] [Algebra k K]

/-- **Rigidity on an affine open of the projective line.** Let `A` be an abelian variety over
`k`, let `T` be a `K`-algebra and let `Spec T ⟶ ℙ¹_K` be an open immersion over `K`. A morphism
`Spec T ⟶ A` over `k` takes the same value at any two `K`-points of `Spec T`. -/
theorem specOverFieldMap_comp_eq_of_isOpenImmersion (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] {T : Type u} [CommRing T] [Algebra K T]
    (j : Spec (.of T) ⟶ projectiveLineProj K) [IsOpenImmersion j]
    (hj : j ≫ projToSpecCoeff K 1 = Spec.map (CommRingCat.ofHom (algebraMap K T)))
    (s : specOverField k K T ⟶ A) (φ ψ : T →ₐ[K] K) :
    specOverFieldMap φ ≫ s = specOverFieldMap ψ ≫ s := by
  set g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let G := (Over.pullback g).obj A
  have hs : s.left ≫ A.hom = (j ≫ projToSpecCoeff K 1) ≫ g := by
    rw [Over.w s, hj]
    rfl
  let f : Spec (.of T) ⟶ G.left := pullback.lift s.left (j ≫ projToSpecCoeff K 1) hs
  have hpt : ∀ φ : T →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j ≫ projToSpecCoeff K 1 = 𝟙 _ := by
    intro φ
    have hφ : φ.toRingHom.comp (algebraMap K T) = RingHom.id K := RingHom.ext fun r => φ.commutes r
    rw [hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [hφ, CommRingCat.ofHom_id, Spec.map_id]
  have h := comp_eq_comp_of_isOpenImmersion_projectiveLineProj G j f (pullback.lift_snd _ _ _)
    _ _ (hpt φ) (hpt ψ)
  ext1
  have h' := congrArg (· ≫ pullback.fst A.hom g) h
  simp only [Category.assoc, f, pullback.lift_fst] at h'
  exact h'

end AlgebraicGeometry

namespace Deformation.Artin

open AlgebraicGeometry LaurentPolynomial

section CechComputation

variable {K : Type u} [Field K]

/-- Evaluation of a Laurent polynomial at a unit, as a map of `K`-algebras. -/
def laurentEval (c : Kˣ) : K[T;T⁻¹] →ₐ[K] K :=
  AlgHom.mk (LaurentPolynomial.eval₂ (RingHom.id K) c) fun r => by
    rw [← LaurentPolynomial.C_eq_algebraMap]
    exact LaurentPolynomial.eval₂_C _ _ r

@[simp]
theorem laurentEval_T_one (c : Kˣ) : laurentEval c (T 1) = c := by
  change LaurentPolynomial.eval₂ (RingHom.id K) c (T 1) = c
  rw [LaurentPolynomial.eval₂_T, zpow_one]

@[simp]
theorem laurentEval_one (c : Kˣ) : laurentEval c 1 = 1 := map_one _

variable {k : Type u} [Field k] [Algebra k K] (A : Over (Spec (.of k))) [GrpObj A]
  [IsAbelianVariety k A]

/-- Rigidity on the affine line: a morphism `Spec K[t] ⟶ A` over `k` takes the same value at any
two `K`-points. -/
theorem specOverFieldMap_comp_eq_of_polynomial (s : specOverField k K (Polynomial K) ⟶ A)
    (φ ψ : Polynomial K →ₐ[K] K) : specOverFieldMap φ ≫ s = specOverFieldMap ψ ≫ s :=
  have : IsOpenImmersion (projectiveLineProjChart K 0) := by
    rw [← projectiveLineXChart_comp_projectiveLineIsoProj_hom]
    infer_instance
  specOverFieldMap_comp_eq_of_isOpenImmersion A (projectiveLineProjChart K 0)
    (by rw [projectiveLineProjChart_comp_projToSpecCoeff, Polynomial.algebraMap_eq]) s φ ψ

/-- Rigidity on the punctured affine line: a morphism `Spec K[t, t⁻¹] ⟶ A` over `k` takes the
same value at any two `K`-points. -/
theorem specOverFieldMap_comp_eq_of_laurent (s : specOverField k K K[T;T⁻¹] ⟶ A)
    (φ ψ : K[T;T⁻¹] →ₐ[K] K) : specOverFieldMap φ ≫ s = specOverFieldMap ψ ≫ s :=
  have : IsOpenImmersion (projectiveLineProjChart K 0) := by
    rw [← projectiveLineXChart_comp_projectiveLineIsoProj_hom]
    infer_instance
  specOverFieldMap_comp_eq_of_isOpenImmersion A
    (projectiveLinePuncturedChart K ≫ projectiveLineProjChart K 0) (by
      rw [Category.assoc, projectiveLineProjChart_comp_projToSpecCoeff,
        projectiveLineAffineStructureMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      simp [← LaurentPolynomial.C_eq_algebraMap]) s φ ψ

omit [GrpObj A] [IsAbelianVariety k A] in
/-- Precomposing with the morphism of a composite of algebra maps. -/
theorem specOverFieldMap_comp_comp {T T' : Type u} [CommRing T] [Algebra K T] [CommRing T']
    [Algebra K T'] (φ : T →ₐ[K] K) (ℓ : T' →ₐ[K] T) (s : specOverField k K T' ⟶ A) :
    specOverFieldMap (φ.comp ℓ) ≫ s = specOverFieldMap φ ≫ specOverFieldMap ℓ ≫ s := by
  rw [← Category.assoc, specOverFieldMap_comp]

/-- An evaluation of the localization `R_n[1/g]` at a solution of `uv(u + v - 1) = 0`, where
`(1 - u)(1 - v)` is the unit `g` is sent to. -/
theorem isUnit_triangleLevelLift_one_sub_mul {T : Type u} [CommRing T] [Algebra K T] {n : ℕ}
    (u v : T) (h : u * v * (u + v - 1) = 0) (huv : IsUnit ((1 - u) * (1 - v))) :
    IsUnit (triangleLevelLift (n := n) u v h ((1 - triangleX K n) * (1 - triangleY K n))) := by
  rwa [map_mul, map_sub, map_sub, map_one, triangleLevelLift_triangleX,
    triangleLevelLift_triangleY]

theorem isUnit_triangleLevelLift_one_sub_x {T : Type u} [CommRing T] [Algebra K T] {n : ℕ}
    (u v : T) (h : u * v * (u + v - 1) = 0) (hu : IsUnit (1 - u)) :
    IsUnit (triangleLevelLift (n := n) u v h (1 - triangleX K n)) := by
  rwa [map_sub, map_one, triangleLevelLift_triangleX]

theorem isUnit_triangleLevelLift_one_sub_y {T : Type u} [CommRing T] [Algebra K T] {n : ℕ}
    (u v : T) (h : u * v * (u + v - 1) = 0) (hv : IsUnit (1 - v)) :
    IsUnit (triangleLevelLift (n := n) u v h (1 - triangleY K n)) := by
  rwa [map_sub, map_one, triangleLevelLift_triangleY]

variable (K) in
/-- The vertex `(0, 0)` of the triangle, a `K`-point of `U ∩ W` on its piece `xy = 0`. -/
def triangleOverlapOrigin (n : ℕ) : triangleOverlap K n →ₐ[K] K :=
  triangleAwayLift _ 0 0 (by ring) (isUnit_triangleLevelLift_one_sub_mul _ _ _ (by simp))

/-- The point `(a, 1 - a)`, for `a ≠ 0, 1`, a `K`-point of `U ∩ W` on its open edge. -/
def triangleOverlapEdgePoint (n : ℕ) {a : K} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) :
    triangleOverlap K n →ₐ[K] K :=
  triangleAwayLift _ a (1 - a) (by ring) (isUnit_triangleLevelLift_one_sub_mul _ _ _ (by
    rw [sub_sub_cancel]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (sub_ne_zero.mpr (Ne.symm ha₁)) ha₀)))

variable (K) in
/-- The line `x = 0` inside `U`, parametrized by `y`. -/
def triangleLeftLine (n : ℕ) : triangleLeft K n →ₐ[K] Polynomial K :=
  triangleAwayLift _ 0 Polynomial.X (by ring) (isUnit_triangleLevelLift_one_sub_x _ _ _ (by simp))

variable (K) in
/-- The edge `x + y = 1` minus the vertex `(1, 0)` inside `U`, parametrized by `y ≠ 0`. -/
def triangleLeftEdge (n : ℕ) : triangleLeft K n →ₐ[K] K[T;T⁻¹] :=
  triangleAwayLift _ (1 - T 1) (T 1) (by ring)
    (isUnit_triangleLevelLift_one_sub_x _ _ _ (by rw [sub_sub_cancel]; exact isUnit_T 1))

variable (K) in
/-- The line `y = 0` inside `W`, parametrized by `x`. -/
def triangleRightLine (n : ℕ) : triangleRight K n →ₐ[K] Polynomial K :=
  triangleAwayLift _ Polynomial.X 0 (by ring) (isUnit_triangleLevelLift_one_sub_y _ _ _ (by simp))

variable (K) in
/-- The edge `x + y = 1` minus the vertex `(0, 1)` inside `W`, parametrized by `x ≠ 0`. -/
def triangleRightEdge (n : ℕ) : triangleRight K n →ₐ[K] K[T;T⁻¹] :=
  triangleAwayLift _ (T 1) (1 - T 1) (by ring)
    (isUnit_triangleLevelLift_one_sub_y _ _ _ (by rw [sub_sub_cancel]; exact isUnit_T 1))

/-- On `U`, the vertex `(0, 0)` of `U ∩ W` is the origin of the line `x = 0`. -/
theorem triangleOverlapOrigin_comp_left (n : ℕ) :
    (triangleOverlapOrigin K n).comp (triangleLeftToOverlap K n) =
      (Polynomial.aeval 0).comp (triangleLeftLine K n) :=
  triangleLevel_away_algHom_ext
    (by simp [triangleOverlapOrigin, triangleLeftLine])
    (by simp [triangleOverlapOrigin, triangleLeftLine])

/-- On `U`, the vertex `(0, 1)` lies on the line `x = 0` and on the punctured edge. -/
theorem triangleLeftLine_vertex (n : ℕ) :
    (Polynomial.aeval 1).comp (triangleLeftLine K n) =
      (laurentEval 1).comp (triangleLeftEdge K n) :=
  triangleLevel_away_algHom_ext
    (by simp [triangleLeftLine, triangleLeftEdge])
    (by simp [triangleLeftLine, triangleLeftEdge])

/-- On `U`, the point `(a, 1 - a)` of `U ∩ W` lies on the punctured edge, at `y = 1 - a`. -/
theorem triangleOverlapEdgePoint_comp_left (n : ℕ) {a : K} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) :
    (triangleOverlapEdgePoint n ha₀ ha₁).comp (triangleLeftToOverlap K n) =
      (laurentEval (Units.mk0 _ (sub_ne_zero.mpr (Ne.symm ha₁)))).comp (triangleLeftEdge K n) :=
  triangleLevel_away_algHom_ext
    (by simp [triangleOverlapEdgePoint, triangleLeftEdge])
    (by simp [triangleOverlapEdgePoint, triangleLeftEdge])

/-- On `W`, the vertex `(0, 0)` of `U ∩ W` is the origin of the line `y = 0`. -/
theorem triangleOverlapOrigin_comp_right (n : ℕ) :
    (triangleOverlapOrigin K n).comp (triangleRightToOverlap K n) =
      (Polynomial.aeval 0).comp (triangleRightLine K n) :=
  triangleLevel_away_algHom_ext
    (by simp [triangleOverlapOrigin, triangleRightLine])
    (by simp [triangleOverlapOrigin, triangleRightLine])

/-- On `W`, the vertex `(1, 0)` lies on the line `y = 0` and on the punctured edge. -/
theorem triangleRightLine_vertex (n : ℕ) :
    (Polynomial.aeval 1).comp (triangleRightLine K n) =
      (laurentEval 1).comp (triangleRightEdge K n) :=
  triangleLevel_away_algHom_ext
    (by simp [triangleRightLine, triangleRightEdge])
    (by simp [triangleRightLine, triangleRightEdge])

/-- On `W`, the point `(a, 1 - a)` of `U ∩ W` lies on the punctured edge, at `x = a`. -/
theorem triangleOverlapEdgePoint_comp_right (n : ℕ) {a : K} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) :
    (triangleOverlapEdgePoint n ha₀ ha₁).comp (triangleRightToOverlap K n) =
      (laurentEval (Units.mk0 _ ha₀)).comp (triangleRightEdge K n) :=
  triangleLevel_away_algHom_ext
    (by simp [triangleOverlapEdgePoint, triangleRightEdge])
    (by simp [triangleOverlapEdgePoint, triangleRightEdge])

/-- **The Čech computation on the triangle.** Let `A` be an abelian variety over `k`, let `K/k`
be a field extension with an element `a ≠ 0, 1`, and let `pt` be a `K`-point of `A`. If the
`m`-th power of the glueing cocycle of the reduced triangle is the coboundary of
`s_U : U ⟶ A`, `s_W : W ⟶ A` over `k`, that is `c ^ m = s_U⁻¹ s_W` on `U ∩ W`, then
`pt ^ m = 1`. -/
theorem pow_eq_one_of_triangleCocycle_pow_eq (pt : specOverField k K K ⟶ A) (m : ℕ)
    (sU : specOverField k K (triangleLeft K 0) ⟶ A)
    (sW : specOverField k K (triangleRight K 0) ⟶ A)
    (h : triangleCocycle K 0 A pt ^ m =
      (specOverFieldMap (triangleLeftToOverlap K 0) ≫ sU)⁻¹ *
        (specOverFieldMap (triangleRightToOverlap K 0) ≫ sW))
    {a : K} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) : pt ^ m = 1 := by
  have hP : specOverFieldMap (triangleOverlapOrigin K 0) ≫ triangleCocycle K 0 A pt = 1 :=
    specOverFieldMap_comp_triangleCocycle_of_rest A pt _ (by simp [triangleOverlapOrigin])
  have hQ : specOverFieldMap (triangleOverlapEdgePoint 0 ha₀ ha₁) ≫
      triangleCocycle K 0 A pt = pt :=
    specOverFieldMap_comp_triangleCocycle_of_edge A pt _ (by
      rw [triangleOverlapEdgePoint, triangleAwayLift_algebraMap, map_sub, map_add, map_one,
        triangleLevelLift_triangleX, triangleLevelLift_triangleY]
      ring)
  have key : ∀ ψ : triangleOverlap K 0 →ₐ[K] K,
      (specOverFieldMap ψ ≫ triangleCocycle K 0 A pt) ^ m =
        (specOverFieldMap (ψ.comp (triangleLeftToOverlap K 0)) ≫ sU)⁻¹ *
          (specOverFieldMap (ψ.comp (triangleRightToOverlap K 0)) ≫ sW) := by
    intro ψ
    rw [← MonObj.comp_pow, h, MonObj.comp_mul, GrpObj.comp_inv, specOverFieldMap_comp_comp,
      specOverFieldMap_comp_comp]
  have hU : specOverFieldMap ((triangleOverlapOrigin K 0).comp (triangleLeftToOverlap K 0)) ≫
      sU = specOverFieldMap ((triangleOverlapEdgePoint 0 ha₀ ha₁).comp
        (triangleLeftToOverlap K 0)) ≫ sU := by
    rw [triangleOverlapOrigin_comp_left, triangleOverlapEdgePoint_comp_left,
      specOverFieldMap_comp_comp, specOverFieldMap_comp_eq_of_polynomial A _ _
        (Polynomial.aeval 1), ← specOverFieldMap_comp_comp, triangleLeftLine_vertex,
      specOverFieldMap_comp_comp, specOverFieldMap_comp_eq_of_laurent A _ _
        (laurentEval (Units.mk0 _ (sub_ne_zero.mpr (Ne.symm ha₁)))),
      ← specOverFieldMap_comp_comp]
  have hW : specOverFieldMap ((triangleOverlapOrigin K 0).comp (triangleRightToOverlap K 0)) ≫
      sW = specOverFieldMap ((triangleOverlapEdgePoint 0 ha₀ ha₁).comp
        (triangleRightToOverlap K 0)) ≫ sW := by
    rw [triangleOverlapOrigin_comp_right, triangleOverlapEdgePoint_comp_right,
      specOverFieldMap_comp_comp, specOverFieldMap_comp_eq_of_polynomial A _ _
        (Polynomial.aeval 1), ← specOverFieldMap_comp_comp, triangleRightLine_vertex,
      specOverFieldMap_comp_comp, specOverFieldMap_comp_eq_of_laurent A _ _
        (laurentEval (Units.mk0 _ ha₀)), ← specOverFieldMap_comp_comp]
  have hPkey := key (triangleOverlapOrigin K 0)
  rw [hP, one_pow, eq_comm, inv_mul_eq_one] at hPkey
  have hQkey := key (triangleOverlapEdgePoint 0 ha₀ ha₁)
  rw [hQ, ← hU, ← hW, ← hPkey, inv_mul_cancel] at hQkey
  exact hQkey

end CechComputation

/-! ### The generic point -/

section GenericPoint

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]

/-- The function field of an abelian variety `A` over `k`, as a `k`-algebra through the
structure morphism of `A`. -/
abbrev functionFieldAlgebra : Algebra k A.left.functionField :=
  (Spec.preimage (A.left.fromSpecStalk (genericPoint A.left) ≫ A.hom)).hom.toAlgebra

/-- Through `functionFieldAlgebra`, the generic point of `A` lies over `Spec k`. -/
theorem fromSpecStalk_genericPoint_comp_hom :
    letI := functionFieldAlgebra A
    A.left.fromSpecStalk (genericPoint A.left) ≫ A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k A.left.functionField)) := by
  let _ := functionFieldAlgebra A
  change _ = Spec.map (CommRingCat.ofHom
    (Spec.preimage (A.left.fromSpecStalk (genericPoint A.left) ≫ A.hom)).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- Through `functionFieldAlgebra`, the generic point of `A` lies over `Spec k`, in the shape of
the structure morphism of `specOverField`. -/
theorem fromSpecStalk_genericPoint_comp_hom' :
    letI := functionFieldAlgebra A
    A.left.fromSpecStalk (genericPoint A.left) ≫ A.hom =
      (specOverField k A.left.functionField A.left.functionField).hom := by
  let _ := functionFieldAlgebra A
  dsimp only [Over.mk_hom]
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  exact fromSpecStalk_genericPoint_comp_hom A

/-- The generic point of `A`, as a `k(A)`-point in the shape `specOverField` of the glueing
cocycle. -/
def genericPointOverField :
    letI := functionFieldAlgebra A
    specOverField k A.left.functionField A.left.functionField ⟶ A :=
  letI := functionFieldAlgebra A
  Over.homMk (A.left.fromSpecStalk (genericPoint A.left)) (fromSpecStalk_genericPoint_comp_hom' A)

/-- **The generic point of a nonzero abelian variety has infinite order**, in the shape
`genericPointOverField`; this is `Stacks.Groupoids.not_isOfFinOrder_genericPointHom`. -/
theorem not_isOfFinOrder_genericPointOverField
    (hA : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A) :
    letI := functionFieldAlgebra A
    ¬ IsOfFinOrder (genericPointOverField A) := by
  let _ := functionFieldAlgebra A
  let e : specOverField k A.left.functionField A.left.functionField ≅
      Stacks.Groupoids.genericPointOver A :=
    Over.isoMk (Iso.refl _) (by
      rw [Iso.refl_hom, Category.id_comp]
      exact fromSpecStalk_genericPoint_comp_hom' A)
  have he : genericPointOverField A = e.hom ≫ Stacks.Groupoids.genericPointHom A := by
    ext1
    simp [e, genericPointOverField]
  intro h
  refine Stacks.Groupoids.not_isOfFinOrder_genericPointHom A hA ?_
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  rw [he, ← MonObj.comp_pow] at hpow
  have := congrArg (e.inv ≫ ·) hpow
  simpa only [Iso.inv_hom_id_assoc, MonObj.comp_one] using this

/-- **The glueing cocycle along the generic point has infinite order.** Let `A` be a nonzero
abelian variety over an infinite field `k` and let `K = k(A)`. No positive power of the glueing
cocycle of the reduced triangle over `K` along the generic point of `A` is a coboundary for the
cover by `U = D(1 - x)` and `W = D(1 - y)`. -/
theorem triangleCocycle_genericPointOverField_pow_ne [Infinite k]
    (hA : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A) {m : ℕ} (hm : m ≠ 0) :
    letI := functionFieldAlgebra A
    ∀ (sU : specOverField k A.left.functionField (triangleLeft A.left.functionField 0) ⟶ A)
      (sW : specOverField k A.left.functionField (triangleRight A.left.functionField 0) ⟶ A),
      triangleCocycle A.left.functionField 0 A (genericPointOverField A) ^ m ≠
        (specOverFieldMap (triangleLeftToOverlap A.left.functionField 0) ≫ sU)⁻¹ *
          (specOverFieldMap (triangleRightToOverlap A.left.functionField 0) ≫ sW) := by
  classical
  let _ := functionFieldAlgebra A
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  intro sU sW h
  obtain ⟨a₀, ha₀⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₀
  have hinj := (algebraMap k A.left.functionField).injective
  have hpow := pow_eq_one_of_triangleCocycle_pow_eq A (genericPointOverField A) m sU sW h
    (a := algebraMap k _ a₀) ((map_ne_zero _).mpr ha₀.1)
    (by rw [← map_one (algebraMap k A.left.functionField)]; exact hinj.ne ha₀.2)
  exact not_isOfFinOrder_genericPointOverField A hA
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, Nat.pos_of_ne_zero hm, hpow⟩)

end GenericPoint

end Deformation.Artin

end
