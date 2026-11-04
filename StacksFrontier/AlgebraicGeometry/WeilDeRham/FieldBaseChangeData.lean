module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassIntegral
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethOfIsPullback
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.Product
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChange

/-!
# Comparison of two sets of data (D0), (D1), (D2') along a field extension

Lemma 0FVT of the Stacks Project starts from an extension of fields `k'/k`, an extension `F'/F`
of fields of characteristic zero, data (D0), (D1), (D2') for `k` and `F` denoted `F(1)`, `H^*`,
`c₁^H`, data (D0), (D1), (D2') for `k'` and `F'` denoted `F'(1)`, `(H')^*`, `c₁^{H'}`, and

* an isomorphism `F(1) ⊗_F F' → F'(1)`,
* functorial isomorphisms `H^*(X) ⊗_F F' → (H')^*(X_{k'})` on the category of smooth projective
  schemes `X` over `k`,

such that the squares

  `Pic(X)      --c₁^H-->   H^2(X)(1)`
  `   |                        |`
  `Pic(X_{k'}) --c₁^{H'}--> (H')^2(X_{k'})(1)`

commute. This file writes these comparison data down
(`Stacks.WeilDeRham.FieldBaseChangeData`).

## Implementation notes

* `X ↦ X_{k'}` is the base change functor `Stacks.WeilDeRham.fieldBaseChange`, and
  `Pic(X) → Pic(X_{k'})` is pullback along the projection `X_{k'} ⟶ X`, on the class of an
  invertible module as in axiom (A2).
* `H^*(X)` takes values in graded commutative `F`-algebras, so an isomorphism
  `H^*(X) ⊗_F F' → (H')^*(X_{k'})` is one of graded `F'`-algebras: an `F'`-algebra isomorphism
  `F' ⊗_F H^*(X) ≃ (H')^*(X_{k'})` carrying `H^n(X)` into `(H')^n(X_{k'})`. Functoriality is
  naturality along the pullbacks `f^*` and `(f_{k'})^*`. The base change of a vector space `V` is
  written `F' ⊗_F V`, as in Mathlib.
* The right vertical arrow of the square is the map
  `H^*(X)(1) = H^*(X) ⊗_F F(1) → (H^*(X) ⊗_F F') ⊗_{F'} (F(1) ⊗_F F') ≅ (H')^*(X_{k'})(1)`
  induced by the two isomorphisms. It is the restriction to `H^*(X)(1)` of the `F'`-linear
  isomorphism `Stacks.WeilDeRham.twistEquiv` of `F' ⊗_F H^*(X)(n)` with `(H')^*(X_{k'})(n)`,
  built for every `n ∈ 𝐙` from the two isomorphisms through the coordinates of the Tate twists;
  `Stacks.WeilDeRham.twistEquiv_one_tmul` shows that for `n = 1` it is the induced map
  `a ⊗ l ↦ (a ⊗ 1) ⊗ (l ⊗ 1)` above, independently of the coordinate.

## Main definitions

* `Stacks.WeilDeRham.twistEquiv`: the isomorphism `F' ⊗_F H^*(X)(n) ≅ (H')^*(X_{k'})(n)`.
* `Stacks.WeilDeRham.FieldBaseChangeData`: the hypothesis (3) of Lemma 0FVT.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.WeilCohomology

universe u w w'

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']

section Twist

variable (𝔇 : FirstChernClassData k F) (𝔇' : FirstChernClassData k' F')

/-- The coordinate on `F'(1)` induced from the coordinate `tateLineCoordinate` of `F(1)` by an
isomorphism `F' ⊗_F F(1) ≅ F'(1)`. -/
def inducedTateCoordinate (tateEquiv : F' ⊗[F] 𝔇.tate ≃ₗ[F'] 𝔇'.tate) : 𝔇'.tate ≃ₗ[F'] F' :=
  tateEquiv.symm.trans
    ((LinearEquiv.baseChange F F' _ _ (tateLineCoordinate 𝔇.finrank_tate)).trans
      (Algebra.TensorProduct.rid F F' F').toLinearEquiv)

omit [Algebra k k'] in
/-- The induced coordinate on `F'(1)` takes the image of `1 ⊗ l` to the image in `F'` of the
coordinate of `l ∈ F(1)`. -/
theorem inducedTateCoordinate_apply (tateEquiv : F' ⊗[F] 𝔇.tate ≃ₗ[F'] 𝔇'.tate) (l : 𝔇.tate) :
    inducedTateCoordinate 𝔇 𝔇' tateEquiv (tateEquiv (1 ⊗ₜ l)) =
      algebraMap F F' (tateLineCoordinate 𝔇.finrank_tate l) := by
  simp [inducedTateCoordinate, Algebra.algebraMap_eq_smul_one]

/-- **The isomorphism `F' ⊗_F H^*(X)(n) ≅ (H')^*(X_{k'})(n)`** induced by the isomorphisms
`F' ⊗_F F(1) ≅ F'(1)` and `F' ⊗_F H^*(X) ≅ (H')^*(X_{k'})`, read through the coordinates of the
Tate twists. -/
def twistEquiv (tateEquiv : F' ⊗[F] 𝔇.tate ≃ₗ[F'] 𝔇'.tate)
    (cohEquiv : ∀ X, F' ⊗[F] 𝔇.H X ≃ₐ[F'] 𝔇'.H ((fieldBaseChange k k').obj X))
    (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    F' ⊗[F] tateTwist F 𝔇.tate (𝔇.H X) n ≃ₗ[F']
      tateTwist F' 𝔇'.tate (𝔇'.H ((fieldBaseChange k k').obj X)) n :=
  (LinearEquiv.baseChange F F' _ _
      (tateTwistCoordinates (tateLineCoordinate 𝔇.finrank_tate) n)).trans
    ((cohEquiv X).toLinearEquiv.trans
      (tateTwistCoordinates (inducedTateCoordinate 𝔇 𝔇' tateEquiv) n).symm)

variable {𝔇 𝔇'}

/-- `twistEquiv` in coordinates: the coordinates of the image of `a ∈ H^*(X)(n)` are the image
of the coordinates of `a`. -/
theorem tateTwistCoordinates_twistEquiv_tmul (tateEquiv : F' ⊗[F] 𝔇.tate ≃ₗ[F'] 𝔇'.tate)
    (cohEquiv : ∀ X, F' ⊗[F] 𝔇.H X ≃ₐ[F'] 𝔇'.H ((fieldBaseChange k k').obj X))
    (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (a : tateTwist F 𝔇.tate (𝔇.H X) n) :
    tateTwistCoordinates (inducedTateCoordinate 𝔇 𝔇' tateEquiv) n
        (twistEquiv 𝔇 𝔇' tateEquiv cohEquiv X n (1 ⊗ₜ a)) =
      cohEquiv X (1 ⊗ₜ tateTwistCoordinates (tateLineCoordinate 𝔇.finrank_tate) n a) := by
  simp [twistEquiv]

/-- **For `n = 1`, `twistEquiv` is the induced map** `a ⊗ l ↦ (a ⊗ 1) ⊗ (l ⊗ 1)` of
`H^*(X)(1) = H^*(X) ⊗_F F(1)` to `(H')^*(X_{k'}) ⊗_{F'} F'(1)`; in particular it does not
depend on the coordinate of `F(1)`. -/
theorem twistEquiv_one_tmul (tateEquiv : F' ⊗[F] 𝔇.tate ≃ₗ[F'] 𝔇'.tate)
    (cohEquiv : ∀ X, F' ⊗[F] 𝔇.H X ≃ₐ[F'] 𝔇'.H ((fieldBaseChange k k').obj X))
    (X : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X) (l : 𝔇.tate) :
    twistEquiv 𝔇 𝔇' tateEquiv cohEquiv X 1
        (1 ⊗ₜ (a ⊗ₜ PiTensorProduct.tprod F (fun _ : Fin 1 => l) :
          tateTwist F 𝔇.tate (𝔇.H X) 1)) =
      (cohEquiv X (1 ⊗ₜ a) ⊗ₜ PiTensorProduct.tprod F' (fun _ : Fin 1 => tateEquiv (1 ⊗ₜ l)) :
        tateTwist F' 𝔇'.tate (𝔇'.H ((fieldBaseChange k k').obj X)) 1) := by
  apply (tateTwistCoordinates (inducedTateCoordinate 𝔇 𝔇' tateEquiv) 1).injective
  rw [tateTwistCoordinates_twistEquiv_tmul, tateTwistCoordinates_tmul, tateTwistCoordinates_tmul]
  show cohEquiv X (1 ⊗ₜ (tensorPowerCoordinates _ 1 _ • a)) =
    tensorPowerCoordinates _ 1 _ • cohEquiv X (1 ⊗ₜ a)
  simp only [tensorPowerCoordinates, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
    AlgEquiv.toLinearEquiv_apply, PiTensorProduct.constantBaseRingEquiv_tprod,
    Finset.univ_unique, Finset.prod_singleton, inducedTateCoordinate_apply]
  rw [TensorProduct.tmul_smul, ← algebraMap_smul F', map_smul, Algebra.smul_def]

end Twist

/-- **The hypothesis (3) of Lemma 0FVT**: for an extension `k'/k` and an extension `F'/F`, data
(D0), (D1), (D2') `𝔇` for `k`, `F` and `𝔇'` for `k'`, `F'` are compared by

* an isomorphism `F(1) ⊗_F F' ≅ F'(1)`,
* functorial isomorphisms of graded `F'`-algebras `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` on the category
  of smooth projective schemes over `k`,

such that `c₁^{H'}(ℒ_{k'})` is the image of `c₁^H(ℒ)` for every invertible module `ℒ` on `X`, the
image being taken by the map `H^*(X)(1) → (H')^*(X_{k'})(1)` induced by the two isomorphisms. -/
structure FieldBaseChangeData (𝔇 : FirstChernClassData k F) (𝔇' : FirstChernClassData k' F') where
  /-- The isomorphism `F(1) ⊗_F F' ≅ F'(1)`. -/
  tateEquiv : F' ⊗[F] 𝔇.tate ≃ₗ[F'] 𝔇'.tate
  /-- The isomorphisms `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})`. -/
  cohEquiv : ∀ X, F' ⊗[F] 𝔇.H X ≃ₐ[F'] 𝔇'.H ((fieldBaseChange k k').obj X)
  /-- The isomorphisms are functorial: they intertwine `f^*` and `(f_{k'})^*`. -/
  cohEquiv_pull : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (a : 𝔇.H Y),
    cohEquiv X (1 ⊗ₜ 𝔇.pull f a) = 𝔇'.pull ((fieldBaseChange k k').map f) (cohEquiv Y (1 ⊗ₜ a))
  /-- The isomorphisms are graded: they carry `H^n(X)` into `(H')^n(X_{k'})`. -/
  cohEquiv_grade : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (a : 𝔇.H X),
    a ∈ 𝔇.grade X n → cohEquiv X (1 ⊗ₜ a) ∈ 𝔇'.grade ((fieldBaseChange k k').obj X) n
  /-- The squares relating `c₁^H` and `c₁^{H'}` commute. -/
  c₁_compat : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L),
    twistEquiv 𝔇 𝔇' tateEquiv cohEquiv X 1 (1 ⊗ₜ 𝔇.c₁ X (picardClassOf _ L hL)) =
      𝔇'.c₁ ((fieldBaseChange k k').obj X)
        (picardClassOf _ ((Scheme.Modules.pullback (fieldBaseChangeProj X)).obj L)
          (isInvertible_pullback_obj _ L hL))

/-! ### The comparison maps on elements -/

/-- Over a field, `v ↦ 1 ⊗ v` is injective from an `F`-vector space to its base change along a
field extension `F'/F`: `F'` is a nonzero free `F`-module, hence faithfully flat. -/
theorem injective_one_tmul (V : Type*) [AddCommGroup V] [Module F V] :
    Function.Injective fun v : V => (1 : F') ⊗ₜ[F] v := by
  intro v v' h
  obtain ⟨s, hs⟩ := (Algebra.linearMap F F').exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F F').injective)
  have h2 := congrArg ((TensorProduct.lid F V).toLinearMap ∘ₗ LinearMap.rTensor V s) h
  have h1 : s 1 = 1 := by simpa using LinearMap.ext_iff.mp hs 1
  simpa [h1] using h2

namespace FieldBaseChangeData

variable {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}
  (B : FieldBaseChangeData 𝔇 𝔇')

/-- **The comparison map `H^*(X) → (H')^*(X_{k'})`**, `a ↦ image of a ⊗ 1`, a ring map. -/
def cohHom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔇.H X →+* 𝔇'.H ((fieldBaseChange k k').obj X) :=
  (B.cohEquiv X).toRingEquiv.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

/-- `cohHom X a` is the image of `1 ⊗ a` under `cohEquiv X`. -/
theorem cohHom_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X) :
    B.cohHom X a = B.cohEquiv X (1 ⊗ₜ a) :=
  rfl

/-- `cohHom` is semilinear along `F → F'`. -/
theorem cohHom_smul (X : (SmoothProjectiveScheme k).FullSubcategory) (c : F) (a : 𝔇.H X) :
    B.cohHom X (c • a) = algebraMap F F' c • B.cohHom X a := by
  rw [cohHom_apply, cohHom_apply, TensorProduct.tmul_smul, ← algebraMap_smul F', map_smul]

/-- `cohHom` is natural: `(f_{k'})^* ∘ cohHom = cohHom ∘ f^*`. -/
theorem cohHom_pull {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (a : 𝔇.H Y) :
    B.cohHom X (𝔇.pull f a) = 𝔇'.pull ((fieldBaseChange k k').map f) (B.cohHom Y a) :=
  B.cohEquiv_pull f a

/-- `cohHom` carries `H^n(X)` into `(H')^n(X_{k'})`. -/
theorem cohHom_mem_grade (X : (SmoothProjectiveScheme k).FullSubcategory) {n : ℤ} {a : 𝔇.H X}
    (ha : a ∈ 𝔇.grade X n) : B.cohHom X a ∈ 𝔇'.grade ((fieldBaseChange k k').obj X) n :=
  B.cohEquiv_grade X n a ha

/-- **The comparison map `H^*(X)(n) → (H')^*(X_{k'})(n)` on twisted classes**, `a ↦ image of
a ⊗ 1` under `twistEquiv`. For `n = 1` it is the right vertical arrow of the square of the
hypothesis on `c₁` (`Stacks.WeilDeRham.twistEquiv_one_tmul`). -/
def twistHom (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    tateTwist F 𝔇.tate (𝔇.H X) n →+ tateTwist F' 𝔇'.tate (𝔇'.H ((fieldBaseChange k k').obj X)) n :=
  (twistEquiv 𝔇 𝔇' B.tateEquiv B.cohEquiv X n).toLinearMap.toAddMonoidHom.comp
    (TensorProduct.mk F F' _ 1).toAddMonoidHom

/-- `twistHom X n a` is the image of `1 ⊗ a` under `twistEquiv`. -/
theorem twistHom_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a : tateTwist F 𝔇.tate (𝔇.H X) n) :
    B.twistHom X n a = twistEquiv 𝔇 𝔇' B.tateEquiv B.cohEquiv X n (1 ⊗ₜ a) :=
  rfl

/-- `twistHom` in coordinates is `cohHom`. -/
theorem tateTwistCoordinates_twistHom (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a : tateTwist F 𝔇.tate (𝔇.H X) n) :
    tateTwistCoordinates (inducedTateCoordinate 𝔇 𝔇' B.tateEquiv) n (B.twistHom X n a) =
      B.cohHom X (tateTwistCoordinates (tateLineCoordinate 𝔇.finrank_tate) n a) :=
  tateTwistCoordinates_twistEquiv_tmul B.tateEquiv B.cohEquiv X n a

/-- The hypothesis on `c₁` in terms of `twistHom`. -/
theorem twistHom_c₁ (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L) :
    B.twistHom X 1 (𝔇.c₁ X (picardClassOf _ L hL)) =
      𝔇'.c₁ ((fieldBaseChange k k').obj X)
        (picardClassOf _ ((Scheme.Modules.pullback (fieldBaseChangeProj X)).obj L)
          (isInvertible_pullback_obj _ L hL)) :=
  B.c₁_compat X L hL

end FieldBaseChangeData

end Stacks.WeilDeRham

end
