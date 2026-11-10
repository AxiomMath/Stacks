module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# The solutions of a system of linear equations are represented by an affine scheme

This module is independent of `StacksFrontier.AlgebraicGeometry.Quot.LinearEquationsRepresentable`,
which treats the kernel of a map `Γ(-, 𝒪)^m ⟶ Γ(-, 𝒪)^m'` on the test schemes as an algebraic
space.

Let `C` be a scheme and `M` an `n × m` matrix of functions on `C`.  The functor on schemes over
`C` sending `t : T ⟶ C` to the row vectors `v ∈ Γ(T, 𝒪_T)^n` with `v · t^♯M = 0` is represented
by the closed subscheme of the affine space `𝔸^n_C` cut out by the `m` linear forms of the
columns of `M`, which is affine and of finite presentation over `C`.  This is the scheme
`Spec(A[x₁, …, xₙ]/(∑ᵢ aᵢⱼ xᵢ))` of the last step of the proof of Stacks 08JX, built here as the
fibre of the linear map `𝔸^n_C ⟶ 𝔸^m_C` over the zero section, so that no affineness of `C` is
needed.

## Main definitions

* `AlgebraicGeometry.linEqScheme`: the representing scheme, with
  `AlgebraicGeometry.linEqProj` to `C`.
* `AlgebraicGeometry.linEqHomEquiv`: morphisms `T ⟶ linEqScheme M` over `t : T ⟶ C` are the
  solutions `v` of `v · t^♯M = 0`.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.AffineSpace

universe u

namespace AlgebraicGeometry

variable {C : Scheme.{u}} {n m : ℕ} (M : Matrix (Fin n) (Fin m) Γ(C, ⊤))

/-- The linear map `𝔸^n_C ⟶ 𝔸^m_C` of a matrix of functions, on row vectors. -/
def linMap : 𝔸(ULift.{u} (Fin n); C) ⟶ 𝔸(ULift.{u} (Fin m); C) :=
  homOfVector (𝔸(ULift.{u} (Fin n); C) ↘ C)
    (fun k => ∑ j, coord C ⟨j⟩ * (𝔸(ULift.{u} (Fin n); C) ↘ C).appTop (M j k.down))

/-- The linear map `linMap M` is a morphism over `C`. -/
@[reassoc (attr := simp)]
theorem linMap_over : linMap M ≫ 𝔸(ULift.{u} (Fin m); C) ↘ C = 𝔸(ULift.{u} (Fin n); C) ↘ C :=
  homOfVector_over _ _

variable (C m) in
/-- The zero section `C ⟶ 𝔸^m_C`. -/
def zeroSec : C ⟶ 𝔸(ULift.{u} (Fin m); C) := homOfVector (𝟙 C) 0

/-- **The scheme of solutions** of the linear equations of `M`: the fibre of the linear map over
the zero section. -/
abbrev linEqScheme : Scheme.{u} := pullback (linMap M) (zeroSec C m)

/-- The projection of the scheme of solutions to the base. -/
abbrev linEqProj : linEqScheme M ⟶ C := pullback.snd _ _

/-- The linear map `linMap M` is an affine morphism. -/
instance isAffineHom_linMap : IsAffineHom (linMap M) := by
  have : IsAffineHom (linMap M ≫ 𝔸(ULift.{u} (Fin m); C) ↘ C) := by rw [linMap_over]; infer_instance
  exact IsAffineHom.of_comp (linMap M) (𝔸(ULift.{u} (Fin m); C) ↘ C)

/-- The linear map `linMap M` is locally of finite presentation. -/
instance locallyOfFinitePresentation_linMap : LocallyOfFinitePresentation (linMap M) := by
  have : LocallyOfFinitePresentation (linMap M ≫ 𝔸(ULift.{u} (Fin m); C) ↘ C) := by
    rw [linMap_over]; infer_instance
  exact locallyOfFinitePresentation_of_comp (linMap M) (𝔸(ULift.{u} (Fin m); C) ↘ C)

/-- The projection `linEqProj M` of the scheme of solutions to `C` is affine. -/
instance isAffineHom_linEqProj : IsAffineHom (linEqProj M) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback (linMap M) (zeroSec C m)) inferInstance

/-- The projection `linEqProj M` of the scheme of solutions to `C` is locally of finite
presentation. -/
instance locallyOfFinitePresentation_linEqProj : LocallyOfFinitePresentation (linEqProj M) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (IsPullback.of_hasPullback (linMap M) (zeroSec C m)) inferInstance

/-- A morphism into affine space is the vector of its coordinates. -/
theorem eq_homOfVector {T : Scheme.{u}} {k : Type u} (a : T ⟶ 𝔸(k; C)) :
    a = homOfVector (a ≫ 𝔸(k; C) ↘ C) (fun i => a.appTop (coord C i)) := by
  ext1
  · simp
  · rename_i i; simp

/-- The coordinates of `homOfVector` determine the vector. -/
theorem homOfVector_injective {T : Scheme.{u}} {k : Type u} (t : T ⟶ C) {v w : k → Γ(T, ⊤)}
    (h : homOfVector t v = homOfVector t w) : v = w :=
  funext fun i => by
    have := congrArg (fun f : T ⟶ 𝔸(k; C) => f.appTop (coord C i)) h
    simpa using this

/-- The coordinates of the composite of a vector with the linear map. -/
theorem homOfVector_linMap {T : Scheme.{u}} (t : T ⟶ C) (v : Fin n → Γ(T, ⊤)) :
    homOfVector t (fun j => v j.down) ≫ linMap M =
      homOfVector t (fun k => Matrix.vecMul v (M.map t.appTop.hom) k.down) := by
  ext1
  · simp
  · rename_i k
    simp only [linMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      homOfVector_appTop_coord, map_sum, map_mul, Matrix.vecMul, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, homOfVector_over]

/-- The zero section, precomposed. -/
theorem comp_zeroSec {T : Scheme.{u}} (t : T ⟶ C) : t ≫ zeroSec C m = homOfVector t 0 := by
  rw [zeroSec, comp_homOfVector, Category.comp_id]
  congr 1
  funext k
  simp

/-- A morphism into the scheme of solutions over `t`, read in affine space, is the vector of its
coordinates over `t`. -/
theorem fst_eq_homOfVector {T : Scheme.{u}} (t : T ⟶ C) (x : T ⟶ linEqScheme M)
    (hx : x ≫ linEqProj M = t) :
    x ≫ pullback.fst _ _ = homOfVector t (fun j => (x ≫ pullback.fst _ _).appTop (coord C j)) := by
  refine (eq_homOfVector _).trans ?_
  congr 1
  rw [Category.assoc, ← linMap_over M, ← Category.assoc (pullback.fst _ _), pullback.condition,
    Category.assoc]
  change x ≫ pullback.snd _ _ ≫ homOfVector (𝟙 C) 0 ≫ _ = t
  rw [homOfVector_over, Category.comp_id, hx]

/-- **Morphisms into the scheme of solutions over `t : T ⟶ C` are the solutions over `T`.** -/
def linEqHomEquiv {T : Scheme.{u}} (t : T ⟶ C) :
    {x : T ⟶ linEqScheme M // x ≫ linEqProj M = t} ≃
      {v : Fin n → Γ(T, ⊤) // Matrix.vecMul v (M.map t.appTop.hom) = 0} where
  toFun x := ⟨fun j => (x.1 ≫ pullback.fst _ _).appTop (coord C ⟨j⟩), by
    obtain ⟨x, hx⟩ := x
    have h1 := fst_eq_homOfVector M t x hx
    have h2 : homOfVector t (fun k : ULift.{u} (Fin m) => Matrix.vecMul
        (fun j => (x ≫ pullback.fst _ _).appTop (coord C ⟨j⟩)) (M.map t.appTop.hom) k.down) =
        homOfVector t 0 := by
      rw [← homOfVector_linMap, ← comp_zeroSec]
      subst hx
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ linMap M) h1.symm
    funext k
    exact congrFun (homOfVector_injective t h2) (⟨k⟩ : ULift.{u} (Fin m))⟩
  invFun v := ⟨pullback.lift (homOfVector t (fun j => v.1 j.down)) t (by
      rw [homOfVector_linMap, comp_zeroSec]
      congr 1
      funext k
      rw [v.2]
      rfl), pullback.lift_snd _ _ _⟩
  left_inv x := by
    refine Subtype.ext (pullback.hom_ext ?_ ?_)
    · rw [pullback.lift_fst, fst_eq_homOfVector M t x.1 x.2]
    · rw [pullback.lift_snd, x.2]
  right_inv v := by
    refine Subtype.ext (funext fun j => ?_)
    change (pullback.lift (homOfVector t (fun j => v.1 j.down)) t _ ≫
      pullback.fst (linMap M) (zeroSec C m)).appTop (coord C ⟨j⟩) = _
    rw [pullback.lift_fst, homOfVector_appTop_coord]

/-- `AlgebraicGeometry.linEqHomEquiv` is natural in `T`: precomposition with `g : T' ⟶ T` is
pullback of the solution along `g`. -/
theorem linEqHomEquiv_comp {T T' : Scheme.{u}} (t : T ⟶ C) (g : T' ⟶ T)
    (x : {x : T ⟶ linEqScheme M // x ≫ linEqProj M = t}) :
    (linEqHomEquiv M (g ≫ t) ⟨g ≫ x.1, by rw [Category.assoc, x.2]⟩).1 =
      fun j => g.appTop ((linEqHomEquiv M t x).1 j) := by
  funext j
  change (g ≫ x.1 ≫ pullback.fst _ _).appTop _ = _
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rfl

end AlgebraicGeometry
