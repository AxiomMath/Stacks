module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Algebra.Module.GradedModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.GradedComponents
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge

/-!
# The graded exterior algebra of the differentials

The graded module structures on the homogeneous components of the Kähler differentials and of
the differential forms, the graded map induced by the universal derivation, the compatibility of
the wedge product with the exterior and total degrees, the graded algebra structure on the direct
sum of the homogeneous components of the exterior algebra of `Ω_{A/R}`, and the map into it from
the direct sum of the homogeneous components of `Ω_{A/R}`.

## Main results

* `KaehlerDifferential.gradedDifferentialFormComponent_wedgeMul_mem`: the wedge product adds both
  the exterior degree and the total degree.
-/

@[expose] public section

namespace KaehlerDifferential

open DirectSum

universe u v w

@[instance_reducible]
private noncomputable def gradedAlgebra_of_isInternal
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) : GradedAlgebra gr :=
  DirectSum.IsInternal.gradedAlgebra hgr

private theorem gradedDifferentialFormComponent_smul_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    {i g : G} {p : ℕ} {a : A} (ha : a ∈ gr i)
    {x : ⋀[A]^p (KaehlerDifferential R A)}
    (hx : x ∈ gradedDifferentialFormComponent gr p g) :
    a • x ∈ gradedDifferentialFormComponent gr p (i + g) := by
  classical
  rw [gradedDifferentialFormComponent] at hx ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨degree, b, hg, rfl⟩
    rw [smul_smul]
    apply Submodule.subset_span
    let degree' := Function.update degree 0 (i + degree 0)
    let b' : ∀ j, gr (degree' j) := fun j => if hj : j = 0 then by
      subst j
      exact ⟨a * (b 0 : A), by simpa [degree'] using SetLike.GradedMul.mul_mem ha (b 0).property⟩
      else by
        refine ⟨b j, ?_⟩
        simp [degree', Function.update_of_ne hj, (b j).property]
    refine ⟨degree', b', ?_, ?_⟩
    · have hsum : ∑ j : Fin (p + 1), degree' j = i + ∑ j : Fin (p + 1), degree j := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp [degree', add_assoc]
      rw [hsum, ← hg]
    · simp [b', degree']
  · simp
  · intro x y _ _ hx' hy'
    simpa [smul_add] using add_mem hx' hy'
  · intro c x _ hx'
    rw [smul_comm]
    exact Submodule.smul_mem _ c hx'

private theorem gradedDifferentialFormComponent_gradedSMul
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr] (p : ℕ) :
    SetLike.GradedSMul gr (gradedDifferentialFormComponent gr p) where
  smul_mem _ _ _ _ ha hx := gradedDifferentialFormComponent_smul_mem gr ha hx

@[instance_reducible]
private noncomputable def gradedDifferentialFormDirectSumModule
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) (p : ℕ) :
    Module A (⨁ (g : G), gradedDifferentialFormComponent gr p g) := by
  let _ := gradedAlgebra_of_isInternal gr hgr
  let _ : SetLike.GradedSMul gr (gradedDifferentialFormComponent gr p) :=
    gradedDifferentialFormComponent_gradedSMul gr p
  let _ : DirectSum.Gmodule (fun g => gr g) (fun g => gradedDifferentialFormComponent gr p g) :=
    inferInstance
  exact GradedModule.isModule gr (gradedDifferentialFormComponent gr p)

private noncomputable def homogeneousExteriorAlgebraComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) (g : G) :
    Submodule R (ExteriorAlgebra A (KaehlerDifferential R A)) :=
  ⨆ p : ℕ,
    (gradedDifferentialFormComponent gr p g).map
      ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype.restrictScalars R)

/-- Membership in the degree-`g` component of the differentials, via `⋀[A]^1`. -/
private theorem mem_gradedDifferentialComponent_iff_symm_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) (g : G) (x : KaehlerDifferential R A) :
    x ∈ gradedDifferentialComponent gr g ↔
      (exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm x ∈
        gradedDifferentialFormComponent gr 1 g := by
  simpa using exteriorPower_oneEquiv_mem_gradedDifferentialComponent
    gr g ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm x)

private theorem gradedDifferentialComponent_smul_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    {i g : G} {a : A} (ha : a ∈ gr i)
    {x : KaehlerDifferential R A}
    (hx : x ∈ gradedDifferentialComponent gr g) :
    a • x ∈ gradedDifferentialComponent gr (i + g) := by
  rw [mem_gradedDifferentialComponent_iff_symm_mem] at hx ⊢
  simpa using gradedDifferentialFormComponent_smul_mem gr ha hx

private theorem gradedDifferentialComponent_gradedSMul
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr] :
    SetLike.GradedSMul gr
      (gradedDifferentialComponent gr) where
  smul_mem _ _ _ _ ha hx := gradedDifferentialComponent_smul_mem gr ha hx

@[instance_reducible]
private noncomputable def gradedDifferentialDirectSumModule
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
  Module A (⨁ (g : G),
      gradedDifferentialComponent gr g) := by
  let _ := gradedAlgebra_of_isInternal gr hgr
  let _ : SetLike.GradedSMul gr
      (gradedDifferentialComponent gr) :=
    gradedDifferentialComponent_gradedSMul gr
  let _ : DirectSum.Gmodule (fun g => gr g)
      (fun g => gradedDifferentialComponent gr g) :=
    inferInstance
  exact GradedModule.isModule gr
    (gradedDifferentialComponent gr)

private theorem derivation_mem_gradedDifferentialComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    {g : G} {a : A} (ha : a ∈ gr g) :
    KaehlerDifferential.D R A a ∈
      gradedDifferentialComponent gr g := by
  let degree : Fin (1 + 1) → G := Fin.cons 0 (fun _ => g)
  let coeff : ∀ i, gr (degree i) :=
    Fin.cons ⟨1, SetLike.one_mem_graded gr⟩ (fun _ => ⟨a, ha⟩)
  have hform : (exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm
      (KaehlerDifferential.D R A a) ∈ gradedDifferentialFormComponent gr 1 g := by
    have hgen := homogeneousDifferentialForm_mem_gradedDifferentialFormComponent
      gr 1 degree coeff g (by simp [degree])
    have heq : (coeff 0 : A) • exteriorPower.ιMulti A 1
          (fun i ↦ KaehlerDifferential.D R A (coeff i.succ : A)) =
        (exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm
          (KaehlerDifferential.D R A a) := by
      apply (exteriorPower.oneEquiv A (KaehlerDifferential R A)).injective
      simp [coeff, exteriorPower.oneEquiv_ιMulti]
    rwa [← heq]
  exact (mem_gradedDifferentialComponent_iff_symm_mem gr g _).mpr hform

/-- The image of a form of exterior degree `p` and total degree `g` in the exterior algebra lies
in the degree-`g` component. -/
private theorem coe_mem_homogeneousExteriorAlgebraComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) (p : ℕ) {g : G} {x : ⋀[A]^p (KaehlerDifferential R A)}
    (hx : x ∈ gradedDifferentialFormComponent gr p g) :
    (x : ExteriorAlgebra A (KaehlerDifferential R A)) ∈
      homogeneousExteriorAlgebraComponent gr g :=
  Submodule.mem_iSup_of_mem p (Submodule.mem_map_of_mem
    (f := (ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype.restrictScalars R)
    hx)

private theorem exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A)
    {g : G} {x : KaehlerDifferential R A}
    (hx : x ∈ gradedDifferentialComponent gr g) :
    ExteriorAlgebra.ι A x ∈ homogeneousExteriorAlgebraComponent gr g := by
  simpa [exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti_apply_coe] using
    coe_mem_homogeneousExteriorAlgebraComponent gr 1
      ((mem_gradedDifferentialComponent_iff_symm_mem gr g x).mp hx)

private noncomputable def homogeneousDifferentialComponentMap
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr] (g : G) :
    gr g →ₗ[R] gradedDifferentialComponent gr g where
  toFun a := ⟨KaehlerDifferential.D R A (a : A),
    derivation_mem_gradedDifferentialComponent gr a.property⟩
  map_add' x y := Subtype.ext ((KaehlerDifferential.D R A).toLinearMap.map_add x y)
  map_smul' r x := Subtype.ext (by
    exact (KaehlerDifferential.D R A).toLinearMap.map_smul r (x : A))

private noncomputable def gradedDifferentialMap
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    A →ₗ[R] ⨁ g,
      gradedDifferentialComponent gr g := by
  let _ := gradedAlgebra_of_isInternal gr hgr
  let f : (⨁ g, gr g) →ₗ[R] ⨁ g,
      gradedDifferentialComponent gr g :=
    DirectSum.toModule R G _ (fun g =>
      (DirectSum.lof R G (fun g =>
        gradedDifferentialComponent gr g) g).comp
        (homogeneousDifferentialComponentMap gr g))
  exact f.comp (DirectSum.decomposeLinearEquiv gr).toLinearMap

private theorem gradedDifferentialMap_of_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) {g : G} {a : A} (ha : a ∈ gr g) :
    gradedDifferentialMap gr hgr a = DirectSum.of _ g
      ⟨KaehlerDifferential.D R A a, derivation_mem_gradedDifferentialComponent gr ha⟩ := by
  let _ := gradedAlgebra_of_isInternal gr hgr
  change (DirectSum.toModule R G _ (fun g =>
      (DirectSum.lof R G (fun g =>
        gradedDifferentialComponent gr g) g).comp
        (homogeneousDifferentialComponentMap gr g)))
      (DirectSum.decomposeLinearEquiv gr a) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe gr g ⟨a, ha⟩]
  rw [DirectSum.toModule_lof]
  simp [homogeneousDifferentialComponentMap, DirectSum.lof_eq_of]

/-- **Stacks Project, Tag 0FU9.** The wedge product is compatible with the gradings: the wedge
of a form of exterior degree `p` and total degree `g` with a form of exterior degree `q` and
total degree `h` has exterior degree `p + q` and total degree `g + h`. -/
@[stacks 0FU9 "wedge_compatible_with_gradings"]
theorem gradedDifferentialFormComponent_wedgeMul_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (p q : ℕ) {g h : G}
    {x : ⋀[A]^p (KaehlerDifferential R A)}
    (hx : x ∈ gradedDifferentialFormComponent gr p g)
    {y : ⋀[A]^q (KaehlerDifferential R A)}
    (hy : y ∈ gradedDifferentialFormComponent gr q h) :
    exteriorPower.wedgeMul p q x y ∈
      gradedDifferentialFormComponent gr (p + q) (g + h) := by
  classical
  rw [gradedDifferentialFormComponent] at hx hy
  refine Submodule.span_induction₂
    (p := fun x y _ _ => exteriorPower.wedgeMul p q x y ∈
      gradedDifferentialFormComponent gr (p + q) (g + h))
    (s := {x | ∃ (degree : Fin (p + 1) → G) (a : ∀ i, gr (degree i)),
      g = ∑ i, degree i ∧ x = (a 0 : A) • exteriorPower.ιMulti A p
        (fun i ↦ KaehlerDifferential.D R A (a i.succ : A))})
    (t := {x | ∃ (degree : Fin (q + 1) → G) (b : ∀ i, gr (degree i)),
      h = ∑ i, degree i ∧ x = (b 0 : A) • exteriorPower.ιMulti A q
        (fun i ↦ KaehlerDifferential.D R A (b i.succ : A))})
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨degree, a, hdeg, rfl⟩ ⟨degree', b, hdeg', rfl⟩
    let degreeOut : Fin (p + q + 1) → G :=
      Fin.cons (degree 0 + degree' 0)
        (Fin.append (fun i : Fin p ↦ degree i.succ) (fun i : Fin q ↦ degree' i.succ))
    let coeffOut : Fin (p + q + 1) → A :=
      Fin.cons ((a 0 : A) * (b 0 : A))
        (Fin.append (fun i : Fin p ↦ (a i.succ : A)) (fun i : Fin q ↦ (b i.succ : A)))
    have hcoeff : ∀ i, coeffOut i ∈ gr (degreeOut i) := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa [coeffOut, degreeOut] using
          SetLike.GradedMul.mul_mem (a 0).property (b 0).property
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro k; simp [coeffOut, degreeOut]
        · intro k; simp [coeffOut, degreeOut]
    let coeffDegree : ∀ i, gr (degreeOut i) := fun i ↦ ⟨coeffOut i, hcoeff i⟩
    have hsum : (∑ i, degreeOut i) =
        (∑ i : Fin (p + 1), degree i) + (∑ i : Fin (q + 1), degree' i) := by
      dsimp [degreeOut]
      rw [Fin.sum_univ_succ, Fin.sum_univ_add, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.append_left, Fin.append_right]
      abel
    have hform :
        (↑((a 0 : A) • exteriorPower.ιMulti A p
            (fun i ↦ KaehlerDifferential.D R A (a i.succ : A))) :
          ExteriorAlgebra A (KaehlerDifferential R A)) *
          ↑((b 0 : A) • exteriorPower.ιMulti A q
            (fun i ↦ KaehlerDifferential.D R A (b i.succ : A))) =
        ↑((coeffDegree 0 : A) • exteriorPower.ιMulti A (p + q)
          (fun i ↦ KaehlerDifferential.D R A (coeffDegree i.succ : A))) := by
      simp only [Submodule.coe_smul, exteriorPower.ιMulti_apply_coe]
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, ExteriorAlgebra.ιMulti_mul_ιMulti]
      have hvec :
          Fin.append (fun i : Fin p ↦ KaehlerDifferential.D R A (a i.succ : A))
            (fun i : Fin q ↦ KaehlerDifferential.D R A (b i.succ : A)) =
          (fun i : Fin (p + q) ↦ KaehlerDifferential.D R A (coeffDegree i.succ : A)) := by
        funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [coeffDegree, coeffOut, Fin.append]
        · intro j; simp [coeffDegree, coeffOut, Fin.append]
      rw [hvec]
      simp [coeffDegree, coeffOut]
    have hwedge : exteriorPower.wedgeMul p q
        ((a 0 : A) • exteriorPower.ιMulti A p
          (fun i ↦ KaehlerDifferential.D R A (a i.succ : A)))
        ((b 0 : A) • exteriorPower.ιMulti A q
          (fun i ↦ KaehlerDifferential.D R A (b i.succ : A))) =
        (coeffDegree 0 : A) • exteriorPower.ιMulti A (p + q)
          (fun i ↦ KaehlerDifferential.D R A (coeffDegree i.succ : A)) :=
      Subtype.ext hform
    rw [hwedge]
    exact homogeneousDifferentialForm_mem_gradedDifferentialFormComponent
      gr (p + q) degreeOut coeffDegree (g + h) (by rw [hdeg, hdeg', hsum])
  · intro y hy
    simp
  · intro x hx
    simp
  · intro x₁ x₂ y hx₁ hx₂ hy h₁ h₂
    simpa [map_add] using add_mem h₁ h₂
  · intro x y₁ y₂ hx hy₁ hy₂ h₁ h₂
    simpa [map_add] using add_mem h₁ h₂
  · intro c x y hx hy hxy
    rw [show exteriorPower.wedgeMul p q (c • x) y =
      c • exteriorPower.wedgeMul p q x y from Subtype.ext (by simp)]
    exact Submodule.smul_mem _ c hxy
  · intro c x y hx hy hxy
    rw [show exteriorPower.wedgeMul p q x (c • y) =
      c • exteriorPower.wedgeMul p q x y from Subtype.ext (by simp)]
    exact Submodule.smul_mem _ c hxy

private theorem gradedDifferentialFormComponent_mul_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (p q : ℕ) {g h : G}
    {x : ⋀[A]^p (KaehlerDifferential R A)}
    (hx : x ∈ gradedDifferentialFormComponent gr p g)
    {y : ⋀[A]^q (KaehlerDifferential R A)}
    (hy : y ∈ gradedDifferentialFormComponent gr q h) :
    (x : ExteriorAlgebra A (KaehlerDifferential R A)) * y ∈
      homogeneousExteriorAlgebraComponent gr (g + h) := by
  exact coe_mem_homogeneousExteriorAlgebraComponent gr (p + q)
    (gradedDifferentialFormComponent_wedgeMul_mem gr p q hx hy)

private theorem homogeneousExteriorAlgebraComponent_mul_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    {g h : G} {x y : ExteriorAlgebra A (KaehlerDifferential R A)}
    (hx : x ∈ homogeneousExteriorAlgebraComponent gr g)
    (hy : y ∈ homogeneousExteriorAlgebraComponent gr h) :
    x * y ∈ homogeneousExteriorAlgebraComponent gr (g + h) := by
  classical
  unfold homogeneousExteriorAlgebraComponent at hx hy ⊢
  refine Submodule.iSup_induction
    (fun p => (gradedDifferentialFormComponent gr p g).map
      ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype.restrictScalars R))
    (motive := fun x => ∀ y ∈
      ⨆ q : ℕ, (gradedDifferentialFormComponent gr q h).map
        ((ExteriorAlgebra.exteriorPower A q (KaehlerDifferential R A)).subtype.restrictScalars R),
      x * y ∈ ⨆ n : ℕ,
        (gradedDifferentialFormComponent gr n (g + h)).map
          ((ExteriorAlgebra.exteriorPower A n (KaehlerDifferential R A)).subtype.restrictScalars R))
    hx ?_ ?_ ?_ y hy
  · intro p x hx y hy
    rcases Submodule.mem_map.mp hx with ⟨x', hx', rfl⟩
    refine Submodule.iSup_induction
      (fun q => (gradedDifferentialFormComponent gr q h).map
        ((ExteriorAlgebra.exteriorPower A q (KaehlerDifferential R A)).subtype.restrictScalars R))
      (motive := fun y => ((x' : ExteriorAlgebra A (KaehlerDifferential R A)) * y) ∈
        ⨆ n : ℕ,
          (gradedDifferentialFormComponent gr n (g + h)).map
            ((ExteriorAlgebra.exteriorPower A n
              (KaehlerDifferential R A)).subtype.restrictScalars R))
      hy ?_ ?_ ?_
    · intro q y hy
      rcases Submodule.mem_map.mp hy with ⟨y', hy', rfl⟩
      simpa [homogeneousExteriorAlgebraComponent] using
        (gradedDifferentialFormComponent_mul_mem gr p q hx' hy')
    · simp
    · intro y₁ y₂ hy₁ hy₂
      simpa [mul_add] using add_mem hy₁ hy₂
  · intro y hy
    simp
  · intro x₁ x₂ hx₁ hx₂ y hy
    simpa [add_mul] using add_mem (hx₁ y hy) (hx₂ y hy)

/-- The degree-zero monomial `a • ιMulti 0 _` is the scalar `a`. -/
private theorem ιMulti_zero_eq_one
    {R : Type v} {A : Type w} [CommRing R] [CommRing A] [Algebra R A] (a : A) :
    exteriorPower.ιMulti A 0 (fun _ : Fin 0 => KaehlerDifferential.D R A a) =
      (1 : ⋀[A]^0 (KaehlerDifferential R A)) :=
  Subtype.ext (by simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply])

private theorem one_mem_homogeneousExteriorAlgebraComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr] :
    (1 : ExteriorAlgebra A (KaehlerDifferential R A)) ∈
      homogeneousExteriorAlgebraComponent gr 0 := by
  simpa using coe_mem_homogeneousExteriorAlgebraComponent gr 0
    (x := 1) (by
      simpa only [one_smul, ιMulti_zero_eq_one] using
        homogeneousDifferentialForm_mem_gradedDifferentialFormComponent
          gr 0 (fun _ => 0) (fun _ => ⟨1, SetLike.one_mem_graded gr⟩) 0 (by simp))

private instance homogeneousExteriorAlgebraComponent_gradedMonoid
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr] :
    SetLike.GradedMonoid (homogeneousExteriorAlgebraComponent gr) where
  one_mem := one_mem_homogeneousExteriorAlgebraComponent gr
  mul_mem := by
    intro i j x y hx hy
    exact homogeneousExteriorAlgebraComponent_mul_mem gr hx hy

private theorem algebraMap_mem_homogeneousExteriorAlgebraComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A)
    {g : G} {a : A} (ha : a ∈ gr g) :
    algebraMap A (ExteriorAlgebra A (KaehlerDifferential R A)) a ∈
      homogeneousExteriorAlgebraComponent gr g := by
  have hmem := coe_mem_homogeneousExteriorAlgebraComponent gr 0
    (x := (a : A) • (1 : ⋀[A]^0 (KaehlerDifferential R A))) (by
      simpa only [ιMulti_zero_eq_one] using
        homogeneousDifferentialForm_mem_gradedDifferentialFormComponent
          gr 0 (fun _ : Fin (0 + 1) => g) (fun _ => ⟨a, ha⟩) g (by simp))
  simpa [Algebra.algebraMap_eq_smul_one] using hmem

private noncomputable def homogeneousScalarMap
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) (g : G) :
    gr g →ₗ[R] homogeneousExteriorAlgebraComponent gr g where
  toFun a := ⟨algebraMap A (ExteriorAlgebra A (KaehlerDifferential R A)) a,
    algebraMap_mem_homogeneousExteriorAlgebraComponent gr a.property⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by
    simp only [Submodule.coe_smul, Algebra.smul_def, map_mul]
    rw [← IsScalarTower.algebraMap_apply R A (ExteriorAlgebra A (KaehlerDifferential R A)) r]
    simp)

private noncomputable def gradedScalarMap
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    A →ₗ[R] ⨁ g, homogeneousExteriorAlgebraComponent gr g := by
  let _ := gradedAlgebra_of_isInternal gr hgr
  exact
    (DirectSum.toModule R G _ fun g =>
      (DirectSum.lof R G (fun g => homogeneousExteriorAlgebraComponent gr g) g).comp
        (homogeneousScalarMap gr g)).comp (DirectSum.decomposeLinearEquiv gr).toLinearMap

private theorem gradedScalarMap_of_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) {g : G} {a : A} (ha : a ∈ gr g) :
    gradedScalarMap gr hgr a = DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) g
      ⟨algebraMap A (ExteriorAlgebra A (KaehlerDifferential R A)) a,
        algebraMap_mem_homogeneousExteriorAlgebraComponent gr ha⟩ := by
  let _ := gradedAlgebra_of_isInternal gr hgr
  change DirectSum.toModule R G _ _ (DirectSum.decomposeLinearEquiv gr a) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe gr g ⟨a, ha⟩]
  rw [DirectSum.toModule_lof]
  simp [homogeneousScalarMap, DirectSum.lof_eq_of]

private theorem gradedScalarMap_mul
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) (a b : A) :
    gradedScalarMap gr hgr (a * b) = gradedScalarMap gr hgr a * gradedScalarMap gr hgr b := by
  classical
  let _ := gradedAlgebra_of_isInternal gr hgr
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  induction a using DirectSum.Decomposition.inductionOn gr with
  | zero => simp [gradedScalarMap]
  | @homogeneous i x =>
    induction b using DirectSum.Decomposition.inductionOn gr with
    | zero => simp [gradedScalarMap]
    | @homogeneous j y =>
      rw [gradedScalarMap_of_mem gr hgr (SetLike.GradedMul.mul_mem x.property y.property),
        gradedScalarMap_of_mem gr hgr x.property, gradedScalarMap_of_mem gr hgr y.property,
        DirectSum.of_mul_of]
      apply congrArg (DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) (i + j))
      apply Subtype.ext
      simp [map_mul]
    | add b₁ b₂ ih₁ ih₂ =>
      rw [mul_add]
      simp only [map_add, ih₁, ih₂]
      rw [left_distrib]
  | add a₁ a₂ ih₁ ih₂ =>
    rw [add_mul]
    simp only [map_add, ih₁, ih₂]
    rw [right_distrib]

private theorem gradedScalarMap_one
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    gradedScalarMap gr hgr 1 = 1 := by
  classical
  let _ := gradedAlgebra_of_isInternal gr hgr
  rw [gradedScalarMap_of_mem gr hgr (SetLike.one_mem_graded gr)]
  rw [DirectSum.one_def]
  rfl

private noncomputable def gradedScalarRingHom
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    A →+* ⨁ g, homogeneousExteriorAlgebraComponent gr g where
  toFun := gradedScalarMap gr hgr
  map_zero' := map_zero (gradedScalarMap gr hgr)
  map_add' := map_add (gradedScalarMap gr hgr)
  map_one' := gradedScalarMap_one gr hgr
  map_mul' := gradedScalarMap_mul gr hgr

private noncomputable def gradedScalarAlgHom
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    A →ₐ[R] ⨁ g, homogeneousExteriorAlgebraComponent gr g where
  toRingHom := gradedScalarRingHom gr hgr
  commutes' r := by
    change gradedScalarMap gr hgr (algebraMap R A r) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, gradedScalarMap_one gr hgr,
      Algebra.algebraMap_eq_smul_one]

private theorem gradedScalarMap_commutes
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr)
    [Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g)] (a : A)
    (x : ⨁ g, homogeneousExteriorAlgebraComponent gr g) :
    gradedScalarMap gr hgr a * x = x * gradedScalarMap gr hgr a := by
  classical
  let _ := gradedAlgebra_of_isInternal gr hgr
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  induction x using DirectSum.induction_on with
  | zero => simp
  | @of j y =>
    induction a using DirectSum.Decomposition.inductionOn gr with
    | zero => simp [gradedScalarMap]
    | @homogeneous i a =>
      rw [gradedScalarMap_of_mem gr hgr a.property,
        DirectSum.of_mul_of, DirectSum.of_mul_of]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      exact Sigma.subtype_ext (add_comm i j) (Algebra.commutes _ _)
    | add a₁ a₂ ih₁ ih₂ =>
      rw [map_add, add_mul, mul_add, ih₁, ih₂]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [mul_add, add_mul, ih₁, ih₂]

private noncomputable def homogeneousDifferentialMap
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr] (g : G) :
    gr g →ₗ[R] homogeneousExteriorAlgebraComponent gr g where
  toFun a := ⟨(ExteriorAlgebra.exteriorPower A 1 (KaehlerDifferential R A)).subtype
      ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm
        (KaehlerDifferential.D R A (a : A))), by
    exact coe_mem_homogeneousExteriorAlgebraComponent gr 1
      ((mem_gradedDifferentialComponent_iff_symm_mem gr g _).mp
        (derivation_mem_gradedDifferentialComponent gr a.property))⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    let e := (exteriorPower.oneEquiv A (KaehlerDifferential R A)).restrictScalars R
    have hD : KaehlerDifferential.D R A (r • (x : A)) =
        r • KaehlerDifferential.D R A (x : A) :=
      (KaehlerDifferential.D R A).toLinearMap.map_smul r (x : A)
    let f := (ExteriorAlgebra.exteriorPower A 1 (KaehlerDifferential R A)).subtype.restrictScalars R
    change f ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm
        (KaehlerDifferential.D R A (r • (x : A)))) =
      r • f ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm
        (KaehlerDifferential.D R A (x : A)))
    rw [← f.map_smul, hD]
    change f (e.symm (r • KaehlerDifferential.D R A (x : A))) =
      f (r • e.symm (KaehlerDifferential.D R A (x : A)))
    rw [e.symm.map_smul]

private theorem homogeneousExteriorAlgebraComponent_smul_mem
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    {i g : G} {a : A} (ha : a ∈ gr i)
    {x : ExteriorAlgebra A (KaehlerDifferential R A)}
    (hx : x ∈ homogeneousExteriorAlgebraComponent gr g) :
    a • x ∈ homogeneousExteriorAlgebraComponent gr (i + g) := by
  classical
  unfold homogeneousExteriorAlgebraComponent at hx ⊢
  refine Submodule.iSup_induction
    (fun p => (gradedDifferentialFormComponent gr p g).map
      ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype.restrictScalars R))
    (motive := fun y => a • y ∈
      ⨆ p : ℕ, (gradedDifferentialFormComponent gr p (i + g)).map
        ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype.restrictScalars R))
    hx ?_ ?_ ?_
  · intro p y hy
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    simpa [homogeneousExteriorAlgebraComponent] using coe_mem_homogeneousExteriorAlgebraComponent
      gr p (gradedDifferentialFormComponent_smul_mem gr ha hz)
  · simp
  · intro x y hx' hy'
    simpa [smul_add] using add_mem hx' hy'

private theorem homogeneousExteriorAlgebraComponent_gradedSMul
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr] :
    SetLike.GradedSMul gr (homogeneousExteriorAlgebraComponent gr) where
  smul_mem := by
    intro i j a x ha hx
    exact homogeneousExteriorAlgebraComponent_smul_mem gr ha hx

@[instance_reducible]
private noncomputable def homogeneousExteriorAlgebraDirectSumModule
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    Module A (⨁ (g : G), homogeneousExteriorAlgebraComponent gr g) := by
  classical
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  let smulAction : SMul A (⨁ (g : G), homogeneousExteriorAlgebraComponent gr g) :=
    ⟨fun a x => gradedScalarMap gr hgr a * x⟩
  let _ : SMul A (⨁ (g : G), homogeneousExteriorAlgebraComponent gr g) := smulAction
  exact @Module.ofMinimalAxioms A (⨁ (g : G), homogeneousExteriorAlgebraComponent gr g)
    _ _ smulAction
    (smul_add := by
      intro a x y
      change gradedScalarMap gr hgr a * (x + y) = _
      exact mul_add (gradedScalarMap gr hgr a) x y)
    (add_smul := by
      intro a b x
      change gradedScalarMap gr hgr (a + b) * x = _
      rw [map_add]
      exact add_mul (gradedScalarMap gr hgr a) (gradedScalarMap gr hgr b) x)
    (mul_smul := by
      intro a b x
      change gradedScalarMap gr hgr (a * b) * x = _
      rw [gradedScalarMap_mul gr hgr]
      exact mul_assoc (gradedScalarMap gr hgr a) (gradedScalarMap gr hgr b) x)
    (one_smul := by
      intro x
      change gradedScalarMap gr hgr 1 * x = _
      rw [gradedScalarMap_one gr hgr]
      exact one_mul x)

@[instance_reducible]
private noncomputable def homogeneousExteriorAlgebraDirectSumAlgebra
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) := by
  classical
  let _ := gradedAlgebra_of_isInternal gr hgr
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumModule gr hgr
  refine Algebra.ofModule ?_ ?_
  · intro a x y
    calc
      (a • x) * y = (gradedScalarMap gr hgr a * x) * y := rfl
      _ = gradedScalarMap gr hgr a * (x * y) := mul_assoc _ _ _
      _ = a • (x * y) := rfl
  · intro a x y
    calc
      x * (a • y) = x * (gradedScalarMap gr hgr a * y) := rfl
      _ = (x * gradedScalarMap gr hgr a) * y := (mul_assoc _ _ _).symm
      _ = (gradedScalarMap gr hgr a * x) * y := by
        rw [← gradedScalarMap_commutes gr hgr a x]
      _ = gradedScalarMap gr hgr a * (x * y) := mul_assoc _ _ _
      _ = a • (x * y) := rfl

private theorem homogeneousExteriorAlgebraDirectSumAlgebra_algebraMap
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) (a : A) :
    (letI : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      homogeneousExteriorAlgebraDirectSumModule gr hgr
     letI : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
     algebraMap A (⨁ g, homogeneousExteriorAlgebraComponent gr g) a =
       gradedScalarMap gr hgr a) := by
  let _ := gradedAlgebra_of_isInternal gr hgr
  let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumModule gr hgr
  let _ : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
  rw [Algebra.algebraMap_eq_smul_one]
  change gradedScalarMap gr hgr a * 1 = gradedScalarMap gr hgr a
  exact mul_one _

private noncomputable def homogeneousExteriorAlgebraIotaComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) (g : G) :
    gradedDifferentialComponent gr g →ₗ[R]
      homogeneousExteriorAlgebraComponent gr g where
  toFun x := ⟨ExteriorAlgebra.ι A (x : KaehlerDifferential R A),
    exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent gr x.property⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

private noncomputable def homogeneousExteriorAlgebraIotaDirectSumMap
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) :
    (⨁ g, gradedDifferentialComponent gr g) →ₗ[R]
      ⨁ g, homogeneousExteriorAlgebraComponent gr g :=
  DirectSum.toModule R G _ fun g =>
    (DirectSum.lof R G (fun g => homogeneousExteriorAlgebraComponent gr g) g).comp
      (homogeneousExteriorAlgebraIotaComponent gr g)

private theorem homogeneousExteriorAlgebraIotaDirectSumMap_of
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) {g : G}
    (x : gradedDifferentialComponent gr g) :
    homogeneousExteriorAlgebraIotaDirectSumMap gr (DirectSum.of _ g x) =
      DirectSum.of _ g
        ⟨ExteriorAlgebra.ι A (x : KaehlerDifferential R A),
          exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent gr x.property⟩ := by
  change DirectSum.toModule R G _ _
    (DirectSum.lof R G
      (fun g => gradedDifferentialComponent gr g)
      g x) = _
  rw [DirectSum.toModule_lof]
  rfl

end KaehlerDifferential
