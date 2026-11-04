module

public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum.GradedExteriorAlgebra
import all StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum.GradedExteriorAlgebra

/-!
# The direct-sum decomposition of differential forms

The map from the direct sum of the homogeneous components of `Ω_{A/R}` into the graded exterior
algebra anticommutes and squares to zero; together with the graded derivation into the direct sum
of the homogeneous components of `Ω_{A/R}`, this identifies the graded exterior algebra with the
exterior algebra of `Ω_{A/R}`, and gives the internal direct-sum decomposition of each exterior
power by total degree.

## Main results

* `KaehlerDifferential.isInternal_gradedDifferentialFormComponent`: the homogeneous components of
  the `p`-forms are an internal direct sum.
-/

@[expose] public section

namespace KaehlerDifferential

open DirectSum

universe u v w

private theorem directSum_of_subtype_add_comm
    {G : Type u} {α : Type v} [AddCommMonoid G] [DecidableEq G]
    (P : G → α → Prop) [∀ g, AddCommMonoid {x // P g x}]
    {i j : G} {x : α} (hji : P (j + i) x) (hij : P (i + j) x) :
    DirectSum.of (fun g => {x // P g x}) (j + i) ⟨x, hji⟩ =
      DirectSum.of (fun g => {x // P g x}) (i + j) ⟨x, hij⟩ :=
  DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm j i) rfl)

/-- A summand `of g ⟨x, hx⟩` of a direct sum of subtypes vanishes when `⟨x, hx⟩` does. -/
private theorem directSum_of_subtype_eq_zero
    {G : Type u} {α : Type v} [AddCommMonoid G] [DecidableEq G]
    (P : G → α → Prop) [∀ g, AddCommMonoid {x // P g x}]
    {g : G} {x : α} (hx : P g x) (h0 : (⟨x, hx⟩ : {x // P g x}) = 0) :
    DirectSum.of (fun g => {x // P g x}) g ⟨x, hx⟩ = 0 := by
  rw [h0, map_zero]

private theorem homogeneousExteriorAlgebraIotaDirectSumMap_of_anticomm
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    {i j : G}
    (x : gradedDifferentialComponent gr i)
    (y : gradedDifferentialComponent gr j) :
    homogeneousExteriorAlgebraIotaDirectSumMap gr (DirectSum.of _ i x) *
        homogeneousExteriorAlgebraIotaDirectSumMap gr (DirectSum.of _ j y) +
      homogeneousExteriorAlgebraIotaDirectSumMap gr (DirectSum.of _ j y) *
        homogeneousExteriorAlgebraIotaDirectSumMap gr (DirectSum.of _ i x) = 0 := by
  classical
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  rw [homogeneousExteriorAlgebraIotaDirectSumMap_of,
    homogeneousExteriorAlgebraIotaDirectSumMap_of,
    DirectSum.of_mul_of, DirectSum.of_mul_of]
  change DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) (i + j)
      ⟨ExteriorAlgebra.ι A (x : KaehlerDifferential R A) *
          ExteriorAlgebra.ι A (y : KaehlerDifferential R A), _⟩ +
    DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) (j + i)
      ⟨ExteriorAlgebra.ι A (y : KaehlerDifferential R A) *
          ExteriorAlgebra.ι A (x : KaehlerDifferential R A), _⟩ = 0
  have hmemXY : ExteriorAlgebra.ι A (x : KaehlerDifferential R A) *
      ExteriorAlgebra.ι A (y : KaehlerDifferential R A) ∈
      homogeneousExteriorAlgebraComponent gr (i + j) :=
    SetLike.GradedMul.mul_mem
      (exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent gr x.property)
      (exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent gr y.property)
  have hmemYX : ExteriorAlgebra.ι A (y : KaehlerDifferential R A) *
      ExteriorAlgebra.ι A (x : KaehlerDifferential R A) ∈
      homogeneousExteriorAlgebraComponent gr (j + i) :=
    SetLike.GradedMul.mul_mem
      (exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent gr y.property)
      (exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent gr x.property)
  have hmemYX' : ExteriorAlgebra.ι A (y : KaehlerDifferential R A) *
      ExteriorAlgebra.ι A (x : KaehlerDifferential R A) ∈
      homogeneousExteriorAlgebraComponent gr (i + j) := by
    simpa [add_comm] using hmemYX
  have hswap : DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) (j + i)
        ⟨ExteriorAlgebra.ι A (y : KaehlerDifferential R A) *
          ExteriorAlgebra.ι A (x : KaehlerDifferential R A), hmemYX⟩ =
        DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) (i + j)
        ⟨ExteriorAlgebra.ι A (y : KaehlerDifferential R A) *
          ExteriorAlgebra.ι A (x : KaehlerDifferential R A), hmemYX'⟩ :=
    directSum_of_subtype_add_comm
      (P := fun g z => z ∈ homogeneousExteriorAlgebraComponent gr g)
      hmemYX hmemYX'
  rw [hswap, ← map_add (DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g)
    (i + j))]
  exact directSum_of_subtype_eq_zero (fun g z => z ∈ homogeneousExteriorAlgebraComponent gr g) _
    (Subtype.ext (ExteriorAlgebra.ι_add_mul_swap _ _))

private noncomputable def homogeneousExteriorAlgebraIotaDirectSumMap_anticommBilinear
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr] :
    (⨁ g, gradedDifferentialComponent gr g) →ₗ[R]
      (⨁ g, gradedDifferentialComponent gr g) →ₗ[R]
        ⨁ g, homogeneousExteriorAlgebraComponent gr g := by
  classical
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  let F := homogeneousExteriorAlgebraIotaDirectSumMap gr
  refine LinearMap.mk₂ R (fun x y => F x * F y + F y * F x) ?_ ?_ ?_ ?_
  · intro x₁ x₂ y
    simp only [map_add, add_mul, mul_add]
    abel
  · intro r x y
    simp only [map_smul, smul_mul_assoc, mul_smul_comm]
    rw [← smul_add]
  · intro x y₁ y₂
    simp only [map_add, mul_add, add_mul]
    abel
  · intro r x y
    simp only [map_smul, smul_mul_assoc, mul_smul_comm]
    rw [← smul_add]

private theorem homogeneousExteriorAlgebraIotaDirectSumMap_anticomm
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (x y : ⨁ g,
      gradedDifferentialComponent gr g) :
    homogeneousExteriorAlgebraIotaDirectSumMap gr x *
        homogeneousExteriorAlgebraIotaDirectSumMap gr y +
      homogeneousExteriorAlgebraIotaDirectSumMap gr y *
        homogeneousExteriorAlgebraIotaDirectSumMap gr x = 0 := by
  classical
  have h : homogeneousExteriorAlgebraIotaDirectSumMap_anticommBilinear gr = 0 := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro y
    simpa [homogeneousExteriorAlgebraIotaDirectSumMap_anticommBilinear,
      LinearMap.mk₂_apply, DirectSum.lof_eq_of] using
      homogeneousExteriorAlgebraIotaDirectSumMap_of_anticomm gr x y
  exact congrArg (fun f => f x y) h

private theorem homogeneousExteriorAlgebraIotaDirectSumMap_smul
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) (a : A)
    (x : ⨁ g,
      gradedDifferentialComponent gr g) :
    (letI : Module A (⨁ g,
      gradedDifferentialComponent gr g) :=
        gradedDifferentialDirectSumModule gr hgr
     letI : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
        homogeneousExteriorAlgebraDirectSumModule gr hgr
     letI : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
        homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
     homogeneousExteriorAlgebraIotaDirectSumMap gr (a • x) =
       algebraMap A (⨁ g, homogeneousExteriorAlgebraComponent gr g) a *
         homogeneousExteriorAlgebraIotaDirectSumMap gr x) := by
  classical
  let _ := gradedAlgebra_of_isInternal gr hgr
  let _ : SetLike.GradedSMul gr
      (gradedDifferentialComponent gr) :=
    gradedDifferentialComponent_gradedSMul gr
  let _ : DirectSum.Gmodule (fun g => gr g)
      (fun g => gradedDifferentialComponent gr g) :=
    inferInstance
  let _ : Module A (⨁ g,
      gradedDifferentialComponent gr g) :=
    gradedDifferentialDirectSumModule gr hgr
  let _ : SetLike.GradedSMul gr (homogeneousExteriorAlgebraComponent gr) :=
    homogeneousExteriorAlgebraComponent_gradedSMul gr
  let _ : DirectSum.Gmodule (fun g => gr g)
      (fun g => homogeneousExteriorAlgebraComponent gr g) := inferInstance
  let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumModule gr hgr
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  let _ : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
  induction a using DirectSum.Decomposition.inductionOn gr with
  | zero => simp
  | @homogeneous i a =>
    induction x using DirectSum.induction_on with
    | zero => simp
    | @of j x =>
      change homogeneousExteriorAlgebraIotaDirectSumMap gr
          (DirectSum.decompose gr (a : A) • DirectSum.of _ j x) = _
      rw [DirectSum.decompose_coe gr a, DirectSum.Gmodule.of_smul_of,
        homogeneousExteriorAlgebraIotaDirectSumMap_of,
        homogeneousExteriorAlgebraDirectSumAlgebra_algebraMap,
        gradedScalarMap_of_mem gr hgr a.property,
        homogeneousExteriorAlgebraIotaDirectSumMap_of,
        DirectSum.of_mul_of]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      refine Sigma.subtype_ext (by rfl) ?_
      change ExteriorAlgebra.ι A ((a : A) • (x : KaehlerDifferential R A)) =
        algebraMap A (ExteriorAlgebra A (KaehlerDifferential R A)) (a : A) *
          ExteriorAlgebra.ι A (x : KaehlerDifferential R A)
      simp [Algebra.smul_def]
    | add x y ihx ihy =>
      simp only [smul_add, map_add, ihx, ihy]
      exact (mul_add _ _ _).symm
  | add a b iha ihb =>
    rw [add_smul, map_add, iha, ihb, map_add, add_mul]

private theorem homogeneousExteriorAlgebraIotaDirectSumMap_sq_zero
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (x : ⨁ g,
      gradedDifferentialComponent gr g) :
    letI : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
      SetLike.gring (homogeneousExteriorAlgebraComponent gr)
    homogeneousExteriorAlgebraIotaDirectSumMap gr x *
      homogeneousExteriorAlgebraIotaDirectSumMap gr x = 0 := by
  classical
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  induction x using DirectSum.induction_on with
  | zero => simp
  | @of i x =>
    rw [homogeneousExteriorAlgebraIotaDirectSumMap_of, DirectSum.of_mul_of]
    exact directSum_of_subtype_eq_zero (fun g z => z ∈ homogeneousExteriorAlgebraComponent gr g) _
      (Subtype.ext (ExteriorAlgebra.ι_sq_zero _))
  | add x y ihx ihy =>
    rw [map_add]
    calc
      (homogeneousExteriorAlgebraIotaDirectSumMap gr x +
          homogeneousExteriorAlgebraIotaDirectSumMap gr y) *
          (homogeneousExteriorAlgebraIotaDirectSumMap gr x +
            homogeneousExteriorAlgebraIotaDirectSumMap gr y) =
        (homogeneousExteriorAlgebraIotaDirectSumMap gr x *
            homogeneousExteriorAlgebraIotaDirectSumMap gr x +
          homogeneousExteriorAlgebraIotaDirectSumMap gr x *
            homogeneousExteriorAlgebraIotaDirectSumMap gr y) +
          (homogeneousExteriorAlgebraIotaDirectSumMap gr y *
            homogeneousExteriorAlgebraIotaDirectSumMap gr x +
          homogeneousExteriorAlgebraIotaDirectSumMap gr y *
            homogeneousExteriorAlgebraIotaDirectSumMap gr y) := by
          simp only [add_mul, mul_add]
          abel
      _ = 0 := by
        rw [ihx, ihy]
        simpa only [zero_add, add_zero] using
          homogeneousExteriorAlgebraIotaDirectSumMap_anticomm gr x y

/-- The direct sum of the homogeneous components of `Ω_{A/R}` carries a scalar tower over
`R → A`: the image of `r : R` in `A` is homogeneous of degree zero, and acts there as `r` does. -/
private lemma isScalarTower_gradedDifferentialDirectSum
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    letI := gradedAlgebra_of_isInternal gr hgr
    letI : SetLike.GradedSMul gr (gradedDifferentialComponent gr) :=
      gradedDifferentialComponent_gradedSMul gr
    letI : Module A (⨁ g, gradedDifferentialComponent gr g) :=
      gradedDifferentialDirectSumModule gr hgr
    IsScalarTower R A (⨁ g, gradedDifferentialComponent gr g) := by
  let _ : GradedAlgebra gr := gradedAlgebra_of_isInternal gr hgr
  let _ : SetLike.GradedSMul gr (gradedDifferentialComponent gr) :=
    gradedDifferentialComponent_gradedSMul gr
  let _ : DirectSum.Gmodule (fun g => gr g)
      (fun g => gradedDifferentialComponent gr g) := inferInstance
  let _ : Module A (⨁ g, gradedDifferentialComponent gr g) :=
    gradedDifferentialDirectSumModule gr hgr
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  induction x using DirectSum.induction_on with
  | zero => simp
  | @of i x =>
    have hr : algebraMap R A r ∈ gr 0 := SetLike.algebraMap_mem_graded gr r
    change DirectSum.decompose gr (algebraMap R A r) •
      DirectSum.of
        (fun g => gradedDifferentialComponent gr g)
        i x = r • DirectSum.of
          (fun g => gradedDifferentialComponent gr g)
          i x
    rw [DirectSum.decompose_coe gr ⟨algebraMap R A r, hr⟩,
      DirectSum.Gmodule.of_smul_of, ← DirectSum.of_smul]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    refine Sigma.subtype_ext ?_ ?_
    · change (0 : G) + i = i
      exact zero_add i
    · exact IsScalarTower.algebraMap_smul (R := R) (A := A)
        (M := KaehlerDifferential R A) r (x : KaehlerDifferential R A)
  | add x y ihx ihy => simp [ihx, ihy]

/-- The universal derivation of `A` over `R`, valued in the direct sum of the homogeneous
components of `Ω_{A/R}`: it sends a homogeneous element to its differential, placed in the
matching degree. -/
private noncomputable def gradedDifferentialDerivation
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    letI := gradedAlgebra_of_isInternal gr hgr
    letI : SetLike.GradedSMul gr (gradedDifferentialComponent gr) :=
      gradedDifferentialComponent_gradedSMul gr
    letI : Module A (⨁ g, gradedDifferentialComponent gr g) :=
      gradedDifferentialDirectSumModule gr hgr
    letI : IsScalarTower R A (⨁ g, gradedDifferentialComponent gr g) :=
      isScalarTower_gradedDifferentialDirectSum gr hgr
    Derivation R A (⨁ g, gradedDifferentialComponent gr g) := by
  letI := gradedAlgebra_of_isInternal gr hgr
  letI : SetLike.GradedSMul gr (gradedDifferentialComponent gr) :=
    gradedDifferentialComponent_gradedSMul gr
  letI : DirectSum.Gmodule (fun g => gr g)
      (fun g => gradedDifferentialComponent gr g) := inferInstance
  letI : Module A (⨁ g, gradedDifferentialComponent gr g) :=
    gradedDifferentialDirectSumModule gr hgr
  letI : IsScalarTower R A (⨁ g, gradedDifferentialComponent gr g) :=
    isScalarTower_gradedDifferentialDirectSum gr hgr
  refine ⟨gradedDifferentialMap gr hgr, ?_, ?_⟩
  · rw [gradedDifferentialMap_of_mem gr hgr (SetLike.one_mem_graded gr)]
    exact directSum_of_subtype_eq_zero (fun g z => z ∈ gradedDifferentialComponent gr g) _
      (Subtype.ext (Derivation.map_one_eq_zero (KaehlerDifferential.D R A)))
  · intro a b
    induction a using DirectSum.Decomposition.inductionOn gr with
    | zero => simp [gradedDifferentialMap]
    | @homogeneous i x =>
      induction b using DirectSum.Decomposition.inductionOn gr with
      | zero => simp [gradedDifferentialMap]
      | @homogeneous j y =>
        rw [gradedDifferentialMap_of_mem gr hgr
          (SetLike.GradedMul.mul_mem x.property y.property),
          gradedDifferentialMap_of_mem gr hgr x.property,
          gradedDifferentialMap_of_mem gr hgr y.property]
        change DirectSum.of
            (fun g => gradedDifferentialComponent gr g) (i + j)
            (⟨KaehlerDifferential.D R A ((x : A) * (y : A)),
              derivation_mem_gradedDifferentialComponent gr
                (SetLike.GradedMul.mul_mem x.property y.property)⟩ :
              gradedDifferentialComponent gr (i+j)) =
          DirectSum.decompose gr (x : A) • DirectSum.of
              (fun g => gradedDifferentialComponent gr g) j
              (⟨KaehlerDifferential.D R A (y : A),
                derivation_mem_gradedDifferentialComponent gr y.property⟩ :
                gradedDifferentialComponent gr j) +
            DirectSum.decompose gr (y : A) • DirectSum.of
              (fun g => gradedDifferentialComponent gr g) i
              (⟨KaehlerDifferential.D R A (x : A),
                derivation_mem_gradedDifferentialComponent gr x.property⟩ :
                gradedDifferentialComponent gr i)
        rw [DirectSum.decompose_coe gr x, DirectSum.Gmodule.of_smul_of,
          DirectSum.decompose_coe gr y, DirectSum.Gmodule.of_smul_of]
        have hleft : DirectSum.of
            (fun g => gradedDifferentialComponent gr g)
            (i +ᵥ j)
            (⟨(x : A) • KaehlerDifferential.D R A (y : A),
              gradedDifferentialComponent_smul_mem gr x.property
                (derivation_mem_gradedDifferentialComponent gr y.property)⟩ :
              gradedDifferentialComponent gr (i +ᵥ j)) =
            DirectSum.of
            (fun g => gradedDifferentialComponent gr g)
            (i + j)
            (⟨(x : A) • KaehlerDifferential.D R A (y : A),
              gradedDifferentialComponent_smul_mem gr x.property
                (derivation_mem_gradedDifferentialComponent gr y.property)⟩) :=
          rfl
        have hright_mem : (y : A) • KaehlerDifferential.D R A (x : A) ∈
            gradedDifferentialComponent gr (i + j) := by
          simpa [add_comm] using
            (gradedDifferentialComponent_smul_mem gr y.property
              (derivation_mem_gradedDifferentialComponent gr x.property))
        have hright : DirectSum.of
            (fun g => gradedDifferentialComponent gr g)
            (j +ᵥ i)
            (⟨(y : A) • KaehlerDifferential.D R A (x : A),
              gradedDifferentialComponent_smul_mem gr y.property
                (derivation_mem_gradedDifferentialComponent gr x.property)⟩ :
              gradedDifferentialComponent gr (j +ᵥ i)) =
            DirectSum.of
            (fun g => gradedDifferentialComponent gr g)
            (i + j)
            (⟨(y : A) • KaehlerDifferential.D R A (x : A), hright_mem⟩) :=
          directSum_of_subtype_add_comm
            (P := fun g z => z ∈ gradedDifferentialComponent gr g) _ hright_mem
        change DirectSum.of
            (fun g => gradedDifferentialComponent gr g)
            (i + j) _ =
          DirectSum.of
            (fun g => gradedDifferentialComponent gr g)
            (i +ᵥ j)
            (⟨(x : A) • KaehlerDifferential.D R A (y : A), _⟩) +
          DirectSum.of
            (fun g => gradedDifferentialComponent gr g)
            (j +ᵥ i)
            (⟨(y : A) • KaehlerDifferential.D R A (x : A), _⟩)
        rw [hleft, hright, ← map_add (DirectSum.of
          (fun g => gradedDifferentialComponent gr g)
          (i + j))]
        congr 1
        exact Subtype.ext (Derivation.leibniz (KaehlerDifferential.D R A) (x : A) (y : A))
      | add b₁ b₂ ih₁ ih₂ =>
        rw [mul_add, map_add (gradedDifferentialMap gr hgr), map_add, ih₁, ih₂]
        simp only [add_smul, smul_add]
        abel
    | add a₁ a₂ ih₁ ih₂ =>
      rw [add_mul, map_add (gradedDifferentialMap gr hgr), map_add, ih₁, ih₂]
      simp only [add_smul, smul_add]
      abel

/-- The direct sum of the homogeneous components of the exterior algebra of `Ω_{A/R}` carries a
scalar tower over `R → A`: the image of `r : R` in `A` is homogeneous of degree zero, and
multiplying by it there is the action of `r`. -/
private lemma isScalarTower_homogeneousExteriorAlgebraDirectSum
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) :
    letI := gradedAlgebra_of_isInternal gr hgr
    letI : SetLike.GradedSMul gr (homogeneousExteriorAlgebraComponent gr) :=
      homogeneousExteriorAlgebraComponent_gradedSMul gr
    letI : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      homogeneousExteriorAlgebraDirectSumModule gr hgr
    letI : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
      SetLike.gring (homogeneousExteriorAlgebraComponent gr)
    letI : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
    letI : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      Algebra.toModule (R := A) (A := ⨁ g, homogeneousExteriorAlgebraComponent gr g)
    IsScalarTower R A (⨁ g, homogeneousExteriorAlgebraComponent gr g) := by
  let _ : GradedAlgebra gr := gradedAlgebra_of_isInternal gr hgr
  let _ : SetLike.GradedSMul gr (homogeneousExteriorAlgebraComponent gr) :=
    homogeneousExteriorAlgebraComponent_gradedSMul gr
  let _ : DirectSum.Gmodule (fun g => gr g)
      (fun g => homogeneousExteriorAlgebraComponent gr g) := inferInstance
  let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumModule gr hgr
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  let _ : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
  let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    Algebra.toModule (R := A) (A := ⨁ g, homogeneousExteriorAlgebraComponent gr g)
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  induction x using DirectSum.induction_on with
  | zero => simp
  | @of i x =>
    have hr : algebraMap R A r ∈ gr 0 := SetLike.algebraMap_mem_graded gr r
    rw [Algebra.smul_def]
    change algebraMap A (⨁ g, homogeneousExteriorAlgebraComponent gr g)
        (algebraMap R A r) *
        DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) i x =
      r • DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) i x
    rw [homogeneousExteriorAlgebraDirectSumAlgebra_algebraMap gr hgr,
      gradedScalarMap_of_mem gr hgr hr, DirectSum.of_mul_of, ← DirectSum.of_smul]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    refine Sigma.subtype_ext (zero_add i) ?_
    change algebraMap A (ExteriorAlgebra A (KaehlerDifferential R A))
        (algebraMap R A r) * (x : ExteriorAlgebra A (KaehlerDifferential R A)) =
      r • (x : ExteriorAlgebra A (KaehlerDifferential R A))
    rw [← IsScalarTower.algebraMap_apply R A
      (ExteriorAlgebra A (KaehlerDifferential R A)) r]
    rw [← Algebra.smul_def]
  | add x y ihx ihy => simp [ihx, ihy]

/-- A homogeneous component of the `p`-forms, included into the matching homogeneous component
of the whole exterior algebra of `Ω_{A/R}`. -/
private noncomputable def gradedFormInclusion
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) (p : ℕ) (g : G) :
    gradedDifferentialFormComponent gr p g →ₗ[R]
      homogeneousExteriorAlgebraComponent gr g where
  toFun x := ⟨(ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype x,
    Submodule.mem_iSup_of_mem p <| Submodule.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

/-- Any algebra map out of the exterior algebra of `Ω_{A/R}` that sends `da` to the summand
of `homogeneousExteriorAlgebraIotaDirectSumMap` indicated by the degree of `a` carries a
homogeneous `p`-form of total degree `g` to the degree-`g` summand, namely to its image under
`gradedFormInclusion`. -/
private lemma lift_subtype_eq_of_gradedFormInclusion
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) (p : ℕ) :
    letI := gradedAlgebra_of_isInternal gr hgr
    letI : SetLike.GradedSMul gr (homogeneousExteriorAlgebraComponent gr) :=
      homogeneousExteriorAlgebraComponent_gradedSMul gr
    letI : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      homogeneousExteriorAlgebraDirectSumModule gr hgr
    letI : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
      SetLike.gring (homogeneousExteriorAlgebraComponent gr)
    letI : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
    letI : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      Algebra.toModule (R := A) (A := ⨁ g, homogeneousExteriorAlgebraComponent gr g)
    ∀ lift : ExteriorAlgebra A (KaehlerDifferential R A) →ₐ[A]
      (⨁ g, homogeneousExteriorAlgebraComponent gr g),
      (∀ a : A, lift (ExteriorAlgebra.ι A (KaehlerDifferential.D R A a)) =
        homogeneousExteriorAlgebraIotaDirectSumMap gr (gradedDifferentialMap gr hgr a)) →
      ∀ (g : G) (x : gradedDifferentialFormComponent gr p g),
        lift ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype x) =
          DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) g
            (gradedFormInclusion gr p g x) := by
  let _ : GradedAlgebra gr := gradedAlgebra_of_isInternal gr hgr
  let _ : SetLike.GradedSMul gr (homogeneousExteriorAlgebraComponent gr) :=
    homogeneousExteriorAlgebraComponent_gradedSMul gr
  let _ : DirectSum.Gmodule (fun g => gr g)
      (fun g => homogeneousExteriorAlgebraComponent gr g) := inferInstance
  let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumModule gr hgr
  let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
    SetLike.gring (homogeneousExteriorAlgebraComponent gr)
  let _ : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
  let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    Algebra.toModule (R := A) (A := ⨁ g, homogeneousExteriorAlgebraComponent gr g)
  let _ : IsScalarTower R A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
    isScalarTower_homogeneousExteriorAlgebraDirectSum gr hgr
  intro liftForms liftForms_D g x
  refine Submodule.span_induction
    (p := fun z hz =>
      liftForms
          ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype z) =
        DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) g
          (gradedFormInclusion gr p g ⟨z, hz⟩))
    ?_ ?_ ?_ ?_ x.property
  · rintro y ⟨degree, coeff, hdegree, rfl⟩
    simp only [gradedFormInclusion]
    change liftForms
        ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype
          ((coeff 0 : A) • exteriorPower.ιMulti A p
            (fun i ↦ KaehlerDifferential.D R A (coeff i.succ : A)))) = _
    simp only [map_smul, Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply, List.ofFn_comp', List.map_ofFn, Algebra.smul_def, map_mul,
      AlgHom.commutes, homogeneousExteriorAlgebraDirectSumAlgebra_algebraMap, map_list_prod,
      LinearMap.coe_mk, AddHom.coe_mk, SetLike.val_smul]
    have hterm (i : Fin p) :
        liftForms (ExteriorAlgebra.ι A
          (KaehlerDifferential.D R A (coeff i.succ : A))) =
          DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g)
            (degree i.succ)
            ⟨ExteriorAlgebra.ι A
                (KaehlerDifferential.D R A (coeff i.succ : A)),
              exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent gr
                (derivation_mem_gradedDifferentialComponent gr
                  (coeff i.succ).property)⟩ := by
      rw [liftForms_D]
      rw [gradedDifferentialMap_of_mem gr hgr (coeff i.succ).property]
      exact homogeneousExteriorAlgebraIotaDirectSumMap_of gr _
    have hlist :
        List.ofFn (fun i : Fin p => liftForms (ExteriorAlgebra.ι A
          (KaehlerDifferential.D R A (coeff i.succ : A)))) =
        List.ofFn (fun i : Fin p => DirectSum.of
          (fun g => homogeneousExteriorAlgebraComponent gr g) (degree i.succ)
          ⟨ExteriorAlgebra.ι A
              (KaehlerDifferential.D R A (coeff i.succ : A)),
            exteriorAlgebra_iota_mem_homogeneousExteriorAlgebraComponent gr
              (derivation_mem_gradedDifferentialComponent gr
                (coeff i.succ).property)⟩) := by
      congr 1
      funext i
      exact hterm i
    change gradedScalarMap gr hgr (coeff 0 : A) *
        ((List.ofFn fun i : Fin p => liftForms (ExteriorAlgebra.ι A
          (KaehlerDifferential.D R A (coeff i.succ : A)))).prod) =
      DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) g
        ⟨algebraMap A (ExteriorAlgebra A (KaehlerDifferential R A))
            (coeff 0 : A) *
          (List.ofFn fun i : Fin p => ExteriorAlgebra.ι A
            (KaehlerDifferential.D R A (coeff i.succ : A))).prod, _⟩
    rw [hlist, gradedScalarMap_of_mem gr hgr (coeff 0).property,
      DirectSum.list_prod_ofFn_of_eq_dProd]
    rw [DirectSum.of_mul_of]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    change (⟨degree 0 +
        (List.finRange p).dProdIndex (fun i => degree i.succ), _⟩ :
        Σ g, homogeneousExteriorAlgebraComponent gr g) =
      ⟨g, ⟨algebraMap A (ExteriorAlgebra A (KaehlerDifferential R A))
          (coeff 0 : A) *
        (List.ofFn fun i : Fin p => ExteriorAlgebra.ι A
          (KaehlerDifferential.D R A (coeff i.succ : A))).prod, _⟩⟩
    have hdegree' : degree 0 +
        (List.finRange p).dProdIndex (fun i => degree i.succ) = g := by
      rw [List.dProdIndex_eq_map_sum, ← List.ofFn_eq_map, List.sum_ofFn, hdegree,
        Fin.sum_univ_succ]
    refine Sigma.subtype_ext hdegree' ?_
    simp [List.ofFn_eq_map]
  · change liftForms 0 = DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g)
      g (gradedFormInclusion gr p g ⟨0, Submodule.zero_mem _⟩)
    have hz : gradedFormInclusion gr p g ⟨0, Submodule.zero_mem _⟩ = 0 := map_zero _
    rw [hz]
    simp
  · intro y z hymem hzmem hy hz
    have hyz : y + z ∈
        gradedDifferentialFormComponent
          gr p g := add_mem hymem hzmem
    change liftForms
        ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype (y + z)) =
      DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) g
        (gradedFormInclusion gr p g ⟨y + z, hyz⟩)
    calc
      _ = liftForms ((ExteriorAlgebra.exteriorPower A p
          (KaehlerDifferential R A)).subtype y) +
          liftForms ((ExteriorAlgebra.exteriorPower A p
            (KaehlerDifferential R A)).subtype z) := by simp
      _ = DirectSum.of _ g (gradedFormInclusion gr p g ⟨y, hymem⟩) +
          DirectSum.of _ g (gradedFormInclusion gr p g ⟨z, hzmem⟩) := by rw [hy, hz]
      _ = DirectSum.of _ g
          (gradedFormInclusion gr p g ⟨y, hymem⟩ +
            gradedFormInclusion gr p g ⟨z, hzmem⟩) := by
        rw [← map_add (DirectSum.of _ g)]
      _ = DirectSum.of _ g (gradedFormInclusion gr p g ⟨y + z, hyz⟩) := by
        congr 1
  · intro r y hymem hy
    have hry : r • y ∈
        gradedDifferentialFormComponent
          gr p g := Submodule.smul_mem _ r hymem
    change liftForms
        ((ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype (r • y)) =
      DirectSum.of (fun g => homogeneousExteriorAlgebraComponent gr g) g
        (gradedFormInclusion gr p g ⟨r • y, hry⟩)
    calc
      _ = r • liftForms ((ExteriorAlgebra.exteriorPower A p
          (KaehlerDifferential R A)).subtype y) :=
        LinearMap.map_smul_of_tower liftForms.toLinearMap r _
      _ = r • DirectSum.of _ g (gradedFormInclusion gr p g ⟨y, hymem⟩) := by rw [hy]
      _ = DirectSum.of _ g (r • gradedFormInclusion gr p g ⟨y, hymem⟩) := by
        rw [DirectSum.of_smul]
      _ = DirectSum.of _ g (gradedFormInclusion gr p g ⟨r • y, hry⟩) := by
        congr 1

/-- Differential forms decompose as the internal direct sum of their
homogeneous total-degree components. -/
@[stacks 0FU9 "forms_direct_sum"]
theorem isInternal_gradedDifferentialFormComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [DecidableEq G]
    [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) [SetLike.GradedMonoid gr]
    (hgr : DirectSum.IsInternal gr) (p : ℕ) :
    DirectSum.IsInternal
      (gradedDifferentialFormComponent gr p) :=
  by
    let := gradedAlgebra_of_isInternal gr hgr
    let : SetLike.GradedSMul gr (gradedDifferentialComponent gr) :=
      gradedDifferentialComponent_gradedSMul gr
    let : Module A (⨁ g, gradedDifferentialComponent gr g) :=
      gradedDifferentialDirectSumModule gr hgr
    let : IsScalarTower R A (⨁ g, gradedDifferentialComponent gr g) :=
      isScalarTower_gradedDifferentialDirectSum gr hgr
    let Dcomp : Derivation R A (⨁ g, gradedDifferentialComponent gr g) :=
      gradedDifferentialDerivation gr hgr
    let _ : SetLike.GradedSMul gr (homogeneousExteriorAlgebraComponent gr) :=
      homogeneousExteriorAlgebraComponent_gradedSMul gr
    let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      homogeneousExteriorAlgebraDirectSumModule gr hgr
    let _ : DirectSum.GRing (fun g : G => ↥(homogeneousExteriorAlgebraComponent gr g)) :=
      SetLike.gring (homogeneousExteriorAlgebraComponent gr)
    let _ : Algebra A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      homogeneousExteriorAlgebraDirectSumAlgebra gr hgr
    let _ : Module A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      Algebra.toModule (R := A) (A := ⨁ g, homogeneousExteriorAlgebraComponent gr g)
    let _ : IsScalarTower R A (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      isScalarTower_homogeneousExteriorAlgebraDirectSum gr hgr
    let f : KaehlerDifferential R A →ₗ[A] (⨁ g, homogeneousExteriorAlgebraComponent gr g) := {
      toFun := fun x => homogeneousExteriorAlgebraIotaDirectSumMap gr
        (Dcomp.liftKaehlerDifferential x)
      map_add' := by simp
      map_smul' := by
        intro a x
        change homogeneousExteriorAlgebraIotaDirectSumMap gr
            (Dcomp.liftKaehlerDifferential (a • x)) =
          a • homogeneousExteriorAlgebraIotaDirectSumMap gr (Dcomp.liftKaehlerDifferential x)
        rw [map_smul, homogeneousExteriorAlgebraIotaDirectSumMap_smul gr hgr, Algebra.smul_def] }
    have hf_sq (x : KaehlerDifferential R A) : f x * f x = 0 :=
      homogeneousExteriorAlgebraIotaDirectSumMap_sq_zero gr (Dcomp.liftKaehlerDifferential x)
    let liftForms : ExteriorAlgebra A (KaehlerDifferential R A) →ₐ[A]
        (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      ExteriorAlgebra.lift A ⟨f, hf_sq⟩
    have liftForms_D (a : A) :
        liftForms (ExteriorAlgebra.ι A (KaehlerDifferential.D R A a)) =
          homogeneousExteriorAlgebraIotaDirectSumMap gr (gradedDifferentialMap gr hgr a) := by
      change (ExteriorAlgebra.lift A ⟨f, hf_sq⟩)
        (ExteriorAlgebra.ι A (KaehlerDifferential.D R A a)) = _
      rw [ExteriorAlgebra.lift_ι_apply A f hf_sq]
      change homogeneousExteriorAlgebraIotaDirectSumMap gr
        (Dcomp.liftKaehlerDifferential (KaehlerDifferential.D R A a)) = _
      rw [Derivation.liftKaehlerDifferential_comp_D]
      rfl
    let componentMap : (⨁ g, gradedDifferentialFormComponent gr p g) →ₗ[R]
        (⨁ g, homogeneousExteriorAlgebraComponent gr g) :=
      DirectSum.lmap (gradedFormInclusion gr p)
    let extPowerInclusion : (⋀[A]^p (KaehlerDifferential R A)) →ₗ[R]
        ExteriorAlgebra A (KaehlerDifferential R A) :=
      (ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype.restrictScalars R
    have componentMap_injective : Function.Injective componentMap := by
      refine (DirectSum.lmap_injective (f := gradedFormInclusion gr p)).2 fun g x y hxy => ?_
      apply Subtype.ext
      have hval := congrArg Subtype.val hxy
      change (ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype x =
        (ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)).subtype y at hval
      exact Submodule.injective_subtype
        (ExteriorAlgebra.exteriorPower A p (KaehlerDifferential R A)) hval
    have liftForms_coe_eq_componentMap :
        (liftForms.toLinearMap.restrictScalars R).comp
          (extPowerInclusion.comp (DirectSum.coeLinearMap
            (gradedDifferentialFormComponent gr p))) = componentMap := by
      refine DirectSum.linearMap_ext _ fun g => LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, extPowerInclusion,
        DirectSum.lmap_lof, componentMap]
      exact lift_subtype_eq_of_gradedFormInclusion gr hgr p liftForms liftForms_D g x
    have forms_coe_injective : Function.Injective
        (DirectSum.coeLinearMap (gradedDifferentialFormComponent gr p)) := by
      intro x y hxy
      apply componentMap_injective
      rw [← liftForms_coe_eq_componentMap]
      simp [hxy]
    have forms_iSupIndep : iSupIndep (gradedDifferentialFormComponent gr p) := by
      apply iSupIndep_of_dfinsupp_lsum_injective
      simpa [DirectSum.coeLinearMap, DirectSum.toModule] using forms_coe_injective
    let formComponentSum : Submodule R (⋀[A]^p (KaehlerDifferential R A)) :=
      ⨆ g, gradedDifferentialFormComponent gr p g
    have formComponentSum_smul (a : A) {x : ⋀[A]^p (KaehlerDifferential R A)}
        (hx : x ∈ formComponentSum) : a • x ∈ formComponentSum := by
      induction a using DirectSum.Decomposition.inductionOn gr with
      | zero => simp [formComponentSum]
      | @homogeneous i a =>
        refine Submodule.iSup_induction (gradedDifferentialFormComponent gr p)
          (motive := fun x => (a : A) • x ∈ formComponentSum) hx ?_ ?_ ?_
        · intro g y hy
          exact Submodule.mem_iSup_of_mem (i + g)
            (gradedDifferentialFormComponent_smul_mem gr a.property hy)
        · rw [smul_zero]
          exact Submodule.zero_mem _
        · intro x y hx hy
          rw [smul_add]
          exact add_mem hx hy
      | add a b ha hb =>
        rw [add_smul]
        exact add_mem ha hb
    let homogeneousDifferentialSet : Set (KaehlerDifferential R A) :=
      Set.range fun x : Σ g, gr g => KaehlerDifferential.D R A (x.2 : A)
    have homogeneousDifferentials_span :
        Submodule.span A homogeneousDifferentialSet = ⊤ := by
      rw [← KaehlerDifferential.span_range_derivation (R := R) (S := A)]
      refine le_antisymm ?_ ?_ <;> rw [Submodule.span_le]
      · rintro _ ⟨x, rfl⟩
        exact Submodule.subset_span ⟨x.2, rfl⟩
      · rintro _ ⟨a, rfl⟩
        induction a using DirectSum.Decomposition.inductionOn gr with
        | zero => simp [homogeneousDifferentialSet]
        | @homogeneous g a => exact Submodule.subset_span ⟨⟨g, a⟩, rfl⟩
        | add a b ha hb => simpa [map_add] using add_mem ha hb
    have forms_iSup_eq_top : formComponentSum = ⊤ := by
      refine top_unique fun x _ => ?_
      have hx : x ∈ Submodule.span A (exteriorPower.ιMulti A p ''
          {v : Fin p → KaehlerDifferential R A | Set.range v ⊆ homogeneousDifferentialSet}) := by
        rw [exteriorPower.ιMulti_span_of_span (R := A) (n := p)
          (M := KaehlerDifferential R A) homogeneousDifferentials_span]
        trivial
      refine Submodule.span_induction (p := fun x _ => x ∈ formComponentSum) ?_
        (by simp [formComponentSum]) (fun _ _ _ _ hx hy => add_mem hx hy)
        (fun a _ _ hx => formComponentSum_smul a hx) hx
      rintro _ ⟨v, hv, rfl⟩
      classical
      let witness (i : Fin p) : Σ g, gr g := Classical.choose (hv (Set.mem_range_self i))
      have hwitness (i : Fin p) : KaehlerDifferential.D R A ((witness i).2 : A) = v i :=
        Classical.choose_spec (hv (Set.mem_range_self i))
      let degree : Fin (p + 1) → G := Fin.cons 0 (fun i => (witness i).1)
      let coeff : ∀ i, gr (degree i) :=
        Fin.cons ⟨1, SetLike.one_mem_graded gr⟩ (fun i => (witness i).2)
      have hgen : (1 : A) • exteriorPower.ιMulti A p
          (fun i => KaehlerDifferential.D R A ((witness i).2 : A)) ∈
          gradedDifferentialFormComponent gr p (∑ i : Fin p, (witness i).1) :=
        homogeneousDifferentialForm_mem_gradedDifferentialFormComponent
          gr p degree coeff (∑ i : Fin p, (witness i).1) (by simp [degree])
      have hvw : v = fun i => KaehlerDifferential.D R A ((witness i).2 : A) :=
        funext fun i => (hwitness i).symm
      have hmem : exteriorPower.ιMulti A p v ∈
          gradedDifferentialFormComponent gr p (∑ i : Fin p, (witness i).1) := by
        rw [hvw]
        simpa using hgen
      exact Submodule.mem_iSup_of_mem _ hmem
    exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      forms_iSupIndep forms_iSup_eq_top

end KaehlerDifferential
