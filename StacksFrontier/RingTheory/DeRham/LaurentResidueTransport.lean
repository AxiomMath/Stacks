module

public import StacksFrontier.RingTheory.DeRham.LaurentResidueTrivialization
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The residue computation of a Laurent algebra, transported along an isomorphism

Let `R` be a commutative ring, `A` an `R`-algebra and `B` an `A`-algebra, and suppose given an
isomorphism of `A`-algebras `e : A[T;T⁻¹] ≃ₐ[A] B`. The local computation of the residue of
`A[T;T⁻¹]` (Stacks 0FUF) transports to `B`: the grading of `B` is the image of the weight grading
of `A[T;T⁻¹]`, the coordinate is the unit `e T`, and the relative forms of `B` over `R` of weight
zero are, uniquely, `ω' + dlog (e T) ∧ ω` with `ω'` and `ω` pulled back from `A`.

## Main definitions

* `KaehlerDifferential.mapₛₗ`: the map `Ω[A₁⁄R] →ₛₗ Ω[A₂⁄R]` of an `R`-algebra homomorphism
  `φ : A₁ →ₐ[R] A₂`, semilinear over `φ`.
* `KaehlerDifferential.formsₛₗ`: its exterior powers `⋀^p Ω[A₁⁄R] →ₛₗ ⋀^p Ω[A₂⁄R]`, taken over
  `A₁` on the source and over `A₂` on the target.
* `LaurentDeRham.transportGrading`: the grading of `B` transported from the weight grading of
  `A[T;T⁻¹]`.
* `LaurentDeRham.transportDlog`: the logarithmic differential `dlog (e T)` of the coordinate.
* `LaurentDeRham.transportResidue`, `LaurentDeRham.transportResidueRight`: the residue on `B`,
  against a left and against a right wedge with `dlog`.
* `LaurentDeRham.FormsModel`: groups of forms identified with the Kähler forms of `A` and of
  `B`, with the residue `LaurentDeRham.FormsModel.res`.

## Main results

* `KaehlerDifferential.formsₛₗ_smul_ιMulti_D`, `formsₛₗ_wedgeMul`, `formsₛₗ_wedgeLeft`,
  `formsₛₗ_deRhamDifferential`: the transport is computed on the generators
  `a₀ · d a₁ ∧ ⋯ ∧ d a_p`, is multiplicative, and commutes with the de Rham differential.
* `KaehlerDifferential.formsₛₗ_mem_gradedDifferentialFormComponent`: a homomorphism respecting
  gradings respects the graded components of Stacks 0FU9.
* `LaurentDeRham.exists_of_mem_transport_zero` and `LaurentDeRham.exists_of_mem_transport_succ`:
  **every weight-zero form on `B` is `ω' + dlog (e T) ∧ ω`** with `ω'`, `ω` pulled back from `A`.
* `LaurentDeRham.eq_zero_of_transport_eq_zero` and
  `LaurentDeRham.injective_transport_mapExteriorPower`: **that decomposition is unique**.
* `LaurentDeRham.transport_mapExteriorPower_mem` and `LaurentDeRham.transport_wedgeLeft_mem`:
  the two kinds of summands have weight zero.
* `LaurentDeRham.deRhamDifferential_transport`: `d (ω' + dlog (e T) ∧ ω) = dω' − dlog (e T) ∧ dω`.
* `LaurentDeRham.FormsModel.exists_decomposition`, `LaurentDeRham.FormsModel.res_decomposition`,
  `LaurentDeRham.FormsModel.res_dF`: the decomposition of weight-zero forms, the residue formula
  and the compatibility of the residue with the differentials, in a forms model.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
-/

open KaehlerDifferential LaurentPolynomial

@[expose] public section

noncomputable section

universe u

namespace KaehlerDifferential

section Transport

variable {R A₁ A₂ A₃ : Type u} [CommRing R] [CommRing A₁] [CommRing A₂] [CommRing A₃]
  [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- **The Kähler differentials along an algebra homomorphism, as a semilinear map**:
`Ω[A₁⁄R] →ₛₗ[φ] Ω[A₂⁄R]`, carrying `d a` to `d (φ a)`. This is `KaehlerDifferential.map` with
the `A₁`-algebra structure of `A₂` supplied by `φ`. -/
@[ega "0 20.5.2"]
def mapₛₗ (φ : A₁ →ₐ[R] A₂) : Ω[A₁⁄R] →ₛₗ[(φ : A₁ →+* A₂)] Ω[A₂⁄R] :=
  letI : Algebra A₁ A₂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R A₁ A₂ := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  { toFun := map R R A₁ A₂
    map_add' := map_add _
    map_smul' := fun a x => by
      rw [(map R R A₁ A₂).map_smul a x, ← algebraMap_smul A₂ a (map R R A₁ A₂ x)]
      rfl }

/-- The map `KaehlerDifferential.mapₛₗ φ` sends `d a` to `d (φ a)`. -/
@[simp]
theorem mapₛₗ_D (φ : A₁ →ₐ[R] A₂) (a : A₁) : mapₛₗ φ (D R A₁ a) = D R A₂ (φ a) :=
  let : Algebra A₁ A₂ := φ.toRingHom.toAlgebra
  have : IsScalarTower R A₁ A₂ := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  map_D R R A₁ A₂ a

omit [Algebra R A₂] in
/-- Two semilinear maps out of `Ω[A₁⁄R]` agreeing on the differentials are equal. -/
theorem semilinear_ext_D {P : Type*} [AddCommGroup P] [Module A₂ P] {φ : A₁ →+* A₂}
    {f g : Ω[A₁⁄R] →ₛₗ[φ] P} (h : ∀ a, f (D R A₁ a) = g (D R A₁ a)) : f = g := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ (⊤ : Submodule A₁ Ω[A₁⁄R]) := Submodule.mem_top
  rw [← span_range_derivation] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact h a
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul r y _ hy => rw [map_smulₛₗ, map_smulₛₗ, hy]

/-- `KaehlerDifferential.mapₛₗ` is functorial: `mapₛₗ ψ ∘ mapₛₗ φ = mapₛₗ (ψ ∘ φ)`. -/
theorem mapₛₗ_comp (φ : A₁ →ₐ[R] A₂) (ψ : A₂ →ₐ[R] A₃) (x : Ω[A₁⁄R]) :
    mapₛₗ ψ (mapₛₗ φ x) = mapₛₗ (ψ.comp φ) x := by
  have : RingHomCompTriple (φ : A₁ →+* A₂) (ψ : A₂ →+* A₃) ((ψ.comp φ : A₁ →ₐ[R] A₃) : A₁ →+* A₃) :=
    ⟨rfl⟩
  exact LinearMap.congr_fun (semilinear_ext_D (f := (mapₛₗ ψ).comp (mapₛₗ φ))
    (g := mapₛₗ (ψ.comp φ)) fun a => by rw [LinearMap.comp_apply, mapₛₗ_D, mapₛₗ_D, mapₛₗ_D]; rfl) x

/-- `KaehlerDifferential.mapₛₗ` of the identity is the identity. -/
@[simp]
theorem mapₛₗ_id (x : Ω[A₁⁄R]) : mapₛₗ (AlgHom.id R A₁) x = x :=
  LinearMap.congr_fun (semilinear_ext_D (f := mapₛₗ (AlgHom.id R A₁))
    (g := (LinearMap.id : Ω[A₁⁄R] →ₗ[A₁] Ω[A₁⁄R])) fun a => by rw [mapₛₗ_D]; rfl) x

/-- **The exterior powers of the Kähler differentials along an algebra homomorphism**,
`⋀^p_{A₁} Ω[A₁⁄R] →ₛₗ[φ] ⋀^p_{A₂} Ω[A₂⁄R]`: base change of the exterior power along `φ` applied
to `KaehlerDifferential.mapₛₗ`. -/
def formsₛₗ (φ : A₁ →ₐ[R] A₂) (p : ℕ) :
    ⋀[A₁]^p (Ω[A₁⁄R]) →ₛₗ[(φ : A₁ →+* A₂)] ⋀[A₂]^p (Ω[A₂⁄R]) :=
  ExteriorAlgebra.powMapₛₗ p (φ : A₁ →+* A₂) (mapₛₗ φ)

/-- The map `KaehlerDifferential.formsₛₗ φ p` sends `v₁ ∧ ⋯ ∧ v_p` to
`mapₛₗ φ v₁ ∧ ⋯ ∧ mapₛₗ φ v_p`. -/
@[simp]
theorem formsₛₗ_ιMulti (φ : A₁ →ₐ[R] A₂) (p : ℕ) (v : Fin p → Ω[A₁⁄R]) :
    formsₛₗ φ p (exteriorPower.ιMulti A₁ p v) =
      exteriorPower.ιMulti A₂ p fun i => mapₛₗ φ (v i) :=
  ExteriorAlgebra.powMapₛₗ_ιMulti p _ _ v

/-- The transport on a generator `a₀ · d a₁ ∧ ⋯ ∧ d a_p`. -/
theorem formsₛₗ_smul_ιMulti_D (φ : A₁ →ₐ[R] A₂) (p : ℕ) (a₀ : A₁) (a : Fin p → A₁) :
    formsₛₗ φ p (a₀ • exteriorPower.ιMulti A₁ p fun i => D R A₁ (a i)) =
      φ a₀ • exteriorPower.ιMulti A₂ p fun i => D R A₂ (φ (a i)) := by
  rw [map_smulₛₗ, formsₛₗ_ιMulti]
  simp only [mapₛₗ_D]
  rfl

/-- The transport is `R`-linear. -/
theorem formsₛₗ_smul_base (φ : A₁ →ₐ[R] A₂) (p : ℕ) (r : R) (x : ⋀[A₁]^p (Ω[A₁⁄R])) :
    formsₛₗ φ p (r • x) = r • formsₛₗ φ p x := by
  rw [← algebraMap_smul A₁ r x, map_smulₛₗ, ← algebraMap_smul A₂ r]
  exact congrArg (· • formsₛₗ φ p x) (φ.commutes r)

/-- The transport as an `R`-linear map. -/
def formsₗ (φ : A₁ →ₐ[R] A₂) (p : ℕ) : ⋀[A₁]^p (Ω[A₁⁄R]) →ₗ[R] ⋀[A₂]^p (Ω[A₂⁄R]) where
  toFun := formsₛₗ φ p
  map_add' := map_add _
  map_smul' := formsₛₗ_smul_base φ p

/-- `KaehlerDifferential.formsₗ φ p` agrees with `KaehlerDifferential.formsₛₗ φ p`. -/
@[simp]
theorem formsₗ_apply (φ : A₁ →ₐ[R] A₂) (p : ℕ) (x : ⋀[A₁]^p (Ω[A₁⁄R])) :
    formsₗ φ p x = formsₛₗ φ p x := rfl

/-- `KaehlerDifferential.formsₛₗ` is functorial:
`formsₛₗ ψ p ∘ formsₛₗ φ p = formsₛₗ (ψ ∘ φ) p`. -/
theorem formsₛₗ_comp (φ : A₁ →ₐ[R] A₂) (ψ : A₂ →ₐ[R] A₃) (p : ℕ) (x : ⋀[A₁]^p (Ω[A₁⁄R])) :
    formsₛₗ ψ p (formsₛₗ φ p x) = formsₛₗ (ψ.comp φ) p x :=
  (ExteriorAlgebra.powMapₛₗ_eq_comp p (mapₛₗ φ) (mapₛₗ ψ) (mapₛₗ (ψ.comp φ))
    (fun _ => rfl) (fun m => (mapₛₗ_comp φ ψ m).symm) x).symm

/-- `KaehlerDifferential.formsₛₗ` of the identity is the identity. -/
@[simp]
theorem formsₛₗ_id (p : ℕ) (x : ⋀[A₁]^p (Ω[A₁⁄R])) : formsₛₗ (AlgHom.id R A₁) p x = x :=
  ExteriorAlgebra.powMapₛₗ_eq_self p _ (fun _ => rfl) (fun m => mapₛₗ_id m) x

/-- For an isomorphism `e`, the map `formsₛₗ e.symm p` is a left inverse of `formsₛₗ e p`. -/
@[simp]
theorem formsₛₗ_symm_apply (e : A₁ ≃ₐ[R] A₂) (p : ℕ) (x : ⋀[A₁]^p (Ω[A₁⁄R])) :
    formsₛₗ (e.symm : A₂ →ₐ[R] A₁) p (formsₛₗ (e : A₁ →ₐ[R] A₂) p x) = x := by
  rw [formsₛₗ_comp]
  have : (e.symm : A₂ →ₐ[R] A₁).comp (e : A₁ →ₐ[R] A₂) = AlgHom.id R A₁ := by
    ext a; simp
  rw [this, formsₛₗ_id]

/-- For an isomorphism `e`, the map `formsₛₗ e.symm p` is a right inverse of `formsₛₗ e p`. -/
@[simp]
theorem formsₛₗ_apply_symm (e : A₁ ≃ₐ[R] A₂) (p : ℕ) (x : ⋀[A₂]^p (Ω[A₂⁄R])) :
    formsₛₗ (e : A₁ →ₐ[R] A₂) p (formsₛₗ (e.symm : A₂ →ₐ[R] A₁) p x) = x :=
  formsₛₗ_symm_apply e.symm p x

/-- For an isomorphism `e`, the map `formsₛₗ e p` is injective. -/
theorem formsₛₗ_injective (e : A₁ ≃ₐ[R] A₂) (p : ℕ) :
    Function.Injective (formsₛₗ (e : A₁ →ₐ[R] A₂) p) :=
  Function.LeftInverse.injective (formsₛₗ_symm_apply e p)

/-- **The transport is multiplicative.** -/
theorem formsₛₗ_wedgeMul (φ : A₁ →ₐ[R] A₂) (p q : ℕ) (x : ⋀[A₁]^p (Ω[A₁⁄R]))
    (y : ⋀[A₁]^q (Ω[A₁⁄R])) :
    formsₛₗ φ (p + q) (exteriorPower.wedgeMul p q x y) =
      exteriorPower.wedgeMul p q (formsₛₗ φ p x) (formsₛₗ φ q y) := by
  refine Subtype.ext ?_
  show ExteriorAlgebra.mapₛₗ _ (mapₛₗ φ)
      ((x : ExteriorAlgebra A₁ (Ω[A₁⁄R])) * (y : ExteriorAlgebra A₁ (Ω[A₁⁄R]))) =
    (ExteriorAlgebra.mapₛₗ _ (mapₛₗ φ) (x : ExteriorAlgebra A₁ (Ω[A₁⁄R]))) *
      (ExteriorAlgebra.mapₛₗ _ (mapₛₗ φ) (y : ExteriorAlgebra A₁ (Ω[A₁⁄R])))
  exact map_mul _ _ _

/-- **The transport commutes with wedging on the left by a one-form.** -/
theorem formsₛₗ_wedgeLeft (φ : A₁ →ₐ[R] A₂) (ξ : Ω[A₁⁄R]) (p : ℕ) (x : ⋀[A₁]^p (Ω[A₁⁄R])) :
    formsₛₗ φ (p + 1) (exteriorPower.wedgeLeft ξ p x) =
      exteriorPower.wedgeLeft (mapₛₗ φ ξ) p (formsₛₗ φ p x) := by
  refine Subtype.ext ?_
  rw [formsₛₗ, formsₛₗ, ExteriorAlgebra.powMapₛₗ_coe, exteriorPower.coe_wedgeLeft,
    exteriorPower.coe_wedgeLeft, ExteriorAlgebra.powMapₛₗ_coe, map_mul, ExteriorAlgebra.mapₛₗ_ι]

/-- **A homomorphism of graded algebras carries graded components of forms into graded
components**, the components of Stacks 0FU9. -/
theorem formsₛₗ_mem_gradedDifferentialFormComponent {G : Type*} [AddCommMonoid G]
    (φ : A₁ →ₐ[R] A₂) {gr₁ : G → Submodule R A₁} {gr₂ : G → Submodule R A₂}
    (h : ∀ g, ∀ a ∈ gr₁ g, φ a ∈ gr₂ g) {p : ℕ} {g : G} {x : ⋀[A₁]^p (Ω[A₁⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent gr₁ p g) :
    formsₛₗ φ p x ∈ gradedDifferentialFormComponent gr₂ p g := by
  have hle : gradedDifferentialFormComponent gr₁ p g ≤
      (gradedDifferentialFormComponent gr₂ p g).comap (formsₗ φ p) := by
    rw [gradedDifferentialFormComponent_le_iff]
    intro degree a hg
    rw [Submodule.mem_comap, formsₗ_apply, formsₛₗ_smul_ιMulti_D]
    exact homogeneousDifferentialForm_mem_gradedDifferentialFormComponent gr₂ p degree
      (fun i => ⟨φ (a i), h _ _ (a i).2⟩) g hg
  exact hle hx

/-- **The transport along an isomorphism commutes with the de Rham differential.** -/
theorem formsₛₗ_deRhamDifferential (e : A₁ ≃ₐ[R] A₂) (p : ℕ) (x : ⋀[A₁]^p (Ω[A₁⁄R])) :
    formsₛₗ (e : A₁ →ₐ[R] A₂) (p + 1) (deRhamDifferential (A := R) p x) =
      deRhamDifferential (A := R) p (formsₛₗ (e : A₁ →ₐ[R] A₂) p x) := by
  have key : (formsₗ (e.symm : A₂ →ₐ[R] A₁) (p + 1)).comp
      ((deRhamDifferential (A := R) (B := A₂) p).comp (formsₗ (e : A₁ →ₐ[R] A₂) p)) =
      deRhamDifferential (A := R) (B := A₁) p := by
    refine deRhamDifferential_unique p _ fun b => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, formsₗ_apply]
    rw [formsₛₗ_smul_ιMulti_D,
      deRhamDifferential_smul_ιMulti_D (A := R) p (fun i => (e : A₁ →ₐ[R] A₂) (b i)),
      formsₛₗ_ιMulti]
    refine congrArg (exteriorPower.ιMulti A₁ (p + 1)) (funext fun i => ?_)
    rw [mapₛₗ_D]
    exact congrArg (D R A₁) (e.symm_apply_apply (b i))
  have h := LinearMap.congr_fun key x
  simp only [LinearMap.coe_comp, Function.comp_apply, formsₗ_apply] at h
  rw [← h, formsₛₗ_apply_symm]

/-- The transport carries `dlog u` to `dlog` of the image unit. -/
theorem mapₛₗ_dlogUnit (φ : A₁ →ₐ[R] A₂) (w : A₁ˣ) :
    mapₛₗ φ (Stacks.LogPoles.dlogUnit R w) =
      Stacks.LogPoles.dlogUnit R (Units.map (φ : A₁ →* A₂) w) := by
  rw [Stacks.LogPoles.dlogUnit, map_smulₛₗ, mapₛₗ_D]
  rfl

/-- **A graded component of forms is stable under multiplication by elements of degree zero**,
for a multiplicative grading. -/
theorem smul_mem_gradedDifferentialFormComponent {G : Type*} [AddCommMonoid G]
    {gr : G → Submodule R A₁}
    (hmul : ∀ {i j : G} {a b : A₁}, a ∈ gr i → b ∈ gr j → a * b ∈ gr (i + j))
    {b : A₁} (hb : b ∈ gr 0) {p : ℕ} {g : G} {x : ⋀[A₁]^p (Ω[A₁⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent gr p g) :
    b • x ∈ gradedDifferentialFormComponent gr p g := by
  have hle : gradedDifferentialFormComponent gr p g ≤
      (gradedDifferentialFormComponent gr p g).comap
        ((LinearMap.lsmul A₁ (⋀[A₁]^p (Ω[A₁⁄R])) b).restrictScalars R) := by
    rw [gradedDifferentialFormComponent_le_iff]
    intro degree a hg
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_smul]
    have h0 : b * (a 0 : A₁) ∈ gr (degree 0) := by
      simpa using hmul hb (a 0).2
    exact homogeneousDifferentialForm_mem_gradedDifferentialFormComponent gr p degree
      (fun i => Fin.cases ⟨b * a 0, h0⟩ (fun j => a j.succ) i) g hg
  exact hle hx

/-- A generator of a graded component of forms, with its homogeneous elements given as a plain
family. -/
theorem smul_ιMulti_D_mem_gradedDifferentialFormComponent {G : Type*} [AddCommMonoid G]
    (gr : G → Submodule R A₁) {p : ℕ} (degree : Fin (p + 1) → G) (a : Fin (p + 1) → A₁)
    (ha : ∀ i, a i ∈ gr (degree i)) {g : G} (hg : g = ∑ i, degree i) :
    a 0 • exteriorPower.ιMulti A₁ p (fun i => D R A₁ (a i.succ)) ∈
      gradedDifferentialFormComponent gr p g :=
  homogeneousDifferentialForm_mem_gradedDifferentialFormComponent gr p degree
    (fun i => ⟨a i, ha i⟩) g hg

/-- **Wedging a graded form on the right with the differential of a homogeneous element adds the
degrees.** -/
theorem wedgeMul_ιMulti_D_mem_gradedDifferentialFormComponent {G : Type*} [AddCommMonoid G]
    {gr : G → Submodule R A₁} {p : ℕ} {i j : G} {x : ⋀[A₁]^p (Ω[A₁⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent gr p i) {b : A₁} (hb : b ∈ gr j) :
    exteriorPower.wedgeMul p 1 x (exteriorPower.ιMulti A₁ 1 fun _ => D R A₁ b) ∈
      gradedDifferentialFormComponent gr (p + 1) (i + j) := by
  have hle : gradedDifferentialFormComponent gr p i ≤
      (gradedDifferentialFormComponent gr (p + 1) (i + j)).comap
        (((exteriorPower.wedgeMul p 1).flip
          (exteriorPower.ιMulti A₁ 1 fun _ => D R A₁ b)).restrictScalars R) := by
    rw [gradedDifferentialFormComponent_le_iff]
    intro degree a hg
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
      LinearMap.map_smul₂, exteriorPower.wedgeMul_ιMulti, Fin.append_right_eq_snoc]
    have key : (Fin.snoc (fun i : Fin p => D R A₁ (a i.succ)) (D R A₁ b) : Fin (p + 1) → _) =
        fun i => D R A₁ ((Fin.snoc (fun k : Fin (p + 1) => (a k : A₁)) b : Fin (p + 2) → A₁)
          i.succ) := by
      funext k
      refine Fin.lastCases ?_ (fun l => ?_) k
      · rw [Fin.snoc_last, Fin.succ_last, Fin.snoc_last]
      · rw [Fin.snoc_castSucc, ← Fin.castSucc_fin_succ, Fin.snoc_castSucc]
    rw [key]
    have h0 : (a 0 : A₁) = (Fin.snoc (fun k : Fin (p + 1) => (a k : A₁)) b : Fin (p + 2) → A₁) 0 :=
      (Fin.snoc_castSucc (α := fun _ => A₁) (x := b) (p := fun k => (a k : A₁)) 0).symm
    rw [h0]
    refine smul_ιMulti_D_mem_gradedDifferentialFormComponent gr
      (Fin.snoc degree j) _ (fun k => ?_) ?_
    · refine Fin.lastCases ?_ (fun l => ?_) k
      · rw [Fin.snoc_last, Fin.snoc_last]; exact hb
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact (a l).2
    · rw [Fin.sum_univ_castSucc, Fin.snoc_last, hg]
      simp only [Fin.snoc_castSucc]
  exact hle hx

/-- **Wedging a generator on the right with an exact one-form.** -/
theorem wedgeMul_smul_ιMulti_D (p : ℕ) (a₀ : A₁) (v : Fin p → A₁) (w : A₁) :
    exteriorPower.wedgeMul p 1 (a₀ • exteriorPower.ιMulti A₁ p fun i => D R A₁ (v i))
        (exteriorPower.ιMulti A₁ 1 fun _ => D R A₁ w) =
      a₀ • exteriorPower.ιMulti A₁ (p + 1) fun i => D R A₁ (Fin.snoc (α := fun _ => A₁) v w i) := by
  rw [LinearMap.map_smul₂, exteriorPower.wedgeMul_ιMulti, Fin.append_right_eq_snoc]
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun l => ?_) i
  · rw [Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- A scalar multiple of a one-form, read in the first exterior power. -/
theorem smul_ιMulti_one {M : Type*} [AddCommGroup M] [Module A₁ M] (a : A₁) (ξ : M) :
    a • exteriorPower.ιMulti A₁ 1 (fun _ => ξ) = exteriorPower.ιMulti A₁ 1 fun _ => a • ξ := by
  have h : (fun _ : Fin 1 => a • ξ) = Function.update (fun _ => ξ) 0 (a • ξ) := by
    funext i
    rw [Subsingleton.elim i 0, Function.update_self]
  rw [h, AlternatingMap.map_update_smul, Function.update_eq_self]

/-- Right wedge with a one-form is left wedge up to the sign of graded commutativity. -/
theorem wedgeMul_ιMulti_one {M : Type*} [AddCommGroup M] [Module A₁ M] {p : ℕ}
    (x : ⋀[A₁]^p M) (ξ : M) :
    exteriorPower.wedgeMul p 1 x (exteriorPower.ιMulti A₁ 1 fun _ => ξ) =
      ((-1 : ℤ) ^ p) • exteriorPower.wedgeLeft ξ p x := by
  refine Subtype.ext ?_
  have h1 : ((((-1 : ℤ) ^ p) • exteriorPower.wedgeLeft ξ p x : ⋀[A₁]^(p + 1) M) :
      ExteriorAlgebra A₁ M) =
        ((-1 : ℤ) ^ p) • (exteriorPower.wedgeLeft ξ p x : ExteriorAlgebra A₁ M) :=
    rfl
  rw [exteriorPower.wedgeMul_apply_coe, exteriorPower.mul_comm_of_mem x.2
    (exteriorPower.ιMulti A₁ 1 fun _ => ξ).2, h1, exteriorPower.coe_wedgeLeft,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, mul_one, zsmul_eq_mul]
  push_cast
  rfl

/-- Left wedge with a one-form is the signed right wedge. -/
theorem neg_one_pow_smul_wedgeMul_ιMulti_one {M : Type*} [AddCommGroup M] [Module A₁ M] {p : ℕ}
    (x : ⋀[A₁]^p M) (ξ : M) :
    ((-1 : ℤ) ^ p) • exteriorPower.wedgeMul p 1 x (exteriorPower.ιMulti A₁ 1 fun _ => ξ) =
      exteriorPower.wedgeLeft ξ p x := by
  rw [wedgeMul_ιMulti_one, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- A signed right wedge with a one-form, the sign carried by the form. -/
theorem smul_zsmul_wedgeMul_ιMulti_one {M : Type*} [AddCommGroup M] [Module A₁ M] {p : ℕ}
    (x : ⋀[A₁]^p M) (ξ : M) :
    exteriorPower.wedgeMul p 1 (((-1 : ℤ) ^ p) • x) (exteriorPower.ιMulti A₁ 1 fun _ => ξ) =
      exteriorPower.wedgeLeft ξ p x := by
  rw [map_zsmul, LinearMap.smul_apply, neg_one_pow_smul_wedgeMul_ιMulti_one]

/-- Left wedge with a one-form is the signed right wedge, the sign being a scalar of the base
ring. -/
theorem neg_one_pow_smul_wedgeMul_ιMulti_one' {M : Type*} [AddCommGroup M] [Module A₁ M] {p : ℕ}
    (x : ⋀[A₁]^p M) (ξ : M) :
    ((-1 : A₁) ^ p) • exteriorPower.wedgeMul p 1 x (exteriorPower.ιMulti A₁ 1 fun _ => ξ) =
      exteriorPower.wedgeLeft ξ p x := by
  rw [← neg_one_pow_smul_wedgeMul_ιMulti_one x ξ, ← Int.cast_smul_eq_zsmul A₁]
  push_cast
  rfl

end Transport

end KaehlerDifferential

namespace LaurentDeRham

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

variable {R A B} (e : A[T;T⁻¹] ≃ₐ[A] B)

/-- The isomorphism `A[T;T⁻¹] ≃ B`, read as an isomorphism of `R`-algebras. -/
abbrev transportEquiv : A[T;T⁻¹] ≃ₐ[R] B := e.restrictScalars R

/-- **The grading of `B` transported from the weight grading of `A[T;T⁻¹]`.** -/
def transportGrading (n : ℤ) : Submodule R B :=
  (weightGrading R A n).map (transportEquiv (R := R) e).toLinearMap

/-- An element `b` of `B` has degree `n` for the transported grading if and only if `e.symm b`
has weight `n`. -/
theorem mem_transportGrading {n : ℤ} {b : B} :
    b ∈ transportGrading (R := R) e n ↔ e.symm b ∈ weightGrading R A n := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · exact fun h => ⟨e.symm b, h, by simp⟩

/-- The pullback of forms along `A → B` is the transport of the pullback along
`A → A[T;T⁻¹]`. -/
theorem formsₛₗ_mapExteriorPower (p : ℕ) (ω : ⋀[A]^p (Ω[A⁄R])) :
    formsₛₗ (transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B) p
        (mapExteriorPower R A A[T;T⁻¹] p ω) = mapExteriorPower R A B p ω := by
  have hΩ : ∀ y : Ω[A⁄R], mapₛₗ (transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B)
      (map R R A A[T;T⁻¹] y) = map R R A B y := by
    intro y
    have hy : y ∈ (⊤ : Submodule A Ω[A⁄R]) := Submodule.mem_top
    rw [← span_range_derivation] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨a, rfl⟩ := hw
        rw [map_D, map_D, mapₛₗ_D]
        congr 1
        exact e.commutes a
    | zero => rw [map_zero, map_zero, map_zero]
    | add w w' _ _ hw hw' => rw [map_add, map_add, map_add, hw, hw']
    | smul a w _ hw =>
        rw [LinearMap.map_smul (map R R A A[T;T⁻¹]), LinearMap.map_smul (map R R A B),
          ← algebraMap_smul A[T;T⁻¹] a (map R R A A[T;T⁻¹] w), map_smulₛₗ, hw,
          ← algebraMap_smul B a (map R R A B w)]
        congr 1
        exact e.commutes a
  have hx : ω ∈ (⊤ : Submodule A (⋀[A]^p (Ω[A⁄R]))) := Submodule.mem_top
  rw [← exteriorPower.ιMulti_span A p (Ω[A⁄R])] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [mapExteriorPower_ιMulti, mapExteriorPower_ιMulti, formsₛₗ_ιMulti]
      simp only [hΩ]
  | zero => rw [map_zero, map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, map_add, hy, hz]
  | smul a y _ hy =>
      rw [LinearMap.map_smul (mapExteriorPower R A A[T;T⁻¹] p),
        LinearMap.map_smul (mapExteriorPower R A B p),
        ← algebraMap_smul A[T;T⁻¹] a (mapExteriorPower R A A[T;T⁻¹] p y), map_smulₛₗ, hy,
        ← algebraMap_smul B a (mapExteriorPower R A B p y)]
      congr 1
      exact e.commutes a

/-- The transport carries the weight grading into the transported grading. -/
theorem transport_mem_transportGrading {n : ℤ} {q : A[T;T⁻¹]} (hq : q ∈ weightGrading R A n) :
    (transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B) q ∈ transportGrading (R := R) e n :=
  ⟨q, hq, rfl⟩

/-- The inverse transport carries the transported grading into the weight grading. -/
theorem transport_symm_mem_weightGrading {n : ℤ} {b : B}
    (hb : b ∈ transportGrading (R := R) e n) :
    ((transportEquiv (R := R) e).symm : B →ₐ[R] A[T;T⁻¹]) b ∈ weightGrading R A n :=
  (mem_transportGrading e).mp hb

omit [Algebra A B] [IsScalarTower R A B] in
/-- The weight grading of `A[T;T⁻¹]` is multiplicative. -/
theorem mul_mem_weightGrading {i j : ℤ} {q q' : A[T;T⁻¹]} (hq : q ∈ weightGrading R A i)
    (hq' : q' ∈ weightGrading R A j) : q * q' ∈ weightGrading R A (i + j) := by
  obtain ⟨a, rfl⟩ := exists_single_of_mem_weightGrading R A hq
  obtain ⟨a', rfl⟩ := exists_single_of_mem_weightGrading R A hq'
  rw [AddMonoidAlgebra.single_mul_single]
  exact single_mem_weightGrading R A (i + j) (a * a')

/-- **The transported grading of `B` is multiplicative.** -/
theorem mul_mem_transportGrading {i j : ℤ} {b b' : B} (hb : b ∈ transportGrading (R := R) e i)
    (hb' : b' ∈ transportGrading (R := R) e j) : b * b' ∈ transportGrading (R := R) e (i + j) := by
  rw [mem_transportGrading] at hb hb' ⊢
  rw [map_mul]
  exact mul_mem_weightGrading hb hb'

/-- The image of `A` in `B` has degree zero. -/
theorem algebraMap_mem_transportGrading (a : A) :
    algebraMap A B a ∈ transportGrading (R := R) e 0 := by
  rw [mem_transportGrading, ← e.commutes a, AlgEquiv.symm_apply_apply]
  exact C_mem_weightGrading R A a

/-- **The unit `e T` of `B`**, the coordinate. -/
def transportUnit : Bˣ := Units.map (e : A[T;T⁻¹] →* B) (weightOneUnit (1 : Aˣ))

/-- The coordinate `e T` is homogeneous of degree one for the transported grading. -/
theorem transportUnit_mem : (transportUnit e : B) ∈ transportGrading (R := R) e 1 := by
  rw [mem_transportGrading]
  show e.symm (e (weightOneUnit (1 : Aˣ) : A[T;T⁻¹])) ∈ _
  rw [AlgEquiv.symm_apply_apply]
  exact weightOneUnit_mem_weightGrading R A 1

/-- A unit of `B` homogeneous of degree one, read back on `A[T;T⁻¹]`. -/
def transportUnitSymm (v : Bˣ) : A[T;T⁻¹]ˣ := Units.map (e.symm : B →* A[T;T⁻¹]) v

/-- A unit of `B` of degree one is read back on `A[T;T⁻¹]` as a unit of weight one. -/
theorem transportUnitSymm_mem {v : Bˣ} (hv : (v : B) ∈ transportGrading (R := R) e 1) :
    (transportUnitSymm e v : A[T;T⁻¹]) ∈ weightGrading R A 1 :=
  (mem_transportGrading e).mp hv

/-- The transport of `dlog` of the unit `e.symm v` of `A[T;T⁻¹]` is `dlog v`. -/
theorem mapₛₗ_dlogUnit_transportUnitSymm (v : Bˣ) :
    mapₛₗ (transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B)
        (Stacks.LogPoles.dlogUnit R (transportUnitSymm e v)) = Stacks.LogPoles.dlogUnit R v := by
  rw [mapₛₗ_dlogUnit]
  congr 1
  ext
  exact e.apply_symm_apply (v : B)

variable (R) in
/-- A transported weight-zero form, read back on `A[T;T⁻¹]`, has weight zero. -/
theorem formsₛₗ_symm_mem_weightComponent {g : ℤ} {p : ℕ} {x : ⋀[B]^p (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) p g) :
    formsₛₗ ((transportEquiv (R := R) e).symm : B →ₐ[R] A[T;T⁻¹]) p x ∈
      weightComponent R A g p :=
  formsₛₗ_mem_gradedDifferentialFormComponent _
    (fun _ _ hb => transport_symm_mem_weightGrading e hb) hx

/-- A form of weight `g` on `A[T;T⁻¹]` transports to a form of weight `g` on `B`. -/
theorem formsₛₗ_mem_transport {g : ℤ} {p : ℕ} {x : ⋀[A[T;T⁻¹]]^p (Ω[A[T;T⁻¹]⁄R])}
    (hx : x ∈ weightComponent R A g p) :
    formsₛₗ (transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B) p x ∈
      gradedDifferentialFormComponent (transportGrading (R := R) e) p g :=
  formsₛₗ_mem_gradedDifferentialFormComponent _ (fun _ _ hq => transport_mem_transportGrading e hq)
    hx

/-- **The logarithmic differential `dlog (e T)` of the coordinate of `B`.** -/
def transportDlog : Ω[B⁄R] := Stacks.LogPoles.dlogUnit R (transportUnit e)

/-- The transport of `dlog T` is `dlog (e T)`. -/
theorem mapₛₗ_dlogT :
    mapₛₗ ((transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B)) (dlogT R A) =
      transportDlog (R := R) e := by
  rw [← dlogUnit_weightOneUnit_one, mapₛₗ_dlogUnit]
  rfl

/-- The transport of `ω' + ξ ∧ ω`, for forms `ω'` and `ω` pulled back from `A`. -/
private theorem formsₛₗ_mapExteriorPower_add_wedgeLeft (ξ : Ω[A[T;T⁻¹]⁄R]) (p : ℕ)
    (ω' : ⋀[A]^(p + 1) (Ω[A⁄R])) (ω : ⋀[A]^p (Ω[A⁄R])) :
    formsₛₗ (transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B) (p + 1)
        (mapExteriorPower R A A[T;T⁻¹] (p + 1) ω' +
          exteriorPower.wedgeLeft ξ p (mapExteriorPower R A A[T;T⁻¹] p ω)) =
      mapExteriorPower R A B (p + 1) ω' + exteriorPower.wedgeLeft
        (mapₛₗ (transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B) ξ) p
        (mapExteriorPower R A B p ω) := by
  rw [map_add, formsₛₗ_wedgeLeft, formsₛₗ_mapExteriorPower, formsₛₗ_mapExteriorPower]

/-! ### The local computation on `B` -/

/-- **A form pulled back from `A` has weight zero on `B`.** -/
theorem transport_mapExteriorPower_mem (p : ℕ) (ω : ⋀[A]^p (Ω[A⁄R])) :
    mapExteriorPower R A B p ω ∈
      gradedDifferentialFormComponent (transportGrading (R := R) e) p 0 := by
  rw [← formsₛₗ_mapExteriorPower e]
  exact formsₛₗ_mem_transport e (mapExteriorPower_mem_weightComponent R A p ω)

/-- **`dlog (e T)` wedged with a form pulled back from `A` has weight zero on `B`.** -/
theorem transport_wedgeLeft_mem (p : ℕ) (ω : ⋀[A]^p (Ω[A⁄R])) :
    exteriorPower.wedgeLeft (transportDlog (R := R) e) p (mapExteriorPower R A B p ω) ∈
      gradedDifferentialFormComponent (transportGrading (R := R) e) (p + 1) 0 := by
  rw [← formsₛₗ_mapExteriorPower e, ← mapₛₗ_dlogT e, ← formsₛₗ_wedgeLeft]
  exact formsₛₗ_mem_transport e (wedgeLeft_dlogT_mem_weightComponent R A p ω)

/-- **Every weight-zero `0`-form on `B` is pulled back from `A`.** -/
theorem exists_of_mem_transport_zero {x : ⋀[B]^0 (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) 0 0) :
    ∃ ω' : ⋀[A]^0 (Ω[A⁄R]), x = mapExteriorPower R A B 0 ω' := by
  obtain ⟨ω', hω'⟩ := exists_of_mem_weightComponent_zero R A
    (formsₛₗ_symm_mem_weightComponent R e hx)
  refine ⟨ω', ?_⟩
  rw [← formsₛₗ_mapExteriorPower e, ← hω']
  exact (formsₛₗ_apply_symm (transportEquiv (R := R) e) 0 x).symm

/-- **Every weight-zero form of positive degree on `B` is `ω' + dlog (e T) ∧ ω`** with `ω'` and
`ω` pulled back from `A`: the local computation of Stacks 0FUF, on `B`. -/
theorem exists_of_mem_transport_succ {p : ℕ} {x : ⋀[B]^(p + 1) (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) (p + 1) 0) :
    ∃ (ω' : ⋀[A]^(p + 1) (Ω[A⁄R])) (ω : ⋀[A]^p (Ω[A⁄R])),
      x = mapExteriorPower R A B (p + 1) ω' +
        exteriorPower.wedgeLeft (transportDlog (R := R) e) p (mapExteriorPower R A B p ω) := by
  obtain ⟨ω', ω, hω⟩ := exists_of_mem_weightComponent_succ R A
    (formsₛₗ_symm_mem_weightComponent R e hx)
  refine ⟨ω', ω, ?_⟩
  rw [← mapₛₗ_dlogT e, ← formsₛₗ_mapExteriorPower_add_wedgeLeft e, ← hω]
  exact (formsₛₗ_apply_symm (transportEquiv (R := R) e) (p + 1) x).symm

include e in
/-- **The pullback of forms `Ω^p_{A/R} → Ω^p_{B/R}` is injective.** -/
theorem injective_transport_mapExteriorPower (p : ℕ) :
    Function.Injective (mapExteriorPower R A B p) := by
  intro ω₁ ω₂ h
  rw [← formsₛₗ_mapExteriorPower e, ← formsₛₗ_mapExteriorPower e] at h
  exact ((pullbackRetract_mapExteriorPower R A p ω₁).symm.trans
    (congrArg (pullbackRetract R A p) (formsₛₗ_injective (transportEquiv (R := R) e) p h))).trans
    (pullbackRetract_mapExteriorPower R A p ω₂)

/-- **The decomposition `ω' + dlog (e T) ∧ ω` is unique.** -/
theorem eq_zero_of_transport_eq_zero {p : ℕ} {ω' : ⋀[A]^(p + 1) (Ω[A⁄R])}
    {ω : ⋀[A]^p (Ω[A⁄R])}
    (h : mapExteriorPower R A B (p + 1) ω' +
        exteriorPower.wedgeLeft (transportDlog (R := R) e) p (mapExteriorPower R A B p ω) = 0) :
    ω' = 0 ∧ ω = 0 := by
  rw [← mapₛₗ_dlogT e, ← formsₛₗ_mapExteriorPower_add_wedgeLeft e,
    show (0 : ⋀[B]^(p + 1) (Ω[B⁄R])) =
      formsₛₗ (transportEquiv (R := R) e : A[T;T⁻¹] →ₐ[R] B) (p + 1) 0 from (map_zero _).symm] at h
  have h' := formsₛₗ_injective (transportEquiv (R := R) e) (p + 1) h
  have hω : ω = 0 := by
    have := congrArg (residue R A p) h'
    rwa [residue_mapExteriorPower_add_wedgeLeft, map_zero] at this
  refine ⟨?_, hω⟩
  rw [hω, map_zero, map_zero, add_zero] at h'
  have := congrArg (pullbackRetract R A (p + 1)) h'
  rwa [pullbackRetract_mapExteriorPower, map_zero] at this

/-- **`dlog v` wedged with a form pulled back from `A` has weight zero on `B`**, for every unit
`v` of `B` homogeneous of degree one. -/
theorem transport_wedgeLeft_dlogUnit_mem {v : Bˣ} (hv : (v : B) ∈ transportGrading (R := R) e 1)
    (p : ℕ) (ω : ⋀[A]^p (Ω[A⁄R])) :
    exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p (mapExteriorPower R A B p ω) ∈
      gradedDifferentialFormComponent (transportGrading (R := R) e) (p + 1) 0 := by
  rw [← formsₛₗ_mapExteriorPower e, ← mapₛₗ_dlogUnit_transportUnitSymm e v, ← formsₛₗ_wedgeLeft]
  obtain ⟨a, ha⟩ := exists_weightOneUnit_eq R A (transportUnitSymm_mem e hv)
  rw [← ha]
  exact formsₛₗ_mem_transport e (wedgeLeft_dlogUnit_mem_weightComponent R A a p ω)

/-- **Every weight-zero form of positive degree on `B` is `ω' + dlog v ∧ ω`**, for every unit `v`
of `B` homogeneous of degree one. -/
theorem exists_of_mem_transport_succ_dlogUnit {v : Bˣ}
    (hv : (v : B) ∈ transportGrading (R := R) e 1) {p : ℕ} {x : ⋀[B]^(p + 1) (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) (p + 1) 0) :
    ∃ (ω' : ⋀[A]^(p + 1) (Ω[A⁄R])) (ω : ⋀[A]^p (Ω[A⁄R])),
      x = mapExteriorPower R A B (p + 1) ω' +
        exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p (mapExteriorPower R A B p ω) := by
  obtain ⟨ω', ω, hω⟩ := exists_of_mem_weightComponent_succ_dlogUnit R A
    (transportUnitSymm_mem e hv) (formsₛₗ_symm_mem_weightComponent R e hx)
  refine ⟨ω', ω, ?_⟩
  rw [← mapₛₗ_dlogUnit_transportUnitSymm e v, ← formsₛₗ_mapExteriorPower_add_wedgeLeft e, ← hω]
  exact (formsₛₗ_apply_symm (transportEquiv (R := R) e) (p + 1) x).symm

/-- **The residue does not depend on the unit**: if a form on `B` is `ω₁' + dlog v ∧ ω₁` and
`ω₂' + dlog w ∧ ω₂` for two units `v`, `w` homogeneous of degree one, then `ω₁ = ω₂`. -/
theorem eq_of_transport_dlogUnit {v w : Bˣ} (hv : (v : B) ∈ transportGrading (R := R) e 1)
    (hw : (w : B) ∈ transportGrading (R := R) e 1) {p : ℕ}
    {ω₁' ω₂' : ⋀[A]^(p + 1) (Ω[A⁄R])} {ω₁ ω₂ : ⋀[A]^p (Ω[A⁄R])}
    (h : mapExteriorPower R A B (p + 1) ω₁' +
          exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p (mapExteriorPower R A B p ω₁) =
        mapExteriorPower R A B (p + 1) ω₂' +
          exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R w) p
            (mapExteriorPower R A B p ω₂)) :
    ω₁ = ω₂ := by
  rw [← mapₛₗ_dlogUnit_transportUnitSymm e v, ← mapₛₗ_dlogUnit_transportUnitSymm e w,
    ← formsₛₗ_mapExteriorPower_add_wedgeLeft e, ← formsₛₗ_mapExteriorPower_add_wedgeLeft e] at h
  exact eq_of_mapExteriorPower_add_wedgeLeft_dlogUnit R A (transportUnitSymm_mem e hv)
    (transportUnitSymm_mem e hw) (formsₛₗ_injective (transportEquiv (R := R) e) (p + 1) h)

/-- **The decomposition `ω' + dlog v ∧ ω` is unique**, for every unit `v` homogeneous of degree
one. -/
theorem eq_zero_of_transport_dlogUnit_eq_zero {v : Bˣ}
    (hv : (v : B) ∈ transportGrading (R := R) e 1) {p : ℕ} {ω' : ⋀[A]^(p + 1) (Ω[A⁄R])}
    {ω : ⋀[A]^p (Ω[A⁄R])}
    (h : mapExteriorPower R A B (p + 1) ω' +
        exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p (mapExteriorPower R A B p ω) = 0) :
    ω' = 0 ∧ ω = 0 := by
  have hω : ω = 0 := eq_of_transport_dlogUnit e hv (transportUnit_mem e)
    (h.trans (by rw [map_zero, map_zero, map_zero, add_zero]) :
      _ = mapExteriorPower R A B (p + 1) 0 +
        exteriorPower.wedgeLeft (transportDlog (R := R) e) p (mapExteriorPower R A B p 0))
  refine ⟨?_, hω⟩
  rw [hω, map_zero, map_zero, add_zero] at h
  exact injective_transport_mapExteriorPower e (p + 1) (h.trans (map_zero _).symm)

/-- **The differential of `ω' + dlog (e T) ∧ ω` is `dω' − dlog (e T) ∧ dω`.** -/
theorem deRhamDifferential_transport (p : ℕ) (ω' : ⋀[A]^(p + 1) (Ω[A⁄R]))
    (ω : ⋀[A]^p (Ω[A⁄R])) :
    deRhamDifferential (A := R) (p + 1) (mapExteriorPower R A B (p + 1) ω' +
        exteriorPower.wedgeLeft (transportDlog (R := R) e) p (mapExteriorPower R A B p ω)) =
      mapExteriorPower R A B (p + 2) (deRhamDifferential (A := R) (p + 1) ω') +
        exteriorPower.wedgeLeft (transportDlog (R := R) e) (p + 1)
          (mapExteriorPower R A B (p + 1) (-deRhamDifferential (A := R) p ω)) := by
  rw [← mapₛₗ_dlogT e, ← formsₛₗ_mapExteriorPower_add_wedgeLeft e, ← formsₛₗ_deRhamDifferential,
    deRhamDifferential_mapExteriorPower_add_wedgeLeft, formsₛₗ_mapExteriorPower_add_wedgeLeft]

/-! ### The residue on `B` -/

/-- **The residue of a relative form on `B`**: the residue of `A[T;T⁻¹]` read through `e`. On the
weight-zero forms it sends `ω' + dlog v ∧ ω` to `ω`, for every unit `v` of degree one. -/
def transportResidue (p : ℕ) : ⋀[B]^(p + 1) (Ω[B⁄R]) →ₗ[R] ⋀[A]^p (Ω[A⁄R]) :=
  (residue R A p).comp
    (formsₗ ((transportEquiv (R := R) e).symm : B →ₐ[R] A[T;T⁻¹]) (p + 1))

/-- The inverse transport of a form pulled back from `A` to `B` is its pullback to
`A[T;T⁻¹]`. -/
theorem formsₛₗ_symm_mapExteriorPower (p : ℕ) (ω : ⋀[A]^p (Ω[A⁄R])) :
    formsₛₗ ((transportEquiv (R := R) e).symm : B →ₐ[R] A[T;T⁻¹]) p
        (mapExteriorPower R A B p ω) = mapExteriorPower R A A[T;T⁻¹] p ω := by
  rw [← formsₛₗ_mapExteriorPower e, formsₛₗ_symm_apply]

/-- **The defining formula of the residue on `B`**, for every unit `v` homogeneous of degree
one. -/
theorem transportResidue_formula {v : Bˣ} (hv : (v : B) ∈ transportGrading (R := R) e 1) (p : ℕ)
    (ω' : ⋀[A]^(p + 1) (Ω[A⁄R])) (ω : ⋀[A]^p (Ω[A⁄R])) :
    transportResidue e p (mapExteriorPower R A B (p + 1) ω' +
      exteriorPower.wedgeLeft (Stacks.LogPoles.dlogUnit R v) p (mapExteriorPower R A B p ω)) =
      ω := by
  rw [transportResidue, LinearMap.comp_apply, formsₗ_apply, map_add, formsₛₗ_wedgeLeft,
    formsₛₗ_symm_mapExteriorPower, formsₛₗ_symm_mapExteriorPower, mapₛₗ_dlogUnit]
  exact residue_mapExteriorPower_add_wedgeLeft_dlogUnit R A (transportUnitSymm_mem e hv) p ω' ω

/-- **The residue on `B` intertwines the de Rham differential with `−d`** on weight-zero
forms. -/
theorem transportResidue_deRhamDifferential (p : ℕ) {x : ⋀[B]^(p + 1) (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) (p + 1) 0) :
    transportResidue e (p + 1) (deRhamDifferential (A := R) (p + 1) x) =
      -deRhamDifferential (A := R) p (transportResidue e p x) := by
  simp only [transportResidue, LinearMap.comp_apply, formsₗ_apply]
  rw [formsₛₗ_deRhamDifferential (transportEquiv (R := R) e).symm]
  exact residue_deRhamDifferential R A p (formsₛₗ_symm_mem_weightComponent R e hx)

/-- The residue on `B` of the differential of a weight-zero `0`-form vanishes. -/
theorem transportResidue_deRhamDifferential_zero {x : ⋀[B]^0 (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) 0 0) :
    transportResidue e 0 (deRhamDifferential (A := R) 0 x) = 0 := by
  rw [transportResidue, LinearMap.comp_apply, formsₗ_apply,
    formsₛₗ_deRhamDifferential (transportEquiv (R := R) e).symm]
  exact residue_deRhamDifferential_zero R A (formsₛₗ_symm_mem_weightComponent R e hx)

/-- **The residue on `B` is linear over `A`** on weight-zero forms. -/
theorem transportResidue_smul (p : ℕ) (a : A) {x : ⋀[B]^(p + 1) (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) (p + 1) 0) :
    transportResidue e p (algebraMap A B a • x) = a • transportResidue e p x := by
  obtain ⟨ω', ω, rfl⟩ := exists_of_mem_transport_succ e hx
  have h1 : algebraMap A B a • mapExteriorPower R A B (p + 1) ω' =
      mapExteriorPower R A B (p + 1) (a • ω') := by
    rw [LinearMap.map_smul, algebraMap_smul]
  have h2 : algebraMap A B a • exteriorPower.wedgeLeft (transportDlog (R := R) e) p
      (mapExteriorPower R A B p ω) = exteriorPower.wedgeLeft (transportDlog (R := R) e) p
        (mapExteriorPower R A B p (a • ω)) := by
    rw [← LinearMap.map_smul, LinearMap.map_smul (mapExteriorPower R A B p) a ω,
      algebraMap_smul]
  rw [smul_add, h1, h2, transportDlog, transportResidue_formula e (transportUnit_mem e),
    transportResidue_formula e (transportUnit_mem e)]

/-! ### The residue against a right wedge -/

/-- **The residue of a form on `B` against a right wedge**: `π^*α + π^*β ∧ dlog v ↦ β`. It is the
residue `transportResidue`, which reads off `ω` from `ω' + dlog v ∧ ω`, up to the sign
`(-1)^p` of graded commutativity. -/
def transportResidueRight (p : ℕ) : ⋀[B]^(p + 1) (Ω[B⁄R]) →ₗ[R] ⋀[A]^p (Ω[A⁄R]) :=
  ((-1 : ℤ) ^ p) • transportResidue e p

/-- `transportResidueRight e p` is `(-1)^p` times `transportResidue e p`. -/
theorem transportResidueRight_apply (p : ℕ) (x : ⋀[B]^(p + 1) (Ω[B⁄R])) :
    transportResidueRight e p x = ((-1 : ℤ) ^ p) • transportResidue e p x :=
  rfl

/-- **The defining formula of the right-wedge residue on `B`**, for every unit `v` homogeneous of
degree one. -/
theorem transportResidueRight_formula {v : Bˣ} (hv : (v : B) ∈ transportGrading (R := R) e 1)
    (p : ℕ) (ω' : ⋀[A]^(p + 1) (Ω[A⁄R])) (ω : ⋀[A]^p (Ω[A⁄R])) :
    transportResidueRight e p (mapExteriorPower R A B (p + 1) ω' +
      exteriorPower.wedgeMul p 1 (mapExteriorPower R A B p ω)
        (exteriorPower.ιMulti B 1 fun _ => Stacks.LogPoles.dlogUnit R v)) = ω := by
  rw [wedgeMul_ιMulti_one, ← map_zsmul, ← map_zsmul, transportResidueRight_apply,
    transportResidue_formula e hv, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_smul]

/-- **The right-wedge residue on `B` commutes with the de Rham differential** on weight-zero
forms. -/
theorem transportResidueRight_deRhamDifferential (p : ℕ) {x : ⋀[B]^(p + 1) (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) (p + 1) 0) :
    transportResidueRight e (p + 1) (deRhamDifferential (A := R) (p + 1) x) =
      deRhamDifferential (A := R) p (transportResidueRight e p x) := by
  rw [transportResidueRight_apply, transportResidueRight_apply,
    transportResidue_deRhamDifferential e p hx, map_zsmul, pow_succ, mul_neg_one, neg_smul,
    smul_neg, neg_neg]

/-- The right-wedge residue on `B` of the differential of a weight-zero `0`-form vanishes. -/
theorem transportResidueRight_deRhamDifferential_zero {x : ⋀[B]^0 (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) 0 0) :
    transportResidueRight e 0 (deRhamDifferential (A := R) 0 x) = 0 := by
  rw [transportResidueRight_apply, transportResidue_deRhamDifferential_zero e hx, smul_zero]

/-- **The right-wedge residue on `B` is linear over `A`** on weight-zero forms. -/
theorem transportResidueRight_smul (p : ℕ) (a : A) {x : ⋀[B]^(p + 1) (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (transportGrading (R := R) e) (p + 1) 0) :
    transportResidueRight e p (algebraMap A B a • x) = a • transportResidueRight e p x := by
  rw [transportResidueRight_apply, transportResidueRight_apply, transportResidue_smul e p a hx,
    smul_comm]

/-! ### Models of the forms of `B` -/

universe v

variable (R A B) in
/-- **A model of the relative forms of `B` and of `A`**: abelian groups `F p` and `G p` together
with additive identifications with `⋀^p Ω[B⁄R]` and `⋀^p Ω[A⁄R]` under which a pullback map, a
product by a one-form, distinguished weight-zero subgroups and two differentials become the
corresponding algebraic operations. -/
structure FormsModel where
  /-- The isomorphism `A[T;T⁻¹] ≃ B`. -/
  equiv : A[T;T⁻¹] ≃ₐ[A] B
  /-- The forms of degree `p` on `B`. -/
  F : ℕ → Type v
  /-- The abelian group structure of `F p`. -/
  [addCommGroupF : ∀ p, AddCommGroup (F p)]
  /-- The `A`-module structure of `F p`. -/
  [moduleF : ∀ p, Module A (F p)]
  /-- The forms of degree `p` on `A`. -/
  G : ℕ → Type v
  /-- The abelian group structure of `G p`. -/
  [addCommGroupG : ∀ p, AddCommGroup (G p)]
  /-- The `A`-module structure of `G p`. -/
  [moduleG : ∀ p, Module A (G p)]
  /-- The identification of `F p` with `⋀^p Ω[B⁄R]`. -/
  ψ : ∀ p, F p ≃+ ⋀[B]^p (Ω[B⁄R])
  /-- `ψ p` is `A`-linear. -/
  ψ_smul : ∀ p (a : A) (x : F p), ψ p (a • x) = algebraMap A B a • ψ p x
  /-- The identification of `G p` with `⋀^p Ω[A⁄R]`. -/
  χ : ∀ p, G p ≃+ ⋀[A]^p (Ω[A⁄R])
  /-- `χ p` is `A`-linear. -/
  χ_smul : ∀ p (a : A) (x : G p), χ p (a • x) = a • χ p x
  /-- The pullback `G p → F p`. -/
  pull : ∀ p, G p →+ F p
  /-- Under the identifications, the pullback is `mapExteriorPower R A B p`. -/
  ψ_pull : ∀ p x, ψ p (pull p x) = mapExteriorPower R A B p (χ p x)
  /-- The product of a form by a one-form. -/
  wedge : ∀ p, F p → F 1 → F (p + 1)
  /-- Under the identifications, the product by a one-form is `exteriorPower.wedgeMul p 1`. -/
  ψ_wedge : ∀ p x y, ψ (p + 1) (wedge p x y) = exteriorPower.wedgeMul p 1 (ψ p x) (ψ 1 y)
  /-- The weight-zero forms. -/
  N : ∀ p, AddSubgroup (F p)
  /-- Under `ψ p`, the weight-zero forms are the transported weight-zero component. -/
  mem_N : ∀ p x, x ∈ N p ↔ ψ p x ∈ gradedDifferentialFormComponent
    (transportGrading (R := R) equiv) p 0
  /-- The differential of `F`. -/
  dF : ∀ p, F p → F (p + 1)
  /-- Under the identifications, `dF` is the de Rham differential of `B`. -/
  ψ_dF : ∀ p x, ψ (p + 1) (dF p x) = deRhamDifferential (A := R) p (ψ p x)
  /-- The differential of `G`. -/
  dG : ∀ p, G p → G (p + 1)
  /-- Under the identifications, `dG` is the de Rham differential of `A`. -/
  χ_dG : ∀ p x, χ (p + 1) (dG p x) = deRhamDifferential (A := R) p (χ p x)

namespace FormsModel

attribute [instance] addCommGroupF moduleF addCommGroupG moduleG

variable (M : FormsModel.{u, v} R A B)

/-- **The residue of a model**, against a right wedge: `pull α + wedge (pull β) (dlog v) ↦ β`. -/
def res (p : ℕ) (x : M.F (p + 1)) : M.G p :=
  (M.χ p).symm (transportResidueRight M.equiv p (M.ψ (p + 1) x))

/-- A one-form of `F` is `dlog v` when its identification is `dlog v`. -/
def IsDlog (θ : M.F 1) (v : Bˣ) : Prop :=
  M.ψ 1 θ = exteriorPower.ιMulti B 1 fun _ => Stacks.LogPoles.dlogUnit R v

/-- The identification `ψ` of `pull α + wedge (pull β) θ`, for `θ` equal to `dlog v`, is
`π^*α + π^*β ∧ dlog v`. -/
theorem ψ_decomposition (p : ℕ) (α : M.G (p + 1)) (β : M.G p) {θ : M.F 1} {v : Bˣ}
    (hθ : M.IsDlog θ v) :
    M.ψ (p + 1) (M.pull (p + 1) α + M.wedge p (M.pull p β) θ) =
      mapExteriorPower R A B (p + 1) (M.χ (p + 1) α) +
        exteriorPower.wedgeMul p 1 (mapExteriorPower R A B p (M.χ p β))
          (exteriorPower.ιMulti B 1 fun _ => Stacks.LogPoles.dlogUnit R v) := by
  rw [map_add, M.ψ_pull, M.ψ_wedge, M.ψ_pull, show M.ψ 1 θ = _ from hθ]

/-- **The defining formula of the residue.** -/
theorem res_decomposition (p : ℕ) (α : M.G (p + 1)) (β : M.G p) {θ : M.F 1} {v : Bˣ}
    (hθ : M.IsDlog θ v) (hv : (v : B) ∈ transportGrading (R := R) M.equiv 1) :
    M.res p (M.pull (p + 1) α + M.wedge p (M.pull p β) θ) = β := by
  rw [res, M.ψ_decomposition p α β hθ, transportResidueRight_formula M.equiv hv,
    AddEquiv.symm_apply_apply]

/-- **Decomposed forms have weight zero.** -/
theorem decomposition_mem (p : ℕ) (α : M.G (p + 1)) (β : M.G p) {θ : M.F 1} {v : Bˣ}
    (hθ : M.IsDlog θ v) (hv : (v : B) ∈ transportGrading (R := R) M.equiv 1) :
    M.pull (p + 1) α + M.wedge p (M.pull p β) θ ∈ M.N (p + 1) := by
  rw [M.mem_N, M.ψ_decomposition p α β hθ, wedgeMul_ιMulti_one]
  exact Submodule.add_mem _ (transport_mapExteriorPower_mem M.equiv (p + 1) _)
    (Submodule.smul_of_tower_mem _ _ (transport_wedgeLeft_dlogUnit_mem M.equiv hv p _))

/-- **Forms pulled back from `A` have weight zero.** -/
theorem pull_mem (p : ℕ) (α : M.G p) : M.pull p α ∈ M.N p := by
  rw [M.mem_N, M.ψ_pull]
  exact transport_mapExteriorPower_mem M.equiv p _

/-- **Every weight-zero form of positive degree is `pull α + wedge (pull β) (dlog v)`**, with `β`
its residue. -/
theorem exists_decomposition {p : ℕ} {x : M.F (p + 1)} (hx : x ∈ M.N (p + 1)) {θ : M.F 1}
    {v : Bˣ} (hθ : M.IsDlog θ v) (hv : (v : B) ∈ transportGrading (R := R) M.equiv 1) :
    ∃ α : M.G (p + 1), x = M.pull (p + 1) α + M.wedge p (M.pull p (M.res p x)) θ := by
  rw [M.mem_N] at hx
  obtain ⟨ω', ω, h⟩ := exists_of_mem_transport_succ_dlogUnit M.equiv hv hx
  refine ⟨(M.χ (p + 1)).symm ω', (M.ψ (p + 1)).injective ?_⟩
  have hres : M.res p x = (M.χ p).symm (((-1 : ℤ) ^ p) • ω) := by
    rw [res, h, ← smul_zsmul_wedgeMul_ιMulti_one, ← map_zsmul,
      transportResidueRight_formula M.equiv hv]
  rw [M.ψ_decomposition _ _ _ hθ, hres, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    map_zsmul, smul_zsmul_wedgeMul_ιMulti_one, h]

/-- **Every weight-zero form of degree zero is pulled back from `A`.** -/
theorem exists_pull_zero {x : M.F 0} (hx : x ∈ M.N 0) : ∃ α : M.G 0, x = M.pull 0 α := by
  rw [M.mem_N] at hx
  obtain ⟨ω', h⟩ := exists_of_mem_transport_zero M.equiv hx
  exact ⟨(M.χ 0).symm ω', (M.ψ 0).injective (by rw [M.ψ_pull, AddEquiv.apply_symm_apply, h])⟩

/-- **The pullback is injective.** -/
theorem pull_injective (p : ℕ) : Function.Injective (M.pull p) := by
  intro α β h
  have h' := congrArg (M.ψ p) h
  rw [M.ψ_pull, M.ψ_pull] at h'
  exact (M.χ p).injective (injective_transport_mapExteriorPower M.equiv p h')

/-- **The pullback is `A`-linear.** -/
theorem pull_smul (p : ℕ) (a : A) (α : M.G p) : M.pull p (a • α) = a • M.pull p α := by
  refine (M.ψ p).injective ?_
  rw [M.ψ_pull, M.χ_smul, M.ψ_smul, M.ψ_pull, LinearMap.map_smul, algebraMap_smul]

/-- **The pullback commutes with the differentials.** -/
theorem dF_pull (p : ℕ) (α : M.G p) : M.dF p (M.pull p α) = M.pull (p + 1) (M.dG p α) := by
  refine (M.ψ (p + 1)).injective ?_
  rw [M.ψ_dF, M.ψ_pull, M.ψ_pull, M.χ_dG, mapExteriorPower_deRhamDifferential]

/-- **The differential of `G` commutes with integer multiples.** -/
theorem dG_zsmul (p : ℕ) (n : ℤ) (α : M.G p) : M.dG p (n • α) = n • M.dG p α := by
  refine (M.χ (p + 1)).injective ?_
  rw [M.χ_dG, map_zsmul, map_zsmul, map_zsmul, M.χ_dG]

/-- **The residue is additive.** -/
theorem res_add (p : ℕ) (x y : M.F (p + 1)) : M.res p (x + y) = M.res p x + M.res p y := by
  rw [res, res, res, map_add, map_add, map_add]

/-- **The residue of zero is zero.** -/
theorem res_zero (p : ℕ) : M.res p 0 = 0 := by
  rw [res, map_zero, map_zero, map_zero]

/-- **The residue is `A`-linear on weight-zero forms.** -/
theorem res_smul (p : ℕ) (a : A) {x : M.F (p + 1)} (hx : x ∈ M.N (p + 1)) :
    M.res p (a • x) = a • M.res p x := by
  rw [M.mem_N] at hx
  refine (M.χ p).injective ?_
  rw [res, AddEquiv.apply_symm_apply, M.ψ_smul, transportResidueRight_smul M.equiv p a hx,
    M.χ_smul, res, AddEquiv.apply_symm_apply]

/-- The product of the zero form by a one-form vanishes. -/
private theorem wedge_zero_aux (p : ℕ) (θ : M.F 1) : M.wedge p 0 θ = 0 :=
  (M.ψ (p + 1)).injective (by
    rw [M.ψ_wedge, map_zero (M.ψ p), LinearMap.map_zero₂, map_zero (M.ψ (p + 1))])

/-- **The residue kills the forms pulled back from `A`.** -/
theorem res_pull (p : ℕ) (α : M.G (p + 1)) {θ : M.F 1} {v : Bˣ} (hθ : M.IsDlog θ v)
    (hv : (v : B) ∈ transportGrading (R := R) M.equiv 1) : M.res p (M.pull (p + 1) α) = 0 := by
  have h := M.res_decomposition p α 0 hθ hv
  rwa [map_zero, M.wedge_zero_aux, add_zero] at h

/-- **The residue commutes with the differentials** on weight-zero forms. -/
theorem res_dF (p : ℕ) {x : M.F (p + 1)} (hx : x ∈ M.N (p + 1)) :
    M.res (p + 1) (M.dF (p + 1) x) = M.dG p (M.res p x) := by
  rw [M.mem_N] at hx
  refine (M.χ (p + 1)).injective ?_
  rw [res, AddEquiv.apply_symm_apply, M.ψ_dF, transportResidueRight_deRhamDifferential M.equiv p hx,
    M.χ_dG, res, AddEquiv.apply_symm_apply]

/-- **The residue of the differential of a weight-zero form of degree zero vanishes.** -/
theorem res_dF_zero {x : M.F 0} (hx : x ∈ M.N 0) : M.res 0 (M.dF 0 x) = 0 := by
  rw [M.mem_N] at hx
  rw [res, M.ψ_dF, transportResidueRight_deRhamDifferential_zero M.equiv hx, map_zero]

/-- **The signed residue anticommutes with the differentials**: for a weight-zero form `x` of
degree `p + 1`, `(-1)^(p+1) res (d x) = - d ((-1)^p res x)`. -/
theorem neg_one_pow_res_dF (p : ℕ) {x : M.F (p + 1)} (hx : x ∈ M.N (p + 1)) :
    ((-1 : ℤ) ^ (p + 1)) • M.res (p + 1) (M.dF (p + 1) x) =
      -M.dG p (((-1 : ℤ) ^ p) • M.res p x) := by
  rw [M.res_dF p hx, M.dG_zsmul, pow_succ, mul_neg_one, neg_smul]

/-- The product of the zero form by a one-form vanishes. -/
theorem wedge_zero_left (p : ℕ) (θ : M.F 1) : M.wedge p 0 θ = 0 :=
  M.wedge_zero_aux p θ

/-- **A weight-zero form of positive degree with zero residue is pulled back from `A`.** -/
theorem exists_pull_of_res_eq_zero {p : ℕ} {x : M.F (p + 1)} (hx : x ∈ M.N (p + 1)) {θ : M.F 1}
    {v : Bˣ} (hθ : M.IsDlog θ v) (hv : (v : B) ∈ transportGrading (R := R) M.equiv 1)
    (h : M.res p x = 0) : ∃ α : M.G (p + 1), x = M.pull (p + 1) α := by
  obtain ⟨α, hα⟩ := M.exists_decomposition hx hθ hv
  refine ⟨α, hα.trans ?_⟩
  rw [h, map_zero, M.wedge_zero_left, add_zero]

/-- **The decomposition is unique**: two decompositions against units of degree one have the
same residue part. -/
theorem eq_of_decomposition {p : ℕ} {α α' : M.G (p + 1)} {β β' : M.G p} {θ θ' : M.F 1}
    {v v' : Bˣ} (hθ : M.IsDlog θ v) (hv : (v : B) ∈ transportGrading (R := R) M.equiv 1)
    (hθ' : M.IsDlog θ' v') (hv' : (v' : B) ∈ transportGrading (R := R) M.equiv 1)
    (h : M.pull (p + 1) α + M.wedge p (M.pull p β) θ =
      M.pull (p + 1) α' + M.wedge p (M.pull p β') θ') : β = β' := by
  rw [← M.res_decomposition p α β hθ hv, h, M.res_decomposition p α' β' hθ' hv']

end FormsModel

end LaurentDeRham

end

end
