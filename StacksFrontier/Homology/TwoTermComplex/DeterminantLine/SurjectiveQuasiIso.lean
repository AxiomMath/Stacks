module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.Algebra.Module.Projective.Determinant.ShortExact

/-!
# The determinant line of a two-term complex of finite projective modules

Let `R` be a commutative ring and let `K : K₁ → K₀` be a map of finite projective `R`-modules,
thought of as a complex in degrees `-1` and `0`. Its determinant line is
`det K₁ ⊗ (det K₀)⁻¹`, and `K` has *rank zero* when `K₁` and `K₀` have the same rank at every
prime, in which case the determinant line is canonically trivial and so carries a canonical
element `δ K`.

A morphism of two-term complexes that is a degreewise-surjective quasi-isomorphism induces an
isomorphism of determinant lines, built from the determinant of the short exact sequence formed
by its kernel. This isomorphism sends `δ` to `δ` when the source and target have rank zero, and
it is compatible with composition. Two degreewise-surjective quasi-isomorphisms out of one
complex that are homotopic induce the same isomorphism, the comparison being the determinant
identity `det (1 + a ∘ b) = det (1 + b ∘ a)` for the homotopy.

## Main definitions

* `TwoTermComplex.Hom`: a morphism of two-term complexes, with its induced maps
  `TwoTermComplex.Hom.hMinus` and `TwoTermComplex.Hom.hZero` on kernel and cokernel.
* `TwoTermComplex.determinantLine`, `TwoTermComplex.IsRankZero`, `TwoTermComplex.delta`: the
  determinant line, the rank-zero condition and the canonical element.
* `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso`: the isomorphism of determinant lines
  attached to a degreewise-surjective quasi-isomorphism.

## Implementation notes

A two-term complex is recorded as a bare linear map `K₁ →ₗ[R] K₀` between finite projective
modules rather than as a cochain complex, so the finiteness and projectivity hypotheses stay on
the two terms and the determinant-line construction for modules applies directly. The kernel of
a degreewise-surjective quasi-isomorphism is again a two-term complex of finite projective
modules, which is what makes the induced isomorphism available.
-/

namespace TwoTermComplex

/-! ### Two-term complexes and their determinant lines -/

section

universe u v₁ v₀ w₁ w₀

@[expose] public section

variable {R : Type u} [CommRing R]
variable {K₁ : Type v₁} {K₀ : Type v₀} {L₁ : Type w₁} {L₀ : Type w₀}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]

/-- The determinant line of a two-term finite-projective complex `K₁ → K₀`. -/
public noncomputable abbrev determinantLine (_K : K₁ →ₗ[R] K₀) :=
  ProjectiveDeterminant.module (R := R) (M := K₁) →ₗ[R]
    ProjectiveDeterminant.module (R := R) (M := K₀)

/-- A two-term complex has rank zero when its terms have the same rank at every prime. -/
public def IsRankZero (_K : K₁ →ₗ[R] K₀) : Prop :=
  ∀ p : PrimeSpectrum R, Module.rankAtStalk K₁ p = Module.rankAtStalk K₀ p

/-- The canonical element of the determinant line of a rank-zero two-term complex is the
determinant map induced by its differential. -/
public noncomputable def delta (K : K₁ →ₗ[R] K₀) (hK : IsRankZero K) :
    determinantLine K :=
  ProjectiveDeterminant.map hK K

/-- A morphism between two-term complexes. -/
public structure Hom (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) where
  /-- The map in degree `-1`. -/
  neg : K₁ →ₗ[R] L₁
  /-- The map in degree `0`. -/
  zero : K₀ →ₗ[R] L₀
  /-- The square with the two differentials commutes. -/
  comm : zero.comp K = L.comp neg

namespace Hom

variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀} (a : Hom K L)

/-- The map induced by a morphism of two-term complexes on degree `-1` cohomology. -/
public def hMinus : LinearMap.ker K →ₗ[R] LinearMap.ker L :=
  (a.neg.domRestrict (LinearMap.ker K)).codRestrict (LinearMap.ker L) fun x => by
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun a.comm x
    simp only [LinearMap.comp_apply] at h
    change L (a.neg (x : K₁)) = 0
    rw [← h]
    simp

/-- The map induced by a morphism of two-term complexes on degree `0` cohomology. -/
public def hZero : (K₀ ⧸ K.range) →ₗ[R] (L₀ ⧸ L.range) :=
  K.range.mapQ L.range a.zero <| by
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_comap]
    exact ⟨a.neg x, (LinearMap.congr_fun a.comm x).symm⟩

/-- A morphism of two-term complexes is a quasi-isomorphism when its maps on the two
cohomology modules are bijective. -/
public def IsQuasiIso : Prop :=
  Function.Bijective a.hMinus ∧ Function.Bijective a.hZero

/-- A morphism of two-term complexes is degreewise surjective when both of its component maps
are surjective. -/
public def IsDegreewiseSurjective : Prop :=
  Function.Surjective a.neg ∧ Function.Surjective a.zero

/-- The differential on the kernel complex of a morphism of two-term complexes. -/
public def kernelDifferential : LinearMap.ker a.neg →ₗ[R] LinearMap.ker a.zero :=
  (K.domRestrict (LinearMap.ker a.neg)).codRestrict (LinearMap.ker a.zero) fun x => by
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun a.comm x
    simp only [LinearMap.comp_apply] at h
    change a.zero (K (x : K₁)) = 0
    rw [h]
    simp

end Hom

/-- The kernel of a surjection from a finite module to a finite projective module is finite. -/
public theorem kernel_finite {M : Type*} {N : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Finite R (LinearMap.ker f) := by
  apply Module.Finite.of_fg
  let : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  exact Module.FinitePresentation.fg_ker f hf

/-- The kernel of a surjection onto a projective module is projective when its source is
projective. -/
public theorem kernel_projective {M : Type*} {N : Type*}
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let p : M →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - s.comp f) fun x => by
      rw [LinearMap.mem_ker]
      have hsx := LinearMap.congr_fun hs (f x)
      simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub,
        sub_eq_zero] using hsx.symm
  apply Module.Projective.of_split (LinearMap.ker f).subtype p
  ext x
  simp [p]

/-- The canonical identification between the rank-stratum determinant module and its
annihilator description in the exterior algebra. -/
public noncomputable def determinantAnnihilatorEquiv {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ProjectiveDeterminant.module (R := R) (M := M) ≃ₗ[R]
      ↥(⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))) :=
  LinearEquiv.ofEq _ _ (ProjectiveDeterminant.determinant_submodule_eq_annihilator R M)

/-- The canonical determinant equivalence of the short exact sequence associated to a
surjective map of finite projective modules. -/
public noncomputable def kernelDeterminantEquiv {M : Type*} {N : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)] :
    TensorProduct R
        (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
        (ProjectiveDeterminant.module (R := R) (M := N)) ≃ₗ[R]
      ProjectiveDeterminant.module (R := R) (M := M) :=
  (TensorProduct.congr determinantAnnihilatorEquiv determinantAnnihilatorEquiv).trans <|
    (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
      (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
        f.exact_subtype_ker_map hf).val |>.trans determinantAnnihilatorEquiv.symm

/-- The data characterized by the determinant diagram of a degreewise-surjective
quasi-isomorphism. The uniqueness field records the canonicity of the equivalence. -/
public structure SurjectiveQuasiIsoDeterminantData
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : Hom K L)
    (ha : a.IsDegreewiseSurjective)
    [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
    [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)] where
  /-- The kernel complex has rank zero. -/
  kernelRankZero : IsRankZero a.kernelDifferential
  /-- The kernel complex is acyclic. -/
  kernelAcyclic : Function.Bijective a.kernelDifferential
  /-- The induced equivalence of determinant lines. -/
  equiv : determinantLine K ≃ₗ[R] determinantLine L
  /-- The defining commutative determinant diagram, evaluated on pure tensors. -/
  compatibility : ∀ (φ : determinantLine K)
      (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (y : ProjectiveDeterminant.module (R := R) (M := L₁)),
    kernelDeterminantEquiv a.zero ha.2
        (delta a.kernelDifferential kernelRankZero x ⊗ₜ[R] equiv φ y) =
      φ (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y))
  /-- The defining compatibility uniquely determines the equivalence. -/
  unique : ∀ e : determinantLine K ≃ₗ[R] determinantLine L,
    (∀ (φ : determinantLine K)
        (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
        (y : ProjectiveDeterminant.module (R := R) (M := L₁)),
      kernelDeterminantEquiv a.zero ha.2
          (delta a.kernelDifferential kernelRankZero x ⊗ₜ[R] e φ y) =
        φ (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y))) → e = equiv

/-- A degreewise-surjective quasi-isomorphism of two-term finite-projective complexes induces
the canonical equivalence of their determinant lines, characterized by compatibility with the
canonical trivialization of its acyclic kernel complex. -/
public noncomputable def determinantEquivOfSurjectiveQuasiIso
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : Hom K L)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    SurjectiveQuasiIsoDeterminantData K L a ha := by
  letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  have hd : Function.Bijective a.kernelDifferential := by
    constructor
    · intro x y hxy
      have hKxy : K (x : K₁) = K (y : K₁) := congrArg Subtype.val hxy
      let z' : LinearMap.ker K := ⟨x - y, by
        rw [LinearMap.mem_ker]
        simp only [map_sub]
        exact sub_eq_zero.mpr hKxy⟩
      have hminus : a.hMinus z' = 0 := by
        apply Subtype.ext
        change a.neg (x - y) = 0
        rw [map_sub, x.property, y.property, sub_self]
      exact Subtype.ext <| sub_eq_zero.mp <| congrArg Subtype.val
        (hqa.1.1 (show a.hMinus z' = a.hMinus 0 by simpa using hminus))
    · intro z
      have hzq : a.hZero (Submodule.Quotient.mk z.1) = 0 := by
        change Submodule.Quotient.mk (a.zero z.1) = 0
        rw [z.property]
        rfl
      have hzK : Submodule.Quotient.mk z.1 = (0 : K₀ ⧸ K.range) :=
        hqa.2.1 (hzq.trans (map_zero a.hZero).symm)
      rw [Submodule.Quotient.mk_eq_zero] at hzK
      obtain ⟨x, hx⟩ := hzK
      have hL : L (a.neg x) = 0 := by
        rw [← LinearMap.comp_apply, ← a.comm, LinearMap.comp_apply, hx]
        exact z.property
      obtain ⟨k, hk⟩ := hqa.1.2 ⟨a.neg x, hL⟩
      refine ⟨⟨x - k, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, map_sub]
        have hkval : a.neg (k : K₁) = a.neg x := congrArg Subtype.val hk
        rw [hkval, sub_self]
      · apply Subtype.ext
        change K (x - (k : K₁)) = z
        rw [map_sub, hx]
        exact sub_eq_self.mpr k.property
  let de : LinearMap.ker a.neg ≃ₗ[R] LinearMap.ker a.zero :=
    LinearEquiv.ofBijective a.kernelDifferential hd
  have hr : IsRankZero a.kernelDifferential := fun p =>
    congrFun (Module.rankAtStalk_eq_of_equiv de) p
  let ddet : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg) ≃ₗ[R]
      ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero) :=
    ProjectiveDeterminant.mapEquiv de
  let kn := kernelDeterminantEquiv a.neg ha.1
  let kz := kernelDeterminantEquiv a.zero ha.2
  letI : Module.Invertible R
      (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)) :=
    ProjectiveDeterminant.invertible
  let tensorEquiv :=
    (Module.Invertible.rTensorEquiv
      (ProjectiveDeterminant.module (R := R) (M := L₁))
      (ProjectiveDeterminant.module (R := R) (M := L₀))
      ((TensorProduct.comm R
          (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
          (Module.Dual R
            (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)))).trans
        (Module.Invertible.linearEquiv R
          (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))))).trans
      (LinearEquiv.arrowCongr
        (TensorProduct.comm R
          (ProjectiveDeterminant.module (R := R) (M := L₁))
          (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)))
        ((TensorProduct.comm R
          (ProjectiveDeterminant.module (R := R) (M := L₀))
          (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))).trans
          (TensorProduct.congr ddet (LinearEquiv.refl R _))))
  let diagramEquiv : determinantLine K ≃ₗ[R]
      ((TensorProduct R
          (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
          (ProjectiveDeterminant.module (R := R) (M := L₁))) →ₗ[R]
        (TensorProduct R
          (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero))
          (ProjectiveDeterminant.module (R := R) (M := L₀)))) :=
    LinearEquiv.arrowCongr kn.symm kz.symm
  let resultEquiv : determinantLine K ≃ₗ[R] determinantLine L :=
    diagramEquiv.trans tensorEquiv.symm
  have tensorEquiv_apply (ψ : determinantLine L)
      (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (y : ProjectiveDeterminant.module (R := R) (M := L₁)) :
      tensorEquiv ψ (x ⊗ₜ[R] y) = ddet x ⊗ₜ[R] ψ y := by
    simp only [tensorEquiv, LinearEquiv.trans_apply, LinearEquiv.arrowCongr_apply]
    change (TensorProduct.congr ddet (LinearEquiv.refl R _))
      ((TensorProduct.comm R _ _) (ψ y ⊗ₜ[R] x)) = _
    rw [TensorProduct.comm_tmul, TensorProduct.congr_tmul]
    rfl
  refine
    { kernelRankZero := hr
      kernelAcyclic := hd
      equiv := resultEquiv
      compatibility := ?_
      unique := ?_ }
  · intro φ x y
    change kz (ddet x ⊗ₜ[R] resultEquiv φ y) = φ (kn (x ⊗ₜ[R] y))
    rw [← tensorEquiv_apply]
    rw [show tensorEquiv (resultEquiv φ) = diagramEquiv φ by
      simp [resultEquiv]]
    simp [diagramEquiv]
  · intro e he
    apply LinearEquiv.ext
    intro φ
    apply tensorEquiv.injective
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        apply kz.injective
        rw [tensorEquiv_apply, tensorEquiv_apply]
        have he' := he φ x y
        change kz (ddet x ⊗ₜ[R] e φ y) = φ (kn (x ⊗ₜ[R] y)) at he'
        rw [he']
        rw [← tensorEquiv_apply]
        rw [show tensorEquiv (resultEquiv φ) = diagramEquiv φ by
          simp [resultEquiv]]
        simp [diagramEquiv]
    | add x y hx hy =>
        simp only [map_add]
        rw [hx, hy]

end

end

end TwoTermComplex
