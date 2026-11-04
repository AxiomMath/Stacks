module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMaps
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.FunnyMapNaturality
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap

/-!
# Naturality of the maps of Remark 0FL9

Let `P` be a square presentation `B = A[x_1, …, x_n]/(f_1, …, f_n)` which is a relative global
complete intersection, and `P'` one of `B'` over `A'`, for a commutative square of rings
`A → A'`, `B → B'`. A morphism of presentations `Φ : P → P'` over the square which carries the
relations of `P` to those of `P'` and induces an isomorphism `B' ⊗_B Ω_{P/A} ⊗ B ≅ Ω_{P'/A'} ⊗ B'`
is a morphism of the diagrams of Remark 0FL9 to which Lemma 0H9F applies. This file draws the
consequence: the maps of Remark 0FL9 (`Stacks.DeRham.presentationFunnyMap`, and their versions
with values in `det(NL)`, `Stacks.DeRham.presentationDetNLMap`) commute with the maps on forms
and, on the determinant, with the base change map `det(NL_{B/A}) → det(NL_{B'/A'})` of
Discriminants, Section 0FKB (`NaiveCotangent.detNLMap`).

## Main definitions

* `Stacks.DeRham.kaehlerMapₛₗ`, `Stacks.DeRham.formsBaseChangeMapₛₗ`: the maps
  `Ω[B⁄ℤ] → Ω[B'⁄ℤ]` and `B ⊗[A] Ω[A⁄ℤ] → B' ⊗[A'] Ω[A'⁄ℤ]`, semilinear along `B → B'`.
* `Stacks.DeRham.cotangentMapₛₗ`, `cotangentSpaceMapₛₗ`, `polynomialFormsMapₛₗ`,
  `cokernelMapₛₗ`: the components of the morphism of diagrams of Remark 0FL9 induced by `Φ`.
* `Stacks.DeRham.topDualMap`: the semilinear map of duals of top exterior powers attached to
  bases.

## Main results

* `Stacks.DeRham.presentationDetNLEquiv_map`: the identifications of the determinant lines of
  `P` and `P'` with `det(NL)` intertwine the map of determinant lines with
  `NaiveCotangent.detNLMap`.
* `Stacks.DeRham.funnyMapOfEquiv_naturality`: Lemma 0H9F read through identifications of the
  cokernels.
* `Stacks.DeRham.presentationFunnyMap_naturality` and
  `Stacks.DeRham.presentationDetNLMap_naturality`: **Lemma 0H9F for the maps of Remark 0FL9**.

## Implementation notes

The maps between the two sides are semilinear along `B → B'`, and the exterior powers of semilinear
maps are `ExteriorAlgebra.powMapₛₗ`. The statements are stated through generic lemmas over abstract
modules (`twoTermDeterminantEquivDeterminantLine_baseChange`, `funnyMapOfEquiv_naturality`,
`lTensor_map_eq_map_lTensor`) and instantiated once: unifying the concrete instances of the modules
of a presentation is expensive, and a single instantiation keeps it to one check.

## References

* [Stacks Project, Tag 0FL9](https://stacks.math.columbia.edu/tag/0FL9)
* [Stacks Project, Tag 0H9F](https://stacks.math.columbia.edu/tag/0H9F)
* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Stacks.DeRham

namespace CotangentDiagram

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin n)) [P.IsRelativeGlobalCompleteIntersection]

/-- The inclusion `B ⊗[A] Ω[A⁄ℤ] → B ⊗[A[x]] Ω[A[x]⁄ℤ]` of the diagram of Remark 0FL9 on a pure
tensor. -/
theorem cotangentDiagram_i_tmul (b : B) (ω : Ω[A⁄ℤ]) :
    (cotangentDiagram P).i (b ⊗ₜ ω) =
      b ⊗ₜ KaehlerDifferential.map ℤ ℤ A P.toExtension.Ring ω := by
  show ((KaehlerDifferential.mapBaseChange ℤ A P.toExtension.Ring).baseChange B)
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A P.toExtension.Ring B B Ω[A⁄ℤ]).symm
      (b ⊗ₜ ω)) = _
  simp [KaehlerDifferential.mapBaseChange_tmul]

/-- The projection of the diagram of Remark 0FL9 is the base change of
`Ω[A[x]⁄ℤ] → Ω[A[x]⁄A]`. -/
theorem cotangentDiagram_π :
    (cotangentDiagram P).π =
      (KaehlerDifferential.map ℤ A P.toExtension.Ring P.toExtension.Ring).baseChange B :=
  rfl

/-- The projection `B ⊗[A[x]] Ω[A[x]⁄ℤ] → B ⊗[A[x]] Ω[A[x]⁄A]` of the diagram of Remark 0FL9 on
a pure tensor. -/
theorem cotangentDiagram_π_tmul (b : B) (ω : Ω[P.toExtension.Ring⁄ℤ]) :
    (cotangentDiagram P).π (b ⊗ₜ ω) =
      b ⊗ₜ KaehlerDifferential.map ℤ A P.toExtension.Ring P.toExtension.Ring ω :=
  rfl

/-- The conormal map of the diagram of Remark 0FL9 sends the class of `x ∈ I` to `1 ⊗ d x`. -/
theorem cotangentDiagram_d_mk (x : P.toExtension.ker) :
    (cotangentDiagram P).d (Algebra.Extension.Cotangent.mk x) =
      (1 : B) ⊗ₜ KaehlerDifferential.D ℤ P.toExtension.Ring (x : P.toExtension.Ring) :=
  ConormalSeq.conormalMap_toCotangent ℤ P.toExtension.algebraMap_surjective x

/-- The identification of the cokernel of the conormal map with `Ω[B⁄ℤ]` is induced by
`B ⊗[A[x]] Ω[A[x]⁄ℤ] → Ω[B⁄ℤ]`. -/
theorem cotangentDiagram_quotientEquiv_mk (x : B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]) :
    (cotangentDiagram P).quotientEquiv (Submodule.Quotient.mk x) =
      KaehlerDifferential.mapBaseChange ℤ P.toExtension.Ring B x :=
  rfl

/-- The maps of Remark 0FL9 are the maps of Tag 0FL8 of the diagram of the presentation, read
through the identification of the cokernel of its conormal map with `Ω[B⁄ℤ]`. -/
theorem presentationFunnyMap_eq_funnyMap (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationFunnyMap P p η =
      funnyMap n (cotangentDiagram P).i (cotangentDiagram P).π (cotangentDiagram P).d
        P.toExtension.cotangentComplex (cotangentDiagram P).hi (cotangentDiagram P).hexact
        (cotangentDiagram P).hπ (cotangentDiagram P).hsquare (cotangentDiagram P).hzero
        (cotangentDiagram P).hneg p
        (exteriorPower.map p (cotangentDiagram P).quotientEquiv.symm.toLinearMap η) :=
  rfl

end CotangentDiagram

/-- Exterior powers of semilinear maps commute with exterior powers of identifications: if
`k ∘ e₁ = e₂ ∘ c` then `⋀ᵖe₂⁻¹ ∘ ⋀ᵖk = ⋀ᵖc ∘ ⋀ᵖe₁⁻¹`. -/
theorem exteriorPower_map_symm_powMapₛₗ {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]
    {σ : R₁ →+* R₂} {Q₁ H₁ : Type*} [AddCommGroup Q₁] [Module R₁ Q₁] [AddCommGroup H₁]
    [Module R₁ H₁] {Q₂ H₂ : Type*} [AddCommGroup Q₂] [Module R₂ Q₂] [AddCommGroup H₂]
    [Module R₂ H₂] (e₁ : Q₁ ≃ₗ[R₁] H₁) (e₂ : Q₂ ≃ₗ[R₂] H₂) (c : Q₁ →ₛₗ[σ] Q₂)
    (k : H₁ →ₛₗ[σ] H₂) (h : ∀ w, e₂.symm (k (e₁ w)) = c w) (p : ℕ) (η : ⋀[R₁]^p H₁) :
    exteriorPower.map p e₂.symm.toLinearMap (ExteriorAlgebra.powMapₛₗ p σ k η) =
      ExteriorAlgebra.powMapₛₗ p σ c (exteriorPower.map p e₁.symm.toLinearMap η) := by
  have H := ExteriorAlgebra.powMapₛₗ_ext (n := p) (φ := σ)
    (f := (exteriorPower.map p e₂.symm.toLinearMap).comp (ExteriorAlgebra.powMapₛₗ p σ k))
    (g := (ExteriorAlgebra.powMapₛₗ p σ c).comp (exteriorPower.map p e₁.symm.toLinearMap))
    (fun v => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ExteriorAlgebra.powMapₛₗ_ιMulti,
        exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
        ExteriorAlgebra.powMapₛₗ_ιMulti]
      congr 1
      funext i
      rw [Function.comp_apply, Function.comp_apply, ← h, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])
  exact LinearMap.congr_fun H η

/-! ### Semilinear maps attached to a square of rings -/

section Semilinear

variable {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]

variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R₁ N₁] [AddCommGroup N₂] [Module R₂ N₂]
  {n : ℕ}

/-- The semilinear map `(⋀ⁿN₁)^∨ → (⋀ⁿN₂)^∨` attached to bases `b` of `N₁` and `b'` of `N₂`:
`φ ↦ φ(b₁ ∧ ⋯ ∧ bₙ) · (b'₁ ∧ ⋯ ∧ b'ₙ)^∨`. -/
noncomputable def topDualMap (b : Module.Basis (Fin n) R₁ N₁) (b' : Module.Basis (Fin n) R₂ N₂) :
    Module.Dual R₁ (⋀[R₁]^n N₁) →ₛₗ[algebraMap R₁ R₂] Module.Dual R₂ (⋀[R₂]^n N₂) where
  toFun φ := (algebraMap R₁ R₂ (φ (exteriorPower.ιMulti R₁ n b)) : R₂) •
    (basisTopDual b' : Module.Dual R₂ (⋀[R₂]^n N₂))
  map_add' φ ψ := by
    change (algebraMap R₁ R₂ (φ _ + ψ _)) • _ = _
    rw [map_add, add_smul]
  map_smul' r φ := by
    change (algebraMap R₁ R₂ (r * φ _)) • _ = algebraMap R₁ R₂ r • _
    rw [map_mul, mul_smul]

/-- `topDualMap b b'` sends `φ` to `φ(b₁ ∧ ⋯ ∧ bₙ) · (b'₁ ∧ ⋯ ∧ b'ₙ)^∨`. -/
theorem topDualMap_apply (b : Module.Basis (Fin n) R₁ N₁) (b' : Module.Basis (Fin n) R₂ N₂)
    (φ : Module.Dual R₁ (⋀[R₁]^n N₁)) :
    topDualMap b b' φ = (algebraMap R₁ R₂ (φ (exteriorPower.ιMulti R₁ n b)) : R₂) •
      (basisTopDual b' : Module.Dual R₂ (⋀[R₂]^n N₂)) :=
  rfl

/-- `topDualMap b b'` sends the dual basis vector of `b` to the dual basis vector of `b'`. -/
theorem topDualMap_basisTopDual (b : Module.Basis (Fin n) R₁ N₁)
    (b' : Module.Basis (Fin n) R₂ N₂) : topDualMap b b' (basisTopDual b) = basisTopDual b' := by
  rw [topDualMap_apply, basisTopDual_apply, map_one, one_smul]

/-- If a semilinear map carries the basis `b` to the basis `b'`, then `topDualMap b b'` is dual to
its top exterior power. -/
theorem topDualMap_powMapₛₗ (b : Module.Basis (Fin n) R₁ N₁) (b' : Module.Basis (Fin n) R₂ N₂)
    (f : N₁ →ₛₗ[algebraMap R₁ R₂] N₂) (hf : ∀ i, f (b i) = b' i)
    (φ : Module.Dual R₁ (⋀[R₁]^n N₁)) (x : ⋀[R₁]^n N₁) :
    topDualMap b b' φ (ExteriorAlgebra.powMapₛₗ n (algebraMap R₁ R₂) f x) =
      algebraMap R₁ R₂ (φ x) := by
  have hx := eq_basisTopDual_smul b LinearMap.id x
  rw [LinearMap.id_apply, LinearMap.id_apply] at hx
  have hfb : (fun i => f (b i)) = ⇑b' := funext hf
  rw [hx, LinearMap.map_smulₛₗ, ExteriorAlgebra.powMapₛₗ_ιMulti, hfb, LinearMap.map_smul,
    topDualMap_apply, LinearMap.smul_apply, basisTopDual_apply, LinearMap.map_smul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, mul_one, map_mul]

end Semilinear

/-- The inverse base-change comparison of exterior algebras on a wedge of degree-one
generators. -/
theorem exteriorAlgebraBaseChange_symm_one_tmul_ιMulti (R A M : Type*) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] {n : ℕ} (v : Fin n → M) :
    (ProjectiveDeterminant.exteriorAlgebraBaseChange R A M).symm
        (1 ⊗ₜ[R] ExteriorAlgebra.ιMulti R n v) =
      ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] v i) := by
  let F : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra A (A ⊗[R] M) :=
    ((ProjectiveDeterminant.exteriorAlgebraBaseChange R A M).symm.toAlgHom.restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  have hF : ∀ m, F (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι A ((1 : A) ⊗ₜ[R] m) := fun m =>
    ProjectiveDeterminant.exteriorAlgebraBaseChange_symm_one_tmul_ι A M m
  show F (ExteriorAlgebra.ιMulti R n v) = _
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => hF (v i)))

/-- `ιMulti` of the images of the elements `v i` under a semilinear map `f` extended to a base
change isomorphism `e` is the image under `⋀e` of the base change of the wedge of the `v i`. -/
private theorem ιMulti_eq_map_symm_baseChange {R₁ R₂ M₁ M₂ : Type*} [CommRing R₁] [CommRing R₂]
    [Algebra R₁ R₂] [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup M₂] [Module R₂ M₂] {n : ℕ}
    (e : R₂ ⊗[R₁] M₁ ≃ₗ[R₂] M₂) (f : M₁ →ₛₗ[algebraMap R₁ R₂] M₂)
    (he : ∀ x, e (1 ⊗ₜ x) = f x) (v : Fin n → M₁) :
    ExteriorAlgebra.ιMulti R₂ n (fun i => f (v i)) = ExteriorAlgebra.map e.toLinearMap
      ((ProjectiveDeterminant.exteriorAlgebraBaseChange R₁ R₂ M₁).symm
        (1 ⊗ₜ ExteriorAlgebra.ιMulti R₁ n v)) := by
  rw [exteriorAlgebraBaseChange_symm_one_tmul_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext i
  rw [Function.comp_apply, LinearEquiv.coe_coe, he]

/-- Two elements of the determinant line of a two-term complex whose degree `-1` term is free of
rank `n` agree as soon as they agree on the top wedge of a basis. -/
theorem determinantLine_ext {R N Z : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] [AddCommGroup Z] [Module R Z] [Module.Finite R Z]
    [Module.Projective R Z] {n : ℕ} (dM : N →ₗ[R] Z) (hN : Nonempty (Module.Basis (Fin n) R N))
    (b : Module.Basis (Fin n) R N) {F G : TwoTermComplex.determinantLine dM}
    (h : F ((determinantEquivExteriorPower n hN).symm (exteriorPower.ιMulti R n b)) =
      G ((determinantEquivExteriorPower n hN).symm (exteriorPower.ιMulti R n b))) : F = G := by
  have H := linearMap_top_ext b (F := F ∘ₗ (determinantEquivExteriorPower n hN).symm.toLinearMap)
    (G := G ∘ₗ (determinantEquivExteriorPower n hN).symm.toLinearMap) h
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun H (determinantEquivExteriorPower n hN x)
  rwa [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] at hx

section DeterminantNaturality

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
  {N₁ Z₁ N₂ Z₂ : Type u} [AddCommGroup N₁] [Module R₁ N₁] [Module.Finite R₁ N₁]
  [Module.Projective R₁ N₁] [AddCommGroup Z₁] [Module R₁ Z₁] [Module.Finite R₁ Z₁]
  [Module.Projective R₁ Z₁] [AddCommGroup N₂] [Module R₂ N₂] [Module.Finite R₂ N₂]
  [Module.Projective R₂ N₂] [AddCommGroup Z₂] [Module R₂ Z₂] [Module.Finite R₂ Z₂]
  [Module.Projective R₂ Z₂] {n : ℕ}

/-- **The base change of determinant lines along an isomorphism of two-term complexes**, on the
determinant lines of Tag 0FL8: if `neg` carries a basis of `N₁` to a basis of `N₂` and `en`,
`ez` are base change isomorphisms extending `neg` and `zero`, then conjugating the base change of
`b ↦ c` (for `b`, `c` the top wedges of bases) by the determinant maps of `en` and `ez` is the map
`neg(b) ↦ zero(c)`. -/
theorem twoTermDeterminantEquivDeterminantLine_baseChange (dM₁ : N₁ →ₗ[R₁] Z₁)
    (dM₂ : N₂ →ₗ[R₂] Z₂) (hZ₁ : Nonempty (Module.Basis (Fin n) R₁ Z₁))
    (hN₁ : Nonempty (Module.Basis (Fin n) R₁ N₁)) (hZ₂ : Nonempty (Module.Basis (Fin n) R₂ Z₂))
    (hN₂ : Nonempty (Module.Basis (Fin n) R₂ N₂)) (bN : Module.Basis (Fin n) R₁ N₁)
    (bZ : Module.Basis (Fin n) R₁ Z₁) (bN' : Module.Basis (Fin n) R₂ N₂)
    (neg : N₁ →ₛₗ[algebraMap R₁ R₂] N₂) (zero : Z₁ →ₛₗ[algebraMap R₁ R₂] Z₂)
    (hneg : ∀ i, neg (bN i) = bN' i)
    (en : R₂ ⊗[R₁] N₁ ≃ₗ[R₂] N₂) (ez : R₂ ⊗[R₁] Z₁ ≃ₗ[R₂] Z₂)
    (hen : ∀ x, en (1 ⊗ₜ x) = neg x) (hez : ∀ x, ez (1 ⊗ₜ x) = zero x) :
    twoTermDeterminantEquivDeterminantLine n dM₂ hZ₂ hN₂
        (exteriorPower.ιMulti R₂ n (fun i => zero (bZ i)) ⊗ₜ basisTopDual bN') =
      (ProjectiveDeterminant.mapEquiv ez).toLinearMap ∘ₗ
        TwoTermComplex.determinantLineBaseChangeMap R₂ dM₁
          (twoTermDeterminantEquivDeterminantLine n dM₁ hZ₁ hN₁
            (exteriorPower.ιMulti R₁ n bZ ⊗ₜ basisTopDual bN)) ∘ₗ
        (ProjectiveDeterminant.mapEquiv en).symm.toLinearMap := by
  refine determinantLine_ext dM₂ hN₂ bN' ?_
  rw [twoTermDeterminantEquivDeterminantLine_ιMulti_tmul_basisTopDual, LinearMap.comp_apply,
    LinearMap.comp_apply]
  have h1 : (ProjectiveDeterminant.mapEquiv en).symm
      ((determinantEquivExteriorPower n hN₂).symm (exteriorPower.ιMulti R₂ n bN')) =
      ProjectiveDeterminant.baseChangeEquiv
        (1 ⊗ₜ (determinantEquivExteriorPower n hN₁).symm (exteriorPower.ιMulti R₁ n bN)) := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    show ExteriorAlgebra.ιMulti R₂ n bN' = ExteriorAlgebra.map en.toLinearMap _
    exact (congrArg _ (funext fun i => (hneg i).symm)).trans
      (ιMulti_eq_map_symm_baseChange en neg hen bN)
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, h1,
    TwoTermComplex.determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul,
    twoTermDeterminantEquivDeterminantLine_ιMulti_tmul_basisTopDual]
  apply Subtype.ext
  exact ιMulti_eq_map_symm_baseChange ez zero hez bZ

omit [Module.Finite R₁ N₁] [Module.Projective R₁ N₁] [Module.Finite R₁ Z₁]
  [Module.Projective R₁ Z₁] [Module.Finite R₂ N₂] [Module.Projective R₂ N₂] [Module.Finite R₂ Z₂]
  [Module.Projective R₂ Z₂] in
/-- The map of determinant lines of Tag 0FL8 attached to semilinear maps on the two terms, on the
tensor attached to bases. -/
theorem map_ιMulti_tmul_basisTopDual (bN : Module.Basis (Fin n) R₁ N₁)
    (bZ : Module.Basis (Fin n) R₁ Z₁) (bN' : Module.Basis (Fin n) R₂ N₂)
    (zero : Z₁ →ₛₗ[algebraMap R₁ R₂] Z₂) :
    TensorProduct.map (ExteriorAlgebra.powMapₛₗ n (algebraMap R₁ R₂) zero) (topDualMap bN bN')
        (exteriorPower.ιMulti R₁ n bZ ⊗ₜ basisTopDual bN) =
      exteriorPower.ιMulti R₂ n (fun i => zero (bZ i)) ⊗ₜ basisTopDual bN' := by
  rw [TensorProduct.map_tmul, ExteriorAlgebra.powMapₛₗ_ιMulti, topDualMap_basisTopDual]

omit [Module.Finite R₁ N₁] [Module.Projective R₁ N₁] [Module.Finite R₁ Z₁]
  [Module.Projective R₁ Z₁] in
/-- Two semilinear maps out of the determinant line `⋀ⁿZ ⊗ (⋀ⁿN)^∨` of free modules of rank `n`
agree as soon as they agree on the tensor attached to bases. -/
theorem twoTermDeterminant_hom_ext (bN : Module.Basis (Fin n) R₁ N₁)
    (bZ : Module.Basis (Fin n) R₁ Z₁) {W : Type*} [AddCommGroup W] [Module R₂ W]
    {F G : twoTermDeterminant R₁ n N₁ Z₁ →ₛₗ[algebraMap R₁ R₂] W}
    (h : F (exteriorPower.ιMulti R₁ n bZ ⊗ₜ basisTopDual bN) =
      G (exteriorPower.ιMulti R₁ n bZ ⊗ₜ basisTopDual bN)) : F = G := by
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul z φ =>
    have hz := eq_basisTopDual_smul bZ LinearMap.id z
    rw [LinearMap.id_apply, LinearMap.id_apply] at hz
    have hφ : φ = φ (exteriorPower.ιMulti R₁ n bN) • basisTopDual bN := by
      refine LinearMap.ext fun x => ?_
      rw [eq_basisTopDual_smul bN φ x, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    have he : z ⊗ₜ[R₁] φ = (φ (exteriorPower.ιMulti R₁ n bN) * basisTopDual bZ z) •
        (exteriorPower.ιMulti R₁ n bZ ⊗ₜ[R₁] basisTopDual bN) := by
      calc z ⊗ₜ[R₁] φ = (basisTopDual bZ z • exteriorPower.ιMulti R₁ n bZ) ⊗ₜ[R₁]
            (φ (exteriorPower.ιMulti R₁ n bN) • basisTopDual bN) := by rw [← hz, ← hφ]
        _ = _ := by rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul]
    rw [he, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h]

end DeterminantNaturality

/-- Induction on `S ⊗[R] Ω[R⁄ℤ]`: a property of its elements which holds for `0`, for the
tensors `s ⊗ d r` and is stable under sums holds everywhere. -/
theorem tensorKaehler_induction {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {motive : S ⊗[R] Ω[R⁄ℤ] → Prop} (x : S ⊗[R] Ω[R⁄ℤ]) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (tmul : ∀ (s : S) (r : R), motive (s ⊗ₜ KaehlerDifferential.D ℤ R r)) : motive x := by
  induction x using TensorProduct.induction_on with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | tmul s ω =>
    have hω : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D ℤ R)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hω using Submodule.span_induction generalizing s with
    | mem ω hω =>
      obtain ⟨r, rfl⟩ := hω
      exact tmul s r
    | zero => rw [TensorProduct.tmul_zero]; exact zero
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add _ _ (hx s) (hy s)
    | smul a x _ hx => rw [← TensorProduct.smul_tmul]; exact hx _

/-- **Stacks Project, Tag 0H9F, read through identifications of the cokernels.** The naturality
of the maps of Tag 0FL8 (`Stacks.DeRham.funnyMap_naturality`) for the transported maps
`Stacks.DeRham.funnyMapOfEquiv`, when the map `onH` on cokernels is induced by a semilinear map
`kH` between the identified modules. -/
theorem funnyMapOfEquiv_naturality (R₁ R₂ : Type*) [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
    {K₁ L₁ N₁ Z₁ H₁ K₂ L₂ N₂ Z₂ H₂ : Type*}
    [AddCommGroup K₁] [Module R₁ K₁] [AddCommGroup L₁] [Module R₁ L₁]
    [AddCommGroup N₁] [Module R₁ N₁] [AddCommGroup Z₁] [Module R₁ Z₁]
    [AddCommGroup H₁] [Module R₁ H₁]
    [AddCommGroup K₂] [Module R₂ K₂] [AddCommGroup L₂] [Module R₂ L₂]
    [AddCommGroup N₂] [Module R₂ N₂] [AddCommGroup Z₂] [Module R₂ Z₂]
    [AddCommGroup H₂] [Module R₂ H₂]
    (n p : ℕ)
    (i₁ : K₁ →ₗ[R₁] L₁) (π₁ : L₁ →ₗ[R₁] Z₁) (d₁ : N₁ →ₗ[R₁] L₁) (dM₁ : N₁ →ₗ[R₁] Z₁)
    (i₂ : K₂ →ₗ[R₂] L₂) (π₂ : L₂ →ₗ[R₂] Z₂) (d₂ : N₂ →ₗ[R₂] L₂) (dM₂ : N₂ →ₗ[R₂] Z₂)
    (hi₁ : Function.Injective i₁) (hexact₁ : Function.Exact i₁ π₁)
    (hπ₁ : Function.Surjective π₁) (hsquare₁ : π₁.comp d₁ = dM₁)
    (hi₂ : Function.Injective i₂) (hexact₂ : Function.Exact i₂ π₂)
    (hπ₂ : Function.Surjective π₂) (hsquare₂ : π₂.comp d₂ = dM₂)
    (hZ₁ : Nonempty (Module.Basis (Fin n) R₁ Z₁)) (hN₁ : Nonempty (Module.Basis (Fin n) R₁ N₁))
    (hZ₂ : Nonempty (Module.Basis (Fin n) R₂ Z₂)) (hN₂ : Nonempty (Module.Basis (Fin n) R₂ N₂))
    (e₁ : (L₁ ⧸ LinearMap.range d₁) ≃ₗ[R₁] H₁) (e₂ : (L₂ ⧸ LinearMap.range d₂) ≃ₗ[R₂] H₂)
    (k : K₁ →ₛₗ[algebraMap R₁ R₂] K₂) (l : L₁ →ₛₗ[algebraMap R₁ R₂] L₂)
    (neg : N₁ →ₛₗ[algebraMap R₁ R₂] N₂) (zero : Z₁ →ₛₗ[algebraMap R₁ R₂] Z₂)
    (kH : H₁ →ₛₗ[algebraMap R₁ R₂] H₂)
    (hki : ∀ x, l (i₁ x) = i₂ (k x)) (hlπ : ∀ x, zero (π₁ x) = π₂ (l x))
    (hnd : ∀ x, l (d₁ x) = d₂ (neg x))
    (hkH : ∀ x, kH (e₁ (Submodule.Quotient.mk x)) = e₂ (Submodule.Quotient.mk (l x)))
    (negBaseChange : TensorProduct R₁ R₂ N₁ ≃ₗ[R₂] N₂)
    (zeroBaseChange : TensorProduct R₁ R₂ Z₁ ≃ₗ[R₂] Z₂)
    (hnegBaseChange : ∀ x r, negBaseChange (r ⊗ₜ[R₁] x) = r • neg x)
    (hzeroBaseChange : ∀ x r, zeroBaseChange (r ⊗ₜ[R₁] x) = r • zero x)
    (onNegDual : Module.Dual R₁ (⋀[R₁]^n N₁) →ₛₗ[algebraMap R₁ R₂]
      Module.Dual R₂ (⋀[R₂]^n N₂))
    (honNegDual : ∀ (φ : Module.Dual R₁ (⋀[R₁]^n N₁)) (x : ⋀[R₁]^n N₁),
      onNegDual φ (ExteriorAlgebra.powMapₛₗ n (algebraMap R₁ R₂) neg x) = algebraMap R₁ R₂ (φ x))
    (η : ⋀[R₁]^p H₁) :
    funnyMapOfEquiv n i₂ π₂ d₂ dM₂ hi₂ hexact₂ hπ₂ hsquare₂ hZ₂ hN₂ e₂ p
        (ExteriorAlgebra.powMapₛₗ p (algebraMap R₁ R₂) kH η) =
      TensorProduct.map (ExteriorAlgebra.powMapₛₗ p (algebraMap R₁ R₂) k)
        (TensorProduct.map (ExteriorAlgebra.powMapₛₗ n (algebraMap R₁ R₂) zero) onNegDual)
        (funnyMapOfEquiv n i₁ π₁ d₁ dM₁ hi₁ hexact₁ hπ₁ hsquare₁ hZ₁ hN₁ e₁ p η) := by
  have hl : LinearMap.range d₁ ≤ (LinearMap.range d₂).comap l := by
    rintro _ ⟨x, rfl⟩
    exact ⟨neg x, (hnd x).symm⟩
  have H := funnyMap_naturality R₁ R₂ n p i₁ π₁ d₁ dM₁ i₂ π₂ d₂ dM₂ hi₁ hexact₁ hπ₁ hsquare₁
    hi₂ hexact₂ hπ₂ hsquare₂ hZ₁ hN₁ hZ₂ hN₂ k l neg zero hki hlπ hnd negBaseChange zeroBaseChange
    hnegBaseChange hzeroBaseChange
    (ExteriorAlgebra.powMapₛₗ p (algebraMap R₁ R₂) (Submodule.mapQ _ _ l hl))
    (ExteriorAlgebra.powMapₛₗ p (algebraMap R₁ R₂) k)
    (ExteriorAlgebra.powMapₛₗ n (algebraMap R₁ R₂) neg)
    (ExteriorAlgebra.powMapₛₗ n (algebraMap R₁ R₂) zero) onNegDual
    (TensorProduct.map (ExteriorAlgebra.powMapₛₗ n (algebraMap R₁ R₂) zero) onNegDual)
    (fun x => ExteriorAlgebra.powMapₛₗ_ιMulti _ _ _ _)
    (fun x => ExteriorAlgebra.powMapₛₗ_ιMulti _ _ _ x)
    (fun x => ExteriorAlgebra.powMapₛₗ_ιMulti _ _ _ x)
    (fun x => ExteriorAlgebra.powMapₛₗ_ιMulti _ _ _ x) honNegDual
    (fun z φ => TensorProduct.map_tmul _ _ z φ)
  have hq : ∀ w, e₂.symm (kH (e₁ w)) = Submodule.mapQ _ _ l hl w := by
    intro w
    induction w using Submodule.Quotient.induction_on with
    | _ x => rw [LinearEquiv.symm_apply_eq, hkH, Submodule.mapQ_apply]
  rw [funnyMapOfEquiv_apply, funnyMapOfEquiv_apply,
    exteriorPower_map_symm_powMapₛₗ e₁ e₂ _ kH hq p η]
  exact (LinearMap.congr_fun H _).symm

/-- Moving a tensor product of semilinear maps across identifications of the second factors:
if `e₂ ∘ g = h ∘ e₁` then `(1 ⊗ e₂) ∘ (f ⊗ g) = (f ⊗ h) ∘ (1 ⊗ e₁)`. -/
theorem lTensor_map_eq_map_lTensor {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]
    {σ : R₁ →+* R₂} {M₁ T₁ D₁ : Type*} [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup T₁]
    [Module R₁ T₁] [AddCommGroup D₁] [Module R₁ D₁] {M₂ T₂ D₂ : Type*} [AddCommGroup M₂]
    [Module R₂ M₂] [AddCommGroup T₂] [Module R₂ T₂] [AddCommGroup D₂] [Module R₂ D₂]
    (f : M₁ →ₛₗ[σ] M₂) (g : T₁ →ₛₗ[σ] T₂) (h : D₁ →ₛₗ[σ] D₂) (e₁ : T₁ ≃ₗ[R₁] D₁)
    (e₂ : T₂ ≃ₗ[R₂] D₂) (he : ∀ t, e₂ (g t) = h (e₁ t)) (u : M₁ ⊗[R₁] T₁) :
    e₂.toLinearMap.lTensor M₂ (TensorProduct.map f g u) =
      TensorProduct.map f h (e₁.toLinearMap.lTensor M₁ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x t =>
    rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.map_tmul, LinearEquiv.coe_coe, LinearEquiv.coe_coe, he]

section Maps

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] {n n' : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin n)) [P.IsRelativeGlobalCompleteIntersection]
  (P' : Algebra.Presentation A' B' (Fin n') (Fin n')) [P'.IsRelativeGlobalCompleteIntersection]
  (Φ : P.toExtension.Hom P'.toExtension)


/-- The map on conormal modules induced by a morphism of presentations, semilinear along
`B → B'`. -/
noncomputable def cotangentMapₛₗ :
    P.toExtension.Cotangent →ₛₗ[algebraMap B B'] P'.toExtension.Cotangent where
  toFun := Algebra.Extension.Cotangent.map Φ
  map_add' := map_add _
  map_smul' b x := ((Algebra.Extension.Cotangent.map Φ).map_smul b x).trans
    (algebraMap_smul B' b _).symm

/-- The map on cotangent spaces induced by a morphism of presentations, semilinear along
`B → B'`. -/
noncomputable def cotangentSpaceMapₛₗ :
    P.toExtension.CotangentSpace →ₛₗ[algebraMap B B'] P'.toExtension.CotangentSpace where
  toFun := Algebra.Extension.CotangentSpace.map Φ
  map_add' := map_add _
  map_smul' b x := ((Algebra.Extension.CotangentSpace.map Φ).map_smul b x).trans
    (algebraMap_smul B' b _).symm

variable {P P' Φ}

variable (B B') in
/-- The map `Ω[B⁄ℤ] → Ω[B'⁄ℤ]`, semilinear along `B → B'`. -/
noncomputable def kaehlerMapₛₗ : Ω[B⁄ℤ] →ₛₗ[algebraMap B B'] Ω[B'⁄ℤ] where
  toFun := KaehlerDifferential.map ℤ ℤ B B'
  map_add' := map_add _
  map_smul' b x := ((KaehlerDifferential.map ℤ ℤ B B').map_smul b x).trans
    (algebraMap_smul B' b _).symm

variable (B B') in
/-- `kaehlerMapₛₗ` sends `d b` to `d (algebraMap B B' b)`. -/
theorem kaehlerMapₛₗ_D (b : B) :
    kaehlerMapₛₗ B B' (KaehlerDifferential.D ℤ B b) =
      KaehlerDifferential.D ℤ B' (algebraMap B B' b) :=
  KaehlerDifferential.map_D ℤ ℤ B B' b

variable (A B A' B') in
/-- The map `B ⊗[A] Ω[A⁄ℤ] → B' ⊗[A'] Ω[A'⁄ℤ]` of base changed differentials, semilinear along
`B → B'`. -/
noncomputable def formsBaseChangeMapₛₗ :
    B ⊗[A] Ω[A⁄ℤ] →ₛₗ[algebraMap B B'] B' ⊗[A'] Ω[A'⁄ℤ] where
  toFun := LinearMap.liftBaseChange B
    ((TensorProduct.mk A' B' Ω[A'⁄ℤ] 1).restrictScalars A ∘ₗ KaehlerDifferential.map ℤ ℤ A A')
  map_add' := map_add _
  map_smul' b x := (LinearMap.map_smul _ b x).trans (algebraMap_smul B' b _).symm

variable (A B A' B') in
/-- `formsBaseChangeMapₛₗ` sends `b ⊗ ω` to `algebraMap B B' b ⊗ Ω(ω)`, where `Ω(ω)` is the image
of `ω` under `Ω[A⁄ℤ] → Ω[A'⁄ℤ]`. -/
theorem formsBaseChangeMapₛₗ_tmul (b : B) (ω : Ω[A⁄ℤ]) :
    formsBaseChangeMapₛₗ A B A' B' (b ⊗ₜ ω) =
      algebraMap B B' b ⊗ₜ KaehlerDifferential.map ℤ ℤ A A' ω := by
  show LinearMap.liftBaseChange B _ (b ⊗ₜ ω) = _
  rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    TensorProduct.mk_apply, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

variable (P P' Φ) in
/-- The map `B ⊗[A[x]] Ω[A[x]⁄ℤ] → B' ⊗[A'[x]] Ω[A'[x]⁄ℤ]` induced by a morphism of
presentations, semilinear along `B → B'`. -/
noncomputable def polynomialFormsMapₛₗ :
    B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ] →ₛₗ[algebraMap B B']
      B' ⊗[P'.toExtension.Ring] Ω[P'.toExtension.Ring⁄ℤ] :=
  letI : Algebra P.toExtension.Ring B' :=
    ((algebraMap B B').comp (algebraMap P.toExtension.Ring B)).toAlgebra
  haveI : IsScalarTower P.toExtension.Ring B B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra P.toExtension.Ring P'.toExtension.Ring := Φ.toRingHom.toAlgebra
  haveI : IsScalarTower P.toExtension.Ring P'.toExtension.Ring B' :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ (Φ.algebraMap_toRingHom x).symm)
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := P.toExtension.Ring)
    (A := P'.toExtension.Ring) (RingHom.ext_int _ _)
  { toFun := LinearMap.liftBaseChange B
      ((TensorProduct.mk P'.toExtension.Ring B' Ω[P'.toExtension.Ring⁄ℤ] 1).restrictScalars
        P.toExtension.Ring ∘ₗ
        KaehlerDifferential.map ℤ ℤ P.toExtension.Ring P'.toExtension.Ring)
    map_add' := map_add _
    map_smul' := fun b x => (LinearMap.map_smul _ b x).trans (algebraMap_smul B' b _).symm }

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
    [P.IsRelativeGlobalCompleteIntersection] [P'.IsRelativeGlobalCompleteIntersection] in
/-- `polynomialFormsMapₛₗ` sends `b ⊗ d q` to `algebraMap B B' b ⊗ d (Φ q)`. -/
theorem polynomialFormsMapₛₗ_tmul_D (b : B) (q : P.toExtension.Ring) :
    polynomialFormsMapₛₗ P P' Φ (b ⊗ₜ KaehlerDifferential.D ℤ P.toExtension.Ring q) =
      algebraMap B B' b ⊗ₜ KaehlerDifferential.D ℤ P'.toExtension.Ring (Φ.toRingHom q) := by
  let : Algebra P.toExtension.Ring B' :=
    ((algebraMap B B').comp (algebraMap P.toExtension.Ring B)).toAlgebra
  have : IsScalarTower P.toExtension.Ring B B' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra P.toExtension.Ring P'.toExtension.Ring := Φ.toRingHom.toAlgebra
  have : IsScalarTower P.toExtension.Ring P'.toExtension.Ring B' :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ (Φ.algebraMap_toRingHom x).symm)
  have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := P.toExtension.Ring)
    (A := P'.toExtension.Ring) (RingHom.ext_int _ _)
  show LinearMap.liftBaseChange B _ (b ⊗ₜ _) = _
  rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    KaehlerDifferential.map_D, TensorProduct.mk_apply, TensorProduct.smul_tmul', Algebra.smul_def,
    mul_one]
  rfl

/-! ### The morphism of diagrams of Remark 0FL9 -/

/-- `polynomialFormsMapₛₗ` commutes with the maps `i` of the cotangent diagrams of `P` and `P'`
and the map `formsBaseChangeMapₛₗ`. -/
theorem polynomialFormsMapₛₗ_i (x : B ⊗[A] Ω[A⁄ℤ]) :
    polynomialFormsMapₛₗ P P' Φ ((cotangentDiagram P).i x) =
      (cotangentDiagram P').i (formsBaseChangeMapₛₗ A B A' B' x) := by
  refine tensorKaehler_induction (R := A) (S := B) (motive := fun x =>
    polynomialFormsMapₛₗ P P' Φ
    ((cotangentDiagram P).i x) = (cotangentDiagram P').i (formsBaseChangeMapₛₗ A B A' B' x)) x
    (by rw [map_zero, map_zero, map_zero, map_zero]) (fun x y hx hy => by
      rw [map_add, map_add, hx, hy, map_add, map_add]) (fun b a => ?_)
  rw [CotangentDiagram.cotangentDiagram_i_tmul, KaehlerDifferential.map_D,
    polynomialFormsMapₛₗ_tmul_D, formsBaseChangeMapₛₗ_tmul, KaehlerDifferential.map_D,
    CotangentDiagram.cotangentDiagram_i_tmul, KaehlerDifferential.map_D,
    Algebra.Extension.Hom.toRingHom_algebraMap]

omit [IsScalarTower A B B'] in
/-- `cotangentSpaceMapₛₗ` commutes with the maps `π` of the cotangent diagrams of `P` and `P'`
and the map `polynomialFormsMapₛₗ`. -/
theorem cotangentSpaceMapₛₗ_π (x : B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]) :
    cotangentSpaceMapₛₗ P P' Φ ((cotangentDiagram P).π x) =
      (cotangentDiagram P').π (polynomialFormsMapₛₗ P P' Φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b ω =>
    have hω : ω ∈ Submodule.span P.toExtension.Ring
        (Set.range (KaehlerDifferential.D ℤ P.toExtension.Ring)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hω using Submodule.span_induction generalizing b with
    | mem ω hω =>
      obtain ⟨q, rfl⟩ := hω
      rw [CotangentDiagram.cotangentDiagram_π_tmul, KaehlerDifferential.map_D,
        polynomialFormsMapₛₗ_tmul_D, CotangentDiagram.cotangentDiagram_π_tmul,
        KaehlerDifferential.map_D]
      show Algebra.Extension.CotangentSpace.map Φ _ = _
      rw [Algebra.Extension.CotangentSpace.map_tmul, Algebra.Extension.Hom.toAlgHom_apply]
      rfl
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | smul a x _ hx => rw [← TensorProduct.smul_tmul]; exact hx _

omit [IsScalarTower A B B'] in
/-- `polynomialFormsMapₛₗ` commutes with the conormal maps `d` of the cotangent diagrams of `P`
and `P'` and the map `cotangentMapₛₗ`. -/
theorem polynomialFormsMapₛₗ_d (x : P.toExtension.Cotangent) :
    polynomialFormsMapₛₗ P P' Φ ((cotangentDiagram P).d x) =
      (cotangentDiagram P').d (cotangentMapₛₗ P P' Φ x) := by
  obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  show _ = (cotangentDiagram P').d (Algebra.Extension.Cotangent.map Φ _)
  rw [CotangentDiagram.cotangentDiagram_d_mk, polynomialFormsMapₛₗ_tmul_D, map_one,
    Algebra.Extension.Cotangent.map_mk, CotangentDiagram.cotangentDiagram_d_mk]
  rfl

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `kaehlerMapₛₗ` commutes with the identifications `quotientEquiv` of the cokernels of the
conormal maps of `P` and `P'` with `Ω[B⁄ℤ]` and `Ω[B'⁄ℤ]`, on classes of elements. -/
theorem kaehlerMapₛₗ_quotientEquiv
    (x : B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]) :
    kaehlerMapₛₗ B B' ((cotangentDiagram P).quotientEquiv (Submodule.Quotient.mk x)) =
      (cotangentDiagram P').quotientEquiv
        (Submodule.Quotient.mk (polynomialFormsMapₛₗ P P' Φ x)) := by
  rw [CotangentDiagram.cotangentDiagram_quotientEquiv_mk,
    CotangentDiagram.cotangentDiagram_quotientEquiv_mk]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b ω =>
    have hω : ω ∈ Submodule.span P.toExtension.Ring
        (Set.range (KaehlerDifferential.D ℤ P.toExtension.Ring)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hω using Submodule.span_induction generalizing b with
    | mem ω hω =>
      obtain ⟨q, rfl⟩ := hω
      rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, map_smulₛₗ,
        kaehlerMapₛₗ_D, polynomialFormsMapₛₗ_tmul_D, KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.map_D, Algebra.Extension.Hom.algebraMap_toRingHom]
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | smul a x _ hx => rw [← TensorProduct.smul_tmul]; exact hx _

omit [IsScalarTower A B B'] in
/-- `polynomialFormsMapₛₗ` carries the range of the conormal map of `P` into the range of the
conormal map of `P'`. -/
theorem range_d_le_comap_polynomialFormsMapₛₗ :
    LinearMap.range (cotangentDiagram P).d ≤
      (LinearMap.range (cotangentDiagram P').d).comap (polynomialFormsMapₛₗ P P' Φ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨cotangentMapₛₗ P P' Φ x, (polynomialFormsMapₛₗ_d x).symm⟩

variable (P P' Φ) in
/-- The map of cokernels of the conormal maps induced by a morphism of presentations. -/
noncomputable def cokernelMapₛₗ :
    (B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ] ⧸ LinearMap.range (cotangentDiagram P).d)
      →ₛₗ[algebraMap B B']
      (B' ⊗[P'.toExtension.Ring] Ω[P'.toExtension.Ring⁄ℤ] ⧸
        LinearMap.range (cotangentDiagram P').d) :=
  Submodule.mapQ (LinearMap.range (cotangentDiagram P).d) (LinearMap.range (cotangentDiagram P').d)
    (polynomialFormsMapₛₗ P P' Φ) range_d_le_comap_polynomialFormsMapₛₗ

omit [IsScalarTower A B B'] in
/-- `cokernelMapₛₗ` sends the class of `x` to the class of `polynomialFormsMapₛₗ P P' Φ x`. -/
theorem cokernelMapₛₗ_mk (x : B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]) :
    cokernelMapₛₗ P P' Φ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (polynomialFormsMapₛₗ P P' Φ x) :=
  rfl

omit [IsScalarTower A B B'] in
/-- Under the identifications `quotientEquiv` of the cokernels of the conormal maps with the
modules of differentials, `kaehlerMapₛₗ` corresponds to `cokernelMapₛₗ`. -/
theorem quotientEquiv_symm_kaehlerMapₛₗ
    (w : B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ] ⧸ LinearMap.range (cotangentDiagram P).d) :
    (cotangentDiagram P').quotientEquiv.symm
      (kaehlerMapₛₗ B B' ((cotangentDiagram P).quotientEquiv w)) = cokernelMapₛₗ P P' Φ w := by
  induction w using Submodule.Quotient.induction_on with
  | _ x =>
    rw [LinearEquiv.symm_apply_eq, kaehlerMapₛₗ_quotientEquiv (Φ := Φ), cokernelMapₛₗ_mk]

end Maps

section Square

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B'] {n : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin n)) [P.IsRelativeGlobalCompleteIntersection]
  (P' : Algebra.Presentation A' B' (Fin n) (Fin n)) [P'.IsRelativeGlobalCompleteIntersection]
  (Φ : P.toExtension.Hom P'.toExtension)

/-- The basis of the conormal module of a square relative global complete intersection
presentation given by the classes of the relations. -/
noncomputable def cotangentBasis : Module.Basis (Fin n) B P.toExtension.Cotangent :=
  (Algebra.Presentation.exists_basis_cotangent_relation P).choose

/-- The `i`-th element of `cotangentBasis P` is the class of the `i`-th relation. -/
theorem cotangentBasis_apply (i : Fin n) :
    cotangentBasis P i = Algebra.Extension.Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩ :=
  (Algebra.Presentation.exists_basis_cotangent_relation P).choose_spec i

variable {P P' Φ}

omit [IsScalarTower A B B'] in
/-- A morphism of presentations carrying relations to relations carries the basis of relation
classes to the basis of relation classes. -/
theorem cotangentMapₛₗ_cotangentBasis (hrel : ∀ i, Φ.toRingHom (P.relation i) = P'.relation i)
    (i : Fin n) : cotangentMapₛₗ P P' Φ (cotangentBasis P i) = cotangentBasis P' i := by
  rw [cotangentBasis_apply, cotangentBasis_apply]
  show Algebra.Extension.Cotangent.mk _ = _
  congr 1
  exact Subtype.ext (hrel i)

omit [IsScalarTower A B B'] in
/-- A morphism of presentations carrying relations to relations induces an isomorphism of the
base changed conormal module with the conormal module. -/
theorem bijective_liftBaseChange_cotangentMap
    (hrel : ∀ i, Φ.toRingHom (P.relation i) = P'.relation i) :
    Function.Bijective ((Algebra.Extension.Cotangent.map Φ).liftBaseChange B') := by
  let b₁ := Algebra.TensorProduct.basis B' (cotangentBasis P)
  let e := b₁.equiv (cotangentBasis P') (Equiv.refl _)
  have : (Algebra.Extension.Cotangent.map Φ).liftBaseChange B' = e.toLinearMap := by
    refine b₁.ext fun i => ?_
    have he : e (b₁ i) = cotangentBasis P' i := by
      rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [LinearEquiv.coe_coe, he, Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul,
      one_smul]
    exact cotangentMapₛₗ_cotangentBasis hrel i
  rw [this]
  exact e.bijective

variable (Φ) in
/-- The basis of the conormal module of `P'` image of the basis of relation classes of `P`, when
the morphism induces an isomorphism of base changed conormal modules. -/
noncomputable def cotangentBasisImage
    (hneg : Function.Bijective ((Algebra.Extension.Cotangent.map Φ).liftBaseChange B')) :
    Module.Basis (Fin n) B' P'.toExtension.Cotangent :=
  (Algebra.TensorProduct.basis B' (cotangentBasis P)).map (LinearEquiv.ofBijective _ hneg)

omit [IsScalarTower A B B'] [P'.IsRelativeGlobalCompleteIntersection] in
/-- `cotangentMapₛₗ` sends the `i`-th element of `cotangentBasis P` to the `i`-th element of
`cotangentBasisImage Φ hneg`. -/
theorem cotangentMapₛₗ_cotangentBasis_eq_image
    (hneg : Function.Bijective ((Algebra.Extension.Cotangent.map Φ).liftBaseChange B'))
    (i : Fin n) : cotangentMapₛₗ P P' Φ (cotangentBasis P i) = cotangentBasisImage Φ hneg i := by
  rw [cotangentBasisImage, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

section Syntomic

variable [Algebra.Syntomic A B] [Algebra.Syntomic A' B']

/-- **The identifications of determinant lines with `det(NL)` are compatible with the base change
map of determinants**, along a morphism of square presentations over a good square carrying
relations to relations and inducing an isomorphism of base changed cotangent spaces: on the
determinant lines `⋀ⁿ(Ω_{P/A} ⊗ B) ⊗ (⋀ⁿ(I/I²))^∨` of Tag 0FL8 the morphism acts by the top
exterior power of its map on cotangent spaces and the dual of the top exterior power of its map
on conormal modules. -/
theorem presentationDetNLEquiv_map (hsq : NaiveCotangent.IsGoodSquare A B A' B')
    (hneg : Function.Bijective ((Algebra.Extension.Cotangent.map Φ).liftBaseChange B'))
    (hzero : Function.Bijective ((Algebra.Extension.CotangentSpace.map Φ).liftBaseChange B'))
    (t : twoTermDeterminant B n P.toExtension.Cotangent P.toExtension.CotangentSpace) :
    presentationDetNLEquiv P' (TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ n (algebraMap B B') (cotangentSpaceMapₛₗ P P' Φ))
        (topDualMap (cotangentBasis P) (cotangentBasisImage Φ hneg)) t) =
      NaiveCotangent.detNLMap hsq (presentationDetNLEquiv P t) := by
  have hbij₁ := hneg
  have hq := NaiveCotangent.isQuasiIso_of_bijective (NaiveCotangent.nlBaseChangeMap (T := B') Φ)
    hbij₁ hzero
  have hgen : presentationDetNLEquiv P' (TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ n (algebraMap B B') (cotangentSpaceMapₛₗ P P' Φ))
        (topDualMap (cotangentBasis P) (cotangentBasisImage Φ hneg))
        (exteriorPower.ιMulti B n (Algebra.Generators.cotangentSpaceBasis P.toGenerators) ⊗ₜ
          basisTopDual (cotangentBasis P))) =
      NaiveCotangent.detNLMap hsq (presentationDetNLEquiv P
        (exteriorPower.ιMulti B n (Algebra.Generators.cotangentSpaceBasis P.toGenerators) ⊗ₜ
          basisTopDual (cotangentBasis P))) := by
    apply (NaiveCotangent.detNLEquiv P'.toExtension
      (P'.toGenerators.defaultHom (Algebra.Generators.self A' B')).toExtensionHom).injective
    rw [NaiveCotangent.detNLMap_eq hsq P.toExtension
        (P.toGenerators.defaultHom (Algebra.Generators.self A B)).toExtensionHom,
      NaiveCotangent.detNLEquiv_detNLMapOf hsq P.toExtension _ P'.toExtension _ Φ hq]
    have key := twoTermDeterminantEquivDeterminantLine_baseChange P.toExtension.cotangentComplex
      P'.toExtension.cotangentComplex (nonempty_basis_cotangentSpace P) (nonempty_basis_cotangent P)
      (nonempty_basis_cotangentSpace P') (nonempty_basis_cotangent P') (cotangentBasis P)
      (Algebra.Generators.cotangentSpaceBasis P.toGenerators) (cotangentBasisImage Φ hneg)
      (cotangentMapₛₗ P P' Φ) (cotangentSpaceMapₛₗ P P' Φ)
      (cotangentMapₛₗ_cotangentBasis_eq_image hneg)
      (LinearEquiv.ofBijective _ hbij₁) (LinearEquiv.ofBijective _ hzero)
      (fun x => (LinearMap.liftBaseChange_tmul _ _ _ x).trans (one_smul _ _))
      (fun x => (LinearMap.liftBaseChange_tmul _ _ _ x).trans (one_smul _ _))
    have h3 := (map_ιMulti_tmul_basisTopDual (cotangentBasis P)
      (Algebra.Generators.cotangentSpaceBasis P.toGenerators) (cotangentBasisImage Φ hneg)
      (cotangentSpaceMapₛₗ P P' Φ))
    have h4 := NaiveCotangent.detTransport_eq_detEquiv _ hq hbij₁.2 hzero.2
    have h5 := TwoTermComplex.Hom.detEquiv_apply_of_bijective
      (NaiveCotangent.nlBaseChangeMap (T := B') Φ).toHom hbij₁ hzero
    refine (detNLEquiv_presentationDetNLEquiv P' _).trans ?_
    refine Eq.trans ?_ (congrArg (fun φ => NaiveCotangent.detTransport _ hq
      ((NaiveCotangent.nlOfExtension P.toExtension).detBaseChange B' φ))
        (detNLEquiv_presentationDetNLEquiv P _)).symm
    exact (congrArg (twoTermDeterminantEquivDeterminantLine n _ _ _) h3).trans
      (key.trans ((h5 _ _ _).symm.trans (LinearEquiv.congr_fun h4 _).symm))
  exact LinearMap.congr_fun (twoTermDeterminant_hom_ext (cotangentBasis P)
    (Algebra.Generators.cotangentSpaceBasis P.toGenerators)
    (F := (presentationDetNLEquiv P').toLinearMap.comp (TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ n (algebraMap B B') (cotangentSpaceMapₛₗ P P' Φ))
        (topDualMap (cotangentBasis P) (cotangentBasisImage Φ hneg))))
    (G := (NaiveCotangent.detNLMap hsq).comp (presentationDetNLEquiv P).toLinearMap) hgen) t

end Syntomic

/-- **Stacks Project, Tag 0H9F, for the maps of Remark 0FL9.** A morphism of square relative
global complete intersection presentations over a good square, carrying relations to relations
and inducing an isomorphism of base changed cotangent spaces, intertwines the maps of
Remark 0FL9, read on the determinant lines of the presentations. -/
theorem presentationFunnyMap_naturality
    (hneg : Function.Bijective ((Algebra.Extension.Cotangent.map Φ).liftBaseChange B'))
    (hzero : Function.Bijective ((Algebra.Extension.CotangentSpace.map Φ).liftBaseChange B'))
    (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationFunnyMap P' p (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (kaehlerMapₛₗ B B') η) =
      TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (formsBaseChangeMapₛₗ A B A' B'))
        (TensorProduct.map
          (ExteriorAlgebra.powMapₛₗ n (algebraMap B B') (cotangentSpaceMapₛₗ P P' Φ))
          (topDualMap (cotangentBasis P) (cotangentBasisImage Φ hneg)))
        (presentationFunnyMap P p η) :=
  funnyMapOfEquiv_naturality B B' n p (cotangentDiagram P).i (cotangentDiagram P).π
    (cotangentDiagram P).d P.toExtension.cotangentComplex (cotangentDiagram P').i
    (cotangentDiagram P').π (cotangentDiagram P').d P'.toExtension.cotangentComplex
    (cotangentDiagram P).hi (cotangentDiagram P).hexact (cotangentDiagram P).hπ
    (cotangentDiagram P).hsquare (cotangentDiagram P').hi (cotangentDiagram P').hexact
    (cotangentDiagram P').hπ (cotangentDiagram P').hsquare (cotangentDiagram P).hzero
    (cotangentDiagram P).hneg (cotangentDiagram P').hzero (cotangentDiagram P').hneg
    (cotangentDiagram P).quotientEquiv (cotangentDiagram P').quotientEquiv
    (formsBaseChangeMapₛₗ A B A' B') (polynomialFormsMapₛₗ P P' Φ) (cotangentMapₛₗ P P' Φ)
    (cotangentSpaceMapₛₗ P P' Φ) (kaehlerMapₛₗ B B') polynomialFormsMapₛₗ_i
    cotangentSpaceMapₛₗ_π polynomialFormsMapₛₗ_d (kaehlerMapₛₗ_quotientEquiv (Φ := Φ))
    (LinearEquiv.ofBijective _ hneg)
    (LinearEquiv.ofBijective _ hzero)
    (fun x r => LinearMap.liftBaseChange_tmul _ _ r x)
    (fun x r => LinearMap.liftBaseChange_tmul _ _ r x)
    (topDualMap (cotangentBasis P) (cotangentBasisImage Φ hneg))
    (topDualMap_powMapₛₗ _ _ _ (cotangentMapₛₗ_cotangentBasis_eq_image hneg)) η

variable [Algebra.Syntomic A B] [Algebra.Syntomic A' B']

/-- **Stacks Project, Tag 0H9F, for the maps of Remark 0FL9 with values in `det(NL)`.** A morphism
of square relative global complete intersection presentations over a good square, carrying
relations to relations and inducing an isomorphism of base changed cotangent spaces, intertwines
the maps `Stacks.DeRham.presentationDetNLMap`: the square formed with the maps
`Ω^p_{B/ℤ} → Ω^p_{B'/ℤ}`, `Ω^p_{A/ℤ} ⊗_A B → Ω^p_{A'/ℤ} ⊗_{A'} B'` and the base change map of
determinants `det(NL_{B/A}) → det(NL_{B'/A'})` commutes. -/
theorem presentationDetNLMap_naturality (hsq : NaiveCotangent.IsGoodSquare A B A' B')
    (hneg : Function.Bijective ((Algebra.Extension.Cotangent.map Φ).liftBaseChange B'))
    (hzero : Function.Bijective ((Algebra.Extension.CotangentSpace.map Φ).liftBaseChange B'))
    (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationDetNLMap P' p (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (kaehlerMapₛₗ B B') η) =
      TensorProduct.map
        (ExteriorAlgebra.powMapₛₗ p (algebraMap B B') (formsBaseChangeMapₛₗ A B A' B'))
        (NaiveCotangent.detNLMap hsq) (presentationDetNLMap P p η) :=
  (congrArg ((presentationDetNLEquiv P').toLinearMap.lTensor _)
    (presentationFunnyMap_naturality hneg hzero p η)).trans
    (lTensor_map_eq_map_lTensor _ _ _ _ _ (presentationDetNLEquiv_map hsq hneg hzero) _)

end Square

end Stacks.DeRham

end
