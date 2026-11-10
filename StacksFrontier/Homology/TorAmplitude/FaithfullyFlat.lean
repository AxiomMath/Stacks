module

public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.Algebra.Homology.KFlat


@[expose] public section

-- Required by the carrier-level definitional steps of the `restrictScalars`/`extendScalars`
-- component isos below; without it they no longer elaborate in reasonable time.
set_option backward.isDefEq.respectTransparency false

/-!
# Tor-amplitude under faithfully flat base change

Let `R → A → B` be ring maps such that `A → B` is faithfully flat, and let `K` be a complex of
`A`-modules. Then `K` has tor-amplitude in `[a, b]` over `R` if and only if `K ⊗_A^L B` has
tor-amplitude in `[a, b]` over `R` (Stacks 0DJF).

## Main definitions

* `derivedTensorHomology`: the `i`-th cohomology of `K ⊗_R^L M`.
* `HasTorAmplitude`: a complex has tor-amplitude in `[a, b]` (Stacks 0652).

## Main results

* `derivedTensorHomology_isZero_iff_extendScalars`: for every `R`-module `M` and every `i`,
  `H^i(K ⊗_R^L M)` vanishes if and only if `H^i((K ⊗_A^L B) ⊗_R^L M)` does.
* `hasTorAmplitudeIn_iff_extendScalars`: Stacks 0DJF.
* `derivedTensorHomologySingle₀Iso`: for a module `N` placed in degree `0`, `derivedTensorHomology`
  is Mathlib's `Tor`.

## Implementation notes

* Objects of `D(R)` are represented by cochain complexes `CochainComplex (ModuleCat R) ℤ`, with
  cohomological indexing; cohomology is `HomologicalComplex.homology`, and its vanishing is
  `IsZero` in `ModuleCat R`.
* Mathlib has no derived tensor product on the derived category. The derived tensor product
  `K ⊗_R^L M` with a module `M` is modelled by the total tensor complex `K ⊗ P` for a projective
  resolution `P → M`, placed in nonpositive degrees via `ComplexShape.embeddingDownNat`; its
  cohomology is the hyper-Tor `H^i(K ⊗_R^L M)` (Stacks 0654).
* As `B` is flat over `A`, the derived base change `K ⊗_A^L B` is represented by the termwise
  extension of scalars `CochainComplex.extendScalars` applied to `K`.
* Tor-amplitude over `R` is tor-amplitude of the complex obtained by restriction of scalars along
  `R → A` (resp. `R → B`). The ring maps are algebra structures with `IsScalarTower R A B`, and the
  modules quantified over live in the universe `u` of the rings.
* The rings and modules share one universe `u`: the monoidal structure used for `tensorLeft` is
  `ModuleCat.monoidalCategory`, which Mathlib states only for modules in the universe of the ring.
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace StacksDraft.TorAmplitude.FaithfullyFlat

/-! ## Main definitions -/

/-- A cochain-complex (over `ℤ`) representative of a chosen projective resolution of the
module `M`, placed in nonpositive cohomological degrees (degree `-n` carries the `n`-th
term of the resolution). -/
noncomputable def projResComplex {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).obj
    (ProjectiveResolution.of M).complex

/-- The `i`-th cohomology of the derived tensor product `K ⊗_R^L M`, computed as the
cohomology of `K ⊗ P` where `P → M` is a projective resolution of `M`. -/
noncomputable def derivedTensorHomology {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) (i : ℤ) :
    ModuleCat.{u} R :=
  ((tensorLeft K).obj (projResComplex M)).homology i

/-- The complex `K` (viewed as an object of `D(R)`) has *tor-amplitude in `[a, b]`* if
`H^i(K ⊗_R^L M) = 0` for every `R`-module `M` and every `i ∉ [a, b]`. -/
def HasTorAmplitude {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
    IsZero (derivedTensorHomology K M i)

@[deprecated (since := "2026-09-27")]
alias HasTorAmplitudeIn := HasTorAmplitude

/-- Unfolding lemma for `HasTorAmplitude`: tor-amplitude in `[a, b]` is exactly the
vanishing of `H^i(K ⊗_R^L M)` for all `R`-modules `M` and all `i ∉ [a, b]`. -/
theorem hasTorAmplitudeIn_iff {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) :
    HasTorAmplitude K a b ↔
      ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
        IsZero (derivedTensorHomology K M i) :=
  Iff.rfl

/-- The defining vanishing supplied by a tor-amplitude hypothesis: if `K` has tor-amplitude
in `[a, b]` then `H^i(K ⊗_R^L M)` is zero for every `R`-module `M` and every `i ∉ [a, b]`. -/
theorem HasTorAmplitude.isZero {R : Type u} [CommRing R]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ} (h : HasTorAmplitude K a b)
    (M : ModuleCat.{u} R) {i : ℤ} (hi : i < a ∨ b < i) :
    IsZero (derivedTensorHomology K M i) := h M i hi

/-! Restriction and extension of scalars on cochain complexes along a ring map are
`CochainComplex.restrictScalars` and `CochainComplex.extendScalars` from
`StacksFrontier.Algebra.Homology.KFlat`; below they are used along `algebraMap`. Under flatness of
`A → B` the latter represents the derived base change `- ⊗_A^L B`. -/

/-- The `A`-module lift of the (`R`-side) derived-tensor homology of a complex `K` of `A`-modules:
the `R`-module resolution `projResComplex M` is extended to `A` along `algebraMap R A`, tensored
with `K` over `A`, and the `i`-th homology is taken in `ModuleCat A`. -/
noncomputable def derivedTensorHomologyA (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} R) (i : ℤ) :
    ModuleCat.{u} A :=
  ((tensorLeft K).obj
    ((CochainComplex.extendScalars (algebraMap R A)).obj (projResComplex M))).homology i

/-- `restrictScalars` along a ring map preserves and reflects `IsZero`. -/
@[simp]
theorem isZero_restrictScalars_iff {A B : Type u} [Ring A] [Ring B] (f : A →+* B)
    (N : ModuleCat.{u} B) :
    IsZero ((ModuleCat.restrictScalars f).obj N) ↔ IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]; rfl

/-- The identity `A' ≃ₗ[R] A`, where `A'` is `A` carrying the `restrictScalars`-induced `R`-module
structure. -/
noncomputable def restrictScalarsSelfEquiv (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) : Type u) ≃ₗ[R] A :=
  { Equiv.refl A with
    map_add' := fun _ _ => rfl
    map_smul' := fun r b => by
      rw [ModuleCat.restrictScalars.smul_def]
      simp only [RingHom.id_apply, smul_eq_mul, Algebra.smul_def]; rfl }

/-- The `A`-linear equivalence from the carrier of `extendScalars.obj N` (which is
`TensorProduct R A' N`) to `TensorProduct R A N`, identifying `A'` with `A`. -/
noncomputable def extendScalarsCarrierEquiv (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (N : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars (algebraMap R A)).obj N : Type u) ≃ₗ[A]
      TensorProduct R A (N : Type u) := by
  let E := TensorProduct.congr (restrictScalarsSelfEquiv R A) (LinearEquiv.refl R (N : Type u))
  refine { toFun := E, invFun := E.symm, left_inv := E.left_inv, right_inv := E.right_inv,
           map_add' := E.map_add', map_smul' := ?_ }
  intro a z
  induction z using TensorProduct.inductionOn with
  | tmul x n =>
      change E (a • (x ⊗ₜ[R] n)) = a • E (x ⊗ₜ[R] n)
      rw [show a • (x ⊗ₜ[R] n : ((ModuleCat.extendScalars (algebraMap R A)).obj N : Type u))
            = (a • x) ⊗ₜ[R] n from rfl]
      simp only [E, TensorProduct.congr_tmul, LinearEquiv.refl_apply]; rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **Faithfully-flat reflection (module level).** If `A → B` is faithfully flat then for an
`A`-module `NA`, `NA ⊗_A B = 0 ↔ NA = 0`, phrased as `IsZero` of `extendScalars`. -/
theorem isZero_extendScalars_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (NA : ModuleCat.{u} A) :
    IsZero ((ModuleCat.extendScalars (algebraMap A B)).obj NA) ↔ IsZero NA := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact (extendScalarsCarrierEquiv A B NA).toEquiv.subsingleton_congr.trans
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B (N := (NA : Type u)))

/-- The per-summand projection-formula iso (degree `(i,k)`): the restriction of
`K_i ⊗_A (A ⊗_R P_k)` is `R`-linearly isomorphic to `(restrict K_i) ⊗_R P_k`, built from
`extendScalarsCarrierEquiv` and the base-change cancellation `cancelBaseChange`. -/
noncomputable def restrictTensorLeftExtendSummandIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (i k : ℤ) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj
      (((curriedTensor (ModuleCat.{u} A)).obj (K.X i)).obj
        (((CochainComplex.extendScalars (algebraMap R A)).obj P).X k))
      ≅ ((curriedTensor (ModuleCat.{u} R)).obj
          (((CochainComplex.restrictScalars (algebraMap R A)).obj K).X i)).obj (P.X k) := by
  letI : Module R ((K.X i) : Type u) :=
    (inferInstance : Module R ((ModuleCat.restrictScalars (algebraMap R A)).obj (K.X i) : Type u))
  letI : IsScalarTower R A ((K.X i) : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower R A (TensorProduct R ((K.X i) : Type u) ((P.X k) : Type u)) := inferInstance
  letI : IsScalarTower R A
      ((ModuleCat.restrictScalars (algebraMap R A)).obj
        (((curriedTensor (ModuleCat.{u} A)).obj (K.X i)).obj
          (((CochainComplex.extendScalars (algebraMap R A)).obj P).X k)) : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  have e :
      ((ModuleCat.restrictScalars (algebraMap R A)).obj
        (((curriedTensor (ModuleCat.{u} A)).obj (K.X i)).obj
          (((CochainComplex.extendScalars (algebraMap R A)).obj P).X k)) : Type u)
        ≃ₗ[R] TensorProduct R ((K.X i) : Type u) ((P.X k) : Type u) :=
    (LinearEquiv.restrictScalars R
      ((TensorProduct.congr (LinearEquiv.refl A ((K.X i) : Type u))
          (extendScalarsCarrierEquiv R A (P.X k))).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A ((K.X i) : Type u) ((P.X k) :
            Type u))))
  exact LinearEquiv.toModuleIso e

/-- The per-summand projection-formula iso sends `k ⊗ₐ (a ⊗ᵣ q)` to `(a • k) ⊗ᵣ q`. -/
theorem restrictTensorLeftExtendSummandIso_hom_tmul (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i k : ℤ) (x : K.X i) (a : A) (q : P.X k) :
    (restrictTensorLeftExtendSummandIso R A K P i k).hom.hom (x ⊗ₜ[A] (a ⊗ₜ[R] q))
      = TensorProduct.tmul R
          (M := ((ModuleCat.restrictScalars (algebraMap R A)).obj (K.X i) : Type u))
          (a • x : K.X i) q := by
  let : Module R ((K.X i) : Type u) :=
    (inferInstance : Module R ((ModuleCat.restrictScalars (algebraMap R A)).obj (K.X i) : Type u))
  let : IsScalarTower R A ((K.X i) : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  change (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A ((K.X i) : Type u)
      ((P.X k) : Type u)) ((TensorProduct.congr (LinearEquiv.refl A ((K.X i) : Type u))
        (extendScalarsCarrierEquiv R A (P.X k))) (x ⊗ₜ[A] (a ⊗ₜ[R] q))) = (a • x) ⊗ₜ[R] q
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  change (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A ((K.X i) : Type u)
      ((P.X k) : Type u)) (x ⊗ₜ[A] (a ⊗ₜ[R] q)) = (a • x) ⊗ₜ[R] q
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

/-- **Per-degree component iso for the projection formula.** In each total degree `j`, the
restriction of the A-side total tensor complex `K ⊗_A (A ⊗_R P)` is `R`-linearly isomorphic to
the degree-`j` object of the R-side total tensor complex `(restrict K) ⊗_R P`. -/
noncomputable def restrictTensorLeftExtendComponentsIso (R A : Type u)
    [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ((CochainComplex.restrictScalars (algebraMap R A)).obj
        ((tensorLeft K).obj ((CochainComplex.extendScalars (algebraMap R A)).obj P))).X j
      ≅ ((tensorLeft ((CochainComplex.restrictScalars (algebraMap R A)).obj K)).obj P).X j := by
  let F := ModuleCat.restrictScalars (algebraMap R A)
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z : GradedObject (ℤ × ℤ) (ModuleCat.{u} A) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} A)) ℤ ℤ).obj K.X).obj
      ((CochainComplex.extendScalars (algebraMap R A)).obj P).X
  let Z' : GradedObject (ℤ × ℤ) (ModuleCat.{u} R) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
      ((CochainComplex.restrictScalars (algebraMap R A)).obj K).X).obj P.X
  exact IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves F (Z.isColimitCofanMapObj p j))
    (Z'.isColimitCofanMapObj p j) (Discrete.natIso fun x =>
      restrictTensorLeftExtendSummandIso R A K P x.as.1.1 x.as.1.2)

/-- **Colimit-injection interaction for the component iso.** The component iso `.hom`
(built as `IsColimit.coconePointsIsoOfNatIso` of the antidiagonal-fiber coproduct cofans)
intertwines the cofan injections `ιMapObj` on the two sides with the per-summand iso
`restrictTensorLeftExtendSummandIso`. -/
theorem restrictTensorLeftExtendComponentsIso_ι (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) :
    (ModuleCat.restrictScalars (algebraMap R A)).map
        ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} A)) ℤ ℤ).obj K.X).obj
            ((CochainComplex.extendScalars (algebraMap R A)).obj P).X).ιMapObj
            (fun x => x.1 + x.2) (i₁, i₂) j h)
        ≫ (restrictTensorLeftExtendComponentsIso R A K P j).hom
      = (restrictTensorLeftExtendSummandIso R A K P i₁ i₂).hom
        ≫ (((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
            ((CochainComplex.restrictScalars (algebraMap R A)).obj K).X).obj P.X).ιMapObj
              (fun x => x.1 + x.2) (i₁, i₂) j h := by
  unfold restrictTensorLeftExtendComponentsIso
  have key := IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves (ModuleCat.restrictScalars (algebraMap R A))
      ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} A)) ℤ ℤ).obj
          K.X).obj
        ((CochainComplex.extendScalars (algebraMap R A)).obj P).X).isColimitCofanMapObj
          (fun x => x.1 + x.2) j))
    ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
        ((CochainComplex.restrictScalars (algebraMap R A)).obj K).X).obj P.X).isColimitCofanMapObj
          (fun x => x.1 + x.2) j)
    (Discrete.natIso (fun x => restrictTensorLeftExtendSummandIso R A K P x.as.1.1 x.as.1.2))
    (Discrete.mk (⟨(i₁, i₂), h⟩ : ((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {j})))
  rw [Discrete.natIso_hom_app] at key
  exact key

/-- Two `R`-linear maps out of the restriction of `K_i ⊗_A (A ⊗_R P_k)` agree once they agree on
pure tensors `x ⊗ (a ⊗ q)`. -/
private theorem restrictScalars_tensor_extend_hom_ext (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i k : ℤ) {Y : ModuleCat.{u} R}
    (f g : (ModuleCat.restrictScalars (algebraMap R A)).obj
      (((curriedTensor (ModuleCat.{u} A)).obj (K.X i)).obj
        (((CochainComplex.extendScalars (algebraMap R A)).obj P).X k)) ⟶ Y)
    (h : ∀ (x : K.X i)
      (a : (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) (q : P.X k),
      f.hom (x ⊗ₜ[A] (a ⊗ₜ[R] q)) = g.hom (x ⊗ₜ[A] (a ⊗ₜ[R] q))) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x y =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd => rw [TensorProduct.tmul_add, map_add, map_add, hc, hd]
    | tmul a q => exact h x a q

/-- **d₁-square (naturality of the summand iso in the `K`-variable).** The per-summand
projection-formula iso `restrictTensorLeftExtendSummandIso` is natural with respect to
the (`A`-linear) `K`-differential `K.d i₁ i₁'` whiskered on the right by the `P`-factor. -/
theorem restrictTensorLeftExtendSummandIso_naturality_left (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i₁ i₁' i₂ : ℤ) :
    (restrictTensorLeftExtendSummandIso R A K P i₁ i₂).hom
        ≫ ((curriedTensor (ModuleCat.{u} R)).map
            ((ModuleCat.restrictScalars (algebraMap R A)).map (K.d i₁ i₁'))).app (P.X i₂)
      = (ModuleCat.restrictScalars (algebraMap R A)).map
          (((curriedTensor (ModuleCat.{u} A)).map (K.d i₁ i₁')).app
            (((CochainComplex.extendScalars (algebraMap R A)).obj P).X i₂))
        ≫ (restrictTensorLeftExtendSummandIso R A K P i₁' i₂).hom := by
  let : Module R ((K.X i₁) : Type u) :=
    (inferInstance : Module R ((ModuleCat.restrictScalars (algebraMap R A)).obj (K.X i₁) : Type u))
  let : Module R ((K.X i₁') : Type u) :=
    (inferInstance : Module R ((ModuleCat.restrictScalars (algebraMap R A)).obj (K.X i₁') : Type u))
  let hst1 : IsScalarTower R A ((K.X i₁) : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  let hst1' : IsScalarTower R A ((K.X i₁') : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  refine restrictScalars_tensor_extend_hom_ext R A K P _ _ _ _ ?_
  intro x a q
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hA : (ModuleCat.Hom.hom
        ((ModuleCat.restrictScalars (algebraMap R A)).map
          (((curriedTensor (ModuleCat.{u} A)).map (K.d i₁ i₁')).app
            (((CochainComplex.extendScalars (algebraMap R A)).obj P).X i₂))))
        (x ⊗ₜ[A] (a ⊗ₜ[R] q))
      = ((K.d i₁ i₁').hom x) ⊗ₜ[A] (a ⊗ₜ[R] q) :=
    ModuleCat.MonoidalCategory.whiskerRight_apply (K.d i₁ i₁')
      (((CochainComplex.extendScalars (algebraMap R A)).obj P).X i₂) x (a ⊗ₜ[R] q)
  have hR : (ModuleCat.Hom.hom
        (((curriedTensor (ModuleCat.{u} R)).map
            ((ModuleCat.restrictScalars (algebraMap R A)).map (K.d i₁ i₁'))).app (P.X i₂)))
        (((@id A a) • x) ⊗ₜ[R] q)
      = (((ModuleCat.restrictScalars (algebraMap R A)).map (K.d i₁ i₁')).hom ((@id A a) • x))
        ⊗ₜ[R] q :=
    ModuleCat.MonoidalCategory.whiskerRight_apply
      ((ModuleCat.restrictScalars (algebraMap R A)).map (K.d i₁ i₁')) (P.X i₂) ((@id A a) • x) q
  rw [restrictTensorLeftExtendSummandIso_hom_tmul, hA]
  exact hR.trans ((congrArg (· ⊗ₜ[R] q) (map_smul (K.d i₁ i₁').hom (@id A a) x)).trans
    (restrictTensorLeftExtendSummandIso_hom_tmul R A K P _ _ _ _ _).symm)

/-- **d₂-square (naturality of the summand iso in the `P`-variable).** The per-summand
projection-formula iso is natural with respect to the (`R`-linear) `P`-differential `P.d i₂ i₂'`
whiskered on the left by the `K`-factor. -/
theorem restrictTensorLeftExtendSummandIso_naturality_right (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i₁ i₂ i₂' : ℤ) :
    (restrictTensorLeftExtendSummandIso R A K P i₁ i₂).hom
        ≫ ((curriedTensor (ModuleCat.{u} R)).obj
            (((CochainComplex.restrictScalars (algebraMap R A)).obj K).X i₁)).map (P.d i₂ i₂')
      = (ModuleCat.restrictScalars (algebraMap R A)).map
          (((curriedTensor (ModuleCat.{u} A)).obj (K.X i₁)).map
            (((CochainComplex.extendScalars (algebraMap R A)).obj P).d i₂ i₂'))
        ≫ (restrictTensorLeftExtendSummandIso R A K P i₁ i₂').hom := by
  let : Module R ((K.X i₁) : Type u) :=
    (inferInstance : Module R ((ModuleCat.restrictScalars (algebraMap R A)).obj (K.X i₁) : Type u))
  let hst1 : IsScalarTower R A ((K.X i₁) : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  refine restrictScalars_tensor_extend_hom_ext R A K P _ _ _ _ ?_
  intro x a q
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hA : (ModuleCat.Hom.hom
        ((ModuleCat.restrictScalars (algebraMap R A)).map
          (((curriedTensor (ModuleCat.{u} A)).obj (K.X i₁)).map
            (((CochainComplex.extendScalars (algebraMap R A)).obj P).d i₂ i₂'))))
        (x ⊗ₜ[A] (a ⊗ₜ[R] q))
      = x ⊗ₜ[A] (a ⊗ₜ[R] ((P.d i₂ i₂').hom q)) := by
    have h1 := ModuleCat.MonoidalCategory.whiskerLeft_apply (K.X i₁)
      (((CochainComplex.extendScalars (algebraMap R A)).obj P).d i₂ i₂') x (a ⊗ₜ[R] q)
    have h2 : (ModuleCat.Hom.hom
          (((CochainComplex.extendScalars (algebraMap R A)).obj P).d i₂ i₂')) (a ⊗ₜ[R] q)
        = a ⊗ₜ[R] ((P.d i₂ i₂').hom q) :=
      ModuleCat.ExtendScalars.map_tmul (algebraMap R A) (P.d i₂ i₂') a q
    exact h1.trans (by rw [h2])
  have hR : (ModuleCat.Hom.hom
        (((curriedTensor (ModuleCat.{u} R)).obj
            (((CochainComplex.restrictScalars (algebraMap R A)).obj K).X i₁)).map (P.d i₂ i₂')))
        (((@id A a) • x) ⊗ₜ[R] q)
      = ((@id A a) • x) ⊗ₜ[R] ((P.d i₂ i₂').hom q) :=
    ModuleCat.MonoidalCategory.whiskerLeft_apply
      (((CochainComplex.restrictScalars (algebraMap R A)).obj K).X i₁) (P.d i₂ i₂')
      ((@id A a) • x) q
  rw [restrictTensorLeftExtendSummandIso_hom_tmul, hA]
  exact hR.trans (restrictTensorLeftExtendSummandIso_hom_tmul R A K P _ _ _ _ _).symm

/-- Differential compatibility of the `d₁`-parts, for a functor `F` and summand isos `s` that
commute with the colimit injections (`hι`) and are natural in the first variable (`hnat`). -/
private theorem d₁_comm_of_summands {S₁ S₂ : Type u} [CommRing S₁] [CommRing S₂]
    (F : ModuleCat.{u} S₁ ⥤ ModuleCat.{u} S₂) [F.Additive]
    (K Q : CochainComplex (ModuleCat.{u} S₁) ℤ) (K' Q' : CochainComplex (ModuleCat.{u} S₂) ℤ)
    (s : ∀ i₁ i₂ : ℤ, F.obj (((curriedTensor (ModuleCat.{u} S₁)).obj (K.X i₁)).obj (Q.X i₂)) ≅
      ((curriedTensor (ModuleCat.{u} S₂)).obj (K'.X i₁)).obj (Q'.X i₂))
    (c : ∀ j : ℤ, F.obj (((tensorLeft K).obj Q).X j) ⟶ ((tensorLeft K').obj Q').X j)
    (hι : ∀ i₁ i₂ j (h : i₁ + i₂ = j),
      F.map (HomologicalComplex.ιMapBifunctor K Q (curriedTensor (ModuleCat.{u} S₁))
        (ComplexShape.up ℤ) i₁ i₂ j h) ≫ c j
        = (s i₁ i₂).hom ≫ HomologicalComplex.ιMapBifunctor K' Q'
          (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ) i₁ i₂ j h)
    (hnat : ∀ i₁ i₁' i₂ : ℤ, (s i₁ i₂).hom ≫ ((curriedTensor (ModuleCat.{u} S₂)).map
          (K'.d i₁ i₁')).app (Q'.X i₂)
      = F.map (((curriedTensor (ModuleCat.{u} S₁)).map (K.d i₁ i₁')).app (Q.X i₂))
        ≫ (s i₁' i₂).hom)
    (i₁ i₂ j : ℤ) (hπ : i₁ + 1 + i₂ = j) :
    (s i₁ i₂).hom ≫ HomologicalComplex.mapBifunctor.d₁ K' Q'
        (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ) i₁ i₂ j
      = F.map (HomologicalComplex.mapBifunctor.d₁ K Q (curriedTensor (ModuleCat.{u} S₁))
          (ComplexShape.up ℤ) i₁ i₂ j) ≫ c j := by
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ rfl i₂ j hπ,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ rfl i₂ j hπ]
  rw [Linear.comp_units_smul, Functor.map_units_smul, Linear.units_smul_comp]
  refine congr_arg (_ • ·) ?_
  rw [Functor.map_comp, Category.assoc, hι, ← Category.assoc, ← Category.assoc, hnat]

/-- Differential compatibility of the `d₂`-parts, for a functor `F` and summand isos `s` that
commute with the colimit injections (`hι`) and are natural in the second variable (`hnat`). -/
private theorem d₂_comm_of_summands {S₁ S₂ : Type u} [CommRing S₁] [CommRing S₂]
    (F : ModuleCat.{u} S₁ ⥤ ModuleCat.{u} S₂) [F.Additive]
    (K Q : CochainComplex (ModuleCat.{u} S₁) ℤ) (K' Q' : CochainComplex (ModuleCat.{u} S₂) ℤ)
    (s : ∀ i₁ i₂ : ℤ, F.obj (((curriedTensor (ModuleCat.{u} S₁)).obj (K.X i₁)).obj (Q.X i₂)) ≅
      ((curriedTensor (ModuleCat.{u} S₂)).obj (K'.X i₁)).obj (Q'.X i₂))
    (c : ∀ j : ℤ, F.obj (((tensorLeft K).obj Q).X j) ⟶ ((tensorLeft K').obj Q').X j)
    (hι : ∀ i₁ i₂ j (h : i₁ + i₂ = j),
      F.map (HomologicalComplex.ιMapBifunctor K Q (curriedTensor (ModuleCat.{u} S₁))
        (ComplexShape.up ℤ) i₁ i₂ j h) ≫ c j
        = (s i₁ i₂).hom ≫ HomologicalComplex.ιMapBifunctor K' Q'
          (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ) i₁ i₂ j h)
    (hnat : ∀ i₁ i₂ i₂' : ℤ, (s i₁ i₂).hom ≫ ((curriedTensor (ModuleCat.{u} S₂)).obj
          (K'.X i₁)).map (Q'.d i₂ i₂')
      = F.map (((curriedTensor (ModuleCat.{u} S₁)).obj (K.X i₁)).map (Q.d i₂ i₂'))
        ≫ (s i₁ i₂').hom)
    (i₁ i₂ j : ℤ) (hπ : i₁ + (i₂ + 1) = j) :
    (s i₁ i₂).hom ≫ HomologicalComplex.mapBifunctor.d₂ K' Q'
        (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ) i₁ i₂ j
      = F.map (HomologicalComplex.mapBifunctor.d₂ K Q (curriedTensor (ModuleCat.{u} S₁))
          (ComplexShape.up ℤ) i₁ i₂ j) ≫ c j := by
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ i₁ rfl j hπ,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ i₁ rfl j hπ]
  rw [Linear.comp_units_smul, Functor.map_units_smul, Linear.units_smul_comp]
  refine congr_arg (_ • ·) ?_
  rw [Functor.map_comp, Category.assoc, hι, ← Category.assoc, ← Category.assoc, hnat]

/-- Differential compatibility of the component isos `c`, for a colimit-preserving functor `F`
and summand isos `s` compatible with the `d₁`- and `d₂`-parts of the total differentials. -/
private theorem comm_of_summands {S₁ S₂ : Type u} [CommRing S₁] [CommRing S₂]
    (F : ModuleCat.{u} S₁ ⥤ ModuleCat.{u} S₂) [F.Additive] [PreservesColimitsOfSize.{0, 0} F]
    (K Q : CochainComplex (ModuleCat.{u} S₁) ℤ) (K' Q' : CochainComplex (ModuleCat.{u} S₂) ℤ)
    (s : ∀ i₁ i₂ : ℤ, F.obj (((curriedTensor (ModuleCat.{u} S₁)).obj (K.X i₁)).obj (Q.X i₂)) ≅
      ((curriedTensor (ModuleCat.{u} S₂)).obj (K'.X i₁)).obj (Q'.X i₂))
    (c : ∀ j : ℤ, F.obj (((tensorLeft K).obj Q).X j) ⟶ ((tensorLeft K').obj Q').X j)
    (hι : ∀ i₁ i₂ j (h : i₁ + i₂ = j),
      F.map (HomologicalComplex.ιMapBifunctor K Q (curriedTensor (ModuleCat.{u} S₁))
        (ComplexShape.up ℤ) i₁ i₂ j h) ≫ c j
        = (s i₁ i₂).hom ≫ HomologicalComplex.ιMapBifunctor K' Q'
          (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ) i₁ i₂ j h)
    (hd₁ : ∀ i₁ i₂ j : ℤ, i₁ + 1 + i₂ = j →
      (s i₁ i₂).hom ≫ HomologicalComplex.mapBifunctor.d₁ K' Q'
          (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ) i₁ i₂ j
        = F.map (HomologicalComplex.mapBifunctor.d₁ K Q (curriedTensor (ModuleCat.{u} S₁))
          (ComplexShape.up ℤ) i₁ i₂ j) ≫ c j)
    (hd₂ : ∀ i₁ i₂ j : ℤ, i₁ + (i₂ + 1) = j →
      (s i₁ i₂).hom ≫ HomologicalComplex.mapBifunctor.d₂ K' Q'
          (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ) i₁ i₂ j
        = F.map (HomologicalComplex.mapBifunctor.d₂ K Q (curriedTensor (ModuleCat.{u} S₁))
          (ComplexShape.up ℤ) i₁ i₂ j) ≫ c j)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    c i ≫ ((tensorLeft K').obj Q').d i j = F.map (((tensorLeft K).obj Q).d i j) ≫ c j := by
  refine IsColimit.hom_ext (isColimitOfPreserves F
    ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} S₁)) ℤ ℤ).obj K.X).obj
      Q.X).isColimitCofanMapObj (fun x => x.1 + x.2) i)) (fun b => ?_)
  obtain ⟨⟨i₁, i₂⟩, (hb : i₁ + i₂ = i)⟩ := b
  have hj : i + 1 = j := hij
  change F.map (HomologicalComplex.ιMapBifunctor K Q (curriedTensor (ModuleCat.{u} S₁))
      (ComplexShape.up ℤ) i₁ i₂ i hb) ≫ c i ≫ ((tensorLeft K').obj Q').d i j
    = F.map (HomologicalComplex.ιMapBifunctor K Q (curriedTensor (ModuleCat.{u} S₁))
      (ComplexShape.up ℤ) i₁ i₂ i hb) ≫ F.map (((tensorLeft K).obj Q).d i j) ≫ c j
  rw [← Category.assoc, hι, ← Functor.map_comp_assoc, Category.assoc]
  change (s i₁ i₂).hom ≫ (HomologicalComplex.ιMapBifunctor K' Q'
        (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ) i₁ i₂ i hb ≫
      (HomologicalComplex.mapBifunctor K' Q'
        (curriedTensor (ModuleCat.{u} S₂)) (ComplexShape.up ℤ)).d i j)
    = F.map (HomologicalComplex.ιMapBifunctor K Q (curriedTensor (ModuleCat.{u} S₁))
        (ComplexShape.up ℤ) i₁ i₂ i hb ≫
      (HomologicalComplex.mapBifunctor K Q (curriedTensor (ModuleCat.{u} S₁))
        (ComplexShape.up ℤ)).d i j) ≫ c j
  rw [HomologicalComplex.mapBifunctor.d_eq, HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂, Functor.map_add, Preadditive.add_comp]
  exact congr_arg₂ (· + ·) (hd₁ i₁ i₂ j (by omega)) (hd₂ i₁ i₂ j (by omega))

/-- The `d₁`-part (the `K`-differential) of the total differential commutes with the
projection-formula component isos. -/
theorem restrictTensorLeftExtendIso_d₁_comm (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i₁ i₂ j : ℤ) (hπ : i₁ + 1 + i₂ = j) :
    (restrictTensorLeftExtendSummandIso R A K P i₁ i₂).hom ≫
        HomologicalComplex.mapBifunctor.d₁
          ((CochainComplex.restrictScalars (algebraMap R A)).obj K) P
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) i₁ i₂ j =
      (ModuleCat.restrictScalars (algebraMap R A)).map
          (HomologicalComplex.mapBifunctor.d₁ K
            ((CochainComplex.extendScalars (algebraMap R A)).obj P)
            (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) i₁ i₂ j) ≫
        (restrictTensorLeftExtendComponentsIso R A K P j).hom := by
  exact d₁_comm_of_summands (ModuleCat.restrictScalars (algebraMap R A)) K
    ((CochainComplex.extendScalars (algebraMap R A)).obj P)
    ((CochainComplex.restrictScalars (algebraMap R A)).obj K) P
    (restrictTensorLeftExtendSummandIso R A K P)
    (fun j => (restrictTensorLeftExtendComponentsIso R A K P j).hom)
    (restrictTensorLeftExtendComponentsIso_ι R A K P)
    (restrictTensorLeftExtendSummandIso_naturality_left R A K P) i₁ i₂ j hπ

/-- The `d₂`-part (the `P`-differential) of the total differential commutes with the
projection-formula component isos. -/
theorem restrictTensorLeftExtendIso_d₂_comm (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i₁ i₂ j : ℤ) (hπ : i₁ + (i₂ + 1) = j) :
    (restrictTensorLeftExtendSummandIso R A K P i₁ i₂).hom ≫
        HomologicalComplex.mapBifunctor.d₂
          ((CochainComplex.restrictScalars (algebraMap R A)).obj K) P
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) i₁ i₂ j =
      (ModuleCat.restrictScalars (algebraMap R A)).map
          (HomologicalComplex.mapBifunctor.d₂ K
            ((CochainComplex.extendScalars (algebraMap R A)).obj P)
            (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) i₁ i₂ j) ≫
        (restrictTensorLeftExtendComponentsIso R A K P j).hom := by
  exact d₂_comm_of_summands (ModuleCat.restrictScalars (algebraMap R A)) K
    ((CochainComplex.extendScalars (algebraMap R A)).obj P)
    ((CochainComplex.restrictScalars (algebraMap R A)).obj K) P
    (restrictTensorLeftExtendSummandIso R A K P)
    (fun j => (restrictTensorLeftExtendComponentsIso R A K P j).hom)
    (restrictTensorLeftExtendComponentsIso_ι R A K P)
    (restrictTensorLeftExtendSummandIso_naturality_right R A K P) i₁ i₂ j hπ

/-- The degreewise isomorphisms `restrictTensorLeftExtendComponentsIso` between
`restrictScalars (K ⊗_A (A ⊗_R P))` and `restrictScalars K ⊗_R P` commute with the
differentials. -/
theorem restrictTensorLeftExtendIso_comm (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (restrictTensorLeftExtendComponentsIso R A K P i).hom
        ≫ ((tensorLeft ((CochainComplex.restrictScalars (algebraMap R A)).obj K)).obj P).d i j
      = ((CochainComplex.restrictScalars (algebraMap R A)).obj ((tensorLeft K).obj
          ((CochainComplex.extendScalars (algebraMap R A)).obj P))).d i j
        ≫ (restrictTensorLeftExtendComponentsIso R A K P j).hom := by
  exact comm_of_summands (ModuleCat.restrictScalars (algebraMap R A)) K
    ((CochainComplex.extendScalars (algebraMap R A)).obj P)
    ((CochainComplex.restrictScalars (algebraMap R A)).obj K) P
    (restrictTensorLeftExtendSummandIso R A K P)
    (fun j => (restrictTensorLeftExtendComponentsIso R A K P j).hom)
    (restrictTensorLeftExtendComponentsIso_ι R A K P)
    (fun i₁ i₂ j hπ => restrictTensorLeftExtendIso_d₁_comm R A K P i₁ i₂ j hπ)
    (fun i₁ i₂ j hπ => restrictTensorLeftExtendIso_d₂_comm R A K P i₁ i₂ j hπ) i j hij

/-- For a complex `K` of `A`-modules and a complex `P` of `R`-modules, the restriction of scalars
of `K ⊗_A (A ⊗_R P)` to `R` is isomorphic to `restrictScalars K ⊗_R P`. -/
noncomputable def restrictTensorLeftExtendIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CochainComplex.restrictScalars (algebraMap R A)).obj
        ((tensorLeft K).obj ((CochainComplex.extendScalars (algebraMap R A)).obj P))
      ≅ (tensorLeft ((CochainComplex.restrictScalars (algebraMap R A)).obj K)).obj P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => restrictTensorLeftExtendComponentsIso R A K P j)
    (fun i j hij => restrictTensorLeftExtendIso_comm R A K P i j hij)

/-- Restricting `derivedTensorHomologyA R A K M i` along `R → A` gives the `i`-th cohomology of
the derived tensor product of `K`, viewed as a complex of `R`-modules, with `M`. -/
noncomputable def derivedTensorHomologyARestrictIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (K : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} R) (i : ℤ) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (derivedTensorHomologyA R A K M i)
      ≅ derivedTensorHomology ((CochainComplex.restrictScalars (algebraMap R A)).obj K) M i := by
  set D : CochainComplex (ModuleCat.{u} A) ℤ :=
    (tensorLeft K).obj
      ((CochainComplex.extendScalars (algebraMap R A)).obj (projResComplex M))
  -- `((F.mapHomologicalComplex c).obj D).sc i = (D.sc i).map F` definitionally.
  have e1 :
      (ModuleCat.restrictScalars (algebraMap R A)).obj (D.homology i)
        ≅ ((CochainComplex.restrictScalars (algebraMap R A)).obj D).homology i :=
    (ShortComplex.mapHomologyIso (D.sc i) (ModuleCat.restrictScalars (algebraMap R A))).symm
  exact e1 ≪≫ (HomologicalComplex.homologyFunctor _ _ i).mapIso
    (restrictTensorLeftExtendIso R A K (projResComplex M))

/-- Extension of scalars is an additive functor. -/
private theorem additive_extendScalars (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Functor.Additive
      (ModuleCat.extendScalars (algebraMap A B) : ModuleCat.{u} A ⥤ ModuleCat.{u} B) :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).left_adjoint_additive

section ExtendTensorLeft

/-- Per-degree component iso: applying `extendScalars (A→B)` (lifted to complexes) to the total
tensor complex `K ⊗_A Q` agrees, in each degree, with the total tensor complex of the extended
factors, via the strong-monoidal comparison `μIso`. -/
noncomputable def extendTensorLeftComponentsIso (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (K Q : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ) :
    ((CochainComplex.extendScalars (algebraMap A B)).obj ((tensorLeft K).obj Q)).X j
      ≅ ((tensorLeft ((CochainComplex.extendScalars (algebraMap A B)).obj K)).obj
          ((CochainComplex.extendScalars (algebraMap A B)).obj Q)).X j := by
  let G := ModuleCat.extendScalars (algebraMap A B)
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z : GradedObject (ℤ × ℤ) (ModuleCat.{u} A) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} A)) ℤ ℤ).obj
        K.X).obj Q.X
  let Z' : GradedObject (ℤ × ℤ) (ModuleCat.{u} B) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} B)) ℤ ℤ).obj
      ((CochainComplex.extendScalars (algebraMap A B)).obj K).X).obj
        ((CochainComplex.extendScalars (algebraMap A B)).obj Q).X
  exact IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves G (Z.isColimitCofanMapObj p j))
    (Z'.isColimitCofanMapObj p j) (Discrete.natIso fun x =>
      (Functor.Monoidal.μIso G (K.X x.as.1.1) (Q.X x.as.1.2)).symm)

/-- Colimit-injection interaction for the component iso (analogue of
`restrictTensorLeftExtendComponentsIso_ι`). -/
theorem extendTensorLeftComponentsIso_ι (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (K Q : CochainComplex (ModuleCat.{u} A) ℤ) (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) :
    (ModuleCat.extendScalars (algebraMap A B)).map
        ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} A)) ℤ ℤ).obj K.X).obj
            Q.X).ιMapObj (fun x => x.1 + x.2) (i₁, i₂) j h)
        ≫ (extendTensorLeftComponentsIso A B K Q j).hom
      = (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B)) (K.X i₁)
          (Q.X i₂)).symm.hom
        ≫ (((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} B)) ℤ ℤ).obj
            ((CochainComplex.extendScalars (algebraMap A B)).obj K).X).obj
              ((CochainComplex.extendScalars (algebraMap A B)).obj Q).X).ιMapObj
              (fun x => x.1 + x.2) (i₁, i₂) j h := by
  unfold extendTensorLeftComponentsIso
  have key := IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves (ModuleCat.extendScalars (algebraMap A B))
      ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} A)) ℤ ℤ).obj
          K.X).obj
        Q.X).isColimitCofanMapObj (fun x => x.1 + x.2) j))
    ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} B)) ℤ ℤ).obj
        ((CochainComplex.extendScalars (algebraMap A B)).obj K).X).obj
          ((CochainComplex.extendScalars (algebraMap A B)).obj Q).X).isColimitCofanMapObj
          (fun x => x.1 + x.2) j)
    (Discrete.natIso (fun x => (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B))
      (K.X x.as.1.1) (Q.X x.as.1.2)).symm))
    (Discrete.mk (⟨(i₁, i₂), h⟩ : ((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {j})))
  rw [Discrete.natIso_hom_app] at key
  exact key

/-- d₁-square: naturality of `μ` in the left (`K`) variable (`μ_natural_left`). -/
theorem extendTensorLeftIso_naturality_left (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K Q : CochainComplex (ModuleCat.{u} A) ℤ) (i₁ i₁' i₂ : ℤ) :
    (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B)) (K.X i₁) (Q.X i₂)).symm.hom
        ≫ ((curriedTensor (ModuleCat.{u} B)).map
            (((CochainComplex.extendScalars (algebraMap A B)).obj K).d i₁ i₁')).app
              (((CochainComplex.extendScalars (algebraMap A B)).obj Q).X i₂)
      = (ModuleCat.extendScalars (algebraMap A B)).map
          (((curriedTensor (ModuleCat.{u} A)).map (K.d i₁ i₁')).app (Q.X i₂))
        ≫ (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B))
            (K.X i₁') (Q.X i₂)).symm.hom := by
  set G := ModuleCat.extendScalars (algebraMap A B)
  change (Functor.Monoidal.μIso G (K.X i₁) (Q.X i₂)).inv ≫ (G.map (K.d i₁ i₁') ▷ G.obj (Q.X i₂))
      = G.map (K.d i₁ i₁' ▷ Q.X i₂) ≫ (Functor.Monoidal.μIso G (K.X i₁') (Q.X i₂)).inv
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact Functor.LaxMonoidal.μ_natural_left G (K.d i₁ i₁') (Q.X i₂)

/-- d₂-square: naturality of `μ` in the right (`Q`) variable (`μ_natural_right`). -/
theorem extendTensorLeftIso_naturality_right (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K Q : CochainComplex (ModuleCat.{u} A) ℤ) (i₁ i₂ i₂' : ℤ) :
    (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B)) (K.X i₁) (Q.X i₂)).symm.hom
        ≫ ((curriedTensor (ModuleCat.{u} B)).obj
            (((CochainComplex.extendScalars (algebraMap A B)).obj K).X i₁)).map
              (((CochainComplex.extendScalars (algebraMap A B)).obj Q).d i₂ i₂')
      = (ModuleCat.extendScalars (algebraMap A B)).map
          (((curriedTensor (ModuleCat.{u} A)).obj (K.X i₁)).map (Q.d i₂ i₂'))
        ≫ (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B))
            (K.X i₁) (Q.X i₂')).symm.hom := by
  set G := ModuleCat.extendScalars (algebraMap A B)
  change (Functor.Monoidal.μIso G (K.X i₁) (Q.X i₂)).inv ≫ (G.obj (K.X i₁) ◁ G.map (Q.d i₂ i₂'))
      = G.map (K.X i₁ ◁ Q.d i₂ i₂') ≫ (Functor.Monoidal.μIso G (K.X i₁) (Q.X i₂')).inv
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact Functor.LaxMonoidal.μ_natural_right G (K.X i₁) (Q.d i₂ i₂')

/-- The `d₁`-part of the total differential commutes with the base-change component isos. -/
theorem extendTensorLeftIso_d₁_comm (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K Q : CochainComplex (ModuleCat.{u} A) ℤ) (i₁ i₂ j : ℤ) (hπ : i₁ + 1 + i₂ = j) :
    (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B)) (K.X i₁) (Q.X i₂)).symm.hom
        ≫ HomologicalComplex.mapBifunctor.d₁ ((CochainComplex.extendScalars (algebraMap A B)).obj K)
          ((CochainComplex.extendScalars (algebraMap A B)).obj Q)
          (curriedTensor (ModuleCat.{u} B)) (ComplexShape.up ℤ) i₁ i₂ j =
      (ModuleCat.extendScalars (algebraMap A B)).map
          (HomologicalComplex.mapBifunctor.d₁ K Q (curriedTensor (ModuleCat.{u} A))
            (ComplexShape.up ℤ) i₁ i₂ j) ≫
        (extendTensorLeftComponentsIso A B K Q j).hom := by
  have := additive_extendScalars A B
  exact d₁_comm_of_summands (ModuleCat.extendScalars (algebraMap A B)) K Q
    ((CochainComplex.extendScalars (algebraMap A B)).obj K)
    ((CochainComplex.extendScalars (algebraMap A B)).obj Q)
    (fun i₁ i₂ => (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B)) (K.X i₁)
      (Q.X i₂)).symm)
    (fun j => (extendTensorLeftComponentsIso A B K Q j).hom)
    (extendTensorLeftComponentsIso_ι A B K Q)
    (extendTensorLeftIso_naturality_left A B K Q) i₁ i₂ j hπ

/-- The `d₂`-part of the total differential commutes with the base-change component isos. -/
theorem extendTensorLeftIso_d₂_comm (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K Q : CochainComplex (ModuleCat.{u} A) ℤ) (i₁ i₂ j : ℤ) (hπ : i₁ + (i₂ + 1) = j) :
    (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B)) (K.X i₁) (Q.X i₂)).symm.hom
        ≫ HomologicalComplex.mapBifunctor.d₂ ((CochainComplex.extendScalars (algebraMap A B)).obj K)
          ((CochainComplex.extendScalars (algebraMap A B)).obj Q)
          (curriedTensor (ModuleCat.{u} B)) (ComplexShape.up ℤ) i₁ i₂ j =
      (ModuleCat.extendScalars (algebraMap A B)).map
          (HomologicalComplex.mapBifunctor.d₂ K Q (curriedTensor (ModuleCat.{u} A))
            (ComplexShape.up ℤ) i₁ i₂ j) ≫
        (extendTensorLeftComponentsIso A B K Q j).hom := by
  have := additive_extendScalars A B
  exact d₂_comm_of_summands (ModuleCat.extendScalars (algebraMap A B)) K Q
    ((CochainComplex.extendScalars (algebraMap A B)).obj K)
    ((CochainComplex.extendScalars (algebraMap A B)).obj Q)
    (fun i₁ i₂ => (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B)) (K.X i₁)
      (Q.X i₂)).symm)
    (fun j => (extendTensorLeftComponentsIso A B K Q j).hom)
    (extendTensorLeftComponentsIso_ι A B K Q)
    (extendTensorLeftIso_naturality_right A B K Q) i₁ i₂ j hπ

/-- Differential compatibility of the component isos (analogue of
`restrictTensorLeftExtendIso_comm`). -/
theorem extendTensorLeftIso_comm (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K Q : CochainComplex (ModuleCat.{u} A) ℤ) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (extendTensorLeftComponentsIso A B K Q i).hom
        ≫ ((tensorLeft ((CochainComplex.extendScalars (algebraMap A B)).obj K)).obj
            ((CochainComplex.extendScalars (algebraMap A B)).obj Q)).d i j
      = ((CochainComplex.extendScalars (algebraMap A B)).obj ((tensorLeft K).obj Q)).d i j
        ≫ (extendTensorLeftComponentsIso A B K Q j).hom := by
  have := additive_extendScalars A B
  exact comm_of_summands (ModuleCat.extendScalars (algebraMap A B)) K Q
    ((CochainComplex.extendScalars (algebraMap A B)).obj K)
    ((CochainComplex.extendScalars (algebraMap A B)).obj Q)
    (fun i₁ i₂ => (Functor.Monoidal.μIso (ModuleCat.extendScalars (algebraMap A B)) (K.X i₁)
      (Q.X i₂)).symm)
    (fun j => (extendTensorLeftComponentsIso A B K Q j).hom)
    (extendTensorLeftComponentsIso_ι A B K Q)
    (fun i₁ i₂ j hπ => extendTensorLeftIso_d₁_comm A B K Q i₁ i₂ j hπ)
    (fun i₁ i₂ j hπ => extendTensorLeftIso_d₂_comm A B K Q i₁ i₂ j hπ) i j hij

/-- **Monoidal base-change complex iso.** `extendScalars (A→B)` lifted to cochain complexes
commutes with `tensorLeft`: `extend (K ⊗_A Q) ≅ (extend K) ⊗_B (extend Q)`. -/
noncomputable def extendTensorLeftIso (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    (CochainComplex.extendScalars (algebraMap A B)).obj ((tensorLeft K).obj Q)
      ≅ (tensorLeft ((CochainComplex.extendScalars (algebraMap A B)).obj K)).obj
          ((CochainComplex.extendScalars (algebraMap A B)).obj Q) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => extendTensorLeftComponentsIso A B K Q j)
    (fun i j hij => extendTensorLeftIso_comm A B K Q i j hij)

/-- **Scalar-tower identity for `CochainComplex.extendScalars`.**
`extend (R→B) P ≅ extend (A→B) (extend (R→A) P)`
as cochain complexes, from `ModuleCat.extendScalarsComp` and `IsScalarTower`. -/
noncomputable def extendComplexTowerIso (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CochainComplex.extendScalars (algebraMap R B)).obj P
      ≅ (CochainComplex.extendScalars (algebraMap A B)).obj
        ((CochainComplex.extendScalars (algebraMap R A)).obj P) := by
  let e : (ModuleCat.extendScalars (algebraMap R B)) ≅
      (ModuleCat.extendScalars (algebraMap R A)) ⋙ (ModuleCat.extendScalars (algebraMap A B)) := by
    rw [IsScalarTower.algebraMap_eq R A B]
    exact ModuleCat.extendScalarsComp (algebraMap R A) (algebraMap A B)
  exact (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P

end ExtendTensorLeft

/-- The `R`-side derived-tensor homology of the base change
`(CochainComplex.extendScalars (algebraMap A B)) K` is isomorphic to the restriction to `R` of the
`extendScalars (A→B)` of the `A`-module lift `derivedTensorHomologyA R A K M i`. -/
noncomputable def derivedTensorHomologyBIso (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.Flat A B] (K : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} R) (i : ℤ) :
    derivedTensorHomology
        ((CochainComplex.restrictScalars (algebraMap R B)).obj
          ((CochainComplex.extendScalars (algebraMap A B)).obj K)) M i
      ≅ (ModuleCat.restrictScalars (algebraMap R B)).obj
          ((ModuleCat.extendScalars (algebraMap A B)).obj (derivedTensorHomologyA R A K M i)) := by
  set P := projResComplex M
  set G := ModuleCat.extendScalars (algebraMap A B)
  set ResB := ModuleCat.restrictScalars (algebraMap R B)
  have : G.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).left_adjoint_additive
  have : Limits.PreservesFiniteLimits G :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A B›)
  have : G.PreservesHomology := Functor.preservesHomologyOfExact G
  set D : CochainComplex (ModuleCat.{u} A) ℤ :=
    (tensorLeft K).obj ((CochainComplex.extendScalars (algebraMap R A)).obj P)
  have eHomG : G.obj (D.homology i)
      ≅ ((CochainComplex.extendScalars (algebraMap A B)).obj D).homology i :=
    (ShortComplex.mapHomologyIso (D.sc i) G).symm
  have eHomRes :
      ResB.obj (((CochainComplex.extendScalars (algebraMap A B)).obj D).homology i)
        ≅ ((CochainComplex.restrictScalars (algebraMap R B)).obj
            ((CochainComplex.extendScalars (algebraMap A B)).obj D)).homology i :=
    (ShortComplex.mapHomologyIso
      (((CochainComplex.extendScalars (algebraMap A B)).obj D).sc i) ResB).symm
  let e1 := restrictTensorLeftExtendIso R B
    ((CochainComplex.extendScalars (algebraMap A B)).obj K) P
  let e2 := extendTensorLeftIso A B K ((CochainComplex.extendScalars (algebraMap R A)).obj P)
  let eStep2 :
      (tensorLeft ((CochainComplex.extendScalars (algebraMap A B)).obj K)).obj
        ((CochainComplex.extendScalars (algebraMap R B)).obj P)
        ≅ (CochainComplex.extendScalars (algebraMap A B)).obj D :=
    ((tensorLeft ((CochainComplex.extendScalars (algebraMap A B)).obj K)).mapIso
      (extendComplexTowerIso R A B P))
      ≪≫ e2.symm
  let eComplex :
      (tensorLeft ((CochainComplex.restrictScalars (algebraMap R B)).obj
          ((CochainComplex.extendScalars (algebraMap A B)).obj K))).obj P
        ≅ (CochainComplex.restrictScalars (algebraMap R B)).obj
            ((CochainComplex.extendScalars (algebraMap A B)).obj D) :=
    e1.symm ≪≫ (CochainComplex.restrictScalars (algebraMap R B)).mapIso eStep2
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      eComplex
    ≪≫ eHomRes.symm ≪≫ ResB.mapIso eHomG.symm

/-! ## Comparison with Mathlib's `Tor`

When the first argument is a module placed in degree `0`, `derivedTensorHomology` is Mathlib's
`Tor`. -/

/-- In the total tensor complex `single₀ N ⊗ C`, the antidiagonal summand `(i₁, i₂)` is the zero
object whenever `i₁ ≠ 0`. -/
theorem isZero_single_tensorLeft_summand {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (i₁ i₂ : ℤ) (h : i₁ ≠ 0) :
    Limits.IsZero
      ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X).obj C.X) (i₁, i₂)) := by
  have hz : Limits.IsZero (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X i₁) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N i₁ h
  change Limits.IsZero (((curriedTensor (ModuleCat.{u} R)).obj
      (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X i₁)).obj (C.X i₂))
  rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
  have : Subsingleton (TensorProduct R (↥(((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      N).X i₁)) (↥(C.X i₂))) :=
    Unique.instSubsingleton
  exact this

/-- The `(0, j)` antidiagonal summand of `single₀ N ⊗ C` equals the degree-`j` object of the
degreewise complex `(tensorLeft N).mapHomologicalComplex C`. -/
theorem single_tensorLeft_mapObjFun_eq {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ)
    (b : ↑((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {j})) (hi : b.1.1 = 0) :
    (((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X).obj C.X).mapObjFun
        (fun x => x.1 + x.2) j b
    = (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X j := by
  obtain ⟨⟨i₁, i₂⟩, hb⟩ := b
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
  simp only at hi
  subst hi
  have : i₂ = j := by omega
  subst this
  rfl

/-- Per-degree component iso: the colimit-collapse of the antidiagonal coproduct
(all summands but `(0, j)` are zero) identifies `(single₀ N ⊗ C).X j` with `(N ⊗ C.X j)`. -/
noncomputable def singleTensorLeftComponentsIso {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (C : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ((tensorLeft ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).obj C).X j
      ≅ (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X j := by
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z : GradedObject (ℤ × ℤ) (ModuleCat.{u} R) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X).obj C.X
  let RHS : ModuleCat.{u} R := (((tensorLeft N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C).X j
  have iLHS : IsColimit (Z.cofanMapObj p j) := Z.isColimitCofanMapObj p j
  have h0 : p (0, j) = j := by change (0:ℤ) + j = j; ring
  let injFn : (b : ↑(p ⁻¹' {j})) → Z.mapObjFun p j b ⟶ RHS :=
    fun b => if hi : b.1.1 = 0 then eqToHom (single_tensorLeft_mapObjFun_eq N C j b hi) else 0
  refine
    { hom := Cofan.IsColimit.desc iLHS injFn
      inv := Z.ιMapObj p (0, j) j h0
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Cofan.IsColimit.hom_ext iLHS
    intro b
    rw [← Category.assoc, Cofan.IsColimit.fac iLHS injFn b]
    erw [Category.comp_id]
    by_cases hi : b.1.1 = 0
    · obtain ⟨⟨i₁, i₂⟩, hb⟩ := b
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
      dsimp only [p] at hb
      simp only at hi
      subst hi
      have hj : i₂ = j := by omega
      subst hj
      change injFn ⟨(0,i₂), _⟩ ≫ Z.ιMapObj p (0, i₂) i₂ h0 = (Z.cofanMapObj p i₂).inj ⟨(0,i₂), _⟩
      simp only [injFn, dite_eq_left]
      rw [show (eqToHom (single_tensorLeft_mapObjFun_eq N C i₂ ⟨(0,i₂), hb⟩ rfl)) = 𝟙 _ from rfl,
          Category.id_comp]
      rfl
    · exact (isZero_single_tensorLeft_summand N C b.1.1 b.1.2 hi).eq_of_src _ _
  · rw [show Z.ιMapObj p (0, j) j h0 = (Z.cofanMapObj p j).inj ⟨(0,j), h0⟩ from rfl,
      Cofan.IsColimit.fac iLHS injFn ⟨(0,j), h0⟩]
    change injFn ⟨(0,j), h0⟩ = 𝟙 RHS
    simp only [injFn, dite_eq_left]
    rfl

/-- Differential compatibility: the per-degree component isos
`singleTensorLeftComponentsIso` commute with the total differential of `single₀ N ⊗ C` (whose
`d₁` part vanishes, the single complex having zero differential) and the degreewise differential of
`(tensorLeft N).mapHomologicalComplex C` (the `d₂` part with Koszul sign `ε₂(0,·)=1`). -/
theorem singleTensorLeftComponentsIso_comm {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (singleTensorLeftComponentsIso N C i).hom ≫ (((tensorLeft N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).d i j
      = ((tensorLeft ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          N)).obj C).d i j
        ≫ (singleTensorLeftComponentsIso N C j).hom := by
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z : GradedObject (ℤ × ℤ) (ModuleCat.{u} R) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N).X).obj C.X
  refine Cofan.IsColimit.hom_ext (Z.isColimitCofanMapObj p i) _ _ fun b => ?_
  by_cases hi : b.1.1 = 0
  · obtain ⟨⟨i₁, i₂⟩, hb⟩ := b
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
    dsimp only [p] at hb
    simp only at hi
    subst hi
    have hi2 : i₂ = i := by omega
    subst hi2
    have hjv : i₂ + 1 = j := hij
    subst hjv
    rw [← Category.assoc]
    have hL : (Z.cofanMapObj p i₂).inj ⟨(0,i₂), hb⟩
        ≫ (singleTensorLeftComponentsIso N C i₂).hom = 𝟙 _ :=
      (singleTensorLeftComponentsIso N C i₂).inv_hom_id
    rw [hL, Category.id_comp, ← Category.assoc]
    have hR : (Z.cofanMapObj p i₂).inj ⟨(0,i₂), hb⟩
        ≫ ((tensorLeft ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            N)).obj C).d i₂ (i₂+1)
      = HomologicalComplex.ιMapBifunctor ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)
          C
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) 0 i₂ i₂ hb
        ≫ (HomologicalComplex.mapBifunctor ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            N) C
            (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).d i₂ (i₂+1) :=
                rfl
    rw [hR]
    have hrel1 : (ComplexShape.up ℤ).Rel (0:ℤ) 1 := rfl
    have hrel2 : (ComplexShape.up ℤ).Rel i₂ (i₂+1) := rfl
    have hπ1 :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ((0:ℤ)+1, i₂) = i₂+1 := by
      change (1:ℤ) + i₂ = i₂+1; ring
    have hπ2 :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ((0:ℤ), i₂+1) = i₂+1 := by
      change (0:ℤ) + (i₂+1) = i₂+1; ring
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
        HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hrel1 i₂ (i₂+1) hπ1,
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0 hrel2 (i₂+1) hπ2]
    rw [CochainComplex.singleFunctor_obj_d N 0 0 1]
    simp only [Functor.map_zero, Limits.zero_app, Limits.zero_comp, smul_zero, zero_add]
    rw [show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (0, i₂) = 1 from rfl,
        one_smul, Category.assoc,
      show HomologicalComplex.ιMapBifunctor ((CochainComplex.singleFunctor (ModuleCat.{u} R)
        0).obj N) C
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) 0 (i₂+1) (i₂+1) hπ2
        ≫ (singleTensorLeftComponentsIso N C (i₂+1)).hom = 𝟙 _
        from (singleTensorLeftComponentsIso N C (i₂+1)).inv_hom_id,
      Category.comp_id]
    rfl
  · exact (isZero_single_tensorLeft_summand N C b.1.1 b.1.2 hi).eq_of_src _ _

/-- Tensoring a complex `C` on the left with the module `N` placed in degree `0` is isomorphic
to applying `N ⊗ -` to `C` degreewise. -/
noncomputable def singleTensorLeftMapHomologicalComplexIso {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorLeft ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).obj C
      ≅ ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C :=
  HomologicalComplex.Hom.isoOfComponents (fun j => singleTensorLeftComponentsIso N C j)
    (fun i j hij => singleTensorLeftComponentsIso_comm N C i j hij)

/-- In each degree `i'`, applying `(tensorLeft N).mapHomologicalComplex` to
`K.extend ComplexShape.embeddingDownNat` is isomorphic to the degree-`i'` object of the extension
of the degreewise image. -/
noncomputable def mapHomologicalComplexExtendXIso {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (K : ChainComplex (ModuleCat.{u} R) ℕ) (i' : ℤ) :
    (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat)).X i'
      ≅ ((((tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extend
          ComplexShape.embeddingDownNat).X i' :=
  match h : ComplexShape.embeddingDownNat.r i' with
  | some i =>
      (tensorLeft N).mapIso
          (K.extendXIso ComplexShape.embeddingDownNat (ComplexShape.Embedding.f_eq_of_r_eq_some _
              h)) ≪≫
        ((((tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            K).extendXIso
            ComplexShape.embeddingDownNat (ComplexShape.Embedding.f_eq_of_r_eq_some _ h)).symm
  | none =>
      (by
        have hz : IsZero ((K.extend ComplexShape.embeddingDownNat).X i') := by
          rw [show (K.extend ComplexShape.embeddingDownNat).X i'
                = HomologicalComplex.extend.X K (ComplexShape.embeddingDownNat.r i') from rfl, h]
          exact isZero_zero _
        haveI : (tensorLeft N).Additive := inferInstance
        exact ((tensorLeft N).map_isZero hz).iso
          (by rw [show ((((tensorLeft N).mapHomologicalComplex (ComplexShape.down
              ℕ)).obj K).extend
                  ComplexShape.embeddingDownNat).X i'
                = HomologicalComplex.extend.X (((tensorLeft
                    N).mapHomologicalComplex (ComplexShape.down ℕ)).obj K)
                    (ComplexShape.embeddingDownNat.r i') from rfl, h]; exact isZero_zero _) : _)

private theorem mapHomologicalComplexExtendXIso_hom_some {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (K : ChainComplex (ModuleCat.{u} R) ℕ) (i' : ℤ) (i : ℕ)
    (h : ComplexShape.embeddingDownNat.r i' = some i) :
    (mapHomologicalComplexExtendXIso N K i').hom
      = (tensorLeft N).map (K.extendXIso ComplexShape.embeddingDownNat
          (ComplexShape.Embedding.f_eq_of_r_eq_some _ h)).hom
        ≫ ((((tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extendXIso
            ComplexShape.embeddingDownNat (ComplexShape.Embedding.f_eq_of_r_eq_some _ h)).inv := by
  rw [mapHomologicalComplexExtendXIso]; split
  · rename_i i2 h2; rw [h] at h2; cases h2; rfl
  · rename_i h2; rw [h] at h2; exact absurd h2 (by simp)

private theorem mapHomologicalComplexExtendXIso_isZero_src {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (K : ChainComplex (ModuleCat.{u} R) ℕ) (i' : ℤ)
    (h : ComplexShape.embeddingDownNat.r i' = none) :
    IsZero ((((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat)).X i') := by
  exact (tensorLeft N).map_isZero (K.isZero_extend_X' ComplexShape.embeddingDownNat i' h)

private theorem mapHomologicalComplexExtendXIso_isZero_tgt {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (K : ChainComplex (ModuleCat.{u} R) ℕ) (i' : ℤ)
    (h : ComplexShape.embeddingDownNat.r i' = none) :
    IsZero (((((tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extend
        ComplexShape.embeddingDownNat).X i') := by
  exact HomologicalComplex.isZero_extend_X' _ _ _ h

/-- Differential compatibility for `mapHomologicalComplexExtendXIso`. -/
theorem mapHomologicalComplexExtendXIso_comm {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (i' j' : ℤ) :
    (mapHomologicalComplexExtendXIso N K i').hom
        ≫ ((((tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extend
            ComplexShape.embeddingDownNat).d i' j'
      = (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (K.extend ComplexShape.embeddingDownNat)).d i' j'
        ≫ (mapHomologicalComplexExtendXIso N K j').hom := by
  set e := ComplexShape.embeddingDownNat
  rcases hi : e.r i' with _ | i
  · exact (mapHomologicalComplexExtendXIso_isZero_src N K i' hi).eq_of_src _ _
  rcases hj : e.r j' with _ | j
  · exact (mapHomologicalComplexExtendXIso_isZero_tgt N K j' hj).eq_of_tgt _ _
  · rw [mapHomologicalComplexExtendXIso_hom_some N K i' i hi,
      mapHomologicalComplexExtendXIso_hom_some N K j' j hj]
    set hfi := ComplexShape.Embedding.f_eq_of_r_eq_some e hi
    set hfj := ComplexShape.Embedding.f_eq_of_r_eq_some e hj
    rw [HomologicalComplex.extend_d_eq (((tensorLeft N).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K) e hfi hfj]
    rw [Functor.mapHomologicalComplex_obj_d (tensorLeft N) (ComplexShape.up ℤ)
        (K.extend e) i' j']
    rw [HomologicalComplex.extend_d_eq K e hfi hfj]
    rw [Functor.mapHomologicalComplex_obj_d (tensorLeft N) (ComplexShape.down ℕ) K
        i j]
    rw [(tensorLeft N).map_comp, (tensorLeft N).map_comp]
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom,
        eqToIso.inv,
      CategoryTheory.MonoidalCategory.curriedTensor_obj_obj,
      CategoryTheory.MonoidalCategory.curriedTensor_obj_map]
    rw [CategoryTheory.MonoidalCategory.whiskerLeft_eqToHom,
      CategoryTheory.MonoidalCategory.whiskerLeft_eqToHom,
      CategoryTheory.MonoidalCategory.whiskerLeft_eqToHom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- Applying `N ⊗ -` degreewise commutes with extending a chain complex indexed by `ℕ` to a
cochain complex indexed by `ℤ` along `ComplexShape.embeddingDownNat`. -/
noncomputable def mapHomologicalComplexExtendIso {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat)
      ≅ (((tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extend
          ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (fun i' => mapHomologicalComplexExtendXIso N K i')
    (fun i' j' _ => mapHomologicalComplexExtendXIso_comm N K i' j')

/-- The `(-n)`-th cohomology of the derived tensor product of the module `N`, placed in
degree `0`, with `M` is isomorphic to `Tor_n(N, M)`. -/
noncomputable def derivedTensorHomologySingle₀Iso {R : Type u} [CommRing R]
    (N M : ModuleCat.{u} R) (n : ℕ) :
    derivedTensorHomology ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) M (-(n : ℤ))
      ≅ ((Tor (ModuleCat.{u} R) n).obj N).obj M := by
  set F := tensorLeft N
  set Kres := (ProjectiveResolution.of M).complex
  let eA := singleTensorLeftMapHomologicalComplexIso N (projResComplex M)
  let eB := mapHomologicalComplexExtendIso N Kres
  -- `projResComplex M = Kres.extend embeddingDownNat` and `(Tor _ n).obj N = F.leftDerived n`
  -- hold by definition.
  calc (((tensorLeft
              ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).obj
            (projResComplex M)).homology (-(n:ℤ)))
        ≅ (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (projResComplex M)).homology
            (-(n:ℤ))) :=
          (HomologicalComplex.homologyFunctor _ _ (-(n:ℤ))).mapIso eA
    _ ≅ (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Kres.extend
        ComplexShape.embeddingDownNat)).homology (-(n:ℤ))) := Iso.refl _
    _ ≅ ((((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Kres).extend
        ComplexShape.embeddingDownNat).homology (-(n:ℤ))) :=
          (HomologicalComplex.homologyFunctor _ _ (-(n:ℤ))).mapIso eB
    _ ≅ (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Kres).homology n) :=
          HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingDownNat rfl
    _ ≅ (F.leftDerived n).obj M :=
          (ProjectiveResolution.isoLeftDerivedObj (ProjectiveResolution.of M) F n).symm
    _ ≅ ((Tor (ModuleCat.{u} R) n).obj N).obj M := Iso.refl _

/-! ## Main statements -/

/-- For every `R`-module `M` and every integer `i`, the degree-`i` derived-tensor cohomology of `K`
over `R` vanishes iff that of the base change `K ⊗_A^L B` over `R` vanishes. -/
theorem derivedTensorHomology_isZero_iff_extendScalars
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} R) (i : ℤ) :
    IsZero (derivedTensorHomology ((CochainComplex.restrictScalars (algebraMap R A)).obj K) M i) ↔
      IsZero (derivedTensorHomology
        ((CochainComplex.restrictScalars (algebraMap R B)).obj
          ((CochainComplex.extendScalars (algebraMap A B)).obj K)) M i) := by
  let eα := derivedTensorHomologyARestrictIso R A K M i
  let eβ := derivedTensorHomologyBIso R A B K M i
  rw [← eα.isZero_iff, isZero_restrictScalars_iff]
  rw [eβ.isZero_iff, isZero_restrictScalars_iff, isZero_extendScalars_iff]

/-- Let `R → A → B` be ring maps with `A → B` faithfully flat, and let `K ∈ D(A)`. Then, viewing
both `K` and `K ⊗_A^L B` as objects of `D(R)` via restriction of scalars, `K` has tor-amplitude in
`[a, b]` over `R` if and only if `K ⊗_A^L B` has tor-amplitude in `[a, b]` over `R`. -/
@[stacks 0DJF]
theorem hasTorAmplitudeIn_iff_extendScalars
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitude ((CochainComplex.restrictScalars (algebraMap R A)).obj K) a b ↔
      HasTorAmplitude ((CochainComplex.restrictScalars (algebraMap R B)).obj
        ((CochainComplex.extendScalars (algebraMap A B)).obj K)) a b :=
  ⟨fun h M i hi => (derivedTensorHomology_isZero_iff_extendScalars R A B K M i).mp
      (h.isZero M hi),
    fun h M i hi => (derivedTensorHomology_isZero_iff_extendScalars R A B K M i).mpr
      (h.isZero M hi)⟩

/-- A homotopy equivalence of `ℕ`-indexed chain complexes extends to a homotopy equivalence of
the associated cochain complexes in nonpositive degrees. -/
public noncomputable def homotopyEquivExtendDownNat
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    {K L : ChainComplex C ℕ} (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat)
      (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom ComplexShape.embeddingDownNat
  inv := HomologicalComplex.extendMap h.inv ComplexShape.embeddingDownNat
  homotopyHomInvId := by
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_id]
    exact h.homotopyHomInvId.extend ComplexShape.embeddingDownNat
  homotopyInvHomId := by
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_id]
    exact h.homotopyInvHomId.extend ComplexShape.embeddingDownNat

end StacksDraft.TorAmplitude.FaithfullyFlat
