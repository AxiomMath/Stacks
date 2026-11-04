module

public import Mathlib.LinearAlgebra.Span.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Etale.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingComposition.Factorizations
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingBaseChange.Tower

/-!
# Arbitrary base change for the dualizing module: the finite flat case

Let `A → B` be a quasi-finite map of Noetherian rings presented by a finite-open factorization
`A → B' → B`, so that the relative dualizing module is `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B`
(Tag 0BSZ), let `A → A₁` be any ring map and `B₁ = A₁ ⊗[A] B`. The canonical base change map
`ω_{B/A} → ω_{B₁/A₁}` of Tag 0BVB induces a `B₁`-linear map `B₁ ⊗_B ω_{B/A} → ω_{B₁/A₁}`,
and that map is an isomorphism whenever `A → A₁` is flat (Tag 0BT3). The parts of
`FlatAlgebraBaseChange` prove the complementary statement: it is an isomorphism for an
*arbitrary* `A → A₁` as soon as `A → B` is flat.

This first part defines that map and treats the finite flat case, the heart of the matter: there
`B` is finite locally free over `A`, the dualizing module is the dual `A`-module `Hom_A(B, A)`,
and the dual of a finitely generated projective module commutes with arbitrary base change.

## Main definitions

* `Stacks.Discriminant.dualizingModule.baseChangeLinearMap` is the `B₁`-linear map
  `B₁ ⊗_B ω_{B/A} → ω_{B₁/A₁}` induced by the base change map of Tag 0BVB.

## Main results

* `Stacks.Discriminant.dualizingModule.baseChangeLinearMap_bijective_of_flat_finitePresentation`:
  `baseChangeLinearMap` is bijective for a flat `A → A₁` when `B'` is finitely presented over `A`.
* `Stacks.Discriminant.dualizingModule.baseChangeLinearMap_bijective_of_finite_projective`: it is
  bijective for an arbitrary `A → A₁` when `B'` is projective over `A`.

## References

* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
* [Stacks Project, Tag 0BT3](https://stacks.math.columbia.edu/tag/0BT3)
-/

@[expose] public section


open scoped TensorProduct

universe u v w x y

namespace Stacks.Discriminant

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private noncomputable def dualTensorBaseChangeMap
    {R : Type u} {M : Type v} {S : Type x}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing S] [Algebra R S] :
    S ⊗[R] Module.Dual R M →ₗ[S] Module.Dual S (S ⊗[R] M) := by
  let f := Module.Dual.baseChange (R := R) (V := M) S
  exact TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s =>
        ((LinearMap.lsmul S (Module.Dual S (S ⊗[R] M)) s).restrictScalars R).comp f
      map_add' := by
        intro s t
        ext g z
        simp
      map_smul' := by
        intro s t
        ext g z
        simp [smul_smul] }

private lemma dualTensorBaseChangeMap_natural
    {R : Type u} {M : Type v} {N : Type w} {S : Type x}
    [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [CommRing S] [Algebra R S]
    (f : M →ₗ[R] N) :
    (dualTensorBaseChangeMap (R := R) (M := M) (S := S)).comp
        (TensorProduct.AlgebraTensorModule.lTensor S S f.dualMap) =
      (f.baseChange S).dualMap.comp
        (dualTensorBaseChangeMap (R := R) (M := N) (S := S)) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
    show dualTensorBaseChangeMap (R := R) (M := M) (S := S)
        ((TensorProduct.AlgebraTensorModule.lTensor S S f.dualMap) (z + z')) =
      (f.baseChange S).dualMap
        (dualTensorBaseChangeMap (R := R) (M := N) (S := S) (z + z'))
    calc
      _ = dualTensorBaseChangeMap (R := R) (M := M) (S := S)
            ((TensorProduct.AlgebraTensorModule.lTensor S S f.dualMap) z) +
          dualTensorBaseChangeMap (R := R) (M := M) (S := S)
            ((TensorProduct.AlgebraTensorModule.lTensor S S f.dualMap) z') := by
        rw [(TensorProduct.AlgebraTensorModule.lTensor S S f.dualMap).map_add,
          map_add]
      _ = (f.baseChange S).dualMap
          (dualTensorBaseChangeMap (R := R) (M := N) (S := S) z) +
          (f.baseChange S).dualMap
            (dualTensorBaseChangeMap (R := R) (M := N) (S := S) z') :=
        congrArg₂ (· + ·) hz hz'
      _ = _ := by
        rw [(dualTensorBaseChangeMap (R := R) (M := N) (S := S)).map_add,
          (f.baseChange S).dualMap.map_add]
  | tmul s g =>
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
      calc
        (dualTensorBaseChangeMap (R := R) (M := M) (S := S)
            (s ⊗ₜ[R] f.dualMap g)) (z + z') =
            (dualTensorBaseChangeMap (R := R) (M := M) (S := S)
              (s ⊗ₜ[R] f.dualMap g)) z +
              (dualTensorBaseChangeMap (R := R) (M := M) (S := S)
                (s ⊗ₜ[R] f.dualMap g)) z' := map_add _ _ _
        _ = (((LinearMap.baseChange S f).dualMap.comp
            (dualTensorBaseChangeMap (R := R) (M := N) (S := S)))
              (s ⊗ₜ[R] g)) z +
            (((LinearMap.baseChange S f).dualMap.comp
              (dualTensorBaseChangeMap (R := R) (M := N) (S := S)))
                (s ⊗ₜ[R] g)) z' := congrArg₂ (· + ·) hz hz'
        _ = _ := ((((f.baseChange S).dualMap).comp
          (dualTensorBaseChangeMap (R := R) (M := N) (S := S)))
            (s ⊗ₜ[R] g)).map_add z z' |>.symm
    | tmul t m =>
      simp [dualTensorBaseChangeMap, LinearMap.dualMap_apply,
        Module.Dual.baseChange_apply_tmul, LinearMap.baseChange_tmul,
        smul_eq_mul, mul_assoc]

private lemma dual_baseChange_isBaseChange_of_free
    {R : Type u} {M : Type v} {S : Type x}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing S] [Algebra R S]
    [Module.Free R M] [Module.Finite R M] :
    IsBaseChange S (Module.Dual.baseChange S :
      Module.Dual R M →ₗ[R] Module.Dual S (S ⊗[R] M)) := by
  let j : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  have hj : IsBaseChange S j := TensorProduct.isBaseChange R M S
  have h := hj.dual
  have hequiv : hj.equiv = LinearEquiv.refl S (S ⊗[R] M) := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
    | tmul s z => simp [j, TensorProduct.smul_tmul']
  have heq : hj.toDual = Module.Dual.baseChange S := by
    ext f z
    rw [hj.toDual_apply]
    rw [hequiv]
    simp [Module.Dual.baseChange]
  rw [← heq]
  exact h

private lemma dual_baseChange_isBaseChange_of_finite_projective
    {R : Type u} {M : Type v} {S : Type x}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing S] [Algebra R S]
    [Module.Finite R M] [Module.Projective R M] :
    IsBaseChange S (Module.Dual.baseChange S :
      Module.Dual R M →ₗ[R] Module.Dual S (S ⊗[R] M)) := by
  classical
  obtain ⟨n, i, p, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let P := Fin n → R
  let hP := dual_baseChange_isBaseChange_of_free (R := R) (M := P) (S := S)
  let eP := hP.equiv
  let mapP := dualTensorBaseChangeMap (R := R) (M := P) (S := S)
  let mapM := dualTensorBaseChangeMap (R := R) (M := M) (S := S)
  have heP : eP.toLinearMap = mapP := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
      calc
        eP (z + z') = eP z + eP z' := map_add eP _ _
        _ = mapP z + mapP z' := congrArg₂ (· + ·) hz hz'
        _ = mapP (z + z') := (map_add mapP _ _).symm
    | tmul s f => simp [mapP, dualTensorBaseChangeMap, eP, hP.equiv_tmul]
  let iS := i.baseChange S
  let pS := p.baseChange S
  let iDual := iS.dualMap
  let pDual := pS.dualMap
  let iDualTensor := TensorProduct.AlgebraTensorModule.lTensor S S i.dualMap
  let pDualTensor := TensorProduct.AlgebraTensorModule.lTensor S S p.dualMap
  have hi : mapP.comp iDualTensor = iDual.comp mapM :=
    dualTensorBaseChangeMap_natural i
  have hp : mapM.comp pDualTensor = pDual.comp mapP :=
    dualTensorBaseChangeMap_natural p
  have hip : pDual.comp iDual = LinearMap.id := by
    rw [LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi,
      LinearMap.baseChange_id, LinearMap.dualMap_id]
  have hipt : pDualTensor.comp iDualTensor = LinearMap.id := by
    rw [← TensorProduct.AlgebraTensorModule.lTensor_comp,
      LinearMap.dualMap_comp_dualMap, hpi]
    simp [LinearMap.dualMap_id]
  let inv := pDualTensor.comp (eP.symm.toLinearMap.comp iDual)
  have hsymm : eP.symm.toLinearMap.comp mapP = LinearMap.id := by
    rw [← heP]
    ext z
    simp
  have hleft : mapM.comp inv = LinearMap.id := by
    calc
      mapM.comp inv = (mapM.comp pDualTensor).comp
          (eP.symm.toLinearMap.comp iDual) := by simp [inv, LinearMap.comp_assoc]
      _ = (pDual.comp mapP).comp (eP.symm.toLinearMap.comp iDual) := by rw [hp]
      _ = pDual.comp iDual := by
        rw [LinearMap.comp_assoc, ← heP]
        simp [LinearMap.comp_assoc]
      _ = LinearMap.id := hip
  have hright : inv.comp mapM = LinearMap.id := by
    calc
      inv.comp mapM = pDualTensor.comp
          (eP.symm.toLinearMap.comp (iDual.comp mapM)) := by
            simp [inv, LinearMap.comp_assoc]
      _ = pDualTensor.comp
          (eP.symm.toLinearMap.comp (mapP.comp iDualTensor)) := by rw [hi]
      _ = pDualTensor.comp iDualTensor := by
        calc
          pDualTensor.comp
              (eP.symm.toLinearMap.comp (mapP.comp iDualTensor)) =
            pDualTensor.comp
              ((eP.symm.toLinearMap.comp mapP).comp iDualTensor) := by
                rw [LinearMap.comp_assoc]
          _ = pDualTensor.comp (LinearMap.id.comp iDualTensor) := by rw [hsymm]
          _ = pDualTensor.comp iDualTensor := by simp
      _ = LinearMap.id := hipt
  have hinj : Function.Injective mapM := by
    intro x y hxy
    have h' := congrArg inv hxy
    have hx : inv (mapM x) = x := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hright x
    have hy : inv (mapM y) = y := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hright y
    exact hx.symm.trans (h'.trans hy)
  have hsurj : Function.Surjective mapM := by
    intro y
    exact ⟨inv y, LinearMap.congr_fun hleft y⟩
  have hb : Function.Bijective mapM := ⟨hinj, hsurj⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective mapM hb) ?_
  intro f
  simp [mapM, dualTensorBaseChangeMap]

section FlatFinitePresentationDualBaseChange

variable {R : Type u} {M : Type v} {S : Type x}
  [CommRing R] [CommRing M] [Algebra R M]
  [CommRing S] [Algebra R S]

/-- The `S`-algebra structure on `S ⊗[R] M` from the left factor. -/
local instance : Algebra S (S ⊗[R] M) := Algebra.TensorProduct.leftAlgebra
/-- The `M`-algebra structure on `S ⊗[R] M` from the right factor. -/
local instance : Algebra M (S ⊗[R] M) := Algebra.TensorProduct.rightAlgebra
/-- The `R`-algebra structure on `S ⊗[R] M` through the left factor. -/
local instance : Algebra R (S ⊗[R] M) := Algebra.TensorProduct.leftAlgebra
/-- The scalar tower `R → M → S ⊗[R] M`. -/
local instance : IsScalarTower R M (S ⊗[R] M) := Algebra.TensorProduct.right_isScalarTower
/-- The `M`-module structure on `Hom_R(M, R)` given by `(m • f) x = f (m * x)`. -/
local instance : Module M (Module.Dual R M) := algebraDualModule R M
/-- The scalar tower `R → M → Hom_R(M, R)`. -/
local instance : IsScalarTower R M (Module.Dual R M) :=
  IsScalarTower.of_algebraMap_smul (by
    intro r f
    ext m
    change f ((algebraMap R M r) * m) = r * f m
    rw [← Algebra.smul_def]
    simpa using f.map_smul r m)
/-- The `S ⊗[R] M`-module structure on `Hom_S(S ⊗[R] M, S)` by precomposition with
multiplication. -/
local instance : Module (S ⊗[R] M) (Module.Dual S (S ⊗[R] M)) :=
  algebraDualModule S (S ⊗[R] M)
/-- The `M`-module structure on `Hom_S(S ⊗[R] M, S)` by restriction of scalars along
`M → S ⊗[R] M`. -/
local instance : Module M (Module.Dual S (S ⊗[R] M)) :=
  Module.compHom _ (algebraMap M (S ⊗[R] M))
/-- The scalar tower `M → S ⊗[R] M → Hom_S(S ⊗[R] M, S)`. -/
local instance : IsScalarTower M (S ⊗[R] M) (Module.Dual S (S ⊗[R] M)) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
/-- The square `R → S, M → S ⊗[R] M` is a pushout. -/
local instance : Algebra.IsPushout R S M (S ⊗[R] M) := Algebra.IsPushout.symm inferInstance

end FlatFinitePresentationDualBaseChange

open Topology CategoryTheory Opposite AlgebraicGeometry

/-- If `A → B` admits a finite open factorization, then `B` is of finite type and quasi-finite
over `A`. -/
lemma finiteType_quasiFinite_of_finiteOpenFactorization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Algebra.FiniteType A B ∧ Algebra.QuasiFinite A B := by
  let : Algebra.FiniteType A F.middle := inferInstance
  let : Algebra.FiniteType F.middle B := finiteType_of_finiteOpenFactorization F
  let : Algebra.QuasiFinite F.middle B := quasiFinite_of_finiteOpenFactorization F
  exact ⟨Algebra.FiniteType.trans (R := A) (S := F.middle) (A := B)
      inferInstance inferInstance,
    Algebra.QuasiFinite.trans A F.middle B⟩

/-- The linear map induced by the canonical base change map on the tensor product
with the base-changed algebra. -/
noncomputable def baseChangeLinearMap
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    (A₁ ⊗[A] B) ⊗[B] dualizingModule F →ₗ[A₁ ⊗[A] B]
      dualizingModule (FiniteOpenFactorization.baseChange F A₁) := by
  letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : Module B
      (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
  letI : IsScalarTower B (A₁ ⊗[A] B)
      (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    IsScalarTower.of_compHom B (A₁ ⊗[A] B) _
  let f := dualizingModule.baseChange F A₁
  exact TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b₁ =>
        ((LinearMap.lsmul (A₁ ⊗[A] B)
          (dualizingModule (FiniteOpenFactorization.baseChange F A₁))
          b₁).restrictScalars B).comp f
      map_add' := by
        intro b₁ c₁
        ext m
        simp
      map_smul' := by
        intro b₁ c₁
        ext m
        simp [smul_smul] }

/-- If the dual of the middle algebra commutes with the base change `A → A₁`, then the
dualizing module does too. -/
private theorem dualizingModule_isBaseChange_of_dual_isBaseChange
    (F : FiniteOpenFactorization.{u, v, w} A B)
    [Module.FinitePresentation A F.middle]
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (hdual : IsBaseChange A₁ (Module.Dual.baseChange A₁ :
      Module.Dual A F.middle →ₗ[A] Module.Dual A₁ (A₁ ⊗[A] F.middle))) :
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
    letI : IsScalarTower B (A₁ ⊗[A] B)
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      IsScalarTower.of_compHom B (A₁ ⊗[A] B) _
    IsBaseChange (A₁ ⊗[A] B) (dualizingModule.baseChange F A₁) := by
  -- Every instance is introduced before the abbreviation that uses it, and the
  -- intermediate algebra of the base-changed factorization keeps the ambient
  -- tensor-product instances: giving it the factorization's own `Algebra A₁ C₁`
  -- leaves `Module.Dual A₁ C₁` and `algebraDualModule A₁ C₁` agreeing only after
  -- unfolding.
  let C := F.middle
  let _ : CommRing C := F.commRingMiddle
  let _ : Algebra A C := F.algebraMiddle
  let _ : Algebra C B := F.algebraTarget
  let _ : IsScalarTower A C B := F.scalarTower
  let _ : Module.Finite A C := F.finite_middle
  let _ : Module.FinitePresentation A C := inferInstance
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let C₁ := A₁ ⊗[A] C
  let B₁ := A₁ ⊗[A] B
  let E := Module.Dual A C
  let E₁ := Module.Dual A₁ C₁
  let _ : Module C E := algebraDualModule A C
  let _ : Algebra C C₁ := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra C₁ B₁ := F₁.algebraTarget
  let _ : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra C B₁ := Algebra.compHom B₁ (algebraMap C B)
  let _ : Module C B₁ := Module.compHom B₁ (algebraMap C B)
  let _ : Module C₁ E₁ := algebraDualModule A₁ C₁
  let _ : Module C E₁ := Module.compHom E₁ (algebraMap C C₁)
  let _ : IsScalarTower C C₁ E₁ :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let _ : IsScalarTower A₁ C₁ B₁ :=
    FiniteOpenFactorization.baseChange_scalarTower F A₁
  let _ : IsScalarTower C B B₁ :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsScalarTower C C₁ B₁ := IsScalarTower.of_algebraMap_eq (fun c => by
    show algebraMap C₁ B₁ (algebraMap C C₁ c) =
      algebraMap B B₁ (algebraMap C B c)
    show Algebra.TensorProduct.map (AlgHom.id A A₁)
        (IsScalarTower.toAlgHom A C B) (1 ⊗ₜ[A] c) = _
    rw [Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.id_apply]
    show algebraMap B B₁ (algebraMap C B c) = _
    rfl)
  let _ : Module B (E ⊗[C] B) :=
    (TensorProduct.comm C E B).toAddEquiv.module B
  let _ : Module B₁ (E₁ ⊗[C₁] B₁) :=
    (TensorProduct.comm C₁ E₁ B₁).toAddEquiv.module B₁
  let _ : Module B (dualizingModule F) :=
    (TensorProduct.comm C E B).toAddEquiv.module B
  let _ : Module B₁ (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    (TensorProduct.comm C₁ E₁ B₁).toAddEquiv.module B₁
  let _ : Module B (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    Module.compHom _ (algebraMap B B₁)
  let hTower : IsScalarTower B B₁
      (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let _ : IsScalarTower B B₁
      (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) := hTower
  let hE := dual_baseChange_isBaseChange_overTensor_of_isBaseChange
    (R := A) (M := C) (S := A₁) hdual
  let eComm : E ⊗[C] B ≃ₗ[B] B ⊗[C] E :=
    (TensorProduct.comm C E B).toAddEquiv.linearEquiv B
  let eCommTarget : E₁ ⊗[C₁] B₁ ≃ₗ[B₁] B₁ ⊗[C₁] E₁ :=
    (TensorProduct.comm C₁ E₁ B₁).toAddEquiv.linearEquiv B₁
  let eTensor : B₁ ⊗[B] (E ⊗[C] B) ≃ₗ[B]
      B₁ ⊗[B] (B ⊗[C] E) := LinearEquiv.lTensor B₁ eComm
  let eTensor' : B₁ ⊗[B] (E ⊗[C] B) ≃ₗ[B₁]
      B₁ ⊗[B] (B ⊗[C] E) :=
    { eTensor with
      map_smul' := by
        intro b z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z z' hz hz' =>
          calc
            eTensor (b • (z + z')) = eTensor (b • z + b • z') :=
              congrArg eTensor (smul_add b z z')
            _ = eTensor (b • z) + eTensor (b • z') :=
              map_add eTensor (b • z) (b • z')
            _ = b • eTensor z + b • eTensor z' := congrArg₂ (· + ·) hz hz'
            _ = b • eTensor (z + z') := by
              rw [eTensor.map_add, smul_add]
        | tmul b' y =>
          show (b * b') ⊗ₜ[B] eComm y = b • (b' ⊗ₜ[B] eComm y)
          rw [TensorProduct.smul_tmul']
          rfl }
  let eCancel :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange C B B₁ B₁ E
  let eSource := eTensor'.trans eCancel
  let eCancelC :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange C C₁ B₁ B₁ E
  let eLiftRaw := LinearEquiv.lTensor B₁ hE.equiv
  let eLift : B₁ ⊗[C₁] (C₁ ⊗[C] E) ≃ₗ[B₁] B₁ ⊗[C₁] E₁ :=
    { eLiftRaw with
      map_smul' := by
        intro b z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z z' hz hz' =>
          calc
            eLiftRaw (b • (z + z')) = eLiftRaw (b • z + b • z') :=
              congrArg eLiftRaw (smul_add b z z')
            _ = eLiftRaw (b • z) + eLiftRaw (b • z') :=
              map_add eLiftRaw (b • z) (b • z')
            _ = b • eLiftRaw z + b • eLiftRaw z' := congrArg₂ (· + ·) hz hz'
            _ = b • eLiftRaw (z + z') := by
              rw [eLiftRaw.map_add, smul_add]
        | tmul b' y =>
          show (b * b') ⊗ₜ[C₁] hE.equiv y = b • (b' ⊗ₜ[C₁] hE.equiv y)
          rw [TensorProduct.smul_tmul']
          rfl }
  let eMiddle := eCancelC.symm.trans eLift
  let e : B₁ ⊗[B] dualizingModule F ≃ₗ[B₁]
      dualizingModule (FiniteOpenFactorization.baseChange F A₁) :=
    eSource.trans (eMiddle.trans eCommTarget.symm)
  refine @IsBaseChange.of_equiv B _ _ B₁ _ _ _ _ _ _ _ _ hTower
    (f := dualizingModule.baseChange F A₁) e ?_
  intro x
  dsimp only [dualizingModule] at x ⊢
  induction x using TensorProduct.induction_on with
  | zero =>
    calc
      e 0 = 0 := map_zero e
      _ = dualizingModule.baseChange F A₁ 0 :=
        (map_zero (dualizingModule.baseChange F A₁)).symm
  | add x y hx hy =>
    -- `rw [TensorProduct.tmul_add]` cannot abstract the sum here, because the `+` of the goal
    -- and the `+` of the lemma are two instances identified only definitionally; splitting the
    -- tensor is therefore done as a term, where the check happens at elaboration.
    have hsplit : e (1 ⊗ₜ[B] (x + y)) = e (1 ⊗ₜ[B] x) + e (1 ⊗ₜ[B] y) :=
      (congrArg e (TensorProduct.tmul_add (1 : B₁) x y)).trans (map_add e _ _)
    have hsum : dualizingModule.baseChange F A₁ x + dualizingModule.baseChange F A₁ y =
        dualizingModule.baseChange F A₁ (x + y) :=
      (map_add (dualizingModule.baseChange F A₁) x y).symm
    exact hsplit.trans ((congrArg₂ (· + ·) hx hy).trans hsum)
  | tmul f b =>
    show e (1 ⊗ₜ[B] dualizingModule.tmul F f b) =
      dualizingModule.baseChange F A₁
        (dualizingModule.tmul F f b)
    rw [dualizingModule.baseChange_tmul]
    have h1 : eTensor' (1 ⊗ₜ[B] (f ⊗ₜ[C] b)) =
        1 ⊗ₜ[B] (b ⊗ₜ[C] f) := by
      show (1 : B₁) ⊗ₜ[B] eComm (f ⊗ₜ[C] b) = _
      rfl
    have h2 : eCancel (1 ⊗ₜ[B] (b ⊗ₜ[C] f)) =
        (algebraMap B B₁ b) ⊗ₜ[C] f := by
      simp [eCancel, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        Algebra.smul_def]
    have h3 : eCancelC.symm ((algebraMap B B₁ b) ⊗ₜ[C] f) =
        (algebraMap B B₁ b) ⊗ₜ[C₁] (1 ⊗ₜ[C] f) := by
      simp [eCancelC, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    have h4 : eLift ((algebraMap B B₁ b) ⊗ₜ[C₁] (1 ⊗ₜ[C] f)) =
        (algebraMap B B₁ b) ⊗ₜ[C₁] (Module.Dual.baseChange A₁ f) := by
      show (algebraMap B B₁ b) ⊗ₜ[C₁] hE.equiv (1 ⊗ₜ[C] f) = _
      rw [IsBaseChange.equiv_tmul]
      rw [one_smul, dualBaseChangeRestrictScalars]
      rfl
    have h5 : eCommTarget.symm
        ((algebraMap B B₁ b) ⊗ₜ[C₁] (Module.Dual.baseChange A₁ f)) =
        (Module.Dual.baseChange A₁ f) ⊗ₜ[C₁] (algebraMap B B₁ b) := rfl
    show eCommTarget.symm
      (eLift (eCancelC.symm (eCancel
        (eTensor' (1 ⊗ₜ[B] (f ⊗ₜ[C] b)))))) = _
    rw [h1, h2, h3, h4, h5]
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    rfl



private theorem baseChangeLinearMap_bijective_of_isBaseChange
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (h : letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
      letI : Module B
          (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
        Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
      letI : IsScalarTower B (A₁ ⊗[A] B)
          (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
        IsScalarTower.of_compHom B (A₁ ⊗[A] B) _
      IsBaseChange (A₁ ⊗[A] B) (dualizingModule.baseChange F A₁)) :
    Function.Bijective (baseChangeLinearMap F A₁) := by
  let B₁ := A₁ ⊗[A] B
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule F₁) :=
    Module.compHom _ (algebraMap B B₁)
  let : IsScalarTower B B₁ (dualizingModule F₁) :=
    IsScalarTower.of_compHom B B₁ _
  let h' : IsBaseChange B₁ (dualizingModule.baseChange F A₁) := h
  show Function.Bijective h'.equiv.toLinearMap
  exact h'.equiv.bijective

theorem baseChangeLinearMap_bijective_of_flat_finitePresentation
    (F : FiniteOpenFactorization.{u, v, w} A B)
    [Module.FinitePresentation A F.middle]
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] [Module.Flat A A₁] :
    Function.Bijective (baseChangeLinearMap F A₁) := by
  exact baseChangeLinearMap_bijective_of_isBaseChange F A₁
    (dualizingModule_isBaseChange_of_dual_isBaseChange F A₁
      (dual_baseChange_isBaseChange_of_flat_finitePresentation (R := A) (M := F.middle)
        (S := A₁)))

theorem baseChangeLinearMap_bijective_of_finite_projective
    (F : FiniteOpenFactorization.{u, v, w} A B)
    [Module.Projective A F.middle]
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    Function.Bijective (baseChangeLinearMap F A₁) := by
  let : Module.FinitePresentation A F.middle :=
    Module.finitePresentation_of_projective A F.middle
  exact baseChangeLinearMap_bijective_of_isBaseChange F A₁
    (dualizingModule_isBaseChange_of_dual_isBaseChange F A₁
      (dual_baseChange_isBaseChange_of_finite_projective (R := A) (M := F.middle)
        (S := A₁)))

end dualizingModule
end Stacks.Discriminant
