module

public import StacksFrontier.Homology.Tor.IndependenceFlatModule
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange

/-!
# The Tor-independence step of [stacks 0E2F] (2)

Let `R → A` be flat, let `R → R'` be arbitrary and put `A' = A ⊗[R] R'`, `B = A ⊗[R] A`,
`B' = A' ⊗[R'] A'`.  The derived and the underived extension of scalars of the diagonal `A` along
`B → B'` agree, `A ⊗ᴸ_B B' = A ⊗_B B'`, by Tor independence (More on Algebra, Lemma 15.62.2), as
in the proof of [stacks 0E2F] (2).

The key input is that `B'` is the base change of `B` along `R → R'`.  As `B'` is a tensor product
over `R'` of two base changes, the identification with `B ⊗[R] R'` is an explicit isomorphism,
`Dualizing.diagonalBaseChangeEquiv`, and `Dualizing.diagonalBaseChangeMap` is the resulting map
of diagonals `B → B'`, `a₁ ⊗ a₂ ↦ (a₁ ⊗ 1) ⊗ (a₂ ⊗ 1)`.  Once the square `R → B`, `R → R'`,
`B → B'`, `R' → B'` is known to be a pushout, `B` is flat over `R`, so `B` and `R'` are Tor
independent over `R`, and the diagonal `A` is flat over `R`; those are exactly the hypotheses of
`RingTheory.TorIndependence.isIso_comparison_single_of_flat`.

## Main definitions

* `Dualizing.diagonalBaseChangeEquiv` — the `R'`-algebra identification
  `B ⊗[R] R' = B'`: the diagonal of the base change is the base change of the diagonal.
* `Dualizing.diagonalBaseChangeMap` — the map of diagonals `B → B'`.

## Main results

* `Dualizing.diagonalBaseChangeMap_comp_includeLeft` and
  `Dualizing.lmul'_comp_diagonalBaseChangeMap` — the map of diagonals commutes with the two left
  coprojections and with the two multiplication maps; the second is the commuting square
  `B → A`, `B → B'`, `A → A'`, `B' → A'`.
* `Dualizing.isPushout_diagonalBaseChange` — the square `R → B`, `R → R'`, `B → B'`, `R' → B'`
  is a pushout of rings.
* `Dualizing.isIso_comparison_diagonalBaseChange_single` — `A ⊗ᴸ_B B' = A ⊗_B B'`, i.e. the
  comparison from derived to termwise extension of scalars along the map of diagonals is
  invertible on the diagonal `A` placed in degree zero.
* `Dualizing.isIso_comparison_diagonalBaseChange_of_kFlat` and
  `Dualizing.isIso_comparison_diagonalBaseChange_of_flat` — the same statement at a complex of
  `B`-modules that is K-flat after restriction to `R`, and at a bounded above complex of
  `R`-flat `B`-modules, which is K-flat over `R` by [stacks 064K].

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

noncomputable section

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- In `A ⊗[R] R'`, the second tensor factor is the `R'`-action on the unit of that factor. -/
theorem tmul_right_eq_smul (a : A) (r' : R') :
    (a ⊗ₜ[R] r' : A ⊗[R] R') = r' • (a ⊗ₜ[R] (1 : R')) := by
  rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The diagonal of the base change is the base change of the diagonal. -/
def diagonalBaseChangeEquiv :
    ((A ⊗[R] A) ⊗[R] R') ≃ₐ[R'] ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) :=
  AlgEquiv.ofRingEquiv
    (f := (((Algebra.TensorProduct.assoc R R R A A R').toRingEquiv.trans
        (Algebra.TensorProduct.comm R A (A ⊗[R] R')).toRingEquiv).trans
        (Algebra.TensorProduct.cancelBaseChange R R' R' (A ⊗[R] R') A).symm.toRingEquiv).trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := R') (A₁ := A ⊗[R] R'))
        (baseChangeComm R A R')).trans
        (Algebra.TensorProduct.comm R' (A ⊗[R] R') (A ⊗[R] R'))).toRingEquiv)
    (fun r' => by
      change _ = (algebraMap R' (A ⊗[R] R')) r' ⊗ₜ[R'] (1 : A ⊗[R] R')
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      simp only [AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
        AlgEquiv.symm_toEquiv_eq_symm, baseChangeComm, Algebra.TensorProduct.one_def,
        RingEquiv.coe_trans, RingEquiv.coe_mk, EquivLike.coe_coe, AlgEquiv.coe_trans,
        Function.comp_apply, Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
        AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        AlgEquiv.coe_toAlgHom, AlgEquiv.ofRingEquiv_apply]
      rw [Algebra.TensorProduct.right_algebraMap_apply,
        tmul_right_eq_smul R A R' (1 : A) r',
        TensorProduct.tmul_smul, TensorProduct.smul_tmul'])

/-- `Dualizing.diagonalBaseChangeEquiv` sends `(a₁ ⊗ a₂) ⊗ r'` to `(a₁ ⊗ r') ⊗ (a₂ ⊗ 1)`. -/
@[simp]
theorem diagonalBaseChangeEquiv_tmul (a₁ a₂ : A) (r' : R') :
    diagonalBaseChangeEquiv R A R' ((a₁ ⊗ₜ[R] a₂) ⊗ₜ[R] r') =
      (a₁ ⊗ₜ[R] r') ⊗ₜ[R'] (a₂ ⊗ₜ[R] (1 : R')) := by
  change (Algebra.TensorProduct.comm R' (A ⊗[R] R') (A ⊗[R] R'))
      ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := R') (A₁ := A ⊗[R] R'))
        (baseChangeComm R A R'))
        ((Algebra.TensorProduct.cancelBaseChange R R' R' (A ⊗[R] R') A).symm
          ((Algebra.TensorProduct.comm R A (A ⊗[R] R'))
            ((Algebra.TensorProduct.assoc R R R A A R') ((a₁ ⊗ₜ[R] a₂) ⊗ₜ[R] r'))))) = _
  simp only [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, baseChangeComm, AlgEquiv.ofRingEquiv_apply,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_refl, id_eq, AlgEquiv.coe_toAlgHom]
  rw [tmul_right_eq_smul R A R' a₁ r', tmul_right_eq_smul R A R' a₂ r',
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- The map of diagonals `A ⊗[R] A → A' ⊗[R'] A'`, `a₁ ⊗ a₂ ↦ (a₁ ⊗ 1) ⊗ (a₂ ⊗ 1)`, written as
the left coprojection of the base change followed by `Dualizing.diagonalBaseChangeEquiv`. -/
def diagonalBaseChangeMap :
    (A ⊗[R] A) →+* ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) :=
  (diagonalBaseChangeEquiv R A R').toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeLeftRingHom :
      (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R')

/-- The map of diagonals sends `a₁ ⊗ a₂` to `(a₁ ⊗ 1) ⊗ (a₂ ⊗ 1)`. -/
@[simp]
theorem diagonalBaseChangeMap_tmul (a₁ a₂ : A) :
    diagonalBaseChangeMap R A R' (a₁ ⊗ₜ[R] a₂) =
      (a₁ ⊗ₜ[R] (1 : R')) ⊗ₜ[R'] (a₂ ⊗ₜ[R] (1 : R')) :=
  diagonalBaseChangeEquiv_tmul R A R' a₁ a₂ 1

/-- The map of diagonals is compatible with the two left coprojections. -/
theorem diagonalBaseChangeMap_comp_includeLeft :
    (diagonalBaseChangeMap R A R').comp
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) =
      (Algebra.TensorProduct.includeLeftRingHom :
          (A ⊗[R] R') →+* (A ⊗[R] R') ⊗[R'] (A ⊗[R] R')).comp
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R') :=
  RingHom.ext fun a => diagonalBaseChangeMap_tmul R A R' a 1

/-- The map of diagonals is compatible with the two multiplication maps: the square
`B → A`, `B → B'`, `A → A'`, `B' → A'` commutes. -/
theorem lmul'_comp_diagonalBaseChangeMap :
    ((Algebra.TensorProduct.lmul' R' :
          (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] A ⊗[R] R').toRingHom).comp
        (diagonalBaseChangeMap R A R') =
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R').comp
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
  | tmul a₁ a₂ =>
      change (Algebra.TensorProduct.lmul' R')
          ((a₁ ⊗ₜ[R] (1 : R')) ⊗ₜ[R'] (a₂ ⊗ₜ[R] (1 : R'))) = _
      rw [Algebra.TensorProduct.lmul'_apply_tmul]
      change (a₁ ⊗ₜ[R] (1 : R')) * (a₂ ⊗ₜ[R] (1 : R')) = (a₁ * a₂) ⊗ₜ[R] (1 : R')
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The algebra structure on the base-changed diagonal given by the map of diagonals. -/
abbrev diagonalBaseChangeAlgebra :
    Algebra (A ⊗[R] A) ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) :=
  (diagonalBaseChangeMap R A R').toAlgebra

attribute [local instance] diagonalBaseChangeAlgebra

/-- With `B'` a `B`-algebra through the map of diagonals, the actions of `R`, `B` and `B'`
form a scalar tower. -/
theorem isScalarTower_diagonalBaseChange :
    IsScalarTower R (A ⊗[R] A) ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  change _ = diagonalBaseChangeMap R A R' (algebraMap R (A ⊗[R] A) r)
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def]

attribute [local instance] isScalarTower_diagonalBaseChange

/-- The square `R → B`, `R → R'`, `B → B'`, `R' → B'`, with `B → B'` the map of diagonals, is
a pushout of rings: `B' = (A ⊗[R] R') ⊗[R'] (A ⊗[R] R')` is the base change of
`B = A ⊗[R] A` along `R → R'`. -/
theorem isPushout_diagonalBaseChange :
    Algebra.IsPushout R (A ⊗[R] A) R' ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) := by
  let e : ((A ⊗[R] A) ⊗[R] R') ≃ₗ[A ⊗[R] A] ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) :=
    { (diagonalBaseChangeEquiv R A R').toRingEquiv.toAddEquiv with
      map_smul' := fun b x => by
        change diagonalBaseChangeEquiv R A R' (b • x) = b • diagonalBaseChangeEquiv R A R' x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  refine ⟨IsBaseChange.of_equiv e (fun x => ?_)⟩
  exact (diagonalBaseChangeEquiv R A R').commutes x

attribute [local instance] isPushout_diagonalBaseChange

variable [Module.Flat R A]

/-- The diagonal `A`, as a module over `B = A ⊗[R] A`. -/
abbrev diagonalModule : ModuleCat.{u} (A ⊗[R] A) :=
  (ModuleCat.restrictScalars
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj (ModuleCat.of A A)

/-- Restricted to `R`, the diagonal module is `A`, hence flat. -/
theorem flat_restrictScalars_diagonalModule :
    Module.Flat R ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj
      (diagonalModule R A)) := by
  have h : ∀ r : R, (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A)
      (algebraMap R (A ⊗[R] A) r) = algebraMap R A r := fun r => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
  refine Module.Flat.of_linearEquiv
    (M := A) (N := ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj
      (diagonalModule R A)))
    { AddEquiv.refl A with map_smul' := fun r x => ?_ }
  exact (congrArg (fun y : A => HMul.hMul (α := A) (β := A) (γ := A) y x) (h r)).trans
    (Algebra.smul_def (R := R) (A := A) r x).symm

/-- `A ⊗ᴸ_B B' = A ⊗_B B'`: for `R → A` flat, the comparison from derived to termwise extension
of scalars along the map of diagonals `B = A ⊗[R] A → B' = A' ⊗[R'] A'` is invertible on the
diagonal `A` placed in degree zero. -/
theorem isIso_comparison_diagonalBaseChange_single :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (diagonalBaseChangeMap R A R')).comparison.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
        (diagonalModule R A))) := by
  exact RingTheory.TorIndependence.isIso_comparison_single_of_flat
    (R := R) (A := A ⊗[R] A) (B := R') (T := (A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
    RingTheory.TorIndependence.torIndependent_of_flat_left (diagonalModule R A)
    (flat_restrictScalars_diagonalModule R A)

/-- For `R → A` flat and `P` a cochain complex of `B`-modules whose restriction to `R` is
K-flat, the comparison from derived to termwise extension of scalars along the map of diagonals
`B → B'` is invertible at `P`: `P ⊗ᴸ_B B' = P ⊗_B B'`. -/
theorem isIso_comparison_diagonalBaseChange_of_kFlat
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ)
    (hP : CochainComplex.KFlat.{u, u}
      (((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (diagonalBaseChangeMap R A R')).comparison.app P) := by
  exact RingTheory.TorIndependence.isIso_comparison_of_kFlat_restrictScalars
    (R := R) (A := A ⊗[R] A) (B := R') (T := (A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
    RingTheory.TorIndependence.torIndependent_of_flat_left P hP

/-- For `R → A` flat and `P` a bounded above cochain complex of `B`-modules whose terms are flat
over `R`, the comparison from derived to termwise extension of scalars along the map of diagonals
`B → B'` is invertible at `P`: `P ⊗ᴸ_B B' = P ⊗_B B'`. -/
theorem isIso_comparison_diagonalBaseChange_of_flat
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [P.IsStrictlyLE d]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (P.X i))) :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (diagonalBaseChangeMap R A R')).comparison.app P) := by
  have : CochainComplex.IsStrictlyLE (((ModuleCat.restrictScalars
      (algebraMap R (A ⊗[R] A))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) d :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P
      (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))) d).2 inferInstance
  have : ∀ n : ℤ, Module.Flat R ((((ModuleCat.restrictScalars
      (algebraMap R (A ⊗[R] A))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n) := hflat
  exact isIso_comparison_diagonalBaseChange_of_kFlat R A R' P
    (CochainComplex.KFlat.kFlat_of_flat _ d)

end

end Dualizing

end
