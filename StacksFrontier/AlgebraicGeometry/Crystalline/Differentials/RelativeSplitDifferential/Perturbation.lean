module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamPerturbation
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BidegreeFiltration
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareSpecial
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelTransition
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential.Contraction

/-!
# The completed relative contraction and the instantiation of the perturbation argument

Part of `StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential`, whose
module docstring explains the construction.  This file contains the completed counterparts of
wedging with a coefficient one-form and of the relative contraction identity on `Ω̂^*_{D'}`, the
five maps of the perturbation argument recorded as `D`-linear maps, the completed forms of `D'` as
a de Rham complex over `D`, the pushed connection, and the instantiation
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_completedPolynomialForms` and
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_pushedConnection` of the completed
clause of [Stacks, Lemma 60.21.2, Tag 07LD].
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW uM

namespace Crystalline

namespace DividedPowerPolynomial

section CompletedScalars

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ)

/-! ### The completion of a base-linear map is `D`-linear -/

section CompletedScalarsLinear

variable [LinearOrder W]

/-- **Wedging with a coefficient one-form raises the coefficient degree on `Ω̂^*_{D'}`** — the
`hprojwedge` hypothesis of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` at the
completed forms.  The wedge product of the completed forms is built level by level from the
uncompleted one, so this is
`Crystalline.DividedPowerPolynomial.formsBidegreeProjection_wedge_formsBidegreeProjection_eq_zero`
carried across by `Crystalline.PAdicCompletion.mapBilinear_comp_eq_zero`. -/
theorem completedFormsBidegreeProjection_wedge_eq_zero (n l i : ℕ) (hli : l ≤ i)
    (x : completedPolynomialForms A B W p n) (y : completedPolynomialForms A B W p 1) :
    completedFormsBidegreeProjection A B W p (n + 1) l
        (completedDividedPowerWedge p A (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (completedFormsBidegreeProjection A B W p n i x)
          (completedFormsBidegreeProjection A B W p 1 1 y)) = 0 :=
  PAdicCompletion.mapBilinear_comp_eq_zero p (setIndexedDividedPowerPolynomialAlgebra B W)
    (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n)
    (formsBidegreeProjection A B W n i).toAddMonoidHom
    (formsBidegreeProjection A B W 1 1).toAddMonoidHom
    (formsBidegreeProjection A B W (n + 1) l).toAddMonoidHom
    (fun u v ↦ formsBidegreeProjection_wedge_formsBidegreeProjection_eq_zero A B W n l i hli u v)
    x y

/-- **The completed comparison `ψ̂` lands in the top coefficient degree**: `π̂_n ψ̂ = ψ̂`.  This is
what discharges the `hnabla` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` for a connection whose values come
from `M ⊗̂_D Ω̂¹_D`. -/
theorem completedFormsBidegreeProjection_completedCoefficientFormsMap (n : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers n) :
    completedFormsBidegreeProjection A B W p n n
        (completedCoefficientFormsMap A B W p n x) =
      completedCoefficientFormsMap A B W p n x := by
  classical
  have huncomp : (formsBidegreeProjection A B W n n).toAddMonoidHom.comp
        (coefficientFormsMap A B W n).toAddMonoidHom =
      (coefficientFormsMap A B W n).toAddMonoidHom :=
    AddMonoidHom.ext fun omega ↦
      (formsBidegreeProjection_coefficientFormsMap A B W n n omega).trans (if_pos rfl)
  have hcomp : (completedFormsBidegreeProjection A B W p n n).comp
      (completedCoefficientFormsMap A B W p n).toAddMonoidHom =
      (completedCoefficientFormsMap A B W p n).toAddMonoidHom := by
    rw [completedCoefficientFormsMap_toAddMonoidHom, completedFormsBidegreeProjection_eq,
      ← PAdicCompletion.mapAddHom_comp, huncomp]
  exact DFunLike.congr_fun hcomp x

/-! ### The relative contraction identity on `Ω̂^*_{D'}` -/

/-- **The degree-zero relative contraction identity on `Ω̂^0_{D'}`, as an identity of additive
maps**: `ĥ₀ ∘ d_rel,₀ + ψ̂ ε̂ = id`. -/
theorem completedRelativeFormsRelContraction_addHom_zero :
    (completedRelativeFormsHomotopy A B W p 0).comp (completedFormsRelDifferential A B W p 0) +
        completedRelativeFormsProjection A B W p 0 =
      AddMonoidHom.id (completedPolynomialForms A B W p 0) :=
  PAdicCompletion.mapAddHom_contraction_zero p
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (formsRelDifferentialAux A B W 0).toAddMonoidHom
    (relativeFormsHomotopy A B W 0).toAddMonoidHom
    ((coefficientFormsMap A B W 0).toAddMonoidHom.comp
      (relativeFormsRetraction A B W 0).toAddMonoidHom)
    (completedFormsRelDifferential A B W p 0)
    (completedRelativeFormsHomotopy A B W p 0)
    (completedRelativeFormsProjection A B W p 0)
    (completedFormsRelDifferential_eq A B W p 0)
    (completedRelativeFormsHomotopy_eq A B W p 0)
    (completedRelativeFormsProjection_eq A B W p 0)
    (AddMonoidHom.ext fun y ↦ relativeFormsHomotopy_relContraction_zero A B W y)

/-- **The relative contraction identity on `Ω̂^{n+1}_{D'}`, as an identity of additive maps**:
`d_rel ∘ ĥ + ĥ ∘ d_rel + ψ̂ ε̂ = id`.  Every term is the `p`-adic completion of its uncompleted
counterpart, so this *is*
`Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_relContraction`. -/
theorem completedRelativeFormsRelContraction_addHom (n : ℕ) :
    (completedFormsRelDifferential A B W p n).comp (completedRelativeFormsHomotopy A B W p n) +
          (completedRelativeFormsHomotopy A B W p (n + 1)).comp
            (completedFormsRelDifferential A B W p (n + 1)) +
        completedRelativeFormsProjection A B W p (n + 1) =
      AddMonoidHom.id (completedPolynomialForms A B W p (n + 1)) :=
  PAdicCompletion.mapAddHom_contraction p (setIndexedDividedPowerPolynomialAlgebra B W)
    (formsRelDifferentialAux A B W n).toAddMonoidHom
    (relativeFormsHomotopy A B W n).toAddMonoidHom
    (formsRelDifferentialAux A B W (n + 1)).toAddMonoidHom
    (relativeFormsHomotopy A B W (n + 1)).toAddMonoidHom
    ((coefficientFormsMap A B W (n + 1)).toAddMonoidHom.comp
      (relativeFormsRetraction A B W (n + 1)).toAddMonoidHom)
    (completedFormsRelDifferential A B W p n)
    (completedRelativeFormsHomotopy A B W p n)
    (completedFormsRelDifferential A B W p (n + 1))
    (completedRelativeFormsHomotopy A B W p (n + 1))
    (completedRelativeFormsProjection A B W p (n + 1))
    (completedFormsRelDifferential_eq A B W p n)
    (completedRelativeFormsHomotopy_eq A B W p n)
    (completedFormsRelDifferential_eq A B W p (n + 1))
    (completedRelativeFormsHomotopy_eq A B W p (n + 1))
    (completedRelativeFormsProjection_eq A B W p (n + 1))
    (AddMonoidHom.ext fun y ↦ relativeFormsHomotopy_relContraction A B W n y)

/-- **The completion of a `B`-linear map of the forms of `P` is `D`-linear**, both sides carrying
the `D`-module structure of
`Crystalline.DividedPowerPolynomial.moduleCompletedPolynomialForms`.  This is
`Crystalline.PAdicCompletion.mapAddHom_smul` with both ring maps the coefficient inclusion. -/
theorem mapAddHom_smul_polynomialForms {m n : ℕ}
    (u : dividedPowerPolynomialForms A B W m →+ dividedPowerPolynomialForms A B W n)
    (hu : ∀ (b : (B : Type uB)) (x : dividedPowerPolynomialForms A B W m), u (b • x) = b • u x)
    (c : completedDividedPowerRing p (B := (B : Type uB)))
    (z : completedPolynomialForms A B W p m) :
    PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W) u (c • z) =
      c • PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W) u z :=
  ((congrArg (fun w : completedPolynomialForms A B W p m ↦
        PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
          (setIndexedDividedPowerPolynomialAlgebra B W) u w)
      (completedPolynomialForms_smul_mapRingHom A B W p m c z)).trans
    ((PAdicCompletion.mapAddHom_smul p (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W))
        (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)) u
        (fun b x ↦ by rw [algebraMap_smul, algebraMap_smul]; exact hu b x) c z).trans
      (completedPolynomialForms_smul_mapRingHom A B W p n c
        (PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
          (setIndexedDividedPowerPolynomialAlgebra B W) u z)).symm))

/-- **The completion of a `B`-linear map from the forms of `P` to the forms of `B` is
`D`-linear**: the source carries the restricted structure of
`Crystalline.DividedPowerPolynomial.moduleCompletedPolynomialForms` and the target the
`AdicCompletion` structure it already had. -/
theorem mapAddHom_smul_polynomialFormsToForms {m n : ℕ}
    (u : dividedPowerPolynomialForms A B W m →+
      dividedPowerDifferentialForms (A := A) B.dividedPowers n)
    (hu : ∀ (b : (B : Type uB)) (x : dividedPowerPolynomialForms A B W m), u (b • x) = b • u x)
    (c : completedDividedPowerRing p (B := (B : Type uB)))
    (z : completedPolynomialForms A B W p m) :
    PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W) (B : Type uB) u
        (c • z) =
      c • PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
        (B : Type uB) u z :=
  (congrArg (fun w : completedPolynomialForms A B W p m ↦
        PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
          (B : Type uB) u w)
      (completedPolynomialForms_smul_mapRingHom A B W p m c z)).trans
    ((PAdicCompletion.mapAddHom_smul p (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W) (B : Type uB)
        (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W))
        (RingHom.id (B : Type uB)) u
        (fun b x ↦ by rw [algebraMap_smul]; exact hu b x) c z).trans
      (congrArg (fun y : completedDividedPowerRing p (B := (B : Type uB)) ↦
          y • PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
            (B : Type uB) u z)
        (PAdicCompletion.mapRingHom_id_apply p (B : Type uB) c)))

/-- **The completion of a `B`-linear map from the forms of `B` to the forms of `P` is
`D`-linear**, the target carrying the restricted structure of
`Crystalline.DividedPowerPolynomial.moduleCompletedPolynomialForms`. -/
theorem mapAddHom_smul_formsToPolynomialForms {m n : ℕ}
    (u : dividedPowerDifferentialForms (A := A) B.dividedPowers m →+
      dividedPowerPolynomialForms A B W n)
    (hu : ∀ (b : (B : Type uB))
      (x : dividedPowerDifferentialForms (A := A) B.dividedPowers m), u (b • x) = b • u x)
    (c : completedDividedPowerRing p (B := (B : Type uB)))
    (z : completedDividedPowerForms p A B.dividedPowers m) :
    PAdicCompletion.mapAddHom p (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) u
        (c • z) =
      c • PAdicCompletion.mapAddHom p (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W) u z :=
  ((congrArg (fun w : completedDividedPowerForms p A B.dividedPowers m ↦
        PAdicCompletion.mapAddHom p (B : Type uB)
          (setIndexedDividedPowerPolynomialAlgebra B W) u w)
      (congrArg (fun y : completedDividedPowerRing p (B := (B : Type uB)) ↦ y • z)
        (PAdicCompletion.mapRingHom_id_apply p (B : Type uB) c).symm)).trans
    (PAdicCompletion.mapAddHom_smul p (B : Type uB) (B : Type uB)
      (setIndexedDividedPowerPolynomialAlgebra B W) (RingHom.id (B : Type uB))
      (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)) u
      (fun b x ↦ by rw [algebraMap_smul]; exact hu b x) c z)).trans
    (completedPolynomialForms_smul_mapRingHom A B W p n c
      (PAdicCompletion.mapAddHom p (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W) u z)).symm

/-! ### The five maps of the perturbation argument, over `D` -/

/-- **The relative part of the de Rham differential of `Ω̂^*_{D'}`, as a `D`-linear map**, which
is the `drel` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`.  The underlying
additive map is `Crystalline.DividedPowerPolynomial.completedFormsRelDifferential`; what is added
is the record of its `D`-linearity, which is the completion of the `B`-linearity
`Crystalline.DividedPowerPolynomial.formsRelDifferentialAux_smul`. -/
def completedFormsRelDifferentialₗ (n : ℕ) :
    completedPolynomialForms A B W p n →ₗ[completedDividedPowerRing p (B := (B : Type uB))]
      completedPolynomialForms A B W p (n + 1) where
  toFun := PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (formsRelDifferentialAux A B W n).toAddMonoidHom
  map_add' := map_add _
  map_smul' c x :=
    mapAddHom_smul_polynomialForms A B W p (formsRelDifferentialAux A B W n).toAddMonoidHom
      (fun b y ↦ formsRelDifferentialAux_smul A B W n b y) c x

/-- The `D`-linear relative differential is the additive one. -/
theorem completedFormsRelDifferentialₗ_toAddMonoidHom (n : ℕ) :
    (completedFormsRelDifferentialₗ A B W p n).toAddMonoidHom =
      completedFormsRelDifferential A B W p n :=
  rfl

/-- The `D`-linear relative differential, on an element. -/
theorem completedFormsRelDifferentialₗ_apply (n : ℕ) (x : completedPolynomialForms A B W p n) :
    completedFormsRelDifferentialₗ A B W p n x = completedFormsRelDifferential A B W p n x :=
  rfl

/-- **The projection of `Ω̂ⁿ_{D'}` onto the forms with `i` coefficient differentials, as a
`D`-linear map**, which is the `proj` of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`. -/
def completedFormsBidegreeProjectionₗ (n i : ℕ) :
    completedPolynomialForms A B W p n →ₗ[completedDividedPowerRing p (B := (B : Type uB))]
      completedPolynomialForms A B W p n where
  toFun := PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (formsBidegreeProjection A B W n i).toAddMonoidHom
  map_add' := map_add _
  map_smul' c x :=
    mapAddHom_smul_polynomialForms A B W p (formsBidegreeProjection A B W n i).toAddMonoidHom
      (fun b y ↦ formsBidegreeProjection_smul A B W n i b y) c x

/-- The `D`-linear bidegree projection is the additive one. -/
theorem completedFormsBidegreeProjectionₗ_toAddMonoidHom (n i : ℕ) :
    (completedFormsBidegreeProjectionₗ A B W p n i).toAddMonoidHom =
      completedFormsBidegreeProjection A B W p n i :=
  rfl

/-- The `D`-linear bidegree projection, on an element. -/
theorem completedFormsBidegreeProjectionₗ_apply (n i : ℕ)
    (x : completedPolynomialForms A B W p n) :
    completedFormsBidegreeProjectionₗ A B W p n i x =
      completedFormsBidegreeProjection A B W p n i x :=
  rfl

/-- **The completed relative homotopy `ĥ : Ω̂^{n+1}_{D'} → Ω̂ⁿ_{D'}`, as a `D`-linear map**, which
is the `hhat` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`.  Its `D`-linearity is
the completion of `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_smul`. -/
def completedRelativeFormsHomotopyₗ (n : ℕ) :
    completedPolynomialForms A B W p (n + 1) →ₗ[
      completedDividedPowerRing p (B := (B : Type uB))] completedPolynomialForms A B W p n where
  toFun := PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (relativeFormsHomotopy A B W n).toAddMonoidHom
  map_add' := map_add _
  map_smul' c x :=
    mapAddHom_smul_polynomialForms A B W p (relativeFormsHomotopy A B W n).toAddMonoidHom
      (fun b y ↦ relativeFormsHomotopy_smul A B W n b y) c x

/-- The `D`-linear completed homotopy is the additive one. -/
theorem completedRelativeFormsHomotopyₗ_toAddMonoidHom (n : ℕ) :
    (completedRelativeFormsHomotopyₗ A B W p n).toAddMonoidHom =
      completedRelativeFormsHomotopy A B W p n :=
  rfl

/-- The `D`-linear completed homotopy, on an element. -/
theorem completedRelativeFormsHomotopyₗ_apply (n : ℕ)
    (x : completedPolynomialForms A B W p (n + 1)) :
    completedRelativeFormsHomotopyₗ A B W p n x = completedRelativeFormsHomotopy A B W p n x :=
  rfl

/-- **The completed coefficient retraction `ε̂ : Ω̂ⁿ_{D'} → Ω̂ⁿ_D`, as a `D`-linear map**, which is
the `piForm` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`.  Its `D`-linearity is
the completion of `Crystalline.DividedPowerPolynomial.relativeFormsRetraction_smul`; source and
target are modules over the two different rings `D'` and `D`, and it is the restriction of
scalars of the source that makes the single word `D`-linear apply to both. -/
def completedRelativeFormsRetractionₗ (n : ℕ) :
    completedPolynomialForms A B W p n →ₗ[completedDividedPowerRing p (B := (B : Type uB))]
      completedDividedPowerForms p A B.dividedPowers n where
  toFun := PAdicCompletion.mapAddHom p (setIndexedDividedPowerPolynomialAlgebra B W)
    (B : Type uB) (relativeFormsRetraction A B W n).toAddMonoidHom
  map_add' := map_add _
  map_smul' c x :=
    mapAddHom_smul_polynomialFormsToForms A B W p
      (relativeFormsRetraction A B W n).toAddMonoidHom
      (fun b y ↦ relativeFormsRetraction_smul A B W n b y) c x

/-- The `D`-linear completed retraction is the additive one. -/
theorem completedRelativeFormsRetractionₗ_toAddMonoidHom (n : ℕ) :
    (completedRelativeFormsRetractionₗ A B W p n).toAddMonoidHom =
      completedRelativeFormsRetraction A B W p n :=
  rfl

/-- The `D`-linear completed retraction, on an element. -/
theorem completedRelativeFormsRetractionₗ_apply (n : ℕ)
    (x : completedPolynomialForms A B W p n) :
    completedRelativeFormsRetractionₗ A B W p n x = completedRelativeFormsRetraction A B W p n x :=
  rfl

/-- **The completed comparison `ψ̂ : Ω̂ⁿ_D → Ω̂ⁿ_{D'}`, as a `D`-linear map**, which is the
`iotaForm` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`.

The map `Crystalline.DividedPowerPolynomial.completedCoefficientFormsMap` is semilinear over
the *uncompleted* coefficient inclusion `B → P`; what makes it `D`-linear is exactly the
restriction of scalars along `D → D'` installed above, under which semilinearity over the
completed ring map becomes linearity. -/
def completedCoefficientFormsMapₗ (n : ℕ) :
    completedDividedPowerForms p A B.dividedPowers n →ₗ[
      completedDividedPowerRing p (B := (B : Type uB))] completedPolynomialForms A B W p n where
  toFun := PAdicCompletion.mapAddHom p (B : Type uB)
    (setIndexedDividedPowerPolynomialAlgebra B W) (coefficientFormsMap A B W n).toAddMonoidHom
  map_add' := map_add _
  map_smul' c x :=
    mapAddHom_smul_formsToPolynomialForms A B W p (coefficientFormsMap A B W n).toAddMonoidHom
      (fun b y ↦ map_smul (coefficientFormsMap A B W n) b y) c x

/-- The `D`-linear completed comparison is the semilinear one. -/
theorem completedCoefficientFormsMapₗ_toAddMonoidHom (n : ℕ) :
    (completedCoefficientFormsMapₗ A B W p n).toAddMonoidHom =
      (completedCoefficientFormsMap A B W p n).toAddMonoidHom :=
  (completedCoefficientFormsMap_toAddMonoidHom A B W p n).symm

/-- The `D`-linear completed comparison, on an element. -/
theorem completedCoefficientFormsMapₗ_apply (n : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers n) :
    completedCoefficientFormsMapₗ A B W p n x = completedCoefficientFormsMap A B W p n x :=
  (DFunLike.congr_fun (completedCoefficientFormsMap_toAddMonoidHom A B W p n) x).symm

/-! ### The completed forms of `D'` as a de Rham complex over `D` -/

/-- **The wedge product `Ω̂ⁱ_{D'} × Ω̂¹_{D'} → Ω̂^{i+1}_{D'}`, read `D`-bilinearly**, which is the
`wedge` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`.  The underlying function is
the library's `Crystalline.completedDividedPowerWedge` of the divided power polynomial algebra;
only the ring of bilinearity is restricted. -/
def completedPolynomialFormsWedge (i : ℕ) :
    completedPolynomialForms A B W p i →ₗ[completedDividedPowerRing p (B := (B : Type uB))]
      completedPolynomialForms A B W p 1 →ₗ[completedDividedPowerRing p (B := (B : Type uB))]
        completedPolynomialForms A B W p (i + 1) :=
  CompletedDeRham.bilinearOfRingHom (completedDividedPowerRing p (B := (B : Type uB)))
    (completedDividedPowerPolynomialRing B W p) (completedCoefficientRingHom A B W p)
    (completedPolynomialForms A B W p)
    (completedDividedPowerWedge p A (setIndexedDividedPowerPolynomialDividedPowers B W))
    (completedPolynomialForms_smul A B W p) i

/-- The `D`-bilinear wedge product is the library's wedge product. -/
@[simp] theorem completedPolynomialFormsWedge_apply (i : ℕ)
    (x : completedPolynomialForms A B W p i) (y : completedPolynomialForms A B W p 1) :
    completedPolynomialFormsWedge A B W p i x y =
      completedDividedPowerWedge p A (setIndexedDividedPowerPolynomialDividedPowers B W) i x y :=
  rfl

/-- **The universal differential `D → Ω̂¹_{D'}`**, the `dmap` of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`: the universal differential of `D'`
precomposed with the ring map `D → D'`.  It is the differential of a scalar of the base, read in
the forms of the polynomial algebra, and it is where the Leibniz rule of the complex over `D`
takes its values. -/
def completedPolynomialFormsDifferential :
    completedDividedPowerRing p (B := (B : Type uB)) → completedPolynomialForms A B W p 1 :=
  fun c ↦ completedFormsDifferential p A (setIndexedDividedPowerPolynomialDividedPowers B W)
    (completedCoefficientRingHom A B W p c)

omit [LinearOrder W] in
/-- **The Leibniz rule `d (c · ω) = c · d ω + d c ∧ ω` on `Ω̂^*_{D'}` over `D`**, which is the
`hleib` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` re-read over `D`.  It is the
Leibniz rule of `Ω̂^*_{D'}` over its own ring `D'`,
`Crystalline.isGradedLeibniz_completedDividedPower`, restricted along `D → D'`. -/
theorem isGradedLeibniz_completedPolynomialForms [LinearOrder W] :
    CompletedDeRham.IsGradedLeibniz (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W))
      (completedPolynomialFormsDifferential A B W p) :=
  CompletedDeRham.isGradedLeibniz_of_ringHom
    (completedDividedPowerRing p (B := (B : Type uB)))
    (completedDividedPowerPolynomialRing B W p) (completedCoefficientRingHom A B W p)
    (completedPolynomialForms A B W p)
    (completedDividedPowerWedge p A (setIndexedDividedPowerPolynomialDividedPowers B W))
    (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W))
    (completedFormsDifferential p A (setIndexedDividedPowerPolynomialDividedPowers B W))
    (completedPolynomialForms_smul A B W p) (fun _ _ _ ↦ rfl)
    (isGradedLeibniz_completedDividedPower p A
      (setIndexedDividedPowerPolynomialDividedPowers B W))

/-- **The Leibniz rule for the base part of the differential of `Ω̂^*_{D'}` over `D`**, which is
the `hleibBase` of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`.  The relative part
is `D`-linear, so the whole of the Leibniz correction stays with the base part; this is
`Crystalline.CompletedDeRham.isGradedLeibniz_base_of_split` at the splitting
`..._completedDividedPowerDeRham_eq_completedFormsRelDifferential_add`, in the namespace
`Crystalline.DividedPowerPolynomial`. -/
theorem isGradedLeibniz_completedFormsBaseDifferential :
    CompletedDeRham.IsGradedLeibniz (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedFormsBaseDifferential A B W p)
      (completedPolynomialFormsDifferential A B W p) :=
  CompletedDeRham.isGradedLeibniz_base_of_split
    (completedDividedPowerRing p (B := (B : Type uB))) (completedPolynomialForms A B W p)
    (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W))
    (completedFormsRelDifferentialₗ A B W p) (completedFormsBaseDifferential A B W p)
    (isGradedLeibniz_completedPolynomialForms A B W p)
    (completedDividedPowerDeRham_eq_completedFormsRelDifferential_add A B W p)

/-- The completed projection `ψ̂ ε̂`, read as the composite of the two `D`-linear maps. -/
theorem completedRelativeFormsProjection_eq_comp (n : ℕ)
    (x : completedPolynomialForms A B W p n) :
    completedRelativeFormsProjection A B W p n x =
      completedCoefficientFormsMapₗ A B W p n (completedRelativeFormsRetractionₗ A B W p n x) :=
  (DFunLike.congr_fun (completedRelativeFormsProjection_eq A B W p n) x).trans
    (DFunLike.congr_fun (PAdicCompletion.mapAddHom_comp p
      (setIndexedDividedPowerPolynomialAlgebra B W) (B : Type uB)
      (setIndexedDividedPowerPolynomialAlgebra B W)
      (relativeFormsRetraction A B W n).toAddMonoidHom
      (coefficientFormsMap A B W n).toAddMonoidHom) x)

/-- **The completed comparison `ψ̂` carries the universal differential of `D` to that of `D'`**:
`ψ̂ (d c) = d c` read in `Ω̂¹_{D'}`.  It is the completion of
`Crystalline.DividedPowerPolynomial.coefficientFormsMap_dividedPowerOneForm`, both sides being
the completion of one additive map `B → Ω¹_{P/A,δ'}`. -/
theorem completedCoefficientFormsMapₗ_completedFormsDifferential
    (c : completedDividedPowerRing p (B := (B : Type uB))) :
    completedCoefficientFormsMapₗ A B W p 1
        (completedFormsDifferential p A B.dividedPowers c) =
      completedPolynomialFormsDifferential A B W p c := by
  have huncomp : (coefficientFormsMap A B W 1).toAddMonoidHom.comp
        (dividedPowerOneForm A B.dividedPowers) =
      (dividedPowerOneForm A (setIndexedDividedPowerPolynomialDividedPowers B W)).comp
        (algebraMap (B : Type uB)
          (setIndexedDividedPowerPolynomialAlgebra B W)).toAddMonoidHom :=
    AddMonoidHom.ext fun b ↦ coefficientFormsMap_dividedPowerOneForm A B W b
  refine Eq.trans (DFunLike.congr_fun (PAdicCompletion.mapAddHom_comp p (B : Type uB)
      (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)
      (dividedPowerOneForm A B.dividedPowers)
      (coefficientFormsMap A B W 1).toAddMonoidHom).symm c) ?_
  refine Eq.trans (DFunLike.congr_fun (congrArg (fun g : (B : Type uB) →+
        dividedPowerPolynomialForms A B W 1 ↦
      PAdicCompletion.mapAddHom p (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W) g) huncomp) c) ?_
  refine Eq.trans (DFunLike.congr_fun (PAdicCompletion.mapAddHom_comp p (B : Type uB)
      (setIndexedDividedPowerPolynomialAlgebra B W)
      (setIndexedDividedPowerPolynomialAlgebra B W)
      (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)).toAddMonoidHom
      (dividedPowerOneForm A (setIndexedDividedPowerPolynomialDividedPowers B W))) c) ?_
  exact congrArg (fun z : completedDividedPowerPolynomialRing B W p ↦
      completedFormsDifferential p A (setIndexedDividedPowerPolynomialDividedPowers B W) z)
    (completedCoefficientRingHom_apply A B W p c).symm

/-- **`π̂_{1,1} ∘ ψ̂ = ψ̂`, as `D`-linear maps.** -/
theorem completedFormsBidegreeProjectionₗ_comp_completedCoefficientFormsMapₗ (n : ℕ) :
    completedFormsBidegreeProjectionₗ A B W p n n ∘ₗ completedCoefficientFormsMapₗ A B W p n =
      completedCoefficientFormsMapₗ A B W p n :=
  LinearMap.ext fun z ↦ by
    rw [LinearMap.comp_apply, completedCoefficientFormsMapₗ_apply]
    exact completedFormsBidegreeProjection_completedCoefficientFormsMap A B W p n z

/-- **The connection of `M` over `D`, pushed into the forms of `D'` along `ψ̂`**: this is the
connection the source's clause starts from, `M` being a `D`-module with a connection with values
in `M ⊗̂_D Ω̂¹_D`. -/
def pushedConnection (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M) :
    CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p 1) (completedPolynomialFormsDifferential A B W p) M :=
  CompletedDeRham.pushforwardConnection p (completedDividedPowerRing p (B := (B : Type uB))) M
    (completedCoefficientFormsMapₗ A B W p 1)
    (completedCoefficientFormsMapₗ_completedFormsDifferential A B W p) nabla

/-- **`∇` takes its values in coefficient degree one** — the `hnabla` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`, discharged for the connection pushed
into `Ω̂¹_{D'}` from `Ω̂¹_D`.

The image of `ψ̂` is the top coefficient degree, by
`Crystalline.DividedPowerPolynomial.completedFormsBidegreeProjection_completedCoefficientFormsMap`,
and in exterior degree one the top coefficient degree is one.  For a connection that does *not*
come from `Ω̂¹_D` the statement is false, which is why the abstract theorem carries it. -/
theorem completedLTensor_pushedConnection (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M) (m : M) :
    CompletedDeRham.completedLTensor p (completedDividedPowerRing p (B := (B : Type uB))) M
        (completedFormsBidegreeProjectionₗ A B W p 1 1) (pushedConnection A B W p M nabla m) =
      pushedConnection A B W p M nabla m :=
  CompletedDeRham.completedLTensor_pushforwardConnection p
    (completedDividedPowerRing p (B := (B : Type uB))) M
    (completedCoefficientFormsMapₗ A B W p 1)
    (completedCoefficientFormsMapₗ_completedFormsDifferential A B W p) nabla
    (completedFormsBidegreeProjectionₗ A B W p 1 1)
    (completedFormsBidegreeProjectionₗ_comp_completedCoefficientFormsMapₗ A B W p 1) m

/-! ### The instantiation of the perturbation argument at the completed forms -/

/-- **The completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] at the genuine completed divided
power forms.**

Let `D` be the `p`-adic completion of the divided power ring `B`, let
`D' = B⟨x_w : w ∈ W⟩^∧`, and let `M` be a `D`-module with a completed connection
`∇ : M → M ⊗̂_D Ω̂¹_{D'}` whose de Rham differential squares to zero and which takes its values in
coefficient degree one.  Then the comparison `M ⊗̂_D Ω̂^*_D → M ⊗̂_D Ω̂^*_{D'}` is a homotopy
equivalence of the connection-twisted de Rham complexes: `M ⊗̂_D Ω̂^*_D` carries a differential
`d_L` squaring to zero, the perturbed `ι'` and `π'` are maps of complexes, `π' ι' = 1`, and
`ι' π'` is chain homotopic to the identity.

This is `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` instantiated at the genuine
forms.  Everything it asks for is discharged here: the `D`-module structure of
`Crystalline.DividedPowerPolynomial.moduleCompletedPolynomialForms`, the five `D`-linear maps
`..._completedFormsRelDifferentialₗ`, `..._completedFormsBidegreeProjectionₗ`,
`..._completedRelativeFormsHomotopyₗ`, `..._completedCoefficientFormsMapₗ` and
`..._completedRelativeFormsRetractionₗ`, the splitting `d = d_rel + d_base`, `d_rel² = 0`, the
relative contraction identity and the three side conditions of a special deformation retract, the
bidegree bookkeeping `∑ πᵢ = id`, `π_l d_base π_i = 0`, `π_l (− ∧ π₁ η) π_i = 0` and
`ĥ π = π ĥ`.  What remains as a hypothesis is the vanishing of the curvature of the connection,
which is a hypothesis everywhere in this library — including on
`Crystalline.CompletedDeRham.complex` itself — and the statement that `∇` takes its values in
coefficient degree one, which is a property of `∇` and is discharged for a connection pushed
forward from `Ω̂¹_D` by
`Crystalline.DividedPowerPolynomial.completedFormsBidegreeProjection_completedCoefficientFormsMap`.

No tag attribute is placed: the clause at `M = D` is already tagged on
`Crystalline.DividedPowerPolynomial.completedRelativeFormsHomotopy_identity`, and the clause with
a module is tagged, with the source's own hypothesis of integrability in place of the square-zero
identity, on `Crystalline.DividedPowerPolynomial.exists_homotopyEquiv_isIntegrable`, which
derives that identity from this statement's `hsq` input by
`Crystalline.DividedPowerPolynomial.isSquareZero_pushedConnection`. -/
theorem exists_twistedHomotopyEquiv_completedPolynomialForms (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p 1) (completedPolynomialFormsDifferential A B W p) M)
    (hsq : CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
      nabla (isGradedLeibniz_completedPolynomialForms A B W p))
    (hnabla : ∀ m : M, CompletedDeRham.completedLTensor p
      (completedDividedPowerRing p (B := (B : Type uB))) M
      (completedFormsBidegreeProjectionₗ A B W p 1 1) (nabla m) = nabla m) :
    ∃ (dL : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M →+
          CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers (i + 1)) M)
      (iota' : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M →+
          CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p i) M)
      (pi' : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p i) M →+
          CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M)
      (H : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p (i + 1)) M →+
          CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p i) M),
      (∀ (i : ℕ) (x : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedDividedPowerForms p A B.dividedPowers i) M), dL (i + 1) (dL i x) = 0) ∧
        (∀ (i : ℕ) (x : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M), pi' i (iota' i x) = x) ∧
          (∀ (i : ℕ) (x : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                (completedDividedPowerForms p A B.dividedPowers i) M),
              CompletedDeRham.differential p (completedDividedPowerRing p (B := (B : Type uB)))
                  (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
                  (completedDividedPowerDeRham p A
                    (setIndexedDividedPowerPolynomialDividedPowers B W)) M nabla
                  (isGradedLeibniz_completedPolynomialForms A B W p) i (iota' i x) =
                iota' (i + 1) (dL i x)) ∧
            (∀ (i : ℕ) (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                  (completedPolynomialForms A B W p i) M),
                pi' (i + 1) (CompletedDeRham.differential p
                    (completedDividedPowerRing p (B := (B : Type uB)))
                    (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
                    (completedDividedPowerDeRham p A
                      (setIndexedDividedPowerPolynomialDividedPowers B W)) M nabla
                    (isGradedLeibniz_completedPolynomialForms A B W p) i z) =
                  dL i (pi' i z)) ∧
              (∀ x : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                  (completedPolynomialForms A B W p 0) M,
                  H 0 (CompletedDeRham.differential p
                      (completedDividedPowerRing p (B := (B : Type uB)))
                      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
                      (completedDividedPowerDeRham p A
                        (setIndexedDividedPowerPolynomialDividedPowers B W)) M nabla
                      (isGradedLeibniz_completedPolynomialForms A B W p) 0 x) +
                    iota' 0 (pi' 0 x) = x) ∧
                ∀ (n : ℕ) (x : CompletedTensor p
                    (completedDividedPowerRing p (B := (B : Type uB)))
                    (completedPolynomialForms A B W p (n + 1)) M),
                  CompletedDeRham.differential p
                        (completedDividedPowerRing p (B := (B : Type uB)))
                        (completedPolynomialForms A B W p)
                        (completedPolynomialFormsWedge A B W p)
                        (completedDividedPowerDeRham p A
                          (setIndexedDividedPowerPolynomialDividedPowers B W)) M nabla
                        (isGradedLeibniz_completedPolynomialForms A B W p) n (H n x) +
                      H (n + 1) (CompletedDeRham.differential p
                        (completedDividedPowerRing p (B := (B : Type uB)))
                        (completedPolynomialForms A B W p)
                        (completedPolynomialFormsWedge A B W p)
                        (completedDividedPowerDeRham p A
                          (setIndexedDividedPowerPolynomialDividedPowers B W)) M nabla
                        (isGradedLeibniz_completedPolynomialForms A B W p) (n + 1) x) +
                    iota' (n + 1) (pi' (n + 1) x) = x := by
  refine CompletedDeRham.exists_twistedHomotopyEquiv p
    (completedDividedPowerRing p (B := (B : Type uB))) (completedPolynomialForms A B W p)
    (completedDividedPowerForms p A B.dividedPowers) (completedPolynomialFormsWedge A B W p)
    (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W))
    (completedFormsRelDifferentialₗ A B W p) (completedFormsBaseDifferential A B W p) M nabla
    (isGradedLeibniz_completedPolynomialForms A B W p)
    (isGradedLeibniz_completedFormsBaseDifferential A B W p)
    (completedFormsBidegreeProjectionₗ A B W p) (completedRelativeFormsHomotopyₗ A B W p)
    (completedCoefficientFormsMapₗ A B W p) (completedRelativeFormsRetractionₗ A B W p)
    (completedDividedPowerDeRham_eq_completedFormsRelDifferential_add A B W p)
    (fun i ↦ LinearMap.ext fun z ↦
      completedFormsRelDifferential_completedFormsRelDifferential A B W p i z)
    hsq ?_ ?_
    (fun i ↦ LinearMap.ext fun z ↦
      completedRelativeFormsHomotopy_completedRelativeFormsHomotopy A B W p i z)
    (fun i ↦ LinearMap.ext fun z ↦ by
      rw [LinearMap.comp_apply, completedCoefficientFormsMapₗ_apply]
      exact completedRelativeFormsHomotopy_completedCoefficient A B W p i z)
    (fun i ↦ LinearMap.ext fun z ↦
      completedRelativeFormsRetraction_completedRelativeFormsHomotopy A B W p i z)
    (fun i ↦ LinearMap.ext fun z ↦ by
      rw [LinearMap.comp_apply, completedCoefficientFormsMapₗ_apply]
      exact completedRelativeFormsRetraction_completedCoefficient A B W p i z)
    (completedFormsBidegreeProjection_sum A B W p) hnabla
    (fun n l i hli omega ↦ LinearMap.ext fun eta ↦
      completedFormsBidegreeProjection_wedge_eq_zero A B W p n l i hli omega eta)
    (fun n l i hli omega ↦
      completedFormsBidegreeProjection_completedFormsBaseDifferential_eq_zero A B W p n hli omega)
    (fun n i ↦ LinearMap.ext fun z ↦
      completedRelativeFormsHomotopy_completedFormsBidegreeProjection A B W p n i z)
  · refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      ← completedRelativeFormsProjection_eq_comp]
    exact DFunLike.congr_fun
      (completedRelativeFormsRelContraction_addHom_zero A B W p) z
  · intro n
    refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      ← completedRelativeFormsProjection_eq_comp]
    exact DFunLike.congr_fun
      (completedRelativeFormsRelContraction_addHom A B W p n) z

/-- **The completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] for a `D`-module with a
connection of its own**: the form the source states it in, and the form step R5 of
[Stacks, Proposition 60.21.3, Tag 07LG] consumes.

`M` is a `D`-module with a completed connection `∇ : M → M ⊗̂_D Ω̂¹_D` whose de Rham differential
on `M ⊗̂_D Ω̂^*_{D'}`, after `∇` is pushed into the forms of `D'` along `ψ̂`, squares to zero.  The
comparison `M ⊗̂_D Ω̂^*_D → M ⊗̂_D Ω̂^*_{D'}` is then a homotopy equivalence of the twisted de Rham
complexes.

This is
`Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_completedPolynomialForms` with
its last hypothesis discharged by
`Crystalline.DividedPowerPolynomial.completedLTensor_pushedConnection`: its one remaining input
is the vanishing of the curvature, which
`Crystalline.DividedPowerPolynomial.isSquareZero_pushedConnection` obtains from the source's
hypothesis that `∇` is integrable. -/
theorem exists_twistedHomotopyEquiv_pushedConnection (M : Type uM) [AddCommGroup M]
    [Module (completedDividedPowerRing p (B := (B : Type uB))) M]
    (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedDividedPowerForms p A B.dividedPowers 1)
      (completedFormsDifferential p A B.dividedPowers) M)
    (hsq : CompletedDeRham.IsSquareZero p (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
      (completedDividedPowerDeRham p A (setIndexedDividedPowerPolynomialDividedPowers B W)) M
      (pushedConnection A B W p M nabla)
      (isGradedLeibniz_completedPolynomialForms A B W p)) :
    ∃ (dL : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M →+
          CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers (i + 1)) M)
      (iota' : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M →+
          CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p i) M)
      (pi' : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p i) M →+
          CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M)
      (H : ∀ i, CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p (i + 1)) M →+
          CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedPolynomialForms A B W p i) M),
      (∀ (i : ℕ) (x : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
          (completedDividedPowerForms p A B.dividedPowers i) M), dL (i + 1) (dL i x) = 0) ∧
        (∀ (i : ℕ) (x : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
            (completedDividedPowerForms p A B.dividedPowers i) M), pi' i (iota' i x) = x) ∧
          (∀ (i : ℕ) (x : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                (completedDividedPowerForms p A B.dividedPowers i) M),
              CompletedDeRham.differential p (completedDividedPowerRing p (B := (B : Type uB)))
                  (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
                  (completedDividedPowerDeRham p A
                    (setIndexedDividedPowerPolynomialDividedPowers B W)) M
                  (pushedConnection A B W p M nabla)
                  (isGradedLeibniz_completedPolynomialForms A B W p) i (iota' i x) =
                iota' (i + 1) (dL i x)) ∧
            (∀ (i : ℕ) (z : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                  (completedPolynomialForms A B W p i) M),
                pi' (i + 1) (CompletedDeRham.differential p
                    (completedDividedPowerRing p (B := (B : Type uB)))
                    (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
                    (completedDividedPowerDeRham p A
                      (setIndexedDividedPowerPolynomialDividedPowers B W)) M
                    (pushedConnection A B W p M nabla)
                    (isGradedLeibniz_completedPolynomialForms A B W p) i z) =
                  dL i (pi' i z)) ∧
              (∀ x : CompletedTensor p (completedDividedPowerRing p (B := (B : Type uB)))
                  (completedPolynomialForms A B W p 0) M,
                  H 0 (CompletedDeRham.differential p
                      (completedDividedPowerRing p (B := (B : Type uB)))
                      (completedPolynomialForms A B W p) (completedPolynomialFormsWedge A B W p)
                      (completedDividedPowerDeRham p A
                        (setIndexedDividedPowerPolynomialDividedPowers B W)) M
                      (pushedConnection A B W p M nabla)
                      (isGradedLeibniz_completedPolynomialForms A B W p) 0 x) +
                    iota' 0 (pi' 0 x) = x) ∧
                ∀ (n : ℕ) (x : CompletedTensor p
                    (completedDividedPowerRing p (B := (B : Type uB)))
                    (completedPolynomialForms A B W p (n + 1)) M),
                  CompletedDeRham.differential p
                        (completedDividedPowerRing p (B := (B : Type uB)))
                        (completedPolynomialForms A B W p)
                        (completedPolynomialFormsWedge A B W p)
                        (completedDividedPowerDeRham p A
                          (setIndexedDividedPowerPolynomialDividedPowers B W)) M
                        (pushedConnection A B W p M nabla)
                        (isGradedLeibniz_completedPolynomialForms A B W p) n (H n x) +
                      H (n + 1) (CompletedDeRham.differential p
                        (completedDividedPowerRing p (B := (B : Type uB)))
                        (completedPolynomialForms A B W p)
                        (completedPolynomialFormsWedge A B W p)
                        (completedDividedPowerDeRham p A
                          (setIndexedDividedPowerPolynomialDividedPowers B W)) M
                        (pushedConnection A B W p M nabla)
                        (isGradedLeibniz_completedPolynomialForms A B W p) (n + 1) x) +
                    iota' (n + 1) (pi' (n + 1) x) = x :=
  exists_twistedHomotopyEquiv_completedPolynomialForms A B W p M
    (pushedConnection A B W p M nabla) hsq (completedLTensor_pushedConnection A B W p M nabla)

end CompletedScalarsLinear

end CompletedScalars

end DividedPowerPolynomial

end Crystalline

end
