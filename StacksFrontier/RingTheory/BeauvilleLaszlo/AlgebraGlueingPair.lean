module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.RingTheory.BeauvilleLaszlo.AlgebraGlueing

/-!
# Cartesian data of algebras over a Beauville--Laszlo pair

Let `(R → R', f)` be a glueing pair, write `R_f` for the localization of `R` away from `f` and
`R'_f` for the localization of `R'` away from the image of `f`. A *cartesian datum of algebras*
over the pair consists of an `R'`-algebra `A'`, an `R_f`-algebra `A₁`, base changes `C₂` of `A'`
and `C₁` of `A₁` to `R'_f`, and an isomorphism `C₂ ≃ C₁` of `R'_f`-algebras. The
Beauville--Laszlo theorem produces from such a datum a glueable `R`-algebra whose two base
changes are `A'` and `A₁`.

## Main results

* `BeauvilleLaszlo.isPushout_localizationAway`: the localization square of a pair,
  `R' ⊗[R] R_f ≅ R'_f`.
* `BeauvilleLaszlo.exists_glued_of_cartesianDatum`: from a cartesian datum of algebras over a
  glueing pair one obtains a glueable `R`-algebra `A`, of cardinality at most
  `max ℵ₀ (max #A' #A₁)`, with `A' ≅ R' ⊗[R] A` and `A₁ ≅ R_f ⊗[R] A`, whose two images in
  `C₁` agree under the glueing isomorphism.
* `BeauvilleLaszlo.IsGlueableFor.of_linearEquiv` and
  `BeauvilleLaszlo.IsGlueableFor.of_ringEquiv`: glueability only depends on the isomorphism
  class of the module, resp. of the algebra.

## References

* [Stacks Project, Tag 0BP2](https://stacks.math.columbia.edu/tag/0BP2)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/

@[expose] public section

open scoped TensorProduct

namespace BeauvilleLaszlo

universe u

section LocalizationSquare

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)

/-- The localization `R'_f` of `R'` away from the image of `f` is an algebra over the
localization `R_f` of `R` away from `f`, via `Localization.awayMap`. -/
noncomputable instance awayAlgebra :
    Algebra (Localization.Away f) (Localization.Away ((algebraMap R R') f)) :=
  (Localization.awayMap (algebraMap R R') f).toAlgebra

/-- The structure maps `R → R_f → R'_f` compose to the structure map `R → R'_f`. -/
instance awayIsScalarTower :
    IsScalarTower R (Localization.Away f) (Localization.Away ((algebraMap R R') f)) :=
  .of_algebraMap_eq' <| by
    rw [RingHom.algebraMap_toAlgebra,
      IsScalarTower.algebraMap_eq R R' (Localization.Away ((algebraMap R R') f))]
    exact (IsLocalization.map_comp _).symm

/-- **The localization square of a pair `(R → R', f)` is cartesian**: the localization `R'_f` of
`R'` away from the image of `f` is the base change `R' ⊗[R] R_f` of the localization of `R`
away from `f`. -/
theorem isPushout_localizationAway :
    Algebra.IsPushout R R' (Localization.Away f)
      (Localization.Away ((algebraMap R R') f)) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid R' (Submonoid.powers f))
      (Localization.Away ((algebraMap R R') f)) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  exact Algebra.isPushout_of_isLocalization (S := Submonoid.powers f)
    (A := Localization.Away f) (T := R') (B := Localization.Away ((algebraMap R R') f))

end LocalizationSquare

section Transport

variable {R R' A A₂ : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  [AddCommGroup A] [Module R A] [AddCommGroup A₂] [Module R A₂]

/-- The `R`-linear equivalence between the pairs of base changes of `A` and of `A₂` induced by
an `R`-linear equivalence `ε : A ≃ₗ[R] A₂`. -/
private noncomputable def congrPair (f : R) (ε : A ≃ₗ[R] A₂) :
    (TensorProduct R A R' × TensorProduct R A (Localization.Away f)) ≃ₗ[R]
      TensorProduct R A₂ R' × TensorProduct R A₂ (Localization.Away f) :=
  (TensorProduct.congr ε (LinearEquiv.refl R R')).prodCongr
    (TensorProduct.congr ε (LinearEquiv.refl R (Localization.Away f)))

/-- The `R`-linear equivalence between the base changes of `A` and of `A₂` to `R'_f` induced by
an `R`-linear equivalence `ε : A ≃ₗ[R] A₂`. -/
private noncomputable def congrAway (f : R) (ε : A ≃ₗ[R] A₂) :
    TensorProduct R A (Localization.Away ((algebraMap R R') f)) ≃ₗ[R]
      TensorProduct R A₂ (Localization.Away ((algebraMap R R') f)) :=
  TensorProduct.congr ε (LinearEquiv.refl R (Localization.Away ((algebraMap R R') f)))

/-- The map `toTensorBaseChanges` of the Beauville--Laszlo module sequence commutes with an
`R`-linear equivalence `ε : A ≃ₗ[R] A₂` and the induced equivalence `congrPair f ε`. -/
private theorem congrPair_comp_toTensorBaseChanges (f : R) (ε : A ≃ₗ[R] A₂) :
    toTensorBaseChanges (S := R') A₂ f ∘ₗ (ε : A →ₗ[R] A₂) =
      (congrPair (R' := R') f ε : _ →ₗ[R] _) ∘ₗ toTensorBaseChanges (S := R') A f :=
  LinearMap.ext fun a ↦ by simp [congrPair]

/-- The map `tensorAwayDifference` of the Beauville--Laszlo module sequence commutes with the
equivalences `congrPair f ε` and `congrAway f ε` induced by an `R`-linear equivalence `ε`. -/
private theorem congrAway_comp_tensorAwayDifference (f : R) (ε : A ≃ₗ[R] A₂) :
    tensorAwayDifference (S := R') A₂ f ∘ₗ (congrPair (R' := R') f ε : _ →ₗ[R] _) =
      (congrAway (R' := R') f ε : _ →ₗ[R] _) ∘ₗ tensorAwayDifference (S := R') A f := by
  have hb : ∀ x : TensorProduct R A R',
      baseChangeToAway (S := R') A₂ f (TensorProduct.congr ε (LinearEquiv.refl R R') x) =
        congrAway (R' := R') f ε (baseChangeToAway (S := R') A f x) := by
    intro x
    induction x with
    | tmul a s => simp [congrAway]
    | add x y hx hy => simp [hx, hy]
  have hl : ∀ x : TensorProduct R A (Localization.Away f),
      localizedBaseChangeToAway (S := R') A₂ f
          (TensorProduct.congr ε (LinearEquiv.refl R (Localization.Away f)) x) =
        congrAway (R' := R') f ε (localizedBaseChangeToAway (S := R') A f x) := by
    intro x
    induction x with
    | tmul a s => simp [congrAway]
    | add x y hx hy => simp [hx, hy]
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, tensorAwayDifference_apply,
    LinearEquiv.coe_coe, congrPair, LinearEquiv.prodCongr_apply, map_sub]
  rw [hb x.1, hl x.2]

/-- **Glueability is invariant under isomorphism of modules.** -/
theorem IsGlueableFor.of_linearEquiv (f : R) (ε : A ≃ₗ[R] A₂)
    (h : IsGlueableFor (S := R') A f) : IsGlueableFor (S := R') A₂ f := by
  obtain ⟨hinj, hex, hsurj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have hcomp : Function.Injective
        (toTensorBaseChanges (S := R') A₂ f ∘ₗ (ε : A →ₗ[R] A₂)) := by
      rw [congrPair_comp_toTensorBaseChanges (R' := R') f ε]
      exact (congrPair (R' := R') f ε).injective.comp hinj
    rw [LinearMap.coe_comp] at hcomp
    exact hcomp.of_comp_right ε.surjective
  · exact Function.Exact.of_ladder_linearEquiv_of_exact
      (e₁ := ε) (e₂ := congrPair (R' := R') f ε) (e₃ := congrAway (R' := R') f ε)
      (congrPair_comp_toTensorBaseChanges (R' := R') f ε)
      (congrAway_comp_tensorAwayDifference (R' := R') f ε) hex
  · intro z
    obtain ⟨y, hy⟩ := hsurj ((congrAway (R' := R') f ε).symm z)
    refine ⟨congrPair (R' := R') f ε y, ?_⟩
    have := LinearMap.congr_fun (congrAway_comp_tensorAwayDifference (R' := R') f ε) y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, hy, LinearEquiv.apply_symm_apply]

end Transport

section TransportAlgebra

variable {R R' A A₂ : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  [CommRing A] [Algebra R A] [CommRing A₂] [Algebra R A₂]

/-- **Glueability is invariant under isomorphism of algebras.** -/
theorem IsGlueableFor.of_ringEquiv (f : R) (e : A ≃ₐ[R] A₂)
    (h : IsGlueableFor (S := R') A f) : IsGlueableFor (S := R') A₂ f :=
  IsGlueableFor.of_linearEquiv (R' := R') f e.toLinearEquiv h

end TransportAlgebra

section CartesianDatum

/-- **The Beauville--Laszlo theorem for a cartesian datum of algebras.** Let `(R → R', f)` be a
glueing pair, let `A'` be an `R'`-algebra and `A₁` an `R_f`-algebra, let `C₂` be the base change
of `A'` to `R'_f` and `C₁` the base change of `A₁` to `R'_f`, and let `ψ : C₂ ≃ C₁` be an
isomorphism of `R'_f`-algebras. Then there is an `R`-algebra `A`, glueable for `(R → R', f)` and
of cardinality at most `max ℵ₀ (max #A' #A₁)`, whose base change to `R'` is `A'`, whose base
change to `R_f` is `A₁`, and whose two images in `C₁` agree under `ψ`. -/
theorem exists_glued_of_cartesianDatum
    {R R' A' A₁ C₁ C₂ : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    (hpair : IsGlueingPair (algebraMap R R') f)
    [CommRing A'] [Algebra R' A'] [Algebra R A'] [IsScalarTower R R' A']
    [CommRing A₁] [Algebra (Localization.Away f) A₁] [Algebra R A₁]
      [IsScalarTower R (Localization.Away f) A₁]
    [CommRing C₁] [Algebra (Localization.Away ((algebraMap R R') f)) C₁]
      [Algebra (Localization.Away f) C₁] [Algebra A₁ C₁]
      [IsScalarTower (Localization.Away f) (Localization.Away ((algebraMap R R') f)) C₁]
      [IsScalarTower (Localization.Away f) A₁ C₁]
    [CommRing C₂] [Algebra (Localization.Away ((algebraMap R R') f)) C₂]
      [Algebra R' C₂] [Algebra A' C₂]
      [IsScalarTower R' (Localization.Away ((algebraMap R R') f)) C₂]
      [IsScalarTower R' A' C₂]
    (h₁ : Algebra.IsPushout (Localization.Away f)
      (Localization.Away ((algebraMap R R') f)) A₁ C₁)
    (h₂ : Algebra.IsPushout R' (Localization.Away ((algebraMap R R') f)) A' C₂)
    (ψ : C₂ ≃ₐ[Localization.Away ((algebraMap R R') f)] C₁) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (_ : Algebra A A') (_ : Algebra A A₁)
      (_ : IsScalarTower R A A') (_ : IsScalarTower R A A₁),
      IsGlueableFor (S := R') A f ∧
      Algebra.IsPushout R R' A A' ∧
      Algebra.IsPushout R (Localization.Away f) A A₁ ∧
      Cardinal.mk A ≤ max Cardinal.aleph0 (max (Cardinal.mk A') (Cardinal.mk A₁)) ∧
      (∀ a : A, ψ (algebraMap A' C₂ (algebraMap A A' a)) =
        algebraMap A₁ C₁ (algebraMap A A₁ a)) := by
  let : Algebra R' C₁ :=
    ((algebraMap (Localization.Away ((algebraMap R R') f)) C₁).comp
      (algebraMap R' (Localization.Away ((algebraMap R R') f)))).toAlgebra
  have htR'C₁ :
      IsScalarTower R' (Localization.Away ((algebraMap R R') f)) C₁ :=
    IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
  let : Algebra R C₁ :=
    ((algebraMap (Localization.Away f) C₁).comp (algebraMap R (Localization.Away f))).toAlgebra
  have htRfC₁ : IsScalarTower R (Localization.Away f) C₁ :=
    IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
  have htRawayC₁ :
      IsScalarTower R (Localization.Away ((algebraMap R R') f)) C₁ := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply R (Localization.Away f) C₁,
      IsScalarTower.algebraMap_apply (Localization.Away f)
        (Localization.Away ((algebraMap R R') f)) C₁,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f)
        (Localization.Away ((algebraMap R R') f))]
  have htRR'C₁ : IsScalarTower R R' C₁ := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply R (Localization.Away ((algebraMap R R') f)) C₁,
      IsScalarTower.algebraMap_apply R' (Localization.Away ((algebraMap R R') f)) C₁,
      ← IsScalarTower.algebraMap_apply R R' (Localization.Away ((algebraMap R R') f))]
  have htA₁C₁ : IsScalarTower R A₁ C₁ := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply R (Localization.Away f) C₁,
      IsScalarTower.algebraMap_apply (Localization.Away f) A₁ C₁,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f) A₁]
  have := (isPushout_localizationAway (R' := R') f).symm
  have : Algebra.IsPushout R R' A₁ C₁ :=
    ((Algebra.IsPushout.comp_iff R (Localization.Away f) R'
      (Localization.Away ((algebraMap R R') f)) (T := A₁) (T' := C₁)).mpr h₁.symm).symm
  set eC : C₁ ≃ₐ[R'] R' ⊗[R] A₁ := (Algebra.IsPushout.equiv R R' A₁ C₁).symm
  have heC_apply : ∀ a : A₁, eC (algebraMap A₁ C₁ a) = (1 : R') ⊗ₜ[R] a :=
    Algebra.IsPushout.equiv_symm_algebraMap_right R R' A₁ C₁
  set ψ' : C₂ ≃ₐ[R'] C₁ := ψ.restrictScalars R'
  set θ : A' →ₐ[R'] R' ⊗[R] A₁ :=
    (eC.toAlgHom.comp ψ'.toAlgHom).comp (IsScalarTower.toAlgHom R' A' C₂)
  have hθ_apply : ∀ x : A', θ x = eC (ψ (algebraMap A' C₂ x)) := fun x ↦ rfl
  have hlm : IsLocalizedModule (Submonoid.powers ((algebraMap R R') f))
      (IsScalarTower.toAlgHom R' A' C₂).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr <|
      (Algebra.isLocalization_iff_isPushout (Submonoid.powers ((algebraMap R R') f))
        (Localization.Away ((algebraMap R R') f))).mpr h₂.symm
  have hθ : IsLocalizedModule (Submonoid.powers ((algebraMap R R') f)) θ.toLinearMap :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers ((algebraMap R R') f))
      (IsScalarTower.toAlgHom R' A' C₂).toLinearMap (ψ'.toLinearEquiv ≪≫ₗ eC.toLinearEquiv)
  let : Algebra (glueSubalgebra θ) A' := (gluedGenericAlgHom θ).toRingHom.toAlgebra
  let : Algebra (glueSubalgebra θ) A₁ := (gluedLocalAlgHom θ).toRingHom.toAlgebra
  have hcA' : ∀ x : glueSubalgebra θ, algebraMap (glueSubalgebra θ) A' x =
      gluedToGeneric θ x := fun _ ↦ rfl
  have hcA₁ : ∀ x : glueSubalgebra θ, algebraMap (glueSubalgebra θ) A₁ x =
      gluedToLocal θ x := fun _ ↦ rfl
  have : IsScalarTower R (glueSubalgebra θ) A' :=
    .of_algebraMap_eq' (RingHom.ext fun r ↦ ((gluedGenericAlgHom θ).commutes r).symm)
  have : IsScalarTower R (glueSubalgebra θ) A₁ :=
    .of_algebraMap_eq' (RingHom.ext fun r ↦ ((gluedLocalAlgHom θ).commutes r).symm)
  refine ⟨glueSubalgebra θ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, isGlueableFor_glueSubalgebra f θ hpair,
    isPushout_glueSubalgebra_generic f hθ hcA' hpair,
    isPushout_glueSubalgebra_local f hθ hcA₁, ?_, ?_⟩
  · calc Cardinal.mk (glueSubalgebra θ : Type u)
        ≤ Cardinal.mk (A' × A₁) := Cardinal.mk_subtype_le _
      _ = Cardinal.mk A' * Cardinal.mk A₁ := by simp
      _ ≤ max (max (Cardinal.mk A') (Cardinal.mk A₁)) Cardinal.aleph0 :=
          Cardinal.mul_le_max _ _
      _ = max Cardinal.aleph0 (max (Cardinal.mk A') (Cardinal.mk A₁)) := max_comm _ _
  · intro a
    have ha : θ (a : A' × A₁).1 = (1 : R') ⊗ₜ[R] (a : A' × A₁).2 := a.2
    refine eC.injective ?_
    rw [heC_apply]
    exact (hθ_apply (a : A' × A₁).1).symm.trans ha

end CartesianDatum

end BeauvilleLaszlo

end
