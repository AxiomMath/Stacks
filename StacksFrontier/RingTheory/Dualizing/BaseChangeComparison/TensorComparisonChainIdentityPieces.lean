module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonSquareOfProjection
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraBaseChangeResolution
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeUnitChainValue
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.RestrictionIsoComputation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMateUnitSquare

/-!
# Pieces of the chain-level identity behind [stacks 0E2A]

Pure tensors of extensions of scalars, typed as elements of the extended modules
(`Dualizing.bcTmul`, `Dualizing.bcTmulC`), and the values on them of the maps composing the two
sides of `Dualizing.chainIdentity`: the composition isomorphisms of extensions of scalars, the
chain-level projection formula, the comparison of [stacks 0661] and the base change of the
algebra resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
  (hP : CochainComplex.KFlat.{uR, max v uA uRp} P)
  (p : P ⟶ algebraComplex.{max v uRp} (algebraMap R A)) [QuasiIso p]


section ExtendScalarsComp

/-- A pure tensor of the base change `(extendScalars f).obj M`, typed as an element of it. -/
def bcTmul {S : Type uR} {T : Type uA} [CommRing S] [CommRing T] (f : S →+* T)
    {M : ModuleCat.{v} S} (t : T) (m : M) :
    (ModuleCat.extendScalars.{uR, uA, v} f).obj M :=
  t ⊗ₜ[S, f] m

section BcTmul

variable {S : Type uR} {T : Type uA} [CommRing S] [CommRing T] (f : S →+* T)
  {M : ModuleCat.{v} S}

/-- Scalar multiplication by `T` on a pure tensor: `t • (t' ⊗ m) = (t * t') ⊗ m`. -/
theorem bcTmul_smul (t t' : T) (m : M) :
    t • bcTmul.{uR, uA, v} f t' m = bcTmul.{uR, uA, v} f (t * t') m :=
  rfl

/-- A scalar `s : S` moves across a pure tensor: `t ⊗ (s • m) = (f s * t) ⊗ m`. -/
theorem bcTmul_smul_right (t : T) (s : S) (m : M) :
    bcTmul.{uR, uA, v} f t (s • m) = bcTmul.{uR, uA, v} f (f s * t) m := by
  have key : ∀ (t' : (ModuleCat.restrictScalars.{uA, uR, uA} f).obj (ModuleCat.of T T))
      (x : M), (t' ⊗ₜ[S] (s • x) : TensorProduct S _ _) = (s • t') ⊗ₜ[S] x :=
    fun t' x => TensorProduct.tmul_smul s t' x
  exact key t m

/-- A pure tensor `t ⊗ m` equals `t • (1 ⊗ m)`. -/
theorem bcTmul_eq_smul (t : T) (m : M) :
    bcTmul.{uR, uA, v} f t m = t • bcTmul.{uR, uA, v} f 1 m := by
  rw [bcTmul_smul, mul_one]

/-- The base change of a linear map `g : M ⟶ N` carries `t ⊗ m` to `t ⊗ g m`. -/
theorem extendScalars_map_bcTmul {N : ModuleCat.{v} S} (g : M ⟶ N) (t : T) (m : M) :
    ((ModuleCat.extendScalars.{uR, uA, v} f).map g).hom (bcTmul.{uR, uA, v} f t m) =
      bcTmul.{uR, uA, v} f t (g.hom m) :=
  rfl

end BcTmul

/-- A pure tensor of a degree of the termwise base change of a complex, typed as an element of
that degree. -/
def bcTmulC {S : Type uR} {T : Type uA} [CommRing S] [CommRing T] (f : S →+* T)
    (X : CochainComplex (ModuleCat.{v} S) ℤ) (i : ℤ) (t : T) (m : X.X i) :
    (((ModuleCat.extendScalars.{uR, uA, v} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X).X i :=
  bcTmul.{uR, uA, v} f t m

/-- The termwise base change of a chain map `φ` carries `t ⊗ m` in degree `i` to `t ⊗ φ.f i m`. -/
theorem mapHomologicalComplex_map_f_bcTmulC {S : Type uR} {T : Type uA} [CommRing S] [CommRing T]
    (f : S →+* T) {X Y : CochainComplex (ModuleCat.{v} S) ℤ} (φ : X ⟶ Y) (i : ℤ) (t : T)
    (m : X.X i) :
    ((((ModuleCat.extendScalars.{uR, uA, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        φ).f i).hom (bcTmulC.{uR, uA, v} f X i t m) =
      bcTmulC.{uR, uA, v} f Y i t ((φ.f i).hom m) :=
  rfl

variable {R₀ : Type uR} {A₀ : Type uA} {B₀ : Type uRp} [CommRing R₀] [CommRing A₀] [CommRing B₀]

/-- The composition isomorphism of extensions of scalars on a pure tensor:
`x ⊗ m ↦ x ⊗ (1 ⊗ m)`. -/
theorem extendScalarsComp_hom_app_bcTmul (f : R₀ →+* A₀) (g : A₀ →+* B₀)
    (M : ModuleCat.{max v uR uA uRp} R₀) (x : B₀) (m : M) :
    ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{uR, uA, uRp, v} f g).hom.app
        M).hom (bcTmul.{uR, uRp, max v uR uA uRp} (g.comp f) x m) =
      bcTmul.{uA, uRp, max v uR uA uRp} g x (bcTmul.{uR, uA, max v uR uA uRp} f 1 m) := by
  have h₁ := ConcreteCategory.congr_hom
    (StacksDraft.DerivedExtensionScalarsModelComp.unit_extendScalarsComp.{uR, uA, uRp, v} f g M) m
  have h₂ : ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{uR, uA, uRp, v}
      f g).hom.app M).hom (bcTmul.{uR, uRp, max v uR uA uRp} (g.comp f) 1 m) =
      bcTmul.{uA, uRp, max v uR uA uRp} g 1 (bcTmul.{uR, uA, max v uR uA uRp} f 1 m) := h₁
  rw [bcTmul_eq_smul, _root_.map_smul, h₂, bcTmul_smul, mul_one]

/-- The inverse of the composition isomorphism on a pure tensor: `x ⊗ (a ⊗ m) ↦ x g(a) ⊗ m`. -/
theorem extendScalarsComp_inv_app_bcTmul (f : R₀ →+* A₀) (g : A₀ →+* B₀)
    (M : ModuleCat.{max v uR uA uRp} R₀) (x : B₀) (a : A₀) (m : M) :
    ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{uR, uA, uRp, v} f g).inv.app
        M).hom (bcTmul.{uA, uRp, max v uR uA uRp} g x (bcTmul.{uR, uA, max v uR uA uRp} f a m)) =
      bcTmul.{uR, uRp, max v uR uA uRp} (g.comp f) (x * g a) m := by
  have h : ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{uR, uA, uRp, v}
      f g).hom.app M).hom (bcTmul.{uR, uRp, max v uR uA uRp} (g.comp f) (x * g a) m) =
      bcTmul.{uA, uRp, max v uR uA uRp} g x (bcTmul.{uR, uA, max v uR uA uRp} f a m) := by
    rw [extendScalarsComp_hom_app_bcTmul, bcTmul_eq_smul f a, bcTmul_smul_right, mul_comm]
  rw [← h]
  exact ConcreteCategory.congr_hom
    (((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{uR, uA, uRp, v}
      f g).app M).hom_inv_id) _

/-- `RingTheory.TorIndependence.extendScalarsCompInvOfEq` on a pure tensor. -/
theorem extendScalarsCompInvOfEq_app_bcTmul (f : R₀ →+* A₀) (h : A₀ →+* B₀) (hc : R₀ →+* B₀)
    (hfh : h.comp f = hc) (M : ModuleCat.{max v uR uA uRp} R₀) (x : B₀) (a : A₀) (m : M) :
    ((RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, uRp, v} f h hc hfh).app
        M).hom (bcTmul.{uA, uRp, max v uR uA uRp} h x (bcTmul.{uR, uA, max v uR uA uRp} f a m)) =
      bcTmul.{uR, uRp, max v uR uA uRp} hc (x * h a) m := by
  subst hfh
  simp only [RingTheory.TorIndependence.extendScalarsCompInvOfEq, eqToHom_refl,
    Category.comp_id]
  exact extendScalarsComp_inv_app_bcTmul f h M x a m

/-- The inverse of `Dualizing.extendScalarsCompIsoOfEq` on a pure tensor: `y ⊗ m ↦ y ⊗ (1 ⊗ m)`. -/
theorem extendScalarsCompIsoOfEq_inv_app_bcTmul (f : R₀ →+* A₀) (h : A₀ →+* B₀) (hc : R₀ →+* B₀)
    (hfh : h.comp f = hc) (M : ModuleCat.{max v uR uA uRp} R₀) (y : B₀) (m : M) :
    ((extendScalarsCompIsoOfEq.{uR, uA, uRp, v} f h hc hfh).inv.app M).hom
        (bcTmul.{uR, uRp, max v uR uA uRp} hc y m) =
      bcTmul.{uA, uRp, max v uR uA uRp} h y (bcTmul.{uR, uA, max v uR uA uRp} f 1 m) := by
  subst hfh
  simp only [extendScalarsCompIsoOfEq, Iso.trans_inv, eqToIso_refl, Iso.refl_inv,
    Iso.symm_inv, Category.id_comp]
  exact extendScalarsComp_hom_app_bcTmul f h M y m

end ExtendScalarsComp


section ChainProjection

variable {S : Type uR} {T : Type uA} [CommRing S] [CommRing T] (φ : S →+* T)
  (K : CochainComplex (ModuleCat.{max v uR uA} S) ℤ)

/-- The degree-`n` component of the chain-level projection formula
`Dualizing.extendRestrictComplexIso`: the flip `t ⊗ m ↦ m ⊗ t`, then the inclusion of the summand
of bidegree `(n, 0)`. -/
theorem extendRestrictComplexIso_hom_f (n : ℤ) :
    haveI := moduleTensor_flip_obj_additive.{max v uR uA, uR} (algebraModule.{v} φ)
    (extendRestrictComplexIso.{v} φ K).hom.f n =
      (extendRestrictFlipIso.{v} φ).hom.app (K.X n) ≫
        ((moduleTensor.{uR, max v uR uA} S).obj (K.X n)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (algebraModule.{v} φ)).inv ≫
        HomologicalComplex.singleRightι (moduleTensor.{uR, max v uR uA} S) K
          (algebraModule.{v} φ) n :=
  rfl

/-- `Dualizing.extendRestrictComplexIso` on a pure tensor. -/
theorem extendRestrictComplexIso_hom_f_tmul (n : ℤ) (t : T) (m : K.X n) :
    haveI := moduleTensor_flip_obj_additive.{max v uR uA, uR} (algebraModule.{v} φ)
    letI := φ.toModule
    ((extendRestrictComplexIso.{v} φ K).hom.f n).hom (t ⊗ₜ[S] m) =
      (HomologicalComplex.singleRightι (moduleTensor.{uR, max v uR uA} S) K
          (algebraModule.{v} φ) n).hom
        (m ⊗ₜ[S] (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (algebraModule.{v} φ)).inv.hom (ULift.up t : ULift.{max v uR uA} T)) := by
  rw [extendRestrictComplexIso_hom_f]
  rfl

/-- The inverse of `Dualizing.extendRestrictComplexIso` on the summand of bidegree `(n, 0)`. -/
theorem extendRestrictComplexIso_inv_f_singleRightι (n : ℤ) (m : K.X n)
    (x : ((algebraComplex.{v} φ).X 0 : Type _)) :
    haveI := moduleTensor_flip_obj_additive.{max v uR uA, uR} (algebraModule.{v} φ)
    letI := φ.toModule
    ((extendRestrictComplexIso.{v} φ K).inv.f n).hom
        ((HomologicalComplex.singleRightι (moduleTensor.{uR, max v uR uA} S) K
          (algebraModule.{v} φ) n).hom (m ⊗ₜ[S] x)) =
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (algebraModule.{v} φ)).hom.hom x).down : T) ⊗ₜ[S] m := by
  have := moduleTensor_flip_obj_additive.{max v uR uA, uR} (algebraModule.{v} φ)
  let := φ.toModule
  have hy : ((extendRestrictComplexIso.{v} φ K).hom.f n).hom
        ((((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (algebraModule.{v} φ)).hom.hom x).down : T) ⊗ₜ[S] m) =
      (HomologicalComplex.singleRightι (moduleTensor.{uR, max v uR uA} S)
        K (algebraModule.{v} φ) n).hom (m ⊗ₜ[S] x) := by
    rw [extendRestrictComplexIso_hom_f_tmul]
    congr 2
  rw [← hy]
  have h := HomologicalComplex.congr_hom (extendRestrictComplexIso.{v} φ K).hom_inv_id n
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h
  exact ConcreteCategory.congr_hom h _

/-- `Dualizing.extendRestrictComplexIso_inv_f_singleRightι`, with the pure tensor written with
`Dualizing.bcTmul`. -/
theorem extendRestrictComplexIso_inv_f_singleRightι_bcTmul (n : ℤ) (m : K.X n)
    (x : ((algebraComplex.{v} φ).X 0 : Type _)) :
    haveI := moduleTensor_flip_obj_additive.{max v uR uA, uR} (algebraModule.{v} φ)
    ((extendRestrictComplexIso.{v} φ K).inv.f n).hom
        ((HomologicalComplex.singleRightι (moduleTensor.{uR, max v uR uA} S) K
          (algebraModule.{v} φ) n).hom (m ⊗ₜ[S] x)) =
      bcTmul.{uR, uA, max v uR uA} φ (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (algebraModule.{v} φ)).hom.hom x).down : T) m :=
  extendRestrictComplexIso_inv_f_singleRightι φ K n m x

/-- `Dualizing.extendRestrictComplexIso_hom_f_tmul`, with the pure tensor written with
`Dualizing.bcTmul`. -/
theorem extendRestrictComplexIso_hom_f_bcTmul (n : ℤ) (t : T) (m : K.X n) :
    haveI := moduleTensor_flip_obj_additive.{max v uR uA, uR} (algebraModule.{v} φ)
    ((extendRestrictComplexIso.{v} φ K).hom.f n).hom (bcTmul.{uR, uA, max v uR uA} φ t m) =
      (HomologicalComplex.singleRightι (moduleTensor.{uR, max v uR uA} S) K
          (algebraModule.{v} φ) n).hom
        (m ⊗ₜ[S] (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (algebraModule.{v} φ)).inv.hom (ULift.up t : ULift.{max v uR uA} T)) :=
  extendRestrictComplexIso_hom_f_tmul φ K n t m

end ChainProjection

/-- Two maps out of `(T ⊗ M) ⊗_T (T ⊗ N)` agree as soon as they agree on `(1 ⊗ m) ⊗ (1 ⊗ n)`. -/
theorem extendScalars_tensor_hom_ext {S : Type uR} {T : Type uRp} [CommRing S] [CommRing T]
    (f : S →+* T) {M N : ModuleCat.{max v uR uA uRp} S}
    {Z : ModuleCat.{max v uR uA uRp} T}
    (α β : ((moduleTensor.{uRp, max v uR uA} T).obj
        ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj M)).obj
        ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj N) ⟶ Z)
    (h : ∀ (m : M) (x : N), α.hom (bcTmul.{uR, uRp, max v uR uA uRp} f 1 m ⊗ₜ[T]
        bcTmul.{uR, uRp, max v uR uA uRp} f 1 x) =
      β.hom (bcTmul.{uR, uRp, max v uR uA uRp} f 1 m ⊗ₜ[T]
        bcTmul.{uR, uRp, max v uR uA uRp} f 1 x)) :
    α = β := by
  have h₁ : ∀ (m : M) (y' : (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj N),
      α (((1 : T) ⊗ₜ[S, f] m) ⊗ₜ[T] y') = β (((1 : T) ⊗ₜ[S, f] m) ⊗ₜ[T] y') := by
    intro m y'
    have := ModuleCat.ExtendScalars.hom_ext
      (α := ModuleCat.ofHom (X := (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj N)
        (Y := Z) (α.hom ∘ₗ TensorProduct.mk T
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj M)
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj N) ((1 : T) ⊗ₜ[S, f] m)))
      (β := ModuleCat.ofHom (X := (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj N)
        (Y := Z) (β.hom ∘ₗ TensorProduct.mk T
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj M)
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj N) ((1 : T) ⊗ₜ[S, f] m)))
      (fun x => h m x)
    exact congrArg (fun φ => φ.hom y') this
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro y y'
  have := ModuleCat.ExtendScalars.hom_ext
    (α := ModuleCat.ofHom (X := (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj M)
      (Y := Z) (α.hom ∘ₗ (TensorProduct.mk T
        ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj M)
        ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj N)).flip y'))
    (β := ModuleCat.ofHom (X := (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj M)
      (Y := Z) (β.hom ∘ₗ (TensorProduct.mk T
        ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj M)
        ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).obj N)).flip y'))
    (fun m => h₁ m y')
  exact congrArg (fun φ => φ.hom y) this

/-- `Dualizing.extendScalars_tensor_hom_ext` for the degrees of two termwise base changes. -/
theorem extendScalars_tensor_hom_ext_complex {S : Type uR} {T : Type uRp} [CommRing S]
    [CommRing T] (f : S →+* T) (X Y : CochainComplex (ModuleCat.{max v uR uA uRp} S) ℤ) (a b : ℤ)
    {Z : ModuleCat.{max v uR uA uRp} T}
    (α β : ((moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} T).obj
        ((((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X).X a)).obj
        ((((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Y).X b) ⟶ Z)
    (h : ∀ (m : X.X a) (x : Y.X b),
      α.hom (bcTmulC.{uR, uRp, max v uR uA uRp} f X a 1 m ⊗ₜ[T]
        bcTmulC.{uR, uRp, max v uR uA uRp} f Y b 1 x) =
      β.hom (bcTmulC.{uR, uRp, max v uR uA uRp} f X a 1 m ⊗ₜ[T]
        bcTmulC.{uR, uRp, max v uR uA uRp} f Y b 1 x)) :
    α = β :=
  extendScalars_tensor_hom_ext.{uR, uA, uRp, v} f α β h

/-- `Dualizing.algebraBaseChangeChain` in degree zero, on `1 ⊗ x`: it carries the class of
`a ∈ A` to the class of `a ⊗ 1 ∈ A ⊗_R R'`. -/
theorem algebraBaseChangeChain_f_zero_bcTmul
    (x : ((algebraComplex.{max v uRp} (algebraMap R A)).X 0 : Type _)) :
    ((algebraBaseChangeChain.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
        comparisonA).f 0).hom (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 x) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R' (TensorProduct R A R'))).obj
          (ModuleCat.of (TensorProduct R A R')
            (ULift.{max v uR uA uRp} (TensorProduct R A R'))))).inv.hom
        (ULift.up (algebraMap A (TensorProduct R A R')
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (algebraModule.{max v uRp} (algebraMap R A))).hom.hom x).down)) := by
  have := ModuleCat.instIsLeftAdjointExtendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')
  have := ModuleCat.instIsLeftAdjointExtendScalars.{uA, max uA uRp, max v uR uA uRp}
    (algebraMap A (TensorProduct R A R'))
  let X : ModuleCat.{max v uR uA uRp} A := ModuleCat.of A (ULift.{max v uR uA uRp} A)
  let M := ((HomologicalComplex.single (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ) 0).obj
    X).X 0
  let τ := (RingTheory.TorIndependence.derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v}
    (algebraMap R A) (algebraMap R R')
    (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
    ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
      (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
    baseChangeR baseChangeA comparisonR comparisonA).1
  let Φ₁ := ((((ModuleCat.restrictScalars.{max v uR uA uRp}
    (algebraMap R A)).mapCochainComplexSingleFunctor 0).inv.app X).f 0)
  let T₃ := (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R' (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
            (algebraMap A (TensorProduct R A R'))) (ComplexShape.up ℤ) 0).app X).hom ≫
        (HomologicalComplex.single (ModuleCat.{max v uR uA uRp} (TensorProduct R A R'))
          (ComplexShape.up ℤ) 0).map
          (extendScalarsULiftUnitIso.{uA, max uA uRp, max v uR uRp}
            (algebraMap A (TensorProduct R A R'))).hom)).f 0 ≫
    (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R' (TensorProduct R A R'))).mapCochainComplexSingleFunctor 0).hom.app
      (ModuleCat.of (TensorProduct R A R') (ULift.{max v uR uA uRp} (TensorProduct R A R')))).f 0
  have hchain : (algebraBaseChangeChain.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
      comparisonA).f 0 =
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).map Φ₁ ≫
        τ.app M ≫ T₃ := rfl
  have hτ : (τ.app M).hom (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 (Φ₁.hom x)) =
      bcTmul.{uA, max uA uRp, max v uR uA uRp} (algebraMap A (TensorProduct R A R')) 1
        (Φ₁.hom x) := by
    refine (RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_tmul.{uR, uA, uRp,
      max uA uRp, v} _ _ _ _ _ _ _ _ _ M 1 (Φ₁.hom x)).trans ?_
    rw [map_one]
    rfl
  have hT₃ : T₃.hom (bcTmul.{uA, max uA uRp, max v uR uA uRp} (algebraMap A (TensorProduct R A R'))
      1 (Φ₁.hom x)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R' (TensorProduct R A R'))).obj
          (ModuleCat.of (TensorProduct R A R')
            (ULift.{max v uR uA uRp} (TensorProduct R A R'))))).inv.hom
        (ULift.up (algebraMap A (TensorProduct R A R')
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (algebraModule.{max v uRp} (algebraMap R A))).hom.hom x).down * 1)) :=
    rfl
  rw [hchain, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    extendScalars_map_bcTmul, hτ, hT₃, mul_one]

/-- The map of total tensor complexes induced by two chain maps, on a pure tensor of a summand. -/
theorem mapBifunctorMap_f_ι_tmul.{u₁, w₁} {S : Type u₁} [CommRing S]
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat.{max u₁ w₁} S) ℤ} (f₁ : K₁ ⟶ K₂) (f₂ : L₁ ⟶ L₂)
    (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
    (x : K₁.X a) (y : L₁.X b) :
    ((HomologicalComplex.mapBifunctorMap f₁ f₂ (moduleTensor.{u₁, w₁} S)
        (ComplexShape.up ℤ)).f n).hom
      ((HomologicalComplex.ιMapBifunctor K₁ L₁ (moduleTensor.{u₁, w₁} S)
        (ComplexShape.up ℤ) a b n hab).hom (x ⊗ₜ[S] y)) =
      (HomologicalComplex.ιMapBifunctor K₂ L₂ (moduleTensor.{u₁, w₁} S)
        (ComplexShape.up ℤ) a b n hab).hom ((f₁.f a).hom x ⊗ₜ[S] (f₂.f b).hom y) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.ι_mapBifunctorMap f₁ f₂ (moduleTensor.{u₁, w₁} S)
      (ComplexShape.up ℤ) a b n hab) (x ⊗ₜ[S] y)
  exact h

/-- The comparison of [stacks 0661] on complexes, typed with the two composites of
`mapHomologicalComplex` written out. -/
def chainBaseChangeComparison (X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ) :
    ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X) ⟶
    ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
  (NatTrans.mapHomologicalComplex
    (RingTheory.TorIndependence.derivedBaseChangeComparison
      (algebraMap R A) (algebraMap R R')
      (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
      ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
        (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
      baseChangeR baseChangeA comparisonR comparisonA).1
    (ComplexShape.up ℤ)).app X

/-- The two composition isomorphisms of extensions of scalars on complexes, typed with the
composites of `mapHomologicalComplex` written out. -/
def chainExtendScalarsSwap (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    ((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
    ((ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  (NatTrans.mapHomologicalComplex
      (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
        (algebraMap R A)
        (algebraMap A (TensorProduct R A R')) (algebraMap R (TensorProduct R A R'))
        algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K ≫
    ((NatIso.mapHomologicalComplex
      (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom
        (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
      (ComplexShape.up ℤ)).app K).inv

/-- A composite of six morphisms of modules on an element, computed one step at a time. -/
theorem ModuleCat_hom_comp₆_eq {T : Type*} [Ring T] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : ModuleCat T}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄} {f₄ : X₄ ⟶ X₅} {f₅ : X₅ ⟶ X₆}
    {y : X₀} {w₂ : X₂} {w₃ : X₃} {w₄ : X₄} {w₅ : X₅} {w₆ : X₆}
    (h₂ : f₁.hom (f₀.hom y) = w₂) (h₃ : f₂.hom w₂ = w₃) (h₄ : f₃.hom w₃ = w₄)
    (h₅ : f₄.hom w₄ = w₅) (h₆ : f₅.hom w₅ = w₆) :
    (f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅).hom y = w₆ := by
  subst h₂ h₃ h₄ h₅ h₆
  rfl

/-- A composite of two morphisms of modules on an element, computed one step at a time. -/
theorem ModuleCat_hom_comp₂_eq {T : Type*} [Ring T] {X₀ X₁ X₂ : ModuleCat T}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {y : X₀} {w₁ : X₁} {w₂ : X₂}
    (h₁ : f₀.hom y = w₁) (h₂ : f₁.hom w₁ = w₂) :
    (f₀ ≫ f₁).hom y = w₂ := by
  subst h₁ h₂
  rfl

/-- A composite of six morphisms of modules on an element. -/
theorem ModuleCat_hom_comp₆ {T : Type*} [Ring T] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : ModuleCat T}
    (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅) (f₅ : X₅ ⟶ X₆)
    (y : X₀) :
    (f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅).hom y =
      f₅.hom (f₄.hom (f₃.hom (f₂.hom (f₁.hom (f₀.hom y))))) :=
  rfl

/-- A composite of two morphisms of modules on an element. -/
theorem ModuleCat_hom_comp₂ {T : Type*} [Ring T] {X₀ X₁ X₂ : ModuleCat T}
    (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (y : X₀) :
    (f₀ ≫ f₁).hom y = f₁.hom (f₀.hom y) :=
  rfl

omit [QuasiIso p] in
/-- The first piece of the chain identity on a pure tensor of the summand of bidegree `(a, 0)`. -/
theorem chainIdentity_piece₁ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) :
    ((((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) ≫
          (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv)).f a).hom
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
          (HomologicalComplex.mapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
            (ComplexShape.up ℤ)) a 1
          ((HomologicalComplex.ιMapBifunctor K P (moduleTensor.{uR, max (max v uRp) uR uA} R)
            (ComplexShape.up ℤ) a 0 a hab).hom (k ⊗ₜ[R] z))) =
      bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a 1
        (bcTmul.{uR, uA, max v uR uA uRp} (algebraMap R A)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down k) := by
    rw [mapHomologicalComplex_map_f_bcTmulC, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, mapBifunctorMap_f_ι_tmul, HomologicalComplex.id_f, ModuleCat.id_apply]
    rw [show HomologicalComplex.ιMapBifunctor K (algebraComplex.{max v uRp} (algebraMap R A))
        (moduleTensor.{uR, max (max v uRp) uR uA} R) (ComplexShape.up ℤ) a 0 a hab =
      HomologicalComplex.singleRightι (moduleTensor.{uR, max (max v uRp) uR uA} R) K
        (algebraModule.{max v uRp} (algebraMap R A)) a from rfl,
      extendRestrictComplexIso_inv_f_singleRightι_bcTmul]

/-- Restriction of scalars does not change a map of complexes on elements. -/
theorem restrictScalars_mapHomologicalComplex_map_f_apply {S : Type uR} {T : Type uA}
    [Ring S] [Ring T] (φ : S →+* T) {X Y : CochainComplex (ModuleCat.{v} T) ℤ}
    (f : X ⟶ Y) (i : ℤ) (x : X.X i) :
    ((((ModuleCat.restrictScalars.{v} φ).mapHomologicalComplex (ComplexShape.up ℤ)).map f).f
        i).hom x = (f.f i).hom x :=
  rfl

/-- The second piece of the chain identity: the comparison of [stacks 0661] on `1 ⊗ m`. -/
theorem chainIdentity_piece₂ (X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ) (a : ℤ)
    (m : X.X a) :
    ((chainBaseChangeComparison.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
        comparisonA X).f a).hom
      (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R')
        (((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) a 1 m) =
      bcTmulC.{uA, max uA uRp, max v uR uA uRp} (algebraMap A (TensorProduct R A R')) X a 1 m := by
  have := ModuleCat.instIsLeftAdjointExtendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')
  have := ModuleCat.instIsLeftAdjointExtendScalars.{uA, max uA uRp, max v uR uA uRp}
    (algebraMap A (TensorProduct R A R'))
  refine (RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_tmul.{uR, uA, uRp,
    max uA uRp, v} (algebraMap R A) (algebraMap R R')
      (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
      ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
        (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
      baseChangeR baseChangeA comparisonR comparisonA (X.X a) 1 m).trans ?_
  rw [map_one]
  rfl

/-- The fourth piece of the chain identity: the chain-level projection formula over `R'`. -/
theorem chainIdentity_piece₄ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (t : TensorProduct R A R') (k : K.X a) :
    ((extendRestrictComplexIso.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom.f a).hom
      (bcTmulC.{uRp, max uA uRp, max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a t
        (bcTmul.{uR, uRp, max v uR uA uRp} (algebraMap R R') 1 k)) =
      (HomologicalComplex.singleRightι
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (algebraModule.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom) a).hom
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k ⊗ₜ[R']
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (algebraModule.{max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)).inv.hom
            (ULift.up t : ULift.{max v uR uA uRp} (TensorProduct R A R'))) :=
  extendRestrictComplexIso_hom_f_bcTmul _ _ a t _

omit [QuasiIso p] in
/-- The right side of the chain identity on a pure tensor of the summand of bidegree `(a, 0)`. -/
theorem chainIdentity_rhs (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) (a : ℤ)
    (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, 0) = a)
    (k : K.X a) (z : P.X 0) :
    (HomologicalComplex.ιMapBifunctor
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ) a 0 a hab ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 _)
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
            P p)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ)).f a).hom
        ((bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k) ⊗ₜ[R']
          (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') P 0 1 z)) =
      (HomologicalComplex.singleRightι
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (algebraModule.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom) a).hom
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k ⊗ₜ[R']
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (algebraModule.{max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)).inv.hom
            (ULift.up (algebraMap A (TensorProduct R A R')
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (algebraModule.{max v uRp} (algebraMap R A))).hom.hom ((p.f 0).hom z)).down) :
              ULift.{max v uR uA uRp} (TensorProduct R A R'))) := by
  have hCH := algebraBaseChangeChain_f_zero_bcTmul baseChangeR comparisonR baseChangeA
    comparisonA ((p.f 0).hom z)
  refine ModuleCat_hom_comp₂_eq rfl
    ((mapBifunctorMap_f_ι_tmul.{uRp, max (max v uR) uRp (max uA uRp)} _ _ a 0 a hab _ _).trans ?_)
  exact congrArg (fun w => (HomologicalComplex.singleRightι
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R')
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (algebraModule.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom) a).hom
        (bcTmulC.{uR, uRp, max v uR uA uRp} (algebraMap R R') K a 1 k ⊗ₜ[R'] w)) hCH

end Dualizing
