module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistFunctorAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# The twist of a Galois descent sheaf

Let `C` be a Galois covering of `X` with group `H` and let `𝒫 = D(N)` be the descent sheaf of an
`R`-module `N` with an `H`-action, `R = ℤ/ℓᴹ[G]`.  This file shows that `𝒫` is acyclic for the
twist functor `Ψ = Hom_R(E^∨, -)` as soon as `N` is coinduced from a flat `ℤ/ℓᴹ`-module, for
instance `N = R`.

## Main results

* `Stacks.EtaleCohomology.isLocallyConstant_evalₗ_comp`: a linear map out of a finite module
  into locally constant maps is locally constant pointwise.
* `Stacks.EtaleCohomology.locallyConstantCoinductionEquiv`: locally constant maps into a
  coinduced module are the coinduction of locally constant maps.
* `Stacks.EtaleCohomology.rightAcyclic_twistFunctor_descentSheaf`: the descent sheaf of a module
  coinduced from a flat `ℤ/ℓᴹ`-module is acyclic for the twist functor.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.ZModPrimePower

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Locally constant maps and `Hom` out of a finite module -/

/-- **A linear map from a finite module into locally constant maps is pointwise locally
constant**: the map `w ↦ (d ↦ φ(d)(w))` is locally constant. -/
theorem isLocallyConstant_evalₗ_comp {A : Type*} [Ring A] {D M W : Type*} [AddCommGroup D]
    [Module A D] [Module.Finite A D] [AddCommGroup M] [Module A M] [TopologicalSpace W]
    (φ : D →ₗ[A] LocallyConstant W M) :
    IsLocallyConstant fun w : W => (LocallyConstant.evalₗ A w) ∘ₗ φ := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := D)
  have h : ∀ᶠ y in nhds x, ∀ d ∈ s, φ d y = φ d x :=
    (Filter.eventually_all_finset s).2 fun d _ =>
      (IsLocallyConstant.iff_eventually_eq _).1 (φ d).isLocallyConstant x
  filter_upwards [h] with y hy
  exact LinearMap.ext_on hs fun d hd => hy d hd

/-! ### Locally constant maps into a coinduced module -/

section Coinduction

variable (k₀ : Type) [CommRing k₀] (G : Type) [Group G] [Fintype G]

omit [Fintype G] in
/-- `k₀[G]` is a finite `k₀`-module through `k₀ → k₀[G]`. -/
instance [Finite G] : Module.Finite k₀ (GroupRingRes k₀ G) :=
  Module.Finite.equiv
    ({ toFun := toGroupRingRes
       invFun := ofGroupRingRes
       map_add' := fun _ _ => rfl
       map_smul' := fun c a => by
         rw [RingHom.id_apply, ← toGroupRingRes_single_one_mul]
         congr 1
         ext m
         simp
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : MonoidAlgebra k₀ G ≃ₗ[k₀] GroupRingRes k₀ G)

/-- The coinduction of locally constant maps, evaluated at a point. -/
def coinductionEvalPoint {W : Type u} [TopologicalSpace W] (N₀ : ModuleCat.{u + 1} k₀)
    (φ : (groupRingCoinduction k₀ G).obj (ModuleCat.of k₀ (LocallyConstant W N₀))) (w : W) :
    (groupRingCoinduction k₀ G).obj N₀ :=
  (ModuleCat.CoextendScalars.equiv _ N₀).symm
    ((LocallyConstant.evalₗ k₀ w) ∘ₗ ModuleCat.CoextendScalars.equiv _ _ φ)

/-- **Locally constant maps into a coinduced module are the coinduction of locally constant
maps**: `LC(W, Hom_{k₀}(k₀[G], N₀)) ≅ Hom_{k₀}(k₀[G], LC(W, N₀))`. -/
def locallyConstantCoinductionEquiv (W : Type u) [TopologicalSpace W]
    (N₀ : ModuleCat.{u + 1} k₀) :
    LocallyConstant W ((groupRingCoinduction k₀ G).obj N₀) ≃ₗ[MonoidAlgebra k₀ G]
      (groupRingCoinduction k₀ G).obj (ModuleCat.of k₀ (LocallyConstant W N₀)) where
  toFun f := (ModuleCat.CoextendScalars.equiv _ _).symm
    { toFun := fun a => f.map fun ψ => coindEval ψ (ofGroupRingRes a)
      map_add' := fun a b => LocallyConstant.ext fun w => by
        change coindEval (f w) (ofGroupRingRes (a + b)) =
          coindEval (f w) (ofGroupRingRes a) + coindEval (f w) (ofGroupRingRes b)
        exact map_add (ModuleCat.CoextendScalars.equiv _ N₀ (f w)) a b
      map_smul' := fun c a => LocallyConstant.ext fun w =>
        (ModuleCat.CoextendScalars.equiv _ N₀ (f w)).map_smul c a }
  invFun φ := ⟨coinductionEvalPoint k₀ G N₀ φ,
    ((isLocallyConstant_evalₗ_comp (ModuleCat.CoextendScalars.equiv _ _ φ)).comp
      (ModuleCat.CoextendScalars.equiv _ N₀).symm)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The sheaf of locally constant maps into a coinduced module is the coinduced sheaf of
locally constant maps.** -/
def locallyConstantMapsCoinductionIso (X : Scheme.{u}) (N₀ : ModuleCat.{u + 1} k₀) :
    smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} (MonoidAlgebra k₀ G) X
        ((groupRingCoinduction k₀ G).obj N₀) ≅
      (etaleModuleCoinduction k₀ G X).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} k₀ X N₀) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun T => (locallyConstantCoinductionEquiv k₀ G T.unop.left N₀).toModuleIso)
      (fun _ => rfl))

end Coinduction

/-! ### Restriction to an étale object and the slice -/

section Restriction

variable {Λ : Type} [Ring Λ] {X : Scheme.{u}}

/-- An étale scheme over `U.left`, as an object of the slice of the small étale site of `X` over
`U`. -/
def smallEtaleToSlice (U : X.Etale) [Etale U.hom] : U.left.Etale ⥤ Over U where
  obj V := Over.mk (MorphismProperty.Over.homMk V.hom rfl trivial :
    (Scheme.Etale.smallEtaleCompose U.hom).obj V ⟶ U)
  map g := Over.homMk ((Scheme.Etale.smallEtaleCompose U.hom).map g) (by
    apply MorphismProperty.Over.Hom.ext
    exact MorphismProperty.Over.w g)

/-- **Restriction to `U` only depends on the restriction to the slice over `U`**: an isomorphism
of the restrictions of two sheaves to the slice over `U` gives one of their restrictions along
`U ⟶ X`. -/
def etaleModuleRestrictionIsoOfOverPullbackIso (U : X.Etale) [Etale U.hom]
    {F F' : EtaleModules.{u, 0} Λ X}
    (e : (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) U).obj F ≅
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) U).obj F') :
    (etaleModuleRestriction.{u, 0} Λ U.hom).obj F ≅
      (etaleModuleRestriction.{u, 0} Λ U.hom).obj F' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun V => ((sheafToPresheaf _ _).mapIso e).app (op ((smallEtaleToSlice U).obj V.unop)))
      (fun g => ((sheafToPresheaf _ _).mapIso e).hom.naturality
        ((smallEtaleToSlice U).map g.unop).op))

end Restriction

/-! ### Flatness of locally constant maps -/

/-- **Locally constant maps into a flat `ℤ/ℓᴹ`-module form a flat sheaf.** -/
theorem powExact_locallyConstantMaps {ℓ M : ℕ} [Fact ℓ.Prime] (X : Scheme.{u})
    (N₀ : ModuleCat.{u + 1} (ZMod (ℓ ^ M))) (h : IsPowExact ℓ M N₀) :
    PowExact ℓ M (smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} (ZMod (ℓ ^ M)) X N₀) := by
  classical
  refine powExact_of_exact (etaleModules_pow_nsmul_id _) (fun a ha => ?_)
  refine shortComplex_exact_of_sections _ (fun U x hx => ?_)
  let s : N₀ → N₀ := fun c => if hc : ℓ ^ a • c = 0 then Classical.choose (h a ha c hc) else 0
  let x' : LocallyConstant U.unop.left N₀ := x
  have hx' : ℓ ^ a • x' = 0 := hx
  refine ⟨(x'.map s : LocallyConstant U.unop.left N₀), ?_⟩
  show ℓ ^ (M - a) • x'.map s = x'
  refine LocallyConstant.ext fun t => ?_
  have hxt : ℓ ^ a • x' t = 0 := congrArg (fun f : LocallyConstant _ N₀ => f t) hx'
  show ℓ ^ (M - a) • s (x' t) = x' t
  rw [show s (x' t) = Classical.choose (h a ha (x' t) hxt) from dif_pos hxt]
  exact Classical.choose_spec (h a ha (x' t) hxt)

/-! ### The group ring is coinduced -/

section GroupRing

variable (k₀ : Type) [CommRing k₀] (G : Type) [Group G] [Fintype G]

/-- `k₀[G] ⟶ Hom_{k₀}(k₀[G], k₀)`, `a ↦ a • δ₁`. -/
def groupRingToCoinduction :
    ULift.{u + 1} (MonoidAlgebra k₀ G) →ₗ[MonoidAlgebra k₀ G]
      (groupRingCoinduction k₀ G).obj (ModuleCat.of k₀ (ULift.{u + 1} k₀)) where
  toFun x := x.down • groupRingCoinductionDelta (ModuleCat.of k₀ (ULift.{u + 1} k₀)) (ULift.up 1)
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := mul_smul _ _ _

omit [Fintype G] in
/-- The map `groupRingToCoinduction`, `a ↦ a • δ₁`, is bijective. -/
theorem bijective_groupRingToCoinduction [Finite G] :
    Function.Bijective (groupRingToCoinduction.{u} k₀ G) := by
  classical
  have := Fintype.ofFinite G
  refine ⟨fun x y hxy => ULift.ext _ _ (MonoidAlgebra.ext (Finsupp.ext fun g => ?_)), fun f => ?_⟩
  · have h := congrArg (fun φ : (groupRingCoinduction k₀ G).obj
      (ModuleCat.of k₀ (ULift.{u + 1} k₀)) =>
        (show ULift.{u + 1} k₀ from coindEval φ (MonoidAlgebra.single g⁻¹ 1)).down) hxy
    simpa [groupRingToCoinduction, coindEval_smul, coindEval_delta,
      MonoidAlgebra.coeff_single_mul_apply] using h
  · refine ⟨ULift.up (∑ g : G, MonoidAlgebra.single g (1 : k₀) *
      MonoidAlgebra.single (1 : G) (coindEval f (MonoidAlgebra.single g⁻¹ 1)).down), ?_⟩
    conv_rhs => rw [groupRingCoinduction_eq_sum_smul_delta _ f]
    simp only [groupRingToCoinduction, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_smul,
      mul_smul]
    refine Finset.sum_congr rfl fun g _ => congrArg _ ?_
    rw [← groupRingCoinductionDelta_smul]
    congr 1
    exact ULift.ext _ _ (mul_one _)

/-- **`k₀[G]` is coinduced from `k₀`**: `k₀[G] ≅ Hom_{k₀}(k₀[G], k₀)` as `k₀[G]`-modules. -/
def groupRingCoinductionEquiv :
    ULift.{u + 1} (MonoidAlgebra k₀ G) ≃ₗ[MonoidAlgebra k₀ G]
      (groupRingCoinduction k₀ G).obj (ModuleCat.of k₀ (ULift.{u + 1} k₀)) :=
  LinearEquiv.ofBijective _ (bijective_groupRingToCoinduction k₀ G)

end GroupRing

/-! ### Acyclicity of the descent sheaf for the twist functor -/

section Twist

variable (ℓ M : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [Fintype G] (Λ : Type) [CommRing Λ]
  [Algebra (ZMod (ℓ ^ M)) Λ] (E : Type (u + 1)) [AddCommGroup E] [Module Λ E]
  [Module (ZMod (ℓ ^ M)) E] [IsScalarTower (ZMod (ℓ ^ M)) Λ E] (ρ : Representation Λ G E)
  [Finite E] {X : Scheme.{u}} {H : Type*} [Group H] (C : EtaleGaloisCovering X H)

/-- Locally constant maps into isomorphic modules. -/
def locallyConstantCongrRight {R : Type*} [Ring R] {W N N' : Type*} [TopologicalSpace W]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (e : N ≃ₗ[R] N') :
    LocallyConstant W N ≃ₗ[R] LocallyConstant W N' where
  toFun f := f.map e
  invFun f := f.map e.symm
  map_add' _ _ := LocallyConstant.ext fun _ => map_add e _ _
  map_smul' _ _ := LocallyConstant.ext fun _ => map_smul e _ _
  left_inv _ := LocallyConstant.ext fun _ => e.symm_apply_apply _
  right_inv _ := LocallyConstant.ext fun _ => e.apply_symm_apply _

omit [Fintype G] in
/-- **A descent sheaf of a coinduced module is acyclic for the twist functor**: if `N` is
coinduced from a flat `ℤ/ℓᴹ`-module `N₀`, the descent sheaf of `N` is acyclic for `Ψ`. -/
theorem rightAcyclic_twistFunctor_descentSheaf [Finite G] (N : Type (u + 1)) [AddCommGroup N]
    [Module (MonoidAlgebra (ZMod (ℓ ^ M)) G) N]
    (ρ' : H →* Module.End (MonoidAlgebra (ZMod (ℓ ^ M)) G) N)
    (N₀ : ModuleCat.{u + 1} (ZMod (ℓ ^ M))) (hN₀ : IsPowExact ℓ M N₀)
    (eN : N ≃ₗ[MonoidAlgebra (ZMod (ℓ ^ M)) G] (groupRingCoinduction (ZMod (ℓ ^ M)) G).obj N₀) :
    (sheafCompose X.smallEtaleTopology (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ)).rightAcyclic
      (EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C (MonoidAlgebra (ZMod (ℓ ^ M)) G) N ρ') := by
  have := Fintype.ofFinite G
  have : Etale C.cover.hom := C.cover.prop
  let R := MonoidAlgebra (ZMod (ℓ ^ M)) G
  let J := smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} (ZMod (ℓ ^ M)) X N₀
  let eL : smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} R X (ModuleCat.of R N) ≅
      (etaleModuleCoinduction (ZMod (ℓ ^ M)) G X).obj J :=
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (fun T => (locallyConstantCongrRight (W := T.unop.left) eN).toModuleIso)
        (fun _ => rfl)) :
        smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} R X (ModuleCat.of R N) ≅
          smallEtaleLocallyConstantMapsModuleSheaf.{u, 0} R X
            ((groupRingCoinduction (ZMod (ℓ ^ M)) G).obj N₀)) ≪≫
      locallyConstantMapsCoinductionIso (ZMod (ℓ ^ M)) G X N₀
  let e : (etaleModuleInverseImage.{u, 0} R C.cover.hom).obj
        (EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C R N ρ') ≅
      (etaleModuleInverseImage.{u, 0} R C.cover.hom).obj
        ((etaleModuleCoinduction (ZMod (ℓ ^ M)) G X).obj J) :=
    (etaleModuleInverseImageRestrictionIso.{u, 0} R C.cover.hom).app _ ≪≫
      etaleModuleRestrictionIsoOfOverPullbackIso C.cover
        (EtaleGaloisCovering.restrictIso.{u, 0, _, 0} C R N ρ' ≪≫
          (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) C.cover).mapIso eL) ≪≫
      ((etaleModuleInverseImageRestrictionIso.{u, 0} R C.cover.hom).app _).symm
  refine rightAcyclic_twistFunctor_of_inverseImage ℓ M G Λ E ρ C.cover.hom _ ?_
  exact Stacks.RightAcyclicProduct.rightAcyclic_of_iso _ e.symm
    (rightAcyclic_twistFunctor_inverseImage ℓ M G Λ E ρ C.cover.hom _
      (rightAcyclic_twistFunctor_coinduction ℓ M G Λ E ρ J
        (powExact_locallyConstantMaps X N₀ hN₀)))

omit [Fintype G] in
/-- **The descent sheaf `𝒫 = D(k₀[G])` is acyclic for the twist functor**, for any action on the
group ring. -/
theorem rightAcyclic_twistFunctor_descentSheaf_groupRing [Finite G]
    (ρ' : H →* Module.End (MonoidAlgebra (ZMod (ℓ ^ M)) G)
      (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G))) :
    (sheafCompose X.smallEtaleTopology (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ)).rightAcyclic
      (EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C (MonoidAlgebra (ZMod (ℓ ^ M)) G)
        (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G)) ρ') :=
  have := Fintype.ofFinite G
  rightAcyclic_twistFunctor_descentSheaf ℓ M G Λ E ρ C _ ρ' _
    (IsPowExact.of_addEquiv AddEquiv.ulift.symm (isPowExact_of_baer baer_self))
    (groupRingCoinductionEquiv (ZMod (ℓ ^ M)) G)

/-- The terms of a complex concentrated in degree `0` are acyclic as soon as its degree `0` term
is. -/
theorem rightAcyclic_singleFunctor_obj_X {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {A : C} (hA : F.rightAcyclic A) (n : ℤ) :
    F.rightAcyclic (((CochainComplex.singleFunctor C 0).obj A).X n) := by
  by_cases hn : n = 0
  · subst hn
    exact Stacks.RightAcyclicProduct.rightAcyclic_of_iso F
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).symm hA
  · exact Stacks.RightAcyclicProduct.rightAcyclic_of_isZero F
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

omit [Fintype G] in
/-- **`𝒫 = D(k₀[G])` placed in degree `0` is termwise acyclic for the twist functor.** -/
theorem rightAcyclic_twistFunctor_single_descentSheaf_groupRing [Finite G]
    (ρ' : H →* Module.End (MonoidAlgebra (ZMod (ℓ ^ M)) G)
      (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G))) (n : ℤ) :
    (sheafCompose X.smallEtaleTopology (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ)).rightAcyclic
      (((CochainComplex.singleFunctor _ 0).obj
        (EtaleGaloisCovering.descentSheaf.{u, 0, _, 0} C (MonoidAlgebra (ZMod (ℓ ^ M)) G)
          (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G)) ρ')).X n) :=
  rightAcyclic_singleFunctor_obj_X _
    (rightAcyclic_twistFunctor_descentSheaf_groupRing ℓ M G Λ E ρ C ρ') n

end Twist

end Stacks.EtaleCohomology

end
