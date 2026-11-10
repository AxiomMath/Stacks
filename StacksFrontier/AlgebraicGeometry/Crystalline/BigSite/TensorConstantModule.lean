module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.AffineBaseChangeCriterion
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.AffineModuleComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CrystalValues
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionCohomologyULift
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation

/-!
# The tensor product of a quasi-coherent module on `CRIS(X/S)` with a module over the base

Fix a global crystalline situation `(p, (S, I, γ), X)` and write `A = Γ(S, 𝒪_S)`.  Every object
`(U, T, δ)` of the big crystalline site `CRIS(X/S)` comes with the structure map
`A ⟶ Γ(T, 𝒪_T)` of its divided power morphism `T ⟶ S`, so the sections `N(T)` of a sheaf of
`𝒪_{X/S}`-modules `N` are `A`-modules.  For an `A`-module `M` this file constructs the sheaf of
`𝒪_{X/S}`-modules `N ⊗_A M`, for `N` quasi-coherent, whose sections over every object with affine
ambient scheme are `N(T) ⊗_A M`.

## The construction

The presheaf `T ↦ N(T) ⊗_A M` (`TensorConstant.tensorPresheaf`) is in general not a sheaf: over an
object whose ambient scheme is not quasi-compact a tensor product does not commute with the
infinite products of the sheaf condition.  It is a sheaf on the objects with affine ambient
scheme: there, for a morphism `T' ⟶ T`, the base change of sections
`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} (N(T) ⊗_A M) ⟶ N(T') ⊗_A M` is the base change of sections of `N`
tensored with `M` (`TensorConstant.bijective_liftBaseChange_rTensorOver`), and that of `N` is
bijective because `N` is quasi-coherent ([Stacks, Tag 07IT], read on values in
`...bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite`);
a presheaf of modules on `CRIS_aff(X/S)` with bijective base change maps is a sheaf
(`Crystalline.GlobalCrystallineSituation.BigAffine.isSheaf_of_bijective_baseChange`, Zariski
descent for modules).  The objects with affine ambient scheme form a dense subsite of
`CRIS(X/S)`, so restriction is an equivalence of categories of sheaves of modules
(`Crystalline.GlobalCrystallineSituation.BigAffine.moduleEquivalence`, at the universe of the
sections of `𝒪_{X/S}`), and `N ⊗_A M` is the sheaf corresponding to `T ↦ N(T) ⊗_A M`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.tensorConstantModule N M` — **the sheaf `N ⊗_A M`**.
* `Crystalline.GlobalCrystallineSituation.tensorConstantModuleSectionsEquiv` — **its sections over
  an object with affine ambient scheme are `N(T) ⊗_A M`**, as `Γ(T, 𝒪_T)`-modules, and
  `tensorConstantModuleBaseSectionsIso`, the same as an isomorphism of `A`-modules with the tensor
  product `N(T) ⊗ M` of the monoidal category of `A`-modules.
* `Crystalline.GlobalCrystallineSituation.tensorConstantModuleBaseSectionsNatIso` — the same
  identification as a natural isomorphism of presheaves of `A`-modules on `CRIS_aff(X/S)`.
* `Crystalline.GlobalCrystallineSituation.tensorConstantModuleMap` and
  `Crystalline.GlobalCrystallineSituation.tensorConstantFunctor` — functoriality in `N` and `M`.

## Main results

* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_tensorConstantModule` —
  **`N ⊗_A M` is quasi-coherent**: its base change of sections between objects with affine
  ambient schemes is bijective, which characterises quasi-coherence on `CRIS(X/S)`
  (`...isQuasicoherentOnSite_of_bijective_extensionSectionsMapAlong`).
  So is its universe lift to the module universe `u + 1`
  (`isQuasicoherentOnSite_bigModuleULift_tensorConstantModule`).
* `tensorConstantModuleSectionsEquiv_restrict` — the identification of the sections is natural
  for morphisms between objects with affine ambient schemes.
* `tensorConstantModuleAffineSectionsEquiv_map` — it is natural in `N` and `M`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 00EK](https://stacks.math.columbia.edu/tag/00EK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.TensorConstant

/-- Additive maps out of a tensor product which agree on pure tensors are equal. -/
private theorem coe_eq_of_tmul {R P Q Z F G : Type*} [CommSemiring R] [AddCommMonoid P]
    [AddCommMonoid Q] [AddCommMonoid Z] [Module R P] [Module R Q] [FunLike F (P ⊗[R] Q) Z]
    [FunLike G (P ⊗[R] Q) Z] [AddMonoidHomClass F (P ⊗[R] Q) Z] [AddMonoidHomClass G (P ⊗[R] Q) Z]
    (f : F) (g : G) (h : ∀ (x : P) (y : Q), f (x ⊗ₜ y) = g (x ⊗ₜ y)) : ⇑f = ⇑g := by
  funext z
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-! ### Base change commutes with tensoring by a module over a third ring -/

section Algebra

variable {A R T : Type*} [CommRing A] [CommRing R] [CommRing T] [Algebra R T]
  {X Y M : Type*} [AddCommGroup X] [Module R X] [Module A X] [SMulCommClass A R X]
  [AddCommGroup Y] [Module T Y] [Module R Y] [IsScalarTower R T Y] [Module A Y]
  [SMulCommClass A T Y] [SMulCommClass A R Y] [AddCommGroup M] [Module A M]
  (f : X →ₗ[R] Y) (hf : ∀ (a : A) (x : X), f (a • x) = a • f x)

/-- An `R`-linear map which is also `A`-linear, as an `A`-linear map. -/
def linearMapOver : X →ₗ[A] Y where
  toFun := f
  map_add' := map_add f
  map_smul' a x := hf a x

/-- **The map `f ⊗ id_M : X ⊗_A M ⟶ Y ⊗_A M`**, linear over `R` acting on the left factors. -/
def rTensorOver (M : Type*) [AddCommGroup M] [Module A M] : X ⊗[A] M →ₗ[R] Y ⊗[A] M where
  toFun := TensorProduct.map (linearMapOver f hf) LinearMap.id
  map_add' := map_add _
  map_smul' r z := by
    induction z using TensorProduct.inductionOn with
    | tmul x m =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        RingHom.id_apply, TensorProduct.smul_tmul']
      exact congrArg (· ⊗ₜ[A] LinearMap.id m) (f.map_smul r x)
    | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

/-- `rTensorOver` on a pure tensor. -/
@[simp]
theorem rTensorOver_tmul (x : X) (m : M) :
    rTensorOver f hf M (x ⊗ₜ m) = f x ⊗ₜ m :=
  rfl

/-- The map `x ↦ x ⊗ m`, linear over `R`. -/
def tmulRight (m : M) : X →ₗ[R] X ⊗[A] M where
  toFun x := x ⊗ₜ m
  map_add' x y := TensorProduct.add_tmul x y m
  map_smul' r x := (TensorProduct.smul_tmul' r x m).symm

include hf in
/-- **Base change commutes with tensoring by a module over a third ring.**  If `f : X ⟶ Y`
identifies `Y` with the base change `T ⊗_R X`, then `f ⊗ id_M` identifies `Y ⊗_A M` with
`T ⊗_R (X ⊗_A M)`, for any `A`-module `M`, `A` acting on `X` and `Y` compatibly with `f`. -/
theorem bijective_liftBaseChange_rTensorOver (h : Function.Bijective (f.liftBaseChange T)) :
    Function.Bijective ((rTensorOver f hf M).liftBaseChange T) := by
  let e : T ⊗[R] X ≃ₗ[T] Y := LinearEquiv.ofBijective (f.liftBaseChange T) h
  have he : ∀ (t : T) (x : X), e (t ⊗ₜ x) = t • f x := fun t x ↦ rfl
  let aX : A → X →ₗ[R] X := fun a ↦
    { toFun x := a • x
      map_add' x y := smul_add a x y
      map_smul' r x := smul_comm a r x }
  have heA : ∀ (a : A) (z : T ⊗[R] X), e (LinearMap.lTensor T (aX a) z) = a • e z := by
    intro a z
    induction z using TensorProduct.inductionOn with
    | tmul t x =>
      rw [LinearMap.lTensor_tmul, he, he]
      change t • f (a • x) = a • t • f x
      rw [hf]
      exact (smul_comm a t (f x)).symm
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, smul_add]
  have hsymm : ∀ (a : A) (y : Y), e.symm (a • y) = LinearMap.lTensor T (aX a) (e.symm y) := by
    intro a y
    apply e.injective
    rw [heA, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let β : Y →+ M →+ T ⊗[R] (X ⊗[A] M) :=
    AddMonoidHom.mk'
      (fun y ↦ AddMonoidHom.mk' (fun m ↦ LinearMap.lTensor T (tmulRight m) (e.symm y))
        fun m m' ↦ by
          have : (tmulRight (A := A) (R := R) (X := X) (m + m')) =
              tmulRight m + tmulRight m' := by
            ext x
            exact TensorProduct.tmul_add x m m'
          rw [this, LinearMap.lTensor_add, LinearMap.add_apply])
      fun y y' ↦ by
        ext m
        simp only [map_add, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
  have hβ : ∀ (a : A) (y : Y) (m : M), β (a • y) m = β y (a • m) := by
    intro a y m
    change LinearMap.lTensor T (tmulRight m) (e.symm (a • y)) =
      LinearMap.lTensor T (tmulRight (a • m)) (e.symm y)
    rw [hsymm, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    congr 2
    ext x
    exact TensorProduct.smul_tmul a x m
  let ψ : Y ⊗[A] M →+ T ⊗[R] (X ⊗[A] M) := TensorProduct.liftAddHom β hβ
  let L := (rTensorOver f hf M).liftBaseChange T
  have hLl : ∀ (m : M) (z : T ⊗[R] X), L (LinearMap.lTensor T (tmulRight m) z) = e z ⊗ₜ m := by
    intro m z
    induction z using TensorProduct.inductionOn with
    | tmul t x =>
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, he]
      rfl
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, TensorProduct.add_tmul]
  have h₁ : ∀ w, L (ψ w) = w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul y m =>
      change L (LinearMap.lTensor T (tmulRight m) (e.symm y)) = y ⊗ₜ m
      rw [hLl, LinearEquiv.apply_symm_apply]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  have h₂ : ∀ z, ψ (L z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul t w =>
      induction w using TensorProduct.inductionOn with
      | tmul x m =>
        rw [LinearMap.liftBaseChange_tmul, rTensorOver_tmul, TensorProduct.smul_tmul']
        change LinearMap.lTensor T (tmulRight m) (e.symm (t • f x)) = t ⊗ₜ (x ⊗ₜ m)
        rw [← he, LinearEquiv.symm_apply_apply, LinearMap.lTensor_tmul]
        rfl
      | add w w' hw hw' => rw [TensorProduct.tmul_add, map_add, map_add, hw, hw']
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  exact ⟨Function.LeftInverse.injective (g := ψ) h₂, Function.RightInverse.surjective
    (g := ψ) h₁⟩

end Algebra

/-! ### The presheaf `T ↦ N(T) ⊗_A M` -/

variable {S : GlobalCrystallineSituation.{u}}

/-- The ring `A = Γ(S, 𝒪_S)` of global sections of the divided power base. -/
abbrev BaseRing (S : GlobalCrystallineSituation.{u}) : Type u := Γ(S.S.scheme, ⊤)

/-- **The structure map `A ⟶ Γ(T, 𝒪_T)`** of an object `(U, T, δ)` of `CRIS(X/S)`: the map on
global sections of its divided power morphism `T ⟶ S`. -/
def baseMap (T : Thickening S) : BaseRing S →+* crysSheafRing S T :=
  T.toBase.hom.appTop.hom

/-- The structure maps are compatible with the restriction maps of `𝒪_{X/S}`. -/
theorem crysSheafRingMap_baseMap {T T' : Thickening S} (g : T' ⟶ T) (a : BaseRing S) :
    crysSheafRingMap g (baseMap T a) = baseMap T' a := by
  have h := congrArg (fun φ : T'.thickening.target ⟶ S.S ↦ φ.hom.appTop.hom a) g.base_naturality
  simp only [DividedPowerScheme.Hom.comp_hom, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply] at h
  exact h

variable (N : PresheafOfModules.{u} (crystallineStructureSheaf S).obj)
  (M : ModuleCat.{u} (BaseRing S))

/-- **The sections of a presheaf of `𝒪_{X/S}`-modules over an object `T`, as a module over
`A = Γ(S, 𝒪_S)`** through the structure map `A ⟶ Γ(T, 𝒪_T)`.  A synonym of `N(T)`, so that the
`A`-module structure, which depends on `T`, can be an instance. -/
def BaseSections (T : Thickening S) : Type u := N.obj (op T)

/-- The additive group of `BaseSections N T`, that of `N(T)`. -/
instance (T : Thickening S) : AddCommGroup (BaseSections N T) :=
  inferInstanceAs (AddCommGroup (N.obj (op T)))

/-- `N(T)` as a module over `Γ(T, 𝒪_T)`, its own module structure. -/
instance (T : Thickening S) : Module (crysSheafRing S T) (BaseSections N T) :=
  inferInstanceAs (Module (crysSheafRing S T) (N.obj (op T)))

/-- `N(T)` as an `A`-module through the structure map `A ⟶ Γ(T, 𝒪_T)`. -/
instance (T : Thickening S) : Module (BaseRing S) (BaseSections N T) :=
  Module.compHom (N.obj (op T)) (baseMap T)

/-- The action of `A` on `N(T)` is that of its image in `Γ(T, 𝒪_T)`. -/
theorem baseRing_smul_def (T : Thickening S) (a : BaseRing S) (x : BaseSections N T) :
    a • x = (baseMap T a • (x : N.obj (op T)) : N.obj (op T)) := rfl

/-- The actions of `A` and of `Γ(T, 𝒪_T)` on `N(T)` commute. -/
instance (T : Thickening S) :
    SMulCommClass (BaseRing S) (crysSheafRing S T) (BaseSections N T) where
  smul_comm a b x := by
    let y : N.obj (op T) := x
    change baseMap T a • b • y = b • baseMap T a • y
    rw [smul_smul, smul_smul, mul_comm]

/-- The actions of `Γ(T, 𝒪_T)` and of `A` on `N(T)` commute. -/
instance (T : Thickening S) :
    SMulCommClass (crysSheafRing S T) (BaseRing S) (BaseSections N T) :=
  SMulCommClass.symm _ _ _

/-- **The sections `N(T) ⊗_A M`** of the tensor product of `N` with the `A`-module `M`, a module
over `Γ(T, 𝒪_T)` through the left factor. -/
abbrev TensorSections (T : Thickening S) : Type u := BaseSections N T ⊗[BaseRing S] M

/-- The restriction map `N(T) ⟶ N(T')` along `g : T' ⟶ T`, as an `A`-linear map. -/
def restrictBase {T T' : Thickening S} (g : T' ⟶ T) :
    BaseSections N T →ₗ[BaseRing S] BaseSections N T' where
  toFun x := N.restrictₛₗ g.op x
  map_add' x y := map_add (N.restrictₛₗ g.op) x y
  map_smul' a x := by
    let y : N.obj (op T) := x
    change N.restrictₛₗ g.op (baseMap T a • y) = baseMap T' a • N.restrictₛₗ g.op y
    rw [map_smulₛₗ]
    exact congrArg (· • N.restrictₛₗ g.op x) (crysSheafRingMap_baseMap g a)

/-- `restrictBase` is the restriction map of `N`. -/
@[simp]
theorem restrictBase_apply {T T' : Thickening S} (g : T' ⟶ T) (x : BaseSections N T) :
    restrictBase N g x = N.restrictₛₗ g.op x := rfl

/-- The restriction map `N(T) ⊗_A M ⟶ N(T') ⊗_A M` along `g : T' ⟶ T`. -/
def tensorRestrict {T T' : Thickening S} (g : T' ⟶ T) :
    TensorSections N M T →ₗ[BaseRing S] TensorSections N M T' :=
  TensorProduct.map (restrictBase N g) LinearMap.id

/-- `tensorRestrict` on a pure tensor. -/
@[simp]
theorem tensorRestrict_tmul {T T' : Thickening S} (g : T' ⟶ T) (x : BaseSections N T)
    (m : M) : tensorRestrict N M g (x ⊗ₜ m) = restrictBase N g x ⊗ₜ m := rfl

/-- `tensorRestrict` is semilinear over the restriction map of `𝒪_{X/S}`. -/
theorem tensorRestrict_smul {T T' : Thickening S} (g : T' ⟶ T) (b : crysSheafRing S T)
    (z : TensorSections N M T) :
    tensorRestrict N M g (b • z) = crysSheafRingMap g b • tensorRestrict N M g z := by
  induction z using TensorProduct.inductionOn with
  | tmul x m =>
    rw [TensorProduct.smul_tmul', tensorRestrict_tmul, tensorRestrict_tmul,
      TensorProduct.smul_tmul']
    congr 1
    exact map_smulₛₗ (N.restrictₛₗ g.op) b x
  | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

/-- **The presheaf of `𝒪_{X/S}`-modules `T ↦ N(T) ⊗_A M` on `CRIS(X/S)`.** -/
def tensorPresheaf : PresheafOfModules.{u} (crystallineStructureSheaf S).obj where
  obj T := ModuleCat.of (crysSheafRing S T.unop) (TensorSections N M T.unop)
  map {T T'} g := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((crystallineStructureSheaf S).obj.map g).hom).obj
      (ModuleCat.of (crysSheafRing S T'.unop) (TensorSections N M T'.unop)))
    { toFun := tensorRestrict N M g.unop
      map_add' := map_add _
      map_smul' := tensorRestrict_smul N M g.unop }
  map_id T := by
    ext z
    change tensorRestrict N M (𝟙 T.unop) z = z
    induction z using TensorProduct.inductionOn with
    | tmul x m =>
      rw [tensorRestrict_tmul]
      exact congrArg (· ⊗ₜ[BaseRing S] m) (PresheafOfModules.restrictₛₗ_id_apply N T x)
    | add z z' hz hz' => rw [map_add, hz, hz']
  map_comp {T T' T''} g g' := by
    ext z
    change tensorRestrict N M (g ≫ g').unop z =
      tensorRestrict N M g'.unop (tensorRestrict N M g.unop z)
    induction z using TensorProduct.inductionOn with
    | tmul x m =>
      rw [tensorRestrict_tmul, tensorRestrict_tmul, tensorRestrict_tmul]
      exact congrArg (· ⊗ₜ[BaseRing S] m) (PresheafOfModules.restrictₛₗ_comp_apply N g g' x)
    | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- The restriction maps of `tensorPresheaf N M` are the maps `tensorRestrict N M`. -/
theorem tensorPresheaf_restrictₛₗ {T T' : Thickening S} (g : T' ⟶ T)
    (z : TensorSections N M T) :
    (tensorPresheaf N M).restrictₛₗ g.op z = tensorRestrict N M g z := rfl

section Functoriality

variable {N} {N' N'' : PresheafOfModules.{u} (crystallineStructureSheaf S).obj}
  {M} {M' M'' : ModuleCat.{u} (BaseRing S)}

/-- The map `N(T) ⟶ N'(T)` of a morphism of presheaves of modules, as an `A`-linear map. -/
def baseSectionsMap (φ : N ⟶ N') (T : Thickening S) :
    BaseSections N T →ₗ[BaseRing S] BaseSections N' T where
  toFun x := (φ.app (op T)).hom x
  map_add' x y := map_add (φ.app (op T)).hom x y
  map_smul' a x := (φ.app (op T)).hom.map_smul (baseMap T a) x

/-- `baseSectionsMap` is the component of the morphism. -/
@[simp]
theorem baseSectionsMap_apply (φ : N ⟶ N') (T : Thickening S) (x : BaseSections N T) :
    baseSectionsMap φ T x = (φ.app (op T)).hom x := rfl

/-- The map `N(T) ⊗_A M ⟶ N'(T) ⊗_A M'` of morphisms `N ⟶ N'` and `M ⟶ M'`. -/
def tensorSectionsMap (φ : N ⟶ N') (ψ : M ⟶ M') (T : Thickening S) :
    TensorSections N M T →ₗ[crysSheafRing S T] TensorSections N' M' T where
  toFun := TensorProduct.map (baseSectionsMap φ T) ψ.hom
  map_add' := map_add _
  map_smul' b z := by
    induction z using TensorProduct.inductionOn with
    | tmul x m =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        RingHom.id_apply, TensorProduct.smul_tmul']
      exact congrArg (· ⊗ₜ[BaseRing S] ψ.hom m) ((φ.app (op T)).hom.map_smul b x)
    | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

/-- `tensorSectionsMap` on a pure tensor. -/
@[simp]
theorem tensorSectionsMap_tmul (φ : N ⟶ N') (ψ : M ⟶ M') (T : Thickening S)
    (x : BaseSections N T) (m : M) :
    tensorSectionsMap φ ψ T (x ⊗ₜ m) = baseSectionsMap φ T x ⊗ₜ ψ.hom m := rfl

/-- **The morphism `N ⊗_A M ⟶ N' ⊗_A M'` of presheaves** induced by `N ⟶ N'` and `M ⟶ M'`. -/
def tensorPresheafMap (φ : N ⟶ N') (ψ : M ⟶ M') : tensorPresheaf N M ⟶ tensorPresheaf N' M' where
  app T := ModuleCat.ofHom (tensorSectionsMap φ ψ T.unop)
  naturality {T T'} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    change tensorSectionsMap φ ψ T'.unop (tensorRestrict N M g.unop z) =
      tensorRestrict N' M' g.unop (tensorSectionsMap φ ψ T.unop z)
    induction z using TensorProduct.inductionOn with
    | tmul x m =>
      rw [tensorRestrict_tmul, tensorSectionsMap_tmul, tensorSectionsMap_tmul,
        tensorRestrict_tmul]
      exact congrArg (· ⊗ₜ[BaseRing S] ψ.hom m)
        (PresheafOfModules.restrictₛₗ_naturality_apply φ g x)
    | add z z' hz hz' => rw [map_add, map_add, map_add, map_add, hz, hz']

/-- The components of `tensorPresheafMap` are the maps `tensorSectionsMap`. -/
@[simp]
theorem tensorPresheafMap_app_apply (φ : N ⟶ N') (ψ : M ⟶ M') (T : (Thickening S)ᵒᵖ)
    (z : TensorSections N M T.unop) :
    (tensorPresheafMap φ ψ).app T z = tensorSectionsMap φ ψ T.unop z := rfl

/-- `tensorPresheafMap` preserves identities. -/
theorem tensorPresheafMap_id : tensorPresheafMap (𝟙 N) (𝟙 M) = 𝟙 (tensorPresheaf N M) := by
  ext T z
  exact congrFun (coe_eq_of_tmul (tensorSectionsMap (𝟙 N) (𝟙 M) T.unop) (AddMonoidHom.id _)
    fun _ _ ↦ rfl) z

/-- `tensorPresheafMap` preserves composition. -/
theorem tensorPresheafMap_comp (φ : N ⟶ N') (φ' : N' ⟶ N'') (ψ : M ⟶ M') (ψ' : M' ⟶ M'') :
    tensorPresheafMap (φ ≫ φ') (ψ ≫ ψ') = tensorPresheafMap φ ψ ≫ tensorPresheafMap φ' ψ' := by
  ext T z
  exact congrFun (coe_eq_of_tmul (tensorSectionsMap (φ ≫ φ') (ψ ≫ ψ') T.unop)
    (tensorSectionsMap φ' ψ' T.unop ∘ₗ tensorSectionsMap φ ψ T.unop) fun _ _ ↦ rfl) z

end Functoriality

/-! ### The sections as `A`-modules -/

/-- **The `A`-module of sections `T ↦ N(T)`** of a presheaf of `𝒪_{X/S}`-modules, through the
structure maps `A ⟶ Γ(T, 𝒪_T)`, as a presheaf of `A`-modules on `CRIS(X/S)`. -/
def baseSectionsFunctor : (Thickening S)ᵒᵖ ⥤ ModuleCat.{u} (BaseRing S) where
  obj T := ModuleCat.of (BaseRing S) (BaseSections N T.unop)
  map g := ModuleCat.ofHom (restrictBase N g.unop)
  map_id T := by
    ext x
    exact PresheafOfModules.restrictₛₗ_id_apply N T x
  map_comp g g' := by
    ext x
    exact PresheafOfModules.restrictₛₗ_comp_apply N g g' x

/-- The `Γ(T, 𝒪_T)`-module structure of `N(T) ⊗_A M` restricts along `A ⟶ Γ(T, 𝒪_T)` to its
`A`-module structure. -/
theorem baseMap_smul_tensorSections (T : Thickening S) (a : BaseRing S)
    (z : TensorSections N M T) : baseMap T a • z = a • z := by
  induction z using TensorProduct.inductionOn with
  | tmul x m => rfl
  | add z z' hz hz' => rw [smul_add, smul_add, hz, hz']

/-! ### The restriction to `CRIS_aff(X/S)` and its base change maps -/

/-- **The presheaf `T ↦ N(T) ⊗_A M` restricted to `CRIS_aff(X/S)`.** -/
abbrev affineTensorPresheaf : PresheafOfModules.{u} (BigAffine.structureSheaf S).obj :=
  (PresheafOfModules.pushforward₀ (bigAffineι S) (crystallineStructureSheaf S).obj).obj
    (tensorPresheaf N M)

/-- **The base change of sections of `T ↦ N(T) ⊗_A M` between objects with affine ambient
schemes is bijective, for a quasi-coherent `N`.**  It is the base change of sections of `N`,
bijective by [Stacks, Tag 07IT] read on values
(`bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite`),
tensored over `A` with `M`, and base change commutes with that tensor product,
`bijective_liftBaseChange_rTensorOver`. -/
theorem bijective_baseChange_affineTensorPresheaf
    (N₀ : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N₀.IsQuasicoherentOnSite)
    {A B : BigAffineThickening S} (k : A ⟶ B) :
    Function.Bijective (BigAffine.baseChange (affineTensorPresheaf N₀.val M) k) := by
  let iRX : Module (BigAffine.SectionRing B) (BaseSections N₀.val B.obj) :=
    inferInstanceAs (Module (crysSheafRing S B.obj) (BaseSections N₀.val B.obj))
  have : SMulCommClass (BaseRing S) (BigAffine.SectionRing B) (BaseSections N₀.val B.obj) :=
    inferInstanceAs
      (SMulCommClass (BaseRing S) (crysSheafRing S B.obj) (BaseSections N₀.val B.obj))
  let iTY : Module (BigAffine.RingAlong k) (BaseSections N₀.val A.obj) :=
    inferInstanceAs (Module (crysSheafRing S A.obj) (BaseSections N₀.val A.obj))
  let iRY : Module (BigAffine.SectionRing B) (BaseSections N₀.val A.obj) :=
    Module.compHom (BaseSections N₀.val A.obj) (crysSheafRingMap k.hom)
  have : IsScalarTower (BigAffine.SectionRing B) (BigAffine.RingAlong k)
      (BaseSections N₀.val A.obj) :=
    ⟨fun b t y ↦ mul_smul (crysSheafRingMap k.hom b)
      (@id (crysSheafRing S A.obj) t) (@id (N₀.val.obj (op A.obj)) y)⟩
  have : SMulCommClass (BaseRing S) (BigAffine.RingAlong k) (BaseSections N₀.val A.obj) :=
    inferInstanceAs
      (SMulCommClass (BaseRing S) (crysSheafRing S A.obj) (BaseSections N₀.val A.obj))
  have : SMulCommClass (BaseRing S) (BigAffine.SectionRing B) (BaseSections N₀.val A.obj) :=
    ⟨fun a b y ↦ by
      change baseMap A.obj a • crysSheafRingMap k.hom b • (@id (N₀.val.obj (op A.obj)) y) =
        crysSheafRingMap k.hom b • baseMap A.obj a • (@id (N₀.val.obj (op A.obj)) y)
      rw [smul_smul, smul_smul, mul_comm]⟩
  let f : BaseSections N₀.val B.obj →ₗ[BigAffine.SectionRing B] BaseSections N₀.val A.obj :=
    { toFun := fun x ↦ N₀.val.restrictₛₗ k.hom.op x
      map_add' := fun x y ↦ map_add (N₀.val.restrictₛₗ k.hom.op) x y
      map_smul' := fun b x ↦ (map_smulₛₗ (N₀.val.restrictₛₗ k.hom.op) b x).trans rfl }
  have hf : ∀ (a : BaseRing S) (x : BaseSections N₀.val B.obj), f (a • x) = a • f x :=
    fun a x ↦ (restrictBase N₀.val k.hom).map_smul a x
  have h0 : Function.Bijective (f.liftBaseChange (BigAffine.RingAlong k)) := by
    exact (congrArg Function.Bijective (coe_eq_of_tmul (f.liftBaseChange (BigAffine.RingAlong k))
      (extensionSectionsMapAlong N₀ k.hom) fun _ _ ↦ rfl)).mpr
        (bijective_extensionSectionsMapAlong_of_isQuasicoherentOnSite N₀ k.hom hN)
  have hfun := coe_eq_of_tmul ((rTensorOver f hf M).liftBaseChange (BigAffine.RingAlong k))
    (BigAffine.baseChange (affineTensorPresheaf N₀.val M) k) fun _ _ ↦ rfl
  exact hfun ▸ bijective_liftBaseChange_rTensorOver (M := M) f hf h0

/-- **The sheaf `T ↦ N(T) ⊗_A M` on `CRIS_aff(X/S)`**, for a quasi-coherent `N`: its base change
maps are bijective, `bijective_baseChange_affineTensorPresheaf`, so it is a sheaf. -/
def affineTensorSheaf (N₀ : SheafOfModules.{u} (crystallineStructureSheaf S))
    [hN : N₀.IsQuasicoherentOnSite] : SheafOfModules.{u} (BigAffine.structureSheaf S) :=
  BigAffine.sheafOfBijectiveBaseChange (affineTensorPresheaf N₀.val M)
    (bijective_baseChange_affineTensorPresheaf M N₀ hN)

variable {M} in
/-- The morphism of sheaves on `CRIS_aff(X/S)` induced by morphisms `N ⟶ N'` and `M ⟶ M'`. -/
def affineTensorSheafMap {N₀ N₀' : SheafOfModules.{u} (crystallineStructureSheaf S)}
    [N₀.IsQuasicoherentOnSite] [N₀'.IsQuasicoherentOnSite] {M' : ModuleCat.{u} (BaseRing S)}
    (φ : N₀ ⟶ N₀') (ψ : M ⟶ M') : affineTensorSheaf M N₀ ⟶ affineTensorSheaf M' N₀' :=
  ⟨(PresheafOfModules.pushforward₀ (bigAffineι S) (crystallineStructureSheaf S).obj).map
    (tensorPresheafMap φ.val ψ)⟩

end Crystalline.GlobalCrystallineSituation.TensorConstant

namespace Crystalline.GlobalCrystallineSituation

open TensorConstant

variable {S : GlobalCrystallineSituation.{u}}

/-- **The tensor product `N ⊗_A M` of a quasi-coherent sheaf of `𝒪_{X/S}`-modules `N` on
`CRIS(X/S)` with a module `M` over `A = Γ(S, 𝒪_S)`.**  It is the sheaf of modules whose
restriction to the objects with affine ambient scheme is the presheaf `T ↦ N(T) ⊗_A M`, which is
already a sheaf there (`TensorConstant.affineTensorSheaf`); the objects with affine ambient
scheme form a dense subsite, so this determines a sheaf on `CRIS(X/S)`
(`BigAffine.moduleEquivalence`). -/
def tensorConstantModule (N : SheafOfModules.{u} (crystallineStructureSheaf S))
    [N.IsQuasicoherentOnSite] (M : ModuleCat.{u} (BaseRing S)) :
    SheafOfModules.{u} (crystallineStructureSheaf S) :=
  (BigAffine.moduleEquivalence S).inverse.obj (affineTensorSheaf M N)

variable (N : SheafOfModules.{u} (crystallineStructureSheaf S)) [N.IsQuasicoherentOnSite]
  (M : ModuleCat.{u} (BaseRing S))

/-- **The sections of `N ⊗_A M` over an object of `CRIS_aff(X/S)` are `N(T) ⊗_A M`**, through
the counit of `BigAffine.moduleEquivalence`. -/
def tensorConstantModuleAffineSectionsEquiv (B : BigAffineThickening S) :
    (tensorConstantModule N M).val.obj (op B.obj) ≃ₗ[crysSheafRing S B.obj]
      TensorSections N.val M B.obj :=
  ((PresheafOfModules.evaluation _ (op B)).mapIso ((SheafOfModules.forget _).mapIso
    (BigAffine.moduleEquivalenceInverseObjRestrictionIso S (affineTensorSheaf M N)))).toLinearEquiv

/-- **The identification of the sections of `N ⊗_A M` over the objects of `CRIS_aff(X/S)` with
`N(T) ⊗_A M` is natural.** -/
theorem tensorConstantModuleAffineSectionsEquiv_restrict {B B' : BigAffineThickening S}
    (k : B' ⟶ B) (x : (tensorConstantModule N M).val.obj (op B.obj)) :
    tensorConstantModuleAffineSectionsEquiv N M B'
        ((tensorConstantModule N M).val.restrictₛₗ k.hom.op x) =
      tensorRestrict N.val M k.hom (tensorConstantModuleAffineSectionsEquiv N M B x) :=
  PresheafOfModules.naturality_apply ((SheafOfModules.forget _).map
    (BigAffine.moduleEquivalenceInverseObjRestrictionIso S (affineTensorSheaf M N)).hom) k.op x

/-- **The sections of `N ⊗_A M` over an object `(U, T, δ)` of `CRIS(X/S)` with affine ambient
scheme are `N(T) ⊗_A M`**, as a module over `Γ(T, 𝒪_T)` acting on the left factor. -/
def tensorConstantModuleSectionsEquiv (T : Thickening S) [IsAffine T.thickening.target.scheme] :
    (tensorConstantModule N M).val.obj (op T) ≃ₗ[crysSheafRing S T] TensorSections N.val M T :=
  tensorConstantModuleAffineSectionsEquiv N M (BigAffineThickening.mk T)

/-- **The identification of the sections of `N ⊗_A M` with `N(T) ⊗_A M` is natural** in the
objects with affine ambient scheme: it carries the restriction map of `N ⊗_A M` along
`g : T' ⟶ T` to the map `N(T) ⊗_A M ⟶ N(T') ⊗_A M` induced by the restriction map of `N`. -/
theorem tensorConstantModuleSectionsEquiv_restrict {T T' : Thickening S}
    [IsAffine T.thickening.target.scheme] [IsAffine T'.thickening.target.scheme] (g : T' ⟶ T)
    (x : (tensorConstantModule N M).val.obj (op T)) :
    tensorConstantModuleSectionsEquiv N M T' ((tensorConstantModule N M).val.restrictₛₗ g.op x) =
      tensorRestrict N.val M g (tensorConstantModuleSectionsEquiv N M T x) :=
  tensorConstantModuleAffineSectionsEquiv_restrict N M
    (B := BigAffineThickening.mk T) (B' := BigAffineThickening.mk T') (ObjectProperty.homMk g) x

/-- **The sections of `N ⊗_A M` over an object with affine ambient scheme are `N(T) ⊗_A M`, as
`A`-modules**, `A = Γ(S, 𝒪_S)` acting through the structure map `A ⟶ Γ(T, 𝒪_T)`; the right-hand
side is the tensor product `N(T) ⊗ M` of the monoidal category of `A`-modules. -/
def tensorConstantModuleBaseSectionsIso (T : Thickening S) [IsAffine T.thickening.target.scheme] :
    (baseSectionsFunctor (tensorConstantModule N M).val).obj (op T) ≅
      MonoidalCategory.tensorObj ((baseSectionsFunctor N.val).obj (op T)) M :=
  LinearEquiv.toModuleIso
    { toFun := tensorConstantModuleSectionsEquiv N M T
      invFun := (tensorConstantModuleSectionsEquiv N M T).symm
      map_add' := map_add _
      map_smul' := fun a x ↦ ((tensorConstantModuleSectionsEquiv N M T).map_smul (baseMap T a)
        (@id ((tensorConstantModule N M).val.obj (op T)) x)).trans
          (baseMap_smul_tensorSections N.val M T a _)
      left_inv := (tensorConstantModuleSectionsEquiv N M T).left_inv
      right_inv := (tensorConstantModuleSectionsEquiv N M T).right_inv }

/-- `tensorConstantModuleBaseSectionsIso` is `tensorConstantModuleSectionsEquiv`. -/
@[simp]
theorem tensorConstantModuleBaseSectionsIso_hom_apply (T : Thickening S)
    [IsAffine T.thickening.target.scheme] (x : (tensorConstantModule N M).val.obj (op T)) :
    (tensorConstantModuleBaseSectionsIso N M T).hom x = tensorConstantModuleSectionsEquiv N M T x :=
  rfl

/-- **The sections of `N ⊗_A M` on the objects with affine ambient scheme are `T ↦ N(T) ⊗_A M`,
naturally**, as presheaves of `A`-modules on `CRIS_aff(X/S)`. -/
def tensorConstantModuleBaseSectionsNatIso :
    (bigAffineι S).op ⋙ baseSectionsFunctor (tensorConstantModule N M).val ≅
      (bigAffineι S).op ⋙ baseSectionsFunctor N.val ⋙ MonoidalCategory.tensorRight M :=
  NatIso.ofComponents (fun B ↦ tensorConstantModuleBaseSectionsIso N M B.unop.obj) fun {B B'} k ↦ by
    ext x
    exact tensorConstantModuleAffineSectionsEquiv_restrict N M k.unop x

/-! ### Quasi-coherence -/

/-- **The base change of sections of `N ⊗_A M` between objects with affine ambient schemes is
bijective**: through the identifications of the sections with `N(T) ⊗_A M` it is the base change
of sections of `T ↦ N(T) ⊗_A M`, `TensorConstant.bijective_baseChange_affineTensorPresheaf`. -/
theorem bijective_extensionSectionsMapAlong_tensorConstantModule {T T' : Thickening S}
    (g : T' ⟶ T) [IsAffine T.thickening.target.scheme] [IsAffine T'.thickening.target.scheme] :
    Function.Bijective (extensionSectionsMapAlong (tensorConstantModule N M) g) := by
  let k : BigAffineThickening.mk T' ⟶ BigAffineThickening.mk T := ObjectProperty.homMk g
  let eT := tensorConstantModuleSectionsEquiv N M T
  let eT' := tensorConstantModuleSectionsEquiv N M T'
  let L := LinearEquiv.lTensor (ringAlong g) eT
  have hfun := congrFun (coe_eq_of_tmul
    (eT'.toAddEquiv.toAddMonoidHom.comp (extensionSectionsMapAlong (tensorConstantModule N M) g))
    ((BigAffine.baseChange (affineTensorPresheaf N.val M) k).toAddMonoidHom.comp
      L.toAddEquiv.toAddMonoidHom) fun t x ↦ by
    change eT' (extensionSectionsMapAlong (tensorConstantModule N M) g (t ⊗ₜ x)) =
      BigAffine.baseChange (affineTensorPresheaf N.val M) k (L (t ⊗ₜ x))
    rw [extensionSectionsMapAlong_tmul, LinearEquiv.lTensor_tmul]
    exact (eT'.map_smul (siteRingAlong g t) _).trans
      (congrArg (siteRingAlong g t • ·) (tensorConstantModuleSectionsEquiv_restrict N M g x)))
  have hcomp : (extensionSectionsMapAlong (tensorConstantModule N M) g : _ → _) =
      eT'.symm ∘ (BigAffine.baseChange (affineTensorPresheaf N.val M) k) ∘ L :=
    funext fun z ↦ (eT'.symm_apply_apply _).symm.trans (congrArg eT'.symm (hfun z))
  rw [hcomp]
  exact eT'.symm.bijective.comp
    ((bijective_baseChange_affineTensorPresheaf M N inferInstance k).comp L.bijective)

/-- **`N ⊗_A M` is quasi-coherent**: its base change of sections between objects with affine
ambient schemes is bijective, and that characterises quasi-coherence on `CRIS(X/S)`
(`isQuasicoherentOnSite_of_bijective_extensionSectionsMapAlong`, [Stacks, Tag 07IT]). -/
instance isQuasicoherentOnSite_tensorConstantModule :
    (tensorConstantModule N M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_bijective_extensionSectionsMapAlong _ fun g hA' hA ↦
    haveI := hA
    haveI := hA'
    bijective_extensionSectionsMapAlong_tensorConstantModule N M g

/-- **The universe lift `N ↦ N` at module universe `u + 1` preserves quasi-coherence**, the lift
being computed objectwise and therefore commuting with restriction to the slices of the site. -/
theorem isQuasicoherentOnSite_bigModuleULift (N₀ : SheafOfModules.{u} (crystallineStructureSheaf S))
    [hN : N₀.IsQuasicoherentOnSite] :
    ((SmallSite.bigModuleULift S).obj N₀).IsQuasicoherentOnSite :=
  hN.ulift

/-- **The universe lift of `N ⊗_A M` to the module universe `u + 1` is quasi-coherent.** -/
instance isQuasicoherentOnSite_bigModuleULift_tensorConstantModule :
    ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_bigModuleULift _

section Functoriality

variable {N} {N' N'' : SheafOfModules.{u} (crystallineStructureSheaf S)}
  [N'.IsQuasicoherentOnSite] [N''.IsQuasicoherentOnSite] {M} {M' M'' : ModuleCat.{u} (BaseRing S)}

/-- **The morphism `N ⊗_A M ⟶ N' ⊗_A M'`** induced by morphisms `N ⟶ N'` and `M ⟶ M'`. -/
def tensorConstantModuleMap (φ : N ⟶ N') (ψ : M ⟶ M') :
    tensorConstantModule N M ⟶ tensorConstantModule N' M' :=
  (BigAffine.moduleEquivalence S).inverse.map (affineTensorSheafMap φ ψ)

/-- `tensorConstantModuleMap` preserves identities. -/
theorem tensorConstantModuleMap_id :
    tensorConstantModuleMap (𝟙 N) (𝟙 M) = 𝟙 (tensorConstantModule N M) := by
  have h : affineTensorSheafMap (𝟙 N) (𝟙 M) = 𝟙 _ := by
    refine SheafOfModules.Hom.ext ?_
    change (PresheafOfModules.pushforward₀ (bigAffineι S) (crystallineStructureSheaf S).obj).map
      (tensorPresheafMap (𝟙 N.val) (𝟙 M)) = _
    rw [tensorPresheafMap_id, CategoryTheory.Functor.map_id]
    rfl
  rw [tensorConstantModuleMap, h, CategoryTheory.Functor.map_id]
  rfl

/-- `tensorConstantModuleMap` preserves composition. -/
theorem tensorConstantModuleMap_comp (φ : N ⟶ N') (φ' : N' ⟶ N'') (ψ : M ⟶ M')
    (ψ' : M' ⟶ M'') :
    tensorConstantModuleMap (φ ≫ φ') (ψ ≫ ψ') =
      tensorConstantModuleMap φ ψ ≫ tensorConstantModuleMap φ' ψ' := by
  have h : affineTensorSheafMap (φ ≫ φ') (ψ ≫ ψ') =
      affineTensorSheafMap φ ψ ≫ affineTensorSheafMap φ' ψ' := by
    refine SheafOfModules.Hom.ext ?_
    change (PresheafOfModules.pushforward₀ (bigAffineι S) (crystallineStructureSheaf S).obj).map
      (tensorPresheafMap (φ.val ≫ φ'.val) (ψ ≫ ψ')) = _
    rw [tensorPresheafMap_comp, CategoryTheory.Functor.map_comp]
    rfl
  rw [tensorConstantModuleMap, h, CategoryTheory.Functor.map_comp]
  rfl

/-- **The identification of the sections of `N ⊗_A M` with `N(T) ⊗_A M` is natural in `N` and
`M`.** -/
theorem tensorConstantModuleAffineSectionsEquiv_map (φ : N ⟶ N') (ψ : M ⟶ M')
    (B : BigAffineThickening S) (x : (tensorConstantModule N M).val.obj (op B.obj)) :
    tensorConstantModuleAffineSectionsEquiv N' M' B
        ((tensorConstantModuleMap φ ψ).val.app (op B.obj) x) =
      tensorSectionsMap φ.val ψ B.obj (tensorConstantModuleAffineSectionsEquiv N M B x) := by
  have h := (BigAffine.moduleEquivalence S).counitIso.hom.naturality (affineTensorSheafMap φ ψ)
  exact congrArg (fun f ↦ (f.val.app (op B)).hom x) h

end Functoriality

/-- **The tensor product `N ⊗_A M` as a functor** of the quasi-coherent sheaf of
`𝒪_{X/S}`-modules `N` and of the `A`-module `M`. -/
def tensorConstantFunctor :
    (SheafOfModules.isQuasicoherentOnSite (crystallineStructureSheaf S)).FullSubcategory ⥤
      ModuleCat.{u} (BaseRing S) ⥤ SheafOfModules.{u} (crystallineStructureSheaf S) where
  obj N :=
    { obj M := tensorConstantModule N.obj M
      map ψ := tensorConstantModuleMap (𝟙 N.obj) ψ
      map_id M := tensorConstantModuleMap_id
      map_comp ψ ψ' := by
        rw [← tensorConstantModuleMap_comp, Category.id_comp] }
  map φ :=
    { app M := tensorConstantModuleMap φ.hom (𝟙 M)
      naturality M M' ψ := by
        change tensorConstantModuleMap (𝟙 _) ψ ≫ tensorConstantModuleMap φ.hom (𝟙 M') =
          tensorConstantModuleMap φ.hom (𝟙 M) ≫ tensorConstantModuleMap (𝟙 _) ψ
        rw [← tensorConstantModuleMap_comp, ← tensorConstantModuleMap_comp, Category.id_comp,
          Category.comp_id, Category.id_comp, Category.comp_id] }
  map_id N := by
    ext M : 2
    exact tensorConstantModuleMap_id
  map_comp φ φ' := by
    ext M : 2
    change tensorConstantModuleMap (φ.hom ≫ φ'.hom) (𝟙 M) =
      tensorConstantModuleMap φ.hom (𝟙 M) ≫ tensorConstantModuleMap φ'.hom (𝟙 M)
    rw [← tensorConstantModuleMap_comp, Category.id_comp]

/-- The values of `tensorConstantFunctor`. -/
@[simp]
theorem tensorConstantFunctor_obj_obj
    (N : (SheafOfModules.isQuasicoherentOnSite (crystallineStructureSheaf S)).FullSubcategory)
    (M : ModuleCat.{u} (BaseRing S)) :
    (tensorConstantFunctor.obj N).obj M = tensorConstantModule N.obj M := rfl

end Crystalline.GlobalCrystallineSituation

end
