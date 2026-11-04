module

public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
public import StacksFrontier.Deformation.Artin.Obstruction.TangentPullback
public import StacksFrontier.RingTheory.Flat.EqualizerBaseChange

/-!
# Descent of flat base change of tangent modules along an equalizer

Let `x` be an object over `Spec A` of a category fibred in groupoids over the big fppf site of
`S`, let `A → C` be a flat homomorphism of `S`-algebras and `y = x|_{Spec C}`. Say that the
tangent modules of `x` *commute with the base change* `A → C` at the coefficients `M → N` when
the map of Stacks 07YA induces a `C`-linear isomorphism `C ⊗_A T_x(M) ≅ T_y(N)`.

This file proves the diagram chase of the first paragraph of the proof of Stacks 0DNT: given
ring maps `A → A₁ ⇉ A₂` with the base changes `C₁ = C ⊗_A A₁`, `C₂ = C ⊗_A A₂`, if the two rows
`T_x(M) → T_{x₁}(M₁) ⇉ T_{x₂}(M₂)` and `T_y(N) → T_{y₁}(N₁) ⇉ T_{y₂}(N₂)` are equalizers and the
tangent modules of `x₁` and `x₂` commute with the base changes `A₁ → C₁` and `A₂ → C₂`, then
those of `x` commute with `A → C`.

## Main definitions

* `Deformation.Artin.IsTangentBaseChangeIso`: the map of Stacks 07YA induces
  `C ⊗_A T_x(M) ≅ T_y(N)`.
* `Deformation.Artin.coeffComp`: the composite of two maps of coefficients across ring maps.

## Main results

* `Deformation.Artin.tangentPullbackFun_congr`: the map of Stacks 07YA depends only on the ring
  map, the arrow and the map of coefficients, not on how they are written.
* `Deformation.Artin.tangentPullbackFun_comp_of_eq`: functoriality of the map of Stacks 07YA in
  the ring map, for a composite given up to equality.
* `Deformation.Artin.isTangentBaseChangeIso_of_equalizer`: the diagram chase.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace Deformation.Artin

universe u v w

/-- The composite of two maps of coefficients across ring maps `A → C → E`. -/
public def coeffComp {A C E : Type u} [CommRing A] [CommRing C] [CommRing E] (f₁ : A →+* C)
    (f₂ : C →+* E) {M : ModuleCat.{u} A} {N : ModuleCat.{u} C} {K : ModuleCat.{u} E}
    (ψ₁ : M ⟶ (ModuleCat.restrictScalars f₁).obj N)
    (ψ₂ : N ⟶ (ModuleCat.restrictScalars f₂).obj K) :
    M ⟶ (ModuleCat.restrictScalars (f₂.comp f₁)).obj K :=
  ψ₁ ≫ (ModuleCat.restrictScalars f₁).map ψ₂ ≫ (ModuleCat.restrictScalarsComp f₁ f₂).inv.app K

/-- `coeffComp` applies the two maps of coefficients in turn. -/
@[simp]
public theorem coeffComp_apply {A C E : Type u} [CommRing A] [CommRing C] [CommRing E]
    (f₁ : A →+* C) (f₂ : C →+* E) {M : ModuleCat.{u} A} {N : ModuleCat.{u} C}
    {K : ModuleCat.{u} E} (ψ₁ : M ⟶ (ModuleCat.restrictScalars f₁).obj N)
    (ψ₂ : N ⟶ (ModuleCat.restrictScalars f₂).obj K) (m : M) :
    (coeffComp f₁ f₂ ψ₁ ψ₂).hom m = ψ₂.hom (ψ₁.hom m) := rfl

/-- Two `A'`-linear maps out of `A' ⊗[A] P` which agree on the tensors `1 ⊗ p` are equal. -/
private theorem linearMap_ext_of_one_tmul {A A' P N' : Type*} [CommRing A] [CommRing A']
    [Algebra A A'] [AddCommGroup P] [Module A P] [AddCommGroup N'] [Module A' N']
    (f g : A' ⊗[A] P →ₗ[A'] N') (h : ∀ p, f (1 ⊗ₜ p) = g (1 ⊗ₜ p)) : f = g :=
  LinearMap.ext fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      rw [show r ⊗ₜ[A] p = r • (1 ⊗ₜ[A] p) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_smul, h]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Base change of a cokernel, compared with a second cokernel.** Let `K → P → N → 0` be an
exact sequence of `A`-modules and `K' → P' → N' → 0` one of `A'`-modules. Let
`θP : A' ⊗_A P → P'` be bijective and `θK : A' ⊗_A K → K'` surjective, compatible with the two
maps out of `K`. Then an `A`-linear map `μ : N → N'` compatible with `θP` has a bijective
`A'`-linear extension `A' ⊗_A N → N'`. No flatness is needed: this is right exactness of the
tensor product. It is the algebra of the second paragraph of the proof of Stacks 0DNT. -/
public theorem bijective_liftBaseChange_of_exact_surjective {A A' : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] {K P N : Type*} [AddCommGroup K] [Module A K] [AddCommGroup P]
    [Module A P] [AddCommGroup N] [Module A N] {K' P' N' : Type*} [AddCommGroup K']
    [Module A' K'] [AddCommGroup P'] [Module A' P'] [AddCommGroup N'] [Module A' N']
    [Module A N'] [IsScalarTower A A' N']
    (k : K →ₗ[A] P) (q : P →ₗ[A] N) (hkq : Function.Exact k q) (hq : Function.Surjective q)
    (k' : K' →ₗ[A'] P') (q' : P' →ₗ[A'] N') (hkq' : Function.Exact k' q')
    (hq' : Function.Surjective q')
    (θK : A' ⊗[A] K →ₗ[A'] K') (θP : A' ⊗[A] P →ₗ[A'] P')
    (hθK : Function.Surjective θK) (hθP : Function.Bijective θP)
    (hk : ∀ z, k' (θK z) = θP (k.baseChange A' z))
    (μ : N →ₗ[A] N') (hμ : ∀ p, q' (θP (1 ⊗ₜ p)) = μ (q p)) :
    Function.Bijective (μ.liftBaseChange A') := by
  have hcomp : ∀ z, q' (θP z) = μ.liftBaseChange A' (q.baseChange A' z) := fun z =>
    LinearMap.congr_fun (linearMap_ext_of_one_tmul ((q'.comp θP : A' ⊗[A] P →ₗ[A'] N'))
      ((μ.liftBaseChange A').comp (q.baseChange A')) fun p => by
        simp [hμ]) z
  have hqA : Function.Surjective (q.baseChange A') := LinearMap.lTensor_surjective A' hq
  have hexA : Function.Exact (k.baseChange A') (q.baseChange A') := lTensor_exact A' hkq hq
  refine ⟨fun z₁ z₂ h => ?_, fun n' => ?_⟩
  · obtain ⟨w₁, rfl⟩ := hqA z₁
    obtain ⟨w₂, rfl⟩ := hqA z₂
    rw [← sub_eq_zero, ← map_sub]
    rw [← hcomp, ← hcomp, ← sub_eq_zero, ← map_sub, ← map_sub] at h
    obtain ⟨κ', hκ'⟩ := (hkq' _).1 h
    obtain ⟨v, rfl⟩ := hθK κ'
    rw [hk] at hκ'
    rw [← hθP.1 hκ']
    exact (hexA _).2 ⟨v, rfl⟩
  · obtain ⟨p', rfl⟩ := hq' n'
    obtain ⟨w, rfl⟩ := hθP.2 p'
    exact ⟨q.baseChange A' w, (hcomp w).symm⟩

section Congr

variable {A C : Type u} [CommRing A] [CommRing C]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)
  {x y : X} {hx : p.obj x = algebraOver A B S hS toS hA}
  {hy : p.obj y = algebraOver C B S hS toSC hC}
  (F : TangentFunctorData A B S hS toS hA p x hx)
  (G : TangentFunctorData C B S hS toSC hC p y hy)

/-- **The map of Stacks 07YA depends only on its data.** Two presentations of the same ring map,
the same arrow and the same map of coefficients give the same map on tangent modules. -/
public theorem tangentPullbackFun_congr {f f' : A →+* C} (h : f = f')
    (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toSC)
    (hf' : Spec.map (CommRingCat.ofHom f') ≫ toS = toSC)
    {φ φ' : y ⟶ x} (hφeq : φ = φ')
    (hφ : p.IsHomLift (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) φ)
    (hφ' : p.IsHomLift (algebraOverMapOfRingHom f' B S hS toS toSC hA hC hf') φ')
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (ψ' : M.obj ⟶ (ModuleCat.restrictScalars f').obj N.obj)
    (hψ : ∀ m, (ψ.hom m : N.obj) = ψ'.hom m) (t : ↥(F.functor.obj M)) :
    tangentPullbackFun f hf hp φ hφ F G ψ t = tangentPullbackFun f' hf' hp φ' hφ' F G ψ' t := by
  subst h hφeq
  have : ψ = ψ' := ModuleCat.hom_ext (LinearMap.ext hψ)
  subst this
  rfl

variable {E : Type u} [CommRing E] {toSE : Spec (.of E) ⟶ S} {hE : B.Contains (Spec (.of E))}
  {z : X} {hz : p.obj z = algebraOver E B S hS toSE hE}
  (H : TangentFunctorData E B S hS toSE hE p z hz)

/-- **Functoriality of the map of Stacks 07YA**, for a composite ring map, composite arrow and
composite map of coefficients each given up to equality. -/
public theorem tangentPullbackFun_comp_of_eq (f₁ : A →+* C) (f₂ : C →+* E) {g : A →+* E}
    (hg : f₂.comp f₁ = g)
    (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ toS = toSC)
    (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ toSC = toSE)
    (hfg : Spec.map (CommRingCat.ofHom g) ≫ toS = toSE)
    (φ₁ : y ⟶ x) (hφ₁ : p.IsHomLift (algebraOverMapOfRingHom f₁ B S hS toS toSC hA hC hf₁) φ₁)
    (φ₂ : z ⟶ y) (hφ₂ : p.IsHomLift (algebraOverMapOfRingHom f₂ B S hS toSC toSE hC hE hf₂) φ₂)
    {φ : z ⟶ x} (hφeq : φ₂ ≫ φ₁ = φ)
    (hφ : p.IsHomLift (algebraOverMapOfRingHom g B S hS toS toSE hA hE hfg) φ)
    {M : SiteModule A B} {N : SiteModule C B} {K : SiteModule E B}
    (ψ₁ : M.obj ⟶ (ModuleCat.restrictScalars f₁).obj N.obj)
    (ψ₂ : N.obj ⟶ (ModuleCat.restrictScalars f₂).obj K.obj)
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars g).obj K.obj)
    (hψ : ∀ m, (ψ.hom m : K.obj) = ψ₂.hom (ψ₁.hom m)) (t : ↥(F.functor.obj M)) :
    tangentPullbackFun g hfg hp φ hφ F H ψ t =
      tangentPullbackFun f₂ hf₂ hp φ₂ hφ₂ G H ψ₂
        (tangentPullbackFun f₁ hf₁ hp φ₁ hφ₁ F G ψ₁ t) := by
  subst hg hφeq
  exact tangentPullbackFun_comp f₁ f₂ hf₁ hf₂ hfg hp φ₁ hφ₁ φ₂ hφ₂ hφ F G H ψ₁ ψ₂ ψ hψ t

end Congr

/-- A linear map whose extension of scalars agrees with a linear equivalence on the tensors
`1 ⊗ n` has bijective extension of scalars. -/
public theorem bijective_liftBaseChange_of_linearEquiv {A A' : Type*} [CommRing A] [CommRing A']
    [Algebra A A'] {N M' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M']
    [Module A' M'] [Module A M'] [IsScalarTower A A' M'] (μ : N →ₗ[A] M')
    (e : A' ⊗[A] N ≃ₗ[A'] M') (he : ∀ n, e (1 ⊗ₜ n) = μ n) :
    Function.Bijective (μ.liftBaseChange A') := by
  have hfun : ⇑(μ.liftBaseChange A') = ⇑e := funext fun z =>
    (LinearMap.comp_eq_liftBaseChange_of_tmul e.toLinearMap LinearMap.id μ he z).symm
  rw [hfun]
  exact e.bijective

/-- An `f`-semilinear map between modules over `A₁` and `A₂` is linear over any common base `R`
whose structure maps are compatible with `f`. -/
public def semilinearRestrictScalars {R A₁ A₂ M₁ M₂ : Type*} [CommSemiring R] [Semiring A₁]
    [Semiring A₂] [Algebra R A₁] [Algebra R A₂] {f : A₁ →+* A₂} [AddCommMonoid M₁]
    [Module A₁ M₁] [Module R M₁] [IsScalarTower R A₁ M₁] [AddCommMonoid M₂] [Module A₂ M₂]
    [Module R M₂] [IsScalarTower R A₂ M₂] (l : M₁ →ₛₗ[f] M₂)
    (hf : ∀ r, f (algebraMap R A₁ r) = algebraMap R A₂ r) : M₁ →ₗ[R] M₂ where
  toFun := l
  map_add' := map_add l
  map_smul' r t := by
    rw [RingHom.id_apply, ← algebraMap_smul A₁ r t, l.map_smulₛₗ, hf, algebraMap_smul]

/-- `semilinearRestrictScalars` is the underlying map. -/
@[simp]
public theorem semilinearRestrictScalars_apply {R A₁ A₂ M₁ M₂ : Type*} [CommSemiring R]
    [Semiring A₁] [Semiring A₂] [Algebra R A₁] [Algebra R A₂] {f : A₁ →+* A₂} [AddCommMonoid M₁]
    [Module A₁ M₁] [Module R M₁] [IsScalarTower R A₁ M₁] [AddCommMonoid M₂] [Module A₂ M₂]
    [Module R M₂] [IsScalarTower R A₂ M₂] (l : M₁ →ₛₗ[f] M₂)
    (hf : ∀ r, f (algebraMap R A₁ r) = algebraMap R A₂ r) (t : M₁) :
    semilinearRestrictScalars l hf t = l t := rfl

/-- **Descent of a base change isomorphism along an equalizer.** Let `A → C` be flat with
`C₁ = C ⊗_A A₁` and `C₂ = C ⊗_A A₂`, let `N → P ⇉ Q` and `N' → P' ⇉ Q'` be equalizers, and let
`μ, μ₁, μ₂` commute with the rows. If `μ₁` and `μ₂` extend to isomorphisms
`C₁ ⊗_{A₁} P ≅ P'` and `C₂ ⊗_{A₂} Q ≅ Q'`, then `μ` extends to an isomorphism `C ⊗_A N ≅ N'`. -/
public theorem bijective_liftBaseChange_of_equalizer_of_isPushout
    {A A₁ A₂ C C₁ C₂ : Type*} [CommRing A] [CommRing A₁] [CommRing A₂] [CommRing C]
    [CommRing C₁] [CommRing C₂] [Algebra A C] [Algebra A A₁] [Algebra A₁ C₁] [Algebra C C₁]
    [Algebra A C₁] [IsScalarTower A A₁ C₁] [IsScalarTower A C C₁] [Algebra.IsPushout A C A₁ C₁]
    [Algebra A A₂] [Algebra A₂ C₂] [Algebra C C₂] [Algebra A C₂] [IsScalarTower A A₂ C₂]
    [IsScalarTower A C C₂] [Algebra.IsPushout A C A₂ C₂] [Module.Flat A C]
    {N P Q N' P' Q' : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A₁ P] [Module A P] [IsScalarTower A A₁ P]
    [AddCommGroup Q] [Module A₂ Q] [Module A Q] [IsScalarTower A A₂ Q]
    [AddCommGroup N'] [Module C N'] [Module A N'] [IsScalarTower A C N']
    [AddCommGroup P'] [Module C₁ P'] [Module C P'] [Module A₁ P'] [Module A P']
    [IsScalarTower C C₁ P'] [IsScalarTower A₁ C₁ P'] [IsScalarTower A A₁ P']
    [IsScalarTower A C P']
    [AddCommGroup Q'] [Module C₂ Q'] [Module C Q'] [Module A₂ Q'] [Module A Q']
    [IsScalarTower C C₂ Q'] [IsScalarTower A₂ C₂ Q'] [IsScalarTower A A₂ Q']
    [IsScalarTower A C Q']
    (i : N →ₗ[A] P) (a b : P →ₗ[A] Q)
    (hrow : Function.Injective i ∧ ∀ p, (a p = b p ↔ ∃ n, i n = p))
    (i' : N' →ₗ[C] P') (a' b' : P' →ₗ[C] Q')
    (hrow' : Function.Injective i' ∧ ∀ p, (a' p = b' p ↔ ∃ n, i' n = p))
    (μ : N →ₗ[A] N') (μ₁ : P →ₗ[A₁] P') (μ₂ : Q →ₗ[A₂] Q')
    (hμ₁ : Function.Bijective (μ₁.liftBaseChange C₁))
    (hμ₂ : Function.Bijective (μ₂.liftBaseChange C₂))
    (ha : ∀ p, μ₂ (a p) = a' (μ₁ p)) (hb : ∀ p, μ₂ (b p) = b' (μ₁ p))
    (hμ : ∀ n, i' (μ n) = μ₁ (i n)) :
    Function.Bijective (μ.liftBaseChange C) := by
  have hθP := LinearMap.bijective_liftBaseChange_restrictScalars_of_isPushout (R := A) (S := C)
    μ₁ hμ₁
  have hθQ := LinearMap.bijective_liftBaseChange_restrictScalars_of_isPushout (R := A) (S := C)
    μ₂ hμ₂
  have hP : ∀ r p, (μ₁.restrictScalars A).liftBaseChange C (r ⊗ₜ p) = r • μ₁ p :=
    fun r p => LinearMap.liftBaseChange_tmul _ _ r p
  have hQ : ∀ r q, (μ₂.restrictScalars A).liftBaseChange C (r ⊗ₜ q) = r • μ₂ q :=
    fun r q => LinearMap.liftBaseChange_tmul _ _ r q
  exact LinearMap.bijective_liftBaseChange_of_equalizer i a b hrow.1
    (LinearMap.ext fun n => (hrow.2 (i n)).2 ⟨n, rfl⟩) (fun p h => (hrow.2 p).1 h) i' a' b'
    hrow'.1 (LinearMap.ext fun n => (hrow'.2 (i' n)).2 ⟨n, rfl⟩) _ _ hθP hθQ.1
    (LinearMap.map_liftBaseChange_eq_of_tmul _ _ μ₁ μ₂ hP hQ a a' ha)
    (LinearMap.map_liftBaseChange_eq_of_tmul _ _ μ₁ μ₂ hP hQ b b' hb) μ
    fun n => by rw [hP, one_smul, hμ]

/-- The structure morphisms to `S` of a composite ring map compose. -/
public theorem spec_ofHom_comp_eq {S : Scheme.{u}} {A C E : Type u} [CommRing A] [CommRing C]
    [CommRing E] {f₁ : A →+* C} {f₂ : C →+* E} {toS : Spec (.of A) ⟶ S}
    {toSC : Spec (.of C) ⟶ S} {toSE : Spec (.of E) ⟶ S}
    (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ toS = toSC)
    (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ toSC = toSE) :
    Spec.map (CommRingCat.ofHom (f₂.comp f₁)) ≫ toS = toSE := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hf₁, hf₂]

/-- A composite of arrows lying over the morphisms of two ring maps lies over the morphism of
the composite ring map. -/
public theorem isHomLift_algebraOverMapOfRingHom_comp {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {A C E : Type u} [CommRing A] [CommRing C] [CommRing E]
    {f₁ : A →+* C} {f₂ : C →+* E} {toS : Spec (.of A) ⟶ S}
    {toSC : Spec (.of C) ⟶ S} {toSE : Spec (.of E) ⟶ S} {hA : B.Contains (Spec (.of A))}
    {hC : B.Contains (Spec (.of C))} {hE : B.Contains (Spec (.of E))}
    (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ toS = toSC)
    (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ toSC = toSE)
    (hf₁₂ : Spec.map (CommRingCat.ofHom (f₂.comp f₁)) ≫ toS = toSE)
    {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x y z : X}
    {φ₁ : y ⟶ x} (hφ₁ : p.IsHomLift (algebraOverMapOfRingHom f₁ B S hS toS toSC hA hC hf₁) φ₁)
    {φ₂ : z ⟶ y} (hφ₂ : p.IsHomLift (algebraOverMapOfRingHom f₂ B S hS toSC toSE hC hE hf₂) φ₂) :
    p.IsHomLift (algebraOverMapOfRingHom (f₂.comp f₁) B S hS toS toSE hA hE hf₁₂) (φ₂ ≫ φ₁) := by
  rw [← algebraOverMapOfRingHom_comp f₁ f₂ hf₁ hf₂ hf₁₂]
  exact IsHomLift.comp p _ _ φ₂ φ₁

section Naturality

variable {A C D E : Type u} [CommRing A] [CommRing C] [CommRing D] [CommRing E]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S} {toSD : Spec (.of D) ⟶ S}
  {toSE : Spec (.of E) ⟶ S} {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
  {hD : B.Contains (Spec (.of D))} {hE : B.Contains (Spec (.of E))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)
  {x y w z : X} {hx : p.obj x = algebraOver A B S hS toS hA}
  {hy : p.obj y = algebraOver C B S hS toSC hC} {hw : p.obj w = algebraOver D B S hS toSD hD}
  {hz : p.obj z = algebraOver E B S hS toSE hE}
  (F : TangentFunctorData A B S hS toS hA p x hx) (G : TangentFunctorData C B S hS toSC hC p y hy)
  (G' : TangentFunctorData D B S hS toSD hD p w hw)
  (H : TangentFunctorData E B S hS toSE hE p z hz)

/-- **Naturality of the map of Stacks 07YA in commutative squares.** Pulling back along the two
sides of a commutative square of ring maps, arrows and maps of coefficients gives the same map
on tangent modules. -/
public theorem tangentPullbackFun_comm (f₁ : A →+* C) (f₂ : C →+* E) (g₁ : A →+* D)
    (g₂ : D →+* E) (hfg : g₂.comp g₁ = f₂.comp f₁)
    (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ toS = toSC)
    (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ toSC = toSE)
    (hg₁ : Spec.map (CommRingCat.ofHom g₁) ≫ toS = toSD)
    (hg₂ : Spec.map (CommRingCat.ofHom g₂) ≫ toSD = toSE)
    {φ₁ : y ⟶ x} (hφ₁ : p.IsHomLift (algebraOverMapOfRingHom f₁ B S hS toS toSC hA hC hf₁) φ₁)
    {φ₂ : z ⟶ y} (hφ₂ : p.IsHomLift (algebraOverMapOfRingHom f₂ B S hS toSC toSE hC hE hf₂) φ₂)
    {χ₁ : w ⟶ x} (hχ₁ : p.IsHomLift (algebraOverMapOfRingHom g₁ B S hS toS toSD hA hD hg₁) χ₁)
    {χ₂ : z ⟶ w} (hχ₂ : p.IsHomLift (algebraOverMapOfRingHom g₂ B S hS toSD toSE hD hE hg₂) χ₂)
    (hsq : χ₂ ≫ χ₁ = φ₂ ≫ φ₁)
    {M : SiteModule A B} {N : SiteModule C B} {K : SiteModule E B} {L : SiteModule D B}
    (ψ₁ : M.obj ⟶ (ModuleCat.restrictScalars f₁).obj N.obj)
    (ψ₂ : N.obj ⟶ (ModuleCat.restrictScalars f₂).obj K.obj)
    (χψ₁ : M.obj ⟶ (ModuleCat.restrictScalars g₁).obj L.obj)
    (χψ₂ : L.obj ⟶ (ModuleCat.restrictScalars g₂).obj K.obj)
    (hψ : ∀ m, ψ₂.hom (ψ₁.hom m) = χψ₂.hom (χψ₁.hom m)) (t : ↥(F.functor.obj M)) :
    tangentPullbackFun f₂ hf₂ hp φ₂ hφ₂ G H ψ₂ (tangentPullbackFun f₁ hf₁ hp φ₁ hφ₁ F G ψ₁ t) =
      tangentPullbackFun g₂ hg₂ hp χ₂ hχ₂ G' H χψ₂
        (tangentPullbackFun g₁ hg₁ hp χ₁ hχ₁ F G' χψ₁ t) := by
  have hfc := spec_ofHom_comp_eq hf₁ hf₂
  have hl := isHomLift_algebraOverMapOfRingHom_comp hf₁ hf₂ hfc hφ₁ hφ₂
  rw [← tangentPullbackFun_comp_of_eq hp F G H f₁ f₂ rfl hf₁ hf₂ hfc φ₁ hφ₁ φ₂ hφ₂ rfl hl ψ₁ ψ₂
      (coeffComp f₁ f₂ ψ₁ ψ₂) (fun _ => rfl) t,
    ← tangentPullbackFun_comp_of_eq hp F G' H g₁ g₂ hfg hg₁ hg₂ hfc χ₁ hχ₁ χ₂ hχ₂ hsq hl χψ₁ χψ₂
      (coeffComp f₁ f₂ ψ₁ ψ₂) (fun m => hψ m) t]

end Naturality

section Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)

/-- **The tangent modules of `x` commute with the base change `A → C` at `M → N`**: the map of
Stacks 07YA induces a `C`-linear isomorphism `C ⊗_A T_x(M) ≅ T_y(N)`, sending `1 ⊗ t` to the
image of `t`. -/
public def IsTangentBaseChangeIso {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S}
    {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
    (hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC)
    {x y : X} {hx : p.obj x = algebraOver A B S hS toS hA}
    {hy : p.obj y = algebraOver C B S hS toSC hC} (φ : y ⟶ x)
    (hφ : p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ)
    (F : TangentFunctorData A B S hS toS hA p x hx)
    (G : TangentFunctorData C B S hS toSC hC p y hy)
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A C)).obj N.obj) : Prop :=
  ∃ e : (C ⊗[A] ↥(F.functor.obj M)) ≃ₗ[C] ↥(G.functor.obj N),
    ∀ t, e (1 ⊗ₜ t) = tangentPullbackHom (algebraMap A C) hf hp φ hφ F G ψ t

variable {A A₁ A₂ C C₁ C₂ : Type u} [CommRing A] [CommRing A₁] [CommRing A₂] [CommRing C]
  [CommRing C₁] [CommRing C₂]
  [Algebra A C] [Algebra A A₁] [Algebra A₁ C₁] [Algebra C C₁] [Algebra A C₁]
  [IsScalarTower A A₁ C₁] [IsScalarTower A C C₁] [Algebra.IsPushout A C A₁ C₁]
  [Algebra A A₂] [Algebra A₂ C₂] [Algebra C C₂] [Algebra A C₂]
  [IsScalarTower A A₂ C₂] [IsScalarTower A C C₂] [Algebra.IsPushout A C A₂ C₂]
  {a b : A₁ →+* A₂} {a' b' : C₁ →+* C₂}
  {toS : Spec (.of A) ⟶ S} {toS₁ : Spec (.of A₁) ⟶ S} {toS₂ : Spec (.of A₂) ⟶ S}
  {toSC : Spec (.of C) ⟶ S} {toSC₁ : Spec (.of C₁) ⟶ S} {toSC₂ : Spec (.of C₂) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hA₁ : B.Contains (Spec (.of A₁))}
  {hA₂ : B.Contains (Spec (.of A₂))} {hC : B.Contains (Spec (.of C))}
  {hC₁ : B.Contains (Spec (.of C₁))} {hC₂ : B.Contains (Spec (.of C₂))}
  {hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A A₁)) ≫ toS = toS₁}
  {hfa : Spec.map (CommRingCat.ofHom a) ≫ toS₁ = toS₂}
  {hfb : Spec.map (CommRingCat.ofHom b) ≫ toS₁ = toS₂}
  {hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC}
  {hf₁ : Spec.map (CommRingCat.ofHom (algebraMap A₁ C₁)) ≫ toS₁ = toSC₁}
  {hf₂ : Spec.map (CommRingCat.ofHom (algebraMap A₂ C₂)) ≫ toS₂ = toSC₂}
  {hfc₀₁ : Spec.map (CommRingCat.ofHom (algebraMap C C₁)) ≫ toSC = toSC₁}
  {hfa' : Spec.map (CommRingCat.ofHom a') ≫ toSC₁ = toSC₂}
  {hfb' : Spec.map (CommRingCat.ofHom b') ≫ toSC₁ = toSC₂}
  {x x₁ x₂ y y₁ y₂ : X}
  {hx : p.obj x = algebraOver A B S hS toS hA} {hx₁ : p.obj x₁ = algebraOver A₁ B S hS toS₁ hA₁}
  {hx₂ : p.obj x₂ = algebraOver A₂ B S hS toS₂ hA₂}
  {hy : p.obj y = algebraOver C B S hS toSC hC} {hy₁ : p.obj y₁ = algebraOver C₁ B S hS toSC₁ hC₁}
  {hy₂ : p.obj y₂ = algebraOver C₂ B S hS toSC₂ hC₂}
  {φ₀₁ : x₁ ⟶ x}
  {hφ₀₁ : p.IsHomLift (algebraOverMapOfRingHom (algebraMap A A₁) B S hS toS toS₁ hA hA₁ hf₀₁) φ₀₁}
  {α β : x₂ ⟶ x₁}
  {hα : p.IsHomLift (algebraOverMapOfRingHom a B S hS toS₁ toS₂ hA₁ hA₂ hfa) α}
  {hβ : p.IsHomLift (algebraOverMapOfRingHom b B S hS toS₁ toS₂ hA₁ hA₂ hfb) β}
  {φ : y ⟶ x}
  {hφ : p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ}
  {φ₁ : y₁ ⟶ x₁}
  {hφ₁ : p.IsHomLift (algebraOverMapOfRingHom (algebraMap A₁ C₁) B S hS toS₁ toSC₁ hA₁ hC₁ hf₁) φ₁}
  {φ₂ : y₂ ⟶ x₂}
  {hφ₂ : p.IsHomLift (algebraOverMapOfRingHom (algebraMap A₂ C₂) B S hS toS₂ toSC₂ hA₂ hC₂ hf₂) φ₂}
  {φ₀₁' : y₁ ⟶ y}
  {hφ₀₁' : p.IsHomLift
    (algebraOverMapOfRingHom (algebraMap C C₁) B S hS toSC toSC₁ hC hC₁ hfc₀₁) φ₀₁'}
  {α' β' : y₂ ⟶ y₁}
  {hα' : p.IsHomLift (algebraOverMapOfRingHom a' B S hS toSC₁ toSC₂ hC₁ hC₂ hfa') α'}
  {hβ' : p.IsHomLift (algebraOverMapOfRingHom b' B S hS toSC₁ toSC₂ hC₁ hC₂ hfb') β'}
  {M : SiteModule A B} {M₁ : SiteModule A₁ B} {M₂ : SiteModule A₂ B}
  {N : SiteModule C B} {N₁ : SiteModule C₁ B} {N₂ : SiteModule C₂ B}
  {ψ₀₁ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A A₁)).obj M₁.obj}
  {ψa : M₁.obj ⟶ (ModuleCat.restrictScalars a).obj M₂.obj}
  {ψb : M₁.obj ⟶ (ModuleCat.restrictScalars b).obj M₂.obj}
  {ψ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A C)).obj N.obj}
  {ψ₁ : M₁.obj ⟶ (ModuleCat.restrictScalars (algebraMap A₁ C₁)).obj N₁.obj}
  {ψ₂ : M₂.obj ⟶ (ModuleCat.restrictScalars (algebraMap A₂ C₂)).obj N₂.obj}
  {ψ₀₁' : N.obj ⟶ (ModuleCat.restrictScalars (algebraMap C C₁)).obj N₁.obj}
  {ψa' : N₁.obj ⟶ (ModuleCat.restrictScalars a').obj N₂.obj}
  {ψb' : N₁.obj ⟶ (ModuleCat.restrictScalars b').obj N₂.obj}
  {F : TangentFunctorData A B S hS toS hA p x hx}
  {F₁ : TangentFunctorData A₁ B S hS toS₁ hA₁ p x₁ hx₁}
  {F₂ : TangentFunctorData A₂ B S hS toS₂ hA₂ p x₂ hx₂}
  {G : TangentFunctorData C B S hS toSC hC p y hy}
  {G₁ : TangentFunctorData C₁ B S hS toSC₁ hC₁ p y₁ hy₁}
  {G₂ : TangentFunctorData C₂ B S hS toSC₂ hC₂ p y₂ hy₂}

/-- **Descent of a base change isomorphism along an equalizer, for semilinear maps.** The form
of `bijective_liftBaseChange_of_equalizer_of_isPushout` in which every map is semilinear over
its own ring map, as the maps of Stacks 07YA are. -/
public theorem exists_linearEquiv_of_equalizer_of_isPushout [Module.Flat A C]
    {T T₁ T₂ U U₁ U₂ : Type*} [AddCommGroup T] [Module A T] [AddCommGroup T₁] [Module A₁ T₁]
    [AddCommGroup T₂] [Module A₂ T₂] [AddCommGroup U] [Module C U] [AddCommGroup U₁]
    [Module C₁ U₁] [AddCommGroup U₂] [Module C₂ U₂]
    (ha : ∀ r, a (algebraMap A A₁ r) = algebraMap A A₂ r)
    (hb : ∀ r, b (algebraMap A A₁ r) = algebraMap A A₂ r)
    (ha' : ∀ r, a' (algebraMap C C₁ r) = algebraMap C C₂ r)
    (hb' : ∀ r, b' (algebraMap C C₁ r) = algebraMap C C₂ r)
    (i : T →ₛₗ[algebraMap A A₁] T₁) (la : T₁ →ₛₗ[a] T₂) (lb : T₁ →ₛₗ[b] T₂)
    (i' : U →ₛₗ[algebraMap C C₁] U₁) (la' : U₁ →ₛₗ[a'] U₂) (lb' : U₁ →ₛₗ[b'] U₂)
    (μ : T →ₛₗ[algebraMap A C] U) (μ₁ : T₁ →ₛₗ[algebraMap A₁ C₁] U₁)
    (μ₂ : T₂ →ₛₗ[algebraMap A₂ C₂] U₂)
    (hrow : Function.Injective i ∧ ∀ t, (la t = lb t ↔ ∃ s, i s = t))
    (hrow' : Function.Injective i' ∧ ∀ t, (la' t = lb' t ↔ ∃ s, i' s = t))
    (hnat_a : ∀ t, μ₂ (la t) = la' (μ₁ t)) (hnat_b : ∀ t, μ₂ (lb t) = lb' (μ₁ t))
    (hμi : ∀ t, i' (μ t) = μ₁ (i t))
    (h₁ : ∃ e : C₁ ⊗[A₁] T₁ ≃ₗ[C₁] U₁, ∀ t, e (1 ⊗ₜ t) = μ₁ t)
    (h₂ : ∃ e : C₂ ⊗[A₂] T₂ ≃ₗ[C₂] U₂, ∀ t, e (1 ⊗ₜ t) = μ₂ t) :
    ∃ e : C ⊗[A] T ≃ₗ[C] U, ∀ t, e (1 ⊗ₜ t) = μ t := by
  let : Module A T₁ := .compHom T₁ (algebraMap A A₁)
  have : IsScalarTower A A₁ T₁ := .of_algebraMap_smul fun _ _ => rfl
  let : Module A T₂ := .compHom T₂ (algebraMap A A₂)
  have : IsScalarTower A A₂ T₂ := .of_algebraMap_smul fun _ _ => rfl
  let : Module A U := .compHom U (algebraMap A C)
  have : IsScalarTower A C U := .of_algebraMap_smul fun _ _ => rfl
  let : Module C U₁ := .compHom U₁ (algebraMap C C₁)
  let : Module A₁ U₁ := .compHom U₁ (algebraMap A₁ C₁)
  let : Module A U₁ := .compHom U₁ (algebraMap A C₁)
  have : IsScalarTower C C₁ U₁ := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A₁ C₁ U₁ := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A A₁ U₁ := .of_algebraMap_smul fun r t => by
    show algebraMap A₁ C₁ (algebraMap A A₁ r) • t = algebraMap A C₁ r • t
    rw [← IsScalarTower.algebraMap_apply]
  have : IsScalarTower A C U₁ := .of_algebraMap_smul fun r t => by
    show algebraMap C C₁ (algebraMap A C r) • t = algebraMap A C₁ r • t
    rw [← IsScalarTower.algebraMap_apply]
  let : Module C U₂ := .compHom U₂ (algebraMap C C₂)
  let : Module A₂ U₂ := .compHom U₂ (algebraMap A₂ C₂)
  let : Module A U₂ := .compHom U₂ (algebraMap A C₂)
  have : IsScalarTower C C₂ U₂ := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A₂ C₂ U₂ := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A A₂ U₂ := .of_algebraMap_smul fun r t => by
    show algebraMap A₂ C₂ (algebraMap A A₂ r) • t = algebraMap A C₂ r • t
    rw [← IsScalarTower.algebraMap_apply]
  have : IsScalarTower A C U₂ := .of_algebraMap_smul fun r t => by
    show algebraMap C C₂ (algebraMap A C r) • t = algebraMap A C₂ r • t
    rw [← IsScalarTower.algebraMap_apply]
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  let iL : T →ₗ[A] T₁ := semilinearRestrictScalars i fun _ => rfl
  let aL : T₁ →ₗ[A] T₂ := semilinearRestrictScalars la ha
  let bL : T₁ →ₗ[A] T₂ := semilinearRestrictScalars lb hb
  let iL' : U →ₗ[C] U₁ := semilinearRestrictScalars i' fun _ => rfl
  let aL' : U₁ →ₗ[C] U₂ := semilinearRestrictScalars la' ha'
  let bL' : U₁ →ₗ[C] U₂ := semilinearRestrictScalars lb' hb'
  let μL : T →ₗ[A] U := semilinearRestrictScalars μ fun _ => rfl
  let μL₁ : T₁ →ₗ[A₁] U₁ := semilinearRestrictScalars μ₁ fun _ => rfl
  let μL₂ : T₂ →ₗ[A₂] U₂ := semilinearRestrictScalars μ₂ fun _ => rfl
  exact ⟨.ofBijective _ (bijective_liftBaseChange_of_equalizer_of_isPushout iL aL bL hrow iL' aL'
    bL' hrow' μL μL₁ μL₂ (bijective_liftBaseChange_of_linearEquiv μL₁ e₁ he₁)
    (bijective_liftBaseChange_of_linearEquiv μL₂ e₂ he₂) hnat_a hnat_b hμi),
    fun t => LinearMap.liftBaseChange_one_tmul C μL t⟩

include hp in
/-- **The diagram chase of the first paragraph of the proof of Stacks 0DNT.** Let
`A → A₁ ⇉ A₂` be ring maps (through `a`, `b`), `A → C` flat, and `C₁ = C ⊗_A A₁`,
`C₂ = C ⊗_A A₂` with the induced maps `a', b' : C₁ ⇉ C₂`. Let `x ← x₁ ⇇ x₂` and `y ← y₁ ⇇ y₂`
be the restrictions of an object `x` over `Spec A` and of `y = x|_{Spec C}`, compatibly with the
restrictions `y ⟶ x`, `y₁ ⟶ x₁`, `y₂ ⟶ x₂`, and let compatible coefficient modules be given.
If the two rows of tangent modules
`T_x(M) → T_{x₁}(M₁) ⇉ T_{x₂}(M₂)` and `T_y(N) → T_{y₁}(N₁) ⇉ T_{y₂}(N₂)` are equalizers
and the tangent modules of `x₁` and `x₂` commute with the base changes `A₁ → C₁` and
`A₂ → C₂`, then those of `x` commute with `A → C`. -/
public theorem isTangentBaseChangeIso_of_equalizer [Module.Flat A C]
    (ha : a.comp (algebraMap A A₁) = algebraMap A A₂)
    (hb : b.comp (algebraMap A A₁) = algebraMap A A₂)
    (ha' : a'.comp (algebraMap A₁ C₁) = (algebraMap A₂ C₂).comp a)
    (hb' : b'.comp (algebraMap A₁ C₁) = (algebraMap A₂ C₂).comp b)
    (ha'' : a'.comp (algebraMap C C₁) = algebraMap C C₂)
    (hb'' : b'.comp (algebraMap C C₁) = algebraMap C C₂)
    (hsq₀₁ : φ₀₁' ≫ φ = φ₁ ≫ φ₀₁) (hsqa : α' ≫ φ₁ = φ₂ ≫ α) (hsqb : β' ≫ φ₁ = φ₂ ≫ β)
    (hψ₀₁ : ∀ m, ψ₁.hom (ψ₀₁.hom m) = ψ₀₁'.hom (ψ.hom m))
    (hψa : ∀ m, ψ₂.hom (ψa.hom m) = ψa'.hom (ψ₁.hom m))
    (hψb : ∀ m, ψ₂.hom (ψb.hom m) = ψb'.hom (ψ₁.hom m))
    (hrow : Function.Injective (tangentPullbackFun (algebraMap A A₁) hf₀₁ hp φ₀₁ hφ₀₁ F F₁ ψ₀₁) ∧
      ∀ t₁, (tangentPullbackFun a hfa hp α hα F₁ F₂ ψa t₁ =
          tangentPullbackFun b hfb hp β hβ F₁ F₂ ψb t₁ ↔
        ∃ t, tangentPullbackFun (algebraMap A A₁) hf₀₁ hp φ₀₁ hφ₀₁ F F₁ ψ₀₁ t = t₁))
    (hrow' : Function.Injective
        (tangentPullbackFun (algebraMap C C₁) hfc₀₁ hp φ₀₁' hφ₀₁' G G₁ ψ₀₁') ∧
      ∀ t₁, (tangentPullbackFun a' hfa' hp α' hα' G₁ G₂ ψa' t₁ =
          tangentPullbackFun b' hfb' hp β' hβ' G₁ G₂ ψb' t₁ ↔
        ∃ t, tangentPullbackFun (algebraMap C C₁) hfc₀₁ hp φ₀₁' hφ₀₁' G G₁ ψ₀₁' t = t₁))
    (h₁ : IsTangentBaseChangeIso hp hf₁ φ₁ hφ₁ F₁ G₁ ψ₁)
    (h₂ : IsTangentBaseChangeIso hp hf₂ φ₂ hφ₂ F₂ G₂ ψ₂) :
    IsTangentBaseChangeIso hp hf φ hφ F G ψ := by
  refine exists_linearEquiv_of_equalizer_of_isPushout (T := ↥(F.functor.obj M))
    (T₁ := ↥(F₁.functor.obj M₁)) (T₂ := ↥(F₂.functor.obj M₂)) (U := ↥(G.functor.obj N))
    (U₁ := ↥(G₁.functor.obj N₁)) (U₂ := ↥(G₂.functor.obj N₂))
    ?_ ?_ ?_ ?_
    (tangentPullbackHom (algebraMap A A₁) hf₀₁ hp φ₀₁ hφ₀₁ F F₁ ψ₀₁)
    (tangentPullbackHom a hfa hp α hα F₁ F₂ ψa) (tangentPullbackHom b hfb hp β hβ F₁ F₂ ψb)
    (tangentPullbackHom (algebraMap C C₁) hfc₀₁ hp φ₀₁' hφ₀₁' G G₁ ψ₀₁')
    (tangentPullbackHom a' hfa' hp α' hα' G₁ G₂ ψa')
    (tangentPullbackHom b' hfb' hp β' hβ' G₁ G₂ ψb')
    (tangentPullbackHom (algebraMap A C) hf hp φ hφ F G ψ)
    (tangentPullbackHom (algebraMap A₁ C₁) hf₁ hp φ₁ hφ₁ F₁ G₁ ψ₁)
    (tangentPullbackHom (algebraMap A₂ C₂) hf₂ hp φ₂ hφ₂ F₂ G₂ ψ₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact RingHom.congr_fun ha
  · exact RingHom.congr_fun hb
  · exact RingHom.congr_fun ha''
  · exact RingHom.congr_fun hb''
  · exact hrow
  · exact hrow'
  · exact tangentPullbackFun_comm hp F₁ F₂ G₁ G₂ a (algebraMap A₂ C₂) (algebraMap A₁ C₁) a' ha'
      hfa hf₂ hf₁ hfa' hα hφ₂ hφ₁ hα' hsqa ψa ψ₂ ψ₁ ψa' hψa
  · exact tangentPullbackFun_comm hp F₁ F₂ G₁ G₂ b (algebraMap A₂ C₂) (algebraMap A₁ C₁) b' hb'
      hfb hf₂ hf₁ hfb' hβ hφ₂ hφ₁ hβ' hsqb ψb ψ₂ ψ₁ ψb' hψb
  · exact tangentPullbackFun_comm hp F G F₁ G₁ (algebraMap A C) (algebraMap C C₁)
      (algebraMap A A₁) (algebraMap A₁ C₁)
      (by rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq])
      hf hfc₀₁ hf₀₁ hf₁ hφ hφ₀₁' hφ₀₁ hφ₁ hsq₀₁.symm ψ ψ₀₁' ψ₀₁ ψ₁ fun m => (hψ₀₁ m).symm
  · exact h₁
  · exact h₂

end Descent

section OneMorphism

universe v₁ w₁ v₂ w₂

variable {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toSC)
  {X : Type v₁} [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y]
  {p : X ⥤ BigFppfOver B S hS} {q : Y ⥤ BigFppfOver B S hS}
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (Φ : X ⥤ Y) (hΦ : Φ ⋙ q = p)
  {x y : X} (hx : p.obj x = algebraOver A B S hS toS hA)
  (hy : p.obj y = algebraOver C B S hS toSC hC)
  (φ : y ⟶ x) (hφ : p.IsHomLift (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) φ)

include hΦ hx hy hφ in
/-- The image under a `1`-morphism of an arrow lying over `Spec C ⟶ Spec A` lies over it. -/
public theorem isHomLift_oneMorphism_map :
    q.IsHomLift (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) (Φ.map φ) :=
  lift_map_isHomLift p q Φ hΦ _ hy hx φ hφ

include hq in
/-- **A `1`-morphism commutes with the pullback of lift classes of Stacks 07YA.** Pulling a
class of lifts of `x` back to `y` and then taking its image under `Φ` is taking the image of the
class under `Φ` and pulling back along `Φ φ`. -/
public theorem liftClassOfOneMorphism_liftClassPullback {M : SiteModule A B}
    {N : SiteModule C B} (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M) :
    liftClassOfOneMorphism C B S hS toSC hC p q Φ hΦ y hy N
        (liftClassPullback f hf hp φ hφ ψ a) =
      liftClassPullback f hf hq (Φ.map φ)
        (isHomLift_oneMorphism_map f hf Φ hΦ hx hy φ hφ) ψ
        (liftClassOfOneMorphism A B S hS toS hA p q Φ hΦ x hx M a) := by
  induction a using Quotient.ind with
  | _ u =>
    obtain ⟨ρ, hρ, hw⟩ := (underFiberPullback p hp (tangentPullbackBase f hf ψ)
      (tangentPullbackBase_square f hf ψ) φ hφ (hy := hy) u).2
    refine eq_underFiberClassPullback_of_cartesian q hq (tangentPullbackBase f hf ψ)
      (tangentPullbackBase_square f hf ψ) (Φ.map φ) _
      ((squareZeroLiftPost A B S hS toS hA p q Φ hΦ x hx M).obj u)
      ((squareZeroLiftPost C B S hS toSC hC p q Φ hΦ y hy N).obj
        (underFiberPullback p hp (tangentPullbackBase f hf ψ)
          (tangentPullbackBase_square f hf ψ) φ hφ (hy := hy) u).1) rfl rfl (Φ.map ρ) ?_ ?_
    · have hρ' : p.IsHomLift (tangentPullbackBase f hf ψ) ρ := hρ.toIsHomLift
      have h₁ : q.IsHomLift (tangentPullbackBase f hf ψ) (Φ.map ρ) :=
        lift_map_isHomLift p q Φ hΦ _
          (underFiber_right_obj p hy _ (underFiberPullback p hp (tangentPullbackBase f hf ψ)
            (tangentPullbackBase_square f hf ψ) φ hφ (hy := hy) u).1)
          (underFiber_right_obj p hx _ u) ρ hρ'
      exact @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ q hq _ _ _ _ _ _ h₁
    · show Φ.map _ ≫ Φ.map ρ = Φ.map φ ≫ Φ.map u.1.hom
      rw [← Φ.map_comp, ← Φ.map_comp, hw]

variable {F : TangentFunctorData A B S hS toS hA p x hx}
  {G : TangentFunctorData C B S hS toSC hC p y hy}
  {F' : TangentFunctorData A B S hS toS hA q (Φ.obj x)
    (oneMorphism_obj_eq A B S hS toS hA p q Φ hΦ x hx)}
  {G' : TangentFunctorData C B S hS toSC hC q (Φ.obj y)
    (oneMorphism_obj_eq C B S hS toSC hC p q Φ hΦ y hy)}

include hq in
/-- **A `1`-morphism commutes with the map of Stacks 07YA on tangent modules.** -/
public theorem tangentMapOfOneMorphism_tangentPullbackFun {M : SiteModule A B}
    {N : SiteModule C B} (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (t : ↥(F.functor.obj M)) :
    tangentMapOfOneMorphism C B S hS toSC hC p q Φ hΦ y hy G G' N
        (tangentPullbackFun f hf hp φ hφ F G ψ t) =
      tangentPullbackFun f hf hq (Φ.map φ) (isHomLift_oneMorphism_map f hf Φ hΦ hx hy φ hφ)
        F' G' ψ (tangentMapOfOneMorphism A B S hS toS hA p q Φ hΦ x hx F F' M t) := by
  apply (G'.liftEquiv N).injective
  rw [liftEquiv_tangentMapOfOneMorphism, liftEquiv_tangentPullbackFun,
    liftEquiv_tangentPullbackFun, liftEquiv_tangentMapOfOneMorphism]
  exact liftClassOfOneMorphism_liftClassPullback f hf hp hq Φ hΦ hx hy φ hφ ψ _

include hq in
/-- **Flat base change of tangent modules transfers along a `1`-morphism which is bijective on
tangent modules.** If `Φ` induces bijections `T_x(M) ≅ T_{Φ x}(M)` and `T_y(N) ≅ T_{Φ y}(N)`
and the tangent modules of `x` commute with the base change `A → C`, then so do those of
`Φ x`. -/
public theorem isTangentBaseChangeIso_of_oneMorphism [Algebra A C]
    {hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC}
    {hφ : p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ}
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A C)).obj N.obj)
    (hbx : Function.Bijective (tangentMapOfOneMorphism A B S hS toS hA p q Φ hΦ x hx F F' M))
    (hby : Function.Bijective (tangentMapOfOneMorphism C B S hS toSC hC p q Φ hΦ y hy G G' N))
    (h : IsTangentBaseChangeIso hp hf φ hφ F G ψ) :
    IsTangentBaseChangeIso hq hf (Φ.map φ) (isHomLift_oneMorphism_map _ hf Φ hΦ hx hy φ hφ)
      F' G' ψ := by
  obtain ⟨e, he⟩ := h
  let ex := LinearEquiv.ofBijective
    (tangentLinearMapOfOneMorphism A B S hS toS hA p q Φ hΦ x hx F F' hq M) hbx
  let ey := LinearEquiv.ofBijective
    (tangentLinearMapOfOneMorphism C B S hS toSC hC p q Φ hΦ y hy G G' hq N) hby
  let ex' : (C ⊗[A] ↥(F.functor.obj M)) ≃ₗ[C] (C ⊗[A] ↥(F'.functor.obj M)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) ex
  refine ⟨ex'.symm.trans (e.trans ey), fun t' => ?_⟩
  obtain ⟨t, rfl⟩ := ex.surjective t'
  have h₁ : ex'.symm (1 ⊗ₜ ex t) = 1 ⊗ₜ t := ex'.symm_apply_eq.mpr
    (TensorProduct.AlgebraTensorModule.congr_tmul (LinearEquiv.refl C C) ex 1 t).symm
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h₁, he]
  exact tangentMapOfOneMorphism_tangentPullbackFun _ hf hp hq Φ hΦ hx hy φ hφ ψ t

include hq in
/-- **Flat base change of tangent modules descends along a 1-morphism surjective on tangent
modules, given the kernels.** Let `Φ` induce surjections `T_u(M) → T_{Φ u}(M)` and
`T_v(N) → T_{Φ v}(N)`, whose kernels are the images of `k : K → T_u(M)` and
`k' : K' → T_v(N)`, and let `θK : C ⊗_A K → K'` be surjective and compatible with the map of
Stacks 07YA. If the tangent modules of `u` commute with the base change `A → C`, then so do
those of `Φ u`. This is the second paragraph of the proof of Stacks 0DNT, where `Φ` is a smooth
atlas, `K = T_{e ∘ u}(R)` for `R = U ×_𝒳 U` and the kernel is given by Stacks 0DNN. -/
public theorem isTangentBaseChangeIso_of_surjective_oneMorphism [Algebra A C]
    {hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC}
    {hφ : p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ}
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A C)).obj N.obj)
    {K K' : Type*} [AddCommGroup K] [Module A K] [AddCommGroup K'] [Module C K']
    (k : K →ₗ[A] ↥(F.functor.obj M)) (k' : K' →ₗ[C] ↥(G.functor.obj N))
    (hk : Function.Exact k (tangentLinearMapOfOneMorphism A B S hS toS hA p q Φ hΦ x hx F F' hq M))
    (hk' : Function.Exact k'
      (tangentLinearMapOfOneMorphism C B S hS toSC hC p q Φ hΦ y hy G G' hq N))
    (hsx : Function.Surjective (tangentMapOfOneMorphism A B S hS toS hA p q Φ hΦ x hx F F' M))
    (hsy : Function.Surjective (tangentMapOfOneMorphism C B S hS toSC hC p q Φ hΦ y hy G G' N))
    (θK : C ⊗[A] K →ₗ[C] K') (hθK : Function.Surjective θK)
    (hkθ : ∀ κ, k' (θK (1 ⊗ₜ κ)) = tangentPullbackHom (algebraMap A C) hf hp φ hφ F G ψ (k κ))
    (h : IsTangentBaseChangeIso hp hf φ hφ F G ψ) :
    IsTangentBaseChangeIso hq hf (Φ.map φ) (isHomLift_oneMorphism_map _ hf Φ hΦ hx hy φ hφ)
      F' G' ψ := by
  obtain ⟨e, he⟩ := h
  let : Module A ↥(G'.functor.obj N) := Module.compHom _ (algebraMap A C)
  have : IsScalarTower A C ↥(G'.functor.obj N) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hl := isHomLift_oneMorphism_map _ hf Φ hΦ hx hy φ hφ
  let μ : ↥(F'.functor.obj M) →ₗ[A] ↥(G'.functor.obj N) :=
    semilinearRestrictScalars (tangentPullbackHom (algebraMap A C) hf hq (Φ.map φ) hl F' G' ψ)
      fun _ => rfl
  have hθk : ∀ z, k' (θK z) = e.toLinearMap (k.baseChange C z) := fun z =>
    LinearMap.congr_fun (linearMap_ext_of_one_tmul ((k'.comp θK : C ⊗[A] K →ₗ[C] _))
      (e.toLinearMap.comp (k.baseChange C)) fun κ => by simp [hkθ, he]) z
  have hbij := bijective_liftBaseChange_of_exact_surjective k
    (tangentLinearMapOfOneMorphism A B S hS toS hA p q Φ hΦ x hx F F' hq M) hk hsx k'
    (tangentLinearMapOfOneMorphism C B S hS toSC hC p q Φ hΦ y hy G G' hq N) hk' hsy
    θK e.toLinearMap hθK e.bijective hθk μ (fun t => by
      rw [LinearEquiv.coe_coe, he, tangentLinearMapOfOneMorphism_apply,
        tangentLinearMapOfOneMorphism_apply]
      exact tangentMapOfOneMorphism_tangentPullbackFun _ hf hp hq Φ hΦ hx hy φ hφ ψ t)
  refine ⟨LinearEquiv.ofBijective (μ.liftBaseChange C) hbij, fun t => ?_⟩
  rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end OneMorphism

section FormallySmooth

universe w'

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- The square-zero immersion `Spec A ⟶ Spec A[M]` is a first-order thickening of affine
schemes. -/
public theorem isFirstOrderThickening_squareZeroArrow (M : SiteModule A B) :
    Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (squareZeroArrow A B S hS toS hA M)) := by
  refine Stacks.Smooth.isFirstOrderThickening_specMap
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) ?_
  rw [pow_two, ← le_bot_iff]
  refine Ideal.mul_le.2 fun r hr s hs => ?_
  have hr' : r.fst = 0 := hr
  have hs' : s.fst = 0 := hs
  exact Ideal.mem_bot.2 (TrivSqZeroExt.ext (by simp [hr', hs']) (by simp [hr', hs']))

/-- **The commuting square of formal smoothness on objects, as a factorization.** For a
`1`-morphism `Φ` of fibred categories, an object `x` over `U`, a lift `x'` over `U'` of it along
`i : U ⟶ U'` (through `β`), an object `y'` over `U'` with an isomorphism `γ` from `Φ x` to the
pullback of `y'` and an isomorphism `γ'` from `Φ x'` to `y'`, the square relating `γ`, `β`,
`γ'` and the comparison `cmp` of pullbacks says that the arrow `Φ x ⟶ y'` read off from `γ`
factors as `Φ` of the arrow `x ⟶ x'` followed by `γ'`. -/
public theorem fiberSquare_fac {𝒮 : Type*} [Category 𝒮] {X : Type*} [Category X] {Y : Type*}
    [Category Y] {p : X ⥤ 𝒮} {q : Y ⥤ 𝒮} [p.IsFibered] [q.IsFibered] (Φ : X ⥤ Y)
    (hΦ : Φ ⋙ q = p) {U U' : 𝒮} (i : U ⟶ U') {x : p.Fiber U} {y' : q.Fiber U'}
    {γ : (Functor.Fiber.mapOfComp p q Φ hΦ U).obj x ≅ Functor.pullbackFiber q y' i}
    {x' : p.Fiber U'} {β : Functor.pullbackFiber p x' i ≅ x}
    {γ' : (Functor.Fiber.mapOfComp p q Φ hΦ U').obj x' ≅ y'}
    {cmp : Functor.pullbackFiber q ((Functor.Fiber.mapOfComp p q Φ hΦ U').obj x') i ≅
      (Functor.Fiber.mapOfComp p q Φ hΦ U).obj (Functor.pullbackFiber p x' i)}
    (hcmp : Functor.Fiber.fiberInclusion.map cmp.hom ≫
        Φ.map (Functor.IsPreFibered.pullbackMap x'.2 i) =
      Functor.IsPreFibered.pullbackMap ((Functor.Fiber.mapOfComp p q Φ hΦ U').obj x').2 i)
    (hsq : (cmp.hom ≫ (Functor.Fiber.mapOfComp p q Φ hΦ U).map β.hom) ≫ γ.hom =
      Functor.pullbackFiberHom (p := q) γ'.hom i) :
    Functor.Fiber.fiberInclusion.map γ.hom ≫ Functor.IsPreFibered.pullbackMap y'.2 i =
      Φ.map (Functor.Fiber.fiberInclusion.map β.inv ≫
          Functor.IsPreFibered.pullbackMap x'.2 i) ≫
        Functor.Fiber.fiberInclusion.map γ'.hom := by
  have hsqMap := congrArg Functor.Fiber.fiberInclusion.map hsq
  rw [Functor.Fiber.fiberInclusion.map_comp, Functor.Fiber.fiberInclusion.map_comp,
    Functor.Fiber.fiberInclusion_map_mapOfComp_map p q Φ hΦ U β.hom] at hsqMap
  have h := congrArg (fun t => t ≫ Functor.IsPreFibered.pullbackMap y'.2 i) hsqMap
  have e₂ := Functor.pullbackFiberHom_fac γ'.hom i
  have k₁ : Functor.Fiber.fiberInclusion.map cmp.hom ≫
      (Φ.map (Functor.Fiber.fiberInclusion.map β.hom) ≫
        (Functor.Fiber.fiberInclusion.map γ.hom ≫ Functor.IsPreFibered.pullbackMap y'.2 i)) =
      Functor.Fiber.fiberInclusion.map cmp.hom ≫
        (Φ.map (Functor.IsPreFibered.pullbackMap x'.2 i) ≫
          Functor.Fiber.fiberInclusion.map γ'.hom) :=
    ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm).trans
      (h.trans (e₂.trans ((congrArg (· ≫ Functor.Fiber.fiberInclusion.map γ'.hom)
        hcmp.symm).trans (Category.assoc _ _ _))))
  have hcancel := (cancel_epi (Functor.Fiber.fiberInclusion.map cmp.hom)).mp k₁
  have hβ : Φ.map (Functor.Fiber.fiberInclusion.map β.inv) ≫
      Φ.map (Functor.Fiber.fiberInclusion.map β.hom) = 𝟙 _ := by
    rw [← Φ.map_comp, ← CategoryTheory.Functor.map_comp, β.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hβ.symm)).trans
    (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hcancel)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Φ.map_comp _ _).symm)))

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w'} (BigFppfOver B S hS)} (P : 𝒳 ⟶ 𝒴)

/-- **A 1-morphism formally smooth on objects is surjective on lift classes.** If `P : 𝒳 ⟶ 𝒴`
is formally smooth on objects (Stacks 06D0), then every lift of `P x` to `Spec A[M]` is, up to
isomorphism, the image of a lift of `x`: the map `T_x(M) ⟶ T_{P x}(M)` on lift classes is
surjective. This is the surjectivity in the second paragraph of the proof of Stacks 0DNT. -/
public theorem surjective_liftClassOfOneMorphism_of_isFormallySmoothOnObjects
    (hP : Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 P) (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA) (M : SiteModule A B) :
    Function.Surjective (liftClassOfOneMorphism A B S hS toS hA 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor P) (CatFiberedInGroupoids.homFunctor_comp_p P) x hx M) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  set Φ := CatFiberedInGroupoids.homFunctor P
  set i := squareZeroArrow A B S hS toS hA M
  rintro ⟨t⟩
  have hFx : 𝒴.val.p.obj (Φ.obj x) = algebraOver A B S hS toS hA :=
    oneMorphism_obj_eq A B S hS toS hA 𝒳.val.p 𝒴.val.p Φ
      (CatFiberedInGroupoids.homFunctor_comp_p P) x hx
  have : 𝒴.val.p.IsHomLift i t.1.hom := underFiber_isHomLift 𝒴.val.p hFx i t
  let x₀ : 𝒳.val.p.Fiber (algebraOver A B S hS toS hA) := ⟨x, hx⟩
  let y' : 𝒴.val.p.Fiber (squareZeroOver A B S hS toS M) :=
    ⟨t.1.right, underFiber_right_obj 𝒴.val.p hFx i t⟩
  let pU := Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p Φ
    (CatFiberedInGroupoids.homFunctor_comp_p P) (algebraOver A B S hS toS hA)
  have htc : 𝒴.val.p.IsCartesian i t.1.hom :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ _ _ _ _ _ _ _
      (𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift i t.1.hom)
  let γ : pU.obj x₀ ≅ Functor.pullbackFiber 𝒴.val.p y' i :=
    Functor.fiberIsoOfCartesian (z := pU.obj x₀) i t.1.hom
      (Functor.IsPreFibered.pullbackMap y'.2 i) htc
      (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
  have hγ : Functor.Fiber.fiberInclusion.map γ.hom ≫ Functor.IsPreFibered.pullbackMap y'.2 i =
      t.1.hom := Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _
  obtain ⟨x', β, γ', hsq⟩ := hP _ _ i (show IsAffine (Spec (.of A)) from inferInstance)
    (show IsAffine (Spec (squareZeroRing A M.obj)) from inferInstance)
    (isFirstOrderThickening_squareZeroArrow A toS hA M) x₀ y' γ
  have hfac := fiberSquare_fac Φ (CatFiberedInGroupoids.homFunctor_comp_p P) i
    (Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _) hsq
  rw [hγ] at hfac
  -- The lift of `x` produced by formal smoothness.
  let ℓ : x ⟶ x'.1 :=
    Functor.Fiber.fiberInclusion.map β.inv ≫ Functor.IsPreFibered.pullbackMap x'.2 i
  have hℓ : 𝒳.val.p.IsHomLift i ℓ :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒳.val.p _ _ _ (algebraOver A B S hS toS hA) _ β.inv.2
      _ _ i (Functor.IsPreFibered.pullbackMap x'.2 i)
      (Functor.IsPreFibered.pullbackMap.IsCartesian x'.2 i).toIsHomLift
  let l := underFiberObjMk 𝒳.val.p hx i ℓ hℓ
  refine ⟨Quotient.mk _ l, ?_⟩
  show Quotient.mk _ ((squareZeroLiftPost A B S hS toS hA 𝒳.val.p 𝒴.val.p Φ
    (CatFiberedInGroupoids.homFunctor_comp_p P) x hx M).obj l) = Quotient.mk _ t
  exact underFiberClass_eq_of_cartesian 𝒴.val.p (𝟙 _) (𝟙 (Φ.obj x)) (u₁ := t) (u₂ := t) rfl
    (Functor.Fiber.fiberInclusion.map γ'.hom) (𝟙 t.1.right)
    (@Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ 𝒴.val.p
      𝒴.isFiberedInGroupoids _ _ _ _ _ _ γ'.hom.2)
    (@Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ 𝒴.val.p
      𝒴.isFiberedInGroupoids _ _ _ _ _ _ (IsHomLift.id (underFiber_right_obj 𝒴.val.p hFx i t)))
    (by rw [Category.id_comp]; exact hfac.symm) (by rw [Category.id_comp, Category.comp_id])

end FormallySmooth

end Deformation.Artin

end
