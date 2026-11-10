module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# The completed stalk of a coherent adic system along a specialization

Let `X` be a locally Noetherian scheme, let `ℐ` be a quasi-coherent sheaf of ideals on `X`, let
`(ℱ_n)` be an object of `Coh(X, ℐ)` and let `y ⤳ y'` be a specialization of points of `X`. Write
`𝒪_{X,y'}^∧` for the `ℐ`-adically completed local ring of
`Stacks.Algebraization.completedLocalRing` and `ℱ_{y'}^∧` for the completed stalk of
`Stacks.Algebraization.completedStalk`. Let `𝔭 ⊆ 𝒪_{X,y'}` be the prime corresponding to `y` under
`AlgebraicGeometry.Scheme.fromSpecStalk`, assumed to contain the stalk `ℐ_{y'}`, and let `𝔮` be
the prime `Stacks.Algebraization.completedStalkPrime` of `𝒪_{X,y'}^∧` above it. This file proves
that

  `ℱ_y^∧ = ((ℱ_{y'}^∧)_𝔮)^∧`,

the module-level analogue of
`Stacks.Algebraization.nonempty_algEquiv_completedLocalRing_of_specializes`: the completed stalk
at `y` is the adic completion of the localization at `𝔮` of the completed stalk at `y'`.

## Main definitions

* `Stacks.Algebraization.adicCompletionLinearEquivOfLevelEquiv`: The isomorphism of adic
  completions of modules over two different rings assembled from compatible isomorphisms of the
  level quotients.

## Main results

* `Stacks.Algebraization.nonempty_linearEquiv_completedStalk_of_specializes`: The completed stalk
  at a generalization is the adic completion of a localization of the completed stalk.

## Implementation notes

The two sides are modules over different rings — `𝒪_{X,y}` and the localization of
`𝒪_{X,y'}^∧` at `𝔮` — and the equivalence is stated over the common base `𝒪_{X,y'}`. Instance
search cannot produce the `𝒪_{X,y'}`-module structure on the formal stalk at `y`, since that is
the restriction of scalars along the specialization map of local rings; it is carried in the
statement by `letI`, exactly as the algebra structure on `𝒪_{X,y}` is in the ring-level
statement. The remaining structures on the right-hand side — the `𝒪_{X,y'}`-algebra structure on
the localization, and its module structure on the localized completed stalk — are found by
instance search, through the localization instances.

## References

* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the paragraph
  introducing `𝒪_{X,y}^∧` and `ℱ_y^∧`.
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE), the completed stalk.
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), the base change of the
  completed stalk along a specialization; its second display, which the source states for an
  abstract Noetherian ring, is what is proved here on a scheme.
* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

/-! ### Assembling an isomorphism of adic completions from the level quotients -/

/-- **An isomorphism of adic completions assembled from the level quotients.** -/
public def adicCompletionLinearEquivOfLevelEquiv
    {A : Type*} [CommRing A]
    {R₁ : Type*} [CommRing R₁] [Algebra A R₁]
    {R₂ : Type*} [CommRing R₂] [Algebra A R₂]
    {M₁ : Type*} [AddCommGroup M₁] [Module R₁ M₁] [Module A M₁] [IsScalarTower A R₁ M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R₂ M₂] [Module A M₂] [IsScalarTower A R₂ M₂]
    (I₁ : Ideal R₁) (I₂ : Ideal R₂)
    (e : ∀ n : ℕ, (M₁ ⧸ (I₁ ^ n • ⊤ : Submodule R₁ M₁)) ≃ₗ[A]
      (M₂ ⧸ (I₂ ^ n • ⊤ : Submodule R₂ M₂)))
    (he : ∀ {m n : ℕ} (hmn : m ≤ n) (x : M₁ ⧸ (I₁ ^ n • ⊤ : Submodule R₁ M₁)),
      AdicCompletion.transitionMap I₂ M₂ hmn (e n x) =
        e m (AdicCompletion.transitionMap I₁ M₁ hmn x)) :
    AdicCompletion I₁ M₁ ≃ₗ[A] AdicCompletion I₂ M₂ where
  toFun x := ⟨fun n => e n (x.val n), fun hmn => by rw [he hmn, x.property hmn]⟩
  invFun x := ⟨fun n => (e n).symm (x.val n), fun {m n} hmn => by
    apply (e m).injective
    rw [← he hmn, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, x.property hmn]⟩
  left_inv x := AdicCompletion.ext fun n => (e n).symm_apply_apply _
  right_inv x := AdicCompletion.ext fun n => (e n).apply_symm_apply _
  map_add' x y := AdicCompletion.ext fun n => (e n).map_add _ _
  map_smul' a x := AdicCompletion.ext fun n => (e n).map_smul _ _

/-! ### Elementary facts about the level quotients -/

/-- The level-zero quotient `M ⧸ I ^ 0 • ⊤` is trivial. -/
private theorem subsingleton_quotient_pow_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) : Subsingleton (M ⧸ (I ^ 0 • ⊤ : Submodule R M)) := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  infer_instance

/-- The zero map is a linear equivalence between trivial modules. -/
private def linearEquivOfSubsingleton {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Subsingleton M] [Subsingleton N] : M ≃ₗ[R] N where
  toFun _ := 0
  invFun _ := 0
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- A scalar whose action lands inside the submodule acts by zero on the quotient, even when the
submodule is taken over a larger ring. -/
private theorem smul_quotient_eq_zero {B C M : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [AddCommGroup M] [Module B M] [Module C M] [IsScalarTower B C M]
    (M' : Submodule C M) {d : B} (hd : ∀ m : M, d • m ∈ M') (z : M ⧸ M') : d • z = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hd m

/-- An element of an adic completion outside the prime `𝔮` of
`Stacks.Algebraization.adicPrimeOver` differs, modulo `JⁿR^∧`, from an element of `R` outside
`𝔭`. -/
private theorem exists_notMem_sub_mem_map_pow {R : Type u} [CommRing R] (Jr : Ideal R)
    (hJ : Jr.FG) {p : Ideal R} [p.IsPrime] (hJp : Jr ≤ p) (n : ℕ)
    {x : AdicCompletion Jr R} (hx : x ∉ (adicPrimeOver Jr hJp).asIdeal) :
    ∃ a : R, a ∉ p ∧ x - algebraMap R (AdicCompletion Jr R) a ∈
      (Jr ^ n).map (algebraMap R (AdicCompletion Jr R)) := by
  obtain ⟨a, ha⟩ := AdicCompletion.exists_sub_mem_map_pow Jr hJ (max n 1) x
  have hmax0 : max n 1 ≠ 0 := by omega
  refine ⟨a, ?_, Ideal.map_mono (Ideal.pow_le_pow_right (le_max_left n 1)) ha⟩
  intro hap
  refine hx ?_
  have h1 : x - algebraMap R (AdicCompletion Jr R) a ∈ (adicPrimeOver Jr hJp).asIdeal :=
    map_le_adicPrimeOver Jr hJp (Ideal.map_mono (Ideal.pow_le_self hmax0) ha)
  have h2 : algebraMap R (AdicCompletion Jr R) a ∈ (adicPrimeOver Jr hJp).asIdeal := by
    rw [← Ideal.mem_comap, comap_adicPrimeOver]
    exact hap
  simpa using (adicPrimeOver Jr hJp).asIdeal.add_mem h1 h2

/-! ### Changing the base ring of a localization -/

/-- **A localization over a ring is a localization over a subring whose multiplicative set acts
in the same way.** -/
private theorem isLocalizedModule_restrictScalars_of_smul_eq
    {R B M P : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [AddCommGroup P] [Module R P] [Module B P] [IsScalarTower R B P]
    (S : Submonoid R) (T : Submonoid B)
    (hST : ∀ a ∈ S, algebraMap R B a ∈ T)
    (hTS : ∀ t ∈ T, ∃ a ∈ S, (∀ m : M, t • m = algebraMap R B a • m) ∧
      (∀ x : P, t • x = algebraMap R B a • x))
    (g : M →ₗ[B] P) [IsLocalizedModule T g] :
    IsLocalizedModule S (g.restrictScalars R) where
  map_units a := by
    refine (Module.End.isUnit_iff _).mpr ?_
    have hb := (Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units g ⟨algebraMap R B (a : R), hST a a.2⟩)
    convert hb using 1
    exact funext fun x => by
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, algebraMap_smul]
  surj x := by
    obtain ⟨⟨m, t⟩, ht⟩ := IsLocalizedModule.surj T g x
    obtain ⟨a, ha, _, hP⟩ := hTS t t.2
    refine ⟨⟨m, ⟨a, ha⟩⟩, ?_⟩
    have h1 : (a : R) • x = (t : B) • x := by
      rw [hP x, algebraMap_smul]
    simpa [Submonoid.smul_def, h1] using ht
  exists_of_eq {m₁ m₂} e := by
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g) e
    obtain ⟨a, ha, hM, _⟩ := hTS t t.2
    refine ⟨⟨a, ha⟩, ?_⟩
    have h1 : ∀ m : M, (a : R) • m = (t : B) • m := fun m => by
      rw [hM m, algebraMap_smul]
    simpa [Submonoid.smul_def, h1] using ht

/-! ### Naturality of the level identifications -/

section Levels

variable {X : Scheme.{u}} {J : X.IdealSheafData}

/-- **The specialization map of stalks is natural in the sheaf of modules.** -/
private theorem stalkSpecializes_modulesStalkFunctor_map {F F' : X.Modules} (φ : F ⟶ F')
    {y y' : X} (h : y ⤳ y') (m : F.presheaf.stalk y') :
    F'.presheaf.stalkSpecializes h (((modulesStalkFunctor X y').map φ).hom m) =
      ((modulesStalkFunctor X y).map φ).hom (F.presheaf.stalkSpecializes h m) := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
  rw [modulesStalkFunctor_map_germ φ y' U hU s,
    Stacks.ModuleStalkSpecialization.germ_stalkSpecializes_apply F' hU h,
    Stacks.ModuleStalkSpecialization.germ_stalkSpecializes_apply F hU h,
    modulesStalkFunctor_map_germ φ y U (h.mem_open U.isOpen hU) s]

/-- The identification of the level-`n` quotient of the formal stalk with `ℱ_{n,x}` is induced by
the limit projection to level `n`. -/
private theorem formalStalkQuotientEquivStalk_mk [IsLocallyNoetherian X]
    (G : Stacks.Coherent.CoherentAdicSystems J) (x : X) (n : ℕ) (m : formalStalk G x) :
    formalStalkQuotientEquivStalk G x n (Submodule.Quotient.mk m) =
      (limit.π (G.obj ⋙ modulesStalkFunctor X x) (op n)).hom
        (formalStalkEquivModuleStalkLimit G x m) := rfl

/-- The identification of the level-`n` quotient of the completed stalk with `ℱ_{n,x}` is the
limit projection read on the formal stalk. -/
private theorem completedStalkQuotientEquivStalk_mk [IsLocallyNoetherian X]
    (G : Stacks.Coherent.CoherentAdicSystems J) (x : X) (n : ℕ) (a : completedStalk J G x) :
    completedStalkQuotientEquivStalk G x n (Submodule.Quotient.mk a) =
      (limit.π (G.obj ⋙ modulesStalkFunctor X x) (op n)).hom
        (formalStalkEquivModuleStalkLimit G x
          ((formalStalkEquivCompletedStalk G x).symm a)) := rfl

/-- The level identifications of the formal stalk are compatible with the transition maps. -/
private theorem formalStalkQuotientEquivStalk_factorPow [IsLocallyNoetherian X]
    (G : Stacks.Coherent.CoherentAdicSystems J) (x : X) {k l : ℕ} (hkl : k ≤ l)
    (hmn : k + 1 ≤ l + 1)
    (z : formalStalk G x ⧸ (IdealSheafData.stalk J x ^ (l + 1) •
      (⊤ : Submodule (X.presheaf.stalk x) (formalStalk G x)))) :
    ((modulesStalkFunctor X x).map (G.obj.map (homOfLE hkl).op)).hom
        (formalStalkQuotientEquivStalk G x l z) =
      formalStalkQuotientEquivStalk G x k
        (AdicCompletion.transitionMap (IdealSheafData.stalk J x) (formalStalk G x) hmn z) := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [formalStalkQuotientEquivStalk_mk,
    show AdicCompletion.transitionMap (IdealSheafData.stalk J x) (formalStalk G x)
        hmn (Submodule.Quotient.mk m) = Submodule.Quotient.mk m from rfl,
    formalStalkQuotientEquivStalk_mk]
  exact congrArg (fun f => f.hom (formalStalkEquivModuleStalkLimit G x m))
    (limit.w (G.obj ⋙ modulesStalkFunctor X x) (homOfLE hkl).op)

/-- The level identifications of the completed stalk are compatible with the transition maps. -/
private theorem completedStalkQuotientEquivStalk_factorPow [IsLocallyNoetherian X]
    (G : Stacks.Coherent.CoherentAdicSystems J) (x : X) {k l : ℕ} (hkl : k ≤ l)
    (hmn : k + 1 ≤ l + 1)
    (z : completedStalk J G x ⧸ (completedLocalIdeal J x ^ (l + 1) •
      (⊤ : Submodule (completedLocalRing J x) (completedStalk J G x)))) :
    ((modulesStalkFunctor X x).map (G.obj.map (homOfLE hkl).op)).hom
        (completedStalkQuotientEquivStalk G x l z) =
      completedStalkQuotientEquivStalk G x k
        (AdicCompletion.transitionMap (completedLocalIdeal J x) (completedStalk J G x) hmn z) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [completedStalkQuotientEquivStalk_mk,
    show AdicCompletion.transitionMap (completedLocalIdeal J x) (completedStalk J G x)
        hmn (Submodule.Quotient.mk a) = Submodule.Quotient.mk a from rfl,
    completedStalkQuotientEquivStalk_mk]
  exact congrArg (fun f => f.hom (formalStalkEquivModuleStalkLimit G x
      ((formalStalkEquivCompletedStalk G x).symm a)))
    (limit.w (G.obj ⋙ modulesStalkFunctor X x) (homOfLE hkl).op)

/-! ### The level maps along a specialization -/

/-- **The stalk of a quasi-coherent module at a generalization is the localization of the stalk
at `𝔭`**, where `𝔭` is the prime of `𝒪_{X,y'}` corresponding to the generalization under
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
private theorem isLocalizedModule_stalkSpecializesₗ (F : X.Modules) [F.IsQuasicoherent]
    {y y' : X} (h : y ⤳ y') (q : PrimeSpectrum (X.presheaf.stalk y'))
    (hqy : X.fromSpecStalk y' q = y) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F y'
    letI := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F h
    IsLocalizedModule q.asIdeal.primeCompl
      (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F h) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule F y'
  let := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F h
  let : Algebra (X.presheaf.stalk y') (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk y) q.asIdeal :=
    Chow.isLocalization_stalk_of_specializes h q hqy
  exact Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_of_eq
    (IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y) q.asIdeal)
    (Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes F h)

section Specialization

open Stacks.ModuleStalkSpecialization

variable [IsLocallyNoetherian X] {y y' : X} (G : Stacks.Coherent.CoherentAdicSystems J)
  (h : y ⤳ y') [Algebra (X.presheaf.stalk y') (X.presheaf.stalk y)]
  [Module (X.presheaf.stalk y') (formalStalk G y)]
  [IsScalarTower (X.presheaf.stalk y') (X.presheaf.stalk y) (formalStalk G y)]
  (halg : algebraMap (X.presheaf.stalk y') (X.presheaf.stalk y) =
    (X.presheaf.stalkSpecializes h).hom)

/-- The `𝒪_{X,y'}`-module structure on the stalk `ℱ_{k,y}` at the generalization, by restricting
scalars along the specialization map of local rings. -/
@[instance_reducible]
private def specializesStalkModule (k : ℕ) :
    Module (X.presheaf.stalk y') ((modulesStalkFunctor X y).obj (G.obj.obj (op k))) :=
  stalkSpecializesModule (G.obj.obj (op k)) h

omit [IsLocallyNoetherian X] [Module (X.presheaf.stalk y') (formalStalk G y)]
  [IsScalarTower (X.presheaf.stalk y') (X.presheaf.stalk y) (formalStalk G y)] in
include halg in
/-- The scalar tower `𝒪_{X,y'} → 𝒪_{X,y} → ℱ_{k,y}` for the module structure of
`Stacks.Algebraization.specializesStalkModule`. -/
private theorem specializesStalkTower (k : ℕ) :
    letI := specializesStalkModule G h k
    IsScalarTower (X.presheaf.stalk y') (X.presheaf.stalk y)
      ((modulesStalkFunctor X y).obj (G.obj.obj (op k))) :=
  let := specializesStalkModule G h k
  IsScalarTower.of_algebraMap_smul fun _ _ => by rw [halg]; rfl

include halg in
/-- The level-`(k+1)` comparison of the two completed stalks: the level quotient of `ℱ_{y'}^∧` is
`ℱ_{k,y'}`, the level quotient of `ℱ_y^∧` is `ℱ_{k,y}`, and the comparison between them is the
specialization map of the stalks of `ℱ_k`. -/
private def specializationLevelMap (k : ℕ) :
    (completedStalk J G y' ⧸ (completedLocalIdeal J y' ^ (k + 1) •
        (⊤ : Submodule (completedLocalRing J y') (completedStalk J G y')))) →ₗ[X.presheaf.stalk y']
      (formalStalk G y ⧸ (IdealSheafData.stalk J y ^ (k + 1) •
        (⊤ : Submodule (X.presheaf.stalk y) (formalStalk G y)))) :=
  letI := specializesStalkModule G h k
  haveI := specializesStalkTower G h halg k
  ((formalStalkQuotientEquivStalk G y k).restrictScalars (X.presheaf.stalk y')).symm.toLinearMap ∘ₗ
    (stalkSpecializesₗ (G.obj.obj (op k)) h) ∘ₗ
      (completedStalkQuotientEquivStalk G y' k).toLinearMap

include halg in
/-- The level map, read through the identification of the level quotient at `y` with the stalk
`ℱ_{k,y}`, is the specialization map of the stalks of `ℱ_k`. -/
private theorem formalStalkQuotientEquivStalk_specializationLevelMap (k : ℕ)
    (z : completedStalk J G y' ⧸ (completedLocalIdeal J y' ^ (k + 1) •
      (⊤ : Submodule (completedLocalRing J y') (completedStalk J G y')))) :
    formalStalkQuotientEquivStalk G y k (specializationLevelMap G h halg k z) =
      stalkSpecializesₗ (G.obj.obj (op k)) h (completedStalkQuotientEquivStalk G y' k z) :=
  (formalStalkQuotientEquivStalk G y k).apply_symm_apply _

include halg in
/-- The level maps along the specialization commute with the transition maps of the two
towers. -/
private theorem specializationLevelMap_factorPow {k l : ℕ} (hmn : k + 1 ≤ l + 1)
    (z : completedStalk J G y' ⧸ (completedLocalIdeal J y' ^ (l + 1) •
      (⊤ : Submodule (completedLocalRing J y') (completedStalk J G y')))) :
    AdicCompletion.transitionMap (IdealSheafData.stalk J y) (formalStalk G y) hmn
        (specializationLevelMap G h halg l z) =
      specializationLevelMap G h halg k
        (AdicCompletion.transitionMap (completedLocalIdeal J y') (completedStalk J G y')
          hmn z) := by
  have hkl : k ≤ l := Nat.le_of_succ_le_succ hmn
  apply (formalStalkQuotientEquivStalk G y k).injective
  rw [← formalStalkQuotientEquivStalk_factorPow G y hkl hmn,
    formalStalkQuotientEquivStalk_specializationLevelMap,
    formalStalkQuotientEquivStalk_specializationLevelMap,
    ← completedStalkQuotientEquivStalk_factorPow G y' hkl hmn]
  exact (stalkSpecializes_modulesStalkFunctor_map (G.obj.map (homOfLE hkl).op) h _).symm

include halg in
/-- **The level map along the specialization is a localization at `𝔭`.** -/
private theorem isLocalizedModule_specializationLevelMap
    (qq : PrimeSpectrum (X.presheaf.stalk y')) (hqy : X.fromSpecStalk y' qq = y) (k : ℕ) :
    IsLocalizedModule qq.asIdeal.primeCompl (specializationLevelMap G h halg k) := by
  have hcoh : _root_.SheafOfModules.IsCoherent.{u} (G.obj.obj (op k)) := G.property.1 k
  have : (G.obj.obj (op k)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have := isLocalizedModule_stalkSpecializesₗ (G.obj.obj (op k)) h qq hqy
  let := specializesStalkModule G h k
  have := specializesStalkTower G h halg k
  let := stalkModule (G.obj.obj (op k)) y'
  let : Module (X.presheaf.stalk y') ((G.obj.obj (op k)).presheaf.stalk y) :=
    stalkSpecializesModule (G.obj.obj (op k)) h
  change IsLocalizedModule qq.asIdeal.primeCompl
    (((formalStalkQuotientEquivStalk G y k).restrictScalars
        (X.presheaf.stalk y')).symm.toLinearMap ∘ₗ
      (stalkSpecializesₗ (G.obj.obj (op k)) h) ∘ₗ
        (completedStalkQuotientEquivStalk G y' k).toLinearMap)
  have : IsLocalizedModule qq.asIdeal.primeCompl
      ((stalkSpecializesₗ (G.obj.obj (op k)) h) ∘ₗ
        (completedStalkQuotientEquivStalk G y' k).toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right qq.asIdeal.primeCompl
      (stalkSpecializesₗ (G.obj.obj (op k)) h) (completedStalkQuotientEquivStalk G y' k)
  exact IsLocalizedModule.of_linearEquiv qq.asIdeal.primeCompl
    ((stalkSpecializesₗ (G.obj.obj (op k)) h) ∘ₗ
      (completedStalkQuotientEquivStalk G y' k).toLinearMap)
    ((formalStalkQuotientEquivStalk G y k).restrictScalars (X.presheaf.stalk y')).symm

end Specialization

/-! ### The level maps into the localized completed stalk -/

section Localization

variable [IsLocallyNoetherian X] {y' : X} (G : Stacks.Coherent.CoherentAdicSystems J)
  (q : PrimeSpectrum (X.presheaf.stalk y')) (hq : IdealSheafData.stalk J y' ≤ q.asIdeal)

omit [IsLocallyNoetherian X] in
/-- The `n`-th power of the adic ideal of the localization is the extension of the `n`-th power
of `ℐ𝒪_{X,y'}^∧`. -/
private theorem map_stalk_pow_eq (n : ℕ) :
    ((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
        (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal))) ^ n =
      (completedLocalIdeal J y' ^ n).map (algebraMap (completedLocalRing J y')
        (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)) := by
  rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

omit [IsLocallyNoetherian X] in
/-- The localization of the level-`n` submodule `(ℐ𝒪_{X,y'}^∧)ⁿ ℱ_{y'}^∧` is the level-`n`
submodule of the localized completed stalk. -/
private theorem localized'_pow_smul_top (n : ℕ) :
    Submodule.localized' (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)
        (completedStalkPrime J y' q hq).asIdeal.primeCompl
        (LocalizedModule.mkLinearMap (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y'))
        (completedLocalIdeal J y' ^ n • ⊤) =
      ((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
          (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal))) ^ n • ⊤ := by
  rw [Submodule.localized'_smul, Submodule.localized'_top, map_stalk_pow_eq q hq n]
  congr 1
  rw [Submodule.localized'_eq_span, Ideal.map]
  rfl

/-- The level-`n` comparison: the level-`n` quotient of the localized completed stalk is the
localization of the level-`n` quotient of the completed stalk. -/
private def localizationLevelMap (n : ℕ) :
    (completedStalk J G y' ⧸ (completedLocalIdeal J y' ^ n •
        (⊤ : Submodule (completedLocalRing J y') (completedStalk J G y')))) →ₗ[X.presheaf.stalk y']
      (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y') ⧸
        (((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
            (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal))) ^ n •
          (⊤ : Submodule (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)
            (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
              (completedStalk J G y'))))) :=
  LinearMap.restrictScalars (X.presheaf.stalk y')
    ((LinearEquiv.restrictScalars (completedLocalRing J y')
          (Submodule.quotEquivOfEq _ _ (localized'_pow_smul_top G q hq n))).toLinearMap ∘ₗ
      Submodule.toLocalizedQuotient'
        (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)
        (completedStalkPrime J y' q hq).asIdeal.primeCompl
        (LocalizedModule.mkLinearMap (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y'))
        (completedLocalIdeal J y' ^ n • ⊤))

omit [IsLocallyNoetherian X] in
/-- The level map into the localized completed stalk is induced by the localization map. -/
private theorem localizationLevelMap_mk (n : ℕ) (a : completedStalk J G y') :
    localizationLevelMap G q hq n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk
        (LocalizedModule.mkLinearMap (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y') a) := rfl

omit [IsLocallyNoetherian X] in
/-- The level maps into the localized completed stalk commute with the transition maps of the two
towers. -/
private theorem localizationLevelMap_factorPow {m n : ℕ} (hmn : m ≤ n)
    (z : completedStalk J G y' ⧸ (completedLocalIdeal J y' ^ n •
      (⊤ : Submodule (completedLocalRing J y') (completedStalk J G y')))) :
    AdicCompletion.transitionMap
        ((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
          (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)))
        (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y')) hmn (localizationLevelMap G q hq n z) =
      localizationLevelMap G q hq m
        (AdicCompletion.transitionMap (completedLocalIdeal J y') (completedStalk J G y')
          hmn z) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

omit [IsLocallyNoetherian X] in
/-- An element of `ℐ(𝒪_{X,y'}^∧)ⁿ` annihilates both level-`n` quotients. -/
private theorem smul_level_eq_zero {d : completedLocalRing J y'} (n : ℕ)
    (hd : d ∈ completedLocalIdeal J y' ^ n) :
    (∀ z : completedStalk J G y' ⧸ (completedLocalIdeal J y' ^ n •
        (⊤ : Submodule (completedLocalRing J y') (completedStalk J G y'))), d • z = 0) ∧
      (∀ x : LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y') ⧸
          (((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
              (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal))) ^ n •
            (⊤ : Submodule (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)
              (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
                (completedStalk J G y')))), d • x = 0) := by
  refine ⟨fun z => smul_quotient_eq_zero _
    (fun _ => Submodule.smul_mem_smul hd Submodule.mem_top) z, fun x => ?_⟩
  refine smul_quotient_eq_zero _ (fun m => ?_) x
  have hdc : algebraMap (completedLocalRing J y')
      (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal) d ∈
      ((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
        (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal))) ^ n := by
    rw [map_stalk_pow_eq q hq n]
    exact Ideal.mem_map_of_mem _ hd
  rw [← algebraMap_smul (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal) d m]
  exact Submodule.smul_mem_smul hdc Submodule.mem_top

omit [IsLocallyNoetherian X] in
/-- **The level-`n` quotient of the localized completed stalk is the localization, at the prime
`𝔭` of `𝒪_{X,y'}`, of the level-`n` quotient of the completed stalk.** -/
private theorem isLocalizedModule_localizationLevelMap
    (hfg : (IdealSheafData.stalk J y').FG) (n : ℕ) :
    IsLocalizedModule q.asIdeal.primeCompl (localizationLevelMap G q hq n) := by
  refine isLocalizedModule_restrictScalars_of_smul_eq (B := completedLocalRing J y')
    q.asIdeal.primeCompl (completedStalkPrime J y' q hq).asIdeal.primeCompl ?_ ?_ _
  · intro a ha hmem
    exact ha (by rw [← comap_completedStalkPrime J y' q hq]; exact hmem)
  · intro t ht
    obtain ⟨a, ha, hd⟩ := exists_notMem_sub_mem_map_pow (IdealSheafData.stalk J y') hfg hq n ht
    have he : ((IdealSheafData.stalk J y') ^ n).map
        (algebraMap (X.presheaf.stalk y') (completedLocalRing J y')) =
        completedLocalIdeal J y' ^ n := Ideal.map_pow _ _ _
    obtain ⟨h1, h2⟩ := smul_level_eq_zero G q hq n (he ▸ hd)
    exact ⟨a, ha, fun m => sub_eq_zero.mp ((sub_smul _ _ _).symm.trans (h1 m)),
      fun x => sub_eq_zero.mp ((sub_smul _ _ _).symm.trans (h2 x))⟩

end Localization

end Levels

/-! ### The completed stalk at a generalization -/

/-- **The completed stalk at a generalization is the adic completion of a localization of the
completed stalk.** -/
public theorem nonempty_linearEquiv_completedStalk_of_specializes
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (G : Stacks.Coherent.CoherentAdicSystems J) {y y' : X} (h : y ⤳ y')
    (q : PrimeSpectrum (X.presheaf.stalk y')) (hqy : X.fromSpecStalk y' q = y)
    (hq : IdealSheafData.stalk J y' ≤ q.asIdeal) :
    letI : Algebra (X.presheaf.stalk y') (X.presheaf.stalk y) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    letI : Module (X.presheaf.stalk y') (formalStalk G y) :=
      Module.compHom _ (X.presheaf.stalkSpecializes h).hom
    haveI : IsScalarTower (X.presheaf.stalk y') (X.presheaf.stalk y) (formalStalk G y) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Nonempty (completedStalk J G y ≃ₗ[X.presheaf.stalk y']
      AdicCompletion
        ((IdealSheafData.stalk J y').map
          (algebraMap (X.presheaf.stalk y')
            (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)))
        (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y'))) := by
  let : Algebra (X.presheaf.stalk y') (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let : Module (X.presheaf.stalk y') (formalStalk G y) :=
    Module.compHom _ (X.presheaf.stalkSpecializes h).hom
  have : IsScalarTower (X.presheaf.stalk y') (X.presheaf.stalk y) (formalStalk G y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have halg : algebraMap (X.presheaf.stalk y') (X.presheaf.stalk y) =
      (X.presheaf.stalkSpecializes h).hom := rfl
  have hfg : (IdealSheafData.stalk J y').FG := Ideal.fg_of_isNoetherianRing _
  have : Subsingleton (formalStalk G y ⧸ (IdealSheafData.stalk J y ^ 0 •
      (⊤ : Submodule (X.presheaf.stalk y) (formalStalk G y)))) :=
    subsingleton_quotient_pow_zero _
  have : Subsingleton (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
      (completedStalk J G y') ⧸
      (((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
          (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal))) ^ 0 •
        (⊤ : Submodule (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)
          (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
            (completedStalk J G y'))))) :=
    subsingleton_quotient_pow_zero _
  have : ∀ k, IsLocalizedModule q.asIdeal.primeCompl (specializationLevelMap G h halg k) :=
    isLocalizedModule_specializationLevelMap G h halg q hqy
  have : ∀ k, IsLocalizedModule q.asIdeal.primeCompl (localizationLevelMap G q hq (k + 1)) :=
    fun k => isLocalizedModule_localizationLevelMap G q hq hfg (k + 1)
  let E : ∀ k : ℕ, (formalStalk G y ⧸ (IdealSheafData.stalk J y ^ (k + 1) •
        (⊤ : Submodule (X.presheaf.stalk y) (formalStalk G y)))) ≃ₗ[X.presheaf.stalk y']
      (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y') ⧸
        (((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
            (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal))) ^ (k + 1) •
          (⊤ : Submodule (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)
            (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
              (completedStalk J G y'))))) := fun k => by
    exact IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
      (specializationLevelMap G h halg k) (localizationLevelMap G q hq (k + 1))
  have hE : ∀ (k : ℕ) (z : completedStalk J G y' ⧸ (completedLocalIdeal J y' ^ (k + 1) •
        (⊤ : Submodule (completedLocalRing J y') (completedStalk J G y')))),
      E k (specializationLevelMap G h halg k z) = localizationLevelMap G q hq (k + 1) z := by
    intro k z
    exact IsLocalizedModule.linearEquiv_apply q.asIdeal.primeCompl
      (specializationLevelMap G h halg k) (localizationLevelMap G q hq (k + 1)) z
  let e : ∀ n : ℕ, (formalStalk G y ⧸ (IdealSheafData.stalk J y ^ n •
        (⊤ : Submodule (X.presheaf.stalk y) (formalStalk G y)))) ≃ₗ[X.presheaf.stalk y']
      (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
          (completedStalk J G y') ⧸
        (((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
            (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal))) ^ n •
          (⊤ : Submodule (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)
            (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
              (completedStalk J G y'))))) := fun n =>
    Nat.casesOn n linearEquivOfSubsingleton E
  refine ⟨adicCompletionLinearEquivOfLevelEquiv _ _ e ?_⟩
  intro m n hmn x
  rcases m with _ | k
  · exact Subsingleton.elim _ _
  rcases n with _ | l
  · exact absurd hmn (by omega)
  rw [show e (l + 1) = E l from rfl, show e (k + 1) = E k from rfl]
  have key : (LinearMap.restrictScalars (X.presheaf.stalk y')
          (AdicCompletion.transitionMap
            ((IdealSheafData.stalk J y').map (algebraMap (X.presheaf.stalk y')
              (Localization.AtPrime (completedStalkPrime J y' q hq).asIdeal)))
            (LocalizedModule (completedStalkPrime J y' q hq).asIdeal.primeCompl
              (completedStalk J G y')) hmn)).comp (E l).toLinearMap =
        (E k).toLinearMap.comp (LinearMap.restrictScalars (X.presheaf.stalk y')
          (AdicCompletion.transitionMap (IdealSheafData.stalk J y) (formalStalk G y) hmn)) := by
    refine IsLocalizedModule.linearMap_ext q.asIdeal.primeCompl
      (specializationLevelMap G h halg l) (localizationLevelMap G q hq (k + 1)) ?_
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [hE l z, localizationLevelMap_factorPow G q hq hmn,
      specializationLevelMap_factorPow G h halg hmn z, hE k]
  exact DFunLike.congr_fun key x


end Stacks.Algebraization

end
