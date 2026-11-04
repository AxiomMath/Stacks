module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomology

/-!
# `μ_n` is the constant sheaf `ℤ/n` once a primitive `n`-th root of unity is chosen

Let `X` be a scheme over a field `k` and let `ζ ∈ k` be a primitive `n`-th root of unity,
`n ≠ 0`. The map `ℤ/n → μ_n`, `m ↦ ζ^m`, from the constant sheaf to the sheaf of `n`-th roots of
unity on `X_étale` is an isomorphism. Over a separably closed field in which `n` is invertible a
primitive root exists, so `μ_n ≅ ℤ/n` there; the isomorphism depends on the choice of `ζ`.

## Main definitions

* `Stacks.Kummer.rootsOfUnityConstantHom`: `ℤ/n ⟶ μ_n`, `m ↦ ζ^m`.
* `Stacks.Kummer.rootsOfUnityConstantIso`: the resulting isomorphism.

## Main results

* `Stacks.Kummer.isIso_rootsOfUnityConstantHom`: the map is an isomorphism.
* `Stacks.Kummer.nonempty_rootsOfUnity_iso_constant`: over a separably closed field with `n`
  invertible, `μ_n ≅ ℤ/n` on `X_étale`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Kummer

/-! ### The idempotents attached to an `n`-th root of unity -/

section Ring

open Polynomial

variable {k : Type u} [Field k] [DecidableEq k] {n : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ n)
  (hn : n ≠ 0) {R : Type*} [CommRing R] [Algebra k R] (x : R) (hx : x ^ n = 1)

/-- The Lagrange idempotent of `x` at the root of unity `ρ`: it is `1` where `x = ρ` and `0`
where `x` is another root of unity. -/
def rootIdempotent (n : ℕ) (ρ : k) : R :=
  aeval x (Lagrange.basis (nthRootsFinset n (1 : k)) id ρ)

include hζ hn in
/-- The Lagrange idempotents of `x` at the `n`-th roots of unity sum to `1`. -/
theorem sum_rootIdempotent :
    ∑ ρ ∈ nthRootsFinset n (1 : k), rootIdempotent x n ρ = 1 := by
  simp only [rootIdempotent]
  rw [← map_sum (aeval x), Lagrange.sum_basis (Set.injOn_id _)
    ⟨1, (mem_nthRootsFinset (Nat.pos_of_ne_zero hn) (1 : k)).2 (one_pow n)⟩, map_one]

include hζ hn hx in
/-- If `x ^ n = 1`, then `(x - ρ) e_ρ = 0` for the Lagrange idempotent `e_ρ` of `x` at an `n`-th
root of unity `ρ`. -/
theorem sub_mul_rootIdempotent {ρ : k} (hρ : ρ ∈ nthRootsFinset n (1 : k)) :
    (x - algebraMap k R ρ) * rootIdempotent x n ρ = 0 := by
  have h : (X - C ρ) * Lagrange.basis (nthRootsFinset n (1 : k)) id ρ =
      C (Lagrange.nodalWeight (nthRootsFinset n (1 : k)) id ρ) * (X ^ n - 1) := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hρ, X_pow_sub_one_eq_prod
      (Nat.pos_of_ne_zero hn) hζ, ← Lagrange.nodal_eq, mul_left_comm, id,
      EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero ρ)
        (Lagrange.X_sub_C_dvd_nodal id hρ)]
    rfl
  simpa only [rootIdempotent, map_mul, map_sub, aeval_X, aeval_C, map_pow, map_one, hx, sub_self,
    mul_zero] using congrArg (aeval x) h

end Ring

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ} {ζ : k}
  (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)

/-- The structure map `k → Γ(U, 𝒪_U)` of an étale `X`-scheme `U`. -/
def structMap (U : X.Etale) : k →+* Γ(U.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ U.hom.appTop).hom

/-- The structure maps of étale `X`-schemes are compatible with a morphism `V ⟶ U` over `X`. -/
theorem structMap_comp {U V : X.Etale} (g : V ⟶ U) :
    g.left.appTop.hom.comp (structMap f U) = structMap f V := by
  rw [structMap, structMap, ← CommRingCat.hom_comp]
  congr 1
  rw [Category.assoc, Category.assoc, ← Scheme.Hom.comp_appTop]
  congr 3
  exact MorphismProperty.Over.w g

/-- The image of the primitive root `ζ` in the invertible functions on an étale `X`-scheme. -/
def rootOn (U : X.Etale) : (Γ(U.left, ⊤))ˣ :=
  Units.map (structMap f U).toMonoidHom (Units.mk0 ζ (hζ.ne_zero hn))

/-- The image of `ζ` on an étale `X`-scheme is an `n`-th root of unity. -/
theorem rootOn_pow (U : X.Etale) : rootOn f hζ hn U ^ n = 1 := by
  rw [rootOn, ← map_pow]
  have : Units.mk0 ζ (hζ.ne_zero hn) ^ n = 1 := Units.ext (by simpa using hζ.pow_eq_one)
  rw [this, map_one]

/-- The image of `ζ` is compatible with pullback along a morphism `V ⟶ U` of étale
`X`-schemes. -/
theorem map_rootOn {U V : X.Etale} (g : V ⟶ U) :
    Units.map g.left.appTop.hom.toMonoidHom (rootOn f hζ hn U) = rootOn f hζ hn V := by
  rw [rootOn, rootOn, ← structMap_comp f g]
  rfl

/-- `m ↦ ζ^m`, from `ℤ/n` to the sections of `𝐆_m` over `U`. -/
def rootHom (U : X.Etale) :
    ZMod n →+ ToType ((multiplicativeSheaf.{u, 0} X).obj.obj (op U)) :=
  ZMod.lift n ⟨zmultiplesHom _ (ofUnit.{u, 0} (rootOn f hζ hn U)), by
    change (n : ℤ) • ofUnit.{u, 0} (rootOn f hζ hn U) = 0
    rw [natCast_zsmul]
    change ULift.up (n • Additive.ofMul (rootOn f hζ hn U)) = ULift.up (Additive.ofMul 1)
    rw [← ofMul_pow, rootOn_pow]⟩

/-- `rootHom` sends the class of an integer `z` to `z • ζ`, written additively. -/
theorem rootHom_intCast (U : X.Etale) (z : ℤ) :
    rootHom f hζ hn U z = z • ofUnit.{u, 0} (rootOn f hζ hn U) :=
  ZMod.lift_coe _ _ z

/-- In the additive notation of the sections of `𝐆_m`, `z • x` is the unit `x ^ z`. -/
theorem zsmul_ofUnit (U : X.Etale) (z : ℤ) (x : (Γ(U.left, ⊤))ˣ) :
    z • ofUnit.{u, 0} x = ofUnit.{u, 0} (x ^ z) := by
  show ULift.up (z • Additive.ofMul x) = ULift.up (Additive.ofMul (x ^ z))
  rw [ofMul_zpow]

/-- On a nonempty étale `X`-scheme, `ζ^m = 1` if and only if `m = 0` in `ℤ/n`. -/
theorem rootHom_eq_zero_iff (U : X.Etale) [Nonempty U.left] (m : ZMod n) :
    rootHom f hζ hn U m = 0 ↔ m = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
  rw [rootHom_intCast, zsmul_ofUnit, ← ofUnit_one, ofUnit_injective.eq_iff,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ← hζ.zpow_eq_one_iff_dvd]
  have : Nontrivial Γ(U.left, ⊤) := by
    obtain ⟨p⟩ := ‹Nonempty U.left›
    have : Nonempty (⊤ : U.left.Opens) := ⟨⟨p, trivial⟩⟩
    infer_instance
  rw [rootOn, ← map_zpow, Units.ext_iff, Units.coe_map, Units.val_one]
  exact ⟨fun h ↦ (structMap f U).injective (by simpa using h), fun h ↦ by simp [h]⟩

/-- The presheaf map from the constant presheaf `ℤ/n` to `𝐆_m`, `m ↦ ζ^m`. -/
def rootPresheafHom :
    (Functor.const (X.Etale)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ⟶
      (multiplicativeSheaf.{u, 0} X).obj where
  app U := AddCommGrpCat.ofHom ((rootHom f hζ hn U.unop).comp
    (AddEquiv.ulift.{0, u + 1} (α := ZMod n)).toAddMonoidHom)
  naturality U V g := by
    ext m
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective m.down
    change rootHom f hζ hn V.unop m.down =
      (multiplicativeSheaf.{u, 0} X).obj.map g.unop.op (rootHom f hζ hn U.unop m.down)
    rw [← hz, rootHom_intCast, rootHom_intCast, map_zsmul, map_ofUnit]
    exact congrArg (z • ofUnit.{u, 0} ·) (map_rootOn f hζ hn g.unop).symm

/-- `ℤ/n ⟶ 𝐆_m`, `m ↦ ζ^m`, as a map of sheaves out of the constant sheaf `ℤ/n`. -/
def rootSheafHom :
    Stacks.EtaleCohomology.etaleConstantSheaf X (ZMod n) ⟶ multiplicativeSheaf.{u, 0} X :=
  ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _
    (multiplicativeSheaf.{u, 0} X)).symm (rootPresheafHom f hζ hn)

/-- `rootSheafHom` restricted along the sheafification unit is `rootPresheafHom`. -/
@[reassoc]
theorem toSheafify_rootSheafHom :
    toSheafify X.smallEtaleTopology _ ≫ (rootSheafHom f hζ hn).hom = rootPresheafHom f hζ hn :=
  toSheafify_sheafifyLift _ _ (multiplicativeSheaf.{u, 0} X).property

/-- The `n`-th power map kills the image of `rootPresheafHom`. -/
theorem rootPresheafHom_comp_powMap :
    rootPresheafHom f hζ hn ≫ (powMap.{u, 0} X n).hom = 0 := by
  ext U m
  show (powMap.{u, 0} X n).hom.app U (rootHom f hζ hn U.unop m.down) = 0
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective m.down
  rw [← hz, rootHom_intCast, zsmul_ofUnit, powMap_app_ofUnit, ← zpow_natCast, ← zpow_mul,
    mul_comm, zpow_mul, zpow_natCast, rootOn_pow, one_zpow]
  rfl

/-- The `n`-th power map kills the image of `rootSheafHom`. -/
theorem rootSheafHom_comp_powMap : rootSheafHom f hζ hn ≫ powMap.{u, 0} X n = 0 := by
  ext : 1
  refine sheafify_hom_ext _ _ _ (multiplicativeSheaf.{u, 0} X).property ?_
  show toSheafify X.smallEtaleTopology _ ≫ (rootSheafHom f hζ hn).hom ≫
    (powMap.{u, 0} X n).hom = toSheafify X.smallEtaleTopology _ ≫ 0
  exact (toSheafify_rootSheafHom_assoc f hζ hn _).trans
    ((rootPresheafHom_comp_powMap f hζ hn).trans comp_zero.symm)

/-- **`ℤ/n ⟶ μ_n`, `m ↦ ζ^m`.** -/
def rootsOfUnityConstantHom :
    Stacks.EtaleCohomology.etaleConstantSheaf X (ZMod n) ⟶ rootsOfUnitySheaf.{u, 0} X n :=
  kernel.lift _ (rootSheafHom f hζ hn) (rootSheafHom_comp_powMap f hζ hn)

/-- `rootsOfUnityConstantHom` followed by the inclusion `μ_n ⟶ 𝐆_m` is `rootSheafHom`. -/
theorem rootsOfUnityConstantHom_comp_ι :
    rootsOfUnityConstantHom f hζ hn ≫ rootsOfUnityι.{u, 0} X n = rootSheafHom f hζ hn :=
  kernel.lift_ι _ _ _

/-- Every sieve on an étale `X`-scheme with empty underlying scheme is covering. -/
theorem mem_smallEtaleTopology_of_isEmpty (U : X.Etale) (hU : IsEmpty U.left) (S : Sieve U) :
    S ∈ X.smallEtaleTopology U := by
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff (Z := fun i : PEmpty.{u + 2} => U)
      (fun i => i.elim)).2 (Set.eq_univ_of_forall fun p => hU.elim p))
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨⟨⟩⟩

/-- The presheaf map `rootPresheafHom` is locally injective. -/
instance isLocallyInjective_rootPresheafHom :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (rootPresheafHom f hζ hn) where
  equalizerSieve_mem {U} a b h := by
    rcases isEmpty_or_nonempty U.unop.left with hU | hU
    · exact mem_smallEtaleTopology_of_isEmpty U.unop hU _
    · have hab : a = b := by
        have h' : rootHom f hζ hn U.unop a.down = rootHom f hζ hn U.unop b.down := h
        rw [← sub_eq_zero, ← map_sub, rootHom_eq_zero_iff, sub_eq_zero] at h'
        exact ULift.ext _ _ h'
      rw [hab, Presheaf.equalizerSieve_self_eq_top]
      exact X.smallEtaleTopology.top_mem _

omit [Field k] in
private lemma isLocallyInjective_of_fac {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) (f₃ : F₁ ⟶ F₃)
    (fac : f₁ ≫ f₂ = f₃) (h₃ : Presheaf.IsLocallyInjective J f₃)
    (h₁ : Presheaf.IsLocallySurjective J f₁) : Presheaf.IsLocallyInjective J f₂ :=
  Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J f₃ fac

/-- The sheaf map `rootSheafHom` is locally injective. -/
instance isLocallyInjective_rootSheafHom :
    Sheaf.IsLocallyInjective (rootSheafHom f hζ hn) := by
  have := Scheme.wEqualsLocallyBijective_smallEtaleTopology.{u, 0} X
  exact isLocallyInjective_of_fac _ _ _ (toSheafify_rootSheafHom f hζ hn) inferInstance
    ((X.smallEtaleTopology.W_toSheafify _).isLocallySurjective)

/-- `rootsOfUnityConstantHom` is a monomorphism. -/
instance mono_rootsOfUnityConstantHom : Mono (rootsOfUnityConstantHom f hζ hn) := by
  have : Sheaf.IsLocallyInjective (rootsOfUnityConstantHom f hζ hn) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_fac X.smallEtaleTopology
      (congrArg InducedCategory.Hom.hom (rootsOfUnityConstantHom_comp_ι f hζ hn))
  exact Sheaf.mono_of_isLocallyInjective _

omit [Field k] in
/-- The inclusion `μ_n ⟶ 𝐆_m` is injective on sections. -/
theorem rootsOfUnityι_app_op_injective (U : (X.Etale)ᵒᵖ) :
    Function.Injective ((rootsOfUnityι.{u, 0} X n).hom.app U) := by
  have : Mono (rootsOfUnityι.{u, 0} X n).hom :=
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_mono _
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

omit [Field k] in
/-- A section restricted to its basic open set becomes a unit on the open subscheme. -/
theorem isUnit_ι_appTop_basicOpen (Y : Scheme.{u}) (e : Γ(Y, ⊤)) :
    IsUnit ((Y.basicOpen e).ι.appTop.hom e) := by
  rw [Scheme.Opens.ι_appTop]
  have h : (Y.basicOpen e).ι ''ᵁ ⊤ ≤ Y.basicOpen e := by rw [Scheme.Opens.ι_image_top]
  have hfac : (homOfLE (x := (Y.basicOpen e).ι ''ᵁ ⊤) le_top).op =
      (homOfLE (Y.basicOpen_le e)).op ≫ (homOfLE h).op := rfl
  rw [hfac, Functor.map_comp]
  exact (Y.toRingedSpace.isUnit_res_basicOpen e).map (Y.presheaf.map (homOfLE h).op).hom

/-- `rootsOfUnityConstantHom_comp_ι` on the underlying presheaves. -/
theorem rootsOfUnityConstantHom_hom_comp_ι :
    (rootsOfUnityConstantHom f hζ hn).hom ≫ (rootsOfUnityι.{u, 0} X n).hom =
      (rootSheafHom f hζ hn).hom :=
  congrArg InducedCategory.Hom.hom (rootsOfUnityConstantHom_comp_ι f hζ hn)

/-- On the image under the sheafification unit of a section `m` of the constant presheaf `ℤ/n`,
`rootsOfUnityConstantHom` followed by the inclusion `μ_n ⟶ 𝐆_m` is `rootHom` at `m`. -/
theorem ι_rootsOfUnityConstantHom_toSheafify_apply (U : (X.Etale)ᵒᵖ)
    (m : ULift.{u + 1} (ZMod n)) :
    (rootsOfUnityι.{u, 0} X n).hom.app U ((rootsOfUnityConstantHom f hζ hn).hom.app U
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1, 0} (ZMod n))))).app U m)) =
      rootHom f hζ hn U.unop m.down := by
  let y := (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1, 0} (ZMod n))))).app U m
  have e1 : (rootsOfUnityι.{u, 0} X n).hom.app U ((rootsOfUnityConstantHom f hζ hn).hom.app U y) =
      (rootSheafHom f hζ hn).hom.app U y :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (rootsOfUnityConstantHom_hom_comp_ι f hζ hn) U) y
  have e2 : (rootSheafHom f hζ hn).hom.app U y = rootHom f hζ hn U.unop m.down :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_rootSheafHom f hζ hn) U) m
  exact e1.trans e2

variable [DecidableEq k]

omit [DecidableEq k] in
/-- Every section of `μ_n` lies, locally, in the image of `ℤ/n ⟶ μ_n`. -/
theorem imageSieve_rootsOfUnityConstantHom_mem (U : X.Etale)
    (s : ToType ((rootsOfUnitySheaf.{u, 0} X n).obj.obj (op U))) :
    Presheaf.imageSieve (toSheafify X.smallEtaleTopology _ ≫
      (rootsOfUnityConstantHom f hζ hn).hom) s ∈ X.smallEtaleTopology U := by
  classical
  have : NeZero n := ⟨hn⟩
  obtain ⟨x, hx⟩ := ofUnit_surjective.{u, 0} ((rootsOfUnityι.{u, 0} X n).hom.app (op U) s)
  have hxn : x ^ n = 1 := pow_eq_one_of_rootsOfUnitySheaf X n U s x hx.symm
  let : Algebra k Γ(U.left, ⊤) := (structMap f U).toAlgebra
  have hxn' : (x : Γ(U.left, ⊤)) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hxn, Units.val_one]
  let S := Polynomial.nthRootsFinset n (1 : k)
  let e : S → Γ(U.left, ⊤) := fun ρ => rootIdempotent (x : Γ(U.left, ⊤)) n ρ.1
  let Z : S → X.Etale := fun ρ => Scheme.Etale.mk ((U.left.basicOpen (e ρ)).ι ≫ U.hom)
  let g : (ρ : S) → Z ρ ⟶ U := fun ρ => MorphismProperty.Over.homMk (U.left.basicOpen (e ρ)).ι rfl
  have hcov : Sieve.ofArrows Z g ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    have hspan : Ideal.span (Set.range e) = ⊤ := by
      rw [Ideal.eq_top_iff_one, ← sum_rootIdempotent hζ hn (x : Γ(U.left, ⊤)),
        ← Finset.sum_coe_sort]
      exact Ideal.sum_mem _ fun ρ _ => Ideal.subset_span ⟨ρ, rfl⟩
    have h := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (X := U.left) ⊤ _ hspan
    refine Set.eq_univ_of_forall fun p => ?_
    have hp : p ∈ (⨆ i ∈ Set.range e, U.left.basicOpen i) := by rw [h]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup, Set.mem_range, exists_prop] at hp
    obtain ⟨_, ⟨ρ, rfl⟩, hρ⟩ := hp
    exact Set.mem_iUnion.2 ⟨ρ, by
      show p ∈ Set.range (U.left.basicOpen (e ρ)).ι
      rw [Scheme.Opens.range_ι]
      exact hρ⟩
  refine X.smallEtaleTopology.superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨ρ⟩
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one
    ((Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) (1 : k)).1 ρ.2)
  refine ⟨ULift.up (i : ZMod n), rootsOfUnityι_app_op_injective (op (Z ρ)) ?_⟩
  show _ = (rootsOfUnityι.{u, 0} X n).hom.app (op (Z ρ))
    ((rootsOfUnitySheaf.{u, 0} X n).obj.map (g ρ).op s)
  refine (ι_rootsOfUnityConstantHom_toSheafify_apply f hζ hn (op (Z ρ)) _).trans ?_
  rw [NatTrans.naturality_apply, ← hx, map_ofUnit]
  show rootHom f hζ hn (Z ρ) (i : ZMod n) = _
  rw [← Int.cast_natCast, rootHom_intCast, zsmul_ofUnit]
  congr 1
  have hunit := isUnit_ι_appTop_basicOpen U.left (e ρ)
  have hzero := sub_mul_rootIdempotent hζ hn (x : Γ(U.left, ⊤)) hxn' ρ.2
  have himg := congrArg (U.left.basicOpen (e ρ)).ι.appTop.hom hzero
  rw [map_mul, map_zero, map_sub] at himg
  have hxρ := sub_eq_zero.1 (hunit.mul_left_eq_zero.1 himg)
  apply Units.ext
  rw [Units.coe_map, zpow_natCast, Units.val_pow_eq_pow_val, rootOn, Units.coe_map,
    Units.val_mk0]
  show (structMap f (Z ρ) ζ) ^ i = _
  rw [← map_pow, hi, ← structMap_comp f (g ρ)]
  exact hxρ.symm

omit [DecidableEq k] in
/-- **`m ↦ ζ^m` is an isomorphism `ℤ/n ≅ μ_n` of sheaves on `X_étale`** for a primitive `n`-th
root of unity `ζ` of the base field `k`. -/
theorem isIso_rootsOfUnityConstantHom : IsIso (rootsOfUnityConstantHom f hζ hn) := by
  classical
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology _ ≫ (rootsOfUnityConstantHom f hζ hn).hom) :=
    ⟨fun s => imageSieve_rootsOfUnityConstantHom_mem f hζ hn _ s⟩
  have : Sheaf.IsLocallySurjective (rootsOfUnityConstantHom f hζ hn) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology _) (rootsOfUnityConstantHom f hζ hn).hom
  have : Epi (rootsOfUnityConstantHom f hζ hn) := Sheaf.epi_of_isLocallySurjective _
  exact isIso_of_mono_of_epi _

/-- **`μ_n ≅ ℤ/n` on the small étale site of a scheme over a field with a primitive `n`-th root of
unity `ζ`**, the isomorphism `ℤ/n ⟶ μ_n` sending `m` to `ζ^m`. -/
def rootsOfUnityConstantIso :
    Stacks.EtaleCohomology.etaleConstantSheaf X (ZMod n) ≅ rootsOfUnitySheaf.{u, 0} X n :=
  haveI := isIso_rootsOfUnityConstantHom f hζ hn
  asIso (rootsOfUnityConstantHom f hζ hn)

omit hζ [DecidableEq k] in
include f hn in
/-- **Over a separably closed field in which `n ≠ 0` is invertible, `μ_n ≅ ℤ/n` on the small
étale site of any scheme over it.** The isomorphism depends on the choice of a primitive `n`-th
root of unity, which exists since `k` is separably closed. -/
theorem nonempty_rootsOfUnity_iso_constant [IsSepClosed k] (hnk : (n : k) ≠ 0) :
    Nonempty (Stacks.EtaleCohomology.etaleConstantSheaf X (ZMod n) ≅
      rootsOfUnitySheaf.{u, 0} X n) := by
  have : NeZero (n : k) := ⟨hnk⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  exact ⟨rootsOfUnityConstantIso f hζ hn⟩

end Stacks.Kummer

end
