module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant

/-!
# `μ_n` is the constant sheaf `ℤ/n` over a ring with separated `n`-th roots of unity

Let `R` be a commutative ring, `n ≠ 0` invertible in `R`, and `ζ ∈ R` with `ζ ^ n = 1` such that
`1 - ζ ^ i` is a unit of `R` for `0 < i < n`. For every scheme `X` over `R` the map
`ℤ/n ⟶ μ_n`, `m ↦ ζ^m`, of sheaves on `X_étale` is an isomorphism. The hypothesis on `ζ` holds
for instance when `R` is a henselian local ring with separably closed residue field in which `n`
is invertible.

## Main definitions

* `Stacks.Kummer.OverRing.rootsOfUnityConstantHom`: `ℤ/n ⟶ μ_n`, `m ↦ ζ^m`.
* `Stacks.Kummer.OverRing.rootsOfUnityConstantIso`: the resulting isomorphism.

## Main results

* `Stacks.Kummer.OverRing.exists_pow_eq_of_isLocalRing`: in a local ring in which `n` is
  invertible and the `1 - ζ ^ i` are units, every `n`-th root of unity is a power of `ζ`.
* `Stacks.Kummer.OverRing.isIso_rootsOfUnityConstantHom`: `ℤ/n ⟶ μ_n`, `m ↦ ζ^m`, is an
  isomorphism.
* `Stacks.Kummer.OverRing.exists_separated_root_of_henselianLocalRing`: a henselian local ring
  with separably closed residue field in which `n` is invertible has such a `ζ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Kummer.OverRing

/-! ### Roots of unity in a local ring -/

/-- If `(n : A)` is a unit in a nontrivial ring then `n ≠ 0`. -/
private theorem ne_zero_of_isUnit_natCast {A : Type*} [CommRing A] [Nontrivial A] {n : ℕ}
    (hn : IsUnit (n : A)) : n ≠ 0 := by
  rintro rfl
  simp at hn

/-- If `(n : A)` is a unit in a local ring then `n` is nonzero in the residue field. -/
private theorem natCast_residueField_ne_zero {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ}
    (hn : IsUnit (n : A)) : (n : IsLocalRing.ResidueField A) ≠ 0 := by
  simpa using (hn.map (IsLocalRing.residue A)).ne_zero

/-- A ring hom to a nontrivial ring sending `a` to `1` shows that `1 - a` is not a unit. -/
private theorem not_isUnit_one_sub_of_map_eq_one {A B : Type*} [CommRing A] [CommRing B]
    [Nontrivial B] (φ : A →+* B) {a : A} (ha : φ a = 1) : ¬ IsUnit (1 - a) := fun hu ↦ by
  have := hu.map φ
  rw [map_sub, map_one, ha, sub_self] at this
  exact not_isUnit_zero this

/-- **In a local ring in which `n` is invertible and the `1 - ζ ^ i` (`0 < i < n`) are units, every
`n`-th root of unity is a power of `ζ`.** -/
theorem exists_pow_eq_of_isLocalRing {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ}
    (hn : IsUnit (n : A)) {ζ : A} (hζ : ζ ^ n = 1)
    (hsep : ∀ i : ℕ, 0 < i → i < n → IsUnit (1 - ζ ^ i)) {x : A} (hx : x ^ n = 1) :
    ∃ i < n, ζ ^ i = x := by
  have hn0 := ne_zero_of_isUnit_natCast hn
  have : NeZero n := ⟨hn0⟩
  let r := IsLocalRing.residue A
  have hprim : IsPrimitiveRoot (r ζ) n := by
    refine IsPrimitiveRoot.mk_of_lt _ (Nat.pos_of_ne_zero hn0) (by rw [← map_pow, hζ, map_one])
      fun l hl0 hln h ↦ ?_
    exact not_isUnit_one_sub_of_map_eq_one r (by rwa [map_pow]) (hsep l hl0 hln)
  obtain ⟨i, hi, hix⟩ := hprim.eq_pow_of_pow_eq_one (by rw [← map_pow, hx, map_one] : r x ^ n = 1)
  refine ⟨i, hi, ?_⟩
  have hζu : IsUnit ζ := IsUnit.of_pow_eq_one hζ hn0
  set m := x * (hζu.unit⁻¹ : Aˣ) ^ i - 1 with hm
  have hxm : x = ζ ^ i * (1 + m) := by
    rw [hm, add_sub_cancel, mul_comm x, ← mul_assoc, ← mul_pow, IsUnit.mul_val_inv, one_pow,
      one_mul]
  have hmr : r m = 0 := by
    rw [hm, map_sub, map_mul, map_pow, map_one, ← hix]
    have : r ζ * r ((hζu.unit⁻¹ : Aˣ) : A) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    rw [← mul_pow, this, one_pow, sub_self]
  have hpow : (1 + m) ^ n = 1 := by
    rwa [hxm, mul_pow, ← pow_mul, mul_comm i, pow_mul, hζ, one_pow, one_mul] at hx
  have hmr' : IsLocalRing.residue A m = 0 := hmr
  have hgeom : IsUnit (∑ k ∈ Finset.range n, (1 + m) ^ k) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simpa [hmr'] using natCast_residueField_ne_zero hn
  have hzero := geom_sum_mul (1 + m) n
  rw [hpow, sub_self, add_sub_cancel_left] at hzero
  rw [hxm, hgeom.mul_right_eq_zero.1 hzero, add_zero, mul_one]

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
  (hζ : ζ ^ n = 1) (hn : n ≠ 0)

/-- The structure map `R → Γ(U, 𝒪_U)` of an étale `X`-scheme `U`. -/
def structMap (U : X.Etale) : R →+* Γ(U.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ U.hom.appTop).hom

/-- The structure maps are compatible with restriction along a morphism of étale `X`-schemes. -/
theorem structMap_comp
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    {U V : X.Etale} (g : V ⟶ U) :
    g.left.appTop.hom.comp (structMap f U) = structMap f V := by
  rw [structMap, structMap, ← CommRingCat.hom_comp]
  congr 1
  rw [Category.assoc, Category.assoc, ← Scheme.Hom.comp_appTop]
  congr 3
  exact MorphismProperty.Over.w g

/-- `ζ` as a unit of `R`. -/
def rootUnit : Rˣ := (IsUnit.of_pow_eq_one hζ hn).unit

/-- The image of `ζ` in the invertible functions on an étale `X`-scheme. -/
def rootOn (U : X.Etale) : (Γ(U.left, ⊤))ˣ :=
  Units.map (structMap f U).toMonoidHom (rootUnit hζ hn)

/-- The invertible function `rootOn f hζ hn U` is the image of `ζ` under `structMap f U`. -/
theorem coe_rootOn (U : X.Etale) : (rootOn f hζ hn U : Γ(U.left, ⊤)) = structMap f U ζ := rfl

/-- The image of `ζ` on an étale `X`-scheme is an `n`-th root of unity. -/
theorem rootOn_pow
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) (U : X.Etale) : rootOn f hζ hn U ^ n = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_rootOn, ← map_pow, hζ, map_one, Units.val_one]

/-- Restriction along a morphism of étale `X`-schemes carries the image of `ζ` to the image
of `ζ`. -/
theorem map_rootOn
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) {U V : X.Etale} (g : V ⟶ U) :
    Units.map g.left.appTop.hom.toMonoidHom (rootOn f hζ hn U) = rootOn f hζ hn V := by
  rw [rootOn, rootOn, ← structMap_comp f g]
  rfl

/-- `m ↦ ζ^m`, from `ℤ/n` to the sections of `𝐆_m` over `U`. -/
def rootHom
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) (U : X.Etale) :
    ZMod n →+ ToType ((multiplicativeSheaf.{u, 0} X).obj.obj (op U)) :=
  ZMod.lift n ⟨zmultiplesHom _ (ofUnit.{u, 0} (rootOn f hζ hn U)), by
    change (n : ℤ) • ofUnit.{u, 0} (rootOn f hζ hn U) = 0
    rw [natCast_zsmul]
    change ULift.up (n • Additive.ofMul (rootOn f hζ hn U)) = ULift.up (Additive.ofMul 1)
    rw [← ofMul_pow, rootOn_pow]⟩

/-- `rootHom` sends the class of an integer `z` to `ζ^z`, written additively. -/
theorem rootHom_intCast
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) (U : X.Etale) (z : ℤ) :
    rootHom f hζ hn U z = z • ofUnit.{u, 0} (rootOn f hζ hn U) :=
  ZMod.lift_coe _ _ z

variable (hsep : ∀ i : ℕ, 0 < i → i < n → IsUnit (1 - ζ ^ i))

/-- On a nonempty étale `X`-scheme, `ζ^m = 1` exactly when `m = 0` in `ℤ/n`. -/
theorem rootHom_eq_zero_iff
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0)
    (hsep : ∀ i : ℕ, 0 < i → i < n → IsUnit (1 - ζ ^ i)) (U : X.Etale) [Nonempty U.left]
    (m : ZMod n) :
    rootHom f hζ hn U m = 0 ↔ m = 0 := by
  have : NeZero n := ⟨hn⟩
  have : Nontrivial Γ(U.left, ⊤) := by
    obtain ⟨p⟩ := ‹Nonempty U.left›
    have : Nonempty (⊤ : U.left.Opens) := ⟨⟨p, trivial⟩⟩
    infer_instance
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [← ZMod.natCast_zmod_val m] at h ⊢
  rw [← Int.cast_natCast, rootHom_intCast, Stacks.Kummer.zsmul_ofUnit, ← ofUnit_one,
    ofUnit_injective.eq_iff, zpow_natCast, Units.ext_iff, Units.val_pow_eq_pow_val, coe_rootOn,
    ← map_pow, Units.val_one] at h
  by_contra hne
  have hpos : 0 < m.val := Nat.pos_of_ne_zero fun h0 ↦ hne (by rw [h0, Nat.cast_zero])
  exact not_isUnit_one_sub_of_map_eq_one (structMap f U) h (hsep m.val hpos (ZMod.val_lt m))

/-- The presheaf map from the constant presheaf `ℤ/n` to `𝐆_m`, `m ↦ ζ^m`. -/
def rootPresheafHom
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) :
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

/-- The sheaf map from the constant sheaf `ℤ/n` to `𝐆_m`, `m ↦ ζ^m`. -/
def rootSheafHom
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) :
    Stacks.EtaleCohomology.etaleConstantSheaf X (ZMod n) ⟶ multiplicativeSheaf.{u, 0} X :=
  ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _
    (multiplicativeSheaf.{u, 0} X)).symm (rootPresheafHom f hζ hn)

/-- Precomposed with sheafification, the sheaf map `rootSheafHom` is the presheaf map
`rootPresheafHom`. -/
@[reassoc]
theorem toSheafify_rootSheafHom
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) :
    toSheafify X.smallEtaleTopology _ ≫ (rootSheafHom f hζ hn).hom = rootPresheafHom f hζ hn :=
  toSheafify_sheafifyLift _ _ (multiplicativeSheaf.{u, 0} X).property

/-- The presheaf map `m ↦ ζ^m` composed with the `n`-th power map of `𝐆_m` is zero. -/
theorem rootPresheafHom_comp_powMap
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) :
    rootPresheafHom f hζ hn ≫ (powMap.{u, 0} X n).hom = 0 := by
  ext U m
  change (powMap.{u, 0} X n).hom.app U (rootHom f hζ hn U.unop m.down) = 0
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective m.down
  rw [← hz, rootHom_intCast, Stacks.Kummer.zsmul_ofUnit, powMap_app_ofUnit, ← zpow_natCast,
    ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, rootOn_pow, one_zpow]
  rfl

/-- The sheaf map `m ↦ ζ^m` composed with the `n`-th power map of `𝐆_m` is zero. -/
theorem rootSheafHom_comp_powMap
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) : rootSheafHom f hζ hn ≫ powMap.{u, 0} X n = 0 := by
  ext : 1
  refine sheafify_hom_ext _ _ _ (multiplicativeSheaf.{u, 0} X).property ?_
  change toSheafify X.smallEtaleTopology _ ≫ (rootSheafHom f hζ hn).hom ≫
    (powMap.{u, 0} X n).hom = toSheafify X.smallEtaleTopology _ ≫ 0
  exact (toSheafify_rootSheafHom_assoc f hζ hn _).trans
    ((rootPresheafHom_comp_powMap f hζ hn).trans comp_zero.symm)

/-- **`ℤ/n ⟶ μ_n`, `m ↦ ζ^m`.** -/
def rootsOfUnityConstantHom
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) :
    Stacks.EtaleCohomology.etaleConstantSheaf X (ZMod n) ⟶ rootsOfUnitySheaf.{u, 0} X n :=
  kernel.lift _ (rootSheafHom f hζ hn) (rootSheafHom_comp_powMap f hζ hn)

/-- The map `ℤ/n ⟶ μ_n` followed by the inclusion `μ_n ⟶ 𝐆_m` is `rootSheafHom`. -/
theorem rootsOfUnityConstantHom_comp_ι
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) :
    rootsOfUnityConstantHom f hζ hn ≫ rootsOfUnityι.{u, 0} X n = rootSheafHom f hζ hn :=
  kernel.lift_ι _ _ _

include hsep in
/-- The presheaf map `m ↦ ζ^m` from the constant presheaf `ℤ/n` to `𝐆_m` is locally
injective. -/
theorem isLocallyInjective_rootPresheafHom :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (rootPresheafHom f hζ hn) where
  equalizerSieve_mem {U} a b h := by
    rcases isEmpty_or_nonempty U.unop.left with hU | hU
    · exact Stacks.Kummer.mem_smallEtaleTopology_of_isEmpty U.unop hU _
    · have hab : a = b := by
        have h' : rootHom f hζ hn U.unop a.down = rootHom f hζ hn U.unop b.down := h
        rw [← sub_eq_zero, ← map_sub, rootHom_eq_zero_iff f hζ hn hsep, sub_eq_zero] at h'
        exact ULift.ext h'
      rw [hab, Presheaf.equalizerSieve_self_eq_top]
      exact X.smallEtaleTopology.top_mem _

include hsep in
/-- The sheaf map `m ↦ ζ^m` from the constant sheaf `ℤ/n` to `𝐆_m` is locally injective. -/
theorem isLocallyInjective_rootSheafHom :
    Sheaf.IsLocallyInjective (rootSheafHom f hζ hn) := by
  have := Scheme.wEqualsLocallyBijective_smallEtaleTopology.{u, 0} X
  have key {F₁ F₂ F₃ : (X.Etale)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
      (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃) (h₃ : Presheaf.IsLocallyInjective X.smallEtaleTopology f₃)
      (h₁ : Presheaf.IsLocallySurjective X.smallEtaleTopology f₁) :
      Presheaf.IsLocallyInjective X.smallEtaleTopology f₂ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ f₃ fac
  exact key _ _ _ (toSheafify_rootSheafHom f hζ hn)
    (isLocallyInjective_rootPresheafHom f hζ hn hsep)
    ((X.smallEtaleTopology.W_toSheafify _).isLocallySurjective)

include hsep in
/-- The map `ℤ/n ⟶ μ_n`, `m ↦ ζ^m`, is a monomorphism. -/
theorem mono_rootsOfUnityConstantHom : Mono (rootsOfUnityConstantHom f hζ hn) := by
  have := isLocallyInjective_rootSheafHom f hζ hn hsep
  have : Sheaf.IsLocallyInjective (rootsOfUnityConstantHom f hζ hn) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_fac X.smallEtaleTopology
      (congrArg InducedCategory.Hom.hom (rootsOfUnityConstantHom_comp_ι f hζ hn))
  exact Sheaf.mono_of_isLocallyInjective _

/-- The map `ℤ/n ⟶ μ_n` followed by the inclusion `μ_n ⟶ 𝐆_m` is `rootSheafHom`, on the underlying
morphisms of presheaves. -/
theorem rootsOfUnityConstantHom_hom_comp_ι
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) :
    (rootsOfUnityConstantHom f hζ hn).hom ≫ (rootsOfUnityι.{u, 0} X n).hom =
      (rootSheafHom f hζ hn).hom :=
  congrArg InducedCategory.Hom.hom (rootsOfUnityConstantHom_comp_ι f hζ hn)

/-- On the image in the constant sheaf of a section `m` of the constant presheaf `ℤ/n`, the map
`ℤ/n ⟶ μ_n` followed by `μ_n ⟶ 𝐆_m` takes the value `ζ^m`. -/
theorem ι_rootsOfUnityConstantHom_toSheafify_apply
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0) (U : (X.Etale)ᵒᵖ)
    (m : ULift.{u + 1} (ZMod n)) :
    (rootsOfUnityι.{u, 0} X n).hom.app U ((rootsOfUnityConstantHom f hζ hn).hom.app U
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1, 0} (ZMod n))))).app U m)) =
      rootHom f hζ hn U.unop m.down := by
  let y := (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1, 0} (ZMod n))))).app U m
  have e1 : (rootsOfUnityι.{u, 0} X n).hom.app U ((rootsOfUnityConstantHom f hζ hn).hom.app U y) =
      (rootSheafHom f hζ hn).hom.app U y :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (rootsOfUnityConstantHom_hom_comp_ι f hζ hn) U) y
  have e2 : (rootSheafHom f hζ hn).hom.app U y = rootHom f hζ hn U.unop m.down :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_rootSheafHom f hζ hn) U) m
  exact e1.trans e2

variable (hnR : IsUnit (n : R))

/-- Every section of `μ_n` over an étale `X`-scheme is locally a power of `ζ`: its image sieve
under sheafification followed by `ℤ/n ⟶ μ_n` is a covering sieve. -/
theorem imageSieve_rootsOfUnityConstantHom_mem
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0)
    (hsep : ∀ i : ℕ, 0 < i → i < n → IsUnit (1 - ζ ^ i)) (hnR : IsUnit (n : R)) (U : X.Etale)
    (s : ToType ((rootsOfUnitySheaf.{u, 0} X n).obj.obj (op U))) :
    Presheaf.imageSieve (toSheafify X.smallEtaleTopology _ ≫
      (rootsOfUnityConstantHom f hζ hn).hom) s ∈ X.smallEtaleTopology U := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨x, hx⟩ := ofUnit_surjective.{u, 0} ((rootsOfUnityι.{u, 0} X n).hom.app (op U) s)
  have hxn : x ^ n = 1 := pow_eq_one_of_rootsOfUnitySheaf X n U s x hx.symm
  have hxn' : (x : Γ(U.left, ⊤)) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hxn, Units.val_one]
  let V := U.left
  have hloc : ∀ p : V, ∃ (i : ℕ) (W : V.Opens) (_ : p ∈ W) (iW : W ⟶ ⊤),
      V.presheaf.map iW.op (structMap f U ζ ^ i) = V.presheaf.map iW.op (x : Γ(V, ⊤)) := by
    intro p
    let φ : Γ(V, ⊤) →+* V.presheaf.stalk p := (V.presheaf.germ ⊤ p trivial).hom
    obtain ⟨i, -, hi⟩ := exists_pow_eq_of_isLocalRing (A := V.presheaf.stalk p)
      (n := n) (ζ := φ (structMap f U ζ))
      (by simpa using hnR.map (φ.comp (structMap f U)))
      (by rw [← map_pow, ← map_pow, hζ, map_one, map_one])
      (fun i hi0 hin ↦ by simpa using (hsep i hi0 hin).map (φ.comp (structMap f U)))
      (x := φ x) (by rw [← map_pow, hxn', map_one])
    rw [← map_pow] at hi
    obtain ⟨W, hpW, iU, iV, he⟩ := V.presheaf.germ_eq (U := ⊤) (V := ⊤) p trivial trivial _ _ hi
    exact ⟨i, W, hpW, iU, by rwa [Subsingleton.elim iV iU] at he⟩
  choose i W hpW iW hW using hloc
  let Z : V → X.Etale := fun p ↦ Scheme.Etale.mk ((W p).ι ≫ U.hom)
  let g : (p : V) → Z p ⟶ U := fun p ↦ MorphismProperty.Over.homMk (W p).ι rfl
  have hcov : Sieve.ofArrows Z g ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ⟨p, ?_⟩
    change p ∈ Set.range (W p).ι
    rw [Scheme.Opens.range_ι]
    exact hpW p
  refine X.smallEtaleTopology.superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨p⟩
  refine ⟨ULift.up (i p : ZMod n),
    Stacks.Kummer.rootsOfUnityι_app_op_injective (X := X) (n := n) (U := op (Z p)) ?_⟩
  change _ = (rootsOfUnityι.{u, 0} X n).hom.app (op (Z p))
    ((rootsOfUnitySheaf.{u, 0} X n).obj.map (g p).op s)
  refine (ι_rootsOfUnityConstantHom_toSheafify_apply f hζ hn (op (Z p)) _).trans ?_
  rw [NatTrans.naturality_apply, ← hx, map_ofUnit]
  change rootHom f hζ hn (Z p) (i p : ZMod n) = _
  rw [← Int.cast_natCast, rootHom_intCast, Stacks.Kummer.zsmul_ofUnit]
  congr 1
  apply Units.ext
  rw [Units.coe_map, zpow_natCast, Units.val_pow_eq_pow_val, coe_rootOn,
    ← structMap_comp f (g p), RingHom.comp_apply, ← map_pow]
  change (W p).ι.appTop.hom (structMap f U ζ ^ i p) = (W p).ι.appTop.hom (x : Γ(V, ⊤))
  have h : (W p).ι ''ᵁ ⊤ ≤ W p := by rw [Scheme.Opens.ι_image_top]
  have hfac : (homOfLE (le_top : (W p).ι ''ᵁ ⊤ ≤ ⊤)).op = (iW p).op ≫ (homOfLE h).op :=
    rfl
  rw [Scheme.Opens.ι_appTop, hfac, Functor.map_comp]
  change (V.presheaf.map (homOfLE h).op).hom ((V.presheaf.map (iW p).op).hom _) =
    (V.presheaf.map (homOfLE h).op).hom ((V.presheaf.map (iW p).op).hom _)
  rw [hW p]

/-- **`m ↦ ζ^m` is an isomorphism `ℤ/n ≅ μ_n` of sheaves on `X_étale`**, for `X` a scheme over a
ring `R` in which `n` is invertible and `ζ ^ n = 1` with `1 - ζ ^ i` a unit for `0 < i < n`. -/
theorem isIso_rootsOfUnityConstantHom
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {n : ℕ} {ζ : R}
    (hζ : ζ ^ n = 1) (hn : n ≠ 0)
    (hsep : ∀ i : ℕ, 0 < i → i < n → IsUnit (1 - ζ ^ i)) (hnR : IsUnit (n : R)) :
    IsIso (rootsOfUnityConstantHom f hζ hn) := by
  have := mono_rootsOfUnityConstantHom f hζ hn hsep
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology _ ≫ (rootsOfUnityConstantHom f hζ hn).hom) :=
    ⟨fun s ↦ imageSieve_rootsOfUnityConstantHom_mem f hζ hn hsep hnR _ s⟩
  have : Sheaf.IsLocallySurjective (rootsOfUnityConstantHom f hζ hn) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology _) (rootsOfUnityConstantHom f hζ hn).hom
  have : Epi (rootsOfUnityConstantHom f hζ hn) := Sheaf.epi_of_isLocallySurjective _
  exact isIso_of_mono_of_epi _

/-- **`μ_n ≅ ℤ/n` on the small étale site of a scheme over a ring with separated `n`-th roots of
unity**, the isomorphism `ℤ/n ⟶ μ_n` sending `m` to `ζ^m`. -/
def rootsOfUnityConstantIso :
    Stacks.EtaleCohomology.etaleConstantSheaf X (ZMod n) ≅ rootsOfUnitySheaf.{u, 0} X n :=
  haveI := isIso_rootsOfUnityConstantHom f hζ hn hsep hnR
  asIso (rootsOfUnityConstantHom f hζ hn)

/-- **A henselian local ring with separably closed residue field contains separated `n`-th roots
of unity** when `n` is invertible: there is `ζ` with `ζ ^ n = 1` and `1 - ζ ^ i` a unit for
`0 < i < n`. -/
theorem exists_separated_root_of_henselianLocalRing (A : Type*) [CommRing A]
    [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] {n : ℕ}
    (hn : IsUnit (n : A)) :
    ∃ ζ : A, ζ ^ n = 1 ∧ ∀ i : ℕ, 0 < i → i < n → IsUnit (1 - ζ ^ i) := by
  open Polynomial in
  have hn0 := ne_zero_of_isUnit_natCast hn
  let κ := IsLocalRing.ResidueField A
  let r := IsLocalRing.residue A
  have : NeZero (n : κ) := ⟨natCast_residueField_ne_zero hn⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot κ n
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective ζ₀
  have hmonic : (X ^ n - 1 : A[X]).Monic := monic_X_pow_sub_C 1 hn0
  have heval : (X ^ n - 1 : A[X]).eval a₀ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp [hζ₀.pow_eq_one]
  have ha₀ : IsUnit a₀ :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (hζ₀.ne_zero hn0)
  have hder : IsUnit ((X ^ n - 1 : A[X]).derivative.eval a₀) := by
    have : (X ^ n - 1 : A[X]).derivative.eval a₀ = (n : A) * a₀ ^ (n - 1) := by
      simp [derivative_X_pow]
    rw [this]
    exact hn.mul (ha₀.pow _)
  obtain ⟨ζ, hroot, hdiff⟩ := HenselianLocalRing.is_henselian _ hmonic a₀ heval hder
  have hζn : ζ ^ n = 1 := by simpa [sub_eq_zero] using hroot.eq_zero
  have hres : r ζ = r a₀ := by
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hdiff
  refine ⟨ζ, hζn, fun i hi0 hin ↦ ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_one, map_pow, hres, sub_ne_zero]
  exact fun h ↦ hζ₀.pow_ne_one_of_pos_of_lt hi0.ne' hin h.symm

end Stacks.Kummer.OverRing

end
