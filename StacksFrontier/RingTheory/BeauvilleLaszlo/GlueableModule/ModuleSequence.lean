module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueingPair

/-!
# Glueable modules: the module sequence

Let `R` be a commutative ring, let `f : R`, and let `R → R'` be a ring map inducing
isomorphisms `R/fⁿR → R'/fⁿR'` for every `n > 0`. Tensoring the sequence of a glueing pair
with an `R`-module `M` gives
`0 → M → (M ⊗[R] R') ⊕ M_f → M ⊗[R] R'_f → 0`,
and `M` is called *glueable for `(R → R', f)`* when this sequence is exact. For `R' = R^∧`
the `(f)`-adic completion one simply says `M` is *glueable*. Glueability is exactly the
condition under which `M` is recovered from its base changes to `R'` and `R_f`, and it is
the hypothesis of the Beauville--Laszlo equivalence.

## Main definitions

* `beauvilleLaszloModuleSequence` (Stacks 0F1R): the sequence
  `0 → M → (M ⊗[R] R') ⊕ (M ⊗[R] R_f) → M ⊗[R] R'_f → 0`, as a `ShortComplex` of additive
  groups, together with the maps `toTensorBaseChanges` and `tensorAwayDifference` it is
  built from.
* `IsGlueableFor`, `IsGlueable` (Stacks 0BNV): glueability for `(R → R', f)` and its
  specialization to the `(f)`-adic completion.

## Main results

* `isGlueable_iff_adicCompletion_beauvilleLaszloModuleSequence_shortExact` (Stacks 0BNV):
  glueability is short exactness of the completion sequence.
* `beauvilleLaszloModuleSequence_exactness_iff_powerTorsionMap` (Stacks 0BNW): the sequence
  is always exact on the right; it is exact on the left, resp. in the middle, exactly when
  `M[f^∞] → (M ⊗[R] R')[f^∞]` is injective, resp. surjective. So `M` is glueable for
  `(R → R', f)` iff that map is bijective, and for a glueing pair injectivity already
  suffices.

## Implementation notes

As for the ring sequence, the module sequence is a `ShortComplex AddCommGrpCat` whose objects
are universe-lifted, and `IsGlueableFor` is stated elementwise (injective, exact, surjective)
with `isGlueable_iff_adicCompletion_beauvilleLaszloModuleSequence_shortExact` transporting
between the two formulations. `M ⊗[R] R_f` is used in place of the localization `M_f`; the two
agree by `IsLocalizedModule`, which is what the middle-exactness argument exploits.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0F1R](https://stacks.math.columbia.edu/tag/0F1R)
* [Stacks Project, Tag 0BNV](https://stacks.math.columbia.edu/tag/0BNV)
* [Stacks Project, Tag 0BNW](https://stacks.math.columbia.edu/tag/0BNW)
-/

@[expose] public section

namespace BeauvilleLaszlo
section

open CategoryTheory


universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- Base change from `S` to its localization away from the image of `f`, tensored with `M`. -/
public noncomputable def baseChangeToAway (f : R) :
    TensorProduct R M S →ₗ[R]
      TensorProduct R M (Localization.Away (algebraMap R S f)) :=
  TensorProduct.map LinearMap.id
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S f))).toLinearMap

/-- `baseChangeToAway` sends `m ⊗ s` to `m ⊗ s/1`. -/
@[simp]
public theorem baseChangeToAway_tmul (f : R) (m : M) (s : S) :
    baseChangeToAway M f (m ⊗ₜ[R] s) =
      m ⊗ₜ[R] algebraMap S (Localization.Away (algebraMap R S f)) s := by
  simp [baseChangeToAway]

/-- The map `R_f → S_f` induced by `R → S`, regarded as an `R`-linear map and tensored with
`M`. -/
public noncomputable def localizedBaseChangeToAway (f : R) :
    TensorProduct R M (Localization.Away f) →ₗ[R]
      TensorProduct R M (Localization.Away (algebraMap R S f)) :=
  TensorProduct.map LinearMap.id
    { toFun := Localization.awayMap (algebraMap R S) f
      map_add' := map_add _
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [map_mul]
        congr 1
        rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
        exact (IsScalarTower.algebraMap_apply R S
          (Localization.Away (algebraMap R S f)) r).symm }

/-- `localizedBaseChangeToAway` sends `m ⊗ x` to `m ⊗ x'`, where `x'` is the image of `x` under
`R_f → S_f`. -/
@[simp]
public theorem localizedBaseChangeToAway_tmul (f : R) (m : M)
    (x : Localization.Away f) :
    localizedBaseChangeToAway M f (m ⊗ₜ[R] x) =
      m ⊗ₜ[R] Localization.awayMap (algebraMap R S) f x := by
  simp [localizedBaseChangeToAway]

/-- The diagonal map from `M` to its base changes to `S` and `R_f`. -/
public noncomputable def toTensorBaseChanges (f : R) :
    M →ₗ[R] (TensorProduct R M S × TensorProduct R M (Localization.Away f)) :=
  LinearMap.prod ((TensorProduct.mk R M S).flip (1 : S))
    ((TensorProduct.mk R M (Localization.Away f)).flip 1)

/-- `toTensorBaseChanges` sends `m` to the pair `(m ⊗ 1, m ⊗ 1)`. -/
@[simp]
public theorem toTensorBaseChanges_apply (f : R) (m : M) :
    toTensorBaseChanges M f m = (m ⊗ₜ[R] (1 : S), m ⊗ₜ[R] (1 : Localization.Away f)) :=
  rfl

/-- The difference of the two canonical maps from the two base changes of `M` to its base change
to `S_f`. -/
public noncomputable def tensorAwayDifference (f : R) :
    (TensorProduct R M S × TensorProduct R M (Localization.Away f)) →ₗ[R]
      TensorProduct R M (Localization.Away (algebraMap R S f)) :=
  LinearMap.coprod (baseChangeToAway M f) (-localizedBaseChangeToAway M f)

/-- `tensorAwayDifference` sends a pair `(x, y)` to the difference of the images of `x` and `y`
in the base change to `S_f`. -/
@[simp]
public theorem tensorAwayDifference_apply (f : R)
    (x : TensorProduct R M S × TensorProduct R M (Localization.Away f)) :
    tensorAwayDifference M f x =
      baseChangeToAway M f x.1 - localizedBaseChangeToAway M f x.2 := by
  rfl

/-- The canonical sequence
`0 → M → (M ⊗[R] S) ⊕ (M ⊗[R] R_f) → M ⊗[R] S_f → 0`.
The right-hand map is the difference of the two maps induced by localization. -/
@[stacks 0F1R]
public noncomputable def beauvilleLaszloModuleSequence (f : R) :
    ShortComplex AddCommGrpCat.{max u v w} :=
  let d : AddCommGrpCat.of (ULift.{max u v w} M) ⟶
      AddCommGrpCat.of (ULift.{max u v w}
        (TensorProduct R M S × TensorProduct R M (Localization.Away f))) :=
    AddCommGrpCat.ofHom
      { toFun := fun m ↦ ⟨toTensorBaseChanges (R := R) (S := S) M f m.down⟩
        map_zero' := ULift.down_injective (map_zero (toTensorBaseChanges (R := R) (S := S) M f))
        map_add' := by
          intro x y
          apply ULift.down_injective
          exact map_add (toTensorBaseChanges (R := R) (S := S) M f) x.down y.down }
  let e : AddCommGrpCat.of (ULift.{max u v w}
      (TensorProduct R M S × TensorProduct R M (Localization.Away f))) ⟶
      AddCommGrpCat.of (ULift.{max u v w}
        (TensorProduct R M (Localization.Away (algebraMap R S f)))) :=
    AddCommGrpCat.ofHom
      { toFun := fun x ↦ ⟨tensorAwayDifference (R := R) (S := S) M f x.down⟩
        map_zero' := ULift.down_injective (map_zero (tensorAwayDifference (R := R) (S := S) M f))
        map_add' := by
          intro x y
          apply ULift.down_injective
          exact map_add (tensorAwayDifference (R := R) (S := S) M f) x.down y.down }
  ShortComplex.mk d e
    (by
      ext m
      rcases m with ⟨m⟩
      simp [d, e, toTensorBaseChanges, tensorAwayDifference, baseChangeToAway,
        localizedBaseChangeToAway])

end

section

open CategoryTheory


universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- An `R`-module is glueable for `(R → S, f)` if its canonical Beauville--Laszlo sequence
is injective on the left, exact in the middle, and surjective on the right. -/
public def IsGlueableFor (f : R) : Prop :=
  Function.Injective (toTensorBaseChanges (R := R) (S := S) M f) ∧
    Function.Exact (toTensorBaseChanges (R := R) (S := S) M f)
      (tensorAwayDifference (R := R) (S := S) M f) ∧
    Function.Surjective (tensorAwayDifference (R := R) (S := S) M f)

/-- An `R`-module is glueable at `f` if it is glueable after base change to the `(f)`-adic
completion and localization away from `f`. -/
public abbrev IsGlueable {R : Type u} [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
    (f : R) : Prop :=
  IsGlueableFor (S := AdicCompletion (Ideal.span {f}) R) M f

end

section

open CategoryTheory


universe u w

/-- An `R`-module is glueable at `f` exactly when
`0 → M → (M ⊗[R] R̂) ⊕ (M ⊗[R] R_f) → M ⊗[R] R̂_f → 0`
is short exact, where `R̂` is the `(f)`-adic completion. -/
@[stacks 0BNV]
public theorem isGlueable_iff_adicCompletion_beauvilleLaszloModuleSequence_shortExact {R : Type u}
  [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
    (f : R) :
    IsGlueable M f ↔
      (beauvilleLaszloModuleSequence
        (S := AdicCompletion (Ideal.span {f}) R) M f).ShortExact := by
  let S := beauvilleLaszloModuleSequence
    (S := AdicCompletion (Ideal.span {f}) R) M f
  constructor
  · rintro ⟨hinj, hexact, hsurj⟩
    apply ShortComplex.ShortExact.mk'
    · rw [S.ab_exact_iff_function_exact]
      intro x
      constructor
      · intro hx
        obtain ⟨z, hz⟩ := (hexact x.down).mp (congr_arg ULift.down hx)
        refine ⟨⟨z⟩, ?_⟩
        apply ULift.ext
        exact hz
      · rintro ⟨z, hz⟩
        apply ULift.ext
        apply (hexact x.down).mpr
        exact ⟨z.down, congr_arg ULift.down hz⟩
    · rw [AddCommGrpCat.mono_iff_injective]
      intro x y hxy
      apply ULift.ext
      exact hinj (congr_arg ULift.down hxy)
    · rw [AddCommGrpCat.epi_iff_surjective]
      rintro ⟨z⟩
      obtain ⟨x, hx⟩ := hsurj z
      refine ⟨⟨x⟩, ?_⟩
      apply ULift.ext
      exact hx
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      have hi := h.ab_injective_f
      apply congr_arg ULift.down
      apply hi
      apply ULift.ext
      exact hxy
    · intro x
      constructor
      · intro hx
        have he := S.ab_exact_iff_function_exact.mp h.exact
        have hx' : S.g ⟨x⟩ = 0 := ULift.ext hx
        obtain ⟨y, hy⟩ := (he ⟨x⟩).mp hx'
        exact ⟨y.down, congr_arg ULift.down hy⟩
      · rintro ⟨y, rfl⟩
        have he := S.ab_exact_iff_function_exact.mp h.exact
        have hz : S.g (S.f ⟨y⟩) = 0 := (he _).mpr ⟨⟨y⟩, rfl⟩
        exact congr_arg ULift.down hz
    · intro z
      obtain ⟨x, hx⟩ := h.ab_surjective_g ⟨z⟩
      exact ⟨x.down, congr_arg ULift.down hx⟩

end

section

open CategoryTheory


universe u v w

/-- The canonical map `M[f^∞] → (M ⊗[R] S)[f^∞]` induced by `m ↦ m ⊗ 1`. -/
public noncomputable def tensorProductPowerTorsionMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R) :
    modulePowerTorsion M f →ₗ[R] modulePowerTorsion (TensorProduct R M S) f where
  toFun x := ⟨x.1 ⊗ₜ[R] (1 : S), by
    obtain ⟨a, ha⟩ := x.2
    refine ⟨a, ?_⟩
    change (a : R) • (x.1 ⊗ₜ[R] (1 : S)) = 0
    change (a : R) • x.1 = 0 at ha
    rw [TensorProduct.smul_tmul', ha, TensorProduct.zero_tmul]⟩
  map_add' x y := Subtype.ext (TensorProduct.add_tmul x.1 y.1 1)
  map_smul' r x := Subtype.ext (TensorProduct.smul_tmul' r x.1 1)

/-- `tensorProductPowerTorsionMap` sends `m` to `m ⊗ 1`. -/
@[simp]
public theorem tensorProductPowerTorsionMap_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R)
    (x : modulePowerTorsion M f) :
    (tensorProductPowerTorsionMap (S := S) M f x : TensorProduct R M S) =
      x.1 ⊗ₜ[R] (1 : S) :=
  rfl

end

section

open CategoryTheory



universe u v w

private theorem quotientPowMap_surjective_decomposition
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (f : R) (n : ℕ)
    (h : Function.Surjective
      (quotientPowMap f n (algebraMap R S))) (s : S) :
    ∃ r : R, ∃ t : S, s = algebraMap R S r + (algebraMap R S f) ^ n * t := by
  obtain ⟨q, hq⟩ := h (Ideal.Quotient.mk ((Ideal.span {algebraMap R S f}) ^ n) s)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hs : s - algebraMap R S r ∈
      (Ideal.span {algebraMap R S f}) ^ n := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    simpa only [quotientPowMap_mk] using hq.symm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hs
  obtain ⟨t, ht⟩ := hs
  refine ⟨r, t, ?_⟩
  rw [← ht]
  abel

private theorem tensorProduct_mod_power_decomposition
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R) (n : ℕ)
    (h : Function.Surjective
      (quotientPowMap f n (algebraMap R S)))
    (x : TensorProduct R M S) :
    ∃ m : M, ∃ y : TensorProduct R M S,
      x = m ⊗ₜ[R] (1 : S) + f ^ n • y := by
  induction x with
  | tmul m s =>
      obtain ⟨r, t, hs⟩ := quotientPowMap_surjective_decomposition f n h s
      refine ⟨r • m, m ⊗ₜ[R] t, ?_⟩
      calc
        m ⊗ₜ[R] s =
            m ⊗ₜ[R] (algebraMap R S r + (algebraMap R S f) ^ n * t) := by rw [hs]
        _ = (r • m) ⊗ₜ[R] (1 : S) + f ^ n • (m ⊗ₜ[R] t) := by
          rw [TensorProduct.tmul_add, ← map_pow]
          congr 1
          · simpa [Algebra.smul_def] using
              (TensorProduct.smul_tmul r m (1 : S)).symm
          · rw [← Algebra.smul_def, ← TensorProduct.smul_tmul]
            rfl
  | add x y hx hy =>
      obtain ⟨m, z, rfl⟩ := hx
      obtain ⟨m', z', rfl⟩ := hy
      refine ⟨m + m', z + z', ?_⟩
      simp [TensorProduct.add_tmul, smul_add, add_assoc, add_left_comm, add_comm]

private theorem tensorProduct_mod_power_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R) (n : ℕ)
    (h : Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (m : M) (x : TensorProduct R M S) (hx : m ⊗ₜ[R] (1 : S) = f ^ n • x) :
    ∃ m' : M, m = f ^ n • m' := by
  let I : Ideal R := (Ideal.span {f}) ^ n
  let J : Ideal S := (Ideal.span {algebraMap R S f}) ^ n
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ J) := AlgEquiv.ofBijective
    { __ := quotientPowMap f n (algebraMap R S)
      commutes' := fun r ↦ by
        change Ideal.Quotient.mk J (algebraMap R S r) = _
        exact Ideal.Quotient.mk_algebraMap R J r } h
  let k : S →ₗ[R] R ⧸ I := e.symm.toLinearMap.comp (Ideal.Quotient.mkₐ R J).toLinearMap
  have hkone : k 1 = 1 := by simp [k]
  have hpow : (Ideal.Quotient.mk I) (f ^ n) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change f ^ n ∈ (Ideal.span {f}) ^ n
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hz : ∀ y : TensorProduct R M (R ⧸ I), f ^ n • y = 0 := by
    intro y
    induction y with
    | tmul m r =>
        rw [← TensorProduct.tmul_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          hpow, zero_mul, TensorProduct.tmul_zero]
    | add y z hy hz => simp [smul_add, hy, hz]
  have hm : (Algebra.linearMap R (R ⧸ I)).lTensor M (m ⊗ₜ[R] (1 : R)) = 0 := by
    have ht := congrArg (k.lTensor M) hx
    simpa only [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one, map_smul,
      hkone, hz] using ht
  have he : Function.Exact (f ^ n • (LinearMap.id : R →ₗ[R] R))
      (Algebra.linearMap R (R ⧸ I)) := by
    intro r
    change Ideal.Quotient.mk I r = 0 ↔ ∃ a : R, f ^ n * a = r
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change r ∈ (Ideal.span {f}) ^ n ↔ _
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact exists_congr (fun a ↦ eq_comm)
  obtain ⟨y, hy⟩ := (lTensor_exact M he Ideal.Quotient.mk_surjective _).mp hm
  refine ⟨TensorProduct.rid R M y, ?_⟩
  have ht := congrArg (TensorProduct.rid R M) hy
  simpa only [LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul, TensorProduct.rid_tmul, one_smul] using ht.symm

private theorem isLocalizedModule_lTensor {R : Type*} [CommSemiring R] {A B M : Type*}
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [AddCommMonoid M] [Module R M] (s : Submonoid R)
    (g : A →ₗ[R] B) [IsLocalizedModule s g] : IsLocalizedModule s (g.lTensor M) := by
  have h : IsLocalizedModule s (g.rTensor M) :=
    IsLocalizedModule.rTensor R s g
  have h' := IsLocalizedModule.of_linearEquiv_right s (g.rTensor M) (TensorProduct.comm R M A)
  have h'' := IsLocalizedModule.of_linearEquiv s _ (TensorProduct.comm R B M)
    (hf := h')
  convert h'' using 1
  ext m a
  rfl

private theorem isLocalizedModule_tensor_away
    {R : Type u} [CommSemiring R] (M : Type w) [AddCommMonoid M] [Module R M] (f : R) :
    IsLocalizedModule.Away f ((TensorProduct.mk R M (Localization.Away f)).flip 1) := by
  have h := IsLocalizedModule.of_linearEquiv (Submonoid.powers f)
    (TensorProduct.mk R (Localization.Away f) M 1)
    (TensorProduct.comm R (Localization.Away f) M)
  convert h using 1
  ext m
  rfl

private theorem isLocalizedModule_scalar_away
    {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S] (f : R) :
    IsLocalizedModule.Away f
      (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S f))).toLinearMap := by
  exact IsLocalizedModule.restrictScalars_powers f
    (Algebra.linearMap S (Localization.Away (algebraMap R S f)))

/-- An element lies in `M[f^∞]` iff some power of `f` kills it. -/
private theorem mem_modulePowerTorsion_iff {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (f : R) (a : M) :
    a ∈ modulePowerTorsion M f ↔ ∃ n : ℕ, f ^ n • a = 0 := by
  constructor
  · rintro ⟨⟨_, ⟨n, rfl⟩⟩, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨f ^ n, ⟨n, rfl⟩⟩, hn⟩

/-- A localization map away from `f` kills exactly the elements killed by a power of `f`. -/
private theorem eq_zero_iff_exists_pow_smul_eq_zero {R : Type*} [CommRing R] {A B : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (f : R) (v : A →ₗ[R] B)
    [IsLocalizedModule.Away f v] (a : A) : v a = 0 ↔ ∃ n : ℕ, f ^ n • a = 0 :=
  (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) v).trans (mem_modulePowerTorsion_iff f a)

/-- The elementwise argument for a square whose horizontal maps become
localizations after inverting `f`. -/
private theorem localization_square_exactness
    {R : Type u} [CommRing R]
    {A : Type v} {B : Type w} {C : Type*} {D : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (f : R) (u : A →ₗ[R] B) (v : A →ₗ[R] C)
    (p : B →ₗ[R] D) (q : C →ₗ[R] D)
    (hcomm : p.comp u = q.comp v)
    (hlocalC : IsLocalizedModule.Away f v)
    (hlocalD : IsLocalizedModule.Away f p)
    (hmodsurj : ∀ n : ℕ, 0 < n → ∀ b : B,
      ∃ a : A, ∃ b' : B, b = u a + f ^ n • b')
    (hmodinj : ∀ n : ℕ, 0 < n → ∀ a : A,
      (∃ b : B, u a = f ^ n • b) → ∃ a' : A, a = f ^ n • a') :
    Function.Surjective (fun z : B × C ↦ p z.1 - q z.2) ∧
    (Function.Injective (fun a : A ↦ (u a, v a)) ↔
      ∀ a : A, (∃ n : ℕ, f ^ n • a = 0) → u a = 0 → a = 0) ∧
    (Function.Exact (fun a : A ↦ (u a, v a))
      (fun z : B × C ↦ p z.1 - q z.2) ↔
      ∀ b : B, (∃ n : ℕ, f ^ n • b = 0) →
        ∃ a : A, (∃ n : ℕ, f ^ n • a = 0) ∧ u a = b) := by
  let : IsLocalizedModule.Away f v := hlocalC
  let : IsLocalizedModule.Away f p := hlocalD
  have hvzero (a : A) : v a = 0 ↔ ∃ n : ℕ, f ^ n • a = 0 :=
    eq_zero_iff_exists_pow_smul_eq_zero f v a
  have hpzero (b : B) : p b = 0 ↔ ∃ n : ℕ, f ^ n • b = 0 :=
    eq_zero_iff_exists_pow_smul_eq_zero f p b
  have hvinj (n : ℕ) : Function.Injective (fun c : C ↦ f ^ n • c) :=
    IsLocalizedModule.smul_injective (S := Submonoid.powers f) v ⟨f ^ n, ⟨n, rfl⟩⟩
  have hpinj (n : ℕ) : Function.Injective (fun d : D ↦ f ^ n • d) :=
    IsLocalizedModule.smul_injective (S := Submonoid.powers f) p ⟨f ^ n, ⟨n, rfl⟩⟩
  have hvdiv (n : ℕ) (c : C) : ∃ c' : C, f ^ n • c' = c := by
    have hu := IsLocalizedModule.Away.isUnit_algebraMap v f
    simpa only [← map_pow, Module.algebraMap_end_apply] using
      ((Module.End.isUnit_iff _).mp (hu.pow n)).surjective c
  constructor
  · intro d
    obtain ⟨n, b, hb⟩ := IsLocalizedModule.Away.surj p f d
    obtain ⟨a, b', hdecomp⟩ := hmodsurj (n + 1) (Nat.zero_lt_succ n) (f • b)
    obtain ⟨c, hc⟩ := hvdiv (n + 1) (v a)
    have hnum : f ^ (n + 1) • d = p (f • b) := by
      calc
        f ^ (n + 1) • d = f • (f ^ n • d) := by rw [pow_succ, mul_smul, smul_comm]
        _ = f • p b := by rw [hb]
        _ = p (f • b) := by rw [map_smul]
    have h : f ^ (n + 1) • (d - p b' - q c) = 0 := by
      rw [smul_sub, smul_sub, hnum, ← map_smul, ← map_smul, hc,
        hdecomp, map_add, ← LinearMap.comp_apply, hcomm,
        LinearMap.comp_apply]
      abel
    have heq : d = p b' + q c := by
      have h0 : d - p b' - q c = 0 := hpinj (n + 1) (by simpa using h)
      exact sub_eq_zero.mp (by simpa only [sub_add_eq_sub_sub] using h0)
    refine ⟨(b', -c), ?_⟩
    simp [heq]
  · constructor
    · constructor
      · intro hi a ha hu
        apply hi
        apply Prod.ext
        · simpa using hu
        · simpa using (hvzero a).2 ha
      · intro hi a b hab
        have huba : u (a - b) = 0 := by
          simpa [map_sub] using sub_eq_zero.mpr (congrArg Prod.fst hab)
        have hvba : v (a - b) = 0 := by
          simpa [map_sub] using sub_eq_zero.mpr (congrArg Prod.snd hab)
        exact sub_eq_zero.mp (hi (a - b) ((hvzero _).1 hvba) huba)
    · constructor
      · intro hex b hb
        obtain ⟨a, ha⟩ := (hex (b, 0)).mp (by simp [(hpzero b).2 hb])
        refine ⟨a, (hvzero a).1 ?_, ?_⟩
        · simpa using congrArg Prod.snd ha
        · simpa using congrArg Prod.fst ha
      · intro hsurj z
        constructor
        · intro hz
          obtain ⟨n, a, ha⟩ := IsLocalizedModule.Away.surj v f z.2
          have hpb : p (f ^ n • z.1 - u a) = 0 := by
            have hq : p z.1 = q z.2 := sub_eq_zero.mp hz
            rw [map_sub, map_smul, hq, ← map_smul, ha,
              ← LinearMap.comp_apply, ← LinearMap.comp_apply, hcomm,
              LinearMap.comp_apply, sub_self]
          obtain ⟨a₁, ha₁, hua₁⟩ := hsurj _ ((hpzero _).1 hpb)
          have hu' : u (a + a₁) = f ^ n • z.1 := by
            rw [map_add, hua₁]
            abel
          have hv' : v (a + a₁) = f ^ n • z.2 := by
            rw [map_add, (hvzero _).2 ha₁, add_zero, ha]
          have hna : ∃ a₂ : A, a + a₁ = f ^ n • a₂ := by
            by_cases hn : n = 0
            · exact ⟨a + a₁, by simp [hn]⟩
            · exact hmodinj n (Nat.pos_of_ne_zero hn) (a + a₁) ⟨z.1, hu'⟩
          obtain ⟨a₂, hna₂⟩ := hna
          have hy : z.2 = v a₂ := by
            apply hvinj n
            change f ^ n • z.2 = f ^ n • v a₂
            rw [← hv', hna₂, map_smul]
          have hbtors : ∃ k : ℕ, f ^ k • (z.1 - u a₂) = 0 := by
            refine ⟨n, ?_⟩
            rw [smul_sub, ← map_smul, ← hna₂, ← hu', sub_self]
          obtain ⟨a₃, ha₃, hua₃⟩ := hsurj _ hbtors
          refine ⟨a₂ + a₃, ?_⟩
          apply Prod.ext
          · simp [map_add, hua₃]
          · simp [hy, (hvzero _).2 ha₃]
        · rintro ⟨a, rfl⟩
          change p (u a) - q (v a) = 0
          rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, sub_self]

private theorem ulift_exact_iff {A B C : Type*} [Zero C] (a : A → B) (b : B → C) :
    Function.Exact (ULift.map a : ULift.{u} A → ULift.{v} B)
      (ULift.map b : ULift.{v} B → ULift.{w} C) ↔ Function.Exact a b := by
  simp only [Function.Exact, ULift.forall, ULift.map, ULift.ext_iff,
    Set.mem_range, ULift.exists]
  rfl

private theorem module_sequence_exact_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R) :
    (beauvilleLaszloModuleSequence (S := S) M f).Exact ↔
      Function.Exact (toTensorBaseChanges (S := S) M f)
        (tensorAwayDifference (S := S) M f) := by
  rw [ShortComplex.ab_exact_iff_function_exact]
  exact ulift_exact_iff _ _

private theorem module_sequence_mono_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R) :
    Mono (beauvilleLaszloModuleSequence (S := S) M f).f ↔
      Function.Injective (tensorProductPowerTorsionMap (S := S) M f) := by
  rw [AddCommGrpCat.mono_iff_injective]
  change Function.Injective (ULift.map (toTensorBaseChanges (S := S) M f)) ↔ _
  rw [ULift.map_injective]
  let l := (TensorProduct.mk R M (Localization.Away f)).flip 1
  let : IsLocalizedModule.Away f l := isLocalizedModule_tensor_away M f
  have hl (m : M) : l m = 0 ↔ m ∈ modulePowerTorsion M f :=
    IsLocalizedModule.eq_zero_iff (Submonoid.powers f) l
  constructor
  · intro hi x y hxy
    apply Subtype.ext
    apply hi
    apply Prod.ext
    · exact congrArg Subtype.val hxy
    · change l x = l y
      rw [(hl _).mpr x.property, (hl _).mpr y.property]
  · intro hi x y hxy
    have hv : l (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
    have ht : tensorProductPowerTorsionMap (S := S) M f ⟨x - y, (hl _).mp hv⟩ = 0 := by
      apply Subtype.ext
      change (x - y) ⊗ₜ[R] (1 : S) = 0
      rw [TensorProduct.sub_tmul]
      exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
    have hh := congrArg Subtype.val (hi (ht.trans (map_zero _).symm))
    exact sub_eq_zero.mp hh

private theorem torsionMap_surjective_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R) :
    Function.Surjective (tensorProductPowerTorsionMap (S := S) M f) ↔
      ∀ b : TensorProduct R M S, (∃ n : ℕ, f ^ n • b = 0) →
        ∃ a : M, (∃ n : ℕ, f ^ n • a = 0) ∧ a ⊗ₜ[R] (1 : S) = b := by
  constructor
  · intro h b ht
    obtain ⟨a, ha⟩ := h ⟨b, (mem_modulePowerTorsion_iff f b).mpr ht⟩
    exact ⟨a, (mem_modulePowerTorsion_iff f a.1).mp a.property, congrArg Subtype.val ha⟩
  · intro h b
    obtain ⟨a, ha, hab⟩ := h b ((mem_modulePowerTorsion_iff f b.1).mp b.property)
    exact ⟨⟨a, (mem_modulePowerTorsion_iff f a).mpr ha⟩, Subtype.ext hab⟩

private theorem module_sequence_exact_epi_of_ring
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R)
    (hs : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact) :
    (beauvilleLaszloModuleSequence (S := S) M f).Exact ∧
      Epi (beauvilleLaszloModuleSequence (S := S) M f).g := by
  let a : R →ₗ[R] S × Localization.Away f :=
    (Algebra.linearMap R S).prod (Algebra.linearMap R (Localization.Away f))
  let c : S →ₗ[R] Localization.Away (algebraMap R S f) :=
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S f))).toLinearMap
  let d : Localization.Away f →ₗ[R] Localization.Away (algebraMap R S f) :=
    { toFun := Localization.awayMap (algebraMap R S) f
      map_add' := map_add _
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [map_mul]
        congr 1
        rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
        exact (IsScalarTower.algebraMap_apply R S
          (Localization.Away (algebraMap R S f)) r).symm }
  let b := c.coprod (-d)
  have he : Function.Exact a b := by
    have hh := (ShortComplex.ab_exact_iff_function_exact _).mp hs.exact
    exact (ulift_exact_iff a b).mp hh
  have hb : Function.Surjective b := by
    have hh := (AddCommGrpCat.epi_iff_surjective _).mp hs.epi_g
    exact ULift.map_surjective.mp hh
  let e := TensorProduct.prodRight R R M S (Localization.Away f)
  have hea : e.toLinearMap.comp (a.lTensor M) =
      (toTensorBaseChanges (S := S) M f).comp (TensorProduct.rid R M).toLinearMap := by
    apply TensorProduct.ext'
    intro m r
    apply Prod.ext
    · simp [e, a, toTensorBaseChanges]
      simpa [Algebra.smul_def] using (TensorProduct.tmul_smul r m (1 : S))
    · simp [e, a, toTensorBaseChanges]
      simpa [Algebra.smul_def] using
        (TensorProduct.tmul_smul r m (1 : Localization.Away f))
  have heb : b.lTensor M = (tensorAwayDifference (S := S) M f).comp e.toLinearMap := by
    apply TensorProduct.ext'
    intro m z
    simp [b, c, d, e, tensorAwayDifference, TensorProduct.tmul_add,
      TensorProduct.tmul_neg]
  have het := lTensor_exact M he hb
  have hbt := LinearMap.lTensor_surjective M hb
  constructor
  · rw [module_sequence_exact_iff]
    intro z
    constructor
    · intro hz
      have hz' : b.lTensor M (e.symm z) = 0 := by
        simp only [heb, LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply, hz]
      obtain ⟨x, hx⟩ := (het _).mp hz'
      refine ⟨TensorProduct.rid R M x, ?_⟩
      have heax := LinearMap.congr_fun hea x
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx, e.apply_symm_apply] using heax.symm
    · rintro ⟨m, rfl⟩
      change tensorAwayDifference M f (toTensorBaseChanges M f m) = 0
      simp [toTensorBaseChanges, tensorAwayDifference]
  · rw [AddCommGrpCat.epi_iff_surjective]
    change Function.Surjective (ULift.map (tensorAwayDifference (S := S) M f))
    rw [ULift.map_surjective]
    intro z
    obtain ⟨x, hx⟩ := hbt z
    exact ⟨e x, by simpa only [heb, LinearMap.comp_apply, LinearEquiv.coe_coe] using hx⟩

private theorem module_sequence_shortExact_iff_of_ring
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] (f : R)
    (hs : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact) :
    (beauvilleLaszloModuleSequence (S := S) M f).ShortExact ↔
      Function.Injective (tensorProductPowerTorsionMap (S := S) M f) := by
  obtain ⟨he, hg⟩ := module_sequence_exact_epi_of_ring M f hs
  constructor
  · intro h
    exact (module_sequence_mono_iff M f).mp h.mono_f
  · intro h
    exact ShortComplex.ShortExact.mk' he ((module_sequence_mono_iff M f).mpr h) hg

/-- If `R → S` is an isomorphism modulo every positive power of `f`, the module
Beauville--Laszlo sequence is surjective on the right; its left and middle exactness
are equivalent to injectivity and surjectivity of the canonical map on `f`-power torsion.
Thus the module is glueable exactly when this map is bijective. If the ring sequence is
short exact, surjectivity on power torsion is automatic, so injectivity alone characterizes
glueability. The latter criterion also applies to the `(f)`-adic completion. -/
@[stacks 0BNW]
public theorem beauvilleLaszloModuleSequence_exactness_iff_powerTorsionMap :
    (∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
      (M : Type w) [AddCommGroup M] [Module R M] (f : R),
      (∀ n : ℕ, 0 < n → Function.Bijective
        (quotientPowMap f n (algebraMap R S))) →
      Epi (beauvilleLaszloModuleSequence (S := S) M f).g ∧
        (Mono (beauvilleLaszloModuleSequence (S := S) M f).f ↔
          Function.Injective (tensorProductPowerTorsionMap (S := S) M f)) ∧
        ((beauvilleLaszloModuleSequence (S := S) M f).Exact ↔
          Function.Surjective (tensorProductPowerTorsionMap (S := S) M f)) ∧
        ((beauvilleLaszloModuleSequence (S := S) M f).ShortExact ↔
          Function.Bijective (tensorProductPowerTorsionMap (S := S) M f)) ∧
        ((beauvilleLaszloSequence f (algebraMap R S)).ShortExact →
          ((beauvilleLaszloModuleSequence (S := S) M f).ShortExact ↔
            Function.Injective (tensorProductPowerTorsionMap (S := S) M f)))) ∧
    (∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M] (f : R),
      (beauvilleLaszloSequence f
          (algebraMap R (AdicCompletion (Ideal.span {f}) R))).ShortExact →
        ((beauvilleLaszloModuleSequence
            (S := AdicCompletion (Ideal.span {f}) R) M f).ShortExact ↔
          Function.Injective
            (tensorProductPowerTorsionMap
              (S := AdicCompletion (Ideal.span {f}) R) M f))) := by
  constructor
  · intro R S _ _ _ M _ _ f h
    let u : M →ₗ[R] TensorProduct R M S := (TensorProduct.mk R M S).flip 1
    let v : M →ₗ[R] TensorProduct R M (Localization.Away f) :=
      (TensorProduct.mk R M (Localization.Away f)).flip 1
    let p := baseChangeToAway (S := S) M f
    let q := localizedBaseChangeToAway (S := S) M f
    have hc : p.comp u = q.comp v := by
      ext m
      simp [p, q, u, v]
    have hv : IsLocalizedModule.Away f v := isLocalizedModule_tensor_away M f
    have hp : IsLocalizedModule.Away f p := by
      let c := (IsScalarTower.toAlgHom R S
        (Localization.Away (algebraMap R S f))).toLinearMap
      let : IsLocalizedModule.Away f c := isLocalizedModule_scalar_away f
      exact isLocalizedModule_lTensor (Submonoid.powers f) c
    have hsurj : ∀ n : ℕ, 0 < n → ∀ b : TensorProduct R M S,
        ∃ a : M, ∃ b' : TensorProduct R M S, b = u a + f ^ n • b' := by
      intro n hn b
      exact tensorProduct_mod_power_decomposition M f n (h n hn).2 b
    have hinj : ∀ n : ℕ, 0 < n → ∀ a : M,
        (∃ b : TensorProduct R M S, u a = f ^ n • b) → ∃ a' : M, a = f ^ n • a' := by
      rintro n hn a ⟨b, hb⟩
      exact tensorProduct_mod_power_injective M f n (h n hn) a b hb
    obtain ⟨hepi, _, hex⟩ := localization_square_exactness f u v p q hc hv hp hsurj hinj
    have hepi' : Epi (beauvilleLaszloModuleSequence (S := S) M f).g := by
      rw [AddCommGrpCat.epi_iff_surjective]
      exact ULift.map_surjective.mpr hepi
    have hmono := module_sequence_mono_iff (S := S) M f
    have hex' : (beauvilleLaszloModuleSequence (S := S) M f).Exact ↔
        Function.Surjective (tensorProductPowerTorsionMap (S := S) M f) := by
      rw [module_sequence_exact_iff, torsionMap_surjective_iff]
      exact hex
    refine ⟨hepi', hmono, hex', ?_, module_sequence_shortExact_iff_of_ring M f⟩
    constructor
    · intro hs
      exact ⟨hmono.mp hs.mono_f, hex'.mp hs.exact⟩
    · intro hb
      exact ShortComplex.ShortExact.mk' (hex'.mpr hb.2) (hmono.mpr hb.1) hepi'
  · intro R _ M _ _ f hs
    exact module_sequence_shortExact_iff_of_ring M f hs

end

end BeauvilleLaszlo

end
