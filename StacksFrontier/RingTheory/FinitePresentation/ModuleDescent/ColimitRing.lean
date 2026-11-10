module

public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent.ModuleColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Colimits and maps of finite presentation: the colimit ring and descent of surjectivity

For a directed system of `A`-algebras `R_i` with a cocone `ψ_i : R_i → S`, we build the
direct limit ring `B = colim_i R_i` with its `A`-algebra structure and the induced map
`χ : B → S`. When `χ` is bijective, tensoring with any `A`-module `P` commutes with the
colimit, `S ⊗_A P = colim_i (R_i ⊗_A P)`. Combined with a Nakayama argument at primes,
this gives the descent of surjectivity of base-changed maps.

## Main results

* `nakayama_descent`: prime-localization Nakayama for finite modules over `B`.
* `lambda_bijective`: the map `B ⊗_A P → S ⊗_A P` is bijective when `χ` is.
* `isModuleColimit_of_χ_bijective`: tensoring a directed colimit of rings with a module gives
  the directed colimit of the base changes.
* `statement_two`: if `N` is finite and `u : M → N` becomes surjective after base change
  to `R`, it is surjective after base change to some `R_i`.
-/

@[expose] public section

universe u v

@[expose] public section


open scoped TensorProduct

namespace Stacks.FinitePresentation.ColimitDescent

section Statements

variable {A : Type*} [CommRing A]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable {S : Type*} [CommRing S] [Algebra A S]
variable (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
variable (ψ : ∀ i, R i →ₐ[A] S)

/-! ### The colimit ring `B = colim_i R_i`

We build the direct limit ring `B := Ring.DirectLimit R (transFun φ)`, equip it with
an `A`-algebra structure compatible with all the `R_i`, the canonical `A`-algebra maps
`βAlg i : R i →ₐ[A] B`, and the induced `A`-algebra map `χ : B →ₐ[A] S` with
`χ ∘ βAlg i = ψ i`. -/

/-- The raw transition function for `Ring.DirectLimit`. -/
noncomputable def transFun : (i j : ι) → i ≤ j → R i → R j :=
  fun _ _ h => (φ h)

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- `DirectedSystem` instance from the `TransitionSystem` laws. -/
lemma directedSystem (htrans : TransitionSystem φ) :
    DirectedSystem R (transFun φ) where
  map_self := fun {i} x => htrans.refl i x
  map_map := fun {_ _ _} hij hjk x => htrans.trans hij hjk x

/-- The colimit ring `B := colim_i R_i`. -/
abbrev B : Type _ := Ring.DirectLimit R (transFun φ)

/-- Canonical ring maps `β i : R i →+* B`. -/
noncomputable abbrev β (i : ι) : R i →+* B φ := Ring.DirectLimit.of R (transFun φ) i

omit [Nonempty ι] in
/-- The composite `R i → B` sends `algebraMap A (R i) a` to a value independent of `i`. -/
lemma β_algebraMap_eq (i i' : ι) (a : A) :
    β φ i (algebraMap A (R i) a) = β φ i' (algebraMap A (R i') a) := by
  obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i i'
  have e : ∀ j (hjk : j ≤ k),
      β φ j (algebraMap A (R j) a) = β φ k (algebraMap A (R k) a) := by
    intro j hjk
    rw [← Ring.DirectLimit.of_f (G := R) (f := transFun φ) hjk (algebraMap A (R j) a)]
    congr 1
    change (φ hjk) (algebraMap A (R j) a) = algebraMap A (R k) a
    rw [AlgHom.commutes]
  rw [e i hik, e i' hi'k]

/-- The structure `A`-algebra map into `B`, via a basepoint. -/
noncomputable def algMapB : A →+* B φ :=
  (β φ (Classical.arbitrary ι)).comp (algebraMap A (R (Classical.arbitrary ι)))

/-- The `A`-algebra structure on `B` given by `algMapB`. -/
noncomputable instance algebraB : Algebra A (B φ) :=
  (algMapB φ).toAlgebra

/-- The structure map `A → B` agrees with `A → R_i → B` for every index `i`. -/
lemma algebraMap_B_eq (i : ι) (a : A) :
    algebraMap A (B φ) a = β φ i (algebraMap A (R i) a) := by
  change algMapB φ a = _
  unfold algMapB
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact β_algebraMap_eq φ _ i a

/-- `β i` is an `A`-algebra map. -/
noncomputable def βAlg (i : ι) : R i →ₐ[A] B φ where
  toRingHom := β φ i
  commutes' := fun a => by
    change β φ i (algebraMap A (R i) a) = algebraMap A (B φ) a
    rw [algebraMap_B_eq φ i a]

/-- The induced ring map `χ : B →+* S` from the cocone `ψ`. -/
noncomputable def χRing (hcocone : IsCoconeAlg φ ψ) : B φ →+* S :=
  Ring.DirectLimit.lift R (transFun φ) S (fun i => (ψ i).toRingHom)
    (fun _ _ hij x => hcocone hij x)

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- `χRing` restricted along `β i` is the cocone map `ψ i`. -/
@[simp] lemma χRing_β (hcocone : IsCoconeAlg φ ψ) (i : ι) (x : R i) :
    χRing φ ψ hcocone (β φ i x) = ψ i x :=
  Ring.DirectLimit.lift_of _ _ _ _ _

/-- The induced `A`-algebra map `χ : B →ₐ[A] S` with `χ ∘ βAlg i = ψ i`. -/
noncomputable def χ (hcocone : IsCoconeAlg φ ψ) : B φ →ₐ[A] S where
  toRingHom := χRing φ ψ hcocone
  commutes' := fun a => by
    change χRing φ ψ hcocone (algebraMap A (B φ) a) = algebraMap A S a
    rw [algebraMap_B_eq φ (Classical.arbitrary ι) a, χRing_β, AlgHom.commutes]

/-- `χ` restricted along `βAlg i` is the cocone map `ψ i`. -/
@[simp] lemma χ_βAlg (hcocone : IsCoconeAlg φ ψ) (i : ι) (x : R i) :
    χ φ ψ hcocone (βAlg φ i x) = ψ i x :=
  χRing_β φ ψ hcocone i x

/-- **The map out of the direct limit is bijective when the target is detected at stages.**
If every element of `S` is the image of an element of some `R_i`, and two elements of an `R_i`
with the same image in `S` are already identified by a transition map, then
`χ : colim_i R_i → S` is bijective. -/
lemma χ_bijective_of_colimit_data (hcocone : IsCoconeAlg φ ψ)
    (hrep : ∀ s : S, ∃ (i : ι) (r : R i), ψ i r = s)
    (heq : ∀ (i : ι) (r t : R i), ψ i r = ψ i t →
      ∃ (j : ι) (hij : i ≤ j), φ hij r = φ hij t) :
    Function.Bijective (χ φ ψ hcocone) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨i, r, hr⟩ := Ring.DirectLimit.exists_of b
    obtain ⟨j, hij, hj⟩ := heq i r 0 (by
      rw [← χ_βAlg φ ψ hcocone i r, show βAlg φ i r = b from hr, hb, map_zero])
    rw [← hr, ← Ring.DirectLimit.of_f (G := R) (f := transFun φ) hij r]
    change β φ j (φ hij r) = 0
    rw [show φ hij r = 0 by simpa using hj, map_zero]
  · intro s
    obtain ⟨i, r, hr⟩ := hrep s
    exact ⟨βAlg φ i r, by rw [χ_βAlg, hr]⟩

/-- **Nakayama at a prime.** If `M` is a finite `B`-module whose localization at the
prime `𝔭` is nonzero, then the residue-field tensor `k ⊗[B] M` is nonzero, where
`k = ResidueField (B_𝔭)`. -/
@[ega "IV 2.5.5.4" "more general"]
private lemma residueField_tensor_nontrivial
    {B : Type*} [CommRing B] (𝔭 : Ideal B) [𝔭.IsPrime]
    {M : Type*} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hM : Nontrivial (LocalizedModule 𝔭.primeCompl M)) :
    Nontrivial ((IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) ⊗[B] M) := by
  set Bp := Localization.AtPrime 𝔭
  set k := IsLocalRing.ResidueField Bp
  set Mp := LocalizedModule 𝔭.primeCompl M
  have hfin : Module.Finite Bp Mp :=
    Module.Finite.of_isLocalizedModule 𝔭.primeCompl (LocalizedModule.mkLinearMap 𝔭.primeCompl M)
  -- Nakayama: 𝔪 • ⊤ ≠ ⊤
  have hnak : (IsLocalRing.maximalIdeal Bp) • (⊤ : Submodule Bp Mp) ≠ ⊤ := by
    intro h
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤ Module.Finite.fg_top h.ge
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal Bp) bot_ne_top).ge
    rw [Submodule.eq_bot_iff] at hbot
    obtain ⟨a, b, hab⟩ := (exists_pair_ne Mp)
    exact hab (by rw [hbot a (Submodule.mem_top), hbot b (Submodule.mem_top)])
  -- Mp / 𝔪 Mp nontrivial
  have hquot : Nontrivial (Mp ⧸ (IsLocalRing.maximalIdeal Bp) • (⊤ : Submodule Bp Mp)) :=
    Submodule.Quotient.nontrivial_iff.mpr hnak
  -- iso chain transferring nontriviality back to k ⊗[B] M
  have e1 : (k ⊗[Bp] Mp) ≃ₗ[Bp]
      (Mp ⧸ (IsLocalRing.maximalIdeal Bp) • (⊤ : Submodule Bp Mp)) :=
    TensorProduct.quotTensorEquivQuotSMul Mp (IsLocalRing.maximalIdeal Bp)
  have e2 : Mp ≃ₗ[Bp] (Bp ⊗[B] M) := LocalizedModule.equivTensorProduct 𝔭.primeCompl M
  have e3 : (k ⊗[Bp] (Bp ⊗[B] M)) ≃ₗ[k] (k ⊗[B] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B Bp k k M
  have h1 : Nontrivial (k ⊗[Bp] Mp) := e1.toEquiv.nontrivial
  have h2 : Nontrivial (k ⊗[Bp] (Bp ⊗[B] M)) :=
    (LinearEquiv.lTensor k e2).toEquiv.symm.nontrivial
  exact e3.toEquiv.symm.nontrivial

/-- **Base change distributes over tensor products** (as a bijection).
`(k ⊗[B] S) ⊗[k] (k ⊗[B] X) ≃ k ⊗[B] (S ⊗[B] X)`. -/
private noncomputable def baseChangeTensorEquiv
    {B : Type*} [CommRing B] {k : Type*} [CommRing k] [Algebra B k]
    {S : Type*} [AddCommGroup S] [Module B S]
    {X : Type*} [AddCommGroup X] [Module B X] :
    ((k ⊗[B] S) ⊗[k] (k ⊗[B] X)) ≃ (k ⊗[B] (S ⊗[B] X)) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange B k k (k ⊗[B] S) X).toEquiv.trans
    (TensorProduct.assoc B k S X).toEquiv

/-- **Prime-localization Nakayama (no local-ring hypothesis).**
`B` a commutative ring, `S` a `B`-algebra.  `P` a finite `B`-module whose unit map
`P → S ⊗[B] P` (`p ↦ 1 ⊗ p`) is bijective.  `Q` a quotient of `P` with `S ⊗[B] Q`
a subsingleton.  Then `Q` is a subsingleton. -/
lemma nakayama_descent
    {B : Type*} [CommRing B]
    {S : Type*} [CommRing S] [Algebra B S]
    {P : Type*} [AddCommGroup P] [Module B P] [Module.Finite B P]
    {Q : Type*} [AddCommGroup Q] [Module B Q]
    (f : P →ₗ[B] Q) (hf : Function.Surjective f)
    (hPiso : Function.Bijective (fun p : P => (1 : S) ⊗ₜ[B] p))
    (hSQ : Subsingleton (S ⊗[B] Q)) :
    Subsingleton Q := by
  -- suppose not
  by_contra hQ
  rw [not_subsingleton_iff_nontrivial] at hQ
  -- support is nonempty
  have hsupp : Module.support B Q ≠ ∅ := by
    rw [Ne, Module.support_eq_empty_iff]
    exact not_subsingleton_iff_nontrivial.mpr hQ
  obtain ⟨𝔭, h𝔭⟩ := Set.nonempty_iff_ne_empty.mpr hsupp
  -- Q is finite (quotient of finite P)
  have : Module.Finite B Q := Module.Finite.of_surjective f hf
  -- nonzero localized module of Q
  have hQp : Nontrivial (LocalizedModule 𝔭.asIdeal.primeCompl Q) :=
    Module.mem_support_iff.mp h𝔭
  set k := IsLocalRing.ResidueField (Localization.AtPrime 𝔭.asIdeal)
  -- kQ nonzero
  have hkQ : Nontrivial (k ⊗[B] Q) := residueField_tensor_nontrivial 𝔭.asIdeal hQp
  -- kP nonzero (surjects onto kQ)
  have hkP : Nontrivial (k ⊗[B] P) := (LinearMap.lTensor_surjective k hf).nontrivial
  -- φ : P ≃ₗ[B] S ⊗[B] P
  let φ : P ≃ₗ[B] (S ⊗[B] P) := LinearEquiv.ofBijective (TensorProduct.mk B S P 1) hPiso
  -- base change φ to k: k⊗P ≃ k⊗(S⊗P)
  have hkSP : Nontrivial (k ⊗[B] (S ⊗[B] P)) :=
    (LinearEquiv.lTensor k φ).toEquiv.symm.nontrivial
  -- so (kS) ⊗[k] (kP) nonzero
  have hkSkP : Nontrivial ((k ⊗[B] S) ⊗[k] (k ⊗[B] P)) :=
    (baseChangeTensorEquiv (B := B) (k := k) (S := S) (X := P)).nontrivial
  -- hence kS nonzero
  have hkS : Nontrivial (k ⊗[B] S) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left k (k ⊗[B] S)).mp hkSkP
  -- now contradiction with hSQ
  -- transfer to (kS) ⊗[k] (kQ)
  have hss : Subsingleton ((k ⊗[B] S) ⊗[k] (k ⊗[B] Q)) :=
    (baseChangeTensorEquiv (B := B) (k := k) (S := S) (X := Q)).subsingleton
  -- but (kS) ⊗[k] (kQ) is nontrivial since both factors are
  have hnt : Nontrivial ((k ⊗[B] S) ⊗[k] (k ⊗[B] Q)) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right k (k ⊗[B] S)).mpr hkQ
  exact not_subsingleton_iff_nontrivial.mpr hnt hss

/-- `χ ⊗ id` after `βAlg i ⊗ id` is the canonical map `canonMod ψ P i`. -/
private lemma map_χ_map_βAlg (hcocone : IsCoconeAlg φ ψ)
    {P : Type*} [AddCommGroup P] [Module A P] (i : ι) (y : (R i) ⊗[A] P) :
    TensorProduct.map (χ φ ψ hcocone).toLinearMap (LinearMap.id (R := A) (M := P))
        (TensorProduct.map (βAlg φ i).toLinearMap (LinearMap.id (R := A) (M := P)) y) =
      canonMod ψ P i y := by
  induction y using TensorProduct.inductionOn with
  | tmul r p =>
      change (χ φ ψ hcocone (βAlg φ i r)) ⊗ₜ[A] p = (ψ i r) ⊗ₜ[A] p
      rw [χ_βAlg]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `βAlg ⊗ id` is compatible with the transition maps `transMod`. -/
private lemma map_βAlg_transMod
    {P : Type*} [AddCommGroup P] [Module A P] {i j : ι} (hij : i ≤ j) (y : (R i) ⊗[A] P) :
    TensorProduct.map (βAlg φ j).toLinearMap (LinearMap.id (R := A) (M := P))
        (transMod φ P hij y) =
      TensorProduct.map (βAlg φ i).toLinearMap (LinearMap.id (R := A) (M := P)) y := by
  induction y using TensorProduct.inductionOn with
  | tmul r p =>
      change (βAlg φ j (φ hij r)) ⊗ₜ[A] p = (βAlg φ i r) ⊗ₜ[A] p
      exact congrArg (fun b => b ⊗ₜ[A] p) (Ring.DirectLimit.of_f hij r)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Every element of `B φ ⊗[A] P` comes from some `R i ⊗[A] P`. -/
private lemma exists_map_βAlg_eq
    {P : Type*} [AddCommGroup P] [Module A P] (t : (B φ) ⊗[A] P) :
    ∃ (i : ι) (y : (R i) ⊗[A] P),
      TensorProduct.map (βAlg φ i).toLinearMap (LinearMap.id (R := A) (M := P)) y = t := by
  induction t using TensorProduct.inductionOn with
  | tmul b p =>
      obtain ⟨i, r, hr⟩ := Ring.DirectLimit.exists_of b
      exact ⟨i, r ⊗ₜ[A] p, congrArg (fun z => z ⊗ₜ[A] p) hr⟩
  | add x y hx hy =>
      obtain ⟨i, a, ha⟩ := hx
      obtain ⟨j, b, hb⟩ := hy
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      exact ⟨k, transMod φ P hik a + transMod φ P hjk b, by
        rw [map_add, map_βAlg_transMod, map_βAlg_transMod, ha, hb]⟩

/-- The `A`-linear map `λ_P : B ⊗[A] P → S ⊗[A] P`
induced by `χ : B →ₐ[A] S` (i.e. `χ ⊗ id_P`) is bijective, whenever `P` has the
colimit property `hcolim : IsModuleColimit φ ψ P`.  Equivalently `B ⊗[A] P ≅ S ⊗[A] P`.
This uses the identification `B ⊗[A] P = colim_i (R_i ⊗[A] P)` (tensor commutes with
the directed colimit `B = colim_i R_i`) together with the two pieces of the
`IsModuleColimit` API (joint surjectivity + the equalizer/zero criterion). -/
lemma lambda_bijective
    (hcocone : IsCoconeAlg φ ψ)
    {P : Type*} [AddCommGroup P] [Module A P]
    (hcolim : IsModuleColimit φ ψ P) :
    Function.Bijective
      (TensorProduct.map (χ φ ψ hcocone).toLinearMap (LinearMap.id (R := A) (M := P))) := by
  classical
  -- Now assemble bijectivity.
  constructor
  · -- Injectivity.
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨i, y, rfl⟩ := exists_map_βAlg_eq φ t
    -- `canonMod ψ P i y = 0`.
    have hcm : canonMod ψ P i y = canonMod ψ P i 0 := by
      rwa [map_zero, ← map_χ_map_βAlg φ ψ hcocone i y]
    obtain ⟨j, hij, hj⟩ := hcolim.exists_eq_of_canonMod_eq i y 0 hcm
    rw [map_zero] at hj
    rw [← map_βAlg_transMod φ hij, hj, map_zero]
  · -- Surjectivity.
    intro x
    obtain ⟨i, y, hy⟩ := hcolim.jointly_surjective x
    exact ⟨TensorProduct.map (βAlg φ i).toLinearMap LinearMap.id y,
      by rw [map_χ_map_βAlg, hy]⟩

/-- The linearized transition maps `(φ h).toLinearMap : R i →ₗ[A] R j`. -/
private noncomputable def transLin : (i j : ι) → i ≤ j → R i →ₗ[A] R j :=
  fun _ _ h => (φ h).toLinearMap

/-- `B φ` (the ring direct limit) is `A`-linearly isomorphic to the module direct
limit of the `R i` along the linearized transition maps. -/
private noncomputable def bModuleEquiv (htrans : TransitionSystem φ) [DecidableEq ι] :
    Module.DirectLimit R (transLin φ) ≃ₗ[A] B φ := by
  classical
  haveI := directedSystem φ htrans
  -- forward map via the universal property of the module direct limit
  refine LinearEquiv.ofBijective
    (Module.DirectLimit.lift A ι R (transLin φ) (fun i => (βAlg φ i).toLinearMap) ?_) ?_
  · intro i j hij x
    change β φ j ((transFun φ i j hij) x) = βAlg φ i x
    rw [Ring.DirectLimit.of_f]
    rfl
  constructor
  · -- injective
    rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
        rw [Module.DirectLimit.lift_of] at hz
        have hz' : (Ring.DirectLimit.of R (transFun φ) i) x = 0 := hz
        have : DirectedSystem R (fun i j h => ⇑((φ h).toRingHom)) := directedSystem φ htrans
        obtain ⟨j, hij, hj⟩ :=
          Ring.DirectLimit.of.zero_exact (f' := fun i j h => (φ h).toRingHom) hz'
        rw [← Module.DirectLimit.of_f (hij := hij)]
        change (Module.DirectLimit.of A ι R (transLin φ) j) ((φ hij) x) = 0
        rw [show (φ hij) x = 0 from hj, map_zero]
  · -- surjective
    intro b
    obtain ⟨i, x, hx⟩ := Ring.DirectLimit.exists_of b
    refine ⟨Module.DirectLimit.of A ι R (transLin φ) i x, ?_⟩
    rwa [Module.DirectLimit.lift_of]

-- needed: `tensor_zero_exact`'s `rw [LinearEquiv.ofBijective_apply]` only matches after
-- `βAlg φ i` is unfolded past `Module.DirectLimit.lift`, i.e. non-transparently.
set_option backward.isDefEq.respectTransparency false in
/-- Zero-exactness of `B φ ⊗[A] C = colim_i (R i ⊗[A] C)`: if `(βAlg φ i ⊗ id) x = 0`
in `B φ ⊗[A] C`, then `x` already dies after a transition map. -/
private lemma tensor_zero_exact (htrans : TransitionSystem φ)
    {C : Type*} [AddCommGroup C] [Module A C] (i : ι) (x : (R i) ⊗[A] C)
    (hx : TensorProduct.map (βAlg φ i).toLinearMap (LinearMap.id (R := A) (M := C)) x = 0) :
    ∃ (j : ι) (hij : i ≤ j), transMod φ C hij x = 0 := by
  classical
  have := directedSystem φ htrans
  -- the equiv B φ ⊗ C ≃ DirectLimit (R · ⊗ C)
  set bE := bModuleEquiv φ htrans with hbE
  -- equiv: B φ ⊗ C ≃ₗ (DirectLimit R transLin) ⊗ C
  set e1 : (B φ) ⊗[A] C ≃ₗ[A] (Module.DirectLimit R (transLin φ)) ⊗[A] C :=
    (TensorProduct.congr bE.symm (LinearEquiv.refl A C))
  -- equiv: (DirectLimit R transLin) ⊗ C ≃ DirectLimit (R · ⊗ C) (rTensor)
  set e2 := TensorProduct.directLimitLeft (transLin φ) C with he2
  -- the DirectLimit of (R · ⊗ C) along rTensor
  -- key: transMod φ C hij = rTensor C (transLin φ i j hij)
  have htm : ∀ ⦃i j : ι⦄ (hij : i ≤ j),
      transMod φ C hij = LinearMap.rTensor C (transLin φ i j hij) :=
    fun _ _ _ => TensorProduct.ext' fun _ _ => rfl
  -- δ_i x corresponds under e2 ∘ e1 to of i x
  -- Compute: e1 (δ_i x) and then e2.
  -- We show (e2 (e1 (δ_i x))) = Module.DirectLimit.of A ι (R · ⊗ C) (rTensor) i x
  have hcompose : ∀ y : (R i) ⊗[A] C,
      e2 (e1 (TensorProduct.map (βAlg φ i).toLinearMap (LinearMap.id (R := A) (M := C)) y))
        = Module.DirectLimit.of A ι (fun k => (R k) ⊗[A] C)
            (fun i j h => LinearMap.rTensor C (transLin φ i j h)) i y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul r c =>
        change e2 (e1 ((βAlg φ i r) ⊗ₜ[A] c)) = _
        have hbeta : bE.symm (βAlg φ i r) = Module.DirectLimit.of A ι R (transLin φ) i r := by
          rw [hbE, LinearEquiv.symm_apply_eq, bModuleEquiv, LinearEquiv.ofBijective_apply,
            Module.DirectLimit.lift_of]
          rfl
        change e2 ((bE.symm (βAlg φ i r)) ⊗ₜ[A] c) = _
        rw [hbeta, he2, TensorProduct.directLimitLeft_tmul_of]
    | add y z hy hz => simp only [map_add, hy, hz]
  -- Now apply zero-exactness in the module direct limit.
  have hzero : Module.DirectLimit.of A ι (fun k => (R k) ⊗[A] C)
      (fun i j h => LinearMap.rTensor C (transLin φ i j h)) i x = 0 := by
    rw [← hcompose x, hx, map_zero, map_zero]
  have : DirectedSystem (fun k => (R k) ⊗[A] C)
      (fun i j h => ⇑(LinearMap.rTensor C (transLin φ i j h))) := by
    constructor
    · intro i y
      change LinearMap.rTensor C (transLin φ i i (le_refl i)) y = y
      induction y using TensorProduct.inductionOn with
      | tmul r c =>
          rw [LinearMap.rTensor_tmul]
          change ((φ (le_refl i)) r) ⊗ₜ[A] c = r ⊗ₜ[A] c
          rw [htrans.refl i r]
      | add a b ha hb => simp only [map_add, ha, hb]
    · intro k j i hij hjk y
      induction y using TensorProduct.inductionOn with
      | tmul r c =>
          change LinearMap.rTensor C (transLin φ j k hjk)
              (LinearMap.rTensor C (transLin φ i j hij) (r ⊗ₜ[A] c))
            = LinearMap.rTensor C (transLin φ i k (le_trans hij hjk)) (r ⊗ₜ[A] c)
          rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
          change ((φ hjk) ((φ hij) r)) ⊗ₜ[A] c = ((φ (le_trans hij hjk)) r) ⊗ₜ[A] c
          rw [htrans.trans hij hjk r]
      | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hzero
  exact ⟨j, hij, by rwa [htm hij]⟩

/-- **Tensoring a directed colimit of rings with a module gives the directed colimit of the
base changes.**  If the canonical map `colim_i R_i → S` is bijective, then every `A`-module `P`
has the colimit property `IsModuleColimit φ ψ P`: the maps `R_i ⊗_A P → S ⊗_A P` are jointly
surjective and detect equality up to a transition map. -/
lemma isModuleColimit_of_χ_bijective (htrans : TransitionSystem φ) (hcocone : IsCoconeAlg φ ψ)
    (hχ : Function.Bijective (χ φ ψ hcocone))
    (P : Type*) [AddCommGroup P] [Module A P] : IsModuleColimit φ ψ P := by
  classical
  let δ (i : ι) : (R i) ⊗[A] P →ₗ[A] (B φ) ⊗[A] P :=
    TensorProduct.map (βAlg φ i).toLinearMap LinearMap.id
  let Λ : (B φ) ⊗[A] P →ₗ[A] S ⊗[A] P :=
    TensorProduct.map (χ φ ψ hcocone).toLinearMap LinearMap.id
  have hΛbij : Function.Bijective Λ :=
    (TensorProduct.congr (LinearEquiv.ofBijective (χ φ ψ hcocone).toLinearMap hχ)
      (LinearEquiv.refl A P)).bijective
  constructor
  · intro x
    obtain ⟨t, rfl⟩ := hΛbij.2 x
    obtain ⟨i, y, rfl⟩ := exists_map_βAlg_eq φ t
    exact ⟨i, y, (map_χ_map_βAlg φ ψ hcocone i y).symm⟩
  · intro i y z hyz
    have hδeq : δ i y = δ i z := hΛbij.1
      ((map_χ_map_βAlg φ ψ hcocone i y).trans (hyz.trans (map_χ_map_βAlg φ ψ hcocone i z).symm))
    have hzero : δ i (y - z) = 0 := by rw [map_sub, hδeq, sub_self]
    obtain ⟨j, hij, hj⟩ := tensor_zero_exact φ htrans i (y - z) hzero
    exact ⟨j, hij, by rwa [map_sub, sub_eq_zero] at hj⟩

/-- **Core descent lemma for (2)**, the colimit-ring part of the argument.
Given the colimit property for the finite module `N` and a *finite* quotient
`C` of `N` whose base change to `S` vanishes, the base change of `C` to some
`R_i` already vanishes.

Proof outline.
Let `B := colim_i R_i` be the direct limit of the `A`-algebras `R_i`
(it exists as a commutative `A`-algebra, `Ring.DirectLimit`, even though it is
not named in the hypotheses); the `ψ_i` induce `χ : B →ₐ[A] S`.  Tensor commutes
with the directed colimit (`TensorProduct.directLimitRight`), so
`B ⊗[A] N = colim_i (R_i ⊗[A] N)`.  The colimit property `hcolimN`
(joint surjectivity + equalizer) identifies this colimit with `S ⊗[A] N`, i.e.
`λ_N : B ⊗[A] N ≃ₗ S ⊗[A] N` (induced by `χ`).  Set `P := B ⊗[A] N`
(finite `B`-module), `Q := B ⊗[A] C` (a quotient of `P`).  Via `λ_N` and tensor
cancellation `S ⊗[B] (B ⊗[A] N) ≃ S ⊗[A] N`, the unit map `P → S ⊗[B] P` is an
isomorphism, while `S ⊗[B] Q ≃ S ⊗[A] C = 0`.  A prime-localization Nakayama
argument (NO local-ring assumption: localize at a prime where `Q ≠ 0`, reduce
mod the maximal ideal, derive a contradiction from `S/𝔪S ≠ 0` and
`(S/𝔪S) ⊗ (Q/𝔪Q) = 0`) gives `Q = B ⊗[A] C = 0`.  Finally, `C` finite and
`B ⊗ C = colim (R_i ⊗ C) = 0` forces each generator `1 ⊗ c_k` to die at a finite
stage; a common upper bound `j` gives `R_j ⊗ C = 0`. -/
lemma statement_two_coker_descend
    (htrans : TransitionSystem φ) (hcocone : IsCoconeAlg φ ψ)
    {C : Type*} [AddCommGroup C] [Module A C]
    (hcolimN : IsModuleColimit φ ψ N)
    (hN : Module.Finite A N)
    (q : N →ₗ[A] C) (hq : Function.Surjective q)
    (hSC : Subsingleton (S ⊗[A] C)) :
    ∃ i : ι, Subsingleton ((R i) ⊗[A] C) := by
  classical
  -- Give `S` the `B φ`-algebra structure via `χ`.
  let : Algebra (B φ) S := (χ φ ψ hcocone).toRingHom.toAlgebra
  have halg : ∀ b : B φ, algebraMap (B φ) S b = χ φ ψ hcocone b := fun _ => rfl
  have : IsScalarTower A (B φ) S :=
    IsScalarTower.of_algebraMap_eq fun a => ((χ φ ψ hcocone).commutes a).symm
  -- Finite module instances.
  have : Module.Finite A N := hN
  have : Module.Finite (B φ) ((B φ) ⊗[A] N) := Module.Finite.base_change A (B φ) N
  -- Step 5 target: B φ ⊗ C subsingleton.
  have hBC : Subsingleton ((B φ) ⊗[A] C) := by
    -- the cancellation isos
    set cN : (S ⊗[B φ] ((B φ) ⊗[A] N)) ≃ₗ[S] (S ⊗[A] N) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange A (B φ) S S N with hcN
    set cC : (S ⊗[B φ] ((B φ) ⊗[A] C)) ≃ₗ[S] (S ⊗[A] C) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange A (B φ) S S C with hcC
    -- Λ_N : B φ ⊗ N → S ⊗ N
    set ΛN : (B φ) ⊗[A] N →ₗ[A] S ⊗[A] N :=
      TensorProduct.map (χ φ ψ hcocone).toLinearMap (LinearMap.id (R := A) (M := N)) with hΛN
    have hΛNbij : Function.Bijective ΛN := lambda_bijective φ ψ hcocone hcolimN
    -- f := baseChange q surjective
    have hfsurj : Function.Surjective (LinearMap.baseChange (B φ) q) :=
      LinearMap.baseChange_surjective (B φ) hq
    -- hSQ: S ⊗[B φ] (B φ ⊗ C) subsingleton via cC and hSC
    have hSQ : Subsingleton (S ⊗[B φ] ((B φ) ⊗[A] C)) := cC.toEquiv.subsingleton
    -- hPiso: unit map p ↦ (1:S) ⊗ₜ[B φ] p bijective
    have hunit_eq : ∀ p : (B φ) ⊗[A] N,
        cN ((1 : S) ⊗ₜ[B φ] p) = ΛN p := by
      intro p
      induction p using TensorProduct.inductionOn with
      | tmul b n =>
          rw [hcN, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
          change (b • (1 : S)) ⊗ₜ[A] n = (χ φ ψ hcocone b) ⊗ₜ[A] n
          rw [Algebra.smul_def, halg, mul_one]
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
    have hPiso : Function.Bijective (fun p : (B φ) ⊗[A] N => (1 : S) ⊗ₜ[B φ] p) := by
      have hcomp : (fun p : (B φ) ⊗[A] N => (1 : S) ⊗ₜ[B φ] p)
          = cN.symm ∘ ΛN := by
        funext p
        rw [Function.comp_apply, ← hunit_eq, LinearEquiv.symm_apply_apply]
      rw [hcomp]
      exact (cN.symm.bijective).comp hΛNbij
    exact nakayama_descent (LinearMap.baseChange (B φ) q) hfsurj hPiso hSQ
  -- Step 6: descend.
  -- C is finite (quotient of finite N).
  have : Module.Finite A C := Module.Finite.of_surjective q hq
  obtain ⟨n, cgen, hspan⟩ := Module.Finite.exists_fin (R := A) (M := C)
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  -- predicate: (1 : R i) ⊗ c = 0
  set Q : ι → C → Prop := fun i c => (1 : R i) ⊗ₜ[A] c = 0 with hQ
  have hmono : ∀ ⦃i j : ι⦄, i ≤ j → ∀ c, Q i c → Q j c := by
    intro i j hij c hc
    simp only [hQ] at hc ⊢
    have := one_tmul_eq_of_le φ hij (p := c) (q := (0 : C)) (by rw [hc, TensorProduct.tmul_zero])
    rw [this, TensorProduct.tmul_zero]
  -- each generator dies at a finite stage
  have hsgood : ∀ c ∈ (Finset.image cgen Finset.univ), ∃ i, Q i c := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨k, rfl⟩ := hc
    -- (1 : B φ) ⊗ cgen k = 0
    have hzero : TensorProduct.map (βAlg φ i₀).toLinearMap (LinearMap.id (R := A) (M := C))
        ((1 : R i₀) ⊗ₜ[A] cgen k) = 0 := by
      have : TensorProduct.map (βAlg φ i₀).toLinearMap (LinearMap.id (R := A) (M := C))
          ((1 : R i₀) ⊗ₜ[A] cgen k) = (1 : B φ) ⊗ₜ[A] cgen k := by
        rw [TensorProduct.map_tmul]
        simp only [LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply, map_one]
      rw [this]
      exact Subsingleton.elim _ _
    obtain ⟨j, hij, hj⟩ := tensor_zero_exact φ htrans i₀ ((1 : R i₀) ⊗ₜ[A] cgen k) hzero
    refine ⟨j, ?_⟩
    simp only [hQ]
    rwa [transMod_one_tmul] at hj
  obtain ⟨j, hj⟩ := exists_forall_one_tmul_eq Q hmono (Finset.image cgen Finset.univ) hsgood
  -- (1 : R j) ⊗ c = 0 for all generators
  have hgen : ∀ k : Fin n, (1 : R j) ⊗ₜ[A] cgen k = 0 := by
    intro k
    have := hj (cgen k) (by simp only [Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨k, rfl⟩)
    simpa [hQ] using this
  -- extend to all c : C
  have hall : ∀ c : C, (1 : R j) ⊗ₜ[A] c = 0 := by
    intro c
    have hmem : c ∈ Submodule.span A (Set.range cgen) := by rw [hspan]; exact Submodule.mem_top
    induction hmem using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hgen k
    | zero => rw [TensorProduct.tmul_zero]
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [TensorProduct.tmul_smul, hx, smul_zero]
  -- conclude R j ⊗ C subsingleton
  refine ⟨j, ?_⟩
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  apply not_subsingleton_iff_nontrivial.mpr hnt
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : (R j) ⊗[A] C, z = 0 by rw [h x, h y]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r c =>
      calc r ⊗ₜ[A] c = r • ((1 : R j) ⊗ₜ[A] c) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        _ = r • (0 : (R j) ⊗[A] C) := by rw [hall c]
        _ = 0 := smul_zero r
  | add x y hx hy => rw [hx, hy, add_zero]

/-- **Statement (2).** If `N` is a finite `A`-module and `u : M → N` has
surjective base change to `R`, then its base change to some `R_i` is surjective. -/
@[stacks 05LI "(2)"]
theorem statement_two
    (htrans : TransitionSystem φ) (hcocone : IsCoconeAlg φ ψ)
    (hcolimN : IsModuleColimit φ ψ N)
    (hN : Module.Finite A N)
    (u : M →ₗ[A] N)
    (h : Function.Surjective (LinearMap.baseChange S u)) :
    ∃ i : ι, Function.Surjective (LinearMap.baseChange (R i) u) := by
  -- Reduce to vanishing of the cokernel `C := N ⧸ range u` after base change.
  set C := N ⧸ LinearMap.range u with hC
  set q : N →ₗ[A] C := (LinearMap.range u).mkQ with hq_def
  have hqsurj : Function.Surjective q := Submodule.mkQ_surjective _
  -- `S ⊗ C` is a subsingleton because `baseChange S u` is surjective.
  have hSC : Subsingleton (S ⊗[A] C) :=
    (baseChange_surjective_iff_coker_subsingleton S u).mp h
  -- Core descent: `R_i ⊗ C` vanishes for some `i`.
  obtain ⟨i, hi⟩ :=
    statement_two_coker_descend φ ψ htrans hcocone hcolimN hN q hqsurj hSC
  -- Translate back to surjectivity of `baseChange (R i) u`.
  exact ⟨i, (baseChange_surjective_iff_coker_subsingleton (R i) u).mpr hi⟩

end Statements

end Stacks.FinitePresentation.ColimitDescent
