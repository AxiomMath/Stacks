module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generalizations lift along the support of a finite flat module

Let `φ : R → S` be a homomorphism of commutative rings and let `N` be an `S`-module that is
finite as an `S`-module and flat as an `R`-module.  Give the support `Supp(N) ⊆ Spec(S)` the
subspace topology and consider the restriction

    π : Supp(N) → Spec(R),    𝔮 ↦ φ⁻¹(𝔮)

of the map `Spec(φ) : Spec(S) → Spec(R)`.  Then generalizations lift along `π`.

## Conventions

`Spec(R)` is the set of prime ideals of `R` with the Zariski topology, and a ring map
`φ : R → S` induces the continuous map `PrimeSpectrum.comap φ : Spec(S) → Spec(R)`,
`𝔮 ↦ φ⁻¹(𝔮)`.  For a prime `𝔮 ∈ Spec(S)` write `N_𝔮` for the localization of `N` at `𝔮`; the
support is `Supp(N) = {𝔮 : N_𝔮 ≠ 0}`, which is `Module.support S N`, defined as
`{p | Nontrivial (LocalizedModule p.asIdeal.primeCompl N)}`, and is modelled here as the
subtype `{q : PrimeSpectrum S // q ∈ Module.support S N}` with its subspace topology.

A point `x'` *specializes* to `x`, written `x' ⤳ x`, if `x ∈ closure {x'}`, and then `x'` is a
*generalization* of `x`; on `Spec` of a ring, `𝔭' ⤳ 𝔭` if and only if `𝔭' ⊆ 𝔭`
(`PrimeSpectrum.le_iff_specializes`).  A continuous map `f : X → Y` is *generalizing*,
`GeneralizingMap f`, if for every `y' ⤳ y` in `Y` and every `x ∈ X` with `f x = y` there is an
`x' ⤳ x` with `f x' = y'`.

The map `φ : R → S` is carried by an `R`-algebra structure on `S`, so `φ = algebraMap R S`, and
the `R`-module structure on `N` is restriction of scalars along `φ`, recorded by
`IsScalarTower R S N`.

## Outline

The theorem `goingDown_support` is reduced to two commutative-algebra kernels together with a
localization-transport assembly.

* `faithfullyFlat_of_localHom` is the Nakayama core: a nonzero finitely generated module over a
  local ring `B`, flat over a local base `A` with `A → B` a local ring homomorphism, is
  *faithfully* flat over `A`.
* `exists_prime_mem_support_comap_eq` is support surjectivity: for a `B`-module `M` finite over
  `B` and faithfully flat over `A`, the map `Supp_B(M) → Spec(A)` is surjective.
* `goingDown_support` assembles these by localizing `N` at `q'`, with base `A = R_{p'}`, ring
  `B = S_{q'}` and module `M = N_{q'}`, and transporting the resulting prime of `S_{q'}` back to
  a prime `q ⊆ q'` of `S`.

The two kernels are stated over arbitrary `A`, `B`, `M`, the localization bookkeeping living in
the assembly.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The support of the `S`-module `N`, viewed as a topological space via the subspace
topology induced from `Spec(S)`. -/
@[ega "0 1.7.1", sga "1 IV 2.4", sga "2 III 1.1"]
abbrev SuppOfModule (S N : Type*) [CommRing S] [AddCommGroup N] [Module S N] : Type _ :=
  {q : PrimeSpectrum S // q ∈ Module.support S N}

/-- The map `π : Supp(N) → Spec(R)`, `𝔮 ↦ φ⁻¹(𝔮)`, i.e. the restriction of
`Spec(φ) = PrimeSpectrum.comap (algebraMap R S)` to the support of `N`. -/
def suppMap : SuppOfModule S N → PrimeSpectrum R :=
  fun q => PrimeSpectrum.comap (algebraMap R S) q.val

/-- **Nakayama: local flatness implies faithful flatness.**
Let `A → B` be a *local* homomorphism of local rings and let `M` be a `B`-module that is
finite over `B`, nonzero, and flat over `A` (via restriction of scalars `A → B`). Then `M`
is faithfully flat over `A`.

Faithful flatness over the local ring `A` is
equivalent to: `M` is flat and `M ⊗_A κ(𝔪_A) ≠ 0` (equivalently `𝔪_A · M ≠ M`).  We are
given flatness, so it remains to show `𝔪_A · M ≠ M`.  Because `A → B` is a local ring map,
the image of `𝔪_A` lies in `𝔪_B`, hence `𝔪_A · M ⊆ 𝔪_B · M`.  Since `M` is a nonzero
finite module over the local ring `B`, Nakayama's lemma (`Submodule.eq_bot_of_le_smul_…` /
`Module.FaithfullyFlat`/`Ideal.smul_top` form) gives `𝔪_B · M ≠ M`, i.e. `𝔪_B · M ⊊ M`.
Therefore `𝔪_A · M ⊆ 𝔪_B · M ⊊ M`, so `M ⊗_A κ(𝔪_A) = M / 𝔪_A M ≠ 0`.  Combined with
flatness this is exactly `Module.FaithfullyFlat A M`
(`Module.FaithfullyFlat.iff_flat_and_proper_smul`-style characterization over a local
ring; cf. `Module.FaithfullyFlat.of_flat_of_…`). -/
@[ega "0 6.6.1" "(e) ⇒ (a), special case",
  ega "0 6.6.2" "partial, special case",
  ega "IV 2.5.5.4" "sufficiency", sga "1 IV 2.2" "sufficiency", sga "1 IV 2.6" "(i), special case"]
theorem faithfullyFlat_of_localHom
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] [Nontrivial M] [Module.Flat A M] :
    Module.FaithfullyFlat A M := by
  -- Faithful flatness over a (local) ring = flat + `m • ⊤ ≠ ⊤` for every maximal ideal `m`.
  rw [Module.faithfullyFlat_iff]
  refine ⟨inferInstance, fun m hm => ?_⟩
  -- The only maximal ideal of the local ring `A` is `maximalIdeal A`.
  obtain rfl : m = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
  -- `M` nonzero ⇒ its `B`-annihilator is a proper ideal.
  have hannih : Module.annihilator B M ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, Module.mem_annihilator]
    push Not
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact ⟨x, by simpa using hx⟩
  -- Nakayama over the local ring `B`: `𝔪_B • ⊤ ≠ ⊤` (the jacobson of the annihilator is `𝔪_B`).
  have hB : (⊤ : Submodule B M) ≠ (IsLocalRing.maximalIdeal B) • ⊤ := by
    apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ hannih]
  -- The image of `𝔪_A` under the local hom lies in `𝔪_B`.
  have himg := IsLocalRing.map_maximalIdeal_le (algebraMap A B)
  -- Hence (as `A`-submodules) `𝔪_A • ⊤ ⊆ 𝔪_B • ⊤` via the scalar tower.
  have hle : (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) ≤
      ((IsLocalRing.maximalIdeal B) • ⊤ : Submodule B M).restrictScalars A := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.restrictScalars_mem, algebra_compatible_smul B r n]
    exact Submodule.smul_mem_smul (himg (Ideal.mem_map_of_mem _ hr)) trivial
  -- If `𝔪_A • ⊤ = ⊤` then `𝔪_B • ⊤ = ⊤`, contradicting Nakayama.
  exact fun htop => hB ((Submodule.restrictScalars_eq_top_iff A B M).mp
    (top_le_iff.mp (htop.ge.trans hle))).symm

/-- The pullback of a prime `P` of `C` to `S` lies in `Supp_S(N)` once `P` contains the image of
`Ann_S(N)`. -/
private theorem comap_mem_support_of_annihilator {S C N : Type*} [CommRing S] [CommRing C]
    [Algebra S C] [AddCommGroup N] [Module S N] [Module.Finite S N] (P : PrimeSpectrum C)
    (h : ∀ a ∈ Module.annihilator S N, algebraMap S C a ∈ P.asIdeal) :
    PrimeSpectrum.comap (algebraMap S C) P ∈ Module.support S N := by
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  exact h

/-- **Faithful flatness implies surjectivity on supports.**
Let `A` be a commutative ring, `B` an `A`-algebra, and `M` a `B`-module that is finite over
`B` and faithfully flat over `A`. Then for every prime `r` of `A` there is a prime `Q` of
`B` with `Q ∈ Supp_B(M)` and `comap(A → B) Q = r`; i.e. the map
`Supp_B(M) → Spec(A)` is surjective.

Fix a prime `r` of `A` with residue field
`κ(r) = A_r / r A_r`.  Faithful flatness of `M` over `A` gives `M ⊗_A κ(r) ≠ 0`
(`Module.FaithfullyFlat.lTensor_nontrivial`, applied to the nonzero `A`-module `κ(r)`).
Now `M ⊗_A κ(r)` is a module over the fibre ring `B_r := B ⊗_A κ(r)`, and it is finite over
`B_r` (base change of the finite `B`-module `M`).  A nonzero finite module over a ring has
nonempty support (`Module.nonempty_support_iff` : `Supp ≠ ∅ ↔ Nontrivial`), so pick a prime
`P ∈ Supp_{B_r}(M ⊗_A κ(r))`.  Pull `P` back along the ring map `B → B_r = B ⊗_A κ(r)` to a
prime `Q` of `B`.  By construction `Q` lies over `r` (the fibre ring `B_r` is supported on
the fibre over `r`, so `comap(A → B) Q = r`), and `Q ∈ Supp_B(M)` because localizing/
base-changing `M` does not leave the support (compatibility of `Module.support` with base
change to the fibre: a point of `Supp_{B_r}(M ⊗ κ(r))` maps into `Supp_B(M)`). -/
@[ega "0 6.5.1" "special case",
  ega "IV 2.2.5" "special case",
  ega "IV 2.2.6" "partial",
  sga "1 IV 2.3" "M finite over B"]
theorem exists_prime_mem_support_comap_eq
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] [Module.FaithfullyFlat A M]
    (r : PrimeSpectrum A) :
    ∃ Q : PrimeSpectrum B, Q ∈ Module.support B M ∧
      PrimeSpectrum.comap (algebraMap A B) Q = r := by
  classical
  -- `κ(r)`, the residue field of the prime `r`.
  set κ := r.asIdeal.ResidueField with hκ
  -- Faithful flatness of `M` over `A` makes `M ⊗_A κ(r)` nonzero.
  have : Nontrivial (TensorProduct A M κ) := Module.FaithfullyFlat.lTensor_nontrivial A M κ
  -- `C := B / Ann_B(M)`; its spectrum is exactly `Supp_B(M)` and `M` is a faithful finite
  -- `C`-module.
  set I := Module.annihilator B M with hI
  set C := B ⧸ I with hC
  have ht : IsScalarTower A B C := by
    apply IsScalarTower.of_algebraMap_eq; intro x; rfl
  -- Key step: the fibre ring `κ(r) ⊗_A C` is nonzero.  Otherwise the right-exact base change
  -- `κ(r) ⊗_A (Cⁿ ↠ M)` would force `M ⊗_A κ(r) = 0`, contradicting faithful flatness.
  have hCnt : Nontrivial (TensorProduct A κ C) := by
    have tor : Module.IsTorsionBySet B M (I : Set B) := Module.isTorsionBySet_annihilator B M
    let : Module C M := tor.module
    have hBCM : IsScalarTower B C M := by
      refine ⟨fun b c m => ?_⟩
      induction c using Quotient.inductionOn' with
      | _ c =>
        show (Ideal.Quotient.mk I (b * c)) • m = b • (Ideal.Quotient.mk I c) • m
        rw [tor.mk_smul, tor.mk_smul, mul_smul]
    have hACM : IsScalarTower A C M := by
      refine ⟨fun a c m => ?_⟩
      have h1 : (a • c) • m = (algebraMap A C a * c) • m := by rw [Algebra.smul_def]
      rw [h1, mul_smul, algebra_compatible_smul C a (c • m)]
    have hfin : Module.Finite C M :=
      Module.Finite.of_surjective
        (σ := Ideal.Quotient.mk I) (M := M) (P := M)
        ⟨⟨id, fun _ _ => rfl⟩, fun b x => (tor.mk_smul b x).symm⟩ Function.surjective_id
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' C M
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply absurd (inferInstance : Nontrivial (TensorProduct A M κ))
    rw [not_nontrivial_iff_subsingleton]
    have : Subsingleton (TensorProduct A κ (Fin n → C)) :=
      (TensorProduct.piRight A A κ (fun _ : Fin n => C)).toEquiv.subsingleton
    have hkM : Subsingleton (TensorProduct A κ M) := by
      have hsurj : Function.Surjective (LinearMap.lTensor κ (f.restrictScalars A)) :=
        LinearMap.lTensor_surjective κ hf
      exact hsurj.subsingleton
    exact (TensorProduct.comm A κ M).surjective.subsingleton
  -- Therefore `r` lies in the image of `Spec C → Spec A`.
  have hmem : r ∈ Set.range (PrimeSpectrum.comap (algebraMap A C)) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap r).mp hCnt
  obtain ⟨P, hP⟩ := hmem
  -- Pull the prime `P` of `C` back to a prime `Q := comap (B → C) P` of `B`.
  refine ⟨PrimeSpectrum.comap (algebraMap B C) P, ?_, ?_⟩
  · -- `Q ∈ Supp_B(M)`: `Q ⊇ Ann_B(M)` since it contains `ker(B → C) = Ann_B(M)`.
    refine comap_mem_support_of_annihilator _ fun x hx => ?_
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem _
  · -- `comap (A → B) Q = r`: chase `A → B → C` against `A → C` and use `hP`.
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq A B C]
    exact hP

/-- Auxiliary: if `B` is a flat `S`-algebra and `N` is a flat `R`-module (with the scalar
tower `R → S` and `R → S → B`), then `B ⊗[S] N` is a flat `R`-module.  This is the
"localization preserves flatness over the base" fact (Stacks 080T uses it for `N_{q'}` over
`R`), proved by the standard tensor-associativity argument. -/
@[ega "0 6.2.1" "special case",
  ega "IV 2.1.5" "special case",
  ega "IV 2.1.7" "special case",
  ega "IV 2.2.10" "special case"]
theorem flat_R_baseChange
    {R : Type*} {S : Type*} {N : Type*} {B : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [CommRing B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    [Module.Flat S B] [Module.Flat R N] :
    Module.Flat R (TensorProduct S B N) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ g hg
  have hNg : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor S N g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g hg
  have hBNg : Function.Injective
      (LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor S N g)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hNg
  have hsq : ∀ x : TensorProduct R (TensorProduct S B N) P,
      (TensorProduct.AlgebraTensorModule.assoc R S B B N Q)
          (LinearMap.lTensor (TensorProduct S B N) g x) =
      LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor S N g)
          ((TensorProduct.AlgebraTensorModule.assoc R S B B N P) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | tmul bn p =>
      induction bn using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
        rw [TensorProduct.add_tmul, map_add, map_add, map_add, map_add, ha, hb]
      | tmul b n =>
        rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.assoc_tmul,
            TensorProduct.AlgebraTensorModule.assoc_tmul, LinearMap.lTensor_tmul,
            TensorProduct.AlgebraTensorModule.lTensor_tmul]
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.assoc R S B B N P).injective
  apply hBNg
  rw [← hsq, ← hsq, hxy]

/-- **Stacks Tag 080T (explicit prime-ideal "going down" formulation).** For all primes
`𝔭 ⊆ 𝔭'` of `R` and every prime `𝔮' ⊆ S` with `𝔮' ∈ Supp(N)` and `φ⁻¹(𝔮') = 𝔭'`,
there exists a prime `𝔮 ⊆ S` with `𝔮 ⊆ 𝔮'`, `𝔮 ∈ Supp(N)`, and `φ⁻¹(𝔮) = 𝔭`. -/
@[sga "1 IV 2.4" "more general"]
theorem goingDown_support [Module.Finite S N] [Module.Flat R N]
    (p p' : PrimeSpectrum R) (q' : PrimeSpectrum S)
    (hpp' : p ≤ p') (hq' : q' ∈ Module.support S N)
    (hcomap : PrimeSpectrum.comap (algebraMap R S) q' = p') :
    ∃ q : PrimeSpectrum S, q ≤ q' ∧ q ∈ Module.support S N ∧
      PrimeSpectrum.comap (algebraMap R S) q = p := by
  -- ASSEMBLY (Stacks 080T): localize at `q'` and apply the two kernels above.
  --   A := R_{p'},   B := S_{q'},   M := N_{q'}.
  set A := Localization.AtPrime p'.asIdeal
  set B := Localization.AtPrime q'.asIdeal
  set M := LocalizedModule q'.asIdeal.primeCompl N
  -- The algebra map `R → S → S_{q'}` inverts everything outside `q'`, hence (as
  -- `hcomap : comap φ q' = p'`, i.e. `φ⁻¹ q' = p'`) it inverts everything outside `p'`,
  -- so `R → S_{q'}` factors uniquely through `R_{p'}`, giving a local `A`-algebra `B`.
  -- (`IsLocalization.localRingHom` / `IsLocalization.lift` along the inclusion of
  -- `Ideal.primeCompl p'` into the preimage of `Ideal.primeCompl q'`.)
  -- `hcomap` rephrased at the ideal level: `p'.asIdeal = (algebraMap R S)⁻¹ q'.asIdeal`.
  have hcomap' : p'.asIdeal = q'.asIdeal.comap (algebraMap R S) :=
    (congrArg PrimeSpectrum.asIdeal hcomap).symm
  -- The ring hom `R_{p'} → S_{q'}` induced by `algebraMap R S`.
  let φAB : A →+* B := Localization.localRingHom p'.asIdeal q'.asIdeal (algebraMap R S) hcomap'
  let algAB : Algebra A B := φAB.toAlgebra
  -- The factorisation is compatible with the maps from `R` (a tower `R → A → B`).
  have : IsScalarTower R A B := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show (algebraMap R B) x = φAB ((algebraMap R A) x)
    rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R S B]
  -- The induced map `A = R_{p'} → S_{q'} = B` is local.
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom φAB)
  -- `M = N_{q'}` is a `B`-module; make it an `A`-module by restriction along `A → B`.
  let modAM : Module A M := Module.compHom M φAB
  have : IsScalarTower A B M := by
    refine ⟨fun a b m => ?_⟩
    show (φAB a * b) • m = a • (b • m)
    rw [mul_smul]
    rfl
  -- `M` is finite over `B`: localization of the finite `S`-module `N`
  -- (`Module.Finite.of_isLocalizedModule` for `LocalizedModule.mkLinearMap`).
  have : Module.Finite B M :=
    Module.Finite.of_isLocalizedModule (S := q'.asIdeal.primeCompl) (Rₚ := B)
      (LocalizedModule.mkLinearMap q'.asIdeal.primeCompl N)
  -- `M ≠ 0` because `q' ∈ Supp_S(N)` (`Module.mem_support_iff`).
  have : Nontrivial M := Module.mem_support_iff.mp hq'
  -- `M` is flat over `A = R_{p'}`.  First, `M = N_{q'} ≅ B ⊗[S] N` is flat over `R`
  -- (localization preserves flatness over the base, `flat_R_baseChange`); then flatness over
  -- the localization `A = R_{p'}` follows from `Module.flat_iff_of_isLocalization`.
  have : Module.Flat A M := by
    have : IsScalarTower R A M := by
      apply IsScalarTower.of_algebraMap_smul
      intro r x
      show φAB (algebraMap R A r) • x = r • x
      rw [Localization.localRingHom_to_map, ← IsScalarTower.algebraMap_apply R S B,
          IsScalarTower.algebraMap_smul]
    have hflatR : Module.Flat R M := by
      have e : M ≃ₗ[R] TensorProduct S B N :=
        (LocalizedModule.equivTensorProduct q'.asIdeal.primeCompl N).restrictScalars R
      have : Module.Flat R (TensorProduct S B N) :=
        flat_R_baseChange (R := R) (S := S) (N := N) (B := B)
      exact Module.Flat.of_linearEquiv e
    exact (Module.flat_iff_of_isLocalization A p'.asIdeal.primeCompl M).mpr hflatR
  -- `M` is faithfully flat over `A`.
  have : Module.FaithfullyFlat A M := faithfullyFlat_of_localHom (A := A) (B := B) (M := M)
  -- `p ≤ p'` corresponds to the prime `r := p R_{p'}` of `A = R_{p'}` lying over `p`.
  -- (Image of `p` under `Spec(R_{p'}) ≃ {primes ≤ p'}`, `IsLocalization.AtPrime.orderIsoOfPrime`.)
  obtain ⟨r, hr⟩ : ∃ r : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap R A) r = p := by
    show p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A))
    rw [PrimeSpectrum.localization_comap_range _ p'.asIdeal.primeCompl]
    show Disjoint (p'.asIdeal.primeCompl : Set R) p.asIdeal
    rw [Set.disjoint_left]
    intro x hx hxp
    exact hx (hpp' hxp)
  -- A prime `Q` of `B = S_{q'}` in `Supp_B(M)` lying over `r`.
  obtain ⟨Q, hQsupp, hQr⟩ := exists_prime_mem_support_comap_eq (A := A) (B := B) (M := M) r
  -- Transport `Q` back to a prime `q` of `S`.  Primes of `B = S_{q'}` correspond
  -- (`PrimeSpectrum.localization_comap_injective`/`localization_comap_range`,
  -- `IsLocalization.AtPrime.orderIsoOfPrime`) to primes `q ⊆ q'` of `S`; set
  -- `q := comap (algebraMap S B) Q`.
  refine ⟨PrimeSpectrum.comap (algebraMap S B) Q, ?_, ?_, ?_⟩
  · -- `q ≤ q'`: the image of `Spec(S_{q'}) → Spec(S)` is exactly the primes `≤ q'`
    -- (`PrimeSpectrum.localization_comap_range`, primes disjoint from `S \ q'`).
    have hmem : PrimeSpectrum.comap (algebraMap S B) Q ∈
        Set.range (PrimeSpectrum.comap (algebraMap S B)) := ⟨Q, rfl⟩
    rw [PrimeSpectrum.localization_comap_range _ q'.asIdeal.primeCompl] at hmem
    intro x hx
    by_contra hxq
    exact Set.disjoint_left.mp hmem hxq hx
  · -- `q ∈ Supp_S(N)`: localization compatibility of support — `Q ∈ Supp_B(M) =
    -- Supp_{S_{q'}}(N_{q'})` pulls back to `Supp_S(N)` under `S → S_{q'}`.
    refine comap_mem_support_of_annihilator _ fun a ha => ?_
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus] at hQsupp
    apply hQsupp
    rw [SetLike.mem_coe, Module.mem_annihilator]
    intro m
    induction m using LocalizedModule.induction_on with
    | h n s =>
      have han : a • n = 0 := (Module.mem_annihilator.mp ha) n
      rw [← algebra_compatible_smul B a (LocalizedModule.mk n s),
          LocalizedModule.smul'_mk, han]
      simp
  · -- `comap φ q = p`: chase the commuting square `R → A → B` and `R → S → B`.  We have
    -- `comap (S→B) Q = q`, `comap (A→B) Q = r` (`hQr`), `comap (R→A) r = p` (`hr`), and the
    -- tower `IsScalarTower R A B` / `IsScalarTower R S B` makes the two composites
    -- `R → B` agree, giving `comap φ q = comap (R→A) r = p`.
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R S B,
        IsScalarTower.algebraMap_eq R A B, PrimeSpectrum.comap_comp_apply, hQr, hr]

/-- **Stacks Tag 080T (topological formulation).** If `N` is a finite `S`-module that is
flat over `R`, then generalizations lift along `π : Supp(N) → Spec(R)`. -/
@[stacks 080T, sga "1 IV 2.4" "more general"]
theorem generalizingMap_suppMap [Module.Finite S N] [Module.Flat R N] :
    GeneralizingMap (suppMap (R := R) (S := S) (N := N)) := by
  intro a b hb
  -- `hb : b ⤳ suppMap a`, i.e. `b ≤ suppMap a` in `Spec R`.
  rw [← PrimeSpectrum.le_iff_specializes] at hb
  obtain ⟨q, hqle, hqsupp, hqcomap⟩ :=
    goingDown_support (R := R) (S := S) (N := N) b (suppMap a) a.val hb a.property rfl
  refine ⟨⟨q, hqsupp⟩, ?_, hqcomap⟩
  show (⟨q, hqsupp⟩ : SuppOfModule S N) ⤳ a
  rw [subtype_specializes_iff]
  exact (PrimeSpectrum.le_iff_specializes _ _).mp hqle
