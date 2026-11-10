module
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import StacksCore.Tactic.StacksAttribute
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Faithful flatness via nonzero fibers (Stacks 00HP)

Let `M` be a flat `R`-module. The following are equivalent:
1. `M` is faithfully flat;
2. for every nonzero `R`-module `N`, the tensor product `M ⊗[R] N` is nonzero;
3. for every prime `𝔭`, the tensor product `M ⊗[R] κ(𝔭)` is nonzero;
4. for every maximal ideal `𝔪`, the tensor product `M ⊗[R] κ(𝔪) = M/𝔪M` is nonzero.

Here `κ(I) = Ideal.ResidueField I` is the residue field, and "nonzero" is
`Nontrivial`.
-/


open Module TensorProduct

universe u v

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- For a maximal ideal `𝔪`, the fiber `M ⊗[R] κ(𝔪)` is `R`-linearly isomorphic to
`M / 𝔪 M`. -/
@[ega "0 6.4.5" "M ⊗_A (A/m) ≅ M/mM"]
noncomputable def fiberEquivQuotSMul (m : Ideal R) [m.IsMaximal] :
    (M ⊗[R] m.ResidueField) ≃ₗ[R] M ⧸ (m • (⊤ : Submodule R M)) :=
  (LinearEquiv.lTensor M
      (LinearEquiv.ofBijective
        (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField).toLinearMap
        (Ideal.bijective_algebraMap_quotient_residueField m))).symm ≪≫ₗ
    TensorProduct.tensorQuotEquivQuotSMul M m

/-- If `M ⊗[R] κ(𝔪)` is nonzero for a maximal ideal `𝔪`, then `𝔪 • ⊤ ≠ ⊤` in `M`. -/
theorem smul_top_ne_top_of_nontrivial_fiber (m : Ideal R) [m.IsMaximal]
    (h : Nontrivial (M ⊗[R] m.ResidueField)) : m • (⊤ : Submodule R M) ≠ ⊤ := by
  have := h
  have : Nontrivial (M ⧸ (m • (⊤ : Submodule R M))) :=
    (fiberEquivQuotSMul R M m).symm.toEquiv.nontrivial
  intro htop
  exact not_subsingleton _ (Submodule.Quotient.subsingleton_iff.mpr htop)

/-- For a flat `R`-module `M`, faithful flatness is equivalent to each of: `M ⊗[R] N` is
nonzero for every nonzero `R`-module `N`; `M ⊗[R] κ(𝔭)` is nonzero for every prime `𝔭`;
`M ⊗[R] κ(𝔪)` is nonzero for every maximal ideal `𝔪`. -/
@[stacks 00HP,
  ega "0 6.4.1" "(a) ⇔ (b), (a) ⇔ (d)",
  ega "IV 2.2.1" "affine case, a)<=>b)",
  sga "1 IV 2.1" "(i bis) <=> (i ter)", ega "IV 2.2.7" "special case", ega "IV 2.5.8.8" "partial"]
theorem faithfullyFlat_tfae [Module.Flat R M] :
    [ FaithfullyFlat R M,
      ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (M ⊗[R] N),
      ∀ (p : Ideal R) [p.IsPrime], Nontrivial (M ⊗[R] p.ResidueField),
      ∀ (m : Ideal R) [m.IsMaximal], Nontrivial (M ⊗[R] m.ResidueField) ].TFAE := by
  tfae_have 1 → 2 := fun h N _ _ hN =>
    (FaithfullyFlat.iff_flat_and_lTensor_faithful R M).mp h |>.right N hN
  tfae_have 2 → 3 := by
    intro h p _
    have := h (ULift.{v} p.ResidueField) inferInstance
    exact (LinearEquiv.lTensor M
      (ULift.moduleEquiv (R := R) (M := p.ResidueField)).symm).toEquiv.nontrivial
  tfae_have 3 → 4 := fun h m _ => h m
  tfae_have 4 → 1 := by
    intro h
    refine (FaithfullyFlat.iff_flat_and_proper_ideal R M).mpr ⟨inferInstance, fun I hI => ?_⟩
    obtain ⟨m, hm, hle⟩ := I.exists_le_maximal hI
    have hmne := smul_top_ne_top_of_nontrivial_fiber R M m (h m)
    intro hItop
    have hsub : I • (⊤ : Submodule R M) ≤ m • ⊤ := Submodule.smul_mono hle le_rfl
    rw [hItop] at hsub
    exact hmne (eq_top_iff.mpr hsub)
  tfae_finish

-- ===== merged from Sec39/Tag00HQ =====


/-!
# Faithfully flat ring maps via surjective Spec (Stacks 00HQ)

Let `f : R → S` be a flat ring map. The following are equivalent:
1. `f` is faithfully flat,
2. the induced map `Spec(S) → Spec(R)` is surjective,
3. every closed point `x ∈ Spec(R)` is in the image of `Spec(S) → Spec(R)`.

Closed points of `Spec(R)` correspond to maximal ideals of `R`, by
`PrimeSpectrum.isClosed_singleton_iff_isMaximal`.

The implication `(3) ⇒ (2)` uses going-down for flat ring maps: any prime `p`
is contained in some maximal ideal `m`; lifting `m` to `Spec(S)` and applying
going-down produces a prime of `S` lying over `p`.
-/


open PrimeSpectrum

/-- Going-down for flat ring maps, at the level of `PrimeSpectrum`:
if `p ≤ q` in `Spec(R)` and `q` lies in the image of `PrimeSpectrum.comap f`,
then so does `p`. -/
private lemma flat_comap_range_isClosedUnderGeneralization
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : RingHom.Flat f)
    {p q : PrimeSpectrum R} (hpq : p.asIdeal ≤ q.asIdeal)
    (hq : q ∈ Set.range (PrimeSpectrum.comap f)) :
    p ∈ Set.range (PrimeSpectrum.comap f) := by
  obtain ⟨Q, hQ⟩ := hq
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  have : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  have hgen : GeneralizingMap (PrimeSpectrum.comap (algebraMap R S)) :=
    Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp ‹_›
  obtain ⟨Q', _, hQ'eq⟩ := hgen
    (hQ ▸ (PrimeSpectrum.le_iff_specializes p q).mp hpq :
      p ⤳ PrimeSpectrum.comap (algebraMap R S) Q)
  exact ⟨Q', hQ'eq⟩

/-- For a flat ring map `f : R →+* S`, faithful flatness is equivalent to surjectivity of
`Spec(S) → Spec(R)`, and to every closed point of `Spec(R)` lying in the image of that
map. -/
@[stacks 00HQ,
  sga "1 IV 2.6" "(i) ⇔ (ii) ⇔ (ii bis)",
  ega "IV 2.2.2" "a)<=>b'), affine F=O_X",
  ega "IV 2.2.3" "M = B with A → B flat",
  ega "IV 2.2.5" "special case",
  ega "IV 2.2.6" "special case",
  sga "1 IV 2.3" "M = B",
  sga "3 V 4.1.1" "Faithful flatness clause",
  sga "4½ Arcata 1.4.1" "special case"]
theorem faithfullyFlat_tfae00HQ
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : RingHom.Flat f) :
    List.TFAE
      [ RingHom.FaithfullyFlat f,
        Function.Surjective (PrimeSpectrum.comap f),
        ∀ x : PrimeSpectrum R, IsClosed ({x} : Set (PrimeSpectrum R)) →
          x ∈ Set.range (PrimeSpectrum.comap f) ] := by
  tfae_have h12 : 1 → 2 := fun hff =>
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff).right
  tfae_have h23 : 2 → 3 := fun hsurj x _ => hsurj x
  tfae_have h31 : 3 → 1 := fun h =>
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
      ⟨hf, fun p => by
        obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
        exact flat_comap_range_isClosedUnderGeneralization f hf hpm
          (h ⟨m, hm.isPrime⟩ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm))⟩
  tfae_finish

-- ===== merged from Sec39/Tag00HO =====

/-!
### Faithful flatness detects zero maps, and the local case

Mathlib states the two remaining tags of this file.

Stacks 00HO — an `R`-module is faithfully flat exactly when it is flat and detects zero maps,
`α = 0` iff `α ⊗ id_M = 0` — is `Module.FaithfullyFlat.iff_zero_iff_rTensor_zero`, with the two
modules implicit and the inner biconditional stated in the other direction; the `lTensor`
variant is `Module.FaithfullyFlat.iff_zero_iff_lTensor_zero`.

Stacks 00HR — a flat local ring homomorphism of local rings is faithfully flat — is
`Module.FaithfullyFlat.of_flat_of_isLocalHom`, stated for the module rather than for the ring
map, which is the same thing by `RingHom.FaithfullyFlat`.
-/

add_to_stacks 00HO "with the two modules implicit and the inner biconditional the other way
  round" Module.FaithfullyFlat.iff_zero_iff_rTensor_zero
add_to_sga "1 IV 2.1" Module.FaithfullyFlat.iff_zero_iff_rTensor_zero
add_to_ega "0 6.6.1" "more general" Module.FaithfullyFlat.iff_zero_iff_rTensor_zero
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.iff_zero_iff_rTensor_zero
add_to_ega "0 6.4.1" "(a) ⇔ (c)" Module.FaithfullyFlat.iff_zero_iff_rTensor_zero
add_to_stacks 00HO "the `lTensor` variant" Module.FaithfullyFlat.iff_zero_iff_lTensor_zero
add_to_sga "1 IV 2.1" Module.FaithfullyFlat.iff_zero_iff_lTensor_zero
add_to_ega "0 6.4.1" Module.FaithfullyFlat.iff_zero_iff_lTensor_zero
add_to_ega "0 6.6.1" "more general" Module.FaithfullyFlat.iff_zero_iff_lTensor_zero
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.iff_zero_iff_lTensor_zero
add_to_stacks 00HR Module.FaithfullyFlat.of_flat_of_isLocalHom
add_to_sga "1 IV 2.6" "(i), special case" Module.FaithfullyFlat.of_flat_of_isLocalHom
add_to_ega "0 6.6.1" "(e) ⇒ (a), special case" Module.FaithfullyFlat.of_flat_of_isLocalHom
add_to_ega "0 6.6.2" "partial, special case" Module.FaithfullyFlat.of_flat_of_isLocalHom
add_to_ega "IV 2.5.5.4" "special case" Module.FaithfullyFlat.of_flat_of_isLocalHom
add_to_sga "1 IV 2.2" "case M = B"
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A flat local homomorphism of local rings is faithfully flat: Stacks 00HR read at the
algebra structure the ring homomorphism itself induces, rather than at a module.  The
`Module`-level statement is Mathlib's `Module.FaithfullyFlat.of_flat_of_isLocalHom`. -/
@[ega "0 6.6.1" "(e) ⇒ (a), special case",
  ega "0 6.6.2" "partial, special case",
  sga "1 IV 2.2" "special case",
  sga "1 IV 2.6" "(i), special case"]
theorem faithfullyFlat_of_flat_of_isLocalHom {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] (hφ : φ.Flat) :
    φ.FaithfullyFlat := by
  let := φ.toAlgebra
  have : Module.Flat A B := hφ
  have : IsLocalHom (algebraMap A B) := by rwa [RingHom.algebraMap_toAlgebra]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom
