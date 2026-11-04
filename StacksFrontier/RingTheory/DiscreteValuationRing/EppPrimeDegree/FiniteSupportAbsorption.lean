module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConstantNumeratorFamily
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationTower

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Prime-degree input: fraction-field towers and finite-support absorption

Fraction-field towers for embedded DVR maps and the finite weakly-unramified residue
absorptions (finite support, mixed level support) used by the prime-degree solvers.
-/

@[expose] public section

open IsLocalRing
open IsDiscreteValuationRing
open scoped TensorProduct

namespace Stacks.EppTheorem

universe u v w uΩ

/-- Extend an embedded DVR map to its fraction field, retaining compatibility with an older
fraction-field tower.  This is the field map needed after finite-support residue absorption: the
new DVR lies inside the old upper DVR, hence its fraction field lies inside the old upper fraction
field as well. -/
theorem exists_fractionField_algebra_tower
    {A A₁ K K₁ L : Type u}
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁]
    [Field K] [Field K₁] [Field L]
    [Algebra A A₁] [Algebra A K] [Algebra A₁ K₁] [Algebra K K₁] [Algebra A K₁]
    [Algebra A L] [Algebra A₁ L] [Algebra K L]
    [FaithfulSMul A₁ L]
    [IsFractionRing A K] [IsFractionRing A₁ K₁]
    [IsScalarTower A A₁ K₁] [IsScalarTower A K K₁]
    [IsScalarTower A A₁ L] [IsScalarTower A K L] :
    ∃ (_ : Algebra K₁ L), IsScalarTower A₁ K₁ L ∧ IsScalarTower K K₁ L := by
  let algK₁L : Algebra K₁ L :=
    (IsFractionRing.lift (A := A₁) (K := K₁) (L := L)
      (FaithfulSMul.algebraMap_injective A₁ L)).toAlgebra
  let : Algebra K₁ L := algK₁L
  let hA₁K₁L : IsScalarTower A₁ K₁ L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (A := A₁) (K := K₁) (L := L)
      (FaithfulSMul.algebraMap_injective A₁ L) a).symm
  let : IsScalarTower A₁ K₁ L := hA₁K₁L
  have hmaps : (algebraMap K L) =
      (algebraMap K₁ L).comp (algebraMap K K₁) := by
    apply IsFractionRing.ringHom_ext (A := A) (K := K)
    intro a
    show algebraMap K L (algebraMap A K a) =
      algebraMap K₁ L (algebraMap K K₁ (algebraMap A K a))
    calc
      algebraMap K L (algebraMap A K a) = algebraMap A L a :=
        (IsScalarTower.algebraMap_apply A K L a).symm
      _ = algebraMap A₁ L (algebraMap A A₁ a) :=
        IsScalarTower.algebraMap_apply A A₁ L a
      _ = algebraMap K₁ L (algebraMap A₁ K₁ (algebraMap A A₁ a)) :=
        IsScalarTower.algebraMap_apply A₁ K₁ L (algebraMap A A₁ a)
      _ = algebraMap K₁ L (algebraMap A K₁ a) := by
        rw [← IsScalarTower.algebraMap_apply A A₁ K₁]
      _ = algebraMap K₁ L (algebraMap K K₁ (algebraMap A K a)) := by
        rw [IsScalarTower.algebraMap_apply A K K₁]
  let hKK₁L : IsScalarTower K K₁ L := IsScalarTower.of_algebraMap_eq fun x =>
    RingHom.congr_fun hmaps x
  exact ⟨algK₁L, hA₁K₁L, hKK₁L⟩

/-- A module-finite faithful extension `A → A₁` of a DVR induces a finite extension of fraction
fields `K → FractionRing A₁` compatible with the scalar towers. -/
private theorem exists_algebra_fractionRing_tower_of_finite
    {A A₁ K : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing A₁] [IsDomain A₁] [Field K] [Algebra A A₁] [Algebra A K] [IsFractionRing A K]
    [Module.Finite A A₁] [FaithfulSMul A A₁] :
    ∃ (_ : Algebra K (FractionRing A₁)), IsScalarTower A K (FractionRing A₁) ∧
      IsScalarTower A A₁ (FractionRing A₁) ∧ Module.Finite K (FractionRing A₁) := by
  have hinj : Function.Injective (algebraMap A A₁) :=
    FaithfulSMul.algebraMap_injective A A₁
  have hnonzero : nonZeroDivisors A ≤
      Submonoid.comap (algebraMap A A₁) (nonZeroDivisors A₁) := by
    intro x hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using hinj.ne (nonZeroDivisors.ne_zero hx)
  let : Algebra K (FractionRing A₁) :=
    (IsFractionRing.map (K := K) (L := FractionRing A₁) hinj).toAlgebra
  let : IsScalarTower A A₁ (FractionRing A₁) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A K (FractionRing A₁) := IsScalarTower.of_algebraMap_eq fun a => by
    calc
      algebraMap A (FractionRing A₁) a = algebraMap A₁ (FractionRing A₁) (algebraMap A A₁ a) :=
        rfl
      _ = IsFractionRing.map (K := K) (L := FractionRing A₁) hinj (algebraMap A K a) :=
        by simpa only [IsFractionRing.map] using
          (IsLocalization.map_eq (Q := FractionRing A₁) hnonzero a).symm
      _ = algebraMap K (FractionRing A₁) (algebraMap A K a) := rfl
  exact ⟨inferInstance, inferInstance, inferInstance,
    finiteDimensional_fractionRing_of_finite A A₁ K (FractionRing A₁) hinj⟩

/-- **Shared residue absorption, together with the fraction-field extension it defines.**

This is
`EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`, with
`K₂ = FractionRing R₂` added to its output.  The induced map `K → K₂` is the map of
fraction fields attached to `R → R₂`; module-finiteness of `K₂ / K` follows from
module-finiteness of `R₂ / R`.

The overfield conclusion is unchanged and remains quantified after `R₂` and `K₂` are fixed.
Thus the same normal residue extension supplies the deep roots in every conjugate factor. -/
theorem
  EppCondition.exists_fractionField_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [IsAdicComplete (maximalIdeal R) R] [PerfectField (ResidueField R)]
    {ι : Type w} [Finite ι] (S : ι → Type v)
    [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalHom (algebraMap R (S i))]
    {p : ℕ} [∀ i, ExpChar (ResidueField (S i)) p]
    (h : ∀ i, EppCondition R (S i) p)
    (s : ∀ i, Finset (ResidueField (S i)))
    (hs : ∀ i, ∀ x ∈ s i, x ∈ perfectCore (ResidueField (S i)) p) (N : ℕ) :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂)
      (_ : IsDiscreteValuationRing R₂) (_ : Algebra R R₂) (_ : Module.Finite R R₂)
      (_ : IsDiscreteValuationRing.IsExtension R R₂)
      (_ : IsAdicComplete (maximalIdeal R₂) R₂) (_ : PerfectField (ResidueField R₂))
      (K₂ : Type u) (_ : Field K₂) (_ : Algebra R₂ K₂) (_ : IsFractionRing R₂ K₂)
      (_ : Algebra K K₂) (_ : Algebra R K₂) (_ : IsScalarTower R K K₂)
      (_ : IsScalarTower R R₂ K₂) (_ : Module.Finite K K₂),
      IsDiscreteValuationRing.IsWeaklyUnramified R R₂ ∧
        IsGalois (ResidueField R) (ResidueField R₂) ∧
        ∀ (i : ι) (Ω : Type uΩ) [Field Ω] [Algebra (ResidueField R) Ω]
          [Algebra (ResidueField (S i)) Ω] [Algebra (ResidueField R₂) Ω]
          [IsScalarTower (ResidueField R) (ResidueField (S i)) Ω]
          [IsScalarTower (ResidueField R) (ResidueField R₂) Ω],
          ∀ x ∈ s i, ∃ z : ResidueField R₂,
            algebraMap (ResidueField R₂) Ω z ^ p ^ N =
              algebraMap (ResidueField (S i)) Ω x := by
  obtain ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext,
      hweak, hgal, hroot⟩ :=
    EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield
      S h s hs N
  let := hR₂comm
  let := hR₂dom
  let := hR₂dvr
  let := hRR₂
  let := hR₂fin
  let := hR₂ext
  let hR₂complete : IsAdicComplete (maximalIdeal R₂) R₂ :=
    IsDiscreteValuationRing.isAdicComplete_of_finite R R₂
  let hR₂perfect : PerfectField (ResidueField R₂) :=
    IsDiscreteValuationRing.perfectField_residueField_of_finite R R₂
  let K₂ := FractionRing R₂
  obtain ⟨hKK₂, hRKK₂, hRR₂K₂, hK₂fin⟩ :=
    exists_algebra_fractionRing_tower_of_finite (A := R) (A₁ := R₂) (K := K)
  let := hKK₂
  let := hRKK₂
  let := hRR₂K₂
  let := hK₂fin
  refine ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext,
    hR₂complete, hR₂perfect,
    K₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hweak, hgal, hroot⟩

/-- **Finite-support residue absorption, retaining the embedded DVR and its fraction field.**

For a finite part of the perfect core of `κ_B`, Epp's condition gives a finite étale
extension `A₁ / A` embedded in `B` whose residue field absorbs that support.  This packages the
fraction field `K₁` of `A₁` at the same time.  In particular the output retains every datum
needed to re-enter a mixed-characteristic level step: `A₁ → B`, completeness and perfectness
of `A₁`, and a finite extension `K₁ / K` compatible with both integral models. -/
theorem EppCondition.exists_fractionField_finiteEtale_absorbs_finset
    {A B K : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B]
    [Field K] [Algebra A B] [Algebra A K]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    {p : ℕ} [ExpChar (ResidueField A) p] [PerfectRing (ResidueField A) p]
    [ExpChar (ResidueField B) p]
    (h : EppCondition A B p) (s : Finset (ResidueField B))
    (hs : ∀ z ∈ s, z ∈ perfectCore (ResidueField B) p) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁)
      (_ : IsDiscreteValuationRing A₁) (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁)
      (_ : Algebra A₁ B) (_ : IsScalarTower A A₁ B)
      (_ : IsLocalHom (algebraMap A₁ B))
      (_ : IsAdicComplete (maximalIdeal A₁) A₁)
      (_ : PerfectField (ResidueField A₁))
      (K₁ : Type u) (_ : Field K₁) (_ : Algebra A₁ K₁) (_ : IsFractionRing A₁ K₁)
      (_ : Algebra K K₁) (_ : Algebra A K₁) (_ : IsScalarTower A K K₁)
      (_ : IsScalarTower A A₁ K₁) (_ : Module.Finite K K₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        (∀ z ∈ s, z ∈ (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange) ∧
        (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange ≤
          perfectCore (ResidueField B) p := by
  obtain ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext,
      hA₁B, hAA₁B, hlocal, hweak, habs, hrange⟩ :=
    h.exists_isWeaklyUnramified_absorbing_finset s hs
  let := hA₁comm
  let := hA₁dom
  let := hA₁dvr
  let := hAA₁
  let := hA₁fin
  let := hA₁ext
  let := hA₁B
  let := hAA₁B
  let := hlocal
  let hA₁complete : IsAdicComplete (maximalIdeal A₁) A₁ :=
    IsDiscreteValuationRing.isAdicComplete_of_finite A A₁
  let hA₁perfect : PerfectField (ResidueField A₁) :=
    IsDiscreteValuationRing.perfectField_residueField_of_finite A A₁
  let K₁ := FractionRing A₁
  obtain ⟨hKK₁, hAKK₁, hAA₁K₁, hK₁fin⟩ :=
    exists_algebra_fractionRing_tower_of_finite (A := A) (A₁ := A₁) (K := K)
  let := hKK₁
  let := hAKK₁
  let := hAA₁K₁
  let := hK₁fin
  refine ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext,
    hA₁B, hAA₁B, hlocal, hA₁complete, hA₁perfect,
    K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hAKK₁, hAA₁K₁, inferInstance, hweak, habs, hrange⟩

/-- **Turn the finite-support alternative of the mixed level step into an actual re-entry base.**

If a construction either has already produced `Q` or exposes finitely many missing elements of
the perfect core, Epp's condition absorbs those elements in a finite weakly-unramified DVR inside
`B`.  The fraction field is retained, and a supplied uniformizer remains irreducible in the new
base.  This is the exact state needed to re-run the uniformizer-pinned version of Tag 09F5. -/
theorem EppCondition.absorb_finiteSupport_or
    {A B K L : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    {p : ℕ} [ExpChar (ResidueField A) p] [PerfectRing (ResidueField A) p]
    [ExpChar (ResidueField B) p]
    (hepp : EppCondition A B p) (πA : A) (hπA : Irreducible πA) (Q : Prop)
    (R : Finset (ResidueField B) → Prop)
    (hstep : Q ∨ ∃ s : Finset (ResidueField B),
      (∀ x ∈ s, x ∈ perfectCore (ResidueField B) p) ∧
        (¬∀ x ∈ s, x ∈ (algebraMap (ResidueField A) (ResidueField B)).fieldRange) ∧
        R s) :
    Q ∨
      ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁)
        (_ : IsDiscreteValuationRing A₁) (_ : Algebra A A₁) (_ : Module.Finite A A₁)
        (_ : IsDiscreteValuationRing.IsExtension A A₁)
        (_ : Algebra A₁ B) (_ : IsScalarTower A A₁ B)
        (_ : IsLocalHom (algebraMap A₁ B))
        (_ : IsDiscreteValuationRing.IsExtension A₁ B)
        (_ : IsAdicComplete (maximalIdeal A₁) A₁)
        (_ : PerfectField (ResidueField A₁))
        (K₁ : Type u) (_ : Field K₁) (_ : Algebra A₁ K₁) (_ : IsFractionRing A₁ K₁)
        (_ : Algebra K K₁) (_ : Algebra A K₁) (_ : IsScalarTower A K K₁)
        (_ : IsScalarTower A A₁ K₁) (_ : Module.Finite K K₁)
        (_ : Algebra A₁ L) (_ : IsScalarTower A₁ B L) (_ : IsScalarTower A A₁ L)
        (_ : Algebra K₁ L) (_ : IsScalarTower A₁ K₁ L) (_ : IsScalarTower K K₁ L),
        IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
          Irreducible (algebraMap A A₁ πA) ∧
          EppCondition A₁ B p ∧
          ∃ s : Finset (ResidueField B),
            (∀ x ∈ s, x ∈ perfectCore (ResidueField B) p) ∧
            (¬∀ x ∈ s,
              x ∈ (algebraMap (ResidueField A) (ResidueField B)).fieldRange) ∧
            (∀ x ∈ s,
              x ∈ (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange) ∧
            (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange ≤
              perfectCore (ResidueField B) p ∧
            R s := by
  rcases hstep with hQ | ⟨s, hs, hmissing, hR⟩
  · exact Or.inl hQ
  · obtain ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hAA₁ext,
        hA₁B, hAA₁B, hlocal, hA₁complete, hA₁perfect,
        K₁, hK₁field, hA₁K₁, hfrac, hKK₁, hAK₁, hAKK₁, hAA₁K₁, hK₁fin,
        hweak, habs, hrange⟩ :=
      EppCondition.exists_fractionField_finiteEtale_absorbs_finset
        (A := A) (B := B) (K := K) (p := p) hepp s hs
    let := hA₁comm
    let := hA₁dom
    let := hA₁dvr
    let := hAA₁
    let := hA₁fin
    let := hAA₁ext
    let := hA₁B
    let := hAA₁B
    let := hlocal
    let : Algebra A₁ L := ((algebraMap B L).comp (algebraMap A₁ B)).toAlgebra
    let : IsScalarTower A₁ B L := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower A A₁ L := IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A B L,
        IsScalarTower.algebraMap_apply A A₁ B,
        IsScalarTower.algebraMap_apply A₁ B L]
    let : FaithfulSMul A L :=
      (faithfulSMul_iff_algebraMap_injective A L).mpr (by
        rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K))
    let : Algebra.IsIntegral A A₁ := inferInstance
    let : FaithfulSMul A₁ L := by
      apply (faithfulSMul_iff_algebraMap_injective A₁ L).mpr
      apply (RingHom.injective_iff_ker_eq_bot _).mpr
      apply Ideal.eq_bot_of_comap_eq_bot (R := A)
      rw [RingHom.ker_eq_comap_bot, Ideal.comap_comap,
        ← IsScalarTower.algebraMap_eq A A₁ L]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A L)
    let : FaithfulSMul A₁ B :=
      (faithfulSMul_iff_algebraMap_injective A₁ B).mpr (by
        intro x y hxy
        apply FaithfulSMul.algebraMap_injective A₁ L
        show algebraMap B L (algebraMap A₁ B x) =
          algebraMap B L (algebraMap A₁ B y)
        rw [hxy])
    let hA₁Bext : IsDiscreteValuationRing.IsExtension A₁ B := ⟨⟩
    let : IsDiscreteValuationRing.IsExtension A₁ B := hA₁Bext
    have hepp₁ : EppCondition A₁ B p :=
      EppCondition.of_finite_square (A := A) (A' := A₁) (B := B) (B' := B) hepp
    let := hK₁field
    let := hA₁K₁
    let := hfrac
    let := hKK₁
    let := hAK₁
    let := hAKK₁
    let := hAA₁K₁
    obtain ⟨hK₁L, hA₁K₁L, hKK₁L⟩ :=
      exists_fractionField_algebra_tower (A := A) (A₁ := A₁) (K := K) (K₁ := K₁) (L := L)
    have hπA₁ : Irreducible (algebraMap A A₁ πA) :=
      irreducible_algebraMap_of_isWeaklyUnramified hweak hπA
    exact Or.inr ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hAA₁ext,
      hA₁B, hAA₁B, hlocal, hA₁Bext, hA₁complete, hA₁perfect,
      K₁, hK₁field, hA₁K₁, hfrac, hKK₁, hAK₁, hAKK₁, hAA₁K₁, hK₁fin,
      inferInstance, inferInstance, inferInstance,
      hK₁L, hA₁K₁L, hKK₁L,
      hweak, hπA₁, hepp₁, s, hs, hmissing, habs, hrange, hR⟩

/-- **Discharge the finite-support alternative of a mixed level step.**

The re-entry function returned by the uniformizer-pinned 09F5 theorem is evaluated on the
finite étale base which absorbs its exact coefficient support.  Thus this theorem returns an
actual successful mixed level step over the enlarged base, rather than rerunning 09F5 and
exposing a potentially different existential support. -/
theorem EppCondition.absorb_mixedLevelSupport_or
    (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K L]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [HenselianLocalRing B]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharZero K]
    [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (hepp : EppCondition A B p) (πA : A) (hπA : Irreducible πA)
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B) (l : ℚ)
    (hstep : Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelStepOutcome A B C K L M p f P
      l ∨
      ∃ s : Finset (ResidueField B),
        (∀ x ∈ s, x ∈ perfectCore (ResidueField B) p) ∧
        (¬∀ x ∈ s,
          x ∈ (algebraMap (ResidueField A) (ResidueField B)).fieldRange) ∧
        Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelPreparation B L M p f P l
          (algebraMap A B πA) s ∧
        Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelStepReentry B C L M p f P l
          (algebraMap A B πA) s) :
    Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelStepOutcome A B C K L M p f P l ∨
      ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁)
        (_ : IsDiscreteValuationRing A₁) (_ : Algebra A A₁) (_ : Module.Finite A A₁)
        (_ : IsDiscreteValuationRing.IsExtension A A₁)
        (_ : Algebra A₁ B) (_ : IsScalarTower A A₁ B)
        (_ : IsLocalHom (algebraMap A₁ B))
        (_ : IsDiscreteValuationRing.IsExtension A₁ B)
        (_ : IsAdicComplete (maximalIdeal A₁) A₁)
        (_ : PerfectField (ResidueField A₁))
        (K₁ : Type u) (_ : Field K₁) (_ : Algebra A₁ K₁) (_ : IsFractionRing A₁ K₁)
        (_ : Algebra K K₁) (_ : Algebra A K₁) (_ : IsScalarTower A K K₁)
        (_ : IsScalarTower A A₁ K₁) (_ : Module.Finite K K₁)
        (_ : Algebra A₁ L) (_ : IsScalarTower A₁ B L) (_ : IsScalarTower A A₁ L)
        (_ : Algebra K₁ L) (_ : IsScalarTower A₁ K₁ L) (_ : IsScalarTower K K₁ L)
        (_ : Algebra A₁ C) (_ : Algebra A₁ M) (_ : Algebra K₁ M)
        (_ : IsScalarTower A₁ B C) (_ : IsScalarTower A₁ C M)
        (_ : IsScalarTower A₁ K₁ M) (_ : IsScalarTower K₁ L M)
        (_ : IsDiscreteValuationRing.IsExtension A₁ C),
        IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
          IsDiscreteValuationRing.IsWeaklyUnramified A₁ B ∧
          Irreducible (algebraMap A A₁ πA) ∧ EppCondition A₁ B p ∧
          Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelStepOutcome A₁ B C K₁ L M p f P l
            := by
  let R := fun s : Finset (ResidueField B) =>
    Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelStepReentry B C L M p f P l (algebraMap
      A B πA) s
  have hstep' : Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelStepOutcome A B C K L M p f
    P l ∨
      ∃ s : Finset (ResidueField B),
        (∀ x ∈ s, x ∈ perfectCore (ResidueField B) p) ∧
        (¬∀ x ∈ s,
          x ∈ (algebraMap (ResidueField A) (ResidueField B)).fieldRange) ∧ R s := by
    rcases hstep with h | ⟨s, hs, hmissing, _hprep, hreentry⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hmissing, hreentry⟩
  rcases hepp.absorb_finiteSupport_or (A := A) (B := B) (K := K) (L := L) (p := p) πA hπA
      (Stacks.DiscreteValuationRing.EppLevelInduction.MixedLevelStepOutcome A B C K L M p f P l) R
        hstep' with
    h | ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hAA₁ext,
      hA₁B, hAA₁B, hlocal, hA₁Bext, hA₁complete, hA₁perfect,
      K₁, hK₁field, hA₁K₁, hfrac, hKK₁, hAK₁, hAKK₁, hAA₁K₁, hK₁fin,
      hA₁L, hA₁BL, hAA₁L, hK₁L, hA₁K₁L, hKK₁L,
      hweakAA₁, hπA₁, hepp₁, s, hs, hmissing, habs, hrange, hreentry⟩
  · exact Or.inl h
  · let := hA₁comm
    let := hA₁dom
    let := hA₁dvr
    let := hAA₁
    let := hA₁fin
    let := hAA₁ext
    let := hA₁B
    let := hAA₁B
    let := hlocal
    let := hA₁Bext
    let := hA₁complete
    let := hA₁perfect
    let := hK₁field
    let := hA₁K₁
    let := hfrac
    let := hKK₁
    let := hAK₁
    let := hAKK₁
    let := hAA₁K₁
    let := hK₁fin
    let := hA₁L
    let := hA₁BL
    let := hAA₁L
    let := hK₁L
    let := hA₁K₁L
    let := hKK₁L
    let : Algebra A₁ C := ((algebraMap B C).comp (algebraMap A₁ B)).toAlgebra
    let : IsScalarTower A₁ B C := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A₁ M := ((algebraMap B M).comp (algebraMap A₁ B)).toAlgebra
    let : Algebra K₁ M := ((algebraMap L M).comp (algebraMap K₁ L)).toAlgebra
    let : IsScalarTower K₁ L M := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower A₁ C M := IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap B M (algebraMap A₁ B x) =
        algebraMap C M (algebraMap B C (algebraMap A₁ B x))
      rw [IsScalarTower.algebraMap_apply B C M]
    let : IsScalarTower A₁ K₁ M := IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap B M (algebraMap A₁ B x) =
        algebraMap L M (algebraMap K₁ L (algebraMap A₁ K₁ x))
      calc
        algebraMap B M (algebraMap A₁ B x) =
            algebraMap L M (algebraMap B L (algebraMap A₁ B x)) := by
              rw [IsScalarTower.algebraMap_apply B L M]
        _ = algebraMap L M (algebraMap A₁ L x) := by
              rw [IsScalarTower.algebraMap_apply A₁ B L]
        _ = algebraMap L M (algebraMap K₁ L (algebraMap A₁ K₁ x)) := by
              rw [IsScalarTower.algebraMap_apply A₁ K₁ L]
    let : FaithfulSMul A₁ C :=
      (faithfulSMul_iff_algebraMap_injective A₁ C).mpr
        ((FaithfulSMul.algebraMap_injective B C).comp
          (FaithfulSMul.algebraMap_injective A₁ B))
    let : IsLocalHom (algebraMap A₁ C) := by
      show IsLocalHom ((algebraMap B C).comp (algebraMap A₁ B))
      infer_instance
    let hA₁Cext : IsDiscreteValuationRing.IsExtension A₁ C := ⟨⟩
    let : IsDiscreteValuationRing.IsExtension A₁ C := hA₁Cext
    let : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap K K₁).injective
    let : CharP (ResidueField A₁) p :=
      CharP.of_ringHom_of_ne_zero
        (algebraMap (ResidueField A) (ResidueField A₁)) p (Fact.out : p.Prime).ne_zero
    have hweakA₁B : IsDiscreteValuationRing.IsWeaklyUnramified A₁ B :=
      (Stacks.DiscreteValuationRing.Ramification.isWeaklyUnramified_of_isWeaklyUnramified A A₁ B
        hweak).2
    have hπmap : algebraMap A₁ B (algebraMap A A₁ πA) = algebraMap A B πA := by
      rw [IsScalarTower.algebraMap_apply A A₁ B]
    have hout := hreentry A₁ K₁ hweakA₁B (algebraMap A A₁ πA) hπA₁ hπmap habs
    exact Or.inr ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hAA₁ext,
      hA₁B, hAA₁B, hlocal, hA₁Bext, hA₁complete, hA₁perfect,
      K₁, hK₁field, hA₁K₁, hfrac, hKK₁, hAK₁, hAKK₁, hAA₁K₁, hK₁fin,
      hA₁L, hA₁BL, hAA₁L, hK₁L, hA₁K₁L, hKK₁L,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, hA₁Cext,
      hweakAA₁, hweakA₁B, hπA₁, hepp₁, hout⟩

end Stacks.EppTheorem

end
