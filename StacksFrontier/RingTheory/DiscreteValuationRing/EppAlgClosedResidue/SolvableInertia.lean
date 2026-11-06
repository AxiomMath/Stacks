module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppMixedReentry
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois
public import StacksFrontier.RingTheory.DiscreteValuationRing.Inertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolution
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.IntegralClosure.Pi
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.CompleteIntegralClosure

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: solvable inertia and the normal case

Solvability of inertia groups, induction over intermediate fields, the normal case, maps of
integral closures in towers, and the finite field factors of a base-change package.

Part of `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue`;
see there for the overview and references.
-/

@[expose] public section

universe uA uB uC uK uL uM

namespace IsDiscreteValuationRing

open scoped TensorProduct

universe uK₁

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraKL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerABB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureB₁

/-- Solvability of a subgroup of a finite Galois group passes to the Galois group of its fixed
field. -/
private theorem isSolvable_galois_fixedField {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (H : Subgroup Gal(L/K)) [Group.IsSolvable H] :
    Group.IsSolvable Gal(L/IntermediateField.fixedField H) :=
  Group.isSolvable_of_surjective (f := (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom)
    (IntermediateField.subgroupEquivAlgEquiv H).surjective

/-- The inertia group of a maximal ideal is solvable.

It is what turns "no proper normal intermediate field, and separable" into a prime-degree Galois
bottom layer. -/
theorem isSolvable_inertia
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    Group.IsSolvable (P.inertia Gal(L/K)) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  obtain ⟨W, _, _, _, _, hWp, _, _, θ, _, hexact, _, hcyclic, _⟩ :=
    IsDiscreteValuationRing.exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity A K L P
  rw [ringChar.eq (IsLocalRing.ResidueField A) p] at hWp
  let : Group.IsNilpotent W := (hWp (Fact.out : p.Prime).pos).isNilpotent
  let : IsCyclic (rootsOfUnity (P.ramificationIdx A) ((integralClosure A L) ⧸ P)) := hcyclic
  exact Group.isSolvable_of_ker_le_range W.subtype θ hexact.monoidHom_ker_eq.le


/-- Solvability over the fixed field of the inertia group. -/
theorem isSolvable_over_fixedField_inertia
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    Group.IsSolvable Gal(L/IntermediateField.fixedField (P.inertia Gal(L/K))) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : Group.IsSolvable (P.inertia Gal(L/K)) := isSolvable_inertia A K L p P
  exact isSolvable_galois_fixedField (P.inertia Gal(L/K))

/-- A nontrivial solvable group whose subgroup lattice is coatomic has a prime cyclic quotient. -/
private theorem exists_normal_subgroup_prime_card_quotient_of_isSolvable
    (G : Type*) [Group G] [Group.IsSolvable G] [Nontrivial G]
    [IsCoatomic (Subgroup G)] :
    ∃ (H : Subgroup G) (_ : H.Normal),
      IsCoatom H ∧ (Nat.card (G ⧸ H)).Prime ∧ IsCyclic (G ⧸ H) := by
  obtain ⟨H, hH, hcom⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (commutator G)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne
  have : H.Normal := Subgroup.Normal.of_commutator_le G hcom
  have : Nontrivial (G ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH.ne_top
  let : IsMulCommutative (G ⧸ H) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcom
  let : CommGroup (G ⧸ H) := { (inferInstance : Group (G ⧸ H)) with mul_comm := mul_comm' }
  have : IsSimpleGroup (G ⧸ H) := ⟨fun J _ => by
    have hle : H ≤ J.comap (QuotientGroup.mk' H) := by
      intro x hx
      change (x : G ⧸ H) ∈ J
      rw [(QuotientGroup.eq_one_iff x).mpr hx]
      exact J.one_mem
    rcases eq_or_lt_of_le hle with heq | hlt
    · refine Or.inl <| Subgroup.comap_injective (QuotientGroup.mk'_surjective H) ?_
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      exact heq.symm
    · refine Or.inr <| Subgroup.comap_injective (QuotientGroup.mk'_surjective H) ?_
      rw [Subgroup.comap_top]
      exact hH.2 _ hlt⟩
  exact ⟨H, inferInstance, hH, IsSimpleGroup.prime_card, inferInstance⟩

/-- Passing to the top of a tower with a nontrivial first layer strictly lowers the degree. -/
private theorem finrank_lt_of_one_lt_finrank_bot (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Module.Finite E L]
    (h : 1 < Module.finrank K E) : Module.finrank E L < Module.finrank K L := by
  have hmul := Module.finrank_mul_finrank K E L
  have hpos : 0 < Module.finrank E L := Module.finrank_pos
  nlinarith

/-- A nontrivial finite solvable Galois extension has a cyclic prime-degree intermediate
extension, over which the remaining extension has smaller degree.

This is the splitting step of a layer induction: it turns "finite solvable Galois" into "one
prime-degree layer plus a strictly smaller problem", and the strict inequality
`Module.finrank E L < Module.finrank K L` is the decreasing measure such an induction recurses
on. -/
theorem exists_intermediateField_prime_finrank_of_isSolvable
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable Gal(L/K)]
    (hdegree : 1 < Module.finrank K L) :
    ∃ E : IntermediateField K L, IsGalois K E ∧
      (Module.finrank K E).Prime ∧ IsCyclic Gal(E/K) ∧
      Module.finrank E L < Module.finrank K L ∧ IsGalois E L ∧
      Group.IsSolvable Gal(L/E) := by
  have hcard : 1 < Nat.card Gal(L/K) := by
    simpa only [IsGalois.card_aut_eq_finrank] using hdegree
  let : Fintype Gal(L/K) := Fintype.ofFinite _
  have : Nontrivial Gal(L/K) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨H, hnormal, hH, hprime, hcyclic⟩ :=
    exists_normal_subgroup_prime_card_quotient_of_isSolvable Gal(L/K)
  let E := IntermediateField.fixedField H
  let e := IsGalois.normalAutEquivQuotient H
  have hdeg : Module.finrank K E = Nat.card (Gal(L/K) ⧸ H) := by
    rw [← IsGalois.card_aut_eq_finrank K E]
    exact (Nat.card_congr e.toEquiv).symm
  refine ⟨E, inferInstance, hdeg ▸ hprime,
    isCyclic_of_surjective e e.surjective, ?_, inferInstance, ?_⟩
  · exact finrank_lt_of_one_lt_finrank_bot K E L (hdeg ▸ hprime.one_lt)
  · exact isSolvable_galois_fixedField H


/-- **An injective map from a domain admitting a map to a ring of prime characteristic has target
characteristic zero or that prime.**

In a layer recursion the base field `L` carries no characteristic hypothesis of its own, only the
residue characteristic of `A` does, and this is what turns that into the equal-versus-mixed
dichotomy on `L` that decides whether a purely inseparable layer can occur at all. -/
theorem charZero_or_charP_of_injective
    {R S T : Type*} [CommRing R] [IsDomain R]
    [Semiring S] [Semiring T] [Nontrivial T]
    (f : R →+* S) (hf : Function.Injective f) (g : R →+* T)
    (p : ℕ) [Fact p.Prime] [CharP T p] : CharZero S ∨ CharP S p := by
  rcases CharP.char_is_prime_or_zero R (ringChar R) with hprime | hzero
  · have hdvd : p ∣ ringChar R := (CharP.cast_eq_zero_iff T p _).mp (by
      simpa only [map_natCast, map_zero] using congrArg g (CharP.cast_eq_zero R (ringChar R)))
    have heq : p = ringChar R := (hprime.eq_one_or_self_of_dvd p hdvd).resolve_left
      (Fact.out : p.Prime).ne_one
    let : CharP R p := ringChar.of_eq heq.symm
    exact Or.inr (charP_of_injective_ringHom hf p)
  · let : CharZero R := (CharP.ringChar_zero_iff_CharZero R).mp hzero
    exact Or.inl (charZero_of_injective_ringHom hf)

/-- A nontrivial purely inseparable extension contains an element generating a degree `p`
subextension, namely a suitable `p`-power of an element outside the base.

This is the splitting step in the purely inseparable case, which a layer induction has to handle
alongside the Galois one (`exists_intermediateField_prime_finrank_of_isSolvable`).  The witness
`y` satisfies `y ^ p ∈ (algebraMap F E).range`, so the layer it cuts out is the degree-`p` radical
extension the prime-degree solver expects. -/
theorem exists_intermediateField_finrank_eq_of_isPurelyInseparable
    (F E : Type*) [Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E]
    (p : ℕ) [ExpChar F p] (hbot : (⊥ : IntermediateField F E) ≠ ⊤) :
    ∃ y : E, y ^ p ∈ (algebraMap F E).range ∧
      Module.finrank F (IntermediateField.adjoin F {y}) = p := by
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ (algebraMap F E).range := by
    by_contra! h
    exact hbot (eq_top_iff.mpr fun x _ => IntermediateField.mem_bot.mpr (h x))
  have he : 0 < IsPurelyInseparable.elemExponent F x := by
    by_contra! h0
    have := IsPurelyInseparable.elemExponent_def' F p x
    rw [Nat.le_zero.mp h0, pow_zero, pow_one] at this
    exact hx this
  set e := IsPurelyInseparable.elemExponent F x
  refine ⟨x ^ p ^ (e - 1), ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel he]
    exact IsPurelyInseparable.elemExponent_def' F p x
  · have hy : IsPurelyInseparable.elemExponent F (x ^ p ^ (e - 1)) = 1 := by
      apply le_antisymm
      · apply IsPurelyInseparable.elemExponent_le_of_pow_mem' (K := F) p
        rw [pow_one, ← pow_mul, ← pow_succ, Nat.sub_add_cancel he]
        exact IsPurelyInseparable.elemExponent_def' F p x
      · by_contra h1
        push Not at h1
        have h0 := Nat.lt_one_iff.mp h1
        have := IsPurelyInseparable.elemExponent_def' F p (x ^ p ^ (e - 1))
        rw [h0, pow_zero, pow_one] at this
        exact IsPurelyInseparable.elemExponent_min' F p (Nat.sub_lt he one_pos) this
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
      IsPurelyInseparable.minpoly_natDegree_eq' F p, hy, pow_one]

/-- A property of intermediate fields of a finite solvable Galois extension that holds for
the base and propagates along cyclic Galois steps of prime degree holds for the top. -/
private theorem IntermediateField.induction_on_isSolvable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable Gal(L/K)]
    (Q : IntermediateField K L → Prop) (hbot : Q ⊥)
    (hstep : ∀ (E : IntermediateField K L) (F : IntermediateField E L), IsGalois E F →
      (Module.finrank E F).Prime → IsCyclic Gal(F/E) → Q E → Q (F.restrictScalars K)) :
    Q ⊤ := by
  suffices h : ∀ n (E : IntermediateField K L), Module.finrank E L = n →
      Group.IsSolvable Gal(L/E) → Q E → Q ⊤ by
    exact h _ ⊥ rfl
      (Group.isSolvable_of_isSolvable_injective
        (f := AlgEquiv.restrictScalarsHom K (S := (⊥ : IntermediateField K L)) (A := L))
        (AlgEquiv.restrictScalars_injective K)) hbot
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hn hsol hE
    by_cases h1 : Module.finrank E L = 1
    · exact IntermediateField.finrank_eq_one_iff_eq_top.mp h1 ▸ hE
    · have hlt : 1 < Module.finrank E L := lt_of_le_of_ne Module.finrank_pos (Ne.symm h1)
      obtain ⟨F, hFgal, hFp, hFcyc, hFlt, _, hFsol⟩ :=
        exists_intermediateField_prime_finrank_of_isSolvable E L hlt
      exact ih _ (hn ▸ hFlt) (F.restrictScalars K) rfl hFsol (hstep E F hFgal hFp hFcyc hE)

/-- A property of intermediate fields of a finite purely inseparable extension of exponential
characteristic `p` that holds for the base and propagates along purely inseparable steps of
degree `p` holds for the top. -/
private theorem IntermediateField.induction_on_isPurelyInseparable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L] (p : ℕ) [Fact p.Prime] [ExpChar K p]
    (Q : IntermediateField K L → Prop) (hbot : Q ⊥)
    (hstep : ∀ (E : IntermediateField K L) (F : IntermediateField E L),
      IsPurelyInseparable E F → Module.finrank E F = p → Q E → Q (F.restrictScalars K)) :
    Q ⊤ := by
  suffices h : ∀ n (E : IntermediateField K L), Module.finrank E L = n → Q E → Q ⊤ from
    h _ ⊥ rfl hbot
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hn hE
    by_cases htop : E = ⊤
    · exact htop ▸ hE
    have : ExpChar E p := ExpChar.of_injective_algebraMap' K (A := E) p
    have hne : (⊥ : IntermediateField E L) ≠ ⊤ := fun h =>
      htop (by simpa using congrArg (IntermediateField.restrictScalars K) h)
    obtain ⟨y, -, hy⟩ := exists_intermediateField_finrank_eq_of_isPurelyInseparable E L p hne
    let F := IntermediateField.adjoin E {y}
    have hlt : Module.finrank F L < Module.finrank E L :=
      finrank_lt_of_one_lt_finrank_bot E F L (hy ▸ (Fact.out : p.Prime).one_lt)
    exact ih _ (hn ▸ hlt) (F.restrictScalars K) rfl
      (hstep E F (IsPurelyInseparable.tower_bot E F L) hy hE)

/-- A finite extension `M / L` sits inside a finite normal extension `N / L`, namely the normal
closure of `M / L` inside an algebraic closure of `M`. The data is packaged existentially so
that `N` may be used as an opaque type.

Pure field theory: no discrete valuation rings, no residue fields. -/
theorem exists_normalClosure_data (L : Type uL) (M : Type uM)
    [Field L] [Field M] [Algebra L M] [Module.Finite L M] :
    ∃ (N : Type uM) (_ : Field N) (_ : Algebra L N) (_ : Algebra M N)
      (_ : IsScalarTower L M N) (_ : Module.Finite L N), Normal L N :=
  ⟨IntermediateField.normalClosure L M (AlgebraicClosure M), inferInstance, inferInstance,
    inferInstance,
    normalClosure.instIsScalarTowerSubtypeMemIntermediateFieldNormalClosure L M
      (AlgebraicClosure M),
    normalClosure.is_finiteDimensional L M (AlgebraicClosure M),
    normalClosure.normal L M (AlgebraicClosure M)⟩

/-- Extensions of discrete valuation rings compose. -/
private theorem isExtension_trans (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C] [IsDiscreteValuationRing A]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension B C] : IsDiscreteValuationRing.IsExtension A C := by
  have hinj : Function.Injective (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    exact (FaithfulSMul.algebraMap_injective B C).comp (FaithfulSMul.algebraMap_injective A B)
  have : IsLocalHom (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    infer_instance
  exact { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective A C).mpr hinj }

/-- Reduction of the complete case of Epp's theorem to a normal top extension: the finite
extension `M / L` may be replaced by its normal closure `N`, with `C` replaced by the
integral closure of `C` in `N`. -/
theorem exists_finite_extension_isWeakSolution_of_normal
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    [Module.Finite L M]
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    (hnormal : ∀ (C' : Type uM) (N : Type uM)
      [CommRing C'] [IsDomain C'] [IsDiscreteValuationRing C'] [Field N]
      [Algebra B C'] [Algebra A C'] [Algebra C' N] [Algebra L N] [Algebra K N]
      [Algebra B N] [Algebra A N]
      [IsScalarTower A B C'] [IsScalarTower A C' N] [IsScalarTower B C' N]
      [IsScalarTower B L N] [IsScalarTower A K N] [IsScalarTower K L N]
      [IsDiscreteValuationRing.IsExtension B C'] [IsDiscreteValuationRing.IsExtension A C']
      [IsFractionRing C' N] [Module.Finite L N] [Normal L N]
      [IsAdicComplete (IsLocalRing.maximalIdeal C') C'] [IsIntegralClosure C' B N],
      ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
        (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
        ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uM, uK, uM, uK,
            max uM uK, uK, max uM uK} A C' K N K₁,
          D.IsWeakSolution) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
          max uM uK, uK, max uM uK} A C K M K₁,
        D.IsWeakSolution := by
  classical
  have hchar : CharZero K ∨ CharP K p :=
    charZero_or_charP_of_injective (algebraMap A K) (IsFractionRing.injective A K)
      (IsLocalRing.residue A) p
  by_cases hAC : IsDiscreteValuationRing.IsWeaklyUnramified A C
  · obtain ⟨D⟩ := nonempty_integralClosureBaseChange A C K M K
    exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      D, isWeakSolution_self A C K M D hAC⟩
  by_cases hprime : CharP K p ∧ IsGalois L M ∧ Module.finrank L M = p
  · let : CharP K p := hprime.1
    let : IsGalois L M := hprime.2.1
    obtain ⟨K₁, hK₁, hKK₁, hAK₁, hAKK₁, hfin, hgal, _, D, hD⟩ :=
      IsDiscreteValuationRing.exists_isGalois_totallyRamified_isWeakSolution_of_charP
        A B C K L M p (Fact.out : p.Prime) hprime.2.2 hweak hresidue
    exact ⟨K₁, hK₁, hKK₁, hAK₁, hAKK₁, hfin, D, hD⟩
  have hBC : ¬ IsDiscreteValuationRing.IsWeaklyUnramified B C :=
    fun h => hAC (isWeaklyUnramified_trans A B C hweak h)
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  let : Module.Finite B C := Module.Finite.equiv
    (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv
  have hnotunram : ¬ Algebra.FormallyUnramified B C := by
    intro h
    let : Algebra.FormallyUnramified B C := h
    exact hBC (isWeaklyUnramified_of_formallyUnramified B C)
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := isAdicComplete_of_finite B C
  obtain ⟨N, _instFieldN, _instAlgLN, _instAlgMN, _instTowerLMN, _instFinLN, _instNormalLN⟩ :=
    exists_normalClosure_data L M
  let : Module.Finite M N := Module.Finite.right L M N
  let : Algebra K N := ((algebraMap M N).comp (algebraMap K M)).toAlgebra
  let : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun k => by
    change algebraMap M N (algebraMap K M k) = algebraMap L N (algebraMap K L k)
    rw [IsScalarTower.algebraMap_apply K L M, ← IsScalarTower.algebraMap_apply L M N]
  let : Algebra C N := ((algebraMap M N).comp (algebraMap C M)).toAlgebra
  let : IsScalarTower C M N := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A N := ((algebraMap C N).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A K N := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap M N (algebraMap C M (algebraMap A C a)) =
      algebraMap M N (algebraMap K M (algebraMap A K a))
    rw [← IsScalarTower.algebraMap_apply A C M, ← IsScalarTower.algebraMap_apply A K M]
  let C' := integralClosure C N
  obtain ⟨hC', hfinC'⟩ :=
    isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete C M N
  let : IsDiscreteValuationRing C' := hC'
  let : Module.Finite C C' := hfinC'
  let : IsFractionRing C' N :=
    IsIntegralClosure.isFractionRing_of_finite_extension C M N C'
  let : FaithfulSMul C C' := (faithfulSMul_iff_algebraMap_injective C C').mpr fun _ _ h =>
    IsFractionRing.injective C M ((algebraMap M N).injective (congrArg (algebraMap C' N) h))
  let : IsLocalHom (algebraMap C C') := Algebra.IsIntegral.isLocalHom C C'
  let : IsDiscreteValuationRing.IsExtension C C' := ⟨⟩
  let : Algebra A C' := ((algebraMap C C').comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A C' N := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap C N (algebraMap A C a) =
      algebraMap C' N (algebraMap C C' (algebraMap A C a))
    rw [← IsScalarTower.algebraMap_apply C C' N]
  let : IsDiscreteValuationRing.IsExtension A C' := isExtension_trans A C C'
  let : Algebra B N := ((algebraMap M N).comp (algebraMap B M)).toAlgebra
  let : IsScalarTower B M N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B L N := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap M N (algebraMap B M b) =
      algebraMap L N (algebraMap B L b)
    rw [IsScalarTower.algebraMap_apply B L M, ← IsScalarTower.algebraMap_apply L M N]
  let : IsScalarTower B C N := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap M N (algebraMap B M b) =
      algebraMap M N (algebraMap C M (algebraMap B C b))
    rw [← IsScalarTower.algebraMap_apply B C M]
  let : Algebra B C' := ((algebraMap C C').comp (algebraMap B C)).toAlgebra
  let : IsScalarTower B C C' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B C' N := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap M N (algebraMap B M b) =
      algebraMap C' N (algebraMap C C' (algebraMap B C b))
    rw [← IsScalarTower.algebraMap_apply C C' N]
    exact IsScalarTower.algebraMap_apply B C N b
  let : IsScalarTower A B C' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap C C' (algebraMap A C a) =
      algebraMap C C' (algebraMap B C (algebraMap A B a))
    rw [← IsScalarTower.algebraMap_apply A B C]
  let : IsDiscreteValuationRing.IsExtension B C' := isExtension_trans B C C'
  let : Module.Finite B C' := Module.Finite.trans (R := B) C C'
  let : IsAdicComplete (IsLocalRing.maximalIdeal C') C' := isAdicComplete_of_finite C C'
  let : IsIntegralClosure C' B N := isIntegralClosure_of_isAdicComplete B C' L N
  exact exists_isWeakSolution_of_tower A C C' K M N (hnormal C' N)

/-- The canonical map on integral closures associated to a commutative ring square.

The algebra `integralClosure A K₁ → integralClosure B (E i)` that `isWeakSolution_factor` and
`integralClosure_factor_isExtension` speak of is this map turned into an `Algebra` instance. -/
def mapIntegralClosureOfTower
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S U] [IsScalarTower R T U] :
    integralClosure R T →ₐ[R] (integralClosure S U).restrictScalars R :=
  (Subalgebra.inclusion (show integralClosure R U ≤
    (integralClosure S U).restrictScalars R from fun _ hx => hx.tower_top)).comp
    (IsScalarTower.toAlgHom R T U).mapIntegralClosure

/-- The integral-closure map is induced by the map of ambient rings. -/
lemma mapIntegralClosureOfTower_apply
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S U] [IsScalarTower R T U] (x : integralClosure R T) :
    (mapIntegralClosureOfTower R S T U x : U) = algebraMap T U x := rfl

/-- Injectivity of the ambient map implies injectivity on integral closures.

Injectivity is what upgrades the induced algebra to a `FaithfulSMul`, which every `IsExtension`
conclusion about the map needs. -/
lemma mapIntegralClosureOfTower_injective
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S U] [IsScalarTower R T U]
    (h : Function.Injective (algebraMap T U)) :
    Function.Injective (mapIntegralClosureOfTower R S T U) := by
  intro x y hxy
  exact Subtype.ext (h (congrArg Subtype.val hxy))

/-- A map out of an integral local algebra is local when its restriction to the base is local. -/
lemma isLocalHom_of_isIntegral_tower
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] [IsLocalHom (algebraMap R T)] :
    IsLocalHom (algebraMap S T) := by
  let q := (IsLocalRing.maximalIdeal T).under S
  have hq : q.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
    change ((IsLocalRing.maximalIdeal T).comap
      ((algebraMap S T).comp (algebraMap R S))).IsMaximal
    rw [← IsScalarTower.algebraMap_eq, IsLocalRing.maximalIdeal_comap]
    infer_instance
  have heq : q = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hq
  exact ((IsLocalRing.local_hom_TFAE (algebraMap S T)).out 1 5).mpr heq


/-- **The integral closure of a complete discrete valuation ring in a finite extension of its
fraction field is again a complete discrete valuation ring**, module-finite over the base and with
that extension as its fraction field. -/
@[sga "6 X 7.16" "special case"]
theorem integralClosure_isCompleteDVR
    (B L E : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Field E] [Algebra B L] [Algebra L E] [Algebra B E]
    [IsScalarTower B L E] [IsFractionRing B L] [Module.Finite L E]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    ∃ hD : IsDiscreteValuationRing (integralClosure B E),
      let := hD
      ∃ _ : IsDiscreteValuationRing.IsExtension B (integralClosure B E),
        Module.Finite B (integralClosure B E) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure B E))
          (integralClosure B E) ∧
        IsFractionRing (integralClosure B E) E := by
  obtain ⟨hD, hfin⟩ :=
    isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L E
  let := hD
  let := hfin
  have hinj : Function.Injective (algebraMap B (integralClosure B E)) := by
    intro x y h
    apply IsFractionRing.injective B L
    apply (algebraMap L E).injective
    simpa only [← IsScalarTower.algebraMap_apply B L E, Subalgebra.coe_algebraMap] using
      congrArg Subtype.val h
  let : FaithfulSMul B (integralClosure B E) :=
    (faithfulSMul_iff_algebraMap_injective B _).mpr hinj
  let : IsLocalHom (algebraMap B (integralClosure B E)) :=
    Algebra.IsIntegral.isLocalHom B _
  let : IsDiscreteValuationRing.IsExtension B (integralClosure B E) := ⟨⟩
  exact ⟨hD, inferInstance, hfin, isAdicComplete_of_finite B _,
    IsIntegralClosure.isFractionRing_of_finite_extension B L E _⟩

/-- The integral-closure map attached to a field factor is an extension of complete DVRs.

That is, the square `A → A₁ = integralClosure A K₁`, `B → B₁ = integralClosure B E` again
presents an extension of complete discrete valuation rings with the right fraction fields, which
is what lets a factor-level recursion re-enter at `(A₁, B₁)` after one layer. -/
theorem integralClosure_factor_isExtension
    (A B K L K₁ E : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field E]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [Algebra A E] [Algebra K₁ E] [IsScalarTower A B E] [IsScalarTower A K₁ E]
    [Module.Finite K K₁] [Module.Finite L E]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    let A₁ := integralClosure A K₁
    let B₁ := integralClosure B E
    let f := mapIntegralClosureOfTower A B K₁ E
    letI : Algebra A₁ B₁ := f.toRingHom.toAlgebra
    ∃ (hA₁ : IsDiscreteValuationRing A₁) (hB₁ : IsDiscreteValuationRing B₁),
      let := hA₁
      let := hB₁
      IsDiscreteValuationRing.IsExtension A₁ B₁ ∧
        IsAdicComplete (IsLocalRing.maximalIdeal A₁) A₁ ∧
        IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁ ∧
        IsFractionRing A₁ K₁ ∧ IsFractionRing B₁ E := by
  obtain ⟨hA₁, hAA₁, hAfin, hAc, hAf⟩ := integralClosure_isCompleteDVR A K K₁
  obtain ⟨hB₁, hBB₁, hBfin, hBc, hBf⟩ := integralClosure_isCompleteDVR B L E
  let := hA₁
  let := hB₁
  let := hAA₁
  let := hBB₁
  let A₁ := integralClosure A K₁
  let B₁ := integralClosure B E
  let f := mapIntegralClosureOfTower A B K₁ E
  let : Algebra A₁ B₁ := f.toRingHom.toAlgebra
  let : IsScalarTower A A₁ B₁ :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : IsLocalHom (algebraMap A B₁) := by
    rw [IsScalarTower.algebraMap_eq A B B₁]
    infer_instance
  let : FaithfulSMul A₁ B₁ := (faithfulSMul_iff_algebraMap_injective A₁ B₁).mpr
    (mapIntegralClosureOfTower_injective A B K₁ E (algebraMap K₁ E).injective)
  let : IsLocalHom (algebraMap A₁ B₁) := isLocalHom_of_isIntegral_tower A A₁ B₁
  exact ⟨hA₁, hB₁, ⟨⟩, hAc, hBc, hAf, hBf⟩

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraK₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKK₁L₁

/-- The reduced compositum in a base-change package is a finite product of finite fields. -/
private theorem finiteFieldFactors_baseChange
    (A B K L K₁ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁) :
    IsDiscreteValuationRing.IsNonemptyFiniteProductOfFiniteFieldExtensions L D.L₁ := by
  let eA := IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁)
  let eB := IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)
  exact (IsDiscreteValuationRing.integralClosures_after_finite_fraction_field_extension
    A B K L K₁ D.L₁ D.A₁ D.B₁ D.eL₁ eA eB D.eL₁_left D.eL₁_right
    (fun x => IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x)
    (fun x => by rw [← IsScalarTower.algebraMap_apply K L D.L₁,
      ← IsScalarTower.algebraMap_apply K K₁ D.L₁])
    (fun x => by
      rw [show (eA x : K₁) = algebraMap D.A₁ K₁ x from
        IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x]
      exact D.ringSquare x)).1

universe uF uD₁ uD₂ uD₃

/-- The field factors inherit both field maps and the original ring square.

Note the output universe: `E : Fin n → Type (max uL uD₁)`, where `uD₁` is the package's `L₁`
universe.  So a step built from this lands its output in a universe that is in general larger than
its input's, and an induction whose members must all live in one universe has to collapse them —
see `Stacks.EppTheorem.exists_finiteFieldFactors_of_package` for the collapsed wrapper. -/
theorem finiteFieldFactors_compatible
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uF)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uF, uD₁, uD₂, uD₃}
      A B K L K₁) :
    ∃ (n : ℕ) (E : Fin n → Type (max uL uD₁))
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra L (E i))
      (_ : ∀ i, Algebra K₁ (E i)) (_ : ∀ i, Algebra B (E i))
      (_ : ∀ i, Algebra A (E i))
      (_ : ∀ i, IsScalarTower B L (E i))
      (_ : ∀ i, IsScalarTower A B (E i))
      (_ : ∀ i, IsScalarTower A K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i)),
      0 < n ∧ ∃ e : D.L₁ ≃ₐ[L] ∀ i, E i,
        ∀ (i : Fin n) (x : K₁),
          e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x := by
  obtain ⟨n, E, hE, hLE, hfin, hn, ⟨e⟩⟩ := finiteFieldFactors_baseChange A B K L K₁ D
  let := hE
  let := hLE
  let := hfin
  let : ∀ i, Algebra K₁ (E i) := fun i =>
    (((Pi.evalAlgHom L E i).toRingHom.comp e.toRingHom).comp
      (algebraMap K₁ D.L₁)).toAlgebra
  let : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower B L (E i) := fun i => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower A B (E i) := fun i => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower A K₁ (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap L (E i) (algebraMap B L (algebraMap A B a)) =
        e (algebraMap K₁ D.L₁ (algebraMap A K₁ a)) i
      rw [← IsScalarTower.algebraMap_apply A B L]
      have hs : algebraMap K₁ D.L₁ (algebraMap A K₁ a) =
          algebraMap L D.L₁ (algebraMap A L a) := by
        rw [IsScalarTower.algebraMap_apply A K K₁,
          IsScalarTower.algebraMap_apply A K L,
          ← IsScalarTower.algebraMap_apply K K₁ D.L₁,
          ← IsScalarTower.algebraMap_apply K L D.L₁]
      rw [hs, e.commutes]
      rfl
  exact ⟨n, E, hE, hLE, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hfin, hn, e, fun _ _ => rfl⟩

end IsDiscreteValuationRing
