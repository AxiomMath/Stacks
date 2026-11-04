module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.TensorAlgebra.Localization

/-!
# The rank strata and components of the determinant line

Let `R` be a commutative ring and `M` a finite projective `R`-module. The rank of `M` is locally
constant on `Spec R`, so the rank strata are clopen and give a decomposition of `R` into
orthogonal idempotents. The *determinant line* of `M` is the sum, inside the exterior algebra of
`M`, of the top exterior power on each rank stratum.

## Main definitions

* `ProjectiveDeterminant.rankIdempotent`: the idempotent cutting out a rank stratum.
* `ProjectiveDeterminant.submodule`, `ProjectiveDeterminant.module`: the determinant line, as a
  submodule of the exterior algebra and as a module in its own right.

## Main results

* `ProjectiveDeterminant.component_finite_projective`: each rank component is finite projective.
* `ProjectiveDeterminant.submodule_eq_iSup_finset_cover`: the determinant line is the supremum
  of the components over any finite cover of the rank strata.

## Implementation notes

Writing the determinant line inside the exterior algebra, rather than as an abstract product of
top exterior powers, makes the rank-stratum decomposition canonical and supplies the inclusion
used in the annihilator description. The rank strata are indexed by `ℕ`; only finitely many are
nonempty, and the corresponding idempotents are orthogonal and sum to `1`.

## References

* [Stacks Project, Section 0FJ9](https://stacks.math.columbia.edu/tag/0FJ9)
-/

namespace ProjectiveDeterminant

/-! ### The determinant line and the determinant of an endomorphism -/

section

universe u v w

@[expose] public section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The locus on which a module has rank `n` at every stalk. -/
public abbrev rankLocus (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    Set (PrimeSpectrum R) := {p | Module.rankAtStalk M p = n}

/-- Rank strata of a finite projective module are clopen. -/
public theorem rankLocus_isClopen [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    IsClopen (rankLocus (R := R) M n) := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let : Module.Flat R M := Module.Flat.of_projective
  exact Module.isLocallyConstant_rankAtStalk.isClopen_fiber n

/-- The idempotent cutting out the rank `n` component of a finite projective module. -/
public noncomputable def rankIdempotent [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) : R :=
  Classical.choose (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
    (rankLocus_isClopen (R := R) (M := M) n))

/-- The rank idempotent cuts out precisely its rank stratum. -/
public theorem rankIdempotent_spec [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) : IsIdempotentElem (rankIdempotent (R := R) (M := M) n) ∧
      rankLocus (R := R) M n =
        (PrimeSpectrum.basicOpen (rankIdempotent (R := R) (M := M) n) :
          Set (PrimeSpectrum R)) :=
  (Classical.choose_spec (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
    (rankLocus_isClopen (R := R) (M := M) n))).1

/-- The `n`th component of the determinant line, embedded in the exterior algebra. -/
public noncomputable def component [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) : Submodule R (ExteriorAlgebra R M) :=
  (⋀[R]^n M).map ((rankIdempotent (R := R) (M := M) n) •
    (LinearMap.id : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M))

/-- The determinant line, formed as the sum of the top exterior powers on the rank strata. -/
@[sga "6 X 6.2" "special case"]
public noncomputable def submodule [Module.Finite R M] [Module.Projective R M] :
    Submodule R (ExteriorAlgebra R M) :=
  ⨆ n : ℕ, component (M := M) n

/-- Each rank component belongs to the determinant line. -/
public theorem component_le_submodule [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) : component (R := R) (M := M) n ≤ submodule (R := R) (M := M) :=
  le_iSup (fun n : ℕ => component (R := R) (M := M) n) n

/-- The determinant module of a finite projective module. -/
public noncomputable abbrev module [Module.Finite R M] [Module.Projective R M] :=
  ↥(submodule (R := R) (M := M))

/-- The canonical inclusion of the determinant line into the exterior algebra. -/
public noncomputable abbrev inclusion [Module.Finite R M] [Module.Projective R M] :
    module (R := R) (M := M) →ₗ[R] ExteriorAlgebra R M :=
  (submodule (R := R) (M := M)).subtype

section Invertibility

open TensorProduct

variable {P : Type*} [AddCommGroup P] [Module R P]

private theorem local_equiv [Module.Finite R P] [Module.Projective R P]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk P p = 1)
    (J : Ideal R) [J.IsMaximal] :
    Nonempty (LocalizedModule J.primeCompl P ≃ₗ[Localization.AtPrime J]
      Localization.AtPrime J) := by
  let : Module.Free (Localization.AtPrime J)
      (LocalizedModule J.primeCompl P) := Module.free_of_flat_of_isLocalRing
  have hd : Module.finrank (Localization.AtPrime J)
      (LocalizedModule J.primeCompl P) = 1 := h ⟨J, inferInstance⟩
  exact ⟨(Module.nonempty_linearEquiv_of_finrank_eq_one hd).some.symm⟩

private theorem rank_one_smul_commutes {A Q : Type*} [CommRing A]
    [AddCommGroup Q] [Module A Q] (e : Q ≃ₗ[A] A)
    (φ : Q →ₗ[A] A) (x y : Q) : φ x • y = φ y • x := by
  have hφ (z : Q) : φ z = e z * φ (e.symm 1) := by
    calc
      φ z = φ (e.symm (e z)) := by simp
      _ = φ ((e z) • e.symm 1) := by
        congr 1
        simpa only [smul_eq_mul, mul_one] using
          (e.symm.map_smul (e z) (1 : A))
      _ = e z * φ (e.symm 1) := by simp [map_smul, smul_eq_mul]
  apply e.injective
  simp only [map_smul, smul_eq_mul]
  rw [hφ x, hφ y]
  ring

private theorem rank_one_dual_smul_commutes [Module.Finite R P] [Module.Projective R P]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk P p = 1)
    (φ : Module.Dual R P) (x y : P) : φ x • y = φ y • x := by
  apply Module.eq_of_localization_maximal
    (Mₚ := fun (J : Ideal R) [hJ : J.IsMaximal] => LocalizedModule J.primeCompl P)
    (f := fun (J : Ideal R) [hJ : J.IsMaximal] => LocalizedModule.mkLinearMap J.primeCompl P)
  intro J hJ
  let e := (local_equiv h J).some
  let j := LocalizedModule.mkLinearMap J.primeCompl P
  let bc : IsBaseChange (Localization.AtPrime J) j :=
    IsLocalizedModule.isBaseChange J.primeCompl (Localization.AtPrime J) j
  have hh := rank_one_smul_commutes e (bc.toDual φ) (j x) (j y)
  have hx := bc.toDual_comp_apply φ x
  have hy := bc.toDual_comp_apply φ y
  dsimp [j] at hh hx hy ⊢
  simpa only [map_smul, algebraMap_smul, hx, hy] using hh

private theorem rank_one_toModuleEnd_injective [Module.Finite R P] [Module.Projective R P]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk P p = 1) :
    Function.Injective (Module.toModuleEnd R (S := R) P) := by
  intro a b hab
  apply Module.eq_of_localization_maximal
    (Mₚ := fun (J : Ideal R) [hJ : J.IsMaximal] => Localization.AtPrime J)
    (f := fun (J : Ideal R) [hJ : J.IsMaximal] =>
      Algebra.linearMap R (Localization.AtPrime J))
  intro J hJ
  let A := Localization.AtPrime J
  let Q := LocalizedModule J.primeCompl P
  let j : P →ₗ[R] Q := LocalizedModule.mkLinearMap J.primeCompl P
  let e : Q ≃ₗ[A] A := (local_equiv h J).some
  let q : Q := e.symm 1
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.mk'_surjective J.primeCompl j q
  have hjx : j x = (s : R) • q := by
    rw [← hs]
    exact (IsLocalizedModule.mk'_cancel' j x s).symm
  have habx : a • x = b • x := congrArg (fun f : Module.End R P => f x) hab
  have hjabx := congrArg j habx
  have hu : IsUnit ((algebraMap R A) s) := IsLocalization.map_units A s
  have hjabx' : a • j x = b • j x := by simpa only [map_smul] using hjabx
  rw [hjx] at hjabx'
  have hsq : ((algebraMap R A) s) • ((algebraMap R A) a • q) =
      ((algebraMap R A) s) • ((algebraMap R A) b • q) := by
    calc
      _ = a • ((s : R) • q) := by rw [algebraMap_smul, algebraMap_smul, smul_comm]
      _ = b • ((s : R) • q) := hjabx'
      _ = _ := by rw [algebraMap_smul, algebraMap_smul, smul_comm]
  have hq := hu.smul_left_cancel.mp hsq
  have ha := congrArg e hq
  simp only [map_smul, smul_eq_mul] at ha
  have heq : e q = 1 := e.apply_symm_apply 1
  rw [heq, mul_one, mul_one] at ha
  exact ha

theorem invertible_of_rankAtStalk_eq_one [Module.Finite R P]
    [Module.Projective R P]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk P p = 1) :
    Module.Invertible R P := by
  let c : (Module.Dual R P ⊗[R] P) →ₗ[R] R := contractLeft R P
  let d : (Module.Dual R P ⊗[R] P) →ₗ[R] Module.End R P := dualTensorHom R P P
  let s : R →+* Module.End R P := Module.toModuleEnd R (S := R) P
  have hrel (t : Module.Dual R P ⊗[R] P) : s (c t) = d t := by
    induction t using TensorProduct.induction_on with
    | zero =>
      apply LinearMap.ext
      intro y
      simp [c, d, s]
    | tmul φ x =>
      apply LinearMap.ext
      intro y
      show (φ x) • y = (φ y) • x
      exact rank_one_dual_smul_commutes h φ x y
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hd : Function.Bijective d := dualTensorHom_bijective
  have hs : Function.Injective s := rank_one_toModuleEnd_injective h
  constructor
  constructor
  · intro x y hxy
    apply hd.1
    rw [← hrel x, ← hrel y, hxy]
  · intro r
    obtain ⟨t, ht⟩ := hd.2 (s r)
    exact ⟨t, hs ((hrel t).trans ht)⟩

/-- Exterior powers preserve finite projectivity. The projective part is obtained by realizing a
finite projective module as a retract of a finite free module and applying the exterior-power
functor to the retraction. -/
@[sga "6 V 2.2" "special case"]
private theorem exteriorPower_finite_projective [Module.Finite R M]
    [Module.Projective R M] (n : ℕ) :
    Module.Finite R (⋀[R]^n M) ∧ Module.Projective R (⋀[R]^n M) := by
  classical
  have hfin : Module.Finite R (⋀[R]^n M) := inferInstance
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := M)
  let v : S → M := Subtype.val
  have hv : Submodule.span R (Set.range v) = ⊤ := by simpa [v] using hS
  let F := S → R
  let q : F →ₗ[R] M := Fintype.linearCombination R v
  have hq : Function.Surjective q := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
  obtain ⟨i, hi⟩ := Module.projective_lifting_property q LinearMap.id hq
  let fi : (⋀[R]^n M) →ₗ[R] (⋀[R]^n F) := exteriorPower.map n i
  let fq : (⋀[R]^n F) →ₗ[R] (⋀[R]^n M) := exteriorPower.map n q
  have hsplit : fq.comp fi = LinearMap.id := by
    rw [← exteriorPower.map_comp, hi, exteriorPower.map_id]
  exact ⟨hfin, Module.Projective.of_split fi fq hsplit⟩

/-- The cutting idempotent is idempotent as a scalar action on any module. -/
private theorem rankIdempotent_smul_smul [Module.Finite R M] [Module.Projective R M] {N : Type*}
    [AddCommGroup N] [Module R N] (n : ℕ) (x : N) :
    rankIdempotent (R := R) (M := M) n • rankIdempotent (R := R) (M := M) n • x =
      rankIdempotent (R := R) (M := M) n • x := by
  rw [← mul_smul, (rankIdempotent_spec (R := R) (M := M) n).1]

/-- Every rank component is a finite projective module. It is the image of an idempotent
endomorphism of the corresponding exterior power. -/
public theorem component_finite_projective [Module.Finite R M]
    [Module.Projective R M] (n : ℕ) :
    Module.Finite R (component (R := R) (M := M) n) ∧
      Module.Projective R (component (R := R) (M := M) n) := by
  classical
  let W := ⋀[R]^n M
  let E := ExteriorAlgebra R M
  let e : R := rankIdempotent (R := R) (M := M) n
  let p : W →ₗ[R] W := e • LinearMap.id
  have hp (x : W) : p (p x) = p x := rankIdempotent_smul_smul (R := R) (M := M) n x
  let P : Submodule R W := LinearMap.range p
  let sE : E →ₗ[R] E := e • LinearMap.id
  let iW : W →ₗ[R] E := (⋀[R]^n M).subtype
  have hmem (x : W) : sE (iW x) ∈ component (R := R) (M := M) n := by
    exact Submodule.mem_map.mpr ⟨x, x.2, rfl⟩
  let g : W →ₗ[R] component (R := R) (M := M) n :=
    (sE.comp iW).codRestrict _ hmem
  let f : P →ₗ[R] component (R := R) (M := M) n := g.comp P.subtype
  have hfix (x : P) : p x.1 = x.1 := by
    rcases x.2 with ⟨y, hy⟩
    calc
      p x.1 = p (p y) := congrArg p hy.symm
      _ = p y := hp y
      _ = x.1 := hy
  have hgp (x : W) : g (p x) = g x := by
    apply Subtype.ext
    exact rankIdempotent_smul_smul (R := R) (M := M) n (iW x)
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hval := congrArg Subtype.val hxy
      change e • (iW x.1) = e • (iW y.1) at hval
      have hx : e • iW x.1 = iW x.1 := by
        simpa [p] using congrArg iW (hfix x)
      have hy : e • iW y.1 = iW y.1 := by
        simpa [p] using congrArg iW (hfix y)
      have hxy' : x.1 = y.1 := by
        apply Submodule.subtype_injective
        exact hx.symm.trans (hval.trans hy)
      exact Subtype.ext hxy'
    · intro y
      rcases Submodule.mem_map.mp y.2 with ⟨z, hz, hzy⟩
      let zW : W := ⟨z, hz⟩
      refine ⟨⟨p zW, ⟨zW, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      exact (rankIdempotent_smul_smul (R := R) (M := M) n (iW zW)).trans hzy
  let eP : P ≃ₗ[R] component (R := R) (M := M) n := LinearEquiv.ofBijective f hbij
  have hfinW : Module.Finite R W :=
    (exteriorPower_finite_projective (R := R) (M := M) n).1
  have hfg : (component (R := R) (M := M) n).FG := by
    show ((⋀[R]^n M).map sE).FG
    exact Submodule.FG.map sE (Module.Finite.iff_fg.mp hfinW)
  have hprojW : Module.Projective R W := (exteriorPower_finite_projective (R := R) (M := M) n).2
  have hprojP : Module.Projective R P := by
    let inc : P →ₗ[R] W := P.subtype
    let proj : W →ₗ[R] P := p.codRestrict P (fun x => ⟨x, rfl⟩)
    apply Module.Projective.of_split inc proj
    apply LinearMap.ext
    intro x
    exact Subtype.ext (hfix x)
  exact ⟨Module.Finite.iff_fg.mpr hfg, Module.Projective.of_equiv' eP⟩

/-- The clopen rank strata of a finite projective module have a finite subcover of the spectrum.
Each point lies in the stratum indexed by its own stalk rank. -/
public theorem exists_finset_rankLocus_cover [Module.Finite R M]
    [Module.Projective R M] :
    ∃ s : Finset ℕ, (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ n ∈ s, rankLocus (R := R) M n := by
  have hopen (n : ℕ) : IsOpen (rankLocus (R := R) M n) :=
    (rankLocus_isClopen (R := R) (M := M) n).isOpen
  have hcover : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ n : ℕ, rankLocus (R := R) M n := by
    intro p hp
    simp only [Set.mem_iUnion]
    exact ⟨Module.rankAtStalk M p, rfl⟩
  exact isCompact_univ.elim_finite_subcover _ hopen hcover

/-- An idempotent whose basic open is empty is zero. -/
private theorem eq_zero_of_isIdempotentElem_of_basicOpen_eq_empty {e : R}
    (he : IsIdempotentElem e) (h : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) = ∅) :
    e = 0 :=
  he.eq_zero_of_isNilpotent
    ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp (TopologicalSpace.Opens.ext h))

/-- Idempotents associated to distinct stalk-rank strata are orthogonal. -/
public theorem rankIdempotent_mul_eq_zero_of_ne [Module.Finite R M]
    [Module.Projective R M] {m n : ℕ} (hmn : m ≠ n) :
    rankIdempotent (R := R) (M := M) m * rankIdempotent (R := R) (M := M) n = 0 := by
  refine eq_zero_of_isIdempotentElem_of_basicOpen_eq_empty
    ((rankIdempotent_spec (R := R) (M := M) m).1.mul_of_commute (Commute.all _ _)
      (rankIdempotent_spec (R := R) (M := M) n).1) ?_
  rw [PrimeSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf,
    ← (rankIdempotent_spec (R := R) (M := M) m).2,
    ← (rankIdempotent_spec (R := R) (M := M) n).2]
  ext p
  simp only [rankLocus, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hpm hpn => hmn (hpm.symm.trans hpn)

/-- A rank stratum with no points has zero cutting idempotent. -/
public theorem rankIdempotent_eq_zero_of_rankLocus_eq_empty [Module.Finite R M]
    [Module.Projective R M] {n : ℕ}
    (hn : rankLocus (R := R) M n = ∅) :
    rankIdempotent (R := R) (M := M) n = 0 :=
  eq_zero_of_isIdempotentElem_of_basicOpen_eq_empty (rankIdempotent_spec (R := R) (M := M) n).1
    (by rw [← (rankIdempotent_spec (R := R) (M := M) n).2, hn])

/-- The cutting idempotent acts as the identity on its determinant component. -/
public theorem rankIdempotent_smul_eq_self_of_mem_component
    [Module.Finite R M] [Module.Projective R M] {n : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ component (R := R) (M := M) n) :
    rankIdempotent (R := R) (M := M) n • x = x := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact rankIdempotent_smul_smul (R := R) (M := M) n y

/-- A finite clopen rank cover contains every nonempty rank stratum. -/
public theorem rankLocus_eq_empty_of_not_mem_finset_cover [Module.Finite R M]
    [Module.Projective R M] {s : Finset ℕ}
    (hs : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ n ∈ s, rankLocus (R := R) M n) {n : ℕ} (hn : n ∉ s) :
    rankLocus (R := R) M n = ∅ := by
  ext p
  constructor
  · intro hp
    have hp' := hs (Set.mem_univ p)
    rcases Set.mem_iUnion₂.mp hp' with ⟨m, hm, hpm⟩
    have hmn : m = n := hpm.symm.trans hp
    exact False.elim (hn (hmn ▸ hm))
  · intro hp
    exact False.elim hp

/-- Outside a finite cover of the rank strata, the associated exterior-power component vanishes.
-/
public theorem component_eq_bot_of_not_mem_finset_cover [Module.Finite R M]
    [Module.Projective R M] {s : Finset ℕ}
    (hs : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ n ∈ s, rankLocus (R := R) M n) {n : ℕ} (hn : n ∉ s) :
    component (R := R) (M := M) n = ⊥ := by
  unfold component
  rw [rankIdempotent_eq_zero_of_rankLocus_eq_empty
    (rankLocus_eq_empty_of_not_mem_finset_cover hs hn)]
  simp

/-- Outside a finite cover of the rank strata, the cutting idempotent itself vanishes: the
stratum it cuts out is empty, so its basic open is empty, so it is nilpotent, and an idempotent
nilpotent is zero. -/
public theorem rankIdempotent_eq_zero_of_not_mem_finset_cover [Module.Finite R M]
    [Module.Projective R M] {s : Finset ℕ}
    (hs : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ n ∈ s, rankLocus (R := R) M n) {n : ℕ} (hn : n ∉ s) :
    rankIdempotent (R := R) (M := M) n = 0 :=
  rankIdempotent_eq_zero_of_rankLocus_eq_empty
    (rankLocus_eq_empty_of_not_mem_finset_cover hs hn)

/-- The determinant submodule is already the supremum over any finite subcover of its rank
strata. -/
public theorem submodule_eq_iSup_finset_cover [Module.Finite R M]
    [Module.Projective R M] {s : Finset ℕ}
    (hs : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ n ∈ s, rankLocus (R := R) M n) :
    submodule (R := R) (M := M) = ⨆ n : s, component (R := R) (M := M) n := by
  show (⨆ n : ℕ, component (R := R) (M := M) n) = _
  apply le_antisymm
  · refine iSup_le fun n => ?_
    by_cases hn : n ∈ s
    · exact le_iSup_of_le ⟨n, hn⟩ le_rfl
    · rw [component_eq_bot_of_not_mem_finset_cover hs hn]
      exact bot_le
  · refine iSup_le fun n => le_iSup (fun m : ℕ => component (R := R) (M := M) m) n

end Invertibility

end

end

end ProjectiveDeterminant
