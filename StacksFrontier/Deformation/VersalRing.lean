module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace

/-!
# Uniqueness of versal rings

Formal homotopy of maps out of a versal ring, and the resulting uniqueness
statement.

## Main definitions

* `FormallyHomotopic` says that two morphisms factor through a formal
  power-series ring in the manner prescribed by a formal homotopy.

## Main results

* `Ideal.map_eq_of_formallyHomotopic_of_mem_minimalPrimes` says that formally
  homotopic maps induce the same extended ideal from a minimal prime.
* `formallyHomotopic_comp` gives postcomposition of a formal homotopy.
* `CompleteLocalAlgCat.formallyHomotopic_equivalence` says that formal homotopy is an
  equivalence relation on each hom-set, with its three clauses
  `CompleteLocalAlgCat.formallyHomotopic_refl`,
  `CompleteLocalAlgCat.formallyHomotopic_symm` and
  `CompleteLocalAlgCat.formallyHomotopic_trans`.

## Implementation notes

### Formally homotopic maps on minimal primes

The source introduces formal homotopy in the unnumbered preamble to its section.  Here it
is expressed directly using local algebra homomorphisms.  The equations in the definition
identify the constant-term specialization with the identity and the two specializations
with the given morphisms; consequently these maps have exactly the compatibility with the
fixed residue fields required of morphisms in the category.

The ideal denoted by `f(p)S` in the source is `p.map f.hom.toRingHom`.

### Postcomposition preserves formal homotopy

The category's composition `f ≫ g` denotes the composite called `g ∘ f` in the source.
The formal homotopy relation is the one introduced in the preamble to the source section.

### Formal homotopy is an equivalence relation

Reflexivity uses the homotopy in no variables, where the constant-series inclusion and the
lift both specialise to the given morphism.

Symmetry exchanges the two specialisations by substituting the homotopy into itself: the
`R`-algebra map `h : R → R[[x_1, …, x_r]]` extends, by sending each variable to itself, to a
substitution endomorphism `F` of `R[[x_1, …, x_r]]`. Since `h` is a section of the
constant-coefficient map, `F` is surjective modulo the ideal of the variables, hence
surjective by adic completeness, hence bijective because a surjective endomorphism of a
Noetherian ring is injective. Composing the homotopy with `F` and `F⁻¹` interchanges the two
specialisations.

Transitivity concatenates the variables. Given homotopies in `x_1, …, x_n` and in
`y_1, …, y_m`, one substitutes the first into the second: `R[[x]] → R[[x, y]]` sends the
variables to the first block, and `R[[y]] → R[[x, y]]` sends `R` along that composite and
the variables to the second block. Evaluating the variables of `R[[x, y]]` at the images of
the variables under the two given lifts gives a lift of the concatenated homotopy, and the
two specialisations are those of the first and the second homotopy respectively. The
identification of the two evaluations with the given lifts is uniqueness of a continuous
algebra map out of a power series ring prescribed on the constants and the variables; the
hypotheses of that uniqueness statement are supplied by comparing the product topology on
`R[[x]]` with the adic topology of its maximal ideal, which is where
the finite-coefficient description of a power of the maximal ideal is used.

## References

* [Stacks Project, Tag 0DQB](https://stacks.math.columbia.edu/tag/0DQB)
* [Stacks Project, Tag 0DQC](https://stacks.math.columbia.edu/tag/0DQC)
* [Stacks Project, Tag 0DQE](https://stacks.math.columbia.edu/tag/0DQE)
-/

@[expose] public section

namespace Deformation

/-! ### Formally homotopic maps on minimal primes -/

section
open CategoryTheory
universe u v w


namespace CompleteLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Two morphisms of complete local `Λ`-algebras are formally homotopic if they are the
two specializations of a local map out of a multivariable formal power-series ring, one
through the constant-series inclusion and the other through a local lift which is the
identity after taking constant coefficients. -/
def FormallyHomotopic {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (f₁ f₂ : R ⟶ S) : Prop :=
  ∃ (r : ℕ) (h : R →ₐ[Λ] MvPowerSeries (Fin r) R)
      (l : MvPowerSeries (Fin r) R →ₐ[Λ] S),
    IsLocalHom h.toRingHom ∧
      IsLocalHom l.toRingHom ∧
      (∀ a, MvPowerSeries.constantCoeff (h a) = a) ∧
      (∀ a, f₁.hom a = l (MvPowerSeries.C a)) ∧
      (∀ a, f₂.hom a = l (h a))

end CompleteLocalAlgCat

namespace Ideal

open CompleteLocalAlgCat

-- The induction invokes Mathlib's substantial PowerSeries ideal comparison theorem.
private theorem map_eq_map_of_constCoeff_id
    {R : Type*} [CommRing R] [IsNoetherianRing R] {p : Ideal R} [p.IsPrime] :
    ∀ n (h : R →+* MvPowerSeries (Fin n) R),
      MvPowerSeries.constantCoeff.comp h = RingHom.id R →
      Ideal.map h p ≤ Ideal.map MvPowerSeries.C p →
      Ideal.map h p = Ideal.map MvPowerSeries.C p := by
  have hpfg : p.FG := Ideal.fg_of_isNoetherianRing p
  intro n
  induction n with
  | zero =>
      intro h hcc hle
      let e := MvPowerSeries.isEmptyEquiv (Fin 0) R
      have heq : h = MvPowerSeries.C := by
        apply RingHom.ext
        intro x
        apply e.injective
        have hx := congrArg (fun f : R →+* R => f x) hcc
        simpa [e, MvPowerSeries.isEmptyEquiv, RingHom.comp_apply] using hx
      simp [heq]
  | succ n ih =>
      intro h hcc hle
      let e := MvPowerSeries.finSuccEquiv R n
      let eR := e.toRingEquiv
      have hecomp : e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
          RingHom.id _ :=
        RingHom.ext fun x => e.symm_apply_apply x
      let h' : R →+* MvPowerSeries (Fin n) R :=
        PowerSeries.constantCoeff.comp (e.toRingHom.comp h)
      have hecc : MvPowerSeries.constantCoeff.comp
          (PowerSeries.constantCoeff.comp e.toRingHom) =
          MvPowerSeries.constantCoeff := by
        apply RingHom.ext
        intro f
        simp only [RingHom.comp_apply]
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
        change MvPowerSeries.coeff (0 : Fin n →₀ ℕ)
            (PowerSeries.coeff 0 (MvPowerSeries.finSuccEquiv R n f)) =
          MvPowerSeries.coeff (0 : Fin (n + 1) →₀ ℕ) f
        rw [MvPowerSeries.coeff_coeff_finSuccEquiv]
        simp [Finsupp.cons_zero_zero]
      have h'cc : MvPowerSeries.constantCoeff.comp h' = RingHom.id R := by
        calc
          MvPowerSeries.constantCoeff.comp h' =
              MvPowerSeries.constantCoeff.comp
                (PowerSeries.constantCoeff.comp (e.toRingHom.comp h)) := rfl
          _ = MvPowerSeries.constantCoeff.comp
                ((PowerSeries.constantCoeff.comp e.toRingHom).comp h) :=
                  congrArg (fun f => MvPowerSeries.constantCoeff.comp f)
                    (RingHom.comp_assoc h e.toRingHom PowerSeries.constantCoeff).symm
          _ = (MvPowerSeries.constantCoeff.comp
                (PowerSeries.constantCoeff.comp e.toRingHom)).comp h :=
                  (RingHom.comp_assoc h (PowerSeries.constantCoeff.comp e.toRingHom)
                    MvPowerSeries.constantCoeff).symm
          _ = MvPowerSeries.constantCoeff.comp h :=
                congrArg (fun f : MvPowerSeries (Fin (n + 1)) R →+* R => f.comp h) hecc
          _ = RingHom.id R := hcc
      have hC : (PowerSeries.constantCoeff.comp e.toRingHom).comp MvPowerSeries.C =
          MvPowerSeries.C := by ext x; simp [e, MvPowerSeries.finSuccEquiv_C]
      have h'le : Ideal.map h' p ≤ Ideal.map MvPowerSeries.C p := by
        calc
          Ideal.map h' p = Ideal.map PowerSeries.constantCoeff
              (Ideal.map e.toRingHom (Ideal.map h p)) := by
                simp [h', Ideal.map_map]
          _ ≤ Ideal.map PowerSeries.constantCoeff
              (Ideal.map e.toRingHom (Ideal.map MvPowerSeries.C p)) :=
                Ideal.map_mono (Ideal.map_mono hle)
          _ = Ideal.map MvPowerSeries.C p := by
                rw [Ideal.map_map, Ideal.map_map, hC]
      have h'ind := ih h' h'cc h'le
      let I' : Ideal (PowerSeries (MvPowerSeries (Fin n) R)) :=
        Ideal.map eR.toRingHom (Ideal.map MvPowerSeries.C p)
      let J' : Ideal (PowerSeries (MvPowerSeries (Fin n) R)) :=
        Ideal.map eR.toRingHom (Ideal.map h p)
      have hJI : J' ≤ I' := by
        intro z hz
        obtain ⟨y, hy, heq⟩ :=
          (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hz
        subst z
        exact Ideal.mem_map_of_mem e.toRingHom (hle hy)
      have hJfg : J'.FG := Ideal.FG.map (Ideal.FG.map hpfg h) e.toRingHom
      have hconstI : Ideal.map PowerSeries.constantCoeff I' =
          Ideal.map MvPowerSeries.C p := by
        dsimp [I']
        rw [Ideal.map_map, Ideal.map_map]
        exact congrArg (fun f => Ideal.map f p) hC
      have hconstJ : Ideal.map PowerSeries.constantCoeff J' =
          Ideal.map h' p := by
        dsimp [J']
        rw [Ideal.map_map, Ideal.map_map]
        exact congrArg (fun f => Ideal.map f p)
          (RingHom.comp_assoc h e.toRingHom PowerSeries.constantCoeff).symm
      have hconst : Ideal.map PowerSeries.constantCoeff I' =
          Ideal.map PowerSeries.constantCoeff J' :=
        hconstI.trans (h'ind.symm.trans hconstJ.symm)
      have hX : PowerSeries.X ∉ I' := by
        intro hX
        have hinv : Ideal.map e.symm.toRingHom I' =
            Ideal.map MvPowerSeries.C p := by
          dsimp [I']
          rw [Ideal.map_map, Ideal.map_map]
          change Ideal.map ((e.symm.toRingHom.comp e.toRingHom).comp
            MvPowerSeries.C) p = _
          rw [hecomp]
          simp
        have hx0 : MvPowerSeries.X (0 : Fin (n + 1)) ∈
            Ideal.map MvPowerSeries.C p := by
          have hback := Ideal.mem_map_of_mem e.symm.toRingHom hX
          have hX0eq : e.symm PowerSeries.X =
              MvPowerSeries.X (0 : Fin (n + 1)) := by
            apply e.injective
            rw [e.apply_symm_apply]
            exact (MvPowerSeries.finSuccEquiv_X_zero (R := R) (n := n)).symm
          have hback' : e.symm PowerSeries.X ∈ Ideal.map MvPowerSeries.C p := hinv ▸ hback
          rw [hX0eq] at hback'
          exact hback'
        have hcoeff := (MvPowerSeries.mem_map_C_iff_of_fg hpfg).mp hx0
          (Finsupp.single (0 : Fin (n + 1)) 1)
        rw [MvPowerSeries.coeff_X] at hcoeff
        exact (Ideal.IsPrime.ne_top ‹p.IsPrime›)
          ((Ideal.eq_top_iff_one p).2 (by simpa using hcoeff))
      have hpC : (Ideal.map
          (MvPowerSeries.C : R →+* MvPowerSeries (Fin (n + 1)) R) p).IsPrime := by
        let : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
        let : IsDomain (MvPowerSeries (Fin (n + 1)) (R ⧸ p)) := IsDomain.mk
        have hker : RingHom.ker
            (MvPowerSeries.map (σ := Fin (n + 1)) (Ideal.Quotient.mk p)) =
              Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin (n + 1)) R) p := by
          calc
            _ = Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin (n + 1)) R)
                (RingHom.ker (Ideal.Quotient.mk p)) :=
                  MvPowerSeries.ker_map_of_fg (Ideal.Quotient.mk p) (by simpa using hpfg)
            _ = Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin (n + 1)) R) p := by
                  simp
        rw [← hker]
        exact RingHom.ker_isPrime
          (MvPowerSeries.map (σ := Fin (n + 1)) (Ideal.Quotient.mk p))
      let : (Ideal.map
          (MvPowerSeries.C : R →+* MvPowerSeries (Fin (n + 1)) R) p).IsPrime := hpC
      let : I'.IsPrime := Ideal.map_isPrime_of_equiv e
      have hEq : I' = J' :=
        PowerSeries.eq_of_le_of_X_notMem_of_fg_of_isPrime hJI hX hJfg hconst.le
      have hback := congrArg (Ideal.map eR.symm.toRingHom) hEq
      dsimp [I', J'] at hback
      simp only [Ideal.map_of_equiv eR] at hback
      exact hback.symm

private theorem map_minimalPrime_le_map_C
    {R : Type*} [CommRing R] [IsNoetherianRing R] {p : Ideal R} [p.IsPrime]
    (hp : p ∈ minimalPrimes R) (n : ℕ)
    (h : R →+* MvPowerSeries (Fin n) R)
    (hcc : MvPowerSeries.constantCoeff.comp h = RingHom.id R) :
    Ideal.map h p ≤ Ideal.map MvPowerSeries.C p := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  let Rₚ := Localization.AtPrime p
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (R := R) (A := Rₚ) p (⊥ : Ideal R) (by simpa using hp)
  have hxloc : algebraMap R Rₚ x ∈ p.map (algebraMap R Rₚ) :=
    Ideal.mem_map_of_mem (algebraMap R Rₚ) hx
  have hxrad : algebraMap R Rₚ x ∈
      ((⊥ : Ideal R).map (algebraMap R Rₚ)).radical := by rw [hrad]; exact hxloc
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hxrad
  have hmzero : (algebraMap R Rₚ x) ^ m = 0 := by simpa using hm
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rₚ (x ^ m)).mp (by
    simpa only [map_pow] using hmzero)
  have hsnotp : (s : R) ∉ p := s.2
  let q : R →+* R ⧸ p := Ideal.Quotient.mk p
  let g : MvPowerSeries (Fin n) R →+* MvPowerSeries (Fin n) (R ⧸ p) :=
    MvPowerSeries.map (σ := Fin n) q
  let : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  have hgs : g (h s) ≠ 0 := by
    intro he
    have hc := congrArg MvPowerSeries.constantCoeff he
    simp only [g, MvPowerSeries.constantCoeff_map] at hc
    have hccs : MvPowerSeries.constantCoeff (h s) = s := by
      simpa only [RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : R →+* R => f s) hcc
    rw [hccs] at hc
    have : q s = 0 := hc
    exact hsnotp ((Ideal.Quotient.eq_zero_iff_mem).mp this)
  have hmul : g (h s) * g (h x) ^ m = 0 := by
    have hrel : s.1 * x ^ m = 0 := hs
    have hmap := congrArg (fun z : R => g (h z)) hrel
    simpa [map_mul, map_pow, g, q] using hmap
  have hpow : g (h x) ^ m = 0 := (mul_eq_zero.mp hmul).resolve_left hgs
  have hgx : g (h x) = 0 := by
    have hpos : m ≠ 0 := by
      intro hm0
      subst m
      simp at hpow
    exact (pow_eq_zero_iff hpos).mp hpow
  have hqker : RingHom.ker q = p := by simp [q]
  have hqfg : (RingHom.ker q).FG := by rw [hqker]; exact Ideal.fg_of_isNoetherianRing p
  rw [← hqker, ← MvPowerSeries.ker_map_of_fg (σ := Fin n) q hqfg]
  exact hgx

/-- Formally homotopic morphisms of Noetherian complete local algebras extend a minimal
prime of the source to the same ideal of the target. -/
@[stacks 0DQE]
theorem map_eq_of_formallyHomotopic_of_mem_minimalPrimes
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f₁ f₂ : R ⟶ S)
    (hf : FormallyHomotopic f₁ f₂) (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    p.map f₁.hom.toRingHom = p.map f₂.hom.toRingHom := by
  obtain ⟨r, h, l, hhlocal, hllocal, hconst, hf₁, hf₂⟩ := hf
  let : p.IsPrime := hp.1.1
  have hcc : MvPowerSeries.constantCoeff.comp h.toRingHom = RingHom.id R := by
    ext x; exact hconst x
  have hle := map_minimalPrime_le_map_C hp r h.toRingHom hcc
  have heq := map_eq_map_of_constCoeff_id (p := p) r h.toRingHom hcc hle
  have hf₁ring : f₁.hom.toRingHom = l.toRingHom.comp MvPowerSeries.C := by
    ext x; exact hf₁ x
  have hf₂ring : f₂.hom.toRingHom = l.toRingHom.comp h.toRingHom := by
    ext x; exact hf₂ x
  rw [hf₁ring, hf₂ring, ← Ideal.map_map, ← Ideal.map_map]
  exact congrArg (Ideal.map l.toRingHom) heq.symm

end Ideal

end

/-! ### Postcomposition preserves formal homotopy -/

section
open CategoryTheory CompleteLocalAlgCat
universe u v w

/-- Postcomposing two formally homotopic maps with the same morphism preserves their
formal homotopy. -/
@[stacks 0DQC]
theorem formallyHomotopic_comp
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S S' : CompleteLocalAlgCat.{u, v, w} Λ k}
    {f₁ f₂ : R ⟶ S} (hf : FormallyHomotopic f₁ f₂) (g : S ⟶ S') :
    FormallyHomotopic (f₁ ≫ g) (f₂ ≫ g) := by
  rcases hf with ⟨r, h, l, hh, hl, hc, h₁, h₂⟩
  let : IsLocalHom l.toRingHom := hl
  let : IsLocalHom g.hom.toRingHom := g.isLocal
  exact ⟨r, h, g.hom.comp l, hh, RingHom.isLocalHom_comp g.hom.toRingHom l.toRingHom, hc,
    (fun a => congrArg g.hom (h₁ a)), (fun a => congrArg g.hom (h₂ a))⟩

end

/-! ### Formal homotopy is an equivalence relation -/

section
open CategoryTheory Filter
open scoped Topology
universe u v w

namespace CompleteLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {R S : CompleteLocalAlgCat.{u, v, w} Λ k}

/-- A finite family of elements of the distinguished ideal of an adic ring can be substituted
for the variables of a power series ring. -/
private theorem hasEval_of_forall_mem_ideal {A σ : Type*} [CommRing A] [WithIdeal A]
    [Finite σ] (a : σ → A) (ha : ∀ i, a i ∈ WithIdeal.i) :
    MvPowerSeries.HasEval a := by
  refine ⟨fun i ↦ WithIdeal.isTopologicallyNilpotent_of_mem (ha i), ?_⟩
  simp [Filter.cofinite_eq_bot]

/-- A ring map `A → A[[σ]]` extends to the substitution endomorphism of `A[[σ]]` that is the
identity on the variables. -/
private theorem exists_substitution {A σ : Type*} [CommRing A] [Finite σ]
    (h : A →+* MvPowerSeries σ A) :
    ∃ F : MvPowerSeries σ A →+* MvPowerSeries σ A,
      (∀ i, F (MvPowerSeries.X i) = MvPowerSeries.X i) ∧
      (∀ a, F (MvPowerSeries.C a) = h a) := by
  let P := MvPowerSeries σ A
  let J : Ideal P := Ideal.span (Set.range (MvPowerSeries.X : σ → P))
  let : WithIdeal A := ⟨⊥⟩
  let : DiscreteTopology A := is_bot_adic_iff.1 rfl
  let : WithIdeal P := ⟨J⟩
  have hcomplete : IsAdicComplete J P := inferInstance
  obtain ⟨hcs, ht2⟩ := (IsAdic.isAdicComplete_iff (I := J) rfl).1 hcomplete
  let := hcs
  let := ht2
  have ha : MvPowerSeries.HasEval (MvPowerSeries.X : σ → P) :=
    hasEval_of_forall_mem_ideal _ (fun i => Ideal.subset_span ⟨i, rfl⟩)
  let F : P →+* P :=
    MvPowerSeries.eval₂Hom (φ := h) continuous_of_discreteTopology ha
  have hFc : ⇑F = MvPowerSeries.eval₂ h MvPowerSeries.X :=
    MvPowerSeries.coe_eval₂Hom _ _
  refine ⟨F, fun i => ?_, fun a => ?_⟩
  · rw [hFc]
    exact MvPowerSeries.eval₂_X h MvPowerSeries.X i
  · rw [hFc]
    exact MvPowerSeries.eval₂_C h MvPowerSeries.X a


/-- A surjective endomorphism of a Noetherian ring is injective. -/
private theorem injective_of_surjective_of_isNoetherianRing
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (f : A →+* A) (hf : Function.Surjective f) : Function.Injective f := by
  let K : ℕ →o Ideal A :=
    { toFun := fun n => RingHom.ker (f ^ n)
      monotone' := by
        apply monotone_nat_of_le_succ
        intro n x hx
        change (f ^ (n + 1)) x = 0
        simpa only [RingHom.coe_pow, Function.iterate_succ_apply', map_zero] using
          congrArg f hx }
  obtain ⟨N, hN⟩ :=
    (monotone_stabilizes_iff_noetherian).mpr (inferInstance : IsNoetherian A A) K
  have hs : ∀ n : ℕ, Function.Surjective (f ^ n) := by
    intro n
    induction n with
    | zero => exact (RingHom.id A).surjective
    | succ n ih => simpa only [RingHom.coe_pow, Function.iterate_succ'] using hf.comp ih
  intro x y hxy
  have hx0 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := hs N (x - y)
  have hzker : z ∈ RingHom.ker (f ^ (N + 1)) := by
    change (f ^ (N + 1)) z = 0
    rw [← hz] at hx0
    simpa only [RingHom.coe_pow, Function.iterate_succ_apply'] using hx0
  have hNk : RingHom.ker (f ^ N) = RingHom.ker (f ^ (N + 1)) := by
    simpa [K] using hN (N + 1) (Nat.le_succ N)
  have hzero : x - y = 0 := by
    rw [← hz]
    exact RingHom.mem_ker.mp (hNk ▸ hzker)
  exact sub_eq_zero.mp hzero

/-- A ring map out of `A[[X₁, …, Xₙ]]` sending every variable into an ideal `K` sends the ideal
generated by the variables into `K`. -/
private theorem map_span_X_le {A B : Type*} [CommRing A] [CommRing B] {n : ℕ}
    (F : MvPowerSeries (Fin n) A →+* B) (K : Ideal B)
    (hX : ∀ i, F (MvPowerSeries.X i) ∈ K) :
    Ideal.map F (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) A))) ≤
      K := by
  rw [Ideal.map_span]
  exact Ideal.span_le.2 (by rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩; exact hX i)

/-- A ring map out of `A[[X₁, …, Xₙ]]` sending every variable into an ideal `K` agrees, modulo
`K`, with its value on the constant coefficient. -/
private theorem map_sub_C_constantCoeff_mem {A B : Type*} [CommRing A] [CommRing B] {n : ℕ}
    (F : MvPowerSeries (Fin n) A →+* B) (K : Ideal B)
    (hX : ∀ i, F (MvPowerSeries.X i) ∈ K) (x : MvPowerSeries (Fin n) A) :
    F x - F (MvPowerSeries.C (MvPowerSeries.constantCoeff x)) ∈ K := by
  have hx : x - MvPowerSeries.C (MvPowerSeries.constantCoeff x) ∈
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) A)) :=
    (Stacks.MvPowerSeries.RegularParameters.mem_span_X_iff_constantCoeff_eq_zero n _).2 (by simp)
  rw [← map_sub]
  exact map_span_X_le F K hX (Ideal.mem_map_of_mem F hx)

/-- The substitution endomorphism attached to a section of the constant-coefficient map is
bijective. -/
private theorem bijective_of_substitution {A : Type*} [CommRing A] [IsNoetherianRing A]
    (n : ℕ) (h : A →+* MvPowerSeries (Fin n) A)
    (hc : ∀ a, MvPowerSeries.constantCoeff (h a) = a)
    (F : MvPowerSeries (Fin n) A →+* MvPowerSeries (Fin n) A)
    (hX : ∀ i, F (MvPowerSeries.X i) = MvPowerSeries.X i)
    (hC : ∀ a, F (MvPowerSeries.C a) = h a) : Function.Bijective F := by
  let P := MvPowerSeries (Fin n) A
  let J : Ideal P := Ideal.span (Set.range (MvPowerSeries.X : Fin n → P))
  have hXJ (i : Fin n) : MvPowerSeries.X i ∈ J := Ideal.subset_span ⟨i, rfl⟩
  have hmap : Ideal.map F J = J :=
    le_antisymm (map_span_X_le F J fun i => by rw [hX]; exact hXJ i)
      (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hX i ▸ Ideal.mem_map_of_mem F (hXJ i)))
  have hquot : Function.Surjective ((Ideal.Quotient.mk (Ideal.map F J)).comp F) := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    let a := MvPowerSeries.constantCoeff x
    have hx : x - MvPowerSeries.C a ∈ J := by
      apply (Stacks.MvPowerSeries.RegularParameters.mem_span_X_iff_constantCoeff_eq_zero n _).2
      simp [a]
    have hh : h a - MvPowerSeries.C a ∈ J := by
      apply (Stacks.MvPowerSeries.RegularParameters.mem_span_X_iff_constantCoeff_eq_zero n _).2
      simp [hc]
    refine ⟨MvPowerSeries.C a, ?_⟩
    rw [RingHom.comp_apply, hC a, hmap, Ideal.Quotient.eq]
    have hsub : h a - x ∈ J := by
      have heq : h a - x = (h a - MvPowerSeries.C a) - (x - MvPowerSeries.C a) := by ring
      rw [heq]
      exact J.sub_mem hh hx
    simpa using hsub
  have hsurj : Function.Surjective F := by
    let : IsAdicComplete J P := inferInstance
    let : IsHausdorff (Ideal.map F J) P := by rw [hmap]; infer_instance
    exact _root_.surjective_of_mk_map_comp_surjective (I := J) F hquot
  exact ⟨injective_of_surjective_of_isNoetherianRing F hsurj, hsurj⟩

/-- A substitution that is a section of the constant coefficient on constants and sends the
variables into the kernel of the constant coefficient preserves constant coefficients. -/
private theorem constantCoeff_eval₂ {A τ : Type*} [CommRing A] (n : ℕ)
    (F : MvPowerSeries (Fin n) A →+* MvPowerSeries τ A)
    (φ : A →+* MvPowerSeries τ A) (a : Fin n → MvPowerSeries τ A)
    (hC : ∀ r, F (MvPowerSeries.C r) = φ r)
    (hX : ∀ i, F (MvPowerSeries.X i) = a i)
    (hφ : ∀ r, MvPowerSeries.constantCoeff (φ r) = r)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (x : MvPowerSeries (Fin n) A) :
    MvPowerSeries.constantCoeff (F x) = MvPowerSeries.constantCoeff x := by
  have h := map_sub_C_constantCoeff_mem F (RingHom.ker MvPowerSeries.constantCoeff)
    (fun i => by rw [hX i]; exact RingHom.mem_ker.mpr (ha0 i)) x
  rw [RingHom.mem_ker, map_sub, hC, hφ] at h
  exact sub_eq_zero.1 h

/-- A substitution into a local ring sending the variables into the maximal ideal is local as
soon as the map on constants is. -/
private theorem isLocalHom_of_eval₂ {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing B] (n : ℕ) (φ : A →+* B) [IsLocalHom φ]
    (a : Fin n → B)
    (F : MvPowerSeries (Fin n) A →+* B)
    (hC : ∀ x, F (MvPowerSeries.C x) = φ x)
    (hX : ∀ i, F (MvPowerSeries.X i) = a i)
    (ha_max : ∀ i, a i ∈ IsLocalRing.maximalIdeal B) :
    IsLocalHom F := by
  refine ⟨fun x hFxUnit => ?_⟩
  by_contra hxUnit
  have hc : MvPowerSeries.constantCoeff x ∈ nonunits A := fun hcUnit =>
    hxUnit ((MvPowerSeries.isUnit_iff_constantCoeff).2 hcUnit)
  have hφc : φ (MvPowerSeries.constantCoeff x) ∈ IsLocalRing.maximalIdeal B := fun hφunit =>
    hc ((isUnit_map_iff φ _).mp hφunit)
  have hFJ := map_sub_C_constantCoeff_mem F (IsLocalRing.maximalIdeal B)
    (fun i => by rw [hX i]; exact ha_max i) x
  rw [hC] at hFJ
  have hFx : F x ∈ IsLocalRing.maximalIdeal B := by
    simpa only [sub_add_cancel] using (IsLocalRing.maximalIdeal B).add_mem hFJ hφc
  exact (IsLocalRing.mem_maximalIdeal _ |>.1 hFx) hFxUnit

/-- A local ring map out of a power series ring over a nontrivial ring sends each variable
into the maximal ideal. -/
private theorem map_X_mem_maximalIdeal {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B]
    [IsLocalRing B] {σ : Type*} {l : MvPowerSeries σ A →+* B} (hl : IsLocalHom l) (i : σ) :
    l (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal B := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hi
  simpa using MvPowerSeries.isUnit_iff_constantCoeff.1 (hl.map_nonunit _ hi)

/-- A power series over `A` lies in `I · A[[X]] + (X ^ n)` exactly when its first `n`
coefficients lie in `I`. -/
private theorem mem_map_C_sup_span_X_pow_iff {A : Type*} [CommRing A]
    (I : Ideal A) :
    ∀ (n : ℕ) (f : PowerSeries A),
      f ∈ I.map (PowerSeries.C : A →+* PowerSeries A) ⊔
          Ideal.span {(PowerSeries.X : PowerSeries A) ^ n} ↔
        ∀ j < n, PowerSeries.coeff j f ∈ I := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ n ih =>
    intro f
    constructor
    · intro hf j hj
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
      have hb' : PowerSeries.coeff j b = 0 :=
        (PowerSeries.X_pow_dvd_iff.1 (Ideal.mem_span_singleton.1 hb)) j hj
      have hcoeffa : PowerSeries.coeff j a ∈ I := by
        simpa [PowerSeries.coeff] using
          MvPowerSeries.coeff_mem_of_mem_map_C ha (Finsupp.single () j)
      have hcoeffab : PowerSeries.coeff j (a + b) = PowerSeries.coeff j a := by
        rw [map_add, hb', add_zero]
      rw [hcoeffab]
      exact hcoeffa
    · intro hf
      obtain ⟨q, hq⟩ : (PowerSeries.X : PowerSeries A) ∣
          f - PowerSeries.C (PowerSeries.coeff 0 f) := by
        rw [PowerSeries.X_dvd_iff]
        simp
      have hsplit : f = PowerSeries.C (PowerSeries.coeff 0 f) + PowerSeries.X * q := by
        rw [← hq]
        ring
      have hqcoeff : ∀ j < n, PowerSeries.coeff j q ∈ I := by
        intro j hj
        have hcoeff : PowerSeries.coeff (j + 1) f = PowerSeries.coeff j q := by
          rw [hsplit]
          simp [PowerSeries.coeff_succ_X_mul]
        rw [← hcoeff]
        exact hf (j + 1) (by omega)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((ih q).2 hqcoeff)
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hb
      rw [hsplit, ← hab, mul_add, ← add_assoc]
      refine Submodule.add_mem_sup ?_ (Ideal.mem_span_singleton.2 ⟨c, ?_⟩)
      · exact Ideal.add_mem _
          (Ideal.mem_map_of_mem (PowerSeries.C : A →+* PowerSeries A) (hf 0 n.succ_pos))
          (Ideal.mul_mem_left _ _ ha)
      · rw [hc, pow_succ]
        ring

/-- The maximal ideal of a power series ring over a local ring is generated by the maximal
ideal of the coefficients together with the variable. -/
private theorem maximalIdeal_powerSeries (A : Type*) [CommRing A] [IsLocalRing A] :
    IsLocalRing.maximalIdeal (PowerSeries A) =
      (IsLocalRing.maximalIdeal A).map (PowerSeries.C : A →+* PowerSeries A) ⊔
        Ideal.span {(PowerSeries.X : PowerSeries A)} := by
  ext f
  rw [Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_mem]
  change PowerSeries.constantCoeff f ∈ IsLocalRing.maximalIdeal A ↔ _
  simpa only [pow_one, Nat.lt_one_iff, forall_eq, PowerSeries.coeff_zero_eq_constantCoeff] using
    (mem_map_C_sup_span_X_pow_iff (IsLocalRing.maximalIdeal A) 1 f).symm

/-- The `n`-th power of the maximal ideal of a power series ring contains the ideal generated
by the `n`-th power of the coefficient maximal ideal and by `X ^ n`. -/
private theorem map_C_sup_span_X_pow_le_maximalIdeal_pow
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    (IsLocalRing.maximalIdeal A ^ n).map (PowerSeries.C : A →+* PowerSeries A) ⊔
        Ideal.span {(PowerSeries.X : PowerSeries A) ^ n} ≤
      IsLocalRing.maximalIdeal (PowerSeries A) ^ n := by
  rw [maximalIdeal_powerSeries A, Ideal.map_pow, ← Ideal.span_singleton_pow]
  exact sup_le (Ideal.pow_right_mono le_sup_left n) (Ideal.pow_right_mono le_sup_right n)

/-- Membership of a power series in a power of the maximal ideal is implied by a condition on
finitely many of its coefficients. -/
private theorem exists_finset_coeff_mem_maximalIdeal_pow
    {A : Type*} [CommRing A] [IsLocalRing A] (n : ℕ) :
    ∀ N : ℕ, ∃ E : Finset (Fin n →₀ ℕ),
      ∀ f : MvPowerSeries (Fin n) A,
        (∀ e ∈ E, MvPowerSeries.coeff e f ∈ IsLocalRing.maximalIdeal A ^ N) →
          f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A) ^ N := by
  induction n with
  | zero =>
    intro N
    refine ⟨{0}, ?_⟩
    intro f hf
    let e : MvPowerSeries (Fin 0) A ≃+* A :=
      (MvPowerSeries.isEmptyEquiv (Fin 0) A).toRingEquiv
    have hemax : Ideal.map e (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 0) A)) =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
    have hepow : Ideal.map e (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 0) A) ^ N) =
        IsLocalRing.maximalIdeal A ^ N := by rw [Ideal.map_pow, hemax]
    have heval : e f = MvPowerSeries.coeff (0 : Fin 0 →₀ ℕ) f := by
      simp [e, MvPowerSeries.coeff_zero_eq_constantCoeff]
    have hfmap : e f ∈ Ideal.map e
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 0) A) ^ N) := by
      rw [hepow]
      simpa [heval] using hf 0 (by simp)
    obtain ⟨g, hg, hgf⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).1 hfmap
    have hgeq : g = f := e.injective hgf
    simpa [hgeq] using hg
  | succ n ih =>
    intro N
    obtain ⟨E, hE⟩ := ih N
    classical
    let e : MvPowerSeries (Fin (n + 1)) A ≃+* PowerSeries (MvPowerSeries (Fin n) A) :=
      (MvPowerSeries.finSuccEquiv A n).toRingEquiv
    let E' : Finset (Fin (n + 1) →₀ ℕ) :=
      ((Finset.range N).product E).image (fun x => Finsupp.cons x.1 x.2)
    refine ⟨E', ?_⟩
    intro f hf
    let m₀ := IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A)
    let m₁ := IsLocalRing.maximalIdeal (PowerSeries (MvPowerSeries (Fin n) A))
    have hcoeff (j : ℕ) (hj : j < N) : PowerSeries.coeff j (e f) ∈ m₀ ^ N := by
      refine hE (PowerSeries.coeff j (e f)) fun d hd => ?_
      have hmem : Finsupp.cons j d ∈ E' :=
        Finset.mem_image.mpr
          ⟨(j, d), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, hd⟩, rfl⟩
      have hc := MvPowerSeries.coeff_coeff_finSuccEquiv (R := A) (n := n) f (k := j) (x := d)
      simpa [e] using hc ▸ hf (Finsupp.cons j d) hmem
    have hsum : e f ∈ (m₀ ^ N).map (PowerSeries.C : _ →+* _) ⊔
        Ideal.span {(PowerSeries.X : PowerSeries (MvPowerSeries (Fin n) A)) ^ N} :=
      (mem_map_C_sup_span_X_pow_iff (m₀ ^ N) N (e f)).2 hcoeff
    have hmap : Ideal.map e (IsLocalRing.maximalIdeal (MvPowerSeries (Fin (n + 1)) A)) = m₁ :=
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
    have hmem : e f ∈ Ideal.map e
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin (n + 1)) A) ^ N) := by
      rw [Ideal.map_pow, hmap]
      exact map_C_sup_span_X_pow_le_maximalIdeal_pow (MvPowerSeries (Fin n) A) N hsum
    obtain ⟨g, hg, hgf⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).1 hmem
    have hgeq : g = f := e.injective hgf
    simpa [hgeq] using hg

/-- Over a discrete local ring the powers of the maximal ideal of a power series ring are open
for the product topology. -/
private theorem isOpen_maximalIdeal_pow_piTopology
    {A : Type*} [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] (n N : ℕ) :
    @IsOpen (MvPowerSeries (Fin n) A)
      (MvPowerSeries.WithPiTopology.instTopologicalSpace A)
      (((IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A) ^ N :
        Ideal (MvPowerSeries (Fin n) A)) : Set (MvPowerSeries (Fin n) A))) := by
  let : TopologicalSpace (MvPowerSeries (Fin n) A) :=
    MvPowerSeries.WithPiTopology.instTopologicalSpace A
  let : IsTopologicalRing (MvPowerSeries (Fin n) A) :=
    MvPowerSeries.WithPiTopology.instIsTopologicalRing (Fin n) A
  obtain ⟨E, hE⟩ := exists_finset_coeff_mem_maximalIdeal_pow (A := A) n N
  let U : Set (MvPowerSeries (Fin n) A) :=
    ⋂ e ∈ E, (MvPowerSeries.coeff e) ⁻¹' ((IsLocalRing.maximalIdeal A ^ N : Ideal A) : Set A)
  have hU : IsOpen U := by
    change IsOpen (⋂ e ∈ E,
      (MvPowerSeries.coeff e) ⁻¹' ((IsLocalRing.maximalIdeal A ^ N : Ideal A) : Set A))
    refine isOpen_biInter_finset fun e _ => ?_
    exact (isOpen_discrete _).preimage (MvPowerSeries.WithPiTopology.continuous_coeff A e)
  have hU0 : U ∈ 𝓝 (0 : MvPowerSeries (Fin n) A) := hU.mem_nhds (by simp [U])
  have hUsub : U ⊆
      ((IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A) ^ N : Ideal _) : Set _) := by
    intro f hf
    simp only [U, Set.mem_iInter] at hf
    exact hE f fun e he => hf e he
  refine isOpen_iff_mem_nhds.2 fun f hf => ?_
  have htrans : (fun x : MvPowerSeries (Fin n) A => f + x) '' U ∈ 𝓝 f := by
    rw [← map_add_left_nhds_zero f]
    exact Filter.mem_map.mpr (Filter.mem_of_superset hU0 fun x hx => ⟨x, hx, rfl⟩)
  refine Filter.mem_of_superset htrans ?_
  rintro g ⟨x, hx, rfl⟩
  exact Ideal.add_mem _ hf (hUsub hx)

/-- Over a discrete local ring the product topology on a power series ring is finer than the
adic topology of its maximal ideal. -/
private theorem continuous_id_piTopology_toAdic
    {A : Type*} [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] (n : ℕ) :
    @Continuous (MvPowerSeries (Fin n) A) (MvPowerSeries (Fin n) A)
      (MvPowerSeries.WithPiTopology.instTopologicalSpace A)
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A)).adicTopology id := by
  let : TopologicalSpace (MvPowerSeries (Fin n) A) :=
    MvPowerSeries.WithPiTopology.instTopologicalSpace A
  let : IsTopologicalRing (MvPowerSeries (Fin n) A) :=
    MvPowerSeries.WithPiTopology.instIsTopologicalRing (Fin n) A
  have hopen (N : ℕ) : IsOpen
      ((IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A) ^ N :
        Ideal (MvPowerSeries (Fin n) A)) : Set (MvPowerSeries (Fin n) A)) :=
    isOpen_maximalIdeal_pow_piTopology (A := A) n N
  apply continuous_iff_le_induced.2
  rw [@induced_id _ (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A)).adicTopology]
  refine TopologicalSpace.le_def.2 fun s hs => isOpen_iff_mem_nhds.2 fun f hf => ?_
  have hmemAdic : s ∈ @nhds _
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A)).adicTopology f := by
    let : TopologicalSpace (MvPowerSeries (Fin n) A) :=
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A)).adicTopology
    exact hs.mem_nhds hf
  obtain ⟨N, -, hN⟩ :=
    (Ideal.hasBasis_nhds_adic
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A)) f).mem_iff.mp hmemAdic
  let V : Set (MvPowerSeries (Fin n) A) :=
    (fun y => y - f) ⁻¹' ((IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) A) ^ N :
      Ideal (MvPowerSeries (Fin n) A)) : Set (MvPowerSeries (Fin n) A))
  have hVmem : V ∈ 𝓝 f :=
    ((hopen N).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  exact Filter.mem_of_superset hVmem fun y hy => hN ⟨y - f, by simpa [V] using hy, by abel_nf⟩

/-- **Stacks Project, Tag 0DQB.** Every morphism of complete local `Λ`-algebras is formally
homotopic to itself: take the homotopy in no variables. -/
@[stacks 0DQB "reflexivity"]
theorem formallyHomotopic_refl (f : R ⟶ S) : FormallyHomotopic f f := by
  let P := MvPowerSeries (Fin 0) R
  let : IsScalarTower Λ R P := inferInstance
  let h₀ : R →+* P := MvPowerSeries.C
  let h : R →ₐ[Λ] P :=
    { toRingHom := h₀
      commutes' := fun a => MvPowerSeries.algebraMap_apply.symm }
  let l₀ : P →+* S := f.hom.toRingHom.comp MvPowerSeries.constantCoeff
  let l : P →ₐ[Λ] S :=
    { toRingHom := l₀
      commutes' := fun a => by
        rw [MvPowerSeries.algebraMap_apply]
        change f.hom (MvPowerSeries.constantCoeff
          (MvPowerSeries.C (algebraMap Λ R a))) = algebraMap Λ S a
        rw [MvPowerSeries.constantCoeff_C]
        exact f.hom.commutes a }
  have hh : IsLocalHom h₀ := by
    refine isLocalHom_of_leftInverse MvPowerSeries.constantCoeff fun x => ?_
    change MvPowerSeries.constantCoeff (MvPowerSeries.C x : MvPowerSeries (Fin 0) R) = x
    rfl
  have hl₀ : IsLocalHom (MvPowerSeries.constantCoeff : P →+* R) :=
    ⟨fun x hx => (MvPowerSeries.isUnit_iff_constantCoeff).2 hx⟩
  have hl : IsLocalHom l₀ :=
    ⟨fun x hx => hl₀.map_nonunit _ (f.isLocal.map_nonunit _ hx)⟩
  refine ⟨0, h, l, hh, hl, fun a => ?_, fun a => ?_, fun a => ?_⟩
  · change MvPowerSeries.constantCoeff (MvPowerSeries.C a : MvPowerSeries (Fin 0) R) = a
    exact MvPowerSeries.constantCoeff_C (σ := Fin 0) a
  · change f.hom a = f.hom (MvPowerSeries.constantCoeff
      (MvPowerSeries.C a : MvPowerSeries (Fin 0) R))
    rw [MvPowerSeries.constantCoeff_C]
  · change f.hom a = f.hom (MvPowerSeries.constantCoeff
      (MvPowerSeries.C a : MvPowerSeries (Fin 0) R))
    rw [MvPowerSeries.constantCoeff_C]

/-- **Stacks Project, Tag 0DQB.** Formal homotopy is symmetric: substituting the homotopy into
itself gives an automorphism of the power series ring exchanging the two specializations. -/
@[stacks 0DQB "symmetry"]
theorem formallyHomotopic_symm {f g : R ⟶ S}
    (h : FormallyHomotopic f g) : FormallyHomotopic g f := by
  rcases h with ⟨n, h₀, l, hloc, lloc, hcc, hf, hg⟩
  let P := MvPowerSeries (Fin n) R
  let : IsScalarTower Λ R P := inferInstance
  obtain ⟨F, hX, hC⟩ := exists_substitution h₀.toRingHom
  let e : P ≃+* P := RingEquiv.ofBijective F (bijective_of_substitution n h₀.toRingHom hcc F hX hC)
  have hefix : ∀ a : Λ, e (algebraMap Λ P a) = algebraMap Λ P a := by
    intro a
    calc
      e (algebraMap Λ P a) = h₀ (algebraMap Λ R a) := by
        change F (algebraMap Λ P a) = _
        rw [MvPowerSeries.algebraMap_apply]
        exact hC (algebraMap Λ R a)
      _ = algebraMap Λ P a := h₀.commutes a
  let h' : R →ₐ[Λ] P :=
    { toRingHom := e.symm.toRingHom.comp MvPowerSeries.C
      commutes' := fun a => by
        have hCa : MvPowerSeries.C (algebraMap Λ R a) = algebraMap Λ P a :=
          MvPowerSeries.algebraMap_apply.symm
        calc
          (e.symm.toRingHom.comp MvPowerSeries.C) (algebraMap Λ R a) =
              e.symm (MvPowerSeries.C (algebraMap Λ R a)) := rfl
          _ = e.symm (algebraMap Λ P a) := congrArg e.symm hCa
          _ = algebraMap Λ P a := by simpa using (congrArg e.symm (hefix a)).symm }
  let l' : P →ₐ[Λ] S :=
    { toRingHom := l.toRingHom.comp e.toRingHom
      commutes' := fun a => by
        change l (e (algebraMap Λ P a)) = algebraMap Λ S a
        rw [hefix]
        exact l.commutes a }
  have hccF : ∀ x : P, MvPowerSeries.constantCoeff (F x) = MvPowerSeries.constantCoeff x :=
    constantCoeff_eval₂ n F h₀.toRingHom MvPowerSeries.X hC hX hcc
      (fun i => MvPowerSeries.constantCoeff_X i)
  have hcc' : ∀ a, MvPowerSeries.constantCoeff (h' a) = a := by
    intro a
    calc
      MvPowerSeries.constantCoeff (h' a) =
          MvPowerSeries.constantCoeff (F (h' a)) := (hccF (h' a)).symm
      _ = MvPowerSeries.constantCoeff (MvPowerSeries.C a) := by
        refine congrArg _ ?_
        change e (e.symm (MvPowerSeries.C a)) = MvPowerSeries.C a
        exact e.apply_symm_apply _
      _ = a := MvPowerSeries.constantCoeff_C a
  have he_local : IsLocalHom e.toRingHom :=
    isLocalHom_of_leftInverse e.symm.toRingHom e.symm_apply_apply
  have hloc' : IsLocalHom h'.toRingHom :=
    isLocalHom_of_leftInverse MvPowerSeries.constantCoeff hcc'
  have lloc' : IsLocalHom l'.toRingHom :=
    ⟨fun x hx => he_local.map_nonunit x (lloc.map_nonunit (e x) hx)⟩
  refine ⟨n, h', l', hloc', lloc', hcc', fun a => ?_, fun a => ?_⟩
  · change g.hom a = l (e (MvPowerSeries.C a))
    rw [show e (MvPowerSeries.C a) = h₀ a from hC a]
    exact hg a
  · change f.hom a = l (e (h' a))
    rw [show e (h' a) = MvPowerSeries.C a by simp [h', e]]
    exact hf a

/-- **Stacks Project, Tag 0DQB.** Formal homotopy is transitive: concatenating the variables
of two homotopies and substituting the first into the second gives a homotopy between the
outer two morphisms. -/
@[stacks 0DQB "transitivity"]
theorem formallyHomotopic_trans {f g h : R ⟶ S}
    (hfg : FormallyHomotopic f g) (hgh : FormallyHomotopic g h) :
    FormallyHomotopic f h := by
  rcases hfg with ⟨n, h₁, l₁, h₁local, l₁local, h₁cc, hf, hg⟩
  rcases hgh with ⟨m, h₂, l₂, h₂local, l₂local, h₂cc, hg', hh⟩
  let P := MvPowerSeries (Fin n) R
  let Q := MvPowerSeries (Fin m) R
  let B := MvPowerSeries (Fin (n + m)) R
  let JB : Ideal B := Ideal.span (Set.range (MvPowerSeries.X : Fin (n + m) → B))
  let : IsScalarTower Λ R P := inferInstance
  let : IsScalarTower Λ R Q := inferInstance
  let : IsScalarTower Λ R B := inferInstance
  let : WithIdeal R := ⟨⊥⟩
  let : DiscreteTopology R := is_bot_adic_iff.1 rfl
  let : WithIdeal B := ⟨JB⟩
  have hBcomplete : IsAdicComplete JB B := inferInstance
  obtain ⟨hBcs, hBt2⟩ := (IsAdic.isAdicComplete_iff (I := JB) rfl).1 hBcomplete
  let : CompleteSpace B := hBcs
  let : T2Space B := hBt2
  let xvars : Fin n → B := fun i => MvPowerSeries.X (Fin.castAdd m i)
  have hxvars : MvPowerSeries.HasEval xvars :=
    hasEval_of_forall_mem_ideal _ fun i => Ideal.subset_span ⟨Fin.castAdd m i, rfl⟩
  let iota : P →+* B :=
    MvPowerSeries.eval₂Hom (φ := MvPowerSeries.C) continuous_of_discreteTopology hxvars
  have hiota_eval : ⇑iota = MvPowerSeries.eval₂ MvPowerSeries.C xvars :=
    MvPowerSeries.coe_eval₂Hom _ _
  have hiotaC (a : R) : iota (MvPowerSeries.C a) = MvPowerSeries.C a := by
    rw [hiota_eval, MvPowerSeries.eval₂_C]
  have hiotaX (i : Fin n) : iota (MvPowerSeries.X i) = xvars i := by
    rw [hiota_eval, MvPowerSeries.eval₂_X]
  have hiotaCC (x : P) :
      MvPowerSeries.constantCoeff (iota x) = MvPowerSeries.constantCoeff x :=
    constantCoeff_eval₂ n iota MvPowerSeries.C xvars hiotaC hiotaX
      (fun a => MvPowerSeries.constantCoeff_C a) (fun i => MvPowerSeries.constantCoeff_X _) x
  let β : R →+* B := iota.comp h₁.toRingHom
  have hβCC (a : R) : MvPowerSeries.constantCoeff (β a) = a := by
    change MvPowerSeries.constantCoeff (iota (h₁ a)) = a
    rw [hiotaCC, h₁cc]
  let yvars : Fin m → B := fun j => MvPowerSeries.X (Fin.natAdd n j)
  have hyvars : MvPowerSeries.HasEval yvars :=
    hasEval_of_forall_mem_ideal _ fun j => Ideal.subset_span ⟨Fin.natAdd n j, rfl⟩
  let G : Q →+* B :=
    MvPowerSeries.eval₂Hom (φ := β) continuous_of_discreteTopology hyvars
  have hG_eval : ⇑G = MvPowerSeries.eval₂ β yvars := MvPowerSeries.coe_eval₂Hom _ _
  have hGC (a : R) : G (MvPowerSeries.C a) = β a := by
    rw [hG_eval, MvPowerSeries.eval₂_C]
  have hGX (j : Fin m) : G (MvPowerSeries.X j) = yvars j := by
    rw [hG_eval, MvPowerSeries.eval₂_X]
  have hGCC (x : Q) : MvPowerSeries.constantCoeff (G x) = MvPowerSeries.constantCoeff x :=
    constantCoeff_eval₂ m G β yvars hGC hGX hβCC
      (fun j => MvPowerSeries.constantCoeff_X _) x
  let h₃₀ : R →+* B := G.comp h₂.toRingHom
  have h₃cc (a : R) : MvPowerSeries.constantCoeff (h₃₀ a) = a := by
    change MvPowerSeries.constantCoeff (G (h₂ a)) = a
    rw [hGCC, h₂cc]
  have hiota_scalar (a : Λ) : iota (algebraMap Λ P a) = algebraMap Λ B a := by
    rw [MvPowerSeries.algebraMap_apply, hiotaC, MvPowerSeries.algebraMap_apply]
  have hβ_scalar (a : Λ) : β (algebraMap Λ R a) = algebraMap Λ B a := by
    change iota (h₁ (algebraMap Λ R a)) = _
    rw [h₁.commutes, hiota_scalar]
  let h₃ : R →ₐ[Λ] B :=
    { toRingHom := h₃₀
      commutes' := fun a => by
        change G (h₂ (algebraMap Λ R a)) = algebraMap Λ B a
        rw [h₂.commutes]
        rw [MvPowerSeries.algebraMap_apply, hGC, hβ_scalar] }
  have h₃local : IsLocalHom h₃.toRingHom :=
    isLocalHom_of_leftInverse MvPowerSeries.constantCoeff h₃cc
  let : WithIdeal S := ⟨IsLocalRing.maximalIdeal S⟩
  have hScomplete : IsAdicComplete (IsLocalRing.maximalIdeal S) S := inferInstance
  obtain ⟨hScs, hSt2⟩ :=
    (IsAdic.isAdicComplete_iff (I := IsLocalRing.maximalIdeal S) rfl).1 hScomplete
  let : CompleteSpace S := hScs
  let : T2Space S := hSt2
  let z : Fin (n + m) → S :=
    Fin.addCases (fun i => l₁ (MvPowerSeries.X i)) (fun j => l₂ (MvPowerSeries.X j))
  have hzmax : ∀ i, z i ∈ IsLocalRing.maximalIdeal S := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa [z] using map_X_mem_maximalIdeal l₁local i
    | right j => simpa [z] using map_X_mem_maximalIdeal l₂local j
  have hz : MvPowerSeries.HasEval z := hasEval_of_forall_mem_ideal z hzmax
  let L : B →+* S :=
    MvPowerSeries.eval₂Hom (φ := f.hom.toRingHom) continuous_of_discreteTopology hz
  have hL_eval : ⇑L = MvPowerSeries.eval₂ f.hom.toRingHom z := MvPowerSeries.coe_eval₂Hom _ _
  have hLC (a : R) : L (MvPowerSeries.C a) = f.hom.toRingHom a := by
    rw [hL_eval, MvPowerSeries.eval₂_C]
  have hLX (i : Fin (n + m)) : L (MvPowerSeries.X i) = z i := by
    rw [hL_eval, MvPowerSeries.eval₂_X]
  have hLlocal : IsLocalHom L := by
    let : IsLocalHom f.hom.toRingHom := f.isLocal
    exact isLocalHom_of_eval₂ (n + m) f.hom.toRingHom z L hLC hLX hzmax
  let l₃ : B →ₐ[Λ] S :=
    { toRingHom := L
      commutes' := fun a => by
        rw [MvPowerSeries.algebraMap_apply]
        exact (hLC _).trans (f.hom.commutes a) }
  have hLmap : Ideal.map L JB ≤ IsLocalRing.maximalIdeal S :=
    map_span_X_le L _ fun i => by rw [hLX]; exact hzmax i
  have hLcont : Continuous L :=
    (WithIdeal.uniformContinuous_of_map_le (f := L) hLmap).continuous
  have hL_l1_X (i : Fin n) : L (xvars i) = l₁ (MvPowerSeries.X i) := by
    change L (MvPowerSeries.X (Fin.castAdd m i)) = _
    rw [hLX]
    simp [z, Fin.addCases_left]
  have hL_l2_X (j : Fin m) : L (yvars j) = l₂ (MvPowerSeries.X j) := by
    change L (MvPowerSeries.X (Fin.natAdd n j)) = _
    rw [hLX]
    simp [z, Fin.addCases_right]
  have hL_iota_formula : ∀ x : P,
      L (iota x) =
        MvPowerSeries.eval₂ f.hom.toRingHom (fun i => l₁ (MvPowerSeries.X i)) x := by
    intro x
    rw [hiota_eval]
    change (L ∘ MvPowerSeries.eval₂ MvPowerSeries.C xvars) x = _
    rw [MvPowerSeries.comp_eval₂ continuous_of_discreteTopology hxvars hLcont]
    congr 1
    · ext a
      simp [hLC, hf]
    · funext i
      exact hL_l1_X i
  have hl₁vars : MvPowerSeries.HasEval (fun i : Fin n => l₁ (MvPowerSeries.X i)) :=
    hasEval_of_forall_mem_ideal _ (map_X_mem_maximalIdeal l₁local)
  have eval_unique (r : ℕ) (φ : R →+* S)
      (a : MvPowerSeries (Fin r) R →+* S)
      (ha : MvPowerSeries.HasEval (fun i => a (MvPowerSeries.X i)))
      (hc : ∀ x, a (MvPowerSeries.C x) = φ x)
      (hcont : @Continuous (MvPowerSeries (Fin r) R) S
        (MvPowerSeries.WithPiTopology.instTopologicalSpace R)
        (IsLocalRing.maximalIdeal S).adicTopology a) :
      a = MvPowerSeries.eval₂ φ (fun i => a (MvPowerSeries.X i)) := by
    refine MvPowerSeries.eval₂_unique continuous_of_discreteTopology ha hcont fun p => ?_
    induction p using MvPolynomial.induction_on with
    | C x => simpa only [MvPolynomial.coe_C, MvPolynomial.eval₂_C] using hc x
    | add p q hp hq => rw [MvPolynomial.coe_add, map_add, MvPolynomial.eval₂_add, hp, hq]
    | mul_X p i hp =>
        rw [MvPolynomial.coe_mul, map_mul, MvPolynomial.eval₂_mul, hp, MvPolynomial.coe_X,
          MvPolynomial.eval₂_X]
  have eval_unique_local (r : ℕ) (φ : R →+* S)
      (a : MvPowerSeries (Fin r) R →+* S) (hloc : IsLocalHom a)
      (ha : MvPowerSeries.HasEval (fun i => a (MvPowerSeries.X i)))
      (hc : ∀ x, a (MvPowerSeries.C x) = φ x) :
      a = MvPowerSeries.eval₂ φ (fun i => a (MvPowerSeries.X i)) := by
    let : WithIdeal (MvPowerSeries (Fin r) R) :=
      ⟨IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) R)⟩
    let : IsLocalHom a := hloc
    have hcont : Continuous a :=
      (WithIdeal.uniformContinuous_of_map_le (f := a)
        (IsLocalRing.map_maximalIdeal_le a)).continuous
    exact eval_unique r φ a ha hc <| @Continuous.comp _ _ _
      (MvPowerSeries.WithPiTopology.instTopologicalSpace R)
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) R)).adicTopology
      (IsLocalRing.maximalIdeal S).adicTopology id a hcont
      (continuous_id_piTopology_toAdic (A := R) r)
  have hl₁_eval : (l₁.toRingHom : P →+* S) =
      MvPowerSeries.eval₂ f.hom.toRingHom (fun i => l₁ (MvPowerSeries.X i)) :=
    eval_unique_local n f.hom.toRingHom l₁.toRingHom l₁local hl₁vars (fun x => (hf x).symm)
  have hLiota : L.comp iota = l₁.toRingHom := by
    ext x
    rw [RingHom.comp_apply, hL_iota_formula, hl₁_eval]
  have hL_beta : L.comp β = l₂.toRingHom.comp MvPowerSeries.C := by
    ext a
    change L (iota (h₁ a)) = l₂ (MvPowerSeries.C a)
    rw [← RingHom.comp_apply, hLiota]
    exact (hg a).symm.trans (hg' a)
  have hL_G_formula : ∀ x : Q,
      L (G x) = MvPowerSeries.eval₂ (l₂.toRingHom.comp MvPowerSeries.C)
        (fun j => l₂ (MvPowerSeries.X j)) x := by
    intro x
    rw [hG_eval]
    change (L ∘ MvPowerSeries.eval₂ β yvars) x = _
    rw [MvPowerSeries.comp_eval₂ continuous_of_discreteTopology hyvars hLcont, hL_beta]
    congr 1
    funext j
    exact hL_l2_X j
  have hl₂vars : MvPowerSeries.HasEval (fun j : Fin m => l₂ (MvPowerSeries.X j)) :=
    hasEval_of_forall_mem_ideal _ (map_X_mem_maximalIdeal l₂local)
  have hl₂_eval : (l₂.toRingHom : Q →+* S) =
      MvPowerSeries.eval₂ (l₂.toRingHom.comp MvPowerSeries.C)
        (fun j => l₂ (MvPowerSeries.X j)) :=
    eval_unique_local m (l₂.toRingHom.comp MvPowerSeries.C) l₂.toRingHom l₂local hl₂vars
      (fun _ => rfl)
  have hLG : L.comp G = l₂.toRingHom := by
    ext x
    rw [RingHom.comp_apply, hL_G_formula, hl₂_eval]
  refine ⟨n + m, h₃, l₃, h₃local, hLlocal, h₃cc, fun a => ?_, fun a => ?_⟩
  · change f.hom.toRingHom a = L (MvPowerSeries.C a)
    exact (hLC a).symm
  · change h.hom a = L (G (h₂ a))
    calc
      h.hom a = l₂ (h₂ a) := hh a
      _ = L (G (h₂ a)) := by
        simpa [RingHom.comp_apply] using
          (congrArg (fun q : Q →+* S => q (h₂ a)) hLG).symm

/-- **Stacks Project, Tag 0DQB.** Formal homotopy is an equivalence relation on each set of
morphisms of `\widehat{\mathcal C}_Λ`. -/
@[stacks 0DQB]
theorem formallyHomotopic_equivalence :
    Equivalence (α := R ⟶ S) FormallyHomotopic :=
  ⟨formallyHomotopic_refl, formallyHomotopic_symm, formallyHomotopic_trans⟩

end CompleteLocalAlgCat

end

end Deformation
