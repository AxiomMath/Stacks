module

public import StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation.LocalRingColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of finite-presentation data: the quotient side

Cofinality of a tail of the index (`Descent.cofinalColimit`), descent of the relations to a
single stage (`Descent.descendRelations`), and the construction `T_i = R_i[x]/(f_{j,i})` over a
pointed index with `colim_i T_i ≅ T` (`Descent.colimQuotient`). Split from
`StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.cdot false

open scoped TensorProduct

universe u

/-!
### Descent of the finite-presentation data

Suppose `R = colim_λ R_λ` is a filtered colimit of local rings as produced by `tag_00QT`, and
`S` is the localization at a prime `q` of `T = R[x₁, …, xₙ]/(f₁, …, f_m)`, with `φ : R → S` the
(local) structure map. Then there is a `λ₀` and a directed sub-system over `{λ ≥ λ₀}` with
`S_λ = (R_λ[x]/(f_{j,λ}))_{q_λ}` giving local homomorphisms `ψ_λ : R_λ → S_λ` satisfying
conditions (1)–(4).

* **Descending the generators.** The `f_j ∈ R[x]` have finitely many coefficients in `R`, each
  the image of an element of some `R_λ`; by directedness there is a single `λ₀` carrying all
  coefficients of all `f_j`, giving `f_{j,λ₀} ∈ R_{λ₀}[x]`, and for `λ ≥ λ₀` one takes for
  `f_{j,λ}` their images under the transition maps. Set `T_λ = R_λ[x]/(f_{j,λ})`, of finite
  presentation over `R_λ`, let `q_λ ⊂ T_λ` be the contraction of `q` along `T_λ → T → S`, and
  put `S_λ = (T_λ)_{q_λ}`, a local ring, with `ψ_λ : R_λ → T_λ → S_λ`.
* **Directedness and locality.** Restricting `Λ` to `{λ ≥ λ₀}` leaves a directed index with the
  same colimit `R`. The transition maps `S_λ → S_μ` are induced by `R_λ → R_μ` on `T_λ → T_μ`
  and the compatibility `q_μ ∩ T_λ = q_λ`; locality of `ψ_λ` and of the transition maps follows
  because the maximal ideals are the `q_λ · (T_λ)_{q_λ}` and the contractions are compatible.
* **Condition (1).** `colim_λ T_λ = R[x]/(f_j) = T`, since polynomial rings and quotients by a
  *fixed finite* generator set commute with filtered colimits, and `colim_λ S_λ = T_q = S`,
  since localization commutes with filtered colimits and the `q_λ` assemble to `q`. The induced
  colimit map is `φ`.
* **Condition (3).** `S_λ = (T_λ)_{q_λ}` is a localization of the finitely presented, hence
  finite type, `R_λ`-algebra `T_λ`, so `ψ_λ` is essentially of finite type.
* **Condition (4).** For `λ ≤ μ`, base change gives
  `S_λ ⊗_{R_λ} R_μ = (T_λ)_{q_λ} ⊗_{R_λ} R_μ ≅ (T_λ ⊗_{R_λ} R_μ)_{image of q_λ}`, and
  `T_λ ⊗_{R_λ} R_μ ≅ T_μ` because base change commutes with a quotient of a polynomial ring by
  a finitely generated ideal — this is where finite *presentation* is essential. Localizing
  further at `q_μ` gives `S_μ`, so `S_μ` is a localization of `S_λ ⊗_{R_λ} R_μ` at the prime
  corresponding to `q_μ`.
-/

namespace Descent

/-!
### The construction

The system is built from concrete data, so that each of the four conditions can be verified, and
the whole conclusion is bundled into the single construction lemma `Descent.systemBundle`. Its
internal decomposition consists of the concrete construction definitions (`Tobj`, `qcon`,
`Sobj'`, `fSmap`, `psiS`, …, mirroring `namespace Stacks.EssentialFiniteness.LocalRingColimit`)
together with four key lemmas:

* `descendRelations`: choose a `λ₀` over which all coefficients of the `f_j` lift, using the
  directedness of `Λ` and representability of elements of `Ring.DirectLimit`.
* `colimQuotient`: `colim_λ (R_λ[x]/(f_{j,λ})) ≅ T` — a polynomial ring and a quotient by a
  *fixed* finite relation set commute with a filtered colimit.
* `colimLocalization`: `colim_λ (T_λ)_{q_λ} ≅ S` — localization commutes with a filtered colimit,
  and the `q_λ = π_λ⁻¹ q` assemble to `q`.
* `baseChangeQuotient`: `T_λ ⊗_{R_λ} R_μ ≅ T_μ` — base change commutes with a quotient of a
  polynomial ring by a finitely generated ideal, followed by localization of a localization.
-/

/-- **Cofinality of a tail of the index.**

Given the R-side colimit data from `tag_00QT R` (a directed index `Λ`, the family `Robj` with
its instances, transition maps `fR`, the directed-system/locality data, and the colimit iso
`eR : colim Robj ≃+* R` together with locality `heR` of the structural maps) and a chosen
`lam0 : Λ`, the *cofinal tail* `Lam := {x : Λ // lam0 ≤ x}` carries the restricted family
`Robj' i = Robj i.val` with transition maps `fR' i j h = fR i.val j.val h`, and the colimit over
`Lam` is still `R`. Concretely, there is an iso
`eR' : colim Robj' ≃+* R` whose structural maps are local.

The directedness, locality and essential finite type of the restricted family follow from the
originals by passing to `i.val`; the content is the existence of `eR'`, i.e. that a cofinal
subdiagram of a filtered colimit has the same colimit. -/
lemma cofinalColimit
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Λ : Type u) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (Robj : Λ → Type u) [∀ i, CommRing (Robj i)] [∀ i, IsLocalRing (Robj i)]
    (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
    (heR : ∀ i, IsLocalHom ((eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i)))
    (lam0 : Λ) :
    ∃ eR' : Ring.DirectLimit (fun i : {x : Λ // lam0 ≤ x} => Robj i.val)
        (fun i j h => ((fR i.val j.val h : Robj i.val →+* Robj j.val) :
          (fun i : {x : Λ // lam0 ≤ x} => Robj i.val) i →
          (fun i : {x : Λ // lam0 ≤ x} => Robj i.val) j)) ≃+* R,
      (∀ i : {x : Λ // lam0 ≤ x},
        IsLocalHom ((eR'.toRingHom).comp
          (Ring.DirectLimit.of (fun i : {x : Λ // lam0 ≤ x} => Robj i.val) _ i))) ∧
      -- the structural maps of the tail agree with the original structural maps (cofinality):
      (∀ i : {x : Λ // lam0 ≤ x},
        (eR'.toRingHom).comp
            (Ring.DirectLimit.of (fun i : {x : Λ // lam0 ≤ x} => Robj i.val) _ i)
          = (eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i.val)) := by
  -- Strategy: build the canonical comparison `ι : colim Robj' →+* colim Robj` via
  -- `Ring.DirectLimit.lift` from `of Robj _ i.val`; then `eR' := eR ∘ ι` satisfies clause (2)
  -- by `lift_of` and clause (1) from `heR`. `ι` is bijective by cofinality of the tail.
  set Lam := {x : Λ // lam0 ≤ x} with hLam
  have : Nonempty Lam := ⟨⟨lam0, le_refl lam0⟩⟩
  have : IsDirected Lam (· ≤ ·) := ⟨fun a b =>
    let ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.val b.val
    ⟨⟨c, a.property.trans hac⟩, hac, hbc⟩⟩
  set Robj' : Lam → Type u := fun i => Robj i.val with hRobj'
  set fR' : ∀ i j : Lam, i ≤ j → Robj' i → Robj' j :=
    fun i j h => (fR i.val j.val h : Robj i.val → Robj j.val) with hfR'
  set ι : Ring.DirectLimit Robj' fR' →+*
      Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) :=
    Ring.DirectLimit.lift Robj' fR' _
      (fun i => Ring.DirectLimit.of Robj _ i.val)
      (fun i j hij x =>
        Ring.DirectLimit.of_f (f := fun i j h => (fR i j h : Robj i → Robj j)) hij x)
    with hι
  have hι_of : ∀ (i : Lam) (x : Robj' i),
      ι (Ring.DirectLimit.of Robj' fR' i x) = Ring.DirectLimit.of Robj _ i.val x :=
    fun i x => Ring.DirectLimit.lift_of _ _ _ i x
  have hsurj : Function.Surjective ι := by
    intro z
    obtain ⟨ν, x, rfl⟩ := Ring.DirectLimit.exists_of z
    obtain ⟨c, hνc, hl0c⟩ := directed_of (· ≤ ·) ν lam0
    refine ⟨Ring.DirectLimit.of Robj' fR' ⟨c, hl0c⟩ (fR ν c hνc x), ?_⟩
    rw [hι_of]
    exact Ring.DirectLimit.of_f (f := fun i j h => (fR i j h : Robj i → Robj j)) hνc x
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
    rw [hι_of] at hz
    obtain ⟨j, hij, hj0⟩ := Ring.DirectLimit.of.zero_exact (f' := fR) hz
    obtain ⟨c, hic, hjc⟩ := directed_of (· ≤ ·) i.val j
    have hl0c : lam0 ≤ c := le_trans i.property hic
    have hxc : fR i.val c (le_trans hij hjc) x = 0 := by
      have := hRdir.map_map (f := fun i j h => (fR i j h : Robj i → Robj j)) hij hjc x
      rw [← this, hj0]
      simp
    have hstep : Ring.DirectLimit.of Robj' fR' i x
        = Ring.DirectLimit.of Robj' fR' ⟨c, hl0c⟩ (fR i.val c (le_trans hij hjc) x) :=
      (Ring.DirectLimit.of_f (G := Robj') (f := fR') (i := i) (j := ⟨c, hl0c⟩) hic x).symm
    rw [hstep, hxc, map_zero]
  set ιe : Ring.DirectLimit Robj' fR' ≃+*
      Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) :=
    RingEquiv.ofBijective ι ⟨hinj, hsurj⟩ with hιe
  have hcomp : ∀ i : Lam, (ιe.trans eR).toRingHom.comp (Ring.DirectLimit.of Robj' fR' i)
      = (eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i.val) := by
    intro i
    ext x
    simp only [RingHom.comp_apply]
    show eR (ιe (Ring.DirectLimit.of Robj' fR' i x)) = eR (Ring.DirectLimit.of Robj _ i.val x)
    exact congrArg eR (hι_of i x)
  exact ⟨ιe.trans eR, fun i => hcomp i ▸ heR i.val, hcomp⟩

/-- Every element of the colimit ring lifts to an element of some stage. -/
private theorem exists_eq_comp_of
    {R : Type u} [CommRing R] {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {Robj : Λ → Type u} [∀ i, CommRing (Robj i)] {fR : ∀ i j, i ≤ j → Robj i →+* Robj j}
    (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R) (c : R) :
    ∃ (i : Λ) (x : Robj i), ((eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i)) x = c := by
  obtain ⟨i, x, hx⟩ := Ring.DirectLimit.exists_of (eR.symm c)
  exact ⟨i, x, by simp [hx]⟩

/-- **Descent of the finite presentation to a single stage.**

From the finite-presentation and localization data for `S` over `R`, together with the `R`-side
colimit data of `tag_00QT R`, there is a stage `lam0 : Λ`, a prime `q` realizing `S` as `T_q`,
and relations `frel : Fin m → MvPolynomial (Fin n) (Robj lam0)` whose images under the structural
map `R_{lam0} → R` (that is, `eR ∘ of _ lam0`) present `T`, hence `S = T_q`.

The point is that the `f_j` have only finitely many coefficients, so all of them lift to a common
stage of the colimit. -/
@[ega "IV 1.8.4.2" "Local base, special case",
  ega "IV 8.1.1" "special case",
  sga "3 VIB 10.0" "(ii), special case"]
theorem descendRelations
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Algebra T S] [IsScalarTower R T S]
    (hTfp : Algebra.FinitePresentation R T)
    (M : Submonoid T) (hM : IsLocalization M S)
    (Λ : Type u) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (Robj : Λ → Type u) [∀ i, CommRing (Robj i)] [∀ i, IsLocalRing (Robj i)]
    (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
    (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R) :
    ∃ (q : Ideal T) (_ : q.IsPrime) (_ : IsLocalization q.primeCompl S)
      (lam0 : Λ) (n m : ℕ) (frel : Fin m → MvPolynomial (Fin n) (Robj lam0)),
      Nonempty (T ≃ₐ[R] (MvPolynomial (Fin n) R ⧸
        Ideal.span (Set.range (fun j => MvPolynomial.map
          ((eR.toRingHom).comp (Ring.DirectLimit.of Robj _ lam0)) (frel j))))) := by
  -- `hTfp.out` gives `T = R[x]/(f_j)` with `m` relations; each relation's finitely many
  -- coefficients lift to a common stage `lam0` (directedness over the finite coefficient set);
  -- `q` = contraction of `𝔪_S` along `T → S` (from `hM`, `S` local localization of `T`).
  classical
  -- PART A: the prime q = contraction of 𝔪_S; S = T_q since S is local localization of T.
  have hAtP : IsLocalization.AtPrime S (IsLocalRing.maximalIdeal S) := by
    refine IsLocalization.of_le_isUnit fun x hx => ?_
    rwa [IsUnit.mem_submonoid_iff, ← IsLocalRing.notMem_maximalIdeal]
  refine ⟨Ideal.comap (algebraMap T S) (IsLocalRing.maximalIdeal S), inferInstance,
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M S
      (IsLocalRing.maximalIdeal S), ?_⟩
  -- PART B: descend the relations.
  obtain ⟨n, f, hf_surj, hker⟩ := hTfp.out
  obtain ⟨G, hG⟩ := hker
  -- hG : Ideal.span ↑G = RingHom.ker f.toRingHom
  set ρ : ∀ i, Robj i →+* R := fun i => (eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i) with hρ
  -- the finite set of all coefficients of the relations
  set C : Finset R :=
    G.biUnion (fun p => Finset.image (fun s => p.coeff s) p.support) with hC
  -- each element of R lifts to some stage of the colimit (via `eR.symm` and `exists_of`)
  have key : ∀ c : R, ∃ (i : Λ) (x : Robj i), ρ i x = c := exists_eq_comp_of eR
  choose stage pre hpre using key
  -- a single common stage `lam0` dominating all stages of coefficients in `C` (directedness)
  obtain ⟨lam0, hlam0⟩ := (C.image stage).exists_le
  -- a section `sec : R → Robj lam0` of `ρ lam0` over `C`, sending `0 ↦ 0`
  set sec : R → Robj lam0 := fun c => if c = 0 then 0 else if h : c ∈ C then
    fR (stage c) lam0 (hlam0 _ (Finset.mem_image_of_mem _ h)) (pre c) else 0 with hsec
  have hsec0 : sec 0 = 0 := by simp [hsec]
  have hsecC : ∀ c ∈ C, ρ lam0 (sec c) = c := by
    intro c hc
    by_cases hc0 : c = 0
    · simp only [hsec, ite_eq_left hc0]; rw [map_zero, hc0]
    · simp only [hsec, ite_eq_right hc0, dite_eq_left hc]
      simp only [hρ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show (Ring.DirectLimit.of Robj (fun i j h => (fR i j h : Robj i → Robj j)) lam0)
        (fR (stage c) lam0 (hlam0 _ (Finset.mem_image_of_mem _ hc)) (pre c))
        = (Ring.DirectLimit.of Robj (fun i j h => (fR i j h : Robj i → Robj j)) (stage c)) (pre c)
        from Ring.DirectLimit.of_f _ _]
      simpa only [hρ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using
        hpre c
  -- the section recovers every coefficient of every relation
  have hsecP : ∀ p ∈ G, ∀ s, ρ lam0 (sec (p.coeff s)) = p.coeff s := by
    intro p hp s
    by_cases hz : p.coeff s = 0
    · rw [hz, hsec0, map_zero]
    · refine hsecC _ ?_
      rw [hC, Finset.mem_biUnion]
      exact ⟨p, hp, Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.mpr hz)⟩
  -- enumerate `G` as a family indexed by `Fin G.card`
  let e := G.equivFin
  set frelR : Fin G.card → MvPolynomial (Fin n) R :=
    fun j => (e.symm j : MvPolynomial (Fin n) R) with hfrelR
  -- the lifted relations: replace each coefficient by its chosen preimage
  set frel : Fin G.card → MvPolynomial (Fin n) (Robj lam0) :=
    fun j => AddMonoidAlgebra.ofCoeff
      (Finsupp.mapRange sec hsec0 (AddMonoidAlgebra.coeff (frelR j))) with hfrel
  -- pushing the lifted relations back along `ρ lam0` recovers the original relations
  have hmap : ∀ j, MvPolynomial.map (ρ lam0) (frel j) = frelR j := by
    refine fun j => MvPolynomial.ext _ _ fun s => ?_
    rw [MvPolynomial.coeff_map]
    show ρ lam0 ((Finsupp.mapRange sec hsec0 (AddMonoidAlgebra.coeff (frelR j))) s)
      = (frelR j).coeff s
    rw [Finsupp.mapRange_apply]
    exact hsecP _ (e.symm j).property _
  -- hence the range of the pushed relations is exactly `↑G`
  have hrange : Set.range (fun j => MvPolynomial.map (ρ lam0) (frel j))
      = (↑G : Set (MvPolynomial (Fin n) R)) := by
    rw [show (fun j => MvPolynomial.map (ρ lam0) (frel j)) = frelR from funext hmap, hfrelR]
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    exact ⟨fun ⟨j, hj⟩ => hj ▸ (e.symm j).property, fun hx => ⟨e ⟨x, hx⟩, by simp⟩⟩
  -- assemble the recovery isomorphism
  refine ⟨lam0, n, G.card, frel, ⟨?_⟩⟩
  have hspan : RingHom.ker f.toRingHom
      = Ideal.span (Set.range (fun j => MvPolynomial.map (ρ lam0) (frel j))) := by
    rw [hrange, ← hG]
  exact (Ideal.quotientKerAlgEquivOfSurjective hf_surj).symm.trans
    (Ideal.quotientEquivAlgOfEq R hspan)

/-!
### The construction over a pointed index

For an index with `lam0 ≤ i` for every `i`, mirroring `namespace
Stacks.EssentialFiniteness.LocalRingColimit`:

* `Tobj i = R_i[x] / (images of frel under fR lam0 i)`, a polynomial ring modulo the fixed
  relations;
* `qcon i`, the preimage of `𝔪_S` along `T_i → T → S`, a prime ideal;
* `Sobj' i = (T_i)_{qcon i}`, a local ring;
* the transition maps `fSmap` and the structure maps `psiS`, both obtained from
  `Localization.localRingHom` and hence local.

The analytic content sits in three lemmas: `colimQuotient` (`colim_i T_i ≅ T`),
`colimLocalization` (`colim_i S_i ≅ S`, giving condition (1)) and `baseChangeQuotient`
(`T_i ⊗_{R_i} R_j ≅ T_j`, giving condition (4)).
-/

section

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] (φ : R →+* S)
variable {T : Type u} [CommRing T] [Algebra R T] [Algebra T S] [IsScalarTower R T S]
variable {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
variable {Robj : Λ → Type u} [∀ i, CommRing (Robj i)] [∀ i, IsLocalRing (Robj i)]
variable (fR : ∀ i j, i ≤ j → Robj i →+* Robj j)
variable (eR : Ring.DirectLimit Robj (fun i j h => (fR i j h : Robj i → Robj j)) ≃+* R)
variable (lam0 : Λ) (hbot : ∀ i, lam0 ≤ i)
variable (n m : ℕ) (frel : Fin m → MvPolynomial (Fin n) (Robj lam0))

/-- The structural ring map `R_i → R` (`= eR ∘ of i`). -/
noncomputable def RtoR (i : Λ) : Robj i →+* R :=
  (eR.toRingHom).comp (Ring.DirectLimit.of Robj _ i)

/-- The relations transported to stage `i` (using `lam0 ≤ i`). -/
noncomputable def frelAt (i : Λ) (j : Fin m) : MvPolynomial (Fin n) (Robj i) :=
  MvPolynomial.map (fR lam0 i (hbot i)) (frel j)

/-- The relation ideal at stage `i`. -/
noncomputable def Irel (i : Λ) : Ideal (MvPolynomial (Fin n) (Robj i)) :=
  Ideal.span (Set.range (frelAt fR lam0 hbot n m frel i))

/-- `T_i = R_i[x]/(frel images)`. -/
def Tobj (i : Λ) : Type u :=
  MvPolynomial (Fin n) (Robj i) ⧸ Irel fR lam0 hbot n m frel i

/-- The commutative ring structure on `Tobj`, that of the quotient `R_i[x]/(frel images)`. -/
noncomputable instance (i : Λ) : CommRing (Tobj fR lam0 hbot n m frel i) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin n) (Robj i) ⧸ Irel fR lam0 hbot n m frel i))

/-- The structural map `R_i → T_i` (coefficient inclusion `R_i ↪ R_i[x] ↠ T_i`). -/
noncomputable def RtoT (i : Λ) : Robj i →+* Tobj fR lam0 hbot n m frel i :=
  (Ideal.Quotient.mk (Irel fR lam0 hbot n m frel i)).comp (MvPolynomial.C)

/-- Transition maps compose with `RtoR` correctly: `RtoR j ∘ fR i j = RtoR i`. -/
lemma RtoR_comp_fR (i j : Λ) (hij : i ≤ j) :
    (RtoR fR eR j).comp (fR i j hij) = RtoR fR eR i := by
  ext x
  simp only [RtoR, RingHom.comp_apply, Ring.DirectLimit.of_f]

/-- `fR i j ∘ fR lam0 i = fR lam0 j` (from `hRdir`). -/
lemma fR_comp_fR (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j : Λ) (hij : i ≤ j) :
    (fR i j hij).comp (fR lam0 i (hbot i)) = fR lam0 j (hbot j) := by
  ext x
  exact hRdir.map_map (hbot i) hij x

/-- Transitivity of the `fR` system: `fR j k ∘ fR i j = fR i k`. -/
lemma fR_trans (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j k : Λ) (hij : i ≤ j) (hjk : j ≤ k) :
    (fR j k hjk).comp (fR i j hij) = fR i k (le_trans hij hjk) := by
  ext x
  exact hRdir.map_map hij hjk x

/-- The relation generators transport: `map (fR i j) (frelAt i k) = frelAt j k`. -/
lemma frelAt_transport
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j : Λ) (hij : i ≤ j) (k : Fin m) :
    MvPolynomial.map (fR i j hij) (frelAt fR lam0 hbot n m frel i k)
      = frelAt fR lam0 hbot n m frel j k := by
  simp only [frelAt, MvPolynomial.map_map, fR_comp_fR fR lam0 hbot hRdir i j hij]

/-- Well-definedness inclusion for the transition map: `Irel i ≤ comap (map (fR i j)) (Irel j)`. -/
lemma Irel_le_comap
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j : Λ) (hij : i ≤ j) :
    Irel fR lam0 hbot n m frel i
      ≤ Ideal.comap (MvPolynomial.map (fR i j hij)) (Irel fR lam0 hbot n m frel j) := by
  rw [Irel, Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, frelAt_transport fR lam0 hbot n m frel hRdir i j hij k]
  exact Ideal.subset_span ⟨k, rfl⟩

/-- The transition map `T_i → T_j`. -/
noncomputable def fTmap
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j : Λ) (hij : i ≤ j) :
    Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j :=
  Ideal.quotientMap (Irel fR lam0 hbot n m frel j) (MvPolynomial.map (fR i j hij))
    (Irel_le_comap fR lam0 hbot n m frel hRdir i j hij)

/-- `fTmap` sends the class of `p` to the class of its image under `fR i j`. -/
@[simp] lemma fTmap_mk
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j : Λ) (hij : i ≤ j) (p : MvPolynomial (Fin n) (Robj i)) :
    fTmap fR lam0 hbot n m frel hRdir i j hij (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk _ (MvPolynomial.map (fR i j hij) p) :=
  Ideal.quotientMap_mk

/-- The directed system structure on `(Tobj, fTmap)`. -/
lemma Tobj_directedSystem
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j))) :
    DirectedSystem (Tobj fR lam0 hbot n m frel)
      (fun i j h => (fTmap fR lam0 hbot n m frel hRdir i j h :
        Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j)) := by
  refine ⟨fun i x => ?_, fun k j i hij hjk x => ?_⟩
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show fTmap fR lam0 hbot n m frel hRdir i i _ (Ideal.Quotient.mk _ p) = _
    rw [fTmap_mk]
    refine congrArg _ ?_
    have hid : ∀ (h : i ≤ i), fR i i h = RingHom.id (Robj i) := by
      intro h; ext y; exact hRdir.map_self y
    rw [hid, MvPolynomial.map_id]
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show fTmap fR lam0 hbot n m frel hRdir j k hjk
          (fTmap fR lam0 hbot n m frel hRdir i j hij (Ideal.Quotient.mk _ p)) = _
    rw [fTmap_mk, fTmap_mk]
    show _ = fTmap fR lam0 hbot n m frel hRdir i k _ (Ideal.Quotient.mk _ p)
    rw [fTmap_mk, MvPolynomial.map_map, fR_trans fR hRdir i j k hij hjk]

/-- The relation generators map down to the same `R`-relations: `map (RtoR i) (frelAt i k)
    = map (RtoR lam0) (frel k)`. -/
lemma frelAt_to_R (i : Λ) (k : Fin m) :
    MvPolynomial.map (RtoR fR eR i) (frelAt fR lam0 hbot n m frel i k)
      = MvPolynomial.map (RtoR fR eR lam0) (frel k) := by
  rw [frelAt, MvPolynomial.map_map, RtoR_comp_fR fR eR lam0 i (hbot i)]

/-- The target ideal in `R[x]` cutting out `T`. -/
noncomputable def Jrel : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range (fun j => MvPolynomial.map (RtoR fR eR lam0) (frel j)))

/-- The structural map `R_i[x] → T` (factoring through `R[x]/Jrel ≅ T`). -/
noncomputable def alphaT
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T) (i : Λ) :
    MvPolynomial (Fin n) (Robj i) →+* T :=
  (e.toRingHom).comp ((Ideal.Quotient.mk (Jrel fR eR lam0 n m frel)).comp
    (MvPolynomial.map (RtoR fR eR i)))

/-- The map `alphaT` kills the relation ideal `Irel i`, so it descends to `T_i`. -/
lemma alphaT_vanish
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T) (i : Λ) :
    ∀ a ∈ Irel fR lam0 hbot n m frel i, alphaT fR eR lam0 n m frel e i a = 0 := by
  intro a ha
  rw [Irel] at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨k, rfl⟩
    simp only [alphaT, RingHom.comp_apply, frelAt_to_R fR eR lam0 hbot n m frel i k]
    have hmem : MvPolynomial.map (RtoR fR eR lam0) (frel k) ∈ Jrel fR eR lam0 n m frel :=
      Ideal.subset_span (Set.mem_range_self k)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
    exact map_zero _
  · simp only [map_zero]
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The structural map `T_i → T`. -/
noncomputable def piTmap
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T) (i : Λ) :
    Tobj fR lam0 hbot n m frel i →+* T :=
  Ideal.Quotient.lift (Irel fR lam0 hbot n m frel i)
    (alphaT fR eR lam0 n m frel e i) (alphaT_vanish fR eR lam0 hbot n m frel e i)

/-- `piTmap` sends the class of `p` to `alphaT i p`. -/
@[simp] lemma piTmap_mk
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T) (i : Λ)
    (p : MvPolynomial (Fin n) (Robj i)) :
    piTmap fR eR lam0 hbot n m frel e i (Ideal.Quotient.mk _ p)
      = alphaT fR eR lam0 n m frel e i p :=
  Ideal.Quotient.lift_mk _ _ _

/-- `R`-compatibility of the transition maps: `fT i j ∘ RtoT i = RtoT j ∘ fR i j`. -/
lemma fT_comp_RtoT
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (i j : Λ) (hij : i ≤ j) :
    (fTmap fR lam0 hbot n m frel hRdir i j hij).comp (RtoT fR lam0 hbot n m frel i)
      = (RtoT fR lam0 hbot n m frel j).comp (fR i j hij) := by
  ext r
  show fTmap fR lam0 hbot n m frel hRdir i j hij
        (Ideal.Quotient.mk _ (MvPolynomial.C r))
      = Ideal.Quotient.mk _ (MvPolynomial.C (fR i j hij r))
  rw [fTmap_mk, MvPolynomial.map_C]

/-- `R`-compatibility of the structural map to `T`: `πT i ∘ RtoT i = algebraMap R T ∘ RtoR i`,
where `e` is the presentation iso and `he` records that `e` is `R`-linear on constants. -/
lemma piT_comp_RtoT
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T)
    (he : ∀ s : R, e (Ideal.Quotient.mk (Jrel fR eR lam0 n m frel) (MvPolynomial.C s))
      = algebraMap R T s)
    (i : Λ) :
    (piTmap fR eR lam0 hbot n m frel e i).comp (RtoT fR lam0 hbot n m frel i)
      = (algebraMap R T).comp (RtoR fR eR i) := by
  ext r
  show piTmap fR eR lam0 hbot n m frel e i
        (Ideal.Quotient.mk _ (MvPolynomial.C r))
      = algebraMap R T (RtoR fR eR i r)
  rw [piTmap_mk, alphaT]
  simp only [RingHom.comp_apply, MvPolynomial.map_C]
  exact he (RtoR fR eR i r)

/-- Compatibility of the structural maps to `T` with the transition maps:
`πT j ∘ fT i j = πT i`. -/
lemma piT_compat
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T)
    (i j : Λ) (hij : i ≤ j) :
    (piTmap fR eR lam0 hbot n m frel e j).comp (fTmap fR lam0 hbot n m frel hRdir i j hij)
      = piTmap fR eR lam0 hbot n m frel e i := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  show piTmap fR eR lam0 hbot n m frel e j
      (fTmap fR lam0 hbot n m frel hRdir i j hij (Ideal.Quotient.mk _ p))
    = piTmap fR eR lam0 hbot n m frel e i (Ideal.Quotient.mk _ p)
  rw [fTmap_mk, piTmap_mk, piTmap_mk, alphaT, alphaT]
  simp only [RingHom.comp_apply, MvPolynomial.map_map, RtoR_comp_fR fR eR i j hij]

/-- Surjectivity of `RtoR` at a suitable stage: every `r : R` lifts to some `Robj j`. -/
lemma RtoR_surj (r : R) : ∃ j, ∃ a : Robj j, RtoR fR eR j a = r := by
  exact exists_eq_comp_of eR r

/-- Lift a polynomial over `R` to a polynomial over some `Robj j` (`lam0 ≤ j`). -/
lemma mvpoly_lift (P : MvPolynomial (Fin n) R) :
    ∃ j, ∃ _ : lam0 ≤ j, ∃ Q : MvPolynomial (Fin n) (Robj j),
      MvPolynomial.map (RtoR fR eR j) Q = P := by
  classical
  -- choose a stage for each coefficient
  choose! jc ac hac using fun (v : Fin n →₀ ℕ) => RtoR_surj fR eR (P.coeff v)
  obtain ⟨J, hJ⟩ := (P.support.image jc).exists_le
  obtain ⟨J', hJlam, hJ'⟩ := directed_of (· ≤ ·) J lam0
  refine ⟨J', hJ',
    ∑ v ∈ P.support, MvPolynomial.monomial v
      (if h : jc v ≤ J' then fR (jc v) J' h (ac v) else 0), ?_⟩
  rw [map_sum]
  conv_rhs => rw [P.as_sum]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [MvPolynomial.map_monomial]
  have hjcJ' : jc v ≤ J' := le_trans (hJ _ (Finset.mem_image_of_mem _ hv)) hJlam
  rw [dite_eq_left hjcJ']
  congr 1
  rw [show RtoR fR eR J' (fR (jc v) J' hjcJ' (ac v))
      = (RtoR fR eR J').comp (fR (jc v) J' hjcJ') (ac v) from rfl,
    RtoR_comp_fR fR eR (jc v) J' hjcJ', hac v]

/-- Kernel descent for a single element: `RtoR j a = 0` implies the relation descends. -/
lemma RtoR_ker_elt
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (j : Λ) (a : Robj j) (ha : RtoR fR eR j a = 0) :
    ∃ j', ∃ hjj' : j ≤ j', fR j j' hjj' a = 0 := by
  have hof : Ring.DirectLimit.of Robj (fun i j h => (fR i j h : Robj i → Robj j)) j a = 0 := by
    have h1 : eR (Ring.DirectLimit.of Robj _ j a) = 0 := ha
    have h2 := congrArg eR.symm h1
    rwa [RingEquiv.symm_apply_apply, map_zero] at h2
  exact Ring.DirectLimit.of.zero_exact (f' := fR) hof

/-- Kernel descent for polynomials: `map (RtoR j) D = 0` implies `map (fR j j') D = 0`
    at a later stage. -/
lemma RtoR_ker_descent
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (j : Λ) (D : MvPolynomial (Fin n) (Robj j))
    (hD : MvPolynomial.map (RtoR fR eR j) D = 0) :
    ∃ j', ∃ hjj' : j ≤ j', MvPolynomial.map (fR j j' hjj') D = 0 := by
  classical
  have hcoeff : ∀ v, RtoR fR eR j (D.coeff v) = 0 := by
    intro v
    rw [← MvPolynomial.coeff_map, hD, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  choose! jv hjv hjva using fun (v : Fin n →₀ ℕ) =>
    RtoR_ker_elt fR eR hRdir j (D.coeff v) (hcoeff v)
  obtain ⟨J, hJ⟩ := (D.support.image jv).exists_le
  obtain ⟨J', hjJ', hJJ'⟩ := directed_of (· ≤ ·) j J
  refine ⟨J', hjJ', ?_⟩
  rw [MvPolynomial.eq_zero_iff]
  intro v
  rw [MvPolynomial.coeff_map]
  by_cases hv : v ∈ D.support
  · have hjvJ' : jv v ≤ J' := le_trans (hJ _ (Finset.mem_image_of_mem _ hv)) hJJ'
    have key : fR (jv v) J' hjvJ' (fR j (jv v) (hjv v) (D.coeff v)) = 0 := by
      rw [hjva v, map_zero]
    rw [show fR j J' hjJ' (D.coeff v)
        = fR (jv v) J' hjvJ' (fR j (jv v) (hjv v) (D.coeff v)) from ?_, key]
    rw [← RingHom.comp_apply, fR_trans fR hRdir j (jv v) J' (hjv v) hjvJ']
  · rw [MvPolynomial.notMem_support_iff] at hv
    rw [hv, map_zero]

/-- The pointwise compatibility needed for `Ring.DirectLimit.lift`. -/
lemma piT_compat_pointwise
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T)
    (i j : Λ) (hij : i ≤ j) (x : Tobj fR lam0 hbot n m frel i) :
    piTmap fR eR lam0 hbot n m frel e j (fTmap fR lam0 hbot n m frel hRdir i j hij x)
      = piTmap fR eR lam0 hbot n m frel e i x :=
  DFunLike.congr_fun (piT_compat fR eR lam0 hbot n m frel hRdir e i j hij) x

/-- The induced map `colim T_i → T`. -/
noncomputable def iotaT
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T) :
    Ring.DirectLimit (Tobj fR lam0 hbot n m frel)
      (fun i j h => (fTmap fR lam0 hbot n m frel hRdir i j h :
        Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j)) →+* T :=
  Ring.DirectLimit.lift _ _ _ (piTmap fR eR lam0 hbot n m frel e)
    (piT_compat_pointwise fR eR lam0 hbot n m frel hRdir e)

/-- `iotaT` restricted along the `i`-th structural map of the colimit is `piTmap i`. -/
lemma iotaT_of
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T)
    (i : Λ) (x : Tobj fR lam0 hbot n m frel i) :
    iotaT fR eR lam0 hbot n m frel hRdir e
        (Ring.DirectLimit.of _ _ i x)
      = piTmap fR eR lam0 hbot n m frel e i x :=
  Ring.DirectLimit.lift_of _ _ _ _ _

-- `Tobj i` is only defeq (not syntactically equal) to `MvPolynomial … ⧸ Irel i`;
-- relax type-transparency so `rw` matches through the `Ring.DirectLimit` term.
set_option backward.isDefEq.respectTransparency.types false in
/-- `iotaT : colim T_i → T` is surjective: every element of `T` is the class of a polynomial over
`R`, and such a polynomial lifts to a polynomial over some `R_j`. -/
lemma iotaT_surjective
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T) :
    Function.Surjective (iotaT fR eR lam0 hbot n m frel hRdir e) := by
  intro t
  obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective (e.symm t)
  obtain ⟨j, _, Q, hQ⟩ := mvpoly_lift fR eR lam0 n P
  refine ⟨Ring.DirectLimit.of _ _ j (Ideal.Quotient.mk _ Q), ?_⟩
  rw [iotaT_of, piTmap_mk, alphaT, RingHom.comp_apply, RingHom.comp_apply, hQ, hP]
  exact e.apply_symm_apply t

/-- Any `R_i`-linear combination of the relations lies in `Irel i`. -/
lemma frelAt_combo_mem (i : Λ) (c : Fin m → MvPolynomial (Fin n) (Robj i)) :
    (∑ k, c k * frelAt fR lam0 hbot n m frel i k) ∈ Irel fR lam0 hbot n m frel i := by
  refine Ideal.sum_mem _ (fun k _ => ?_)
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

-- needed: `iotaT_injective`'s `rw` through `Ring.DirectLimit` only matches because `Tobj i` is
-- merely defeq to `MvPolynomial … ⧸ Irel i`.
set_option backward.isDefEq.respectTransparency.types false in
/-- `iotaT : colim T_i → T` is injective: if a polynomial over `R_i` lands in the relation ideal
over `R`, then already over some later stage it lies in the relation ideal there. -/
lemma iotaT_injective
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T) :
    Function.Injective (iotaT fR eR lam0 hbot n m frel hRdir e) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- hz : iotaT (of i (mk P)) = 0
  rw [iotaT_of, piTmap_mk, alphaT, RingHom.comp_apply, RingHom.comp_apply] at hz
  -- e (mk (map (RtoR i) P)) = 0  ⇒  mk (map (RtoR i) P) = 0
  have hmem0 : (Ideal.Quotient.mk (Jrel fR eR lam0 n m frel)) (MvPolynomial.map (RtoR fR eR i) P)
      = 0 := e.injective (by rw [map_zero]; exact hz)
  rw [Ideal.Quotient.eq_zero_iff_mem, Jrel,
    Ideal.mem_span_range_iff_exists_fun] at hmem0
  obtain ⟨c, hc⟩ := hmem0
  -- lift each coefficient polynomial c k to a stage
  classical
  choose! jk _ cc hcc using fun (k : Fin m) => mvpoly_lift fR eR lam0 n (c k)
  -- common stage J ≥ i, ≥ lam0, ≥ all jk
  obtain ⟨J0, hJ0⟩ := (Finset.univ.image jk).exists_le
  obtain ⟨J1, hiJ1, hJ01⟩ := directed_of (· ≤ ·) i J0
  obtain ⟨J, hJ1J, hlamJ⟩ := directed_of (· ≤ ·) J1 lam0
  have hiJ : i ≤ J := le_trans hiJ1 hJ1J
  have hjkJ : ∀ k, jk k ≤ J := fun k =>
    le_trans (hJ0 _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) (le_trans hJ01 hJ1J)
  -- the transported pieces at stage J
  set cJ : Fin m → MvPolynomial (Fin n) (Robj J) :=
    fun k => MvPolynomial.map (fR (jk k) J (hjkJ k)) (cc k) with hcJ
  set PJ : MvPolynomial (Fin n) (Robj J) := MvPolynomial.map (fR i J hiJ) P with hPJ
  set D : MvPolynomial (Fin n) (Robj J) :=
    (∑ k, cJ k * frelAt fR lam0 hbot n m frel J k) - PJ with hD
  -- map (RtoR J) D = 0
  have hmapcJ : ∀ k, MvPolynomial.map (RtoR fR eR J) (cJ k) = c k := by
    intro k
    rw [hcJ, MvPolynomial.map_map, RtoR_comp_fR fR eR (jk k) J (hjkJ k), hcc k]
  have hmapPJ : MvPolynomial.map (RtoR fR eR J) PJ = MvPolynomial.map (RtoR fR eR i) P := by
    rw [hPJ, MvPolynomial.map_map, RtoR_comp_fR fR eR i J hiJ]
  have hDzero : MvPolynomial.map (RtoR fR eR J) D = 0 := by
    rw [hD, map_sub, map_sum, hmapPJ,
      show (∑ k, MvPolynomial.map (RtoR fR eR J) (cJ k * frelAt fR lam0 hbot n m frel J k))
        = MvPolynomial.map (RtoR fR eR i) P from ?_, sub_self]
    rw [← hc]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_mul, hmapcJ k, frelAt_to_R fR eR lam0 hbot n m frel J k]
  -- descend the kernel relation
  obtain ⟨J', hJJ', hD'⟩ := RtoR_ker_descent fR eR n hRdir J D hDzero
  -- now map (fR i J') P ∈ Irel J'
  have hPJ' : MvPolynomial.map (fR i J' (le_trans hiJ hJJ')) P
      = MvPolynomial.map (fR J J' hJJ') (∑ k, cJ k * frelAt fR lam0 hbot n m frel J k) := by
    have : MvPolynomial.map (fR J J' hJJ') D = 0 := hD'
    rw [hD, map_sub, hPJ, MvPolynomial.map_map, fR_trans fR hRdir i J J' hiJ hJJ',
      sub_eq_zero] at this
    exact this.symm
  have hmemP : MvPolynomial.map (fR i J' (le_trans hiJ hJJ')) P
      ∈ Irel fR lam0 hbot n m frel J' := by
    rw [hPJ', map_sum]
    simp only [map_mul, frelAt_transport fR lam0 hbot n m frel hRdir J J' hJJ']
    exact frelAt_combo_mem fR lam0 hbot n m frel J' _
  -- conclude of i (mk P) = 0
  have hfT : fTmap fR lam0 hbot n m frel hRdir i J' (le_trans hiJ hJJ')
      (Ideal.Quotient.mk _ P) = 0 := by
    rw [fTmap_mk]
    exact (Ideal.Quotient.eq_zero_iff_mem (I := Irel fR lam0 hbot n m frel J')).mpr hmemP
  have hstep := (Ring.DirectLimit.of_f
    (G := Tobj fR lam0 hbot n m frel)
    (f := fun i j h => (fTmap fR lam0 hbot n m frel hRdir i j h :
      Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
    (le_trans hiJ hJJ') (Ideal.Quotient.mk _ P)).symm
  rw [hstep, hfT, map_zero]

/-- The colimit of the `T_i = R_i[x]/(images of frel)` over the pointed index recovers `T`. This
is where finite *presentation* is essential: a fixed finite relation set commutes with the
filtered colimit.

The structural maps `T_i → T` are induced by `MvPolynomial.map (RtoR i)`, well defined on the
quotient because the images of `frel` generate the kernel of `R[x] ↠ T`, and they assemble to a
directed system whose induced map `colim T_i → T` is a ring isomorphism.

The hypothesis `hRdir` is necessary: for incoherent transition maps `fR` the relation ideal
`Irel`, which is derived from the bottom stage, need not be compatible with the system. -/
@[ega "IV 5.13.1" "Clause (i), special case"]
lemma colimQuotient
    (hRdir : DirectedSystem Robj (fun i j h => (fR i j h : Robj i → Robj j)))
    (hTfp : Algebra.FinitePresentation R T)
    (hpres : Nonempty (T ≃ₐ[R] MvPolynomial (Fin n) R ⧸
      Ideal.span (Set.range (fun j => MvPolynomial.map (RtoR fR eR lam0) (frel j))))) :
    ∃ (fT : ∀ i j, i ≤ j → Tobj fR lam0 hbot n m frel i →+* Tobj fR lam0 hbot n m frel j)
      (πT : ∀ i, Tobj fR lam0 hbot n m frel i →+* T),
      (DirectedSystem (Tobj fR lam0 hbot n m frel)
        (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))) ∧
      (∀ i j (hij : i ≤ j), (πT j).comp (fT i j hij) = πT i) ∧
      -- `R`-compatibility of the colimit data (needed by the S-side `descendSPointedBundle`):
      (∀ i j (hij : i ≤ j),
        (fT i j hij).comp (RtoT fR lam0 hbot n m frel i)
          = (RtoT fR lam0 hbot n m frel j).comp (fR i j hij)) ∧
      (∀ i, (πT i).comp (RtoT fR lam0 hbot n m frel i)
          = (algebraMap R T).comp (RtoR fR eR i)) ∧
      -- `fT` is the CANONICAL transition map `fTmap` (pins `fT` on the polynomial-variable
      -- generators, not just on the coefficient subring — essential for condition (4)):
      (∀ i j (hij : i ≤ j),
        fT i j hij = fTmap fR lam0 hbot n m frel hRdir i j hij) ∧
      (∃ (eT : Ring.DirectLimit (Tobj fR lam0 hbot n m frel)
          (fun i j h => (fT i j h : Tobj fR lam0 hbot n m frel i → Tobj fR lam0 hbot n m frel j))
          ≃+* T),
        ∀ i, eT.toRingHom.comp (Ring.DirectLimit.of _ _ i) = πT i) := by
  set e : MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel ≃+* T :=
    hpres.some.symm.toRingEquiv with he
  have heconst : ∀ s : R, e (Ideal.Quotient.mk (Jrel fR eR lam0 n m frel) (MvPolynomial.C s))
      = algebraMap R T s := by
    intro s
    have hmk : Ideal.Quotient.mk (Jrel fR eR lam0 n m frel) (MvPolynomial.C s)
        = algebraMap R (MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel) s := by
      rw [show (algebraMap R (MvPolynomial (Fin n) R ⧸ Jrel fR eR lam0 n m frel) s)
          = Ideal.Quotient.mk _ (algebraMap R (MvPolynomial (Fin n) R) s) from rfl,
        MvPolynomial.algebraMap_eq]
    rw [hmk, he]
    exact hpres.some.symm.commutes s
  refine ⟨fun i j hij => fTmap fR lam0 hbot n m frel hRdir i j hij,
    fun i => piTmap fR eR lam0 hbot n m frel e i,
    Tobj_directedSystem fR lam0 hbot n m frel hRdir,
    fun i j hij => piT_compat fR eR lam0 hbot n m frel hRdir e i j hij,
    fun i j hij => fT_comp_RtoT fR lam0 hbot n m frel hRdir i j hij,
    fun i => piT_comp_RtoT fR eR lam0 hbot n m frel e heconst i,
    fun i j hij => rfl, ?_⟩
  refine ⟨RingEquiv.ofBijective (iotaT fR eR lam0 hbot n m frel hRdir e)
    ⟨iotaT_injective fR eR lam0 hbot n m frel hRdir e,
     iotaT_surjective fR eR lam0 hbot n m frel hRdir e⟩, ?_⟩
  intro i
  exact RingHom.ext fun x => iotaT_of fR eR lam0 hbot n m frel hRdir e i x

end

end Descent

end
