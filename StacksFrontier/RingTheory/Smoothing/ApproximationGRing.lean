module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Unramified.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.CompletionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationMorphism
public import StacksFrontier.RingTheory.AdicCompletion.AdicCompletionMapUniqueness
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianGRing
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianPair

/-!
# The approximation property of a Noetherian local G-ring

Let `(R, 𝔪)` be a Noetherian local ring and let `R^∧` be its `𝔪`-adic completion. A system of
polynomial equations over `R` with a solution in `R^∧` has, for every `N`, a solution in an étale
extension `R → R'` at a maximal ideal `𝔪'` over `𝔪` with `κ(𝔪) = κ(𝔪')`, congruent to the given
one modulo `(𝔪')^N R^∧`.

The source deduces the needed smooth factorization from Popescu's theorem (Tag 07GC), which
enters only through the presentation of `R → R^∧` as a filtered colimit of smooth ring maps —
the predicate `Stacks.Smoothing.IsIndSmoothAdicCompletion` of Lemma 0AH5. The source's
hypothesis that `R` is a G-ring yields it through 07GC and Lemma 0AH2
(`isRegularRingHom_algebraMap_adicCompletion`), which is
`Stacks.Smoothing.isIndSmoothAdicCompletion_of_isGRing`; both are proved, so the theorem below
carries no hypothesis beyond the source's own.

## Main definitions

* `StacksDraft.ArtinApproximation.LocalEtaleSolution`: the data the theorem produces — an étale
  extension, a prime over `𝔪` with trivial residue extension, a solution there, and the
  congruence read in the completion of the local ring of the extension at that prime. This is
  the *only* record of that datum in the library: Lemma 0CAR consumes the same structure, whose
  congruence is the one stated there, and the two extra conclusions that Theorem 07QZ's own
  statement adds to it — that the prime is maximal, and the congruence read in `R^∧` along an
  embedding `R' ⊂ R^∧` — are stated by the theorem below alongside the structure rather than by
  a second copy of it.
* `StacksDraft.ArtinApproximation.localCompletionComparison`: the map `R^∧ → (R'_{𝔪'})^∧` along
  which that congruence is read.

## Main results

* `StacksDraft.ArtinApproximation.bijective_localCompletionComparison`: that comparison map is an
  isomorphism when `R → R'` is étale and `𝔪'` lies over `𝔪` with the same residue field. This is
  the ring-level content of the remark preceding Theorem 07QZ, and it is unconditional.
* `StacksDraft.ArtinApproximation.exists_algHom_approx_of_localEtaleSolution`: consequently the
  datum above, whose congruence is read in `(R'_{𝔪'})^∧`, yields an embedding `R' ⊂ R^∧` along
  which the congruence reads `a_i - b_i ∈ (𝔪')^N R^∧`. This is what makes the two tags' spellings
  one statement, and is also unconditional.
* `Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`: Theorem 07QZ.
* `Stacks.Smoothing.exists_localEtaleSolution_of_isAdicComplete`: the same conclusion for an
  `𝔪`-adically complete Noetherian local ring, where it is near-trivial and needs no G-ring
  hypothesis.

## Implementation notes

*The four conclusions and where each comes from.* The construction below produces one étale
extension `R → R'` and one ideal `𝔪'`, and reads the congruence off the single isomorphism
`R ⧸ 𝔪 ^ K ≅ R' ⧸ 𝔪 ^ K R'` (`K = max N 1`) supplied by the étale lift:

* the congruence modulo `(𝔪')^N (R'_{𝔪'})^∧` of Lemma 0CAR, the `approx` field of the structure,
  holds because the lift gives `b_i ≡ y_i` modulo `𝔪 ^ K R'` for a `y_i ∈ R` representing
  `a_i` modulo `𝔪 ^ N`, and `𝔪 ^ K R' ≤ (𝔪')^N`; pushing that into `R'_{𝔪'}` and using
  `𝔪' R'_{𝔪'} = 𝔪_{R'_{𝔪'}}` gives the statement. No comparison of `R^∧` with `(R'_{𝔪'})^∧` is
  needed, and none is used;
* the congruence modulo `(𝔪')^N R^∧` of Theorem 07QZ is the same congruence read along the
  embedding `R' ⊂ R^∧`;
* the congruence modulo the smaller `𝔪 ^ N R^∧` is what the étale lift gives directly, before
  `𝔪 ^ K R' ≤ (𝔪')^N` is used; it is what Example 0A1W reads;
* maximality of `𝔪'` is part of its construction as a kernel of a map onto `R ⧸ 𝔪`.

The étale extension is produced by Lemma 07M7 (`exists_etale_lift_of_smooth`) applied to the
ideal `𝔪 ^ N`, as in Lemma 0AH5; the maximal ideal `𝔪'` is then the kernel of the `R`-algebra map
`R' → R ⧸ 𝔪` obtained from the induced isomorphism `R ⧸ 𝔪 ^ N ≅ R' ⧸ 𝔪 ^ N R'`. That description
makes `𝔪'` maximal with residue field `κ(𝔪)` and makes it lie over `𝔪` by construction, and it
contains `𝔪 R'`, so the congruence modulo `𝔪 ^ N R'` that the étale lift supplies is a congruence
modulo `(𝔪')^N`.

The embedding `R' ⊂ R^∧` of the source's remark preceding the theorem — there obtained from
`R ⊂ R'_{𝔪'} ⊂ R^h ⊂ R^∧` by Tags 04GR and 06LJ — is obtained here from the completion being a
henselian local ring, which lifts the residue-field point `R' → κ(𝔪) = κ(R^∧)` uniquely
(`HenselianLocalRing.existsUnique_algHom_residue_of_etale`). That lift agrees with the map
`R' → R ⧸ 𝔪 ^ N` it has to agree with because `R'` is unramified over `R` and the two maps agree
modulo the nilpotent ideal `𝔪 ⧸ 𝔪 ^ N`.

`N = 0` is admitted: the construction runs at `max N 1` and `(𝔪')^{max N 1} ≤ (𝔪')^N`.

The construction is carried out once, as a private theorem taking
`IsIndSmoothAdicCompletion R (maximalIdeal R)`, and then run twice: at a G-ring, which is the
theorem of the tag, and at an adically complete ring, where the hypothesis holds degenerately
(`Stacks.Smoothing.isIndSmoothAdicCompletion_of_isAdicComplete`) and the conclusion is
near-trivial, `R' = R` and `𝔪' = 𝔪` already working.

## References

* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 0AH5](https://stacks.math.columbia.edu/tag/0AH5)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Smoothing

/-- An element of an adic completion dying in `A ⧸ I ^ n` lies in the extension of `I ^ n`,
provided `I` is finitely generated. -/
private theorem mem_map_pow_of_evalₐ_eq_zero {A : Type u} [CommRing A] {I : Ideal A} (hI : I.FG)
    {n : ℕ} {x : AdicCompletion I A} (hx : AdicCompletion.evalₐ I n x = 0) :
    x ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  have h1 : AdicCompletion.eval I A n x = 0 := by
    have h2 := AdicCompletion.factor_evalₐ_eq_eval (I := I) (n := n) x (by simp)
    rw [hx, map_zero] at h2
    exact h2.symm
  have h3 : x ∈ (I ^ n) • (⊤ : Submodule A (AdicCompletion I A)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    exact h1
  rwa [Ideal.smul_top_eq_map] at h3

/-- Two elements of an adic completion with the same image in `A ⧸ I ^ n` differ by an element of
the extension of `I ^ n`, provided `I` is finitely generated. -/
private theorem sub_mem_map_pow_of_evalₐ_eq {A : Type u} [CommRing A] {I : Ideal A} (hI : I.FG)
    {n : ℕ} {x y : AdicCompletion I A}
    (h : AdicCompletion.evalₐ I n x = AdicCompletion.evalₐ I n y) :
    x - y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) :=
  mem_map_pow_of_evalₐ_eq_zero hI (by rw [map_sub, h, sub_self])

/-- The projection of an adic completion to `A ⧸ I ^ n` kills the extension of `I ^ n`. -/
theorem evalₐ_eq_zero_of_mem_map_pow {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ)
    {x : AdicCompletion I A} (hx : x ∈ (I ^ n).map (algebraMap A (AdicCompletion I A))) :
    AdicCompletion.evalₐ I n x = 0 := by
  have hle : (I ^ n).map (algebraMap A (AdicCompletion I A)) ≤
      Ideal.comap (AdicCompletion.evalₐ I n).toRingHom ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    simp only [Ideal.mem_comap, Ideal.mem_bot, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  simpa using hle hx

/-- The projection of an adic completion to `A ⧸ I ^ n` sends the image of `y : A` to the class
of `y`. -/
theorem evalₐ_algebraMap {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) (y : A) :
    AdicCompletion.evalₐ I n (algebraMap A (AdicCompletion I A) y)
      = Ideal.Quotient.mk (I ^ n) y := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  simp

end Stacks.Smoothing

namespace StacksDraft.ArtinApproximation

/-! ### The datum produced by Theorem 07QZ and consumed by Lemma 0CAR

The structure below is the single record in this library of an étale solution of a polynomial
system over a local ring. Theorem 07QZ, in this file, produces it; Lemma 0CAR
(`StacksDraft.ArtinApproximation.artinApproximationGRing_of_local`) consumes it. It is stated in
the vocabulary of `StacksDraft.ArtinApproximation.Completion` — a prime `q`, and the congruence
read in the completion `(R'_q)^∧` of the local ring at `q` — because that is the form in which
0CAR states its conclusion and the form in which it survives the passage from a local ring to a
general Noetherian ring, where the distinguished prime of the étale extension need not be
maximal. The two further conclusions that Theorem 07QZ's own statement carries, maximality of
`q` and the congruence read in `R^∧`, are stated by `07QZ` itself, next to the structure. -/

/-- The map from the `𝔪`-adic completion of a local ring `L` to the completion of the local ring
of an `L`-algebra `S` at a prime `q` lying over `𝔪`. -/
noncomputable def localCompletionComparison {L S : Type u} [CommRing L] [IsLocalRing L]
    [CommRing S] [Algebra L S] (q : Ideal S) [q.IsPrime]
    (hq : maximalIdeal L = q.comap (algebraMap L S)) :
    AdicCompletion (maximalIdeal L) L →+* Completion q :=
  letI : Algebra L (Localization.AtPrime q) :=
    ((algebraMap S (Localization.AtPrime q)).comp (algebraMap L S)).toAlgebra
  Stacks.Nagata.PthRootDescent.mapAdicCompletion (maximalIdeal L)
    (maximalIdeal (Localization.AtPrime q))
    (by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [hq] at hx
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr hx)

/-- The comparison map out of the completion of the base takes the image of `x : L` to the image
of `x` in the completion of the local ring at `q`. -/
theorem localCompletionComparison_algebraMap {L S : Type u} [CommRing L] [IsLocalRing L]
    [CommRing S] [Algebra L S] (q : Ideal S) [q.IsPrime]
    (hq : maximalIdeal L = q.comap (algebraMap L S)) (x : L) :
    localCompletionComparison q hq (algebraMap L (AdicCompletion (maximalIdeal L) L) x)
      = toCompletion q (algebraMap L S x) := by
  let : Algebra L (Localization.AtPrime q) :=
    ((algebraMap S (Localization.AtPrime q)).comp (algebraMap L S)).toAlgebra
  rw [localCompletionComparison]
  exact Stacks.Nagata.PthRootDescent.mapAdicCompletion_of _ x

/-- **The completion comparison of the remark preceding Theorem 07QZ.** Let `(L, 𝔪)` be a
Noetherian local ring, let `S` be an étale `L`-algebra and let `q` be a prime of `S` lying over
`𝔪` with `κ(𝔪) = κ(q)`. Then the comparison map `L^∧ → (S_q)^∧` is an isomorphism.

This is what makes the congruence `a_i - b_i ∈ (𝔪')^N L^∧` of Theorem 07QZ and the congruence
`a_i - b_i ∈ q^N (S_q)^∧` of Lemma 0CAR two readings of one statement rather than two
statements: the source's chain `L ⊂ S_q ⊂ L^h ⊂ L^∧` identifies the two completions, and this is
that identification, for the canonical map rather than for some abstract equivalence.

Nothing is assumed: the ingredients are
`RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom` — surjectivity from Lemma 039H (2) and
injectivity from faithful flatness, through Lemma 0C4G — together with the uniqueness of a map
out of an adic completion that is compatible with the base
(`eq_adicCompletionMap_of_apply_algebraMap`), which is what pins the abstract isomorphism to
`localCompletionComparison` itself. -/
@[sga "1 I 4.4" "special case"]
theorem bijective_localCompletionComparison {L S : Type u} [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] [CommRing S] [Algebra L S] [Algebra.Etale L S] (q : Ideal S)
    [q.IsPrime] (hq : maximalIdeal L = q.comap (algebraMap L S))
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal L) q (algebraMap L S) hq)) :
    Function.Bijective (localCompletionComparison q hq) := by
  have hnoethS : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing L S
  have hnoethLoc : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ hnoethS
  -- The composite `L → S → S_q`, as a ring homomorphism.
  set f : L →+* Localization.AtPrime q :=
    (algebraMap S (Localization.AtPrime q)).comp (algebraMap L S)
  -- It is a local homomorphism, because `q` lies over `𝔪`.
  have hlocalhom : IsLocalHom f := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have h1 : algebraMap L S x ∈ q := by
      have := (IsLocalRing.mem_maximalIdeal x).mpr hnu
      rwa [hq, Ideal.mem_comap] at this
    exact (IsLocalRing.mem_maximalIdeal (f x)).mp
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr h1) hx
  -- It is étale as a homomorphism of local rings: flat, formally unramified and essentially of
  -- finite type, each inherited from `L → S` étale and `S → S_q` a localization.
  have hfe : Algebra.FormallyEtale S (Localization.AtPrime q) :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have hflatLoc : Module.Flat S (Localization.AtPrime q) :=
    IsLocalization.flat _ q.primeCompl
  have hetale : RingHom.IsEtaleLocalHom f := by
    refine ⟨RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
        (RingHom.flat_algebraMap_iff.mpr hflatLoc),
      RingHom.FormallyUnramified.comp (RingHom.formallyUnramified_algebraMap.mpr inferInstance)
        (RingHom.formallyUnramified_algebraMap.mpr inferInstance),
      RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.mpr inferInstance)
        (RingHom.essFiniteType_algebraMap.mpr inferInstance)⟩
  -- The residue field map is bijective: injective because both are fields, surjective because
  -- `κ(𝔪) → κ(q)` is.
  have hκ : Function.Bijective (IsLocalRing.ResidueField.map f) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨x, hx⟩ := hres.surjective y
    obtain ⟨r, hr⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal L) x
    refine ⟨IsLocalRing.residue L r, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, ← hx, ← hr,
      Ideal.ResidueField.map_algebraMap (maximalIdeal L) q (algebraMap L S) hq r,
      IsScalarTower.algebraMap_apply S (Localization.AtPrime q) (Ideal.ResidueField q),
      IsLocalRing.ResidueField.algebraMap_eq]
    rfl
  -- The comparison map is the canonical one, by uniqueness of a map out of a completion that is
  -- compatible with the base.
  have heq : localCompletionComparison q hq
      = adicCompletionMap f (maximalIdeal L) (maximalIdeal (Localization.AtPrime q))
        (IsLocalRing.map_maximalIdeal_le f) :=
    eq_adicCompletionMap_of_apply_algebraMap _ _ _ _ (maximalIdeal L).fg_of_isNoetherianRing _
      fun x => localCompletionComparison_algebraMap q hq x
  rw [heq]
  exact RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom f hetale hκ

/-- An element of `completionIdeal q N` dies in the quotient by the `N`-th power of the maximal
ideal. -/
theorem evalₐ_eq_zero_of_mem_completionIdeal {B : Type u} [CommRing B] (q : Ideal B)
    [q.IsPrime] {N : ℕ} {x : Completion q} (hx : x ∈ completionIdeal q N) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) N x = 0 :=
  Stacks.Smoothing.evalₐ_eq_zero_of_mem_map_pow _ _ hx

/-- Conversely, an element of the completion dying in the quotient by the `N`-th power of the
maximal ideal lies in `completionIdeal q N`, the maximal ideal being finitely generated. -/
theorem mem_completionIdeal_of_evalₐ_eq_zero {B : Type u} [CommRing B] (q : Ideal B)
    [q.IsPrime] [IsNoetherianRing (Localization.AtPrime q)] {N : ℕ} {x : Completion q}
    (hx : AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) N x = 0) :
    x ∈ completionIdeal q N :=
  Stacks.Smoothing.mem_map_pow_of_evalₐ_eq_zero
    (IsNoetherian.noetherian (maximalIdeal (Localization.AtPrime q))) hx

/-- How `localCompletionComparison` acts on the quotient by the `N`-th power of the maximal
ideal. -/
theorem evalₐ_localCompletionComparison_mk {L S : Type u} [CommRing L] [IsLocalRing L]
    [CommRing S] [Algebra L S] (q : Ideal S) [q.IsPrime]
    (hq : maximalIdeal L = q.comap (algebraMap L S)) (N : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) (y : L)
    (hy : AdicCompletion.evalₐ (maximalIdeal L) N x = Ideal.Quotient.mk _ y) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) N
        (localCompletionComparison q hq x)
      = Ideal.Quotient.mk _
        (algebraMap S (Localization.AtPrime q) (algebraMap L S y)) := by
  let : Algebra L (Localization.AtPrime q) :=
    ((algebraMap S (Localization.AtPrime q)).comp (algebraMap L S)).toAlgebra
  rw [localCompletionComparison, Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion, hy,
    Ideal.quotientMap_mk]
  rfl

/-- The datum that the approximation property for a Noetherian local G-ring produces: an étale
algebra `S` over `L`, a prime `q` of `S` lying over the maximal ideal with the same residue
field, and a solution of the polynomial system in `S` agreeing with the given solution in the
completion modulo the `N`-th power of the maximal ideal. -/
structure LocalEtaleSolution (L : Type u) [CommRing L] [IsLocalRing L]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) L) (N : ℕ)
    (a : Fin n → AdicCompletion (maximalIdeal L) L) where
  /-- The étale extension of `L`. -/
  carrier : Type u
  /-- Its ring structure. -/
  [commRing : CommRing carrier]
  /-- Its algebra structure over `L`. -/
  [algebra : Algebra L carrier]
  /-- It is étale over `L`. -/
  [etale : Algebra.Etale L carrier]
  /-- The chosen prime of the étale extension. -/
  prime : Ideal carrier
  /-- It is prime. -/
  [isPrime : prime.IsPrime]
  /-- It lies over the maximal ideal of `L`. -/
  comap_prime : maximalIdeal L = prime.comap (algebraMap L carrier)
  /-- The residue field extension is trivial. -/
  residueField_bijective : Function.Bijective
    (Ideal.ResidueField.map (maximalIdeal L) prime (algebraMap L carrier) comap_prime)
  /-- The solution of the polynomial system in the étale extension. -/
  sol : Fin n → carrier
  /-- It is a solution. -/
  eval_sol : ∀ j, MvPolynomial.eval₂ (algebraMap L carrier) sol (f j) = 0
  /-- It approximates the given solution to order `N`. -/
  approx : ∀ i, localCompletionComparison prime comap_prime (a i) -
    toCompletion prime (sol i) ∈ completionIdeal prime N

attribute [instance] LocalEtaleSolution.commRing LocalEtaleSolution.algebra
  LocalEtaleSolution.etale LocalEtaleSolution.isPrime

/-- The `N`-th power of the maximal ideal of the localization at a prime `q` is the extension of
`q ^ N`. -/
private theorem maximalIdeal_pow_eq_map {B : Type u} [CommRing B] (q : Ideal B) [q.IsPrime]
    (N : ℕ) : maximalIdeal (Localization.AtPrime q) ^ N
      = (q ^ N).map (algebraMap B (Localization.AtPrime q)) := by
  rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]

/-- **The congruence of Theorem 07QZ, read off the datum of Lemma 0CAR.** The structure above
records the congruence in `(S_q)^∧`, which is the form Lemma 0CAR states. Over a Noetherian local
ring that is the same statement as the congruence in `L^∧` of Theorem 07QZ: the comparison map
`L^∧ → (S_q)^∧` is an isomorphism, so inverting it produces the embedding `S ⊂ L^∧` — an
`L`-algebra map — along which the congruence reads `a_i - b_i ∈ q^N L^∧`.

This is why one structure suffices for both tags. Note that it needs `L` Noetherian, which both
tags hypothesise, and nothing else. -/
theorem exists_algHom_approx_of_localEtaleSolution {L : Type u} [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] {n m : ℕ} {f : Fin m → MvPolynomial (Fin n) L} {N : ℕ}
    {a : Fin n → AdicCompletion (maximalIdeal L) L} (s : LocalEtaleSolution L f N a) :
    ∃ ι : s.carrier →ₐ[L] AdicCompletion (maximalIdeal L) L,
      ∀ i, a i - ι (s.sol i)
        ∈ (s.prime ^ N).map (ι : s.carrier →+* AdicCompletion (maximalIdeal L) L) := by
  set e : AdicCompletion (maximalIdeal L) L ≃+* Completion s.prime :=
    RingEquiv.ofBijective (localCompletionComparison s.prime s.comap_prime)
      (bijective_localCompletionComparison s.prime s.comap_prime s.residueField_bijective)
  have hee : ∀ z : AdicCompletion (maximalIdeal L) L,
      e z = localCompletionComparison s.prime s.comap_prime z := fun _ => rfl
  set ι : s.carrier →ₐ[L] AdicCompletion (maximalIdeal L) L :=
    ⟨(e.symm : Completion s.prime →+* AdicCompletion (maximalIdeal L) L).comp
      (toCompletion s.prime), by
      intro x
      change e.symm (toCompletion s.prime (algebraMap L s.carrier x)) = _
      rw [← localCompletionComparison_algebraMap s.prime s.comap_prime x, ← hee,
        e.symm_apply_apply]⟩
  refine ⟨ι, fun i => ?_⟩
  -- The ideal `q^N (S_q)^∧` of the structure's congruence is `q^N L^∧` read along `e`.
  have hideal : (completionIdeal s.prime N).map
      (e.symm : Completion s.prime →+* AdicCompletion (maximalIdeal L) L)
      = (s.prime ^ N).map (ι : s.carrier →+* AdicCompletion (maximalIdeal L) L) := by
    rw [completionIdeal, maximalIdeal_pow_eq_map, Ideal.map_map, Ideal.map_map]
    rfl
  rw [← hideal]
  have hmem := Ideal.mem_map_of_mem
    (e.symm : Completion s.prime →+* AdicCompletion (maximalIdeal L) L) (s.approx i)
  have h2 : (e.symm : Completion s.prime →+* AdicCompletion (maximalIdeal L) L)
      (localCompletionComparison s.prime s.comap_prime (a i)) = a i :=
    e.symm_apply_apply (a i)
  rwa [map_sub, h2] at hmem

end StacksDraft.ArtinApproximation

namespace Stacks.Smoothing

/-- **The construction behind Theorem 07QZ.** Let `(R, 𝔪)` be a Noetherian local ring whose
`𝔪`-adic completion is a filtered colimit of smooth `R`-algebras. A system of polynomial
equations over `R` with a solution in `R^∧` has, for every `N`, a solution in an étale extension
`R → R'` at a maximal ideal `𝔪'` over `𝔪` with `κ(𝔪) = κ(𝔪')`, congruent to the given solution
modulo `(𝔪')^N R^∧`.

The hypothesis is where the source appeals to Popescu's Theorem 07GC. It holds for a G-ring, by
`Stacks.Smoothing.isIndSmoothAdicCompletion_of_isGRing`, which is how
`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing` below — the theorem of the tag — is
obtained; and it holds degenerately for an adically complete ring, which is
`Stacks.Smoothing.exists_localEtaleSolution_of_isAdicComplete`. -/
private theorem exists_localEtaleSolution_of_isIndSmoothAdicCompletion
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hind : IsIndSmoothAdicCompletion R (maximalIdeal R))
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (N : ℕ)
    (a : Fin n → AdicCompletion (maximalIdeal R) R)
    (ha : ∀ j, MvPolynomial.aeval a (f j) = 0) :
    ∃ s : StacksDraft.ArtinApproximation.LocalEtaleSolution R f N a,
      s.prime.IsMaximal ∧
        ∃ ι : s.carrier →ₐ[R] AdicCompletion (maximalIdeal R) R,
          (∀ x : s.carrier,
              x ∈ s.prime ↔ ι x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R)) ∧
            (∀ i, a i - ι (s.sol i) ∈
              (s.prime ^ N).map (ι : s.carrier →+* AdicCompletion (maximalIdeal R) R)) ∧
            ∀ i, a i - ι (s.sol i) ∈
              (maximalIdeal R ^ N).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  classical
  have hfg : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
  set K := max N 1 with hKdef
  have hK0 : K ≠ 0 := by simp [hKdef]
  have hKN : N ≤ K := le_max_left _ _
  have hKle : maximalIdeal R ^ K ≤ maximalIdeal R := Ideal.pow_le_self hK0
  -- The universal solution algebra `C = R[x]/(f)`, finitely presented over `R`.
  set J : Ideal (MvPolynomial (Fin n) R) := Ideal.span (Set.range f) with hJdef
  have hJfg : J.FG := Submodule.fg_span (Set.finite_range f)
  have : Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ J) :=
    Algebra.FinitePresentation.quotient hJfg
  have hJle : ∀ x ∈ J, MvPolynomial.aeval a x = 0 := by
    intro x hx
    have : J ≤ RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] _) := by
      rw [hJdef, Ideal.span_le]
      rintro y ⟨j, rfl⟩
      simpa using ha j
    simpa using this hx
  set ψ : (MvPolynomial (Fin n) R ⧸ J) →ₐ[R] AdicCompletion (maximalIdeal R) R :=
    Ideal.Quotient.liftₐ J (MvPolynomial.aeval a) hJle with hψdef
  -- Popescu's input: factor `ψ` through a smooth `R`-algebra `B`.
  obtain ⟨B, _, _, hBsm, p, q, hpq⟩ :=
    exists_smooth_factorization_of_isIndSmoothAdicCompletion hind _ ψ
  have : Algebra.Smooth R B := hBsm
  set π : MvPolynomial (Fin n) R →ₐ[R] B := p.comp (Ideal.Quotient.mkₐ R J) with hπdef
  set bB : Fin n → B := fun i => π (MvPolynomial.X i) with hbBdef
  have hψcomp : ψ.comp (Ideal.Quotient.mkₐ R J) = MvPolynomial.aeval a := by
    rw [hψdef]; exact Ideal.Quotient.liftₐ_comp J (MvPolynomial.aeval a) hJle
  have hqb : ∀ i, q (bB i) = a i := by
    intro i
    have h1 : q (bB i) = (ψ.comp (Ideal.Quotient.mkₐ R J)) (MvPolynomial.X i) := by
      rw [hbBdef, hπdef]
      exact AlgHom.congr_fun hpq _
    rw [h1, hψcomp, MvPolynomial.aeval_X]
  have hfb : ∀ j, MvPolynomial.aeval bB (f j) = 0 := by
    intro j
    have h1 : MvPolynomial.aeval bB (f j) = π (f j) := by
      rw [hbBdef, ← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_X_left_apply]
    have hmem : f j ∈ J := by rw [hJdef]; exact Ideal.subset_span ⟨j, rfl⟩
    rw [h1, hπdef]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hmem]
  -- Lift `B → R ⧸ 𝔪 ^ K` along an étale extension (Tag 07M7).
  set σ : B →ₐ[R] R ⧸ maximalIdeal R ^ K :=
    (AdicCompletion.evalₐ (maximalIdeal R) K).comp q with hσdef
  obtain ⟨R', _, _, hR'et, hbij, στ, hστ⟩ :=
    exists_etale_lift_of_smooth (maximalIdeal R ^ K) σ
  have : Algebra.Etale R R' := hR'et
  set J' : Ideal R' := (maximalIdeal R ^ K).map (algebraMap R R') with hJ'def
  set qm : (R ⧸ maximalIdeal R ^ K) →+* (R' ⧸ J') :=
    Ideal.quotientMap J' (algebraMap R R') Ideal.le_comap_map with hqmdef
  set e : (R ⧸ maximalIdeal R ^ K) ≃+* (R' ⧸ J') := RingEquiv.ofBijective qm hbij with hedef
  have hqme : ∀ x, e x = qm x := fun _ => rfl
  have hmkJ' : ∀ r : R, Ideal.Quotient.mk J' (algebraMap R R' r)
      = qm (Ideal.Quotient.mk (maximalIdeal R ^ K) r) := fun _ => Ideal.quotientMap_mk.symm
  -- The canonical `R`-algebra maps `R' → R ⧸ 𝔪 ^ K` and `R' → R ⧸ 𝔪`.
  set Θ' : R' →ₐ[R] R ⧸ maximalIdeal R ^ K :=
    ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk J'), by
      intro r
      change e.symm (Ideal.Quotient.mk J' (algebraMap R R' r)) = _
      rw [hmkJ', ← hqme, e.symm_apply_apply]
      rfl⟩ with hΘ'def
  set Θ : R' →ₐ[R] R ⧸ maximalIdeal R := (Ideal.Quotient.factorₐ R hKle).comp Θ' with hΘdef
  have hΘalg : ∀ r : R, (Θ : R' →+* R ⧸ maximalIdeal R) (algebraMap R R' r)
      = Ideal.Quotient.mk (maximalIdeal R) r := by
    intro r
    change Θ (algebraMap R R' r) = _
    rw [Θ.commutes]
    rfl
  set 𝔪' : Ideal R' := RingHom.ker (Θ : R' →+* R ⧸ maximalIdeal R) with h𝔪'def
  have hcompalg : (Θ : R' →+* R ⧸ maximalIdeal R).comp (algebraMap R R')
      = Ideal.Quotient.mk (maximalIdeal R) := RingHom.ext hΘalg
  have hcomap : maximalIdeal R = 𝔪'.comap (algebraMap R R') := by
    rw [h𝔪'def, RingHom.comap_ker, hcompalg, Ideal.mk_ker]
  have hmle : (maximalIdeal R).map (algebraMap R R') ≤ 𝔪' := by
    rw [Ideal.map_le_iff_le_comap]
    exact hcomap.le
  -- `κ(𝔪) → κ(𝔪')` is bijective, so `𝔪'` is maximal with residue field `κ(𝔪)`.
  set κ : (R ⧸ maximalIdeal R) →+* (R' ⧸ 𝔪') :=
    Ideal.quotientMap 𝔪' (algebraMap R R') hcomap.le with hκdef
  have hκmk : ∀ x : R, κ (Ideal.Quotient.mk (maximalIdeal R) x)
      = Ideal.Quotient.mk 𝔪' (algebraMap R R' x) := fun x => Ideal.quotientMap_mk
  have hκinj : Function.Injective κ := by
    intro u v huv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [hκmk, hκmk, Ideal.Quotient.eq, ← map_sub] at huv
    rw [Ideal.Quotient.eq, hcomap]
    exact huv
  have hκsurj : Function.Surjective κ := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective ((Θ : R' →+* R ⧸ maximalIdeal R) z)
    refine ⟨Ideal.Quotient.mk (maximalIdeal R) r, ?_⟩
    rw [hκmk]
    refine (Ideal.Quotient.eq.2 ?_).symm
    change z - algebraMap R R' r ∈ 𝔪'
    rw [h𝔪'def, RingHom.mem_ker, map_sub, hΘalg r, hr, sub_self]
  have h𝔪'max : 𝔪'.IsMaximal := by
    refine (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪').mpr ?_
    have hF : IsField (R ⧸ maximalIdeal R) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient (maximalIdeal R)).mp inferInstance
    obtain ⟨x₀, y₀, hxy⟩ := hF.exists_pair_ne
    refine ⟨⟨κ x₀, κ y₀, fun h => hxy (hκinj h)⟩, mul_comm, ?_⟩
    · intro x hx
      obtain ⟨u, rfl⟩ := hκsurj x
      have hu : u ≠ 0 := fun h => hx (by rw [h, map_zero])
      obtain ⟨v, hv⟩ := hF.mul_inv_cancel hu
      exact ⟨κ v, by rw [← map_mul, hv, map_one]⟩
  -- Transport bijectivity to the residue fields of the two ideals.
  have hres_bij : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) 𝔪' (algebraMap R R') hcomap) := by
    have hsq : ∀ x : R, Ideal.ResidueField.map (maximalIdeal R) 𝔪' (algebraMap R R') hcomap
        (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField
          (Ideal.Quotient.mk (maximalIdeal R) x))
        = algebraMap (R' ⧸ 𝔪') 𝔪'.ResidueField
            (κ (Ideal.Quotient.mk (maximalIdeal R) x)) := by
      intro x
      rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap, hκmk,
        Ideal.algebraMap_quotient_residueField_mk]
    have hα := Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R)
    have hβ := Ideal.bijective_algebraMap_quotient_residueField 𝔪'
    constructor
    · intro u v huv
      obtain ⟨u, rfl⟩ := hα.2 u
      obtain ⟨v, rfl⟩ := hα.2 v
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
      rw [hsq, hsq] at huv
      rw [hκmk, hκmk] at huv
      have := hβ.1 huv
      rw [← hκmk, ← hκmk] at this
      rw [hκinj this]
    · intro w
      obtain ⟨w, rfl⟩ := hβ.2 w
      obtain ⟨z, rfl⟩ := hκsurj w
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨_, hsq z⟩
  -- The completion is a henselian local ring, so the residue point of `R'` lifts to it.
  have hmaxhat : maximalIdeal (AdicCompletion (maximalIdeal R) R)
      = (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
    AdicCompletion.maximalIdeal_eq_map
  have hhens : HenselianLocalRing (AdicCompletion (maximalIdeal R) R) :=
    henselianLocalRing_of_isAdicComplete_maximalIdeal _
  set κhat : (R ⧸ maximalIdeal R) →+* ResidueField (AdicCompletion (maximalIdeal R) R) :=
    Ideal.Quotient.lift (maximalIdeal R)
      ((residue (AdicCompletion (maximalIdeal R) R)).comp
        (algebraMap R (AdicCompletion (maximalIdeal R) R)))
      (by
        intro x hx
        have hmem : algebraMap R (AdicCompletion (maximalIdeal R) R) x
            ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
          rw [hmaxhat]; exact Ideal.mem_map_of_mem _ hx
        exact Ideal.Quotient.eq_zero_iff_mem.2 hmem) with hκhatdef
  have hκhatmk : ∀ x : R, κhat (Ideal.Quotient.mk (maximalIdeal R) x)
      = residue (AdicCompletion (maximalIdeal R) R)
        (algebraMap R (AdicCompletion (maximalIdeal R) R) x) := fun _ => rfl
  have hκhatinj : Function.Injective κhat := by
    rw [hκhatdef]
    refine RingHom.lift_injective_of_ker_le_ideal _ _ ?_
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue,
      IsLocalRing.maximalIdeal_comap (algebraMap R (AdicCompletion (maximalIdeal R) R))]
  set ψ' : R' →ₐ[R] ResidueField (AdicCompletion (maximalIdeal R) R) :=
    ⟨κhat.comp (Θ : R' →+* R ⧸ maximalIdeal R), by
      intro r
      change κhat ((Θ : R' →+* R ⧸ maximalIdeal R) (algebraMap R R' r)) = _
      rw [hΘalg r, hκhatmk]
      rfl⟩ with hψ'def
  obtain ⟨ι, hι, -⟩ :=
    HenselianLocalRing.existsUnique_algHom_residue_of_etale
      (R := R) (A := R') (S := AdicCompletion (maximalIdeal R) R) ψ'
  -- An element of `R^∧` lies over `r : R` modulo `𝔪` iff it differs from `r` by `𝔪 R^∧`.
  have hone : ∀ (z : AdicCompletion (maximalIdeal R) R) (r : R),
      AdicCompletion.evalOneₐ (maximalIdeal R) z = Ideal.Quotient.mk (maximalIdeal R) r
        ↔ z - algebraMap R (AdicCompletion (maximalIdeal R) R) r
          ∈ (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    intro z r
    rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hfg, RingHom.mem_ker]
    change _ ↔ AdicCompletion.evalOneₐ (maximalIdeal R) _ = 0
    have halg : AdicCompletion.evalOneₐ (maximalIdeal R)
        (algebraMap R (AdicCompletion (maximalIdeal R) R) r)
        = Ideal.Quotient.mk (maximalIdeal R) r :=
      RingHom.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk (maximalIdeal R)) r
    rw [map_sub, sub_eq_zero, halg]
  -- The residue map of `R^∧` factors through `R ⧸ 𝔪` along `evalOneₐ`.
  have hresfac : ∀ z : AdicCompletion (maximalIdeal R) R,
      κhat (AdicCompletion.evalOneₐ (maximalIdeal R) z)
        = residue (AdicCompletion (maximalIdeal R) R) z := by
    intro z
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (maximalIdeal R) z)
    have hz := (hone z r).1 hr.symm
    rw [← hmaxhat] at hz
    have hzz : residue (AdicCompletion (maximalIdeal R) R) z
        = residue (AdicCompletion (maximalIdeal R) R)
          (algebraMap R (AdicCompletion (maximalIdeal R) R) r) := by
      rw [← sub_eq_zero, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hz
    rw [hzz, ← hr, hκhatmk]
  -- `evalₐ K` followed by the projection `R ⧸ 𝔪 ^ K → R ⧸ 𝔪` is `evalOneₐ`.
  have hfactorK : ∀ z : AdicCompletion (maximalIdeal R) R,
      Ideal.Quotient.factor hKle (AdicCompletion.evalₐ (maximalIdeal R) K z)
        = AdicCompletion.evalOneₐ (maximalIdeal R) z := by
    intro z
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) K z)
    have hz : z - algebraMap R (AdicCompletion (maximalIdeal R) R) r
        ∈ (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
      Ideal.map_mono hKle (sub_mem_map_pow_of_evalₐ_eq hfg (by rw [evalₐ_algebraMap, hr]))
    rw [← hr, Ideal.Quotient.factor_mk, (hone z r).2 hz]
  -- `ι` is compatible with `Θ'` because `R'` is unramified over `R`.
  have hcompat : (AdicCompletion.evalₐ (maximalIdeal R) K).comp ι = Θ' := by
    refine Algebra.FormallyUnramified.ext' (Ideal.Quotient.factor hKle) ⟨K, ?_⟩ _ _ ?_
    · rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.zero_eq_bot,
        Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    · intro y
      change Ideal.Quotient.factor hKle (AdicCompletion.evalₐ (maximalIdeal R) K (ι y))
        = Ideal.Quotient.factor hKle (Θ' y)
      rw [hfactorK (ι y)]
      refine hκhatinj ?_
      rw [hresfac (ι y), hι y]
      change _ = κhat ((Θ : R' →+* R ⧸ maximalIdeal R) y)
      rfl
  -- The solution in `R'` and the congruence.
  set b : Fin n → R' := fun i => στ (bB i) with hbdef
  have hsol : ∀ j, MvPolynomial.aeval b (f j) = 0 := by
    intro j
    have h1 : MvPolynomial.aeval b (f j) = στ (MvPolynomial.aeval bB (f j)) := by
      rw [hbdef, MvPolynomial.comp_aeval_apply]
    rw [h1, hfb j, map_zero]
  have hlift : ∀ x : B, qm (σ x) = Ideal.Quotient.mk J' (στ x) := fun x =>
    RingHom.congr_fun hστ x
  have hcong : ∀ i, AdicCompletion.evalₐ (maximalIdeal R) K (a i) = Θ' (b i) := by
    intro i
    have h1 : qm (AdicCompletion.evalₐ (maximalIdeal R) K (a i))
        = Ideal.Quotient.mk J' (b i) := by
      rw [hbdef]
      have := hlift (bB i)
      rw [hσdef] at this
      simpa [hqb i] using this
    change _ = e.symm (Ideal.Quotient.mk J' (b i))
    rw [← h1, ← hqme, e.symm_apply_apply]
  have hfinal : ∀ i, a i - ι (b i)
      ∈ (maximalIdeal R ^ K).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    intro i
    refine sub_mem_map_pow_of_evalₐ_eq hfg ?_
    rw [hcong i]
    exact (AlgHom.congr_fun hcompat (b i)).symm
  -- `𝔪 ^ K R' ≤ (𝔪')^N`, the inclusion through which both congruences are read.
  have hJ'le : J' ≤ 𝔪' ^ N := by
    rw [hJ'def, Ideal.map_pow]
    exact le_trans (Ideal.pow_right_mono hmle K) (Ideal.pow_le_pow_right hKN)
  have hstep : (maximalIdeal R ^ K).map (algebraMap R (AdicCompletion (maximalIdeal R) R))
      ≤ (𝔪' ^ N).map (ι : R' →+* AdicCompletion (maximalIdeal R) R) := by
    have hcompι : (ι : R' →+* AdicCompletion (maximalIdeal R) R).comp (algebraMap R R')
        = algebraMap R (AdicCompletion (maximalIdeal R) R) := RingHom.ext fun x => ι.commutes x
    have h1 : (maximalIdeal R ^ K).map (algebraMap R (AdicCompletion (maximalIdeal R) R))
        = ((maximalIdeal R ^ K).map (algebraMap R R')).map
            (ι : R' →+* AdicCompletion (maximalIdeal R) R) := by
      rw [Ideal.map_map, hcompι]
    rw [h1]
    exact Ideal.map_mono hJ'le
  -- `ι` is local at `𝔪'`: it is the embedding `R' ⊂ R'_{𝔪'} ⊂ R^h ⊂ R^∧` of the source.
  have hιlocal : ∀ x : R',
      x ∈ 𝔪' ↔ ι x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
    intro x
    rw [h𝔪'def, RingHom.mem_ker, show ι x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R)
        ↔ residue (AdicCompletion (maximalIdeal R) R) (ι x) = 0 from
      (Ideal.Quotient.eq_zero_iff_mem).symm, hι x,
      show ψ' x = κhat ((Θ : R' →+* R ⧸ maximalIdeal R) x) from rfl]
    exact (map_eq_zero_iff κhat hκhatinj).symm
  -- The congruence of Lemma 0CAR, read in the completion of `R'_{𝔪'}`.
  have h𝔪'prime : 𝔪'.IsPrime := h𝔪'max.isPrime
  have hnoethR' : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have hnoethLoc : IsNoetherianRing (Localization.AtPrime 𝔪') :=
    IsLocalization.isNoetherianRing 𝔪'.primeCompl _ hnoethR'
  have hlocal : ∀ i, StacksDraft.ArtinApproximation.localCompletionComparison 𝔪' hcomap (a i)
      - StacksDraft.ArtinApproximation.toCompletion 𝔪' (b i)
      ∈ StacksDraft.ArtinApproximation.completionIdeal 𝔪' N := by
    intro i
    -- `y` represents `a i` modulo `𝔪 ^ K`, hence also modulo `𝔪 ^ N`.
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Θ' (b i))
    have hyK : a i - algebraMap R (AdicCompletion (maximalIdeal R) R) y
        ∈ (maximalIdeal R ^ K).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
      refine sub_mem_map_pow_of_evalₐ_eq hfg ?_
      rw [evalₐ_algebraMap, hcong i, hy]
    have hyN : AdicCompletion.evalₐ (maximalIdeal R) N (a i)
        = Ideal.Quotient.mk (maximalIdeal R ^ N) y := by
      have h0 := evalₐ_eq_zero_of_mem_map_pow (maximalIdeal R) N
        (Ideal.map_mono (Ideal.pow_le_pow_right hKN) hyK)
      rw [map_sub, evalₐ_algebraMap, sub_eq_zero] at h0
      exact h0
    -- `b i` and `y` agree modulo `𝔪 ^ K R'`, hence modulo `(𝔪')^N`.
    have hbz : algebraMap R R' y - b i ∈ 𝔪' ^ N := by
      refine hJ'le (Ideal.Quotient.eq.mp ?_)
      rw [hmkJ', hy, ← hqme, hΘ'def]
      change e (e.symm (Ideal.Quotient.mk J' (b i))) = _
      rw [e.apply_symm_apply]
    refine StacksDraft.ArtinApproximation.mem_completionIdeal_of_evalₐ_eq_zero 𝔪' ?_
    rw [map_sub, StacksDraft.ArtinApproximation.evalₐ_localCompletionComparison_mk 𝔪' hcomap N
        (a i) y hyN,
      show AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime 𝔪')) N
          (StacksDraft.ArtinApproximation.toCompletion 𝔪' (b i))
        = Ideal.Quotient.mk _ (algebraMap R' (Localization.AtPrime 𝔪') (b i)) from
        AdicCompletion.evalₐ_of _ N _,
      sub_eq_zero]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← map_sub, StacksDraft.ArtinApproximation.maximalIdeal_pow_eq_map]
    exact Ideal.mem_map_of_mem _ hbz
  exact ⟨{ carrier := R'
           prime := 𝔪'
           isPrime := h𝔪'prime
           comap_prime := hcomap
           residueField_bijective := hres_bij
           sol := b
           eval_sol := fun j => by rw [← MvPolynomial.aeval_def]; exact hsol j
           approx := hlocal },
    h𝔪'max, ι, hιlocal, fun i => hstep (hfinal i),
    fun i => Ideal.map_mono (Ideal.pow_le_pow_right hKN) (hfinal i)⟩

/-- **Stacks 07QZ (the approximation property for G-rings).** Let `(R, 𝔪)` be a Noetherian local
G-ring. A system of polynomial equations over `R` with a solution in the `𝔪`-adic completion
`R^∧` has, for every `N`, a solution in an étale extension `R → R'` at a maximal ideal `𝔪'` over
`𝔪` with `κ(𝔪) = κ(𝔪')`, congruent to the given solution modulo `(𝔪')^N R^∧`.

The G-ring hypothesis is the source's, and it enters where the source puts it: through Popescu's
Theorem 07GC and Lemma 0AH2, which is
`Stacks.Smoothing.isIndSmoothAdicCompletion_of_isGRing`. -/
@[stacks 07QZ "the conclusion for a Noetherian local G-ring, with NO hypothesis beyond the \
source's own: the appeal to Popescu's Theorem 07GC that the source makes here runs through \
Lemma 0AH2 and `indSmooth_of_isRegularRingMap`, which is proved. The instance \
`IsNoetherianRing R` is redundant, being the first component of `IsGRing` (Tag 07GH); it is \
present because the statement names the maximal ideal of `R^∧`, which is only known to be local \
once `R` is known to be Noetherian. Every part of the source's conclusion is here: the étale \
`R → R'`, the ideal `𝔪'` lying over `𝔪`, its MAXIMALITY, the residue field equality \
`κ(𝔪) = κ(𝔪')`, the solution `b` in `R'`, and the congruence `a_i - b_i ∈ (𝔪')^N R^∧` read \
along the embedding `R' ⊂ R^∧` — which is local at `𝔪'`, as in the source's \
`R ⊂ R'_{𝔪'} ⊂ R^h ⊂ R^∧`. Two further conclusions are added: the same congruence modulo the \
smaller `𝔪^N R^∧`, and the congruence of Lemma 0CAR in `(R'_{𝔪'})^∧`, which is the `approx` \
field of `LocalEtaleSolution`. See the module docstring."]
theorem exists_localEtaleSolution_of_isGRing
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hG : IsGRing R)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (N : ℕ)
    (a : Fin n → AdicCompletion (maximalIdeal R) R)
    (ha : ∀ j, MvPolynomial.aeval a (f j) = 0) :
    ∃ s : StacksDraft.ArtinApproximation.LocalEtaleSolution R f N a,
      s.prime.IsMaximal ∧
        ∃ ι : s.carrier →ₐ[R] AdicCompletion (maximalIdeal R) R,
          (∀ x : s.carrier,
              x ∈ s.prime ↔ ι x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R)) ∧
            (∀ i, a i - ι (s.sol i) ∈
              (s.prime ^ N).map (ι : s.carrier →+* AdicCompletion (maximalIdeal R) R)) ∧
            ∀ i, a i - ι (s.sol i) ∈
              (maximalIdeal R ^ N).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  exists_localEtaleSolution_of_isIndSmoothAdicCompletion
    (isIndSmoothAdicCompletion_of_isGRing hG _) f N a ha

/-- **Theorem 07QZ for an `𝔪`-adically complete Noetherian local ring**, where no G-ring
hypothesis is needed and the conclusion is near-trivial: `R → R^∧` is an isomorphism, so `R' = R`
and `𝔪' = 𝔪` already work. -/
theorem exists_localEtaleSolution_of_isAdicComplete
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (N : ℕ)
    (a : Fin n → AdicCompletion (maximalIdeal R) R)
    (ha : ∀ j, MvPolynomial.aeval a (f j) = 0) :
    Nonempty (StacksDraft.ArtinApproximation.LocalEtaleSolution R f N a) := by
  obtain ⟨s, -⟩ := exists_localEtaleSolution_of_isIndSmoothAdicCompletion
    (isIndSmoothAdicCompletion_of_isAdicComplete _) f N a ha
  exact ⟨s⟩

end Stacks.Smoothing

end
