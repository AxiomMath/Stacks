module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.TermwiseSplit
public import StacksFrontier.RingTheory.Cech.PairSectionsObstruction
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.PrincipalCutFirstCohomology

/-!
# No resolution of the structure presheaf of pairs has `Γ_I`-acyclic sections

Step 3 of the proof of [Stacks, Tag 099D] chooses an injective resolution `𝒪 ⟶ 𝒥•` of the
structure presheaf on the chaotically topologized category of presented pairs and asserts that
`𝒥•(U)` is a resolution of `A` *by injective `A`-modules* at every object `U = (A, I)`, which is
what makes `ℱ• = ⋃ₙ 𝒥•[ℐⁿ]` satisfy `ℱ•(U) ≅ RΓ_I(A)`. That assertion is refuted in
`StacksFrontier/RingTheory/Cech/PairEvaluationInjectives.lean`, and the two obvious repairs —
degreewise injective sections, K-injective sections — are refuted in
`StacksFrontier/RingTheory/Cech/PairSectionsObstruction.lean`.

Both of those refutations use *divisibility*: an injective module over `P.ring` is divisible by a
nonzerodivisor `a`, and a morphism of pairs whose ring map kills `a` therefore annihilates it. The
remaining repair asks for much less than injectivity. All the rest of Step 3 uses is that the
sections be **`Γ_I`-acyclic**: a bounded below `Γ_{I_P}`-acyclic resolution of `A` computes
`RΓ_{I_P}(A)` just as well as an injective one, and acyclicity gives no divisibility at all —
restriction of scalars along a non-flat ring map carries `Γ_I`-acyclic modules to `Γ_I`-acyclic
modules, which is why that repair looked flatness-free.

**This file refutes the acyclic repair too.** For a principal ideal `I = (g)` a module `N` is
`Γ_I`-acyclic exactly when the localization map `N ⟶ N_g` is surjective: the extended Čech
complex on the one element family `g` is the two term complex `N ⟶ N_g`, so `H⁰_I(N)` is its
kernel and `H¹_I(N)` its cokernel. Surjectivity says that every element of `N` is divisible by `g`
*modulo `g`-power torsion*, which is weaker than divisibility — but the witness is still
**uniform**: one exponent `k` bounds the torsion for the element at hand. Reducing modulo
`2 ^ (k + 1)` destroys it.

## The obstruction

The pair `(ℤ, 2ℤ)` — `Stacks.PairSite.intIdealPair` — admits for every `n` a morphism of pairs
onto `(ℤ/2ⁿ⁺¹, 2 · ℤ/2ⁿ⁺¹)` — `Stacks.PairSite.nilTwoPair`, the morphism being
`Stacks.PairSite.intIdealToNil` — because the image of `2ℤ` generates the ideal `2 · ℤ/2ⁿ⁺¹` on
the nose, which is what a morphism of `Stacks.PairSite.Pair` demands. Let `ι : 𝒪 ⟶ J` be a
monomorphism of pair-modules and let `ε = ι(1)` be the image of the unit section at `(ℤ, 2ℤ)`. If
`2 ^ k • (2 • m - ε) = 0` for some section `m` of `J` at `(ℤ, 2ℤ)` — which is what surjectivity of
`J(ℤ, 2ℤ) ⟶ J(ℤ, 2ℤ)_2` provides for the fraction `ε / 2` — then restricting along the morphism to
`(ℤ/2ᵏ⁺¹, 2 · ℤ/2ᵏ⁺¹)` and using `2 ^ (k + 1) = 0` there gives `ι(2 ^ k) = 0`, hence `2 ^ k = 0` in
`ℤ/2ᵏ⁺¹`, which is false.

Note where the obstruction sits: at the *source* `(ℤ, 2ℤ)`, not at the target. Shrinking the
category of pairs does not help, because `(A₀, I₀) ⟶ (A₀/aA₀, …)` is a morphism of pairs whenever
the target is a presented pair.

## Main results

* `Stacks.PairSite.ne_zero_pow_smul_sub_app_one` — **the obstruction.** For a monomorphism
  `ι : 𝒪 ⟶ J` of pair-modules, no section `m` of `J` at `(ℤ, 2ℤ)` and no exponent `k` satisfy
  `2 ^ k • (2 • m - ι(1)) = 0`.
* `Stacks.PairSite.notMem_range_mkLinearMap_value` and
  `Stacks.PairSite.not_surjective_mkLinearMap_value` — the localization map
  `J(ℤ, 2ℤ) ⟶ J(ℤ, 2ℤ)_2` is not surjective, i.e. `H¹_{2ℤ}(J(ℤ, 2ℤ)) ≠ 0`.
* `Stacks.PairSite.not_exists_mono_surjective_value` — **the structure presheaf does not embed
  into a pair-module with `Γ_I`-acyclic sections.** Since every resolution of `𝒪` starts with such
  an embedding, there is no `Γ_I`-acyclic resolution of `𝒪` at all.
* `Stacks.PairSite.not_exists_resolution_surjective_value` — the same conclusion in the shape in
  which Step 3 would have used it: a complex of pair-modules, strictly bounded below by `0` and
  quasi-isomorphic to `𝒪[0]`, whose sections at every pair are `Γ_I`-acyclic in every degree.
* `Stacks.PairSite.not_exists_resolution_isZero_localCohomology` — the same statement with the
  acyclicity hypothesis spelled with the library's local cohomology functor
  `Stacks.LocalCohomology.localCohomologyWithSupportIn`, via
  `Stacks.PairSite.surjective_mkLinearMap_of_isZero_localCohomology`.

## Implementation notes

The refuted hypothesis is stated as surjectivity of `LocalizedModule.mkLinearMap` at a generator
of the pair's ideal, rather than as the vanishing of a local cohomology functor in positive
degrees. For a principal ideal the two are equivalent — that is the content of the two term
extended Čech complex — and the elementary form is both implied by every spelling of
`Γ_I`-acyclicity in the library and free of the Noetherian hypotheses that the library's
comparison between `RΓ_I` and `RΓ_{V(I)}` carries. Refuting the weaker hypothesis refutes the
stronger ones.

`Stacks.PairSite.intIdealPair` has the same *ring* as `Stacks.PairSite.intPair`, namely
`ℤ[x₁, …, xₙ]` in no variables modulo no relations; only the distinguished ideal differs. The
ideal has to be nonzero for the statement to have content: `Γ_0` is the identity functor, so every
module is `Γ_0`-acyclic and the pair `(ℤ, 0)` used by the divisibility refutations says nothing
here.

`Stacks.PairSite.moduleValue` restates the module structure that `Stacks.PairSite.PairModule.value`
already carries, as an instance keyed on `P.ring`: instance synthesis does not unfold the
structure presheaf of rings, so a goal `Module P.ring (M.value P)` is not solved by the generic
`ModuleCat` instance even though the two module structures are definitionally equal.

No `@[stacks 099D]` attribute is attached: as with the other obstruction files in this directory,
this is a statement about what the proof of the tag cannot be formalized by, not a part of the
tag's statement.

## References

* [The Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [The Stacks Project, Tag 0952](https://stacks.math.columbia.edu/tag/0952)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.PairSite

/-- **The sections of a pair-module at a pair, as a module over the pair's ring.** This is the
module structure `Stacks.PairSite.PairModule.value` carries, restated as an instance keyed on
`P.ring` rather than on `↑(structureRings.obj P.ix)`; the two rings are definitionally equal, but
instance synthesis does not unfold the structure presheaf of rings. -/
instance moduleValue (M : PairModule.{u}) (P : Pair.{u}) : Module P.ring (M.value P) :=
  (M.value P).isModule

/-! ### The rings `ℤ/2ⁿ⁺¹` -/

/-- **The ring `ℤ/2ⁿ⁺¹`**, presented as a quotient of `ℤ[x₁, …, xₙ]` in no variables. -/
abbrev nilTwoRing (n : ℕ) : Type u :=
  presentationRing.{u} 0 ⧸ Ideal.span {(2 : presentationRing.{u} 0) ^ (n + 1)}

/-- `2` in `ℤ/2ⁿ⁺¹` is the image of `2` under the quotient map. -/
private theorem two_eq_mk_nilTwoRing (n : ℕ) : (2 : nilTwoRing.{u} n) =
    Ideal.Quotient.mk (Ideal.span {(2 : presentationRing.{u} 0) ^ (n + 1)}) 2 :=
  (map_ofNat _ 2).symm

/-- `2 ^ (n + 1)` vanishes in `ℤ/2ⁿ⁺¹`. -/
theorem two_pow_succ_eq_zero_nilTwoRing (n : ℕ) : (2 : nilTwoRing.{u} n) ^ (n + 1) = 0 := by
  rw [two_eq_mk_nilTwoRing, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/-- `2 ^ n` does *not* vanish in `ℤ/2ⁿ⁺¹`: this is the exactness of the nilpotency order that the
obstruction below exploits. -/
theorem two_pow_ne_zero_nilTwoRing (n : ℕ) : (2 : nilTwoRing.{u} n) ^ n ≠ 0 := by
  rw [two_eq_mk_nilTwoRing, ← map_pow]
  intro h
  have hdvd := map_dvd (presentationRingZeroEquiv.{u} : presentationRing.{u} 0 →+* ℤ)
    (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h))
  rw [map_pow, map_pow, map_ofNat] at hdvd
  have hle : (2 : ℤ) ^ (n + 1) ≤ 2 ^ n := Int.le_of_dvd (by positivity) hdvd
  rw [pow_succ] at hle
  linarith [pow_pos (two_pos : (0 : ℤ) < 2) n]

/-! ### The pairs `(ℤ, 2ℤ)` and `(ℤ/2ⁿ⁺¹, 2 · ℤ/2ⁿ⁺¹)` -/

/-- **The pair `(ℤ, 2ℤ)`**, presented with no variables and no relations. Its ring is the ring of
`Stacks.PairSite.intPair`; what differs is the distinguished ideal, which has to be nonzero for
`Γ_I`-acyclicity to say anything. -/
def intIdealPair : Pair.{u} where
  numVars := 0
  relations := ⊥
  ideal := Ideal.span {2}

/-- **The pair `(ℤ/2ⁿ⁺¹, 2 · ℤ/2ⁿ⁺¹)`**, presented with no variables and the single relation
`2 ^ (n + 1) = 0`. -/
def nilTwoPair (n : ℕ) : Pair.{u} where
  numVars := 0
  relations := Ideal.span {(2 : presentationRing.{u} 0) ^ (n + 1)}
  ideal := Ideal.span {2}

/-- The ideal of `(ℤ, 2ℤ)` is generated by the single element `2`. -/
theorem span_two_intIdealPair :
    Ideal.span {(2 : (intIdealPair.{u}).ring)} = (intIdealPair.{u}).ideal := rfl

/-- `2 ^ (n + 1)` vanishes in the ring of `(ℤ/2ⁿ⁺¹, 2 · ℤ/2ⁿ⁺¹)`. -/
theorem two_pow_succ_eq_zero_nilTwoPair (n : ℕ) :
    (2 : (nilTwoPair.{u} n).ring) ^ (n + 1) = 0 :=
  two_pow_succ_eq_zero_nilTwoRing.{u} n

/-- `2 ^ n` does not vanish in the ring of `(ℤ/2ⁿ⁺¹, 2 · ℤ/2ⁿ⁺¹)`. -/
theorem two_pow_ne_zero_nilTwoPair (n : ℕ) : (2 : (nilTwoPair.{u} n).ring) ^ n ≠ 0 :=
  two_pow_ne_zero_nilTwoRing.{u} n

/-- **The reduction `ℤ ⟶ ℤ/2ⁿ⁺¹`** between the rings of the two pairs. -/
def intIdealToNilRingHom (n : ℕ) : (intIdealPair.{u}).ring →+* (nilTwoPair.{u} n).ring :=
  Ideal.Quotient.lift (⊥ : Ideal (presentationRing.{u} 0))
    (Ideal.Quotient.mk (Ideal.span {(2 : presentationRing.{u} 0) ^ (n + 1)}))
    (fun a ha => by
      obtain rfl : a = 0 := by simpa using ha
      exact map_zero _)

/-- **The reduction `(ℤ, 2ℤ) ⟶ (ℤ/2ⁿ⁺¹, 2 · ℤ/2ⁿ⁺¹)`**, a morphism of pairs: the image of the
ideal `2ℤ` generates the ideal `2 · ℤ/2ⁿ⁺¹` on the nose, which is the condition `J₀ = I₀ B₀`. -/
def intIdealToNil (n : ℕ) : intIdealPair.{u} ⟶ nilTwoPair.{u} n where
  toRingHom := intIdealToNilRingHom.{u} n
  map_ideal := by
    change Ideal.span {(2 : (nilTwoPair.{u} n).ring)} =
      Ideal.map (intIdealToNilRingHom.{u} n) (Ideal.span {(2 : (intIdealPair.{u}).ring)})
    rw [Ideal.map_span, Set.image_singleton, map_ofNat]

/-- The reduction sends `2` to `2`. -/
theorem intIdealToNil_two (n : ℕ) :
    (intIdealToNil.{u} n).toRingHom (2 : (intIdealPair.{u}).ring) =
      (2 : (nilTwoPair.{u} n).ring) :=
  map_ofNat _ 2

/-! ### The obstruction -/

/-- **The obstruction.** Let `ι : 𝒪 ⟶ J` be a monomorphism of pair-modules and let `ε = ι(1)` be
the image of the unit section at the pair `(ℤ, 2ℤ)`. Then no section `m` of `J` at `(ℤ, 2ℤ)`
satisfies `2 ^ k • (2 • m - ε) = 0`, for any exponent `k`.

An element of that form is exactly a witness that the fraction `ε / 2` lies in the image of the
localization map, with `2 ^ k` the torsion bound; the point is that a single `k` has to serve,
whereas restricting along `(ℤ, 2ℤ) ⟶ (ℤ/2ᵏ⁺¹, 2 · ℤ/2ᵏ⁺¹)` turns the witness into the false
statement `2 ^ k = 0` in `ℤ/2ᵏ⁺¹`. -/
theorem ne_zero_pow_smul_sub_app_one {J : PairModule.{u}} (ι : structureModule.{u} ⟶ J) [Mono ι]
    (m : J.value intIdealPair.{u}) (k : ℕ) :
    (2 : (intIdealPair.{u}).ring) ^ k •
        ((2 : (intIdealPair.{u}).ring) • m -
          PresheafOfModules.Hom.app ι (intIdealPair.{u}).ix (1 : (intIdealPair.{u}).ring)) ≠ 0 := by
  intro hzero
  -- the hypothesis, rearranged: `2 ^ k • ι(1)` is `2 ^ (k + 1) • m`
  have hsub : (2 : (intIdealPair.{u}).ring) ^ k •
        ((2 : (intIdealPair.{u}).ring) • m) =
      (2 : (intIdealPair.{u}).ring) ^ k •
        PresheafOfModules.Hom.app ι (intIdealPair.{u}).ix (1 : (intIdealPair.{u}).ring) := by
    rwa [← sub_eq_zero, ← smul_sub]
  -- restricting `2 ^ k • ι(1)` along the reduction kills it, because `2 ^ (k + 1) = 0` there
  have hres : J.restriction (intIdealToNil.{u} k)
      ((2 : (intIdealPair.{u}).ring) ^ k •
        PresheafOfModules.Hom.app ι (intIdealPair.{u}).ix (1 : (intIdealPair.{u}).ring)) = 0 := by
    rw [← hsub, map_smul, map_smul, smul_smul, ← pow_succ,
      ModuleCat.restrictScalars.smul_def, map_pow, intIdealToNil_two,
      two_pow_succ_eq_zero_nilTwoPair, zero_smul]
    rfl
  -- `2 ^ k • ι(1) = ι(2 ^ k)`; stated term-level, because `ι(1)` is an element of
  -- `↑(structureModule.obj P.ix)` and `rw` refuses the defeq with `P.ring`
  have hiota : (2 : (intIdealPair.{u}).ring) ^ k •
        PresheafOfModules.Hom.app ι (intIdealPair.{u}).ix (1 : (intIdealPair.{u}).ring) =
      PresheafOfModules.Hom.app ι (intIdealPair.{u}).ix
        ((2 : (intIdealPair.{u}).ring) ^ k) :=
    (map_smul _ _ _).symm.trans
      (congrArg (PresheafOfModules.Hom.app ι (intIdealPair.{u}).ix)
        (mul_one ((2 : (intIdealPair.{u}).ring) ^ k)))
  -- naturality moves it to the target pair
  have hzeroQ : PresheafOfModules.Hom.app ι (nilTwoPair.{u} k).ix
      ((intIdealToNil.{u} k).toRingHom ((2 : (intIdealPair.{u}).ring) ^ k)) = 0 :=
    (PairModule.naturality_apply ι (intIdealToNil.{u} k)
        ((2 : (intIdealPair.{u}).ring) ^ k)).trans
      ((congrArg (fun y => J.restriction (intIdealToNil.{u} k) y) hiota.symm).trans hres)
  -- `ι` is injective at every pair, so `2 ^ k = 0` in `ℤ/2ᵏ⁺¹`
  refine two_pow_ne_zero_nilTwoPair.{u} k ?_
  calc (2 : (nilTwoPair.{u} k).ring) ^ k
      = (intIdealToNil.{u} k).toRingHom ((2 : (intIdealPair.{u}).ring) ^ k) := by
        rw [map_pow, intIdealToNil_two]
    _ = 0 := PresheafOfModules.injective_of_mono ι (nilTwoPair.{u} k).ix
        (hzeroQ.trans (map_zero _).symm)

/-- **The fraction `ε / 2` is not in the image of the localization map**, where `ε = ι(1)` is the
image of the unit section at `(ℤ, 2ℤ)` under a monomorphism `ι : 𝒪 ⟶ J` of pair-modules. -/
theorem notMem_range_mkLinearMap_value {J : PairModule.{u}} (ι : structureModule.{u} ⟶ J)
    [Mono ι] :
    LocalizedModule.mk
        (PresheafOfModules.Hom.app ι (intIdealPair.{u}).ix (1 : (intIdealPair.{u}).ring))
        ⟨(2 : (intIdealPair.{u}).ring), Submonoid.mem_powers _⟩ ∉
      Set.range (LocalizedModule.mkLinearMap
        (Submonoid.powers (2 : (intIdealPair.{u}).ring)) (J.value intIdealPair.{u})) := by
  rintro ⟨m, hm⟩
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq] at hm
  obtain ⟨w, hw⟩ := hm
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 w.2
  refine ne_zero_pow_smul_sub_app_one ι m j ?_
  rw [smul_sub, sub_eq_zero, hj]
  simpa only [Submonoid.smul_def, one_smul] using hw

/-- **The localization map on the sections at `(ℤ, 2ℤ)` is not surjective.** Equivalently
`H¹_{2ℤ}(J(ℤ, 2ℤ)) ≠ 0`: the sections at `(ℤ, 2ℤ)` of a pair-module receiving a monomorphism from
the structure presheaf are never `Γ_{2ℤ}`-acyclic. -/
theorem not_surjective_mkLinearMap_value {J : PairModule.{u}} (ι : structureModule.{u} ⟶ J)
    [Mono ι] :
    ¬ Function.Surjective (LocalizedModule.mkLinearMap
      (Submonoid.powers (2 : (intIdealPair.{u}).ring)) (J.value intIdealPair.{u})) := fun hsurj =>
  notMem_range_mkLinearMap_value ι (hsurj _)

/-! ### The repair fails -/

/-- **The structure presheaf of pairs does not embed into a pair-module whose sections are
`Γ_I`-acyclic.** Every resolution `0 ⟶ 𝒪 ⟶ J⁰ ⟶ J¹ ⟶ ⋯` begins with a monomorphism `𝒪 ⟶ J⁰`, so
there is no `Γ_I`-acyclic resolution of the structure presheaf at all, bounded below or not.

The hypothesis is used only at the pair `(ℤ, 2ℤ)` and only for the generator `2` of its ideal;
every spelling of "the local cohomology of `J(P)` vanishes in positive degrees" implies it, since
for a principal ideal `(g)` the extended Čech complex is the two term complex `N ⟶ N_g` whose
cokernel is `H¹_{(g)}(N)`. -/
theorem not_exists_mono_surjective_value :
    ¬ ∃ (J : PairModule.{u}) (ι : structureModule.{u} ⟶ J), Mono ι ∧
      ∀ (P : Pair.{u}) (g : P.ring), Ideal.span {g} = P.ideal →
        Function.Surjective
          (LocalizedModule.mkLinearMap (Submonoid.powers g) (J.value P)) := by
  rintro ⟨J, ι, hmono, hacyclic⟩
  exact not_surjective_mkLinearMap_value ι
    (hacyclic intIdealPair.{u} 2 span_two_intIdealPair.{u})

/-- **There is no complex of pair-modules, strictly bounded below by `0` and quasi-isomorphic to
`𝒪[0]`, whose sections at every pair are `Γ_I`-acyclic in every degree.** This is the repair of
the refuted step of [Stacks, Tag 099D] in the shape in which it would have been used: the rest of
Step 3 needs only that `𝒥•(U)` be a bounded below `Γ_I`-acyclic resolution of `A` rather than an
injective one, and the Cartan–Eilenberg comparison would then put `ℱ•(U) = Γ_I(𝒥•(U))` in the
place that [Stacks, Tag 0952] gives to the torsion subcomplex of an injective resolution. It is
unavailable.

The quasi-isomorphism and the strict bound force `𝒪 ⟶ 𝒥⁰` to be a monomorphism, and
`Stacks.PairSite.not_exists_mono_surjective_value` applies. -/
theorem not_exists_resolution_surjective_value :
    ¬ ∃ (J : CochainComplex PairModule.{u} ℤ) (ι : structureSingle.{u} ⟶ J), QuasiIso ι ∧
      J.IsStrictlyGE 0 ∧ ∀ (P : Pair.{u}) (n : ℤ) (g : P.ring), Ideal.span {g} = P.ideal →
        Function.Surjective
          (LocalizedModule.mkLinearMap (Submonoid.powers g) ((J.X n).value P)) := by
  rintro ⟨J, ι, hqi, hGE, hacyclic⟩
  have hmono : Mono (ι.f 0) :=
    CochainComplex.FilteredInjective.TermwiseSplit.mono_f_zero_of_quasiIso ι
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 structureModule.{u} 1
        one_ne_zero)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 structureModule.{u} (-1)
        (by decide))
      (J.isZero_of_isStrictlyGE 0 (-1))
  exact not_exists_mono_surjective_value.{u}
    ⟨J.X 0, (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 structureModule.{u}).inv ≫
      ι.f 0, inferInstance, fun P g hg => hacyclic P 0 g hg⟩

/-! ### The repair in the local cohomology spelling -/

section LocalCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **`Γ_{(g)}`-acyclicity gives a surjective localization map.** If the first local cohomology of
`N` with support in `V(g)` vanishes then `N ⟶ N[1/g]` is surjective: over a Noetherian ring that
cohomology module *is* the cokernel of the localization map
(`Stacks.LocalCohomology.nonempty_principalSupport_firstCohomology_iso_cokernel`). -/
theorem surjective_mkLinearMap_of_isZero_localCohomology {A : Type u} [CommRing A]
    [IsNoetherianRing A] (g : A) (N : ModuleCat.{u} A)
    (h : IsZero (LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      (PrimeSpectrum.zeroLocus ({g} : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) 1)) :
    Function.Surjective (LocalizedModule.mkLinearMap (Submonoid.powers g) N) := by
  obtain ⟨e⟩ :=
    LocalCohomology.nonempty_principalSupport_firstCohomology_iso_cokernel.{u, u} A g N
  exact (ModuleCat.epi_iff_surjective _).1
    ((Preadditive.epi_iff_isZero_cokernel _).2 (IsZero.of_iso h e.symm))

/-- **There is no complex of pair-modules, strictly bounded below by `0` and quasi-isomorphic to
`𝒪[0]`, whose sections have vanishing local cohomology in positive degrees at every pair.** This is
`Stacks.PairSite.not_exists_resolution_surjective_value` with the hypothesis in the library's local
cohomology spelling: the refuted repair of Step 3 of [Stacks, Tag 099D] as the source's argument
would have used it, with "resolution of `A` by injective `A`-modules" weakened all the way to
"`Γ_I`-acyclic resolution of `A`".

The rings of pairs are Noetherian, so the support flavour `RΓ_{V(I)}` used here and the
power-torsion flavour `RΓ_I` of [Stacks, Tag 0952] agree
(`Dualizing.derivedPowerTorsionObjIsoLocalCohomologyObj`); the hypothesis is used only in
degree `1` and only at the pair `(ℤ, 2ℤ)`. -/
theorem not_exists_resolution_isZero_localCohomology :
    ¬ ∃ (J : CochainComplex PairModule.{u} ℤ) (ι : structureSingle.{u} ⟶ J), QuasiIso ι ∧
      J.IsStrictlyGE 0 ∧ ∀ (P : Pair.{u}) (n i : ℤ), 0 < i →
        IsZero (LocalCohomology.localCohomologyWithSupportIn.{u, u} P.ring
          (PrimeSpectrum.zeroLocus ((P.ideal : Ideal P.ring) : Set P.ring))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).obj ((J.X n).value P)) i) := by
  rintro ⟨J, ι, hqi, hGE, hvanish⟩
  refine not_exists_resolution_surjective_value.{u} ⟨J, ι, hqi, hGE, fun P n g hg => ?_⟩
  have h1 := hvanish P n 1 one_pos
  rw [← hg, PrimeSpectrum.zeroLocus_span] at h1
  exact surjective_mkLinearMap_of_isZero_localCohomology g ((J.X n).value P) h1

end LocalCohomology

end Stacks.PairSite

end
