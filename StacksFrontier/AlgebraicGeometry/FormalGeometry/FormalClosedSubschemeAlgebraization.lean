module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.ClosedImmersionInfinitesimal

/-!
# Algebraization of a formal system of closed subschemes

**Stacks 0899.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, write
`S = Spec A` and `Sₙ = Spec (A / Iⁿ)`, and let `f : X ⟶ S` be separated of finite type. Put
`Xₙ = X ×_S Sₙ`. Given a commutative diagram

```
  Z₁ --> Z₂ --> Z₃ --> ⋯
  |      |      |
  X₁ -i₁-> X₂ -i₂-> X₃ --> ⋯
```

with *cartesian* squares in which `Z₁ ⟶ X₁` is a closed immersion and `Z₁ ⟶ S₁` is proper, there
is a closed immersion `Z ⟶ X` with `Zₙ = Z ×_S Sₙ`; moreover `Z` is proper over `S`.

Note the asymmetry: `f` itself is only separated of finite type, and it is the *closed member*
`Z₁ ⟶ S₁` of the system that is assumed proper.

## The two inputs of the proof

The source deduces 0899 from Grothendieck's existence theorem. The theorem of this file names the
two consequences of it that the proof needs as predicates, and both are proved downstream over a
complete Noetherian base:

* `AlgebraicGeometry.AdicFiniteSystemAlgebraization` is **Stacks 09ZT** for the morphism `f`: a
  cartesian system of *finite* morphisms over the `Xₙ` whose closed member is proper over `S₁` is
  the system of adic base changes of a single scheme `Z` over `X` proper over `S`. It is proved by
  `AlgebraicGeometry.adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization` applied to
  `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds`.
* `AlgebraicGeometry.AdicMorphismRigidity` is the uniqueness clause of **Stacks 0A42**: two
  morphisms over `S` from a proper scheme to a separated scheme of finite type with the same adic
  base changes are equal. It is proved by `AlgebraicGeometry.adicMorphismRigidity`.

Stacks 0899 with both inputs discharged is
`AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback_holds`, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicFiniteAlgebraizationTags.lean`,
which carries the tag.

Everything else is proved: that *every* member of the system is a closed immersion (hence finite,
which is what feeds 09ZT), that the algebraizing morphism `Z ⟶ X` is a monomorphism and hence a
closed immersion, and that the whole diagram — the transition maps `Zₙ ⟶ Z_{n+1}` included — is
recovered by base change.

## Main definitions

* `AlgebraicGeometry.AdicFiniteSystemAlgebraization`,
  `AlgebraicGeometry.AdicMorphismRigidity` — the two predicates described above.

## Main results

* `AlgebraicGeometry.isClosedImmersion_adicThickeningSucc`,
  `AlgebraicGeometry.bijective_base_adicThickeningSucc`,
  `AlgebraicGeometry.finitePresentation_adicThickeningSucc` and their base-changed companions —
  the transition maps of the adic systems are closed immersions which are bijective on points and
  of finite presentation.
* `AlgebraicGeometry.isClosedImmersion_of_isPullback_adicBaseChangeSucc` — in a cartesian system
  over the `Xₙ`, if the first member is a closed immersion then so is every member.
* `AlgebraicGeometry.hom_ext_adicThickening_of_isPullback`,
  `AlgebraicGeometry.mono_of_adicBaseChange_isClosedImmersion` — the algebraizing morphism is a
  monomorphism.
* `AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback` — Stacks 0899 from the
  two predicates above.

## Implementation notes

Positive powers `Iⁿ` are indexed by `ℕ` through `n ↦ I ^ (n + 1)`, as in
`StacksFrontier.AlgebraicGeometry.Algebraization`, so the index `n` here is the source's `n + 1`.
Following Mathlib, "of finite type" is `LocallyOfFiniteType` together with `QuasiCompact`.

That every `jₙ : Zₙ ⟶ Xₙ` is a closed immersion is proved by induction using Stacks 0896
(`AlgebraicGeometry.isClosedImmersion_of_infinitesimal_baseChange`): the transition map
`Xₙ ⟶ X_{n+1}` is a closed immersion which is bijective on points, because the kernel of
`A / I ^ (n + 2) → A / I ^ (n + 1)` is square zero, and it is of finite presentation because `A`
is Noetherian.

Monomorphy of the algebraized `g : Z ⟶ X` is proved through its kernel pair: `Z ×_X Z` is proper
over `S`, the two projections have equal adic base changes because each `jₙ` is a
monomorphism, and so they agree by rigidity.

## References

* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0896](https://stacks.math.columbia.edu/tag/0896)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The map `A ⧸ I ^ (n + 2) → A ⧸ I ^ (n + 1)` is surjective. -/
private theorem surjective_factorPow_succ (n : ℕ) :
    Function.Surjective (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) :=
  Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- The transition map between consecutive adic thickenings is a closed immersion. -/
public instance isClosedImmersion_adicThickeningSucc (n : ℕ) :
    IsClosedImmersion (adicThickeningSucc A I n) := by
  rw [adicThickeningSucc]
  exact IsClosedImmersion.spec_of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))

/-- The kernel of `A ⧸ I ^ (n + 2) → A ⧸ I ^ (n + 1)` is a square-zero ideal, hence consists
of nilpotent elements. -/
public lemma ker_factorPow_le_nilradical (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) ≤
      nilradical (A ⧸ I ^ (n + 2)) := by
  have hker : RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) =
      (I ^ (n + 1)).map (Ideal.Quotient.mk (I ^ (n + 2))) :=
    Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  have hsq : ((I ^ (n + 1)).map (Ideal.Quotient.mk (I ^ (n + 2)))) ^ 2 = ⊥ := by
    rw [pow_two, ← Ideal.map_mul]
    refine Ideal.map_mk_eq_bot_of_le ?_
    calc I ^ (n + 1) * I ^ (n + 1) = I ^ ((n + 1) + (n + 1)) := (pow_add I _ _).symm
      _ ≤ I ^ (n + 2) := Ideal.pow_le_pow_right (by omega)
  rw [hker]
  intro x hx
  have hx2 : x ^ 2 ∈ ((I ^ (n + 1)).map (Ideal.Quotient.mk (I ^ (n + 2)))) ^ 2 :=
    Ideal.pow_mem_pow hx 2
  rw [hsq, Ideal.mem_bot] at hx2
  exact ⟨2, hx2⟩

/-- The transition map between consecutive adic thickenings is bijective on points: it is the
spectrum of a surjective ring map with square-zero kernel. -/
public lemma bijective_base_adicThickeningSucc (n : ℕ) :
    Function.Bijective (adicThickeningSucc A I n).base := by
  change Function.Bijective
    (PrimeSpectrum.comap (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))
  refine (PrimeSpectrum.isHomeomorph_comap _ (fun x => ?_)
    (ker_factorPow_le_nilradical A I n)).bijective
  obtain ⟨y, hy⟩ := surjective_factorPow_succ A I n x
  exact ⟨1, by norm_num, y, by simpa using hy⟩

/-- The transition maps between consecutive adic thickenings are surjective on points. -/
public instance surjective_adicThickeningSucc (n : ℕ) :
    Surjective (adicThickeningSucc A I n) :=
  ⟨(bijective_base_adicThickeningSucc A I n).2⟩

/-- The transition map between consecutive adic thickenings is of finite presentation: it is
the spectrum of a surjective map of Noetherian rings. -/
public lemma finitePresentation_adicThickeningSucc [IsNoetherianRing A] (n : ℕ) :
    FinitePresentation (adicThickeningSucc A I n) := by
  refine ⟨?_, inferInstance, inferInstance⟩
  rw [adicThickeningSucc, LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.FinitePresentation.of_finiteType.1
    (RingHom.FiniteType.of_surjective _ (surjective_factorPow_succ A I n))

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The transition map between consecutive adic base changes is a closed immersion. -/
public instance isClosedImmersion_adicBaseChangeSucc (n : ℕ) :
    IsClosedImmersion (adicBaseChangeSucc A I f n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_adicBaseChangeSucc A I f n).flip inferInstance

/-- The transition map between consecutive adic base changes is surjective on points. -/
public instance surjective_adicBaseChangeSucc (n : ℕ) :
    Surjective (adicBaseChangeSucc A I f n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_adicBaseChangeSucc A I f n).flip inferInstance

/-- The transition map between consecutive adic base changes is bijective on points. -/
public lemma bijective_base_adicBaseChangeSucc (n : ℕ) :
    Function.Bijective (adicBaseChangeSucc A I f n).base :=
  ⟨(adicBaseChangeSucc A I f n).isClosedEmbedding.injective,
    (adicBaseChangeSucc A I f n).surjective⟩

/-- The transition map between consecutive adic base changes is of finite presentation. -/
public lemma finitePresentation_adicBaseChangeSucc [IsNoetherianRing A] (n : ℕ) :
    FinitePresentation (adicBaseChangeSucc A I f n) := by
  obtain ⟨hlfp, hqc, hqs⟩ := finitePresentation_adicThickeningSucc A I n
  have key : ∀ {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange],
      P (adicThickeningSucc A I n) → P (adicBaseChangeSucc A I f n) := fun h =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_adicBaseChangeSucc A I f n).flip h
  exact ⟨key (P := @LocallyOfFinitePresentation) hlfp, key (P := @QuasiCompact) hqc,
    key (P := @QuasiSeparated) hqs⟩

/-- The transition map between consecutive adic base changes is a morphism over `X`. -/
@[reassoc]
public lemma adicBaseChangeSucc_fst (n : ℕ) :
    adicBaseChangeSucc A I f n ≫ pullback.fst f (adicThickeningι A I (n + 1)) =
      pullback.fst f (adicThickeningι A I n) := by
  rw [adicBaseChangeSucc, pullback.lift_fst]

/-! ### Every member of a cartesian system of closed subschemes is a closed immersion -/

/-- **Stacks 0899, first step.** In a system of morphisms `jₙ : Zₙ ⟶ Xₙ` over the adic base
changes of `f` whose squares are cartesian, if the first member `j 0` is a closed immersion then
so is every member.

The transition map `Xₙ ⟶ X_{n+1}` is a closed immersion, bijective on points and of finite
presentation, and the base change of `j (n + 1)` along it is `j n`; so Stacks 0896 applies. -/
public lemma isClosedImmersion_of_isPullback_adicBaseChangeSucc [IsNoetherianRing A]
    {Z : ℕ → Scheme.{u}} (j : ∀ n, Z n ⟶ adicBaseChange A I f n) (t : ∀ n, Z n ⟶ Z (n + 1))
    (hcart : ∀ n, IsPullback (t n) (j n) (j (n + 1)) (adicBaseChangeSucc A I f n))
    (hclosed : IsClosedImmersion (j 0)) (n : ℕ) : IsClosedImmersion (j n) := by
  induction n with
  | zero => exact hclosed
  | succ n ih =>
    have heq : (hcart n).isoPullback.inv ≫ j n =
        pullback.snd (j (n + 1)) (adicBaseChangeSucc A I f n) :=
      (Iso.inv_comp_eq _).2 (hcart n).isoPullback_hom_snd.symm
    have : IsClosedImmersion (pullback.snd (j (n + 1)) (adicBaseChangeSucc A I f n)) := by
      rw [← heq]
      have := ih
      infer_instance
    exact isClosedImmersion_of_infinitesimal_baseChange (j (n + 1))
      (adicBaseChangeSucc A I f n) (bijective_base_adicBaseChangeSucc A I f n)
      (Or.inr (finitePresentation_adicBaseChangeSucc A I f n))

/-! ### The two inputs of the proof -/

/-- **Stacks 09ZT for the morphism `f`.** Let `f : X ⟶ Spec A` be separated of finite type and let
`(Zₙ)` be a system of schemes finite over the adic base changes `Xₙ = X ×_{Spec A} Sₙ`, cartesian
over the transition maps `Xₙ ⟶ X_{n+1}`, whose first member is proper over `S₀`. Then the system
is the system of adic base changes of a single scheme `Z` finite over `X` and proper over
`Spec A`: there are maps `kₙ : Zₙ ⟶ Z` exhibiting each `Zₙ` as `Z ×_{Spec A} Sₙ` compatibly with
the morphisms to `X`.

This is where Grothendieck's existence theorem enters the existence half of Stacks 0899. Over a
complete Noetherian base it is proved by
`AlgebraicGeometry.adicFiniteSystemAlgebraization_of_adicFiniteAlgebraAlgebraization` applied to
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds`. -/
public def AdicFiniteSystemAlgebraization : Prop :=
  ∀ (Z : ℕ → Scheme.{u}) (j : ∀ n, Z n ⟶ adicBaseChange A I f n) (t : ∀ n, Z n ⟶ Z (n + 1)),
    (∀ n, IsPullback (t n) (j n) (j (n + 1)) (adicBaseChangeSucc A I f n)) →
    (∀ n, IsFinite (j n)) →
    IsProper (j 0 ≫ pullback.snd f (adicThickeningι A I 0)) →
    ∃ (W : Scheme.{u}) (g : W ⟶ X) (k : ∀ n, Z n ⟶ W), IsFinite g ∧ IsProper (g ≫ f) ∧
      (∀ n, IsPullback (k n) (j n ≫ pullback.snd f (adicThickeningι A I n)) (g ≫ f)
        (adicThickeningι A I n)) ∧
      ∀ n, k n ≫ g = j n ≫ pullback.fst f (adicThickeningι A I n)

/-- **The uniqueness clause of Stacks 0A42.** Two morphisms over `Spec A` from a scheme proper
over `Spec A` to a scheme separated of finite type over `Spec A` whose base changes to every adic
thickening agree are equal.

This is what the proof of Stacks 0899 needs in order to know that the algebraized morphism is a
monomorphism. Over a complete Noetherian base it is proved by
`AlgebraicGeometry.adicMorphismRigidity`. -/
public def AdicMorphismRigidity : Prop :=
  ∀ {P W : Scheme.{u}} (fP : P ⟶ Spec (.of A)) (fW : W ⟶ Spec (.of A)),
    IsProper fP → IsSeparated fW → LocallyOfFiniteType fW → QuasiCompact fW →
    ∀ (a : P ⟶ W) (ha : a ≫ fW = fP) (b : P ⟶ W) (hb : b ≫ fW = fP),
      (∀ n, adicBaseChangeMap A I a ha n = adicBaseChangeMap A I b hb n) → a = b

/-! ### The algebraizing morphism is a monomorphism -/

/-- **Cancelling the algebraizing morphism at a single thickening.** Suppose `jₙ : Zₙ ⟶ Xₙ` is a
closed immersion and `kₙ : Zₙ ⟶ W` exhibits `Zₙ` as `W ×_{Spec A} Sₙ` compatibly with
`g : W ⟶ X`. Then two morphisms `p, q : T ⟶ W` that factor through `Sₙ` in the same way and agree
after `g` are equal: they lift to `Zₙ`, and the lifts agree because `jₙ` is a monomorphism. -/
public lemma hom_ext_adicThickening_of_isPullback {W : Scheme.{u}} (g : W ⟶ X) (n : ℕ)
    {Zn : Scheme.{u}} (jn : Zn ⟶ adicBaseChange A I f n) (hjn : IsClosedImmersion jn)
    (kn : Zn ⟶ W)
    (hcart : IsPullback kn (jn ≫ pullback.snd f (adicThickeningι A I n)) (g ≫ f)
      (adicThickeningι A I n))
    (hkg : kn ≫ g = jn ≫ pullback.fst f (adicThickeningι A I n))
    {T : Scheme.{u}} (p q : T ⟶ W) (β : T ⟶ adicThickening A I n)
    (hp : p ≫ g ≫ f = β ≫ adicThickeningι A I n)
    (hq : q ≫ g ≫ f = β ≫ adicThickeningι A I n) (hpq : p ≫ g = q ≫ g) : p = q := by
  have hmono : Mono jn := ((IsClosedImmersion.iff_isFinite_and_mono jn).1 hjn).2
  have hpk := hcart.lift_fst p β hp
  have hps := hcart.lift_snd p β hp
  have hqk := hcart.lift_fst q β hq
  have hqs := hcart.lift_snd q β hq
  have hlift : hcart.lift p β hp ≫ jn = hcart.lift q β hq ≫ jn := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [← hkg, ← Category.assoc, ← Category.assoc, hpk, hqk]
      exact hpq
    · simp only [Category.assoc]
      rw [hps, hqs]
  calc p = hcart.lift p β hp ≫ kn := hpk.symm
    _ = hcart.lift q β hq ≫ kn := by rw [(cancel_mono jn).1 hlift]
    _ = q := hqk

/-- **Stacks 0899, second step.** A morphism `g : W ⟶ X`, with `W` proper over `Spec A`, whose
adic base changes are the members of a cartesian system of closed immersions `jₙ : Zₙ ⟶ Xₙ`, is a
monomorphism.

The argument is applied to the kernel pair `W ×_X W`, which is proper over `Spec A`; its two
projections have the same base change to every thickening by
`AlgebraicGeometry.hom_ext_adicThickening_of_isPullback`, hence agree by rigidity. -/
public lemma mono_of_adicBaseChange_isClosedImmersion (hrig : AdicMorphismRigidity A I)
    {W : Scheme.{u}} (g : W ⟶ X) [IsProper g] [IsProper (g ≫ f)]
    {Z : ℕ → Scheme.{u}} (j : ∀ n, Z n ⟶ adicBaseChange A I f n)
    (hclosed : ∀ n, IsClosedImmersion (j n)) (k : ∀ n, Z n ⟶ W)
    (hcart : ∀ n, IsPullback (k n) (j n ≫ pullback.snd f (adicThickeningι A I n)) (g ≫ f)
      (adicThickeningι A I n))
    (hkg : ∀ n, k n ≫ g = j n ≫ pullback.fst f (adicThickeningι A I n)) : Mono g := by
  have hw : pullback.snd g g ≫ g ≫ f = pullback.fst g g ≫ g ≫ f := by
    rw [← Category.assoc, ← Category.assoc, pullback.condition]
  have hfst : pullback.fst g g = pullback.snd g g := by
    refine hrig (pullback.fst g g ≫ g ≫ f) (g ≫ f) inferInstance inferInstance inferInstance
      inferInstance (pullback.fst g g) rfl (pullback.snd g g) hw fun n => ?_
    apply pullback.hom_ext
    · rw [adicBaseChangeMap, adicBaseChangeMap, pullback.lift_fst, pullback.lift_fst]
      refine hom_ext_adicThickening_of_isPullback A I f g n (j n) (hclosed n) (k n) (hcart n)
        (hkg n) _ _ (pullback.snd (pullback.fst g g ≫ g ≫ f) (adicThickeningι A I n)) ?_ ?_ ?_
      · rw [Category.assoc]
        exact pullback.condition
      · rw [Category.assoc, hw]
        exact pullback.condition
      · simp only [Category.assoc]
        rw [pullback.condition]
    · rw [adicBaseChangeMap, adicBaseChangeMap, pullback.lift_snd, pullback.lift_snd]
  exact IsKernelPair.mono_of_eq_fst_snd (IsPullback.of_hasPullback g g) hfst

/-! ### Stacks 0899 -/

/-- **Stacks Project, Tag 0899.** Let `A` be a Noetherian ring complete with respect to an ideal
`I`, write `S = Spec A` and `Sₙ = Spec (A / Iⁿ)`, and let `f : X ⟶ S` be separated of finite type.
Put `Xₙ = X ×_S Sₙ`. Suppose given a system of morphisms `jₙ : Zₙ ⟶ Xₙ` together with transition
maps `tₙ : Zₙ ⟶ Z_{n+1}` making every square

```
  Zₙ --tₙ--> Z_{n+1}
  |            |
  Xₙ --iₙ--> X_{n+1}
```

cartesian, and assume that `j 0 : Z₀ ⟶ X₀` is a closed immersion and that `Z₀ ⟶ S₀` is proper.
Then there is a closed immersion `g : Z ⟶ X` with `Z` proper over `S` which recovers the given
system by base change: each `Zₙ` is `Z ×_S Sₙ`, the morphism `Zₙ ⟶ X` is `jₙ` followed by the
projection `Xₙ ⟶ X`, and the transition maps `tₙ` are compatible with the identifications.

The hypotheses are the source's: `f` is only separated of finite type, and it is the closed member
`Z₀ ⟶ S₀` of the system, not `f`, that is proper.

The proof is the source's. Stacks 0896 upgrades the closed immersion `j 0` to a closed immersion
`jₙ` for every `n` (`isClosedImmersion_of_isPullback_adicBaseChangeSucc`); each `jₙ` is therefore
finite, so Stacks 09ZT, in the form `halg`, algebraizes the system to a finite `g : Z ⟶ X` with
`Z` proper over `S`; and `g` is a monomorphism, hence a closed immersion, by rigidity, in the form
`hrig`, the uniqueness clause of Stacks 0A42. Both `halg` and `hrig` are proved over a complete
Noetherian base, and the statement with them discharged is
`AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback_holds`, which carries the
tag. `IsNoetherianRing A` is moreover used directly, to see that the transition maps of the adic
system are of finite presentation. -/
public theorem exists_closedImmersion_algebraization_of_isPullback [IsNoetherianRing A]
    (hcomplete : IsAdicComplete I A) (halg : AdicFiniteSystemAlgebraization A I f)
    (hrig : AdicMorphismRigidity A I) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : ℕ → Scheme.{u}) (j : ∀ n, Z n ⟶ adicBaseChange A I f n) (t : ∀ n, Z n ⟶ Z (n + 1))
    (hcart : ∀ n, IsPullback (t n) (j n) (j (n + 1)) (adicBaseChangeSucc A I f n))
    (hclosed : IsClosedImmersion (j 0))
    (hproper : IsProper (j 0 ≫ pullback.snd f (adicThickeningι A I 0))) :
    ∃ (W : Scheme.{u}) (g : W ⟶ X) (k : ∀ n, Z n ⟶ W),
      IsClosedImmersion g ∧ IsProper (g ≫ f) ∧
      (∀ n, IsPullback (k n) (j n ≫ pullback.snd f (adicThickeningι A I n)) (g ≫ f)
        (adicThickeningι A I n)) ∧
      (∀ n, k n ≫ g = j n ≫ pullback.fst f (adicThickeningι A I n)) ∧
      ∀ n, t n ≫ k (n + 1) = k n := by
  have := hcomplete
  have hclosed_all : ∀ n, IsClosedImmersion (j n) :=
    isClosedImmersion_of_isPullback_adicBaseChangeSucc A I f j t hcart hclosed
  obtain ⟨W, g, k, hfinite_g, hproper_g, hkcart, hkg⟩ :=
    halg Z j t hcart (fun n => have := hclosed_all n; inferInstance) hproper
  have : IsFinite g := hfinite_g
  have : IsProper (g ≫ f) := hproper_g
  have hmono : Mono g :=
    mono_of_adicBaseChange_isClosedImmersion A I f hrig g j hclosed_all k hkcart hkg
  refine ⟨W, g, k, (IsClosedImmersion.iff_isFinite_and_mono g).2 ⟨hfinite_g, hmono⟩, hproper_g,
    hkcart, hkg, fun n => ?_⟩
  refine (cancel_mono g).1 ?_
  rw [Category.assoc, hkg (n + 1), hkg n, ← Category.assoc, (hcart n).w, Category.assoc,
    adicBaseChangeSucc_fst]

end AlgebraicGeometry

end
