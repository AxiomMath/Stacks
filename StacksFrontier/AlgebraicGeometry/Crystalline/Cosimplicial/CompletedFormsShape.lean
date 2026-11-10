module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelForms
public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod
public import StacksFrontier.LinearAlgebra.ExteriorPower.ScalarTower
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow

/-!
# The two shapes of the completed forms, level by level

[Stacks, Lemma 60.19.1, Tag 07LA] — `Crystalline.id_completedTensorCompletedForms_homotopic_zero`
— is about `Ωⁱ_{D(n)}` read as the completion of the `i`-th exterior power of the **completed**
differentials, `⋀ⁱ_{D̂} Ω̂`.  The forms of the bigraded family
`Crystalline.CosimplicialDPAlgebra.forms`, and so the forms of the target complex
`M ⊗^∧_D Ω^*_D` of [Stacks, Proposition 60.21.3, Tag 07LG] as
`Crystalline.completedDividedPowerDeRhamComplex` builds them, are instead the completion of the
`i`-th exterior power of the **uncompleted** differentials, `⋀ⁱ_B Ω`.  Nothing in this library
identified the two; see the module documentation of `Cosimplicial/BigradedForms.lean` and the
`hcolumns` entry of `Crystalline/Computes07LGFromDoubleComplex.lean`.  Stripped of the divided
power vocabulary the identification wanted is, for a ring `B`, an ideal `I` of `B` and a
`B`-module `N`,

`AdicCompletion_B (⋀ⁱ_B N) ≃ AdicCompletion_{B̂} (⋀ⁱ_{B̂} N̂)`,

and this module builds and pins it down, for `I` finitely generated and `i > 0`, level by level:
the level `k` step is

`(⋀ⁱ_B N) ⧸ Iᵏ ≃ (⋀ⁱ_{B̂} N̂) ⧸ (I B̂)ᵏ`,

these steps commute with the transition maps, and the completion is the limit of its levels.

## Why it is true, and where `i > 0` enters

Both sides are exterior powers of the one module `N ⧸ Iᵏ · N`, over the two level rings `B ⧸ Iᵏ`
and `B̂ ⧸ (I B̂)ᵏ`:

* `Crystalline.exteriorPowerQuotSmulTopEquiv` reduces each side to an exterior power over its own
  level ring.  It is two applications of `Crystalline.isBaseChange_mkQ_smulTop` — once in degree
  one, carried up by `Crystalline.isBaseChange_exteriorPowerMapOfBaseChange`, and once on the
  exterior power itself — so it needs no hypothesis at all, in particular none on `i`.
* `AdicCompletion.quotPowSMulTopEquiv`, which is [Stacks, Tag 05GG] and is where the finite
  generation of `I` is used, identifies the two modules: `N̂ ⧸ Iᵏ ≃ N ⧸ Iᵏ`.  That the quotient
  of `N̂` by `Iᵏ` taken over `B` and by `(I B̂)ᵏ` taken over `B̂` is the same quotient is
  `Crystalline.smul_top_pow_restrictScalars`.
* The two level rings are cleared away by `exteriorPower.towerEquiv`, which compares `⋀ⁱ_B` with
  `⋀ⁱ_S` on one and the same module for a **surjective** `B → S`.  For `B → B ⧸ Iᵏ` that is the
  quotient map; for `B → B̂ ⧸ (I B̂)ᵏ` it is
  `Crystalline.surjective_algebraMap_adicCompletion_quotient`.  `exteriorPower.towerEquiv`
  assumes `0 < i` and genuinely needs it — in degree zero the comparison *is* the ring map
  `B → S`, by `exteriorPower.zeroEquiv_towerMap` — and this is the only place the degree
  hypothesis is used.  It costs nothing here: [Stacks, Tag 07LA] is itself stated for `i > 0`.

No flatness, no finiteness of `N` and no noetherian hypothesis appears.  The route through
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, which would describe `N̂` as a base
change of `N`, would need both and is not taken.

## Main definitions

* `Crystalline.exteriorPowerQuotSmulTopEquiv` — **exterior powers commute with reduction modulo
  an ideal**: `(⋀ⁱ_R N) ⧸ K ≃ ⋀ⁱ_{R ⧸ K} (N ⧸ K · N)`, in every degree.
* `Crystalline.adicQuotLevelEquiv` — [Stacks, Tag 05GG] with the quotient of `N̂` taken over the
  completed ring.
* `Crystalline.completedFormsShapeLevelEquiv` — **the level `k` comparison of the two shapes**.
* `Crystalline.adicCompletionEquivOfLevels` — an identification of two adic completions out of
  compatible identifications of their levels.
* `Crystalline.completedFormsShapeEquiv` — **the comparison of the two shapes**,
  `AdicCompletion_B (⋀ⁱ_B N) ≃+ AdicCompletion_{B̂} (⋀ⁱ_{B̂} N̂)`.

## Main results

* `Crystalline.smul_top_pow_restrictScalars` and
  `Crystalline.quotSmulTopPowRestrictEquiv` — `Iᵏ · M` computed over `R` and `(I S)ᵏ · M`
  computed over an `R`-algebra `S` are the same submodule, and the two quotients are the same
  quotient.
* `Crystalline.surjective_algebraMap_adicCompletion_quotient` — **`R → R̂ ⧸ (I R̂)ᵏ` is
  surjective**, which is what lets `exteriorPower.towerEquiv` be applied over the completed
  level ring.
* `Crystalline.completedFormsShapeLevelEquiv_mk_ιMulti` — **the equation pinning the level
  comparison down**: the class of `ω₁ ∧ ⋯ ∧ ωᵢ` goes to the class of the wedge, formed over `B̂`,
  of the images of the `ωⱼ` in `N̂`.  Those classes span the source, so no second identification
  satisfies it.  `Crystalline.exteriorPowerQuotSmulTopEquiv_mk_ιMulti` and
  `Crystalline.adicQuotLevelEquiv_mk_of` are the same for the two halves.
* `Crystalline.quotSmulTop_exteriorPower_hom_ext` — two maps out of a reduction of an exterior
  power agreeing on the classes of wedges are equal, which is what makes the pinning equations
  determine the comparisons.
* `Crystalline.transitionMap_completedFormsShapeLevelEquiv` — **the level comparisons commute
  with the transition maps**, which is what lets them be assembled.
* `Crystalline.completedFormsShapeEquiv_of_ιMulti` — the assembled comparison on a wedge.

## What is and is not proved

Everything stated is proved, under no hypothesis beyond `I.FG` and `0 < i`.  **No tag attribute
is placed**: this is one identification inside the proof of [Stacks, Tag 07LG] and is not a
clause of any tag's statement.

Two things about the comparison are **not** here, and both are proved in the two modules built
on this one.

`Crystalline.completedFormsShapeEquiv` is built as an **additive** equivalence: the two
completions are modules over `B̂` — the right one along the identity of `B̂`, the left one along
`AdicCompletion.module` — and that the comparison respects those actions is not proved here.  It
is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShapeLinear.lean`, as
`Crystalline.completedFormsShapeEquiv_smul`, and the comparison is upgraded there to the
`B̂`-linear `Crystalline.completedFormsShapeLinearEquiv`.

And nothing is said here about **naturality in `B`**.  [Stacks, Tag 07LA] is a statement about a
cosimplicial module over `Crystalline.CosimplicialEnvelope.ring`, and transporting its null
homotopy along the comparison needs the comparison to be a morphism of cosimplicial modules,
hence to commute with the transition maps `D(m) → D(n)` of the cosimplicial envelope — in the
semilinear shape of `Crystalline.adicCompletionMapₛₗ`.  That is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShapeNatural.lean`, as
`Crystalline.completedFormsShapeEquiv_natural`.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public section

open scoped TensorProduct

namespace Crystalline

/-! ### Reduction modulo a power of an ideal, over the base and over an algebra -/

section Levels

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- `Iᵏ • ⊤` on a module over an `R`-algebra `S`, computed over `R`, is `(I S)ᵏ • ⊤` computed
over `S`. -/
public theorem smul_top_pow_restrictScalars (I : Ideal R) (k : ℕ) :
    ((I.map (algebraMap R S) ^ k • (⊤ : Submodule S M)).restrictScalars R) =
      I ^ k • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

/-- The reduction of a module over an `R`-algebra `S` modulo `Iᵏ`, formed over `R` and formed
over `S`, agree. -/
public noncomputable def quotSmulTopPowRestrictEquiv (I : Ideal R) (k : ℕ) :
    (M ⧸ (I ^ k • (⊤ : Submodule R M))) ≃ₗ[R]
      (M ⧸ (I.map (algebraMap R S) ^ k • (⊤ : Submodule S M))) :=
  (Submodule.quotEquivOfEq _ _ (smul_top_pow_restrictScalars I k).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

/-- The two readings of the reduction agree on classes: `quotSmulTopPowRestrictEquiv` sends the
class of `x` to the class of `x`. -/
@[simp]
public theorem quotSmulTopPowRestrictEquiv_mk (I : Ideal R) (k : ℕ) (x : M) :
    quotSmulTopPowRestrictEquiv (S := S) (M := M) I k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  rfl

/-- The inverse of the two readings of the reduction is again the identity on classes. -/
@[simp]
public theorem quotSmulTopPowRestrictEquiv_symm_mk (I : Ideal R) (k : ℕ) (x : M) :
    (quotSmulTopPowRestrictEquiv (S := S) (M := M) I k).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  (LinearEquiv.symm_apply_eq _).2 (quotSmulTopPowRestrictEquiv_mk (S := S) I k x).symm

/-- The base acts on `M ⧸ 𝔞 · M` through `S ⧸ 𝔞`. -/
public instance isScalarTower_quotient_idealSmulTop (a : Ideal S) :
    IsScalarTower R (S ⧸ a) (M ⧸ (a • (⊤ : Submodule S M))) := by
  refine IsScalarTower.of_algebraMap_smul fun r w => ?_
  induction w using Submodule.Quotient.induction_on with
  | _ n =>
    change Submodule.Quotient.mk (algebraMap R S r • n) = Submodule.Quotient.mk (r • n)
    rw [IsScalarTower.algebraMap_smul]

end Levels

/-! ### The base surjects onto the levels of the completion -/

section Surjective

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- **The map `R → R̂ ⧸ (I R̂)ᵏ` is surjective**: an element of the completion agrees with one
coming from `R` modulo `Iᵏ`, since `Iᵏ · R̂` is the kernel of the `k`-th evaluation. -/
public theorem surjective_algebraMap_adicCompletion_quotient (hI : I.FG) (k : ℕ) :
    Function.Surjective (algebraMap R
      (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R)) ^ k)) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I R k x)
  refine ⟨r, ?_⟩
  change Ideal.Quotient.mk _ (AdicCompletion.of I R r) = Ideal.Quotient.mk _ x
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 ?_
  have hker : AdicCompletion.of I R r - x ∈ (AdicCompletion.eval I R k).ker := by
    simp only [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, ← hr, Submodule.mkQ_apply,
      sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
    Ideal.map_pow] at hker
  exact hker

end Surjective

/-! ### Exterior powers commute with reduction modulo an ideal -/

section ExteriorLevel

variable {R : Type*} [CommRing R] (K : Ideal R)
  {N : Type*} [AddCommGroup N] [Module R N]

/-- **Exterior powers commute with reduction modulo an ideal**:
`(⋀ⁱ_R N) ⧸ K · (⋀ⁱ_R N) ≃ ⋀ⁱ_{R ⧸ K} (N ⧸ K · N)`.  Both sides are the base change of
`⋀ⁱ_R N` along `R → R ⧸ K`, the left one by `Crystalline.isBaseChange_mkQ_smulTop` and the
right one by `Crystalline.isBaseChange_exteriorPowerMapOfBaseChange` fed with the same lemma in
degree one. -/
public noncomputable def exteriorPowerQuotSmulTopEquiv (i : ℕ) :
    (↥(⋀[R]^i N) ⧸ (K • (⊤ : Submodule R ↥(⋀[R]^i N)))) ≃ₗ[R ⧸ K]
      ↥(⋀[R ⧸ K]^i (N ⧸ (K • (⊤ : Submodule R N)))) :=
  (isBaseChange_mkQ_smulTop K ↥(⋀[R]^i N)).equiv.symm.trans
    (isBaseChange_exteriorPowerMapOfBaseChange _ (isBaseChange_mkQ_smulTop K N) i).equiv

/-- The exterior power of a linear equivalence carries a wedge to the wedge of the images. -/
public theorem exteriorPowerCongr_apply_ιMulti {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (n : ℕ) (e : M ≃ₗ[R] M') (w : Fin n → M) :
    exteriorPowerCongr n e (exteriorPower.ιMulti R n w) =
      exteriorPower.ιMulti R n fun j => e (w j) := by
  change exteriorPower.map n (e : M →ₗ[R] M') _ = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl

/-- **The equation pinning `Crystalline.exteriorPowerQuotSmulTopEquiv` down**: the class of a
wedge is the wedge of the classes.  Those classes span, so no second identification satisfies
the same equation. -/
public theorem exteriorPowerQuotSmulTopEquiv_mk_ιMulti (i : ℕ) (v : Fin i → N) :
    exteriorPowerQuotSmulTopEquiv K i
        (Submodule.Quotient.mk (exteriorPower.ιMulti R i v)) =
      exteriorPower.ιMulti (R ⧸ K) i fun j => Submodule.Quotient.mk (v j) := by
  have h1 : ((isBaseChange_mkQ_smulTop K ↥(⋀[R]^i N)).equiv).symm
      (Submodule.Quotient.mk (exteriorPower.ιMulti R i v)) =
      (1 : R ⧸ K) ⊗ₜ[R] exteriorPower.ιMulti R i v := by
    rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
    rfl
  change (isBaseChange_exteriorPowerMapOfBaseChange _ (isBaseChange_mkQ_smulTop K N) i).equiv
      (((isBaseChange_mkQ_smulTop K ↥(⋀[R]^i N)).equiv).symm _) = _
  rw [h1, IsBaseChange.equiv_tmul, one_smul, exteriorPowerMapOfBaseChange_ιMulti]
  rfl

/-- The inverse of `Crystalline.exteriorPowerQuotSmulTopEquiv` on a wedge of classes. -/
public theorem exteriorPowerQuotSmulTopEquiv_symm_ιMulti (i : ℕ) (v : Fin i → N) :
    (exteriorPowerQuotSmulTopEquiv K i).symm
        (exteriorPower.ιMulti (R ⧸ K) i fun j => Submodule.Quotient.mk (v j)) =
      Submodule.Quotient.mk (exteriorPower.ιMulti R i v) :=
  (LinearEquiv.symm_apply_eq _).2 (exteriorPowerQuotSmulTopEquiv_mk_ιMulti K i v).symm

end ExteriorLevel

/-! ### The level comparison of the two shapes -/

section Shape

variable {R : Type*} [CommRing R] {I : Ideal R} {N : Type*} [AddCommGroup N] [Module R N]

/-- The identification `N̂ ⧸ (I R̂)ᵏ · N̂ ≃ N ⧸ Iᵏ · N` of [Stacks, Tag 05GG], with the quotient
on the left taken over the completed ring. -/
public noncomputable def adicQuotLevelEquiv (hI : I.FG) (k : ℕ) :
    (AdicCompletion I N ⧸ (I.map (algebraMap R (AdicCompletion I R)) ^ k •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I N)))) ≃ₗ[R]
      (N ⧸ (I ^ k • (⊤ : Submodule R N))) :=
  (quotSmulTopPowRestrictEquiv (S := AdicCompletion I R) (M := AdicCompletion I N) I k).symm.trans
    (AdicCompletion.quotPowSMulTopEquiv hI N k)

/-- The level identification carries the class of the image of `x` in the completion to the
class of `x`. -/
@[simp]
public theorem adicQuotLevelEquiv_mk_of (hI : I.FG) (k : ℕ) (x : N) :
    adicQuotLevelEquiv hI k (Submodule.Quotient.mk (AdicCompletion.of I N x)) =
      Submodule.Quotient.mk x := by
  change AdicCompletion.quotPowSMulTopEquiv hI N k
      ((quotSmulTopPowRestrictEquiv (S := AdicCompletion I R) (M := AdicCompletion I N) I k).symm
        (Submodule.Quotient.mk (AdicCompletion.of I N x))) = _
  rw [quotSmulTopPowRestrictEquiv_symm_mk, AdicCompletion.quotPowSMulTopEquiv_mk,
    ← AdicCompletion.eval_apply, AdicCompletion.eval_of, Submodule.mkQ_apply]

/-- The inverse of the level identification. -/
@[simp]
public theorem adicQuotLevelEquiv_symm_mk (hI : I.FG) (k : ℕ) (x : N) :
    (adicQuotLevelEquiv hI k).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (AdicCompletion.of I N x) :=
  (LinearEquiv.symm_apply_eq _).2 (adicQuotLevelEquiv_mk_of hI k x).symm

/-- **The level-`k` comparison of the two shapes of the completed forms**, in positive exterior
degree:

`(⋀ⁱ_R N) ⧸ Iᵏ ≃ (⋀ⁱ_R̂ N̂) ⧸ (I R̂)ᵏ`.

Both sides reduce, by `Crystalline.exteriorPowerQuotSmulTopEquiv`, to an exterior power over a
level ring of the common reduction `N ⧸ Iᵏ · N`; the two level rings `R ⧸ Iᵏ` and `R̂ ⧸ (I R̂)ᵏ`
are cleared away by `exteriorPower.towerEquiv`, which is where `0 < i` is used — in degree zero
the comparison of exterior powers over a ring and over a quotient of it is the ring map itself
and is not an isomorphism. -/
public noncomputable def completedFormsShapeLevelEquiv (hI : I.FG) (i k : ℕ) (hi : 0 < i) :
    (↥(⋀[R]^i N) ⧸ (I ^ k • (⊤ : Submodule R ↥(⋀[R]^i N)))) ≃ₗ[R]
      (↥(⋀[AdicCompletion I R]^i (AdicCompletion I N)) ⧸
        (I.map (algebraMap R (AdicCompletion I R)) ^ k •
          (⊤ : Submodule (AdicCompletion I R)
            ↥(⋀[AdicCompletion I R]^i (AdicCompletion I N))))) :=
  ((exteriorPowerQuotSmulTopEquiv (I ^ k) (N := N) i).restrictScalars R).trans
    (((exteriorPower.towerEquiv R (R ⧸ I ^ k) (N ⧸ (I ^ k • (⊤ : Submodule R N))) i
          Ideal.Quotient.mk_surjective hi).symm).trans
      ((exteriorPowerCongr i (adicQuotLevelEquiv hI k).symm).trans
        ((exteriorPower.towerEquiv R
            (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R)) ^ k)
            (AdicCompletion I N ⧸ (I.map (algebraMap R (AdicCompletion I R)) ^ k •
              (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I N)))) i
            (surjective_algebraMap_adicCompletion_quotient hI k) hi).trans
          ((exteriorPowerQuotSmulTopEquiv
              (I.map (algebraMap R (AdicCompletion I R)) ^ k)
              (N := AdicCompletion I N) i).restrictScalars R).symm)))

/-- **The equation pinning the level comparison down**: it carries the class of a wedge
`ω₁ ∧ ⋯ ∧ ωᵢ` of elements of `N` to the class of the wedge, formed over the completed ring, of
their images in the completion.  Those classes span the source, so no second identification
satisfies the same equation. -/
public theorem completedFormsShapeLevelEquiv_mk_ιMulti (hI : I.FG) (i k : ℕ) (hi : 0 < i)
    (v : Fin i → N) :
    completedFormsShapeLevelEquiv hI i k hi
        (Submodule.Quotient.mk (exteriorPower.ιMulti R i v)) =
      Submodule.Quotient.mk (exteriorPower.ιMulti (AdicCompletion I R) i
        fun j => AdicCompletion.of I N (v j)) := by
  simp only [completedFormsShapeLevelEquiv, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_symm_apply,
    exteriorPowerQuotSmulTopEquiv_mk_ιMulti, exteriorPower.towerEquiv_symm_ιMulti,
    exteriorPowerCongr_apply_ιMulti, adicQuotLevelEquiv_symm_mk, exteriorPower.towerEquiv_ιMulti,
    exteriorPowerQuotSmulTopEquiv_symm_ιMulti]

end Shape

/-! ### From the levels to the completions -/

section Assembly

/-- Two `R`-linear maps out of a reduction of an exterior power agree as soon as they agree on
the classes of wedges: those classes span the reduction. -/
public theorem quotSmulTop_exteriorPower_hom_ext {R : Type*} [CommRing R] {N : Type*}
    [AddCommGroup N] [Module R N] {P : Type*} [AddCommGroup P] [Module R P] (K : Ideal R)
    {i : ℕ} {f g : (↥(⋀[R]^i N) ⧸ (K • (⊤ : Submodule R ↥(⋀[R]^i N)))) →ₗ[R] P}
    (h : ∀ v : Fin i → N, f (Submodule.Quotient.mk (exteriorPower.ιMulti R i v)) =
      g (Submodule.Quotient.mk (exteriorPower.ιMulti R i v))) : f = g := by
  refine LinearMap.ext fun y => ?_
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R i (M := N))) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨v, rfl⟩ := hz; exact h v
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Submodule.Quotient.mk_add, map_add, map_add, ha, hb]
    | smul r a _ ha =>
      rw [Submodule.Quotient.mk_smul, map_smul, map_smul, ha]

/-- The transition map of an adic completion fixes the class of an element.  This is
`Crystalline.transitionMap_mk` for an arbitrary ideal rather than for `(p)`. -/
public theorem adicTransitionMap_mk {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (I : Ideal R) {m n : ℕ} (h : m ≤ n) (x : P) :
    AdicCompletion.transitionMap I P h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  simp [AdicCompletion.transitionMap]

/-- **An identification of two adic completions out of compatible identifications of their
levels.**  The completion is by definition the limit of the levels, so a family of
identifications commuting with the transition maps is exactly an identification of the two
limits. -/
public def adicCompletionEquivOfLevels {R S P Q : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module S Q]
    (e : ∀ k : ℕ, (P ⧸ (I ^ k • (⊤ : Submodule R P))) ≃+ (Q ⧸ (J ^ k • (⊤ : Submodule S Q))))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : P ⧸ (I ^ n • (⊤ : Submodule R P))),
      AdicCompletion.transitionMap J Q h (e n x) = e m (AdicCompletion.transitionMap I P h x)) :
    AdicCompletion I P ≃+ AdicCompletion J Q where
  toFun x := ⟨fun k => e k (x.val k), fun {_ _} h => by rw [he h, x.property h]⟩
  invFun y := ⟨fun k => (e k).symm (y.val k), fun {m n} h => by
    apply (e m).injective
    rw [← he h, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, y.property h]⟩
  left_inv x := AdicCompletion.ext fun k => (e k).symm_apply_apply (x.val k)
  right_inv y := AdicCompletion.ext fun k => (e k).apply_symm_apply (y.val k)
  map_add' x y := AdicCompletion.ext fun k => map_add (e k) (x.val k) (y.val k)

/-- The value of `Crystalline.adicCompletionEquivOfLevels` at a level. -/
@[simp]
public theorem adicCompletionEquivOfLevels_val {R S P Q : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module S Q]
    (e : ∀ k : ℕ, (P ⧸ (I ^ k • (⊤ : Submodule R P))) ≃+ (Q ⧸ (J ^ k • (⊤ : Submodule S Q))))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : P ⧸ (I ^ n • (⊤ : Submodule R P))),
      AdicCompletion.transitionMap J Q h (e n x) = e m (AdicCompletion.transitionMap I P h x))
    (x : AdicCompletion I P) (k : ℕ) :
    (adicCompletionEquivOfLevels I J e he x).val k = e k (x.val k) :=
  rfl

variable {R : Type*} [CommRing R] {I : Ideal R} {N : Type*} [AddCommGroup N] [Module R N]

/-- **The level comparisons commute with the transition maps.**  Both composites send the class
of `ω₁ ∧ ⋯ ∧ ωᵢ` to the class, at the lower level, of the wedge of the images of the `ωⱼ` in the
completion, and those classes span. -/
public theorem transitionMap_completedFormsShapeLevelEquiv (hI : I.FG) (i : ℕ) (hi : 0 < i)
    {m n : ℕ} (h : m ≤ n)
    (x : ↥(⋀[R]^i N) ⧸ (I ^ n • (⊤ : Submodule R ↥(⋀[R]^i N)))) :
    AdicCompletion.transitionMap (I.map (algebraMap R (AdicCompletion I R)))
        ↥(⋀[AdicCompletion I R]^i (AdicCompletion I N)) h
        (completedFormsShapeLevelEquiv hI i n hi x) =
      completedFormsShapeLevelEquiv hI i m hi
        (AdicCompletion.transitionMap I ↥(⋀[R]^i N) h x) := by
  have key : ((AdicCompletion.transitionMap (I.map (algebraMap R (AdicCompletion I R)))
        ↥(⋀[AdicCompletion I R]^i (AdicCompletion I N)) h).restrictScalars R).comp
          (completedFormsShapeLevelEquiv hI i n hi).toLinearMap =
      (completedFormsShapeLevelEquiv hI i m hi).toLinearMap.comp
        (AdicCompletion.transitionMap I ↥(⋀[R]^i N) h) := by
    refine quotSmulTop_exteriorPower_hom_ext (I ^ n) fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.restrictScalars_apply,
      completedFormsShapeLevelEquiv_mk_ιMulti, adicTransitionMap_mk]
  exact congrFun (congrArg DFunLike.coe key) x

/-- **The two shapes of the completed forms agree**, in positive exterior degree:

`AdicCompletion_B (⋀ⁱ_B N) ≃ AdicCompletion_{B̂} (⋀ⁱ_{B̂} N̂)`.

This is `Crystalline.completedFormsShapeLevelEquiv` assembled over the levels, which is legitimate
by `Crystalline.transitionMap_completedFormsShapeLevelEquiv`. -/
public noncomputable def completedFormsShapeEquiv (hI : I.FG) (i : ℕ) (hi : 0 < i) :
    AdicCompletion I ↥(⋀[R]^i N) ≃+
      AdicCompletion (I.map (algebraMap R (AdicCompletion I R)))
        ↥(⋀[AdicCompletion I R]^i (AdicCompletion I N)) :=
  adicCompletionEquivOfLevels I (I.map (algebraMap R (AdicCompletion I R)))
    (fun k => (completedFormsShapeLevelEquiv hI i k hi).toAddEquiv)
    (fun h x => transitionMap_completedFormsShapeLevelEquiv hI i hi h x)

/-- The comparison of the two shapes, read at a level, is the level comparison. -/
@[simp]
public theorem completedFormsShapeEquiv_val (hI : I.FG) (i : ℕ) (hi : 0 < i)
    (x : AdicCompletion I ↥(⋀[R]^i N)) (k : ℕ) :
    (completedFormsShapeEquiv hI i hi x).val k =
      completedFormsShapeLevelEquiv hI i k hi (x.val k) :=
  rfl

/-- **The comparison of the two shapes carries a wedge to the wedge of the images**: it sends
the image in the completion of `ω₁ ∧ ⋯ ∧ ωᵢ` to the image in the completion of the wedge, formed
over `B̂`, of the images of the `ωⱼ` in `N̂`. -/
public theorem completedFormsShapeEquiv_of_ιMulti (hI : I.FG) (i : ℕ) (hi : 0 < i)
    (v : Fin i → N) :
    completedFormsShapeEquiv hI i hi
        (AdicCompletion.of I ↥(⋀[R]^i N) (exteriorPower.ιMulti R i v)) =
      AdicCompletion.of (I.map (algebraMap R (AdicCompletion I R)))
        ↥(⋀[AdicCompletion I R]^i (AdicCompletion I N))
        (exteriorPower.ιMulti (AdicCompletion I R) i fun j => AdicCompletion.of I N (v j)) :=
  AdicCompletion.ext fun k => completedFormsShapeLevelEquiv_mk_ιMulti hI i k hi v

end Assembly

end Crystalline

end
