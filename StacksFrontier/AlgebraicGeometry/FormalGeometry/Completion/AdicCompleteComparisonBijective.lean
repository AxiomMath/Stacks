module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ModuleTower
public import StacksFrontier.Homology.DerivedComplete.CompletionUnitDenseModIdeal
public import StacksCore.Tactic.StacksAttribute

/-!
# A comparison into an adic completion that extends the completion map is bijective

Let `A` be a Noetherian ring, `I ⊂ A` an ideal and `M` a finite `A`-module. Let `T` be an
`A`-module that is *abstractly* isomorphic to `AdicCompletion I M`, and let

`Φ : T →ₗ[A] AdicCompletion I M`

be a linear map for which there is `a : M →ₗ[A] T` with `Φ ∘ a = AdicCompletion.of I M`. Then `Φ`
is bijective.

## Why this shape

This is the commutative-algebra core of the comparison that part (2) of [Stacks, Tag 0A0K] needs
over an affine open. The point of the hypotheses is that `T` is only ever given *abstractly*: in
the application `T = H^q(U, K^∧)` and the identification of it with an adic completion is
[Stacks, Tag 0A0L], which is formalized as a `Nonempty` isomorphism carrying no compatibility with
the completion unit. A statement about a *map* cannot be transported across such an isomorphism —
but being `I`-adically complete is a *property*, so it can, and that is all `θ` is used for here.
The map itself enters only through `Φ` and the single identity `Φ ∘ a = of`, both of which the
application supplies canonically, hence naturally in `U`.

## The argument

Everything happens modulo the powers of `I`, where the modules in sight are finite over `A`, so
no finiteness over `AdicCompletion I A` and no `AdicCompletion I A`-linearity is needed.

* `Φ` is surjective modulo `I`, because `AdicCompletion.of` is
  (`Stacks.Algebraization.range_adicCompletion_of_sup_smul_eq_top`) and `of` factors through `Φ`;
  an induction upgrades this to surjectivity modulo every `Iⁿ`.
* `AdicCompletion.pow_smul_top_eq_ker_eval` identifies `AdicCompletion I M ⧸ Iⁿ • ⊤` with
  `M ⧸ Iⁿ • M`, which is finite over `A`; and `θ` carries `T ⧸ Iⁿ • ⊤` to the same module. So the
  reduction of `Φ` modulo `Iⁿ` is a surjection between two modules identified with a Noetherian
  one, hence injective by Orzech's theorem
  (`IsNoetherian.injective_of_surjective_of_injective`).
* Injectivity of `Φ` follows because its kernel lies in every `Iⁿ • T` and `T` is separated;
  surjectivity follows by assembling the approximate preimages, which the injectivity modulo `Iⁿ`
  makes a Cauchy sequence, and `T` is precomplete.

## Main results

* `Stacks.Algebraization.surjective_mapQ_pow_of_comp_eq_of` — the reduction of `Φ` modulo `Iⁿ` is
  surjective.
* `Stacks.Algebraization.bijective_mapQ_pow_of_comp_eq_of` — it is bijective.
* `Stacks.Algebraization.bijective_of_isAdicComplete_comp_eq_of` — `Φ` is bijective.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public noncomputable section

open Function

universe u

namespace Stacks.Algebraization

section

variable {A : Type u} [CommRing A] (I : Ideal A)
  {M : Type u} [AddCommGroup M] [Module A M]
  {T : Type u} [AddCommGroup T] [Module A T]

/-- A linear map carries `Iⁿ • ⊤` into `Iⁿ • ⊤`. -/
public theorem pow_smul_top_le_comap (n : ℕ) (f : T →ₗ[A] M) :
    (I ^ n • (⊤ : Submodule A T)) ≤ Submodule.comap f (I ^ n • (⊤ : Submodule A M)) := by
  refine Submodule.map_le_iff_le_comap.1 ?_
  refine le_of_eq_of_le (Submodule.map_smul'' _ _ f) ?_
  exact Submodule.smul_le.2 fun r hr x _ => Submodule.smul_mem_smul hr Submodule.mem_top

/-- The reduction of a linear map modulo `Iⁿ`. -/
public def mapQPow (n : ℕ) (f : T →ₗ[A] M) :
    (T ⧸ (I ^ n • (⊤ : Submodule A T))) →ₗ[A] (M ⧸ (I ^ n • (⊤ : Submodule A M))) :=
  Submodule.mapQ _ _ f (pow_smul_top_le_comap I n f)

/-- `mapQPow I n f` sends the class of `t` to the class of `f t`. -/
public theorem mapQPow_mk (n : ℕ) (f : T →ₗ[A] M) (t : T) :
    mapQPow I n f (Submodule.Quotient.mk t) = Submodule.Quotient.mk (f t) := rfl

/-- The reduction modulo `Iⁿ` of a linear equivalence is a linear equivalence. -/
public def equivQPow (n : ℕ) (e : T ≃ₗ[A] M) :
    (T ⧸ (I ^ n • (⊤ : Submodule A T))) ≃ₗ[A] (M ⧸ (I ^ n • (⊤ : Submodule A M))) :=
  Submodule.Quotient.equiv _ _ e
    (((Submodule.map_smul'' _ _ (e : T →ₗ[A] M)).trans
      (congrArg (fun N => I ^ n • N) (Submodule.map_top (e : T →ₗ[A] M)))).trans
      (congrArg (fun N => I ^ n • N) (LinearMap.range_eq_top.2 e.surjective)))

/-- **Surjectivity modulo `I` upgrades to surjectivity modulo every `Iⁿ`.** Writing
`Iⁿ • ⊤ = Iⁿ • (range f ⊔ I • ⊤) = Iⁿ • range f ⊔ Iⁿ⁺¹ • ⊤` puts the first summand inside
`range f`. -/
public theorem range_sup_pow_smul_top_eq_top_of_sup_eq_top (f : T →ₗ[A] M)
    (h : LinearMap.range f ⊔ I • (⊤ : Submodule A M) = ⊤) (n : ℕ) :
    LinearMap.range f ⊔ I ^ n • (⊤ : Submodule A M) = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_antisymm le_top ?_
    refine le_trans (le_of_eq ih.symm) (sup_le le_sup_left ?_)
    rw [show I ^ n • (⊤ : Submodule A M) =
        I ^ n • (LinearMap.range f ⊔ I • (⊤ : Submodule A M)) by rw [h], Submodule.smul_sup]
    refine sup_le (le_sup_of_le_left Submodule.smul_le_right) (le_sup_of_le_right ?_)
    rw [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ]

/-- **The reduction of `f` modulo `Iⁿ` is surjective** when `range f ⊔ Iⁿ • ⊤ = ⊤`. -/
public theorem surjective_mapQPow_of_range_sup_eq_top (f : T →ₗ[A] M) (n : ℕ)
    (h : LinearMap.range f ⊔ I ^ n • (⊤ : Submodule A M) = ⊤) :
    Surjective (mapQPow I n f) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule A M)) y
  have hy : y ∈ LinearMap.range f ⊔ I ^ n • (⊤ : Submodule A M) := by simp [h]
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨t, rfl⟩ := hu
  refine ⟨Submodule.Quotient.mk t, ?_⟩
  rw [mapQPow_mk]
  refine (Submodule.Quotient.eq _).2 ?_
  simpa using Submodule.neg_mem _ hv

/-- **A map that is bijective modulo every `Iⁿ` is bijective**, provided its source is
`I`-adically complete and its target separated: the source's separatedness gives injectivity and
its precompleteness assembles the approximate preimages, whose compatibility is the injectivity
modulo `Iⁿ`. -/
public theorem bijective_of_bijective_mapQPow (f : T →ₗ[A] M)
    [hTc : IsAdicComplete I T] [hMh : IsHausdorff I M]
    (hbij : ∀ n : ℕ, Bijective (mapQPow I n f)) : Bijective f := by
  constructor
  · intro t t' htt
    refine (IsHausdorff.eq_iff_smodEq (I := I)).2 fun n => ?_
    refine (hbij n).1 ?_
    change mapQPow I n f (Submodule.Quotient.mk t) = mapQPow I n f (Submodule.Quotient.mk t')
    rw [mapQPow_mk, mapQPow_mk, htt]
  · intro y
    have hstep : ∀ n : ℕ, ∃ t : T, f t ≡ y [SMOD I ^ n • (⊤ : Submodule A M)] := fun n => by
      obtain ⟨z, hz⟩ := (hbij n).2 (Submodule.Quotient.mk y)
      obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule A T)) z
      exact ⟨t, (mapQPow_mk I n f t).symm.trans hz⟩
    choose t ht using hstep
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → t m ≡ t n [SMOD I ^ m • (⊤ : Submodule A T)] := by
      intro m n hmn
      refine (hbij m).1 ?_
      show mapQPow I m f (Submodule.Quotient.mk (t m)) =
        mapQPow I m f (Submodule.Quotient.mk (t n))
      rw [mapQPow_mk, mapQPow_mk]
      exact (ht m).trans (SModEq.mono (Submodule.pow_smul_top_le I _ hmn) (ht n)).symm
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hTc.toIsPrecomplete hcauchy
    refine ⟨L, (IsHausdorff.eq_iff_smodEq (I := I)).2 fun n => ?_⟩
    have h1 : f (t n) ≡ f L [SMOD I ^ n • (⊤ : Submodule A M)] := by
      have h := congrArg (mapQPow I n f) (hL n)
      rwa [mapQPow_mk, mapQPow_mk] at h
    exact h1.symm.trans (ht n)

/-- If `g ∘ b = f` and `f` has range generating the module modulo `I`, so does `g`. -/
private theorem range_sup_smul_top_eq_top_of_comp_eq {L : Type*} [AddCommGroup L] [Module A L]
    (f : L →ₗ[A] M) (g : T →ₗ[A] M) (b : L →ₗ[A] T) (h : ∀ l, g (b l) = f l)
    (hf : LinearMap.range f ⊔ I • (⊤ : Submodule A M) = ⊤) :
    LinearMap.range g ⊔ I • (⊤ : Submodule A M) = ⊤ :=
  top_unique (hf.symm.trans_le (sup_le_sup_right (by rintro _ ⟨l, rfl⟩; exact ⟨b l, h l⟩) _))

/-- A surjective reduction modulo `Iⁿ` is bijective if its source is isomorphic to its Noetherian
target. -/
private theorem bijective_mapQPow_of_surjective {M' : Type u} [AddCommGroup M'] [Module A M']
    (n : ℕ) (e : T ≃ₗ[A] M') (f : T →ₗ[A] M') (hs : Surjective (mapQPow I n f))
    [IsNoetherian A (M' ⧸ (I ^ n • (⊤ : Submodule A M')))] : Bijective (mapQPow I n f) :=
  ⟨IsNoetherian.injective_of_surjective_of_injective
    (equivQPow I n e : (T ⧸ (I ^ n • (⊤ : Submodule A T))) →ₗ[A] _) (mapQPow I n f)
    (equivQPow I n e).injective hs, hs⟩

end

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
  {T : Type u} [AddCommGroup T] [Module A T]

/-- `AdicCompletion I M ⧸ Iⁿ • ⊤` is identified with `M ⧸ Iⁿ • M` by evaluation at level `n`:
evaluation is surjective and, `I` being finitely generated, its kernel is exactly `Iⁿ • ⊤`
(`AdicCompletion.pow_smul_top_eq_ker_eval`). -/
public def completionQuotPowEquiv (n : ℕ) :
    (AdicCompletion I M ⧸ (I ^ n • (⊤ : Submodule A (AdicCompletion I M)))) ≃ₗ[A]
      (M ⧸ (I ^ n • (⊤ : Submodule A M))) :=
  (Submodule.quotEquivOfEq _ _
      (AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing)).trans
    (LinearMap.quotKerEquivOfSurjective _ (AdicCompletion.eval_surjective I M n))

/-- `AdicCompletion I M ⧸ Iⁿ • ⊤` is a Noetherian `A`-module: it is `M ⧸ Iⁿ • M`, a quotient of
the finite module `M`. -/
public theorem isNoetherian_completionQuotPow (n : ℕ) :
    IsNoetherian A (AdicCompletion I M ⧸ (I ^ n • (⊤ : Submodule A (AdicCompletion I M)))) := by
  have : Module.Finite A (M ⧸ (I ^ n • (⊤ : Submodule A M))) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact isNoetherian_of_linearEquiv (completionQuotPowEquiv I n).symm

variable (a : M →ₗ[A] T) (Φ : T →ₗ[A] AdicCompletion I M)
  (hcomp : ∀ m, Φ (a m) = AdicCompletion.of I M m)

omit [IsNoetherianRing A] [Module.Finite A M] in
include hcomp in
/-- The completion map factors through `Φ`, so its range is contained in the range of `Φ`. -/
public theorem range_of_le_range : LinearMap.range (AdicCompletion.of I M) ≤
    LinearMap.range Φ := by
  rintro x ⟨m, rfl⟩
  exact ⟨a m, hcomp m⟩

omit [Module.Finite A M] in
include hcomp in
/-- **`Φ` is surjective modulo every power of `I`.** For `n = 1` this is the surjectivity modulo
`I` of the completion map, and the induction step replaces `Iⁿ • ⊤` by
`Iⁿ • (range Φ ⊔ I • ⊤) ≤ range Φ ⊔ Iⁿ⁺¹ • ⊤`. -/
public theorem range_sup_pow_smul_top_eq_top (n : ℕ) :
    LinearMap.range Φ ⊔ I ^ n • (⊤ : Submodule A (AdicCompletion I M)) = ⊤ :=
  range_sup_pow_smul_top_eq_top_of_sup_eq_top I Φ
    (range_sup_smul_top_eq_top_of_comp_eq I _ Φ a hcomp
      (range_adicCompletion_of_sup_smul_eq_top I I.fg_of_isNoetherianRing M)) n

omit [Module.Finite A M] in
include hcomp in
/-- **The reduction of `Φ` modulo `Iⁿ` is surjective**, which is
`Stacks.Algebraization.range_sup_pow_smul_top_eq_top` read on the quotient. -/
public theorem surjective_mapQ_pow_of_comp_eq_of (n : ℕ) :
    Surjective (mapQPow I n Φ) :=
  surjective_mapQPow_of_range_sup_eq_top I Φ n (range_sup_pow_smul_top_eq_top I a Φ hcomp n)

include hcomp in
/-- **The reduction of `Φ` modulo `Iⁿ` is bijective.** It is surjective, and both its source and
its target are identified with the Noetherian module `M ⧸ Iⁿ • M` — the target by
`Stacks.Algebraization.completionQuotPowEquiv` and the source by `θ` — so Orzech's theorem makes
it injective. -/
public theorem bijective_mapQ_pow_of_comp_eq_of (θ : T ≃ₗ[A] AdicCompletion I M) (n : ℕ) :
    Bijective (mapQPow I n Φ) := by
  have := isNoetherian_completionQuotPow (M := M) I n
  have hs := surjective_mapQ_pow_of_comp_eq_of I a Φ hcomp n
  exact bijective_mapQPow_of_surjective I n θ Φ hs

include hcomp in
/-- **A comparison into an adic completion that extends the completion map is bijective.**

Let `A` be Noetherian, `M` a finite `A`-module and `T` an `A`-module *abstractly* isomorphic to
`AdicCompletion I M`. If `Φ : T →ₗ[A] AdicCompletion I M` satisfies `Φ ∘ a = AdicCompletion.of`
for some `a : M →ₗ[A] T`, then `Φ` is bijective.

The isomorphism `θ` is used only for the two *properties* it transports — that `T` is separated
and precomplete, and that `T ⧸ Iⁿ • ⊤` is Noetherian — never to transport a map; see the module
documentation. -/
public theorem bijective_of_isAdicComplete_comp_eq_of (θ : T ≃ₗ[A] AdicCompletion I M) :
    Bijective Φ := by
  have : IsAdicComplete I T := Stacks.Coherent.isAdicComplete_of_linearEquiv I θ
    (AdicCompletion.isAdicComplete I.fg_of_isNoetherianRing)
  exact bijective_of_bijective_mapQPow I Φ (bijective_mapQ_pow_of_comp_eq_of I a Φ hcomp θ)

include hcomp in
/-- `Stacks.Algebraization.bijective_of_isAdicComplete_comp_eq_of` packaged as a linear
equivalence, which is the form the comparison over an affine open is consumed in. -/
public def adicCompleteComparisonEquiv (θ : T ≃ₗ[A] AdicCompletion I M) :
    T ≃ₗ[A] AdicCompletion I M :=
  LinearEquiv.ofBijective Φ (bijective_of_isAdicComplete_comp_eq_of I a Φ hcomp θ)

include hcomp in
/-- The equivalence `adicCompleteComparisonEquiv I a Φ hcomp θ` acts as `Φ`. -/
@[simp] public theorem adicCompleteComparisonEquiv_apply (θ : T ≃ₗ[A] AdicCompletion I M) (t : T) :
    adicCompleteComparisonEquiv I a Φ hcomp θ t = Φ t := rfl

end

section UnitDirection

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
  {T : Type u} [AddCommGroup T] [Module A T]

/-- `T ⧸ Iⁿ • ⊤` is Noetherian when `T` is abstractly isomorphic to `AdicCompletion I M`. -/
public theorem isNoetherian_quotPow_of_linearEquiv (θ : T ≃ₗ[A] AdicCompletion I M) (n : ℕ) :
    IsNoetherian A (T ⧸ (I ^ n • (⊤ : Submodule A T))) := by
  have := isNoetherian_completionQuotPow (M := M) I n
  exact isNoetherian_of_linearEquiv (equivQPow I n θ).symm

/-- **The canonical comparison *out of* an adic completion is bijective.**

Let `A` be Noetherian, `M` a finite `A`-module and `T` an `A`-module *abstractly* isomorphic to
`AdicCompletion I M`. Let `a : M →ₗ[A] T` be a map whose image generates `T` modulo `I`, and let
`c : AdicCompletion I M →ₗ[A] T` extend it along the completion map. Then `c` is bijective.

This is the direction the geometric application actually produces. There `T = H^q(U, K^∧)`,
`a = H^q` of the derived completion unit, and `c` is the extension of `a` over the completion,
which exists because `T` is `I`-adically complete — a *property*, so it transports across the
non-canonical identification `θ` of [Stacks, Tag 0A0L] where a map would not. The density
hypothesis is the statement that the completion unit is surjective modulo `I` on cohomology,
which is `Stacks.Algebraization.range_homologyMap_derivedCompletionUnit_sup_smul_eq_top`.

No pro-isomorphism of adic towers and no derived tensor tower enters: the comparison is built
from the unit alone. -/
public theorem bijective_of_isAdicComplete_of_range_sup_eq_top
    (θ : T ≃ₗ[A] AdicCompletion I M) (a : M →ₗ[A] T) (c : AdicCompletion I M →ₗ[A] T)
    (hc : ∀ m, c (AdicCompletion.of I M m) = a m)
    (hdense : LinearMap.range a ⊔ I • (⊤ : Submodule A T) = ⊤) :
    Bijective c := by
  have hTA : IsAdicComplete I T := Stacks.Coherent.isAdicComplete_of_linearEquiv I θ
    (AdicCompletion.isAdicComplete I.fg_of_isNoetherianRing)
  have hbase := range_sup_smul_top_eq_top_of_comp_eq I a c (AdicCompletion.of I M) hc hdense
  refine bijective_of_bijective_mapQPow I c fun n => ?_
  have := isNoetherian_quotPow_of_linearEquiv I θ n
  have hs := surjective_mapQPow_of_range_sup_eq_top I c n
    (range_sup_pow_smul_top_eq_top_of_sup_eq_top I c hbase n)
  exact bijective_mapQPow_of_surjective I n θ.symm c hs

/-- `Stacks.Algebraization.bijective_of_isAdicComplete_of_range_sup_eq_top` as a linear
equivalence `AdicCompletion I M ≃ₗ[A] T`. -/
public def adicCompleteUnitComparisonEquiv (θ : T ≃ₗ[A] AdicCompletion I M)
    (a : M →ₗ[A] T) (c : AdicCompletion I M →ₗ[A] T)
    (hc : ∀ m, c (AdicCompletion.of I M m) = a m)
    (hdense : LinearMap.range a ⊔ I • (⊤ : Submodule A T) = ⊤) :
    AdicCompletion I M ≃ₗ[A] T :=
  LinearEquiv.ofBijective c
    (bijective_of_isAdicComplete_of_range_sup_eq_top I θ a c hc hdense)

end UnitDirection

/-! ### A map out of a completion is determined by its restriction along the completion map -/

section Unique

variable {A : Type u} [CommRing A] (I : Ideal A)
  {M : Type u} [AddCommGroup M] [Module A M]

/-- **An additive map out of `AdicCompletion I M` is determined by its restriction along the
completion map**, provided the difference of two such maps carries the filtration `Iⁿ • ⊤` into a
separated filtration of the target.

The image of `AdicCompletion.of` together with `Iⁿ • ⊤` is everything
(`Stacks.Algebraization.range_sup_pow_smul_top_eq_top_of_sup_eq_top` applied to the completion
map), so the difference of the two maps lands in every member of the filtration, hence in zero.

The filtration `P` is what stands in for linearity over `A`: where this is used the target is a
module over a *different* ring, over which the two maps compared are not linear, and all that is
needed is that their difference shrinks the filtration. -/
public theorem eq_of_separated_filtration_of_comp_eq (hI : I.FG)
    {N : Type*} [AddCommGroup N] (P : ℕ → AddSubgroup N)
    (g₁ g₂ : AdicCompletion I M →+ N)
    (hsmall : ∀ (n : ℕ) (x : AdicCompletion I M),
      x ∈ I ^ n • (⊤ : Submodule A (AdicCompletion I M)) → g₁ x - g₂ x ∈ P n)
    (hsep : ∀ y : N, (∀ n, y ∈ P n) → y = 0)
    (h : ∀ m, g₁ (AdicCompletion.of I M m) = g₂ (AdicCompletion.of I M m)) :
    g₁ = g₂ := by
  have hbase := range_adicCompletion_of_sup_smul_eq_top I hI M
  refine AddMonoidHom.ext fun x => ?_
  refine sub_eq_zero.mp (hsep _ fun n => ?_)
  have hx : x ∈ LinearMap.range (AdicCompletion.of I M) ⊔
      I ^ n • (⊤ : Submodule A (AdicCompletion I M)) := by
    simp [range_sup_pow_smul_top_eq_top_of_sup_eq_top I (AdicCompletion.of I M) hbase n]
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨m, rfl⟩ := hu
  rw [map_add, map_add, h m, add_sub_add_left_eq_sub]
  exact hsmall n v hv

/-- **A linear map out of `AdicCompletion I M` is determined by its restriction along the
completion map**, when the target is `I`-adically separated. A linear map always shrinks the
filtration (`Stacks.Algebraization.pow_smul_top_le_comap`), so this is
`Stacks.Algebraization.eq_of_separated_filtration_of_comp_eq` at the `I`-adic filtration of the
target. -/
public theorem eq_of_isHausdorff_of_comp_eq (hI : I.FG) {T : Type u} [AddCommGroup T] [Module A T]
    [IsHausdorff I T] (g₁ g₂ : AdicCompletion I M →ₗ[A] T)
    (h : ∀ m, g₁ (AdicCompletion.of I M m) = g₂ (AdicCompletion.of I M m)) :
    g₁ = g₂ := by
  refine LinearMap.ext fun x => ?_
  have hg : (g₁ : AdicCompletion I M →+ T) = (g₂ : AdicCompletion I M →+ T) := by
    refine eq_of_separated_filtration_of_comp_eq I hI
      (fun n => (I ^ n • (⊤ : Submodule A T)).toAddSubgroup) _ _
      (fun n y hy => pow_smul_top_le_comap I n (g₁ - g₂) hy)
      (fun y hy => IsHausdorff.haus' y fun n => SModEq.zero.2 (hy n)) h
  exact DFunLike.congr_fun hg x

end Unique

/-! ### The canonical extension of a map over the completion -/

section Extend

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
  {T : Type u} [AddCommGroup T] [Module A T] [IsAdicComplete I T]

/-- **The canonical extension of `a : M →ₗ[A] T` over the adic completion of `M`**, available
because `T` is `I`-adically complete: complete the map and then undo the completion map of `T`,
which is bijective. -/
public def adicCompletionExtend (a : M →ₗ[A] T) : AdicCompletion I M →ₗ[A] T :=
  (AdicCompletion.ofLinearEquiv I T).symm.toLinearMap ∘ₗ
    ((AdicCompletion.map I a).restrictScalars A)

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- The canonical extension restricts along the completion map to the original map. -/
@[simp] public theorem adicCompletionExtend_of (a : M →ₗ[A] T) (m : M) :
    adicCompletionExtend I a (AdicCompletion.of I M m) = a m := by
  change (AdicCompletion.ofLinearEquiv I T).symm (AdicCompletion.map I a
    (AdicCompletion.of I M m)) = a m
  rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]

omit [Module.Finite A M] in
/-- **The canonical extension is the only linear extension of `a` over the completion.** An
`I`-adically complete module is separated, so
`Stacks.Algebraization.eq_of_isHausdorff_of_comp_eq` applies; this is what makes
`Stacks.Algebraization.adicCompletionExtend` natural wherever `a` is. -/
public theorem eq_adicCompletionExtend (a : M →ₗ[A] T) (g : AdicCompletion I M →ₗ[A] T)
    (hg : ∀ m, g (AdicCompletion.of I M m) = a m) :
    g = adicCompletionExtend I a :=
  eq_of_isHausdorff_of_comp_eq I I.fg_of_isNoetherianRing g (adicCompletionExtend I a)
    fun m => (hg m).trans (adicCompletionExtend_of I a m).symm

/-- **The canonical extension over the completion is an isomorphism** as soon as `T` is
abstractly isomorphic to `AdicCompletion I M` and the image of `a` generates `T` modulo `I`.

This is the form [Stacks, Tag 0A0K] part (2) consumes over an affine open: `a` is `H^q` of the
derived completion unit, the density is the surjectivity modulo `I` of that unit, and `θ` is the
non-canonical identification of [Stacks, Tag 0A0L], used only for the properties it transports. -/
public theorem bijective_adicCompletionExtend (θ : T ≃ₗ[A] AdicCompletion I M) (a : M →ₗ[A] T)
    (hdense : LinearMap.range a ⊔ I • (⊤ : Submodule A T) = ⊤) :
    Bijective (adicCompletionExtend I a) :=
  bijective_of_isAdicComplete_of_range_sup_eq_top I θ a (adicCompletionExtend I a)
    (adicCompletionExtend_of I a) hdense

/-- `Stacks.Algebraization.bijective_adicCompletionExtend` as a linear equivalence. -/
public def adicCompletionExtendEquiv (θ : T ≃ₗ[A] AdicCompletion I M) (a : M →ₗ[A] T)
    (hdense : LinearMap.range a ⊔ I • (⊤ : Submodule A T) = ⊤) :
    AdicCompletion I M ≃ₗ[A] T :=
  LinearEquiv.ofBijective _ (bijective_adicCompletionExtend I θ a hdense)

end Extend

end Stacks.Algebraization

end
