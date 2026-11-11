module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompletelyDecomposedCover
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafGeneral
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic

/-!
# Stacks 0FDX on every test scheme: the induction on the dimension, assembled

Stacks 0FDX says that for a scheme `X` of finite type over the base scheme of chapter 42 of the
Stacks Project, carrying an ample invertible module and of dimension `d`, and for invertible
`𝒪_X`-modules `ℒ_1, …, ℒ_{d+1}`, the composite `c₁(ℒ_1) ∘ ⋯ ∘ c₁(ℒ_{d+1})` is zero in
`A^{d+1}(X)`. A bivariant class vanishes exactly when its cap operation vanishes on **every**
test scheme `u : T ⟶ X` locally of finite type (Stacks 02UC), with no bound on the dimension of
`T`, so the conclusion unwinds to

  `c₁(u^*ℒ_1) ∩ ⋯ ∩ c₁(u^*ℒ_{d+1}) ∩ α = 0`   in `A_k(T)`,  for every `α ∈ A_{k+d+1}(T)`,

quantified over all such `u`. That is what this file proves, by the source's own induction on
`d`: `Stacks.Chow.iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le`.

The inductive step, the base case and the dimension drop are
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction`; what is added here is the
recursion that runs them, and the two reformulations of the step the recursion needs.

## The recursion

At `d + 1` the last module `ℒ_{d+2}` is written as a difference of effective Cartier divisors by
Stacks 0AYM (`AlgebraicGeometry.InvertibleSheafGeneral`
`.exists_effectiveCartierDivisors_tensor_invertibleSheaf`), which is where the ample invertible
module of the source's hypotheses is used and the only place it is used. The step
`Stacks.Chow.iteratedChernCapOnChow_capOnChow_eq_zero_of_tensorObj` then reduces the vanishing to
the two inductive hypotheses on the zero schemes of the canonical sections of `𝒪_X(D)` and
`𝒪_X(D')`, and those zero schemes **are** `D` and `D'`, by Stacks 01WX in the form
`Stacks.Divisors.zeroScheme_canonicalSection`. On `D` the inductive hypothesis is available
because

* `D` is Noetherian — `AlgebraicGeometry.isNoetherian_source_of_isProper` at the closed immersion
  `i : D ⟶ X`;
* `i^*A` is ample for `A` ample — the easy half of Stacks 09MS, in this repository as the
  unconditional `Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion` (Stacks 0B3E
  for a closed immersion). Note that the `Surjective` and `IsNoetherian` hypotheses that
  `Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion` carries —
  and that a divisor's immersion does not satisfy — are *not* an obstruction: that declaration is
  Stacks 09MS's statement at Stacks 09MS's own hypotheses, and the general statement is proved
  beside it;
* and `dim D ≤ d` — `Stacks.Chow.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor`,
  an effective Cartier divisor having nowhere dense support.

The modules the inductive hypothesis is applied to on `D` are the restrictions `i^*ℒ_j`, so what
it delivers on a test scheme `g : T' ⟶ D` is the product of the caps of `g^*i^*ℒ_j`, while the
step asks for the product of the caps of `(g ≫ i)^*ℒ_j`; the two are identified by
`AlgebraicGeometry.Scheme.Modules.pullbackComp` through `Stacks.Chow.invCap_capOnChow_congr` and
`Stacks.Chow.iteratedChernCapOnChow_congr_forall₂`, exactly as inside the step itself.

At `d = 0` the list of cap operators has one entry and the base case
`Stacks.Chow.invCap_capOnChow_pullback_eq_zero_of_topologicalKrullDim_le_zero` applies.

## Main results

* `Stacks.Chow.iteratedChernCapOnChow_capOnChow_eq_zero_of_effectiveCartierDivisors` — the
  inductive step of Stacks 0FDX with the divisors of Stacks 0AYM in place of the zero schemes of
  their canonical sections.
* `Stacks.Chow.iteratedChernCapOnChow_ofFn_succ_eq_zero_of_effectiveCartierDivisors` — the same
  step read on a family `ℒ_1, …, ℒ_{n+1}` indexed by `Fin (n + 1)`, the last member being the one
  the divisors present; this is the shape the recursion consumes.
* `Stacks.Chow.iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le` — **Stacks 0FDX on
  every test scheme**: the vanishing of `c₁(u^*ℒ_1) ∩ ⋯ ∩ c₁(u^*ℒ_{d+1}) ∩ −` on every test
  scheme `u : T ⟶ X` locally of finite type, with no bound on the dimension of `T`.

## Implementation notes

### The two spellings of invertibility

`Stacks.Ample.IsInvertibleModule`, which `Stacks.Ample.IsAmple` and Stacks 0AYM are stated over,
and `AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property`, which
`Stacks.Chow.invCap` is stated over, are definitionally equal but are not found in each other by
instance search. The ample module is therefore bound in the first spelling and the modules whose
Chern classes are capped in the second, and where a module must be read in both the instance is
passed as an explicit term.

### The pullback along a bound morphism is invertible only as a scoped instance

Stacks 0B8L is deliberately kept out of instance search in this library and is made an instance
`scoped` to `Stacks.AlgebraicGeometry.AmpleLimit`. The statements below quantify over test
schemes, so the invertible modules they mention are pullbacks along *bound* morphisms and cannot
be written without it; this file therefore opens that scope, as its documentation prescribes.

### What this is not

The conclusion of the source is an equality in `A^{d+1}(X)`. Its left hand side is a term of this
repository — the composite of Stacks 0B75 at the bivariant first Chern classes of Stacks 0B77,
read for `𝟙 X` as `Stacks.Chow.BivariantClass.mulId` — and a bivariant class is zero exactly when
every one of its cap operations is, by
`Stacks.Chow.BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero`. The vanishing
proved here is of the iterated cap operation quantified over all lists of cap operators that the
modules supply, which is what that unwinding asks for. The equality of bivariant classes itself is
`Stacks.Chow.firstChernClassProduct_eq_zero_of_topologicalKrullDim_le`, which is deduced from
the theorem here.

## References

* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-! ### The step at a pair of effective Cartier divisors -/

/-- An iterated cap at a list known to be `[O]` is that one cap. -/
private theorem iteratedChernCapOnChow_eq_capOnChow_of_eq_singleton {P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] {Os : List (ChernCapOperator C sP)}
    {O : ChernCapOperator C sP} (h : Os = [O]) (k : ℤ) (x : chowGroup C sP (k + (Os.length : ℤ)))
    (y : chowGroup C sP (k + 1)) (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP Os k x = O.capOnChow C sP k y := by
  subst h
  exact iteratedChernCapOnChow_singleton_eq C sP O k x y hxy

/-- An iterated cap at a list known to be `Ps ++ [O]` caps by `O` first, then iterates `Ps`. -/
private theorem iteratedChernCapOnChow_eq_of_eq_append_singleton {P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] {Os Ps : List (ChernCapOperator C sP)}
    {O : ChernCapOperator C sP} (h : Os = Ps ++ [O]) (k : ℤ)
    (x : chowGroup C sP (k + (Os.length : ℤ))) (y : chowGroup C sP (k + (Ps.length : ℤ) + 1))
    (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP Os k x =
      iteratedChernCapOnChow C sP Ps k (O.capOnChow C sP (k + (Ps.length : ℤ)) y) := by
  subst h
  have hy := chowGroupCast_heq C sP (show k + (Ps.length : ℤ) + 1 =
    k + (Ps.length : ℤ) + ([O].length : ℤ) by simp) y
  rw [iteratedChernCapOnChow_append C sP Ps [O] k x _ (hxy.trans hy.symm),
    iteratedChernCapOnChow_singleton_eq C sP O _ _ y hy]

section Step

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

omit [LocallyOfFiniteType sX] in
/-- **The inductive step of Stacks 0FDX at a pair of effective Cartier divisors.**

Let `D` and `D'` be effective Cartier divisors on `X` with `ℒ ⊗ 𝒪_X(D') ≅ 𝒪_X(D)` — the
presentation of `ℒ` that Stacks 0AYM delivers — and let `ℒ_1, …, ℒ_n` be further invertible
`𝒪_X`-modules. If the product `c₁(ℒ_1) ∩ ⋯ ∩ c₁(ℒ_n) ∩ −` annihilates every Chow class of every
test scheme over `D` and over `D'`, then on every test scheme `u : T ⟶ X` locally of finite type

  `c₁(u^*ℒ_1) ∩ ⋯ ∩ c₁(u^*ℒ_n) ∩ c₁(u^*ℒ) ∩ y = 0`.

This is `Stacks.Chow.iteratedChernCapOnChow_capOnChow_eq_zero_of_tensorObj` with the zero scheme
of the canonical section of `𝒪_X(D)` recognized as `D` (Stacks 01WX, in the form
`Stacks.Divisors.zeroScheme_canonicalSection`), which is what makes the dimension drop of
`Stacks.Chow.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor` applicable to it. -/
theorem iteratedChernCapOnChow_capOnChow_eq_zero_of_effectiveCartierDivisors (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (D D' : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Stacks.Divisors.IsEffectiveCartierDivisor D']
    (eM : Scheme.Modules.tensorObj M (Stacks.Divisors.divisorSheaf D') ≅
      Stacks.Divisors.divisorSheaf D)
    {n : ℕ} (N : Fin n → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N i)]
    (IH : ∀ (T' : Scheme.{u}) (g : T' ⟶ D.subscheme) (_ : LocallyOfFiniteType g) (u' : T' ⟶ X)
      (_ : LocallyOfFiniteType u') (_ : g ≫ D.subschemeι = u') (q' : T' ⟶ C.S)
      (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
      (β : chowGroup C q' (m + ((List.ofFn fun i =>
        invCap C q' ((Scheme.Modules.pullback u').obj (N i))).length : ℤ))),
      iteratedChernCapOnChow C q'
        (List.ofFn fun i => invCap C q' ((Scheme.Modules.pullback u').obj (N i))) m β = 0)
    (IH' : ∀ (T' : Scheme.{u}) (g : T' ⟶ D'.subscheme) (_ : LocallyOfFiniteType g) (u' : T' ⟶ X)
      (_ : LocallyOfFiniteType u') (_ : g ≫ D'.subschemeι = u') (q' : T' ⟶ C.S)
      (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
      (β : chowGroup C q' (m + ((List.ofFn fun i =>
        invCap C q' ((Scheme.Modules.pullback u').obj (N i))).length : ℤ))),
      iteratedChernCapOnChow C q'
        (List.ofFn fun i => invCap C q' ((Scheme.Modules.pullback u').obj (N i))) m β = 0)
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (hq : u ≫ sX = q) (k : ℤ)
    (y : chowGroup C q (k +
      ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ) + 1)) :
    iteratedChernCapOnChow C q
        (List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))) k
        ((invCap C q ((Scheme.Modules.pullback u).obj M)).capOnChow C q
          (k + ((List.ofFn fun i =>
            invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ)) y) = 0 := by
  refine iteratedChernCapOnChow_capOnChow_eq_zero_of_tensorObj C sX M
    (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.divisorSheaf D')
    (Stacks.Divisors.divisorSheafGlobalSection D) (Stacks.Divisors.divisorSheafGlobalSection D')
    eM N ?_ ?_ u q hq k y
  · rw [show Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.divisorSheafGlobalSection D) = D from
      Stacks.Divisors.zeroScheme_canonicalSection D]
    exact IH
  · rw [show Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf D')
        (Stacks.Divisors.divisorSheafGlobalSection D') = D' from
      Stacks.Divisors.zeroScheme_canonicalSection D']
    exact IH'

omit [LocallyOfFiniteType sX] in
/-- **The inductive step of Stacks 0FDX read on a family indexed by `Fin (n + 1)`**, the last
member `ℒ_{n+1}` being the one that Stacks 0AYM presents as a difference of the effective Cartier
divisors `D` and `D'`. The inductive hypothesis is carried for the first `n` members.

The list of cap operators of the whole family splits as the list of the first `n` followed by the
operator of the last (`List.ofFn_succ'`), the head of a list being applied last, so the operator
of `ℒ_{n+1}` acts first — which is the one the source decomposes into divisors. -/
theorem iteratedChernCapOnChow_ofFn_succ_eq_zero_of_effectiveCartierDivisors {n : ℕ}
    (N : Fin (n + 1) → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N i)]
    (D D' : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Stacks.Divisors.IsEffectiveCartierDivisor D']
    (eM : Scheme.Modules.tensorObj (N (Fin.last n)) (Stacks.Divisors.divisorSheaf D') ≅
      Stacks.Divisors.divisorSheaf D)
    (IH : ∀ (T' : Scheme.{u}) (g : T' ⟶ D.subscheme) (_ : LocallyOfFiniteType g) (u' : T' ⟶ X)
      (_ : LocallyOfFiniteType u') (_ : g ≫ D.subschemeι = u') (q' : T' ⟶ C.S)
      (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
      (β : chowGroup C q' (m + ((List.ofFn fun i : Fin n =>
        invCap C q' ((Scheme.Modules.pullback u').obj (N i.castSucc))).length : ℤ))),
      iteratedChernCapOnChow C q'
        (List.ofFn fun i : Fin n =>
          invCap C q' ((Scheme.Modules.pullback u').obj (N i.castSucc))) m β = 0)
    (IH' : ∀ (T' : Scheme.{u}) (g : T' ⟶ D'.subscheme) (_ : LocallyOfFiniteType g) (u' : T' ⟶ X)
      (_ : LocallyOfFiniteType u') (_ : g ≫ D'.subschemeι = u') (q' : T' ⟶ C.S)
      (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
      (β : chowGroup C q' (m + ((List.ofFn fun i : Fin n =>
        invCap C q' ((Scheme.Modules.pullback u').obj (N i.castSucc))).length : ℤ))),
      iteratedChernCapOnChow C q'
        (List.ofFn fun i : Fin n =>
          invCap C q' ((Scheme.Modules.pullback u').obj (N i.castSucc))) m β = 0)
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (hq : u ≫ sX = q) (k : ℤ)
    (α : chowGroup C q
      (k + ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ))) :
    iteratedChernCapOnChow C q
      (List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))) k α = 0 := by
  rw [iteratedChernCapOnChow_eq_of_eq_append_singleton C q
    (by rw [List.ofFn_succ', List.concat_eq_append]) k α
    (chowGroupCast C q (by simp; ring) α) (chowGroupCast_heq C q _ α).symm]
  exact iteratedChernCapOnChow_capOnChow_eq_zero_of_effectiveCartierDivisors C sX
    (N (Fin.last n)) D D' eM (fun i : Fin n => N i.castSucc) IH IH' u q hq k _

end Step

/-! ### Stacks 0FDX on every test scheme -/

/-- **Stacks 0FDX, on every test scheme locally of finite type.**

Let `X` be locally of finite type over the base scheme of chapter 42, Noetherian, and carrying an
ample invertible module `A`, and let `dim X ≤ d`. For invertible `𝒪_X`-modules `ℒ_1, …, ℒ_{d+1}`
and every test scheme `u : T ⟶ X` locally of finite type,

  `c₁(u^*ℒ_1) ∩ ⋯ ∩ c₁(u^*ℒ_{d+1}) ∩ α = 0`   for every Chow class `α` of `T`.

No bound is placed on the dimension of `T`: this is the cap-level content of the vanishing of
`c₁(ℒ_1) ∘ ⋯ ∘ c₁(ℒ_{d+1})` in `A^{d+1}(X)`, which by Stacks 02UC is exactly the vanishing of
the cap operation on every such `T`, and it is what the source's induction on `d` establishes.

The proof is that induction. The base case `d = 0` is
`Stacks.Chow.invCap_capOnChow_pullback_eq_zero_of_topologicalKrullDim_le_zero`; the step is
`Stacks.Chow.iteratedChernCapOnChow_ofFn_succ_eq_zero_of_effectiveCartierDivisors` applied to the
two effective Cartier divisors Stacks 0AYM produces from `ℒ_{d+2}` and the ample module, with the
inductive hypothesis transported to each of them along the closed immersion.

The ample invertible module is used only through Stacks 0AYM, and Noetherianness only through
Stacks 0AYM and the dimension drop; both follow from the source's hypothesis that `X` be of
finite type over the base, the base being locally Noetherian. -/
theorem iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le (d : ℕ) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsNoetherian X] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (N : Fin (d + 1) → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N i)]
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (hq : u ≫ sX = q) (k : ℤ)
    (α : chowGroup C q
      (k + ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ))) :
    iteratedChernCapOnChow C q
      (List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))) k α = 0 := by
  have key : ∀ (d : ℕ) (X : Scheme.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsNoetherian X]
      (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] (_ : Stacks.Ample.IsAmple X A)
      (_ : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (N : Fin (d + 1) → X.Modules)
      [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
        (N i)]
      (T : Scheme.{u}) (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S)
      [LocallyOfFiniteType q] (_ : u ≫ sX = q) (k : ℤ)
      (α : chowGroup C q (k + ((List.ofFn fun i =>
        invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ))),
      iteratedChernCapOnChow C q
        (List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))) k α = 0 := by
    intro d
    induction d with
    | zero =>
      intro X sX _ _ A _ _ hdim N _ T u _ q _ hqe k α
      rw [iteratedChernCapOnChow_eq_capOnChow_of_eq_singleton C q
        (O := invCap C q ((Scheme.Modules.pullback u).obj (N 0))) (by simp [List.ofFn_succ]) k α
        (chowGroupCast C q (by simp) α) (chowGroupCast_heq C q _ α).symm]
      exact invCap_capOnChow_pullback_eq_zero_of_topologicalKrullDim_le_zero C sX u q hqe
        (by simpa using hdim) (N 0) k _
    | succ d ih =>
      intro X sX _ _ A _ hA hdim N _ T u _ q _ hqe k α
      -- Stacks 0AYM: the last module is a difference of two effective Cartier divisors
      have : Stacks.Ample.IsInvertibleModule X (N (Fin.last (d + 1))) :=
        (inferInstance : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
          X.ringCatSheaf.property (N (Fin.last (d + 1))))
      obtain ⟨D, D', hD, hD', -, -, ⟨e⟩⟩ :=
        InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf A hA
          (N (Fin.last (d + 1))) (E := (∅ : Set X)) Set.finite_empty
      have := hD
      have := hD'
      have eM : Scheme.Modules.tensorObj (N (Fin.last (d + 1)))
          (Stacks.Divisors.divisorSheaf D') ≅ Stacks.Divisors.divisorSheaf D :=
        (Stacks.SheafOfModules.tensorObjIso X.sheaf.obj X.ringCatSheaf.property
          (N (Fin.last (d + 1))) (Stacks.Divisors.invertibleSheaf' D')).symm ≪≫ e
      -- the inductive hypothesis on an effective Cartier divisor of `X`
      have step : ∀ (E : X.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor E)
          (T' : Scheme.{u}) (g : T' ⟶ E.subscheme) (_ : LocallyOfFiniteType g) (u' : T' ⟶ X)
          (_ : LocallyOfFiniteType u') (_ : g ≫ E.subschemeι = u') (q' : T' ⟶ C.S)
          (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
          (β : chowGroup C q' (m + ((List.ofFn fun i : Fin (d + 1) =>
            invCap C q' ((Scheme.Modules.pullback u').obj (N i.castSucc))).length : ℤ))),
          iteratedChernCapOnChow C q'
            (List.ofFn fun i : Fin (d + 1) =>
              invCap C q' ((Scheme.Modules.pullback u').obj (N i.castSucc))) m β = 0 := by
        intro E hE T' g hg u' hu' hgu q' hq' hq'e m β
        subst hgu
        have := hE
        have := hg
        have := hq'
        have : IsNoetherian (E.subscheme : Scheme.{u}) :=
          AlgebraicGeometry.isNoetherian_source_of_isProper E.subschemeι
        have : Stacks.Ample.IsInvertibleModule E.subscheme
            ((Scheme.Modules.pullback E.subschemeι).obj A) :=
          Stacks.AlgebraicGeometry.AmpleLimit.algebraicGeometryIsInvertible_pullback
            E.subschemeι A
        have hdc : m + ((List.ofFn fun i : Fin (d + 1) => invCap C q'
              ((Scheme.Modules.pullback (g ≫ E.subschemeι)).obj (N i.castSucc))).length : ℤ) =
            m + ((List.ofFn fun i : Fin (d + 1) => invCap C q' ((Scheme.Modules.pullback g).obj
              ((Scheme.Modules.pullback E.subschemeι).obj (N i.castSucc)))).length : ℤ) := by
          simp
        -- the iterated pullback and the pullback along the composite agree (Stacks 01CD)
        have e : ∀ i : Fin (d + 1), (Scheme.Modules.pullback g).obj
              ((Scheme.Modules.pullback E.subschemeι).obj (N i.castSucc)) ≅
            (Scheme.Modules.pullback (g ≫ E.subschemeι)).obj (N i.castSucc) :=
          fun i => (Scheme.Modules.pullbackComp g E.subschemeι).app (N i.castSucc)
        refine (iteratedChernCapOnChow_congr_forall₂ C q'
          (forall₂_ofFn fun i => fun m' z => invCap_capOnChow_congr C q' _ _
            (e i).symm m' z) m β
          (chowGroupCast C q' hdc β) (chowGroupCast_heq C q' hdc β).symm).trans ?_
        exact ih E.subscheme (E.subschemeι ≫ sX)
          ((Scheme.Modules.pullback E.subschemeι).obj A)
          (Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion E.subschemeι A hA)
          (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor E hE
            (by exact_mod_cast hdim))
          (fun i : Fin (d + 1) => (Scheme.Modules.pullback E.subschemeι).obj (N i.castSucc))
          T' g q' (by rw [← Category.assoc]; exact hq'e) m _
      exact iteratedChernCapOnChow_ofFn_succ_eq_zero_of_effectiveCartierDivisors C sX N D D' eM
        (step D hD) (step D' hD') u q hqe k α
  exact key d X sX A hA hdim N T u q hq k α

end Stacks.Chow

end
