module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFirstOrderComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsToPairsEquivalence
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimitTensorShift

/-!
# The comparison datum of [Stacks, Tag 07JG] on `M = lim_e M_e`, with no finiteness

`Crystalline.FirstOrderComparison.ofLevels` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelComparisonInterchange.lean` assembles the
*uncompleted* comparison datum of [Stacks, Lemma 60.17.3, Tag 07JG] on the limit module
`M = lim_e M_e` out of the comparison data of the levels, and it costs a basis of `Ω` **indexed by
a finite type**.  That hypothesis is not an artefact: the interchange it runs on,

`(D ⊕ Ω) ⊗_D M ≅ lim_e ((D ⊕ Ω) ⊗_D M_e)`,

is not surjective for `Ω` free of infinite rank, and surjectivity is what the assembly consumes.
The source's presentation is `P = A[x_i]` for an arbitrary family of variables, so the finite case
is not the source's case.

**This module removes the hypothesis.**  The datum is assembled over the *completed* base change
`(D ⊕ Ω) ⊗̂_D M` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedFirstOrderComparison.lean`, where the
interchange is

`(D ⊕ Ω) ⊗̂_D M ≅ lim_e ((D ⊕ Ω) ⊗_D M_e)`

and holds for **every** module of differentials, by
`Crystalline.tensorCompletionLevelEquiv`.  What replaces the basis is the statement that the levels
are the quotients of `M` by the shifted `p`-adic filtration: the reductions `r_e : M ⟶ M_e` are
surjective with `ker (r_e) = p^{N+e} M`.  For a quasi-coherent crystal over the system of
[Stacks, Proposition 60.21.1, Tag 07JN] that is a theorem,
`...SmallSite.mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero`; the source's own route to it is
the footnote at [Stacks, Lemma 60.19.3, Tag 07LF].  Nothing about `Ω` is assumed at all.

So item (07JC) of [Stacks, Lemma 60.17.3, Tag 07JG] — the connection on `M = lim_e M_e` with its
Leibniz rule — needs neither `[Fintype ι]` nor any basis of `Ω` once the comparison datum is read
over the completed base change.  The level-by-level comparison datum is an input here; what
changes is the price of passing from the levels to the limit.

## Main definitions

* `Crystalline.completedLevelProj` — the level-`e` readout of the completed base change.
* `Crystalline.levelComparisonTower` — the level-by-level comparison values of an element of `M`,
  as a compatible family.
* `Crystalline.completedLevelComparisonFun` — the comparison map on `M`, that family read back
  across the completed interchange.
* `Crystalline.CompletedFirstOrderComparison.ofLevels` — **the completed comparison datum on
  `M`**, its three clauses checked level by level.

## Main results

* `Crystalline.completedLevelProj_completedLevelComparisonFun` — the comparison map on `M` is the
  one with the prescribed values at the levels, which together with
  `Crystalline.completedLevelProj_injective` determines it.
* `Crystalline.completedLevelComparisonFun_naturality` — **the naturality of the completed
  interchange**: a map of towers compatible with the level data induces the naturality of the
  limit data.
* `Crystalline.completedConnection_ofLevels_apply` — the connection of the assembled datum is the
  completion of the differential components of the level data, so item (07JC) of the tag holds
  over an arbitrary module of differentials.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open scoped TensorProduct

universe u w

noncomputable section

namespace Crystalline

section CompletedOfLevels

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ}
  (M₀ : Type w) [AddCommGroup M₀] [Module (D : Type u) M₀]
  (lev : ℕ → Type w) [∀ n, AddCommGroup (lev n)] [∀ n, Module (D : Type u) (lev n)]
  (trans : ∀ n, lev (n + 1) →ₗ[(D : Type u)] lev n) (N : ℕ)
  (r : ∀ n, M₀ →ₗ[(D : Type u)] lev n)
  (hsurj : ∀ n, Function.Surjective (r n))
  (hker : ∀ n, LinearMap.ker (r n) =
    DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + n) •
      (⊤ : Submodule (D : Type u) M₀))
  (hcomp : ∀ n, trans n ∘ₗ r (n + 1) = r n)

/-! ### The two level readouts -/

include hsurj hker in
/-- **The level-`e` readout of the completed base change `(D ⊕ Ω) ⊗̂_D M`.** -/
def completedLevelProj (n : ℕ) :
    CompletedFirstOrderTensor D Omega p M₀ →ₗ[(D : Type u)]
      firstOrderExtension D Omega ⊗[D] lev n :=
  tensorCompletionLevel (firstOrderExtension D Omega) M₀ lev N r hsurj hker n

include hker in
/-- **The level-`e` readout of the completion of `M` itself.**  The reduction clause of a completed
comparison datum is an identity in `M̂`, and this is what checks it level by level. -/
def completedLimitProj (n : ℕ) :
    AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p) M₀ →ₗ[(D : Type u)] lev n :=
  completionLevel (DividedPowers.pAdicIdeal (A := (D : Type u)) p) M₀ lev N r hker n

include hsurj hker in
/-- The level-`n` readout of the image of `z` in the completed base change is the level-`n`
projection of `z`. -/
@[simp] theorem completedLevelProj_of (n : ℕ) (z : firstOrderExtension D Omega ⊗[D] M₀) :
    completedLevelProj M₀ lev N r hsurj hker n
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) _ z) =
      tensorLevelProj (firstOrderExtension D Omega) M₀ lev r n z :=
  rfl

include hker in
/-- The level-`n` readout of the image of `m` in the completion of `M` is `r n m`. -/
@[simp] theorem completedLimitProj_of (n : ℕ) (m : M₀) :
    completedLimitProj M₀ lev N r hker n
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) M₀ m) =
      r n m :=
  rfl

include hsurj hker in
/-- **The readouts of the completed base change separate its points**, which is what lets the
clauses of a comparison datum on `M` be checked one level at a time. -/
theorem completedLevelProj_injective {z z' : CompletedFirstOrderTensor D Omega p M₀}
    (h : ∀ n, completedLevelProj M₀ lev N r hsurj hker n z =
      completedLevelProj M₀ lev N r hsurj hker n z') :
    z = z' :=
  tensorCompletionLevel_injective (firstOrderExtension D Omega) M₀ lev N r hsurj hker h

include hsurj hker in
/-- **The readouts of the completion of `M` separate its points.** -/
theorem completedLimitProj_injective
    {z z' : AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p) M₀}
    (h : ∀ n, completedLimitProj M₀ lev N r hker n z =
      completedLimitProj M₀ lev N r hker n z') :
    z = z' :=
  completionLevel_injective (DividedPowers.pAdicIdeal (A := (D : Type u)) p) M₀ lev N r hker
    hsurj h

/-- The level-`n` readout of the completion of a map of base changes is the level map applied to
the readout. -/
private theorem completedLevelProj_map_apply {M₁ : Type w} [AddCommGroup M₁]
    [Module (D : Type u) M₁] {lev' : ℕ → Type w} [∀ n, AddCommGroup (lev' n)]
    [∀ n, Module (D : Type u) (lev' n)] {r' : ∀ n, M₁ →ₗ[(D : Type u)] lev' n}
    (hsurj' : ∀ n, Function.Surjective (r' n))
    (hker' : ∀ n, LinearMap.ker (r' n) =
      DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + n) •
        (⊤ : Submodule (D : Type u) M₁))
    (Ψ : firstOrderExtension D Omega ⊗[D] M₀ →ₗ[(D : Type u)] firstOrderExtension D Omega ⊗[D] M₁)
    (Ψn : ∀ n, firstOrderExtension D Omega ⊗[D] lev n →ₗ[(D : Type u)]
      firstOrderExtension D Omega ⊗[D] lev' n)
    (hΨ : ∀ n, Ψn n ∘ₗ tensorLevelProj (firstOrderExtension D Omega) M₀ lev r n =
      tensorLevelProj (firstOrderExtension D Omega) M₁ lev' r' n ∘ₗ Ψ) (n : ℕ)
    (z : CompletedFirstOrderTensor D Omega p M₀) :
    completedLevelProj M₁ lev' N r' hsurj' hker' n
        (AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p) Ψ z) =
      Ψn n (completedLevelProj M₀ lev N r hsurj hker n z) := by
  rw [completedLevelProj, tensorCompletionLevel,
    completionLevel_map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
      (firstOrderExtension D Omega ⊗[D] M₀) (fun n ↦ firstOrderExtension D Omega ⊗[D] lev n) N
      (tensorLevelProj (firstOrderExtension D Omega) M₀ lev r)
      (ker_tensorLevelProj (firstOrderExtension D Omega) M₀ lev N r hsurj hker)
      (firstOrderExtension D Omega ⊗[D] M₁)
      (fun n ↦ firstOrderExtension D Omega ⊗[D] lev' n)
      (tensorLevelProj (firstOrderExtension D Omega) M₁ lev' r')
      (ker_tensorLevelProj (firstOrderExtension D Omega) M₁ lev' N r' hsurj' hker')
      Ψ Ψn hΨ n]
  rfl

/-! ### The comparison map on `M` -/

variable (c : ∀ n, FirstOrderComparison A D g Omega d (lev n))
  (hc : ∀ (n : ℕ) (x : lev (n + 1)),
    LinearMap.lTensor (firstOrderExtension D Omega) (trans n) (c (n + 1) x) = c n (trans n x))

include hcomp hc in
/-- **The level-by-level comparison values of an element of `M`, as a compatible family.**  The
family is compatible because the comparison maps of the levels are, which is the hypothesis `hc`,
and because the reductions of `M` to the levels are, which is `hcomp`. -/
def levelComparisonTower (m : M₀) :
    ↥(invLimitTensor (firstOrderExtension D Omega) lev trans) :=
  ⟨fun n ↦ c n (r n m), fun n ↦ by
    change LinearMap.lTensor (firstOrderExtension D Omega) (trans n) (c (n + 1) (r (n + 1) m)) = _
    rw [hc n (r (n + 1) m), ← LinearMap.comp_apply, hcomp n]⟩

include hcomp hc in
/-- The level-`n` component of `levelComparisonTower` at `m` is `c n (r n m)`. -/
@[simp] theorem levelComparisonTower_val (m : M₀) (n : ℕ) :
    (levelComparisonTower M₀ lev trans r hcomp c hc m).val n = c n (r n m) :=
  rfl

include hsurj hker hcomp hc in
/-- **The comparison map on `M = lim_e M_e`, over the completed base change**: the level-by-level
comparison values read back across the completed interchange
`Crystalline.tensorCompletionLevelEquiv`. -/
def completedLevelComparisonFun (m : M₀) : CompletedFirstOrderTensor D Omega p M₀ :=
  (tensorCompletionLevelEquiv (firstOrderExtension D Omega) M₀ lev trans N r hsurj hker
    hcomp).symm (levelComparisonTower M₀ lev trans r hcomp c hc m)

include hsurj hker hcomp hc in
/-- **The comparison map on `M` is the one with the prescribed values at the levels.**  Together
with `Crystalline.completedLevelProj_injective` this determines it. -/
@[simp] theorem completedLevelProj_completedLevelComparisonFun (m : M₀) (n : ℕ) :
    completedLevelProj M₀ lev N r hsurj hker n
        (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc m) =
      c n (r n m) := by
  change (tensorCompletionLevelEquiv (firstOrderExtension D Omega) M₀ lev trans N r hsurj hker hcomp
      ((tensorCompletionLevelEquiv (firstOrderExtension D Omega) M₀ lev trans N r hsurj hker
        hcomp).symm (levelComparisonTower M₀ lev trans r hcomp c hc m))).val n = _
  rw [LinearEquiv.apply_symm_apply, levelComparisonTower_val]

/-! ### The three clauses -/

include hsurj hker hcomp hc in
/-- **The reduction clause**, checked level by level: the reduction of the comparison map modulo
`Ω` is the canonical map `M → M̂`.  At the level `e` both sides are the component of `m`, by the
reduction clause of the datum of the level. -/
theorem reduction_completedLevelComparisonFun (m : M₀) :
    AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderReduction D Omega M₀)
        (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc m) =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) M₀ m := by
  refine completedLimitProj_injective M₀ lev N r hsurj hker fun n ↦ ?_
  rw [completedLimitProj, completionLevel_map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
      (firstOrderExtension D Omega ⊗[D] M₀) (fun n ↦ firstOrderExtension D Omega ⊗[D] lev n) N
      (tensorLevelProj (firstOrderExtension D Omega) M₀ lev r)
      (ker_tensorLevelProj (firstOrderExtension D Omega) M₀ lev N r hsurj hker) M₀ lev r hker
      (firstOrderReduction D Omega M₀) (fun n ↦ firstOrderReduction D Omega (lev n))
      (fun n ↦ LinearMap.ext fun z ↦ firstOrderReduction_lTensor D Omega M₀ (lev n) (r n) z) n]
  change firstOrderReduction D Omega (lev n)
      (completedLevelProj M₀ lev N r hsurj hker n
        (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc m)) = _
  rw [completedLevelProj_completedLevelComparisonFun, (c n).reduction']
  rfl

include hsurj hker hcomp hc in
/-- **The semilinearity clause**, checked level by level: at the level `e` it is the semilinearity
of the datum of the level, the multiplication by `p₁ f` commuting with the level projection of the
base change. -/
theorem semilinear_completedLevelComparisonFun (f : (D : Type u)) (m : M₀) :
    completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc (f • m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderMul D Omega M₀ (firstOrderP₁ A D g Omega d f))
        (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc m) := by
  refine completedLevelProj_injective M₀ lev N r hsurj hker fun n ↦ ?_
  rw [completedLevelProj_completedLevelComparisonFun,
    completedLevelProj_map_apply M₀ lev N r hsurj hker hsurj hker _
      (fun n ↦ firstOrderMul D Omega (lev n) (firstOrderP₁ A D g Omega d f))
      (fun n ↦ firstOrderMul_comp_lTensor D Omega M₀ (firstOrderP₁ A D g Omega d f) (r n)) n,
    completedLevelProj_completedLevelComparisonFun, firstOrderMul_apply,
    _root_.map_smul (r n) f m, (c n).semilinear']

include hsurj hker hcomp hc in
/-- **The completed comparison datum on `M = lim_e M_e`, from the comparison data of the levels.**

This is the restatement of `Crystalline.FirstOrderComparison.ofLevels` over the completed base
change, and the point of the restatement: **no basis of `Ω` and no finiteness of its index
appears**.  What replaces them is that the levels are the quotients of `M` by the shifted `p`-adic
filtration, which for a quasi-coherent crystal over the system of
[Stacks, Proposition 60.21.1, Tag 07JN] is a theorem.

All three clauses are checked level by level, by
`Crystalline.completedLevelProj_injective` and `Crystalline.completedLimitProj_injective`; nothing
about the tower is assumed beyond the compatibility `hc` of the data with its transition maps. -/
def CompletedFirstOrderComparison.ofLevels :
    CompletedFirstOrderComparison A D g Omega d p M₀ where
  toFun := completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc
  map_add' m m' :=
    completedLevelProj_injective M₀ lev N r hsurj hker fun n ↦ by
      rw [_root_.map_add (completedLevelProj M₀ lev N r hsurj hker n),
        completedLevelProj_completedLevelComparisonFun,
        completedLevelProj_completedLevelComparisonFun,
        completedLevelProj_completedLevelComparisonFun, _root_.map_add (r n), (c n).map_add']
  reduction' m :=
    reduction_completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc m
  semilinear' f m :=
    semilinear_completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc f m

include hsurj hker hcomp hc in
/-- The completed comparison datum `CompletedFirstOrderComparison.ofLevels` is given by the map
`completedLevelComparisonFun`. -/
@[simp] theorem CompletedFirstOrderComparison.ofLevels_apply (m : M₀) :
    CompletedFirstOrderComparison.ofLevels M₀ lev trans N r hsurj hker hcomp c hc m =
      completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc m :=
  rfl

include hsurj hker hcomp hc in
/-- **Item (07JC) of [Stacks, Lemma 60.17.3, Tag 07JG] on `M = lim_e M_e`, with no finiteness.**
The connection of the assembled datum is the completion of the differential component of the
comparison map; the Leibniz rule is
`Crystalline.CompletedFirstOrderComparison.completedConnection`. -/
theorem completedConnection_ofLevels_apply (m : M₀) :
    (CompletedFirstOrderComparison.ofLevels M₀ lev trans N r hsurj hker hcomp c
        hc).completedConnection m =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderDifferentialComm D Omega M₀)
        (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc m) :=
  rfl

end CompletedOfLevels

/-! ### Naturality -/

section Naturality

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ}
  (M₀ : Type w) [AddCommGroup M₀] [Module (D : Type u) M₀]
  (M₁ : Type w) [AddCommGroup M₁] [Module (D : Type u) M₁]
  (lev : ℕ → Type w) [∀ n, AddCommGroup (lev n)] [∀ n, Module (D : Type u) (lev n)]
  (trans : ∀ n, lev (n + 1) →ₗ[(D : Type u)] lev n)
  (lev' : ℕ → Type w) [∀ n, AddCommGroup (lev' n)] [∀ n, Module (D : Type u) (lev' n)]
  (trans' : ∀ n, lev' (n + 1) →ₗ[(D : Type u)] lev' n) (N : ℕ)
  (r : ∀ n, M₀ →ₗ[(D : Type u)] lev n) (r' : ∀ n, M₁ →ₗ[(D : Type u)] lev' n)
  (hsurj : ∀ n, Function.Surjective (r n))
  (hker : ∀ n, LinearMap.ker (r n) =
    DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + n) •
      (⊤ : Submodule (D : Type u) M₀))
  (hcomp : ∀ n, trans n ∘ₗ r (n + 1) = r n)
  (hsurj' : ∀ n, Function.Surjective (r' n))
  (hker' : ∀ n, LinearMap.ker (r' n) =
    DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + n) •
      (⊤ : Submodule (D : Type u) M₁))
  (hcomp' : ∀ n, trans' n ∘ₗ r' (n + 1) = r' n)

include hsurj hker hcomp hsurj' hker' hcomp' in
/-- **The completed interchange is natural.**  Given a `D`-linear map `M ⟶ M'` which at every
level is a `D`-linear map `M_e ⟶ M'_e` (the hypothesis `hphi`), and comparison data on the two
towers that the level maps carry into one another (the hypothesis `hnat`), the comparison maps on
the two limits are carried into one another too.

This is `Crystalline.levelComparisonFun_naturality` over the completed base change, and like the
three clauses of `Crystalline.CompletedFirstOrderComparison.ofLevels` it is proved by comparing the
two sides at each level. -/
theorem completedLevelComparisonFun_naturality
    (phi : M₀ →ₗ[(D : Type u)] M₁) (philev : ∀ n, lev n →ₗ[(D : Type u)] lev' n)
    (hphi : ∀ n, r' n ∘ₗ phi = philev n ∘ₗ r n)
    (c : ∀ n, FirstOrderComparison A D g Omega d (lev n))
    (hc : ∀ (n : ℕ) (x : lev (n + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (trans n) (c (n + 1) x) = c n (trans n x))
    (c' : ∀ n, FirstOrderComparison A D g Omega d (lev' n))
    (hc' : ∀ (n : ℕ) (x : lev' (n + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (trans' n) (c' (n + 1) x) =
        c' n (trans' n x))
    (hnat : ∀ (n : ℕ) (x : lev n),
      c' n (philev n x) = LinearMap.lTensor (firstOrderExtension D Omega) (philev n) (c n x))
    (m : M₀) :
    completedLevelComparisonFun M₁ lev' trans' N r' hsurj' hker' hcomp' c' hc' (phi m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (LinearMap.lTensor (firstOrderExtension D Omega) phi)
        (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp c hc m) := by
  refine completedLevelProj_injective M₁ lev' N r' hsurj' hker' fun n ↦ ?_
  have hpsi : ∀ n : ℕ,
      LinearMap.lTensor (firstOrderExtension D Omega) (philev n) ∘ₗ
          tensorLevelProj (firstOrderExtension D Omega) M₀ lev r n =
        tensorLevelProj (firstOrderExtension D Omega) M₁ lev' r' n ∘ₗ
          LinearMap.lTensor (firstOrderExtension D Omega) phi := by
    intro n
    rw [tensorLevelProj, tensorLevelProj, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp,
      hphi n]
  rw [completedLevelProj_completedLevelComparisonFun,
    completedLevelProj_map_apply M₀ lev N r hsurj hker hsurj' hker' _
      (fun n ↦ LinearMap.lTensor (firstOrderExtension D Omega) (philev n)) hpsi n,
    completedLevelProj_completedLevelComparisonFun,
    show r' n (phi m) = philev n (r n m) from LinearMap.congr_fun (hphi n) m, hnat n]

end Naturality

end Crystalline

end

end
