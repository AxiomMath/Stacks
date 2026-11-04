module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleShift

/-!
# The Chern class cap products of two modules commute

Let `X` be locally of finite type over the base of chapter 42 and let `ℰ`, `ℱ` be finite locally
free `𝒪_X`-modules of ranks `r` and `s`. Then

  `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α`  in  `A_{k-i-j}(X)`,  for `α ∈ A_k(X)`,

for the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6]. This is the
displayed identity of [Stacks, Tag 02UA].

## Main definitions

* `Stacks.Chow.GenuineChern.chernLowering` — `c_j(ℱ) ∩ -` as an operation lowering degrees by
  `j`.

## Main results

* `Stacks.Chow.GenuineChern.chernLowering_flatPullbackChow` — flat pullback carries
  `c_j(ℱ) ∩ -` to `c_j(π^*ℱ) ∩ -`.
* `Stacks.Chow.GenuineChern.chernLowering_invCap_comm` — `c_j(ℱ) ∩ -` commutes with the cap
  product with the first Chern class of an invertible module.
* `Stacks.Chow.GenuineChern.bundleChernCapFamily_chernCap` — for `ℰ` of rank `n + 1`, the family
  attached by `ℰ` to `c_j(ℱ) ∩ α` is `i ↦ c_j(ℱ) ∩ c_i(ℰ) ∩ α`.
* `Stacks.Chow.GenuineChern.chernCap_chernCap_comm` — `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α`.

## References

* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- A Chern class cap product absorbs a transport of its source degree. -/
theorem chernCap_chowGroupCast (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] {a a' : ℤ}
    (ha : a = a') (j : Fin (r + 1)) (x : chowGroup C sX a) :
    chernCap C r sX F a' j (chowGroupCast C sX ha x) =
      chowGroupCast C sX (by omega) (chernCap C r sX F a j x) := by
  subst ha; rfl

/-- `c_j(ℱ) ∩ - : A_a(X) ⟶ A_b(X)` for `a = b + j`, as an operation lowering degrees by `j`. -/
def chernLowering (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (j : Fin (r + 1)) : ChowLowering C sX (j : ℤ) := fun a b h ↦
  (chowGroupCast C sX (show a - (j : ℤ) = b by omega)).toAddMonoidHom.comp (chernCap C r sX F a j)

/-- The lowering operation `c_j(ℱ) ∩ -` acts by the cap product `chernCap`, transported along
the equality of degrees. -/
@[simp]
theorem chernLowering_apply (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (j : Fin (r + 1)) (a b : ℤ) (h : a = b + (j : ℤ)) (x : chowGroup C sX a) :
    chernLowering C sX F r j a b h x =
      chowGroupCast C sX (by omega) (chernCap C r sX F a j x) :=
  rfl

/-- Flat pullback along `π` carries the lowering operation `c_j(ℱ) ∩ -` to `c_j(π^*ℱ) ∩ -`. -/
theorem chernLowering_flatPullbackChow {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
    (d : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π d)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP d hπ k)
    (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (j : Fin (r + 1)) (a b : ℤ) (h : a = b + (j : ℤ)) (x : chowGroup C sX a) :
    letI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r π
    chernLowering C sP ((Scheme.Modules.pullback π).obj F) r j (a + d) (b + d) (by omega)
        (flatPullbackChow C sP sX π hsP d hπ a (hfac a) x) =
      flatPullbackChow C sP sX π hsP d hπ b (hfac b) (chernLowering C sX F r j a b h x) := by
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r π
  refine eq_of_heq ?_
  rw [chernLowering_apply, chernLowering_apply]
  refine (chowGroupCast_heq C sP _ _).trans ?_
  refine (chernCap_flatPullback_heq C sX sP π hsP d hπ F r ((Scheme.Modules.pullback π).obj F)
    (Iso.refl _) a j (hfac a) (hfac (a - (j : ℤ))) x).trans ?_
  exact flatPullbackChow_heq_of_degree C sP sX π hsP d hπ (by omega) _ _
    (chowGroupCast_heq C sX _ _).symm

/-- The lowering operation `c_j(ℱ) ∩ -` commutes with the cap product with the first Chern class
of an invertible module. -/
theorem chernLowering_invCap_comm (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (j : Fin (r + 1)) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (b c : ℤ) (h : b = c + (j : ℤ)) (x : chowGroup C sX (b + 1)) :
    chernLowering C sX F r j b c h ((invCap C sX M).capOnChow C sX b x) =
      (invCap C sX M).capOnChow C sX c
        (chernLowering C sX F r j (b + 1) (c + 1) (by omega) x) := by
  rw [chernLowering_apply, chernLowering_apply, chernCap_invCap_comm,
    ← capOnChow_chowGroupCast C sX (invCap C sX M) (show b - (j : ℤ) = c by omega) (by omega),
    chowGroupCast_chowGroupCast]

/-- For a module `ℰ` of rank `n + 1`, the `i`-th member of the family `bundleChernCapFamily`
attached by `ℰ` to `c_j(ℱ) ∩ α` is `c_j(ℱ) ∩ c_i(ℰ) ∩ α`. -/
theorem bundleChernCapFamily_chernCap (E : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (k : ℤ) (j : Fin (r + 1)) (α : chowGroup C sX k) :
    bundleChernCapFamily E n C sX (k - (j : ℤ)) (chernCap C r sX F k j α) =
      fun i : Fin (n + 1 + 1) ↦ chowGroupCast C sX (by omega)
        (chernCap C r sX F (k - (i : ℤ)) j (bundleChernCapFamily E n C sX k α i)) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r (bundleProj E)
  have hfac := fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _
    (relativeDimension_bundleProj E n) k
  have hcompat := chernTermsCompatibleWithLowering_of C sX (bundleProj E ≫ sX) (bundleProj E) rfl
    (n + 1) (relativeDimension_bundleProj E n)
    hfac
    (bundleTwistCap E C sX) (j : ℤ) (chernLowering C sX F r j)
    (chernLowering C _ ((Scheme.Modules.pullback (bundleProj E)).obj F) r j)
    (fun a b h x ↦ chernLowering_flatPullbackChow C sX (bundleProj E ≫ sX) (bundleProj E)
      rfl (n + 1 - 1) (relativeDimension_bundleProj E n)
      hfac F r j
      a b h x)
    (fun b c h x ↦ chernLowering_invCap_comm C (bundleProj E ≫ sX)
      ((Scheme.Modules.pullback (bundleProj E)).obj F) r j (bundleTwist E) b c h x)
  have hfam := isChernCapFamily_lowering C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
    (relativeDimension_bundleProj E n)
    hfac
    (bundleTwistCap E C sX) (j : ℤ) _ _ hcompat k (k - (j : ℤ)) (by omega) α _
    (isChernCapFamily_bundleChernCapFamily E n C sX k α)
  exact (eq_bundleChernCapFamily_of_isChernCapFamily E n C sX (k - (j : ℤ)) _ _ hfam).symm

/-- The Chern class cap products of two modules commute: for `ℰ` and `ℱ` finite locally free of
ranks `r` and `s` on `X` and `α ∈ A_k(X)`,

  `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α`  in  `A_{k-i-j}(X)`,

the two sides being read in `A_{k-j-i}(X)` and `A_{k-i-j}(X)`. -/
theorem chernCap_chernCap_comm (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (F : X.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s]
    (k : ℤ) (i : Fin (r + 1)) (j : Fin (s + 1)) (α : chowGroup C sX k) :
    chernCap C r sX E (k - (j : ℤ)) i (chernCap C s sX F k j α) =
      chowGroupCast C sX (by omega)
        (chernCap C s sX F (k - (i : ℤ)) j (chernCap C r sX E k i α)) := by
  cases r with
  | zero =>
    rw [chernCap_zero, chernCap_zero, chernCap_chowGroupCast, chowGroupCast_chowGroupCast]
  | succ n =>
    rw [chernCap_succ, chernCap_succ, bundleChernCap_apply, bundleChernCap_apply,
      bundleChernCapFamily_chernCap]

end Stacks.Chow.GenuineChern

end
