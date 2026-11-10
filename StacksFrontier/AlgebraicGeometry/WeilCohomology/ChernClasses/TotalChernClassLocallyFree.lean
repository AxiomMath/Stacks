module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass
import all StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Total Chern classes with pullback compatibility on finite locally free classes

`Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree` is the predicate of the three properties
of the total Chern class of [Stacks, Tag 0FI5], with property (2), `f^*c^A([ℰ]) = c^A([f^*ℰ])`,
asked on the classes of finite locally free modules `ℰ` and on all of `K₀(Vect(X))` for every
additive map carrying `[ℰ]` to `[f^*ℰ]`.

## Main definitions

* `Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree`: the three properties of
  [Stacks, Tag 0FI5].

## Main results

* `Stacks.WeilCohomology.eq_of_isTotalChernClassOnLocallyFree`: two such rules agree on the class
  of a finite locally free module of constant rank.
* `Stacks.WeilCohomology.ChernSetup.chernClass_of_gt`,
  `Stacks.WeilCohomology.ChernSetup.chernClass_central` and
  `Stacks.WeilCohomology.ChernSetup.chernClass_eq_of_relation`: the Chern classes of a module of
  constant rank vanish above the rank, are central, and are determined by equation 45.12.1.1.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- The three properties of the total Chern class of [Stacks, Tag 0FI5], property (2) read on
the classes of finite locally free modules and on all of `K₀(Vect(X))`. A rule `c` assigns to
every object `X` of `𝒞` and every class `α` of `K₀(Vect(X))` the components `c X α n` of its
total Chern class, the `n`-th lying in `A^n(X)`; it is multiplicative on sums, compatible with
pullback on the classes of modules, and takes the value `1 + c₁^A(ℒ)` on an invertible
module. -/
structure IsTotalChernClassOnLocallyFree (𝔄 : ChernSetup.{u, v, v₁, w} C S)
    (c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X) : Prop where
  /-- The `n`-th component lies in `A^n(X)`, so that `c` lands in `∏_{i ≥ 0} A^i(X)`. -/
  mem_grade : ∀ (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ), c X α n ∈ 𝔄.grade X n
  /-- Property (1): `c^A(α + β) = c^A(α) c^A(β)`, componentwise. -/
  map_add : ∀ (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ),
    c X (α + β) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c X α p.1 * c X β p.2
  /-- Property (1): `c^A(0) = 1`. -/
  map_zero : ∀ (X : C) (n : ℕ), c X 0 n = if n = 0 then 1 else 0
  /-- Property (2) on the class of a finite locally free module `ℰ`:
  `f^*c^A([ℰ]) = c^A([f^*ℰ])`. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj Y).ringCatSheaf) E → ∀ n : ℕ,
    𝔄.pull f (c Y (VectorBundleKZero.classOf (S.obj Y) E) n) =
      c X (VectorBundleKZero.classOf (S.obj X)
        ((Scheme.Modules.pullback (S.map f)).obj E)) n
  /-- Property (2) on all of `K₀(Vect(X))`: `f^* ∘ c^A = c^A ∘ f^*` for every additive map
  `κ : K₀(Vect(Y)) →+ K₀(Vect(X))` carrying `[ℰ]` to `[f^*ℰ]` for every finite locally free
  module `ℰ`. -/
  map_pull_kZero : ∀ {X Y : C} (f : X ⟶ Y)
    (κ : VectorBundleKZero (S.obj Y) →+ VectorBundleKZero (S.obj X)),
    (∀ E : (S.obj Y).Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := (S.obj Y).ringCatSheaf) E →
      κ (VectorBundleKZero.classOf (S.obj Y) E) =
        VectorBundleKZero.classOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj E)) →
    ∀ (α : VectorBundleKZero (S.obj Y)) (n : ℕ), 𝔄.pull f (c Y α n) = c X (κ α) n
  /-- Property (3): `c^A([ℒ]) = 1 + c₁^A(ℒ)` for an invertible module `ℒ`. -/
  invertible : ∀ (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ),
    c X (VectorBundleKZero.classOf (S.obj X) L) n =
      if n = 0 then 1 else if n = 1 then 𝔄.c₁ X (picardClassOf (S.obj X) L hL) else 0

/-- Two rules with the three properties agree on a sum of classes of invertible modules. -/
private theorem eq_on_sum_classOf_invertible_onLocallyFree {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    {c c' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hc : IsTotalChernClassOnLocallyFree 𝔄 c)
    (hc' : IsTotalChernClassOnLocallyFree 𝔄 c') (P : C) (k : ℕ) :
    ∀ (L : Fin k → (S.obj P).Modules)
      (_ : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
        (S.obj P).ringCatSheaf.2 (L j)) (n : ℕ),
      c P (∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) n =
        c' P (∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) n := by
  induction k with
  | zero =>
      intro L _ n
      simp [hc.map_zero, hc'.map_zero]
  | succ k ih =>
      intro L hL n
      rw [Fin.sum_univ_castSucc, hc.map_add, hc'.map_add]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [ih (fun j => L j.castSucc) (fun j => hL _) p.1,
        hc.invertible P (L (Fin.last k)) (hL _) p.2,
        hc'.invertible P (L (Fin.last k)) (hL _) p.2]

/-- Two rules satisfying `IsTotalChernClassOnLocallyFree` agree on the class of a finite locally
free module of constant rank. -/
theorem eq_of_isTotalChernClassOnLocallyFree {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    {c c' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hc : IsTotalChernClassOnLocallyFree 𝔄 c) (hc' : IsTotalChernClassOnLocallyFree 𝔄 c') (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (n : ℕ) :
    c X (VectorBundleKZero.classOf (S.obj X) E) n =
      c' X (VectorBundleKZero.classOf (S.obj X) E) n := by
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  refine hinj ?_
  rw [hc.map_pull p E hE.isFiniteLocallyFree n, hc'.map_pull p E hE.isFiniteLocallyFree n, hsum]
  exact eq_on_sum_classOf_invertible_onLocallyFree hc hc' P _ L hL n

namespace ChernSetup

variable (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C) (E : (S.obj X).Modules) (r : ℕ)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))

/-- The Chern classes vanish in degrees above the rank. -/
@[simp,
  sga "5 VII 3.3" "partial"]
theorem chernClass_of_gt {j : ℕ} (hj : r + 1 < j) : 𝔄.chernClass X E r hE j = 0 := by
  unfold chernClass
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

/-- The Chern classes `c_i^A(ℰ)` are central in `A(X)`. -/
theorem chernClass_central (j : ℕ) (b : 𝔄.A X) :
    𝔄.chernClass X E r hE j * b = b * 𝔄.chernClass X E r hE j := by
  have hx : ∀ (c : 𝔄.A (𝔄.bundleDatum X E r hE).bundle) (k : ℕ),
      𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ k * c =
        c * 𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ k :=
    fun c k => Commute.pow_left (𝔄.c₁_central _ _ c) k
  have htuple : ∀ i : Fin (r + 1),
      𝔄.chernTuple X E r hE i * b = b * 𝔄.chernTuple X E r hE i := by
    have hbf : ∑ i : Fin (r + 1),
        𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.chernTuple X E r hE i) =
        𝔄.topTerm X E r hE := 𝔄.bundleFormula_chernTuple X E r hE
    have heq : (fun i : Fin (r + 1) => 𝔄.chernTuple X E r hE i * b) =
        fun i : Fin (r + 1) => b * 𝔄.chernTuple X E r hE i := by
      refine (𝔄.bijective_bundleFormula X E r hE).injective ?_
      have hL : ∑ i : Fin (r + 1),
            𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
              𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.chernTuple X E r hE i * b) =
          𝔄.topTerm X E r hE * 𝔄.pull (𝔄.bundleDatum X E r hE).proj b := by
        rw [← hbf, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_assoc]
      have hR : ∑ i : Fin (r + 1),
            𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
              𝔄.pull (𝔄.bundleDatum X E r hE).proj (b * 𝔄.chernTuple X E r hE i) =
          𝔄.pull (𝔄.bundleDatum X E r hE).proj b * 𝔄.topTerm X E r hE := by
        rw [← hbf, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, ← mul_assoc, hx (𝔄.pull (𝔄.bundleDatum X E r hE).proj b) (i : ℕ),
          mul_assoc]
      change ∑ i : Fin (r + 1), _ * _ = ∑ i : Fin (r + 1), _ * _
      rw [hL, hR, topTerm, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm,
        hx (𝔄.pull (𝔄.bundleDatum X E r hE).proj b) (r + 1)]
    exact fun i => congrFun heq i
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [𝔄.chernClass_zero X E r hE, one_mul, mul_one]
  rcases le_or_gt j (r + 1) with hle | hgt
  · rw [𝔄.chernClass_of_le X E r hE (by omega) hle, smul_mul_assoc, mul_smul_comm, htuple]
  · rw [𝔄.chernClass_of_gt X E r hE hgt, zero_mul, mul_zero]

/-- Equation 45.12.1.1 determines the Chern classes: a family `d` with `d_0 = 1` which vanishes
above degree `r + 1` and satisfies
`∑_{i=0}^{r+1} (-1)^i c₁^A(𝒪_P(1))^i ∪ p^* d_{r+1-i} = 0`
is the family of Chern classes of `ℰ`. -/
theorem chernClass_eq_of_relation (d : ℕ → 𝔄.A X) (hd0 : d 0 = 1)
    (hdtop : ∀ j, r + 1 < j → d j = 0)
    (hrel : ∑ i : Fin (r + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      (𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
        𝔄.pull (𝔄.bundleDatum X E r hE).proj (d (r + 1 - (i : ℕ)))) = 0) (j : ℕ) :
    d j = 𝔄.chernClass X E r hE j := by
  have hform : 𝔄.bundleFormula X E r hE
      (fun i : Fin (r + 1) => ((-1 : ℤ) ^ (i : ℕ)) • d (r + 1 - (i : ℕ))) =
      𝔄.topTerm X E r hE := by
    rw [Fin.sum_univ_castSucc] at hrel
    have hlast : ((-1 : ℤ) ^ ((Fin.last (r + 1) : Fin (r + 2)) : ℕ)) •
        (𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^
            ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) *
          𝔄.pull (𝔄.bundleDatum X E r hE).proj
            (d (r + 1 - ((Fin.last (r + 1) : Fin (r + 2)) : ℕ)))) =
        ((-1 : ℤ) ^ (r + 1)) •
          𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (r + 1) := by
      have : ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = r + 1 := rfl
      rw [this, Nat.sub_self, hd0, map_one, mul_one]
    rw [hlast] at hrel
    rw [bundleFormula, topTerm, eq_neg_iff_add_eq_zero, ← hrel]
    refine congrArg₂ _ (Finset.sum_congr rfl fun i _ => ?_) rfl
    rw [map_zsmul, mul_smul_comm]
    rfl
  have htuple : (fun i : Fin (r + 1) => ((-1 : ℤ) ^ (i : ℕ)) • d (r + 1 - (i : ℕ))) =
      𝔄.chernTuple X E r hE :=
    (𝔄.bijective_bundleFormula X E r hE).injective
      (hform.trans (𝔄.bundleFormula_chernTuple X E r hE).symm)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [hd0, 𝔄.chernClass_zero X E r hE]
  rcases le_or_gt j (r + 1) with hle | hgt
  · rw [𝔄.chernClass_of_le X E r hE (by omega) hle, ← htuple]
    change d j = ((-1 : ℤ) ^ (r + 1 - j)) • (((-1 : ℤ) ^ (r + 1 - j)) • d (r + 1 - (r + 1 - j)))
    rw [show r + 1 - (r + 1 - j) = j from by omega, smul_smul, ← pow_add,
      show (r + 1 - j) + (r + 1 - j) = 2 * (r + 1 - j) from by omega, pow_mul]
    simp
  · rw [hdtop j hgt, 𝔄.chernClass_of_gt X E r hE hgt]

end ChernSetup

end Stacks.WeilCohomology

end
