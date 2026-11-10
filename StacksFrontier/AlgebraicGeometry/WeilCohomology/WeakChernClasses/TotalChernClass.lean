module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClassLocallyFree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.SplittingPrinciple

/-!
# The total Chern class of a Weil cohomology theory, in the weak standing situation

The results of `StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass`,
stated
for `Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation
of Stacks Section 45.12 in which the projective bundle formula, condition (4), is only asked to be
injective and to resolve the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality). The arguments are those of the original module, which use condition
(4) only through these two properties.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

/-! ### Reading a filtration in the `K`-group -/

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The three properties of Tag 0FI5's total Chern class.** A rule `c` assigns to every object
`X` of `𝒞` and every class `α` of `K₀(Vect(X))` the components `c X α n` of its total Chern
class, the `n`-th lying in `A^n(X)`; it is multiplicative on sums, compatible with pullback on
the classes of modules, and takes the value `1 + c₁^A(ℒ)` on an invertible module. -/
structure IsTotalChernClass (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    (c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X) : Prop where
  /-- The `n`-th component lies in `A^n(X)`, so that `c` lands in `∏_{i ≥ 0} A^i(X)`. -/
  mem_grade : ∀ (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ), c X α n ∈ 𝔚.grade X n
  /-- **Property (1).** `c^A(α + β) = c^A(α) c^A(β)`, componentwise. -/
  map_add : ∀ (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ),
    c X (α + β) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c X α p.1 * c X β p.2
  /-- **Property (1).** `c^A(0) = 1`. -/
  map_zero : ∀ (X : C) (n : ℕ), c X 0 n = if n = 0 then 1 else 0
  /-- **Property (2)**, on the class of a finite locally free module: `f^*c^A([ℰ]) =
  c^A([f^*ℰ])`. This is the instance of property (2) at a generator, the pullback of
  `K₀(Vect(-))` carrying `[ℰ]` to `[f^*ℰ]`.

  The hypothesis that `ℰ` be finite locally free is not a restriction and cannot be dropped:
  `AlgebraicGeometry.VectorBundleKZero.classOf` is defined on every sheaf of modules and
  vanishes off the finite locally free ones, so without it the clause would also assert
  `1 = c^A([f^*ℰ])` for a module `ℰ` which is not finite locally free but whose pullback is —
  for instance the restriction of `ℰ` to an open set on which it is invertible with nonzero
  first Chern class. No rule satisfies that, and the source asserts nothing of the kind: its
  `f^*` is the pullback of `K₀(Vect(-))`, under which such an `[ℰ]`, being `0`, goes to `0`. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj Y).ringCatSheaf) E → ∀ n : ℕ,
    𝔚.pull f (c Y (VectorBundleKZero.classOf (S.obj Y) E) n) =
      c X (VectorBundleKZero.classOf (S.obj X)
        ((Scheme.Modules.pullback (S.map f)).obj E)) n
  /-- **Property (2) on all of `K₀(Vect(X))`.** `f^* ∘ c^A = c^A ∘ f^*` for the pullback `f^*` of
  `K₀(Vect(-))`, which is the additive map carrying `[ℰ]` to `[f^*ℰ]`.

  **The map is constructed.** It is `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, a ring
  homomorphism `K₀(Vect(Y)) ⟶ K₀(Vect(X))`, with its defining property `f^*[ℰ] = [f^*ℰ]` as
  `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom_classOf` and its existential form as
  `AlgebraicGeometry.VectorBundleKZero.exists_pullback_ringHom`, all in
  `StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroupPullback`. Read against that map,
  taken additively, this field is the source's property (2) outright, with nothing assumed.

  It is nevertheless stated for an arbitrary such `κ`, and that costs nothing: a `κ` with the
  generator property is unique, by `AlgebraicGeometry.VectorBundleKZero.addHom_ext`, so the
  quantified form and the form naming the constructed map are equivalent predicates on `c` — and
  of the two it is the quantified one that is the stronger to prove. It is kept because this file
  imports `StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup`, where `addHom_ext` lives,
  but not the pullback construction, and because no consumer of this field needs the map named. -/
  map_pull_kZero : ∀ {X Y : C} (f : X ⟶ Y)
    (κ : VectorBundleKZero (S.obj Y) →+ VectorBundleKZero (S.obj X)),
    (∀ E : (S.obj Y).Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := (S.obj Y).ringCatSheaf) E →
      κ (VectorBundleKZero.classOf (S.obj Y) E) =
        VectorBundleKZero.classOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj E)) →
    ∀ (α : VectorBundleKZero (S.obj Y)) (n : ℕ), 𝔚.pull f (c Y α n) = c X (κ α) n
  /-- **Property (3).** `c^A([ℒ]) = 1 + c₁^A(ℒ)` for an invertible module `ℒ`. -/
  invertible : ∀ (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ),
    c X (VectorBundleKZero.classOf (S.obj X) L) n =
      if n = 0 then 1 else if n = 1 then 𝔚.c₁ X (picardClassOf (S.obj X) L hL) else 0

/-- Two rules with the three properties agree on a sum of classes of invertible modules:
property (1) turns the sum into a convolution of values that property (3) pins down. -/
private theorem eq_on_sum_classOf_invertible {𝔚 : ChernSetup.{u, v, v₁, w} C S}
    {c c' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X}
    (hc : IsTotalChernClass 𝔚 c) (hc' : IsTotalChernClass 𝔚 c') (P : C) (k : ℕ) :
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

/-- **The uniqueness half of Stacks Tag 0FI5.** Properties (1), (2) and (3) determine the total
Chern class of the class of a finite locally free module of constant rank: any two rules with
those properties agree there.

The splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a
filtration of `p^*ℰ` with invertible successive quotients. That filtration writes `[p^*ℰ]` as a
sum of classes of invertible modules in `K₀(Vect(P))`, where properties (1) and (3) determine the
total Chern class; property (2) identifies the result with `p^*c^A([ℰ])`, and `p^*` is
injective. -/
theorem eq_of_isTotalChernClass {𝔚 : ChernSetup.{u, v, v₁, w} C S}
    {c c' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X}
    (hc : IsTotalChernClass 𝔚 c) (hc' : IsTotalChernClass 𝔚 c') (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (n : ℕ) :
    c X (VectorBundleKZero.classOf (S.obj X) E) n =
      c' X (VectorBundleKZero.classOf (S.obj X) E) n := by
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔚.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  refine hinj ?_
  rw [hc.map_pull p E hE.isFiniteLocallyFree n, hc'.map_pull p E hE.isFiniteLocallyFree n, hsum]
  exact eq_on_sum_classOf_invertible hc hc' P _ L hL n

/-! ### The Chern classes of a module of constant rank -/

namespace ChernSetup

variable (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C) (E : (S.obj X).Modules) (r : ℕ)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))

/-- The element of `A(𝐏(ℰ))` that the Chern classes are defined to resolve: minus the top term
`(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}` of equation 45.12.1.1. -/
def topTerm : 𝔚.A (𝔚.bundleDatum X E r hE).bundle :=
  -(((-1 : ℤ) ^ (r + 1)) •
    𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (r + 1))

/-- **The tuple of Chern classes of a finite locally free module of constant rank `r + 1`**, as
the projective bundle formula produces it: the `(a_0, …, a_r)` with
`∑_i c₁^A(𝒪_P(1))^i ∪ p^*(a_i) = -(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}`, which exists because condition
(4) resolves `c₁^A(𝒪_P(1))^{r+1}` and is unique because condition (4) is injective. -/
def chernTuple : Fin (r + 1) → 𝔚.A X :=
  -(((-1 : ℤ) ^ (r + 1)) • (𝔚.exists_bundleFormula_eq_pow X E r hE).choose)

/-- The defining property of the tuple. -/
theorem bundleFormula_chernTuple :
    𝔚.bundleFormula X E r hE (𝔚.chernTuple X E r hE) = 𝔚.topTerm X E r hE := by
  have h := 𝔚.bundleFormula_zsmul X E r hE (-((-1 : ℤ) ^ (r + 1)))
    (𝔚.exists_bundleFormula_eq_pow X E r hE).choose
  rw [(𝔚.exists_bundleFormula_eq_pow X E r hE).choose_spec, neg_smul] at h
  rw [chernTuple, topTerm, h, neg_smul]

/-- **The Chern classes `c_j^A(ℰ)` of a finite locally free module of constant rank `r + 1`.**
The zeroth is `1`, those in degrees `1, …, r + 1` are the entries of `chernTuple` with the signs
of equation 45.12.1.1, and the rest vanish.

This is the construction half of Tag 0FI5 for a single module: the resolution of the top power
of the twist class that condition (4) provides, with signs. It is not yet a rule on `K₀(Vect(X))`;
see the module documentation. -/
def chernClass (j : ℕ) : 𝔚.A X :=
  if hj : j = 0 then 1
  else if h : j ≤ r + 1 then
    ((-1 : ℤ) ^ (r + 1 - j)) • 𝔚.chernTuple X E r hE ⟨r + 1 - j, by omega⟩
  else 0

/-- The defining property of the tuple, with the projective bundle formula written out. -/
private theorem sum_pow_mul_pull_chernTuple :
    ∑ i : Fin (r + 1),
      𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
        𝔚.pull (𝔚.bundleDatum X E r hE).proj (𝔚.chernTuple X E r hE i) =
      𝔚.topTerm X E r hE := 𝔚.bundleFormula_chernTuple X E r hE

/-- Scalar multiplication by `(-1)^k` is an involution. -/
private theorem neg_one_pow_smul_neg_one_pow_smul {M : Type*} [AddCommGroup M] (k : ℕ) (x : M) :
    ((-1 : ℤ) ^ k) • ((-1 : ℤ) ^ k) • x = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul]
  simp

/-- `c_0^A(ℰ) = 1`. -/
@[simp] theorem chernClass_zero : 𝔚.chernClass X E r hE 0 = 1 := by
  simp [chernClass]

/-- The Chern classes vanish in degrees above the rank. -/
@[simp] theorem chernClass_of_gt {j : ℕ} (hj : r + 1 < j) : 𝔚.chernClass X E r hE j = 0 := by
  unfold chernClass
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

/-- The Chern classes in degrees `1, …, r + 1` are the signed entries of the tuple. -/
theorem chernClass_of_le {j : ℕ} (hj : j ≠ 0) (h : j ≤ r + 1) :
    𝔚.chernClass X E r hE j =
      ((-1 : ℤ) ^ (r + 1 - j)) • 𝔚.chernTuple X E r hE ⟨r + 1 - j, by omega⟩ := by
  unfold chernClass
  split_ifs with h1
  · exact absurd h1 hj
  · rfl

/-- **Equation 45.12.1.1**, the relation that defines the Chern classes:
`∑_{i=0}^{r+1} (-1)^i c₁^A(𝒪_P(1))^i ∪ p^*c^A_{r+1-i}(ℰ) = 0` in `A(𝐏(ℰ))`.

The term at `i = r + 1` is `(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}`, because `c_0^A(ℰ) = 1`; the terms
below it reproduce the projective bundle formula applied to the tuple, the two signs cancelling,
and that is `-(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}` by construction. -/
theorem sum_chernClass_eq_zero :
    ∑ i : Fin (r + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔚.pull (𝔚.bundleDatum X E r hE).proj (𝔚.chernClass X E r hE (r + 1 - (i : ℕ)))) = 0 := by
  have hlow : ∀ i : Fin (r + 1),
      ((-1 : ℤ) ^ ((i.castSucc : Fin (r + 2)) : ℕ)) •
          (𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^
              ((i.castSucc : Fin (r + 2)) : ℕ) *
            𝔚.pull (𝔚.bundleDatum X E r hE).proj
              (𝔚.chernClass X E r hE (r + 1 - ((i.castSucc : Fin (r + 2)) : ℕ)))) =
        𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔚.pull (𝔚.bundleDatum X E r hE).proj (𝔚.chernTuple X E r hE i) := by
    intro i
    have hi : (i : ℕ) ≤ r := Nat.lt_succ_iff.1 i.isLt
    have hcast : ((i.castSucc : Fin (r + 2)) : ℕ) = (i : ℕ) := rfl
    have hexp : r + 1 - (r + 1 - (i : ℕ)) = (i : ℕ) := by omega
    have hidx : (⟨r + 1 - (r + 1 - (i : ℕ)), by omega⟩ : Fin (r + 1)) = i := Fin.ext hexp
    rw [hcast, 𝔚.chernClass_of_le X E r hE (by omega) (by omega), hidx, hexp, map_zsmul,
      mul_smul_comm, neg_one_pow_smul_neg_one_pow_smul]
  rw [Fin.sum_univ_castSucc, Finset.sum_congr rfl fun i _ => hlow i]
  have hlast : ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = r + 1 := rfl
  rw [hlast, Nat.sub_self, 𝔚.chernClass_zero X E r hE, map_one]
  rw [𝔚.sum_pow_mul_pull_chernTuple X E r hE, topTerm, mul_one]
  abel

/-- **The Chern classes are central in `A(X)`.** This is the source's "the elements
`c_i^A(ℰ)` are in the center of `A(X)`".

The tuples `(c_i b)_i` and `(b c_i)_i` have the same image under the projective bundle formula:
both are `topTerm` multiplied by `p^*b`, on the left in one case and on the right in the other,
and `topTerm` is a scalar multiple of a power of the central class `c₁^A(𝒪_P(1))`. The formula
is injective by condition (4), so the two tuples agree. -/
theorem chernClass_central (j : ℕ) (b : 𝔚.A X) :
    𝔚.chernClass X E r hE j * b = b * 𝔚.chernClass X E r hE j := by
  have hx : ∀ (c : 𝔚.A (𝔚.bundleDatum X E r hE).bundle) (k : ℕ),
      𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ k * c =
        c * 𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ k :=
    fun c k => Commute.pow_left (𝔚.c₁_central _ _ c) k
  have htuple : ∀ i : Fin (r + 1),
      𝔚.chernTuple X E r hE i * b = b * 𝔚.chernTuple X E r hE i := by
    have heq : (fun i : Fin (r + 1) => 𝔚.chernTuple X E r hE i * b) =
        fun i : Fin (r + 1) => b * 𝔚.chernTuple X E r hE i := by
      refine (𝔚.injective_bundleFormula X E r hE) ?_
      have hL : ∑ i : Fin (r + 1),
            𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
              𝔚.pull (𝔚.bundleDatum X E r hE).proj (𝔚.chernTuple X E r hE i * b) =
          𝔚.topTerm X E r hE * 𝔚.pull (𝔚.bundleDatum X E r hE).proj b := by
        rw [← 𝔚.sum_pow_mul_pull_chernTuple X E r hE, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_assoc]
      have hR : ∑ i : Fin (r + 1),
            𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
              𝔚.pull (𝔚.bundleDatum X E r hE).proj (b * 𝔚.chernTuple X E r hE i) =
          𝔚.pull (𝔚.bundleDatum X E r hE).proj b * 𝔚.topTerm X E r hE := by
        rw [← 𝔚.sum_pow_mul_pull_chernTuple X E r hE, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, ← mul_assoc, hx (𝔚.pull (𝔚.bundleDatum X E r hE).proj b) (i : ℕ),
          mul_assoc]
      change ∑ i : Fin (r + 1), _ * _ = ∑ i : Fin (r + 1), _ * _
      rw [hL, hR, topTerm, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm,
        hx (𝔚.pull (𝔚.bundleDatum X E r hE).proj b) (r + 1)]
    exact fun i => congrFun heq i
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [𝔚.chernClass_zero X E r hE, one_mul, mul_one]
  rcases le_or_gt j (r + 1) with hle | hgt
  · rw [𝔚.chernClass_of_le X E r hE (by omega) hle, smul_mul_assoc, mul_smul_comm, htuple]
  · rw [𝔚.chernClass_of_gt X E r hE hgt, zero_mul, mul_zero]

/-- **Equation 45.12.1.1 determines the Chern classes.** A family `d` with `d_0 = 1` which
vanishes above degree `r + 1` and satisfies
`∑_{i=0}^{r+1} (-1)^i c₁^A(𝒪_P(1))^i ∪ p^* d_{r+1-i} = 0`
is the family of Chern classes of `ℰ`.

This is the uniqueness half of the source's "we can uniquely define elements `c_i^A(ℰ)` such
that `c_0^A(ℰ) = 1` and equation 45.12.1.1 is true": the relation says that the signed tuple
`((-1)^i d_{r+1-i})_{i ≤ r}` is carried to
`Stacks.WeilCohomology.Weak.ChernSetup.topTerm` by the projective bundle formula, and that map is
injective by condition (4). -/
theorem chernClass_eq_of_relation (d : ℕ → 𝔚.A X) (hd0 : d 0 = 1)
    (hdtop : ∀ j, r + 1 < j → d j = 0)
    (hrel : ∑ i : Fin (r + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      (𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
        𝔚.pull (𝔚.bundleDatum X E r hE).proj (d (r + 1 - (i : ℕ)))) = 0) (j : ℕ) :
    d j = 𝔚.chernClass X E r hE j := by
  have hform : 𝔚.bundleFormula X E r hE
      (fun i : Fin (r + 1) => ((-1 : ℤ) ^ (i : ℕ)) • d (r + 1 - (i : ℕ))) =
      𝔚.topTerm X E r hE := by
    rw [Fin.sum_univ_castSucc] at hrel
    have hlast : ((-1 : ℤ) ^ ((Fin.last (r + 1) : Fin (r + 2)) : ℕ)) •
        (𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^
            ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) *
          𝔚.pull (𝔚.bundleDatum X E r hE).proj
            (d (r + 1 - ((Fin.last (r + 1) : Fin (r + 2)) : ℕ)))) =
        ((-1 : ℤ) ^ (r + 1)) •
          𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (r + 1) := by
      have : ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = r + 1 := rfl
      rw [this, Nat.sub_self, hd0, map_one, mul_one]
    rw [hlast] at hrel
    rw [bundleFormula, topTerm, eq_neg_iff_add_eq_zero, ← hrel]
    refine congrArg₂ _ (Finset.sum_congr rfl fun i _ => ?_) rfl
    rw [map_zsmul, mul_smul_comm]
    rfl
  have htuple : (fun i : Fin (r + 1) => ((-1 : ℤ) ^ (i : ℕ)) • d (r + 1 - (i : ℕ))) =
      𝔚.chernTuple X E r hE :=
    (𝔚.injective_bundleFormula X E r hE)
      (hform.trans (𝔚.bundleFormula_chernTuple X E r hE).symm)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [hd0, 𝔚.chernClass_zero X E r hE]
  rcases le_or_gt j (r + 1) with hle | hgt
  · rw [𝔚.chernClass_of_le X E r hE (by omega) hle, ← htuple]
    change d j = ((-1 : ℤ) ^ (r + 1 - j)) • (((-1 : ℤ) ^ (r + 1 - j)) • d (r + 1 - (r + 1 - j)))
    rw [show r + 1 - (r + 1 - j) = j from by omega, neg_one_pow_smul_neg_one_pow_smul]
  · rw [hdtop j hgt, 𝔚.chernClass_of_gt X E r hE hgt]

end ChernSetup

end Stacks.WeilCohomology.Weak

end
