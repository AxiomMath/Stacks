module

public import Mathlib.RingTheory.Polynomial.Vieta
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.CentralChernEval
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.PullbackTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClassLocallyFree

/-!
# Chern classes of a twist by an invertible module, from the splitting principle

In the standing situation of Stacks Section 45.12, let `ℰ` be a finite locally free
`𝒪_X`-module of constant rank `r` and let `ℒ` be an invertible `𝒪_X`-module. Tag 0FI8 is the
formula

`c^A_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`

for the Chern classes `c^A_i`, the components of the total Chern class `c^A` of Tag 0FI5. This
file proves it for **every** rule `c^A` with the three properties of Tag 0FI5, with no
hypothesis beyond those of the situation.

## Main results

* `Stacks.WeilCohomology.esymm_map_add_const`: the elementary symmetric functions of the shifted
  roots `x_k + t`, for a multiset of `r` roots.
* `Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree.apply_sum_classOf_invertible`: the
  components of the total Chern class of a sum of classes of invertible modules are the
  elementary symmetric functions of their first Chern classes.
* `Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree.apply_classOf_tensorObj_invertible`:
  **Tag 0FI8.**

## The argument

The source compares the projective bundles of `ℰ` and of `ℰ ⊗ ℒ` along the isomorphism of
Constructions, Lemma 27.20.1. That comparison is a morphism of `𝒞` only when `𝒞` contains it,
which the conditions of Section 45.12 do not say; the argument here uses instead the splitting
principle, Tag 0FI7, which is stated in those conditions. It gives `p : P ⟶ X` with `p^*`
injective on `A` and a filtration of `p^*ℰ` with invertible successive quotients `ℒ_1, …, ℒ_r`.
In `K₀(Vect(P))` one has `[p^*ℰ] = ∑_k [ℒ_k]` and, by Tag 01CD and Tag 0FDK,
`[p^*(ℰ ⊗ ℒ)] = [p^*ℰ] · [p^*ℒ] = ∑_k [ℒ_k ⊗ p^*ℒ]`. Properties (1) and (3) of Tag 0FI5 make the
Chern classes of these the elementary symmetric functions of the roots `x_k = c₁^A(ℒ_k)` and
`x_k + t`, `t = c₁^A(p^*ℒ) = p^*c₁^A(ℒ)`, and the formula is the identity
`e_i(x_1 + t, …, x_r + t) = ∑_{j=0}^{i} binom(r - i + j, j) e_{i-j}(x) t^j`, which is the
coefficient of `X^{r - i}` in `∏_k (X + t + x_k) = ∑_m e_m(x) (X + t)^{r - m}`.

The degree is restricted to `i ≤ r`: the upper index `r - i + j` is a truncated natural
subtraction, which for `i > r` does not realise the convention under which the formula holds.

## References

* [Stacks Project, Tag 0FI8](https://stacks.math.columbia.edu/tag/0FI8)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

universe u v v₁ w

namespace Stacks.WeilCohomology

/-! ### The elementary symmetric functions of shifted roots -/

/-- **The elementary symmetric functions of the roots shifted by `t`.** For a multiset `s` of `r`
elements of a commutative ring and `i ≤ r`,
`e_i(s + t) = ∑_{j=0}^{i} binom(r - i + j, j) e_{i-j}(s) t^j`. It is the coefficient of
`X^{r - i}` in `∏_{x ∈ s} (X + t + x) = ∑_m e_m(s) (X + t)^{r - m}`. -/
theorem esymm_map_add_const {R : Type*} [CommRing R] (s : Multiset R) (t : R) {i : ℕ}
    (hi : i ≤ Multiset.card s) :
    (s.map (· + t)).esymm i =
      ∑ j ∈ Finset.range (i + 1),
        ((Multiset.card s - i + j).choose j : R) * (s.esymm (i - j) * t ^ j) := by
  set r := Multiset.card s with hr
  have hcomp : ((s.map (· + t)).map fun x => (Polynomial.X : R[X]) + C x).prod =
      ((s.map fun x => (Polynomial.X : R[X]) + C x).prod).comp ((Polynomial.X : R[X]) + C t) := by
    rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply, add_comp, X_comp, C_comp, map_add]
    ring
  have hcard : Multiset.card (s.map (· + t)) = r := Multiset.card_map _ _
  have hlhs := Multiset.prod_X_add_C_coeff (s.map (· + t)) (k := r - i) (by rw [hcard]; omega)
  rw [hcard, show r - (r - i) = i by omega, hcomp, Multiset.prod_X_add_C_eq_sum_esymm] at hlhs
  rw [← hlhs, ← hr]
  simp only [sum_comp, mul_comp, C_comp, X_pow_comp, finsetSum_coeff, coeff_C_mul,
    coeff_X_add_C_pow]
  have hsub : Finset.range (i + 1) ⊆ Finset.range (r + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub fun k hk hki => by
    have hk' : k ≤ r := by simpa [Nat.lt_succ_iff] using hk
    have hki' : i < k := by simpa [Nat.lt_succ_iff] using hki
    rw [Nat.choose_eq_zero_of_lt (by omega : r - k < r - i)]
    simp]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ i := by simpa [Nat.lt_succ_iff] using hj
  rw [show i + 1 - 1 - j = i - j by omega, show r - (i - j) - (r - i) = j by omega,
    show r - (i - j) = r - i + j by omega, Nat.choose_symm_add]
  ring

/-! ### The Chern classes of a sum of classes of invertible modules -/

namespace IsTotalChernClassOnLocallyFree

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {𝔄 : ChernSetup.{u, v, v₁, w} C S}
  {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}

/-- **The total Chern class of a sum of classes of invertible modules is the product of the
`1 + c₁^A(ℒ_j)`**: its components are the elementary symmetric functions of the first Chern
classes, read in the centre of `A(P)` where condition (1) puts them. Property (1) of Tag 0FI5
turns the sum into a convolution and property (3) gives each factor. -/
theorem apply_sum_classOf_invertible (hc : IsTotalChernClassOnLocallyFree 𝔄 c) (P : C)
    {ι : Type*} (L : ι → (S.obj P).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (L j))
    (x : ι → Subring.center (𝔄.A P))
    (hx : ∀ j, (x j : 𝔄.A P) = 𝔄.c₁ P (picardClassOf (S.obj P) (L j) (hL j)))
    (s : Finset ι) (n : ℕ) :
    c P (∑ j ∈ s, VectorBundleKZero.classOf (S.obj P) (L j)) n =
      ((s.val.map x).esymm n : Subring.center (𝔄.A P)) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
      rw [Finset.sum_empty, hc.map_zero]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [ite_eq_right (by omega : ¬ n = 0), Finset.empty_val, Multiset.map_zero,
          Multiset.esymm_of_card_lt (by simpa using hn)]
        simp
  | insert a s ha ih =>
      have hval : ((insert a s).val.map x) = x a ::ₘ (s.val.map x) := by
        rw [Finset.insert_val_of_notMem ha, Multiset.map_cons]
      have hexp : c P (∑ j ∈ insert a s, VectorBundleKZero.classOf (S.obj P) (L j)) n =
          ∑ k ∈ Finset.range (n + 1),
            (if k = 0 then (1 : 𝔄.A P) else if k = 1 then (x a : 𝔄.A P) else 0) *
              (((s.val.map x).esymm (n - k) : Subring.center (𝔄.A P)) : 𝔄.A P) := by
        rw [Finset.sum_insert ha, hc.map_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hc.invertible P (L a) (hL a) k, ih (n - k), hx a]
      rw [hexp, hval]
      cases n with
      | zero => simp
      | succ m =>
          have hzero : ∀ k ∈ Finset.range m,
              (if k + 1 + 1 = 0 then (1 : 𝔄.A P)
                else if k + 1 + 1 = 1 then (x a : 𝔄.A P) else 0) *
                (((s.val.map x).esymm (m + 1 - (k + 1 + 1)) :
                  Subring.center (𝔄.A P)) : 𝔄.A P) = 0 := by
            intro k _
            simp
          rw [esymm_cons, Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ' _ m,
            Finset.sum_congr rfl hzero, Finset.sum_const_zero]
          push_cast
          simp
          abel

/-! ### Tag 0FI8 -/

/-- **Stacks Project, Tag 0FI8: the Chern classes of a twist.** In the standing situation of
Section 45.12, let `c^A` be a rule with the three properties of Tag 0FI5, let `ℰ` be a finite
locally free `𝒪_X`-module of constant rank `r` and `ℒ` an invertible `𝒪_X`-module. Then for
`i ≤ r`

`c^A_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`,

where `c^A_i(ℱ)` is the `i`-th component of `c^A([ℱ])`. By the splitting principle, Tag 0FI7,
after an injective pullback `ℰ` has Chern roots `x_1, …, x_r` and `ℰ ⊗ ℒ` the roots `x_k + t`
with `t` the pullback of `c₁^A(ℒ)`; the formula is then
`Stacks.WeilCohomology.esymm_map_add_const`. -/
@[stacks 0FI8 "for every rule c^A with the three properties of Tag 0FI5 (by that proposition \
  there is exactly one), at the Chern classes c^A_i(E) = the i-th component of c^A([E]); E of \
  constant rank r, L invertible, i <= r. Unconditional: no comparison of projective bundles is \
  assumed; the proof is the splitting principle 0FI7 instead of Constructions 02NC"]
theorem apply_classOf_tensorObj_invertible (hc : IsTotalChernClassOnLocallyFree 𝔄 c) (X : C)
    (E L : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (i : ℕ) (hi : i ≤ r) :
    c X (VectorBundleKZero.classOf (S.obj X)
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L)) i =
      ∑ j ∈ Finset.range (i + 1), (r - i + j).choose j •
        (c X (VectorBundleKZero.classOf (S.obj X) E) (i - j) *
          𝔄.c₁ X (picardClassOf (S.obj X) L hL) ^ j) := by
  classical
  obtain ⟨P, p, hpflat, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, Lk, hLk, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  set L' := (Scheme.Modules.pullback (S.map p)).obj L with hL'def
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 L' := isInvertible_pullback_obj (S.map p) L hL
  have hLkL' : ∀ k, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (Scheme.Modules.tensorObjRingedSpace (S.obj P) (Lk k) L') :=
    fun k => isInvertible_tensorObjRingedSpace _ _ (hLk k) hL'
  have stacksFlf : ∀ {Z : Scheme.{u}} (M : Z.Modules) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M m →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M := fun M _ h =>
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mpr
      h.isFiniteLocallyFree
  have rankOne : ∀ {Z : Scheme.{u}} (M : Z.Modules),
      AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M →
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1 := by
    intro Z M hM
    have := hM
    exact inferInstance
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r := hE
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    rankOne L hL
  have hEL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L) (r * 1) :=
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (S.obj X) E L r 1
  have hpull : ∀ M m,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M m →
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map p)).obj M) m := fun M m h =>
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) M m h
  have hclassP : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj
          (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L)) =
      ∑ k, VectorBundleKZero.classOf (S.obj P)
        (Scheme.Modules.tensorObjRingedSpace (S.obj P) (Lk k) L') := by
    rw [VectorBundleKZero.classOf_eq_of_iso (pullbackTensorObjRingedSpaceIso (S.map p) E L)
      (stacksFlf _ _ (hpull _ _ hEL)),
      ← VectorBundleKZero.classOf_mul _ _ (stacksFlf _ _ (hpull E r hE))
        (stacksFlf _ _ (rankOne _ hL')),
      hsum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ =>
      VectorBundleKZero.classOf_mul _ _ (stacksFlf _ _ (rankOne _ (hLk k)))
        (stacksFlf _ _ (rankOne _ hL'))
  let central : (S.obj P).picardGroup → Subring.center (𝔄.A P) := fun N =>
    ⟨𝔄.c₁ P N, Subring.mem_center_iff.mpr fun b => (𝔄.c₁_central P N b).symm⟩
  let x : Fin r → Subring.center (𝔄.A P) := fun k =>
    central (picardClassOf (S.obj P) (Lk k) (hLk k))
  let t : Subring.center (𝔄.A P) := central (picardClassOf (S.obj P) L' hL')
  have hpullc₁ : 𝔄.pull p (𝔄.c₁ X (picardClassOf (S.obj X) L hL)) = (t : 𝔄.A P) := by
    have hc₁ : ∀ Y M hM,
        c Y (VectorBundleKZero.classOf (S.obj Y) M) 1 = 𝔄.c₁ Y (picardClassOf (S.obj Y) M hM) :=
      fun Y M hM => by rw [hc.invertible Y M hM 1]; simp
    rw [← hc₁ X L hL, hc.map_pull p L (rankOne L hL).isFiniteLocallyFree 1, hc₁ P L' hL']
  have hpullE : ∀ n, 𝔄.pull p (c X (VectorBundleKZero.classOf (S.obj X) E) n) =
      ((Finset.univ.val.map x).esymm n : Subring.center (𝔄.A P)) := fun n => by
    rw [hc.map_pull p E hE.isFiniteLocallyFree n, hsum,
      hc.apply_sum_classOf_invertible P Lk hLk x (fun k => rfl) Finset.univ n]
  have hpullEL : 𝔄.pull p (c X (VectorBundleKZero.classOf (S.obj X)
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L)) i) =
      (((Finset.univ.val.map x).map (· + t)).esymm i : Subring.center (𝔄.A P)) := by
    rw [hc.map_pull p _ hEL.isFiniteLocallyFree i, hclassP,
      hc.apply_sum_classOf_invertible P _ hLkL' (fun k => x k + t) (fun k => ?_) Finset.univ i,
      Multiset.map_map]
    · rfl
    · exact (c₁_picardClassOf_tensorObjRingedSpace 𝔄 P (Lk k) L' (hLk k) hL' (hLkL' k)).symm
  have hcard : Multiset.card (Finset.univ.val.map x) = r := by simp
  refine hinj ?_
  rw [hpullEL, esymm_map_add_const _ t (by rw [hcard]; exact hi), hcard, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_nsmul, map_mul, map_pow, hpullE, hpullc₁, nsmul_eq_mul]

end IsTotalChernClassOnLocallyFree

end Stacks.WeilCohomology

end
