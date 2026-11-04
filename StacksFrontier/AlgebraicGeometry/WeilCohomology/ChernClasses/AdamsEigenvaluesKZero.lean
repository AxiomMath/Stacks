module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.AdamsEigenvalues
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacterUniqueness
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernSeries
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleTensor
import all StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.AdamsEigenvalues

/-!
# The second Adams operator scales `c^A_i` and `ch^A_i` by `2^i`, on all of `K₀(Vect(X))`

`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.AdamsEigenvalues` proves Tag 0FIA for
the class of a finite locally free module of constant rank, with the pullback homomorphism of
`K₀(Vect(-))` and the second Adams operator carried as hypotheses. Here the pullback is the
constructed `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, the rank is arbitrary and the
class
is an arbitrary element of `K₀(Vect(X))`; the second Adams operator is also instantiated at the
constructed ring map of Tag 0FEJ.

## Main results

* `Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree.pull_eq`: property (2) of the total Chern
class on all of `K₀(Vect(X))`, against the constructed pullback.
* `Stacks.WeilCohomology.chernClass_secondAdams_kZero`: `c^A_i(ψ²(α)) = 2^i c^A_i(α)` for every
  `α` in `K₀(Vect(X))`.
* `Stacks.WeilCohomology.chernCharacter_secondAdams_kZero`: `ch^A_i(ψ²(α)) = 2^i ch^A_i(α)` for
  every `α` in `K₀(Vect(X))`.
* `Stacks.WeilCohomology.chernClass_secondAdams_secondAdamsRingHom` and
  `Stacks.WeilCohomology.chernCharacter_secondAdams_secondAdamsRingHom`: the same for the
  constructed second Adams operator.

## References

* [Stacks Project, Tag 0FIA](https://stacks.math.columbia.edu/tag/0FIA)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- Doubling the first Chern class of each summand multiplies the degree-`n` part of the total
Chern class of a sum of classes of invertible modules by `2^n`: in the convolution that property
(1) turns the sum into, the factor contributed in degree `0` is `1` and the one contributed in
degree `1` doubles, so every term of total degree `n` acquires exactly `2^n`. -/
private theorem chernClass_sum_double_onLocallyFree {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X} (hc : IsTotalChernClassOnLocallyFree 𝔄 c)
    (P : C) (k : ℕ) :
    ∀ (L M : Fin k → (S.obj P).Modules)
      (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
        (S.obj P).ringCatSheaf.2 (L j))
      (hM : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
        (S.obj P).ringCatSheaf.2 (M j)),
      (∀ j, picardClassOf (S.obj P) (M j) (hM j) = 2 • picardClassOf (S.obj P) (L j) (hL j)) →
      ∀ n : ℕ,
        c P (∑ j, VectorBundleKZero.classOf (S.obj P) (M j)) n =
          (2 ^ n : ℕ) • c P (∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) n := by
  induction k with
  | zero =>
      intro L M _ _ _ n
      simp only [Finset.univ_eq_empty, Finset.sum_empty, hc.map_zero]
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp [hn]
  | succ k ih =>
      intro L M hL hM hpic n
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hc.map_add, hc.map_add, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqn : q.1 + q.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      rw [ih (fun j => L j.castSucc) (fun j => M j.castSucc) (fun j => hL _) (fun j => hM _)
          (fun j => hpic _) q.1,
        hc.invertible P (M (Fin.last k)) (hM (Fin.last k)) q.2,
        hc.invertible P (L (Fin.last k)) (hL (Fin.last k)) q.2, hpic (Fin.last k), map_nsmul]
      exact nsmul_mul_degreeOneFactor _ _ hqn

/-! ### Property (2) of the total Chern class against the constructed pullback -/

/-- **Property (2) of Tag 0FI5 on all of `K₀(Vect(X))`**, read against the pullback homomorphism
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom` of `K₀(Vect(-))`. This is the field
`Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree.map_pull_kZero` at the map that repository
constructs,
whose defining property is `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom_classOf`; it is the
counterpart, for the total Chern class, of
`Stacks.WeilCohomology.IsChernCharacterOnLocallyFree.map_pull_kzero`. -/
theorem IsTotalChernClassOnLocallyFree.pull_eq {𝔄 : SourceChernSetup.{u, v, v₁, w} C S}
    {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c)
    {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)) (n : ℕ) :
    𝔄.pull f (c Y α n) = c X (VectorBundleKZero.pullbackRingHom (S.map f) α) n :=
  hc.map_pull_kZero f (VectorBundleKZero.pullbackRingHom (S.map f)).toAddMonoidHom
    (fun E hE => VectorBundleKZero.pullbackRingHom_classOf (S.map f) E
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr hE)) α n

/-! ### The two eigenvalue statements on all of `K₀(Vect(X))` -/

section

variable {𝔄 : SourceChernSetup.{u, v, v₁, w} C S}
  (ψ : ∀ X : C, VectorBundleKZero (S.obj X) →+* VectorBundleKZero (S.obj X))

/-- Tag 0FIA at the class of a finite locally free module, for any rule `c` satisfying property
(2) and the doubling of sums of classes of invertible modules: the splitting principle of Tag 0FI7
handles constant rank, and the source's decomposition of `X` into the loci where the rank is
constant handles the general case. -/
private theorem secondAdams_classOf_of_sum
    {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)) (n : ℕ),
      𝔄.pull f (c Y α n) = c X (VectorBundleKZero.pullbackRingHom (S.map f) α) n)
    (hsum : ∀ (P : C) (k : ℕ) (L M : Fin k → (S.obj P).Modules)
      (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
        (S.obj P).ringCatSheaf.2 (L j))
      (hM : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
        (S.obj P).ringCatSheaf.2 (M j)),
      (∀ j, picardClassOf (S.obj P) (M j) (hM j) = 2 • picardClassOf (S.obj P) (L j) (hL j)) →
      ∀ n : ℕ,
        c P (∑ j, VectorBundleKZero.classOf (S.obj P) (M j)) n =
          (2 ^ n : ℕ) • c P (∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) n)
    (hψpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      VectorBundleKZero.pullbackRingHom (S.map f) (ψ Y α) =
        ψ X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hψinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ∃ (M : (S.obj X).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsInvertible
        (S.obj X).presheaf (S.obj X).ringCatSheaf.2 M),
        ψ X (VectorBundleKZero.classOf (S.obj X) L) =
            VectorBundleKZero.classOf (S.obj X) M ∧
          picardClassOf (S.obj X) M hM = 2 • picardClassOf (S.obj X) L hL)
    (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (n : ℕ) :
    c X (ψ X (VectorBundleKZero.classOf (S.obj X) E)) n =
      (2 ^ n : ℕ) • c X (VectorBundleKZero.classOf (S.obj X) E) n := by
  classical
  have rank (X : C) (E : (S.obj X).Modules) (r : ℕ)
      (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
      c X (ψ X (VectorBundleKZero.classOf (S.obj X) E)) n =
        (2 ^ n : ℕ) • c X (VectorBundleKZero.classOf (S.obj X) E) n := by
    obtain ⟨P, p, -, hinj, hfil⟩ :=
      𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
    obtain ⟨-, L, hL, hsumL⟩ := (hfil ()).exists_classOf_eq_sum
    choose M hM hψM hpic using fun j => hψinv P (L j) (hL j)
    refine hinj ?_
    rw [map_nsmul, hpull p _ n, hpull p _ n, hψpull p _,
      VectorBundleKZero.pullbackRingHom_classOf (S.map p) E
        ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr
          hE.isFiniteLocallyFree),
      hsumL, map_sum, Finset.sum_congr rfl fun j _ => hψM j]
    exact hsum P _ L M hL hM hpic n
  refine 𝔄.eq_of_pull_constantRank X Unit inferInstance (fun _ => E) (fun _ => hE) _ _ ?_
  intro Z g _ m hm
  rw [hpull g _ n, map_nsmul, hpull g _ n, hψpull g _,
    VectorBundleKZero.pullbackRingHom_classOf (S.map g) E
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr hE)]
  exact rank Z _ (m ()) (hm ())

/-- **Stacks Project, Tag 0FIA for the total Chern class.** The second Adams operator scales the
degree-`n` part of the total Chern class by `2^n`: `c^A_n(ψ²(α)) = 2^n c^A_n(α)` for every
`α ∈ K₀(Vect(X))`.

The rule `c^A` is the one of Tag 0FI5, named by
`Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree`, and
`ψ²` is named by the two properties Tag 0FEJ gives it. The pullback of `K₀(Vect(-))` is the
constructed `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`; see the module documentation. -/
@[stacks 0FIA "the identity `c^A_i(psi^2(alpha)) = 2^i c^A_i(alpha)` for EVERY element alpha of \
  K_0(Vect(X)) and a module of ARBITRARY rank -- the source's own statement, with no restriction \
  to generators and no constant rank: the reduction to the generators is \
  eq_of_convolutive_of_eq_classOf and the reduction to constant rank is the source's \
  decomposition of X by the rank, ChernSetup.eq_of_pull_constantRank. The rule c^A is the \
  predicate IsTotalChernClassOnLocallyFree of Tag 0FI5, which exactly one rule satisfies \
  (existsUnique_isTotalChernClass_of_source), so fixing it by that predicate is the source's \
  'let c^A be as in Proposition 45.12.1'. psi^2 is named by the two properties Tag 0FEJ gives \
  it, its value on an invertible module and its commutation with the pullback of K_0(Vect(-)), \
  and the identity is proved for every ring endomorphism with those two properties; this \
  repository CONSTRUCTS such a map, VectorBundleKZero.secondAdamsRingHom, and the two \
  properties are verified for it in chernClass_secondAdams_secondAdamsRingHom. The pullback of \
  K_0(Vect(-)) is NOT named by a property: it is the constructed ring homomorphism \
  VectorBundleKZero.pullbackRingHom, with its defining property pullback_classOf, and property \
  (2) is \
  read against it by IsTotalChernClassOnLocallyFree.map_pull_kZero. psi^2([L]) = [L tensor L] is \
  read in \
  Pic, where addition is the tensor product by Tag 01CX \
  (picardClassOf_tensorObjRingedSpace)"]
theorem chernClass_secondAdams_kZero
    {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c)
    (hψpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      VectorBundleKZero.pullbackRingHom (S.map f) (ψ Y α) =
        ψ X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hψinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ∃ (M : (S.obj X).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsInvertible
        (S.obj X).presheaf (S.obj X).ringCatSheaf.2 M),
        ψ X (VectorBundleKZero.classOf (S.obj X) L) =
            VectorBundleKZero.classOf (S.obj X) M ∧
          picardClassOf (S.obj X) M hM = 2 • picardClassOf (S.obj X) L hL)
    (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    c X (ψ X α) n = (2 ^ n : ℕ) • c X α n := by
  classical
  refine eq_of_convolutive_of_eq_classOf (c := fun a k => c X (ψ X a) k)
    (c' := fun a k => (2 ^ k : ℕ) • c X a k) (fun a b k => ?_) (fun k => ?_) (fun a b k => ?_)
    (fun k => ?_) (fun M k => ?_) α n
  · rw [map_add, hc.map_add]
  · rw [map_zero, hc.map_zero]
  · rw [hc.map_add, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq2 : q.1 + q.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, hq2]
  · rw [hc.map_zero]
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [hk]
  · by_cases hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := (S.obj X).ringCatSheaf) M
    · exact secondAdams_classOf_of_sum ψ (fun f a m => hc.pull_eq f a m)
        (chernClass_sum_double_onLocallyFree hc) hψpull hψinv X M hM k
    · rw [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M fun h =>
          hM ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp h),
        map_zero, hc.map_zero]
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · simp [hk]

/-- **Stacks Project, Tag 0FIA for the Chern character.** The second Adams operator scales the
degree-`n` part of the Chern character by `2^n`: `ch^A_n(ψ²(α)) = 2^n ch^A_n(α)` for every
`α ∈ K₀(Vect(X))`.

The rule `ch^A` is the one of Tag 0FI9, named by
`Stacks.WeilCohomology.IsChernCharacterOnLocallyFree`, and
`ψ²` is named by the two properties Tag 0FEJ gives it. The pullback of `K₀(Vect(-))` is the
constructed `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`; see the module documentation. -/
@[stacks 0FIA "the identity `ch^A_i(psi^2(alpha)) = 2^i ch^A_i(alpha)` for EVERY element alpha \
  of K_0(Vect(X)) and a module of ARBITRARY rank -- the source's own statement, with no \
  restriction to generators and no constant rank: the reduction to the generators is \
  VectorBundleKZero.addHom_ext and the reduction to constant rank is the source's \
  decomposition of X by the rank, ChernSetup.eq_of_pull_constantRank. The rule ch^A is the \
  predicate IsChernCharacterOnLocallyFree of Tag 0FI9, which exactly one rule satisfies \
  (existsUnique_isChernCharacter_of_source), so fixing it by that predicate is the source's \
  'let ch^A be as in Proposition 45.12.4'. psi^2 is named by the two properties Tag 0FEJ gives \
  it, its value on an invertible module and its commutation with the pullback of K_0(Vect(-)), \
  and the identity is proved for every ring endomorphism with those two properties; this \
  repository CONSTRUCTS such a map, VectorBundleKZero.secondAdamsRingHom, and the two \
  properties are verified for it in chernCharacter_secondAdams_secondAdamsRingHom. The pullback \
  of K_0(Vect(-)) is NOT named by a property: it is the constructed ring homomorphism \
  VectorBundleKZero.pullbackRingHom, with its defining property pullback_classOf, and property \
  (2) is \
  read against it by IsChernCharacterOnLocallyFree.map_pull_kzero. psi^2([L]) = [L tensor L] is \
  read in Pic, \
  where addition is the tensor product by Tag 01CX (picardClassOf_tensorObjRingedSpace)"]
theorem chernCharacter_secondAdams_kZero [∀ X : C, Algebra ℚ (𝔄.A X)]
    {ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hch : IsChernCharacterOnLocallyFree 𝔄.toChernSetup ch)
    (hψpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      VectorBundleKZero.pullbackRingHom (S.map f) (ψ Y α) =
        ψ X (VectorBundleKZero.pullbackRingHom (S.map f) α))
    (hψinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ∃ (M : (S.obj X).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsInvertible
        (S.obj X).presheaf (S.obj X).ringCatSheaf.2 M),
        ψ X (VectorBundleKZero.classOf (S.obj X) L) =
            VectorBundleKZero.classOf (S.obj X) M ∧
          picardClassOf (S.obj X) M hM = 2 • picardClassOf (S.obj X) L hL)
    (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    ch X (ψ X α) n = (2 ^ n : ℕ) • ch X α n := by
  have hhom : (hch.componentHom X n).comp (ψ X).toAddMonoidHom =
      (AddMonoidHom.mk' (fun a : 𝔄.A X => (2 ^ n : ℕ) • a)
        fun a b => smul_add ((2 : ℕ) ^ n) a b).comp (hch.componentHom X n) := by
    refine VectorBundleKZero.addHom_ext fun E hE => ?_
    show ch X (ψ X (VectorBundleKZero.classOf (S.obj X) E)) n =
      (2 ^ n : ℕ) • ch X (VectorBundleKZero.classOf (S.obj X) E) n
    exact secondAdams_classOf_of_sum ψ (fun f a m => hch.map_pull_kzero f a m)
      (fun P k L M hL hM hpic n => by
        rw [hch.map_sum P Finset.univ _ n, hch.map_sum P Finset.univ _ n, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hch.invertible P (M j) (hM j) n, hch.invertible P (L j) (hL j) n, hpic j,
          map_nsmul, smul_pow, mul_smul_comm]) hψpull hψinv X E
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE) n
  exact DFunLike.congr_fun hhom α

end

/-! ### The second Adams operator this repository constructs -/

section Constructed

variable {𝔄 : SourceChernSetup.{u, v, v₁, w} C S}
  (hsq : ∀ X : C, VectorBundleKZero.SquarePowersData (S.obj X))

/-- `AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom` commutes with the pullback of
`K₀(Vect(-))`: the third clause of Tag 0FEJ, at the constructed pullback. -/
theorem secondAdamsRingHom_pullback {X Y : C} (f : X ⟶ Y)
    (α : VectorBundleKZero (S.obj Y)) :
    VectorBundleKZero.pullbackRingHom (S.map f)
        (VectorBundleKZero.secondAdamsRingHom (hsq Y) α) =
      VectorBundleKZero.secondAdamsRingHom (hsq X)
        (VectorBundleKZero.pullbackRingHom (S.map f) α) := by
  simp only [VectorBundleKZero.secondAdamsRingHom_apply]
  exact (VectorBundleKZero.secondAdamsAddHom_pullback (S.map f) (hsq X) (hsq Y)
    (VectorBundleKZero.pullbackRingHom (S.map f))
    (fun E hE => VectorBundleKZero.pullbackRingHom_classOf (S.map f) E hE)
    (fun E hE => VectorBundleKZero.isFiniteLocallyFree_pullback (S.map f) E hE) α).symm

/-- `AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom` sends the class of an invertible
module `ℒ` to the class of an invertible module whose class in `Pic` is twice that of `ℒ`: the
second clause of Tag 0FEJ, read in `Pic` through Tag 01CX. -/
theorem secondAdamsRingHom_classOf_invertible (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) :
    ∃ (M : (S.obj X).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsInvertible
      (S.obj X).presheaf (S.obj X).ringCatSheaf.2 M),
      VectorBundleKZero.secondAdamsRingHom (hsq X)
            (VectorBundleKZero.classOf (S.obj X) L) =
          VectorBundleKZero.classOf (S.obj X) M ∧
        picardClassOf (S.obj X) M hM = 2 • picardClassOf (S.obj X) L hL := by
  have : Stacks.SheafOfModules.IsInvertible (S.obj X).sheaf.obj
      (S.obj X).ringCatSheaf.property L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr hL
  refine ⟨Scheme.Modules.tensorObjRingedSpace (S.obj X) L L,
    isInvertible_tensorObjRingedSpace L L hL hL, ?_, ?_⟩
  · rw [VectorBundleKZero.secondAdamsRingHom_apply]
    exact VectorBundleKZero.secondAdamsAddHom_classOf_isInvertible (hsq X) L
  · rw [picardClassOf_tensorObjRingedSpace L L hL hL
      (isInvertible_tensorObjRingedSpace L L hL hL), two_nsmul]

/-- **Tag 0FIA for the total Chern class and the second Adams operator of this repository.** The
general statement `Stacks.WeilCohomology.chernClass_secondAdams_kZero` at
`AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom`, whose two named properties are
`Stacks.WeilCohomology.secondAdamsRingHom_pullback` and
`secondAdamsRingHom_classOf_invertible`. -/
theorem chernClass_secondAdams_secondAdamsRingHom
    {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hc : IsTotalChernClassOnLocallyFree 𝔄.toChernSetup c)
    (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    c X (VectorBundleKZero.secondAdamsRingHom (hsq X) α) n = (2 ^ n : ℕ) • c X α n :=
  chernClass_secondAdams_kZero (fun Z => VectorBundleKZero.secondAdamsRingHom (hsq Z)) hc
    (fun f a => secondAdamsRingHom_pullback hsq f a)
    (fun Z L hL => secondAdamsRingHom_classOf_invertible hsq Z L hL) X α n

/-- **Tag 0FIA for the Chern character and the second Adams operator of this repository.** The
general statement `Stacks.WeilCohomology.chernCharacter_secondAdams_kZero` at
`AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom`. -/
theorem chernCharacter_secondAdams_secondAdamsRingHom [∀ X : C, Algebra ℚ (𝔄.A X)]
    {ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hch : IsChernCharacterOnLocallyFree 𝔄.toChernSetup ch)
    (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    ch X (VectorBundleKZero.secondAdamsRingHom (hsq X) α) n = (2 ^ n : ℕ) • ch X α n :=
  chernCharacter_secondAdams_kZero (fun Z => VectorBundleKZero.secondAdamsRingHom (hsq Z)) hch
    (fun f a => secondAdamsRingHom_pullback hsq f a)
    (fun Z L hL => secondAdamsRingHom_classOf_invertible hsq Z L hL) X α n

end Constructed

end Stacks.WeilCohomology

end
