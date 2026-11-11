module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementFormalFunctions
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalFunctionsDegreeZero
public import StacksCore.Tactic.StacksAttribute

/-!
# Formal functions in higher degrees: cohomology away from a closed set commutes with reduction

Let `A` be a Noetherian ring which is `f`-adically complete, let `f ∈ 𝔞`, let `M` be a finite
`A`-module, let `s ≥ 0`, and assume `H^k_𝔞(M)` is annihilated by a power of `f` for every
`k ≤ s + 1`. Then with `U = Spec(A) ∖ V(𝔞)` the canonical map

`H^i(U, M̃) ⟶ lim_n H^i(U, (M/fⁿM)̃)`

is an isomorphism for every `i < s`.

Cohomology on `U` is the cohomology of derived sections on `U`, modelled by the cone of the Čech
augmentation of a finite family of generators of `𝔞`; this is the functor
`Stacks.Algebraization.complementCohomologyFunctor`, whose degree-`i` value on `M` is `H^{i+1}_𝔞(M)`
for `i ≥ 1` and `Γ(U, M̃)` for `i = 0`. That model is identified with the sheaf cohomology of
`M̃|U` on the open subscheme `U`, naturally in `M`, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/ComplementSheafCohomologyComparison.lean`, and the
statement for sheaf cohomology is deduced in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/ComplementFormalFunctionsSheaf.lean`.

## The argument

Fix `i` and write `H^i` for `H^i(U, -)`. The comparison map factors as

`H^i(M) --κ--> limₙ H^i(M) / fⁿ H^i(M) --lim ψₙ--> limₙ H^i(M/fⁿM)`

exactly as in degree zero: `fⁿ` annihilates `M/fⁿM`, hence `H^i(M/fⁿM)`, so the reduction map
kills `fⁿ H^i(M)` and `ψₙ` is defined. The first map is a bijection precisely when `H^i(M)` is
`f`-adically complete, and the second is handled by the pro-zero criterion
`Stacks.ProZero.bijective_towerSectionsMap_of_proZero`, whose two inputs are the kernel and
cokernel steps of the degree-zero argument with the degrees shifted: both only ever use the long
exact sequences of derived sections on `U` attached to `0 → fⁿM → M → M/fⁿM → 0` and
`0 → M[fⁿ] → M → fⁿM → 0` in the two consecutive degrees `i` and `i + 1`, together with the
annihilation of `H^{i+1}(M)` by a power of `f`. The declarations
`Stacks.Algebraization.exists_pow_smul_of_complementCohomology_quotient_eq_zero` and
`Stacks.Algebraization.exists_complementCohomology_preimage_of_quotient` are the case `i = 0` of
the two steps proved here.

The completeness of `H^i(M)` is where the two ranges of `i` part company. For `i ≥ 1` the module
`H^i(M) = H^{i+1}_𝔞(M)` is itself killed by a power of `f`, so its `f`-adic filtration is
eventually zero and completeness is automatic. For `i = 0` the module `Γ(U, M̃)` is an extension
of `H¹_𝔞(M)` by `M / H⁰_𝔞(M)`, and its completeness is
`Stacks.Algebraization.isAdicComplete_complementGlobalSections`.

## Main definitions

* `Stacks.Algebraization.HigherComplementTower.quotientCohomologyTower` — the tower
  `H^i(U, (M/fⁿM)̃)` with its reduction transition maps.
* `Stacks.Algebraization.HigherComplementTower.toTowerSections` — the canonical map from
  `H^i(U, M̃)` to the compatible sequences of that tower.

## Main results

* `Stacks.Algebraization.HigherComplementTower.bijective_toTowerSections_of_isAdicComplete` — the
  comparison map in degree `i` is a bijection as soon as `H^i(U, M̃)` is `f`-adically complete and
  `H^{i+1}(U, M̃)` is annihilated by a power of `f`.
* `Stacks.Algebraization.HigherComplementTower.bijective_toTowerSections`: the comparison map is
  a bijection for every `i < s`, in the Čech cone model of `H^i(U, -)`. Its transport to sheaf
  cohomology on `U`, which is Stacks 0EKM, is
  `Stacks.Algebraization.HigherComplementTower.bijective_sheafCohomologyToTowerSections` in
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/ComplementFormalFunctionsSheaf.lean`.

## References

* [Stacks Project, Tag 0EKM](https://stacks.math.columbia.edu/tag/0EKM)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.LocalCohomology Stacks.ProZero

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **A module annihilated by a power of `f` is `f`-adically complete.** Its `f`-adic filtration
is eventually the zero submodule, so the canonical map to the completion is a bijection. -/
theorem isAdicComplete_of_pow_smul_eq_zero {R : Type u} [CommRing R] {N : Type*}
    [AddCommGroup N] [Module R N] (f : R) (c : ℕ) (h : ∀ x : N, f ^ c • x = 0) :
    IsAdicComplete (Ideal.span {f}) N :=
  isAdicComplete_of_pow_smul_top_le (Ideal.span {f}) ⊥ c
    (le_of_eq (smul_top_eq_bot_of_pow_smul_eq_zero f c h)) inferInstance

end Stacks.Algebraization

namespace Stacks.Algebraization.HigherComplementTower

open Stacks.Algebraization

variable {A : Type u} [CommRing A] {r : ℕ} (fam : Fin r → A) (f : A) (M : ModuleCat.{u} A)

/-! ### The two pro-zero steps in an arbitrary degree -/

/-- The image of a class under `H^i(U, M̃) ⟵ H^i(U, (fᵐM)̃) ⟶ H^i(U, (fᵖM)̃)` comes from
`H^i(U, M̃)`: the connecting map of the level-`p` torsion sequence kills it. -/
private theorem exists_torsion_preimage_powerSmulTopLE (i j : ℤ) (hij : i + 1 = j) {p m : ℕ}
    (hpm : p ≤ m) (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0)
    (u : (complementCohomologyFunctor fam i).obj (ModuleCat.of A (powerSmulTop f M m))) :
    ∃ w : (complementCohomologyFunctor fam i).obj M,
      (complementCohomologyFunctor fam i).map (powerTorsionShortComplex f M p).g w =
        (complementCohomologyFunctor fam i).map (powerSmulTopLE f M hpm) u := by
  refine (exact_complementCohomologyFunctor_δ fam (powerTorsionShortComplex f M p)
    (powerTorsionShortComplex_shortExact f M p) i j hij _).1 ?_
  refine (complementCohomologyFunctorδ_naturality fam
    (powerTorsionShortComplex_shortExact f M m) (powerTorsionShortComplex_shortExact f M p)
    (powerTorsionSESMap f M hpm hkill) i j hij u).trans ?_
  rw [powerTorsionSESMap_τ₁]
  exact complementCohomologyFunctor_map_zero_apply fam j _

/-- **The kernel step in degree `i`.** Let `p ≤ m` and suppose `f ^ (m - p)` annihilates `M[fᵐ]`.
A class in `H^i(U, M̃)` whose image in `H^i(U, (M/fᵐM)̃)` vanishes is `f ^ p` times a class in
`H^i(U, M̃)`.

It comes from `H^i(U, (fᵐM)̃)`, by exactness of the quotient sequence at the middle term. The
connecting map `H^i → H^{i+1}` of the level-`p` torsion sequence kills its image in
`H^i(U, (fᵖM)̃)`, because that connecting map factors through the first component of the morphism
of torsion sequences, which is zero; so by exactness that image is a value of
`H^i(U, M̃) ⟶ H^i(U, (fᵖM)̃)`. Composing with `fᵖM ⊆ M`, which turns that map into multiplication
by `f ^ p`, gives the conclusion. -/
theorem exists_pow_smul_of_quotient_eq_zero (i j : ℤ) (hij : i + 1 = j) {p m : ℕ} (hpm : p ≤ m)
    (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0)
    (s : (complementCohomologyFunctor fam i).obj M)
    (hs : (complementCohomologyFunctor fam i).map (powerQuotientShortComplex f M m).g s = 0) :
    ∃ w : (complementCohomologyFunctor fam i).obj M, s = f ^ p • w := by
  obtain ⟨u, hu⟩ := (exact_complementCohomologyFunctor_map fam (powerQuotientShortComplex f M m)
    (powerQuotientShortComplex_shortExact f M m) i s).1 hs
  obtain ⟨w, hw⟩ := exists_torsion_preimage_powerSmulTopLE fam f M i j hij hpm hkill u
  refine ⟨w, ?_⟩
  have key : (complementCohomologyFunctor fam i).map ((f ^ p) • 𝟙 M) w = s := by
    rw [← powerSmulToSmulTop_comp_subtype f M p]
    refine (complementCohomologyFunctor_map_comp_apply fam i _ _ w).trans ?_
    erw [hw]
    refine (complementCohomologyFunctor_map_comp_apply fam i
      (powerSmulTopLE f M hpm) (powerQuotientShortComplex f M p).f u).symm.trans ?_
    exact (congrArg (fun φ ↦ (complementCohomologyFunctor fam i).map φ u)
      (powerSmulTopLE_comp_subtype f M hpm)).trans hu
  rw [← key, complementCohomologyFunctor_map_smul_id_apply fam i M (f ^ p) w]

/-- **The cokernel step in degree `i`.** Let `n ≤ p ≤ m`, suppose `f ^ (m - p)` annihilates
`M[fᵐ]`, and suppose `f ^ (p - n)` annihilates `H^{i+1}(U, M̃)`. Then every class in
`H^i(U, (M/fᵐM)̃)` has its image in `H^i(U, (M/fⁿM)̃)` in the image of `H^i(U, M̃)`.

By exactness of the level-`n` quotient sequence at the third term it is enough that the connecting
map kill that image, and by naturality the value of the connecting map there is the image in
`H^{i+1}(U, (fⁿM)̃)` of the level-`m` connecting class `z`. Pushing `z` to level `p` lands it in a
value of `H^{i+1}(U, M̃) ⟶ H^{i+1}(U, (fᵖM)̃)`, exactly as in the kernel step; and pushing on to
level `n` turns that map into multiplication by `f ^ (p - n)` on `H^{i+1}(U, M̃)` followed by
`H^{i+1}(U, M̃) ⟶ H^{i+1}(U, (fⁿM)̃)`, so it is zero. -/
theorem exists_preimage_of_quotient (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k)
    {n p m : ℕ} (hnp : n ≤ p) (hpm : p ≤ m)
    (hkill : ∀ x : M, f ^ m • x = 0 → f ^ (m - p) • x = 0)
    (hc : ∀ x : (complementCohomologyFunctor fam j).obj M, f ^ (p - n) • x = 0)
    (y : (complementCohomologyFunctor fam i).obj (powerQuotientShortComplex f M m).X₃) :
    ∃ s : (complementCohomologyFunctor fam i).obj M,
      (complementCohomologyFunctor fam i).map (powerQuotientShortComplex f M n).g s =
        (complementCohomologyFunctor fam i).map
          (powerQuotientSESMap f M (hnp.trans hpm)).τ₃ y := by
  obtain ⟨z, hzdef⟩ : ∃ z, DerivedCategory.HomologySequence.δ
      (cechComplementTriangle.{u} fam (powerQuotientShortComplex f M m)
        (powerQuotientShortComplex_shortExact f M m)) i j hij y = z := ⟨_, rfl⟩
  have hnat := complementCohomologyFunctorδ_naturality fam
    (powerQuotientShortComplex_shortExact f M m) (powerQuotientShortComplex_shortExact f M n)
    (powerQuotientSESMap f M (hnp.trans hpm)) i j hij y
  rw [hzdef] at hnat
  obtain ⟨w, hw⟩ := exists_torsion_preimage_powerSmulTopLE fam f M j k hjk hpm hkill z
  have hzero : (complementCohomologyFunctor fam j).map
      (powerSmulTopLE f M (hnp.trans hpm)) z = 0 := by
    have h1 : (complementCohomologyFunctor fam j).map (powerSmulTopLE f M (hnp.trans hpm)) z =
        (complementCohomologyFunctor fam j).map ((powerTorsionShortComplex f M p).g ≫
          powerSmulTopLE f M hnp) w := by
      refine Eq.symm ((complementCohomologyFunctor_map_comp_apply fam j _ _ w).trans ?_)
      erw [hw]
      refine (complementCohomologyFunctor_map_comp_apply fam j
        (powerSmulTopLE f M hpm) (powerSmulTopLE f M hnp) z).symm.trans ?_
      exact congrArg (fun φ ↦ (complementCohomologyFunctor fam j).map φ z)
        (powerSmulTopLE_trans f M hnp hpm)
    refine h1.trans ?_
    refine (congrArg (fun φ ↦ (complementCohomologyFunctor fam j).map φ w)
      (powerSmulToSmulTop_comp_powerSmulTopLE f M hnp)).trans ?_
    refine (complementCohomologyFunctor_map_comp_apply fam j ((f ^ (p - n)) • 𝟙 M)
      (powerTorsionShortComplex f M n).g w).trans ?_
    rw [complementCohomologyFunctor_map_smul_id_apply fam j M (f ^ (p - n)) w, hc w]
    exact map_zero _
  exact (exact_complementCohomologyFunctor_δ fam (powerQuotientShortComplex f M n)
    (powerQuotientShortComplex_shortExact f M n) i j hij
    ((complementCohomologyFunctor fam i).map
      (powerQuotientSESMap f M (hnp.trans hpm)).τ₃ y)).1 (hnat.trans hzero)

/-! ### The tower of cohomology of the quotients, and the comparison with the `f`-adic tower -/

/-- The tower `H^i(U, (M/fⁿM)̃)` of degree-`i` cohomology of derived sections on `U` of the
quotients of `M` by the powers of `f`. -/
abbrev quotientCohomologyTower (i : ℤ) (n : ℕ) : ModuleCat.{u} A :=
  (complementCohomologyFunctor fam i).obj (powerQuotientShortComplex f M n).X₃

/-- The transition maps of the tower `H^i(U, (M/fⁿM)̃)`, induced by the projections between the
quotients. -/
abbrev quotientCohomologyTransition (i : ℤ) (n : ℕ) :
    quotientCohomologyTower fam f M i (n + 1) ⟶ quotientCohomologyTower fam f M i n :=
  (complementCohomologyFunctor fam i).map (powerQuotientSESMap f M (Nat.le_succ n)).τ₃

/-- The map `H^i(U, M̃) ⟶ H^i(U, (M/fⁿM)̃)` induced by the reduction `M ⟶ M / fⁿM`. -/
abbrev quotientReduction (i : ℤ) (n : ℕ) :
    (complementCohomologyFunctor fam i).obj M ⟶ quotientCohomologyTower fam f M i n :=
  (complementCohomologyFunctor fam i).map (powerQuotientShortComplex f M n).g

/-- `fⁿ` annihilates `H^i(U, (M/fⁿM)̃)`, because it annihilates `M / fⁿM`. -/
theorem pow_smul_quotientCohomologyTower_eq_zero (i : ℤ) (n : ℕ)
    (y : quotientCohomologyTower fam f M i n) : f ^ n • y = 0 :=
  smul_complementCohomologyFunctor_eq_zero fam i _ (f ^ n)
    (pow_smul_powerQuotient_eq_zero f M n) y

/-- `fⁿ H^i(U, M̃)` is killed by the reduction map, because `fⁿ` annihilates its target. -/
theorem powerSmulTop_le_ker_reductionMap (i : ℤ) (n : ℕ) :
    (Ideal.span {f}) ^ n • (⊤ : Submodule A ((complementCohomologyFunctor fam i).obj M)) ≤
      LinearMap.ker (quotientReduction fam f M i n).hom := by
  refine Submodule.smul_le.2 ?_
  intro a ha x _
  rw [Ideal.span_singleton_pow] at ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [LinearMap.mem_ker, map_smul, mul_comm b (f ^ n), mul_smul]
  exact pow_smul_quotientCohomologyTower_eq_zero fam f M i n _

/-- **The level-`n` comparison `H^i(U, M̃) / fⁿ H^i(U, M̃) ⟶ H^i(U, (M/fⁿM)̃)`.** It is induced by
the reduction `M ⟶ M / fⁿM`, which kills `fⁿ H^i(U, M̃)` because `fⁿ` annihilates its target. -/
def quotientCompare (i : ℤ) (n : ℕ) :
    adicTower (Ideal.span {f}) ((complementCohomologyFunctor fam i).obj M) n ⟶
      quotientCohomologyTower fam f M i n :=
  ModuleCat.ofHom (Submodule.liftQ _ (quotientReduction fam f M i n).hom
    (powerSmulTop_le_ker_reductionMap fam f M i n))

/-- The level-`n` comparison sends the class of `s` to the reduction of `s`. -/
theorem quotientCompare_mk (i : ℤ) (n : ℕ) (s : (complementCohomologyFunctor fam i).obj M) :
    quotientCompare fam f M i n (Submodule.Quotient.mk s) = quotientReduction fam f M i n s := rfl

/-- The reductions to the quotients are compatible with the transition maps. -/
private theorem quotientCohomologyTransition_quotientReduction (i : ℤ) (n : ℕ)
    (s : (complementCohomologyFunctor fam i).obj M) :
    quotientCohomologyTransition fam f M i n (quotientReduction fam f M i (n + 1) s) =
      quotientReduction fam f M i n s :=
  (complementCohomologyFunctor_map_comp_apply fam i (powerQuotientShortComplex f M (n + 1)).g
    (powerQuotientSESMap f M (Nat.le_succ n)).τ₃ s).symm.trans
    (congrArg (fun φ ↦ (complementCohomologyFunctor fam i).map φ s)
      (powerQuotient_g_comp_τ₃ f M (Nat.le_succ n)))

/-- The comparison maps commute with the transition maps of the two towers. -/
theorem quotientCompare_comm (i : ℤ) (n : ℕ)
    (x : adicTower (Ideal.span {f}) ((complementCohomologyFunctor fam i).obj M) (n + 1)) :
    quotientCohomologyTransition fam f M i n (quotientCompare fam f M i (n + 1) x) =
      quotientCompare fam f M i n
        (adicTowerTransition (Ideal.span {f})
          ((complementCohomologyFunctor fam i).obj M) n x) := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [quotientCompare_mk]
  exact (quotientCohomologyTransition_quotientReduction fam f M i n s).trans
    (quotientCompare_mk fam f M i n s).symm

/-- **The comparison of the two towers is a bijection on compatible sequences** when
`H^{i+1}(U, M̃)` is annihilated by `f ^ c`: both the kernels and the cokernels of the level maps
are pro-zero, so `Stacks.ProZero.bijective_towerSectionsMap_of_proZero` applies. -/
theorem bijective_towerSectionsMap_quotientCompare [IsNoetherian A M] (i j : ℤ) (hij : i + 1 = j)
    (c : ℕ) (hc : ∀ x : (complementCohomologyFunctor fam j).obj M, f ^ c • x = 0) :
    Function.Bijective (towerSectionsMap
      (adicTowerTransition (Ideal.span {f}) ((complementCohomologyFunctor fam i).obj M))
      (quotientCohomologyTransition fam f M i) (quotientCompare fam f M i)
      (quotientCompare_comm fam f M i)) := by
  obtain ⟨Nst, hNst⟩ := exists_powerTorsion_stable f M
  refine bijective_towerSectionsMap_of_proZero _ _ _ _ ?_ ?_
  · intro n
    refine ⟨n + Nst, Nat.le_add_right n Nst, ?_⟩
    intro x hx
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, hw⟩ := exists_pow_smul_of_quotient_eq_zero fam f M i j hij
      (Nat.le_add_right n Nst)
      (pow_smul_eq_zero_of_powerTorsion_stable f M hNst (by omega) (by omega)) s hx
    rw [towerMapLE_adicTower]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rw [hw]
    exact powerSmul_mem_powerSmulTop f ((complementCohomologyFunctor fam i).obj M) n w
  · intro n
    refine ⟨n + c + Nst, by omega, ?_⟩
    intro y
    obtain ⟨s, hs⟩ := exists_preimage_of_quotient fam f M i j (j + 1) hij rfl
      (Nat.le_add_right n c) (Nat.le_add_right (n + c) Nst)
      (pow_smul_eq_zero_of_powerTorsion_stable f M hNst (by omega) (by omega))
      (by
        intro x
        rw [Nat.add_sub_cancel_left]
        exact hc x) y
    refine ⟨Submodule.Quotient.mk s, ?_⟩
    rw [quotientCompare_mk,
      towerMapLE_functor (complementCohomologyFunctor fam i)
        (fun k ↦ (powerQuotientShortComplex f M k).X₃)
        (fun k ↦ (powerQuotientSESMap f M (Nat.le_succ k)).τ₃) (by omega : n ≤ n + c + Nst),
      towerMapLE_powerQuotient]
    exact hs

/-! ### The comparison map and its bijectivity -/

/-- **The canonical map `H^i(U, M̃) ⟶ lim_n H^i(U, (M/fⁿM)̃)`**, whose `n`-th component is the map
induced by the reduction `M ⟶ M / fⁿM`. -/
def toTowerSections (i : ℤ) :
    (complementCohomologyFunctor fam i).obj M →ₗ[A]
      towerSections (quotientCohomologyTower fam f M i)
        (quotientCohomologyTransition fam f M i) where
  toFun x :=
    ⟨fun n ↦ quotientReduction fam f M i n x, fun n ↦ by
      refine (complementCohomologyFunctor_map_comp_apply fam i
        (powerQuotientShortComplex f M (n + 1)).g
        (powerQuotientSESMap f M (Nat.le_succ n)).τ₃ x).symm.trans ?_
      exact congrArg (fun φ ↦ (complementCohomologyFunctor fam i).map φ x)
        (powerQuotient_g_comp_τ₃ f M (Nat.le_succ n))⟩
  map_add' x y := Subtype.ext (funext fun n ↦ map_add (quotientReduction fam f M i n).hom x y)
  map_smul' a x := Subtype.ext (funext fun n ↦ map_smul (quotientReduction fam f M i n).hom a x)

/-- The `n`-th component of the comparison map is the reduction map to `H^i(U, (M/fⁿM)̃)`. -/
@[simp]
theorem toTowerSections_apply_coe (i : ℤ) (x : (complementCohomologyFunctor fam i).obj M)
    (n : ℕ) : (toTowerSections fam f M i x).1 n = quotientReduction fam f M i n x := rfl

/-- The comparison map factors through the `f`-adic tower of `H^i(U, M̃)`. -/
theorem toTowerSections_eq (i : ℤ) (x : (complementCohomologyFunctor fam i).obj M) :
    toTowerSections fam f M i x =
      towerSectionsMap
        (adicTowerTransition (Ideal.span {f}) ((complementCohomologyFunctor fam i).obj M))
        (quotientCohomologyTransition fam f M i) (quotientCompare fam f M i)
        (quotientCompare_comm fam f M i)
        (toAdicTowerSections (Ideal.span {f})
          ((complementCohomologyFunctor fam i).obj M) x) :=
  Subtype.ext (funext fun _ ↦ rfl)

/-- **The comparison map in degree `i` is a bijection** as soon as `H^i(U, M̃)` is `f`-adically
complete and `H^{i+1}(U, M̃)` is annihilated by `f ^ c`.

The map factors as the canonical map into the compatible sequences of the `f`-adic tower of
`H^i(U, M̃)`, which is a bijection by completeness, followed by the comparison of that tower with
the tower `H^i(U, (M/fⁿM)̃)`, which is a bijection by the pro-zero criterion. -/
theorem bijective_toTowerSections_of_isAdicComplete [IsNoetherian A M] (i j : ℤ)
    (hij : i + 1 = j) (c : ℕ)
    (hcomplete : IsAdicComplete (Ideal.span {f})
      ((complementCohomologyFunctor fam i).obj M))
    (hc : ∀ x : (complementCohomologyFunctor fam j).obj M, f ^ c • x = 0) :
    Function.Bijective (toTowerSections fam f M i) := by
  have := hcomplete
  have hb : Function.Bijective (fun x ↦ toTowerSections fam f M i x) := by
    rw [funext (toTowerSections_eq fam f M i)]
    exact (bijective_towerSectionsMap_quotientCompare fam f M i j hij c hc).comp
      (bijective_toAdicTowerSections (Ideal.span {f})
        ((complementCohomologyFunctor fam i).obj M))
  exact hb

/-! ### Completeness of the source in the two ranges of degrees -/

/-- **In degree zero the source is `f`-adically complete** under the first hypothesis of Stacks
0EII: `Γ(U, M̃)` is an extension of `H¹_𝔞(M)` by `M / H⁰_𝔞(M)`, the submodule is a finite module
over a complete Noetherian ring and the quotient is killed by `f ^ c`. -/
theorem isAdicComplete_complementCohomology_zero {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} (hI : I.FG) {r : ℕ} (fam : Fin r → A)
    (hfam : Ideal.span (Set.range fam) = I) (f : A) (M : ModuleCat.{u} A) [Module.Finite A M]
    [IsAdicComplete (Ideal.span {f}) A] (c : ℕ)
    (h1 : ∀ x : localCohomologyModule A I hI M 1, f ^ c • x = 0) :
    IsAdicComplete (Ideal.span {f}) ((complementCohomologyFunctor fam (0 : ℤ)).obj M) :=
  Stacks.Examples.isAdicComplete_of_linearEquiv
    ((cechLocalizationTriangleData.{u} fam I hI hfam).sectionsIso M)
    (isAdicComplete_complementGlobalSections A I hI f M c h1)

/-- **In a degree `i ≥ 1` the cohomology `H^i(U, M̃)` is `H^{i+1}_𝔞(M)`**, so if the latter is
annihilated by `f ^ c` then so is the former. -/
theorem pow_smul_complementCohomology_eq_zero {A : Type u} [CommRing A]
    {I : Ideal A} (hI : I.FG) {r : ℕ} (fam : Fin r → A)
    (hfam : Ideal.span (Set.range fam) = I) (f : A) (M : ModuleCat.{u} A) (i : ℕ) (hi : 1 ≤ i)
    (c : ℕ) (h : ∀ x : localCohomologyModule A I hI M ((i : ℤ) + 1), f ^ c • x = 0)
    (x : (complementCohomologyFunctor fam (i : ℤ)).obj M) : f ^ c • x = 0 := by
  set e := homologyComplementIsoLocalCohomologyModule
    (cechLocalizationTriangleData.{u} fam I hI hfam) M i hi with he
  have hinj : Function.Injective e.hom.hom :=
    fun _ _ hh ↦ (ModuleCat.mono_iff_injective e.hom).1 inferInstance hh
  exact hinj ((map_smul _ (f ^ c) x).trans ((h _).trans (_root_.map_zero _).symm))

/-! ### Stacks 0EKM -/

/-- Let `A` be a Noetherian ring, let `f ∈ 𝔞` be an element of a finitely generated ideal of `A`,
let `M` be a finite `A`-module and let `s ≥ 0`. Assume `A` is `f`-adically complete and `H^k_𝔞(M)`
is annihilated by a power of `f` for `k ≤ s + 1`. Then with `U = Spec(A) ∖ V(𝔞)` the canonical map
`H^i(U, M̃) ⟶ lim_n H^i(U, (M/fⁿM)̃)` is a bijection for every `i < s`.

Here `H^i(U, -)` is the Čech cone model `Stacks.Algebraization.complementCohomologyFunctor` of a
finite family generating `𝔞`. It is identified with the sheaf cohomology of [Stacks, Tag 01E3] on
`U`, naturally in the module, by
`Stacks.Algebraization.ComplementSheafComparison.hfunctorComplementTildeIso`, and the statement of
Stacks 0EKM for sheaf cohomology is
`Stacks.Algebraization.HigherComplementTower.bijective_sheafCohomologyToTowerSections`, which is
deduced from this one.

In degree zero the source is complete by the extension argument of Stacks 0EII; in a positive
degree `i < s` it equals `H^{i+1}_𝔞(M)`, which is killed by a power of `f` because `i + 1 ≤ s + 1`,
and a module killed by a power of `f` is complete. In both cases `H^{i+1}(U, M̃) = H^{i+2}_𝔞(M)` is
killed by a power of `f` because `i + 2 ≤ s + 1`. -/
theorem bijective_toTowerSections {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} (hI : I.FG) {r : ℕ} (fam : Fin r → A)
    (hfam : Ideal.span (Set.range fam) = I) (f : A) (hf : f ∈ I) (M : ModuleCat.{u} A)
    [Module.Finite A M] [IsAdicComplete (Ideal.span {f}) A] (s : ℕ)
    (hann : ∀ k : ℕ, k ≤ s + 1 →
      ∃ c : ℕ, ∀ x : localCohomologyModule A I hI M (k : ℤ), f ^ c • x = 0)
    (i : ℕ) (hi : i < s) :
    Function.Bijective (toTowerSections fam f M (i : ℤ)) := by
  have : f ∈ I := hf
  obtain ⟨c₂, hc₂⟩ := hann (i + 2) (by omega)
  have hc₂' : ∀ x : localCohomologyModule A I hI M (((i + 1 : ℕ) : ℤ) + 1), f ^ c₂ • x = 0 := by
    have hcast : ((i + 2 : ℕ) : ℤ) = ((i + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hc₂
    exact hc₂
  have hc : ∀ x : (complementCohomologyFunctor fam ((i + 1 : ℕ) : ℤ)).obj M,
      f ^ c₂ • x = 0 :=
    pow_smul_complementCohomology_eq_zero hI fam hfam f M (i + 1) (by omega) c₂ hc₂'
  have hij : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · obtain ⟨c₁, hc₁⟩ := hann 1 (by omega)
    have hcast1 : ((1 : ℕ) : ℤ) = (1 : ℤ) := by norm_num
    rw [hcast1] at hc₁
    have hcomplete : IsAdicComplete (Ideal.span {f})
        ((complementCohomologyFunctor fam (((0 : ℕ) : ℤ))).obj M) := by
      have h0 : ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
      rw [h0]
      exact isAdicComplete_complementCohomology_zero hI fam hfam f M c₁ hc₁
    exact bijective_toTowerSections_of_isAdicComplete fam f M _ _ hij c₂ hcomplete hc
  · obtain ⟨c₁, hc₁⟩ := hann (i + 1) (by omega)
    have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hc₁
    have hcomplete : IsAdicComplete (Ideal.span {f})
        ((complementCohomologyFunctor fam (i : ℤ)).obj M) :=
      isAdicComplete_of_pow_smul_eq_zero f c₁
        (pow_smul_complementCohomology_eq_zero hI fam hfam f M i hipos c₁ hc₁)
    exact bijective_toTowerSections_of_isAdicComplete fam f M _ _ hij c₂ hcomplete hc

end Stacks.Algebraization.HigherComplementTower

end
