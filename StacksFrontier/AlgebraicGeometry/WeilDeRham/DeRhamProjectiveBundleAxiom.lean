module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.ProjectiveBundleAxiomDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilData
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamBundleFormulaBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleFormula

/-!
# Axiom (A3) for de Rham cohomology

Let `k` be a field. Axiom (A3) of Weil Cohomology Theories, Section 0FID, for the data (D0), (D1),
(D2') of de Rham cohomology (`Stacks.DeRhamWeil.deRhamFirstChernClassData`, Section 0FWC) is the
projective bundle formula: for `X` smooth projective over `k`, `ℰ` locally free of rank `r + 1`
and `p : P = 𝐏(ℰ) → X`, the map `⨁_{i ≤ r} H^*_{dR}(X/k)(-i) → H^*_{dR}(P/k)`,
`(a_i) ↦ ∑ c₁^{dR}(𝒪_P(1))^i ∪ p^*(a_i)`, is bijective. This is how the proof of
Proposition 0FWD obtains (A3): from the projective bundle formula of Tag 0FMT, which is proved one
degree at a time (`Stacks.ProjectiveBundleDeRham.bijective_sum_cup_bundle`), and
`Stacks.WeilDeRham.projectiveBundleAxiom_of_degreewise`, which assembles the degrees.

The bridge between the two is bookkeeping: `H^*_{dR}(X/k)` is the direct sum of the groups
`H^n_{dR}(X/k)` of Tag 0FMT, its product is the cup product on homogeneous classes, and its
pullback is the pullback of each degree. The only non-literal point is the Tate twist: the class
`c₁^{dR}(𝒪_P(1))` read in the coordinates of the data on `H^*(P)(1)` is a nonzero multiple
`μ • c₁^{dR}(𝒪_P(1))` of the class of Tag 0FMT (the coordinate on the line `k` is a chosen one),
and the degreewise map for `μ • ξ` is that for `ξ` after rescaling the `i`-th summand by `μ^{-i}`.

## Main results

* `Stacks.WeilDeRham.of_pow_eq_deRhamCohomologyPow`: in `H^*_{dR}`, the `t`-th power of a class
  of degree `d` is its cup power `ξ^t ∈ H^{dt}_{dR}`.
* `Stacks.WeilDeRham.bijective_degreewiseMap_deRham`: the map
  `∏_{i ≤ r} H^{n - 2i}_{dR}(X/k) → H^n_{dR}(P/k)` of `Stacks.WeilDeRham.degreewiseMap`, for the
  de Rham data, is bijective.
* `Stacks.WeilDeRham.deRham_projectiveBundleAxiom`: **axiom (A3) for de Rham cohomology.**

## Implementation notes

The summands of Tag 0FMT and of this file are the same terms except for the proofs of
`IsFiniteLocallyFree ℰ` they carry (elaborated with different sheafification instances in scope).
They are identified by `convert`, argument by argument: unifying the two whole summands with
`exact` does not finish in reasonable time.

## References

* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace DirectSum
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme Stacks.DeRhamWeil
open AlgebraicGeometry.SheafOfModules (deRhamCohomology deRhamPiece gradedDeRhamCohomology
  deRhamCohomologyPow reindexDeRhamCohomology)

universe u

namespace Stacks.WeilDeRham

/-! ### Powers of homogeneous de Rham classes -/

section Pow

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier)
    (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u} φ))
  (D : AlgebraicGeometry.SheafOfModules.DeRhamDifferential B)

/-- **Powers of a homogeneous class are its cup powers**: in `H^*_{dR} = ⨁_n H^n_{dR}`, the
`t`-th power of the class of `ξ ∈ H^d_{dR}` is the class of `ξ^t ∈ H^{dt}_{dR}`. -/
theorem of_pow_eq_deRhamCohomologyPow (d : ℕ) (ξ : deRhamCohomology B D (d : ℤ)) (t : ℕ) :
    (DirectSum.of (deRhamPiece B D) (d : ℤ) ξ : gradedDeRhamCohomology B D) ^ t =
      DirectSum.of (deRhamPiece B D) ((d * t : ℕ) : ℤ) (deRhamCohomologyPow B D d ξ t) := by
  induction t with
  | zero => exact pow_zero _
  | succ t ih =>
    rw [pow_succ', ih, AlgebraicGeometry.SheafOfModules.gradedDeRhamCohomology_of_mul_of,
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow_succ,
      AlgebraicGeometry.SheafOfModules.of_reindexDeRhamCohomology]

end Pow

/-! ### The coordinate on the twist by the trivial line -/

section Twist

variable {k : Type u} [Field k]

/-- The scalar by which the coordinate `c` of the line `k` differs from its canonical coordinate,
on the twist by `k(1)`. -/
def twistScalar (c : k ≃ₗ[k] k) : k :=
  tateLineCoordinates c 1 ((tateLineCoordinates (LinearEquiv.refl k k) 1).symm 1)

/-- `Stacks.WeilDeRham.twistScalar` is nonzero, the coordinates being linear equivalences. -/
theorem twistScalar_ne_zero (c : k ≃ₗ[k] k) : twistScalar c ≠ 0 :=
  (LinearEquiv.map_ne_zero_iff _).2 ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero)

/-- **Two coordinates on `V(1)`**: reading `V(1)` in a coordinate `c` of the line `k` is reading it
in the canonical coordinate `Stacks.DeRhamWeil.untwist`, times `twistScalar c`. -/
theorem tateTwistCoordinates_untwist_symm (c : k ≃ₗ[k] k) (V : Type u) [AddCommGroup V]
    [Module k V] (y : V) :
    tateTwistCoordinates c 1 ((untwist V 1).symm y) = twistScalar c • y := by
  have hy : (untwist V 1).symm y =
      y ⊗ₜ[k] (tateLineCoordinates (LinearEquiv.refl k k) 1).symm (1 : k) := by
    apply (untwist V 1).injective
    rw [LinearEquiv.apply_symm_apply, untwist, tateTwistCoordinates_tmul,
      LinearEquiv.apply_symm_apply, one_smul]
  rw [hy, tateTwistCoordinates_tmul]
  rfl

/-- Rescaling `ξ` by `μ ≠ 0` and `x` by `μ^{-i}` leaves `ξ^i φ(x)` unchanged. -/
theorem smul_pow_mul_map_inv_pow_smul {F A B : Type*} [Field F] [Ring A] [Algebra F A] [Ring B]
    [Algebra F B] (φ : A →ₐ[F] B) {μ : F} (hμ : μ ≠ 0) (ξ : B) (i : ℕ) (x : A) :
    (μ • ξ) ^ i * φ ((μ⁻¹) ^ i • x) = ξ ^ i * φ x := by
  rw [smul_pow, map_smul, smul_mul_smul_comm, ← mul_pow, mul_inv_cancel₀ hμ, one_pow, one_smul]

end Twist

/-! ### The degreewise projective bundle formula for the de Rham data -/

section Bundle

variable {k : Type u} [Field k]

/-- A homogeneous class of degree `m` lies in the part of degree `m'` of `H^*_{dR}(X/k)` for
`m = m'`. -/
theorem of_mem_grade_of_eq (X : (SmoothProjectiveScheme k).FullSubcategory) {m m' : ℤ}
    (h : m = m') (x : piece X m) : DirectSum.of (piece X) m x ∈ grade X m' :=
  h ▸ of_mem_grade X m x

/-- Up to a nonzero scalar, `x ↦ [x]` is a bijection `H^m_{dR}(X/k) → H^*_{dR}(X/k)^{m'}` for
`m = m'`. -/
theorem bijective_smul_of_grade (X : (SmoothProjectiveScheme k).FullSubcategory) {m m' : ℤ}
    (h : m = m') {c : k} (hc : c ≠ 0) :
    Function.Bijective fun x : piece X m =>
      (⟨c • DirectSum.of (piece X) m x, Submodule.smul_mem _ c (of_mem_grade_of_eq X h x)⟩ :
        grade X m') := by
  subst h
  refine ⟨fun x y hxy => DirectSum.of_injective (β := piece X) m ?_, fun y => ?_⟩
  · exact smul_right_injective _ hc (congrArg Subtype.val hxy)
  · obtain ⟨z, hz⟩ := (DirectSum.mem_rangeGrading k (piece X) m _).1 (c⁻¹ • y).2
    refine ⟨z, Subtype.ext ?_⟩
    change c • DirectSum.of (piece X) m z = (y : cohomology X)
    rw [← hz, Submodule.coe_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- In `H^*_{dR}(P/k)`, for `c ∈ H^d_{dR}(P/k)`, `p : P → X` and `x ∈ H^m_{dR}(X/k)`,
`[c]^i ∪ p^*[x] = [c^i ∪ p^*x]`. -/
theorem of_pow_mul_pullback_of {P X : (SmoothProjectiveScheme k).FullSubcategory}
    (p : P ⟶ X) (d : ℕ) (c : piece P (d : ℤ)) (i : ℕ) (m : ℤ) (x : piece X m) :
    DirectSum.of (piece P) (d : ℤ) c ^ i * pullback p (DirectSum.of (piece X) m x) =
      DirectSum.of (piece P) (((d * i : ℕ) : ℤ) + m)
        (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras P) (differential P) _ m
          (deRhamCohomologyPow (algebras P) (differential P) d c i) (pullbackPiece p m x)) := by
  rw [pullback_of, of_pow_eq_deRhamCohomologyPow,
    AlgebraicGeometry.SheafOfModules.gradedDeRhamCohomology_of_mul_of]

/-- `c₁^{dR}(𝒪_P(1))` in the coordinates of the de Rham data is `twistScalar` times the class of
`c₁^{dR}(𝒪_P(1)) ∈ H^2_{dR}(P/k)`. -/
theorem bundleClassU_deRham (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    (deRhamFirstChernClassData k).bundleClassU X E r =
      (twistScalar (deRhamFirstChernClassData k).coord •
        DirectSum.of (piece (bundle X E r)) 2 (firstChernClassPiece (bundle X E r)
          (picardClassOf (Stacks.Chow.bundle E) (Stacks.Chow.bundleTwist E)
            (Stacks.Chow.isInvertible_bundleTwist E))) :
        (deRhamFirstChernClassData k).H (bundle X E r)) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  rw [FirstChernClassData.bundleClassU, FirstChernClassData.bundleClass]
  change tateTwistCoordinates (deRhamFirstChernClassData k).coord 1
    (firstChernClass (bundle X E r) (picardClassOf (Stacks.Chow.bundle E)
      (Stacks.Chow.bundleTwist E) (Stacks.Chow.isInvertible_bundleTwist E))) = _
  simp only [firstChernClass]
  exact tateTwistCoordinates_untwist_symm _ _ _

/-- **The `i`-th summand of the projective bundle formula of the de Rham data is that of
Tag 0FMT**: for `x ∈ H^{n - 2i}_{dR}(X/k)` rescaled by `μ^{-i}` (`μ = twistScalar`),
`ξ^i ∪ p^*(μ^{-i} [x])` is the class of `c₁^{dR}(𝒪_P(1))^i ∪ p^*x ∈ H^n_{dR}(P/k)`. -/
theorem bundleClassU_pow_mul_pull (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] (i : ℕ)
    (n : ℤ) (x : piece X (n - ((2 * i : ℕ) : ℤ))) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    (deRhamFirstChernClassData k).bundleClassU X E r ^ i *
        (deRhamFirstChernClassData k).pull (bundleProj X E r)
          ((twistScalar (deRhamFirstChernClassData k).coord)⁻¹ ^ i •
            (DirectSum.of (piece X) _ x : (deRhamFirstChernClassData k).H X)) =
      DirectSum.of (piece (bundle X E r)) n ((eqToHom (congrArg
          (AlgebraicGeometry.SheafOfModules.deRhamCohomology
            (Scheme.Hom.deRhamAlgebras (Stacks.Chow.bundleProj E ≫ X.obj.hom))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (Stacks.Chow.bundleProj E ≫ X.obj.hom))))
          (add_sub_cancel ((2 * i : ℕ) : ℤ) n))).hom
        (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ ((2 * i : ℕ) : ℤ)
          (n - ((2 * i : ℕ) : ℤ))
          (AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow _ _ 2
            (Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard
              (Stacks.Chow.bundleProj E ≫ X.obj.hom)
              (picardClassOf _ (Stacks.Chow.bundleTwist E)
                (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E
                  (Stacks.Chow.bundlePieces E)))) i)
          (DeRhamKatzOdaCech.deRhamPullbackModule (Stacks.Chow.bundleProj E) X.obj.hom
            (n - ((2 * i : ℕ) : ℤ)) x))) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  exact ((congrArg (fun ξ => ξ ^ i * (deRhamFirstChernClassData k).pull (bundleProj X E r)
      ((twistScalar (deRhamFirstChernClassData k).coord)⁻¹ ^ i •
        (DirectSum.of (piece X) _ x : (deRhamFirstChernClassData k).H X)))
      (bundleClassU_deRham X E r)).trans
    (smul_pow_mul_map_inv_pow_smul _ (twistScalar_ne_zero _) _ i _)).trans
    ((of_pow_mul_pullback_of (bundleProj X E r) 2 _ i _ x).trans
      ((AlgebraicGeometry.SheafOfModules.of_reindexDeRhamCohomology _ _
        (add_sub_cancel ((2 * i : ℕ) : ℤ) n) _).symm.trans
        (congrArg (DirectSum.of (piece (bundle X E r)) n)
          (AlgebraicGeometry.SheafOfModules.reindexDeRhamCohomology_eq_eqToHom _ _
            (add_sub_cancel ((2 * i : ℕ) : ℤ) n) _))))

/-- **The degreewise projective bundle formula for the de Rham data** ([Stacks, Tag 0FMT]): for
`X` smooth projective over `k`, `ℰ` locally free of rank `r + 1`, `p : P = 𝐏(ℰ) → X` and every
`n`, the map `∏_{i ≤ r} H^{n - 2i}_{dR}(X/k) → H^n_{dR}(P/k)`, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)`, is
bijective, `ξ` being `c₁^{dR}(𝒪_P(1))` read in the coordinates of the data. -/
theorem bijective_degreewiseMap_deRham (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] (n : ℤ) :
    Function.Bijective (degreewiseMap ((deRhamFirstChernClassData k).grade X)
      ((deRhamFirstChernClassData k).grade (bundle X E r))
      ((deRhamFirstChernClassData k).pull_grade (bundleProj X E r))
      ((deRhamFirstChernClassData k).bundleClassU_mem X E r) (r + 1) n) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  set μ := twistScalar (deRhamFirstChernClassData k).coord
  have hdeg : ∀ i : Fin (r + 1), n - (((2 * (i : ℕ) : ℕ)) : ℤ) = n - 2 * ((i : ℕ) : ℤ) :=
    fun i => by push_cast; ring
  -- The identification of the source of Tag 0FMT (spelled as there: the scheme of `X` read as
  -- `(toScheme k).obj X`) with that of `degreewiseMap`, the `i`-th summand rescaled by `μ^{-i}`.
  let Φ : (∀ i : Fin (r + 1), AlgebraicGeometry.SheafOfModules.deRhamCohomology
      (Scheme.Hom.deRhamAlgebras (X := (toScheme k).obj X) X.obj.hom)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras (X := (toScheme k).obj X) X.obj.hom))
      (n - ((2 * (i : ℕ) : ℕ) : ℤ))) →
      ∀ i : Fin (r + 1), (deRhamFirstChernClassData k).grade X (n - 2 * ((i : ℕ) : ℤ)) :=
    fun a i => ⟨(μ⁻¹) ^ (i : ℕ) • DirectSum.of (piece X) _ (a i),
      Submodule.smul_mem _ _ (of_mem_grade_of_eq X (hdeg i) (a i))⟩
  have hΦ : Function.Bijective Φ :=
    Function.Bijective.piMap fun i =>
      bijective_smul_of_grade X (hdeg i) (pow_ne_zero _ (inv_ne_zero (twistScalar_ne_zero _)))
  let Ψ : piece (bundle X E r) n → (deRhamFirstChernClassData k).grade (bundle X E r) n :=
    fun y => ⟨(1 : k) • DirectSum.of (piece (bundle X E r)) n y,
      Submodule.smul_mem _ _ (of_mem_grade_of_eq (bundle X E r) rfl y)⟩
  have hΨ : Function.Bijective Ψ := bijective_smul_of_grade (bundle X E r) rfl one_ne_zero
  have hΨc : ∀ y, ((Ψ y : (deRhamFirstChernClassData k).grade (bundle X E r) n) :
      (deRhamFirstChernClassData k).H (bundle X E r)) = DirectSum.of (piece (bundle X E r)) n y :=
    fun y => one_smul k _
  refine (Function.Bijective.of_comp_iff _ hΦ).1 ?_
  convert hΨ.comp (Stacks.ProjectiveBundleDeRham.bijective_sum_cup_bundle
    (X := (toScheme k).obj X) X.obj.hom E (r + 1) n) using 1
  funext a
  refine Subtype.ext ?_
  refine (coe_degreewiseMap _ _ _ _ (r + 1) n (Φ a)).trans ?_
  refine Eq.trans ?_ (hΨc _).symm
  refine Eq.trans ?_ (map_sum (DirectSum.of (piece (bundle X E r)) n) _ _).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  -- The two spellings of the summand differ only in the proofs of `IsFiniteLocallyFree ℰ` (the
  -- sheafification instances found here and in the file of Tag 0FMT); `convert` matches them
  -- argument by argument, where unifying the whole terms is very slow.
  convert bundleClassU_pow_mul_pull X E r (i : ℕ) n (a i) using 3

/-- **Axiom (A3) for de Rham cohomology** ([Stacks, Tag 0FMT], as used in the proof of
[Stacks, Proposition 0FWD]): for `X` smooth projective over `k`, `ℰ` locally free of rank
`r + 1` and `p : P = 𝐏(ℰ) → X`, the map `⨁_{i ≤ r} H^*_{dR}(X/k)(-i) → H^*_{dR}(P/k)`,
`(a_i) ↦ ∑ c₁^{dR}(𝒪_P(1))^i ∪ p^*(a_i)`, is bijective. -/
theorem deRham_projectiveBundleAxiom :
    (deRhamFirstChernClassData k).ProjectiveBundleAxiom :=
  projectiveBundleAxiom_of_degreewise _ fun X E r _ n => bijective_degreewiseMap_deRham X E r n

end Bundle

end Stacks.WeilDeRham

end
