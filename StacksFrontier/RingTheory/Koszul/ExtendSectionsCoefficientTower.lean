module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtensionAbsoluteTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedLimit
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower
public import StacksFrontier.RingTheory.Koszul.LiftedSheafAlgebras

/-!
# The sections of the extension of scalars to the Koszul sheaf are the coefficient Koszul tower

Let `R` be a commutative ring, `f₁, …, f_r ∈ R` and let `ℬ = (K_{n+1})_n` be the sheaf of
differential graded algebras of the proof of Proposition 0GZK on the natural numbers with the
chaotic topology (`Koszul.liftedPowSheafAlgebra`): over the stage `n` it is the Koszul algebra
`K_{n+1} = R⟨ξ₁, …, ξ_r⟩` with `d ξᵢ = fᵢ ^ (n + 1)`. For a complex `K` of `R`-modules the
extension of scalars `K ⊗_R ℬ` has over the stage `n` the complex of sections
`(⊕ₚ Kᵖ) ⊗_R K_{n+1}`. This file identifies the tower `n ↦ (K ⊗_R ℬ)(n)` of complexes of
sections with the strict coefficient Koszul tower of Tag 091Z
(`KoszulCoefficientTower.coefficientKoszulTower`), whose stage `n` has in degree `t` the module
`∏_{S ⊆ {1, …, r}} K^{t + |S|}`: the component of `x ⊗ e` at `S` is the coordinate of `e` at the
ordered wedge `e_S = ξ_{s₁} ∧ ⋯ ∧ ξ_{s_k}` times the component of `x` in degree `t + |S|`. No
sign twist is needed: the contraction of `e_S` and the signed tensor differential produce exactly
the signs `(-1)^{t + |S| + 1} (-1)^{#{s ∈ S, s < i}}` of `coefficientKoszulDifferential`.

## Main definitions

* `Koszul.stdWedge S` and `Koszul.extCoord S`: the ordered wedges of the standard basis of `Rʳ`
  in the exterior algebra, and the coordinates at them.
* `Koszul.tensorCoord f n K t`: the coordinates `(⊕ₚ Kᵖ) ⊗_R K_{n+1} → ∏_S K^{t + |S|}`.
* `Koszul.extendSectionsTower f K`: the tower of complexes of sections of `K ⊗_R ℬ`, and
  `Koszul.extendSectionsTowerMap f g`, `Koszul.extendSectionsTowerFunctor f` its functoriality.
* `Koszul.extendSectionsTowerIso f K`: **the isomorphism of towers of complexes of `R`-modules
  between the sections of `K ⊗_R ℬ` and the coefficient Koszul tower**, and
  `Koszul.extendSectionsTowerNatIso f` its naturality in `K`.

## Main results

* `Koszul.extendSectionsTowerIso_naturality`: the isomorphism is natural in `K`.
* `Koszul.extendUnit_extendSectionsTowerIso`: it carries the unit `k ↦ k ⊗ 1` to the
  augmentation of the coefficient Koszul tower.
* `Koszul.quasiIso_extendSectionsTowerMap`: extension of scalars to `ℬ` carries
  quasi-isomorphisms to sectionwise quasi-isomorphisms.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks
open scoped TensorProduct

universe u

namespace Koszul

/-! ### The ordered wedges of the standard basis -/

section Wedge

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The ordered wedge `e_S = ξ_{s₁} ∧ ⋯ ∧ ξ_{s_k}` of the standard basis vectors indexed by
`S = {s₁ < ⋯ < s_k}`. -/
def stdWedge (S : Finset (Fin r)) : ExteriorAlgebra R (Fin r → R) :=
  (S.sort.map fun i ↦ ExteriorAlgebra.ι R (Pi.single i (1 : R) : Fin r → R)).prod

/-- Inserting an index smaller than all others multiplies the ordered wedge on the left. -/
theorem stdWedge_insert (S : Finset (Fin r)) (i : Fin r) (hi : ∀ j ∈ S, i < j) :
    stdWedge (R := R) (insert i S) =
      ExteriorAlgebra.ι R (Pi.single i (1 : R) : Fin r → R) * stdWedge S := by
  have hnot : i ∉ S := fun h ↦ (hi i h).false
  simp only [stdWedge, Finset.sort_insert (· ≤ ·) (fun j hj ↦ (hi j hj).le) hnot,
    List.map_cons, List.prod_cons]

/-- The basis vectors of the exterior powers of `Rʳ` are the ordered wedges. -/
theorem exteriorPower_basis_eq_stdWedge {j : ℕ} (S : Finset (Fin r)) (hS : S.card = j) :
    (((Pi.basisFun R (Fin r)).exteriorPower j ⟨S, hS⟩ : ⋀[R]^j (Fin r → R)) :
      ExteriorAlgebra R (Fin r → R)) = stdWedge S := by
  subst hS
  rw [exteriorPower.basis_apply]
  show ExteriorAlgebra.ιMulti R S.card _ = _
  rw [ExteriorAlgebra.ιMulti_apply]
  simp only [Function.comp_apply, Pi.basisFun_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  show (List.ofFn (fun i ↦ ExteriorAlgebra.ι R
    (Pi.single ((S.orderEmbOfFin rfl) i) (1 : R) : Fin r → R))).prod = _
  rw [List.ofFn_comp' (S.orderEmbOfFin (k := S.card) rfl)
    (fun j : Fin r ↦ ExteriorAlgebra.ι R (Pi.single j (1 : R) : Fin r → R)),
    List.ofFn_eq_map, Finset.listMap_orderEmbOfFin_finRange]
  rfl

/-- The ordered wedge `e_S` lies in the `|S|`-th exterior power. -/
theorem stdWedge_mem (S : Finset (Fin r)) : stdWedge (R := R) S ∈ ⋀[R]^S.card (Fin r → R) := by
  rw [← exteriorPower_basis_eq_stdWedge S rfl]
  exact Subtype.property _

/-- **The contraction of an ordered wedge.** -/
theorem contraction_stdWedge (φ : Module.Dual R (Fin r → R)) (S : Finset (Fin r)) :
    contraction φ (stdWedge (R := R) S) =
      ∑ i ∈ S, ((-1 : R) ^ (S.filter (· < i)).card * φ (Pi.single i 1)) •
        stdWedge (S.erase i) := by
  classical
  induction S using Finset.induction_on_min with
  | empty => simp [stdWedge, contraction]
  | @insert i S hmin ih =>
    have hi : i ∉ S := fun h ↦ (hmin i h).false
    have hfilter : (insert i S).filter (· < i) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false,
        not_and, not_lt]
      rintro (rfl | hj)
      · rfl
      · exact (hmin j hj).le
    rw [stdWedge_insert S i hmin, contraction, CliffordAlgebra.contractLeft_ι_mul,
      ← contraction, ih, Finset.sum_insert hi, hfilter, Finset.card_empty, pow_zero, one_mul,
      Finset.erase_insert hi]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := (hmin j hj).ne
    have he : (insert i S).erase j = insert i (S.erase j) := Finset.erase_insert_of_ne hij
    have hf : (insert i S).filter (· < j) = insert i (S.filter (· < j)) := by
      simp [Finset.filter_insert, hmin j hj]
    rw [he, stdWedge_insert (S.erase j) i (fun k hk ↦ hmin k (Finset.mem_of_mem_erase hk)),
      hf, Finset.card_insert_of_notMem (fun hh ↦ hi (Finset.mem_filter.mp hh).1),
      pow_succ, mul_smul_comm]
    simp [mul_smul]

/-- **Scaling the coordinates scales an ordered wedge** by the product of the scalars. -/
theorem map_mulLeft_stdWedge (c : Fin r → R) (S : Finset (Fin r)) :
    ExteriorAlgebra.map (LinearMap.mulLeft R c) (stdWedge (R := R) S) =
      (∏ i ∈ S, c i) • stdWedge S := by
  classical
  induction S using Finset.induction_on_min with
  | empty => simp [stdWedge]
  | @insert i S hmin ih =>
    have hi : i ∉ S := fun h ↦ (hmin i h).false
    have h : (Pi.single i (c i) : Fin r → R) = c i • Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    rw [stdWedge_insert S i hmin, map_mul, ExteriorAlgebra.map_apply_ι, mulLeft_single, ih, h,
      map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, Finset.prod_insert hi]

/-! ### Coordinates in the ordered wedges -/

/-- The projection of the exterior algebra onto its `k`-th exterior power. -/
def extProj (k : ℕ) : ExteriorAlgebra R (Fin r → R) →ₗ[R] ⋀[R]^k (Fin r → R) :=
  (DirectSum.component R ℕ (fun i ↦ ⋀[R]^i (Fin r → R)) k).comp
    (DirectSum.decomposeLinearEquiv (fun i : ℕ ↦ ⋀[R]^i (Fin r → R))).toLinearMap

/-- The projection onto the `k`-th exterior power is the identity on it. -/
theorem extProj_of_mem {k : ℕ} {e : ExteriorAlgebra R (Fin r → R)} (he : e ∈ ⋀[R]^k (Fin r → R)) :
    extProj k e = ⟨e, he⟩ :=
  Subtype.ext (DirectSum.decompose_of_mem_same (fun i : ℕ ↦ ⋀[R]^i (Fin r → R)) he)

/-- The projection onto the `j`-th exterior power kills the `k`-th one for `k ≠ j`. -/
theorem extProj_of_mem_ne {j k : ℕ} {e : ExteriorAlgebra R (Fin r → R)}
    (he : e ∈ ⋀[R]^k (Fin r → R)) (h : k ≠ j) : extProj j e = 0 :=
  Subtype.ext (DirectSum.decompose_of_mem_ne (fun i : ℕ ↦ ⋀[R]^i (Fin r → R)) he h)

/-- **The coordinate of an element of the exterior algebra at the ordered wedge `e_S`.** -/
def extCoord (S : Finset (Fin r)) : ExteriorAlgebra R (Fin r → R) →ₗ[R] R :=
  (((Pi.basisFun R (Fin r)).exteriorPower S.card).coord ⟨S, rfl⟩).comp (extProj S.card)

/-- The coordinates of the ordered wedges are the Kronecker delta. -/
theorem extCoord_stdWedge (S T : Finset (Fin r)) :
    extCoord T (stdWedge (R := R) S) = if S = T then 1 else 0 := by
  by_cases hc : S.card = T.card
  · have hp : extProj T.card (stdWedge (R := R) S) =
        (Pi.basisFun R (Fin r)).exteriorPower T.card ⟨S, hc⟩ :=
      (extProj_of_mem (by rw [← hc]; exact stdWedge_mem S)).trans
        (Subtype.ext (exteriorPower_basis_eq_stdWedge S hc).symm)
    rw [extCoord, LinearMap.comp_apply, hp, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases hST : S = T
    · subst hST
      simp
    · rw [Finsupp.single_eq_of_ne (fun h ↦ hST (congrArg Subtype.val h).symm), ite_eq_right hST]
  · rw [extCoord, LinearMap.comp_apply, extProj_of_mem_ne (stdWedge_mem S) hc, map_zero,
      ite_eq_right (fun h ↦ hc (congrArg Finset.card h))]

/-- The coordinates of an element of the `k`-th exterior power vanish at the subsets of
cardinality different from `k`. -/
theorem extCoord_of_mem_ne {k : ℕ} {e : ExteriorAlgebra R (Fin r → R)}
    (he : e ∈ ⋀[R]^k (Fin r → R)) {S : Finset (Fin r)} (h : S.card ≠ k) : extCoord S e = 0 := by
  rw [extCoord, LinearMap.comp_apply, extProj_of_mem_ne he (Ne.symm h), map_zero]

/-- **A homogeneous element of the exterior algebra is the sum of its coordinates times the
ordered wedges.** -/
theorem sum_extCoord_smul {k : ℕ} {e : ExteriorAlgebra R (Fin r → R)}
    (he : e ∈ ⋀[R]^k (Fin r → R)) :
    ∑ S : Finset (Fin r), extCoord S e • stdWedge (R := R) S = e := by
  classical
  let b := (Pi.basisFun R (Fin r)).exteriorPower k
  calc ∑ S : Finset (Fin r), extCoord S e • stdWedge (R := R) S
      = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin r) ↦ S.card = k),
          extCoord S e • stdWedge (R := R) S :=
        (Finset.sum_filter_of_ne (fun S _ hS ↦ by
          by_contra h
          exact hS (by rw [extCoord_of_mem_ne he h, zero_smul]))).symm
    _ = ∑ s : Set.powersetCard (Fin r) k, extCoord s.1 e • stdWedge (R := R) s.1 :=
        Finset.sum_subtype _ (fun S ↦ by simp [Set.powersetCard.mem_iff]) _
    _ = ∑ s : Set.powersetCard (Fin r) k,
          (((b.repr ⟨e, he⟩ s • b s : ⋀[R]^k (Fin r → R))) : ExteriorAlgebra R (Fin r → R)) := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        obtain ⟨S, hS⟩ := s
        have hS' : S.card = k := hS
        rw [Submodule.coe_smul, exteriorPower_basis_eq_stdWedge S hS']
        congr 1
        subst hS'
        rw [extCoord, LinearMap.comp_apply, extProj_of_mem he, Module.Basis.coord_apply]
    _ = e := by rw [← Submodule.coe_sum, b.sum_repr]

/-- The ordered wedge of the empty set is the unit. -/
theorem stdWedge_empty : stdWedge (R := R) (r := r) ∅ = 1 := by
  simp [stdWedge]

/-- **Extensionality on ordered wedges**: two linear maps out of the exterior algebra of `Rʳ`
agreeing on the ordered wedges are equal. -/
theorem linearMap_ext_stdWedge {M : Type*} [AddCommGroup M] [Module R M]
    {g h : ExteriorAlgebra R (Fin r → R) →ₗ[R] M}
    (hgh : ∀ S : Finset (Fin r), g (stdWedge S) = h (stdWedge S)) : g = h := by
  refine LinearMap.ext fun e => ?_
  induction e using DirectSum.Decomposition.inductionOn (fun i : ℕ ↦ ⋀[R]^i (Fin r → R)) with
  | zero => rw [map_zero, map_zero]
  | add e e' he he' => rw [map_add, map_add, he, he']
  | @homogeneous k e =>
    rw [← sum_extCoord_smul e.2, map_sum, map_sum]
    exact Finset.sum_congr rfl fun S _ => by rw [map_smul, map_smul, hgh]

end Wedge

/-! ### Coordinates on the tensor product with the exterior algebra -/

section Coordinates

open Stacks.ChaoticSite.AbsoluteExtension KoszulCoefficientTower

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The inverse system `n ↦ K_{n+1}` of Koszul algebras, over `LiftedNat`. -/
abbrev powDiagram : LiftedNat.{u}ᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R :=
  LiftedNat.liftDiagram (powAlgebraDiagram f)

/-- The stage `n`, as an object of `LiftedNatᵒᵖ`. -/
abbrev stage (n : ℕ) : LiftedNat.{u}ᵒᵖ := op (LiftedNat.up n)

/-- The Koszul algebra `K_{n+1}` at the stage `n`. -/
abbrev stageAlg (n : ℕ) : DifferentialGradedAlgebra.{u, u} R := (powDiagram f).obj (stage n)

variable (n : ℕ)

/-- The ordered wedge `e_S`, in `K_{n+1}`. -/
def sw (S : Finset (Fin r)) : (stageAlg f n).A := stdWedge S

/-- The coordinate at `e_S`, on `K_{n+1}`. -/
def sc (S : Finset (Fin r)) : (stageAlg f n).A →ₗ[R] R := extCoord S

/-- The coordinates of the ordered wedges are the Kronecker delta. -/
theorem sc_sw (S T : Finset (Fin r)) : sc f n T (sw f n S) = if S = T then 1 else 0 :=
  extCoord_stdWedge S T

/-- The ordered wedge `e_S` has cohomological degree `-|S|` in `K_{n+1}`. -/
theorem sw_mem (S : Finset (Fin r)) : sw f n S ∈ (stageAlg f n).grading (-(S.card : ℤ)) := by
  have h := powAlgebra_grading_neg_natCast f (n + 1) S.card
  show stdWedge S ∈ (powAlgebra f (n + 1)).grading (-(S.card : ℤ))
  rw [h]
  exact stdWedge_mem S

/-- The ordered wedge of the empty set is the unit of `K_{n+1}`. -/
theorem sw_empty : sw f n (∅ : Finset (Fin r)) = 1 := stdWedge_empty

/-- An element of `K_{n+1}` of degree `-j` lies in the `j`-th exterior power. -/
theorem mem_exteriorPower_of_mem {j : ℕ} {e : (stageAlg f n).A}
    (he : e ∈ (stageAlg f n).grading (-(j : ℤ))) : e ∈ ⋀[R]^j (Fin r → R) := by
  have h := powAlgebra_grading_neg_natCast f (n + 1) j
  change e ∈ (powAlgebra f (n + 1)).grading (-(j : ℤ)) at he
  rw [h] at he
  exact he

/-- The algebra `K_{n+1}` vanishes in positive degrees. -/
theorem eq_zero_of_mem_pos {q : ℤ} (hq : 0 < q) {e : (stageAlg f n).A}
    (he : e ∈ (stageAlg f n).grading q) : e = 0 := by
  have h := powAlgebra_grading_of_pos f (n + 1) hq
  change e ∈ (powAlgebra f (n + 1)).grading q at he
  rw [h] at he
  exact (Submodule.mem_bot R).1 he

/-- The coordinates of an element of degree `-j` vanish at the subsets of cardinality
different from `j`. -/
theorem sc_of_mem_ne {j : ℕ} {e : (stageAlg f n).A} (he : e ∈ (stageAlg f n).grading (-(j : ℤ)))
    {S : Finset (Fin r)} (h : S.card ≠ j) : sc f n S e = 0 :=
  extCoord_of_mem_ne (mem_exteriorPower_of_mem f n he) h

/-- A homogeneous element of `K_{n+1}` is the sum of its coordinates times the ordered wedges. -/
theorem sum_sc_smul_sw {j : ℕ} {e : (stageAlg f n).A}
    (he : e ∈ (stageAlg f n).grading (-(j : ℤ))) :
    ∑ S : Finset (Fin r), sc f n S e • sw f n S = e :=
  sum_extCoord_smul (mem_exteriorPower_of_mem f n he)

/-- Extensionality on ordered wedges for linear maps out of `K_{n+1}`. -/
theorem linearMap_ext_sw {M : Type*} [AddCommGroup M] [Module R M]
    {g h : (stageAlg f n).A →ₗ[R] M}
    (hgh : ∀ S : Finset (Fin r), g (sw f n S) = h (sw f n S)) : g = h :=
  linearMap_ext_stdWedge (g := g) (h := h) hgh

/-- The differential of `K_{n+1}` on an ordered wedge. -/
theorem stageAlg_d_sw (S : Finset (Fin r)) :
    (stageAlg f n).d (sw f n S) =
      ∑ i ∈ S, ((-1 : R) ^ (S.filter (· < i)).card * f i ^ (n + 1)) • sw f n (S.erase i) := by
  have h := contraction_stdWedge (R := R) (seqDual fun i => f i ^ (n + 1)) S
  simp only [seqDual_single] at h
  exact h

/-- The transition `K_{n'+1} → K_{n+1}` on an ordered wedge. -/
theorem powDiagram_map_sw {n n' : ℕ} (a : stage.{u} n' ⟶ stage n) (S : Finset (Fin r)) :
    ((powDiagram.{u} f).map a).toAlgebraHom (sw f n' S) = (∏ i ∈ S, f i ^ (n' - n)) • sw f n S := by
  have h := map_mulLeft_stdWedge (R := R) (fun i => f i ^ (n' + 1 - (n + 1))) S
  rw [show n' + 1 - (n + 1) = n' - n by omega] at h
  have e : ((powDiagram.{u} f).map a).toAlgebraHom (sw f n' S) =
      ExteriorAlgebra.map (LinearMap.mulLeft R fun i => f i ^ (n' + 1 - (n + 1))) (stdWedge S) :=
    rfl
  rw [show n' + 1 - (n + 1) = n' - n by omega] at e
  exact e.trans h

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The tensor product `(⊕ₙ Kⁿ) ⊗_R K_{n+1}`. -/
abbrev KTensor := (absBase K).M ⊗[R] (stageAlg f n).A

/-- The `S`-coordinate in degree `t`: `x ⊗ e ↦ e_S(e) · x^{t + |S|}`. -/
def tensorCoordBilin (t : ℤ) (S : Finset (Fin r)) :
    (absBase K).M →ₗ[R] (stageAlg f n).A →ₗ[R] K.X (t + S.card) :=
  LinearMap.mk₂ R (fun x e => sc f n S e • compR K (t + S.card) x)
    (fun x x' e => by rw [map_add, smul_add])
    (fun c x e => by rw [map_smul, smul_comm])
    (fun x e e' => by rw [map_add, add_smul])
    (fun c x e => by rw [map_smul, smul_eq_mul, mul_smul])

/-- **The coordinates in degree `t`**: `(⊕ₙ Kⁿ) ⊗_R K_{n+1} → ∏_S K^{t + |S|}`,
`x ⊗ e ↦ (e_S(e) · x^{t + |S|})_S`. -/
def tensorCoord (t : ℤ) : KTensor f n K →ₗ[R] coefficientKoszulTerm (r := r) K t :=
  LinearMap.pi fun S => TensorProduct.lift (tensorCoordBilin f n K t S)

/-- The coordinates on a pure tensor. -/
theorem tensorCoord_tmul (t : ℤ) (x : (absBase K).M) (e : (stageAlg f n).A)
    (S : Finset (Fin r)) :
    tensorCoord f n K t (x ⊗ₜ[R] e) S = sc f n S e • compR K (t + S.card) x := rfl

/-- **The synthesis in degree `t`**: `(y_S)_S ↦ ∑_S y_S ⊗ e_S`. -/
def tensorSynth (t : ℤ) : coefficientKoszulTerm (r := r) K t →ₗ[R] KTensor f n K :=
  ∑ S : Finset (Fin r), ((TensorProduct.mk R (absBase K).M (stageAlg f n).A).flip
    (sw f n S)).comp ((lofR K (t + S.card)).comp (LinearMap.proj S))

/-- The synthesis is `(y_S)_S ↦ ∑_S y_S ⊗ e_S`. -/
theorem tensorSynth_apply (t : ℤ) (y : coefficientKoszulTerm (r := r) K t) :
    tensorSynth f n K t y = ∑ S : Finset (Fin r), lofR K (t + S.card) (y S) ⊗ₜ[R] sw f n S := by
  rw [tensorSynth, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, LinearMap.proj_apply]

/-- **The coordinates invert the synthesis.** -/
theorem tensorCoord_synth (t : ℤ) (y : coefficientKoszulTerm (r := r) K t) :
    tensorCoord f n K t (tensorSynth f n K t y) = y := by
  classical
  funext S
  rw [tensorSynth_apply, map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single S (fun T _ hT => by
      rw [tensorCoord_tmul, sc_sw, ite_eq_right hT, zero_smul])
      (fun h => absurd (Finset.mem_univ S) h),
    tensorCoord_tmul, sc_sw, ite_eq_left rfl, one_smul]
  exact compR_lofR_self K _ _

/-- The synthesis of the coordinates of `k ⊗ e_T`, for `k ∈ Kᵖ`: the pure tensor itself if it
has degree `t`, and zero otherwise. -/
theorem tensorSynth_coord_lofR_sw (t p : ℤ) (k : K.X p) (T : Finset (Fin r)) :
    tensorSynth f n K t (tensorCoord f n K t (lofR K p k ⊗ₜ[R] sw f n T)) =
      if p = t + T.card then lofR K p k ⊗ₜ[R] sw f n T else 0 := by
  classical
  rw [tensorSynth_apply, Finset.sum_eq_single T (fun S _ hS => by
      rw [tensorCoord_tmul, sc_sw, ite_eq_right (Ne.symm hS), zero_smul, map_zero,
        TensorProduct.zero_tmul])
      (fun h => absurd (Finset.mem_univ T) h),
    tensorCoord_tmul, sc_sw, ite_eq_left rfl, one_smul, lofR_compR_lofR]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

/-- **The synthesis inverts the coordinates on the elements of degree `t`.** -/
theorem tensorSynth_coord_of_mem (t : ℤ) {w : KTensor f n K}
    (hw : w ∈ _root_.DifferentialGradedModule.absTensorGrading (absBase K) (stageAlg f n) t) :
    tensorSynth f n K t (tensorCoord f n K t w) = w := by
  classical
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, q, a, b, ⟨k, hk⟩, hb, hpq, rfl⟩ := hw
    rw [show a = lofR K p k from hk.symm]
    by_cases hq : q ≤ 0
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, q = -(j : ℤ) := ⟨(-q).toNat, by omega⟩
      have hexp : (lofR K p k ⊗ₜ[R] b : KTensor f n K) =
          ∑ S : Finset (Fin r), sc f n S b • (lofR K p k ⊗ₜ[R] sw f n S) := by
        conv_lhs => rw [← sum_sc_smul_sw f n hb]
        rw [TensorProduct.tmul_sum]
        exact Finset.sum_congr rfl fun S _ => TensorProduct.tmul_smul _ _ _
      rw [hexp, map_sum, map_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [map_smul, map_smul, tensorSynth_coord_lofR_sw]
      split_ifs with h
      · rfl
      · rw [sc_of_mem_ne f n hb (fun h' => h (by omega)), zero_smul, zero_smul]
    · rw [eq_zero_of_mem_pos f n (by omega) hb, TensorProduct.tmul_zero, map_zero, map_zero]
  | zero => rw [map_zero, map_zero]
  | add w w' _ _ hw hw' => rw [map_add, map_add, hw, hw']
  | smul c w _ hw => rw [map_smul, map_smul, hw]

/-- The synthesis has degree `t`. -/
theorem tensorSynth_mem (t : ℤ) (y : coefficientKoszulTerm (r := r) K t) :
    tensorSynth f n K t y ∈
      _root_.DifferentialGradedModule.absTensorGrading (absBase K) (stageAlg f n) t := by
  rw [tensorSynth_apply]
  refine Submodule.sum_mem _ fun S _ => ?_
  have h := _root_.DifferentialGradedModule.absTmul_mem (absBase K) (stageAlg f n) (t + S.card)
    (-(S.card : ℤ)) _ _ (lofR_mem K _ (y S)) (sw_mem f n S)
  rwa [show t + (S.card : ℤ) + -(S.card : ℤ) = t by ring] at h

/-- The coordinates of the pure tensor `k ⊗ e_T` are supported at `T`. -/
theorem tensorCoord_lofR_sw (t p : ℤ) (k : K.X p) (T S : Finset (Fin r)) :
    tensorCoord f n K t (lofR K p k ⊗ₜ[R] sw f n T) S =
      if T = S then compR K (t + S.card) (lofR K p k) else 0 := by
  rw [tensorCoord_tmul, sc_sw]
  split_ifs
  · exact one_smul _ _
  · exact zero_smul _ _

/-- Transport along an equality of degrees commutes with the projections, for any proof of the
equality of the terms. -/
theorem eqToHom_compR' {i j : ℤ} (h : K.X i = K.X j) (hij : i = j) (x : (absBase K).M) :
    (eqToHom h).hom (compR K i x) = compR K j x := by
  subst hij
  rfl

/-- The component formula for the differential of the coefficient Koszul tower. -/
theorem coefficientKoszulDifferential_apply (t : ℤ) (y : coefficientKoszulTerm (r := r) K t)
    (S : Finset (Fin r)) :
    (coefficientKoszulDifferential f n K t).hom y S =
      (K.d (t + S.card) ((t + 1) + S.card)).hom (y S) +
        ∑ i : {i : Fin r // i ∉ S},
          ((-1 : R) ^ (t + S.card + 1).natAbs *
              (-1 : R) ^ (S.filter (· < i.1)).card * f i.1 ^ (n + 1)) •
            ((eqToHom (by
              rw [Finset.card_insert_of_notMem i.2]
              norm_num [Nat.cast_add, Nat.cast_one]
              abel_nf) :
                K.X (t + (insert i.1 S).card) ⟶ K.X ((t + 1) + S.card))).hom
                  (y (insert i.1 S)) := rfl

/-- **The coordinates intertwine the differentials**, on the pure tensor of an element of `Kᵖ`
with an ordered wedge. -/
theorem tensorCoord_d_lofR_sw (t p : ℤ) (k : K.X p) (T : Finset (Fin r)) :
    tensorCoord f n K (t + 1) (_root_.DifferentialGradedModule.absTensorDifferential (absBase K)
        (stageAlg f n) (lofR K p k ⊗ₜ[R] sw f n T)) =
      (coefficientKoszulDifferential f n K t).hom
        (tensorCoord f n K t (lofR K p k ⊗ₜ[R] sw f n T)) := by
  classical
  have hd : _root_.DifferentialGradedModule.absTensorDifferential (absBase K) (stageAlg f n)
      (lofR K p k ⊗ₜ[R] sw f n T) = (absBase K).d (lofR K p k) ⊗ₜ[R] sw f n T +
        (p.negOnePow : ℤ) • (lofR K p k ⊗ₜ[R] (stageAlg f n).d (sw f n T)) :=
    _root_.DifferentialGradedModule.absTensorDifferential_tmul (absBase K) (stageAlg f n) p
      ⟨lofR K p k, lofR_mem K p k⟩ (sw f n T)
  rw [hd, stageAlg_d_sw, TensorProduct.tmul_sum, map_add, map_zsmul, map_sum]
  funext S
  rw [coefficientKoszulDifferential_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
    tensorCoord_tmul, tensorCoord_lofR_sw, sc_sw]
  simp only [TensorProduct.tmul_smul, map_smul, Pi.smul_apply]
  by_cases hST : T = S
  · subst hST
    rw [ite_eq_left rfl, one_smul, ite_eq_left rfl,
      compR_d K (show t + (T.card : ℤ) + 1 = t + 1 + T.card by ring),
      Finset.sum_eq_zero (fun i hi => by
        rw [tensorCoord_lofR_sw, ite_eq_right (Finset.erase_ne_self.2 hi), smul_zero]),
      smul_zero, add_zero, Finset.sum_eq_zero (fun i _ => by
        rw [tensorCoord_lofR_sw, ite_eq_right (fun h => i.2 (Finset.insert_eq_self.1 h.symm)),
          map_zero, smul_zero]),
      add_zero]
  · rw [ite_eq_right hST, zero_smul, zero_add, ite_eq_right hST, map_zero, zero_add]
    by_cases hex : ∃ i ∈ T, T.erase i = S
    · obtain ⟨i, hiT, rfl⟩ := hex
      have hiS : i ∉ T.erase i := Finset.notMem_erase i T
      rw [Finset.sum_eq_single_of_mem i hiT (fun j hjT hji => by
          rw [tensorCoord_lofR_sw, ite_eq_right (fun h => hji ((Finset.erase_inj T hjT).1 h)),
            smul_zero]),
        tensorCoord_lofR_sw, ite_eq_left rfl, Fintype.sum_eq_single ⟨i, hiS⟩ (fun j hj => by
          rw [tensorCoord_lofR_sw, ite_eq_right (fun h => hj (Subtype.ext (by
            have hjT : j.1 ∈ T := (Finset.ext_iff.1 h j.1).2 (Finset.mem_insert_self _ _)
            by_contra hji
            exact j.2 (Finset.mem_erase.2 ⟨hji, hjT⟩)))), map_zero, smul_zero]),
        tensorCoord_lofR_sw, ite_eq_left (Finset.insert_erase hiT).symm, eqToHom_compR' K _ (by
          rw [Finset.insert_erase hiT, Finset.card_erase_of_mem hiT]
          have : 0 < T.card := Finset.card_pos.2 ⟨i, hiT⟩
          push_cast [Nat.cast_sub this]
          ring)]
      have hfilter : ((T.erase i).filter (· < i)).card = (T.filter (· < i)).card := by
        rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp)]
      rw [hfilter]
      dsimp only
      by_cases hp : p = t + 1 + (T.erase i).card
      · rw [negOnePow_smul_eq (R := R), smul_smul,
          show p.natAbs = (t + ((T.erase i).card : ℤ) + 1).natAbs by rw [hp]; ring_nf]
        congr 1
        ring
      · rw [compR_lofR_of_ne K hp, smul_zero, smul_zero, smul_zero]
    · push Not at hex
      rw [Finset.sum_eq_zero (fun i hi => by
          rw [tensorCoord_lofR_sw, ite_eq_right (hex i hi), smul_zero]), smul_zero,
        Finset.sum_eq_zero (fun j _ => by
          rw [tensorCoord_lofR_sw, ite_eq_right (fun (h : T = insert j.1 S) => hex j.1
            ((Finset.ext_iff.1 h j.1).2 (Finset.mem_insert_self _ _))
            (by rw [h, Finset.erase_insert j.2])), map_zero, smul_zero])]


/-- Linear maps out of `(⊕ₙ Kⁿ) ⊗_R K_{n+1}` agreeing on the pure tensors `k ⊗ e_T` are equal. -/
private theorem linearMap_ext_lofR_sw {M : Type*} [AddCommGroup M] [Module R M]
    {g h : KTensor f n K →ₗ[R] M}
    (hgh : ∀ (p : ℤ) (k : K.X p) (T : Finset (Fin r)),
      g (lofR K p k ⊗ₜ[R] sw f n T) = h (lofR K p k ⊗ₜ[R] sw f n T)) : g = h :=
  TensorProduct.ext (DirectSum.linearMap_ext R fun p => LinearMap.ext fun k =>
    linearMap_ext_sw f n fun T => hgh p k T)

/-- **The coordinates intertwine the differentials**: the total differential of
`(⊕ₙ Kⁿ) ⊗_R K_{n+1}` becomes the differential `coefficientKoszulDifferential` of 091Z. -/
theorem tensorCoord_d (t : ℤ) (w : KTensor f n K) :
    tensorCoord f n K (t + 1) (_root_.DifferentialGradedModule.absTensorDifferential (absBase K)
        (stageAlg f n) w) =
      (coefficientKoszulDifferential f n K t).hom (tensorCoord f n K t w) :=
  LinearMap.congr_fun (linearMap_ext_lofR_sw f n K (g := (tensorCoord f n K (t + 1)).comp
      (_root_.DifferentialGradedModule.absTensorDifferential (absBase K) (stageAlg f n)))
      (h := (coefficientKoszulDifferential f n K t).hom.comp (tensorCoord f n K t))
      fun p k T => tensorCoord_d_lofR_sw f n K t p k T) w

/-- The component formula for the transitions of the coefficient Koszul tower. -/
theorem coefficientKoszulTransitionTerm_apply (m n' : ℕ) (t : ℤ)
    (y : coefficientKoszulTerm (r := r) K t) (S : Finset (Fin r)) :
    (coefficientKoszulTransitionTerm f m n' K t).hom y S = (∏ i ∈ S, f i ^ (m - n')) • y S :=
  rfl

/-- **The coordinates intertwine the transitions** `K_{n'+1} → K_{n+1}` with the transitions of
the coefficient Koszul tower. -/
theorem tensorCoord_absRestr {n n' : ℕ} (a : stage.{u} n' ⟶ stage n) (t : ℤ)
    (w : KTensor f n' K) :
    tensorCoord f n K t (absRestr (powDiagram f) K a w) =
      (coefficientKoszulTransitionTerm f n' n K t).hom (tensorCoord f n' K t w) := by
  refine LinearMap.congr_fun (linearMap_ext_lofR_sw f n' K
    (g := (tensorCoord f n K t).comp (absRestr (powDiagram f) K a))
    (h := (coefficientKoszulTransitionTerm f n' n K t).hom.comp (tensorCoord f n' K t))
    fun p k T => ?_) w
  funext S
  show tensorCoord f n K t (absRestr (powDiagram f) K a (absTmul (powDiagram f) K _ (lofR K p k)
    (sw f n' T))) S = (coefficientKoszulTransitionTerm f n' n K t).hom
      (tensorCoord f n' K t (lofR K p k ⊗ₜ[R] sw f n' T)) S
  rw [absRestr_tmul, coefficientKoszulTransitionTerm_apply, tensorCoord_tmul,
    tensorCoord_tmul, sc_sw, powDiagram_map_sw, map_smul, sc_sw, smul_eq_mul, mul_smul]
  split_ifs with h
  · subst h
    rfl
  · rw [zero_smul, smul_zero, smul_zero]

/-- **The coordinates are natural in the complex.** -/
theorem tensorCoord_absMap {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L) (t : ℤ)
    (w : KTensor f n K) :
    tensorCoord f n L t (absMap (powDiagram f) g (stage n) w) =
      (coefficientMapTerm g t).hom (tensorCoord f n K t w) := by
  have key : (tensorCoord f n L t).comp (absMap (powDiagram f) g (stage n)) =
      (coefficientMapTerm g t).hom.comp (tensorCoord f n K t) := by
    refine TensorProduct.ext' fun x e => ?_
    funext S
    show tensorCoord f n L t (absMap (powDiagram f) g (stage n)
        (absTmul (powDiagram f) K _ x e)) S = (g.f (t + S.card)).hom (tensorCoord f n K t
          (x ⊗ₜ[R] e) S)
    rw [absMap_tmul]
    show sc f n S e • compR L (t + S.card) (DirectSum.lmap (fun n => (g.f n).hom) x) =
      (g.f (t + S.card)).hom (sc f n S e • compR K (t + S.card) x)
    rw [map_smul]
    rfl
  exact LinearMap.congr_fun key w

/-- **The coordinates of the unit `x ↦ x ⊗ 1`** are the empty-subset inclusion. -/
theorem tensorCoord_lofR_one (t : ℤ) (k : K.X t) :
    tensorCoord f n K t (lofR K t k ⊗ₜ[R] 1) = (coefficientKoszulUnitTerm (r := r) K t).hom k := by
  funext S
  rw [← sw_empty f n, tensorCoord_lofR_sw]
  show _ = (if h : S = ∅ then (eqToHom (by subst S; simp) : K.X t ⟶ K.X (t + S.card)).hom
    else 0) k
  by_cases hS : S = ∅
  · subst hS
    rw [ite_eq_left rfl, dite_eq_left rfl, compR_lofR_eq K (by simp)]
  · rw [ite_eq_right (Ne.symm hS), dite_eq_right hS]
    rfl


end Coordinates


/-! ### The sections of the extension of scalars -/

section Sections

open Stacks.ChaoticSite Stacks.ChaoticSite.AbsoluteExtension KoszulCoefficientTower
  _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] _root_.SheafOfModules.GradedAlgebra.sectionsGOne
  _root_.SheafOfModules.GradedAlgebra.sectionsGMul _root_.SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- **The sheaf `ℬ` of Proposition 0GZK**, `n ↦ K_{n+1}`, read over the underlying sheaf of rings
of the constant sheaf of commutative rings. -/
abbrev liftedPowAlg : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.PresheafOfModules.constCommRingSheaf (C := LiftedNat.{u}) R)) :=
  liftedPowSheafAlgebra f

variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) (t : ℤ)

/-- The degree-`t` sections over the stage `n` of the extension of scalars `K ⊗_R ℬ`. -/
abbrev extSec : ModuleCat.{u} R :=
  ((sectionsFunctor R).obj (((extendFunctor (liftedPowAlg f)).obj K).complex.X t)).obj (stage n)

/-- A section of degree `t`, as a homogeneous element of `K ⊗_R ℬ(n)`. -/
def extSecElt (x : extSec f K n t) :
    (extensionSections (sysAlg (powDiagram f)) K (stage n)).M :=
  ((extensionSystem (sysAlg (powDiagram f)) K).cElt (n := t) (U := stage n) x).1

/-- A section of degree `t` is homogeneous of degree `t`. -/
theorem extSecElt_mem (x : extSec f K n t) :
    extSecElt f K n t x ∈ (extensionSections (sysAlg (powDiagram f)) K (stage n)).grading t :=
  ((extensionSystem (sysAlg (powDiagram f)) K).cElt (n := t) (U := stage n) x).2

/-- A homogeneous element of `K ⊗_R ℬ(n)`, as a section of degree `t`. -/
def eltExtSec (z : (extensionSections (sysAlg (powDiagram f)) K (stage n)).M)
    (hz : z ∈ (extensionSections (sysAlg (powDiagram f)) K (stage n)).grading t) :
    extSec f K n t :=
  (extensionSystem (sysAlg (powDiagram f)) K).eltPiece (n := t) (U := stage n) ⟨z, hz⟩

/-- Reading a homogeneous element as a section and back is the identity. -/
@[simp] theorem extSecElt_eltExtSec (z : (extensionSections (sysAlg (powDiagram f)) K (stage n)).M)
    (hz : z ∈ (extensionSections (sysAlg (powDiagram f)) K (stage n)).grading t) :
    extSecElt f K n t (eltExtSec f K n t z hz) = z := rfl

/-- Sections of degree `t` are determined by the homogeneous elements they are. -/
theorem extSec_ext {x y : extSec f K n t} (h : extSecElt f K n t x = extSecElt f K n t y) :
    x = y :=
  (extensionSystem (sysAlg (powDiagram f)) K).cElt_injective h

/-- Reading a section as a homogeneous element is additive. -/
theorem extSecElt_add (x y : extSec f K n t) :
    extSecElt f K n t (x + y) = extSecElt f K n t x + extSecElt f K n t y := rfl

/-- The scalar `c · 1` of `ℬ(n)` acting on the sections of `K ⊗_R ℬ`, read in the opposite of the
section algebra over the stage `n`. -/
abbrev extSecScalar (c : R) : ((sysAlg (powDiagram f)).sectionAlgebra (stage n)).Aᵐᵒᵖ :=
  (sysAlg (powDiagram f)).sectionScalarOp (stage n) c

/-- The `R`-module structure of the sections is the action of the scalars `r · 1`. -/
theorem extSecElt_smul (c : R) (x : extSec f K n t) :
    extSecElt f K n t (c • x) = extSecScalar f n c • extSecElt f K n t x := rfl

/-- The coordinates of a section of degree `t`. -/
def extSecCoord : extSec f K n t →ₗ[R] coefficientKoszulTerm (r := r) K t where
  toFun x := tensorCoord f n K t (absEquiv (powDiagram f) K (stage n) (extSecElt f K n t x))
  map_add' x y := by rw [extSecElt_add, map_add, map_add]
  map_smul' c x := by
    rw [extSecElt_smul,
      show absEquiv (powDiagram f) K (stage n) (extSecScalar f n c • extSecElt f K n t x) =
          c • absEquiv (powDiagram f) K (stage n) (extSecElt f K n t x) from
        absEquiv_smul (powDiagram f) K (stage n) c (extSecElt f K n t x), map_smul]
    rfl

/-- The coordinates of a section are those of its image in `(⊕ₙ Kⁿ) ⊗_R K_{n+1}`. -/
theorem extSecCoord_apply (x : extSec f K n t) :
    extSecCoord f K n t x =
      tensorCoord f n K t (absEquiv (powDiagram f) K (stage n) (extSecElt f K n t x)) := rfl

/-- The section of degree `t` with prescribed coordinates. -/
def extSecSynth (y : coefficientKoszulTerm (r := r) K t) : extSec f K n t :=
  eltExtSec f K n t ((absEquiv (powDiagram f) K (stage n)).symm (tensorSynth f n K t y)) (by
    rw [tensorSynth_apply, map_sum]
    exact Submodule.sum_mem _ fun S _ => absEquiv_symm_tmul_mem (powDiagram f) K (stage n)
      (show t + (S.card : ℤ) + -(S.card : ℤ) = t by ring) (lofR_mem K _ _) (sw_mem f n S))

/-- The coordinates invert the synthesis of sections. -/
theorem extSecCoord_synth (y : coefficientKoszulTerm (r := r) K t) :
    extSecCoord f K n t (extSecSynth f K n t y) = y := by
  rw [extSecCoord_apply, extSecSynth, extSecElt_eltExtSec, AddEquiv.apply_symm_apply,
    tensorCoord_synth]

/-- The synthesis of sections inverts the coordinates. -/
theorem extSecSynth_coord (x : extSec f K n t) :
    extSecSynth f K n t (extSecCoord f K n t x) = x := by
  refine extSec_ext f K n t ?_
  rw [extSecSynth, extSecElt_eltExtSec, extSecCoord_apply,
    tensorSynth_coord_of_mem f n K t (absEquiv_mem (powDiagram f) K (stage n)
      (extSecElt_mem f K n t x)), AddEquiv.symm_apply_apply]

/-- **The degree-`t` sections of `K ⊗_R ℬ` over the stage `n` are `∏_S K^{t + |S|}`.** -/
def extSecIso : extSec f K n t ≅ coefficientKoszulTerm (r := r) K t :=
  LinearEquiv.toModuleIso
    { extSecCoord f K n t with
      invFun := extSecSynth f K n t
      left_inv := extSecSynth_coord f K n t
      right_inv := extSecCoord_synth f K n t }

/-- The isomorphism of sections is given by the coordinates. -/
theorem extSecIso_hom_apply (x : extSec f K n t) :
    (extSecIso f K n t).hom x = extSecCoord f K n t x := rfl

end Sections


/-! ### The tower of sections -/

section Tower

open Stacks.ChaoticSite Stacks.ChaoticSite.AbsoluteExtension KoszulCoefficientTower
  _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] _root_.SheafOfModules.GradedAlgebra.sectionsGOne
  _root_.SheafOfModules.GradedAlgebra.sectionsGMul _root_.SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- **The tower `n ↦ (K ⊗_R ℬ)(n)` of complexes of sections of the extension of scalars** of a
complex `K` of `R`-modules to the sheaf `ℬ = (K_{n+1})_n` of Proposition 0GZK. -/
abbrev extendSectionsTower (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  sectionsTower R ((extendFunctor (liftedPowAlg f)).obj K).complex

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The element of `K ⊗_R ℬ` underlying the differential of a section of the tower is the
differential of the element underlying the section. -/
theorem extSecElt_d (n : ℕ) (t : ℤ) (x : extSec f K n t) :
    extSecElt f K n (t + 1) ((((extendSectionsTower f K).obj (op n)).d t (t + 1)).hom x) =
      (extensionSections (sysAlg (powDiagram f)) K (stage n)).d (extSecElt f K n t x) :=
  (extensionSystem (sysAlg (powDiagram f)) K).coe_cElt_d (k := t) (U := stage n) x

/-- The coordinates intertwine the differentials of the sections with those of the coefficient
Koszul tower. -/
theorem extSecCoord_d (n : ℕ) (t : ℤ) (x : extSec f K n t) :
    extSecCoord f K n (t + 1) ((((extendSectionsTower f K).obj (op n)).d t (t + 1)).hom x) =
      (coefficientKoszulDifferential f n K t).hom (extSecCoord f K n t x) :=
  (extSecCoord_apply f K n (t + 1) _).trans (by rw [extSecElt_d, absEquiv_d, tensorCoord_d]; rfl)

/-- **The stage `n` of the tower of sections is the stage `n` of the coefficient Koszul tower.** -/
def extendSectionsStageIso (n : ℕ) :
    (extendSectionsTower f K).obj (op n) ≅ ((coefficientKoszulTower f).obj K).obj (op n) :=
  HomologicalComplex.Hom.isoOfComponents (fun t => extSecIso f K n t) (by
    rintro t _ rfl
    rw [coefficientKoszulTower_d]
    ext x
    exact (extSecCoord_d f K n t x).symm)

/-- The isomorphism at a stage is, in degree `t`, the isomorphism of sections. -/
theorem extendSectionsStageIso_hom_f (n : ℕ) (t : ℤ) :
    ((extendSectionsStageIso f K n).hom.f t) = (extSecIso f K n t).hom := rfl

/-- The morphism `stage n' ⟶ stage n` of `LiftedNatᵒᵖ` given by a morphism of `ℕᵒᵖ`. -/
abbrev stageHom {n n' : ℕ} (g : (op n' : ℕᵒᵖ) ⟶ op n) : stage.{u} n' ⟶ stage n :=
  LiftedNat.ofNat.op.map g

/-- The transition maps of the tower of sections are the restriction maps of `K ⊗_R ℬ`. -/
theorem extSecElt_map {n n' : ℕ} (g : (op n' : ℕᵒᵖ) ⟶ op n) (t : ℤ) (x : extSec f K n' t) :
    extSecElt f K n t ((((extendSectionsTower f K).map g).f t).hom x) =
      secRestr (powDiagram f) K (stageHom g) (extSecElt f K n' t x) := by
  have h1 : (((extendSectionsTower f K).map g).f t).hom x =
      (((extendFunctor (liftedPowAlg f)).obj K).complex.X t).val.map
        (LiftedNat.ofNat.op.map g) x := rfl
  rw [h1]
  exact congrArg Subtype.val ((extensionSystem (sysAlg (powDiagram f)) K).pieceSheaf_map_apply t
    (LiftedNat.ofNat.op.map g) ((extensionSystem (sysAlg (powDiagram f)) K).cElt x))

/-- The transitions of the coefficient Koszul tower, along any morphism of `ℕᵒᵖ`. -/
theorem coefficientKoszulTower_map_f' {n n' : ℕ} (g : (op n' : ℕᵒᵖ) ⟶ op n) (t : ℤ) :
    (((coefficientKoszulTower f).obj K).map g).f t =
      coefficientKoszulTransitionTerm f n' n K t := rfl

/-- **The isomorphism of towers of complexes**: the tower of sections of the extension of scalars
`K ⊗_R ℬ` is the strict coefficient Koszul tower of 091Z. -/
def extendSectionsTowerIso : extendSectionsTower f K ≅ (coefficientKoszulTower f).obj K :=
  NatIso.ofComponents (fun n => extendSectionsStageIso f K n.unop) (by
    rintro ⟨n'⟩ ⟨n⟩ g
    ext t x
    change extSecCoord f K n t ((((extendSectionsTower f K).map g).f t).hom x) =
      (coefficientKoszulTransitionTerm f n' n K t).hom (extSecCoord f K n' t x)
    exact (extSecCoord_apply f K n t _).trans ((congrArg
      (fun z => tensorCoord f n K t (absEquiv (powDiagram f) K (stage n) z))
      (extSecElt_map f K g t x)).trans (by rw [absEquiv_restr, tensorCoord_absRestr]; rfl)))

/-- The isomorphism of towers is, at the stage `n` and in degree `t`, the isomorphism of
sections. -/
theorem extendSectionsTowerIso_hom_app_f (n : ℕ) (t : ℤ) :
    ((extendSectionsTowerIso f K).hom.app (op n)).f t = (extSecIso f K n t).hom := rfl

variable {K} in
/-- The map of towers of sections induced by a cochain map `g : K ⟶ L`, through
`g ⊗ 1 : K ⊗_R ℬ ⟶ L ⊗_R ℬ`. -/
def extendSectionsTowerMap {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L) :
    extendSectionsTower f K ⟶ extendSectionsTower f L :=
  Functor.whiskerLeft LiftedNat.ofNat.op
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((sectionsFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((extendFunctor (liftedPowAlg f)).map g).toHomologicalComplex))

variable {K} in
/-- The induced map of towers, at the stage `n` and in degree `t`. -/
theorem extendSectionsTowerMap_app_f {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L)
    (n : ℕ) (t : ℤ) :
    ((extendSectionsTowerMap f g).app (op n)).f t =
      ((sectionsFunctor R).map (((extendFunctor (liftedPowAlg f)).map g).toHomologicalComplex.f
        t)).app (stage n) := rfl

variable {K} in
/-- The induced map of towers acts on sections as `g ⊗ 1`. -/
theorem extSecElt_extendMap {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L) (n : ℕ) (t : ℤ)
    (x : extSec f K n t) :
    extSecElt f L n t ((((extendSectionsTowerMap f g).app (op n)).f t).hom x) =
      (extensionSectionsMap (sysAlg (powDiagram f)) g (stage n)).toFun (extSecElt f K n t x) := by
  have h1 : (((extendSectionsTowerMap f g).app (op n)).f t).hom x =
      (((extendFunctor (liftedPowAlg f)).map g).toHomologicalComplex.f t).val.app (stage n) x :=
    rfl
  rw [h1]
  exact SectionSystem.coe_realizeMap_f (extensionSystemMap (sysAlg (powDiagram f)) g) t
    (stage n) x

variable {K} in
/-- **The isomorphism of towers is natural in the complex.** -/
theorem extendSectionsTowerIso_naturality {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L)
    (n : ℕ) :
    (extendSectionsTowerMap f g).app (op n) ≫ (extendSectionsTowerIso f L).hom.app (op n) =
      (extendSectionsTowerIso f K).hom.app (op n) ≫
        ((coefficientKoszulTower f).map g).app (op n) := by
  ext t x
  show extSecCoord f L n t ((((extendSectionsTowerMap f g).app (op n)).f t).hom x) =
    (coefficientMapTerm g t).hom (extSecCoord f K n t x)
  exact (extSecCoord_apply f L n t _).trans ((congrArg
    (fun z => tensorCoord f n L t (absEquiv (powDiagram f) L (stage n) z))
    (extSecElt_extendMap f g n t x)).trans (by rw [absEquiv_map, tensorCoord_absMap]; rfl))

/-- **The isomorphism of towers is compatible with the augmentations**: the unit `k ↦ k ⊗ 1`
of the extension of scalars becomes the inclusion of the empty-subset component. -/
theorem extendUnit_extendSectionsTowerIso (n : ℕ) (p : ℤ) :
    extendUnitApp (liftedPowAlg f) K p (stage n) ≫
        ((extendSectionsTowerIso f K).hom.app (op n)).f p =
      ((coefficientKoszulAugmentation f n).app K).f p := by
  rw [coefficientKoszulAugmentation_f]
  ext k
  show extSecCoord f K n p (extendUnitElt (liftedPowAlg f) K p (stage n) k) =
    (coefficientKoszulUnitTerm (r := r) K p).hom k
  have h1 : extSecElt f K n p (extendUnitElt (liftedPowAlg f) K p (stage n) k) =
      unitElt (sysAlg (powDiagram f)) K (stage n) (baseElt K p k) := rfl
  refine (extSecCoord_apply f K n p (extendUnitElt (liftedPowAlg f) K p (stage n) k)).trans ?_
  rw [h1, absEquiv_unitElt, toAbsBase_baseElt]
  exact tensorCoord_lofR_one f n K p k


variable {K} in
/-- **Extension of scalars to `ℬ` carries quasi-isomorphisms to sectionwise
quasi-isomorphisms**: for a quasi-isomorphism `g : K ⟶ L` of complexes of `R`-modules, the map
`(K ⊗_R ℬ)(n) ⟶ (L ⊗_R ℬ)(n)` of complexes of sections over every stage `n` is a
quasi-isomorphism, being identified with the map of coefficient Koszul complexes induced by `g`. -/
theorem quasiIso_extendSectionsTowerMap {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L)
    [QuasiIso g] (n : ℕ) : QuasiIso ((extendSectionsTowerMap f g).app (op n)) := by
  have h : (extendSectionsTowerMap f g).app (op n) =
      (extendSectionsTowerIso f K).hom.app (op n) ≫ ((coefficientKoszulTower f).map g).app (op n) ≫
        (extendSectionsTowerIso f L).inv.app (op n) := by
    rw [← Category.assoc, ← extendSectionsTowerIso_naturality, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [h]
  infer_instance


/-- **The towers of sections of the extensions of scalars**, as a functor of the complex. -/
def extendSectionsTowerFunctor :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) where
  obj K := extendSectionsTower f K
  map g := extendSectionsTowerMap f g
  map_id K := by
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro t
    rw [extendSectionsTowerMap_app_f, CategoryTheory.Functor.map_id]
    rfl
  map_comp g g' := by
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro t
    rw [extendSectionsTowerMap_app_f, CategoryTheory.Functor.map_comp]
    rfl

/-- **The towers of sections of the extensions of scalars are the coefficient Koszul towers**,
naturally in the complex. -/
def extendSectionsTowerNatIso : extendSectionsTowerFunctor f ≅ coefficientKoszulTower f :=
  NatIso.ofComponents (fun K => extendSectionsTowerIso f K) (fun g => by
    apply NatTrans.ext
    funext n
    exact extendSectionsTowerIso_naturality f g n.unop)


end Tower


end Koszul
