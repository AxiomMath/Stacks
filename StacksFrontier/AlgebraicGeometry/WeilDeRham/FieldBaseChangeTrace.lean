module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethBigraded
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeKunneth

/-!
# The normalisation of (A6) descends along a field extension (Lemma 0FVT)

The paragraph (A6) of the proof of Lemma 0FVT of the Stacks Project: for `X` nonempty
equidimensional of dimension `d`, write `γ = γ([Δ])` and `γ' = γ([Δ'])` for the classes of the
diagonals of `X` and `X_{k'}`. If `γ` maps to `γ'` under the comparison isomorphisms, then the
existence of `λ'` with `(1 ⊗ λ')γ' = 1` implies the existence of `λ` with `(1 ⊗ λ)γ = 1`, by the
linear algebra principle `Stacks.WeilDeRham.exists_contract_eq_of_baseChange` and the
compatibility of the Künneth decompositions
(`Stacks.WeilDeRham.FieldBaseChangeData.kunnethMap_fieldBaseChange`).

The base change `(X × X)_{k'}` of `X × X` is a fibre product of `X_{k'}` with itself, but not the
product `X_{k'} × X_{k'}` of `Stacks.WeilCohomology.SmoothProjectiveScheme.prod`; so this file
uses the contraction `(1 ⊗ λ)` of `Stacks.WeilCohomology.FirstChernClassData.traceContract` for
an arbitrary fibre product `P` of `X` with itself, through the Künneth isomorphism of `P`
(`Stacks.WeilDeRham.traceContractOfIsPullback`), and compares the two along `P ≅ X × X`
(`Stacks.WeilDeRham.traceContractOfIsPullback_pullTw`). It proves the implication for an
arbitrary class `γ`, its compatibility being a hypothesis; the classes of the diagonals for the
cycle class maps of Lemma 0FIF satisfy it.

## Main results

* `Stacks.WeilDeRham.diagonalContract_eq_of_coordinate`: `(id ⊗ λ)(v)` in any
  coordinate.
* `Stacks.WeilDeRham.traceContractOfIsPullback_pullTw`: `(id ⊗ λ)` is invariant under a
  morphism of fibre products.
* `Stacks.WeilDeRham.contractRight_comp_gradedProj`: contracting against a form restricted to
  degree `m` takes the degree `N - m` part.
* `Stacks.WeilDeRham.exists_isDiagonalNormalized_of_fieldBaseChange`: the descent.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct DirectSum
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.WeilCohomology.DiagonalExpansion (contractRight contractRight_tmul)

universe u w w'

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k] {F : Type w} [Field F]

section Coordinate

variable {𝔇 : FirstChernClassData k F} (hA5 : 𝔇.KunnethAxiom)
  {X P : (SmoothProjectiveScheme k).FullSubcategory} (p q : P ⟶ X)
  (hP : IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom X.obj.hom)
  (c : 𝔇.tate ≃ₗ[F] F) (d : ℕ)

/-- `λ : H^{2d}(X)(d) → F` read through the coordinate `c` of `F(d)` and extended by zero: for
`c = 𝔇.coord` this is `Stacks.WeilCohomology.FirstChernClassData.untwistTrace`. -/
def traceCoordWith (t : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F) :
    𝔇.H X →ₗ[F] F :=
  (t ∘ₗ (tateTwistCoordinates c (d : ℤ)).symm.toLinearMap) ∘ₗ 𝔇.projGrade X (2 * (d : ℤ))

/-- **The contraction `(id ⊗ λ) : H^*(P)(d) → H^*(X)`** for a fibre product `P` of `X` with
itself, with projections `p`, `q`: `Stacks.WeilCohomology.FirstChernClassData.traceContract`,
read through the Künneth isomorphism `H^*(X) ⊗ H^*(X) ≅ H^*(P)` of (A5)
(`Stacks.WeilDeRham.kunnethEquivOfIsPullback`). -/
def traceContractOfIsPullback
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F) :
    tateTwist F 𝔇.tate (𝔇.H P) d →ₗ[F] 𝔇.H X :=
  contractRight (𝔇.untwistTrace X d lam) ∘ₗ
    (kunnethEquivOfIsPullback p q hP hA5).symm.toLinearMap ∘ₗ 𝔇.κ P d

/-- For the product `X × X` with its projections, the contraction is that of the base. -/
theorem traceContract_eq_traceContractOfIsPullback
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F) :
    𝔇.traceContract hA5 X d lam =
      traceContractOfIsPullback hA5 (fst X X) (snd X X) (isPullback_fst_snd X X) d lam :=
  rfl

/-- `λ` read through a coordinate `c`, times the coordinate of `ℓ ∈ F(d)`, is `λ(a_{2d} ⊗ ℓ)`. -/
theorem tateLineCoordinates_mul_traceCoordWith
    (t : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F) (y : 𝔇.H X)
    (l : tateLine F 𝔇.tate (d : ℤ)) :
    tateLineCoordinates c (d : ℤ) l * traceCoordWith c d t y =
      t (𝔇.projGrade X (2 * (d : ℤ)) y ⊗ₜ[F] l) := by
  have hy : (𝔇.projGrade X (2 * (d : ℤ)) y ⊗ₜ[F] l :
      tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ)) =
      tateLineCoordinates c (d : ℤ) l •
        (tateTwistCoordinates c (d : ℤ)).symm (𝔇.projGrade X (2 * (d : ℤ)) y) := by
    apply (tateTwistCoordinates c (d : ℤ)).injective
    rw [tateTwistCoordinates_tmul, map_smul, LinearEquiv.apply_symm_apply]
  rw [hy, map_smul, smul_eq_mul]
  rfl

/-- The contraction of a pure twisted class `κ(s) ⊗ ℓ` read in a coordinate `c` does not depend
on `c`. -/
theorem contractRight_traceCoordWith_tmul
    (t : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F) (s : 𝔇.H X ⊗[F] 𝔇.H X)
    (l : tateLine F 𝔇.tate (d : ℤ)) :
    contractRight (traceCoordWith c d t) ((kunnethEquivOfIsPullback p q hP hA5).symm
        (tateTwistCoordinates c (d : ℤ)
          ((kunnethEquivOfIsPullback p q hP hA5 s) ⊗ₜ[F] l))) =
      contractRight (t ∘ₗ (TensorProduct.mk F _ (tateLine F 𝔇.tate (d : ℤ))).flip l ∘ₗ
        𝔇.projGrade X (2 * (d : ℤ))) s := by
  rw [tateTwistCoordinates_tmul, map_smul, LinearEquiv.symm_apply_apply, map_smul]
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add s s' hs hs' => simp only [map_add, smul_add, hs, hs']
  | tmul x y =>
    rw [contractRight_tmul, contractRight_tmul, smul_smul,
      tateLineCoordinates_mul_traceCoordWith]
    rfl

/-- **`id ⊗ λ` in an arbitrary coordinate.** -/
theorem diagonalContract_eq_of_coordinate
    (t : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F)
    (v : tateTwist F 𝔇.tate (𝔇.H P) (d : ℤ)) :
    traceContractOfIsPullback hA5 p q hP d t v =
      contractRight (traceCoordWith c d t)
        ((kunnethEquivOfIsPullback p q hP hA5).symm (tateTwistCoordinates c (d : ℤ) v)) := by
  set κ := kunnethEquivOfIsPullback p q hP hA5
  show contractRight (traceCoordWith 𝔇.coord d t) (κ.symm (tateTwistCoordinates 𝔇.coord
    (d : ℤ) v)) = _
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp only [map_add, hv, hv']
  | tmul w l =>
    obtain ⟨s, rfl⟩ := κ.surjective w
    rw [contractRight_traceCoordWith_tmul, contractRight_traceCoordWith_tmul]

/-- **The contraction is invariant under a morphism of fibre products**: for `φ : P ⟶ Q`
compatible with the projections, `(id ⊗ λ)(φ^*g)` on `P` is `(id ⊗ λ)(g)` on `Q`. -/
theorem traceContractOfIsPullback_pullTw {Q : (SmoothProjectiveScheme k).FullSubcategory}
    (p' q' : Q ⟶ X)
    (hQ : IsPullback ((toScheme k).map p') ((toScheme k).map q') X.obj.hom X.obj.hom)
    (φ : P ⟶ Q) (hp : φ ≫ p' = p) (hq : φ ≫ q' = q)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F)
    (g : tateTwist F 𝔇.tate (𝔇.H Q) d) :
    traceContractOfIsPullback hA5 p q hP d lam (𝔇.pullTw φ d g) =
      traceContractOfIsPullback hA5 p' q' hQ d lam g := by
  have hK : ∀ z, kunnethEquivOfIsPullback p q hP hA5 z =
      𝔇.pull φ (kunnethEquivOfIsPullback p' q' hQ hA5 z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul a b =>
      rw [kunnethEquivOfIsPullback_tmul, kunnethEquivOfIsPullback_tmul, map_mul,
        ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← 𝔇.pull_comp, ← 𝔇.pull_comp, hp, hq]
  simp only [traceContractOfIsPullback, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [FirstChernClassData.κ_pullTw]
  congr 1
  rw [LinearEquiv.symm_apply_eq, hK, LinearEquiv.apply_symm_apply]

/-- **Contracting against a form restricted to degree `m` takes the degree `N - m` part**, for the
Künneth preimage of a class of degree `N`. -/
theorem contractRight_comp_gradedProj {z : 𝔇.H X ⊗[F] 𝔇.H X} {N m : ℤ}
    (hz : kunnethEquivOfIsPullback p q hP hA5 z ∈ 𝔇.grade P N) (μ : 𝔇.H X →ₗ[F] F) :
    contractRight (μ ∘ₗ (𝔇.grade X m).subtype ∘ₗ 𝔇.projGrade X m) z =
      (𝔇.projGrade X (N - m) (contractRight μ z) : 𝔇.H X) := by
  classical
  have hproj : ∀ {n : ℤ} {a : 𝔇.H X} (ha : a ∈ 𝔇.grade X n), 𝔇.projGrade X n a = ⟨a, ha⟩ :=
    fun ha => Subtype.ext (by
      rw [FirstChernClassData.coe_projGrade, DirectSum.decompose_of_mem_same _ ha])
  have hproj0 : ∀ {n n' : ℤ} {a : 𝔇.H X} (_ : a ∈ 𝔇.grade X n') (_ : n' ≠ n),
      𝔇.projGrade X n a = 0 := fun ha hne => Subtype.ext (by
      rw [FirstChernClassData.coe_projGrade, DirectSum.decompose_of_mem_ne _ ha hne]; rfl)
  obtain ⟨S, f, hf, rfl⟩ := exists_bigraded_sum (𝔇 := 𝔇) z
  set κ := kunnethEquivOfIsPullback p q hP hA5
  have hκ : ∀ s ∈ S, κ (f s) ∈ 𝔇.grade P (s.1 + s.2) := fun s hs =>
    kunnethEquiv_mem_grade_of_mem_bigradedPiece hA5 p q hP (hf s)
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun s => s.1 + s.2 = N) f
  have hrest : ∑ s ∈ S.filter (fun s => ¬ s.1 + s.2 = N), f s = 0 := by
    apply κ.injective
    rw [map_zero]
    have h2 : κ (∑ s ∈ S.filter (fun s => s.1 + s.2 = N), f s) ∈ 𝔇.grade P N := by
      rw [map_sum]
      refine Submodule.sum_mem _ fun s hs => ?_
      have := hκ s (Finset.mem_filter.mp hs).1
      rwa [(Finset.mem_filter.mp hs).2] at this
    have hmemN : κ (∑ s ∈ S.filter (fun s => ¬ s.1 + s.2 = N), f s) ∈ 𝔇.grade P N := by
      have := congrArg κ hsplit
      rw [map_add] at this
      rw [eq_sub_of_add_eq' this]
      exact Submodule.sub_mem _ hz h2
    rw [← decompose_of_mem_same (𝔇.grade P) hmemN, map_sum, decompose_sum,
      DFinsupp.finset_sum_apply, Submodule.coe_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [decompose_of_mem_ne (𝔇.grade P) (hκ s (Finset.mem_filter.mp hs).1)
      (Finset.mem_filter.mp hs).2]
  rw [← hsplit, hrest, add_zero, map_sum, map_sum, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsN : s.1 + s.2 = N := (Finset.mem_filter.mp hs).2
  obtain ⟨t, ht⟩ := hf s
  rw [← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' h h' => simp only [map_add, h, h', Submodule.coe_add]
  | tmul a b =>
    rw [TensorProduct.map_tmul, contractRight_tmul, contractRight_tmul, Submodule.subtype_apply,
      Submodule.subtype_apply, map_smul, Submodule.coe_smul]
    by_cases hm : s.2 = m
    · have h1 : s.1 = N - m := by omega
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        hproj (hm ▸ b.2), ← h1, hproj a.2]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hproj0 b.2 hm]
      have h1 : s.1 ≠ N - m := by omega
      rw [hproj0 a.2 h1]
      simp

end Coordinate

/-! ### The descent -/

variable {k' : Type u} [Field k'] [Algebra k k'] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

/-- **The normalisation of (A6) descends** (Lemma 0FVT, paragraph (A6)): for a fibre product `P`
of `X` with itself and a class `g ∈ H^{2d}(P)(d)` (it will be the class `γ([Δ])` of the
diagonal), if `λ'` is normalised for the image of `g` on the fibre product `P_{k'}` of `X_{k'}`
with itself, `(id ⊗ λ')(g') = 1`, then some `λ` is normalised for `g`. -/
theorem exists_isDiagonalNormalized_of_fieldBaseChange (B : FieldBaseChangeData 𝔇 𝔇')
    (hA5 : 𝔇.KunnethAxiom) (hA5' : 𝔇'.KunnethAxiom)
    {X P : (SmoothProjectiveScheme k).FullSubcategory} (p q : P ⟶ X)
    (hP : IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom X.obj.hom) (d : ℕ)
    (g : tateTwist F 𝔇.tate (𝔇.H P) d) (hg : 𝔇.κ P d g ∈ 𝔇.grade P (2 * (d : ℤ)))
    (l' : tateTwist F' 𝔇'.tate (𝔇'.grade ((fieldBaseChange k k').obj X) (2 * (d : ℤ))) (d : ℤ)
      →ₗ[F'] F')
    (hl' : traceContractOfIsPullback hA5' ((fieldBaseChange k k').map p)
      ((fieldBaseChange k k').map q) (isPullback_fieldBaseChange_of_isPullback hP) d l'
      (B.twistHom P d g) = 1) :
    ∃ l, traceContractOfIsPullback hA5 p q hP d l g = 1 := by
  set c := tateLineCoordinate 𝔇.finrank_tate
  set c' := inducedTateCoordinate 𝔇 𝔇' B.tateEquiv
  set κ := kunnethEquivOfIsPullback p q hP hA5
  set κ' := kunnethEquivOfIsPullback ((fieldBaseChange k k').map p) ((fieldBaseChange k k').map q)
    (isPullback_fieldBaseChange_of_isPullback hP) hA5'
  set ξ := κ.symm (tateTwistCoordinates c (d : ℤ) g)
  set E := (AlgebraTensorModule.distribBaseChange F F' (𝔇.H X) (𝔇.H X)).trans
    (TensorProduct.congr (B.cohEquiv X).toLinearEquiv (B.cohEquiv X).toLinearEquiv)
  -- the Künneth preimage of `g'` is the base change of that of `g`
  have hξ' : κ'.symm (tateTwistCoordinates c' (d : ℤ) (B.twistHom P d g)) = E (1 ⊗ₜ ξ) := by
    apply κ'.injective
    rw [LinearEquiv.apply_symm_apply, B.tateTwistCoordinates_twistHom]
    have := B.kunnethMap_fieldBaseChange p q ξ
    change κ' (E (1 ⊗ₜ ξ)) = B.cohEquiv P (1 ⊗ₜ κ ξ) at this
    rw [κ.apply_symm_apply] at this
    exact this.symm
  have hn' := hl'
  rw [diagonalContract_eq_of_coordinate _ _ _ _ c'] at hn'
  change contractRight (traceCoordWith c' d l') (κ'.symm (tateTwistCoordinates c' (d : ℤ)
    (B.twistHom P d g))) = 1 at hn'
  rw [hξ'] at hn'
  -- the base-changed contraction problem has a solution
  set L : F' ⊗[F] 𝔇.H X →ₗ[F'] F' := traceCoordWith c' d l' ∘ₗ (B.cohEquiv X).toLinearMap
  have hL : baseChangeContract L ξ = (1 : F') ⊗ₜ[F] (1 : 𝔇.H X) := by
    apply (B.cohEquiv X).injective
    have hc : ∀ z : 𝔇.H X ⊗[F] 𝔇.H X, B.cohEquiv X (baseChangeContract L z) =
        contractRight (traceCoordWith c' d l') (E (1 ⊗ₜ z)) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, TensorProduct.tmul_add, hz, hz']
      | tmul x y =>
        simp only [baseChangeContract_tmul, map_smul, E, LinearEquiv.trans_apply,
          AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
          contractRight_tmul, L, LinearMap.comp_apply]
        rfl
    rw [hc, hn', ← Algebra.TensorProduct.one_def, map_one]
  obtain ⟨μ, hμ⟩ := exists_contract_eq_of_baseChange ξ 1 L hL
  refine ⟨μ ∘ₗ (𝔇.grade X (2 * (d : ℤ))).subtype ∘ₗ (tateTwistCoordinates c (d : ℤ)).toLinearMap,
    ?_⟩
  rw [diagonalContract_eq_of_coordinate _ _ _ _ c]
  have htc : traceCoordWith c d (μ ∘ₗ (𝔇.grade X (2 * (d : ℤ))).subtype ∘ₗ
      (tateTwistCoordinates c (d : ℤ)).toLinearMap) =
      μ ∘ₗ (𝔇.grade X (2 * (d : ℤ))).subtype ∘ₗ 𝔇.projGrade X (2 * (d : ℤ)) := by
    ext x
    simp [traceCoordWith]
  rw [htc, contractRight_comp_gradedProj hA5 p q hP (N := 2 * (d : ℤ))
    (by rw [LinearEquiv.apply_symm_apply]; exact hg) μ]
  show ((𝔇.projGrade X _ (contractRight μ ξ) : 𝔇.H X)) = 1
  rw [show contractRight μ ξ = 1 from hμ, sub_self, FirstChernClassData.coe_projGrade,
    DirectSum.decompose_of_mem_same _ SetLike.GradedOne.one_mem]

end Stacks.WeilDeRham

end
