module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerTopDimensionalComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The intersection number of a closed subspace as a sum over its top-dimensional components

Let `k` be a field, `X` a proper algebraic space over `k`, `i : Z ⟶ X` a closed subspace of
dimension `d` and `L₁, …, L_d` invertible `𝒪_X`-modules.  Stacks 0EDI writes the intersection
number `(L₁ ⋯ L_d · Z)` of Stacks 0EDF as `∑ m_i (L₁ ⋯ L_d · Z_i)`, the sum running over the
irreducible components `Z_i` of `Z` of dimension `d` and `m_i` being the length of `𝒪_Z` at a
geometric generic point of `Z_i`.  Its proof is "immediate from Stacks 0EDE": the function

`n ↦ χ(X, i_*𝒪_Z ⊗ L^{⊗ n}) - ∑ m_i χ(X, i_{i,*}𝒪_{Z_i} ⊗ L^{⊗ n})`

is a numerical polynomial of total degree `< d`, so its coefficient of `n₁ ⋯ n_d` vanishes.

This file proves Stacks 0EDI in that way, from the form
`AlgebraicGeometry.Space.exists_twistedEuler_sub_finsum_mul_componentStructureSheaf` of
Stacks 0EDE.  Because the intersection number is *defined*
as the `d`-fold mixed finite difference of the Euler characteristics at the indicator tuples
(`AlgebraicGeometry.Space.intersectionNumber_eq_sum`), and the mixed finite difference is linear,
only the polynomiality of the difference is used: no representing polynomial of any single one of
the Euler characteristics enters.

## Main results

* `Space.intersectionNumber_eq_finsum_mul_intersectionNumber_irreducibleComponents`:
  **Stacks 0EDI**, `(L₁ ⋯ L_d · Z) = ∑ m_i (L₁ ⋯ L_d · Z_i)` over the irreducible components
  `Z_i` of `Z` of dimension `d`.
* `AlgebraicGeometry.Space.moduleSupportSet_structureSheafPushforward_of_isClosedImmersion`: the
  support of `i_*𝒪_Z` is the image of `|Z|` in `|X|`, so the irreducible components of `Z` are
  those of the support of `i_*𝒪_Z`.
* `AlgebraicGeometry.Space.dimension_eq_topologicalKrullDim_range_of_isClosedImmersion` and
  `AlgebraicGeometry.Space.dimension_reducedClosedSubspace`: in a decent algebraic space the
  dimension of a closed subspace is the Krull dimension of its set of points; in particular the
  reduced closed subspace on an irreducible component of `|Z|` of dimension `d` has dimension `d`.
* `MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_zero_of_totalDegree_lt`: the `d`-fold
  mixed finite difference of a polynomial in `d` variables of total degree `< d` vanishes.
* `AlgebraicGeometry.Space.intersectionNumber_eq_finsum_mul_of_eval_eq_sub_finsum`: if the
  Euler characteristics of the twists of `i_*𝒪_Z` differ from a finite combination
  `∑ m_j χ(X, (i_j)_*𝒪_{Z_j} ⊗ L^{⊗ n})` by a polynomial of total degree `< d`, where each
  `i_j : Z_j ⟶ X` is a closed subspace of dimension `d`, then
  `(L₁ ⋯ L_d · Z) = ∑ m_j (L₁ ⋯ L_d · Z_j)`.
* `Space.intersectionNumber_eq_finsum_mul_of_eval_eq_sub_finsum_irreducibleComponents`:
  the same comparison indexed by the irreducible components of a closed set `T ⊆ |X|` of
  dimension `d`, the closed subspaces being the reduced closed subspaces on the components of
  dimension `d`.  Its polynomial hypothesis is the conclusion of Stacks 0EDE, read through the
  direct images along the inclusions of those subspaces.

## References

* [Stacks Project, Tag 0EDI](https://stacks.math.columbia.edu/tag/0EDI)
* [Stacks Project, Tag 0EDE](https://stacks.math.columbia.edu/tag/0EDE)
* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace MvPolynomial

/-- **The mixed finite difference of a polynomial of low degree vanishes.**  For a rational
polynomial `P` in `d` variables of total degree `< d`, or zero,

`∑_{S ⊆ {1, …, d}} (-1)^{d - |S|} P(1_S) = 0`.

The alternating sum is the coefficient of `n₁ ⋯ n_d`
(`MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one`), a monomial of degree `d`. -/
theorem sum_neg_one_pow_mul_eval_indicator_eq_zero_of_totalDegree_lt {d : ℕ}
    (P : MvPolynomial (Fin d) ℚ) (hP : P = 0 ∨ P.totalDegree < d) :
    ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        eval (fun j => if j ∈ S then (1 : ℚ) else 0) P = 0 := by
  rcases hP with rfl | hP
  · simp
  rw [sum_neg_one_pow_mul_eval_indicator_eq_coeff_one P hP.le]
  refine coeff_eq_zero_of_totalDegree_lt (hP.trans_le (le_of_eq ?_))
  change d = (Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1).sum fun _ e => e
  rw [Finsupp.sum_fintype _ _ fun _ => rfl]
  simp

end MvPolynomial

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section ClosedSubspace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The support of `i_*𝒪_Z` is `|Z|`.**  For a closed immersion `i : Z ⟶ X` of algebraic
spaces, the support of the direct image of the structure sheaf of `Z` is the image of `|Z|` in
`|X|`: the support of a direct image along a closed immersion is the image of the support
(`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion`), and
`Supp(𝒪_Z) = |Z|` (`AlgebraicGeometry.Space.supportOfSheaf_structureSheafModule`). -/
theorem moduleSupportSet_structureSheafPushforward_of_isClosedImmersion
    {X Z : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    moduleSupportSet B S hS X (structureSheafPushforward B S hS i) =
      Set.range (pointsMap B S hS Z.1 i.hom) := by
  have h := supportOfSheaf_structureSheafModule B S hS Z
  have e := supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS i hi
    (structureSheafModule B S hS Z) (by rw [h]; exact isClosed_univ)
  rw [h, Set.image_univ] at e
  exact e

/-- **The dimension of a closed subspace is the Krull dimension of its set of points.**  For a
closed immersion `j : W ⟶ X` into a decent algebraic space, the dimension of `W` (Stacks 04N6)
is the topological Krull dimension of the image of `|W|` in `|X|`.  The space `W` is decent
(Stacks 03KF, a closed immersion being representable), so its dimension is the Krull dimension
of `|W|` (Stacks 0A4J), and `|W| → |X|` is a closed embedding, hence a homeomorphism onto its
image. -/
theorem dimension_eq_topologicalKrullDim_range_of_isClosedImmersion
    {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hW : IsAlgebraicSpace B S hS W) (j : W ⟶ X)
    (hj : IsClosedImmersion B S hS j) :
    dimension B S hS W hW = topologicalKrullDim (Set.range (pointsMap B S hS W j)) := by
  rw [← topologicalKrullDim_points_eq_dimension_of_isDecentSpace B S hS hW
    (isDecentSpace_of_relativelyRepresentable B S hS hW j hj.rep hdec)]
  have he := isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hj
  exact IsHomeomorph.topologicalKrullDim_eq _ he.isEmbedding.toHomeomorph.isHomeomorph

/-- **The dimension of a reduced closed subspace is the Krull dimension of its closed set.**  For
a closed set `T ⊆ |X|` of a decent algebraic space, the reduced closed subspace on `T`
(Stacks 03IQ) has dimension `dim T`: its set of points is `T`
(`AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace`), and
`AlgebraicGeometry.Space.dimension_eq_topologicalKrullDim_range_of_isClosedImmersion` applies. -/
theorem dimension_reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    dimension B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
        (isClosedSubspace_reducedClosedSubspace B S hS X hX T hT).1 =
      topologicalKrullDim T := by
  rw [dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B S hS hX hdec _ _
    (isClosedSubspace_reducedClosedSubspace B S hS X hX T hT).2,
    range_pointsMap_ι_reducedClosedSubspace]

end ClosedSubspace

section IntersectionNumber

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X Z : AlgebraicSpaces B (Spec (.of k)) hk)

/-- **The intersection number is additive along a decomposition up to lower degree.**  Let
`i : Z ⟶ X` be a closed subspace of dimension `d` of a proper algebraic space over `k`, let
`L₁, …, L_d` be invertible `𝒪_X`-modules, and let `i_j : Z_j ⟶ X`, for `j` in a finite index
type, be closed subspaces of dimension `d` with integers `m_j`.  If

`χ(X, i_*𝒪_Z ⊗ L^{⊗ n}) - ∑_j m_j χ(X, (i_j)_*𝒪_{Z_j} ⊗ L^{⊗ n})`

is the restriction to the integral tuples of a rational polynomial of total degree `< d`, then
`(L₁ ⋯ L_d · Z) = ∑_j m_j (L₁ ⋯ L_d · Z_j)`.

This is the coefficient comparison by which Stacks 0EDI follows from Stacks 0EDE: the
intersection numbers are the mixed finite differences at the indicator tuples
(`AlgebraicGeometry.Space.intersectionNumber_eq_sum`), the mixed finite difference is linear,
and that of a polynomial of total degree `< d` vanishes
(`MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_zero_of_totalDegree_lt`). -/
theorem intersectionNumber_eq_finsum_mul_of_eval_eq_sub_finsum (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    {ι : Type*} [Finite ι] (Zc : ι → AlgebraicSpaces B (Spec (.of k)) hk)
    (ic : ∀ j, Zc j ⟶ X) (hic : ∀ j, IsClosedImmersion B (Spec (.of k)) hk (ic j).hom)
    (hdc : ∀ j, dimension B (Spec (.of k)) hk (Zc j).1 (Zc j).2 = d) (m : ι → ℤ)
    (P : MvPolynomial (Fin d) ℚ) (hPdeg : P = 0 ∨ P.totalDegree < d)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L n)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi L n) : ℤ) : ℚ) -
        ∑ᶠ j, (m j : ℚ) * ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk (ic j)) L n)
            (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
              k B hk X (Zc j) f hf (ic j) (hic j) L n) : ℤ) : ℚ)) :
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      ∑ᶠ j, m j * intersectionNumber.{u, w} k B hk X (Zc j) d f hf (ic j) (hic j) (hdc j) L := by
  have := Fintype.ofFinite ι
  have hval : ∀ S : Finset (Fin d),
      MvPolynomial.eval (fun j => if j ∈ S then (1 : ℚ) else 0) P =
        MvPolynomial.eval (fun j => (((if j ∈ S then 1 else 0 : ℤ)) : ℚ)) P := by
    intro S
    refine congrArg (fun v => MvPolynomial.eval v P) (funext fun j => ?_)
    split_ifs <;> simp
  have hzero := MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_zero_of_totalDegree_lt P hPdeg
  simp_rw [hval, hP, finsum_eq_sum_of_fintype] at hzero
  apply Int.cast_injective (α := ℚ)
  rw [finsum_eq_sum_of_fintype, intersectionNumber_eq_sum]
  simp_rw [intersectionNumber_eq_sum]
  push_cast
  rw [← sub_eq_zero, ← hzero]
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S _ => ?_
  ring

/-- **The coefficient comparison over the top-dimensional components of a closed set.**  Let
`i : Z ⟶ X` be a closed subspace of dimension `d` of a decent proper algebraic space over `k`, let
`T ⊆ |X|` be a closed set of Krull dimension `d` with finitely many irreducible components, and
let `m_C` be integers indexed by those components.  For a component `C` write `Z_C` for the
reduced closed subspace on `C` (Stacks 03IQ).  If

`χ(X, i_*𝒪_Z ⊗ L^{⊗ n}) - ∑_{C, dim C = dim T} m_C χ(X, 𝒪_{Z_C} ⊗ L^{⊗ n})`

is the function of a rational polynomial of total degree `< dim T`, then
`(L₁ ⋯ L_d · Z) = ∑_{C, dim C = d} m_C (L₁ ⋯ L_d · Z_C)`.

This is the shape in which Stacks 0EDE delivers its conclusion; the reduced closed subspace on a
component of dimension `d` has dimension `d`
(`AlgebraicGeometry.Space.dimension_reducedClosedSubspace`), so its intersection number is
defined, and `AlgebraicGeometry.Space.intersectionNumber_eq_finsum_mul_of_eval_eq_sub_finsum`
applies. -/
theorem intersectionNumber_eq_finsum_mul_of_eval_eq_sub_finsum_irreducibleComponents (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (hdec : IsDecentSpace B (Spec (.of k)) hk X.1) {T : Set (points B (Spec (.of k)) hk X.1)}
    (hT : IsClosed T) (hTd : topologicalKrullDim T = d) [Finite (irreducibleComponents T)]
    (m : irreducibleComponents T → ℤ) (P : MvPolynomial (Fin d) ℚ)
    (hPdeg : P = 0 ∨ (P.totalDegree : WithBot ℕ∞) < topologicalKrullDim T)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L n)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi L n) : ℤ) : ℚ) -
        ∑ᶠ C ∈ {C : irreducibleComponents T |
            topologicalKrullDim (Subtype.val '' (C : Set T)) = topologicalKrullDim T},
          (m C : ℚ) * ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
            (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
              (structureSheafPushforward B (Spec (.of k)) hk
                (closedSubfunctorι B (Spec (.of k)) hk
                  (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                    (closedSetComponentPoints B (Spec (.of k)) hk T hT C).isClosed))) L n)
              (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X _ f hf
                (closedSubfunctorι B (Spec (.of k)) hk
                  (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                    (closedSetComponentPoints B (Spec (.of k)) hk T hT C).isClosed))
                (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                  (closedSetComponentPoints B (Spec (.of k)) hk T hT C).isClosed).2 L n) :
                ℤ) : ℚ)) :
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      ∑ᶠ (C : {C : irreducibleComponents T //
          topologicalKrullDim (Subtype.val '' (C : Set T)) = d}),
        m C.1 * intersectionNumber.{u, w} k B hk X
          (closedSubfunctorSpace B (Spec (.of k)) hk
            (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
              (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed)) d f hf
          (closedSubfunctorι B (Spec (.of k)) hk
            (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
              (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed))
          (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
            (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed).2
          ((dimension_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 hdec _ _).trans C.2) L := by
  refine intersectionNumber_eq_finsum_mul_of_eval_eq_sub_finsum.{u, w} k B hk X Z d f hf i hi hd L
    (ι := {C : irreducibleComponents T // topologicalKrullDim (Subtype.val '' (C : Set T)) = d})
    _ _ _ _ (fun C => m C.1) P ?_ fun n => ?_
  · rcases hPdeg with h | h
    · exact Or.inl h
    · rw [hTd] at h
      exact Or.inr (by exact_mod_cast h)
  · rw [hP n]
    simp only [Set.mem_ofPred_eq, hTd]
    rw [← finsum_subtype_eq_finsum_cond]

/-- **Stacks 0EDI.**  Let `k` be a field, `X` a proper algebraic space over `k`, `i : Z ⟶ X` a
closed subspace of dimension `d` and `L₁, …, L_d` invertible `𝒪_X`-modules.  Let `Z_C ⊆ Z` be the
irreducible components of `Z` of dimension `d` — the components `C` of the closed set
`|Z| ⊆ |X|` of Krull dimension `d`, each with its reduced induced structure (Stacks 03IQ) — let
`x̄_C` be a geometric generic point of `Z_C` and let
`m_C = length_{𝒪_{X, x̄_C}}(𝒪_{Z, x̄_C})`, the length of the stalk of `i_*𝒪_Z` at `x̄_C`.  Then

`(L₁ ⋯ L_d · Z) = ∑_C m_C (L₁ ⋯ L_d · Z_C)`.

As in the source this is immediate from Stacks 0EDE, in the form
`AlgebraicGeometry.Space.exists_twistedEuler_sub_finsum_mul_componentStructureSheaf` applied to
`F = i_*𝒪_Z`, whose support is `|Z|`
(`AlgebraicGeometry.Space.moduleSupportSet_structureSheafPushforward_of_isClosedImmersion`):
the difference of the Euler characteristics is a polynomial of total degree `< d`, so its
coefficient of `n₁ ⋯ n_d` vanishes, and comparing that coefficient is
`Space.intersectionNumber_eq_finsum_mul_of_eval_eq_sub_finsum_irreducibleComponents`.
The length `m_C` is a natural number by Stacks 0EE4. -/
@[stacks 0EDI, sga "6 X 4.4" "partial"]
theorem intersectionNumber_eq_finsum_mul_intersectionNumber_irreducibleComponents (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (x : irreducibleComponents (Set.range (pointsMap B (Spec (.of k)) hk Z.1 i.hom)) →
      GeometricPoint B (Spec (.of k)) hk X.1)
    (hx : ∀ C, IsGenericPoint (x C).image
      (Subtype.val '' (C : Set (Set.range (pointsMap B (Spec (.of k)) hk Z.1 i.hom))))) :
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      ∑ᶠ (C : {C : irreducibleComponents (Set.range (pointsMap B (Spec (.of k)) hk Z.1 i.hom)) //
          topologicalKrullDim (Subtype.val ''
            (C : Set (Set.range (pointsMap B (Spec (.of k)) hk Z.1 i.hom)))) = d}),
        ((geometricLength B (Spec (.of k)) hk X (x C.1)
            (structureSheafPushforward B (Spec (.of k)) hk i)).toNat : ℤ) *
          intersectionNumber.{u, w} k B hk X
            (closedSubfunctorSpace B (Spec (.of k)) hk
              (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                (closedSetComponentPoints B (Spec (.of k)) hk _
                  (isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of k)) hk X.2 i.hom hi)
                  C.1).isClosed)) d f hf
            (closedSubfunctorι B (Spec (.of k)) hk
              (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                (closedSetComponentPoints B (Spec (.of k)) hk _
                  (isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of k)) hk X.2 i.hom hi)
                  C.1).isClosed))
            (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
              (closedSetComponentPoints B (Spec (.of k)) hk _
                (isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of k)) hk X.2 i.hom hi)
                C.1).isClosed).2
            ((dimension_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2
              (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) _ _).trans C.2) L := by
  have hdec := isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf
  have hT := isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of k)) hk X.2 i.hom hi
  have hTd : topologicalKrullDim (Set.range (pointsMap B (Spec (.of k)) hk Z.1 i.hom)) = d :=
    (dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B (Spec (.of k)) hk X.2 hdec Z.2
      i.hom hi).symm.trans hd
  have := noetherianSpace_points_of_isProper_baseObject k B hk X.1 X.2 f hf
  have : Finite (irreducibleComponents (Set.range (pointsMap B (Spec (.of k)) hk Z.1 i.hom))) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hF := isCoherent_structureSheafPushforward B (Spec (.of k)) hk
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) i hi
  obtain ⟨P, hPdeg, hP⟩ := exists_twistedEuler_sub_finsum_mul_componentStructureSheaf.{u, w}
    k B hk X f hf L hT x hx _ hF
    (moduleSupportSet_structureSheafPushforward_of_isClosedImmersion B (Spec (.of k)) hk i hi).le
  exact intersectionNumber_eq_finsum_mul_of_eval_eq_sub_finsum_irreducibleComponents.{u, w}
    k B hk X Z d f hf i hi hd L hdec hT hTd _ P hPdeg hP

end IntersectionNumber

end AlgebraicGeometry.Space

end
