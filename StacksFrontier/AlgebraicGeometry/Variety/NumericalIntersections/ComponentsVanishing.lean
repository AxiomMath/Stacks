module

public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Components
public import StacksCore.Tactic.StacksAttribute

/-!
# The intersection number as a sum over the components of dimension exactly `d`

Let `k` be a field, let `X` be a proper scheme over `k`, let `i : Z ⟶ X` be a closed subscheme
of dimension *at most* `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  [Stacks, Tag
0BES] says that the intersection number `(𝓛_1 ⋯ 𝓛_d · Z)` of [Stacks, Tag 0BEP] is the sum,
over the irreducible components `Z_1, …, Z_t` of `Z` *of dimension `d`*, of the intersection
numbers of the components weighted by the multiplicities
`m_i = length_{𝒪_{X, ξ_i}} 𝒪_{Z, ξ_i}` at the generic points `ξ_i`:

`(𝓛_1 ⋯ 𝓛_d · Z) = ∑_i m_i (𝓛_1 ⋯ 𝓛_d · Z_i)`.

`AlgebraicGeometry.intersectionNumber_eq_sum_topDimComponents` is the case `dim Z = d`, where
the components of dimension `d` are exactly the top-dimensional ones.  This file adds the
remaining case `dim Z < d`, where there are no components of dimension `d` at all: the sum is
empty and the intersection number vanishes.  Putting the two together gives the tag over its
whole range of hypotheses.

## Main results

* `AlgebraicGeometry.intersectionNumber_eq_sum_dimComponents`: **[Stacks, Tag 0BES].**  The
  intersection number of a closed subscheme of dimension at most `d` is the length-weighted sum
  over its integral closed subschemes of dimension exactly `d`.
* `AlgebraicGeometry.intersectionNumber_eq_zero_of_topologicalKrullDim_lt`: the case
  `dim Z < d` of the tag, in which the intersection number is zero.
* `AlgebraicGeometry.isEmpty_dimIntegralSubscheme_of_topologicalKrullDim_lt`: the reason it is
  zero, namely that `Supp ℱ` has no integral closed subscheme of dimension `d` once
  `dim Supp ℱ < d`.

## Implementation notes

**The index of the sum.**  `AlgebraicGeometry.DimIntegralSubscheme ℱ d` is the type of integral
closed subschemes of `X` contained in `Supp ℱ` and of dimension exactly `d`.  For `ℱ = i_*𝒪_Z`
with `dim Z ≤ d` these are the source's `Z_i`: an integral closed subscheme of `Z` of dimension
`d` admits no strictly larger irreducible closed subset of `Z`, because such a subset would
have dimension greater than `d ≥ dim Z`, so it is an irreducible component of `Z`.  When
`dim Z = d` the type is `AlgebraicGeometry.TopDimIntegralSubscheme (i_*𝒪_Z)` of [Stacks, Tag
0BEN] — the same subtype with the dimension condition spelled through `dim Supp ℱ` — and the
two sums are identified by transport along that bijection.

**The vanishing.**  [Stacks, Tag 0BEM]
(`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`) produces a polynomial `P`
which is zero or of total degree at most `dim Supp (i_*𝒪_Z) = dim Z` and whose values are the
Euler characteristics `χ(X, i_*𝒪_Z ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯)`; these are the Euler characteristics
`χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ |_Z)` downstairs, by
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion`.  By
[Stacks, Tag 0BEP] (`AlgebraicGeometry.intersectionNumber_eq_coeff`) the intersection number is
the coefficient of the squarefree monomial `n_1 ⋯ n_d` in `P`.  That monomial has degree `d`,
which exceeds the total degree of `P`, so the coefficient — and with it the intersection
number — is zero.

## References

* [Stacks Project, Tag 0BES](https://stacks.math.columbia.edu/tag/0BES)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEN](https://stacks.math.columbia.edu/tag/0BEN)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] twistedSheaf_isCoherent isCoherent_pushforward_of_isClosedImmersion
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent

/-! ### Integral closed subschemes of a prescribed dimension -/

/-- The integral closed subschemes of `X` contained in the support of a module `ℱ` and of
dimension exactly `d`, carrying their reduced induced closed-subscheme structures.  When
`dim Supp ℱ ≤ d` these are the irreducible components of `Supp ℱ` of dimension `d`: no
irreducible closed subset of `Supp ℱ` can strictly contain one of them. -/
public abbrev DimIntegralSubscheme {X : Scheme.{u}} (F : X.Modules) (d : ℕ) : Type u :=
  {Z : X.IdealSheafData // IsIntegral Z.subscheme ∧
    (Z.support : Set X) ⊆ _root_.SheafOfModules.supp F ∧
    topologicalKrullDim Z.subscheme = (d : WithBot ℕ∞)}

namespace DimIntegralSubscheme

variable {X : Scheme.{u}} {F : X.Modules} {d : ℕ}

/-- The generic point of a `d`-dimensional integral component of `Supp ℱ`, read as a point of
the ambient scheme. -/
public def genericPt (Z : DimIntegralSubscheme F d) : X :=
  have := Z.2.1
  Z.1.subschemeι (genericPoint Z.1.subscheme)

/-- A `d`-dimensional integral component of `Supp ℱ` has dimension at most `d`, so its
intersection number against `d` invertible modules is defined. -/
public theorem topologicalKrullDim_le (Z : DimIntegralSubscheme F d) :
    topologicalKrullDim Z.1.subscheme ≤ (d : WithBot ℕ∞) :=
  le_of_eq Z.2.2.2

end DimIntegralSubscheme

/-- **A support of dimension less than `d` has no integral closed subscheme of dimension `d`.**
Such a subscheme has the dimension of its underlying closed subset of `X`, and that subset sits
inside `Supp ℱ`, whose dimension is smaller. -/
public theorem isEmpty_dimIntegralSubscheme_of_topologicalKrullDim_lt {X : Scheme.{u}}
    (F : X.Modules) {d : ℕ}
    (h : topologicalKrullDim (_root_.SheafOfModules.supp F) < (d : WithBot ℕ∞)) :
    IsEmpty (DimIntegralSubscheme F d) := by
  refine ⟨fun W => absurd W.2.2.2 (ne_of_lt ?_)⟩
  calc topologicalKrullDim W.1.subscheme
      = topologicalKrullDim (W.1.support : Set X) := (topologicalKrullDim_support_eq W.1).symm
    _ ≤ topologicalKrullDim (_root_.SheafOfModules.supp F) :=
        (Topology.IsEmbedding.inclusion W.2.2.1).isInducing.topologicalKrullDim_le
    _ < (d : WithBot ℕ∞) := h

/-- The support of the pushforward of the structure sheaf along a closed immersion `i : Z ⟶ X` has
the dimension of `Z`. -/
private theorem topologicalKrullDim_supp_pushforward_unitModule {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    topologicalKrullDim (_root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) =
        topologicalKrullDim Z := by
  rw [Stacks.Chow.supp_pushforwardStructureSheaf i, topologicalKrullDim_range_eq i]

/-! ### Tag 0BES, the case `dim Z < d` -/

/-- **[Stacks, Tag 0BES], the case `dim Z < d`.**  Let `k` be a field, let `X` be proper over
`k`, let `i : Z ⟶ X` be a closed subscheme of dimension *strictly* less than `d` and let
`𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  Then `(𝓛_1 ⋯ 𝓛_d · Z) = 0`.

This is the degenerate half of the tag: `Z` has no irreducible component of dimension `d`, so
the weighted sum over those components is empty, and the intersection number has to vanish. -/
public theorem intersectionNumber_eq_zero_of_topologicalKrullDim_lt (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞))
    (hlt : topologicalKrullDim Z < (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i d hd L = 0 := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hZcoh : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  have hFcoh : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i (Stacks.Ample.unitModule Z)
  have hdimF := topologicalKrullDim_supp_pushforward_unitModule i ▸ hlt
  obtain ⟨P, hPdeg, hPeval⟩ :=
    exists_eulerPolynomial_twistedSheaf_of_isProper k f L
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) hFcoh
  have hPlt : P = 0 ∨ P.totalDegree < d :=
    hPdeg.imp_right fun h => by exact_mod_cast lt_of_le_of_lt h hdimF
  have hdegle : P.totalDegree ≤ d := by
    rcases hPlt with h | h
    · simp [h]
    · exact h.le
  have hcoeff : P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = 0 := by
    rcases hPlt with h | hlt'
    · simp [h]
    · have hv : ∀ j : Fin d,
          (Finsupp.equivFunOnFinite.symm fun _ : Fin d => (1 : ℕ)) j = 1 := fun _ => rfl
      have hsupp : (Finsupp.equivFunOnFinite.symm fun _ : Fin d => (1 : ℕ)).support =
          Finset.univ :=
        Finset.eq_univ_of_forall fun j =>
          Finsupp.mem_support_iff.mpr (by rw [hv j]; exact one_ne_zero)
      refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt (hlt'.trans_le (le_of_eq ?_))
      rw [hsupp]
      simp [hv]
  have hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun j => (Scheme.Modules.pullback i).obj (L j)) n)
        (isCoherent_twistedSheafUnitPullback k f i L n) : ℤ) : ℚ) := by
    intro n
    rw [hPeval n]
    exact congrArg (fun m : ℤ => (m : ℚ))
      (eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k i f L
        (Stacks.Ample.unitModule Z) n inferInstance inferInstance)
  have hmain := intersectionNumber_eq_coeff k f i d hd L P hP hdegle
  rw [hcoeff] at hmain
  exact_mod_cast hmain

/-! ### Tag 0BES -/

/-- **[Stacks, Tag 0BES].**  Let `k` be a field, let `X` be proper over `k`, let `i : Z ⟶ X` be
a closed subscheme of dimension at most `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.
Writing `Z_1, …, Z_t` for the irreducible components of `Z` of dimension `d`, with generic
points `ξ_i` and multiplicities `m_i = length_{𝒪_{X, ξ_i}} 𝒪_{Z, ξ_i}`, the intersection number
of `Z` is the weighted sum of those of its `d`-dimensional components:

`(𝓛_1 ⋯ 𝓛_d · Z) = ∑_i m_i (𝓛_1 ⋯ 𝓛_d · Z_i)`.

For `dim Z = d` this is
`AlgebraicGeometry.intersectionNumber_eq_sum_topDimComponents`, the components of dimension `d`
being then the top-dimensional ones; for `dim Z < d` both sides are zero, the sum being
empty. -/
@[stacks 0BES]
public theorem intersectionNumber_eq_sum_dimComponents (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i d hd L =
      ∑ᶠ W : DimIntegralSubscheme
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d,
        Stacks.Chow.sheafMultiplicity
            ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) W.genericPt *
          intersectionNumber k f W.1.subschemeι d W.topologicalKrullDim_le L := by
  rcases lt_or_eq_of_le hd with hlt | heq
  · -- No component has dimension `d`: the sum is empty and the intersection number vanishes.
    have : IsEmpty (DimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d) :=
      isEmpty_dimIntegralSubscheme_of_topologicalKrullDim_lt _
        (topologicalKrullDim_supp_pushforward_unitModule i ▸ hlt)
    rw [intersectionNumber_eq_zero_of_topologicalKrullDim_lt k f i d hd hlt L,
      finsum_of_isEmpty]
  · -- The components of dimension `d` are the top-dimensional ones.
    have hdimF := (topologicalKrullDim_supp_pushforward_unitModule i).trans heq
    let e : DimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d ≃
        TopDimIntegralSubscheme
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) :=
      { toFun := fun W => ⟨W.1, W.2.1, W.2.2.1, by rw [hdimF]; exact W.2.2.2⟩
        invFun := fun W => ⟨W.1, W.2.1, W.2.2.1, by rw [← hdimF]; exact W.2.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine (intersectionNumber_eq_sum_topDimComponents k f i d heq L).trans ?_
    exact (finsum_comp_equiv e).symm

end AlgebraicGeometry

end
