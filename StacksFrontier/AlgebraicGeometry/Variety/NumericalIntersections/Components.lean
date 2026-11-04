module

public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
public import StacksCore.Tactic.StacksAttribute

/-!
# The intersection number as a sum over the top-dimensional components

Let `k` be a field, let `X` be a proper scheme over `k`, let `i : Z ⟶ X` be a closed subscheme
of dimension `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  [Stacks, Tag 0BES] says
that the intersection number `(𝓛_1 ⋯ 𝓛_d · Z)` of [Stacks, Tag 0BEP] is the sum, over the
irreducible components `Z_1, …, Z_t` of `Z` of dimension `d`, of the intersection numbers of
the components weighted by the multiplicities
`m_i = length_{𝒪_{X, ξ_i}} 𝒪_{Z, ξ_i}` at the generic points `ξ_i`:

`(𝓛_1 ⋯ 𝓛_d · Z) = ∑_i m_i (𝓛_1 ⋯ 𝓛_d · Z_i)`.

## Main results

* `AlgebraicGeometry.intersectionNumber_eq_sum_topDimComponents`: **[Stacks, Tag 0BES]**, in the
  case `dim Z = d`.
* `AlgebraicGeometry.topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme`: a
  `d`-dimensional component of a `d`-dimensional closed subscheme is itself of dimension at
  most `d`, which is what makes its intersection number against `d` invertible modules
  meaningful.

## Implementation notes

**The index of the sum.**  The components are indexed exactly as in [Stacks, Tag 0BEN]: a term
of `AlgebraicGeometry.TopDimIntegralSubscheme ℱ` is an integral closed subscheme of `X`
contained in `Supp ℱ` and of the same dimension as it, so for `ℱ = i_*𝒪_Z` these are the
`d`-dimensional irreducible components of `Z` carrying their reduced induced structures.  The
multiplicity `m_i` is `Stacks.Chow.sheafMultiplicity (i_*𝒪_Z) ξ_i`, the length of the stalk
`(i_*𝒪_Z)_{ξ_i} = 𝒪_{Z, ξ_i}` over `𝒪_{X, ξ_i}`, which is the source's `m_i`.  The
intersection number of a component is the library's own
`AlgebraicGeometry.intersectionNumber` for the closed immersion
`Scheme.IdealSheafData.subschemeι` of that component.

**The dimension hypothesis.**  [Stacks, Tag 0BEP] is set up here with `dim Z ≤ d`, but the
source's `Z_i` are the components *of dimension `d`*, so the hypothesis below is the source's
own `dim Z = d`.  With only `dim Z < d` the index type `TopDimIntegralSubscheme (i_*𝒪_Z)` would
still be inhabited — by the components of dimension `dim Z` — whereas the source sums over the
components of dimension `d`, of which there are none; that case is
`AlgebraicGeometry.intersectionNumber_eq_zero_of_topologicalKrullDim_lt`, and the two cases are
put together over the source's own hypothesis `dim Z ≤ d` in
`AlgebraicGeometry.intersectionNumber_eq_sum_dimComponents`, both in
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/ComponentsVanishing.lean`.

**The route.**  The proof is the source's.  The intersection number is the `d`-fold mixed
finite difference `∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} χ(Z, ⨂_{t ∈ T} 𝓛_t|_Z)` of the Euler
characteristics, which is the coefficient of `n_1 ⋯ n_d` in any interpolating polynomial of
total degree at most `d` (`MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one`).
[Stacks, Tag 0BEN] produces a polynomial `P` of total degree *strictly* less than `d` whose
values are `χ(X, i_*𝒪_Z ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯) - ∑_i m_i χ(Z_i, 𝒪_{Z_i} ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯)`;
the squarefree monomial `n_1 ⋯ n_d` has degree `d`, so its coefficient in `P` vanishes, and the
mixed finite difference of the difference of Euler characteristics is zero.  The two Euler
characteristics upstairs and downstairs agree by
`AlgebraicGeometry.eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion`.

**Finiteness of the index.**  The alternating sum over `T ⊆ {1, …, d}` has to be interchanged
with the sum over the components, so the index type is shown finite: a top-dimensional integral
closed subscheme of `Supp ℱ` is determined by its underlying closed set, which is an
irreducible component of `Supp ℱ` because it is irreducible, closed and of the full (finite)
dimension, and a Noetherian space has finitely many irreducible components.

## References

* [Stacks Project, Tag 0BES](https://stacks.math.columbia.edu/tag/0BES)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEN](https://stacks.math.columbia.edu/tag/0BEN)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] twistedSheaf_isCoherent isCoherent_pushforward_of_isClosedImmersion
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent

/-! ### Tag 0BES -/

/-- The support of `i_*𝒪_Z`, for `i : Z ⟶ X` a closed subscheme of dimension `d`, has dimension
`d`. -/
private theorem topologicalKrullDim_supp_pushforward_unitModule {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {d : ℕ} (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) :
    topologicalKrullDim (_root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) = (d : WithBot ℕ∞) := by
  rw [Stacks.Chow.supp_pushforwardStructureSheaf i, topologicalKrullDim_range_eq i]
  exact hd

/-- A `d`-dimensional integral component of the support of `i_*𝒪_Z`, for `i : Z ⟶ X` a closed
subscheme of dimension `d`, has dimension at most `d`, so its intersection number against `d`
invertible modules is defined. -/
public theorem topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {d : ℕ}
    (hd : topologicalKrullDim Z = (d : WithBot ℕ∞))
    (W : TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :
    topologicalKrullDim W.1.subscheme ≤ (d : WithBot ℕ∞) := by
  exact le_of_eq (W.2.2.2.trans (topologicalKrullDim_supp_pushforward_unitModule i hd))

/-- **[Stacks, Tag 0BES].**  Let `k` be a field, let `X` be proper over `k`, let `i : Z ⟶ X` be
a closed subscheme of dimension `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  Writing
`Z_1, …, Z_t` for the irreducible components of `Z` of dimension `d`, with generic points `ξ_i`
and multiplicities `m_i = length_{𝒪_{X, ξ_i}} 𝒪_{Z, ξ_i}`, the intersection number of `Z` is
the weighted sum of those of its components:

`(𝓛_1 ⋯ 𝓛_d · Z) = ∑_i m_i (𝓛_1 ⋯ 𝓛_d · Z_i)`. -/
@[stacks 0BES "the intersection number is the length-weighted sum of the intersection numbers
of the top-dimensional irreducible components"]
public theorem intersectionNumber_eq_sum_topDimComponents (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i d hd.le L =
      ∑ᶠ W : TopDimIntegralSubscheme
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
        Stacks.Chow.sheafMultiplicity
            ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) W.genericPt *
          intersectionNumber k f W.1.subschemeι d
            (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd W) L := by
  classical
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hnoe : IsNoetherian X := ⟨⟩
  have hZcoh : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  have hFcoh : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i (Stacks.Ample.unitModule Z)
  have hfinite : Finite (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :=
    finite_topDimIntegralSubscheme k f _
  have hft : Fintype (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) := Fintype.ofFinite _
  obtain ⟨P, hPdeg, hPeval⟩ :=
    exists_eulerPolynomial_sub_topDimComponents_totalDegree_lt k f L
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))
  rw [topologicalKrullDim_supp_pushforward_unitModule i hd] at hPdeg
  -- The coefficient of the degree-`d` monomial `n_1 ⋯ n_d` in `P` vanishes.
  have hdegle : P.totalDegree ≤ d := by
    rcases hPdeg with h | h
    · simp [h]
    · exact le_of_lt (by exact_mod_cast h)
  have hcoeff : P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = 0 := by
    rcases hPdeg with h | h
    · simp [h]
    · refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
      have hlt : P.totalDegree < d := by exact_mod_cast h
      simpa using hlt
  have hsum : ∑ T : Finset (Fin d), (-1 : ℚ) ^ (d - T.card) *
      MvPolynomial.eval (fun j => if j ∈ T then (1 : ℚ) else 0) P = 0 := by
    rw [MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one P hdegle, hcoeff]
  -- The values of `P` at the indicator functions, read downstairs on `Z`.
  have hevalT : ∀ T : Finset (Fin d),
      MvPolynomial.eval (fun j => if j ∈ T then (1 : ℚ) else 0) P =
        ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
            (twistedSheaf (Stacks.Ample.unitModule Z)
              (fun j => (Scheme.Modules.pullback i).obj (L j))
              (fun j => if j ∈ T then 1 else 0)) inferInstance : ℤ) : ℚ) -
          ∑ W : TopDimIntegralSubscheme
              ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
            (Stacks.Chow.sheafMultiplicity
                ((Scheme.Modules.pushforward i).obj
                  (Stacks.Ample.unitModule Z)) W.genericPt : ℚ) *
              (componentTwistEulerCharacteristic k f L W
                (fun j => if j ∈ T then 1 else 0) : ℚ) := by
    intro T
    have h := hPeval fun j => if j ∈ T then (1 : ℤ) else 0
    rw [show (fun j : Fin d => (((if j ∈ T then (1 : ℤ) else 0) : ℤ) : ℚ)) =
        fun j : Fin d => if j ∈ T then (1 : ℚ) else 0 from
      funext fun j => by split_ifs <;> simp] at h
    rw [h, finsum_eq_sum_of_fintype]
    congr 1
    exact congrArg (fun m : ℤ => (m : ℚ))
      (eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion k i f L
        (Stacks.Ample.unitModule Z) _ inferInstance inferInstance)
  -- The mixed finite difference of the correction vanishes.
  have hzero : ∑ T : Finset (Fin d), (-1 : ℚ) ^ (d - T.card) *
      (((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
            (twistedSheaf (Stacks.Ample.unitModule Z)
              (fun j => (Scheme.Modules.pullback i).obj (L j))
              (fun j => if j ∈ T then 1 else 0)) inferInstance : ℤ) : ℚ) -
        ∑ W : TopDimIntegralSubscheme
            ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
          (Stacks.Chow.sheafMultiplicity
              ((Scheme.Modules.pushforward i).obj
                (Stacks.Ample.unitModule Z)) W.genericPt : ℚ) *
            (componentTwistEulerCharacteristic k f L W
              (fun j => if j ∈ T then 1 else 0) : ℚ)) = 0 := by
    rw [← hsum]
    exact (Finset.sum_congr rfl fun T _ => by rw [hevalT T]).symm
  simp only [mul_sub] at hzero
  rw [Finset.sum_sub_distrib, sub_eq_zero] at hzero
  -- Compare the two sides of the tag, after casting to `ℚ`.
  have hcomp : ∀ W : TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
      ((intersectionNumber k f W.1.subschemeι d
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd W) L : ℤ) : ℚ) =
        ∑ T : Finset (Fin d), (-1 : ℚ) ^ (d - T.card) *
          (componentTwistEulerCharacteristic k f L W
            (fun j => if j ∈ T then 1 else 0) : ℚ) := by
    intro W
    rw [intersectionNumber_eq_sum_eulerCharacteristic]
    push_cast
    exact Finset.sum_congr rfl fun T _ => rfl
  have hgoal : ((intersectionNumber k f i d hd.le L : ℤ) : ℚ) =
      ((∑ᶠ W : TopDimIntegralSubscheme
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
        Stacks.Chow.sheafMultiplicity
            ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) W.genericPt *
          intersectionNumber k f W.1.subschemeι d
            (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd W) L : ℤ) : ℚ) := by
    rw [finsum_eq_sum_of_fintype, intersectionNumber_eq_sum_eulerCharacteristic]
    push_cast
    rw [hzero]
    simp only [hcomp, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun T _ => by ring
  exact_mod_cast hgoal

end AlgebraicGeometry

end
