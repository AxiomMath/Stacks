module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.EulerCharacteristicAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberPolynomial

/-!
# Intersecting with an effective Cartier divisor, unconditionally (Stacks 0EDK)

Let `k` be a field, let `X` be a proper algebraic space over `k`, let `i : Z ⟶ X` be a closed
subspace of dimension `d + 1` and let `L₁, …, L_{d+1}` be invertible `𝒪_X`-modules.  If
`L₁|_Z ≅ 𝒪_Z(D)` for an effective Cartier divisor `D ⊆ Z`, then

`(L₁ ⋯ L_{d+1} · Z) = (L₂ ⋯ L_{d+1} · D)`.

## Main results

* `AlgebraicGeometry.Space.intersectionNumber_eq_sum_of_isEffectiveCartierDivisor`:
  **Stacks 0EDK**, with the right-hand side the intersection number of Definition 0EDF read for
  the closed subspace `D`, of dimension at most `d`.
* `AlgebraicGeometry.Space.intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor_of_dimension_eq`:
  the same with the right-hand side `AlgebraicGeometry.Space.intersectionNumber` of `D`, when
  `D` has dimension exactly `d`.
* `AlgebraicGeometry.Space.sum_eulerCharacteristic_eq_zero_of_dimension_lt`: the right-hand side
  vanishes when `D` has dimension less than `d`.

## Implementation notes

**The dimension of `D`.**  The source writes `(L₂ ⋯ L_{d+1} · D)` although `D` need not have
dimension exactly `d`: for `Z` the disjoint union of a plane and a line and `D` a point of the
line, `d + 1 = 2` and `dim D = 0`.  What it means is the coefficient of `n₂ ⋯ n_{d+1}` in the
numerical polynomial of `D`, that is the defining expression of Definition 0EDF for a closed
subspace of dimension at most `d`; `D` does have dimension at most `d`
(`AlgebraicGeometry.Space.dimension_le_of_isEffectiveCartierDivisor`, from Stacks 083T).
`AlgebraicGeometry.Space.intersectionNumber` asks for the dimension to be exactly `d`, so the
registered statement takes as its right-hand side the defining mixed finite difference

`∑_{T ⊆ {2, …, d + 1}} (-1)^{d - |T|} χ(X, j_*𝒪_D ⊗ ⨂_{l ∈ T} L_l)`,

which is `AlgebraicGeometry.Space.intersectionNumber` of `D` by
`AlgebraicGeometry.Space.intersectionNumber_eq_sum` whenever `dim D = d`, and which is `0` when
`dim D < d` by Stacks 0DN4.

**The proof** is the source's.  The twists of the divisor sequence
`0 ⟶ i_*𝒪_Z ⊗ L₁^{⊗ -1} ⟶ i_*𝒪_Z ⊗ L₁^{⊗ 0} ⟶ j_*𝒪_D ⟶ 0`
(`AlgebraicGeometry.Space.effectiveCartierDivisorShortComplex_shortExact`) by `L₂, …, L_{d+1}`
give, by additivity of the twisted Euler characteristics (Stacks 0DN2), the first-difference
relation `P(0, n) - P(-1, n) = Q(n)` between the numerical polynomial `P` of `Z` (Stacks 0DN4) and
the twisted Euler characteristics `Q` of `D`, and the degree bound on `P` makes the mixed finite
difference of the left-hand side the coefficient of `n₁ ⋯ n_{d+1}` in `P`
(`MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one`).

## References

* [Stacks Project, Tag 0EDK](https://stacks.math.columbia.edu/tag/0EDK)
* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 083T](https://stacks.math.columbia.edu/tag/083T)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X Z : AlgebraicSpaces B (Spec (.of k)) hk)

/-- The twisted Euler characteristics of `i_*𝒪_Z` along the exponent tuples `(0, 1_S)` and
`(-1, 1_S)` differ by those of `j_*𝒪_D` at `1_S`, when `L₁|_Z ≅ 𝒪_Z(D)`: additivity (Stacks 0DN2)
along the twist by `L₂, …, L_{d+1}` of the divisor sequence. -/
theorem eulerCharacteristic_sub_eq_of_isEffectiveCartierDivisor (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (Dv : ClosedSubspaces B (Spec (.of k)) hk Z.1)
    (hDv : IsEffectiveCartierDivisor B (Spec (.of k)) hk Z Dv)
    (L : Fin (d + 1) → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    (hL : (modulePullback B (Spec (.of k)) hk i).obj (L 0) ≅
      associatedInvertibleSheaf B (Spec (.of k)) hk Z Dv hDv)
    (n : Fin d → ℤ) :
    @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L (Fin.cons 0 n))
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi L _) -
      @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L (Fin.cons (-1) n))
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi L _) =
      @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk
            ((ObjectProperty.homMk Dv.1.ι :
              (⟨Dv.1.toFunctor, Dv.2.1⟩ : AlgebraicSpaces B (Spec (.of k)) hk) ⟶ Z) ≫ i))
          (fun j => L j.succ) n)
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X
          ⟨Dv.1.toFunctor, Dv.2.1⟩ f hf _
          (isClosedImmersion_comp B (Spec (.of k)) hk Dv.1.ι i.hom Dv.2.2 hi) _ _) := by
  have hfact : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf⟩
  have hE := effectiveCartierDivisorShortComplex_shortExact B (Spec (.of k)) hk i hi (L 0) Dv hDv
    hL
  have hM := isCoherent_structureSheafPushforward B (Spec (.of k)) hk hfact.out i hi
  have hT : ∀ a : ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) a
        (structureSheafPushforward B (Spec (.of k)) hk i)) := fun a =>
    let := isCoherentOnSite_twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) a _
      hM.toIsCoherentOnSite
    isCoherent_of_isCoherentOnSite B (Spec (.of k)) hk X.1 X.2 _
  have h₃ : IsCoherent B (Spec (.of k)) hk X.1 X.2
      (structureSheafPushforward B (Spec (.of k)) hk
        ((ObjectProperty.homMk Dv.1.ι :
          (⟨Dv.1.toFunctor, Dv.2.1⟩ : AlgebraicSpaces B (Spec (.of k)) hk) ⟶ Z) ≫ i)) :=
    isCoherent_structureSheafPushforward B (Spec (.of k)) hk hfact.out _
      (isClosedImmersion_comp B (Spec (.of k)) hk Dv.1.ι i.hom Dv.2.2 hi)
  have hadd := hasAdditiveTwistedEulerOnCoherent_of_isProper.{u, w} k B hk X f hf
    (fun j => L j.succ) _ hE (hT (-1)) (hT 0) h₃ n
  have e : ∀ a : ℤ, twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
      (structureSheafPushforward B (Spec (.of k)) hk i) L (Fin.cons a n) =
      twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) a
          (structureSheafPushforward B (Spec (.of k)) hk i)) (fun j => L j.succ) n := fun a =>
    congrArg (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w})
      (twistedModule_cons B (Spec (.of k)) hk _ L a n)
  have := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf (fun j => L j.succ)
    _ (hT (-1)) n
  have := isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf (fun j => L j.succ)
    _ (hT 0) n
  have := isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi L
    (Fin.cons 0 n)
  have := isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi L
    (Fin.cons (-1) n)
  rw [eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf (eqToIso (e 0)),
    eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf (eqToIso (e (-1)))]
  exact sub_eq_of_eq_add' hadd

/-- **Stacks 0EDK.**  Let `k` be a field, let `X` be a proper algebraic space over `k`, let
`i : Z ⟶ X` be a closed subspace of dimension `d + 1` and let `L₁, …, L_{d+1}` be invertible
`𝒪_X`-modules.  Let `D ⊆ Z` be an effective Cartier divisor with `L₁|_Z ≅ 𝒪_Z(D)`, and let
`j : D ⟶ X` be its inclusion into `X`.  Then

`(L₁ ⋯ L_{d+1} · Z) = (L₂ ⋯ L_{d+1} · D)`.

The right-hand side is written as the defining expression of Definition 0EDF,
`∑_{T ⊆ {2, …, d + 1}} (-1)^{d - |T|} χ(X, j_*𝒪_D ⊗ ⨂_{l ∈ T} L_l)`:

* (i) this is the intersection number of Definition 0EDF read for the closed subspace `D`, which
  has dimension at most `d` (`AlgebraicGeometry.Space.dimension_le_of_isEffectiveCartierDivisor`)
  but not necessarily exactly `d`;
* (ii) it is `AlgebraicGeometry.Space.intersectionNumber` of `D` by
  `AlgebraicGeometry.Space.intersectionNumber_eq_sum` whenever `dim D = d`, which is
  `intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor_of_dimension_eq`;
* (iii) it is `0` when `dim D < d`, by Stacks 0DN4, which is
  `AlgebraicGeometry.Space.sum_eulerCharacteristic_eq_zero_of_dimension_lt`.

No hypothesis beyond the source's is taken. -/
@[stacks 0EDK "the right-hand side as the defining sum of Definition 0EDF for D, of dimension \
at most d; it is intersectionNumber D when dim D = d and 0 when dim D < d"]
theorem intersectionNumber_eq_sum_of_isEffectiveCartierDivisor (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d + 1)
    (Dv : ClosedSubspaces B (Spec (.of k)) hk Z.1)
    (hDv : IsEffectiveCartierDivisor B (Spec (.of k)) hk Z Dv)
    (L : Fin (d + 1) → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    (hL : (modulePullback B (Spec (.of k)) hk i).obj (L 0) ≅
      associatedInvertibleSheaf B (Spec (.of k)) hk Z Dv hDv) :
    intersectionNumber.{u, w} k B hk X Z (d + 1) f hf i hi hd L =
      ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk
              ((ObjectProperty.homMk Dv.1.ι :
                (⟨Dv.1.toFunctor, Dv.2.1⟩ : AlgebraicSpaces B (Spec (.of k)) hk) ⟶ Z) ≫ i))
            (fun j => L j.succ) fun j => if j ∈ T then 1 else 0)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X
            ⟨Dv.1.toFunctor, Dv.2.1⟩ f hf _
            (isClosedImmersion_comp B (Spec (.of k)) hk Dv.1.ι i.hom Dv.2.2 hi) _ _) := by
  classical
  obtain ⟨P, hP, hPdeg⟩ := exists_representsTwistedEuler_structureSheafPushforward.{u, w}
    k B hk X Z (d + 1) f hf i hi hd L
  have hcast : ∀ (m : ℤ) (S : Finset (Fin d)),
      (fun j : Fin (d + 1) =>
          (((Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0 : Fin (d + 1) → ℤ) j : ℤ) : ℚ)) =
        (Fin.cons (m : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) := by
    intro m S
    refine funext fun j => ?_
    refine Fin.cases ?_ (fun l => ?_) j
    · simp
    · simp only [Fin.cons_succ]
      split_ifs <;> simp
  have hval : ∀ (m : ℤ) (S : Finset (Fin d)),
      MvPolynomial.eval
          (Fin.cons (m : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) P =
        ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L
            (Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0))
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi L
            _) : ℤ) : ℚ) := by
    intro m S
    have h := hP (Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0)
    rw [hcast m S] at h
    exact h
  have hZ := intersectionNumber_eq_coeff.{u, w} k B hk X Z (d + 1) f hf i hi hd L P hP hPdeg
  have hshift := MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one P hPdeg 0
  refine Int.cast_injective (α := ℚ) ?_
  rw [hZ, ← hshift]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← eulerCharacteristic_sub_eq_of_isEffectiveCartierDivisor.{u, w} k B hk X Z d f hf i hi Dv
    hDv L hL fun j => if j ∈ S then 1 else 0]
  rw [show (Fin.cons (0 : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) =
      (Fin.cons (((0 : ℤ) : ℚ)) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) by
    norm_num,
    show (Fin.cons ((0 : ℚ) - 1) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) =
      (Fin.cons (((-1 : ℤ) : ℚ)) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) by
    norm_num, hval 0 S, hval (-1) S]
  push_cast
  ring

/-- **Stacks 0EDK when `D` has dimension exactly `d`**: then the right-hand side of
`AlgebraicGeometry.Space.intersectionNumber_eq_sum_of_isEffectiveCartierDivisor` is the
intersection number `(L₂ ⋯ L_{d+1} · D)` of `AlgebraicGeometry.Space.intersectionNumber`. -/
theorem intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor_of_dimension_eq
    (d : ℕ) (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d + 1)
    (Dv : ClosedSubspaces B (Spec (.of k)) hk Z.1)
    (hDv : IsEffectiveCartierDivisor B (Spec (.of k)) hk Z Dv)
    (hdD : dimension B (Spec (.of k)) hk Dv.1.toFunctor Dv.2.1 = d)
    (L : Fin (d + 1) → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    (hL : (modulePullback B (Spec (.of k)) hk i).obj (L 0) ≅
      associatedInvertibleSheaf B (Spec (.of k)) hk Z Dv hDv) :
    intersectionNumber.{u, w} k B hk X Z (d + 1) f hf i hi hd L =
      intersectionNumber.{u, w} k B hk X ⟨Dv.1.toFunctor, Dv.2.1⟩ d f hf
        (ObjectProperty.homMk Dv.1.ι ≫ i)
        (isClosedImmersion_comp B (Spec (.of k)) hk Dv.1.ι i.hom Dv.2.2 hi) hdD
        fun j => L j.succ := by
  rw [intersectionNumber_eq_sum_of_isEffectiveCartierDivisor.{u, w} k B hk X Z d f hf i hi hd Dv
    hDv L hL, intersectionNumber_eq_sum]

/-- **The right-hand side of Stacks 0EDK vanishes below the expected dimension.**  If the closed
subspace `j : D ⟶ X` has dimension less than `d`, the mixed finite difference
`∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} χ(X, j_*𝒪_D ⊗ ⨂_{l ∈ T} L_l)` of Definition 0EDF is `0`: by
Stacks 0DN4 the twisted Euler characteristics of `j_*𝒪_D` are a polynomial of total degree at most
`dim D < d`, whose coefficient of `n₁ ⋯ n_d` vanishes. -/
theorem sum_eulerCharacteristic_eq_zero_of_dimension_lt (D : AlgebraicSpaces B (Spec (.of k)) hk)
    (d : ℕ) (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (j : D ⟶ X) (hj : IsClosedImmersion B (Spec (.of k)) hk j.hom)
    (hdD : dimension B (Spec (.of k)) hk D.1 D.2 < d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ l, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L l)] :
    ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk j) L fun l => if l ∈ T then 1 else 0)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X D f hf j hj L
            _) = 0 := by
  classical
  obtain ⟨P, hP, hPdeg⟩ := exists_representsTwistedEuler_structureSheafPushforward_withBot.{u, w}
    k B hk X D f hf j hj L
  have hval : ∀ T : Finset (Fin d),
      MvPolynomial.eval (fun l => if l ∈ T then (1 : ℚ) else 0) P =
        ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk j) L
            fun l => if l ∈ T then 1 else 0)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X D f hf j hj L
            _) : ℤ) : ℚ) := by
    intro T
    have h := hP fun l => if l ∈ T then (1 : ℤ) else 0
    rw [show (fun l : Fin d => (((if l ∈ T then (1 : ℤ) else 0) : ℤ) : ℚ)) =
        fun l : Fin d => if l ∈ T then (1 : ℚ) else 0 from
      funext fun l => by split_ifs <;> simp] at h
    exact h
  have hcoeff : P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = 0 := by
    rcases hPdeg with rfl | hPdeg
    · rfl
    refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
    have hsupp : (Finsupp.equivFunOnFinite.symm fun _ : Fin d => (1 : ℕ)).support =
        Finset.univ := by
      ext l
      simp
    rw [hsupp]
    have hlt : (P.totalDegree : WithBot ℕ∞) < d := hPdeg.trans_lt hdD
    simpa using (by exact_mod_cast hlt : P.totalDegree < d)
  have hle : P.totalDegree ≤ d := by
    rcases hPdeg with rfl | hPdeg
    · simp
    · exact (by exact_mod_cast (hPdeg.trans_lt hdD).le : P.totalDegree ≤ d)
  have hsum := MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one P hle
  refine Int.cast_injective (α := ℚ) ?_
  push_cast
  rw [← hcoeff, ← hsum]
  exact Finset.sum_congr rfl fun T _ => by rw [hval T]

end AlgebraicGeometry.Space

end
