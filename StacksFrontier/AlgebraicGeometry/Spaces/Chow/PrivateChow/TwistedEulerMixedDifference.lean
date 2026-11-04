module

public import StacksFrontier.AlgebraicGeometry.Spaces.EulerCharacteristicAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerTopDimensionalComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The mixed finite difference of twisted Euler characteristics of a coherent module

Let `X` be proper over a field, `F` a coherent `𝒪_X`-module and `L₁, …, L_d` invertible modules.
The *mixed finite difference*

`Δ(F; L) = ∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} χ(X, F ⊗ ⨂_{j ∈ T} L_j)`

is the coefficient of `n₁ ⋯ n_d` of the numerical polynomial of `F` whenever that polynomial has
total degree at most `d`, and the intersection number `(L₁ ⋯ L_d · Z)` of a closed subspace
`i : Z ⟶ X` is `Δ(i_*𝒪_Z; L)` by definition. It is additive along short exact sequences and
invariant under isomorphism, and for `L = (N, M)` and `F = i_*𝒪_Z` the intersection number is the
first difference `Δ(F ⊗ N; M) - Δ(F; M)`.

## Main definitions

* `AlgebraicGeometry.Space.twistedEulerMixedDifference`.

## Main results

* `AlgebraicGeometry.Space.intersectionNumber_eq_twistedEulerMixedDifference`.
* `AlgebraicGeometry.Space.twistedEulerMixedDifference_of_shortExact`.
* `AlgebraicGeometry.Space.twistedEulerMixedDifference_congr`.
* `AlgebraicGeometry.Space.intersectionNumber_eq_sub_twistedEulerMixedDifference_twistStep`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)

/-- **The mixed finite difference of the twisted Euler characteristics** of a coherent module
`F` along `L₁, …, L_d`: `∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} χ(X, F ⊗ ⨂_{j ∈ T} L_j)`. -/
def twistedEulerMixedDifference {d : ℕ} (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] : ℤ :=
  ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
    @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L fun j => if j ∈ T then 1 else 0)
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF _)

variable {d : ℕ} (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]

/-- The intersection number of a closed subspace is the mixed difference of `i_*𝒪_Z`. -/
theorem intersectionNumber_eq_twistedEulerMixedDifference (Z : AlgebraicSpaces B (Spec (.of k)) hk)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d) :
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      twistedEulerMixedDifference.{u, w} k B hk X f hf
        (structureSheafPushforward B (Spec (.of k)) hk i)
        (isCoherent_structureSheafPushforward B (Spec (.of k)) hk
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) i hi) L :=
  rfl

/-- The mixed difference is additive along short exact sequences of coherent modules. -/
theorem twistedEulerMixedDifference_of_shortExact
    {E : ShortComplex (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)} (hE : E.ShortExact)
    (h₁ : IsCoherent B (Spec (.of k)) hk X.1 X.2 E.X₁)
    (h₂ : IsCoherent B (Spec (.of k)) hk X.1 X.2 E.X₂)
    (h₃ : IsCoherent B (Spec (.of k)) hk X.1 X.2 E.X₃) :
    twistedEulerMixedDifference.{u, w} k B hk X f hf E.X₂ h₂ L =
      twistedEulerMixedDifference.{u, w} k B hk X f hf E.X₁ h₁ L +
        twistedEulerMixedDifference.{u, w} k B hk X f hf E.X₃ h₃ L := by
  unfold twistedEulerMixedDifference
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [hasAdditiveTwistedEulerOnCoherent_of_isProper.{u, w} k B hk X f hf L E hE h₁ h₂ h₃, mul_add]

/-- The mixed difference only depends on the module up to isomorphism. -/
theorem twistedEulerMixedDifference_congr {F G : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2}
    (e : F ≅ G) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (hG : IsCoherent B (Spec (.of k)) hk X.1 X.2 G) :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L =
      twistedEulerMixedDifference.{u, w} k B hk X f hf G hG L := by
  unfold twistedEulerMixedDifference
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  exact @eulerCharacteristic_congr.{u, w} k _ B hk X.1 X.2 f hf _ _
    (twistedModuleUliftIsoOfIso.{u, w} B (Spec (.of k)) hk X.1 X.2 F L _ L _ (Iso.refl _) ≪≫
      uliftForPresentationMapIso.{u, w} B (Spec (.of k)) hk X.1 X.2
        (foldlTwistStepIso B (Spec (.of k)) hk X.1 X.2 L _ (List.finRange d) e))
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF _)
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L G hG _)

omit [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] in
include hf in
/-- A twisting step of a coherent module is coherent. -/
theorem isCoherent_twistStep_of_isProper (N : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property N]
    (a : ℤ) (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F) :
    IsCoherent B (Spec (.of k)) hk X.1 X.2 (twistStep B (Spec (.of k)) hk X.1 X.2 N a F) :=
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf⟩
  let := isCoherentOnSite_twistStep B (Spec (.of k)) hk X.1 X.2 N a _ hF.toIsCoherentOnSite
  isCoherent_of_isCoherentOnSite B (Spec (.of k)) hk X.1 X.2 _


/-- The first difference of mixed differences in the first module is the top coefficient of any
polynomial of total degree at most `d + 1` interpolating the twisted Euler characteristics. -/
private theorem cast_twistedEulerMixedDifference_sub_twistStep_eq_coeff
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (L : Fin (d + 1) → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (P : MvPolynomial (Fin (d + 1)) ℚ)
    (hP : ∀ n : Fin (d + 1) → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF n) : ℤ) : ℚ))
    (hPdeg : P.totalDegree ≤ d + 1) :
    ((twistedEulerMixedDifference.{u, w} k B hk X f hf
          (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) 1 F)
          (isCoherent_twistStep_of_isProper k B hk X f hf (L 0) 1 _ hF) (fun j => L j.succ) -
        twistedEulerMixedDifference.{u, w} k B hk X f hf
          (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) 0 F)
          (isCoherent_twistStep_of_isProper k B hk X f hf (L 0) 0 _ hF) (fun j => L j.succ) : ℤ) :
        ℚ) = P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  classical
  have hcast : ∀ (m : ℤ) (S : Finset (Fin d)),
      (fun j : Fin (d + 1) =>
          (((Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0 : Fin (d + 1) → ℤ) j : ℤ) : ℚ)) =
        (Fin.cons (m : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) := by
    intro m S
    refine funext fun j => Fin.cases ?_ (fun l => ?_) j
    · simp
    · simp only [Fin.cons_succ]
      split_ifs <;> simp
  have hval : ∀ (m : ℤ) (S : Finset (Fin d)),
      MvPolynomial.eval
          (Fin.cons (m : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) P =
        ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) m F) (fun j => L j.succ)
            (fun l => if l ∈ S then (1 : ℤ) else 0))
          (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf _ _
            (isCoherent_twistStep_of_isProper k B hk X f hf (L 0) m _ hF) _) : ℤ) : ℚ) := by
    intro m S
    have h := hP (Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0)
    rw [hcast m S] at h
    rw [h]
    congr 1
    exact @eulerCharacteristic_congr.{u, w} k _ B hk X.1 X.2 f hf _ _
      (eqToIso (congrArg (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w})
        (twistedModule_cons B (Spec (.of k)) hk _ L m _)))
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF _)
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf _ _
        (isCoherent_twistStep_of_isProper k B hk X f hf (L 0) m _ hF) _)
  have hshift := MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one P hPdeg 1
  rw [← hshift]
  unfold twistedEulerMixedDifference
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [show (Fin.cons (1 : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) =
      (Fin.cons (((1 : ℤ) : ℚ)) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) by
    norm_num,
    show (Fin.cons ((1 : ℚ) - 1) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) =
      (Fin.cons (((0 : ℤ) : ℚ)) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) by
    norm_num, hval 1 S, hval 0 S]
  ring

omit [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] in
/-- **The intersection number as a first difference in the first module.** For a closed
subspace `i : Z ⟶ X` of dimension `d + 1` and `L₀, L₁, …, L_d`,
`(L₀ L₁ ⋯ L_d · Z) = Δ(i_*𝒪_Z ⊗ L₀; L₁, …, L_d) - Δ(i_*𝒪_Z; L₁, …, L_d)`, both sides read with
the twisting steps at exponents `1` and `0`. -/
theorem intersectionNumber_eq_sub_twistedEulerMixedDifference_twistStep
    (Z : AlgebraicSpaces B (Spec (.of k)) hk) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d + 1)
    (L : Fin (d + 1) → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    have hM := isCoherent_structureSheafPushforward B (Spec (.of k)) hk
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) i hi
    intersectionNumber.{u, w} k B hk X Z (d + 1) f hf i hi hd L =
      twistedEulerMixedDifference.{u, w} k B hk X f hf
          (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) 1
            (structureSheafPushforward B (Spec (.of k)) hk i))
          (isCoherent_twistStep_of_isProper k B hk X f hf (L 0) 1 _ hM) (fun j => L j.succ) -
        twistedEulerMixedDifference.{u, w} k B hk X f hf
          (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) 0
            (structureSheafPushforward B (Spec (.of k)) hk i))
          (isCoherent_twistStep_of_isProper k B hk X f hf (L 0) 0 _ hM) (fun j => L j.succ) := by
  classical
  intro hM
  obtain ⟨P, hP, hPdeg⟩ := exists_representsTwistedEuler_structureSheafPushforward.{u, w}
    k B hk X Z (d + 1) f hf i hi hd L
  have hZ := intersectionNumber_eq_coeff.{u, w} k B hk X Z (d + 1) f hf i hi hd L P hP hPdeg
  exact Int.cast_injective (α := ℚ) (hZ.trans
    (cast_twistedEulerMixedDifference_sub_twistStep_eq_coeff.{u, w} k B hk X f hf _ hM L P hP
      hPdeg).symm)

/-- **The mixed difference is additive along a decomposition up to lower degree.** If
`χ(F ⊗ L^n) - ∑_j m_j χ(G_j ⊗ L^n)` is a polynomial of total degree `< d`, then
`Δ(F; L) = ∑_j m_j Δ(G_j; L)`. -/
theorem twistedEulerMixedDifference_eq_finsum_of_eval {ι : Type*} [Finite ι]
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (G : ι → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hG : ∀ j, IsCoherent B (Spec (.of k)) hk X.1 X.2 (G j)) (m : ι → ℤ)
    (P : MvPolynomial (Fin d) ℚ) (hPdeg : P = 0 ∨ P.totalDegree < d)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF n) : ℤ) : ℚ) -
        ∑ᶠ j, (m j : ℚ) * ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 (G j) L n)
          (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L (G j) (hG j) n) :
            ℤ) : ℚ)) :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L =
      ∑ᶠ j, m j * twistedEulerMixedDifference.{u, w} k B hk X f hf (G j) (hG j) L := by
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
  rw [finsum_eq_sum_of_fintype]
  unfold twistedEulerMixedDifference
  push_cast
  rw [← sub_eq_zero, ← hzero]
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S _ => ?_
  ring

attribute [local instance] pointTopology

/-- **Stacks 0EDE read on the mixed difference.** Let `F` be coherent with support inside a
closed set `T ⊆ |X|` of dimension `d`, and `x̄_C` a geometric generic point of each irreducible
component `C` of `T`. Then `Δ(F; L₁, …, L_d) = ∑_C length_{x̄_C}(F) (L₁ ⋯ L_d · Z_C)`, the sum
over the components of dimension `d`, `Z_C` the reduced closed subspace on `C`. -/
theorem twistedEulerMixedDifference_eq_finsum_components
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    {T : Set (points B (Spec (.of k)) hk X.1)} (hT : IsClosed T) (hTd : topologicalKrullDim T = d)
    (x : irreducibleComponents T → GeometricPoint B (Spec (.of k)) hk X.1)
    (hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set T)))
    (hFT : moduleSupportSet B (Spec (.of k)) hk X F ⊆ T) :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L =
      ∑ᶠ (C : {C : irreducibleComponents T //
          topologicalKrullDim (Subtype.val '' (C : Set T)) = d}),
        ((geometricLength B (Spec (.of k)) hk X (x C.1) F).toNat : ℤ) *
          intersectionNumber.{u, w} k B hk X
            (closedSubfunctorSpace B (Spec (.of k)) hk
              (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed)) d f hf
            (closedSubfunctorι B (Spec (.of k)) hk
              (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed))
            (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
              (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed).2
            ((dimension_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2
              (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) _ _).trans C.2) L := by
  have := noetherianSpace_points_of_isProper_baseObject k B hk X.1 X.2 f hf
  have : Finite (irreducibleComponents T) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  obtain ⟨P, hPdeg, hP⟩ := exists_twistedEuler_sub_finsum_mul_componentStructureSheaf.{u, w}
    k B hk X f hf L hT x hx F hF hFT
  have hPdeg' : P = 0 ∨ P.totalDegree < d := hPdeg.imp_right fun h => by
    rw [hTd] at h
    exact_mod_cast h
  rw [twistedEulerMixedDifference_eq_finsum_of_eval.{u, w} k B hk X f hf L F hF
    (ι := {C : irreducibleComponents T // topologicalKrullDim (Subtype.val '' (C : Set T)) = d})
    (fun C => componentStructureSheaf B (Spec (.of k)) hk X hT C.1)
    (fun C => isCoherent_componentStructureSheaf k B hk X f hf hT C.1)
    (fun C => ((geometricLength B (Spec (.of k)) hk X (x C.1) F).toNat : ℤ)) P hPdeg' ?_]
  · rfl
  · intro n
    rw [hP n]
    congr 1
    simp only [Set.mem_ofPred_eq, hTd]
    rw [← finsum_subtype_eq_finsum_cond]
    push_cast
    rfl

/-- **The mixed difference vanishes below the expected dimension**: if the support of `F` has
dimension `< d`, then `Δ(F; L₁, …, L_d) = 0`, by Stacks 0DN4. -/
theorem twistedEulerMixedDifference_eq_zero_of_lt
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (h : topologicalKrullDim (moduleSupportSet B (Spec (.of k)) hk X F) < d) :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L = 0 := by
  obtain ⟨P, hP, hPdeg⟩ := exists_representsTwistedEuler_of_isCoherent.{u, w} k B hk X f hf L F hF
  have hPdeg' : P = 0 ∨ P.totalDegree < d :=
    hPdeg.imp_right fun h' => by exact_mod_cast h'.trans_lt h
  rw [twistedEulerMixedDifference_eq_finsum_of_eval.{u, w} k B hk X f hf L F hF
    (ι := Empty) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) P hPdeg' ?_]
  · exact finsum_of_isEmpty _
  · intro n
    rw [hP n, finsum_of_isEmpty, sub_zero]

omit [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] in
/-- **The mixed difference as a first difference in the first module.** For a coherent `F` whose
support has dimension at most `d + 1`,
`Δ(F; L₀, L₁, …, L_d) = Δ(F ⊗ L₀; L₁, …, L_d) - Δ(F; L₁, …, L_d)`, the two terms read with the
twisting steps at exponents `1` and `0`. -/
theorem twistedEulerMixedDifference_eq_sub_twistStep
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (hdim : topologicalKrullDim (moduleSupportSet B (Spec (.of k)) hk X F) ≤ d + 1)
    (L : Fin (d + 1) → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L =
      twistedEulerMixedDifference.{u, w} k B hk X f hf
          (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) 1 F)
          (isCoherent_twistStep_of_isProper k B hk X f hf (L 0) 1 _ hF) (fun j => L j.succ) -
        twistedEulerMixedDifference.{u, w} k B hk X f hf
          (twistStep B (Spec (.of k)) hk X.1 X.2 (L 0) 0 F)
          (isCoherent_twistStep_of_isProper k B hk X f hf (L 0) 0 _ hF) (fun j => L j.succ) := by
  classical
  obtain ⟨P, hP, hPdeg⟩ := exists_representsTwistedEuler_of_isCoherent.{u, w} k B hk X f hf L F hF
  have hPdeg' : P.totalDegree ≤ d + 1 := by
    rcases hPdeg with h | h
    · simp [h]
    · exact_mod_cast h.trans hdim
  have hsum := MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one P hPdeg'
  have hP' : ∀ T : Finset (Fin (d + 1)),
      MvPolynomial.eval (fun j => if j ∈ T then (1 : ℚ) else 0) P =
        ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L
            fun j => if j ∈ T then 1 else 0)
          (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF _) : ℤ) : ℚ) := by
    intro T
    have h := hP fun j => if j ∈ T then (1 : ℤ) else 0
    rwa [show (fun j : Fin (d + 1) => (((if j ∈ T then (1 : ℤ) else 0) : ℤ) : ℚ)) =
        fun j : Fin (d + 1) => if j ∈ T then (1 : ℚ) else 0 from
      funext fun j => by split_ifs <;> simp] at h
  refine Int.cast_injective (α := ℚ) ?_
  have hlhs : ((twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L : ℤ) : ℚ) =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
    rw [← hsum]
    unfold twistedEulerMixedDifference
    push_cast
    exact Finset.sum_congr rfl fun T _ => by rw [hP' T]
  rw [hlhs]
  exact (cast_twistedEulerMixedDifference_sub_twistStep_eq_coeff.{u, w} k B hk X f hf F hF L P hP
    hPdeg').symm


omit [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] in
/-- `AlgebraicGeometry.Space.twistedEulerMixedDifference_eq_sub_twistStep` for a family
`Fin.cons N M`. -/
theorem twistedEulerMixedDifference_cons_eq_sub_twistStep
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (hdim : topologicalKrullDim (moduleSupportSet B (Spec (.of k)) hk X F) ≤ d + 1)
    (N : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property N]
    (M : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (M j)] :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF (Fin.cons N M) =
      twistedEulerMixedDifference.{u, w} k B hk X f hf
          (twistStep B (Spec (.of k)) hk X.1 X.2 N 1 F)
          (isCoherent_twistStep_of_isProper k B hk X f hf N 1 _ hF) M -
        twistedEulerMixedDifference.{u, w} k B hk X f hf
          (twistStep B (Spec (.of k)) hk X.1 X.2 N 0 F)
          (isCoherent_twistStep_of_isProper k B hk X f hf N 0 _ hF) M :=
  twistedEulerMixedDifference_eq_sub_twistStep.{u, w} k B hk X f hf F hF hdim (Fin.cons N M)

omit [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] in
/-- Appending an invertible module to a family of invertible modules: every member of
`Fin.snoc M N` is invertible. -/
instance isInvertible_snoc (N : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property N]
    (M : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (M j)]
    (p : Fin (d + 1)) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property
      ((Fin.snoc M N : Fin (d + 1) → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) p) := by
  induction p using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    infer_instance
  | cast j =>
    rw [Fin.snoc_castSucc]
    infer_instance

omit [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] in
/-- Twisting by `Fin.snoc M N` is twisting by `M` and then by `N`. -/
theorem twistedModule_snoc (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (N : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property N]
    (M : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (M j)]
    (a : ℤ) (n : Fin d → ℤ) :
    twistedModule B (Spec (.of k)) hk X.1 X.2 F (Fin.snoc M N) (Fin.snoc n a) =
      twistStep B (Spec (.of k)) hk X.1 X.2 N a
        (twistedModule B (Spec (.of k)) hk X.1 X.2 F M n) := by
  rw [twistedModule, List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.foldl_cons, List.foldl_nil]
  rfl

omit [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] in
/-- Twisting by `Fin.snoc M N` and by `Fin.cons N M` agree up to isomorphism. -/
def twistedModuleSnocIsoCons (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (N : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property N]
    (M : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (M j)]
    (a : ℤ) (n : Fin d → ℤ) :
    twistedModule B (Spec (.of k)) hk X.1 X.2 F (Fin.snoc M N) (Fin.snoc n a) ≅
      twistedModule B (Spec (.of k)) hk X.1 X.2 F (Fin.cons N M) (Fin.cons a n) :=
  eqToIso (twistedModule_snoc k B hk X F N M a n) ≪≫
    foldlTwistStepCommIso B (Spec (.of k)) hk X.1 X.2 N a M n (List.finRange d) F ≪≫
    eqToIso (twistedModule_cons B (Spec (.of k)) hk F (Fin.cons N M) a n).symm

omit [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] in
/-- **The mixed difference is unchanged by moving the last module to the front.** -/
theorem twistedEulerMixedDifference_snoc_eq_cons
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (N : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property N]
    (M : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (M j)] :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF (Fin.snoc M N) =
      twistedEulerMixedDifference.{u, w} k B hk X f hf F hF (Fin.cons N M) := by
  classical
  unfold twistedEulerMixedDifference
  let σ := finRotate (d + 1)
  have h0 : σ (Fin.last d) = 0 := finRotate_last
  have hs : ∀ i : Fin d, σ (Fin.castSucc i) = i.succ := fun i => by
    rw [finRotate_apply]
    exact Fin.coeSucc_eq_succ
  have hind : ∀ T : Finset (Fin (d + 1)),
      (Fin.cons ((fun j => if j ∈ T then (1 : ℤ) else 0) (Fin.last d))
          (fun i => (fun j => if j ∈ T then (1 : ℤ) else 0) (Fin.castSucc i)) :
          Fin (d + 1) → ℤ) =
        fun j => if j ∈ T.map σ.toEmbedding then 1 else 0 := by
    intro T
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [← h0, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      rw [h0, Fin.cons_zero]
    · simp only [← hs i, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      rw [hs i, Fin.cons_succ]
  have hterm : ∀ T : Finset (Fin (d + 1)),
      @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F (Fin.snoc M N)
          fun j => if j ∈ T then 1 else 0)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf _ F hF _) =
      @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F (Fin.cons N M)
          fun j => if j ∈ T.map σ.toEmbedding then 1 else 0)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf _ F hF _) := by
    intro T
    refine @eulerCharacteristic_congr.{u, w} k _ B hk X.1 X.2 f hf _ _ ?_
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf _ F hF _)
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf _ F hF _)
    refine uliftForPresentationMapIso.{u, w} B (Spec (.of k)) hk X.1 X.2 ?_
    refine eqToIso ?_ ≪≫ twistedModuleSnocIsoCons k B hk X F N M
      ((fun j => if j ∈ T then (1 : ℤ) else 0) (Fin.last d))
      (fun i => (fun j => if j ∈ T then (1 : ℤ) else 0) (Fin.castSucc i)) ≪≫ eqToIso ?_
    · exact congrArg _ (Fin.snoc_init_self _).symm
    · exact congrArg _ (hind T)
  simp_rw [hterm]
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun T => ?_
  simp [Equiv.finsetCongr_apply]

/-- **The intersection number of a closed subspace, read on the closed subspace.**
`(L₁ ⋯ L_d · Z)` computed on `X` is the mixed difference on `Z` of `𝒪_Z` along the inverse images
`L_j|_Z`: the direct image along a closed immersion does not change twisted Euler characteristics
(`eulerCharacteristic_twistedModuleUlift_modulePushforward_of_isClosedImmersion`). -/
theorem intersectionNumber_eq_twistedEulerMixedDifference_closedSubspace
    (Z : AlgebraicSpaces B (Spec (.of k)) hk) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d) :
    have hfZ : IsProper B (Spec (.of k)) hk (i.hom ≫ f) :=
      isProper_comp B (Spec (.of k)) hk Z.2 X.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom f
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk Z.2 X.2 i.hom hi) hf
    haveI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L j)
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      twistedEulerMixedDifference.{u, w} k B hk Z (i.hom ≫ f) hfZ
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk Z.1 Z.2).O))
        (isCoherent_unit_of_isClosedImmersion k B hk X Z f hf i hi)
        (fun j => (modulePullback B (Spec (.of k)) hk i).obj (L j)) := by
  intro hfZ
  rw [intersectionNumber_eq_twistedEulerMixedDifference]
  unfold twistedEulerMixedDifference
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  exact eulerCharacteristic_twistedModuleUlift_modulePushforward_of_isClosedImmersion.{u, w}
    k B hk f hf i hi _ (isCoherent_unit_of_isClosedImmersion k B hk X Z f hf i hi) L _

/-- The mixed difference depends on the family of invertible modules only up to isomorphism. -/
theorem twistedEulerMixedDifference_congr_family
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    {L' : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2}
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L' j)]
    (e : ∀ j, L j ≅ L' j) :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L =
      twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L' := by
  unfold twistedEulerMixedDifference
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  exact @eulerCharacteristic_congr.{u, w} k _ B hk X.1 X.2 f hf _ _
    (uliftForPresentationMapIso.{u, w} B (Spec (.of k)) hk X.1 X.2
      (twistedModuleCongrIndicatorIso B (Spec (.of k)) hk X e T F))
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF _)
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L' F hF _)

/-- **Intersection numbers of a closed subspace of a closed subspace.** For closed immersions
`j : W' ⟶ W` and `i : W ⟶ X`, `(L₁ ⋯ L_d · W')` computed on `X` is `(L₁|_W ⋯ L_d|_W · W')`
computed on `W`. -/
theorem intersectionNumber_comp_eq (W W' : AlgebraicSpaces B (Spec (.of k)) hk) (i : W ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom) (j : W' ⟶ W)
    (hj : IsClosedImmersion B (Spec (.of k)) hk j.hom)
    (hd : dimension B (Spec (.of k)) hk W'.1 W'.2 = d) :
    have hfW : IsProper B (Spec (.of k)) hk (i.hom ≫ f) :=
      isProper_comp B (Spec (.of k)) hk W.2 X.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom f
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk W.2 X.2 i.hom hi) hf
    haveI := fun l => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L l)
    intersectionNumber.{u, w} k B hk X W' d f hf (j ≫ i)
        (isClosedImmersion_comp B (Spec (.of k)) hk j.hom i.hom hj hi) hd L =
      intersectionNumber.{u, w} k B hk W W' d (i.hom ≫ f) hfW j hj hd
        (fun l => (modulePullback B (Spec (.of k)) hk i).obj (L l)) := by
  intro hfW
  have := fun l => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L l)
  rw [intersectionNumber_eq_twistedEulerMixedDifference_closedSubspace,
    intersectionNumber_eq_twistedEulerMixedDifference_closedSubspace]
  have := fun l => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk (j ≫ i) (L l)
  have : ∀ l, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk W'.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk W'.1 W'.2).O).property
      ((modulePullback B (Spec (.of k)) hk i ⋙ modulePullback B (Spec (.of k)) hk j).obj (L l)) :=
    fun l => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk j
      ((modulePullback B (Spec (.of k)) hk i).obj (L l))
  exact (twistedEulerMixedDifference_congr_family.{u, w} k B hk W' _ _ _ _ _
    (fun l => (modulePullbackCompIso B (Spec (.of k)) hk j i).app (L l))).symm

end AlgebraicGeometry.Space

end
