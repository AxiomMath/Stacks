module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.UnionOfClosedSubschemes
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion

/-!
# The exact sequence of Chow groups of a closed cover

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, and let `I` and `J` be two ideal sheaves on `X` cutting out
closed subschemes `X₁` and `X₂` which cover `X` set-theoretically. Their scheme-theoretic
intersection `X₁ ∩ X₂` is cut out by `I ⊔ J`, and Stacks 0F94 says that for every `k` the
sequence of abelian groups

  `A_k(X₁ ∩ X₂) → A_k(X₁) ⊕ A_k(X₂) → A_k(X) → 0`

is exact. The first map is the pair of pushforwards with the second one negated, the second map
is the sum of the two pushforwards; all four pushforwards are along the inclusion of a closed
subscheme, `Stacks.Chow.chowPushforwardOfIsClosedImmersion`.

## Main definitions

* `Stacks.Chow.intersectionToSummandsChow` — the pair of pushforwards on Chow groups from the
  scheme-theoretic intersection, the second one negated.
* `Stacks.Chow.summandsToUnionChow` — the sum of the pushforwards on Chow groups from the two
  closed subschemes.

## Main results

* `Stacks.Chow.exact_intersectionToSummandsChow_summandsToUnionChow` — exactness in the middle.
* `Stacks.Chow.surjective_summandsToUnionChow` — exactness at `A_k(X)`.
* `Stacks.Chow.exists_rationallyEquivalentToZero_summandsToUnion` — the decomposition of a
  rational equivalence along a cover by two closed subschemes.
* `Stacks.Chow.exists_idealSheafData_of_support_subset` — an integral closed subscheme of `X`
  contained in `X₁` is an integral closed subscheme of `X₁`, with the same support, the same
  delta-dimension, and matching principal divisors.

## References

* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
* [Stacks Project, Tag 0F92](https://stacks.math.columbia.edu/tag/0F92)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

open Scheme.IdealSheafData (inclusion inclusion_subschemeι inclusion_subschemeι_assoc)

universe u

namespace Stacks.Chow

/-! ### Integral closed subschemes of a closed subscheme -/

/-- An integral closed subscheme of `X` is contained in one of two closed subschemes covering `X`
set-theoretically. -/
theorem support_subset_left_or_right_of_isIntegral {X : Scheme.{u}} (I J W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) (hcover : I.support ⊔ J.support = ⊤) :
    (W.support : Set X) ⊆ (I.support : Set X) ∨ (W.support : Set X) ⊆ (J.support : Set X) := by
  have hx : genericPointOf W hW ∈ (I.support : Set X) ∪ (J.support : Set X) := by
    rw [← Closeds.coe_sup, hcover]
    exact Set.mem_univ _
  rw [support_eq_closure_genericPointOf W hW]
  exact hx.imp (fun h ↦ closure_minimal (Set.singleton_subset_iff.mpr h) I.support.isClosed)
    fun h ↦ closure_minimal (Set.singleton_subset_iff.mpr h) J.support.isClosed

/-! ### Transporting cycles along a closed immersion and along an isomorphism -/

variable (C : ChowSituation.{u})

/-- Along a closed immersion over the base, the weighted pushforward of cycles carries the
coefficient of a cycle at a point to its coefficient at the image of that point. -/
theorem algebraicCycle_map_relativeDimension_apply_image {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : i ≫ sX = sZ) (c : AlgebraicCycle Z ℤ) (z : Z) :
    AlgebraicCycle.map i (relativeDimension C.dimensionFunction sZ)
        (relativeDimension C.dimensionFunction sX) c (i.base z) = c z := by
  have hfibre : i.base ⁻¹' {i.base z} = {z} := by
    ext w
    simp [i.isClosedEmbedding.injective.eq_iff]
  have hdim : relativeDimension C.dimensionFunction sZ z =
      relativeDimension C.dimensionFunction sX (i.base z) := by
    rw [← hi, relativeDimension_comp_closedImmersion]
  have hweight : (AlgebraicCycle.mapCoeff i (relativeDimension C.dimensionFunction sZ)
      (relativeDimension C.dimensionFunction sX) z : ℤ) = 1 := by
    simp [AlgebraicCycle.mapCoeff, hdim, residueDegree_eq_one_of_isClosedImmersion]
  show (∑ᶠ w ∈ i.base ⁻¹' {i.base z}, c w *
    (AlgebraicCycle.mapCoeff i (relativeDimension C.dimensionFunction sZ)
      (relativeDimension C.dimensionFunction sX) w : ℤ)) = c z
  rw [hfibre, finsum_mem_singleton, hweight, mul_one]

/-- The pushforward along a proper morphism `q : Z ⟶ X` over the base of the principal divisor of a
nonzero rational function on an integral closed subscheme `T ⊆ Z` is the principal divisor of the
transported rational function on an integral closed subscheme `W ⊆ X`, as soon as `q` restricts to
an isomorphism `T ≅ W`. -/
theorem map_principalDivisorPushforward_of_iso {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (q : Z ⟶ X) [IsProper q]
    (hq : q ≫ sX = sZ) (T : Z.IdealSheafData) (W : X.IdealSheafData)
    [hT : IsIntegral T.subscheme] [hW : IsIntegral W.subscheme] (φ : T.subscheme ≅ W.subscheme)
    (hφ : φ.hom ≫ W.subschemeι = T.subschemeι ≫ q) (g : (rationalFunctions T.subscheme)ˣ) :
    AlgebraicCycle.map q (relativeDimension C.dimensionFunction sZ)
        (relativeDimension C.dimensionFunction sX)
        (principalDivisorPushforward C sZ T hT g) =
      principalDivisorPushforward C sX W hW (rationalFunctionsUnitsMulEquivOfIso φ g) := by
  have _ : IsLocallyNoetherian T.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (T.subschemeι ≫ sZ)
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sX)
  have hφs : φ.hom ≫ (W.subschemeι ≫ sX) = T.subschemeι ≫ sZ := by
    rw [← Category.assoc, hφ, Category.assoc, hq]
  have hw : ∀ z : T.subscheme, relativeDimension C.dimensionFunction (T.subschemeι ≫ sZ) z =
      relativeDimension C.dimensionFunction (W.subschemeι ≫ sX) (φ.hom.base z) := fun z ↦
    (relativeDimension_of_iso C.dimensionFunction (T.subschemeι ≫ sZ) (W.subschemeι ≫ sX) φ
      hφs z).symm
  calc AlgebraicCycle.map q (relativeDimension C.dimensionFunction sZ)
        (relativeDimension C.dimensionFunction sX)
        (principalDivisorPushforward C sZ T hT g)
      = AlgebraicCycle.map (T.subschemeι ≫ q)
          (relativeDimension C.dimensionFunction (T.subschemeι ≫ sZ))
          (relativeDimension C.dimensionFunction sX)
          (principalCycle T.subscheme ((rationalFunctionsEquivFunctionField T.subscheme).1
            (g : rationalFunctions T.subscheme))) :=
        algebraicCycle_map_comp_relativeDimension C (T.subschemeι ≫ sZ) sZ sX T.subschemeι q
          rfl hq _
    _ = AlgebraicCycle.map (φ.hom ≫ W.subschemeι)
          (relativeDimension C.dimensionFunction (T.subschemeι ≫ sZ))
          (relativeDimension C.dimensionFunction sX)
          (principalCycle T.subscheme ((rationalFunctionsEquivFunctionField T.subscheme).1
            (g : rationalFunctions T.subscheme))) :=
        algebraicCycle_map_congr hφ.symm _ _ _
    _ = AlgebraicCycle.map W.subschemeι
          (relativeDimension C.dimensionFunction (W.subschemeι ≫ sX))
          (relativeDimension C.dimensionFunction sX)
          (AlgebraicCycle.map φ.hom
            (relativeDimension C.dimensionFunction (T.subschemeι ≫ sZ))
            (relativeDimension C.dimensionFunction (W.subschemeι ≫ sX))
            (principalCycle T.subscheme ((rationalFunctionsEquivFunctionField T.subscheme).1
              (g : rationalFunctions T.subscheme)))) :=
        (algebraicCycle_map_comp_relativeDimension C (T.subschemeι ≫ sZ) (W.subschemeι ≫ sX) sX
          φ.hom W.subschemeι hφs rfl _).symm
    _ = principalDivisorPushforward C sX W hW (rationalFunctionsUnitsMulEquivOfIso φ g) := by
        rw [map_principalCycle_rationalFunctions_of_iso φ _ _ hw]
        rfl

/-! ### An integral closed subscheme inside a closed subscheme -/

/-- An integral closed subscheme `W ⊆ X` whose support lies inside the support of an ideal sheaf
`I` on `X` is also an integral closed subscheme of the closed subscheme `V(I)` cut out by `I`:
there is an ideal sheaf `T` on `V(I)` whose closed subscheme is integral, whose support is the
preimage of the support of `W`, which has the same delta-dimension over the base, and on which a
prescribed nonzero rational function on `W` has a counterpart whose principal divisor pushes
forward to the pushforward of the principal divisor on `W`. -/
theorem exists_idealSheafData_of_support_subset {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (I W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hsub : (W.support : Set X) ⊆ (I.support : Set X))
    (g : (rationalFunctions W.subscheme)ˣ) :
    ∃ (T : I.subscheme.IdealSheafData) (hT : IsIntegral T.subscheme)
      (gT : (rationalFunctions T.subscheme)ˣ),
      ((T.support : Set I.subscheme) = I.subschemeι.base ⁻¹' (W.support : Set X)) ∧
        schemeDeltaDimension C (T.subschemeι ≫ I.subschemeι ≫ sX) =
            schemeDeltaDimension C (W.subschemeι ≫ sX) ∧
          AlgebraicCycle.map I.subschemeι
              (relativeDimension C.dimensionFunction (I.subschemeι ≫ sX))
              (relativeDimension C.dimensionFunction sX)
              (principalDivisorPushforward C (I.subschemeι ≫ sX) T hT gT) =
            principalDivisorPushforward C sX W hW g := by
  have _ := hW
  have hIW : I ≤ W := by
    have h : I ≤ Scheme.IdealSheafData.vanishingIdeal W.support :=
      Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hsub
    rwa [← Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme W W.support rfl] at h
  have hker : I.subschemeι.ker ≤ W.subschemeι.ker := by
    rwa [I.ker_subschemeι, W.ker_subschemeι]
  set f : W.subscheme ⟶ I.subscheme := IsClosedImmersion.lift I.subschemeι W.subschemeι hker
  have hf : f ≫ I.subschemeι = W.subschemeι := IsClosedImmersion.lift_fac _ _ hker
  have hfw : ∀ w : W.subscheme, I.subschemeι.base (f.base w) = W.subschemeι.base w := fun w ↦
    congrArg (fun r : W.subscheme ⟶ X ↦ r.base w) hf
  have _ : IsClosedImmersion (f ≫ I.subschemeι) := by rw [hf]; infer_instance
  have _ : IsClosedImmersion f := IsClosedImmersion.of_comp_isClosedImmersion f I.subschemeι
  have htoim : f.toImage ≫ f.ker.subschemeι = f := Scheme.Hom.toImage_imageι f
  set φ : f.ker.subscheme ≅ W.subscheme := (asIso f.toImage).symm
  have hφ : φ.hom ≫ W.subschemeι = f.ker.subschemeι ≫ I.subschemeι := by
    show inv f.toImage ≫ W.subschemeι = f.ker.subschemeι ≫ I.subschemeι
    exact (IsIso.inv_comp_eq f.toImage).mpr (by rw [← Category.assoc, htoim, hf])
  have hφs : φ.hom ≫ (W.subschemeι ≫ sX) = f.ker.subschemeι ≫ I.subschemeι ≫ sX := by
    rw [← Category.assoc, hφ, Category.assoc]
  have hT : IsIntegral f.ker.subscheme := IsIntegral.of_isIso φ.inv
  refine ⟨f.ker, hT, (rationalFunctionsUnitsMulEquivOfIso φ).symm g, ?_, ?_, ?_⟩
  · have hrange : (f.ker.support : Set I.subscheme) = Set.range f.base := by
      rw [Scheme.Hom.support_ker]
      exact f.isClosedEmbedding.isClosed_range.closure_eq
    rw [hrange]
    refine Set.Subset.antisymm ?_ fun y hy ↦ ?_
    · rintro _ ⟨w, rfl⟩
      rw [Set.mem_preimage, hfw w, ← W.range_subschemeι]
      exact ⟨w, rfl⟩
    · rw [Set.mem_preimage, ← W.range_subschemeι] at hy
      obtain ⟨w, hw⟩ := hy
      exact ⟨w, I.subschemeι.isClosedEmbedding.injective ((hfw w).trans hw)⟩
  · have _ := hT
    exact (schemeDeltaDimension_of_iso C (f.ker.subschemeι ≫ I.subschemeι ≫ sX)
      (W.subschemeι ≫ sX) φ hφs).symm
  · have _ := hT
    rw [map_principalDivisorPushforward_of_iso C (I.subschemeι ≫ sX) sX I.subschemeι rfl f.ker W
      φ hφ, MulEquiv.apply_symm_apply]

/-! ### Decomposing a rational equivalence along a cover by two closed subschemes -/

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- If every member of a locally finite family of integral closed subschemes of `X` of
delta-dimension `k + 1` lies inside the closed subscheme `V(I)` cut out by an ideal sheaf `I`, then
the `k`-cycle the family defines through the principal divisors of a family of rational functions
pulls back to a `k`-cycle rationally equivalent to zero on `V(I)`. -/
theorem isRationallyEquivalentToZero_cyclePullbackAlongClosedImmersion (I : X.IdealSheafData)
    (k : ℤ) {K : Type u} (W : K → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ)
    (hsub : ∀ j, ((W j).support : Set X) ⊆ (I.support : Set X)) (α : CycleGroup C sX k)
    (hα : ∀ x : X, α.1 x = principalDivisorFamilyCoefficient C sX W hW g x) :
    IsRationallyEquivalentToZero C (I.subschemeι ≫ sX) k
      (cyclePullbackAlongClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k α) := by
  choose T hT gT hsupp hdim hmap using fun j ↦
    exists_idealSheafData_of_support_subset C sX I (W j) (hW j) (hsub j) (g j)
  refine ⟨K, T, hT, fun j ↦ (hdim j).trans (hDim j), ?_, gT, fun y ↦ ?_⟩
  · rw [show (fun j ↦ ((T j).support : Set I.subscheme)) =
      fun j ↦ I.subschemeι.base ⁻¹' ((W j).support : Set X) from funext hsupp]
    exact hLocal.preimage_continuous I.subschemeι.continuous
  · rw [cyclePullbackAlongClosedImmersion_apply, hα]
    refine finsum_congr fun j ↦ ?_
    rw [← congrArg (fun c : AlgebraicCycle X ℤ ↦ c (I.subschemeι.base y)) (hmap j)]
    exact algebraicCycle_map_relativeDimension_apply_image C (I.subschemeι ≫ sX) sX I.subschemeι
      rfl _ y

/-- If the two closed subschemes cut out by `I` and `J` cover `X` set-theoretically, a `k`-cycle on
`X` rationally equivalent to zero is the sum of the pushforwards of a `k`-cycle rationally
equivalent to zero on each of them. -/
theorem exists_rationallyEquivalentToZero_summandsToUnion (I J : X.IdealSheafData) (k : ℤ)
    (hcover : I.support ⊔ J.support = ⊤) {α : CycleGroup C sX k}
    (hα : IsRationallyEquivalentToZero C sX k α) :
    ∃ (a : CycleGroup C (I.subschemeι ≫ sX) k) (b : CycleGroup C (J.subschemeι ≫ sX) k),
      IsRationallyEquivalentToZero C (I.subschemeι ≫ sX) k a ∧
        IsRationallyEquivalentToZero C (J.subschemeι ≫ sX) k b ∧
          summandsToUnion C sX I J k (a, b) = α := by
  classical
  obtain ⟨K, W, hW, hDim, hLocal, g, hcoeff⟩ := hα
  set P : K → Prop := fun j ↦ ((W j).support : Set X) ⊆ (I.support : Set X)
  have hLoc : ∀ Q : K → Prop, LocallyFinite fun j : {j // Q j} ↦ ((W j.1).support : Set X) :=
    fun _ ↦ hLocal.comp_injective Subtype.val_injective
  have hsubR : ∀ j : {j // ¬ P j}, ((W j.1).support : Set X) ⊆ (J.support : Set X) := fun j ↦
    (support_subset_left_or_right_of_isIntegral I J (W j.1) (hW j.1) hcover).resolve_left j.2
  obtain ⟨αL, hαL⟩ := exists_principalDivisorFamilySum C sX k (fun j : {j // P j} ↦ W j.1)
    (fun j ↦ hW j.1) (fun j ↦ hDim j.1) (hLoc _) fun j ↦ g j.1
  obtain ⟨αR, hαR⟩ := exists_principalDivisorFamilySum C sX k (fun j : {j // ¬ P j} ↦ W j.1)
    (fun j ↦ hW j.1) (fun j ↦ hDim j.1) (hLoc _) fun j ↦ g j.1
  have hsupport : ∀ (Q : K → Prop) (L : X.IdealSheafData)
      (hQ : ∀ j : {j // Q j}, ((W j.1).support : Set X) ⊆ (L.support : Set X))
      (β : CycleGroup C sX k)
      (hβ : ∀ x : X, β.1 x = principalDivisorFamilyCoefficient C sX
        (fun j : {j // Q j} ↦ W j.1) (fun j ↦ hW j.1) (fun j ↦ g j.1) x)
      (x : X), x ∉ (L.support : Set X) → β.1 x = 0 := by
    intro Q L hQ β hβ x hxL
    rw [hβ x]
    refine finsum_eq_zero_of_forall_eq_zero fun j ↦ ?_
    by_contra h
    exact hxL (hQ j (support_principalDivisorPushforward_subset C sX (W j.1) (hW j.1)
      (g j.1) (by simpa [Function.mem_support] using h)))
  have hsplit : ∀ x : X, αL.1 x + αR.1 x = α.1 x := by
    intro x
    have hfin : ∀ Q : K → Prop, (Function.support fun j : {j // Q j} ↦
        principalDivisorPushforward C sX (W j.1) (hW j.1) (g j.1) x).Finite := fun Q ↦
      finite_support_of_locallyFinite _ (hLoc Q)
        (fun j ↦ principalDivisorPushforward C sX (W j.1) (hW j.1) (g j.1))
        (fun j ↦ support_principalDivisorPushforward_subset C sX (W j.1) (hW j.1) (g j.1)) x
    rw [hαL x, hαR x, hcoeff x]
    show ((∑ᶠ j : {j // P j}, _) + ∑ᶠ j : {j // ¬ P j}, _) = ∑ᶠ j : K, _
    rw [← finsum_sum_elim _ _ (hfin _) (hfin _), ← finsum_comp_equiv (Equiv.sumCompl P)]
    exact finsum_congr fun j ↦ by cases j with | inl j => rfl | inr j => rfl
  refine ⟨cyclePullbackAlongClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k αL,
    cyclePullbackAlongClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k αR,
    isRationallyEquivalentToZero_cyclePullbackAlongClosedImmersion C sX I k
      (fun j : {j // P j} ↦ W j.1) (fun j ↦ hW j.1) (fun j ↦ hDim j.1) (hLoc _)
      (fun j ↦ g j.1) (fun j ↦ j.2) αL hαL,
    isRationallyEquivalentToZero_cyclePullbackAlongClosedImmersion C sX J k
      (fun j : {j // ¬ P j} ↦ W j.1) (fun j ↦ hW j.1) (fun j ↦ hDim j.1) (hLoc _)
      (fun j ↦ g j.1) hsubR αR hαR,
    Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)⟩
  have hadd : ∀ (q r : CycleGroup C sX k) (w : X), (q + r).1 w = q.1 w + r.1 w := fun _ _ _ ↦ rfl
  rw [summandsToUnion_apply, hadd]
  dsimp only
  rw [properPushforward_cyclePullbackAlongClosedImmersion_apply,
    properPushforward_cyclePullbackAlongClosedImmersion_apply, I.range_subschemeι,
    J.range_subschemeι,
    Set.indicator_apply_eq_self.2 (hsupport P I (fun j ↦ j.2) αL hαL x),
    Set.indicator_apply_eq_self.2 (hsupport (fun j ↦ ¬ P j) J hsubR αR hαR x)]
  exact hsplit x

/-! ### The two maps of the sequence of Chow groups -/

variable (I J : X.IdealSheafData) (k : ℤ)

/-- The first map of the sequence of Chow groups of a union of two closed subschemes: the class of
a `k`-cycle on the scheme-theoretic intersection is sent to the class of its pushforward to the
closed subscheme cut out by `I`, together with minus the class of its pushforward to the one cut
out by `J`. -/
def intersectionToSummandsChow :
    chowGroup C ((I ⊔ J).subschemeι ≫ sX) k →+
      chowGroup C (I.subschemeι ≫ sX) k × chowGroup C (J.subschemeι ≫ sX) k :=
  (chowPushforwardOfIsClosedImmersion C ((I ⊔ J).subschemeι ≫ sX) (I.subschemeι ≫ sX)
      (inclusion (le_sup_left : I ≤ I ⊔ J))
      (inclusion_subschemeι_assoc (le_sup_left : I ≤ I ⊔ J) sX) k).prod
    (-chowPushforwardOfIsClosedImmersion C ((I ⊔ J).subschemeι ≫ sX) (J.subschemeι ≫ sX)
      (inclusion (le_sup_right : J ≤ I ⊔ J))
      (inclusion_subschemeι_assoc (le_sup_right : J ≤ I ⊔ J) sX) k)

/-- The second map of the sequence of Chow groups of a union of two closed subschemes: a pair of
classes of `k`-cycles on the two closed subschemes is sent to the sum of the classes of their
pushforwards to the ambient scheme. -/
def summandsToUnionChow :
    chowGroup C (I.subschemeι ≫ sX) k × chowGroup C (J.subschemeι ≫ sX) k →+
      chowGroup C sX k :=
  (chowPushforwardOfIsClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k).coprod
    (chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k)

/-- The first map of the sequence of Chow groups is induced by the first map of the sequence of
cycle groups, `Stacks.Chow.intersectionToSummands`. -/
@[simp]
theorem intersectionToSummandsChow_mk (c : CycleGroup C ((I ⊔ J).subschemeι ≫ sX) k) :
    intersectionToSummandsChow C sX I J k
        (QuotientAddGroup.mk' (rationalEquivalences C ((I ⊔ J).subschemeι ≫ sX) k) c) =
      (QuotientAddGroup.mk' (rationalEquivalences C (I.subschemeι ≫ sX) k)
          (intersectionToSummands C sX I J k c).1,
        QuotientAddGroup.mk' (rationalEquivalences C (J.subschemeι ≫ sX) k)
          (intersectionToSummands C sX I J k c).2) := by
  refine Prod.ext ?_ ?_
  · show chowPushforwardOfIsClosedImmersion C ((I ⊔ J).subschemeι ≫ sX) (I.subschemeι ≫ sX)
      (inclusion (le_sup_left : I ≤ I ⊔ J))
      (inclusion_subschemeι_assoc (le_sup_left : I ≤ I ⊔ J) sX) k
      (QuotientAddGroup.mk' _ c) = _
    rw [chowPushforwardOfIsClosedImmersion_mk, intersectionToSummands_apply_fst]
  · show -chowPushforwardOfIsClosedImmersion C ((I ⊔ J).subschemeι ≫ sX) (J.subschemeι ≫ sX)
      (inclusion (le_sup_right : J ≤ I ⊔ J))
      (inclusion_subschemeι_assoc (le_sup_right : J ≤ I ⊔ J) sX) k
      (QuotientAddGroup.mk' _ c) = _
    rw [chowPushforwardOfIsClosedImmersion_mk, intersectionToSummands_apply_snd, map_neg]

/-- The second map of the sequence of Chow groups is induced by the second map of the sequence of
cycle groups, `Stacks.Chow.summandsToUnion`. -/
@[simp]
theorem summandsToUnionChow_mk (a : CycleGroup C (I.subschemeι ≫ sX) k)
    (b : CycleGroup C (J.subschemeι ≫ sX) k) :
    summandsToUnionChow C sX I J k
        (QuotientAddGroup.mk' (rationalEquivalences C (I.subschemeι ≫ sX) k) a,
          QuotientAddGroup.mk' (rationalEquivalences C (J.subschemeι ≫ sX) k) b) =
      QuotientAddGroup.mk' (rationalEquivalences C sX k) (summandsToUnion C sX I J k (a, b)) := by
  show chowPushforwardOfIsClosedImmersion C (I.subschemeι ≫ sX) sX I.subschemeι rfl k
      (QuotientAddGroup.mk' _ a) +
    chowPushforwardOfIsClosedImmersion C (J.subschemeι ≫ sX) sX J.subschemeι rfl k
      (QuotientAddGroup.mk' _ b) = _
  rw [chowPushforwardOfIsClosedImmersion_mk, chowPushforwardOfIsClosedImmersion_mk,
    summandsToUnion_apply, map_add]

/-! ### Exactness -/

/-- The composite of the two maps of the sequence of Chow groups is zero. -/
theorem summandsToUnionChow_intersectionToSummandsChow
    (c : chowGroup C ((I ⊔ J).subschemeι ≫ sX) k) :
    summandsToUnionChow C sX I J k (intersectionToSummandsChow C sX I J k c) = 0 := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  rw [intersectionToSummandsChow_mk, summandsToUnionChow_mk]
  show QuotientAddGroup.mk' (rationalEquivalences C sX k)
    (summandsToUnion C sX I J k (intersectionToSummands C sX I J k c)) = 0
  rw [summandsToUnion_intersectionToSummands, map_zero]

/-- Subtracting a `k`-cycle rationally equivalent to zero does not change the class of a
`k`-cycle in the Chow group. -/
private theorem mk_sub_eq_of_isRationallyEquivalentToZero {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (k : ℤ) (a a' : CycleGroup C sY k)
    (h : IsRationallyEquivalentToZero C sY k a') :
    QuotientAddGroup.mk' (rationalEquivalences C sY k) (a - a') =
      QuotientAddGroup.mk' (rationalEquivalences C sY k) a := by
  have h0 : QuotientAddGroup.mk' (rationalEquivalences C sY k) a' = 0 :=
    (QuotientAddGroup.eq_zero_iff (N := rationalEquivalences C sY k) a').mpr
      ((mem_rationalEquivalences C sY k a').mpr h)
  rw [map_sub, h0, sub_zero]

/-- A pair of classes of `k`-cycles killed by the sum of the pushforwards comes from the
scheme-theoretic intersection. -/
private theorem mem_range_intersectionToSummandsChow_of_summandsToUnionChow_eq_zero
    (hcover : I.support ⊔ J.support = ⊤)
    (qI : chowGroup C (I.subschemeι ≫ sX) k) (qJ : chowGroup C (J.subschemeι ≫ sX) k)
    (hzero : summandsToUnionChow C sX I J k (qI, qJ) = 0) :
    (qI, qJ) ∈ Set.range (intersectionToSummandsChow C sX I J k) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ qI
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ qJ
  rw [summandsToUnionChow_mk] at hzero
  have hα : IsRationallyEquivalentToZero C sX k (summandsToUnion C sX I J k (a, b)) :=
    (QuotientAddGroup.eq_zero_iff _).mp hzero
  obtain ⟨a', b', ha', hb', hsum⟩ :=
    exists_rationallyEquivalentToZero_summandsToUnion C sX I J k hcover hα
  have hzero' : summandsToUnion C sX I J k (a - a', b - b') = 0 := by
    rw [show ((a - a', b - b') :
        CycleGroup C (I.subschemeι ≫ sX) k × CycleGroup C (J.subschemeι ≫ sX) k) =
      (a, b) - (a', b') from rfl, map_sub, hsum, sub_self]
  obtain ⟨c, hc⟩ :=
    (exact_intersectionToSummands_summandsToUnion C sX I J k (a - a', b - b')).mp hzero'
  refine ⟨QuotientAddGroup.mk' _ c, ?_⟩
  rw [intersectionToSummandsChow_mk, hc]
  exact Prod.ext (mk_sub_eq_of_isRationallyEquivalentToZero C _ k a a' ha')
    (mk_sub_eq_of_isRationallyEquivalentToZero C _ k b b' hb')

/-- The sequence of Chow groups of a union of two closed subschemes is exact in the middle: a pair
of classes of `k`-cycles on the two closed subschemes has vanishing sum of pushforwards exactly
when it comes from a class of `k`-cycles on the scheme-theoretic intersection. -/
@[stacks 0F94 "exactness in the middle"]
theorem exact_intersectionToSummandsChow_summandsToUnionChow
    (hcover : I.support ⊔ J.support = ⊤) :
    Function.Exact (intersectionToSummandsChow C sX I J k) (summandsToUnionChow C sX I J k) := by
  intro p
  refine ⟨mem_range_intersectionToSummandsChow_of_summandsToUnionChow_eq_zero C sX I J k hcover
    p.1 p.2, ?_⟩
  rintro ⟨c, rfl⟩
  exact summandsToUnionChow_intersectionToSummandsChow C sX I J k c

/-- If two closed subschemes cover the ambient scheme set-theoretically, every class of `k`-cycles
on it is the sum of the classes of the pushforwards of a `k`-cycle on each of them. -/
@[stacks 0F94 "surjectivity"]
theorem surjective_summandsToUnionChow (hcover : I.support ⊔ J.support = ⊤) :
    Function.Surjective (summandsToUnionChow C sX I J k) := by
  intro q
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  obtain ⟨⟨a, b⟩, hab⟩ := surjective_summandsToUnion C sX I J k hcover c
  exact ⟨(QuotientAddGroup.mk' _ a, QuotientAddGroup.mk' _ b), by
    rw [summandsToUnionChow_mk, hab]⟩

end Stacks.Chow

end
