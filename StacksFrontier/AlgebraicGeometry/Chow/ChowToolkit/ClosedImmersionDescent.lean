module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Divisors.SplitClosedImmersionIdeal
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Descent of a rational equivalence into a closed subscheme

Let `j : Z ⟶ Y` be a closed immersion over the base and `β` a `k`-cycle on `Z`. If the proper
pushforward of `β` is rationally equivalent to zero on `Y` *within the image of `j`*, then `β` is
already rationally equivalent to zero on `Z`. This is the converse of
`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion`.

The witnessing family descends. A witness `W ⊆ Y` is integral, hence reduced, hence the vanishing
ideal of its support; its support lies in the image of `j`, so `j.ker ≤ W` and therefore
`(W.comap j).map j = W`. The scheme-theoretic image of `W.comap j` under `j` is thus `W` itself,
so `Stacks.Chow.imageIsoOfIsClosedImmersion` is an isomorphism `(W.comap j).subscheme ≅
W.subscheme` compatible with the two closed immersions into `Z` and `Y`. Integrality, the
delta-dimension, the rational function and the principal divisor all transport along it, and the
coefficient identity at a point `z` of `Z` is the identity on `Y` read at `j z`, where proper
pushforward along a closed immersion changes nothing.

## Main results

* `exists_descent_principalDivisorPushforward_comap` — a single witness of a rational equivalence
  whose support lies in the image of `j` descends to a witness on `Z`, with the same
  pushed-forward principal divisor.
* `isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin` — the
  descent of the whole rational equivalence.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Descending a closed subscheme through a closed immersion -/

section Witness

variable {Z Y : Scheme.{u}} (j : Z ⟶ Y) [IsClosedImmersion j]

omit [IsClosedImmersion j] in
/-- A reduced closed subscheme of `Y` whose support lies in the image of the closed immersion `j`
contains the kernel of `j`: it is the vanishing ideal of its support by the uniqueness half of
Stacks 01J3, and the kernel of `j` is contained in that vanishing ideal because the image of `j`
lies in the support of the kernel. -/
theorem ker_le_of_support_subset_range (W : Y.IdealSheafData) [IsReduced W.subscheme]
    (hsub : (W.support : Set Y) ⊆ Set.range j.base) : j.ker ≤ W := by
  have hsupp : (W.support : Set Y) ⊆ (j.ker.support : Set Y) :=
    hsub.trans j.range_subset_ker_support
  have hle := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    (SetLike.coe_subset_coe.mp hsupp)
  rwa [← Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme W W.support rfl] at hle

/-- A reduced closed subscheme of `Y` whose support lies in the image of the closed immersion `j`
is the scheme-theoretic image of its inverse image: the ideal correspondence for `j` recovers it
up to the kernel of `j`, which it already contains. -/
theorem map_comap_eq_of_support_subset_range (W : Y.IdealSheafData) [IsReduced W.subscheme]
    (hsub : (W.support : Set Y) ⊆ Set.range j.base) : (W.comap j).map j = W := by
  rw [Stacks.IdealSheaf.map_comap_of_isClosedImmersion,
    sup_eq_left.mpr (ker_le_of_support_subset_range j W hsub)]

/-- An ideal sheaf on `Z` whose scheme-theoretic image under the closed immersion `j` is `W`
has its closed subscheme isomorphic to that of `W`, compatibly with the two closed immersions.
This is `Stacks.Chow.imageIsoOfIsClosedImmersion` with the target rewritten. -/
private theorem exists_subschemeIso_of_map_eq (I : Z.IdealSheafData) (W : Y.IdealSheafData)
    (h : I.map j = W) :
    ∃ φ : I.subscheme ≅ W.subscheme, φ.hom ≫ W.subschemeι = I.subschemeι ≫ j := by
  subst h
  exact ⟨imageIsoOfIsClosedImmersion j I, imageIsoOfIsClosedImmersion_hom_subschemeι j I⟩

/-! ### Descending a single witness of a rational equivalence -/

/-- **One witness of a rational equivalence descends through a closed immersion.** If `W ⊆ Y` is
an integral closed subscheme of delta-dimension `k + 1` whose support lies in the image of the
closed immersion `j : Z ⟶ Y` over the base, and `g` is a nonzero rational function on `W`, then
the inverse image `W.comap j` is an integral closed subscheme of `Z` of delta-dimension `k + 1`
carrying a nonzero rational function whose pushed-forward principal divisor has, at every point
`z` of `Z`, the coefficient that the pushed-forward principal divisor of `g` has at `j z`. -/
theorem exists_descent_principalDivisorPushforward_comap (C : ChowSituation.{u})
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (hj : j ≫ sY = sZ) (k : ℤ) (W : Y.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hsub : (W.support : Set Y) ⊆ Set.range j.base)
    (g : (rationalFunctions W.subscheme)ˣ) :
    ∃ hV : IsIntegral (W.comap j).subscheme,
      schemeDeltaDimension C ((W.comap j).subschemeι ≫ sZ) = ((k + 1 : ℤ) : EInt) ∧
        ∃ g' : (rationalFunctions (W.comap j).subscheme)ˣ, ∀ z : Z,
          principalDivisorPushforward C sZ (W.comap j) hV g' z =
            principalDivisorPushforward C sY W hW g (j.base z) := by
  have _ := hW
  obtain ⟨φ, hφ⟩ := exists_subschemeIso_of_map_eq j (W.comap j) W
    (map_comap_eq_of_support_subset_range j W hsub)
  have hV : IsIntegral (W.comap j).subscheme := IsIntegral.of_isIso φ.inv
  have _ := hV
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sY)
  have _ : IsLocallyNoetherian (W.comap j).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((W.comap j).subschemeι ≫ sZ)
  have hφ' : φ.hom ≫ (W.subschemeι ≫ sY) = (W.comap j).subschemeι ≫ sZ := by
    rw [← Category.assoc, hφ, Category.assoc, hj]
  have hVDim : schemeDeltaDimension C ((W.comap j).subschemeι ≫ sZ) = ((k + 1 : ℤ) : EInt) :=
    (schemeDeltaDimension_of_iso C ((W.comap j).subschemeι ≫ sZ) (W.subschemeι ≫ sY) φ
      hφ').symm.trans hDim
  have hw : ∀ z : (W.comap j).subscheme,
      relativeDimension C.dimensionFunction ((W.comap j).subschemeι ≫ sZ) z =
        relativeDimension C.dimensionFunction (W.subschemeι ≫ sY) (φ.hom.base z) :=
    fun z ↦ (relativeDimension_of_iso C.dimensionFunction ((W.comap j).subschemeι ≫ sZ)
      (W.subschemeι ≫ sY) φ hφ' z).symm
  refine ⟨hV, hVDim, (rationalFunctionsUnitsMulEquivOfIso φ).symm g, fun z ↦ ?_⟩
  set g' := (rationalFunctionsUnitsMulEquivOfIso φ).symm g with hg'
  have hgg : rationalFunctionsRingEquivOfIso φ (g' : rationalFunctions (W.comap j).subscheme) =
      (g : rationalFunctions W.subscheme) := by
    rw [← rationalFunctionsUnitsMulEquivOfIso_coe φ g', hg', MulEquiv.apply_symm_apply]
  -- the two pushed-forward principal divisors agree as cycles on `Y`
  have hcycle : AlgebraicCycle.map j (relativeDimension C.dimensionFunction sZ)
      (relativeDimension C.dimensionFunction sY)
      (principalDivisorPushforward C sZ (W.comap j) hV g') =
        principalDivisorPushforward C sY W hW g :=
    calc AlgebraicCycle.map j (relativeDimension C.dimensionFunction sZ)
          (relativeDimension C.dimensionFunction sY)
          (principalDivisorPushforward C sZ (W.comap j) hV g')
        = AlgebraicCycle.map ((W.comap j).subschemeι ≫ j)
            (relativeDimension C.dimensionFunction ((W.comap j).subschemeι ≫ sZ))
            (relativeDimension C.dimensionFunction sY)
            (principalCycle (W.comap j).subscheme
              ((rationalFunctionsEquivFunctionField (W.comap j).subscheme).1
                (g' : rationalFunctions (W.comap j).subscheme))) :=
          algebraicCycle_map_comp_relativeDimension C ((W.comap j).subschemeι ≫ sZ) sZ sY
            (W.comap j).subschemeι j rfl hj _
      _ = AlgebraicCycle.map (φ.hom ≫ W.subschemeι)
            (relativeDimension C.dimensionFunction ((W.comap j).subschemeι ≫ sZ))
            (relativeDimension C.dimensionFunction sY)
            (principalCycle (W.comap j).subscheme
              ((rationalFunctionsEquivFunctionField (W.comap j).subscheme).1
                (g' : rationalFunctions (W.comap j).subscheme))) :=
          algebraicCycle_map_congr hφ.symm _ _ _
      _ = AlgebraicCycle.map W.subschemeι
            (relativeDimension C.dimensionFunction (W.subschemeι ≫ sY))
            (relativeDimension C.dimensionFunction sY)
            (AlgebraicCycle.map φ.hom
              (relativeDimension C.dimensionFunction ((W.comap j).subschemeι ≫ sZ))
              (relativeDimension C.dimensionFunction (W.subschemeι ≫ sY))
              (principalCycle (W.comap j).subscheme
                ((rationalFunctionsEquivFunctionField (W.comap j).subscheme).1
                  (g' : rationalFunctions (W.comap j).subscheme)))) :=
          (algebraicCycle_map_comp_relativeDimension C ((W.comap j).subschemeι ≫ sZ)
            (W.subschemeι ≫ sY) sY φ.hom W.subschemeι hφ' rfl _).symm
      _ = principalDivisorPushforward C sY W hW g := by
          rw [map_principalCycle_rationalFunctions_of_iso φ _ _ hw, hgg]
          rfl
  -- read it at `j z`, where pushforward along a closed immersion changes nothing
  have hpush := properPushforward_apply_image_of_isClosedImmersion C sZ sY j hj k
    (⟨principalDivisorPushforward C sZ (W.comap j) hV g',
      principalDivisorPushforward_mem_cyclesOfDimension C sZ k (W.comap j) hV hVDim g'⟩ :
        CycleGroup C sZ k) z
  rw [← hcycle]
  exact hpush.symm

end Witness

/-! ### Descent of the whole rational equivalence -/

/-- **Descent of a rational equivalence into a closed subscheme.** Along a closed immersion
`j : Z ⟶ Y` over the base, a `k`-cycle `β` on `Z` whose proper pushforward is rationally
equivalent to zero within the image of `j` is itself rationally equivalent to zero.

The witnessing family `W` on `Y` is replaced by the family of inverse images `W a |>.comap j`,
each of which is integral of delta-dimension `k + 1` and carries a rational function with the
same pushed-forward principal divisor by
`Stacks.Chow.exists_descent_principalDivisorPushforward_comap`. The new family is locally finite
because the supports are the preimages of the old supports
(`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`) and `j` is continuous, and the
coefficient identity at `z` is the one on `Y` at `j z`.

This is the converse of
`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion`. -/
theorem isRationallyEquivalentToZero_of_properPushforward_isRationallyEquivalentToZeroWithin
    (C : ChowSituation.{u}) {Z Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hj : j ≫ sY = sZ) (k : ℤ) (β : CycleGroup C sZ k)
    (h : IsRationallyEquivalentToZeroWithin C sY k
      (properPushforward C sZ sY j hj k β) (Set.range j.base)) :
    IsRationallyEquivalentToZero C sZ k β := by
  obtain ⟨A, W, hW, hDim, hLocal, hsub, g, hg⟩ := h
  choose hV hVDim g' hcoeff using fun a ↦ exists_descent_principalDivisorPushforward_comap j C
    sZ sY hj k (W a) (hW a) (hDim a) (hsub a) (g a)
  have hsupp : (fun a ↦ (((W a).comap j).support : Set Z)) =
      fun a ↦ j.base ⁻¹' ((W a).support : Set Y) := by
    funext a
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  refine ⟨A, fun a ↦ (W a).comap j, hV, hVDim, ?_, g', fun z ↦ ?_⟩
  · rw [hsupp]
    exact hLocal.preimage_continuous j.continuous
  · rw [← properPushforward_apply_image_of_isClosedImmersion C sZ sY j hj k β z,
      hg (j.base z)]
    exact (finsum_congr fun a ↦ hcoeff a z).symm

end Stacks.Chow

end
