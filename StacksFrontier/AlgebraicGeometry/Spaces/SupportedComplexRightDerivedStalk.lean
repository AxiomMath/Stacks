module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPrecomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExistsKInjectiveResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportedDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedComplexDerivedStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafStalkAnyGeometricPointGeneral

/-!
# Stacks 0AEQ: the stalk of `Rf_*` of a complex supported on `f^{-1}Z`

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `Z ⊆ X` be a closed
subspace and let `f^{-1}Z = Y ×_X Z` be its inverse image, with `f' : f^{-1}Z ⟶ Z` integral and
universally injective. For a geometric point `ȳ` of `Y` with image `x̄ = f(ȳ)` and an object `Q`
of `D(Y_étale)` supported on `|f^{-1}Z|`,
```
(Rf_*Q)_{x̄} ≅ Q_ȳ   in D(Ab).
```
This is **Stacks 0AEQ**, stated here at the generality of the source: `f` is an arbitrary
morphism of algebraic spaces, `ȳ` an arbitrary geometric point of `Y`, `Rf_*` any total right
derived functor of the direct image of abelian sheaves along `f`, and every derived category in
the statement is an arbitrary model (`HasDerivedCategory`).

## Main results

* `AlgebraicGeometry.Space.epi_of_epi_smallEtaleAbelianStalk_map`: the geometric stalks jointly
  detect epimorphisms of abelian sheaves on the small étale site of an algebraic space.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkIsoOfIntegral` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_smallEtaleAbelianPushforward_of_isIntegralHom`:
  for an integral universally injective morphism `g : W ⟶ Z` the stalk of `g_*G` at `g(w̄)` is
  `G_w̄`, and `g_*` is exact.
* `AlgebraicGeometry.Space.isIso_exactAdjunctionDerived_unit_app_of_supportOfSheaf_subset`: for a
  closed immersion `i : Z ⟶ X` the unit `K ⟶ i_*i^{-1}K` is invertible on every complex supported
  on `|Z|`, in any model of the derived categories.
* `AlgebraicGeometry.Space.hasRightDerivedFunctor_smallEtaleAbelianDirectImage`: the total right
  derived functor `Rf_*` exists, for an arbitrary morphism `f`.
* `AlgebraicGeometry.Space.stalkRightDerivedDirectImageIsoOnSupported`: the comparison of
  Stacks 0AEQ as an isomorphism of functors on `D_{|f^{-1}Z|}(Y_étale)`.
* `AlgebraicGeometry.Space.stalkRightDerivedDirectImageIso` is **Stacks 0AEQ**, and
  `AlgebraicGeometry.Space.stalkRightDerivedDirectImageIso_naturality` is its naturality in `Q`.

## Implementation notes

The proof is the source's. Write `Q = i'_*K'` with `K' = i'^{-1}Q`, the unit of the adjunction
`i'^{-1} ⊣ i'_*` being invertible on supported complexes (Stacks 0AEI). The composite
`Rf_* ∘ i'_*` is a right derived functor of `f_* ∘ i'_*`, because `i'_*` has the exact left
adjoint `i'^{-1}` and so preserves K-injective complexes (Stacks 015N in the form the proof uses
it, `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint`). The functor
`f_* ∘ i'_*` is `i_* ∘ f'_*`, which is exact: `i_*` along the closed immersion, and `f'_*` along
the integral universally injective `f'` because its stalk at `f'(w̄)` is the stalk at `w̄`
(Stacks 0AEH and Stacks 04K2). So `Rf_*(i'_*K')` is `(f_* ∘ i'_*)(K')` computed degreewise, and
its stalk at `x̄` is the degreewise stalk of `f_*i'_*K'`. That is identified with the stalk at `ȳ`
of `i'_*K'` by the sheaf-level comparison
`AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support_of_isPullback`,
which holds at every geometric point of `Y`, on or off `|f^{-1}Z|`.

The closed subspace `f^{-1}Z` enters as an arbitrary cartesian square `sq`; that `i'` is a closed
immersion is derived from `sq` (`AlgebraicGeometry.Space.isClosedImmersion_of_isPullback`). The
intermediate derived category `D((f^{-1}Z)_étale)`, which does not occur in the statement, is
taken to be the standard model inside the proofs.

`AlgebraicGeometry.Space.stalkDerivedPushforwardIso` in
`StacksFrontier.AlgebraicGeometry.Spaces.SupportedComplexDerivedStalk` is an earlier form of this
result which carries Stacks 0AEH part (1) and Stacks 015N as the fields of a structure, requires
`f` representable and `ȳ` lifted to `f^{-1}Z`, and fixes the standard model; nothing here
depends on it.

## References

* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
* [Stacks Project, Tag 0AEI](https://stacks.math.columbia.edu/tag/0AEI)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w₁ w₂ w₃ w₄ u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z W : AlgebraicSpaces B S hS}

/-! ### Epimorphisms are detected on geometric stalks -/

/-- **The geometric stalks jointly detect epimorphisms** of abelian sheaves on the small étale
site of an algebraic space: the cokernel has vanishing stalks, the stalks being right exact, so
it is zero by conservativity of the stalks (Stacks 04K5). -/
theorem epi_of_epi_smallEtaleAbelianStalk_map {P Q : abelianSheaves.{u + 1} B S hS X}
    (φ : P ⟶ Q) (h : ∀ x : GeometricPoint B S hS X.1,
      Epi ((smallEtaleAbelianStalk B S hS x).map φ)) :
    Epi φ := by
  have hz : IsZero (cokernel φ) := by
    have hiso : IsIso (0 : cokernel φ ⟶ 0) := by
      refine isIso_of_isIso_stalkFunctor_map B S hS X.property _ fun x ↦ ?_
      have := h x
      have hC : IsZero ((smallEtaleAbelianStalk B S hS x).obj (cokernel φ)) :=
        (isZero_cokernel_of_epi ((smallEtaleAbelianStalk B S hS x).map φ)).of_iso
          (PreservesCokernel.iso (smallEtaleAbelianStalk B S hS x) φ)
      have h0 : IsZero
          ((smallEtaleAbelianStalk B S hS x).obj (0 : abelianSheaves.{u + 1} B S hS X)) :=
        (smallEtaleAbelianStalk B S hS x).map_isZero (isZero_zero _)
      exact ⟨⟨h0.to_ _, hC.eq_of_src _ _, h0.eq_of_src _ _⟩⟩
    exact (isZero_zero _).of_iso (asIso (0 : cokernel φ ⟶ 0))
  exact Preadditive.epi_of_isZero_cokernel φ hz

/-! ### The direct image along an integral universally injective morphism -/

section Integral

variable (g : W ⟶ Z) (hg : IsIntegralHom B S hS g.hom) (hgi : UniversallyInjective B S hS g.hom)

include hgi

/-- **The stalk of a direct image along an integral universally injective morphism.** For
`g : W ⟶ Z` integral and universally injective and a geometric point `w̄` of `W`, the stalk of
`g_*G` at `g(w̄)` is the stalk of `G` at `w̄`, naturally in the abelian sheaf `G`: the stalk of
an inverse image is the stalk at the image point (Stacks 04K2 part (4)), and the counit
`g^{-1}g_* ⟶ 𝟭` is invertible (Stacks 0AEH). -/
def smallEtaleAbelianPushforwardStalkIsoOfIntegral (w : GeometricPoint B S hS W.1) :
    smallEtaleAbelianPushforward.{u + 1} B S hS g
        (relativelyRepresentable_of_isIntegralHom B S hS g hg) ⋙
        smallEtaleAbelianStalk B S hS (geometricPointMap g.hom w) ≅
      smallEtaleAbelianStalk B S hS w := by
  let hr := relativelyRepresentable_of_isIntegralHom B S hS g hg
  have : ∀ K, IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS g hr).counit.app K) :=
    fun K ↦ smallEtaleAdjunctionCounitIsIsoAbelianOfIntegralUniversallyInjective.{u + 1}
      B S hS g hg hgi K
  have : IsIso (smallEtaleAbelianInverseImageAdjunction B S hS g hr).counit :=
    NatIso.isIso_of_isIso_app _
  exact Functor.isoWhiskerLeft _
      (smallEtaleAbelianInverseImageStalkIso B S hS g hr w).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (smallEtaleAbelianInverseImageAdjunction B S hS g hr).counit)
      (smallEtaleAbelianStalk B S hS w) ≪≫
    Functor.leftUnitor _

/-- **The direct image along an integral universally injective morphism is exact.** It is left
exact as a right adjoint; it preserves epimorphisms because at a geometric point lying on the
image its stalk is the stalk upstairs
(`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkIsoOfIntegral`), and off the image
it vanishes (Stacks 04FX). -/
theorem preservesFiniteColimits_smallEtaleAbelianPushforward_of_isIntegralHom :
    PreservesFiniteColimits (smallEtaleAbelianPushforward.{u + 1} B S hS g
      (relativelyRepresentable_of_isIntegralHom B S hS g hg)) := by
  let hr := relativelyRepresentable_of_isIntegralHom B S hS g hg
  rw [Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi]
  intro T hT
  refine ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).1 inferInstance
    T hT).1, ?_⟩
  have : Epi T.g := hT.epi_g
  refine epi_of_epi_smallEtaleAbelianStalk_map B S hS _ fun z ↦ ?_
  by_cases hz : z.image ∈ Set.range (pointsMap B S hS W.1 g.hom)
  · obtain ⟨w, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range_of_isIntegralHom B S hS g hg z hz
    let e := smallEtaleAbelianPushforwardStalkIsoOfIntegral B S hS g hg hgi w
    have hmap : (smallEtaleAbelianStalk B S hS (geometricPointMap g.hom w)).map
        ((smallEtaleAbelianPushforward.{u + 1} B S hS g hr).map T.g) =
        e.hom.app T.X₂ ≫ (smallEtaleAbelianStalk B S hS w).map T.g ≫ e.inv.app T.X₃ := by
      rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
      rfl
    rw [hmap]
    infer_instance
  · exact (isZero_stalkFunctor_abelianPushforward_of_notMem_of_isIntegralHom B S hS g hg
      T.X₃ z hz).epi _

end Integral

/-! ### The unit of a closed immersion on supported complexes, in any model -/

section Unit

variable [HasDerivedCategory.{w₁} (abelianSheaves.{u + 1} B S hS X)]
  [HasDerivedCategory.{w₂} (abelianSheaves.{u + 1} B S hS Z)]

/-- **The unit `K ⟶ i_*i^{-1}K` is invertible on complexes supported on `|Z|`**, for a closed
immersion `i : Z ⟶ X` and any models of the derived categories. Invertibility is tested on
cohomology sheaves, where it is Étale Cohomology 04CA part (2) for algebraic spaces,
`AlgebraicGeometry.Space.isIso_unit_app_of_supportOfSheaf_subset`. -/
theorem isIso_exactAdjunctionDerived_unit_app_of_supportOfSheaf_subset (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (K : DerivedCategory (abelianSheaves.{u + 1} B S hS X))
    (hK : ∀ n : ℤ, supportOfSheaf B S hS X.1
      ((DerivedCategory.homologyFunctor (abelianSheaves.{u + 1} B S hS X) n).obj K) ⊆
        Set.range (pointsMap B S hS Z.1 i.hom)) :
    letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    IsIso ((exactAdjunctionDerived
      (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)).unit.app K) := by
  let := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  set M := DerivedCategory.Q.objPreimage K
  have e := DerivedCategory.Q.objObjPreimageIso K
  have hQ : IsIso ((exactAdjunctionDerived
      (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)).unit.app
        (DerivedCategory.Q.obj M)) := by
    refine exactAdjunctionDerived_unit_isIso_of_homology _ _ fun n ↦ ?_
    refine isIso_unit_app_of_supportOfSheaf_subset B S hS i hi _ ?_
    have e' : (DerivedCategory.homologyFunctor (abelianSheaves.{u + 1} B S hS X) n).obj K ≅
        M.homology n :=
      ((DerivedCategory.homologyFunctor _ n).mapIso e).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (abelianSheaves.{u + 1} B S hS X) n).app M
    exact (supportOfSheaf_subset_of_isLocallySurjective B S hS X.1 X.property e'.hom).trans (hK n)
  exact ((exactAdjunctionDerived
    (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)).unit.isIso_app_iff_of_iso e).mp hQ

end Unit

/-! ### Existence of `Rf_*` -/

/-- Every complex of abelian sheaves on the small étale site of an algebraic space has a
K-injective resolution (Stacks 079P): the abelian sheaves form a Grothendieck abelian
category. -/
theorem exists_quasiIso_isKInjective_abelianSheaves (Y : AlgebraicSpaces B S hS)
    (K : CochainComplex (abelianSheaves.{u + 1} B S hS Y) ℤ) :
    ∃ (I : CochainComplex (abelianSheaves.{u + 1} B S hS Y) ℤ) (φ : K ⟶ I),
      I.IsKInjective ∧ QuasiIso φ := by
  have : IsGrothendieckAbelian.{u + 1} (abelianSheaves.{u + 1} B S hS Y) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _
  exact Stacks.Cohomology.moduleExistsKInjectiveResolution _ K

/-- **The total right derived functor `Rf_*` exists**, for an arbitrary morphism `f : Y ⟶ X` of
algebraic spaces and any model of the derived categories: abelian sheaves on the small étale
site form a Grothendieck abelian category, so every complex has a K-injective resolution
(Stacks 079P), and a functor out of the homotopy category is right derivable as soon as that is
so (Stacks 070K). -/
theorem hasRightDerivedFunctor_smallEtaleAbelianDirectImage
    [HasDerivedCategory.{w₁} (abelianSheaves.{u + 1} B S hS X)] (f : Y ⟶ X) :
    ((smallEtaleAbelianDirectImage B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS Y) (ComplexShape.up ℤ)) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
    u + 1, w₁, 0, u + 2, u + 2, 0}
    ((smallEtaleAbelianDirectImage B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_abelianSheaves B S hS Y)).1
  infer_instance

/-! ### Stacks 0AEQ -/

section Main

variable [HasDerivedCategory.{w₁} (abelianSheaves.{u + 1} B S hS Y)]
  [HasDerivedCategory.{w₂} (abelianSheaves.{u + 1} B S hS X)]
  [HasDerivedCategory.{w₃} AddCommGrpCat.{u + 1}]

/-- The objects of `D(Y_étale)` supported on `|f^{-1}Z|`: those all of whose cohomology sheaves
have support in the point set of `i' : f^{-1}Z ⟶ Y` (Stacks 08GF). -/
abbrev supportedOnPullbackProperty (i' : W ⟶ Y) :
    ObjectProperty (DerivedCategory (abelianSheaves.{u + 1} B S hS Y)) :=
  fun Q ↦ ∀ n : ℤ, supportOfSheaf B S hS Y.1
    ((DerivedCategory.homologyFunctor (abelianSheaves.{u + 1} B S hS Y) n).obj Q) ⊆
      Set.range (pointsMap B S hS W.1 i'.hom)

/-- **The comparison of Stacks 0AEQ as an isomorphism of functors on the supported
complexes.** On the full subcategory of `D(Y_étale)` of complexes supported on `|f^{-1}Z|`, the
geometric stalk at `x̄ = f(ȳ)` of `Rf_*` is the geometric stalk at `ȳ`, for every geometric
point `ȳ` of `Y`. -/
def stalkRightDerivedDirectImageIsoOnSupported (f : Y ⟶ X) (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (i' : W ⟶ Y) (f' : W ⟶ Z) (sq : IsPullback f' i' i f) (hf'int : IsIntegralHom B S hS f'.hom)
    (hf'inj : UniversallyInjective B S hS f'.hom)
    (RF : DerivedCategory (abelianSheaves.{u + 1} B S hS Y) ⥤
      DerivedCategory (abelianSheaves.{u + 1} B S hS X))
    (α : (smallEtaleAbelianDirectImage B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS Y) (ComplexShape.up ℤ))]
    (y : GeometricPoint B S hS Y.1) :
    (supportedOnPullbackProperty B S hS i').ι ⋙ RF ⋙
        (smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).mapDerivedCategory ≅
      (supportedOnPullbackProperty B S hS i').ι ⋙
        (smallEtaleAbelianStalk B S hS y).mapDerivedCategory := by
  let : HasDerivedCategory (abelianSheaves.{u + 1} B S hS W) := HasDerivedCategory.standard _
  have hi' : IsClosedImmersion B S hS i'.hom := isClosedImmersion_of_isPullback B S hS sq hi
  have hf'r := relativelyRepresentable_of_isIntegralHom B S hS f' hf'int
  let := additive_smallEtaleAbelianInverseImage B S hS i' hi'.rep
  let := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i' hi'.rep
  let := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i' hi'.rep
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i' hi'
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isIntegralHom B S hS f' hf'int
    hf'inj
  let P := supportedOnPullbackProperty B S hS i'
  let Pi' := smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep
  let V := smallEtaleAbelianInverseImage B S hS i' hi'.rep
  let adj := smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep
  let Sx := smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)
  let Sy := smallEtaleAbelianStalk B S hS y
  -- `f_* ∘ i'_*` is `i_* ∘ f'_*`, hence exact.
  let H := Pi' ⋙ smallEtaleAbelianDirectImage B S hS f
  let eH : H ≅ smallEtaleAbelianPushforward.{u + 1} B S hS f' hf'r ⋙
      smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep :=
    smallEtaleAbelianMixedSquareIso B S hS i' f' f i (i' ≫ f) hi'.rep hf'r hi.rep rfl sq.w
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits H := preservesFiniteColimits_of_natIso eH.symm
  have : PreservesFiniteLimits (H ⋙ Sx) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (H ⋙ Sx) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (Pi' ⋙ Sy) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (Pi' ⋙ Sy) := comp_preservesFiniteColimits _ _
  -- Stacks 015N for the square: `Rf_* ∘ i'_*` is the derived functor of the exact `H`.
  have := Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint Pi'
    (smallEtaleAbelianDirectImage B S hS f) RF α V adj
    (exists_quasiIso_isKInjective_abelianSheaves B S hS Y)
    (exists_quasiIso_isKInjective_abelianSheaves B S hS W)
  have : H.mapDerivedCategory.IsRightDerivedFunctor H.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS W) (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ H.mapDerivedCategoryFactorsh
  let eL : Pi'.mapDerivedCategory ⋙ RF ≅ H.mapDerivedCategory :=
    Functor.rightDerivedUnique _ _ (Stacks.DerivedFunctor.precomposeUnit Pi'
      (smallEtaleAbelianDirectImage B S hS f) RF α) H.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS W) (ComplexShape.up ℤ))
  -- The sheaf-level comparison, at every geometric point of `Y`.
  have : ∀ G, IsIso ((Functor.whiskerLeft Pi'
      (smallEtaleAbelianDirectImageStalkMap B S hS f y)).app G) := fun G ↦
    isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support_of_isPullback B S hS f i hi
      i' hi' f' hf'int hf'inj sq y (Pi'.obj G)
      (supportOfSheaf_smallEtaleAbelianPushforward_subset B S hS i' hi' G)
  have : IsIso (Functor.whiskerLeft Pi' (smallEtaleAbelianDirectImageStalkMap B S hS f y)) :=
    NatIso.isIso_of_isIso_app _
  let Φ : H ⋙ Sx ≅ Pi' ⋙ Sy :=
    asIso (Functor.whiskerLeft Pi' (smallEtaleAbelianDirectImageStalkMap B S hS f y))
  -- A supported complex is the direct image of its inverse image.
  have : ∀ Q : P.FullSubcategory, IsIso ((exactAdjunctionDerived adj).unit.app Q.obj) :=
    fun Q ↦ isIso_exactAdjunctionDerived_unit_app_of_supportOfSheaf_subset B S hS i' hi'
      Q.obj Q.property
  let η : P.ι ≅ (P.ι ⋙ V.mapDerivedCategory) ⋙ Pi'.mapDerivedCategory :=
    NatIso.ofComponents (fun Q ↦ asIso ((exactAdjunctionDerived adj).unit.app Q.obj))
      (fun φ ↦ (exactAdjunctionDerived adj).unit.naturality φ.hom)
  exact Functor.isoWhiskerRight η (RF ⋙ Sx.mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft (P.ι ⋙ V.mapDerivedCategory)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eL Sx.mapDerivedCategory ≪≫
        Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl (H ⋙ Sx)) ≪≫
        Functor.mapDerivedCategoryCongr Φ ≪≫
        (Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl (Pi' ⋙ Sy))).symm) ≪≫
    (Functor.isoWhiskerRight η Sy.mapDerivedCategory).symm

/-- **Stacks 0AEQ.** Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let
`i : Z ⟶ X` be a closed immersion and let `f^{-1}Z` be its inverse image, a cartesian square
`sq` with `f' : f^{-1}Z ⟶ Z` and `i' : f^{-1}Z ⟶ Y`, such that `f'` is integral and universally
injective. Let `ȳ` be a geometric point of `Y` and `x̄ = f(ȳ)`. Then for every object `Q` of
`D(Y_étale)` supported on `|f^{-1}Z|` there is an isomorphism `(Rf_*Q)_{x̄} ≅ Q_ȳ` in `D(Ab)`,
where `Rf_*` is any total right derived functor of the direct image of abelian sheaves along `f`
and the derived categories are arbitrary models. -/
@[stacks 0AEQ]
def stalkRightDerivedDirectImageIso (f : Y ⟶ X) (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (i' : W ⟶ Y) (f' : W ⟶ Z) (sq : IsPullback f' i' i f) (hf'int : IsIntegralHom B S hS f'.hom)
    (hf'inj : UniversallyInjective B S hS f'.hom)
    (RF : DerivedCategory (abelianSheaves.{u + 1} B S hS Y) ⥤
      DerivedCategory (abelianSheaves.{u + 1} B S hS X))
    (α : (smallEtaleAbelianDirectImage B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS Y) (ComplexShape.up ℤ))]
    (y : GeometricPoint B S hS Y.1)
    (Q : DerivedCategory (abelianSheaves.{u + 1} B S hS Y))
    (hQ : ∀ n : ℤ, supportOfSheaf B S hS Y.1
      ((DerivedCategory.homologyFunctor (abelianSheaves.{u + 1} B S hS Y) n).obj Q) ⊆
        Set.range (pointsMap B S hS W.1 i'.hom)) :
    (smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).mapDerivedCategory.obj
        (RF.obj Q) ≅
      (smallEtaleAbelianStalk B S hS y).mapDerivedCategory.obj Q :=
  (stalkRightDerivedDirectImageIsoOnSupported B S hS f i hi i' f' sq hf'int hf'inj RF α y).app
    ⟨Q, hQ⟩

/-- **Stacks 0AEQ: the comparison is natural** in the complex `Q` supported on `|f^{-1}Z|`,
being the value at `Q` of an isomorphism of functors. -/
@[stacks 0AEQ "naturality of the comparison in the supported complex"]
theorem stalkRightDerivedDirectImageIso_naturality (f : Y ⟶ X) (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (i' : W ⟶ Y) (f' : W ⟶ Z) (sq : IsPullback f' i' i f) (hf'int : IsIntegralHom B S hS f'.hom)
    (hf'inj : UniversallyInjective B S hS f'.hom)
    (RF : DerivedCategory (abelianSheaves.{u + 1} B S hS Y) ⥤
      DerivedCategory (abelianSheaves.{u + 1} B S hS X))
    (α : (smallEtaleAbelianDirectImage B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS Y) (ComplexShape.up ℤ))]
    (y : GeometricPoint B S hS Y.1)
    {Q Q' : DerivedCategory (abelianSheaves.{u + 1} B S hS Y)}
    (hQ : ∀ n : ℤ, supportOfSheaf B S hS Y.1
      ((DerivedCategory.homologyFunctor (abelianSheaves.{u + 1} B S hS Y) n).obj Q) ⊆
        Set.range (pointsMap B S hS W.1 i'.hom))
    (hQ' : ∀ n : ℤ, supportOfSheaf B S hS Y.1
      ((DerivedCategory.homologyFunctor (abelianSheaves.{u + 1} B S hS Y) n).obj Q') ⊆
        Set.range (pointsMap B S hS W.1 i'.hom)) (g : Q ⟶ Q') :
    (smallEtaleAbelianStalk B S hS (geometricPointMap f.hom y)).mapDerivedCategory.map
        (RF.map g) ≫
        (stalkRightDerivedDirectImageIso B S hS f i hi i' f' sq hf'int hf'inj RF α y Q' hQ').hom =
      (stalkRightDerivedDirectImageIso B S hS f i hi i' f' sq hf'int hf'inj RF α y Q hQ).hom ≫
        (smallEtaleAbelianStalk B S hS y).mapDerivedCategory.map g :=
  (stalkRightDerivedDirectImageIsoOnSupported B S hS f i hi i' f' sq hf'int hf'inj RF α
    y).hom.naturality (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) (ObjectProperty.homMk g)

end Main

end AlgebraicGeometry.Space

end
