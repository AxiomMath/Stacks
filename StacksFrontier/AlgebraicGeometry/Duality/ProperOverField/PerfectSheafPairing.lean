module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SerreDualityLocallyFree

/-!
# Duality for a perfect pairing of sheaves into the dualizing module

Let `X` be a proper Cohen--Macaulay scheme over a field `k`, equidimensional of dimension `d`,
with dualizing module `ω_X` (`ω_X^• = ω_X[d]`, [Stacks, Tag 0FVZ]) and trace
`t : Hᵈ(X, ω_X) ⟶ k` ([Stacks, Tag 0FVW]). Let `ℰ` be a finite locally free `𝒪_X`-module, `ℱ` an
`𝒪_X`-module and `μ : ℱ ⊗ ℰ ⟶ ω_X` a pairing which is *perfect at the level of sheaves*: every
morphism `𝒯 ⊗ ℰ ⟶ ω_X` is `μ ∘ (g ⊗ 1)` for exactly one `g : 𝒯 ⟶ ℱ`, that is, `μ` identifies `ℱ`
with `ω_X ⊗ ℰ^∨`. Then for `i + j = d` the pairing

`Hⁱ(X, ℱ) × Hʲ(X, ℰ) ⟶ k,  (ξ, η) ↦ t(μ(ξ ∪ η))`

is perfect, for the cup product of Cohomology, Section 0FKU built from **any** one-point
comparison whose tensor comparison is invertible. This is [Stacks, Tag 0FW0]
(`Stacks.Duality.serrePairing_isPerfPair`, which is the case `ℱ = ω_X ⊗ ℰ^∨`, `μ = 1 ⊗ ε`, at the
comparison `onePointComparisonCanonical`) in the generality in which [Stacks, Tag 0FW4] applies it:
there `ℱ = Ω^p`, `ℰ = Ω^{d-p}`, `μ` is the wedge product, and the cup product is the one of the
canonical one-point comparison, for which the unit law of the cup product is available.

## Main definitions

* `Stacks.Duality.contractionMapOf`: `ℱ[0] ⊗^𝐋 ℰ[0] ⟶ (ℱ ⊗ ℰ)[0] ⟶ 𝒲[0]` for `μ : ℱ ⊗ ℰ ⟶ 𝒲`.
* `Stacks.Duality.cupContraction`: `ξ ⊗ η ↦ μ(ξ ∪ η)`.
* `Stacks.Duality.tracePairing`: the pairing `(ξ, η) ↦ t(μ(ξ ∪ η))`.

## Main results

* `Stacks.Duality.isIso_homEquiv_of_bijective`: a sheaf-level perfect pairing
  `ℱ ⊗ ℰ ⟶ 𝒲` identifies `ℱ` with `𝒲 ⊗ ℰ^∨`.
* `Stacks.Duality.isPerfPair_tracePairing`: **the pairing is perfect.**

## Implementation notes

The proof is the proof of `Stacks.Duality.bijective_serrePairing`, with two changes. The
representing object `L(A[-i])` of the one-point comparison `c` is compared with the one of
`onePointComparisonCanonical` by uniqueness of left adjoints of `RΓ(X, -)`
(`Stacks.Duality.tensorPullbackBaseShiftIsoOf`). The bijection
`Hom(P, ℱ[0]) ≃ Hom(P ⊗^𝐋 ℰ[0], ω_X[0])` is obtained from the one for `ω_X ⊗ ℰ^∨` through the
isomorphism `ℱ ≅ ω_X ⊗ ℰ^∨` which `μ` induces.

standard model: uses `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing`, which exists only
there.

## References

* [Stacks Project, Tag 0FW0](https://stacks.math.columbia.edu/tag/0FW0)
* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
* [Stacks Project, Tag 0FVY](https://stacks.math.columbia.edu/tag/0FVY)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections onePointComparisonCanonical
  GlobalCupProduct)
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

universe w u

namespace Stacks.Duality

/-! ### Comparing the representing objects of two one-point comparisons -/

section Comparison

attribute [local instance 100000] HasDerivedCategory.standard

variable {S : RingedSpace.{u, u}}
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Tensoring with `L(A[-i])` is the shift by `-i`**, for the left adjoint `L` of an arbitrary
one-point comparison: `L` is a left adjoint of `RΓ(S, -)`, hence isomorphic to the left adjoint of
`onePointComparisonCanonical`, for which this is `tensorPullbackBaseShiftIso`. -/
def tensorPullbackBaseShiftIsoOf (c : OnePointComparison S) (i : ℤ) :
    (derivedTensorProductFunctor S.sheaf).obj (c.pullback.obj (baseShift S i)) ≅
      shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (-i) :=
  (derivedTensorProductFunctor S.sheaf).mapIso
      ((c.adjunction.leftAdjointUniq (onePointComparisonCanonical S).adjunction).app
        (baseShift S i)) ≪≫
    tensorPullbackBaseShiftIso S i

/-- **Tensoring with `L(A[-i])` is bijective on morphisms**, for an arbitrary one-point
comparison. -/
theorem bijective_map_tensorPullbackBaseShiftOf (c : OnePointComparison S) (i : ℤ)
    (Y Y' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    Function.Bijective (fun g : Y ⟶ Y' => ((derivedTensorProductFunctor S.sheaf).obj
      (c.pullback.obj (baseShift S i))).map g) :=
  ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ (-i))).ofIso
    (tensorPullbackBaseShiftIsoOf c i).symm).map_bijective Y Y'

end Comparison

/-! ### Naturality of the comparison with the tensor product in degree zero -/

section Naturality

open Stacks.SheafOfModules.DerivedMonoidal (Mod)

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Mod R)]

/-- **The canonical map `ℱ[0] ⊗^𝐋 𝒢[0] ⟶ (ℱ ⊗ 𝒢)[0]` is natural in `ℱ`.** -/
theorem derivedTensorSingleToTensor_naturality_left {F F' : Mod R} (a : F ⟶ F')
    (G : Mod R) :
    ((derivedTensorProductFunctor R).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map a))).app
          (DerivedCategory.Q.obj (singleComplex G)) ≫ derivedTensorSingleToTensor F' G =
      derivedTensorSingleToTensor F G ≫ DerivedCategory.Q.map
        ((CochainComplex.singleFunctor _ 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).app G)) := by
  let s := CochainComplex.singleFunctor (Mod R) 0
  let T := derivedTensorProductFunctor R
  let toT := (canonicalDerivedTensorProduct R).toTensor
  let i := fun M : Mod R => (HomologicalComplex.mapBifunctorSingleRightIso
    (Stacks.SheafOfModules.Tensor.sheafTensor R) (s.obj M) G).hom
  let m := ((MonoidalCategory.tensorRight (C := Mod R) G).mapCochainComplexSingleFunctor 0).hom
  have hid : (T.obj (DerivedCategory.Q.obj (singleComplex F'))).map
      (DerivedCategory.Q.map (𝟙 (s.obj G))) = 𝟙 _ :=
    (congrArg (T.obj (DerivedCategory.Q.obj (singleComplex F'))).map
      (DerivedCategory.Q.map_id _)).trans
      (CategoryTheory.Functor.map_id _ _)
  have h₁ : (T.map (DerivedCategory.Q.map (s.map a))).app
        (DerivedCategory.Q.obj (singleComplex G)) ≫ toT (s.obj F') (s.obj G) =
      toT (s.obj F) (s.obj G) ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (s.map a) (𝟙 (s.obj G))
          (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)) := by
    refine Eq.trans ?_ ((canonicalDerivedTensorProduct R).toTensor_naturality
      (s.map a) (𝟙 (s.obj G)))
    exact congrArg (_ ≫ ·) ((congrArg (· ≫ toT (s.obj F') (s.obj G)) hid).trans
      (Category.id_comp _)).symm
  have h₂ : HomologicalComplex.mapBifunctorMap (s.map a) (𝟙 (s.obj G))
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) ≫ i F' ≫ m.app F' =
      i F ≫ m.app F ≫ s.map (((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).app G) :=
    (HomologicalComplex.mapBifunctorSingleRightIso_hom_naturality_assoc
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (s.obj F) G (s.map a) _).trans
      (congrArg (i F ≫ ·) (m.naturality a))
  calc (T.map (DerivedCategory.Q.map (s.map a))).app (DerivedCategory.Q.obj (singleComplex G)) ≫
        (toT (s.obj F') (s.obj G) ≫ DerivedCategory.Q.map (i F' ≫ m.app F'))
      = ((T.map (DerivedCategory.Q.map (s.map a))).app (DerivedCategory.Q.obj (singleComplex G)) ≫
          toT (s.obj F') (s.obj G)) ≫ DerivedCategory.Q.map (i F' ≫ m.app F') :=
        (Category.assoc _ _ _).symm
    _ = toT (s.obj F) (s.obj G) ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (s.map a) (𝟙 (s.obj G))
            (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) ≫
            i F' ≫ m.app F') :=
        (congrArg (· ≫ DerivedCategory.Q.map (i F' ≫ m.app F')) h₁).trans
          ((Category.assoc _ _ _).trans (congrArg (toT (s.obj F) (s.obj G) ≫ ·)
            (DerivedCategory.Q.map_comp _ _).symm))
    _ = (toT (s.obj F) (s.obj G) ≫ DerivedCategory.Q.map (i F ≫ m.app F)) ≫
          DerivedCategory.Q.map
            (s.map (((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).app G)) :=
        (congrArg (fun t => toT (s.obj F) (s.obj G) ≫ DerivedCategory.Q.map t) (h₂.trans
          (Category.assoc _ _ _).symm)).trans
          ((congrArg (toT (s.obj F) (s.obj G) ≫ ·) (DerivedCategory.Q.map_comp _ _)).trans
            (Category.assoc _ _ _).symm)


variable (E : Mod R) [HasRightDual E]

omit [HasDerivedCategory (SheafOfModules.DerivedMonoidal.Mod R)] in
/-- **A pairing of sheaves which is perfect identifies its first factor with `𝒲 ⊗ ℰ^∨`.** Let
`ℰ` have a left dual `ℰ^∨` and let `μ : ℱ ⊗ ℰ ⟶ 𝒲` be such that every morphism `𝒯 ⊗ ℰ ⟶ 𝒲` is
`μ ∘ (g ⊗ 1)` for exactly one `g : 𝒯 ⟶ ℱ`. Then the morphism `ℱ ⟶ 𝒲 ⊗ ℰ^∨` corresponding to `μ`
under `- ⊗ ℰ ⊣ - ⊗ ℰ^∨` is an isomorphism. -/
theorem isIso_homEquiv_of_bijective {F W : Mod R} (μ : F ⊗ E ⟶ W)
    (hμ : ∀ T : Mod R, Function.Bijective (fun g : T ⟶ F => g ▷ E ≫ μ)) :
    IsIso ((tensorRightAdjunction E Eᘁ).homEquiv F W μ) := by
  refine isIso_of_yoneda_map_bijective _ fun T => ?_
  have h : (fun g : T ⟶ F => g ≫ (tensorRightAdjunction E Eᘁ).homEquiv F W μ) =
      (tensorRightAdjunction E Eᘁ).homEquiv T W ∘ (fun g : T ⟶ F => g ▷ E ≫ μ) :=
    funext fun g => ((tensorRightAdjunction E Eᘁ).homEquiv_naturality_left g μ).symm
  rw [h]
  exact ((tensorRightAdjunction E Eᘁ).homEquiv T W).bijective.comp (hμ T)

/-- **`Hom(P, ℱ[0]) ≃ Hom(P ⊗^𝐋 ℰ[0], 𝒲[0])` for a perfect pairing `μ : ℱ ⊗ ℰ ⟶ 𝒲`**: the map
`ψ ↦ μ ∘ (ψ ⊗ ℰ[0])` is bijective, for every object `P` of `D(𝒪)`. Through the isomorphism
`ℱ ≅ 𝒲 ⊗ ℰ^∨` induced by `μ` (`isIso_homEquiv_of_bijective`) it is the bijection
`bijective_tensorRightSingle_comp_counit` of the adjunction `- ⊗ ℰ ⊣ - ⊗ ℰ^∨`. -/
theorem bijective_map_app_comp_derivedTensorSingleToTensor {F W : Mod R} (μ : F ⊗ E ⟶ W)
    (hμ : ∀ T : Mod R, Function.Bijective (fun g : T ⟶ F => g ▷ E ≫ μ))
    (P : DerivedCategory (Mod R)) :
    Function.Bijective (fun ψ : P ⟶ DerivedCategory.Q.obj (singleComplex F) =>
      ((derivedTensorProductFunctor R).map ψ).app (DerivedCategory.Q.obj (singleComplex E)) ≫
        derivedTensorSingleToTensor F E ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor (Mod R) 0).map μ)) := by
  let adj := tensorRightAdjunction E Eᘁ
  let α := adj.homEquiv F W μ
  let e : F ≅ W ⊗ Eᘁ := @asIso _ _ _ _ α (isIso_homEquiv_of_bijective E μ hμ)
  let eD := DerivedCategory.Q.mapIso ((CochainComplex.singleFunctor (Mod R) 0).mapIso e)
  have hμα : μ = α ▷ E ≫ adj.counit.app W :=
    ((adj.homEquiv F W).symm_apply_apply μ).symm.trans (adj.homEquiv_counit (g := α))
  have key : derivedTensorSingleToTensor F E ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (Mod R) 0).map μ) =
      ((derivedTensorProductFunctor R).map eD.hom).app (DerivedCategory.Q.obj (singleComplex E)) ≫
        derivedTensorSingleToTensor (W ⊗ Eᘁ) E ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor (Mod R) 0).map
            (adj.counit.app W)) := by
    rw [hμα, CategoryTheory.Functor.map_comp, DerivedCategory.Q.map_comp, ← Category.assoc]
    exact (congrArg (· ≫ _) (derivedTensorSingleToTensor_naturality_left α E).symm).trans
      (Category.assoc _ _ _)
  have hfun : (fun ψ : P ⟶ DerivedCategory.Q.obj (singleComplex F) =>
      ((derivedTensorProductFunctor R).map ψ).app (DerivedCategory.Q.obj (singleComplex E)) ≫
        derivedTensorSingleToTensor F E ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor (Mod R) 0).map μ)) =
      (fun ψ : P ⟶ DerivedCategory.Q.obj (singleComplex (W ⊗ Eᘁ)) =>
        ((derivedTensorProductFunctor R).map ψ).app (DerivedCategory.Q.obj (singleComplex E)) ≫
          derivedTensorSingleToTensor (W ⊗ Eᘁ) E ≫
            DerivedCategory.Q.map ((CochainComplex.singleFunctor (Mod R) 0).map
              (adj.counit.app W))) ∘ (fun ψ => ψ ≫ eD.hom) := by
    funext ψ
    rw [key, Function.comp_apply, CategoryTheory.Functor.map_comp, NatTrans.comp_app,
      Category.assoc]
  rw [hfun]
  exact (bijective_tensorRightSingle_comp_counit E P W).comp
    (by simpa [Iso.homCongr] using ((Iso.refl P).homCongr eD).bijective)

end Naturality

/-! ### Perfect pairings of sheaves -/

section SheafPairing

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **`ℱ[0] ⊗^𝐋 ℰ[0] ⟶ (ℱ ⊗ ℰ)[0] ⟶ 𝒲[0]`** for a pairing `μ : ℱ ⊗ ℰ ⟶ 𝒲`: the canonical map to
the tensor product in degree zero, followed by `μ`. -/
def contractionMapOf {F E W : X.Modules} (μ : tensorModule F E ⟶ W) :
    ((derivedTensorProductFunctor X.sheaf).obj (singleModule F)).obj (singleModule E) ⟶
      singleModule W :=
  derivedTensorSingleToTensor (R := X.sheaf) F E ≫
    DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map μ)

/-- `contractionMap` is `contractionMapOf` at `1 ⊗ ε`. -/
theorem contractionMap_eq_contractionMapOf (M E : X.Modules) :
    contractionMap M E = contractionMapOf (dualContraction M E) :=
  rfl

/-- **`ξ ⊗ η ↦ μ(ξ ∪ η)`**, `Hⁱ(X, ℱ) ⊗ Hʲ(X, ℰ) ⟶ Hⁿ(X, 𝒲)` for `i + j = n`: the cup product of
Section 0FKU attached to the global cup product `κ`, `Hⁱ⁺ʲ` of `contractionMapOf μ`, and
`Hⁱ⁺ʲ = Hⁿ`. -/
def cupContraction (κ : GlobalCupProduct X.toRingedSpace) {F E W : X.Modules}
    (μ : tensorModule F E ⟶ W) (i j n : ℤ) (h : i + j = n) :
    cohomologyModule (singleModule F) i ⊗ cohomologyModule (singleModule E) j ⟶
      cohomologyModule (singleModule W) n :=
  cupPairing κ _ _ i j ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) (i + j)).map
      ((baseSections X.toRingedSpace).map (contractionMapOf μ)) ≫
    eqToHom (by rw [h])

/-- `contractedCupProduct` is `cupContraction` at the canonical global cup product and `1 ⊗ ε`. -/
theorem contractedCupProduct_eq_cupContraction (M E : X.Modules) (i j n : ℤ) (h : i + j = n) :
    contractedCupProduct M E i j n h =
      cupContraction (Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical X.toRingedSpace)
        (dualContraction M E) i j n h :=
  rfl

end SheafPairing

/-! ### The pairing against the trace, and its perfectness -/

section Pairing

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The pairing `Hⁱ(X, ℱ) × Hʲ(X, ℰ) ⟶ k, (ξ, η) ↦ t(μ(ξ ∪ η))`** for `i + j = d` and a pairing
`μ : ℱ ⊗ ℰ ⟶ ω_X`: the cup product of Section 0FKU attached to the global cup product `κ`, then
`μ`, then the trace `t : Hᵈ(X, ω_X) ⟶ k` of [Stacks, Tag 0FVW] read through `ω_X^• = ω_X[d]`
([Stacks, Tag 0FVZ]), as a `k`-bilinear map. -/
def tracePairing (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (κ : GlobalCupProduct X.toRingedSpace) {F E : X.Modules}
    (μ : tensorModule F E ⟶ dualizingModule f) (i j : ℤ) (hij : i + j = d) :
    sheafCohomology f F i →ₗ[k] sheafCohomology f E j →ₗ[k] k :=
  let T := (topTrace f hCM hequi d hd).hom
  let B := (TensorProduct.mk ↑(baseRing X.toRingedSpace)
      ↑(cohomologyModule (singleModule F) i) ↑(cohomologyModule (singleModule E) j)).compr₂
    (cupContraction κ μ i j d hij).hom
  LinearMap.mk₂ k (fun ξ η => T (B ξ η))
    (fun ξ₁ ξ₂ η => (congrArg T (B.map_add₂ ξ₁ ξ₂ η)).trans (map_add T _ _))
    (fun c ξ η => (congrArg T (B.map_smul₂ (globalRingHom f c) ξ η)).trans (map_smul T c _))
    (fun ξ η₁ η₂ => (congrArg T ((B ξ).map_add η₁ η₂)).trans (map_add T _ _))
    (fun c ξ η => (congrArg T ((B ξ).map_smul (globalRingHom f c) η)).trans (map_smul T c _))

/-- The value of the pairing. -/
theorem tracePairing_apply (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (κ : GlobalCupProduct X.toRingedSpace) {F E : X.Modules}
    (μ : tensorModule F E ⟶ dualizingModule f) (i j : ℤ) (hij : i + j = d)
    (ξ : sheafCohomology f F i) (η : sheafCohomology f E j) :
    tracePairing f hCM hequi d hd κ μ i j hij ξ η =
      (topTrace f hCM hequi d hd).hom ((cupContraction κ μ i j d hij).hom (ξ ⊗ₜ η)) :=
  rfl

/-- `serrePairing` is `tracePairing` at the canonical global cup product and `1 ⊗ ε`. -/
theorem serrePairing_eq_tracePairing (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (E : X.Modules) (i j : ℤ) (hij : i + j = d) :
    serrePairing f hCM hequi d hd E i j hij =
      tracePairing f hCM hequi d hd
        (Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical X.toRingedSpace)
        (dualContraction (dualizingModule f) E) i j hij :=
  rfl

/-- A finite locally free module is quasi-coherent. -/
private theorem isQuasicoherent_of_isFiniteLocallyFree {E : X.Modules}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) : E.IsQuasicoherent :=
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.isFinitePresentation E hE
  _root_.isQuasicoherent_of_isFinitePresentation E

/-- **The pairing is perfect on the left**: for a one-point comparison `c` with invertible tensor
comparison, `ℰ` finite locally free and `μ : ℱ ⊗ ℰ ⟶ ω_X` perfect at the level of sheaves, every
linear form on `Hʲ(X, ℰ)` is `η ↦ t(μ(ξ ∪ η))` for exactly one `ξ ∈ Hⁱ(X, ℱ)`. -/
theorem bijective_tracePairing (c : OnePointComparison X.toRingedSpace)
    [IsIso c.tensorComparison] (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    {F E : X.Modules} (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (μ : tensorModule F E ⟶ dualizingModule f)
    (hμ : ∀ T : X.Modules, Function.Bijective (fun g : T ⟶ F =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map g).app E ≫ μ))
    (i j : ℤ) (hij : i + j = d) :
    Function.Bijective (tracePairing f hCM hequi d hd (globalCupProduct c) μ i j hij) := by
  let P := c.pullback.obj (baseShift X.toRingedSpace i)
  let T := derivedTensorProductFunctor X.toRingedSpace.sheaf
  let ω := dualizingModule f
  let G0 := singleModule F
  let E0 := singleModule E
  let Z := (T.obj P).obj E0
  -- `ξ̃ ↦ (1 ⊗ ε) ∘ (ξ̃ ⊗ ℰ[0])` is bijective
  let Ψ : (P ⟶ G0) → (Z ⟶ singleModule ω) := fun ψ => (T.map ψ).app E0 ≫ contractionMapOf μ
  have hΨ : Function.Bijective Ψ := by
    let := hasRightDualOfFiniteLocallyFree E hE
    exact bijective_map_app_comp_derivedTensorSingleToTensor (R := X.toRingedSpace.sheaf) E μ hμ P
  -- duality against the trace
  have hZ : ∀ n : ℤ, ((@DerivedCategory.homologyFunctor X.Modules _ _
      (Scheme.Modules.hasDerivedCategory X) n).obj
      ((Scheme.Modules.derivedModelEquiv X).functor.obj Z)).IsQuasicoherent := by
    have hEq := isQuasicoherent_of_isFiniteLocallyFree hE
    let eZ : (Scheme.Modules.derivedModelEquiv X).functor.obj Z ≅
        ((@DerivedCategory.singleFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) 0).obj
          E)⟦-i⟧ :=
      (Scheme.Modules.derivedModelEquiv X).functor.mapIso
          ((tensorPullbackBaseShiftIsoOf c i).app E0) ≪≫
        ((Scheme.Modules.derivedModelEquiv X).functor.commShiftIso (-i)).app E0 ≪≫
        (shiftFunctor _ (-i)).mapIso ((Scheme.Modules.derivedModelEquivCompQIso X).app
          ((CochainComplex.singleFunctor X.Modules 0).obj E))
    have hq : ∀ m : ℤ, ((@DerivedCategory.homologyFunctor X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) m).obj ((@DerivedCategory.singleFunctor X.Modules _ _
          (Scheme.Modules.hasDerivedCategory X) 0).obj E)).IsQuasicoherent := by
      let := Scheme.Modules.hasDerivedCategory X
      intro m
      rcases lt_trichotomy m 0 with hm | rfl | hm
      · exact isQuasicoherent_of_isZero X _
          (DerivedCategory.isZero_of_isGE
            ((DerivedCategory.singleFunctor X.Modules 0).obj E) 0 m hm)
      · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app E).symm hEq
      · exact isQuasicoherent_of_isZero X _
          (DerivedCategory.isZero_of_isLE
            ((DerivedCategory.singleFunctor X.Modules 0).obj E) 0 m hm)
    intro n
    let iso₁ := ((@DerivedCategory.homologyFunctor X.Modules _ _
      (Scheme.Modules.hasDerivedCategory X) 0).shiftIso (-i) n (-i + n) rfl).app
        ((@DerivedCategory.singleFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) 0).obj
          E)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (iso₁.symm ≪≫ (@DerivedCategory.homologyFunctor X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) n).mapIso eZ.symm)
      (hq (-i + n))
  have hB3 := bijective_map_comp_topTrace f hCM hequi d hd Z hZ
  -- `η ↦ gᵢ ∪ η`
  let cupGen : sheafCohomology f E j ⟶
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule Z d) :=
    (ModuleCat.restrictScalars.{u} (globalRingHom f)).map
      (ModuleCat.ofHom ((cupPairing (globalCupProduct c) P E0 i j).hom ∘ₗ
        TensorProduct.mk _ _ _ (generatingClass c i)) ≫ eqToHom (by rw [hij]))
  have hcupGen : Function.Bijective cupGen.hom := by
    have hiso : IsIso (c.pullback.map (pinnedSplitting X.toRingedSpace i j) ≫
        c.tensorComparison.app (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j)) := by
      have : IsIso (c.tensorComparison.app
          (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j)) :=
        NatIso.isIso_app_of_isIso _ _
      infer_instance
    have h₁ : Function.Bijective (fun η : cohomologyModule E0 j =>
        (cupPairing (globalCupProduct c) P E0 i j).hom (generatingClass c i ⊗ₜ η)) := by
      let χ' := asIso (c.pullback.map (pinnedSplitting X.toRingedSpace i j) ≫
        c.tensorComparison.app (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j))
      have hχ : Function.Bijective (fun g :
          (T.obj (c.pullback.obj (baseShift X.toRingedSpace i))).obj
          (c.pullback.obj (baseShift X.toRingedSpace j)) ⟶ Z => χ'.hom ≫ g) :=
        ⟨fun g₁ g₂ h => (Iso.cancel_iso_hom_left χ' g₁ g₂).1 h,
          fun g => ⟨χ'.inv ≫ g, χ'.hom_inv_id_assoc g⟩⟩
      have hR : Function.Bijective
          ((fun g => (c.pullback.map (pinnedSplitting X.toRingedSpace i j) ≫
              c.tensorComparison.app (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j)) ≫
            (T.obj P).map g) ∘ elementAdjunct c E0 j) :=
        hχ.comp ((bijective_map_tensorPullbackBaseShiftOf c i _ _).comp
          (bijective_elementAdjunct c E0 j))
      have hEq : (elementAdjunct c Z (i + j)) ∘ (fun η : cohomologyModule E0 j =>
          (cupPairing (globalCupProduct c) P E0 i j).hom (generatingClass c i ⊗ₜ η)) =
          (fun g => (c.pullback.map (pinnedSplitting X.toRingedSpace i j) ≫
              c.tensorComparison.app (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j)) ≫
            (T.obj P).map g) ∘ elementAdjunct c E0 j :=
        funext fun η => (elementAdjunct_cupPairing_generatingClass c E0 i j η).trans
          (Category.assoc _ _ _).symm
      rw [← hEq] at hR
      exact (Function.Bijective.of_comp_iff' (bijective_elementAdjunct c Z (i + j)) _).1 hR
    have h₂ : Function.Bijective (eqToHom (show cohomologyModule Z (i + j) =
        cohomologyModule Z d by rw [hij])).hom :=
      (eqToIso (show cohomologyModule Z (i + j) = cohomologyModule Z d by
        rw [hij])).toLinearEquiv.bijective
    exact h₂.comp h₁
  let e := LinearEquiv.ofBijective cupGen.hom hcupGen
  have hformula : ∀ (ξ : sheafCohomology f F i) (η : sheafCohomology f E j),
      tracePairing f hCM hequi d hd (globalCupProduct c) μ i j hij ξ η =
        ((ModuleCat.restrictScalars.{u} (globalRingHom f)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) d).map
            ((baseSections X.toRingedSpace).map (Ψ (elementAdjunct c G0 i ξ)))) ≫
          topTrace f hCM hequi d hd).hom (cupGen.hom η) := by
    intro ξ η
    rw [tracePairing_apply]
    refine congrArg (topTrace f hCM hequi d hd).hom ?_
    let H := fun n : ℤ =>
      DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) n
    let ξ' := elementAdjunct c G0 i ξ
    let y := (cupPairing (globalCupProduct c) P E0 i j).hom (generatingClass c i ⊗ₜ η)
    have h₁ := map_elementAdjunct_generatingClass c G0 i ξ
    have h₂ := cupPairing_naturality_apply (globalCupProduct c) ξ' (𝟙 E0) i j
      (generatingClass c i) η
    have hT : (Functor.uncurry.obj T).map (ξ' ×ₘ 𝟙 E0) = (T.map ξ').app E0 :=
      (congrArg (fun g => (T.map ξ').app E0 ≫ g) ((T.obj G0).map_id E0)).trans
        (Category.comp_id _)
    have h₃ := eqToHom_comp_homologyFunctor_map (X := X) (Ψ ξ') hij
    have hid : ((H j).map ((baseSections X.toRingedSpace).map (𝟙 E0))).hom η = η :=
      congrArg (fun φ => φ.hom η)
        ((congrArg (H j).map ((baseSections X.toRingedSpace).map_id E0)).trans ((H j).map_id _))
    let castω : cohomologyModule (singleModule ω) (i + j) ⟶ cohomologyModule (singleModule ω) d :=
      eqToHom (by rw [hij])
    let Hβ := (H (i + j)).map ((baseSections X.toRingedSpace).map (contractionMapOf μ))
    have e₁ : (cupContraction (globalCupProduct c) μ i j d hij).hom (ξ ⊗ₜ η) =
        castω.hom (Hβ.hom ((cupPairing (globalCupProduct c) G0 E0 i j).hom (ξ ⊗ₜ η))) := rfl
    have e₂ : (cupPairing (globalCupProduct c) G0 E0 i j).hom (ξ ⊗ₜ η) =
        ((H (i + j)).map ((baseSections X.toRingedSpace).map ((T.map ξ').app E0))).hom y :=
      (congrArg (fun z => (cupPairing (globalCupProduct c) G0 E0 i j).hom z)
        (congrArg₂ (fun a b => a ⊗ₜ[↑(baseRing X.toRingedSpace)] b) h₁.symm hid.symm)).trans
        (h₂.trans (congrArg (fun φ => ((H (i + j)).map
          ((baseSections X.toRingedSpace).map φ)).hom y) hT))
    have hcomp : (H (i + j)).map ((baseSections X.toRingedSpace).map ((T.map ξ').app E0)) ≫ Hβ =
        (H (i + j)).map ((baseSections X.toRingedSpace).map (Ψ ξ')) :=
      ((H (i + j)).map_comp _ _).symm.trans
        (congrArg (H (i + j)).map ((baseSections X.toRingedSpace).map_comp _ _).symm)
    exact e₁.trans ((congrArg (fun z => castω.hom (Hβ.hom z)) e₂).trans
      ((congrArg castω.hom (congrArg (fun φ => φ.hom y) hcomp)).trans
        (congrArg (fun φ => φ.hom y) h₃)))
  have hprecomp : Function.Bijective (fun φ : (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj
      (cohomologyModule Z d) ⟶ ModuleCat.of k k => φ.hom ∘ₗ e.toLinearMap) :=
    (e.arrowCongr (LinearEquiv.refl k k)).symm.bijective.comp ModuleCat.homEquiv.bijective
  have heq : (tracePairing f hCM hequi d hd (globalCupProduct c) μ i j hij : _ → _) =
      (fun φ : (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule Z d) ⟶
          ModuleCat.of k k => φ.hom ∘ₗ e.toLinearMap) ∘
        (fun β : Z ⟶ singleModule ω =>
          (ModuleCat.restrictScalars.{u} (globalRingHom f)).map
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) d).map
              ((baseSections X.toRingedSpace).map β)) ≫ topTrace f hCM hequi d hd) ∘ Ψ ∘
        elementAdjunct c G0 i :=
    funext fun ξ => LinearMap.ext (hformula ξ)
  rw [heq]
  exact hprecomp.comp (hB3.comp (hΨ.comp (bijective_elementAdjunct c G0 i)))


/-- **Duality for a perfect pairing of sheaves into the dualizing module.** Let `X` be a proper
Cohen--Macaulay scheme over a field `k`, equidimensional of dimension `d`, with dualizing module
`ω_X` and trace `t : Hᵈ(X, ω_X) ⟶ k`. Let `ℰ` be a finite locally free `𝒪_X`-module and
`μ : ℱ ⊗ ℰ ⟶ ω_X` a pairing such that every morphism `𝒯 ⊗ ℰ ⟶ ω_X` is `μ ∘ (g ⊗ 1)` for exactly
one `g : 𝒯 ⟶ ℱ`. Then for `i + j = d` the pairing `Hⁱ(X, ℱ) × Hʲ(X, ℰ) ⟶ k`,
`(ξ, η) ↦ t(μ(ξ ∪ η))`, is perfect, for the cup product of Section 0FKU attached to any one-point
comparison with invertible tensor comparison. -/
theorem isPerfPair_tracePairing (c : OnePointComparison X.toRingedSpace)
    [IsIso c.tensorComparison] (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    {F E : X.Modules} (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (μ : tensorModule F E ⟶ dualizingModule f)
    (hμ : ∀ T : X.Modules, Function.Bijective (fun g : T ⟶ F =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map g).app E ≫ μ))
    (i j : ℤ) (hij : i + j = d) :
    (tracePairing f hCM hequi d hd (globalCupProduct c) μ i j hij).IsPerfPair := by
  have : E.IsQuasicoherent := isQuasicoherent_of_isFiniteLocallyFree hE
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E :=
    ⟨hE.exists_isFiniteLocallyFreeData⟩
  have : E.IsFiniteType :=
    (Stacks.FiniteLocallyFree.isLocallyFree_isFiniteType_isFinitePresentation E).2.1
  have : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType E
  have := finiteDimensional_sheafCohomology f E j
  exact LinearMap.IsPerfPair.of_bijective _
    (bijective_tracePairing f c hCM hequi d hd hE μ hμ i j hij)

end Pairing

end Stacks.Duality
