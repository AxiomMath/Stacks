module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.PlusTriangleOfDegreewiseSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.DerivedBaseChangeHomologyMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDerived

/-!
# The derived inverse image of a complex compared with a target complex

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ^•` a complex of abelian sheaves on `Y_étale` and
`𝒢^•` one on `X_étale`, both vanishing in degrees `< a`, and `ι : f^{-1}ℱ^• ⟶ 𝒢^•` a map of
complexes. Inverse image is exact, so the unit of its total right derived functor is invertible,
and `ι` induces a comparison `R f^{-1}ℱ^• ⟶ 𝒢^•` in `D^+(X_étale)`. This file constructs that
comparison along an arbitrary morphism and proves the two properties the colimit assertions of
[Stacks, Tag 0GIU] and [Stacks, Tag 0GIV] use: the comparisons compose along factorisations, and
the derived base change map on cohomology sheaves commutes with the connecting morphisms of
degreewise split short exact sequences of complexes.

At the projection `f_i : X ⟶ X_i` of a cone it has the same definition as
`Stacks.EtaleCohomology.LimitHigherDirectImage.complexPullbackComparison`.

## Main definitions

* `smallEtaleComplexPullbackComparison` — the comparison `R f^{-1}ℱ^• ⟶ 𝒢^•` attached to a map of
  complexes `ι : f^{-1}ℱ^• ⟶ 𝒢^•`.

## Main results

* `smallEtaleComplexPullbackComparison_paste` — the comparisons compose along factorisations.
* `derivedBaseChangeHomologyMap_smallEtaleComplexPullbackComparison_homologySequenceδ` — the
  derived base change map on cohomology sheaves commutes with the connecting morphisms of
  degreewise split short exact sequences of bounded below complexes.
* `derivedTransitionMap_eq_derivedBaseChangeHomologyMap`,
  `derivedProjectionMap_eq_derivedBaseChangeHomologyMap` — the comparison maps of
  [Stacks, Tag 0GIU] and [Stacks, Tag 0GIV] are derived base change maps on cohomology sheaves.

## References

* [Stacks Project, Tag 0GIU](https://stacks.math.columbia.edu/tag/0GIU)
* [Stacks Project, Tag 0GIV](https://stacks.math.columbia.edu/tag/0GIV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex (plusDerivedObj)

universe v u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

section Comparison

variable (a : ℤ)

/-- The comparison `R f^{-1}(ℱ^•) ⟶ 𝒢^•` in `D^+` attached to a map of complexes
`ι : f^{-1}ℱ^• ⟶ 𝒢^•` along a morphism of schemes `f`: inverse image is exact, so the unit of its
total right derived functor is invertible, and the comparison is the inverse of that unit
followed by the class of `ι`. -/
def smallEtaleComplexPullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ) [F.IsStrictlyGE a]
    (G : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    (ι : ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶ G) :
    (derivedPullbackAb f).obj (plusDerivedObj a F) ⟶ plusDerivedObj a G :=
  letI : IsIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnit :=
    (smallEtalePullbackAb f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  letI : IsIso ((smallEtalePullbackAb f).rightDerivedFunctorPlusUnit.app
      (CochainComplex.plusHomotopyObj a F)) :=
    NatIso.isIso_app_of_isIso _ _
  let ι' : (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj
      (CochainComplex.plusHomotopyObj a F) ⟶ CochainComplex.plusHomotopyObj a G :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι)
  inv ((smallEtalePullbackAb f).rightDerivedFunctorPlusUnit.app
      (CochainComplex.plusHomotopyObj a F)) ≫ DerivedCategory.Plus.Qh.map ι'

/-- The comparison `smallEtaleComplexPullbackComparison`, with the inverse of the unit written as
the inverse of the unit isomorphism. -/
theorem smallEtaleComplexPullbackComparison_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ) [F.IsStrictlyGE a]
    (G : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    (ι : ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶ G) :
    letI : IsIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnit :=
      (smallEtalePullbackAb f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    smallEtaleComplexPullbackComparison a f F G ι =
      (asIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnit).inv.app
          (CochainComplex.plusHomotopyObj a F) ≫
        DerivedCategory.Plus.Qh.map
          (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι) :
            (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj
                (CochainComplex.plusHomotopyObj a F) ⟶
              CochainComplex.plusHomotopyObj a G) := by
  simp only [smallEtaleComplexPullbackComparison, asIso_inv, NatIso.isIso_inv_app]

/-- **The comparisons `smallEtaleComplexPullbackComparison` compose along a factorisation.** For
`f = f₂ ≫ f₁` and maps of complexes `ι₁ : f₁^{-1}ℱ₀ ⟶ ℱ₁`, `ι₂ : f₂^{-1}ℱ₁ ⟶ ℱ₂` and
`ι : f^{-1}ℱ₀ ⟶ ℱ₂` with `ι` the composite of `f₂^{-1}ι₁` and `ι₂` through the comparison of
inverse images, the comparison of `ι` is the one of `ι₁` pulled back along `f₂`, followed by the
one of `ι₂`, through the comparison of derived inverse images. -/
theorem smallEtaleComplexPullbackComparison_paste {X₀ X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ X₀)
    (f₂ : X₂ ⟶ X₁) (f : X₂ ⟶ X₀) (hf : f = f₂ ≫ f₁)
    (F₀ : CochainComplex (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) ℤ) [F₀.IsStrictlyGE a]
    (F₁ : CochainComplex (Sheaf (smallEtaleTopology X₁) Ab.{u + 1}) ℤ) [F₁.IsStrictlyGE a]
    (F₂ : CochainComplex (Sheaf (smallEtaleTopology X₂) Ab.{u + 1}) ℤ) [F₂.IsStrictlyGE a]
    (ι₁ : ((smallEtalePullbackAb f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F₀ ⟶ F₁)
    (ι₂ : ((smallEtalePullbackAb f₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj F₁ ⟶ F₂)
    (ι : ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F₀ ⟶ F₂)
    (hι : (NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' f₂ f₁ f hf)
        (ComplexShape.up ℤ)).inv.app F₀ ≫
      ((smallEtalePullbackAb f₂).mapHomologicalComplex (ComplexShape.up ℤ)).map ι₁ ≫ ι₂ = ι) :
    smallEtaleComplexPullbackComparison a f F₀ F₂ ι =
      (smallEtaleDerivedPullbackAbPlusComp' f₁ f₂ f hf).inv.app (plusDerivedObj a F₀) ≫
        (derivedPullbackAb f₂).map (smallEtaleComplexPullbackComparison a f₁ F₀ F₁ ι₁) ≫
          smallEtaleComplexPullbackComparison a f₂ F₁ F₂ ι₂ := by
  let : IsIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnit :=
    (smallEtalePullbackAb f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let : IsIso (smallEtalePullbackAb f₁).rightDerivedFunctorPlusUnit :=
    (smallEtalePullbackAb f₁).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let : IsIso (smallEtalePullbackAb f₂).rightDerivedFunctorPlusUnit :=
    (smallEtalePullbackAb f₂).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have key := Functor.rightDerivedFunctorPlusCompIsoOfExact_inv_app (smallEtalePullbackAb f₁)
    (smallEtalePullbackAb f₂) (smallEtalePullbackAb f) (smallEtalePullbackAbComp' f₂ f₁ f hf)
    (CochainComplex.plusHomotopyObj a F₀)
  have hnat := (asIso (smallEtalePullbackAb f₂).rightDerivedFunctorPlusUnit).inv.naturality
    (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι₁) :
      (smallEtalePullbackAb f₁).mapHomotopyCategoryPlus.obj (CochainComplex.plusHomotopyObj a F₀) ⟶
        CochainComplex.plusHomotopyObj a F₁)
  have hq : ((Functor.mapHomotopyCategoryPlusCompIso (smallEtalePullbackAbComp' f₂ f₁ f hf)).inv.app
        (CochainComplex.plusHomotopyObj a F₀) ≫
      (smallEtalePullbackAb f₂).mapHomotopyCategoryPlus.map
        (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι₁) :
          (smallEtalePullbackAb f₁).mapHomotopyCategoryPlus.obj
              (CochainComplex.plusHomotopyObj a F₀) ⟶
            CochainComplex.plusHomotopyObj a F₁) ≫
      (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι₂) :
          (smallEtalePullbackAb f₂).mapHomotopyCategoryPlus.obj
              (CochainComplex.plusHomotopyObj a F₁) ⟶
            CochainComplex.plusHomotopyObj a F₂)) =
      (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι) :
          (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj
              (CochainComplex.plusHomotopyObj a F₀) ⟶
            CochainComplex.plusHomotopyObj a F₂) := by
    ext
    rw [← hι]
    rfl
  simp only [Functor.comp_map] at hnat
  rw [smallEtaleComplexPullbackComparison_eq, smallEtaleComplexPullbackComparison_eq,
    smallEtaleComplexPullbackComparison_eq,
    Functor.map_comp, ← hq, Functor.map_comp, Functor.map_comp]
  simp only [smallEtaleDerivedPullbackAbPlusComp', Category.assoc]
  rw [reassoc_of% hnat, ← reassoc_of% key]

section Delta

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

/-- **The derived base change map on cohomology sheaves commutes with the connecting morphisms
of degreewise split short exact sequences of bounded below complexes.** For a commutative square
`h ≫ f' = e ≫ g`, degreewise split sequences `S` on `T` and `S'` on `Y` of complexes vanishing in
degrees `< a`, and a morphism `ψ : e^{-1}S ⟶ S'` compatible with the splittings, the maps
attached to the comparisons of the third and first terms form a commuting square with the
connecting morphisms of `Rg_*` of the triangle of `S`, pulled back along `f'`, and of `Rh_*` of
the triangle of `S'`. -/
theorem derivedBaseChangeHomologyMap_smallEtaleComplexPullbackComparison_homologySequenceδ
    {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
    (w : h ≫ f' = e ≫ g)
    {𝒮 : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1}) ℤ)}
    (σ : ∀ n, (𝒮.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)
    [𝒮.X₁.IsStrictlyGE a] [𝒮.X₂.IsStrictlyGE a] [𝒮.X₃.IsStrictlyGE a]
    {𝒮' : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ)}
    (σ' : ∀ n, (𝒮'.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)
    [𝒮'.X₁.IsStrictlyGE a] [𝒮'.X₂.IsStrictlyGE a] [𝒮'.X₃.IsStrictlyGE a]
    (ψ : 𝒮.map ((smallEtalePullbackAb e).mapHomologicalComplex _) ⟶ 𝒮')
    (hs : ∀ n, (smallEtalePullbackAb e).map (σ n).s ≫ ψ.τ₂.f n = ψ.τ₃.f n ≫ (σ' n).s)
    (hr : ∀ n, (smallEtalePullbackAb e).map (σ n).r ≫ ψ.τ₁.f n = ψ.τ₂.f n ≫ (σ' n).r)
    (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    letI : IsIso (smallEtalePullbackAb e).rightDerivedFunctorPlusUnit :=
      (smallEtalePullbackAb e).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    derivedBaseChangeHomologyMap f' g h e w n₀ (plusDerivedObj a 𝒮.X₃) (plusDerivedObj a 𝒮'.X₃)
        (smallEtaleComplexPullbackComparison a e 𝒮.X₃ 𝒮'.X₃ ψ.τ₃) ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
        ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.obj
          (DerivedCategory.Plus.Qh.mapTriangle.obj
            (CochainComplex.trianglehPlusOfDegreewiseSplit a 𝒮' σ'))) n₀ n₁ hn =
      (smallEtalePullbackAb f').map
          ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
            ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj
              (DerivedCategory.Plus.Qh.mapTriangle.obj
                (CochainComplex.trianglehPlusOfDegreewiseSplit a 𝒮 σ))) n₀ n₁ hn) ≫
        derivedBaseChangeHomologyMap f' g h e w n₁ (plusDerivedObj a 𝒮.X₁)
          (plusDerivedObj a 𝒮'.X₁) (smallEtaleComplexPullbackComparison a e 𝒮.X₁ 𝒮'.X₁ ψ.τ₁) := by
  let : IsIso (smallEtalePullbackAb e).rightDerivedFunctorPlusUnit :=
    (smallEtalePullbackAb e).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have key := derivedBaseChangeHomologyMap_homologySequenceδ f' g h e w _ _
    (CochainComplex.rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom (smallEtalePullbackAb e) a
      σ σ' ψ hs hr) n₀ n₁ hn
  rw [CochainComplex.rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom_hom₃,
    CochainComplex.rightDerivedFunctorPlusTriangleOfDegreewiseSplitHom_hom₁] at key
  rw [smallEtaleComplexPullbackComparison_eq, smallEtaleComplexPullbackComparison_eq]
  exact key

end Delta

end Comparison

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)

/-- The transition comparison map of [Stacks, Tag 0GIU] and [Stacks, Tag 0GIV] is the derived
base change map on cohomology sheaves of the transition square. -/
theorem derivedTransitionMap_eq_derivedBaseChangeHomologyMap (p : ℤ) {i j : Iᵒᵖ} (a : i ⟶ j)
    (L : PlusAb (DX.obj j)) (L' : PlusAb (DX.obj i))
    (κ : (derivedPullbackAb (DX.map a)).obj L ⟶ L') :
    derivedTransitionMap γ p a L L' κ =
      derivedBaseChangeHomologyMap (DS.map a) (γ.app j) (γ.app i) (DX.map a)
        (transition_comm γ a) p L L' κ :=
  rfl

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS) (p : ℤ)

/-- The comparison map of [Stacks, Tag 0GIU] and [Stacks, Tag 0GIV] is the derived base change
map on cohomology sheaves of the projection square. -/
theorem derivedProjectionMap_eq_derivedBaseChangeHomologyMap (i : Iᵒᵖ) (L : PlusAb (DX.obj i))
    (M : PlusAb cX.pt) (κ : (derivedPullbackAb (cX.π.app i)).obj L ⟶ M) :
    derivedProjectionMap γ cX cS hcS p i L M κ =
      derivedBaseChangeHomologyMap (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
        (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) p L M κ :=
  rfl

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
