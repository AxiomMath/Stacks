module

public import
    StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectAugmentationFunctorLeft
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Continuity
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectAugmented
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringForkVertexCosimplicial
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectTotalSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSiteCharts
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSiteEquivalence

/-!
# The two models of the total site of a simplicial object over `X`

Let `C` be a site with fibre products, `U` a simplicial object of `C` and `a : U ⟶ X` an
augmentation. The total site `(C/U)_total` of Stacks 09X8 has two models in the library: the
simplicial family of sites `n ↦ C/U_n` (`CategoryTheory.SimplicialOver.situation`), and the
simplicial semi-representable object `n ↦ {U_n ⟶ X}` of `C/X` with its componentwise localized
sites `n ↦ (C/X)/{U_n/X}` (`CategoryTheory.SimplicialSemiRepresentable.totalSituation`). The
iterated slice functors `(C/X)/(U_n/X) ⥤ C/U_n` form a morphism of simplicial sites between them
whose components are equivalences, continuous and cocontinuous; it carries the functor
`V/U_n ↦ V/X` to `j_total`. Hence descent along the augmentation holds in the first model as soon
as it holds in the second, which is Stacks 0DA8.

## Main results

* `CategoryTheory.SimplicialOver.isContinuous_of_ι_overSimplicialObjectComparison`: a functor
  out of `(C/U)_total` is continuous as soon as it is continuous in each simplicial degree.
* `CategoryTheory.SimplicialOver.semiRepresentableMorphismOverSimplicialObjectComparison`: the
  morphism of simplicial sites.
* `CategoryTheory.SimplicialOver.semiRepresentableAugmentationIsoOverSimplicialObjectComparison`:
  its total functor followed by `V/U_n ↦ V/X` is `j_total`.
* `SimplicialOver.descent_sheaves_augmented_hypercoveringBySimplicialObjectAugmented`: for a
  hypercovering `a : U ⟶ X`, restriction along `V/U_n ↦ V/X` is fully faithful on sheaves of sets
  with essential image the cartesian sheaves.

## References

* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering
  CategoryTheory.SemiRepresentable

universe u

namespace CategoryTheory.SimplicialOver

section Continuity

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)
  (U : SimplicialObject C)

/-- A functor out of the total site `(C/U)_total` is continuous as soon as its restriction to
every simplicial degree is. -/
theorem isContinuous_of_ι_overSimplicialObjectComparison {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D)
    (F : Grothendieck (slices U) ⥤ D)
    (hF : ∀ n, (Grothendieck.ι (slices U) n ⋙ F).IsContinuous (J.over (U.obj n)) K) :
    F.IsContinuous (totalTopology J U) K :=
  CocontinuousSimplicialSite.isContinuous_of_ι_overSimplicialObjectComparison (simplicialSite J U)
    K F fun n ↦ (topologyOfCoverings_sliceCoverings J U n).symm ▸ hF n

variable {U} {X : C} (a : U ⟶ (SimplicialObject.const C).obj X)

/-- The functor `V/U_n ↦ V/X` is continuous. -/
instance augmentationFunctor_isContinuous_overSimplicialObjectComparison :
    (augmentationFunctor U a).IsContinuous (totalTopology J U) (J.over X) :=
  isContinuous_of_ι_overSimplicialObjectComparison J U _ _ fun n ↦ by
    rw [ι_comp_augmentationFunctor]
    change (Over.map (augmentationApp U a n)).IsContinuous (J.over (U.obj n)) (J.over X)
    infer_instance

end Continuity

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {U : SimplicialObject C} {X : C}
  (a : U ⟶ (SimplicialObject.const C).obj X)

/-- In simplicial degree `n`, the iterated slice functor `(C/X)/(U_n/X) ⥤ C/U_n` on the single
component of the semi-representable object `{U_n ⟶ X}`. -/
abbrev semiRepresentableComparisonAppOverSimplicialObjectComparison (n : SimplexCategoryᵒᵖ) :
    ComponentOver ((associatedSimplicialObject.{u} U a).obj n) ⥤ Over (U.obj n) :=
  Sigma.desc fun _ ↦ (Over.mk (X := X) (a.app n)).iteratedSliceForward

/-- The iterated slice functors are compatible with the transitions of the two simplicial
families of sites. -/
def semiRepresentableComparisonOverSimplicialObjectComparison :
    SimplicialSemiRepresentable.slices (associatedSimplicialObject.{u} U a) ⟶ slices U where
  app n := (semiRepresentableComparisonAppOverSimplicialObjectComparison a n).toCatHom
  naturality {m n} α := by
    refine Cat.Hom.ext (CategoryTheory.Functor.ext ?_ ?_)
    · rintro ⟨⟨⟩, x⟩
      rfl
    · rintro ⟨⟨⟩, x⟩ ⟨⟨⟩, y⟩ ⟨f⟩
      exact ((Category.id_comp _).trans (Category.comp_id _)).symm

variable (J : GrothendieckTopology C)

/-- The iterated slice functor of degree `n` is cocontinuous. -/
instance semiRepresentableComparisonApp_isCocontinuous_overSimplicialObjectComparison
    (n : SimplexCategoryᵒᵖ) :
    (semiRepresentableComparisonAppOverSimplicialObjectComparison a n).IsCocontinuous
      (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
      (J.over (U.obj n)) where
  cover_lift {x S} hS := by
    obtain ⟨⟨⟩, x⟩ := x
    exact Functor.IsCocontinuous.cover_lift (G := (Over.mk (X := X) (a.app n)).iteratedSliceForward)
      (J := (J.over X).over (Over.mk (X := X) (a.app n)))
      (K := J.over (Over.mk (X := X) (a.app n)).left) hS

/-- The iterated slice functor of degree `n` is continuous. -/
instance semiRepresentableComparisonApp_isContinuous_overSimplicialObjectComparison
    (n : SimplexCategoryᵒᵖ) :
    (semiRepresentableComparisonAppOverSimplicialObjectComparison a n).IsContinuous
      (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
      (J.over (U.obj n)) where
  op_comp_isSheaf_of_types G :=
    isSheaf_componentwise (J.over X) _ fun _ ↦ Functor.IsContinuous.op_comp_isSheaf_of_types
      (F := (Over.mk (X := X) (a.app n)).iteratedSliceForward)
      (J := (J.over X).over (Over.mk (X := X) (a.app n)))
      (K := J.over (Over.mk (X := X) (a.app n)).left) G

/-- The iterated slice functor of degree `n` is an equivalence of categories. -/
instance semiRepresentableComparisonApp_isEquivalence_overSimplicialObjectComparison
    (n : SimplexCategoryᵒᵖ) :
    (semiRepresentableComparisonAppOverSimplicialObjectComparison a n).IsEquivalence := by
  let incl :=
    Sigma.incl (C := fun _ : PUnit.{u + 1} ↦ Over (Over.mk (X := X) (a.app n))) PUnit.unit
  have : incl.EssSurj := ⟨by rintro ⟨⟨⟩, x⟩; exact ⟨x, ⟨Iso.refl _⟩⟩⟩
  have : incl.IsEquivalence := { }
  have : (incl ⋙ semiRepresentableComparisonAppOverSimplicialObjectComparison a n).IsEquivalence :=
    (Over.mk (X := X) (a.app n)).iteratedSliceEquiv.isEquivalence_functor
  exact Functor.isEquivalence_of_comp_left incl _

/-- **The morphism of simplicial sites from the semi-representable model to `n ↦ C/U_n`.** In
degree `n` it is the iterated slice functor `(C/X)/(U_n/X) ⥤ C/U_n`. -/
def semiRepresentableMorphismOverSimplicialObjectComparison :
    CocontinuousSimplicialSite.Morphism
      (SimplicialSemiRepresentable.simplicialSite (J.over X) (associatedSimplicialObject.{u} U a))
      (simplicialSite J U) where
  hom := semiRepresentableComparisonOverSimplicialObjectComparison a
  isCocontinuous n := by
    have e₁ : topologyOfCoverings ((SimplicialSemiRepresentable.simplicialSite (J.over X)
        (associatedSimplicialObject.{u} U a)).coverage n) =
        componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n) :=
      SimplicialSemiRepresentable.topologyOfCoverings_sliceCoverings _ _ n
    have e₂ : topologyOfCoverings ((simplicialSite J U).coverage n) = J.over (U.obj n) :=
      topologyOfCoverings_sliceCoverings J U n
    rw [e₁, e₂]
    exact semiRepresentableComparisonApp_isCocontinuous_overSimplicialObjectComparison a J n

/-- The iterated slice functor of degree `n` is continuous for the topologies generated by the
coverings of the two simplicial sites. -/
theorem semiRepresentableMorphism_isContinuous_overSimplicialObjectComparison
    (n : SimplexCategoryᵒᵖ) :
    ((semiRepresentableMorphismOverSimplicialObjectComparison a J).hom.app n).toFunctor.IsContinuous
      (topologyOfCoverings ((SimplicialSemiRepresentable.simplicialSite (J.over X)
        (associatedSimplicialObject.{u} U a)).coverage n))
      (topologyOfCoverings ((simplicialSite J U).coverage n)) := by
  have e₁ : topologyOfCoverings ((SimplicialSemiRepresentable.simplicialSite (J.over X)
      (associatedSimplicialObject.{u} U a)).coverage n) =
      componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n) :=
    SimplicialSemiRepresentable.topologyOfCoverings_sliceCoverings _ _ n
  have e₂ : topologyOfCoverings ((simplicialSite J U).coverage n) = J.over (U.obj n) :=
    topologyOfCoverings_sliceCoverings J U n
  rw [e₁, e₂]
  exact semiRepresentableComparisonApp_isContinuous_overSimplicialObjectComparison a J n

/-- The degree `n` component of the morphism of simplicial sites is an equivalence of
categories. -/
instance semiRepresentableMorphism_isEquivalence_overSimplicialObjectComparison
    (n : SimplexCategoryᵒᵖ) :
    ((semiRepresentableMorphismOverSimplicialObjectComparison a J).hom.app
      n).toFunctor.IsEquivalence :=
  semiRepresentableComparisonApp_isEquivalence_overSimplicialObjectComparison a n

omit [HasPullbacks C] in
/-- The iterated slice functor does not change the underlying morphism of `C`. -/
theorem semiRepresentableComparisonApp_map_left_overSimplicialObjectComparison
    (n : SimplexCategoryᵒᵖ)
    {P Q : ComponentOver ((associatedSimplicialObject.{u} U a).obj n)} (g : P ⟶ Q) :
    ((semiRepresentableComparisonAppOverSimplicialObjectComparison a n).map g).left =
      ((componentOverForget _).map g).left := by
  obtain ⟨⟨⟩, A⟩ := P
  obtain ⟨⟨⟩, B⟩ := Q
  obtain ⟨g⟩ := g
  rfl

/-- **The two models of `V/U_n ↦ V/X`.** The functor between the total sites followed by
`V/U_n ↦ V/X` is the localization functor `j_total` of the semi-representable model. -/
def semiRepresentableAugmentationIsoOverSimplicialObjectComparison :
    (semiRepresentableMorphismOverSimplicialObjectComparison a J).totalFunctor ⋙
        augmentationFunctor U a ≅
      SimplicialSemiRepresentable.totalForget (associatedSimplicialObject.{u} U a) :=
  NatIso.ofComponents (fun x ↦ Over.isoMk (Iso.refl _) (by
      obtain ⟨n, ⟨⟨⟩, V⟩⟩ := x
      exact (Category.id_comp _).trans (Over.w V.hom).symm)) (by
    intro x y t
    ext
    change ((augmentationFunctor U a).map
        ((semiRepresentableMorphismOverSimplicialObjectComparison a J).totalFunctor.map t)).left
        ≫ 𝟙 _ = 𝟙 _ ≫ ((SimplicialSemiRepresentable.totalForget _).map t).left
    rw [Category.comp_id, Category.id_comp]
    refine (augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft a _).trans ?_
    refine Eq.trans ?_
      (congrArg CommaMorphism.left (SimplicialSemiRepresentable.totalForget_map _ t)).symm
    change ((eqToHom ((semiRepresentableComparisonOverSimplicialObjectComparison a).naturality
        t.base).symm).toNatTrans.app x.fiber ≫
      (semiRepresentableComparisonAppOverSimplicialObjectComparison a y.base).map t.fiber).left = _
    refine (Over.comp_left _ _ _ _ _).trans ?_
    refine ((congrArg (· ≫ _) ?_).trans (Category.id_comp _)).trans
      (semiRepresentableComparisonApp_map_left_overSimplicialObjectComparison a y.base t.fiber)
    exact (congrArg CommaMorphism.left (Cat.eqToHom_app _ _ _ x.fiber)).trans
      ((Comma.eqToHom_left (H := _)).trans (eqToHom_refl _ _)))

variable (P : Pretopology C)

/-- **Stacks 0DA8 (1) in the model `n ↦ C/U_n`.** Let `C` be a site with fibre products and
`a : U ⟶ X` a hypercovering of `X` in `C`. Restriction along `V/U_n ↦ V/X` is a fully faithful
functor `Sh(C/X) ⥤ Sh((C/U)_total)` whose essential image consists of the cartesian sheaves.
Here `J` is the topology generated by the pretopology `P` of the hypercovering. -/
theorem descent_sheaves_augmented_hypercoveringBySimplicialObjectAugmented
    {J : GrothendieckTopology C} (hJ : P.toGrothendieck = J)
    (h : IsHypercoveringAugmentation P U a) :
    Nonempty ((augmentationFunctor U a).sheafPushforwardContinuous (Type u)
      (totalTopology J U) (J.over X)).FullyFaithful ∧
      ∀ G : Sheaf (totalTopology J U) (Type u),
        ((augmentationFunctor U a).sheafPushforwardContinuous (Type u)
          (totalTopology J U) (J.over X)).essImage G ↔
          (situation J U).IsCartesianSheaf G := by
  subst hJ
  have hd :=
    SimplicialSemiRepresentable.descent_sheaves_augmented_hypercoveringBySimplicialObjectAugmented
      P U a h
  let S₁ := SimplicialSemiRepresentable.simplicialSite (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a)
  let S₂ := simplicialSite P.toGrothendieck U
  let F₁ : Grothendieck S₁.underlying ⥤ Over X :=
    SimplicialSemiRepresentable.totalForget (associatedSimplicialObject.{u} U a)
  let F₂ : Grothendieck S₂.underlying ⥤ Over X := augmentationFunctor U a
  have : F₁.IsContinuous (SimplicialCoverings.totalTopology S₁.underlying S₁.coverage)
      (P.toGrothendieck.over X) :=
    SimplicialSemiRepresentable.totalForget_isContinuous _ _
  have : F₂.IsContinuous (SimplicialCoverings.totalTopology S₂.underlying S₂.coverage)
      (P.toGrothendieck.over X) :=
    augmentationFunctor_isContinuous_overSimplicialObjectComparison P.toGrothendieck a
  have e : ∀ k : SimplexCategory, (CocontinuousSimplicialSite.situation S₂).componentTopology k =
      P.toGrothendieck.over (U.obj (op k)) := fun k ↦ topologyOfCoverings_sliceCoverings _ U (op k)
  exact (semiRepresentableMorphismOverSimplicialObjectComparison a
      P.toGrothendieck).descent_of_descent_totalSiteEquivalence
    (semiRepresentableMorphism_isContinuous_overSimplicialObjectComparison a _)
    (fun _ _ φ ↦
      SimplicialSemiRepresentable.isContinuous_componentOverMap_componentTopology_totalSiteCharts
        _ _ φ)
    (fun _ _ φ ↦ by
      rw [e, e]
      change (Over.map (U.map φ.op)).IsContinuous _ _
      infer_instance)
    (P.toGrothendieck.over X) F₁ F₂
    (semiRepresentableAugmentationIsoOverSimplicialObjectComparison a _) hd.1 hd.2.1

end CategoryTheory.SimplicialOver
