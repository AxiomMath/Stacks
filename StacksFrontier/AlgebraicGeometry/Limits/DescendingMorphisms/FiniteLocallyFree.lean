module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.DegreeDecomposition
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.LimitFiniteLocallyFreeBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.UniversallyOpen

/-!
# Descending finite local freeness of a morphism along a limit of schemes

Let a scheme be the limit of a cofiltered inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, and let a morphism of quasi-compact and quasi-separated
schemes over the stage at a chosen index be locally of finite presentation. If its base change to
the limit is finite locally free, then its base change to some later stage already is, and if the
base change to the limit is moreover of constant degree `d`, then so is the base change to some
later stage.

## Main results

* `AlgebraicGeometry.exists_isFiniteLocallyFree_baseChange_of_isLimit` descends finite local
  freeness to a finite stage.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_baseChange_of_isLimit` descends finite local
  freeness of a fixed degree to a finite stage.

## Implementation notes

The plain statement is
`AlgebraicGeometry.exists_isFiniteLocallyFree_baseChange_of_limitBaseChange` with its two
hypotheses discharged by
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation` and
`AlgebraicGeometry.exists_isFinite_baseChange_of_isLimit`. It assumes the index category
essentially small in the universe of the schemes.

The fixed-degree refinement assumes instead that the objects and the morphisms of the index
category both lie in the universe of the schemes, which implies that essential smallness. It is
proved on the system of base changes of `Y₀`, `AlgebraicGeometry.baseChangeDiagram` with
`AlgebraicGeometry.baseChangeConeIsLimit`, indexed by `CategoryTheory.Over i₀`, using the degree
strata `Stacks.Morphisms.rankStratum`.

## References

* [Stacks Project, Tag 06AC](https://stacks.math.columbia.edu/tag/06AC)
* [Stacks Project, Tag 081D](https://stacks.math.columbia.edu/tag/081D)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-- A morphism over a stage of a cofiltered inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, essentially small in the universe of the schemes, which
is locally of finite presentation and whose base change to the limit is finite locally free, is
finite locally free after base change to some later stage. -/
@[stacks 06AC "the plain statement; the degree-d refinement is \
exists_isFiniteLocallyFreeOfRank_baseChange_of_isLimit. Carries the \
essential smallness of the index category, a hypothesis of the inputs without which the \
statement is false and which the source, having no universe hierarchy, states implicitly by \
indexing on a directed set"]
theorem exists_isFiniteLocallyFree_baseChange_of_isLimit
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    [Stacks.Morphisms.IsFiniteLocallyFree ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀),
      Stacks.Morphisms.IsFiniteLocallyFree ((Over.pullback (D.map g)).map f₀).left := by
  have : IsFinite ((Over.pullback (c.π.app i₀)).map f₀).left :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1 ‹_›).1
  exact exists_isFiniteLocallyFree_baseChange_of_limitBaseChange D c i₀ X₀ Y₀ f₀ hc
    @Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    (exists_isFinite_baseChange_of_isLimit D c hc i₀ X₀ Y₀ f₀)

/-- `baseChangeMap` has finite locally free rank `d` iff the base change of `f` does. -/
private theorem isFiniteLocallyFreeOfRank_baseChangeMap_iff {T B : Scheme.{u}} (g : T ⟶ B)
    (X Y : Over B) (f : X ⟶ Y) (d : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (baseChangeMap g X Y f) d ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((Over.pullback g).map f).left d :=
  (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff _ d).symm.trans
    ((baseChangeMap_prop_iff (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
      g X Y f).trans (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff _ d))

/-- A morphism over a stage of a cofiltered inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, indexed in the universe of the schemes, which is locally
of finite presentation and whose base change to the limit is finite locally free of degree `d`, is
finite locally free of degree `d` after base change to some later stage. -/
@[stacks 06AC "the degree-d refinement. Narrower than the plain statement in the index \
universes: the objects and the morphisms of the index category are both in the universe of the \
schemes, which is the form in which the cofiltered Tag 05F4 used to descend the degree stratum \
along the system of base changes of Y₀ is available, that system being indexed by the over \
category, which inherits both universes. The plain statement's essential smallness is implied \
by this narrowing rather than assumed"]
theorem exists_isFiniteLocallyFreeOfRank_baseChange_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((Over.pullback (c.π.app i₀)).map f₀).left d] :
    ∃ (i : I) (g : i ⟶ i₀),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((Over.pullback (D.map g)).map f₀).left d := by
  have hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) d :=
    (isFiniteLocallyFreeOfRank_baseChangeMap_iff _ X₀ Y₀ f₀ d).mpr inferInstance
  have := hq
  obtain ⟨hqfin, hqflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
        (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) d)
  obtain ⟨a₁, h₁⟩ : ∃ a : Over i₀, Stacks.Morphisms.IsFiniteLocallyFree
      ((baseChangeDiagramMap D i₀ f₀).app a) := by
    have : Stacks.Morphisms.IsFiniteLocallyFree ((Over.pullback (c.π.app i₀)).map f₀).left :=
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
    obtain ⟨i₁, g₁, h₁⟩ := exists_isFiniteLocallyFree_baseChange_of_isLimit D c hc i₀ X₀ Y₀ f₀
    exact ⟨Over.mk g₁, (baseChangeMap_prop_iff (@Stacks.Morphisms.IsFiniteLocallyFree)
      (D.map g₁) X₀ Y₀ f₀).mpr h₁⟩
  obtain ⟨h₁fin, h₁flat, h₁lfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp h₁
  set E : Set ((baseChangeDiagram D i₀ Y₀).obj a₁) :=
    (Stacks.Morphisms.rankStratum ((baseChangeDiagramMap D i₀ f₀).app a₁) d)ᶜ
  have hEopen : IsOpen E := (Stacks.Morphisms.isClosed_rankStratum _ d).isOpen_compl
  have hEretro : IsRetrocompact E := fun _ hUcomp _ =>
    hUcomp.inter_left (Stacks.Morphisms.rankStratum _ d).isOpen.isClosed_compl
  have hlimrank : ∀ y, ((baseChangeDiagramMap D i₀ f₀).app a₁).finrank
      ((baseChangeCone D c i₀ Y₀).π.app a₁ y) = d := fun y =>
    (Scheme.Hom.finrank_of_isPullback _ _ _ _
        (baseChangeCone_π_isPullback D i₀ f₀ c a₁) y).symm.trans
      ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ d).mp hq y)
  have hempty : ⇑((baseChangeCone D c i₀ Y₀).π.app a₁) ⁻¹' E = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
      hy ((Stacks.Morphisms.mem_rankStratum _).mpr (hlimrank y))
  have : ∀ {a b : Over i₀} (g : a ⟶ b),
      IsAffineHom ((baseChangeDiagram D i₀ Y₀).map g) := fun g =>
    isAffineHom_baseChangeDiagram_map D i₀ Y₀ g
  have : ∀ a : Over i₀, CompactSpace ((baseChangeDiagram D i₀ Y₀).obj a) := fun a =>
    compactSpace_baseChangeDiagram_obj D i₀ Y₀ a
  obtain ⟨a₂, g₂, hg₂⟩ := exists_empty_preimage_of_isConstructible
    (baseChangeDiagram D i₀ Y₀) (baseChangeCone D c i₀ Y₀)
    (baseChangeConeIsLimit D hc i₀ Y₀) a₁ _ (hEretro.isConstructible hEopen) hempty
  have h₂fin : IsFinite ((baseChangeDiagramMap D i₀ f₀).app a₂) :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (baseChangeDiagramMap_isPullback D i₀ f₀ g₂) h₁fin
  have h₂flat : Flat ((baseChangeDiagramMap D i₀ f₀).app a₂) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (baseChangeDiagramMap_isPullback D i₀ f₀ g₂) h₁flat
  have h₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((baseChangeDiagramMap D i₀ f₀).app a₂) d := by
    refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ d).mpr fun z => ?_
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (baseChangeDiagramMap_isPullback D i₀ f₀ g₂) z]
    refine (Stacks.Morphisms.mem_rankStratum _).mp ?_
    by_contra hmem
    exact Set.eq_empty_iff_forall_notMem.mp hg₂ z hmem
  exact ⟨a₂.left, a₂.hom, (isFiniteLocallyFreeOfRank_baseChangeMap_iff _ X₀ Y₀ f₀ d).mp h₂⟩

end AlgebraicGeometry

end
