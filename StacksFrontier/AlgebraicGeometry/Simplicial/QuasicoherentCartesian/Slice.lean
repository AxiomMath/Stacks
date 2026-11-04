module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesian
public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSitesGeneral
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCartesianOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality

/-!
# Slices of the total site of a simplicial site, and their components

For a simplicial-site situation `S` (Stacks 09WE) and an object `Q` of the degree-`n` component,
the degree-`n` component inclusion `Cₙ ⥤ C_total` localizes to a functor
`μ : Cₙ/Q ⥤ C_total/Q`, and more generally an arrow `c : P ⟶ Q` of the total category, with
`P` in degree `k`, gives `λ_c : C_k/P ⥤ C_total/Q`. This file sets up the restrictions of
sheaves of modules along these functors, the extension `μ_!` left adjoint to restriction along
`μ`, and their behaviour on the structure sheaf.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.CartesianSlice.sliceRestriction`: restriction along `μ`.
* `CategoryTheory.SimplicialSiteSituation.CartesianSlice.sliceExtension`: its left adjoint.
* `CategoryTheory.SimplicialSiteSituation.CartesianSlice.sliceRestrictionAt`: restriction along
  `λ_c`.

## Main results

* `CategoryTheory.GrothendieckTopology.coversTop_map_of_coversTop_obj`: a continuous functor
  whose image of the final object is covered carries a family covering the final object to one.
* `SheafOfModules.coversTop_hasGlobalPresentation`: the objects over which a quasi-coherent
  module has a global presentation cover the final object.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- **Covering families travel along a continuous functor whose image covers the final object.**
If the objects `u T` cover the final object of the target and `Y` covers the final object of the
source, then the objects `u (Y i)` cover the final object of the target. -/
theorem coversTop_map_of_coversTop_obj (u : D ⥤ C) [u.IsContinuous K J] (hu : J.CoversTop u.obj)
    {I : Type*} {Y : I → D} (hY : K.CoversTop Y) : J.CoversTop fun i => u.obj (Y i) := by
  intro A
  refine J.transitive (hu A) _ fun B k hk => ?_
  obtain ⟨T, ⟨g⟩⟩ := hk
  refine J.superset_covering ?_ (J.pullback_stable g
    ((CoverPreserving.of_isContinuous u K J).cover_preserve (hY T)))
  rintro B' k' ⟨Z, p, q, ⟨i, ⟨b⟩⟩, -⟩
  exact ⟨i, ⟨q ≫ u.map b⟩⟩

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules

/-- On a site, the objects over which a quasi-coherent module has a global presentation cover the
final object. -/
theorem coversTop_hasGlobalPresentation {D : Type*} [Category* D] {K : GrothendieckTopology D}
    {R : Sheaf K RingCat.{u}} (F : SheafOfModules.{u} R) (hF : F.IsQuasicoherentOnSite) :
    K.CoversTop fun i : {Z : D // (F.over Z).HasGlobalPresentation} => i.1 := by
  intro X
  obtain ⟨I, V, f, hsieve, hpres⟩ := hF.locally_hasGlobalPresentation X
  refine K.superset_covering ?_ hsieve
  rintro Z g ⟨W, h, k, ⟨i⟩, rfl⟩
  exact ⟨⟨V i, hpres i⟩, ⟨h⟩⟩

end SheafOfModules

namespace CategoryTheory.SimplicialSiteSituation.CartesianSlice

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})

/-- The categories of the simplicial-site situation are small, in the universe they live in. -/
instance (priority := high) smallComponent (k : SimplexCategory) :
    Small.{u, u} (S.component k) := small_self _

/-- The total category of the simplicial-site situation is small. -/
instance (priority := high) smallTotalCategory : Small.{u, u} S.totalCategory := small_self _

section Inclusion

variable {n : SimplexCategory} (Q : S.component n)

/-- The degree-`n` component inclusion, localized at `Q`. -/
abbrev sliceInclusion : Over Q ⥤ Over ((componentFunctor S n).obj Q) :=
  Over.post (componentFunctor S n)

/-- The identity of the degree-`n` slice structure sheaf, read as the structure map of the slice
inclusion; named so that instance search sees the shape of a structure map. -/
def sliceInclusionRing :
    (S.componentRingSheaf O n).over Q ⟶
      ((sliceInclusion S Q).sheafPushforwardContinuous RingCat.{u}
        ((S.componentTopology n).over Q) (S.totalTopology.over _)).obj
        (O.over ((componentFunctor S n).obj Q)) := 𝟙 _

/-- Restriction of modules on the total slice at `Q` to the degree-`n` slice at `Q`. -/
abbrev sliceRestriction :
    SheafOfModules.{u} (O.over ((componentFunctor S n).obj Q)) ⥤
      SheafOfModules.{u} ((S.componentRingSheaf O n).over Q) :=
  SheafOfModules.pushforward.{u} (F := sliceInclusion S Q) (𝟙 ((S.componentRingSheaf O n).over Q))

/-- Restriction to the degree-`n` slice is a right adjoint. -/
instance isRightAdjoint_sliceRestriction : (sliceRestriction S O Q).IsRightAdjoint :=
  inferInstanceAs (SheafOfModules.pushforward.{u} (sliceInclusionRing S O Q)).IsRightAdjoint

/-- Restriction to the degree-`n` slice is a left adjoint. -/
instance isLeftAdjoint_sliceRestriction : (sliceRestriction S O Q).IsLeftAdjoint :=
  (Stacks.SheafOfModules.RestrictRan.sheafAdjunction (sliceInclusion S Q)
    ((S.componentTopology n).over Q) (S.totalTopology.over _) (O.over _)).isLeftAdjoint

/-- The degree-`n` restriction of the structure sheaf of the total slice is the structure sheaf. -/
abbrev sliceRestrictionUnitHom :
    SheafOfModules.unit ((S.componentRingSheaf O n).over Q) ⟶
      (sliceRestriction S O Q).obj (SheafOfModules.unit _) :=
  SheafOfModules.unitToPushforwardObjUnit (F := sliceInclusion S Q)
    (J := (S.componentTopology n).over Q) (K := S.totalTopology.over _)
    (S := (S.componentRingSheaf O n).over Q) (R := O.over ((componentFunctor S n).obj Q))
    (𝟙 ((S.componentRingSheaf O n).over Q))

/-- `sliceRestrictionUnitHom` is invertible: the degree-`n` restriction of the structure sheaf
of the total slice really is the structure sheaf. -/
instance isIso_sliceRestrictionUnitHom : IsIso (sliceRestrictionUnitHom S O Q) :=
  @AlgebraicGeometry.SimplicialScheme.isIso_unitToPushforwardObjUnit' _ _ _ _ _ _ _ _ _ _
    (𝟙 ((S.componentRingSheaf O n).over Q)) (IsIso.id _)

/-- The extension of modules from the degree-`n` slice at `Q` to the total slice at `Q`: the left
adjoint of restriction. -/
abbrev sliceExtension :
    SheafOfModules.{u} ((S.componentRingSheaf O n).over Q) ⥤
      SheafOfModules.{u} (O.over ((componentFunctor S n).obj Q)) :=
  SheafOfModules.pullback.{u} (F := sliceInclusion S Q)
    (J := (S.componentTopology n).over Q) (K := S.totalTopology.over _)
    (S := (S.componentRingSheaf O n).over Q) (R := O.over ((componentFunctor S n).obj Q))
    (𝟙 ((S.componentRingSheaf O n).over Q))

/-- Extension is left adjoint to restriction. -/
abbrev sliceExtensionAdj : sliceExtension S O Q ⊣ sliceRestriction S O Q :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (F := sliceInclusion S Q)
    (J := (S.componentTopology n).over Q) (K := S.totalTopology.over _)
    (S := (S.componentRingSheaf O n).over Q) (R := O.over ((componentFunctor S n).obj Q))
    (𝟙 ((S.componentRingSheaf O n).over Q))

/-- Extension carries the structure sheaf to the structure sheaf. -/
abbrev sliceExtensionUnitHom :
    (sliceExtension S O Q).obj (SheafOfModules.unit _) ⟶
      SheafOfModules.unit (O.over ((componentFunctor S n).obj Q)) :=
  SheafOfModules.pullbackObjUnitToUnit (F := sliceInclusion S Q)
    (J := (S.componentTopology n).over Q) (K := S.totalTopology.over _)
    (S := (S.componentRingSheaf O n).over Q) (R := O.over ((componentFunctor S n).obj Q))
    (𝟙 ((S.componentRingSheaf O n).over Q))

/-- `sliceExtensionUnitHom` is invertible: extension to the total slice carries the structure
sheaf to the structure sheaf. -/
instance isIso_sliceExtensionUnitHom : IsIso (sliceExtensionUnitHom S O Q) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

end Inclusion

section InclusionAt

variable {k n : SimplexCategory} {P : S.component k} {Q : S.component n}
  (c : (componentFunctor S k).obj P ⟶ (componentFunctor S n).obj Q)

/-- The degree-`k` component inclusion at `P`, followed by an arrow `c` of the total category. -/
abbrev sliceInclusionAt : Over P ⥤ Over ((componentFunctor S n).obj Q) :=
  Over.post (componentFunctor S k) ⋙ Over.map c

/-- The degree-`k` inclusion at `P` followed by `c` is cocontinuous, being the composite of two
cocontinuous functors. -/
instance isCocontinuous_sliceInclusionAt :
    (sliceInclusionAt S c).IsCocontinuous ((S.componentTopology k).over P)
      (S.totalTopology.over _) :=
  isCocontinuous_comp _ _ _ (S.totalTopology.over _)

/-- Restriction of modules on the total slice at `Q` to the degree-`k` slice at `P`, along `c`. -/
abbrev sliceRestrictionAt :
    SheafOfModules.{u} (O.over ((componentFunctor S n).obj Q)) ⥤
      SheafOfModules.{u} ((S.componentRingSheaf O k).over P) :=
  SheafOfModules.pushforward.{u} (F := sliceInclusionAt S c) (𝟙 ((S.componentRingSheaf O k).over P))

/-- Restriction along `c` to the degree-`k` slice is a left adjoint, the inclusion at `P` being
cocontinuous. -/
instance isLeftAdjoint_sliceRestrictionAt : (sliceRestrictionAt S O c).IsLeftAdjoint :=
  (Stacks.SheafOfModules.RestrictRan.sheafAdjunction (sliceInclusionAt S c)
    ((S.componentTopology k).over P) (S.totalTopology.over _) (O.over _)).isLeftAdjoint

/-- The degree-`k` restriction along `c` of the structure sheaf is the structure sheaf. -/
abbrev sliceRestrictionAtUnitHom :
    SheafOfModules.unit ((S.componentRingSheaf O k).over P) ⟶
      (sliceRestrictionAt S O c).obj (SheafOfModules.unit _) :=
  SheafOfModules.unitToPushforwardObjUnit (F := sliceInclusionAt S c)
    (J := (S.componentTopology k).over P) (K := S.totalTopology.over _)
    (S := (S.componentRingSheaf O k).over P) (R := O.over ((componentFunctor S n).obj Q))
    (𝟙 ((S.componentRingSheaf O k).over P))

/-- `sliceRestrictionAtUnitHom` is invertible: the degree-`k` restriction along `c` of the
structure sheaf really is the structure sheaf. -/
instance isIso_sliceRestrictionAtUnitHom : IsIso (sliceRestrictionAtUnitHom S O c) :=
  @AlgebraicGeometry.SimplicialScheme.isIso_unitToPushforwardObjUnit' _ _ _ _ _ _ _ _ _ _
    (𝟙 ((S.componentRingSheaf O k).over P)) (IsIso.id _)

end InclusionAt

end CategoryTheory.SimplicialSiteSituation.CartesianSlice
