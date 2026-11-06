module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.Algebra.Homology.RightDerivedCoEdgeReflective
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSituationData
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedProperBaseChange
public import StacksFrontier.CategoryTheory.Sites.Localization.OverMapKanExtension
import StacksCore.Tactic.StacksAttribute

/-!
# Abelian sheaves and the comparison morphisms of the quasi-compact site

The category `LC_α` of Hausdorff, locally quasi-compact spaces carries the quasi-compact
topology and the coarser Zariski topology, and for an object `X` of it the identity functor on
the slice compares them, giving the change-of-topology morphism of topoi
`ε_X : Sh(LC_qc/X) → Sh(LC_Zar/X)`; composing with the Zariski comparison
`π_X : Sh(LC_Zar/X) → Sh(X)` to sheaves on the underlying space gives `a_X = π_X ∘ ε_X`. All of
this is available in this development for sheaves of sets. This file supplies the same
morphisms for sheaves of **abelian groups**, where the higher direct images `R^i ε_{X,*}` and
`R^i f_{qc,*}` live, and states clause (1) of Stacks 0DCY about them; clauses (2), (3) and (4)
are proved in `QcDerivedComparison.lean`, over the canonical maps constructed here.

## Main definitions

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `qcAbelianDirectImage`, `qcAbelianInverseImage`, `qcAbelianComparisonAdjunction`: the
  change-of-topology morphism `ε_X` on abelian sheaves.
* `qcTopologicalAbelianInverseImage`: the inverse image `a_X^{-1} = ε_X^{-1} ∘ π_X^{-1}`.
* `qcAbelianSliceDirectImage`: the direct image `f_{qc,*}` of the morphism of quasi-compact
  slice topoi induced by `f`, in the form `(f_{qc,*}G)(Z/Y) = G(Z ×_Y X / X)`.
* `qcHigherDirectImageComparison`: the canonical degree-`i` comparison
  `R^i f_{Zar,*} ε_{X,*} ⟶ ε_{Y,*} R^i f_{qc,*}`.
* `qcDerivedComparisonUnit`: the canonical map `K ⟶ Rε_{X,*}(ε_X^{-1}K)` on bounded below
  derived categories.
* `qcAbelianComparisonBaseChange` and `qcDerivedComparisonBaseChangeMap`: the mate of the
  square of direct images, and the canonical map `ε_Y^{-1} Rf_{Zar,*} ⟶ Rf_{qc,*} ε_X^{-1}` on
  bounded below derived categories it extends to.
* `qcTopologicalDerivedBaseChangeMap`: the canonical map
  `a_Y^{-1} Rf_* ⟶ Rf_{qc,*} a_X^{-1}` of clause (4) of Stacks 0DCY.

## Main results

* `qcAbelianDirectImageTopologicalInverseImageIso`: the first half of clause (1) of
  Stacks 0DCY, `ε_{X,*}(a_X^{-1}F) = π_X^{-1}F`.
* `isZero_rightDerived_qcAbelianDirectImage_qcTopologicalInverseImage`: the second half of
  clause (1), the vanishing of `R^i ε_{X,*}(a_X^{-1}F)` for `i > 0`.
* `isIso_qcHigherDirectImageComparison_app`: the degreewise comparison is an isomorphism, from
  the vanishing of the higher change-of-topology direct images in the range and the sheaf
  condition at the target.
* `qcDerivedComparisonBaseChangeMap_fac`: the equation characterizing the derived
  change-of-topology base change map.

## Implementation notes

The coefficient category is `AddCommGrpCat.{max (u + 1) v}`, as everywhere in this development:
the objects of the site lie one universe above the spaces, so the abelian comparison adjunction
is only available for coefficients in a universe containing that of the objects. Sheafification
for the localized quasi-compact topology at those coefficients is
`hasSheafify_qcTopology_over_abelian`, proved exactly as its Zariski counterpart from essential
smallness of the slice. The categories of abelian sheaves on the space and on the localized
Zariski site need their own sheafification, which is carried as an instance hypothesis here as
it is in `ZariskiDerivedProperBaseChange.lean`; enough injectives is carried the same way,
since the sites are not small and the Grothendieck-abelian instance does not apply at these
universes.

Both slice direct images are taken in the form `sheafPushforwardContinuous (Over.pullback f)`,
in which the square `ε_{X,*} ∘ f_{Zar,*} = f_{qc,*} ∘ ε_{Y,*}` of Stacks 0EZ2 holds strictly:
none of the four functors changes the underlying presheaf of a sheaf except by remembering a
weaker sheaf condition. That strict square is what the two edge morphisms of
`qcHigherDirectImageComparison` are composed across. Preservation of injective objects by
those pushforwards is transported along `zariskiSlicePushforwardIso` from the cocontinuous
form, whose left adjoint is restriction along `Over.map f` and hence exact.

### What is proved and what is carried

Stacks 0DCY is deduced in the source from the results of Section 21.30 (Stacks 0EZ1) through
Stacks 0EZI, which asserts five conditions making Situation 0EZ3 apply to the pair
`(LC_qc, LC_Zar)` with the proper maps as distinguished class and the sheaves pulled back from
the space as weak Serre class. Three of those five are not in this repository — see the
discussion in `ZariskiComparisonSituationData.lean` — and the leading assertion of Stacks 0EZF,
that the vanishing conditions `(V_n)` hold for every `n`, is not proved there either. So:

* The first half of clause (1) is **proved**, from the condition (0EZ6) of Situation 0EZ3 for
  this situation, carried as `h0EZI`.
* The second half of clause (1) is the condition `(V_n)` itself and is **carried**, as `hV`.
* `isIso_qcHigherDirectImageComparison_app` is **proved** outright.
* For clauses (3) and (4) this file contributes the construction of the two canonical maps
  whose invertibility they assert; that invertibility is proved in `QcDerivedComparison.lean`.

## References

* [Stacks Project, Tag 0DCY](https://stacks.math.columbia.edu/tag/0DCY)
* [Stacks Project, Tag 0EZ1](https://stacks.math.columbia.edu/tag/0EZ1)
* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ2](https://stacks.math.columbia.edu/tag/0EZ2)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0EZ9](https://stacks.math.columbia.edu/tag/0EZ9)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-! ### The change-of-topology morphism on abelian sheaves -/

/-- Presheaves of abelian groups on the localized quasi-compact site can be sheafified, at the
coefficient universe of this development, because the slice of the site is essentially small
there. -/
instance hasSheafify_qcTopology_over_abelian
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    HasSheafify (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  have : EssentiallySmall.{max (u + 1) v} (Over X) :=
    EssentiallySmall.mk' (AsSmall.equiv.{u, u + 1, max (u + 1) v} (C := Over X))
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v} _ _

/-- Restriction of presheaves of abelian groups along `Over.map f` has pointwise right Kan
extensions, the site having fibre products. -/
instance hasPointwiseRightKanExtension_overMap_abelian
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) :
    (Over.map f).op.HasPointwiseRightKanExtension F :=
  Stacks.Localization.hasPointwiseRightKanExtension_overMapOp f _ F

/-- Direct image for the change-of-topology morphism `ε_X : Sh(LC_qc/X) → Sh(LC_Zar/X)` on
abelian sheaves: a sheaf for the quasi-compact topology, regarded as a sheaf for the coarser
Zariski topology. -/
def qcAbelianDirectImage (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  ObjectProperty.ιOfLE fun _ hF ↦ hF.of_le (S.zariskiTopology_over_le_qc X)

/-- The abelian change-of-topology direct image is full: it is a full subcategory inclusion. -/
instance qcAbelianDirectImage_full (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) : (qcAbelianDirectImage.{u, w, v} S X).Full :=
  ObjectProperty.full_ιOfLE _

/-- The abelian change-of-topology direct image is faithful: it is a full subcategory
inclusion. -/
instance qcAbelianDirectImage_faithful
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (qcAbelianDirectImage.{u, w, v} S X).Faithful :=
  ObjectProperty.faithful_ιOfLE _

/-- The abelian change-of-topology direct image is additive, so its higher right derived
functors are defined. -/
instance qcAbelianDirectImage_additive
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (qcAbelianDirectImage.{u, w, v} S X).Additive where
  map_add := rfl

/-- Inverse image for the change-of-topology morphism on abelian sheaves, that is,
quasi-compact sheafification of a Zariski sheaf of abelian groups. -/
def qcAbelianInverseImage (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  sheafToPresheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} ⋙
    presheafToSheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v}

/-- The change-of-topology adjunction on abelian sheaves: quasi-compact sheafification is left
adjoint to regarding a quasi-compact sheaf as a Zariski sheaf. -/
def qcAbelianComparisonAdjunction
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    qcAbelianInverseImage.{u, w, v} S X ⊣ qcAbelianDirectImage.{u, w, v} S X :=
  (sheafificationAdjunction (S.qcSite.grothendieckTopology.over X)
      AddCommGrpCat.{max (u + 1) v}).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful
      (sheafToPresheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}))
    (Functor.FullyFaithful.ofFullyFaithful
      (𝟭 (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v})))
    (Iso.refl _) (Iso.refl _)

/-- The abelian change-of-topology inverse image is additive, being a left adjoint between
abelian categories. -/
instance qcAbelianInverseImage_additive
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (qcAbelianInverseImage.{u, w, v} S X).Additive :=
  (qcAbelianComparisonAdjunction.{u, w, v} S X).left_adjoint_additive

/-- The abelian change-of-topology direct image is left exact, being a right adjoint. -/
instance qcAbelianDirectImage_preservesFiniteLimits
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    PreservesFiniteLimits (qcAbelianDirectImage.{u, w, v} S X) :=
  have := (qcAbelianComparisonAdjunction.{u, w, v} S X).isRightAdjoint
  ((qcAbelianComparisonAdjunction.{u, w, v} S X).rightAdjoint_preservesLimits.{max (u + 1) v,
    max (u + 1) v}).preservesFiniteLimits

/-- The abelian change-of-topology inverse image preserves epimorphisms, being a left
adjoint. -/
instance qcAbelianInverseImage_preservesEpimorphisms
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (qcAbelianInverseImage.{u, w, v} S X).PreservesEpimorphisms :=
  have := (qcAbelianComparisonAdjunction.{u, w, v} S X).isLeftAdjoint
  inferInstance

/-- The abelian change-of-topology inverse image preserves monomorphisms: forgetting the sheaf
condition preserves limits and sheafification of abelian groups is left exact. -/
instance qcAbelianInverseImage_preservesMonomorphisms
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (qcAbelianInverseImage.{u, w, v} S X).PreservesMonomorphisms := by
  dsimp only [qcAbelianInverseImage]
  infer_instance

/-- The abelian change-of-topology inverse image is left exact: forgetting the sheaf condition
preserves limits and sheafification of abelian groups is left exact. -/
instance qcAbelianInverseImage_preservesFiniteLimits
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    PreservesFiniteLimits (qcAbelianInverseImage.{u, w, v} S X) := by
  dsimp only [qcAbelianInverseImage]
  infer_instance

/-- The abelian change-of-topology inverse image is right exact, being a left adjoint. -/
instance qcAbelianInverseImage_preservesFiniteColimits
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    PreservesFiniteColimits (qcAbelianInverseImage.{u, w, v} S X) :=
  have := (qcAbelianComparisonAdjunction.{u, w, v} S X).isLeftAdjoint
  ((qcAbelianComparisonAdjunction.{u, w, v} S X).leftAdjoint_preservesColimits.{max (u + 1) v,
    max (u + 1) v}).preservesFiniteColimits

/-- The abelian change-of-topology direct image preserves injective objects, its left adjoint
preserving monomorphisms. -/
instance qcAbelianDirectImage_preservesInjectiveObjects
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    (qcAbelianDirectImage.{u, w, v} S X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (qcAbelianComparisonAdjunction.{u, w, v} S X)

/-- The unit of the abelian change-of-topology adjunction is invertible at a Zariski sheaf of
abelian groups which already satisfies the sheaf condition for the quasi-compact topology: such
a sheaf lies in the essential image of the fully faithful direct image. -/
theorem isIso_qcAbelianComparisonAdjunction_unit_app
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (G : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})
    (hG : Presheaf.IsSheaf (S.qcSite.grothendieckTopology.over X) G.obj) :
    IsIso ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app G) :=
  (Adjunction.isIso_unit_app_iff_mem_essImage
    (qcAbelianComparisonAdjunction.{u, w, v} S X)).2 ⟨⟨G.obj, hG⟩, ⟨Iso.refl _⟩⟩

/-- Inverse image along `a_X = π_X ∘ ε_X` on abelian sheaves: the Zariski comparison inverse
image followed by quasi-compact sheafification. -/
abbrev qcTopologicalAbelianInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙ qcAbelianInverseImage.{u, w, v} S X

/-- The sheaves pulled back from the space contain every `π_X^{-1}F`: that is what the class
`A'_X` of Stacks 0EZI is. -/
theorem zariskiPullbackClass_abelianComparisonInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    S.zariskiPullbackClass.{u, w, v} X
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F) := by
  rw [zariskiPullbackClass, ObjectProperty.prop_map_iff]
  exact ⟨F, trivial, ⟨Iso.refl _⟩⟩

/-! ### Direct image along a morphism of the site, on abelian sheaves -/

/-- Direct image along `f` on the localized quasi-compact sites, on abelian sheaves, in the
form `(f_{qc,*}G)(Z/Y) = G(Z ×_Y X / X)`. -/
abbrev qcAbelianSliceDirectImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y) :
    Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (S.qcSite.grothendieckTopology.over Y) AddCommGrpCat.{max (u + 1) v} :=
  Functor.sheafPushforwardContinuous (Over.pullback f) AddCommGrpCat.{max (u + 1) v}
    (S.qcSite.grothendieckTopology.over Y) (S.qcSite.grothendieckTopology.over X)

/-- The direct image of the morphism of quasi-compact slice topoi is restriction along
`Over.pullback f`: the pushforward attached to cocontinuity of `Over.map f` agrees with the
pushforward attached to continuity of its right adjoint. -/
def qcAbelianSlicePushforwardIso
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y) :
    (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) v}
        (S.qcSite.grothendieckTopology.over X) (S.qcSite.grothendieckTopology.over Y) ≅
      qcAbelianSliceDirectImage.{u, w, v} S f :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso AddCommGrpCat.{max (u + 1) v}

/-- Direct image along `f` on the localized quasi-compact sites preserves injective objects:
the cocontinuous form of it does, its left adjoint being restriction along `Over.map f`, which
is both a left and a right adjoint and hence exact. -/
instance qcAbelianSliceDirectImage_preservesInjectiveObjects
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y) :
    (qcAbelianSliceDirectImage.{u, w, v} S f).PreservesInjectiveObjects := by
  have hmono : (S.qcSite.grothendieckTopology.overMapPullback
      AddCommGrpCat.{max (u + 1) v} f).PreservesMonomorphisms :=
    have := ((Over.map f).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (S.qcSite.grothendieckTopology.over X)
      (S.qcSite.grothendieckTopology.over Y)).isRightAdjoint
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have hcoc : ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) v}
      (S.qcSite.grothendieckTopology.over X)
      (S.qcSite.grothendieckTopology.over Y)).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{max (u + 1) v}
        (S.qcSite.grothendieckTopology.over X) (S.qcSite.grothendieckTopology.over Y))
  constructor
  intro I hI
  exact Injective.of_iso ((qcAbelianSlicePushforwardIso.{u, w, v} S f).app I)
    (hcoc.injective_obj hI)

/-- Direct image along `f` on the localized Zariski sites preserves injective objects, for the
same reason as on the quasi-compact sites. -/
instance sliceDirectImage_preservesInjectiveObjects
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}] :
    (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).PreservesInjectiveObjects := by
  have hmono : (S.zariskiTopology.overMapPullback
      AddCommGrpCat.{max (u + 1) v} f).PreservesMonomorphisms :=
    have := ((Over.map f).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (S.zariskiTopology.over X) (S.zariskiTopology.over Y)).isRightAdjoint
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have hcoc : ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) v}
      (S.zariskiTopology.over X)
      (S.zariskiTopology.over Y)).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{max (u + 1) v}
        (S.zariskiTopology.over X) (S.zariskiTopology.over Y))
  constructor
  intro I hI
  exact Injective.of_iso ((zariskiSlicePushforwardIso S f AddCommGrpCat.{max (u + 1) v}).app I)
    (hcoc.injective_obj hI)

/-- **The square of topoi of Stacks 0EZ2 on abelian sheaves over the localized sites.**
Change-of-topology direct image followed by direct image along `f` for the Zariski topology is
direct image along `f` for the quasi-compact topology followed by change-of-topology direct
image, as one and the same functor: none of the four changes the underlying presheaf of a sheaf
except by remembering a weaker sheaf condition. -/
theorem qcAbelianDirectImage_comp_sliceDirectImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y) :
    qcAbelianDirectImage.{u, w, v} S X ⋙ sliceDirectImage S f AddCommGrpCat.{max (u + 1) v} =
      qcAbelianSliceDirectImage.{u, w, v} S f ⋙ qcAbelianDirectImage.{u, w, v} S Y :=
  rfl

/-! ### Clause (1): the change-of-topology direct images of a sheaf pulled back from the space -/

section ClauseOne

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]

/-- **Stacks 0DCY (1), the identification `ε_{X,*}(a_X^{-1}F) = π_X^{-1}F`.** For an object `X`
of the site and an abelian sheaf `F` on the space underlying `X`, the change-of-topology direct
image of `a_X^{-1}F` is `π_X^{-1}F`.

The hypothesis `h0EZI` is condition (0EZ6) of Situation 0EZ3 for this situation, one of the five
conditions asserted by Stacks 0EZI: a sheaf pulled back from the space already satisfies the
sheaf condition for quasi-compact coverings. Granted it, the unit of the change-of-topology
adjunction is invertible at `π_X^{-1}F`, which is the assertion. -/
@[stacks 0DCY "clause (1), the identification eps_{X,*}a_X^{-1}F = pi_X^{-1}F. PROVED, from
condition (0EZ6) of Situation 0EZ3 for this situation, carried as h0EZI: that condition is
one of the clauses of Tag 0EZI absent from this repository (see LocallyQuasiCompact/
ZariskiComparisonSituationData.lean:52). The sheaves-of-sets version of (0EZ6) IS proved, as
isSheaf_qc_comparisonInverseImage (LocallyQuasiCompact/QcComparisonNaturality.lean:357, which
carries no tag of its own; the tagged 09X3 carriers are isSheaf_qc_germSectionsPresheaf and
isIso_toSheafify_comparisonInverseImage, both in LocallyQuasiCompact/QcGermSectionsSheaf.lean),
but only at coefficients Type u, which is why the abelian form is carried"]
def qcAbelianDirectImageTopologicalInverseImageIso
    (h0EZI : ∀ G : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v},
      S.zariskiPullbackClass.{u, w, v} X G →
        Presheaf.IsSheaf (S.qcSite.grothendieckTopology.over X) G.obj)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    (qcAbelianDirectImage.{u, w, v} S X).obj
        ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F) ≅
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F :=
  have := isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S X _
    (h0EZI _ (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F))
  (asIso ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app
    ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F))).symm

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}] in
/-- **Stacks 0DCY (1), the vanishing `R^i ε_{X,*}(a_X^{-1}F) = 0` for `i > 0`.**

The hypothesis `hV` is the family of vanishing conditions `(V_n)` of Situation 0EZ3 for this
situation, stated for the class of sheaves pulled back from the space: it is the leading
assertion of Stacks 0EZF, which this development does not prove — see
`Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition_of_singleCoveringDescent`,
where it is reduced to a descent statement for a single covering arrow of the distinguished
class. This clause is therefore carried, not proved; the content here is only that `π_X^{-1}F`
belongs to the class. -/
@[stacks 0DCY "clause (1), the vanishing R^i eps_{X,*}(a_X^{-1}F) = 0 for i > 0. NOT PROVED:
it IS the vanishing condition (V_n) of Situation 0EZ3, carried as hV. The leading assertion
of Tag 0EZF supplies that condition only granted SingleCoveringDescent -- see
ChangeOfTopology/VanishingConditionAllDegrees.lean:117 -- and that descent statement is not
proved anywhere. What IS proved here is only that pi_X^{-1}F lies in the class A'_X"]
theorem isZero_rightDerived_qcAbelianDirectImage_qcTopologicalInverseImage
    [EnoughInjectives
      (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v})]
    (hV : ∀ G : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v},
      S.zariskiPullbackClass.{u, w, v} X G → ∀ i : ℕ, 0 < i →
        IsZero (((qcAbelianDirectImage.{u, w, v} S X).rightDerived i).obj
          ((qcAbelianInverseImage.{u, w, v} S X).obj G)))
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
    (i : ℕ) (hi : 0 < i) :
    IsZero (((qcAbelianDirectImage.{u, w, v} S X).rightDerived i).obj
      ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F)) :=
  hV _ (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F) i hi

end ClauseOne

/-! ### Clause (2): higher direct images along a morphism of the site -/

section ClauseTwo

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category}
  (f : X ⟶ Y)
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- **The canonical degreewise comparison of higher direct images across the change of
topology,** `R^i f_{Zar,*} ε_{X,*} ⟶ ε_{Y,*} R^i f_{qc,*}`, natural in the abelian sheaf on the
localized quasi-compact site over `X`.

It is the composite of the two edge morphisms of the Grothendieck spectral sequence of the
strict square `qcAbelianDirectImage_comp_sliceDirectImage`: the edge `E₂^{i,0} ⟶ H^i` for the
pair `(ε_{X,*}, f_{Zar,*})` followed by the edge `H^i ⟶ E₂^{0,i}` for the pair
`(f_{qc,*}, ε_{Y,*})`. Neither uses any vanishing hypothesis, so the map is defined for every
sheaf. -/
def qcHigherDirectImageComparison (i : ℕ) :
    qcAbelianDirectImage.{u, w, v} S X ⋙
        (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i ⟶
      (qcAbelianSliceDirectImage.{u, w, v} S f).rightDerived i ⋙
        qcAbelianDirectImage.{u, w, v} S Y :=
  Stacks.Cohomology.RightDerivedEdge.edge (qcAbelianDirectImage.{u, w, v} S X)
      (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}) i ≫
    Stacks.Cohomology.RightDerivedCoEdge.secondEdge (qcAbelianSliceDirectImage.{u, w, v} S f)
      (qcAbelianDirectImage.{u, w, v} S Y) i

/-- **The degreewise comparison is an isomorphism in degree `i`** as soon as the higher
change-of-topology direct images of the sheaf vanish in degrees `1 ≤ q ≤ i` and the target
already satisfies the sheaf condition for quasi-compact coverings.

Both factors are invertible, for different reasons: the first edge morphism by
`Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app`, which needs exactly the vanishing; the
second by `Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_of_isIso_unit`, which
needs exactly that the object it starts from lies in the essential image of the
change-of-topology direct image. This is the form taken by Stacks 0EZA in this situation. -/
theorem isIso_qcHigherDirectImageComparison_app (i : ℕ)
    (F : Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v})
    (hvan : ∀ q, 1 ≤ q → q ≤ i →
      IsZero (((qcAbelianDirectImage.{u, w, v} S X).rightDerived q).obj F))
    (hsheaf : Presheaf.IsSheaf (S.qcSite.grothendieckTopology.over Y)
      (((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).obj
        ((qcAbelianDirectImage.{u, w, v} S X).obj F)).obj) :
    IsIso ((qcHigherDirectImageComparison.{u, w, v} S f i).app F) := by
  have h₁ : IsIso ((Stacks.Cohomology.RightDerivedEdge.edge
      (qcAbelianDirectImage.{u, w, v} S X)
      (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}) i).app F) :=
    Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app _ _ F i hvan
  have hunit : IsIso ((qcAbelianComparisonAdjunction.{u, w, v} S Y).unit.app
      (((qcAbelianSliceDirectImage.{u, w, v} S f ⋙
        qcAbelianDirectImage.{u, w, v} S Y).rightDerived i).obj F)) :=
    (NatTrans.isIso_app_iff_of_iso (qcAbelianComparisonAdjunction.{u, w, v} S Y).unit
        (asIso ((Stacks.Cohomology.RightDerivedEdge.edge
          (qcAbelianDirectImage.{u, w, v} S X)
          (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}) i).app F))).1
      (isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S Y _ hsheaf)
  exact IsIso.comp_isIso' h₁
    (Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_of_isIso_unit _
      (qcAbelianComparisonAdjunction.{u, w, v} S Y) i F hunit)

section ClauseTwoSpace

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]

end ClauseTwoSpace

end ClauseTwo

/-! ### Clause (3): the derived change-of-topology unit -/

section ClauseThree

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives
    (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- **The canonical map `K ⟶ Rε_{X,*}(ε_X^{-1}K)` on bounded below derived categories.** It is
obtained from the ordinary change-of-topology adjunction unit, the unit of right derivation of
`ε_{X,*}`, and the degreewise description of the action of the exact functor `ε_X^{-1}`; the
localization functor to the bounded below derived category being a localization, whiskering by
it is fully faithful on natural transformations out of it, which is what produces the map. -/
def qcDerivedComparisonUnit :
    𝟭 (DerivedCategory.Plus (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})) ⟶
      (qcAbelianInverseImage.{u, w, v} S X).mapDerivedCategoryPlus ⋙
        (qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlus :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})) _).preimage
      (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdComparison
            (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}))
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans
            (qcAbelianComparisonAdjunction.{u, w, v} S X).unit) DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (qcAbelianInverseImage.{u, w, v} S X ⋙
              qcAbelianDirectImage.{u, w, v} S X))).inv DerivedCategory.Plus.Qh ≫
        Functor.whiskerLeft (qcAbelianInverseImage.{u, w, v} S X).mapHomotopyCategoryPlus
          (qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlusUnith ≫
        Functor.whiskerRight
          (qcAbelianInverseImage.{u, w, v} S X).mapDerivedCategoryPlusFactorsh.inv
          (qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlus)

end ClauseThree

/-! ### Clause (4): derived base change along a morphism of the site -/

section ClauseFour

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category}
  (f : X ⟶ Y)
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives
    (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v})]

/-- Right derivation does nothing to the abelian change-of-topology inverse image: that functor
is exact, hence preserves homology, hence inverts quasi-isomorphisms already on the homotopy
category. -/
instance qcAbelianInverseImage_rightDerivedFunctorPlusUnit_isIso (T : S.category)
    [HasSheafify (S.zariskiTopology.over T) AddCommGrpCat.{max (u + 1) v}]
    [EnoughInjectives (Sheaf (S.zariskiTopology.over T) AddCommGrpCat.{max (u + 1) v})] :
    IsIso (qcAbelianInverseImage.{u, w, v} S T).rightDerivedFunctorPlusUnith :=
  Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology _

/-- **The mate of the strict square `ε_{X,*} ∘ f_{Zar,*} = f_{qc,*} ∘ ε_{Y,*}` of Stacks 0EZ2 on
abelian sheaves:** the natural map `ε_Y^{-1} f_{Zar,*} ⟶ f_{qc,*} ε_X^{-1}` of inverse images,
obtained from that identity by the two change-of-topology adjunctions. -/
def qcAbelianComparisonBaseChange :
    sliceDirectImage S f AddCommGrpCat.{max (u + 1) v} ⋙
        qcAbelianInverseImage.{u, w, v} S Y ⟶
      qcAbelianInverseImage.{u, w, v} S X ⋙ qcAbelianSliceDirectImage.{u, w, v} S f :=
  Functor.whiskerRight
      (Functor.whiskerRight (qcAbelianComparisonAdjunction.{u, w, v} S X).unit
        (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}))
      (qcAbelianInverseImage.{u, w, v} S Y) ≫
    Functor.whiskerLeft (qcAbelianInverseImage.{u, w, v} S X)
      (Functor.whiskerLeft (qcAbelianSliceDirectImage.{u, w, v} S f)
        (qcAbelianComparisonAdjunction.{u, w, v} S Y).counit)

/-- The mate applied degreewise on bounded below homotopy categories and composed with the
units of right derivation. The unit for `ε_Y^{-1}` is inverted, which is legitimate because
that functor is exact. -/
def qcDerivedComparisonBaseChangeOnHomotopy :
    (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙
        (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.Qh ⋙
        (qcAbelianInverseImage.{u, w, v} S X).rightDerivedFunctorPlus ⋙
        (qcAbelianSliceDirectImage.{u, w, v} S f).rightDerivedFunctorPlus :=
  Functor.whiskerLeft
      (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).mapHomotopyCategoryPlus
      (inv (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlusUnith) ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v} ⋙
          qcAbelianInverseImage.{u, w, v} S Y))).hom DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans
        (qcAbelianComparisonBaseChange.{u, w, v} S f)) DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (qcAbelianInverseImage.{u, w, v} S X ⋙
          qcAbelianSliceDirectImage.{u, w, v} S f))).inv DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft (qcAbelianInverseImage.{u, w, v} S X).mapHomotopyCategoryPlus
      (qcAbelianSliceDirectImage.{u, w, v} S f).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight (qcAbelianInverseImage.{u, w, v} S X).rightDerivedFunctorPlusUnith
      (qcAbelianSliceDirectImage.{u, w, v} S f).rightDerivedFunctorPlus

/-- **The canonical derived base change map of the change-of-topology morphisms,**
`ε_Y^{-1} Rf_{Zar,*} ⟶ Rf_{qc,*} ε_X^{-1}` on bounded below derived categories. It is the
transformation produced by the universal property of right derivation from
`qcDerivedComparisonBaseChangeOnHomotopy`, so it is characterized by
`qcDerivedComparisonBaseChangeMap_fac`. -/
def qcDerivedComparisonBaseChangeMap :
    (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
        (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus ⟶
      (qcAbelianInverseImage.{u, w, v} S X).rightDerivedFunctorPlus ⋙
        (qcAbelianSliceDirectImage.{u, w, v} S f).rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc
    ((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
      (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus)
    (L := DerivedCategory.Plus.Qh)
    (Functor.whiskerRight
      (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnith
      (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}))
    _ (qcDerivedComparisonBaseChangeOnHomotopy.{u, w, v} S f)

/-- The equation defining the canonical derived base change map of the change-of-topology
morphisms. -/
theorem qcDerivedComparisonBaseChangeMap_fac :
    Functor.whiskerRight
        (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnith
        (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (qcDerivedComparisonBaseChangeMap.{u, w, v} S f) =
          qcDerivedComparisonBaseChangeOnHomotopy.{u, w, v} S f :=
  Functor.rightDerived_fac
    ((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
      (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus)
    (L := DerivedCategory.Plus.Qh)
    (Functor.whiskerRight
      (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnith
      (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}))
    _ (qcDerivedComparisonBaseChangeOnHomotopy.{u, w, v} S f)

section ClauseFourSpace

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]

/-- **The canonical derived base change map of the comparison morphisms to the underlying
spaces,** `a_Y^{-1} Rf_* ⟶ Rf_{qc,*} a_X^{-1}` on bounded below derived categories, `a` being
`π` followed by the change of topology. It is the Zariski derived base change map
`derivedComparisonBaseChangeMap` of Stacks 0DCU followed by the change-of-topology one. Clause
(4) of Stacks 0DCY is the assertion that it is an isomorphism for a proper `f`.

Both inverse images appear as their total right derived functors. That is the same thing: each
is exact, so the unit of right derivation is invertible on it, by
`qcAbelianInverseImage_rightDerivedFunctorPlusUnit_isIso` and its Zariski counterpart
`abelianComparisonInverseImage_rightDerivedFunctorPlusUnit_isIso`. -/
def qcTopologicalDerivedBaseChangeMap :
    (spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⋙
        (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus ⟶
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlus ⋙
        (qcAbelianInverseImage.{u, w, v} S X).rightDerivedFunctorPlus ⋙
        (qcAbelianSliceDirectImage.{u, w, v} S f).rightDerivedFunctorPlus :=
  Functor.whiskerRight (derivedComparisonBaseChangeMap.{u, w, v} S f)
      (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus ≫
    Functor.whiskerLeft
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlus
      (qcDerivedComparisonBaseChangeMap.{u, w, v} S f)

end ClauseFourSpace

end ClauseFour

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
