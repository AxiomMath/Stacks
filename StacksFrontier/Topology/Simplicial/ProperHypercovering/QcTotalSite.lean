module

public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.FromSimplicialObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The total site `(LC_qc/U)_total` of a simplicial object of `LC`

Let `U` be a simplicial object of the quasi-compact site `LC_qc` of Hausdorff, locally
quasi-compact spaces and let `a : U → X` be an augmentation. Stacks Section 09X8 attaches to it
the site `(LC_qc/U)_total`: its objects are the `V/U_n`, its morphisms `V/U_n → W/U_m` are the
commutative squares over the simplicial structure maps, and the augmentation morphism of topoi

`a_qc : Sh((LC_qc/U)_total) → Sh(LC_qc/X)`

is the one of the cocontinuous functor `V/U_n ↦ V/X`. The site is the total localization of the
simplicial semi-representable object `n ↦ {U_n → X}` over the localized site `LC_qc/X`.

The objects of `LC_qc` form a proper class, but the category `LC_α` underlying the site is
essentially small in the universe of the spaces, and so is `(LC_qc/U)_total`. Hence the topos
and the augmentation can be formed with sheaves of sets in the universe of the spaces, which is
the universe of the sheaves of sets on the spaces themselves.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTotal` and `qcTotalTopology`: the site
  `(LC_qc/U)_total`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTotalForget`: the functor
  `V/U_n ↦ V/X`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcAugmentation`: the augmentation
  morphism of topoi `a_qc`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.essentiallySmall_qcTotal`: the total
  site is essentially small in the universe of the spaces.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.hasSheafify_qcTotalTopology`: presheaves
  of sets on it in that universe can be sheafified.

## References

* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentable.Simplicial
open Stacks.CategoryTheory.Hypercovering

universe x u w

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
  (U : SimplicialObject S.category) {X : S.category}
  (a : U ⟶ (SimplicialObject.const S.category).obj X)

/-- The simplicial semi-representable object `n ↦ {U_n → X}` of `SR(LC_qc, X)` attached to the
augmentation. -/
abbrev qcSemiRepresentable : SimplicialObject (FormalCoproduct.{x} (Over X)) :=
  Over.lift U a ⋙ FormalCoproduct.incl (Over X)

/-- The semi-representable object of the augmentation is the one attached to an augmented
simplicial object of a site, `Stacks.CategoryTheory.Hypercovering.associatedSimplicialObject`. -/
theorem qcSemiRepresentable_eq :
    qcSemiRepresentable.{x} S U a = associatedSimplicialObject.{x} U a := rfl

/-- The category of the site `(LC_qc/U)_total` of Stacks Section 09X8: an object is an object
`V` of `LC_qc/X` in a simplicial degree `n` together with a morphism `V → U_n` over `X`, and a
morphism is a commutative square over a simplicial structure map. -/
abbrev qcTotal := TotalLocalization (qcSemiRepresentable.{x} S U a)

/-- The topology of `(LC_qc/U)_total`: a sieve covers when its arrows inside the simplicial
degree of its target cover in the localized quasi-compact site `LC_qc/X`. -/
abbrev qcTotalTopology : GrothendieckTopology (qcTotal.{x} S U a) :=
  totalLocalizationTopology (qcSemiRepresentable.{x} S U a)
    (S.qcSite.grothendieckTopology.over X)

/-- The functor `V/U_n ↦ V/X` from `(LC_qc/U)_total` to `LC_qc/X`. -/
abbrev qcTotalForget : qcTotal.{x} S U a ⥤ Over X :=
  totalLocalizationFunctor (qcSemiRepresentable.{x} S U a)

/-- `(LC_qc/U)_total` is essentially small in the universe of the spaces. -/
instance essentiallySmall_qcTotal : EssentiallySmall.{u} (qcTotal.{x} S U a) := by
  have : EssentiallySmall.{u} (Over X) := essentiallySmall_over.{u, w, 0} S X
  rw [essentiallySmall_iff]
  refine ⟨?_, inferInstance⟩
  let e := equivSmallModel.{u} (Over X)
  let ι : (Σ (n : SimplexCategory), Σ (W : SmallModel.{u} (Over X)),
      (e.inverse.obj W ⟶ (Over.lift U a).obj (op n))) → Skeleton (qcTotal.{x} S U a) :=
    fun t => toSkeleton (⟨e.inverse.obj t.2.1, op t.1,
      (FormalCoproduct.incl (Over X)).map t.2.2⟩ : qcTotal.{x} S U a)
  refine small_of_surjective (f := ι) fun Z => ?_
  let Z₀ : qcTotal.{x} S U a := (fromSkeleton _).obj Z
  let i : e.inverse.obj (e.functor.obj Z₀.left) ≅ Z₀.left := e.unitIso.symm.app Z₀.left
  let f : e.inverse.obj (e.functor.obj Z₀.left) ⟶ (Over.lift U a).obj Z₀.right :=
    i.hom ≫ (FormalCoproduct.fullyFaithfulIncl (C := Over X)).preimage Z₀.hom
  refine ⟨⟨Z₀.right.unop, e.functor.obj Z₀.left, f⟩, ?_⟩
  rw [← toSkeleton_fromSkeleton_obj Z]
  refine toSkeleton_eq_toSkeleton_iff.2 ⟨Comma.isoMk i (Iso.refl _) ?_⟩
  have h : (FormalCoproduct.incl (Over X)).map
      ((FormalCoproduct.fullyFaithfulIncl (C := Over X)).preimage Z₀.hom) = Z₀.hom :=
    (FormalCoproduct.fullyFaithfulIncl (C := Over X)).map_preimage _
  simp only [f, Functor.map_comp, h, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

/-- The shapes computing right Kan extensions along `(V/U_n ↦ V/X)ᵒᵖ` are essentially small in
the universe of the spaces. -/
theorem essentiallySmall_structuredArrow_qcTotalForget (W : (Over X)ᵒᵖ) :
    EssentiallySmall.{u} (StructuredArrow W (qcTotalForget.{x} S U a).op) :=
  StructuredArrow.essentiallySmall

/-- Right Kan extensions along `(V/U_n ↦ V/X)ᵒᵖ` of presheaves of sets in the universe of the
spaces exist pointwise. -/
instance hasPointwiseRightKanExtension_qcTotalForget (F : (qcTotal.{x} S U a)ᵒᵖ ⥤ Type u) :
    (qcTotalForget.{x} S U a).op.HasPointwiseRightKanExtension F := fun W => by
  have := essentiallySmall_structuredArrow_qcTotalForget.{x} S U a W
  have : HasLimitsOfShape (StructuredArrow W (qcTotalForget.{x} S U a).op) (Type u) :=
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

/-- Presheaves of sets in the universe of the spaces on `(LC_qc/U)_total` can be sheafified. -/
theorem hasSheafify_qcTotalTopology :
    HasSheafify (qcTotalTopology.{x} S U a) (Type u) :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _

/-- Restriction of sheaves of sets along a continuous functor preserves finite limits. -/
@[sga "4 III 1.8" "partial"]
theorem preservesFiniteLimits_sheafPushforwardContinuous_type
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K] :
    PreservesFiniteLimits (G.sheafPushforwardContinuous (Type u) J K) := by
  have : PreservesFiniteLimits (G.sheafPushforwardContinuous (Type u) J K ⋙
      sheafToPresheaf J (Type u)) :=
    preservesFiniteLimits_of_natIso
      (G.sheafPushforwardContinuousCompSheafToPresheafIso (Type u) J K).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type u))

/-- The augmentation morphism of topoi
`a_qc : Sh((LC_qc/U)_total) → Sh(LC_qc/X)` of an augmentation `a : U → X` of a simplicial object
of `LC_qc`: the morphism of topoi of the cocontinuous functor `V/U_n ↦ V/X`. Its inverse image is
restriction along that functor and its direct image the right Kan extension. -/
def qcAugmentation :
    MorphismOfTopoi (Sheaf (qcTotalTopology.{x} S U a) (Type u))
      (Sheaf (S.qcSite.grothendieckTopology.over X) (Type u)) where
  inverseImage := (qcTotalForget.{x} S U a).sheafPushforwardContinuous (Type u) _ _
  pushforward := (qcTotalForget.{x} S U a).sheafPushforwardCocontinuous (Type u) _ _
  adj := (qcTotalForget.{x} S U a).sheafAdjunctionCocontinuous (Type u) _ _
  preservesFiniteLimits := preservesFiniteLimits_sheafPushforwardContinuous_type _ _ _

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
