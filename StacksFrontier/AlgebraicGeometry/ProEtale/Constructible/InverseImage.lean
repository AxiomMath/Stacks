module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# Inverse image of pro-étale sheaves of modules

Let `g : Z ⟶ X` be a morphism of schemes and `Λ` a ring. Inverse image of sheaves of
`Λ`-modules from the small pro-étale site of `X` to that of `Z`,
`AlgebraicGeometry.ProEtale.proetaleModuleInverseImage`, is exact and additive, is compatible
with composition of morphisms of schemes up to canonical isomorphism, and carries sheaves which
are locally constant of finite type to sheaves which are locally constant of finite type.

## Main definitions

* `AlgebraicGeometry.Scheme.proetaleBaseChangeCompIso`: pro-étale base change along `a` after
  base change along `b` is base change along `a ≫ b`.
* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImageAdjunction`: inverse image is left
  adjoint to direct image.
* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImageIsoSheafPullback`: inverse image agrees
  with the inverse image `CategoryTheory.Functor.sheafPullback` defined as a chosen left adjoint.
* `AlgebraicGeometry.ProEtale.proetaleModuleInverseImageCompIso`: inverse image along `b`
  followed by inverse image along `a` is inverse image along `a ≫ b`.

## Main results

* `AlgebraicGeometry.ProEtale.preservesFiniteLimits_proetaleModuleInverseImage` and
  `AlgebraicGeometry.ProEtale.preservesFiniteColimits_proetaleModuleInverseImage`: inverse image
  is exact.
* `AlgebraicGeometry.ProEtale.isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage`:
  inverse image preserves local constancy of finite type.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- Pro-étale base change along `b` followed by pro-étale base change along `a` is pro-étale
base change along `a ≫ b`. -/
public def Scheme.proetaleBaseChangeCompIso {Y Z X : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X) :
    Scheme.proetaleBaseChange b ⋙ Scheme.proetaleBaseChange a ≅
      Scheme.proetaleBaseChange (a ≫ b) := by
  letI : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      MorphismProperty.HasPullbacksAlong (@WeaklyEtale : MorphismProperty Scheme.{u}) f :=
    fun _ ↦ ⟨fun _ _ ↦ inferInstance⟩
  letI : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      MorphismProperty.IsStableUnderBaseChangeAlong
        (@WeaklyEtale : MorphismProperty Scheme.{u}) f :=
    fun _ ↦ ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact (MorphismProperty.Over.pullbackComp a b).symm

namespace ProEtale

variable (Λ : Type v) [CommRing Λ]

/-- The left Kan extension along the opposite of pro-étale base change is left exact, for
coefficients in `ModuleCat.{max (u + 1) v w} Λ`: base change is representably flat, so the
comma categories computing the Kan extension pointwise are filtered. -/
public theorem preservesFiniteLimits_lan_op_proetaleBaseChange {Z X : Scheme.{u}} (g : Z ⟶ X) :
    PreservesFiniteLimits ((Scheme.proetaleBaseChange g).op.lan :
      (X.ProEtᵒᵖ ⥤ ModuleCat.{max (u + 1) v w} Λ) ⥤ _) := by
  have : RepresentablyFlat (Scheme.proetaleBaseChange g) := flat_of_preservesFiniteLimits _
  refine Stacks.Topology.lan_preservesFiniteLimits_of_flat _ fun V => ?_
  have : IsFiltered (CostructuredArrow (Scheme.proetaleBaseChange g).op V) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (Scheme.proetaleBaseChange g) (Opposite.unop V))
  have : PreservesColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{max (u + 1) v w} Λ) AddCommGrpCat.{max (u + 1) v w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v w, v, u, u + 1} Λ
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (forget AddCommGrpCat.{max (u + 1) v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v w, max (u + 1) v w, u, u + 1} _
  exact inferInstanceAs (PreservesColimitsOfShape
    (CostructuredArrow (Scheme.proetaleBaseChange g).op V)
    (forget₂ (ModuleCat.{max (u + 1) v w} Λ) AddCommGrpCat.{max (u + 1) v w} ⋙
      forget AddCommGrpCat.{max (u + 1) v w}))

variable {Λ}

variable (Λ) in
/-- Inverse image of pro-étale sheaves of modules is left adjoint to direct image, which is
restriction along base change. -/
public def proetaleModuleInverseImageAdjunction {Z X : Scheme.{u}} (g : Z ⟶ X) :
    proetaleModuleInverseImage.{u, v, w} g Λ ⊣
      (Scheme.proetaleBaseChange g).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) v w} Λ) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

variable (Λ) in
/-- Inverse image of pro-étale sheaves of modules agrees with the inverse image along base change
defined as a chosen left adjoint of direct image. -/
public def proetaleModuleInverseImageIsoSheafPullback {Z X : Scheme.{u}} (g : Z ⟶ X) :
    proetaleModuleInverseImage.{u, v, w} g Λ ≅
      (Scheme.proetaleBaseChange g).sheafPullback (ModuleCat.{max (u + 1) v w} Λ)
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) :=
  (proetaleModuleInverseImageAdjunction.{u, v, w} Λ g).leftAdjointUniq
    (Functor.sheafAdjunctionContinuous _ _ _ _)

/-- **Inverse image of pro-étale sheaves of modules is left exact.** -/
public instance preservesFiniteLimits_proetaleModuleInverseImage {Z X : Scheme.{u}}
    (g : Z ⟶ X) : PreservesFiniteLimits (proetaleModuleInverseImage.{u, v, w} g Λ) := by
  have := preservesFiniteLimits_lan_op_proetaleBaseChange.{u, v, w} Λ g
  have := Functor.sheafPullbackConstruction.preservesFiniteLimits (Scheme.proetaleBaseChange g)
    (ModuleCat.{max (u + 1) v w} Λ) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
  exact preservesFiniteLimits_of_natIso (proetaleModuleInverseImageIsoSheafPullback Λ g).symm

/-- **Inverse image of pro-étale sheaves of modules is right exact**, being a left adjoint. -/
public instance preservesFiniteColimits_proetaleModuleInverseImage {Z X : Scheme.{u}}
    (g : Z ⟶ X) : PreservesFiniteColimits (proetaleModuleInverseImage.{u, v, w} g Λ) := by
  have := (proetaleModuleInverseImageAdjunction.{u, v, w} Λ g).leftAdjoint_preservesColimits
  infer_instance

/-- Inverse image of pro-étale sheaves of modules is additive, since it preserves binary
products. -/
public instance additive_proetaleModuleInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleModuleInverseImage.{u, v, w} g Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (Λ) in
/-- **Inverse image is compatible with composition.** Inverse image along `b` followed by
inverse image along `a` is inverse image along `a ≫ b`, canonically. -/
public def proetaleModuleInverseImageCompIso {Y Z X : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X) :
    proetaleModuleInverseImage.{u, v, w} b Λ ⋙ proetaleModuleInverseImage.{u, v, w} a Λ ≅
      proetaleModuleInverseImage.{u, v, w} (a ≫ b) Λ :=
  Functor.isoWhiskerRight (proetaleModuleInverseImageIsoSheafPullback Λ b) _ ≪≫
    Functor.isoWhiskerLeft _ (proetaleModuleInverseImageIsoSheafPullback Λ a) ≪≫
    Functor.sheafPullbackComp' (Scheme.proetaleBaseChangeCompIso a b) _ _ _ _ ≪≫
    (proetaleModuleInverseImageIsoSheafPullback Λ (a ≫ b)).symm

/-- **Inverse image preserves local constancy of finite type.** If a sheaf of `Λ`-modules on the
small pro-étale site of `X` is locally constant of finite type, so is its inverse image along any
morphism of schemes `g : Z ⟶ X`; the constant values are unchanged. -/
public theorem isFiniteTypeLocallyConstantModuleSheaf_proetaleModuleInverseImage
    {Z X : Scheme.{u}} (g : Z ⟶ X)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology X) Λ F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology Z) Λ ((proetaleModuleInverseImage.{u, v, w} g Λ).obj F) := by
  have (S : Scheme.{u}) (U : S.ProEt) :
      HasSheafify ((Scheme.ProEt.topology S).over U) (ModuleCat.{max (u + 1) v w} Λ) :=
    hasSheafify_moduleCat.{u + 1, u, max v w, v} _ _
  exact ObjectProperty.prop_of_iso _
    ((proetaleModuleInverseImageIsoSheafPullback.{u, v, w} Λ g).app F).symm
    (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_sheafPullback
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) Λ (Scheme.proetaleBaseChange g)
      (CoverPreserving.of_isContinuous _ _ _) F hF)

end ProEtale

end AlgebraicGeometry

end
