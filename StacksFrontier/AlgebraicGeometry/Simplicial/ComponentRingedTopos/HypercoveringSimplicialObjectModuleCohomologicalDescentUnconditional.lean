module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSimplicialObjectModuleDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSimplicialObjectModuleCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedUnitAfterAnExactFaithfulFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.UnboundedBaseChangeForACocontinuousSquare
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectDerivedPushforwardUnconditional
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardSituation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardUnconditional

/-!
# Cohomological descent for modules along a hypercovering of an object

Let `C` be a site with fibre products, let `O_C` be a sheaf of commutative rings on it, let `X`
be an object of `C` and set `O_X = O_C|_{C/X}`. Let `K` be a hypercovering of `X` by
semi-representable objects, with total site `(C/K)_total` carrying the pulled-back structure
sheaf `O = a⁻¹O_X` and the morphism of ringed topoi `a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)`
of Stacks 0D9X. Stacks 0DA5 asserts that for `E` in the unbounded derived category `D(O_X)` the
map

`E ⟶ Ra_*La^*E`

is an isomorphism, and Stacks 0DAC is the same assertion for a hypercovering `U ⟶ X` of `X` by
a simplicial object of `C`, read as a hypercovering by semi-representable objects with one
summand in each degree.

The source's proof is a reduction to abelian sheaves: since `a⁻¹O_X = O` one has `La^* = a^* = a⁻¹`,
the derived direct image of modules agrees with that of abelian sheaves by Stacks 0D6J, and the
assertion becomes its abelian counterpart Stacks 0D8L. The same reduction is made here, at the one
place where it is needed: the map is the derived unit of `La^* ⊣ Ra_*`, which by
`AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit` is invertible as soon as the
underived unit `M ⟶ a_*a^*M` is invertible and `a^*` of a K-injective complex `I` of `O_X`-modules
computes `Ra_*`. The first input is Stacks 0DA4 (`isIso_pullbackAdjPushforwardModules_unit_over`).
For the second input, forgetting the module structure is exact and reflects isomorphisms, it carries
`a_*` to the direct image of abelian sheaves along the localization functor `j_total` and `a^*` to
restriction along `j_total`; the underlying abelian complex of a K-injective complex of `O`-modules
computes the abelian `Ra_*` by Stacks 0D6J for the cocontinuous functor `j_total`; and the
comparison `a_* ⟶ Ra_*` is invertible at `a⁻¹` of *every* complex of abelian sheaves on `C/X`,
because there it is the abelian derived unit of Stacks 0D8L composed with the inverse of the
underived unit of Stacks 0D8K.

## Main definitions

All declarations are in the namespace `CategoryTheory.SimplicialSemiRepresentable`.

* `hypercoveringObjectPushforwardModulesToSheafIso`: the underlying abelian sheaf of `a_*F` is the
  direct image of the underlying abelian sheaf of `F` along `j_total`.
* `hypercoveringObjectPullbackModulesToSheafIso`: the underlying abelian sheaf of `a^*M` is the
  restriction along `j_total` of the underlying abelian sheaf of `M`.

## Main results

* `isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage_of_isHypercovering`: for a
  hypercovering of `X`, `a⁻¹` of every complex of abelian sheaves on `C/X` computes `Ra_*`.
* `pullbackComputesDerivedPushforward_of_isHypercovering`: `a^*` of a K-injective complex of
  `O_X`-modules computes the derived direct image of modules.
* `isIso_derivedPullbackPushforwardUnit_app_of_isHypercovering`: for a hypercovering `K` of `X`
  by semi-representable objects, `E ⟶ Ra_*La^*E` is an isomorphism for every `E` in `D(O_X)`.
* `isIso_derivedPullbackPushforwardUnit_app_of_isHypercoveringAugmentation`: the same for a
  hypercovering `U ⟶ X` of `X` by a simplicial object of `C`.

## Implementation notes

The ringed augmentation is the one of Stacks 0D9X attached by
`CategoryTheory.SimplicialSemiRepresentable.hypercoveringObjectRingedAugmentation`, and the
coefficients are the sheaves of `O_X`-modules on the slice site `C/X`
(`simplicialObjectRingedAugmentation_augmentationRingedTopos_J` and `_O`). The sheafification
instances its types need are the three stated for an arbitrary simplicial-site situation in
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringObjectModuleDescent`;
being attached there as local instances they are not visible here, and are re-attached below.

## References

* [Stacks Project, Tag 0DAC](https://stacks.math.columbia.edu/tag/0DAC)
* [Stacks Project, Tag 0DA5](https://stacks.math.columbia.edu/tag/0DA5)
* [Stacks Project, Tag 0DA4](https://stacks.math.columbia.edu/tag/0DA4)
* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Section 85.21 (Tag 09X8)](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation SemiRepresentable

section Over

attribute [local instance] additive_abelianTotalPushforwardOver
  additive_abelianTotalInverseImageOver preservesFiniteColimits_abelianTotalInverseImageOver
  hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver
  hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- **For a hypercovering of `X`, the inverse image of every complex of abelian sheaves on `C/X`
computes `Ra_*`.** At `a⁻¹M` the comparison `a_* ⟶ Ra_*` is the middle factor of the derived unit
`M ⟶ Ra_*a⁻¹M` of Stacks 0D8L, the outer factor being the localization of the underived unit
`M ⟶ a_*a⁻¹M`; both units are invertible for a hypercovering, by Stacks 0D8L and Stacks 0D8K. -/
theorem isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage_of_isHypercovering
    (hK : IsHypercovering P K)
    (M : HomotopyCategory (AbelianSheavesOver P.toGrothendieck X) (ComplexShape.up ℤ)) :
    IsIso ((derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X K).app
      (((abelianTotalInverseImageOver P.toGrothendieck X K).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj M)) := by
  have := isIso_homotopyAugmentationUnitOver_of_isHypercovering P K hK
  refine (isIso_derivedAbelianTotalPushforwardOverUnit_app_iff P.toGrothendieck X K M
    inferInstance).mpr ?_
  have h := isIso_derivedAugmentationUnitOver_app_of_isHypercovering_unconditional P K hK
    (DerivedCategory.Qh.obj M)
  rw [← whiskerLeft_derivedAugmentationUnitOver]
  exact h

/-- **The underlying abelian sheaf of the direct image of a sheaf of modules along the
augmentation is the direct image along `j_total` of its underlying abelian sheaf.** On
underlying sheaves of sets the direct image of modules is the direct image of the morphism of
topoi of Stacks 0D70 on the nose; that is the direct image of abelian sheaves along it, which
`abelianTotalPushforwardOverIso` identifies with the direct image along `j_total`. -/
def hypercoveringObjectPushforwardModulesToSheafIso :
    (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom.pushforwardModules ⋙
        SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ abelianTotalPushforwardOver P.toGrothendieck X K := by
  haveI : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (hypercoveringObjectRingedAugmentation P K OC).O).O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  haveI := Augmentation.additive_abelianTotalPushforward (situation (P.toGrothendieck.over X) K)
    (Cat.of (Over X)) (P.toGrothendieck.over X) (situationAugmentation (P.toGrothendieck.over X) K)
  refine Iso.trans ?_
    (Functor.isoWhiskerLeft _ (abelianTotalPushforwardOverIso P.toGrothendieck X K))
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _ inferInstance
    ⟨fun {_ _ f g} => ((Augmentation.abelianTotalPushforward _ _ _ _).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((Augmentation.abelianTotalPushforward _ _ _ _).map_add)⟩ (Iso.refl _)

/-- **The underlying abelian sheaf of the pullback of a sheaf of modules along the augmentation
is the restriction along `j_total` of its underlying abelian sheaf.** The structure map of the
augmentation is invertible, so on underlying sheaves of sets the pullback of modules is the
inverse image of the morphism of topoi of Stacks 0D70
(`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso`); that is the inverse image of
abelian sheaves along it, which `situationTotalInverseImageAbIso` identifies with restriction
along `j_total`. -/
def hypercoveringObjectPullbackModulesToSheafIso :
    (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom.toModulesHom.pullbackModules ⋙
        SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ abelianTotalInverseImageOver P.toGrothendieck X K := by
  haveI : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (hypercoveringObjectRingedAugmentation P K OC).augmentationRingedTopos.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  refine Iso.trans ?_ (Functor.isoWhiskerLeft _
    (situationTotalInverseImageAbIso (P.toGrothendieck.over X) K))
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _
    (inferInstanceAs ((hypercoveringObjectRingedAugmentation P K
      OC).totalRingedHom.toModulesHom.pullbackModules ⋙ SheafOfModules.toSheaf _).Additive)
    ⟨fun {_ _ f g} => ((Augmentation.totalInverseImageAb _ _ _ _).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((Augmentation.totalInverseImageAb _ _ _ _).map_add)⟩
    (RingedToposHom.pullbackUnderlyingIsoOfIsIso
      (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom)

/-- **For a hypercovering of `X`, `a^*` of a K-injective complex of `O_X`-modules computes
`Ra_*`.** This is the second input of
`AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit`. The comparison
`a_* ⟶ Ra_*` at `a^*I` is checked after forgetting the module structure
(`Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget`): forgetting carries
`a_*` and `a^*` to the direct image and the restriction along `j_total`; the underlying abelian
complex of a K-injective complex of `O`-modules computes the abelian `Ra_*` by Stacks 0D6J for
the cocontinuous functor `j_total`; and the underlying abelian complex of `a^*I` is `a⁻¹` of that
of `I`, where the abelian comparison is invertible by
`isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage_of_isHypercovering`. -/
theorem pullbackComputesDerivedPushforward_of_isHypercovering (hK : IsHypercovering P K) :
    RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom := by
  intro I hI
  have hU := fun (I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (hypercoveringObjectRingedAugmentation P K OC).O).O)) ℤ)
      (hI' : I'.IsKInjective) =>
   @Stacks.Cohomology.CocontinuousForgetModule.abelianPushforwardUnit_isIso_at_underlying_kInjective
      _ _ _ _ (situation (P.toGrothendieck.over X) K).totalTopology (P.toGrothendieck.over X)
      (totalForget K) (totalForget_isCocontinuous (P.toGrothendieck.over X) K) _ _ _
      (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (hypercoveringObjectRingedAugmentation P K OC).O).O) I' hI'
  let eP := hypercoveringObjectPullbackModulesToSheafIso P K OC
  let ι : ((SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (hypercoveringObjectRingedAugmentation P K OC).O).O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((hypercoveringObjectRingedAugmentation P K
          OC).totalRingedHom.toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      ((abelianTotalInverseImageOver P.toGrothendieck X K).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (hypercoveringObjectRingedAugmentation P K
        OC).augmentationRingedTopos.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
    HomologicalComplex.Hom.isoOfComponents (fun i => eP.app (I.X i))
      (fun i j _ => (eP.hom.naturality (I.d i j)).symm)
  have hK' := (NatTrans.isIso_app_iff_of_iso
    (derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X K)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso ι)).mpr
      (isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage_of_isHypercovering P K hK
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
  exact @Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom.pushforwardModules
    (abelianTotalPushforwardOver P.toGrothendieck X K)
    (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (hypercoveringObjectRingedAugmentation P K OC).O).O))
    (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (hypercoveringObjectRingedAugmentation P K OC).augmentationRingedTopos.O))
    _ _ ⟨fun {_ _ f g} => (SheafOfModules.toSheaf _).map_add (f := f) (g := g)⟩
    ⟨fun {_ _ f g} => (SheafOfModules.toSheaf _).map_add (f := f) (g := g)⟩
    (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((situation (P.toGrothendieck.over X) K).totalRingedTopos
          (hypercoveringObjectRingedAugmentation P K OC).O).O)))
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (hypercoveringObjectRingedAugmentation P K OC).augmentationRingedTopos.O)))
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (hypercoveringObjectRingedAugmentation P K
        OC).augmentationRingedTopos.O)).ReflectsIsomorphisms)
    (hypercoveringObjectPushforwardModulesToSheafIso P K OC)
    _ (derivedAbelianTotalPushforwardOver P.toGrothendieck X K) _
    (derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X K) _ hU _ hK'

/-- **Stacks 0DA5.** Let `C` be a site with fibre products, `X` an object of `C`, `O_C` a sheaf
of commutative rings on `C` and `K` a hypercovering of `X`. With `O_X = O_C|_{C/X}`,
`O = a⁻¹O_X` on the total site of `K` and `a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)` the ringed
augmentation of Stacks 0D9X, the canonical map

`E ⟶ R a_* L a^* E`

is an isomorphism for every object `E` of the unbounded derived category `D(O_X)` of sheaves of
`O_X`-modules. Nothing is assumed beyond the hypercovering conditions on `K`: both inputs of the
reduction `AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit` are proved
here from `hK`: the underived unit `M ⟶ a_*a^*M` by Stacks 0DA4
(`isIso_pullbackAdjPushforwardModules_unit_over`), and the acyclicity of `a^*` of a K-injective
complex by `pullbackComputesDerivedPushforward_of_isHypercovering`, which consumes the
hypercovering conditions through Stacks 0D8L and 0D8K. In particular this is not the conditional
`isIso_derivedPullbackPushforwardUnit_app_of_hypercovering_over` (in the namespace
`Stacks.CategoryTheory.Hypercovering`), which takes those two inputs as hypotheses and does not
use `hK`; that declaration carries no tag.
A hypercovering of `X` is, as in the source, a simplicial semi-representable object over `X`
(`IsHypercovering`), and the rings are commutative, following the Stacks convention. -/
@[stacks 0DA5 "for a site with fibre products, a sheaf of rings and a hypercovering K of an \
object X, the map E -> Ra_*La^*E is an isomorphism for every E in the unbounded D(O_X)"]
theorem isIso_derivedPullbackPushforwardUnit_app_of_isHypercovering (hK : IsHypercovering P K)
    (E : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (hypercoveringObjectRingedAugmentation P K OC).augmentationRingedTopos.J))
      (hypercoveringObjectRingedAugmentation P K OC).augmentationRingedTopos.O))) :
    IsIso ((AlgebraicGeometry.RingedToposHom.derivedPullbackPushforwardUnit
      (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom).app E) :=
  have := AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit
    (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom
    (isIso_pullbackAdjPushforwardModules_unit_over P K OC hK)
    (pullbackComputesDerivedPushforward_of_isHypercovering P K OC hK)
  NatIso.isIso_app_of_isIso _ E

end Over

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- **Stacks 0DAC.** Let `C` be a site with fibre products, `X` an object of `C`, `O_C` a sheaf
of commutative rings on `C` and `a : U ⟶ X` a hypercovering of `X` in `C` by a simplicial
object `U` of `C` (Stacks, Section 85.21). With `O_X = O_C|_{C/X}`, `O = a⁻¹O_X` on the total
site of `U` and `a : (Sh((C/U)_total), O) ⟶ (Sh(C/X), O_X)` the ringed augmentation of
Stacks 0D9X, the canonical map

`E ⟶ R a_* L a^* E`

is an isomorphism for every object `E` of the unbounded derived category `D(O_X)` of sheaves of
`O_X`-modules.

As in the source this is Stacks 0DA5 for the hypercovering of `X` by semi-representable objects
with one summand in each degree that `a` determines
(`CategoryTheory.SimplicialSemiRepresentable.IsHypercoveringAugmentation.isHypercovering`). -/
@[stacks 0DAC]
theorem isIso_derivedPullbackPushforwardUnit_app_of_isHypercoveringAugmentation
    (h : IsHypercoveringAugmentation P U a)
    (E : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
        OC).augmentationRingedTopos.J))
      (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
        OC).augmentationRingedTopos.O))) :
    IsIso ((AlgebraicGeometry.RingedToposHom.derivedPullbackPushforwardUnit
      (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
        OC).totalRingedHom).app E) :=
  isIso_derivedPullbackPushforwardUnit_app_of_isHypercovering P
    (associatedSimplicialObject.{u} U a) OC (h.isHypercovering P U a) E

end CategoryTheory.SimplicialSemiRepresentable

end
