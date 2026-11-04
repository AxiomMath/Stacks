module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModuleDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringAbelianTotalPushforwardComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedUnitAfterAnExactFaithfulFunctor

/-!
# Cohomological descent for modules along a hypercovering of a site

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of commutative rings
on it and let `K` be a hypercovering of `C`. With `O = a⁻¹O_C` on the total site and
`a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` the ringed augmentation of Stacks 0D9W, Stacks 0DA0
asserts that for every `E` in the unbounded derived category `D(O_C)` the map

`E ⟶ Ra_*La^*E`

is an isomorphism. This file proves it with no hypothesis beyond the hypercovering conditions
on `K`, by discharging the two inputs of
`AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit`:

* the underived unit `M ⟶ a_*a^*M` is invertible, which is the module form of Stacks 0D8E
  (`CategoryTheory.SimplicialSiteSituation.RingedAugmentation`
  `.isIso_pullbackAdjPushforwardModules_unit`, Stacks 0D9Z);
* `a^*` of a K-injective complex of `O_C`-modules computes `Ra_*`
  (`pullbackComputesDerivedPushforward_of_hypercoveringOfTerminal`).

The second is the source's reduction to abelian sheaves. Forgetting the module structure is
exact and reflects isomorphisms; it carries `a_*` to the direct image of abelian sheaves of the
morphism of topoi of Stacks 0D70 and `a^*` to its inverse image. The underlying abelian complex
of a K-injective complex of `O`-modules computes the abelian `Ra_*` (Stacks 0D6J for the
cocontinuous localization functor `j_total`, which presents that direct image), and at `a⁻¹` of
*every* complex of abelian sheaves on `C` the comparison `a_* ⟶ Ra_*` is invertible: there it
is the middle factor of the abelian derived unit of Stacks 0D8G, whose outer factor is the
localization of the underived unit of Stacks 0D8E (2).

This is the case of a hypercovering of the final object; the case of a hypercovering of an
object `X`, over the slice site `C/X`, is analogous.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.inverseImageRingedAugmentationPushforwardToSheafIso`
  and `.inverseImageRingedAugmentationPullbackToSheafIso`: for any augmentation with
  `O = a⁻¹O_D`, the underlying abelian sheaves of `a_*F` and `a^*M` are the abelian direct and
  inverse images of the underlying abelian sheaves.

## Main results

* `CategoryTheory.SimplicialSiteSituation`
  `.pullbackComputesDerivedPushforward_of_inverseImageRingedAugmentation`: **the reduction of
  module cohomological descent to abelian sheaves**, for any augmentation with `O = a⁻¹O_D`:
  `a^*` of a K-injective complex of `O_D`-modules computes `Ra_*` as soon as underlying abelian
  complexes of K-injective complexes of `O`-modules compute the abelian `Ra_*` and `a⁻¹` of every
  complex of abelian sheaves does.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.isIso_pullbackAdjPushforwardModules_unit_of_hypercoveringOfTerminal`: the module form of
  Stacks 0D8E, `M = a_*a^*M`.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.pullbackComputesDerivedPushforward_of_hypercoveringOfTerminal`: `a^*` of a K-injective
  complex of `O_C`-modules computes `Ra_*`.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.isIso_derivedPullbackPushforwardUnit_of_hypercoveringOfTerminal`
  and `.isIso_derivedPullbackPushforwardUnit_app_of_hypercoveringOfTerminal`: **Stacks 0DA0**.

## References

* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

universe u

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

namespace CategoryTheory.SimplicialSiteSituation

/-! ### Reduction to abelian sheaves, for any augmentation with `O = a⁻¹O_D` -/

section General

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (OD : Sheaf K CommRingCat.{u})

/-- **The underlying abelian sheaf of the direct image of a sheaf of modules along the ringed
augmentation with `O = a⁻¹O_D` is the direct image of its underlying abelian sheaf.** On
underlying sheaves of sets the direct image of modules is the direct image of the morphism of
topoi of Stacks 0D70 on the nose. -/
def inverseImageRingedAugmentationPushforwardToSheafIso :
    (inverseImageRingedAugmentation S D K a OD).totalRingedHom.pushforwardModules ⋙
        SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ Augmentation.abelianTotalPushforward S D K a := by
  haveI : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (S.totalRingedTopos (inverseImageRingedAugmentation S D K a OD).O).O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  haveI := Augmentation.additive_abelianTotalPushforward S D K a
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _ inferInstance
    ⟨fun {_ _ f g} => ((Augmentation.abelianTotalPushforward S D K a).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((Augmentation.abelianTotalPushforward S D K a).map_add)⟩ (Iso.refl _)

/-- **The underlying abelian sheaf of the pullback of a sheaf of modules along the ringed
augmentation with `O = a⁻¹O_D` is the inverse image of its underlying abelian sheaf.** The
structure map of the augmentation is invertible, so on underlying sheaves of sets the pullback
of modules is the inverse image of the morphism of topoi of Stacks 0D70
(`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso`). This is the source's
`a^* = a⁻¹`. -/
def inverseImageRingedAugmentationPullbackToSheafIso :
    (inverseImageRingedAugmentation S D K a OD).totalRingedHom.toModulesHom.pullbackModules ⋙
        SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ Augmentation.totalInverseImageAb S D K a := by
  haveI : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (inverseImageRingedAugmentation S D K a OD).augmentationRingedTopos.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _
    (inferInstanceAs ((inverseImageRingedAugmentation S D K a
      OD).totalRingedHom.toModulesHom.pullbackModules ⋙ SheafOfModules.toSheaf _).Additive)
    ⟨fun {_ _ f g} => ((Augmentation.totalInverseImageAb S D K a).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((Augmentation.totalInverseImageAb S D K a).map_add)⟩
    (RingedToposHom.pullbackUnderlyingIsoOfIsIso
      (inverseImageRingedAugmentation S D K a OD).totalRingedHom)

/-- **`a^*` of a K-injective complex of `O_D`-modules computes `Ra_*`, as soon as two abelian
facts hold**: the underlying abelian complex of a K-injective complex of `O`-modules on the total
site computes the abelian `Ra_*` (`hU`, the source's appeal to Stacks 0D6J), and `a⁻¹` of every
complex of abelian sheaves on `D` computes `Ra_*` (`hinv`).

This is the source's reduction of Stacks 0DA0 to abelian sheaves. The comparison `a_* ⟶ Ra_*`
at `a^*I` is checked after forgetting the module structure
(`Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget`), which carries `a_*`
and `a^*` to the abelian direct and inverse images of the morphism of topoi of Stacks 0D70
(`inverseImageRingedAugmentationPushforwardToSheafIso` and `...PullbackToSheafIso`). -/
theorem pullbackComputesDerivedPushforward_of_inverseImageRingedAugmentation
    (hU : ∀ (O : Sheaf S.totalTopology RingCat.{u}) (I : CochainComplex (SheafOfModules.{u} O) ℤ),
      I.IsKInjective → IsIso ((Augmentation.derivedTotalPushforwardUnit S D K a).app
        ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))))
    (hinv : ∀ M : HomotopyCategory (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ),
      IsIso ((Augmentation.derivedTotalPushforwardUnit S D K a).app
        (((Augmentation.totalInverseImageAb S D K a).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M))) :
    RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (inverseImageRingedAugmentation S D K a OD).totalRingedHom := by
  intro I hI
  let A := inverseImageRingedAugmentation S D K a OD
  let UT := SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (S.totalRingedTopos A.O).O)
  let UC := SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    A.augmentationRingedTopos.O)
  have hU' := fun (I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (S.totalRingedTopos A.O).O)) ℤ) (hI' : I'.IsKInjective) =>
    (NatTrans.isIso_app_iff_of_iso _
      ((Functor.mapHomotopyCategoryFactors UT (ComplexShape.up ℤ)).app I')).mpr
      (hU _ I' hI')
  let eP := inverseImageRingedAugmentationPullbackToSheafIso S D K a OD
  let ι : (UT.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((A.totalRingedHom.toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      ((Augmentation.totalInverseImageAb S D K a).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((UC.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    HomologicalComplex.Hom.isoOfComponents (fun i => eP.app (I.X i))
      (fun i j _ => (eP.hom.naturality (I.d i j)).symm)
  have hK' := (NatTrans.isIso_app_iff_of_iso
    (Augmentation.derivedTotalPushforwardUnit S D K a)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso ι)).mpr
      (hinv ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((UC.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
  have := Augmentation.additive_abelianTotalPushforward S D K a
  exact @Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    A.totalRingedHom.pushforwardModules (Augmentation.abelianTotalPushforward S D K a)
    UT UC _ _ ⟨fun {_ _ f g} => UT.map_add (f := f) (g := g)⟩
    ⟨fun {_ _ f g} => UC.map_add (f := f) (g := g)⟩
    (inferInstance : PreservesFiniteLimits UT)
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : PreservesFiniteLimits UC)
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : UC.ReflectsIsomorphisms)
    (inverseImageRingedAugmentationPushforwardToSheafIso S D K a OD)
    _ (Augmentation.derivedTotalPushforward S D K a) _
    (Augmentation.derivedTotalPushforwardUnit S D K a) _ hU' _ hK'

end General

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation SemiRepresentable

section Terminal

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} P) (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- **The module form of Stacks 0D8E for a hypercovering of the site: `M = a_*a^*M`.** The unit
of `a^* ⊣ a_*` on sheaves of `O_C`-modules is an isomorphism; this is the quasi-inverse clause of
Stacks 0D9Z, `a^*` being fully faithful. -/
theorem isIso_pullbackAdjPushforwardModules_unit_of_hypercoveringOfTerminal :
    IsIso (RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringRingedAugmentation P H OC).totalRingedHom).unit :=
  have := isIso_inverseImageRingedAugmentation_fSharpInverseImage
    (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
    (situationAugmentation P.toGrothendieck H.toSimplicialObject) OC
  RingedAugmentation.isIso_pullbackAdjPushforwardModules_unit H
    (inverseImageRingedAugmentation (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C)
      P.toGrothendieck (situationAugmentation P.toGrothendieck H.toSimplicialObject) OC)

/-- **For a hypercovering of the site, `a^*` of a K-injective complex of `O_C`-modules computes
`Ra_*`.** This is the second input of
`AlgebraicGeometry.RingedToposHom.isIso_derivedPullbackPushforwardUnit`, obtained from
`CategoryTheory.SimplicialSiteSituation`
`.pullbackComputesDerivedPushforward_of_inverseImageRingedAugmentation` with its two abelian
inputs: `isIso_derivedTotalPushforwardUnit_app_underlying_of_isKInjective` (Stacks 0D6J for the
localization functor `j_total`) and
`isIso_derivedTotalPushforwardUnit_app_inverseImage_of_hypercoveringOfTerminal` (Stacks 0D8G and
Stacks 0D8E (2)). -/
theorem pullbackComputesDerivedPushforward_of_hypercoveringOfTerminal :
    RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (hypercoveringRingedAugmentation P H OC).totalRingedHom :=
  pullbackComputesDerivedPushforward_of_inverseImageRingedAugmentation
    (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
    (situationAugmentation P.toGrothendieck H.toSimplicialObject) OC
    (isIso_derivedTotalPushforwardUnit_app_underlying_of_isKInjective P.toGrothendieck
      H.toSimplicialObject)
    (isIso_derivedTotalPushforwardUnit_app_inverseImage_of_hypercoveringOfTerminal P H)

/-- **Stacks 0DA0, as an invertible natural transformation.** For a site `C` with equalizers
and fibre products, a sheaf of commutative rings `O_C` on it and a hypercovering `K` of `C`, the
canonical map `E ⟶ Ra_*La^*E` along the ringed augmentation of Stacks 0D9W is an isomorphism,
naturally in `E` in the unbounded derived category `D(O_C)`. Nothing is assumed beyond the
hypercovering conditions on `K`. -/
theorem isIso_derivedPullbackPushforwardUnit_of_hypercoveringOfTerminal :
    IsIso (RingedToposHom.derivedPullbackPushforwardUnit
      (hypercoveringRingedAugmentation P H OC).totalRingedHom) :=
  RingedToposHom.isIso_derivedPullbackPushforwardUnit
    (hypercoveringRingedAugmentation P H OC).totalRingedHom
    (isIso_pullbackAdjPushforwardModules_unit_of_hypercoveringOfTerminal P H OC)
    (pullbackComputesDerivedPushforward_of_hypercoveringOfTerminal P H OC)

/-- **Stacks 0DA0.** Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of
commutative rings on it and let `K` be a hypercovering of `C`. With `O = a⁻¹O_C` on the total
site and `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` the ringed augmentation of Stacks 0D9W, the
canonical map

`E ⟶ R a_* L a^* E`

is an isomorphism for every object `E` of the unbounded derived category `D(O_C)`. -/
theorem isIso_derivedPullbackPushforwardUnit_app_of_hypercoveringOfTerminal
    (E : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (hypercoveringRingedAugmentation P H OC).augmentationRingedTopos.J))
      (hypercoveringRingedAugmentation P H OC).augmentationRingedTopos.O))) :
    IsIso ((RingedToposHom.derivedPullbackPushforwardUnit
      (hypercoveringRingedAugmentation P H OC).totalRingedHom).app E) :=
  have := isIso_derivedPullbackPushforwardUnit_of_hypercoveringOfTerminal P H OC
  NatIso.isIso_app_of_isIso _ E

end Terminal

end CategoryTheory.SimplicialSemiRepresentable

end
