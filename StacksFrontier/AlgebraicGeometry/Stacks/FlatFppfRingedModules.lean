module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposTriangle
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Pullback of modules along the flat-fppf comparison is restriction

Let `𝒳` be an algebraic stack over `S` and let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the
morphism of ringed topoi `AlgebraicGeometry.Stack.FlatFppf.ringedToposMorphism`. Pullback of
sheaves of modules along `g` is restriction of sheaves of modules along the inclusion of the flat
objects.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.ringedToposModulesHom`: the flat-fppf morphism of ringed
  topoi, presented as a `Stacks.Sheaves.RingedToposModules.RingedToposHom`.
* `AlgebraicGeometry.Stack.FlatFppf.ringRestrictionIso`: the inverse image of the fppf
  structure sheaf is its restriction, at the level of sheaves of rings.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso`: pullback of sheaves of modules along the
  flat-fppf morphism of ringed topoi is restriction of sheaves of modules along the inclusion of
  the flat objects.
* `AlgebraicGeometry.Stack.FlatFppf.ringedToposModulesHom_fSharpInverseImage`: the
  inverse-image form of the structure map of that morphism is the ring-level restriction
  comparison.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry

universe u w

namespace Stack.FlatFppf

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- Sheafification of `AddCommGrpCat.{u}`-valued presheaves on the flat-fppf site exists. -/
theorem hasSheafify_addCommGrpCat : HasSheafify (topology B S hS 𝒳) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} (topology B S hS 𝒳) _

/-- On the flat-fppf site, the sheafification equivalences for `AddCommGrpCat.{u}`-valued
presheaves are the local bijections. -/
theorem wEqualsLocallyBijective_addCommGrpCat :
    (topology B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u}
    (topology B S hS 𝒳)

attribute [local instance] hasSheafify_addCommGrpCat wEqualsLocallyBijective_addCommGrpCat

/-- The inverse image of the fppf structure sheaf along the flat-fppf morphism of topoi is its
restriction to the flat-fppf site, as a sheaf of rings. -/
noncomputable def ringRestrictionIso :
    inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1} (toposMorphismOnRings B S hS 𝒳)
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (fppfRingedTopos B S hS 𝒳).O) ≅
      Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (ringedTopos B S hS 𝒳).O :=
  restrictionRingIso (topology B S hS 𝒳) (fppfTopology B S hS 𝒳)
    (objectProperty B S hS 𝒳).ι
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (fppfRingedTopos B S hS 𝒳).O)

/-- The flat-fppf morphism of ringed topoi `AlgebraicGeometry.Stack.FlatFppf.ringedToposMorphism`,
presented as a `Stacks.Sheaves.RingedToposModules.RingedToposHom`: the same morphism of topoi and
the same inverse-image structure map, read at the `RingCat` level. -/
noncomputable def ringedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (ringedTopos B S hS 𝒳) (fppfRingedTopos B S hS 𝒳) :=
  RingedToposHom.ofFSharpInverseImage (X := ringedTopos B S hS 𝒳)
    (Y := fppfRingedTopos B S hS 𝒳) (toposMorphismOnRings B S hS 𝒳)
    ((sheafCompose (topology B S hS 𝒳) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (ringedToposMorphism B S hS 𝒳).fSharpInverseImage)

/-- The inverse-image form of the structure map of the flat-fppf morphism of ringed topoi is the
ring-level restriction comparison `AlgebraicGeometry.Stack.FlatFppf.ringRestrictionIso`. -/
theorem ringedToposModulesHom_fSharpInverseImage :
    (ringedToposModulesHom B S hS 𝒳).fSharpInverseImage = (ringRestrictionIso B S hS 𝒳).hom :=
  congrArg
    (fun m ↦ (sheafCompose (topology B S hS 𝒳) (forget₂ CommRingCat.{u} RingCat.{u})).map m)
    (ringedToposMorphism_fSharpInverseImage B S hS 𝒳)

/-- Pullback of sheaves of modules along the flat-fppf morphism of ringed topoi is restriction of
sheaves of modules along the inclusion of the flat objects, over the fppf structure sheaf and its
restriction. -/
@[stacks 0788 "pullback of modules along it, as an identification"]
noncomputable def modulePullbackIso :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1}
        (ringedToposModulesHom B S hS 𝒳) ≅
      moduleRestriction B S hS 𝒳 := by
  let f := ringedToposModulesHom B S hS 𝒳
  let E := extendScalarsFSharp.{u, u, u, u + 1, u, u + 1} f
  let R := SheafOfModules.restrictScalars.{u, u, u, u + 1} (ringRestrictionIso B S hS 𝒳).hom
  let adj : E ⊣ R :=
    Adjunction.ofNatIsoRight
      (extendRestrictScalarsAdjunction (topology B S hS 𝒳) (fSharpCommRing f)
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1} f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
            (fppfRingedTopos B S hS 𝒳).O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (ringedTopos B S hS 𝒳).O).property)
      (eqToIso (congrArg SheafOfModules.restrictScalars
        ((commRingSheafMap_fSharpCommRing f).trans
          (ringedToposModulesHom_fSharpInverseImage B S hS 𝒳))))
  let ff := RingedSite.restrictScalarsFullyFaithful (ringRestrictionIso B S hS 𝒳).hom
  have hc : IsIso adj.counit :=
    @Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ E R adj ff.full ff.faithful
  exact Functor.isoWhiskerRight
      (restrictionModuleIso (topology B S hS 𝒳) (fppfTopology B S hS 𝒳)
        (objectProperty B S hS 𝒳).ι
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (fppfRingedTopos B S hS 𝒳).O)) E ≪≫
    Functor.associator (moduleRestriction B S hS 𝒳) R E ≪≫
    Functor.isoWhiskerLeft (moduleRestriction B S hS 𝒳) (@asIso _ _ _ _ adj.counit hc) ≪≫
      Functor.rightUnitor (moduleRestriction B S hS 𝒳)

end Stack.FlatFppf

end AlgebraicGeometry

end
