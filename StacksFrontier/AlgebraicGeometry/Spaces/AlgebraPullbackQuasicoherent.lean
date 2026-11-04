module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackUnderlyingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the pullback of an algebra sheaf on an algebraic space

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `A` be a sheaf of commutative `𝒪_X`-algebras on the small étale site of `X`.
This file proves that the `𝒪_Y`-module underlying the pullback algebra
`g^*A = 𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A` is the pullback `g^*` of the `𝒪_X`-module underlying `A`, and
deduces that `g^*A` is quasi-coherent whenever `A` is.

## Main results

* `AlgebraicGeometry.Space.ringSheafMap_ringSheafPullback_map`: **the sheaf-of-rings map
  underlying the inverse image of a morphism of sheaves of commutative rings is the inverse
  image of the underlying map.**
* `AlgebraicGeometry.Space.underlyingModule_inverseImageAlgebra`: **the module underlying
  `g⁻¹A` is the inverse image of the module underlying `A`**, up to the interchange of the
  inverse image with restriction of scalars.
* `AlgebraicGeometry.Space.algebraPullback_isQuasicoherent`: **the pullback of a
  quasi-coherent algebra sheaf is quasi-coherent.**  This is the field of the same name of
  `AlgebraicGeometry.Space.BaseChangeCompatibility`.

## Implementation notes

`AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackIso` identifies the module underlying
`g^*A` with the extension of scalars along `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` of the module underlying
`g⁻¹A`, and `AlgebraicGeometry.Space.modulePullback` is by definition that same extension of
scalars applied to an inverse image of modules.  What remains is therefore the inverse-image
half, and all of it is definitional except for one comparison on morphisms.

`Stacks.FlatChangeOfRings.ringSheafMap ((ringSheafPullback B S hS g).map a)` forgets
commutativity *after* taking the inverse image, so it is
`CategoryTheory.sheafCompose _ (forget₂ CommRingCat RingCat)` applied to a morphism built by
`CategoryTheory.Functor.FullyFaithful.preimage`;
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMap _ Φ
(Stacks.FlatChangeOfRings.ringSheafMap a)` forgets commutativity *first* and transports the
ring operations with `CategoryTheory.Sheaf.ringObjMap`.  The two are not definitionally equal,
and `ringSheafMap_ringSheafPullback_map` below is the identification; it is
`Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap` read at the
small étale site, whose proof is `CategoryTheory.Functor.FullyFaithful.map_preimage` for
`Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf`.  Transporting
`Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMap` along the faithfulness of
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)` would reach the same statement
one step further on, past forgetting the ring operations as well.

Every other link is `rfl`.  `AlgebraicGeometry.Space.modulePullback` unfolds to
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` followed by
`Stacks.FlatChangeOfRings.extendScalars` along
`AlgebraicGeometry.Space.structurePullbackMap`; the inverse image of the free module of rank
one is the free module of rank one over the inverse-image ring sheaf
(`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso` is `Iso.refl`); and the module
underlying an algebra sheaf is a restriction of scalars by
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_eq_restrictScalars`.  The one genuine
isomorphism is
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`, the interchange of
the inverse image with restriction of scalars, which is the identity on underlying sheaves of
sets but not on the module structures.

Quasi-coherence then transports along that isomorphism, by
`SheafOfModules.IsQuasicoherentOnSite.of_iso`, from
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`,
Stacks 03GA at an arbitrary morphism of algebraic spaces and an arbitrary quasi-coherent
module.  No quasi-coherence statement for extension of scalars is needed, and none is
available: the composite is recognised as `AlgebraicGeometry.Space.modulePullback` before
quasi-coherence is invoked.

## References

* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The sheaf of rings underlying the inverse image of a morphism of sheaves of commutative
rings is the inverse image of the underlying morphism of sheaves of rings.**

The two sides are not definitionally equal: the left-hand side forgets commutativity after
taking the inverse image, the right-hand side transports the ring operations of the already
noncommutative inverse image.  They agree because forgetting commutativity is fully faithful
on sheaves, which is how the inverse image of a morphism of sheaves of *commutative* rings is
built in the first place. -/
theorem ringSheafMap_ringSheafPullback_map (g : Y ⟶ X)
    {R R' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (a : R ⟶ R') :
    Stacks.FlatChangeOfRings.ringSheafMap ((ringSheafPullback B S hS g).map a) =
      Stacks.Sheaves.ToposPullback.pullbackRingSheafMap
        (SmallEtale.topology B S hS Y.1)
        ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
        (Stacks.FlatChangeOfRings.ringSheafMap (O₁ := R) (O₂ := R') a) :=
  Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap
    (SmallEtale.topology B S hS Y.1)
    ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage a

/-- **The module underlying `g⁻¹A` is the inverse image of the free module of rank one over
`g⁻¹A`, with its scalars restricted along the inverse image of the structure map of `A`.**

This is the spelling of `Stacks.SheafOfModules.AlgebraPushout.underlyingModule_anySite` at
`AlgebraicGeometry.Space.inverseImageAlgebra` in which
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso` applies; the content
is `AlgebraicGeometry.Space.ringSheafMap_ringSheafPullback_map`, the rest being definitional. -/
theorem underlyingModule_inverseImageAlgebra (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    Stacks.SheafOfModules.AlgebraPushout.underlyingModule_anySite.{u, u + 1, u}
        (inverseImageAlgebra B S hS g A) =
      (SheafOfModules.restrictScalars
          (Stacks.Sheaves.ToposPullback.pullbackRingSheafMap
            (SmallEtale.topology B S hS Y.1)
            ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
            (Stacks.FlatChangeOfRings.ringSheafMap
              (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom))).obj
        (Stacks.Sheaves.ToposPullback.pullbackModuleObj
          (SmallEtale.topology B S hS Y.1)
          ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf A.right)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))) :=
  congrArg
    (fun m => (SheafOfModules.restrictScalars m).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringSheafPullback B S hS g).obj A.right))))
    (ringSheafMap_ringSheafPullback_map B S hS g A.hom)

/-- **The module underlying the pullback algebra `g^*A` is the pullback of the module
underlying `A`.**

Composing `AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackIso`, which is the
extension-of-scalars half, with the interchange of the inverse image and restriction of
scalars, which is the inverse-image half. -/
def underlyingModuleAlgebraPullbackModulePullbackIso (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS g).obj A.underlyingModule ≅
      ((algebraPullback B S hS g).obj A).underlyingModule :=
  (Stacks.FlatChangeOfRings.extendScalars (structurePullbackMap B S hS g)).mapIso
      ((Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso
        (SmallEtale.topology B S hS Y.1)
        ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
        (Stacks.FlatChangeOfRings.ringSheafMap
          (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))).symm) ≪≫
    eqToIso (congrArg (Stacks.FlatChangeOfRings.extendScalars
        (structurePullbackMap B S hS g)).obj
      (underlyingModule_inverseImageAlgebra B S hS g A).symm) ≪≫
    (underlyingModuleAlgebraPullbackIso B S hS g A).symm

/-- **The pullback of a quasi-coherent algebra sheaf along a morphism of algebraic spaces is
quasi-coherent.**

This is the `algebraPullback_isQuasicoherent` field of
`AlgebraicGeometry.Space.BaseChangeCompatibility`, at
`AlgebraicGeometry.Space.algebraPullback`. -/
@[stacks 081V "the algebraPullback_isQuasicoherent clause"]
theorem algebraPullback_isQuasicoherent (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent) :
    ((algebraPullback B S hS g).obj A).IsQuasicoherent :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g
      A.underlyingModule hA)

end AlgebraicGeometry.Space

end
