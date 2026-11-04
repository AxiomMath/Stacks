module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposCoefficientChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientChangePushforward

/-!
# Modules along the change of coefficient rings of a ringed topos

Let `α : O ⟶ O'` be a map of sheaves of commutative rings on a site `(C, J)`, and let
`AlgebraicGeometry.RingedToposHom.coefficientMorphism J α : (Sh(J), O') ⟶ (Sh(J), O)` be the
morphism of ringed topoi it presents: the identity geometric morphism with structure map `α`.
This file identifies its direct image of sheaves of modules with restriction of scalars along
`α` and its pullback of sheaves of modules with extension of scalars `O' ⊗_O -` along `α`, at
independent object, morphism and section universes.

## Main results

* `AlgebraicGeometry.RingedToposHom.coefficientMapOfIdentityTopos_coefficientMorphism`: the
  structure map of `coefficientMorphism J α`, read as a map `O ⟶ O'`, is `α`.
* `AlgebraicGeometry.RingedToposHom.pushforwardModulesCoefficientMorphismIso`: the direct image
  of sheaves of modules along `coefficientMorphism J α` is restriction of scalars along `α`.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesCoefficientMorphismIso`: the pullback of
  sheaves of modules along `coefficientMorphism J α` is extension of scalars along `α`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedToposHom

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget CommRingCat.{w})]
  {O O' : Sheaf J CommRingCat.{w}} (α : O ⟶ O')

omit [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The structure map of the change of coefficient rings along `α`, read as a map `O ⟶ O'` of
the two structure sheaves, is `α`: on underlying sheaves of sets both comparisons involved are
identities. -/
lemma coefficientMapOfIdentityTopos_coefficientMorphism :
    coefficientMapOfIdentityTopos (coefficientMorphism J α).fSharp = α := by
  have h : (sheafCompose J (forget CommRingCat.{w})).map
      (coefficientMapOfIdentityTopos (coefficientMorphism J α).fSharp) =
      (sheafCompose J (forget CommRingCat.{w})).map α := by
    refine ((sheafCompose J (forget CommRingCat.{w})).map_comp (coefficientMorphism J α).fSharp
      (Stacks.Sheaves.ToposPullback.restrictionCommRingIso J J (𝟭 C) O').hom).trans
      ((congrArg (fun m => (sheafCompose J (forget CommRingCat.{w})).map
          (coefficientMorphism J α).fSharp ≫ m)
        (Stacks.Sheaves.ToposPullback.restrictionCommRingIso_hom_forget J J (𝟭 C) O')).trans
      ((Category.comp_id _).trans
      ((Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv _ _ _
        _).trans ?_)))
    refine (congrArg (fun m => (MorphismOfTopoi.id (Sheaf J (Type w))).adj.homEquiv _ _ m)
      (((sheafCompose J (forget CommRingCat.{w})).map_comp _ α).trans
        ((congrArg (· ≫ _)
          (Stacks.Sheaves.ToposPullback.forget_map_pullbackCommRingSheafFunctorId_hom_app
            J O)).trans
          (Category.id_comp _)))).trans ?_
    exact (Adjunction.homEquiv_unit _ _ _ _).trans (Category.id_comp _)
  refine Sheaf.hom_ext ?_
  ext U x
  exact congrFun (congrArg (fun φ => φ.hom.app U) h) x

/-- **The direct image of sheaves of modules along a change of coefficient rings is
restriction of scalars.** This is
`AlgebraicGeometry.RingedToposHom.pushforwardModulesOfIdentityToposIso` read through
`coefficientMapOfIdentityTopos_coefficientMorphism`. -/
def pushforwardModulesCoefficientMorphismIso :
    (coefficientMorphism J α).pushforwardModules ≅
      SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α) :=
  pushforwardModulesOfIdentityToposIso (coefficientMorphism J α).fSharp ≪≫
    eqToIso (congrArg
      (fun β : O ⟶ O' => (RingedToposSiteHom.coefficientChange J β).pushforwardTopos)
      (coefficientMapOfIdentityTopos_coefficientMorphism J α))

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The pullback of sheaves of modules along a change of coefficient rings is extension of
scalars**, `O' ⊗_O -` sheafified: both are left adjoint to restriction of scalars along `α`, by
Stacks 03D7 and `pushforwardModulesCoefficientMorphismIso` on one side and by Stacks 03CZ on the
other. -/
def pullbackModulesCoefficientMorphismIso :
    (coefficientMorphism J α).toModulesHom.pullbackModules ≅
      Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
        (Stacks.SheafOfModules.Tensor.ringSheaf O).property
        (Stacks.SheafOfModules.Tensor.ringSheaf O').property :=
  Adjunction.leftAdjointUniq
    ((pullbackAdjPushforwardModules (coefficientMorphism J α)).ofNatIsoRight
      (pushforwardModulesCoefficientMorphismIso J α))
    (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction J α.hom
      (Stacks.SheafOfModules.Tensor.ringSheaf O).property
      (Stacks.SheafOfModules.Tensor.ringSheaf O').property)

end AlgebraicGeometry.RingedToposHom

end
