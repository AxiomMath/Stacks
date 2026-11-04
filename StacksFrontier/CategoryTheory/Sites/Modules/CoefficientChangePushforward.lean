module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos

/-!
# The direct image of sheaves of modules for a change of coefficients on a fixed site

Fix a site `(C, J)` and two sheaves of commutative rings `O`, `O'` on it. A morphism of ringed
topoi `(Sh(J), O') ⟶ (Sh(J), O)` whose underlying geometric morphism is the identity of `Sh(J)`
is a change of coefficients, and its direct image of sheaves of modules is restriction of
scalars along the structure map. This file identifies the *topos-level* direct image
`AlgebraicGeometry.RingedToposHom.pushforwardModules`, which transports the module structure
along the geometric morphism, with Mathlib's `SheafOfModules.pushforward` along the identity
functor of the site, which restricts scalars.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.ofIdentityTopos`: the morphism of ringed topoi on a fixed
  site with the identity geometric morphism and a given structure map.
* `AlgebraicGeometry.RingedToposHom.coefficientMapOfIdentityTopos`: its structure map, read as a
  map `O ⟶ O'` of the two structure sheaves.

## Main results

* `AlgebraicGeometry.RingedToposHom.pushforwardModulesOfIdentityToposIso`: the two direct images
  of sheaves of modules agree.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

universe w v u

namespace AlgebraicGeometry.RingedToposHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O O' : Sheaf J CommRingCat.{w}}

/-- The change of coefficient rings on a fixed site: the morphism of ringed topoi
`(Sh(J), O') ⟶ (Sh(J), O)` whose underlying geometric morphism is the identity of `Sh(J)` and
whose structure map is `φ`. -/
def ofIdentityTopos
    (φ : O ⟶ (pushforwardCommRingFunctor (MorphismOfTopoi.id (Sheaf J (Type w)))).obj O') :
    RingedToposHom (⟨C, J, O'⟩ : RingedTopos.{v, u, w})
      (⟨C, J, O⟩ : RingedTopos.{v, u, w}) where
  toToposHom := MorphismOfTopoi.id _
  fSharp := φ

/-- The structure map of a change of coefficient rings, read as a map `O ⟶ O'` of the two
structure sheaves: `φ` followed by `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`. -/
abbrev coefficientMapOfIdentityTopos
    (φ : O ⟶ (pushforwardCommRingFunctor (MorphismOfTopoi.id (Sheaf J (Type w)))).obj O') :
    O ⟶ O' :=
  φ ≫ (restrictionCommRingIso J J (𝟭 C) O').hom

/-- The sections over `Z` of the direct image of a sheaf of sets along the identity morphism of
topoi are the sections over `Z`: the identity transformation. -/
def sectionsComparisonOfIdentityTopos (Z : Cᵒᵖ) :
    ((MorphismOfTopoi.id (Sheaf J (Type w))).pushforward ⋙ Sheaf.sectionsFunctor J Z) ⟶
      Sheaf.sectionsFunctor J Z where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- The two direct images of a sheaf of modules along a change of coefficient rings agree: the
underlying sheaf of abelian groups is the module itself on both sides and the comparison is the
identity there. -/
def pushforwardModulesObjOfIdentityToposIso
    (φ : O ⟶ (pushforwardCommRingFunctor (MorphismOfTopoi.id (Sheaf J (Type w)))).obj O')
    (F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O')) :
    (ofIdentityTopos φ).pushforwardModules.obj F ≅
      (RingedToposSiteHom.coefficientChange J
        (coefficientMapOfIdentityTopos φ)).pushforwardTopos.obj F :=
  isoOfSheafIso (Iso.refl _)
    ((moduleAddHom_comp_iff _).mpr
      (fun Z x y ↦ Sheaf.app_moduleAddObj _ F (sectionsComparisonOfIdentityTopos (J := J) Z) x y))
    ((moduleSMulHom_comp_iff _).mpr
      (fun Z _ x ↦ Sheaf.app_moduleSMulObj _ F (sectionsComparisonOfIdentityTopos (J := J) Z) _ x))

/-- The direct image of sheaves of modules along a morphism of ringed topoi whose geometric
morphism is the identity of `Sh(J)` is restriction of scalars along its structure map. -/
def pushforwardModulesOfIdentityToposIso
    (φ : O ⟶ (pushforwardCommRingFunctor (MorphismOfTopoi.id (Sheaf J (Type w)))).obj O') :
    (ofIdentityTopos φ).pushforwardModules ≅
      (RingedToposSiteHom.coefficientChange J
        (coefficientMapOfIdentityTopos φ)).pushforwardTopos :=
  NatIso.ofComponents (fun F ↦ pushforwardModulesObjOfIdentityToposIso φ F)
    fun _ ↦ hom_ext_moduleSheafFunctor rfl

end AlgebraicGeometry.RingedToposHom

end
