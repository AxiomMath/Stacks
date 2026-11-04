module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestrictionComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall

/-!
# The comparison map of restricted modules (Stacks 06WC)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, let `F` be a presheaf of
modules over the structure sheaf of Stacks 06TV, and let `φ : x ⟶ y` be an arrow of `𝒳` lying
over a morphism of schemes `a : U ⟶ V`. Stacks 06WJ restricts `F` to the small étale sites of
`U` and of `V`. Stacks 06WC compares the two restrictions: the comparison map of Stacks 06W2 is
compatible with the map `a_{small}^♯` of structure sheaves, and therefore induces a map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of `𝒪_{U_ét}`-modules.

The map `a_{small}^♯` is the comparison of Stacks 06W2 applied to the structure sheaf itself:
both restrictions of the structure sheaf of `𝒳` are identified with the structure sheaves of
the small étale sites by Stacks 06W9, and conjugating by those identifications turns the
comparison into a morphism of presheaves of rings on the small étale site of `V`.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleStructureComparison`: the map `a_{small}^♯` of structure
  sheaves below an arrow of `𝒳`.
* `AlgebraicGeometry.Stack.restrictModulePushforwardComparison`: the comparison of Stacks 06W2
  for a presheaf of modules, as a morphism of presheaves of modules over `a_{small}^♯`. This is
  the compatibility asserted by Stacks 06WC.
* `AlgebraicGeometry.Stack.restrictModulePullbackComparison`: **Stacks 06WC**, the induced map
  `c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}`.

## Main results

* `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app`: the underlying map of
  abelian presheaves of the module comparison is the comparison of Stacks 06W2.
* `AlgebraicGeometry.Stack.restrictModulePullbackComparison_adjunct`: the induced map is the
  mate of the module comparison, which characterizes it.

## Implementation notes

The comparison is built on the direct-image form of Stacks 06W2 rather than the inverse-image
form of Stacks 06W3, because the direct image of modules needs no adjoint: it is restriction of
scalars along `a_{small}^♯` composed with reindexing, and exists for a presheaf of modules with
sections in any universe. The pullback `a_{small}^*` is then its left adjoint, and the mate of
the direct-image comparison is the map of the source.

That left adjoint exists because the small étale site is essentially small in the universe of
its structure sheaf, by `AlgebraicGeometry.SmallEtale.essentiallySmall`; the sections of the
module must then lie in that same universe, which is why the pullback comparison fixes the
module universe while the direct-image comparison does not. No sheafification and no sheaf
condition on the module enter, so the statement is about presheaves of modules throughout; the
source states it for an étale sheaf only because that is the hypothesis under which it reads
the comparison in the inverse-image form.

Semilinearity of the comparison is the one piece of content. It holds because the comparison of
Stacks 06W2 is, at each small étale object, restriction of the presheaf along an arrow of `𝒳`
that depends only on the site data and not on the presheaf being restricted
(`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app`, applicable by
`AlgebraicGeometry.Stack.exists_restrictionComparisonLift`). The same arrow therefore computes
the comparison for the module and for the structure sheaf, and semilinearity of restriction
along it is part of being a presheaf of modules.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The map `a_{small}^♯ : 𝒪_{V_ét} ⟶ a_{small, *}𝒪_{U_ét}` of structure sheaves below an arrow
`φ : x ⟶ y` of `𝒳`: the comparison of Stacks 06W2 for the structure sheaf of `𝒳`, conjugated by
the identifications of Stacks 06W9 of its restrictions with the structure sheaves of the small
étale sites. -/
@[stacks 06WC "the map of structure sheaves below an arrow"]
noncomputable def smallEtaleStructureComparison {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)).obj ⟶
      (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op ⋙
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
  (localStructurePresheafIso B E h S hS p hp y τ hτ).hom ≫
    restrictionPushforwardComparison B E h S hS p hp φ
      (ringStructureSheafCore B S hS p hp τ hτ).obj ≫
    Functor.whiskerLeft (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op
      (localStructurePresheafIso B E h S hS p hp x τ hτ).inv

/-- **Stacks 06WC.** The comparison of Stacks 06W2 for a presheaf of modules on `𝒳` is a
morphism of presheaves of modules over the map `a_{small}^♯` of structure sheaves: the
restriction at `y` maps to the direct image of the restriction at `x`.

This is the compatibility of the comparison map with `a_{small}^♯` asserted by the source. -/
@[stacks 06WC "compatibility of the comparison map with the map of structure sheaves"]
noncomputable def restrictModulePushforwardComparison {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    restrictModuleToSmallEtale B E h S hS p hp y τ hτ F ⟶
      (PresheafOfModules.pushforward.{m}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F) :=
  PresheafOfModules.homMk
    (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf)
    (by
      intro W r n
      obtain ⟨φ', hfac, hbase⟩ :=
        exists_restrictionComparisonLift B E h S hS p hp φ W.unop
      have hmod : (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf).app W =
          F.presheaf.map φ'.op :=
        restrictionPushforwardComparison_app B E h S hS p hp φ F.presheaf W.unop φ' hfac hbase
      have hring : (restrictionPushforwardComparison B E h S hS p hp φ
            (ringStructureSheafCore B S hS p hp τ hτ).obj).app W =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op :=
        restrictionPushforwardComparison_app B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj W.unop φ' hfac hbase
      have hcancel := ConcreteCategory.congr_hom
        ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv_hom_id_app
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj W))
        ((restrictionPushforwardComparison B E h S hS p hp φ
            (ringStructureSheafCore B S hS p hp τ hτ).obj).app W
          ((localStructurePresheafIso B E h S hS p hp y τ hτ).hom.app W r))
      simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hcancel
      have hscalar : (localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app
            ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj W)
            ((smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app W r) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op
            ((localStructurePresheafIso B E h S hS p hp y τ hτ).hom.app W r) := by
        have happ : (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app W r =
            (localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app
              ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op.obj W)
              ((restrictionPushforwardComparison B E h S hS p hp φ
                  (ringStructureSheafCore B S hS p hp τ hτ).obj).app W
                ((localStructurePresheafIso B E h S hS p hp y τ hτ).hom.app W r)) :=
          rfl
        rw [happ, hcancel, hring]
      simp only [hmod]
      refine (PresheafOfModules.map_smul F φ'.op
        ((localStructurePresheafIso B E h S hS p hp y τ hτ).hom.app W r) n).trans ?_
      rw [← hscalar]
      rfl)

/-- The underlying map of abelian presheaves of the module comparison is the comparison of
Stacks 06W2: putting the module structure on the comparison does not change it on sections. -/
@[simp]
theorem restrictModulePushforwardComparison_app {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (W : (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))ᵒᵖ)
    (n : (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).obj W) :
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F).app W n =
      (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf).app W n :=
  rfl

section Pullback

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The small étale site of the scheme below an object of `𝒳` is locally small in the universe
of its structure sheaf, its morphisms already forming a type of that universe. -/
instance locallySmall_smallEtale (z : 𝒳) :
    LocallySmall.{u} (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z)) :=
  ⟨fun _ _ => inferInstance⟩

/-- The direct image of presheaves of modules along `a_{small}^♯` has a left adjoint, the small
étale site of the scheme below `y` being essentially small in the universe of its structure
sheaf. -/
instance isRightAdjoint_pushforward_smallEtaleStructureComparison :
    (PresheafOfModules.pushforward.{u}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)

/-- **Stacks 06WC.** The comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of `𝒪_{U_ét}`-modules below an arrow `φ : x ⟶ y` of
`𝒳` lying over a morphism of schemes `a : U ⟶ V`: the mate, under the
pullback–direct image adjunction along `a_{small}^♯`, of the comparison of Stacks 06W2 for the
presheaf of modules `F`. -/
@[stacks 06WC]
noncomputable def restrictModulePullbackComparison
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    (PresheafOfModules.pullback.{u}
        (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F) ⟶
      restrictModuleToSmallEtale B E h S hS p hp x τ hτ F :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv _ _).symm
      (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F)

/-- The comparison map of Stacks 06WC is characterized by its mate being the comparison of
Stacks 06W2 for the presheaf of modules. -/
@[stacks 06WC "the adjoint characterization"]
theorem restrictModulePullbackComparison_adjunct
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv _ _
        (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F) =
      restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F :=
  Equiv.apply_symm_apply _ _

end Pullback

end AlgebraicGeometry.Stack

end
