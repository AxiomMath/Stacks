module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiComponentConservative
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSystemPair

/-!
# Cartesian modules on the total Zariski site are pairs with a cocycle isomorphism

Let `X` be a simplicial scheme. A cartesian sheaf of `𝒪_X`-modules `F` on the total Zariski site
of `X` determines a pair: the module `F_0` on `X_0` with the isomorphism
`(d¹_1)^* F_0 ≅ F_1 ≅ (d¹_0)^* F_0` of its two transitions to degree one, which satisfies the
cocycle condition on `X_2`. This file proves that this is an equivalence between cartesian
modules and pairs, which is Stacks 07TH for the total Zariski site of a simplicial scheme, and
that under it the quasi-coherent modules on the total Zariski site correspond to the pairs whose
module is quasi-coherent (Stacks 0D7M).

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.homOfFamily`: the morphism of modules on the total Zariski
  site assembled from a family of morphisms of the components compatible with the transitions.
* `AlgebraicGeometry.SimplicialScheme.CartesianZariskiModule`: the cartesian modules.
* `AlgebraicGeometry.SimplicialScheme.zariskiPairFunctor`: the functor to pairs.
* `AlgebraicGeometry.SimplicialScheme.quasicoherentEquivQuasicoherentPair`: the quasi-coherent
  modules on `X_Zar` are the pairs `(F, α)` with `F` quasi-coherent.

## Main results

* `AlgebraicGeometry.SimplicialScheme.zariskiPairFunctor_isEquivalence`: **Stacks 07TH for the
  total Zariski site.**

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial
open scoped Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {X : SimplicialObject Scheme.{u}}

/-! ### Morphisms of modules from their components -/

/-- A morphism of modules on the total Zariski site is determined by its components. -/
theorem hom_ext_of_componentModule {F G : Modules X} {f g : F ⟶ G}
    (h : ∀ n : SimplexCategoryᵒᵖ, (componentModule X n).map f = (componentModule X n).map g) :
    f = g := by
  apply (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map_injective
  refine NatTrans.ext (funext fun U => ?_)
  exact (componentModule_forget_app U.unop.degree f U.unop.toOpens).symm.trans
    ((congrArg (fun t => ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      t).app (op U.unop.toOpens)) (h U.unop.degree)).trans
        (componentModule_forget_app U.unop.degree g U.unop.toOpens))

section HomOfFamily

variable {F G : Modules X}
  (β : ∀ n : SimplexCategory, (componentModule X (op n)).obj F ⟶ (componentModule X (op n)).obj G)
  (hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (Scheme.Modules.pullback (X.map φ.op)).map (β m) ≫ componentModuleTransition X φ.op G =
      componentModuleTransition X φ.op F ≫ β n)

include hβ in
/-- A family of morphisms of the components compatible with the transitions is compatible with
the direct transitions. -/
theorem componentModuleDirectTransition_comp_of_family {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentModuleDirectTransition X φ.op).app F ≫
        (Scheme.Modules.pushforward (X.map φ.op)).map (β n) =
      β m ≫ (componentModuleDirectTransition X φ.op).app G := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ.op)).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm]
  exact (hβ φ).symm

include hβ in
/-- The compatibility of a family with the direct transitions, on sections. -/
theorem presheaf_map_transitionHom_comp_of_family {m n : SimplexCategory} (φ : m ⟶ n)
    (W : Opens ((zariskiSpace X).obj (op m))) :
    F.val.presheaf.map (SimplicialSheafSystem.transitionHom φ.op W).op ≫
        (β n).app ((Opens.map ((zariskiSpace X).map φ.op)).obj W) =
      (β m).app W ≫ G.val.presheaf.map (SimplicialSheafSystem.transitionHom φ.op W).op :=
  congrArg (fun t => Scheme.Modules.Hom.app t W)
    (componentModuleDirectTransition_comp_of_family β hβ φ)

include hβ in
/-- The morphism of underlying presheaves of abelian groups assembled from a compatible family of
morphisms of the components. -/
noncomputable def homOfFamilyPresheaf : F.val.presheaf ⟶ G.val.presheaf where
  app U := (β U.unop.degree.unop).app U.unop.toOpens
  naturality U V f := by
    let ψ := f.unop.base
    let pre : Opens ((zariskiSpace X).obj V.unop.degree) :=
      (Opens.map ((zariskiSpace X).map ψ)).obj U.unop.toOpens
    let mid : ZariskiOpen X := ⟨V.unop.degree, pre⟩
    let i : V.unop.toOpens ⟶ pre := homOfLE (SimplicialOpen.Hom.le f.unop)
    let a : V.unop ⟶ mid := (levelFunctor (zariskiSpace X) V.unop.degree).map i
    let b : mid ⟶ U.unop := SimplicialSheafSystem.transitionHom ψ U.unop.toOpens
    have hf : f = b.op ≫ a.op := Quiver.Hom.unop_inj (by
      apply SimplicialOpen.Hom.ext
      exact (Category.id_comp _).symm)
    have hF : F.val.presheaf.map f = F.val.presheaf.map b.op ≫ F.val.presheaf.map a.op :=
      (congrArg (fun k => F.val.presheaf.map k) hf).trans (F.val.presheaf.map_comp _ _)
    have hG : G.val.presheaf.map f = G.val.presheaf.map b.op ≫ G.val.presheaf.map a.op :=
      (congrArg (fun k => G.val.presheaf.map k) hf).trans (G.val.presheaf.map_comp _ _)
    have hlev : F.val.presheaf.map a.op ≫ (β V.unop.degree.unop).app V.unop.toOpens =
        (β V.unop.degree.unop).app pre ≫ G.val.presheaf.map a.op :=
      (β V.unop.degree.unop).mapPresheaf.naturality i.op
    have htr := presheaf_map_transitionHom_comp_of_family β hβ ψ.unop U.unop.toOpens
    exact (congrArg (fun t => t ≫ (β V.unop.degree.unop).app V.unop.toOpens) hF).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => F.val.presheaf.map b.op ≫ t) hlev).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun t => t ≫ G.val.presheaf.map a.op) htr).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun t => (β U.unop.degree.unop).app U.unop.toOpens ≫ t) hG.symm))))))

include hβ in
/-- **The morphism assembled from a compatible family of morphisms of the components.** -/
noncomputable def homOfFamily : F ⟶ G where
  val := PresheafOfModules.homMk (homOfFamilyPresheaf β hβ)
    (fun U r x => Scheme.Modules.Hom.app_smul (β U.unop.degree.unop) (U := U.unop.toOpens) r x)

include hβ in
/-- The components of the morphism assembled from a family are the members of the family. -/
theorem componentModule_map_homOfFamily (n : SimplexCategory) :
    (componentModule X (op n)).map (homOfFamily β hβ) = β n :=
  Scheme.Modules.hom_ext _ _ fun _ => rfl

end HomOfFamily

/-! ### The functor to pairs -/

/-- The cartesian sheaves of `𝒪_X`-modules on the total Zariski site of a simplicial scheme. -/
abbrev CartesianZariskiModule (X : SimplicialObject Scheme.{u}) :=
  ObjectProperty.FullSubcategory (IsCartesianModule X)

/-- The transitions of the cartesian systems of two cartesian modules are compatible with the
components of a morphism. -/
theorem cartesianModuleSystem_naturality {M M' : CartesianZariskiModule X} (f : M ⟶ M')
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((zariskiModuleFamily X).map φ).map ((componentModule X (op m)).map f.hom) ≫
        ((cartesianModuleSystem X M'.obj M'.property).trans φ).hom =
      ((cartesianModuleSystem X M.obj M.property).trans φ).hom ≫
        (componentModule X (op n)).map f.hom :=
  componentModuleTransition_naturality φ.op f.hom

variable (X) in
/-- **The functor from cartesian modules to pairs**: a cartesian module goes to its component in
degree zero with the comparison isomorphism of its two transitions to degree one. -/
noncomputable def zariskiPairFunctor : CartesianZariskiModule X ⥤ (zariskiModuleFamily X).Pair where
  obj M := (cartesianModuleSystem X M.obj M.property).toPair
  map f := SimplicialPseudoFamily.CartesianSystem.toPairHom
    (fun n => (componentModule X (op n)).map f.hom) (fun φ => cartesianModuleSystem_naturality f φ)
  map_id M := SimplicialPseudoFamily.Pair.hom_ext ((componentModule X (op ⦋0⦌)).map_id M.obj)
  map_comp f g := SimplicialPseudoFamily.Pair.hom_ext
    ((componentModule X (op ⦋0⦌)).map_comp f.hom g.hom)

/-- The functor to pairs is faithful: a morphism of cartesian modules is determined by its
component in degree zero. -/
instance zariskiPairFunctor_faithful : (zariskiPairFunctor X).Faithful where
  map_injective {M M'} f g h := by
    have h0 : (componentModule X (op ⦋0⦌)).map f.hom = (componentModule X (op ⦋0⦌)).map g.hom :=
      congrArg SimplicialPseudoFamily.Pair.Hom.map h
    apply ObjectProperty.hom_ext
    apply hom_ext_of_componentModule
    intro n
    let μ : ⦋0⦌ ⟶ n.unop := SimplexCategory.const ⦋0⦌ n.unop 0
    have hf := cartesianModuleSystem_naturality f μ
    have hg := cartesianModuleSystem_naturality g μ
    rw [h0] at hf
    exact (cancel_epi ((cartesianModuleSystem X M.obj M.property).trans μ).hom).mp
      (hf.symm.trans hg)

/-- The functor to pairs is full: a morphism in degree zero compatible with the comparison
isomorphisms extends to the components by Stacks 0D7I's argument, and the extended family
assembles into a morphism of modules on the total Zariski site. -/
instance zariskiPairFunctor_full : (zariskiPairFunctor X).Full where
  map_surjective {M M'} f := by
    let N := cartesianModuleSystem X M.obj M.property
    let N' := cartesianModuleSystem X M'.obj M'.property
    have hh : SimplicialPseudoFamily.CartesianSystem.IsCompatible N N' f.map :=
      SimplicialPseudoFamily.CartesianSystem.isCompatible_of_comm f.comm
    let β := SimplicialPseudoFamily.CartesianSystem.homFamily (N := N) (N' := N') (h := f.map)
    have hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        (Scheme.Modules.pullback (X.map φ.op)).map (β m) ≫
            componentModuleTransition X φ.op M'.obj =
          componentModuleTransition X φ.op M.obj ≫ β n := fun φ =>
      SimplicialPseudoFamily.CartesianSystem.homFamily_naturality hh φ
    exact ⟨ObjectProperty.homMk (homOfFamily β hβ), SimplicialPseudoFamily.Pair.hom_ext
      ((componentModule_map_homOfFamily β hβ ⦋0⦌).trans
        SimplicialPseudoFamily.CartesianSystem.homFamily_zero)⟩

/-- **Stacks 07TH for the total Zariski site**, essential surjectivity: every pair is the pair of
the cartesian module glued from its cartesian system. -/
instance zariskiPairFunctor_essSurj : (zariskiPairFunctor X).EssSurj where
  mem_essImage A :=
    ⟨⟨systemModule ((zariskiModuleFamily X).pairSystem A.obj A.iso A.cocycle),
      isCartesianModule_systemModule _⟩, ⟨systemModulePairIso A⟩⟩

/-- **Stacks 07TH for the total Zariski site of a simplicial scheme.** The functor from cartesian
sheaves of `𝒪_X`-modules on `X_Zar` to pairs `(ℱ, α)` of a module `ℱ` on `X_0` and an
isomorphism `α : (d¹_1)^* ℱ ≅ (d¹_0)^* ℱ` satisfying the cocycle condition on `X_2` is an
equivalence of categories. -/
instance zariskiPairFunctor_isEquivalence : (zariskiPairFunctor X).IsEquivalence := { }

end AlgebraicGeometry.SimplicialScheme

end
