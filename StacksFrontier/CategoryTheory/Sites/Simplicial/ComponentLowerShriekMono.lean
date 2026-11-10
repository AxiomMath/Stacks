module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import StacksFrontier.CategoryTheory.Sites.AbelianPullbackExact.SimplicialComponent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.Sigma.LocallyZero

/-!
# Exactness of the abelian lower shriek of a component inclusion, from the sum formula

Stacks 09WG(7) says that the lower shriek of abelian sheaves along the inclusion of a simplicial
component is exact, and the source deduces it from the sum formula 09WG(6): the restriction of
`g_{n!}G` to the degree-`m` component is `⊕_{ψ : [n] → [m]} f_ψ^{-1}G`. This file proves the
monomorphism-preservation half from the sum formula, which enters as a hypothesis `Θ`: a family of
morphisms of functors indexed by the simplex maps whose induced map out of the coproduct is an
isomorphism at every presheaf.

On the way it proves two facts about sheafification on an arbitrary site: a colimit of presheaves
each of which sheafifies to zero sheafifies to zero, and a colimit of morphisms each of which
sheafifies to a monomorphism sheafifies to a monomorphism, when colimits of that shape are exact.

## Main results

* `Stacks.Sites.ComponentLowerShriek.isZero_presheafToSheaf_colimit`: a colimit of presheaves with
  vanishing sheafification has vanishing sheafification.
* `Stacks.Sites.ComponentLowerShriek.mono_presheafToSheaf_map_colimMap` and
  `Stacks.Sites.ComponentLowerShriek.mono_presheafToSheaf_map_sigmaMap`: a colimit, respectively
  a coproduct, of morphisms of presheaves which sheafify to monomorphisms sheafifies to a
  monomorphism.
* `Stacks.Sites.ComponentLowerShriek.mono_of_isIso_sq`: monomorphy transfers across a commutative
  square whose horizontal legs are isomorphisms.
* `preservesMonomorphisms_sheafPullback_componentFunctor_of_lanSum`, in the namespace
  `Stacks.Sites.ComponentLowerShriek`: Stacks 09WG(7) in case (A), from 09WG(6). Given the sum
  decomposition of the left Kan extension along the component inclusion, the pullback of abelian
  sheaves along that inclusion preserves monomorphisms.

## Implementation notes

The two general lemmas are stated for `CategoryTheory.Limits.colim` rather than for a coproduct,
so that the identification of the kernel of the colimit map with the colimit of the kernels is
`CategoryTheory.Limits.PreservesKernel.iso`. The coproduct form is the case of a discrete shape.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open Stacks.Sites.AbelianSumFormula

universe w v u

namespace Stacks.Sites.ComponentLowerShriek

section General

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (A : Type v)
  [Category.{u} A] {K : Type w} [SmallCategory K]

/-- **A colimit of locally zero presheaves is locally zero.** -/
theorem isZero_presheafToSheaf_colimit [Preadditive A] [HasWeakSheafify J A]
    (F : K ⥤ (Cᵒᵖ ⥤ A)) [HasColimit F]
    (h : ∀ j, IsZero ((presheafToSheaf J A).obj (F.obj j))) :
    IsZero ((presheafToSheaf J A).obj (colimit F)) := by
  rw [isZero_presheafToSheaf_iff]
  intro T t
  refine colimit.hom_ext fun j => ?_
  rw [comp_zero]
  exact (isZero_presheafToSheaf_iff A J (F.obj j)).mp (h j) T _

/-- **A colimit of morphisms which sheafify to monomorphisms sheafifies to a monomorphism**, when
colimits of that shape are exact on presheaves. -/
theorem mono_presheafToSheaf_map_colimMap [Abelian A] [HasSheafify J A]
    {F G : K ⥤ (Cᵒᵖ ⥤ A)} (η : F ⟶ G) [HasColimitsOfShape K (Cᵒᵖ ⥤ A)]
    [HasExactColimitsOfShape K (Cᵒᵖ ⥤ A)]
    (hη : ∀ j, Mono ((presheafToSheaf J A).map (η.app j))) :
    Mono ((presheafToSheaf J A).map (colim.map η)) := by
  have : PreservesFiniteLimits (colim (J := K) (C := Cᵒᵖ ⥤ A)) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  rw [mono_presheafToSheaf_map_iff]
  refine IsZero.of_iso ?_ ((presheafToSheaf J A).mapIso (PreservesKernel.iso colim η).symm)
  refine isZero_presheafToSheaf_colimit J A (kernel η) fun j => ?_
  have hj : (kernel η).obj j ≅ kernel (η.app j) :=
    PreservesKernel.iso ((evaluation K (Cᵒᵖ ⥤ A)).obj j) η
  refine IsZero.of_iso ?_ ((presheafToSheaf J A).mapIso hj)
  exact (mono_presheafToSheaf_map_iff A J (η.app j)).mp (hη j)

/-- **A coproduct of morphisms which sheafify to monomorphisms sheafifies to a monomorphism**, when
coproducts of that size are exact on presheaves. -/
theorem mono_presheafToSheaf_map_sigmaMap [Abelian A] [HasSheafify J A] {I : Type w}
    {P Q : I → (Cᵒᵖ ⥤ A)} [HasColimitsOfShape (Discrete I) (Cᵒᵖ ⥤ A)]
    [HasExactColimitsOfShape (Discrete I) (Cᵒᵖ ⥤ A)] (g : ∀ i, P i ⟶ Q i)
    (hg : ∀ i, Mono ((presheafToSheaf J A).map (g i))) :
    Mono ((presheafToSheaf J A).map (Limits.Sigma.map g)) :=
  mono_presheafToSheaf_map_colimMap J A
    (Discrete.natTrans (F := Discrete.functor P) (G := Discrete.functor Q)
      fun X : Discrete I => g X.as) fun j => hg j.as

/-- **Monomorphy transfers across a commutative square whose horizontal legs are isomorphisms.** -/
theorem mono_of_isIso_sq {D : Type v} [Category.{w} D] {X Y X' Y' : D} {u : X ⟶ Y} {a : X ⟶ X'}
    {b : Y ⟶ Y'} {v : X' ⟶ Y'} (hu : IsIso u) (hv : IsIso v) (ha : Mono a)
    (h : u ≫ b = a ≫ v) : Mono b := by
  rw [← mono_comp_iff_of_isIso u, h]
  infer_instance

end General

section Simplicial

variable (Cs : SimplicialSite.{u}) (n : SimplexCategory)

/-- **Stacks 09WG(7) in case (A), deduced from 09WG(6).** Let `Θ` be the sum decomposition of
Stacks 09WG(6) at the level of presheaves: for each degree `m` a morphism of functors from the
left Kan extension along the transition functor `u_ψ` to the restriction to `C_m` of the left Kan
extension along the degree-`n` component inclusion, whose induced morphism out of the coproduct
over the simplex maps `ψ : n ⟶ m` is an isomorphism at every presheaf. Then the pullback of
abelian sheaves along the component inclusion preserves monomorphisms. -/
theorem preservesMonomorphisms_sheafPullback_componentFunctor_of_lanSum
    [HasSheafify Cs.totalTopology AddCommGrpCat.{u}]
    [∀ m : SimplexCategory, HasSheafify (Cs.coverage m).toGrothendieck AddCommGrpCat.{u}]
    (Θ : ∀ (m : SimplexCategory) (ψ : n ⟶ m),
      (((Cs.underlying.map ψ).toFunctor).op.lan :
          ((Cs.underlying.obj n)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
            ((Cs.underlying.obj m)ᵒᵖ ⥤ AddCommGrpCat.{u})) ⟶
        (CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan ⋙
          (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
            (CoGrothendieck.ι Cs.totalPseudofunctor (op m)).op)
    (hΘ : ∀ (m : SimplexCategory) (P : (Cs.underlying.obj n)ᵒᵖ ⥤ AddCommGrpCat.{u}),
      IsIso (Limits.Sigma.desc fun ψ : n ⟶ m => (Θ m ψ).app P)) :
    ((SimplicialSiteSituation.componentFunctor
        (⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}) n).sheafPullback AddCommGrpCat.{u}
      ((⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      (⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}).totalTopology).PreservesMonomorphisms := by
  rw [Functor.PreservesMonomorphisms.iso_iff
    (Functor.sheafPullbackConstruction.sheafPullbackIso
      (SimplicialSiteSituation.componentFunctor
        (⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}) n) AddCommGrpCat.{u}
      ((⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      (⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}).totalTopology)]
  constructor
  intro G G' α hα
  have hαi : @Mono (Sheaf (Cs.coverage n).toGrothendieck AddCommGrpCat.{u}) _ G G' α := hα
  set h₀ := (sheafToPresheaf (Cs.coverage n).toGrothendieck AddCommGrpCat.{u}).map α with hh₀
  refine mono_presheafToSheaf_map_totalTopology_of_forall_degree AddCommGrpCat.{u}
    (⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}) _ fun m => ?_
  set L := presheafToSheaf (Cs.coverage m).toGrothendieck AddCommGrpCat.{u} with hLdef
  change Mono (L.map
    (Functor.whiskerLeft (CoGrothendieck.ι Cs.totalPseudofunctor (op m)).op
      ((CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan.map h₀)))
  have hmid : Mono (L.map
      (Limits.Sigma.map fun ψ : n ⟶ m => ((Cs.underlying.map ψ).toFunctor).op.lan.map h₀)) := by
    refine mono_presheafToSheaf_map_sigmaMap _ AddCommGrpCat.{u} _ fun ψ => ?_
    have hcont := (Cs.isMorphismOfSites ψ).isContinuous
    have hstep : (((Cs.underlying.map ψ).toFunctor).sheafPullback AddCommGrpCat.{u}
        (Cs.coverage n).toGrothendieck (Cs.coverage m).toGrothendieck).PreservesMonomorphisms :=
      Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_transition Cs ψ
    have hconstr : (Functor.sheafPullbackConstruction.sheafPullback
        ((Cs.underlying.map ψ).toFunctor) AddCommGrpCat.{u}
        (Cs.coverage n).toGrothendieck (Cs.coverage m).toGrothendieck).PreservesMonomorphisms :=
      (Functor.PreservesMonomorphisms.iso_iff
        (Functor.sheafPullbackConstruction.sheafPullbackIso
          ((Cs.underlying.map ψ).toFunctor) AddCommGrpCat.{u}
          (Cs.coverage n).toGrothendieck (Cs.coverage m).toGrothendieck)).mp hstep
    exact hconstr.preserves α
  have hsq : (Limits.Sigma.desc fun ψ : n ⟶ m => (Θ m ψ).app G.obj) ≫
        Functor.whiskerLeft (CoGrothendieck.ι Cs.totalPseudofunctor (op m)).op
          ((CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan.map h₀) =
      (Limits.Sigma.map fun ψ : n ⟶ m => ((Cs.underlying.map ψ).toFunctor).op.lan.map h₀) ≫
        (Limits.Sigma.desc fun ψ : n ⟶ m => (Θ m ψ).app G'.obj) := by
    refine Limits.Sigma.hom_ext _ _ fun ψ => ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => t ≫ Functor.whiskerLeft
      (CoGrothendieck.ι Cs.totalPseudofunctor (op m)).op
      ((CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan.map h₀))
        (Limits.Sigma.ι_comp_desc _ ψ)).trans ?_
    refine (((Θ m ψ).naturality h₀).symm).trans ?_
    refine (congrArg (fun t => ((Cs.underlying.map ψ).toFunctor).op.lan.map h₀ ≫ t)
      (Limits.Sigma.ι_comp_desc (fun ψ : n ⟶ m => (Θ m ψ).app G'.obj) ψ).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (fun t => t ≫ (Limits.Sigma.desc fun ψ : n ⟶ m => (Θ m ψ).app G'.obj))
      (Limits.Sigma.ι_map
        (fun ψ : n ⟶ m => ((Cs.underlying.map ψ).toFunctor).op.lan.map h₀) ψ).symm).trans
      (Category.assoc _ _ _)
  have hiD : ∀ P, IsIso (L.map (Limits.Sigma.desc fun ψ : n ⟶ m => (Θ m ψ).app P)) := fun P =>
    inferInstanceAs (IsIso (L.mapIso (@asIso _ _ _ _ _ (hΘ m P))).hom)
  refine mono_of_isIso_sq (hiD _) (hiD _) hmid ?_
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg (fun t => L.map t) hsq).trans (Functor.map_comp _ _ _))

end Simplicial

end Stacks.Sites.ComponentLowerShriek

end
