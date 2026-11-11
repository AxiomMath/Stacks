module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.ClassRestrictionToAnObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# First cohomology along a continuous functor of sites

Let `G : C ⥤ D` be a continuous functor of sites whose restriction functor
`G^s : Sh(D) ⥤ Sh(C)` on abelian sheaves is exact. For an abelian sheaf `F` on `D` and an
object `U` of `C` there is a comparison map

`H¹(G U, F) ⟶ H¹(U, G^s F)`,

which applies the exact functor `G^s` to an `Ext`-class out of the free abelian sheaf `ℤ[G U]`
and precomposes with the map `ℤ[U] ⟶ G^s ℤ[G U]` given by the generator of `ℤ[G U]` over
`G U`. This file proves that the comparison is natural in `U` and injective.

## Main definitions

* `Stacks.Cohomology.ContinuousRestriction.restrictH1`: the comparison map.

## Main results

* `Stacks.Cohomology.ContinuousRestriction.restrictH1_naturality`: the comparison commutes with
  the restriction maps of the two cohomology presheaves.
* `Stacks.Cohomology.ContinuousRestriction.restrictH1_injective`: the comparison is injective.

## Implementation notes

Injectivity is proved with extensions rather than with injective resolutions: a class in
`H¹(G U, F)` is the class of a short exact sequence `0 → F → E → ℤ[G U] → 0`, its image vanishes
exactly when the generator of `ℤ[G U]` over `G U` lifts to a section of `E` over `G U`, and such a
section splits the sequence. No adjoint of `G^s` and no injective object is needed, which is
what makes the statement available for big sites whose objects are larger than their
morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w w' v u₁ u₂

namespace Stacks.Cohomology.ContinuousRestriction

open OverObjectCohomology

section Free

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- The generator of the free abelian sheaf on `U` over `U`. -/
public def generator (U : C) : (freeYonedaSheaf J U).obj.obj (op U) :=
  freeYonedaSheafHomEquiv J U _ (𝟙 _)

/-- The map of free abelian sheaves induced by a morphism of the site. -/
public abbrev freeMap {U V : C} (g : V ⟶ U) : freeYonedaSheaf J V ⟶ freeYonedaSheaf J U :=
  (presheafToSheaf J AddCommGrpCat.{v}).map
    (Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free)

/-- The corepresentation of sections is natural in the object: precomposing with the map
of free abelian sheaves induced by `g` restricts the section along `g`. -/
public lemma freeYonedaSheafHomEquiv_precomp {U V : C} (g : V ⟶ U)
    (F : Sheaf J AddCommGrpCat.{v})
    (h : freeYonedaSheaf J U ⟶ F) :
    freeYonedaSheafHomEquiv J V F (freeMap J g ≫ h) =
      F.obj.map g.op (freeYonedaSheafHomEquiv J U F h) := by
  dsimp only [freeYonedaSheafHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  have := (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left (yoneda.map g)
    ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F h)
  exact (congrArg yonedaEquiv this).trans (yonedaEquiv_naturality' _ g.op).symm

/-- The generator over `V` is sent by `ℤ[g]` to the restriction along `g` of the generator
over `U`. -/
public lemma freeMap_generator {U V : C} (g : V ⟶ U) :
    freeYonedaSheafHomEquiv J V _ (freeMap J g) = (freeYonedaSheaf J U).obj.map g.op
      (generator J U) := by
  rw [generator, ← freeYonedaSheafHomEquiv_precomp, Category.comp_id]

end Free

section Restriction

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]

/-- Restriction of abelian sheaves along `G`. -/
public abbrev restriction : Sheaf K AddCommGrpCat.{v} ⥤ Sheaf J AddCommGrpCat.{v} :=
  G.sheafPushforwardContinuous AddCommGrpCat.{v} J K

/-- The morphism `ℤ[U] ⟶ G^s ℤ[G U]` given by the generator of `ℤ[G U]` over `G U`. -/
public def unitMap (U : C) :
    freeYonedaSheaf J U ⟶ (restriction J K G).obj (freeYonedaSheaf K (G.obj U)) :=
  (freeYonedaSheafHomEquiv J U _).symm (generator K (G.obj U))

/-- The section of `G^s ℤ[G U]` over `U` defining `unitMap` is the generator. -/
public lemma freeYonedaSheafHomEquiv_unitMap (U : C) :
    freeYonedaSheafHomEquiv J U _ (unitMap J K G U) = generator K (G.obj U) :=
  Equiv.apply_symm_apply _ _

/-- `unitMap` is natural in the object of `C`. -/
public lemma freeMap_comp_unitMap {U V : C} (g : V ⟶ U) :
    freeMap J g ≫ unitMap J K G U =
      unitMap J K G V ≫ (restriction J K G).map (freeMap K (G.map g)) := by
  apply (freeYonedaSheafHomEquiv J V _).injective
  rw [freeYonedaSheafHomEquiv_precomp, freeYonedaSheafHomEquiv_comp,
    freeYonedaSheafHomEquiv_unitMap, freeYonedaSheafHomEquiv_unitMap]
  exact (freeMap_generator K (G.map g)).symm

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  [(restriction J K G).Additive] [PreservesFiniteLimits (restriction J K G)]
  [PreservesFiniteColimits (restriction J K G)]

/-- The comparison `H¹(G U, F) ⟶ H¹(U, G^s F)`, written on `Ext`-groups. -/
public def restrictH1 (F : Sheaf K AddCommGrpCat.{v}) (U : C) :
    Ext.{w'} (freeYonedaSheaf K (G.obj U)) F 1 →+
      Ext.{w} (freeYonedaSheaf J U) ((restriction J K G).obj F) 1 where
  toFun x := (Ext.mk₀ (unitMap J K G U)).comp (x.mapExactFunctor (restriction J K G)) (zero_add 1)
  map_zero' := by
    rw [Ext.mapExactFunctor_zero, Ext.comp_zero]
  map_add' x y := by
    rw [Ext.mapExactFunctor_add, Ext.comp_add]

/-- The defining formula of `restrictH1`. -/
public lemma restrictH1_apply (F : Sheaf K AddCommGrpCat.{v}) (U : C)
    (x : Ext.{w'} (freeYonedaSheaf K (G.obj U)) F 1) :
    restrictH1 J K G F U x =
      (Ext.mk₀ (unitMap J K G U)).comp (x.mapExactFunctor (restriction J K G)) (zero_add 1) :=
  rfl

/-- **Naturality of the comparison.** For `g : V ⟶ U`, comparing after restricting along
`G g` is restricting along `g` after comparing. -/
public lemma restrictH1_naturality (F : Sheaf K AddCommGrpCat.{v}) {U V : C} (g : V ⟶ U)
    (x : Ext.{w'} (freeYonedaSheaf K (G.obj U)) F 1) :
    restrictH1 J K G F V ((F.cohomologyPresheaf 1).map (G.map g).op x) =
      (((restriction J K G).obj F).cohomologyPresheaf 1).map g.op (restrictH1 J K G F U x) := by
  have h₁ := Torsors.cohomologyPresheaf_map_apply F (G.map g) x
  have h₂ := Torsors.cohomologyPresheaf_map_apply ((restriction J K G).obj F) g
    (restrictH1 J K G F U x)
  refine (congrArg (restrictH1 J K G F V) h₁).trans (Eq.trans ?_ h₂.symm)
  rw [restrictH1_apply, restrictH1_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc]
  exact congrArg (fun a => (Ext.mk₀ a).comp _ (zero_add 1)) (freeMap_comp_unitMap J K G g).symm

/-- **The comparison is injective.** If the image of the class of an extension
`0 → F → E → ℤ[G U] → 0` vanishes, the generator of `ℤ[G U]` over `G U` lifts to a section of
`E` over `G U`, which splits the extension. -/
public theorem restrictH1_injective (F : Sheaf K AddCommGrpCat.{v}) (U : C) :
    Function.Injective (restrictH1 J K G F U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨E, i, p, w, h, rfl⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ _ _).1 x
  have hP := h.map_of_exact (restriction J K G)
  have hx' : (Ext.mk₀ (unitMap J K G U)).comp hP.extClass (zero_add 1) = 0 := by
    rw [← Ext.mapExactFunctor_extClass]
    exact hx
  obtain ⟨r, hr⟩ := (Torsors.ext_one_boundary_eq_zero_iff_lift _ hP _ _).1 hx'
  obtain ⟨s, hs'⟩ := (freeYonedaSheafHomEquiv K (G.obj U) E).surjective
    (freeYonedaSheafHomEquiv J U _ r)
  have hs : s ≫ p = 𝟙 _ := by
    apply (freeYonedaSheafHomEquiv K (G.obj U) _).injective
    rw [freeYonedaSheafHomEquiv_comp, hs']
    have := freeYonedaSheafHomEquiv_comp J U r ((restriction J K G).map p)
    have hr' : r ≫ (restriction J K G).map p = unitMap J K G U := hr
    rw [hr', freeYonedaSheafHomEquiv_unitMap] at this
    exact this.symm
  have h0 := (Torsors.ext_one_boundary_eq_zero_iff_lift _ h _ (𝟙 _)).2 ⟨s, hs⟩
  rwa [Ext.mk₀_id_comp] at h0

end Restriction

end Stacks.Cohomology.ContinuousRestriction


end
