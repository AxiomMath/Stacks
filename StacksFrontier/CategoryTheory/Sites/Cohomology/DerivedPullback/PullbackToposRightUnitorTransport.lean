module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUnitEssentiallySmall

/-! # The right-unitor coherence of Stacks 03EL, transported to the site-presented pullback

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor of
the underlying sites which is a morphism of sites. Two pullbacks of sheaves of modules are then
available: the one of the four-field presentation of Stacks 03D6,
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` at
`Stacks.Sheaves.DerivedPullback.modulesHomOfSiteHom f hmos`, and the site-presented one,
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`. They are identified by
`Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso`.

This file shows that the right-unitor coherence of the comparison of Stacks 03EL for the
site-presented pullback, `Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`,
follows from the same coherence for the four-field pullback. The only identification needed is
that the unit comparison `ν : f^*𝒪_D ⟶ 𝒪_C` of Mathlib's `SheafOfModules.pullbackObjUnitToUnit`,
precomposed with the identification of the two pullbacks, is the four-field unit comparison
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`.

## Main results

* `CategoryTheory.Sheaf.unit_hom_ext_val_app_one`: a morphism out of the free sheaf of modules of
  rank one is determined by the image of the unit section.
* `Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence_of_fourFieldCoherence`: the
  right-unitor coherence of Stacks 03EL for the site-presented pullback follows from the
  right-unitor coherence of Stacks 03EL for the four-field pullback at
  `modulesHomOfSiteHom f hmos`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

namespace CategoryTheory.Sheaf

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] {R : Sheaf J RingCat.{u}}

/-- **A morphism out of the free sheaf of modules of rank one is determined by the image of the
unit section.** -/
theorem unit_hom_ext_val_app_one {N : SheafOfModules.{u} R} (a b : SheafOfModules.unit R ⟶ N)
    (h : ∀ W : Cᵒᵖ, a.val.app W (1 : R.obj.obj W) = b.val.app W (1 : R.obj.obj W)) : a = b := by
  have key : ∀ (c : SheafOfModules.unit R ⟶ N) (W : Cᵒᵖ),
      (SheafOfModules.unitHomEquiv N c).val W = c.val.app W (1 : R.obj.obj W) := fun c W ↦
    (unitHomEquiv_symm_val_app_one N (SheafOfModules.unitHomEquiv N c) W).symm.trans
      (congrArg (fun z : SheafOfModules.unit R ⟶ N ↦ z.val.app W (1 : R.obj.obj W))
        ((SheafOfModules.unitHomEquiv N).symm_apply_apply c))
  refine (SheafOfModules.unitHomEquiv N).injective ?_
  ext W
  exact (key a W).trans ((h W).trans (key b W).symm)

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.DerivedPullback

/-! ## Transport of a right-unitor coherence along an isomorphism of functors -/

section Abstract

universe v₁ u₁ v₂ u₂

/-- **Transport of a right-unitor coherence along an isomorphism of left adjoints.** Let
`P ≅ P' : C ⥤ E` be two functors identified by `ε`, let `T` be a bifunctor on `E` with `I`-right
unitor `ρ`, and suppose the coherence holds for `P` with unit comparison `ν₄`. Then it holds for
`P'` with any unit comparison `ν` whose precomposition with `ε` is `ν₄`. -/
private lemma transportRightUnitor {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
    {P P' : C ⥤ E} (ε : P ≅ P') (T : E ⥤ E ⥤ E) (I : E) (ρ : T.flip.obj I ≅ 𝟭 E)
    (A W Z : C) (ρ₀ : W ⟶ A) (Θ : P.obj W ⟶ (T.obj (P.obj A)).obj (P.obj Z))
    (ν : P'.obj Z ⟶ I) (ν₄ : P.obj Z ⟶ I) (hunit : ε.hom.app Z ≫ ν = ν₄)
    (hfour : Θ ≫ (T.obj (P.obj A)).map ν₄ ≫ ρ.hom.app (P.obj A) = P.map ρ₀) :
    (ε.inv.app W ≫ Θ ≫ (T.map (ε.hom.app A)).app (P.obj Z) ≫
          (T.obj (P'.obj A)).map (ε.hom.app Z)) ≫
        (T.obj (P'.obj A)).map ν ≫ ρ.hom.app (P'.obj A) =
      P'.map ρ₀ := by
  subst hunit
  have key : (T.map (ε.hom.app A)).app (P.obj Z) ≫ (T.obj (P'.obj A)).map (ε.hom.app Z) ≫
        (T.obj (P'.obj A)).map ν ≫ ρ.hom.app (P'.obj A) =
      ((T.obj (P.obj A)).map (ε.hom.app Z ≫ ν) ≫ ρ.hom.app (P.obj A)) ≫ ε.hom.app A := by
    rw [← Functor.map_comp_assoc, ← Category.assoc,
      ← (T.map (ε.hom.app A)).naturality (ε.hom.app Z ≫ ν), Category.assoc, Category.assoc]
    refine congrArg (fun z ↦ (T.obj (P.obj A)).map (ε.hom.app Z ≫ ν) ≫ z) ?_
    exact ρ.hom.naturality (ε.hom.app A)
  rw [Category.assoc, Category.assoc, Category.assoc, key, ← Category.assoc, ← Category.assoc,
    Category.assoc (ε.inv.app W), hfour, Category.assoc, ε.hom.naturality ρ₀,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end Abstract

section SiteMorphism

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

/- Sheafification of abelian presheaves is not a section variable here: the statement and proof
below use the global instance `Stacks.SheafOfModules.coefficientSheafification`. -/

/-! ## The transport -/

/-- **The right-unitor coherence of Stacks 03EL for the site-presented pullback follows from the
right-unitor coherence of Stacks 03EL for the four-field pullback.**

The hypothesis is the coherence of [Stacks, Tag 03EL] against the right unitor for the
four-field morphism of ringed topoi `modulesHomOfSiteHom f hmos` of Stacks 03D6: the comparison
`f^*(A ⊗_{𝒪_D} 𝒪_D) ⟶ f^*A ⊗_{𝒪_C} f^*𝒪_D` of `Stacks.SheafOfModules.pullbackTensorIso`,
followed by the four-field unit comparison
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` of Stacks 03LU in the second
tensor factor and by the right unitor `Stacks.SheafOfModules.sheafTensorUnitNatIso`, is the
pullback of the right unitor. The conclusion is
`Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`, the same statement for the
site-presented pullback and Mathlib's unit comparison `SheafOfModules.pullbackObjUnitToUnit`. -/
theorem pullbackToposRightUnitorCoherence_of_fourFieldCoherence
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hfour : ∀ A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      (Stacks.SheafOfModules.pullbackTensorIso (modulesHomOfSiteHom f hmos)).hom.app
            (A, SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (((modulesHomOfSiteHom f hmos).pullbackModules).obj A)).map
              (pullbackModulesObjUnitIso (modulesHomOfSiteHom f hmos)).inv ≫
            (Stacks.SheafOfModules.sheafTensorUnitNatIso X.O).hom.app
              (((modulesHomOfSiteHom f hmos).pullbackModules).obj A) =
        ((modulesHomOfSiteHom f hmos).pullbackModules).map
          ((Stacks.SheafOfModules.sheafTensorUnitNatIso Y.O).hom.app A)) :
    PullbackToposRightUnitorCoherence f hmos := by
  intro A
  exact transportRightUnitor (ε := pullbackModulesSiteIso f hmos)
    (T := Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (I := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ρ := Stacks.SheafOfModules.sheafTensorUnitNatIso X.O)
    (A := A)
    (W := ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj A).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (Z := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ρ₀ := (Stacks.SheafOfModules.sheafTensorUnitNatIso Y.O).hom.app A)
    (Θ := (Stacks.SheafOfModules.pullbackTensorIso (modulesHomOfSiteHom f hmos)).hom.app
      (A, SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (ν := SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing)
    (ν₄ := (pullbackModulesObjUnitIso (modulesHomOfSiteHom f hmos)).inv)
    (hunit := pullbackModulesSiteIso_hom_app_unit_comp_pullbackObjUnitToUnit f hmos)
    (hfour := hfour A)

end SiteMorphism

end Stacks.Sheaves.DerivedPullback

end
