module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineIff
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineZariskiBaseChange
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The two module-level paths of the affine base change differ by a unit

For a morphism `g : U' ⟶ U` of objects of the big fppf site over `S` with affine underlying
schemes, the base change of the associated module `M^~` can be computed through `Φ` (the pullback
of `ε_U^* (M^~|_{X_0})` along `g`) or through Stacks 08GH (the square `ε_U ∘ f = g_0 ∘ ε_{U'}`, the
Zariski pullbacks and Stacks 01I9). On modules both are isomorphisms
`f^* ε_U^* j^* M^~ ≅ (A' ⊗_A M)^~`; this file shows they differ by multiplication by a unit of
`A'`, and records the generic computation which reads the two paths on complexes, degree by
degree.

## Main results

* `ModuleCat.ExtendScalars.exists_isUnit_app_eq_comp_map`: two isomorphisms
  `F₀ ⋙ H ≅ (B ⊗_A -) ⋙ F₂` with `F₂` fully faithful differ by a unit of `B`.
* `Stacks.Homology.pathZ_tail_eq`: the homotopy-level shape of the two paths, generic form.
* `AlgebraicGeometry.Space.representedAffinePathModuleZ`,
  `AlgebraicGeometry.Space.representedAffinePathModuleβ`: the two module-level paths.
* `AlgebraicGeometry.Space.exists_isUnit_representedAffinePathModuleZ`: they differ by a unit.
* `AlgebraicGeometry.Space.representedAffineZariskiPathTail_of_module`: on complexes, after the
  comparison for `Lf^*`, the tails of the two paths differ by the same unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace Stacks.Homology

variable {MA MA' Sp Sp' X0 X0' E E' : Type*} [Category* MA] [Category* MA'] [Category* Sp]
  [Category* Sp'] [Category* X0] [Category* X0'] [Category* E] [Category* E']
  {pMA : Preadditive MA} {pMA' : Preadditive MA'} {pSp : Preadditive Sp} {pSp' : Preadditive Sp'}
  {pX0 : Preadditive X0} {pX0' : Preadditive X0'} {pE : Preadditive E} {pE' : Preadditive E'}

/-- The component of `mapHomotopyCategoryIso e` at `Q` is the image under the quotient of the
component of `e` on the complex `Q.as`. -/
theorem mapHomotopyCategoryIso_hom_app_eq {F G : X0 ⥤ X0'} {_ : F.Additive} {_ : G.Additive}
    (e : F ≅ G) (Q : HomotopyCategory X0 (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app Q =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex e.hom _).app Q.as) :=
  rfl

/-- The component of `Functor.mapHomotopyCategoryCompIso e` at `Q` is the image under the quotient
of the component of `Functor.mapHomologicalComplexCompIso e` on `Q.as`. -/
theorem mapHomotopyCategoryCompIso_hom_app_eq {F : X0 ⥤ X0'} {G : X0' ⥤ E'} {H : X0 ⥤ E'}
    {_ : F.Additive} {_ : G.Additive} {_ : H.Additive} (e : F ⋙ G ≅ H)
    (Q : HomotopyCategory X0 (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app Q =
      (HomotopyCategory.quotient _ _).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app Q.as) :=
  rfl

/-- The inverse of `Functor.mapHomotopyCategoryCompIso e` at `Q` is the image under the quotient
of the inverse of `Functor.mapHomologicalComplexCompIso e` on `Q.as`. -/
theorem mapHomotopyCategoryCompIso_inv_app_eq {F : X0 ⥤ X0'} {G : X0' ⥤ E'} {H : X0 ⥤ E'}
    {_ : F.Additive} {_ : G.Additive} {_ : H.Additive} (e : F ⋙ G ≅ H)
    (Q : HomotopyCategory X0 (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app Q =
      (HomotopyCategory.quotient _ _).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app Q.as) :=
  rfl

/-- The component of `Functor.mapHomotopyCategoryCompFactorsIso ρ` at a complex `K` is the image
under the quotient of the component of `Functor.mapHomologicalComplexCompIso ρ` at `K`. -/
theorem mapHomotopyCategoryCompFactorsIso_hom_app_eq (F : MA ⥤ X0) (G : X0 ⥤ E) (H : MA ⥤ E)
    {hF : F.Additive} {hG : G.Additive} {hH : H.Additive} (ρ : F ⋙ G ≅ H)
    (K : CochainComplex MA ℤ) :
    (@Functor.mapHomotopyCategoryCompFactorsIso _ _ _ _ _ _ _ _ _ F G H hF hG hH ρ).hom.app K =
      (HomotopyCategory.quotient _ _).map
        ((Functor.mapHomologicalComplexCompIso ρ (ComplexShape.up ℤ)).hom.app K) := by
  simp only [Functor.mapHomotopyCategoryCompFactorsIso, Iso.trans_hom, NatTrans.comp_app]
  exact (Category.id_comp _).trans (Category.id_comp _)

/-- Componentwise form of `Stacks.Homology.pathZ_tail_eq`. -/
private theorem pathZ_tail_eq_aux (Ψ₁ Ψ₂ : Sp ⥤ X0') {_ : Ψ₁.Additive} {_ : Ψ₂.Additive}
    (t : MA ⥤ Sp) (j : Sp ⥤ X0) (ε : X0 ⥤ E) (f : E ⥤ E') (g0z g0 : X0 ⥤ X0') (ε' : X0' ⥤ E')
    (fε εg : X0 ⥤ E') (sc : Sp ⥤ Sp') (j' : Sp' ⥤ X0') (t' : MA' ⥤ Sp') (ext : MA ⥤ MA')
    (a : MA ⥤ E) (a' : MA' ⥤ E')
    {_ : t.Additive} {_ : j.Additive} {hε : ε.Additive} {_ : f.Additive} {_ : g0z.Additive}
    {_ : g0.Additive} {hε' : ε'.Additive} {_ : fε.Additive} {_ : εg.Additive} {_ : sc.Additive}
    {_ : j'.Additive} {_ : t'.Additive} {_ : ext.Additive} {ha : a.Additive} {ha' : a'.Additive}
    {htj : (t ⋙ j).Additive} {htj' : (t' ⋙ j').Additive} {_ : (t ⋙ sc).Additive}
    {_ : (ext ⋙ t').Additive} [(ext ⋙ a').Additive]
    (pc1 : fε ≅ ε ⋙ f) (e : fε ≅ εg) (pc2 : εg ≅ g0z ⋙ ε') (z : g0z ≅ g0)
    (m1 : j ⋙ g0 ≅ Ψ₁) (κ : Ψ₁ ≅ Ψ₂) (m2 : sc ⋙ j' ≅ Ψ₂) (tp : t ⋙ sc ≅ ext ⋙ t')
    (η : t ⋙ j ⋙ ε ≅ a) (η' : t' ⋙ j' ⋙ ε' ≅ a') (pb : a ⋙ f ≅ ext ⋙ a') (τm : ext ⟶ ext)
    (sqI : ε.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ f.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      g0z.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ ε'.mapHomotopyCategory (ComplexShape.up ℤ))
    (hsq : Functor.mapHomotopyCategoryCompIso pc1.symm (ComplexShape.up ℤ) ≪≫
      mapHomotopyCategoryIso e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso pc2.symm (ComplexShape.up ℤ)).symm = sqI)
    (M1 : j.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ g0.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      Ψ₁.mapHomotopyCategory (ComplexShape.up ℤ))
    (hM1 : Functor.mapHomotopyCategoryCompIso m1 (ComplexShape.up ℤ) = M1)
    (M2 : sc.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ j'.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      Ψ₂.mapHomotopyCategory (ComplexShape.up ℤ))
    (hM2 : Functor.mapHomotopyCategoryCompIso m2 (ComplexShape.up ℤ) = M2)
    (tpc : t.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        sc.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ext.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ t'.mapHomologicalComplex (ComplexShape.up ℤ))
    (htpc : Functor.mapHomologicalComplexCompIso (Iso.refl (t ⋙ sc)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex tp (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ t')) (ComplexShape.up ℤ)).symm = tpc)
    (Hη : t.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        j.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient _ _ ⋙ ε.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      a.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (hHη : (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (t ⋙ j))
        (ComplexShape.up ℤ)) _ ≪≫
      @Functor.mapHomotopyCategoryCompFactorsIso _ _ _ _ _ _ _ _ _ (t ⋙ j) ε a htj hε ha
        (Functor.associator _ _ _ ≪≫ η) = Hη)
    (Hη' : t'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        j'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient _ _ ⋙ ε'.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      a'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (hHη' : (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (t' ⋙ j'))
        (ComplexShape.up ℤ)) _ ≪≫
      @Functor.mapHomotopyCategoryCompFactorsIso _ _ _ _ _ _ _ _ _ (t' ⋙ j') ε' a' htj' hε' ha'
        (Functor.associator _ _ _ ≪≫ η') = Hη')
    (hmod : ∀ M, pc1.inv.app (j.obj (t.obj M)) ≫ e.hom.app (j.obj (t.obj M)) ≫
        pc2.hom.app (j.obj (t.obj M)) ≫
        ε'.map (z.hom.app (j.obj (t.obj M)) ≫ m1.hom.app (t.obj M) ≫
          κ.hom.app (t.obj M) ≫ m2.inv.app (t.obj M) ≫ j'.map (tp.hom.app M)) ≫
        η'.hom.app (ext.obj M) =
      f.map (η.hom.app M) ≫ pb.hom.app M ≫ a'.map (τm.app M))
    (P : CochainComplex MA ℤ) (τc : (ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      (ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (hτ : (NatTrans.mapHomologicalComplex τm (ComplexShape.up ℤ)).app P = τc)
    (azph : (g0.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((j.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj
            ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ⟶
      (j'.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
        ((t'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))))
    (haz : M1.hom.app
        ((HomotopyCategory.quotient _ _).obj
        ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          (mapHomotopyCategoryIso κ (ComplexShape.up ℤ)).hom.app
            ((HomotopyCategory.quotient _ _).obj
                ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          M2.inv.app _ ≫ (j'.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((HomotopyCategory.quotient _ _).map (tpc.hom.app P)) = azph) :
    sqI.hom.app ((j.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj
        ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      (ε'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((mapHomotopyCategoryIso z (ComplexShape.up ℤ)).hom.app
            ((j.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj
                ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
          azph) ≫
      Hη'.hom.app ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
    (f.mapHomotopyCategory (ComplexShape.up ℤ)).map (Hη.hom.app P) ≫
      (homotopyEdgeIso pb).hom.app P ≫
      (a'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map τc := by
  subst hsq hM1 hM2 htpc hHη hHη' hτ haz
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.id_comp,
    mapHomotopyCategoryCompIso_hom_app_eq, mapHomotopyCategoryCompIso_inv_app_eq,
    mapHomotopyCategoryIso_hom_app_eq, mapHomotopyCategoryCompFactorsIso_hom_app_eq,
    Functor.comp_map,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.comp_map, Functor.mapHomotopyCategory_map, homotopyEdgeIso_hom_app,
    HomotopyCategory.quotient_obj_as]
  have hc : ((Functor.mapHomologicalComplexCompIso pc1.symm (ComplexShape.up ℤ)).hom.app
      ((j.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
      ((j.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      (Functor.mapHomologicalComplexCompIso pc2.symm (ComplexShape.up ℤ)).inv.app
      ((j.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      (ε'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex z.hom (ComplexShape.up ℤ)).app
            ((j.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          (Functor.mapHomologicalComplexCompIso m1 (ComplexShape.up ℤ)).hom.app
          ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (NatTrans.mapHomologicalComplex κ.hom (ComplexShape.up ℤ)).app
          ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Functor.mapHomologicalComplexCompIso m2 (ComplexShape.up ℤ)).inv.app
          ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (j'.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (t ⋙ sc))
                (ComplexShape.up ℤ)).hom.app P ≫
              (NatIso.mapHomologicalComplex tp (ComplexShape.up ℤ)).hom.app P ≫
              (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ t'))
                  (ComplexShape.up ℤ)).inv.app P)) ≫
      (ε'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (t' ⋙ j')) (ComplexShape.up ℤ)).hom.app
            ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      (Functor.mapHomologicalComplexCompIso (Functor.associator _ _ _ ≪≫ η')
          (ComplexShape.up ℤ)).hom.app ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
    (f.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ε.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (t ⋙ j))
              (ComplexShape.up ℤ)).hom.app P) ≫
        (Functor.mapHomologicalComplexCompIso (Functor.associator _ _ _ ≪≫ η)
            (ComplexShape.up ℤ)).hom.app P) ≫
      ((Functor.mapHomologicalComplexCompIso pb (ComplexShape.up ℤ)).hom.app P ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ a')) (ComplexShape.up ℤ)).inv.app P) ≫
      (a'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τm (ComplexShape.up ℤ)).app P) := by
    ext n
    simpa using hmod (P.X n)
  refine congrArg (HomotopyCategory.quotient _ _).map ?_
  exact hc


/-- **The path through Stacks 08GH and the path through `Φ` on complexes**, generic form: they
differ by the image of an endomorphism of `ext` as soon as the module-level paths do. -/
theorem pathZ_tail_eq {D : Type*} [Category* D] (Qh : HomotopyCategory E' (ComplexShape.up ℤ) ⥤ D)
    (Ψ₁ Ψ₂ : Sp ⥤ X0') {hΨ₁ : Ψ₁.Additive} {hΨ₂ : Ψ₂.Additive}
    (t : MA ⥤ Sp) (j : Sp ⥤ X0) (ε : X0 ⥤ E) (f : E ⥤ E') (g0z g0 : X0 ⥤ X0') (ε' : X0' ⥤ E')
    (fε εg : X0 ⥤ E') (sc : Sp ⥤ Sp') (j' : Sp' ⥤ X0') (t' : MA' ⥤ Sp') (ext : MA ⥤ MA')
    (a : MA ⥤ E) (a' : MA' ⥤ E')
    {hAt : t.Additive} {hAj : j.Additive} {hε : ε.Additive} {hAf : f.Additive}
    {hAg0z : g0z.Additive}
    {hAg0 : g0.Additive} {hε' : ε'.Additive} {hAfε : fε.Additive} {hAεg : εg.Additive}
    {hAsc : sc.Additive}
    {hAj' : j'.Additive} {hAt' : t'.Additive} {hAext : ext.Additive} {ha : a.Additive}
    {ha' : a'.Additive}
    {htj : (t ⋙ j).Additive} {htj' : (t' ⋙ j').Additive} {hts : (t ⋙ sc).Additive}
    {het : (ext ⋙ t').Additive} {hea : (ext ⋙ a').Additive}
    (pc1 : fε ≅ ε ⋙ f) (e : fε ≅ εg) (pc2 : εg ≅ g0z ⋙ ε') (z : g0z ≅ g0)
    (m1 : j ⋙ g0 ≅ Ψ₁) (κ : Ψ₁ ≅ Ψ₂) (m2 : sc ⋙ j' ≅ Ψ₂) (tp : t ⋙ sc ≅ ext ⋙ t')
    (η : t ⋙ j ⋙ ε ≅ a) (η' : t' ⋙ j' ⋙ ε' ≅ a') (pb : a ⋙ f ≅ ext ⋙ a') (τm : ext ⟶ ext)
    (sqI : ε.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ f.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      g0z.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ ε'.mapHomotopyCategory (ComplexShape.up ℤ))
    (hsq : Functor.mapHomotopyCategoryCompIso pc1.symm (ComplexShape.up ℤ) ≪≫
      mapHomotopyCategoryIso e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso pc2.symm (ComplexShape.up ℤ)).symm = sqI)
    (M1 : j.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ g0.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      Ψ₁.mapHomotopyCategory (ComplexShape.up ℤ))
    (hM1 : Functor.mapHomotopyCategoryCompIso m1 (ComplexShape.up ℤ) = M1)
    (M2 : sc.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ j'.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      Ψ₂.mapHomotopyCategory (ComplexShape.up ℤ))
    (hM2 : Functor.mapHomotopyCategoryCompIso m2 (ComplexShape.up ℤ) = M2)
    (tpc : t.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        sc.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ext.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ t'.mapHomologicalComplex (ComplexShape.up ℤ))
    (htpc : Functor.mapHomologicalComplexCompIso (Iso.refl (t ⋙ sc)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex tp (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ t')) (ComplexShape.up ℤ)).symm = tpc)
    (Hη : t.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        j.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient _ _ ⋙ ε.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      a.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (hHη : (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (t ⋙ j))
        (ComplexShape.up ℤ)) _ ≪≫
      @Functor.mapHomotopyCategoryCompFactorsIso _ _ _ _ _ _ _ _ _ (t ⋙ j) ε a htj hε ha
        (Functor.associator _ _ _ ≪≫ η) = Hη)
    (Hη' : t'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        j'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient _ _ ⋙ ε'.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      a'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (hHη' : (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (t' ⋙ j'))
        (ComplexShape.up ℤ)) _ ≪≫
      @Functor.mapHomotopyCategoryCompFactorsIso _ _ _ _ _ _ _ _ _ (t' ⋙ j') ε' a' htj' hε' ha'
        (Functor.associator _ _ _ ≪≫ η') = Hη')
    (hmod : ∀ M, (Functor.isoWhiskerLeft (t ⋙ j) (pc1.symm ≪≫ e ≪≫ pc2) ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft t (Functor.isoWhiskerLeft j z ≪≫ m1 ≪≫
          κ ≪≫ m2.symm) ≪≫ Functor.isoWhiskerRight tp j') ε' ≪≫
      Functor.isoWhiskerLeft ext η').hom.app M =
        (Functor.isoWhiskerRight η f ≪≫ pb).hom.app M ≫ a'.map (τm.app M))
    (P : CochainComplex MA ℤ) (τc : (ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      (ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (hτ : (NatTrans.mapHomologicalComplex τm (ComplexShape.up ℤ)).app P = τc)
    (azph : (g0.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((j.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj
            ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ⟶
      (j'.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
        ((t'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))))
    (haz : M1.hom.app
        ((HomotopyCategory.quotient _ _).obj
        ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          (mapHomotopyCategoryIso κ (ComplexShape.up ℤ)).hom.app
            ((HomotopyCategory.quotient _ _).obj
                ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          M2.inv.app _ ≫ (j'.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((HomotopyCategory.quotient _ _).map (tpc.hom.app P)) = azph) :
    Qh.map (sqI.hom.app
        ((j.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
        ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      Qh.map ((ε'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((mapHomotopyCategoryIso z (ComplexShape.up ℤ)).hom.app
            ((j.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj
                ((t.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
          azph)) ≫
      Qh.map (Hη'.hom.app ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
    (f.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh).map (Hη.hom.app P) ≫
      Qh.map ((homotopyEdgeIso pb).hom.app P) ≫
      Qh.map ((a'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              HomotopyCategory.quotient _ _).map τc) := by
  have key := @pathZ_tail_eq_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Ψ₁ Ψ₂ _ _ t j ε f g0z g0 ε' fε εg sc j' t' ext a a'
    hAt _ _ _ _ _ _ _ _ _ _ hAt' hAext _ _ _ _ hts het _
    pc1 e pc2 z m1 κ m2 tp η η' pb τm sqI hsq M1 hM1 M2 hM2 tpc htpc Hη hHη Hη' hHη'
    (by intro M; simpa using hmod M) P τc hτ azph haz
  refine Eq.trans ?_ ((congrArg Qh.map key).trans ?_)
  · exact ((Qh.map_comp _ _).trans (congrArg (Qh.map _ ≫ ·) (Qh.map_comp _ _))).symm
  · exact (Qh.map_comp _ _).trans (congrArg (Qh.map _ ≫ ·) (Qh.map_comp _ _))

/-- Multiplication by a scalar on a functor, read degreewise on complexes. -/
theorem mapHomologicalComplex_smul_id_app {R : Type*} [Semiring R] {V W : Type*} [Category* V]
    [Category* W] [Preadditive V] [Preadditive W] [Linear R W] (F : V ⥤ W) [F.Additive] (c : R)
    (P : CochainComplex V ℤ) :
    (NatTrans.mapHomologicalComplex (c • 𝟙 F) (ComplexShape.up ℤ)).app P =
      c • 𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  ext n
  simp

end Stacks.Homology

namespace ModuleCat.ExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- **Two isomorphisms `F₀ ⋙ H ≅ (B ⊗_A -) ⋙ F₂` differ by a unit**, when `F₂` is fully
faithful: every natural automorphism of extension of scalars is multiplication by a unit. -/
theorem exists_isUnit_app_eq_comp_map {N₀ N₂ : Type*} [Category* N₀] [Category* N₂]
    {F₀ : ModuleCat.{u} A ⥤ N₀} {H : N₀ ⥤ N₂} {F₂ : ModuleCat.{u} B ⥤ N₂}
    (hF : F₂.FullyFaithful) (Ψa Ψb : F₀ ⋙ H ⟶ ModuleCat.extendScalars.{u, u, u} f ⋙ F₂)
    [IsIso Ψa] [IsIso Ψb] :
    ∃ c : B, IsUnit c ∧ ∀ M, Ψa.app M = Ψb.app M ≫ F₂.map (c • 𝟙 _) := by
  obtain ⟨δ, hδ⟩ := Stacks.Homology.exists_app_eq_comp_map Ψa Ψb inferInstance hF
  have hiso : ∀ M, IsIso (δ.app M) := fun M => by
    have e : F₂.map (δ.app M) = inv (Ψb.app M) ≫ Ψa.app M := by
      rw [hδ M, IsIso.inv_hom_id_assoc]
    have : IsIso (F₂.map (δ.app M)) := by
      rw [e]
      infer_instance
    exact hF.isIso_of_isIso_map (δ.app M)
  have : IsIso δ := NatIso.isIso_of_isIso_app δ
  obtain ⟨c, hc, hθ⟩ := exists_isUnit_hom_app_eq_smul f (Iso.refl _) (asIso δ)
  exact ⟨c, hc, fun M => (hδ M).trans (congrArg (Ψb.app M ≫ F₂.map ·) (hθ M))⟩

end ModuleCat.ExtendScalars

namespace AlgebraicGeometry

/-- Transport along an equality of morphisms of schemes, on the homotopy category of modules. -/
theorem pullback_mapHomotopyCategory_eqToHom {X Y : Scheme.{u}} {t₁ t₂ : X ⟶ Y} (h : t₁ = t₂)
    (Q : HomotopyCategory Y.Modules (ComplexShape.up ℤ)) :
    eqToHom (congrArg (fun t => ((Scheme.Modules.pullback t).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj Q) h) =
      (Stacks.Homology.mapHomotopyCategoryIso (eqToIso (congrArg Scheme.Modules.pullback h))
        (ComplexShape.up ℤ)).hom.app Q := by
  subst h
  simp [Stacks.Homology.mapHomotopyCategoryIso_hom_app_eq]
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

attribute [local instance] additive_extendScalars_representedAffineRingHom

/-- The module-level path through `Φ`. -/
def representedAffinePathModuleβ :
    (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⋙
        Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
        representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U) ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom ≅
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom ⋙
        representedAffineToposAssociated B S hS U' :=
  Functor.isoWhiskerRight (representedAffineZariskiAssociatedModuleIso U)
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom) ≪≫
    representedAffineToposPullbackIso B S hS g

/-- The square of Stacks 08GH on modules: `f^* ε^* ≅ (ε ∘ f)^* ≅ (g_0 ∘ ε')^* ≅ ε'^* g_0^*`. -/
def representedZariskiPathModuleSquare :
    representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom ≅
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          ((B.inclusion.map g.left).zariskiRingedToposHom).toModulesHom ⋙
        representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U' :=
  (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := smallEtaleRingedTopos B S hS (representedSpace U))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)).symm ≪≫
    representedZariskiPullbackModulesCompIso B S hS g ≪≫
    RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U')
      (B.inclusion.map g.left).zariskiRingedToposHom

/-- `g_0^* j^* ≅ (g_0 ≫ j)^*` on modules. -/
def representedZariskiPathModuleCompIso :
    Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
        Scheme.Modules.pullback (B.inclusion.map g.left) ≅
      Scheme.Modules.pullback
          ((B.inclusion.map g.left) ≫ ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom) :=
  Stacks.DerivedPullback.Composition.modulePullbackComp
      (B.inclusion.map g.left).toLRSHom.toShHom
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.toLRSHom.toShHom

/-- `j'^* (Spec c)^* ≅ (j' ≫ Spec c)^*` on modules. -/
def representedZariskiPathModuleSpecIso :
    Scheme.Modules.pullback (Spec.map (representedAffineCommRingCatHom B S hS g)) ⋙
        Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom ≅
      Scheme.Modules.pullback (((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom ≫
        Spec.map (representedAffineCommRingCatHom B S hS g)) :=
  Stacks.DerivedPullback.Composition.modulePullbackComp
      ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom.toLRSHom.toShHom
      (Spec.map (representedAffineCommRingCatHom B S hS g)).toLRSHom.toShHom

/-- The Zariski path on modules: `g_0^* j^* M^~ ≅ (g_0 ≫ j)^* M^~ = (j' ≫ Spec c)^* M^~ ≅
j'^* (Spec c)^* M^~`. -/
def representedZariskiPathModuleComp :
    Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
          ((B.inclusion.map g.left).zariskiRingedToposHom).toModulesHom ≅
      Scheme.Modules.pullback (Spec.map (representedAffineCommRingCatHom B S hS g)) ⋙
        Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom)
      (B.inclusion.map g.left).zariskiPullbackModulesIsoModulePullback ≪≫
    representedZariskiPathModuleCompIso g ≪≫
    eqToIso (congrArg Scheme.Modules.pullback (isoSpec_hom_square g)) ≪≫
    (representedZariskiPathModuleSpecIso g).symm

/-- The module-level path through Stacks 08GH. -/
def representedAffinePathModuleZ :
    (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⋙
        Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
        representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U) ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom ≅
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom ⋙
        representedAffineToposAssociated B S hS U' :=
  Functor.isoWhiskerLeft (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⋙
      Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom)
      (representedZariskiPathModuleSquare g) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
          (representedZariskiPathModuleComp g) ≪≫
        Functor.isoWhiskerRight (pullbackTildeIso _ _ (representedAffineCommRingCatHom B S hS g))
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom))
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U') ≪≫
    Functor.isoWhiskerLeft
        (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom)
      (representedAffineZariskiAssociatedModuleIso U')

/-- **The two module-level paths differ by a unit.** -/
theorem exists_isUnit_representedAffinePathModuleZ :
    ∃ c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤), IsUnit c ∧
      ∀ M, (representedAffinePathModuleZ g).hom.app M =
        (representedAffinePathModuleβ g).hom.app M ≫
          (representedAffineToposAssociated B S hS U').map
            ((c • 𝟙 (ModuleCat.extendScalars.{u, u, u}
                (representedAffineCommRingCatHom B S hS g).hom)).app M) := by
  obtain ⟨c, hc, h⟩ := ModuleCat.ExtendScalars.exists_isUnit_app_eq_comp_map _
    (representedAffineToposAssociatedFullyFaithful B S hS U') (representedAffinePathModuleZ g).hom
    (representedAffinePathModuleβ g).hom
  refine ⟨c, hc, fun M => (h M).trans ?_⟩
  simp

/-- The degreewise Zariski path, through the module-level isomorphisms. -/
theorem representedAffineZariskiPathHomotopy_eq
    (P : CochainComplex (ModuleCat.{u} Γ(((BigFppfOver.toScheme B S hS).obj U), ⊤)) ℤ) :
    (Functor.mapHomotopyCategoryCompIso (representedZariskiPathModuleCompIso g)
        (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      (Stacks.Homology.mapHomotopyCategoryIso
          (eqToIso (congrArg Scheme.Modules.pullback (isoSpec_hom_square g)))
        (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      (Functor.mapHomotopyCategoryCompIso (representedZariskiPathModuleSpecIso g)
          (ComplexShape.up ℤ)).inv.app _ ≫
      ((Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient _ _).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (tilde.functor _ ⋙
              Scheme.Modules.pullback (Spec.map (representedAffineCommRingCatHom B S hS g))))
                  (ComplexShape.up ℤ) ≪≫
            NatIso.mapHomologicalComplex
                (pullbackTildeIso _ _ (representedAffineCommRingCatHom B S hS g))
              (ComplexShape.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (ModuleCat.extendScalars.{u, u, u}
              (representedAffineCommRingCatHom B S hS g).hom ⋙ tilde.functor _))
              (ComplexShape.up ℤ)).symm).hom.app P)) =
      affineZariskiPathHomotopy (B.inclusion.map g.left)
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom
        ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom
        (representedAffineCommRingCatHom B S hS g)
        (isoSpec_hom_square g) P := by
  refine (whisker_eq _
      (eq_whisker (pullback_mapHomotopyCategory_eqToHom (isoSpec_hom_square g) _).symm _)).trans ?_
  rfl

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- Transport an equation along heterogeneous equalities of its two sides. -/
private theorem eq_of_heq_of_eq_of_heq {α β : Sort u} {a b : α} {a' b' : β} (h₁ : HEq a' a)
    (h : a = b) (h₂ : HEq b b') : a' = b' :=
  eq_of_heq (h₁.trans ((heq_of_eq h).trans h₂))

attribute [local instance 10000] AlgebraicGeometry.Space.hasSheafCompose_smallEtale_forget₂_ringCat

attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

/-- **The tails of the two paths differ by a unit**, after the comparison for `Lf^*`. -/
theorem representedAffineZariskiPathTail_of_module
    (c : Γ(((BigFppfOver.toScheme B S hS).obj U'), ⊤))
    (hch : ∀ M, (representedAffinePathModuleZ g).hom.app M =
        (representedAffinePathModuleβ g).hom.app M ≫
          (representedAffineToposAssociated B S hS U').map
            ((c • 𝟙 (ModuleCat.extendScalars.{u, u, u}
                (representedAffineCommRingCatHom B S hS g).hom)).app M))
    (P : CochainComplex (ModuleCat.{u} Γ(((BigFppfOver.toScheme B S hS).obj U), ⊤)) ℤ) :
      letI := pullbackModules_smallEtale_additive (representedSpaceMap B S hS g)
      DerivedCategory.Qh.map ((pullbackMapHomotopySquareIso
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U')
        (B.inclusion.map g.left).zariskiRingedToposHom
        (representedZariskiPullbackModulesCompIso B S hS g)).hom.app
        (((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj
            (((tilde.functor _).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      DerivedCategory.Qh.map ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
        (X := smallEtaleRingedTopos B S hS (representedSpace U'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U')).map
          ((@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
            (RingedToposHom.pullbackModules_additive (B.inclusion.map g.left).zariskiRingedToposHom)
            (RingedSpaceModuleAdjunction.modulePullback_additive
                (B.inclusion.map g.left).toLRSHom.toShHom)
            (B.inclusion.map g.left).zariskiPullbackModulesIsoModulePullback
            (ComplexShape.up ℤ)).hom.app _ ≫
          affineZariskiPathHomotopy (B.inclusion.map g.left)
              ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom
            ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom
            (representedAffineCommRingCatHom B S hS g)
            (isoSpec_hom_square g) P)) ≫
      DerivedCategory.Qh.map
        ((representedAffineZariskiAssociatedHomotopyIsoh U').hom.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) =
      (smallEtaleModulePullbackOnHomotopy B S hS (representedSpaceMap B S hS g)).map
        ((representedAffineZariskiAssociatedHomotopyIsoh U).hom.app P) ≫
      DerivedCategory.Qh.map
        ((Stacks.Homology.homotopyEdgeIso (representedAffineToposPullbackIso B S hS g)).hom.app P) ≫
      DerivedCategory.Qh.map ((representedAffineToposHomotopyAssociated B S hS U').map
        (c • 𝟙 _)) := by
  have n := Stacks.Homology.pathZ_tail_eq DerivedCategory.Qh
    (Scheme.Modules.pullback
        ((B.inclusion.map g.left) ≫ ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom))
    (Scheme.Modules.pullback (((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom ≫
        Spec.map (representedAffineCommRingCatHom B S hS g)))
    (hΨ₁ := Scheme.Modules.instAdditivePullback (X := (BigFppfOver.toScheme B S hS).obj U')
      (Y := Spec Γ(((BigFppfOver.toScheme B S hS).obj U), ⊤)) _)
    (hΨ₂ := Scheme.Modules.instAdditivePullback (X := (BigFppfOver.toScheme B S hS).obj U')
      (Y := Spec Γ(((BigFppfOver.toScheme B S hS).obj U), ⊤)) _)
    (MA := ModuleCat.{u} Γ(((BigFppfOver.toScheme B S hS).obj U), ⊤))
    (MA' := ModuleCat.{u} Γ(((BigFppfOver.toScheme B S hS).obj U'), ⊤))
    (Sp := (Spec Γ(((BigFppfOver.toScheme B S hS).obj U), ⊤)).Modules)
    (Sp' := (Spec Γ(((BigFppfOver.toScheme B S hS).obj U'), ⊤)).Modules)
    (X0 := ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (X0' := ((BigFppfOver.toScheme B S hS).obj U').Modules)
    (E := SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
    (E' := SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩))
    (tilde.functor _) (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom)
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U)
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom)
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      ((B.inclusion.map g.left).zariskiRingedToposHom).toModulesHom)
    (Scheme.Modules.pullback (B.inclusion.map g.left))
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U')
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (representedZariskiCompSmallEtaleHom B S hS g).toModulesHom)
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (zariskiCompRepresentedZariskiHom B S hS g).toModulesHom)
    (Scheme.Modules.pullback (Spec.map (representedAffineCommRingCatHom B S hS g)))
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom) (tilde.functor _)
    (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom)
    (representedAffineToposAssociated B S hS U) (representedAffineToposAssociated B S hS U')
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := smallEtaleRingedTopos B S hS (representedSpace U))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U))
    (representedZariskiPullbackModulesCompIso B S hS g)
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U')
      (B.inclusion.map g.left).zariskiRingedToposHom)
    (B.inclusion.map g.left).zariskiPullbackModulesIsoModulePullback
    (representedZariskiPathModuleCompIso g)
    (eqToIso (congrArg Scheme.Modules.pullback (isoSpec_hom_square g)))
    (representedZariskiPathModuleSpecIso g)
    (pullbackTildeIso _ _ (representedAffineCommRingCatHom B S hS g))
    (representedAffineZariskiAssociatedModuleIso U) (representedAffineZariskiAssociatedModuleIso U')
    (representedAffineToposPullbackIso B S hS g) (c • 𝟙 _)
    _ rfl
    _ rfl _ rfl _ rfl
    _ rfl _ rfl
    (fun M => eq_of_heq_of_eq_of_heq (by heq_congr_full) (hch M) (by heq_congr_full)) P (c • 𝟙 _)
    (Stacks.Homology.mapHomologicalComplex_smul_id_app _ _ _)
    (affineZariskiPathHomotopy (B.inclusion.map g.left)
        ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom
        ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom
        (representedAffineCommRingCatHom B S hS g)
        (isoSpec_hom_square g) P)
    (eq_of_heq_of_eq_of_heq (by heq_congr_full) (representedAffineZariskiPathHomotopy_eq g P)
      (by heq_congr_full))
    (hea := inferInstance) (hAt := inferInstance) (hAj := inferInstance)
    (hε := RingedToposHom.pullbackModules_additive
        (X := smallEtaleRingedTopos B S hS (representedSpace U))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U))
    (hAf := pullbackModules_smallEtale_additive (representedSpaceMap B S hS g))
    (hAg0z := RingedToposHom.pullbackModules_additive
        (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (B.inclusion.map g.left).zariskiRingedToposHom)
    (hAg0 := RingedSpaceModuleAdjunction.modulePullback_additive
        (B.inclusion.map g.left).toLRSHom.toShHom)
    (hε' := RingedToposHom.pullbackModules_additive
        (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U').zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U'))
    (hAfε := RingedToposHom.pullbackModules_additive
        (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (representedZariskiCompSmallEtaleHom B S hS g))
    (hAεg := RingedToposHom.pullbackModules_additive
        (X := smallEtaleRingedTopos B S hS (representedSpace U'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (zariskiCompRepresentedZariskiHom B S hS g))
    (hAsc := inferInstance) (hAj' := inferInstance) (hAt' := inferInstance) (hAext := inferInstance)
    (ha := additive_representedAffineToposAssociated B S hS U)
    (ha' := additive_representedAffineToposAssociated B S hS U')
    (htj := inferInstance) (htj' := inferInstance) (hts := inferInstance) (het := inferInstance)
  exact eq_of_heq_of_eq_of_heq (by heq_congr_full) n (by heq_congr_full)




end

end AlgebraicGeometry.Space
