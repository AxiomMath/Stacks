module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageFiberGerm

/-!
# Composition law for the fibre comparison of sheaves of sets

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` and let `x`
be a geometric point of `X`.  The fibre comparison `(f⁻¹ G)_x ≅ G_{f ∘ x}` of Stacks 04K2,
part (4), for sheaves of sets (`AlgebraicGeometry.Space.smallEtaleInverseImageFiberIso`) is
compatible with composition: the comparison for `f ≫ g` is the comparison for `g` at `f ∘ x`,
followed by the comparison for `f` at `x`, followed by the composition isomorphism
`(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` of inverse images.

## Main results

* `AlgebraicGeometry.Space.smallEtaleSkyscraperIso_comp`: the skyscraper comparisons compose,
  through the composition isomorphism of direct images of Stacks 03G2, part (3).
* `AlgebraicGeometry.Space.smallEtaleInverseImageCompIso`: the composition isomorphism of
  inverse images, the conjugate of `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`.
* `AlgebraicGeometry.Space.smallEtaleInverseImageFiberIso_comp`: the composition law for the
  fibre comparison, and its component form `smallEtaleInverseImageFiberIso_comp_hom_app`.

## Implementation notes

The skyscraper form is proved on the spaces-étale sites, where it is a statement about lifts of
geometric points through the composition isomorphism of base changes of Stacks 03G2, part (2)
(`AlgebraicGeometry.Space.spacesBaseChange_comp_projection`), and carried to the small étale
sites by `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_comparison`.  The fibre form is
its conjugate, by `CategoryTheory.conjugateIsoEquiv_symm_comp_of_eq`, a formal statement about
conjugates of composite adjunctions.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

noncomputable section

universe u

namespace CategoryTheory

/-- Let `σ_{fg} : K_x ⋙ R_{fg} ≅ K_z` be the composite of `σ_f : K_x ⋙ R_f ≅ K_y`,
`σ_g : K_y ⋙ R_g ≅ K_z` and `κ : R_f ⋙ R_g ≅ R_{fg}`.  Then the conjugate of `σ_{fg}` is the
composite of the conjugates of `σ_g`, `σ_f` and `κ`. -/
theorem conjugateIsoEquiv_symm_comp_of_eq {A B C T : Type*} [Category A] [Category B]
    [Category C] [Category T] {Lg : A ⥤ B} {Rg : B ⥤ A} {Lf : B ⥤ C} {Rf : C ⥤ B}
    {Lfg : A ⥤ C} {Rfg : C ⥤ A} {Fx : C ⥤ T} {Kx : T ⥤ C} {Fy : B ⥤ T} {Ky : T ⥤ B}
    {Fz : A ⥤ T} {Kz : T ⥤ A} (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adjfg : Lfg ⊣ Rfg)
    (adjx : Fx ⊣ Kx) (adjy : Fy ⊣ Ky) (adjz : Fz ⊣ Kz) (σf : Kx ⋙ Rf ≅ Ky)
    (σg : Ky ⋙ Rg ≅ Kz) (σfg : Kx ⋙ Rfg ≅ Kz) (κ : Rf ⋙ Rg ≅ Rfg)
    (h : σfg = Functor.isoWhiskerLeft Kx κ.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight σf Rg ≪≫ σg) :
    (conjugateIsoEquiv (adjfg.comp adjx) adjz).symm σfg =
      (conjugateIsoEquiv (adjg.comp adjy) adjz).symm σg ≪≫
        Functor.isoWhiskerLeft Lg ((conjugateIsoEquiv (adjf.comp adjx) adjy).symm σf) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((conjugateIsoEquiv (adjg.comp adjf) adjfg).symm κ).symm Fx := by
  subst h
  ext : 1
  simp only [conjugateIsoEquiv_symm_apply_hom, Iso.trans_hom]
  rw [Equiv.symm_apply_eq, ← conjugateEquiv_comp _ (adjg.comp adjy),
    ← conjugateEquiv_comp _ (adjg.comp (adjf.comp adjx)),
    ← conjugateEquiv_comp _ ((adjg.comp adjf).comp adjx)]
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, conjugateIsoEquiv_symm_apply_hom,
    conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply,
    Category.assoc]
  have hassoc := conjugateEquiv_comm (adjg.comp (adjf.comp adjx)) ((adjg.comp adjf).comp adjx)
    (α := (Lg.associator Lf Fx).hom) (β := (Lg.associator Lf Fx).inv) (Iso.inv_hom_id _)
  rw [conjugateEquiv_associator_hom] at hassoc
  rw [(Iso.hom_comp_eq_id _).1 hassoc]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- The maps on lifts of geometric points induced by base change compose, through the
composition isomorphism of base changes of Stacks 03G2, part (2). -/
theorem spacesBaseChangeFiberMap_comp_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : GeometricPoint B S hS X.1) (V : SpacesEtale B S hS Z)
    (w : (spacesGeometricFiber x).obj ((spacesBaseChange B S hS (f ≫ g)).functor.obj V)) :
    (spacesBaseChangeFiberMap B S hS g (geometricPointMap f.hom x)).app V
        ((spacesBaseChangeFiberMap B S hS f x).app ((spacesBaseChange B S hS g).functor.obj V)
          ((spacesGeometricFiber x).map ((spacesBaseChange_comp B S hS f g).inv.app V) w)) =
      (spacesBaseChangeFiberMap B S hS (f ≫ g) x).app V w := by
  have hkey : ((spacesBaseChange_comp B S hS f g).inv.app V).hom.left ≫
      (spacesBaseChange B S hS f).projection.app ((spacesBaseChange B S hS g).functor.obj V) ≫
        (spacesBaseChange B S hS g).projection.app V =
      (spacesBaseChange B S hS (f ≫ g)).projection.app V := by
    rw [← spacesBaseChange_comp_projection, ← Category.assoc]
    exact (congrArg (fun m => m ≫ (spacesBaseChange B S hS (f ≫ g)).projection.app V)
      (congrArg (fun k => k.hom.left)
        ((spacesBaseChange_comp B S hS f g).inv_hom_id_app V))).trans (Category.id_comp _)
  exact Subtype.ext (congrArg (fun k => k.hom.app (op x.val.siteObject) w.1) hkey)

/-- The base-change skyscraper comparisons of sheaves of sets compose, through the composition
isomorphism of spaces-étale direct images. -/
theorem spacesBaseChangeSkyscraperIso_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : GeometricPoint B S hS X.1) (M : Type u) :
    ((spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)).map
        ((spacesBaseChangeSkyscraperIso B S hS f x).hom.app M) ≫
      (spacesBaseChangeSkyscraperIso B S hS g (geometricPointMap f.hom x)).hom.app M =
    (spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
        ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M) ≫
      (spacesBaseChangeSkyscraperIso B S hS (f ≫ g) x).hom.app M := by
  ext V : 3
  induction V using Opposite.rec with | op V => ?_
  refine Pi.hom_ext _ _ (fun v => ?_)
  have hg := spacesBaseChangeSkyscraperIso_hom_app_π B S hS g (geometricPointMap f.hom x) M V v
  have hf := spacesBaseChangeSkyscraperIso_hom_app_π B S hS f x M
    ((spacesBaseChange B S hS g).functor.obj V)
    ((spacesBaseChangeFiberIso B S hS g (geometricPointMap f.hom x)).inv.app V v)
  have hfg := spacesBaseChangeSkyscraperIso_hom_app_π B S hS (f ≫ g) x M V v
  refine ((Category.assoc _ _ _).trans ((congrArg (fun m => _ ≫ m) hg).trans hf)).trans ?_
  refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (fun m => _ ≫ m) hfg).trans ?_))
  have hfib : (spacesGeometricFiber x).map ((spacesBaseChange_comp B S hS f g).inv.app V)
        ((spacesBaseChangeFiberIso B S hS (f ≫ g) x).inv.app V v) =
      (spacesBaseChangeFiberIso B S hS f x).inv.app ((spacesBaseChange B S hS g).functor.obj V)
        ((spacesBaseChangeFiberIso B S hS g (geometricPointMap f.hom x)).inv.app V v) := by
    set w := (spacesGeometricFiber x).map ((spacesBaseChange_comp B S hS f g).inv.app V)
        ((spacesBaseChangeFiberIso B S hS (f ≫ g) x).inv.app V v)
    have h : (spacesBaseChangeFiberIso B S hS g (geometricPointMap f.hom x)).hom.app V
        ((spacesBaseChangeFiberIso B S hS f x).hom.app
          ((spacesBaseChange B S hS g).functor.obj V) w) = v :=
      (spacesBaseChangeFiberMap_comp_app B S hS f g x V _).trans
        (ConcreteCategory.congr_hom
          ((spacesBaseChangeFiberIso B S hS (f ≫ g) x).inv_hom_id_app V) v)
    rw [← h]
    simp
  have hmap : ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
        ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M)).hom.app (op V) =
      Pi.map' ((spacesEtaleSitePoint x).fiber.map
        ((spacesBaseChange_comp B S hS f g).inv.app V)) (fun _ => 𝟙 M) :=
    rfl
  rw [hmap]
  exact (Pi.map'_comp_π _ _ _).trans ((Category.comp_id _).trans (congrArg (Pi.π _) hfib))

/-- The small étale skyscraper comparison at a sheaf of sets is the direct-image comparison of
Stacks 03G8 followed by the base-change skyscraper comparison. -/
theorem smallEtaleSkyscraperIso_hom_app (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)
    (M : Type u) :
    (smallEtaleSkyscraperIso B S hS f x).hom.app M =
      (smallToposMorphismTypeU_comparison B S hS f).hom.app
          ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M) ≫
        ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
          ((spacesBaseChangeSkyscraperIso B S hS f x).hom.app M) := by
  have h0 : (smallEtaleSkyscraperIso B S hS f x).hom.app M =
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
            (𝟙 (((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor
              (A := Type u)).obj M)) ≫
          𝟙 _ ≫
          (smallEtaleRingedToposHom_pushforward B S hS f).hom.app
            ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M) ≫
          𝟙 _ ≫
          ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
              (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
            ((spacesBaseChangeSkyscraperIso B S hS f x).hom.app M) ≫ 𝟙 _ := rfl
  rw [h0, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
    Category.id_comp, Category.comp_id]
  rfl

/-- The diagram chase behind `smallEtaleSkyscraperIso_comp_hom_app`, in an arbitrary
category. -/
private theorem skyscraperComp_chase {C : Type*} [Category C] {P Q R R' T U T₀ T₁ : C}
    (i : P ⟶ Q) (j : Q ⟶ P) (a : Q ⟶ R) (b : R ⟶ R') (ab : Q ⟶ R') (c : R' ⟶ T)
    (d : T ⟶ U) (cd : R' ⟶ U) (c₀ : R ⟶ T₀) (e : T₀ ⟶ T) (k : T₀ ⟶ T₁) (m : T₁ ⟶ U)
    (p : P ⟶ T₁) (hab : ab = a ≫ b) (hcd : cd = c ≫ d) (hnat : b ≫ c = c₀ ≫ e)
    (hii : e ≫ d = k ≫ m) (hcomp : a ≫ c₀ ≫ k = j ≫ p) (hij : i ≫ j = 𝟙 P) :
    p ≫ m = i ≫ ab ≫ cd := by
  rw [hab, hcd, Category.assoc, reassoc_of% hnat, hii, reassoc_of% hcomp, reassoc_of% hij]

/-- The component form of `AlgebraicGeometry.Space.smallEtaleSkyscraperIso_comp`. -/
theorem smallEtaleSkyscraperIso_comp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : GeometricPoint B S hS X.1) (M : Type u) :
    (smallEtaleSkyscraperIso B S hS (f ≫ g) x).hom.app M =
      (smallToposMorphismTypeU_comp B S hS f g).inv.app
          (((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor (A := Type u)).obj M) ≫
        (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.map
          ((smallEtaleSkyscraperIso B S hS f x).hom.app M) ≫
        (smallEtaleSkyscraperIso B S hS g (geometricPointMap f.hom x)).hom.app M := by
  let H := (spacesEtaleSitePoint x).skyscraperSheafFunctor (A := Type u) |>.obj M
  let cZ := (comparisonFunctor B S hS Z).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)
  let gs := (smallToposMorphismTypeU B S hS g).pushforward
  have hab := (congrArg gs.map (smallEtaleSkyscraperIso_hom_app B S hS f x M)).trans
    (gs.map_comp _ _)
  have hii := ((cZ.map_comp _ _).symm.trans
    (congrArg cZ.map (spacesBaseChangeSkyscraperIso_comp B S hS f g x M))).trans
      (cZ.map_comp _ _)
  exact (smallEtaleSkyscraperIso_hom_app B S hS (f ≫ g) x M).trans
    (skyscraperComp_chase _ _ _ _ _ _ _ _ _ _ _ _ _ hab
      (smallEtaleSkyscraperIso_hom_app B S hS g (geometricPointMap f.hom x) M)
      ((smallToposMorphismTypeU_comparison B S hS g).hom.naturality
        ((spacesBaseChangeSkyscraperIso B S hS f x).hom.app M))
      hii (smallToposMorphismTypeU_comp_comparison B S hS f g H)
      ((smallToposMorphismTypeU_comp B S hS f g).inv_hom_id_app _))

/-- The small étale skyscraper comparisons of sheaves of sets compose: the comparison for
`f ≫ g` at `x` is the comparison for `f` at `x` followed by the comparison for `g` at `f ∘ x`,
through the composition isomorphism of direct images of Stacks 03G2, part (3). -/
theorem smallEtaleSkyscraperIso_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : GeometricPoint B S hS X.1) :
    smallEtaleSkyscraperIso B S hS (f ≫ g) x =
      Functor.isoWhiskerLeft
          ((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor (A := Type u))
          (smallToposMorphismTypeU_comp B S hS f g).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleSkyscraperIso B S hS f x)
          (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward ≪≫
        smallEtaleSkyscraperIso B S hS g (geometricPointMap f.hom x) :=
  Iso.ext (NatTrans.ext (funext fun M =>
    (smallEtaleSkyscraperIso_comp_hom_app B S hS f g x M).trans
      (congrArg (fun m => _ ≫ m) (Category.id_comp _).symm)))

/-- The inverse-image composition isomorphism `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` of sheaves of sets on
the small étale sites: the conjugate of `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`. -/
noncomputable def smallEtaleInverseImageCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom.inverseImage ≅
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage ⋙
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage :=
  (conjugateIsoEquiv ((smallEtaleRingedToposHom B S hS g).toToposHom.adj.comp
      (smallEtaleRingedToposHom B S hS f).toToposHom.adj)
    (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom.adj).symm
    (smallToposMorphismTypeU_comp B S hS f g)

/-- **Composition law for the fibre comparison of Stacks 04K2, part (4).**  For sheaves of
sets, the comparison `((f ≫ g)⁻¹ G)_x ≅ G_{g ∘ f ∘ x}` is the comparison for `g` at `f ∘ x`,
followed by the comparison for `f` at `x`, followed by `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹`. -/
theorem smallEtaleInverseImageFiberIso_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : GeometricPoint B S hS X.1) :
    smallEtaleInverseImageFiberIso B S hS (f ≫ g) x =
      smallEtaleInverseImageFiberIso B S hS g (geometricPointMap f.hom x) ≪≫
        Functor.isoWhiskerLeft (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
          (smallEtaleInverseImageFiberIso B S hS f x) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleInverseImageCompIso B S hS f g).symm
          ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)) :=
  conjugateIsoEquiv_symm_comp_of_eq _ _ _ _ _ _ _ _ _ _
    (smallEtaleSkyscraperIso_comp B S hS f g x)

/-- The component form of `AlgebraicGeometry.Space.smallEtaleInverseImageFiberIso_comp`. -/
theorem smallEtaleInverseImageFiberIso_comp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : GeometricPoint B S hS X.1) (F : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) :
    (smallEtaleInverseImageFiberIso B S hS (f ≫ g) x).hom.app F =
      (smallEtaleInverseImageFiberIso B S hS g (geometricPointMap f.hom x)).hom.app F ≫
        (smallEtaleInverseImageFiberIso B S hS f x).hom.app
          ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.obj F) ≫
        ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)).map
          ((smallEtaleInverseImageCompIso B S hS f g).inv.app F) :=
  (congrArg (fun e => e.hom.app F) (smallEtaleInverseImageFiberIso_comp B S hS f g x)).trans
    (congrArg (fun m => _ ≫ _ ≫ m) (Category.id_comp _))

end AlgebraicGeometry.Space

end
