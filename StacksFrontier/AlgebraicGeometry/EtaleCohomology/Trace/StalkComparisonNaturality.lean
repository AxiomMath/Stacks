module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap

/-!
# Naturality of the stalk comparison in the geometric point

`AlgebraicGeometry.sheafEquivCompSheafFiberIso` identifies the stalk functor of Mathlib's point of
the small étale site at a geometric point with the stalk functor of the bounded small étale site of
[Stacks, Tag 021B].  This file computes it on germs and shows that it is natural in morphisms of
geometric points: the map of stalks that Mathlib attaches to a morphism of points corresponds to
the canonical map `geometricPointStalkMap` of [Stacks, Tag 04FN].

## Main results

* `AlgebraicGeometry.toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv`: the germ formula for the
  fibre comparison through a continuous functor of sites.
* `AlgebraicGeometry.toPresheafFiber_sheafEquivCompSheafFiberIso_inv`: its instance for the two
  small étale sites.
* `AlgebraicGeometry.sheafEquivCompSheafFiberIso_inv_naturality`: naturality of the stalk
  comparison in morphisms of geometric points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w r z uC vC uD vD uA vA

namespace AlgebraicGeometry

section General

/-- The unit of the skyscraper adjunction at a point, followed by a projection of the product,
is the germ at the corresponding element of the fibre. -/
theorem skyscraperSheafAdjunction_unit_app_hom_app_π {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{z}) {A : Type uA} [Category.{vA} A]
    [HasProducts.{z} A] [HasColimitsOfSize.{z, z} A] (F : Sheaf J A) (U : C)
    (x : Φ.fiber.obj U) :
    (Φ.skyscraperSheafAdjunction.unit.app F).hom.app (op U) ≫
        Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj F) x =
      Φ.toPresheafFiber U x F.obj := by
  have h1 : (Φ.skyscraperSheafAdjunction.unit.app F).hom =
      Φ.skyscraperPresheafHomEquiv (𝟙 (Φ.presheafFiber.obj F.obj)) := by
    rw [← Adjunction.homEquiv_id]
    exact Φ.skyscraperSheafAdjunction_homEquiv_apply_hom _
  have h2 := Φ.skyscraperPresheafHomEquiv_app_π (P := F.obj) (𝟙 (Φ.presheafFiber.obj F.obj)) U x
  rw [Category.comp_id] at h2
  exact (congrArg (fun φ => φ.app (op U) ≫ Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj F) x)
    h1).trans h2

/-- The unit of the skyscraper adjunction at a point, followed by the skyscraper of a map out of
the fibre and a projection of the product, is the germ followed by that map. -/
theorem skyscraperSheafAdjunction_unit_app_map_hom_app_π {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{z}) {A : Type uA} [Category.{vA} A]
    [HasProducts.{z} A] [HasColimitsOfSize.{z, z} A] (F : Sheaf J A) {N : A}
    (g : Φ.sheafFiber.obj F ⟶ N) (U : C) (x : Φ.fiber.obj U) :
    ((Φ.skyscraperSheafAdjunction.unit.app F).hom.app (op U) ≫
        (Φ.skyscraperSheafFunctor.map g).hom.app (op U)) ≫ Pi.π (fun _ : Φ.fiber.obj U => N) x =
      Φ.toPresheafFiber U x F.obj ≫ g := by
  have h : (Φ.skyscraperSheafFunctor.map g).hom.app (op U) ≫ Pi.π (fun _ : Φ.fiber.obj U => N) x =
      Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj F) x ≫ g :=
    Pi.map_π (fun _ : Φ.fiber.obj U => g) x
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans
    ((Category.assoc _ _ _).symm.trans ?_))
  exact congrArg (· ≫ g) (skyscraperSheafAdjunction_unit_app_hom_app_π Φ F U x)

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
  (p : J.Point.{z}) (q : K.Point.{z}) (G : C ⥤ D) [G.IsContinuous J K]
  {A : Type uA} [Category.{vA} A] [HasProducts.{z} A] [HasColimitsOfSize.{z, z} A]
  {L : Sheaf J A ⥤ Sheaf K A} (adj : L ⊣ G.sheafPushforwardContinuous A J K)

/-- The germ formula for a fibre comparison obtained by conjugating an isomorphism of skyscraper
functors which, on sections over `U`, is the reindexing of products along a map of fibres. -/
theorem toPresheafFiber_conjugateIsoEquiv_symm_hom (ε : p.fiber ⟶ G ⋙ q.fiber)
    (e' : q.skyscraperSheafFunctor ⋙ G.sheafPushforwardContinuous A J K ≅
      p.skyscraperSheafFunctor)
    (he' : ∀ (M : A) (U : C) (x : p.fiber.obj U),
      (e'.hom.app M).hom.app (op U) ≫ Pi.π (fun _ : p.fiber.obj U => M) x =
        Pi.π (fun _ : q.fiber.obj (G.obj U) => M) (ε.app U x))
    (F : Sheaf J A) (U : C) (x : p.fiber.obj U) :
    p.toPresheafFiber U x F.obj ≫ p.sheafToPresheafCompPresheafFiberIso.hom.app F ≫
        ((conjugateIsoEquiv (adj.comp q.skyscraperSheafAdjunction)
          p.skyscraperSheafAdjunction).symm e').hom.app F =
      (adj.unit.app F).hom.app (op U) ≫
        q.toPresheafFiber (G.obj U) (ε.app U x) (L.obj F).obj := by
  have h := congrArg (fun φ => φ.hom.app (op U) ≫
      Pi.π (fun _ : p.fiber.obj U => q.sheafFiber.obj (L.obj F)) x)
    (unit_conjugateEquiv_symm (adj.comp q.skyscraperSheafAdjunction)
      p.skyscraperSheafAdjunction e'.hom F)
  rw [Adjunction.comp_unit_app] at h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  have hA := skyscraperSheafAdjunction_unit_app_map_hom_app_π p F
    (((conjugateEquiv (adj.comp q.skyscraperSheafAdjunction) p.skyscraperSheafAdjunction).symm
      e'.hom).app F) U x
  have hB : ((adj.unit.app F).hom.app (op U) ≫
      ((G.sheafPushforwardContinuous A J K).map
        (q.skyscraperSheafAdjunction.unit.app (L.obj F))).hom.app (op U) ≫
          (e'.hom.app ((L ⋙ q.sheafFiber).obj F)).hom.app (op U)) ≫
        Pi.π (fun _ : p.fiber.obj U => q.sheafFiber.obj (L.obj F)) x =
      (adj.unit.app F).hom.app (op U) ≫
        q.toPresheafFiber (G.obj U) (ε.app U x) (L.obj F).obj := by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      ((congrArg (fun k => _ ≫ _ ≫ k) (he' _ U x)).trans ?_))
    exact congrArg ((adj.unit.app F).hom.app (op U) ≫ ·)
      (skyscraperSheafAdjunction_unit_app_hom_app_π q (L.obj F) (G.obj U) (ε.app U x))
  exact (congrArg (p.toPresheafFiber U x F.obj ≫ ·) (Category.id_comp _)).trans
    (hA.symm.trans (h.symm.trans
      ((congrArg (· ≫ Pi.π (fun _ : p.fiber.obj U => q.sheafFiber.obj (L.obj F)) x)
        (Category.assoc _ _ _)).trans hB)))

/-- **The germ formula for the fibre comparison through a continuous functor.**  For a left
adjoint `L` of the direct image along `G`, the comparison `L ⋙ q.sheafFiber ≅ p.sheafFiber` of
`sheafFiberIsoOfAdjOfFiberIso` sends the germ of a section `σ` over `U` at `x` to the germ of the
image of `σ` in `(L F)(G U)` at the element of the fibre of `q` corresponding to `x`. -/
theorem toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv (e : G ⋙ q.fiber ≅ p.fiber)
    (F : Sheaf J A) (U : C) (x : p.fiber.obj U) :
    p.toPresheafFiber U x F.obj ≫ p.sheafToPresheafCompPresheafFiberIso.hom.app F ≫
        (sheafFiberIsoOfAdjOfFiberIso p q G e adj).inv.app F =
      (adj.unit.app F).hom.app (op U) ≫
        q.toPresheafFiber (G.obj U) (e.inv.app U x) (L.obj F).obj :=
  toPresheafFiber_conjugateIsoEquiv_symm_hom p q G adj e.inv _
    (fun _ _ x => (Pi.map'_comp_π _ _ x).trans (Category.comp_id _)) F U x

end General

section SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

/-- The germ formula for the stalk comparison of the two small étale sites: a germ on the bounded
site goes to the germ, at the same lift of the geometric point, of the corresponding section of
the sheaf on Mathlib's site. -/
theorem toPresheafFiber_sheafEquivCompSheafFiberIso_inv (s : GeometricPoint X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (U : SmallEtale B X.obj X.property) (x : (geometricPointFiber B X.obj X.property s).obj U) :
    (geometricSitePoint B X s).toPresheafFiber U x F.obj ≫
        (sheafEquivCompSheafFiberIso B X Λ s).inv.app F =
      ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).unit.app F).hom.app (op U) ≫
        (Scheme.pointSmallEtale s.hom).toPresheafFiber
          ((SmallEtale.toEtaleSite B X.obj X.property).obj U)
          ((toEtaleSiteFiberIso B X.obj X.property s).inv.app U x)
          ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor.obj F).obj :=
  (congrArg ((geometricSitePoint B X s).toPresheafFiber U x F.obj ≫ ·)
      (Category.id_comp _)).symm.trans
    (toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv (geometricSitePoint B X s)
      (Scheme.pointSmallEtale s.hom) (SmallEtale.toEtaleSite B X.obj X.property)
      (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).toAdjunction
      (toEtaleSiteFiberIso B X.obj X.property s) F U x)

/-- **Naturality of the stalk comparison in the geometric point.**  For a morphism `a` of
geometric points, the map of stalk functors of Mathlib's points induced by `a` corresponds, under
the comparison of the two small étale sites, to the canonical map `geometricPointStalkMap` of
[Stacks, Tag 04FN] on the bounded site. -/
theorem sheafEquivCompSheafFiberIso_inv_naturality {s t : GeometricPoint X.obj}
    (a : GeometricPoint.Hom s t) :
    (sheafEquivCompSheafFiberIso B X Λ t).inv ≫
        Functor.whiskerLeft (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor
          (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X.obj a)) =
      Functor.whiskerLeft (sheafToPresheaf _ _)
          (geometricPointStalkMap B X.obj X.property a (ModuleCat.{w} Λ)) ≫
        (sheafEquivCompSheafFiberIso B X Λ s).inv := by
  ext F : 2
  refine (geometricSitePoint B X t).presheafFiber_hom_ext (fun U x => ?_)
  let L := (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor
  have h2 := (Scheme.pointSmallEtale t.hom).toPresheafFiber_presheafFiberDesc
    (A := ModuleCat.{w} Λ) (P := (L.obj F).obj)
    (fun V v => (Scheme.pointSmallEtale s.hom).toPresheafFiber V
      ((smallEtalePointHom X.obj a).hom.app V v) (L.obj F).obj) (by
        intro V W g v
        exact ((Scheme.pointSmallEtale s.hom).toPresheafFiber_w g _ _).trans (by congr 1))
    ((SmallEtale.toEtaleSite B X.obj X.property).obj U)
    ((toEtaleSiteFiberIso B X.obj X.property t).inv.app U x)
  have hl := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (GrothendieckTopology.Point.Hom.sheafFiber
        (smallEtalePointHom X.obj a)).app (L.obj F))
      (toPresheafFiber_sheafEquivCompSheafFiberIso_inv B X Λ t F U x)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2)))
  have hr := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (sheafEquivCompSheafFiberIso B X Λ s).inv.app F)
      (colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B X.obj X.property s)).op ⋙
        F.obj) (neighborhoodFunctor B X.obj X.property a).op (op ⟨U, x⟩))).trans
    (toPresheafFiber_sheafEquivCompSheafFiberIso_inv B X Λ s F U _))
  refine hl.trans (Eq.trans ?_ hr.symm)
  congr 2

end SmallEtale

end AlgebraicGeometry
