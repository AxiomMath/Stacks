module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZero
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of an extension by zero along an étale morphism of algebraic spaces

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` and let `x̄` be a
geometric point of `Y`.  The stalk at `x̄` of the extension by zero `f_!F` of an abelian sheaf
`F` on the small étale site of `X` is the direct sum of the stalks of `F` at the lifts of `x̄`
to `X`:

```
(f_!F)_x̄ = ⨁_{t} F_t.
```

## Main definitions

* `AlgebraicGeometry.Space.EtaleShriekStalk.stalkFamily` is the family of stalks at the lifts.
* `AlgebraicGeometry.Space.EtaleShriekStalk.restrictedSkyscraper` is the restriction to `X` of
  the skyscraper sheaf at `x̄`.

## Main results

* `AlgebraicGeometry.Space.EtaleShriekStalk.stalkExtensionByZeroIso` — the stalk of `f_!F` is
  the direct sum of the stalks of `F` at the lifts.
* `AlgebraicGeometry.Space.EtaleShriekStalk.stalkExtensionByZeroIso_germ` — its value on a
  germ, which characterises it.
* `AlgebraicGeometry.Space.EtaleShriekStalk.isZero_stalkExtensionByZero_of_isEmpty` — the
  stalk vanishes at a geometric point with no lift.

## References

* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace EtaleShriekStalk

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
  (x : GeometricPoint B S hS Y.1)

/-- The family of stalks of an abelian sheaf on `X` at all the lifts of `x̄`, as a functor of
the sheaf. -/
def stalkFamily :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} ⥤
      (GeometricPointLift B S hS f.hom x → AddCommGrpCat.{u}) where
  obj F t := (liftSitePoint B S hS f t).sheafFiber.obj F
  map a t := (liftSitePoint B S hS f t).sheafFiber.map a
  map_id _ := by ext t; simp
  map_comp _ _ := by ext t; simp

/-- The germ map from the sections over an étale neighbourhood `W` of a lift to the stalk
there, the stalk being read as the fibre of the sheaf at the corresponding point of the
site. -/
abbrev liftedGerm (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
    (t : GeometricPointLift B S hS f.hom x) (W : SmallEtale B S hS X.1)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    F.obj.obj (op W) ⟶ (liftSitePoint B S hS f t).sheafFiber.obj F :=
  (liftSitePoint B S hS f t).toPresheafFiber W w F.obj

/-- Sections of the skyscraper sheaf at `x̄` over a chart form the product of copies of `M`
indexed by the lifts of `x̄` to that chart.  This is the projection to one such copy. -/
abbrev skyscraperπ (M : AddCommGrpCat.{u}) (W : SmallEtale B S hS Y.1)
    (q : (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj W) :
    ((etaleSitePoint B S hS Y.1 x Y.2).skyscraperSheafFunctor.obj M).obj.obj (op W) ⟶ M :=
  Pi.π (fun _ => M) q

/-- The adjunction bijection for the skyscraper sheaf, read componentwise. -/
theorem skyscraperSheafAdjunction_app_π
    {F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u}} {M : AddCommGrpCat.{u}}
    (a : (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj F ⟶ M)
    (W : SmallEtale B S hS Y.1) (q : (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj W) :
    (((etaleSitePoint B S hS Y.1 x Y.2).skyscraperSheafAdjunction.homEquiv F M) a).hom.app
        (op W) ≫ skyscraperπ B S hS x M W q =
      (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber W q F.obj ≫ a :=
  (congrArg (fun k => k.app (op W) ≫ Pi.π (fun _ => M) q)
    (GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_apply_hom
      (Φ := etaleSitePoint B S hS Y.1 x Y.2) a)).trans
    ((etaleSitePoint B S hS Y.1 x Y.2).skyscraperPresheafHomEquiv_app_π a W q)

/-- The direct sum of the stalks of a sheaf on `X` at all the lifts of `x̄`. -/
abbrev liftedStalkSum (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :
    AddCommGrpCat.{u} :=
  (stalkFamily B S hS f x ⋙ Sigma.functor (GeometricPointLift B S hS f.hom x)).obj F

/-- The inclusion of the stalk at one lift into the direct sum over all of them. -/
abbrev liftedStalkι (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
    (t : GeometricPointLift B S hS f.hom x) :
    (liftSitePoint B S hS f t).sheafFiber.obj F ⟶ liftedStalkSum B S hS f x F :=
  Sigma.ι (fun t => (liftSitePoint B S hS f t).sheafFiber.obj F) t

/-- The direct sum of the stalks is functorial componentwise. -/
theorem liftedStalkι_map_assoc
    {F G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (a : F ⟶ G)
    (t : GeometricPointLift B S hS f.hom x) {T : AddCommGrpCat.{u}}
    (h : liftedStalkSum B S hS f x G ⟶ T) :
    liftedStalkι B S hS f x F t ≫
        (stalkFamily B S hS f x ⋙ Sigma.functor (GeometricPointLift B S hS f.hom x)).map a ≫
          h =
      (liftSitePoint B S hS f t).sheafFiber.map a ≫ liftedStalkι B S hS f x G t ≫ h :=
  Sigma.ι_map_assoc _ t h

/-- The restriction to `X` of the skyscraper sheaf at `x̄`. -/
abbrev restrictedSkyscraper :
    AddCommGrpCat.{u} ⥤ Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
  (etaleSitePoint B S hS Y.1 x Y.2).skyscraperSheafFunctor (A := AddCommGrpCat.{u}) ⋙
    abelianEtaleRestriction B S hS f hf

/-- The projection of the restricted skyscraper sheaf to the copy indexed by one lift. -/
abbrev restrictedSkyscraperπ (M : AddCommGrpCat.{u}) (W : SmallEtale B S hS X.1)
    (q : (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj
      ((smallEtalePostcomp B S hS f hf).obj W)) :
    ((restrictedSkyscraper B S hS f hf x).obj M).obj.obj (op W) ⟶ M :=
  Pi.π (fun _ => M) q

/-- Two maps into the sections of the restricted skyscraper sheaf agree as soon as all their
components agree. -/
theorem restrictedSkyscraper_hom_ext {M : AddCommGrpCat.{u}} {W : SmallEtale B S hS X.1}
    {T : AddCommGrpCat.{u}}
    {a b : T ⟶ ((restrictedSkyscraper B S hS f hf x).obj M).obj.obj (op W)}
    (h : ∀ q, a ≫ restrictedSkyscraperπ B S hS f hf x M W q =
      b ≫ restrictedSkyscraperπ B S hS f hf x M W q) : a = b :=
  Pi.hom_ext _ _ h

/-- The restriction maps of the restricted skyscraper sheaf are the reindexings of the
product along the action of the lifts. -/
theorem restrictedSkyscraper_obj_map_π (M : AddCommGrpCat.{u})
    {W V : SmallEtale B S hS X.1} (g : W ⟶ V)
    (q : (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj
      ((smallEtalePostcomp B S hS f hf).obj W)) :
    ((restrictedSkyscraper B S hS f hf x).obj M).obj.map g.op ≫
        restrictedSkyscraperπ B S hS f hf x M W q =
      restrictedSkyscraperπ B S hS f hf x M V
        ((etaleSitePoint B S hS Y.1 x Y.2).fiber.map
          ((smallEtalePostcomp B S hS f hf).map g) q) :=
  (Limits.Pi.map'_comp_π
    (f := fun _ : (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj
      ((smallEtalePostcomp B S hS f hf).obj V) => M)
    (g := fun _ : (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj
      ((smallEtalePostcomp B S hS f hf).obj W) => M)
    ((etaleSitePoint B S hS Y.1 x Y.2).fiber.map
      ((smallEtalePostcomp B S hS f hf).map g)) (fun _ => 𝟙 M) q).trans
    (Category.comp_id _)

/-- Post-composition with a map of abelian groups acts componentwise. -/
theorem restrictedSkyscraperπ_naturality {M N : AddCommGrpCat.{u}} (g : M ⟶ N)
    (W : SmallEtale B S hS X.1)
    (q : (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj
      ((smallEtalePostcomp B S hS f hf).obj W)) :
    ((restrictedSkyscraper B S hS f hf x).map g).hom.app (op W) ≫
        restrictedSkyscraperπ B S hS f hf x N W q =
      restrictedSkyscraperπ B S hS f hf x M W q ≫ g :=
  Pi.map_π (fun _ => g) q

section StalkComparison

variable (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) (M : AddCommGrpCat.{u})

/-- The component at `W` of the map to the restricted skyscraper sheaf determined by a family
of maps out of the stalks at the lifts. -/
def stalkFamilyToSkyscraperApp
    (a : ∀ t : GeometricPointLift B S hS f.hom x,
      (liftSitePoint B S hS f t).sheafFiber.obj F ⟶ M)
    (W : SmallEtale B S hS X.1) :
    F.obj.obj (op W) ⟶ ((restrictedSkyscraper B S hS f hf x).obj M).obj.obj (op W) :=
  Pi.lift fun q =>
    let tw := (liftFiberEquiv B S hS f hf W).symm q
    liftedGerm B S hS f x F tw.1 W tw.2 ≫ a tw.1

/-- The defining formula for the components of `stalkFamilyToSkyscraperApp`. -/
theorem stalkFamilyToSkyscraperApp_π
    (a : ∀ t : GeometricPointLift B S hS f.hom x,
      (liftSitePoint B S hS f t).sheafFiber.obj F ⟶ M)
    (W : SmallEtale B S hS X.1) (t : GeometricPointLift B S hS f.hom x)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    stalkFamilyToSkyscraperApp B S hS f hf x F M a W ≫
        restrictedSkyscraperπ B S hS f hf x M W (pushLift B S hS f hf W t w) =
      liftedGerm B S hS f x F t W w ≫ a t := by
  show Pi.lift _ ≫ Pi.π _ ((liftFiberEquiv B S hS f hf W) ⟨t, w⟩) = _
  rw [Pi.lift_π, Equiv.symm_apply_apply]

/-- A family of maps out of the stalks at the lifts assembles into a map to the restricted
skyscraper sheaf. -/
def stalkFamilyToSkyscraper (a : ∀ t : GeometricPointLift B S hS f.hom x,
      (liftSitePoint B S hS f t).sheafFiber.obj F ⟶ M) :
    F ⟶ (restrictedSkyscraper B S hS f hf x).obj M where
  hom :=
    { app W := stalkFamilyToSkyscraperApp B S hS f hf x F M a W.unop
      naturality {W V} g := by
        apply restrictedSkyscraper_hom_ext
        intro q
        obtain ⟨⟨t, w⟩, rfl⟩ := (liftFiberEquiv B S hS f hf V.unop).surjective q
        rw [← Quiver.Hom.op_unop g, liftFiberEquiv_apply, Category.assoc,
          stalkFamilyToSkyscraperApp_π, Category.assoc,
          restrictedSkyscraper_obj_map_π, pushLift_map, stalkFamilyToSkyscraperApp_π]
        exact (liftSitePoint B S hS f t).toPresheafFiber_w_assoc g.unop w F.obj (a t) }

/-- A map to the restricted skyscraper sheaf restricts to a map out of the stalk at each
lift. -/
def skyscraperToStalkFamily (b : F ⟶ (restrictedSkyscraper B S hS f hf x).obj M)
    (t : GeometricPointLift B S hS f.hom x) :
    (liftSitePoint B S hS f t).sheafFiber.obj F ⟶ M :=
  (liftSitePoint B S hS f t).presheafFiberDesc
    (fun W w => b.hom.app (op W) ≫
      restrictedSkyscraperπ B S hS f hf x M W (pushLift B S hS f hf W t w)) (by
      intro W V g w
      change F.obj.map g.op ≫ (b.hom.app (op W) ≫
        restrictedSkyscraperπ B S hS f hf x M W (pushLift B S hS f hf W t w)) = _
      rw [← Category.assoc, b.hom.naturality g.op, Category.assoc,
        restrictedSkyscraper_obj_map_π, pushLift_map])

/-- Families of maps out of the stalks at the lifts correspond to maps into the restricted
skyscraper sheaf. -/
def stalkFamilySkyscraperEquiv :
    (∀ t : GeometricPointLift B S hS f.hom x,
        (liftSitePoint B S hS f t).sheafFiber.obj F ⟶ M) ≃
      (F ⟶ (restrictedSkyscraper B S hS f hf x).obj M) where
  toFun := stalkFamilyToSkyscraper B S hS f hf x F M
  invFun := skyscraperToStalkFamily B S hS f hf x F M
  left_inv a := by
    funext t
    apply (liftSitePoint B S hS f t).presheafFiber_hom_ext
    intro W w
    simp only [skyscraperToStalkFamily,
      GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
    exact stalkFamilyToSkyscraperApp_π B S hS f hf x F M a W t w
  right_inv b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    obtain ⟨W⟩ := W
    apply restrictedSkyscraper_hom_ext
    intro q
    obtain ⟨⟨t, w⟩, rfl⟩ := (liftFiberEquiv B S hS f hf W).surjective q
    change stalkFamilyToSkyscraperApp B S hS f hf x F M _ W ≫
      restrictedSkyscraperπ B S hS f hf x M W (pushLift B S hS f hf W t w) = _
    rw [stalkFamilyToSkyscraperApp_π]
    exact (liftSitePoint B S hS f t).toPresheafFiber_presheafFiberDesc _ _ W w

/-- Maps out of the direct sum of the stalks at the lifts correspond to maps into the
restricted skyscraper sheaf. -/
def directSumHomEquiv :
    ((stalkFamily B S hS f x ⋙ Sigma.functor (GeometricPointLift B S hS f.hom x)).obj F ⟶ M) ≃
      (F ⟶ (restrictedSkyscraper B S hS f hf x).obj M) :=
  (show (∐ (fun t : GeometricPointLift B S hS f.hom x =>
      (liftSitePoint B S hS f t).sheafFiber.obj F) ⟶ M) ≃
    (∀ t : GeometricPointLift B S hS f.hom x,
      (liftSitePoint B S hS f t).sheafFiber.obj F ⟶ M) from
    { toFun := fun a t =>
        Sigma.ι (fun t : GeometricPointLift B S hS f.hom x =>
          (liftSitePoint B S hS f t).sheafFiber.obj F) t ≫ a
      invFun := fun a => Sigma.desc a
      left_inv := fun a => Sigma.hom_ext _ _ fun t => by simp
      right_inv := fun a => by funext t; simp }).trans
    (stalkFamilySkyscraperEquiv B S hS f hf x F M)

/-- The defining formula for the components of `directSumHomEquiv`. -/
theorem directSumHomEquiv_π (a : liftedStalkSum B S hS f x F ⟶ M)
    (W : SmallEtale B S hS X.1) (t : GeometricPointLift B S hS f.hom x)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    (directSumHomEquiv B S hS f hf x F M a).hom.app (op W) ≫
        restrictedSkyscraperπ B S hS f hf x M W (pushLift B S hS f hf W t w) =
      liftedGerm B S hS f x F t W w ≫ liftedStalkι B S hS f x F t ≫ a :=
  stalkFamilyToSkyscraperApp_π B S hS f hf x F M _ W t w

/-- The germ map into the stalk at a lift is natural in the sheaf. -/
theorem liftedGerm_naturality_assoc
    {F G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (a : F ⟶ G)
    (t : GeometricPointLift B S hS f.hom x) (W : SmallEtale B S hS X.1)
    (w : (liftSitePoint B S hS f t).fiber.obj W) {T : AddCommGrpCat.{u}}
    (h : (liftSitePoint B S hS f t).sheafFiber.obj G ⟶ T) :
    liftedGerm B S hS f x F t W w ≫ (liftSitePoint B S hS f t).sheafFiber.map a ≫ h =
      a.hom.app (op W) ≫ liftedGerm B S hS f x G t W w ≫ h :=
  (liftSitePoint B S hS f t).toPresheafFiber_naturality_assoc a.hom W w h

/-- The germ into a summand of the direct sum of the stalks is natural in the sheaf. -/
theorem liftedGerm_ι_map_assoc
    {F G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (a : F ⟶ G)
    (t : GeometricPointLift B S hS f.hom x) (W : SmallEtale B S hS X.1)
    (w : (liftSitePoint B S hS f t).fiber.obj W) {T : AddCommGrpCat.{u}}
    (h : liftedStalkSum B S hS f x G ⟶ T) :
    liftedGerm B S hS f x F t W w ≫ liftedStalkι B S hS f x F t ≫
        (stalkFamily B S hS f x ⋙
          Sigma.functor (GeometricPointLift B S hS f.hom x)).map a ≫ h =
      a.hom.app (op W) ≫ liftedGerm B S hS f x G t W w ≫
        liftedStalkι B S hS f x G t ≫ h := by
  rw [liftedStalkι_map_assoc, liftedGerm_naturality_assoc]

end StalkComparison

/-- The direct sum of the stalks at the lifts of `x̄` is left adjoint to the restricted
skyscraper sheaf at `x̄`. -/
def directSumAdjunction :
    (stalkFamily B S hS f x ⋙ Sigma.functor (GeometricPointLift B S hS f.hom x)) ⊣
      restrictedSkyscraper B S hS f hf x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F M => directSumHomEquiv B S hS f hf x F M
      homEquiv_naturality_left_symm := by
        intro F G M a b
        apply (directSumHomEquiv B S hS f hf x F M).injective
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext W
        obtain ⟨W⟩ := W
        apply restrictedSkyscraper_hom_ext
        intro q
        obtain ⟨⟨t, w⟩, rfl⟩ := (liftFiberEquiv B S hS f hf W).surjective q
        rw [liftFiberEquiv_apply, Equiv.apply_symm_apply]
        change (a.hom.app (op W) ≫ b.hom.app (op W)) ≫
          restrictedSkyscraperπ B S hS f hf x M W (pushLift B S hS f hf W t w) = _
        rw [directSumHomEquiv_π]
        change _ = liftedGerm B S hS f x F t W w ≫ liftedStalkι B S hS f x F t ≫
          (stalkFamily B S hS f x ⋙
            Sigma.functor (GeometricPointLift B S hS f.hom x)).map a ≫
              (directSumHomEquiv B S hS f hf x G M).symm b
        rw [liftedGerm_ι_map_assoc]
        have h := directSumHomEquiv_π B S hS f hf x G M
          ((directSumHomEquiv B S hS f hf x G M).symm b) W t w
        rw [Equiv.apply_symm_apply] at h
        exact congrArg (fun k => a.hom.app (op W) ≫ k) h
      homEquiv_naturality_right := by
        intro F M N a g
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext W
        obtain ⟨W⟩ := W
        apply restrictedSkyscraper_hom_ext
        intro q
        obtain ⟨⟨t, w⟩, rfl⟩ := (liftFiberEquiv B S hS f hf W).surjective q
        rw [liftFiberEquiv_apply, directSumHomEquiv_π]
        change _ = (directSumHomEquiv B S hS f hf x F M a).hom.app (op W) ≫
          ((restrictedSkyscraper B S hS f hf x).map g).hom.app (op W) ≫
            restrictedSkyscraperπ B S hS f hf x N W (pushLift B S hS f hf W t w)
        rw [restrictedSkyscraperπ_naturality]
        have h := directSumHomEquiv_π B S hS f hf x F M a W t w
        simpa only [Category.assoc] using congrArg (fun k => k ≫ g) h.symm }

/-- The component at an étale chart `W` of `X` of the unit of the extension-by-zero
adjunction. -/
abbrev extensionByZeroUnitApp
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
    (W : SmallEtale B S hS X.1) :
    F.obj.obj (op W) ⟶
      ((abelianEtaleExtensionByZero B S hS f hf).obj F).obj.obj
        (op ((smallEtalePostcomp B S hS f hf).obj W)) :=
  ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).unit.app F).hom.app (op W)

/-- Taking the stalk at `x̄` of the extension by zero is left adjoint to the restricted
skyscraper sheaf at `x̄`. -/
def extensionStalkAdjunction :
    (abelianEtaleExtensionByZero B S hS f hf ⋙
        (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber) ⊣
      restrictedSkyscraper B S hS f hf x :=
  (abelianEtaleExtensionByZeroAdjunction B S hS f hf).comp
    (etaleSitePoint B S hS Y.1 x Y.2).skyscraperSheafAdjunction

/-- The defining formula for the components of the adjunction bijection of
`extensionStalkAdjunction`. -/
theorem extensionStalkHomEquiv_π
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) (M : AddCommGrpCat.{u})
    (a : (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj
      ((abelianEtaleExtensionByZero B S hS f hf).obj F) ⟶ M)
    (W : SmallEtale B S hS X.1)
    (q : (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj
      ((smallEtalePostcomp B S hS f hf).obj W)) :
    ((extensionStalkAdjunction B S hS f hf x).homEquiv F M a).hom.app (op W) ≫
        restrictedSkyscraperπ B S hS f hf x M W q =
      extensionByZeroUnitApp B S hS f hf F W ≫
        (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
          ((smallEtalePostcomp B S hS f hf).obj W) q
          ((abelianEtaleExtensionByZero B S hS f hf).obj F).obj ≫ a := by
  rw [extensionStalkAdjunction, Adjunction.comp_homEquiv]
  show (((abelianEtaleExtensionByZeroAdjunction B S hS f hf).homEquiv F _
      ((etaleSitePoint B S hS Y.1 x Y.2).skyscraperSheafAdjunction.homEquiv _ M a)).hom.app
        (op W)) ≫
    skyscraperπ B S hS x M ((smallEtalePostcomp B S hS f hf).obj W) q = _
  rw [Adjunction.homEquiv_apply]
  show (extensionByZeroUnitApp B S hS f hf F W ≫
      (((etaleSitePoint B S hS Y.1 x Y.2).skyscraperSheafAdjunction.homEquiv _ M a).hom.app
        (op ((smallEtalePostcomp B S hS f hf).obj W)))) ≫
    skyscraperπ B S hS x M ((smallEtalePostcomp B S hS f hf).obj W) q = _
  rw [Category.assoc, skyscraperSheafAdjunction_app_π]

/-- The two left adjoints of the restricted skyscraper sheaf agree. -/
def extensionStalkIso :
    (abelianEtaleExtensionByZero B S hS f hf ⋙
        (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber) ≅
      (stalkFamily B S hS f x ⋙ Sigma.functor (GeometricPointLift B S hS f.hom x)) :=
  (extensionStalkAdjunction B S hS f hf x).leftAdjointUniq
    (directSumAdjunction B S hS f hf x)

/-- The stalk at a geometric point `x̄` of `Y` of the extension by zero of an abelian étale sheaf
on `X` is the direct sum of its stalks at the lifts of `x̄` to `X`. -/
@[stacks 08GU "the stalk of an extension by zero of abelian sheaves"]
def stalkExtensionByZeroIso
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :
    (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj
        ((abelianEtaleExtensionByZero B S hS f hf).obj F) ≅
      (∐ fun t : GeometricPointLift B S hS f.hom x =>
        (liftSitePoint B S hS f t).sheafFiber.obj F) :=
  (extensionStalkIso B S hS f hf x).app F

/-- The stalk isomorphism sends the germ of a section over an étale chart `W` of `X`, viewed in
the extension by zero through the adjunction unit, to its germ at the induced lift, in the
corresponding summand. -/
@[stacks 08GU "the germ computation"]
theorem stalkExtensionByZeroIso_germ
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
    (W : SmallEtale B S hS X.1) (t : GeometricPointLift B S hS f.hom x)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    extensionByZeroUnitApp B S hS f hf F W ≫
        (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
          ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w)
          ((abelianEtaleExtensionByZero B S hS f hf).obj F).obj ≫
        (stalkExtensionByZeroIso B S hS f hf x F).hom =
      liftedGerm B S hS f x F t W w ≫ liftedStalkι B S hS f x F t := by
  have h := (extensionStalkAdjunction B S hS f hf x).homEquiv_leftAdjointUniq_hom_app
    (directSumAdjunction B S hS f hf x) F
  have hu : (directSumAdjunction B S hS f hf x).unit.app F =
      directSumHomEquiv B S hS f hf x F _ (𝟙 _) := by
    rw [← Adjunction.homEquiv_id, directSumAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rw [hu] at h
  have he := congrArg (fun k => k.hom.app (op W) ≫
    restrictedSkyscraperπ B S hS f hf x _ W (pushLift B S hS f hf W t w)) h
  rwa [extensionStalkHomEquiv_π, directSumHomEquiv_π B S hS f hf x F _ (𝟙 _) W t w,
    Category.comp_id] at he

/-- The stalk decomposition `stalkExtensionByZeroIso` is natural in the abelian sheaf. -/
@[stacks 08GU "naturality"]
theorem stalkExtensionByZeroIso_naturality
    {F G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (a : F ⟶ G) :
    (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
          ((abelianEtaleExtensionByZero B S hS f hf).map a) ≫
        (stalkExtensionByZeroIso B S hS f hf x G).hom =
      (stalkExtensionByZeroIso B S hS f hf x F).hom ≫
        (stalkFamily B S hS f x ⋙
          Sigma.functor (GeometricPointLift B S hS f.hom x)).map a :=
  (extensionStalkIso B S hS f hf x).hom.naturality a

/-- A coproduct of abelian groups indexed by an empty type is a zero object. -/
theorem isZero_sigma_of_isEmpty {I : Type u} [IsEmpty I] (K : I → AddCommGrpCat.{u}) :
    IsZero (∐ K) := by
  have : ∀ T : AddCommGrpCat.{u}, Unique (∐ K ⟶ T) := fun T =>
    ⟨⟨0⟩, fun _ => Sigma.hom_ext _ _ fun i => isEmptyElim i⟩
  exact IsZero.of_iso (isZero_zero _)
    (IsInitial.uniqueUpToIso (IsInitial.ofUnique _) (isZero_zero _).isInitial)

/-- The extension by zero has zero stalk at every geometric point of `Y` with no lift to `X`. -/
@[stacks 08GU "vanishing away from the image"]
theorem isZero_stalkExtensionByZero_of_isEmpty
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
    [IsEmpty (GeometricPointLift B S hS f.hom x)] :
    IsZero ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj
      ((abelianEtaleExtensionByZero B S hS f hf).obj F)) :=
  IsZero.of_iso (isZero_sigma_of_isEmpty _) (stalkExtensionByZeroIso B S hS f hf x F)

end EtaleShriekStalk

end AlgebraicGeometry.Space

end
