module

public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceBaseChange

/-!
# Gluing a family of algebraic spaces over the points of an algebraic space

Let `T` be an algebraic space over the base scheme `S` of a big fppf site, and let `G` be a functor
over the site from the category `𝒮_T` of points of `T` to the families of algebraic spaces over
varying schemes with cartesian squares as morphisms. For a point `(U, t)` write `G(U, t) ⟶ U` for
the family `G` attaches to it. This file builds the presheaf `X` on the site whose sections over
`W` are the pairs of a point `t ∈ T(W)` and a section over `W` of `G(W, t) ⟶ W`, together with
its projection to `T`, and shows that for every point `(U, t)` the square

```text
  G(U, t) ---> X
     |         |
     v         v
     U  --t--> T
```

is cartesian. This is the construction of the quasi-inverse in Stacks 0E93.

## Main definitions

* `AlgebraicGeometry.SpacesOverSpace.glue`: the presheaf `X`.
* `AlgebraicGeometry.SpacesOverSpace.glueToBase`: its projection to `T`.
* `AlgebraicGeometry.SpacesOverSpace.famToGlue`: the map `G(U, t) ⟶ X`.

## Main results

* `AlgebraicGeometry.SpacesOverSpace.isPullback_famToGlue`: the square above is cartesian.

## References

* [Stacks Project, Tag 0E93](https://stacks.math.columbia.edu/tag/0E93)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

/-- A commutative square of functors which is cartesian after evaluation at every object is
cartesian. -/
theorem isPullback_of_isPullback_app {K : Type*} [Category* K] {D : Type*} [Category* D]
    {P X Y Z : K ⥤ D} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (w : fst ≫ f = snd ≫ g)
    (h : ∀ k, IsPullback (fst.app k) (snd.app k) (f.app k) (g.app k)) :
    IsPullback fst snd f g :=
  IsPullback.of_isLimit (evaluationJointlyReflectsLimits (PullbackCone.mk fst snd w) fun k =>
    (isLimitMapConePullbackConeEquiv ((evaluation K D).obj k) w).symm (h k).isLimit)

/-- A cartesian square of functors is cartesian after evaluation at every object. -/
theorem isPullback_app_of_isPullback {K : Type*} [Category* K] {D : Type*} [Category* D]
    [HasPullbacks D] {P X Y Z : K ⥤ D} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (k : K) :
    IsPullback (fst.app k) (snd.app k) (f.app k) (g.app k) :=
  h.map ((evaluation K D).obj k)

end CategoryTheory.Limits

namespace AlgebraicGeometry.SpacesOverSpace

universe u

-- The local reducibility below lets rewrites see through the spellings of the points category
-- (`Stack.fibredCategory`, the Grothendieck construction of the presheaf of discrete groupoids
-- `T ⋙ typeToGrpd`), of the category structure of `BasedCategory.ofFunctor`, and of the fibre
-- products of algebraic spaces.
attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor
  AlgebraicSpaces.fiberProduct schemeSpace Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat

/-- A morphism lying over `f` which is strongly cartesian over its own image is strongly cartesian
over `f`. -/
theorem isStronglyCartesian_of_isHomLift {𝒮 : Type*} [Category* 𝒮] {𝒳 : Type*} [Category* 𝒳]
    {p : 𝒳 ⥤ 𝒮} {R R' : 𝒮} {x y : 𝒳} (f : R ⟶ R') (φ : x ⟶ y) [p.IsHomLift f φ]
    (h : p.IsStronglyCartesian (p.map φ) φ) : p.IsStronglyCartesian f φ := by
  obtain rfl := IsHomLift.domain_eq p f φ
  obtain rfl := IsHomLift.codomain_eq p f φ
  obtain rfl := IsHomLift.eq_of_isHomLift p f φ
  exact h

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {P : MorphismProperty (AlgebraicSpaces B S hS)} {T : AlgebraicSpaces B S hS}

section Points

/-- The point `t ∈ T(W)` of `T`, as an object of `𝒮_T`. -/
abbrev pt (W : BigFppfOver B S hS) (t : T.obj.obj (op W)) : (pointsCategory B S hS T).obj :=
  ⟨W, ⟨t⟩⟩

/-- The morphism of points of `T` over `f : W' ⟶ W` from `t'` to `t`, when `t'` restricts `t`. -/
abbrev ptHom {W' W : BigFppfOver B S hS} (f : W' ⟶ W) {t' : T.obj.obj (op W')}
    {t : T.obj.obj (op W)} (h : t' = T.obj.map f.op t) : pt W' t' ⟶ pt W t :=
  ⟨f, Discrete.eqToHom h⟩

/-- The morphism from the point `t` over `W` to a point `a`, over `g : W ⟶ a.base`, when `t`
restricts `a`. -/
abbrev toPoint {W : BigFppfOver B S hS} {a : (pointsCategory B S hS T).obj} (g : W ⟶ a.base)
    {t : T.obj.obj (op W)} (h : t = T.obj.map g.op a.fiber.as) : pt W t ⟶ a :=
  ⟨g, Discrete.eqToHom h⟩

/-- A morphism of points of `T` is determined by its base. -/
theorem hom_ext_base {x y : (pointsCategory B S hS T).obj} (u v : x ⟶ y) (h : u.base = v.base) :
    u = v :=
  PresheafOfCategories.elements_hom_ext (G := T.obj) u v h

end Points

variable (G : pointsCategory B S hS T ⥤ᵇ BasedCategory.ofFunctor (cartesianProjection B S hS P))

section Families

/-- The family of algebraic spaces that `G` attaches to a point of `T`. -/
abbrev fam (a : (pointsCategory B S hS T).obj) :=
  (G.obj a).obj.obj

/-- The family attached to a point lies over the base of the point. -/
theorem fam_right (a : (pointsCategory B S hS T).obj) : (fam G a).right = a.base :=
  G.w_obj a

/-- The structure morphism of the family attached to a point, to the base of the point. -/
abbrev famHom (a : (pointsCategory B S hS T).obj) :
    (fam G a).left.obj ⟶ yoneda.obj a.base :=
  (fam G a).hom ≫ yoneda.map (eqToHom (fam_right G a))

/-- The map of total spaces of the cartesian square `G` attaches to a morphism of points. -/
abbrev famMap {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) :
    (fam G a').left.obj ⟶ (fam G a).left.obj :=
  (G.map u).hom.hom.left.hom

/-- The square `G` attaches to a morphism of points of `T` is cartesian. -/
theorem isPullback_famMap {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) :
    IsPullback (famMap G u) (famHom G a') (famHom G a) (yoneda.map u.base) := by
  have h1 : (pointsCategory B S hS T).p.IsHomLift u.base u :=
    IsHomLift.map (pointsCategory B S hS T).p u
  have h2 : (cartesianProjection B S hS P).IsHomLift u.base (G.map u) :=
    BasedFunctor.preserves_isHomLift G u.base u
  have h3 : (spacesProjection B S hS).IsHomLift u.base (G.map u).hom.hom :=
    IsHomLift.of_fac' (p := spacesProjection B S hS) u.base (G.map u).hom.hom
      (IsHomLift.domain_eq (cartesianProjection B S hS P) u.base (G.map u))
      (IsHomLift.codomain_eq (cartesianProjection B S hS P) u.base (G.map u))
      (IsHomLift.fac' (cartesianProjection B S hS P) u.base (G.map u))
  have h4 : (spacesProjection B S hS).IsStronglyCartesian u.base (G.map u).hom.hom :=
    isStronglyCartesian_of_isHomLift _ _ (G.map u).property
  exact SpacesDescent.isPullback_of_isStronglyCartesian u.base (G.map u).hom.hom
    (fam_right G a') (fam_right G a)

/-- The square `G` attaches to a morphism of points, evaluated at a scheme `W`. -/
theorem isPullback_famMap_app {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a)
    (W : BigFppfOver B S hS) :
    IsPullback ((famMap G u).app (op W)) ((famHom G a').app (op W)) ((famHom G a).app (op W))
      ((yoneda.map u.base).app (op W)) :=
  isPullback_app_of_isPullback (isPullback_famMap G u) (op W)

/-- The map of total spaces attached to a morphism of points lies over the morphism. -/
theorem famHom_famMap_apply {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a)
    {W : BigFppfOver B S hS} (z : (fam G a').left.obj.obj (op W)) :
    (famHom G a).app (op W) ((famMap G u).app (op W) z) = (famHom G a').app (op W) z ≫ u.base := by
  have h := ConcreteCategory.congr_hom (isPullback_famMap_app G u W).w z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- A section of the family at `a'` is determined by its image in the family at `a` and by its
image in the base. -/
theorem ext_famMap {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) {W : BigFppfOver B S hS}
    {z₁ z₂ : (fam G a').left.obj.obj (op W)}
    (h₁ : (famMap G u).app (op W) z₁ = (famMap G u).app (op W) z₂)
    (h₂ : (famHom G a').app (op W) z₁ = (famHom G a').app (op W) z₂) : z₁ = z₂ :=
  Types.ext_of_isPullback (isPullback_famMap_app G u W) h₁ h₂

/-- A section of the family at `a` over `W` whose image in the base factors through the base of
`u : a' ⟶ a` lifts to the family at `a'`. -/
theorem exists_lift {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) {W : BigFppfOver B S hS}
    (y : (fam G a).left.obj.obj (op W)) (g : W ⟶ a'.base)
    (h : (famHom G a).app (op W) y = g ≫ u.base) :
    ∃ z, (famMap G u).app (op W) z = y ∧ (famHom G a').app (op W) z = g :=
  Types.exists_of_isPullback (isPullback_famMap_app G u W) y g h

/-- The lift of a section along a cartesian square of `G`. -/
def lift {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) {W : BigFppfOver B S hS}
    (y : (fam G a).left.obj.obj (op W)) (g : W ⟶ a'.base)
    (h : (famHom G a).app (op W) y = g ≫ u.base) : (fam G a').left.obj.obj (op W) :=
  (exists_lift G u y g h).choose

/-- The lift of `y` is carried to `y` in the family at `a`. -/
theorem famMap_lift {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) {W : BigFppfOver B S hS}
    (y : (fam G a).left.obj.obj (op W)) (g : W ⟶ a'.base)
    (h : (famHom G a).app (op W) y = g ≫ u.base) :
    (famMap G u).app (op W) (lift G u y g h) = y :=
  (exists_lift G u y g h).choose_spec.1

/-- The lift of `y` maps to `g` in the base of `a'`. -/
theorem famHom_lift {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) {W : BigFppfOver B S hS}
    (y : (fam G a).left.obj.obj (op W)) (g : W ⟶ a'.base)
    (h : (famHom G a).app (op W) y = g ≫ u.base) :
    (famHom G a').app (op W) (lift G u y g h) = g :=
  (exists_lift G u y g h).choose_spec.2

/-- The map of total spaces attached to an identity is the identity. -/
theorem famMap_id_apply (a : (pointsCategory B S hS T).obj) {W : BigFppfOver B S hS}
    (z : (fam G a).left.obj.obj (op W)) : (famMap G (𝟙 a)).app (op W) z = z := by
  simp only [famMap, G.map_id]
  rfl

/-- The map of total spaces attached to a composite is the composite. -/
theorem famMap_comp_apply {a'' a' a : (pointsCategory B S hS T).obj} (u : a'' ⟶ a') (v : a' ⟶ a)
    {W : BigFppfOver B S hS} (z : (fam G a'').left.obj.obj (op W)) :
    (famMap G (u ≫ v)).app (op W) z = (famMap G v).app (op W) ((famMap G u).app (op W) z) := by
  simp only [famMap, G.map_comp]
  rfl

/-- The structure morphism of a family is natural in the scheme it is evaluated at. -/
theorem famHom_map_apply (a : (pointsCategory B S hS T).obj) {W W' : BigFppfOver B S hS}
    (f : W' ⟶ W) (z : (fam G a).left.obj.obj (op W)) :
    (famHom G a).app (op W') ((fam G a).left.obj.map f.op z) = f ≫ (famHom G a).app (op W) z := by
  have h := ConcreteCategory.congr_hom ((famHom G a).naturality f.op) z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- The map of total spaces attached to a morphism of points is natural in the scheme. -/
theorem famMap_map_apply {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a)
    {W W' : BigFppfOver B S hS} (f : W' ⟶ W) (z : (fam G a').left.obj.obj (op W)) :
    (famMap G u).app (op W') ((fam G a').left.obj.map f.op z) =
      (fam G a).left.obj.map f.op ((famMap G u).app (op W) z) := by
  have h := ConcreteCategory.congr_hom ((famMap G u).naturality f.op) z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- Two morphisms of points with the same base induce the same map of total spaces. -/
theorem famMap_congr {a' a : (pointsCategory B S hS T).obj} (u v : a' ⟶ a) (h : u.base = v.base)
    {W : BigFppfOver B S hS} (z : (fam G a').left.obj.obj (op W)) :
    (famMap G u).app (op W) z = (famMap G v).app (op W) z := by
  rw [hom_ext_base u v h]

end Families

section Glue

/-- A section over `W` of the family at the point `t` of `T`. -/
abbrev Sec (W : BigFppfOver B S hS) (t : T.obj.obj (op W)) :=
  {z : (fam G (pt W t)).left.obj.obj (op W) // (famHom G (pt W t)).app (op W) z = 𝟙 W}

/-- The sections over `W` of the glued presheaf: a point of `T` over `W` together with a section of
the family at that point. -/
abbrev GlueObj (W : BigFppfOver B S hS) :=
  Σ t : T.obj.obj (op W), Sec G W t

/-- The restriction along `f : W' ⟶ W` of a section of the family at `t` lies over `f` in the
base of the point `t`. -/
theorem restrictSec_cond {W W' : BigFppfOver B S hS} (f : W' ⟶ W) (t : T.obj.obj (op W))
    (x : Sec G W t) :
    (famHom G (pt W t)).app (op W') ((fam G (pt W t)).left.obj.map f.op x.1) =
      𝟙 W' ≫ (ptHom f (rfl : T.obj.map f.op t = T.obj.map f.op t)).base := by
  rw [famHom_map_apply, x.2]
  exact (Category.comp_id f).trans (Category.id_comp f).symm

/-- The restriction of a section of the family at `t` along `f : W' ⟶ W`, as a section of the
family at the restricted point. -/
abbrev restrictSec {W W' : BigFppfOver B S hS} (f : W' ⟶ W) (t : T.obj.obj (op W)) (x : Sec G W t) :
    Sec G W' (T.obj.map f.op t) :=
  ⟨lift G (ptHom f rfl) ((fam G (pt W t)).left.obj.map f.op x.1) (𝟙 W')
      (restrictSec_cond G f t x),
    famHom_lift G _ _ _ _⟩

/-- The restriction along `f` of a section `x` of the family at `t` is carried, by any morphism of
points over `f`, to the restriction of `x` in the family at `t`. -/
theorem famMap_restrictSec {W W' : BigFppfOver B S hS} (f : W' ⟶ W) (t : T.obj.obj (op W))
    (x : Sec G W t) (u : pt W' (T.obj.map f.op t) ⟶ pt W t) (hu : u.base = f) :
    (famMap G u).app (op W') (restrictSec G f t x).1 = (fam G (pt W t)).left.obj.map f.op x.1 := by
  rw [famMap_congr G u (ptHom f rfl) hu]
  exact famMap_lift G (ptHom f rfl) _ (𝟙 W') (restrictSec_cond G f t x)

/-- Two sections of the glued presheaf agree when a morphism of points over the identity carries
one to the other. -/
theorem glue_ext {W : BigFppfOver B S hS} {t₁ t₂ : T.obj.obj (op W)} (e : pt W t₁ ⟶ pt W t₂)
    (he : e.base = 𝟙 W) (x₁ : Sec G W t₁) (x₂ : Sec G W t₂)
    (hx : (famMap G e).app (op W) x₁.1 = x₂.1) :
    (⟨t₁, x₁⟩ : GlueObj G W) = ⟨t₂, x₂⟩ := by
  have ht : t₁ = t₂ := by
    simpa only [he, op_id, FunctorToTypes.map_id_apply] using fiber_as_eq e
  subst ht
  rw [hom_ext_base e (𝟙 _) he, famMap_id_apply] at hx
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hx))

/-- The presheaf glued from the families `G` attaches to the points of `T`. -/
def glue : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj W := GlueObj G W.unop
  map {W W'} φ := ↾fun x => ⟨T.obj.map φ.unop.op x.1, restrictSec G φ.unop x.1 x.2⟩
  map_id W := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, x⟩
    refine glue_ext G (ptHom (𝟙 W).unop rfl) rfl (restrictSec G (𝟙 W).unop t x) x ?_
    rw [famMap_restrictSec G _ _ _ _ rfl]
    exact FunctorToTypes.map_id_apply _ _
  map_comp {W W' W''} φ₁ φ₂ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, x⟩
    have h : T.obj.map (φ₁ ≫ φ₂).unop.op t =
        T.obj.map (𝟙 W''.unop).op (T.obj.map φ₂.unop.op (T.obj.map φ₁.unop.op t)) := by
      rw [op_id, FunctorToTypes.map_id_apply, ← FunctorToTypes.map_comp_apply]
      rfl
    refine glue_ext G (ptHom (𝟙 W''.unop) h) rfl (restrictSec G (φ₁ ≫ φ₂).unop t x)
      (restrictSec G φ₂.unop _ (restrictSec G φ₁.unop t x)) ?_
    apply ext_famMap G (ptHom φ₂.unop rfl)
    · rw [← famMap_comp_apply,
        famMap_restrictSec G φ₂.unop _ (restrictSec G φ₁.unop t x) (ptHom φ₂.unop rfl) rfl]
      apply ext_famMap G (ptHom φ₁.unop rfl)
      · rw [← famMap_comp_apply, famMap_map_apply,
          famMap_restrictSec G φ₁.unop t x (ptHom φ₁.unop rfl) rfl,
          famMap_restrictSec G (φ₁ ≫ φ₂).unop t x
            ((ptHom (𝟙 W''.unop) h ≫ ptHom φ₂.unop rfl) ≫ ptHom φ₁.unop rfl) (by
              change (𝟙 _ ≫ φ₂.unop) ≫ φ₁.unop = (φ₁ ≫ φ₂).unop
              rw [Category.id_comp, unop_comp]),
          ← FunctorToTypes.map_comp_apply]
        rfl
      · rw [famHom_famMap_apply, famHom_map_apply, (restrictSec G (φ₁ ≫ φ₂).unop t x).2,
          (restrictSec G φ₁.unop t x).2]
        change 𝟙 _ ≫ (𝟙 _ ≫ φ₂.unop) = φ₂.unop ≫ 𝟙 _
        rw [Category.id_comp, Category.id_comp, Category.comp_id]
    · rw [famHom_famMap_apply, (restrictSec G (φ₁ ≫ φ₂).unop t x).2,
        (restrictSec G φ₂.unop _ _).2]
      exact Category.id_comp _

/-- The projection of the glued presheaf to `T`. -/
def glueToBase : glue G ⟶ T.obj where
  app _ := ↾fun x => x.1
  naturality _ _ _ := rfl

/-- The section of the glued presheaf named by a section `y` over `W` of the family at a point
`a`: the point of `T` it lies over, and `y` read as a section of the family at that point. -/
abbrev famToGlueApp (a : (pointsCategory B S hS T).obj) {W : BigFppfOver B S hS}
    (y : (fam G a).left.obj.obj (op W)) : GlueObj G W :=
  ⟨T.obj.map ((famHom G a).app (op W) y).op a.fiber.as,
    ⟨lift G (toPoint ((famHom G a).app (op W) y) rfl) y (𝟙 W) (Category.id_comp _).symm,
      famHom_lift G _ _ _ _⟩⟩

/-- A section of the glued presheaf named by `y` gives back `y` along any morphism of points to `a`
over the image of `y` in the base. -/
theorem famMap_famToGlueApp (a : (pointsCategory B S hS T).obj) {W : BigFppfOver B S hS}
    (y : (fam G a).left.obj.obj (op W)) (z : GlueObj G W) (hz : famToGlueApp G a y = z)
    (v : pt W z.1 ⟶ a) (hv : v.base = (famHom G a).app (op W) y) :
    (famMap G v).app (op W) z.2.1 = y := by
  subst hz
  rw [famMap_congr G v (toPoint ((famHom G a).app (op W) y) rfl) hv]
  exact famMap_lift G (toPoint _ rfl) y (𝟙 W) (Category.id_comp _).symm

/-- The map from the family at a point `a` to the glued presheaf. -/
def famToGlue (a : (pointsCategory B S hS T).obj) : (fam G a).left.obj ⟶ glue G where
  app W := ↾fun y => famToGlueApp G a y
  naturality {W W'} φ := by
    apply ConcreteCategory.hom_ext
    intro y
    change famToGlueApp G a ((fam G a).left.obj.map φ.unop.op y) =
      ⟨T.obj.map φ.unop.op (famToGlueApp G a y).1,
        restrictSec G φ.unop (famToGlueApp G a y).1 (famToGlueApp G a y).2⟩
    set g := (famHom G a).app (op W.unop) y with hg
    have hg' : (famHom G a).app (op W'.unop) ((fam G a).left.obj.map φ.unop.op y) =
        φ.unop ≫ g := famHom_map_apply G a φ.unop y
    have h : T.obj.map ((famHom G a).app (op W'.unop) ((fam G a).left.obj.map φ.unop.op y)).op
        a.fiber.as =
          T.obj.map (𝟙 W'.unop).op (T.obj.map φ.unop.op (T.obj.map g.op a.fiber.as)) := by
      rw [hg', op_id, FunctorToTypes.map_id_apply, ← FunctorToTypes.map_comp_apply, op_comp]
    refine glue_ext G (ptHom (𝟙 W'.unop) h) rfl _ _ ?_
    apply ext_famMap G (ptHom φ.unop (rfl : T.obj.map φ.unop.op (T.obj.map g.op a.fiber.as) = _))
    · rw [← famMap_comp_apply, famMap_restrictSec G φ.unop _ _ (ptHom φ.unop rfl) rfl]
      apply ext_famMap G (toPoint g (rfl : T.obj.map g.op a.fiber.as = _))
      · rw [← famMap_comp_apply, famMap_map_apply,
          famMap_famToGlueApp G a y _ rfl (toPoint g rfl) rfl,
          famMap_famToGlueApp G a _ _ rfl _ (by
            change (𝟙 _ ≫ φ.unop) ≫ g = _
            rw [Category.id_comp, hg'])]
      · refine (famHom_famMap_apply G _ _).trans ?_
        refine Eq.trans ?_ (famHom_map_apply G _ φ.unop _).symm
        rw [famHom_lift, famHom_lift]
        change 𝟙 _ ≫ (𝟙 _ ≫ φ.unop) = φ.unop ≫ 𝟙 _
        rw [Category.id_comp, Category.id_comp, Category.comp_id]
    · rw [famHom_famMap_apply, (famToGlueApp G a _).2.2, (restrictSec G φ.unop _ _).2]
      exact Category.id_comp _

/-- The square of the map from the family at `a` to the glued presheaf commutes. -/
theorem famToGlue_comp_glueToBase (a : (pointsCategory B S hS T).obj) :
    famToGlue G a ≫ glueToBase G = famHom G a ≫ (pointMap a).hom := by
  ext W y
  show T.obj.map ((famHom G a).app W y).op a.fiber.as =
    (yonedaEquiv.symm a.fiber.as).app W ((famHom G a).app W y)
  rw [yonedaEquiv_symm_app_apply]
  rfl

/-- **The glued presheaf restricts to the families.** For every point `a = (U, t)` of `T`, the
family `G(U, t)` is the base change of the glued presheaf along `t : U ⟶ T`. -/
theorem isPullback_famToGlue (a : (pointsCategory B S hS T).obj) :
    IsPullback (famHom G a) (famToGlue G a) (pointMap a).hom (glueToBase G) := by
  refine isPullback_of_isPullback_app (famToGlue_comp_glueToBase G a).symm fun W => ?_
  rw [Types.isPullback_iff]
  refine ⟨congr_app (famToGlue_comp_glueToBase G a).symm W, ?_, ?_⟩
  · rintro y₁ y₂ ⟨h₁, h₂⟩
    have hz₁ : (famToGlueApp G a y₁).1 =
        T.obj.map ((famHom G a).app W y₁).op a.fiber.as := rfl
    let v : pt W.unop (famToGlueApp G a y₁).1 ⟶ a := toPoint ((famHom G a).app W y₁) hz₁
    have e₁ := famMap_famToGlueApp G a y₁ _ rfl v rfl
    have e₂ := famMap_famToGlueApp G a y₂ (famToGlueApp G a y₁) h₂.symm v h₁
    exact e₁.symm.trans e₂
  · intro g z hz
    have hz' : z.1 = T.obj.map g.op a.fiber.as := by
      rw [← yonedaEquiv_symm_app_apply]
      exact hz.symm
    let v : pt W.unop z.1 ⟶ a := toPoint g hz'
    refine ⟨(famMap G v).app W z.2.1, ?_, ?_⟩
    · rw [famHom_famMap_apply, z.2.2]
      exact Category.id_comp g
    · obtain ⟨t, x⟩ := z
      have hg : (famHom G a).app W ((famMap G v).app W x.1) = g := by
        rw [famHom_famMap_apply, x.2]
        exact Category.id_comp g
      have h : T.obj.map ((famHom G a).app W ((famMap G v).app W x.1)).op a.fiber.as =
          T.obj.map (𝟙 W.unop).op t := by
        rw [hg, op_id, FunctorToTypes.map_id_apply]
        exact hz'.symm
      show famToGlueApp G a ((famMap G v).app W x.1) = ⟨t, x⟩
      refine glue_ext G (ptHom (𝟙 W.unop) h) rfl _ _ ?_
      apply ext_famMap G v
      · rw [← famMap_comp_apply]
        exact famMap_famToGlueApp G a _ _ rfl _ (by
          show 𝟙 _ ≫ g = _
          rw [Category.id_comp, hg])
      · rw [famHom_famMap_apply, (famToGlueApp G a _).2.2, x.2]
        exact Category.id_comp _

end Glue

end AlgebraicGeometry.SpacesOverSpace

end
