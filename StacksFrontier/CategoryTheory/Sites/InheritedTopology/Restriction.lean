module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-! # Restrictions of objects of a fibred category

For a structure functor `p : 𝒮 ⥤ 𝒞`, an object `x` of `𝒮` over `U` and a base morphism
`f : V ⟶ U`, a *restriction* of `x` along `f` is a choice of strongly cartesian lift
`f^* x ⟶ x` of `f`. Two restrictions of the same object are compared by the canonical
morphism coming from the universal property of a strongly cartesian arrow.

## Main definitions

* `CategoryTheory.Functor.Restriction`: a chosen strongly cartesian lift `f^* x ⟶ x`.
* `CategoryTheory.Functor.Restriction.compTo`: the canonical comparison of two
  restrictions of the same object along composable base morphisms.
* `CategoryTheory.Functor.FibreHom`: a morphism of the fibre category over `U`.
* `CategoryTheory.Functor.IsRestrictionOf`: the relation "`β` is the canonical
  restriction of the fibre morphism `α`".
-/

@[expose] public section

open CategoryTheory

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/-- A *restriction* of `x` along `f : V ⟶ U`, where `x` lies over `U`: a choice of
strongly cartesian lift `f^* x ⟶ x` of `f`, with source lying over `V`. -/
structure Restriction (p : 𝒮 ⥤ 𝒞)
    {V U : 𝒞} (f : V ⟶ U) (x : 𝒮) (hx : p.obj x = U) where
  /-- The pullback object `f^* x`. -/
  pt : 𝒮
  /-- It lies over `V`. -/
  hpt : p.obj pt = V
  /-- The cartesian morphism `f^* x ⟶ x`. -/
  hom : pt ⟶ x
  /-- It lies over `f`. -/
  isHomLift : p.IsHomLift (eqToHom hpt ≫ f ≫ eqToHom hx.symm) hom
  /-- It is strongly cartesian. -/
  isCart : p.IsStronglyCartesian (eqToHom hpt ≫ f ≫ eqToHom hx.symm) hom

attribute [instance] Restriction.isHomLift Restriction.isCart

/-- The canonical comparison `xrW.pt ⟶ xr.pt` over `g : W ⟶ V` between a restriction
`xrW` of `x` along `h : W ⟶ U` and a restriction `xr` of `x` along `f : V ⟶ U`, where
`h = g ≫ f`: the unique morphism over `g` satisfying `Restriction.compTo_hom`. -/
noncomputable def Restriction.compTo (p : 𝒮 ⥤ 𝒞) {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U)
    {h : W ⟶ U} (hh : h = g ≫ f)
    {x : 𝒮} {hx : p.obj x = U}
    (xr : Restriction p f x hx) (xrW : Restriction p h x hx) :
    xrW.pt ⟶ xr.pt := by
  haveI := xr.isCart
  haveI : p.IsHomLift ((eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
      (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)) xrW.hom := by
    have hlift := xrW.isHomLift
    have e : (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
        (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)
        = eqToHom xrW.hpt ≫ h ≫ eqToHom hx.symm := by subst hh; simp
    rw [e]; exact hlift
  exact Functor.IsStronglyCartesian.map p (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom
    (g := eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) rfl xrW.hom

/-- The canonical comparison `Restriction.compTo` factors `xrW.hom` through `xr.hom`. -/
theorem Restriction.compTo_hom (p : 𝒮 ⥤ 𝒞) {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U)
    {h : W ⟶ U} (hh : h = g ≫ f)
    {x : 𝒮} {hx : p.obj x = U}
    (xr : Restriction p f x hx) (xrW : Restriction p h x hx) :
    Restriction.compTo p g f hh xr xrW ≫ xr.hom = xrW.hom := by
  have : p.IsHomLift ((eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
      (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)) xrW.hom := by
    have e : (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
        (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)
        = eqToHom xrW.hpt ≫ h ≫ eqToHom hx.symm := by subst hh; simp
    rw [e]
    exact xrW.isHomLift
  exact Functor.IsStronglyCartesian.fac p _ xr.hom _ xrW.hom

/-- The restriction of `x` along the identity of `U`, with `pt = x` and `hom = 𝟙 x`. -/
@[implicit_reducible]
def Restriction.id (p : 𝒮 ⥤ 𝒞) {U : 𝒞} (x : 𝒮) (hx : p.obj x = U) :
    Restriction p (𝟙 U) x hx where
  pt := x
  hpt := hx
  hom := 𝟙 x
  isHomLift := by
    have e : eqToHom hx ≫ 𝟙 U ≫ eqToHom hx.symm = p.map (𝟙 x) := by simp
    rw [e]; exact CategoryTheory.IsHomLift.map p (𝟙 x)
  isCart := by
    have e : eqToHom hx ≫ 𝟙 U ≫ eqToHom hx.symm = p.map (𝟙 x) := by simp
    rw [e]
    have : p.IsHomLift (p.map (𝟙 x)) (Iso.refl x).hom := CategoryTheory.IsHomLift.map p (𝟙 x)
    exact Functor.IsStronglyCartesian.of_iso (p := p) (f := p.map (𝟙 x)) (Iso.refl x)

/-- A morphism of the fibre category over `U`: a morphism of `𝒮` between two objects
lying over `U` which itself lies over `𝟙 U`. -/
abbrev FibreHom (p : 𝒮 ⥤ 𝒞) {U : 𝒞}
    (a b : 𝒮) (ha : p.obj a = U) (hb : p.obj b = U) (φ : a ⟶ b) : Prop :=
  p.IsHomLift (eqToHom ha ≫ eqToHom hb.symm) φ

/-- The relation "`β` is the canonical restriction of the fibre morphism `α` along
`g : W ⟶ V`". Here `α : xr.pt ⟶ yr.pt` is a fibre morphism over `V` between a
restriction of `x` along `fx : V ⟶ Ux` and a restriction of `y` along `fy : V ⟶ Uy`,
and `β : xrW.pt ⟶ yrW.pt` is a fibre morphism over `W`. The condition is commutativity of the
square of canonical comparisons. -/
abbrev IsRestrictionOf (p : 𝒮 ⥤ 𝒞) {W V Ux Uy : 𝒞} (g : W ⟶ V)
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy}
    (hfx : hx_ = g ≫ fx) (hfy : hy_ = g ≫ fy)
    {x y : 𝒮} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    (xrW : Restriction p hx_ x hx) (yrW : Restriction p hy_ y hy)
    (α : xr.pt ⟶ yr.pt) (β : xrW.pt ⟶ yrW.pt) : Prop :=
  β ≫ Restriction.compTo p g fy hfy yr yrW = Restriction.compTo p g fx hfx xr xrW ≫ α

/-- In a category fibred in groupoids, every object over `U` admits a restriction along
every base morphism `g : W ⟶ U`. -/
noncomputable def Restriction.ofIsFiberedInGroupoids (p : 𝒮 ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) {W U : 𝒞} (g : W ⟶ U) (x : 𝒮) (hx : p.obj x = U) :
    Restriction p g x hx := by
  have hex := hp.exists_lift (g ≫ eqToHom hx.symm) x rfl
  let y := hex.choose
  let φ := hex.choose_spec.choose
  have hφ : p.IsHomLift (g ≫ eqToHom hx.symm) φ := hex.choose_spec.choose_spec
  haveI := hφ
  have hy : p.obj y = W := CategoryTheory.IsHomLift.domain_eq p (g ≫ eqToHom hx.symm) φ
  refine
    { pt := y
      hpt := hy
      hom := φ
      isHomLift := ?_
      isCart := ?_ }
  · refine CategoryTheory.IsHomLift.of_commsq p _ φ rfl rfl ?_
    have hmap : p.map φ = eqToHom hy ≫ (g ≫ eqToHom hx.symm) ≫
        eqToHom (CategoryTheory.IsHomLift.codomain_eq p (g ≫ eqToHom hx.symm) φ).symm := by
      simpa using CategoryTheory.IsHomLift.fac' p (g ≫ eqToHom hx.symm) φ
    rw [hmap]; simp
  · have h := hp.isStronglyCartesian φ
    have hmap : p.map φ = eqToHom hy ≫ g ≫ eqToHom hx.symm := by
      have := CategoryTheory.IsHomLift.fac' p (g ≫ eqToHom hx.symm) φ
      simp only [Category.assoc] at this ⊢
      simpa [eqToHom_trans] using this
    rwa [hmap] at h

/-- An endomorphism of an object of a category fibred in groupoids lying over an
identity of the base is an isomorphism. -/
theorem isIso_of_isHomLift_id (p : 𝒮 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids)
    {a : 𝒮} (b : a ⟶ a) (hb : p.IsHomLift (𝟙 (p.obj a)) b) : IsIso b := by
  have : p.IsStronglyCartesian (𝟙 (p.obj a)) b :=
    (CategoryTheory.IsHomLift.eq_of_isHomLift p (𝟙 (p.obj a)) b) ▸ hp.isStronglyCartesian b
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p.obj a)) b

end CategoryTheory.Functor
