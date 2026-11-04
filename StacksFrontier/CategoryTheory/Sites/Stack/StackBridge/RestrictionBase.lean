module

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary

/-!
# The base morphism of a canonical restriction

A `CategoryTheory.Functor.DescentDatum` states its cocycle condition through auxiliary morphisms
over the triple overlap, each required only to be a *canonical restriction*
(`CategoryTheory.Functor.IsRestrictionOf`) of one of the gluing isomorphisms. Such a requirement
does not say outright that the auxiliary morphism lies over an identity; what it does say is proved
here, and it is the seed from which that conclusion is drawn in
`CategoryTheory.Functor.DescentDatum.isHomLift_id_αij`.

## Main results

* `CategoryTheory.Functor.comp_eq_of_isRestrictionOf`: if `β` is the canonical restriction of a
  fibre morphism `α` along `g`, and `β` lies over `e`, then `e ≫ g = g`. This leaves `e` free
  whenever `g` is not a monomorphism, which is why the genuine fibre products of Stacks 02ZI are
  needed to pin it down.
* `CategoryTheory.Functor.fibreHom_of_isHomLift_id`, the converse reading: a morphism lying over an
  identity is a morphism of the fibre.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered]

omit [p.IsFibered] in
/-- Every morphism of `𝒳` lies over some morphism of the base, once the images of its endpoints
are named. -/
lemma exists_isHomLift_base {R S : 𝒞} {a b : 𝒳} (ha : p.obj a = R) (hb : p.obj b = S) (φ : a ⟶ b) :
    ∃ n : R ⟶ S, p.IsHomLift n φ :=
  ⟨eqToHom ha.symm ≫ p.map φ ≫ eqToHom hb, IsHomLift.of_fac' p _ φ ha hb (by simp)⟩

omit [p.IsFibered] in
/-- A morphism lying over an identity is a morphism of the fibre. -/
lemma fibreHom_of_isHomLift_id {V : 𝒞} {a b : 𝒳} (ha : p.obj a = V) (hb : p.obj b = V)
    {φ : a ⟶ b} (h : p.IsHomLift (𝟙 V) φ) : FibreHom p a b ha hb φ := by
  refine IsHomLift.of_fac' p _ φ rfl rfl ?_
  simpa using IsHomLift.fac' p (𝟙 V) φ

/-- **The base morphism of a canonical restriction fixes the morphism it is taken along.** If `β`
is the canonical restriction of a fibre morphism `α` along `g`, and `β` lies over `e`, then
`e ≫ g = g`. -/
lemma comp_eq_of_isRestrictionOf {Ux Uy V W : 𝒞} {g : W ⟶ V} {fx : V ⟶ Ux} {fy : V ⟶ Uy}
    {mx : W ⟶ Ux} {my : W ⟶ Uy} (hmx : mx = g ≫ fx) (hmy : my = g ≫ fy)
    {x y : 𝒳} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    (xrW : Restriction p mx x hx) (yrW : Restriction p my y hy)
    {α : xr.pt ⟶ yr.pt} (hα : FibreHom p xr.pt yr.pt xr.hpt yr.hpt α)
    {β : xrW.pt ⟶ yrW.pt} {e : W ⟶ W} (he : p.IsHomLift e β)
    (h : IsRestrictionOf p g hmx hmy xr yr xrW yrW α β) : e ≫ g = g := by
  have hcy := Restriction.isHomLift_compTo g fy hmy yr yrW
  have hcx := Restriction.isHomLift_compTo g fx hmx xr xrW
  have hαl : p.IsHomLift (𝟙 V) α := (fibreHomMk hα).2
  have h1 : p.IsHomLift (e ≫ g) (β ≫ Restriction.compTo p g fy hmy yr yrW) := inferInstance
  have h2 : p.IsHomLift g (Restriction.compTo p g fx hmx xr xrW ≫ α) :=
    isHomLift_of_eq (n := g ≫ 𝟙 V) inferInstance (by simp)
  rw [h] at h1
  exact eq_of_isHomLift_of_isHomLift h1 h2

end Functor

end CategoryTheory
