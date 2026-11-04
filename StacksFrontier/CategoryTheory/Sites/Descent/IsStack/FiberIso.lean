module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiber

/-!
# Isomorphisms of a fibre, and comparison of cartesian lifts

An isomorphism of a fibre is an isomorphism of `𝒳` lying over an identity
(`CategoryTheory.Functor.Fiber.isoMk`), and two cartesian lifts of one morphism at one object are
canonically isomorphic in the fibre (`CategoryTheory.Functor.fiberIsoOfCartesian`). Two morphisms
of a fibre into the domain of a cartesian morphism agree as soon as their composites with it do
(`CategoryTheory.Functor.fiber_hom_ext_of_cartesian`).

## Main definitions

* `CategoryTheory.Functor.Fiber.isoMk`, an isomorphism of `𝒳` over an identity read as an
  isomorphism of the fibre;
* `CategoryTheory.Functor.fiberIsoOfCartesian`, the canonical comparison of two cartesian lifts.
-/

@[expose] public section

-- Needed by `fiberIsoOfCartesian_hom_fac` and `fiberIsoOfCartesian_inv_fac` only, and at
-- statement level: `@[reassoc]` reassociates their conclusions, which means identifying
-- `Fiber.fiberInclusion.obj z'` with `z'.1`, and that holds only at default transparency.
-- Without this option the generated `..._assoc` lemmas carry a differently bracketed statement.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable {p : 𝒳 ⥤ 𝒮}

/-- An isomorphism of the fibre of `p` over `S` from an isomorphism of `𝒳` lying over `𝟙 S`. -/
def Fiber.isoMk {S : 𝒮} {a b : p.Fiber S} (e : a.1 ≅ b.1) (he : p.IsHomLift (𝟙 S) e.hom) :
    a ≅ b :=
  have := he
  { hom := ⟨e.hom, he⟩
    inv := ⟨e.inv, inferInstance⟩
    hom_inv_id := Fiber.hom_ext e.hom_inv_id
    inv_hom_id := Fiber.hom_ext e.inv_hom_id }

/-- The forward direction of `Fiber.isoMk e he`, seen in `𝒳`, is `e.hom`. -/
@[simp] lemma Fiber.fiberInclusion_map_isoMk_hom {S : 𝒮} {a b : p.Fiber S} (e : a.1 ≅ b.1)
    (he : p.IsHomLift (𝟙 S) e.hom) :
    Fiber.fiberInclusion.map (Fiber.isoMk e he).hom = e.hom := rfl

/-- The inverse of `Fiber.isoMk e he`, seen in `𝒳`, is `e.inv`. -/
@[simp] lemma Fiber.fiberInclusion_map_isoMk_inv {S : 𝒮} {a b : p.Fiber S} (e : a.1 ≅ b.1)
    (he : p.IsHomLift (𝟙 S) e.hom) :
    Fiber.fiberInclusion.map (Fiber.isoMk e he).inv = e.inv := rfl

/-- An idempotent automorphism of a fibre is the identity. -/
lemma eq_id_of_comp_self_eq {S : 𝒮} {z : p.Fiber S} (e : z ≅ z) (h : e.hom ≫ e.hom = e.hom) :
    e.hom = 𝟙 z := by
  rwa [← cancel_mono e.hom, Category.id_comp]

/-- Two parallel morphisms of a fibre agree as soon as their composites with one cartesian
morphism out of their common target agree. -/
lemma fiber_hom_ext_of_cartesian {Z W : 𝒮} (b : Z ⟶ W) {a : 𝒳} {z z' : p.Fiber Z}
    (φ' : z'.1 ⟶ a) (hφ' : p.IsCartesian b φ') (ψ ψ' : z ⟶ z')
    (h : Fiber.fiberInclusion.map ψ ≫ φ' = Fiber.fiberInclusion.map ψ' ≫ φ') : ψ = ψ' :=
  have := hφ'
  Fiber.hom_ext (IsCartesian.ext p b φ' _ _ h)

/-- Two objects of the fibre over `Z` carrying cartesian morphisms over one and the same
`b : Z ⟶ W` into one and the same object of `𝒳` are canonically isomorphic in the fibre. -/
noncomputable def fiberIsoOfCartesian {Z W : 𝒮} (b : Z ⟶ W) {a : 𝒳}
    {z z' : p.Fiber Z} (φ : z.1 ⟶ a) (φ' : z'.1 ⟶ a)
    (hφ : p.IsCartesian b φ) (hφ' : p.IsCartesian b φ') : z ≅ z' :=
  have := hφ
  have := hφ'
  Fiber.isoMk (IsCartesian.domainUniqueUpToIso p b φ' φ) inferInstance

/-- The comparison of two cartesian lifts of `b` factors the first lift through the second. -/
@[reassoc (attr := simp)]
lemma fiberIsoOfCartesian_hom_fac {Z W : 𝒮} (b : Z ⟶ W) {a : 𝒳}
    {z z' : p.Fiber Z} (φ : z.1 ⟶ a) (φ' : z'.1 ⟶ a)
    (hφ : p.IsCartesian b φ) (hφ' : p.IsCartesian b φ') :
    Fiber.fiberInclusion.map (fiberIsoOfCartesian b φ φ' hφ hφ').hom ≫ φ' = φ :=
  have := hφ
  have := hφ'
  IsCartesian.fac p b φ' φ

/-- Comparing a cartesian lift of `b` with itself gives the identity. -/
@[simp]
lemma fiberIsoOfCartesian_self {Z W : 𝒮} (b : Z ⟶ W) {a : 𝒳} {z : p.Fiber Z} (φ : z.1 ⟶ a)
    (hφ : p.IsCartesian b φ) : (fiberIsoOfCartesian b φ φ hφ hφ).hom = 𝟙 z :=
  have := hφ
  Fiber.hom_ext (IsCartesian.map_self p b φ)

/-- The comparison of two cartesian lifts of `b` factors, in the inverse direction, the second
lift through the first. -/
@[reassoc (attr := simp)]
lemma fiberIsoOfCartesian_inv_fac {Z W : 𝒮} (b : Z ⟶ W) {a : 𝒳}
    {z z' : p.Fiber Z} (φ : z.1 ⟶ a) (φ' : z'.1 ⟶ a)
    (hφ : p.IsCartesian b φ) (hφ' : p.IsCartesian b φ') :
    Fiber.fiberInclusion.map (fiberIsoOfCartesian b φ φ' hφ hφ').inv ≫ φ = φ' :=
  have := hφ
  have := hφ'
  IsCartesian.fac p b φ φ'

end Functor

end CategoryTheory
