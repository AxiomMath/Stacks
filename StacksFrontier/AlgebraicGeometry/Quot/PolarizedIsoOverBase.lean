module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional

/-!
# Isomorphisms of polarized families over the identity of the base, and their corepresentability

An isomorphism of the fibre of `𝒫olarized` over a scheme is a morphism of polarized families whose
base map is the identity (`AlgebraicGeometry.PolarizedFamily.IsoOverBase`). For two polarized
families `a`, `b` over an affine scheme `V`, the isomorphisms between their pullbacks to affine
test schemes `T ⟶ V` are *corepresented* by a ring `H` over `Γ(V, 𝒪_V)` when they correspond,
naturally in the test scheme, to the ring homomorphisms `H ⟶ Γ(T, 𝒪_T)` over `Γ(V, 𝒪_V)`
(`AlgebraicGeometry.PolarizedFamily.IsIsoOverBaseCorepresented`); equivalently, the isomorphism
functor is the affine scheme `Spec H` over `V`.

## Main definitions

* `AlgebraicGeometry.PolarizedFamily.IsoOverBase`: the morphisms of polarized families whose base
  map is the identity, read through an equality of the bases.
* `AlgebraicGeometry.PolarizedFamily.IsIsoOverBaseCorepresented`: the assertion that the
  isomorphisms between pullbacks of two polarized families correspond, naturally in the test datum,
  to the ring homomorphisms out of a given ring over the ring of functions on the base.

## References

* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- **Isomorphisms of polarized families lying over the identity of a common base**: the
morphisms whose base map is the identity, read through the equality of the bases. -/
def IsoOverBase (x y : PolarizedFamily B) (h : x.base = y.base) : Type u :=
  {φ : x ⟶ y // φ.baseMap = eqToHom h}

/-- **The isomorphisms between pullbacks of `a` and `b` are corepresented by `H`**: for every
pair of polarized families `x`, `y` over a common affine test base with morphisms `cx : x ⟶ a`,
`cy : y ⟶ b` over the same base map, the isomorphisms `x ≅ y` over the identity correspond to the
ring homomorphisms `H ⟶ Γ(x.base)` over `Γ(a.base)` (through `ι` and the base map), naturally in
the test datum. -/
def IsIsoOverBaseCorepresented (a b : PolarizedFamily B) (hab : a.base = b.base) (H : Type u)
    [CommRing H] (ι : Γ(B.inclusion.obj a.base, ⊤) →+* H) : Prop :=
  ∃ e : ∀ (x y : PolarizedFamily B) (hxy : x.base = y.base)
      (_ : IsAffine (B.inclusion.obj x.base)) (cx : x ⟶ a) (cy : y ⟶ b)
      (_ : cx.baseMap ≫ eqToHom hab = eqToHom hxy ≫ cy.baseMap),
      IsoOverBase x y hxy ≃
        {f : H →+* Γ(B.inclusion.obj x.base, ⊤) //
          f.comp ι = (B.inclusion.map cx.baseMap).appTop.hom},
    ∀ (x y : PolarizedFamily B) (hxy : x.base = y.base)
      (hx : IsAffine (B.inclusion.obj x.base)) (cx : x ⟶ a) (cy : y ⟶ b)
      (hc : cx.baseMap ≫ eqToHom hab = eqToHom hxy ≫ cy.baseMap)
      (x' y' : PolarizedFamily B) (hxy' : x'.base = y'.base)
      (hx' : IsAffine (B.inclusion.obj x'.base)) (rx : x' ⟶ x) (ry : y' ⟶ y)
      (hr : rx.baseMap ≫ eqToHom hxy = eqToHom hxy' ≫ ry.baseMap)
      (φ' : IsoOverBase x' y' hxy') (φ : IsoOverBase x y hxy) (_ : φ'.1 ≫ ry = rx ≫ φ.1),
      (e x' y' hxy' hx' (rx ≫ cx) (ry ≫ cy) (by
          simp only [PolarizedFamily.comp_baseMap, Category.assoc, hc]
          rw [← Category.assoc, hr, Category.assoc]) φ').1 =
        (B.inclusion.map rx.baseMap).appTop.hom.comp (e x y hxy hx cx cy hc φ).1

end AlgebraicGeometry.PolarizedFamily

end
