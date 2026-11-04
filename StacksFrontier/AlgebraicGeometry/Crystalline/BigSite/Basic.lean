module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.ClosedFiber
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.RingTheory.DividedPowers.Extend

/-!
# The big crystalline category of a scheme

Fix a prime `p`, a divided power scheme `(S, I, γ)` over `ℤ_(p)`, and a scheme `X` over the closed
fibre `S₀ = V(I)` on which `p` is locally nilpotent.  A *divided power thickening of `X` relative
to `(S, I, γ)`* is a divided power thickening `U ↪ T` over `(S, I, γ)` together with an
`S`-morphism `U ⟶ X`; these objects and the commuting maps between them form the big crystalline
category `CRIS(X/S)`.  Forgetting the ambient thickening and keeping only `U ⟶ X` is a functor
`CRIS(X/S) ⥤ Sch/X`.

A divided power thickening of schemes is a thickening `U ↪ T` of schemes, with `T` a divided power
scheme, whose defining ideal is the divided power ideal of `T`.  The identification of the two
ideal sheaves is imposed on affine opens, where an ideal sheaf datum lives; over an arbitrary open
it follows, and `Crystalline.SchemeThickening.immersion_app_eq_zero_of_mem` records that the
immersion kills every section of the divided power ideal.

## Main definitions

* `Crystalline.SchemeThickening` — a divided power thickening of schemes, [Stacks, Tag 07I4].
* `Crystalline.GlobalCrystallineSituation` — the standing global crystalline data,
  [Stacks, Tag 07MF].
* `Crystalline.GlobalCrystallineSituation.Thickening` — an object of `CRIS(X/S)`, and
  `.Thickening.Hom` a morphism of such, [Stacks, Tag 07I6].
* `Crystalline.GlobalCrystallineSituation.forget` — the functor `CRIS(X/S) ⥤ Sch/X`,
  [Stacks, Tag 07I7].

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.instCategory` — `CRIS(X/S)` is a category.
* `Crystalline.SchemeThickening.immersion_app_eq_zero_of_mem` — over any open of the ambient
  scheme, the immersion of a divided power thickening kills the divided power ideal.

## Implementation notes

The closed fibre `S₀ = V(I)` is `Crystalline.DividedPowerScheme.closedFiber`, the canonical
presentation of the closed fibre built from Mathlib's `IdealSheafData.subscheme`, and the
structure morphism `U ⟶ S` of an object is the composite through it.  Morphisms preserve the
immersion, the divided power map on the ambient scheme and the map to `X`; no Cartesian condition
is imposed on the underlying square.  Keeping `U` and its immersion as fields of
`SchemeThickening` is what makes the forgetful functor and the covering families of the site
direct to formulate.

Since the library already has `Crystalline.DividedPowerThickening` for the *affine* situation
[Stacks, Tag 07HM], the geometric notion of [Stacks, Tag 07I4] is called `SchemeThickening` here,
and the objects of `CRIS(X/S)` are `S.Thickening` for `S` the standing situation.

## References

* [Stacks Project, Tag 07I4](https://stacks.math.columbia.edu/tag/07I4)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07I7](https://stacks.math.columbia.edu/tag/07I7)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
open Stacks.Thickenings

universe u

namespace Crystalline

/-- **A divided power thickening of schemes.**  A thickening `immersion : source ⟶ target.scheme`
whose defining ideal is, on every affine open, the divided power ideal of `target`. -/
@[ext, stacks 07I4]
structure SchemeThickening where
  /-- The scheme being thickened. -/
  source : Scheme.{u}
  /-- The ambient divided power scheme. -/
  target : DividedPowerScheme.{u}
  /-- The immersion into the ambient scheme. -/
  immersion : source ⟶ target.scheme
  /-- The immersion is a thickening. -/
  isThickening : IsThickening immersion
  /-- On each affine open, the divided power ideal is the defining ideal of the immersion. -/
  ideal_eq_ker (V : target.scheme.affineOpens) :
    target.ideal.obj (op (V : target.scheme.Opens)) = immersion.ker.ideal V

namespace SchemeThickening

/-- The immersion of a divided power thickening is a closed immersion. -/
instance (D : SchemeThickening.{u}) : IsClosedImmersion D.immersion := D.isThickening.1

/-- Over any open of the ambient scheme, the immersion of a divided power thickening kills every
section of the divided power ideal. -/
theorem immersion_app_eq_zero_of_mem (D : SchemeThickening.{u}) (V : D.target.scheme.Opens)
    (s : Γ(D.target.scheme, V)) (hs : s ∈ D.target.ideal.obj (op V)) :
    D.immersion.app V s = 0 :=
  D.immersion.app_eq_zero_of_mem_of_le_ker _ (fun U ↦ (D.ideal_eq_ker U).le) V s hs

end SchemeThickening

/-- The standing global crystalline situation: a prime `p`, a divided power scheme `(S, I, γ)`
over `ℤ_(p)`, and a scheme `X` over the closed fibre `S₀ = V(I)` on which `p` is locally
nilpotent. -/
@[stacks 07MF]
structure GlobalCrystallineSituation where
  /-- The fixed prime. -/
  p : ℕ
  /-- The primality hypothesis. -/
  [prime : Fact p.Prime]
  /-- The divided power base scheme. -/
  S : DividedPowerScheme.{u}
  /-- The `ℤ_(p)`-structure, expressed on global sections. -/
  [algebraAtPrime : Algebra (DividedPowers.IntegersAtPrime p) Γ(S.scheme, ⊤)]
  /-- The scheme on which the crystalline site is based. -/
  X : Scheme.{u}
  /-- The structure morphism to the closed fibre `S₀ = V(I)`. -/
  toClosedFiber : X ⟶ DividedPowerScheme.closedFiber S
  /-- The prime is nilpotent in every local ring of `X`. -/
  prime_locallyNilpotent : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)

attribute [instance] GlobalCrystallineSituation.prime
  GlobalCrystallineSituation.algebraAtPrime

namespace GlobalCrystallineSituation

/-- The structural morphism of `X` over the divided power base `S`, through the closed fibre. -/
noncomputable abbrev sourceToBase (S : GlobalCrystallineSituation.{u}) : S.X ⟶ S.S.scheme :=
  S.toClosedFiber ≫ DividedPowerScheme.closedFiberι S.S

/-- An object of the big crystalline category `CRIS(X/S)`: a divided power thickening `U ↪ T`
over `S`, together with a map `U ⟶ X` over `S`. -/
@[stacks 07I6 "(1)"]
structure Thickening (S : GlobalCrystallineSituation.{u}) where
  /-- The divided power thickening `U ↪ T`. -/
  thickening : SchemeThickening.{u}
  /-- The divided power morphism `T ⟶ S`. -/
  toBase : thickening.target ⟶ S.S
  /-- The map `U ⟶ X`. -/
  toX : thickening.source ⟶ S.X
  /-- The map to `X` is a morphism over `S`. -/
  over_base : thickening.immersion ≫ toBase.hom = toX ≫ sourceToBase S

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}}

/-- A morphism of `CRIS(X/S)`: a map of the underlying thickenings over the divided power base
which is compatible with the maps to `X`. -/
@[ext, stacks 07I6 "(2)"]
structure Hom (A B : Thickening S) where
  /-- The map on the thickened schemes. -/
  sourceHom : A.thickening.source ⟶ B.thickening.source
  /-- The divided power map on the ambient schemes. -/
  targetHom : A.thickening.target ⟶ B.thickening.target
  /-- The square of thickenings commutes. -/
  immersion_naturality :
    A.thickening.immersion ≫ targetHom.hom = sourceHom ≫ B.thickening.immersion
  /-- The map on ambient schemes is over the divided power base. -/
  base_naturality : targetHom ≫ B.toBase = A.toBase
  /-- The map on thickened schemes is over `X`. -/
  toX_naturality : sourceHom ≫ B.toX = A.toX

/-- Divided power thickenings of `X` relative to `S` form the big crystalline category
`CRIS(X/S)`. -/
@[stacks 07I6 "the category CRIS(X/S)"]
instance instCategory : Category.{u} (Thickening S) where
  Hom := Hom
  id A :=
    { sourceHom := 𝟙 A.thickening.source
      targetHom := 𝟙 A.thickening.target
      immersion_naturality := by simp
      base_naturality := by simp
      toX_naturality := by simp }
  comp f g :=
    { sourceHom := f.sourceHom ≫ g.sourceHom
      targetHom := f.targetHom ≫ g.targetHom
      immersion_naturality := by
        simp only [DividedPowerScheme.Hom.comp_hom]
        rw [← Category.assoc, f.immersion_naturality, Category.assoc,
          g.immersion_naturality, ← Category.assoc]
      base_naturality := by rw [Category.assoc, g.base_naturality, f.base_naturality]
      toX_naturality := by rw [Category.assoc, g.toX_naturality, f.toX_naturality] }
  id_comp f := by apply Hom.ext <;> simp
  comp_id f := by apply Hom.ext <;> simp
  assoc f g h :=
    Hom.ext (Category.assoc f.sourceHom g.sourceHom h.sourceHom)
      (Category.assoc f.targetHom g.targetHom h.targetHom)

/-- The identity morphism of `CRIS(X/S)` is the identity on thickened schemes. -/
@[simp]
theorem id_sourceHom (A : Thickening S) :
    (𝟙 A : A ⟶ A).sourceHom = 𝟙 A.thickening.source := rfl

/-- The identity morphism of `CRIS(X/S)` is the identity on ambient divided power schemes. -/
@[simp]
theorem id_targetHom (A : Thickening S) :
    (𝟙 A : A ⟶ A).targetHom = 𝟙 A.thickening.target := rfl

/-- The map on thickened schemes of a composite is the composite of the maps. -/
@[simp]
theorem comp_sourceHom {A B C : Thickening S} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).sourceHom = f.sourceHom ≫ g.sourceHom := rfl

/-- The map on ambient divided power schemes of a composite is the composite of the maps. -/
@[simp]
theorem comp_targetHom {A B C : Thickening S} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).targetHom = f.targetHom ≫ g.targetHom := rfl

end Thickening

/-- The forgetful functor `CRIS(X/S) ⥤ Sch/X`, sending a divided power thickening `U ↪ T` with
its map `U ⟶ X` to the scheme `U` over `X`. -/
@[stacks 07I7]
def forget (S : GlobalCrystallineSituation.{u}) : Thickening S ⥤ Over S.X where
  obj A := Over.mk A.toX
  map f := Over.homMk f.sourceHom f.toX_naturality
  map_id A := by ext; simp
  map_comp f g := by ext; simp

/-- The underlying scheme of `(forget S).obj A` is the thickened scheme of `A`. -/
@[simp]
theorem forget_obj_left (S : GlobalCrystallineSituation.{u}) (A : Thickening S) :
    ((forget S).obj A).left = A.thickening.source := rfl

/-- The structure morphism of `(forget S).obj A` is the map `A.toX`. -/
@[simp]
theorem forget_obj_hom (S : GlobalCrystallineSituation.{u}) (A : Thickening S) :
    ((forget S).obj A).hom = A.toX := rfl

/-- The map of schemes underlying `(forget S).map f` is the map on thickened schemes of `f`. -/
@[simp]
theorem forget_map_left (S : GlobalCrystallineSituation.{u}) {A B : Thickening S} (f : A ⟶ B) :
    ((forget S).map f).left = f.sourceHom := rfl

end GlobalCrystallineSituation

end Crystalline

end
