module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Group schemes over a base, by their functor of points

A group scheme over a scheme `S` is a pair `(G, m)` of a scheme `G` over `S` and a
multiplication morphism `m : G ×_S G ⟶ G` of `S`-schemes such that, for every scheme `T` over
`S`, the induced multiplication makes the set `G(T)` of `T`-valued points into a group; a
morphism of group schemes is an `S`-morphism inducing a group homomorphism on `T`-points for
every `T`. This file states this functor-of-points definition as
`AlgebraicGeometry.GroupSchemeOverPoints` and `AlgebraicGeometry.GroupSchemeOverPoints.Hom`, and
identifies it with an internal group object `GrpObj` in the Cartesian monoidal category
`Over S`, via the Yoneda embedding `CategoryTheory.yonedaGrp` of group objects into presheaves
of groups.

## Main definitions

* `AlgebraicGeometry.GroupSchemeOverPoints` is a group scheme over `S` in the sense of the
  source: a pair `(G, m)` whose induced multiplication makes every `T`-points set a group.
* `AlgebraicGeometry.GroupSchemeOverPoints.Hom` is a morphism of group schemes over `S` in the
  sense of the source: an `S`-morphism inducing a group homomorphism on every `T`-points set.

## Main results

* `AlgebraicGeometry.GroupSchemeOverPoints.grpObj` builds Mathlib's internal `GrpObj` structure
  on the underlying `S`-scheme of a `GroupSchemeOverPoints`, via the presheaf of `T`-points and
  the Yoneda embedding `CategoryTheory.GrpObj.ofRepresentableBy`.
* `AlgebraicGeometry.GrpObj.toGroupSchemeOverPoints` goes the other way: an internal `GrpObj`
  on an `S`-scheme `G` induces the source's functor-of-points group structure on `G`, using the
  group structure `CategoryTheory.Hom.group` that `GrpObj` puts on every `T`-points set.
* `AlgebraicGeometry.GroupSchemeOverPoints.Hom.toIsMonHom` shows that a morphism of group
  schemes over `S` in the source's sense is a morphism of the associated `GrpObj`s, i.e. an
  `IsMonHom` for the `grpObj` instances; conversely
  `AlgebraicGeometry.GroupSchemeOverPoints.homOfIsMonHom` builds a `Hom` from an `S`-morphism of
  `GrpObj`s.

## References

* [Stacks Project, Tag 022S](https://stacks.math.columbia.edu/tag/022S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **Stacks Project, Tag 022S** (1). A group scheme over `S`: a scheme `G` over `S` together
with a multiplication morphism `m : G ×_S G ⟶ G` of schemes over `S`, such that for every
scheme `T` over `S` the induced multiplication makes the set of `T`-valued points
`G(T) = Hom_{Over S}(T, G)` into a group. -/
@[stacks_fixed 022S "a group scheme over S"]
structure GroupSchemeOverPoints (S : Scheme.{u}) where
  /-- The underlying scheme over `S`. -/
  obj : Over S
  /-- The multiplication morphism `m : G ×_S G ⟶ G`. -/
  mul : obj ⊗ obj ⟶ obj
  /-- A choice of group structure on the `T`-valued points, for every `T` over `S`. -/
  group (T : Over S) : Group (T ⟶ obj)
  /-- The group multiplication on `T`-valued points is the one induced by `mul`. -/
  mul_eq (T : Over S) (a b : T ⟶ obj) :
    letI := group T
    a * b = lift a b ≫ mul

namespace GroupSchemeOverPoints

attribute [instance] group

/-- **Stacks Project, Tag 022S** (2). A morphism `ψ : (G, m) ⟶ (G', m')` of group schemes over
`S`: a morphism `ψ : G ⟶ G'` of schemes over `S` such that for every scheme `T` over `S`, the
induced map `ψ : G(T) ⟶ G'(T)` is a homomorphism of groups. -/
@[stacks_fixed 022S "morphisms of group schemes over S",
  sga "3 XI 2.1" "The value of M_H",
  sga "7 VII 2.9.6" "partial"]
structure Hom (G H : GroupSchemeOverPoints S) where
  /-- The underlying morphism of `S`-schemes. -/
  hom : G.obj ⟶ H.obj
  /-- The induced map on `T`-valued points is multiplicative, for every `T` over `S`. -/
  map_mul (T : Over S) (a b : T ⟶ G.obj) : (a * b) ≫ hom = (a ≫ hom) * (b ≫ hom)

variable (g h k : GroupSchemeOverPoints S)

/-- The presheaf of `T`-points of a `GroupSchemeOverPoints`, valued in groups: on objects it is
the group of `T`-valued points given by `g.group`, and on morphisms it is precomposition. -/
noncomputable def presheaf : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (T.unop ⟶ g.obj)
  map {T T'} φ := GrpCat.ofHom (MonoidHom.mk' (fun a => φ.unop ≫ a) (fun a b => by
    show φ.unop ≫ (a * b) = (φ.unop ≫ a) * (φ.unop ≫ b)
    rw [g.mul_eq, g.mul_eq, ← Category.assoc, comp_lift]))
  map_id T := by
    apply GrpCat.hom_ext; apply MonoidHom.ext
    intro a; change 𝟙 T.unop ≫ a = a; simp
  map_comp {T T' T''} φ ψ := by
    apply GrpCat.hom_ext; apply MonoidHom.ext
    intro a; change (ψ.unop ≫ φ.unop) ≫ a = ψ.unop ≫ φ.unop ≫ a; simp

/-- The presheaf `g.presheaf` sends `φ : T ⟶ T'` to precomposition `a ↦ φ.unop ≫ a` on
points. -/
@[simp] lemma presheaf_map_apply {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') (a : T.unop ⟶ g.obj) :
    ((presheaf g).map φ : (T.unop ⟶ g.obj) → (T'.unop ⟶ g.obj)) a = φ.unop ≫ a := rfl

/-- The identity equivalence `Hom(T, G) ≃ Hom(T, G)` exhibits `g.obj` as representing the
underlying-type functor of `g.presheaf`. -/
def presheafRepresentableBy : (g.presheaf ⋙ forget _).RepresentableBy g.obj where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- Mathlib's internal `GrpObj` structure on the underlying `S`-scheme of a
`GroupSchemeOverPoints`, obtained from the presheaf of `T`-points via the Yoneda
embedding `CategoryTheory.GrpObj.ofRepresentableBy`. This is the bridge from the source's
functor-of-points Definition 39.4.1 (Tag 022S) to Mathlib's internal group object, already used
throughout this repository as `[GrpObj (Over.mk f)]`. -/
@[instance_reducible,
  ega "0 8.2.3",
  ega "II 8.3.9" "Direction",
  sga "3 I 2.2" "partial",
  sga "3 I 4.2" "partial"]
noncomputable def grpObj : GrpObj g.obj :=
  GrpObj.ofRepresentableBy g.obj g.presheaf g.presheafRepresentableBy

/-- The multiplication of `g.grpObj` is `g.mul`. -/
lemma grpObj_mul : letI := g.grpObj; μ[g.obj] = g.mul := by
  let := g.grpObj
  have h := g.mul_eq (g.obj ⊗ g.obj) (fst g.obj g.obj) (snd g.obj g.obj)
  rw [lift_fst_snd, Category.id_comp] at h
  exact h

/-- The unit of `g.grpObj` is the identity element of the group of `𝟙_ (Over S)`-valued
points. -/
lemma grpObj_one : letI := g.grpObj; η[g.obj] = (1 : 𝟙_ (Over S) ⟶ g.obj) := rfl

namespace Hom

variable {g h} (ψ : Hom g h)

/-- A morphism of `GroupSchemeOverPoints` sends the identity element of the group of
`T`-valued points to the identity element, for every `T` over `S`. -/
lemma map_one (T : Over S) : (1 : T ⟶ g.obj) ≫ ψ.hom = 1 := by
  have h1 := ψ.map_mul T 1 1
  rw [one_mul] at h1
  have h2 : ((1 : T ⟶ g.obj) ≫ ψ.hom) * 1 =
      ((1 : T ⟶ g.obj) ≫ ψ.hom) * ((1 : T ⟶ g.obj) ≫ ψ.hom) := by
    rw [mul_one]; exact h1
  exact (mul_left_cancel h2).symm

/-- A morphism of `GroupSchemeOverPoints` in the source's sense is a morphism of the
associated `GrpObj`s. -/
theorem toIsMonHom : letI := g.grpObj; letI := h.grpObj; IsMonHom ψ.hom := by
  let := g.grpObj
  let := h.grpObj
  have hmul : μ[g.obj] ≫ ψ.hom = (ψ.hom ⊗ₘ ψ.hom) ≫ μ[h.obj] := by
    rw [g.grpObj_mul, h.grpObj_mul, ← lift_fst_comp_snd_comp, ← h.mul_eq, ← ψ.map_mul,
      g.mul_eq, lift_fst_snd, Category.id_comp]
  have hone : η[g.obj] ≫ ψ.hom = η[h.obj] := by
    rw [g.grpObj_one, h.grpObj_one]
    exact ψ.map_one (𝟙_ (Over S))
  exact { one_hom := hone, mul_hom := hmul }

end Hom

/-- An `S`-morphism between the underlying schemes of two
`GroupSchemeOverPoints` that is a morphism of their associated `GrpObj`s is a morphism of
`GroupSchemeOverPoints` in the source's sense. -/
def homOfIsMonHom (ψ : g.obj ⟶ h.obj)
    (_ : letI := g.grpObj; letI := h.grpObj; IsMonHom ψ) : Hom g h where
  hom := ψ
  map_mul T a b := by
    let := g.grpObj
    let := h.grpObj
    have hmul : g.mul ≫ ψ = (ψ ⊗ₘ ψ) ≫ h.mul := by
      have := ‹IsMonHom ψ›.mul_hom
      rwa [g.grpObj_mul, h.grpObj_mul] at this
    rw [g.mul_eq, Category.assoc, hmul, ← Category.assoc, lift_map, ← h.mul_eq]

end GroupSchemeOverPoints

/-- The functor-of-points group structure induced by Mathlib's internal `GrpObj`: for every
`T` over `S`, the group `CategoryTheory.Hom.group` on `T`-valued points has multiplication given
by `CategoryTheory.Hom.mul_def`, i.e. by the multiplication morphism of `G`. -/
@[ega "0 8.2.3",
  ega "II 8.3.9" "Direction",
  sga "3 I 2.1.2" "special case",
  sga "3 I 2.2" "partial"]
noncomputable def GrpObj.toGroupSchemeOverPoints (G : Over S) [GrpObj G] :
    GroupSchemeOverPoints S where
  obj := G
  mul := μ[G]
  group _ := CategoryTheory.Hom.group
  mul_eq _ a b := CategoryTheory.Hom.mul_def a b

end AlgebraicGeometry
