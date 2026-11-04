module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Étale neighbourhoods of a point of a scheme

Let `s` be a point of a scheme `S`. An *étale neighbourhood* of `(S, s)` is an étale morphism
`U ⟶ S` together with a point of `U` lying over `s`. A morphism of étale neighbourhoods is a
morphism over `S` carrying the distinguished point to the distinguished point; these make the
étale neighbourhoods of `(S, s)` into a category. The neighbourhood is *elementary* when the
induced extension of residue fields is trivial, i.e. when the canonical map
`κ(s) ⟶ κ(U.point)` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.EtaleNeighborhood S s` is an étale neighbourhood of `S` at `s`.
* `AlgebraicGeometry.EtaleNeighborhood.Hom` is a morphism of étale neighbourhoods, and
  `AlgebraicGeometry.EtaleNeighborhood.instCategory` the resulting category structure.
* `AlgebraicGeometry.EtaleNeighborhood.residueFieldMap` is the induced map of residue fields
  `κ(s) ⟶ κ(U.point)`.
* `AlgebraicGeometry.EtaleNeighborhood.IsElementary` says that this map is an isomorphism.
* `AlgebraicGeometry.EtaleNeighborhood.self` is the neighbourhood `𝟙 S`, and
  `AlgebraicGeometry.EtaleNeighborhood.ofEtale` the neighbourhood attached to an arbitrary étale
  morphism and a point of its source.
* `AlgebraicGeometry.EtaleNeighborhood.comp` composes a neighbourhood of `(S, s)` with a
  neighbourhood of its distinguished point.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.isElementary_iff`: a neighbourhood is elementary exactly
  when the residue field map of its structure morphism at the distinguished point is an
  isomorphism.
* `AlgebraicGeometry.EtaleNeighborhood.IsElementary.comp`: a composite of elementary
  neighbourhoods is elementary.
* `AlgebraicGeometry.EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion`: an open
  subscheme is an elementary étale neighbourhood of each of its points.

## References

* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If `x₁ = x₂`, the residue field map of `f` at `x₁` is an isomorphism if and only if the one
at `x₂` is. -/
theorem Scheme.Hom.isIso_residueFieldMap_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {x₁ x₂ : X}
    (e : x₁ = x₂) : IsIso (f.residueFieldMap x₁) ↔ IsIso (f.residueFieldMap x₂) := by
  subst e; rfl

/-- An *étale neighbourhood* of a scheme `S` at a point `s` is a scheme which is étale over `S`,
together with a distinguished point lying over `s`. -/
@[stacks 02LE "part (1)"]
structure EtaleNeighborhood (S : Scheme.{u}) (s : S) where
  /-- The scheme underlying the neighbourhood. -/
  scheme : Scheme.{u}
  /-- The distinguished point of the neighbourhood. -/
  point : scheme
  /-- The structure morphism of the neighbourhood, which is étale. -/
  toBase : scheme ⟶ S
  [etale_toBase : Etale toBase]
  /-- The distinguished point lies over the given point of the base. -/
  map_point : toBase point = s

namespace EtaleNeighborhood

attribute [instance] etale_toBase

variable {S : Scheme.{u}} {s : S}

/-- A morphism of étale neighbourhoods of `(S, s)` is a morphism of schemes over `S` which
carries the distinguished point to the distinguished point. -/
@[ext, stacks 02LE "part (2)"]
structure Hom (U V : EtaleNeighborhood S s) where
  /-- The underlying morphism of schemes. -/
  hom : U.scheme ⟶ V.scheme
  /-- The underlying morphism is a morphism over the base. -/
  over : hom ≫ V.toBase = U.toBase
  /-- The underlying morphism preserves the distinguished points. -/
  map_point : hom U.point = V.point

/-- Étale neighbourhoods of `(S, s)` form a category, with the morphisms of `Hom`. -/
instance : Category (EtaleNeighborhood S s) where
  Hom := Hom
  id U :=
    { hom := 𝟙 U.scheme
      over := by simp
      map_point := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      over := by simp only [Category.assoc, g.over, f.over]
      map_point := by simp [f.map_point, g.map_point] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

@[simp]
lemma id_hom (U : EtaleNeighborhood S s) : Hom.hom (𝟙 U) = 𝟙 U.scheme := rfl

@[simp]
lemma comp_hom {U V W : EtaleNeighborhood S s} (f : U ⟶ V) (g : V ⟶ W) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

/-- The canonical homomorphism from the residue field at the base point to the residue field at
the distinguished point of an étale neighbourhood. It is the residue field map of the structure
morphism, transported along `EtaleNeighborhood.map_point`. -/
def residueFieldMap (U : EtaleNeighborhood S s) :
    S.residueField s ⟶ U.scheme.residueField U.point :=
  (S.residueFieldCongr U.map_point).inv ≫ U.toBase.residueFieldMap U.point

lemma residueFieldMap_def (U : EtaleNeighborhood S s) :
    U.residueFieldMap =
      (S.residueFieldCongr U.map_point).inv ≫ U.toBase.residueFieldMap U.point :=
  rfl

/-- An étale neighbourhood is *elementary* if the induced extension of residue fields is
trivial. -/
@[stacks 02LE "part (3)"]
abbrev IsElementary (U : EtaleNeighborhood S s) : Prop := IsIso U.residueFieldMap

/-- A neighbourhood is elementary exactly when the residue field map of its structure morphism
at the distinguished point is an isomorphism. -/
theorem isElementary_iff (U : EtaleNeighborhood S s) :
    U.IsElementary ↔ IsIso (U.toBase.residueFieldMap U.point) := by
  rw [IsElementary, residueFieldMap_def, isIso_comp_left_iff]

/-- The identity morphism of `S`, with the point `s`, is an étale neighbourhood of `(S, s)`. -/
def self (S : Scheme.{u}) (s : S) : EtaleNeighborhood S s where
  scheme := S
  point := s
  toBase := 𝟙 S
  map_point := by simp

/-- The neighbourhood `EtaleNeighborhood.self` is elementary. -/
theorem isElementary_self (S : Scheme.{u}) (s : S) : (self S s).IsElementary := by
  rw [isElementary_iff]
  exact (Scheme.residueFieldMap_id s).symm ▸ IsIso.id _

/-- An étale morphism together with a point of its source is an étale neighbourhood of the base
at the image of that point. -/
def ofEtale {X : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X) : EtaleNeighborhood S (f x) where
  scheme := X
  point := x
  toBase := f
  map_point := rfl

@[simp]
lemma ofEtale_scheme {X : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X) :
    (ofEtale f x).scheme = X := rfl

@[simp]
lemma ofEtale_point {X : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X) :
    (ofEtale f x).point = x := rfl

@[simp]
lemma ofEtale_toBase {X : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X) :
    (ofEtale f x).toBase = f := rfl

/-- An open subscheme is an elementary étale neighbourhood of each of its points. -/
theorem isElementary_ofEtale_of_isOpenImmersion {X : Scheme.{u}} (f : X ⟶ S)
    [IsOpenImmersion f] (x : X) : (ofEtale f x).IsElementary := by
  rw [isElementary_iff]
  exact inferInstanceAs (IsIso (f.residueFieldMap x))

/-- An étale neighbourhood of the distinguished point of an étale neighbourhood `U` of `(S, s)`
is again an étale neighbourhood of `(S, s)`, via the composite structure morphism. -/
def comp (U : EtaleNeighborhood S s) (V : EtaleNeighborhood U.scheme U.point) :
    EtaleNeighborhood S s where
  scheme := V.scheme
  point := V.point
  toBase := V.toBase ≫ U.toBase
  map_point := by simp [V.map_point, U.map_point]

@[simp]
lemma comp_scheme (U : EtaleNeighborhood S s) (V : EtaleNeighborhood U.scheme U.point) :
    (U.comp V).scheme = V.scheme := rfl

@[simp]
lemma comp_point (U : EtaleNeighborhood S s) (V : EtaleNeighborhood U.scheme U.point) :
    (U.comp V).point = V.point := rfl

@[simp]
lemma comp_toBase (U : EtaleNeighborhood S s) (V : EtaleNeighborhood U.scheme U.point) :
    (U.comp V).toBase = V.toBase ≫ U.toBase := rfl

/-- A composite of elementary étale neighbourhoods is an elementary étale neighbourhood. -/
theorem IsElementary.comp {U : EtaleNeighborhood S s} {V : EtaleNeighborhood U.scheme U.point}
    (hU : U.IsElementary) (hV : V.IsElementary) : (U.comp V).IsElementary := by
  rw [isElementary_iff] at hU hV ⊢
  exact Scheme.residueFieldMap_comp V.toBase U.toBase V.point ▸
    IsIso.comp_isIso' ((U.toBase.isIso_residueFieldMap_congr V.map_point).mpr hU) hV

end EtaleNeighborhood

end AlgebraicGeometry

end
