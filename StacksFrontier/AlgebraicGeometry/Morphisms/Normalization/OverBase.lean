module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty

/-!
# Functoriality of normalization for schemes over a base

Fix a scheme `S`. Among the schemes over `S` whose quasi-compact opens have finitely many
irreducible components, consider the morphisms over `S` which carry generic points of
irreducible components to generic points of irreducible components. These form a category, and
normalization is a functor on it: the normalization of the source maps uniquely to the
normalization of the target over the given morphism, and the normalization morphisms assemble
into a natural transformation to the underlying-scheme functor.

## Main definitions

* `AlgebraicGeometry.NormalizableOver` is a scheme over `S` whose quasi-compact opens have
  finitely many irreducible components.
* `AlgebraicGeometry.NormalizableOver.Hom` is a morphism over `S` preserving generic points,
  and `AlgebraicGeometry.NormalizableOver.instCategory` is the resulting category.
* `AlgebraicGeometry.NormalizableOver.forget` is the functor to schemes.
* `AlgebraicGeometry.NormalizableOver.normalizationFunctor` is normalization as a functor.
* `AlgebraicGeometry.NormalizableOver.normalizationNatTrans` is the natural transformation of
  normalization morphisms.

## Main results

* `AlgebraicGeometry.NormalizableOver.isNormal_normalizationScheme`: the normalization of an
  object is normal.
* `AlgebraicGeometry.NormalizableOver.existsUnique_normalizationLift`: every morphism lifts
  uniquely to the normalizations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- A scheme over a base scheme `S` every one of whose quasi-compact opens has finitely many
irreducible components. -/
structure NormalizableOver (S : Scheme.{u}) where
  /-- The underlying scheme. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the base. -/
  toBase : scheme ⟶ S
  /-- Every quasi-compact open has finitely many irreducible components. -/
  finite_irreducibleComponents :
    ∀ U : scheme.Opens, IsCompact (U : Set scheme) → (irreducibleComponents U).Finite

namespace NormalizableOver

variable {S : Scheme.{u}}

/-- A morphism over the base which carries generic points of irreducible components to
generic points of irreducible components. -/
structure Hom (U V : NormalizableOver S) where
  /-- The underlying morphism of schemes. -/
  hom : U.scheme ⟶ V.scheme
  /-- Compatibility with the structure morphisms. -/
  over : hom ≫ V.toBase = U.toBase
  /-- Generic points are carried to generic points. -/
  mapsTo_genericPoints : Set.MapsTo hom (genericPoints U.scheme) (genericPoints V.scheme)

/-- The category of schemes over `S` with finitely many irreducible components locally, whose
morphisms are the morphisms over `S` carrying generic points to generic points. -/
instance instCategory (S : Scheme.{u}) : Category (NormalizableOver S) where
  Hom := Hom
  id U :=
    { hom := 𝟙 U.scheme
      over := Category.id_comp _
      mapsTo_genericPoints := fun _ hx ↦ by simpa using hx }
  comp f g :=
    { hom := f.hom ≫ g.hom
      over := by rw [Category.assoc, g.over, f.over]
      mapsTo_genericPoints := g.mapsTo_genericPoints.comp f.mapsTo_genericPoints }
  id_comp f := by cases f; simp
  comp_id f := by cases f; simp
  assoc f g h := by cases f; cases g; cases h; simp

/-- The functor forgetting the structure morphism and the finiteness condition. -/
def forget (S : Scheme.{u}) : NormalizableOver S ⥤ Scheme.{u} where
  obj U := U.scheme
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The normalization of an object. -/
abbrev normalizationScheme (U : NormalizableOver S) : Scheme.{u} :=
  U.scheme.normalizationScheme U.finite_irreducibleComponents

/-- The normalization morphism of an object. -/
abbrev normalization (U : NormalizableOver S) : U.normalizationScheme ⟶ U.scheme :=
  U.scheme.normalization U.finite_irreducibleComponents

/-- The normalization of an object is normal. -/
theorem isNormal_normalizationScheme (U : NormalizableOver S) : IsNormal U.normalizationScheme :=
  U.scheme.isNormal_normalizationScheme U.finite_irreducibleComponents

/-- A morphism of the category lifts uniquely to the normalizations: there is exactly one
morphism of normalizations lying over it. -/
theorem existsUnique_normalizationLift {U V : NormalizableOver S} (g : U ⟶ V) :
    ∃! lift : U.normalizationScheme ⟶ V.normalizationScheme,
      lift ≫ V.normalization = U.normalization ≫ Hom.hom g := by
  have : IsNormal U.normalizationScheme := U.isNormal_normalizationScheme
  refine Scheme.existsUnique_lift_normalization V.finite_irreducibleComponents
    (U.normalization ≫ Hom.hom g) fun η ↦ ?_
  simpa only [Scheme.Hom.comp_apply] using Hom.mapsTo_genericPoints g
    (U.scheme.normalization_mem_genericPoints U.finite_irreducibleComponents η.2)

/-- The canonical lift of a morphism to the normalizations. -/
def normalizationLift {U V : NormalizableOver S} (g : U ⟶ V) :
    U.normalizationScheme ⟶ V.normalizationScheme :=
  (existsUnique_normalizationLift g).choose

/-- The canonical lift composed with the normalization of the target is the normalization of
the source composed with the morphism. -/
@[reassoc (attr := simp)]
theorem normalizationLift_normalization {U V : NormalizableOver S} (g : U ⟶ V) :
    normalizationLift g ≫ V.normalization = U.normalization ≫ Hom.hom g :=
  (existsUnique_normalizationLift g).choose_spec.1

/-- Any morphism of normalizations lying over a given morphism is the canonical lift. -/
theorem normalizationLift_unique {U V : NormalizableOver S} (g : U ⟶ V)
    (lift : U.normalizationScheme ⟶ V.normalizationScheme)
    (h : lift ≫ V.normalization = U.normalization ≫ Hom.hom g) :
    lift = normalizationLift g :=
  (existsUnique_normalizationLift g).choose_spec.2 lift h

/-- Normalization as a functor on schemes over the base whose morphisms preserve generic
points. -/
def normalizationFunctor (S : Scheme.{u}) : NormalizableOver S ⥤ Scheme.{u} where
  obj U := U.normalizationScheme
  map g := normalizationLift g
  map_id U := (normalizationLift_unique (𝟙 U) (𝟙 U.normalizationScheme) (by
    change U.normalization = U.normalization ≫ 𝟙 U.scheme
    simp)).symm
  map_comp f g := (normalizationLift_unique (f ≫ g)
    (normalizationLift f ≫ normalizationLift g) (by
      simp only [Category.assoc, normalizationLift_normalization,
        normalizationLift_normalization_assoc]
      rfl)).symm

/-- The normalization morphisms form a natural transformation to the underlying schemes. -/
def normalizationNatTrans (S : Scheme.{u}) : normalizationFunctor S ⟶ forget S where
  app U := U.normalization
  naturality _ _ g := normalizationLift_normalization g

end NormalizableOver

end AlgebraicGeometry

end
