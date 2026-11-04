module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The big fppf site of the terminal scheme

Over the terminal scheme `Spec ℤ` an object of the big fppf site is a scheme of the site with its
unique structure morphism, so the functor to schemes is fully faithful. Consequently a cone of
objects of the site whose underlying cone of schemes is a limit cone is a limit cone in the site,
and its image in presheaves is a limit cone of representable presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A morphism of schemes between objects of the big fppf site of the terminal scheme, as a
morphism of the site. -/
noncomputable def homOfScheme {A A' : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (φ : (toScheme B (⊤_ Scheme.{u}) hZ).obj A ⟶ (toScheme B (⊤_ Scheme.{u}) hZ).obj A') :
    A ⟶ A' :=
  Over.homMk (ObjectProperty.homMk φ) (ObjectProperty.hom_ext _ (terminal.hom_ext _ _))

/-- The functor to schemes sends `homOfScheme B hZ φ` to `φ`. -/
@[simp]
theorem toScheme_map_homOfScheme {A A' : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (φ : (toScheme B (⊤_ Scheme.{u}) hZ).obj A ⟶ (toScheme B (⊤_ Scheme.{u}) hZ).obj A') :
    (toScheme B (⊤_ Scheme.{u}) hZ).map (homOfScheme B hZ φ) = φ :=
  rfl

/-- Over the terminal scheme the functor from the big fppf site to schemes is fully faithful. -/
noncomputable def toSchemeFullyFaithfulOfTerminal :
    (toScheme B (⊤_ Scheme.{u}) hZ).FullyFaithful where
  preimage φ := homOfScheme B hZ φ
  map_preimage _ := rfl
  preimage_map f := by
    ext
    rfl

/-- Over the terminal scheme the functor from the big fppf site to schemes is full. -/
instance : (toScheme B (⊤_ Scheme.{u}) hZ).Full :=
  (toSchemeFullyFaithfulOfTerminal B hZ).full

/-- Over the terminal scheme the functor from the big fppf site to schemes is faithful. -/
instance : (toScheme B (⊤_ Scheme.{u}) hZ).Faithful :=
  (toSchemeFullyFaithfulOfTerminal B hZ).faithful

variable {B hZ}

/-- Over the terminal scheme, a cone of objects of the big fppf site whose underlying cone of
schemes is a limit cone is a limit cone in the site. -/
noncomputable def isLimitOfIsLimitToScheme {J : Type*} [Category* J]
    {F : J ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ} {c : Cone F}
    (hc : IsLimit ((toScheme B (⊤_ Scheme.{u}) hZ).mapCone c)) : IsLimit c :=
  isLimitOfReflects (toScheme B (⊤_ Scheme.{u}) hZ) hc

/-- Over the terminal scheme, a cone of objects of the big fppf site whose underlying cone of
schemes is a limit cone becomes a limit cone of representable presheaves. -/
noncomputable def isLimitYonedaMapConeOfIsLimitToScheme {J : Type*} [Category* J]
    {F : J ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ} {c : Cone F}
    (hc : IsLimit ((toScheme B (⊤_ Scheme.{u}) hZ).mapCone c)) : IsLimit (yoneda.mapCone c) :=
  isLimitOfPreserves yoneda (isLimitOfIsLimitToScheme hc)

end AlgebraicGeometry.BigFppfOver

end
