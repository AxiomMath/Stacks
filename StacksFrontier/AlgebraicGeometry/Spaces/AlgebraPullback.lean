module

public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# Pullback of algebra sheaves along a morphism of algebraic spaces

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `A` be a sheaf of commutative `𝒪_X`-algebras on the small étale site of `X`
in the sense of `AlgebraicGeometry.Space.AlgebraSheaf`.  Its *pullback* along `g` is the
`𝒪_Y`-algebra `𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A`, the extension of scalars of the inverse image of `A`
along the inverse-image form `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` of the structure map of Stacks 03G8.

## Main definitions

* `AlgebraicGeometry.Space.ringSheafPullback` is the inverse image of sheaves of commutative
  rings along the morphism of small étale topoi attached to `g`.
* `AlgebraicGeometry.Space.algebraPullback` is the pullback functor on algebra sheaves, and
  `AlgebraicGeometry.Space.algebraPullbackMap` the canonical map from the inverse image of an
  algebra to its pullback.
* `AlgebraicGeometry.Space.AlgebraSheaf.ofHomMap` reads a morphism of the underlying sheaves of
  rings commuting with the structure maps as a morphism of the algebra sheaves they present.
* `AlgebraicGeometry.Space.structurePullbackMap` is the inverse-image form
  `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` of the structure map of `g`.

## Main results

* `AlgebraicGeometry.Space.algebraPullback_isPushout`: the pullback of `A` along `g` is the
  extension of scalars `𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A`; this is its universal property.
* `AlgebraicGeometry.Space.AlgebraSheaf.hom_comp_right`: a morphism of algebra sheaves commutes
  with the structure maps, read as morphisms of sheaves of rings.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe u

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {R R' : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u}}

/-- The sheaf of rings underlying the algebra presented by a homomorphism out of the structure
sheaf is the target of that homomorphism. -/
@[simp]
theorem ofHom_right (a : structureSheaf B S hS F hF ⟶ R) : (ofHom a).right = R :=
  rfl

/-- Reading a homomorphism out of the structure sheaf as an algebra and taking its structure
map again gives that homomorphism. -/
@[simp]
theorem hom_ofHom (a : structureSheaf B S hS F hF ⟶ R) : (ofHom a).hom = a :=
  rfl

/-- A morphism of algebra sheaves carries the structure map of its source to the structure map
of its target, as a homomorphism of sheaves of rings. -/
theorem hom_comp_right {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C) :
    A.hom ≫ φ.right = C.hom := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  ext r
  exact φ.comm U r

/-- A homomorphism of sheaves of rings commuting with the structure maps, as a morphism of the
algebra sheaves those structure maps present. -/
def ofHomMap {a : structureSheaf B S hS F hF ⟶ R} {a' : structureSheaf B S hS F hF ⟶ R'}
    (ρ : R ⟶ R') (h : a ≫ ρ = a') : ofHom a ⟶ ofHom a' where
  right := ρ
  comm _ _ := by subst h; rfl

/-- The underlying homomorphism of sheaves of rings of `ofHomMap ρ h` is `ρ`. -/
@[simp]
theorem ofHomMap_right {a : structureSheaf B S hS F hF ⟶ R}
    {a' : structureSheaf B S hS F hF ⟶ R'} (ρ : R ⟶ R') (h : a ≫ ρ = a') :
    (ofHomMap ρ h).right = ρ :=
  rfl

end AlgebraSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The inverse image `g⁻¹` of sheaves of commutative rings along the morphism of small étale
topoi of a morphism `g : Y ⟶ X` of algebraic spaces. -/
def ringSheafPullback (g : Y ⟶ X) :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} :=
  inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS g).toToposHom

/-- The inverse-image form `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` of the structure map of the morphism of small
étale ringed topoi of `g`. -/
def structurePullbackMap (g : Y ⟶ X) :
    (ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2) ⟶
      structureSheaf B S hS Y.1 Y.2 :=
  (smallEtaleRingedToposHom B S hS g).fSharpInverseImage

variable {B S hS}

/-- A morphism `φ : A ⟶ C` of algebra sheaves makes the inverse image of the structure map of
`A` commute with the pushout cocone built from `C`. -/
theorem ringSheafPullback_comp_inl (g : Y ⟶ X) {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    (φ : A ⟶ C) :
    (ringSheafPullback B S hS g).map A.hom ≫
        ((ringSheafPullback B S hS g).map φ.right ≫
          pushout.inl ((ringSheafPullback B S hS g).map C.hom)
            (structurePullbackMap B S hS g)) =
      structurePullbackMap B S hS g ≫
        pushout.inr ((ringSheafPullback B S hS g).map C.hom)
          (structurePullbackMap B S hS g) := by
  rw [← Category.assoc, ← Functor.map_comp, AlgebraSheaf.hom_comp_right φ]
  exact pushout.condition

variable (B S hS)

/-- Pullback of algebra sheaves along a morphism `g : Y ⟶ X` of algebraic spaces: the
`𝒪_Y`-algebra `𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A`, obtained by taking the inverse image of `A` as a sheaf of
rings over `g⁻¹𝒪_X` and pushing out along `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`. -/
def algebraPullback (g : Y ⟶ X) :
    AlgebraSheaf.{u, u} B S hS X.1 X.2 ⥤ AlgebraSheaf.{u, u} B S hS Y.1 Y.2 where
  obj A := AlgebraSheaf.ofHom
    (pushout.inr ((ringSheafPullback B S hS g).map A.hom)
      (structurePullbackMap B S hS g))
  map {_ _} φ := AlgebraSheaf.ofHomMap
    (pushout.desc _ _ (ringSheafPullback_comp_inl g φ))
    (pushout.inr_desc _ _ (ringSheafPullback_comp_inl g φ))
  map_id A := by
    refine AlgebraSheaf.Hom.ext (pushout.hom_ext ?_ ?_)
    · simp
    · simp
  map_comp φ ψ := by
    refine AlgebraSheaf.Hom.ext (pushout.hom_ext ?_ ?_)
    · simp
    · simp

/-- The sections of the pullback algebra are the pushout of the inverse image of `A` and the
structure sheaf of `Y` over the inverse image of the structure sheaf of `X`. -/
@[simp]
theorem algebraPullback_obj_right (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    ((algebraPullback B S hS g).obj A).right =
      pushout ((ringSheafPullback B S hS g).map A.hom) (structurePullbackMap B S hS g) :=
  rfl

/-- The structure map of the pullback algebra is the leg of the pushout out of the structure
sheaf of `Y`. -/
@[simp]
theorem algebraPullback_obj_hom (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    ((algebraPullback B S hS g).obj A).hom =
      pushout.inr ((ringSheafPullback B S hS g).map A.hom) (structurePullbackMap B S hS g) :=
  rfl

/-- The canonical map from the inverse image of an algebra sheaf to its pullback. -/
def algebraPullbackMap (g : Y ⟶ X) :
    AlgebraSheaf.forget ⋙ ringSheafPullback B S hS g ⟶
      algebraPullback B S hS g ⋙ AlgebraSheaf.forget where
  app _ := pushout.inl _ _
  naturality _ _ _ := (pushout.inl_desc _ _ _).symm

/-- **Algebra pullback is extension of scalars.**  The pullback of `A` along `g : Y ⟶ X` is
`𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A`: the inverse image of `A` and the structure sheaf of `Y` are pushed out
over the inverse image of the structure sheaf of `X`. -/
theorem algebraPullback_isPushout (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    IsPushout ((ringSheafPullback B S hS g).map A.hom)
      (structurePullbackMap B S hS g)
      ((algebraPullbackMap B S hS g).app A) ((algebraPullback B S hS g).obj A).hom :=
  IsPushout.of_hasPushout _ _

end AlgebraicGeometry.Space

end
