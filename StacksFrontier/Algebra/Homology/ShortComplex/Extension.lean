module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extensions of an object by another, and their category

Let `𝒜` be an abelian category and `A`, `B` objects of `𝒜`. An extension `E` of `B` by `A` is
a short exact sequence `0 → A → E → B → 0`. A morphism from an extension
`0 → A → E → B → 0` to an extension `0 → A → F → B → 0` is a map `φ : E → F` making the ladder
with the identity on `A` and on `B` commute. With these morphisms, the extensions of `B` by `A`
form a category.

## Main definitions

* `CategoryTheory.Abelian.Extension B A`: the extensions of `B` by `A`.
* `CategoryTheory.Abelian.Extension.toShortComplex`: the short complex `A → E → B` of an
  extension, which is short exact (`CategoryTheory.Abelian.Extension.shortExact`).
* `CategoryTheory.Abelian.Extension.Hom`: the morphisms of extensions.
* `CategoryTheory.Abelian.Extension.category`: the category of extensions of `B` by `A`.
-/

@[expose] public section

namespace CategoryTheory.Abelian

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]

/-- An *extension of `B` by `A`* in an abelian category `𝒜`: a short exact sequence
`0 → A → X → B → 0`, given by its middle term `X` and its maps `f : A ⟶ X` and `g : X ⟶ B`. -/
@[stacks 010J "extensions of `B` by `A`"]
structure Extension (B A : 𝒜) where
  /-- The middle term of the extension. -/
  X : 𝒜
  /-- The map `A ⟶ X`. -/
  f : A ⟶ X
  /-- The map `X ⟶ B`. -/
  g : X ⟶ B
  /-- The composite `A ⟶ X ⟶ B` is zero. -/
  zero : f ≫ g = 0
  /-- The sequence `0 → A → X → B → 0` is short exact. -/
  shortExact' : (ShortComplex.mk f g zero).ShortExact

attribute [reassoc (attr := simp)] Extension.zero

namespace Extension

variable {B A : 𝒜}

/-- The short complex `A ⟶ X ⟶ B` of an extension of `B` by `A`. -/
abbrev toShortComplex (E : Extension B A) : ShortComplex 𝒜 :=
  ShortComplex.mk E.f E.g E.zero

lemma shortExact (E : Extension B A) : E.toShortComplex.ShortExact :=
  E.shortExact'

instance (E : Extension B A) : Mono E.f :=
  E.shortExact.mono_f

instance (E : Extension B A) : Epi E.g :=
  E.shortExact.epi_g

/-- A *morphism of extensions* from `0 → A → E → B → 0` to `0 → A → F → B → 0`: a morphism
`hom : E → F` of the middle terms making the ladder commute with the identity maps on `A` and
on `B`, i.e. `E.f ≫ hom = F.f` and `hom ≫ F.g = E.g`. -/
@[stacks 010J "morphisms of extensions", ext]
structure Hom (E F : Extension B A) where
  /-- The map of the middle terms. -/
  hom : E.X ⟶ F.X
  /-- The square at `A`, with the identity on `A`, commutes. -/
  comm_f : E.f ≫ hom = F.f := by cat_disch
  /-- The square at `B`, with the identity on `B`, commutes. -/
  comm_g : hom ≫ F.g = E.g := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm_f Hom.comm_g

/-- The identity morphism of an extension. -/
@[simps]
def Hom.id (E : Extension B A) : Hom E E where
  hom := 𝟙 E.X

/-- The composite of two morphisms of extensions. -/
@[simps]
def Hom.comp {E F G : Extension B A} (φ : Hom E F) (ψ : Hom F G) : Hom E G where
  hom := φ.hom ≫ ψ.hom

/-- The extensions of `B` by `A` form a category, whose morphisms are the morphisms of
extensions `CategoryTheory.Abelian.Extension.Hom`. -/
@[stacks 010J "the category of extensions of `B` by `A`"]
instance category : Category (Extension B A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext {E F : Extension B A} {φ ψ : E ⟶ F} (h : φ.hom = ψ.hom) : φ = ψ :=
  Hom.ext h

@[simp]
lemma id_hom (E : Extension B A) : Hom.hom (𝟙 E) = 𝟙 E.X :=
  rfl

@[simp, reassoc]
lemma comp_hom {E F G : Extension B A} (φ : E ⟶ F) (ψ : F ⟶ G) :
    (φ ≫ ψ).hom = φ.hom ≫ ψ.hom :=
  rfl

end Extension

end CategoryTheory.Abelian
