module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Morphisms into a coproduct of sheaves

A coproduct of sheaves has a universal property for morphisms *out* of it, and none for morphisms
*into* it: it is the sheafification of the coproduct of the underlying presheaves, so a section of
it over an object is only locally a finite sum of sections of the summands. A morphism into it can
therefore not be assembled from a family of morphisms into the summands.

What does assemble it is a morphism of *presheaves* into the coproduct of the underlying
presheaves. The coproduct of presheaves does have a universal property for morphisms out of it, so
the family of underlying presheaf morphisms of the summand inclusions descends to a comparison
morphism from the presheaf coproduct to the underlying presheaf of the sheaf coproduct; composing
with it turns a presheaf morphism into the presheaf coproduct into a morphism of sheaves, because
a morphism of sheaves is nothing but a morphism of the underlying presheaves.

## Main definitions

* `CategoryTheory.Sheaf.sigmaPresheafComparison`: the comparison morphism from the coproduct of
  the underlying presheaves of a family of sheaves to the underlying presheaf of their coproduct.
* `CategoryTheory.Sheaf.sigmaHomOfPresheafHom`: **the morphism into a coproduct of sheaves
  determined by a morphism of presheaves into the coproduct of the underlying presheaves.**

## Main results

* `CategoryTheory.Sheaf.ι_sigmaPresheafComparison`: the comparison morphism restricts on each
  summand of the presheaf coproduct to the underlying presheaf morphism of the summand inclusion.
* `CategoryTheory.Sheaf.sigmaHomOfPresheafHom_ι`: a presheaf morphism that factors through a
  single summand determines the corresponding composite with that summand's inclusion, so the
  construction extends the summand inclusions.

## Implementation notes

The two coproducts are hypotheses rather than instances of a single hypothesis: the coproduct of
sheaves exists as soon as the one of presheaves does and the topology admits sheafification, but
asking for sheafification would be a stronger hypothesis than the statements need, and on the
sites where this is used both coproducts are supplied by hand because instance search does not
find them.

The comparison morphism is *not* in general an isomorphism, nor even a monomorphism or an
epimorphism, and nothing here claims it is. It becomes an epimorphism locally — that is what
makes the sheaf coproduct a sheafification of the presheaf one — but the construction below needs
none of that, only functoriality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₂ u₂ v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u₂}
  [Category.{v₂} A] {I : Type w} (G : I → Sheaf J A) [HasCoproduct G]
  [HasCoproduct fun i ↦ (G i).obj]

/-- **The comparison morphism from the coproduct of the underlying presheaves of a family of
sheaves to the underlying presheaf of their coproduct.** It is the morphism out of the presheaf
coproduct given by the underlying presheaf morphisms of the summand inclusions. -/
def sigmaPresheafComparison : (∐ fun i ↦ (G i).obj) ⟶ (∐ G).obj :=
  Sigma.desc fun i ↦ (Sigma.ι G i).hom

/-- The comparison morphism restricts on the summand at `i` of the presheaf coproduct to the
underlying presheaf morphism of the summand inclusion at `i`. -/
@[simp]
theorem ι_sigmaPresheafComparison (i : I) :
    Sigma.ι (fun i ↦ (G i).obj) i ≫ sigmaPresheafComparison G = (Sigma.ι G i).hom :=
  Sigma.ι_desc _ i

variable {F : Sheaf J A}

/-- **The morphism into a coproduct of sheaves determined by a morphism of presheaves into the
coproduct of the underlying presheaves.**

Over each object the datum is a section of the presheaf coproduct, that is, a finitely supported
family of sections of the summands, natural in the object. -/
def sigmaHomOfPresheafHom (φ : F.obj ⟶ ∐ fun i ↦ (G i).obj) : F ⟶ ∐ G :=
  ObjectProperty.homMk (φ ≫ sigmaPresheafComparison G)

/-- The underlying presheaf morphism of `sigmaHomOfPresheafHom G φ` is `φ` followed by the
comparison morphism `sigmaPresheafComparison G`. -/
@[simp]
theorem sigmaHomOfPresheafHom_hom (φ : F.obj ⟶ ∐ fun i ↦ (G i).obj) :
    (sigmaHomOfPresheafHom G φ).hom = φ ≫ sigmaPresheafComparison G :=
  rfl

/-- **The construction extends the summand inclusions**: a presheaf morphism that factors through
the summand at `i`, by the underlying presheaf morphism of a morphism of sheaves, determines that
morphism followed by the summand inclusion at `i`. -/
theorem sigmaHomOfPresheafHom_ι (i : I) (ψ : F ⟶ G i) :
    sigmaHomOfPresheafHom G (ψ.hom ≫ Sigma.ι (fun i ↦ (G i).obj) i) = ψ ≫ Sigma.ι G i :=
  Sheaf.hom_ext (by
    rw [sigmaHomOfPresheafHom_hom, Category.assoc, ι_sigmaPresheafComparison]
    rfl)

end CategoryTheory.Sheaf

end
