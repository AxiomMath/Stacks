module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Direct image of quasi-coherent modules along an affine morphism of algebraic spaces

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `A = f_*𝒪_Y` be the direct image of the structure sheaf of `Y`, a sheaf of
rings on the small étale site of `X`. **Stacks 08AI** asserts that `F ↦ f_*F` is an equivalence
from the quasi-coherent `𝒪_Y`-modules onto the quasi-coherent `A`-modules, and that an
`A`-module is quasi-coherent as an `𝒪_X`-module exactly when it is quasi-coherent as an
`A`-module.

The functor needs nothing new: the direct image of `𝒪_Y`-modules *over* `A` is
`AlgebraicGeometry.Space.moduleDirectImage`, which is Stacks 03D1 for the small étale sites and
already has `A = AlgebraicGeometry.Space.structureRingSheafDirectImage` as its coefficient ring
sheaf. What this file carries is that functor on the quasi-coherent subcategories, the first
assertion of the tag as a statement, and the identifications that pin it to direct image. The
equivalence itself is not proved here.

## Main definitions

* `AlgebraicGeometry.Space.affineDirectImageAlgebra` — the algebra `A = f_*𝒪_Y`.
* `AlgebraicGeometry.Space.DirectImagePreservesQuasicoherence` — that direct image over `A`
  carries quasi-coherent `𝒪_Y`-modules to quasi-coherent `A`-modules.
* `AlgebraicGeometry.Space.quasicoherentDirectImage` — **Stacks 08AI**, the functor
  `QCoh(𝒪_Y) ⥤ QCoh(A)` of the tag, granted that preservation.
* `AlgebraicGeometry.Space.AffineDirectImageEquivalence`,
  `AlgebraicGeometry.Space.AffinePushforwardEquivalence` — the first sentence of the tag, as a
  statement about one affine morphism and in the binders of the source.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDirectImage_comp_ι` — the functor on quasi-coherent
  modules is `AlgebraicGeometry.Space.moduleDirectImage` itself, so the statement of the
  equivalence is a statement about `f_*` and not about some other functor of the same type.
* `AlgebraicGeometry.Space.restrictScalars_moduleDirectImage` — the two readings of `f_*`, over
  `A` and over `𝒪_X`, differ only by restriction of scalars along `f♯ : 𝒪_X ⟶ A`.

## Implementation notes

The **equivalence** needs quasi-coherent modules on the small étale site of an algebraic space to
be described by an étale presentation groupoid, which is Stacks 03M3,
`AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase`, together with the passage from
`𝒪_X`-modules to `A`-modules: 03M3 describes the quasi-coherent modules over the *structure*
sheaf by chart data, and essential surjectivity here has to take a quasi-coherent `A`-module
apart, for the direct-image algebra `A = f_*𝒪_Y`. The scheme-level case of the equivalence is
Stacks 01SB; the case of algebraic spaces is its étale localisation.

`AlgebraicGeometry.Space.quasicoherentDirectImage` takes `DirectImagePreservesQuasicoherence` as
a hypothesis, and `quasicoherentDirectImage_comp_ι` says that whatever that hypothesis is
discharged by, the functor it produces is direct image on the nose.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- The algebra `A = f_*𝒪_Y` of an affine morphism `f : Y ⟶ X` of algebraic spaces, as a sheaf
of rings on the small étale site of `X`: the coefficient ring sheaf of the direct image of
`𝒪_Y`-modules of Stacks 03D1. -/
noncomputable abbrev affineDirectImageAlgebra (f : Y ⟶ X) :=
  structureRingSheafDirectImage B S hS f

/-- Restriction of scalars along the structure map `f♯ : 𝒪_X ⟶ f_*𝒪_Y` of Stacks 03G8 carries
the direct image of `𝒪_Y`-modules over `A` to the direct image of `𝒪_Y`-modules read as
`𝒪_X`-modules, which is Stacks 03LU.  So the two readings of `f_*` differ only by the
coefficients, on the nose. -/
theorem restrictScalars_moduleDirectImage (f : Y ⟶ X) :
    moduleDirectImage B S hS f ⋙ SheafOfModules.restrictScalars (structureSharp B S hS f) =
      modulePushforward B S hS f := rfl

/-- The first half of the first sentence of Stacks 08AI, as a statement: the direct image over
`A = f_*𝒪_Y` of a quasi-coherent `𝒪_Y`-module is quasi-coherent as an `A`-module. -/
def DirectImagePreservesQuasicoherence (f : Y ⟶ X) : Prop :=
  ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
    ((moduleDirectImage B S hS f).obj M).IsQuasicoherentOnSite

/-- **Stacks 08AI, the functor.** Direct image as a functor `QCoh(𝒪_Y) ⥤ QCoh(A)`, granted
that it preserves quasi-coherence. This is the functor `F ↦ f_*F` whose invertibility is the
first sentence of the tag. -/
@[stacks 08AI "the functor F ↦ f_*F on quasi-coherent modules"]
noncomputable def quasicoherentDirectImage (f : Y ⟶ X)
    (hqc : DirectImagePreservesQuasicoherence B S hS f) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ⥤
      (SheafOfModules.isQuasicoherentOnSite (affineDirectImageAlgebra B S hS f)).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ moduleDirectImage B S hS f)
    fun M ↦ hqc M.obj M.property

/-- The functor on quasi-coherent modules is the direct image over `A`: composing it with the
inclusion of the quasi-coherent `A`-modules into all `A`-modules recovers
`AlgebraicGeometry.Space.moduleDirectImage` on the nose.  This is what makes the statement of
the equivalence a statement about `f_*`. -/
theorem quasicoherentDirectImage_comp_ι (f : Y ⟶ X)
    (hqc : DirectImagePreservesQuasicoherence B S hS f) :
    quasicoherentDirectImage B S hS f hqc ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ moduleDirectImage B S hS f := rfl

/-- **The first sentence of Stacks 08AI**, as a statement about one affine morphism `f : Y ⟶ X`
of algebraic spaces: direct image over `A = f_*𝒪_Y` preserves quasi-coherence, and the induced
functor from the quasi-coherent `𝒪_Y`-modules to the quasi-coherent `A`-modules is an
equivalence of categories.

By `AlgebraicGeometry.Space.quasicoherentDirectImage_comp_ι` the functor whose invertibility is
asserted is the direct image of Stacks 03D1 itself. -/
def AffineDirectImageEquivalence (f : Y ⟶ X) : Prop :=
  ∃ hqc : DirectImagePreservesQuasicoherence B S hS f,
    (quasicoherentDirectImage B S hS f hqc).IsEquivalence

/-- The statement of the first sentence of Stacks 08AI, in the binders of its source: for every
affine morphism of algebraic spaces over `S`, direct image is an equivalence from the
quasi-coherent `𝒪_Y`-modules onto the quasi-coherent `f_*𝒪_Y`-modules. -/
def AffinePushforwardEquivalence : Prop :=
  ∀ {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X), IsAffineHom B S hS f.hom →
    AffineDirectImageEquivalence B S hS f

end AlgebraicGeometry.Space

end
