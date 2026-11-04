module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.AlgebraPushoutAnySite
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule

/-!
# The module underlying the pullback of an algebra sheaf on an algebraic space

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `A` be a sheaf of commutative `𝒪_X`-algebras on the small étale site of `X`.
`AlgebraicGeometry.Space.algebraPullback` sends `A` to the `𝒪_Y`-algebra
`𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A`, the pushout of `g⁻¹A ⟵ g⁻¹𝒪_X ⟶ 𝒪_Y` in the sheaves of commutative
rings.  This file identifies the `𝒪_Y`-module *underlying* that pullback with an extension of
scalars.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageAlgebra` is the inverse image `g⁻¹A`, read as an algebra
  over `g⁻¹𝒪_X`, i.e. as an object of `Under (g⁻¹𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.underlyingModule_algebraPullback`: **the module underlying `g^*A` is
  the module underlying the pushout of `g⁻¹A` along `g♯`**, on the nose.
* `AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackIso`: **the module underlying `g^*A`
  is the extension of scalars along `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` of the module underlying `g⁻¹A`.**

## Implementation notes

The content is
`Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso_anySite`, instantiated at the
small étale site of `Y`.  Its small-site predecessor cannot be instantiated here:
`AlgebraicGeometry.Space.smallEtaleRingedSite` is a `RingedSite.{u + 1, u, u}`, with objects one
universe above its morphisms and its structure sheaf.  All six instances the `_anySite`
statements carry — pushouts and sheafification of sheaves of commutative rings, `HasSheafCompose`
for `forget₂ CommRingCat RingCat`, sheafification of abelian sheaves, and the two
`WEqualsLocallyBijective` hypotheses — are found by instance search on the small étale site.

Both comparisons with `AlgebraicGeometry.Space.algebraPullback` are definitional:
`CategoryTheory.Under.pushout` sends `x` to `Under.mk (pushout.inr x.hom f)`, which is literally
the sheaf of rings `algebraPullback` builds, and
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_eq_restrictScalars` says the module
underlying an algebra sheaf here is the term that
`Stacks.SheafOfModules.AlgebraPushout.underlyingModule_anySite` names.

**What quasi-coherence of the pullback still needs, and where every input for it is.**  The
remaining field of `AlgebraicGeometry.Space.BaseChangeCompatibility` that is statable without an
anti-equivalence, `algebraPullback_isQuasicoherent`, follows from this file together with
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` — Stacks
03GA, available unconditionally at an arbitrary morphism and an arbitrary quasi-coherent module —
as soon as the right-hand side here is identified with
`(AlgebraicGeometry.Space.modulePullback B S hS g).obj A.underlyingModule`.  That is the step
`Stacks.SheafOfModules.AlgebraPushout.algebraPullbackComparison` records as its own remaining
input: the identification of the module underlying `g⁻¹A` with the inverse image of the module
underlying `A`.

Unlike the universe gap this file closes, that step is *not* missing mathematics.  Writing `f`
for `AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom B S hS g` and `Φ` for
`f.toToposHom.inverseImage`, `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`
is by definition `inverseImageModules f ⋙ extendScalarsFSharp f`, and each factor is already
available:

* *The inverse image of the free rank-one module.*
  `Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso` is
  `SheafOfModules.unit (pullbackRingSheaf J Φ O) ≅ (pullbackModuleFunctor J Φ O).obj
  (SheafOfModules.unit O)` for an **arbitrary** sheaf of rings `O` on an arbitrary site, and is
  `Iso.refl`.  `Stacks.Sheaves.FinitePresentation.inverseImageModulesUnitIso` is only its
  instance at a structure sheaf; no generalisation of it is needed.
* *Inverse image commutes with restriction of scalars.*
  `Stacks.Sheaves.RingedToposModules.pullbackModuleFunctorRestrictScalarsIso` is
  `pullbackModuleFunctor J Φ S ⋙ SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α) ≅
  SheafOfModules.restrictScalars α ⋙ pullbackModuleFunctor J Φ S'`, for arbitrary sheaves of
  rings and arbitrary `α`.  This is the semilinear statement, and it is proved.
* *The two extensions of scalars agree.*
  `Stacks.Sheaves.RingedToposModules.extendScalarsFSharp_eq_changeOfRings` says
  `extendScalarsFSharp f = Stacks.FlatChangeOfRings.extendScalars (fSharpCommRingSheaf f)`, by
  `rfl`, which is exactly the functor appearing on the right-hand side here.

Three of the four comparisons that chain these at the small étale site hold by `rfl`:
`structurePullbackMap B S hS g = fSharpCommRingSheaf f`; the sheaf of rings underlying the
inverse image of a sheaf of commutative rings is the inverse-image sheaf of rings,
`Stacks.SheafOfModules.Tensor.ringSheaf ((ringSheafPullback B S hS g).obj R) =
pullbackRingSheaf _ Φ (Stacks.SheafOfModules.Tensor.ringSheaf R)`; and
`underlyingModule_algebraPullback` above.

What is left is the same comparison **on morphisms**:
`Stacks.FlatChangeOfRings.ringSheafMap ((ringSheafPullback B S hS g).map a)` and
`pullbackRingSheafMap _ Φ (Stacks.FlatChangeOfRings.ringSheafMap a)` are two spellings of one
morphism of sheaves of rings which are *not* definitionally equal — the first goes through
`sheafCompose`, the second through `Sheaf.ringObjMap`.  They agree on underlying sheaves of
sets, which is
`Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMap`, so what the chain needs is
that equality transported along the faithfulness of `sheafCompose _ (forget RingCat)`.  That one
lemma, and the assembly of the three isomorphisms above, is the whole remaining distance to
`algebraPullback_isQuasicoherent`.

The scheme-level theorem `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_obj`
takes a different route, localizing to affine opens and transporting along
`Stacks.AffineAlgebraEquivalence.algebraPullbackComp`, a composition comparison that
`AlgebraicGeometry.Space.algebraPullback` does not have.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The inverse image `g⁻¹A` of a sheaf of commutative `𝒪_X`-algebras, read as a sheaf of
commutative algebras over `g⁻¹𝒪_X`.  This is the object the pushout defining
`AlgebraicGeometry.Space.algebraPullback` is taken of. -/
def inverseImageAlgebra (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    Under ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2)) :=
  Under.mk ((ringSheafPullback B S hS g).map A.hom)

/-- The sheaf of rings underlying `g⁻¹A` is the inverse image of the sheaf of rings underlying
`A`. -/
@[simp]
theorem inverseImageAlgebra_right (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (inverseImageAlgebra B S hS g A).right = (ringSheafPullback B S hS g).obj A.right :=
  rfl

/-- The sheaf of rings underlying the pullback algebra is the pushout of `g⁻¹A` along
`g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`, at the spelling `CategoryTheory.Under.pushout` produces. -/
theorem algebraPullback_obj_right_eq (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    ((algebraPullback B S hS g).obj A).right =
      ((Under.pushout (structurePullbackMap B S hS g)).obj
        (inverseImageAlgebra B S hS g A)).right :=
  rfl

/-- **The module underlying the pullback algebra is the module underlying the pushout.**  The
two are the same term: `CategoryTheory.Under.pushout` sends an object to
`Under.mk (pushout.inr _ _)`, which is the sheaf of rings `AlgebraicGeometry.Space.algebraPullback`
builds, and the module underlying an algebra sheaf is by
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_eq_restrictScalars` the restriction of
scalars along its structure morphism of the free module of rank one. -/
theorem underlyingModule_algebraPullback (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    ((algebraPullback B S hS g).obj A).underlyingModule =
      Stacks.SheafOfModules.AlgebraPushout.underlyingModule_anySite.{u, u + 1, u}
        ((Under.pushout (structurePullbackMap B S hS g)).obj
          (inverseImageAlgebra B S hS g A)) :=
  rfl

/-- **The module underlying the pullback `g^*A` of an algebra sheaf is the extension of scalars
along `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` of the module underlying `g⁻¹A`.**

This is the extension-of-scalars half of the identification of the module underlying `g^*A`
with the pullback of the module underlying `A`, which is what quasi-coherence of `g^*A` needs;
the inverse-image half is not available, and the module docstring of this file says precisely
what it would be. -/
def underlyingModuleAlgebraPullbackIso (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    ((algebraPullback B S hS g).obj A).underlyingModule ≅
      (Stacks.FlatChangeOfRings.extendScalars (structurePullbackMap B S hS g)).obj
        (Stacks.SheafOfModules.AlgebraPushout.underlyingModule_anySite.{u, u + 1, u}
          (inverseImageAlgebra B S hS g A)) :=
  Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso_anySite.{u, u + 1, u}
    (structurePullbackMap B S hS g) (inverseImageAlgebra B S hS g A)

end AlgebraicGeometry.Space

end
