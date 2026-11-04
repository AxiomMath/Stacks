module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTensorSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingForComplexesOfModules
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.TensorHomAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Internal Hom out of two localizations is internal Hom out of one

Let `(𝒞, 𝒪)` be a ringed site and let `f`, `g` be global sections of `𝒪`. For every complex `I`
of sheaves of `𝒪`-modules,

`SheafHom•_𝒪(𝒪_f, SheafHom•_𝒪(𝒪_g, I)) = SheafHom•_𝒪(𝒪_{g f}, I)`,

the internal Hom complexes being taken over `𝒪` throughout. This is the displayed identity in
the proof of [Stacks, Tag 0996(3)], and with it that clause:

`R𝑆heafHom_𝒪(𝒪_f, R𝑆heafHom_𝒪(𝒪_g, K)) = R𝑆heafHom_𝒪(𝒪_{g f}, K)` for `K ∈ D(𝒪)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayComplex`: `𝒪_f`, as a complex of `𝒪`-modules concentrated
  in degree zero.
* `AlgebraicGeometry.RingedSite.awayComplexTensorIso`: `Tot(𝒪_f ⊗_𝒪 𝒪_g) = 𝒪_{f g}` for those
  complexes.
* `AlgebraicGeometry.RingedSite.awaySheafHomComplexMulIso`: **the displayed identity above**, at
  the level of complexes and for an arbitrary complex `I`.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_awayMulIso`: its image in `D(𝒪)` for a
  K-injective `I`. Tag 0996(3) itself is registered on
  `AlgebraicGeometry.RingedSite.derivedSheafHom_awayMulCurryIso` of
  `AwayInternalHomMulDerived.lean`, which states the clause for the [Stacks, Tag 0A8X] internal
  Hom complex — the spelling in which the inner complex is known K-injective.

## Implementation notes

Two inputs, and no computation. Stacks 0A90 — `sheafHomTensorIso` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/CurryingForComplexesOfModules.lean` — is
`SheafHom•(K, SheafHom•(L, M)) ≅ SheafHom•(Tot(K ⊗ L), M)`; and
`AlgebraicGeometry.RingedSite.awayTensorSheafIso` is `𝒪_f ⊗_𝒪 𝒪_g = 𝒪_{f g}`. The
bridge between them is that the total complex of the tensor double complex of two complexes
concentrated in degree zero is concentrated in degree zero, on the tensor product of the two
sheaves — `HomologicalComplex.mapBifunctorSingleIso`, which applies because
`Stacks.Cohomology.SheafHomComplexCurrying.tensorComplex` is definitionally
`HomologicalComplex.mapBifunctor` of `Stacks.SheafOfModules.Tensor.sheafTensor`. Internal Hom is
then carried along the resulting isomorphism of complexes by `MonoidalClosed.preIso`.

The comparison is canonical rather than merely some isomorphism, by the pins of its two inputs:
`CategoryTheory.MonoidalClosed.uncurry_ihomTensorIso_hom` for the currying isomorphism, and
`AlgebraicGeometry.RingedSite.awayTensorSectionIso_hom_tmul` — a pure tensor goes to the product
of the images of its factors — for the tensor identity.

The monoidal and closed structures on complexes of `𝒪`-modules are the ones
`Stacks.Cohomology.SheafHomComplexCurrying` pins by `letI`, re-declared here as local instances
so that `sheafHomComplex` and `tensorComplex`, which are abbreviations elaborated against them,
mean the same thing here as there; `MonoidalClosed.preIso` needs the structures themselves and
not only those abbreviations, which is why the graded-object instances are re-declared too.

The derived clause is the image of the complex-level identity under `DerivedCategory.Q`, with
`I` K-injective, which is the shape the neighbouring clause
`AlgebraicGeometry.RingedSite.derivedSheafHom_coextendScalarsIso` of `HomIntoCoextension.lean`
takes. The hypothesis is the source's own "let `𝓘•` be a K-injective complex of `𝒪`-modules
representing `K`": with it `SheafHom•_𝒪(𝒪_{g f}, 𝓘•)` represents `R𝑆heafHom_𝒪(𝒪_{g f}, K)`, and
`SheafHom•_𝒪(𝒪_g, 𝓘•)` represents `R𝑆heafHom_𝒪(𝒪_g, K)`. Reading the left-hand side as the
*iterated* derived internal Hom uses one further fact, the one the source's proof of this clause
cites and does not prove: that `SheafHom•_𝒪(𝒪_g, 𝓘•)` is again K-injective as a complex of
`𝒪`-modules. That fact **is** in the development, as
`AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_awayComplex` of
`AwayInternalHomMulDerived.lean` —
[Stacks, Tag 0A96] applied to the K-flatness of `𝒪_g` in degree zero — but for the
[Stacks, Tag 0A8X] internal Hom complex `AlgebraicGeometry.RingedSite.sheafHomComplex`, not for
the `MonoidalClosed.ihom` realisation `sheafHomComplex` of this file, and no comparison of the
two *at the level of complexes* is in the development. So the derived clause is stated for the
Tag 0A8X complex instead, in `AwayInternalHomMulDerived.lean`, where that K-injectivity is
available; the complex-level identity above is independent of it and holds for every `I`.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
* [Stacks Project, Tag 093Z](https://stacks.math.columbia.edu/tag/093Z)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.SheafOfModules
open Stacks.Cohomology.SheafHomComplexCurrying

universe u

attribute [local instance] CochainComplex.monoidalClosed CochainComplex.symmetricCategory

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  (f g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-! The monoidal, symmetric and closed structures on `Mod(𝒪)`, and the graded-object
hypotheses of the monoidal structure on `Comp(Mod(𝒪))`, are the ones
`Stacks.Cohomology.SheafHomComplexCurrying` seats for a ringed site.  Each is **named here with
its site written out**, and the graded-object ones are handed that file's own term rather than
re-synthesized, exactly as that file's ringed-space section does and for the same reason: over
the site of a `RingedSite.{u, u, u}` the universe of the site and the universe of the sections
of `𝒪` coincide, so a structure stated at `max u v w` leaves instance search to solve
`max ?u ?v ?w =?= u`, which it cannot; taken that way `GradedObject.HasTensor` is attacked with
the module universe still unknown and the search for the coproducts it unfolds to overruns.
None of them is an assumption: they are the same instances as there. -/

/-- The monoidal structure on `Mod(𝒪)` whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`, with the site written out. -/
local instance monoidalSite : MonoidalCategory (Mod X.O) :=
  _root_.SheafOfModules.monoidalCategorySheafTensor (J := X.J) X.O

/-- `⊗_𝒪` is symmetric, named for the same reason. -/
local instance symmetricSite : SymmetricCategory (Mod X.O) :=
  _root_.SheafOfModules.symmetricCategorySheafTensor (J := X.J) X.O

/-- `⊗_𝒪` is bilinear on morphisms, named for the same reason. -/
local instance monoidalPreadditiveSite : MonoidalPreadditive (Mod X.O) :=
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor (J := X.J) X.O

/-- `Mod(𝒪)` is monoidal closed, named for the same reason. -/
local instance monoidalClosedSite : MonoidalClosed (Mod X.O) :=
  _root_.SheafOfModules.monoidalClosedSheafTensor (J := X.J) X.O

/-- `- ⊗_𝒪 𝒢` commutes with colimits, named for the same reason. -/
local instance preservesColimitTensorRightSite {T : Type*} [Category T] (F : T ⥤ Mod X.O)
    (N : Mod X.O) : PreservesColimit F (tensorRight N) :=
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor (J := X.J) X.O F N

/-- The total complexes of the tensor double complexes of complexes of `𝒪`-modules exist. -/
local instance hasMapBifunctorMod : ∀ K L : Complexes X.O,
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ) :=
  Stacks.Cohomology.SheafHomComplexCurrying.hasMapBifunctor (J := X.J) X.O

/-- The graded tensor products of `𝒪`-modules exist; the same instance as in
`Stacks.Cohomology.SheafHomComplexCurrying`, named rather than synthesized because instance
search solves the `∀`-quantified form only in applied form. -/
local instance hasTensorMod : ∀ A B : GradedObject ℤ (Mod X.O), GradedObject.HasTensor A B :=
  hasTensor (J := X.J) X.O

/-- The left-bracketed triple graded tensor products of `𝒪`-modules are good. -/
local instance hasGoodTensor₁₂TensorMod : ∀ A B C : GradedObject ℤ (Mod X.O),
    GradedObject.HasGoodTensor₁₂Tensor A B C := hasGoodTensor₁₂Tensor (J := X.J) X.O

/-- The right-bracketed triple graded tensor products of `𝒪`-modules are good. -/
local instance hasGoodTensorTensor₂₃Mod : ∀ A B C : GradedObject ℤ (Mod X.O),
    GradedObject.HasGoodTensorTensor₂₃ A B C := hasGoodTensorTensor₂₃ (J := X.J) X.O

/-- A morphism out of a fourfold graded tensor product of `𝒪`-modules is determined on the
summands. -/
local instance hasTensor₄ObjExtMod : ∀ A B C D : GradedObject ℤ (Mod X.O),
    GradedObject.HasTensor₄ObjExt A B C D := hasTensor₄ObjExt (J := X.J) X.O

/-- `𝒪_f`, as a complex of `𝒪`-modules concentrated in degree zero. -/
abbrev awayComplex : Complexes X.O :=
  (CochainComplex.singleFunctor (Mod X.O) 0).obj (awayModule X f)

/-- **`Tot(𝒪_f ⊗_𝒪 𝒪_g) = 𝒪_{f g}`** for the complexes concentrated in degree zero: the total
complex of the tensor double complex of two such complexes is concentrated in degree zero, on
the tensor product of the two sheaves, which is `𝒪_{f g}`. -/
def awayComplexTensorIso :
    awayComplex X (mulGlobalSection X f g) ≅
      tensorComplex X.O (awayComplex X f) (awayComplex X g) :=
  ((CochainComplex.singleFunctor (Mod X.O) 0).mapIso (awayTensorSheafIso X f g)).symm ≪≫
    (HomologicalComplex.mapBifunctorSingleIso (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (awayModule X f) (awayModule X g)).symm

/-- **The displayed identity in the proof of Stacks Tag 0996(3)**, at the level of complexes:
`SheafHom•_𝒪(𝒪_f, SheafHom•_𝒪(𝒪_g, I)) = SheafHom•_𝒪(𝒪_{g f}, I)`, over `𝒪` throughout and for
an arbitrary complex `I` of sheaves of `𝒪`-modules. It is Stacks 0A90 followed by
`𝒪_f ⊗_𝒪 𝒪_g = 𝒪_{f g}`. -/
def awaySheafHomComplexMulIso (I : Complexes X.O) :
    Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O (awayComplex X f)
        (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O (awayComplex X g) I) ≅
      Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O
        (awayComplex X (mulGlobalSection X f g)) I :=
  Stacks.Cohomology.SheafHomComplexCurrying.sheafHomTensorIso X.O
      (awayComplex X f) (awayComplex X g) I ≪≫
    (MonoidalClosed.preIso (awayComplexTensorIso X f g)).app I

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The image in `D(𝒪)` of the complex-level identity above, for a K-injective `I`.

This is **not** where [Stacks, Tag 0996(3)] is registered, and the reason is the one the
implementation notes give: reading the left-hand side as the *iterated* derived internal Hom
needs `SheafHom•_𝒪(𝒪_g, 𝓘•)` to be K-injective, and that is
`AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_awayComplex`, available for the
[Stacks, Tag 0A8X] internal Hom complex and not for the `MonoidalClosed.ihom` realisation used
here. The clause is
`AlgebraicGeometry.RingedSite.derivedSheafHom_awayMulCurryIso` of
`AwayInternalHomMulDerived.lean`, stated in that spelling. -/
def derivedSheafHom_awayMulIso (I : Complexes X.O) [I.IsKInjective] :
    DerivedCategory.Q.obj
        (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O (awayComplex X f)
          (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O
            (awayComplex X g) I)) ≅
      DerivedCategory.Q.obj
        (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O
          (awayComplex X (mulGlobalSection X f g)) I) :=
  DerivedCategory.Q.mapIso (awaySheafHomComplexMulIso X f g I)

/-- The derived comparison of Tag 0996(3) is the image of the complex-level comparison. -/
theorem derivedSheafHom_awayMulIso_eq (I : Complexes X.O) [I.IsKInjective] :
    DerivedCategory.Q.mapIso (awaySheafHomComplexMulIso X f g I) =
      derivedSheafHom_awayMulIso X f g I :=
  rfl

end Derived

end AlgebraicGeometry.RingedSite

end
