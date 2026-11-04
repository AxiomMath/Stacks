module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayInternalHomMul
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 0996(3), in the derived category

Let `(𝒞, 𝒪)` be a ringed site, let `f`, `g` be global sections of `𝒪` and let `K ∈ D(𝒪)`. Then

`R𝑆heafHom_𝒪(𝒪_f, R𝑆heafHom_𝒪(𝒪_g, K)) = R𝑆heafHom_𝒪(𝒪_{g f}, K)`.

## Main results

* `AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_awayComplex`:
  `SheafHom•_𝒪(𝒪_f, I)` is K-injective when `I` is, which is what makes the left-hand side of
  the clause the *iterated* derived internal Hom.

## Main definitions

* `AlgebraicGeometry.RingedSite.awaySheafHomComplexMulCurryIso`: the displayed identity of the
  source's proof, `SheafHom•_𝒪(𝒪_f, SheafHom•_𝒪(𝒪_g, I)) = SheafHom•_𝒪(𝒪_{g f}, I)`, for the
  [Stacks, Tag 0A8X] internal Hom complex.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_awayMulCurryIso`: **Stacks Tag 0996(3)**.

## Implementation notes

`AwayInternalHomMul.lean` proves the same displayed identity for the `MonoidalClosed.ihom`
realisation of the internal Hom complex. That realisation is a different one from the
[Stacks, Tag 0A8X] complex `AlgebraicGeometry.RingedSite.sheafHomComplex`, and the tree relates
the two for single sheaves of modules only — see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/CurryingForComplexesOfModules.lean` and of `StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedCurryingOnARingedSpace.lean`. The
difference matters here: reading the left-hand side as the *iterated* derived internal Hom needs
the inner complex `SheafHom•_𝒪(𝒪_g, 𝓘•)` to be K-injective, which is
`AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_awayComplex` — [Stacks, Tag 0A96] for
the Tag 0A8X complex — and is available in that spelling only. So this file states the clause
there, and that is where the tag is registered.

The identity itself is [Stacks, Tag 0A90] in the Tag 0A8X spelling,
`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso`, followed by `𝒪_f ⊗_𝒪 𝒪_g = 𝒪_{f g}` —
`AlgebraicGeometry.RingedSite.awayComplexTensorIso` — carried into the contravariant slot of the
internal Hom complex by `AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor`.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.SheafOfModules

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  (f g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **`SheafHom•_𝒪(𝒪_f, I)` is K-injective whenever `I` is.** This is the step the source's
proof of [Stacks, Tag 0996(3)] cites and does not prove: it is what makes
`SheafHom•_𝒪(𝒪_g, 𝓘•)` a complex one may take derived internal Hom out of again, so that the
left-hand side of the clause is the *iterated* derived internal Hom.

It is [Stacks, Tag 0A96] applied to the K-flatness of `𝒪_f` in degree zero,
`AlgebraicGeometry.RingedSite.isKFlat_awayComplex`, whose own input is
`isFlatMap_toAwaySheaf`. Nothing is assumed of `f`. -/
instance isKInjective_sheafHomComplex_awayComplex
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    (sheafHomComplex X (awayComplex X f) I).obj.IsKInjective :=
  isKInjective_sheafHomComplex_of_isKFlat X (awayComplex X f) I (isKFlat_awayComplex X f)

/-- **The displayed identity in the proof of Stacks Tag 0996(3)**, for the Tag 0A8X internal Hom
complex: `SheafHom•_𝒪(𝒪_f, SheafHom•_𝒪(𝒪_g, I)) = SheafHom•_𝒪(𝒪_{g f}, I)`, over `𝒪`
throughout and for an arbitrary complex `I` of sheaves of `𝒪`-modules. -/
def awaySheafHomComplexMulCurryIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (sheafHomComplex X (awayComplex X f)
        (sheafHomComplex X (awayComplex X g) I).obj).obj ≅
      (sheafHomComplex X (awayComplex X (mulGlobalSection X f g)) I).obj :=
  sheafHomTensorCurryIso X (awayComplex X f) (awayComplex X g) I ≪≫
    ((sheafHomComplexBifunctor X).mapIso (awayComplexTensorIso X f g).op).app I

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Tag 0996(3).** Let `(𝒞, 𝒪)` be a ringed site, let `f` and `g` be global sections of
`𝒪` and let `K ∈ D(𝒪)`. Then

`R𝑆heafHom_𝒪(𝒪_f, R𝑆heafHom_𝒪(𝒪_g, K)) = R𝑆heafHom_𝒪(𝒪_{g f}, K)`.

Computing `K` by a K-injective complex `I` of sheaves of `𝒪`-modules, `SheafHom•_𝒪(𝒪_g, I)`
represents `R𝑆heafHom_𝒪(𝒪_g, K)` and is itself K-injective as a complex of sheaves of
`𝒪`-modules — `AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_awayComplex` — so
`SheafHom•_𝒪(𝒪_f, SheafHom•_𝒪(𝒪_g, I))` represents the left-hand side; and
`SheafHom•_𝒪(𝒪_{g f}, I)` represents the right-hand side. Nothing is assumed of `f` or `g`. -/
@[stacks 0996 "part (3)"]
def derivedSheafHom_awayMulCurryIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.obj (sheafHomComplex X (awayComplex X f)
        (sheafHomComplex X (awayComplex X g) I).obj).obj ≅
      DerivedCategory.Q.obj (sheafHomComplex X (awayComplex X (mulGlobalSection X f g)) I).obj :=
  DerivedCategory.Q.mapIso (awaySheafHomComplexMulCurryIso X f g I)

end Derived

end AlgebraicGeometry.RingedSite

end
