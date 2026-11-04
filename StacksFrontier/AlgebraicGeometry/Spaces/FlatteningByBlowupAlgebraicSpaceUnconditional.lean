module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningByBlowupAlgebraicSpace

/-!
# Flattening by blowing up for algebraic spaces

Let `A` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let
`f : X ⟶ A` be locally of finite presentation with `X` quasi-compact, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `U ⊆ A` be a quasi-compact open subspace such that `F_U` is
of finite presentation and flat over `U`. Then there is a `U`-admissible blowup `A' ⟶ A` such
that the strict transform of `F` is an `𝒪_{X ×_A A'}`-module of finite presentation, flat over
`A'`. This is [Stacks, Tag 087C].

## Main results

* `AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_isLocallyOfFinitePresentation`:
  Stacks 087C.

## Implementation notes

The proof is `AlgebraicGeometry.Space.exists_isFlatteningBlowup`, whose only input, Stacks 07VR
(through which Stacks 087B is proved), is
`AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite`.

## References

* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Flattening by blowing up for algebraic spaces.** Let `A` be a quasi-compact and
quasi-separated algebraic space over `S`, let `f : X ⟶ A` be locally of finite presentation with
`X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite type and let `U ⊆ A` be a
quasi-compact open subspace such that `F_U = F|_{X ×_A U}` is of finite presentation and flat
over `U`. Then there is a blowup `b : A' ⟶ A` in a finitely presented closed subspace `Z`
disjoint from `U` (a `U`-admissible blowup) such that the strict transform of `F` with respect
to `b` is an `𝒪_{X ×_A A'}`-module of finite presentation, flat over `A'`. -/
@[stacks 087C]
theorem exists_isFlatteningBlowup_of_isLocallyOfFinitePresentation
    {A : AlgebraicSpaces B S hS} (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hAqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal A.1)
    (U : OpenSubspaces B S hS A.1) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b :=
  exists_isFlatteningBlowup B.contains_terminal hAqc hAqs U hUqc
    (fun g hX hY hfin hYqc hYqs =>
      exists_integralFiniteSystem_of_isFinite B S hS g hX hY hfin hYqc hYqs)
    f hXqc hf F hFqc hFft hFUfp hFUflat

end AlgebraicGeometry.Space

end
