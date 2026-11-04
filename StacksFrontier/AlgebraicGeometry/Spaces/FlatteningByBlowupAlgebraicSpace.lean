module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningBlowupRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.FlatteningOverAffine

/-!
# Flattening by blowing up for algebraic spaces

Let `A` be a quasi-compact and quasi-separated algebraic space, let `f : X ⟶ A` be locally of
finite presentation with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite
type and let `U ⊆ A` be a quasi-compact open subspace such that `F_U` is of finite presentation
and flat over `U`.  Then there is a `U`-admissible blowup `A' ⟶ A` such that the strict
transform of `F` is an `𝒪_{X ×_A A'}`-module of finite presentation, flat over `A'`.  This is
[Stacks, Tag 087C].

## Main results

* `AlgebraicGeometry.Space.exists_isFlatteningBlowup`: Stacks 087C, over Stacks 07VR
  (through which Stacks 087B is proved).

## Implementation notes

The proof is the source's.  The source is replaced by a surjective étale chart which is a
quasi-compact scheme; an affine surjective étale chart `W` of the base is chosen; the case of an
affine base, which is Stacks 0815 read on algebraic spaces
(`AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_isAffineSpace`), flattens over `W`;
Stacks 087B descends the centre to `A`; and the blowup of `A` in that centre is recognized on the
étale cover.  See `AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_schemeCase`.

## References

* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 087B](https://stacks.math.columbia.edu/tag/087B)
-/

/- The only hypothesis of `exists_isFlatteningBlowup` below is `h07VR`, the statement of
Stacks 07VR.  It is a theorem of this library, `exists_integralFiniteSystem_of_isFinite`;
supplying it gives Stacks 087C with no hypotheses beyond the source's, namely
`exists_isFlatteningBlowup_of_isLocallyOfFinitePresentation` in
`FlatteningByBlowupAlgebraicSpaceUnconditional.lean`.  Stacks 0865 part (2) and 0868 part (1) are
used through `exists_isBlowupAlong_sum_isFinitePresentation_isFlatOver` and need nothing
further. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 087C, flattening by blowing up, over Stacks 07VR (`h07VR`).**
Let `A` be a quasi-compact and quasi-separated algebraic space over `S`, let `f : X ⟶ A` be
locally of finite presentation
with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite type and let `U ⊆ A`
be a quasi-compact open subspace such that `F_U` is of finite presentation and flat over `U`.
Then there is a blowup `b : A' ⟶ A` in a finitely presented closed subspace `Z` disjoint from
`U` — a `U`-admissible blowup — such that the strict transform of `F` is of finite presentation
and flat over `A'`. -/
theorem exists_isFlatteningBlowup (hZ : B.Contains (⊤_ Scheme.{u}))
    {A : AlgebraicSpaces B S hS} (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1) (U : OpenSubspaces B S hS A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b :=
  exists_isFlatteningBlowup_of_schemeCase hZ hAqc hAqs U hUqc
    (fun _ _ hA _ f' hqc hlfp G hGqc hGft U' hU'qc hGfp hGflat =>
      exists_isFlatteningBlowup_of_isAffineSpace hA f' hqc hlfp G hGqc hGft U' hU'qc hGfp hGflat)
    h07VR f hXqc hf F hFqc hFft hFUfp hFUflat

end AlgebraicGeometry.Space

end
