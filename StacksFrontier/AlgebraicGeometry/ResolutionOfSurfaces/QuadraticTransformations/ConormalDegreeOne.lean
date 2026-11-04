module

public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwists
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DifferentialsVanishing

/-!
# The conormal sheaf of an exceptional curve of the first kind has degree one

`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` says that `E ⊆ X` is an
exceptional curve of the first kind: an effective Cartier divisor `D` together with an isomorphism
`e : 𝐏¹_k ≅ E` of its subscheme with the projective line under which the *normal* sheaf of `E`
pulls back to `𝒪(-1)`. This file reads the same hypothesis on the *conormal* sheaf,
`e^* 𝒞_{E/X} ≅ 𝒪(1)`, and combines it with the conormal comparison of `ConormalComparison.lean`
and the vanishing of `DifferentialsVanishing.lean`, giving a step of the proof of
[Stacks, Tag 0C5R] (Resolution of Surfaces, Lemma 54.17.1) for exceptional curves of the first
kind.

The two applications assume `Stacks.ResolutionOfSurfaces.NonzeroTwistEndoIsIso` (the equality
clause of part (5) of [Stacks, Tag 0B40] at the projective line), and the second also
`Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow` (the second arrow of [Stacks, Tag 067L]
with two clauses of that tag); both are quantified over all of their own data. In the second
application the degree of `𝒞_{E/Y'}` is the explicit hypothesis `α`.

## Main results

* `Stacks.ResolutionOfSurfaces.nonempty_pullback_conormalSheaf_iso_projectiveLineTwist` —
  `e^* 𝒞_{E/X} ≅ 𝒪(1)` for an exceptional curve of the first kind.
* `Stacks.ResolutionOfSurfaces.nonempty_pullback_comp_conormalSheaf_iso_projectiveLineTwist` —
  the same read through a morphism `g : E ⟶ E'` of two such curves with compatible
  presentations: `e^* g^* 𝒞_{E'/Y'} ≅ 𝒪(1)`.
* `Stacks.ResolutionOfSurfaces.isIso_immersionConormalSheafMap_of_isExceptionalCurveOfFirstKind`
  — for two exceptional curves of the first kind `E ⊆ X'` and `E' ⊆ Y'` with compatible
  presentations as `𝐏¹_k`, a morphism `g : E ⟶ E'` and a morphism `f' : X' ⟶ Y'` making the
  square commute, the conormal comparison map `g^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}` of [Stacks, Tag 01R4]
  is an isomorphism as soon as it is nonzero.
* `Stacks.ResolutionOfSurfaces.isZero_pullback_relativeDifferentials_of_isExceptionalCurve` —
  for an exceptional curve of the first kind `E ⊆ X'` and an immersion `j : E ⟶ Y'` with
  `i ≫ f' = j` whose conormal sheaf also has degree one on `E`, a nonzero first arrow of the
  conormal sequence of [Stacks, Tag 067L] forces `i^* Ω_{X'/Y'} = 0`.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open RingedSpaceModuleAdjunction (toShHomIso)
open Stacks.RingedSpace (modulePullbackComp modulePullbackCongr)

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The conormal sheaf of an exceptional curve of the first kind -/

/-- For an exceptional curve of the first kind `E ⊆ X` with presentation `e : 𝐏¹_k ≅ E`, the
pullback `e^* 𝒞_{E/X}` of its conormal sheaf is isomorphic to the first twist `𝒪(1)`. -/
public theorem nonempty_pullback_conormalSheaf_iso_projectiveLineTwist (k : Type u) [Field k]
    {X : Scheme.{u}} {D : X.IdealSheafData} {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Nonempty ((modulePullback (toShHomIso e).hom).obj
      (Stacks.Conormal.conormalSheaf D.subschemeι) ≅ projectiveLineTwist k 1) := by
  obtain ⟨φ⟩ := hE.nonempty_pullback_negativeTwist_iso_twistingSheaf
  exact ⟨(modulePullback (toShHomIso e).hom).mapIso
    (Stacks.CartierConormal.conormalSheafIsoNegativeTwist D) ≪≫ φ⟩

/-- For an exceptional curve of the first kind `E' ⊆ Y'` with presentation `e' : 𝐏¹_k ≅ E'`,
a scheme `E` with an isomorphism `e : 𝐏¹_k ≅ E`, and a morphism `g : E ⟶ E'`
with `e ≫ g = e'`, the pullback `e^* g^* 𝒞_{E'/Y'}` is isomorphic to `𝒪(1)`. -/
public theorem nonempty_pullback_comp_conormalSheaf_iso_projectiveLineTwist (k : Type u)
    [Field k] {Y' : Scheme.{u}} {E : Scheme.{u}} {D' : Y'.IdealSheafData}
    {e : projectiveLineProj k ≅ E} {e' : projectiveLineProj k ≅ D'.subscheme}
    (g : E ⟶ D'.subscheme) (he : e.hom ≫ g = e'.hom)
    (hE' : D'.IsExceptionalCurveOfFirstKind k e') :
    Nonempty ((modulePullback (toShHomIso e).hom).obj
      ((modulePullback g.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf D'.subschemeι)) ≅
        projectiveLineTwist k 1) := by
  obtain ⟨φ⟩ := nonempty_pullback_conormalSheaf_iso_projectiveLineTwist k hE'
  exact ⟨(RingedSpace.modulePullbackComp (toShHomIso e).hom g.toLRSHom.toShHom).app _ ≪≫
    (RingedSpace.modulePullbackCongr
      (show (toShHomIso e).hom ≫ g.toLRSHom.toShHom = (toShHomIso e').hom from
        congrArg (fun p : projectiveLineProj k ⟶ D'.subscheme => p.toLRSHom.toShHom) he)).app _
    ≪≫ φ⟩

/-! ### The conormal comparison map and the relative differentials -/

/-- Let `E ⊆ X'` and `E' ⊆ Y'` be exceptional curves of the first kind with presentations
`e : 𝐏¹_k ≅ E` and `e' : 𝐏¹_k ≅ E'`, let `g : E ⟶ E'` be a morphism with `e ≫ g = e'`, and let
`f' : X' ⟶ Y'` make the square `i ≫ f' = g ≫ i'` commute. If the conormal comparison map

`g^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}`

of [Stacks, Tag 01R4] is nonzero, it is an isomorphism. The hypothesis `hk` is the equality
clause of part (5) of [Stacks, Tag 0B40] at the projective line. -/
public theorem isIso_immersionConormalSheafMap_of_isExceptionalCurveOfFirstKind (k : Type u)
    [Field k] (hk : NonzeroTwistEndoIsIso k) {X' Y' : Scheme.{u}} (f' : X' ⟶ Y')
    {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    {e : projectiveLineProj k ≅ D.subscheme} {e' : projectiveLineProj k ≅ D'.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (hE' : D'.IsExceptionalCurveOfFirstKind k e')
    (g : D.subscheme ⟶ D'.subscheme) (he : e.hom ≫ g = e'.hom)
    (comm : D.subschemeι ≫ f' = g ≫ D'.subschemeι)
    (hne : Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      (Stacks.Immersion.toShHom_square comm) ≠ 0) :
    IsIso (Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      (Stacks.Immersion.toShHom_square comm)) := by
  obtain ⟨α⟩ := nonempty_pullback_comp_conormalSheaf_iso_projectiveLineTwist k g he hE'
  obtain ⟨β⟩ := nonempty_pullback_conormalSheaf_iso_projectiveLineTwist k hE
  exact isIso_immersionConormalSheafMap_of_ne_zero k hk 1 D.subschemeι D'.subschemeι g f'
    comm e α β hne

/-- Let `E ⊆ X'` be an exceptional curve of the first kind with presentation `e : 𝐏¹_k ≅ E`, let
`f' : X' ⟶ Y'` be a morphism and let `j : E ⟶ Y'` be an immersion with `i ≫ f' = j` whose
conormal sheaf also has degree one on `E`, which is the datum `α`. If the first arrow

`𝒞_{E/Y'} ⟶ 𝒞_{E/X'}`

of the conormal sequence of [Stacks, Tag 067L] is nonzero then `i^* Ω_{X'/Y'}` is a zero object.
The hypotheses `hk` and `hsec` are the equality clause of part (5) of [Stacks, Tag 0B40] at the
projective line and the second arrow of [Stacks, Tag 067L] with two clauses of that tag. -/
public theorem isZero_pullback_relativeDifferentials_of_isExceptionalCurve (k : Type u) [Field k]
    (hk : NonzeroTwistEndoIsIso k) (hsec : ConormalSequenceSecondArrow.{u})
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') {D : X'.IdealSheafData}
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (j : D.subscheme ⟶ Y') [IsImmersion j] (h : D.subschemeι ≫ f' = j)
    (α : (modulePullback (toShHomIso e).hom).obj (Stacks.Conormal.conormalSheaf j) ≅
      projectiveLineTwist k 1)
    (hne : Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap D.subschemeι j f' h ≠ 0) :
    IsZero ((Scheme.Modules.pullback D.subschemeι).obj
      (Scheme.Hom.relativeDifferentials f')) := by
  obtain ⟨β⟩ := nonempty_pullback_conormalSheaf_iso_projectiveLineTwist k hE
  exact isZero_pullback_relativeDifferentials_of_ne_zero k hk hsec 1 D.subschemeι j f' h e α β hne

end Stacks.ResolutionOfSurfaces

end
