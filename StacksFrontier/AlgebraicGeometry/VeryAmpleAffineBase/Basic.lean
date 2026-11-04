module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.AffineBase
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne

/-!
# Relative very ampleness over an affine base: the projective bundle is an absolute `Proj`

Stacks Tag 02NP says that a relatively very ample invertible sheaf on a scheme of finite type over
an affine base is the hyperplane sheaf pulled back along an immersion into a finite-dimensional
projective space over that base. Its proof opens by writing `S = Spec R` and reading the
projective bundle `𝐏(E)` of the very ampleness hypothesis as the absolute homogeneous spectrum
`Proj(Sym_R M)`; the rest of the argument is a choice of finitely many degree-one coordinates in
that graded ring. This file performs the first step and names the second.

## Main definitions

* `Stacks.VeryAmpleAffineBase.topChart`: the chart of a relative `Proj` over the whole of an
  affine base, which is an isomorphism.
* `Stacks.VeryAmpleAffineBase.projStructureHom`: the structure morphism to `S` of the absolute
  `Proj` of the graded ring of global sections.
* `Stacks.VeryAmpleAffineBase.ProjCoordinateCut`: **the one input Stacks Tag 02NP still owes.**
  `StacksFrontier/AlgebraicGeometry/VeryAmpleAffineBase/CoordinateCut.lean` cuts it down to its
  immersion clause alone, `Stacks.VeryAmpleAffineBase.ProjCoordinateImmersion`; see "What is not
  done" below.

## Main results

* `Stacks.VeryAmpleAffineBase.exists_immersion_proj_of_isRelativelyVeryAmple`: **over an affine
  base, relative very ampleness gives an immersion into an absolute `Proj`.** For a relatively
  very ample invertible `𝒪_X`-module `L` there are a quasi-coherent `𝒪_S`-module `E` and an
  immersion `α : X ⟶ Proj Γ(S, Sym(E))` over `S` with `L ≅ α^* 𝒪(1)`, the twist being the
  absolute degree-one twisting sheaf of that graded ring.
* `Stacks.VeryAmpleAffineBase.hasImmersionTwistOver_of_isRelativelyVeryAmple`: Stacks Tag 02NP
  from `ProjCoordinateCut`.

## Implementation notes

The graded ring of the absolute `Proj` is `(symAlgebra E).grading ⊤`, the grading of the ring of
global sections of `Sym(E)`; it is generated in degree one over its degree-zero part by
`Stacks.Tag01VMRelativeVeryAmple.adjoin_symAlgebra_eq_top`, which is what a choice of degree-one
coordinates consumes. No ring presentation of that graded ring is needed, and none is available:
`Stacks.AlgebraicGeometry.RelativeProjAffineBase` records that the graded ring of sections of a
symmetric algebra is not computed, and the statement below does not compute it either.

The twist is transported in three steps, all of them formal: the chart identification
`Stacks.Tag01VMVeryAmple.twistOneChartIso` is stated for
`AlgebraicGeometry.Scheme.Modules.restrict`, which `restrictFunctorIsoPullback` turns into a
pullback; `pullbackComp` splits the pullback along `α ≫ topChart` into the two pullbacks; and
`pullbackCongr` identifies that composite with the immersion the hypothesis supplies.

## Where the Tag 02NP attribute is

Not here: the unconditional statement is
`Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple`, and the attribute
sits there. `Stacks.VeryAmpleAffineBase.hasImmersionTwistOver_of_isRelativelyVeryAmple` below is
the same statement on `ProjCoordinateCut`, which is now a theorem
(`Stacks.CoordinateImmersion.projCoordinateCut`) and is kept as a named `Prop` because it is
where the two halves of the source's argument meet.

Of three ingredients `ProjCoordinateCut` might be expected to need, **two are not needed, and
the third is proved.**
`StacksFrontier/AlgebraicGeometry/VeryAmpleAffineBase/CoordinateCut.lean` spends the first two and
`StacksFrontier/AlgebraicGeometry/VeryAmpleAffineBase/CoordinateImmersion.lean` the third:

1. **The twist comparison of Tag 01MY does not enter the coordinate cut at all.** It is not
   known that `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap` is an
   isomorphism for `R[Y₀, …, Yₙ] ⟶ Γ(S, Sym(E))`, and that is irrelevant. The
   source's `θ` is one way to produce the identification `L ≅ i^*𝒪(1)`; it is not the only one.
   `Stacks.AmpleImmersionReduction.twistPullback` is proved unconditionally, and it identifies
   the hyperplane sheaf with any invertible module carrying a generating family of global sections
   whose pinned morphism to `ℙⁿ_S` the family itself defines. So
   `Stacks.VeryAmpleAffineBase.hasImmersionTwistOver_of_generatesStalks` gets the twist for free.
2. **The comparison of hyperplane sheaves along `Proj R[T₀, …, Tₙ] ≅ ℙⁿ_{Spec R}` is not needed
   either**, for the same reason: no polynomial `Proj` occurs on the route through
   `twistPullback`, whose target is `ℙⁿ_S` itself.
3. **What is left is the immersion clause**, isolated as
   `Stacks.VeryAmpleAffineBase.ProjCoordinateImmersion`:
   `Stacks.VeryAmpleAffineBase.projCoordinateCut_of_projCoordinateImmersion` proves
   `ProjCoordinateCut` from it. Its generation clause is not the obstacle — a finite generating
   family of global sections of `L` always exists, by
   `Stacks.VeryAmpleAffineBase.exists_generatesStalks_of_pullback_twistingSheaf`, which is the
   step the source describes as choosing finitely many degree-one coordinates: `Γ(S, Sym(E))` is
   generated in degree one over its degree-zero part, so `α` factors through the degree-one open
   `U₁` of Tag 01N5 (`Stacks.VeryAmpleAffineBase.degreeOpen_symAlgebra_one_eq_top`), the global
   generation clause of Tag 01N7 generates `α⁎𝒪(1) ≅ L` by the sections of the degree-one
   elements, and `X` is quasi-compact. The obstacle is that the family has to be chosen so that
   the morphism it defines is an immersion, and that is the source's remaining argument: a finite
   family of homogeneous elements `f_j` cutting out an affine cover on which `α` is a closed
   immersion, the algebra generators of each `Γ(α⁻¹D₊(f_j))` written as ratios `f_{j,k}/f_j^{e}`,
   and degree-one elements in which every `f_j` and `f_{j,k}` is a polynomial. The glue that turns
   the chart-local statement into `IsImmersion` is proved unconditionally —
   `Stacks.ChartImmersionAssembly.isImmersion_of_isImmersion_restrict_of_cover` for an arbitrary
   target, `Stacks.ProjectivityLabelChoice.isImmersion_of_isImmersion_restrict` in the range form,
   `Stacks.ChartImmersionFinish.isImmersion_of_closure_subcover` for the coordinate charts, with
   `AlgebraicGeometry.Proj.isAffineOpen_basicOpen` and
   `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'` supplying the cover. The restriction of the pinned morphism over a standard open `D₊(F_j)` of
   `ℙⁿ_S`, for `F_j` homogeneous of degree `deg f_j`, is never identified: **no such standard
   open is needed.** The cut stays inside one coordinate chart
   `D₊(T_i)` and uses the standard open of a *section* of it, which is
   `Stacks.OverlapSurjectivity.preimage_basicOpen_eq` and
   `Stacks.OverlapSurjectivity.isClosedImmersion_morphismRestrict_basicOpen`; the chart whose
   affineness the argument needs is the overlap `α⁻¹(D₊(y_i f_j))`, a cutting chart of the same
   kind as `α⁻¹(D₊(f_j))` by `Stacks.OverlapChart`, and not `α⁻¹(D₊(y_i))` — which is indeed not
   affine. The choice itself — the finite cover by the charts `α⁻¹(D₊(f_j))`, the algebra
   generators of each chart as fractions, and the degree-one `y_i` in which those are
   polynomials — is in
   `StacksFrontier/AlgebraicGeometry/VeryAmpleAffineBase/CoordinateChoice.lean`, and the immersion
   clause is proved in
   `StacksFrontier/AlgebraicGeometry/VeryAmpleAffineBase/CoordinateImmersion.lean`.

## References

* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.Tag01VMRelativeVeryAmple

universe u

namespace Stacks.VeryAmpleAffineBase

variable {S : Scheme.{u}}

/-! ### The chart over the whole of an affine base -/

/-- The chart of the relative homogeneous spectrum of `A` over the whole of the base: the
absolute `Proj` of the graded ring of global sections of `A`, mapping to `Proj_S(A)`. -/
abbrev topChart (A : SheafGradedAlgebra S) (hS : IsAffineOpen (⊤ : S.Opens)) :
    AlgebraicGeometry.Proj (A.grading (⊤ : S.Opens)) ⟶ (relativeProj A).scheme :=
  (relativeProj A).chart (⊤ : S.Opens) hS

/-- **Over an affine base the chart over `⊤` is an isomorphism**, so the relative homogeneous
spectrum is the absolute `Proj` of the graded ring of global sections. -/
instance isIso_topChart (A : SheafGradedAlgebra S) (hS : IsAffineOpen (⊤ : S.Opens)) :
    IsIso (topChart A hS) :=
  RelativeProjAffineBase.isIso_chart_top A.toGradedAlgebra hS

/-- The structure morphism to the base of the absolute `Proj` of the graded ring of global
sections: its structure morphism to `⊤`, followed by the inclusion of `⊤` in `S`. -/
abbrev projStructureHom (A : SheafGradedAlgebra S) (hS : IsAffineOpen (⊤ : S.Opens)) :
    AlgebraicGeometry.Proj (A.grading (⊤ : S.Opens)) ⟶ S :=
  projInclusionToOpen A (⊤ : S.Opens) hS ≫ (⊤ : S.Opens).ι

/-- The chart over `⊤` lies over the base: composing it with the structure morphism of
`Proj_S(A)` gives the structure morphism of the absolute `Proj`. -/
theorem topChart_toBase (A : SheafGradedAlgebra S) (hS : IsAffineOpen (⊤ : S.Opens)) :
    topChart A hS ≫ (relativeProj A).toBase = projStructureHom A hS :=
  ((relativeProj A).chart_isPullback (⊤ : S.Opens) hS).w

/-! ### Stacks Tag 02NP, step one -/

/-- **Over an affine base a relatively very ample invertible sheaf comes from an immersion into
an absolute homogeneous spectrum.** This is the opening step of the proof of Stacks Tag 02NP:
for a relatively very ample `L` there are a quasi-coherent `E` and an immersion
`α : X ⟶ Proj Γ(S, Sym(E))` over `S` with `L` the pullback along `α` of the absolute degree-one
twisting sheaf. -/
theorem exists_immersion_proj_of_isRelativelyVeryAmple {X : Scheme.{u}}
    (hS : IsAffineOpen (⊤ : S.Opens)) (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    (hL : Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    ∃ (E : S.Modules) (hE : E.IsQuasicoherent),
      have := hE
      ∃ α : X ⟶ AlgebraicGeometry.Proj ((symAlgebra E).grading (⊤ : S.Opens)),
        IsImmersion α ∧ α ≫ projStructureHom (symAlgebra E) hS = f ∧
          Nonempty (L ≅ (Scheme.Modules.pullback α).obj
            (twistingSheaf ((symAlgebra E).grading (⊤ : S.Opens)) 1)) := by
  obtain ⟨E, hE, i, him, hover, ⟨e⟩⟩ := hL
  have := hE
  have := him
  have hαc : (i ≫ inv (topChart (symAlgebra E) hS)) ≫ topChart (symAlgebra E) hS = i := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨E, hE, i ≫ inv (topChart (symAlgebra E) hS), inferInstance, ?_, ⟨?_⟩⟩
  · rw [← topChart_toBase (symAlgebra E) hS, ← Category.assoc, hαc]
    exact hover
  · refine e ≪≫ (Scheme.Modules.pullbackCongr hαc.symm).app (Tag01VMVeryAmple.twistOne E) ≪≫
      ((Scheme.Modules.pullbackComp (i ≫ inv (topChart (symAlgebra E) hS))
        (topChart (symAlgebra E) hS)).app (Tag01VMVeryAmple.twistOne E)).symm ≪≫ ?_
    exact (Scheme.Modules.pullback (i ≫ inv (topChart (symAlgebra E) hS))).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback (topChart (symAlgebra E) hS)).app
          (Tag01VMVeryAmple.twistOne E)).symm ≪≫
        Tag01VMVeryAmple.twistOneChartIso E (⊤ : S.Opens) hS)

/-! ### What Stacks Tag 02NP still owes -/

/-- **The one input Stacks Tag 02NP still owes**: from an immersion over an affine base into the
absolute homogeneous spectrum of the graded ring of global sections of `Sym(E)`, carrying the
degree-one twisting sheaf to `L`, an immersion into a finite-dimensional projective space over
the base carrying the hyperplane sheaf to `L`.

This is the source's choice of finitely many degree-one coordinates and everything it is used
for; the graded ring it is stated over is generated in degree one over its degree-zero part by
`Stacks.Tag01VMRelativeVeryAmple.adjoin_symAlgebra_eq_top`.

Its twist clause and its finiteness clause are both discharged in
`StacksFrontier/AlgebraicGeometry/VeryAmpleAffineBase/CoordinateCut.lean`:
`Stacks.VeryAmpleAffineBase.projCoordinateCut_of_projCoordinateImmersion` proves this condition
from `Stacks.VeryAmpleAffineBase.ProjCoordinateImmersion`, which asks only that the finitely many
degree-one coordinates can be chosen so that the morphism they define is an immersion. -/
def ProjCoordinateCut : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] [QuasiCompact f] (hS : IsAffineOpen (⊤ : S.Opens))
    (E : S.Modules) [E.IsQuasicoherent]
    (α : X ⟶ AlgebraicGeometry.Proj ((symAlgebra E).grading (⊤ : S.Opens))),
    IsImmersion α → α ≫ projStructureHom (symAlgebra E) hS = f →
      (L ≅ (Scheme.Modules.pullback α).obj
        (twistingSheaf ((symAlgebra E).grading (⊤ : S.Opens)) 1)) →
      AmpleProjectiveImmersion.HasImmersionTwistOver f L

/-- **Stacks Tag 02NP, reduced to `Stacks.VeryAmpleAffineBase.ProjCoordinateCut`.** A relatively
very ample invertible sheaf on a scheme of finite type over an affine base is the hyperplane sheaf
pulled back along an immersion into a finite-dimensional projective space over that base, lying
over the base.

Finite type is the conjunction of local finiteness of type with quasi-compactness, and the
conclusion is `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`, the source's conclusion
written out.

`ProjCoordinateCut` is the coordinate-cutting step of the source's proof, isolated as a named
`Prop` rather than left implicit. **It is a theorem**,
`Stacks.CoordinateImmersion.projCoordinateCut`, so this statement is unconditional once that is
substituted: the tag sits on
`Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple`, which does exactly
that, and this form is kept only because the reduction is where the two halves of the argument
meet. An earlier note here said that `ProjCoordinateCut` reduces to the twist clause of Tag 01N2
and the chart-local step of Tag 01VS, both not proved here; that is not what it reduces to,
and Tag 01VS reaches only a sufficiently high tensor power of `L`, where Tag 02NP is about `L`
itself. What it reduces to is `Stacks.VeryAmpleAffineBase.ProjCoordinateImmersion`, by
`Stacks.VeryAmpleAffineBase.projCoordinateCut_of_projCoordinateImmersion`: the twist
identification is `Stacks.AmpleImmersionReduction.twistPullback`, the existence of the finitely
many degree-one coordinates is
`Stacks.VeryAmpleAffineBase.exists_generatesStalks_of_pullback_twistingSheaf`, and that they can
be chosen to define an immersion is
`Stacks.CoordinateImmersion.projCoordinateImmersion`. -/
theorem hasImmersionTwistOver_of_isRelativelyVeryAmple (hcut : ProjCoordinateCut.{u})
    {X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsAffine S]
    (hL : Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    AmpleProjectiveImmersion.HasImmersionTwistOver f L := by
  have hS : IsAffineOpen (⊤ : S.Opens) := isAffineOpen_top S
  obtain ⟨E, hE, α, hα, hover, ⟨e⟩⟩ :=
    exists_immersion_proj_of_isRelativelyVeryAmple hS f L hL
  have := hE
  exact hcut f L hS E α hα hover e

end Stacks.VeryAmpleAffineBase

end
