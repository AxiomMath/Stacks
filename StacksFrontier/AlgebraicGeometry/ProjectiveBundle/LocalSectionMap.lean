module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalSection

/-!
# The local section of a projective bundle as a named morphism

`Stacks.RelativeProj.exists_hom_projectiveBundle_of_trivializing` produces, over an affine open
`V` of `X` on which an invertible quotient `q : F ⟶ L` is trivialized, a morphism
`V ⟶ 𝐏(F)` lying over the inclusion of `V`, as an existential. **This file names that
morphism.**

A gluing argument cannot consume an existential: to glue local sections one must compare *the*
section over `V` with *the* section over `W` on `V ∩ W`, and for that the section has to be a
function of the data. So the construction is repeated here as a definition.

## The choice of lift disappears

The existential statement chooses a section `m` of `F` over `V` whose image under the
trivialization is the unit section, and feeds the degree-one homogeneous section it determines to
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit`. That lift looks like a second
choice on top of the trivialization, but it is not one:
`ProjF1DegreeOneChart.fromOfIsUnit 𝒜 φ hd hr hu` is by definition
`AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 φ (map_irrelevant_eq_top_of_isUnit 𝒜 φ hd hr hu)`,
and `fromOfGlobalSections` depends on its last argument only through a `Prop`. So the classified
morphism depends on the ring map `ψ` alone, and the lift is needed only to *prove* that the
irrelevant ideal's image is the unit ideal.

Accordingly `localChartMap` below is built from `AlgebraicGeometry.Proj.fromOfGlobalSections`
directly, with `map_irrelevant_localDehomogenize_eq_top` — an ordinary theorem, whose proof
chooses the lift internally — as its hypothesis. The only data the named local section depends on
are `V`, `q` and the trivialization `e`; the surjectivity hypothesis enters as a `Prop`.

## Main definitions

* `Stacks.RelativeProj.localDehomogenize`: the dehomogenization of `Sym F` over `V` at the
  trivialized quotient `(q, e)`, a ring map `Γ(V, Sym F) ⟶ Γ(V, 𝒪)`.
* `Stacks.RelativeProj.localChartMap`: the morphism `V ⟶ Proj Γ(V, Sym F)` it classifies, into
  the chart of the relative `Proj` over `V`.
* `Stacks.RelativeProj.localSection`: **the local section**, `V ⟶ 𝐏(F)`.

## Main results

* `Stacks.RelativeProj.localDehomogenize_strHom`: the degree-zero clause, in the form the chart
  construction consumes.
* `Stacks.RelativeProj.map_irrelevant_localDehomogenize_eq_top`: the image of the irrelevant
  ideal is the unit ideal. This is where the lift of the unit section is chosen, and it is a
  `Prop`, so no choice leaks into the definitions.
* `Stacks.RelativeProj.localChartMap_comp_projInclusionToOpen`: the morphism into the chart lies
  over `V` **on the nose** — its composite with the chart's structure morphism is the identity of
  `V`, not merely a morphism to the base.
* `Stacks.RelativeProj.localSection_comp_projectiveBundleToBase`: **the local section is a
  section of `π` over `V`.**

## Implementation notes

The statements are written with `Stacks.SymGraded.schemeSheafGradedAlgebra F
(Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F)` spelled out rather than behind an
abbreviation, which is the spelling `Stacks.RelativeProj.symGradedBundle` and
`Stacks.RelativeProj.bundlePresentationIso` are already stated at; the quasi-coherence argument
is a `Prop`, so every spelling of it is the same term.

No `@[stacks]` attribute is attached. Tag 0B3V is the bijection between sections of `π` and
invertible quotients of `F`; naming a section over one open of the base, with no statement about
which quotient it classifies, is not a covering part of it. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalSection.lean` for what gluing still needs.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F L : X.Modules} [F.IsQuasicoherent] (V : X.Opens) (q : F ⟶ L)
  (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))

/-- **The dehomogenization of `Sym F` over `V` at a trivialized quotient.** The ring map out of
the graded ring of homogeneous sections of `Sym F` over `V` built from
`Stacks.RelativeProj.trivializedQuotientHom`, which is the shape
`AlgebraicGeometry.Proj.fromOfGlobalSections` consumes. -/
public def localDehomogenize :
    (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).sectionRing V →+*
      Γ(V.toScheme, ⊤) :=
  Stacks.SymmetricDehomogenize.dehomogenize V.ι F (trivializedQuotientHom V q e) V
    (preimageSelfTopRingHom V) (isQuasicoherentPieces_of_isQuasicoherent F)

/-- **The degree-zero clause of the dehomogenization**, in the form the chart construction
consumes: on the degree-zero multiple of the unit attached to a function on `V`, the
dehomogenization is that function read through the identity of `V`. The trivialization does not
appear, which is what places the classified morphism over `V`. -/
public theorem localDehomogenize_strHom (x : Γ(X, V)) :
    localDehomogenize V q e
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).strHom V x) =
      (V.topIso.inv ≫ (𝟙 V.toScheme : V.toScheme ⟶ V.toScheme).appTop).hom x := by
  refine (Stacks.SymmetricDehomogenize.dehomogenize_strHom_app V.ι F
    (trivializedQuotientHom V q e) V (preimageSelfTopRingHom V)
    (isQuasicoherentPieces_of_isQuasicoherent F) x).trans ?_
  rw [AlgebraicGeometry.Scheme.Hom.id_appTop, Category.comp_id,
    ← appLE_self_top_eq_topIso_inv V]
  rfl

/-- **The image of the irrelevant ideal under the dehomogenization is the unit ideal.** This is
the one hypothesis `AlgebraicGeometry.Proj.fromOfGlobalSections` asks for. A section of `F` over
`V` that the trivialization carries to the unit section — which
`Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` supplies from the surjectivity of
`q` on sections — gives a degree-one homogeneous section whose dehomogenization is `1`, and one
positive-degree unit already generates.

The lift is chosen inside this proof and the statement is a `Prop`, so the definitions below
depend on `V`, `q` and `e` only. -/
public theorem map_irrelevant_localDehomogenize_eq_top
    (hq : Function.Surjective (q.val.app (op V))) :
    (HomogeneousIdeal.irrelevant
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)).toIdeal.map
      (localDehomogenize V q e) = ⊤ := by
  obtain ⟨m, hm⟩ := exists_app_trivializedQuotientHom_eq_one V q e hq
  have hval : localDehomogenize V q e
      (DirectSum.of ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).sectionPieces V) 1
        ((symmetricAlgebraGen X F).val.app (op V) m)) = 1 :=
    (Stacks.SymmetricDehomogenize.dehomogenize_of_one V.ι F (trivializedQuotientHom V q e) V
        (preimageSelfTopRingHom V) (isQuasicoherentPieces_of_isQuasicoherent F) m).trans
      ((congrArg (fun z => preimageSelfTopRingHom V z) hm).trans
        (map_one (preimageSelfTopRingHom V)))
  exact Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.map_irrelevant_eq_top_of_isUnit _
    (localDehomogenize V q e) Nat.one_pos
    (SheafGradedAlgebra.of_mem_grading _ V _) (hval ▸ isUnit_one)

/-- **The morphism into the chart of `𝐏(F)` over `V` classified by the dehomogenization.** -/
public def localChartMap (hq : Function.Surjective (q.val.app (op V))) :
    V.toScheme ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) :=
  AlgebraicGeometry.Proj.fromOfGlobalSections _ (localDehomogenize V q e)
    (map_irrelevant_localDehomogenize_eq_top V q e hq)

/-- **The morphism into the chart lies over `V` on the nose**: its composite with the chart's
structure morphism is the identity of `V`. This is the degree-zero clause of the dehomogenization
read through
`Stacks.AlgebraicGeometry.RelativeProj.fromOfGlobalSections_comp_projInclusionToOpen`. -/
public theorem localChartMap_comp_projInclusionToOpen (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V))) :
    localChartMap V q e hq ≫ projInclusionToOpen
        (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)) V hV =
      𝟙 V.toScheme :=
  Stacks.AlgebraicGeometry.RelativeProj.fromOfGlobalSections_comp_projInclusionToOpen _ hV
    (𝟙 V.toScheme) (localDehomogenize V q e) _ (localDehomogenize_strHom V q e)

/-- **The local section of `π : 𝐏(F) ⟶ X` over `V`**, as a named morphism: the morphism into the
chart, carried into the `SheafGradedAlgebra` presentation of the bundle by its chart and from
there to `𝐏(F)` by `Stacks.RelativeProj.bundlePresentationIso`. -/
public def localSection (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V))) : V.toScheme ⟶ projectiveBundle X F :=
  localChartMap V q e hq ≫ (symGradedBundle F).chart V hV ≫ (bundlePresentationIso F).hom

/-- **The local section is a section of `π` over `V`.** -/
public theorem localSection_comp_projectiveBundleToBase (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V))) :
    localSection V q e hV hq ≫ projectiveBundleToBase X F = V.ι := by
  rw [localSection, Category.assoc, Category.assoc, bundlePresentationIso_hom_comp_toBase,
    ((symGradedBundle F).chart_isPullback V hV).w, ← Category.assoc,
    localChartMap_comp_projInclusionToOpen V q e hV hq, Category.id_comp]

end Stacks.RelativeProj

end
