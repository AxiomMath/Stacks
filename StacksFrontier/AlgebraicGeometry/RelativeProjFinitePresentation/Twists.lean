module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Twists

/-!
# Finite presentation of the twists on a relative projective spectrum

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra which is of finite presentation
over the structure sheaf. Stacks tag 0D4D asserts that every twist `𝒪_X(t)` on the relative
projective spectrum `X = Proj_S(A)` is then a module of finite presentation.

What this file contains is that assertion **reduced to its absolute case on the affine charts**,
and the same assertion proved outright **over a locally Noetherian base**.

The reduction,
`Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.isFinitePresentation_twist_of_charts`, is
the whole geometric content of the tag: given that every twist on the absolute `Proj (A(U))` is of
finite presentation, for `U` an affine open of the base, the glued twist on the relative `Proj` is
of finite presentation. The relative `Proj` is covered by affine opens — the images under the
charts of the standard opens `D₊(f)` of the absolute `Proj`s — and on each of them the glued twist
is an absolute twist, by the chart identifications.

The Noetherian version goes a different way: over a locally Noetherian base `X` is locally
Noetherian, because its structure morphism is locally of finite type (Stacks tag 07ZY, first
assertion); the twist is quasi-coherent and of finite type (Stacks tag 07ZY, second assertion); and
on a locally Noetherian scheme a quasi-coherent module of finite type is of finite presentation
(Stacks tag 01XZ).

## Main results

In namespace `Stacks.AlgebraicGeometry.RelativeProjFinitePresentation`:

* `isFiniteType_of_finitePresentation`: a graded algebra whose structure map is of finite
  presentation on every affine open of the base is of finite type in the affine-local sense of
  Stacks tag 07ZY.
* `isFinitePresentation_twist_of_isLocallyNoetherian`: every twist on the relative projective
  spectrum of a finite type quasi-coherent graded algebra over a locally Noetherian base is of
  finite presentation.
* `isFinitePresentation_twist_of_charts`: the assertion of Stacks tag 0D4D, conditional on its
  absolute case over every affine chart of the base.

## Implementation notes

Neither result here carries `@[stacks 0D4D]`: `isFinitePresentation_twist_of_isLocallyNoetherian`
adds the hypothesis `[IsLocallyNoetherian S]`, which the source does not make, and
`isFinitePresentation_twist_of_charts` adds the hypothesis `habs`, an intermediate assertion inside
the proof of the tag.

In the direction of the hypothesis on `A` the Noetherian statement below is a generalisation rather
than a weakening: finite type of the graded algebra, in the affine-local form
`Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType`, is weaker than finite presentation
of its structure map over every affine open, and it is all the Noetherian argument needs.

The twist data is a parameter, so that the results here are the general form of the assertion, of
which the statement for any particular glued family of twists is an instance.

## References

* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjFiniteType
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjFinitePresentation

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

include A in
/-- **A graded algebra whose structure map is of finite presentation over every affine open of the
base is of finite type**, in the affine-local sense of Stacks tag 07ZY: the affine opens cover the
base, and a ring map of finite presentation is of finite type. -/
public theorem isFiniteType_of_finitePresentation
    (hA : ∀ U : S.Opens, IsAffineOpen U → (A.strHom U).FinitePresentation) :
    IsFiniteType A := fun x => by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := x) (U := ⊤) (by trivial)
  exact ⟨U, hU, hxU, RingHom.FiniteType.of_finitePresentation (hA U hU)⟩

include A in
/-- **Finite presentation of the twists on a relative projective spectrum over a locally Noetherian
base.**

If a quasi-coherent graded `𝒪_S`-algebra is of finite type over a locally Noetherian base `S`, then
every homogeneous piece of the glued graded algebra of twists on the relative projective spectrum
of `A` is a module of finite presentation.

No tag is attached: Stacks tag 0D4D does not assume that `S` is locally Noetherian. -/
public theorem isFinitePresentation_twist_of_isLocallyNoetherian [IsLocallyNoetherian S]
    (D : TwistData A) (hA : IsFiniteType A) (t : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (D.algebra.piece t) := by
  let _ : LocallyOfFiniteType (relativeProj A).toBase := locallyOfFiniteType_toBase A hA
  let _ : IsLocallyNoetherian (relativeProj A).scheme :=
    LocallyOfFiniteType.isLocallyNoetherian (relativeProj A).toBase
  let _ : (D.algebra.piece t).IsQuasicoherent := D.isQuasicoherent t
  have h : (D.algebra.piece t).IsQuasicoherent ∧
      SheafOfModules.IsFiniteType.{u, u, u} (D.algebra.piece t) :=
    ⟨inferInstance, isFiniteType_twist A D hA t⟩
  exact ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae
    (relativeProj A).scheme (D.algebra.piece t)).out 2 3).mp h

include A in
/-- **Finite presentation of the twists on a relative projective spectrum, reduced to the absolute
statement on the affine charts.**

If every twist on the absolute projective spectrum of the graded ring of sections `A(U)`, for `U`
an affine open of the base, is a module of finite presentation, then so is every homogeneous piece
of the glued graded algebra of twists on the relative projective spectrum of `A`.

No tag is attached: the hypothesis `habs` is an intermediate assertion of the proof of Stacks
tag 0D4D, not a hypothesis of it. -/
public theorem isFinitePresentation_twist_of_charts (D : TwistData A) (t : ℤ)
    (habs : ∀ (U : S.Opens), IsAffineOpen U →
      SheafOfModules.IsFinitePresentation.{u, u, u} (twistingSheaf (A.grading U) t)) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (D.algebra.piece t) := by
  classical
  let p := (relativeProj A).toBase
  let F : (relativeProj A).scheme.Modules := D.algebra.piece t
  let _ : F.IsQuasicoherent := D.isQuasicoherent t
  let chart (V : S.affineOpens) := (relativeProj A).chart (V : S.Opens) V.2
  let _ (V : S.affineOpens) : IsOpenImmersion (chart V) :=
    D.chartData.chart_isOpenImmersion (V : S.Opens) V.2
  let std (V : S.affineOpens) (c : Σ m : ℕ+, A.grading (V : S.Opens) (m : ℕ)) :
      (AlgebraicGeometry.Proj (A.grading (V : S.Opens))).Opens :=
    Proj.basicOpen (A.grading (V : S.Opens)) (c.2 : A.sectionRing (V : S.Opens))
  have hstd (V : S.affineOpens) (c : Σ m : ℕ+, A.grading (V : S.Opens) (m : ℕ)) :
      IsAffineOpen (std V c) :=
    Proj.isAffineOpen_basicOpen (A.grading (V : S.Opens)) _ c.2.2 c.1.2
  let _ (V : S.affineOpens) (c : Σ m : ℕ+, A.grading (V : S.Opens) (m : ℕ)) :
      IsAffine (std V c).toScheme := hstd V c
  let g (i : Σ V : S.affineOpens, Σ m : ℕ+, A.grading (V : S.Opens) (m : ℕ)) :
      (std i.1 i.2).toScheme ⟶ (relativeProj A).scheme := (std i.1 i.2).ι ≫ chart i.1
  let O (i : Σ V : S.affineOpens, Σ m : ℕ+, A.grading (V : S.Opens) (m : ℕ)) :
      (relativeProj A).scheme.Opens := (g i).opensRange
  have hOaff (i : Σ V : S.affineOpens, Σ m : ℕ+, A.grading (V : S.Opens) (m : ℕ)) :
      IsAffineOpen (O i) := isAffineOpen_opensRange (g i)
  have himg (V : S.affineOpens) : (chart V).opensRange = p ⁻¹ᵁ (V : S.Opens) := by
    rw [← Scheme.Hom.image_top_eq_opensRange]
    exact D.chartData.chart_range (V : S.Opens) V.2
  have hcov : IsOpenCover O := by
    refine IsOpenCover.mk (eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ?_)
    obtain ⟨V, hV, hyV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S) (x := p.base y) (U := ⊤) (by trivial)
    obtain ⟨z, hz⟩ : y ∈ (chart ⟨V, hV⟩).opensRange := by
      rwa [himg ⟨V, hV⟩]
    have hztop : z ∈ (⨆ c : Σ m : ℕ+, A.grading V (m : ℕ),
        Proj.basicOpen (A.grading V) (c.2 : A.sectionRing V)) := by
      rw [Proj.iSup_basicOpen_homogeneous_eq_top]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hztop
    exact ⟨⟨⟨V, hV⟩, c⟩, ⟨⟨z, hc⟩, hz⟩⟩
  refine FinitePresentationLocal.isFinitePresentation_of_affineCover_restrict
    F O hcov hOaff fun i => ?_
  let T : (AlgebraicGeometry.Proj (A.grading (i.1 : S.Opens))).Modules :=
    twistingSheaf (A.grading (i.1 : S.Opens)) t
  have h1 : (T.restrict (std i.1 i.2).ι).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_restrict
      (std i.1 i.2).ι T (habs (i.1 : S.Opens) i.1.2)
  have hrange : Set.range (g i).base = Set.range (O i).ι.base := by
    rw [Scheme.Opens.range_ι]; rfl
  let e := AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq (g i) (O i).ι hrange
  have h3 : ((F.restrict (O i).ι).restrict e.hom).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation.{u, u, u} (std i.1 i.2).toScheme.ringCatSheaf).prop_of_iso
      ((((Scheme.Modules.restrictFunctor (std i.1 i.2).ι).mapIso
          (D.chartData.chartIso (i.1 : S.Opens) i.1.2 t)).symm ≪≫
        ((Scheme.Modules.restrictFunctorComp (std i.1 i.2).ι (chart i.1)).app F).symm) ≪≫
        (Scheme.Modules.restrictFunctorCongr
          (IsOpenImmersion.isoOfRangeEq_hom_fac (g i) (O i).ι hrange).symm).app F ≪≫
        (Scheme.Modules.restrictFunctorComp e.hom (O i).ι).app F) h1
  exact (SheafOfModules.isFinitePresentation.{u, u, u} (O i).toScheme.ringCatSheaf).prop_of_iso
    (Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSelf e.symm (F.restrict (O i).ι))
    (Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_restrict e.inv _ h3)

end Stacks.AlgebraicGeometry.RelativeProjFinitePresentation

end
