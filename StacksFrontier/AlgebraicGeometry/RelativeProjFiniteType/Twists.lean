module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.FlatOverBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.DegreeZeroFinite
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type of the twists on a relative projective spectrum

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra of finite type. Then every twist
`𝒪_X(t)` on the relative projective spectrum `X = Proj_S(A)` is a finite-type module sheaf.

The assertion is local on `X`, and the opens over which it is checked are the images of the charts:
over an affine open `U` of the base on which the graded ring of sections `A(U)` is a finite type
`Γ(S, U)`-algebra, the part of `X` lying over `U` is the absolute `Proj A(U)`, and the twist
restricts there to the absolute twist `𝒪(t)` on `Proj A(U)`. So the whole content is the absolute
statement, which is proved first: the `t`-th twisting sheaf on the `Proj` of a graded ring of finite
type over its degree-zero part is of finite type. That one is in turn local on the standard affine
opens `D₊(f)`, where the sections are the degree-zero part of the twisted localization and the
finiteness is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_twistSections`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isFiniteType_twistingSheaf`: every twist of an
  absolute `Proj` is of finite type when the graded ring is a finite type algebra over its
  degree-zero part.
* `Stacks.AlgebraicGeometry.RelativeProjFiniteType.isFiniteType_twist`: every twist of a relative
  `Proj` is of finite type when the graded algebra is of finite type.

## Implementation notes

The twists are taken as a parameter: `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is
the structure Tag 01NR produces, and the statement is made for an arbitrary term of it, which is
this development's convention for every other result about the twists. The actual twists of the
relative `Proj` are the pieces of
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, Tag 01NR's datum for the
graded algebra itself; the second assertion of tag 07ZY is this result at that datum, and is
`Stacks.AlgebraicGeometry.RelativeProjFiniteType.isFiniteType_relativeProjTwist` in
`StacksFrontier/AlgebraicGeometry/RelativeProjFiniteType/GluedTwists.lean`.

The hypothesis `Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType` asserts finite type
only on *some* affine neighbourhood of each point of the base, so the cover of `X` used here is
indexed by the points of `S`: for each of them an affine open is chosen on which the graded ring of
sections is of finite type, and the inverse images of those opens cover `X` because the opens
themselves cover `S`.

Going from the absolute statement on a chart to the statement on the corresponding open of `X`
needs no computation with `appLE` or with the structure morphism: the image of the chart is an open
of `X` and the chart is an isomorphism onto it
(`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`), so the two restrictions of the twist differ by
restriction along an isomorphism, which
`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSelf` undoes.

The degree-zero part of the graded ring of sections is in general larger than `Γ(S, U)`, and it is
the base over which the absolute statement is phrased; finite type over `Γ(S, U)` gives finite type
over it by the scalar tower `Γ(S, U) → A(U)₀ → A(U)`, which commutes because the structure map
lands in degree zero.

## References

* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Every twist of the structure sheaf on a homogeneous spectrum is a finite-type module
sheaf** when the graded ring is a finite type algebra over its degree-zero part.

Finite type is local, and the standard opens `D₊(f)` at the homogeneous elements `f` of positive
degree are affine opens covering `Proj 𝒜`. Over one of them the sections of the twist are a finite
module over the degree-zero localization `A₍f₎`
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_twistSections`), hence over the functions on
`D₊(f)`, which `AlgebraicGeometry.Proj.basicOpenIsoAway` identifies with `A₍f₎` by the very map
that defines the action.

This is the absolute case of the second assertion of Stacks tag 07ZY. -/
public theorem isFiniteType_twistingSheaf [Algebra.FiniteType (𝒜 0) A] (t : ℤ) :
    SheafOfModules.IsFiniteType.{u, u, u} (twistingSheaf 𝒜 t) := by
  have hqc : SheafOfModules.IsQuasicoherent.{u, u, u} (twistingSheaf 𝒜 t) := inferInstance
  let F : (AlgebraicGeometry.Proj 𝒜).Modules := twistingSheaf 𝒜 t
  let _ : F.IsQuasicoherent := hqc
  refine Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn F
    (fun i : Σ m : ℕ+, 𝒜 (m : ℕ) => Proj.basicOpen 𝒜 (i.2 : A))
    (IsOpenCover.mk (Proj.iSup_basicOpen_homogeneous_eq_top 𝒜))
    (fun i => Proj.isAffineOpen_basicOpen 𝒜 _ i.2.2 i.1.2) fun i => ?_
  let _ : Module (HomogeneousLocalization.Away 𝒜 (i.2 : A))
      Γ(F, Proj.basicOpen 𝒜 (i.2 : A)) :=
    associatedModuleSheafStandardOpenModule 𝒜 (twistGrading 𝒜 t) (i.2 : A)
  let ε : HomogeneousLocalization.Away 𝒜 (i.2 : A) ≃+*
      Γ(AlgebraicGeometry.Proj 𝒜, Proj.basicOpen 𝒜 (i.2 : A)) :=
    (Proj.basicOpenIsoAway 𝒜 (i.2 : A) i.2.2 i.1.2).commRingCatIsoToRingEquiv
  have hfin : Module.Finite Γ(AlgebraicGeometry.Proj 𝒜, Proj.basicOpen 𝒜 (i.2 : A))
      Γ(F, Proj.basicOpen 𝒜 (i.2 : A)) :=
    Module.Finite.of_addEquiv ε.toRingHom (AddEquiv.refl _) (fun _ _ => rfl)
      (finite_twistSections 𝒜 i.1.2 i.2.2 t)
  exact Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_finite_specModule F _
    (Proj.isAffineOpen_basicOpen 𝒜 _ i.2.2 i.1.2)
    (Module.Finite.equiv (Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv F
      (Proj.isAffineOpen_basicOpen 𝒜 _ i.2.2 i.1.2)).symm)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.RelativeProjFiniteType

open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

include A in
/-- The graded ring of sections over an open on which the graded algebra is of finite type is a
finite type algebra over its own degree-zero part: the scalar tower `Γ(S, U) → A(U)₀ → A(U)`
commutes, because the structure map lands in degree zero. -/
private theorem finiteType_gradeZero_sectionRing (U : S.Opens)
    (hft : (A.strHom U).FiniteType) :
    Algebra.FiniteType (A.grading U 0) (A.sectionRing U) := by
  let _ := A.sectionRingAlgebra U
  let φ := (GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)
  let _ : Algebra Γ(S, U) (A.grading U 0) := φ.toAlgebra
  have hcomp : (algebraMap (A.grading U 0) (A.sectionRing U)).comp φ =
      algebraMap Γ(S, U) (A.sectionRing U) := by
    refine RingHom.ext fun r => ?_
    have hr : φ r = GradedRing.toGradeZero (A.grading U) (A.strHom_mem U) r := by
      rw [A.toGradeZero_eq U]
    rw [RingHom.comp_apply, hr]
    rfl
  let _ := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let _ : Algebra.FiniteType Γ(S, U) (A.sectionRing U) := RingHom.finiteType_algebraMap.mp hft
  exact Algebra.FiniteType.of_restrictScalars_finiteType Γ(S, U) (A.grading U 0) (A.sectionRing U)

include A in
/-- **Every twist on the relative projective spectrum of a finite type quasi-coherent graded
algebra is a finite-type module sheaf**, for an arbitrary term of Tag 01NR's twist datum.

Instantiated at the actual twists — the pieces of
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` — this is the second
assertion of Stacks tag 07ZY; see
`Stacks.AlgebraicGeometry.RelativeProjFiniteType.isFiniteType_relativeProjTwist`.

Finite type is local on the relative `Proj`, and the opens used are the inverse images of affine
opens of the base over which the graded ring of sections is of finite type; one such open is chosen
around the image of each point. Over it the relative `Proj` is the chart, an absolute `Proj`, and
the twist restricts to the absolute twist there, which is of finite type by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.isFiniteType_twistingSheaf`. -/
@[ega "III 2.3.4" "(i)"]
public theorem isFiniteType_twist (D : TwistData A) (hA : IsFiniteType A) (t : ℤ) :
    SheafOfModules.IsFiniteType.{u, u, u} (D.algebra.piece t) := by
  classical
  choose U hU hmem hft using hA
  let p := (relativeProj A).toBase
  let F : (relativeProj A).scheme.Modules := D.algebra.piece t
  let _ : F.IsQuasicoherent := D.isQuasicoherent t
  have hUtop : (⨆ x : S, U x) = ⊤ :=
    eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩
  refine Modules.isFiniteType_of_restrict F (fun x : S => p ⁻¹ᵁ U x)
    (IsOpenCover.mk (p.iSup_preimage_eq_top hUtop)) fun x => ?_
  let W : (relativeProj A).scheme.Opens := p ⁻¹ᵁ U x
  let j := (relativeProj A).chart (U x) (hU x)
  let _ : IsOpenImmersion j := D.chartData.chart_isOpenImmersion (U x) (hU x)
  have himg : j.opensRange = W := by
    rw [← Scheme.Hom.image_top_eq_opensRange]
    exact D.chartData.chart_range (U x) (hU x)
  have hrange : Set.range j.base = Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι, ← himg]
    rfl
  let e := AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq j W.ι hrange
  have he : e.hom ≫ W.ι = j :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac j W.ι hrange
  have h0 := finiteType_gradeZero_sectionRing A (U x) (hft x)
  have habs : SheafOfModules.IsFiniteType.{u, u, u} (twistingSheaf (A.grading (U x)) t) :=
    isFiniteType_twistingSheaf (A.grading (U x)) t
  have h1 : (F.restrict j).IsFiniteType :=
    Modules.isFiniteType_of_iso (D.chartData.chartIso (U x) (hU x) t).symm habs
  have h2 : ((F.restrict W.ι).restrict e.hom).IsFiniteType :=
    Modules.isFiniteType_of_iso
      ((Scheme.Modules.restrictFunctorCongr he.symm).app F ≪≫
        (Scheme.Modules.restrictFunctorComp e.hom W.ι).app F) h1
  exact Modules.isFiniteType_of_iso
    (Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSelf e.symm (F.restrict W.ι))
    (Modules.isFiniteType_restrict e.inv _ h2)

end Stacks.AlgebraicGeometry.RelativeProjFiniteType

end
