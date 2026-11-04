module

public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentQuasicoherent

/-!
# The two models of projective space, and where they meet

The development carries two projective `n`-spaces over a commutative ring, and until now no
declaration related them.

* `AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)` — the source's
  own definition. Everything about the twisting sheaf `𝒪(d)` lives here: the sheaf itself, its
  invertibility, and the identification of its sections over an intersection of standard
  coordinate opens with the degree-`d` part of a localization of the polynomial ring.
* `AlgebraicGeometry.projectiveSpaceOverRing n R` — the library's, defined as the base change of
  the integral model `Proj (ULift ℤ)[T₀, …, Tₙ]` along `Spec R ⟶ Spec ℤ`. Everything
  cohomological lives here: the vanishing above the dimension, the Čech comparison for the
  standard charts, and the top-degree base-change situation of
  `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofProjectiveSpace`.

This file connects them **over the integers**, where the connection is a formality: the base
`Spec (ULift ℤ)` is a terminal scheme, so the projection to the integral model is an
isomorphism. For a general coefficient ring the comparison is still owed; see
`## What is not proved`.

The point of doing it over the integers is that it suffices for the one question the
`TopDegreeBaseChangeSituation` family leaves open. That family's only non-affine inhabitant is
the structure morphism of `ℙⁿ_R` at top degree `n`, and whether its degree-`n` object is nonzero
was reduced to the degree-`n` homology of the Čech complex of the `n + 1` standard charts — on
the library's model, where the twisting sheaf's sections are not described. Over the integers
the two models are identified here, and the question becomes the degree-`n` homology of the Čech
complex of the standard coordinate opens of `Proj (ULift ℤ)[T₀, …, Tₙ]` with coefficients in
`𝒪(d)` — a complex every one of whose terms is described, as a free module on Laurent
monomials, in `StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/TwistWeights.lean`.

## Main definitions

* `Stacks.ProjectiveCohomology.basicOpenXAtUniverse`: the standard coordinate opens of
  `Proj R[T₀, …, Tₙ]`, indexed in the universe of `R` so that they can be fed to the Čech
  comparison.
* `Stacks.ProjectiveCohomology.projectiveSpaceOverIsoAtUniverse`: the comparison of the two
  models over a terminal base.
* `Stacks.ProjectiveCohomology.integralModelIso`: **the two models of projective `n`-space agree
  over the integers.**
* `Stacks.ProjectiveCohomology.integralTwist`: `𝒪(d)` on the library's `ℙⁿ` over the integers,
  i.e. the second tensor factor of `AlgebraicGeometry.projectiveTwist`.

## Main results

* `Stacks.Cohomology.SchemeIso.isZero_Hgroup_iff_pushforward_of_isIso` and
  `isZero_Hgroup_pullback_iff`: **cohomology is invariant under an isomorphism of schemes**, in
  the `Hgroup` spelling that this development's vanishing hypotheses use, both for the direct
  image and for the inverse image. Unconditional on the scheme and on the module.
* `Stacks.ProjectiveCohomology.isZero_Hgroup_twistingSheaf_iff`: the cohomology of a twist on
  `Proj R[T₀, …, Tₙ]` is the homology of the **explicit** Čech complex of the `n + 1` standard
  coordinate opens, in every degree and for every coefficient ring.
* `Stacks.ProjectiveCohomology.isZero_Hgroup_proj_of_lt`: the cohomology of a quasi-coherent
  module on `Proj R[T₀, …, Tₙ]` vanishes above degree `n`. This is the `Proj`-model counterpart
  of `Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt`; see the implementation notes for why no
  attribute is attached to it.
* `Stacks.ProjectiveCohomology.integralTwist_eq_pullback_integralModelIso` and
  `projectiveTwist_eq_integralTwist`: **the twisting sheaves correspond under the comparison**,
  both by `rfl`.
* `Stacks.ProjectiveCohomology.isZero_Hgroup_integralTwist_iff`: **the cohomology of `𝒪(d)` is
  the same on both models over the integers.**
* `Stacks.ProjectiveCohomology.not_isZero_topDirectImage_of_not_isZero_cechHomology_twistingSheaf`:
  **the top-degree object of the projective situation over the integers is nonzero as soon as
  the degree-`n` homology of the Čech complex of the standard coordinate opens of
  `Proj (ULift ℤ)[T₀, …, Tₙ]` with coefficients in `𝒪(d)` is.** The hypothesis mentions no
  situation, no derived category, no higher direct image and no sheaf cohomology.

## What is not proved

**The comparison of the two models over a general coefficient ring.** The statement
proved here is the comparison over a *terminal* base, which is the integral one. For a general
`R` the comparison is a cartesian square, and the machinery for it is already in the
development:
`AlgebraicGeometry.Proj.isPullback_toSpecZero_map` in
`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/MapBaseChange.lean` derives the square
`Proj ℬ ⟶ Spec ℬ₀` over `Proj 𝒜 ⟶ Spec 𝒜₀` from `Stacks.Proj.IsBaseChangeOnCharts` alone. What
is missing is three things: the graded ring homomorphism
`(ULift ℤ)[T₀, …, Tₙ] →+*ᵍ R[T₀, …, Tₙ]` together with the containment of irrelevant ideals that
`AlgebraicGeometry.Proj.map` requires; the chart hypothesis for it, which by
`Stacks.Proj.IsBaseChangeOnCharts.of_isPushout` is the purely ring-theoretic statement that
`Away R[T] (ψ s) = Away (ULift ℤ)[T] s ⊗_ℤ R` for every homogeneous `s` of positive degree (and
`StacksFrontier/RingTheory/GradedAlgebra/Proj/StandardOpenBaseChange.lean` proves exactly this for
a *literal* tensor product of graded algebras, so a graded transport along
`MvPolynomial.algebraTensorAlgEquiv` is what stands between the two); and the identification of
`Spec` of the degree-zero parts with `Spec ℤ` and `Spec R`, carrying
`AlgebraicGeometry.Proj.toSpecZero` to the structure morphism.

**The twist correspondence beyond the integral case.** Over the integers nothing has to be
proved about it, and that is a fact about the definitions rather than a theorem:
`Stacks.ProjectiveCohomology.integralTwist_eq_pullback_integralModelIso` and
`projectiveTwist_eq_integralTwist` are both `rfl`, because the library's twist is *defined* as
the inverse image along the projection to the integral model of the `Proj`-model twisting sheaf
and over a terminal base that projection is the comparison isomorphism itself. For a general
coefficient ring the correspondence has no content to be free: there is no comparison morphism
to pull back along.

**The nonvanishing itself.** Nothing here computes any cohomology group. The statements above
are reductions; the Čech differential is not split along the Laurent weight here and no
contracting homotopy is constructed.

## Implementation notes

**Why no attribute is attached to `isZero_Hgroup_proj_of_lt`.** It states the same clause —
vanishing above the dimension — as `Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt`,
which carries the attribute, but at the other model. The two models are not identified for a
general coefficient ring, so the two declarations are about different constants; attaching the
same tag to both would register one tag on two different constants, a split no tag scan can
see. The attribute therefore stays
on the library-model statement alone, and this one is recorded as its counterpart in prose.

**Why the two general transport results are stated for `Hgroup` rather than reused from
`AlgebraicGeometry.cohomologyOverFieldPushforwardIso`.** That isomorphism restricts scalars to a
base field, which `Proj` of a polynomial ring over `ULift ℤ` has none of. The engine underneath
it, `AlgebraicGeometry.rightDerivedEvaluationTopPushforwardIso`, needs no field; composing it
with `Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup` and
`Stacks.ProjectiveCohomology.isZero_restrictScalars_iff` gives the `Hgroup` statement for every
scheme.

**Three instances are supplied positionally rather than left to synthesis**:
`IsIso` of the projection to the integral model, quasi-coherence of the `Proj`-model
twisting sheaf, and quasi-coherence of a module in the Čech comparison. With the
imports of this file, instance search does not find any of the three even when the fact is a
hypothesis in the local context, while the same `inferInstance` succeeds in a file importing
only `…/ProjectiveCohomology/Basic.lean`. Supplying the instance before elaboration — as a
positional argument to `@asIso` and to the two consumers — works in both cases, so that is what
is done. Which import changes the behaviour was not isolated.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.SchemeIso

/-- **Cohomology is invariant under an isomorphism of schemes.** For an isomorphism
`f : X ⟶ Y` the group `Hᵍ(X, ℳ)` vanishes exactly when `Hᵍ(Y, f_* ℳ)` does.

This is `AlgebraicGeometry.rightDerivedEvaluationTopPushforwardIso` — which needs no base field
— read through the module-valued/abelian-group-valued comparison of
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`
on both sides, restriction of scalars neither creating nor destroying vanishing. -/
public theorem isZero_Hgroup_iff_pushforward_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (M : X.Modules) (q : ℕ) :
    IsZero (Hgroup X.ringCatSheaf ⊤ q M) ↔
      IsZero (Hgroup Y.ringCatSheaf ⊤ q ((Scheme.Modules.pushforward f).obj M)) := by
  refine Iff.trans
    (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf ⊤ q M).symm
    (Iff.trans ?_ (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      Y.ringCatSheaf ⊤ q ((Scheme.Modules.pushforward f).obj M)))
  exact ⟨fun h ↦ IsZero.of_iso
      ((Stacks.ProjectiveCohomology.isZero_restrictScalars_iff
        (f.app (⊤ : Y.Opens)).hom _).mpr h)
      (rightDerivedEvaluationTopPushforwardIso f M q).symm,
    fun h ↦ (Stacks.ProjectiveCohomology.isZero_restrictScalars_iff
      (f.app (⊤ : Y.Opens)).hom _).mp
      (IsZero.of_iso h (rightDerivedEvaluationTopPushforwardIso f M q))⟩

/-- For an isomorphism of schemes, the direct image of an inverse image is the module itself:
`Stacks.Modules.pushforwardIsoPullbackInv` turns the direct image into the inverse image along
the other direction, and the two inverse images cancel by
`AlgebraicGeometry.Scheme.Modules.pullbackEquivOfIso`. -/
public def pushforwardPullbackIso {X Y : Scheme.{u}} (e : X ≅ Y) (F : Y.Modules) :
    (Scheme.Modules.pushforward e.hom).obj ((Scheme.Modules.pullback e.hom).obj F) ≅ F :=
  (Stacks.Modules.pushforwardIsoPullbackInv e).app _ ≪≫
    ((Scheme.Modules.pullbackEquivOfIso e).unitIso.app F).symm

/-- **Cohomology is invariant under an isomorphism of schemes, inverse-image form.** For an
isomorphism `e : X ≅ Y` of schemes and a module `ℱ` on `Y`, `Hᵍ(X, e^* ℱ)` vanishes exactly when
`Hᵍ(Y, ℱ)` does. This is the form a transported *statement* consumes, the module on the smaller
model being the inverse image of the one that is understood. -/
public theorem isZero_Hgroup_pullback_iff {X Y : Scheme.{u}} (e : X ≅ Y) (F : Y.Modules)
    (q : ℕ) :
    IsZero (Hgroup X.ringCatSheaf ⊤ q ((Scheme.Modules.pullback e.hom).obj F)) ↔
      IsZero (Hgroup Y.ringCatSheaf ⊤ q F) := by
  refine (isZero_Hgroup_iff_pushforward_of_isIso e.hom
    ((Scheme.Modules.pullback e.hom).obj F) q).trans ?_
  exact ((Hfunctor Y.ringCatSheaf ⊤ q).mapIso (pushforwardPullbackIso e F)).isZero_iff

end Stacks.Cohomology.SchemeIso

namespace Stacks.ProjectiveCohomology

/-! ### The standard coordinate opens of `Proj R[T₀, …, Tₙ]` as a Čech cover -/

section ProjModel

variable (R : Type u) [CommRing R]

/-- Reducible abbreviation for the library's own
`polyGrading R n`, the grading of `R[T₀, …, Tₙ]` by total
degree. It is introduced only to keep the statements below inside the default `synthInstance`
budget; see the implementation notes. Being an `abbrev` it is transparent to unification and to
instance search, so no statement here is about a second constant —
`Stacks.ProjectiveCohomology.polyGrading_eq` records that. -/
public abbrev polyGrading (n : ℕ) :
    ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- `Stacks.ProjectiveCohomology.polyGrading R n` is, by definition, the grading of
`R[T₀, …, Tₙ]` by total degree. -/
public theorem polyGrading_eq (n : ℕ) :
    polyGrading R n = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R := rfl

/-- The standard coordinate opens `D₊(Tᵢ)` of `Proj R[T₀, …, Tₙ]`, indexed in the universe of
`R`, which is what the Čech comparison of [Stacks, Tag 01XD] requires of a covering. -/
public def basicOpenXAtUniverse (n : ℕ) (i : ULift.{u} (Fin (n + 1))) :
    (AlgebraicGeometry.Proj
      (polyGrading R n)).Opens :=
  Proj.basicOpen (polyGrading R n)
    (MvPolynomial.X i.down)

/-- The standard coordinate opens cover `Proj R[T₀, …, Tₙ]`. -/
public theorem iSup_basicOpenXAtUniverse_eq_top (n : ℕ) :
    (⨆ i, basicOpenXAtUniverse R n i) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R n]
  exact iSup_le fun i => le_iSup_of_le (ULift.up i) le_rfl

/-- Every finite intersection of standard coordinate opens of `Proj R[T₀, …, Tₙ]` is an affine
open, in the indexing the Čech comparison wants. -/
public theorem isAffineOpen_iInf_basicOpenXAtUniverse (n r : ℕ)
    (s : Fin (r + 1) → ULift.{u} (Fin (n + 1))) :
    IsAffineOpen (⨅ k, basicOpenXAtUniverse R n (s k)) :=
  isAffineOpen_iInf_basicOpen_X R (fun k => (s k).down)

/-- A twisting sheaf on `Proj R[T₀, …, Tₙ]` is quasi-coherent: it is invertible, a polynomial
ring being generated in degree one. -/
public theorem isQuasicoherent_twistingSheaf (n : ℕ) (d : ℤ) :
    (ProjectiveSpectrum.Proj.twistingSheaf
      (polyGrading R n) d).IsQuasicoherent := by
  have h : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj
        (polyGrading R n)).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj
          (polyGrading R n)).toRingedSpace).property
      (ProjectiveSpectrum.Proj.twistingSheaf
        (polyGrading R n) d) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2
      (ProjectiveSpectrum.Proj.projectiveSpace_isInvertible_twistingSheaf R (n + 1) d)
  exact Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible
    (AlgebraicGeometry.Proj (polyGrading R n))
    (ProjectiveSpectrum.Proj.twistingSheaf
      (polyGrading R n) d)

/-- **The cohomology of a twist on `Proj R[T₀, …, Tₙ]` is the homology of the explicit Čech
complex of the `n + 1` standard coordinate opens**, in every degree and over every coefficient
ring. The twisting sheaf is quasi-coherent and the finite intersections of the standard opens
are affine, which are the two hypotheses of the vanishing form of [Stacks, Tag 01XD]. -/
public theorem isZero_Hgroup_twistingSheaf_iff (n : ℕ) (d : ℤ) (q : ℕ) :
    IsZero (Hgroup (AlgebraicGeometry.Proj
          (polyGrading R n)).ringCatSheaf ⊤ q
        (ProjectiveSpectrum.Proj.twistingSheaf
          (polyGrading R n) d)) ↔
      IsZero ((cechComplex.{u, u, u, u}
        (⊤ : (AlgebraicGeometry.Proj
          (polyGrading R n)).Opens)
        (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
        (ProjectiveSpectrum.Proj.twistingSheaf
          (polyGrading R n) d)).homology q) :=
  @Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology
    (AlgebraicGeometry.Proj (polyGrading R n)) _ ⊤
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse R n r s) _
    (isQuasicoherent_twistingSheaf R n d) q

/-- **The cohomology of a quasi-coherent module on `Proj R[T₀, …, Tₙ]` vanishes above degree
`n`.** This is the `Proj`-model counterpart of
`Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt`, with the same proof: the `n + 1` standard
coordinate opens are affine and cover, and `Proj` of a graded ring is separated in Mathlib with
no hypothesis at all, so the diagonal is affine. No Noetherian hypothesis on `R` appears and
quasi-coherence replaces coherence. No attribute is attached; see the implementation notes. -/
public theorem isZero_Hgroup_proj_of_lt (n : ℕ)
    (F : (AlgebraicGeometry.Proj
      (polyGrading R n)).Modules) [F.IsQuasicoherent]
    (q : ℕ) (hq : n < q) :
    IsZero (Hgroup (AlgebraicGeometry.Proj
      (polyGrading R n)).ringCatSheaf ⊤ q F) := by
  have hdiag : IsAffineHom (pullback.diagonal (terminal.from (AlgebraicGeometry.Proj
    (polyGrading R n)))) := inferInstance
  exact @Stacks.Cohomology.FiniteCover.isZero_Hgroup_of_finite_affine_cover
    (AlgebraicGeometry.Proj (polyGrading R n)) hdiag F
    inferInstance _
    (fun i : Fin (n + 1) =>
      Proj.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (fun i => Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X R i) one_pos) ⊤
    (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R n) q (by omega)

end ProjModel

/-! ### The two models agree over the integers -/

/-- **The projection to the integral model is an isomorphism over a terminal base.** Projective
`n`-space over `S` is the fibre product of `S` and the integral model over the terminal scheme;
if `S` is itself terminal the first leg is an isomorphism, hence so is the second projection. -/
public theorem isIso_toIntegralAtUniverse_of_isTerminal (n : ℕ) {S : Scheme.{u}}
    (hS : IsTerminal S) : IsIso (projectiveSpaceOver.toIntegralAtUniverse n S) := by
  have : IsIso (terminal.from S) := isIso_of_isTerminal hS terminalIsTerminal _
  dsimp [projectiveSpaceOver.toIntegralAtUniverse]
  infer_instance

/-- **The comparison of the two models over a terminal base**, whose underlying morphism is the
projection to the integral model. -/
public def projectiveSpaceOverIsoAtUniverse (n : ℕ) {S : Scheme.{u}} (hS : IsTerminal S) :
    projectiveSpaceOver n S ≅ projectiveSpaceAtUniverse.{u} n :=
  @asIso _ _ _ _ _ (isIso_toIntegralAtUniverse_of_isTerminal n hS)

/-- The comparison over a terminal base is the projection to the integral model. -/
@[simp]
public theorem projectiveSpaceOverIsoAtUniverse_hom (n : ℕ) {S : Scheme.{u}}
    (hS : IsTerminal S) :
    (projectiveSpaceOverIsoAtUniverse n hS).hom =
      projectiveSpaceOver.toIntegralAtUniverse n S := rfl

/-- The library's name for the integral model and the `Proj` of the integral polynomial ring are
the same term. Recorded so that a statement at either spelling is visibly a statement about the
same constant. -/
public theorem projectiveSpaceAtUniverse_eq (n : ℕ) :
    AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n =
      AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) := rfl

/-- **The two models of projective `n`-space agree over the integers**: the library's
`ℙⁿ` over `ULift ℤ` is `Proj (ULift ℤ)[T₀, …, Tₙ]`, the source's definition, and the
isomorphism is the projection to the integral model. -/
public def integralModelIso (n : ℕ) :
    projectiveSpaceOverRing n (CommRingCat.of (ULift.{u} ℤ)) ≅
      AlgebraicGeometry.Proj
        (polyGrading (ULift.{u} ℤ) n) :=
  projectiveSpaceOverIsoAtUniverse n AlgebraicGeometry.specULiftZIsTerminal.{u}

/-- The comparison of the two models over the integers is the projection of projective
`n`-space over `Spec (ULift ℤ)` to the integral model. -/
@[simp]
public theorem integralModelIso_hom (n : ℕ) :
    (integralModelIso.{u} n).hom =
      projectiveSpaceOver.toIntegralAtUniverse n
        (Spec (CommRingCat.of (ULift.{u} ℤ))) := rfl

/-- `𝒪(d)` on the library's projective `n`-space over the integers. This is both the second
tensor factor of `AlgebraicGeometry.projectiveTwist` and the inverse image of the `Proj`-model
twisting sheaf along `Stacks.ProjectiveCohomology.integralModelIso`: the two are the same term,
since the library's twist is defined by pulling back along the projection to the integral model
and that projection is the comparison isomorphism. -/
public abbrev integralTwist (n : ℕ) (d : ℤ) :
    (projectiveSpaceOverRing n (CommRingCat.of (ULift.{u} ℤ))).Modules :=
  (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n
    (Spec (CommRingCat.of (ULift.{u} ℤ))))).obj
    (ProjectiveSpectrum.Proj.twistingSheaf
      (polyGrading (ULift.{u} ℤ) n) d)

/-- `𝒪(d)` on projective `n`-space over the integers is quasi-coherent: it is the inverse image
of the invertible twisting sheaf of the `Proj` model, hence invertible. -/
public instance isQuasicoherent_integralTwist (n : ℕ) (d : ℤ) :
    (integralTwist.{u} n d).IsQuasicoherent := by
  have h0 := isInvertible_pullback_projectiveSpaceAtUniverseTwistingSheaf
    (R := ULift.{u} ℤ) n d
  have h : Stacks.SheafOfModules.IsInvertible
      (projectiveSpaceOverRing n (CommRingCat.of (ULift.{u} ℤ))).presheaf
      (structureSheafRing
        (projectiveSpaceOverRing n (CommRingCat.of (ULift.{u} ℤ))).toRingedSpace).property
      (integralTwist.{u} n d) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 h0
  exact Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible _ (integralTwist.{u} n d)

/-- **The twisting sheaves correspond, half one:** over the integers `𝒪(d)` on the library's
model is the inverse image of the `Proj`-model twisting sheaf along the comparison isomorphism.
Nothing has to be proved — the library's twist is *defined* by pulling back along the projection
to the integral model, and over a terminal base that projection is the comparison. -/
public theorem integralTwist_eq_pullback_integralModelIso (n : ℕ) (d : ℤ) :
    integralTwist.{u} n d =
      (Scheme.Modules.pullback (integralModelIso.{u} n).hom).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading (ULift.{u} ℤ) n) d) :=
  rfl

/-- **The twisting sheaves correspond, half two:** `AlgebraicGeometry.projectiveTwist` over the
integers is the tensor product with that same module, so a statement about the `Proj`-model
`𝒪(d)` is a statement about the twisting operation the development already uses. -/
public theorem projectiveTwist_eq_integralTwist (n : ℕ) (d : ℤ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of (ULift.{u} ℤ))).Modules) :
    projectiveTwist n F d =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((projectiveSpaceOverRing n (CommRingCat.of (ULift.{u} ℤ))).toSheafedSpace)).presheaf,
          (((projectiveSpaceOverRing n
            (CommRingCat.of (ULift.{u} ℤ))).toSheafedSpace)).IsSheaf⟩))).obj
        (F, integralTwist.{u} n d) :=
  rfl

/-- **The cohomology of `𝒪(d)` is the same on both models over the integers.** The left-hand
side is the library's `Hᵍ(ℙⁿ_ℤ, 𝒪(d))`, the right-hand side the `Proj`-model one, and the two
agree because the models are isomorphic and the library's twist is the inverse image of the
`Proj`-model twist along that isomorphism. -/
public theorem isZero_Hgroup_integralTwist_iff (n : ℕ) (d : ℤ) (q : ℕ) :
    IsZero (Hgroup (projectiveSpaceOverRing n (CommRingCat.of (ULift.{u} ℤ))).ringCatSheaf
        ⊤ q (integralTwist.{u} n d)) ↔
      IsZero (Hgroup (AlgebraicGeometry.Proj
          (polyGrading (ULift.{u} ℤ) n)).ringCatSheaf ⊤ q
        (ProjectiveSpectrum.Proj.twistingSheaf
          (polyGrading (ULift.{u} ℤ) n) d)) :=
  Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff (integralModelIso.{u} n)
    (ProjectiveSpectrum.Proj.twistingSheaf
      (polyGrading (ULift.{u} ℤ) n) d) q

/-! ### The top-degree object of the projective situation -/

open Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation in
/-- **The top-degree object of the projective situation over the integers is nonzero as soon as
`Hⁿ(Proj (ULift ℤ)[T₀, …, Tₙ], 𝒪(d))` is.** The consumer is stated on the library's model
and this feeds the model comparison into it directly, with no bridging lemma. -/
public theorem not_isZero_topDirectImage_of_not_isZero_Hgroup_twistingSheaf (n : ℕ) (d : ℤ)
    (h : ¬ IsZero (Hgroup (AlgebraicGeometry.Proj
      (polyGrading (ULift.{u} ℤ) n)).ringCatSheaf ⊤ n
      (ProjectiveSpectrum.Proj.twistingSheaf
        (polyGrading (ULift.{u} ℤ) n) d))) :
    ¬ IsZero (((Scheme.Modules.pushforward
      (ofProjectiveSpaceSelf n (CommRingCat.of (ULift.{u} ℤ))).f').rightDerivedPlus
      (((ofProjectiveSpaceSelf n (CommRingCat.of (ULift.{u} ℤ))).d : ℕ) : ℤ)).obj
      (integralTwist.{u} n d)) :=
  not_isZero_topDirectImage_of_not_isZero_Hgroup n (CommRingCat.of (ULift.{u} ℤ))
    (integralTwist.{u} n d) fun hz => h ((isZero_Hgroup_integralTwist_iff.{u} n d n).mp hz)

open Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation in
/-- **Non-degeneracy of the projective situation, reduced to the Čech complex of the model where
the terms are described.** The top-degree object of `ofProjectiveSpaceSelf n (ULift ℤ)` is
nonzero as soon as the degree-`n` homology of the Čech cochain complex of the `n + 1` standard
coordinate opens of `Proj (ULift ℤ)[T₀, …, Tₙ]`, with coefficients in the twisting sheaf
`𝒪(d)`, is nonzero.

The hypothesis mentions no situation, no derived category, no higher direct image and no sheaf
cohomology; and unlike the previous reduction on the library's model, every term of this complex
is identified — it is the free module on the Laurent monomials of total degree `d` that are
nonnegative on the coordinates that were not inverted, by
`Stacks.ProjectiveCohomology.sectionsTwistProdXEquivWeightSpan`. The witness the source uses is
`d = -n-1`. -/
public theorem not_isZero_topDirectImage_of_not_isZero_cechHomology_twistingSheaf
    (n : ℕ) (d : ℤ)
    (h : ¬ IsZero ((cechComplex.{u, u, u, u}
      (⊤ : (AlgebraicGeometry.Proj
        (polyGrading (ULift.{u} ℤ) n)).Opens)
      (basicOpenXAtUniverse (ULift.{u} ℤ) n)
      (iSup_basicOpenXAtUniverse_eq_top (ULift.{u} ℤ) n).symm
      (ProjectiveSpectrum.Proj.twistingSheaf
        (polyGrading (ULift.{u} ℤ) n) d)).homology n)) :
    ¬ IsZero (((Scheme.Modules.pushforward
      (ofProjectiveSpaceSelf n (CommRingCat.of (ULift.{u} ℤ))).f').rightDerivedPlus
      (((ofProjectiveSpaceSelf n (CommRingCat.of (ULift.{u} ℤ))).d : ℕ) : ℤ)).obj
      (integralTwist.{u} n d)) :=
  not_isZero_topDirectImage_of_not_isZero_Hgroup_twistingSheaf n d
    fun hz => h ((isZero_Hgroup_twistingSheaf_iff (ULift.{u} ℤ) n d n).mp hz)

end Stacks.ProjectiveCohomology

end
