module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLineBaseChange

/-!
# Base change of a two-term finite-projective presentation

Let `φ : R → A` be a homomorphism of commutative rings and let `K` be an object of `D(R)` with a
two-term presentation by finite projective modules in degrees `-1` and `0`. The termwise
extension of scalars of the presenting complex is again a two-term complex of finite projective
modules, and it presents the total derived extension of scalars of `K`: a bounded complex of
projective modules is K-flat, and a K-flat complex computes derived extension of scalars.

This is the ring-level half of the chart-change step in the construction of the determinant of a
two-term perfect complex on a scheme: on a smaller affine chart the complex presenting the
restriction is the base change of the complex presenting it on the larger one.

## Main definitions

* `TwoTermDeterminant.presentationBaseChangeComplexMap` and
  `TwoTermDeterminant.presentationBaseChangeComplex`: the termwise extension of scalars of the
  presenting complex, as the image of `ModuleCat.extendScalars` under
  `Functor.mapHomologicalComplex` and with its terms spelled as the tensor products themselves;
  they agree by definition.
* `TwoTermDeterminant.TwoTermPresentation.baseChange`: **the base change of a two-term
  finite-projective presentation**, a two-term finite-projective presentation of the total derived
  extension of scalars.

## Main results

* `TwoTermDeterminant.finite_extendScalars` and `TwoTermDeterminant.projective_extendScalars`: the
  extension of scalars of a finite projective module is finite projective.
* `TwoTermDeterminant.TwoTermPresentation.baseChange_complex`: the presenting complex of the base
  change is the termwise extension of scalars, by definition.
* `TwoTermDeterminant.TwoTermPresentation.baseChange_isRankZero`: a rank-zero presentation stays
  rank zero after base change, the rank of `A ⊗_R M` at a prime of `A` being the rank of `M` at
  the prime below it.
* `TwoTermDeterminant.perfectTwoTermComplexProperty_of_presentation`: an object with a two-term
  finite-projective presentation is perfect of Tor-amplitude in `[-1, 0]`, the converse of
  `TwoTermDeterminant.nonempty_twoTermPresentation`.
* `TwoTermDeterminant.PerfectTwoTermComplex.baseChange`: **the base change of a perfect object of
  Tor-amplitude in `[-1, 0]`**, with `baseChange_obj` and
  `TwoTermPresentation.baseChange_presents`.

## Implementation notes

Derived extension of scalars is
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, whose `comparison` to the
termwise construction is invertible on a K-flat complex. K-flatness of
the presenting complex comes from `CochainComplex.KFlat.kFlat_of_flat` (Tag 064K) applied with the
upper bound `0`, projective modules being flat; only the upper bound is used, the lower bound of a
two-term presentation playing no role here.

The `IsIso` instance for the comparison has to be supplied explicitly rather than by instance
search: the comparison lands in `extensionOfScalarsComplexGeneral`, which is definitionally the
termwise construction followed by localization but only through a semireducible definition, and
`IsIso` carries its endpoints. The same transparency point is recorded in
`StacksFrontier.AlgebraicGeometry.DerivedTilde.FlatBaseChangeComplex`.

No flatness of `A` over `R` is needed: the presenting complex is a bounded complex of projectives,
so it computes the derived functor whatever `φ` is.

**Why the base-changed complex is spelled twice.** The determinant line of a two-term complex is a
module of homomorphisms between submodules of exterior algebras on its two terms, and comparing
two spellings of a term forces the elaborator to compare the `Module` instances on those exterior
algebras. Written as `((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj P.complex`, the
term in degree `i` is a value of a functor applied to a value of another functor and does not
match the `A ⊗[R] -` that `TwoTermComplex.determinantLineBaseChange` produces, so that comparison
is carried out through `ProjectiveDeterminant.submodule` and does not terminate within the
heartbeat limit. `TwoTermDeterminant.presentationBaseChangeComplex` writes the same complex with
`X i` literally `ModuleCat.of A (A ⊗[R] P^i)`; the two are definitionally equal, by
`presentationBaseChangeComplex_eq`, and the determinant lines then agree on the nose.

## References

* [Stacks Project, Section 15.63 (Tag 064F)](https://stacks.math.columbia.edu/tag/064F)
* [Stacks Project, Lemma 15.63.2 (Tag 064K)](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

namespace TwoTermDeterminant

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] (φ : R →+* A)


/-- The extension of scalars of a finite module is finite. -/
theorem finite_extendScalars (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite A ((ModuleCat.extendScalars.{u, u, u} φ).obj M) :=
  let : Algebra R A := φ.toAlgebra
  inferInstanceAs (Module.Finite A (A ⊗[R] M))

/-- The extension of scalars of a projective module is projective. -/
theorem projective_extendScalars (M : ModuleCat.{u} R) [Module.Projective R M] :
    Module.Projective A ((ModuleCat.extendScalars.{u, u, u} φ).obj M) :=
  let : Algebra R A := φ.toAlgebra
  inferInstanceAs (Module.Projective A (A ⊗[R] M))

/-- The termwise extension of scalars of the complex presenting a two-term presentation, as the
image of `ModuleCat.extendScalars` under `Functor.mapHomologicalComplex`. -/
abbrev presentationBaseChangeComplexMap {K : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) : CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.complex

/-- **The termwise extension of scalars of the complex presenting a two-term presentation**, with
its terms spelled as the tensor products `A ⊗_R P^i` themselves.

This is `TwoTermDeterminant.presentationBaseChangeComplexMap` — the two agree by definition,
`TwoTermDeterminant.presentationBaseChangeComplex_eq` — but with the degrees written in the
spelling `A ⊗[R] -` rather than as values of `ModuleCat.extendScalars`. The determinant line of
the base-changed complex is then the one `TwoTermComplex.determinantLineBaseChange` produces on
the nose, which is what keeps the comparison of the two determinant lines cheap; see the
implementation notes. -/
def presentationBaseChangeComplex {K : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) : CochainComplex (ModuleCat.{u} A) ℤ :=
  letI : Algebra R A := φ.toAlgebra
  { X := fun i => ModuleCat.of A (A ⊗[R] ((P.complex.X i) : Type u))
    d := fun i j => ModuleCat.ofHom (LinearMap.baseChange A (P.complex.d i j).hom)
    shape := fun i j h => (presentationBaseChangeComplexMap φ P).shape i j h
    d_comp_d' := fun i j k hij hjk =>
      (presentationBaseChangeComplexMap φ P).d_comp_d' i j k hij hjk }

/-- The two spellings of the base-changed complex agree by definition. -/
theorem presentationBaseChangeComplex_eq {K : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) :
    presentationBaseChangeComplex φ P = presentationBaseChangeComplexMap φ P := rfl

/-- **The base change of a two-term finite-projective presentation.** The termwise extension of
scalars of the presenting complex is a two-term complex of finite projective `A`-modules, and it
presents the total derived extension of scalars of the presented object: the presenting complex is
a bounded complex of projectives, hence K-flat by Tag 064K, and a K-flat complex computes derived
extension of scalars. -/
def TwoTermPresentation.baseChange {K : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) :
    TwoTermPresentation ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K) where
  complex := presentationBaseChangeComplex φ P
  finite i := haveI := P.finite i; finite_extendScalars φ (P.complex.X i)
  projective i := haveI := P.projective i; projective_extendScalars φ (P.complex.X i)
  strictlyGE := haveI := P.strictlyGE
    inferInstanceAs ((presentationBaseChangeComplexMap φ P).IsStrictlyGE (-1))
  strictlyLE := haveI := P.strictlyLE
    inferInstanceAs ((presentationBaseChangeComplexMap φ P).IsStrictlyLE 0)
  iso :=
    haveI := P.strictlyLE
    haveI : ∀ i, Module.Flat R (P.complex.X i) := fun i =>
      haveI := P.projective i; Module.Flat.of_projective
    haveI hiso : IsIso ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P.complex) :=
      (totalDerivedExtensionScalars.{u, u, u} φ).comparison_isIso_of_kFlat P.complex
        (CochainComplex.KFlat.kFlat_of_flat.{u, u} P.complex 0)
    (totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso P.iso ≪≫ @asIso _ _ _ _ _ hiso

/-- The presenting complex of the base change of a presentation is the termwise extension of
scalars of the presenting complex. -/
@[simp] theorem TwoTermPresentation.baseChange_complex
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) :
    (P.baseChange φ).complex = presentationBaseChangeComplex φ P := rfl

/-- **A rank-zero two-term presentation stays rank zero after base change.** The rank of
`A ⊗_R M` at a prime of `A` is the rank of `M` at the prime below it. -/
theorem TwoTermPresentation.baseChange_isRankZero {K : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (hP : P.IsRankZero) : (P.baseChange φ).IsRankZero := by
  let : Algebra R A := φ.toAlgebra
  have := P.finite (-1)
  have := P.projective (-1)
  have := P.finite 0
  have := P.projective 0
  exact TwoTermComplex.isRankZero_baseChange A hP

/-- **An object of `D(R)` with a two-term finite-projective presentation is perfect of
Tor-amplitude in `[-1, 0]`.** Being perfect is being represented by a bounded complex of finite
projective modules, and a bounded complex of projectives is in particular a bounded flat
representative in degrees `[-1, 0]`. This is the converse of
`TwoTermDeterminant.nonempty_twoTermPresentation`. -/
theorem perfectTwoTermComplexProperty_of_presentation {K : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) : perfectTwoTermComplexProperty R K :=
  ⟨⟨P.complex, -1, 0, P.strictlyGE, P.strictlyLE, P.finite, P.projective, ⟨P.iso⟩⟩,
    ⟨P.complex, fun i => have := P.projective i; Module.Flat.of_projective,
      P.strictlyGE, P.strictlyLE, ⟨P.iso⟩⟩⟩

/-- **The base change of a perfect object of Tor-amplitude in `[-1, 0]`.** Its total derived
extension of scalars is again perfect of Tor-amplitude in `[-1, 0]`, being presented by the base
change of any two-term finite-projective presentation. -/
def PerfectTwoTermComplex.baseChange (K : PerfectTwoTermComplex R) : PerfectTwoTermComplex A :=
  ⟨(totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K.obj,
    perfectTwoTermComplexProperty_of_presentation
      ((Classical.choice (nonempty_twoTermPresentation K)).baseChange φ)⟩

/-- The object underlying the base change of a perfect object of Tor-amplitude in `[-1, 0]` is
its total derived extension of scalars. -/
@[simp] theorem PerfectTwoTermComplex.baseChange_obj (K : PerfectTwoTermComplex R) :
    (PerfectTwoTermComplex.baseChange φ K).obj =
      (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K.obj := rfl

/-- The base change of a two-term finite-projective presentation of `K` presents the base change
of `K`. -/
def TwoTermPresentation.baseChange_presents {K : PerfectTwoTermComplex R}
    (P : TwoTermPresentation K.obj) :
    (PerfectTwoTermComplex.baseChange φ K).obj ≅
      DerivedCategory.Q.obj (presentationBaseChangeComplex φ P) :=
  (P.baseChange φ).iso

end TwoTermDeterminant

end
