module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardStep

/-!
# The twisted global sections of the blowup are a finite module over the Rees algebra

Let `A` be a Noetherian ring, `I ⊆ A` an ideal with a chosen finite generating family
`x₀, …, x_m`, and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec A` in `I`. This file proves
[Stacks, Tag 01YS] clause (5) for the Rees grading: for every `k ∈ ℤ` the graded `⨁ₙ Iⁿ`-module
`⨁_{d ≥ k} Γ(X, 𝒪_X(d))` is a finite `⨁ₙ Iⁿ`-module.

Both hypotheses of
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation` are
now available for `𝒮 = Stacks.Blowup.reesGrading I`. The second, `hstep`, is
`Stacks.Blowup.exists_forall_mem_degreeOneSections_reesGrading`, transported from projective
space in `StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardStep.lean`. The first,
`hfg` — that each homogeneous piece spans a finitely generated submodule — is what this file
supplies, and it has two halves.

## The coefficients as global functions on the blowup

The structure morphism `Stacks.Blowup.toSpec` of the blowup is, by construction,
`AlgebraicGeometry.Proj.toSpecZero` followed by `Spec` of
`Stacks.Blowup.reesGradingZeroEquiv`, the identification of `A` with the degree-zero part of the
Rees algebra. So `Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val`, which
describes the global sections of `Proj 𝒜 ⟶ Spec 𝒜₀` for an arbitrary graded ring, computes the
pullback of a coefficient `a : A` along it: `Stacks.Blowup.blowUpCoeffScalar_val` says the value
of that global function at every point of `X` is the fraction `a / 1`.

That is exactly the hypothesis of
`Stacks.AlgebraicGeometry.ProjTwistedSections.cast_homogeneousScalarTwistedSections_zero`, so
`Stacks.Blowup.reesGradingZeroEquiv_smul_of` identifies the degree-zero graded action of
`reesGrading I 0` on the summand `Γ(X, 𝒪_X(d))` with the action of `A` through
`Stacks.Blowup.blowUpCoeffScalar`. This is the `hι` of
`Stacks.AlgebraicGeometry.ProjTwistedSections.fg_span_twistedGlobalSectionsGrading_of_span_eq_top`.

## Finiteness of one section group over the coefficients

`Stacks.Blowup.twistedSectionsUnitMap` is a bijection `Γ(𝐏, (i_*𝒪_X)(d)) → Γ(X, 𝒪_X(d))` and is
`Γ(𝐏, 𝒪_𝐏)`-linear, being the global sections of a morphism of `𝒪_𝐏`-modules; the sections of a
direct image over the whole target carry the scalars of the target restricted along `i^\#`
(`Stacks.Cohomology.AffineBase.pushforwardSectionsIso`, the identity). That reading of the
linearity is `Stacks.Blowup.twistedSectionsUnitMap_smul`, and
`Stacks.Blowup.moduleFinite_unitSections_of_pushforward` turns it into a transport of finiteness
over any coefficient ring acting through global functions on both sides compatibly with `i^\#`.
The finiteness of the source is
`Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistedSectionsComponent`, with `A` acting
through `Stacks.ProjectiveSpace.Cohomology.coeffScalar`.

The compatibility itself is
`Stacks.Blowup.blowUpSpecToProjSpace_comp_projSpaceToSpec` read on
`AlgebraicGeometry.Scheme.Hom.appTop`: `Stacks.Blowup.projMapGlobalFunctions_coeffScalar`. The two
structure morphisms of projective space in play, `Stacks.Blowup.projSpaceToSpec` and
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`, identify `A` with the degree-zero part
of the total-degree grading by two different ring homomorphisms, both sending `a` to the constant
`C a`; `Stacks.Blowup.projSpaceToSpec_eq_projToSpecCoeff` reconciles them.

## Where `hfg` is, and why it is not a statement

`hfg` is not stated for the blowup. Writing `Submodule.span (reesAlgebra I) …` into a statement
sends `isDefEq` through the module paths of the `Subalgebra` carrier and exhausts the kernel's
deterministic reduction budget; the span forms are therefore kept as lemmas over an arbitrary
graded ring and instantiated inside the proof of
`Stacks.Blowup.moduleFinite_truncation_reesGrading`. The extraction of a finite generating family
from `Module.Finite`, which is all that stands between
`Stacks.AlgebraicGeometry.ProjTwistedSections.fg_span_twistedGlobalSectionsGrading_of_span_eq_top`
and `hfg`, is done over an arbitrary graded ring for the same reason:
`Stacks.Blowup.fg_span_twistedGlobalSectionsGrading_of_moduleFinite`.

## Main results

The elided prefix is `Stacks.Blowup`.

* `blowUpCoeffScalar` and `blowUpCoeffScalar_val`: the coefficients as global functions on the
  blowup, and their values in the fibres.
* `reesGradingZeroEquiv_smul_of`: the degree-zero graded action is that of the coefficients —
  the `hι` of `fg_span_twistedGlobalSectionsGrading_of_span_eq_top`.
* `projMapGlobalFunctions` and `twistedSectionsUnitMap_smul`: `π^\#` on global functions, and the
  linearity of the comparison over it.
* `moduleFinite_unitSections_of_pushforward`: the transport of finiteness over the coefficients
  along the comparison, for an arbitrary graded surjection whose `Proj` is a closed immersion.
* `fg_span_twistedGlobalSectionsGrading_of_moduleFinite`: a homogeneous piece whose section group
  is a finite module over the coefficients spans a finitely generated submodule.
* `projSpaceToSpec_eq_projToSpecCoeff` and `projMapGlobalFunctions_coeffScalar`: the closed
  immersion carries the coefficients of `𝐏` to the coefficients of `X`.
* `moduleFinite_twistedSectionsComponent_reesGrading`: `Γ(X, 𝒪_X(d))` is a finite `A`-module.
* `moduleFinite_truncation_reesGrading`: **[Stacks, Tag 01YS] clause (5) for the Rees grading.**

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistSheafOfModules twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedSectionsComponent
  twistedGlobalSectionsGrading homogeneousScalarTwistedSections twistedDegree_zero
  TwistedGlobalSectionsModule fg_span_twistedGlobalSectionsGrading_of_span_eq_top
  moduleFinite_twistedGlobalSectionsTruncation)
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistFunctor (projRingSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)

universe u w

namespace Stacks.Blowup

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

section StructureMorphism

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **The coefficients as global functions on the blowup.** The ring homomorphism
`R → Γ(X, 𝒪_X)` obtained from the structure morphism `Stacks.Blowup.toSpec` by identifying `R`
with the global sections of `Spec R`. -/
def blowUpCoeffScalar : R →+* SectionRing (projRingSheaf (reesGrading I)) ⊤ :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom

/-- **The structure morphism of the blowup on global sections.** Composed with the identification
of `R` with the global sections of `Spec R`, it is the identification of `R` with the degree-zero
part of the Rees grading followed by the structure morphism of `Proj`. -/
theorem ΓSpecIso_inv_comp_toSpec_appTop :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop =
      CommRingCat.ofHom (reesGradingZeroEquiv I).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (reesGrading I 0))).inv ≫
          (Proj.toSpecZero (reesGrading I)).appTop :=
  (Scheme.ΓSpecIso_inv_naturality_assoc
    (CommRingCat.ofHom (reesGradingZeroEquiv I).toRingHom)
    (Proj.toSpecZero (reesGrading I)).appTop).symm

/-- **The coefficients pull back to the constant fractions.** The value of the global function
`Stacks.Blowup.blowUpCoeffScalar I a` at every point of the blowup is the fraction `a / 1`, the
numerator being `a` read in the degree-zero part of the Rees algebra. -/
theorem blowUpCoeffScalar_val (a : R) (x : ProjectiveSpectrum.top (reesGrading I)) :
    HomogeneousLocalization.val ((blowUpCoeffScalar I a).1 ⟨x, trivial⟩) =
      algebraMap (reesAlgebra I) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I) := by
  have h := DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (ΓSpecIso_inv_comp_toSpec_appTop I)) a
  refine Eq.trans (congrArg
    (fun s : Γ(AlgebraicGeometry.Proj (reesGrading I), ⊤) =>
      HomogeneousLocalization.val (s.1 ⟨x, trivial⟩)) h) ?_
  exact Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val
    (reesGrading I) (reesGradingZeroEquiv I a) x

variable (F : SheafOfModules.{u} (projRingSheaf (reesGrading I)))

/-- **The coefficients act through the degree-zero scalars on the blowup.** On the global sections
of `ℱ(n)` the degree-zero homogeneous scalar `a : R`, read in `reesGrading I 0`, acts as the
global function that `a` pulls back to along the structure morphism `X ⟶ Spec R`, once the degree
`0 + n` is identified with `n`. -/
theorem cast_homogeneousScalarTwistedSections_reesGradingZeroEquiv (n : ℤ) (a : R)
    (s : twistedSectionsComponent (reesGrading I) F n) :
    cast (congrArg (twistedSectionsComponent (reesGrading I) F) (twistedDegree_zero n))
        (homogeneousScalarTwistedSections (reesGrading I) F 0 n
          (reesGradingZeroEquiv I a) s) =
      blowUpCoeffScalar I a • s :=
  Stacks.AlgebraicGeometry.ProjTwistedSections.cast_homogeneousScalarTwistedSections_zero
    (reesGrading I) F n (reesGradingZeroEquiv I a) (blowUpCoeffScalar I a)
    (fun x => blowUpCoeffScalar_val I a x) s

/-- **The `R = 𝒮₀` action bridge on the blowup.** For the graded `⨁ₙ Iⁿ`-module structure on
`⨁_{n ∈ ℤ} Γ(X, ℱ(n))`, a coefficient `a : R` acting through its image in `reesGrading I 0` acts
on the degree-`n` summand as the global function that `a` pulls back to along `X ⟶ Spec R`, which
is the `R`-action of `Stacks.Blowup.blowUpCoeffScalar`.

This is the hypothesis `hι` of
`Stacks.AlgebraicGeometry.ProjTwistedSections.fg_span_twistedGlobalSectionsGrading_of_span_eq_top`
for `ι` the inclusion of the degree-zero part of the Rees algebra. -/
theorem reesGradingZeroEquiv_smul_of (D : TwistedGlobalSectionsModule (reesGrading I) F)
    (a : R) (n : ℤ) (s : twistedSectionsComponent (reesGrading I) F n) :
    letI := D.moduleInst
    ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I) •
        (DirectSum.of (fun k : ℤ => twistedSectionsComponent (reesGrading I) F k) n s :
          twistedGlobalSections (reesGrading I) F) =
      DirectSum.of (fun k : ℤ => twistedSectionsComponent (reesGrading I) F k) n
        (blowUpCoeffScalar I a • s) :=
  let := D.moduleInst
  (D.smul_homogeneous 0 n (reesGradingZeroEquiv I a) s).trans
    (DirectSum.of_eq_of_heq (twistedDegree_zero n)
      ((cast_heq (congrArg (twistedSectionsComponent (reesGrading I) F)
            (twistedDegree_zero n)) _).symm.trans
        (heq_of_eq
          (cast_homogeneousScalarTwistedSections_reesGradingZeroEquiv I F n a s))))

end StructureMorphism

section General

variable {S B' σ τ : Type u} [CommRing S] [CommRing B'] [SetLike σ S] [AddSubgroupClass σ S]
  [SetLike τ B'] [AddSubgroupClass τ B'] (𝒮 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒮] [GradedRing ℬ]
  (ψ : 𝒮 →+*ᵍ ℬ)
  (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
  (hsurj : Function.Surjective (ψ : S → B'))
  (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
  [IsClosedImmersion (AlgebraicGeometry.Proj.map ψ hψ)]

/-- **`π^\#` on global functions**, for `π = Proj ψ`, with both source and target spelled through
the sheaf of rings that the twisting sheaves are modules over. -/
def projMapGlobalFunctions :
    SectionRing (projRingSheaf 𝒮) ⊤ →+* SectionRing (projRingSheaf ℬ) ⊤ :=
  (AlgebraicGeometry.Proj.map ψ hψ).appTop.hom

/-- **The comparison on global sections is linear over the global functions of the target of
`π = Proj ψ`.** A global function `c` of `Proj 𝒮` acts on `Γ(Proj ℬ, 𝒪(d))` through
`π^\#`, the sections of a direct image over the whole target being the sections of the source with
their scalars restricted (`Stacks.Cohomology.AffineBase.pushforwardSectionsIso`, the identity), so
the `Γ(Proj 𝒮, 𝒪)`-linearity of the global sections of a morphism of `𝒪_{Proj 𝒮}`-modules reads as
this. -/
theorem twistedSectionsUnitMap_smul (d : ℤ) (c : SectionRing (projRingSheaf 𝒮) ⊤)
    (s : twistedSectionsComponent 𝒮 ((Scheme.Modules.pushforward
      (AlgebraicGeometry.Proj.map ψ hψ)).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d) :
    twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d (c • s) =
      projMapGlobalFunctions 𝒮 ℬ ψ hψ c •
        twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d s :=
  map_smul ((pushforwardTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d).hom.val.app (op ⊤)).hom c s

/-- `Γ(Proj 𝒮, (π_*𝒪_{Proj ℬ})(d))`, the source of the comparison on global sections. -/
abbrev pushforwardUnitSections (d : ℤ) : Type u :=
  twistedSectionsComponent 𝒮 ((Scheme.Modules.pushforward
    (AlgebraicGeometry.Proj.map ψ hψ)).obj
      (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf)) d

/-- `Γ(Proj ℬ, 𝒪(d))`, the target of the comparison on global sections. -/
abbrev unitSections (d : ℤ) : Type u :=
  twistedSectionsComponent ℬ (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf) d

variable (R : Type u) [CommRing R] (ι𝒮 : R →+* SectionRing (projRingSheaf 𝒮) ⊤)
  (ιℬ : R →+* SectionRing (projRingSheaf ℬ) ⊤)

include hsurj hgen in
/-- **Finiteness of the twisted global sections over a coefficient ring transports along the
comparison.** The coefficients act on each side through a ring homomorphism to the global
functions — the hypotheses `h𝒮` and `hℬ` say so, and both are `rfl` for the actions obtained by
restriction of scalars — and `hι` makes the two compatible with `π^\#`. Then
`Stacks.Blowup.twistedSectionsUnitMap` is a surjective `R`-linear map, by
`Stacks.Blowup.twistedSectionsUnitMap_smul`. -/
theorem moduleFinite_unitSections_of_pushforward (d : ℤ)
    [Module R (pushforwardUnitSections 𝒮 ℬ ψ hψ d)] [Module R (unitSections ℬ d)]
    (h𝒮 : ∀ (r : R) (s : pushforwardUnitSections 𝒮 ℬ ψ hψ d), r • s = ι𝒮 r • s)
    (hℬ : ∀ (r : R) (t : unitSections ℬ d), r • t = ιℬ r • t)
    (hι : ∀ r : R, projMapGlobalFunctions 𝒮 ℬ ψ hψ (ι𝒮 r) = ιℬ r)
    (hM : Module.Finite R (pushforwardUnitSections 𝒮 ℬ ψ hψ d)) :
    Module.Finite R (unitSections ℬ d) := by
  let := hM
  refine Module.Finite.of_surjective
    ({ toFun := twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d
       map_add' := twistedSectionsUnitMap_add 𝒮 ℬ ψ hψ hsurj hgen d
       map_smul' := ?_ } :
      pushforwardUnitSections 𝒮 ℬ ψ hψ d →ₗ[R] unitSections ℬ d)
    (twistedSectionsUnitMap_surjective 𝒮 ℬ ψ hψ hsurj hgen d)
  intro r s
  change twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d (r • s) =
    r • twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d s
  rw [h𝒮 r s, twistedSectionsUnitMap_smul 𝒮 ℬ ψ hψ hsurj hgen d (ι𝒮 r) s, hι r,
    ← hℬ r (twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d s)]

end General

section Grading

variable {Sr : Type u} {σ : Type w} [CommRing Sr] [SetLike σ Sr] [AddSubgroupClass σ Sr]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (G : SheafOfModules.{u} (projRingSheaf 𝒜))

/-- **A homogeneous piece whose section group is a finite module over a coefficient ring spans a
finitely generated submodule.** This is
`Stacks.AlgebraicGeometry.ProjTwistedSections.fg_span_twistedGlobalSectionsGrading_of_span_eq_top`
with the finite generating family extracted from `Module.Finite` rather than passed as data.

The extraction is done here, over an arbitrary graded ring, because performing it at
`Sr = ⨁ₙ Iⁿ` sends `isDefEq` through the `Subalgebra` carrier's module paths and exhausts the
deterministic reduction budget. -/
theorem fg_span_twistedGlobalSectionsGrading_of_moduleFinite
    [Module Sr (twistedGlobalSections 𝒜 G)] (d : ℤ) (R : Type u) [CommRing R]
    [Module R (twistedSectionsComponent 𝒜 G d)] (ι : R → Sr)
    (hι : ∀ (r : R) (s : twistedSectionsComponent 𝒜 G d),
      ι r • (DirectSum.of (fun n : ℤ => twistedSectionsComponent 𝒜 G n) d s :
          twistedGlobalSections 𝒜 G) =
        DirectSum.of (fun n : ℤ => twistedSectionsComponent 𝒜 G n) d (r • s))
    (hfin : Module.Finite R (twistedSectionsComponent 𝒜 G d)) :
    (Submodule.span Sr (twistedGlobalSectionsGrading 𝒜 G d :
      Set (twistedGlobalSections 𝒜 G))).FG := by
  classical
  obtain ⟨t, ht⟩ := Module.finite_def.mp hfin
  exact fg_span_twistedGlobalSectionsGrading_of_span_eq_top 𝒜 G d ι hι t ht

/-- The coefficient action on `Γ(Proj 𝒜, 𝒢(d))`, by restriction of scalars along a ring
homomorphism to the global functions. -/
private abbrev coeffModule (R : Type u) [CommRing R] (ι : R →+* SectionRing (projRingSheaf 𝒜) ⊤)
    (d : ℤ) : Module R (twistedSectionsComponent 𝒜 G d) :=
  ((ModuleCat.restrictScalars.{u} ι).obj
    ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj 𝒜) ⊤).obj
      (twistSheafOfModules 𝒜 G d))).isModule

end Grading

section Blowup

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The two identifications of the coefficients with the degree-zero forms agree.**
`Stacks.Blowup.projSpaceToSpec` uses `AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv` and
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff` uses `GradedRing.projZeroRingHom'` after
`algebraMap`; both send `r` to the constant polynomial `C r`, and a degree-zero form is determined
by the polynomial underlying it. -/
theorem gradeZeroEquiv_toRingHom_eq (R : Type u) [CommRing R] (n : ℕ) :
    (AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv (Fin (n + 1)) R).toRingHom =
      (GradedRing.projZeroRingHom' (polyGrading R n)).comp
        (algebraMap R (MvPolynomial (Fin (n + 1)) R)) := by
  refine RingHom.ext fun r => Subtype.ext ?_
  rw [Stacks.AlgebraicGeometry.ProjEulerSequence.coe_projZeroRingHom'_algebraMap R n r,
    show ((AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv (Fin (n + 1)) R).toRingHom r :
        polyGrading R n 0) =
      algebraMap R (polyGrading R n 0) r from rfl,
    SetLike.GradeZero.coe_algebraMap]
  simp [MvPolynomial.algebraMap_eq]

/-- **The two structure morphisms of projective space over the coefficients are the same
morphism.** -/
theorem projSpaceToSpec_eq_projToSpecCoeff (R : Type u) [CommRing R] (n : ℕ) :
    projSpaceToSpec R (n + 1) =
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n := by
  rw [projSpaceToSpec, Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff,
    gradeZeroEquiv_toRingHom_eq R n]

variable {A : Type u} [CommRing A] {I : Ideal A} {m : ℕ} (x : Fin (m + 1) → A)
  (hx : ∀ j, x j ∈ I) (hspan : I = Ideal.span (Set.range x))

/-- **The closed immersion of the blowup carries the coefficients to the coefficients.** The
global function on `𝐏` that `a : A` pulls back to along `𝐏 ⟶ Spec A` pulls back along
`i : X ⟶ 𝐏` to the global function on `X` that `a` pulls back to along `X ⟶ Spec A`: this is
`Stacks.Blowup.blowUpSpecToProjSpace_comp_projSpaceToSpec`, read on
`AlgebraicGeometry.Scheme.Hom.appTop`. -/
theorem projMapGlobalFunctions_coeffScalar (a : A) :
    projMapGlobalFunctions (polyGrading A m) (reesGrading I) (reesPresentation I x hx)
        (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
          (surjective_reesPresentation I x hx hspan))
        (Stacks.ProjectiveSpace.Cohomology.coeffScalar A m a) =
      blowUpCoeffScalar I a := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff A m).appTop ≫
          (blowUpSpecToProjSpace I x hx hspan).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (toSpec I).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← projSpaceToSpec_eq_projToSpecCoeff A m,
      blowUpSpecToProjSpace_comp_projSpaceToSpec I x hx hspan]
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp h) a

include x hx hspan in
/-- **`Γ(X, 𝒪_X(d))` is a finite `A`-module.** The comparison
`Stacks.Blowup.twistedSectionsUnitMap` is a surjection from `Γ(𝐏, (i_*𝒪_X)(d))`, which is a finite
`A`-module by `Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistedSectionsComponent`, and it is
`A`-linear for the coefficient actions on the two sides by
`Stacks.Blowup.projMapGlobalFunctions_coeffScalar`.

The `A`-action is passed as data together with `hsm`, the equation saying that it is the action
through `Stacks.Blowup.blowUpCoeffScalar`; at the action obtained by restriction of scalars that
equation is `rfl`. -/
theorem moduleFinite_twistedSectionsComponent_reesGrading [IsNoetherianRing A] (d : ℤ)
    [Module A (unitSections (reesGrading I) d)]
    (hsm : ∀ (a : A) (t : unitSections (reesGrading I) d),
      a • t = blowUpCoeffScalar I a • t) :
    Module.Finite A (unitSections (reesGrading I) d) := by
  have : IsClosedImmersion (AlgebraicGeometry.Proj.map (reesPresentation I x hx)
      (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
        (surjective_reesPresentation I x hx hspan))) :=
    isClosedImmersion_blowUpSpecToProjSpace I x hx hspan
  have : IsLocallyNoetherian (blowUpSpec I) :=
    isLocallyNoetherian_of_isClosedImmersion (blowUpSpecToProjSpace I x hx hspan)
  have : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit (blowUpSpec I).ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit (blowUpSpec I)
  let : Module A (pushforwardUnitSections (polyGrading A m) (reesGrading I)
      (reesPresentation I x hx) (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
        (surjective_reesPresentation I x hx hspan)) d) :=
    coeffModule (polyGrading A m) _ A (Stacks.ProjectiveSpace.Cohomology.coeffScalar A m) d
  exact moduleFinite_unitSections_of_pushforward (polyGrading A m) (reesGrading I)
    (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
    (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A m) A
    (Stacks.ProjectiveSpace.Cohomology.coeffScalar A m) (blowUpCoeffScalar I) d
    (fun _ _ => rfl) hsm (projMapGlobalFunctions_coeffScalar x hx hspan)
    (Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistedSectionsComponent A m
      ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
        (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))
      (isCoherent_pushforward_of_isClosedImmersion (blowUpSpecToProjSpace I x hx hspan)
        (SheafOfModules.unit (blowUpSpec I).ringCatSheaf)) d)

include x hx hspan in
/-- **[Stacks, Tag 01YS] clause (5) for the Rees grading.** Let `A` be a Noetherian ring, `I ⊆ A`
an ideal with a finite generating family and `X` the blowup of `Spec A` in `I`. For every `k ∈ ℤ`
the graded `⨁ₙ Iⁿ`-module `⨁_{d ≥ k} Γ(X, 𝒪_X(d))` is a finite `⨁ₙ Iⁿ`-module.

Both hypotheses of
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation` are
now in hand: `hstep` is
`Stacks.Blowup.exists_forall_mem_degreeOneSections_reesGrading` read on the graded module by
`Stacks.ProjectiveSpace.Cohomology.subset_span_grading_of_forall_mem_degreeOneSections`, and
`hfg` is
`Stacks.AlgebraicGeometry.ProjTwistedSections.fg_span_twistedGlobalSectionsGrading_of_span_eq_top`
fed with `Stacks.Blowup.moduleFinite_twistedSectionsComponent_reesGrading` and
`Stacks.Blowup.reesGradingZeroEquiv_smul_of`.

The span forms stay inside this proof: writing `Submodule.span (reesAlgebra I) …` into a statement
sends `isDefEq` through the `Subalgebra` carrier's module paths and exhausts the budget. -/
theorem moduleFinite_truncation_reesGrading [IsNoetherianRing A]
    (D : TwistedGlobalSectionsModule (reesGrading I)
      (SheafOfModules.unit (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf)) (k : ℤ) :
    letI := D.moduleInst
    Module.Finite (reesAlgebra I)
      (TwistedGlobalSectionsModule.truncation (reesGrading I)
        (SheafOfModules.unit (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf) D k) := by
  classical
  let := D.moduleInst
  obtain ⟨B, hB⟩ := exists_forall_mem_degreeOneSections_reesGrading x hx hspan
  refine moduleFinite_twistedGlobalSectionsTruncation (reesGrading I)
    (SheafOfModules.unit (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf)
    D.smul_homogeneous k B (fun d => ?_)
    (Stacks.ProjectiveSpace.Cohomology.subset_span_grading_of_forall_mem_degreeOneSections
      (reesGrading I) (SheafOfModules.unit (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf)
      D B hB)
  let : Module A (unitSections (reesGrading I) d) :=
    coeffModule (reesGrading I) _ A (blowUpCoeffScalar I) d
  have hfin : Module.Finite A (unitSections (reesGrading I) d) :=
    moduleFinite_twistedSectionsComponent_reesGrading x hx hspan d (fun _ _ => rfl)
  exact fg_span_twistedGlobalSectionsGrading_of_moduleFinite (reesGrading I)
    (SheafOfModules.unit (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf) d A
    (fun a => ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I))
    (fun a s => reesGradingZeroEquiv_smul_of I
      (SheafOfModules.unit (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf) D a d s) hfin

end Blowup

end Stacks.Blowup

end
