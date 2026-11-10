module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceQuasiIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomTensorComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomTensorIso
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Trivial duality through a differential graded resolution

Let `R → A` be a map of commutative rings. Suppose given a differential graded `R`-algebra
`(E, d)` together with a quasi-isomorphism `E → A`, where `A` is viewed as a differential graded
algebra over `R` with zero differential concentrated in degree zero. Then `D(E, d)` and `D(A)`
are equivalent, the two triangles of the situation over `D(R)` commute, and the functor
`R Hom(A, -) : D(R) ⥤ D(A)` of Tag 0A70 is the composition of `R Hom(E, -) : D(R) ⥤ D(E, d)`
with the equivalence `- ⊗_E^𝐋 A : D(E, d) ⥤ D(A)`.

## Main definitions

* `Dualizing.DGAResolution`: the data of Situation 0BZB — the resolving differential graded
  algebra together with its quasi-isomorphism to `A`.
* `Dualizing.DGAResolution.derivedEquivalence`: the equivalence `D(E, d) ≌ D(A)`.
* `Dualizing.DGAResolution.derivedHomToResolution`: the functor `R Hom(E, -) : D(R) ⥤ D(E, d)`,
  built as the right adjoint of the forgetful functor.
* `Dualizing.DGAResolution.extensionFromBase`: the functor `- ⊗_R^𝐋 E : D(R) ⥤ D(E, d)`, built
  as the left adjoint of the forgetful functor.
* `Dualizing.resolvingBimodule`: `E` as a differential graded `(E, R)`-bimodule, whose underlying
  right module is the complex `E^•` of `R`-modules.
* `Dualizing.gradedDualBimodule`: `N = Hom^•_R(E^•, R)` as a differential graded
  `(R, E)`-bimodule.

## Main results

* `Dualizing.DGAResolution.restrictionTriangle`: the first diagram of Situation 0BZB.
* `Dualizing.DGAResolution.derivedExtension_comp_iso`: the second diagram of Situation 0BZB.
* `Dualizing.DGAResolution.derivedHom_comp_derivedEquivalence_iso`: **Tag 0BZC**.
* `Dualizing.derivedHomIsoGradedDualTensor`: **Tag 0BZD**, that `R Hom(E, -)` is derived
  tensoring with `N`.

## Implementation notes

The two functors `R Hom(E, -)` and `- ⊗_R^𝐋 E` out of `D(R)` are characterized here by their
adjunctions with the forgetful functor `D(E, d) ⥤ D(R)`, which is restriction of scalars along
`R → E`; this is the characterization the source uses, through Tag 09LT. Both triangles and
Tag 0BZC are therefore stated for an *arbitrary* functor with the relevant adjunction, so that
they do not depend on the model chosen for `R Hom(E, -)` or `- ⊗_R^𝐋 E`; a model of each is
constructed as well. Those models are transported from `D(A)` along the equivalence, so they
depend on the resolution; `Dualizing.derivedExtensionToDGA` in
`StacksFrontier/RingTheory/Dualizing/DifferentialGradedResolutionExtension.lean` is a construction
of `- ⊗_R^𝐋 E` that does not, and instantiating the second triangle at it gives the
unconditional `Dualizing.DGAResolution.derivedExtensionToDGA_comp_iso`.

The base ring, the algebra `A` and the differential graded modules all live in a single
universe, which is the encoding of the differential graded chapter in this tree (Tag 09JJ). The
derived categories of `ModuleCat R` and `ModuleCat A` are taken at the standard model. That is
forced by the declarations used — `Dualizing.derivedHom` and
`Dualizing.restrictScalarsDerived_adj_derivedHom` of
`StacksFrontier/RingTheory/Dualizing/TrivialDuality.lean` install
`HasDerivedCategory.standard` at file level — and not by Tag 0A70 or Tag 0GMT, both of which
hold at an arbitrary model: `Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom` and
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` take independent
`HasDerivedCategory` instances.

Tag 0BZD is the case `T = E` of the second assertion of Tag 0BZ0, which is
`DifferentialGraded.Bimodule.derivedTensorHomDualFunctorIso`;
`Dualizing.derivedHomIsoGradedDualTensor` invokes it rather than assuming it, and its two
hypotheses read here as `Dualizing.IsCompactBimodule` and `Dualizing.ComputesDerivedHom` of the
resolving bimodule, which are hypotheses (1) and (2) of Tag 0BZD itself, so the tag attribute
carries no caveat. For Tag 0BZD the two derived categories are the differential graded ones,
`D(R)` being the derived category of `R` concentrated in degree zero; it is the derived category
of `R`-modules by `DifferentialGradedModule.degreeZeroDerivedEquivalence`.

## References

* [Stacks Project, Tag 0BZB](https://stacks.math.columbia.edu/tag/0BZB), the situation.
* [Stacks Project, Tag 0BZC](https://stacks.math.columbia.edu/tag/0BZC), the lemma.
* [Stacks Project, Tag 0BZD](https://stacks.math.columbia.edu/tag/0BZD), trivial duality through
  the graded dual, and [Tag 0BZ0](https://stacks.math.columbia.edu/tag/0BZ0), of which it is the
  special case `T = E`.
* [Stacks Project, Tag 09S6](https://stacks.math.columbia.edu/tag/09S6) for the equivalence,
  [Tag 0A70](https://stacks.math.columbia.edu/tag/0A70) for `R Hom(A, -)` and
  [Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT) for derived extension of scalars.
-/

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Dualizing

add_to_stacks 0BZB "horizontal equivalence"
  DifferentialGraded.Bimodule.derivedExtensionEquivalence

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

/-- **Situation 0BZB.** A differential graded resolution of a commutative `R`-algebra `A`: a
differential graded `R`-algebra `E` together with a homomorphism to `A`, viewed as a
differential graded algebra with zero differential in degree zero, which is a quasi-isomorphism,
that is, an isomorphism on cohomology. -/
@[stacks 0BZB "resolution data"]
structure DGAResolution (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] where
  /-- The resolving differential graded `R`-algebra. -/
  E : DifferentialGradedAlgebra.{u, u} R
  /-- The homomorphism to `A` in degree zero. -/
  toTarget : E.Hom (DifferentialGradedAlgebra.degreeZero R A)
  /-- The homomorphism is a quasi-isomorphism. -/
  quasiIso : ∀ k : ℤ, Function.Bijective (toTarget.cohomologyMap k)

namespace DGAResolution

variable (S : DGAResolution R A)

/-- **The horizontal equivalence of Situation 0BZB.** Extension of scalars along the resolution,
followed by the identification of differential graded modules over `A` in degree zero with
complexes of `A`-modules, is an equivalence `D(E, d) ≌ D(A)`. -/
@[stacks 0BZB "ordinary derived equivalence"]
noncomputable def derivedEquivalence :
    derivedCategory' S.E ≌ DerivedCategory (ModuleCat.{u} A) :=
  (DifferentialGraded.Bimodule.derivedExtensionEquivalence S.toTarget S.quasiIso).trans
    degreeZeroDerivedEquivalence

/-- **The first diagram of Situation 0BZB commutes.** Passing from `D(A)` to `D(E, d)` through
the equivalence and then forgetting the `E`-action is restriction of scalars along `R → A`. -/
@[stacks 0BZB "restriction triangle"]
noncomputable def restrictionTriangle :
    S.derivedEquivalence.inverse ⋙ derivedForget S.E ≅
      (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory := by
  set D0 := DifferentialGradedAlgebra.degreeZero R A with hD0
  set φ := S.toTarget with hφ
  set U := derivedForget S.E with hU
  set T := (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory with hT
  set V := degreeZeroTotalFunctor R A with hV
  set QE := toHomotopyCategory S.E ⋙ (quasiIsomorphisms' S.E).Q with hQE
  set QZ := toHomotopyCategory D0 ⋙ (quasiIsomorphisms' D0).Q with hQZ
  have d₂ : QE ⋙ U ≅ forgetToCochainComplex S.E ⋙ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (toHomotopyCategory S.E) (derivedForgetFactorization S.E) ≪≫
      forgetHomotopyToDerivedCategoryIso S.E
  have d₁ : QZ ⋙ derivedRestriction φ ≅ restrictScalarsFunctor φ ⋙ QE :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (toHomotopyCategory D0) (derivedRestrictionFactorization φ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictScalarsHomotopyFunctorIso φ) _ ≪≫
      Functor.associator _ _ _
  have d₃ : (restrictScalarsFunctor φ ⋙ QE) ⋙ U ≅
      forgetToCochainComplex D0 ⋙ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (restrictScalarsFunctor φ) d₂ ≪≫
      (Functor.associator _ _ _).symm
  have hcomp : DerivedCategory.Q ⋙ (S.derivedEquivalence.inverse ⋙ U) ≅
      DerivedCategory.Q ⋙ T := by
    change DerivedCategory.Q ⋙ (degreeZeroDerivedEquivalence.inverse ⋙
      (derivedRestriction φ ⋙ U)) ≅ _
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (degreeZeroDerivedFactorization (R := R) (A := A)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft V ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight d₁ U ≪≫ d₃) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (degreeZeroTotalForgetIso (R := R) (A := A)) DerivedCategory.Q ≪≫
      (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategoryFactors.symm
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))
    (DerivedCategory.Q ⋙ (S.derivedEquivalence.inverse ⋙ U)) (DerivedCategory.Q ⋙ T)
    (S.derivedEquivalence.inverse ⋙ U) T hcomp

/-- Forgetting the `E`-action is the equivalence followed by restriction of scalars along
`R → A`. -/
noncomputable def forgetIso :
    derivedForget S.E ≅
      S.derivedEquivalence.functor ⋙
        (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight S.derivedEquivalence.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft S.derivedEquivalence.functor S.restrictionTriangle

/-! ### Derived Hom through the resolution -/

/-- The functor `R Hom(E, -) : D(R) ⥤ D(E, d)`, transported from `R Hom(A, -)` along the
equivalence. The adjunction below identifies it as derived Hom out of `E`. -/
noncomputable def derivedHomToResolution :
    DerivedCategory (ModuleCat.{u} R) ⥤ derivedCategory' S.E :=
  Dualizing.derivedHom.{u, u, u} (algebraMap R A) ⋙ S.derivedEquivalence.inverse

/-- The transported functor is right adjoint to forgetting the `E`-action, which is what
characterizes it as `R Hom(E, -)`. -/
noncomputable def derivedForget_adj_derivedHomToResolution :
    derivedForget S.E ⊣ S.derivedHomToResolution :=
  Adjunction.ofNatIsoLeft
    (S.derivedEquivalence.toAdjunction.comp
      (Classical.choice
        (Dualizing.restrictScalarsDerived_adj_derivedHom.{u, u, u} (algebraMap R A))))
    S.forgetIso.symm

/-- **Stacks 0BZC.** In Situation 0BZB the functor `R Hom(A, -) : D(R) ⥤ D(A)` is the
composition of `R Hom(E, -) : D(R) ⥤ D(E, d)` with the equivalence `- ⊗_E^𝐋 A : D(E, d) ⥤ D(A)`.

The functor `R Hom(E, -)` enters as an arbitrary right adjoint `G` of the forgetful functor
`D(E, d) ⥤ D(R)`, which is what Tag 09LT says derived Hom out of `E` is; so the statement is
independent of the model chosen for it. -/
@[stacks 0BZC]
noncomputable def derivedHom_comp_derivedEquivalence_iso
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ derivedCategory' S.E)
    (adjG : derivedForget S.E ⊣ G) :
    Dualizing.derivedHom.{u, u, u} (algebraMap R A) ≅ G ⋙ S.derivedEquivalence.functor :=
  (Adjunction.rightAdjointUniq
    (Adjunction.ofNatIsoLeft (S.derivedEquivalence.symm.toAdjunction.comp adjG)
      S.restrictionTriangle)
    (Classical.choice
      (Dualizing.restrictScalarsDerived_adj_derivedHom.{u, u, u} (algebraMap R A)))).symm

/-! ### Derived extension of scalars through the resolution -/

/-- Ordinary derived extension of scalars `- ⊗_R^𝐋 A : D(R) ⥤ D(A)`. -/
noncomputable abbrev ordinaryExtension :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R A)).functor

/-- Ordinary derived extension of scalars is left adjoint to restriction of scalars. -/
noncomputable def ordinaryExtension_adj :
    ordinaryExtension (R := R) (A := A) ⊣
      (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory := by
  let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R A)
  let c : DerivedCategory.Q ⋙ T.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := T.comparison
  have hD : T.functor.IsLeftDerivedFunctor c
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := T.isLeftDerived
  exact CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
    (algebraMap R A) T.functor c

/-- The functor `- ⊗_R^𝐋 E : D(R) ⥤ D(E, d)`, transported from `- ⊗_R^𝐋 A` along the
equivalence. The adjunction below identifies it as derived extension of scalars. -/
noncomputable def extensionFromBase :
    DerivedCategory (ModuleCat.{u} R) ⥤ derivedCategory' S.E :=
  ordinaryExtension (R := R) (A := A) ⋙ S.derivedEquivalence.inverse

/-- The transported functor is left adjoint to forgetting the `E`-action, which is what
characterizes it as derived extension of scalars along `R → E`. -/
noncomputable def extensionFromBase_adj :
    S.extensionFromBase ⊣ derivedForget S.E :=
  Adjunction.ofNatIsoRight
    ((ordinaryExtension_adj (R := R) (A := A)).comp
      S.derivedEquivalence.symm.toAdjunction)
    S.forgetIso.symm

/-- **The second diagram of Situation 0BZB commutes.** Derived extension of scalars from `D(R)`
to `D(E, d)` followed by the equivalence `- ⊗_E^𝐋 A` is derived extension of scalars
`- ⊗_R^𝐋 A : D(R) ⥤ D(A)`.

Derived extension of scalars to the resolution enters as an arbitrary left adjoint `F` of the
forgetful functor, so the statement is independent of the model chosen for it. That data is
discharged by `Dualizing.derivedExtensionToDGA` together with
`Dualizing.derivedExtensionToDGA_adj`, giving the unconditional
`Dualizing.DGAResolution.derivedExtensionToDGA_comp_iso`. -/
@[stacks 0BZB "extension triangle, for an arbitrary left adjoint F of the forgetful functor; \
its data F, adjF is discharged by derivedExtensionToDGA and derivedExtensionToDGA_adj, giving \
the unconditional DGAResolution.derivedExtensionToDGA_comp_iso"]
noncomputable def derivedExtension_comp_iso
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ derivedCategory' S.E)
    (adjF : F ⊣ derivedForget S.E) :
    F ⋙ S.derivedEquivalence.functor ≅ ordinaryExtension (R := R) (A := A) :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight (adjF.comp S.derivedEquivalence.toAdjunction)
      S.restrictionTriangle)
    (ordinaryExtension_adj (R := R) (A := A))

end DGAResolution

/-! ### Trivial duality through the graded dual of the resolution -/

section GradedDual

open DifferentialGraded

variable (E : DifferentialGradedAlgebra.{u, u} R)

/-- The base ring `R`, viewed as a differential graded `R`-algebra concentrated in degree zero
with zero differential; its derived category is the derived category of `R`-modules, by
`DifferentialGradedModule.degreeZeroDerivedEquivalence`. -/
noncomputable abbrev baseAlgebra (R : Type u) [CommRing R] :
    DifferentialGradedAlgebra.{u, u} R :=
  DifferentialGradedAlgebra.degreeZero R R

/-- A scalar is a homogeneous element of degree zero of a differential graded algebra. -/
private theorem algebraMap_mem_grading_zero (r : R) : algebraMap R E.A r ∈ E.grading 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (E.grading 0).smul_mem r (SetLike.one_mem_graded E.grading)

/-- The differential of a differential graded algebra annihilates the unit: the Leibniz rule in
degree zero gives `d 1 = d 1 + d 1`. -/
private theorem d_one_eq_zero : E.d 1 = 0 := by
  have h := E.leibniz 0 0 1 1 (SetLike.one_mem_graded E.grading)
    (SetLike.one_mem_graded E.grading)
  simp only [one_mul, mul_one, Int.negOnePow_zero, Units.val_one, one_smul] at h
  exact add_left_cancel (a := E.d 1) (by rw [add_zero]; exact h.symm)

/-- The structure homomorphism of differential graded algebras from the base ring, concentrated
in degree zero, to a differential graded `R`-algebra `E`: it sends a scalar `r` to `r · 1`. -/
def baseHom : (baseAlgebra R).Hom E where
  toAlgebraHom := Algebra.ofId R E.A
  map_grading n a ha := by
    rcases eq_or_ne n 0 with rfl | hn
    · exact algebraMap_mem_grading_zero E a
    · have ha0 : a = 0 := by
        simpa [DifferentialGradedAlgebra.degreeZeroGrading, hn] using ha
      simp [ha0]
  map_d a := by
    have hL : (baseAlgebra R).d a = 0 := rfl
    rw [hL, map_zero, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, map_smul,
      d_one_eq_zero E, smul_zero]

/-- `E` as a differential graded `(E, R)`-bimodule: the algebra `E` with its own multiplication
as the left action, read on the right over the base ring through the structure homomorphism. Its
underlying right module is the complex `E^•` of `R`-modules. -/
noncomputable def resolvingBimodule : Bimodule E (baseAlgebra R) :=
  Bimodule.restrictRight (baseHom E) (Bimodule.regular (DifferentialGradedAlgebra.idHom E))

/-- `N = Hom^•_R(E^•, R)`, the graded dual of `E^•` over the base ring, as a differential graded
`(R, E)`-bimodule: the left `R`-action is postcomposition with multiplication on `R` and the
right `E`-action is precomposition with multiplication on `E`. -/
noncomputable def gradedDualBimodule : Bimodule (baseAlgebra R) E :=
  Bimodule.homDualBimodule (resolvingBimodule E)

variable {E}

/-- Hypothesis (1) of [Stacks, Tag 0BZ0] for a differential graded `(B, C)`-bimodule `T`: the
class of `T` in `D(C, d)` is a compact object. -/
def IsCompactBimodule {B C : DifferentialGradedAlgebra.{u, u} R} (T : Bimodule B C) : Prop :=
  IsCompactObject.{u} ((toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q).obj T.rightModule)

/-- Hypothesis (2) of [Stacks, Tag 0BZ0] for a differential graded `(B, C)`-bimodule `T`: the
internal hom `Hom^•_C(T, C)` computes `R Hom(T, C)`, that is, the comparison map of the right
derived functor of Tag 09LI is invertible at the regular module `C`. -/
def ComputesDerivedHom {B C : DifferentialGradedAlgebra.{u, u} R} (T : Bimodule B C) : Prop :=
  IsIso ((derivedHomData B C T.rightModule T.leftAction).comparison.app
    ((toHomotopyCategory C).obj (regularModule C)))

variable (E)

/-- **Stacks 0BZD.** Let `(E, d)` be a differential graded algebra over a commutative ring `R` —
in Situation 0BZB, the algebra resolving the `R`-algebra `A` — and let
`N = Hom^•_R(E^•, R)` be the graded dual of `E^•` over `R`, a differential graded
`(R, E)`-bimodule. Assume that `E^•` is a compact object of `D(R)` and that `N` computes
`R Hom(E, R)`. Then `R Hom(E, -) : D(R) ⥤ D(E, d)` is isomorphic to `K ↦ K ⊗_R^𝐋 N`.

Here `D(R)` is the derived category of `R` viewed as a differential graded algebra concentrated
in degree zero, which is the derived category of `R`-modules by
`DifferentialGradedModule.degreeZeroDerivedEquivalence`; `R Hom(E, -)` is the right derived
functor of Tag 09LI for the bimodule `E`, and `- ⊗_R^𝐋 N` the left derived functor of Tag 09LS.

The source deduces this as the case `T = E` of the second assertion of Tag 0BZ0, which is
`DifferentialGraded.Bimodule.derivedTensorHomDualFunctorIso`; the two hypotheses above are
exactly its two hypotheses for `T = E`. -/
@[stacks 0BZD]
noncomputable def derivedHomIsoGradedDualTensor
    (hcompact : IsCompactBimodule (resolvingBimodule E))
    (hdual : ComputesDerivedHom (resolvingBimodule E)) :
    (derivedHomData E (baseAlgebra R) (resolvingBimodule E).rightModule
        (resolvingBimodule E).leftAction).functor ≅
      Bimodule.derivedTensorFunctor (gradedDualBimodule E) :=
  (Bimodule.derivedTensorHomDualFunctorIso (resolvingBimodule E) hcompact hdual).symm

end GradedDual

end Dualizing

end

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u

namespace Dualizing

/-! ### The second hypothesis of Tag 0BZ0 is not available for an arbitrary resolution

`Dualizing.derivedHomIsoGradedDualTensor` takes as its hypothesis `hdual` the assertion that the
graded dual `N = Hom^•_R(E^•, R)` computes `R Hom(E^•, R)`. That assertion is *false* for some
Situation-0BZB data, so it cannot be removed by proving it in general; a proof of it has to use a
property of the resolving algebra that Situation 0BZB does not supply.
-/

section GradedDualFailure

open DifferentialGradedAlgebra CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

variable {R : Type u} [CommRing R]

/-- A homomorphism of differential graded modules is determined by its underlying linear map, so
there is at most one when there is at most one linear map. -/
private theorem subsingleton_hom_of_subsingleton_toFun {C : DifferentialGradedAlgebra.{u, u} R}
    {X Y : DifferentialGradedModule.{u, u, u} C} (h : Subsingleton (X.M →ₗ[R] Y.M)) :
    Subsingleton (X ⟶ Y) :=
  ⟨fun _ _ => DifferentialGradedModule.Hom.ext (Subsingleton.elim _ _)⟩

/-- Morphisms of the homotopy category are classes of homomorphisms, so vanishing of the
homomorphisms gives vanishing of the classes. -/
private theorem subsingleton_homotopyCategory_hom {C : DifferentialGradedAlgebra.{u, u} R}
    {X Y : DifferentialGradedModule.{u, u, u} C} (h : Subsingleton (X ⟶ Y)) :
    Subsingleton ((toHomotopyCategory C).obj X ⟶ (toHomotopyCategory C).obj Y) := by
  constructor
  intro f g
  obtain ⟨f', rfl⟩ := (toHomotopyCategory C).map_surjective f
  obtain ⟨g', rfl⟩ := (toHomotopyCategory C).map_surjective g
  rw [Subsingleton.elim f' g']

/-- Transporting a vanishing morphism module along an isomorphism of the target. -/
private theorem subsingleton_hom_of_isoRight {D : Type*} [Category D] {X Y Z : D} (e : Y ≅ Z)
    (h : Subsingleton (X ⟶ Y)) : Subsingleton (X ⟶ Z) :=
  ⟨fun f g => by
    have : f ≫ e.inv = g ≫ e.inv := Subsingleton.elim _ _
    simpa using congrArg (fun u => u ≫ e.hom) this⟩

/-- Transporting a vanishing morphism module along an isomorphism of the source. -/
private theorem subsingleton_hom_of_isoLeft {D : Type*} [Category D] {X X' Z : D} (e : X ≅ X')
    (h : Subsingleton (X' ⟶ Z)) : Subsingleton (X ⟶ Z) :=
  ⟨fun f g => by
    have : e.inv ≫ f = e.inv ≫ g := Subsingleton.elim _ _
    simpa using congrArg (fun u => e.hom ≫ u) this⟩

/-- Shifting the source down by one is the adjoint of shifting the target up by one. -/
private theorem subsingleton_hom_shiftNegOne {D : Type*} [Category D] [HasShift D ℤ] (X Y : D)
    (h : Subsingleton (X ⟶ Y⟦(1 : ℤ)⟧)) : Subsingleton (X⟦(-1 : ℤ)⟧ ⟶ Y) :=
  (Equiv.subsingleton_congr
    ((CategoryTheory.shiftEquiv' D (-1 : ℤ) 1 (by ring)).toAdjunction.homEquiv X Y)).2 h

/-- If the comparison map of Tag 09LI is invertible at an object `X` of `K(C, d)`, then the
degree-`n` cohomology of `Hom^•_C(N, X)` is the module `Hom_{D(C,d)}(N, Q(X)[n])` of Tag 0CS5;
so a vanishing of the first gives a vanishing of the second. -/
private theorem subsingleton_ext_of_isIso_comparison
    (B C : DifferentialGradedAlgebra.{u, u} R) (N : DifferentialGradedModule.{u, u, u} C)
    (L : BimoduleStructure B C N) (n : ℤ) (X : HomotopyCategory C)
    (hcomp : IsIso ((derivedHomData B C N L).comparison.app X))
    (hsub : Subsingleton ((homShiftCohomologyFunctor B C N L n).obj X)) :
    Subsingleton ((quasiIsomorphisms' C).Q.obj ((toHomotopyCategory C).obj N) ⟶
      ((quasiIsomorphisms' C).Q.obj X)⟦n⟧) := by
  set D := derivedHomData B C N L with hD
  have h1 : IsIso ((extCohomologyComparisonUnit B C N L D n).app X) := by
    have : IsIso ((extCohomologyFunctor B n).map (D.comparison.app X)) := inferInstance
    change IsIso ((extCohomologyFunctor B n).map (D.comparison.app X) ≫ _)
    infer_instance
  have h2 : IsIso ((extComparisonUnit B C N L n).app X) := by
    have hfac := NatTrans.congr_app (extIso_fac B C N L D n) X
    rw [← hfac, NatTrans.comp_app]
    have : IsIso ((Functor.whiskerLeft (quasiIsomorphisms' C).Q
        (extIso B C N L D n).hom).app X) := by
      change IsIso ((extIso B C N L D n).hom.app ((quasiIsomorphisms' C).Q.obj X))
      infer_instance
    infer_instance
  exact (Equiv.subsingleton_congr
    (asIso ((extComparisonUnit B C N L n).app X)).toLinearEquiv.toEquiv).1 hsub

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **If the graded dual of `A` computes derived Hom, then `A` has no derived dual at all.**
Take for the resolving algebra of Situation 0BZB the target `A` itself, placed in degree zero,
and suppose that the only `R`-linear map `A → R` is the zero one. Then `Hom^•_R(A, R)` has no
nonzero element in any degree, so the hypothesis `hdual` of
`Dualizing.derivedHomIsoGradedDualTensor` forces every module
`Hom_{D(R)}(A, R[n]) = Ext^n_R(A, R)` to be trivial, in every degree `n` at once.

Here `D(R)` is the derived category of `R` as a differential graded algebra in degree zero, and
the identification of the cohomology of derived Hom with these morphism modules is Tag 0CS5,
`DifferentialGradedModule.extLinearEquiv`. -/
theorem subsingleton_ext_of_computesDerivedHom_degreeZero
    (hzero : Subsingleton (A →ₗ[R] R))
    (hdual : ComputesDerivedHom
      (resolvingBimodule (DifferentialGradedAlgebra.degreeZero R A))) (n : ℤ) :
    Subsingleton
      ((quasiIsomorphisms' (baseAlgebra R)).Q.obj ((toHomotopyCategory (baseAlgebra R)).obj
          (resolvingBimodule (DifferentialGradedAlgebra.degreeZero R A)).rightModule) ⟶
        ((quasiIsomorphisms' (baseAlgebra R)).Q.obj
          ((toHomotopyCategory (baseAlgebra R)).obj (regularModule (baseAlgebra R))))⟦n⟧) := by
  set C := baseAlgebra R with hC
  set T := resolvingBimodule (DifferentialGradedAlgebra.degreeZero R A) with hT
  have h1 : Subsingleton ((toHomotopyCategory C).obj T.rightModule ⟶
      ((toHomotopyCategory C).obj (regularModule C))⟦n⟧) :=
    subsingleton_hom_of_isoRight (quotientShiftIso (regularModule C) n)
      (subsingleton_homotopyCategory_hom (subsingleton_hom_of_subsingleton_toFun hzero))
  refine subsingleton_ext_of_isIso_comparison _ C T.rightModule T.leftAction n _ hdual ?_
  exact (Equiv.subsingleton_congr
      ((homShiftCohomologyUliftIso (DifferentialGradedAlgebra.degreeZero R A) C
        T.rightModule T.leftAction n).app
        ((toHomotopyCategory C).obj (regularModule C))).toLinearEquiv.toEquiv).2
    ((Equiv.subsingleton_congr Equiv.ulift).2 h1)

/-- **The tautological differential graded resolution.** Every commutative `R`-algebra `A` is a
resolution of itself in the sense of Situation 0BZB: take for the resolving differential graded
algebra `A` placed in degree zero with zero differential, and for the resolution map the
identity, which is an isomorphism on cohomology because it is an isomorphism. -/
noncomputable def tautologicalResolution (R : Type u) [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] : DGAResolution R A where
  E := DifferentialGradedAlgebra.degreeZero R A
  toTarget := DifferentialGradedAlgebra.idHom _
  quasiIso k := by
    have h : (DifferentialGradedAlgebra.idHom
        (DifferentialGradedAlgebra.degreeZero R A)).cohomologyMap k = id := by
      funext x
      induction x using Quotient.inductionOn with
      | h a => rfl
    rw [h]
    exact Function.bijective_id

end GradedDualFailure
/-! #### A Situation-0BZB resolution whose graded dual does not compute derived Hom -/

section Witness

open DifferentialGradedAlgebra CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-- The base ring `ℤ`, as a differential graded algebra in degree zero. -/
private noncomputable abbrev intBase : DifferentialGradedAlgebra.{0, 0} ℤ := baseAlgebra ℤ

/-- The resolving algebra of the tautological resolution of `ZMod 2` over `ℤ`. -/
private noncomputable abbrev zmodTwoDGA : DifferentialGradedAlgebra.{0, 0} ℤ :=
  degreeZero ℤ (ZMod 2)

/-- `ZMod 2` in degree zero, as a differential graded module over `ℤ` in degree zero; this is
the complex `E^•` of the tautological resolution. -/
private noncomputable abbrev zmodTwoModule : DifferentialGradedModule.{0, 0, 0} intBase :=
  (resolvingBimodule zmodTwoDGA).rightModule

/-- Multiplication by two on the regular module of `ℤ` in degree zero. -/
private noncomputable def multByTwo : regularModule intBase ⟶ regularModule intBase :=
  (2 : ℤ) • 𝟙 (regularModule intBase)

private theorem multByTwo_toFun (x : ℤ) : multByTwo.toFun x = 2 * x := by
  rw [multByTwo, Hom.hom_zsmul_toFun]
  change (2 : ℤ) • x = 2 * x
  rw [smul_eq_mul]

/-- The Koszul complex `ℤ --2--> ℤ` of the element `2`, as the cone of multiplication by two. -/
private noncomputable abbrev koszulCone : DifferentialGradedModule.{0, 0, 0} intBase :=
  coneObject multByTwo

private theorem koszulCone_d (x : ℤ × ℤ) : koszulCone.d x = (2 * x.2, 0) := by
  rw [show koszulCone.d x = coneD multByTwo x from rfl, coneD_apply]
  change ((0 : ℤ) + multByTwo.toFun x.2, -(0 : ℤ)) = _
  rw [multByTwo_toFun, zero_add, neg_zero]

private theorem mem_koszulCone_grading (n : ℤ) (x : ℤ × ℤ) :
    x ∈ koszulCone.grading n ↔
      x.1 ∈ degreeZeroGrading ℤ ℤ n ∧ x.2 ∈ degreeZeroGrading ℤ ℤ (n + 1) :=
  Submodule.mem_prod

/-- In a nonzero degree, the degree-zero grading of an algebra over `ℤ` has only the zero
element. -/
private theorem eq_zero_of_mem_degreeZeroGrading {A : Type} [Ring A] [Algebra ℤ A] {n : ℤ}
    (hn : n ≠ 0) {x : A} (h : x ∈ degreeZeroGrading ℤ A n) : x = 0 := by
  rwa [degreeZeroGrading_eq_bot ℤ A hn, Submodule.mem_bot] at h

/-- The reduction map from the regular module of `ℤ` onto `ZMod 2`. -/
private noncomputable def reduceModTwo : regularModule intBase ⟶ zmodTwoModule where
  toFun :=
    { toFun := fun x => ((x : ℤ) : ZMod 2)
      map_add' := fun x y => by push_cast; rfl
      map_smul' := fun r x => by
        change (((r * x : ℤ)) : ZMod 2) = r • ((x : ℤ) : ZMod 2)
        rw [zsmul_eq_mul]
        push_cast
        rfl }
  map_smul x a := by
    change (((x * a : ℤ)) : ZMod 2) = ((x : ℤ) : ZMod 2) * algebraMap ℤ (ZMod 2) a
    rw [eq_intCast (algebraMap ℤ (ZMod 2)) a]
    push_cast
    rfl
  map_grading n x hx := by
    rcases eq_or_ne n 0 with rfl | hn
    · change ((x : ℤ) : ZMod 2) ∈ degreeZeroGrading ℤ (ZMod 2) 0
      rw [degreeZeroGrading_zero]
      exact Submodule.mem_top
    · change ((x : ℤ) : ZMod 2) ∈ degreeZeroGrading ℤ (ZMod 2) n
      rw [eq_zero_of_mem_degreeZeroGrading hn (show x ∈ degreeZeroGrading ℤ ℤ n from hx),
        Int.cast_zero]
      exact Submodule.zero_mem _
  map_d := by
    refine LinearMap.ext fun x => ?_
    change (((0 : ℤ)) : ZMod 2) = 0
    simp

private theorem reduceModTwo_toFun (x : ℤ) : reduceModTwo.toFun x = ((x : ℤ) : ZMod 2) := rfl

/-- The augmentation of the Koszul complex: the degree-zero term read in `ZMod 2`. -/
private noncomputable def koszulAug : koszulCone ⟶ zmodTwoModule where
  toFun := reduceModTwo.toFun ∘ₗ LinearMap.fst ℤ ℤ ℤ
  map_smul x a := reduceModTwo.map_smul x.1 a
  map_grading n x hx := reduceModTwo.map_grading n x.1 ((mem_koszulCone_grading n x).1 hx).1
  map_d := by
    ext x
    change (((koszulCone.d x).1 : ℤ) : ZMod 2) = 0
    rw [koszulCone_d]
    push_cast
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem koszulAug_toFun (x : ℤ × ℤ) : koszulAug.toFun x = ((x.1 : ℤ) : ZMod 2) := rfl

private theorem zmodTwoModule_d : zmodTwoModule.d = 0 := rfl

/-- The augmentation is a quasi-isomorphism: the Koszul complex `ℤ --2--> ℤ` has cohomology
`ZMod 2` in degree zero and nothing elsewhere. -/
private theorem isQuasiIsomorphism_koszulAug : IsQuasiIsomorphism koszulAug := by
  intro n
  constructor
  · intro y hy _
    rcases eq_or_ne n 0 with rfl | hn
    · obtain ⟨m, hm⟩ := ZMod.intCast_surjective (n := 2) y
      refine ⟨(m, 0), ?_, ?_, 0, Submodule.zero_mem _, ?_⟩
      · exact (mem_koszulCone_grading 0 (m, 0)).2
          ⟨by rw [degreeZeroGrading_zero]; trivial, Submodule.zero_mem _⟩
      · rw [koszulCone_d]
        change ((2 * 0 : ℤ), (0 : ℤ)) = ((0 : ℤ), (0 : ℤ))
        rw [mul_zero]
      · change (0 : zmodTwoModule.M) = y - koszulAug.toFun (m, 0)
        rw [show koszulAug.toFun (m, 0) = y from hm, sub_self]
    · refine ⟨0, Submodule.zero_mem _, map_zero _, 0, Submodule.zero_mem _, ?_⟩
      change (0 : zmodTwoModule.M) = y - koszulAug.toFun 0
      rw [eq_zero_of_mem_degreeZeroGrading (A := ZMod 2) hn hy, map_zero]
      exact (sub_zero _).symm
  · rintro x hx hdx ⟨z, -, hz⟩
    rw [zmodTwoModule_d] at hz
    have hx2 : (x.2 : ℤ) = 0 := by
      rw [koszulCone_d] at hdx
      have h2 : (2 : ℤ) * (x.2 : ℤ) = 0 := congrArg Prod.fst hdx
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
    rcases eq_or_ne n 0 with rfl | hn
    · have hdvd : (2 : ℤ) ∣ x.1 := by
        have hcast : ((x.1 : ℤ) : ZMod 2) = 0 := hz.symm
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd x.1 2).1 hcast
      obtain ⟨m, hm⟩ := hdvd
      refine ⟨(0, m), ?_, ?_⟩
      · refine (mem_koszulCone_grading (0 - 1) (0, m)).2 ⟨Submodule.zero_mem _, ?_⟩
        norm_num
        rw [degreeZeroGrading_zero]
        trivial
      · rw [koszulCone_d]
        refine Prod.ext ?_ ?_
        · simpa using hm.symm
        · simpa using hx2.symm
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero]
      exact (Prod.ext (eq_zero_of_mem_degreeZeroGrading hn ((mem_koszulCone_grading n x).1 hx).1)
        hx2).symm

private theorem reduceModTwo_ne_zero : reduceModTwo ≠ 0 := by
  intro h
  have h1 : reduceModTwo.toFun 1 = (0 : zmodTwoModule.M) := by rw [h]; rfl
  rw [reduceModTwo_toFun, Int.cast_one] at h1
  have h2 : (1 : ZMod 2) = 0 := h1
  exact absurd h2 (by decide)

/-- Every homomorphism from the regular module to `ZMod 2` kills multiplication by two, because
the target is killed by two. -/
private theorem multByTwo_comp_eq_zero (k : regularModule intBase ⟶ zmodTwoModule) :
    multByTwo ≫ k = 0 := by
  refine Hom.ext (LinearMap.ext fun x => ?_)
  change k.toFun (multByTwo.toFun x) = 0
  rw [multByTwo_toFun, two_mul, map_add]
  exact (by decide : ∀ y : ZMod 2, y + y = 0) _

/-- Both differentials vanish, so homotopic homomorphisms from the regular module to `ZMod 2`
are equal. -/
private theorem eq_of_homotopic_reg {f g : regularModule intBase ⟶ zmodTwoModule}
    (h : Homotopic f g) : f = g := by
  obtain ⟨H⟩ := h
  refine Hom.ext (LinearMap.ext fun x => ?_)
  have hx := H.homotopy_eq x
  change f.toFun x - g.toFun x =
    zmodTwoModule.d _ + H.toLinearMap ((regularModule intBase).d x) at hx
  rw [show zmodTwoModule.d = 0 from rfl, show (regularModule intBase).d = 0 from rfl] at hx
  simp only [LinearMap.zero_apply, map_zero, add_zero] at hx
  exact sub_eq_zero.1 hx

/-- The regular module is orthogonal on the left to the acyclic objects, so the localization is
bijective on morphisms out of it. -/
private theorem leftOrthogonal_regularModule_int : (acyclic' intBase).leftOrthogonal
    ((toHomotopyCategory intBase).obj (regularModule intBase)) := by
  intro Y f hY
  have e := (CategoryTheory.shiftFunctorZero (HomotopyCategory intBase) ℤ).app
    ((toHomotopyCategory intBase).obj (regularModule intBase))
  have h0 : e.hom ≫ f = 0 := isZero_hom_shift_regularModule intBase 0 hY _
  simpa using congrArg (e.inv ≫ ·) h0

/-- The cone triangle of multiplication by two is distinguished in `K(ℤ, d)`. -/
private theorem mem_distTriang_koszulConeTriangle :
    mappingConeTriangle multByTwo ∈ distTriang (HomotopyCategory intBase) := by
  obtain ⟨L', M', f', g', hfg, b, hb, e, -, -⟩ :=
    exists_associatedTriangle_iso_mappingConeTriangle multByTwo
  exact Pretriangulated.isomorphic_distinguished _
    (associatedTriangle_mem_distTriang intBase f' g' hfg) _ e.symm

/-- `ZMod 2` carries no nonzero `ℤ`-linear functional, since `ℤ` has no two-torsion. -/
private theorem subsingleton_zmodTwo_dual : Subsingleton (ZMod 2 →ₗ[ℤ] ℤ) := by
  have key : ∀ (h : ZMod 2 →ₗ[ℤ] ℤ) (x : ZMod 2), h x = 0 := by
    intro h x
    have h2 : (2 : ℤ) • x = 0 := by
      rw [zsmul_eq_mul]
      change ((2 : ℤ) : ZMod 2) * x = 0
      rw [show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul]
    have h3 := congrArg h h2
    rw [map_smul, map_zero, smul_eq_mul] at h3
    omega
  exact ⟨fun f g => LinearMap.ext fun x => by rw [key f x, key g x]⟩

/-- **The second assertion of Tag 0BZ0 fails for a Situation-0BZB resolution.** Take `R = ℤ`,
`A = ZMod 2` and for the resolving differential graded algebra the tautological choice
`Dualizing.tautologicalResolution`: the target `ZMod 2` itself, in degree zero, with the
identity as the resolution map. Then the graded dual `N = Hom^•_R(E^•, R)` does *not* compute
`R Hom(E^•, R)`.

Consequently the hypothesis `hdual` of `Dualizing.derivedHomIsoGradedDualTensor` is a genuine
restriction on the resolution and not a property of Situation 0BZB: there is no way to obtain it
for an arbitrary resolving algebra, and it cannot be proved in that
generality.

The obstruction is visible on cohomology. Here `E^• = ZMod 2` and `R = ℤ`, and the only
`ℤ`-linear map `ZMod 2 → ℤ` is zero, so the graded dual has no nonzero element in any degree;
whereas `R Hom_ℤ(ZMod 2, ℤ)` is `ZMod 2` placed in degree one, as the resolution `ℤ --2--> ℤ`
shows. Note that `ZMod 2` is as finite over `ℤ` as a nonfree module can be — that same
resolution makes it perfect — so finiteness of `A` is not what is missing.

What a proof of Tag 0BZE has to do instead is *choose* the resolving algebra: a Tate resolution,
bounded above and free over `R` in each degree. Its underlying complex `E^•` then has property
(P) over `DifferentialGradedAlgebra.degreeZero R R`, and property (P) is exactly what Tag 0BYW,
`DifferentialGradedModule.DerivedHomData.isIso_comparison_of_propertyP`
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLeftOrthogonal.lean`), turns into the
invertibility of the comparison map that `hdual` asserts. -/
theorem not_computesDerivedHom_tautologicalResolution :
    ¬ ComputesDerivedHom (resolvingBimodule (tautologicalResolution ℤ (ZMod 2)).E) := by
  intro hdual0
  have hdual : ComputesDerivedHom (resolvingBimodule zmodTwoDGA) := hdual0
  have hvan := subsingleton_ext_of_computesDerivedHom_degreeZero subsingleton_zmodTwo_dual hdual
  have hqiso : IsIso ((quasiIsomorphisms' intBase).Q.map
      ((toHomotopyCategory intBase).map koszulAug)) :=
    isIso_q_map_toHomotopyCategory_map koszulAug
      (quasiIso_of_isQuasiIsomorphism koszulAug isQuasiIsomorphism_koszulAug)
  have hP1 : Subsingleton
      ((quasiIsomorphisms' intBase).Q.obj ((toHomotopyCategory intBase).obj koszulCone) ⟶
        ((quasiIsomorphisms' intBase).Q.obj
          ((toHomotopyCategory intBase).obj (regularModule intBase)))⟦(1 : ℤ)⟧) :=
    subsingleton_hom_of_isoLeft
      (asIso ((quasiIsomorphisms' intBase).Q.map
        ((toHomotopyCategory intBase).map koszulAug))) (hvan 1)
  have hP2 := subsingleton_hom_shiftNegOne _ _ hP1
  have hT := ((quasiIsomorphisms' intBase).Q).map_distinguished _
    mem_distTriang_koszulConeTriangle
  set T := ((quasiIsomorphisms' intBase).Q).mapTriangle.obj (mappingConeTriangle multByTwo)
    with hTdef
  obtain ⟨u, hu⟩ := Triangle.yoneda_exact₂ T.invRotate (inv_rot_of_distTriang _ hT)
    (𝟙 T.obj₁) (hP2.elim _ _)
  have hu2 : 𝟙 ((quasiIsomorphisms' intBase).Q.obj
        ((toHomotopyCategory intBase).obj (regularModule intBase))) =
      (quasiIsomorphisms' intBase).Q.map ((toHomotopyCategory intBase).map multByTwo) ≫
        (u : (quasiIsomorphisms' intBase).Q.obj
            ((toHomotopyCategory intBase).obj (regularModule intBase)) ⟶
          (quasiIsomorphisms' intBase).Q.obj
            ((toHomotopyCategory intBase).obj (regularModule intBase))) := hu
  obtain ⟨kK, hkK⟩ := (bijective_q_map_of_leftOrthogonal leftOrthogonal_regularModule_int
    ((toHomotopyCategory intBase).obj zmodTwoModule)).2
      ((u : (quasiIsomorphisms' intBase).Q.obj
            ((toHomotopyCategory intBase).obj (regularModule intBase)) ⟶
          (quasiIsomorphisms' intBase).Q.obj
            ((toHomotopyCategory intBase).obj (regularModule intBase))) ≫
        (quasiIsomorphisms' intBase).Q.map ((toHomotopyCategory intBase).map reduceModTwo))
  obtain ⟨k, rfl⟩ := (toHomotopyCategory intBase).map_surjective kK
  have hQeq : (quasiIsomorphisms' intBase).Q.map
        ((toHomotopyCategory intBase).map reduceModTwo) =
      (quasiIsomorphisms' intBase).Q.map ((toHomotopyCategory intBase).map
        (0 : regularModule intBase ⟶ zmodTwoModule)) := by
    have h1 : (quasiIsomorphisms' intBase).Q.map
          ((toHomotopyCategory intBase).map reduceModTwo) =
        (quasiIsomorphisms' intBase).Q.map ((toHomotopyCategory intBase).map multByTwo) ≫
          ((u : (quasiIsomorphisms' intBase).Q.obj
                ((toHomotopyCategory intBase).obj (regularModule intBase)) ⟶
              (quasiIsomorphisms' intBase).Q.obj
                ((toHomotopyCategory intBase).obj (regularModule intBase))) ≫
            (quasiIsomorphisms' intBase).Q.map
              ((toHomotopyCategory intBase).map reduceModTwo)) := by
      calc (quasiIsomorphisms' intBase).Q.map ((toHomotopyCategory intBase).map reduceModTwo)
          = 𝟙 _ ≫ (quasiIsomorphisms' intBase).Q.map
              ((toHomotopyCategory intBase).map reduceModTwo) := (Category.id_comp _).symm
        _ = ((quasiIsomorphisms' intBase).Q.map
              ((toHomotopyCategory intBase).map multByTwo) ≫ u) ≫
            (quasiIsomorphisms' intBase).Q.map
              ((toHomotopyCategory intBase).map reduceModTwo) := by
            rw [hu2]
            rfl
        _ = _ := Category.assoc _ _ _
    rw [h1, ← hkK, ← Functor.map_comp, ← Functor.map_comp, multByTwo_comp_eq_zero k]
  have key : (toHomotopyCategory intBase).map reduceModTwo =
      (toHomotopyCategory intBase).map (0 : regularModule intBase ⟶ zmodTwoModule) :=
    (bijective_q_map_of_leftOrthogonal leftOrthogonal_regularModule_int _).1 hQeq
  exact reduceModTwo_ne_zero (eq_of_homotopic_reg
    ((CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel intBase) reduceModTwo 0).1 key))

/-- **There is a Situation-0BZB resolution for which the hypothesis `hdual` of
`Dualizing.derivedHomIsoGradedDualTensor` is false.** The witness is
`Dualizing.tautologicalResolution` for the algebra `ZMod 2` over `ℤ`. -/
theorem exists_dgaResolution_not_computesDerivedHom :
    ∃ S : DGAResolution ℤ (ZMod 2), ¬ ComputesDerivedHom (resolvingBimodule S.E) :=
  ⟨tautologicalResolution ℤ (ZMod 2), not_computesDerivedHom_tautologicalResolution⟩

end Witness

end Dualizing

end
