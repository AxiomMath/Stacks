module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientKernelLift
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistDownFactorMultiplication
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.GeometricFactorBaseScalar

/-!
# The degree-zero scalar of the `c`-step law is the base scalar of [Stacks, Tag 0GA8]

Let `A` be a commutative ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`. The `c`-step law of `BitUniformityIII/TwistDownFactorMultiplication.lean`,
`Stacks.Blowup.twistDownFactorMap_comp_twistScalarFactorMap_reesDegOnePow`, exhibits twisting down
`c` steps followed by multiplication by `(b⁽¹⁾)^c` as multiplication by the **degree-zero
homogeneous** scalar `Stacks.Blowup.reesConst I (b^c)` inside the geometric factor
`N ↦ 𝒪_X(q) ⊗ p^*Ñ`. [Stacks, Tag 0GA8] on this blowup,
`Stacks.LocalCohomology.UniformityIII.smul_twistedPullbackSupported_eq_zero`, kills multiplication
by `b^c ∈ I^c` in the **`A`-linear** structure `Stacks.Blowup.blowUpModulesLinear`. The two are the
same morphism; this file proves it.

## The three steps

* **A base scalar is a global function.** For a scheme `X` over `Spec(A)` the central endomorphism
  `AlgebraicGeometry.baseScalar` of `A` on `𝒪_X`-modules is
  `Stacks.RegularSequence.globalSmulCenter` at the global function `a` pulls back to: on sections
  over every open both multiply by the image of `a` in the functions there, which is what
  `AlgebraicGeometry.baseRingToSections` names. No file of this tree related the two before, and
  the equation is the one the second bridge recorded in
  `BitUniformityIII/BlowupTwistDownCohomology.lean` asks for. It is stated here for an arbitrary
  `A`-scheme, since nothing about the blowup enters.
* **The twist index is an integer.** `twistScalarSheafMap_reesConst_eq_globalSmulCenter` of
  `BitUniformityIII/AmbientKernelLift.lean` already rewrites the degree-zero scalar as a global
  function, but only for a *natural* twist, because its right-hand side is written at the
  ℕ-indexed `Stacks.LocalCohomology.UniformityIII.blowupTwist`. The twists of
  [Stacks, Tag 0GAA] clause (3) are integers — the source twist `q - c` of the dotted arrow is
  negative for small `q` — so the statement is repeated here at
  `Stacks.Blowup.blowUpTwist`, whose index is an integer. Its input
  `…ProjTwistedSections.twistScalarSheafMap_zero_eq_globalSmulCenter` is already stated for
  every integer, so nothing but the spelling changes.
* **The tensor slot.** The degree-zero scalar enters the geometric factor through
  `Stacks.Blowup.twistScalarFactorMap`, which is
  `…TopDegreeBaseChange.geometricFactorFormulaMap` at a morphism of the **fixed, left** factor
  `𝒪_X(q)`, while `AlgebraicGeometry.tensorLeft_linear` is the linearity of the **variable,
  right** one. `…TopDegreeBaseChange.geometricFactorFormulaMap_smul_id_app` of
  `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/GeometricFactorBaseScalar.lean` is the
  missing half, and it is proved there for an arbitrary `A`-scheme and an arbitrary fixed factor.

## Main results

* `AlgebraicGeometry.globalSmulCenter_appTop_eq_baseScalar` and
  `…globalSmulCenter_appTop_app_eq_smul_id`: **the base scalar of an `A`-scheme is multiplication
  by the global function the scalar pulls back to**, as an element of the centre and at a fixed
  module.
* `Stacks.LocalCohomology.UniformityIII.twistScalarSheafMap_reesConst_eq_globalSmulCenter_int`:
  the degree-zero scalar on `𝒪_X(q)` is a global function, for **every integer** `q`.
* `Stacks.LocalCohomology.UniformityIII.twistScalarFactorMap_reesConst_app_eq_smul_id`:
  **the identification the `c`-step law and [Stacks, Tag 0GA8] meet in** — the degree-zero scalar
  `reesConst I b` acting inside `N ↦ 𝒪_X(q) ⊗ p^*Ñ` is `b • 𝟙`, for every integer `q`.

## References

* [Stacks Project, Tag 0GA8](https://stacks.math.columbia.edu/tag/0GA8)
* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistedDegree_zero)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange (geometricFactorFormulaMap_congr
  geometricFactorFormulaMap_smul_id_app)
open Stacks.RegularSequence (globalSmulCenter)

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] (X : Over (Spec (CommRingCat.of A)))

/-- **The base scalar of an `A`-scheme is multiplication by the global function the scalar pulls
back to.** `AlgebraicGeometry.baseScalar` multiplies the sections over an open `U` by
`AlgebraicGeometry.baseRingToSections`, which is by construction the restriction to `U` of the
image of the scalar under `Γ(Spec A, ⊤) ⟶ Γ(X, ⊤)`; and that restriction is what
`Stacks.RegularSequence.globalSmulCenter` multiplies by. So the two central endomorphisms have
the same value on the sections of every module over every open. -/
theorem globalSmulCenter_appTop_eq_baseScalar (a : A) :
    globalSmulCenter X.left
        (X.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) =
      baseScalar A X a := by
  refine CatCenter.ext _ _ fun M => ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- **Multiplication by a global function pulled back from the base is the base scalar**, at a
fixed sheaf of modules and in the form the `A`-linear structure
`AlgebraicGeometry.modulesLinear` states its scalars in. This is
`globalSmulCenter_appTop_eq_baseScalar` read through `AlgebraicGeometry.baseRingToCenter`, whose
scalar action on morphisms is precomposition with the value of `baseScalar`. -/
theorem globalSmulCenter_appTop_app_eq_smul_id (a : A) (M : X.left.Modules) :
    letI := modulesLinear A X
    (globalSmulCenter X.left
        (X.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))).app M =
      a • 𝟙 M := by
  let := modulesLinear A X
  rw [globalSmulCenter_appTop_eq_baseScalar]
  rfl

end AlgebraicGeometry

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **Multiplication by `b ∈ A` on `𝒪_X(q)` is multiplication by the global function `b` pulls
back to, for every integer twist `q`.** This is
`Stacks.LocalCohomology.UniformityIII.twistScalarSheafMap_reesConst_eq_globalSmulCenter` with the
twist no longer restricted to the natural numbers: its input
`…ProjTwistedSections.twistScalarSheafMap_zero_eq_globalSmulCenter` holds for every integer, and
the only obstacle was that `Stacks.LocalCohomology.UniformityIII.blowupTwist` is ℕ-indexed, so the
statement is made at the integer-indexed `Stacks.Blowup.blowUpTwist` instead. -/
theorem twistScalarSheafMap_reesConst_eq_globalSmulCenter_int (q : ℤ) (b : A) :
    twistScalarSheafMap (Stacks.Blowup.reesGrading I) 0 q q (twistedDegree_zero q)
        ⟨(Stacks.Blowup.reesConst I b : reesAlgebra I),
          SetLike.algebraMap_mem_graded (Stacks.Blowup.reesGrading I) b⟩ =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app
        (Stacks.Blowup.blowUpTwist I q) :=
  Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_zero_eq_globalSmulCenter
    (Stacks.Blowup.reesGrading I) q _ (pullbackCoeff I b)
    (fun x => val_appTop_toSpec I b x)

/-- **The global function that `b : A` pulls back to acts as the scalar `b`** on every sheaf of
modules on the blowup, for the `A`-linear structure `Stacks.Blowup.blowUpModulesLinear`. This is
`AlgebraicGeometry.globalSmulCenter_appTop_app_eq_smul_id` at the blowup read as a scheme over
`Spec(A)`; `Stacks.LocalCohomology.UniformityIII.pullbackCoeff` is the pullback of `b` by
definition. -/
theorem globalSmulCenter_pullbackCoeff_app_eq_smul_id (b : A) (M : (blowupScheme I).Modules) :
    letI := Stacks.Blowup.blowUpModulesLinear I
    (globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app M = b • 𝟙 M :=
  globalSmulCenter_appTop_app_eq_smul_id (Stacks.Blowup.blowUpOver I) b M

/-- **The degree-zero homogeneous scalar of the `c`-step law is the scalar of [Stacks, Tag 0GA8],
inside the geometric factor and at every integer twist.** Multiplication by `reesConst I b` as a
natural transformation of `N ↦ 𝒪_X(q) ⊗ p^*Ñ` is `b • 𝟙`.

The scalar is first rewritten as a global function on the twisting sheaf
(`twistScalarSheafMap_reesConst_eq_globalSmulCenter_int`), then as the base scalar
(`globalSmulCenter_pullbackCoeff_app_eq_smul_id`); tensoring into the fixed factor depends on the
sheaf morphism alone
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaMap_congr`), and a base
scalar on that fixed factor is the base scalar of the tensor product
(`…geometricFactorFormulaMap_smul_id_app`). -/
theorem twistScalarFactorMap_reesConst_app_eq_smul_id (q : ℤ) (b : A) (N : ModuleCat.{u} A) :
    letI := Stacks.Blowup.blowUpModulesLinear I
    (Stacks.Blowup.twistScalarFactorMap I 0 q q (twistedDegree_zero q)
        ⟨(Stacks.Blowup.reesConst I b : reesAlgebra I),
          SetLike.algebraMap_mem_graded (Stacks.Blowup.reesGrading I) b⟩).app N =
      b • 𝟙 ((Stacks.Blowup.twistedGeometricFactor I q).obj N) :=
  let := Stacks.Blowup.blowUpModulesLinear I
  (NatTrans.congr_app
        (geometricFactorFormulaMap_congr A (Stacks.Blowup.blowUpOver I)
          ((twistScalarSheafMap_reesConst_eq_globalSmulCenter_int I q b).trans
            (globalSmulCenter_pullbackCoeff_app_eq_smul_id I b
              (Stacks.Blowup.blowUpTwist I q))))
        N).trans
    (geometricFactorFormulaMap_smul_id_app A (Stacks.Blowup.blowUpOver I)
      (Stacks.Blowup.blowUpTwist I q) b N)

end Stacks.LocalCohomology.UniformityIII

end
