module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.KoszulLeibniz
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The filtration of `⋀(𝒪(-1)^{⊕ (n+1)})` and right multiplication

On `X = Proj R[T₀, …, Tₙ]` let `E = 𝒪(-1)^{⊕ (n+1)}`, `ι : ⋀^{p+1} E ⟶ ⋀^p E` the Koszul
contraction against the Euler surjection `φ : E ⟶ 𝒪`, and `q_p : ⋀^{p+1} E ⟶ Ωᵖ` the quotient
arrow of the filtration `0 ⟶ Ω^{p+1} ⟶ ⋀^{p+1} E ⟶ Ωᵖ ⟶ 0`, so that `⋀ᵖ(Ω ⟶ E) ∘ q_p = ι`. The
Leibniz rule `ι(g ∧ e) = ι(g) ∧ e + (-1)^{p+1} φ(e) g` gives the two identities relating the
products `⋀^{p+1} E × E ⟶ ⋀^{p+2} E`, `Ωᵖ × Ω ⟶ Ω^{p+1}` and the scalar action, which are the
commutative squares of [Stacks, Tag 07MC] in the proof of [Stacks, Tag 0FMI]:

* `q_{p+1}(g ∧ ω) = q_p(g) ∧ ω` for a local section `ω` of `Ω ⊆ E`;
* `q_{p+1}((-1)^{p+1} x ∧ e) = φ(e) x` for a local section `x` of `Ω^{p+1} ⊆ ⋀^{p+1} E`.

## References

* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

open Stacks.AlgebraicGeometry.ProjPolyChart

variable (R : Type u) [CommRing R] (n : ℕ)

/-- `⋀^k` of the first arrow of the Euler sequence is injective on sections. -/
@[sga "7 XI 1.1" "(1.1.8)"]
theorem injective_exteriorPowerMap_eulerFirstArrow_app (k : ℕ)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n))) :
    Function.Injective ((Scheme.Modules.exteriorPowerMap
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n) (k : ℤ)).val.app
        (op U)) :=
  @Stacks.SheafOfModules.injective_app_of_mono _ _ _ _ _ _ _
    (mono_exteriorPowerMap_eulerFirstArrow R n k) (op U)

/-- `⋀ᵖ(Ω ⟶ E) ∘ q_p = ι`, on local sections. -/
theorem exteriorPowerMap_eulerWedgeQuotient_app (p : ℕ)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (g : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n) ((p + 1 : ℕ) : ℤ)).val.obj (op U)) :
    (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) ((p : ℕ) : ℤ)).val.app (op U)
        ((eulerWedgeQuotient R n p).val.app (op U) g) =
      (eulerWedgeContraction R n p).val.app (op U) g :=
  congrArg (fun φ => φ.val.app (op U) g) (eulerWedgeQuotient_comp_exteriorPowerMap R n p)

/-- The exterior powers of the first arrow of the Euler sequence are multiplicative. -/
theorem exteriorPowerMap_mul_app (i j : ℤ) (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (x : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n) i).val.obj (op U))
    (y : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n) j).val.obj (op U)) :
    (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) (i + j)).val.app (op U)
        (((Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n)).mul i j).app (op U) x y) =
      ((Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n)).mul i j).app (op U)
        ((Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
          (eulerFirstArrow R n) i).val.app (op U) x)
        ((Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
          (eulerFirstArrow R n) j).val.app (op U) y) :=
  ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n)).map
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
        (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (eulerFirstArrow R n)).map_mul i j (op U) x y

/-- `⋀¹(Ω ⟶ E)` on a generator. -/
theorem exteriorPowerMap_one_generator (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (ω : (projDifferentials R n).val.obj (op U)) :
    (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) 1).val.app (op U)
        ((Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n)).val.app (op U) ω) =
      (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n)).val.app (op U)
        ((eulerFirstArrow R n).val.app (op U) ω) :=
  congrArg (fun φ => φ.val.app (op U) ω)
    ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
        (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n)).map_app_one
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
          (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
      (eulerFirstArrow R n))

/-- The Euler surjection kills the image of the first arrow, on local sections. -/
theorem eulerSurjection_eulerFirstArrow_app (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (ω : (projDifferentials R n).val.obj (op U)) :
    (eulerSurjection R n).val.app (op U) ((eulerFirstArrow R n).val.app (op U) ω) = 0 :=
  congrArg (fun φ => φ.val.app (op U) ω) (eulerFirstArrow_comp_eulerSurjection R n)

/-- `⋀ᵖ(Ω ⟶ E)` is multiplicative for the product of a `p`-form with a `1`-form, with the degree
of the product written `p + 1`. -/
theorem exteriorPowerMap_mul_one_app (p : ℕ)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (x : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n) (p : ℤ)).val.obj (op U))
    (y : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n) 1).val.obj (op U)) :
    (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)).val.app (op U)
        (((Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
          (projDifferentials R n)).mul (p : ℤ) 1).app (op U) x y) =
      ((Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
          (twistMinusOneSum R n)).mul (p : ℤ) 1).app (op U)
        ((Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
          (eulerFirstArrow R n) (p : ℤ)).val.app (op U) x)
        ((Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
          (eulerFirstArrow R n) 1).val.app (op U) y) :=
  exteriorPowerMap_mul_app R n (p : ℤ) 1 U x y

/-- The Euler surjection kills the image of the first arrow, as an element of the ring of local
sections. -/
theorem unitDualApp_eulerSurjection_eulerFirstArrow
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (ω : (projDifferentials R n).val.obj (op U)) :
    SheafOfModules.unitDualApp (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
      (M := twistMinusOneSum R n) (eulerSurjection R n) (op U)
        ((eulerFirstArrow R n).val.app (op U) ω) = 0 :=
  eulerSurjection_eulerFirstArrow_app R n U ω

/-- `q_p g = x` as soon as `ι g = ⋀ᵖ(Ω ⟶ E) x`, on local sections. -/
private theorem eulerWedgeQuotient_app_eq_of_contraction_eq (p : ℕ)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (g : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n) ((p + 1 : ℕ) : ℤ)).val.obj (op U))
    (x : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n) (p : ℤ)).val.obj (op U))
    (h : (eulerWedgeContraction R n p).val.app (op U) g =
      (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) (p : ℤ)).val.app (op U) x) :
    (eulerWedgeQuotient R n p).val.app (op U) g = x :=
  injective_exteriorPowerMap_eulerFirstArrow_app R n p U
    ((exteriorPowerMap_eulerWedgeQuotient_app R n p U g).trans h)

/-- **`q_{p+1}(g ∧ ω) = q_p(g) ∧ ω`** for a local section `g` of `⋀^{p+1} E` and a local section
`ω` of `Ω ⊆ E`. -/
theorem eulerWedgeQuotient_mul_eulerFirstArrow (p : ℕ)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (g : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n) ((p + 1 : ℕ) : ℤ)).val.obj (op U))
    (ω : (projDifferentials R n).val.obj (op U)) :
    (eulerWedgeQuotient R n (p + 1)).val.app (op U)
        (((Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
          (twistMinusOneSum R n)).mul ((p + 1 : ℕ) : ℤ) 1).app
          (op U) g ((Scheme.Modules.exteriorGenerator
              (X := AlgebraicGeometry.Proj (polyGrading R n))
            (twistMinusOneSum R n)).val.app (op U)
            ((eulerFirstArrow R n).val.app (op U) ω))) =
      ((Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
          (projDifferentials R n)).mul (p : ℤ) 1).app (op U)
        ((eulerWedgeQuotient R n p).val.app (op U) g)
        ((Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
          (projDifferentials R n)).val.app (op U) ω) := by
  refine eulerWedgeQuotient_app_eq_of_contraction_eq R n (p + 1) U _ _ ?_
  have hL := SheafOfModules.exteriorContraction_mul_gen_of_unitDualApp_eq_zero
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
        (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (eulerSurjection R n) p U g ((eulerFirstArrow R n).val.app (op U) ω)
    (unitDualApp_eulerSurjection_eulerFirstArrow R n U ω)
  refine hL.trans ?_
  refine Eq.trans ?_ (exteriorPowerMap_mul_one_app R n p U _ _).symm
  exact congrArg₂ (fun a b => ((Scheme.Modules.exteriorAlgebra
    (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n)).mul (p : ℤ) 1).app
      (op U) a b) (exteriorPowerMap_eulerWedgeQuotient_app R n p U g).symm
    (exteriorPowerMap_one_generator R n U ω).symm

/-- The Koszul contraction kills the image of `⋀^{p+1}(Ω ⟶ E)`. -/
theorem eulerWedgeContraction_exteriorPowerMap_app (p : ℕ)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (x : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n) ((p + 1 : ℕ) : ℤ)).val.obj (op U)) :
    (eulerWedgeContraction R n p).val.app (op U)
        ((Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
          (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)).val.app (op U) x) = 0 := by
  refine (exteriorPowerMap_eulerWedgeQuotient_app R n p U _).symm.trans ?_
  refine (congrArg _ (congrArg (fun φ => φ.val.app (op U) x)
    (exteriorPowerMap_comp_eulerWedgeQuotient R n p))).trans ?_
  exact map_zero _

/-- **`q_{p+1}((-1)^{p+1} x ∧ e) = φ(e) x`** for a local section `x` of `Ω^{p+1} ⊆ ⋀^{p+1} E` and
a local section `e` of `E`. -/
theorem eulerWedgeQuotient_mul_exteriorPowerMap (p : ℕ)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (x : (Scheme.Modules.exteriorPower (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n) ((p + 1 : ℕ) : ℤ)).val.obj (op U))
    (e : (twistMinusOneSum R n).val.obj (op U)) :
    (eulerWedgeQuotient R n (p + 1)).val.app (op U)
        (((Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
          (twistMinusOneSum R n)).mul ((p + 1 : ℕ) : ℤ) 1).app (op U)
          ((((p : ℤ) + 1).negOnePow : ℤ) •
            (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
              (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)).val.app (op U) x)
          ((Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
            (twistMinusOneSum R n)).val.app (op U) e)) =
      (show (AlgebraicGeometry.Proj (polyGrading R n)).ringCatSheaf.obj.obj (op U) from
        (eulerSurjection R n).val.app (op U) e) • x := by
  refine eulerWedgeQuotient_app_eq_of_contraction_eq R n (p + 1) U _ _ ?_
  refine (SheafOfModules.exteriorContraction_mul_gen_of_eq_zero
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
        (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (eulerSurjection R n) p U _ e (eulerWedgeContraction_exteriorPowerMap_app R n p U x)).trans ?_
  exact ((ModuleCat.Hom.hom ((Scheme.Modules.exteriorPowerMap
    (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)
      ((p + 1 : ℕ) : ℤ)).val.app (op U))).map_smul _ x).symm

end Stacks.AlgebraicGeometry.ProjEulerSequence
