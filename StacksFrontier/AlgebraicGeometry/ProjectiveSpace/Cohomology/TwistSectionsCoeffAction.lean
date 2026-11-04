module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Functoriality
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsLinear
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishing
public import StacksFrontier.AlgebraicGeometry.TwistDataConstruction.Absolute

/-!
# The coefficients act on the twisted global sections through the degree-zero scalars

Let `𝒮` be a nonnegatively graded ring, `X = Proj 𝒮` and `ℱ` a sheaf of `𝒪_X`-modules. A
degree-zero scalar acts on `Γ(X, ℱ(m))` through the morphism `ℱ(m) ⟶ ℱ(m)` it induces, and that
morphism is multiplication by the global function whose value at every point is the scalar over
`1`. For `ℙⁿ_R = Proj R[T₀, …, Tₙ]` this identifies the action of a constant polynomial `C r`
with the action of the global function that `r : R` pulls back to along `ℙⁿ_R ⟶ Spec R`, which is
the `R`-module structure the cohomology of [Stacks, Tag 01YS] clause (3) carries.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_zero_eq_globalSmulCenter`:
  on `𝒪(m)` a degree-zero scalar acts as a global function.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.tensorSheafMap_id_globalSmulCenter`: tensoring
  with the identity of `ℱ` carries that action to `ℱ(m)`.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.cast_homogeneousScalarTwistedSections_zero`: the
  degree-zero homogeneous action on `Γ(X, ℱ(m))` is the action of that global function.
* `Stacks.ProjectiveSpace.Cohomology.cast_homogeneousScalarTwistedSections_C` and
  `Stacks.ProjectiveSpace.Cohomology.C_smul_of`: on `ℙⁿ_R` the degree-zero scalar `C r` acts as
  `Stacks.ProjectiveSpace.Cohomology.coeffScalar`.

## Implementation notes

Multiplication by a global function is
`Stacks.RegularSequence.globalSmulCenter`, an element of the centre of the category of
`𝒪_X`-modules; the twisting step is checked on the pure tensors of sections, where it is
`TensorProduct.tmul_smul` followed by linearity of the sheafification unit.

The global function is passed as a parameter together with the equation pinning down its value at
each point, so that the general statements are available for any spelling of the pullback; the
`ℙⁿ_R` statements instantiate it by
`Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val`.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (twistingSheaf twistSheafOfModules twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistSheafScalarMap
  twistedSectionsComponent homogeneousScalarTwistedSections twistedDegree_zero
  cast_homogeneousScalarTwistedSections TwistedGlobalSectionsModule)
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.RegularSequence (globalSmulCenter)
open scoped Stacks.GradedLocalization TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The localization of multiplication by a ring element is multiplication by the image of that
element in the localization. -/
private theorem map_mul_eq {A : Type u} [CommRing A] {P : Submonoid A} (a : A)
    (z : Localization P) :
    LocalizedModule.map P (LinearMap.mul A A a) z = algebraMap A (Localization P) a * z := by
  rw [← Localization.mk_one_eq_algebraMap a]
  induction z using Localization.induction_on with
  | H y =>
    show LocalizedModule.map P (LinearMap.mul A A a) (LocalizedModule.mk y.1 y.2) = _
    rw [LocalizedModule.map_mk, Localization.mk_mul]
    simp only [LinearMap.mul_apply', one_mul]
    rfl

/-- **Multiplication by a degree-zero scalar on `𝒪(m)` is multiplication by a global function.**
Let `c` be a global section of `𝒪_{Proj 𝒮}` whose value at every point is the fraction `a / 1`
for a degree-zero `a`. Then multiplication by `a` on the twisting sheaf `𝒪(m)` is the action
of `c`. -/
theorem twistScalarSheafMap_zero_eq_globalSmulCenter (m : ℤ) (a : 𝒮 0)
    (c : (projRingSheaf 𝒮).obj.obj (op ⊤))
    (hc : ∀ x : ProjectiveSpectrum.top 𝒮,
      HomogeneousLocalization.val (c.1 ⟨x, trivial⟩) =
        algebraMap S (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (a : S)) :
    twistScalarSheafMap 𝒮 0 m m (twistedDegree_zero m) a =
      (globalSmulCenter (AlgebraicGeometry.Proj 𝒮) c).app (twistingSheaf 𝒮 m) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  refine Subtype.ext (funext fun x => ?_)
  have key : LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
        (LinearMap.mul S S (a : S)) (s.1 x) =
      HomogeneousLocalization.val (c.1 ⟨x.1, trivial⟩) * s.1 x :=
    (map_mul_eq (a : S) (s.1 x)).trans
      (congrArg (fun z => z * s.1 x) (hc x.1).symm)
  exact key

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-- **Multiplication by a global function commutes with twisting.** Tensoring the identity of
`ℱ` with multiplication by a global function `c` on `𝒪(m)` is multiplication by `c` on
`ℱ(m) = ℱ ⊗ 𝒪(m)`: the tensor product is taken over `𝒪_X`. -/
theorem tensorSheafMap_id_globalSmulCenter (m : ℤ) (c : (projRingSheaf 𝒮).obj.obj (op ⊤)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩)).map
        (((𝟙 F), ((globalSmulCenter (AlgebraicGeometry.Proj 𝒮) c).app (twistingSheaf 𝒮 m))) :
          (_, _) ⟶ (_, _))) =
      (globalSmulCenter (AlgebraicGeometry.Proj 𝒮) c).app (twistSheafOfModules 𝒮 F m) := by
  refine Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext _ _ ?_
  intro U x y
  obtain ⟨U⟩ := U
  refine Eq.trans
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 m) F (twistingSheaf 𝒮 m) (𝟙 F)
      ((globalSmulCenter (AlgebraicGeometry.Proj 𝒮) c).app (twistingSheaf 𝒮 m)) U x y) ?_
  have crossScalar : x ⊗ₜ[(AlgebraicGeometry.Proj 𝒮).presheaf.obj (op U)]
        ((AlgebraicGeometry.Proj 𝒮).presheaf.map U.leTop.op c • y) =
      (AlgebraicGeometry.Proj 𝒮).presheaf.map U.leTop.op c •
        x ⊗ₜ[(AlgebraicGeometry.Proj 𝒮).presheaf.obj (op U)] y :=
    TensorProduct.tmul_smul _ x y
  have key : Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 m) (op U)
        (x ⊗ₜ[(AlgebraicGeometry.Proj 𝒮).presheaf.obj (op U)]
          ((AlgebraicGeometry.Proj 𝒮).presheaf.map U.leTop.op c • y)) =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf
            ⟨(AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf,
              (AlgebraicGeometry.Proj 𝒮).toRingedSpace.IsSheaf⟩).obj.obj (op U))
          _ _ ((AlgebraicGeometry.Proj 𝒮).presheaf.map U.leTop.op c)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 m) (op U)
          (x ⊗ₜ[(AlgebraicGeometry.Proj 𝒮).presheaf.obj (op U)] y)) :=
    (congrArg (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 m) (op U))
      crossScalar).trans
      (map_smul ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit
        (AlgebraicGeometry.Proj 𝒮).toRingedSpace
        ((PresheafOfModules.tensorObj (O := ((AlgebraicGeometry.Proj 𝒮).toRingedSpace).presheaf)
          (F.val) ((twistingSheaf 𝒮 m).val)))).app (op U)).hom _ _)
  exact key

/-- **Multiplication by a degree-zero scalar on `ℱ(m)` is multiplication by a global function.**
Let `c` be a global section of `𝒪_{Proj 𝒮}` whose value at every point is `a / 1` for a
degree-zero `a`. Then the morphism `ℱ(m) ⟶ ℱ(m)` induced by `a` is the action of `c`. -/
theorem twistSheafScalarMap_zero_eq_globalSmulCenter (m : ℤ) (a : 𝒮 0)
    (c : (projRingSheaf 𝒮).obj.obj (op ⊤))
    (hc : ∀ x : ProjectiveSpectrum.top 𝒮,
      HomogeneousLocalization.val (c.1 ⟨x, trivial⟩) =
        algebraMap S (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (a : S)) :
    twistSheafScalarMap 𝒮 F 0 m m (twistedDegree_zero m) a =
      (globalSmulCenter (AlgebraicGeometry.Proj 𝒮) c).app (twistSheafOfModules 𝒮 F m) := by
  refine Eq.trans ?_ (tensorSheafMap_id_globalSmulCenter 𝒮 F m c)
  show ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
        (((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩)).map
      (((𝟙 F), (twistScalarSheafMap 𝒮 0 m m (twistedDegree_zero m) a)) :
        (_, _) ⟶ (_, _))) = _
  rw [twistScalarSheafMap_zero_eq_globalSmulCenter 𝒮 m a c hc]
  rfl

/-- Restricting a global section to `⊤` changes nothing. -/
private theorem map_leTop_top (c : (projRingSheaf 𝒮).obj.obj (op ⊤)) :
    (projRingSheaf 𝒮).obj.map
      (homOfLE (le_top : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) ≤ ⊤)).op c = c := by
  rw [show (homOfLE (le_top : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)) ≤ ⊤)) = 𝟙 _ from
      Subsingleton.elim _ _,
    op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The degree-zero homogeneous action on the twisted global sections is the action of a global
function.** A degree-zero scalar `a` acts on `Γ(Proj 𝒮, ℱ(m))` as the global section `c` of
`𝒪_{Proj 𝒮}` whose value at every point is `a / 1`, once the degree `0 + m` is identified
with `m`. -/
theorem cast_homogeneousScalarTwistedSections_zero (m : ℤ) (a : 𝒮 0)
    (c : (projRingSheaf 𝒮).obj.obj (op ⊤))
    (hc : ∀ x : ProjectiveSpectrum.top 𝒮,
      HomogeneousLocalization.val (c.1 ⟨x, trivial⟩) =
        algebraMap S (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (a : S))
    (s : twistedSectionsComponent 𝒮 F m) :
    cast (congrArg (twistedSectionsComponent 𝒮 F) (twistedDegree_zero m))
        (homogeneousScalarTwistedSections 𝒮 F 0 m a s) = c • s := by
  rw [cast_homogeneousScalarTwistedSections 𝒮 F 0 m m (twistedDegree_zero m) a s,
    twistSheafScalarMap_zero_eq_globalSmulCenter 𝒮 F m a c hc]
  exact congrArg (fun z : (projRingSheaf 𝒮).obj.obj (op ⊤) => z • s) (map_leTop_top 𝒮 c)

end Stacks.AlgebraicGeometry.ProjTwistedSections

namespace Stacks.ProjectiveSpace.Cohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

variable (R : Type u) [CommRing R] (n : ℕ)

/-- A constant polynomial is homogeneous of degree zero. -/
theorem C_mem_polyGrading_zero (r : R) :
    MvPolynomial.C r ∈ polyGrading R n 0 :=
  (MvPolynomial.mem_homogeneousSubmodule 0 (MvPolynomial.C r)).2
    (MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (polyGrading R n)))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))))

/-- **The coefficients act through the degree-zero scalars.** On the global sections of `ℱ(m)`
the degree-zero homogeneous scalar `C r` acts as the global function that `r : R` pulls back to
along the structure morphism `ℙⁿ_R ⟶ Spec R`, once the degree `0 + m` is identified with `m`. -/
theorem cast_homogeneousScalarTwistedSections_C (m : ℤ) (r : R)
    (s : twistedSectionsComponent (polyGrading R n) F m) :
    cast (congrArg (twistedSectionsComponent (polyGrading R n) F) (twistedDegree_zero m))
        (homogeneousScalarTwistedSections (polyGrading R n) F 0 m
          ⟨MvPolynomial.C r, C_mem_polyGrading_zero R n r⟩ s) =
      coeffScalar R n r • s :=
  Stacks.AlgebraicGeometry.ProjTwistedSections.cast_homogeneousScalarTwistedSections_zero
    (polyGrading R n) F m ⟨MvPolynomial.C r, C_mem_polyGrading_zero R n r⟩
    (coeffScalar R n r)
    (fun x => Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val R n r x) s

/-- **The `R = 𝒮₀` action bridge.** For the graded `MvPolynomial (Fin (n+1)) R`-module structure
on `⨁_{m ∈ ℤ} Γ(ℙⁿ_R, ℱ(m))`, a coefficient `r : R` acting through the constant polynomial `C r`
acts on the degree-`m` summand as the global function that `r` pulls back to along
`ℙⁿ_R ⟶ Spec R`, which is the `R`-action of
`Stacks.ProjectiveSpace.Cohomology.coeffScalar`. -/
theorem C_smul_of
    (D : Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule
      (polyGrading R n) F)
    (r : R) (m : ℤ) (s : twistedSectionsComponent (polyGrading R n) F m) :
    letI := D.moduleInst
    (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) •
        (DirectSum.of (fun k : ℤ => twistedSectionsComponent (polyGrading R n) F k) m s :
          twistedGlobalSections (polyGrading R n) F) =
      DirectSum.of (fun k : ℤ => twistedSectionsComponent (polyGrading R n) F k) m
        (coeffScalar R n r • s) :=
  let := D.moduleInst
  (D.smul_homogeneous 0 m ⟨MvPolynomial.C r, C_mem_polyGrading_zero R n r⟩ s).trans
    (DirectSum.of_eq_of_heq (twistedDegree_zero m)
      ((cast_heq (congrArg (twistedSectionsComponent (polyGrading R n) F)
            (twistedDegree_zero m)) _).symm.trans
        (heq_of_eq (cast_homogeneousScalarTwistedSections_C R n F m r s))))

end Stacks.ProjectiveSpace.Cohomology

end
