module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence

/-!
# Lower cohomological bounds under a total right derived functor

Let `F` be an additive functor out of an abelian category `A` with enough injectives and let
`(R, β)` be a total right derived functor of `F` on the whole unbounded derived category `D(A)`.
If `β` is invertible at a K-injective complex `I`, then `R` applied to the object represented by
`I` is the object represented by the termwise image `F(I)`. For an additive functor out of the
`𝒪_X`-modules of a scheme, `β` is invertible at every K-injective complex, `R` preserves the
lower end of the range of degrees in which an object lives, and the canonical comparison
`H^i(R(τ_{≤ a}E)) ⟶ H^i(R(E))` is an isomorphism for `i ≤ a`.

## Main results

* `Stacks.SmallDerivedCategory.rightDerivedKInjectiveIso` — the isomorphism
  `Q(F(I)) ≅ R(Q(I))` at a K-injective complex `I`.
* `AlgebraicGeometry.isIso_app_isKInjective_of_isRightDerivedFunctor` — for a functor out of
  the `𝒪_X`-modules of a scheme, the structure map is invertible at every K-injective complex.
* `AlgebraicGeometry.isGE_rightDerivedFunctor_obj` — for such a functor, `R` preserves the lower
  bound of an object with quasi-coherent cohomology.
* `AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι` — the lower
  truncation comparison for such a functor.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 0D62](https://stacks.math.columbia.edu/tag/0D62)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.SmallDerivedCategory

section KInjectiveComputation

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
    IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))

/-- **The value of a total right derived functor at a K-injective complex.** If the structure map
`β` of `(R, β)` is invertible at the K-injective complex `I`, then `R` applied to the object of
`D(A)` represented by `I` is the object represented by the termwise image `F(I)`. -/
def rightDerivedKInjectiveIso (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      R.obj (DerivedCategory.Q.obj I) :=
  have := hcomp I hI
  ((DerivedCategory.quotientCompQhIso B).app _).symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I).symm ≪≫
    asIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) ≪≫
    R.mapIso ((DerivedCategory.quotientCompQhIso A).app I)

end KInjectiveComputation

end Stacks.SmallDerivedCategory

namespace AlgebraicGeometry

section Scheme

variable (X : Scheme.{u}) {B : Type*} [Category B] [Abelian B]
  [HasDerivedCategory X.Modules] [HasDerivedCategory B]
  (F : X.Modules ⥤ B) [F.Additive]
  (RF : DerivedCategory X.Modules ⥤ DerivedCategory B)
  (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]

/-- The structure map of a total right derived functor out of `K(𝒪_X)` is invertible at every
K-injective complex of `𝒪_X`-modules. -/
theorem isIso_app_isKInjective_of_isRightDerivedFunctor
    (I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
    IsIso (alpha.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (Scheme.Modules.exists_quasiIso_isKInjective X)).2 DerivedCategory.Qh RF alpha I hI

include F alpha in
/-- A total right derived functor of an additive functor out of the `𝒪_X`-modules of a scheme
preserves the lower end of the range of degrees in which an object with quasi-coherent cohomology
lives. -/
@[stacks 08D4 "part (3), lower bound"]
theorem isGE_rightDerivedFunctor_obj
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a : ℤ) (hE : E.IsGE a) : (RF.obj E).IsGE a := by
  have _hcoh := hcoh
  exact Stacks.SmallDerivedCategory.isGE_obj_of_isGE F RF alpha
    (isIso_app_isKInjective_of_isRightDerivedFunctor X F RF alpha) E a hE

include F alpha in
/-- A total right derived functor of an additive functor out of the `𝒪_X`-modules of a scheme
agrees in degrees at most `a` on an object with quasi-coherent cohomology and on its canonical
truncation in degrees at most `a`. -/
@[stacks 08D4 "part (1)"]
theorem isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι
    (E : DerivedCategory X.Modules)
    (hE : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (RF.map ((DerivedCategory.TStructure.t.truncLEι a).app E))) := by
  have _hE := hE
  let _ := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  let T := RF.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E)
  have ht : T ∈ distTriang (DerivedCategory B) :=
    RF.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E)
  have hg : T.obj₃.IsGE (a + 1) :=
    Stacks.SmallDerivedCategory.isGE_obj_of_isGE F RF alpha
      (isIso_app_isKInjective_of_isRightDerivedFunctor X F RF alpha)
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E) (a + 1) inferInstance
  have : Epi ((DerivedCategory.homologyFunctor B i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₁_iff
      T ht i).2 ((T.obj₃.isZero_of_isGE (a + 1) i (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor B i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
      T ht (i - 1) i (by omega)).2
        ((T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor B i).map T.mor₁)

end Scheme

end AlgebraicGeometry

end
