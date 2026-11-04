module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegMultiplicative
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleChartGlue
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleFromPair
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback

/-!
# The base-changed homogeneous-section map is multiplicative

Let `D` be a twist datum for `𝒜` over `S`, with structure morphism `π : Proj_S(𝒜) ⟶ S`, and let
`r : T ⟶ Proj_S(𝒜)` be a morphism with `r ≫ π = f`. The adjoint transpose `TwistData.psiTranspose`
of the homogeneous-section map across `π^* ⊣ π_*`, pulled back along `r` and read in the
`d`-divisible grading, is `TwistData.psiLegVeronese`. This file proves it multiplicative and
assembles it into a homomorphism `f^*𝒜^{(d)} ⟶ r^*(⨁_{n ∈ ℤ} 𝒪(nd))` of sheaves of `ℤ`-graded
`𝒪_T`-algebras. The base change is carried out for an arbitrary homomorphism out of a pulled-back
graded algebra, in `Stacks.AlgebraicGeometry.GradedLegBaseChange`.

## Main definitions

* `GradedLegBaseChange.leg`: a homomorphism `h^*ℬ ⟶ 𝒞` of graded algebras out of a pulled-back
  one, base-changed along `g` to a degreewise family `(g ≫ h)^*ℬ_m ⟶ g^*𝒞_m`.
* `RelativeProjTwists.TwistData.psiLegVeroneseHom`: `TwistData.psiLegVeronese` as a homomorphism
  of sheaves of `ℤ`-graded `𝒪_T`-algebras `f^*𝒜^{(d)} ⟶ r^*(⨁_{n ∈ ℤ} 𝒪(nd))`.

## Main results

* `GradedLegBaseChange.leg_mulSheaf` and `GradedLegBaseChange.leg_mulSheaf'`: the base-changed
  family is multiplicative in every pair of degrees, the second with the target degree free and
  carried by an `eqToHom`.
* `GradedLegBaseChange.leg_veronese_mulSheaf`: the same in the `d`-divisible grading.
* `RelativeProjTwists.TwistData.psiLegVeronese_mulSheaf`: `TwistData.psiLegVeronese` carries the
  multiplication of `f^*𝒜^{(d)}` to that of `r^*(⨁_n 𝒪(nd))`.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.RingedSpace
open Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists
open Stacks.AlgebraicGeometry.GradedVeronese
open SheafOfModules.GradedAlgebra

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal

universe u

namespace Stacks.AlgebraicGeometry.GradedLegBaseChange

variable {T X Sb : Scheme.{u}} (g : T ⟶ X) (h : X ⟶ Sb)
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Sb.toRingedSpace)}
  {C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
  (φ : Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom h) B
    (isSheafStruct Sb) ⟶ C)

/-- A homomorphism `φ : h^*ℬ ⟶ 𝒞` out of a pulled-back graded algebra, base-changed along `g`: in
degree `m`, the comparison `(g ≫ h)^*ℬ_m ⟶ g^*h^*ℬ_m` followed by `g^*φ_m`. -/
def leg (m : ℤ) :
    (pullbackFunctor (ringedSpaceHom (g ≫ h))).obj (B.piece m) ⟶
      (pullbackFunctor (ringedSpaceHom g)).obj (C.piece m) :=
  compComparison g h (B.piece m) ≫
    (pullbackFunctor (ringedSpaceHom g)).map (φ.app m)

/-- The base-changed family is multiplicative in every pair of degrees, the target degree being the
sum. -/
theorem leg_mulSheaf (m n : ℤ) :
    inv (pullbackTensorComparison (ringedSpaceHom (g ≫ h)) (B.piece m) (B.piece n)) ≫
        (pullbackFunctor (ringedSpaceHom (g ≫ h))).map (B.mulSheaf m n) ≫ leg g h φ (m + n) =
      (leg g h φ m ⊗ₘ leg g h φ n) ≫
        inv (pullbackTensorComparison (ringedSpaceHom g) (C.piece m) (C.piece n)) ≫
          (pullbackFunctor (ringedSpaceHom g)).map (C.mulSheaf m n) := by
  simp only [leg]
  have key := inv_pullbackTensorComparison_comp_map_comp_compComparison g h
    (B.mulSheaf m n) (φ.app (m + n))
    (𝟙 ((pullbackFunctor (ringedSpaceHom g)).obj (C.piece (m + n))))
  simp only [Category.comp_id] at key
  have inner : inv (pullbackTensorComparison (ringedSpaceHom h) (B.piece m) (B.piece n)) ≫
      (pullbackFunctor (ringedSpaceHom h)).map (B.mulSheaf m n) ≫ φ.app (m + n) =
      (φ.app m ⊗ₘ φ.app n) ≫ C.mulSheaf m n :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ φ.app (m + n))
        (ProjRepresentsF1.mulSheaf_pullbackGradedAlgebra (f := h) B m n).symm)).trans
      (mulSheaf_comp_app _ C φ m n)
  have nat' : inv (pullbackTensorComparison (ringedSpaceHom g)
        ((pullbackFunctor (ringedSpaceHom h)).obj (B.piece m))
        ((pullbackFunctor (ringedSpaceHom h)).obj (B.piece n))) ≫
      (pullbackFunctor (ringedSpaceHom g)).map (φ.app m ⊗ₘ φ.app n) =
      ((pullbackFunctor (ringedSpaceHom g)).map (φ.app m) ⊗ₘ
          (pullbackFunctor (ringedSpaceHom g)).map (φ.app n)) ≫
        inv (pullbackTensorComparison (ringedSpaceHom g) (C.piece m) (C.piece n)) :=
    (IsIso.inv_comp_eq _).2 (((IsIso.eq_comp_inv _).2
      (pullbackTensorComparison_naturality_tensorHom (ringedSpaceHom g)
        (φ.app m) (φ.app n))).trans (Category.assoc _ _ _))
  have step : inv (pullbackTensorComparison (ringedSpaceHom g)
        ((pullbackFunctor (ringedSpaceHom h)).obj (B.piece m))
        ((pullbackFunctor (ringedSpaceHom h)).obj (B.piece n))) ≫
      (pullbackFunctor (ringedSpaceHom g)).map ((φ.app m ⊗ₘ φ.app n) ≫ C.mulSheaf m n) =
      ((pullbackFunctor (ringedSpaceHom g)).map (φ.app m) ⊗ₘ
          (pullbackFunctor (ringedSpaceHom g)).map (φ.app n)) ≫
        inv (pullbackTensorComparison (ringedSpaceHom g) (C.piece m) (C.piece n)) ≫
          (pullbackFunctor (ringedSpaceHom g)).map (C.mulSheaf m n) :=
    (congrArg (fun z => inv (pullbackTensorComparison (ringedSpaceHom g)
          ((pullbackFunctor (ringedSpaceHom h)).obj (B.piece m))
          ((pullbackFunctor (ringedSpaceHom h)).obj (B.piece n))) ≫ z)
        ((pullbackFunctor (ringedSpaceHom g)).map_comp (φ.app m ⊗ₘ φ.app n)
          (C.mulSheaf m n))).trans
      (((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ (pullbackFunctor (ringedSpaceHom g)).map
            (C.mulSheaf m n)) nat')).trans (Category.assoc _ _ _))
  rw [key, inner]
  simp only [Category.assoc, ← MonoidalCategory.tensorHom_comp_tensorHom]
  exact congrArg (fun z => (compComparison g h (B.piece m) ⊗ₘ
    compComparison g h (B.piece n)) ≫ z) step

/-- `leg_mulSheaf` with the target degree free, carried by an `eqToHom`. -/
theorem leg_mulSheaf' (m n k : ℤ) (hk : m + n = k) :
    inv (pullbackTensorComparison (ringedSpaceHom (g ≫ h)) (B.piece m) (B.piece n)) ≫
        (pullbackFunctor (ringedSpaceHom (g ≫ h))).map
            (B.mulSheaf m n ≫ eqToHom (congrArg B.piece hk)) ≫ leg g h φ k =
      (leg g h φ m ⊗ₘ leg g h φ n) ≫
        inv (pullbackTensorComparison (ringedSpaceHom g) (C.piece m) (C.piece n)) ≫
          (pullbackFunctor (ringedSpaceHom g)).map
            (C.mulSheaf m n ≫ eqToHom (congrArg C.piece hk)) := by
  subst hk
  exact (congrArg (fun z =>
        inv (pullbackTensorComparison (ringedSpaceHom (g ≫ h)) (B.piece m) (B.piece n)) ≫
          (pullbackFunctor (ringedSpaceHom (g ≫ h))).map z ≫ leg g h φ (m + n))
      (Category.comp_id (B.mulSheaf m n))).trans
    ((leg_mulSheaf g h φ m n).trans
      (congrArg (fun z => (leg g h φ m ⊗ₘ leg g h φ n) ≫
          inv (pullbackTensorComparison (ringedSpaceHom g) (C.piece m) (C.piece n)) ≫
            (pullbackFunctor (ringedSpaceHom g)).map z)
        (Category.comp_id (C.mulSheaf m n)).symm))

/-- The base-changed family, read in the `d`-divisible grading, is multiplicative. -/
theorem leg_veronese_mulSheaf (d i j : ℤ) :
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom (g ≫ h))
          (veronese B d) (isSheafStruct Sb)).mulSheaf i j ≫ leg g h φ ((i + j) * d) =
      (leg g h φ (i * d) ⊗ₘ leg g h φ (j * d)) ≫
        (Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom g)
          (veronese C d)).mulSheaf i j := by
  rw [ProjRepresentsF1.mulSheaf_pullbackGradedAlgebra, veronese_mulSheaf B d,
    Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra, veronese_mulSheaf C d]
  exact leg_mulSheaf' g h φ (i * d) (j * d) ((i + j) * d) (by ring)

end Stacks.AlgebraicGeometry.GradedLegBaseChange

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

namespace TwistData

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A)
  {f : T ⟶ S} (r : T ⟶ (relativeProj A).scheme)

/-- For `f` equal to `r ≫ π` by `rfl`, the leg `TwistData.psiLeg` is the contraction of the
iterated pullback followed by the pullback along `r` of the transpose. -/
theorem psiLeg_rfl_eq (m : ℤ) :
    D.psiLeg r rfl m =
      compComparison r (relativeProj A).toBase ((situationAlgebra A).piece m) ≫
        (pullbackFunctor (ringedSpaceHom r)).map (D.psiTranspose m) :=
  congrArg (fun z => z ≫ (pullbackFunctor (ringedSpaceHom r)).map (D.psiTranspose m))
    (compComparison_eq_pullbackComp_inv r (relativeProj A).toBase
      ((situationAlgebra A).piece m)).symm

/-- The leg `TwistData.psiLegVeronese` carries the multiplication of `f^*𝒜^{(d)}` to that of
`r^*(⨁_n 𝒪(nd))`. -/
theorem psiLegVeronese_mulSheaf (hr : r ≫ (relativeProj A).toBase = f) (d i j : ℤ) :
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f)
          (veronese (situationAlgebra A) d) (isSheafStruct S)).mulSheaf i j ≫
        D.psiLegVeronese r hr d (i + j) =
      (D.psiLegVeronese r hr d i ⊗ₘ D.psiLegVeronese r hr d j) ≫
        (RelativeVeroneseTwists.pullbackTwistVeronese D d r).mulSheaf i j := by
  subst hr
  simp only [TwistData.psiLegVeronese_eq, D.psiLeg_rfl_eq r]
  exact GradedLegBaseChange.leg_veronese_mulSheaf r (relativeProj A).toBase
    D.psiTransposeHom d i j

/-- The leg `TwistData.psiLegVeronese` as a homomorphism of sheaves of `ℤ`-graded `𝒪_T`-algebras
`f^*𝒜^{(d)} ⟶ r^*(⨁_{n ∈ ℤ} 𝒪(nd))`. -/
def psiLegVeroneseHom (hr : r ≫ (relativeProj A).toBase = f) (d : ℤ) :
    Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f)
        (veronese (situationAlgebra A) d) (isSheafStruct S) ⟶
      RelativeVeroneseTwists.pullbackTwistVeronese D d r :=
  homOfMulSheaf _ _ (D.psiLegVeronese r hr d) (D.psiLegVeronese_mulSheaf r hr d)

/-- The components of `psiLegVeroneseHom` are those of `TwistData.psiLegVeronese`. -/
@[simp] theorem psiLegVeroneseHom_app (hr : r ≫ (relativeProj A).toBase = f) (d n : ℤ) :
    (D.psiLegVeroneseHom r hr d).app n = D.psiLegVeronese r hr d n := rfl

end TwistData

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
