module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PushforwardSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.BilinearZero
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiPullbackLeg
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPull

/-!
# The homogeneous-section map of Tag 01NR is multiplicative, in every integer bidegree

The field `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ` of [Stacks, Tag 01NR] is a
family of morphisms `𝒜_n ⟶ π_*𝒪(n)` indexed by the **natural** numbers, and the multiplicativity
it carries is the field `TwistData.ψ_mul`, an `HEq` between local sections. The packaging that
turns such a family into a homomorphism of sheaves of `ℤ`-graded algebras — and hence transposes
it, multiplicativity included, across `π^* ⊣ π_*` — asks instead for an **integer**-indexed family
together with an honest equation in every bidegree.

This file performs that match. Negative degrees are filled in by the unique morphism out of a zero
object, the homogeneous pieces of Situation 01NN vanishing below degree zero; the equation in a
bidegree where one of the two degrees is negative holds because the local section there is zero and
both multiplications kill a zero argument; and in a bidegree where both are natural it is `ψ_mul`,
read through the identification `↑(n + m) = ↑n + ↑m` of the sum degree.

The outcome is that `TwistData.psiTranspose` of
`StacksFrontier.AlgebraicGeometry.TwistTensor.PsiPullbackLeg` — the second leg of Lemma 01O1's
triangle, before its base change along `r` — is the degreewise family of a homomorphism of sheaves
of graded algebras, so it is compatible with the multiplications.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiDirect`: **the homogeneous-section map
  in every integer degree**, as a map into the direct image, the negative degrees being the unique
  morphism out of a zero object.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiDirectHom`: **the homomorphism of
  sheaves of graded algebras `𝒜 ⟶ π_*(⨁_{n ∈ ℤ} 𝒪(n))`** it assembles into.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTransposeHom`: **the adjoint transpose
  `π^*𝒜 ⟶ ⨁_{n ∈ ℤ} 𝒪(n)` as a homomorphism of sheaves of graded algebras**, across the
  correspondence of Tag 0FQX.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiDirect_map_mul`: **the integer-indexed
  section map preserves products of homogeneous local sections**, in every bidegree.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTransposeHom_app`: **the components of
  the transposed homomorphism are `TwistData.psiTranspose`** — the homomorphism is the leg of the
  triangle and not some other morphism with the same source and target.
* `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.psiTranspose_mulSheaf`: **the leg is
  compatible with the morphism-level multiplications**, which is the form a graded comparison
  consumes.

## Implementation notes

`psiDirect` is defined by a pattern match on `Int`, as `TwistData.psiTranspose` is, so that in the
nonnegative branch the degree is literally `((n : ℕ) : ℤ)` and `psiDirect_natCast` is `rfl`.

The sum degree is the one place a transport cannot be avoided: `ψ_mul` is stated at the degree
`↑(n + m)` and the `map_mul` field of a homomorphism of graded algebras is stated at `↑n + ↑m`.
`psiDirect_app_congr` is the bridge, and it is proved by `subst` followed by `rfl` rather than by
a congruence lemma — the equation of degrees is substituted into the goal, after which the two
sides are the same term.

The two adjunctions in play are the same term: `Scheme.Modules.pullbackPushforwardAdjunction π`,
which `psiTranspose` is defined with, **is** `Stacks.RingedSpace.pullbackAdjunction` of the
underlying morphism of ringed spaces, which the transport of graded algebras is stated with, by
`Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackPushforwardAdjunction_eq`. So
`psiTransposeHom_app` needs no conversion.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open SheafOfModules.GradedAlgebra

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal
attribute [local instance] Stacks.PushforwardGradedAlgebra.pushforwardFunctorLaxMonoidal

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

namespace TwistData

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A)

/-! ### The homogeneous-section map in every integer degree -/

/-- **The homogeneous-section map of [Stacks, Tag 01NR] in every integer degree**, as a map into
the direct image along the structure morphism `π : Proj_S(𝒜) ⟶ S`.

In a nonnegative degree this is the field `TwistData.ψ`; in a negative degree the homogeneous piece
`𝒜_m` vanishes and this is the unique morphism out of it. -/
def psiDirect : ∀ m : ℤ,
    (situationAlgebra A).piece m ⟶
      (Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra
        (ringedSpaceHom (relativeProj A).toBase) D.algebra).piece m
  | (n : ℕ) => D.ψ n
  | .negSucc n => (A.negative_isZero _ (Int.negSucc_lt_zero n)).to_ _

/-- In a nonnegative degree the integer-indexed section map is the field `TwistData.ψ`, on the
nose. -/
@[simp] theorem psiDirect_natCast (n : ℕ) : D.psiDirect (n : ℤ) = D.ψ n := rfl

/-- In a negative degree the integer-indexed section map is the unique morphism out of a zero
module, so it agrees with every other morphism there. -/
theorem psiDirect_eq_of_neg {m : ℤ} (hm : m < 0)
    (w : (situationAlgebra A).piece m ⟶
      (Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra
        (ringedSpaceHom (relativeProj A).toBase) D.algebra).piece m) :
    D.psiDirect m = w :=
  (A.negative_isZero m hm).eq_of_src _ _

/-- **The value of the section map transported along an equality of degrees.** This is the bridge
between the degree `↑(n + m)` at which the field `TwistData.ψ_mul` is stated and the degree
`↑n + ↑m` at which the `map_mul` field of a homomorphism of sheaves of graded algebras is. -/
theorem psiDirect_app_congr {i j : ℤ} (hij : i = j) (U : S.Opens)
    (x : Γ((situationAlgebra A).piece i, U)) :
    HEq ((D.psiDirect i).val.app (op U) x) ((D.psiDirect j).val.app (op U) (hij ▸ x)) := by
  subst hij
  rfl

/-! ### Multiplicativity in every bidegree -/

/-- **The integer-indexed section map preserves products of homogeneous local sections, in a
bidegree where both degrees are natural.** This is the field `TwistData.ψ_mul`, read at the sum
degree `↑n + ↑m` instead of at `↑(n + m)`. -/
theorem psiDirect_map_mul_natCast (n m : ℕ) (U : S.Opens)
    (a : Γ((situationAlgebra A).piece (n : ℤ), U))
    (b : Γ((situationAlgebra A).piece (m : ℤ), U)) :
    (D.psiDirect ((n : ℤ) + (m : ℤ))).val.app (op U)
        (((situationAlgebra A).mul (n : ℤ) (m : ℤ)).app (op U) a b) =
      ((Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra
          (ringedSpaceHom (relativeProj A).toBase) D.algebra).mul (n : ℤ) (m : ℤ)).app (op U)
        ((D.psiDirect (n : ℤ)).val.app (op U) a) ((D.psiDirect (m : ℤ)).val.app (op U) b) := by
  have hnm : ((n : ℤ) + (m : ℤ)) = ((n + m : ℕ) : ℤ) := (Int.natCast_add n m).symm
  refine eq_of_heq (HEq.trans (D.psiDirect_app_congr hnm U _) ?_)
  refine HEq.trans (D.ψ_mul U n m a b) ?_
  exact heq_of_eq (ProjRepresentsF1.pushforwardGradedAlgebra_mul_app
    (relativeProj A).toBase D.algebra (n : ℤ) (m : ℤ) U _ _).symm

/-- **The integer-indexed section map preserves products of homogeneous local sections**, in every
bidegree.

Where both degrees are natural this is `psiDirect_map_mul_natCast`. Where one of them is negative
the homogeneous piece of `𝒜` in that degree is a zero object, so the local section there is zero,
and both sides vanish: a sheaf-level bilinear map kills a zero argument
(`SheafBilinearMap.app_zero_left`, `app_zero_right`), and so does the multiplication of the direct
image. The piece in the sum degree need not vanish, which is why this is an argument about the
arguments and not about the target. -/
theorem psiDirect_map_mul (i j : ℤ) (U : (Opens S.carrier)ᵒᵖ)
    (a : ((situationAlgebra A).piece i).val.obj U)
    (b : ((situationAlgebra A).piece j).val.obj U) :
    (D.psiDirect (i + j)).val.app U (((situationAlgebra A).mul i j).app U a b) =
      ((Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra
          (ringedSpaceHom (relativeProj A).toBase) D.algebra).mul i j).app U
        ((D.psiDirect i).val.app U a) ((D.psiDirect j).val.app U b) := by
  obtain ⟨U⟩ := U
  rcases lt_or_ge i 0 with hi | hi
  · have ha : a = 0 := section_eq_zero_of_isZero (A.negative_isZero i hi) U a
    subst ha
    rw [show ((situationAlgebra A).mul i j).app (op U) 0 b = 0 from
      SheafBilinearMap.app_zero_left (A.mul i j) U b]
    simp only [map_zero]
    rfl
  rcases lt_or_ge j 0 with hj | hj
  · have hb : b = 0 := section_eq_zero_of_isZero (A.negative_isZero j hj) U b
    subst hb
    rw [show ((situationAlgebra A).mul i j).app (op U) a 0 = 0 from
      SheafBilinearMap.app_zero_right (A.mul i j) U a]
    simp only [map_zero]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  exact D.psiDirect_map_mul_natCast n m U a b

/-! ### The homomorphism of sheaves of graded algebras, and its transpose -/

/-- **The homomorphism of sheaves of `ℤ`-graded algebras `𝒜 ⟶ π_*(⨁_{n ∈ ℤ} 𝒪(n))` carried by the
homogeneous-section map of [Stacks, Tag 01NR].** -/
def psiDirectHom :
    situationAlgebra A ⟶
      Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra
        (ringedSpaceHom (relativeProj A).toBase) D.algebra where
  app := D.psiDirect
  map_mul := D.psiDirect_map_mul

/-- The degree-`m` component of `TwistData.psiDirectHom` is the homogeneous-section map
`TwistData.psiDirect m`. -/
@[simp] theorem psiDirectHom_app (m : ℤ) : (D.psiDirectHom).app m = D.psiDirect m := rfl

/-- **The adjoint transpose of the homogeneous-section homomorphism** across the correspondence of
[Stacks, Tag 0FQX] between homomorphisms out of a pullback and homomorphisms into a pushforward.
Its components are `TwistData.psiTranspose` by `psiTransposeHomAux_app`. -/
def psiTransposeHomAux :
    Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
        (ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A) (isSheafStruct S) ⟶
      D.algebra :=
  transportHomBackward (pullbackAdjunction (ringedSpaceHom (relativeProj A).toBase))
    (isSheafStruct (relativeProj A).scheme) (isSheafStruct S) D.psiDirectHom

/-- **The components of the transposed homomorphism are `TwistData.psiTranspose`**: the
homomorphism is the second leg of Lemma 01O1's triangle, before its base change, and not some
other morphism with the same source and target.

In a nonnegative degree both sides are the inverse hom-set bijection applied to `ψ`, the two
adjunctions being the same term by
`Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackPushforwardAdjunction_eq`. In a negative degree
the source is a zero object and a morphism out of one is unique. -/
theorem psiTransposeHomAux_app (m : ℤ) : (D.psiTransposeHomAux).app m = D.psiTranspose m := by
  rcases lt_or_ge m 0 with hm | hm
  · exact (D.psiTranspose_eq_of_neg hm _).symm
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rfl

/-- **The second leg of Lemma 01O1's triangle preserves products of homogeneous local sections**,
before its base change along `r`.

This is the multiplicativity of `psiTransposeHomAux` read through `psiTransposeHomAux_app`. It is
stated on sections rather than on the morphism-level multiplications because sections mention no
monoidal structure, so a consumer may read it in whichever of the equal monoidal structures on
sheaves of modules it has chosen; `psiTranspose_mulSheaf` is the morphism-level form. -/
theorem psiTranspose_map_mul (i j : ℤ)
    (U : (Opens (relativeProj A).scheme.carrier)ᵒᵖ)
    (x : ((Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
        (ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A)
        (isSheafStruct S)).piece i).val.obj U)
    (y : ((Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
        (ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A)
        (isSheafStruct S)).piece j).val.obj U) :
    (D.psiTranspose (i + j)).val.app U
        (((Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
          (ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A)
          (isSheafStruct S)).mul i j).app U x y) =
      (D.algebra.mul i j).app U ((D.psiTranspose i).val.app U x)
        ((D.psiTranspose j).val.app U y) := by
  rw [← D.psiTransposeHomAux_app i, ← D.psiTransposeHomAux_app j,
    ← D.psiTransposeHomAux_app (i + j)]
  exact (D.psiTransposeHomAux).map_mul i j U x y

/-- **The second leg of Lemma 01O1's triangle, as a homomorphism of sheaves of `ℤ`-graded
algebras** `π^*𝒜 ⟶ ⨁_{n ∈ ℤ} 𝒪(n)`, with `TwistData.psiTranspose` for its components on the
nose. -/
def psiTransposeHom :
    Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
        (ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A) (isSheafStruct S) ⟶
      D.algebra where
  app := D.psiTranspose
  map_mul := D.psiTranspose_map_mul

/-- The degree-`m` component of `TwistData.psiTransposeHom` is the transposed map
`TwistData.psiTranspose m`. -/
@[simp] theorem psiTransposeHom_app (m : ℤ) : (D.psiTransposeHom).app m = D.psiTranspose m := rfl

/-- **The second leg of Lemma 01O1's triangle is compatible with the morphism-level
multiplications**, before its base change along `r`: the family `TwistData.psiTranspose` carries
the multiplication of `π^*𝒜` to that of `⨁_{n ∈ ℤ} 𝒪(n)`.

This is the form a comparison of graded algebras consumes, and it is the multiplicativity that
`TwistData.psiLeg` and `TwistData.psiLegVeronese` inherit. -/
theorem psiTranspose_mulSheaf (i j : ℤ) :
    mulSheaf (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
          (ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A)
          (isSheafStruct S)) i j ≫ D.psiTranspose (i + j) =
      MonoidalCategoryStruct.tensorHom (D.psiTranspose i) (D.psiTranspose j) ≫
        mulSheaf D.algebra i j :=
  (mulSheaf_comp_eq_iff (isSheafStruct (relativeProj A).scheme)
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
      (ringedSpaceHom (relativeProj A).toBase) (situationAlgebra A) (isSheafStruct S))
    D.algebra D.psiTranspose i j).mpr (D.psiTranspose_map_mul i j)

end TwistData

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
