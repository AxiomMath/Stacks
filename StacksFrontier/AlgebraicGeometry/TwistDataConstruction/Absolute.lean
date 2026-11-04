module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPresentation
public import StacksFrontier.AlgebraicGeometry.TwistDataFromChart.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded algebra of twists on an absolute projective spectrum

For a graded ring `𝒜`, the twisting sheaves `𝒪(n)` on `Proj 𝒜` form a sheaf of `ℤ`-graded
algebras, with the canonical product of local sections of the twists as its multiplication and the
global section of `𝒪(0)` attached to `1` as its unit. Sections of a twist are dependent functions
into the fibres, so addition, the scalar action, restriction, the product and the unit are all
computed pointwise.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistDataConstruction.twistProd`: the canonical product of two local
  sections of the twists, over an object of the opposite site of `Proj 𝒜`.
* `Stacks.AlgebraicGeometry.TwistDataConstruction.twistUnit`: the unit section of `𝒪(0)`, over
  an object of the opposite site of `Proj 𝒜`.
* `Stacks.AlgebraicGeometry.TwistDataConstruction.twistAlgebra`: `⨁ₙ 𝒪(n)` as a sheaf of
  `ℤ`-graded algebras on `Proj 𝒜`.

## Main results

* `Stacks.AlgebraicGeometry.TwistDataConstruction.twistProd_heq_assoc`,
  `twistProd_heq_one_mul` and `twistProd_heq_mul_one`: the canonical product of local sections of
  the twists is associative and unital.
* `Stacks.AlgebraicGeometry.TwistDataConstruction.twistAlgebra_mul_app` and
  `twistAlgebra_one_eval`: the multiplication and unit of `twistAlgebra` are
  `Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` and `absoluteTwistUnit`.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistDataConstruction

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {R : Type u} {σ : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### Sections of a twist are functions

The sections of `twistingSheaf 𝒜 n` over an open form a submodule of the dependent functions into
the fibres, with the pointwise module structure, and restriction is precomposition with the
inclusion of opens. -/

/-- Two sections of a twist agreeing at every point are equal. -/
public theorem twist_ext {n : ℤ} {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    {a b : (twistingSheaf 𝒜 n).val.obj X} (h : ∀ x : X.unop, a.1 x = b.1 x) : a = b :=
  Subtype.ext (funext h)

/-- Addition of sections of a twist is pointwise. -/
public theorem add_val {n : ℤ} {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    (a b : (twistingSheaf 𝒜 n).val.obj X) (x : X.unop) :
    (a + b).1 x = a.1 x + b.1 x := rfl

/-- The scalar action on sections of a twist is pointwise, through the value of the section of
the structure sheaf at the point. -/
public theorem smul_val {n : ℤ} {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj X)
    (a : (twistingSheaf 𝒜 n).val.obj X) (x : X.unop) :
    (r • a).1 x = HomogeneousLocalization.val (r.1 x) * a.1 x := rfl

/-- Restriction of sections of a twist is restriction of functions. -/
public theorem map_val {n : ℤ} {X Y : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (f : X ⟶ Y)
    (a : (twistingSheaf 𝒜 n).val.obj X) (x : Y.unop) :
    ((twistingSheaf 𝒜 n).val.map f a).1 x = a.1 (f.unop x) := rfl

/-! ### The product and the unit over an object of the opposite site -/

/-- The canonical product of two local sections of the twists, over an object of the opposite
site of `Proj 𝒜`. -/
public def twistProd (i j : ℤ) {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    (a : (twistingSheaf 𝒜 i).val.obj X) (b : (twistingSheaf 𝒜 j).val.obj X) :
    (twistingSheaf 𝒜 (i + j)).val.obj X :=
  absoluteTwistProduct 𝒜 i j X.unop a b

/-- The unit section of the degree-zero twist, over an object of the opposite site. -/
public def twistUnit {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} :
    (twistingSheaf 𝒜 0).val.obj X :=
  absoluteTwistUnit 𝒜 X.unop

/-- The value of the product at a point is the product of the two values. -/
public theorem twistProd_val (i j : ℤ) {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    (a : (twistingSheaf 𝒜 i).val.obj X) (b : (twistingSheaf 𝒜 j).val.obj X) (x : X.unop) :
    (twistProd 𝒜 i j a b).1 x = a.1 x * b.1 x :=
  TwistRigidity.absoluteTwistProduct_apply 𝒜 i j X.unop a b x

/-- The value of the unit at every point is `1`. -/
public theorem twistUnit_val {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (x : X.unop) :
    (twistUnit 𝒜 (X := X)).1 x = 1 :=
  ThetaMultiplicative.absoluteTwistUnit_apply 𝒜 X.unop x

/-- Sections of two twists whose degrees are equal are heterogeneously equal if the transport of
the first along the equality of degrees is the second. -/
public theorem heq_of_eqRec_eq {k l : ℤ} (e : k = l)
    {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    {x : (twistingSheaf 𝒜 k).val.obj X} {y : (twistingSheaf 𝒜 l).val.obj X}
    (h : e ▸ x = y) : HEq x y := by
  subst e
  exact heq_of_eq h

/-! ### Bilinearity of the canonical product -/

/-- The canonical product is additive in its second variable. -/
public theorem twistProd_add_right (i j : ℤ)
    {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (a : (twistingSheaf 𝒜 i).val.obj X)
    (b b' : (twistingSheaf 𝒜 j).val.obj X) :
    twistProd 𝒜 i j a (b + b') = twistProd 𝒜 i j a b + twistProd 𝒜 i j a b' :=
  twist_ext 𝒜 fun x => by simp only [twistProd_val, add_val, mul_add]

/-- The canonical product is additive in its first variable. -/
public theorem twistProd_add_left (i j : ℤ)
    {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (a a' : (twistingSheaf 𝒜 i).val.obj X)
    (b : (twistingSheaf 𝒜 j).val.obj X) :
    twistProd 𝒜 i j (a + a') b = twistProd 𝒜 i j a b + twistProd 𝒜 i j a' b :=
  twist_ext 𝒜 fun x => by simp only [twistProd_val, add_val, add_mul]

/-- The canonical product is linear in its first variable. -/
public theorem twistProd_smul_left (i j : ℤ) {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj X)
    (a : (twistingSheaf 𝒜 i).val.obj X) (b : (twistingSheaf 𝒜 j).val.obj X) :
    twistProd 𝒜 i j (r • a) b = r • twistProd 𝒜 i j a b :=
  twist_ext 𝒜 fun x => by simp only [twistProd_val, smul_val, mul_assoc]

/-- The canonical product is linear in its second variable. -/
public theorem twistProd_smul_right (i j : ℤ) {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj X)
    (a : (twistingSheaf 𝒜 i).val.obj X) (b : (twistingSheaf 𝒜 j).val.obj X) :
    twistProd 𝒜 i j a (r • b) = r • twistProd 𝒜 i j a b :=
  twist_ext 𝒜 fun x => by
    simp only [twistProd_val, smul_val]
    exact mul_left_comm _ _ _

/-- The canonical product commutes with restriction. -/
public theorem twistProd_naturality (i j : ℤ)
    {X Y : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (f : X ⟶ Y)
    (a : (twistingSheaf 𝒜 i).val.obj X) (b : (twistingSheaf 𝒜 j).val.obj X) :
    (twistingSheaf 𝒜 (i + j)).val.map f (twistProd 𝒜 i j a b) =
      twistProd 𝒜 i j ((twistingSheaf 𝒜 i).val.map f a)
        ((twistingSheaf 𝒜 j).val.map f b) :=
  twist_ext 𝒜 fun x =>
    (twistProd_val 𝒜 i j a b (f.unop x)).trans
      (twistProd_val 𝒜 i j ((twistingSheaf 𝒜 i).val.map f a)
        ((twistingSheaf 𝒜 j).val.map f b) x).symm

/-! ### The three laws -/

/-- Sections of twists of equal degrees are heterogeneously equal if their values agree at every
point. -/
private theorem heq_of_val_eq {k l : ℤ} (e : k = l) {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    {x : (twistingSheaf 𝒜 k).val.obj X} {y : (twistingSheaf 𝒜 l).val.obj X}
    (h : ∀ p : X.unop, x.1 p = y.1 p) : HEq x y :=
  heq_of_eqRec_eq 𝒜 e (twist_ext 𝒜 fun p =>
    (congrFun (TwistDataFromChart.eqRec_val 𝒜 e x) p).trans (h p))

/-- **The canonical product of local sections of the twists is associative**, as a heterogeneous
equality between sections of the twists of degrees `(i + j) + k` and `i + (j + k)`. -/
public theorem twistProd_heq_assoc (i j k : ℤ)
    {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (a : (twistingSheaf 𝒜 i).val.obj X)
    (b : (twistingSheaf 𝒜 j).val.obj X) (c : (twistingSheaf 𝒜 k).val.obj X) :
    HEq (twistProd 𝒜 (i + j) k (twistProd 𝒜 i j a b) c)
      (twistProd 𝒜 i (j + k) a (twistProd 𝒜 j k b c)) := by
  refine heq_of_val_eq 𝒜 (add_assoc i j k) fun x => ?_
  simp only [twistProd_val, mul_assoc]

/-- **The unit section is a left identity for the canonical product.** -/
public theorem twistProd_heq_one_mul (i : ℤ)
    {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (a : (twistingSheaf 𝒜 i).val.obj X) :
    HEq (twistProd 𝒜 0 i (twistUnit 𝒜) a) a := by
  refine heq_of_val_eq 𝒜 (zero_add i) fun x => ?_
  simp only [twistProd_val, twistUnit_val, one_mul]

/-- **The unit section is a right identity for the canonical product.** -/
public theorem twistProd_heq_mul_one (i : ℤ)
    {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (a : (twistingSheaf 𝒜 i).val.obj X) :
    HEq (twistProd 𝒜 i 0 a (twistUnit 𝒜)) a := by
  refine heq_of_val_eq 𝒜 (add_zero i) fun x => ?_
  simp only [twistProd_val, twistUnit_val, mul_one]

/-! ### The graded algebra -/

/-- **The canonical product of local sections of the twists, as an `𝒪`-bilinear map of sheaves
of modules**, namely `Stacks.AlgebraicGeometry.ProjConeTwist.twistMul`. -/
public def twistMul (i j : ℤ) :
    SheafOfModules.BilinearMap (twistingSheaf 𝒜 i) (twistingSheaf 𝒜 j)
      (twistingSheaf 𝒜 (i + j)) :=
  ProjConeTwist.twistMul 𝒜 i j

/-- **The unit of the graded algebra of twists**: the global section of `𝒪(0)` attached to the
homogeneous element `1` of degree `0`, as a compatible family of sections over every open, namely
`Stacks.AlgebraicGeometry.ProjConeTwist.twistOne`. -/
public def twistOne : (twistingSheaf 𝒜 0).sections :=
  ProjConeTwist.twistOne 𝒜

/-- **The twists on an absolute projective spectrum form a sheaf of `ℤ`-graded algebras**, with
the twisting sheaves as its homogeneous pieces, the canonical product of local sections of the
twists as its multiplication, and the global section attached to `1` as its unit. -/
@[ega "II 8.1.5" "partial", ega "III 2.3.2" "special case"]
public def twistAlgebra : SchemeGradedAlgebra (AlgebraicGeometry.Proj 𝒜) where
  piece n := twistingSheaf 𝒜 n
  mul i j := ProjConeTwist.twistMul 𝒜 i j
  one := ProjConeTwist.twistOne 𝒜
  mul_assoc i j k U a b c := ProjConeTwist.twistMul_heq_assoc 𝒜 i j k U a b c
  one_mul i U a := ProjConeTwist.twistMul_heq_one_mul 𝒜 i U a
  mul_one i U a := ProjConeTwist.twistMul_heq_mul_one 𝒜 i U a

/-- The homogeneous pieces of `twistAlgebra` are the twisting sheaves. -/
public theorem twistAlgebra_piece (n : ℤ) : (twistAlgebra 𝒜).piece n = twistingSheaf 𝒜 n := rfl

/-- **The multiplication of `twistAlgebra` is the canonical product of absolute twist sections**,
on every open and in every pair of integer degrees. -/
public theorem twistAlgebra_mul_app (i j : ℤ) {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ}
    (a : (twistingSheaf 𝒜 i).val.obj X) (b : (twistingSheaf 𝒜 j).val.obj X) :
    ((twistAlgebra 𝒜).mul i j).app X a b = absoluteTwistProduct 𝒜 i j X.unop a b :=
  twist_ext 𝒜 fun x => (twistProd_val 𝒜 i j a b x).symm

/-- **The unit of `twistAlgebra` is the unit section of the degree-zero twist**, on every
open. -/
public theorem twistAlgebra_one_eval {X : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} :
    (twistAlgebra 𝒜).one.eval X = absoluteTwistUnit 𝒜 X.unop :=
  twist_ext 𝒜 fun x => (twistUnit_val 𝒜 (X := X) x).symm

end Stacks.AlgebraicGeometry.TwistDataConstruction

end
