module

public import StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Universal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trivially graded algebra of the structure sheaf, and the trivialization datum it carries

`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.GradedSectionAlgebraHom` is the datum that
dehomogenizes a quotient pair: an additive map out of the homogeneous sections of each degree
over one open of the site, into a commutative ring, carrying the graded product to the product
and the graded unit to `1`. `Universal.datumOfGenerator` descends such a datum along the
universal property of the tensor algebra: a datum for *any* sheaf of graded algebras `G`
together with a degree-one map `L ⟶ G.piece 1` gives one for the tensor algebra of `L`.

This file supplies the `G` that makes that descent usable, and it is the simplest one there is:
the graded algebra whose homogeneous piece is the free sheaf of rank one in *every* degree, with
the product of the sheaf of rings as its graded multiplication. It is `𝒪[x, x⁻¹]` with `x` a
unit of degree one, written so that its degree-`n` local sections are the ring of local sections
on the nose.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.ofUnit` and `toUnit`: the identification of
  the local sections of `SheafOfModules.unit` with the local sections of the sheaf of rings,
  both of which are the identity function.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.unitGradedAlgebra`: the sheaf of graded
  algebras whose every homogeneous piece is `SheafOfModules.unit`, with multiplication the
  product of the sheaf of rings.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.unitDatum`: the trivialization datum it
  carries, for any ring homomorphism out of its ring of sections over the chosen open. In every
  degree the datum is that one homomorphism.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.unitDatum_toFun`: the datum is the given
  ring homomorphism in every degree, with no comparison map in between.

## Implementation notes

**Every homogeneous piece is the same object, which is what makes the algebra laws cheap.**
`SheafOfModules.GradedAlgebra` states associativity and the two unit laws with `HEq`, because in
general `piece ((i + j) + k)` and `piece (i + (j + k))` are different sheaves of modules indexed
by equal integers. Here `piece` is a constant function, so the two sides of each law already
have the same type and `heq_of_eq` applies to the corresponding ring identity. No transport
along an equality of degrees appears anywhere in this file.

**The homogeneous sections are the ring of sections definitionally.** `SheafOfModules.unit` is
`PresheafOfModules.unit`, whose value at `W` is `ModuleCat.of _ (R.obj W)`, so the carrier of
`(unitGradedAlgebra R h).piece n |>.val.obj W` *is* the carrier of `R.obj.obj W`; its addition
is the ring's addition, its scalar action is the ring's multiplication, and its restriction maps
are the ring's restriction maps. All four are `rfl`, which is what makes `unitDatum` a ring
homomorphism read in every degree, and which realizes literally the datum of a trivializing
section described in the module docstring of
`StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Basic`.

**`ofUnit` and `toUnit` are identity functions and exist for instance search alone.** A local
section of a homogeneous piece has the *syntactic* type `↥((SheafOfModules.unit R).val.obj W)`,
and `Mul` is not found at that head even though it is found at the definitionally equal
`↥(R.obj.obj W)`; a type ascription does not help, because it leaves the term's inferred type
unchanged. Applying `ofUnit` does change the inferred type, so the product elaborates. Every
proof in the file is then the ring identity itself: the two propositions are definitionally
equal, so no transport is needed, only the term-level spelling.

**Commutativity of the sheaf of rings is a hypothesis rather than a typeclass.** Bilinearity of
the multiplication in the *second* variable is `x * (r * y) = r * (x * y)`, which fails for a
noncommutative sheaf of rings; `SheafOfModules` is indexed by `RingCat`, where commutativity is
not part of the type. The hypothesis is a `Prop` on local sections, and
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.isCommutativeRingSheaf_scheme` discharges it
for the structure sheaf of a scheme.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjF1Dehomogenization

universe w t v u

section UnitAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{t})

/-- **A local section of the free sheaf of rank one, read as a local section of the sheaf of
rings.** The identity function; see the implementation notes. -/
public def ofUnit {W : Cᵒᵖ} (x : (SheafOfModules.unit R).val.obj W) : R.obj.obj W := x

/-- **A local section of the sheaf of rings, read as a local section of the free sheaf of rank
one.** The identity function; see the implementation notes. -/
public def toUnit {W : Cᵒᵖ} (x : R.obj.obj W) : (SheafOfModules.unit R).val.obj W := x

/-- Reading a local section of the sheaf of rings into the free sheaf of rank one and back is
the identity. -/
@[simp]
public theorem ofUnit_toUnit {W : Cᵒᵖ} (x : R.obj.obj W) : ofUnit R (toUnit R x) = x := rfl

/-- Reading a local section of the free sheaf of rank one into the sheaf of rings and back is
the identity. -/
@[simp]
public theorem toUnit_ofUnit {W : Cᵒᵖ} (x : (SheafOfModules.unit R).val.obj W) :
    toUnit R (ofUnit R x) = x := rfl

/-- The identification `ofUnit` over `W`, as an additive homomorphism. -/
public def ofUnitHom (W : Cᵒᵖ) : (SheafOfModules.unit R).val.obj W →+ R.obj.obj W where
  toFun := ofUnit R
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `ofUnitHom` applied to a local section is `ofUnit` of that section. -/
@[simp]
public theorem ofUnitHom_apply (W : Cᵒᵖ) (x : (SheafOfModules.unit R).val.obj W) :
    ofUnitHom R W x = ofUnit R x :=
  rfl

/-- **Commutativity of a sheaf of rings, on local sections**: over every object of the site,
any two local sections commute. -/
@[ega "0 4.1.3"]
public def IsCommutativeRingSheaf : Prop :=
  ∀ (W : Cᵒᵖ) (x y : R.obj.obj W), x * y = y * x

variable (hR : IsCommutativeRingSheaf R)

/-- **The unit section**: the global section of `SheafOfModules.unit` whose value over every
object of the site is `1`. -/
public def unitSections : (SheafOfModules.unit R).sections :=
  PresheafOfModules.sectionsMk (M := PresheafOfModules.unit R.obj)
    (fun W => toUnit R 1) (by intro X Y f; exact PresheafOfModules.unit_map_one R.obj f)

/-- The unit section, read as a local section of the sheaf of rings, is `1` over every object. -/
@[simp]
public theorem ofUnit_unitSections_eval (W : Cᵒᵖ) :
    ofUnit R ((unitSections R).eval W) = 1 :=
  rfl

/-- **The product of the sheaf of rings, as a bilinear map of the free sheaf of rank one.**
Linearity in the first variable is associativity of the product; in the second it is
associativity together with the commutativity hypothesis. -/
public def unitMul :
    SheafOfModules.BilinearMap (SheafOfModules.unit R) (SheafOfModules.unit R)
      (SheafOfModules.unit R) where
  app _ :=
    { toFun := fun x =>
        { toFun := fun y => toUnit R (ofUnit R x * ofUnit R y)
          map_zero' := mul_zero (ofUnit R x)
          map_add' := fun a b => mul_add (ofUnit R x) (ofUnit R a) (ofUnit R b) }
      map_zero' := AddMonoidHom.ext fun y => zero_mul (ofUnit R y)
      map_add' := fun a b =>
        AddMonoidHom.ext fun y => add_mul (ofUnit R a) (ofUnit R b) (ofUnit R y) }
  map_smul_left _ r x y := _root_.mul_assoc r (ofUnit R x) (ofUnit R y)
  map_smul_right W r x y :=
    Eq.trans (congrArg (fun z : R.obj.obj W => ofUnit R x * z) (hR W r (ofUnit R y)))
      (Eq.trans (_root_.mul_assoc (ofUnit R x) (ofUnit R y) r).symm
        (hR W (ofUnit R x * ofUnit R y) r))
  naturality {_ _} f x y := (R.obj.map f).hom.map_mul (ofUnit R x) (ofUnit R y)

/-- `unitMul` of two local sections, read in the sheaf of rings, is their product. -/
@[simp]
public theorem ofUnit_unitMul_app (W : Cᵒᵖ) (x y : (SheafOfModules.unit R).val.obj W) :
    ofUnit R ((unitMul R hR).app W x y) = ofUnit R x * ofUnit R y :=
  rfl

/-- **The free sheaf of rank one in every degree.** The sheaf of graded algebras whose
homogeneous piece is the free sheaf of rank one in every degree and whose multiplication is the
product of the sheaf of rings: `𝒪[x, x⁻¹]` with `x` an invertible section of degree one. -/
public def unitGradedAlgebra : SheafOfModules.GradedAlgebra.{t, t} R where
  piece _ := SheafOfModules.unit R
  mul _ _ := unitMul R hR
  one := unitSections R
  mul_assoc _ _ _ _ x y z := heq_of_eq (_root_.mul_assoc (ofUnit R x) (ofUnit R y) (ofUnit R z))
  one_mul _ _ x := heq_of_eq (_root_.one_mul (ofUnit R x))
  mul_one _ _ x := heq_of_eq (_root_.mul_one (ofUnit R x))

/-- Every homogeneous piece of `unitGradedAlgebra` is the free sheaf of rank one. -/
@[simp]
public theorem unitGradedAlgebra_piece (n : ℤ) :
    (unitGradedAlgebra R hR).piece n = SheafOfModules.unit R :=
  rfl

/-- **The trivialization datum of the free sheaf of rank one in every degree.** A ring
homomorphism out of the ring of sections over the chosen open is a trivialization datum for
`unitGradedAlgebra`, the same homomorphism in every degree: multiplicativity is the
homomorphism's own, and the graded unit is the ring unit. -/
public def unitDatum {B : Type w} [CommRing B] {W : Cᵒᵖ} (φ : (R.obj.obj W) →+* B) :
    GradedSectionAlgebraHom (unitGradedAlgebra R hR) W B where
  toFun _ := (φ : (R.obj.obj W) →+ B).comp (ofUnitHom R W)
  map_gmul _ _ x y := φ.map_mul (ofUnit R x) (ofUnit R y)
  map_gone := φ.map_one

/-- In every degree, `unitDatum` sends a local section `x` to `φ (ofUnit R x)`. -/
@[simp]
public theorem unitDatum_toFun {B : Type w} [CommRing B] {W : Cᵒᵖ} (φ : (R.obj.obj W) →+* B)
    (n : ℤ) (x : (SheafOfModules.unit R).val.obj W) :
    (unitDatum R hR φ).toFun n x = φ (ofUnit R x) :=
  rfl

end UnitAlgebra

/-! ### The structure sheaf of a scheme -/

section Scheme

universe u'

/-- **The structure sheaf of a scheme is a commutative sheaf of rings.** -/
public theorem isCommutativeRingSheaf_scheme (X : Scheme.{u'}) :
    IsCommutativeRingSheaf X.ringCatSheaf :=
  fun W x y =>
    mul_comm (show (X.sheaf.val.obj W : Type u') from x) (show (X.sheaf.val.obj W : Type u') from y)

end Scheme

end Stacks.AlgebraicGeometry.ProjF1Dehomogenization

end
