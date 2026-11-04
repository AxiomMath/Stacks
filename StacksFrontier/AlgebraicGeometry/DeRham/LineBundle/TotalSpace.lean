module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Glueing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The algebra sheaf of a line bundle

Let `f : X ⟶ S` be a morphism of schemes and let `L` be an invertible `𝒪_X`-module. The total
space of the line bundle attached to `L` is the relative spectrum of the symmetric algebra
`Sym(L) = ⨁_{n ≥ 0} L^{⊗ n}`, so a sheaf of commutative `𝒪_X`-algebras has to be extracted from
the sheaf of *graded* algebras `Sym(L)`. This file carries out that passage.

The ungraded realization of a sheaf of graded algebras is a sheaf of possibly noncommutative
rings, `SheafOfModules.GradedAlgebra.ungradedSheaf`. When homogeneous multiplication commutes in
every pair of degrees — which is the case for a symmetric algebra — the direct sum of the
homogeneous components is a presheaf of *commutative* rings, and its sheafification in
`CommRingCat`, together with the structure map `r ↦ r • 1`, is an object of
`Stacks.RelativeSpec.AlgebraSheaf X`.

## Main definitions

* `Stacks.GradedAlgebra.totalCommPresheaf`: the ungraded realization of a graded algebra with
  commuting homogeneous multiplication, as a presheaf of commutative rings.
* `Stacks.GradedAlgebra.totalCommStructureMap`: its structure map `r ↦ r • 1`.
* `Stacks.RelativeSpec.ungradedAlgebraSheaf`: **the ungraded realization of a commutative sheaf
  of graded algebras on a scheme, as a sheaf of commutative `𝒪_X`-algebras.**
* `Stacks.LineBundle.Situation`: a morphism of schemes together with an invertible module on its
  source.
* `Stacks.LineBundle.Situation.symmetricAlgebra` and
  `Stacks.LineBundle.Situation.algebraSheaf`: `Sym(L)` as a sheaf of graded algebras, and its
  ungraded realization as a sheaf of commutative `𝒪_X`-algebras.

## Main results

* `Stacks.GradedAlgebra.mul_comm_total_of_addCommMonoid`: the ungraded realization of a graded
  algebra is commutative as soon as homogeneous multiplication is, in every pair of degrees.
* `Stacks.LineBundle.Situation.isQuasicoherent_lineBundle`: an invertible module on a scheme is
  quasi-coherent.
* `Stacks.LineBundle.Situation.symmetricAlgebra_mul_comm`: homogeneous multiplication in `Sym(L)`
  commutes in every pair of degrees, which is what makes the ungraded realization commutative.

## Implementation notes

Commutativity of the ungraded realization is proved on the direct sum, not on its sheafification:
every section of `Stacks.GradedAlgebra.Total` is a finite sum of homogeneous ones, so the double
induction `Stacks.GradedAlgebra.incl_induction` reduces the statement to the homogeneous case,
where it is the hypothesis transported along `i + j = j + i`. Sheafifying afterwards in
`CommRingCat` rather than transporting commutativity across a sheafification is what avoids the
separatedness argument of `Stacks.GradedAlgebra.mul_comm_totalSheaf`.

Homogeneous multiplication of a symmetric algebra commutes in every pair of degrees, not only in
degree one: that is `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra_mul_comm`, which comes from
the sectionwise symmetric algebra and not from the graded universal property.

A relative spectrum requires its algebra sheaf to be quasi-coherent, and that is not proved here:
`Stacks.LineBundle.Situation.isQuasicoherent_algebraSheaf` identifies the module underlying the
algebra sheaf below with the coproduct `⨁_{n ≥ 0} Sym^n L`, and
`Stacks.LineBundle.Situation.totalSpace` constructs the total space from it.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe w v u

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddCommMonoid ι] {P : ι → PresheafOfModules.{w} R} (A : GradedAlgebra P)

/-- Two homogeneous local sections of equal degree which are heterogeneously equal have the same
image in the ungraded realization. -/
theorem incl_congr_heq {U : Cᵒᵖ} {i j : ι} (h : i = j) {x : (P i).obj U} {y : (P j).obj U}
    (hxy : HEq x y) : A.incl i x = A.incl j y := by
  subst h
  rw [eq_of_heq hxy]

/-- **The ungraded realization of a graded algebra is commutative as soon as homogeneous
multiplication is**, in every pair of degrees. Every section is a finite sum of homogeneous
ones, so the statement reduces to the homogeneous case.

This is the universe-polymorphic form over an `AddCommMonoid` of degrees; the single-universe
`Stacks.GradedAlgebra.mul_comm_total` in `Constructions.GradedAlgebraToAlgebraSheaf` takes the
commutativity of the degree monoid as an explicit hypothesis instead. -/
theorem mul_comm_total_of_addCommMonoid
    (hcomm : ∀ (i j : ι) (U : Cᵒᵖ) (x : (P i).obj U) (y : (P j).obj U),
      HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
    {U : Cᵒᵖ} (a b : A.Total U) : a * b = b * a := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i x =>
    induction b using A.incl_induction with
    | zero => simp
    | incl j y =>
      rw [A.incl_mul_incl, A.incl_mul_incl]
      exact A.incl_congr_heq (add_comm i j) (hcomm i j U x y)
    | add b b' hb hb' => rw [mul_add, add_mul, hb, hb']
  | add a a' ha ha' => rw [add_mul, mul_add, ha, ha']

/-- The commutative ring of sections of the ungraded realization of a graded algebra whose
homogeneous multiplication commutes. -/
@[instance_reducible]
def commRingTotal
    (hcomm : ∀ (i j : ι) (U : Cᵒᵖ) (x : (P i).obj U) (y : (P j).obj U),
      HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x)) (U : Cᵒᵖ) :
    CommRing (A.Total U) :=
  { (inferInstance : Ring (A.Total U)) with
    mul_comm := fun a b => A.mul_comm_total_of_addCommMonoid hcomm a b }

/-- Restriction along the identity is the identity on sections of the ungraded realization. -/
theorem totalRestrict_id (U : Cᵒᵖ) (a : A.Total U) : A.totalRestrict (𝟙 U) a = a := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i y => rw [A.totalRestrict_incl, sectionRestrict_id]
  | add a a' ha ha' => rw [map_add, ha, ha']

/-- Restriction along a composite is the composite of the restrictions, on sections of the
ungraded realization. -/
theorem totalRestrict_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (a : A.Total U) :
    A.totalRestrict (f ≫ g) a = A.totalRestrict g (A.totalRestrict f a) := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i y =>
    rw [A.totalRestrict_incl, A.totalRestrict_incl, A.totalRestrict_incl, sectionRestrict_comp]
  | add a a' ha ha' => rw [map_add, map_add, map_add, ha, ha']

/-- **The ungraded realization of a graded algebra with commuting homogeneous multiplication, as
a presheaf of commutative rings**: over each object of the site its sections are the direct sum
of the homogeneous components. -/
def totalCommPresheaf
    (hcomm : ∀ (i j : ι) (U : Cᵒᵖ) (x : (P i).obj U) (y : (P j).obj U),
      HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x)) :
    Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := @CommRingCat.of _ (A.commRingTotal hcomm U)
  map f := @CommRingCat.ofHom _ _ (A.commRingTotal hcomm _) (A.commRingTotal hcomm _)
    (A.totalRestrictRingHom f)
  map_id U := CommRingCat.hom_ext (RingHom.ext fun a => A.totalRestrict_id U a)
  map_comp f g := CommRingCat.hom_ext (RingHom.ext fun a => A.totalRestrict_comp f g a)

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Q : ι → PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
  (B : GradedAlgebra Q)

/-- **The structure map `r ↦ r • 1` of the ungraded realization, as a morphism of presheaves of
commutative rings.** -/
def totalCommStructureMap
    (hcomm : ∀ (i j : ι) (U : Cᵒᵖ) (x : (Q i).obj U) (y : (Q j).obj U),
      HEq ((B.mul i j).app U x y) ((B.mul j i).app U y x)) :
    O ⟶ B.totalCommPresheaf hcomm where
  app U := @CommRingCat.ofHom _ _ _ (B.commRingTotal hcomm U) (B.structureMap U)
  naturality U V f := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    exact (B.structureMap_naturality f r).symm

end Stacks.GradedAlgebra

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))

/-- The ungraded realization of a sheaf of graded algebras with commuting homogeneous
multiplication on a scheme, as a presheaf of commutative rings. -/
def ungradedCommPresheaf : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} :=
  A.toPresheafGradedAlgebra.totalCommPresheaf hA

/-- The structure map of the ungraded realization of a sheaf of graded algebras on a scheme. -/
def ungradedCommStructureMap : X.sheaf.obj ⟶ ungradedCommPresheaf X A hA :=
  Stacks.GradedAlgebra.totalCommStructureMap (O := X.sheaf.obj) A.toPresheafGradedAlgebra hA

/-- **The ungraded realization of a sheaf of graded algebras with commuting homogeneous
multiplication on a scheme, as a sheaf of commutative `𝒪_X`-algebras**: the sheafification of
the direct sum of the homogeneous components, with the structure map `r ↦ r • 1`. -/
def ungradedAlgebraSheaf : AlgebraSheaf X :=
  Under.mk (Y := (presheafToSheaf (Opens.grothendieckTopology (X : TopCat))
      CommRingCat.{u}).obj (ungradedCommPresheaf X A hA))
    { hom := ungradedCommStructureMap X A hA ≫
        (sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
          CommRingCat.{u}).unit.app (ungradedCommPresheaf X A hA) }

/-- The sheafification unit of the ungraded realization over an open of the scheme: the map from
the direct sum of the homogeneous components to the sections of the algebra sheaf. -/
def ungradedCommUnit (U : X.Opens) :
    (ungradedCommPresheaf X A hA).obj (.op U) ⟶
      AlgebraSheaf.sections (ungradedAlgebraSheaf X A hA) U :=
  ((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
    CommRingCat.{u}).unit.app (ungradedCommPresheaf X A hA)).app (.op U)

/-- A homogeneous local section of a sheaf of graded algebras, viewed in the sections of its
ungraded algebra sheaf. -/
def ungradedAlgebraSheafIncl (n : ℤ) (U : X.Opens) (x : (A.piece n).val.obj (.op U)) :
    AlgebraSheaf.sections (ungradedAlgebraSheaf X A hA) U :=
  (ungradedCommUnit X A hA U).hom (A.toPresheafGradedAlgebra.incl n x)

/-- The product of two homogeneous local sections in the ungraded algebra sheaf is the image of
their graded product. -/
theorem ungradedAlgebraSheafIncl_mul (n m : ℤ) (U : X.Opens)
    (x : (A.piece n).val.obj (.op U)) (y : (A.piece m).val.obj (.op U)) :
    ungradedAlgebraSheafIncl X A hA n U x * ungradedAlgebraSheafIncl X A hA m U y =
      ungradedAlgebraSheafIncl X A hA (n + m) U ((A.mul n m).app (.op U) x y) := by
  refine Eq.trans ?_ (congrArg (ungradedCommUnit X A hA U).hom
    (A.toPresheafGradedAlgebra.incl_mul_incl n m x y))
  exact (map_mul (ungradedCommUnit X A hA U).hom _ _).symm

/-- The image of the graded unit in the ungraded algebra sheaf is the unit. -/
theorem ungradedAlgebraSheafIncl_one (U : X.Opens) :
    ungradedAlgebraSheafIncl X A hA 0 U (A.one.eval (.op U)) = 1 := by
  refine Eq.trans ?_ (map_one (ungradedCommUnit X A hA U).hom)
  exact congrArg (ungradedCommUnit X A hA U).hom
    (A.toPresheafGradedAlgebra.one_eq_incl (.op U)).symm

end Stacks.RelativeSpec

namespace Stacks.LineBundle

/-- A morphism of schemes together with an invertible module on its source. -/
structure Situation where
  /-- The source of the morphism, on which the invertible module lives. -/
  X : Scheme.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The structure morphism to the base. -/
  f : X ⟶ S
  /-- The invertible module. -/
  L : X.Modules
  /-- The module is invertible. -/
  [invertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

attribute [instance] Situation.invertible

variable (D : Situation.{u})

/-- **An invertible module on a scheme is quasi-coherent**, and in particular the line bundle of
a situation is. -/
instance isQuasicoherent_lineBundle : D.L.IsQuasicoherent :=
  Stacks.Divisors.isQuasicoherent_of_isInvertible D.L

/-- **The symmetric algebra `Sym(L) = ⨁_{n ≥ 0} L^{⊗ n}` of the line bundle**, as a sheaf of
graded algebras over the structure sheaf. -/
def Situation.symmetricAlgebra : SheafOfModules.GradedAlgebra.{u, u} D.X.ringCatSheaf :=
  AlgebraicGeometry.Scheme.Modules.symmetricAlgebra D.X D.L

/-- The degree-one generator `L ⟶ Sym¹(L)` of the symmetric algebra of the line bundle. -/
def Situation.symmetricAlgebraGen : D.L ⟶ D.symmetricAlgebra.piece 1 :=
  AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen D.X D.L

/-- `Sym(L)` with its degree-one generator is the symmetric algebra of `L`. -/
theorem Situation.isSymmetricAlgebra_symmetricAlgebra :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra D.symmetricAlgebra D.symmetricAlgebraGen :=
  AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra D.X D.L

/-- The negative-degree pieces of `Sym(L)` vanish. -/
theorem Situation.isZero_symmetricAlgebra_piece (n : ℤ) (hn : n < 0) :
    Limits.IsZero (D.symmetricAlgebra.piece n) :=
  AlgebraicGeometry.Scheme.Modules.isZero_symmetricAlgebra_piece D.X D.L n hn

/-- **Homogeneous multiplication in `Sym(L)` commutes**, in every pair of degrees. -/
theorem Situation.symmetricAlgebra_mul_comm (i j : ℤ) (U : (Opens D.X)ᵒᵖ)
    (x : (D.symmetricAlgebra.piece i).val.obj U) (y : (D.symmetricAlgebra.piece j).val.obj U) :
    HEq ((D.symmetricAlgebra.mul i j).app U x y) ((D.symmetricAlgebra.mul j i).app U y x) :=
  AlgebraicGeometry.Scheme.Modules.symmetricAlgebra_mul_comm D.X D.L i j U x y

/-- **The algebra sheaf of the line bundle**: the ungraded realization of `Sym(L)`, as a sheaf of
commutative `𝒪_X`-algebras. Its relative spectrum is the total space of the line bundle. -/
@[ega "II 8.9.3" "partial"]
def Situation.algebraSheaf : Stacks.RelativeSpec.AlgebraSheaf D.X :=
  Stacks.RelativeSpec.ungradedAlgebraSheaf D.X D.symmetricAlgebra D.symmetricAlgebra_mul_comm

/-- A homogeneous local section of `Sym(L)`, viewed in the sections of the algebra sheaf of the
line bundle. -/
def Situation.algebraSheafIncl (n : ℤ) (U : D.X.Opens)
    (x : (D.symmetricAlgebra.piece n).val.obj (.op U)) :
    Stacks.RelativeSpec.AlgebraSheaf.sections D.algebraSheaf U :=
  Stacks.RelativeSpec.ungradedAlgebraSheafIncl D.X D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm n U x

/-- The product of two homogeneous local sections of `Sym(L)` in the algebra sheaf of the line
bundle is the image of their graded product. -/
theorem Situation.algebraSheafIncl_mul (n m : ℤ) (U : D.X.Opens)
    (x : (D.symmetricAlgebra.piece n).val.obj (.op U))
    (y : (D.symmetricAlgebra.piece m).val.obj (.op U)) :
    D.algebraSheafIncl n U x * D.algebraSheafIncl m U y =
      D.algebraSheafIncl (n + m) U ((D.symmetricAlgebra.mul n m).app (.op U) x y) :=
  Stacks.RelativeSpec.ungradedAlgebraSheafIncl_mul D.X D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm n m U x y

/-- The image of the unit of `Sym(L)` in the algebra sheaf of the line bundle is the unit. -/
theorem Situation.algebraSheafIncl_one (U : D.X.Opens) :
    D.algebraSheafIncl 0 U (D.symmetricAlgebra.one.eval (.op U)) = 1 :=
  Stacks.RelativeSpec.ungradedAlgebraSheafIncl_one D.X D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm U

end Stacks.LineBundle
