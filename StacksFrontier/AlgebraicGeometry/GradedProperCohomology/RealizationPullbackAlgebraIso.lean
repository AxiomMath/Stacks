module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RealizationPullbackAlgebra
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization

/-!
# The algebra pullback of an ungraded realization is the realization of the degreewise pullback

Let `g : Z ⟶ X` be a morphism of schemes and `A` a sheaf of graded `𝒪_X`-algebras whose
homogeneous multiplication commutes.
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/RealizationPullbackAlgebra.lean` builds
the comparison

`realizationPullbackHom : (algebraPullback g).obj R(A) ⟶ R(g^*A)`

of sheaves of commutative `𝒪_Z`-algebras, out of the pushout exhibiting the algebra pullback as
extension of scalars, and leaves its invertibility open. **This file proves it invertible**, by
constructing a two-sided inverse.

## The inverse, and the one step that is not formal

A morphism *out of* `R(g^*A)` is `Stacks.GradedAlgebra.totalSheafLift` of a morphism of
presheaves of rings out of `totalPresheaf`, which
`Stacks.GradedAlgebra.totalRingHomOfFamily` supplies from a degreewise family of additive maps.
The family is `Stacks.RelativeSpec.RealizationPullback.pieceToPullbackAlgebra`, the adjoint
transpose of the homogeneous inclusion followed by the unit of the base-change adjunction, and
it already exists.

What it costs is **multiplicativity of that family for all local sections**. The family is
computed only on pullback-unit images (`pieceToPullbackAlgebra_pullbackUnit`), and those do not
exhaust the sections of `g^*(A_n)`: `modulePullback` is an abstract left adjoint. Both sides of
the multiplicativity equation are bilinear, so `Stacks.RingedSpace.pullbackBilinear_ext`
applies — with the left side packaged by `Stacks.RingedSpace.bilinPostcomp` out of the
pulled-back multiplication and the right side by `Stacks.BilinearMap.compLeft` and `compRight`
out of `Stacks.RelativeSpec.AlgebraSheaf.mulBilinearMap`, the multiplication of an algebra
sheaf as a bilinear map of sheaves of modules. On pullback-unit images the identity is
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit` together with
`SheafOfModules.GradedAlgebra.ungradedIncl_mul` and the multiplicativity of the unit.

Unitality is not bilinear and needs no such device, but it is not a pullback-unit statement
either: over an arbitrary open of `Z` the unit of `g^*A` is the restriction of its value over
`⊤`, which is a pullback-unit image.

## The two round trips

Each is checked on generators, and neither describes the sections of the pushout.

* `inverseCommHom_comp_realizationPullbackHom` is checked on homogeneous local sections of
  `g^*A` by `Stacks.RelativeSpec.gradedAlgebraSheaf_hom_ext`, and then — degree by degree, both
  sides being morphisms of `𝒪_Z`-modules out of `g^*(A_n)` — on pulled-back sections by
  `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection`.
* `realizationPullbackHom_right_comp_inverseCommHom` is checked on the two legs of the pushout
  square. The leg out of `𝒪_Z` is the triangle of two morphisms of algebra sheaves; the leg out
  of `g⁻¹R(A)` is transposed and then checked on homogeneous local sections of `A`, again by
  `gradedAlgebraSheaf_hom_ext`.

The computation both round trips rest on is `unit_right_comp_map_realizationPullbackHom`: the
unit of the base-change adjunction followed by the direct image of the forward comparison is
the transposed comparison `toPushforwardRealization` the comparison was descended from. That is
`CategoryTheory.Adjunction.homEquiv_unit` together with
`Stacks.AffineAlgebraEquivalence.homEquiv_right` and `IsPushout.inl_desc`.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.mulBilinearMap`: the multiplication of a sheaf of
  commutative `𝒪_X`-algebras as an `𝒪_X`-bilinear map of sheaves of modules.
* `Stacks.RelativeSpec.RealizationPullback.realizationPullbackInv`: **the inverse
  comparison** `R(g^*A) ⟶ (algebraPullback g).obj R(A)`.
* `Stacks.RelativeSpec.RealizationPullback.realizationPullbackIso`: **the comparison as an
  isomorphism.**

## Main results

* `Stacks.RelativeSpec.gradedAlgebraSheaf_hom_ext`: two morphisms of sheaves of commutative
  rings out of an ungraded realization which agree on homogeneous local sections are equal.
* `Stacks.RelativeSpec.RealizationPullback.pieceToPullbackAlgebra_mul` and
  `pieceToPullbackAlgebra_one`: **the degreewise family is multiplicative on all local sections
  and carries the graded unit to the unit.**
* `Stacks.RelativeSpec.RealizationPullback.isIso_realizationPullbackHom`: **the comparison is
  invertible.**

## Implementation notes

**No `@[stacks]` attribute is attached here.** [Stacks, Tag 01LX] part (2) is proved in full
generality for a quasi-coherent algebra sheaf as
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`, and no clause of 01LX mentions a
grading; what this file supplies is the plumbing between that statement and the graded input of
[Stacks, Tag 0897], exactly as recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Constructions/UngradedRealizationPullback.lean`.

**The proofs are in term mode, and not by choice.** A goal mentioning the sections of an
algebra sheaf is not type-correct under `implicit` transparency — `AlgebraicGeometry.Scheme.sheaf`
is spelled `TopCat.Sheaf CommRingCat ↑Z.toPresheafedSpace` while `CategoryTheory.sheafCompose`
expects `CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat` — so `rw` cannot
build a motive on such a goal at all; a `rw` proof of
`pieceToPullbackAlgebra_mul` fails in exactly that way. `Eq.trans`, `congrArg` and `exact`
check at default transparency and cross it.

For the same reason the scalar of a module is taken at the `X.ringCatSheaf` spelling and not at
the `Scheme.sheaf` one: `inverseUngradedHom_structureMap` is stated with
`r : Z.ringCatSheaf.obj.obj (op V)` because at the `Z.sheaf` spelling the `SMul` instance on
the sections of the underlying module is not found at all.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-- The multiplication of an algebra sheaf as an `𝒪_X`-bilinear map of sheaves of modules. -/
def mulBilinearMap (B : AlgebraSheaf X) :
    SheafOfModules.BilinearMap (underlyingModule B) (underlyingModule B)
      (underlyingModule B) where
  app W := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => mulSection B W x y)
      (fun y y' => mulSection_add_right B W x y y'))
    (fun x x' => AddMonoidHom.ext fun y => mulSection_add_left B W x x' y)
  map_smul_left W _ x y := mulSection_mul_left B W _ x y
  map_smul_right W _ x y := mulSection_mul_right B W _ x y
  naturality f x y := mulSection_naturality B f x y

/-- The bilinear map `mulBilinearMap B` sends sections `x` and `y` over `W` to their product
`mulSection B W x y`. -/
@[simp] theorem mulBilinearMap_app (B : AlgebraSheaf X) (W : (Opens ↥X)ᵒᵖ)
    (x y : B.right.obj.obj W) : (mulBilinearMap B).app W x y = mulSection B W x y := rfl

end Stacks.RelativeSpec.AlgebraSheaf

namespace Stacks.RelativeSpec

/-- **Two morphisms of sheaves of commutative rings out of the ungraded realization of a sheaf
of graded algebras which agree on homogeneous local sections are equal.**

The realization is a sheafification, so a morphism out of it is determined by its composite
with the sheafification unit (`Stacks.GradedAlgebra.totalSheaf_hom_ext`), and the sections of
the presheaf being sheafified are finite sums of homogeneous ones. -/
theorem gradedAlgebraSheaf_hom_ext {X : Scheme.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology (X : TopCat)) CommRingCat.{u}}
    {u v : (gradedAlgebraSheaf X A hc).right ⟶ O}
    (h : ∀ (n : ℤ) (W : (Opens ↥X)ᵒᵖ) (x : (A.piece n).val.obj W),
      (u.hom.app W).hom (A.ungradedIncl n x) = (v.hom.app W).hom (A.ungradedIncl n x)) :
    u = v := by
  have key : (sheafCompose (Opens.grothendieckTopology (X : TopCat))
        (forget₂ CommRingCat.{u} RingCat.{u})).map u =
      (sheafCompose (Opens.grothendieckTopology (X : TopCat))
        (forget₂ CommRingCat.{u} RingCat.{u})).map v := by
    refine Stacks.GradedAlgebra.totalSheaf_hom_ext A.toPresheafGradedAlgebra
      (Opens.grothendieckTopology (X : TopCat)) ?_
    refine NatTrans.ext (funext fun W => RingCat.hom_ext (RingHom.ext fun a => ?_))
    induction a using A.toPresheafGradedAlgebra.incl_induction with
    | zero => exact Eq.trans (map_zero _) (map_zero _).symm
    | incl n x => exact h n W x
    | add a b ha hb =>
      exact Eq.trans (map_add _ a b)
        (Eq.trans (congrArg₂ (fun p q => p + q) ha hb) (map_add _ a b).symm)
  exact Stacks.CommRingSheaf.sheaf_hom_ext (A.mul_comm_ungradedSheaf hc)
    fun W y => congrArg (fun φ => RingCat.Hom.hom (φ.hom.app W) y) key

end Stacks.RelativeSpec

namespace Stacks.RelativeSpec.RealizationPullback

variable {Z X : Scheme.{u}} (g : Z ⟶ X) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
    (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

/-- `pieceToPullbackAlgebra` on a pullback-unit image, written with the homogeneous inclusion
spelled out. -/
theorem pieceToPullbackAlgebra_pullbackUnit_pieceIncl (n : ℤ) (U : X.Opens)
    (x : (A.piece n).val.obj (op U)) :
    (pieceToPullbackAlgebra g A hc n).val.app (op (g ⁻¹ᵁ U))
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece n) (op U) x) =
      (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app
          (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))).val.app (op U)
        (A.ungradedIncl n x) :=
  pieceToPullbackAlgebra_pullbackUnit g A hc n U x

/-- **Multiplicativity of the degreewise family on all local sections.** -/
theorem pieceToPullbackAlgebra_mul (i j : ℤ) (V : Opens ↥Z)
    (x : ((Stacks.Conormal.gradedPullback g A).piece i).val.obj (op V))
    (y : ((Stacks.Conormal.gradedPullback g A).piece j).val.obj (op V)) :
    (pieceToPullbackAlgebra g A hc (i + j)).val.app (op V)
        (((Stacks.Conormal.gradedPullback g A).mul i j).app (op V) x y) =
      Stacks.RelativeSpec.AlgebraSheaf.mulSection
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (op V)
        ((pieceToPullbackAlgebra g A hc i).val.app (op V) x)
        ((pieceToPullbackAlgebra g A hc j).val.app (op V) y) := by
  refine Stacks.RingedSpace.pullbackBilinear_ext g.toLRSHom.toShHom
    (Stacks.RingedSpace.bilinPostcomp ((Stacks.Conormal.gradedPullback g A).mul i j)
      (pieceToPullbackAlgebra g A hc (i + j)))
    (((Stacks.RelativeSpec.AlgebraSheaf.mulBilinearMap
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))).compLeft
      (pieceToPullbackAlgebra g A hc i).val).compRight
      (pieceToPullbackAlgebra g A hc j).val) (fun W a b => ?_) V x y
  change (pieceToPullbackAlgebra g A hc (i + j)).val.app (op (g ⁻¹ᵁ W))
      (((Stacks.RingedSpace.pullbackGradedAlgebra g.toLRSHom.toShHom A).mul i j).app
        (op (g ⁻¹ᵁ W))
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece i) (op W) a)
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece j) (op W) b)) =
    Stacks.RelativeSpec.AlgebraSheaf.mulSection
      ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (op (g ⁻¹ᵁ W))
      ((pieceToPullbackAlgebra g A hc i).val.app (op (g ⁻¹ᵁ W))
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece i) (op W) a))
      ((pieceToPullbackAlgebra g A hc j).val.app (op (g ⁻¹ᵁ W))
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece j) (op W) b))
  refine Eq.trans (congrArg (fun z => (pieceToPullbackAlgebra g A hc (i + j)).val.app
      (op (g ⁻¹ᵁ W)) z)
    (Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit
      g.toLRSHom.toShHom A i j W a b)) ?_
  refine Eq.trans (pieceToPullbackAlgebra_pullbackUnit_pieceIncl g A hc (i + j) W _) ?_
  refine Eq.trans (congrArg (fun z => (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
      ((algebraPullbackPushforwardAdjunction g).unit.app
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))).val.app (op W) z)
    (A.ungradedIncl_mul i j a b).symm) ?_
  refine Eq.trans (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap_mulSection
    ((algebraPullbackPushforwardAdjunction g).unit.app
      (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (op W)
    (A.ungradedIncl i a) (A.ungradedIncl j b)) ?_
  exact congrArg₂ (fun p q => Stacks.RelativeSpec.AlgebraSheaf.mulSection
      ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))
      (op (g ⁻¹ᵁ W)) p q)
    (pieceToPullbackAlgebra_pullbackUnit_pieceIncl g A hc i W a).symm
    (pieceToPullbackAlgebra_pullbackUnit_pieceIncl g A hc j W b).symm

/-- **The degreewise family carries the graded unit to the unit.** Over an arbitrary open of
`Z` the unit of `g^*A` is not a pullback-unit image; it is the restriction of its value over
`⊤`, which is one, and both the family and the unit commute with restriction. -/
theorem pieceToPullbackAlgebra_one (V : Opens ↥Z) :
    (pieceToPullbackAlgebra g A hc 0).val.app (op V)
        ((Stacks.Conormal.gradedPullback g A).one.eval (op V)) =
      Stacks.RelativeSpec.AlgebraSheaf.oneSection
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (op V) := by
  have hres : (Stacks.Conormal.gradedPullback g A).one.eval (op V) =
      ((Stacks.Conormal.gradedPullback g A).piece 0).val.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Stacks.Conormal.gradedPullback g A).one.eval (op ⊤)) :=
    (PresheafOfModules.sections_property (Stacks.Conormal.gradedPullback g A).one
      (homOfLE (le_top : V ≤ ⊤)).op).symm
  have htop : (pieceToPullbackAlgebra g A hc 0).val.app (op (⊤ : Opens ↥Z))
        ((Stacks.Conormal.gradedPullback g A).one.eval (op ⊤)) =
      Stacks.RelativeSpec.AlgebraSheaf.oneSection
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (op ⊤) := by
    refine Eq.trans (congrArg (fun z => (pieceToPullbackAlgebra g A hc 0).val.app
        (op (⊤ : Opens ↥Z)) z)
      (Stacks.RingedSpace.pullbackGradedAlgebra_one_eval g.toLRSHom.toShHom A ⊤)) ?_
    refine Eq.trans (pieceToPullbackAlgebra_pullbackUnit_pieceIncl g A hc 0 ⊤ _) ?_
    refine Eq.trans (congrArg (fun z => (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app
          (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))).val.app (op (⊤ : Opens ↥X)) z)
      (A.ungradedIncl_one (op ⊤))) ?_
    exact Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap_oneSection
      ((algebraPullbackPushforwardAdjunction g).unit.app
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (op ⊤)
  refine Eq.trans (congrArg (fun z => (pieceToPullbackAlgebra g A hc 0).val.app (op V) z)
    hres) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply (pieceToPullbackAlgebra g A hc 0).val
    (homOfLE (le_top : V ≤ ⊤)).op ((Stacks.Conormal.gradedPullback g A).one.eval (op ⊤))) ?_
  refine Eq.trans (congrArg (fun z => (Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
      ((algebraPullback g).obj
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))).val.map
    (homOfLE (le_top : V ≤ ⊤)).op z) htop) ?_
  exact map_one (((algebraPullback g).obj
    (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right.obj.map
      (homOfLE (le_top : V ≤ ⊤)).op).hom

/-! ### The inverse comparison -/

/-- `g^*A` read as a graded algebra of presheaves of modules, named once: the ungraded
realization is taken of that reading, and the spelling occurs in every statement below. -/
abbrev pullbackPresheafAlgebra :
    Stacks.GradedAlgebra fun i : ℤ => ((Stacks.Conormal.gradedPullback g A).piece i).val :=
  (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra

/-- The degreewise family, read as an additive map into the sections of the algebra pullback
over an open of `Z`. -/
def pieceAddHom (n : ℤ) (V : Opens ↥Z) :
    ((Stacks.Conormal.gradedPullback g A).piece n).val.obj (op V) →+
      ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right.obj.obj
        (op V) where
  toFun x := (pieceToPullbackAlgebra g A hc n).val.app (op V) x
  map_zero' := map_zero ((pieceToPullbackAlgebra g A hc n).val.app (op V)).hom
  map_add' := map_add ((pieceToPullbackAlgebra g A hc n).val.app (op V)).hom

/-- **The sections of the algebra pullback of the realization of `A`, as a ring under the
sections of the direct sum of the homogeneous pieces of `g^*A`.** The multiplicativity is
`pieceToPullbackAlgebra_mul` and the unit is `pieceToPullbackAlgebra_one`. -/
def totalToPullbackAlgebra (V : Opens ↥Z) :
    (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.Total (op V) →+*
      ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right.obj.obj
        (op V) :=
  (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.totalRingHomOfFamily (op V)
    (pieceAddHom g A hc · V) (fun i j x y => pieceToPullbackAlgebra_mul g A hc i j V x y)
    (pieceToPullbackAlgebra_one g A hc V)

/-- `totalToPullbackAlgebra` on a homogeneous section is the degreewise family. -/
theorem totalToPullbackAlgebra_incl (n : ℤ) (V : Opens ↥Z)
    (x : ((Stacks.Conormal.gradedPullback g A).piece n).val.obj (op V)) :
    totalToPullbackAlgebra g A hc V
        ((Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.incl n x) =
      (pieceToPullbackAlgebra g A hc n).val.app (op V) x :=
  (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.totalRingHomOfFamily_incl
    _ _ _ _ n x

/-- The inverse comparison as a morphism of presheaves of rings out of the direct sum of the
homogeneous pieces of `g^*A`. -/
def inverseRealizationPresheafHom :
    (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.totalPresheaf ⟶
      (Stacks.RelativeSpec.AlgebraSheaf.ringSheaf
        ((algebraPullback g).obj
          (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))).obj where
  app W := RingCat.ofHom (totalToPullbackAlgebra g A hc W.unop)
  naturality W₁ W₂ α := by
    obtain ⟨V₁⟩ := W₁
    obtain ⟨V₂⟩ := W₂
    refine RingCat.hom_ext (RingHom.ext fun a => ?_)
    change totalToPullbackAlgebra g A hc V₂
        ((Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.totalRestrict α a) =
      (((algebraPullback g).obj
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right.obj.map α).hom
        (totalToPullbackAlgebra g A hc V₁ a)
    induction a using
      (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.incl_induction with
    | zero =>
      refine Eq.trans (congrArg (totalToPullbackAlgebra g A hc V₂)
        (map_zero ((pullbackPresheafAlgebra g A).totalRestrict α))) ?_
      refine Eq.trans (map_zero (totalToPullbackAlgebra g A hc V₂)) ?_
      refine Eq.trans (map_zero ((((algebraPullback g).obj
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right.obj.map α).hom)).symm ?_
      exact congrArg ((((algebraPullback g).obj
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right.obj.map α).hom)
        (map_zero (totalToPullbackAlgebra g A hc V₁)).symm
    | incl n x =>
      refine Eq.trans (congrArg (totalToPullbackAlgebra g A hc V₂)
        ((Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.totalRestrict_incl
          α n x)) ?_
      refine Eq.trans (totalToPullbackAlgebra_incl g A hc n V₂ _) ?_
      refine Eq.trans (PresheafOfModules.naturality_apply
        (pieceToPullbackAlgebra g A hc n).val α x) ?_
      exact congrArg ((((algebraPullback g).obj
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right.obj.map α).hom)
        (totalToPullbackAlgebra_incl g A hc n V₁ x).symm
    | add a b ha hb =>
      rw [map_add, map_add, map_add, ha, hb]
      exact (map_add _ _ _).symm

/-- The inverse comparison as a morphism of sheaves of rings: `inverseRealizationPresheafHom`
extended across the sheafification. -/
def inverseUngradedHom :
    (Stacks.Conormal.gradedPullback g A).ungradedSheaf ⟶
      Stacks.RelativeSpec.AlgebraSheaf.ringSheaf
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) :=
  (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.totalSheafLift
    (Opens.grothendieckTopology (Z : TopCat)) _ (inverseRealizationPresheafHom g A hc)

/-- The morphism of sheaves of rings is `totalToPullbackAlgebra` on the sheafification unit. -/
theorem inverseUngradedHom_totalUnit (V : Opens ↥Z)
    (a : (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.Total (op V)) :
    ((inverseUngradedHom g A hc).hom.app (op V)).hom
        ((Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.totalUnit
          (Opens.grothendieckTopology (Z : TopCat)) (op V) a) =
      totalToPullbackAlgebra g A hc V a := by
  have h := Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift
    (pullbackPresheafAlgebra g A) (Opens.grothendieckTopology (Z : TopCat))
    (Stacks.RelativeSpec.AlgebraSheaf.ringSheaf ((algebraPullback g).obj
      (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)))
    (inverseRealizationPresheafHom g A hc)
  exact congrArg (fun φ => RingCat.Hom.hom (NatTrans.app φ (op V)) a) h

/-- The inverse comparison on a homogeneous local section of `g^*A` is the degreewise
family. -/
theorem inverseUngradedHom_ungradedIncl (n : ℤ) (V : Opens ↥Z)
    (x : ((Stacks.Conormal.gradedPullback g A).piece n).val.obj (op V)) :
    ((inverseUngradedHom g A hc).hom.app (op V)).hom
        ((Stacks.Conormal.gradedPullback g A).ungradedIncl n x) =
      (pieceToPullbackAlgebra g A hc n).val.app (op V) x :=
  Eq.trans (inverseUngradedHom_totalUnit g A hc V _)
    (totalToPullbackAlgebra_incl g A hc n V x)

/-- **The inverse comparison as a morphism of sheaves of commutative rings**: the lift
`inverseUngradedHom` read in `CommRingCat`. -/
def inverseCommHom :
    (pullbackRealization g A hc).right ⟶
      ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right :=
  Stacks.CommRingSheaf.homMk' _
    ((Stacks.Conormal.gradedPullback g A).mul_comm_ungradedSheaf
      (Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom A hc))
    (inverseUngradedHom g A hc)

/-- **The inverse comparison is compatible with the two structure morphisms.** A section of
`𝒪_Z` enters the realization of `g^*A` as that scalar times the graded unit, and the
degreewise family carries the graded unit to the unit. -/
theorem inverseUngradedHom_structureMap (V : Opens ↥Z)
    (r : Z.ringCatSheaf.obj.obj (op V)) :
    ((inverseUngradedHom g A hc).hom.app (op V)).hom
        (((Stacks.Conormal.gradedPullback g A).ungradedStructureMap.hom.app (op V)).hom r) =
      Stacks.RelativeSpec.AlgebraSheaf.structSection
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (op V) r := by
  refine Eq.trans (congrArg (fun y => ((inverseUngradedHom g A hc).hom.app (op V)).hom y)
    ((Stacks.Conormal.gradedPullback g A).ungradedIncl_smul_one (op V) r).symm) ?_
  refine Eq.trans (inverseUngradedHom_ungradedIncl g A hc 0 V _) ?_
  refine Eq.trans (map_smul ((pieceToPullbackAlgebra g A hc 0).val.app (op V)).hom r _) ?_
  refine Eq.trans (congrArg (fun y => r • y) (pieceToPullbackAlgebra_one g A hc V)) ?_
  exact (Stacks.RelativeSpec.AlgebraSheaf.structSection_eq_smul_oneSection
    ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (op V) r).symm

/-- The inverse comparison `inverseCommHom` composed after the structure morphism of the
realization of `g^*A` is the structure morphism of the algebra pullback. -/
theorem structureMap_comp_inverseCommHom :
    (pullbackRealization g A hc).hom ≫ inverseCommHom g A hc =
      ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).hom := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => CommRingCat.hom_ext
    (RingHom.ext fun r => ?_)))
  obtain ⟨V⟩ := W
  exact inverseUngradedHom_structureMap g A hc V r

/-- **The inverse comparison**, as a morphism of sheaves of commutative `𝒪_Z`-algebras from the
ungraded realization of `g^*A` to the algebra pullback of the ungraded realization of `A`. -/
def realizationPullbackInv :
    pullbackRealization g A hc ⟶
      (algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc) :=
  Under.homMk (inverseCommHom g A hc) (structureMap_comp_inverseCommHom g A hc)

/-! ### The two round trips -/

/-- **The transpose of the forward comparison is the transposed comparison it was built
from.** Composing the unit of the base-change adjunction with the direct image of
`realizationPullbackHom` undoes the `IsPushout.desc`. -/
theorem unit_right_comp_map_realizationPullbackHom :
    ((algebraPullbackPushforwardAdjunction g).unit.app
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
        (realizationPullbackHom g A hc).right =
    toPushforwardRealization g A hc := by
  have h1 : (algebraPullbackPushforwardAdjunction g).unit.app
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc) ≫
      (algebraPushforward g).map (realizationPullbackHom g A hc) =
      (algebraPullbackPushforwardAdjunction g).homEquiv _ _
        (realizationPullbackHom g A hc) :=
    (Adjunction.homEquiv_unit (algebraPullbackPushforwardAdjunction g) _ _ _).symm
  refine Eq.trans (congrArg (fun k : Stacks.RelativeSpec.gradedAlgebraSheaf X A hc ⟶
      (algebraPushforward g).obj (pullbackRealization g A hc) => k.right) h1) ?_
  refine Eq.trans (homEquiv_right g (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)
    (pullbackRealization g A hc) (realizationPullbackHom g A hc)) ?_
  refine Eq.trans (congrArg
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
      (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right
      (pullbackRealization g A hc).right)
    ((algebraPullback_isPushout g (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).inl_desc
      (inverseImageToRealization g A hc) (pullbackRealization g A hc).hom
      (algebraPullback_square g A hc))) ?_
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
    (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right
    (pullbackRealization g A hc).right).apply_symm_apply _

/-- The forward ring map out of the realization of `A`, on a homogeneous local section, is the
pullback-unit image read in the realization of `g^*A`. -/
private theorem ungradedRealizationHom_ungradedIncl (n : ℤ) (U : X.Opens)
    (x : (A.piece n).val.obj (op U)) :
    ((ungradedRealizationHom g A hc).hom.app (op U)).hom (A.ungradedIncl n x) =
      (Stacks.Conormal.gradedPullback g A).ungradedIncl n
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece n) (op U) x) :=
  Eq.trans (ungradedRealizationHom_totalUnit g A hc U (A.toPresheafGradedAlgebra.incl n x))
    (totalToRealization_incl g A n U x)

/-- **The degreewise family followed by the forward comparison is the homogeneous inclusion.**
Both sides are morphisms of `𝒪_Z`-modules out of `g^*(A_n)`, so they agree as soon as they
agree on pulled-back sections, where the left one is computed by
`pieceToPullbackAlgebra_pullbackUnit_pieceIncl` together with
`unit_right_comp_map_realizationPullbackHom` and the right one by
`pieceInclUnderlyingModule_app`. -/
theorem pieceToPullbackAlgebra_comp_underlyingModuleMap (n : ℤ) :
    pieceToPullbackAlgebra g A hc n ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        (realizationPullbackHom g A hc) =
      pieceInclUnderlyingModule (Stacks.Conormal.gradedPullback g A)
        (Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom A hc) n := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection g fun U a => ?_
  refine Eq.trans (congrArg (fun z => (pieceToPullbackAlgebra g A hc n ≫
      Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        (realizationPullbackHom g A hc)).val.app (op (g ⁻¹ᵁ U)) z)
    (Stacks.Conormal.pullbackSection_self g (A.piece n) U a)) ?_
  refine Eq.trans (Eq.trans (congrArg (fun z => ((realizationPullbackHom g A hc).right.hom.app
      (op (g ⁻¹ᵁ U))).hom z) (pieceToPullbackAlgebra_pullbackUnit_pieceIncl g A hc n U a))
    (congrArg (fun φ : (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj
          (pullbackRealization g A hc).right =>
      (φ.hom.app (op U)).hom (A.ungradedIncl n a))
      (unit_right_comp_map_realizationPullbackHom g A hc))) ?_
  refine Eq.trans (ungradedRealizationHom_ungradedIncl g A hc n U a) ?_
  exact (congrArg (fun z => (pieceInclUnderlyingModule (Stacks.Conormal.gradedPullback g A)
      (Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom A hc) n).val.app
        (op (g ⁻¹ᵁ U)) z)
    (Stacks.Conormal.pullbackSection_self g (A.piece n) U a)).symm

/-- **The inverse comparison followed by the forward comparison is the identity** of the
realization of `g^*A`. -/
theorem inverseCommHom_comp_realizationPullbackHom :
    inverseCommHom g A hc ≫ (realizationPullbackHom g A hc).right =
      𝟙 (pullbackRealization g A hc).right := by
  refine Stacks.RelativeSpec.gradedAlgebraSheaf_hom_ext (Stacks.Conormal.gradedPullback g A)
    (Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom A hc) fun n W x => ?_
  obtain ⟨V⟩ := W
  refine Eq.trans (congrArg (fun z => ((realizationPullbackHom g A hc).right.hom.app
      (op V)).hom z) (inverseUngradedHom_ungradedIncl g A hc n V x)) ?_
  exact congrArg (fun φ : (Stacks.Conormal.gradedPullback g A).piece n ⟶
      Stacks.RelativeSpec.AlgebraSheaf.underlyingModule (pullbackRealization g A hc) =>
    φ.val.app (op V) x) (pieceToPullbackAlgebra_comp_underlyingModuleMap g A hc n)

/-- **The transposed comparison followed by the direct image of the inverse comparison is the
unit of the base-change adjunction.** Both sides are morphisms out of the realization of `A`,
so they agree as soon as they agree on homogeneous local sections. -/
theorem toPushforwardRealization_comp_map_inverseCommHom :
    toPushforwardRealization g A hc ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map (inverseCommHom g A hc) =
      ((algebraPullbackPushforwardAdjunction g).unit.app
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right := by
  refine Stacks.RelativeSpec.gradedAlgebraSheaf_hom_ext A hc fun n W x => ?_
  obtain ⟨U⟩ := W
  refine Eq.trans (congrArg (fun z => ((inverseCommHom g A hc).hom.app (op (g ⁻¹ᵁ U))).hom z)
    (ungradedRealizationHom_ungradedIncl g A hc n U x)) ?_
  refine Eq.trans (inverseUngradedHom_ungradedIncl g A hc n (g ⁻¹ᵁ U) _) ?_
  exact pieceToPullbackAlgebra_pullbackUnit_pieceIncl g A hc n U x

/-- The unit of the base-change adjunction, read on underlying sheaves of rings, is the
adjoint transpose of the canonical map `g⁻¹R(A) ⟶ g⁻¹R(A) ⊗_{g⁻¹𝒪_X} 𝒪_Z`. -/
theorem unit_right_eq_homEquiv_algebraPullbackMap :
    ((algebraPullbackPushforwardAdjunction g).unit.app
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right
        ((algebraPullbackMap g).app (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) := by
  have h0 : (algebraPullbackPushforwardAdjunction g).homEquiv
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (𝟙 _) =
      (algebraPullbackPushforwardAdjunction g).unit.app
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc) :=
    Eq.trans (Adjunction.homEquiv_unit (algebraPullbackPushforwardAdjunction g) _ _ (𝟙 _))
      (Eq.trans (congrArg (fun k => (algebraPullbackPushforwardAdjunction g).unit.app
          (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc) ≫ k)
        ((algebraPushforward g).map_id _)) (Category.comp_id _))
  refine Eq.trans (congrArg (fun k : Stacks.RelativeSpec.gradedAlgebraSheaf X A hc ⟶
      (algebraPushforward g).obj ((algebraPullback g).obj
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) => k.right) h0.symm) ?_
  refine Eq.trans (homEquiv_right g (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)
    ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) (𝟙 _)) ?_
  exact congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
    (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right
    ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right)
    (Category.comp_id _)

/-- The leg of the pushout square out of `g⁻¹R(A)`, followed by the inverse comparison, is the
canonical map into the pushout. -/
theorem inverseImageToRealization_comp_inverseCommHom :
    inverseImageToRealization g A hc ≫ inverseCommHom g A hc =
      (algebraPullbackMap g).app (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc) := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
    (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right
    ((algebraPullback g).obj
      (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right).injective ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_right _ _ _) ?_
  refine Eq.trans (congrArg (fun k => k ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
      (inverseCommHom g A hc))
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
      (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right
      (pullbackRealization g A hc).right).apply_symm_apply
        (toPushforwardRealization g A hc))) ?_
  exact Eq.trans (toPushforwardRealization_comp_map_inverseCommHom g A hc)
    (unit_right_eq_homEquiv_algebraPullbackMap g A hc)

/-- **The forward comparison followed by the inverse comparison is the identity** of the
algebra pullback. Both legs of the pushout square are checked: the one out of `g⁻¹R(A)` is
`inverseImageToRealization_comp_inverseCommHom` and the one out of `𝒪_Z` is the triangle of
the two algebra-sheaf morphisms. -/
theorem realizationPullbackHom_right_comp_inverseCommHom :
    (realizationPullbackHom g A hc).right ≫ inverseCommHom g A hc =
      𝟙 ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).right := by
  refine (algebraPullback_isPushout g
    (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).hom_ext ?_ ?_
  · refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans ?_ (Category.comp_id _).symm)
    refine Eq.trans (congrArg (fun k => k ≫ inverseCommHom g A hc)
      ((algebraPullback_isPushout g (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).inl_desc
        (inverseImageToRealization g A hc) (pullbackRealization g A hc).hom
        (algebraPullback_square g A hc))) ?_
    exact inverseImageToRealization_comp_inverseCommHom g A hc
  · refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans ?_ (Category.comp_id _).symm)
    refine Eq.trans (congrArg (fun k => k ≫ inverseCommHom g A hc)
      (Under.w (realizationPullbackHom g A hc))) ?_
    exact structureMap_comp_inverseCommHom g A hc

/-- **The comparison of the algebra pullback of the ungraded realization of `A` with the
ungraded realization of the degreewise pullback `g^*A` is an isomorphism of sheaves of
commutative `𝒪_Z`-algebras.**

`Stacks.RelativeSpec.RealizationPullback.realizationPullbackInv` is a two-sided inverse of the
underlying morphism of sheaves of commutative rings, and `CategoryTheory.Under.forget` reflects
isomorphisms. -/
theorem isIso_realizationPullbackHom : IsIso (realizationPullbackHom g A hc) := by
  have hright : IsIso ((Under.forget Z.sheaf).map (realizationPullbackHom g A hc)) :=
    ⟨inverseCommHom g A hc, realizationPullbackHom_right_comp_inverseCommHom g A hc,
      inverseCommHom_comp_realizationPullbackHom g A hc⟩
  exact isIso_of_reflects_iso (realizationPullbackHom g A hc) (Under.forget Z.sheaf)

/-- **The algebra pullback of the ungraded realization of `A` is the ungraded realization of
the degreewise pullback `g^*A`**, as sheaves of commutative `𝒪_Z`-algebras. -/
def realizationPullbackIso :
    (algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc) ≅
      pullbackRealization g A hc :=
  haveI := isIso_realizationPullbackHom g A hc
  asIso (realizationPullbackHom g A hc)

end Stacks.RelativeSpec.RealizationPullback

end
