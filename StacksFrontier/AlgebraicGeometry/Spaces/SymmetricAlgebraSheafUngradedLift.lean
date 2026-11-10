module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafMap

/-!
# The ungraded universal property of the symmetric algebra of a module sheaf on an algebraic space

`AlgebraicGeometry.Space.symmetricAlgebraSheaf` sends a sheaf of modules `ℱ` on the small étale
site of an algebraic space `W` to the sheaf of commutative `𝒪_W`-algebras `Sym(ℱ)`.  The
universal property available for it, `AlgebraicGeometry.Space.isSymmetricAlgebra_symmetricAlgebra`,
produces a homomorphism of *graded* algebras out of a degree-one generator with pairwise
commuting image.  **This file produces instead a morphism of algebra sheaves `Sym(ℱ) ⟶ 𝒜` out of
a morphism of module sheaves `ℱ ⟶ 𝒜`, for `𝒜` an algebra sheaf carrying no grading at all** —
the form in which Stacks 082A and Stacks 086Z use it, and the algebraic-space analogue of
`Stacks.SymAlgSheaf.algebraLift`.

## Main definitions

* `AlgebraicGeometry.Space.SymAlgSheaf.constGraded`: **an algebra sheaf on an algebraic space,
  read as a sheaf of graded algebras with every homogeneous piece the whole algebra.**
* `AlgebraicGeometry.Space.SymAlgSheaf.descHom`: the degreewise comparison `Symⁿ(ℱ) ⟶ 𝒜`
  extending a morphism of module sheaves, from the graded universal property at `constGraded`.
* `AlgebraicGeometry.Space.SymAlgSheaf.psiTotal` and `psiPresheafHom`: the comparison out of the
  ungraded realization, on sections and as a morphism of presheaves of rings.
* `AlgebraicGeometry.Space.SymAlgSheaf.ungradedLift` and `commLift`: that comparison descended
  across the sheafification, as a morphism of sheaves of rings and of sheaves of commutative
  rings.
* `AlgebraicGeometry.Space.SymAlgSheaf.algebraLift`: **the morphism of algebra sheaves
  `Sym(ℱ) ⟶ 𝒜` extending a morphism of module sheaves `ℱ ⟶ 𝒜`.**

## Main results

* `AlgebraicGeometry.Space.SymAlgSheaf.psiTotal_mul`, `psiTotal_one` and `psiTotal_naturality`:
  the comparison on sections of the ungraded realization is a homomorphism of presheaves of
  rings.
* `AlgebraicGeometry.Space.SymAlgSheaf.psiTotal_structureMap`: it carries the structure map
  `r ↦ r • 1` of the ungraded realization to the structure-algebra map of `𝒜`, which is what
  makes the lift a morphism of *algebra* sheaves.
* `AlgebraicGeometry.Space.SymAlgSheaf.algebraLift_ungradedIncl_gen`: **the lift restricts to the
  given morphism in degree one.**  This is its defining property.

## Implementation notes

### Why every piece is the whole algebra

`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra` quantifies over sheaves of *graded* algebras
and produces a `SheafOfModules.GradedAlgebra.UnitalHom` of degreewise maps.  An arbitrary algebra
sheaf is not one, and the obvious repair — presenting it as a graded algebra concentrated in
degree zero — destroys the statement, since it forces the degree-one generator to land in the
zero module and so kills the very morphism being extended.

What works is the **opposite** degenerate grading:
`AlgebraicGeometry.Space.SymAlgSheaf.constGraded` has `piece n = 𝒜.underlyingModule` for *every*
`n`, with the ring multiplication of `𝒜` as the homogeneous multiplication in every pair of
degrees.  Nothing in `SheafOfModules.GradedAlgebra` requires the pieces to be distinct or the
grading to be faithful — its data are a bilinear multiplication `piece i × piece j ⟶ piece (i+j)`,
a unit in degree zero, associativity and the two unit laws — and all of them are the `CommRing`
axioms of the sections.  A `UnitalHom (Sym ℱ) (constGraded 𝒜)` is then exactly a multiplicative,
unital family `Symⁿ(ℱ) ⟶ 𝒜`, which is the ungraded data wanted, and `PairwiseCommutes` of the
given morphism is commutativity of `𝒜`.  Because every piece is the same object, the three `HEq`
laws of `SheafOfModules.GradedAlgebra` have both sides in the same type and are discharged by
`heq_of_eq`; no transport appears below.

This is the argument of the scheme-level `Stacks.SymAlgSheaf.algebraLift`, transported.
Everything it uses —
`SheafOfModules.GradedAlgebra`, `UnitalHom`, `PairwiseCommutes`, `IsUniversal.desc`,
`Stacks.GradedAlgebra.Total` with `incl`, `incl_mul_incl`, `incl_induction`, `totalPresheaf`,
`structureMap`, `totalSheaf` and `totalSheafLift` — is stated for a site `C : Type u₁` with
`Category.{v₁} C` for independent `u₁` and `v₁`, so it applies to the small étale site
`AlgebraicGeometry.Space.SmallEtale B S hS F : Type (u + 1)` with morphisms in `Type u` with no
restatement; that is why no universe-general restatements appear here, unlike in
`StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafMap`.  The one place the two levels
differ is the last step: at the scheme level an algebra sheaf is an object of
`CategoryTheory.Under`, so the lift ends with `CategoryTheory.Under.homMk`, whereas
`AlgebraicGeometry.Space.AlgebraSheaf` is a bespoke structure and the lift ends with its `right`
and `comm` fields, `comm` being `AlgebraicGeometry.Space.SymAlgSheaf.psiTotal_structureMap`.

### What is not claimed

**Uniqueness.**  The lift is not claimed unique.  Uniqueness of an ungraded extension needs
`Sym(ℱ)` to be generated in degree one on the sections over each object of the site, which is
false for a general étale chart, so what is proved is existence together with the degree-one
equation `AlgebraicGeometry.Space.SymAlgSheaf.algebraLift_ungradedIncl_gen`.  This matches the
scheme level, where `Stacks.SymAlgSheaf.algebraLift` is likewise not unique.

**Quasi-coherence of `Sym(ℱ)`.**  Still absent at the algebraic-space level, and not needed by
anything here: `algebraLift` is a morphism of `AlgebraicGeometry.Space.AlgebraSheaf`, which
asserts no quasi-coherence of either side.  See
`StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafMap` for what the remaining
obstruction
to it is.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SymAlgSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : AlgebraicSpaces B S hS) (𝒜 : AlgebraSheaf.{u, u} B S hS W.1 W.2)

/-! ### An algebra sheaf as a degenerately graded algebra -/

/-- The commutative ring of sections of an algebra sheaf over an étale chart.  This is the
spelling on which the ring operations are available; the sections of
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule` are the same type with the same
addition. -/
abbrev algSections (V : (SmallEtale B S hS W.1)ᵒᵖ) : CommRingCat.{u} := 𝒜.right.obj.obj V

/-- Multiplication by the image `𝒜.algebraMap V r` of a section `r` of the structure sheaf
associates with the multiplication of the sections of `𝒜`. -/
theorem mul_assoc_algSections (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (r : (structureSheaf B S hS W.1 W.2).obj.obj V) (x y : algSections B S hS W 𝒜 V) :
    𝒜.algebraMap V r * x * y = 𝒜.algebraMap V r * (x * y) :=
  mul_assoc _ _ _

/-- Left-commutativity of multiplication by `𝒜.algebraMap V r` in the sections of `𝒜`. -/
theorem mul_left_comm_algSections (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (r : (structureSheaf B S hS W.1 W.2).obj.obj V) (x y : algSections B S hS W 𝒜 V) :
    x * (𝒜.algebraMap V r * y) = 𝒜.algebraMap V r * (x * y) :=
  mul_left_comm _ _ _

/-- Restriction of sections of `𝒜` along `f : V ⟶ V'` is multiplicative. -/
theorem map_mul_algSections {V V' : (SmallEtale B S hS W.1)ᵒᵖ} (f : V ⟶ V')
    (x y : algSections B S hS W 𝒜 V) :
    (𝒜.right.obj.map f).hom (x * y) =
      (𝒜.right.obj.map f).hom x * (𝒜.right.obj.map f).hom y :=
  map_mul _ x y

/-- Associativity of multiplication in the sections of `𝒜` over `V`. -/
theorem assoc_algSections (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (x y z : algSections B S hS W 𝒜 V) : x * y * z = x * (y * z) :=
  mul_assoc x y z

/-- The unit is a left identity for multiplication in the sections of `𝒜` over `V`. -/
theorem one_mul_algSections (V : (SmallEtale B S hS W.1)ᵒᵖ) (x : algSections B S hS W 𝒜 V) :
    1 * x = x :=
  one_mul x

/-- The unit is a right identity for multiplication in the sections of `𝒜` over `V`. -/
theorem mul_one_algSections (V : (SmallEtale B S hS W.1)ᵒᵖ) (x : algSections B S hS W 𝒜 V) :
    x * 1 = x :=
  mul_one x

/-- Commutativity of multiplication in the sections of `𝒜` over `V`. -/
theorem mul_comm_algSections (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (x y : algSections B S hS W 𝒜 V) : x * y = y * x :=
  mul_comm x y

/-- Multiplication on the underlying module of an algebra sheaf, as a bilinear map of sheaves of
modules.  Linearity in the second variable is where commutativity of `𝒜` is used. -/
def mulBilinear :
    SheafOfModules.BilinearMap (AlgebraSheaf.underlyingModule 𝒜)
      (AlgebraSheaf.underlyingModule 𝒜) (AlgebraSheaf.underlyingModule 𝒜) where
  app V := AddMonoidHom.mul (R := algSections B S hS W 𝒜 V)
  map_smul_left V r x y := mul_assoc_algSections B S hS W 𝒜 V r x y
  map_smul_right V r x y := mul_left_comm_algSections B S hS W 𝒜 V r x y
  naturality {_V _V'} f x y := map_mul_algSections B S hS W 𝒜 f x y

/-- The unit section of the underlying module of an algebra sheaf. -/
def oneSection : (AlgebraSheaf.underlyingModule 𝒜).sections :=
  PresheafOfModules.sectionsMk (fun V => (1 : algSections B S hS W 𝒜 V))
    (fun {_V _V'} f => map_one (𝒜.right.obj.map f).hom)

/-- **An algebra sheaf on an algebraic space, read as a sheaf of graded algebras with every
homogeneous piece the whole algebra** and the ring multiplication as the homogeneous
multiplication in every pair of degrees.

This is not the degree-zero concentration: that one forces a degree-one generator to be zero.
See the implementation notes. -/
def constGraded : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS W) where
  piece _ := AlgebraSheaf.underlyingModule 𝒜
  mul _ _ := mulBilinear B S hS W 𝒜
  one := oneSection B S hS W 𝒜
  mul_assoc _ _ _ V x y z := heq_of_eq (assoc_algSections B S hS W 𝒜 V x y z)
  one_mul _ V x := heq_of_eq (one_mul_algSections B S hS W 𝒜 V x)
  mul_one _ V x := heq_of_eq (mul_one_algSections B S hS W 𝒜 V x)

/-! ### The lift -/

section Lift

variable (F : SheafOfModules.{u} (structureRingSheaf B S hS W))
    (φ : F ⟶ AlgebraSheaf.underlyingModule 𝒜)

/-- `Sym(F)` read as a graded algebra of presheaves of modules, which is what the ungraded
realization is formed from. -/
abbrev symPre : Stacks.GradedAlgebra fun n : ℤ =>
    ((symmetricAlgebra B S hS W F).piece n).val :=
  (symmetricAlgebra B S hS W F).toPresheafGradedAlgebra

/-- A morphism into an algebra sheaf is a pairwise-commuting degree-one generator of
`AlgebraicGeometry.Space.SymAlgSheaf.constGraded`, because `𝒜` is commutative. -/
theorem pairwiseCommutes_constGraded :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (A := constGraded B S hS W 𝒜) (M := F) φ :=
  fun V _ _ => mul_comm_algSections B S hS W 𝒜 V _ _

/-- **The degreewise comparison `Symⁿ(F) ⟶ 𝒜` extending `φ`**, as a unital homomorphism of
sheaves of graded algebras into `AlgebraicGeometry.Space.SymAlgSheaf.constGraded`: the unique
witness of the graded universal property of `Sym(F)` at the degenerately graded `𝒜`. -/
def descHom : SheafOfModules.GradedAlgebra.UnitalHom
    (symmetricAlgebra B S hS W F) (constGraded B S hS W 𝒜) :=
  SheafOfModules.GradedAlgebra.IsUniversal.desc
    (isSymmetricAlgebra_symmetricAlgebra B S hS W F) (constGraded B S hS W 𝒜) φ
    (pairwiseCommutes_constGraded B S hS W 𝒜 F φ)

/-- The degreewise comparison extends `φ`: its degree-one component composed with the degree-one
generator of `Sym(F)` is `φ`. -/
theorem symmetricAlgebraGen_comp_descHom :
    symmetricAlgebraGen B S hS W F ≫ (descHom B S hS W 𝒜 F φ).app 1 = φ :=
  SheafOfModules.GradedAlgebra.IsUniversal.desc_extends
    (isSymmetricAlgebra_symmetricAlgebra B S hS W F) (constGraded B S hS W 𝒜) φ
    (pairwiseCommutes_constGraded B S hS W 𝒜 F φ)

/-- The degree-`n` component of the comparison on sections, as an additive map into the ring of
sections of `𝒜`. -/
def psiAdd (n : ℤ) (V : (SmallEtale B S hS W.1)ᵒᵖ) :
    (((symmetricAlgebra B S hS W F).piece n).val.obj V : Type u) →+ algSections B S hS W 𝒜 V :=
  AddMonoidHom.mk' (fun x => ((descHom B S hS W 𝒜 F φ).app n).val.app V x)
    (fun x y => map_add (((descHom B S hS W 𝒜 F φ).app n).val.app V).hom x y)

/-- **The comparison on sections of the ungraded realization**: a section of `⨁ₙ Symⁿ(F)(V)` is
sent to the sum of the images of its homogeneous components. -/
def psiTotal (V : (SmallEtale B S hS W.1)ᵒᵖ) :
    (symPre B S hS W F).Total V →+ algSections B S hS W 𝒜 V :=
  DirectSum.toAddMonoid fun n => psiAdd B S hS W 𝒜 F φ n V

/-- On a homogeneous section `x` of degree `n`, the comparison `psiTotal` is the degree-`n`
component `psiAdd` applied to `x`. -/
theorem psiTotal_incl (n : ℤ) (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (x : ((symmetricAlgebra B S hS W F).piece n).val.obj V) :
    psiTotal B S hS W 𝒜 F φ V ((symPre B S hS W F).incl n x) =
      psiAdd B S hS W 𝒜 F φ n V x :=
  DirectSum.toAddMonoid_of _ _ _

/-- The comparison is unital: the unit of the ungraded realization is the degree-zero graded
unit. -/
theorem psiTotal_one (V : (SmallEtale B S hS W.1)ᵒᵖ) : psiTotal B S hS W 𝒜 F φ V 1 = 1 := by
  rw [(symPre B S hS W F).one_eq_incl, psiTotal_incl]
  exact (descHom B S hS W 𝒜 F φ).map_one V

/-- **The comparison is multiplicative on the sections of the ungraded realization.**  The
multiplication of the realization is determined on homogeneous sections by the graded one
(`Stacks.GradedAlgebra.incl_mul_incl`) and is biadditive, so the `map_mul` law of the unital
homomorphism suffices. -/
theorem psiTotal_mul (V : (SmallEtale B S hS W.1)ᵒᵖ) (a b : (symPre B S hS W F).Total V) :
    psiTotal B S hS W 𝒜 F φ V (a * b) =
      psiTotal B S hS W 𝒜 F φ V a * psiTotal B S hS W 𝒜 F φ V b := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | incl i x =>
      induction b using Stacks.GradedAlgebra.incl_induction with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | incl j y =>
          rw [Stacks.GradedAlgebra.incl_mul_incl, psiTotal_incl, psiTotal_incl, psiTotal_incl]
          exact (descHom B S hS W 𝒜 F φ).map_mul i j V x y
      | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]

/-- The comparison commutes with restriction. -/
theorem psiTotal_naturality {V V' : (SmallEtale B S hS W.1)ᵒᵖ} (f : V ⟶ V')
    (a : (symPre B S hS W F).Total V) :
    psiTotal B S hS W 𝒜 F φ V' ((symPre B S hS W F).totalRestrict f a) =
      (𝒜.right.obj.map f).hom (psiTotal B S hS W 𝒜 F φ V a) := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | incl i x =>
      rw [Stacks.GradedAlgebra.totalRestrict_incl, psiTotal_incl, psiTotal_incl]
      exact PresheafOfModules.naturality_apply ((descHom B S hS W 𝒜 F φ).app i).val f x
  | add a a' ha ha' =>
      rw [map_add ((symPre B S hS W F).totalRestrict f),
        map_add (psiTotal B S hS W 𝒜 F φ V'), ha, ha',
        map_add (psiTotal B S hS W 𝒜 F φ V), map_add (𝒜.right.obj.map f).hom]

/-- The comparison on sections of the ungraded realization, as a ring homomorphism. -/
def psiRingHom (V : (SmallEtale B S hS W.1)ᵒᵖ) :
    (symPre B S hS W F).Total V →+* (AlgebraSheaf.ringSheafOfSite 𝒜).obj.obj V where
  toFun := psiTotal B S hS W 𝒜 F φ V
  map_one' := psiTotal_one B S hS W 𝒜 F φ V
  map_mul' := psiTotal_mul B S hS W 𝒜 F φ V
  map_zero' := map_zero _
  map_add' := map_add _

/-- **The comparison out of the ungraded realization at the presheaf level**: a morphism of
presheaves of rings `⨁ₙ Symⁿ(F) ⟶ 𝒜`. -/
def psiPresheafHom :
    (symPre B S hS W F).totalPresheaf ⟶ (AlgebraSheaf.ringSheafOfSite 𝒜).obj where
  app V := RingCat.ofHom (psiRingHom B S hS W 𝒜 F φ V)
  naturality _V _V' f :=
    RingCat.hom_ext (RingHom.ext fun a => psiTotal_naturality B S hS W 𝒜 F φ f a)

/-- The degree-`n` component of the comparison is linear over the structure sheaf: it carries
`r • x` to `𝒜.algebraMap V r * psiAdd x`. -/
theorem psiAdd_smul (n : ℤ) (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (r : (structureRingSheaf B S hS W).obj.obj V)
    (x : ((symmetricAlgebra B S hS W F).piece n).val.obj V) :
    psiAdd B S hS W 𝒜 F φ n V (r • x) =
      𝒜.algebraMap V r * psiAdd B S hS W 𝒜 F φ n V x :=
  map_smul (((descHom B S hS W 𝒜 F φ).app n).val.app V).hom r x

/-- The comparison on sections of the ungraded realization carries `r • a` to
`𝒜.algebraMap V r * psiTotal a`. -/
theorem psiTotal_smul (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (r : (structureRingSheaf B S hS W).obj.obj V) (a : (symPre B S hS W F).Total V) :
    psiTotal B S hS W 𝒜 F φ V (r • a) =
      𝒜.algebraMap V r * psiTotal B S hS W 𝒜 F φ V a := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | incl i x =>
      rw [← Stacks.GradedAlgebra.incl_smul, psiTotal_incl, psiTotal_incl, psiAdd_smul]
  | add a a' ha ha' =>
      rw [smul_add, map_add (psiTotal B S hS W 𝒜 F φ V), ha, ha',
        map_add (psiTotal B S hS W 𝒜 F φ V), mul_add]

/-- **The comparison carries the structure map `r ↦ r • 1` of the ungraded realization to the
structure-algebra map of `𝒜`.**  This is what makes the lift a morphism of algebra sheaves. -/
theorem psiTotal_structureMap (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (r : (structureRingSheaf B S hS W).obj.obj V) :
    psiTotal B S hS W 𝒜 F φ V ((symPre B S hS W F).structureMap V r) = 𝒜.algebraMap V r := by
  have h : psiTotal B S hS W 𝒜 F φ V (r • (1 : (symPre B S hS W F).Total V)) =
      𝒜.algebraMap V r := by
    rw [psiTotal_smul, psiTotal_one, mul_one]
  exact h

/-- **The lift out of the ungraded realization, as a morphism of sheaves of rings**: the
presheaf-level comparison descended across the sheafification by
`Stacks.GradedAlgebra.totalSheafLift`. -/
def ungradedLift :
    (symPre B S hS W F).totalSheaf (SmallEtale.topology B S hS W.1) ⟶
      AlgebraSheaf.ringSheafOfSite 𝒜 :=
  (symPre B S hS W F).totalSheafLift (SmallEtale.topology B S hS W.1)
    (AlgebraSheaf.ringSheafOfSite 𝒜) (psiPresheafHom B S hS W 𝒜 F φ)

/-- The defining property of the lift: it agrees with the presheaf-level comparison on the image
of the sheafification unit. -/
theorem ungradedLift_totalUnit (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (z : (symPre B S hS W F).Total V) :
    ((ungradedLift B S hS W 𝒜 F φ).hom.app V).hom
        ((symPre B S hS W F).totalUnit (SmallEtale.topology B S hS W.1) V z) =
      psiTotal B S hS W 𝒜 F φ V z :=
  congrArg (fun t : (symPre B S hS W F).totalPresheaf ⟶ _ => RingCat.Hom.hom (t.app V) z)
    ((symPre B S hS W F).toTotalSheaf_totalSheafLift (SmallEtale.topology B S hS W.1)
      (AlgebraSheaf.ringSheafOfSite 𝒜) (psiPresheafHom B S hS W 𝒜 F φ))

/-- The lift, as a morphism of sheaves of commutative rings.  The underlying morphism of sheaves
of rings is unchanged: `AlgebraicGeometry.Space.commRingSheafOfMulComm` keeps the carrier and the
ring operations. -/
def commLift : (symmetricAlgebraSheaf B S hS W F).right ⟶ 𝒜.right :=
  ⟨{ app := fun V => @CommRingCat.ofHom
        ((symmetricAlgebraSheaf B S hS W F).right.obj.obj V) (algSections B S hS W 𝒜 V)
        inferInstance inferInstance ((ungradedLift B S hS W 𝒜 F φ).hom.app V).hom
     naturality := fun _V _V' g => by
       ext x
       exact congrArg (fun ψ => RingCat.Hom.hom ψ x)
         ((ungradedLift B S hS W 𝒜 F φ).hom.naturality g) }⟩

/-- **The ungraded, sectionwise universal property of the symmetric algebra of a sheaf of modules
on an algebraic space**: a morphism of module sheaves `φ : F ⟶ 𝒜.underlyingModule` into an
algebra sheaf `𝒜` extends to a morphism of algebra sheaves `Sym(F) ⟶ 𝒜`.

Its defining property is
`AlgebraicGeometry.Space.SymAlgSheaf.algebraLift_ungradedIncl_gen`: the extension restricts to
`φ` in degree one.  Uniqueness is not claimed; see the implementation notes. -/
def algebraLift : symmetricAlgebraSheaf B S hS W F ⟶ 𝒜 where
  right := commLift B S hS W 𝒜 F φ
  comm V r :=
    (ungradedLift_totalUnit B S hS W 𝒜 F φ V ((symPre B S hS W F).structureMap V r)).trans
      (psiTotal_structureMap B S hS W 𝒜 F φ V r)

/-- **The lift restricts to `φ` in degree one**: on the image in the ungraded ring sheaf of a
degree-one local section of `Sym(F)` coming from a local section `s` of `F`, the lift takes the
value `φ s`. -/
theorem algebraLift_ungradedIncl_gen (V : (SmallEtale B S hS W.1)ᵒᵖ) (s : F.val.obj V) :
    ((algebraLift B S hS W 𝒜 F φ).right.hom.app V).hom
        ((symmetricAlgebra B S hS W F).ungradedIncl 1
          ((symmetricAlgebraGen B S hS W F).val.app V s)) =
      φ.val.app V s := by
  refine (ungradedLift_totalUnit B S hS W 𝒜 F φ V ((symPre B S hS W F).incl 1
    ((symmetricAlgebraGen B S hS W F).val.app V s))).trans ?_
  rw [psiTotal_incl]
  exact congrArg (fun t : F ⟶ AlgebraSheaf.underlyingModule 𝒜 => t.val.app V s)
    (symmetricAlgebraGen_comp_descHom B S hS W 𝒜 F φ)

end Lift

end AlgebraicGeometry.Space.SymAlgSheaf

end
