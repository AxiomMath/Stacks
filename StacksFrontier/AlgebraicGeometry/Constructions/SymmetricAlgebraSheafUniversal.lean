module

public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Properties.QuasicoherentAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ungraded universal property of the symmetric algebra of a module sheaf

Let `X` be a scheme, `F` an `𝒪_X`-module sheaf and `𝒜` a sheaf of commutative `𝒪_X`-algebras
(an object of `AlgebraicGeometry.Scheme.QuasicoherentAlgebra X`, i.e. of `Under X.sheaf`). A
morphism of module sheaves

`φ : F ⟶ 𝒜.underlyingModule`

extends to a morphism of *algebra* sheaves `Sym(F) ⟶ 𝒜`, and the extension restricts to `φ` in
degree one. This is the ungraded, sectionwise form of the universal property of
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf`, which is the input the relative
spectrum consumes, so it is the form needed to map into `𝐕(F) = Spec_X(Sym(F))`.

## Main definitions

* `Stacks.SymAlgSheaf.constGraded`: **an algebra sheaf read as a sheaf of graded algebras with
  every homogeneous piece the whole algebra**, with the ring multiplication as its homogeneous
  multiplication. This is the device that makes the graded universal property applicable; see the
  implementation notes.
* `Stacks.SymAlgSheaf.descHom`: the degreewise comparison `Symⁿ(F) ⟶ 𝒜`, as a unital homomorphism
  of sheaves of graded algebras `Sym(F) ⟶ constGraded 𝒜`.
* `Stacks.SymAlgSheaf.psiTotal` and `psiPresheafHom`: that comparison summed over the degrees —
  the morphism of *presheaves* of rings `⨁ₙ Symⁿ(F) ⟶ 𝒜` out of
  `Stacks.GradedAlgebra.totalPresheaf`.
* `Stacks.SymAlgSheaf.ungradedLift` and `commLift`: the induced morphism out of the
  sheafification, as a morphism of sheaves of rings and then of sheaves of commutative rings.
* `Stacks.SymAlgSheaf.algebraLift`: **the morphism of algebra sheaves `Sym(F) ⟶ 𝒜` extending
  `φ`.**

## Main results

* `Stacks.SymAlgSheaf.psiTotal_mul`, `psiTotal_one` and `psiTotal_smul`: the degreewise comparison
  summed over the degrees is multiplicative, unital and `𝒪_X`-semilinear on the sections of the
  ungraded realization. Multiplicativity is the `map_mul` law of a unital homomorphism of graded
  algebras read through `Stacks.GradedAlgebra.incl_mul_incl` and biadditivity; no sheaf-theoretic
  argument is needed, because the realization is formed at the presheaf level.
* `Stacks.SymAlgSheaf.psiTotal_structureMap`: the comparison carries the structure map `r ↦ r • 1`
  of the ungraded realization to the structure morphism of `𝒜`. This is what makes the lift a
  morphism in `Under X.sheaf` rather than merely of sheaves of rings
  (`structureMap_comp_commLift`).
* `Stacks.SymAlgSheaf.algebraLift_ungradedIncl_gen`: **the lift restricts to `φ` in degree one** —
  on a degree-one local section `s` of `F`, viewed in the ungraded ring sheaf by
  `SheafOfModules.GradedAlgebra.ungradedIncl`, the lift takes the value `φ s`.

## Implementation notes

### The graded universal property quantifies over graded algebras, and that is not a vocabulary
mismatch

`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra` is defined through
`SheafOfModules.GradedAlgebra.IsUniversal`, which quantifies over sheaves of **graded** algebras
`B` and produces a `SheafOfModules.GradedAlgebra.UnitalHom` of degreewise maps. An arbitrary
algebra sheaf `𝒜` is not a graded algebra, and the obvious repair — present it as one
concentrated in degree zero — destroys the statement: it forces the generator to land in
`B.piece 1 = 0`, so the very morphism `φ` being extended is killed. For the same reason
`Stacks.RelativeSpec.ungradedAlgebraSheafMap` does not reach this statement either: it goes
between two algebra sheaves that *both* come from graded algebras.

What does work, and is the whole trick of this file, is the **opposite** degenerate grading:
`constGraded 𝒜` has `piece n = 𝒜.underlyingModule` for *every* `n`, with the ring multiplication
of `𝒜` as the homogeneous multiplication in every pair of degrees. Nothing in
`SheafOfModules.GradedAlgebra` requires the pieces to be distinct or the grading to be faithful —
its fields are a bilinear multiplication `piece i × piece j ⟶ piece (i + j)`, a unit in degree
zero, associativity and the two unit laws — and all five are supplied by `CommRing` axioms of the
sections. A `UnitalHom (Sym F) (constGraded 𝒜)` is then exactly a family of morphisms
`Symⁿ(F) ⟶ 𝒜` that is multiplicative and unital, which is precisely the ungraded data wanted,
and `PairwiseCommutes` of `φ` is commutativity of `𝒜`.

Because every piece is the same object, all the `HEq` laws of `SheafOfModules.GradedAlgebra` have
both sides in the same type and are discharged by `heq_of_eq`; no transport appears anywhere
below.

### Why the comparison is obtained from an `ExistsUnique`

`descHom` is `SheafOfModules.GradedAlgebra.IsUniversal.desc` of
`AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra`, i.e. the *unique* witness
of the graded universal property. It is therefore canonical: `desc_unique` pins it down, and
`symmetricAlgebraGen_comp_descHom` is its defining equation. The alternative — rebuilding the
degreewise comparison by hand from `SymmetricAlgebra.lift` on sections and then descending it
through the degreewise sheafification units — reproves the content of
`Stacks.GradedAlgebra.cmpInt` and `Stacks.GradedAlgebra.isSymmetricAlgebra_sheafify` with a
different target, and is not done here.

### The defeq-spelling discipline

The sections of `𝒜.underlyingModule` over `W` and the sections `𝒜.right.obj.obj W` of `𝒜` are the
same type with the same addition, but not syntactically the same, and `*` is available only on
the second. Each of the three structural facts is therefore stated once, on the ring spelling
(`mul_assoc_algSections`, `mul_left_comm_algSections`, `map_mul_algSections`, and their
companions), and used by *application*, which is defeq-tolerant; the scalar action of
`𝒪_X(W)` on `𝒜.underlyingModule` is `r • m = 𝒜.hom(r) * m` by definition, which is why
`psiAdd_smul` is `map_smul` of a linear map with no bridging lemma.

### What is not here

**No uniqueness.** The lift is *not* claimed unique. Uniqueness of an ungraded extension needs
`Sym(F)` to be generated in degree one on the sections over every open, which is false for a
general open (it holds over affine opens for quasi-coherent `F`,
`Stacks.SymGenDegreeOne`), so the statement proved is existence together with the
degree-one equation, and that is what consumers get.

**No finite presentation.** `Scheme.QuasicoherentAlgebra.IsOfFinitePresentation` of
`symmetricAlgebraSheaf X F` for `F` of finite presentation is not proved here; it needs the ring
of sections of the ungraded realization over an affine open to be identified with
`SymmetricAlgebra Γ(X, V) Γ(F, V)`, which is recorded as unproved in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization` and of
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule`.

**No `@[stacks]` tag.** Tag 01CF's universal properties are the graded ones, already carried by
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`; the ungraded statement below is the form
Tag 01M2's relative spectrum needs and is not itself a tag's assertion.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Scheme.QuasicoherentAlgebra

universe u

namespace Stacks.SymAlgSheaf

variable {X : Scheme.{u}} (𝒜 : X.QuasicoherentAlgebra)

/-! ### An algebra sheaf as a degenerately graded algebra -/

/-- The commutative ring of sections of an algebra sheaf over an open of the site. This is the
spelling on which the ring operations are available; the sections of `𝒜.underlyingModule` are the
same type with the same addition. -/
abbrev algSections (W : (Opens ↥X)ᵒᵖ) : CommRingCat.{u} := 𝒜.right.obj.obj W

/-- In the sections of an algebra sheaf, multiplying by the image of a scalar is associative with
the ring multiplication: `(r • 1) * x * y = (r • 1) * (x * y)`. -/
theorem mul_assoc_algSections (W : (Opens ↥X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W)
    (x y : algSections 𝒜 W) :
    (𝒜.hom.hom.app W).hom r * x * y = (𝒜.hom.hom.app W).hom r * (x * y) :=
  mul_assoc _ _ _

/-- In the sections of an algebra sheaf, the image of a scalar commutes past a left factor:
`x * ((r • 1) * y) = (r • 1) * (x * y)`. -/
theorem mul_left_comm_algSections (W : (Opens ↥X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W)
    (x y : algSections 𝒜 W) :
    x * ((𝒜.hom.hom.app W).hom r * y) = (𝒜.hom.hom.app W).hom r * (x * y) :=
  mul_left_comm _ _ _

/-- Restriction of sections of an algebra sheaf is multiplicative. -/
theorem map_mul_algSections {W W' : (Opens ↥X)ᵒᵖ} (f : W ⟶ W') (x y : algSections 𝒜 W) :
    (𝒜.right.obj.map f).hom (x * y) =
      (𝒜.right.obj.map f).hom x * (𝒜.right.obj.map f).hom y :=
  map_mul _ x y

/-- Multiplication of sections of an algebra sheaf is associative. -/
theorem assoc_algSections (W : (Opens ↥X)ᵒᵖ) (x y z : algSections 𝒜 W) :
    x * y * z = x * (y * z) := mul_assoc x y z

/-- The unit section is a left identity for multiplication of sections of an algebra sheaf. -/
theorem one_mul_algSections (W : (Opens ↥X)ᵒᵖ) (x : algSections 𝒜 W) : 1 * x = x := one_mul x

/-- The unit section is a right identity for multiplication of sections of an algebra sheaf. -/
theorem mul_one_algSections (W : (Opens ↥X)ᵒᵖ) (x : algSections 𝒜 W) : x * 1 = x := mul_one x

/-- Multiplication of sections of an algebra sheaf is commutative. -/
theorem mul_comm_algSections (W : (Opens ↥X)ᵒᵖ) (x y : algSections 𝒜 W) : x * y = y * x :=
  mul_comm x y

/-- Multiplication on the underlying module of an algebra sheaf, as a bilinear map of sheaves of
modules. Linearity in the second variable is where commutativity of `𝒜` is used. -/
def mulBilinear :
    SheafOfModules.BilinearMap (underlyingModule 𝒜) (underlyingModule 𝒜)
      (underlyingModule 𝒜) where
  app W := AddMonoidHom.mul (R := algSections 𝒜 W)
  map_smul_left W r x y := mul_assoc_algSections 𝒜 W r x y
  map_smul_right W r x y := mul_left_comm_algSections 𝒜 W r x y
  naturality {_W _W'} f x y := map_mul_algSections 𝒜 f x y

/-- The unit section of the underlying module of an algebra sheaf. -/
def oneSection : (underlyingModule 𝒜).sections :=
  PresheafOfModules.sectionsMk (fun W => (1 : algSections 𝒜 W))
    (fun {_W _W'} f => map_one (𝒜.right.obj.map f).hom)

/-- **An algebra sheaf, read as a sheaf of graded algebras with every homogeneous piece the whole
algebra** and the ring multiplication as the homogeneous multiplication in every pair of degrees.

This is not the degree-zero concentration: that one forces a degree-one generator to be zero. See
the implementation notes. -/
def constGraded : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf where
  piece _ := underlyingModule 𝒜
  mul _ _ := mulBilinear 𝒜
  one := oneSection 𝒜
  mul_assoc _ _ _ W x y z := heq_of_eq (assoc_algSections 𝒜 W x y z)
  one_mul _ W x := heq_of_eq (one_mul_algSections 𝒜 W x)
  mul_one _ W x := heq_of_eq (mul_one_algSections 𝒜 W x)

/-! ### The lift -/

section Lift

variable (F : SheafOfModules.{u} X.ringCatSheaf) (φ : F ⟶ underlyingModule 𝒜)

/-- `Sym(F)` read as a graded algebra of presheaves of modules, which is what the ungraded
realization is formed from. -/
abbrev symPre : Stacks.GradedAlgebra fun n : ℤ =>
    ((Scheme.Modules.symmetricAlgebra X F).piece n).val :=
  (Scheme.Modules.symmetricAlgebra X F).toPresheafGradedAlgebra

/-- A morphism into an algebra sheaf is a pairwise-commuting degree-one generator of
`constGraded`, because `𝒜` is commutative. -/
theorem pairwiseCommutes_constGraded :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (A := constGraded 𝒜) (M := F) φ :=
  fun W _ _ => mul_comm_algSections 𝒜 W _ _

/-- **The degreewise comparison `Symⁿ(F) ⟶ 𝒜` extending `φ`**, as a unital homomorphism of
sheaves of graded algebras into `Stacks.SymAlgSheaf.constGraded`: the unique witness of the graded
universal property of `Sym(F)` at the degenerately graded `𝒜`. -/
def descHom : SheafOfModules.GradedAlgebra.UnitalHom
    (Scheme.Modules.symmetricAlgebra X F) (constGraded 𝒜) :=
  SheafOfModules.GradedAlgebra.IsUniversal.desc
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F) (constGraded 𝒜) φ
    (pairwiseCommutes_constGraded 𝒜 F φ)

/-- The degreewise comparison extends `φ`: its degree-one component composed with the degree-one
generator of `Sym(F)` is `φ`. -/
theorem symmetricAlgebraGen_comp_descHom :
    Scheme.Modules.symmetricAlgebraGen X F ≫ (descHom 𝒜 F φ).app 1 = φ :=
  SheafOfModules.GradedAlgebra.IsUniversal.desc_extends
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F) (constGraded 𝒜) φ
    (pairwiseCommutes_constGraded 𝒜 F φ)

/-- The degree-`n` component of the comparison on sections, as an additive map into the ring of
sections of `𝒜`. -/
def psiAdd (n : ℤ) (W : (Opens ↥X)ᵒᵖ) :
    (((Scheme.Modules.symmetricAlgebra X F).piece n).val.obj W : Type u) →+ algSections 𝒜 W :=
  AddMonoidHom.mk' (fun x => ((descHom 𝒜 F φ).app n).val.app W x)
    (fun x y => map_add (((descHom 𝒜 F φ).app n).val.app W).hom x y)

/-- **The comparison on sections of the ungraded realization**: a section of `⨁ₙ Symⁿ(F)(W)` is
sent to the sum of the images of its homogeneous components. -/
def psiTotal (W : (Opens ↥X)ᵒᵖ) : (symPre F).Total W →+ algSections 𝒜 W :=
  DirectSum.toAddMonoid fun n => psiAdd 𝒜 F φ n W

/-- On a homogeneous section of degree `n`, the comparison `psiTotal` is the degree-`n` component
`psiAdd`. -/
theorem psiTotal_incl (n : ℤ) (W : (Opens ↥X)ᵒᵖ)
    (x : ((Scheme.Modules.symmetricAlgebra X F).piece n).val.obj W) :
    psiTotal 𝒜 F φ W ((symPre F).incl n x) = psiAdd 𝒜 F φ n W x :=
  DirectSum.toAddMonoid_of _ _ _

/-- The comparison is unital: the unit of the ungraded realization is the degree-zero graded
unit. -/
theorem psiTotal_one (W : (Opens ↥X)ᵒᵖ) : psiTotal 𝒜 F φ W 1 = 1 := by
  rw [(symPre F).one_eq_incl, psiTotal_incl]
  exact (descHom 𝒜 F φ).map_one W

/-- **The comparison is multiplicative on the sections of the ungraded realization.** The
multiplication of the realization is determined on homogeneous sections by the graded one
(`Stacks.GradedAlgebra.incl_mul_incl`) and is biadditive, so the `map_mul` law of the unital
homomorphism suffices. -/
theorem psiTotal_mul (W : (Opens ↥X)ᵒᵖ) (a b : (symPre F).Total W) :
    psiTotal 𝒜 F φ W (a * b) = psiTotal 𝒜 F φ W a * psiTotal 𝒜 F φ W b := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | incl i x =>
      induction b using Stacks.GradedAlgebra.incl_induction with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | incl j y =>
          rw [Stacks.GradedAlgebra.incl_mul_incl, psiTotal_incl, psiTotal_incl, psiTotal_incl]
          exact (descHom 𝒜 F φ).map_mul i j W x y
      | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]

/-- Two additive maps out of the ungraded realization agree if they agree on homogeneous
sections. -/
private theorem total_addHom_ext {W : (Opens ↥X)ᵒᵖ} {M : Type*} [AddZeroClass M]
    {g h : (symPre F).Total W →+ M}
    (H : ∀ (i : ℤ) (x : ((Scheme.Modules.symmetricAlgebra X F).piece i).val.obj W),
      g ((symPre F).incl i x) = h ((symPre F).incl i x)) : g = h :=
  DirectSum.addHom_ext H

/-- The comparison commutes with restriction. -/
theorem psiTotal_naturality {W W' : (Opens ↥X)ᵒᵖ} (f : W ⟶ W') (a : (symPre F).Total W) :
    psiTotal 𝒜 F φ W' ((symPre F).totalRestrict f a) =
      (𝒜.right.obj.map f).hom (psiTotal 𝒜 F φ W a) :=
  DFunLike.congr_fun (total_addHom_ext F
    (g := (psiTotal 𝒜 F φ W').comp ((symPre F).totalRestrict f))
    (h := (𝒜.right.obj.map f).hom.toAddMonoidHom.comp (psiTotal 𝒜 F φ W)) fun i x => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        Stacks.GradedAlgebra.totalRestrict_incl, psiTotal_incl, psiTotal_incl]
      exact PresheafOfModules.naturality_apply ((descHom 𝒜 F φ).app i).val f x) a

/-- The comparison on sections of the ungraded realization, as a ring homomorphism. -/
def psiRingHom (W : (Opens ↥X)ᵒᵖ) :
    (symPre F).Total W →+* (Scheme.QuasicoherentAlgebra.ringSheaf 𝒜).obj.obj W where
  toFun := psiTotal 𝒜 F φ W
  map_one' := psiTotal_one 𝒜 F φ W
  map_mul' := psiTotal_mul 𝒜 F φ W
  map_zero' := map_zero _
  map_add' := map_add _

/-- **The comparison out of the ungraded realization at the presheaf level**: a morphism of
presheaves of rings `⨁ₙ Symⁿ(F) ⟶ 𝒜`. -/
def psiPresheafHom :
    (symPre F).totalPresheaf ⟶ (Scheme.QuasicoherentAlgebra.ringSheaf 𝒜).obj where
  app W := RingCat.ofHom (psiRingHom 𝒜 F φ W)
  naturality _W _W' f :=
    RingCat.hom_ext (RingHom.ext fun a => psiTotal_naturality 𝒜 F φ f a)

/-- The degree-`n` component of the comparison is linear over the structure sheaf: it sends `r • x`
to the product of the image of `r` in `𝒜` with the image of `x`. -/
theorem psiAdd_smul (n : ℤ) (W : (Opens ↥X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W)
    (x : ((Scheme.Modules.symmetricAlgebra X F).piece n).val.obj W) :
    psiAdd 𝒜 F φ n W (r • x) = (𝒜.hom.hom.app W).hom r * psiAdd 𝒜 F φ n W x :=
  map_smul (((descHom 𝒜 F φ).app n).val.app W).hom r x

/-- The comparison on the ungraded realization sends `r • a` to the product of the image of `r` in
`𝒜` with the image of `a`. -/
theorem psiTotal_smul (W : (Opens ↥X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W)
    (a : (symPre F).Total W) :
    psiTotal 𝒜 F φ W (r • a) = (𝒜.hom.hom.app W).hom r * psiTotal 𝒜 F φ W a :=
  DFunLike.congr_fun (total_addHom_ext F
    (g := (psiTotal 𝒜 F φ W).comp (DistribSMul.toAddMonoidHom _ r))
    (h := (AddMonoidHom.mulLeft ((𝒜.hom.hom.app W).hom r)).comp (psiTotal 𝒜 F φ W))
    fun i x => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        DistribSMul.toAddMonoidHom_apply, ← Stacks.GradedAlgebra.incl_smul, psiTotal_incl,
        psiTotal_incl, psiAdd_smul, AddMonoidHom.coe_mulLeft]) a

/-- **The comparison carries the structure map `r ↦ r • 1` of the ungraded realization to the
structure morphism of `𝒜`.** This is what makes the lift a morphism of algebra sheaves. -/
theorem psiTotal_structureMap (W : (Opens ↥X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W) :
    psiTotal 𝒜 F φ W ((symPre F).structureMap W r) = (𝒜.hom.hom.app W).hom r := by
  have h : psiTotal 𝒜 F φ W (r • (1 : (symPre F).Total W)) = (𝒜.hom.hom.app W).hom r := by
    rw [psiTotal_smul, psiTotal_one, mul_one]
  exact h

/-- **The lift out of the ungraded realization, as a morphism of sheaves of rings**: the
presheaf-level comparison descended across the sheafification by
`Stacks.GradedAlgebra.totalSheafLift`. -/
def ungradedLift :
    (symPre F).totalSheaf (Opens.grothendieckTopology (X : TopCat)) ⟶
      Scheme.QuasicoherentAlgebra.ringSheaf 𝒜 :=
  (symPre F).totalSheafLift (Opens.grothendieckTopology (X : TopCat))
    (Scheme.QuasicoherentAlgebra.ringSheaf 𝒜) (psiPresheafHom 𝒜 F φ)

/-- The defining property of the lift: it agrees with the presheaf-level comparison on the image
of the sheafification unit. -/
theorem ungradedLift_totalUnit (W : (Opens ↥X)ᵒᵖ) (z : (symPre F).Total W) :
    ((ungradedLift 𝒜 F φ).hom.app W).hom
        ((symPre F).totalUnit (Opens.grothendieckTopology (X : TopCat)) W z) =
      psiTotal 𝒜 F φ W z :=
  congrArg (fun t : (symPre F).totalPresheaf ⟶ _ => RingCat.Hom.hom (t.app W) z)
    ((symPre F).toTotalSheaf_totalSheafLift (Opens.grothendieckTopology (X : TopCat))
      (Scheme.QuasicoherentAlgebra.ringSheaf 𝒜) (psiPresheafHom 𝒜 F φ))

/-- The lift, as a morphism of sheaves of commutative rings. The underlying morphism of sheaves
of rings is unchanged: `Stacks.CommRingSheaf.ofRingCat` keeps the carrier and the ring
operations. -/
def commLift : (Scheme.Modules.symmetricAlgebraSheaf X F).right ⟶ 𝒜.right :=
  ObjectProperty.homMk
    { app := fun W => @CommRingCat.ofHom
        ((Scheme.Modules.symmetricAlgebraSheaf X F).right.obj.obj W) (algSections 𝒜 W)
        inferInstance inferInstance ((ungradedLift 𝒜 F φ).hom.app W).hom
      naturality := fun _W _W' g => by
        ext x
        exact congrArg (fun ψ => RingCat.Hom.hom ψ x)
          ((ungradedLift 𝒜 F φ).hom.naturality g) }

/-- The lift is compatible with the two structure morphisms, which is the condition for it to be
a morphism in `Under X.sheaf`. -/
theorem structureMap_comp_commLift :
    (Scheme.Modules.symmetricAlgebraSheaf X F).hom ≫ commLift 𝒜 F φ = 𝒜.hom :=
  CategoryTheory.Sheaf.hom_ext
    (NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun r =>
      (ungradedLift_totalUnit 𝒜 F φ W ((symPre F).structureMap W r)).trans
        (psiTotal_structureMap 𝒜 F φ W r))))

/-- **The ungraded, sectionwise universal property of the symmetric algebra of a module sheaf**: a
morphism of module sheaves `φ : F ⟶ 𝒜.underlyingModule` into an algebra sheaf `𝒜` extends to a
morphism of algebra sheaves `Sym(F) ⟶ 𝒜`.

Its defining property is `Stacks.SymAlgSheaf.algebraLift_ungradedIncl_gen`: the extension
restricts to `φ` in degree one. Uniqueness is not claimed; see the implementation notes. -/
@[ega "II 1.7.14" "partial"]
def algebraLift : (Scheme.Modules.symmetricAlgebraSheaf X F : X.QuasicoherentAlgebra) ⟶ 𝒜 :=
  Under.homMk (commLift 𝒜 F φ) (structureMap_comp_commLift 𝒜 F φ)

/-- **The lift restricts to `φ` in degree one**: on the image in the ungraded ring sheaf of a
degree-one local section of `Sym(F)` coming from a local section `s` of `F`, the lift takes the
value `φ s`. -/
theorem algebraLift_ungradedIncl_gen (W : (Opens ↥X)ᵒᵖ) (s : F.val.obj W) :
    ((algebraLift 𝒜 F φ).right.hom.app W).hom
        ((Scheme.Modules.symmetricAlgebra X F).ungradedIncl 1
          ((Scheme.Modules.symmetricAlgebraGen X F).val.app W s)) =
      φ.val.app W s := by
  refine (ungradedLift_totalUnit 𝒜 F φ W ((symPre F).incl 1
    ((Scheme.Modules.symmetricAlgebraGen X F).val.app W s))).trans ?_
  rw [psiTotal_incl]
  exact congrArg (fun t : F ⟶ underlyingModule 𝒜 => t.val.app W s)
    (symmetricAlgebraGen_comp_descHom 𝒜 F φ)

end Lift

end Stacks.SymAlgSheaf

end
