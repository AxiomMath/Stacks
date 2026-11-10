module

public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafUniversal
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedFunctorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ungraded universal property of a symmetric algebra, as a bijection

Let `X` be a scheme, let `A` be a sheaf of graded algebras over `𝒪_X` with commuting homogeneous
multiplication, and let `𝒜` be a sheaf of commutative `𝒪_X`-algebras. The ungraded realization
`Stacks.RelativeSpec.ungradedAlgebraSheaf` of `A` is again a sheaf of commutative `𝒪_X`-algebras,
and this file identifies the morphisms out of it:

`(ungradedAlgebraSheaf X A hA ⟶ 𝒜) ≃ (F ⟶ 𝒜.underlyingModule)`

whenever `A` is a symmetric algebra of `F` in the graded sense, the bijection being restriction
to the degree-one summand.

## Main definitions

* `Stacks.RelativeSpec.algebraPresheaf`: the presheaf of commutative rings underlying an algebra
  sheaf, on `Opens X`.
* `Stacks.RelativeSpec.ungradedTotal` and `ungradedCommHom`: a unital homomorphism of graded
  algebras into `Stacks.SymAlgSheaf.constGraded 𝒜`, summed over the degrees, as an additive map
  on the sections of the ungraded realization and as a morphism of presheaves of commutative
  rings out of it.
* `Stacks.RelativeSpec.pieceHom` and `unitalHomOfCommHom`: the converse passage, reading a
  morphism of presheaves of commutative rings out of the ungraded realization as a family of
  morphisms of modules `Aₙ ⟶ 𝒜`, i.e. as a unital homomorphism into `constGraded 𝒜`.
* `Stacks.RelativeSpec.ungradedCommHomEquiv`: those two passages, as a bijection.
* `Stacks.RelativeSpec.ungradedAlgebraSheafHomEquiv`: the universal property of sheafification,
  read in the category of algebra sheaves.
* `Stacks.RelativeSpec.unitalHomEquivModuleHom`: the graded universal property of a symmetric
  algebra, read at `constGraded 𝒜`.
* `Stacks.RelativeSpec.ungradedAlgebraSheafModuleHomEquiv`: the ungraded universal property, the
  composite of the three bijections above.

## Main results

* `Stacks.RelativeSpec.ungradedAlgebraSheafModuleHomEquiv_apply_val_app`: the bijection is
  restriction to the degree-one summand, computed on local sections.
* `Stacks.RelativeSpec.ungradedAlgebraSheafModuleHomEquiv_comp`: the bijection is natural in the
  target algebra sheaf.
* `Stacks.RelativeSpec.structureMap_comp_ungradedCommHom`: the summed homomorphism carries the
  structure map `r ↦ r • 1` of the ungraded realization to the structure morphism of `𝒜`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SymAlgSheaf

universe u

namespace Stacks.RelativeSpec

/-- The presheaf of commutative rings underlying an algebra sheaf, on the opens of the
scheme. -/
abbrev algebraPresheaf {X : Scheme.{u}} (𝒜 : AlgebraSheaf X) :
    (Opens X)ᵒᵖ ⥤ CommRingCat.{u} := 𝒜.right.obj

variable {X : Scheme.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
  (𝒜 : AlgebraSheaf X)

/-! ### From a unital homomorphism into the degenerate grading -/

section OfUnitalHom

variable (ψ : SheafOfModules.GradedAlgebra.UnitalHom A (constGraded 𝒜))

/-- The degree-`n` component of a unital homomorphism into the degenerately graded `𝒜`, on the
sections over an open, as an additive map. -/
def ungradedAdd (n : ℤ) (W : (Opens X)ᵒᵖ) :
    ((A.piece n).val.obj W : Type u) →+ algSections 𝒜 W :=
  AddMonoidHom.mk' (fun x => ((ψ.app n).val.app W) x)
    (fun x y => map_add ((ψ.app n).val.app W).hom x y)

/-- A unital homomorphism into the degenerately graded `𝒜`, summed over the degrees: a section of
`⨁ₙ Aₙ(W)` is sent to the sum of the images of its homogeneous components. -/
def ungradedTotal (W : (Opens X)ᵒᵖ) :
    A.toPresheafGradedAlgebra.Total W →+ algSections 𝒜 W :=
  DirectSum.toAddMonoid fun n => ungradedAdd A 𝒜 ψ n W

/-- The summed homomorphism is the given degree-`n` component on a homogeneous local section. -/
theorem ungradedTotal_incl (n : ℤ) (W : (Opens X)ᵒᵖ) (x : (A.piece n).val.obj W) :
    ungradedTotal A 𝒜 ψ W (A.toPresheafGradedAlgebra.incl n x) = ((ψ.app n).val.app W) x :=
  DirectSum.toAddMonoid_of _ _ _

/-- The summed homomorphism is unital. -/
theorem ungradedTotal_one (W : (Opens X)ᵒᵖ) : ungradedTotal A 𝒜 ψ W 1 = 1 := by
  rw [A.toPresheafGradedAlgebra.one_eq_incl, ungradedTotal_incl]
  exact ψ.map_one W

/-- The summed homomorphism is multiplicative on the sections of the ungraded realization. -/
theorem ungradedTotal_mul (W : (Opens X)ᵒᵖ) (a b : A.toPresheafGradedAlgebra.Total W) :
    ungradedTotal A 𝒜 ψ W (a * b) =
      ungradedTotal A 𝒜 ψ W a * ungradedTotal A 𝒜 ψ W b := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | incl i x =>
      induction b using Stacks.GradedAlgebra.incl_induction with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | incl j y =>
          rw [Stacks.GradedAlgebra.incl_mul_incl, ungradedTotal_incl, ungradedTotal_incl,
            ungradedTotal_incl]
          exact ψ.map_mul i j W x y
      | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]

/-- The summed homomorphism commutes with restriction. -/
theorem ungradedTotal_naturality {W W' : (Opens X)ᵒᵖ} (f : W ⟶ W')
    (a : A.toPresheafGradedAlgebra.Total W) :
    ungradedTotal A 𝒜 ψ W' (A.toPresheafGradedAlgebra.totalRestrict f a) =
      (𝒜.right.obj.map f).hom (ungradedTotal A 𝒜 ψ W a) := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | incl i x =>
      rw [Stacks.GradedAlgebra.totalRestrict_incl, ungradedTotal_incl, ungradedTotal_incl]
      exact PresheafOfModules.naturality_apply ((ψ.app i).val) f x
  | add a a' ha ha' =>
      rw [map_add (A.toPresheafGradedAlgebra.totalRestrict f),
        map_add (ungradedTotal A 𝒜 ψ W'), ha, ha', map_add (ungradedTotal A 𝒜 ψ W),
        map_add (𝒜.right.obj.map f).hom]

/-- The summed homomorphism is `𝒪_X`-semilinear on the sections of the ungraded realization. -/
theorem ungradedTotal_smul (W : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W)
    (a : A.toPresheafGradedAlgebra.Total W) :
    ungradedTotal A 𝒜 ψ W (r • a) = (𝒜.hom.hom.app W).hom r * ungradedTotal A 𝒜 ψ W a := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | incl i x =>
      rw [← Stacks.GradedAlgebra.incl_smul, ungradedTotal_incl, ungradedTotal_incl]
      exact map_smul ((ψ.app i).val.app W).hom r x
  | add a a' ha ha' =>
      rw [smul_add, map_add (ungradedTotal A 𝒜 ψ W), ha, ha',
        map_add (ungradedTotal A 𝒜 ψ W), mul_add]

/-- The summed homomorphism carries the structure map `r ↦ r • 1` of the ungraded realization to
the structure morphism of `𝒜`. -/
theorem ungradedTotal_structureMap (W : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W) :
    ungradedTotal A 𝒜 ψ W (A.toPresheafGradedAlgebra.structureMap W r) =
      (𝒜.hom.hom.app W).hom r := by
  change ungradedTotal A 𝒜 ψ W (r • (1 : A.toPresheafGradedAlgebra.Total W)) = _
  rw [ungradedTotal_smul, ungradedTotal_one, mul_one]

/-- A unital homomorphism into the degenerately graded `𝒜`, as a morphism of presheaves of
commutative rings out of the ungraded realization. -/
def ungradedCommHom : ungradedCommPresheaf X A hA ⟶ algebraPresheaf 𝒜 where
  app W := @CommRingCat.ofHom ((ungradedCommPresheaf X A hA).obj W) (algSections 𝒜 W)
    inferInstance inferInstance
    { toFun := ungradedTotal A 𝒜 ψ W
      map_one' := ungradedTotal_one A 𝒜 ψ W
      map_mul' := ungradedTotal_mul A 𝒜 ψ W
      map_zero' := map_zero _
      map_add' := map_add _ }
  naturality _W _W' f := CommRingCat.hom_ext
    (RingHom.ext fun a => ungradedTotal_naturality A 𝒜 ψ f a)

/-- On sections, the morphism of presheaves is the summed homomorphism. -/
theorem ungradedCommHom_apply (W : (Opens X)ᵒᵖ) (a : A.toPresheafGradedAlgebra.Total W) :
    ((ungradedCommHom A hA 𝒜 ψ).app W).hom a = ungradedTotal A 𝒜 ψ W a := rfl

/-- The morphism of presheaves attached to a unital homomorphism is a morphism over the structure
sheaf. -/
theorem structureMap_comp_ungradedCommHom :
    ungradedCommStructureMap X A hA ≫ ungradedCommHom A hA 𝒜 ψ = 𝒜.hom.hom :=
  NatTrans.ext (funext fun W => CommRingCat.hom_ext
    (RingHom.ext fun r => ungradedTotal_structureMap A 𝒜 ψ W r))

end OfUnitalHom

/-! ### From a morphism out of the ungraded realization -/

section OfCommHom

variable (u : ungradedCommPresheaf X A hA ⟶ algebraPresheaf 𝒜)
  (hu : ungradedCommStructureMap X A hA ≫ u = 𝒜.hom.hom)

/-- The degree-`n` part of a morphism of presheaves of rings out of the ungraded realization,
on the sections over an open, as an additive map. -/
def pieceAdd (n : ℤ) (W : (Opens X)ᵒᵖ) :
    ((A.piece n).val.obj W : Type u) →+ algSections 𝒜 W :=
  AddMonoidHom.mk' (fun x => (u.app W).hom (A.toPresheafGradedAlgebra.incl n x))
    (fun x y => by
      rw [Stacks.GradedAlgebra.incl_add]
      exact map_add (u.app W).hom _ _)

/-- Scaling a homogeneous local section is multiplying by the structure map in the ungraded
realization. -/
theorem structureMap_mul_incl (n : ℤ) (W : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W)
    (x : (A.piece n).val.obj W) :
    A.toPresheafGradedAlgebra.structureMap W r * A.toPresheafGradedAlgebra.incl n x =
      A.toPresheafGradedAlgebra.incl n (r • x) := by
  rw [Stacks.GradedAlgebra.incl_smul]
  change r • (1 : A.toPresheafGradedAlgebra.Total W) * A.toPresheafGradedAlgebra.incl n x = _
  rw [Stacks.GradedAlgebra.smul_mul_eq, one_mul]

include hu in
/-- The degree-`n` part of a morphism over the base is `𝒪_X`-semilinear. -/
theorem pieceAdd_smul (n : ℤ) (W : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj W)
    (x : (A.piece n).val.obj W) :
    pieceAdd A hA 𝒜 u n W (r • x) =
      (𝒜.hom.hom.app W).hom r * pieceAdd A hA 𝒜 u n W x := by
  have hσ : (u.app W).hom (A.toPresheafGradedAlgebra.structureMap W r) =
      (𝒜.hom.hom.app W).hom r :=
    congrArg (fun k : X.sheaf.obj.obj W ⟶ 𝒜.right.obj.obj W => k.hom r)
      (NatTrans.congr_app hu W)
  change (u.app W).hom (A.toPresheafGradedAlgebra.incl n (r • x)) = _
  exact (congrArg (u.app W).hom (structureMap_mul_incl A n W r x).symm).trans
    ((map_mul (u.app W).hom _ _).trans
      (congrArg (fun z => z * (u.app W).hom (A.toPresheafGradedAlgebra.incl n x)) hσ))

/-- The degree-`n` part of a morphism of presheaves of rings out of the ungraded realization,
on the sections over one open, as a morphism of modules. -/
def pieceModuleHom (n : ℤ) (W : (Opens X)ᵒᵖ) :
    (A.piece n).val.obj W ⟶ (AlgebraSheaf.underlyingModule 𝒜).val.obj W :=
  ModuleCat.homMk (AddCommGrpCat.ofHom (pieceAdd A hA 𝒜 u n W)) (fun r => by
    ext x
    exact (pieceAdd_smul A hA 𝒜 u hu n W r x).symm)

/-- On sections, the degree-`n` part is the morphism evaluated at a homogeneous section. -/
theorem pieceModuleHom_apply (n : ℤ) (W : (Opens X)ᵒᵖ) (x : (A.piece n).val.obj W) :
    (pieceModuleHom A hA 𝒜 u hu n W) x =
      (u.app W).hom (A.toPresheafGradedAlgebra.incl n x) := rfl

/-- A morphism of presheaves of commutative rings out of the ungraded realization, on the
sections over one open, as an additive map on the direct sum of the homogeneous components. -/
def commHomAdd (W : (Opens X)ᵒᵖ) :
    A.toPresheafGradedAlgebra.Total W →+ algSections 𝒜 W :=
  AddMonoidHom.mk' (fun a => (u.app W).hom a) (fun a b => map_add (u.app W).hom a b)

/-- On sections, the additive map is the morphism itself. -/
theorem commHomAdd_apply (W : (Opens X)ᵒᵖ) (a : A.toPresheafGradedAlgebra.Total W) :
    commHomAdd A hA 𝒜 u W a = (u.app W).hom a := rfl

/-- The degree-`n` part of a morphism of presheaves of rings out of the ungraded realization,
as a morphism of sheaves of modules into the underlying module of the algebra. -/
def pieceHom (n : ℤ) : A.piece n ⟶ AlgebraSheaf.underlyingModule 𝒜 where
  val :=
    { app := pieceModuleHom A hA 𝒜 u hu n
      naturality := fun f => by
        ext x
        exact (congrArg (u.app _).hom
            (A.toPresheafGradedAlgebra.totalRestrict_incl f n x)).symm.trans
          (ConcreteCategory.congr_hom (u.naturality f)
            (A.toPresheafGradedAlgebra.incl n x)) }

/-- On sections, the degree-`n` part is the morphism evaluated at a homogeneous section. -/
theorem pieceHom_apply (n : ℤ) (W : (Opens X)ᵒᵖ) (x : (A.piece n).val.obj W) :
    ((pieceHom A hA 𝒜 u hu n).val.app W) x =
      (u.app W).hom (A.toPresheafGradedAlgebra.incl n x) := rfl

/-- A morphism of presheaves of commutative rings out of the ungraded realization of a sheaf of
graded algebras, over the base, as a unital homomorphism into the degenerately graded target. -/
def unitalHomOfCommHom : SheafOfModules.GradedAlgebra.UnitalHom A (constGraded 𝒜) where
  app n := pieceHom A hA 𝒜 u hu n
  map_mul i j W x y :=
    (congrArg (u.app W).hom
      (Stacks.GradedAlgebra.incl_mul_incl A.toPresheafGradedAlgebra i j x y)).symm.trans
        (map_mul (u.app W).hom _ _)
  map_one W :=
    (congrArg (u.app W).hom
      (Stacks.GradedAlgebra.one_eq_incl A.toPresheafGradedAlgebra W)).symm.trans
        (map_one (u.app W).hom)

end OfCommHom

/-! ### The two passages are inverse -/

section Equiv

/-- The two passages are inverse, in one direction: summing the components of a unital
homomorphism and taking the components again returns it. -/
theorem unitalHomOfCommHom_ungradedCommHom
    (ψ : SheafOfModules.GradedAlgebra.UnitalHom A (constGraded 𝒜)) :
    unitalHomOfCommHom A hA 𝒜 (ungradedCommHom A hA 𝒜 ψ)
        (structureMap_comp_ungradedCommHom A hA 𝒜 ψ) = ψ :=
  SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => SheafOfModules.hom_ext <|
    PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext <| LinearMap.ext fun x =>
      (pieceModuleHom_apply A hA 𝒜 (ungradedCommHom A hA 𝒜 ψ)
        (structureMap_comp_ungradedCommHom A hA 𝒜 ψ) n W x).trans (ungradedTotal_incl A 𝒜 ψ n W x)

/-- Summing the components of a morphism out of the ungraded realization returns that morphism,
on the sections over an open. -/
theorem ungradedTotal_unitalHomOfCommHom
    (u : ungradedCommPresheaf X A hA ⟶ algebraPresheaf 𝒜)
    (hu : ungradedCommStructureMap X A hA ≫ u = 𝒜.hom.hom) (W : (Opens X)ᵒᵖ) :
    ungradedTotal A 𝒜 (unitalHomOfCommHom A hA 𝒜 u hu) W = commHomAdd A hA 𝒜 u W := by
  refine DirectSum.addHom_ext fun i x => ?_
  exact (ungradedTotal_incl A 𝒜 (unitalHomOfCommHom A hA 𝒜 u hu) i W x).trans
    (pieceModuleHom_apply A hA 𝒜 u hu i W x)

/-- The two passages are inverse, in the other direction. -/
theorem ungradedCommHom_unitalHomOfCommHom
    (u : ungradedCommPresheaf X A hA ⟶ algebraPresheaf 𝒜)
    (hu : ungradedCommStructureMap X A hA ≫ u = 𝒜.hom.hom) :
    ungradedCommHom A hA 𝒜 (unitalHomOfCommHom A hA 𝒜 u hu) = u :=
  NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun a =>
    DFunLike.congr_fun (ungradedTotal_unitalHomOfCommHom A hA 𝒜 u hu W) a))

/-- Morphisms of presheaves of commutative rings out of the ungraded realization of a sheaf of
graded algebras, over the base, are exactly the unital homomorphisms into the degenerately
graded target. -/
def ungradedCommHomEquiv :
    {u : ungradedCommPresheaf X A hA ⟶ algebraPresheaf 𝒜 //
        ungradedCommStructureMap X A hA ≫ u = 𝒜.hom.hom} ≃
      SheafOfModules.GradedAlgebra.UnitalHom A (constGraded 𝒜) where
  toFun u := unitalHomOfCommHom A hA 𝒜 u.1 u.2
  invFun ψ := ⟨ungradedCommHom A hA 𝒜 ψ, structureMap_comp_ungradedCommHom A hA 𝒜 ψ⟩
  left_inv u := Subtype.ext (ungradedCommHom_unitalHomOfCommHom A hA 𝒜 u.1 u.2)
  right_inv ψ := unitalHomOfCommHom_ungradedCommHom A hA 𝒜 ψ

end Equiv

/-! ### Sheafification -/

section Sheafify

/-- Morphisms of algebra sheaves out of the ungraded realization of a sheaf of graded algebras
are exactly the morphisms of presheaves of commutative rings out of the direct sum of its
homogeneous components which are compatible with the structure maps. -/
def ungradedAlgebraSheafHomEquiv :
    (ungradedAlgebraSheaf X A hA ⟶ 𝒜) ≃
      {u : ungradedCommPresheaf X A hA ⟶ algebraPresheaf 𝒜 //
        ungradedCommStructureMap X A hA ≫ u = 𝒜.hom.hom} where
  toFun f := ⟨ungradedCommToSheaf X A hA ≫ f.right.hom,
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k : X.sheaf ⟶ 𝒜.right => k.hom) (Under.w f))⟩
  invFun u := Under.homMk
    (((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
      CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA) 𝒜.right).symm u.1)
    (CategoryTheory.Sheaf.hom_ext ((Category.assoc _ _ _).trans
      ((congrArg (fun k => ungradedCommStructureMap X A hA ≫ k)
        (((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
          CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA) 𝒜.right).apply_symm_apply
            u.1)).trans u.2)))
  left_inv f := Under.UnderMorphism.ext
    (((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
      CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA) 𝒜.right).symm_apply_apply f.right)
  right_inv u := Subtype.ext
    (((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
      CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA) 𝒜.right).apply_symm_apply u.1)

end Sheafify

/-! ### The ungraded universal property -/

section Universal

variable {F : SheafOfModules.{u} X.ringCatSheaf} (gen : F ⟶ A.piece 1)
  (hsym : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A gen)

/-- The unital homomorphisms of a symmetric algebra of `F` into a degenerately graded algebra
sheaf are exactly the morphisms of modules from `F` into its underlying module. -/
def unitalHomEquivModuleHom :
    SheafOfModules.GradedAlgebra.UnitalHom A (constGraded 𝒜) ≃
      (F ⟶ AlgebraSheaf.underlyingModule 𝒜) where
  toFun ψ := gen ≫ ψ.app 1
  invFun φ := hsym.isUniversal.desc (constGraded 𝒜) φ (pairwiseCommutes_constGraded 𝒜 F φ)
  left_inv ψ :=
    (hsym.isUniversal.desc_unique (constGraded 𝒜) (gen ≫ ψ.app 1)
      (pairwiseCommutes_constGraded 𝒜 F (gen ≫ ψ.app 1)) rfl).symm
  right_inv φ :=
    hsym.isUniversal.desc_extends (constGraded 𝒜) φ (pairwiseCommutes_constGraded 𝒜 F φ)

/-- The ungraded universal property of the symmetric algebra of a sheaf of modules on a scheme:
morphisms of sheaves of commutative `𝒪_X`-algebras `Sym(F) ⟶ 𝒜` out of the ungraded
realization of a symmetric algebra of `F` are exactly the morphisms of `𝒪_X`-modules `F ⟶ 𝒜`
into the module underlying `𝒜`. -/
@[ega "IV 18.5.2" "partial"]
def ungradedAlgebraSheafModuleHomEquiv :
    (ungradedAlgebraSheaf X A hA ⟶ 𝒜) ≃ (F ⟶ AlgebraSheaf.underlyingModule 𝒜) :=
  (ungradedAlgebraSheafHomEquiv A hA 𝒜).trans
    ((ungradedCommHomEquiv A hA 𝒜).trans (unitalHomEquivModuleHom A 𝒜 gen hsym))

/-- The bijection of the ungraded universal property is restriction to the degree-one summand: on
a local section `s` of `F`, the module morphism attached to a morphism of algebra sheaves `f` is
`f` evaluated at the degree-one local section of `Sym(F)` determined by `s`. -/
theorem ungradedAlgebraSheafModuleHomEquiv_apply_val_app
    (f : ungradedAlgebraSheaf X A hA ⟶ 𝒜) (U : X.Opens) (s : F.val.obj (op U)) :
    ((ungradedAlgebraSheafModuleHomEquiv A hA 𝒜 gen hsym f).val.app (op U)) s =
      (f.right.hom.app (op U)).hom
        (ungradedAlgebraSheafIncl X A hA 1 U (gen.val.app (op U) s)) := rfl

/-- The bijection of the ungraded universal property is natural in the target algebra sheaf:
postcomposing a morphism of algebra sheaves `Sym(F) ⟶ 𝒜` with `h : 𝒜 ⟶ ℬ` postcomposes the
module morphism it restricts to with the induced morphism of underlying modules. -/
theorem ungradedAlgebraSheafModuleHomEquiv_comp (ℬ : AlgebraSheaf X)
    (f : ungradedAlgebraSheaf X A hA ⟶ 𝒜) (h : 𝒜 ⟶ ℬ) :
    ungradedAlgebraSheafModuleHomEquiv A hA ℬ gen hsym (f ≫ h) =
      ungradedAlgebraSheafModuleHomEquiv A hA 𝒜 gen hsym f ≫
        AlgebraSheaf.underlyingModuleMap h :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

end Universal

end Stacks.RelativeSpec

end
