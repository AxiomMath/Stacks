module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.DeRham.Cohomology.CechTermPairing
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationDerivedMap
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.Homology.TensorComplex.SingleTensor

/-!
# The Čech-term pairing as a map out of a tensor product of complexes

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and let `μ : ℳ × 𝒩 ⟶ 𝒫` be a pairing of
`𝒪_X`-modules. `Stacks.Perfect.CechPairing.termPair` is the induced pairing on every term of the
extended alternating Čech complex of `f₁, …, f_c`, and
`Stacks.Perfect.CechPairing.termPair_dif` says it commutes with the differentials. This file
turns that family of pairings into a single morphism of cochain complexes out of the total
tensor complex

`Tot(ℳ[0] ⊗_{𝒪_X} 𝓝^•) ⟶ 𝓟^•`,

which is the shape in which the canonical map `DerivedTensorProduct.toTensor` out of a derived
tensor product can be composed with it.

## Main definitions

* `Stacks.Perfect.CechPairing.cechTensorTerm`: the pairing on one term, as a morphism out of the
  tensor product sheaf `ℳ ⊗_{𝒪_X} 𝓝^n`.
* `Stacks.Perfect.CechPairing.cechTensorCplx`: the morphism of `ℕ`-indexed cochain complexes
  `ℳ ⊗_{𝒪_X} 𝓝^• ⟶ 𝓟^•`, where the source is `ℳ ⊗_{𝒪_X} -` applied termwise.
* `Stacks.Perfect.CechPairing.cechTensorTot`: the morphism out of the total tensor complex
  `Tot(ℳ[0] ⊗_{𝒪_X} 𝓝^•)` of the extensions by zero to `ℤ`-indexed complexes.

## Main results

* `Stacks.Perfect.CechPairing.cechTensorTerm_tensorSheafUnit`: the term-level pairing on a local
  pure tensor is `μ` paired into that term.
* `Stacks.Perfect.CechPairing.cechTensorCplx_f_zero`: in degree zero the morphism of complexes
  is the descent of `μ` itself, which is what the augmentation of [Stacks, Tag 0G7L] sees.
* `Stacks.Perfect.CechPairing.cechTensorCplx_comp_augmentationComplex`: **the pairing is
  compatible with the augmentation of [Stacks, Tag 0G7L]** — followed by the projection onto the
  degree-zero term it is `ℳ ⊗ -` of that projection followed by `μ`. This is what computes the
  counit of a candidate multiplication built in the Čech model, by
  `Stacks.Cohomology.SupportedComplexes.cechToDerivedSupport_comp_counit`.

## Implementation notes

**Why the total complex costs nothing.** `ℳ[0] ⊗ 𝓝^•` is the total complex of the tensor double
complex, so its degree-`n` term is a biproduct over the pairs `(a, b)` with `a + b = n`, of
which only `(0, n)` contributes. `TotalTensorComplex.SingleTensor.singleTensorIso` records that,
so the morphism below is built out of the termwise `ℳ ⊗ -` and no sign bookkeeping of the total
complex is redone here.

**The two indexings.** The extended alternating Čech complex is `ℕ`-indexed and the derived
category works with its extension by zero to `ℤ`. Extension by zero commutes with the termwise
functor `ℳ ⊗ -`, by `Stacks.DerivedIndexing.mapExtendIso`, so the `ℤ`-indexed morphism is the
extension of the `ℕ`-indexed one and the degreewise content is unchanged.

**Why the degree-zero component needs an abstract lemma.** The two sides of
`cechTensorCplx_comp_augmentationComplex` in degree zero are composites of identity morphisms
and of the canonical identifications `HomologicalComplex.singleObjXSelf` at objects which are
definitionally but not syntactically equal — `(cplx f ℱ).X 0` against `ℱ`, and
`(ℳ ⊗ -)(((single).obj 𝒩).X 0)` against `((single).obj (ℳ ⊗ 𝒩)).X 0`. Neither
`Category.id_comp` nor `rfl` applies to such a goal, and rewriting under `(ℳ ⊗ -).map` fails at
implicit transparency. The step is therefore hoisted into `comp_id_comp_eq_of_map`, stated at
variable categories with the objects implicit and the morphisms explicit, and applied with
`exact`, which leaves the definitional matching to unification.

**The monoidal seating.** The monoidal structure on `X.Modules` whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` is a named local instance rather than a synthesized
one, for the reason recorded in
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/TensorHomAdjunction.lean`: over the site
`Opens X` the universe of the site and the universe of the sections of `𝒪_X` coincide, so
instance search would have to solve `max ?u ?v =?= u` with both unknown.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.MonoidalCategory
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Perfect.CechPairing

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-- The monoidal structure on `X.Modules` whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`, named rather than synthesized. -/
local instance monoidalSchemeModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategorySheafTensor
    (J := Opens.grothendieckTopology X) X.toRingedSpace.sheaf

/-- The tensor product of sheaves of modules is bilinear on morphisms, named rather than
synthesized. -/
local instance monoidalPreadditiveSchemeModules (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  SheafOfModules.monoidalPreadditiveSheafTensor
    (J := Opens.grothendieckTopology X) X.toRingedSpace.sheaf

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))
variable {M N P : X.Modules} (μ : Stacks.BilinearMap M.val N.val P.val)

/-! ### The pairing on one term -/

/-- **The second-variable action of the tensor product of sheaves of modules on a local pure
tensor.** `ℳ ⊗ -` applied to `g` sends the class of `x ⊗ y` to the class of `x ⊗ g(y)`: the
tensor product sheaf is a sheafification, and this is the naturality of its unit together with
the formula for the objectwise tensor product of two morphisms. -/
theorem sheafTensorObj_map_app_tensorSheafUnit (A : X.Modules) {B B' : X.Modules} (g : B ⟶ B')
    (V : (Opens ↥X)ᵒᵖ) (x : A.val.obj V) (y : B.val.obj V) :
    (((sheafTensor X.toRingedSpace.sheaf).obj A).map g).val.app V
        ((PresheafOfModules.tensorSheafUnit A B).app V (x ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit A B').app V (x ⊗ₜ g.val.app V y) :=
  (PresheafOfModules.unit_naturality_apply (α := 𝟙 X.ringCatSheaf.obj)
      (PresheafOfModules.tensorHom (𝟙 A.val) g.val) V (x ⊗ₜ y)).trans
    (congrArg ((PresheafOfModules.tensorSheafUnit A B').app V)
      (PresheafOfModules.tensorHom_tmul (𝟙 A.val) g.val V x y))

/-- **The Čech-term pairing on one term, as a morphism out of the tensor product sheaf.** The
pairing `Stacks.Perfect.CechPairing.termPair` is given on local sections; this is the morphism
`ℳ ⊗_{𝒪_X} 𝓝^n ⟶ 𝓟^n` it descends to. -/
def cechTensorTerm (n : ℕ) :
    ((sheafTensor X.toRingedSpace.sheaf).obj M).obj (term f N n) ⟶ term f P n :=
  PresheafOfModules.tensorSheafDesc (F := M) (G := term f N n) (Q := term f P n)
    (PresheafOfModules.ofBilinear (termPair f μ n))

/-- The term-level pairing on a local pure tensor is the Čech-term pairing. -/
theorem cechTensorTerm_tensorSheafUnit (n : ℕ) (V : (Opens ↥X)ᵒᵖ) (x : M.val.obj V)
    (y : (term f N n).val.obj V) :
    (cechTensorTerm f μ n).val.app V
        ((PresheafOfModules.tensorSheafUnit M (term f N n)).app V (x ⊗ₜ y)) =
      (termPair f μ n).app V x y :=
  (PresheafOfModules.tensorSheafDesc_unit _ V x y).trans
    (PresheafOfModules.ofBilinear_tmul (termPair f μ n) V x y)

/-! ### The morphism of `ℕ`-indexed complexes -/

/-- **The term-level pairings commute with the differentials.** This is
`Stacks.Perfect.CechPairing.termPair_dif`, read as an equation of morphisms out of the tensor
product sheaf through `PresheafOfModules.tensorSheaf_hom_ext`. -/
theorem cechTensorTerm_comp_dif (n : ℕ) :
    cechTensorTerm f μ n ≫ dif f P n =
      ((sheafTensor X.toRingedSpace.sheaf).obj M).map (dif f N n) ≫
        cechTensorTerm f μ (n + 1) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (F := M) (G := term f N n)
    (Q := term f P (n + 1)) fun V x y => ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ V _) ?_
  refine Eq.trans ?_ (SheafOfModules.comp_val_app_apply _ _ V _).symm
  refine Eq.trans
    (congrArg ((dif f P n).val.app V) (cechTensorTerm_tensorSheafUnit f μ n V x y)) ?_
  refine Eq.trans ?_ (congrArg ((cechTensorTerm f μ (n + 1)).val.app V)
    (sheafTensorObj_map_app_tensorSheafUnit M (dif f N n) V x y)).symm
  refine Eq.trans ?_
    (cechTensorTerm_tensorSheafUnit f μ (n + 1) V x ((dif f N n).val.app V y)).symm
  exact (termPair_dif f μ n V.unop x y).symm

/-- **The Čech-term pairing as a morphism of `ℕ`-indexed cochain complexes.** The source is
`ℳ ⊗_{𝒪_X} -` applied to every term of the extended alternating Čech complex of `𝒩`; the
differential condition is `cechTensorTerm_comp_dif`. -/
def cechTensorCplx :
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cplx f N) ⟶ cplx f P where
  f n := cechTensorTerm f μ n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    change cechTensorTerm f μ i ≫ (cplx f P).d i (i + 1) =
      ((sheafTensor X.toRingedSpace.sheaf).obj M).map ((cplx f N).d i (i + 1)) ≫
        cechTensorTerm f μ (i + 1)
    rw [show (cplx f P).d i (i + 1) = dif f P i from CochainComplex.of_d _ _ i,
      show (cplx f N).d i (i + 1) = dif f N i from CochainComplex.of_d _ _ i]
    exact cechTensorTerm_comp_dif f μ i

/-- In degree zero the morphism of complexes is the descent of `μ` itself. -/
theorem cechTensorCplx_f_zero : (cechTensorCplx f μ).f 0 = cechTensorTerm f μ 0 := rfl

/-! ### The morphism of `ℤ`-indexed complexes and out of the total complex -/

/-- **The Čech-term pairing on the extensions by zero to `ℤ`-indexed complexes.** Extension by
zero commutes with the termwise functor `ℳ ⊗_{𝒪_X} -`
(`Stacks.DerivedIndexing.mapExtendIso`), so this is the extension of `cechTensorCplx`. -/
def cechTensorExtend :
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((cplx f N).extend ComplexShape.embeddingUpNat) ⟶
      (cplx f P).extend ComplexShape.embeddingUpNat :=
  (Stacks.DerivedIndexing.mapExtendIso (tensorLeft M) ComplexShape.embeddingUpNat
      (cplx f N)).inv ≫
    HomologicalComplex.extendMap (cechTensorCplx f μ) ComplexShape.embeddingUpNat

/-- **The degreewise closed form of the `ℤ`-indexed pairing in a degree in the range of the
embedding**: the term-level pairing, read through the two canonical identifications of the
extensions with the terms of the `ℕ`-indexed complexes. -/
theorem cechTensorExtend_f (n : ℕ) :
    (cechTensorExtend f μ).f (n : ℤ) =
      (tensorLeft M).map
          (((cplx f N).extendXIso ComplexShape.embeddingUpNat
            (i := n) (i' := (n : ℤ)) (by simp)).hom) ≫
        cechTensorTerm f μ n ≫
          ((cplx f P).extendXIso ComplexShape.embeddingUpNat
            (i := n) (i' := (n : ℤ)) (by simp)).inv := by
  have h : ComplexShape.embeddingUpNat.f n = (n : ℤ) := by simp
  rw [cechTensorExtend, HomologicalComplex.comp_f,
    Stacks.DerivedIndexing.mapExtendIso_inv_f_eq (tensorLeft M) ComplexShape.embeddingUpNat
      (cplx f N) h,
    HomologicalComplex.extendMap_f (cechTensorCplx f μ) ComplexShape.embeddingUpNat h,
    Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- **The Čech-term pairing as a morphism out of the total tensor complex**,

`Tot(ℳ[0] ⊗_{𝒪_X} 𝓝^•) ⟶ 𝓟^•`.

This is `cechTensorExtend` preceded by
`TotalTensorComplex.SingleTensor.singleTensorIso`, which identifies the total tensor complex of
a complex with a module placed in degree zero with the termwise tensor product. It is the shape
in which the canonical map
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.toTensor` out of a derived tensor product
composes with the pairing. -/
def cechTensorTot :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M)).obj
        ((cplx f N).extend ComplexShape.embeddingUpNat) ⟶
      (cplx f P).extend ComplexShape.embeddingUpNat :=
  (TotalTensorComplex.SingleTensor.singleTensorIso M
      ((cplx f N).extend ComplexShape.embeddingUpNat)).hom ≫ cechTensorExtend f μ

/-- The morphism out of the total tensor complex is `cechTensorExtend` read through the
identification of the total complex, so it carries no information beyond the term-level
pairings. -/
theorem cechTensorTot_eq :
    cechTensorTot f μ =
      (TotalTensorComplex.SingleTensor.singleTensorIso M
          ((cplx f N).extend ComplexShape.embeddingUpNat)).hom ≫ cechTensorExtend f μ :=
  rfl

/-! ### The augmentation of Tag 0G7L sees the pairing in degree zero -/

/-- Cancelling a functor-image isomorphism and an isomorphism against a morphism, with two
identities inserted. Stated at variable categories with the objects implicit and the morphisms
explicit, because that is the only shape in which this step is affordable at the concrete
categories below: there the two sides are composites of identity morphisms at objects which are
definitionally but not syntactically equal, so neither `Category.id_comp` nor `rfl` applies. -/
theorem comp_id_comp_eq_of_map {C : Type*} [Category C] {D : Type*} [Category D] (F : D ⥤ C)
    {Y Y' : D} (a : Y ⟶ Y') (b : Y' ⟶ Y) (hab : a ≫ b = CategoryStruct.id Y) {Z B B' : C}
    (s : F.obj Y ⟶ Z) (r : Z ⟶ F.obj Y) (hsr : s ≫ r = CategoryStruct.id (F.obj Y))
    (w : F.obj Y ⟶ B) (i : B ⟶ B') :
    w ≫ CategoryStruct.id B ≫ i =
      F.map (CategoryStruct.id Y ≫ a) ≫ (F.map b ≫ s) ≫ r ≫ w ≫ i := by
  rw [Category.id_comp, Category.id_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map a) (F.map b), ← F.map_comp, hab, F.map_id, Category.id_comp,
    ← Category.assoc s r, hsr, Category.id_comp]

/-- **The pairing is compatible with the augmentation of [Stacks, Tag 0G7L].** Followed by the
projection of the Čech complex of `𝓟` onto its degree-zero term, the pairing is `ℳ ⊗ -` of the
projection for `𝓝` followed by the degree-zero pairing `ℳ ⊗ 𝓝 ⟶ 𝓟`.

This is the whole content of `Stacks.Perfect.CechPairing.termPair_zero` — the pairing in degree
zero *is* `μ` — and it is what computes the counit of a candidate multiplication built in the
Čech model, by
`Stacks.Cohomology.SupportedComplexes.cechToDerivedSupport_comp_counit`. -/
theorem cechTensorCplx_comp_augmentationComplex :
    cechTensorCplx f μ ≫ Augmentation.augmentationComplex f P =
      ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (Augmentation.augmentationComplex f N) ≫
        (Functor.mapHomologicalComplexSingleIso (tensorLeft M) 0 N).hom ≫
        (CochainComplex.single₀ X.Modules).map (cechTensorTerm f μ 0) := by
  have h0 : ∀ F : X.Modules, (Augmentation.augmentationComplex f F).f 0 =
      (extendedAlternatingCech f F).zeroIso.hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv := fun F => by
    simp [Augmentation.augmentationComplex, CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
  have hz : ∀ F : X.Modules, (extendedAlternatingCech f F).zeroIso = Iso.refl F := fun _ => rfl
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  match n with
  | 0 =>
      refine Eq.trans (HomologicalComplex.comp_f (cechTensorCplx f μ)
        (Augmentation.augmentationComplex f P) 0) ?_
      simp only [h0, hz, Iso.refl_hom, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f,
        Functor.mapHomologicalComplexSingleIso_hom_f_self, cechTensorCplx_f_zero]
      exact comp_id_comp_eq_of_map (tensorLeft M)
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 N).inv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 N).hom
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 N).inv_hom_id
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((tensorLeft M).obj N)).inv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((tensorLeft M).obj N)).hom
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((tensorLeft M).obj N)).inv_hom_id
        (cechTensorTerm f μ 0)
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 P).inv
  | (p + 1) =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 P (p + 1)
        (by omega)).eq_of_tgt _ _

end Stacks.Perfect.CechPairing

end
