module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorUnitFactor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparisonSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-! # The diagonal morphism of Stacks 0A93 at the structure sheaf

Let `(C, O)` be a ringed site, write `O[0]` for the structure sheaf placed in degree zero and
let `A` be a complex of `O`-modules. The diagonal morphism of Stacks 0A93 taken at `L = O[0]`,

`A ⟶ SheafHom(O[0], Tot(A ⊗_O O[0]))`,

followed by evaluation at the unit section, is the morphism `A ⟶ Tot(A ⊗_O O[0])` carrying a
homogeneous local section `x` to the local pure tensor `x ⊗ 1`, and that morphism is an
isomorphism of complexes. Dinaturality of the diagonal in its second variable then computes it
at an arbitrary complex `I` receiving a morphism `g : O[0] ⟶ I`: the diagonal at `I`, followed
by restriction along `g` and evaluation at the unit section, is that isomorphism followed by
`Tot(A ⊗_O g)`.

## Main results

* `AlgebraicGeometry.RingedSite.sheafTensorUnitIsoRight_hom_tmul_one`: the right unit
  constraint of `⊗_O` sends the local pure tensor of a section with the unit section back to
  that section.
* `AlgebraicGeometry.RingedSite.unitRightComponent_apply`: the degreewise collapse of
  `Tot(A ⊗_O O[0])` carries a section `x` to the local pure tensor `x ⊗ 1`.
* `AlgebraicGeometry.RingedSite.diagonalTensorUnit_apply`: the diagonal followed by evaluation at
  the unit section carries `x` to `x ⊗ 1`.
* `AlgebraicGeometry.RingedSite.isIso_diagonalTensorUnit`: that composite is an isomorphism of
  complexes.
* `AlgebraicGeometry.RingedSite.diagonalMap_comp_homMap_comp_structureSheafHomEvaluation`: the
  computation at an arbitrary second complex.
* `diagonalMap_comp_homMap_comp_homMap_comp_structureSheafHomEvaluation`, in the same
  namespace: the same computation with a further morphism `q : Tot(A ⊗_O I) ⟶ J` absorbed.

## References

* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Section 20.48 (Tag 06YM)](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The right unit constraint on local sections -/

/-- The unit of the sheafification adjunction for presheaves of `O`-modules. -/
abbrev sheafifyUnitApp
    (P : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    P ⟶ ((PresheafOfModules.sheafification (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app P

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A composite of morphisms of presheaves of modules acts on sections by composition. -/
private lemma comp_app_apply₅
    {P Q S : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj} (φ : P ⟶ Q)
    (ψ : Q ⟶ S) (U : X.Cᵒᵖ) (x : P.obj U) :
    ((φ ≫ ψ).app U) x = (ψ.app U) ((φ.app U) x) := rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A composite of morphisms of sheaves of modules acts on sections by composition. -/
private lemma comp_val_app_apply₅
    {P Q S : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : P ⟶ Q)
    (ψ : Q ⟶ S) (U : X.Cᵒᵖ) (x : P.val.obj U) :
    ((φ ≫ ψ).val.app U) x = (ψ.val.app U) ((φ.val.app U) x) := rfl

/-- The counit of the sheafification adjunction undoes its unit on the sections of a sheaf.
This is the triangle identity, read on sections. -/
private lemma counit_unit_apply₅
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (y : M.val.obj U) :
    ((PresheafOfModules.sheafificationAdjunction (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app M).val.app U
      ((sheafifyUnitApp X M.val).app U y) = y := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).right_triangle_components (Y := M)
  exact (comp_app_apply₅ X _ _ U y).symm.trans (congrArg (fun z => z.app U y) h)

/-- **The right unit constraint of `⊗_O` on local sections.** The local pure tensor of a
section `t` of `M` with the unit section `1` of the structure sheaf is carried back to `t`. -/
lemma sheafTensorUnitIsoRight_hom_tmul_one
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (t : M.val.obj U) :
    (sheafTensorUnitIsoRight.{u, u, u} X.O M).hom.val.app U
        ((sheafifyUnitApp X
          (M.val ⊗ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val)).app U
          (t ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
            (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))) = t := by
  have hcomp : (sheafTensorUnitIsoRight.{u, u, u} X.O M).hom =
      (PresheafOfModules.sheafification (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
          (ρ_ M.val).hom ≫
        (PresheafOfModules.sheafificationAdjunction
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app M := rfl
  rw [hcomp]
  refine Eq.trans (comp_val_app_apply₅ X _ _ U _) ?_
  refine Eq.trans (congrArg (fun y => ((PresheafOfModules.sheafificationAdjunction
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app M).val.app U y)
    (sheafification_map_unit_apply X (ρ_ M.val).hom U _)) ?_
  refine Eq.trans (counit_unit_apply₅ X M U _) ?_
  change (ConcreteCategory.hom (ρ_ (M.val.obj U)).hom)
    (t ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) = t
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  exact one_smul _ _

/-- **The right unit constraint of `⊗_O` read backwards on local sections.** -/
lemma sheafTensorUnitIsoRight_inv_apply
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (t : M.val.obj U) :
    (sheafTensorUnitIsoRight.{u, u, u} X.O M).inv.val.app U t =
      (sheafifyUnitApp X
        (M.val ⊗ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val)).app U
        (t ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) := by
  have key : ∀ z, (sheafTensorUnitIsoRight.{u, u, u} X.O M).inv.val.app U
      ((sheafTensorUnitIsoRight.{u, u, u} X.O M).hom.val.app U z) = z := fun z => by
    rw [← comp_val_app_apply₅, Iso.hom_inv_id]
    rfl
  exact (congrArg (fun y => (sheafTensorUnitIsoRight.{u, u, u} X.O M).inv.val.app U y)
    (sheafTensorUnitIsoRight_hom_tmul_one X M U t).symm).trans (key _)

/-! ### The total tensor product with the structure sheaf -/

variable [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

variable {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The inclusion of a single possibly-nonzero term of a colimit cofan is an isomorphism: the
inverse is the morphism out of the colimit which is the identity on that term and zero on the
others, all of which are zero objects. -/
private theorem isIso_cofan_inj_of_isZero₅ {D : Type*} [Category D] [HasZeroMorphisms D]
    {ι : Type*} {F : ι → D} (c : Limits.Cofan F) (hc : Limits.IsColimit c) (j : ι)
    (hz : ∀ i, i ≠ j → IsZero (F i)) : IsIso (c.inj j) := by
  classical
  let f (i : ι) : F i ⟶ F j := if h : i = j then eqToHom (congrArg F h) else 0
  refine ⟨⟨Limits.Cofan.IsColimit.desc hc f, ?_, ?_⟩⟩
  · rw [Limits.Cofan.IsColimit.fac]
    simp [f]
  · refine Limits.Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    rw [← Category.assoc, Limits.Cofan.IsColimit.fac]
    by_cases hi : i = j
    · subst i; simp [f]
    · exact (hz i hi).eq_of_src _ _

/-- **The summand of bidegree `(n, 0)` exhausts `Tot(A ⊗_O O[0])` in total degree `n`.** Every
other summand has the structure sheaf complex in a nonzero degree, where it vanishes. -/
theorem isIso_ιMapBifunctor_structureSheafComplex (n : ℤ) :
    IsIso (HomologicalComplex.ιMapBifunctor A (structureSheafComplex X)
      (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) n 0 n (by simp)) := by
  refine isIso_cofan_inj_of_isZero₅ _
    ((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O A
      (structureSheafComplex X)).toGradedObject.isColimitCofanMapObj _ n) _ ?_
  rintro ⟨⟨p, q⟩, hpq⟩ hb
  have hq0 : q ≠ 0 := by
    rintro rfl
    have hs : p + 0 = n := hpq
    obtain rfl : p = n := by omega
    exact hb rfl
  exact ((sheafTensor.{u, u, u, u, u} X.O).obj (A.X p)).map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q hq0)

/-- **The degreewise collapse `A^n ⟶ Tot(A ⊗_O O[0])^n`**: the right unit constraint read
backwards, followed by the inclusion of the summand of bidegree `(n, 0)`. -/
def unitRightComponent (n : ℤ) : A.X n ⟶ (tensorTotal X A (structureSheafComplex X)).X n :=
  (sheafTensorUnitIsoRight.{u, u, u} X.O (A.X n)).inv ≫
    HomologicalComplex.ιMapBifunctor A (structureSheafComplex X) (sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ) n 0 n (by simp) ≫
      (tensorTotalIsoTensorComplex X A (structureSheafComplex X)).inv.f n

/-- The degreewise collapse is an isomorphism. -/
instance isIso_unitRightComponent (n : ℤ) : IsIso (unitRightComponent X (A := A) n) := by
  have h₁ := isIso_ιMapBifunctor_structureSheafComplex X (A := A) n
  have h₂ : IsIso ((tensorTotalIsoTensorComplex X A (structureSheafComplex X)).inv.f n) :=
    (HomologicalComplex.eval (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) n).map_isIso
      (tensorTotalIsoTensorComplex X A (structureSheafComplex X)).inv
  change IsIso ((sheafTensorUnitIsoRight.{u, u, u} X.O (A.X n)).inv ≫
    HomologicalComplex.ιMapBifunctor A (structureSheafComplex X) (sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ) n 0 n (by simp) ≫
      (tensorTotalIsoTensorComplex X A (structureSheafComplex X)).inv.f n)
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h₁ h₂)

/-- **The degreewise collapse carries a section to the local pure tensor with the unit
section.** -/
lemma unitRightComponent_apply (n : ℤ) (W : X.C) (x : (A.X n).val.obj (op W)) :
    (unitRightComponent X (A := A) n).val.app (op W) x =
      tensorTotalSectionAt X A (structureSheafComplex X) W n 0 n (by omega) x
        (structureSheafOne X W) := by
  refine Eq.trans (comp_val_app_apply₅ X _ _ (op W) x) ?_
  refine Eq.trans (congrArg (fun z => ((HomologicalComplex.ιMapBifunctor A
      (structureSheafComplex X) (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) n 0 n
      (by simp) ≫ (tensorTotalIsoTensorComplex X A (structureSheafComplex X)).inv.f n).val.app
        (op W)) z) (sheafTensorUnitIsoRight_inv_apply X (A.X n) (op W) x)) ?_
  refine Eq.trans (comp_val_app_apply₅ X _ _ (op W) _) ?_
  exact tensorTotalIsoTensorComplex_inv_tensorComplexSection X A (structureSheafComplex X) W
    n 0 n (by omega) x (structureSheafOne X W)

/-! ### The diagonal at the structure sheaf -/

/-- **The diagonal of Stacks 0A93 at the structure sheaf, followed by evaluation at the unit
section**: the morphism `A ⟶ Tot(A ⊗_O O[0])` sending a homogeneous local section `x` to the
local pure tensor `x ⊗ 1`. -/
def diagonalTensorUnit : A ⟶ tensorTotal X A (structureSheafComplex X) :=
  diagonalMap X A (structureSheafComplex X) ≫
    structureSheafHomEvaluation X (tensorTotal X A (structureSheafComplex X))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The diagonal followed by evaluation at the unit section carries `x` to `x ⊗ 1`.** -/
lemma diagonalTensorUnit_apply (n : ℤ) (W : X.C) (x : (A.X n).val.obj (op W)) :
    ((diagonalTensorUnit X (A := A)).f n).val.app (op W) x =
      tensorTotalSectionAt X A (structureSheafComplex X) W n 0 n (by omega) x
        (structureSheafOne X W) := by
  refine Eq.trans (comp_val_app_apply₅ X _ _ (op W) x) ?_
  refine Eq.trans (structureSheafHomEvaluation_apply X
    (tensorTotal X A (structureSheafComplex X)) n W _) ?_
  exact diagonalMap_applyHomSection X A (structureSheafComplex X) W n 0 n (zero_add n) x
    (structureSheafOne X W)

/-- **The diagonal at the structure sheaf, followed by evaluation at the unit section, is the
degreewise collapse.** -/
theorem diagonalTensorUnit_f (n : ℤ) :
    (diagonalTensorUnit X (A := A)).f n = unitRightComponent X (A := A) n := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext
    (LinearMap.ext fun x => ?_))
  obtain ⟨W⟩ := W
  exact (diagonalTensorUnit_apply X n W x).trans (unitRightComponent_apply X n W x).symm

/-- **The diagonal of Stacks 0A93 at the structure sheaf, followed by evaluation at the unit
section, is an isomorphism of complexes.** -/
instance isIso_diagonalTensorUnit : IsIso (diagonalTensorUnit X (A := A)) := by
  have h : ∀ n, IsIso ((diagonalTensorUnit X (A := A)).f n) := by
    intro n
    rw [diagonalTensorUnit_f]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The diagonal of Stacks 0A93 at an arbitrary second complex, read through the unit.** For
a morphism `g : O[0] ⟶ I` the diagonal at `I`, followed by restriction along `g` in the source
of the internal Hom and evaluation at the unit section, is the isomorphism `diagonalTensorUnit`
followed by `Tot(A ⊗_O g)`. -/
theorem diagonalMap_comp_homMap_comp_structureSheafHomEvaluation
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (g : structureSheafComplex X ⟶ I) :
    diagonalMap X A I ≫ homMap X g (𝟙 (tensorTotal X A I)) ≫
        structureSheafHomEvaluation X (tensorTotal X A I) =
      diagonalTensorUnit X (A := A) ≫ tensorTotalMap X (𝟙 A) g := by
  have hdiag := diagonalMap_natural X (𝟙 A) g (K := A) (L := structureSheafComplex X)
  rw [Category.id_comp] at hdiag
  rw [← Category.assoc, ← hdiag, Category.assoc,
    structureSheafHomEvaluation_naturality X (tensorTotalMap X (𝟙 A) g), diagonalTensorUnit,
    Category.assoc]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The chain-level comparison of Stacks 0A93 with the structure sheaf, at a model of the
unit and a resolution of the total tensor product.** For a morphism `g : O[0] ⟶ I` and a
morphism `q : Tot(A ⊗_O I) ⟶ J`, the morphism

`A ⟶ SheafHom(I, J)`

obtained from the diagonal of Stacks 0A93 at `I` followed by `SheafHom(I, q)`, read back along
`g` and evaluated at the unit section, is `Tot(A ⊗_O g)` followed by `q`, precomposed with the
isomorphism `diagonalTensorUnit`. -/
theorem diagonalMap_comp_homMap_comp_homMap_comp_structureSheafHomEvaluation
    {I J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : structureSheafComplex X ⟶ I) (q : tensorTotal X A I ⟶ J) :
    diagonalMap X A I ≫ homMap X (𝟙 I) q ≫ homMap X g (𝟙 J) ≫
        structureSheafHomEvaluation X J =
      diagonalTensorUnit X (A := A) ≫ tensorTotalMap X (𝟙 A) g ≫ q := by
  have h1 : homMap X (𝟙 I) q ≫ homMap X g (𝟙 J) =
      homMap X g (𝟙 (tensorTotal X A I)) ≫
        homMap X (𝟙 (structureSheafComplex X)) q := by
    rw [homMap_comp, homMap_comp, Category.comp_id, Category.id_comp, Category.comp_id,
      Category.id_comp]
  rw [← Category.assoc (homMap X (𝟙 I) q), h1, Category.assoc,
    structureSheafHomEvaluation_naturality X q,
    reassoc_of% diagonalMap_comp_homMap_comp_structureSheafHomEvaluation X (A := A) I g]

end AlgebraicGeometry.RingedSite

end
