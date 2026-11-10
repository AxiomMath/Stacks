module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebra
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Algebra

/-!
# Twisting a graded algebra of modules by an invertible sheaf

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra in the sense of Situation 01NN
and `ℒ` an invertible `𝒪_S`-module. The **twist** of `𝒜` by `ℒ` is the graded `𝒪_S`-algebra `ℬ`
whose homogeneous piece of degree `d` is `𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}`; its multiplication
`ℬ_i ⊗ ℬ_j ⟶ ℬ_{i + j}` is the multiplication of `𝒜` on the first factors and the coherent
multiplication of the integer tensor powers of `ℒ` of Tag 01CU on the second, read through the
middle-four interchange of the sheaf tensor product. This is the graded algebra of the setting
of Tag 02NB.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.interchange`: **the middle-four interchange**
  `(A ⊗ B) ⊗ (D ⊗ E) ≅ (A ⊗ D) ⊗ (B ⊗ E)` of the sheaf tensor product.
* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.piece`,
  `Stacks.AlgebraicGeometry.GradedAlgebraTwist.mulMor`,
  `Stacks.AlgebraicGeometry.GradedAlgebraTwist.mulSection` and
  `Stacks.AlgebraicGeometry.GradedAlgebraTwist.oneSec`: the homogeneous pieces of the twist, its
  multiplication as a morphism of sheaves of modules and on local sections, and its unit.
* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.mulHom` and
  `Stacks.AlgebraicGeometry.GradedAlgebraTwist.oneHom`: the multiplication and the unit of a
  sheaf-level graded algebra over a scheme, as morphisms out of a tensor product sheaf and out
  of the structure sheaf.
* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist`: **the twist of a quasi-coherent graded
  `𝒪_S`-algebra by an invertible `𝒪_S`-module**, again a quasi-coherent graded `𝒪_S`-algebra.

## Main results

* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.mulMor_assoc`, `mulMor_comm`, `mulMor_one_mul`
  and `mulMor_mul_one`: **the algebra laws of the twist**, as identities of morphisms of sheaves
  of modules, and `mulSection_assoc`, `mulSection_comm`, `mulSection_one_mul`,
  `mulSection_mul_one`: the same laws as heterogeneous equalities of local sections.
* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.hom_ext_tensor`, `hom_ext_tensor2` and
  `hom_ext_tensor3`: a morphism out of an iterated sheaf tensor product is determined by its
  values on the local sections determined by local sections of the factors.
* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.piece_isZero`: a homogeneous piece of the twist
  vanishes in every degree in which the piece of `𝒜` vanishes.

## Implementation notes

The multiplication of the twist is built as a morphism of sheaves of modules, and each algebra
law is first proved in that form; the laws on local sections, which is the shape
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` demands, follow by evaluating
the morphism identity on the section determined by the given ones. A morphism identity is proved
by the extensionality principles `hom_ext_tensor`, `hom_ext_tensor2` and `hom_ext_tensor3`, which
reduce it to the local sections determined by *pure* local sections of `𝒜` and of the tensor
powers of `ℒ`. Those principles rest on `hom_ext_of_isIso_sheafify_map`: a morphism out of a
sheaf of modules is determined by its values on the image of any presheaf of modules mapping to
it by a morphism that sheafification inverts, and the iterated objectwise tensor products
`flatUnit`, `flat2`, `flat3` are such presheaves by Tag 05NA.

On pure local sections the multiplication of the twist is the multiplication of `𝒜` on the
first factors and the multiplication of the Laurent algebra of `ℒ` on the second, so each of the
four laws is the corresponding law of `𝒜` together with the corresponding law of the Laurent
algebra. Both are heterogeneous equalities, the two sides living in degrees that agree only
propositionally; `pieceReindex`, `heq_pieceReindex` and `heq_tensorSectionsAt_of_eq` are the
degree bookkeeping that combines them, exactly as `tensorPowerReindex` and `heq_reindex` do for
the Laurent algebra itself.

No coherence property of the middle-four interchange is needed: it is only ever evaluated on a
local section determined by four local sections, where the five structural isomorphisms it is
built from are computed one at a time by the section formulas of the monoidal structure.

## References

* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.Invertible (tensorProductIso tensorProductBifunctor
  tensorProductAssociator tensorProductBraiding tensorProductLeftUnitor
  tensorProductRightUnitor)
open Stacks.SheafOfModules.TensorSheafification
    (sheafify toSheafify sheafifyAdjunction structureSheaf structureRingPresheaf)
open scoped TensorProduct

universe v u w

namespace Stacks.AlgebraicGeometry.GradedAlgebraTwist

/-! ### A sixfold extensionality principle for tensor products of modules -/

/-- A linear map out of `((M₁ ⊗ M₂) ⊗ (M₃ ⊗ M₄)) ⊗ (M₅ ⊗ M₆)` is determined by its values on
pure tensors of that shape. -/
theorem linearMap_ext6 {R : Type*} [CommRing R]
    {M₁ M₂ M₃ M₄ M₅ M₆ T : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup M₄] [Module R M₄]
    [AddCommGroup M₅] [Module R M₅] [AddCommGroup M₆] [Module R M₆]
    [AddCommGroup T] [Module R T]
    {φ ψ : (((M₁ ⊗[R] M₂) ⊗[R] (M₃ ⊗[R] M₄)) ⊗[R] (M₅ ⊗[R] M₆)) →ₗ[R] T}
    (h : ∀ (a : M₁) (b : M₂) (d : M₃) (e : M₄) (x : M₅) (y : M₆),
      φ (((a ⊗ₜ b) ⊗ₜ (d ⊗ₜ e)) ⊗ₜ (x ⊗ₜ y)) = ψ (((a ⊗ₜ b) ⊗ₜ (d ⊗ₜ e)) ⊗ₜ (x ⊗ₜ y))) :
    φ = ψ := by
  refine TensorProduct.ext' fun p z => ?_
  induction p using TensorProduct.inductionOn with
  | add p₁ p₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  | tmul u v =>
      induction z using TensorProduct.inductionOn with
      | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
      | tmul x y =>
          induction u using TensorProduct.inductionOn with
          | add u₁ u₂ h₁ h₂ =>
              simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
          | tmul a b =>
              induction v using TensorProduct.inductionOn with
              | add v₁ v₂ h₁ h₂ =>
                  simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, h₁, h₂]
              | tmul d e => exact h a b d e x y

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

attribute [local instance_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The identity isomorphism acts trivially on local sections. -/
theorem refl_app (F : SheafOfModules.{w} (structureSheaf O hO)) (U : Cᵒᵖ) (x : F.val.obj U) :
    (Iso.refl F).hom.val.app U x = x := rfl

/-- The inverse of an isomorphism out of a tensor product sheaf undoes it on the local section
determined by a pair of local sections. -/
private theorem inv_app_tensorSectionsAt_of_hom_app (U : Cᵒᵖ)
    {F G Y : SheafOfModules.{w} (structureSheaf O hO)}
    (e : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        (G)) ≅ Y)
    (s : F.val.obj U) (t : G.val.obj U) {y : Y.val.obj U}
    (h : e.hom.val.app U (tensorSectionsAt O hO U F G s t) = y) :
    e.inv.val.app U y = tensorSectionsAt O hO U F G s t :=
  (congrArg (e.inv.val.app U) h.symm).trans
    (congrArg (fun morphism => (_root_.SheafOfModules.Hom.val morphism).app U
      (tensorSectionsAt O hO U F G s t)) e.hom_inv_id)

/-- The inverse of the associativity constraint of the sheaf tensor product reassociates the
three local sections determining a section of an iterated tensor product. -/
theorem tensorSections_associatorInvAt (U : Cᵒᵖ)
    (F G H : SheafOfModules.{w} (structureSheaf O hO))
    (x : F.val.obj U) (y : G.val.obj U) (z : H.val.obj U) :
    (tensorProductAssociator O hO F G H).inv.val.app U
        (tensorSectionsAt O hO U F
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (G)).obj (H))) x
          (tensorSectionsAt O hO U G H y z)) =
      tensorSectionsAt O hO U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (F)).obj (G))) H
        (tensorSectionsAt O hO U F G x y) z := by
  exact inv_app_tensorSectionsAt_of_hom_app O hO U _ _ _
    (tensorSections_associatorAt O hO U F G H x y z)

/-- **The middle-four interchange of the sheaf tensor product**: the symmetry of the tensor
product exchanges the two inner factors of a fourfold tensor product. -/
def interchange (A B D E : SheafOfModules.{w} (structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (A)).obj
        (B))))).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (D)).obj
        (E))))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (A)).obj (D))))).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (B)).obj (E))))) :=
  tensorProductAssociator O hO A B
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (D)).obj
      (E))) ≪≫
    tensorProductIso O hO (Iso.refl A) (tensorProductAssociator O hO B D E).symm ≪≫
    tensorProductIso O hO (Iso.refl A)
      (tensorProductIso O hO (tensorProductBraiding O hO B D) (Iso.refl E)) ≪≫
    tensorProductIso O hO (Iso.refl A) (tensorProductAssociator O hO D B E) ≪≫
    (tensorProductAssociator O hO A D
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (B)).obj
        (E)))).symm

/-- The middle-four interchange on a local section determined by four local sections. -/
theorem interchange_pure (U : Cᵒᵖ) (A B D E : SheafOfModules.{w} (structureSheaf O hO))
    (a : A.val.obj U) (b : B.val.obj U) (d : D.val.obj U) (e : E.val.obj U) :
    (interchange O hO A B D E).hom.val.app U
        (tensorSectionsAt O hO U
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (A)).obj (B)))
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (D)).obj (E)))
          (tensorSectionsAt O hO U A B a b) (tensorSectionsAt O hO U D E d e)) =
      tensorSectionsAt O hO U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (A)).obj (D)))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (B)).obj (E)))
        (tensorSectionsAt O hO U A D a d) (tensorSectionsAt O hO U B E b e) := by
  let leftAssociate := tensorProductIso O hO (Iso.refl A) (tensorProductAssociator O hO B D E).symm
  let middleSwap := tensorProductIso O hO (Iso.refl A)
    (tensorProductIso O hO (tensorProductBraiding O hO B D) (Iso.refl E))
  let rightAssociate := tensorProductIso O hO (Iso.refl A) (tensorProductAssociator O hO D B E)
  let lastAssociate := tensorProductAssociator O hO A D
    ((sheafify O hO).obj (B.val ⊗ E.val))
  change lastAssociate.inv.val.app U (rightAssociate.hom.val.app U
    (middleSwap.hom.val.app U (leftAssociate.hom.val.app U
      ((tensorProductAssociator O hO A B ((sheafify O hO).obj (D.val ⊗ E.val))).hom.val.app U
          _)))) = _
  refine (congrArg (lastAssociate.inv.val.app U) ?_).trans
    (tensorSections_associatorInvAt O hO U A D ((sheafify O hO).obj (B.val ⊗ E.val))
      a d (tensorSectionsAt O hO U B E b e))
  refine (congrArg (rightAssociate.hom.val.app U) ?_).trans
    ((tensorSections_tensorProductIsoAt O hO U A A _ _ (Iso.refl A)
      (tensorProductAssociator O hO D B E) a _).trans
        (congrArg (tensorSectionsAt O hO U A _ a)
          (tensorSections_associatorAt O hO U D B E d b e)))
  refine (congrArg (middleSwap.hom.val.app U) ?_).trans
    ((tensorSections_tensorProductIsoAt O hO U A A _ _ (Iso.refl A)
      (tensorProductIso O hO (tensorProductBraiding O hO B D) (Iso.refl E)) a _).trans
        (congrArg (tensorSectionsAt O hO U A _ a)
          ((tensorSections_tensorProductIsoAt O hO U _ _ E E
            (tensorProductBraiding O hO B D) (Iso.refl E)
            (tensorSectionsAt O hO U B D b d) e).trans
              (congrArg (fun sectionValue => tensorSectionsAt O hO U _ E sectionValue e)
                (tensorSections_braidingAt O hO U B D b d)))))
  refine (congrArg (leftAssociate.hom.val.app U)
    (tensorSections_associatorAt O hO U A B ((sheafify O hO).obj (D.val ⊗ E.val))
      a b (tensorSectionsAt O hO U D E d e))).trans ?_
  exact (tensorSections_tensorProductIsoAt O hO U A A _ _ (Iso.refl A)
    (tensorProductAssociator O hO B D E).symm a _).trans
      (congrArg (tensorSectionsAt O hO U A _ a)
        (tensorSections_associatorInvAt O hO U B D E b d e))


/-! ### Extensionality through a flat presentation -/

/-- Sheafification inverts the tensor product of two morphisms that it inverts. -/
theorem isIso_sheafify_map_tensorHom
    {A B A' B' : PresheafOfModules.{w} (structureSheaf O hO).obj} (f : A ⟶ A') (g : B ⟶ B')
    (hf : IsIso ((sheafify O hO).map f)) (hg : IsIso ((sheafify O hO).map g)) :
    IsIso ((sheafify O hO).map (f ⊗ₘ g)) := by
  have h₁ : IsIso ((sheafify O hO).map (f ▷ B)) :=
    TensorSheafification.isIso_sheafify_map_whiskerRight O hO f B hf
  have h₂ : IsIso ((sheafify O hO).map (A' ◁ g)) :=
    TensorSheafification.isIso_sheafify_map_whiskerLeft O hO A' g hg
  have e : (sheafify O hO).map (f ⊗ₘ g) =
      (sheafify O hO).map (f ▷ B) ≫ (sheafify O hO).map (A' ◁ g) := by
    rw [← Functor.map_comp]
    exact congrArg (sheafify O hO).map (MonoidalCategory.tensorHom_def f g)
  rw [e]
  infer_instance

/-- **Extensionality through a flat presentation.** Two morphisms out of a sheaf of modules
agree as soon as they agree on the images of the sections of a presheaf of modules mapping to
it by a morphism that sheafification inverts. -/
theorem hom_ext_of_isIso_sheafify_map {M P : SheafOfModules.{w} (structureSheaf O hO)}
    {Q : PresheafOfModules.{w} (structureSheaf O hO).obj} (η : Q ⟶ M.val)
    (hη : IsIso ((sheafify O hO).map η)) {f g : M ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (q : Q.obj U), f.val.app U (η.app U q) = g.val.app U (η.app U q)) :
    f = g := by
  have hcu : IsIso (sheafifyAdjunction O hO).counit := by
    change IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf O hO).obj)).counit
    infer_instance
  let e : (sheafify O hO).obj Q ≅ M :=
    asIso ((sheafify O hO).map η) ≪≫ (asIso (sheafifyAdjunction O hO).counit).app M
  have key : ∀ (U : Cᵒᵖ) (q : Q.obj U),
      e.hom.val.app U ((toSheafify O hO Q).app U q) = η.app U q := by
    intro U q
    change ((sheafifyAdjunction O hO).counit.app M).val.app U
      (((sheafify O hO).map η).val.app U ((toSheafify O hO Q).app U q)) = _
    rw [toSheafify_app_map_obj O hO η U q]
    exact sheafifyCounit_toSheafify_app O hO M U (η.app U q)
  refine (cancel_epi e.hom).mp ?_
  apply ((sheafifyAdjunction O hO).homEquiv Q P).injective
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun q => ?_)
  change f.val.app U (e.hom.val.app U ((toSheafify O hO Q).app U q)) =
    g.val.app U (e.hom.val.app U ((toSheafify O hO Q).app U q))
  rw [key U q]
  exact h U q

/-- The pure tensor of two local sections, as a section of the objectwise tensor product of two
presheaves of modules. -/
def ptmul (A B : PresheafOfModules.{w} (structureSheaf O hO).obj) (U : Cᵒᵖ)
    (a : A.obj U) (b : B.obj U) : (A ⊗ B).obj U := by
  exact a ⊗ₜ[O.obj U] b

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The tensor product of two morphisms of presheaves of modules, on a pure tensor of local
sections. -/
theorem tensorHom_app_ptmul {A B A' B' : PresheafOfModules.{w} (structureSheaf O hO).obj}
    (f : A ⟶ A') (g : B ⟶ B') (U : Cᵒᵖ) (a : A.obj U) (b : B.obj U) :
    (f ⊗ₘ g).app U (ptmul O hO A B U a b) = ptmul O hO A' B' U (f.app U a) (g.app U b) :=
  ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _

/-- The sheafification unit of an objectwise tensor product of two sheaves of modules. -/
def flatUnit (F G : SheafOfModules.{w} (structureSheaf O hO)) :
    (F.val ⊗ G.val) ⟶
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        (G))).val := by
  exact toSheafify O hO (F.val ⊗ G.val)

/-- The sheafification unit sends a pure tensor of local sections to the section of the tensor
product sheaf they determine. -/
theorem flatUnit_app (F G : SheafOfModules.{w} (structureSheaf O hO)) (U : Cᵒᵖ)
    (s : F.val.obj U) (t : G.val.obj U) :
    (flatUnit O hO F G).app U (ptmul O hO F.val G.val U s t) = tensorSectionsAt O hO U F G s t :=
  rfl

/-- Sheafification inverts the sheafification unit of an objectwise tensor product. -/
theorem isIso_sheafify_map_flatUnit (F G : SheafOfModules.{w} (structureSheaf O hO)) :
    IsIso ((sheafify O hO).map (flatUnit O hO F G)) :=
  TensorSheafification.isIso_sheafify_map_toSheafify O hO (F.val ⊗ G.val)

/-- The flat presentation of a twofold iterated tensor product sheaf. -/
def flat2 (A B D E : SheafOfModules.{w} (structureSheaf O hO)) :
    ((A.val ⊗ B.val) ⊗ (D.val ⊗ E.val)) ⟶
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (A)).obj (B))))).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (D)).obj (E)))))).val :=
  (flatUnit O hO A B ⊗ₘ flatUnit O hO D E) ≫ flatUnit O hO
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (A)).obj
      (B)))
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (D)).obj
        (E)))

/-- The flat presentation of a threefold iterated tensor product sheaf. -/
def flat3 (A B D E G H : SheafOfModules.{w} (structureSheaf O hO)) :
    (((A.val ⊗ B.val) ⊗ (D.val ⊗ E.val)) ⊗ (G.val ⊗ H.val)) ⟶
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (A)).obj (B))))).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (D)).obj (E)))))))).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (G)).obj (H)))))).val :=
  (flat2 O hO A B D E ⊗ₘ flatUnit O hO G H) ≫
    flatUnit O hO
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (A)).obj
        (B))))).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (D)).obj
        (E))))))
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (G)).obj (H)))

/-- Sheafification inverts the flat presentation of a twofold iterated tensor product sheaf. -/
theorem isIso_sheafify_map_flat2 (A B D E : SheafOfModules.{w} (structureSheaf O hO)) :
    IsIso ((sheafify O hO).map (flat2 O hO A B D E)) := by
  rw [show (sheafify O hO).map (flat2 O hO A B D E) = _ from (sheafify O hO).map_comp _ _]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (isIso_sheafify_map_tensorHom O hO (flatUnit O hO A B) (flatUnit O hO D E)
      (isIso_sheafify_map_flatUnit O hO A B) (isIso_sheafify_map_flatUnit O hO D E))
    (isIso_sheafify_map_flatUnit O hO _ _)

/-- Sheafification inverts the flat presentation of a threefold iterated tensor product
sheaf. -/
theorem isIso_sheafify_map_flat3 (A B D E G H : SheafOfModules.{w} (structureSheaf O hO)) :
    IsIso ((sheafify O hO).map (flat3 O hO A B D E G H)) := by
  rw [show (sheafify O hO).map (flat3 O hO A B D E G H) = _ from (sheafify O hO).map_comp _ _]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (isIso_sheafify_map_tensorHom O hO (flat2 O hO A B D E) (flatUnit O hO G H)
      (isIso_sheafify_map_flat2 O hO A B D E) (isIso_sheafify_map_flatUnit O hO G H))
    (isIso_sheafify_map_flatUnit O hO _ _)

/-- The flat presentation of a twofold iterated tensor product sheaf, on a pure tensor. -/
theorem flat2_app (A B D E : SheafOfModules.{w} (structureSheaf O hO)) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) (d : D.val.obj U) (e : E.val.obj U) :
    (flat2 O hO A B D E).app U
        (ptmul O hO _ _ U (ptmul O hO A.val B.val U a b) (ptmul O hO D.val E.val U d e)) =
      tensorSectionsAt O hO U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (A)).obj (B)))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (D)).obj (E)))
        (tensorSectionsAt O hO U A B a b) (tensorSectionsAt O hO U D E d e) := by
  refine (congrArg ((flatUnit O hO _ _).app U)
    (tensorHom_app_ptmul O hO (flatUnit O hO A B) (flatUnit O hO D E) U
      (ptmul O hO A.val B.val U a b) (ptmul O hO D.val E.val U d e))).trans ?_
  exact (flatUnit_app O hO _ _ U _ _).trans
    (congrArg₂ (tensorSectionsAt O hO U _ _)
      (flatUnit_app O hO A B U a b) (flatUnit_app O hO D E U d e))

/-- The flat presentation of a threefold iterated tensor product sheaf, on a pure tensor. -/
theorem flat3_app (A B D E G H : SheafOfModules.{w} (structureSheaf O hO)) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) (d : D.val.obj U) (e : E.val.obj U)
    (g : G.val.obj U) (h : H.val.obj U) :
    (flat3 O hO A B D E G H).app U
        (ptmul O hO _ _ U
          (ptmul O hO _ _ U (ptmul O hO A.val B.val U a b) (ptmul O hO D.val E.val U d e))
          (ptmul O hO G.val H.val U g h)) =
      tensorSectionsAt O hO U
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (A)).obj (B))))).obj
            (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (D)).obj (E))))))
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (G)).obj (H)))
        (tensorSectionsAt O hO U
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (A)).obj (B)))
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (D)).obj (E)))
          (tensorSectionsAt O hO U A B a b) (tensorSectionsAt O hO U D E d e))
        (tensorSectionsAt O hO U G H g h) := by
  refine (congrArg ((flatUnit O hO _ _).app U)
    (tensorHom_app_ptmul O hO (flat2 O hO A B D E) (flatUnit O hO G H) U
      (ptmul O hO _ _ U (ptmul O hO A.val B.val U a b) (ptmul O hO D.val E.val U d e))
      (ptmul O hO G.val H.val U g h))).trans ?_
  exact (flatUnit_app O hO _ _ U _ _).trans
    (congrArg₂ (tensorSectionsAt O hO U _ _)
      (flat2_app O hO A B D E U a b d e) (flatUnit_app O hO G H U g h))


omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A morphism of sheaves of modules applied to two equal local sections. -/
theorem congr_app {M P : SheafOfModules.{w} (structureSheaf O hO)} (f : M ⟶ P) (U : Cᵒᵖ)
    {x y : M.val.obj U} (hxy : x = y) : f.val.app U x = f.val.app U y := by rw [hxy]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A morphism out of the underlying presheaf of a sheaf of modules, read on sections. -/
theorem app_apply_of_comp {M P : SheafOfModules.{w} (structureSheaf O hO)} {f g : M ⟶ P}
    {Q : PresheafOfModules.{w} (structureSheaf O hO).obj} (η : Q ⟶ M.val) (U : Cᵒᵖ)
    (key : η.app U ≫ f.val.app U = η.app U ≫ g.val.app U) (q : Q.obj U) :
    f.val.app U (η.app U q) = g.val.app U (η.app U q) :=
  congrArg (fun φ => (ConcreteCategory.hom φ) q) key

/-- **Extensionality for a tensor product sheaf.** Two morphisms out of a tensor product of two
sheaves of modules agree as soon as they agree on the local sections determined by a pair of
local sections of the two factors. -/
theorem hom_ext_tensor {F G P : SheafOfModules.{w} (structureSheaf O hO)}
    {f g :
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        (G)) ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      f.val.app U (tensorSectionsAt O hO U F G x y) =
        g.val.app U (tensorSectionsAt O hO U F G x y)) :
    f = g := by
  refine hom_ext_of_isIso_sheafify_map O hO (flatUnit O hO F G)
    (isIso_sheafify_map_flatUnit O hO F G) (fun U q => ?_)
  refine app_apply_of_comp O hO (flatUnit O hO F G) U ?_ q
  exact ModuleCat.hom_ext (TensorProduct.ext' fun x y => h U x y)

/-- **Extensionality for a twofold iterated tensor product sheaf.** -/
theorem hom_ext_tensor2 {A B D E P : SheafOfModules.{w} (structureSheaf O hO)}
    {f g :
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (A)).obj
        (B))))).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (D)).obj
        (E))))) ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (d : D.val.obj U) (e : E.val.obj U),
      f.val.app U
          (tensorSectionsAt O hO U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (A)).obj (B)))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (D)).obj (E)))
          (tensorSectionsAt O hO U A B a b) (tensorSectionsAt O hO U D E d e)) =
        g.val.app U
            (tensorSectionsAt O hO U
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (A)).obj (B)))
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (D)).obj (E)))
          (tensorSectionsAt O hO U A B a b) (tensorSectionsAt O hO U D E d e))) :
    f = g := by
  refine hom_ext_of_isIso_sheafify_map O hO (flat2 O hO A B D E)
    (isIso_sheafify_map_flat2 O hO A B D E) (fun U q => ?_)
  refine app_apply_of_comp O hO (flat2 O hO A B D E) U ?_ q
  exact ModuleCat.hom_ext <| TensorProduct.ext_fourfold' fun a b d e =>
    (congr_app O hO f U (flat2_app O hO A B D E U a b d e)).trans
      ((h U a b d e).trans (congr_app O hO g U (flat2_app O hO A B D E U a b d e)).symm)

/-- **Extensionality for a threefold iterated tensor product sheaf.** -/
theorem hom_ext_tensor3 {A B D E G H P : SheafOfModules.{w} (structureSheaf O hO)}
    {f g :
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (A)).obj
        (B))))).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (D)).obj
        (E)))))))).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (G)).obj
        (H))))) ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (d : D.val.obj U) (e : E.val.obj U)
        (x : G.val.obj U) (y : H.val.obj U),
      f.val.app U (tensorSectionsAt O hO U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (A)).obj (B))))).obj
              (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (D)).obj (E))))))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (G)).obj (H)))
          (tensorSectionsAt O hO U
              ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (A)).obj (B)))
              ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (D)).obj (E)))
            (tensorSectionsAt O hO U A B a b) (tensorSectionsAt O hO U D E d e))
          (tensorSectionsAt O hO U G H x y)) =
        g.val.app U (tensorSectionsAt O hO U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (A)).obj (B))))).obj
              (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (D)).obj (E))))))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (G)).obj (H)))
          (tensorSectionsAt O hO U
              ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (A)).obj (B)))
              ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (D)).obj (E)))
            (tensorSectionsAt O hO U A B a b) (tensorSectionsAt O hO U D E d e))
          (tensorSectionsAt O hO U G H x y))) :
    f = g := by
  refine hom_ext_of_isIso_sheafify_map O hO (flat3 O hO A B D E G H)
    (isIso_sheafify_map_flat3 O hO A B D E G H) (fun U q => ?_)
  refine app_apply_of_comp O hO (flat3 O hO A B D E G H) U ?_ q
  apply ModuleCat.hom_ext
  refine linearMap_ext6 fun a b d e x y => ?_
  exact ((congr_app O hO f U (flat3_app O hO A B D E G H U a b d e x y)).trans
    ((h U a b d e x y).trans
      (congr_app O hO g U (flat3_app O hO A B D E G H U a b d e x y)).symm))

/-! ### The twisted pieces and their multiplication -/

/-- The sheaf tensor product of two morphisms of sheaves of modules. -/
def tensorMap {M M' N N' : SheafOfModules.{w} (structureSheaf O hO)} (f : M ⟶ M') (g : N ⟶ N') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
        (N)) ⟶
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M')).obj (N')) :=
  (tensorProductBifunctor O hO).map (X := (M, N)) (Y := (M', N')) (f, g)

/-- The tensor product of two morphisms on a local section determined by a pair of local
sections. -/
theorem tensorMap_app {M M' N N' : SheafOfModules.{w} (structureSheaf O hO)} (f : M ⟶ M')
    (g : N ⟶ N') (U : Cᵒᵖ) (s : M.val.obj U) (t : N.val.obj U) :
    (tensorMap O hO f g).val.app U (tensorSectionsAt O hO U M N s t) =
      tensorSectionsAt O hO U M' N' (f.val.app U s) (g.val.app U t) :=
  tensorSections_tensorMapAt O hO U M M' N N' f g s t

/-- The unit section of the structure sheaf, read as a section of the monoidal unit. -/
def unitSection (U : Cᵒᵖ) : (SheafOfModules.unit (structureSheaf O hO)).val.obj U := by
  exact (1 : O.obj U)

/-- The inverse of the left unit constraint inserts the unit section on the left. -/
theorem tensorSections_leftUnitorInvAt (U : Cᵒᵖ) (M : SheafOfModules.{w} (structureSheaf O hO))
    (m : M.val.obj U) :
    (tensorProductLeftUnitor O hO M).inv.val.app U m =
      tensorSectionsAt O hO U (SheafOfModules.unit (structureSheaf O hO)) M
        (unitSection O hO U) m := by
  exact inv_app_tensorSectionsAt_of_hom_app O hO U _ _ _ (tensorSections_leftUnitorAt O hO U M m)

/-- The inverse of the right unit constraint inserts the unit section on the right. -/
theorem tensorSections_rightUnitorInvAt (U : Cᵒᵖ) (M : SheafOfModules.{w} (structureSheaf O hO))
    (m : M.val.obj U) :
    (tensorProductRightUnitor O hO M).inv.val.app U m =
      tensorSectionsAt O hO U M (SheafOfModules.unit (structureSheaf O hO)) m
        (unitSection O hO U) := by
  exact inv_app_tensorSectionsAt_of_hom_app O hO U _ _ _ (tensorSections_rightUnitorAt O hO U M m)

variable (A : ℤ → SheafOfModules.{w} (structureSheaf O hO))
  (ν : ∀ i j : ℤ,
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
      ((A i))).obj ((A j))) ⟶ A (i + j))
  (L : SheafOfModules.{w} (structureSheaf O hO))
  [Stacks.SheafOfModules.IsInvertible O hO L]

/-- **The homogeneous piece of degree `d` of the twist of a graded algebra `A` by an invertible
sheaf `L`**: the tensor product of the degree-`d` piece of `A` with the `d`-th tensor power
of `L`. -/
abbrev piece (d : ℤ) : SheafOfModules.{w} (structureSheaf O hO) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
      ((A d))).obj ((TensorPower.tensorPower O hO L d)))

/-- **Multiplication of the twist in degrees `i` and `j`**: the middle-four interchange followed
by the multiplication of `A` and the coherent multiplication of the tensor powers of `L`. -/
def mulMor (i j : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((piece O hO A L i))).obj ((piece O hO A L j))) ⟶ piece O hO A L (i + j) :=
  (interchange O hO (A i) (TensorPower.tensorPower O hO L i) (A j)
      (TensorPower.tensorPower O hO L j)).hom ≫
    tensorMap O hO (ν i j) (TensorPower.coherentMulIso O hO L i j).hom

/-- Multiplication of the twist, on local sections. -/
def mulSection (i j : ℤ) (U : Cᵒᵖ) (a : (piece O hO A L i).val.obj U)
    (b : (piece O hO A L j).val.obj U) : (piece O hO A L (i + j)).val.obj U :=
  (mulMor O hO A ν L i j).val.app U
    (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L j) a b)

/-- Multiplication of `A` on local sections. -/
def mulA (i j : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U) (y : (A j).val.obj U) :
    (A (i + j)).val.obj U :=
  (ν i j).val.app U (tensorSectionsAt O hO U (A i) (A j) x y)

/-- **Multiplication of the twist on a pair of pure local sections** multiplies the two
sections of `A` and the two sections of the tensor powers of `L` separately. -/
theorem mulSection_pure (i j : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U)
    (s : (TensorPower.tensorPower O hO L i).val.obj U) (y : (A j).val.obj U)
    (t : (TensorPower.tensorPower O hO L j).val.obj U) :
    mulSection O hO A ν L i j U
        (tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s)
        (tensorSectionsAt O hO U (A j) (TensorPower.tensorPower O hO L j) y t) =
      tensorSectionsAt O hO U (A (i + j)) (TensorPower.tensorPower O hO L (i + j))
        ((ν i j).val.app U (tensorSectionsAt O hO U (A i) (A j) x y))
        ((TensorPower.coherentMulIso O hO L i j).hom.val.app U
          (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L i)
            (TensorPower.tensorPower O hO L j) s t)) := by
  refine (congrArg ((tensorMap O hO (ν i j) (TensorPower.coherentMulIso O hO L i j).hom).val.app U)
    (interchange_pure O hO U (A i) (TensorPower.tensorPower O hO L i)
      (A j) (TensorPower.tensorPower O hO L j) x s y t)).trans ?_
  exact tensorMap_app O hO (ν i j) (TensorPower.coherentMulIso O hO L i j).hom U _ _


/-! ### Degree bookkeeping -/

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The identity acts trivially on local sections. -/
theorem id_app (M : SheafOfModules.{w} (structureSheaf O hO)) (U : Cᵒᵖ) (m : M.val.obj U) :
    (𝟙 M : M ⟶ M).val.app U m = m := rfl

/-- Reindexing the homogeneous pieces of the twist along an equality of degrees. -/
def pieceReindex {i j : ℤ} (hij : i = j) : piece O hO A L i ≅ piece O hO A L j := by
  subst hij
  exact Iso.refl _

/-- Reindexing along an equality of degrees leaves a local section unchanged, up to
heterogeneous equality. -/
theorem heq_pieceReindex (U : Cᵒᵖ) {i j : ℤ} (hij : i = j)
    (x : (piece O hO A L i).val.obj U) :
    HEq ((pieceReindex O hO A L hij).hom.val.app U x) x := by
  cases hij
  exact HEq.refl _

/-- Two heterogeneously equal local sections in degrees that agree have equal reindexings. -/
theorem eq_pieceReindex_of_heq (U : Cᵒᵖ) {i j : ℤ} (hij : i = j)
    (p : (piece O hO A L j).val.obj U) (q : (piece O hO A L i).val.obj U) (h : HEq p q) :
    p = (pieceReindex O hO A L hij).hom.val.app U q :=
  eq_of_heq (h.trans (heq_pieceReindex O hO A L U hij q).symm)

/-- The local section of a homogeneous piece determined by a pair of local sections depends,
up to heterogeneous equality, only on the two sections. -/
theorem heq_tensorSectionsAt_of_eq (U : Cᵒᵖ) {i j : ℤ} (hij : i = j)
    {x : (A i).val.obj U} {x' : (A j).val.obj U} (hx : HEq x x')
    {s : (TensorPower.tensorPower O hO L i).val.obj U}
    {s' : (TensorPower.tensorPower O hO L j).val.obj U} (hs : HEq s s') :
    HEq (tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s)
      (tensorSectionsAt O hO U (A j) (TensorPower.tensorPower O hO L j) x' s') := by
  subst hij
  rw [eq_of_heq hx, eq_of_heq hs]

/-- The coherent multiplication of the tensor powers of `L`, read on local sections, is the
multiplication of the Laurent algebra. -/
theorem coherentMulIso_app_eq_mulBilinear (i j : ℤ) (U : Cᵒᵖ)
    (s : (TensorPower.tensorPower O hO L i).val.obj U)
    (t : (TensorPower.tensorPower O hO L j).val.obj U) :
    (TensorPower.coherentMulIso O hO L i j).hom.val.app U
        (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L i)
          (TensorPower.tensorPower O hO L j) s t) =
      (TensorPower.mulBilinear O hO L i j).app U s t :=
  (TensorPower.mulBilinear_app O hO L i j U s t).symm

/-! ### The algebra laws of the twist -/

variable (ε : SheafOfModules.unit (structureSheaf O hO) ⟶ A 0)

/-- **The unit of the twist**: the unit of `A` tensored with the unit section of the zeroth
tensor power of `L`, as a morphism out of the structure sheaf. -/
def oneMor : SheafOfModules.unit (structureSheaf O hO) ⟶ piece O hO A L 0 :=
  ε ≫ (tensorProductRightUnitor O hO (A 0)).inv

/-- The unit of the twist, as a restriction-compatible family of local sections. -/
def oneSec (U : Cᵒᵖ) : (piece O hO A L 0).val.obj U :=
  tensorSectionsAt O hO U (A 0) (TensorPower.tensorPower O hO L 0)
    (ε.val.app U (unitSection O hO U)) ((TensorPower.oneSection O hO L).eval U)

/-- The unit morphism of the twist on the unit section. -/
theorem oneMor_app (U : Cᵒᵖ) :
    (oneMor O hO A L ε).val.app U (unitSection O hO U) = oneSec O hO A L ε U := by
  change (tensorProductRightUnitor O hO (A 0)).inv.val.app U
    (ε.val.app U (unitSection O hO U)) = _
  rw [tensorSections_rightUnitorInvAt]
  rfl

/-- Inserting the unit of the twist on the left. -/
def insertOneLeft (i : ℤ) :
    piece O hO A L i ⟶
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((piece O hO A L 0))).obj ((piece O hO A L i))) :=
  (tensorProductLeftUnitor O hO (piece O hO A L i)).inv ≫
    tensorMap O hO (oneMor O hO A L ε) (𝟙 (piece O hO A L i))

/-- Inserting the unit of the twist on the right. -/
def insertOneRight (i : ℤ) :
    piece O hO A L i ⟶
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((piece O hO A L i))).obj ((piece O hO A L 0))) :=
  (tensorProductRightUnitor O hO (piece O hO A L i)).inv ≫
    tensorMap O hO (𝟙 (piece O hO A L i)) (oneMor O hO A L ε)

/-- Inserting the unit of the twist on the left, on local sections. -/
theorem insertOneLeft_app (i : ℤ) (U : Cᵒᵖ) (m : (piece O hO A L i).val.obj U) :
    (insertOneLeft O hO A L ε i).val.app U m =
      tensorSectionsAt O hO U (piece O hO A L 0) (piece O hO A L i) (oneSec O hO A L ε U) m := by
  change (tensorMap O hO (oneMor O hO A L ε) (𝟙 (piece O hO A L i))).val.app U
    ((tensorProductLeftUnitor O hO (piece O hO A L i)).inv.val.app U m) = _
  rw [tensorSections_leftUnitorInvAt, tensorMap_app, id_app, oneMor_app]

/-- Inserting the unit of the twist on the right, on local sections. -/
theorem insertOneRight_app (i : ℤ) (U : Cᵒᵖ) (m : (piece O hO A L i).val.obj U) :
    (insertOneRight O hO A L ε i).val.app U m =
      tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L 0) m (oneSec O hO A L ε U) := by
  change (tensorMap O hO (𝟙 (piece O hO A L i)) (oneMor O hO A L ε)).val.app U
    ((tensorProductRightUnitor O hO (piece O hO A L i)).inv.val.app U m) = _
  rw [tensorSections_rightUnitorInvAt, tensorMap_app, id_app, oneMor_app]


/-- Multiplication of the twist on a pair of pure local sections, as a morphism applied to a
local section. -/
theorem mulMor_app_pure (i j : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U)
    (s : (TensorPower.tensorPower O hO L i).val.obj U) (y : (A j).val.obj U)
    (t : (TensorPower.tensorPower O hO L j).val.obj U) :
    (mulMor O hO A ν L i j).val.app U
        (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L j)
          (tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s)
          (tensorSectionsAt O hO U (A j) (TensorPower.tensorPower O hO L j) y t)) =
      tensorSectionsAt O hO U (A (i + j)) (TensorPower.tensorPower O hO L (i + j))
        (mulA O hO A ν i j U x y) ((TensorPower.mulBilinear O hO L i j).app U s t) := by
  rw [show (mulMor O hO A ν L i j).val.app U
      (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L j)
        (tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s)
        (tensorSectionsAt O hO U (A j) (TensorPower.tensorPower O hO L j) y t)) =
      mulSection O hO A ν L i j U
        (tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s)
        (tensorSectionsAt O hO U (A j) (TensorPower.tensorPower O hO L j) y t) from rfl,
    mulSection_pure, coherentMulIso_app_eq_mulBilinear]
  rfl

/-- The unit of the twist, unfolded. -/
theorem oneSec_def (U : Cᵒᵖ) :
    oneSec O hO A L ε U = tensorSectionsAt O hO U (A 0) (TensorPower.tensorPower O hO L 0)
      (ε.val.app U (unitSection O hO U)) ((TensorPower.oneSection O hO L).eval U) := rfl

/-- **Multiplication of the twist is commutative**, as an identity of morphisms of sheaves of
modules. -/
theorem mulMor_comm
    (hcomm : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U) (y : (A j).val.obj U),
      HEq (mulA O hO A ν i j U x y) (mulA O hO A ν j i U y x))
    (i j : ℤ) :
    mulMor O hO A ν L i j =
      (tensorProductBraiding O hO (piece O hO A L i) (piece O hO A L j)).hom ≫
        mulMor O hO A ν L j i ≫ (pieceReindex O hO A L (Int.add_comm j i)).hom := by
  refine hom_ext_tensor2 O hO (fun U x s y t => ?_)
  refine (mulMor_app_pure O hO A ν L i j U x s y t).trans ?_
  refine Eq.trans ?_ ((congrArg
    (fun sectionValue => (pieceReindex O hO A L (Int.add_comm j i)).hom.val.app U
      ((mulMor O hO A ν L j i).val.app U sectionValue))
    (tensorSections_braidingAt O hO U (piece O hO A L i) (piece O hO A L j)
      (tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s)
      (tensorSectionsAt O hO U (A j) (TensorPower.tensorPower O hO L j) y t))).trans
        (congrArg ((pieceReindex O hO A L (Int.add_comm j i)).hom.val.app U)
          (mulMor_app_pure O hO A ν L j i U y t x s))).symm
  refine eq_pieceReindex_of_heq O hO A L U _ _ _ ?_
  exact heq_tensorSectionsAt_of_eq O hO A L U (Int.add_comm i j) (hcomm i j U x y)
    (TensorPower.mulBilinear_comm O hO L i j U s t)

/-- **Multiplication of the twist is associative**, as an identity of morphisms of sheaves of
modules. -/
theorem mulMor_assoc
    (hassoc : ∀ (i j k : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U) (y : (A j).val.obj U)
        (z : (A k).val.obj U),
      HEq (mulA O hO A ν (i + j) k U (mulA O hO A ν i j U x y) z)
        (mulA O hO A ν i (j + k) U x (mulA O hO A ν j k U y z)))
    (i j k : ℤ) :
    tensorMap O hO (mulMor O hO A ν L i j) (𝟙 (piece O hO A L k)) ≫
        mulMor O hO A ν L (i + j) k =
      (tensorProductAssociator O hO (piece O hO A L i) (piece O hO A L j)
          (piece O hO A L k)).hom ≫
        tensorMap O hO (𝟙 (piece O hO A L i)) (mulMor O hO A ν L j k) ≫
        mulMor O hO A ν L i (j + k) ≫
        (pieceReindex O hO A L (Int.add_assoc i j k).symm).hom := by
  refine hom_ext_tensor3 O hO (fun U x s y t z u => ?_)
  let leftSection := tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s
  let middleSection := tensorSectionsAt O hO U (A j) (TensorPower.tensorPower O hO L j) y t
  let rightSection := tensorSectionsAt O hO U (A k) (TensorPower.tensorPower O hO L k) z u
  have leftValue := (congrArg ((mulMor O hO A ν L (i + j) k).val.app U)
    ((tensorMap_app O hO (mulMor O hO A ν L i j) (𝟙 (piece O hO A L k)) U
      (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L j) leftSection middleSection)
      rightSection).trans
        (congrArg (fun sectionValue => tensorSectionsAt O hO U
          (piece O hO A L (i + j)) (piece O hO A L k) sectionValue rightSection)
          (mulMor_app_pure O hO A ν L i j U x s y t)))).trans
    (mulMor_app_pure O hO A ν L (i + j) k U (mulA O hO A ν i j U x y)
      ((TensorPower.mulBilinear O hO L i j).app U s t) z u)
  have rightValue := congrArg ((pieceReindex O hO A L (Int.add_assoc i j k).symm).hom.val.app U)
    ((congrArg (fun sectionValue => (mulMor O hO A ν L i (j + k)).val.app U
      ((tensorMap O hO (𝟙 (piece O hO A L i)) (mulMor O hO A ν L j k)).val.app U sectionValue))
      (tensorSections_associatorAt O hO U (piece O hO A L i) (piece O hO A L j)
        (piece O hO A L k) leftSection middleSection rightSection)).trans
      ((congrArg ((mulMor O hO A ν L i (j + k)).val.app U)
        ((tensorMap_app O hO (𝟙 (piece O hO A L i)) (mulMor O hO A ν L j k) U leftSection
          (tensorSectionsAt O hO U (piece O hO A L j) (piece O hO A L k) middleSection
              rightSection)).trans
            (congrArg
                (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L (j + k)) leftSection)
              (mulMor_app_pure O hO A ν L j k U y t z u)))).trans
        (mulMor_app_pure O hO A ν L i (j + k) U x s (mulA O hO A ν j k U y z)
          ((TensorPower.mulBilinear O hO L j k).app U t u))))
  refine leftValue.trans (Eq.trans ?_ rightValue.symm)
  refine eq_pieceReindex_of_heq O hO A L U _ _ _ ?_
  exact heq_tensorSectionsAt_of_eq O hO A L U (Int.add_assoc i j k)
    (hassoc i j k U x y z) (TensorPower.mulBilinear_assoc O hO L i j k U s t u)

/-- **The unit of the twist is a left identity**, as an identity of morphisms of sheaves of
modules. -/
theorem mulMor_one_mul
    (hone : ∀ (i : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U),
      HEq (mulA O hO A ν 0 i U (ε.val.app U (unitSection O hO U)) x) x)
    (i : ℤ) :
    insertOneLeft O hO A L ε i ≫ mulMor O hO A ν L 0 i =
      (pieceReindex O hO A L (Int.zero_add i).symm).hom := by
  refine hom_ext_tensor O hO (fun U x s => ?_)
  refine (congrArg ((mulMor O hO A ν L 0 i).val.app U)
    (insertOneLeft_app O hO A L ε i U
      (tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s))).trans ?_
  refine (mulMor_app_pure O hO A ν L 0 i U (ε.val.app U (unitSection O hO U))
    ((TensorPower.oneSection O hO L).eval U) x s).trans ?_
  refine eq_pieceReindex_of_heq O hO A L U _ _ _ ?_
  exact heq_tensorSectionsAt_of_eq O hO A L U (Int.zero_add i) (hone i U x)
    (TensorPower.mulBilinear_one_mul O hO L i U s)

/-- **The unit of the twist is a right identity**, as an identity of morphisms of sheaves of
modules. -/
theorem mulMor_mul_one
    (hone : ∀ (i : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U),
      HEq (mulA O hO A ν i 0 U x (ε.val.app U (unitSection O hO U))) x)
    (i : ℤ) :
    insertOneRight O hO A L ε i ≫ mulMor O hO A ν L i 0 =
      (pieceReindex O hO A L (Int.add_zero i).symm).hom := by
  refine hom_ext_tensor O hO (fun U x s => ?_)
  refine (congrArg ((mulMor O hO A ν L i 0).val.app U)
    (insertOneRight_app O hO A L ε i U
      (tensorSectionsAt O hO U (A i) (TensorPower.tensorPower O hO L i) x s))).trans ?_
  refine (mulMor_app_pure O hO A ν L i 0 U x s (ε.val.app U (unitSection O hO U))
    ((TensorPower.oneSection O hO L).eval U)).trans ?_
  refine eq_pieceReindex_of_heq O hO A L U _ _ _ ?_
  exact heq_tensorSectionsAt_of_eq O hO A L U (Int.add_zero i) (hone i U x)
    (TensorPower.mulBilinear_mul_one O hO L i U s)


/-! ### Bilinearity and naturality of the multiplication -/

/-- The section of a tensor product determined by a pair of local sections is additive in its
first argument. -/
theorem tensorSectionsAt_add_left (U : Cᵒᵖ) (F G : SheafOfModules.{w} (structureSheaf O hO))
    (s s' : F.val.obj U) (t : G.val.obj U) :
    tensorSectionsAt O hO U F G (s + s') t =
      tensorSectionsAt O hO U F G s t + tensorSectionsAt O hO U F G s' t := by
  exact (congrArg ((toSheafify O hO (F.val ⊗ G.val)).app U) (TensorProduct.add_tmul s s' t)).trans
    (map_add _ _ _)

/-- The section of a tensor product determined by a pair of local sections is additive in its
second argument. -/
theorem tensorSectionsAt_add_right (U : Cᵒᵖ) (F G : SheafOfModules.{w} (structureSheaf O hO))
    (s : F.val.obj U) (t t' : G.val.obj U) :
    tensorSectionsAt O hO U F G s (t + t') =
      tensorSectionsAt O hO U F G s t + tensorSectionsAt O hO U F G s t' := by
  exact (congrArg ((toSheafify O hO (F.val ⊗ G.val)).app U) (TensorProduct.tmul_add s t t')).trans
    (map_add _ _ _)

/-- The section of a tensor product determined by a pair of local sections is linear in its
first argument. -/
theorem tensorSectionsAt_smul_left (U : Cᵒᵖ) (F G : SheafOfModules.{w} (structureSheaf O hO))
    (r : (structureSheaf O hO).obj.obj U) (s : F.val.obj U) (t : G.val.obj U) :
    tensorSectionsAt O hO U F G (r • s) t =
      r • (show ((sheafify O hO).obj (F.val ⊗ G.val)).val.obj U from
        tensorSectionsAt O hO U F G s t) :=
  ((toSheafify O hO (F.val ⊗ G.val)).app U).hom.map_smul r (ptmul O hO F.val G.val U s t)

/-- The section of a tensor product determined by a pair of local sections is linear in its
second argument. -/
theorem tensorSectionsAt_smul_right (U : Cᵒᵖ) (F G : SheafOfModules.{w} (structureSheaf O hO))
    (r : (structureSheaf O hO).obj.obj U) (s : F.val.obj U) (t : G.val.obj U) :
    tensorSectionsAt O hO U F G s (r • t) =
      r • (show ((sheafify O hO).obj (F.val ⊗ G.val)).val.obj U from
        tensorSectionsAt O hO U F G s t) :=
  (congrArg ((toSheafify O hO (F.val ⊗ G.val)).app U)
    (TensorProduct.tmul_smul (show ↑(O.obj U) from r) s t)).trans
      (((toSheafify O hO (F.val ⊗ G.val)).app U).hom.map_smul r _)

/-- The section of a tensor product determined by a pair of local sections is compatible with
restriction. -/
theorem tensorSectionsAt_naturality (F G : SheafOfModules.{w} (structureSheaf O hO))
    {U V : Cᵒᵖ} (f : U ⟶ V) (s : F.val.obj U) (t : G.val.obj U) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
        (G))).val.map f (tensorSectionsAt O hO U F G s t) =
      tensorSectionsAt O hO V F G (F.val.map f s) (G.val.map f t) :=
  (PresheafOfModules.naturality_apply (toSheafify O hO (F.val ⊗ G.val)) f
    (ptmul O hO F.val G.val U s t)).symm

/-! ### The algebra laws on local sections -/

/-- Multiplication of the twist is additive in its first argument. -/
theorem mulSection_add_left (i j : ℤ) (U : Cᵒᵖ) (a a' : (piece O hO A L i).val.obj U)
    (b : (piece O hO A L j).val.obj U) :
    mulSection O hO A ν L i j U (a + a') b =
      mulSection O hO A ν L i j U a b + mulSection O hO A ν L i j U a' b := by
  exact (congrArg ((mulMor O hO A ν L i j).val.app U) (tensorSectionsAt_add_left ..)).trans
    (map_add _ _ _)

/-- Multiplication of the twist is additive in its second argument. -/
theorem mulSection_add_right (i j : ℤ) (U : Cᵒᵖ) (a : (piece O hO A L i).val.obj U)
    (b b' : (piece O hO A L j).val.obj U) :
    mulSection O hO A ν L i j U a (b + b') =
      mulSection O hO A ν L i j U a b + mulSection O hO A ν L i j U a b' := by
  exact (congrArg ((mulMor O hO A ν L i j).val.app U) (tensorSectionsAt_add_right ..)).trans
    (map_add _ _ _)

/-- Multiplication of the twist is linear in its first argument. -/
theorem mulSection_smul_left (i j : ℤ) (U : Cᵒᵖ) (r : (structureSheaf O hO).obj.obj U)
    (a : (piece O hO A L i).val.obj U) (b : (piece O hO A L j).val.obj U) :
    mulSection O hO A ν L i j U (r • a) b = r • mulSection O hO A ν L i j U a b := by
  exact (congrArg ((mulMor O hO A ν L i j).val.app U) (tensorSectionsAt_smul_left ..)).trans
    (((mulMor O hO A ν L i j).val.app U).hom.map_smul r _)

/-- Multiplication of the twist is linear in its second argument. -/
theorem mulSection_smul_right (i j : ℤ) (U : Cᵒᵖ) (r : (structureSheaf O hO).obj.obj U)
    (a : (piece O hO A L i).val.obj U) (b : (piece O hO A L j).val.obj U) :
    mulSection O hO A ν L i j U a (r • b) = r • mulSection O hO A ν L i j U a b := by
  exact (congrArg ((mulMor O hO A ν L i j).val.app U) (tensorSectionsAt_smul_right ..)).trans
    (((mulMor O hO A ν L i j).val.app U).hom.map_smul r _)

/-- Multiplication of the twist commutes with restriction. -/
theorem mulSection_naturality (i j : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (piece O hO A L i).val.obj U) (b : (piece O hO A L j).val.obj U) :
    (piece O hO A L (i + j)).val.map f (mulSection O hO A ν L i j U a b) =
      mulSection O hO A ν L i j V ((piece O hO A L i).val.map f a)
        ((piece O hO A L j).val.map f b) := by
  change (piece O hO A L (i + j)).val.map f
      ((mulMor O hO A ν L i j).val.app U
        (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L j) a b)) =
    (mulMor O hO A ν L i j).val.app V
      (tensorSectionsAt O hO V (piece O hO A L i) (piece O hO A L j)
        ((piece O hO A L i).val.map f a) ((piece O hO A L j).val.map f b))
  rw [← tensorSectionsAt_naturality]
  exact (PresheafOfModules.naturality_apply (mulMor O hO A ν L i j).val f _).symm

/-- **Multiplication of the twist is commutative on local sections.** -/
theorem mulSection_comm
    (hcomm : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U) (y : (A j).val.obj U),
      HEq (mulA O hO A ν i j U x y) (mulA O hO A ν j i U y x))
    (i j : ℤ) (U : Cᵒᵖ) (a : (piece O hO A L i).val.obj U)
    (b : (piece O hO A L j).val.obj U) :
    HEq (mulSection O hO A ν L i j U a b) (mulSection O hO A ν L j i U b a) := by
  have h := congrArg
    (fun φ :
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((piece O hO A L i))).obj ((piece O hO A L j))) ⟶ piece O hO A L (i + j) =>
      φ.val.app U (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L j) a b))
    (mulMor_comm O hO A ν L hcomm i j)
  have evaluation := congrArg
    (fun sectionValue => (pieceReindex O hO A L (Int.add_comm j i)).hom.val.app U
      ((mulMor O hO A ν L j i).val.app U sectionValue))
    (tensorSections_braidingAt O hO U (piece O hO A L i) (piece O hO A L j) a b)
  exact (heq_of_eq (h.trans evaluation)).trans (heq_pieceReindex O hO A L U _ _)

/-- **Multiplication of the twist is associative on local sections.** -/
theorem mulSection_assoc
    (hassoc : ∀ (i j k : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U) (y : (A j).val.obj U)
        (z : (A k).val.obj U),
      HEq (mulA O hO A ν (i + j) k U (mulA O hO A ν i j U x y) z)
        (mulA O hO A ν i (j + k) U x (mulA O hO A ν j k U y z)))
    (i j k : ℤ) (U : Cᵒᵖ) (a : (piece O hO A L i).val.obj U)
    (b : (piece O hO A L j).val.obj U) (c : (piece O hO A L k).val.obj U) :
    HEq (mulSection O hO A ν L (i + j) k U (mulSection O hO A ν L i j U a b) c)
      (mulSection O hO A ν L i (j + k) U a (mulSection O hO A ν L j k U b c)) := by
  have h := congrArg
    (fun φ :
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((piece O hO A L i))).obj ((piece O hO A L j)))))).obj ((piece O hO A L k))) ⟶ piece O hO A
        L (i + j + k) =>
      φ.val.app U (tensorSectionsAt O hO U
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            ((piece O hO A L i))).obj ((piece O hO A L j)))) (piece O hO A L k)
        (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L j) a b) c))
    (mulMor_assoc O hO A ν L hassoc i j k)
  have leftValue := congrArg ((mulMor O hO A ν L (i + j) k).val.app U)
    (tensorMap_app O hO (mulMor O hO A ν L i j) (𝟙 (piece O hO A L k)) U
      (tensorSectionsAt O hO U (piece O hO A L i) (piece O hO A L j) a b) c)
  have rightValue := congrArg ((pieceReindex O hO A L (Int.add_assoc i j k).symm).hom.val.app U)
    ((congrArg (fun sectionValue => (mulMor O hO A ν L i (j + k)).val.app U
      ((tensorMap O hO (𝟙 (piece O hO A L i)) (mulMor O hO A ν L j k)).val.app U sectionValue))
      (tensorSections_associatorAt O hO U (piece O hO A L i) (piece O hO A L j)
        (piece O hO A L k) a b c)).trans
      (congrArg ((mulMor O hO A ν L i (j + k)).val.app U)
        (tensorMap_app O hO (𝟙 (piece O hO A L i)) (mulMor O hO A ν L j k) U a
          (tensorSectionsAt O hO U (piece O hO A L j) (piece O hO A L k) b c))))
  exact (heq_of_eq (leftValue.symm.trans (h.trans rightValue))).trans
    (heq_pieceReindex O hO A L U _ _)

/-- **The unit of the twist is a left identity on local sections.** -/
theorem mulSection_one_mul
    (hone : ∀ (i : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U),
      HEq (mulA O hO A ν 0 i U (ε.val.app U (unitSection O hO U)) x) x)
    (i : ℤ) (U : Cᵒᵖ) (a : (piece O hO A L i).val.obj U) :
    HEq (mulSection O hO A ν L 0 i U (oneSec O hO A L ε U) a) a := by
  have h := congrArg
    (fun φ : piece O hO A L i ⟶ piece O hO A L (0 + i) => φ.val.app U a)
    (mulMor_one_mul O hO A ν L ε hone i)
  have evaluation := congrArg ((mulMor O hO A ν L 0 i).val.app U)
    (insertOneLeft_app O hO A L ε i U a)
  exact (heq_of_eq (evaluation.symm.trans h)).trans (heq_pieceReindex O hO A L U _ a)

/-- **The unit of the twist is a right identity on local sections.** -/
theorem mulSection_mul_one
    (hone : ∀ (i : ℤ) (U : Cᵒᵖ) (x : (A i).val.obj U),
      HEq (mulA O hO A ν i 0 U x (ε.val.app U (unitSection O hO U))) x)
    (i : ℤ) (U : Cᵒᵖ) (a : (piece O hO A L i).val.obj U) :
    HEq (mulSection O hO A ν L i 0 U a (oneSec O hO A L ε U)) a := by
  have h := congrArg
    (fun φ : piece O hO A L i ⟶ piece O hO A L (i + 0) => φ.val.app U a)
    (mulMor_mul_one O hO A ν L ε hone i)
  have evaluation := congrArg ((mulMor O hO A ν L i 0).val.app U)
    (insertOneRight_app O hO A L ε i U a)
  exact (heq_of_eq (evaluation.symm.trans h)).trans (heq_pieceReindex O hO A L U _ a)

/-- The unit of the twist is compatible with restriction. -/
theorem oneSec_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    (piece O hO A L 0).val.map f (oneSec O hO A L ε U) = oneSec O hO A L ε V := by
  refine (tensorSectionsAt_naturality O hO (A 0) (TensorPower.tensorPower O hO L 0)
    f (ε.val.app U (unitSection O hO U)) ((TensorPower.oneSection O hO L).eval U)).trans ?_
  exact congrArg₂ (tensorSectionsAt O hO V (A 0) (TensorPower.tensorPower O hO L 0))
    (((A 0).unitHomEquiv ε).property f) ((TensorPower.oneSection O hO L).property f)

/-- **A homogeneous piece of the twist in a degree where `A` vanishes is zero.** Tensoring by an
invertible sheaf of modules is an equivalence, and an equivalence takes zero objects to zero
objects. -/
theorem piece_isZero (n : ℤ) (hA : IsZero (A n)) : IsZero (piece O hO A L n) := by
  have hinv : Stacks.SheafOfModules.IsInvertible O hO (TensorPower.tensorPower O hO L n) :=
    TensorPower.isInvertible_tensorPower O hO L n
  have hequiv := TensorPower.isEquivalence_tensorRightFunctor O hO
    (TensorPower.tensorPower O hO L n)
  exact (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).flip.obj
      ((TensorPower.tensorPower O hO L n)))).map_isZero hA


end Site

section Scheme

variable {S : Scheme.{u}} (𝒜 : RelativeProjBridge.SheafGradedAlgebra S) (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- Tensoring on the right by an invertible `𝒪_S`-module is an equivalence, in the spelling in
which the integer tensor powers of Tag 01CU are defined. -/
instance isEquivalence_tensorRightFunctor :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
        ⟨S.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (S.sheaf.obj) (forget₂ CommRingCat RingCat)
        (S.ringCatSheaf.property)⟩).flip.obj (L))).IsEquivalence :=
  TensorPower.isEquivalence_tensorRightFunctor S.sheaf.obj S.ringCatSheaf.property L

/-- An `𝒪_S`-bilinear map of `𝒪_S`-modules on a scheme, read as a bilinear map of the
underlying presheaves of modules. -/
def toBilinear {M N P : S.Modules} (β : RelativeProjBridge.SheafBilinearMap M N P) :
    Stacks.BilinearMap M.val N.val P.val where
  app X := β.app X.unop
  map_smul_left X r x y := β.map_smul_left X.unop r x y
  map_smul_right X r x y := β.map_smul_right X.unop r x y
  naturality f x y := β.naturality (leOfHom f.unop) x y

/-- **The multiplication of a sheaf-level graded algebra as a morphism out of the tensor product
sheaf**: the bilinear map on sections extends uniquely over the sheafification. -/
def mulHom (i j : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (S.sheaf.obj) (forget₂ CommRingCat RingCat)
        (S.ringCatSheaf.property)⟩).obj ((𝒜.piece i))).obj ((𝒜.piece j))) ⟶ 𝒜.piece (i + j) :=
  ((sheafifyAdjunction S.sheaf.obj S.ringCatSheaf.property).homEquiv
    ((PresheafOfModules.tensorObj (O := S.sheaf.obj) ((𝒜.piece i).val) ((𝒜.piece j).val)))
      (𝒜.piece (i + j))).symm
      (PresheafOfModules.ofBilinear (toBilinear (𝒜.mul i j)))

/-- The multiplication morphism of a sheaf-level graded algebra on the local section determined
by a pair of homogeneous local sections. -/
theorem mulHom_app (i j : ℤ) (U : S.Opensᵒᵖ) (x : (𝒜.piece i).val.obj U)
    (y : (𝒜.piece j).val.obj U) :
    (mulHom 𝒜 i j).val.app U
        (tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property U (𝒜.piece i) (𝒜.piece j) x y) =
      (𝒜.mul i j).app U.unop x y :=
  (congrArg
      (fun φ => φ.app U (ptmul S.sheaf.obj S.ringCatSheaf.property (𝒜.piece i).val
        (𝒜.piece j).val U x y))
      (((sheafifyAdjunction S.sheaf.obj S.ringCatSheaf.property).homEquiv
        ((PresheafOfModules.tensorObj (O := S.sheaf.obj) ((𝒜.piece i).val) ((𝒜.piece j).val)))
          (𝒜.piece (i + j))).apply_symm_apply
          (PresheafOfModules.ofBilinear (toBilinear (𝒜.mul i j))))).trans
    (PresheafOfModules.ofBilinear_tmul (toBilinear (𝒜.mul i j)) U x y)

/-- **The unit of a sheaf-level graded algebra as a morphism out of the structure sheaf.** -/
def oneHom : SheafOfModules.unit
      (structureSheaf S.sheaf.obj S.ringCatSheaf.property) ⟶ 𝒜.piece 0 :=
  (𝒜.piece 0).unitHomEquiv.symm ((𝒜.piece 0).val.sectionsMk (fun X => 𝒜.one X.unop)
    (fun {_ _} f => 𝒜.one_res (leOfHom f.unop)))

/-- The unit morphism of a sheaf-level graded algebra on the unit section. -/
theorem oneHom_app (U : S.Opensᵒᵖ) :
    (oneHom 𝒜).val.app U (unitSection S.sheaf.obj S.ringCatSheaf.property U) =
      𝒜.one U.unop :=
  congrArg (fun σ : (𝒜.piece 0).sections => σ.val U)
    ((𝒜.piece 0).unitHomEquiv.apply_symm_apply _)

/-- Multiplication of a sheaf-level graded algebra read through `mulHom`. -/
theorem mulA_eq (i j : ℤ) (U : S.Opensᵒᵖ) (x : (𝒜.piece i).val.obj U)
    (y : (𝒜.piece j).val.obj U) :
    mulA S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) i j U x y =
      (𝒜.mul i j).app U.unop x y :=
  mulHom_app 𝒜 i j U x y

/-- **The twist of a quasi-coherent graded `𝒪_S`-algebra by an invertible `𝒪_S`-module**: the
homogeneous piece of degree `d` is `𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}`, with the multiplication induced by
that of `𝒜` and the coherent multiplication of the tensor powers of `ℒ`.

This is the graded algebra `ℬ` of the setting of Tag 02NB. -/
def twist : RelativeProjBridge.SheafGradedAlgebra S where
  piece d := piece S.sheaf.obj S.ringCatSheaf.property 𝒜.piece L d
  mul i j :=
    { app := fun U => AddMonoidHom.mk'
        (fun a => AddMonoidHom.mk'
          (fun b => mulSection S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L i j
            (op U) a b)
          (fun b b' => mulSection_add_right S.sheaf.obj S.ringCatSheaf.property 𝒜.piece
            (mulHom 𝒜) L i j (op U) a b b'))
        (fun a a' => by
          ext b
          exact mulSection_add_left S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L
            i j (op U) a a' b)
      map_smul_left := fun U r x y =>
        mulSection_smul_left S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L i j
          (op U) r x y
      map_smul_right := fun U r x y =>
        mulSection_smul_right S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L i j
          (op U) r x y
      naturality := fun {_ _} h x y =>
        mulSection_naturality S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L i j
          (homOfLE h).op x y }
  one U := oneSec S.sheaf.obj S.ringCatSheaf.property 𝒜.piece L (oneHom 𝒜) (op U)
  one_res h := oneSec_naturality S.sheaf.obj S.ringCatSheaf.property 𝒜.piece L (oneHom 𝒜)
    (homOfLE h).op
  mul_assoc i j k U a b c := by
    refine mulSection_assoc S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L ?_
      i j k (op U) a b c
    intro i j k V x y z
    rw [mulA_eq, mulA_eq, mulA_eq, mulA_eq]
    exact 𝒜.mul_assoc i j k V.unop x y z
  one_mul i U a := by
    refine mulSection_one_mul S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L
      (oneHom 𝒜) ?_ i (op U) a
    intro i V x
    rw [mulA_eq, oneHom_app]
    exact 𝒜.one_mul i V.unop x
  mul_one i U a := by
    refine mulSection_mul_one S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L
      (oneHom 𝒜) ?_ i (op U) a
    intro i V x
    rw [mulA_eq, oneHom_app]
    exact 𝒜.mul_one i V.unop x
  mul_comm i j U a b := by
    refine mulSection_comm S.sheaf.obj S.ringCatSheaf.property 𝒜.piece (mulHom 𝒜) L ?_
      i j (op U) a b
    intro i j V x y
    rw [mulA_eq, mulA_eq]
    exact 𝒜.mul_comm i j V.unop x y
  negative_isZero n hn :=
    piece_isZero S.sheaf.obj S.ringCatSheaf.property 𝒜.piece L n (𝒜.negative_isZero n hn)
  isQuasicoherent n := by
    have hinv : Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property
        (TensorPower.tensorPower S.sheaf.obj S.ringCatSheaf.property L n) :=
      TensorPower.isInvertible_tensorPower S.sheaf.obj S.ringCatSheaf.property L n
    have hL : (TensorPower.tensorPower S.sheaf.obj S.ringCatSheaf.property L n).IsQuasicoherent :=
      @Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible S _ hinv
    exact Scheme.Modules.isQuasicoherent_tensorObj (𝒜.piece n) _ (𝒜.isQuasicoherent n) hL

add_to_stacks 02NB "the twisted graded algebra B_d = A_d ⊗ L^{⊗ d} of the section's setting" twist

end Scheme


end Stacks.AlgebraicGeometry.GradedAlgebraTwist

end
