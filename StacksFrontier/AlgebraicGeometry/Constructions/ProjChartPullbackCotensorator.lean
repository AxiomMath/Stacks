module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartSectionPullbackMul
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.SheafOfModules
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.PowerCompareAgreement

/-!
# The cotensorator of an inverse image, and multiplicativity of the pullback of sections

Let `j : Y' ⟶ Y` be a morphism of schemes and `L` an invertible `𝒪_Y`-module. Stacks Tag 01CD
says that `j^*` carries a tensor product to a tensor product. This file reads that comparison as a
**cotensorator**

  `δ_{A,B} : j^*(A ⊗ B) ⟶ j^*A ⊗ j^*B`

for the monoidal structure in which `Stacks.TensorPowers.natTensorPow` and
`Stacks.GradedSections.mulMap` are written, proves it natural in both variables, and computes the
successor step of the comparison of the tensor powers
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso` in terms of it. That
discharges the hypotheses of
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullSection_mulSections_of_succ`, so

  `pullSection j L (n + m) (s · t) = pullSection j L n s · pullSection j L m t`

holds in every pair of degrees, with no hypothesis.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackCotensorator`: the cotensorator
  `j^*(A ⊗ B) ⟶ j^*A ⊗ j^*B`, built from Stacks Tag 01CD by the comparison
  `Stacks.AmplePullbackPart1.tensorIsoTensorModules` of the monoidal tensor product with the tensor
  product sheaf of Stacks Tag 01CA on each side.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackCotensorator_tensorHom`, and its
  two whiskered forms `..._whiskerRight` and `..._whiskerLeft`: **the cotensorator is natural in
  both variables.** This is the naturality of Stacks Tag 01CD, conjugated by the naturality of the
  comparison of the two spellings of the tensor product.
* `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackPowIso_succ`: **the successor
  step**, `c (k + 1) = δ_{L ^⊗ k, L} ≫ (c k ▷ j^*L)`, where `c` is the comparison
  `j^*(L ^⊗ n) ⟶ (j^*L) ^⊗ n` of Stacks Tag 01CD iterated. The content is that the multiplication
  of the tensor powers of Stacks Tag 01CU in bidegree `(k, 1)` is the identification of the first
  power with `L`, which is
  `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_one_right_natCast`.
* `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackNatTensorPowIso_inv_succ`: that
  step for `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso`.
* `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.mulMap_comp_pullbackNatTensorPowIso_inv`:
  **the identity of morphisms** behind multiplicativity, in every degree and with no hypothesis.
* `Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullSection_mulSections`: **pulling back
  a product of global sections of tensor powers is the product of the pullbacks**, in every pair of
  degrees.

## Implementation notes

**Which monoidal structure.** Every `⊗`, `▷`, `◁` and `⊗ₘ` below is read in
`Stacks.SheafInternalHom.schemeMonoidalCategory`, the structure obtained by localizing the
sectionwise monoidal structure on presheaves of modules along sheafification; this is the structure
`Stacks.TensorPowers.natTensorPow` and `Stacks.GradedSections.mulMap` are written in. Its tensor
product is *not* the tensor product sheaf of Stacks Tag 01CA on the nose — not even up to
definitional equality, the localized tensor product having no reduction to a sheafification — and
Stacks Tag 01CD is available for the tensor product sheaf. The two are compared by
`Stacks.AmplePullbackPart1.tensorIsoTensorModules`, whose naturality against the functorial action
of the tensor product sheaf is `Stacks.TensorSheafSpellingIso.monoidalTensorIso_naturality`.
The equality `Stacks.SheafOfModules.Invertible.tensorIso_eq_tensorObjIso` identifies the existing
comparison with that canonical comparison, whose naturality makes the conjugation possible.

**Spelling, and why four objects are named again.** Four kinds of term have a type that is not
type-correct at the transparency the rewriting tactics check their motives at, each because an
argument of type `AlgebraicGeometry.Scheme.Modules` stands where a sheaf of modules over a
differently-spelled sheaf of rings is expected: the functorial action of the tensor product sheaf,
the comparison of Stacks Tag 01CD (stated over
`RingedSpaceModuleAdjunction.modulePullback` rather than
`AlgebraicGeometry.Scheme.Modules.pullback`), the multiplication of the tensor powers, and the
comparison of the powers. Each is therefore given a name again at the spelling needed here —
`tensorModulesMap`, `pullbackTensorModules`, `natTensorPowSuccIso`, `pullbackPowIso` — whose type
is semireducible and so survives the motive check. Every one of them is its original by `rfl`.
`tensorModulesMap` is the same morphism as `Stacks.Algebraization.tensorModulesMap`, which is not
used here only because it sits in a module whose import closure is an order of magnitude larger.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (mulMap)
open Stacks.AmplePullbackPart1 (tensorIsoTensorModules)
open Stacks.RelativeVeryAmple (tensorModules pullbackTensorModulesIso pullbackTensorPowModuleIso)
open Stacks.Ample (tensorPowModule tensorPowModuleAddIso tensorPowModuleOneIso IsInvertibleModule)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf mulSections)
open Stacks.AlgebraicGeometry.ProjChartSectionPullback (pullbackNatTensorPowIso_inv)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  PresheafOfModules.toPresheaf PresheafOfModulesOfCommRing.Monoidal.tensorObj
  TopCat.Sheaf TopCat.Presheaf.IsSheaf AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The tensor product sheaf, and Stacks Tag 01CD, named again -/

/-- **The tensor product of two morphisms of `𝒪_Z`-modules**, read off the two legs of the
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` and typed over
`Stacks.RelativeVeryAmple.tensorModules`, as `Stacks.RelativeVeryAmple.tensorModulesMapIso` is.
The legs are composed in the order of `Functor.uncurry`'s action on a pair; the product category
itself is not used, its unification with `Z.Modules × Z.Modules` exhausting the heartbeat
budget. -/
def tensorModulesMap (Z : Scheme.{u}) {A A' B B' : Z.Modules} (a : A ⟶ A') (b : B ⟶ B') :
    tensorModules Z A B ⟶ tensorModules Z A' B' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
      Z.presheaf (forget₂ CommRingCat RingCat)
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z)⟩).map a).app B ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
      Z.presheaf (forget₂ CommRingCat RingCat)
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z)⟩).obj A').map b

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y)

/-- **Stacks Tag 01CD** at the `AlgebraicGeometry.Scheme.Modules.pullback` spelling of the inverse
image: `j^*(A ⊗ B) ≅ j^*A ⊗ j^*B` for the tensor product sheaf of Stacks Tag 01CA. This is
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`, which records
`RingedSpaceModuleAdjunction.modulePullback` in its type instead. -/
def pullbackTensorModules (A B : Y.Modules) :
    (Scheme.Modules.pullback j).obj (tensorModules Y A B) ≅
      tensorModules Y' ((Scheme.Modules.pullback j).obj A)
        ((Scheme.Modules.pullback j).obj B) :=
  pullbackTensorModulesIso j A B

/-- **The comparison of the monoidal tensor product with the tensor product sheaf is natural in
both variables.** The existing equality with the canonical comparison reduces this to
`Stacks.TensorSheafSpellingIso.monoidalTensorIso_naturality`, with `tensorModulesMap` on the
right. -/
private theorem tensorIsoTensorModules_naturality (Z : Scheme.{u}) {A A' B B' : Z.Modules}
    (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g) ≫ (tensorIsoTensorModules Z A' B').hom
      = (tensorIsoTensorModules Z A B).hom ≫ tensorModulesMap Z f g := by
  have comparison (A B : Z.Modules) : (tensorIsoTensorModules Z A B).hom =
      (Stacks.TensorSheafSpellingIso.monoidalTensorIso Z A B).hom :=
    congrArg Iso.hom (Stacks.SheafOfModules.Invertible.tensorIso_eq_tensorObjIso Z.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) A B)
  rw [comparison, comparison]
  exact Stacks.TensorSheafSpellingIso.monoidalTensorIso_naturality Z f g

/-- The same naturality read along the inverse comparison. -/
private theorem tensorIsoTensorModules_inv_naturality (Z : Scheme.{u}) {A A' B B' : Z.Modules}
    (f : A ⟶ A') (g : B ⟶ B') :
    (tensorIsoTensorModules Z A B).inv ≫ (f ⊗ₘ g)
      = tensorModulesMap Z f g ≫ (tensorIsoTensorModules Z A' B').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIsoTensorModules_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **Stacks Tag 01CD is natural in both module arguments**: its comparison is a morphism of
bifunctors, so this is one component of `CategoryTheory.NatTrans.naturality`. -/
theorem pullbackTensorModules_naturality {A A' B B' : Y.Modules} (a : A ⟶ A') (b : B ⟶ B') :
    (Scheme.Modules.pullback j).map (tensorModulesMap Y a b) ≫ (pullbackTensorModules j A' B').hom
      = (pullbackTensorModules j A B).hom ≫
        tensorModulesMap Y' ((Scheme.Modules.pullback j).map a)
          ((Scheme.Modules.pullback j).map b) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso j.toLRSHom.toShHom).hom.naturality
    (((a, b) : ((A, B) : Y.Modules × Y.Modules) ⟶ (A', B')))

/-! ### The cotensorator -/

/-- **The cotensorator of the inverse image**, `j^*(A ⊗ B) ⟶ j^*A ⊗ j^*B`, for the monoidal
structure the tensor powers `Stacks.TensorPowers.natTensorPow` are read in: the comparison of
Stacks Tag 01CD, conjugated by `Stacks.AmplePullbackPart1.tensorIsoTensorModules` on the source and
on the target. It is an isomorphism, Tag 01CD's comparison being one, but only the morphism is
needed below. -/
def pullbackCotensorator (A B : Y.Modules) :
    (Scheme.Modules.pullback j).obj (A ⊗ B) ⟶
      (Scheme.Modules.pullback j).obj A ⊗ (Scheme.Modules.pullback j).obj B :=
  (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y A B).hom ≫
    (pullbackTensorModules j A B).hom ≫
      (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A)
        ((Scheme.Modules.pullback j).obj B)).inv

/-- The cotensorator, written out. Stated so that the three factors can be recognised inside a
longer composite without unfolding a definition in the goal. -/
theorem pullbackCotensorator_eq (A B : Y.Modules) :
    pullbackCotensorator j A B
      = (Scheme.Modules.pullback j).map (tensorIsoTensorModules Y A B).hom ≫
        (pullbackTensorModules j A B).hom ≫
          (tensorIsoTensorModules Y' ((Scheme.Modules.pullback j).obj A)
            ((Scheme.Modules.pullback j).obj B)).inv := rfl

/-- **The cotensorator is natural in both variables.** The naturality of Stacks Tag 01CD, with the
naturality of the comparison of the two spellings of the tensor product used once on each side. -/
theorem pullbackCotensorator_tensorHom {A A' B B' : Y.Modules} (a : A ⟶ A') (b : B ⟶ B') :
    (Scheme.Modules.pullback j).map (a ⊗ₘ b) ≫ pullbackCotensorator j A' B'
      = pullbackCotensorator j A B ≫
        ((Scheme.Modules.pullback j).map a ⊗ₘ (Scheme.Modules.pullback j).map b) := by
  simp only [pullbackCotensorator, Category.assoc]
  rw [← Functor.map_comp_assoc, tensorIsoTensorModules_naturality, Functor.map_comp_assoc,
    reassoc_of% (pullbackTensorModules_naturality j a b), ← tensorIsoTensorModules_inv_naturality]

/-- **Naturality of the cotensorator in the first variable**, in whiskered form. This is the
hypothesis `hδ` of
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullSection_mulSections_of_succ`. -/
theorem pullbackCotensorator_whiskerRight {A A' : Y.Modules} (h : A ⟶ A') (B : Y.Modules) :
    (Scheme.Modules.pullback j).map (h ▷ B) ≫ pullbackCotensorator j A' B
      = pullbackCotensorator j A B ≫
        ((Scheme.Modules.pullback j).map h ▷ (Scheme.Modules.pullback j).obj B) := by
  rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_id,
    ← (Scheme.Modules.pullback j).map_id B, pullbackCotensorator_tensorHom]

/-- **Naturality of the cotensorator in the second variable**, in whiskered form. This is what
moves the identification of the first tensor power with `L` out of the successor step of the
comparison of the powers. -/
theorem pullbackCotensorator_whiskerLeft (A : Y.Modules) {B B' : Y.Modules} (k : B ⟶ B') :
    (Scheme.Modules.pullback j).map (A ◁ k) ≫ pullbackCotensorator j A B'
      = pullbackCotensorator j A B ≫
        ((Scheme.Modules.pullback j).obj A ◁ (Scheme.Modules.pullback j).map k) := by
  rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.id_tensorHom,
    ← (Scheme.Modules.pullback j).map_id A, pullbackCotensorator_tensorHom]

/-! ### The successor step of the comparison of the tensor powers -/

variable (L : Y.Modules) [IsInvertibleModule Y L]

/-- **The multiplication of the tensor powers of Stacks Tag 01CU in bidegree `(k, 1)`**, typed over
`Stacks.TensorPowers.natTensorPow` and `Stacks.RelativeVeryAmple.tensorModules`. This is
`Stacks.Ample.tensorPowModuleAddIso`; the target is the `(k+1)`-st power on the nose, the powers
being an iterated tensor product in nonnegative degree. -/
def natTensorPowSuccIso (Z : Scheme.{u}) (M : Z.Modules) [IsInvertibleModule Z M] (k : ℕ) :
    tensorModules Z (natTensorPow M k) (tensorPowModule Z M 1) ≅ natTensorPow M (k + 1) :=
  tensorPowModuleAddIso Z M (k : ℤ) 1

/-- **The normalisation of the multiplication in bidegree `(k, 1)`**: it is the identification
`Stacks.Ample.tensorPowModuleOneIso` of the first power with `M`, whiskered into the `k`-th power,
read through the comparison of the two spellings of the tensor product. This is
`AlgebraicGeometry.SheafOfModules.tensorPowAddIso_one_right_natCast`. -/
private theorem tensorPowModuleAddIso_one (Z : Scheme.{u}) (M : Z.Modules)
    [IsInvertibleModule Z M] (k : ℕ) :
    tensorPowModuleAddIso Z M (k : ℤ) 1
      = (tensorIsoTensorModules Z (natTensorPow M k) (tensorPowModule Z M 1)).symm ≪≫
        whiskerLeftIso (natTensorPow M k) (tensorPowModuleOneIso Z M) :=
  congrArg (fun z => (tensorIsoTensorModules Z (natTensorPow M k)
      (tensorPowModule Z M 1)).symm ≪≫ z)
    (AlgebraicGeometry.SheafOfModules.tensorPowAddIso_one_right_natCast Z.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) M k)

/-- `natTensorPowSuccIso` in the forward direction. -/
theorem natTensorPowSuccIso_hom (Z : Scheme.{u}) (M : Z.Modules) [IsInvertibleModule Z M]
    (k : ℕ) :
    (natTensorPowSuccIso Z M k).hom
      = (tensorIsoTensorModules Z (natTensorPow M k) (tensorPowModule Z M 1)).inv ≫
        (natTensorPow M k ◁ (tensorPowModuleOneIso Z M).hom) :=
  congrArg Iso.hom (tensorPowModuleAddIso_one Z M k)

/-- `natTensorPowSuccIso` in the backward direction. -/
theorem natTensorPowSuccIso_inv (Z : Scheme.{u}) (M : Z.Modules) [IsInvertibleModule Z M]
    (k : ℕ) :
    (natTensorPowSuccIso Z M k).inv
      = (natTensorPow M k ◁ (tensorPowModuleOneIso Z M).inv) ≫
        (tensorIsoTensorModules Z (natTensorPow M k) (tensorPowModule Z M 1)).hom :=
  congrArg Iso.inv (tensorPowModuleAddIso_one Z M k)

/-- **The comparison `j^*(L ^⊗ n) ≅ (j^*L) ^⊗ n`** at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling of the inverse image and the
`Stacks.TensorPowers.natTensorPow` spelling of the powers. This is Stacks Tag 01CD iterated,
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`. -/
def pullbackPowIso (n : ℕ) :
    (Scheme.Modules.pullback j).obj (natTensorPow L n) ≅
      natTensorPow ((Scheme.Modules.pullback j).obj L) n :=
  pullbackTensorPowModuleIso j L n

/-- The comparison of the powers is the inverse of
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso`, which is how the
pullback of a section is read. -/
theorem pullbackPowIso_hom (n : ℕ) :
    (pullbackPowIso j L n).hom = (pullbackNatTensorPowIso j L n).inv :=
  (pullbackNatTensorPowIso_inv j L n).symm

/-- **The recursion defining the comparison of the powers, written out literally**: every
reindexing of the exponent and every spelling the recursion itself uses is kept, so that the only
definitional step here is the unfolding of the recursion.

Separating this from the removal of the two reindexings is what makes the successor step
affordable. A reindexing is an `CategoryTheory.eqToIso`, and reducing one asks whether
`((k + 1 : ℕ) : ℤ)` and `(k : ℤ) + 1` are the same integer; asked once, on its own, that is
immediate, but asked inside the whole composite — where the unifier meets it again for every
occurrence — it exhausts the heartbeat budget of a single declaration. -/
private theorem pullbackPowIso_hom_succ_literal (k : ℕ) :
    (pullbackPowIso j L (k + 1)).hom
      = (Scheme.Modules.pullback j).map
            ((Stacks.RelativeVeryAmple.tensorPowModuleCongr Y L
                (show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring)).hom ≫
              (tensorPowModuleAddIso Y L (k : ℤ) 1).inv) ≫
          (pullbackTensorModulesIso j (tensorPowModule Y L (k : ℤ))
            (tensorPowModule Y L 1)).hom ≫
            (Stacks.RelativeVeryAmple.tensorModulesMapIso Y' (pullbackPowIso j L k)
              ((Scheme.Modules.pullback j).mapIso (tensorPowModuleOneIso Y L) ≪≫
                (tensorPowModuleOneIso Y' ((Scheme.Modules.pullback j).obj L)).symm)).hom ≫
              (tensorPowModuleAddIso Y' ((Scheme.Modules.pullback j).obj L) (k : ℤ) 1).hom ≫
                (Stacks.RelativeVeryAmple.tensorPowModuleCongr Y'
                  ((Scheme.Modules.pullback j).obj L)
                  (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring)).hom := rfl

/-- The recursion defining the comparison of the powers, with the transports between the two
spellings of the degree `k + 1` removed: they are identities, their two ends being the same
object. The two cancellations are named as hypotheses and the second is applied as a term rather
than rewritten, the composite it sits in being read in the tensor-product-sheaf spelling of the
category rather than in `AlgebraicGeometry.Scheme.Modules`, so that a rewrite finds no
occurrence. -/
private theorem pullbackPowIso_hom_succ_aux (k : ℕ) :
    (pullbackPowIso j L (k + 1)).hom
      = (Scheme.Modules.pullback j).map (natTensorPowSuccIso Y L k).inv ≫
        (pullbackTensorModules j (natTensorPow L k) (tensorPowModule Y L 1)).hom ≫
          tensorModulesMap Y' (pullbackPowIso j L k).hom
              ((Scheme.Modules.pullback j).map (tensorPowModuleOneIso Y L).hom ≫
                (tensorPowModuleOneIso Y' ((Scheme.Modules.pullback j).obj L)).inv) ≫
            (natTensorPowSuccIso Y' ((Scheme.Modules.pullback j).obj L) k).hom := by
  have hhead : (Scheme.Modules.pullback j).map
          ((Stacks.RelativeVeryAmple.tensorPowModuleCongr Y L
              (show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring)).hom ≫
            (tensorPowModuleAddIso Y L (k : ℤ) 1).inv)
        = (Scheme.Modules.pullback j).map (natTensorPowSuccIso Y L k).inv :=
    congrArg (Scheme.Modules.pullback j).map (Category.id_comp _)
  have htail : (tensorPowModuleAddIso Y' ((Scheme.Modules.pullback j).obj L) (k : ℤ) 1).hom ≫
          (Stacks.RelativeVeryAmple.tensorPowModuleCongr Y' ((Scheme.Modules.pullback j).obj L)
            (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring)).hom
        = (natTensorPowSuccIso Y' ((Scheme.Modules.pullback j).obj L) k).hom :=
    Category.comp_id _
  refine (pullbackPowIso_hom_succ_literal j L k).trans ?_
  rw [hhead]
  exact congrArg (fun z => (Scheme.Modules.pullback j).map (natTensorPowSuccIso Y L k).inv ≫
      (pullbackTensorModules j (natTensorPow L k) (tensorPowModule Y L 1)).hom ≫
        tensorModulesMap Y' (pullbackPowIso j L k).hom
            ((Scheme.Modules.pullback j).map (tensorPowModuleOneIso Y L).hom ≫
              (tensorPowModuleOneIso Y' ((Scheme.Modules.pullback j).obj L)).inv) ≫ z) htail

/-- **The successor step of the comparison of the tensor powers is the cotensorator.** The
comparison in degree `k + 1` is the cotensorator at `(L ^⊗ k, L)` followed by the comparison in
degree `k` whiskered by `j^*L`.

The recursion defining the comparison splits the power as `L ^⊗ k ⊗ L ^⊗ 1` by the multiplication
of Stacks Tag 01CU; by `natTensorPowSuccIso_hom` that multiplication is the identification of
`L ^⊗ 1` with `L`, so naturality of the cotensorator in the second variable moves it to the front,
where it cancels against the copy appearing in the recursion. -/
theorem pullbackPowIso_succ (k : ℕ) :
    (pullbackPowIso j L (k + 1)).hom
      = pullbackCotensorator j (natTensorPow L k) L ≫
        ((pullbackPowIso j L k).hom ▷ (Scheme.Modules.pullback j).obj L) := by
  rw [pullbackPowIso_hom_succ_aux, natTensorPowSuccIso_inv, natTensorPowSuccIso_hom,
    Functor.map_comp_assoc,
    ← reassoc_of% (tensorIsoTensorModules_inv_naturality Y' (pullbackPowIso j L k).hom
      ((Scheme.Modules.pullback j).map (tensorPowModuleOneIso Y L).hom ≫
        (tensorPowModuleOneIso Y' ((Scheme.Modules.pullback j).obj L)).inv)),
    ← reassoc_of% (pullbackCotensorator_eq j (natTensorPow L k) (tensorPowModule Y L 1)),
    reassoc_of% (pullbackCotensorator_whiskerLeft j (natTensorPow L k)
      (tensorPowModuleOneIso Y L).inv),
    ← MonoidalCategory.id_tensorHom, ← MonoidalCategory.id_tensorHom,
    ← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id]

/-- **The successor step, for the comparison through which the pullback of a section is read.**
This is the hypothesis `hsucc` of
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullSection_mulSections_of_succ`. -/
theorem pullbackNatTensorPowIso_inv_succ (k : ℕ) :
    (pullbackNatTensorPowIso j L (k + 1)).inv
      = pullbackCotensorator j (natTensorPow L k) L ≫
        ((pullbackNatTensorPowIso j L k).inv ▷ (Scheme.Modules.pullback j).obj L) := by
  rw [← pullbackPowIso_hom, ← pullbackPowIso_hom, pullbackPowIso_succ]

/-! ### Multiplicativity of the pullback of sections, unconditionally -/

/-- **The identity of morphisms behind multiplicativity, in every degree and with no
hypothesis**: writing `σ` for a global section of `L ^⊗ n` read as a morphism out of the monoidal
unit and `c` for the comparison of the powers,

  `j^*(mulMap σ m) ≫ c (n + m) = c m ≫ mulMap σ' m`,

where `σ'` is the pullback of `σ` read the same way. This is
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.mulMap_comp_pullbackNatTensorPowIso_inv` with
its hypotheses discharged by the cotensorator. -/
theorem mulMap_comp_pullbackNatTensorPowIso_inv {n : ℕ} (s : Γ(natTensorPow L n, ⊤)) (m : ℕ) :
    (Scheme.Modules.pullback j).map (mulMap (secOf L s) m) ≫
        (pullbackNatTensorPowIso j L (n + m)).inv
      = (pullbackNatTensorPowIso j L m).inv ≫
        mulMap (secOf ((Scheme.Modules.pullback j).obj L) (pullSection j L n s)) m :=
  Stacks.AlgebraicGeometry.ProjChartSectionPullback.mulMap_comp_pullbackNatTensorPowIso_inv
    j L (fun A => pullbackCotensorator j A L)
    (fun h => pullbackCotensorator_whiskerRight j h L)
    (pullbackNatTensorPowIso_inv_succ j L) s m

/-- **Pulling back a product of global sections of tensor powers is the product of the
pullbacks**, in every pair of degrees and with no hypothesis. This is what makes the inverse image
of a datum of graded sections a datum of graded sections again, its multiplicativity clause being
exactly this. -/
theorem pullSection_mulSections {n m : ℕ} (s : Γ(natTensorPow L n, ⊤))
    (t : Γ(natTensorPow L m, ⊤)) :
    pullSection j L (n + m) (mulSections L s t)
      = mulSections ((Scheme.Modules.pullback j).obj L) (pullSection j L n s)
          (pullSection j L m t) :=
  Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullSection_mulSections_of_succ
    j L (fun A => pullbackCotensorator j A L)
    (fun h => pullbackCotensorator_whiskerRight j h L)
    (pullbackNatTensorPowIso_inv_succ j L) s t

end Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator

end
