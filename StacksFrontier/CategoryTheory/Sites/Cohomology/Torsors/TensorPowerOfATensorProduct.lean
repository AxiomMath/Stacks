module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorPowerOfASection

/-!
# Tensor powers of a tensor product of invertible modules

Let `(C, O)` be a ringed site and `L`, `M` invertible `O`-modules. The `k`-th tensor power of
`L ⊗ M` is the tensor product of the `k`-th tensor powers of `L` and of `M`. The comparison is
built by induction on `k` out of the successor comparison of Tag 01CU and the **middle-four
interchange** `(A ⊗ B) ⊗ (D ⊗ E) ≅ (A ⊗ D) ⊗ (B ⊗ E)` of the symmetric monoidal structure of
Tag 01CA; it carries the `k`-th tensor power of a tensor product of sections to the tensor
product of their `k`-th tensor powers, and it is natural in both modules, so that it descends to
isomorphism classes and in particular to the Picard group.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.tensorIsoOfModules` is the tensor product sheaf of two
  isomorphisms, with its source and target written as tensor product sheaves.
* `Stacks.Cohomology.Torsors.Generators.tensorInterchangeIso` is the middle-four interchange of
  the tensor product sheaf.
* `Stacks.Cohomology.Torsors.Generators.tpowTensorIso` is the comparison
  `(L ⊗ M)^{⊗ k} ≅ L^{⊗ k} ⊗ M^{⊗ k}`.

## Main results

* `Stacks.Cohomology.Torsors.Generators.tensorInterchangeIso_tensorSection`: the middle-four
  interchange exchanges the two middle factors of a tensor product of four sections.
* `Stacks.Cohomology.Torsors.Generators.tensorInterchangeIso_naturality`: the middle-four
  interchange is natural in all four arguments.
* `Stacks.Cohomology.Torsors.Generators.tpowTensorIso_powerSection`: **the comparison carries
  `(s ⊗ t)^{⊗ k}` to `s^{⊗ k} ⊗ t^{⊗ k}`.**
* `Stacks.Cohomology.Torsors.Generators.tpowTensorIso_naturality`: **the comparison is natural
  in both modules.**
* `Stacks.Cohomology.Torsors.Generators.associator_tensorSection`,
  `braiding_tensorSection`, `rightUnitor_tensorSection`, `tensorHom_tensorSection`,
  `whiskerLeft_tensorSection` and `whiskerRight_tensorSection` are the section calculus of
  Tag 01CV, restated for the monoidal structure on the modules of a ringed site; they are what
  the two displayed results reduce to.
* `Stacks.Cohomology.Torsors.Generators.tensorMu_naturality_step` is the inductive step of the
  naturality, isolated as an identity of an arbitrary braided monoidal category.

## Implementation notes

**One spelling for the objects.** The symmetric monoidal structure of Tag 01CA is installed as a
local instance on `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)`, which makes
`L ⊗ M` the tensor product sheaf `tensorSheafOfModules`, `α_` and `β_` the constraints
`Stacks.SheafOfModules.Invertible.tensorProductAssociator` and `tensorProductBraiding`, and
`CategoryTheory.MonoidalCategory.tensorμ` the middle-four interchange — all by `rfl`, as the four
`*_eq` lemmas record. What is *not* interchangeable is the index of the category:
`Stacks.SheafOfModules.Invertible.tensorProductIso` produces an isomorphism of sheaves of modules
over `TensorSheafification.structureSheaf X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2`,
and a composite mixing that index with `Stacks.SheafOfModules.Tensor.ringSheaf X.O` is type-correct
only at default transparency, so `rw` and `simp` silently refuse to fire on
`CategoryTheory.Iso.trans_hom` or on any lemma about `CategoryTheory.Iso.hom` inside it.
`tensorIsoOfModules` is the same isomorphism at the `Stacks.SheafOfModules.Tensor.ringSheaf X.O`
index — `tensorIsoOfModules_eq` is the `rfl` — and every statement and composite below is written
with it. The public statements are too: `powerMap` takes its invertibility as an instance argument,
and the only `IsInvertible` instance on a tensor product is `isInvertible_tensorSheafOfModules`,
which is indexed on `tensorSheafOfModules`. A statement spelling the same object through
`tensorProductIso` presents it to instance search with `Stacks.SheafOfModules.Tensor.sheafTensor`
at the head instead, which no instance matches, so `powerMap` applied to a `tensorProductIso` does
not elaborate at all. `tensorIsoOfModules_eq` recovers the `tensorProductIso` spelling for any
consumer that wants it.

The middle-four interchange is not assembled by hand: with the monoidal structure in scope it is
`CategoryTheory.MonoidalCategory.tensorμ`, whose inverse is `tensorδ` and whose naturality in
all four arguments is `CategoryTheory.MonoidalCategory.tensorμ_natural`. Only its value on
sections has to be computed, and that is done by unfolding it into the two associators, the
braiding and the three whiskerings it is defined from.

`tensorMu_naturality_step` is stated in an abstract braided monoidal category for the same
transparency reason: there the objects carry no projections of a ringed site, so `rw` on the
monoidal lemmas works, and the step is applied to the sheaf case by `exact`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules.Invertible (tensorProductIso tensorProductAssociator
  tensorProductBraiding tensorProductRightUnitor)
open Stacks.SheafOfModules (IsInvertible)

universe u v w

namespace Stacks.Cohomology.Torsors.Generators

variable (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]

/-- The tensor product sheaf of Tag 01CA as a monoidal structure on the modules of a ringed
site. -/
noncomputable local instance ringedSiteModulesMonoidal :
    MonoidalCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2

/-- The symmetry constraint of Tag 01CA as a symmetric structure on the modules of a ringed
site. -/
noncomputable local instance ringedSiteModulesSymmetric :
    SymmetricCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.sheafTensorSymmetric X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2

/-- The tensor product of two invertible modules is invertible. This is
`Stacks.SheafOfModules.isInvertible_tensorSheaf` as an instance, so that a tensor power of a
tensor product can be written down without supplying it by hand. -/
instance isInvertible_tensorSheafOfModules
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] :
    IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (tensorSheafOfModules X L M) :=
  Stacks.SheafOfModules.isInvertible_tensorSheaf X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L M

/-- The monoidal tensor product of the modules of a ringed site is the tensor product sheaf. -/
theorem tensorObj_eq (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    L ⊗ M = tensorSheafOfModules X L M := rfl

/-- The monoidal associator of the modules of a ringed site is the associativity constraint of
the tensor product sheaf. -/
theorem associator_eq (L M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    α_ L M N =
      tensorProductAssociator X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L M N := rfl

/-- The monoidal braiding of the modules of a ringed site is the symmetry constraint of the
tensor product sheaf. -/
theorem braiding_eq (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    β_ L M = tensorProductBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L M := rfl

/-- The monoidal right unitor of the modules of a ringed site is the right unit constraint of
the tensor product sheaf. -/
theorem rightUnitor_eq (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ρ_ L = tensorProductRightUnitor X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L := rfl

/-- The tensor product sheaf of two isomorphisms of modules of a ringed site, with its source
and target written as tensor product sheaves. It is
`Stacks.SheafOfModules.Invertible.tensorProductIso` (`tensorIsoOfModules_eq`); writing it this
way keeps every object in one spelling, without which `rw` and `simp` meet a composite whose
intermediate objects live in two definitionally equal but syntactically different categories. -/
noncomputable def tensorIsoOfModules
    {L L' M M' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (e : L ≅ L') (f : M ≅ M') :
    tensorSheafOfModules X L M ≅ tensorSheafOfModules X L' M' where
  hom := e.hom ⊗ₘ f.hom
  inv := e.inv ⊗ₘ f.inv
  hom_inv_id :=
    have h : (e.hom ⊗ₘ f.hom) ≫ (e.inv ⊗ₘ f.inv) = 𝟙 (L ⊗ M) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, e.hom_inv_id, f.hom_inv_id,
        MonoidalCategory.id_tensorHom_id]
    h
  inv_hom_id :=
    have h : (e.inv ⊗ₘ f.inv) ≫ (e.hom ⊗ₘ f.hom) = 𝟙 (L' ⊗ M') := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, e.inv_hom_id, f.inv_hom_id,
        MonoidalCategory.id_tensorHom_id]
    h

/-- The tensor product sheaf of two isomorphisms is their monoidal tensor product. -/
theorem tensorIsoOfModules_hom
    {L L' M M' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (e : L ≅ L') (f : M ≅ M') :
    (tensorIsoOfModules X e f).hom = e.hom ⊗ₘ f.hom := rfl

/-- The tensor product sheaf of two isomorphisms is the one of Tag 01CA. -/
theorem tensorIsoOfModules_eq
    {L L' M M' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (e : L ≅ L') (f : M ≅ M') :
    tensorIsoOfModules X e f =
      tensorProductIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 e f := rfl

/-- The tensor product of two sections is the one of the section calculus of Tag 01CV. -/
theorem tensorSection_eq (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C)
    (s : L.val.obj (op U)) (t : M.val.obj (op U)) :
    tensorSection X L M U s t =
      Stacks.SheafOfModules.tensorSectionsAt X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (op U) L M s t := rfl

/-- The tensor product of two morphisms carries a tensor product of sections to the tensor
product of their images. -/
theorem tensorHom_tensorSection
    {A A' B B' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : A ⟶ A') (g : B ⟶ B') (U : X.C) (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    ((f ⊗ₘ g).val.app (op U)).hom (tensorSection X A B U a b) =
      tensorSection X A' B' U ((f.val.app (op U)).hom a) ((g.val.app (op U)).hom b) :=
  Stacks.SheafOfModules.tensorSections_tensorMapAt X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (op U) A A' B B' f g a b

/-- Left whiskering carries a tensor product of sections to the tensor product of the first
section with the image of the second. -/
theorem whiskerLeft_tensorSection
    (A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B B' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : B ⟶ B') (U : X.C)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    ((A ◁ g).val.app (op U)).hom (tensorSection X A B U a b) =
      tensorSection X A B' U a ((g.val.app (op U)).hom b) :=
  Stacks.SheafOfModules.tensorSections_tensorMapAt X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (op U) A A B B'
    (𝟙 A) g a b

/-- Right whiskering carries a tensor product of sections to the tensor product of the image of
the first section with the second. -/
theorem whiskerRight_tensorSection
    {A A' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ A')
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    ((f ▷ B).val.app (op U)).hom (tensorSection X A B U a b) =
      tensorSection X A' B U ((f.val.app (op U)).hom a) b :=
  Stacks.SheafOfModules.tensorSections_tensorMapAt X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (op U) A A' B B
    f (𝟙 B) a b

/-- The associator reassociates a tensor product of three sections. -/
theorem associator_tensorSection
    (A B D : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) (d : D.val.obj (op U)) :
    ((α_ A B D).hom.val.app (op U)).hom
        (tensorSection X (A ⊗ B) D U (tensorSection X A B U a b) d) =
      tensorSection X A (B ⊗ D) U a (tensorSection X B D U b d) :=
  Stacks.SheafOfModules.tensorSections_associatorAt X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (op U) A B D a b d

/-- The braiding exchanges the two factors of a tensor product of sections. -/
theorem braiding_tensorSection
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    ((β_ A B).hom.val.app (op U)).hom (tensorSection X A B U a b) =
      tensorSection X B A U b a :=
  Stacks.SheafOfModules.tensorSections_braidingAt X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (op U) A B a b

/-- The right unitor cancels the unit section of the structure sheaf. -/
theorem rightUnitor_tensorSection
    (A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (a : A.val.obj (op U)) :
    ((ρ_ A).hom.val.app (op U)).hom
        (tensorSection X A (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U a
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) = a :=
  Stacks.SheafOfModules.tensorSections_rightUnitorAt X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (op U) A a

omit [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat] in
/-- The inverse of an isomorphism of sheaves of modules, read on a section whose image under
the isomorphism is known. -/
theorem inv_app_apply_of_hom_app_apply
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (i : A ≅ B)
    (V : X.Cᵒᵖ) (x : A.val.obj V) (y : B.val.obj V)
    (h : (i.hom.val.app V).hom x = y) : (i.inv.val.app V).hom y = x :=
  (congrArg (i.inv.val.app V).hom h).symm.trans (sheafIso_inv_app_hom_app X i V x)


/-- **The middle-four interchange** `(A ⊗ B) ⊗ (D ⊗ E) ≅ (A ⊗ D) ⊗ (B ⊗ E)` for the tensor
product sheaf: `CategoryTheory.MonoidalCategory.tensorμ` for the monoidal structure of Tag
01CA. -/
noncomputable def tensorInterchangeIso
    (A B D E : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    tensorSheafOfModules X (tensorSheafOfModules X A B) (tensorSheafOfModules X D E) ≅
      tensorSheafOfModules X (tensorSheafOfModules X A D) (tensorSheafOfModules X B E) where
  hom := tensorμ A B D E
  inv := tensorδ A B D E
  hom_inv_id := tensorμ_tensorδ A B D E
  inv_hom_id := tensorδ_tensorμ A B D E

/-- The middle-four interchange is the four-fold tensor comparison of the braiding. -/
theorem tensorInterchangeIso_hom
    (A B D E : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (tensorInterchangeIso X A B D E).hom = tensorμ A B D E := rfl

/-- The middle-four interchange exchanges the two middle factors of a tensor product of four
sections. -/
theorem tensorInterchangeIso_tensorSection
    (A B D E : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) (d : D.val.obj (op U))
    (c : E.val.obj (op U)) :
    ((tensorInterchangeIso X A B D E).hom.val.app (op U)).hom
        (tensorSection X (tensorSheafOfModules X A B) (tensorSheafOfModules X D E) U
          (tensorSection X A B U a b) (tensorSection X D E U d c)) =
      tensorSection X (tensorSheafOfModules X A D) (tensorSheafOfModules X B E) U
        (tensorSection X A D U a d) (tensorSection X B E U b c) := by
  change ((tensorInterchangeIso X A B D E).hom.val.app (op U)).hom
      (tensorSection X (A ⊗ B) (D ⊗ E) U
        (tensorSection X A B U a b) (tensorSection X D E U d c)) =
    tensorSection X (A ⊗ D) (B ⊗ E) U
      (tensorSection X A D U a d) (tensorSection X B E U b c)
  have hBDE : ((α_ B D E).inv.val.app (op U)).hom
        (tensorSection X B (D ⊗ E) U b (tensorSection X D E U d c)) =
      tensorSection X (B ⊗ D) E U (tensorSection X B D U b d) c :=
    inv_app_apply_of_hom_app_apply X (α_ B D E) (op U) _ _
      (associator_tensorSection X B D E U b d c)
  have hADBE : ((α_ A D (B ⊗ E)).inv.val.app (op U)).hom
        (tensorSection X A (D ⊗ (B ⊗ E)) U a
          (tensorSection X D (B ⊗ E) U d (tensorSection X B E U b c))) =
      tensorSection X (A ⊗ D) (B ⊗ E) U
        (tensorSection X A D U a d) (tensorSection X B E U b c) :=
    inv_app_apply_of_hom_app_apply X (α_ A D (B ⊗ E)) (op U) _ _
      (associator_tensorSection X A D (B ⊗ E) U a d (tensorSection X B E U b c))
  have h0 : ((tensorInterchangeIso X A B D E).hom.val.app (op U)).hom
        (tensorSection X (A ⊗ B) (D ⊗ E) U
          (tensorSection X A B U a b) (tensorSection X D E U d c)) =
      ((α_ A D (B ⊗ E)).inv.val.app (op U)).hom
        (((A ◁ (α_ D B E).hom).val.app (op U)).hom
          (((A ◁ ((β_ B D).hom ▷ E)).val.app (op U)).hom
            (((A ◁ (α_ B D E).inv).val.app (op U)).hom
              (((α_ A B (D ⊗ E)).hom.val.app (op U)).hom
                (tensorSection X (A ⊗ B) (D ⊗ E) U (tensorSection X A B U a b)
                  (tensorSection X D E U d c)))))) := rfl
  refine h0.trans ?_
  rw [associator_tensorSection, whiskerLeft_tensorSection, hBDE, whiskerLeft_tensorSection,
    whiskerRight_tensorSection, braiding_tensorSection, whiskerLeft_tensorSection,
    associator_tensorSection, hADBE]

/-- The middle-four interchange is natural in all four arguments. -/
theorem tensorInterchangeIso_naturality
    {A A' B B' D D' E E' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D') (eE : E ≅ E') :
    (tensorIsoOfModules X (tensorIsoOfModules X eA eB) (tensorIsoOfModules X eD eE)).hom ≫
        (tensorInterchangeIso X A' B' D' E').hom =
      (tensorInterchangeIso X A B D E).hom ≫
        (tensorIsoOfModules X (tensorIsoOfModules X eA eD) (tensorIsoOfModules X eB eE)).hom :=
  tensorμ_natural eA.hom eB.hom eD.hom eE.hom

/-- The tensor power of an isomorphism at a successor exponent, with the tensor product of
isomorphisms written through `tensorIsoOfModules`. -/
theorem powerMap_succ_tensorIsoOfModules
    {L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (e : L ≅ M)
    (k : ℕ) :
    powerMap X e (k + 1) =
      ((tpowSuccIso X L k).symm ≪≫ tensorIsoOfModules X (powerMap X e k) e) ≪≫
        tpowSuccIso X M k := rfl


/-- **The `k`-th tensor power of a tensor product is the tensor product of the `k`-th tensor
powers**: `(L ⊗ M)^{⊗ k} ≅ L^{⊗ k} ⊗ M^{⊗ k}`. -/
noncomputable def tpowTensorIso
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] :
    (k : ℕ) → tpow X (tensorSheafOfModules X L M) k ≅
        tensorSheafOfModules X (tpow X L k) (tpow X M k)
  | 0 => (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm
  | k + 1 =>
      (((tpowSuccIso X (tensorSheafOfModules X L M) k).symm ≪≫
            tensorIsoOfModules X (tpowTensorIso L M k)
              (Iso.refl (tensorSheafOfModules X L M))) ≪≫
          tensorInterchangeIso X (tpow X L k) (tpow X M k) L M) ≪≫
        tensorIsoOfModules X (tpowSuccIso X L k) (tpowSuccIso X M k)

/-- The comparison at a successor exponent. -/
theorem tpowTensorIso_succ (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (k : ℕ) :
    tpowTensorIso X L M (k + 1) =
      (((tpowSuccIso X (tensorSheafOfModules X L M) k).symm ≪≫
            tensorIsoOfModules X (tpowTensorIso X L M k)
              (Iso.refl (tensorSheafOfModules X L M))) ≪≫
          tensorInterchangeIso X (tpow X L k) (tpow X M k) L M) ≪≫
        tensorIsoOfModules X (tpowSuccIso X L k) (tpowSuccIso X M k) := rfl

/-- The comparison carries the `k`-th tensor power of a tensor product of sections to the tensor
product of their `k`-th tensor powers. -/
theorem tpowTensorIso_powerSection
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (U : X.C)
    (s : L.val.obj (op U)) (t : M.val.obj (op U)) :
    (k : ℕ) →
      ((tpowTensorIso X L M k).hom.val.app (op U)).hom
          (powerSection X (tensorSheafOfModules X L M) U (tensorSection X L M U s t) k) =
        tensorSection X (tpow X L k) (tpow X M k) U
          (powerSection X L U s k) (powerSection X M U t k)
  | 0 =>
      inv_app_apply_of_hom_app_apply X
        (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (op U) _ _
        (rightUnitor_tensorSection X
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
  | k + 1 => by
      have h0 : ((tpowTensorIso X L M (k + 1)).hom.val.app (op U)).hom
            (powerSection X (tensorSheafOfModules X L M) U
              (tensorSection X L M U s t) (k + 1)) =
          ((((tpowSuccIso X L k).hom ⊗ₘ (tpowSuccIso X M k).hom).val.app (op U)).hom
            (((tensorInterchangeIso X (tpow X L k) (tpow X M k) L M).hom.val.app (op U)).hom
              ((((tpowTensorIso X L M k).hom ▷
                    tensorSheafOfModules X L M).val.app (op U)).hom
                (((tpowSuccIso X (tensorSheafOfModules X L M) k).inv.val.app (op U)).hom
                  (powerSection X (tensorSheafOfModules X L M) U
                    (tensorSection X L M U s t) (k + 1)))))) := rfl
      refine h0.trans ?_
      rw [powerSection_succ, sheafIso_inv_app_hom_app, whiskerRight_tensorSection,
        tpowTensorIso_powerSection L M U s t k, tensorInterchangeIso_tensorSection,
        tensorHom_tensorSection, powerSection_succ, powerSection_succ]

/-- **The inductive step of the naturality of the tensor-power comparison**, isolated as an
identity of a braided monoidal category. Both sides are read after the leading inverse
successor comparison has been cancelled; the hypothesis `ih` is the naturality at the previous
exponent. -/
theorem tensorMu_naturality_step {D : Type*} [Category D] [MonoidalCategory D]
    [BraidedCategory D] {V V' P Q P' Q' R S R' S' Z Z' W W' : D}
    (pg : V ⟶ V') (T : V ⟶ P ⊗ Q) (T' : V' ⟶ P' ⊗ Q')
    (pe : P ⟶ P') (pf : Q ⟶ Q') (er : R ⟶ R') (es : S ⟶ S')
    (pL : P ⊗ R ≅ Z) (pM : Q ⊗ S ≅ Z') (pL' : P' ⊗ R' ⟶ W) (pM' : Q' ⊗ S' ⟶ W')
    (ih : pg ≫ T' = T ≫ (pe ⊗ₘ pf)) :
    (pg ⊗ₘ (er ⊗ₘ es)) ≫ (T' ⊗ₘ 𝟙 (R' ⊗ S')) ≫ tensorμ P' Q' R' S' ≫ (pL' ⊗ₘ pM') =
      (T ⊗ₘ 𝟙 (R ⊗ S)) ≫ tensorμ P Q R S ≫ (pL.hom ⊗ₘ pM.hom) ≫
        ((pL.inv ≫ (pe ⊗ₘ er) ≫ pL') ⊗ₘ (pM.inv ≫ (pf ⊗ₘ es) ≫ pM')) := by
  have h1 : (pg ⊗ₘ (er ⊗ₘ es)) ≫ (T' ⊗ₘ 𝟙 (R' ⊗ S')) =
      (T ⊗ₘ 𝟙 (R ⊗ S)) ≫ ((pe ⊗ₘ pf) ⊗ₘ (er ⊗ₘ es)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, ih]
  have h3 : (pL.hom ⊗ₘ pM.hom) ≫
        ((pL.inv ≫ (pe ⊗ₘ er) ≫ pL') ⊗ₘ (pM.inv ≫ (pf ⊗ₘ es) ≫ pM')) =
      ((pe ⊗ₘ er) ⊗ₘ (pf ⊗ₘ es)) ≫ (pL' ⊗ₘ pM') := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
  rw [← Category.assoc, h1, h3]
  simp only [Category.assoc, MonoidalCategory.tensorμ_natural_assoc]

/-- **The comparison is natural in both arguments.** -/
theorem tpowTensorIso_naturality
    {L L' M M' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L']
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M']
    (e : L ≅ L') (f : M ≅ M') (k : ℕ) :
    (powerMap X (tensorIsoOfModules X e f) k).hom ≫
        (tpowTensorIso X L' M' k).hom =
      (tpowTensorIso X L M k).hom ≫
        ((powerMap X e k).hom ⊗ₘ (powerMap X f k).hom) := by
  induction k with
  | zero =>
      refine Eq.trans (Category.id_comp (tpowTensorIso X L' M' 0).hom) ?_
      refine Eq.trans (Category.comp_id (tpowTensorIso X L M 0).hom).symm ?_
      exact congrArg (fun z => (tpowTensorIso X L M 0).hom ≫ z)
        (MonoidalCategory.id_tensorHom_id (tpow X L 0) (tpow X M 0)).symm
  | succ k ih =>
      change (powerMap X (tensorIsoOfModules X e f) (k + 1)).hom ≫
          (tpowTensorIso X L' M' (k + 1)).hom =
        (tpowTensorIso X L M (k + 1)).hom ≫
          (tensorIsoOfModules X (powerMap X e (k + 1)) (powerMap X f (k + 1))).hom
      simp only [powerMap_succ_tensorIsoOfModules, tpowTensorIso_succ, Iso.trans_hom, Iso.symm_hom,
        Iso.refl_hom, tensorIsoOfModules_hom, tensorInterchangeIso_hom, Category.assoc,
        Iso.hom_inv_id_assoc]
      exact congrArg (fun z => (tpowSuccIso X (tensorSheafOfModules X L M) k).inv ≫ z)
        (tensorMu_naturality_step (powerMap X (tensorIsoOfModules X e f) k).hom
          (tpowTensorIso X L M k).hom (tpowTensorIso X L' M' k).hom
          (powerMap X e k).hom (powerMap X f k).hom e.hom f.hom
          (tpowSuccIso X L k) (tpowSuccIso X M k)
          (tpowSuccIso X L' k).hom (tpowSuccIso X M' k).hom ih)

end Stacks.Cohomology.Torsors.Generators

end
