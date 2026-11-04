module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensor
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkSheafExact

/-!
# Stalks of tensor products of sheaves of modules, with independent site universes

Let `(C, J)` be a site with `C : Type u`, `[Category.{v} C]` and `C` locally `w`-small, `Φ` a
point of it and `O` a sheaf of commutative rings with values in `Type w`. The stalk at `Φ` of a
presheaf of modules is the stalk of its sheafification ([Stacks, Tag 04EQ] (3)), and the stalk
of `A ⊗_O B` is `A_Φ ⊗_{O_Φ} B_Φ` ([Stacks, Tag 03EL]). Here the three universes `u`, `v`, `w`
of the site are independent.

## Main definitions

* `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.fiberSheafifyNatIso`
* `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.tensorSheafifyIso`
* `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso`
* `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorNatIso`

## Implementation notes

Two spellings of the presheaf of rings of the site are in play: presheaves of modules are indexed
by `(Stacks.SheafOfModules.Tensor.ringSheaf O).obj` for sheafification, and by
`O.obj ⋙ forget₂ CommRingCat RingCat` for `Stacks.presheafModuleFiberOfCommRing`. The two are
equal by `rfl` but not reducibly, and comparing morphisms across them makes the unifier unfold
the module structures of a filtered colimit, which is slow. So the identification is made once,
in `fiberSheafifyNatIsoP`, before restriction of scalars; every equation between morphisms is
written `@Eq T lhs rhs` with its type pinned; and the intermediate steps of a proof are `have`s
with no expected type, elaborated in one spelling. `tensorObjP` exists because `M ⊗ N` placed
as an argument of the sheafification functor finds no monoidal instance at the expected type.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL),
  [Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u v w

namespace Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall

/-! ### The stalk of the sheafification of a presheaf of modules -/

section Ring

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (R : Sheaf J RingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Stacks 04EQ part (3) read as an isomorphism of functors.** The stalk at a point of the
site of a presheaf of `R`-modules is the stalk of its sheafification, naturally in the presheaf.
The `IsIso` is passed explicitly: left to instance search, `asIso` exceeds the heartbeat budget
on this term. -/
noncomputable def fiberSheafifyNatIso :
    Stacks.presheafModuleFiber Φ R.obj ≅
      PresheafOfModules.sheafification (R := R) (𝟙 R.obj) ⋙ Stacks.sheafModuleFiber Φ R :=
  @asIso _ _ _ _ (Stacks.moduleFiberSheafificationComparison Φ R)
    (Stacks.isIso_moduleFiberSheafificationComparison Φ R)

end Ring

section CommRing

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- `fiberSheafifyNatIso` for the ring sheaf of `O`, stated over the presheaf of rings
`O.obj ⋙ forget₂ CommRingCat RingCat`: the stalk at `Φ` of a presheaf of `O`-modules is the stalk
of its sheafification, naturally in the presheaf. -/
noncomputable def fiberSheafifyNatIsoP :
    Stacks.presheafModuleFiber Φ (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ≅
      PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) ⋙ Stacks.sheafModuleFiber Φ
        (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  fiberSheafifyNatIso Φ (Stacks.SheafOfModules.Tensor.ringSheaf O)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Naturality of `fiberSheafifyNatIsoP`, with the target of the right-hand composite written
through `SheafOfModules.Hom.val` rather than as a composite functor. -/
lemma fiberSheafifyNatIsoP_naturality
    {P Q : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})} (g : P ⟶ Q) :
    @Eq ((Stacks.presheafModuleFiber Φ (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})).obj P ⟶
          (Stacks.presheafModuleFiber Φ (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})).obj
            ((PresheafOfModules.sheafification
                (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
                (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj Q).val)
      ((Stacks.presheafModuleFiber Φ (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})).map g ≫
        (fiberSheafifyNatIsoP Φ O).hom.app Q)
      ((fiberSheafifyNatIsoP Φ O).hom.app P ≫
        (Stacks.presheafModuleFiber Φ (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})).map
          ((PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map g).val) :=
  (fiberSheafifyNatIsoP Φ O).hom.naturality g

/-- The stalk at `Φ` of a presheaf of `O`-modules, as a module over the stalk `O_Φ`, is the stalk
of its sheafification. -/
noncomputable def sheafifyStalkIso
    (M : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    (Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj M ≅
      (Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
        ((PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj M).val :=
  (ModuleCat.restrictScalars.{w} (Stacks.toRingFiber Φ O.obj)).mapIso
    ((fiberSheafifyNatIsoP Φ O).app M)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `sheafifyStalkIso` is natural in the presheaf of modules. -/
lemma sheafifyStalkIso_naturality
    {P Q : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})} (g : P ⟶ Q) :
    @Eq ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj P ⟶
          (Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
            ((PresheafOfModules.sheafification
                (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
                (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj Q).val)
      ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).map g ≫ (sheafifyStalkIso Φ O Q).hom)
      ((sheafifyStalkIso Φ O P).hom ≫ (Stacks.presheafModuleFiberOfCommRing Φ O.obj).map
        ((PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map g).val) := by
  have hc := (ModuleCat.restrictScalars.{w} (Stacks.toRingFiber Φ O.obj)).map_comp
    ((Stacks.presheafModuleFiber Φ (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})).map g)
    ((fiberSheafifyNatIsoP Φ O).hom.app Q)
  have hd := (ModuleCat.restrictScalars.{w} (Stacks.toRingFiber Φ O.obj)).map_comp
    ((fiberSheafifyNatIsoP Φ O).hom.app P)
    ((Stacks.presheafModuleFiber Φ (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})).map
      ((PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map g).val)
  have h := congrArg (ModuleCat.restrictScalars.{w} (Stacks.toRingFiber Φ O.obj)).map
    (fiberSheafifyNatIsoP_naturality Φ O g)
  have hfinal := hc.symm.trans (h.trans hd)
  exact hfinal

/-! ### The stalk of a tensor product of sheaves of modules -/

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The objectwise tensor product of two presheaves of `O`-modules, with its type written over
`O.obj ⋙ forget₂ CommRingCat RingCat`. -/
noncomputable abbrev tensorObjP
    (M N : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
  M ⊗ N

/-- The stalk at `Φ` of the sheafification of the objectwise tensor product of two presheaves of
`O`-modules is the tensor product of the stalks over the stalk ring `O_Φ`. -/
noncomputable def tensorSheafifyIso
    (M N : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    (Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
        ((PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (tensorObjP O M N)).val ≅
      ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).obj
          ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj M)).obj
        ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj N) :=
  (sheafifyStalkIso Φ O (tensorObjP O M N)).symm ≪≫ Stacks.moduleFiberTensorIso Φ O.obj M N

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The forward map of `tensorSheafifyIso` is the inverse of `sheafifyStalkIso` followed by the
forward map of `Stacks.moduleFiberTensorIso`. -/
lemma tensorSheafifyIso_hom
    (M N : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    @Eq ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
            ((PresheafOfModules.sheafification
                (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
                (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (tensorObjP O M N)).val ⟶
          ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).obj
              ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj M)).obj
            ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj N))
      (tensorSheafifyIso Φ O M N).hom
      ((sheafifyStalkIso Φ O (tensorObjP O M N)).inv ≫
        (Stacks.moduleFiberTensorIso Φ O.obj M N).hom) := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.tensorSheafifyIso` is natural in
the left-hand variable. -/
lemma tensorSheafifyIso_naturality_left
    {M M' : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})} (φ : M ⟶ M')
    (N : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    @Eq ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
            ((PresheafOfModules.sheafification
                (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
                (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (tensorObjP O M N)).val ⟶
          ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).obj
              ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj M')).obj
            ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj N))
      ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).map
          ((PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
            (((curriedTensor (PresheafOfModules.{w}
              (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).map φ).app N)).val ≫
        (tensorSheafifyIso Φ O M' N).hom)
      ((tensorSheafifyIso Φ O M N).hom ≫
        ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).map
          ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).map φ)).app
            ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj N)) := by
  have h1 := sheafifyStalkIso_naturality Φ O (P := tensorObjP O M N) (Q := tensorObjP O M' N)
    (((curriedTensor (PresheafOfModules.{w}
      (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).map φ).app N)
  have h2 := Stacks.moduleFiberTensorIso_naturality_left Φ O.obj M N φ
  have h3 : @Eq ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
          ((PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (tensorObjP O M N)).val ⟶
        (Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
          ((PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (tensorObjP O M' N)).val)
      ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).map
        ((PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
          (((curriedTensor (PresheafOfModules.{w}
            (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).map φ).app N)).val)
      ((sheafifyStalkIso Φ O (tensorObjP O M N)).inv ≫
        (Stacks.presheafModuleFiberOfCommRing Φ O.obj).map
          (((curriedTensor (PresheafOfModules.{w}
            (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).map φ).app N) ≫
          (sheafifyStalkIso Φ O (tensorObjP O M' N)).hom) := by
    rw [h1, Iso.inv_hom_id_assoc]
  rw [tensorSheafifyIso_hom, tensorSheafifyIso_hom, h3]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [h2]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.tensorSheafifyIso` is natural in
the right-hand variable. -/
lemma tensorSheafifyIso_naturality_right
    (M : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    {N N' : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})} (ψ : N ⟶ N') :
    @Eq ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
            ((PresheafOfModules.sheafification
                (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
                (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (tensorObjP O M N)).val ⟶
          ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).obj
              ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj M)).obj
            ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj N'))
      ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).map
          ((PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
            (((curriedTensor (PresheafOfModules.{w}
              (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).obj M).map ψ)).val ≫
        (tensorSheafifyIso Φ O M N').hom)
      ((tensorSheafifyIso Φ O M N).hom ≫
        ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).obj
          ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj M)).map
            ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).map ψ)) := by
  have h1 := sheafifyStalkIso_naturality Φ O (P := tensorObjP O M N) (Q := tensorObjP O M N')
    (((curriedTensor (PresheafOfModules.{w}
      (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).obj M).map ψ)
  have h2 := Stacks.moduleFiberTensorIso_naturality_right Φ O.obj M N ψ
  have h3 : @Eq ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
          ((PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (tensorObjP O M N)).val ⟶
        (Stacks.presheafModuleFiberOfCommRing Φ O.obj).obj
          ((PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj (tensorObjP O M N')).val)
      ((Stacks.presheafModuleFiberOfCommRing Φ O.obj).map
        ((PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
          (((curriedTensor (PresheafOfModules.{w}
            (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).obj M).map ψ)).val)
      ((sheafifyStalkIso Φ O (tensorObjP O M N)).inv ≫
        (Stacks.presheafModuleFiberOfCommRing Φ O.obj).map
          (((curriedTensor (PresheafOfModules.{w}
            (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).obj M).map ψ) ≫
          (sheafifyStalkIso Φ O (tensorObjP O M N')).hom) := by
    rw [h1, Iso.inv_hom_id_assoc]
  rw [tensorSheafifyIso_hom, tensorSheafifyIso_hom, h3]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [h2]

/-- The stalk at `Φ` of the tensor product `A ⊗_O B` of sheaves of `O`-modules is
`A_Φ ⊗_{O_Φ} B_Φ`. -/
noncomputable def stalkSheafTensorIso
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (Stacks.sheafModuleFiberOfCommRing Φ O).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj A).obj B) ≅
      ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).obj
          ((Stacks.sheafModuleFiberOfCommRing Φ O).obj A)).obj
        ((Stacks.sheafModuleFiberOfCommRing Φ O).obj B) :=
  tensorSheafifyIso Φ O A.val B.val

/-- `stalkSheafTensorIso` is natural in the right-hand variable. -/
lemma stalkSheafTensorIso_naturality_right
    (A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {B B' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (g : B ⟶ B') :
    (Stacks.sheafModuleFiberOfCommRing Φ O).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj A).map g) ≫
        (stalkSheafTensorIso Φ O A B').hom =
      (stalkSheafTensorIso Φ O A B).hom ≫
        ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).obj
          ((Stacks.sheafModuleFiberOfCommRing Φ O).obj A)).map
            ((Stacks.sheafModuleFiberOfCommRing Φ O).map g) :=
  tensorSheafifyIso_naturality_right Φ O A.val (ψ := g.val)

/-- The stalk at `Φ` of `A ⊗_O -` is `A_Φ ⊗_{O_Φ} -` of the stalk, as functors. -/
noncomputable def stalkSheafTensorNatIso
    (A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor O).obj A ⋙ Stacks.sheafModuleFiberOfCommRing Φ O ≅
      Stacks.sheafModuleFiberOfCommRing Φ O ⋙
        (curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).obj
          ((Stacks.sheafModuleFiberOfCommRing Φ O).obj A) :=
  NatIso.ofComponents (stalkSheafTensorIso Φ O A)
    (fun g => stalkSheafTensorIso_naturality_right Φ O A g)

end CommRing

end Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall

end
