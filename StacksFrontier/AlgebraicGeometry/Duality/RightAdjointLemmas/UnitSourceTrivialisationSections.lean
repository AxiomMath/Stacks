module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportUnitSourceLeftAdjoint
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualAtTheStructureSheaf

/-!
# The trivialisation of `ℰom_𝒪(𝒪, -)` on sections is evaluation at the unit section

On a ringed site `(C, J, 𝒪)` the clause of [Stacks, Tag 03EM] which says that a local
homomorphism `𝒪|_U ⟶ G|_U` is its value at the unit section is available in two unrelated
spellings:

* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso`, the isomorphism of
  functors `ℰom_𝒪(𝒪, -) ≅ 𝟭` got from the monoidal-closed structure — `ihom` at the monoidal
  unit is the identity functor — and therefore stated with no reference to sections at all;
* `Stacks.SheafOfModules.internalHomSheafUnitIso`, the isomorphism `ℰom_{𝒪_X}(𝒪_X, G) ≅ G` on a
  topological space, got from the characterising structure of [Stacks, Tag 01CO]: both sides are
  internal Hom sheaves of the same pair, and the comparison acts on sections over `U` by
  evaluation at the unit section (`Stacks.SheafOfModules.internalHomSheafUnitIso_hom_val_app`).

**This file computes the first one on sections and identifies the two.** That identification is
the single remaining input of [Stacks, Tag 0B4B]: the underived core of that tag,
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_comp_unitIso_comp_counit`, is
an identity of natural transformations in which the two trivialisations of `ℰom(𝒪, -)` occur in
the monoidal-closed spelling, whereas the identity of sections it has to produce —
`…ClosedQuotientMorphismOfRingedSpaces.SheafHomPushforwardSectionsCore` — is stated with
evaluation at the unit section.

## The shape of the computation

`internalHomSecondFunctorUnitIso` is the conjugate of the inverse left unitor
(`…conjugateEquiv_symm_internalHomSecondFunctorUnitIso_app`), so its component at `A` is the
inverse left unitor at `ℰom_𝒪(𝒪, A)` followed by the counit of the tensor--internal-Hom
adjunction of [Stacks, Tag 03EO] in the *left*-handed spelling `𝒪 ⊗_𝒪 -` (step `L2` below).
Both factors then have to be read on sections, and the obstacle is handedness: what the tree
pins on sections is `Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply`, the
hom-equivalence of the *right*-handed adjunction `- ⊗_𝒪 ℰom(𝒪, A)`.

The translation is where the two adjunctions come from. Both are the presheaf clause of
[Stacks, Tag 03EO] composed with sheafification and restricted along the forgetful functor, and
at the presheaf level the left-handed one is literally the right-handed one re-seated along the
braiding (`Stacks.PresheafOfModules.InternalHom.tensorLeftInternalHomAdjunction`). Since
`CategoryTheory.Adjunction.ofNatIsoLeft` only prepends `e.inv` to the counit, and
`CategoryTheory.Adjunction.comp` and `CategoryTheory.Adjunction.restrictFullyFaithful` treat the
two identically, the two counits differ by the *sheafified presheaf braiding* and nothing else
(`sheafTensorHomAdjunction_counit_app`). That braiding is `x ⊗ y ↦ y ⊗ x` on local pure
tensors, so the computation closes:

`s ↦ 1 ⊗ s` (inverse left unitor) `↦ s ⊗ 1` (braiding) `↦ s(1)` (right-handed evaluation).

## Main results

* `CategoryTheory.Adjunction.comp_ofNatIsoLeft_counit_app`: the counit of a composite adjunction
  whose first factor has been re-seated along an isomorphism of left adjoints.
* `Stacks.SheafOfModules.InternalHom.sheafTensorHomAdjunction_counit_app`: **the left-handed
  counit of [Stacks, Tag 03EO] is the sheafified braiding followed by the right-handed
  evaluation morphism** `Stacks.SheafOfModules.InternalHom.internalHomEvaluation`.
* `Stacks.SheafOfModules.InternalHom.internalHomEvaluation_val_app_tensorSectionsAt_one`:
  **evaluation at the unit section**: the evaluation morphism of `ℰom_𝒪(𝒪, A)` carries the local
  pure tensor `s ⊗ 1` to the value of `s` at the unit section.
* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso_hom_val_app`: **the
  trivialisation of `ℰom_𝒪(𝒪, -)`, on sections, is evaluation at the unit section.**
* `Stacks.SheafOfModules.internalHomSecondFunctorUnitIso_hom_app_eq_internalHomSheafUnitIso`:
  **the two trivialisations agree** — on a topological space the component of
  `internalHomSecondFunctorUnitIso` at `G` is `internalHomSheafUnitIso`.

## Implementation notes

The three structural steps (`sheafTensorHomAdjunction_counit_eq_comp`,
`internalHomEvaluation_eq_comp`, `sheafTensorHomAdjunction_counit_app`) are stated and proved
over the plain adjunction API, using the canonical coefficient sheaf
`Stacks.SheafOfModules.Tensor.ringSheaf 𝒪` and its underlying presheaf `Oforget 𝒪.obj`.
The composites are split on sections by the private `comp_val_app_apply` applied as a term
with one factor given explicitly, rather than by `rw`: left to itself the unifier splits the
inverse left unitor of the re-seated monoidal structure into *its* two factors instead.

The passage between the `Stacks.SheafOfModules.Tensor.*` spelling, in which the adjunctions are
written, and the `Stacks.SheafOfModules.TensorSheafification.*` spelling, in which the section
formulas for the unitors and for the sheafification unit are written, is by `rfl`: their
underlying presheaf is `𝒪.obj ⋙ forget₂ CommRingCat RingCat`, and the sheaf-condition witnesses
are proofs of a proposition.

**The identification is not stated at a general ringed site.**
`Stacks.SheafOfModules.internalHomSheafUnitIso` is only constructed on a topological space,
where `SheafHom` of [Stacks, Tag 01CO] lives; the sections formula above is general, and only
the final identification is specialised.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct

universe u

namespace CategoryTheory.Adjunction

/-- **The counit of a composite adjunction whose first factor is re-seated.** For `adj₁ : L₁ ⊣ R₁`
and an isomorphism `e : L₁ ≅ L₁'`, the counit of `(ofNatIsoLeft adj₁ e).comp adj₂` is the second
left adjoint applied to `e.inv`, followed by the counit of `adj₁.comp adj₂`.

Both `CategoryTheory.Adjunction.ofNatIsoLeft` and `CategoryTheory.Adjunction.comp` prepend a
single factor to the counit, so this is the two formulas composed; it is stated over a plain
category because the adjunctions it is used for are written over three reducibly-equal spellings
of one sheaf of rings, where a `rw` with the two formulas separately does not type-check its
motive. -/
theorem comp_ofNatIsoLeft_counit_app
    {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    {L₁ L₁' : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂}
    (adj₁ : L₁ ⊣ R₁) (e : L₁ ≅ L₁') (adj₂ : L₂ ⊣ R₂) (X : C₃) :
    ((Adjunction.ofNatIsoLeft adj₁ e).comp adj₂).counit.app X =
      L₂.map (e.inv.app (R₁.obj (R₂.obj X))) ≫ (adj₁.comp adj₂).counit.app X := by
  rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app, Adjunction.ofNatIsoLeft_counit]
  simp

end CategoryTheory.Adjunction

namespace Stacks.SheafOfModules.InternalHom

variable {D : Type u} [Category.{u} D] (K : GrothendieckTopology D)
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf K CommRingCat.{u})
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F A : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory

/-- Restricting an adjunction along a fully faithful functor, with identity comparisons, leaves
the counit unchanged. -/
private theorem restrictFullyFaithful_refl_counit_app {C C' D : Type*} [Category C] [Category C']
    [Category D] {iC : C ⥤ C'} {L' : C' ⥤ D} {R : D ⥤ C} (adj : L' ⊣ R ⋙ iC)
    (hiC : iC.FullyFaithful) (X : D) :
    (adj.restrictFullyFaithful hiC (Functor.FullyFaithful.id _) (L := iC ⋙ L') (R := R)
      (Iso.refl _) (Iso.refl _)).counit.app X = adj.counit.app X := by
  have := Adjunction.map_restrictFullyFaithful_counit_app adj hiC (Functor.FullyFaithful.id _)
    (L := iC ⋙ L') (R := R) (Iso.refl _) (Iso.refl _) X
  simpa using this

/-- The counit of the left-handed form of [Stacks, Tag 03EO] is the counit of the presheaf clause
composed with sheafification: restricting an adjunction along the fully faithful forgetful
functor, with identity comparisons, leaves the counit unchanged. -/
theorem sheafTensorHomAdjunction_counit_eq_comp :
    (sheafTensorHomAdjunction.{u, u} O F).counit.app A =
      ((Stacks.PresheafOfModules.InternalHom.tensorLeftInternalHomAdjunction.{u, u, u}
        O.obj F.val).comp (sheafifyForgetAdjunction.{u, u} O)).counit.app A := by
  exact restrictFullyFaithful_refl_counit_app _ _ _

/-- The evaluation morphism of [Stacks, Tag 03EM] is the counit of the presheaf clause of
[Stacks, Tag 03EO] as displayed, composed with sheafification — the same reading of
`CategoryTheory.Adjunction.restrictFullyFaithful` as
`sheafTensorHomAdjunction_counit_eq_comp`, on the right-handed adjunction. -/
theorem internalHomEvaluation_eq_comp :
    internalHomEvaluation.{u, u} O F A =
      ((Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction.{u, u, u}
        O.obj F.val).comp (sheafifyForgetAdjunction.{u, u} O)).counit.app A := by
  exact restrictFullyFaithful_refl_counit_app _ _ _

open Stacks.PresheafOfModules.InternalHom in
/-- **The left-handed counit of [Stacks, Tag 03EO] is the sheafified braiding followed by the
evaluation morphism.** The counit of `𝒪 ⊗_𝒪 - ⊣ ℰom_𝒪(F, -)` at `A` is the sheafification of the
braiding `F ⊗ ℰom_𝒪(F, A) ⟶ ℰom_𝒪(F, A) ⊗ F` of presheaves of modules, followed by
`Stacks.SheafOfModules.InternalHom.internalHomEvaluation`.

Both adjunctions are the presheaf clause of [Stacks, Tag 03EO] composed with sheafification and
restricted along the forgetful functor, and the left-handed presheaf clause
`…tensorLeftInternalHomAdjunction` *is* the right-handed one re-seated along the braiding; so
this is `CategoryTheory.Adjunction.comp_ofNatIsoLeft_counit_app` between the two readings. -/
theorem sheafTensorHomAdjunction_counit_app :
    (sheafTensorHomAdjunction.{u, u} O F).counit.app A =
      (PresheafOfModules.sheafification.{u}
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
          ((tensoringRightIsoTensorLeft.{u, u, u} O.obj F.val).inv.app
            ((Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u} O.obj F.val).obj
              A.val)) ≫
        internalHomEvaluation.{u, u} O F A :=
  ((sheafTensorHomAdjunction_counit_eq_comp K O F A).trans
    (Adjunction.comp_ofNatIsoLeft_counit_app (presheafTensorHomAdjunction.{u, u, u} O.obj F.val)
      (tensoringRightIsoTensorLeft.{u, u, u} O.obj F.val)
      (sheafifyForgetAdjunction.{u, u} O) A)).trans
    (congrArg (fun t => (PresheafOfModules.sheafification.{u}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
        ((tensoringRightIsoTensorLeft.{u, u, u} O.obj F.val).inv.app
          ((Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u} O.obj F.val).obj A.val))
        ≫ t)
      (internalHomEvaluation_eq_comp K O F A).symm)

/-- **The trivialisation of `ℰom_𝒪(𝒪, -)` is the inverse left unitor followed by the counit of
[Stacks, Tag 03EO].** This is
`…conjugateEquiv_symm_internalHomSecondFunctorUnitIso_app`, which says that the conjugate
preimage of the trivialisation is the inverse left unitor of the re-seated monoidal structure,
read forwards through `CategoryTheory.conjugateEquiv_adjunction_id`. -/
theorem internalHomSecondFunctorUnitIso_hom_app_eq_leftUnitor_inv_comp_counit :
    (internalHomSecondFunctorUnitIso O).hom.app A =
      (@MonoidalCategoryStruct.leftUnitor _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor O).toMonoidalCategoryStruct
        ((internalHomSecondFunctor.{u, u, u, u} K O
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A)).inv ≫
      (sheafTensorHomAdjunction O (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).counit.app
        A := by
  refine Eq.trans (congrArg (fun t => NatTrans.app t A)
    ((Equiv.apply_symm_apply
      (conjugateEquiv
        (sheafTensorHomAdjunction O (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))
        Adjunction.id)
      (internalHomSecondFunctorUnitIso O).hom).symm)) ?_
  refine Eq.trans (conjugateEquiv_adjunction_id _ _ A) ?_
  rw [conjugateEquiv_symm_internalHomSecondFunctorUnitIso_app K O]

/-- A composite of morphisms of sheaves of modules, read on sections. Stated as a term so that it
can be applied with one factor given explicitly: the composites it is used on contain an inverse
unitor of the re-seated monoidal structure, which is itself a composite, and a `rw` splits that
one instead. -/
private theorem comp_val_app_apply {R : Sheaf K RingCat.{u}}
    {M N P : _root_.SheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ P) (V : Dᵒᵖ) (x : M.val.obj V) :
    (ConcreteCategory.hom ((f ≫ g).val.app V)) x =
      (ConcreteCategory.hom (g.val.app V)) ((ConcreteCategory.hom (f.val.app V)) x) := rfl

/-- **The trivialisation of `ℰom_𝒪(𝒪, -)` on sections, before the evaluation morphism is
computed:** a section `s` of `ℰom_𝒪(𝒪, A)` over `V` goes to the value of the evaluation morphism
on the local pure tensor `s ⊗ 1`.

The two factors of
`internalHomSecondFunctorUnitIso_hom_app_eq_leftUnitor_inv_comp_counit` are read in turn: the
inverse left unitor of the re-seated monoidal structure is the inverse left unitor
`Stacks.SheafOfModules.tensorSheafUnitLeftIso` of the tensor product sheaf by
`SheafOfModules.leftUnitor_sheafTensor_eq_iso`, hence `s ↦ 1 ⊗ s` on sections; and the counit is
the sheafified braiding followed by evaluation by `sheafTensorHomAdjunction_counit_app`, so the
braiding exchanges the two factors. -/
theorem internalHomSecondFunctorUnitIso_hom_val_app_tensorSectionsAt (V : Dᵒᵖ)
    (s : ((internalHomSecondFunctor.{u, u, u, u} K O
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A).val.obj V) :
    ((internalHomSecondFunctorUnitIso O).hom.app A).val.app V s =
      (internalHomEvaluation O (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) A).val.app V
        (Stacks.SheafOfModules.tensorSectionsAt O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf O).property V
          ((internalHomSecondFunctor.{u, u, u, u} K O
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A)
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) s (1 : O.obj.obj V)) := by
  rw [internalHomSecondFunctorUnitIso_hom_app_eq_leftUnitor_inv_comp_counit K O A,
    sheafTensorHomAdjunction_counit_app K O _ A]
  refine Eq.trans (comp_val_app_apply K _
    ((PresheafOfModules.sheafification.{u}
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
        ((Stacks.PresheafOfModules.InternalHom.tensoringRightIsoTensorLeft.{u, u} O.obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val).inv.app
            ((Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u} O.obj
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val).obj A.val)) ≫
      internalHomEvaluation O (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) A) V s) ?_
  refine Eq.trans (comp_val_app_apply K _
    (internalHomEvaluation O (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) A) V _) ?_
  refine congrArg _ ?_
  refine Eq.trans (congrArg (fun y => (ConcreteCategory.hom
      (((PresheafOfModules.sheafification.{u}
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
        ((Stacks.PresheafOfModules.InternalHom.tensoringRightIsoTensorLeft.{u, u} O.obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val).inv.app
            ((Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u} O.obj
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val).obj A.val))).val.app V)) y)
    ((congrArg (fun (i : _ ≅ _) => (ConcreteCategory.hom (i.inv.val.app V)) s)
        (_root_.SheafOfModules.leftUnitor_sheafTensor_eq_iso O
          ((internalHomSecondFunctor.{u, u, u, u} K O
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A))).trans
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf O).property _ V s))) ?_
  refine Eq.trans (Stacks.SheafOfModules.toSheafify_app_map_obj (O := O.obj)
    (hO := (Stacks.SheafOfModules.Tensor.ringSheaf O).property)
    ((Stacks.PresheafOfModules.InternalHom.tensoringRightIsoTensorLeft.{u, u} O.obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val).inv.app
        ((Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u} O.obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val).obj A.val)) V _) ?_
  refine congrArg (fun y => (Stacks.SheafOfModules.TensorSheafification.toSheafify O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf O).property
      (((internalHomSecondFunctor.{u, u, u, u} K O
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A).val ⊗
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val)).app V y) ?_
  rfl

/-- **Evaluation at the unit section.** The evaluation morphism of `ℰom_𝒪(𝒪, A)` carries the
local pure tensor of a section `s` over `U` with the unit section to the value of `s` at the unit
section over the identity of `U`.

Evaluation is the transpose of the identity
(`Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_internalHomEvaluation`), so this is
`Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply` at the identity morphism of the
site and at the unit section, with the hom-equivalence of the sheafification adjunction written
out by `Stacks.SheafOfModules.InternalHom.sheafifyForgetAdjunction_homEquiv`. -/
theorem internalHomEvaluation_val_app_tensorSectionsAt_one (U : D)
    (s : ((internalHomSecondFunctor.{u, u, u, u} K O
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A).val.obj (op U)) :
    (internalHomEvaluation O (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) A).val.app (op U)
        (Stacks.SheafOfModules.tensorSectionsAt O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf O).property (op U)
          ((internalHomSecondFunctor.{u, u, u, u} K O
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A)
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) s (1 : O.obj.obj (op U))) =
      (s.app (op (Over.mk (𝟙 U))))
        (Stacks.PresheafOfModules.InternalHom.restrSection O.obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val U (𝟙 U)
          (1 : O.obj.obj (op U))) := by
  have h1 := sheafTensorHomEquiv_apply O
    ((internalHomSecondFunctor.{u, u, u, u} K O
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A)
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) A
    (internalHomEvaluation O (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) A) U s (𝟙 U)
    (1 : O.obj.obj (op U))
  rw [sheafTensorHomEquiv_internalHomEvaluation] at h1
  have h2 := sheafifyForgetAdjunction_homEquiv O A
    (((internalHomSecondFunctor.{u, u, u, u} K O
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A).val ⊗
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val)
    (internalHomEvaluation O (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) A)
  have hid : (((internalHomSecondFunctor.{u, u, u, u} K O
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A).val.restrictₛₗ (𝟙 U).op) s
      = s := by
    simp [_root_.PresheafOfModules.restrictₛₗ]
  rw [h2, hid] at h1
  exact h1.symm

/-- **The trivialisation of `ℰom_𝒪(𝒪, -)` of [Stacks, Tag 03EM], on sections, is evaluation at
the unit section:** a section `s` of `ℰom_𝒪(𝒪, A)` over `U` — that is, a morphism
`𝒪|_U ⟶ A|_U` on the slice site — goes to its value at the unit section. -/
theorem internalHomSecondFunctorUnitIso_hom_val_app (U : D)
    (s : ((internalHomSecondFunctor.{u, u, u, u} K O
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj A).val.obj (op U)) :
    ((internalHomSecondFunctorUnitIso O).hom.app A).val.app (op U) s =
      (s.app (op (Over.mk (𝟙 U))))
        (Stacks.PresheafOfModules.InternalHom.restrSection O.obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val U (𝟙 U)
          (1 : O.obj.obj (op U))) :=
  (internalHomSecondFunctorUnitIso_hom_val_app_tensorSectionsAt K O A (op U) s).trans
    (internalHomEvaluation_val_app_tensorSectionsAt_one K O A U s)

end Stacks.SheafOfModules.InternalHom

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  (G : _root_.SheafOfModules.{u} (structureSheaf Rc))

/-- **The two trivialisations of `ℰom_{𝒪_X}(𝒪_X, -)` agree.** On a topological space the
component at `G` of the monoidal-closed trivialisation
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso` is the trivialisation
`Stacks.SheafOfModules.internalHomSheafUnitIso` got from the characterisation of [Stacks, Tag
01CO].

`G` is itself an internal Hom sheaf out of the structure sheaf, by evaluation at the unit section
(`Stacks.SheafOfModules.unitSheafHom`), and the comparison of two such realisations is the unique
morphism acting on sections by postcomposition with the identity
(`SheafHom.eq_postcomp_of_isPostcomp`). That the monoidal-closed trivialisation acts that way is
`…internalHomSecondFunctorUnitIso_hom_val_app`: on sections it is evaluation at the unit
section, which is what `Stacks.SheafOfModules.unitOverAddEquiv` returns. -/
theorem internalHomSecondFunctorUnitIso_hom_app_eq_internalHomSheafUnitIso :
    (InternalHom.internalHomSecondFunctorUnitIso Rc).hom.app G =
      (internalHomSheafUnitIso Rc G).hom := by
  have hm : SheafHom.IsPostcomp Rc (𝟙 G)
      (internalHomSheafHom Rc (_root_.SheafOfModules.unit (structureSheaf Rc)) G)
      (unitSheafHom Rc G) ((InternalHom.internalHomSecondFunctorUnitIso Rc).hom.app G) := by
    intro U s
    show (unitOverAddEquiv Rc G U).symm
        (((InternalHom.internalHomSecondFunctorUnitIso Rc).hom.app G).val.app (op U) s) = _
    refine ((unitOverAddEquiv Rc G U).symm_apply_eq).mpr ?_
    refine Eq.trans (InternalHom.internalHomSecondFunctorUnitIso_hom_val_app
      (Opens.grothendieckTopology ↥X) Rc G U s) ?_
    rfl
  exact SheafHom.eq_postcomp_of_isPostcomp hm

end Stacks.SheafOfModules

end
