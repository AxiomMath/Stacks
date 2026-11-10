module

public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialize.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# Tensoring an arbitrary module with a module trivialized by a section

Let `𝒪` be a sheaf of commutative rings on a site, let `F` and `M` be sheaves of `𝒪`-modules,
and let `U` be an object over which `M` is trivial, meaning that `M` restricted to the localized
site `C/U` is isomorphic to the structure sheaf there. Then `F ⊗ M` restricted to `C/U` is
isomorphic to `F` restricted to `C/U`, and on sections over `U` the isomorphism is `t ↦ t ⊗ a`,
where `a` is the section of `M` corresponding to `1`.

On a ringed space with local stalks this applies to an invertible module `L`, a global section
`s` of it and any open inside the nonvanishing open `X_s`, where the trivialization is the
trivialization clause of [Stacks, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY) and the
section `a` is `s|_W`. The case `F = 𝒪` of the resulting statement about sections is that clause
itself, `Stacks.NonvanishingTrivialize.bijective_smul`; nothing is assumed about `F` here. Since
`M` is arbitrary, the tensor powers `L ^⊗ n` with `n : ℤ` are instances of it, with `s` a global
section of the power.

## Main definitions

* `Stacks.SheafOfModules.TensorGenerator.tensorPresheafSliceIso`: the tensor product presheaf of
  two restrictions to a localized site is the restriction of the tensor product presheaf.
* `Stacks.SheafOfModules.TensorGenerator.tensorSheafSliceIso`: the same for the tensor product
  sheaf of Tag 01CA, `ℱ|_U ⊗ 𝒢|_U ≅ (ℱ ⊗ 𝒢)|_U`.
* `Stacks.SheafOfModules.TensorGenerator.tensorTrivialIso`: **the sheaf-level statement.** If
  `M|_U` is isomorphic to the structure sheaf of `C/U`, then `(F ⊗ M)|_U ≅ F|_U`.
* `Stacks.SheafOfModules.TensorGenerator.generator`: the section of `M` over `U` that such a
  trivialization sends to `1`.
* `Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv`: **the sections-level statement**,
  as a linear equivalence `Γ(F, U) ≃ₗ Γ(F ⊗ M, U)` over the ring of sections of `𝒪` on `U`.
* `Stacks.TensorPowerTrivialize.unitIsoOfSection` and
  `Stacks.TensorPowerTrivialize.tensorSectionsEquiv`: the same on a ringed space with local
  stalks, for an invertible module, a global section of it and an open inside the nonvanishing
  open of that section.

## Main results

* `Stacks.SheafOfModules.TensorGenerator.tensorSheafSliceIso_hom_tensorSectionsAt`: the
  comparison carries the section `a ⊗ b` of the tensor product over `C/U` to the section
  `a ⊗ b` of the tensor product over `C`.
* `Stacks.SheafOfModules.TensorGenerator.tensorTrivialIso_inv_app` and
  `Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv_apply`: the equivalence is
  `t ↦ t ⊗ a`. Without these the equivalence says only that the two modules of sections are
  abstractly isomorphic.
* `Stacks.TensorPowerTrivialize.generator_unitIsoOfSection` and
  `Stacks.TensorPowerTrivialize.tensorSectionsEquiv_apply`: on a ringed space the generator is
  `s|_W` and the equivalence is `t ↦ t ⊗ s|_W`.

## Implementation notes

The comparison `tensorSheafSliceIso` is *not* the tensorator of the monoidal functor
`Stacks.SheafOfModules.SliceRestriction.tensorSheafOver`. The two have the same source and
target, but the tensorator is produced by monoidal localization and its value on a section
`a ⊗ b` is inaccessible, while the comparison built here is the morphism adjoint to the
restricted sheafification unit, whose value on `a ⊗ b` is one application of the unit triangle
of the sheafification adjunction. That value is the whole content of `tensorSectionsEquiv_apply`.

The localized site `C/U` is unavoidable: the hypothesis on `M` is not a statement about sections
over `U` alone, since multiplication by `a` has to be bijective over every object above `U`, and
`SheafOfModules.over` is the vocabulary in which that is one isomorphism rather than a family.

The structure sheaf of rings is spelled `Stacks.SheafOfModules.TensorSheafification.structureSheaf
𝒪 h𝒪` throughout, with the sheaf condition `h𝒪` an explicit argument, rather than through the
reducible abbreviations `structureSheaf X.sheaf` and
`structureSheafRing`: those unfold past the tensor
product sheaf's own ring, so with either of them the scalar action on `Γ(F ⊗ M, U)` is not found
by instance search.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 00XB](https://stacks.math.columbia.edu/tag/00XB)
-/

@[expose] public section

attribute [local instance_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorSheafification
open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules.TensorGenerator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

/-! ### The tensor product and restriction to a localized site -/

/-- The tensor product presheaf of the restrictions of two sheaves of modules to the localized
site over `U` is the restriction of their tensor product presheaf: over an object `V → U` both
are `ℱ(V) ⊗_{𝒪(V)} 𝒢(V)`, and both restriction maps send a pure tensor to the tensor of the
restrictions. -/
noncomputable def tensorPresheafSliceIso
    (A B : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (PresheafOfModules.tensorObj (O := (SliceRestriction.sliceRingPresheaf 𝒪 U))
        ((A.over U).val) ((B.over U).val)) ≅
      (SliceRestriction.sliceFunctor 𝒪 U).obj
        ((PresheafOfModules.tensorObj (O := 𝒪) (A.val) (B.val))) :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; rfl)

/-- **The tensor product sheaf of Tag 01CA commutes with restriction to a localized site**,
`ℱ|_U ⊗ 𝒢|_U ≅ (ℱ ⊗ 𝒢)|_U`, as the morphism adjoint to the restricted sheafification unit. -/
noncomputable def tensorSheafSliceIso
    (A B : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(SliceRestriction.sliceRingPresheaf 𝒪 U),
        Presheaf.isSheaf_of_isSheaf_comp _ ((SliceRestriction.sliceRingPresheaf 𝒪 U))
          (forget₂ CommRingCat RingCat) ((SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U))⟩).obj
        ((A.over U))).obj ((B.over U))) ≅
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
        (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (A)).obj (B))).over U :=
  (SliceRestriction.sliceSheafify 𝒪 h𝒪 U).mapIso (tensorPresheafSliceIso 𝒪 h𝒪 U A B) ≪≫
    ((SliceRestriction.sliceSheafifyIso 𝒪 h𝒪 U).app
      (PresheafOfModules.tensorObj (O := 𝒪) A.val B.val)).symm

/-- **The comparison preserves pure tensors.** Over `U` itself the section `a ⊗ b` of
`ℱ|_U ⊗ 𝒢|_U` goes to the section `a ⊗ b` of `ℱ ⊗ 𝒢`. -/
theorem tensorSheafSliceIso_hom_tensorSectionsAt
    (A B : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    ((tensorSheafSliceIso 𝒪 h𝒪 U A B).hom.val.app (op (Over.mk (𝟙 U)))).hom
        (tensorSectionsAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
          (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
          (op (Over.mk (𝟙 U))) (A.over U) (B.over U) a b) =
      tensorSectionsAt 𝒪 h𝒪 (op U) A B a b := by
  have h2 : (((SliceRestriction.sliceSheafify 𝒪 h𝒪 U).map
        (tensorPresheafSliceIso 𝒪 h𝒪 U A B).hom).val.app (op (Over.mk (𝟙 U)))).hom
        (tensorSectionsAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
          (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
          (op (Over.mk (𝟙 U))) (A.over U) (B.over U) a b) =
      ((TensorSheafification.toSheafify (SliceRestriction.sliceRingPresheaf 𝒪 U)
          (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
          ((SliceRestriction.sliceFunctor 𝒪 U).obj
            (PresheafOfModules.tensorObj (O := 𝒪) A.val B.val))).app
        (op (Over.mk (𝟙 U)))).hom
        (a ⊗ₜ[((SliceRestriction.sliceRingPresheaf 𝒪 U).obj (op (Over.mk (𝟙 U))))] b) :=
    toSheafify_app_map_obj (SliceRestriction.sliceRingPresheaf 𝒪 U)
      (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
      (tensorPresheafSliceIso 𝒪 h𝒪 U A B).hom (op (Over.mk (𝟙 U))) (a ⊗ₜ b)
  have h1 : ((tensorSheafSliceIso 𝒪 h𝒪 U A B).hom.val.app (op (Over.mk (𝟙 U)))).hom
        (tensorSectionsAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
          (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
          (op (Over.mk (𝟙 U))) (A.over U) (B.over U) a b) =
      (((SliceRestriction.sliceComparison 𝒪 h𝒪 U).app
          (PresheafOfModules.tensorObj (O := 𝒪) A.val B.val)).val.app
        (op (Over.mk (𝟙 U)))).hom
        ((((SliceRestriction.sliceSheafify 𝒪 h𝒪 U).map
          (tensorPresheafSliceIso 𝒪 h𝒪 U A B).hom).val.app (op (Over.mk (𝟙 U)))).hom
          (tensorSectionsAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
            (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
            (op (Over.mk (𝟙 U))) (A.over U) (B.over U) a b)) := rfl
  rw [h1, h2]
  set O := SliceRestriction.sliceRingPresheaf 𝒪 U
  set hO := SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U
  set P := PresheafOfModules.tensorObj (O := 𝒪) A.val B.val
  let adj := TensorSheafification.sheafifyAdjunction O hO
  let e := (adj.homEquiv ((SliceRestriction.sliceFunctor 𝒪 U).obj P)
    ((SliceRestriction.overFunctor 𝒪 h𝒪 U).obj ((sheafifyFunctor 𝒪 h𝒪).obj P))).symm
      (SliceRestriction.sliceUnit 𝒪 h𝒪 U P)
  have he : TensorSheafification.toSheafify O hO ((SliceRestriction.sliceFunctor 𝒪 U).obj P) ≫
      (SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (TensorSheafification.structureSheaf O hO).obj)).map e =
      SliceRestriction.sliceUnit 𝒪 h𝒪 U P :=
    (adj.homEquiv_unit (f := e)).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
  exact congrArg (fun k => (k.app (op (Over.mk (𝟙 U)))).hom
    (a ⊗ₜ[(O.obj (op (Over.mk (𝟙 U))))] b)) he

/-! ### Tensoring with a trivialized factor -/

variable (F M : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- **Tensoring with a sheaf of modules that is trivial over `U` changes nothing over `U`.**
If `M` restricted to the localized site over `U` is isomorphic to the structure sheaf there,
then `(F ⊗ M)|_U ≅ F|_U` for an arbitrary sheaf of modules `F`. -/
noncomputable def tensorTrivialIso
    (hM : M.over U ≅ SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
      (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj (M))).over U ≅ F.over U :=
  (tensorSheafSliceIso 𝒪 h𝒪 U F M).symm ≪≫
    Invertible.tensorProductIso (SliceRestriction.sliceRingPresheaf 𝒪 U)
      (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (Iso.refl (F.over U)) hM ≪≫
    Invertible.tensorProductRightUnitor (SliceRestriction.sliceRingPresheaf 𝒪 U)
      (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (F.over U)

/-- The section of `M` over `U` that a trivialization of `M` over `U` sends to `1`. -/
noncomputable def generator
    (hM : M.over U ≅ SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U)) :
    M.val.obj (op U) :=
  (hM.inv.val.app (op (Over.mk (𝟙 U)))).hom
    (1 : (SliceRestriction.sliceRingPresheaf 𝒪 U).obj (op (Over.mk (𝟙 U))))

/-- **The inverse of `tensorTrivialIso` is `t ↦ t ⊗ a`** on sections over `U`, where `a` is the
section of `M` corresponding to `1`. -/
theorem tensorTrivialIso_inv_app
    (hM : M.over U ≅ SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U))
    (t : F.val.obj (op U)) :
    ((tensorTrivialIso 𝒪 h𝒪 U F M hM).inv.val.app (op (Over.mk (𝟙 U)))).hom t =
      tensorSectionsAt 𝒪 h𝒪 (op U) F M t (generator 𝒪 h𝒪 U M hM) := by
  have hr : ((Invertible.tensorProductRightUnitor (SliceRestriction.sliceRingPresheaf 𝒪 U)
          (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (F.over U)).inv.val.app
        (op (Over.mk (𝟙 U)))).hom t =
      tensorSectionsAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
        (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (op (Over.mk (𝟙 U))) (F.over U)
        (SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U)) t
        (1 : (SliceRestriction.sliceRingPresheaf 𝒪 U).obj (op (Over.mk (𝟙 U)))) := by
    conv_lhs => rw [← tensorSections_rightUnitorAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
      (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (op (Over.mk (𝟙 U))) (F.over U) t]
    exact congrArg (fun k => (k.val.app (op (Over.mk (𝟙 U)))).hom
        (tensorSectionsAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
          (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (op (Over.mk (𝟙 U))) (F.over U)
          (SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U)) t
          (1 : (SliceRestriction.sliceRingPresheaf 𝒪 U).obj (op (Over.mk (𝟙 U))))))
      (Invertible.tensorProductRightUnitor (SliceRestriction.sliceRingPresheaf 𝒪 U)
        (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (F.over U)).hom_inv_id
  have hi : ((Invertible.tensorProductIso (SliceRestriction.sliceRingPresheaf 𝒪 U)
          (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
          (Iso.refl (F.over U)) hM).inv.val.app (op (Over.mk (𝟙 U)))).hom
        (tensorSectionsAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
          (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (op (Over.mk (𝟙 U))) (F.over U)
          (SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U)) t
          (1 : (SliceRestriction.sliceRingPresheaf 𝒪 U).obj (op (Over.mk (𝟙 U))))) =
      tensorSectionsAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
        (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (op (Over.mk (𝟙 U))) (F.over U)
        (M.over U) t (generator 𝒪 h𝒪 U M hM) :=
    tensorSections_tensorProductIsoAt (SliceRestriction.sliceRingPresheaf 𝒪 U)
      (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (op (Over.mk (𝟙 U)))
      (F.over U) (F.over U)
      (SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U)) (M.over U)
      (Iso.refl (F.over U)).symm hM.symm t
      (1 : (SliceRestriction.sliceRingPresheaf 𝒪 U).obj (op (Over.mk (𝟙 U))))
  have hd : ((tensorTrivialIso 𝒪 h𝒪 U F M hM).inv.val.app (op (Over.mk (𝟙 U)))).hom t =
      ((tensorSheafSliceIso 𝒪 h𝒪 U F M).hom.val.app (op (Over.mk (𝟙 U)))).hom
        (((Invertible.tensorProductIso (SliceRestriction.sliceRingPresheaf 𝒪 U)
            (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
            (Iso.refl (F.over U)) hM).inv.val.app (op (Over.mk (𝟙 U)))).hom
          (((Invertible.tensorProductRightUnitor (SliceRestriction.sliceRingPresheaf 𝒪 U)
              (SliceRestriction.isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) (F.over U)).inv.val.app
            (op (Over.mk (𝟙 U)))).hom t)) := rfl
  rw [hd, hr, hi, tensorSheafSliceIso_hom_tensorSectionsAt]

/-- **Multiplying by a trivializing section is a linear equivalence on sections.** For an
arbitrary sheaf of modules `F` and a sheaf of modules `M` trivial over `U`, the sections of `F`
over `U` and the sections of `F ⊗ M` over `U` are isomorphic as modules over `𝒪(U)`. -/
noncomputable def tensorSectionsEquiv
    (hM : M.over U ≅ SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U)) :
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩)).val.obj
        (op U) ≃ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat)
            (h𝒪)⟩).obj.obj (op U)]
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
        (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj (M))).val.obj (op U) :=
  ((SheafOfModules.forget (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U) ⋙
      PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).mapIso
    (tensorTrivialIso 𝒪 h𝒪 U F M hM).symm).toLinearEquiv

/-- **The equivalence is `t ↦ t ⊗ a`**, where `a` is the section of `M` corresponding to `1`. -/
theorem tensorSectionsEquiv_apply
    (hM : M.over U ≅ SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U))
    (t : F.val.obj (op U)) :
    tensorSectionsEquiv 𝒪 h𝒪 U F M hM t =
      tensorSectionsAt 𝒪 h𝒪 (op U) F M t (generator 𝒪 h𝒪 U M hM) :=
  tensorTrivialIso_inv_app 𝒪 h𝒪 U F M hM t

end Stacks.SheafOfModules.TensorGenerator

namespace Stacks.TensorPowerTrivialize

/-! ### An invertible module and a global section on a ringed space -/

variable {X : RingedSpace.{u}}
  (hX : Presheaf.IsSheaf (Opens.grothendieckTopology X) (structureRingPresheaf X.presheaf))
  (F L : SheafOfModules.{u} (structureSheaf X.presheaf hX))
  [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
    (_root_.structureSheaf X.sheaf).property L]

/-- **A global section trivializes an invertible module on every open inside its nonvanishing
open**, as an isomorphism with the structure sheaf of the localized site. This is the
trivialization clause of Stacks Tag 01CY, `Stacks.NonvanishingTrivialize.isIso_over_of_le`,
inverted. -/
noncomputable def unitIsoOfSection (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    L.over W ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf X.presheaf hX W) :=
  (@asIso _ _ _ _ ((L.unitHomEquiv.symm s).over W)
    (Stacks.NonvanishingTrivialize.isIso_over_of_le s hW)).symm

/-- The section of `L` that `unitIsoOfSection` sends to `1` is `s|_W`. -/
theorem generator_unitIsoOfSection (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    Stacks.SheafOfModules.TensorGenerator.generator X.presheaf hX W L
      (unitIsoOfSection hX L s hW) = s.eval (op W) := by
  change ((L.unitHomEquiv.symm s).val.app (op W)).hom (1 : X.presheaf.obj (op W)) =
    s.eval (op W)
  have h := Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app s W
    (1 : X.presheaf.obj (op W))
  rwa [one_smul] at h

/-- **Multiplying by a nonvanishing global section of an invertible module is a linear
equivalence on sections, for an arbitrary second module.** On an open `W` inside the nonvanishing
open of a global section `s` of an invertible module `L`, the sections of `F` over `W` and the
sections of `F ⊗ L` over `W` are isomorphic as `𝒪_X(W)`-modules, for every sheaf of modules `F`.

Taking `F = 𝒪_X` recovers the trivialization clause of Stacks Tag 01CY. -/
noncomputable def tensorSectionsEquiv (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
            (forget₂ CommRingCat RingCat) (hX)⟩)).val.obj
        (op W) ≃ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
            (forget₂ CommRingCat RingCat) (hX)⟩).obj.obj (op W)]
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
          (forget₂ CommRingCat RingCat) (hX)⟩).obj (F)).obj (L))).val.obj (op W) :=
  Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv X.presheaf hX W F L
    (unitIsoOfSection hX L s hW)

/-- **The equivalence is `t ↦ t ⊗ s|_W`.** -/
theorem tensorSectionsEquiv_apply (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) (t : F.val.obj (op W)) :
    tensorSectionsEquiv hX F L s hW t =
      Stacks.SheafOfModules.tensorSectionsAt X.presheaf hX (op W) F L t (s.eval (op W)) := by
  rw [← generator_unitIsoOfSection hX L s hW]
  exact Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv_apply X.presheaf hX W F L
    (unitIsoOfSection hX L s hW) t

end Stacks.TensorPowerTrivialize

end
