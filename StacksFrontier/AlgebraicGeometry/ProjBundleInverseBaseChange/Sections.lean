module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSubmoduleFlatPullback
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGeneratorGlue
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.RestrictTensorSection
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.PowerCompareAgreement

/-!
# The four isomorphisms of the inverse base change, on a section

We give section formulas for the four isomorphisms from which the trivialisations of the base
change of the inverse of an invertible module are built — `negOneMulIso`, `negOneMulIso'`,
`pullbackTensorIso` and `pullbackUnitMonoidalIso` — and deduce from them the value on a section of
the base change comparison of the inverse.

All four are stated over `Stacks.SheafInternalHom.monoidalCategory`, the monoidal structure
obtained by localizing the objectwise tensor product of presheaves of modules along
sheafification. A section of `M ⊗ N` for that structure is therefore *not* of the form
`Stacks.SheafOfModules.tensorSectionsAt`, which is a section of the tensor product sheaf
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` of Tag 05NA; the crossing is
`AlgebraicGeometry.SheafOfModules.tensorIso`, and likewise
`AlgebraicGeometry.SheafOfModules.unitIso` crosses the monoidal unit to `SheafOfModules.unit`.
Each statement below writes the crossing into itself, in the *inverse* direction on the source
and on the target, so that it applies to a product section of a tensor product sheaf.

## Main definitions

* `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso`: the right trivialisation read as a
  trivialisation `L ⊗ L^{⊗ -1} ≅ 𝒪_X` of the tensor product *sheaf*.
* `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'`: the same, built from the left
  trivialisation, with no braiding.

## Main results

* `Stacks.ProjBundleInverseBaseChange.negOneMulIso_hom_tensorSectionsAt`: the right
  trivialisation `L^{⊗ -1} ⊗ L ≅ 𝟙` on a product section is Tag 01CU's successor comparison at
  `n = -1` on that product section, reindexed to degree zero and read in the monoidal unit.
* `Stacks.ProjBundleInverseBaseChange.negOneMulIso'_hom_tensorSectionsAt`: the left
  trivialisation `L ⊗ L^{⊗ -1} ≅ 𝟙` on a product section takes the same value, with the two
  factors exchanged.

* `Stacks.ProjBundleInverseBaseChange`
  `.exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top_right`: the pairing
  existence of [Stacks, Tag 01CY] with the generating section in the second factor of a
  trivialisation.
* `Stacks.ProjBundleInverseBaseChange.exists_negOneMulIso_hom_tensorSectionsAt_eq_one`: on an open
  where a section `b` of an invertible `L` generates there is a section `w` of `L^{⊗ -1}` pairing
  with it to `1`.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorIso_hom_val_app` and
  `pullbackUnitMonoidalIso_hom_val_app`: Tag 01CD and the pullback of the unit on a section.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorIso_hom_pullbackSection_tensorSectionsAt`:
  Tag 01CD on the pullback of a product section: the pullback of the product of two sections is
  the product of their pullbacks.
* `Stacks.ProjBundleInverseBaseChange.invIso_inv_val_app`: if `a ⊗ b` pairs to `1` under one
  two-sided tensor inverse's right trivialisation and `b ⊗ c` pairs to `1` under another's left
  trivialisation, then the comparison of the two inverses carries `c` back to `a`.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse_mulIso'_hom_pullbackSection`: if `w₀`
  and `b₀` pair to `1` over `V` then their pullbacks pair to `1` over `W`.
* `Stacks.ProjBundleInverseBaseChange.ofIso_mulIso_hom_tensorSectionsAt`: the left trivialisation
  of `Stacks.TensorPowers.TensorInverse.ofIso` is `negOneMulIso'` with the first factor carried
  across the comparison.
* `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso_inv_val_app`: Tag 0B3V's base
  change of the inverse, read on a section: it carries a section `c` of `(L')^{⊗ -1}` to the
  pullback of `w₀` whenever the two pairings above hold.
* `Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app`: the previous result
  at `g = σ`, `L = 𝒪(1)` and `L' = 𝓛`.

## Implementation notes

`negOneMulIso` and `negOneMulIso'` are read down to
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` at the exponent `-1` and no further. Tag
01CU's `tensorPower` is `(F.asEquivalence ^ n).functor.obj 𝒪` for `F` the functor "tensor by `L`",
so at a negative exponent the power is the chosen quasi-inverse of an equivalence applied to the
structure sheaf, an object with no presentation; there is nothing further for the successor
comparison on a section of it to equal.

Each of the four isomorphisms is a composite whose first and last steps are crossings, so the
proofs cancel the crossings by `Stacks.SheafOfModules.hom_val_app_inv_val_app` and reduce the rest
by `Stacks.SheafOfModules.comp_val_app_apply`. They are written in term mode, since the
`CategoryTheory.MonoidalCategoryStruct` of the localized structure does not reduce at the
transparency at which `rw` and `simp` work.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

universe v u w

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry Opposite

namespace Stacks.ProjBundleInverseBaseChange

open Stacks.SheafOfModules.TensorSheafification Stacks.TensorPowers Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorPower
open Stacks.AlgebraicGeometry.ProjRepresentsF1 (pullbackTensorSchemeIso)
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

/-! ### The two trivialisations of the `(-1)`st tensor power -/

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- **The right trivialisation `L^{⊗ -1} ⊗ L ≅ 𝟙` on a product section.** On the section of
`L^{⊗ -1} ⊗ L` that `AlgebraicGeometry.SheafOfModules.tensorIso` identifies with the product of
`s` and `t`, `Stacks.ProjBundleInverseBaseChange.negOneMulIso` is the section of the monoidal unit
that `AlgebraicGeometry.SheafOfModules.unitIso` identifies with the value of Tag 01CU's successor
comparison at `n = -1` on that product section, reindexed from degree `-1 + 1` to degree zero. -/
public theorem negOneMulIso_hom_tensorSectionsAt (U : Cᵒᵖ)
    (s : (tensorPower 𝒪 h𝒪 L (-1)).val.obj U) (t : L.val.obj U) :
    (negOneMulIso 𝒪 h𝒪 L).hom.val.app U
        ((AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪
            (tensorPower 𝒪 h𝒪 L (-1)) L).inv.val.app U
          (tensorSectionsAt 𝒪 h𝒪 U (tensorPower 𝒪 h𝒪 L (-1)) L s t)) =
      (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv.val.app U
        ((eqToHom (tensorPower_zero 𝒪 h𝒪 L)).val.app U
          ((tensorPowerReindex 𝒪 h𝒪 L (show (-1 : ℤ) + 1 = 0 by omega)).hom.val.app U
            ((tensorPowerSuccIso 𝒪 h𝒪 L (-1)).hom.val.app U
              (tensorSectionsAt 𝒪 h𝒪 U (tensorPower 𝒪 h𝒪 L (-1)) L s t)))) :=
  congrArg
    (fun z : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
        (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (tensorPower 𝒪 h𝒪 L (-1))).obj (L))).val.obj U =>
      ((tensorPowerSuccIso 𝒪 h𝒪 L (-1)).hom ≫
          (tensorPowerReindex 𝒪 h𝒪 L (show (-1 : ℤ) + 1 = 0 by omega)).hom ≫
            eqToHom (tensorPower_zero 𝒪 h𝒪 L) ≫
              (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv).val.app U z)
    (Stacks.SheafOfModules.hom_val_app_inv_val_app
      (AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) L) U
      (tensorSectionsAt 𝒪 h𝒪 U (tensorPower 𝒪 h𝒪 L (-1)) L s t))

/-- **The left trivialisation `L ⊗ L^{⊗ -1} ≅ 𝟙` on a product section.** Its value on the product
of `t` and `s` is the value of
`Stacks.ProjBundleInverseBaseChange.negOneMulIso_hom_tensorSectionsAt` on the product of `s` and
`t`. -/
public theorem negOneMulIso'_hom_tensorSectionsAt (U : Cᵒᵖ)
    (t : L.val.obj U) (s : (tensorPower 𝒪 h𝒪 L (-1)).val.obj U) :
    (negOneMulIso' 𝒪 h𝒪 L).hom.val.app U
        ((AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 L
            (tensorPower 𝒪 h𝒪 L (-1))).inv.val.app U
          (tensorSectionsAt 𝒪 h𝒪 U L (tensorPower 𝒪 h𝒪 L (-1)) t s)) =
      (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv.val.app U
        ((eqToHom (tensorPower_zero 𝒪 h𝒪 L)).val.app U
          ((tensorPowerReindex 𝒪 h𝒪 L (show (-1 : ℤ) + 1 = 0 by omega)).hom.val.app U
            ((tensorPowerSuccIso 𝒪 h𝒪 L (-1)).hom.val.app U
              (tensorSectionsAt 𝒪 h𝒪 U (tensorPower 𝒪 h𝒪 L (-1)) L s t)))) :=
  Eq.trans
    (congrArg
      (fun z : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _
          (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).obj (tensorPower 𝒪 h𝒪 L
          (-1)))).val.obj U =>
        ((tensorSheafBraiding 𝒪 h𝒪 L (tensorPower 𝒪 h𝒪 L (-1))).hom ≫
            (AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪
                (tensorPower 𝒪 h𝒪 L (-1)) L).inv ≫
              (negOneMulIso 𝒪 h𝒪 L).hom).val.app U z)
      (Stacks.SheafOfModules.hom_val_app_inv_val_app
        (AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 L (tensorPower 𝒪 h𝒪 L (-1))) U
        (tensorSectionsAt 𝒪 h𝒪 U L (tensorPower 𝒪 h𝒪 L (-1)) t s)))
    (Eq.trans
      (congrArg
        (fun z : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _
            (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (tensorPower 𝒪 h𝒪 L (-1))).obj
            (L))).val.obj U =>
          (negOneMulIso 𝒪 h𝒪 L).hom.val.app U
            ((AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪
                (tensorPower 𝒪 h𝒪 L (-1)) L).inv.val.app U z))
        (tensorSheafBraiding_tensorSectionsAt 𝒪 h𝒪 U L (tensorPower 𝒪 h𝒪 L (-1)) t s))
      (negOneMulIso_hom_tensorSectionsAt 𝒪 h𝒪 L U s t))

end Site

/-! ### A generating section in the second factor of a trivialisation -/

section Flip

open Stacks.SheafOfModules.TensorStalkRingedSpace IsLocalRing TopologicalSpace

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  {M N : _root_.SheafOfModules.{u} (structureSheafRing X)}

/-- **A section generating at every point of an open pairs to the unit section there — with the
generator in the *second* factor.**
`Stacks.SheafOfModules.exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top`
produces the pairing partner of a generating section of the *first* factor of a trivialisation
`ψ : ℳ ⊗ 𝒩 ≅ 𝒪_X`; this is the same statement for a generating section `w` of the second factor,
producing a section of `ℳ`. -/
public theorem exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top_right
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (M)).obj
        (N)) ≅
      _root_.SheafOfModules.unit (structureSheafRing X))
    (V : Opens X.carrier) (w : N.val.obj (op V))
    (hw : ∀ (y : X.carrier) (hy : y ∈ V), grpGerm X N.val y V hy w ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X N.val y))) :
    ∃ b : M.val.obj (op V), tensorPairing ψ V b w = unitSection X V := by
  obtain ⟨b, hb⟩ :=
    Stacks.SheafOfModules.exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top
      (tensorSheafBraiding X.presheaf (structureSheafRing X).property N M ≪≫ ψ) V w hw
  refine ⟨b, Eq.trans (congrArg
    (fun z : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (M)).obj
        (N)).val.obj (op V) =>
      ψ.hom.val.app (op V) z)
    (Stacks.SheafOfModules.tensorSheafBraiding_tensorSectionsAt X.presheaf
      (structureSheafRing X).property (op V) N M w b)).symm hb⟩

end Flip

/-! ### The pairing to `1` exists wherever the section generates -/

section Pairing

open Stacks.SheafOfModules.TensorStalkRingedSpace IsLocalRing TopologicalSpace

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  (L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L]

/-- **The pairing `L ⊗ L^{⊗ -1} ≅ 𝒪_X` as a trivialization of the tensor product sheaf.** The
right trivialization `Stacks.ProjBundleInverseBaseChange.negOneMulIso` reads the two factors in
the order `L^{⊗ -1} ⊗ L` and lives over the localized monoidal structure, while
`Stacks.SheafOfModules.tensorPairing` — the pairing on sections whose existence statements Tag
01CY proves — is stated for an isomorphism of the tensor product *sheaf* of Tag 01CA with
`SheafOfModules.unit`, with the factors in the order `L ⊗ L^{⊗ -1}`. This composite crosses both
differences: `Stacks.SheafOfModules.tensorSheafBraiding` exchanges the factors,
`Stacks.SheafOfModules.tensorObjIso` crosses the two tensor products and
`Stacks.SheafOfModules.sheafifyUnitIso` crosses the two units. -/
public def negOneMulPairingIso :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (L)).obj
        (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1))) ≅
      _root_.SheafOfModules.unit (structureSheafRing X) :=
  tensorSheafBraiding X.presheaf (structureSheafRing X).property L
      (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1)) ≪≫
    (Stacks.SheafOfModules.tensorObjIso X.presheaf (structureSheafRing X).property
      (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1)) L).symm ≪≫
    negOneMulIso X.presheaf (structureSheafRing X).property L ≪≫
    Stacks.SheafOfModules.sheafifyUnitIso X.presheaf (structureSheafRing X).property

/-- **The pairing `L ⊗ L^{⊗ -1} ≅ 𝒪_X` built from the left trivialisation.** The trivialisation
of the tensor product sheaf `L ⊗ L^{⊗ -1}` of Tag 01CA obtained from
`Stacks.ProjBundleInverseBaseChange.negOneMulIso'`, which already reads its factors in the order
`L ⊗ L^{⊗ -1}`, by `Stacks.SheafOfModules.tensorObjIso` between the tensor product sheaf and the
tensor product of the localized monoidal structure, and `Stacks.SheafOfModules.sheafifyUnitIso`
between the two units. It has the same source and target as
`Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso` but involves no braiding. -/
public def negOneMulPairingIso' :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (L)).obj
        (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1))) ≅
      _root_.SheafOfModules.unit (structureSheafRing X) :=
  (Stacks.SheafOfModules.tensorObjIso X.presheaf (structureSheafRing X).property L
      (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1))).symm ≪≫
    negOneMulIso' X.presheaf (structureSheafRing X).property L ≪≫
    Stacks.SheafOfModules.sheafifyUnitIso X.presheaf (structureSheafRing X).property

/-- **A generating section pairs to `1` with a section of the inverse.** On an open `V` where a
section `b` of an invertible `L` generates — its germ at every point of `V` avoiding `𝔪_y L_y` —
there is a section `w` of `L^{⊗ -1}` over `V` pairing with `b` to `1` under the right
trivialization `Stacks.ProjBundleInverseBaseChange.negOneMulIso`. -/
public theorem exists_negOneMulIso_hom_tensorSectionsAt_eq_one (V : Opens X.carrier)
    (b : L.val.obj (op V))
    (hb : ∀ (y : X.carrier) (hy : y ∈ V), grpGerm X L.val y V hy b ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y))) :
    ∃ w : (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1)).val.obj (op V),
      (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf
          (structureSheafRing X).property).hom.val.app (op V)
        ((negOneMulIso X.presheaf (structureSheafRing X).property L).hom.val.app (op V)
          ((Stacks.SheafOfModules.tensorObjIso X.presheaf (structureSheafRing X).property
              (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1))
              L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf (structureSheafRing X).property (op V)
              (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1)) L w b)))
        = (1 : (structureSheaf X.presheaf (structureSheafRing X).property).obj.obj (op V)) := by
  obtain ⟨w, hw⟩ :=
    exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top
      (negOneMulPairingIso L) V b hb
  refine ⟨w, ?_⟩
  refine Eq.trans (congrArg
    (fun z : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj
        (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1))).obj
        L).val.obj (op V) =>
      (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf
          (structureSheafRing X).property).hom.val.app (op V)
        ((negOneMulIso X.presheaf (structureSheafRing X).property L).hom.val.app (op V)
          ((Stacks.SheafOfModules.tensorObjIso X.presheaf (structureSheafRing X).property
              (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1))
              L).inv.val.app (op V) z)))
    (Stacks.SheafOfModules.tensorSheafBraiding_tensorSectionsAt X.presheaf
      (structureSheafRing X).property (op V) L
      (Invertible.tensorPower X.presheaf (structureSheafRing X).property L (-1)) b w)).symm hw

end Pairing

/-! ### Tag 01CD and the pullback of the unit -/

section Scheme

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- **Tag 01CD at the localized monoidal structure, on a section.** The crossing
`AlgebraicGeometry.SheafOfModules.tensorIso` on the source and on the target carries
`Stacks.ProjBundleInverseBaseChange.pullbackTensorIso` to the comparison
`Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso`, whose action on the pullback
of a product section is known. -/
public theorem pullbackTensorIso_hom_val_app (M N : Mods X) (V : X'.Opens)
    (x : ((pullbackFunctor g).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          (X.presheaf) (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).obj
          (M)).obj (N)))).val.obj (op V)) :
    (pullbackTensorIso g M N).hom.val.app (op V)
        (((pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
            (isSheaf_structureRingPresheaf X) M N)).inv.val.app (op V) x) =
      (AlgebraicGeometry.SheafOfModules.tensorIso X'.presheaf
            (isSheaf_structureRingPresheaf X') ((pullbackFunctor g).obj M)
            ((pullbackFunctor g).obj N)).inv.val.app (op V)
        ((pullbackTensorSchemeIso g M N).hom.val.app (op V) x) :=
  congrArg
    (fun z : ((pullbackFunctor g).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            (X.presheaf) (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).obj
            (M)).obj (N)))).val.obj (op V) =>
      ((pullbackTensorSchemeIso g M N).hom ≫
          (AlgebraicGeometry.SheafOfModules.tensorIso X'.presheaf
            (isSheaf_structureRingPresheaf X') ((pullbackFunctor g).obj M)
            ((pullbackFunctor g).obj N)).inv).val.app (op V) z)
    (Stacks.SheafOfModules.hom_val_app_inv_val_app
      ((pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
        (isSheaf_structureRingPresheaf X) M N)) (op V) x)

/-- **The pullback of the monoidal unit, on a section.** The crossing
`AlgebraicGeometry.SheafOfModules.unitIso` carries
`Stacks.ProjBundleInverseBaseChange.pullbackUnitMonoidalIso` to
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, which is where the pullback of a section of
the structure sheaf is computed. -/
public theorem pullbackUnitMonoidalIso_hom_val_app (V : X'.Opens)
    (x : ((Scheme.Modules.pullback g).obj (Scheme.unitModule X)).val.obj (op V)) :
    (pullbackUnitMonoidalIso g).hom.val.app (op V)
        (((pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
            (isSheaf_structureRingPresheaf X))).inv.val.app (op V) x) =
      (AlgebraicGeometry.SheafOfModules.unitIso X'.presheaf
            (isSheaf_structureRingPresheaf X')).inv.val.app (op V)
        ((Scheme.Modules.pullbackUnitIso g).hom.val.app (op V) x) :=
  congrArg
    (fun z : ((Scheme.Modules.pullback g).obj (Scheme.unitModule X)).val.obj (op V) =>
      ((Scheme.Modules.pullbackUnitIso g).hom ≫
          (AlgebraicGeometry.SheafOfModules.unitIso X'.presheaf
            (isSheaf_structureRingPresheaf X')).inv).val.app (op V) z)
    (Stacks.SheafOfModules.hom_val_app_inv_val_app
      ((pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
        (isSheaf_structureRingPresheaf X))) (op V) x)

/-- **Tag 01CD at the localized monoidal structure, on the pullback of a product section.** Under
`Stacks.ProjBundleInverseBaseChange.pullbackTensorIso`, the pullback to `V ≤ g⁻¹U` of the product
of `m` and `n` is the product of their pullbacks. -/
public theorem pullbackTensorIso_hom_pullbackSection_tensorSectionsAt (M N : Mods X)
    (U : X.Opens) (V : X'.Opens) (h : V ≤ g ⁻¹ᵁ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (pullbackTensorIso g M N).hom.val.app (op V)
        (((pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
            (isSheaf_structureRingPresheaf X) M N)).inv.val.app (op V)
          (Scheme.Modules.pullbackSection g
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
                Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
                (isSheaf_structureRingPresheaf X)⟩).obj (M)).obj (N))) U V h
            (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op U) M N m n))) =
      (AlgebraicGeometry.SheafOfModules.tensorIso X'.presheaf
            (isSheaf_structureRingPresheaf X') ((pullbackFunctor g).obj M)
            ((pullbackFunctor g).obj N)).inv.val.app (op V)
        (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op V)
          ((pullbackFunctor g).obj M) ((pullbackFunctor g).obj N)
          (Scheme.Modules.pullbackSection g M U V h m)
          (Scheme.Modules.pullbackSection g N U V h n)) :=
  Eq.trans
    (pullbackTensorIso_hom_val_app g M N V
      (Scheme.Modules.pullbackSection g
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            (X.presheaf) (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).obj
            (M)).obj (N))) U V h
        (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op U) M N m n)))
    (congrArg
      (fun z : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X'.presheaf) (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X')⟩).obj ((pullbackFunctor g).obj M)).obj
          ((pullbackFunctor g).obj N))).val.obj (op V) =>
        (AlgebraicGeometry.SheafOfModules.tensorIso X'.presheaf
              (isSheaf_structureRingPresheaf X') ((pullbackFunctor g).obj M)
              ((pullbackFunctor g).obj N)).inv.val.app (op V) z)
      (Stacks.ProjectiveBundleConormal.pullbackTensorComparison_pullbackSection_tensorSectionsAt
        g M N U V h m n))

end Scheme

/-! ### The comparison of two tensor inverses, on a section -/

section TensorInverseSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The evaluation normalisation of the comparison of two two-sided tensor inverses, read on a
section.** Let `h` and `k` be two-sided tensor inverses of one sheaf of modules `L`, and let `a`,
`b`, `c` be sections of `h.inv`, `L` and `k.inv` over an object `U` of the site. If the product
of `a` and `b` pairs to `1` under `h`'s right trivialisation, and the product of `b` and `c`
pairs to `1` under `k`'s left trivialisation, then
`Stacks.TensorPowers.TensorInverse.invIso h k` carries `c` back to `a`. Each pairing hypothesis
is stated after the crossing `Stacks.SheafOfModules.sheafifyUnitIso`, as an equation between
sections of the structure sheaf. -/
public theorem invIso_inv_val_app (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    (h k : TensorInverse L) (U : Cᵒᵖ)
    (a : h.inv.val.obj U) (b : L.val.obj U) (c : k.inv.val.obj U)
    (hab : (sheafifyUnitIso 𝒪 h𝒪).hom.val.app U
        (h.mulIso'.hom.val.app U
          ((tensorObjIso 𝒪 h𝒪 h.inv L).inv.val.app U
            (tensorSectionsAt 𝒪 h𝒪 U h.inv L a b))) = (1 : (structureSheaf 𝒪 h𝒪).obj.obj U))
    (hbc : (sheafifyUnitIso 𝒪 h𝒪).hom.val.app U
        (k.mulIso.hom.val.app U
          ((tensorObjIso 𝒪 h𝒪 L k.inv).inv.val.app U
            (tensorSectionsAt 𝒪 h𝒪 U L k.inv b c))) = (1 : (structureSheaf 𝒪 h𝒪).obj.obj U)) :
    (TensorInverse.invIso h k).inv.val.app U c = a := by
  have e1 : (TensorInverse.invIso h k).inv =
      ((((λ_ k.inv).inv ≫ (h.mulIso'.inv ▷ k.inv)) ≫ (α_ h.inv L k.inv).hom) ≫
        (h.inv ◁ k.mulIso.hom)) ≫ (ρ_ h.inv).hom := rfl
  have hinj : k.mulIso.hom.val.app U
        ((tensorObjIso 𝒪 h𝒪 L k.inv).inv.val.app U
          (tensorSectionsAt 𝒪 h𝒪 U L k.inv b c)) =
      h.mulIso'.hom.val.app U
        ((tensorObjIso 𝒪 h𝒪 h.inv L).inv.val.app U
          (tensorSectionsAt 𝒪 h𝒪 U h.inv L a b)) :=
    ((inv_val_app_hom_val_app (sheafifyUnitIso 𝒪 h𝒪) U _).symm.trans
      (congrArg ((sheafifyUnitIso 𝒪 h𝒪).inv.val.app U) (hbc.trans hab.symm))).trans
      (inv_val_app_hom_val_app (sheafifyUnitIso 𝒪 h𝒪) U _)
  have hmi : h.mulIso'.inv.val.app U
        (h.mulIso'.hom.val.app U
          ((tensorObjIso 𝒪 h𝒪 h.inv L).inv.val.app U
            (tensorSectionsAt 𝒪 h𝒪 U h.inv L a b))) =
      (tensorObjIso 𝒪 h𝒪 h.inv L).inv.val.app U
        (tensorSectionsAt 𝒪 h𝒪 U h.inv L a b) :=
    inv_val_app_hom_val_app h.mulIso' U _
  have s1 := tensorSectionsAt_sheafInternalHomLeftUnitor_inv_one 𝒪 h𝒪 k.inv U
    (h.mulIso'.hom.val.app U
      ((tensorObjIso 𝒪 h𝒪 h.inv L).inv.val.app U
        (tensorSectionsAt 𝒪 h𝒪 U h.inv L a b))) hab c
  have s2 := tensorSectionsAt_sheafInternalHomWhiskerRight 𝒪 h𝒪
    (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) k.inv U h.mulIso'.inv
    (h.mulIso'.hom.val.app U
      ((tensorObjIso 𝒪 h𝒪 h.inv L).inv.val.app U
        (tensorSectionsAt 𝒪 h𝒪 U h.inv L a b))) c
  have s3 := (tensorObjIsoLeft_inv_tensorSectionsAt 𝒪 h𝒪 h.inv L k.inv U
    (tensorSectionsAt 𝒪 h𝒪 U h.inv L a b) c).symm
  have s4 := tensorSectionsAt_sheafInternalHomAssociator 𝒪 h𝒪 h.inv L k.inv U a b c
  have s5 := tensorObjIsoRight_inv_tensorSectionsAt 𝒪 h𝒪 h.inv L k.inv U a
    (tensorSectionsAt 𝒪 h𝒪 U L k.inv b c)
  have s6 := tensorSectionsAt_sheafInternalHomWhiskerLeft 𝒪 h𝒪 h.inv (L ⊗ k.inv) U
    k.mulIso.hom a
    ((tensorObjIso 𝒪 h𝒪 L k.inv).inv.val.app U (tensorSectionsAt 𝒪 h𝒪 U L k.inv b c))
  have s7 := tensorSectionsAt_sheafInternalHomRightUnitor_one 𝒪 h𝒪 h.inv U a
    (h.mulIso'.hom.val.app U
      ((tensorObjIso 𝒪 h𝒪 h.inv L).inv.val.app U
        (tensorSectionsAt 𝒪 h𝒪 U h.inv L a b))) hab
  refine Eq.trans (congrArg (fun φ : k.inv ⟶ h.inv => φ.val.app U c) e1) ?_
  simp only [_root_.SheafOfModules.comp_val_app_apply, s1, s2, hmi, s3, s4, s5, s6, hinj, s7]

end TensorInverseSections

/-! ### The pairings of pulled-back and transported sections -/

section InverseBaseChangeSections

/-- The localized monoidal structure, at the `Stacks.ProjBundleInverseBaseChange.Mods` spelling
given by the explicit application of `Stacks.SheafInternalHom.monoidalCategory`. -/
@[instance_reducible] local instance modsMonoidalCategory (Z : Scheme.{u}) :
    MonoidalCategory (Mods Z) :=
  Stacks.SheafInternalHom.monoidalCategory Z.presheaf (isSheaf_structureRingPresheaf Z)

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (L : Mods X)
  [Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) L]

/-- The two crossings of a product section from the tensor product sheaf agree. -/
private theorem tensorIso_inv_val_app_tensorSectionsAt_eq {Z : Scheme.{u}} (M N : Mods Z)
    (U : Z.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (AlgebraicGeometry.SheafOfModules.tensorIso Z.presheaf
        (isSheaf_structureRingPresheaf Z) M N).inv.val.app (op U)
      (tensorSectionsAt Z.presheaf (isSheaf_structureRingPresheaf Z) (op U) M N m n) =
    (tensorObjIso Z.presheaf (isSheaf_structureRingPresheaf Z) M N).inv.val.app (op U)
      (tensorSectionsAt Z.presheaf (isSheaf_structureRingPresheaf Z) (op U) M N m n) := by
  rw [Stacks.SheafOfModules.Invertible.tensorIso_eq_tensorObjIso]
  rfl

/-- **The right trivialisation of the `(-1)`st power on a pair of sections pairing to `1`.** If
`w₀` and `b₀` pair to `1` under `Stacks.ProjBundleInverseBaseChange.negOneMulIso` read through
`Stacks.SheafOfModules.tensorObjIso`, then read through
`AlgebraicGeometry.SheafOfModules.tensorIso` the same product goes to the section of the monoidal
unit that `Stacks.SheafOfModules.sheafifyUnitIso` identifies with `1`. -/
public theorem negOneMulIso_hom_pairing_eq
    (V : X.Opens)
    (w₀ : (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)).val.obj (op V))
    (b₀ : L.val.obj (op V))
    (hup : (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).hom.val.app (op V)
        ((negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom.val.app (op V)
          ((tensorObjIso X.presheaf (isSheaf_structureRingPresheaf X)
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
                L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀))) =
      (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V))) :
    (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom.val.app (op V)
        ((AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
            (isSheaf_structureRingPresheaf X)
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
            L).inv.val.app (op V)
          (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀)) =
      (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).inv.val.app (op V)
        (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V)) := by
  rw [tensorIso_inv_val_app_tensorSectionsAt_eq]
  exact (inv_val_app_hom_val_app (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X))
    (op V) _).symm.trans (congrArg _ hup)

/-- **The pullback trivialisation read down to the unit comparison.** Tag 01CD inverted, followed
by the pullback along `g` of `Stacks.ProjBundleInverseBaseChange.negOneMulIso`, carries the
product of the pullbacks of `w₀` and `b₀` to the section that the pullback of
`Stacks.SheafOfModules.sheafifyUnitIso` identifies with the pullback of `1`, provided `w₀` and
`b₀` pair to `1`. -/
public theorem pullbackSection_negOneMulIso_hom_eq
    (V : X.Opens) (W : X'.Opens) (hWV : W ≤ g ⁻¹ᵁ V)
    (w₀ : (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)).val.obj (op V))
    (b₀ : L.val.obj (op V))
    (hup : (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).hom.val.app (op V)
        ((negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom.val.app (op V)
          ((tensorObjIso X.presheaf (isSheaf_structureRingPresheaf X)
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
                L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀))) =
      (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V))) :
    ((pullbackFunctor g).map
          (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom).val.app (op W)
        ((pullbackTensorIso g
              (tensorPower X.presheaf
                (isSheaf_structureRingPresheaf X) L (-1)) L).inv.val.app (op W)
          ((AlgebraicGeometry.SheafOfModules.tensorIso X'.presheaf
                (isSheaf_structureRingPresheaf X')
                ((pullbackFunctor g).obj
                  (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
                ((pullbackFunctor g).obj L)).inv.val.app (op W)
            (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W)
              ((pullbackFunctor g).obj
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
              ((pullbackFunctor g).obj L)
              (Scheme.Modules.pullbackSection g
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) V W hWV w₀)
              (Scheme.Modules.pullbackSection g L V W hWV b₀)))) =
      ((pullbackFunctor g).map
          (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).inv).val.app (op W)
        (Scheme.Modules.pullbackSection g
          (_root_.SheafOfModules.unit
            (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X))) V W hWV
          (1 : (structureSheaf X.presheaf
            (isSheaf_structureRingPresheaf X)).obj.obj (op V))) := by
  have hstep1 : (pullbackTensorIso g
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L).inv.val.app (op W)
        ((AlgebraicGeometry.SheafOfModules.tensorIso X'.presheaf
            (isSheaf_structureRingPresheaf X')
            ((pullbackFunctor g).obj
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
            ((pullbackFunctor g).obj L)).inv.val.app (op W)
          (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W)
            ((pullbackFunctor g).obj
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
            ((pullbackFunctor g).obj L)
            (Scheme.Modules.pullbackSection g
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) V W hWV w₀)
            (Scheme.Modules.pullbackSection g L V W hWV b₀))) =
      ((pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
          (isSheaf_structureRingPresheaf X)
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
          L)).inv.val.app (op W)
        (Scheme.Modules.pullbackSection g
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
              (isSheaf_structureRingPresheaf X)⟩).obj (tensorPower X.presheaf
              (isSheaf_structureRingPresheaf X) L (-1))).obj (L))) V W hWV
          (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀)) :=
    (congrArg (fun z : ((pullbackFunctor g).obj
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) ⊗
          (pullbackFunctor g).obj L).val.obj (op W) =>
        (pullbackTensorIso g
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
          L).inv.val.app (op W) z)
      (pullbackTensorIso_hom_pullbackSection_tensorSectionsAt g
        (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L V W hWV
        w₀ b₀)).symm.trans
      (inv_val_app_hom_val_app (pullbackTensorIso g
        (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L) (op W)
        (((pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
            (isSheaf_structureRingPresheaf X)
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
            L)).inv.val.app (op W)
          (Scheme.Modules.pullbackSection g
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
                Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
                (isSheaf_structureRingPresheaf X)⟩).obj (tensorPower X.presheaf
                (isSheaf_structureRingPresheaf X) L (-1))).obj (L))) V W hWV
            (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀))))
  have hstep2 : ((pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
          (isSheaf_structureRingPresheaf X)
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
          L)).inv.val.app (op W)
        (Scheme.Modules.pullbackSection g
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
              (isSheaf_structureRingPresheaf X)⟩).obj (tensorPower X.presheaf
              (isSheaf_structureRingPresheaf X) L (-1))).obj (L))) V W hWV
          (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀)) =
      Scheme.Modules.pullbackSection g
        ((tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1) ⊗ L : Mods X))
        V W hWV
        ((AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
            (isSheaf_structureRingPresheaf X)
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
            L).inv.val.app (op V)
          (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀)) :=
    Scheme.Modules.pullbackSection_naturality g
      (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf (isSheaf_structureRingPresheaf X)
        (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L).inv V W hWV
      (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
        (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀)
  have hstep3 : ((pullbackFunctor g).map
          (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom).val.app (op W)
        (Scheme.Modules.pullbackSection g
          ((tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1) ⊗ L : Mods X))
          V W hWV
          ((AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
              (isSheaf_structureRingPresheaf X)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
              L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀))) =
      Scheme.Modules.pullbackSection g (𝟙_ (Mods X)) V W hWV
        ((negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom.val.app (op V)
          ((AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
              (isSheaf_structureRingPresheaf X)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
              L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀))) :=
    Scheme.Modules.pullbackSection_naturality g
      (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom V W hWV
      ((AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
          (isSheaf_structureRingPresheaf X)
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
          L).inv.val.app (op V)
        (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀))
  have hstep5 : Scheme.Modules.pullbackSection g (𝟙_ (Mods X)) V W hWV
        ((sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).inv.val.app (op V)
          (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V))) =
      ((pullbackFunctor g).map
          (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).inv).val.app (op W)
        (Scheme.Modules.pullbackSection g
          (_root_.SheafOfModules.unit
            (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X))) V W hWV
          (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V))) :=
    (Scheme.Modules.pullbackSection_naturality g
      (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).inv V W hWV
      (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V))).symm
  exact (congrArg (fun y : ((pullbackFunctor g).obj
        ((tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1) ⊗
          L : Mods X))).val.obj (op W) =>
      ((pullbackFunctor g).map
        (negOneMulIso X.presheaf
          (isSheaf_structureRingPresheaf X) L).hom).val.app (op W) y)
    (hstep1.trans hstep2)).trans
    (hstep3.trans
      ((congrArg (fun y : (𝟙_ (Mods X)).val.obj (op V) =>
          Scheme.Modules.pullbackSection g (𝟙_ (Mods X)) V W hWV y)
        (negOneMulIso_hom_pairing_eq (L := L) (V := V) (w₀ := w₀) (b₀ := b₀) (hup := hup))).trans
        hstep5))


/-- **The right trivialisation of the pulled-back tensor inverse, split into its three steps on a
section.** `Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse`'s right trivialisation is
Tag 01CD inverted, then `g^*` of
`Stacks.ProjBundleInverseBaseChange.negOneMulIso`, then the pullback of the unit; this reads that
composite on the product of two pulled-back sections, the crossing of the source moved from
`Stacks.SheafOfModules.tensorObjIso` to `AlgebraicGeometry.SheafOfModules.tensorIso` by
`Stacks.SheafOfModules.Invertible.tensorIso_eq_tensorObjIso`. -/
public theorem pullbackTensorInverse_mulIso'_hom_split
    (V : X.Opens) (W : X'.Opens) (hWV : W ≤ g ⁻¹ᵁ V)
    (w₀ : (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)).val.obj (op V))
    (b₀ : L.val.obj (op V)) :
    (pullbackTensorInverse g L
          (negOneTensorInverse X.presheaf
            (isSheaf_structureRingPresheaf X) L)).mulIso'.hom.val.app (op W)
        ((tensorObjIso X'.presheaf (isSheaf_structureRingPresheaf X')
              ((pullbackFunctor g).obj
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
              ((pullbackFunctor g).obj L)).inv.val.app (op W)
          (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W)
            ((pullbackFunctor g).obj
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
            ((pullbackFunctor g).obj L)
            (Scheme.Modules.pullbackSection g
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) V W hWV w₀)
            (Scheme.Modules.pullbackSection g L V W hWV b₀))) =
      (pullbackUnitMonoidalIso g).hom.val.app (op W)
        (((pullbackFunctor g).map
              (negOneMulIso X.presheaf
                (isSheaf_structureRingPresheaf X) L).hom).val.app (op W)
          ((pullbackTensorIso g
                (tensorPower X.presheaf
                  (isSheaf_structureRingPresheaf X) L (-1)) L).inv.val.app (op W)
            ((AlgebraicGeometry.SheafOfModules.tensorIso X'.presheaf
                  (isSheaf_structureRingPresheaf X')
                  ((pullbackFunctor g).obj
                    (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
                  ((pullbackFunctor g).obj L)).inv.val.app (op W)
              (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W)
                ((pullbackFunctor g).obj
                  (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
                ((pullbackFunctor g).obj L)
                (Scheme.Modules.pullbackSection g
                  (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) V W hWV w₀)
                (Scheme.Modules.pullbackSection g L V W hWV b₀))))) := by
  have hsplit : (pullbackTensorInverse g L
        (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L)).mulIso'.hom =
      (pullbackTensorIso g
          (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L).inv ≫
        ((pullbackFunctor g).map
            (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom ≫
          (pullbackUnitMonoidalIso g).hom) := rfl
  rw [hsplit]
  refine ((_root_.SheafOfModules.comp_val_app_apply _ _ (op W) _).trans
    (_root_.SheafOfModules.comp_val_app_apply _ _ (op W) _)).trans ?_
  congr 3
  exact (tensorIso_inv_val_app_tensorSectionsAt_eq (Z := X') _ _ W _ _).symm

/-- **The pullback trivialisation of the inverse, on a pair of pulled-back sections.** Let `L` be
invertible on `X` and let `g : X' ⟶ X`. The right trivialisation of the pulled-back tensor
inverse `Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse` pairs the pullback of `w₀` with
the pullback of `b₀` to the pullback of the value that
`Stacks.ProjBundleInverseBaseChange.negOneMulIso` gives to `w₀` and `b₀` upstairs; so if that
value is `1` over `V`, the pairing downstairs is `1` over `W`. -/
public theorem pullbackTensorInverse_mulIso'_hom_pullbackSection
    (V : X.Opens) (W : X'.Opens) (hWV : W ≤ g ⁻¹ᵁ V)
    (w₀ : (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)).val.obj (op V))
    (b₀ : L.val.obj (op V))
    (hup : (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).hom.val.app (op V)
        ((negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom.val.app (op V)
          ((tensorObjIso X.presheaf (isSheaf_structureRingPresheaf X)
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
                L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀))) =
      (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V))) :
    (sheafifyUnitIso X'.presheaf (isSheaf_structureRingPresheaf X')).hom.val.app (op W)
        ((pullbackTensorInverse g L
              (negOneTensorInverse X.presheaf
                (isSheaf_structureRingPresheaf X) L)).mulIso'.hom.val.app (op W)
          ((tensorObjIso X'.presheaf (isSheaf_structureRingPresheaf X')
                ((pullbackFunctor g).obj
                  (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
                ((pullbackFunctor g).obj L)).inv.val.app (op W)
            (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W)
              ((pullbackFunctor g).obj
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
              ((pullbackFunctor g).obj L)
              (Scheme.Modules.pullbackSection g
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) V W hWV w₀)
              (Scheme.Modules.pullbackSection g L V W hWV b₀)))) =
      (1 : (structureSheaf X'.presheaf (isSheaf_structureRingPresheaf X')).obj.obj (op W)) := by
  have hstep6 := pullbackUnitMonoidalIso_hom_val_app g W
    (Scheme.Modules.pullbackSection g
      (_root_.SheafOfModules.unit
        (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X))) V W hWV
      (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V)))
  have hone0 : g.appLE V W hWV
        (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V)) =
      (1 : (structureSheaf X'.presheaf (isSheaf_structureRingPresheaf X')).obj.obj (op W)) :=
    map_one _
  have hstep7 : (sheafifyUnitIso X'.presheaf
          (isSheaf_structureRingPresheaf X')).hom.val.app (op W)
        ((AlgebraicGeometry.SheafOfModules.unitIso X'.presheaf
            (isSheaf_structureRingPresheaf X')).inv.val.app (op W)
          ((Scheme.Modules.pullbackUnitIso g).hom.val.app (op W)
            (Scheme.Modules.pullbackSection g
              (_root_.SheafOfModules.unit
                (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X))) V W hWV
              (1 : (structureSheaf X.presheaf
                (isSheaf_structureRingPresheaf X)).obj.obj (op V))))) =
      (1 : (structureSheaf X'.presheaf (isSheaf_structureRingPresheaf X')).obj.obj (op W)) :=
    (hom_val_app_inv_val_app
        (sheafifyUnitIso X'.presheaf (isSheaf_structureRingPresheaf X')) (op W)
        ((Scheme.Modules.pullbackUnitIso g).hom.val.app (op W)
          (Scheme.Modules.pullbackSection g
            (_root_.SheafOfModules.unit
              (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X))) V W hWV
            (1 : (structureSheaf X.presheaf
              (isSheaf_structureRingPresheaf X)).obj.obj (op V))))).trans
      ((Stacks.ClosedSubscheme.pullbackUnitIso_hom_app_pullbackSect g V W hWV
          (1 : (structureSheaf X.presheaf
            (isSheaf_structureRingPresheaf X)).obj.obj (op V))).trans hone0)
  refine Eq.trans (congrArg (fun z : (𝟙_ (Mods X')).val.obj (op W) =>
      (sheafifyUnitIso X'.presheaf (isSheaf_structureRingPresheaf X')).hom.val.app (op W) z)
    (pullbackTensorInverse_mulIso'_hom_split (g := g) (L := L) (V := V) (W := W) (hWV := hWV)
      (w₀ := w₀) (b₀ := b₀))) ?_
  refine Eq.trans (congrArg (fun z : ((pullbackFunctor g).obj (𝟙_ (Mods X))).val.obj (op W) =>
      (sheafifyUnitIso X'.presheaf (isSheaf_structureRingPresheaf X')).hom.val.app (op W)
        ((pullbackUnitMonoidalIso g).hom.val.app (op W) z))
    (pullbackSection_negOneMulIso_hom_eq (g := g) (L := L) (V := V) (W := W) (hWV := hWV)
      (w₀ := w₀) (b₀ := b₀) (hup := hup))) ?_
  exact (congrArg (fun z : (𝟙_ (Mods X')).val.obj (op W) =>
      (sheafifyUnitIso X'.presheaf (isSheaf_structureRingPresheaf X')).hom.val.app (op W) z)
    hstep6).trans hstep7



omit [Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) L] in
/-- **The left trivialisation of a transported tensor inverse, on a product section.** For
`hL : L' ≅ g^*L`, the left trivialisation of `Stacks.TensorPowers.TensorInverse.ofIso hL.symm`
applied to the `(-1)`st power of `L'` is `Stacks.ProjBundleInverseBaseChange.negOneMulIso'` of
`L'` with the first factor carried across `hL`. -/
public theorem ofIso_mulIso_hom_tensorSectionsAt (L' : Mods X')
    [Stacks.SheafOfModules.IsInvertible X'.presheaf (isSheaf_structureRingPresheaf X') L']
    (hL : L' ≅ (pullbackFunctor g).obj L) (W : X'.Opens)
    (b : ((pullbackFunctor g).obj L).val.obj (op W))
    (c : (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1)).val.obj (op W)) :
    (TensorInverse.ofIso hL.symm
          (negOneTensorInverse X'.presheaf
            (isSheaf_structureRingPresheaf X') L')).mulIso.hom.val.app (op W)
        ((tensorObjIso X'.presheaf (isSheaf_structureRingPresheaf X')
              ((pullbackFunctor g).obj L)
              (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L'
                (-1))).inv.val.app (op W)
          (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W)
            ((pullbackFunctor g).obj L)
            (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1)) b c)) =
      (negOneMulIso' X'.presheaf (isSheaf_structureRingPresheaf X') L').hom.val.app (op W)
        ((tensorObjIso X'.presheaf (isSheaf_structureRingPresheaf X') L'
              (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L'
                (-1))).inv.val.app (op W)
          (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W) L'
            (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1))
            (hL.inv.val.app (op W) b) c)) := by
  have hsplit : (TensorInverse.ofIso hL.symm
        (negOneTensorInverse X'.presheaf (isSheaf_structureRingPresheaf X') L')).mulIso.hom =
      hL.inv ▷ tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1) ≫
        (negOneMulIso' X'.presheaf (isSheaf_structureRingPresheaf X') L').hom := rfl
  refine Eq.trans (congrArg (fun φ : (pullbackFunctor g).obj L ⊗
      tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1) ⟶ 𝟙_ (Mods X') =>
    φ.val.app (op W)
      ((tensorObjIso X'.presheaf (isSheaf_structureRingPresheaf X')
            ((pullbackFunctor g).obj L)
            (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L'
              (-1))).inv.val.app (op W)
        (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W)
          ((pullbackFunctor g).obj L)
          (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1)) b c)))
    hsplit) ?_
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ (op W) _) ?_
  exact congrArg (fun z : (L' ⊗
        tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1)).val.obj (op W) =>
      (negOneMulIso' X'.presheaf (isSheaf_structureRingPresheaf X') L').hom.val.app (op W) z)
    (tensorSectionsAt_sheafInternalHomWhiskerRight X'.presheaf
      (isSheaf_structureRingPresheaf X') ((pullbackFunctor g).obj L)
      (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1)) (op W) hL.inv b c)

/-- **Tag 0B3V's base change of the inverse, on a section.** For `hL : L' ≅ g^*L`, the comparison
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` carries a section `c` of
`(L')^{⊗ -1}` over `W` to the pullback of a section `w₀` of `L^{⊗ -1}` over `V`, as soon as there
is a section `b₀` of `L` over `V` with

* `hup`: `w₀` and `b₀` pair to `1` under the right trivialisation of `L^{⊗ -1}` upstairs, and
* `hdown`: the image of the pullback of `b₀` under `hL` pairs with `c` to `1` under the left
  trivialisation of `(L')^{⊗ -1}` downstairs. -/
public theorem inverseQuotientBaseChangeIso_inv_val_app (L' : Mods X')
    [Stacks.SheafOfModules.IsInvertible X'.presheaf (isSheaf_structureRingPresheaf X') L']
    (hL : L' ≅ (pullbackFunctor g).obj L)
    (V : X.Opens) (W : X'.Opens) (hWV : W ≤ g ⁻¹ᵁ V)
    (w₀ : (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)).val.obj (op V))
    (b₀ : L.val.obj (op V))
    (c : (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1)).val.obj (op W))
    (hup : (sheafifyUnitIso X.presheaf (isSheaf_structureRingPresheaf X)).hom.val.app (op V)
        ((negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom.val.app (op V)
          ((tensorObjIso X.presheaf (isSheaf_structureRingPresheaf X)
                (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1))
                L).inv.val.app (op V)
            (tensorSectionsAt X.presheaf (isSheaf_structureRingPresheaf X) (op V)
              (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L w₀ b₀))) =
      (1 : (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X)).obj.obj (op V)))
    (hdown : (sheafifyUnitIso X'.presheaf (isSheaf_structureRingPresheaf X')).hom.val.app (op W)
        ((negOneMulIso' X'.presheaf (isSheaf_structureRingPresheaf X') L').hom.val.app (op W)
          ((tensorObjIso X'.presheaf (isSheaf_structureRingPresheaf X') L'
                (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L'
                  (-1))).inv.val.app (op W)
            (tensorSectionsAt X'.presheaf (isSheaf_structureRingPresheaf X') (op W) L'
              (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1))
              (hL.inv.val.app (op W) (Scheme.Modules.pullbackSection g L V W hWV b₀)) c))) =
      (1 : (structureSheaf X'.presheaf (isSheaf_structureRingPresheaf X')).obj.obj (op W))) :
    (inverseQuotientBaseChangeIso g L L' hL).inv.val.app (op W) c =
      Scheme.Modules.pullbackSection g
        (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) V W hWV w₀ :=
  invIso_inv_val_app X'.presheaf (isSheaf_structureRingPresheaf X')
    ((pullbackFunctor g).obj L)
    (pullbackTensorInverse g L
      (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L))
    (TensorInverse.ofIso hL.symm
      (negOneTensorInverse X'.presheaf (isSheaf_structureRingPresheaf X') L'))
    (op W)
    (Scheme.Modules.pullbackSection g
      (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) V W hWV w₀)
    (Scheme.Modules.pullbackSection g L V W hWV b₀) c
    (pullbackTensorInverse_mulIso'_hom_pullbackSection g L V W hWV w₀ b₀ hup)
    ((congrArg (fun z : (𝟙_ (Mods X')).val.obj (op W) =>
        (sheafifyUnitIso X'.presheaf
          (isSheaf_structureRingPresheaf X')).hom.val.app (op W) z)
      (ofIso_mulIso_hom_tensorSectionsAt g L L' hL W
        (Scheme.Modules.pullbackSection g L V W hWV b₀) c)).trans hdown)

/-! ### The base change of the inverse twist on a section -/

section Hw

open Stacks.ProjectiveBundleSplitting (tautologicalTwist)
open Stacks.ProjectiveBundleConormal (bundle symPieces inverseTautologicalTwist
  inverseTwistBaseChangeIso)

variable {Y : Scheme.{u}} (E : Y.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient Y E) {σ : Y ⟶ (bundle E).scheme}
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)

/-- **The base change of the inverse twist, on a section.** The base-change comparison
`Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso` carries a section `w` of `𝓛^{⊗ -1}`
over `W` to the pullback along `σ` of a section `w₀` of `𝒪(-1)` over an open `V` of `𝐏(ℰ)`, as
soon as there is a section `b₀` of `𝒪(1)` over `V` with

* `hup`: `w₀` and `b₀` pair to `1` on `V` upstairs, and
* `hdown`: `e(σ^*b₀)` and `w` pair to `1` on `W` downstairs. -/
public theorem inverseTwistBaseChangeIso_inv_val_app
    (V : (bundle E).scheme.Opens) (W : Y.Opens) (hWV : W ≤ σ ⁻¹ᵁ V)
    (w₀ : (inverseTautologicalTwist E).val.obj (op V))
    (b₀ : (tautologicalTwist E (symPieces E)).val.obj (op V))
    (w : (Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
      Q.L (-1)).val.obj (op W))
    (hup : (sheafifyUnitIso (bundle E).scheme.presheaf
          (isSheaf_structureRingPresheaf (bundle E).scheme)).hom.val.app (op V)
        ((negOneMulIso (bundle E).scheme.presheaf
            (isSheaf_structureRingPresheaf (bundle E).scheme)
            (tautologicalTwist E (symPieces E))).hom.val.app (op V)
          ((tensorObjIso (bundle E).scheme.presheaf
              (isSheaf_structureRingPresheaf (bundle E).scheme)
              (inverseTautologicalTwist E)
              (tautologicalTwist E (symPieces E))).inv.val.app (op V)
            (tensorSectionsAt (bundle E).scheme.presheaf
              (isSheaf_structureRingPresheaf (bundle E).scheme) (op V)
              (inverseTautologicalTwist E) (tautologicalTwist E (symPieces E)) w₀ b₀))) =
      (1 : (structureSheaf (bundle E).scheme.presheaf
        (isSheaf_structureRingPresheaf (bundle E).scheme)).obj.obj (op V)))
    (hdown : (sheafifyUnitIso Y.presheaf (isSheaf_structureRingPresheaf Y)).hom.val.app (op W)
        ((negOneMulIso' Y.presheaf (isSheaf_structureRingPresheaf Y) Q.L).hom.val.app (op W)
          ((tensorObjIso Y.presheaf (isSheaf_structureRingPresheaf Y) Q.L
              (Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
                Q.L (-1))).inv.val.app (op W)
            (tensorSectionsAt Y.presheaf (isSheaf_structureRingPresheaf Y) (op W) Q.L
              (Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
                Q.L (-1))
              (e.hom.val.app (op W)
                (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
                  V W hWV b₀)) w))) =
      (1 : (structureSheaf Y.presheaf (isSheaf_structureRingPresheaf Y)).obj.obj (op W))) :
    (inverseTwistBaseChangeIso E Q e).inv.val.app (op W) w =
      Scheme.Modules.pullbackSection σ (inverseTautologicalTwist E) V W hWV w₀ :=
  inverseQuotientBaseChangeIso_inv_val_app σ (tautologicalTwist E (symPieces E)) Q.L e.symm
    V W hWV w₀ b₀ w hup hdown

end Hw

end InverseBaseChangeSections

end Stacks.ProjBundleInverseBaseChange

end

