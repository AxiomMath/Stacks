module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of quasi-coherent modules

The tensor product of two quasi-coherent modules on a ringed space is quasi-coherent. The
proof is local: a quasi-coherent module is locally presented by free modules, the tensor
product of two such presentations presents the tensor product, and presentations restrict to
an open.

## Main definitions

* `Stacks.SheafOfModules.TensorProduct.freeTensorIso` identifies the tensor product of two free
  sheaves of modules on a site with the free sheaf on the product of their index sets.
* `Stacks.SheafOfModules.TensorProduct.tensorPresentation` builds a presentation of a tensor
  product out of presentations of its two factors.
* `AlgebraicGeometry.presheafModuleRestriction` is the restriction of a presheaf of
  `𝒪_X`-modules to an open.
* `AlgebraicGeometry.tensorPresheafRestrictionIso` and
  `AlgebraicGeometry.tensorSheafRestrictionValIso` are the two pointwise comparisons out of which
  the restriction map on tensor products is built.
* `AlgebraicGeometry.tensorRestrictionPresheafHom` and `AlgebraicGeometry.tensorRestrictionMap`
  are the comparison morphism on presheaves and the morphism it induces on sheafifications.
* `AlgebraicGeometry.tensorRestrictionIso` identifies the restriction of a tensor product to an
  open with the tensor product formed on that open.

## Main results

* `AlgebraicGeometry.tensorSheaf_isQuasicoherent` is the instance asserting that
  quasi-coherence is preserved by the tensor product of sheaves of modules.
* `AlgebraicGeometry.toSheafify_tensorRestrictionMap` and
  `AlgebraicGeometry.tensorRestrictionIso_inv_val_app_toSheafify` read the comparison
  isomorphism on a section coming from the presheaf tensor product formed on the open; this is
  how a pure tensor of sections is identified with its image in the tensor product sheaf.

## Implementation notes

The tensor product is the sheafification of the sectionwise tensor-product presheaf, as
provided by `Stacks.SheafOfModules.Tensor.sheafTensor`. Quasi-coherence is
Mathlib's `SheafOfModules.IsQuasicoherent` predicate.

`freeTensorIso` and `tensorPresentation` are stated for an arbitrary site rather than for a
ringed space, since neither uses the topology of the underlying space; they live in
`Stacks.SheafOfModules.TensorProduct` for that reason, while the two restriction comparisons
and the instance itself are about a ringed space and live in `AlgebraicGeometry`.

The elaboration of `tensorRestrictionIso` has to identify the restriction of a presheaf tensor
product with the presheaf tensor product of the restrictions. That identification is definitional,
but the two sides are built by different routes —
  `Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor` by hand out of
`TensorProduct`, `PresheafOfModules.tensorObj` as the monoidal
  product `F ⊗ G` — so identifying them
as whole structures means comparing `PresheafOfModules.Monoidal.tensorObj` against
`TensorProduct.map` field by field under a binder. `tensorPresheafRestrictionIso` and
`tensorSheafRestrictionValIso` do the identification pointwise instead, where over each open both
sides are literally the same `TensorProduct`, and the comparison map of `tensorRestrictionIso` is
then a composite with them. Everything in this file elaborates within the default budget.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public section
open CategoryTheory MonoidalCategory Limits
open Stacks.SheafOfModules.TensorPresentations
universe v u w

namespace Stacks.SheafOfModules.TensorProduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max v u, w}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

set_option backward.isDefEq.respectTransparency false in
/-- Coproducts of presheaves of modules over the underlying ring sheaf, named directly so that
instance search does not have to find them through the sheaf-of-rings coercion. -/
instance (R : Sheaf J CommRingCat.{w}) :
    HasColimitsOfSize.{w, w} (PresheafOfModules.{w} (Tensor.ringSheaf R).obj) :=
  ⟨fun K _ => PresheafOfModules.hasColimitsOfShape _ K⟩

set_option backward.isDefEq.respectTransparency false in
/-- Coproducts of sheaves of modules over the underlying ring sheaf, named directly for the same
reason. -/
instance (R : Sheaf J CommRingCat.{w}) (K : Type w) :
    HasColimitsOfShape (Discrete K) (SheafOfModules.{w} (Tensor.ringSheaf R)) := by
  have : HasColimitsOfShape (Discrete K) (PresheafOfModules.{w} (Tensor.ringSheaf R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  exact SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    _ _

noncomputable def freeTensorIso (R : Sheaf J CommRingCat.{w}) (I K : Type w) :
    ((Tensor.sheafTensor.{u, v, w, w, w} R).obj
      (SheafOfModules.free (R := Tensor.ringSheaf R) I)).obj
        (SheafOfModules.free (R := Tensor.ringSheaf R) K) ≅
      SheafOfModules.free (R := Tensor.ringSheaf R) (I × K) := by
  let Rsh := Tensor.ringSheaf R
  let L :=
    (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (R)).obj (SheafOfModules.free (R := Rsh) I)
  haveI : PreservesColimitsOfSize.{w, w} L :=
    Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits J R _
  let e₁ : L.obj (SheafOfModules.free (R := Rsh) K) ≅
      ∐ fun (_ : K) => L.obj (SheafOfModules.unit Rsh) :=
    PreservesCoproduct.iso L (fun (_ : K) => SheafOfModules.unit Rsh)
  let e₂ : L.obj (SheafOfModules.unit Rsh) ≅ SheafOfModules.free (R := Rsh) I :=
    (PresheafOfModules.sheafification (R := Rsh) (𝟙 Rsh.obj)).mapIso
      (ρ_ (SheafOfModules.free (R := Rsh) I).val) ≪≫
      (asIso (PresheafOfModules.sheafificationAdjunction (R := Rsh) (𝟙 Rsh.obj)).counit).app _
  let e₃ : (∐ fun (_ : K) => SheafOfModules.free (R := Rsh) I) ≅
      SheafOfModules.free (R := Rsh) (K × I) := by
    let FF := SheafOfModules.freeFunctor (R := Rsh)
    let cop : FF.obj (∐ fun (_ : K) => I) ≅ ∐ fun (_ : K) => FF.obj I :=
      PreservesCoproduct.iso FF (fun (_ : K) => I)
    let et : (∐ fun (_ : K) => I) ≅ K × I :=
      CategoryTheory.Limits.Types.coproductIso (fun (_ : K) => I) ≪≫
        Equiv.toIso (Equiv.sigmaEquivProd K I)
    exact cop.symm ≪≫ FF.mapIso et
  exact e₁ ≪≫ Sigma.whiskerEquiv (Equiv.refl K) (fun _ => e₂.symm) ≪≫ e₃ ≪≫
    (SheafOfModules.freeFunctor (R := Rsh)).mapIso (Equiv.toIso (Equiv.prodComm K I))

noncomputable def tensorPresentation
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (P : F.Presentation) (Q : G.Presentation) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj (G))).Presentation := by
  let f₂ : SheafOfModules.free P.relations.I ⟶ SheafOfModules.free P.generators.I :=
    P.relations.π ≫ kernel.ι _
  let f₁ : SheafOfModules.free P.generators.I ⟶ F := P.generators.π
  let g₂ : SheafOfModules.free Q.relations.I ⟶ SheafOfModules.free Q.generators.I :=
    Q.relations.π ≫ kernel.ι _
  let g₁ : SheafOfModules.free Q.generators.I ⟶ G := Q.generators.π
  have hfzero : f₂ ≫ f₁ = 0 := by
    dsimp [f₂, f₁]
    rw [Category.assoc, kernel.condition, comp_zero]
  have hgzero : g₂ ≫ g₁ = 0 := by
    dsimp [g₂, g₁]
    rw [Category.assoc, kernel.condition, comp_zero]
  have hsF : (ShortComplex.mk f₂ f₁ hfzero).Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    convert P.isColimit using 1
  have hsG : (ShortComplex.mk g₂ g₁ hgzero).Exact := by
    apply ShortComplex.exact_of_g_is_cokernel
    convert Q.isColimit using 1
  have hf : (ComposableArrows.mk₂ f₂ f₁).Exact := hsF.exact_toComposableArrows
  have hg : (ComposableArrows.mk₂ g₂ g₁).Exact := hsG.exact_toComposableArrows
  letI : Epi f₁ := P.generators.epi
  letI : Epi g₁ := Q.generators.epi
  let coefficients : Sheaf J CommRingCat.{w} :=
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩
  let p := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} coefficients).map
      f₁).app (SheafOfModules.free Q.generators.I) ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} coefficients).obj F).map g₁
  let r := biprod.desc
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} coefficients).map f₂).app
      (SheafOfModules.free Q.generators.I))
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} coefficients).obj
      (SheafOfModules.free P.generators.I)).map g₂)
  have hExact := exact_tensorSheaf_presentations_on_site
    𝒪 h𝒪 f₂ f₁ g₂ g₁ hf hg
  have hZero : r ≫ p = 0 := by
    dsimp [r, p]
    exact hExact.zero 0
  have hEpi : Epi p := tensorSheafMapOnSite_epi 𝒪 h𝒪 f₁ g₁
  let eRel₁ := freeTensorIso (R := ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
    (forget₂ CommRingCat RingCat) h𝒪⟩) P.relations.I Q.generators.I
  let eRel₂ := freeTensorIso (R := ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
    (forget₂ CommRingCat RingCat) h𝒪⟩) P.generators.I Q.relations.I
  let eSum :
      (SheafOfModules.free (P.relations.I × Q.generators.I) :
          SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) ⊞
      SheafOfModules.free (P.generators.I × Q.relations.I) ≅
      SheafOfModules.free ((P.relations.I × Q.generators.I) ⊕ (P.generators.I × Q.relations.I)) :=
    biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso _ _
  let eRel := biprod.mapIso eRel₁ eRel₂ ≪≫ eSum
  let eTarget := freeTensorIso (R := ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
    (forget₂ CommRingCat RingCat) h𝒪⟩) P.generators.I Q.generators.I
  let f : SheafOfModules.free (R := TensorSheafification.structureSheaf 𝒪 h𝒪)
      ((P.relations.I × Q.generators.I) ⊕ (P.generators.I × Q.relations.I)) ⟶
      SheafOfModules.free (P.generators.I × Q.generators.I) :=
    eRel.inv ≫ r ≫ eTarget.hom
  let target : SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪) :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} coefficients).obj F).obj G
  let g : SheafOfModules.free (P.generators.I × Q.generators.I) ⟶ target :=
    eTarget.inv ≫ p
  have hfg : f ≫ g = 0 := by
    exact (Category.assoc eRel.inv (r ≫ eTarget.hom) (eTarget.inv ≫ p)).trans
      ((congrArg (fun morphism => eRel.inv ≫ morphism)
        (Category.assoc r eTarget.hom (eTarget.inv ≫ p))).trans
        ((congrArg (fun morphism => eRel.inv ≫ (r ≫ morphism))
          (eTarget.hom_inv_id_assoc p)).trans
          ((congrArg (fun morphism => eRel.inv ≫ morphism) hZero).trans (comp_zero))))
  have hCoker' : IsColimit (CokernelCofork.ofπ g hfg) := by
    let original : ShortComplex (SheafOfModules.{w}
        (TensorSheafification.structureSheaf 𝒪 h𝒪)) := ShortComplex.mk r p hZero
    let transported : ShortComplex (SheafOfModules.{w}
        (TensorSheafification.structureSheaf 𝒪 h𝒪)) := ShortComplex.mk f g hfg
    let comparison : original ≅ transported :=
      ShortComplex.isoMk eRel eTarget (Iso.refl _)
        (eRel.hom_inv_id_assoc (r ≫ eTarget.hom))
        ((eTarget.hom_inv_id_assoc p).trans (Category.comp_id p).symm)
    have transportedExact := (ShortComplex.exact_and_epi_g_iff_of_iso comparison).mp
      ⟨hExact.exact 0, hEpi⟩
    exact (transported.exact_and_epi_g_iff_g_is_cokernel.mp transportedExact).some
  exact SheafOfModules.presentationOfIsCokernelFree f g hfg hCoker'

end Stacks.SheafOfModules.TensorProduct

namespace AlgebraicGeometry
open TopologicalSpace Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules.TensorProduct

/-- Restriction to an open `U` of a presheaf of `𝒪_X`-modules: the pushforward of presheaves of
modules along `CategoryTheory.Over.forget U`.

The functor being pushed forward along is given explicitly, which is what makes the two
comparison isomorphisms below statable: written inline, the `F` of
`PresheafOfModules.pushforward` is a metavariable that only a type ascription on the resulting
morphism can fix, and that ascription is what used to force the comparison of the next lemma to
be performed on whole structures. -/
noncomputable def presheafModuleRestriction (X : AlgebraicGeometry.RingedSpace.{u, u})
    (U : Opens X.carrier) :
    PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj ⥤
      PresheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).over U).obj :=
  PresheafOfModules.pushforward (F := CategoryTheory.Over.forget U)
    (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).over U).obj)

/-- The presheaf tensor product on `U` of the restrictions of `F` and `G` is the restriction to
`U` of their presheaf tensor product.

The two sides are definitionally equal but built by different routes, so identifying them as
whole structures is expensive (see the implementation notes). Identifying them pointwise is
immediate — over each open both sides are the same `TensorProduct` — and `isoMk` then reduces
naturality to equalities of `ModuleCat` morphisms, which `cat_disch` discharges. -/
noncomputable def tensorPresheafRestrictionIso (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) :
    (PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((F.over U).val) ((G.over U).val)) ≅
      (presheafModuleRestriction X U).obj
        ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))) :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)

/-- The restriction to `U` of the underlying presheaf of modules of `F ⊗_{𝒪_X} G` is the
restriction of the sheafification of the presheaf tensor product. Pointwise for the same reason
as `tensorPresheafRestrictionIso`. -/
noncomputable def tensorSheafRestrictionValIso (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) :
    (presheafModuleRestriction X U).obj
        ((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
          ⋙
            PresheafOfModules.restrictScalars
              (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj)).obj
          ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X).obj
            ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))) ≅
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).over U).val :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)

/-- The comparison morphism from the presheaf tensor product formed on `U` to the restriction to
`U` of the tensor product sheaf: the restriction of the sheafification unit, pre- and
post-composed with the two pointwise identifications.

Ascribing the restricted sheafification unit directly to this type, without the two pointwise
identifications, is what made `tensorRestrictionIso` need an unbounded heartbeat budget: the
ascription performs both identifications on whole structures, and `Meta.letToHave` then performs
one of them a third time. -/
noncomputable def tensorRestrictionPresheafHom
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) :
    (PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((F.over U).val) ((G.over U).val)) ⟶
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).over U).val :=
  (tensorPresheafRestrictionIso X F G U).hom ≫
    (presheafModuleRestriction X U).map
      (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
        ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)))) ≫
    (tensorSheafRestrictionValIso X F G U).hom

/-- The morphism from the tensor product sheaf formed on `U` to the restriction to `U` of the
tensor product sheaf, obtained from `tensorRestrictionPresheafHom` by the sheafification
adjunction.  It is an isomorphism, and `tensorRestrictionIso` is its inverse. -/
noncomputable def tensorRestrictionMap
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X.sheaf.over U).obj, Presheaf.isSheaf_of_isSheaf_comp _ ((X.sheaf.over U).obj) (forget₂ CommRingCat RingCat) (((Presheaf.isSheaf_iff_isSheaf_comp
          ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
          (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property))⟩).obj ((F.over U))).obj ((G.over U))) ⟶
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).over U :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (X.sheaf.over U).obj
    ((Presheaf.isSheaf_iff_isSheaf_comp
      ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
      (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)).homEquiv _ _).symm
    (tensorRestrictionPresheafHom X F G U)

/-- The defining property of `tensorRestrictionMap`: composing it with the sheafification unit
recovers the comparison morphism on presheaves. -/
theorem toSheafify_tensorRestrictionMap
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) :
    Stacks.SheafOfModules.TensorSheafification.toSheafify (X.sheaf.over U).obj
        ((Presheaf.isSheaf_iff_isSheaf_comp
          ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
          (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)
        ((PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((F.over U).val) ((G.over U).val))) ≫
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          (X.sheaf.over U).obj
          ((Presheaf.isSheaf_iff_isSheaf_comp
            ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
            (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf (X.sheaf.over U).obj
            ((Presheaf.isSheaf_iff_isSheaf_comp
              ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
              (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)).obj)).map
        (tensorRestrictionMap X F G U) =
      tensorRestrictionPresheafHom X F G U := by
  let O := (X.sheaf.over U).obj
  let hO := (Presheaf.isSheaf_iff_isSheaf_comp ((Opens.grothendieckTopology X.carrier).over U) O
    (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property
  let P : PresheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O) :=
    (PresheafOfModules.tensorObj (O := O) ((F.over U).val) ((G.over U).val))
  let M := ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).over U
  let adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO
  let γ : P ⟶ M.val := tensorRestrictionPresheafHom X F G U
  let e : (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj P ⟶ M :=
    (adj.homEquiv P M).symm γ
  -- Stated as two fully-typed `have`s rather than a `calc`: inside `calc` the intermediate
  -- relation stays a metavariable and `Trans Eq Eq ?r` cannot be synthesised.
  have h1 : Stacks.SheafOfModules.TensorSheafification.toSheafify O hO P ≫
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).map e =
      (adj.homEquiv P M) e :=
    (adj.homEquiv_unit (f := e)).symm
  have h2 : (adj.homEquiv P M) e = γ := (adj.homEquiv P M).apply_symm_apply γ
  exact h1.trans h2

/-- `tensorRestrictionMap` is an isomorphism: the comparison morphism on presheaves is locally
bijective, so both it and the sheafification unit become isomorphisms after sheafification. -/
instance isIso_tensorRestrictionMap
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) : IsIso (tensorRestrictionMap X F G U) := by
  let J := Opens.grothendieckTopology X.carrier
  let JU := J.over U
  let O := (X.sheaf.over U).obj
  let hO := (Presheaf.isSheaf_iff_isSheaf_comp JU O
    (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property
  let P : PresheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O) :=
    (PresheafOfModules.tensorObj (O := O) ((F.over U).val) ((G.over U).val))
  let M := ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).over U
  let mid := (presheafModuleRestriction X U).map
    (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
      ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))
  let γ : P ⟶ M.val := (tensorPresheafRestrictionIso X F G U).hom ≫ mid ≫
    (tensorSheafRestrictionValIso X F G U).hom
  let η := Stacks.SheafOfModules.TensorSheafification.toSheafify O hO P
  let e : (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj P ⟶ M :=
    tensorRestrictionMap X F G U
  let forgetMap := (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf
    O hO) ⋙
    PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO).obj))
  have hecomp : η ≫ forgetMap.map e = γ := toSheafify_tensorRestrictionMap X F G U
  let toAbU := PresheafOfModules.toPresheaf
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj
  have sourceBijective : ∀ (sectionObj : (Over U)ᵒᵖ),
      Function.Bijective ((toAbU.map (tensorPresheafRestrictionIso X F G U).hom).app sectionObj) :=
    fun sectionObj => ConcreteCategory.bijective_of_isIso
      ((toAbU.mapIso (tensorPresheafRestrictionIso X F G U)).app sectionObj).hom
  have targetBijective : ∀ (sectionObj : (Over U)ᵒᵖ),
      Function.Bijective ((toAbU.map (tensorSheafRestrictionValIso X F G U).hom).app sectionObj) :=
    fun sectionObj => ConcreteCategory.bijective_of_isIso
      ((toAbU.mapIso (tensorSheafRestrictionValIso X F G U)).app sectionObj).hom
  have hmidI : Presheaf.IsLocallyInjective JU (toAbU.map mid) := by
    change Presheaf.IsLocallyInjective JU (Functor.whiskerLeft
      (CategoryTheory.Over.forget U).op
      ((PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj).map
        (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))))
    let : Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj).map
          (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
            ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))) := by
      change Presheaf.IsLocallyInjective J
        (CategoryTheory.toSheafify J
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))).presheaf)
      infer_instance
    exact Presheaf.isLocallyInjective_whisker JU J
      (CategoryTheory.Over.forget U) _
  have hmidS : Presheaf.IsLocallySurjective JU (toAbU.map mid) := by
    change Presheaf.IsLocallySurjective JU (Functor.whiskerLeft
      (CategoryTheory.Over.forget U).op
      ((PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj).map
        (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))))
    let : Presheaf.IsLocallySurjective J
        ((PresheafOfModules.toPresheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).obj).map
          (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
            ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))))) := by
      change Presheaf.IsLocallySurjective J
        (CategoryTheory.toSheafify J
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val))).presheaf)
      infer_instance
    exact Presheaf.isLocallySurjective_whisker JU J
      (CategoryTheory.Over.forget U) _
  -- Term mode with an explicitly applied `congrArg`: `rw [Functor.map_comp]` reports the
  -- pattern as absent here, the two `Category` instances on the index presheaf being reached
  -- by different routes.
  have hsplit : toAbU.map γ = toAbU.map (tensorPresheafRestrictionIso X F G U).hom ≫
      toAbU.map mid ≫ toAbU.map (tensorSheafRestrictionValIso X F G U).hom :=
    (toAbU.map_comp _ _).trans
      (congrArg (fun z => toAbU.map (tensorPresheafRestrictionIso X F G U).hom ≫ z)
        (toAbU.map_comp mid (tensorSheafRestrictionValIso X F G U).hom))
  have hγI : Presheaf.IsLocallyInjective JU (toAbU.map γ) := by
    have sourceInjective := Presheaf.isLocallyInjective_of_injective JU
      (toAbU.map (tensorPresheafRestrictionIso X F G U).hom)
      (fun sectionObj => (sourceBijective sectionObj).injective)
    have targetInjective := Presheaf.isLocallyInjective_of_injective JU
      (toAbU.map (tensorSheafRestrictionValIso X F G U).hom)
      (fun sectionObj => (targetBijective sectionObj).injective)
    have middleTargetInjective := @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ JU _ _ _
      (toAbU.map mid) (toAbU.map (tensorSheafRestrictionValIso X F G U).hom)
      hmidI targetInjective
    have composed := @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ JU _ _ _
      (toAbU.map (tensorPresheafRestrictionIso X F G U).hom)
      (toAbU.map mid ≫ toAbU.map (tensorSheafRestrictionValIso X F G U).hom)
      sourceInjective middleTargetInjective
    exact (congrArg (fun morphism => Presheaf.IsLocallyInjective JU morphism) hsplit).mpr composed
  have hγS : Presheaf.IsLocallySurjective JU (toAbU.map γ) := by
    have sourceSurjective := Presheaf.isLocallySurjective_of_surjective JU
      (toAbU.map (tensorPresheafRestrictionIso X F G U).hom)
      (fun sectionObj => (sourceBijective sectionObj).surjective)
    have targetSurjective := Presheaf.isLocallySurjective_of_surjective JU
      (toAbU.map (tensorSheafRestrictionValIso X F G U).hom)
      (fun sectionObj => (targetBijective sectionObj).surjective)
    have middleTargetSurjective := @Presheaf.isLocallySurjective_comp _ _ JU _ _ _ _ _ _ _ _ _
      (toAbU.map mid) (toAbU.map (tensorSheafRestrictionValIso X F G U).hom)
      hmidS targetSurjective
    have composed := @Presheaf.isLocallySurjective_comp _ _ JU _ _ _ _ _ _ _ _ _
      (toAbU.map (tensorPresheafRestrictionIso X F G U).hom)
      (toAbU.map mid ≫ toAbU.map (tensorSheafRestrictionValIso X F G U).hom)
      sourceSurjective middleTargetSurjective
    exact (congrArg (fun morphism => Presheaf.IsLocallySurjective JU morphism) hsplit).mpr composed
  let ηAb := toAbU.map η
  let γAb := toAbU.map γ
  let eAb := toAbU.map e.val
  have hηW : JU.W ηAb := by
    change JU.W (CategoryTheory.toSheafify JU P.presheaf)
    exact JU.W_toSheafify P.presheaf
  have hγW : JU.W γAb :=
    (JU.W_iff_isLocallyBijective γAb).2 ⟨hγI, hγS⟩
  have hηIso : IsIso ((presheafToSheaf JU AddCommGrpCat).map ηAb) :=
    (JU.W_iff ηAb).mp hηW
  have hγIso : IsIso ((presheafToSheaf JU AddCommGrpCat).map γAb) :=
    (JU.W_iff γAb).mp hγW
  have heMapIso : IsIso ((presheafToSheaf JU AddCommGrpCat).map eAb) := by
    have := hηIso
    have := hγIso
    have hcompAb : ηAb ≫ eAb = γAb := by
      change toAbU.map (η ≫ e.val) = toAbU.map γ
      convert congrArg (fun k => toAbU.map k) hecomp using 1 <;> rfl
    have hcomp : (presheafToSheaf JU AddCommGrpCat).map ηAb ≫
        (presheafToSheaf JU AddCommGrpCat).map eAb =
        (presheafToSheaf JU AddCommGrpCat).map γAb :=
      ((presheafToSheaf JU AddCommGrpCat).map_comp ηAb eAb).symm.trans
        (congrArg (presheafToSheaf JU AddCommGrpCat).map hcompAb)
    have : IsIso ((presheafToSheaf JU AddCommGrpCat).map ηAb ≫
        (presheafToSheaf JU AddCommGrpCat).map eAb) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((presheafToSheaf JU AddCommGrpCat).map ηAb)
      ((presheafToSheaf JU AddCommGrpCat).map eAb)
  have heW : JU.W eAb := (JU.W_iff eAb).2 heMapIso
  have heSheafIso : IsIso ((SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map e) := by
    apply (JU.W_sheafToPresheaf_map_iff_isIso _).1
    exact heW
  exact (isIso_iff_of_reflects_iso e
    (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).mp
      heSheafIso

/-- The restriction to an open `U` of the tensor product of two sheaves of modules is the tensor
product, formed on `U`, of their restrictions. -/
noncomputable def tensorRestrictionIso
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).over U ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X.sheaf.over U).obj, Presheaf.isSheaf_of_isSheaf_comp _ ((X.sheaf.over U).obj) (forget₂ CommRingCat RingCat) (((Presheaf.isSheaf_iff_isSheaf_comp
          ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
          (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property))⟩).obj ((F.over U))).obj ((G.over U))) :=
  (asIso (tensorRestrictionMap X F G U)).symm

/-- The inverse of `tensorRestrictionIso` is `tensorRestrictionMap`. -/
theorem tensorRestrictionIso_inv
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) :
    (tensorRestrictionIso X F G U).inv = tensorRestrictionMap X F G U := rfl

/-- The inverse of `tensorRestrictionIso`, read on a section coming from the presheaf tensor
product formed on `U`: it is the comparison morphism `tensorRestrictionPresheafHom`. -/
theorem tensorRestrictionIso_inv_val_app_toSheafify
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    (U : Opens X.carrier) (W : (CategoryTheory.Over U)ᵒᵖ)
    (t : ((PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((F.over U).val) ((G.over U).val))).obj W) :
    ((tensorRestrictionIso X F G U).inv.val.app W).hom
        (((Stacks.SheafOfModules.TensorSheafification.toSheafify (X.sheaf.over U).obj
            ((Presheaf.isSheaf_iff_isSheaf_comp
              ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
              (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)
            ((PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((F.over U).val) ((G.over U).val)))).app W).hom t) =
      ((tensorRestrictionPresheafHom X F G U).app W).hom t := by
  have h := congrArg (fun φ => (φ.app W).hom t) (toSheafify_tensorRestrictionMap X F G U)
  exact h

theorem tensor_isQC (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).IsQuasicoherent := by
  let qF : SheafOfModules.QuasicoherentData.{u, u, u, u} F :=
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)).some
  let qG : SheafOfModules.QuasicoherentData.{u, u, u, u} G :=
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := G)).some
  let J := Opens.grothendieckTopology X.carrier
  have hF : TopologicalSpace.IsOpenCover qF.X :=
    (Opens.coversTop_iff X.carrier qF.X).mp qF.coversTop
  have hG : TopologicalSpace.IsOpenCover qG.X :=
    (Opens.coversTop_iff X.carrier qG.X).mp qG.coversTop
  have hPair : J.CoversTop (fun ij : qF.I × qG.I => qF.X ij.1 ⊓ qG.X ij.2) := by
    rw [Opens.coversTop_iff X.carrier]
    apply top_unique
    intro x hx
    have hxF : x ∈ (⋃ i, (qF.X i : Set X.carrier)) := by simp [hF.iSup_set_eq_univ]
    have hxG : x ∈ (⋃ j, (qG.X j : Set X.carrier)) := by simp [hG.iSup_set_eq_univ]
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxF
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxG
    exact (Opens.mem_iSup).2 ⟨(i, j), ⟨hi, hj⟩⟩
  let qT : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).QuasicoherentData := {
    I := qF.I × qG.I
    X ij := qF.X ij.1 ⊓ qG.X ij.2
    coversTop := hPair
    presentation := fun ij => by
      let U := qF.X ij.1
      let V := qG.X ij.2
      let W := U ⊓ V
      have hWU : W ≤ U := inf_le_left
      have hWV : W ≤ V := inf_le_right
      let fU := SheafOfModules.overMap (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (homOfLE hWU)
      let gV := SheafOfModules.overMap (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (homOfLE hWV)
      haveI : PreservesColimitsOfSize fU := inferInstance
      haveI : PreservesColimitsOfSize gV := inferInstance
      let pF₀ := (qF.presentation ij.1).map fU
        (SheafOfModules.overMapUnitIso (R :=
          (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (homOfLE hWU))
      let pG₀ := (qG.presentation ij.2).map gV
        (SheafOfModules.overMapUnitIso (R :=
          (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (homOfLE hWV))
      let pF := pF₀.ofIsIso ((SheafOfModules.overFunctorMap
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (homOfLE hWU)).app
          F).hom
      let pG := pG₀.ofIsIso ((SheafOfModules.overFunctorMap
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (homOfLE hWV)).app
          G).hom
      let JW := J.over W
      let 𝒪 := (X.sheaf.over W).obj
      let h𝒪 := (Presheaf.isSheaf_iff_isSheaf_comp JW 𝒪
        (forget₂ CommRingCat RingCat)).mp (X.sheaf.over W).property
      let e := tensorRestrictionIso X F G W
      letI : IsIso e.symm.hom := e.symm.isIso_hom
      exact (tensorPresentation 𝒪 h𝒪 pF pG).ofIsIso
        e.symm.hom
  }
  exact qT.isQuasicoherent

/-- **Stacks Project, Tag 01CE.** The tensor product of two quasi-coherent
modules on a ringed space is quasi-coherent. -/
@[stacks 01CE "tensor_quasicoherent"]
instance tensorSheaf_isQuasicoherent
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).IsQuasicoherent := tensor_isQC
      X F G

end AlgebraicGeometry
