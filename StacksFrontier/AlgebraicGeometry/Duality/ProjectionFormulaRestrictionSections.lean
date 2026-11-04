module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaSections
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange

/-!
# Restriction to an open of a scheme, read on local sections

Let `j : X ⟶ Y` be an open immersion of schemes.  Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor j` is the *concrete* restriction of a sheaf of
modules: its sections over an open `W ⊆ X` are the sections of the original over `j(W)`.  The
*abstract* inverse image `AlgebraicGeometry.Scheme.Modules.pullback j` has no description on
sections at all — it is defined as a left adjoint — and the two are identified by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, which is produced by uniqueness
of left adjoints and is therefore equally opaque.

Three isomorphisms built on top of that identification are already in the library, and none of
them came with a description of its effect on sections:

* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` itself;
* `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`, that restriction to an
  open `V` of the target commutes with the direct image;
* `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`, that restriction to
  `f ⁻¹ᵁ V` commutes with the inverse image.

This file supplies those descriptions, together with the comparison of a restriction of a
tensor product with the tensor product of the restrictions and *its* description on sections.
They are what a statement about `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap`
needs in order to be made local on the base, because
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul` — the closed form
for that morphism, and `projectionFormulaMap_unique` the uniqueness clause that makes it
usable — is stated on local sections.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.RestrictionSections`.

* `restrictUnit_eq`: the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is, on
  sections over an open `U` of `Y`, the restriction map `M(U) ⟶ M(j(j⁻¹U))`.  (This is Mathlib's
  `restrictAdjunction_unit_app_app`, restated in the `PresheafOfModules.Hom.app` spelling the
  tensor-product development uses.)
* `exists_restrictUnit_eq`: that map is *surjective* when `U` is an open of the form `j(W)`,
  which is what lets a section of a restriction be written as a restricted section.
* `restrictUnit_naturality`: the restriction unit is natural in the module.
* `pullbackUnit_eq`: **the unit of `j^* ⊣ j_*` on sections.**  It is the restriction map above,
  followed by the comparison `restrictFunctorIsoPullback`.  Together with
  `restrictFunctorIsoPullback_inv_pullbackUnit` this is what makes the abstract inverse image
  along an open immersion computable.
* `restrictTensorIso` and `restrictTensorIso_hom_restrictUnit_unit_tmul`: **the restriction of a
  tensor product is the tensor product of the restrictions**, with its effect on the
  sheafification-unit image of a pure tensor: it carries the restriction of `x ⊗ y` to the
  tensor of the restrictions.
* `restrictPushforwardIso_hom_restrictUnit`: **the restriction-direct-image comparison on
  sections.**  Composed with the restriction unit it is again a restriction map of the module
  itself, along the unique morphism of opens of the source.
* `pullbackRestrictIso_hom_restrictUnit_pullbackUnit`: **the restriction-inverse-image
  comparison on the unit.**  It carries the restriction of `η y`, `η` the unit of `f^* ⊣ f_*`, to
  the image under the unit of `(f ∣_ V)^* ⊣ (f ∣_ V)_*` of the restriction of `y`.

## Implementation notes

Every statement here is about `AlgebraicGeometry.Scheme.Modules`, while the tensor product and
the pullback-tensor comparison of Stacks 01CD are stated for `SheafOfModules` over
`structureSheafRing` of the underlying ringed space.  The two spellings are
*definitionally equal* — `Scheme.Modules.pullback f = modulePullback f.toLRSHom.toShHom`,
`Scheme.Modules.pushforward f = modulePushforward f.toLRSHom.toShHom`,
`X.ringCatSheaf = structureSheafRing X.toRingedSpace` and
`Scheme.Modules.pullbackPushforwardAdjunction f = modulePullbackPushforwardAdjunction f` all
hold by `rfl` — but `AlgebraicGeometry.Scheme.Modules` is not reducible, so *instance search*
does not cross between them.  Accordingly `comparisonIsoApp` wraps the invertibility of the
comparison into an isomorphism on the `SheafOfModules` side, where `comparison_isIso` is
available, before it is used on the `Scheme.Modules` side.  The comparison's own effect on
sections is `Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul`, which is already in the
library; only its composite with the restriction comparison is new here.

For the same reason no proof below uses `rw` on an equation between sections: the element being
rewritten sits in a type spelled through `restrictScalars`, and the two spellings of the
category of modules are interchangeable only up to unfolding.  The proofs are chains of
`Eq.trans` and `congrArg`, which unify up to definitional equality.

The transports along equalities of opens — `j(j⁻¹(j(W))) = j(W)`,
`(f ⁻¹ᵁ V).ι(((f ∣_ V) ⁻¹ᵁ W)) = f ⁻¹ᵁ (V.ι(W))`,
`((f ∣_ V) ≫ V.ι) ⁻¹ᵁ U = ((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ U` — are all written as the restriction map
`M.val.map (homOfLE _).op` of the module along the *unique* morphism of opens between the two,
rather than as an `eqToHom` transport of the type of sections.  Opens of a space form a poset, so
`CategoryTheory.Subsingleton.elim` identifies that morphism with whatever `eqToHom` the library's
own construction produced, and restriction maps — unlike type transports — commute with every
morphism of modules by naturality.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction PresheafOfModules Stacks.RingedSpace
open Stacks.AlgebraicGeometry.AffinePushforward
open scoped TensorProduct
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.RestrictionSections

/-! ### Restriction maps along an equality of opens

The comparisons below are built from `CategoryTheory.eqToHom` transports along equalities of
opens.  Rather than transporting the *type* of a module of sections, every such step is written
as the restriction map of the module along the unique morphism between the two opens; the
lemmas here are what make that usable, namely that such a restriction map is invertible and
that it commutes with the sheafification unit of a tensor product. -/

section Transport

variable {X : Scheme.{u}}

/-- Two successive restriction maps of a module agree with any other restriction map between the
same opens, since opens form a poset. -/
private lemma val_map_val_map {N : X.Modules} {W₁ W₂ W₃ : X.Opens} (g : W₁ ⟶ W₂) (h : W₂ ⟶ W₃)
    (k : W₁ ⟶ W₃) (z : N.val.obj (op W₃)) :
    N.val.map g.op (N.val.map h.op z) = N.val.map k.op z :=
  (PresheafOfModules.map_comp_apply N.val h.op g.op z).symm.trans
    (PresheafOfModules.congr_map_apply N.val (Subsingleton.elim _ _) z)

/-- Restriction maps of a module along morphisms between two opens, in both directions,
compose to the identity, since opens form a poset. -/
private lemma val_map_val_map_self {N : X.Modules} {W₁ W₂ : X.Opens} (g : W₁ ⟶ W₂) (h : W₂ ⟶ W₁)
    (z : N.val.obj (op W₂)) : N.val.map h.op (N.val.map g.op z) = z :=
  (val_map_val_map h g (𝟙 _) z).trans (by simp; rfl)

/-- Applying two morphisms of modules in succession to a section is applying their composite, and
equal composites give equal results. -/
private lemma app_comp_eq {M N P : X.Modules} {a : M ⟶ N} {b : N ⟶ P} {c : M ⟶ P}
    (h : a ≫ b = c) (U : (Opens X)ᵒᵖ) (x : M.val.obj U) :
    Hom.app b.val U (Hom.app a.val U x) = Hom.app c.val U x := by
  subst h
  rfl

/-- The restriction map of a module along a morphism between two *equal* opens is split by the
restriction map along the reverse `eqToHom`.  Opens form a poset, so the given morphism is that
`eqToHom`, and the composite is the identity. -/
lemma val_map_eqToHom_val_map (N : X.Modules) {W₁ W₂ : X.Opens} (e : W₁ = W₂) (g : W₁ ⟶ W₂)
    (z : N.val.obj (op W₂)) :
    N.val.map (eqToHom e.symm).op (N.val.map g.op z) = z :=
  val_map_val_map_self g _ z

/-- The restriction map of a module along a morphism between two equal opens is injective.
This is how a section-level identity is transported from one spelling of an open to another. -/
lemma val_map_injective (N : X.Modules) {W₁ W₂ : X.Opens} (e : W₁ = W₂) (g : W₁ ⟶ W₂)
    {z z' : N.val.obj (op W₂)} (hz : N.val.map g.op z = N.val.map g.op z') : z = z' :=
  (val_map_eqToHom_val_map N e g z).symm.trans
    ((congrArg (N.val.map (eqToHom e.symm).op) hz).trans (val_map_eqToHom_val_map N e g z'))

end Transport

/-- The sheafification unit of a tensor product commutes with restriction: the restriction of
the unit image of a pure tensor is the unit image of the tensor of the restrictions. -/
lemma tensorSheafUnit_val_map {Z : RingedSpace.{u, u}}
    (A B : SheafOfModules.{u} (structureRingSheaf Z)) {U U' : (Opens Z.carrier)ᵒᵖ} (g : U ⟶ U')
    (a : A.val.obj U) (b : B.val.obj U) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩)).obj
        (A, B)).val.map g (Hom.app
        ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf Z)
        (𝟙 (Stacks.RingedSpace.structureRingSheaf Z).obj)).unit.app
        (PresheafOfModules.tensorObj (O := Z.presheaf) A.val B.val)) U (a ⊗ₜ b)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf Z)
          (𝟙 (Stacks.RingedSpace.structureRingSheaf Z).obj)).unit.app
          (PresheafOfModules.tensorObj (O := Z.presheaf) A.val B.val)) U'
          (A.val.map g a ⊗ₜ B.val.map g b) :=
  (PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf Z)
      (𝟙 (Stacks.RingedSpace.structureRingSheaf Z).obj)).unit.app
      (PresheafOfModules.tensorObj (O := Z.presheaf) A.val B.val)) g (a ⊗ₜ b)).symm.trans
    (congrArg (Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf Z)
        (𝟙 (Stacks.RingedSpace.structureRingSheaf Z).obj)).unit.app
        (PresheafOfModules.tensorObj (O := Z.presheaf) A.val B.val)) U')
        (tensorObj_restrictₛₗ_tmul g a b))

/-! ### The unit of the restriction adjunction -/

section OpenImmersion

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- The unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` on local sections: over an
open `U` of `Y` it is the restriction map `M(U) ⟶ M(j(j⁻¹U))`.

This is Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app` in the
`PresheafOfModules.Hom.app` spelling, which is the one the sheafified tensor product is stated
in; it holds by `rfl`. -/
lemma restrictUnit_eq (M : Y.Modules) (U : (Opens Y)ᵒᵖ) (x : M.val.obj U) :
    Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app M).val U x =
      M.val.map (homOfLE (j.image_preimage_le U.unop)).op x := rfl

/-- The image of the preimage of the image of an open is the image of that open. -/
lemma image_preimage_image (W : X.Opens) : j ''ᵁ (j ⁻¹ᵁ (j ''ᵁ W)) = j ''ᵁ W := by
  rw [j.preimage_image_eq]

/-- **A section of a restriction is a restricted section.**  Over an open `U` of `Y` which is
already the image of an open of `X` — equivalently, over an open contained in the range of `j`
— the restriction unit is surjective, because the restriction map `M(U) ⟶ M(j(j⁻¹U))` is then a
restriction map along an *equality* of opens.

This is the step that makes the uniqueness clause of a morphism out of a sheafified tensor
product usable after restriction: that clause quantifies over all sections of the restrictions,
and this writes each of them as the restriction of a section upstairs. -/
lemma exists_restrictUnit_eq (M : Y.Modules) (U : Y.Opens) (hU : j ''ᵁ (j ⁻¹ᵁ U) = U)
    (x' : ((Scheme.Modules.restrictFunctor j).obj M).val.obj (op (j ⁻¹ᵁ U))) :
    ∃ x : M.val.obj (op U),
      Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app M).val (op U) x = x' :=
  ⟨M.val.map (eqToHom hU.symm).op x', (restrictUnit_eq j M (op U) _).trans
    (val_map_val_map_self (N := M) _ _ x')⟩

/-- The restriction unit is natural in the module: restricting and then applying a morphism is
applying the morphism and then restricting. -/
lemma restrictUnit_naturality {M N : Y.Modules} (φ : M ⟶ N) (U : (Opens Y)ᵒᵖ)
    (x : M.val.obj U) :
    Hom.app ((Scheme.Modules.restrictFunctor j).map φ).val ((Opens.map j.base).op.obj U)
        (Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app M).val U x) =
      Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app N).val U (Hom.app φ.val U x) :=
  app_comp_eq ((Scheme.Modules.restrictAdjunction j).unit.naturality φ).symm U x

/-- **The unit of `j^* ⊣ j_*` on local sections, for an open immersion `j`.**  It is the
restriction map `M(U) ⟶ M(j(j⁻¹U))` followed by the comparison of the concrete restriction with
the abstract inverse image.

The inverse image `AlgebraicGeometry.Scheme.Modules.pullback j` is an abstract left adjoint and
has no sections of its own; this identity, obtained from
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, is the only handle on it. -/
lemma pullbackUnit_eq (M : Y.Modules) (U : (Opens Y)ᵒᵖ) (x : M.val.obj U) :
    pullbackUnit j.toLRSHom.toShHom M U x =
      Hom.app ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M).val
        ((Opens.map j.base).op.obj U)
        (Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app M).val U x) :=
  (app_comp_eq (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) M) U x).symm

/-- `pullbackUnit_eq` read backwards: the comparison of the inverse image with the concrete
restriction carries the unit of `j^* ⊣ j_*` to the restriction map. -/
lemma restrictFunctorIsoPullback_inv_pullbackUnit (M : Y.Modules) (U : (Opens Y)ᵒᵖ)
    (x : M.val.obj U) :
    Hom.app ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M).val
        ((Opens.map j.base).op.obj U) (pullbackUnit j.toLRSHom.toShHom M U x) =
      Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app M).val U x :=
  (congrArg (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M).val
    ((Opens.map j.base).op.obj U)) (pullbackUnit_eq j M U x)).trans
    (app_comp_eq ((Scheme.Modules.restrictFunctorIsoPullback j).hom_inv_id_app M) _ _)

end OpenImmersion

/-! ### The restriction of a tensor product -/

/-- Stacks 01CD for a morphism of ringed spaces, as an isomorphism at a fixed pair of modules.

This exists so that the invertibility of
`Stacks.RingedSpace.comparison`, which is available over
`structureSheafRing`, is packaged *before* the statement crosses into the
`AlgebraicGeometry.Scheme.Modules` spelling, where instance search would not find it. -/
def comparisonIsoApp {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (A B : SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).obj
        ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩)).obj (A, B)) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).obj
          ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B) :=
  haveI : IsIso (comparison f A B) := comparison_isIso f A B
  asIso (comparison f A B)

/-- The forward map of `comparisonIsoApp` is the canonical comparison of Stacks 01CD, rather
than an unspecified isomorphism of objects. -/
@[simp]
lemma comparisonIsoApp_hom {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (A B : SheafOfModules.{u} (structureRingSheaf Y)) :
    (comparisonIsoApp f A B).hom = comparison f A B := rfl

section Tensor

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- **The restriction of a tensor product to an open is the tensor product of the
restrictions.**  This is Stacks 01CD for the open immersion `j`, read through the comparison of
the abstract inverse image with the concrete restriction. -/
def restrictTensorIso (A B : Y.Modules) :
    (Scheme.Modules.restrictFunctor j).obj
        ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (A, B)) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.restrictFunctor j).obj A, (Scheme.Modules.restrictFunctor j).obj B) :=
  (Scheme.Modules.restrictFunctorIsoPullback j).app
      ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (A, B)) ≪≫
    comparisonIsoApp j.toLRSHom.toShHom A B ≪≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).mapIso
        (Iso.prod ((Scheme.Modules.restrictFunctorIsoPullback j).app A).symm
          ((Scheme.Modules.restrictFunctorIsoPullback j).app B).symm)

/-- **`restrictTensorIso` on local sections.**  It carries the restriction of the
sheafification-unit image of a pure tensor `x ⊗ y` to the sheafification-unit image of the
tensor of the restrictions of `x` and of `y`.

With `exists_restrictUnit_eq` this determines the comparison, since every section of a
restriction over an open of `X` is a restricted section. -/
lemma restrictTensorIso_hom_restrictUnit_unit_tmul (A B : Y.Modules) (U : (Opens Y)ᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    Hom.app (restrictTensorIso j A B).hom.val ((Opens.map j.base).op.obj U)
        (Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app
            ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (A, B))).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)
              (𝟙 (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj)).unit.app
              (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf) A.val B.val)) U
              (a ⊗ₜ b))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)
          (𝟙 (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj)).unit.app
          (PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf)
          ((Scheme.Modules.restrictFunctor j).obj A).val
          ((Scheme.Modules.restrictFunctor j).obj B).val)) ((Opens.map j.base).op.obj U)
        (Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app A).val U a ⊗ₜ
          Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app B).val U b) := by
  refine Eq.trans (PresheafOfModules.comp_app_apply
    ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (A, B))).val
    ((comparisonIsoApp j.toLRSHom.toShHom A B).hom ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (Iso.prod ((Scheme.Modules.restrictFunctorIsoPullback j).app A).symm
          ((Scheme.Modules.restrictFunctorIsoPullback j).app B).symm).hom).val _ _) ?_
  refine Eq.trans (congrArg _ (pullbackUnit_eq j
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (A, B)) U
    (Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)
        (𝟙 (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj)).unit.app
        (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf) A.val B.val)) U
        (a ⊗ₜ b))).symm) ?_
  refine Eq.trans (PresheafOfModules.comp_app_apply
    (comparisonIsoApp j.toLRSHom.toShHom A B).hom.val
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
      (Iso.prod ((Scheme.Modules.restrictFunctorIsoPullback j).app A).symm
        ((Scheme.Modules.restrictFunctorIsoPullback j).app B).symm).hom).val _ _) ?_
  refine Eq.trans (congrArg _ (Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul
    j.toLRSHom.toShHom A B U a b)) ?_
  refine Eq.trans (tensorSheaf_map_unit_tmul X.toRingedSpace
    ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app A)
    ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app B) _ _ _) ?_
  exact congrArg₂ (fun p q => Hom.app
      ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)
      (𝟙 (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj)).unit.app
      (PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf)
      ((Scheme.Modules.restrictFunctor j).obj A).val
      ((Scheme.Modules.restrictFunctor j).obj B).val)) ((Opens.map j.base).op.obj U) (p ⊗ₜ q))
    (restrictFunctorIsoPullback_inv_pullbackUnit j A U a)
    (restrictFunctorIsoPullback_inv_pullbackUnit j B U b)

/-- Sections maps of a restriction are sections maps of the module along the image of the
morphism of opens. -/
lemma restrictFunctor_val_map (M : Y.Modules) {W W' : X.Opens} (g : W' ⟶ W)
    (z : ((Scheme.Modules.restrictFunctor j).obj M).val.obj (op W)) :
    ((Scheme.Modules.restrictFunctor j).obj M).val.map g.op z =
      M.val.map (j.opensFunctor.map g).op z := rfl

/-- The restriction unit over an open of the form `j(W)`, as a restriction map of the
restriction itself.  The two opens `j⁻¹(j(W))` and `W` are equal and opens form a poset, so the
restriction map of `M` along `j(j⁻¹(j(W))) ≤ j(W)` is the restriction map of `M|_X` along the
corresponding `eqToHom`. -/
lemma restrictUnit_eq_val_map (M : Y.Modules) (W : X.Opens) (z : M.val.obj (op (j ''ᵁ W))) :
    Hom.app ((Scheme.Modules.restrictAdjunction j).unit.app M).val (op (j ''ᵁ W)) z =
      ((Scheme.Modules.restrictFunctor j).obj M).val.map
        (eqToHom (j.preimage_image_eq W)).op z :=
  (restrictUnit_eq j M (op (j ''ᵁ W)) z).trans
    (PresheafOfModules.congr_map_apply M.val (Subsingleton.elim _ _) z)

/-- **`restrictTensorIso` on local sections, with no transport.**  Over an open `W` of `X` the
sections of a restriction *are* the sections over `j(W)` upstairs, and the comparison is the
identity on sheafification-unit images of pure tensors in that reading. -/
lemma restrictTensorIso_hom_unit_tmul (A B : Y.Modules) (W : X.Opens)
    (a : A.val.obj (op (j ''ᵁ W))) (b : B.val.obj (op (j ''ᵁ W))) :
    Hom.app (restrictTensorIso j A B).hom.val (op W)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)
            (𝟙 (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj)).unit.app
            (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf) A.val B.val))
            (op (j ''ᵁ W)) (a ⊗ₜ b)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)
          (𝟙 (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj)).unit.app
          (PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf)
          ((Scheme.Modules.restrictFunctor j).obj A).val
          ((Scheme.Modules.restrictFunctor j).obj B).val)) (op W) (a ⊗ₜ b) := by
  refine val_map_injective _ (j.preimage_image_eq W) (eqToHom (j.preimage_image_eq W)) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply (restrictTensorIso j A B).hom.val
    (eqToHom (j.preimage_image_eq W)).op
    (Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)
        (𝟙 (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj)).unit.app
        (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf) A.val B.val)) (op (j ''ᵁ W))
        (a ⊗ₜ b))).symm ?_
  refine Eq.trans (congrArg (Hom.app (restrictTensorIso j A B).hom.val
      (op (j ⁻¹ᵁ (j ''ᵁ W))))
    (restrictUnit_eq_val_map j
        ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (A, B)) W
      (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)
          (𝟙 (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj)).unit.app
          (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf) A.val B.val)) (op (j ''ᵁ W))
          (a ⊗ₜ b))).symm) ?_
  refine Eq.trans (restrictTensorIso_hom_restrictUnit_unit_tmul j A B (op (j ''ᵁ W)) a b) ?_
  refine Eq.trans (congrArg₂
      (fun p q => Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)
      (𝟙 (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj)).unit.app
      (PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf)
      ((Scheme.Modules.restrictFunctor j).obj A).val
      ((Scheme.Modules.restrictFunctor j).obj B).val)) (op (j ⁻¹ᵁ (j ''ᵁ W))) (p ⊗ₜ q))
    (restrictUnit_eq_val_map j A W a) (restrictUnit_eq_val_map j B W b)) ?_
  exact (tensorSheafUnit_val_map ((Scheme.Modules.restrictFunctor j).obj A)
    ((Scheme.Modules.restrictFunctor j).obj B) (eqToHom (j.preimage_image_eq W)).op a b).symm

end Tensor

/-! ### The two restriction comparisons for a morphism over an open of the target -/

section Restrict

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- The image in `X` of the preimage under `f ∣_ V` of the preimage in `V` of an open `W` of `S`
is contained in `f ⁻¹ᵁ W`.  The two are in fact equal when `W ≤ V`; the inequality is all that
is needed to name the restriction map between the corresponding modules of sections. -/
lemma image_restrict_preimage_le (W : S.Opens) :
    (f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)) ≤ f ⁻¹ᵁ W := by
  rw [image_morphismRestrict_preimage f V (V.ι ⁻¹ᵁ W)]
  exact fun z hz => V.ι.image_preimage_le W hz

/-- **The restriction-direct-image comparison on local sections.**  Restricting a section of
`f_* M` over an open `W` of `S` to `V` and then applying
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` is the restriction map of `M`
itself, from `f ⁻¹ᵁ W` to the preimage of `W` inside `f ⁻¹ᵁ V`.

Both sides are restriction maps of `M` along morphisms of opens of `X` with the same source and
target, and opens form a poset, so they agree. -/
lemma restrictPushforwardIso_hom_restrictUnit (M : X.Modules) (W : S.Opens)
    (w : ((Scheme.Modules.pushforward f).obj M).val.obj (op W)) :
    Hom.app ((restrictPushforwardIso f V).hom.app M).val (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
          ((Scheme.Modules.pushforward f).obj M)).val (op W) w) =
      M.val.map (homOfLE (image_restrict_preimage_le f V W)).op w :=
  val_map_val_map (N := M) _ _ _ w

/-- The preimage of an open of `S` under `(f ⁻¹ᵁ V).ι ≫ f` and under `(f ∣_ V) ≫ V.ι` agree, the
two morphisms being equal by `AlgebraicGeometry.morphismRestrict_ι`. -/
lemma preimage_comp_le (W : S.Opens) :
    ((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ W ≤ ((f ∣_ V) ≫ V.ι) ⁻¹ᵁ W := by
  rw [morphismRestrict_ι]

/-- **The restriction-inverse-image comparison on the unit.**  Let `y` be a section of `H` over
an open `W` of `S` and `η` the unit of `f^* ⊣ f_*`.  Then
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` carries the restriction to
`f ⁻¹ᵁ V` of `η y` to the image, under the unit of `(f ∣_ V)^* ⊣ (f ∣_ V)_*`, of the restriction
of `y` to `V`.

Both `pullbackRestrictIso` and the two units are produced by uniqueness of left adjoints, so the
identity is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` for the two adjunctions
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictAdjunction` and
`restrictPullbackAdjunction`, whose units are the two composites above. -/
lemma pullbackRestrictIso_hom_restrictUnit_pullbackUnit (H : S.Modules) (W : S.Opens)
    (y : H.val.obj (op W)) :
    Hom.app ((pullbackRestrictIso f V).hom.app H).val (op (((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app
            ((Scheme.Modules.pullback f).obj H)).val (op (f ⁻¹ᵁ W))
          (pullbackUnit f.toLRSHom.toShHom H (op W) y)) =
      ((Scheme.Modules.pullback (f ∣_ V)).obj
            ((Scheme.Modules.restrictFunctor V.ι).obj H)).val.map
          (homOfLE (preimage_comp_le f V W)).op
        (pullbackUnit (f ∣_ V).toLRSHom.toShHom ((Scheme.Modules.restrictFunctor V.ι).obj H)
          (op (V.ι ⁻¹ᵁ W))
          (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app H).val (op W) y)) := by
  refine (app_comp_eq (Adjunction.unit_leftAdjointUniq_hom_app (pullbackRestrictAdjunction f V)
    ((restrictPullbackAdjunction f V).ofNatIsoRight
      (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V))) H) (op W) y).trans ?_
  refine (app_comp_eq (congrFun (congrArg NatTrans.app
    (Adjunction.ofNatIsoRight_unit (restrictPullbackAdjunction f V)
      (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)))).symm H) (op W) y).symm.trans ?_
  exact PresheafOfModules.congr_map_apply
    ((Scheme.Modules.pullback (f ∣_ V)).obj ((Scheme.Modules.restrictFunctor V.ι).obj H)).val
    (Subsingleton.elim _ _)
    (pullbackUnit (f ∣_ V).toLRSHom.toShHom ((Scheme.Modules.restrictFunctor V.ι).obj H)
      (op (V.ι ⁻¹ᵁ W)) (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app H).val (op W) y))

/-- `preimage_comp_le` as the equality of opens that it is. -/
lemma preimage_comp_eq (W : S.Opens) :
    ((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ W = ((f ∣_ V) ≫ V.ι) ⁻¹ᵁ W := by
  rw [morphismRestrict_ι]

/-- **The restriction-inverse-image comparison on the unit, with no transport.**  Over the
preimage in `f ⁻¹ᵁ V` of an open `W ∩ V` of `V`, the comparison carries the restriction of `η y`
to `η' y|_V`, where `η` and `η'` are the units of `f^* ⊣ f_*` and of
`(f ∣_ V)^* ⊣ (f ∣_ V)_*`. -/
lemma pullbackRestrictIso_hom_pullbackUnit (H : S.Modules) (W : S.Opens)
    (y : H.val.obj (op W)) :
    Hom.app ((pullbackRestrictIso f V).hom.app H).val (op ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)))
        (((Scheme.Modules.pullback f).obj H).val.map
            (homOfLE (image_restrict_preimage_le f V W)).op
          (pullbackUnit f.toLRSHom.toShHom H (op W) y)) =
      pullbackUnit (f ∣_ V).toLRSHom.toShHom ((Scheme.Modules.restrictFunctor V.ι).obj H)
        (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app H).val (op W) y) := by
  refine val_map_injective _ (preimage_comp_eq f V W) (homOfLE (preimage_comp_le f V W)) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    ((pullbackRestrictIso f V).hom.app H).val (homOfLE (preimage_comp_le f V W)).op
    (((Scheme.Modules.pullback f).obj H).val.map
        (homOfLE (image_restrict_preimage_le f V W)).op
      (pullbackUnit f.toLRSHom.toShHom H (op W) y))).symm ?_
  refine Eq.trans (congrArg (Hom.app ((pullbackRestrictIso f V).hom.app H).val
      (op (((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ W))) ?_)
    (pullbackRestrictIso_hom_restrictUnit_pullbackUnit f V H W y)
  refine Eq.trans (restrictFunctor_val_map (f ⁻¹ᵁ V).ι ((Scheme.Modules.pullback f).obj H)
    (homOfLE (preimage_comp_le f V W)) _) ?_
  refine Eq.trans (val_map_val_map (N := (Scheme.Modules.pullback f).obj H) _ _
    (homOfLE ((f ⁻¹ᵁ V).ι.image_preimage_le (f ⁻¹ᵁ W))) _) ?_
  exact (restrictUnit_eq (f ⁻¹ᵁ V).ι ((Scheme.Modules.pullback f).obj H) (op (f ⁻¹ᵁ W))
    (pullbackUnit f.toLRSHom.toShHom H (op W) y)).symm

end Restrict

end Stacks.AlgebraicGeometry.RestrictionSections

end
