module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionPowerMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestrictOpen
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialize.Basic

/-!
# Multiplying an arbitrary module by a power of a nonvanishing section

Let `(X, 𝒪_X)` be a ringed space with local stalks, `L` an invertible `𝒪_X`-module and `s` a
global section of `L`. For every `𝒪_X`-module `ℱ`, every natural number `n` and every open
`W ⊆ X_s` inside the nonvanishing locus of `s`, the map

`Γ(W, ℱ) ⟶ Γ(W, ℱ ⊗ L ^⊗ n)`, `t ↦ t ⊗ (sⁿ)|_W`,

is **bijective**. The map is `Stacks.SheafOfModules.sectionPowerAction` applied to the morphism
`Stacks.SheafOfModules.sectionPowerHom` representing `sⁿ`, and the tensor product is the
sheafified one of Stacks Tag 01CA.

## Main definitions

* `Stacks.InverseSection.tensorSectionHom`: **multiplication by a global section**, for an
  arbitrary target module: the morphism `ℱ ⟶ ℱ ⊗ 𝒩` attached to a morphism `𝒪 ⟶ 𝒩`, namely the
  inverse of the right unit constraint followed by left whiskering. This is
  `Stacks.SheafOfModules.sectionPowerAction` with the target freed from the tensor powers, which
  is what the recursion defining `sⁿ` needs: its successor step whiskers by `L` itself and not by
  a power of `L`.

## Main results

* `Stacks.InverseSection.isIso_whiskerRestriction_map_tensorSectionHom`: **if a morphism
  `σ : 𝒪 ⟶ 𝒩` becomes an isomorphism after restriction along a continuous, cocontinuous functor
  of sites, so does multiplication by `σ`.** This is the passage from the objectwise tensor
  product to the sheafified one: the restriction of `ℱ ⊗ 𝒩` is `ℱ|_ ⊗ 𝒩|_` by
  `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso`, and under that identification
  multiplication by `σ` becomes the identity of `ℱ|_` tensored with `σ|_`, by
  `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality_right`. No formula on
  sections is needed, and none is proved.
* `Stacks.InverseSection.isIso_whiskerRestriction_map_sectionPowerHom`: **if multiplication by
  `s` becomes an isomorphism after restriction, so does the morphism representing `sⁿ`**, for
  every natural number `n`. The induction runs on the two rules `s⁰ = 𝟙` and `sⁿ⁺¹ = sⁿ ⊗ s`
  cutting out `Stacks.SheafOfModules.sectionPowerHom`, the successor step being the previous
  result.
* `Stacks.InverseSection.isIso_whiskerRestriction_map_of_bijective_app`: a morphism of sheaves of
  modules whose component at every object in the image of the functor of sites is bijective on
  sections restricts to an isomorphism.
* `Stacks.InverseSection.isIso_restrict_unitHomEquiv_symm`: **multiplication by `s` restricts to
  an isomorphism on every open inside the nonvanishing locus of `s`**, for restriction along the
  open-image functor of that open. This is
  `Stacks.NonvanishingTrivialize.isIso_over_of_le` at the site map for which the comparison of
  restriction with the tensor product is available.
* `Stacks.InverseSection.bijective_sectionPowerAction_app`: **the map
  `Γ(W, ℱ) → Γ(W, ℱ ⊗ L ^⊗ n)`, `t ↦ t ⊗ (sⁿ)|_W`, is bijective for an arbitrary module `ℱ`,
  an arbitrary natural number `n` and every open `W` inside the nonvanishing locus of `s`.**

## Implementation notes

**Everything is at the level of isomorphisms of sheaves of modules.** The bijectivity is read off
at the very end, from the component at the top open of the restricted site, which is the component
at `W` of the unrestricted morphism. In particular no section formula for a unitor of the
sheafified tensor product is used, and the only property of the comparison
`whiskerTensorSheafIso` that enters is its naturality in the second variable.

**`IsIso` is carried as an explicit hypothesis, never as an instance.** The comparison
isomorphism of a sheafified tensor product is read at a spelling of the structure sheaf whose
projection iota-reduces, so the sheaf of rings is not recoverable from the statement and instance
search fails even for `IsIso (𝟙 _)` in the categories occurring below.
`Stacks.InverseSection.isIso_comp`, `isIso_of_comp_right`, `isIso_map` and `isIso_of_eq` are
therefore Mathlib's corresponding instances restated over an abstract category with explicit
hypotheses; applied to a concrete morphism they fix the category by unification and need no
search. This is the same difficulty that
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyBijectiveUniqueness.lean` answers with its
explicit-argument `isoOfLocallyBijective`.

**The restriction is along the open-image functor `Opens W ⥤ Opens X`, not along the inclusion of
the slice `Over W ⥤ Opens X`.** Both are continuous and cocontinuous, so the comparison of
restriction with the tensor product is available for either. The slice is unusable here all the
same: the right-hand side of that comparison is a sheafification for the downstream topology, so
it needs `HasWeakSheafify (J.over W) AddCommGrpCat` and
`(J.over W).WEqualsLocallyBijective AddCommGrpCat`, and for `J` the topology of the opens of a
space neither of those is available. For the site of the opens of the
subspace both are automatic, which is why
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerRestrictOpen.lean` carries no such
hypothesis.

**The invertibility hypothesis is taken twice.** `Stacks.NonvanishingTrivialize.nonvanishingOpen`
is indexed by `AlgebraicGeometry.SheafOfModules.IsInvertible` and the tensor powers by
`(Stacks.SheafOfModules.TensorPower.tensorRightFunctor _ _ L).IsEquivalence`. The second follows
from the first by `Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible`, but
only as an explicitly applied term: instance search does not find it at the spelling of the
structure sheaf these statements are read at, so a statement mentioning both a nonvanishing open
and a tensor power has to carry both.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

universe v u v' u' v₂ u₂ v₃ u₃ w

open CategoryTheory TopologicalSpace Opposite MonoidalCategory AlgebraicGeometry
open scoped Stacks.NonvanishingTrivialize
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules.TensorPower
open Stacks.SheafOfModules (sectionPowerAction sectionPowerHom tensorLeftFunctorObjUnitIso)

namespace Stacks.InverseSection

/-! ### Isomorphy with explicit hypotheses

Mathlib's `IsIso` instances, restated over an abstract category with the `IsIso` hypotheses
explicit. See the implementation notes: in the categories of sheaves of modules occurring below
the sheaf of rings is not recoverable from a morphism's type, so instance search cannot be used.
-/

section Explicit

variable {D : Type u₂} [Category.{v₂} D]

/-- A composite of isomorphisms is an isomorphism. -/
theorem isIso_comp {A B E : D} {f : A ⟶ B} {g : B ⟶ E} (hf : IsIso f) (hg : IsIso g) :
    IsIso (f ≫ g) := by
  let _ := hf
  let _ := hg
  infer_instance

/-- A morphism whose composite with an isomorphism is an isomorphism is one. -/
theorem isIso_of_comp_right {A B E : D} {f : A ⟶ B} {g : B ⟶ E} (hg : IsIso g)
    (hfg : IsIso (f ≫ g)) : IsIso f := by
  let _ := hg
  let _ := hfg
  exact IsIso.of_isIso_comp_right f g

/-- A functor carries isomorphisms to isomorphisms. -/
theorem isIso_map {D' : Type u₃} [Category.{v₃} D'] (Fn : D ⥤ D') {A B : D} {f : A ⟶ B}
    (hf : IsIso f) : IsIso (Fn.map f) := by
  let _ := hf
  infer_instance

/-- Isomorphy transports along an equality of morphisms. -/
theorem isIso_of_eq {A B : D} {f g : A ⟶ B} (h : f = g) (hf : IsIso f) : IsIso g := h ▸ hf

/-- A functor carries a composite to an isomorphism if it does so for both factors. -/
private theorem isIso_map_comp {D' : Type u₃} [Category.{v₃} D'] (Fn : D ⥤ D') {A B E : D}
    {f : A ⟶ B} {g : B ⟶ E} (hf : IsIso (Fn.map f)) (hg : IsIso (Fn.map g)) :
    IsIso (Fn.map (f ≫ g)) :=
  isIso_of_eq (Fn.map_comp f g).symm (isIso_comp hf hg)

end Explicit

/-- A component of an isomorphism of sheaves of modules on a site is bijective on sections:
evaluation at an object is a functor, and isomorphisms in `ModuleCat` are bijective. -/
theorem bijective_val_app_of_isIso {C : Type u} [Category.{v} C] {K : GrothendieckTopology C}
    {R : Sheaf K RingCat.{w}} {M N : SheafOfModules.{w} R} (f : M ⟶ N) (hf : IsIso f) (Y : Cᵒᵖ) :
    Function.Bijective fun m : M.val.obj Y => f.val.app Y m := by
  let _ := hf
  exact (ConcreteCategory.isIso_iff_bijective ((SheafOfModules.evaluation R Y).map f)).mp
    inferInstance

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Multiplication by a global section**: the morphism `ℱ ⟶ ℱ ⊗ 𝒩` attached to a morphism
`σ : 𝒪 ⟶ 𝒩` out of the structure sheaf, namely the inverse of the right unit constraint followed
by left whiskering with `σ`. For `𝒩` a tensor power of an invertible module this is
`Stacks.SheafOfModules.sectionPowerAction`. -/
noncomputable def tensorSectionHom (F N : SheafOfModules.{w} (structureSheaf O hO))
    (σ : SheafOfModules.unit (structureSheaf O hO) ⟶ N) :
    F ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj F).obj N :=
  (tensorLeftFunctorObjUnitIso O hO F).inv ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj F).map σ

/-- Multiplication by the power of a section represented by `t : 𝒪 ⟶ L ^⊗ n` is multiplication
by `t` in the sense of `Stacks.InverseSection.tensorSectionHom`. -/
theorem sectionPowerAction_eq_tensorSectionHom
    (L : SheafOfModules.{w} (structureSheaf O hO))
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    (F : SheafOfModules.{w} (structureSheaf O hO)) (n : ℤ)
    (t : SheafOfModules.unit (structureSheaf O hO) ⟶ tensorPower O hO L n) :
    sectionPowerAction O hO L F n t = tensorSectionHom O hO F (tensorPower O hO L n) t := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- A component of a morphism of sheaves of modules is an isomorphism of abelian groups as soon
as it is bijective on sections. -/
theorem isIso_toPresheaf_app_of_bijective
    {M N : SheafOfModules.{w} (structureSheaf O hO)} (ψ : M ⟶ N) (Y : Cᵒᵖ)
    (h : Function.Bijective fun m : M.val.obj Y => ψ.val.app Y m) :
    IsIso (((PresheafOfModules.toPresheaf (structureSheaf O hO).obj).map
      ((SheafOfModules.forget (structureSheaf O hO)).map ψ)).app Y) := by
  rwa [← isIso_iff_of_reflects_iso _ (forget AddCommGrpCat.{w}), isIso_iff_bijective]

variable (H : C' ⥤ C) [H.IsContinuous J' J] [H.IsCocontinuous J' J]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J' AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] in
/-- **A morphism of sheaves of modules bijective on the sections over every object in the image
of a functor of sites restricts to an isomorphism along that functor.** The component of the
restriction at an object `Y` of the smaller site is the component of the original morphism at
`H.obj Y`, and isomorphy is reflected from presheaves of abelian groups through
`PresheafOfModules.toPresheaf` and `SheafOfModules.forget`. -/
theorem isIso_whiskerRestriction_map_of_bijective_app
    {M N : SheafOfModules.{w} (structureSheaf O hO)} (ψ : M ⟶ N)
    (h : ∀ Y : C', Function.Bijective fun m : M.val.obj (op (H.obj Y)) =>
      ψ.val.app (op (H.obj Y)) m) :
    IsIso ((whiskerRestriction (J' := J') O hO H).map ψ) := by
  have happ : ∀ Y : C'ᵒᵖ, IsIso (((PresheafOfModules.toPresheaf
      (structureSheaf (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)).obj).map
        ((SheafOfModules.forget
          (structureSheaf (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H))).map
            ((whiskerRestriction (J' := J') O hO H).map ψ))).app Y) := by
    intro Y
    change IsIso (((PresheafOfModules.toPresheaf (structureSheaf O hO).obj).map
      ((SheafOfModules.forget (structureSheaf O hO)).map ψ)).app (op (H.obj Y.unop)))
    exact isIso_toPresheaf_app_of_bijective O hO ψ _ (h Y.unop)
  have h2 : IsIso ((PresheafOfModules.toPresheaf
      (structureSheaf (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)).obj).map
        ((SheafOfModules.forget
          (structureSheaf (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H))).map
            ((whiskerRestriction (J' := J') O hO H).map ψ))) := NatIso.isIso_of_isIso_app _
  have h3 : IsIso ((SheafOfModules.forget
      (structureSheaf (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H))).map
        ((whiskerRestriction (J' := J') O hO H).map ψ)) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf
      (structureSheaf (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)).obj)
  exact isIso_of_reflects_iso _ (SheafOfModules.forget
    (structureSheaf (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)))

/-- **Multiplication by a morphism out of the structure sheaf that restricts to an isomorphism
restricts to an isomorphism.** Through the comparison of restriction with the tensor product,
multiplication by `σ` becomes the identity of the restricted module tensored with the restriction
of `σ`, which is an isomorphism; the right unit constraint contributes another. This is the
passage from the objectwise tensor product of sections to the sheafified tensor product. -/
theorem isIso_whiskerRestriction_map_tensorSectionHom
    (F N : SheafOfModules.{w} (structureSheaf O hO))
    (σ : SheafOfModules.unit (structureSheaf O hO) ⟶ N)
    (hσ : IsIso ((whiskerRestriction (J' := J') O hO H).map σ)) :
    IsIso ((whiskerRestriction (J' := J') O hO H).map (tensorSectionHom O hO F N σ)) := by
  have hr : IsIso ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨H.op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp _ (H.op ⋙ O) (forget₂ CommRingCat RingCat)
        (whiskerStructureIsSheaf (J' := J') O hO H)⟩)).map
      (((whiskerRestriction (J' := J') O hO H).map (𝟙 F),
        (whiskerRestriction (J' := J') O hO H).map σ) : (_, _) ⟶ (_, _))) :=
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
      ⟨H.op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp _ (H.op ⋙ O)
        (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩)).mapIso
          (((whiskerRestriction (J' := J') O hO H).mapIso (Iso.refl F)).prod
            (@asIso _ _ _ _ ((whiskerRestriction (J' := J') O hO H).map σ) hσ))).isIso_hom
  have key := whiskerTensorSheafIso_naturality_right (J' := J') O hO H F σ
  let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩
  have sourceIdentity := congrArg
    (fun transformation => transformation.app (SheafOfModules.unit (structureSheaf O hO)))
    (sourceTensor.map_id F)
  have sourceAction :=
    (congrArg (fun morphism => morphism ≫ (sourceTensor.obj F).map σ) sourceIdentity).trans
      (Category.id_comp ((sourceTensor.obj F).map σ))
  have normalizedKey := key.symm.trans (congrArg (fun morphism =>
    (whiskerRestriction (J' := J') O hO H).map morphism ≫
      (whiskerTensorSheafIso (J' := J') O hO H F N).hom) sourceAction)
  have hmap : IsIso ((whiskerRestriction (J' := J') O hO H).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj F).map
          σ)) :=
    isIso_of_comp_right (whiskerTensorSheafIso (J' := J') O hO H F N).isIso_hom
      (isIso_of_eq normalizedKey
        (isIso_comp (whiskerTensorSheafIso (J' := J') O hO H F
          (SheafOfModules.unit (structureSheaf O hO))).isIso_hom hr))
  exact isIso_map_comp (whiskerRestriction (J' := J') O hO H)
    (isIso_map (whiskerRestriction (J' := J') O hO H)
      (tensorLeftFunctorObjUnitIso O hO F).isIso_inv) hmap

variable (L : SheafOfModules.{w} (structureSheaf O hO))
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      L).IsEquivalence]

/-- **If multiplication by a global section `s` restricts to an isomorphism, so does the morphism
representing `sⁿ`.** The induction is on the two rules `s⁰ = 𝟙` and `sⁿ⁺¹ = sⁿ ⊗ s` cutting out
`Stacks.SheafOfModules.sectionPowerHom`: the successor step adjoins one copy of `s`, which is
multiplication by `s` on the `n`-th power followed by the comparison `L ^⊗ n ⊗ L ≅ L ^⊗ (n + 1)`,
so it restricts to an isomorphism by
`Stacks.InverseSection.isIso_whiskerRestriction_map_tensorSectionHom`. -/
theorem isIso_whiskerRestriction_map_sectionPowerHom (s : L.sections)
    (hs : IsIso ((whiskerRestriction (J' := J') O hO H).map (L.unitHomEquiv.symm s))) (n : ℕ) :
    IsIso ((whiskerRestriction (J' := J') O hO H).map (sectionPowerHom O hO L s n)) := by
  induction n with
  | zero =>
      exact isIso_of_eq
        (((whiskerRestriction (J' := J') O hO H).map_id
          (SheafOfModules.unit (structureSheaf O hO))).symm) (IsIso.id _)
  | succ n ih =>
      have hmid : IsIso ((whiskerRestriction (J' := J') O hO H).map
          (tensorSectionHom O hO (tensorPower O hO L n) L (L.unitHomEquiv.symm s))) :=
        isIso_whiskerRestriction_map_tensorSectionHom O hO H _ L _ hs
      have hstep : IsIso ((whiskerRestriction (J' := J') O hO H).map
          (tensorPowerSuccIso O hO L n).hom) :=
        isIso_map (whiskerRestriction (J' := J') O hO H) (tensorPowerSuccIso O hO L n).isIso_hom
      exact isIso_map_comp (whiskerRestriction (J' := J') O hO H) ih
        (isIso_map_comp (whiskerRestriction (J' := J') O hO H) hmid hstep)

/-- **Multiplication by `sⁿ` restricts to an isomorphism as soon as multiplication by `s`
does**, for an arbitrary module in the first factor. -/
theorem isIso_whiskerRestriction_map_sectionPowerAction (s : L.sections)
    (hs : IsIso ((whiskerRestriction (J' := J') O hO H).map (L.unitHomEquiv.symm s)))
    (F : SheafOfModules.{w} (structureSheaf O hO)) (n : ℕ) :
    IsIso ((whiskerRestriction (J' := J') O hO H).map
      (sectionPowerAction O hO L F n (sectionPowerHom O hO L s n))) :=
  isIso_whiskerRestriction_map_tensorSectionHom O hO H F _ _
    (isIso_whiskerRestriction_map_sectionPowerHom O hO H L s hs n)

end Site

section RingedSpace

variable (X : RingedSpace.{u, u})

variable (L : SheafOfModules.{u} (_root_.structureSheaf X.sheaf))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
    (_root_.structureSheaf X.sheaf).property L]
  [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- **Multiplication by a global section restricts to an isomorphism on every open inside its
nonvanishing locus**, for restriction along the open-image functor of that open. This is the
content of the trivialization clause of Stacks Tag 01CY -- `bijective_smul` -- read at the site
map for which restriction is known to commute with the tensor product;
`Stacks.NonvanishingTrivialize.isIso_over_of_le` is the same statement for the inclusion of the
slice. -/
theorem isIso_restrict_unitHomEquiv_symm (s : L.sections) {W : Opens (X : TopCat)}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    IsIso ((whiskerRestriction
        (J' := Opens.grothendieckTopology ((Opens.toTopCat (X : TopCat)).obj W))
        X.sheaf.obj (_root_.structureSheaf X.sheaf).property
        W.isOpenEmbedding.functor).map (L.unitHomEquiv.symm s)) := by
  refine isIso_whiskerRestriction_map_of_bijective_app X.sheaf.obj
    (_root_.structureSheaf X.sheaf).property W.isOpenEmbedding.functor _ fun V => ?_
  have hfun : (fun m : (SheafOfModules.unit (_root_.structureSheaf X.sheaf)).val.obj
      (op (W.isOpenEmbedding.functor.obj V)) =>
        (L.unitHomEquiv.symm s).val.app (op (W.isOpenEmbedding.functor.obj V)) m) =
      fun a : X.presheaf.obj (op (W.isOpenEmbedding.functor.obj V)) =>
        a • s.eval (op (W.isOpenEmbedding.functor.obj V)) :=
    funext fun a =>
      Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app s
        (W.isOpenEmbedding.functor.obj V) a
  exact Eq.mpr (congrArg Function.Bijective hfun)
    (Stacks.NonvanishingTrivialize.bijective_smul s
      ((Stacks.Cohomology.HigherDirectImage.isOpenEmbeddingFunctor_obj_le W V).trans hW))

variable [((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
  ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
    (_root_.structureSheaf X.sheaf).property⟩).flip.obj L).IsEquivalence]

/-- **For an arbitrary module `ℱ`, an arbitrary natural number `n` and every open `W` inside the
nonvanishing locus of `s`, the map `Γ(W, ℱ) → Γ(W, ℱ ⊗ L ^⊗ n)`, `t ↦ t ⊗ (sⁿ)|_W`, is
bijective.** The whole statement is read off from an isomorphism of sheaves of modules on the
open subspace `W`: multiplication by `s` restricts to an isomorphism there by
`Stacks.InverseSection.isIso_restrict_unitHomEquiv_symm`, hence so does the morphism representing
`sⁿ` and hence so does multiplication by it, and the component of the restricted morphism at the
top open of `W` is the component of the original morphism at `W`. -/
theorem bijective_sectionPowerAction_app (s : L.sections) {W : Opens (X : TopCat)}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s)
    (F : SheafOfModules.{u} (_root_.structureSheaf X.sheaf)) (n : ℕ) :
    Function.Bijective fun t : F.val.obj (op W) =>
      (sectionPowerAction X.sheaf.obj (_root_.structureSheaf X.sheaf).property L F n
        (sectionPowerHom X.sheaf.obj (_root_.structureSheaf X.sheaf).property L s n)).val.app
          (op W) t := by
  have hiso : IsIso ((whiskerRestriction
      (J' := Opens.grothendieckTopology ((Opens.toTopCat (X : TopCat)).obj W))
      X.sheaf.obj (_root_.structureSheaf X.sheaf).property W.isOpenEmbedding.functor).map
        (sectionPowerAction X.sheaf.obj (_root_.structureSheaf X.sheaf).property L F n
          (sectionPowerHom X.sheaf.obj (_root_.structureSheaf X.sheaf).property L s n))) :=
    isIso_whiskerRestriction_map_sectionPowerAction X.sheaf.obj
      (_root_.structureSheaf X.sheaf).property W.isOpenEmbedding.functor L s
      (isIso_restrict_unitHomEquiv_symm X L s hW) F n
  have hobj : Function.Bijective
      fun t : F.val.obj (op (W.isOpenEmbedding.functor.obj ⊤)) =>
        (sectionPowerAction X.sheaf.obj (_root_.structureSheaf X.sheaf).property L F n
          (sectionPowerHom X.sheaf.obj (_root_.structureSheaf X.sheaf).property L s n)).val.app
            (op (W.isOpenEmbedding.functor.obj ⊤)) t :=
    bijective_val_app_of_isIso _ hiso
      (op (⊤ : Opens ((Opens.toTopCat (X : TopCat)).obj W)))
  rwa [Opens.isOpenEmbedding_obj_top W] at hobj

end RingedSpace

end Stacks.InverseSection

end
