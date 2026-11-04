module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassification
public import StacksFrontier.Deformation.RingedSpaceThickening.FlatCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Flat lifts across a strict morphism of first order thickenings

Let

```
X  --i-->  X'
|          |
f          f'
v          v
S  --t-->  S'
```

be a morphism of first order thickenings of ringed spaces, with ideal sheaf
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)`, and let `ℱ` be an `𝒪_X`-module. A *flat lift* of `ℱ` is a pair
`(ℱ', α)` consisting of an `𝒪_{X'}`-module `ℱ'` flat over `S'` and an isomorphism
`α : i^* ℱ' ≅ ℱ`. When the square is strict and `ℱ` is flat over `S`, the set of isomorphism
classes of such pairs is, if nonempty, principal homogeneous under
`Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`.

The ideal multiple `ℐℱ'` of a flat lift is `ℐ ⊗_{𝒪_X} ℱ`, so a flat lift becomes an extension

    0 ⟶ i_*(ℐ ⊗_{𝒪_X} ℱ) ⟶ ℱ' ⟶ i_* ℱ ⟶ 0

whose canonical map `c` is the identity. Two extensions with the same canonical map differ by
the class of exactly one extension whose middle term is a direct image, and such an extension
descends to an extension of `𝒪_X`-modules.

This file constructs the difference of two flat lifts, shows that it is well defined, and shows
that the resulting action is free.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.FlatLift`: a flat lift of `ℱ`, and
  `FlatLift.IsIsomorphic`, `flatLiftSetoid`, `FlatLiftClass`: their isomorphism classes.
* `AlgebraicGeometry.RingedSpaceThickening.FlatLift.reduction`: the canonical surjection
  `ℱ' ⟶ i_* ℱ` of a flat lift, and
  `AlgebraicGeometry.RingedSpaceThickening.FlatLift.kernelExtension`: the extension of `i_* ℱ`
  by `i_*(ℐ ⊗_{𝒪_X} ℱ)` it defines, with
  `AlgebraicGeometry.RingedSpaceThickening.FlatLift.IsKernelExtension` recording the
  normalization `c = 1`.
* `AlgebraicGeometry.RingedSpaceThickening.DifferencePresentation`: a presentation of the
  difference of two flat lifts, with
  `DifferencePresentation.differenceClass` its class in `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`, and
  `AlgebraicGeometry.RingedSpaceThickening.flatLiftDifference`: the difference of two flat
  lifts, and
  `AlgebraicGeometry.RingedSpaceThickening.flatLiftClassDifference`: the same read on
  isomorphism classes.

## Main results

* `CategoryTheory.Abelian.mapExactFunctor_injective_one` and
  `CategoryTheory.Abelian.existsUnique_mapExactFunctor_eq_of_essImage`: a fully faithful exact
  functor is injective on `Ext¹`, with the classes of extensions whose middle term lies in its
  essential image as its exact range. Specialized to a thickening in
  `AlgebraicGeometry.RingedSpaceThickening.existsUnique_ext_mapExactFunctor_eq`, this is the
  identification of the group through which **Stacks 08L7** acts with `Ext¹_{𝒪_X}(ℱ, 𝒦)`.
* `AlgebraicGeometry.RingedSpaceThickening.FlatLift.kernelExtension_action`: the kernel
  extension of a flat lift has canonical map the identity.
* `AlgebraicGeometry.RingedSpaceThickening.exists_differencePresentation`: **Stacks 08LM**, any
  two flat lifts admit a presentation of their difference.
* `AlgebraicGeometry.RingedSpaceThickening.flatLiftDifference_eq` and
  `AlgebraicGeometry.RingedSpaceThickening.existsUnique_differenceClass`: the difference is a
  well-defined class in `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`.
* `AlgebraicGeometry.RingedSpaceThickening.isIsomorphic_of_flatLiftDifference_eq_zero` and
  `AlgebraicGeometry.RingedSpaceThickening.flatLiftClassDifference_eq_zero_iff`: the action is
  free.

## Implementation notes

The classes by which two extensions with the same canonical map differ are classes in
`Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)` whose extensions have a direct image as middle term. They are
identified here with `Ext¹_{𝒪_X}(ℱ, 𝒦)`: the range is handled by `Ext.mapExactFunctor_extClass`
in one direction and by `CategoryTheory.Abelian.exists_shortExact_mapExactFunctor_extClass_eq` in
the other, and the injectivity comes from full faithfulness of `i_*` for a thickening, through the
fact that two extensions have the same class exactly when they are isomorphic over the identities.

A presentation of the difference carries the identification of its `𝒪_{X'}`-extension with the
direct image of its `𝒪_X`-extension as an isomorphism rather than as a bare morphism; a
morphism of short exact sequences which is the identity on both outer terms is an isomorphism
anyway.

## References

* [Stacks Project, Tag 08LM](https://stacks.math.columbia.edu/tag/08LM)
* [Stacks Project, Tag 08L7](https://stacks.math.columbia.edu/tag/08L7)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace CategoryTheory.Abelian

/-- Two short exact sequences with the same ends have the same class in `Ext¹` exactly when their
middle terms are isomorphic compatibly with the maps. -/
private theorem extClass_eq_iff_exists_iso {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A E E' B : C} {i : A ⟶ E} {p : E ⟶ B} {w : i ≫ p = 0} {i' : A ⟶ E'} {p' : E' ⟶ B}
    {w' : i' ≫ p' = 0} (h : (ShortComplex.mk i p w).ShortExact)
    (h' : (ShortComplex.mk i' p' w').ShortExact) :
    h.extClass = h'.extClass ↔ ∃ φ : E ≅ E', i ≫ φ.hom = i' ∧ φ.hom ≫ p' = p :=
  (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).2.1 _ _ _ _ _ _ _ _ h h'

section Descent

universe v v' w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type*} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  (P : C ⥤ D) [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
  [P.Full] [P.Faithful]

/-- **An extension whose middle term descends, descends, with its comparison.** For a fully
faithful exact functor `P`, a short exact sequence `0 ⟶ P A ⟶ H ⟶ P B ⟶ 0` with `H` in the
essential image of `P` is the image of a short exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`, through an
isomorphism `H ≅ P M` compatible with the maps, and the two have corresponding classes. -/
theorem exists_shortExact_comparison_mapExactFunctor_extClass_eq {A B : C} {H : D}
    {a : P.obj A ⟶ H} {b : H ⟶ P.obj B} {w₁ : a ≫ b = 0}
    (hS : (ShortComplex.mk a b w₁).ShortExact) (hH : P.essImage H) :
    ∃ (M : C) (f : A ⟶ M) (g : M ⟶ B) (w₀ : f ≫ g = 0)
      (h₀ : (ShortComplex.mk f g w₀).ShortExact) (c : H ≅ P.obj M),
      a ≫ c.hom = P.map f ∧ c.hom ≫ P.map g = b ∧
        h₀.extClass.mapExactFunctor P = hS.extClass := by
  obtain ⟨M, ⟨e⟩⟩ := hH
  have hf : P.map (P.preimage (a ≫ e.inv)) = a ≫ e.inv := P.map_preimage _
  have hg : P.map (P.preimage (e.hom ≫ b)) = e.hom ≫ b := P.map_preimage _
  have w₀ : P.preimage (a ≫ e.inv) ≫ P.preimage (e.hom ≫ b) = 0 := by
    apply P.map_injective
    simp only [P.map_comp, P.map_zero, hf, hg, Category.assoc, e.inv_hom_id_assoc, w₁]
  have hfe : P.map (P.preimage (a ≫ e.inv)) ≫ e.hom = a := by
    rw [hf, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hge : e.hom ≫ b = P.map (P.preimage (e.hom ≫ b)) := hg.symm
  have h₀ : (ShortComplex.mk (P.preimage (a ≫ e.inv)) (P.preimage (e.hom ≫ b)) w₀).ShortExact := by
    apply ShortExact.reflects_shortExact_of_faithful P
    refine ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := ShortComplex.mk a b w₁)
        (S₂ := (ShortComplex.mk (P.preimage (a ≫ e.inv)) (P.preimage (e.hom ≫ b)) w₀).map P)
        (Iso.refl _) e.symm (Iso.refl _) ?_ ?_) hS
    · simp
    · simp
  refine ⟨M, _, _, w₀, h₀, e.symm, hf.symm, ?_, ?_⟩
  · rw [Iso.symm_hom, hg, e.inv_hom_id_assoc]
  · rw [Abelian.Ext.mapExactFunctor_extClass]
    exact (extClass_eq_iff_exists_iso (h₀.map_of_exact P) hS).2 ⟨e, hfe, hge⟩

/-- **A fully faithful exact functor is injective on `Ext¹`.** -/
theorem mapExactFunctor_injective_one (A B : C) :
    Function.Injective fun ξ : Ext.{w} B A 1 => ξ.mapExactFunctor P := by
  intro ξ ζ h
  obtain ⟨E, a, b, w₁, hE, rfl⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).1 ξ
  obtain ⟨E', a', b', w₂, hE', rfl⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).1 ζ
  simp only [Ext.mapExactFunctor_extClass] at h
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    (extClass_eq_iff_exists_iso (hE.map_of_exact P) (hE'.map_of_exact P)).1 h
  let ψ : E ≅ E' := P.preimageIso φ
  have hψ : P.map ψ.hom = φ.hom := P.map_preimage _
  refine (extClass_eq_iff_exists_iso hE hE').2 ⟨ψ, P.map_injective ?_, P.map_injective ?_⟩
  · rw [P.map_comp, hψ]; exact hφ₁
  · rw [P.map_comp, hψ]; exact hφ₂

omit [P.Full] [P.Faithful] in
/-- **The image of a class is the class of an extension with descended middle term.** The image
of a class in `Ext¹` under an exact functor is the class of an extension whose middle term is in
the essential image of the functor. -/
theorem exists_yonedaExtension_essImage_extClass_eq_mapExactFunctor {A B : C}
    (ξ : Ext.{w} B A 1) :
    ∃ E : YonedaExtension (P.obj B) (P.obj A) 0,
      (YonedaExtension.shortExact E).extClass = ξ.mapExactFunctor P ∧ P.essImage E.Z.left := by
  obtain ⟨M, a, b, w₁, hE, rfl⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).1 ξ
  refine ⟨shortExactYonedaExtension (hE.map_of_exact P), ?_,
    Functor.obj_mem_essImage P M⟩
  rw [extClass_shortExactYonedaExtension, Ext.mapExactFunctor_extClass]

/-- **The classes with descended middle term are exactly the image of `Ext¹` of the source.**
A class whose extension has middle term in the essential image of a fully faithful exact
functor is the image of exactly one class. -/
theorem existsUnique_mapExactFunctor_eq_of_essImage {A B : C}
    (ξ' : Ext.{w} (P.obj B) (P.obj A) 1)
    (h : ∃ E : YonedaExtension (P.obj B) (P.obj A) 0,
      (YonedaExtension.shortExact E).extClass = ξ' ∧ P.essImage E.Z.left) :
    ∃! ξ : Ext.{w} B A 1, ξ.mapExactFunctor P = ξ' := by
  obtain ⟨E, hEcl, hEess⟩ := h
  obtain ⟨M, f, g, w₀, h₀, c, hcl, hcr, hmap⟩ :=
    exists_shortExact_comparison_mapExactFunctor_extClass_eq P
      (YonedaExtension.shortExact E) hEess
  exact ⟨h₀.extClass, hmap.trans hEcl, fun ζ hζ =>
    mapExactFunctor_injective_one P A B (hζ.trans (hmap.trans hEcl).symm)⟩

end Descent

section KernelExtension

universe v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The extension `0 ⟶ A ⟶ M ⟶ B' ⟶ 0` built from an epimorphism `q : M ⟶ B`, an
identification `e : A ≅ ker q` of its kernel and an identification `t : B ≅ B'` of its
target. -/
noncomputable def yonedaExtensionOfKernelIso {A M B B' : C} (q : M ⟶ B) [Epi q]
    (e : A ≅ Limits.kernel q) (t : B ≅ B') : YonedaExtension B' A 0 := by
  have hw : (e.hom ≫ Limits.kernel.ι q) ≫ q ≫ t.hom = 0 := by simp
  have hT : (ShortComplex.mk (e.hom ≫ Limits.kernel.ι q) (q ≫ t.hom) hw).ShortExact := by
    refine ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk
        (S₁ := ShortComplex.mk (Limits.kernel.ι q) q (Limits.kernel.condition q))
        (S₂ := ShortComplex.mk (e.hom ≫ Limits.kernel.ι q) (q ≫ t.hom) hw)
        e.symm (Iso.refl M) t (by simp) (by simp)) ?_
    exact { exact := ShortComplex.exact_kernel q }
  exact
    { Z := ComposableArrows.mk₀ M
      f := e.hom ≫ Limits.kernel.ι q
      g := q ≫ t.hom
      mono_f := hT.mono_f
      exact := ComposableArrows.exact₁ _
      exact_g := hT.exact.exact_toComposableArrows
      epi_g := hT.epi_g }

/-- The middle term of `CategoryTheory.Abelian.yonedaExtensionOfKernelIso` is the source of the
epimorphism it is built from. -/
theorem yonedaExtensionOfKernelIso_Z_left {A M B B' : C} (q : M ⟶ B) [Epi q]
    (e : A ≅ Limits.kernel q) (t : B ≅ B') :
    (yonedaExtensionOfKernelIso q e t).Z.left = M := rfl

/-- The injection of `CategoryTheory.Abelian.yonedaExtensionOfKernelIso` is the kernel
inclusion read through the given identification of the kernel. -/
theorem yonedaExtensionOfKernelIso_f {A M B B' : C} (q : M ⟶ B) [Epi q]
    (e : A ≅ Limits.kernel q) (t : B ≅ B') :
    (yonedaExtensionOfKernelIso q e t).f = e.hom ≫ Limits.kernel.ι q := rfl

/-- The surjection of `CategoryTheory.Abelian.yonedaExtensionOfKernelIso` is the given
epimorphism read through the given identification of its target. -/
theorem yonedaExtensionOfKernelIso_g {A M B B' : C} (q : M ⟶ B) [Epi q]
    (e : A ≅ Limits.kernel q) (t : B ≅ B') :
    (yonedaExtensionOfKernelIso q e t).g = q ≫ t.hom := rfl

end KernelExtension

end CategoryTheory.Abelian

namespace AlgebraicGeometry.RingedSpaceThickening

universe w

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-! ### The identification of the descended classes with `Ext¹` on the reduced space -/

section Identification

variable [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing X))]
  [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing X'))]
  [Limits.PreservesFiniteLimits (modulePushforward i)]
  [Limits.PreservesFiniteColimits (modulePushforward i)]
  (F K : SheafOfModules.{u} (structureSheafRing X))

/-- Every class in `Ext¹_{𝒪_X}(ℱ, 𝒦)` has an image under `i_*` which is the class of an
extension across the thickening whose middle term is a direct image. -/
theorem exists_yonedaExtension_essImage_extClass_eq_mapExactFunctor
    (ξ : CategoryTheory.Abelian.Ext.{w} F K 1) :
    ∃ D : CategoryTheory.Abelian.YonedaExtension
        ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
      (CategoryTheory.Abelian.YonedaExtension.shortExact D).extClass =
          ξ.mapExactFunctor (modulePushforward i) ∧
        (modulePushforward i).essImage D.Z.left :=
  CategoryTheory.Abelian.exists_yonedaExtension_essImage_extClass_eq_mapExactFunctor
    (modulePushforward i) ξ

/-- The classes in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)` whose extensions have a direct image as middle
term are exactly the images of `Ext¹_{𝒪_X}(ℱ, 𝒦)` under `i_*`, each attained by exactly one
class. -/
@[stacks 08L7 "the identification of the group of classes whose extensions have a direct image \
as middle term with `Ext¹_{𝒪_X}(ℱ, 𝒦)` itself: such a class is `i_*` of exactly one class on \
`X`. SCOPE: this clause only; the action of those classes is `exists_extClass_add_of_essImage` \
and the simple transitivity is \
`existsUnique_extClass_sub_of_firstOrderExtensionAction_eq`"]
theorem existsUnique_ext_mapExactFunctor_eq (hi : IsThickening i)
    (ξ' : CategoryTheory.Abelian.Ext.{w}
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 1)
    (h : ∃ D : CategoryTheory.Abelian.YonedaExtension
        ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
      (CategoryTheory.Abelian.YonedaExtension.shortExact D).extClass = ξ' ∧
        (modulePushforward i).essImage D.Z.left) :
    ∃! ξ : CategoryTheory.Abelian.Ext.{w} F K 1,
      ξ.mapExactFunctor (modulePushforward i) = ξ' := by
  have : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi).full_modulePushforward
  have : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi).faithful_modulePushforward
  exact CategoryTheory.Abelian.existsUnique_mapExactFunctor_eq_of_essImage
    (modulePushforward i) ξ' h

end Identification

/-! ### The ideal action on a flat lift -/

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The comparison `ℐ ⊗_{𝒪_{X'}} 𝒩 ⟶ i_*(i^* ℐ ⊗_{𝒪_X} ℱ)` of **Stacks 08L4** precomposed with
the tensor of a map `𝒩 ⟶ i_* ℱ`: it is the adjoint transpose of the **Stacks 01CD** comparison
followed by the tensor of the adjoint transpose of that map. -/
theorem tensorSheafMap_comp_extensionTensorComparison
    {M : SheafOfModules.{u} (structureSheafRing X')} {F : SheafOfModules.{u} (structureSheafRing X)}
    (g : M ⟶ (modulePushforward i).obj F) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
        (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), g) :
        ((AlgebraicGeometry.SheafOfModules.idealSheaf i), M) ⟶
        ((AlgebraicGeometry.SheafOfModules.idealSheaf i), ((modulePushforward i).obj F)))) ≫
        extensionTensorComparison i F =
      (modulePullbackPushforwardAdjunction i).homEquiv _ _
        ((Stacks.RingedSpace.comparisonBifunctorIso i).hom.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i, M) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)),
              (((modulePullbackPushforwardAdjunction i).homEquiv M F).symm g)) :
              ((idealSheafPullback i), ((modulePullback i).obj M)) ⟶
              ((idealSheafPullback i), F)))) := by
  have hL : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
      (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), g) :
      ((AlgebraicGeometry.SheafOfModules.idealSheaf i), M) ⟶
      ((AlgebraicGeometry.SheafOfModules.idealSheaf i), ((modulePushforward i).obj F)))) ≫
      extensionTensorComparison i F =
      (modulePullbackPushforwardAdjunction i).homEquiv _ _
        ((modulePullback i).map (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
            (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), g) :
            ((AlgebraicGeometry.SheafOfModules.idealSheaf i), M) ⟶
            ((AlgebraicGeometry.SheafOfModules.idealSheaf i), ((modulePushforward i).obj F))))) ≫
          ((Stacks.RingedSpace.comparisonBifunctorIso i).hom.app
              (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F) ≫
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)),
                ((modulePullbackPushforwardAdjunction i).counit.app F)) :
                ((idealSheafPullback i), ((modulePullback i).obj ((modulePushforward i).obj F))) ⟶
                ((idealSheafPullback i), F))))) :=
    ((modulePullbackPushforwardAdjunction i).homEquiv_naturality_left _ _).symm
  have hc : ((modulePullbackPushforwardAdjunction i).homEquiv M F).symm g =
      (modulePullback i).map g ≫ (modulePullbackPushforwardAdjunction i).counit.app F :=
    (modulePullbackPushforwardAdjunction i).homEquiv_counit M F g
  refine hL.trans (congrArg ((modulePullbackPushforwardAdjunction i).homEquiv _ _) ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
      (((𝟙 (idealSheafPullback i)), ((modulePullbackPushforwardAdjunction i).counit.app F)) :
      ((idealSheafPullback i), ((modulePullback i).obj ((modulePushforward i).obj F))) ⟶
      ((idealSheafPullback i), F))))
    (comparisonBifunctorIso_naturality_right i
      (AlgebraicGeometry.SheafOfModules.idealSheaf i) g)).trans ?_
  refine (comp_tensorSheafMap_comp_right (idealSheafPullback i) _ _ _).trans ?_
  exact congrArg (fun z => (Stacks.RingedSpace.comparisonBifunctorIso i).hom.app
      (AlgebraicGeometry.SheafOfModules.idealSheaf i, M) ≫
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)), z) :
        ((idealSheafPullback i), ((modulePullback i).obj M)) ⟶ ((idealSheafPullback i), F))))
        hc.symm

/-! ### Flat lifts and their kernel extensions -/

/-- The coefficient module `ℐ ⊗_{𝒪_X} ℱ`: the ideal of the upper thickening,
read as an `𝒪_X`-module by pullback along `i`, tensored over `𝒪_X` with `ℱ`. -/
noncomputable def idealTensor (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    SheafOfModules.{u} (structureSheafRing D.X) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩).obj
      ((idealSheafPullback D.i))).obj (F))

/-- The module `f^* 𝒥 ⊗_{𝒪_X} ℱ`: the ideal of the lower thickening, pulled back to `X`, tensored
over `𝒪_X` with `ℱ`. -/
noncomputable def baseIdealTensor (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    SheafOfModules.{u} (structureSheafRing D.X) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩).obj
      (((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ)))).obj (F))

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The canonical map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐ ⊗_{𝒪_X} ℱ`: the canonical ideal map of the square
read on the reduced source, tensored with the identity of `ℱ`. -/
noncomputable def baseIdealTensorComparison (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) : baseIdealTensor D F ⟶ idealTensor D F :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map ((D.baseToSourceIdeal, (𝟙 F)) :
      (((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ)), F) ⟶
      ((idealSheafPullback D.i), F)))

/-- The normalization `c = 1`, as a map
`ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_*(ℐ ⊗_{𝒪_X} ℱ)`: the comparison of **Stacks 08L4** attached to the
identity of `ℐ ⊗_{𝒪_X} ℱ`. -/
noncomputable def idealTensorAction (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    (idealTensorFunctor D.i).obj ((modulePushforward D.i).obj F) ⟶
      (modulePushforward D.i).obj (idealTensor D F) :=
  descendedActionOfMap D.i F (idealTensor D F) (𝟙 (idealTensor D F))

/-- The normalized comparison is the comparison of **Stacks 08L4** attached to the identity. -/
theorem idealTensorAction_eq (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    idealTensorAction D F =
      descendedActionOfMap D.i F (idealTensor D F) (𝟙 (idealTensor D F)) := rfl

/-- The normalized comparison is the comparison `extensionTensorComparison` itself. -/
private theorem idealTensorAction_eq_extensionTensorComparison (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    idealTensorAction D F = extensionTensorComparison D.i F :=
  (congrArg (fun z => extensionTensorComparison D.i F ≫ z)
    ((modulePushforward D.i).map_id (idealTensor D F))).trans (Category.comp_id _)

/-- **The comparison of Stacks 08L4 is an epimorphism.** -/
theorem epi_idealTensorAction (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) : Epi (idealTensorAction D F) := by
  have h : idealTensorAction D F =
      (modulePullbackPushforwardAdjunction D.i).unit.app
          ((idealTensorFunctor D.i).obj ((modulePushforward D.i).obj F)) ≫
        (modulePushforward D.i).map (extensionTensorIso D.i D.i_isThickening F).hom :=
    (idealTensorAction_eq_extensionTensorComparison D F).trans
      ((modulePullbackPushforwardAdjunction D.i).homEquiv_unit _ _ _)
  have hu := epi_unit_app_of_isThickening D.i D.i_isThickening
    ((idealTensorFunctor D.i).obj ((modulePushforward D.i).obj F))
  have hiso : IsIso ((modulePushforward D.i).map
      (extensionTensorIso D.i D.i_isThickening F).hom) :=
    ((modulePushforward D.i).mapIso (extensionTensorIso D.i D.i_isThickening F)).isIso_hom
  have hv : Epi ((modulePushforward D.i).map
      (extensionTensorIso D.i D.i_isThickening F).hom) := inferInstance
  rw [h]
  exact @epi_comp _ _ _ _ _ _ hu _ hv

/-- The factorization of the ideal action `ℐ ⊗_{𝒪_{X'}} 𝒩 ⟶ 𝒩` through the ideal multiple
`ℐ𝒩`, read as the kernel of the reduction by **Stacks 08LI**. -/
noncomputable def idealMultipleFactor (hi : IsThickening i)
    (M : SheafOfModules.{u} (structureSheafRing X')) :
    (idealTensorFunctor i).obj M ⟶ infinitesimalPart i M :=
  Abelian.factorThruImage (idealAction i M) ≫ (idealMultipleIso i hi M).1.hom

/-- The factorization of the ideal action through the ideal multiple recovers the ideal
action. -/
theorem idealMultipleFactor_comp_infinitesimalι (hi : IsThickening i)
    (M : SheafOfModules.{u} (structureSheafRing X')) :
    idealMultipleFactor i hi M ≫ infinitesimalι i M = (idealActionNatTrans i).app M :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => Abelian.factorThruImage (idealAction i M) ≫ z)
      (idealMultipleIso i hi M).2).trans (Abelian.image.fac _))

/-- The ideal action of **Stacks 08LI** read on the reduced space: the **Stacks 01CD**
comparison `i^*(ℐ ⊗_{𝒪_{X'}} 𝒩) ≅ i^* ℐ ⊗_{𝒪_X} i^* 𝒩` followed by the restriction of the
ideal action to `X`. -/
noncomputable def restrictedIdealAction (D : MorphismOfThickenings.{u})
    (M : SheafOfModules.{u} (structureSheafRing D.X')) :
    (modulePullback D.i).obj ((idealTensorFunctor D.i).obj M) ⟶
      infinitesimalPartOnSource D.i M :=
  (Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app (D.idealI, M) ≫
    sourceIdealActionImage D M

/-- The ideal action read on the reduced space is the restriction of the factorization of the
ideal action through the ideal multiple. -/
theorem restrictedIdealAction_eq (D : MorphismOfThickenings.{u})
    (M : SheafOfModules.{u} (structureSheafRing D.X')) :
    restrictedIdealAction D M =
      (modulePullback D.i).map (idealMultipleFactor D.i D.i_isThickening M) := by
  refine Eq.trans ?_ (Functor.map_comp _ _ _).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫
      ((modulePullback D.i).map (Abelian.factorThruImage (idealAction D.i M)) ≫
        (modulePullback D.i).map (idealMultipleIso D.i D.i_isThickening M).1.hom))
    ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom_inv_id_app (D.idealI, M))).trans ?_
  exact Category.id_comp _

/-- **The ideal action identifies `i^*(ℐ ⊗_{𝒪_{X'}} ℱ')` with the ideal multiple `ℐℱ'`.** For a
strict square and a module `ℱ'` on `X'` flat over `S'`, the ideal action read on the reduced
space is an isomorphism. -/
theorem isIso_restrictedIdealAction_of_isFlatOver (D : MorphismOfThickenings.{u})
    (hs : D.IsStrict) (M : SheafOfModules.{u} (structureSheafRing D.X'))
    (hM : AlgebraicGeometry.IsFlatOver D.f' M) : IsIso (restrictedIdealAction D M) := by
  have hp : Epi (baseToSourceIdealTensor D M) :=
    @AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi D.X _ _
      ((modulePullback D.i).obj M) D.baseToSourceIdeal (D.epi_baseToSourceIdeal hs)
  have hcomp : IsIso (baseToSourceIdealTensor D M ≫ sourceIdealActionImage D M) :=
    isIso_baseToInfinitesimal_of_isFlatOver D hs M hM
  have hmono : Mono (baseToSourceIdealTensor D M ≫ sourceIdealActionImage D M) :=
    ((isIso_iff_mono_and_epi _).mp hcomp).1
  have : Mono (baseToSourceIdealTensor D M) :=
    mono_of_mono (baseToSourceIdealTensor D M) (sourceIdealActionImage D M)
  have : IsIso (baseToSourceIdealTensor D M) := isIso_of_mono_of_epi _
  have ha : IsIso (sourceIdealActionImage D M) :=
    IsIso.of_isIso_comp_left (baseToSourceIdealTensor D M) (sourceIdealActionImage D M)
  have hcmp : IsIso ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app (D.idealI, M)) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hcmp ha

/-- A *flat lift* of an `𝒪_X`-module `ℱ` across the upper thickening of `D`: an
`𝒪_{X'}`-module flat over `S'` together with an identification of its restriction to `X`
with `ℱ`. -/
structure FlatLift (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) where
  /-- The lifted module on `X'`. -/
  module' : SheafOfModules.{u} (structureSheafRing D.X')
  /-- The lift is flat over `S'`. -/
  flat : AlgebraicGeometry.IsFlatOver D.f' module'
  /-- The prescribed identification of the restriction of the lift with `ℱ`. -/
  identification : (modulePullback D.i).obj module' ≅ F

/-- Two flat lifts are *isomorphic* when an isomorphism of the underlying `𝒪_{X'}`-modules
carries the one identification on `X` to the other. -/
def FlatLift.IsIsomorphic {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B : FlatLift D F) : Prop :=
  ∃ e : A.module' ≅ B.module',
    (modulePullback D.i).mapIso e ≪≫ B.identification = A.identification

/-- Isomorphism of flat lifts is an equivalence relation. -/
def flatLiftSetoid (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) : Setoid (FlatLift D F) where
  r := FlatLift.IsIsomorphic
  iseqv := by
    refine ⟨fun A => ⟨Iso.refl A.module', by simp⟩, ?_, ?_⟩
    · rintro A B ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [← he]
      simp
    · rintro A B C ⟨e, he⟩ ⟨f, hf⟩
      exact ⟨e ≪≫ f, by simp [← he, ← hf]⟩

/-- The isomorphism classes of flat lifts of `ℱ` across the upper thickening of `D`. -/
abbrev FlatLiftClass (D : MorphismOfThickenings.{u})
    (F : SheafOfModules.{u} (structureSheafRing D.X)) : Type _ :=
  Quotient (flatLiftSetoid D F)

/-- The canonical surjection `ℱ' ⟶ i_* ℱ` of a flat lift: the unit of `i^* ⊣ i_*` followed by
the direct image of the chosen identification. -/
noncomputable def FlatLift.reduction {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    A.module' ⟶ (modulePushforward D.i).obj F :=
  (modulePullbackPushforwardAdjunction D.i).unit.app A.module' ≫
    (modulePushforward D.i).map A.identification.hom

/-- The canonical surjection of a flat lift is the adjoint transpose of its identification. -/
theorem FlatLift.homEquiv_symm_reduction {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    ((modulePullbackPushforwardAdjunction D.i).homEquiv A.module' F).symm A.reduction =
      A.identification.hom :=
  ((modulePullbackPushforwardAdjunction D.i).homEquiv A.module' F).symm_apply_eq.2
    ((modulePullbackPushforwardAdjunction D.i).homEquiv_unit A.module' F
      A.identification.hom).symm

/-- The canonical surjection of a flat lift is an epimorphism: the unit of `i^* ⊣ i_*` is one
at every module across a thickening. -/
theorem FlatLift.epi_reduction {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) : Epi A.reduction := by
  have := epi_unit_app_of_isThickening D.i D.i_isThickening A.module'
  have : IsIso ((modulePushforward D.i).map A.identification.hom) :=
    ((modulePushforward D.i).mapIso A.identification).isIso_hom
  unfold FlatLift.reduction
  infer_instance

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The identification `i^*(ℐ ⊗_{𝒪_{X'}} ℱ') ⟶ ℐ ⊗_{𝒪_X} ℱ` attached to a flat lift: the
**Stacks 01CD** comparison followed by the chosen identification of the lift. -/
noncomputable def FlatLift.idealTensorRestriction {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (modulePullback D.i).obj ((idealTensorFunctor D.i).obj A.module') ⟶ idealTensor D F :=
  (Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app (D.idealI, A.module') ≫
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback D.i)),
        A.identification.hom) : ((idealSheafPullback D.i), ((modulePullback D.i).obj A.module')) ⟶
        ((idealSheafPullback D.i), F)))

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The identification attached to a flat lift is an isomorphism: both of its factors are. -/
theorem FlatLift.isIso_idealTensorRestriction {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    IsIso A.idealTensorRestriction := by
  have h1 : IsIso ((Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app
    (D.idealI, A.module')) := inferInstance
  have h2 : IsIso (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback D.i)),
      A.identification.hom) : ((idealSheafPullback D.i), ((modulePullback D.i).obj A.module')) ⟶
      ((idealSheafPullback D.i), F)))) :=
    isIso_tensorSheafMap_id_left (idealSheafPullback D.i) A.identification.hom
      (inferInstance : IsIso A.identification.hom)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- The identification `i^*(ℐ ⊗_{𝒪_{X'}} ℱ') ≅ ℐ ⊗_{𝒪_X} ℱ` attached to a flat lift. -/
noncomputable def FlatLift.idealTensorRestrictionIso {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (modulePullback D.i).obj ((idealTensorFunctor D.i).obj A.module') ≅ idealTensor D F :=
  @asIso _ _ _ _ A.idealTensorRestriction A.isIso_idealTensorRestriction

/-- The forward map of the identification attached to a flat lift is the map it is built
from. -/
theorem FlatLift.idealTensorRestrictionIso_hom {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    A.idealTensorRestrictionIso.hom = A.idealTensorRestriction := rfl

/-- **The ideal multiple of a flat lift is the direct image of `ℐ ⊗_{𝒪_X} ℱ`.** -/
noncomputable def FlatLift.infinitesimalIso {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (modulePushforward D.i).obj (idealTensor D F) ≅ infinitesimalPart D.i A.module' :=
  (modulePushforward D.i).mapIso (A.idealTensorRestrictionIso.symm ≪≫
      @asIso _ _ _ _ (restrictedIdealAction D A.module')
        (isIso_restrictedIdealAction_of_isFlatOver D hs A.module' A.flat)) ≪≫
    (@asIso _ _ _ _ ((modulePullbackPushforwardAdjunction D.i).unit.app
      (infinitesimalPart D.i A.module'))
      (infinitesimalPart_unit_isIso D.i hi A.module')).symm

/-- The identification of `i_*(ℐ ⊗_{𝒪_X} ℱ)` with the ideal multiple of a flat lift, read
through the unit of `i^* ⊣ i_*` at the ideal multiple. -/
theorem FlatLift.infinitesimalIso_hom_comp_unit {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (A.infinitesimalIso hi hs).hom ≫
        (modulePullbackPushforwardAdjunction D.i).unit.app
          (infinitesimalPart D.i A.module') =
      (modulePushforward D.i).map
        (A.idealTensorRestrictionIso.inv ≫ restrictedIdealAction D A.module') := by
  have := infinitesimalPart_unit_isIso D.i hi A.module'
  simp [FlatLift.infinitesimalIso]

/-- **The kernel extension of a flat lift**: the short exact sequence
`0 ⟶ i_*(ℐ ⊗_{𝒪_X} ℱ) ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` whose surjection is the canonical surjection of the
lift and whose injection is the inclusion of the ideal multiple `ℐℱ'`, identified with
`i_*(ℐ ⊗_{𝒪_X} ℱ)` by **Stacks 08LI**. -/
noncomputable def FlatLift.kernelExtension {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    CategoryTheory.Abelian.YonedaExtension ((modulePushforward D.i).obj F)
      ((modulePushforward D.i).obj (idealTensor D F)) 0 :=
  letI : Epi ((modulePullbackPushforwardAdjunction D.i).unit.app A.module') :=
    epi_unit_app_of_isThickening D.i D.i_isThickening A.module'
  CategoryTheory.Abelian.yonedaExtensionOfKernelIso
    ((modulePullbackPushforwardAdjunction D.i).unit.app A.module')
    (A.infinitesimalIso hi hs) ((modulePushforward D.i).mapIso A.identification)

/-- The middle term of the kernel extension of a flat lift is the lift itself. -/
theorem FlatLift.kernelExtension_Z_left {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (A.kernelExtension hi hs).Z.left = A.module' := rfl

/-- The surjection of the kernel extension of a flat lift is its canonical surjection. -/
theorem FlatLift.kernelExtension_g {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (A.kernelExtension hi hs).g = A.reduction := rfl

/-- The injection of the kernel extension of a flat lift is the inclusion of the ideal
multiple, read through the identification of **Stacks 08LI**. -/
theorem FlatLift.kernelExtension_f {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (A.kernelExtension hi hs).f =
      (A.infinitesimalIso hi hs).hom ≫ infinitesimalι D.i A.module' := rfl

/-- **The ideal action on a flat lift factors through its kernel extension.** The ideal action
on the lift, read through the identification of the ideal multiple with `i_*(ℐ ⊗_{𝒪_X} ℱ)`, is
the factorization of the ideal action through the ideal multiple. -/
theorem FlatLift.unit_comp_infinitesimalIso {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (modulePullbackPushforwardAdjunction D.i).unit.app
          ((idealTensorFunctor D.i).obj A.module') ≫
        ((modulePushforward D.i).map A.idealTensorRestrictionIso.hom ≫
          (A.infinitesimalIso hi hs).hom) =
      idealMultipleFactor D.i D.i_isThickening A.module' := by
  have := infinitesimalPart_unit_isIso D.i hi A.module'
  refine (cancel_mono ((modulePullbackPushforwardAdjunction D.i).unit.app
    (infinitesimalPart D.i A.module'))).1 ?_
  rw [Category.assoc, Category.assoc, A.infinitesimalIso_hom_comp_unit hi hs,
    ← Functor.map_comp, Iso.hom_inv_id_assoc, restrictedIdealAction_eq]
  exact ((modulePullbackPushforwardAdjunction D.i).unit.naturality
    (idealMultipleFactor D.i D.i_isThickening A.module')).symm

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The comparison of **Stacks 08L4** precomposed with the ideal tensor of the canonical
surjection of a flat lift: it is the adjoint transpose of the identification
`i^*(ℐ ⊗_{𝒪_{X'}} ℱ') ≅ ℐ ⊗_{𝒪_X} ℱ`. -/
theorem FlatLift.idealTensorFunctor_map_reduction_comp {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (idealTensorFunctor D.i).map A.reduction ≫
        idealTensorAction D F =
      (modulePullbackPushforwardAdjunction D.i).unit.app
          ((idealTensorFunctor D.i).obj A.module') ≫
        (modulePushforward D.i).map A.idealTensorRestrictionIso.hom := by
  have hid := idealTensorAction_eq_extensionTensorComparison D F
  have hres : A.idealTensorRestrictionIso.hom =
      (Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf D.i, A.module') ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback D.i)),
            A.identification.hom) : ((idealSheafPullback D.i),
            ((modulePullback D.i).obj A.module')) ⟶ ((idealSheafPullback D.i), F))) :=
    A.idealTensorRestrictionIso_hom
  refine Eq.trans (congrArg (fun z => (idealTensorFunctor D.i).map A.reduction ≫ z) hid) ?_
  refine (tensorSheafMap_comp_extensionTensorComparison D.i A.reduction).trans ?_
  refine Eq.trans (congrArg ((modulePullbackPushforwardAdjunction D.i).homEquiv _ _)
    (congrArg (fun z => (Stacks.RingedSpace.comparisonBifunctorIso D.i).hom.app
        (AlgebraicGeometry.SheafOfModules.idealSheaf D.i, A.module') ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback D.i)), z) :
          ((idealSheafPullback D.i), ((modulePullback D.i).obj A.module')) ⟶
          ((idealSheafPullback D.i), F)))) A.homEquiv_symm_reduction)) ?_
  refine Eq.trans (congrArg ((modulePullbackPushforwardAdjunction D.i).homEquiv _ _)
    hres.symm) ?_
  exact (modulePullbackPushforwardAdjunction D.i).homEquiv_unit _ _ _

/-- **The kernel extension of a flat lift is normalized.** Its canonical map of **Stacks 08L4**
is the identity of `ℐ ⊗_{𝒪_X} ℱ`. -/
theorem FlatLift.kernelExtension_action {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    (firstOrderExtensionAction D.i F (idealTensor D F) hi (A.kernelExtension hi hs)).val =
      𝟙 (idealTensor D F) := by
  refine (eq_firstOrderExtensionAction_of_descendedAction D.i F (idealTensor D F) hi
    (A.kernelExtension hi hs) (𝟙 (idealTensor D F)) ?_).symm
  calc (idealTensorFunctor D.i).map A.reduction ≫
          (idealTensorAction D F ≫
            ((A.infinitesimalIso hi hs).hom ≫ infinitesimalι D.i A.module'))
      = ((idealTensorFunctor D.i).map A.reduction ≫ idealTensorAction D F) ≫
            ((A.infinitesimalIso hi hs).hom ≫ infinitesimalι D.i A.module') :=
        (Category.assoc _ _ _).symm
    _ = ((modulePullbackPushforwardAdjunction D.i).unit.app
            ((idealTensorFunctor D.i).obj A.module') ≫
          (modulePushforward D.i).map A.idealTensorRestrictionIso.hom) ≫
            ((A.infinitesimalIso hi hs).hom ≫ infinitesimalι D.i A.module') :=
        congrArg (fun z => z ≫ ((A.infinitesimalIso hi hs).hom ≫
          infinitesimalι D.i A.module')) A.idealTensorFunctor_map_reduction_comp
    _ = ((modulePullbackPushforwardAdjunction D.i).unit.app
            ((idealTensorFunctor D.i).obj A.module') ≫
          ((modulePushforward D.i).map A.idealTensorRestrictionIso.hom ≫
            (A.infinitesimalIso hi hs).hom)) ≫ infinitesimalι D.i A.module' := by
        simp only [Category.assoc]
    _ = idealMultipleFactor D.i D.i_isThickening A.module' ≫
          infinitesimalι D.i A.module' :=
        congrArg (fun z => z ≫ infinitesimalι D.i A.module')
          (A.unit_comp_infinitesimalIso hi hs)
    _ = (idealActionNatTrans D.i).app A.module' :=
        idealMultipleFactor_comp_infinitesimalι D.i D.i_isThickening A.module'

/-! ### The difference of two flat lifts -/

/-- `E` is *the kernel extension of the flat lift* `A`: it is an extension
`0 ⟶ i_*(ℐ ⊗_{𝒪_X} ℱ) ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` whose canonical map of **Stacks 08L4** is the identity
— the normalization `c_{ℱ'} = 1` — and whose middle term is the lift, compatibly
with its canonical surjection. -/
def FlatLift.IsKernelExtension {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) {F : SheafOfModules.{u} (structureSheafRing D.X)}
    (A : FlatLift D F)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward D.i).obj F)
      ((modulePushforward D.i).obj (idealTensor D F)) 0) : Prop :=
  (firstOrderExtensionAction D.i F (idealTensor D F) hi E).val = 𝟙 (idealTensor D F) ∧
    ∃ e : E.Z.left ≅ A.module', e.hom ≫ A.reduction = E.g

/-- The kernel extension of a flat lift is a kernel extension of it. -/
theorem FlatLift.isKernelExtension_kernelExtension {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    A.IsKernelExtension hi (A.kernelExtension hi hs) :=
  ⟨A.kernelExtension_action hi hs, ⟨Iso.refl A.module', Category.id_comp _⟩⟩

/-- The defining equation of the canonical map of **Stacks 08L4** for a kernel extension, with
the canonical map normalized to the identity. -/
theorem FlatLift.descendedAction_of_isKernelExtension {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) {F : SheafOfModules.{u} (structureSheafRing D.X)}
    (A : FlatLift D F)
    {E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward D.i).obj F)
      ((modulePushforward D.i).obj (idealTensor D F)) 0}
    (hE : A.IsKernelExtension hi E) :
    (idealTensorFunctor D.i).map E.g ≫ idealTensorAction D F ≫ E.f =
      (idealActionNatTrans D.i).app E.Z.left :=
  (congrArg (fun z => (idealTensorFunctor D.i).map E.g ≫
      descendedActionOfMap D.i F (idealTensor D F) z ≫ E.f) hE.1).symm.trans
    (descendedAction_firstOrderExtensionAction D.i F (idealTensor D F) hi E)

/-- A map of the underlying modules of two flat lifts is compatible with their canonical
surjections exactly when it carries one identification to the other. -/
private theorem FlatLift.comp_reduction_eq_iff {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} {A B : FlatLift D F}
    (e : A.module' ≅ B.module') :
    e.hom ≫ B.reduction = A.reduction ↔
      (modulePullback D.i).mapIso e ≪≫ B.identification = A.identification := by
  have h (C : FlatLift D F) : C.reduction =
      (modulePullbackPushforwardAdjunction D.i).homEquiv C.module' F C.identification.hom :=
    ((modulePullbackPushforwardAdjunction D.i).homEquiv_unit _ _ _).symm
  rw [h A, h B, ← (modulePullbackPushforwardAdjunction D.i).homEquiv_naturality_left,
    Equiv.apply_eq_iff_eq, Iso.ext_iff]
  rfl

/-- An isomorphism of flat lifts is compatible with their canonical surjections. -/
theorem FlatLift.reduction_of_isIsomorphic {D : MorphismOfThickenings.{u}}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} {A B : FlatLift D F}
    {e : A.module' ≅ B.module'}
    (he : (modulePullback D.i).mapIso e ≪≫ B.identification = A.identification) :
    e.hom ≫ B.reduction = A.reduction :=
  (FlatLift.comp_reduction_eq_iff e).2 he

/-- A kernel extension of a flat lift is a kernel extension of every isomorphic flat lift. -/
theorem FlatLift.isKernelExtension_of_isIsomorphic {D : MorphismOfThickenings.{u}}
    (hi : IsFirstOrderThickening D.i) {F : SheafOfModules.{u} (structureSheafRing D.X)}
    {A B : FlatLift D F} (hAB : A.IsIsomorphic B)
    {E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward D.i).obj F)
      ((modulePushforward D.i).obj (idealTensor D F)) 0}
    (hE : A.IsKernelExtension hi E) : B.IsKernelExtension hi E := by
  obtain ⟨e, he⟩ := hAB
  obtain ⟨hc, f, hf⟩ := hE
  refine ⟨hc, f ≪≫ e, ?_⟩
  calc (f ≪≫ e).hom ≫ B.reduction = f.hom ≫ e.hom ≫ B.reduction := Category.assoc _ _ _
    _ = f.hom ≫ A.reduction := congrArg _ (FlatLift.reduction_of_isIsomorphic he)
    _ = E.g := hf

/-- The direct image `i_*` along a thickening is fully faithful and exact. -/
private theorem withModulePushforwardInstances (D : MorphismOfThickenings.{u}) {P : Prop}
    (h : [(modulePushforward D.i).Full] → [(modulePushforward D.i).Faithful] →
      [Limits.PreservesFiniteLimits (modulePushforward D.i)] →
      [Limits.PreservesFiniteColimits (modulePushforward D.i)] → P) : P :=
  haveI : (modulePushforward D.i).Full :=
    (closedQuotientOfIsThickening D.i D.i_isThickening).full_modulePushforward
  haveI : (modulePushforward D.i).Faithful :=
    (closedQuotientOfIsThickening D.i D.i_isThickening).faithful_modulePushforward
  haveI : Limits.PreservesFiniteLimits (modulePushforward D.i) :=
    preservesFiniteLimits_modulePushforward D.i
  haveI : Limits.PreservesFiniteColimits (modulePushforward D.i) :=
    preservesFiniteColimits_modulePushforward D.i D.i_isThickening
  h

section Difference

variable {D : MorphismOfThickenings.{u}}
  [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X))]
  [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X'))]

omit [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X))] in
/-- **The class of the kernel extension of a flat lift is well defined.** Two kernel extensions
of the same lift have the same class in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_*(ℐ ⊗_{𝒪_X} ℱ))`. -/
theorem FlatLift.extClass_eq_of_isKernelExtension (hi : IsFirstOrderThickening D.i)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    {E E' : CategoryTheory.Abelian.YonedaExtension ((modulePushforward D.i).obj F)
      ((modulePushforward D.i).obj (idealTensor D F)) 0}
    (hE : A.IsKernelExtension hi E) (hE' : A.IsKernelExtension hi E') :
    (CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass =
      (CategoryTheory.Abelian.YonedaExtension.shortExact E').extClass := by
  have hdA := A.descendedAction_of_isKernelExtension hi hE
  have hdA' := A.descendedAction_of_isKernelExtension hi hE'
  obtain ⟨-, e, he⟩ := hE
  obtain ⟨-, e', he'⟩ := hE'
  have hg : (e ≪≫ e'.symm).hom ≫ E'.g = E.g := by
    have h1 : e'.inv ≫ E'.g = A.reduction := by
      rw [← he', ← Category.assoc, e'.inv_hom_id, Category.id_comp]
    calc (e ≪≫ e'.symm).hom ≫ E'.g = e.hom ≫ e'.inv ≫ E'.g := Category.assoc _ _ _
      _ = e.hom ≫ A.reduction := congrArg _ h1
      _ = E.g := he
  refine ((CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
    (SheafOfModules.{u} (structureSheafRing D.X')) ((modulePushforward D.i).obj F)
    ((modulePushforward D.i).obj (idealTensor D F))).2.1
      _ _ _ _ _ _ _ _ (CategoryTheory.Abelian.YonedaExtension.shortExact E)
      (CategoryTheory.Abelian.YonedaExtension.shortExact E')).2 ⟨e ≪≫ e'.symm, ?_, hg⟩
  have hTiso : IsIso ((idealTensorFunctor D.i).map (e ≪≫ e'.symm).hom) :=
    ((idealTensorFunctor D.i).mapIso (e ≪≫ e'.symm)).isIso_hom
  have hTg : (idealTensorFunctor D.i).map E.g =
      (idealTensorFunctor D.i).map (e ≪≫ e'.symm).hom ≫
        (idealTensorFunctor D.i).map E'.g :=
    (((idealTensorFunctor D.i).map_comp _ _).symm.trans (congrArg _ hg)).symm
  have hcancel : (idealTensorFunctor D.i).map E'.g ≫ idealTensorAction D F ≫
        (E.f ≫ (e ≪≫ e'.symm).hom) =
      (idealTensorFunctor D.i).map E'.g ≫ idealTensorAction D F ≫ E'.f := by
    refine (cancel_epi ((idealTensorFunctor D.i).map (e ≪≫ e'.symm).hom)).1 ?_
    calc (idealTensorFunctor D.i).map (e ≪≫ e'.symm).hom ≫
            (idealTensorFunctor D.i).map E'.g ≫ idealTensorAction D F ≫
              (E.f ≫ (e ≪≫ e'.symm).hom)
        = ((idealTensorFunctor D.i).map E.g ≫ idealTensorAction D F ≫ E.f) ≫
            (e ≪≫ e'.symm).hom := by rw [hTg]; simp only [Category.assoc]
      _ = (idealActionNatTrans D.i).app E.Z.left ≫ (e ≪≫ e'.symm).hom :=
          congrArg (fun z => z ≫ (e ≪≫ e'.symm).hom) hdA
      _ = (idealTensorFunctor D.i).map (e ≪≫ e'.symm).hom ≫
            (idealActionNatTrans D.i).app E'.Z.left :=
          ((idealActionNatTrans D.i).naturality (e ≪≫ e'.symm).hom).symm
      _ = (idealTensorFunctor D.i).map (e ≪≫ e'.symm).hom ≫
            (idealTensorFunctor D.i).map E'.g ≫ idealTensorAction D F ≫ E'.f :=
          congrArg (fun z => (idealTensorFunctor D.i).map (e ≪≫ e'.symm).hom ≫ z) hdA'.symm
  have hepiTg : Epi ((idealTensorFunctor D.i).map E'.g) :=
    idealTensorFunctor_epi D.i E'.g E'.epi_g
  have hepiA : Epi (idealTensorAction D F) := epi_idealTensorAction D F
  exact (cancel_epi (idealTensorAction D F)).1
    ((cancel_epi ((idealTensorFunctor D.i).map E'.g)).1 hcancel)

/-- **A presentation of the difference of two flat lifts.** It consists of a kernel extension
of each lift, an extension `diff` of `ℱ` by `ℐ ⊗_{𝒪_X} ℱ` over `𝒪_X`, an extension `thickDiff`
of `𝒪_{X'}`-modules whose class is the difference of the classes of the two kernel extensions,
and an identification of `thickDiff` with the direct image of `diff`. -/
structure DifferencePresentation (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) {F : SheafOfModules.{u} (structureSheafRing D.X)}
    (A B : FlatLift D F)
    [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X'))] where
  /-- A kernel extension of the first lift. -/
  extA : CategoryTheory.Abelian.YonedaExtension ((modulePushforward D.i).obj F)
    ((modulePushforward D.i).obj (idealTensor D F)) 0
  /-- `extA` is a kernel extension of `A`, normalized by `c_{ℱ'} = 1`. -/
  isKernelExtension_extA : A.IsKernelExtension hi extA
  /-- A kernel extension of the second lift. -/
  extB : CategoryTheory.Abelian.YonedaExtension ((modulePushforward D.i).obj F)
    ((modulePushforward D.i).obj (idealTensor D F)) 0
  /-- `extB` is a kernel extension of `B`, normalized by `c_{ℱ'} = 1`. -/
  isKernelExtension_extB : B.IsKernelExtension hi extB
  /-- The difference of the two kernel extensions, read as an extension of `𝒪_X`-modules. -/
  diff : CategoryTheory.Abelian.YonedaExtension F (idealTensor D F) 0
  /-- The difference of the two kernel extensions, as an extension of `𝒪_{X'}`-modules. -/
  thickDiff : CategoryTheory.Abelian.YonedaExtension ((modulePushforward D.i).obj F)
    ((modulePushforward D.i).obj (idealTensor D F)) 0
  /-- The identification exhibiting `thickDiff` as the direct image of `diff`. -/
  comparison : thickDiff.Z.left ≅ (modulePushforward D.i).obj diff.Z.left
  /-- The identification respects the injection of `i_*(ℐ ⊗_{𝒪_X} ℱ)`. -/
  comparison_left : thickDiff.f ≫ comparison.hom = (modulePushforward D.i).map diff.f
  /-- The identification respects the surjection onto `i_* ℱ`. -/
  comparison_right : comparison.hom ≫ (modulePushforward D.i).map diff.g = thickDiff.g
  /-- The class of `thickDiff` is the difference of the classes of `extA` and `extB`. -/
  baerDifference :
    (CategoryTheory.Abelian.YonedaExtension.shortExact thickDiff).extClass =
      (CategoryTheory.Abelian.YonedaExtension.shortExact extA).extClass -
        (CategoryTheory.Abelian.YonedaExtension.shortExact extB).extClass

/-- The class in `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)` presented by a difference presentation. -/
noncomputable def DifferencePresentation.differenceClass
    {hi : IsFirstOrderThickening D.i} {F : SheafOfModules.{u} (structureSheafRing D.X)}
    {A B : FlatLift D F} (P : DifferencePresentation.{u, w} D hi A B) :
    CategoryTheory.Abelian.Ext.{w} F (idealTensor D F) 1 :=
  (CategoryTheory.Abelian.YonedaExtension.shortExact P.diff).extClass

/-- Any two flat lifts of `ℱ` across a strict morphism of first order thickenings admit a
presentation of their difference: each has a kernel extension normalized by `c_{ℱ'} = 1`, and
the difference of the two classes is the class of an extension of `𝒪_X`-modules. -/
theorem exists_differencePresentation (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B : FlatLift D F) :
    Nonempty (DifferencePresentation.{u, w} D hi A B) := by
  refine withModulePushforwardInstances D ?_
  intro _ _ _ _
  obtain ⟨ξ, ⟨hξ, Dext, hDcl, hDess⟩, -⟩ :=
    existsUnique_extClass_sub_of_firstOrderExtensionAction_eq D.i F (idealTensor D F) hi
      (B.kernelExtension hi hs) (A.kernelExtension hi hs)
      ((A.kernelExtension_action hi hs).trans (B.kernelExtension_action hi hs).symm)
  obtain ⟨M, f, g, w₀, h₀, c, hcl, hcr, hmap⟩ :=
    CategoryTheory.Abelian.exists_shortExact_comparison_mapExactFunctor_extClass_eq
      (modulePushforward D.i) (CategoryTheory.Abelian.YonedaExtension.shortExact Dext) hDess
  refine ⟨{ extA := A.kernelExtension hi hs
            isKernelExtension_extA := A.isKernelExtension_kernelExtension hi hs
            extB := B.kernelExtension hi hs
            isKernelExtension_extB := B.isKernelExtension_kernelExtension hi hs
            diff := CategoryTheory.Abelian.shortExactYonedaExtension h₀
            thickDiff := Dext
            comparison := c
            comparison_left := hcl
            comparison_right := hcr
            baerDifference := ?_ }⟩
  rw [hDcl, hξ]
  abel

/-- The difference of two flat lifts, as a class in `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`: the class of
a chosen presentation of their difference, which by
`AlgebraicGeometry.RingedSpaceThickening.flatLiftDifference_eq` does not depend on the
choice. -/
noncomputable def flatLiftDifference (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B : FlatLift D F) :
    CategoryTheory.Abelian.Ext.{w} F (idealTensor D F) 1 :=
  (Classical.choice (exists_differencePresentation hi hs A B)).differenceClass

/-- The direct image of the class of a presentation of the difference of two flat lifts is the
difference of the classes of the kernel extensions of the lifts. -/
theorem DifferencePresentation.mapExactFunctor_differenceClass
    [Limits.PreservesFiniteLimits (modulePushforward D.i)]
    [Limits.PreservesFiniteColimits (modulePushforward D.i)]
    {hi : IsFirstOrderThickening D.i} {F : SheafOfModules.{u} (structureSheafRing D.X)}
    {A B : FlatLift D F} (P : DifferencePresentation.{u, w} D hi A B) :
    P.differenceClass.mapExactFunctor (modulePushforward D.i) =
      (CategoryTheory.Abelian.YonedaExtension.shortExact P.extA).extClass -
        (CategoryTheory.Abelian.YonedaExtension.shortExact P.extB).extClass := by
  refine Eq.trans ?_ P.baerDifference
  refine Eq.trans
    (CategoryTheory.Abelian.Ext.mapExactFunctor_extClass (modulePushforward D.i)
      (CategoryTheory.Abelian.YonedaExtension.shortExact P.diff)) ?_
  exact (((CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
    (SheafOfModules.{u} (structureSheafRing D.X')) ((modulePushforward D.i).obj F)
    ((modulePushforward D.i).obj (idealTensor D F))).2.1 _ _ _ _ _ _ _ _
      ((CategoryTheory.Abelian.YonedaExtension.shortExact P.diff).map_of_exact
        (modulePushforward D.i))
      (CategoryTheory.Abelian.YonedaExtension.shortExact P.thickDiff)).2
    ⟨P.comparison.symm,
      by rw [Iso.symm_hom, ← P.comparison_left, Category.assoc, Iso.hom_inv_id,
        Category.comp_id],
      by rw [Iso.symm_hom, ← P.comparison_right, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]⟩)

/-- The direct image of the class of a presentation of the difference of two flat lifts is the
difference of the classes of their canonical kernel extensions. -/
private theorem mapExactFunctor_differenceClass_eq
    [Limits.PreservesFiniteLimits (modulePushforward D.i)]
    [Limits.PreservesFiniteColimits (modulePushforward D.i)]
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} {A B : FlatLift D F}
    (P : DifferencePresentation.{u, w} D hi A B) :
    P.differenceClass.mapExactFunctor (modulePushforward D.i) =
      (CategoryTheory.Abelian.YonedaExtension.shortExact
          (A.kernelExtension hi hs)).extClass -
        (CategoryTheory.Abelian.YonedaExtension.shortExact
          (B.kernelExtension hi hs)).extClass := by
  rw [P.mapExactFunctor_differenceClass,
    A.extClass_eq_of_isKernelExtension hi P.isKernelExtension_extA
      (A.isKernelExtension_kernelExtension hi hs),
    B.extClass_eq_of_isKernelExtension hi P.isKernelExtension_extB
      (B.isKernelExtension_kernelExtension hi hs)]

/-- The difference of two flat lifts is the class of *any* presentation of their difference: it
depends neither on the kernel extensions chosen nor on the extension of `𝒪_X`-modules realizing
their difference. -/
theorem flatLiftDifference_eq (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} {A B : FlatLift D F}
    (P : DifferencePresentation.{u, w} D hi A B) :
    flatLiftDifference hi hs A B = P.differenceClass := by
  refine withModulePushforwardInstances D ?_
  intro _ _ _ _
  exact CategoryTheory.Abelian.mapExactFunctor_injective_one (modulePushforward D.i) _ _
    ((mapExactFunctor_differenceClass_eq hi hs
      (Classical.choice (exists_differencePresentation hi hs A B))).trans
      (mapExactFunctor_differenceClass_eq hi hs P).symm)

/-- Two flat lifts differ by exactly one class in `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`: there is a
unique class that every presentation of their difference realizes. -/
theorem existsUnique_differenceClass (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B : FlatLift D F) :
    ∃! ξ : CategoryTheory.Abelian.Ext.{w} F (idealTensor D F) 1,
      ∀ P : DifferencePresentation.{u, w} D hi A B, P.differenceClass = ξ :=
  ⟨flatLiftDifference hi hs A B, fun P => (flatLiftDifference_eq hi hs P).symm,
    fun _ hζ => (hζ (Classical.choice (exists_differencePresentation hi hs A B))).symm⟩

/-- **Freeness of the action.** Two flat lifts whose difference vanishes are isomorphic. -/
theorem isIsomorphic_of_flatLiftDifference_eq_zero (hi : IsFirstOrderThickening D.i)
    (hs : D.IsStrict) {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B : FlatLift D F)
    (h : flatLiftDifference hi hs A B = 0) : A.IsIsomorphic B := by
  refine withModulePushforwardInstances D ?_
  intro _ _ _ _
  obtain ⟨Q⟩ := exists_differencePresentation.{u, w} hi hs A B
  have hQ : Q.differenceClass = 0 := (flatLiftDifference_eq hi hs Q).symm.trans h
  have hzero : (CategoryTheory.Abelian.YonedaExtension.shortExact
        (A.kernelExtension hi hs)).extClass =
      (CategoryTheory.Abelian.YonedaExtension.shortExact (B.kernelExtension hi hs)).extClass := by
    have h1 := mapExactFunctor_differenceClass_eq hi hs Q
    rw [hQ, CategoryTheory.Abelian.Ext.mapExactFunctor_zero] at h1
    exact sub_eq_zero.1 h1.symm
  obtain ⟨φ, -, hφ⟩ :=
    ((CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{u} (structureSheafRing D.X')) ((modulePushforward D.i).obj F)
      ((modulePushforward D.i).obj (idealTensor D F))).2.1 _ _ _ _ _ _ _ _
        (CategoryTheory.Abelian.YonedaExtension.shortExact (A.kernelExtension hi hs))
        (CategoryTheory.Abelian.YonedaExtension.shortExact (B.kernelExtension hi hs))).1 hzero
  exact ⟨φ, (FlatLift.comp_reduction_eq_iff φ).1 hφ⟩

/-- A presentation of the difference of two flat lifts presents the difference of any two
isomorphic flat lifts. -/
noncomputable def DifferencePresentation.congr {hi : IsFirstOrderThickening D.i}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} {A A' B B' : FlatLift D F}
    (P : DifferencePresentation.{u, w} D hi A B) (hA : A.IsIsomorphic A')
    (hB : B.IsIsomorphic B') : DifferencePresentation.{u, w} D hi A' B' where
  extA := P.extA
  isKernelExtension_extA :=
    FlatLift.isKernelExtension_of_isIsomorphic hi hA P.isKernelExtension_extA
  extB := P.extB
  isKernelExtension_extB :=
    FlatLift.isKernelExtension_of_isIsomorphic hi hB P.isKernelExtension_extB
  diff := P.diff
  thickDiff := P.thickDiff
  comparison := P.comparison
  comparison_left := P.comparison_left
  comparison_right := P.comparison_right
  baerDifference := P.baerDifference

/-- The class of a presentation of the difference does not change when the two lifts are
replaced by isomorphic ones. -/
theorem DifferencePresentation.differenceClass_congr {hi : IsFirstOrderThickening D.i}
    {F : SheafOfModules.{u} (structureSheafRing D.X)} {A A' B B' : FlatLift D F}
    (P : DifferencePresentation.{u, w} D hi A B) (hA : A.IsIsomorphic A')
    (hB : B.IsIsomorphic B') : (P.congr hA hB).differenceClass = P.differenceClass := rfl

/-- **The difference of two flat lifts depends only on their isomorphism classes.** -/
theorem flatLiftDifference_congr (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} {A A' B B' : FlatLift D F}
    (hA : A.IsIsomorphic A') (hB : B.IsIsomorphic B') :
    flatLiftDifference hi hs A B = flatLiftDifference hi hs A' B' := by
  obtain ⟨P⟩ := exists_differencePresentation.{u, w} hi hs A B
  rw [flatLiftDifference_eq hi hs P, flatLiftDifference_eq hi hs (P.congr hA hB),
    P.differenceClass_congr hA hB]

/-- A flat lift differs from itself by the zero class. -/
theorem flatLiftDifference_self (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    flatLiftDifference hi hs A A = 0 := by
  refine withModulePushforwardInstances D ?_
  intro _ _ _ _
  obtain ⟨P⟩ := exists_differencePresentation.{u, w} hi hs A A
  rw [flatLiftDifference_eq hi hs P]
  refine CategoryTheory.Abelian.mapExactFunctor_injective_one (modulePushforward D.i) _ _ ?_
  beta_reduce
  rw [mapExactFunctor_differenceClass_eq hi hs P, CategoryTheory.Abelian.Ext.mapExactFunctor_zero,
    sub_self]

/-- The difference of two flat lifts, as a function of their isomorphism classes. -/
noncomputable def flatLiftClassDifference (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    FlatLiftClass D F → FlatLiftClass D F →
      CategoryTheory.Abelian.Ext.{w} F (idealTensor D F) 1 :=
  Quotient.lift₂ (fun A B => flatLiftDifference hi hs A B)
    fun _ _ _ _ hA hB => flatLiftDifference_congr hi hs hA hB

/-- The difference of the isomorphism classes of two flat lifts is their difference. -/
theorem flatLiftClassDifference_mk (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B : FlatLift D F) :
    flatLiftClassDifference hi hs F (Quotient.mk (flatLiftSetoid D F) A)
        (Quotient.mk (flatLiftSetoid D F) B) =
      flatLiftDifference hi hs A B := rfl

/-- **Freeness of the action.** Two isomorphism classes of flat lifts are equal exactly when
their difference in `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)` vanishes. -/
theorem flatLiftClassDifference_eq_zero_iff (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (a b : FlatLiftClass D F) :
    flatLiftClassDifference hi hs F a b = 0 ↔ a = b := by
  induction a, b using Quotient.inductionOn₂ with
  | h A B =>
    exact ⟨fun h => Quotient.sound (isIsomorphic_of_flatLiftDifference_eq_zero hi hs A B h),
      fun h => (flatLiftDifference_congr hi hs ((flatLiftSetoid D F).iseqv.refl A)
        (Quotient.exact h.symm)).trans (flatLiftDifference_self hi hs A)⟩

end Difference

end AlgebraicGeometry.RingedSpaceThickening

end
