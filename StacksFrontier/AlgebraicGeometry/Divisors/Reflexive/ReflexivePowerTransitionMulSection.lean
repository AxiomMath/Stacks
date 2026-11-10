module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit

/-!
# Multiplication by a global section commutes with restriction to an open

Let `X` be a scheme, `V ⊆ X` an open, `ℱ`, `𝒢` two `𝒪_X`-modules and `s ∈ Γ(X, ℱ)`.  The
transitions of the system of [Stacks, Tag 0EBN] are multiplication by `s`,
`𝒢 ⟶ ℱ ⊗_{𝒪_X} 𝒢`, and
`StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionRestrict` proves the
transition square over `V` with the reflexive hull cancelled, but with the right-hand map still
*the restriction of* multiplication by `s`, transported by `tensorSheafRestrictIso`, rather than
multiplication by `s|_V` on `V`.  This file identifies the two, which is the left-unitor
coherence of [Stacks, Tag 01CD] at `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, and
completes the square.

The coherence itself is the unconditional `Stacks.RingedSpace.comparison_leftUnitor`, proved for
the *pullback* functor.  Conjugating it onto the restriction functor needs one identity that was
missing: `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, Mathlib's `𝒪_X|_V ≅ 𝒪_V`, has to be
the comparison `f^*𝒪_X ≅ 𝒪_V` of `Stacks.RingedSpace.pullbackObjUnitIso` conjugated by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.  That is `restrictUnitIso_eq`
below.

## Main definitions

* `Stacks.RingedSpace.mulSectionTensor`: `Stacks.AlgebraicGeometry.ReflexivePowers.mulSectionHom`
  with its target ascribed at `Stacks.RingedSpace.tensorSheaf`, the bifunctor spelling, so that
  `rw` accepts a goal mentioning it.  The ascription is the one `mulSection` performs at
  `AlgebraicGeometry.Scheme.Modules`, for the same reason.
* `Stacks.AlgebraicGeometry.ReflexivePowers.restrictSection`: the restriction `s|_V` of a global
  section, namely the section of `ℱ|_V` corresponding to `(restrictUnitIso V.ι).inv` followed by
  the restriction of the morphism `𝒪_X ⟶ ℱ` determined by `s`.

## Main results

* `Stacks.RingedSpace.mulSectionTensor_eq`: multiplication by `s` is the inverse left unitor
  followed by the tensor bifunctor applied to `(σ, 𝟙)`.  This is the one statement of the file
  that mentions a monoidal structure, and it is what removes it from all the others.
* `Stacks.RingedSpace.pullback_mulSectionTensor`: **multiplication by a global section commutes
  with pullback along a morphism of ringed spaces**, through the comparison of
  [Stacks, Tag 01CD] and `ν : f^*𝒪_Y ≅ 𝒪_X`.
* `Stacks.AlgebraicGeometry.RestrictMulSection.restrictUnitIso_eq`: **the missing identity**,
  `𝒪_X|_V ≅ 𝒪_V` is `f^*𝒪_X ≅ 𝒪_V` conjugated by `restrictFunctorIsoPullback`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.restrict_mulSectionTensor` and
  `restrict_mulSection`: **multiplication by a global section commutes with restriction to an
  open**, the second written for `mulSection` and the restricted section `s|_V`.
* `restrict_reflexivePowerTransition_comp_restrictPowerIso_hom'`, in the same namespace:
  **the full transition square of the colimit clause of [Stacks, Tag 0EBN]** over an open `V` on
  which `ℱ` is invertible — for every `n`, the restricted transition against
  `tensorPowerTransition (ℱ|_V) (s|_V)`.  Over `V` the system of [Stacks, Tag 0EBN] is therefore
  isomorphic *as a system* to the ordinary tensor-power system of the invertible module `ℱ|_V`
  and the restricted section, which is the system [Stacks, Tag 01PW] is about.

## Implementation notes

**Why the identity is a transposition.**  Both sides are morphisms out of
`(restrictFunctor f).obj 𝒪_Y`, and `restrictFunctor f` is left adjoint to `f_*`
(`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`), so it is enough to compare the adjoint
transposes.  `restrictFunctorIsoPullback` is by definition
`CategoryTheory.Adjunction.leftAdjointUniq` of that adjunction and
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, so
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` turns the transpose of the
right-hand side into the transpose of `ν`, which Mathlib computes as
`SheafOfModules.unitToPushforwardObjUnit`, the morphism `𝒪_Y ⟶ f_*𝒪_X` given by `f^♯`.  The
transpose of `restrictUnitIso` is `f^♯` as well, on sections by
`AlgebraicGeometry.Scheme.Hom.app_appIso_inv`.  So the whole identity is the one geometric fact
that `f^♯` followed by the inverse of `f.appIso` is a restriction map.

**The two adjunctions do agree.**  `Stacks.RingedSpace.pullbackAdjunction`, which
`comparison_leftUnitor` is proved over, is `AlgebraicGeometry.Scheme.Modules`'s
`pullbackPushforwardAdjunction` at an open immersion of schemes, by `rfl`: both are
`SheafOfModules.pullbackPushforwardAdjunction` of the same morphism of sheaves of rings
(`Scheme.Hom.toRingCatSheafHom f` and `RingedSpaceModuleAdjunction.structureSheafHom` of the
underlying morphism of ringed spaces are equal by `rfl`), and
`CategoryTheory.Functor.IsRightAdjoint` is a `Prop`, so the instances cannot differ.  This was
the step nobody had checked.

**Spelling discipline.**  Three mutually `rfl`-equal spellings meet here, and `rw` sees through
none of them: `structureSheafRing` is semireducible, so a goal mixing it with the reducible
`Stacks.RingedSpace.structureRingSheaf` is rejected as ill-typed at `implicit` transparency; the
same holds for `AlgebraicGeometry.Scheme.Modules.pullback` against
`Stacks.RingedSpace.pullbackFunctor`.  Every statement below is therefore written in one
spelling throughout, and each crossing is performed once, inside a defeq-tolerant `:=` — which is
what `mulSectionTensor`, `pullback_mulSectionTensor_scheme` and `mulSectionTensor_comp_map_scheme`
are for.  The monoidal structure `Stacks.SheafOfModules.OnSpace.monoidal` appears only in the
first section.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf TopCat.Sheaf
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.RingedSpace

open Stacks.AlgebraicGeometry.ReflexivePowers (mulSectionHom)

/-! ### Multiplication by a global section, without a monoidal structure -/

section Monoidal

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable (Z : RingedSpace.{u, u})

/-- The tensor product of two morphisms for `Stacks.SheafOfModules.OnSpace.monoidal` is the
tensor bifunctor of [Stacks, Tag 0GMW] applied to the pair: both send a local pure tensor
`a ⊗ b` to `φ a ⊗ ψ b`. -/
theorem tensorHom_eq {A A' B B' : SheafOfModules.{u} (structureSheafRing Z)}
    (φ : A ⟶ A') (ψ : B ⟶ B') : (φ ⊗ₘ ψ) = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map (φ ×ₘ ψ) :=
  Stacks.SheafOfModules.OnSpace.tensor_hom_ext Z fun U a b =>
    (Stacks.SheafOfModules.OnSpace.tensorHom_tmul Z φ ψ U a b).trans
      (tensorSheaf_map_unit_tmul Z φ ψ U a b).symm

/-- The left unitor of `Stacks.SheafOfModules.OnSpace.monoidal` is the left unitor
`𝒪_X ⊗ A ≅ A` of the tensor product sheaf: both send `r ⊗ a` to `r • a`. -/
theorem leftUnitorIso_eq (A : SheafOfModules.{u} (structureSheafRing Z)) :
    (λ_ A) = tensorSheafUnitLeftIso Z A :=
  Iso.ext (Stacks.SheafOfModules.OnSpace.tensor_hom_ext Z fun U r a =>
    (Stacks.SheafOfModules.OnSpace.leftUnitor_tmul Z A U r a).trans
      (tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul Z A U r a).symm)

/-- **Multiplication by a global section, with no monoidal structure in the statement**: it is
the inverse left unitor of the tensor product sheaf followed by the tensor bifunctor at
`(σ, 𝟙)`. -/
theorem mulSectionHom_eq {F G : SheafOfModules.{u} (structureSheafRing Z)}
    (σ : SheafOfModules.unit (structureSheafRing Z) ⟶ F) :
    mulSectionHom Z σ (G := G) =
      (tensorSheafUnitLeftIso Z G).inv ≫ ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map (σ ×ₘ 𝟙 G) := by
  refine Eq.trans (congrArg (fun k => k ≫ (σ ▷ G)) (congrArg Iso.inv (leftUnitorIso_eq Z G))) ?_
  exact congrArg (fun k => (tensorSheafUnitLeftIso Z G).inv ≫ k)
    ((tensorHom_id σ G).symm.trans (tensorHom_eq Z σ (𝟙 G)))

end Monoidal

variable (Z : RingedSpace.{u, u})

/-- **Multiplication by a global section `σ : 𝒪_X ⟶ ℱ`**, `𝒢 ⟶ ℱ ⊗_{𝒪_X} 𝒢`, with its target
ascribed at the tensor bifunctor `Stacks.RingedSpace.tensorSheaf` rather than at the monoidal
product of `Stacks.SheafOfModules.OnSpace.monoidal`.  The two are equal by `rfl`, but `rw`
refuses a goal containing the monoidal spelling, because the monoidal structure is keyed on the
semireducible `structureSheafRing`; the crossing happens once here. -/
def mulSectionTensor {F G : SheafOfModules.{u} (structureRingSheaf Z)}
    (σ : SheafOfModules.unit (structureRingSheaf Z) ⟶ F) :
    G ⟶ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Z.sheaf))).obj (F, G) :=
  mulSectionHom Z σ

/-- `mulSectionTensor_eq` is `mulSectionHom_eq` in the ascribed spelling. -/
theorem mulSectionTensor_eq {F G : SheafOfModules.{u} (structureRingSheaf Z)}
    (σ : SheafOfModules.unit (structureRingSheaf Z) ⟶ F) :
    mulSectionTensor Z σ (G := G) =
      (tensorSheafUnitLeftIso Z G).inv ≫ ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map (σ ×ₘ 𝟙 G) :=
  mulSectionHom_eq Z σ

/-! ### Functoriality of the tensor product sheaf -/

/-- Functoriality of the tensor bifunctor, with the composite in the product category
computed. -/
theorem tensorSheaf_map_comp {A B C D E F : SheafOfModules.{u} (structureRingSheaf Z)}
    (a : A ⟶ B) (b : B ⟶ C) (c : D ⟶ E) (d : E ⟶ F) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
      (a ×ₘ c) ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Z.sheaf))).map (b ×ₘ d) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
        ((a ≫ b) ×ₘ (c ≫ d)) :=
  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    Z.sheaf))).map_comp _ _).symm

/-- Functoriality of the tensor bifunctor in the first variable alone. -/
theorem tensorSheaf_map_comp_left {A B C D : SheafOfModules.{u} (structureRingSheaf Z)}
    (a : A ⟶ B) (b : B ⟶ C) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
      (a ×ₘ 𝟙 D) ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Z.sheaf))).map (b ×ₘ 𝟙 D) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
        ((a ≫ b) ×ₘ 𝟙 D) :=
  (tensorSheaf_map_comp Z a b (𝟙 D) (𝟙 D)).trans
    (congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Z.sheaf))).map (Prod.hom_ext rfl (Category.comp_id (𝟙 D))))

/-- The tensor bifunctor at a pair of identities is the identity. -/
theorem tensorSheaf_map_id_left (A D : SheafOfModules.{u} (structureRingSheaf Z)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
      (𝟙 A ×ₘ 𝟙 D) = 𝟙 (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj (A, D)) :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map_id
    (A, D)

/-- Naturality of the inverse left unitor of the tensor product sheaf. -/
theorem tensorSheafUnitLeftIso_inv_naturality
    {A A' : SheafOfModules.{u} (structureRingSheaf Z)} (u : A ⟶ A') :
    (tensorSheafUnitLeftIso Z A).inv ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf))).map (𝟙 (SheafOfModules.unit (structureRingSheaf Z)) ×ₘ u) =
      u ≫ (tensorSheafUnitLeftIso Z A').inv :=
  (Iso.inv_comp_eq (tensorSheafUnitLeftIso Z A)).2
    (((Iso.eq_comp_inv (tensorSheafUnitLeftIso Z A')).2
      (tensorSheafUnitLeftIso_naturality Z u)).trans (Category.assoc _ _ _))

/-- **Multiplication by a global section is natural in the module it multiplies**, and changing
the section by a morphism of the multiplying module is composition with it. -/
@[reassoc]
theorem mulSectionTensor_comp_map {F F' G G' : SheafOfModules.{u} (structureRingSheaf Z)}
    (σ : SheafOfModules.unit (structureRingSheaf Z) ⟶ F) (a : F ⟶ F') (b : G ⟶ G') :
    mulSectionTensor Z σ (G := G) ≫ ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map (a ×ₘ b) =
      b ≫ mulSectionTensor Z (σ ≫ a) (G := G') := by
  rw [mulSectionTensor_eq, mulSectionTensor_eq, Category.assoc, tensorSheaf_map_comp,
    ← Category.assoc, ← tensorSheafUnitLeftIso_inv_naturality, Category.assoc,
    tensorSheaf_map_comp]
  exact congrArg (fun k => (tensorSheafUnitLeftIso Z G).inv ≫ ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map k) (by simp)

/-! ### Multiplication by a global section and pullback -/

variable {W : RingedSpace.{u, u}} (g : W ⟶ Z)

/-- **Naturality of the comparison of [Stacks, Tag 01CD] in the first variable**, written for the
tensor bifunctor rather than for a whiskering. -/
theorem comparison_naturality_left {F F' G : SheafOfModules.{u} (structureRingSheaf Z)}
    (v : F ⟶ F') :
    (pullbackFunctor g).map (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map (v ×ₘ 𝟙 G)) ≫
      comparison g F' G =
      comparison g F G ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          W.sheaf))).map ((pullbackFunctor g).map v ×ₘ 𝟙 ((pullbackFunctor g).obj G)) := by
  refine Eq.trans ((comparisonNatTrans g).naturality (v ×ₘ 𝟙 G)) ?_
  exact congrArg (fun k => comparison g F G ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf))).map
        ((pullbackFunctor g).map v ×ₘ k)) ((pullbackFunctor g).map_id G)

/-- **The left-unitor coherence of [Stacks, Tag 01CD], solved for the comparison.**  The
inverse left unitor pulled back, followed by the comparison at `(𝒪_Y, 𝒢)`, is the inverse left
unitor on the source followed by `ν⁻¹ ⊗ 𝟙`.  This is
`Stacks.RingedSpace.comparison_leftUnitor` with both unitors inverted. -/
theorem map_leftUnitor_inv_comp_comparison (G : SheafOfModules.{u} (structureRingSheaf Z)) :
    (pullbackFunctor g).map (tensorSheafUnitLeftIso Z G).inv ≫
        comparison g (SheafOfModules.unit (structureRingSheaf Z)) G =
      (tensorSheafUnitLeftIso W ((pullbackFunctor g).obj G)).inv ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          W.sheaf))).map ((pullbackObjUnitIso g).inv ×ₘ 𝟙 ((pullbackFunctor g).obj G)) := by
  have hmm : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    W.sheaf))).map ((pullbackObjUnitIso g).hom ×ₘ 𝟙 ((pullbackFunctor g).obj G)) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf))).map
        ((pullbackObjUnitIso g).inv ×ₘ 𝟙 ((pullbackFunctor g).obj G)) =
      𝟙 _ := by
    rw [tensorSheaf_map_comp_left, Iso.hom_inv_id, tensorSheaf_map_id_left]
  have hco := comparison_leftUnitor g G
  refine (Iso.cancel_iso_hom_left
    ((pullbackFunctor g).mapIso (tensorSheafUnitLeftIso Z G)) _ _).mp ?_
  simp only [Functor.mapIso_hom]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← hco, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, hmm]
  exact (Category.comp_id _).symm

/-- **Multiplication by a global section commutes with pullback.**  For a morphism `f` of ringed
spaces, the pullback of multiplication by `σ : 𝒪_Y ⟶ ℱ`, followed by the comparison of
[Stacks, Tag 01CD], is multiplication by the section `ν⁻¹ ≫ f^*σ` of `f^*ℱ`. -/
@[reassoc]
theorem pullback_mulSectionTensor {F G : SheafOfModules.{u} (structureRingSheaf Z)}
    (σ : SheafOfModules.unit (structureRingSheaf Z) ⟶ F) :
    (pullbackFunctor g).map (mulSectionTensor Z σ (G := G)) ≫ comparison g F G =
      mulSectionTensor W ((pullbackObjUnitIso g).inv ≫ (pullbackFunctor g).map σ) := by
  rw [mulSectionTensor_eq, mulSectionTensor_eq, CategoryTheory.Functor.map_comp,
    Category.assoc, comparison_naturality_left Z g σ, ← tensorSheaf_map_comp_left,
    ← Category.assoc, map_leftUnitor_inv_comp_comparison, Category.assoc]

end Stacks.RingedSpace


namespace Stacks.AlgebraicGeometry.RestrictMulSection

open Stacks.RingedSpace (pullbackObjUnitIso)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The adjoint transpose, along `restrictAdjunction`, of the right-hand side of
`restrictUnitIso_eq`: `restrictFunctorIsoPullback` is `Adjunction.leftAdjointUniq`, so the
transpose of its component is the unit of `pullbackPushforwardAdjunction`, and the transpose of
`ν` is `SheafOfModules.unitToPushforwardObjUnit`, the morphism `𝒪_Y ⟶ f_*𝒪_X` given by `f^♯`. -/
private theorem homEquiv_restrictFunctorIsoPullback_comp_pullbackObjUnitIso :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app
            (SheafOfModules.unit Y.ringCatSheaf) ≫
          (pullbackObjUnitIso f.toLRSHom.toShHom).hom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  refine Eq.trans (Adjunction.homEquiv_naturality_right _ _ _) ?_
  refine Eq.trans (congrArg (fun k => k ≫ (Scheme.Modules.pushforward f).map
      (pullbackObjUnitIso f.toLRSHom.toShHom).hom)
    (Adjunction.homEquiv_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (SheafOfModules.unit Y.ringCatSheaf))) ?_
  refine Eq.trans (Adjunction.homEquiv_unit
    (Scheme.Modules.pullbackPushforwardAdjunction f) _ _ _).symm ?_
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom

/-- The adjoint transpose, along `restrictAdjunction`, of
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso` is `f^♯` as well: on sections over `U` it is
the restriction map `Γ(Y, U) ⟶ Γ(Y, f ''ᵁ f ⁻¹ᵁ U)` followed by `(f.appIso (f ⁻¹ᵁ U)).hom`, and
`AlgebraicGeometry.Scheme.Hom.app_appIso_inv` says that composite is `f.app U`. -/
private theorem homEquiv_restrictUnitIso :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
        (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  refine Eq.trans (Adjunction.homEquiv_unit (Scheme.Modules.restrictAdjunction f) _ _ _) ?_
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  exact congr($(((Iso.comp_inv_eq _).mp (Scheme.Hom.app_appIso_inv f U)).symm) x)

/-- **Mathlib's `𝒪_Y|_X ≅ 𝒪_X` is the comparison `f^*𝒪_Y ≅ 𝒪_X` conjugated by
`restrictFunctorIsoPullback`.**  Both sides are morphisms out of `(restrictFunctor f).obj 𝒪_Y`,
so they are compared by transposing along `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`,
where both become the structure morphism `f^♯ : 𝒪_Y ⟶ f_*𝒪_X`.

This is the identity that lets the left-unitor coherence
`Stacks.RingedSpace.comparison_leftUnitor`, proved for the pullback functor, be read at
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`. -/
theorem restrictUnitIso_eq :
    Scheme.Modules.restrictUnitIso f =
      (Scheme.Modules.restrictFunctorIsoPullback f).app
          (SheafOfModules.unit Y.ringCatSheaf) ≪≫
        pullbackObjUnitIso f.toLRSHom.toShHom :=
  Iso.ext (((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
    ((homEquiv_restrictUnitIso f).trans
      (homEquiv_restrictFunctorIsoPullback_comp_pullbackObjUnitIso f).symm))

/-- The inverse form of `restrictUnitIso_eq`, which is what the transition square uses. -/
theorem restrictUnitIso_inv_eq :
    (Scheme.Modules.restrictUnitIso f).inv =
      (pullbackObjUnitIso f.toLRSHom.toShHom).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
          (SheafOfModules.unit Y.ringCatSheaf) :=
  congrArg Iso.inv (restrictUnitIso_eq f)

end Stacks.AlgebraicGeometry.RestrictMulSection


namespace Stacks.AlgebraicGeometry.ReflexivePowers

open Stacks.RingedSpace (mulSectionTensor pullbackObjUnitIso comparison)

variable {X : Scheme.{u}}

/-! ### Multiplication by a global section and restriction to an open -/

/-- The three factors of `tensorSheafRestrictIso`, written out. -/
theorem tensorSheafRestrictIso_hom (V : X.Opens) (A B : X.Modules) :
    (tensorSheafRestrictIso V A B).hom =
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (A)).obj (B))) ≫
        comparison V.ι.toLRSHom.toShHom A B ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            V.toScheme.sheaf))).map
            ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app A ×ₘ
              (Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app B) :=
  rfl

/-- `Stacks.RingedSpace.pullback_mulSectionTensor` at an open immersion of schemes, restated in
the `AlgebraicGeometry.Scheme.Modules.pullback` spelling that
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is typed over. -/
@[reassoc]
theorem pullback_mulSectionTensor_restrict (V : X.Opens) {F G : X.Modules}
    (σ : SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    (Scheme.Modules.pullback V.ι).map (mulSectionTensor X.toRingedSpace σ (G := G)) ≫
        comparison V.ι.toLRSHom.toShHom F G =
      mulSectionTensor V.toScheme.toRingedSpace
        ((pullbackObjUnitIso V.ι.toLRSHom.toShHom).inv ≫
          (Scheme.Modules.pullback V.ι).map σ) :=
  Stacks.RingedSpace.pullback_mulSectionTensor X.toRingedSpace V.ι.toLRSHom.toShHom σ

/-- **The section that multiplication by `σ` becomes over `V`.**  Transporting `f^*σ` across
`Stacks.AlgebraicGeometry.RestrictMulSection.restrictUnitIso_eq` turns the pullback spelling into
the restriction spelling: it is `(restrictUnitIso V.ι).inv ≫ σ|_V`. -/
theorem pullbackObjUnit_comp_map_comp_restrictFunctorIsoPullback_inv (V : X.Opens)
    {F : X.Modules} (σ : SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    ((pullbackObjUnitIso V.ι.toLRSHom.toShHom).inv ≫ (Scheme.Modules.pullback V.ι).map σ) ≫
        (Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app F =
      (Scheme.Modules.restrictUnitIso V.ι).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map σ := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k => _ ≫ k)
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.naturality σ)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun k => k ≫ (Scheme.Modules.restrictFunctor V.ι).map σ)
    (Stacks.AlgebraicGeometry.RestrictMulSection.restrictUnitIso_inv_eq V.ι).symm

/-- **Multiplication by a global section commutes with restriction to an open.**  Restricting
multiplication by `σ : 𝒪_X ⟶ ℱ` to `V` and comparing the restricted tensor product by
[Stacks, Tag 01CD] gives multiplication by the restricted section on `V`.

This is the left-unitor coherence of [Stacks, Tag 01CD] at
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, obtained from
`Stacks.RingedSpace.pullback_mulSectionTensor` by conjugating with `restrictFunctorIsoPullback`;
the identification of the unit objects it needs is
`Stacks.AlgebraicGeometry.RestrictMulSection.restrictUnitIso_eq`.

Every step is supplied in term mode: the type of `tensorSheafRestrictIso` is not type-correct at
`implicit` transparency — it applies the tensor product sheaf, whose arguments are spelled over
`structureSheafRing`, to modules spelled over `V.toScheme.Modules` — so `rw` refuses any goal
mentioning it. -/
theorem restrict_mulSectionTensor (V : X.Opens) {F G : X.Modules}
    (σ : SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    (Scheme.Modules.restrictFunctor V.ι).map (mulSectionTensor X.toRingedSpace σ (G := G)) ≫
        (tensorSheafRestrictIso V F G).hom =
      mulSectionTensor V.toScheme.toRingedSpace
        ((Scheme.Modules.restrictUnitIso V.ι).inv ≫
          (Scheme.Modules.restrictFunctor V.ι).map σ) := by
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.naturality
    (mulSectionTensor X.toRingedSpace σ (G := G))
  have hP := pullback_mulSectionTensor_restrict V σ (G := G)
  have hM := Stacks.RingedSpace.mulSectionTensor_comp_map V.toScheme.toRingedSpace
    ((pullbackObjUnitIso V.ι.toLRSHom.toShHom).inv ≫ (Scheme.Modules.pullback V.ι).map σ)
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app F)
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app G)
  have hcan : (Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app G ≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app G = 𝟙 _ := by
    rw [← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
  have hσ := pullbackObjUnit_comp_map_comp_restrictFunctorIsoPullback_inv V σ
  refine Eq.trans (congrArg (fun k => (Scheme.Modules.restrictFunctor V.ι).map
      (mulSectionTensor X.toRingedSpace σ (G := G)) ≫ k)
    (tensorSheafRestrictIso_hom V F G)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ _) hnat) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k => _ ≫ k) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun k => _ ≫ k ≫ _) hP) ?_
  refine Eq.trans (congrArg (fun k => _ ≫ k) hM) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ _) hcan) ?_
  refine Eq.trans (Category.id_comp _) ?_
  exact congrArg (fun k => mulSectionTensor V.toScheme.toRingedSpace k
    (G := (Scheme.Modules.restrictFunctor V.ι).obj G)) hσ


/-! ### The transition square of Tag 0EBN, with multiplication by the restricted section -/

/-- **The restriction `s|_V` of a global section** `s ∈ Γ(X, ℱ)` to an open `V`: the section of
`ℱ|_V` corresponding under `SheafOfModules.unitHomEquiv` to the restriction of the morphism
`𝒪_X ⟶ ℱ` determined by `s`, read through `𝒪_X|_V ≅ 𝒪_V`. -/
def restrictSection (V : X.Opens) (F : X.Modules) (s : F.sections) :
    ((Scheme.Modules.restrictFunctor V.ι).obj F).sections :=
  ((Scheme.Modules.restrictFunctor V.ι).obj F).unitHomEquiv
    ((Scheme.Modules.restrictUnitIso V.ι).inv ≫
      (Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s))

/-- The morphism `𝒪_V ⟶ ℱ|_V` determined by the restricted section is the restriction of the
morphism determined by `s`, read through `𝒪_X|_V ≅ 𝒪_V`. -/
theorem unitHomEquiv_symm_restrictSection (V : X.Opens) (F : X.Modules) (s : F.sections) :
    ((Scheme.Modules.restrictFunctor V.ι).obj F).unitHomEquiv.symm (restrictSection V F s) =
      (Scheme.Modules.restrictUnitIso V.ι).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s) :=
  Equiv.symm_apply_apply _ _

/-- **Multiplication by a global section commutes with restriction to an open**, written for
`mulSection` and the restricted section `s|_V`. -/
theorem restrict_mulSection (V : X.Opens) (F G : X.Modules) (s : F.sections) :
    (Scheme.Modules.restrictFunctor V.ι).map (mulSection F s G) ≫
        (tensorSheafRestrictIso V F G).hom =
      mulSection ((Scheme.Modules.restrictFunctor V.ι).obj F) (restrictSection V F s)
        ((Scheme.Modules.restrictFunctor V.ι).obj G) :=
  (restrict_mulSectionTensor V (F := F) (G := G) (F.unitHomEquiv.symm s)).trans
    (congrArg (fun k => mulSectionTensor V.toScheme.toRingedSpace k
      (G := (Scheme.Modules.restrictFunctor V.ι).obj G))
      (unitHomEquiv_symm_restrictSection V F s).symm)

/-- The native tensor bifunctor maps isomorphism pairs by their forward maps. -/
theorem tensorSheafMapIso_hom {Y : Scheme.{u}} {A A' B B' : Y.Modules} (eA : A ≅ A')
    (eB : B ≅ B') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Y.sheaf)).mapIso (X := (A, B)) (Y := (A', B')) (Iso.prod eA eB)).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Y.sheaf)).map (eA.hom ×ₘ eB.hom) :=
  rfl

/-- **Multiplication by a global section is natural in the module it multiplies.** -/
theorem mulSection_comp_tensorSheafMapIso {Y : Scheme.{u}} (L : Y.Modules) (t : L.sections)
    {G G' : Y.Modules} (e : G ≅ G') :
    mulSection L t G ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Y.sheaf)).mapIso (X := (L, G)) (Y := (L, G')) (Iso.prod (Iso.refl L) e)).hom =
      e.hom ≫ mulSection L t G' := by
  refine Eq.trans (congrArg (fun k => mulSection L t G ≫ k)
    (tensorSheafMapIso_hom (Y := Y) (Iso.refl L) e)) ?_
  refine Eq.trans (Stacks.RingedSpace.mulSectionTensor_comp_map Y.toRingedSpace
    (L.unitHomEquiv.symm t) (𝟙 L) e.hom) ?_
  exact congrArg (fun k => e.hom ≫ mulSectionTensor Y.toRingedSpace k (G := G'))
    (Category.comp_id _)

/-- The two factors of `restrictTensorPowerIso`, written out. -/
theorem restrictTensorPowerIso_hom (F : X.Modules) (V : X.Opens) {n : ℕ}
    (e : (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1)) ≅
      tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)) :
    (restrictTensorPowerIso F V e).hom =
      (tensorSheafRestrictIso V F (reflexivePower F (n + 1))).hom ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          V.toScheme.sheaf)).mapIso
            (X := ((Scheme.Modules.restrictFunctor V.ι).obj F,
              (Scheme.Modules.restrictFunctor V.ι).obj (reflexivePower F (n + 1))))
            (Y := ((Scheme.Modules.restrictFunctor V.ι).obj F,
              tensorPower (X := V.toScheme) ((Scheme.Modules.restrictFunctor V.ι).obj F) (n + 1)))
            (Iso.prod (Iso.refl ((Scheme.Modules.restrictFunctor V.ι).obj F)) e)).hom :=
  rfl

/-- **The full transition square of the colimit clause of [Stacks, Tag 0EBN] over an open where
`ℱ` is invertible.**  For every `n` the restricted transition `ℱ^{[n]}|_V ⟶ ℱ^{[n + 1]}|_V`,
followed by the comparison at `n + 1`, is the comparison at `n` followed by the transition
`(ℱ|_V)^{⊗ n} ⟶ (ℱ|_V)^{⊗ (n + 1)}` of the ordinary tensor-power system of `ℱ|_V` and the
restricted section `s|_V`.

So over `V` the system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯` of [Stacks, Tag 0EBN] is *isomorphic as a
system* to `𝒪_V →^{s|_V} ℱ|_V →^{s|_V} (ℱ|_V)^{⊗ 2} → ⋯`, which is the system
[Stacks, Tag 01PW] is about.  The reflexive hull contributes nothing: it is cancelled by
`restrict_toDoubleDual_comp_restrictPowerSuccIso_hom`, and the passage from the restriction of
multiplication by `s` to multiplication by `s|_V` is `restrict_mulSection`. -/
theorem restrict_reflexivePowerTransition_comp_restrictPowerIso_hom' [IsIntegral X]
    [IsLocallyNoetherian X] (F : X.Modules) (V : X.Opens)
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (s : F.sections) (n : ℕ) :
    (Scheme.Modules.restrictFunctor V.ι).map (reflexivePowerTransition F s n) ≫
        (restrictPowerIso F V hF hV (n + 1)).hom =
      (restrictPowerIso F V hF hV n).hom ≫
        tensorPowerTransition ((Scheme.Modules.restrictFunctor V.ι).obj F)
          (restrictSection V F s) n := by
  cases n with
  | zero =>
      refine Eq.trans (Category.comp_id _) (Eq.trans ?_ (congrArg (fun k =>
        (Scheme.Modules.restrictUnitIso V.ι).hom ≫ k)
        (unitHomEquiv_symm_restrictSection V F s)).symm)
      exact (Iso.hom_inv_id_assoc (Scheme.Modules.restrictUnitIso V.ι) _).symm
  | succ m =>
      refine Eq.trans
        (restrict_reflexivePowerTransition_comp_restrictPowerIso_hom F V hF hV s m) ?_
      refine Eq.trans (congrArg (fun k => (Scheme.Modules.restrictFunctor V.ι).map
        (mulSection F s (reflexivePower F (m + 1))) ≫ k)
        (restrictTensorPowerIso_hom F V (restrictPowerIso F V hF hV (m + 1)))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun k => k ≫ _)
        (restrict_mulSection V F (reflexivePower F (m + 1)) s)) ?_
      exact mulSection_comp_tensorSheafMapIso ((Scheme.Modules.restrictFunctor V.ι).obj F)
        (restrictSection V F s) (restrictPowerIso F V hF hV (m + 1))

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
