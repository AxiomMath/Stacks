module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Comparison
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.TargetStalk

/-!
# The quasi-coherence clause of Stacks Tag 01SA

Let `g : T ⟶ S` be a morphism of schemes and `A` a sheaf of commutative `𝒪_S`-algebras.
`Stacks.ModuleStalkTensor.comparison g A` is the canonical morphism of `𝒪_T`-modules
`g^*A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`, and by
`Stacks.ModuleStalkTensor.isQuasicoherent_of_isIso_comparison` the
`algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA] is exactly its invertibility.

**This file proves it invertible**, and so discharges that clause:
`Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent` says that the pullback of a
quasi-coherent algebra sheaf along an *arbitrary* morphism of schemes is quasi-coherent.  No
affineness, Noetherian, finiteness or flatness hypothesis is used anywhere in this file or in
the two files it rests on.

## Main definitions

* `Stacks.AlgebraPullbackQcoh.targetModel`: the model of the comparison's map on the stalk at
  `t`, an `𝒪_{T,t}`-linear equivalence
  `𝒪_{T,t} ⊗_{𝒪_{S,g t}} A_{g t} ≅ (g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T)_t`.
* `Stacks.AlgebraPullbackQcoh.sourceStalkEquiv`: the stalk of the module pullback,
  `(g^*A)_t ≅ 𝒪_{T,t} ⊗_{𝒪_{S,g t}} A_{g t}`, at the scheme spelling.
* `Stacks.AlgebraPullbackQcoh.comparisonStalkMap`: the comparison's map on the stalk at `t`,
  as a linear map over the stalk of the structure sheaf taken in `CommRingCat`.

## Main results

* `Stacks.AlgebraPullbackQcoh.comparisonStalkMap_comp`: **the identity that does the work** —
  the comparison's map on the stalk at `t`, precomposed with the identification of the stalk of
  the module pullback, *is* `targetModel`.
* `Stacks.AlgebraPullbackQcoh.bijective_comparisonStalkMap`: the comparison is bijective on
  the stalk at every point.
* `Stacks.AlgebraPullbackQcoh.isIso_comparison`: the comparison is invertible.
* `Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent`: **the
  `algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA].**

## Route

Invertibility is checked on stalks, by
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk`, and both stalks are tensor
products over the same ring with the same algebra instance:

* the source is `Stacks.PullbackTensorIso.pullbackStalkEquiv` at the ringed-space morphism
  underlying `g`, which carries `1 ⊗ germ a` to the germ of the pullback-unit image of `a`
  (`Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul`).  Nothing has to be generalised for
  this: the ring sheaf, the structure-sheaf morphism, the stalk ring map and the module
  pullback of `T.toRingedSpace ⟶ S.toRingedSpace` are the scheme-level ones by `rfl`;
* the target is `Stacks.AlgebraPullbackQcoh.targetStalkLinearEquiv` composed with the
  identification of the stalk of the underlying module of an algebra sheaf with its stalk in
  `CommRingCat`, `Stacks.AlgebraPullbackQcoh.algebraStalkLinearEquiv`.  On `1 ⊗ germ a` it
  gives the germ of the `algebraPullbackMap`-image of the inverse-image-unit image of `a`;
* the comparison on germs is
  `Stacks.AlgebraPullbackQcoh.germ_comparison_moduleUnit`, which gives the same answer.

Both sides being `𝒪_{T,t}`-linear, `Stacks.PullbackTensorIso.tmul_one_ext` reduces their
equality to the elements `1 ⊗ m`, and every `m` is a germ.  The model being invertible, so is
the comparison's map on stalks.

## What is not done

**Tag 01SA is not fully proved and no project tag attribute is attached here.**  The statement
of Tag 01SA is a single nine-field structure carrying one unqualified `stacks 01SA` attribute, so
nothing can be tagged until all nine fields are proved.  With this file the fields with content
are seven of nine: the two still open are `baseChangeIso`, the compatibility of the anti-equivalence
with arbitrary base change, and `baseChangeIso_canonical`, which identifies that isomorphism
with the canonical comparison.

For those two, what is built is
`Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom` together with
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap_comp_baseChangeAlgebraHom`, which is
precisely the equation `baseChangeIso_canonical` asserts; so `baseChangeIso_canonical` reduces
to the base-change isomorphism *being* `baseChangeAlgebraHom`, and `baseChangeIso` reduces to
`baseChangeAlgebraHom` being invertible for `X` affine over `S`, naturally in `X`.  Neither of
those is proved here or anywhere in the development.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped TensorProduct

universe u

namespace Stacks.AlgebraPullbackQcoh

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.PullbackTensorIso
open Stacks.ModuleStalkTensor

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : AlgebraSheaf S) (t : T)

attribute [local instance] algebraStalkAlgebra schemeStalkAlgebra

/-- **The model of the comparison's map on the stalk at `t`**:
`𝒪_{T,t} ⊗_{𝒪_{S,g t}} A_{g t} ≅ (g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T)_t`, obtained from
`Stacks.AlgebraPullbackQcoh.targetStalkLinearEquiv` by replacing the stalk of `A` in
`CommRingCat` with the stalk of its underlying module on both sides. -/
def targetModel :
    Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t ⊗[
        Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk S.toRingedSpace (g.base t)]
          moduleAbStalk A (g.base t)
      ≃ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t]
      moduleAbStalk ((algebraPullback g).obj A) t :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
      (algebraStalkLinearEquiv A (g.base t))).symm.trans
    ((targetStalkLinearEquiv g A t).trans
      (algebraStalkLinearEquiv ((algebraPullback g).obj A) t))

/-- **The model on elements.**  It carries `1 ⊗ germ a` to the germ of the image under
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap` of the inverse-image-unit image of `a`. -/
lemma targetModel_one_tmul_germ (V : S.Opens) (hV : g.base t ∈ V)
    (a : A.right.obj.obj (op V)) :
    targetModel g A t ((1 : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace
      t) ⊗ₜ
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (underlyingModuleSheaf A).val.presheaf V (g.base t) hV a) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (underlyingModuleSheaf ((algebraPullback g).obj A)).val.presheaf
        ((Opens.map g.base).obj V) t hV
        (((algebraPullbackMap g).app A).hom.app (op ((Opens.map g.base).obj V))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
            A.right).hom.app (op V) a)) := by
  rw [targetModel, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_symm_tmul, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, algebraStalkLinearEquiv_symm_germ]
  exact (congrArg (algebraStalkLinearEquiv ((algebraPullback g).obj A) t)
      (targetStalkIso_hom_one_tmul_germ g A t V hV a)).trans
    (algebraStalkAddEquiv_germ ((algebraPullback g).obj A) t _ hV _)

/-- **The stalk of the module pullback**, `(g^*A)_t ≅ 𝒪_{T,t} ⊗_{𝒪_{S,g t}} A_{g t}`, with the
point of `S` spelled `g.base t`.  This is `Stacks.PullbackTensorIso.pullbackStalkEquiv` at the
ringed-space morphism underlying `g`, which applies with no bridge. -/
def sourceStalkEquiv :
    Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t ⊗[
        Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk S.toRingedSpace (g.base t)]
          moduleAbStalk A (g.base t)
      ≃ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t]
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk T.toRingedSpace
        (pullbackSheaf (ringedSpaceHom g) (underlyingModuleSheaf A)).val t :=
  pullbackStalkEquiv (ringedSpaceHom g) t (underlyingModuleSheaf A)

/-- **The stalk of the module pullback on elements.**  It carries `1 ⊗ germ a` to the germ of
the image of `a` under the unit of the module pullback/pushforward adjunction of `g`. -/
lemma sourceStalkEquiv_one_tmul_germ (V : S.Opens) (hV : g.base t ∈ V)
    (a : A.right.obj.obj (op V)) :
    sourceStalkEquiv g A t ((1 : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
      T.toRingedSpace t) ⊗ₜ
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (underlyingModuleSheaf A).val.presheaf V (g.base t) hV a) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A)).presheaf
        ((Opens.map g.base).obj V) t hV
        (PresheafOfModules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (AlgebraSheaf.underlyingModule A)).val (op V) a) :=
  pullbackStalkEquiv_one_tmul (ringedSpaceHom g) t (underlyingModuleSheaf A) V hV a

/-- The comparison morphism of the quasi-coherence clause of [Stacks, Tag 01SA], read on the
stalk at `t` as a linear map over the stalk of the structure sheaf of `T` taken in
`CommRingCat`. -/
def comparisonStalkMap :
    Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk T.toRingedSpace
        (pullbackSheaf (ringedSpaceHom g) (underlyingModuleSheaf A)).val t
      →ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t]
      moduleAbStalk ((algebraPullback g).obj A) t :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL T.toRingedSpace _ _ (comparison g A).val t

/-- **The comparison's map on stalks, on the elements `1 ⊗ germ a`.**  It gives the germ of
the image under `Stacks.AffineAlgebraEquivalence.algebraPullbackMap` of the
inverse-image-unit image of `a` — the same value as the model. -/
lemma comparisonStalkMap_germ (V : S.Opens) (hV : g.base t ∈ V)
    (a : A.right.obj.obj (op V)) :
    comparisonStalkMap g A t
        (sourceStalkEquiv g A t ((1 : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
          T.toRingedSpace t) ⊗ₜ
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (underlyingModuleSheaf A).val.presheaf V (g.base t) hV a)) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (underlyingModuleSheaf ((algebraPullback g).obj A)).val.presheaf
        ((Opens.map g.base).obj V) t hV
        (((algebraPullbackMap g).app A).hom.app (op ((Opens.map g.base).obj V))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
            A.right).hom.app (op V) a)) :=
  (congrArg (comparisonStalkMap g A t) (sourceStalkEquiv_one_tmul_germ g A t V hV a)).trans
    (germ_comparison_moduleUnit g A t V hV a)

/-- **The comparison induces the model on the stalk at `t`.**  Both sides are
`𝒪_{T,t}`-linear maps out of `𝒪_{T,t} ⊗_{𝒪_{S,g t}} A_{g t}`, so they agree as soon as they
agree on the elements `1 ⊗ m`; there `m` is a germ, and on a germ both give the germ of the
`algebraPullbackMap`-image of the inverse-image-unit image of the section. -/
lemma comparisonStalkMap_comp :
    comparisonStalkMap g A t ∘ₗ (sourceStalkEquiv g A t).toLinearMap =
      (targetModel g A t).toLinearMap := by
  refine tmul_one_ext fun p => ?_
  obtain ⟨V, hV, a, hp⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (underlyingModuleSheaf A).val.presheaf p
  rw [← hp]
  exact (comparisonStalkMap_germ g A t V hV a).trans
    (targetModel_one_tmul_germ g A t V hV a).symm

/-- **The comparison is bijective on the stalk at every point**: it is the model, conjugated
by an isomorphism. -/
lemma bijective_comparisonStalkMap : Function.Bijective (comparisonStalkMap g A t) := by
  have h : (comparisonStalkMap g A t : _ → _) =
      (targetModel g A t) ∘ (sourceStalkEquiv g A t).symm := by
    funext w
    have e := LinearMap.congr_fun (comparisonStalkMap_comp g A t)
      ((sourceStalkEquiv g A t).symm w)
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] at e
    exact e
  rw [h]
  exact (targetModel g A t).bijective.comp (sourceStalkEquiv g A t).symm.bijective

/-- **The comparison morphism `g^*A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is invertible**, for an arbitrary
morphism of schemes and an arbitrary sheaf of commutative `𝒪_S`-algebras. -/
theorem isIso_comparison : IsIso (comparison g A) :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk (comparison g A) fun t' =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_comparisonStalkMap g A t')

/-- **The `algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA].**  The pullback of a
quasi-coherent sheaf of commutative `𝒪_S`-algebras along an arbitrary morphism of schemes
`g : T ⟶ S` is quasi-coherent.

The underlying `𝒪_T`-module of the pullback is the inverse image of the underlying
`𝒪_S`-module by `isIso_comparison`, and the inverse image of a quasi-coherent module is
quasi-coherent by [Stacks, Tag 01BG].

**No project tag attribute is attached**: the statement of Tag 01SA is a single nine-field
structure carrying one unqualified tag, and two of its fields are still open; see the module docstring. -/
theorem algebraPullback_isQuasicoherent (hA : AlgebraSheaf.IsQuasicoherent A) :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  have := hA
  isQuasicoherent_of_isIso_comparison g A (isIso_comparison g A)

end Stacks.AlgebraPullbackQcoh

end
