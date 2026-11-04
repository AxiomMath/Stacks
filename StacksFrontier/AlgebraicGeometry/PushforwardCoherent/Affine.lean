module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# The direct image along a finite morphism of affine schemes is of finite type

Let `g : W ⟶ V` be a morphism of affine schemes whose map on global sections is a finite ring
map, and let `N` be a quasi-coherent `𝒪_W`-module of finite type. This file proves that
`g_* N` is an `𝒪_V`-module of finite type. It is the algebraic core of the second assertion of
[Stacks, Tag 01Y6]: once `V = Spec A` and `W = Spec B`, the module `N` is `M^~` for a finite
`B`-module `M`, the direct image is `M^~` again but read over `A`, and a finite module over a
finite `A`-algebra is a finite `A`-module ([Stacks, Tag 00GJ], `Module.Finite.trans`).

Quasi-coherence of the direct image is *not* proved here: it is already available for an
arbitrary affine morphism as
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`
([Stacks, Tag 02KG]), and it is used as a hypothesis-free instance throughout.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardCoherent.module_finite_restrictScalars`: restriction of
  scalars along a finite ring map takes a finite module to a finite module. This is
  [Stacks, Tag 00GJ] in the vocabulary of `ModuleCat.restrictScalars`.
* `Stacks.AlgebraicGeometry.PushforwardCoherent.finite_moduleSpecΓ`: on a spectrum, a
  quasi-coherent module of finite type has finite global sections, and
  `isFiniteType_of_finite_moduleSpecΓ` is the converse.
* `Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_specMap`: the direct
  image along `Spec.map φ`, for `φ` a finite ring map, of a quasi-coherent module of finite type
  is of finite type.
* `Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isIso`: the direct
  image along an isomorphism of schemes preserves finite type.
* `Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isAffine`: the same
  statement for an arbitrary morphism of affine schemes whose map on global sections is finite.

## Implementation notes

The passage from the `Spec` case to an arbitrary morphism of affine schemes is the one used for
quasi-coherence in `StacksFrontier/AlgebraicGeometry/AffinePushforward/Basic.lean`: factor
`g` as `W.isoSpec.hom ≫ Spec.map g.appTop ≫ V.isoSpec.inv` and conjugate. Pushforward along an
isomorphism is handled by identifying it with restriction along the inverse, through Mathlib's
`Scheme.Modules.restrictFunctorAdjCounitIso`, so that
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict` applies.

`module_finite_restrictScalars` introduces the `Algebra` and `IsScalarTower` instances that
`Module.Finite.trans` needs. They are stated *at the restricted object* rather than at the bare
carrier: the `Module` instance that the goal carries is the one packaged in
`(ModuleCat.restrictScalars φ.hom).obj M`, and an `IsScalarTower` stated through a separately
introduced `Module.compHom` instance is not the one instance search then looks for, even though
the two are definitionally equal.

`Stacks.SheafOfModules.isFiniteType_of_iso` is applied with its universe explicit. Finite type
of the source is an instance argument of that lemma, and the hypotheses available here are
stated at the `Scheme.Modules` spelling, which instance search does not unfold to
`SheafOfModules _`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/CoherentOfFiniteType.lean`.

## References

* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 00GJ](https://stacks.math.columbia.edu/tag/00GJ)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.PushforwardCoherent

/-! ### Restriction of scalars along a finite ring map -/

/-- **[Stacks, Tag 00GJ].** If `φ : A ⟶ B` is a finite ring map and `M` is a finite `B`-module,
then `M` viewed as an `A`-module is finite. -/
theorem module_finite_restrictScalars {A B : CommRingCat.{u}} (φ : A ⟶ B) (hφ : φ.hom.Finite)
    (M : ModuleCat.{u} B) [Module.Finite B M] :
    Module.Finite A ((ModuleCat.restrictScalars φ.hom).obj M) := by
  let alg : Algebra A B := φ.hom.toAlgebra
  have hAB : Module.Finite A B := hφ
  have tower : IsScalarTower A B ((ModuleCat.restrictScalars φ.hom).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hBM : Module.Finite B ((ModuleCat.restrictScalars φ.hom).obj M) := ‹Module.Finite B M›
  exact Module.Finite.trans B ((ModuleCat.restrictScalars φ.hom).obj M)

/-! ### Finite type on a spectrum is finiteness of the global sections -/

/-- **On a spectrum, a quasi-coherent module of finite type has finite global sections.** The
module is isomorphic to the `tilde` of its global sections, and `tilde` of a module is of finite
type exactly when the module is finite. -/
theorem finite_moduleSpecΓ {A : CommRingCat.{u}} (N : (Spec A).Modules) [N.IsQuasicoherent]
    [N.IsFiniteType] : Module.Finite A (moduleSpecΓFunctor.obj N) :=
  have : IsIso N.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ N).mp ‹_›
  have h : (tilde (moduleSpecΓFunctor.obj N)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso N.fromTildeΓ).symm
  (tilde_isFiniteType_iff _).mp h

/-- **On a spectrum, a quasi-coherent module with finite global sections is of finite type.**
This is the converse of `finite_moduleSpecΓ`. -/
theorem isFiniteType_of_finite_moduleSpecΓ {A : CommRingCat.{u}} (N : (Spec A).Modules)
    [N.IsQuasicoherent] (h : Module.Finite A (moduleSpecΓFunctor.obj N)) : N.IsFiniteType :=
  have hiso : IsIso N.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ N).mp ‹_›
  have hft : (tilde (moduleSpecΓFunctor.obj N)).IsFiniteType := (tilde_isFiniteType_iff _).mpr h
  @Stacks.SheafOfModules.isFiniteType_of_iso.{u} _ _ _ _ _ _ _ _ _
    (@asIso _ _ _ _ N.fromTildeΓ hiso) hft

/-! ### The direct image along a morphism of spectra -/

/-- **The direct image along `Spec.map φ`, for a finite ring map `φ`, of a quasi-coherent module
of finite type is of finite type.** Taking global sections turns the direct image into
restriction of scalars along `φ` (`Stacks.Descent.pushforwardSpecΓIso`), and restriction of
scalars along a finite ring map preserves finiteness. -/
theorem isFiniteType_pushforward_specMap {A B : CommRingCat.{u}} (φ : A ⟶ B) (hφ : φ.hom.Finite)
    (N : (Spec B).Modules) [N.IsQuasicoherent] [N.IsFiniteType] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj N).IsFiniteType :=
  have : ((Scheme.Modules.pushforward (Spec.map φ)).obj N).IsQuasicoherent :=
    AffinePushforward.isQuasicoherent_pushforward_specMap φ N
  have : Module.Finite B (moduleSpecΓFunctor.obj N) := finite_moduleSpecΓ N
  have : Module.Finite A ((moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj N) :=
    module_finite_restrictScalars φ hφ (moduleSpecΓFunctor.obj N)
  isFiniteType_of_finite_moduleSpecΓ _
    (Module.Finite.equiv ((Descent.pushforwardSpecΓIso φ).app N).symm.toLinearEquiv)

/-! ### The direct image along an isomorphism, and the affine case -/

/-- **The direct image of a module of finite type along an isomorphism of schemes is of finite
type.** The direct image along `e.hom` is restriction along `e.inv`, and restriction along an
open immersion preserves finite type. -/
theorem isFiniteType_pushforward_of_isIso {Y Z : Scheme.{u}} (e : Y ≅ Z) (N : Y.Modules)
    [N.IsFiniteType] : ((Scheme.Modules.pushforward e.hom).obj N).IsFiniteType :=
  have i₁ : (Scheme.Modules.pushforward e.inv).obj
      ((Scheme.Modules.pushforward e.hom).obj N) ≅ N :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app N ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app N ≪≫
      (Scheme.Modules.pushforwardId Y).app N
  have iso : (Scheme.Modules.restrictFunctor e.inv).obj N ≅
      (Scheme.Modules.pushforward e.hom).obj N :=
    ((Scheme.Modules.restrictFunctor e.inv).mapIso i₁).symm ≪≫
      (Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app _
  have : (N.restrict e.inv).IsFiniteType := CoherentTFAE.isFiniteType_restrict e.inv N
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} iso

/-- **The direct image along a morphism of affine schemes whose map on global sections is finite
takes quasi-coherent modules of finite type to modules of finite type.** The morphism factors as
`W.isoSpec.hom ≫ Spec.map g.appTop ≫ V.isoSpec.inv`, and each of the three factors is covered by
`isFiniteType_pushforward_of_isIso` or by `isFiniteType_pushforward_specMap`. -/
theorem isFiniteType_pushforward_of_isAffine {W V : Scheme.{u}} [IsAffine W] [IsAffine V]
    (g : W ⟶ V) (hg : g.appTop.hom.Finite) (N : W.Modules) [N.IsQuasicoherent]
    [N.IsFiniteType] : ((Scheme.Modules.pushforward g).obj N).IsFiniteType := by
  have key : g = W.isoSpec.hom ≫ (Spec.map g.appTop ≫ V.isoSpec.inv) := by
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have h₁ : ((Scheme.Modules.pushforward W.isoSpec.hom).obj N).IsFiniteType :=
    isFiniteType_pushforward_of_isIso W.isoSpec N
  have h₁' : ((Scheme.Modules.pushforward W.isoSpec.hom).obj N).IsQuasicoherent :=
    AffinePushforward.isQuasicoherent_pushforward_of_isIso W.isoSpec N
  have h₂ : ((Scheme.Modules.pushforward (Spec.map g.appTop)).obj
      ((Scheme.Modules.pushforward W.isoSpec.hom).obj N)).IsFiniteType :=
    isFiniteType_pushforward_specMap g.appTop hg _
  have h₃ : ((Scheme.Modules.pushforward V.isoSpec.symm.hom).obj
      ((Scheme.Modules.pushforward (Spec.map g.appTop)).obj
        ((Scheme.Modules.pushforward W.isoSpec.hom).obj N))).IsFiniteType :=
    isFiniteType_pushforward_of_isIso V.isoSpec.symm _
  have iso : (Scheme.Modules.pushforward V.isoSpec.symm.hom).obj
      ((Scheme.Modules.pushforward (Spec.map g.appTop)).obj
        ((Scheme.Modules.pushforward W.isoSpec.hom).obj N)) ≅
      (Scheme.Modules.pushforward g).obj N :=
    (Scheme.Modules.pushforwardComp (Spec.map g.appTop) V.isoSpec.inv).app _ ≪≫
      (Scheme.Modules.pushforwardComp W.isoSpec.hom
        (Spec.map g.appTop ≫ V.isoSpec.inv)).app N ≪≫
      (Scheme.Modules.pushforwardCongr key.symm).app N
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} iso

end Stacks.AlgebraicGeometry.PushforwardCoherent

end
