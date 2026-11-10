module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectives
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SupportedSubmoduleExtension

/-!
# The internal Hom complex into a complex of injective modules

Let `(X, 𝒪_X)` be a ringed space, `A` an `𝒪_X`-module and `I^•` a complex of injective
`𝒪_X`-modules. This file studies the complex `𝓗om(A, I^•)` of `𝒪_X`-modules, obtained by
applying the internal Hom `𝓗om(A, -)` of [Stacks, Tag 03EN] degreewise. When `I^•` is an
injective resolution of `G` its cohomology sheaves are the sheaf Ext's `𝓔xt^q(A, G)`.

The main facts are the following.

* `𝓗om(-, I)` is exact for an injective `I` ([Stacks, Tag 01DR]), so a short exact sequence
  `0 ⟶ A' ⟶ A ⟶ A'' ⟶ 0` gives a short exact sequence of complexes
  `0 ⟶ 𝓗om(A'', I^•) ⟶ 𝓗om(A, I^•) ⟶ 𝓗om(A', I^•) ⟶ 0`, hence a long exact sequence of
  cohomology sheaves;
* for a finite free `A` the complex `𝓗om(A, I^•)` is a finite direct sum of copies of `I^•`, so
  it is exact in positive degrees when `I^•` is a resolution.

## Main definitions

* `Stacks.SheafHomInjective.cx`: the complex `𝓗om(A, K^•)`.
* `Stacks.SheafHomInjective.cxMap`: the map of complexes induced by a morphism in the first
  variable.

## Main results

* `Stacks.SheafHomInjective.cx_shortExact`: the short exact sequence of complexes.
* `Stacks.SheafHomInjective.exactAt_cx_free`: exactness in positive degrees for a finite free
  first variable.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.InternalHom Stacks.PresheafOfModules.InternalHom

universe u

namespace Stacks.SheafHomInjective

variable {X : Type u} [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- The internal Hom functor `𝓗om(A, -)`. -/
abbrev SH (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology X) O A

/-- The complex `𝓗om(A, K^•)`. -/
abbrev cx (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ :=
  ((SH O A).mapHomologicalComplex _).obj K

/-- The map `𝓗om(A, K^•) ⟶ 𝓗om(A', K^•)` induced by `f : A' ⟶ A`. -/
abbrev cxMap {A A' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : A' ⟶ A)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ) :
    cx O A K ⟶ cx O A' K :=
  (NatTrans.mapHomologicalComplex (internalHomMapLeftNatTrans O f) _).app K

variable {O}

/-- The construction `cxMap` is contravariantly functorial: `cxMap g ≫ cxMap f = cxMap (f ≫ g)`. -/
theorem cxMap_comp {A A' A'' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (f : A'' ⟶ A') (g : A' ⟶ A)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ) :
    cxMap O g K ≫ cxMap O f K = cxMap O (f ≫ g) K := by
  ext n : 2
  rfl

/-- The map of complexes induced by the zero morphism is zero. -/
theorem cxMap_zero (A A' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ) :
    cxMap O (0 : A' ⟶ A) K = 0 := by
  ext n : 2
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext <| LinearMap.ext fun x => ?_
  have h : (restrFun O.obj V.unop).map (0 : A'.val ⟶ A.val) = 0 :=
    PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext <| LinearMap.ext fun _ => rfl
  change (restrFun O.obj V.unop).map (0 : A'.val ⟶ A.val) ≫ x = 0
  rw [h]
  exact zero_comp

/-- Precomposition along a monomorphism is surjective on sections of the internal Hom into an
injective module. -/
theorem surjective_internalHomMapLeft_app
    {A' A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : A' ⟶ A) [Mono f]
    (K : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) [Injective K]
    (U : Opens X) :
    Function.Surjective (((internalHomMapLeftNatTrans O f).app K).val.app (op U)) := by
  intro x
  have hinj : Injective (K.over U) :=
    Stacks.Cohomology.Localization.injective_over
      (Opens.grothendieckTopology X) _ U K
  have hmono : Mono (f.over U) := by
    change Mono ((SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf O) U).map f)
    infer_instance
  let R' := (Stacks.SheafOfModules.Tensor.ringSheaf O).over U
  let hx : A'.over U ⟶ K.over U := (SheafOfModules.fullyFaithfulForget R').preimage x
  let y : A.over U ⟶ K.over U := Injective.factorThru hx (f.over U)
  refine ⟨(SheafOfModules.forget R').map y, ?_⟩
  change (SheafOfModules.forget R').map (f.over U ≫ y) = x
  rw [Injective.comp_factorThru hx (f.over U)]
  exact (SheafOfModules.fullyFaithfulForget R').map_preimage (X := A'.over U) (Y := K.over U) x

/-- **[Stacks, Tag 01DR] for complexes.** A short exact sequence `0 ⟶ A' ⟶ A ⟶ A'' ⟶ 0` gives
a short exact sequence of complexes `0 ⟶ 𝓗om(A'', K^•) ⟶ 𝓗om(A, K^•) ⟶ 𝓗om(A', K^•) ⟶ 0`
when every term of `K^•` is injective. -/
theorem cx_shortExact
    {S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (hS : S.ShortExact)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℕ)
    [∀ n, Injective (K.X n)] :
    (ShortComplex.mk (cxMap O S.g K) (cxMap O S.f K)
      (by rw [cxMap_comp, S.zero, cxMap_zero])).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  obtain ⟨_, hex⟩ := sheafInternalHomMapLeft_exact_of_exact_epi
    (Opens.grothendieckTopology X) O S (K.X n) hS.exact
  exact ShortComplex.ShortExact.mk' hex
    (sheafInternalHomMapLeft_mono_of_epi (Opens.grothendieckTopology X) O S.g)
    (SheafOfModules.epi_of_sectionwise_surjective _ fun T =>
      surjective_internalHomMapLeft_app S.f (K.X n) T.unop)

/-- **`𝓗om` out of a finite free module into an injective resolution is exact in positive
degrees**: it is a finite direct sum of copies of the resolution. -/
theorem exactAt_cx_free (I : Type u) [Finite I]
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (R : InjectiveResolution G) (q : ℕ) :
    (cx O (SheafOfModules.free I) R.cocomplex).ExactAt (q + 1) := by
  let F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
    Functor.const (Discrete I) ⋙ colim
  let e : cx O (SheafOfModules.free I) R.cocomplex ≅ (F.mapHomologicalComplex _).obj R.cocomplex :=
    (NatIso.mapHomologicalComplex
      (freeInternalHomNatIso (Opens.grothendieckTopology X) O I).symm _).app R.cocomplex
  refine HomologicalComplex.ExactAt.of_iso ?_ e.symm
  exact (HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)).2
    ((R.exact_succ q).map F)

end Stacks.SheafHomInjective

end
