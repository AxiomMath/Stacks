module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.FullSubcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackComplex

/-!
# The derived décalage and a flat pullback

Let `f : X ⟶ Y` be a flat morphism of ringed spaces and let `I ⊆ 𝒪_Y` be an invertible ideal
sheaf.  Pullback along `f` is exact, so it induces a functor `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` with no
resolution needed, and the derived décalages `Lη_I` of `D(𝒪_Y)` and `Lη_{f^*I}` of `D(𝒪_X)` of
[Stacks, Tag 0F8Q] are available as `Stacks.IdealTorsion.Eta.derivedEta`.  This file builds the
canonical comparison

`Lf^*(Lη_I M) ⟶ Lη_{f^*I}(Lf^* M)`

at an object `M = [G^•]` of `D(𝒪_Y)` represented by a complex `G^•` of `I`-torsion-free
`𝒪_Y`-modules, and shows it is an isomorphism.

## Main definitions

* `Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap`: the comparison, as the composite of five
  canonical maps — the comparison of `Lη_I` with the chain-level `η_I`
  (`Stacks.IdealTorsion.Eta.derivedEta_iso`, the *morphism* clause of [Stacks, Tag 0F8Q], so a
  natural isomorphism), the identification of `Lf^*` with degreewise pullback
  (`CategoryTheory.Functor.mapDerivedCategoryFactors`), the chain-level comparison
  `Stacks.IdealTorsion.Eta.pullbackEtaMap`, and then those two identifications again, backwards.

## Main results

* `Stacks.IdealTorsion.Eta.isIso_pullbackDerivedEtaMap`: **the comparison is an isomorphism when
  `f` is flat.**  Four of the five constituents are isomorphisms unconditionally; the remaining
  one is `Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap`, which is where flatness enters.

## Implementation notes

`Lf^*` is taken to be `CategoryTheory.Functor.mapDerivedCategory` of the pullback functor, i.e.
the functor induced on derived categories by an exact functor.  For a flat `f` that is the
derived pullback: an exact functor computes its own derived functor, which is the content of
`RingedSpaceModuleAdjunction.isIso_rightDerivedFunctorPlusUnit_modulePullback_of_flat`.  It also
agrees with the *left* derived pullback
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` because the comparison
`Lf^* ∘ Q ⟶ Q ∘ f^*` is an isomorphism at a K-flat complex
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat`), K-flat resolutions exist,
and a flat `f^*` carries quasi-isomorphisms to quasi-isomorphisms.

Exactness of the pullback is taken as the two instance hypotheses
`CategoryTheory.Limits.PreservesFiniteLimits` and
`CategoryTheory.Limits.PreservesFiniteColimits`, rather than derived from flatness inside the
declarations: they occur in the *statements*, through `mapDerivedCategory`, so they have to be
binders.  Flatness supplies both — the first by
`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat` and the second
unconditionally by `RingedSpaceModuleAdjunction.preservesColimits_modulePullback` — and
`Stacks.IdealTorsion.Eta.isIso_pullbackDerivedEtaMap` additionally asks for flatness itself,
which `Stacks.IdealTorsion.Eta.pullbackEtaTermIso` needs.

The object `M` is presented as `[G^•]` for a complex `G^•` of `I`-torsion-free modules rather
than as an arbitrary object of `D(𝒪_Y)`.  That is no loss of generality — granted
`Stacks.IdealTorsion.Eta.HasTorsionFreeResolutions`, which is already what makes `Lη_I` exist,
every object of `D(𝒪_Y)` is of that form — but the comparison is a family of morphisms
indexed by such complexes, not a natural transformation of the two composite functors.

The torsion-freeness of the termwise pullback of `G^•` is a hypothesis, because `η` of a complex
takes torsion-freeness of its terms as data.  For flat `f` with local stalks it holds by
`Stacks.IdealTorsion.Eta.isIdealTorsionFree_pullbackComplex_of_isFlat`.
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)

universe u

namespace Stacks.IdealTorsion.Eta

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The pullback of sheaves of modules, over the `Stacks.SheafOfModules.Tensor.ringSheaf _.sheaf`
spelling of the structure sheaf.

`Stacks.RingedSpace.pullbackFunctor` is typed over `Stacks.RingedSpace.structureRingSheaf`.  The
two spellings give the same category, but the `Abelian` instance the derived category needs is
only found at this one. -/
noncomputable abbrev etaPullbackModules :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) :=
  pullbackFunctor f

/-- Pullback of sheaves of modules is additive, at the ascribed spelling.  This is
`Stacks.RingedSpace.pullbackFunctor_additive`; the ascription is a new head symbol, so
instance search does not find that one through it. -/
noncomputable instance etaPullbackModules_additive : (etaPullbackModules f).Additive :=
  Stacks.RingedSpace.pullbackFunctor_additive f

variable [PreservesFiniteLimits (etaPullbackModules f)]
  [PreservesFiniteColimits (etaPullbackModules f)]
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)]

/-- The complex of `f^*I`-torsion-free `𝒪_X`-modules given by the termwise pullback of a complex
of `I`-torsion-free `𝒪_Y`-modules, once that pullback is known to be termwise torsion-free.

This is `HomologicalComplex.liftObjectProperty` for the property of being
`f^*I`-torsion-free; the underlying complex of `𝒪_X`-modules is the termwise pullback
again, so the two décalages below can be compared. -/
noncomputable def pullbackTorsionFreeComplex
    (K : CochainComplex (TorsionFreeModule Y ι) ℤ)
    (hK : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f ((torsionFreeComplex Y ι).obj K)).X n)) :
    CochainComplex (TorsionFreeModule X (pullbackIdealIncl f I ι)) ℤ :=
  HomologicalComplex.liftObjectProperty (torsionFreeProperty X (pullbackIdealIncl f I ι))
    (pullbackComplex f ((torsionFreeComplex Y ι).obj K)) hK

omit [PreservesFiniteLimits (etaPullbackModules f)] [PreservesFiniteColimits (etaPullbackModules f)]
  [Mono ι] [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)] in
/-- The complex of `𝒪_X`-modules underlying `pullbackTorsionFreeComplex` is the termwise
pullback it was built from. -/
theorem torsionFreeComplex_pullbackTorsionFreeComplex
    (K : CochainComplex (TorsionFreeModule Y ι) ℤ)
    (hK : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f ((torsionFreeComplex Y ι).obj K)).X n)) :
    (torsionFreeComplex X (pullbackIdealIncl f I ι)).obj
        (pullbackTorsionFreeComplex f I ι K hK) =
      pullbackComplex f ((torsionFreeComplex Y ι).obj K) :=
  rfl

/-- **The canonical comparison `Lf^*(Lη_I M) ⟶ Lη_{f^*I}(Lf^* M)`** at an object
`M = [G^•]` of `D(𝒪_Y)` represented by a complex `G^•` of `I`-torsion-free `𝒪_Y`-modules.

The composite of five canonical maps: the comparison of `Lη_I` with the chain-level décalage,
pushed forward by `Lf^*`; the identification of `Lf^*` with degreewise pullback on the chain-level
décalage; the chain-level comparison `Stacks.IdealTorsion.Eta.pullbackEtaMap`; and then the
comparison of `Lη_{f^*I}` with its chain-level décalage and the identification of `Lf^*` with
degreewise pullback, both read backwards. -/
noncomputable def pullbackDerivedEtaMap (hres : HasTorsionFreeResolutions Y ι)
    (hres' : HasTorsionFreeResolutions X (pullbackIdealIncl f I ι))
    (K : CochainComplex (TorsionFreeModule Y ι) ℤ)
    (hK : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f ((torsionFreeComplex Y ι).obj K)).X n)) :
    (etaPullbackModules f).mapDerivedCategory.obj
        ((derivedEta Y I ι hres).obj
          (DerivedCategory.Q.obj ((torsionFreeComplex Y ι).obj K))) ⟶
      (derivedEta X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) hres').obj
        ((etaPullbackModules f).mapDerivedCategory.obj
          (DerivedCategory.Q.obj ((torsionFreeComplex Y ι).obj K))) :=
  (etaPullbackModules f).mapDerivedCategory.map ((derivedEta_iso Y I ι hres).hom.app K) ≫
    ((etaPullbackModules f).mapDerivedCategoryFactors.hom.app
      ((etaFunctor Y I ι).obj K)) ≫
    DerivedCategory.Q.map
      (pullbackEtaMap f I ι ((torsionFreeComplex Y ι).obj K)
        (torsionFreeComplex_torsionFree Y ι K) hK) ≫
    ((derivedEta_iso X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) hres').inv.app
      (pullbackTorsionFreeComplex f I ι K hK)) ≫
    (derivedEta X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) hres').map
      ((etaPullbackModules f).mapDerivedCategoryFactors.inv.app ((torsionFreeComplex Y ι).obj K))

/-- **For a flat morphism the canonical comparison `Lf^*(Lη_I M) ⟶ Lη_{f^*I}(Lf^* M)` is an
isomorphism.**

Of the five constituents of `Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap` all but one are
components of natural isomorphisms, hence isomorphisms; the remaining one is
`DerivedCategory.Q` applied to the chain-level comparison, which is an isomorphism by
`Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap`. -/
theorem isIso_pullbackDerivedEtaMap (hf : AlgebraicGeometry.IsFlat f)
    (hres : HasTorsionFreeResolutions Y ι)
    (hres' : HasTorsionFreeResolutions X (pullbackIdealIncl f I ι))
    (K : CochainComplex (TorsionFreeModule Y ι) ℤ)
    (hK : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f ((torsionFreeComplex Y ι).obj K)).X n)) :
    IsIso (pullbackDerivedEtaMap f I ι hres hres' K hK) := by
  have h : IsIso (pullbackEtaMap f I ι ((torsionFreeComplex Y ι).obj K)
      (torsionFreeComplex_torsionFree Y ι K) hK) :=
    isIso_pullbackEtaMap f I ι ((torsionFreeComplex Y ι).obj K)
      (torsionFreeComplex_torsionFree Y ι K) hK hf
  have := h
  have i1 : IsIso ((etaPullbackModules f).mapDerivedCategory.map
      ((derivedEta_iso Y I ι hres).hom.app K)) := inferInstance
  have i2 : IsIso ((etaPullbackModules f).mapDerivedCategoryFactors.hom.app
      ((etaFunctor Y I ι).obj K)) := inferInstance
  have i3 : IsIso (DerivedCategory.Q.map
      (pullbackEtaMap f I ι ((torsionFreeComplex Y ι).obj K)
        (torsionFreeComplex_torsionFree Y ι K) hK)) :=
    (DerivedCategory.Q.mapIso (asIso (pullbackEtaMap f I ι ((torsionFreeComplex Y ι).obj K)
      (torsionFreeComplex_torsionFree Y ι K) hK))).isIso_hom
  have i4 : IsIso ((derivedEta_iso X ((pullbackFunctor f).obj I)
      (pullbackIdealIncl f I ι) hres').inv.app
      (pullbackTorsionFreeComplex f I ι K hK)) := inferInstance
  have i5 : IsIso ((derivedEta X ((pullbackFunctor f).obj I)
      (pullbackIdealIncl f I ι) hres').map
      ((etaPullbackModules f).mapDerivedCategoryFactors.inv.app
        ((torsionFreeComplex Y ι).obj K))) := inferInstance
  rw [pullbackDerivedEtaMap]
  exact IsIso.comp_isIso' i1 (IsIso.comp_isIso' i2 (IsIso.comp_isIso' i3
    (IsIso.comp_isIso' i4 i5)))

end Stacks.IdealTorsion.Eta

end
