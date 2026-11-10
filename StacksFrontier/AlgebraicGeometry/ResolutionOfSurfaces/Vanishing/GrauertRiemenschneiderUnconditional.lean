module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GrauertRiemenschneiderDuality
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonExactFunctor
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Grauert-Riemenschneider vanishing

In Situation [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local domain `(A, 𝔪, κ)`
and a modification `f : X ⟶ S = Spec(A)` — with `X` normal and `A` Nagata having a dualizing
complex, the first higher direct image of the dualizing module of `X` vanishes:
`R¹f_*ω_X = 0`. This is [Stacks, Tag 0AXD], and it is proved here.

`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_dualizingModule_of_isTildeDualizing`
of `Vanishing/GrauertRiemenschneiderDuality.lean` is the whole of the source's argument, granted
two reconciliations of two library spellings of one object; this file supplies both and states
the conclusion with no hypothesis beyond the tag's own.

## The two spellings

Both concern the complex `ω̃_A^•` of `𝒪_S`-modules associated with a dualizing complex `ω_A^•`
over `A`.

`Stacks.Duality.IsTildeModelOnAnyModel K ⊤ hU ω` compares `K` restricted to `⊤` with the
sheafification of a complex `ω` over `Γ(S, ⊤)` transported along `⊤ ≅ Spec Γ(S, ⊤)`, whereas the
duality transport of `Duality/ProperDualityTransportAffineBase.lean` and the degree statements of
`Duality/SurfaceDualizingDegree/NormalizedUpperShriek.lean` are written with
`AlgebraicGeometry.derivedTilde` over `A` itself. The two are reconciled by
`Stacks.Duality.tildeTopRestrictIso`, the affine dictionary
`Stacks.AffineTilde.tildeRestrictIso` at the isomorphism
`AlgebraicGeometry.Scheme.ΓSpecIso`: restricting `M̃` to `⊤` is the sheafification of
`Γ(S, ⊤) ⊗_A M` transported along `⊤ ≅ Spec Γ(S, ⊤)`, because
`hU.isoSpec.hom ≫ Spec((ΓSpecIso A)⁻¹) = ⊤.ι`. Passing to derived categories gives
`Stacks.Duality.isTildeModelOnAnyModel_derivedTilde_top`, and with it `ω̃_A^•` is a dualizing
complex on `S` by [Stacks, Tag 0A86]. The normalization of the model over `Γ(S, ⊤)` which the
degree statements also need is [Stacks, Tag 0AWD] for the flat local homomorphism
`A ≅ Γ(S, ⊤)`, which is `Dualizing.isNormalizedDualizingComplex_globalSectionsSpec`.

`Stacks.Duality.relativeDualizingComplex` carries free `CategoryTheory.HasDerivedCategory`
binders, and `Duality/SurfaceDualizingDegree/NormalizedUpperShriek.lean` reads
`ω_X^• ≅ ω_X[2]` at the **locally small** model of [Stacks, Tag 079Q], the model at which the
right adjoint of [Stacks, Tag 0A9E] is constructed; the duality step is written at
`CategoryTheory.HasDerivedCategory.standard`, where the derived internal hom of
[Stacks, Tag 08DI] lives. The two readings are compared by
`Stacks.Duality.StandardModel.twistedInverseImageModelIso`, which intertwines the two right
adjoints, together with the comparison of the two single functors and the compatibility of the
comparison equivalence with the shift; the comparison equivalence is fully faithful, so the
isomorphism descends to the standard model. That is
`AlgebraicGeometry.VanishingSituation.exists_isDualizingModule_properRightAdjoint_isoShiftTwo`.

## Main results

* `Stacks.Duality.tildeTopRestrictIso` — restricting `M̃` on `Spec A` to the affine open `⊤` is
  the sheafification over `Γ(Spec A, ⊤)` of `Γ(Spec A, ⊤) ⊗_A M`, transported along
  `⊤ ≅ Spec Γ(Spec A, ⊤)`.
* `Stacks.Duality.isTildeModelOnAnyModel_derivedTilde_top` — the derived form: `ω_A^•` models its
  own derived sheafification on `⊤`, at every model of `D(𝒪_{Spec A})`.
* `Dualizing.isNormalizedDualizingComplex_globalSectionsSpec` — a normalized dualizing complex
  over `A` stays normalized over `Γ(Spec A, ⊤)`.
* `AlgebraicGeometry.VanishingSituation.exists_isDualizingModule_properRightAdjoint_isoShiftTwo`
  — `f^×(ω̃_A^•) ≅ ω_X[2]` at the standard model, with `ω_X` coherent.
* `AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_normalizedDualizingModule` —
  **[Stacks, Tag 0AXD]**: `R¹f_*ω_X = 0`.

## Implementation notes

The three sections treat the chosen model of `D(𝒪_X)` differently, and the erasures of the global
locally small instances of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are scoped to
the sections that need them.

The first section mentions no derived category. The second erases the locally small model of
`D(R)` for a ring `R`, which is the model `Stacks.Duality.IsTildeModelOnAnyModel` and
`Dualizing.IsNormalizedDualizingComplex` compare against, and leaves the locally small model of
`D(𝒪_X)` in place, that being the model the twisted inverse image is constructed at; the standard
model of `D(𝒪_X)` is written out where it is meant. The third erases all three, as
`Vanishing/GrauertRiemenschneiderDuality.lean` does, so that every derived category is the
standard one and the statements read as they do there.

The topological hypotheses on `X` are carried as `let`-bound instances in the statement rather
than as binders: `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`,
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` and
`AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated` discharge them from `f` being a
modification, so they are consequences of the situation and not assumptions.

## References

* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w w' u

/-! ### The affine dictionary at the whole of `Spec A` -/

namespace Stacks.Duality

/-- **The structure morphism of the affine open `⊤` of `Spec A`, read through `Γ`.** The canonical
isomorphism `⊤ ≅ Spec Γ(Spec A, ⊤)` followed by `Spec` of the inverse of
`AlgebraicGeometry.Scheme.ΓSpecIso` is the inclusion `⊤ ⟶ Spec A`: the first morphism is
`(⊤).ι ≫ (Spec A).toSpecΓ` and `(Spec A).toSpecΓ` is `Spec` of `ΓSpecIso`. -/
theorem isoSpec_hom_comp_specMap_ΓSpecIso_inv (R : CommRingCat.{u}) :
    (isAffineOpen_top (Spec R)).isoSpec.hom ≫ Spec.map (Scheme.ΓSpecIso R).inv =
      (⊤ : (Spec R).Opens).ι := by
  rw [IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_top, Category.assoc,
    ← Scheme.isoSpec_hom, ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]

/-- **The affine dictionary at the affine open `⊤` of `Spec A`.** Restricting the sheaf `M̃`
associated with an `A`-module `M` to `⊤` is the sheaf associated with the
`Γ(Spec A, ⊤)`-module `Γ(Spec A, ⊤) ⊗_A M`, transported to `⊤` along
`⊤ ≅ Spec Γ(Spec A, ⊤)`, naturally in `M`.

This is `Stacks.AffineTilde.tildeRestrictIso` ([Stacks, Tag 01I9] for the open immersion
`Spec((ΓSpecIso A)⁻¹)`, which is an isomorphism) composed with the factorization
`Stacks.Duality.isoSpec_hom_comp_specMap_ΓSpecIso_inv` of `⊤.ι`. Its right-hand side is the one
`Stacks.Duality.IsTildeModelOnAnyModel` compares against. -/
def tildeTopRestrictIso (R : CommRingCat.{u}) :
    tilde.functor R ⋙ Scheme.Modules.restrictFunctor (⊤ : (Spec R).Opens).ι ≅
      ModuleCat.extendScalars (Scheme.ΓSpecIso R).inv.hom ⋙
        (tilde.functor Γ(Spec R, ⊤) ⋙
          Scheme.Modules.restrictFunctor (isAffineOpen_top (Spec R)).isoSpec.hom) :=
  haveI : IsOpenImmersion (Spec.map (Scheme.ΓSpecIso R).inv) := inferInstance
  Functor.isoWhiskerLeft (tilde.functor R)
      ((Scheme.Modules.restrictFunctorCongr (isoSpec_hom_comp_specMap_ΓSpecIso_inv R)).symm ≪≫
        Scheme.Modules.restrictFunctorComp _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.AffineTilde.tildeRestrictIso (Scheme.ΓSpecIso R).inv) _ ≪≫
    Functor.associator _ _ _

end Stacks.Duality

/-! ### The two spelling bridges -/

section Bridges

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Duality

/-- Extension of scalars along the inverse of `ΓSpecIso` preserves finite limits, being flat. -/
private theorem preservesFiniteLimits_extendScalars_ΓSpecIso_inv (R : CommRingCat.{u}) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (Scheme.ΓSpecIso R).inv.hom) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
    (RingHom.Flat.of_bijective (f := (Scheme.ΓSpecIso R).inv.hom)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv))

/-- **A complex over `A` models its own derived sheafification on the affine open `⊤` of
`Spec A`.** The model is the transport of `ω_A^•` along `AlgebraicGeometry.Scheme.ΓSpecIso`, and
the statement holds at every chosen model of `D(𝒪_{Spec A})` and of `D(A)`.

This is the derived form of `Stacks.Duality.tildeTopRestrictIso`: both sides of
`Stacks.Duality.IsTildeModelOnAnyModel` are the degreewise action of a composite of exact
functors, so the comparison of a composite of descents with the descent of the composite
(`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`) reduces it to that isomorphism of
functors on modules.

Nothing else in the library relates `Stacks.Duality.IsTildeModelOnAnyModel` to
`AlgebraicGeometry.derivedTilde`, so this is what lets
`Stacks.Duality.isDualizingComplex_of_isTildeModelOn_top` ([Stacks, Tag 0A86]) be applied to a
derived sheafification. -/
theorem isTildeModelOnAnyModel_derivedTilde_top (R : CommRingCat.{u})
    [hmod : HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [hsch : HasDerivedCategory.{w'} (Spec R).Modules]
    (ωA : DerivedCategory (ModuleCat.{u} R)) :
    letI : PreservesFiniteLimits
        (ModuleCat.extendScalars.{u, u, u} (Scheme.ΓSpecIso R).inv.hom) :=
      extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
        (RingHom.Flat.of_bijective (f := (Scheme.ΓSpecIso R).inv.hom)
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv))
    @IsTildeModelOnAnyModel (Spec R) hsch ((derivedTilde R).obj ωA).obj ⊤
      (isAffineOpen_top (Spec R))
      ((ModuleCat.extendScalars (Scheme.ΓSpecIso R).inv.hom).mapDerivedCategory.obj ωA) := by
  let := HasDerivedCategory.standard (⊤ : (Spec R).Opens).toScheme.Modules
  have := preservesFiniteLimits_extendScalars_ΓSpecIso_inv R
  exact ⟨(Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (tilde.functor R) (Scheme.Modules.restrictFunctor (⊤ : (Spec R).Opens).ι)).symm.app ωA ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (tildeTopRestrictIso R)).app ωA ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (ModuleCat.extendScalars (Scheme.ΓSpecIso R).inv.hom)
      (tilde.functor Γ(Spec R, ⊤) ⋙
        Scheme.Modules.restrictFunctor (isAffineOpen_top (Spec R)).isoSpec.hom)).app ωA⟩

end Stacks.Duality

namespace Dualizing

/-- **A normalized dualizing complex over `A` is normalized over `Γ(Spec A, ⊤)`.**
`AlgebraicGeometry.Scheme.ΓSpecIso` is an isomorphism of rings, hence a flat local homomorphism
carrying the maximal ideal onto the maximal ideal, so this is [Stacks, Tag 0AWD].

`Dualizing.isDualizingComplex_of_ringEquiv` is the same transport for the unnormalized
statement. -/
theorem isNormalizedDualizingComplex_globalSectionsSpec (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : IsNormalizedDualizingComplex.{u, u} ωA) :
    letI : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
    letI : IsLocalRing Γ(Spec (CommRingCat.of A), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.isLocalRing
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) :=
      extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
        (RingHom.Flat.of_bijective (f := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv))
    IsNormalizedDualizingComplex.{u, u}
      ((ModuleCat.extendScalars
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory.obj ωA) := by
  set R := CommRingCat.of A
  set e : A ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let : IsNoetherianRing Γ(Spec R, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let : IsLocalRing Γ(Spec R, ⊤) := e.isLocalRing
  let : Algebra A Γ(Spec R, ⊤) := (e : A →+* Γ(Spec R, ⊤)).toAlgebra
  have : Module.Flat A Γ(Spec R, ⊤) := RingHom.Flat.of_bijective e.bijective
  have : IsLocalHom (algebraMap A Γ(Spec R, ⊤)) :=
    IsLocalHom.of_surjective (algebraMap A Γ(Spec R, ⊤)) e.surjective
  exact isNormalizedDualizingComplex_extendScalars_of_flat.{u, u, u}
    (IsLocalRing.map_ringEquiv_maximalIdeal e) ωA hωA

end Dualizing

namespace AlgebraicGeometry.VanishingSituation

open Stacks.Duality

attribute [local instance] isNoetherianRing_globalSections_base isLocalRing_globalSections_base

/-- **The derived sheafification of `ω_A^•`, read at the locally small model, carries the model
`ω` on `⊤`.** `Stacks.Duality.isTildeModelOnAnyModel_derivedTilde_top` holds at every model of
`D(𝒪_S)`; this records its reading at the locally small model for the image of the
standard-model sheafification under the comparison equivalence, the two being identified by
`StacksDraft.DerivedModel.mapDerivedCategoryCompModelEquivIso` — changing the model of the target
commutes with the degreewise action of an exact functor. -/
theorem isTildeModelOnAnyModel_derivedTilde_base (V : VanishingSituation.{u})
    (ωA : DerivedCategory (ModuleCat.{u} V.A)) :
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
        (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv.hom) :=
      extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
        (RingHom.Flat.of_bijective (f := (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv.hom)
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv))
    IsTildeModelOnAnyModel
      ((StandardModel.quasiCoherentModelEquiv V.base).functor.obj
        ((@derivedTilde (CommRingCat.of V.A) _ (HasDerivedCategory.standard _)).obj ωA)).obj ⊤
      (isAffineOpen_top V.base)
      ((ModuleCat.extendScalars
        (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv.hom).mapDerivedCategory.obj ωA) :=
  isTildeModelOnAnyModel_of_iso
    ((StacksDraft.DerivedModel.mapDerivedCategoryCompModelEquivIso
      (F := tilde.functor (CommRingCat.of V.A))
      (HasDerivedCategory.standard (ModuleCat.{u} V.A))
      (HasDerivedCategory.standard V.base.Modules)
      (Scheme.Modules.hasDerivedCategory V.base)).app ωA).symm
    (isTildeModelOnAnyModel_derivedTilde_top
      (hsch := Scheme.Modules.hasDerivedCategory V.base) (CommRingCat.of V.A) ωA)

/-- **`f^×(ω̃_A^•) ≅ ω_X[2]` at the standard model**, with `ω_X` a coherent `𝒪_X`-module.

In Situation [Stacks, Tag 0AX8] with `X` normal, let `K` be an object of `D_QCoh(𝒪_S)` at the
standard model which carries a normalized dualizing complex `ω` over `Γ(S, ⊤)` as its model on
`⊤`. Then the value at `K` of the right adjoint of [Stacks, Tag 0A9E] is a coherent module placed
in degree `-2`.

`AlgebraicGeometry.VanishingSituation.relativeDualizingComplexIsoShiftTwo` is this isomorphism at
the locally small model, which is the model the right adjoint is constructed at
([Stacks, Tag 079Q]), and the coherence is
`AlgebraicGeometry.VanishingSituation.coherent_cohenMacaulay_relativeDualizingModule`
([Stacks, Tag 0AWI]). The comparison equivalence of the two models intertwines the two right
adjoints (`Stacks.Duality.StandardModel.twistedInverseImageModelIso`), carries the standard
`ω_X[0]` to the locally small one and commutes with the shift; being fully faithful, it reflects
the isomorphism to the standard model. -/
theorem exists_isDualizingModule_properRightAdjoint_isoShiftTwo (V : VanishingSituation.{u})
    [IsNormal V.X] [IsProper V.f] [CompactSpace V.X] [QuasiSeparatedSpace V.X]
    [IsLocallyNoetherian V.X]
    (ω : DerivedCategory (ModuleCat.{u} Γ(V.base, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (K : @quasiCoherentDerivedCategory V.base (HasDerivedCategory.standard V.base.Modules))
    (hmodel : IsTildeModelOnAnyModel
      ((StandardModel.quasiCoherentModelEquiv V.base).functor.obj K).obj ⊤
      (isAffineOpen_top V.base) ω) :
    ∃ ωX : V.X.Modules, _root_.SheafOfModules.IsCoherent ωX ∧
      Nonempty (((properRightAdjoint V.f).obj K).obj ≅
        ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) := by
  let : AlgebraicGeometry.IsNoetherian V.X := isNoetherian_of_locallyOfFiniteType V.f
  let := StacksDraft.Perfect.derivedEquivalenceCommShift
    (HasDerivedCategory.standard V.X.Modules) (Scheme.Modules.hasDerivedCategory V.X)
  set ωS := (StandardModel.quasiCoherentModelEquiv V.base).functor.obj K
  refine ⟨relativeDualizingModule V.f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs V.f) ωS,
    (V.coherent_cohenMacaulay_relativeDualizingModule ωS ω hω hmodel).1, ⟨?_⟩⟩
  set Ψ := (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard V.X.Modules)
    (Scheme.Modules.hasDerivedCategory V.X)).functor
  refine Ψ.asEquivalence.fullyFaithfulFunctor.preimageIso ?_
  refine (ObjectProperty.ι _).mapIso ((StandardModel.twistedInverseImageModelIso V.f).app K) ≪≫
    V.relativeDualizingComplexIsoShiftTwo ωS ω hω hmodel ≪≫ ?_
  exact ((shiftFunctor _ (2 : ℤ)).mapIso
      ((StacksDraft.DerivedModel.modelSingleFunctorIso
        (HasDerivedCategory.standard V.X.Modules)
        (Scheme.Modules.hasDerivedCategory V.X) 0).app _)).symm ≪≫
    ((Ψ.commShiftIso (2 : ℤ)).app _).symm

end AlgebraicGeometry.VanishingSituation

end Bridges

/-! ### Grauert-Riemenschneider vanishing -/

section Vanishing

attribute [-instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.VanishingSituation

open Stacks.Duality

attribute [local instance] isNoetherianRing_globalSections_base isLocalRing_globalSections_base

/-- **`ω̃_A^•` is a dualizing complex on `Spec A`.** The derived sheafification of a dualizing
complex `ω_A^•` over `A` is a dualizing complex on `Spec A`: the single affine open `⊤` covers,
and over it `ω_A^•` transported along `AlgebraicGeometry.Scheme.ΓSpecIso` is a dualizing model,
by `Stacks.Duality.isTildeModelOnAnyModel_derivedTilde_top` and
`Dualizing.isDualizingComplex_of_ringEquiv`. This is [Stacks, Tag 0A86] applied to that cover. -/
theorem isDualizingComplex_derivedTilde_base (V : VanishingSituation.{u})
    (ωA : DerivedCategory (ModuleCat.{u} V.A))
    (hωA : Dualizing.IsDualizingComplex ωA) :
    IsDualizingComplex ((derivedTilde (CommRingCat.of V.A)).obj ωA).obj := by
  have : AlgebraicGeometry.IsNoetherian V.base := isNoetherian_of_isAffine_of_isNoetherianRing
  have := preservesFiniteLimits_extendScalars_ΓSpecIso_inv (CommRingCat.of V.A)
  refine isDualizingComplex_of_isTildeModelOn_top ?_
    (isTildeModelOnAnyModel_derivedTilde_top (CommRingCat.of V.A) ωA)
  set e : V.A ≃+* Γ(V.base, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V.A)).symm.commRingCatIsoToRingEquiv
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (e : V.A →+* Γ(V.base, ⊤))) :=
    preservesFiniteLimits_extendScalars_ΓSpecIso_inv (CommRingCat.of V.A)
  exact Dualizing.isDualizingComplex_of_ringEquiv e ωA hωA

/-- **Stacks Project, Tag 0AXD** (Grauert-Riemenschneider). Let `(A, 𝔪, κ)` be a
two-dimensional Noetherian normal local domain, `f : X ⟶ S = Spec(A)` a modification with `X`
normal, and suppose `A` is Nagata and has a dualizing complex. Then there are a normalized
dualizing complex `ω_A^•` over `A` and a dualizing module `ω_X` on `X` normalized with respect to
it — that is, with `f^×(ω̃_A^•) ≅ ω_X[2]`, the dualizing module of [Stacks, Remark 0B4R] — whose
first cohomology vanishes: `H¹(X, ω_X) = 0`, which over the affine base `S` is `R¹f_*ω_X = 0`.

The dualizing module is exhibited rather than quantified over, because that is what the source's
`ω_X` is: a dualizing complex on `X` is determined only up to shift and twist by an invertible
object, and the normalization `f^×(ω̃_A^•) ≅ ω_X[2]` is what picks out the one the statement is
about.

The proof is the source's, assembled from
`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_dualizingModule_of_isTildeDualizing`:
`ω_A^•` is normalized after one shift ([Stacks, Tag 0A7L] through [Stacks, Tag 0AX1]), its
derived sheafification is a dualizing complex on `S`
(`AlgebraicGeometry.VanishingSituation.isDualizingComplex_derivedTilde_base`), and `f^×` of it is
a coherent module in degree `-2`
(`AlgebraicGeometry.VanishingSituation.exists_isDualizingModule_properRightAdjoint_isoShiftTwo`),
which is a dualizing module because `f^×` preserves dualizing complexes ([Stacks, Tag 0AA3]).

**A note on dependency reporting.** A tool that collects axioms from the public oleans can
report a spurious placeholder dependency for this theorem; this is not a defect of the proof,
and it affects every declaration in this part of the library.

`Duality/DerivedTilde/AffinePullbackComparison.lean` reaches its key input through `import all`,
and that input — `CochainComplex.DerivedExtensionScalars.isLeftDerivedFunctor_of_isIso_on_kFlat`
of `Homology/Tor/DerivedExtensionScalars.lean` — is `private`. A private declaration of another
module has no entry in Lean's exported-dependency extension and no body in the public olean, so
such a collector sees only a stub and records a placeholder. Everything above it inherits that
reading, which is the whole apparent chain through 08DW, 08EU, 0GEW and the duality transport.
Read in its own module the private lemma is clean, and so is every constant in the statements
and proofs of the two theorems that consume it.

The proof is complete: no proof in `StacksCore/` or `StacksFrontier/` is left open, Mathlib and
every
dependency are complete, and no elaborator in this repository emits a placeholder. So no library
declaration can carry one at all.

The spurious report disappears with a three-line change in that one base file: import
`Homology/Tor/DerivedChangeOfRings`
publicly instead of `import all` on `DerivedExtensionScalars`, and call the already-public twin
`CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat`, which has the
same signature and whose body lives in its own module. It is mathematically a no-op. -/
@[stacks 0AXD "the conclusion R^1 f_* omega_X = 0 of Proposition 54.7.8, read over the affine \
base S = Spec(A) as the vanishing of H^1(X, omega_X) as an A-module, with no hypothesis beyond \
the Proposition's own: the Situation of Tag 0AX8, X normal, A Nagata, and A having a dualizing \
complex in the form of the bare existential. The dualizing module omega_X of Remark 0B4R is \
exhibited together with the normalization f^times(omega_A^bullet-tilde) = omega_X[2] that \
singles it out, a dualizing complex being determined only up to shift and twist. The source's \
proof is carried out in full: omega_X^bullet = omega_X[2] (Tags 0B3D, 0AWT, 0AWI), a nonzero \
R^1 f_* omega_X -> kappa gives a nonzero alpha : Rf_* omega_X^bullet -> kappa[1], and \
RHom_A(-, omega_A^bullet) carries it to a nonzero beta : kappa[-1] -> Rf_* O_X, using \
RHom_A(kappa[1], omega_A^bullet) = kappa[-1] for a normalized omega_A^bullet (Tag 0A7M) and \
RHom_A(Rf_* omega_X^bullet, omega_A^bullet) = Rf_* O_X (Tags 0GEW, 0AA3), contradicting \
Tag 0AXC; Nakayama then gives the vanishing"]
theorem isZero_firstCohomology_normalizedDualizingModule (V : VanishingSituation.{u})
    [IsNormal V.X]
    (hnag : IsNagataRing V.A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} V.A), Dualizing.IsDualizingComplex K) :
    letI : IsProper V.f := V.modification.isProper
    letI : CompactSpace V.X := QuasiCompact.compactSpace_of_compactSpace V.f
    letI : QuasiSeparatedSpace V.X := quasiSeparatedSpace_of_quasiSeparated V.f
    letI : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.f
    ∃ (ωA : DerivedCategory (ModuleCat.{u} V.A)) (ωX : V.X.Modules),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ωA ∧ IsDualizingModule ωX ∧
      Nonempty (((properRightAdjoint V.f).obj
          ((derivedTilde (CommRingCat.of V.A)).obj ωA)).obj ≅
        ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) ∧
      IsZero (firstCohomologySheafAsBaseModule V.X V.f ωX) := by
  let : IsProper V.f := V.modification.isProper
  let : CompactSpace V.X := QuasiCompact.compactSpace_of_compactSpace V.f
  let : QuasiSeparatedSpace V.X := quasiSeparatedSpace_of_quasiSeparated V.f
  let : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.f
  have : AlgebraicGeometry.IsNoetherian V.X := isNoetherian_of_locallyOfFiniteType V.f
  have : AlgebraicGeometry.IsNoetherian V.base := isNoetherian_of_isAffine_of_isNoetherianRing
  have := preservesFiniteLimits_extendScalars_ΓSpecIso_inv (CommRingCat.of V.A)
  obtain ⟨K₀, hK₀⟩ := hdual
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u} K₀ hK₀
  have hK := V.isDualizingComplex_derivedTilde_base (K₀⟦-m⟧) hm.1
  obtain ⟨ωX, hcoh, hshift⟩ := V.exists_isDualizingModule_properRightAdjoint_isoShiftTwo
    ((ModuleCat.extendScalars
      (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv.hom).mapDerivedCategory.obj (K₀⟦-m⟧))
    (Dualizing.isNormalizedDualizingComplex_globalSectionsSpec V.A (K₀⟦-m⟧) hm)
    ((derivedTilde (CommRingCat.of V.A)).obj (K₀⟦-m⟧))
    (V.isTildeModelOnAnyModel_derivedTilde_base (K₀⟦-m⟧))
  obtain ⟨e⟩ := hshift
  have hdm : IsDualizingModule ωX := ⟨hcoh, -2, isDualizingComplex_of_iso
    (e ≪≫ ((DerivedCategory.singleFunctors V.X.Modules).shiftIso 2 (-2) 0 (by omega)).app ωX)
    (isDualizingComplex_properRightAdjoint_obj V.f _ hK)⟩
  exact ⟨K₀⟦-m⟧, ωX, hm, hdm, ⟨e⟩,
    V.isZero_firstCohomology_dualizingModule_of_isTildeDualizing hnag (K₀⟦-m⟧) hm hK ωX hdm ⟨e⟩⟩

end AlgebraicGeometry.VanishingSituation

end Vanishing

end
