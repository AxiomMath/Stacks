module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelDualityInputs
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GrauertRiemenschneiderUnconditional
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.OfModification
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.DerivedHomCorepresentability
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.HomShift.SourceShift

/-!
# Grauert-Riemenschneider vanishing read through duality: `Hom(RΓ(X, 𝒪_X)[1], ω_A^•) = 0`

Let `(A, 𝔪, κ)` be a two-dimensional Noetherian normal local Nagata domain, let
`f : X ⟶ Spec(A)` be a modification with `X` normal and let `ω_A^•` be a normalized dualizing
complex over `A`. This file proves that every morphism `RΓ(X, 𝒪_X)[1] ⟶ ω_A^•` of `D(A)`
vanishes, which is the hypothesis `hvan` of
`Stacks.ResolutionOfSurfaces`
`.isReductionToRationalSingularitiesPossible_of_hom_vanishing_of_factorisation`.

## The argument

Write `C = RΓ(X, 𝒪_X)[2]` and `N = RΓ(X, ω_X)` for the dualizing module `ω_X` of `X` normalized
with respect to `ω_A^•`, so that `RΓ(X, ω_X^•) ≅ N[2]`. Derived Hom into `ω_A^•` is an
anti-equivalence of `D^b_{Coh}(A)` ([Stacks, Tag 0A7C]), hence **full**, and it carries

* `A[0]` to `ω_A^•`, because derived Hom out of the ring in degree zero is the identity
  (`Dualizing.derivedHomULiftRingIso`), and
* `N[2][-1]` to `C[-1]`, by the duality transport
  `RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)` of
  `Stacks.Duality.nonempty_iso_dualizingDerivedHom_derivedGlobalSections_relativeDualizing`
  together with the commutation of derived Hom with the shift in its source
  (`Dualizing.dualizingDerivedHomSourceShift`).

A full functor carries a subsingleton group of morphisms to a subsingleton group of morphisms,
so it is enough that `Hom_{D(A)}(A[0], N[2][-1])` be a subsingleton. That group is
`H⁰(N[2][-1]) = H¹(X, ω_X)` — the free rank-one module in degree zero corepresents degree-zero
cohomology, `Dualizing.homologyLinearEquiv` — and `H¹(X, ω_X) = 0` is Grauert-Riemenschneider
vanishing, [Stacks, Tag 0AXD].

Since `Hom(C[-1], ω_A^•)` is a subsingleton containing the zero morphism, every morphism in it
is zero. No biduality is applied to `RΓ(X, 𝒪_X)`: the duality transport is used only in the
direction in which it is proved, and fullness replaces the inverse.

## Main results

All in the namespace `Stacks.ResolutionOfSurfaces`.

* `subsingleton_hom_of_full_op` — the formal half: a full contravariant functor between
  categories equipped with a full and faithful functor to a common target reflects a subsingleton
  group of morphisms forward, across two isomorphisms identifying its values.
* `exists_isDualizingModule_isZero_firstCohomology` — [Stacks, Tag 0AXD] at a *supplied*
  normalized dualizing complex rather than one the statement produces: for every normalized
  `ω_A^•` there is a dualizing module `ω_X` of `X` normalized with respect to it, and
  `H¹(X, ω_X) = 0`.
* `hom_shift_standardDerivedGlobalSectionsUnitShift_eq_zero` — **`hvan`**: every morphism
  `C[-1] ⟶ ω_A^•` vanishes.
* `isReductionToRationalSingularitiesPossible_of_factorisation` — [Stacks, Tag 0B4S] with `hvan`
  discharged, leaving only `himage`.

## Implementation notes

The three global locally small instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` arrive through the imports and outrank a
default-priority file-local instance, so they are erased in the section that mentions derived
categories and `CategoryTheory.HasDerivedCategory.standard` is installed in their place; that is
the model all the duality inputs are written at.

`exists_isDualizingModule_isZero_firstCohomology` repeats the body of
`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_normalizedDualizingModule` — which
is where [Stacks, Tag 0AXD] is registered — with the normalizing shift of [Stacks, Tag 0AX1]
removed, that being the one step of its proof which chooses the dualizing complex; everything
after it is performed at whatever normalized complex is given. The normalizing shift is applied
once, at the top of the chain, where a dualizing complex is turned into a normalized one. It is
stated for a bare modification rather than for `AlgebraicGeometry.VanishingSituation`, so that
the module `ω_X` it produces lives in `X.Modules` and the coherence instances it carries are
found for `X` itself; `AlgebraicGeometry.VanishingSituation.ofModification` supplies the
situation inside the proof.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The formal half: a full contravariant functor carries subsingletons forward -/

/-- **A full contravariant functor carries a subsingleton group of morphisms to a subsingleton
group of morphisms.** Let `ι : C ⥤ D` be full and faithful, let `F : Cᵒᵖ ⥤ C` be full, let `K`,
`L` be objects of `C`, and suppose `ι(F(L)) ≅ P` and `ι(F(K)) ≅ Q` with at most one morphism
`ι(K) ⟶ ι(L)`. Then there is at most one morphism `P ⟶ Q`.

This is the companion of `Stacks.Duality.subsingleton_hom_of_faithful_op`, which transports a
subsingleton the other way along a *faithful* contravariant functor. Here the hypothesis is on
the source of `F` and the conclusion on its target, so what is needed is that every morphism
between the images be the image of one. -/
theorem subsingleton_hom_of_full_op {C D : Type*} [Category C] [Category D] (ι : C ⥤ D)
    [ι.Full] [ι.Faithful] (F : Cᵒᵖ ⥤ C) [F.Full] {K L : C} {P Q : D}
    (e₁ : ι.obj (F.obj (op L)) ≅ P) (e₂ : ι.obj (F.obj (op K)) ≅ Q)
    (h : Subsingleton (ι.obj K ⟶ ι.obj L)) : Subsingleton (P ⟶ Q) := by
  have hC : Subsingleton (K ⟶ L) := ⟨fun a b => ι.map_injective (h.allEq _ _)⟩
  have hF : Subsingleton (F.obj (op L) ⟶ F.obj (op K)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := F.map_surjective a
    obtain ⟨b', rfl⟩ := F.map_surjective b
    rw [Quiver.Hom.unop_inj (hC.allEq a'.unop b'.unop)]
  have hι : Subsingleton (ι.obj (F.obj (op L)) ⟶ ι.obj (F.obj (op K))) :=
    Stacks.Duality.subsingleton_hom_map_of_subsingleton ι hF
  refine ⟨fun a b => ?_⟩
  have h₁ : e₁.hom ≫ a ≫ e₂.inv = e₁.hom ≫ b ≫ e₂.inv := hι.allEq _ _
  simpa using congrArg (fun t => e₁.inv ≫ t ≫ e₂.hom) h₁

/-! ### Grauert-Riemenschneider vanishing at a supplied normalized dualizing complex -/

section Vanishing

attribute [local instance] HasDerivedCategory.standard

open Stacks.Duality AlgebraicGeometry.VanishingSituation

attribute [local instance] isNoetherianRing_globalSections_base isLocalRing_globalSections_base

/-- **[Stacks, Tag 0AXD] at a supplied normalized dualizing complex.** In Situation
[Stacks, Tag 0AX8] with `X` normal and `A` Nagata, let `ω_A^•` be *any* normalized dualizing
complex over `A`. Then there is a coherent module `ω_X` on `X` with `f^×(ω̃_A^•) ≅ ω_X[2]` — the
dualizing module of [Stacks, Remark 0B4R] normalized with respect to `ω_A^•` — whose first
cohomology vanishes: `H¹(X, ω_X) = 0`.

`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_normalizedDualizingModule` is the
same statement with `ω_A^•` produced from the mere existence of a dualizing complex, by the
normalizing shift of [Stacks, Tag 0AX1]. -/
theorem exists_isDualizingModule_isZero_firstCohomology {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] {X : Scheme.{u}} [IsNormal X]
    (f : X ⟶ Spec (.of A)) (hnag : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hf : IsModification f) (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA) :
    letI : IsProper f := hf.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ ωX : X.Modules, _root_.SheafOfModules.IsCoherent ωX ∧
      Nonempty (((properRightAdjoint f).obj
          ((derivedTilde (CommRingCat.of A)).obj ωA)).obj ≅
        ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) ∧
      IsZero (firstCohomologySheafAsBaseModule X f ωX) := by
  let V := VanishingSituation.ofModification A hdim f hf
  have : IsNormal V.X := ‹IsNormal X›
  let : IsProper V.f := V.modification.isProper
  let : CompactSpace V.X := QuasiCompact.compactSpace_of_compactSpace V.f
  let : QuasiSeparatedSpace V.X := quasiSeparatedSpace_of_quasiSeparated V.f
  let : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.f
  have : AlgebraicGeometry.IsNoetherian V.X := isNoetherian_of_locallyOfFiniteType V.f
  have : AlgebraicGeometry.IsNoetherian V.base := isNoetherian_of_isAffine_of_isNoetherianRing
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv.hom) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.Flat.of_bijective (f := (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv.hom)
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv))
  have hK := V.isDualizingComplex_derivedTilde_base ωA hωA.1
  obtain ⟨ωX, hcoh, hshift⟩ := V.exists_isDualizingModule_properRightAdjoint_isoShiftTwo
    ((ModuleCat.extendScalars
      (Scheme.ΓSpecIso (CommRingCat.of V.A)).inv.hom).mapDerivedCategory.obj ωA)
    (Dualizing.isNormalizedDualizingComplex_globalSectionsSpec V.A ωA hωA)
    ((derivedTilde (CommRingCat.of V.A)).obj ωA)
    (V.isTildeModelOnAnyModel_derivedTilde_base ωA)
  obtain ⟨e⟩ := hshift
  have hdm : IsDualizingModule ωX := ⟨hcoh, -2, isDualizingComplex_of_iso
    (e ≪≫ ((DerivedCategory.singleFunctors V.X.Modules).shiftIso 2 (-2) 0 (by omega)).app ωX)
    (isDualizingComplex_properRightAdjoint_obj V.f _ hK)⟩
  exact ⟨ωX, hcoh, ⟨e⟩,
    V.isZero_firstCohomology_dualizingModule_of_isTildeDualizing hnag ωA hωA hK ωX hdm ⟨e⟩⟩

/-- Morphisms from the universe-lifted ring to `N[2][-1]` are trivial when `H¹(N) = 0`: the
lifted ring corepresents degree-zero cohomology, and `H⁰(N[2][-1]) ≅ H¹(N)`. -/
private theorem subsingleton_hom_uliftRingObject_shift_of_isZero_homology_one {A : Type u}
    [CommRing A] (N : DerivedCategory (ModuleCat.{u} A))
    (hN : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj N)) :
    Subsingleton ((Dualizing.uliftRingObject.{u, u} A).obj ⟶ (N⟦(2 : ℤ)⟧)⟦(-1 : ℤ)⟧) := by
  have eh₀ : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((N⟦(2 : ℤ)⟧)⟦(-1 : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj (N⟦(2 : ℤ)⟧) := by
    exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso (-1) 0 (-1)
      (by norm_num)).app (N⟦(2 : ℤ)⟧)
  have eh₁ : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj (N⟦(2 : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj N := by
    exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso 2 (-1) 1
      (by norm_num)).app N
  have hsubRing : Subsingleton
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
        (N⟦(2 : ℤ)⟧)⟦(-1 : ℤ)⟧) :=
    @Equiv.subsingleton _ _
      (Dualizing.homologyLinearEquiv ((N⟦(2 : ℤ)⟧)⟦(-1 : ℤ)⟧) 0).symm.toEquiv
      (ModuleCat.isZero_iff_subsingleton.mp (hN.of_iso (eh₀ ≪≫ eh₁)))
  have euli : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (ULift.{u} A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (ULift.moduleEquiv (R := A) (M := A)).toModuleIso
  exact ⟨fun a b => (cancel_epi euli.inv).mp (hsubRing.allEq _ _)⟩

/-! ### The vanishing of `Hom(C[-1], ω_A^•)` -/

section Hvan

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`hvan`: every morphism `RΓ(X, 𝒪_X)[2][-1] ⟶ ω_A^•` of `D(A)` vanishes.** For a modification
`f : X ⟶ Spec(A)` with `X` normal, of a two-dimensional Noetherian normal local Nagata domain,
and a normalized dualizing complex `ω_A^•` over `A`.

Over the affine base this group is `H¹(X, ω_X)` for the dualizing module `ω_X` normalized with
respect to `ω_A^•`, and the vanishing is Grauert-Riemenschneider, [Stacks, Tag 0AXD]; see the
module documentation for the chain. -/
theorem hom_shift_standardDerivedGlobalSectionsUnitShift_eq_zero [IsNormal X]
    (hnag : IsNagataRing A) (hdim : ringKrullDim A = 2) (hf : IsModification f)
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA)
    (g : (standardDerivedGlobalSectionsUnitShift f)⟦(-1 : ℤ)⟧ ⟶ ωA) : g = 0 := by
  have : IsProper f := hf.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨ωX, hcoh, ⟨eshift⟩, hzero⟩ :=
    exists_isDualizingModule_isZero_firstCohomology f hnag hdim hf ωA hωA
  have : _root_.SheafOfModules.IsCoherent ωX := hcoh
  have : ωX.IsQuasicoherent := isQuasicoherent_of_isCoherent ωX
  set 𝒟 := Dualizing.dualizingDerivedHomFunctor.{u, u} A ωA
  set N := (derivedGlobalSectionsOver f).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)
  -- `RΓ(X, ω_X^•) ≅ N[2]`.
  have eN : (derivedGlobalSectionsOver f).obj
        ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj ≅
      N⟦(2 : ℤ)⟧ :=
    (derivedGlobalSectionsOver f).mapIso eshift ≪≫
      ((derivedGlobalSectionsOver f).commShiftIso (2 : ℤ)).app _
  -- `RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)`.
  obtain ⟨etr⟩ := nonempty_iso_dualizingDerivedHom_derivedGlobalSections_relativeDualizing
    f ωA hωA.1
    ((VanishingSituation.ofModification A hdim f hf).isDualizingComplex_derivedTilde_base ωA
      hωA.1)
  have eQ : 𝒟.obj (op (N⟦(2 : ℤ)⟧)) ≅ standardDerivedGlobalSectionsStructureSheaf f :=
    𝒟.mapIso eN.op ≪≫ etr
  -- `RHom_A(N[2][-1], ω_A^•) ≅ RΓ(X, 𝒪_X)[1] ≅ C[-1]`.
  have eP : 𝒟.obj (op ((N⟦(2 : ℤ)⟧)⟦(-1 : ℤ)⟧)) ≅
      (standardDerivedGlobalSectionsUnitShift f)⟦(-1 : ℤ)⟧ :=
    Dualizing.dualizingDerivedHomSourceShift.{u, u} A ωA (-1) (N⟦(2 : ℤ)⟧) ≪≫
      eqToIso (congrArg (fun n : ℤ => (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).obj
        (𝒟.obj (op (N⟦(2 : ℤ)⟧)))) (show -(-1 : ℤ) = 1 by norm_num)) ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).mapIso eQ ≪≫
      (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) 2 (-1) 1 (by norm_num)).app _
  have hsubU := subsingleton_hom_uliftRingObject_shift_of_isZero_homology_one N
    (hzero.of_iso (firstCohomologySheafAsBaseModuleIsoDerivedCohomology f ωX).symm)
  -- `D^b_{Coh}(A)`-level data: `N` is bounded with finite cohomology, and so are its shifts.
  set PN : Dualizing.BoundedCoherentDerivedCategory.{u, u} A :=
    ⟨N, moduleFinite_homology_derivedGlobalSections f ωX, bounded_derivedGlobalSections f ωX⟩
  let : (Dualizing.boundedCoherentDualizingDerivedHomFunctor.{u, u} A ωA hωA.1).IsEquivalence :=
    Dualizing.boundedCoherentDualizingDerivedHom_isEquivalence.{u, u} A ωA hωA.1
  exact (subsingleton_hom_of_full_op (ObjectProperty.ι _)
      (Dualizing.boundedCoherentDualizingDerivedHomFunctor.{u, u} A ωA hωA.1)
      (K := Dualizing.uliftRingObject.{u, u} A)
      (L := Dualizing.boundedCoherentShiftBy (Dualizing.boundedCoherentShiftBy PN 2) (-1))
      eP (Dualizing.derivedHomULiftRingIso.{u, u} A ωA) hsubU).allEq g 0

end Hvan

/-! ### [Stacks, Tag 0B4S] with `hvan` discharged -/

/-- **[Stacks, Tag 0B4S] with Grauert-Riemenschneider discharged, leaving the trace hypothesis.**
Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two with a normalized dualizing
complex `ω_A^•` and let `d ∈ A` be nonzero. Write `C_f = RΓ(X, 𝒪_X)[2]` for a modification
`f : X ⟶ Spec(A)` with `X` normal. If for every such `f` the submodule `d · Hom(A[-2], ω_A^•)`
factors through every `u : A[-2] ⟶ C_f` which is an isomorphism on `H^{-2}`, then reduction to
rational singularities is possible for `A`.

This is
`Stacks.ResolutionOfSurfaces`
`.isReductionToRationalSingularitiesPossible_of_hom_vanishing_of_factorisation`
with its first hypothesis supplied by
`hom_shift_standardDerivedGlobalSectionsUnitShift_eq_zero`, that is, by
[Stacks, Tag 0AXD] read through duality over the affine base.

The remaining hypothesis is the hypothesis of [Stacks, Tag 0B4S] read through duality; it becomes
that hypothesis once composition with `u` is identified with the trace `Γ(X, ω_X) ⟶ ω_A` of
[Stacks, Tag 0AWG]. -/
theorem isReductionToRationalSingularitiesPossible_of_factorisation (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2)
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA) (d : A) (hd : d ≠ 0)
    (himage : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      ∀ u : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶
          standardDerivedGlobalSectionsUnitShift f,
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map u) →
        ∀ q : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶ ωA,
          ∃ r : standardDerivedGlobalSectionsUnitShift f ⟶ ωA, u ≫ r = q ≫ (d • 𝟙 ωA)) :
    IsReductionToRationalSingularitiesPossible A := by
  have : IsNoetherianRing A := ‹IsNagataRing A›.1
  exact isReductionToRationalSingularitiesPossible_of_hom_vanishing_of_factorisation A hdim ωA
    hωA d hd
    (fun X _ f hf g => hom_shift_standardDerivedGlobalSectionsUnitShift_eq_zero f
      ‹IsNagataRing A› hdim hf ωA hωA g)
    himage

end Vanishing

end Stacks.ResolutionOfSurfaces

end
