module

public import StacksFrontier.AlgebraicGeometry.Duality.ModelComparisonRightAdjointTraceUnit
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExtTildeIso
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom

/-!
# `RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)` for `f : X ⟶ Spec A` proper

Let `A` be a Noetherian ring, let `f : X ⟶ Spec A` be a proper morphism, and let `ω_A^•` be an
object of `D(A)` whose derived sheafification `ω̃_A^•` is a dualizing complex on `Spec A`. Write
`ω_X^• = f^×(ω̃_A^•)` for the relative dualizing complex of [Stacks, Tag 0AWI]. Then

`RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)`

in `D(A)`, where the left-hand side is derived Hom into `ω_A^•` as the tagged statement of
[Stacks, Tag 0A7C] spells it, `Dualizing.dualizingDerivedHomFunctor A ω_A^•`.

This is the duality step the source performs inside the proof of [Stacks, Tag 0AXD]: the sheafy
computation `Rf_*𝒪_X ≅ R𝓗om_{𝒪_{Spec A}}(Rf_*ω_X^•, ω̃_A^•)`, transported from `D(𝒪_{Spec A})`
down to `D(A)` along the derived Spec–Γ equivalence of [Stacks, Tag 06Z0].

## Main definitions

All in the namespace `Stacks.Duality`.

* `dualizingDerivedHomDerivedGlobalSectionsRelativeDualizingIso` — the displayed isomorphism.

The four spelling reconciliations the transport needs, each the identification of two library
names for one object:

* `standardTildeEquivalence`, `standardTildeEquivalenceInverseIso`,
  `standardTildeGlobalSectionsUnitIso` and `standardTildeGlobalSectionsCounitIso` — the derived
  Spec–Γ equivalence of [Stacks, Tag 06Z0] at the **standard** model, with its unit and counit.
  These are `AlgebraicGeometry.DualizingDivisor.tildeEquivalence`,
  `tildeEquivalenceInverseIso` and the two structure maps of
  `AlgebraicGeometry.DualizingDivisor.globalSectionsTildeHomEquiv`, read at the standard model
  instead of the locally small one.
* `standardLerayIso` — Leray over the base ring ([Stacks, Tag 0D5W]) with the derived direct
  image restricted to `D_QCoh`, at the standard model: the standard-model counterpart of
  `AlgebraicGeometry.DualizingDivisor.lerayIso`.
* `derivedTildeDerivedGlobalSectionsPushforwardIso` — `(RΓ(X, F))~ ≅ Rf_*F` for `F` in
  `D_QCoh(𝒪_X)`, which is Leray followed by the counit above.

## The four reconciliations, and which of them are definitional

The statement is assembled from four results already in the library, and what stood between them
was four pairs of names for single objects. Three of the four pairs turn out to be *equal*, so
the reconciliation is `rfl` and shows up below only as the fact that the terms compose:

1. **`StacksDraft.DerivedHom.derivedHomAdjunction (R := A)` versus
   `derivedHomAdjunctionOverRing A`.** The first is the fixed-universe construction over `A`, the
   second is built over `ULift A` and transported back, so these are *not* equal; the comparison
   of their internal-Hom objects is
   `StacksDraft.DerivedHom.derivedHomAdjunctionHomObjCompare`, which was already in the tree
   (`Duality/DerivedTilde/AffineExtTildeIso.lean`) and is used here as it stands. The tagged
   statement of [Stacks, Tag 0A6H] (3)(a) is written with the first spelling and
   `Dualizing.dualizingDerivedHomFunctor` with the second.
2. **`(tilde.functor R).mapDerivedCategory` versus `AlgebraicGeometry.derivedTilde`.**
   `derivedTilde R` is `ObjectProperty.lift` of the former, so the underlying object of
   `(derivedTilde R).obj N` *is* `(tilde.functor R).mapDerivedCategory.obj N`, by `rfl`; the
   natural isomorphism recording this is `AlgebraicGeometry.derivedTildeCompι`. Nothing is
   proved here: the two spellings meet in the types below with no mediating map.
3. **`Stacks.Duality.derivedPushforward f` on `D(StructureSheafModules X.sheaf)` versus
   `AlgebraicGeometry.derivedGlobalSectionsOver f`.** These are different functors — one lands in
   `D(𝒪_{Spec A})`, the other in `D(A)` — and what relates them is Leray, `standardLerayIso`
   below. The *spelling* half of the reconciliation is definitional on both sides:
   `Stacks.Duality.derivedPushforward f` and `AlgebraicGeometry.derivedPushforwardModules f`,
   the functor Leray is stated with, are the same term, as are
   `(Stacks.Duality.quasiCoherentDerivedPushforward f hpush).obj F` and
   `(Stacks.Duality.derivedPushforward f).obj F.obj`, and
   `(derivedGlobalSectionsQuasicoherent R).obj E` and
   `(derivedGlobalSectionsOver (𝟙 (Spec R))).obj E.obj`. So `standardLerayIso` is
   `AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso` at one object, with its statement
   reread through those equalities.
4. **The locally small versus the standard model for `properRightAdjoint f`.** No transport is
   needed, because `Stacks.Duality.properRightAdjoint` is *already* the standard-model reading:
   `Stacks.Duality.twistedInverseImage` carries free `[HasDerivedCategory.{w} _]` binders and
   `properRightAdjoint` instantiates them at `HasDerivedCategory.standard`. What the locally
   small model holds and the standard one lacked is
   `AlgebraicGeometry.DualizingDivisor.dualityHomEquiv`, whose ingredients — the Spec–Γ
   equivalence and Leray — are supplied at the standard model by the declarations above;
   `Stacks.Duality.StandardModel.twistedInverseImageModelIso` would carry a statement the other
   way and is not needed. Everything in this file is at the standard model, so nothing crosses.

## What is assumed

`hbm`, `hbb` and `hK` are the hypotheses of
`Stacks.Duality.derivedPushforwardUnitIsoSheafHomPushforwardOfIsDualizingComplex` and are passed
to it unchanged. `hpc` and `hplus` are the hypotheses of [Stacks, Tag 0A6H] (3)(a),
`AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso`: the source of the derived internal
Hom must be pseudo-coherent and its target bounded below. Neither is discharged here. For the
pseudo-coherence of `RΓ(X, ω_X^•)` the library's nearest statement is
`AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_obj_of_isPseudoCoherent`, whose
dévissage hypothesis is not available at this generality.

*No `@[stacks]` attribute is placed on anything in this file, and no tag's coverage changes.*
Nothing here states a tag that its inputs do not already state: it is the composite of
[Stacks, Tag 0GEW] and [Stacks, Tag 08DI] (through
`derivedPushforwardUnitIsoSheafHomPushforwardOfIsDualizingComplex`) with [Stacks, Tag 0A6H]
(3)(a), [Stacks, Tag 06Z0] and [Stacks, Tag 0D5W].

## Implementation notes

Everything is read at `CategoryTheory.HasDerivedCategory.standard`, which is the model all five
inputs are stated at. The locally small instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` arrive through the imports as *global*
instances, so they outrank a file-level local instance; they are erased here rather than
outweighed, exactly as `Duality/ProperDualizingTraceUnit.lean` and
`Duality/ModelComparisonRightAdjointTraceUnit.lean` do. That the terms below compose at all is
itself the check that no other model leaked in, since each input's type has its model baked in.

`AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` is the restriction of
`RΓ(Spec A, -)` to `D_QCoh(𝒪_{Spec A})`, so it cannot be applied to the derived internal Hom,
which is an object of the ambient `D(𝒪_{Spec A})`. The chain below therefore runs through
`AlgebraicGeometry.derivedGlobalSectionsOver (𝟙 (Spec A))` on the ambient category and crosses
to the restricted spelling only where the equivalence of [Stacks, Tag 06Z0] demands it, which is
the definitional step recorded as reconciliation 3.

## References

* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

universe u

namespace Stacks.Duality

/-! ### The derived Spec–Γ equivalence at the standard model -/

section SpecGamma

variable (A : Type u) [CommRing A]

/-- **[Stacks, Tag 06Z0] at the standard model.** Derived sheafification
`D(A) ≌ D_QCoh(𝒪_{Spec A})`, as an equivalence.

This is `AlgebraicGeometry.DualizingDivisor.tildeEquivalence` read at the standard model: the
witness is `AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence` instead of the locally
small `AlgebraicGeometry.derivedTilde_isEquivalence`. -/
def standardTildeEquivalence :
    DerivedCategory (ModuleCat.{u} A) ≌
      quasiCoherentDerivedCategory (Spec (CommRingCat.of A)) :=
  @Functor.asEquivalence _ _ _ _ (derivedTilde (CommRingCat.of A))
    (StandardModel.derivedTilde_isEquivalence (CommRingCat.of A))

/-- The inverse of derived sheafification is `RΓ(Spec A, -)` on `D_QCoh(𝒪_{Spec A})`: both are
right adjoint to derived sheafification, which at the standard model is
`AlgebraicGeometry.StandardModel.derivedTildeQuasicoherentAdjunction`. -/
def standardTildeEquivalenceInverseIso :
    (standardTildeEquivalence A).inverse ≅
      derivedGlobalSectionsQuasicoherent (CommRingCat.of A) :=
  (standardTildeEquivalence A).toAdjunction.rightAdjointUniq
    (StandardModel.derivedTildeQuasicoherentAdjunction (CommRingCat.of A))

/-- **The unit of [Stacks, Tag 06Z0] at the standard model.** For `M` in `D(A)` the canonical
comparison `M ⟶ RΓ(Spec A, M̃)` is an isomorphism: it is the unit of the equivalence
`standardTildeEquivalence`, with the inverse functor named by
`standardTildeEquivalenceInverseIso`. -/
def standardTildeGlobalSectionsUnitIso (M : DerivedCategory (ModuleCat.{u} A)) :
    M ≅ (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj
      ((derivedTilde (CommRingCat.of A)).obj M) :=
  (standardTildeEquivalence A).unitIso.app M ≪≫
    (standardTildeEquivalenceInverseIso A).app ((derivedTilde (CommRingCat.of A)).obj M)

/-- **The counit of [Stacks, Tag 06Z0] at the standard model.** For `E` in `D_QCoh(𝒪_{Spec A})`
the canonical comparison `RΓ(Spec A, E)~ ⟶ E` is an isomorphism. -/
def standardTildeGlobalSectionsCounitIso
    (E : quasiCoherentDerivedCategory (Spec (CommRingCat.of A))) :
    (derivedTilde (CommRingCat.of A)).obj
        ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj E) ≅ E :=
  (derivedTilde (CommRingCat.of A)).mapIso
      ((standardTildeEquivalenceInverseIso A).app E).symm ≪≫
    (standardTildeEquivalence A).counitIso.app E

end SpecGamma

/-! ### Leray over the base ring at the standard model -/

section Leray

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [QuasiCompact f] [QuasiSeparated f]
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **[Stacks, Tag 0D5W] over the base ring, at the standard model, with the derived direct image
restricted to `D_QCoh`.** For `F` in `D_QCoh(𝒪_X)`,

`RΓ(X, F) ≅ RΓ(Spec A, Rf_*F)`,

the right-hand side being derived global sections on `D_QCoh(𝒪_{Spec A})` applied to the
restricted derived direct image.

This is `AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso` at the single object `F.obj`.
Three definitional equalities are used to reread its statement in the restricted spelling, and
they are the content of the third reconciliation named in the module documentation:
`AlgebraicGeometry.derivedPushforwardModules f` is `Stacks.Duality.derivedPushforward f`,
the underlying object of `(quasiCoherentDerivedPushforward f hpush).obj F` is
`(derivedPushforward f).obj F.obj`, and `derivedGlobalSectionsQuasicoherent` is
`RΓ(Spec A, -)` composed with the inclusion. This is the standard-model counterpart of
`AlgebraicGeometry.DualizingDivisor.lerayIso`. -/
def standardLerayIso (F : quasiCoherentDerivedCategory X) :
    (derivedGlobalSectionsOver f).obj F.obj ≅
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj
        ((quasiCoherentDerivedPushforward f hpush).obj F) :=
  (derivedGlobalSectionsOverPushforwardIso f).app F.obj

/-- **`(RΓ(X, F))~ ≅ Rf_*F` for `F` in `D_QCoh(𝒪_X)`.** Derived sheafification of the `A`-linear
derived global sections of `F` is the restricted derived direct image of `F`.

Leray (`standardLerayIso`) rewrites `RΓ(X, F)` as `RΓ(Spec A, Rf_*F)`, and the counit of
[Stacks, Tag 06Z0] (`standardTildeGlobalSectionsCounitIso`) sheafifies that back to `Rf_*F`;
the counit is invertible precisely because `Rf_*F` has quasi-coherent cohomology, which is the
hypothesis `hpush`. -/
def derivedTildeDerivedGlobalSectionsPushforwardIso (F : quasiCoherentDerivedCategory X) :
    (derivedTilde (CommRingCat.of A)).obj ((derivedGlobalSectionsOver f).obj F.obj) ≅
      (quasiCoherentDerivedPushforward f hpush).obj F :=
  (derivedTilde (CommRingCat.of A)).mapIso (standardLerayIso f hpush F) ≪≫
    standardTildeGlobalSectionsCounitIso A _

end Leray

/-! ### The duality transport -/

section Transport

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] [CompactSpace X] [QuasiSeparatedSpace X]
  [IsNoetherian X]

omit [IsNoetherianRing A] [IsProper f] [AlgebraicGeometry.IsNoetherian X] in
/-- **`f^×(ω̃_A^•)` is the relative dualizing complex of [Stacks, Tag 0AWI].** The value of
`Stacks.Duality.properRightAdjoint` is `Stacks.Duality.relativeDualizingComplex` at the standard
model, by definition: `properRightAdjoint f` is `Stacks.Duality.twistedInverseImage` with its free
`HasDerivedCategory` binders instantiated at `HasDerivedCategory.standard`, and
`relativeDualizingComplex` is that functor applied to the chosen object of `D_QCoh(𝒪_Y)`.

This records the spelling in which the statements below are to be read: `ω_X^•` there is written
`(properRightAdjoint f).obj ω̃_A^•`, which is `relativeDualizingComplex f _ ω̃_A^•`. -/
theorem properRightAdjoint_obj_eq_relativeDualizingComplex
    (K : quasiCoherentDerivedCategory (Spec (CommRingCat.of A))) :
    (properRightAdjoint f).obj K =
      relativeDualizingComplex f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f) K :=
  rfl

/-- **`RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)`.** Let `A` be a Noetherian ring, let
`f : X ⟶ Spec A` be proper, let `ω_A^•` be an object of `D(A)` bounded below whose derived
sheafification is a dualizing complex on `Spec A`, and put `ω_X^• = f^×(ω̃_A^•)`, the relative
dualizing complex of [Stacks, Tag 0AWI]. If `RΓ(X, ω_X^•)` is pseudo-coherent then derived Hom
of `RΓ(X, ω_X^•)` into `ω_A^•`, taken in the standard `D(A)` as the tagged statement of
[Stacks, Tag 0A7C] spells it, is `RΓ(X, 𝒪_X)`.

This is the duality step inside the proof of [Stacks, Tag 0AXD]. The sheafy computation
`Stacks.Duality.derivedPushforwardUnitIsoSheafHomPushforwardOfIsDualizingComplex` gives
`Rf_*𝒪_X ≅ R𝓗om_{𝒪_{Spec A}}(Rf_*ω_X^•, ω̃_A^•)` in `D(𝒪_{Spec A})`. Both sides are carried to
`D(A)`: the left by Leray (`standardLerayIso`), the right by [Stacks, Tag 0A6H] (3)(a)
(`AlgebraicGeometry.affinePseudoCoherentDerivedSheafHomIso`), which turns the derived internal
Hom of two sheafifications into the sheafification of a derived Hom, together with the unit of
[Stacks, Tag 06Z0] (`standardTildeGlobalSectionsUnitIso`), which undoes that sheafification. The
first argument of the internal Hom is matched by `derivedTildeDerivedGlobalSectionsPushforwardIso`,
which identifies `(RΓ(X, ω_X^•))~` with `Rf_*ω_X^•`, and the derived Hom that comes out is
carried to the spelling of [Stacks, Tag 0A63] by
`StacksDraft.DerivedHom.derivedHomAdjunctionHomObjCompare`.

The hypotheses `hbm`, `hbb` and `hK` are those of
`derivedPushforwardUnitIsoSheafHomPushforwardOfIsDualizingComplex` and `hpc`, `hplus` those of
[Stacks, Tag 0A6H] (3)(a); all five are passed on unchanged.

`[CompactSpace X]`, `[QuasiSeparatedSpace X]` and `[IsNoetherian X]` are carried as instance
binders, as the inputs themselves carry them, and they are *consequences* of the hypotheses
already present rather than additional assumptions: `Spec A` is compact, so
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` gives the first and
`AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated` the second, and the third then follows
from `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.
`Stacks.Duality.nonempty_dualizingDerivedHomDerivedGlobalSectionsRelativeDualizing_iso` is this
statement with those three discharged. -/
def dualizingDerivedHomDerivedGlobalSectionsRelativeDualizingIso
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hbm : DerivedCategoryB.derivedCategoryBMinus (fun N : X.Modules => N.IsCoherent)
      ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj)
    (hbb : DerivedCategoryB.IsBoundedBelow
      ((derivedTilde (CommRingCat.of A)).obj ωA).obj)
    (hK : IsDualizingComplex ((derivedTilde (CommRingCat.of A)).obj ωA).obj)
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver f).obj
        ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj))
    (hplus : (DerivedCategory.TStructure.t).plus ωA) :
    letI := derivedMonoidalStructure X.sheaf
    (Dualizing.dualizingDerivedHomFunctor.{u, u} A ωA).obj
        (op ((derivedGlobalSectionsOver f).obj
          ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj)) ≅
      (derivedGlobalSectionsOver f).obj
        (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf))) := by
  letI := derivedMonoidalStructure X.sheaf
  haveI : IsNoetherian (Spec (CommRingCat.of A)) := isNoetherian_Spec.mpr ‹_›
  -- `ω_X^• = f^×(ω̃_A^•)` and `RΓ(X, ω_X^•)`.
  have eG : ((derivedTilde (CommRingCat.of A)).obj
        ((derivedGlobalSectionsOver f).obj
          ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj)).obj ≅
      (derivedPushforward f).obj
        ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj :=
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (A := (Spec (CommRingCat.of A)).Modules)
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf))).mapIso
      (derivedTildeDerivedGlobalSectionsPushforwardIso f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f) _)
  -- `RHom_A(RΓ(X, ω_X^•), ω_A^•)` in the spelling of [Stacks, Tag 0A63], then in the
  -- fixed-universe spelling of [Stacks, Tag 0A6H] (3)(a).
  refine (StacksDraft.DerivedHom.derivedHomAdjunctionHomObjCompare A _ ωA).symm ≪≫
    standardTildeGlobalSectionsUnitIso A _ ≪≫ ?_
  -- [Stacks, Tag 0A6H] (3)(a): the sheafified derived Hom is a derived internal Hom.
  refine (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
      (affinePseudoCoherentDerivedSheafHomIso (CommRingCat.of A) _ ωA hpc hplus).symm ≪≫ ?_
  -- `(RΓ(X, ω_X^•))~ ≅ Rf_*ω_X^•`, in the contravariant slot.
  refine (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
      (((derivedSheafHom (Spec (CommRingCat.of A)).sheaf).mapIso eG.symm.op).app
        ((derivedTilde (CommRingCat.of A)).obj ωA).obj) ≪≫ ?_
  -- [Stacks, Tag 0GEW] with [Stacks, Tag 08DI]: the internal Hom is `Rf_*𝒪_X`.
  refine (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
      (derivedPushforwardUnitIsoSheafHomPushforwardOfIsDualizingComplex f
        ((derivedTilde (CommRingCat.of A)).obj ωA) hbm hbb hK).symm ≪≫ ?_
  -- Leray again, on the structure sheaf.
  exact ((derivedGlobalSectionsOverPushforwardIso f).app
    (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)))).symm

omit [CompactSpace X] [QuasiSeparatedSpace X] [AlgebraicGeometry.IsNoetherian X] in
/-- **`RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)`**, with the three topological instance binders of
`Stacks.Duality.dualizingDerivedHomDerivedGlobalSectionsRelativeDualizingIso` discharged, so that
the only hypotheses are that `A` is Noetherian, that `f` is proper, and the five hypotheses the
inputs of that isomorphism carry. -/
theorem nonempty_dualizingDerivedHomDerivedGlobalSectionsRelativeDualizing_iso
    (ωA : DerivedCategory (ModuleCat.{u} A)) :
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X := ⟨⟩
    letI := derivedMonoidalStructure X.sheaf
    DerivedCategoryB.derivedCategoryBMinus (fun N : X.Modules => N.IsCoherent)
        ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj →
      DerivedCategoryB.IsBoundedBelow ((derivedTilde (CommRingCat.of A)).obj ωA).obj →
      IsDualizingComplex ((derivedTilde (CommRingCat.of A)).obj ωA).obj →
      StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((derivedGlobalSectionsOver f).obj
          ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj) →
      (DerivedCategory.TStructure.t).plus ωA →
      Nonempty ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ωA).obj
          (op ((derivedGlobalSectionsOver f).obj
            ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj)) ≅
        (derivedGlobalSectionsOver f).obj
          (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)))) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  intro hbm hbb hK hpc hplus
  exact ⟨dualizingDerivedHomDerivedGlobalSectionsRelativeDualizingIso f ωA hbm hbb hK hpc hplus⟩

end Transport

end Stacks.Duality

end
