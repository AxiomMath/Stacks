module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectAffine

/-!
# Coherence on a locally Noetherian scheme

On a locally Noetherian scheme a quasi-coherent module of finite type is coherent, and with the
converse (which holds on any ringed space) this closes the five-way equivalence of
[Stacks, Tag 01XZ]: coherent, quasi-coherent of finite type, of finite presentation, the `tilde`
of a finite module on every affine open, and the same on *some* affine open covering.

The engine is `isFiniteType_of_mono`: on a locally Noetherian scheme a quasi-coherent submodule
of a quasi-coherent module of finite type is of finite type. Over an affine open `U` the ambient
module is the `tilde` of a finite `Γ(X, U)`-module, which is a Noetherian module because
`Γ(X, U)` is a Noetherian ring; the submodule's module of sections injects into it, hence is
finite as well, and finiteness over every affine open is finite type by
`isFiniteType_of_cover_isFiniteTildeOn`.

Feeding that to the kernel of a map out of a finite free module gives the second condition of
coherence. The only obstacle is that the condition of [Stacks, Tag 01BV] quantifies over the
*slice* site at an open `W`, where no affine opens and no points are available, whereas the
engine lives on the open subscheme `W`. `isFiniteType_of_overEquiv_functor` is the bridge: it
transports being of finite type backwards along `AlgebraicGeometry.Scheme.Modules.overEquiv`,
the equivalence between modules on the slice site at `W` and modules on `W` as a scheme. This is
the transport whose absence is recorded as the blocking obstruction in the implementation notes
of `StacksFrontier/AlgebraicGeometry/CoherentTFAE/Basic.lean`.

## Main results

* `Stacks.SheafOfModules.isFiniteType_overEquiv_inverse` and
  `Stacks.SheafOfModules.isFiniteType_of_overEquiv_functor`: being of finite type transports
  between the slice site at an open `W` of a scheme and the open subscheme `W`.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_mono`: **on a locally Noetherian scheme
  a quasi-coherent submodule of a quasi-coherent module of finite type is of finite type.**
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_kernel`: the kernel of a morphism from a
  quasi-coherent module of finite type to a quasi-coherent module is of finite type.
* `Stacks.AlgebraicGeometry.CoherentTFAE.stacksIsCoherent_of_isQuasicoherent_of_isFiniteType`:
  **(2) ⇒ (1) of [Stacks, Tag 01XZ]**, a quasi-coherent module of finite type on a locally
  Noetherian scheme is coherent, and `isCoherent_iff_isQuasicoherent_and_isFiniteType` for the
  equivalence.
* `Stacks.AlgebraicGeometry.CoherentTFAE.stacksIsCoherent_of_mono_of_isQuasicoherent`: a
  quasi-coherent submodule of a coherent module is coherent.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_tilde`: the sheaf associated with a finite
  module over a Noetherian ring is coherent. This is the affine model, and the witness that the
  coherence predicate holds of modules other than the zero module.
* `Stacks.AlgebraicGeometry.CoherentTFAE.tfae_isCoherent`: **[Stacks, Tag 01XZ]**, the five-way
  equivalence.

## Implementation notes

`specModuleMap` is the map on sections over an affine open induced by a morphism of modules,
built as the image of that morphism under
`restrictFunctor U.ι ⋙ restrictFunctor hU.isoSpec.inv ⋙ moduleSpecΓFunctor`. Its injectivity
for a monomorphism is `injective_specModuleMap`, and rests on
`AlgebraicGeometry.mono_restrictFunctor_map` and `mono_moduleSpecΓFunctor_map`: a monomorphism of
modules on a scheme is injective on sections over every open, and both restriction along an open
immersion and taking global sections read off sections over a single open.

`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a left adjoint, so that it preserves
monomorphisms is not formal; `AlgebraicGeometry.mono_restrictFunctor_map` gets it from the
sectionwise description, that a monomorphism of modules is injective on sections over every open.

The two coherence predicates of this repository — `SheafOfModules.IsCoherent` of
Stacks Tag 01BW and `Stacks.SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean` — are the same two fields under two
names. The closure theory (Stacks 01BY, 01BZ) is stated for the second and the implications of
Stacks 01XZ already proved are stated for the first, so both are provided here:
`stacksIsCoherent_of_isQuasicoherent_of_isFiniteType` for the second and
`isCoherent'_of_isQuasicoherent_of_isFiniteType` for the first, the latter by the field-by-field
conversion. This duplication is not introduced and not resolved here. The `stacksIsCoherent_`
prefix for a conclusion in `Stacks.SheafOfModules.IsCoherent` is the convention of
`Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent` and
`AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent`; the unprefixed names in this
namespace — `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_isQuasicoherent_of_isFiniteType`
of `StacksFrontier/AlgebraicGeometry/Cohomology/LocallyNoetherian/StructureSheafCoherent.lean` and
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent` of
`StacksFrontier/AlgebraicGeometry/Cohomology/LocallyNoetherian/SubQuotient.lean` — are the
statements of the same two results for `SheafOfModules.IsCoherent`, and neither conclusion
implies the other without that conversion.

The universes are forced, not chosen: `Stacks.SheafOfModules.IsCoherent` puts the space, the
sheaf of rings, the sections and the index types of the free modules in one universe, so
everything here is at `Scheme.{u}` with `SheafOfModules.{u}` and no narrowing to `Type 0` is
needed anywhere.

`isFiniteType_overEquiv_inverse` is `Stacks.SheafOfModules.isFiniteType_pushforward` applied to
`TopologicalSpace.Opens.overEquivalence`, which is available because
`Scheme.Modules.overEquiv` is by construction a
`SheafOfModules.pushforwardPushforwardEquivalence`, so its inverse *is* a pushforward. It is
applied with all arguments explicit: with the ring sheaves left to unification the `IsIso`
instance for the comparison morphism is demanded before the sheaves are known and the
application fails.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

/-! ### Finite type across the slice site of an open of a scheme -/

section Transport

variable {X : Scheme.{u}}

/-- **Being of finite type transports from an open subscheme to the slice site.** The inverse of
`AlgebraicGeometry.Scheme.Modules.overEquiv` is a pushforward of sheaves of modules along the
equivalence of sites `TopologicalSpace.Opens.overEquivalence`, so this is
`isFiniteType_pushforward`. -/
theorem isFiniteType_overEquiv_inverse (U : X.Opens) {N : U.toScheme.Modules}
    (h : SheafOfModules.IsFiniteType.{u, u, u} N) :
    SheafOfModules.IsFiniteType.{u, u, u} ((Scheme.Modules.overEquiv U).inverse.obj N) :=
  @isFiniteType_pushforward _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Opens.overEquivalence U).functor) _ _ _ _
    ((Opens.sheafRestrictSheafEquivOver (A := RingCat.{u}) U).app X.ringCatSheaf).inv
    (Iso.isIso_inv _) (Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf) N h

/-- **Being of finite type transports from the slice site at an open to the open subscheme, and
back.** A sheaf of modules on the slice site at `U` is of finite type as soon as its image on the
open subscheme `U` is. -/
theorem isFiniteType_of_overEquiv_functor (U : X.Opens)
    {M : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    (h : SheafOfModules.IsFiniteType.{u, u, u} ((Scheme.Modules.overEquiv U).functor.obj M)) :
    SheafOfModules.IsFiniteType.{u, u, u} M := by
  have h2 := isFiniteType_overEquiv_inverse U h
  have h3 : (((Scheme.Modules.overEquiv U).functor ⋙
      (Scheme.Modules.overEquiv U).inverse).obj M).IsFiniteType := h2
  exact isFiniteType_of_iso.{u} ((Scheme.Modules.overEquiv U).unitIso.app M).symm

end Transport

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.CoherentTFAE

/-! ### Monomorphisms and sections over an affine open -/

section Sections

variable {X : Scheme.{u}}

/-- **Global sections on a spectrum preserve monomorphisms**: the global section functor reads
off the sections over `⊤`, over which a monomorphism is injective. -/
theorem mono_moduleSpecΓFunctor_map {R : CommRingCat.{u}} {A B : (Spec R).Modules} (g : A ⟶ B)
    [Mono g] : Mono (moduleSpecΓFunctor.map g) := by
  have happ : Mono (g.app ⊤) := by
    have hg : Mono ((Scheme.Modules.toPresheaf (Spec R)).map g) := by infer_instance
    exact (NatTrans.mono_iff_mono_app _).mp hg (Opposite.op ⊤)
  rw [ModuleCat.mono_iff_injective]
  exact fun x y hxy => (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp happ hxy

/-- **The `Γ(X, U)`-module map attached to a morphism of modules and an affine open `U`.** It is
the image of the morphism under the restriction to `U`, the transport to `Spec Γ(X, U)` and the
global section functor, so `specModuleMap` is to `specModule` what a functor's action on
morphisms is to its action on objects. -/
noncomputable def specModuleMap {K G : X.Modules} (f : K ⟶ G) {U : X.Opens}
    (hU : IsAffineOpen U) : specModule K hU ⟶ specModule G hU :=
  moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).map
    ((Scheme.Modules.restrictFunctor U.ι).map f))

/-- **A monomorphism of modules is injective on the module attached to an affine open.** -/
theorem injective_specModuleMap {K G : X.Modules} (f : K ⟶ G) [Mono f] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Injective (specModuleMap f hU) := by
  have h1 : Mono ((Scheme.Modules.restrictFunctor U.ι).map f) := mono_restrictFunctor_map _ f
  have : IsOpenImmersion hU.isoSpec.inv := IsOpenImmersion.of_isIso _
  have h2 : Mono ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).map
      ((Scheme.Modules.restrictFunctor U.ι).map f)) := mono_restrictFunctor_map _ _
  have h3 : Mono (specModuleMap f hU) := mono_moduleSpecΓFunctor_map _
  exact (ModuleCat.mono_iff_injective _).mp h3

/-- **A quasi-coherent module of finite type has finite module of sections over every affine
open.** This is the module-level content of (2) ⇒ (4) of [Stacks, Tag 01XZ], which
`isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType` packages as a statement about `tilde`. -/
theorem finite_specModule_of_isFiniteType (F : X.Modules) [F.IsQuasicoherent]
    [SheafOfModules.IsFiniteType.{u, u, u} F] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) (specModule F hU) :=
  have : (F.restrict U.ι).IsFiniteType := isFiniteType_restrict U.ι F
  have : (specRestrict F hU).IsFiniteType := isFiniteType_restrict hU.isoSpec.inv _
  have : (specRestrict F hU).IsQuasicoherent := inferInstance
  have h : (tilde (specModule F hU)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (M := specRestrict F hU)
      (asIso (specRestrict F hU).fromTildeΓ).symm
  (AlgebraicGeometry.tilde_isFiniteType_iff (specModule F hU)).mp h

end Sections

/-! ### Quasi-coherent submodules on a locally Noetherian scheme -/

section Noetherian

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **On a locally Noetherian scheme a quasi-coherent submodule of a quasi-coherent module of
finite type is of finite type.** Over an affine open `U` the ambient module has a finite module
of sections over the Noetherian ring `Γ(X, U)`, hence a Noetherian one; the submodule's module of
sections injects into it and is therefore finite too, and finiteness over every affine open is
finite type by (4) ⇒ (5) ⇒ (2) of [Stacks, Tag 01XZ]. -/
theorem isFiniteType_of_mono {K G : X.Modules}
    [K.IsQuasicoherent] [G.IsQuasicoherent] [SheafOfModules.IsFiniteType.{u, u, u} G]
    (ι : K ⟶ G) [Mono ι] : SheafOfModules.IsFiniteType.{u, u, u} K := by
  have h : ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFiniteTildeOn K U hU := by
    intro U hU
    have hnoeth : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hG : Module.Finite Γ(X, U) (specModule G hU) := finite_specModule_of_isFiniteType G hU
    have hN : _root_.IsNoetherian Γ(X, U) (specModule G hU) :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    have hfin : Module.Finite Γ(X, U) (specModule K hU) :=
      Module.Finite.of_injective (specModuleMap ι hU).hom (injective_specModuleMap ι hU)
    exact isFiniteTildeOn_of_finite_specModule K U hU hfin
  exact (isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn K
    (exists_affineOpenCover_isFiniteTildeOn K h)).2

/-- **On a locally Noetherian scheme the kernel of a morphism from a quasi-coherent module of
finite type to a quasi-coherent module is of finite type.** The kernel is quasi-coherent, and it
is a submodule of the source. -/
theorem isFiniteType_kernel {G H : X.Modules} [G.IsQuasicoherent]
    [SheafOfModules.IsFiniteType.{u, u, u} G] [H.IsQuasicoherent] (φ : G ⟶ H) :
    SheafOfModules.IsFiniteType.{u, u, u} (kernel φ) :=
  isFiniteType_of_mono (K := kernel φ) (G := G) (kernel.ι φ)

end Noetherian

/-! ### The second condition of coherence over an open -/

section KernelOverOpen

variable {X : Scheme.{u}}

/-- The free module on the slice site at an open `W` of a scheme is the free module on `W` as a
scheme, read through `AlgebraicGeometry.Scheme.Modules.overEquiv`. -/
noncomputable def freeOverEquivIso (W : X.Opens) (I : Type u) :
    (free I : SheafOfModules.{u} W.toScheme.ringCatSheaf) ≅
      (Scheme.Modules.overEquiv W).functor.obj
        (free I : SheafOfModules.{u} (X.ringCatSheaf.over W)) :=
  have hpc : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv W).functor := inferInstance
  have hpcd : PreservesColimitsOfShape (Discrete I) (Scheme.Modules.overEquiv W).functor :=
    hpc.preservesColimitsOfShape
  @mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ (Scheme.Modules.overEquiv W).functor I hpcd
    (Opens.sheafOfModulesEquivOverUnit W X.ringCatSheaf).symm

variable [IsLocallyNoetherian X]

/-- **The second condition of [Stacks, Tag 01BV] for a quasi-coherent module of finite type on a
locally Noetherian scheme.** The whole statement is read on the open subscheme `W`, where the
module is quasi-coherent of finite type and the free module is quasi-coherent, so that
`isFiniteType_kernel` applies; the conclusion comes back to the slice site along
`isFiniteType_of_overEquiv_functor`. -/
theorem isFiniteType_kernel_free_over (F : X.Modules) [F.IsQuasicoherent]
    [SheafOfModules.IsFiniteType.{u, u, u} F] (W : X.Opens) {I : Type u} [Finite I]
    (φ : (free I : SheafOfModules.{u} (X.ringCatSheaf.over W)) ⟶ F.over W) :
    SheafOfModules.IsFiniteType.{u, u, u} (kernel φ) := by
  have a : (free I : SheafOfModules.{u} W.toScheme.ringCatSheaf) ≅
      (Scheme.Modules.overEquiv W).functor.obj (free I) := freeOverEquivIso W I
  have b : (Scheme.Modules.overEquiv W).functor.obj (F.over W) ≅ F.restrict W.ι :=
    (Scheme.Modules.overFunctorEquiv W).app F
  have hq : (free (R := W.toScheme.ringCatSheaf) I).IsQuasicoherent :=
    AffineQcohEquivalence.isQuasicoherent_free I
  have hqr : (F.restrict W.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor W.ι F
  have hqa : ((Scheme.Modules.overEquiv W).functor.obj
      (free I : SheafOfModules.{u} (X.ringCatSheaf.over W))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso a hq
  have hfa : SheafOfModules.IsFiniteType.{u, u, u} ((Scheme.Modules.overEquiv W).functor.obj
      (free I : SheafOfModules.{u} (X.ringCatSheaf.over W))) :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} a
  have hqb : ((Scheme.Modules.overEquiv W).functor.obj (F.over W)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso b.symm hqr
  have h1 : SheafOfModules.IsFiniteType.{u, u, u}
      (kernel ((Scheme.Modules.overEquiv W).functor.map φ)) :=
    isFiniteType_kernel _
  have h2 : SheafOfModules.IsFiniteType.{u, u, u}
      ((Scheme.Modules.overEquiv W).functor.obj (kernel φ)) :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (M := kernel ((Scheme.Modules.overEquiv W).functor.map φ))
      (PreservesKernel.iso (Scheme.Modules.overEquiv W).functor φ).symm
  exact Stacks.SheafOfModules.isFiniteType_of_overEquiv_functor W h2

end KernelOverOpen

/-! ### The characterization of coherence -/

section Characterization

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **(2) ⇒ (1) of [Stacks, Tag 01XZ].** A quasi-coherent module of finite type on a locally
Noetherian scheme is coherent.

Coherence is local on the base, so it is enough to check it on `⊤`; there the first condition is
that restriction preserves finite type, and the second is `isFiniteType_kernel_free_over` after
`isFiniteType_kernel_of_epi_comp` replaces a module with finitely many generating sections by the
finite free module surjecting onto it. -/
theorem stacksIsCoherent_of_isQuasicoherent_of_isFiniteType (F : X.Modules) [F.IsQuasicoherent]
    [SheafOfModules.IsFiniteType.{u, u, u} F] : Stacks.SheafOfModules.IsCoherent F := by
  refine Stacks.SheafOfModules.isCoherent_of_coversTop F (fun _ : PUnit.{u + 1} => (⊤ : X.Opens))
    ((Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk (by simp)))
    (fun _ W _ => ⟨Stacks.SheafOfModules.isFiniteType_over_of_isFiniteType W, ?_⟩)
  intro N σ hσ g
  have hfin := hσ
  exact Stacks.SheafOfModules.isFiniteType_kernel_of_epi_comp σ.π g
    (isFiniteType_kernel_free_over F W (σ.π ≫ g))

/-- **(2) ⇒ (1) of [Stacks, Tag 01XZ]** for the coherence predicate of
Stacks Tag 01BW, `_root_.SheafOfModules.IsCoherent`. The two predicates are the same two
conditions under two names; this is the field-by-field conversion. -/
theorem isCoherent'_of_isQuasicoherent_of_isFiniteType (F : X.Modules) [F.IsQuasicoherent]
    [SheafOfModules.IsFiniteType.{u, u, u} F] : _root_.SheafOfModules.IsCoherent F :=
  have h := stacksIsCoherent_of_isQuasicoherent_of_isFiniteType F
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- **(1) ⇔ (2) of [Stacks, Tag 01XZ].** On a locally Noetherian scheme a module is coherent
exactly when it is quasi-coherent of finite type. -/
theorem isCoherent_iff_isQuasicoherent_and_isFiniteType (F : X.Modules) :
    _root_.SheafOfModules.IsCoherent F ↔
      F.IsQuasicoherent ∧ SheafOfModules.IsFiniteType.{u, u, u} F := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · have := h
    exact isQuasicoherent_isFiniteType_of_isCoherent F
  · have := h1
    have := h2
    exact isCoherent'_of_isQuasicoherent_of_isFiniteType F

/-- **A quasi-coherent submodule of a quasi-coherent module of finite type on a locally
Noetherian scheme is coherent.** This is the form in which coherence of a subsheaf is used: the
ambient module need only be assumed quasi-coherent of finite type, which by
`isCoherent_iff_isQuasicoherent_and_isFiniteType` is the same as coherent. -/
theorem stacksIsCoherent_of_mono_of_isQuasicoherent {K G : X.Modules} [K.IsQuasicoherent]
    [G.IsQuasicoherent] [SheafOfModules.IsFiniteType.{u, u, u} G] (ι : K ⟶ G) [Mono ι] :
    Stacks.SheafOfModules.IsCoherent K :=
  have := isFiniteType_of_mono ι
  stacksIsCoherent_of_isQuasicoherent_of_isFiniteType K

/-- **The sheaf associated with a finite module over a Noetherian ring is coherent.** This is the
affine model of [Stacks, Tag 01XZ], and it is what makes the coherence predicate non-vacuous: it
exhibits coherent modules other than the zero module. -/
theorem isCoherent_tilde {R : CommRingCat.{u}} [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] : Stacks.SheafOfModules.IsCoherent (tilde M) :=
  have : SheafOfModules.IsFiniteType.{u, u, u} (tilde M) :=
    (AlgebraicGeometry.tilde_isFiniteType_iff M).mpr inferInstance
  stacksIsCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **[Stacks, Tag 01XZ].** For a module on a locally Noetherian scheme the following are
equivalent:

1. it is coherent;
2. it is quasi-coherent and of finite type;
3. it is of finite presentation;
4. on every affine open `U` it is the `tilde` of a finite `Γ(X, U)`-module;
5. the same on the members of some affine open covering.

The implications not using the Noetherian hypothesis are the ones already proved in
`StacksFrontier/AlgebraicGeometry/CoherentTFAE/` and
`StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/FiniteTilde.lean`; the one that uses it is
(2) ⇒ (1). -/
@[stacks 01XZ]
theorem tfae_isCoherent (F : X.Modules) :
    List.TFAE
      [_root_.SheafOfModules.IsCoherent F,
        F.IsQuasicoherent ∧ SheafOfModules.IsFiniteType.{u, u, u} F,
        F.IsFinitePresentation,
        ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFiniteTildeOn F U hU,
        ∃ (ι : Type u) (U : ι → X.Opens),
          IsOpenCover U ∧ ∀ i, ∃ hU : IsAffineOpen (U i), IsFiniteTildeOn F (U i) hU] := by
  tfae_have 1 → 2 := (isCoherent_iff_isQuasicoherent_and_isFiniteType F).1
  tfae_have 2 → 4 := by
    intro ⟨h1, h2⟩ U hU
    have := h1
    have := h2
    exact isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType F U hU
  tfae_have 4 → 5 := exists_affineOpenCover_isFiniteTildeOn F
  tfae_have 5 → 2 := isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn F
  tfae_have 2 → 1 := (isCoherent_iff_isQuasicoherent_and_isFiniteType F).2
  tfae_have 1 → 3 := by
    intro h
    have := h
    exact isFinitePresentation_of_isCoherent' F
  tfae_have 3 → 2 := isQuasicoherent_isFiniteType_of_isFinitePresentation F
  tfae_finish

end Characterization

end Stacks.AlgebraicGeometry.CoherentTFAE

end
