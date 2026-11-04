module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local

/-!
# Towards the coherence TFAE on a locally Noetherian scheme

[Stacks, Tag 01XZ] asserts that on a locally Noetherian scheme `X` the following are equivalent
for an `𝒪_X`-module `F`:

1. `F` is coherent;
2. `F` is quasi-coherent and of finite type;
3. `F` is of finite presentation;
4. on every affine open `U`, `F|_U` is `M^~` for a finite `Γ(X, U)`-module `M`;
5. there is an affine open covering on which that happens.

The full equivalence is not assembled here; it is
`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae`. What is proved here is every
implication that does not have (1) as its conclusion, namely (1) ⇒ (2), (1) ⇒ (3), (3) ⇒ (2),
(4) ⇒ (5) and (5) ⇒ (2), together with the predicate of (4) in library vocabulary. The
implementation notes say where the others are.

## Main definitions

* `Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn`: the predicate of [Stacks, Tag 01XZ]
  (4) at one affine open — that `F|_U` is the `tilde` of a finite module, read through the
  canonical isomorphism `U ≅ Spec Γ(X, U)`.

## Main results

* `isQuasicoherent_isFiniteType_of_isCoherent`: (1) ⇒ (2).
* `isFinitePresentation_of_isCoherent'`: (1) ⇒ (3).
* `isQuasicoherent_isFiniteType_of_isFinitePresentation`: (3) ⇒ (2).
* `exists_affineOpenCover_isFiniteTildeOn`: (4) ⇒ (5).
* `isQuasicoherent_of_cover_isFiniteTildeOn` and `isFiniteType_of_cover_isFiniteTildeOn`:
  (5) ⇒ (2), in its two halves.
* `isFiniteTildeOn_of_finite_specModule`: for quasi-coherent `F`, condition (4) holds at `U` as
  soon as `specModule F hU` is a finite module. This is the step through which (2) ⇒ (4) is
  proved in `StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde`.

## Implementation notes

**Where the rest of the TFAE is.** No implication *into* (1) is proved in this file, and neither
is (2) ⇒ (4). Both are proved elsewhere, as recorded below; neither is structurally blocked.

* (2) ⇒ (4) is
  `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType`, in
  `StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde`. It feeds
  `isFiniteTildeOn_of_finite_specModule` below with finiteness of `specModule F hU` read off
  `AlgebraicGeometry.tilde_isFiniteType_iff` on `Spec Γ(X, U)`, so it does not need
  [Stacks, Tag 01PB] in the local-global form the module header once called for. The implications
  into (1) do not need it either: the kernel of `𝒪_V^I ⟶ F|_V` is finite with no finiteness
  assumption on `Γ(F|_V)` at all, being a submodule of a finite module over a Noetherian ring.

* (2) ⇒ (1), and through it (3) ⇒ (1), (4) ⇒ (1) and (5) ⇒ (1), is
  `Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`.
  The kernel condition of `Stacks.SheafOfModules.IsCoherent` quantifies over
  `φ : free I ⟶ M.over U`, so `kernel φ` is a sheaf of modules on the slice site
  `(Opens.grothendieckTopology X).over U` and `(kernel φ).IsFiniteType` has to be established by
  descending one level further. That descent exists:
  `Stacks.SheafOfModules.overKernelIso` identifies `(kernel φ).over Z` with `kernel (φ.over Z)`,
  which is exactness of `SheafOfModules.overFunctor` for kernels, and
  `Stacks.SheafOfModules.overOverEquivalence` is the iterated-slice equivalence, usable in both
  directions because it is an equivalence of categories;
  `Stacks.SheafOfModules.isFiniteType_kernel_over_aux` already combines the two.

* The slice-of-a-slice computation can also be bypassed, and that is the route
  `StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType` takes: `((kernel φ).over Z).IsFiniteType`
  is hereditary in `Z`, so the good `Z` form a sieve, the basis of affine opens makes that sieve
  covering, and `Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop` glues. The general
  criterion is `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_basis`, which uses
  neither `IsCoherentOn` nor an exactness statement for `SheafOfModules.overFunctor`.
  `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType`
  is (2) ⇒ (1) by that route, and with it 01XZ (1) ⇔ (2) ⇔ (3) and both halves of
  [Stacks, Tag 01Y1] (`isCoherent_of_mono_of_isQuasicoherent`,
  `isCoherent_of_epi_of_isQuasicoherent`).

* What the descended argument needs at an affine open `V` is only that `Γ(X, V)` is Noetherian.
  The sections of `kernel φ` over `V` embed in those of `free I`, which are finite over
  `Γ(X, V)`; no finiteness of the target module is used, which is why the one lemma above gives
  all four implications into (1) and the coherence of the structure sheaf.

* The TFAE is assembled twice, by two different routes, and both are in the library:
  `Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae` and
  `Stacks.AlgebraicGeometry.CoherentTFAE.tfae_isCoherent` (in
  `StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent`). The second route
  descends to the slice site through
  `Stacks.SheafOfModules.isFiniteType_of_overEquiv_functor`, which carries being of finite type
  back along `AlgebraicGeometry.Scheme.Modules.overEquiv` from the open subscheme `U`, rather
  than through `overKernelIso` and the iterated-slice equivalence; its (2) ⇒ (1) is
  `Stacks.AlgebraicGeometry.CoherentTFAE.stacksIsCoherent_of_isQuasicoherent_of_isFiniteType`,
  and `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent'_of_isQuasicoherent_of_isFiniteType` for
  the coherence predicate of Stacks Tag 01BW, `_root_.SheafOfModules.IsCoherent`.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherentTFAE

variable {X : Scheme.{u}}

/-! ### The predicate of condition (4) -/

/-- **Condition (4) of [Stacks, Tag 01XZ] at one affine open.** The restriction of `F` to the
affine open `U` is the `tilde` of a finite `Γ(X, U)`-module, read through the canonical
isomorphism `U ≅ Spec Γ(X, U)`. -/
def IsFiniteTildeOn (F : X.Modules) (U : X.Opens) (hU : IsAffineOpen U) : Prop :=
  ∃ M : ModuleCat.{u} (CommRingCat.of Γ(X, U)),
    Module.Finite Γ(X, U) M ∧
      Nonempty (F.restrict U.ι ≅ (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde M))

/-- **Condition (4) holds at `U` as soon as `specModule F hU` is a finite module**, for `F`
quasi-coherent. Together with `Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde` this
reduces (2) ⇒ (4) of [Stacks, Tag 01XZ] to [Stacks, Tag 01PB], the finiteness of the global
sections over an arbitrary affine open. -/
theorem isFiniteTildeOn_of_finite_specModule (F : X.Modules) (U : X.Opens)
    (hU : IsAffineOpen U) [F.IsQuasicoherent]
    (h : Module.Finite Γ(X, U) (specModule F hU)) : IsFiniteTildeOn F U hU :=
  ⟨specModule F hU, h, ⟨restrictIsoSpecTilde F hU⟩⟩

/-! ### (1) ⇒ (2) and (1) ⇒ (3) -/

/-- **(1) ⇒ (2).** A coherent module is quasi-coherent and of finite type. Both halves hold on
any ringed space, by [Stacks, Tag 01BW]. -/
theorem isQuasicoherent_isFiniteType_of_isCoherent (F : X.Modules) [F.IsCoherent] :
    F.IsQuasicoherent ∧ F.IsFiniteType :=
  ⟨isQuasicoherent_of_isCoherent F, SheafOfModules.IsCoherent.isFiniteType⟩

/-- **(1) ⇒ (3).** A coherent module is of finite presentation; this is [Stacks, Tag 01BW] (1)
on any ringed space. -/
theorem isFinitePresentation_of_isCoherent' (F : X.Modules) [F.IsCoherent] :
    F.IsFinitePresentation :=
  isFinitePresentation_of_isCoherent F

/-- **(3) ⇒ (2).** A module of finite presentation is quasi-coherent and of finite type. -/
theorem isQuasicoherent_isFiniteType_of_isFinitePresentation (F : X.Modules)
    (h : F.IsFinitePresentation) : F.IsQuasicoherent ∧ F.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := h.exists_quasicoherentData
  have hfp : σ.IsFinitePresentation := hσ
  have h1 : F.IsQuasicoherent := by constructor; exact ⟨σ⟩
  have hd : σ.localGeneratorsData.IsFiniteType := by
    constructor
    intro i
    exact (hfp.isFinite_presentation i).isFiniteType_generators
  have h2 : F.IsFiniteType := by
    constructor
    exact ⟨σ.localGeneratorsData, hd⟩
  exact ⟨h1, h2⟩

/-! ### (4) ⇒ (5) -/

/-- **(4) ⇒ (5).** The affine opens of a scheme cover it, so the universally quantified form of
condition (4) gives the existentially quantified form (5). -/
theorem exists_affineOpenCover_isFiniteTildeOn (F : X.Modules)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFiniteTildeOn F U hU) :
    ∃ (ι : Type u) (U : ι → X.Opens),
      IsOpenCover U ∧ ∀ i, ∃ hU : IsAffineOpen (U i), IsFiniteTildeOn F (U i) hU :=
  ⟨X.affineOpens, fun V => (V : X.Opens), IsOpenCover.mk (iSup_affineOpens_eq_top X),
    fun V => ⟨V.2, h _ V.2⟩⟩

/-! ### (5) ⇒ (2) -/

section Cover

variable {R : CommRingCat.{u}}

/-- Finitely many generating sections of `M^~` for a finite module `M`. -/
theorem exists_finite_generatingSections_tilde (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ σ : (tilde M).GeneratingSections, Finite σ.I := by
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹Module.Finite R ↥M›)
  have hfin : Finite ↥s := hsfin
  have hspan : Submodule.span R (Set.range ((↑) : ↥s → M)) = ⊤ := by rwa [Subtype.range_coe]
  exact ⟨tildeGeneratingSections M ((↑) : ↥s → M) hspan, hfin⟩

/-- A presentation of the pullback of `M^~` along an open immersion into `Spec R`. -/
noncomputable def presentationPullbackTilde {Y : Scheme.{u}} (f : Y ⟶ Spec R)
    [IsOpenImmersion f] (M : ModuleCat.{u} R) :
    ((Scheme.Modules.pullback f).obj (tilde M)).Presentation :=
  AffinePushforward.presentationOfIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app (tilde M))
    (Scheme.Modules.presentationRestrict f
      (presentationTilde.{u} M Set.univ (by simp) _ (Submodule.span_eq _)))

/-- Generating sections of the pullback of `M^~` along an open immersion into `Spec R`, with the
same index type as a chosen family of generating sections of `M^~`. -/
noncomputable def generatingSectionsPullbackTilde {Y : Scheme.{u}} (f : Y ⟶ Spec R)
    [IsOpenImmersion f] (M : ModuleCat.{u} R) (σ : (tilde M).GeneratingSections) :
    ((Scheme.Modules.pullback f).obj (tilde M)).GeneratingSections :=
  GeneratingSections.equivOfIso ((Scheme.Modules.restrictFunctorIsoPullback f).app (tilde M))
    (generatingSectionsRestrict f σ)

/-- The index type of `generatingSectionsPullbackTilde f M σ` is that of `σ`. -/
@[simp]
theorem generatingSectionsPullbackTilde_I {Y : Scheme.{u}} (f : Y ⟶ Spec R)
    [IsOpenImmersion f] (M : ModuleCat.{u} R) (σ : (tilde M).GeneratingSections) :
    (generatingSectionsPullbackTilde f M σ).I = σ.I :=
  rfl

end Cover

/-- **(5) ⇒ (2), quasi-coherence.** A module which on each member of an open covering is the
pullback of a `tilde` is quasi-coherent: `tilde` has a presentation, presentations restrict
along open immersions, and quasi-coherence is local. -/
theorem isQuasicoherent_of_cover_isFiniteTildeOn (F : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hcov : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, IsFiniteTildeOn F (U i) (hU i)) : F.IsQuasicoherent := by
  have hP : ∀ i, Nonempty (F.restrict (U i).ι).Presentation := by
    intro i
    obtain ⟨M, -, ⟨e⟩⟩ := h i
    exact ⟨AffinePushforward.presentationOfIso e.symm
      (presentationPullbackTilde (hU i).isoSpec.hom M)⟩
  exact AffinePushforward.isQuasicoherent_of_presentations F U hcov (fun i => (hP i).some)

/-- **(5) ⇒ (2), finite type.** A module which on each member of an open covering is the
pullback of the `tilde` of a *finite* module is of finite type, by
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections`. -/
theorem isFiniteType_of_cover_isFiniteTildeOn (F : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hcov : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, IsFiniteTildeOn F (U i) (hU i)) : F.IsFiniteType := by
  choose M hMfin he using h
  have e : ∀ i, F.restrict (U i).ι ≅
      (Scheme.Modules.pullback (hU i).isoSpec.hom).obj (tilde (M i)) := fun i => (he i).some
  have hσ : ∀ i, ∃ σ : (F.restrict (U i).ι).GeneratingSections, Finite σ.I := by
    intro i
    obtain ⟨τ, hτ⟩ := @exists_finite_generatingSections_tilde _ (M i) (hMfin i)
    exact ⟨GeneratingSections.equivOfIso (e i).symm
      (generatingSectionsPullbackTilde (hU i).isoSpec.hom (M i) τ), hτ⟩
  choose σ hσfin using hσ
  exact isFiniteType_of_restrict_generatingSections F U hcov σ hσfin

/-- **(5) ⇒ (2).** -/
theorem isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn (F : X.Modules)
    (h : ∃ (ι : Type u) (U : ι → X.Opens),
      IsOpenCover U ∧ ∀ i, ∃ hU : IsAffineOpen (U i), IsFiniteTildeOn F (U i) hU) :
    F.IsQuasicoherent ∧ F.IsFiniteType := by
  obtain ⟨ι, U, hcov, hi⟩ := h
  choose hU hV using hi
  exact ⟨isQuasicoherent_of_cover_isFiniteTildeOn F U hcov hU hV,
    isFiniteType_of_cover_isFiniteTildeOn F U hcov hU hV⟩

end Stacks.AlgebraicGeometry.CoherentTFAE

end
