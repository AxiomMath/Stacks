module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinalSectionsTop
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingAffineness
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSpecQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# The module `M ⊗_A 𝒪_X` of Situation 07UY: `p_*(M ⊗_A 𝒪_X) = M~` and `Γ(X, M ⊗_A 𝒪_X) = M`

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` such that
`H¹(X, 𝓕) = 0` for every quasi-coherent `𝒪_X`-module `𝓕` (Situation 07UY,
`AlgebraicGeometry.Space.CohomologyVanishingSituation`), let `A = Γ(X, 𝒪_X)` and let
`p : X ⟶ Spec(A)` be the canonical morphism of Stacks 05Z1.  For an `A`-module `M` the source
writes `M ⊗_A 𝒪_X` for the quasi-coherent module `p^*M~`.  **Stacks 07UZ** says that
`p_*(M ⊗_A 𝒪_X) = M~` and `Γ(X, M ⊗_A 𝒪_X) = M`.  Both are proved here, in Situation 07UY and
with nothing assumed.

## Main definitions

* `…CohomologyVanishingSituation.spaceOverIntegers`: `X` viewed as an algebraic space over
  `Spec ℤ`, the base over which the morphism `p` of Stacks 05Z1 is formed.
* `…CohomologyVanishingSituation.toSpecA`: the canonical morphism `p : X ⟶ Spec(A)`, that is
  `AlgebraicGeometry.Space.toSpecGlobalFunctions` (Stacks 05Z1 at the identity of `A`).
* `…CohomologyVanishingSituation.tildeModule`: the quasi-coherent module `M~` on `Spec(A)`, the
  image of `M` under `Mod(A) ≌ QCoh(Spec A)`
  (`AlgebraicGeometry.Space.representedSpecQuasicoherentSheavesEquivalence`).
* `…CohomologyVanishingSituation.tensorSheaf`: `M ⊗_A 𝒪_X = p^*M~`, the inverse image of
  Stacks 03LU (`AlgebraicGeometry.Space.modulePullback`).

## Main results

* `…CohomologyVanishingSituation.isIso_unit_tensorSheaf`: **the first assertion of
  Stacks 07UZ**, `p_*(M ⊗_A 𝒪_X) = M~`: the unit `M~ ⟶ p_*p^*M~` of the adjunction
  `p^* ⊣ p_*` of Stacks 03LU is an isomorphism.
* `…CohomologyVanishingSituation.globalSectionsTensorLinearEquiv`: **the second assertion of
  Stacks 07UZ**, `Γ(X, M ⊗_A 𝒪_X) = M` as `A`-modules.
* `…CohomologyVanishingSituation.isIso_toSpecA`: in Situation 07UY the morphism
  `p : X ⟶ Spec(A)` is an isomorphism.

The two assertions above are the registrations of Stacks 07UZ.  The general-site pieces of the
source's route (`Stacks.Cohomology.SiteModules.sectionTensorSheafAdjunction`,
`Stacks.Cohomology.SiteModules.sectionTensorFreeIso`,
`Stacks.Cohomology.SiteModules.isIso_sectionTensorSheafUnit_free`, which assumes that global
sections commute with a direct sum, and
`Stacks.Cohomology.SiteModules.isQuasicoherentOnSite_sectionTensor`) are not registered: they are
steps, not the statement.

## Implementation notes

*The route.*  The source proves `Γ(X, M ⊗_A 𝒪_X) = M` from right exactness of global sections
(the vanishing of `H¹`) and the computation `Γ(X, ⨁ 𝒪_X) = ⨁ A` (Stacks 073E), and then deduces
`p_*(M ⊗_A 𝒪_X) = M~` from quasi-coherence of `p_*` (Stacks 03M9).  Here the vanishing of `H¹`
is used once, through right exactness of global sections on quasi-coherent modules
(`…CohomologyVanishingSituation.surjective_sectionsMap_of_epi_of_isQuasicoherentOnSite`, built
from `AlgebraicGeometry.Space.CohomologyVanishingSituation.surjective_sectionsMap_of_shortExact`
and the closure of quasi-coherent modules under kernels), and fed to
`AlgebraicGeometry.Space.isIso_hom_of_bijective_pullbackToGlobalFunctions`: a quasi-compact,
quasi-separated algebraic space with right exact global sections, mapping to an affine scheme by
a morphism bijective on global functions, maps isomorphically.  That is proved in this
development without Stacks 07UZ (through Stacks 07V4, 07V5, 06RW and Zariski's main theorem
Stacks 082J), so there is no circularity.  Once `p` is an isomorphism, `p^*` is an equivalence
(the unit law of Stacks 03LU), so the unit of `p^* ⊣ p_*` is invertible, which is the first
assertion; and `Γ(X, p^*M~) = Γ(Spec A, p_*p^*M~) = Γ(Spec A, M~) = M`, by Stacks 0732
(`AlgebraicGeometry.Space.globalSectionsPushforwardIsoSite`), the unit, and the computation of
the global sections of `M~` at the identity chart of `Spec A` (the unit of the associated-module
adjunction of Stacks 03DX (2) and `AlgebraicGeometry.tilde.isoTop`).

*`A`-linearity.*  The identification `Γ(X, M ⊗_A 𝒪_X) = M` is a chain of additive
identifications, each semilinear for the rings it involves.  What makes the chain `A`-linear is
that `p^♯` on global sections is the canonical identification of `Γ(Spec A, 𝒪)` with `A` that
`p` was built from (`AlgebraicGeometry.Space.pullbackToGlobalFunctions_toSpecGlobalFunctions`),
read through the chart formula for the ring map of Stacks 0732
(`AlgebraicGeometry.Space.globalSectionsChartEval_globalSectionsRingHomSite`); this is
`…CohomologyVanishingSituation.globalSectionsRingHomSite_modelToSpecGlobal`.

*The base and `Spec A`.*  Stacks 05Z1 is a statement about algebraic spaces over `ℤ`, and `p` is
a morphism over `ℤ`: `Spec A` is not a scheme over `S`.  So `p` is formed on `X` viewed over the
terminal scheme (`AlgebraicGeometry.Space.viewOverIntegers`), whose small étale site, structure
sheaf, modules and global functions are those of `X`
(`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize`); `A` itself is
`…CohomologyVanishingSituation.globalFunctions`, identified with the global functions of `X`
over `ℤ` by `…CohomologyVanishingSituation.globalFunctionsOverIntegersEquiv`, and the base `S`
of the situation is arbitrary.  The ring `A` is a ring of compatible families over the étale
charts and lies in `Type (u + 1)`, so `Spec(A)` is the spectrum of a chosen ring `R` of the
working universe with `R ≅ A` (`AlgebraicGeometry.Space.GlobalFunctionsModel`), as for every
other use of `p` in this development; `M` is read as an `R`-module along `R ≅ A`.

*Universes.*  Modules are those of `AlgebraicGeometry.Space.Modules.{u, u}`, with sections in
the universe of the schemes, which is where `p^*` and `p_*` exist; the `A`-module `M` has its
carrier in `Type u`.  The situation is an arbitrary `CohomologyVanishingSituation.{u, m}`, whose
vanishing hypothesis is imposed on quasi-coherent modules with sections in `Type (max (u + 1) m)`;
it reaches modules with sections in `Type u` by raising the universe of the sections
(`SheafOfModules.uliftForPresentation`), which preserves epimorphisms, kernels and
quasi-coherence (`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`), and along which
surjectivity on global sections descends.  The three lifting statements of
`StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation` are at the amount `u + 1`
only; the versions here (`SheafOfModules.kerUliftForPresentationIsoAbove` and its companions) are
at an arbitrary amount.

*Scalars.*  The ring `A` carries both the `Ring` structure of a subring and the `CommRing`
structure `…CohomologyVanishingSituation.instCommRingGlobalFunctions`; the latter only adds
commutativity to the former, so the semiring over which `ModuleCat` and the `A`-linear statement
are elaborated is the same through either.

## References

* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

/-! ### Raising the universe of the sections by an arbitrary amount

`SheafOfModules.kerUliftForPresentationIso`, `SheafOfModules.epi_uliftForPresentationMap` and
`SheafOfModules.surjective_sectionsMap_of_ulift` of
`StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation` raise the universe of the
sections from `u` to `u + 1` only.  The statements below raise it to `max (u + 1) m` for an
arbitrary `m`, which is what reaches the vanishing hypothesis of an arbitrary
`CohomologyVanishingSituation.{u, m}`; at `m := u` they are those three. -/

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}

/-- The kernel of the universe lift of a morphism, by an arbitrary amount, is the universe lift
of its kernel.  Both are computed objectwise. -/
noncomputable def kerUliftForPresentationIsoAbove {M N : SheafOfModules.{u} R} (g : M ⟶ N) :
    (Submodule.ker (uliftForPresentationMap.{u + 1, u, u, u, max (u + 1) m} g)).toSheafOfModules ≅
      uliftForPresentation.{u + 1, u, u, u, max (u + 1) m} (Submodule.ker g).toSheafOfModules :=
  (fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun _ => LinearEquiv.toModuleIso
        { toFun := fun x => ULift.up ⟨x.1.down, ULift.down_inj.2 x.2⟩
          invFun := fun y => ⟨ULift.up y.down.1, congrArg ULift.up y.down.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl })
      (fun {_ _} _ => by ext x; rfl))

/-- The universe lift of an epimorphism, by an arbitrary amount, is an epimorphism: lifting the
sections does not change the image sieves. -/
theorem epi_uliftForPresentationMap_above [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (g : M ⟶ N) (hg : Epi g) :
    Epi (uliftForPresentationMap.{u + 1, u, u, u, max (u + 1) m} g) := by
  have := hg
  have h0 : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map g.val) :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi g
  have hfac : (PresheafOfModules.toPresheaf R.obj).map
      (uliftForPresentationMap.{u + 1, u, u, u, max (u + 1) m} g).val =
      Functor.whiskerRight ((PresheafOfModules.toPresheaf R.obj).map g.val)
        AddCommGrpCat.uliftFunctor.{max (u + 1) m} := rfl
  have h1 : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf R.obj).map g.val)
        AddCommGrpCat.uliftFunctor.{max (u + 1) m}) := inferInstance
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ (hfac ▸ h1)

/-- Raising the universe of a compatible family of sections, by an arbitrary amount. -/
noncomputable def uliftForPresentationSectionsAbove {M : SheafOfModules.{u} R} (s : M.sections) :
    (uliftForPresentation.{u + 1, u, u, u, max (u + 1) m} M).sections :=
  PresheafOfModules.sectionsMk (fun X => ULift.up (s.val X))
    (fun _ _ _ => congrArg ULift.up (s.property _))

/-- **Surjectivity on global sections descends from the universe lift**, by an arbitrary
amount. -/
theorem surjective_sectionsMap_of_uliftAbove {M N : SheafOfModules.{u} R} (g : M ⟶ N)
    (h : Function.Surjective
      (sectionsMap (uliftForPresentationMap.{u + 1, u, u, u, max (u + 1) m} g))) :
    Function.Surjective (sectionsMap g) := by
  intro t
  obtain ⟨s', hs'⟩ := h (uliftForPresentationSectionsAbove.{u, m} t)
  refine ⟨PresheafOfModules.sectionsMk (fun X => (s'.val X).down)
      (fun _ _ f => congrArg ULift.down (s'.property f)), ?_⟩
  exact PresheafOfModules.sections_ext _ _ fun X =>
    congrArg ULift.down (congrFun (congrArg Subtype.val hs') X)

end SheafOfModules

namespace AlgebraicGeometry.Space.CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m})

/-- **In Situation 07UY global sections are right exact on quasi-coherent modules**, for
modules with sections in the universe of the schemes: an epimorphism of quasi-coherent
`𝒪_X`-modules is surjective on global sections.  Its kernel is quasi-coherent, and after raising
the universe of the sections to the one at which the vanishing hypothesis of the situation is
imposed, `H¹` of it vanishes. -/
theorem surjective_sectionsMap_of_epi_of_isQuasicoherentOnSite
    ⦃M N : Modules.{u, u} T.site T.base T.containsBase T.space.1 T.space.2⦄ (g : M ⟶ N)
    (hg : Epi g) (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    Function.Surjective (_root_.SheafOfModules.sectionsMap g) := by
  have := isClosedUnderKernels_quasicoherentSheaves_smallEtale T.site T.base T.containsBase
    T.space.1 T.space.2
  have hker : (_root_.SheafOfModules.Submodule.ker g).toSheafOfModules.IsQuasicoherentOnSite :=
    _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
      (_root_.SheafOfModules.Submodule.kerIsoKernel g).symm
      ((_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_kernel g hM hN)
  refine SheafOfModules.surjective_sectionsMap_of_uliftAbove.{u, m} g ?_
  have hs : HasSheafify (smallEtaleRingedSite T.site T.base T.containsBase T.space.1 T.space.2).J
      AddCommGrpCat.{max (u + 1) m} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, m}
  have hw : (smallEtaleRingedSite T.site T.base T.containsBase T.space.1
      T.space.2).J.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) m} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, m}
  let _ : Abelian (Modules.{u, max (u + 1) m} T.site T.base T.containsBase T.space.1
      T.space.2) :=
    _root_.SheafOfModules.instAbelian _
  have hQ : (ShortComplex.mk
      (C := Modules.{u, max (u + 1) m} T.site T.base T.containsBase T.space.1 T.space.2)
      (_root_.SheafOfModules.Submodule.ker
        (_root_.SheafOfModules.uliftForPresentationMap.{u + 1, u, u, u, max (u + 1) m} g)).ι
      (_root_.SheafOfModules.uliftForPresentationMap.{u + 1, u, u, u, max (u + 1) m} g)
      (_root_.SheafOfModules.Submodule.ker_ι_comp _)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (_root_.SheafOfModules.Submodule.isLimitKernelFork _)
      mono_f := mono_of_isLimit_fork (_root_.SheafOfModules.Submodule.isLimitKernelFork _)
      epi_g := SheafOfModules.epi_uliftForPresentationMap_above.{u, m} g hg }
  exact T.surjective_sectionsMap_of_shortExact hQ
    (_root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
      (SheafOfModules.kerUliftForPresentationIsoAbove.{u, m} g).symm
      (_root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation' hker))

/-- The space of the situation viewed over `Spec ℤ`. -/
abbrev spaceOverIntegers : AlgebraicSpaces T.site (⊤_ Scheme.{u}) T.containsTerminal :=
  ⟨viewOverIntegers T.site T.base T.containsBase T.containsTerminal T.space.1,
    isAlgebraicSpace_relocalize T.site ⟨T.base, T.containsBase⟩ ⟨⊤_ Scheme.{u}, T.containsTerminal⟩
      ⟨terminal.from T.base⟩ T.space.1 T.space.2⟩

/-- The chosen small model `R ≅ A` of the global functions of `X` viewed over `Spec ℤ`. -/
def modelOverIntegers :
    GlobalFunctionsModel T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers.obj :=
  (nonempty_globalFunctionsModel T.site (⊤_ Scheme.{u}) T.containsTerminal
    T.spaceOverIntegers).some

/-- `Spec(A)`, presented as the spectrum of the small model `R ≅ A`, an object of the ambient
big fppf site over `Spec ℤ`. -/
abbrev specA : BigFppfOver T.site (⊤_ Scheme.{u}) T.containsTerminal :=
  Space.specGlobalFunctions T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers
    T.modelOverIntegers terminalIsTerminal

/-- `Spec(A)` as an algebraic space over `Spec ℤ`. -/
abbrev specSpace : AlgebraicSpaces T.site (⊤_ Scheme.{u}) T.containsTerminal :=
  _root_.AlgebraicGeometry.schemeSpace T.specA

/-- **The canonical morphism `p : X ⟶ Spec(A)` of Stacks 05Z1**, the morphism inducing the
canonical identification `Γ(Spec A, 𝒪) = A` on global functions. -/
def toSpecA : T.spaceOverIntegers ⟶ T.specSpace :=
  Space.toSpecGlobalFunctions T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers
    T.modelOverIntegers terminalIsTerminal

/-- In Situation 07UY the morphism of presheaves underlying `p : X ⟶ Spec(A)` is an
isomorphism: `X` has right exact global sections on quasi-coherent modules, is quasi-compact and
quasi-separated, and `p` is bijective on global functions. -/
theorem isIso_toSpecA_hom : IsIso T.toSpecA.hom := by
  let k : T.site.obj T.containsBase ⟶ T.site.obj T.containsTerminal := ⟨terminal.from T.base⟩
  have hX' := surjective_sectionsMap_relocalize T.site T.base (⊤_ Scheme.{u}) T.containsBase
    T.containsTerminal k T.space.2 T.spaceOverIntegers.2
    T.surjective_sectionsMap_of_epi_of_isQuasicoherentOnSite
  have hqc' : IsQuasiCompactSpace T.site (⊤_ Scheme.{u}) T.containsTerminal
      T.spaceOverIntegers.1 :=
    isQuasiCompactSpace_relocalize T.site T.base T.containsBase T.containsTerminal k
      T.quasiCompact
  have hqs' : IsAbsolutelyQuasiSeparated T.site (⊤_ Scheme.{u}) T.containsTerminal
      T.containsTerminal T.spaceOverIntegers.1 :=
    isAbsolutelyQuasiSeparated_viewOverIntegers T.site T.base T.containsBase T.containsTerminal
      T.space.1 T.quasiSeparated
  have hp : Function.Bijective (pullbackToGlobalFunctions T.site (⊤_ Scheme.{u})
      T.containsTerminal T.spaceOverIntegers T.specA T.toSpecA) := by
    rw [toSpecA, Space.pullbackToGlobalFunctions_toSpecGlobalFunctions]
    exact T.modelOverIntegers.equiv.bijective.comp
      (Scheme.ΓSpecIso T.modelOverIntegers.ring).commRingCatIsoToRingEquiv.bijective
  exact isIso_hom_of_bijective_pullbackToGlobalFunctions hX' hqc' T.toSpecA T.containsTerminal
    hqs' hp

/-- **In Situation 07UY, `p : X ⟶ Spec(A)` is an isomorphism.** -/
instance isIso_toSpecA : IsIso T.toSpecA :=
  have : IsIso ((ObjectProperty.ι _).map T.toSpecA) := T.isIso_toSpecA_hom
  isIso_of_reflects_iso T.toSpecA (ObjectProperty.ι _)

/-- `p` as an isomorphism of algebraic spaces. -/
def toSpecAIso : T.spaceOverIntegers ≅ T.specSpace :=
  asIso T.toSpecA

/-- The isomorphism `toSpecAIso` is `p`. -/
theorem toSpecAIso_hom : T.toSpecAIso.hom = T.toSpecA := rfl

/-- `p^*` is full, `p` being an isomorphism. -/
instance full_modulePullback_toSpecA :
    (modulePullback T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA).Full :=
  ((modulePushforwardCoherence T.site (⊤_ Scheme.{u}) T.containsTerminal).modulePullbackEquivalence
    T.toSpecAIso).full_functor

/-- `p^*` is faithful, `p` being an isomorphism. -/
instance faithful_modulePullback_toSpecA :
    (modulePullback T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA).Faithful :=
  ((modulePushforwardCoherence T.site (⊤_ Scheme.{u}) T.containsTerminal).modulePullbackEquivalence
    T.toSpecAIso).faithful_functor

/-- The identification `R ≅ A`: the small model ring is the ring of global functions of `X`
viewed over `Spec ℤ`, which is the ring `A` of global functions of `X`. -/
def modelRingEquiv : T.modelOverIntegers.ring ≃+* T.globalFunctions :=
  (T.modelOverIntegers.equiv.trans (globalFunctionsRelocalizeEquiv T.site T.base (⊤_ Scheme.{u})
    T.containsBase T.containsTerminal ⟨terminal.from T.base⟩ T.space.1)).trans
    T.globalFunctionsRingEquiv.symm

/-- The identification `R ≅ A` as a ring homomorphism. -/
abbrev modelRingHom : T.modelOverIntegers.ring →+* T.globalFunctions :=
  T.modelRingEquiv.toRingHom

/-- The equivalence `Mod(R) ≌ QCoh(Spec R)`, `N ↦ N~`, read on the small étale site of the
algebraic space `Spec(A)`. -/
abbrev tildeEquivalence :=
  representedSpecQuasicoherentSheavesEquivalence T.site (⊤_ Scheme.{u}) T.containsTerminal
    T.modelOverIntegers.ring T.specA rfl

variable (M : ModuleCat.{u} T.globalFunctions)

/-- **The quasi-coherent module `M~` on `Spec(A)`** attached to an `A`-module `M`: `M` read as
a module over `R ≅ A`, then `N ↦ N~`. -/
def tildeModule : Modules.{u, u} T.site (⊤_ Scheme.{u}) T.containsTerminal
    T.specSpace.1 T.specSpace.2 :=
  (T.tildeEquivalence.functor.obj ((ModuleCat.restrictScalars T.modelRingHom).obj M)).obj

/-- `M~` unfolded: the tilde of `M` on `Spec R`, transported to the small étale site of the
scheme `Spec R` (Stacks 03DX (2)) and then to that of the algebraic space `Spec(A)`. -/
theorem tildeModule_eq : T.tildeModule M =
    representedSmallEtaleModule T.site (⊤_ Scheme.{u}) T.containsTerminal T.specA
      ((SmallEtale.associatedModule (associatedBigEtaleSite T.site) _ T.specA.left.property).obj
        (tilde ((ModuleCat.restrictScalars T.modelRingHom).obj M))) := rfl

/-- **The module `M ⊗_A 𝒪_X = p^*M~`** of Situation 07UY, an `𝒪_X`-module on `X` viewed over
`Spec ℤ`. -/
def tensorSheaf : Modules.{u, u} T.site (⊤_ Scheme.{u}) T.containsTerminal
    T.spaceOverIntegers.1 T.spaceOverIntegers.2 :=
  (modulePullback T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA).obj (T.tildeModule M)

/-- **Stacks 07UZ, first assertion: `p_*(M ⊗_A 𝒪_X) = M~`.**  In Situation 07UY, for every
`A`-module `M`, the unit `M~ ⟶ p_*p^*M~ = p_*(M ⊗_A 𝒪_X)` of the adjunction `p^* ⊣ p_*` of
Stacks 03LU is an isomorphism.

`p` is an isomorphism (`…CohomologyVanishingSituation.isIso_toSpecA`), so `p^*` is fully faithful
and the unit is invertible. -/
@[stacks 07UZ "first assertion: p_*(M ⊗_A 𝒪_X) = M~, the unit M~ ⟶ p_*p^*M~ of the adjunction \
p^* ⊣ p_* being an isomorphism"]
theorem isIso_unit_tensorSheaf :
    IsIso ((modulePullbackAdjunction T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA).unit.app
      (T.tildeModule M)) :=
  NatIso.isIso_app_of_isIso _ _

/-- `p_*(M ⊗_A 𝒪_X) ≅ M~`, the inverse of the unit of `p^* ⊣ p_*` at `M~`. -/
def pushforwardTensorSheafIso :
    (modulePushforward T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA).obj
      (T.tensorSheaf M) ≅ T.tildeModule M :=
  (@asIso _ _ _ _ _ (T.isIso_unit_tensorSheaf M)).symm

/-- `M` read as a module over the small model `R ≅ A`. -/
abbrev restrictModel : ModuleCat.{u} T.modelOverIntegers.ring :=
  (ModuleCat.restrictScalars T.modelRingHom).obj M

/-- The scheme `Spec R` underlying `Spec A`. -/
abbrev specScheme : Scheme.{u} :=
  (BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj T.specA

/-- `(M~)^a` on the small étale site of the scheme `Spec R`. -/
abbrev assocTilde :=
  (SmallEtale.associatedModule (associatedBigEtaleSite T.site) T.specScheme
    T.specA.left.property).obj (tilde (T.restrictModel M))

/-- The identity chart of `Spec A`. -/
abbrev idChart := idEtaleChart T.site (⊤_ Scheme.{u}) T.containsTerminal T.specA

/-- The comparison of the small étale site of the algebraic space `Spec(A)` with that of the
scheme `Spec R`. -/
abbrev chartEquiv :=
  representedSmallEtaleEquivalence T.site (⊤_ Scheme.{u}) T.containsTerminal T.specA

/-- The identity chart of `Spec(A)` and the open `⊤` of `Spec R` are both final objects of the
small étale site of `Spec R`. -/
def idChartIsoTop : T.chartEquiv.functor.obj T.idChart ≅
    SmallEtale.opensObj (associatedBigEtaleSite T.site) T.specScheme T.specA.left.property ⊤ :=
  ((isTerminalIdEtaleChart T.site (⊤_ Scheme.{u}) T.containsTerminal T.specA).isTerminalObj
    T.chartEquiv.functor).uniqueUpToIso
    (SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite T.site) T.specScheme
      T.specA.left.property)

/-- The map `M ⟶ M~(identity chart)`: `M = Γ(Spec R, M~)` (`AlgebraicGeometry.tilde.isoTop`),
the unit of the associated-module adjunction at `⊤`, and restriction to the identity chart. -/
def tildeToIdChart (m : T.restrictModel M) : (T.tildeModule M).val.obj (op T.idChart) :=
  (T.assocTilde M).val.map (T.idChartIsoTop).hom.op
    ((((SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite T.site) T.specScheme
      T.specA.left.property).unit.app (tilde (T.restrictModel M))).val.app (op ⊤)).hom
      ((tilde.isoTop (T.restrictModel M)).hom.hom m))

/-- The structure sheaf of rings of `Spec A`. -/
abbrev specRingSheaf :=
  Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite T.site (⊤_ Scheme.{u})
    T.containsTerminal T.specSpace.1 T.specSpace.2).O

/-- The ring map `R ⟶ 𝒪(identity chart)` through which `R` acts on `M~(identity chart)`. -/
def tildeRingHom : T.modelOverIntegers.ring →+* T.specRingSheaf.obj.obj (op T.idChart) :=
  ((SmallEtale.structureSheaf (associatedBigEtaleSite T.site) T.specScheme
      T.specA.left.property).obj.map T.idChartIsoTop.hom.op).hom.comp
    (((SmallEtale.structureMap (associatedBigEtaleSite T.site) T.specScheme
      T.specA.left.property).hom.app (op ⊤)).hom.comp
      (Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom)

/-- `tildeToIdChart` is semilinear along `tildeRingHom`. -/
theorem tildeToIdChart_smul (r : T.modelOverIntegers.ring) (m : T.restrictModel M) :
    T.tildeToIdChart M (r • m) = T.tildeRingHom r • T.tildeToIdChart M m := by
  unfold tildeToIdChart
  rw [map_smul]
  have h1 : ∀ y : (modulesSpecToSheaf.obj (tilde (T.restrictModel M))).presheaf.obj (op ⊤),
      r • y = (show (Spec T.modelOverIntegers.ring).ringCatSheaf.obj.obj (op ⊤) from
        (Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom r) •
        (show (tilde (T.restrictModel M)).val.obj (op ⊤) from y) := by
    intro y
    change ((Spec T.modelOverIntegers.ring).ringCatSheaf.obj.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤))).hom
      ((Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom r) •
        (show (tilde (T.restrictModel M)).val.obj (op ⊤) from y) = _
    rw [Subsingleton.elim ((Limits.initialOpOfTerminal Limits.isTerminalTop).to
      (op (⊤ : (Spec T.modelOverIntegers.ring).Opens))) (𝟙 _), CategoryTheory.Functor.map_id]
    rfl
  rw [h1]
  have h2 := (((SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite T.site) T.specScheme
    T.specA.left.property).unit.app (tilde (T.restrictModel M))).val.app (op ⊤)).hom.map_smul
      ((Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom r)
      ((tilde.isoTop (T.restrictModel M)).hom.hom m)
  refine (congrArg _ h2).trans ?_
  exact (T.assocTilde M).val.map_smul T.idChartIsoTop.hom.op _ _

/-- `tildeToIdChart` is bijective: each of its three factors is an isomorphism, the unit of
the associated-module adjunction at the quasi-coherent `M~` by Stacks 03DX (2). -/
theorem bijective_tildeToIdChart : Function.Bijective (T.tildeToIdChart M) := by
  have hu : IsIso ((SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite T.site)
      T.specScheme T.specA.left.property).unit.app (tilde (T.restrictModel M))) :=
    SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite T.site) T.specScheme
      T.specA.left.property
      ⟨tilde (T.restrictModel M), (inferInstance : (tilde (T.restrictModel M)).IsQuasicoherent)⟩
  have hu' : Function.Bijective (((SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite T.site) T.specScheme T.specA.left.property).unit.app
        (tilde (T.restrictModel M))).val.app (op ⊤)).hom :=
    ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op ⊤)).mapIso
        (@asIso _ _ _ _ _ hu)).hom
  have hc : Function.Bijective ((T.assocTilde M).val.presheaf.map T.idChartIsoTop.hom.op) :=
    ConcreteCategory.bijective_of_isIso _
  exact hc.comp (hu'.comp
    (ConcreteCategory.bijective_of_isIso (tilde.isoTop (T.restrictModel M)).hom))

/-- `tildeToIdChart` as an additive map. -/
def tildeToIdChartAddHom : T.restrictModel M →+ (T.tildeModule M).val.obj (op T.idChart) where
  toFun := T.tildeToIdChart M
  map_zero' := by
    unfold tildeToIdChart
    refine (congrArg (fun z => (T.assocTilde M).val.map T.idChartIsoTop.hom.op
      ((((SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite T.site) T.specScheme
        T.specA.left.property).unit.app (tilde (T.restrictModel M))).val.app (op ⊤)).hom z))
      ((tilde.isoTop (T.restrictModel M)).hom.hom.map_zero)).trans ?_
    refine (congrArg (fun z => (T.assocTilde M).val.map T.idChartIsoTop.hom.op z)
      ((((SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite T.site) T.specScheme
        T.specA.left.property).unit.app (tilde (T.restrictModel M))).val.app
          (op ⊤)).hom.map_zero)).trans ?_
    exact ((T.assocTilde M).val.map T.idChartIsoTop.hom.op).hom.map_zero
  map_add' x y := by
    unfold tildeToIdChart
    refine (congrArg (fun z => (T.assocTilde M).val.map T.idChartIsoTop.hom.op
      ((((SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite T.site) T.specScheme
        T.specA.left.property).unit.app (tilde (T.restrictModel M))).val.app (op ⊤)).hom z))
      ((tilde.isoTop (T.restrictModel M)).hom.hom.map_add x y)).trans ?_
    refine (congrArg (fun z => (T.assocTilde M).val.map T.idChartIsoTop.hom.op z)
      ((((SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite T.site) T.specScheme
        T.specA.left.property).unit.app (tilde (T.restrictModel M))).val.app
          (op ⊤)).hom.map_add _ _)).trans ?_
    exact ((T.assocTilde M).val.map T.idChartIsoTop.hom.op).hom.map_add _ _

/-- `M ≃ M~(identity chart)`. -/
def tildeIdChartAddEquiv : T.restrictModel M ≃+ (T.tildeModule M).val.obj (op T.idChart) :=
  AddEquiv.ofBijective (T.tildeToIdChartAddHom M) (T.bijective_tildeToIdChart M)

/-- `Γ(Spec A, 𝒪)`, the ring of global sections of the structure sheaf of `Spec A`. -/
abbrev specGlobalRing :=
  RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite T.site
    (⊤_ Scheme.{u}) T.containsTerminal T.specSpace.1 T.specSpace.2).O).obj

/-- `Γ(X, 𝒪_X)` for `X` over `Spec ℤ`. -/
abbrev spaceGlobalRing :=
  RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite T.site
    (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers.1 T.spaceOverIntegers.2).O).obj

/-- `Γ(Spec A, M~)`. -/
abbrev specSections : ModuleCat.{u + 1} T.specGlobalRing :=
  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite T.site
      (⊤_ Scheme.{u}) T.containsTerminal T.specSpace.1 T.specSpace.2).O)).obj (T.tildeModule M)

/-- `Γ(X, M ⊗_A 𝒪_X)`. -/
abbrev spaceSections : ModuleCat.{u + 1} T.spaceGlobalRing :=
  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite T.site
      (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers.1 T.spaceOverIntegers.2).O)).obj
    (T.tensorSheaf M)

/-- Global sections of `M~` are its sections at the identity chart, a final object. -/
def specSectionsAddEquiv : T.specSections M ≃+ (T.tildeModule M).val.obj (op T.idChart) :=
  { Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal (T.tildeModule M)
      (isTerminalIdEtaleChart T.site (⊤_ Scheme.{u}) T.containsTerminal T.specA) with
    map_add' := fun _ _ => rfl }

/-- `Γ(Spec A, M~) ≅ Γ(X, p^* M~)` as modules over `Γ(Spec A, 𝒪)`. -/
def globalSectionsUnitIso : T.specSections M ≅
    (globalSectionsRestrictScalars T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA).obj
      (T.spaceSections M) :=
  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u} _).mapIso
      (@asIso _ _ _ _ _ (T.isIso_unit_tensorSheaf M)) ≪≫
    (globalSectionsPushforwardIsoSite T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA).app
      (T.tensorSheaf M)

/-- The ring map `R ⟶ Γ(Spec A, 𝒪)` read through evaluation at the identity chart. -/
def modelToSpecGlobal : T.modelOverIntegers.ring →+* T.specGlobalRing :=
  (globalSectionsChartRingEquiv T.site (⊤_ Scheme.{u}) T.containsTerminal T.specSpace
    (isTerminalIdEtaleChart T.site (⊤_ Scheme.{u}) T.containsTerminal T.specA)).symm.toRingHom.comp
    T.tildeRingHom

/-- `modelToSpecGlobal r` takes the value `tildeRingHom r` at the identity chart. -/
theorem modelToSpecGlobal_eval (r : T.modelOverIntegers.ring) :
    (T.modelToSpecGlobal r).1 (op T.idChart) = T.tildeRingHom r :=
  (globalSectionsChartRingEquiv T.site (⊤_ Scheme.{u}) T.containsTerminal T.specSpace
    (isTerminalIdEtaleChart T.site (⊤_ Scheme.{u}) T.containsTerminal T.specA)).apply_symm_apply
      (T.tildeRingHom r)

/-- The additive identification `M ≃ Γ(X, M ⊗_A 𝒪_X)`:
`M = M~(identity chart) = Γ(Spec A, M~) = Γ(X, p^*M~)`. -/
def globalSectionsTensorAddEquiv : T.restrictModel M ≃+ T.spaceSections M :=
  (T.tildeIdChartAddEquiv M).trans ((T.specSectionsAddEquiv M).symm.trans
    (T.globalSectionsUnitIso M).toLinearEquiv.toAddEquiv)

/-- `globalSectionsTensorAddEquiv` is semilinear along `p^♯ ∘ modelToSpecGlobal`. -/
theorem globalSectionsTensorAddEquiv_smul (r : T.modelOverIntegers.ring)
    (m : T.restrictModel M) :
    T.globalSectionsTensorAddEquiv M (r • m) =
      globalSectionsRingHomSite T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA
        (T.modelToSpecGlobal r) • T.globalSectionsTensorAddEquiv M m := by
  have h1 : (T.tildeIdChartAddEquiv M) (r • m) = T.tildeRingHom r • T.tildeIdChartAddEquiv M m :=
    T.tildeToIdChart_smul M r m
  have h2 : (T.specSectionsAddEquiv M).symm (T.tildeRingHom r • T.tildeIdChartAddEquiv M m) =
      T.modelToSpecGlobal r • (T.specSectionsAddEquiv M).symm (T.tildeIdChartAddEquiv M m) := by
    apply (T.specSectionsAddEquiv M).injective
    rw [AddEquiv.apply_symm_apply]
    change _ = (T.modelToSpecGlobal r).1 (op T.idChart) • (T.specSectionsAddEquiv M)
      ((T.specSectionsAddEquiv M).symm (T.tildeIdChartAddEquiv M m))
    rw [T.modelToSpecGlobal_eval r, AddEquiv.apply_symm_apply]
  simp only [globalSectionsTensorAddEquiv, AddEquiv.trans_apply]
  refine (congrArg (fun x => (T.globalSectionsUnitIso M).hom.hom
    ((T.specSectionsAddEquiv M).symm x)) h1).trans ?_
  refine (congrArg (fun x => (T.globalSectionsUnitIso M).hom.hom x) h2).trans ?_
  exact (T.globalSectionsUnitIso M).hom.hom.map_smul _ _

/-- `R` acts on `M~(identity chart)` through `Γ(Spec R, 𝒪) = R`: the identity chart lies over
`Spec R` by the identity. -/
theorem tildeRingHom_apply (r : T.modelOverIntegers.ring) :
    T.tildeRingHom r = (show T.specRingSheaf.obj.obj (op T.idChart) from
      (Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom r) := by
  unfold tildeRingHom
  simp only
  let F := _root_.AlgebraicGeometry.SmallEtale.inclusion (associatedBigEtaleSite T.site)
    T.specScheme
    T.specA.left.property ⋙ Over.post (associatedBigEtaleSite T.site).inclusion
  have hW : (F.obj (T.chartEquiv.functor.obj T.idChart)).hom = 𝟙 _ := rfl
  have hTop : (F.obj (SmallEtale.opensObj (associatedBigEtaleSite T.site) T.specScheme
      T.specA.left.property ⊤)).hom = (⊤ : T.specScheme.Opens).ι := rfl
  have key := Over.w (F.map T.idChartIsoTop.hom)
  rw [hW, hTop] at key
  change ((F.map T.idChartIsoTop.hom).left.appTop)
    ((Scheme.Opens.topIso (⊤ : T.specScheme.Opens)).inv
    ((Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom r)) = _
  have ht : (Scheme.Opens.topIso (⊤ : T.specScheme.Opens)).inv =
      (⊤ : T.specScheme.Opens).ι.appTop := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop]
    exact congrArg (fun k => T.specScheme.presheaf.map k) (Subsingleton.elim _ _)
  have hmor := (Scheme.Hom.comp_appTop (F.map T.idChartIsoTop.hom).left
    (⊤ : T.specScheme.Opens).ι).symm.trans
      ((congrArg Scheme.Hom.appTop key).trans Scheme.Hom.id_appTop)
  rw [ht]
  exact ConcreteCategory.congr_hom hmor _

/-- The global functions of `X` over `Spec ℤ`, in the spelling of the sections of its structure
ring sheaf. -/
def spaceGlobalRingEquiv :
    Space.globalFunctions T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers.1 ≃+*
      T.spaceGlobalRing :=
  RingEquiv.refl _

/-- The chart diagram of an étale chart of `X` over the identity chart of `Spec A`. -/
def chartDiagramIdChart (W : SmallEtale T.site (⊤_ Scheme.{u}) T.containsTerminal
    T.spaceOverIntegers.1) :
    ChartDiagram T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers.1 T.specSpace.1
      T.toSpecA.hom where
  U := W
  V := T.idChart
  g := yoneda.preimage (W.1.hom ≫ T.toSpecA.hom)
  comm := by
    rw [Functor.map_preimage]
    rfl

/-- **`p^♯` on global sections is the model identification.**  The ring map
`Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` of Stacks 0732 along `p`, after `R ⟶ Γ(Spec A, 𝒪)`, is the
identification of `R` with the global functions of `X` from which `p` is built. -/
theorem globalSectionsRingHomSite_modelToSpecGlobal (r : T.modelOverIntegers.ring) :
    globalSectionsRingHomSite T.site (⊤_ Scheme.{u}) T.containsTerminal T.toSpecA
        (T.modelToSpecGlobal r) = T.spaceGlobalRingEquiv (T.modelOverIntegers.equiv r) := by
  apply Subtype.ext
  funext W
  have h1 := globalSectionsChartEval_globalSectionsRingHomSite T.site (⊤_ Scheme.{u})
    T.containsTerminal T.toSpecA (T.chartDiagramIdChart W.unop) (T.modelToSpecGlobal r)
  have h2 : globalSectionsChartEval T.site (⊤_ Scheme.{u}) T.containsTerminal T.specSpace T.idChart
      (T.modelToSpecGlobal r) = (Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom r :=
    (T.modelToSpecGlobal_eval r).trans (T.tildeRingHom_apply r)
  have h3 := toSpecGlobalFunctions_chart T.site (⊤_ Scheme.{u}) T.containsTerminal
    T.spaceOverIntegers T.modelOverIntegers terminalIsTerminal W.unop
    ((Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom r)
  have h4 : specGlobalFunctionsGamma T.site (⊤_ Scheme.{u}) T.containsTerminal
      T.spaceOverIntegers T.modelOverIntegers terminalIsTerminal
      ((Scheme.ΓSpecIso T.modelOverIntegers.ring).inv.hom r) = T.modelOverIntegers.equiv r :=
    congrArg T.modelOverIntegers.equiv
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso T.modelOverIntegers.ring) r)
  exact h1.trans ((congrArg (fun x => (Scheme.Γ.map ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u})
    T.containsTerminal).map (T.chartDiagramIdChart W.unop).g).op).hom x) h2).trans
      (h3.symm.trans (congrArg (fun a => a.1 (op W.unop)) h4)))

/-- `A = Γ(X, 𝒪_X)` is the ring of global functions of `X` viewed over `Spec ℤ`. -/
def globalFunctionsOverIntegersEquiv : T.globalFunctions ≃+* T.spaceGlobalRing :=
  (T.globalFunctionsRingEquiv.trans (globalFunctionsRelocalizeEquiv T.site T.base (⊤_ Scheme.{u})
    T.containsBase T.containsTerminal ⟨terminal.from T.base⟩ T.space.1).symm).trans
    T.spaceGlobalRingEquiv

/-- The two identifications of `R` and of `A` with the global functions of `X` over `Spec ℤ`
agree. -/
theorem globalFunctionsOverIntegersEquiv_modelRingEquiv (r : T.modelOverIntegers.ring) :
    T.globalFunctionsOverIntegersEquiv (T.modelRingEquiv r) =
      T.spaceGlobalRingEquiv (T.modelOverIntegers.equiv r) := by
  simp [globalFunctionsOverIntegersEquiv, modelRingEquiv]


/-- `globalSectionsTensorAddEquiv` is semilinear along `A ≅ Γ(X, 𝒪_X)`. -/
theorem globalSectionsTensorAddEquiv_modelRingEquiv_symm_smul (c : T.globalFunctions)
    (m : T.restrictModel M) :
    T.globalSectionsTensorAddEquiv M (T.modelRingEquiv.symm c • m) =
      T.globalFunctionsOverIntegersEquiv c • T.globalSectionsTensorAddEquiv M m := by
  have hr : T.modelRingEquiv (T.modelRingEquiv.symm c) = c :=
    T.modelRingEquiv.apply_symm_apply c
  have h := T.globalSectionsTensorAddEquiv_smul M (T.modelRingEquiv.symm c) m
  rw [T.globalSectionsRingHomSite_modelToSpecGlobal,
    ← T.globalFunctionsOverIntegersEquiv_modelRingEquiv] at h
  exact h.trans (congrArg (fun a => T.globalFunctionsOverIntegersEquiv a •
    (T.globalSectionsTensorAddEquiv M) m) hr)

/-- The action of `A` on `M` is that of `R` through `R ≅ A`. -/
theorem smul_eq_modelRingEquiv_symm_smul (c : T.globalFunctions) (m : M) :
    (c • m : M) =
      (T.modelRingEquiv.symm c • (show T.restrictModel M from m) : T.restrictModel M) := by
  have hr : T.modelRingHom (T.modelRingEquiv.symm c) = c := T.modelRingEquiv.apply_symm_apply c
  exact (congrArg (fun a => (a • m : M)) hr.symm).trans
    (ModuleCat.restrictScalars.smul_def' T.modelRingHom (T.modelRingEquiv.symm c) m).symm

/-- **Stacks 07UZ, second assertion: `Γ(X, M ⊗_A 𝒪_X) = M`.**  In Situation 07UY, for every
`A`-module `M`, the global sections of `M ⊗_A 𝒪_X = p^*M~` are `M`, as `A`-modules, the global
sections being a module over `A = Γ(X, 𝒪_X)`.

It is `M = Γ(Spec A, M~) = Γ(Spec A, p_*p^*M~) = Γ(X, p^*M~)`, the middle step being the first
assertion `…CohomologyVanishingSituation.isIso_unit_tensorSheaf` and the last Stacks 0732. -/
@[stacks 07UZ "second assertion: Γ(X, M ⊗_A 𝒪_X) = M, as A-modules"]
def globalSectionsTensorLinearEquiv :
    M ≃ₗ[T.globalFunctions]
      (ModuleCat.restrictScalars T.globalFunctionsOverIntegersEquiv.toRingHom).obj
        (T.spaceSections M) :=
  { T.globalSectionsTensorAddEquiv M with
    map_smul' := fun c m =>
      (congrArg (T.globalSectionsTensorAddEquiv M) (T.smul_eq_modelRingEquiv_symm_smul M c m)).trans
        (T.globalSectionsTensorAddEquiv_modelRingEquiv_symm_smul M c m) }

end AlgebraicGeometry.Space.CohomologyVanishingSituation

end
