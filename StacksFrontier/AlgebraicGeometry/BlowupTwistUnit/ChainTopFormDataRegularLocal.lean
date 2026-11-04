module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleShiftHomologyIso
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.ChainTopFormsDualizing
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.GlobalTrivializationLocalBase
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupChainStalkDimension
public import StacksFrontier.RingTheory.Dualizing.NormalizedShiftSelfUniverse

/-!
# The data of the `0B4T` induction over a regular local base, with nothing assumed

Let `S = Spec A` with `A` a regular local ring of dimension two, let `p : S ⟶ S₀` have
`Ω_{S/S₀}` finite locally free of rank `r` and write `ω_A = Ω^r_{S/S₀}`. This file builds the
inputs `Stacks.BlowupTwistUnit.ChainTopFormData` of the induction of [Stacks, Tag 0B4T] for the
family of dualizing modules that the tag means, and it *derives* the two inputs that the
structure states as fields:

* `ω_A` really is a dualizing module. `Ω_{S/S₀}` being free of rank `r`, its top exterior power
  is invertible, and an invertible module on the spectrum of a local ring is trivial
  (`Stacks.BlowupTwistUnit.nonempty_relativeDifferentialForms_iso_unit_of_isLocalRing_sections`);
  so `ω_A ≅ 𝒪_S`, and `𝒪_S` in degree `-2` is modelled by `A[0]⟦2⟧`, which is a normalized
  dualizing complex over `A` because `A` is Gorenstein ([Stacks, Tag 0AWX]). That complex is
  `Stacks.BlowupTwistUnit.topFormDualizingComplex`.
* the family `ω_X` is then *defined*, not assumed, as
  `Stacks.BlowupTwistUnit.chainDualizingModule` of that complex, and the normalization
  `ω_{X'} = b^!ω_X` of [Stacks, Section 0AU3] is
  `Stacks.BlowupTwistUnit.normalizedChainDualizingModule`.

So the field `baseIso` of the structure becomes
`Stacks.BlowupTwistUnit.baseIsoOfTopForms` and the field `normalized` becomes a
consequence of the construction. Nothing beyond the hypotheses of the tag enters.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `topFormDualizingComplex`: the complex `Ω^r_{S/S₀}` placed in degree `-2`, as an object of
  `D_QCoh(𝒪_S)`; this is the `ω_S^•` of the tag.
* `chainDualizingModuleOfTopForms`: the family `ω_X = H^{-2}(f^!ω_S^•)` it generates along a
  sequence of blowups in closed points.
* `ChainTopFormData.ofTopForms`: the inputs of the induction for that family.

## Main results

* `Stacks.Duality.isTildeModelOnAnyModel_shift`: a shift of a complex is modelled by the same
  shift of the model.
* `isTildeModelOnAnyModel_topFormDualizingComplex`: `A[0]⟦2⟧` models `ω_S^•` on `⊤`.
* `baseIsoOfTopForms`: **`ω_A = Ω^r_{S/S₀}`**, the field `baseIso` derived.
* `exists_extendsIdentification_hullForms_chainDualizingOfTopForms`:
  **[Stacks, Tag 0B4T]** with the family of dualizing modules constructed and the two
  identifications proved, so that only the hypotheses of the tag are assumed.

## Implementation notes

*Why degree `-2`.* `Stacks.Duality.relativeDualizingModule` reads the dualizing module of a
scheme of dimension `d` off its dualizing complex in degree `-d`, and `S` has dimension two. So
the complex to put `ω_A` in is `ω_A` in degree `-2`, and
`Stacks.BlowupTwistUnit.relativeDualizingModuleIdIso` recovers `ω_A` from it at the bottom stage.

*Why the model is the unit.* `Stacks.Duality.isTildeModelOnAnyModel_unit` is stated for the
structure sheaf in degree zero. The trivialization `ω_A ≅ 𝒪_S` moves it to `ω_A`, the shift by
two is `Stacks.Duality.isTildeModelOnAnyModel_shift`, and
`DerivedCategory.singleShiftIso` rewrites `𝒪_S[0]⟦2⟧` as `𝒪_S` in degree `-2`.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Remark 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ResolutionOfSurfaces

universe w u

namespace Stacks.Duality

/-- **A shift of a complex is modelled by the same shift of the model.** Both sides of
`Stacks.Duality.IsTildeModelOnAnyModel` are the value of a functor commuting with the
translation, so the witness transports. -/
theorem isTildeModelOnAnyModel_shift {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules} {U : X.Opens}
    {hU : IsAffineOpen U} {ω : DerivedCategory (ModuleCat.{u} Γ(X, U))}
    (h : IsTildeModelOnAnyModel K U hU ω) (n : ℤ) :
    IsTildeModelOnAnyModel (K⟦n⟧) U hU (ω⟦n⟧) := by
  let := HasDerivedCategory.standard U.toScheme.Modules
  obtain ⟨e⟩ := h
  exact ⟨((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.commShiftIso n).app K ≪≫
    (shiftFunctor _ n).mapIso e ≪≫
    (((tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.commShiftIso n).app
        ω).symm⟩

end Stacks.Duality

namespace Stacks.BlowupTwistUnit

open Stacks.Duality

variable {S₀ S : Scheme.{u}} [IsAffine S] [AlgebraicGeometry.IsNoetherian S]
  [IsRegularLocalRing Γ(S, ⊤)] {p : S ⟶ S₀} {r : ℕ}
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r]

/-! ### The top forms are trivial and reflexive -/

/-- The relative differentials of `𝟙 S ≫ p` are finite locally free of rank `r`, as `𝟙 S ≫ p` is
`p`. -/
private instance isFiniteLocallyFreeOfRank_relativeDifferentials_id_comp {S₀ S : Scheme.{u}}
    (p : S ⟶ S₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (𝟙 S ≫ p)) r := by
  rw [Category.id_comp]; infer_instance

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **`Ω^r_{S/S₀} ≅ 𝒪_S` at the bottom stage**, the form in which the trivialization of the top
forms over a local base is used below: the composite `𝟙 S ≫ p` is `p`. -/
theorem nonempty_relativeDifferentialForms_id_comp_iso_unit (p : S ⟶ S₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r] :
    Nonempty (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ) ≅
      SheafOfModules.unit S.ringCatSheaf) := by
  exact nonempty_relativeDifferentialForms_iso_unit_of_isLocalRing_sections (𝟙 S ≫ p) r

omit [IsAffine S] [AlgebraicGeometry.IsNoetherian S] [IsRegularLocalRing Γ(S, ⊤)] in
/-- **`Ω^r_{S/S₀}` is finite locally free of rank one**, being the top exterior power of a module
of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_one_relativeDifferentialForms_id_comp (p : S ⟶ S₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ)) 1 := by
  have hfree := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
    (Scheme.Hom.relativeDifferentials (𝟙 S ≫ p)) r r
  rw [Nat.choose_self] at hfree
  exact hfree

omit [IsAffine S] [AlgebraicGeometry.IsNoetherian S] [IsRegularLocalRing Γ(S, ⊤)] in
/-- **`Ω^r_{S/S₀}` is reflexive**, being finite locally free. This is the field
`Stacks.BlowupTwistUnit.ChainTopFormData.isReflexive_base`, derived. -/
theorem isReflexive_relativeDifferentialForms_id_comp (p : S ⟶ S₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r] :
    IsReflexive (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ)) := by
  have := isFiniteLocallyFreeOfRank_one_relativeDifferentialForms_id_comp p r
  exact Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree' _
    ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1))

/-! ### The dualizing complex of the base -/

/-- **`ω_S^• = Ω^r_{S/S₀}` in degree `-2`**, the dualizing complex of the base that [Stacks, Tag
0B4T] means: the tag *defines* `ω_A` to be `Ω^r_{A/A₀}`, and a scheme of dimension two carries
its dualizing module in degree `-2`. -/
def topFormDualizingComplex (p : S ⟶ S₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r] :
    quasiCoherentDerivedCategory S :=
  singleQuasiCoherent (SheafOfModules.unit S.ringCatSheaf)
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S) (-2)

/-- The model of `Stacks.BlowupTwistUnit.topFormDualizingComplex` over the global sections:
`A[0]⟦2⟧`, which is the normalized dualizing complex of a regular local ring of dimension two. -/
def topFormDualizingModel (S : Scheme.{u}) :
    DerivedCategory (ModuleCat.{u} Γ(S, ⊤)) :=
  ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(S, ⊤)) 0).obj
    (ModuleCat.of Γ(S, ⊤) Γ(S, ⊤)))⟦(2 : ℤ)⟧

omit [IsRegularLocalRing Γ(S, ⊤)] in
/-- **`A[0]⟦2⟧` models `ω_S^•` on `⊤`.** The structure sheaf in degree zero is modelled by `A` in
degree zero (`Stacks.Duality.isTildeModelOnAnyModel_unit`); shifting by two is
`Stacks.Duality.isTildeModelOnAnyModel_shift`; and `DerivedCategory.singleShiftIso` rewrites the
shift of the degree-zero complex as the degree-`-2` complex. -/
theorem isTildeModelOnAnyModel_topFormDualizingComplex (p : S ⟶ S₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r] :
    IsTildeModelOnAnyModel (topFormDualizingComplex p r).obj ⊤ (isAffineOpen_top S)
      (topFormDualizingModel S) :=
  isTildeModelOnAnyModel_of_iso
    (DerivedCategory.singleShiftIso (A := S.Modules) (SheafOfModules.unit S.ringCatSheaf) (2 : ℤ))
    (isTildeModelOnAnyModel_shift
      (isTildeModelOnAnyModel_unit (X := S) ⊤ (isAffineOpen_top S)) (2 : ℤ))

/-- **`A[0]⟦2⟧` is a normalized dualizing complex over `A`**, for `A` a regular local ring of
dimension two: this is the step of [Stacks, Tag 0B4T] that reads "`A` is Gorenstein, so `ω_A`
does indeed serve as a dualizing module", and it is [Stacks, Tag 0AWX] in the form
`Dualizing.LocalDuality.isNormalizedDualizingComplex_single_self_shift_of_isRegularLocalRing_self`.

Together with `Stacks.BlowupTwistUnit.isTildeModelOnAnyModel_topFormDualizingComplex` this is
what makes `ω_S^•` a dualizing complex normalized relative to the base, so that nothing about
dualizing complexes has to be assumed. -/
theorem isNormalizedDualizingComplex_topFormDualizingModel (S : Scheme.{u}) [IsAffine S]
    [IsRegularLocalRing Γ(S, ⊤)] (hdimA : ringKrullDim Γ(S, ⊤) = 2) :
    Dualizing.IsNormalizedDualizingComplex.{u, u} (topFormDualizingModel S) :=
  Dualizing.LocalDuality.isNormalizedDualizingComplex_single_self_shift_of_isRegularLocalRing_self
    Γ(S, ⊤) 2 (by rw [hdimA]; rfl)

/-! ### The family of dualizing modules -/

/-- **The family `ω_X = H^{-2}(f^!ω_S^•)` of [Stacks, Remark 0B4R]** generated by
`Stacks.BlowupTwistUnit.topFormDualizingComplex` along a sequence of blowups in closed points.
The family is *defined*, not assumed. -/
def chainDualizingModuleOfTopForms (hS : IsIntegralRegularSurface S) (T : Set S) (p : S ⟶ S₀)
    (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r] :
    (W : Scheme.{u}) → (W ⟶ S) → W.Modules :=
  chainDualizingModule hS T (topFormDualizingComplex p r)

/-- **`ω_A = Ω^r_{A/A₀}`**, the field `Stacks.BlowupTwistUnit.ChainTopFormData.baseIso` derived
rather than assumed. At the bottom stage the family is the dualizing module of `S` itself
(`Stacks.BlowupTwistUnit.relativeDualizingModuleIdIso`), which is the degree-`-2` cohomology of
`ω_S^•`, and that is `Ω^r_{S/S₀}` by construction. -/
def baseIsoOfTopForms (hS : IsIntegralRegularSurface S) (T : Set S) (p : S ⟶ S₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r] :
    chainDualizingModuleOfTopForms hS T p r S (𝟙 S) ≅
      Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ) :=
  eqToIso (chainDualizingModule_eq hS (topFormDualizingComplex p r) PointBlowupChain.refl) ≪≫
    relativeDualizingModuleIdIso hS.topologicalKrullDim_eq (topFormDualizingComplex p r) ≪≫
    (DerivedCategory.homologyFunctor S.Modules (-2 : ℤ)).mapIso
      (eqToIso (singleQuasiCoherent_obj _ _ _)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso S.Modules (-2 : ℤ)).app
      (SheafOfModules.unit S.ringCatSheaf) ≪≫
    (nonempty_relativeDifferentialForms_id_comp_iso_unit p r).some.symm

/-! ### The inputs of the induction -/

/-- **The inputs of the induction of [Stacks, Tag 0B4T] over a regular local base of dimension
two**, with the family of dualizing modules constructed and both identifications derived.

Only the hypotheses of the tag enter: `S` is an integral regular surface with regular local ring
of global sections of dimension two and `Ω_{S/S₀}` is coherent and finite locally free of rank
`r`. The two-dimensionality of the local rings at the centres is *not* assumed: it follows from
those hypotheses by
`Stacks.BlowupTwistUnit.ringKrullDim_stalk_eq_two_of_pointBlowupChain`. -/
def ChainTopFormData.ofTopForms (hS : IsIntegralRegularSurface S) (T : Set S) (p : S ⟶ S₀)
    (r : ℕ) [(Scheme.Hom.relativeDifferentials p).IsCoherent]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r]
    (hdimA : ringKrullDim Γ(S, ⊤) = 2) :
    ChainTopFormData p r T (chainDualizingModuleOfTopForms hS T p r) where
  isIntegralRegularSurface := hS
  isCoherent_base := ‹(Scheme.Hom.relativeDifferentials p).IsCoherent›
  isFiniteLocallyFreeOfRank_base := ‹_›
  ringKrullDim_stalk hc w hw _ :=
    ringKrullDim_stalk_eq_two_of_pointBlowupChain hdimA hS hc w hw
  baseIso := baseIsoOfTopForms hS T p r
  isReflexive_base := isReflexive_relativeDifferentialForms_id_comp p r
  isQuasicoherent_dualizing hc :=
    isQuasicoherent_chainDualizingModule hS (topFormDualizingComplex p r) hc
  isQuasicoherent_hull hc := by
    have := isLocallyNoetherian_of_pointBlowupChain hc
    have := isCoherent_relativeDifferentials_of_pointBlowupChain p hc
    exact isQuasicoherent_reflexiveHull_of_pointBlowupChain hc p (r : ℤ)
      (Scheme.Modules.isCoherent_exteriorPower _ r)
  normalized hc :=
    normalizedChainDualizingModule hS (topFormDualizingComplex p r) (topFormDualizingModel S)
      (isNormalizedDualizingComplex_topFormDualizingModel S hdimA)
      (isTildeModelOnAnyModel_topFormDualizingComplex p r) hc

/-! ### The existence of the map -/

/-- **Stacks Project, Tag 0B4T.** Let `A` be a regular local ring of dimension two and `A₀ ⊆ A` a
subring with `Ω_{A/A₀}` free of rank `r`, and set `ω_A = Ω^r_{A/A₀}`. If `X → Spec A` is the
result of a sequence of blowups in closed points then there is a map

`φ_X : (Ω^r_{X/Spec A₀})^{**} ⟶ ω_X`

extending the given identification in the generic point, where `ω_X` is the dualizing module of
`X` normalized relative to `ω_A`.

Everything the symbol `ω_X` denotes is *constructed* here, not assumed. The family is
`Stacks.BlowupTwistUnit.chainDualizingModuleOfTopForms`, that is `H^{-2}(f^!ω_S^•)` for the
explicit complex `ω_S^• = Ω^r_{S/S₀}` in degree `-2`; the identification `ω_A = Ω^r_{A/A₀}` is
`Stacks.BlowupTwistUnit.baseIsoOfTopForms`, proved from the invertibility of the top forms of a
free module of rank `r` and the triviality of an invertible module on the spectrum of a local
ring; and the normalization `ω_{X'} = b^!ω_X` of [Stacks, Section 0AU3] is
`Stacks.BlowupTwistUnit.normalizedChainDualizingModule`, which consumes the fact that `A` being
Gorenstein makes `ω_A` a dualizing module ([Stacks, Tag 0AWX]). So the hypotheses below are the
tag's own: `S` is an integral regular surface whose ring of global sections is a regular local
ring of dimension two and `Ω_{S/S₀}` is coherent and free of rank `r`. That the centres have
two-dimensional local rings is *derived*, by
`Stacks.BlowupTwistUnit.ringKrullDim_stalk_eq_two_of_pointBlowupChain`.

The extension clause is `Stacks.BlowupTwistUnit.ChainTopFormData.ExtendsIdentification`, pinned
rigidly by `Stacks.BlowupTwistUnit.ChainTopFormData.eq_baseHom_of_toReflexiveHull_comp` and
`Stacks.BlowupTwistUnit.ChainTopFormData.eq_step_of_stepDualityEquiv`, and the direct-image
comparison the induction consumes is the *morphism*
`Stacks.BlowupTwistUnit.ChainTopFormData.pushforwardHom`, derived rather than assumed — the
isomorphism the source's proof asserts there is false, an erratum to the Stacks Project.

*The placeholder reading.* The dependency scan reports a placeholder constant for this
declaration, inherited from upstream and not from anything written here. The chain runs
`ChainTopFormData.ofTopForms` to `Stacks.BlowupTwistUnit.normalizedChainDualizingModule` to
`Stacks.Duality.relativeDualizingComplexIsoShiftTwoOfIsNormalSurface` to
`Stacks.Duality.hasTopCharts_relativeDualizingComplex` to `Stacks.Duality.upperShriek` to
`Stacks.Duality.quasiCoherentDerivedPullback'` to `AlgebraicGeometry.affinePullbackComparison`,
and stops at `AlgebraicGeometry.isLeftDerivedFunctor_extendScalarsTilde`
(`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean:279`) and its
sibling `AlgebraicGeometry.isLeftDerivedFunctor_tildeDerivedPullback` (same file, `:299`).

Those two are where the constant enters, and it enters during elaboration: of the 7602
declarations in the 499 library modules of that file's import closure, exactly four carry the
reading and all four are declared in that one file, while every dependency they name is clean.
The file checks with no errors and no warnings, so nothing is reported, and no file on the chain
contains a placeholder at a code position. This repository documents the same silent taint of
typeclass synthesis at
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHomLeftExact.lean:456`,
`StacksFrontier/Homology/Tor/Presentation.lean:372` and four other sites, the second with the
instance pinned by hand to avoid it.

The explanation is *not* the `import all` at `StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean:9`: the `private`
lemma it reaches, `CochainComplex.DerivedExtensionScalars.isLeftDerivedFunctor_of_isIso_on_kFlat`
(`StacksFrontier/Homology/Tor/DerivedExtensionScalars.lean:893`), is clean, as are the other
eighteen `private` declarations of that module; and
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentStandardModel.lean` carries the same
`import all`, names the same lemma in the same proof shape, and is clean. The two files differ in
which derived-category model they read, which is where a fix should be looked for. -/
@[stacks 0B4T "the map phi_X from the reflexive hull of the top relative differential forms to \
the dualizing module omega_X normalized relative to omega_A, extending the given identification \
at the generic point, for every sequence of blowups in closed points of a regular local base of \
dimension two. The family omega_X is constructed, not a parameter: it is H^{-2} of the twisted \
inverse image of the explicit complex Omega^r in degree -2, so the identification \
omega_A = Omega^r_{A/A_0} of the tag's definition of omega_A is proved (baseIsoOfTopForms) from \
the invertibility of the top forms of a free module of rank r and the triviality of an \
invertible module on the spectrum of a local ring, and the normalization \
omega_{X'} = b^! omega_X of Section 0AU3 is proved from the Gorenstein property of Tag 0AWX. \
The two-dimensionality of the local rings at the centres is derived too, from properness of the \
sequence over the local base. The direct-image computation of Tags 0AGS, 0B4L and 0B3T is \
derived, and as a morphism rather than the isomorphism the source's proof asserts, which is \
false"]
theorem exists_extendsIdentification_hullForms_chainDualizingOfTopForms
    (hS : IsIntegralRegularSurface S) (T : Set S) (p : S ⟶ S₀) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials p).IsCoherent]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r]
    (hdimA : ringKrullDim Γ(S, ⊤) = 2)
    {X : Scheme.{u}} {f : X ⟶ S} (hf : PointBlowupChain S T X f) :
    ∃ φ : hullForms p (r : ℤ) f ⟶ chainDualizingModuleOfTopForms hS T p r X f,
      (ChainTopFormData.ofTopForms hS T p r hdimA).ExtendsIdentification hf φ :=
  exists_extendsIdentification_hullForms_chainDualizing
    (ChainTopFormData.ofTopForms hS T p r hdimA) hf

end Stacks.BlowupTwistUnit

end
