module

public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Locality
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OneDimensionalFibres
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# Eilenberg-Watts in degree zero for the structure sheaf

Let `p : X ⟶ Spec R` be flat, with `X` quasi-compact and quasi-separated, and consider the
endofunctor

> `Φ(M) = H⁰(X, 𝒪_X ⊗_{𝒪_X} p^* M~)`

of `R`-modules. This file proves that `Φ` is tensoring with `Γ(X, 𝒪_X)` and that `Γ(X, 𝒪_X)` is a
flat `R`-module, taking as its vanishing input only

> `H¹(X, 𝒢) = 0` for every **globally generated** quasi-coherent `𝒢`,

which is clause (4) of [Stacks, Tag 0E7H]. This is the affine computation in the proof of
[Stacks, Tag 0E7K] — flatness of `f_* 𝒪_X` over the base, and the commutation of its formation
with base change, for a proper morphism with one-dimensional fibres and vanishing `R¹ f_* 𝒪_X`.

## Why the directory's Eilenberg-Watts package had to be reworked

`EilenbergWattsPhi.lean`, `EilenbergWattsGeometricFactor.lean` and `EilenbergWattsSituation.lean`
run Eilenberg-Watts on the same functor in degree `d`, but they take the vanishing input as
`H^{d+1}(X, 𝒢) = 0` for **every** quasi-coherent `𝒢`, because that is what conclusion (a) of
[Stacks, Tag 0EX3] supplies in the top degree. At `d = 0` that hypothesis is false for a proper
morphism with one-dimensional fibres over an affine base: `H¹(P¹_A, 𝒪(-2)) ≠ 0`. Only the
globally generated form is available, and it is the hypothesis used here.

The weaker hypothesis suffices because of two facts about the particular functor.

* The geometric factor is `M ↦ 𝒪_X ⊗ p^* M~`, and the left unitor of the sheafified tensor
  product makes that `M ↦ p^* M~`, so **every value of the geometric factor is globally
  generated**: `M~` is globally generated on the affine `Spec R`, and pullback preserves global
  generation. The vanishing is therefore only ever asked for at a globally generated module.
* The geometric factor is **exact**, not merely right exact, because `p` is flat. The vanishing
  is consumed at the left-hand term of a short exact sequence, and exactness of the geometric
  factor is what puts a value of the geometric factor there.

Right exactness of `H^d(X, -)` in the existing package is proved by composing right exactness of
the geometric factor with right exactness of the cohomological factor. The second of those two
is where the strong hypothesis enters, and it cannot be weakened on its own: the restriction of
`H¹(X, -)` to the quasi-coherent modules is *not* right exact. So the composition is what has to
go, and `preservesFiniteColimits_affineTopDegreeFunctor_of_isZero_image` replaces it by a single
application of `CategoryTheory.Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi` to
the composite, where the vanishing is asked for only at the modules the geometric factor
produces.

## Main definitions

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `structureSheafQcoh`: `𝒪_X` as an object of the quasi-coherent subcategory.
* `structureSheafFactor`: the geometric factor `M ↦ 𝒪_X ⊗ p^* M~` at `𝒪_X`.
* `structureSheafZeroFunctor`: `Φ(M) = H⁰(X, 𝒪_X ⊗ p^* M~)`.

## Main results

* `preservesFiniteColimits_affineTopDegreeFunctor_of_isZero_image`: **right exactness of `Φ` from
  vanishing on the image of the geometric factor alone.** This is the reworked hypothesis shape.
* `preservesFiniteLimits_structureSheafFactor`: the geometric factor at `𝒪_X` is exact when `p` is
  flat.
* `generatingSectionsStructureSheafFactor`: every value of that factor is globally generated.
* `structureSheafZeroTensorGlobalSectionsIso`: **the tensor identity of the affine computation of
  [Stacks, Tag 0E7K] (b)**, `Γ(X, 𝒪_X) ⊗_R M ≅ H⁰(X, 𝒪_X ⊗ p^* M~)`, naturally in `M`.
* `flat_globalSections_of_generatingSectionsVanishing` and `flat_globalSections_of_isProper`:
  **the affine computation of [Stacks, Tag 0E7K] (a)**, `Γ(X, 𝒪_X)` is a flat `R`-module, the
  second with the vanishing discharged from [Stacks, Tag 0E7H] clause (4).
* `globalSectionsTensorIso_of_isProper`: the same for the tensor identity of (b).
* `flat_globalSections_of_isZero_firstDirectImage`: (a) from the tag's own hypotheses, with
  `H¹(X, 𝒪_X) = 0` read off `R¹ f_* 𝒪_X = 0` over the affine base.
* `isZero_firstCohomology_preimage_of_isZero_firstDirectImage`: the same vanishing over an affine
  open of the base, which is the form the reduction to an affine base needs.

## The one carried hypothesis, and why it is not a conclusion of Tag 0E7K

`CohomologyVanishesAboveOne` is the residue of [Stacks, Tag 0E7D] at fibre dimension one that
`OneDimensionalFibres.lean` already carries: every proper morphism onto an affine base whose
fibres have dimension at most one has vanishing cohomology of quasi-coherent modules in **every
degree above one**. It is the hypothesis `h02V7` of clauses (2) and (4) of [Stacks, Tag 0E7H],
quantified the same way, and it says nothing in degree zero or one — where both conclusions of
[Stacks, Tag 0E7K] live. Neither conclusion of [Stacks, Tag 0E7K] is a case of it, and it
mentions neither flatness nor base change.

## What is not proved here

The two conclusions of [Stacks, Tag 0E7K] are statements over an arbitrary base `S`, and what is
proved here is the source's own reduction to `Y` and `S` affine. Two steps separate them, and
neither is carried out here.

For (a): `AlgebraicGeometry.isFlatOver_tfae` reduces `S`-flatness of `f_* 𝒪_X` to flatness of
`Γ(f_* 𝒪_X, U) = Γ(X, f⁻¹U)` over `Γ(S, V)` for compatible affine opens `U ⊆ Y`, `V ⊆ S`. The
module below is `Γ((f⁻¹U).toScheme, ⊤)` over `Γ(S, V)` through the structure morphism
`(f⁻¹U).toScheme ⟶ V.toScheme ≅ Spec Γ(S, V)`; identifying the two needs
`AlgebraicGeometry.Scheme.Opens.topIso` together with the agreement of
`Stacks.Cohomology.AffineBase.baseSectionsAlgebra` with
`AlgebraicGeometry.Scheme.Hom.appLE` of the composite `X ⟶ Y ⟶ S`.

For (b), two further steps. The source's displayed chain is
`H⁰(X ×_S S', 𝒪) = H⁰(X, 𝒪_X ⊗_A A') = H⁰(X, 𝒪_X) ⊗_A A'`, and only the second equality is
below. The first is available: for `S' = Spec A'` the projection `X ×_S S' ⟶ X` is affine, so
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` ([Stacks, Tag 089W]) rewrites the
left-hand side as `H⁰(X, g'_* 𝒪_{X'})`, and
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`
([Stacks, Tag 02KG])
identifies `g'_* 𝒪_{X'}` with `p^* A'~`. And then the tag asserts that the canonical comparison
of *sheaves* is invertible, where everything below is a statement about modules. The comparison
of this directory is `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange`, for which
the only invertibility criterion in the library is `isIso_pushforwardBaseChange_of_isAffine` — flat base
change, which the base change of [Stacks, Tag 0E7K] is not. Passing from the affine computation
to the sheaf statement needs the comparison's locality on the base, which is available for the
*other* canonical comparison `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`,
together with the identification of the two maps, which is not available.

## References

* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

noncomputable section

variable (R : Type u) [CommRing R] (W : Over (Spec (CommRingCat.of R)))

/-! ### The geometric factor at the structure sheaf -/

/-- `𝒪_X`, as an object of the category of quasi-coherent modules. -/
abbrev structureSheafQcoh (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩

/-- **The geometric factor at the structure sheaf**, `M ↦ 𝒪_X ⊗ p^* M~`. -/
abbrev structureSheafFactor :
    ModuleCat.{u} R ⥤ (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory :=
  geometricFactor R W (structureSheafQcoh W.left)

/-- **The left unitor of the sheafified tensor product** at the spelling `tensorFactor` is
written in: `𝒪_X ⊗ - ≅ 𝟭`. -/
abbrev tensorFactorStructureSheafIso :
    tensorFactor R W (structureSheafQcoh W.left).obj ≅ 𝟭 W.left.Modules :=
  Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso W.left.presheaf (ringSheafCond W.left)

/-- The pullback half of the geometric factor is taken along the structure morphism, so it is flat
as soon as the structure morphism is. -/
theorem flat_toSpecBase_left [Flat W.hom] : Flat (toSpecBase R W).left := by
  rw [toSpecBase_left]
  infer_instance

/-- **`M ↦ 𝒪_X ⊗ p^* M~` is exact when `p` is flat.** The tilde functor is exact
(`AlgebraicGeometry.tilde.preservesFiniteLimits`), pullback along a flat morphism is
exact (`AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat`), and tensoring with
`𝒪_X` is the identity up to the unitor. -/
theorem preservesFiniteLimits_geometricFactorFormula_structureSheaf [Flat W.hom] :
    PreservesFiniteLimits (geometricFactorFormula R W (structureSheafQcoh W.left).obj) := by
  have h1 : PreservesFiniteLimits (tildeFactor R) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits (CommRingCat.of R)
  have h2 : PreservesFiniteLimits (pullbackFactor R W) :=
    have := flat_toSpecBase_left R W
    preservesFiniteLimits_modulesPullback_of_flat (toSpecBase R W).left
  have h3 : PreservesFiniteLimits (tensorFactor R W (structureSheafQcoh W.left).obj) :=
    preservesFiniteLimits_of_natIso (F := 𝟭 W.left.Modules)
      (tensorFactorStructureSheafIso R W).symm
  exact inferInstanceAs (PreservesFiniteLimits (tildeFactor R ⋙ pullbackFactor R W ⋙
    tensorFactor R W (structureSheafQcoh W.left).obj))

/-- **The geometric factor at the structure sheaf is exact when `p` is flat**, inside the
quasi-coherent subcategory. The inclusion reflects limits, and the composite with it is the
formula. -/
theorem preservesFiniteLimits_structureSheafFactor [Flat W.hom] :
    PreservesFiniteLimits (structureSheafFactor R W) := by
  have h := preservesFiniteLimits_geometricFactorFormula_structureSheaf R W
  refine ⟨fun J _ _ => ?_⟩
  have hJ : PreservesLimitsOfShape J
      (geometricFactorFormula R W (structureSheafQcoh W.left).obj) :=
    h.preservesFiniteLimits J
  have h2 : PreservesLimitsOfShape J (structureSheafFactor R W ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)) :=
    @preservesLimitsOfShape_of_natIso _ _ _ _ _ _ _ _
      (geometricFactorCompιIso R W (structureSheafQcoh W.left)).symm hJ
  exact preservesLimitsOfShape_of_reflects_of_preserves (structureSheafFactor R W)
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf))

/-- **`p^* M~` is generated by global sections.** The module `M~` is quasi-coherent on the affine
`Spec R`, hence globally generated (`AlgebraicGeometry.generatingSectionsOfIsAffine`), and
pullback preserves colimits and carries `𝒪` to `𝒪`, hence preserves global generation
(`AlgebraicGeometry.generatingSectionsMap`). -/
def generatingSectionsPullbackFactorTilde (M : ModuleCat.{u} R) :
    SheafOfModules.GeneratingSections ((pullbackFactor R W).obj ((tildeFactor R).obj M)) :=
  have hpres : PreservesColimitsOfSize.{u, u} (pullbackFactor R W) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (Scheme.Modules.pullback (toSpecBase R W).left))
  haveI : ((tildeFactor R).obj M).IsQuasicoherent :=
    inferInstanceAs (((AlgebraicGeometry.tilde.functor (CommRingCat.of R)).obj M).IsQuasicoherent)
  AlgebraicGeometry.generatingSectionsMap
    (AlgebraicGeometry.generatingSectionsOfIsAffine ((tildeFactor R).obj M))
    (pullbackFactor R W) hpres (pullbackFactorObjUnitIso R W).symm

/-- **Every value of the geometric factor at the structure sheaf is generated by global
sections**: `𝒪_X ⊗ p^* M~` is `p^* M~` up to the unitor. This is what makes the globally
generated form of the vanishing enough. -/
def generatingSectionsStructureSheafFactor (M : ModuleCat.{u} R) :
    SheafOfModules.GeneratingSections
      ((ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)).obj
        ((structureSheafFactor R W).obj M)) :=
  (generatingSectionsPullbackFactorTilde R W M).equivOfIso
    ((tensorFactorStructureSheafIso R W).app _).symm

/-! ### Right exactness from vanishing on the image of the geometric factor -/

/-- **Right exactness of `M ↦ H^d(X, T M)` from vanishing at the values of `T` alone**, for an
exact `T` into the quasi-coherent modules.

A short exact sequence of `R`-modules is carried by `T` to a short exact sequence of
quasi-coherent modules, hence of module sheaves, whose left-hand term is a value of `T`; one
degree of vanishing there is one degree of right exactness
(`exact_and_epi_map_rightDerived_of_isZero`). The hypothesis is therefore only ever read at a
value of `T`, which is the whole point: for `d = 0` the vanishing of `H¹` is unavailable in
general and available at the values of the geometric factor at `𝒪_X`. -/
theorem preservesFiniteColimits_comp_qcohCohomology_of_isZero_image (d : ℕ)
    (T : ModuleCat.{u} R ⥤
      (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (hvan : ∀ M : ModuleCat.{u} R,
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj
        ((ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)).obj
          (T.obj M)))) :
    PreservesFiniteColimits (T ⋙ qcohCohomology W.left d) := by
  rw [Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi]
  intro S hS
  exact exact_and_epi_map_rightDerived_of_isZero (moduleGlobalSections W.left)
    (shortExact_map_ι_isQuasicoherent W.left (ShortComplex.ShortExact.map_of_exact hS T)) d
    (hvan S.X₁)

/-- **The third hypothesis of `Stacks.EilenbergWatts.iso` for `Φ`, from vanishing at the values of
the geometric factor alone.** This replaces `preservesFiniteColimits_affineTopDegreeFunctor`,
whose vanishing hypothesis ranges over all quasi-coherent modules. -/
theorem preservesFiniteColimits_affineTopDegreeFunctor_of_isZero_image (d : ℕ)
    (T : ModuleCat.{u} R ⥤
      (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (hvan : ∀ M : ModuleCat.{u} R,
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus ((d : ℤ) + 1)).obj
        ((ObjectProperty.ι (SheafOfModules.isQuasicoherent W.left.ringCatSheaf)).obj
          (T.obj M)))) :
    PreservesFiniteColimits (affineTopDegreeFunctor R W d T) := by
  have h2 : PreservesFiniteColimits ((T ⋙ qcohCohomology W.left d) ⋙
      ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))) := by
    have := preservesFiniteColimits_comp_qcohCohomology_of_isZero_image R W d T hvan
    infer_instance
  exact preservesFiniteColimits_of_natIso
    (Functor.associator T (qcohCohomology W.left d)
      (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))))

/-! ### Left exactness in degree zero -/

/-- **Cohomology in degree zero is left exact on quasi-coherent modules.** Global sections are
left exact, so the degree-zero right derived functor is global sections
(`CategoryTheory.Functor.rightDerivedZeroIsoSelf`), and the inclusion of the quasi-coherent
modules is left exact because quasi-coherence is closed under kernels. -/
theorem preservesFiniteLimits_qcohCohomology_zero (X : Scheme.{u}) :
    PreservesFiniteLimits (qcohCohomology X 0) := by
  let iotaP : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ X.Modules :=
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)
  let H : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) := (moduleGlobalSections X).rightDerived 0
  have hι : PreservesFiniteLimits iotaP :=
    inferInstanceAs (PreservesFiniteLimits
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)))
  have hH : PreservesFiniteLimits H :=
    preservesFiniteLimits_of_natIso ((moduleGlobalSections X).rightDerivedZeroIsoSelf).symm
  exact inferInstanceAs (PreservesFiniteLimits (iotaP ⋙ H))

/-- **`Φ` is left exact in degree zero as soon as the geometric factor is.** Restriction of
scalars is exact, and degree-zero cohomology is left exact on quasi-coherent modules. -/
theorem preservesFiniteLimits_affineTopDegreeFunctor_zero
    (T : ModuleCat.{u} R ⥤
      (SheafOfModules.isQuasicoherent W.left.ringCatSheaf).FullSubcategory)
    [PreservesFiniteLimits T] :
    PreservesFiniteLimits (affineTopDegreeFunctor R W 0 T) := by
  have h : PreservesFiniteLimits (qcohCohomology W.left 0) :=
    preservesFiniteLimits_qcohCohomology_zero W.left
  have h2 : PreservesFiniteLimits ((T ⋙ qcohCohomology W.left 0) ⋙
      ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))) := by
    have h3 : PreservesFiniteLimits (T ⋙ qcohCohomology W.left 0) := inferInstance
    infer_instance
  exact preservesFiniteLimits_of_natIso
    (Functor.associator T (qcohCohomology W.left 0)
      (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))))

/-! ### The affine computation -/

/-- **`Φ(M) = H⁰(X, 𝒪_X ⊗ p^* M~)`**, the functor the affine computation in the proof of
[Stacks, Tag 0E7K] runs Eilenberg-Watts on. -/
abbrev structureSheafZeroFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  affineTopDegreeFunctor R W 0 (structureSheafFactor R W)

/-- **`Φ` is right exact**, from the vanishing of `H¹` on globally generated quasi-coherent
modules alone. -/
theorem preservesFiniteColimits_structureSheafZeroFunctor [Flat W.hom]
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus 1).obj G)) :
    PreservesFiniteColimits (structureSheafZeroFunctor R W) := by
  have := preservesFiniteLimits_structureSheafFactor R W
  refine preservesFiniteColimits_affineTopDegreeFunctor_of_isZero_image R W 0
    (structureSheafFactor R W) fun M => ?_
  rw [show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num]
  exact hvan _ ((structureSheafFactor R W).obj M).property
    (generatingSectionsStructureSheafFactor R W M)

/-- **Eilenberg-Watts for `Φ(M) = H⁰(X, 𝒪_X ⊗ p^* M~)`**: it is tensoring with the `R`-module
`Φ(R)`. The four hypotheses are additivity and `R`-linearity of the geometric factor and of the
cohomological tail, commutation with direct sums, and right exactness — the last from the
globally generated form of the vanishing. -/
def structureSheafZeroTensorIso [Flat W.hom]
    [CompactSpace (W.left : Type u)] [QuasiSeparatedSpace (W.left : Type u)]
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus 1).obj G)) :
    MonoidalCategory.tensorLeft ((structureSheafZeroFunctor R W).obj (ModuleCat.of R R)) ≅
      structureSheafZeroFunctor R W :=
  haveI := additive_affineTopDegreeFunctor R W 0 (structureSheafFactor R W)
  haveI := linear_affineTopDegreeFunctor R W 0 (structureSheafFactor R W)
    (linear_geometricFactor R W (structureSheafQcoh W.left))
  haveI := fun J : Type u =>
    preservesColimitsOfShape_discrete_affineTopDegreeFunctor R W 0 (structureSheafFactor R W)
      (preservesColimitsOfShape_discrete_geometricFactor R W (structureSheafQcoh W.left)) J
  haveI := preservesFiniteColimits_structureSheafZeroFunctor R W hvan
  Stacks.EilenbergWatts.iso (structureSheafZeroFunctor R W)

/-- **The Eilenberg-Watts module of `Φ` is `Γ(X, 𝒪_X)`.** It is `H⁰(X, 𝒪_X ⊗ p^* R~)`, which is
`H⁰(X, 𝒪_X)` by `affineTopDegreeFunctorObjSelfIso` and `Γ(X, 𝒪_X)` because global sections are
left exact. -/
def structureSheafZeroFunctorObjSelfIso :
    (structureSheafZeroFunctor R W).obj (ModuleCat.of R R) ≅
      (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
        (ModuleCat.of Γ(W.left, ⊤) Γ(W.left, ⊤)) :=
  affineTopDegreeFunctorObjSelfIso R W 0 (structureSheafQcoh W.left) ≪≫
    (ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).mapIso
      (((moduleGlobalSections W.left).rightDerivedZeroIsoSelf).app
        (SheafOfModules.unit W.left.ringCatSheaf))

/-- **The tensor identity of the affine computation of [Stacks, Tag 0E7K] (b).** For
`p : X ⟶ Spec R` flat with `X` quasi-compact and quasi-separated and `H¹(X, -)` vanishing on
globally generated quasi-coherent modules, the endofunctor `M ↦ H⁰(X, 𝒪_X ⊗ p^* M~)` of
`R`-modules **is** tensoring with `Γ(X, 𝒪_X)`.

This is the second equality `H⁰(X, 𝒪_X ⊗_A M) = M ⊗_A H⁰(X, 𝒪_X)` of the displayed chain in the
source's proof; the first, which rewrites `H⁰(X ×_S S', 𝒪)` as the left-hand side, is not here --
see the module documentation. -/
def structureSheafZeroTensorGlobalSectionsIso [Flat W.hom]
    [CompactSpace (W.left : Type u)] [QuasiSeparatedSpace (W.left : Type u)]
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus 1).obj G)) :
    MonoidalCategory.tensorLeft
        ((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
          (ModuleCat.of Γ(W.left, ⊤) Γ(W.left, ⊤))) ≅
      structureSheafZeroFunctor R W :=
  (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapIso
      (structureSheafZeroFunctorObjSelfIso R W).symm ≪≫
    structureSheafZeroTensorIso R W hvan

/-- **The affine computation of [Stacks, Tag 0E7K] (a).** For `p : X ⟶ Spec R` flat with `X`
quasi-compact and quasi-separated and `H¹(X, -)` vanishing on globally generated quasi-coherent
modules, `Γ(X, 𝒪_X)` is a flat `R`-module.

`Φ` is left exact — the geometric factor is exact because `p` is flat, and degree-zero cohomology
is left exact — and Eilenberg-Watts identifies it with tensoring by `Γ(X, 𝒪_X)`, so tensoring by
`Γ(X, 𝒪_X)` is left exact, which is flatness
(`Module.Flat.iff_preservesFiniteLimits_tensorLeft`). -/
theorem flat_globalSections_of_generatingSectionsVanishing [Flat W.hom]
    [CompactSpace (W.left : Type u)] [QuasiSeparatedSpace (W.left : Type u)]
    (hvan : ∀ G : W.left.Modules, G.IsQuasicoherent →
      SheafOfModules.GeneratingSections G →
      IsZero (((moduleGlobalSections W.left).rightDerivedPlus 1).obj G)) :
    Module.Flat R Γ(W.left, ⊤) := by
  have hlex : PreservesFiniteLimits (structureSheafZeroFunctor R W) :=
    have := preservesFiniteLimits_structureSheafFactor R W
    preservesFiniteLimits_affineTopDegreeFunctor_zero R W (structureSheafFactor R W)
  have hflat : Module.Flat R ((structureSheafZeroFunctor R W).obj (ModuleCat.of R R)) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft _).mpr
      (preservesFiniteLimits_of_natIso (structureSheafZeroTensorIso R W hvan).symm)
  exact Module.Flat.of_linearEquiv (structureSheafZeroFunctorObjSelfIso R W).symm.toLinearEquiv

/-! ### Discharging the vanishing for a proper morphism with one-dimensional fibres -/

/-- **`H¹(f⁻¹V, 𝒪) = 0` over an affine open of the base, from `R¹ f_* 𝒪_X = 0`.** This is the
hypothesis `R¹ f_* 𝒪_X = 0` of [Stacks, Tag 0E7K] in the shape clause (4) of
[Stacks, Tag 0E7H] consumes over an affine open `V ⊆ Y`: the vanishing restricts along `V` by
`isZero_firstDirectImage_structureSheaf_restrict`, and over the affine `V` a vanishing higher
direct image is vanishing cohomology ([Stacks, Tag 01XK]). -/
theorem isZero_firstCohomology_preimage_of_isZero_firstDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (V : Y.Opens) [IsAffine V.toScheme]
    (h : IsZero (firstDirectImageStructureSheaf f)) :
    IsZero (((moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerivedPlus 1).obj
      (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)) :=
  isZero_cohomology_of_isZero_rightDerivedPlus_pushforward (f ∣_ V) 1
    (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)
    (isZero_firstDirectImage_structureSheaf_restrict f V h)

/-- **The affine computation of [Stacks, Tag 0E7K] (a), with the vanishing discharged.** Let
`X` be flat over `Spec R`, let `f : X ⟶ Y` be proper onto an affine scheme with
`dim(X_y) ≤ 1` for every `y ∈ Y`, and suppose `H¹(X, 𝒪_X) = 0`. Then `Γ(X, 𝒪_X)` is a flat
`R`-module.

The vanishing of `H¹(X, -)` on globally generated quasi-coherent modules is clause (4) of
[Stacks, Tag 0E7H], which `OneDimensionalFibres.lean` proves from `H¹(X, 𝒪_X) = 0` and the
carried hypothesis `hcoh`. -/
theorem flat_globalSections_of_isProper (hcoh : CohomologyVanishesAboveOne.{u})
    [Flat W.hom] {Y : Scheme.{u}} (f : W.left ⟶ Y) [IsProper f] [IsAffine Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hunit : IsZero (((moduleGlobalSections W.left).rightDerivedPlus 1).obj
      (SheafOfModules.unit W.left.ringCatSheaf))) :
    Module.Flat R Γ(W.left, ⊤) := by
  have _ : CompactSpace (W.left : Type u) := QuasiCompact.compactSpace_of_compactSpace f
  have _ : QuasiSeparatedSpace (W.left : Type u) := quasiSeparatedSpace_of_quasiSeparated f
  refine flat_globalSections_of_generatingSectionsVanishing R W fun G hG σ => ?_
  have _ : G.IsQuasicoherent := hG
  exact isZero_cohomology_one_of_generatingSections_of_fiber_dimension_le_one hcoh f hdim hunit
    G σ

/-- **The tensor identity of the affine computation of [Stacks, Tag 0E7K] (b), with the vanishing
discharged**: under the hypotheses of `flat_globalSections_of_isProper`, the endofunctor
`M ↦ H⁰(X, 𝒪_X ⊗ p^* M~)` of `R`-modules is tensoring with `Γ(X, 𝒪_X)`. -/
def globalSectionsTensorIso_of_isProper (hcoh : CohomologyVanishesAboveOne.{u})
    [Flat W.hom] {Y : Scheme.{u}} (f : W.left ⟶ Y) [IsProper f] [IsAffine Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hunit : IsZero (((moduleGlobalSections W.left).rightDerivedPlus 1).obj
      (SheafOfModules.unit W.left.ringCatSheaf))) :
    MonoidalCategory.tensorLeft
        ((ModuleCat.restrictScalars (algebraMap R Γ(W.left, ⊤))).obj
          (ModuleCat.of Γ(W.left, ⊤) Γ(W.left, ⊤))) ≅
      structureSheafZeroFunctor R W :=
  haveI : CompactSpace (W.left : Type u) := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace (W.left : Type u) := quasiSeparatedSpace_of_quasiSeparated f
  structureSheafZeroTensorGlobalSectionsIso R W fun G hG σ =>
    haveI : G.IsQuasicoherent := hG
    isZero_cohomology_one_of_generatingSections_of_fiber_dimension_le_one hcoh f hdim hunit G σ

/-- **The affine computation of [Stacks, Tag 0E7K] (a), from the tag's own hypotheses.** Let `X`
be flat over `Spec R` and let `f : X ⟶ Y` be proper onto an affine scheme with `dim(X_y) ≤ 1` for
every `y ∈ Y` and `R¹ f_* 𝒪_X = 0`. Then `Γ(X, 𝒪_X)` is a flat `R`-module.

This is `flat_globalSections_of_isProper` with `H¹(X, 𝒪_X) = 0` read off the vanishing of
`R¹ f_* 𝒪_X` over the affine base ([Stacks, Tag 01XK]). -/
theorem flat_globalSections_of_isZero_firstDirectImage (hcoh : CohomologyVanishesAboveOne.{u})
    [Flat W.hom] {Y : Scheme.{u}} (f : W.left ⟶ Y) [IsProper f] [IsAffine Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) :
    Module.Flat R Γ(W.left, ⊤) :=
  flat_globalSections_of_isProper R W hcoh f hdim
    (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward f 1
      (SheafOfModules.unit W.left.ringCatSheaf) hR)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
