module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.Tactic.StacksAttribute

/-!
# Ordinary and derived limits of coherent adic quotients

On a locally Noetherian scheme, the ordinary inverse limit of the quotients of a coherent module
by the powers of a quasi-coherent ideal sheaf is their derived inverse limit, and that limit has
no cohomology in positive degree over an affine open.

## Main definitions

* `Stacks.Algebraization.PowerQuotientSystem` specifies the canonical tower of quotients by the
  powers of an ideal sheaf.
* `Stacks.Algebraization.powerQuotientSystem` realizes that specification for a quasi-coherent
  module, by the tower `Stacks.Algebraization.adicQuotientSystem`.

## Main results

* `Stacks.Algebraization.isDerivedLimit_single_limit_powerQuotients` identifies the ordinary
  limit with the derived limit; this is the tag's part (4).
* `Stacks.Algebraization.isZero_cohomology_limit_powerQuotients_of_isAffineOpen` shows that
  ordinary limit has no cohomology in positive degree over an affine open.
* `Stacks.Algebraization.kernelSubmodule_cokernel_π` identifies the sectionwise kernel of a
  quotient projection with the submodule quotiented out.

## Implementation notes

An ideal sheaf is represented by `Scheme.IdealSheafData`. The quotient tower is specified by its
epimorphic quotient maps, their kernels on affine opens, and compatibility with the transition
maps. The equation with the derived limit is expressed by `IsDerivedLimit` after placing the
ordinary limit in degree zero; existence of the required product is part of the conclusion.

Both registered results are about the ordinary limit `lim ℱ/ℐⁿℱ` itself and not about the
derived completion `ℱ^∧`. That is the form in which [Stacks, Tag 0A0K] proves its parts (4) and
(5), both being read off [Stacks, Tag 0A0J] for the quotient tower. The identification of
`lim ℱ/ℐⁿℱ` with `ℱ^∧` is the tag's own part (3). It is now proved at the tag's own hypotheses,
as `Stacks.Algebraization.isIso_comparisonDerivedCompletionLimitAdicQuotient` of
`Completion/AdicQuotientSliceTowerKoszul.lean`; part (2) is
`Stacks.Algebraization.nonempty_iso_homology_derivedCompletion_limit_adicQuotientSystem` of
`Completion/AdicQuotientLimitSheafIso.lean`, and part (5) on `ℱ^∧` itself is
`Stacks.Algebraization.isZero_homology_derivedSections_derivedCompletion_of_isAffineOpen` of
`Completion/CoherentCompletionAffineVanishing.lean`. The paragraphs below record the route
analysis as it stood before those proofs, and the obstructions they describe have been overcome.

*The derived completion along the tag's own ideal exists.* The derived-completeness predicate
`AlgebraicGeometry.RingedSite.IsDerivedComplete` of `DerivedCompletionRinged/Basic.lean` is
stated at an arbitrary ideal subsheaf of the structure sheaf of a ringed site;
`Stacks.Algebraization.idealSheafSiteSubmodule` of `Completion/IdealSheafSiteSubmodule.lean`
reads a `Scheme.IdealSheafData` as such a subsheaf, and
`Stacks.Algebraization.isFiniteType_idealSheafSiteSubmodule` of
`Completion/IdealSheafSiteFiniteType.lean` shows that it is of finite type on a locally
Noetherian scheme. That is the single hypothesis of [Stacks, Tag 099F],
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of
`DerivedCompletionRinged/FiniteTypeReflector.lean`, so the reflector `(-)^∧` onto the
derived-complete objects of `D(𝒪_X)` — and with it the object `ℱ^∧` the tag speaks of — is
available along an arbitrary quasi-coherent sheaf of ideals of a locally Noetherian scheme.
Prose elsewhere in this subtree saying that [Stacks, Tags 099D, 099E, 099F] stand between this
library and that object is out of date: [Stacks, Tag 099E] is
`AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech` of
`DerivedCompletionRinged/FiniteTypeExtendedCech.lean`, and [Stacks, Tag 0CQI] — the one step of
the source's own route to parts (2) and (3) — is
`AlgebraicGeometry.RingedSite.nonempty_iso_derivedSectionsOverObject_derivedCompletion` of
`DerivedCompletionRinged/LocalCalculationFiniteType.lean`, at a finite-type ideal sheaf and with
nothing assumed.

*What part (3) still needs.* [Stacks, Tag 0A0E] computes `ℱ^∧` as a derived limit of a Koszul
tower; at a finite-type ideal sheaf it does so after restriction to a slice over an object
carrying a finite generating family
(`RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_derivedCompletion_over`),
and on the site itself for an ideal sheaf generated by finitely many global sections. Part (4)
above presents `lim ℱ/ℐⁿℱ` as a derived limit of the quotient tower, and the two towers are
pro-isomorphic on a quasi-compact locally Noetherian scheme
(`Stacks.Algebraization.koszulAdicProIso`); that is how
`Stacks.Algebraization.nonempty_iso_completion_limit_adicQuotientSystem` proves part (3) there.

Two things separate that from the tag's own hypotheses, and both are about the shape of the
argument rather than about a missing input.

* The comparison it produces is non-canonical: [Stacks, Tag 0H9L],
  `_root_.Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism`, turns a pro-isomorphism of
  towers into `Nonempty` of an isomorphism of their derived limits and no more. The source works
  locally and concludes by locality of invertibility, which needs a *canonical* comparison
  `ℱ^∧ ⟶ (lim ℱ/ℐⁿℱ)[0]`; there is one as soon as the target is known to be derived complete,
  because the completion unit is then universal
  (`AlgebraicGeometry.RingedSite.exists_iso_derivedCompletion_of_bijective_precomp` and
  `hom_ext_derivedCompletionUnit` of `DerivedCompletionRinged/ReflectorCompletion.lean`).
  Locality of invertibility is `Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` of
  `CategoryTheory/Sites/Cohomology/Slice/DerivedIsomorphismLocality.lean`, and the restriction of
  the completion to a slice is [Stacks, Tag 0A0F],
  `AlgebraicGeometry.RingedSite.derivedCompletionRestrictIso`.
* Quasi-compactness is genuine for the pro-isomorphism, and only for it: the Artin–Rees level
  making the Koszul cohomology sheaves pro-zero below the top degree is produced one per member
  of an affine cover, and the proof maximises over a finite cover
  (`Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_coherent`). With
  infinitely many charts no single level need exist, so it is the pro-vanishing — not part (3) —
  that fails there. An argument by locality would not use it.

So what stands between this file and part (3) at the tag's own hypotheses is that
`(DerivedCategory.singleFunctor X.Modules 0).obj (limit (adicQuotientSystem I F))` be derived
complete along `ℐ`, and that the canonical map to it from `ℱ^∧` be invertible after restriction
to each affine open. The second is where the mathematics is: the per-slice comparisons the
Koszul route supplies are not canonical, and the Artin–Rees input they rest on is stated for
schemes rather than for a slice of the ringed site.

*The first of those two is settled*, in `Completion/AdicQuotientLimitComplete.lean`:
`Stacks.Algebraization.isDerivedComplete_single_limit_adicQuotientSystem` is the derived
completeness of `(lim ℱ/ℐⁿℱ)[0]` along `ℐ`, on a locally Noetherian scheme and at an arbitrary
quasi-coherent sheaf of ideals, and
`Stacks.Algebraization.existsUnique_comparison_derivedCompletion_limit_adicQuotientSystem` is the
canonical comparison `ℱ^∧ ⟶ (lim ℱ/ℐⁿℱ)[0]` it then produces, unique with respect to the two
units. The work there is sectionwise: [Stacks, Tag 0999] quantifies over every object of the
site, while `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` is an infimum and describes
`ℐⁿℱ` only on the affine opens, so the annihilation of `ℱ/ℐⁿℱ` by powers of local sections of `ℐ`
is carried from the affine description to every open by the locality of membership in a
`SheafOfModules.Submodule`. Only the invertibility of that comparison on affine opens remains.

*Part (1) is proved, and it needed no canonical comparison.*
`Stacks.Algebraization.isDerivedLimit_derivedTensor_adicQuotientSystem_completion` of
`Completion/KoszulAdicDerivedTensorLimit.lean` is `K^∧ = R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)` for an arbitrary
object `K` of `D(𝒪_X)`, on a quasi-compact locally Noetherian scheme and at an ideal sheaf
generated by finitely many global sections. The reason it does not need what part (3) needs is
that `R lim` is a predicate: the assertion is that the *object* `K^∧` is a derived limit of the
tower, and there is no comparison map in it to be canonical about, so the non-canonical
[Stacks, Tag 0H9L] suffices — through
`CategoryTheory.Pretriangulated.IsDerivedLimit.of_proIso`, which transfers the predicate across
a pro-isomorphism of towers. Quasi-compactness there is the same Artin–Rees input as above.

*What part (2) still needs.* Part (2) is [Stacks, Tag 0A0L] over every affine open, whose two
equalities are registered in `Completion/FormalFunctionsPseudoCoherent.lean` with the
identification `RΓ(U, K^∧) = RΓ(U, K)^∧` of [Stacks, Tag 0CQI] as an input. That input is
available in general, and the comparison of the two models of `RΓ(U, -)` the two tags are stated
in — the ringed-space `Stacks.Cohomology.HypercohomologyEdge.derivedSections` and the ringed-site
`AlgebraicGeometry.RingedSite.derivedSectionsOverObject` — is the identity
`Stacks.Algebraization.derivedSectionsOverObject_eq_derivedSections` of
`Completion/CoherentCompletionAffineSections.lean`, which is an identity. What remains is the
passage from a statement about affine sections to one about cohomology sheaves.

That passage does not need the hypercohomology edge morphism at
`K^∧` — that `H^q(U, K^∧)` be identified with `Γ(U, H^q(K^∧))`, which
`Stacks.Cohomology.AcyclicOpen.isIso_hypercohomologyEdge_app_of_isBasis` gives only once the
cohomology sheaves of `K^∧` are acyclic over the affine opens, and the formal completion of a
coherent module is not quasi-coherent. That acyclicity is needed for the edge morphism but is
irrelevant to part (2), because the cohomology sheaf
never has to be evaluated: `Stacks.Cohomology.HypercohomologyEdge`
`.sheafificationCohomologyPresheafIso`, which carries no acyclicity hypothesis at all, says that
`H^q(K^∧)` **is** the sheafification of the hypercohomology presheaf `U ↦ H^q(U, K^∧)`. So the
affine-section statement feeds part (2) by sheafification, and the acyclicity of the cohomology
sheaves of `K^∧` is a *consequence* of part (2) rather than an input to it.

The real obstruction is **naturality in `U`**. Sheafification consumes a morphism of presheaves
(`Stacks.AlgebraicGeometry.MeromorphicConstantModule.isIso_sheafification_map_of_bijective_basis`)
and gluing on a basis consumes a compatible family
(`Stacks.BasisRestriction.moduleSheafIsoOfSectionIsoOnBasis`), while [Stacks, Tag 0A0L] is
formalized
as `Nonempty (… ≅ …)` separately for each `U`, and a family of non-canonical isomorphisms
sheafifies to nothing. What supplies the naturality is a *canonical* affine comparison, and three
results of the library make one available:

* `Stacks.Algebraization.adicCompletionExtend` of
  `Completion/AdicCompleteComparisonBijective.lean` is the canonical map
  `lim H^q(U, K)/IⁿH^q(U, K) ⟶ H^q(U, K^∧)` — note the direction: on a derived tensor the natural
  map runs `H^q(N) ⊗ A/Iⁿ ⟶ H^q(N ⊗^𝐋 A/Iⁿ)` and is only injective, so there is no canonical map
  the other way — and `Stacks.Algebraization.eq_adicCompletionExtend` says it is the *only*
  linear extension of `H^q(RΓ(U, η))` over the completion, which is what makes it natural in `U`
  wherever `H^q(RΓ(U, η))` is.
* `Stacks.Algebraization.bijective_adicCompletionExtend` inverts it, given the non-canonical
  identification of [Stacks, Tag 0A0L] used only for the *properties* it transports and the
  density of `H^q(RΓ(U, η))` modulo `I`.
* That density is
  `Stacks.Algebraization.range_homologyMap_adicCompletionUnit_sup_smul_eq_top_degree` of
  `Completion/CompletionUnitDenseAnyDegree.lean`, transported along a form of [Stacks, Tag 0CQI]
  that is compatible with the completion units — which the `Nonempty` form is not, and
  which `CategoryTheory.ObjectProperty.isoReflectionMap_of_nonempty_iso` of
  `Completion/ReflectionAlongTriangulatedFunctor.lean` produces out of it. The source gets that
  compatibility from [Stacks, Tag 0A0G] at the morphism of ringed topoi `(𝒞, 𝒪) ⟶ (pt, A)`, a
  route unavailable here because `RΓ(U, -)` is not a derived pushforward along a morphism of
  ringed sites — `AlgebraicGeometry.RingedSite`
  `.derivedCompletionUnit_comp_derivedCompletionPushforwardComparison` is exactly the needed
  square but only for such a pushforward; the cited engine runs the same argument at the
  generality of a triangulated functor instead.

The cohomology of part (5) is the derived-functor model `Hgroup` of the sections over an open, so
the degrees are natural numbers and `p ≠ 0` reads as `0 < p`. The vanishing comes from
`Stacks.Cohomology.SpaceInverseLimits.isZero_cohomology_limit_of_isBasis` on the basis of affine
opens, whose two hypotheses are the same two the derived-limit statement consumes.

The kernel clause of the specification is where quasi-coherence of the module enters: the sections
of `I ^ n F` over an affine open `U` are `I(U) ^ n F(U)` only then, and that is
`Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine`. The remaining clauses hold for
an arbitrary sheaf of modules.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and the two
presentations carry separately declared instances, so the lattice of submodules and the
monomorphism property of a submodule inclusion are supplied at the `X.Modules` spelling the
elaborator meets, by the two `attribute [local instance]` lines below; both name an existing
declaration rather than introducing anything.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

-- Mathlib's `Mono N.ι` is stated at the `SheafOfModules X.ringCatSheaf` presentation, which
-- instance resolution does not find through the `def` `AlgebraicGeometry.Scheme.Modules`; this
-- is the same instance restated at the `X.Modules` spelling.
attribute [local instance] monoSubmoduleι

/-- The category of `𝒪_X`-modules on a scheme `X` has enough injectives. -/
noncomputable local instance modulesEnoughInjectives (X : Scheme.{u}) :
    EnoughInjectives X.Modules := by
  let _ : IsGrothendieckAbelian.{u} X.Modules := inferInstance
  exact IsGrothendieckAbelian.enoughInjectives

/-- The derived category of `𝒪_X`-modules on a scheme `X`, in its standard construction. -/
noncomputable local instance modulesHasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory X.Modules :=
  HasDerivedCategory.standard _

/-! ### A tower of quasi-coherent modules with surjective transitions -/

/-- A tower of quasi-coherent modules has no higher cohomology in each term over an affine open. -/
private theorem isZero_hgroup_obj_of_isQuasicoherent {X : Scheme.{u}} (F : ℕᵒᵖ ⥤ X.Modules)
    (hqc : ∀ n : ℕ, (F.obj ⟨n⟩).IsQuasicoherent) {V : X.Opens} (hV : V ∈ X.affineOpens) (n p : ℕ)
    (hp : 0 < p) : IsZero (Hgroup X.ringCatSheaf V p (F.obj ⟨n⟩)) := by
  have := hqc n
  exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X (F.obj ⟨n⟩) V hV p hp

/-- For a tower of quasi-coherent modules with epimorphic transitions, the sections over an affine
open have epimorphic inverse limit difference map. -/
private theorem epi_inverseLimitDifference_of_isQuasicoherent {X : Scheme.{u}}
    (F : ℕᵒᵖ ⥤ X.Modules) (hqc : ∀ n : ℕ, (F.obj ⟨n⟩).IsQuasicoherent)
    (hsurj : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) {V : X.Opens}
    (hV : V ∈ X.affineOpens) :
    Epi (Stacks.Cohomology.SpaceInverseLimits.inverseLimitDifference
      (Stacks.Cohomology.SpaceInverseLimits.sectionsSystem X.toRingedSpace F V)) :=
  Stacks.Cohomology.SpaceInverseLimits.epi_inverseLimitDifference_of_surjective _
    (fun n => by
      have := hqc n
      have := hqc (n + 1)
      have := hsurj n
      exact surjective_app_of_epi_of_isAffineOpen
        (F.map (homOfLE (Nat.le_succ n)).op) ⟨V, hV⟩)

/-- A tower of quasi-coherent modules with epimorphic transition maps has its ordinary inverse
limit, placed in degree zero, as a derived inverse limit.

This stands in for tag 0A0J; delete when that tag lands. The source states the conclusion for each
cohomology-sheaf tower of a tower of objects of the derived category, which specializes to this
when the tower is already a tower of modules, and that is the form the adic quotient tower below
consumes. Both hypotheses of the recovery theorem for a basis of opens hold on the affine opens:
the terms are quasi-coherent, so Serre vanishing applies, and the transitions are surjective on
affine sections, so Mittag-Leffler gives the vanishing of `R¹ lim` of the sections. -/
private theorem isDerivedLimit_single_limit_of_isQuasicoherent (X : Scheme.{u})
    (F : ℕᵒᵖ ⥤ X.Modules) (hqc : ∀ n : ℕ, (F.obj ⟨n⟩).IsQuasicoherent)
    (hsurj : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    ∃ h : HasProduct (fun n : ℕ =>
        (F ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory X.Modules) _ _ _ _ _ _
        (F ⋙ DerivedCategory.singleFunctor X.Modules 0) h
        ((DerivedCategory.singleFunctor X.Modules 0).obj (limit F)) :=
  Stacks.Cohomology.SpaceInverseLimits.isDerivedLimit_single_limit_of_isBasis
    X.toRingedSpace F X.affineOpens X.isBasis_affineOpens
    (fun _ hV n p hp => isZero_hgroup_obj_of_isQuasicoherent F hqc hV n p hp)
    (fun _ hV => epi_inverseLimitDifference_of_isQuasicoherent F hqc hsurj hV)

/-! ### The sections of a sheaf quotient -/

/-- The sectionwise kernel of the projection onto the quotient by a submodule is that submodule.
An ingredient of [Stacks, Tag 0A0K]. An alias of
`Stacks.Algebraization.kernelSubmodule_cokernel_π_ι`. -/
public alias kernelSubmodule_cokernel_π := kernelSubmodule_cokernel_π_ι

/-- A section of a quasi-coherent module over an affine open `U` dies in `F / I ^ n F` exactly when
it lies in `I(U) ^ n F(U)`. The kernel clause of [Stacks, Tag 0A0K]. -/
public lemma cokernel_π_idealPowerMultiple_app_eq_zero_iff {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) [F.IsQuasicoherent] (U : X.affineOpens)
    (s : Γ(F, U)) :
    (cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι).app U.1 s = 0 ↔
      s ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(F, U)) := by
  rw [← idealPowerMultiple_toSubmodule_obj_affine I n F U]
  conv_rhs => rw [← kernelSubmodule_cokernel_π (idealPowerMultiple I n F),
    kernelSubmodule_toSubmodule_obj]
  exact Iff.rfl

/-! ### The adic quotient tower and its derived limit -/

/-- The quotient tower `F / IⁿF`, characterized on affine opens by the kernel of each quotient map
and with the canonical transition maps. The tower whose limit [Stacks, Tag 0A0K] is about. -/
public structure PowerQuotientSystem {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) where
  /-- The inverse system of quotients. -/
  system : ℕᵒᵖ ⥤ X.Modules
  /-- The quotient map onto each term. -/
  quotient : ∀ n : ℕᵒᵖ, F ⟶ system.obj n
  /-- Each quotient map is an epimorphism. -/
  quotient_epi : ∀ n, Epi (quotient n)
  /-- On an affine open the kernel of the `n`-th quotient map is `I(U) ^ n F(U)`. -/
  quotient_kernel : ∀ (n : ℕᵒᵖ) (U : X.affineOpens) (s : Γ(F, U)),
    (quotient n).app U s = 0 ↔
      s ∈ (I.ideal U) ^ n.unop • (⊤ : Submodule Γ(X, U) Γ(F, U))
  /-- The quotient maps are compatible with the transition maps. -/
  quotient_naturality : ∀ {i j : ℕᵒᵖ} (hij : i ⟶ j),
    quotient i ≫ system.map hij = quotient j

/-- The inverse system of quotients of a quasi-coherent sheaf of modules by the powers of a
quasi-coherent ideal sheaf. Its specification fixes both the quotient maps and the transitions.
The tower of [Stacks, Tag 0A0K].

This is `Stacks.Algebraization.adicQuotientSystem` together with the cokernel projections. -/
public noncomputable def powerQuotientSystem {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (hF : F.IsQuasicoherent) :
    PowerQuotientSystem I F where
  system := adicQuotientSystem I F
  quotient n := cokernel.π (C := X.Modules) (idealPowerMultiple I n.unop F).ι
  quotient_epi _ := coequalizer.π_epi
  quotient_kernel n U s := by
    have := hF
    exact cokernel_π_idealPowerMultiple_app_eq_zero_iff I n.unop F U s
  quotient_naturality hij :=
    quotientMapOfLE_π (idealPowerMultiple_antitone I F (leOfHom hij.unop))

/-- The quotient tower underlying `Stacks.Algebraization.powerQuotientSystem` is
`Stacks.Algebraization.adicQuotientSystem`. -/
@[simp]
public lemma powerQuotientSystem_system {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (hF : F.IsQuasicoherent) :
    (powerQuotientSystem I F hF).system = adicQuotientSystem I F :=
  rfl

/-- Every term of the adic quotient tower of a quasi-coherent module is quasi-coherent.
An ingredient of [Stacks, Tag 0A0K]. -/
public lemma isQuasicoherent_adicQuotientSystem_obj {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    ((adicQuotientSystem I F).obj ⟨n⟩).IsQuasicoherent := by
  have : ((idealPowerMultiple I n F).toSheafOfModules : X.Modules).IsQuasicoherent :=
    idealPowerMultiple_isQuasicoherent I n F
  exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (X := X) (M := ((idealPowerMultiple I n F).toSheafOfModules : X.Modules)) (N := F)
    (idealPowerMultiple I n F).ι

/-- The transition maps of the adic quotient tower are epimorphisms.
An ingredient of [Stacks, Tag 0A0K]. -/
public lemma epi_adicQuotientSystem_map {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    Epi ((adicQuotientSystem I F).map (homOfLE (Nat.le_succ n)).op) := by
  have hπ : cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F).ι ≫
      (adicQuotientSystem I F).map (homOfLE (Nat.le_succ n)).op =
        cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι :=
    quotientMapOfLE_π (idealPowerMultiple_antitone I F (Nat.le_succ n))
  have hepi : Epi (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F).ι ≫
      (adicQuotientSystem I F).map (homOfLE (Nat.le_succ n)).op) := by
    rw [hπ]
    exact coequalizer.π_epi
  exact epi_of_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F).ι) _

/-- **Stacks Project, Tag 0A0K, part (4).** The ordinary inverse limit of the coherent adic
quotient tower, placed in degree zero, is its derived inverse limit. -/
@[stacks 0A0K "part (4), `lim ℱ/𝓘ⁿℱ = R lim ℱ/𝓘ⁿℱ`: for a coherent module `ℱ` on a locally \
Noetherian scheme and an arbitrary quasi-coherent sheaf of ideals `𝓘`, the **ordinary** inverse \
limit of the adic quotient tower, placed in degree zero, is a **derived** inverse limit of that \
tower, with nothing assumed. The terms of the tower are quasi-coherent, hence acyclic on the \
affine opens, and its transitions are surjective on affine sections, hence Mittag-Leffler, and \
those are the two hypotheses [Stacks, Tag 0BKS] consumes. Existence of the product the derived \
limit is written with is part of the conclusion rather than a hypothesis"]
public theorem isDerivedLimit_single_limit_powerQuotients
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsCoherent] :
    let S := (powerQuotientSystem I F
      (isQuasicoherent_of_isCoherent F)).system
    ∃ h : HasProduct (fun n : ℕ =>
        (S ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory X.Modules) _ _ _ _ _ _
        (S ⋙ DerivedCategory.singleFunctor X.Modules 0) h
        ((DerivedCategory.singleFunctor X.Modules 0).obj (limit S)) := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  exact isDerivedLimit_single_limit_of_isQuasicoherent X (adicQuotientSystem I F)
    (isQuasicoherent_adicQuotientSystem_obj I F) (epi_adicQuotientSystem_map I F)

/-- **Stacks Project, Tag 0A0K, part (5).** On a locally Noetherian scheme the ordinary inverse
limit `lim ℱ/ℐⁿℱ` of the adic quotient tower of a coherent module has no cohomology in positive
degree over an affine open.

The terms of the tower are quasi-coherent, so Serre vanishing gives their acyclicity on the
affine opens, and the transition maps are epimorphisms of quasi-coherent modules, hence
surjective on affine sections, so Mittag-Leffler gives the vanishing of `R¹ lim` of the sections
there. Those are exactly the two hypotheses of
`Stacks.Cohomology.SpaceInverseLimits.isZero_cohomology_limit_of_isBasis` on the basis of affine
opens.

The object is the ordinary limit `lim ℱ/ℐⁿℱ`, which is what the source's own argument for this
part is about: parts (4) and (5) are both read off [Stacks, Tag 0A0J] for the quotient tower,
and it is the tag's part (3) that then names that limit `ℱ^∧`. In this library part (3) at the
tag's own hypotheses is
`Stacks.Algebraization.isIso_comparisonDerivedCompletionLimitAdicQuotient` of
`Completion/AdicQuotientSliceTowerKoszul.lean`, and part (5) stated on the derived completion `ℱ^∧`
itself, in every degree `p ≠ 0` of either sign, is
`Stacks.Algebraization.isZero_homology_derivedSections_derivedCompletion_of_isAffineOpen` of
`Completion/CoherentCompletionAffineVanishing.lean`, which is derived from this statement through
that isomorphism. -/
@[stacks 0A0K "part (5), `H^p(U, ℱ^∧) = 0` for `p ≠ 0` and `U ⊂ X` affine open, read on the \
ordinary limit `lim ℱ/ℐⁿℱ` — the object [Stacks, Tag 0A0K] part (3) names `ℱ^∧` — for a \
coherent module `ℱ` on a locally Noetherian scheme and an arbitrary quasi-coherent sheaf of \
ideals `ℐ`, with nothing assumed: the terms of the adic quotient tower are quasi-coherent, \
hence acyclic on the affine opens, and its transitions are surjective on affine sections, hence \
Mittag-Leffler, and those are the two hypotheses [Stacks, Tag 0BKS] consumes"]
public theorem isZero_cohomology_limit_powerQuotients_of_isAffineOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsCoherent]
    (U : X.affineOpens) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf U.1 p
      (show X.Modules from limit (adicQuotientSystem I F))) := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  exact Stacks.Cohomology.SpaceInverseLimits.isZero_cohomology_limit_of_isBasis
    X.toRingedSpace (adicQuotientSystem I F) X.affineOpens X.isBasis_affineOpens
    (fun _ hV n _ hp => isZero_hgroup_obj_of_isQuasicoherent _
      (isQuasicoherent_adicQuotientSystem_obj I F) hV n _ hp)
    (fun _ hV => epi_inverseLimitDifference_of_isQuasicoherent _
      (isQuasicoherent_adicQuotientSystem_obj I F) (epi_adicQuotientSystem_map I F) hV)
    U.1 U.2 p hp

end Stacks.Algebraization

end
