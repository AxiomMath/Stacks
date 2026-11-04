module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Exactness

/-!
# The associated-sheaf functor on `Proj` is exact

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ`. The functor
`M ↦ M̃` from graded `S`-modules with degree-preserving maps to sheaves of
`𝒪_{Proj(S)}`-modules, which is
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor`, is exact: a
short exact sequence `0 → M → N → P → 0` of graded `S`-modules is carried to a short exact
sequence `0 → M̃ → Ñ → P̃ → 0` in `SheafOfModules 𝒪_{Proj(S)}`.

## Main results

* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor_map_comp_eq_zero`:
  the functor carries a composable pair of degree-preserving maps whose composite vanishes to a
  complex of sheaves of modules.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor_shortExact`:
  the short complex of sheaves of modules obtained from a short exact sequence of graded
  modules is short exact in `SheafOfModules 𝒪_{Proj(S)}`.

## Implementation notes

The proof is the one the source gives: short exactness in the category of sheaves of modules
is short exactness of the sequence of stalks at every point, which is Stacks Tag 01AG, and the
stalk sequences were shown to be short exact in
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkMap_shortExact`.
The stalkwise criterion is used in its module form,
`AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact`, which refines
the abelian-group form `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`
that carries the 01AG tag. Nothing about the stalks is reproved: the stalk map of
`associatedModuleSheafMap` *is*
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkMap` on the nose,
because both are `TopCat.Presheaf.stalkFunctor AddCommGrpCat x` applied to the underlying
morphism of presheaves of abelian groups, so the three clauses transfer by `rfl` (see
`associatedModuleSheafFunctor_stalkMap_coe`).

**The universes are forced, not chosen.** `associatedModuleSheafFunctor.{u, v, w}` sends a
graded module with carrier in `Type v` to a `SheafOfModules.{max u v}` over the space
`ProjectiveSpectrum.top 𝒮 : TopCat.{u}`, and the statement proved here is its restriction to
carriers in `Type u`. The restriction is not a choice: Mathlib's
`TopCat.Presheaf.stalkFunctor C x` ties the universe of the space to the hom universe of `C`
(the same obstruction recorded in
`StacksFrontier/AlgebraicGeometry/ProjStalkGlobalSections/Stalk.lean`), so the stalkwise
criterion for sheaves of modules — 01AG and every form of it — exists only when the modules
live in the universe of the space. Over a space in `Type u` the sheafification needed for the
abelian structure on `SheafOfModules.{max u v}` can still be built by hand from
`CategoryTheory.hasSheafifyEssentiallySmallSite`, but the stalk functor cannot, and with it
goes the criterion; `Abelian (SheafOfModules.{max u v} 𝒪)` is not even found by instance
search at `v ≠ u`.

The category of graded modules is a plain category, not an abelian one, so "exact functor" is
stated as preservation of short exact sequences, with injectivity, surjectivity and exactness
of the given maps as hypotheses, matching the shape of the stalkwise statement.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u w t t'

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M N : Type u} {σ : Type w} {τ : Type t} {υ : Type t'}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- A degree-preserving map that vanishes induces the zero morphism of associated sheaves:
the induced map on sections over an open is the localization of the given map at each point,
and the localization of the zero map is zero. -/
private theorem associatedModuleSheafMap_eq_zero (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (h0 : ∀ m : M, φ m = 0) :
    associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext a
  apply Subtype.ext
  funext x
  have key : ∀ z : ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x.1,
      LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | _ m s => simp [h0 m]
  show LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ
    ((a : ↥(ProjectiveSpectrum.Proj.moduleSections 𝒮 𝒨 (unop U))).1 x) = 0
  exact key _

variable {𝒮}

/-- **Stacks Project, Tag 01M7.** A composable pair of degree-preserving maps of graded
modules whose composite vanishes is carried by `M ↦ M̃` to a complex of sheaves of
`𝒪_{Proj(S)}`-modules. -/
theorem associatedModuleSheafFunctor_map_comp_eq_zero
    {X Y Z : GradedModuleCat.{u, u, w} 𝒮} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (hcomp : ∀ m : X.carrier, ψ.toLinearMap (φ.toLinearMap m) = 0) :
    (associatedModuleSheafFunctor 𝒮).map φ ≫ (associatedModuleSheafFunctor 𝒮).map ψ = 0 :=
  (Functor.map_comp (associatedModuleSheafFunctor 𝒮) φ ψ).symm.trans
    (associatedModuleSheafMap_eq_zero 𝒮 X.grade Z.grade (φ ≫ ψ).toLinearMap
      (φ ≫ ψ).map_grade hcomp)

/-- The map on stalks induced by `(associatedModuleSheafFunctor 𝒮).map φ` is the map
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkMap` induced by the
underlying degree-preserving map: both are `TopCat.Presheaf.stalkFunctor AddCommGrpCat x`
applied to the underlying morphism of presheaves of abelian groups. -/
theorem associatedModuleSheafFunctor_stalkMap_coe
    {X Y : GradedModuleCat.{u, u, w} 𝒮} (φ : X ⟶ Y)
    (x : ProjectiveSpectrum.top 𝒮) :
    ⇑(ConcreteCategory.hom
        (AlgebraicGeometry.SheafOfModules.stalkMap
          ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) x
          ((associatedModuleSheafFunctor 𝒮).map φ))) =
      ⇑(ProjStalkGlobalSections.associatedModuleSheafStalkMap 𝒮 X.grade Y.grade
          φ.toLinearMap φ.map_grade x) :=
  rfl

/-- **Stacks Project, Tag 01M7.** The functor `M ↦ M̃` is exact: a short exact sequence of
graded `S`-modules with degree-preserving maps is carried to a short exact sequence of sheaves
of `𝒪_{Proj(S)}`-modules.

The sheaf-level conclusion comes from the stalkwise one,
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkMap_shortExact`,
through the criterion of Tag 01AG that short exactness of a sequence of sheaves of modules is
short exactness of the sequences of stalks. -/
theorem associatedModuleSheafFunctor_shortExact
    {X Y Z : GradedModuleCat.{u, u, w} 𝒮} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (hinj : Function.Injective φ.toLinearMap)
    (hsurj : Function.Surjective ψ.toLinearMap)
    (hexact : Function.Exact φ.toLinearMap ψ.toLinearMap) :
    (ShortComplex.mk ((associatedModuleSheafFunctor 𝒮).map φ)
        ((associatedModuleSheafFunctor 𝒮).map ψ)
        (associatedModuleSheafFunctor_map_comp_eq_zero φ ψ
          fun m => (hexact (φ.toLinearMap m)).mpr ⟨m, rfl⟩)).ShortExact := by
  refine (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact _).2
    fun x => ?_
  obtain ⟨hi, he, hs⟩ := ProjStalkGlobalSections.associatedModuleSheafStalkMap_shortExact
    𝒮 X.grade Y.grade Z.grade φ.toLinearMap φ.map_grade ψ.toLinearMap ψ.map_grade
    hinj hsurj hexact x
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 he)
    ((ModuleCat.mono_iff_injective _).2 hi)
    ((ModuleCat.epi_iff_surjective _).2 hs)

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality

end
