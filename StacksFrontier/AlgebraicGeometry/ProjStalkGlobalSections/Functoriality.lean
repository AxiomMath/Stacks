module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections

/-!
# Stalks and global sections of a map of associated module sheaves

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ` and let `φ : M →ₗ[S] N`
be a degree-preserving linear map of `ℤ`-graded `S`-modules. Under the identification of the
stalk of an associated sheaf with the degree-zero localization at a homogeneous prime, the
morphism `M̃ ⟶ Ñ` induced by `φ` is the localization of `φ` at that prime; and the canonical
map from degree-zero elements into global sections is natural in the graded module.

Together with the standard-open formula and the functor laws, which are in
`StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic`, these two statements
complete the assertions of Tag 01M7 about functoriality, so the tag is attached here.

## Main results

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafMap_stalk`: the
  stalk identification intertwines the induced morphism with localization of `φ`.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections_naturality`:
  the canonical degree-zero map into global sections is natural in the graded module.

## Implementation notes

The stalk of the associated sheaf is the colimit of the underlying presheaf of abelian
groups over the open neighbourhoods of the point, so the induced map on stalks is the
colimit of the whiskered presheaf morphism, `CategoryTheory.Limits.colim.map`. Both sides of
the stalk formula are additive maps out of that colimit, so they agree as soon as they agree
on every germ, which is `CategoryTheory.Limits.colimit.hom_ext`; on a germ the formula is the
definition of the induced morphism on sections.

Naturality of the global-sections map is a pointwise computation: a section of the associated
sheaf is determined by its values, the induced morphism acts on a value by localizing `φ`,
and the value of the global section attached to `m` is the fraction `m / 1`.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u v w t t'

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M N : Type v} {σ : Type w} {τ : Type t} {υ : Type t'}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- On sections, the morphism induced by a degree-preserving linear map is the localization
of that map in every homogeneous-prime fiber. -/
theorem associatedModuleSheafMap_app_apply (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)) (x : U) :
    ((ProjSheafFunctoriality.associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app (op U) s).1 x =
      LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl φ (s.1 x) := rfl

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- The stalk identification intertwines the morphism of associated sheaves induced by a
degree-preserving linear map with the localization of that map at the homogeneous prime. -/
theorem associatedModuleSheafMap_stalk (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i)
    (x : ProjectiveSpectrum.top 𝒮)
    (s : associatedModuleSheafStalk 𝒮 𝒨 x) :
    ((associatedModuleSheafStalkEquiv 𝒮 𝒩 x
      (CategoryTheory.Limits.colim.map
        (Functor.whiskerLeft (OpenNhds.inclusion x).op
          ((PresheafOfModules.toPresheaf _).map
            (ProjSheafFunctoriality.associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val)) s) :
        degreeZeroModuleAt 𝒮 𝒩 x) : ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) =
      LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ
        (associatedModuleSheafStalkEquiv 𝒮 𝒨 x s : degreeZeroModuleAt 𝒮 𝒨 x) := by
  let F := (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf
  let G := (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩).val.presheaf
  let α : F ⟶ G := (PresheafOfModules.toPresheaf _).map
    (ProjSheafFunctoriality.associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val
  let β := Functor.whiskerLeft (OpenNhds.inclusion x).op α
  let stalkMap : associatedModuleSheafStalk 𝒮 𝒨 x ⟶ associatedModuleSheafStalk 𝒮 𝒩 x :=
    Limits.colim.map β
  let eM := associatedModuleSheafStalkEquiv 𝒮 𝒨 x
  let eN := associatedModuleSheafStalkEquiv 𝒮 𝒩 x
  let pM := (Submodule.subtype _).toAddMonoidHom.comp eM.toAddMonoidHom
  let pN := (Submodule.subtype _).toAddMonoidHom.comp eN.toAddMonoidHom
  let left : AddMonoidHom (associatedModuleSheafStalk 𝒮 𝒨 x)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) :=
    pN.comp (ConcreteCategory.hom stalkMap)
  let right : AddMonoidHom (associatedModuleSheafStalk 𝒮 𝒨 x)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) :=
    (LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ).toAddMonoidHom.comp pM
  have hcat : AddCommGrpCat.ofHom left = AddCommGrpCat.ofHom right := by
    apply Limits.colimit.hom_ext
    intro U
    induction U with
    | op V =>
      let U := V.1
      let hxU : x ∈ U := V.2
      ext t
      change ((OpenNhds.inclusion x).op ⋙ F).obj (op V) at t
      let tM : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U) := by
        change ((OpenNhds.inclusion x).op ⋙ F).obj (op V)
        exact t
      let tN : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩).val.obj (op U) := by
        change ((OpenNhds.inclusion x).op ⋙ G).obj (op V)
        exact β.app (op V) t
      let gM := associatedModuleSheafGerm 𝒮 𝒨 x U hxU tM
      have hg : stalkMap gM = associatedModuleSheafGerm 𝒮 𝒩 x U hxU tN := by
        change Limits.colim.map β
            (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ F) (op V) t) =
          Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ G) (op V) (β.app (op V) t)
        exact Limits.colimit.ι_map_apply β (op V) t
      change eN (stalkMap gM) =
        LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ (eM gM)
      rw [hg]
      change ((associatedModuleSheafStalkEquiv 𝒮 𝒩 x
          (associatedModuleSheafGerm 𝒮 𝒩 x U hxU tN) : degreeZeroModuleAt 𝒮 𝒩 x) :
          ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) =
        LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ
          ((associatedModuleSheafStalkEquiv 𝒮 𝒨 x gM : degreeZeroModuleAt 𝒮 𝒨 x) :
            ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x)
      calc
        (associatedModuleSheafStalkEquiv 𝒮 𝒩 x
            (associatedModuleSheafGerm 𝒮 𝒩 x U hxU tN) :
            ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) = tN.1 ⟨x, hxU⟩ :=
          associatedModuleSheafStalkEquiv_germ 𝒮 𝒩 x U hxU tN
        _ = LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ
            (tM.1 ⟨x, hxU⟩) :=
          associatedModuleSheafMap_app_apply 𝒮 𝒨 𝒩 φ hφ U tM ⟨x, hxU⟩
        _ = LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ
            ((associatedModuleSheafStalkEquiv 𝒮 𝒨 x gM : degreeZeroModuleAt 𝒮 𝒨 x) :
              ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) :=
          congrArg _ (associatedModuleSheafStalkEquiv_germ 𝒮 𝒨 x U hxU tM).symm
  exact ConcreteCategory.congr_hom hcat s

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- The canonical map from degree-zero elements into global sections is natural in the
graded module. -/
theorem degreeZeroToGlobalSections_naturality (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (m : 𝒨 0) :
    (ProjSheafFunctoriality.associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app (op ⊤)
      (degreeZeroToGlobalSections 𝒮 𝒨 m) =
    degreeZeroToGlobalSections 𝒮 𝒩 ⟨φ m.1, hφ 0 m.1 m.2⟩ := by
  apply Subtype.ext
  funext x
  rw [associatedModuleSheafMap_app_apply, degreeZeroToGlobalSections_apply,
    degreeZeroToGlobalSections_apply, LocalizedModule.map_mk]

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections
