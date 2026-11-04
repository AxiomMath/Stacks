module

public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TwistedSectionsFunctor
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.SheafMapIsIso
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistComparisonCompact

/-!
# `(⨁_{n ≥ 0} Γ(X, ℱ(n)))~ ⟶ ℱ`, as a natural transformation

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring and `X = Proj 𝒮`. Tag 0B5I attaches to a
sheaf of `𝒪_X`-modules `ℱ` a canonical comparison morphism

`(⨁_{n ∈ ℤ} Γ(X, ℱ(n)))~ ⟶ ℱ`

(`Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.integerComparison`), and Tag 0AG5 says it
is an isomorphism for `X` quasi-compact and `ℱ` quasi-coherent. Tags 0BXD and 0BXF name the
*nonnegative* truncation `ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))` as the quasi-inverse of `M ↦ M̃`, so what
those propositions need is the composite

`(⨁_{n ≥ 0} Γ(X, ℱ(n)))~ ⟶ (⨁_{n ∈ ℤ} Γ(X, ℱ(n)))~ ⟶ ℱ`,

as a natural transformation of functors. This file constructs it and proves that both of its
factors are isomorphisms: the first, induced by the inclusion of the truncation, with no
hypothesis, and the second, by Tag 0AG5, for `X` quasi-compact and `ℱ` quasi-coherent.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.twistedSectionsCounit`: the comparison of
  Tag 0B5I as a natural transformation `(ℱ ↦ ⨁_{n ∈ ℤ} Γ(X, ℱ(n))) ⋙ (M ↦ M̃) ⟶ 𝟭`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegInclusion` and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegInclusionNatTrans`: the inclusion
  `⨁_{n ≥ 0} Γ(X, ℱ(n)) ⟶ ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` of graded modules, and its naturality.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.nonnegSectionsCounit`: the composite
  natural transformation `(ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))) ⋙ (M ↦ M̃) ⟶ 𝟭`.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIso_map_nonnegInclusion`: the inclusion of
  the truncation induces an isomorphism of associated sheaves, with no hypothesis.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIso_nonnegSectionsCounit_app`: each
  component of `nonnegSectionsCounit` is an isomorphism, for `Proj 𝒮` quasi-compact and `ℱ`
  quasi-coherent.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 0AG5](https://stacks.math.columbia.edu/tag/0AG5)
* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (GradedModuleCat associatedModuleSheafFunctor)
open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.AlgebraicGeometry.ProjTwistComparison (twistedGlobalSectionsAssociatedSheafMap)
open Stacks.AlgebraicGeometry.ProjTwistIntegerComparison
  (integerComparison integerComparison_naturality)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
  (isIso_associatedModuleSheafMap_of_eventually_bijective)

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance] twistedGlobalSectionsModuleInstance nonnegTwistedSectionsModule

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-! ### The comparison of Tag 0B5I, bundled -/

/-- The sheaf `(⨁_{n ∈ ℤ} Γ(X, ℱ(n)))~` obtained by applying `associatedModuleSheafFunctor` to
`twistedSectionsGradedModule 𝒮 ℱ` is `twistedGlobalSectionsAssociatedSheaf 𝒮 ℱ`, the source of
the comparison morphism of Tag 0B5I. -/
theorem associatedModuleSheafFunctor_obj_twistedSectionsGradedModule :
    (associatedModuleSheafFunctor.{u, u, w} 𝒮).obj (twistedSectionsGradedModule 𝒮 F) =
      twistedGlobalSectionsAssociatedSheaf 𝒮 F (twistedGlobalSectionsModule 𝒮 F) :=
  rfl

variable {E F' : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))}

/-- The image under `associatedModuleSheafFunctor` of `twistedSectionsGradedMap 𝒮 ψ` is the
morphism `twistedGlobalSectionsAssociatedSheafMap` of associated sheaves induced by `ψ`. -/
theorem associatedModuleSheafFunctor_map_twistedSectionsGradedMap (ψ : E ⟶ F') :
    (associatedModuleSheafFunctor.{u, u, w} 𝒮).map (twistedSectionsGradedMap 𝒮 ψ) =
      twistedGlobalSectionsAssociatedSheafMap 𝒮 (twistedGlobalSectionsModule 𝒮 E)
        (twistedGlobalSectionsModule 𝒮 F') ψ :=
  rfl

/-- The comparison morphism of Tag 0B5I as a natural transformation
`(ℱ ↦ ⨁_{n ∈ ℤ} Γ(X, ℱ(n))) ⋙ (M ↦ M̃) ⟶ 𝟭`, whose component at `ℱ` is the canonical
`(⨁_{n ∈ ℤ} Γ(X, ℱ(n)))~ ⟶ ℱ`. -/
def twistedSectionsCounit :
    twistedSectionsFunctor.{u, w} 𝒮 ⋙ associatedModuleSheafFunctor.{u, u, w} 𝒮 ⟶
      𝟭 (SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) where
  app G := integerComparison 𝒮 G (twistedGlobalSectionsModule 𝒮 G)
  naturality G H ψ := integerComparison_naturality 𝒮 (twistedGlobalSectionsModule 𝒮 G)
    (twistedGlobalSectionsModule 𝒮 H) ψ

/-- The component of the bundled comparison at a sheaf is the comparison of Tag 0B5I. -/
@[simp]
theorem twistedSectionsCounit_app :
    (twistedSectionsCounit.{u, w} 𝒮).app F =
      integerComparison 𝒮 F (twistedGlobalSectionsModule 𝒮 F) :=
  rfl

/-- Over a quasi-compact `Proj 𝒮`, the component of `twistedSectionsCounit` at a quasi-coherent
sheaf is an isomorphism. -/
theorem isIso_twistedSectionsCounit_app [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) :
    IsIso ((twistedSectionsCounit.{u, w} 𝒮).app F) :=
  ProjTwistComparisonCompact.isIso_integerComparison 𝒮 F hqc

/-! ### The inclusion of the nonnegative truncation -/

/-- The inclusion `⨁_{n ≥ 0} Γ(X, ℱ(n)) ⟶ ⨁_{n ∈ ℤ} Γ(X, ℱ(n))`, as a degree-preserving
morphism of graded `S`-modules. -/
def nonnegInclusion : nonnegTwistedSections 𝒮 F ⟶ twistedSectionsGradedModule 𝒮 F where
  toLinearMap :=
    (TwistedGlobalSectionsModule.truncation 𝒮 F (twistedGlobalSectionsModule 𝒮 F) 0).subtype
  map_grade _ _ hx := hx

/-- The inclusion `⨁_{n ≥ 0} Γ(X, ℱ(n)) ⟶ ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` as a natural transformation of
functors of `ℱ`. -/
def nonnegInclusionNatTrans :
    nonnegTwistedSectionsFunctor.{u, w} 𝒮 ⟶ twistedSectionsFunctor.{u, w} 𝒮 where
  app G := nonnegInclusion 𝒮 G
  naturality _ _ _ := rfl

/-- The component of the bundled inclusion at a sheaf is the inclusion. -/
@[simp]
theorem nonnegInclusionNatTrans_app :
    (nonnegInclusionNatTrans.{u, w} 𝒮).app F = nonnegInclusion 𝒮 F :=
  rfl

/-- The inclusion `⨁_{n ≥ 0} Γ(X, ℱ(n)) ⟶ ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` induces an isomorphism of
associated sheaves, with no hypothesis on `𝒮` or `ℱ`. -/
theorem isIso_map_nonnegInclusion :
    IsIso ((associatedModuleSheafFunctor.{u, u, w} 𝒮).map (nonnegInclusion 𝒮 F)) := by
  refine isIso_associatedModuleSheafMap_of_eventually_bijective 𝒮 _ _ _
    (nonnegInclusion 𝒮 F).map_grade (N₀ := (0 : ℤ))
    (fun _ _ _ _ h => Subtype.ext h)
    (fun j hj n hn => ⟨⟨n, coe_twistedGlobalSectionsGrading_subset_truncation 𝒮 F
      (twistedGlobalSectionsModule 𝒮 F).smul_homogeneous 0 j hj hn⟩, hn, rfl⟩)

/-! ### The candidate counit -/

/-- The natural transformation

`(ℱ ↦ ⨁_{n ≥ 0} Γ(X, ℱ(n))) ⋙ (M ↦ M̃) ⟶ 𝟭`

whose component at `ℱ` is the map of associated sheaves induced by the inclusion of the
truncation, followed by the comparison morphism of Tag 0B5I. -/
def nonnegSectionsCounit :
    nonnegTwistedSectionsFunctor.{u, w} 𝒮 ⋙ associatedModuleSheafFunctor.{u, u, w} 𝒮 ⟶
      𝟭 (SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) :=
  Functor.whiskerRight (nonnegInclusionNatTrans.{u, w} 𝒮)
      (associatedModuleSheafFunctor.{u, u, w} 𝒮) ≫
    twistedSectionsCounit.{u, w} 𝒮

/-- The component of `nonnegSectionsCounit` at `ℱ` is the map of associated sheaves induced by
`nonnegInclusion` followed by `integerComparison`. -/
theorem nonnegSectionsCounit_app :
    (nonnegSectionsCounit.{u, w} 𝒮).app F =
      (associatedModuleSheafFunctor.{u, u, w} 𝒮).map (nonnegInclusion 𝒮 F) ≫
        integerComparison 𝒮 F (twistedGlobalSectionsModule 𝒮 F) := by
  simp [nonnegSectionsCounit, twistedSectionsCounit, nonnegInclusionNatTrans]

/-- For `Proj 𝒮` quasi-compact and `ℱ` quasi-coherent, the component of `nonnegSectionsCounit`
at `ℱ` is an isomorphism. -/
theorem isIso_nonnegSectionsCounit_app [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) :
    IsIso ((nonnegSectionsCounit.{u, w} 𝒮).app F) := by
  rw [nonnegSectionsCounit_app]
  exact IsIso.comp_isIso' (isIso_map_nonnegInclusion.{u, w} 𝒮 F)
    (ProjTwistComparisonCompact.isIso_integerComparison 𝒮 F hqc)

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
