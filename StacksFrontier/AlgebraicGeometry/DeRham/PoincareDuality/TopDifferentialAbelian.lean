module

public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
public import StacksFrontier.Cotangent.CohomologyPresheaf.BiggerSiteGlobal
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero

/-!
# Cohomology of abelian sheaves: three comparisons used in degree `d`

Let `X` be a topological space and write `Hᵖ(X, -)` for the right derived functors of global
sections on abelian sheaves, `(Stacks.Cohomology.Leray.sectionsFunctor X ⊤).rightDerived p`.
This file records three facts about these functors.

* `Hᵖ(X, -)` is naturally isomorphic to Mathlib's `Sheaf.H`, the `Ext`-groups out of the constant
  sheaf `ℤ` (`functorHIsoSectionsRightDerived`).
* For a closed embedding `i : Z ⟶ X`, a morphism `φ` of abelian sheaves on `Z` induces zero on
  `Hᵖ(Z, -)` as soon as `i_* φ` induces zero on `Hᵖ(X, -)`: cohomology of `Z` is cohomology of
  `X` after pushforward ([Stacks, Tag 02UV]).
* On a Noetherian space of dimension at most `d`, an epimorphism of abelian sheaves induces a
  surjection on `Hᵈ(X, -)`: the obstruction lies in `Hᵈ⁺¹(X, ker)`, which vanishes by
  Grothendieck's theorem ([Stacks, Tag 02UZ]).
* For a sheaf of rings `R`, a morphism of `R`-modules is injective (surjective) on the cohomology
  of `R`-modules if and only if it is so on the cohomology of the underlying abelian sheaves
  ([Stacks, Tag 01F1]).

## References

* [Stacks Project, Tag 02UV](https://stacks.math.columbia.edu/tag/02UV)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

namespace Stacks.Cohomology.TopDegree

section Functors

variable {C D : Type*} [Category* C] [Category* D]

/-- A morphism inducing zero along one of two isomorphic functors induces zero along the
other. -/
theorem map_eq_zero_of_natIso [Preadditive D] {F G : C ⥤ D} (e : F ≅ G) {A B : C}
    (φ : A ⟶ B) (h : G.map φ = 0) : F.map φ = 0 := by
  have hn := e.hom.naturality φ
  rw [h, comp_zero] at hn
  exact (cancel_mono (e.hom.app B)).1 (hn.trans zero_comp.symm)

/-- Surjectivity of the induced map of abelian groups transports along an isomorphism of
functors. -/
theorem surjective_map_of_natIso {F G : C ⥤ AddCommGrpCat.{u}} (e : F ≅ G) {A B : C}
    (φ : A ⟶ B) (h : Function.Surjective (F.map φ)) : Function.Surjective (G.map φ) := by
  rw [← AddCommGrpCat.epi_iff_surjective] at h ⊢
  rw [← NatIso.naturality_1 e φ]
  infer_instance

/-- Injectivity of the induced map of abelian groups transports along an isomorphism of
functors. -/
theorem injective_map_of_natIso {F G : C ⥤ AddCommGrpCat.{u}} (e : F ≅ G) {A B : C}
    (φ : A ⟶ B) (h : Function.Injective (F.map φ)) : Function.Injective (G.map φ) := by
  rw [← AddCommGrpCat.mono_iff_injective] at h ⊢
  rw [← NatIso.naturality_1 e φ]
  infer_instance

end Functors

variable (X : TopCat.{u})

/-- **Mathlib's sheaf cohomology of a topological space is the right derived functor of global
sections**: `Sheaf.H` (the `Ext`-groups out of the constant sheaf `ℤ`) is naturally isomorphic to
`Hᵖ(X, -) = (sectionsFunctor X ⊤).rightDerived p`. -/
def functorHIsoSectionsRightDerived (p : ℕ) :
    Sheaf.functorH (Opens.grothendieckTopology X) p ≅ (sectionsFunctor X ⊤).rightDerived p :=
  Stacks.Cohomology.SiteSections.functorHIsoRightDerivedSiteSections _ p ≪≫
    ModuleSheafCohomology.rightDerivedIso
      (Stacks.Cohomology.CompositeRightDerived.siteSections_iso_sections _ ⊤ isTerminalTop) p

/-- **Cohomology of a closed subspace is cohomology after pushforward**, as an isomorphism of
functors: for a closed embedding `i : Z ⟶ X`, `Hᵖ(Z, -) ≅ Hᵖ(X, i_* -)` on abelian sheaves
([Stacks, Tag 02UV]), with the pushforward read on site sheaves. -/
def functorHPushforwardIso {Z : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    (p : ℕ) :
    Sheaf.functorH (Opens.grothendieckTopology Z) p ≅
      Stacks.ClosedImmersion.abelianSheafPushforward.{u, u} i ⋙
        Sheaf.functorH (Opens.grothendieckTopology X) p :=
  have h := Stacks.ClosedImmersion.hasCohomologyPushforwardIso_of_isClosedEmbedding.{u, u, u}
    (hExtZ := inferInstance) (hExtX := inferInstance) i hi
  @asIso _ _ _ _ (@Stacks.ClosedImmersion.cohomologyPushforwardComparison.{u, u, u} X Z _ _ _ _ i
    h.preservesFiniteLimits h.preservesFiniteColimits p) (h.isIso p)

/-- **A morphism of abelian sheaves on a closed subspace induces zero in cohomology as soon as its
pushforward does.** For a closed embedding `i : Z ⟶ X` the cohomology of `Z` is the cohomology of
`X` after pushforward, naturally ([Stacks, Tag 02UV]). -/
theorem rightDerived_map_eq_zero_of_pushforward {Z : TopCat.{u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i) {G G' : AbelianSheaf Z} (φ : G ⟶ G') (p : ℕ)
    (h : ((sectionsFunctor X ⊤).rightDerived p).map
      ((Stacks.ClosedImmersion.abelianSheafPushforward.{u, u} i).map φ) = 0) :
    ((sectionsFunctor Z ⊤).rightDerived p).map φ = 0 :=
  map_eq_zero_of_natIso (functorHIsoSectionsRightDerived Z p).symm φ <|
    map_eq_zero_of_natIso (functorHPushforwardIso X i hi p) φ <|
      map_eq_zero_of_natIso (functorHIsoSectionsRightDerived X p)
        ((Stacks.ClosedImmersion.abelianSheafPushforward.{u, u} i).map φ) h

/-- **An epimorphism of abelian sheaves is surjective on top-degree cohomology.** On a
Noetherian space of topological Krull dimension at most `d`, an epimorphism `φ : B ⟶ C` induces
a surjection `Hᵈ(X, B) ⟶ Hᵈ(X, C)`: the cokernel injects into `Hᵈ⁺¹(X, ker φ)`, which vanishes
by Grothendieck's theorem ([Stacks, Tag 02UZ]). -/
theorem surjective_rightDerived_map_of_epi [NoetherianSpace X] {d : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {B C : AbelianSheaf X} (φ : B ⟶ C)
    [Epi φ] : Function.Surjective (((sectionsFunctor X ⊤).rightDerived d).map φ) := by
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ) }
  refine surjective_map_of_natIso (functorHIsoSectionsRightDerived X d) φ fun x => ?_
  have hz : Subsingleton (Sheaf.H.{u, u, u, u} (kernel φ) (d + 1)) :=
    Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
      hdim (Nat.lt_succ_self d) _
  exact Abelian.Ext.covariant_sequence_exact₃ _ hS x rfl (Subsingleton.elim _ _)

section Modules

variable {Y : Type u} [TopologicalSpace Y] (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
  {M N : SheafOfModules.{u} R} (θ : M ⟶ N) (n : ℕ)

/-- **Injectivity on cohomology does not see the module structure** ([Stacks, Tag 01F1]): a
morphism of `R`-modules is injective on `Hⁿ(Y, -)` computed in `R`-modules if and only if it is
injective on `Hⁿ(Y, -)` of the underlying abelian sheaves. -/
theorem injective_rightDerived_evaluation_iff :
    Function.Injective (((SheafOfModules.evaluation R (op ⊤)).rightDerived n).map θ) ↔
      Function.Injective ((((sheafSections (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj (op ⊤)).rightDerived n).map ((SheafOfModules.toSheaf R).map θ)) :=
  ⟨injective_map_of_natIso
      (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso R ⊤ n) θ,
    injective_map_of_natIso
      (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso R ⊤ n).symm θ⟩

/-- **Surjectivity on cohomology does not see the module structure** ([Stacks, Tag 01F1]). -/
theorem surjective_rightDerived_evaluation_iff :
    Function.Surjective (((SheafOfModules.evaluation R (op ⊤)).rightDerived n).map θ) ↔
      Function.Surjective ((((sheafSections (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj (op ⊤)).rightDerived n).map ((SheafOfModules.toSheaf R).map θ)) :=
  ⟨surjective_map_of_natIso
      (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso R ⊤ n) θ,
    surjective_map_of_natIso
      (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso R ⊤ n).symm θ⟩

end Modules

end Stacks.Cohomology.TopDegree
