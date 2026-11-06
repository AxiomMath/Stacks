module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DiscreteRepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGlobalSectionsCanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationCohomologyNotProjectiveLine
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictionInjectiveAcyclic
public import StacksFrontier.Homology.DerivedIndexing.ExactPrecompositionDelta
public import StacksFrontier.Homology.DerivedIndexing.CompositeUnitSingle
public import StacksFrontier.Homology.DerivedIndexing.NatTransCommShift
public import StacksFrontier.Homology.DerivedIndexing.CoEdgeDelta
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Transport
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology

/-!
# The derived version of `H^i(X_{k̄}, ℱ_ρ) = H^i(π₁(X_{k̄}), M)`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k`, `Λ` a finite ring with `#Λ` invertible in `k`, and assume `X_{k̄} ≇ 𝐏¹_{k̄}`. The
cohomological half of [Stacks, Tag 03VM] identifies `H^i(X_{k̄}, ℱ_ρ)` with
`H^i(π₁(X_{k̄}), M)` as δ-functors of the finite representation `(M, ρ)` of `π₁(X)`; the source
adds "Moreover, in this case there is a derived version too". This file proves the derived
version: a natural isomorphism, in the bounded below derived category of `Λ`-modules,

`RΓ(π₁(X_{k̄}), M) ≅ RΓ(X_{k̄}, ℱ_ρ)`,

where `RΓ(π₁(X_{k̄}), -)` is the right derived functor of the invariants on *all* continuous
discrete `π₁(X_{k̄})`-modules.

## The construction

Write `G = π₁(X_{k̄})` and `Γ = π₁(X)`. The comparison is the image of the degree-zero
identification under the universal property of right derived functors, and it is built on all
continuous discrete `Γ`-modules `N`, where the sheaf `ℱ_N|_{X_{k̄}}` is defined
(`AlgebraicGeometry.discreteRepresentationSheaf`, an exact functor):

* `AlgebraicGeometry.geometricInvariantsToSections` — the degree-zero map
  `N^G ⟶ Γ(X_{k̄}, ℱ_N)`, sending an invariant `n` to the section attached to it on the finite
  `Γ`-stable submodule it spans; on finite modules it is the identification of Tag 03VL;
* restriction to `G` carries injective `Γ`-modules to `G`-acyclic ones
  (`Stacks.ContinuousCohomology.rightDerivedFunctorPlusResCompIso`), so `RΓ(G, res N)` is the
  right derived functor of `N ↦ N^G` on `Γ`-modules;
* `AlgebraicGeometry.geometricDerivedComparison` — `RΓ(G, res N) ⟶ RΓ(X_{k̄}, ℱ_N)`, the
  transformation induced by the degree-zero map followed by the comparison of [Stacks, Tag 05T2]
  of `R(Γ ∘ ℱ)` with `RΓ ∘ ℱ`.

On cohomology the comparison commutes with the connecting morphisms and is the degree-zero
identification in degree zero; both sides being universal δ-functors on finite representations
(the cohomological half of Tag 03VM), it is an isomorphism in every degree, hence an isomorphism
in the derived category.

## Main definitions

* `AlgebraicGeometry.geometricDiscreteSheaf` — `N ↦ ℱ_N|_{X_{k̄}}`.
* `AlgebraicGeometry.geometricInvariantsToSections` — the degree-zero comparison.
* `AlgebraicGeometry.geometricDerivedComparison` — the derived comparison.

## Main results

* `AlgebraicGeometry.isIso_geometricDerivedComparison_app` — it is an isomorphism on finite
  representations.
* `AlgebraicGeometry.geometricDerivedInvariantsIso` — the derived version of the cohomological
  half of Tag 03VM, under exactly the source's hypotheses.
* `AlgebraicGeometry.geometricDerivedSectionsIsoRightDerived` — the same for an arbitrary right
  derived functor of the invariants, with the étale side first.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology

universe u

namespace AlgebraicGeometry

/-- Enough injectives for continuous discrete modules over a fundamental group, pinned at the
module universe of the group: the general instance is indexed by `max u v w`. -/
local instance (priority := 3000) enoughInjectives_continuousModule_etaleFundamentalGroup
    (Λ : Type) [Ring Λ] (G : Type (u + 1)) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u + 1, 0} Λ G

/-- Enough injectives for étale module sheaves, pinned at the coefficient universe. -/
local instance (priority := 3000) enoughInjectives_etaleModules_zero (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ Y) :=
  Stacks.EtaleCohomology.etaleModules_enoughInjectives.{u, 0} Λ Y

section DegreeZero

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (Λ : Type) [Ring Λ]
  [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] (hK : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- **`N ↦ ℱ_N|_{X_K}`**, for continuous discrete `Λ`-`π₁(X)`-modules `N`: the sheaf
`AlgebraicGeometry.discreteRepresentationSheaf` restricted to the base change `X_K`. -/
abbrev geometricDiscreteSheaf :
    Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)) ⥤
      Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) :=
  discreteRepresentationSheaf B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ ⋙
    Stacks.EtaleCohomology.etaleModuleInverseImage.{u, 0} Λ
      (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))

/-- The restriction of a discrete `π₁(X)`-module to `π₁(X_K)`. -/
abbrev geometricRes :
    Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)) ⥤
      Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y) :=
  continuousModuleRes.{0, u + 1, u + 1} Λ (geometricFundamentalGroupMap B X f K hK y)

/-- **`ℱ_N|_{X_K} = ℱ_ρ|_{X_K}` for a finite `N`**, without any choice. -/
def geometricDiscreteSheafιIso :
    finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)) ⋙
        geometricDiscreteSheaf B X Λ f K hK y ≅
      geometricRepresentationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f
        K :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (discreteRepresentationSheafιIso B X _ Λ) _


/-- `Γ(X_K, ℱ_P) ⟶ Γ(X_K, ℱ_N)` for a finite `π₁(X)`-stable submodule `P` of `N`, induced by the
inclusion `ℱ_P ⟶ ℱ_N`. -/
def geometricSectionsIncl (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))
    (P : FiniteStableSubmodule N) :
    (geometricRepresentationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K ⋙
      Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).obj P.toFinite ⟶
    (geometricDiscreteSheaf B X Λ f K hK y ⋙ Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0}
      Λ (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).obj N :=
  (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).map
    ((Stacks.EtaleCohomology.etaleModuleInverseImage.{u, 0} Λ
        (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
      (finiteSubmoduleExtensionIncl
        (representationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ) P))

omit [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)] in
/-- The maps `Γ(X_K, ℱ_P) ⟶ Γ(X_K, ℱ_N)` are compatible with the inclusion `P ≤ P'` of finite
stable submodules of `N`. -/
lemma map_comp_geometricSectionsIncl (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))
    (P P' : FiniteStableSubmodule N) (hPP' : P ≤ P') :
    (geometricRepresentationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K ⋙
      Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).map
        (FiniteStableSubmodule.hom (𝟙 N) P P' fun _ hx ↦ hPP' hx) ≫
      geometricSectionsIncl B X Λ f K hK y N P' = geometricSectionsIncl B X Λ f K hK y N P :=
  (Functor.map_comp _ _ _).symm.trans (congrArg _ ((Functor.map_comp _ _ _).symm.trans
    (congrArg _ (map_comp_finiteSubmoduleExtensionIncl _ P P' hPP'))))

/- `γ` is an identification `M^{π₁(X_K)} = Γ(X_K, ℱ_ρ|_{X_K})` on finite representations, natural
in `ρ` (Tag 03VL in degree zero); at the source's hypotheses it is the canonical one,
`AlgebraicGeometry.geometricInvariantsGlobalSectionsIsoCanonical`. -/
variable (γ : finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y) ≅
      geometricRepresentationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
          Λ f K ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- The maps `P^{π₁(X_K)} ⟶ Γ(X_K, ℱ_N)` through finite stable submodules are compatible with
the inclusions. -/
lemma geometricSectionsIncl_naturality (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))
    (P P' : FiniteStableSubmodule N) (hPP' : P ≤ P') :
    γ.hom.app P.toFinite ≫ geometricSectionsIncl B X Λ f K hK y N P =
      (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).map
          (FiniteStableSubmodule.hom (𝟙 N) P P' fun _ hx ↦ hPP' hx) ≫
        γ.hom.app P'.toFinite ≫ geometricSectionsIncl B X Λ f K hK y N P' :=
  (congrArg (γ.hom.app P.toFinite ≫ ·)
    (map_comp_geometricSectionsIncl B X Λ f K hK y N P P' hPP')).symm.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ geometricSectionsIncl B X Λ f K hK y N P')
        (γ.hom.naturality (FiniteStableSubmodule.hom (𝟙 N) P P' fun _ hx ↦ hPP' hx))).symm.trans
        (Category.assoc _ _ _)))

/-- The invariants of the finite stable submodules of `N` map to those of `N`. -/
def geometricInvariantsCocone (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    Cocone
      (finiteStableSubmoduleDiagram N ⋙
      (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))) where
  pt := (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj N
  ι :=
    { app P := (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).map
        (stableSubmoduleι N P.1 P.2.1)
      naturality _ _ _i :=
        (Functor.map_comp
        (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)) _ _).symm.trans
        ((congrArg
          ((geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))).map
          (continuousModule_hom_ext fun _ ↦ rfl)).trans (Category.comp_id _).symm) }

/-- **`N^{π₁(X_K)}` is the filtered colimit of the invariants of the finite stable submodules
of `N`**, the union of those submodules being `N`. -/
def isColimitGeometricInvariantsCocone (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    IsColimit (geometricInvariantsCocone B X Λ f K hK y N) := by
  haveI : IsFiltered (FiniteStableSubmodule N) := isFiltered_of_directed_le_nonempty _
  haveI : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ
  haveI : PreservesFilteredColimits (forget (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      (forget AddCommGrpCat.{u + 1})
  haveI : ReflectsColimit (finiteStableSubmoduleDiagram N ⋙
      finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
        continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
      (forget (ModuleCat.{u + 1} Λ)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget (ModuleCat.{u + 1} Λ)) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun P a b h ↦ ?_)
  · let P := FiniteStableSubmodule.orbitSpan N {x.1} (Set.finite_singleton _)
    have hx : x.1 ∈ P.1 := FiniteStableSubmodule.subset_orbitSpan N _ _ (Set.mem_singleton _)
    exact
      ⟨P,
      (⟨⟨x.1, hx⟩, fun g ↦ Subtype.ext (x.2 g)⟩ :
      (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj P.toFinite),
      Subtype.ext rfl⟩
  · refine ⟨P, 𝟙 P, ?_⟩
    have h' : (a.1.1 : N.obj.obj.V) = b.1.1 :=
      congrArg (fun z : ((geometricRes B X Λ f K hK y ⋙
        continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj N) ↦
        (z.1 : N.obj.obj.V)) h
    have hab : a = b := Subtype.ext (Subtype.ext h')
    rw [hab]

/-- The sections of `ℱ_N|_{X_K}` attached to the invariants of the finite stable submodules of
`N`: `P^{π₁(X_K)} = Γ(X_K, ℱ_P) ⟶ Γ(X_K, ℱ_N)`. -/
def geometricSectionsCocone (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    Cocone
      (finiteStableSubmoduleDiagram N ⋙
      (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))) where
  pt :=
    (geometricDiscreteSheaf B X Λ f K hK y ⋙ Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0}
      Λ (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).obj N
  ι :=
    { app P := γ.hom.app P.toFinite ≫ geometricSectionsIncl B X Λ f K hK y N P
      naturality P P' i := (geometricSectionsIncl_naturality B X Λ f K hK y γ N P P'
        (leOfHom i)).symm.trans (Category.comp_id _).symm }

omit [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)] in
/-- The maps `Γ(X_K, ℱ_P) ⟶ Γ(X_K, ℱ_N)` are natural in `N`: for `h : N ⟶ N'` carrying `P` into
`Q`, the map through `P` followed by `h` is the map induced by `h` from `P` to `Q` followed by the
map through `Q`. -/
lemma geometricSectionsIncl_comp_map {N N' : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))} (h : N ⟶ N')
    (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) :
    geometricSectionsIncl B X Λ f K hK y N P ≫
      (geometricDiscreteSheaf B X Λ f K hK y ⋙
      Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0}
      Λ (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).map h =
      (geometricRepresentationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f
        K ⋙
      Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).map
          (FiniteStableSubmodule.hom h P Q hPQ) ≫ geometricSectionsIncl B X Λ f K hK y N' Q :=
  (Functor.map_comp _ _ _).symm.trans ((congrArg _ ((Functor.map_comp _ _ _).symm.trans
    (congrArg _ (finiteSubmoduleExtensionIncl_comp_map _ h P Q hPQ)))).trans
      ((congrArg _ (Functor.map_comp _ _ _)).trans (Functor.map_comp _ _ _)))

/-- **The degree-zero comparison `N^{π₁(X_K)} ⟶ Γ(X_K, ℱ_N|_{X_K})`** for continuous discrete
`Λ`-`π₁(X)`-modules `N`: on the invariants of a finite stable submodule `P` it is the
identification `P^{π₁(X_K)} = Γ(X_K, ℱ_P)` of Tag 03VL followed by `ℱ_P ⟶ ℱ_N`. -/
def geometricInvariantsToSections :
    (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)) ⟶
        (geometricDiscreteSheaf B X Λ f K hK y ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0}
      Λ (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) where
  app N := (isColimitGeometricInvariantsCocone B X Λ f K hK y N).desc
    (geometricSectionsCocone B X Λ f K hK y γ N)
  naturality {N N'} h := by
    apply (isColimitGeometricInvariantsCocone B X Λ f K hK y N).hom_ext
    intro P
    have h1 : (geometricInvariantsCocone B X Λ f K hK y N).ι.app P ≫
      (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).map h =
        (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).map
          (FiniteStableSubmodule.hom h P (P.map h) (P.mem_map h)) ≫
          (geometricInvariantsCocone B X Λ f K hK y N').ι.app (P.map h) :=
      (Functor.map_comp
        (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)) _ _).symm.trans
        ((congrArg
        ((geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))).map
        (continuousModule_hom_ext fun _ ↦ rfl)).trans
          (Functor.map_comp
          (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)) _ _))
    refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
    refine ((congrArg (· ≫ _) h1).trans ?_).trans
      (congrArg
      (· ≫
      (geometricDiscreteSheaf B X Λ f K hK y ⋙
      Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0}
      Λ (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).map h)
      ((isColimitGeometricInvariantsCocone B X Λ f K hK y N).fac
        (geometricSectionsCocone B X Λ f K hK y γ N) P)).symm
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((finiteTypeContinuousModuleToRes Λ
        (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).map
          (FiniteStableSubmodule.hom h P (P.map h) (P.mem_map h)) ≫ ·)
      ((isColimitGeometricInvariantsCocone B X Λ f K hK y N').fac
        (geometricSectionsCocone B X Λ f K hK y γ N') (P.map h))).trans ?_
    refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _).symm
    refine (congrArg (· ≫ geometricSectionsIncl B X Λ f K hK y N' (P.map h))
      (γ.hom.naturality (FiniteStableSubmodule.hom h P (P.map h) (P.mem_map h)))).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (γ.hom.app P.toFinite ≫ ·)
      (geometricSectionsIncl_comp_map B X Λ f K hK y h P (P.map h) (P.mem_map h)).symm)

/-- On the invariants of a finite stable submodule `P` of `N`, the degree-zero comparison is
`P^{π₁(X_K)} = Γ(X_K, ℱ_P)` followed by `Γ(X_K, ℱ_P) ⟶ Γ(X_K, ℱ_N)`. -/
lemma geometricInvariantsCocone_ι_comp_geometricInvariantsToSections
    (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))
    (P : FiniteStableSubmodule N) :
    (geometricInvariantsCocone B X Λ f K hK y N).ι.app P ≫
        (geometricInvariantsToSections B X Λ f K hK y γ).app N =
      γ.hom.app P.toFinite ≫ geometricSectionsIncl B X Λ f K hK y N P :=
  (isColimitGeometricInvariantsCocone B X Λ f K hK y N).fac
    (geometricSectionsCocone B X Λ f K hK y γ N) P

/-- **The degree-zero comparison on an element**: an invariant `n` of `N` lying in a finite stable
submodule `P` is sent to the image of `n ∈ P^{π₁(X_K)}` under `P^{π₁(X_K)} = Γ(X_K, ℱ_P)` and
`ℱ_P ⟶ ℱ_N`. -/
lemma geometricInvariantsToSections_app_apply
    (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))
    (P : FiniteStableSubmodule N)
      (n : (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj N)
        (hn : n.1 ∈ P.1) :
    (geometricInvariantsToSections B X Λ f K hK y γ).app N n =
      (γ.hom.app P.toFinite ≫ geometricSectionsIncl B X Λ f K hK y N P)
        (⟨⟨n.1, hn⟩, fun g ↦ Subtype.ext (n.2 g)⟩ :
          (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj
          P.toFinite) := by
  have hc : (geometricInvariantsCocone B X Λ f K hK y N).ι.app P
      (⟨⟨n.1, hn⟩, fun g ↦ Subtype.ext (n.2 g)⟩ :
        (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj
          P.toFinite) = n := Subtype.ext rfl
  exact (congrArg ((geometricInvariantsToSections B X Λ f K hK y γ).app N) hc.symm).trans
    ((ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom
        (geometricInvariantsCocone_ι_comp_geometricInvariantsToSections B X Λ f K hK y γ N P) _))

/-- **On finite modules the degree-zero comparison is the identification of Tag 03VL**: it is
`M^{π₁(X_K)} = Γ(X_K, ℱ_ρ)` followed by `ℱ_ρ = ℱ_M` (`ℱ_M` the extension, `M` finite). -/
lemma geometricInvariantsToSections_app_ι
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    (geometricInvariantsToSections B X Λ f K hK y γ).app M.obj =
      γ.hom.app M ≫ (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).map
        ((Stacks.EtaleCohomology.etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
          ((discreteRepresentationSheafιIso B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
            Λ).inv.app M)) := by
  apply (isColimitGeometricInvariantsCocone B X Λ f K hK y M.obj).hom_ext
  intro P
  refine (geometricInvariantsCocone_ι_comp_geometricInvariantsToSections B X Λ f K hK y γ M.obj
    P).trans ?_
  refine Eq.symm ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) (γ.hom.naturality P.ι)).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (γ.hom.app P.toFinite ≫ ·) ?_)
  have hinc : finiteSubmoduleExtensionIncl
      (representationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ) P =
      (representationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ).map P.ι ≫
        (discreteRepresentationSheafιIso B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
          Λ).inv.app M :=
    (Iso.eq_comp_inv _).2 (finiteSubmoduleExtensionIncl_comp_ιIso_hom _ M P)
  exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ ((Functor.map_comp _ _ _).symm.trans
    (congrArg _ hinc.symm))))

/-- The degree-zero comparison is an isomorphism on finite modules. -/
instance isIso_geometricInvariantsToSections_app_ι
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    IsIso ((geometricInvariantsToSections B X Λ f K hK y γ).app M.obj) := by
  rw [geometricInvariantsToSections_app_ι]
  have : IsIso ((discreteRepresentationSheafιIso B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
      Λ).inv.app M) :=
    ((discreteRepresentationSheafιIso B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ).app
      M).isIso_inv
  have := Functor.map_isIso (Stacks.EtaleCohomology.etaleModuleInverseImage.{u, 0} Λ
    (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)))
    ((discreteRepresentationSheafιIso B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ).inv.app
      M)
  have h2 := Functor.map_isIso (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
    (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    ((Stacks.EtaleCohomology.etaleModuleInverseImage.{u, 0} Λ
      (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
      ((discreteRepresentationSheafιIso B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
        Λ).inv.app M))
  exact IsIso.comp_isIso' inferInstance h2

end DegreeZero

section Derived

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
    Functor.isTriangulated_rightDerivedFunctorPlus

/-- **A morphism of δ-functors whose components are isomorphisms is an isomorphism.** -/
def _root_.CategoryTheory.DeltaFunctor.isoOfIsIsoApp {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] {F G : DeltaFunctor A B} (η : F ⟶ G)
    [∀ n, IsIso (η.app n)] : F ≅ G where
  hom := η
  inv :=
    { app n := (asIso (η.app n)).inv
      comm {S} hS n := by
        change ((asIso (η.app n)).app S.X₃).inv ≫ _ = _ ≫ ((asIso (η.app (n + 1))).app S.X₁).inv
        rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
        exact (η.comm hS n).symm }
  hom_inv_id := DeltaFunctor.hom_ext fun n ↦ (asIso (η.app n)).hom_inv_id
  inv_hom_id := DeltaFunctor.hom_ext fun n ↦ (asIso (η.app n)).inv_hom_id

/-- A δ-functor receiving a morphism from a universal one that is an isomorphism in each degree is
universal. -/
private theorem isUniversal_of_isIso_app {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] {F G : DeltaFunctor A B} (η : F ⟶ G)
    [∀ n, IsIso (η.app n)] (hF : F.IsUniversal) : G.IsUniversal :=
  haveI := hF
  DeltaFunctor.IsUniversal.of_iso (DeltaFunctor.isoOfIsIsoApp η)

/-- The `ℕ`-indexed right derived functors are the `ℤ`-indexed ones, as δ-functors. -/
def _root_.Stacks.DerivedIndexing.rightDerivedDeltaFunctorToPlusDelta {C D : Type*} [Category* C]
    [Category* D] [Abelian C] [Abelian D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive] :
    Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F ⟶
      Stacks.DerivedIndexing.plusDelta F where
  app n := (Stacks.DerivedIndexing.rightDerivedIso F n).hom
  comm {S} hS n := by
    change _ = ((Stacks.DerivedIndexing.rightDerivedIso F n).hom.app S.X₃ ≫
        Stacks.DerivedIndexing.canonicalδ F hS n ≫
        (Stacks.DerivedIndexing.rightDerivedIso F (n + 1)).inv.app S.X₁) ≫
      (Stacks.DerivedIndexing.rightDerivedIso F (n + 1)).hom.app S.X₁
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact congrArg _ (Category.comp_id _).symm

/-- The comparison of the `ℕ`-indexed with the `ℤ`-indexed right derived functors is an
isomorphism in each degree. -/
instance {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    IsIso ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorToPlusDelta F).app n) :=
  inferInstanceAs (IsIso (Stacks.DerivedIndexing.rightDerivedIso F n).hom)

/-- For a left exact functor, `H⁰` of the canonical map `F(X)[0] ⟶ RF(X[0])` is invertible. -/
theorem _root_.Stacks.DerivedIndexing.isIso_homologyFunctor_zero_map_rightDerivedPlusUnitSingle_app
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (X : C) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F).app X)) := by
  have h := (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith).2.2.2 inferInstance X
  show IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
    ((Functor.mapSingleFunctorCompQhIso F).inv.app X ≫
      F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X) ≫
      F.rightDerivedFunctorPlus.map ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X)))
  rw [Functor.map_comp, Functor.map_comp]
  have : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X))) := h
  infer_instance

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (Λ : Type) [Ring Λ]
  [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] (hK : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- Restriction to `π₁(X_K)` is additive. -/
instance additive_geometricRes : (geometricRes B X Λ f K hK y).Additive :=
  additive_continuousModuleRes.{0, u + 1, 0} Λ _

/-- `N ↦ N^{π₁(X_K)}` on continuous discrete `π₁(X)`-modules is additive. -/
instance additive_geometricRes_comp_invariants :
    (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).Additive :=
  additive_continuousModuleRes_comp_invariants.{0, u + 1, 0} Λ _

/-- Restriction to `π₁(X_K)` preserves finite limits. -/
instance preservesFiniteLimits_geometricRes :
    PreservesFiniteLimits (geometricRes B X Λ f K hK y) :=
  preservesFiniteLimits_continuousModuleRes.{0, u + 1, 0} Λ _

/-- Restriction to `π₁(X_K)` preserves finite colimits. -/
instance preservesFiniteColimits_geometricRes :
    PreservesFiniteColimits (geometricRes B X Λ f K hK y) :=
  preservesFiniteColimits_continuousModuleRes.{0, u + 1, 0} Λ _

/-- `N ↦ ℱ_N|_{X_K}` preserves finite limits. -/
instance preservesFiniteLimits_geometricDiscreteSheaf :
    PreservesFiniteLimits (geometricDiscreteSheaf B X Λ f K hK y) :=
  @Limits.comp_preservesFiniteLimits _ _ _ _ _ _ _ _
    (preservesFiniteLimits_discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ)
    (Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ
      (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)))

/-- `N ↦ ℱ_N|_{X_K}` preserves finite colimits. -/
instance preservesFiniteColimits_geometricDiscreteSheaf :
    PreservesFiniteColimits (geometricDiscreteSheaf B X Λ f K hK y) :=
  @Limits.comp_preservesFiniteColimits _ _ _ _ _ _ _ _
    (preservesFiniteColimits_discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ)
    (Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits.{u, 0} Λ
      (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)))

/-- `N ↦ ℱ_N|_{X_K}` is additive. -/
instance additive_geometricDiscreteSheaf : (geometricDiscreteSheaf B X Λ f K hK y).Additive :=
  Functor.additive_of_preserves_binary_products _

variable [IsAlgClosure k K] [CompactSpace X.1] [QuasiSeparatedSpace X.1]

variable (γ : finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y) ≅
      geometricRepresentationSheaf.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
          Λ f K ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- The transformation `R(res) ⋙ R(inv) ⟶ R(Γ ∘ ℱ)`: the inverse of the composition isomorphism
of restriction and invariants (restriction carries injectives to acyclics), followed by the
transformation induced by the degree-zero comparison. -/
def geometricDerivedTrans :
    (geometricRes B X Λ f K hK y).rightDerivedFunctorPlus ⋙
      (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
        y)).rightDerivedFunctorPlus ⟶
      (geometricDiscreteSheaf B X Λ f K hK y ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusResCompIso.{0, u + 1, 0} Λ (geometricFundamentalGroupMap B X f K hK y)
      (isInducing_geometricFundamentalGroupMap B X f K hK y)).inv ≫
    Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
      (geometricInvariantsToSections B X Λ f K hK y γ)

/-- The transformation `geometricDerivedTrans` commutes with the shifts by `ℤ`. -/
instance : NatTrans.CommShift (geometricDerivedTrans B X Λ f K hK y γ) ℤ := by
  have : NatTrans.CommShift (rightDerivedFunctorPlusResCompIso.{0, u + 1, 0} Λ
      (geometricFundamentalGroupMap B X f K hK y)
      (isInducing_geometricFundamentalGroupMap B X f K hK y)).hom ℤ :=
    Stacks.DerivedIndexing.natTransCommShift_rightDerivedPlusCompTrans
      (geometricRes B X Λ f K hK y) (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
  have := Stacks.DerivedIndexing.natTransCommShift_rightDerivedFunctorPlusNatTrans
    (geometricInvariantsToSections B X Λ f K hK y γ)
  exact NatTrans.CommShift.comp _ _ ℤ

/-- **The derived comparison `RΓ(π₁(X_K), res N) ⟶ RΓ(X_K, ℱ_N|_{X_K})`** at a continuous discrete
`Λ`-`π₁(X)`-module `N`. -/
def geometricDerivedComparisonApp
    (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
        y)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((geometricRes B X Λ f K hK y).obj N)) ⟶
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((geometricDiscreteSheaf B X Λ f K hK y).obj N)) :=
  Stacks.DerivedIndexing.derivedPairMap (geometricRes B X Λ f K hK y)
    (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
      (geometricDiscreteSheaf B X Λ f K hK y ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) (geometricDerivedTrans B X Λ f K hK y γ)
      (𝟙 ((geometricRes B X Λ f K hK y).obj N)) ≫
    Stacks.DerivedIndexing.exactPrecompMap (geometricDiscreteSheaf B X Λ f K hK y)
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) N

/-- **The derived comparison `RΓ(π₁(X_K), res N) ⟶ RΓ(X_K, ℱ_N|_{X_K})`**, natural in the
continuous discrete `Λ`-`π₁(X)`-module `N`. -/
def geometricDerivedComparison :
    geometricRes B X Λ f K hK y ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
        y)).rightDerivedFunctorPlus ⟶
      geometricDiscreteSheaf B X Λ f K hK y ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerivedFunctorPlus where
  app N := geometricDerivedComparisonApp B X Λ f K hK y γ N
  naturality {N N'} h :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ Stacks.DerivedIndexing.exactPrecompMap (geometricDiscreteSheaf B X Λ f K hK y)
          (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) N')
        (Stacks.DerivedIndexing.derivedPairMap_naturality (geometricRes B X Λ f K hK y)
          (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
          (geometricDiscreteSheaf B X Λ f K hK y ⋙
            Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) (geometricDerivedTrans B X Λ f K hK y γ)
          (𝟙 _) (𝟙 _) ((geometricRes B X Λ f K hK y).map h) h
          ((Category.comp_id _).trans (Category.id_comp _).symm))).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg
          (Stacks.DerivedIndexing.derivedPairMap (geometricRes B X Λ f K hK y)
          (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
          (geometricDiscreteSheaf B X Λ f K hK y ⋙
            Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) (geometricDerivedTrans B X Λ f K hK y γ)
          (𝟙 ((geometricRes B X Λ f K hK y).obj N)) ≫ ·)
          (Stacks.DerivedIndexing.exactPrecompMap_naturality
            (geometricDiscreteSheaf B X Λ f K hK y)
              (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) h)).trans
        (Category.assoc _ _ _).symm

/-- **The derived comparison commutes with the connecting morphisms**: on cohomology it is a
morphism from `M ↦ Hⁱ(π₁(X_K), res M)` to `M ↦ Hⁱ(X_K, ℱ_M|_{X_K})`. -/
theorem canonicalδ_comp_geometricDerivedComparisonApp
    {S : ShortComplex (Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))}
    (hS : S.ShortExact) (q : ℕ) :
    Stacks.DerivedIndexing.canonicalδ (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
        (hS.map_of_exact (geometricRes B X Λ f K hK y)) q ≫
        (DerivedCategory.Plus.homologyFunctor _ ((q + 1 : ℕ) : ℤ)).map
          (geometricDerivedComparisonApp B X Λ f K hK y γ S.X₁) =
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (geometricDerivedComparisonApp B X Λ f K hK y γ S.X₃) ≫
        Stacks.DerivedIndexing.canonicalδ (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
          (hS.map_of_exact (geometricDiscreteSheaf B X Λ f K hK y)) q := by
  have h1 := Stacks.DerivedIndexing.canonicalδ_comp_derivedPairMap (geometricRes B X Λ f K hK y)
    (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
        (geometricDiscreteSheaf B X Λ f K hK y ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    (geometricDerivedTrans B X Λ f K hK y γ) (hS.map_of_exact (geometricRes B X Λ f K hK y)) hS
    (𝟙 _) q
  have h2 := Stacks.DerivedIndexing.canonicalδ_comp_exactPrecompMap
    (geometricDiscreteSheaf B X Λ f K hK y)
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) hS q
  exact (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) h1).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) h2).trans <| (Category.assoc _ _ _).symm.trans <|
        congrArg (· ≫ _) (Functor.map_comp _ _ _).symm

/-- Restriction of finite representations from `π₁(X)` to `π₁(X_K)` preserves finite limits. -/
instance preservesFiniteLimits_finiteTypeContinuousModuleToRes_geometric :
    PreservesFiniteLimits
      (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y)) :=
  haveI := forall_finite_finiteEtaleFiberFunctor_obj y
  haveI := forall_finite_finiteEtaleFiberFunctor_obj (y.map (fieldBaseChangeObjProj B X f K hK).hom)
  preservesFiniteLimits_finiteTypeContinuousModuleToRes Λ _

/-- Restriction of finite representations from `π₁(X)` to `π₁(X_K)` preserves finite colimits. -/
instance preservesFiniteColimits_finiteTypeContinuousModuleToRes_geometric :
    PreservesFiniteColimits
      (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y)) :=
  haveI := forall_finite_finiteEtaleFiberFunctor_obj y
  haveI := forall_finite_finiteEtaleFiberFunctor_obj (y.map (fieldBaseChangeObjProj B X f K hK).hom)
  preservesFiniteColimits_finiteTypeContinuousModuleToRes Λ _

/-- The inclusion of finite representations of `π₁(X)` into continuous discrete modules preserves
finite limits. -/
instance preservesFiniteLimits_finiteTypeContinuousModuleι_geometric :
    PreservesFiniteLimits (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :=
  haveI : IsArtinianRing Λ := IsArtinianRing.of_finite Λ Λ
  preservesFiniteLimits_finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ _

/-- The inclusion of finite representations of `π₁(X)` into continuous discrete modules preserves
finite colimits. -/
instance preservesFiniteColimits_finiteTypeContinuousModuleι_geometric :
    PreservesFiniteColimits (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :=
  haveI : IsArtinianRing Λ := IsArtinianRing.of_finite Λ Λ
  preservesFiniteColimits_finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ _

/-- `M ↦ ℱ_M|_{X_K}` on finite representations of `π₁(X)` preserves finite limits. -/
instance preservesFiniteLimits_ι_comp_geometricDiscreteSheaf :
    PreservesFiniteLimits (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)) ⋙
        geometricDiscreteSheaf B X Λ f K hK y) :=
  haveI : IsArtinianRing Λ := IsArtinianRing.of_finite Λ Λ
  haveI := preservesFiniteLimits_finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
    (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))
  comp_preservesFiniteLimits _ _

/-- `M ↦ ℱ_M|_{X_K}` on finite representations of `π₁(X)` preserves finite colimits. -/
instance preservesFiniteColimits_ι_comp_geometricDiscreteSheaf :
    PreservesFiniteColimits (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)) ⋙
        geometricDiscreteSheaf B X Λ f K hK y) :=
  haveI : IsArtinianRing Λ := IsArtinianRing.of_finite Λ Λ
  haveI := preservesFiniteColimits_finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
    (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))
  comp_preservesFiniteColimits _ _

/-- `M ↦ ℱ_M|_{X_K}` on finite representations of `π₁(X)` is additive. -/
instance additive_ι_comp_geometricDiscreteSheaf :
    (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)) ⋙
        geometricDiscreteSheaf B X Λ f K hK y).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The source δ-functor: `M ↦ Hⁱ(π₁(X_K), res M)` on finite representations, read in the
bounded below derived category. -/
abbrev geometricDerivedSourceDelta : DeltaFunctor (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))
        (ModuleCat.{u + 1} Λ) :=
  (Stacks.DerivedIndexing.plusDelta (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))).precomp
        (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y))

/-- The target δ-functor: `M ↦ Hⁱ(X_K, ℱ_M|_{X_K})` on finite representations. -/
abbrev geometricDerivedTargetDelta : DeltaFunctor (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))
        (ModuleCat.{u + 1} Λ) :=
  (Stacks.DerivedIndexing.plusDelta (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))).precomp
        (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)) ⋙
        geometricDiscreteSheaf B X Λ f K hK y)

/-- **The derived comparison on cohomology**, as a morphism of δ-functors on finite
representations. -/
def geometricDerivedComparisonDelta :
    geometricDerivedSourceDelta B X Λ f K hK y ⟶ geometricDerivedTargetDelta B X Λ f K hK y where
  app n :=
    { app M := (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map
        ((geometricDerivedComparison B X Λ f K hK y γ).app
          ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M))
      naturality _M _M' h :=
        ((DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map_comp _ _).symm.trans <|
          (congrArg (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map
            ((geometricDerivedComparison B X Λ f K hK y γ).naturality
              ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).map h))).trans
          ((DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map_comp _ _) }
  comm {_S} hS n := (canonicalδ_comp_geometricDerivedComparisonApp B X Λ f K hK y γ
    (hS.map_of_exact (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom)))) n).symm

/-- The source δ-functor is universal: it is `M ↦ Hⁱ(π₁(X_K), res M)`, universal because
`π₁(X_K) → π₁(X)` is an embedding (Tag 0BTX). -/
theorem isUniversal_geometricDerivedSourceDelta :
    (geometricDerivedSourceDelta B X Λ f K hK y).IsUniversal :=
  let η := DeltaFunctor.precompHom
    (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f K hK y))
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorToPlusDelta
        (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)))
  have : ∀ n, IsIso (η.app n) := fun n ↦ by
    show IsIso
      (Functor.whiskerLeft _
      (Stacks.DerivedIndexing.rightDerivedIso (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)) n).hom)
    infer_instance
  isUniversal_of_isIso_app η (isUniversal_geometricGroupCohomology B X Λ f K hK y)

omit [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)] [IsAlgClosure k K]
  [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- The target δ-functor is universal as soon as `M ↦ Hⁱ(X_K, ℱ_M)` is. -/
theorem isUniversal_geometricDerivedTargetDelta
    (hT : (geometricRepresentationCohomology.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K).IsUniversal) :
    (geometricDerivedTargetDelta B X Λ f K hK y).IsUniversal := by
  have := preservesFiniteLimits_geometricRepresentationSheaf.{u, 0} B X
    (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K
  have := preservesFiniteColimits_geometricRepresentationSheaf.{u, 0} B X
    (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K
  let η := DeltaFunctor.precompHom (geometricRepresentationSheaf.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K)
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorToPlusDelta
        (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))) ≫
    DeltaFunctor.precompNatTrans
      (Stacks.DerivedIndexing.plusDelta (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)))
      (geometricDiscreteSheafιIso B X Λ f K hK y).inv
  have : ∀ n, IsIso (η.app n) := fun n ↦ by
    show IsIso
      (Functor.whiskerLeft _
      (Stacks.DerivedIndexing.rightDerivedIso
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) n).hom ≫
      Functor.whiskerRight (geometricDiscreteSheafιIso B X Λ f K hK y).inv _)
    infer_instance
  exact isUniversal_of_isIso_app η hT

/-- **In degree zero the derived comparison is the degree-zero comparison**: the canonical map
`N^{π₁(X_K)}[0] ⟶ RΓ(π₁(X_K), res N)` followed by the derived comparison is the degree-zero
comparison followed by the canonical map `Γ(X_K, ℱ_N)[0] ⟶ RΓ(X_K, ℱ_N)`. -/
theorem rightDerivedPlusUnitSingle_comp_geometricDerivedComparisonApp
    (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
      (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))).app
        ((geometricRes B X Λ f K hK y).obj N) ≫
        geometricDerivedComparisonApp B X Λ f K hK y γ N =
      (DerivedCategory.Plus.singleFunctor _ 0).map
          ((geometricInvariantsToSections B X Λ f K hK y γ).app N) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
          (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))).app
        ((geometricDiscreteSheaf B X Λ f K hK y).obj N) := by
  have h₁ := Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_compTrans
    (geometricRes B X Λ f K hK y) (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)) N
  have h₂ := Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_natTrans
    (geometricInvariantsToSections B X Λ f K hK y γ) N
  have h₃ := Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_compTrans
    (geometricDiscreteSheaf B X Λ f K hK y)
    (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) N
  dsimp only [geometricDerivedComparisonApp, Stacks.DerivedIndexing.derivedPairMap,
    Stacks.DerivedIndexing.exactPrecompMap, geometricDerivedTrans]
  have h₁' : (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
      (geometricRes B X Λ f K hK y ⋙ continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))).app N ≫
        (rightDerivedFunctorPlusResCompIso.{0, u + 1, 0} Λ
          (geometricFundamentalGroupMap B X f K hK y)
          (isInducing_geometricFundamentalGroupMap B X f K hK y)).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N) =
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
        (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))).app
          ((geometricRes B X Λ f K hK y).obj N) ≫
        (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
        y)).rightDerivedFunctorPlus.map
          ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (geometricRes B X Λ f K hK y)).app
            N) :=
    h₁
  rw [CategoryTheory.Functor.map_id, Category.id_comp, NatTrans.comp_app]
  simp only [Category.assoc]
  rw
    [← Category.assoc
    ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
    (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))).app _), ← h₁',
    Category.assoc, Iso.hom_inv_id_app_assoc, ← Category.assoc _
      ((Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans _).app _), h₂, Category.assoc, ←
      Category.assoc _
      ((Stacks.DerivedIndexing.rightDerivedPlusCompTrans _ _).app _), h₃, Category.assoc,
    ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- In degree zero the comparison is an isomorphism on finite representations. -/
theorem isIso_geometricDerivedComparisonDelta_app_zero :
    IsIso ((geometricDerivedComparisonDelta B X Λ f K hK y γ).app 0) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M ↦ ?_)
  have hfac := rightDerivedPlusUnitSingle_comp_geometricDerivedComparisonApp B X Λ f K hK y γ
    ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M)
  have h1 := Stacks.DerivedIndexing.isIso_homologyFunctor_zero_map_rightDerivedPlusUnitSingle_app
    (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
        ((geometricRes B X Λ f K hK y).obj ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M))
  have h2 := Stacks.DerivedIndexing.isIso_homologyFunctor_zero_map_rightDerivedPlusUnitSingle_app
    (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
        ((geometricDiscreteSheaf B X Λ f K hK y).obj
        ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M))
  have h3 : IsIso
    ((geometricInvariantsToSections B X Λ f K hK y γ).app
    ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M)) :=
    isIso_geometricInvariantsToSections_app_ι B X Λ f K hK y γ M
  have h4 : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((geometricInvariantsToSections B X Λ f K hK y γ).app
            ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M)) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
          (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))).app
          ((geometricDiscreteSheaf B X Λ f K hK y).obj
            ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M)))) := by
    rw [Functor.map_comp]
    exact IsIso.comp_isIso' inferInstance h2
  rw [← hfac, Functor.map_comp] at h4
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 h4

/-- **The comparison is an isomorphism of δ-functors on finite representations**, as soon as
`M ↦ Hⁱ(X_K, ℱ_M)` is universal: both sides are universal δ-functors and the comparison is an
isomorphism in degree zero. -/
theorem isIso_geometricDerivedComparisonDelta_app
    (hT : (geometricRepresentationCohomology.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K).IsUniversal) (n : ℕ) :
    IsIso ((geometricDerivedComparisonDelta B X Λ f K hK y γ).app n) := by
  have := isUniversal_geometricDerivedSourceDelta B X Λ f K hK y
  have := isUniversal_geometricDerivedTargetDelta B X Λ f K hK y hT
  have := isIso_geometricDerivedComparisonDelta_app_zero B X Λ f K hK y γ
  let e := DeltaFunctor.IsUniversal.isoOfIso (asIso ((geometricDerivedComparisonDelta
    B X Λ f K hK y γ).app 0))
  have h : geometricDerivedComparisonDelta B X Λ f K hK y γ = e.hom :=
    DeltaFunctor.IsUniversal.hom_ext_zero _ (DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero
      (asIso ((geometricDerivedComparisonDelta B X Λ f K hK y γ).app 0))).symm
  rw [h]
  exact ⟨⟨e.inv.app n, congrArg (fun η ↦ DeltaFunctor.Hom.app η n) e.hom_inv_id,
    congrArg (fun η ↦ DeltaFunctor.Hom.app η n) e.inv_hom_id⟩⟩

/-- **The derived comparison is an isomorphism on finite representations**, as soon as
`M ↦ Hⁱ(X_K, ℱ_M)` is universal. -/
theorem isIso_geometricDerivedComparison_app
    (hT : (geometricRepresentationCohomology.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ f K).IsUniversal)
        (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))) :
    IsIso
      ((geometricDerivedComparison B X Λ f K hK y γ).app
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M)) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  cases n with
  | ofNat m =>
    have := isIso_geometricDerivedComparisonDelta_app B X Λ f K hK y γ hT m
    exact NatIso.isIso_app_of_isIso ((geometricDerivedComparisonDelta B X Λ f K hK y γ).app m) M
  | negSucc m =>
    have h1 := Functor.isZero_rightDerivedPlus_of_neg
      (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y))
      ((geometricRes B X Λ f K hK y).obj ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M))
        (Int.negSucc m) (Int.negSucc_lt_zero m)
    have h2 := Functor.isZero_rightDerivedPlus_of_neg
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
      ((geometricDiscreteSheaf B X Λ f K hK y).obj ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj M))
        (Int.negSucc m) (Int.negSucc_lt_zero m)
    exact ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩

end Derived

section SourceHypotheses

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] (Λ : Type) [Ring Λ] [Finite Λ]


/-- **`M^{π₁(X_{k̄})} = Γ(X_{k̄}, ℱ_ρ)`, canonically** (Tag 03VL in degree zero): evaluation at the
geometric point, `AlgebraicGeometry.geometricGlobalSectionsInvariantsEquiv`, read with the
invariants of the restriction as continuous discrete modules. It involves no choice and is
Galois-equivariant (`AlgebraicGeometry.geometricGlobalSectionsInvariantsEquiv_galois`). -/
def geometricInvariantsGlobalSectionsIsoCanonical
    (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    finiteTypeContinuousModuleToRes Λ
      (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y) ⋙
        continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y) ≅
      geometricRepresentationSheaf.{u, 0} B X
          (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
            Λ f K ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI : Fintype Λ := Fintype.ofFinite Λ
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  continuousModuleInvariantsResIso Λ
    (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y) ≪≫
    (NatIso.ofComponents
      (fun ρ ↦ (geometricGlobalSectionsInvariantsEquiv B X f K Λ y ρ).toModuleIso)
      (fun {_ρ _ρ'} φ ↦ ModuleCat.hom_ext (LinearMap.ext fun z ↦ Subtype.ext
        (geometricGlobalSectionsInvariantsEquiv_naturality B X f K Λ y φ z)))).symm

/-- **The canonical identification is Galois-equivariant**: for `γ ∈ π₁(X)` with image `σ` in
`Aut(k̄/k)`, the invariant attached to `σ` applied to a global section is `ρ(γ)` applied to the
invariant attached to the section. -/
theorem geometricInvariantsGlobalSectionsIsoCanonical_inv_galois
    (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).obj
          ((geometricRepresentationSheaf.{u, 0} B X
            (y.map
              (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ
              f K).obj ρ))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    (((geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).inv.app ρ
        ((Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) K
          (geometricQuotientGaloisEquiv B X f K y (QuotientGroup.mk γ))
          ((representationSheaf.{u, 0} B X
            (y.map
              (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
              Λ).obj ρ)) z)).1 : ρ.obj.obj.obj.V) =
      (ρ.obj.obj.obj.ρ γ).asHom.hom
        ((geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).inv.app ρ z).1 := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  let : Fintype Λ := Fintype.ofFinite Λ
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  exact geometricGlobalSectionsInvariantsEquiv_galois B X f K Λ y ρ γ z

attribute [irreducible] geometricInvariantsGlobalSectionsIsoCanonical

/-- **The derived version of `H^i(X_{k̄}, ℱ_ρ) = H^i(π₁(X_{k̄}), M)`** ([Stacks, Tag 03VM],
"Moreover, in this case there is a derived version too"): for a geometrically connected smooth
curve `X` over `k`, `k̄` an algebraic closure of `k`, `Λ` a finite ring with `#Λ` invertible in
`k`, and `X_{k̄} ≇ 𝐏¹_{k̄}`, there is an isomorphism

`RΓ(π₁(X_{k̄}), M) ≅ RΓ(X_{k̄}, ℱ_ρ)`

in the bounded below derived category of `Λ`-modules, natural in the finite `Λ`-module `M` with
continuous action `ρ` of `π₁(X)`. Here `RΓ(π₁(X_{k̄}), -)` is the right derived functor of the
invariants on all continuous discrete `π₁(X_{k̄})`-modules, and `RΓ(X_{k̄}, -)` that of global
sections on `(X_{k̄})_{étale}`. The source's hypotheses and nothing else. -/
@[stacks 03VM "sixth assertion (the derived version of the cohomological half): `RΓ(π₁(X_k̄, \
η̄), M) ≅ RΓ(X_k̄, ℱ_ρ)`, natural in `(M, ρ)`"]
def geometricDerivedInvariantsIso
    (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    finiteTypeContinuousModuleToRes Λ
        (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y) ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
            y)).rightDerivedFunctorPlus ≅
      geometricRepresentationSheaf.{u, 0} B X
          (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
          Λ f K ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerivedFunctorPlus :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := QuasiCompact.compactSpace_of_compactSpace f
  letI := quasiSeparatedSpace_of_quasiSeparated f
  have hT := isUniversal_geometricRepresentationCohomology_of_not_iso_projectiveLine B X f K Λ y
    hΛ hP
  haveI : IsIso (Functor.whiskerLeft (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
      (geometricDerivedComparison B X Λ f K (contains_fieldBaseChange_of_isCurve B X f K) y
        (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y))) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ isIso_geometricDerivedComparison_app B X Λ f K
      (contains_fieldBaseChange_of_isCurve B X f K) y
        (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y) hT M
  asIso (Functor.whiskerLeft (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
      (geometricDerivedComparison B X Λ f K (contains_fieldBaseChange_of_isCurve B X f K) y
        (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y))) ≪≫
    Functor.isoWhiskerRight (geometricDiscreteSheafιIso B X Λ f K
      (contains_fieldBaseChange_of_isCurve B X f K) y)
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerivedFunctorPlus)

/-- **The derived version of the cohomological half of [Stacks, Tag 03VM], for an arbitrary right
derived functor of the invariants**: under the source's hypotheses, for every right derived
functor `R` of `M ↦ M^{π₁(X_{k̄})}` on continuous discrete `Λ`-`π₁(X_{k̄})`-modules (in the
Kan-extension sense), there is a natural isomorphism, in the bounded below derived category of
`Λ`-modules, between `RΓ(X_{k̄}, ℱ_ρ)` and `R(res M)`, natural in the finite representation
`(M, ρ)` of `π₁(X)`. -/
def geometricDerivedSectionsIsoRightDerived
    (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))
    (R : letI := connectedSpace_fieldBaseChange f K
      DerivedCategory.Plus (Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Λ))
    (α : letI := connectedSpace_fieldBaseChange f K
      (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
          y)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ R)
    [hR : letI := connectedSpace_fieldBaseChange f K;
      R.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso _)] :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    geometricRepresentationSheaf.{u, 0} B X
          (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
          Λ f K ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerivedFunctorPlus ≅
      finiteTypeContinuousModuleToRes Λ
          (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y) ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙ R :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  (geometricDerivedInvariantsIso B X f K Λ y hΛ hP).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.rightDerivedUnique _ R
        (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
            y)).rightDerivedFunctorPlusUnith α (HomotopyCategory.Plus.quasiIso _)))

end SourceHypotheses

end AlgebraicGeometry

/-! ### The fourth and fifth assertions of 03VM

Both are proved in `GeometricRepresentationCohomologyNotProjectiveLine`, under exactly the
source's hypotheses. -/

add_to_stacks 03VM "fifth assertion: `H^i(X_k̄, ℱ_ρ) = H^i(π₁(X_k̄, η̄), M)`, the comparison of \
δ-functors being an isomorphism"
  AlgebraicGeometry.isIso_geometricComparison_of_not_iso_projectiveLine

add_to_stacks 03VM "fourth assertion: `(M, ρ) ↦ H^i(X_k̄, ℱ_ρ)` is a universal δ-functor, i.e. the \
right derived functors of `(M, ρ) ↦ M^{π₁(X_k̄, η̄)}`"
  AlgebraicGeometry.isUniversal_geometricRepresentationCohomology_of_not_iso_projectiveLine

end
