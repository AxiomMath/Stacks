module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSurjectivityLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AlternatingAffineIntersections
public import StacksFrontier.AlgebraicGeometry.Modules.FreeMapIsoLocus
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# The surjectivity locus of a map of modules, read on a scheme over the algebraic space

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `u : 𝓖 ⟶ 𝓕` be a map of
quasi-coherent `𝒪_X`-modules with `𝓕` of finite type, and let `w : h_U ⟶ X` be a morphism from
the algebraic space represented by a scheme `U` of the site, with underlying scheme `W`. The
pullback `w^*u` is a map of quasi-coherent modules on `h_U`, so it is the image under the
comparison `ε^*` of Stacks 03DX of a map `φ` of quasi-coherent `𝒪_W`-modules. This file proves
that a scheme `U' ⟶ U` over `X` factors through the surjectivity locus of `u` exactly when its
image in `W` misses the support of the cokernel of `φ`.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeSource`, `AlgebraicGeometry.Space.chartSchemeTarget` and
  `AlgebraicGeometry.Space.chartPullbackSchemeMap`: the map `φ` of quasi-coherent
  `𝒪_W`-modules whose image under `ε^*` is `w^*u`.

## Main results

* `AlgebraicGeometry.Space.epi_representedAssociatedModule_map_iff`: `ε^*` preserves and reflects
  epimorphisms between quasi-coherent modules.
* `AlgebraicGeometry.Space.exists_factor_surjectivityLocus_iff_range_subset`: **a scheme
  `r : U' ⟶ U` over `X` factors through the surjectivity locus of `u` exactly when the image of
  `r` lies in the complement of the support of `Coker φ`.**

## Implementation notes

The comparison is carried by `ε^*`, `AlgebraicGeometry.Space.representedAssociatedModule`,
because its compatibility with pullback is available as a *natural* isomorphism,
`AlgebraicGeometry.Space.representedAssociatedModulePullbackFunctorIso`: the test is a statement
about the morphism `(r ≫ w)^*u`, and only a natural comparison carries morphisms along. The map
`φ` is the image of `w^*u` under the inverse of the equivalence
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, so that `ε^*φ` is `w^*u` up
to the counit of that equivalence.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Represented

variable (U : BigFppfOver B S hS)

/-- `ε^*` for a representable algebraic space is a left adjoint: the associated-module functor
of Stacks 03DU followed by the transport along the equivalence of small étale sites. -/
def representedAssociatedModuleSmallEtaleAdjunction :
    representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U) ⊣
      (representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
        SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property :=
  (SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).comp
    (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction

/-- **`ε^*` preserves and reflects epimorphisms between quasi-coherent modules.** -/
theorem epi_representedAssociatedModule_map_iff
    {M N : ((BigFppfOver.toScheme B S hS).obj U).Modules} (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) (φ : M ⟶ N) :
    Epi ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map φ) ↔
      Epi φ := by
  have hpc : PreservesColimitsOfSize.{0, 0}
      (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)) :=
    (representedAssociatedModuleSmallEtaleAdjunction U).leftAdjoint_preservesColimits
  have hc : (cokernel φ).IsQuasicoherent :=
    Stacks.Cech.isQuasicoherent_cokernel_of_isQuasicoherent _ φ hM hN
  rw [Preadditive.epi_iff_isZero_cokernel, Preadditive.epi_iff_isZero_cokernel,
    ← (PreservesCokernel.iso
      (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)) φ).isZero_iff]
  refine ⟨isZero_of_isZero_representedAssociatedModule B S hS U _ _ hc, fun h => ?_⟩
  exact Functor.map_isZero _ h

end Represented

section Chart

variable {X : AlgebraicSpaces B S hS} {𝓖 𝓕 : Modules.{u, u} B S hS X.1 X.2} (u : 𝓖 ⟶ 𝓕)
  [h𝓖 : 𝓖.IsQuasicoherentOnSite] [h𝓕 : 𝓕.IsQuasicoherentOnSite]
  {U : BigFppfOver B S hS} (w : yoneda.obj U ⟶ X.1)

/-- The scheme point `w`, as a morphism of algebraic spaces. -/
abbrev chartSpaceMap :
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X :=
  ObjectProperty.homMk w

/-- The pullback of a quasi-coherent module along `w`, as a quasi-coherent module on `h_U`. -/
def chartPullbackQcoh (𝓜 : Modules.{u, u} B S hS X.1 X.2) [𝓜.IsQuasicoherentOnSite] :
    QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  ⟨(modulePullback B S hS (chartSpaceMap w)).obj 𝓜,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ 𝓜 ‹_›⟩

/-- The quasi-coherent `𝒪_W`-module corresponding to `w^*𝓖`. -/
def chartSchemeSource : ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj (chartPullbackQcoh w 𝓖)).obj

/-- The quasi-coherent `𝒪_W`-module corresponding to `w^*𝓕`. -/
def chartSchemeTarget : ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj (chartPullbackQcoh w 𝓕)).obj

/-- The `𝒪_W`-module `chartSchemeSource w` is quasi-coherent. -/
theorem isQuasicoherent_chartSchemeSource : (chartSchemeSource (𝓖 := 𝓖) w).IsQuasicoherent :=
  ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj
      (chartPullbackQcoh w 𝓖)).property

/-- The `𝒪_W`-module `chartSchemeTarget w` is quasi-coherent. -/
theorem isQuasicoherent_chartSchemeTarget : (chartSchemeTarget (𝓕 := 𝓕) w).IsQuasicoherent :=
  ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj
      (chartPullbackQcoh w 𝓕)).property

/-- The map of quasi-coherent `𝒪_W`-modules corresponding to `w^*u`. -/
def chartPullbackSchemeMap : chartSchemeSource (𝓖 := 𝓖) w ⟶ chartSchemeTarget (𝓕 := 𝓕) w :=
  ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.map
    (ObjectProperty.homMk ((modulePullback B S hS (chartSpaceMap w)).map u) :
      chartPullbackQcoh w 𝓖 ⟶ chartPullbackQcoh w 𝓕)).hom

/-- `ε^*` of the chart map is `w^*u`, up to the counit of the equivalence. -/
theorem representedAssociatedModule_map_chartPullbackSchemeMap :
    (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map
        (chartPullbackSchemeMap u w) ≫
      ((representedQuasicoherentSchemeEquivalence B S hS U).counitIso.app
        (chartPullbackQcoh w 𝓕)).hom.hom =
    ((representedQuasicoherentSchemeEquivalence B S hS U).counitIso.app
        (chartPullbackQcoh w 𝓖)).hom.hom ≫
      (modulePullback B S hS (chartSpaceMap w)).map u :=
  congrArg (fun k => k.hom)
    ((representedQuasicoherentSchemeEquivalence B S hS U).counitIso.hom.naturality
      (ObjectProperty.homMk ((modulePullback B S hS (chartSpaceMap w)).map u) :
        chartPullbackQcoh w 𝓖 ⟶ chartPullbackQcoh w 𝓕))

/-- Epimorphisms are detected up to a commuting square of isomorphisms. -/
theorem epi_iff_of_isIso_comm {C : Type*} [Category* C] {A B A' B' : C} (f : A ⟶ B)
    (g : A' ⟶ B') (e₁ : A ≅ A') (e₂ : B ≅ B') (h : e₁.hom ≫ g = f ≫ e₂.hom) :
    Epi f ↔ Epi g :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff (Arrow.isoMk e₁ e₂ h)

/-- **A scheme over `X` factors through the surjectivity locus exactly when its image misses the
support of the cokernel of the chart map.** For `r : U' ⟶ U`, the composite of `h_r` with
`w : h_U ⟶ X` factors through `AlgebraicGeometry.Space.surjectivityLocus u` if and only if the
image of the underlying morphism of schemes lies in the complement of the support of
`Coker(AlgebraicGeometry.Space.chartPullbackSchemeMap u w)`. -/
theorem exists_factor_surjectivityLocus_iff_range_subset
    (hfin : SheafOfModules.IsFiniteTypeOnSite 𝓕) [(chartSchemeTarget (𝓕 := 𝓕) w).IsFiniteType]
    {U' : BigFppfOver B S hS} (r : U' ⟶ U) :
    (∃ k : yoneda.obj U' ⟶ (surjectivityLocus u).toFunctor,
        k ≫ (surjectivityLocus u).ι = yoneda.map r ≫ w) ↔
      Set.range ((BigFppfOver.toScheme B S hS).map r) ⊆
        (_root_.SheafOfModules.supp (cokernel (chartPullbackSchemeMap u w)))ᶜ := by
  /- The factorization is surjectivity of `(r ≫ w)^*u` (Stacks 09TP at the scheme point), which
  is surjectivity of `h_r^*(w^*u)`, hence of `h_r^*(ε^*φ)`, hence — `ε^*` commuting with pullback
  naturally — of `ε^*(r^*φ)`, hence of `r^*φ`; and `r^*φ` is surjective exactly off the inverse
  image of the support of `Coker φ` (Stacks 056J,
  `AlgebraicGeometry.Scheme.Modules.epi_pullback_map_iff_range_subset`). -/
  rw [exists_factor_surjectivityLocus_iff u hfin (yoneda.map r ≫ w)]
  have hcomp : (ObjectProperty.homMk (yoneda.map r ≫ w) :
      (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X) =
        representedSpaceMap B S hS r ≫ chartSpaceMap w := rfl
  rw [hcomp]
  set h := representedSpaceMap B S hS r
  set wA := chartSpaceMap w
  set E := representedQuasicoherentSchemeEquivalence B S hS U
  -- the composite pullback is the iterated pullback
  have h₁ := epi_iff_of_isIso_comm ((modulePullback B S hS h).map
      ((modulePullback B S hS wA).map u)) ((modulePullback B S hS (h ≫ wA)).map u)
    ((modulePullbackCompIso B S hS h wA).app 𝓖) ((modulePullbackCompIso B S hS h wA).app 𝓕)
    ((modulePullbackCompIso B S hS h wA).hom.naturality u).symm
  -- `w^*u` is `ε^*φ` up to the counit of the equivalence
  have h₂ := epi_iff_of_isIso_comm
    ((modulePullback B S hS h).map
      ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map
        (chartPullbackSchemeMap u w)))
    ((modulePullback B S hS h).map ((modulePullback B S hS wA).map u))
    ((modulePullback B S hS h).mapIso ((ObjectProperty.ι _).mapIso
      (E.counitIso.app (chartPullbackQcoh w 𝓖))))
    ((modulePullback B S hS h).mapIso ((ObjectProperty.ι _).mapIso
      (E.counitIso.app (chartPullbackQcoh w 𝓕))))
    (by
      show (modulePullback B S hS h).map
          ((E.counitIso.app (chartPullbackQcoh w 𝓖)).hom.hom) ≫ _ =
        _ ≫ (modulePullback B S hS h).map ((E.counitIso.app (chartPullbackQcoh w 𝓕)).hom.hom)
      exact ((modulePullback B S hS h).map_comp _ _).symm.trans
        ((congrArg (modulePullback B S hS h).map
          (representedAssociatedModule_map_chartPullbackSchemeMap u w).symm).trans
          ((modulePullback B S hS h).map_comp _ _)))
  -- `ε^*` commutes with pullback, naturally
  have h₃ := epi_iff_of_isIso_comm
    ((modulePullback B S hS h).map
      ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map
        (chartPullbackSchemeMap u w)))
    ((representedAssociatedModule B S hS U' (isAlgebraicSpace_yoneda B S hS U')).map
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
          (chartPullbackSchemeMap u w)))
    ((representedAssociatedModulePullbackFunctorIso B S hS r).app _)
    ((representedAssociatedModulePullbackFunctorIso B S hS r).app _)
    ((representedAssociatedModulePullbackFunctorIso B S hS r).hom.naturality
      (chartPullbackSchemeMap u w)).symm
  have := isQuasicoherent_chartSchemeSource (𝓖 := 𝓖) w
  have := isQuasicoherent_chartSchemeTarget (𝓕 := 𝓕) w
  have h₄ := epi_representedAssociatedModule_map_iff U'
    (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _)
    (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _)
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
        (chartPullbackSchemeMap u w))
  have h₅ := Scheme.Modules.epi_pullback_map_iff_range_subset (chartPullbackSchemeMap u w)
    ((BigFppfOver.toScheme B S hS).map r)
  exact h₁.symm.trans (h₂.symm.trans (h₃.trans (h₄.trans h₅)))

end Chart

end AlgebraicGeometry.Space

end
