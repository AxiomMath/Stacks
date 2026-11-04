module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineBiduality
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingModelSliceSite
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Affine

/-!
# Biduality for complexes with coherent cohomology on a locally Noetherian scheme

Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X` and `L` an object of
`D(𝒪_X)` all of whose cohomology sheaves are coherent. The biduality morphism of
[Stacks, Tag 0A89]

`L ⟶ R𝓗om(R𝓗om(L, K), K)`

is an isomorphism. Over an affine open `V` the restrictions of `K` and `L` are the complexes
associated to a dualizing complex and to a complex with finite cohomology over `Γ(X, V)`
([Stacks, Tag 06Z0]), where biduality holds by
`Stacks.Duality.isIso_derivedBiduality_derivedTilde`; invertibility is local.

## Main results

* `Stacks.Duality.exists_finite_iso_restrictFunctor_of_isCoherent`: over an affine open, an
  object with coherent cohomology is associated to a complex with finite cohomology modules.
* `Stacks.Duality.isIso_derivedBiduality_of_isDualizingComplex`: the biduality morphism is an
  isomorphism.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor
  Stacks.DerivedQCoh.preservesFiniteLimits_restrictFunctor

namespace Stacks.Duality

/-- Restricting along an open immersion from a locally Noetherian scheme preserves coherence of
all cohomology sheaves. -/
private theorem isCoherent_homology_mapDerivedCategory_restrictFunctor {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (g : X ⟶ Y) [IsOpenImmersion g] (L : DerivedCategory Y.Modules)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj L).IsCoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj L)).IsCoherent :=
  isCoherent_of_modulesIso
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor g) i).app L).symm
    (isCoherent_restrict_of_isOpenImmersion g _ (hL i))

/-- **Affine models of objects with coherent cohomology.** Over an affine open `V` of a locally
Noetherian scheme, an object of `D(𝒪_X)` with coherent cohomology sheaves restricts to the
complex associated to an object of `D(Γ(X, V))` with finite cohomology modules, transported along
`V ≅ Spec Γ(X, V)`. -/
theorem exists_finite_iso_restrictFunctor_of_isCoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V : X.Opens) (hV : IsAffineOpen V) (L : DerivedCategory X.Modules)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) :
    ∃ M : DerivedCategory (ModuleCat.{u} Γ(X, V)),
      (∀ i : ℤ, Module.Finite Γ(X, V)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, V)) i).obj M)) ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj L ≅
        (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
          ((tilde.functor Γ(X, V)).mapDerivedCategory.obj M)) := by
  have hR : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let L₁ := (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj L
  let L₂ := (Scheme.Modules.restrictFunctor hV.isoSpec.inv).mapDerivedCategory.obj L₁
  have hL₁ := isCoherent_homology_mapDerivedCategory_restrictFunctor V.ι L hL
  have hL₂ := isCoherent_homology_mapDerivedCategory_restrictFunctor hV.isoSpec.inv L₁ hL₁
  obtain ⟨M, ⟨e⟩⟩ := StandardModel.exists_iso_mapDerivedCategory Γ(X, V) L₂ fun n =>
    have := hL₂ n
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((DerivedCategory.homologyFunctor (Spec Γ(X, V)).Modules n).obj L₂)).1
  refine ⟨M, fun i => finite_homology_of_isCoherent_homology_tilde Γ(X, V) M i
    (isCoherent_of_modulesIso
      ((DerivedCategory.homologyFunctor (Spec Γ(X, V)).Modules i).mapIso e.symm) (hL₂ i)), ⟨?_⟩⟩
  let F := Scheme.Modules.restrictFunctor hV.isoSpec.inv
  let G := Scheme.Modules.restrictFunctor hV.isoSpec.hom
  exact ((Stacks.DerivedGlueing.mapDerivedCategoryCongr
        ((Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.isoSpec.inv).symm ≪≫
          Scheme.Modules.restrictFunctorCongr hV.isoSpec.hom_inv_id ≪≫
          Scheme.Modules.restrictFunctorId)).app L₁ ≪≫
        (Stacks.Homology.mapDerivedCategoryIdIso).app L₁).symm ≪≫
    ((Stacks.DerivedGlueing.mapDerivedCategoryCompIso F G).app L₁).symm ≪≫
    G.mapDerivedCategory.mapIso e.symm

/-- **Affine models of objects with coherent cohomology, on the slice site.** The form of
`exists_finite_iso_restrictFunctor_of_isCoherent` read through `overEquiv V`. -/
theorem exists_finite_iso_overFunctor_of_isCoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V : X.Opens) (hV : IsAffineOpen V) (L : DerivedCategory X.Modules)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) :
    ∃ M : DerivedCategory (ModuleCat.{u} Γ(X, V)),
      (∀ i : ℤ, Module.Finite Γ(X, V)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, V)) i).obj M)) ∧
      Nonempty (((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf V).mapDerivedCategory.obj L) ≅
        (tilde.functor Γ(X, V) ⋙
          Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj M) := by
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := X.ringCatSheaf) V
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := X.ringCatSheaf) V
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_finite_iso_restrictFunctor_of_isCoherent V hV L hL
  exact ⟨M, hM, ⟨(Stacks.SheafOfModules.derivedOverFunctorEquiv V).app L ≪≫ e ≪≫
    ((Dualizing.mapDerivedCategoryComp (tilde.functor Γ(X, V))
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom)).app M).symm⟩⟩

/-- **Biduality on a locally Noetherian scheme.** For a dualizing complex `K` on a locally
Noetherian scheme `X` and an object `L` of `D(𝒪_X)` with coherent cohomology sheaves, the
biduality morphism `L ⟶ R𝓗om(R𝓗om(L, K), K)` is an isomorphism. -/
theorem isIso_derivedBiduality_of_isDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    (K L : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) :
    IsIso (RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite X.sheaf) K L) := by
  refine isIso_derivedBiduality_of_affineModels K L fun V hV => ?_
  have hR : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨ω, hω, iK⟩ := exists_isDualizingComplex_iso_overFunctor_of_isDualizingComplex V K hV hK
  obtain ⟨M, hM, iL⟩ := exists_finite_iso_overFunctor_of_isCoherent V hV L hL
  exact ⟨ω, M, iK, iL, isIso_derivedBiduality_derivedTilde Γ(X, V) ω M hω hM⟩

end Stacks.Duality

end
