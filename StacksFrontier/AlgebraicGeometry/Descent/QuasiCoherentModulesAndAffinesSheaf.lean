module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineZariskiCartesian

/-!
# Conditions (1) and (2) of Stacks 0GZX on the small affine site

Let `S` be a scheme and let `τ` be the Zariski or the étale topology. For a presheaf of
`𝒪_affine`-modules `𝓕` on the small affine site `S_{affine, τ}` consider the conditions

1. for each morphism `U ⟶ U'` of `S_{affine, τ}` the base-change map
   `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` is an isomorphism;
2. `𝓕` is a sheaf and is quasi-coherent as a module on the ringed site
   `(S_{affine, τ}, 𝒪_affine)`, in the sense of Modules on Sites, Definition 03DL (6).

This file proves that (1) and (2) are equivalent, for both topologies.

## Main results

* `AlgebraicGeometry.smallAffineZariski_isSheaf_of_baseChange_isIso` and
  `AlgebraicGeometry.smallAffineEtale_isSheaf_of_baseChange_isIso`: a presheaf satisfying (1) is a
  sheaf.
* `AlgebraicGeometry.smallAffineZariski_isSheaf_and_isQuasicoherentOnSite_of_baseChange_isIso`
  and `AlgebraicGeometry.smallAffineEtale_isSheaf_and_isQuasicoherentOnSite_of_baseChange_isIso`:
  for a presheaf of modules, (1) implies (2).
* `AlgebraicGeometry.smallAffineZariski_canonicalMap_isIso_of_isQuasicoherentOnSite` and
  `AlgebraicGeometry.smallAffineEtale_canonicalMap_isIso_of_isQuasicoherentOnSite`: (2) implies
  (1).
* `AlgebraicGeometry.smallAffineZariski_isQuasicoherentOnSite_iff_canonicalMap_isIso` and
  `AlgebraicGeometry.smallAffineEtale_isQuasicoherentOnSite_iff_canonicalMap_isIso`: for a sheaf of
  modules, (1) and (2) are equivalent.

## Implementation notes

Condition (1) is `Stacks.PresheafOfModules.restrictionBaseChange` being an isomorphism, and for a
sheaf of modules on a ringed site that map is `Stacks.SheafOfModules.canonicalMap`: both are the
adjoint transpose of the same restriction map under
`CategoryTheory.ModuleCat.extendRestrictScalarsAdj`. The statements that produce the sheaf
condition are about `CategoryTheory.PresheafOfModules`, the others about
`CategoryTheory.SheafOfModules`.

The implication (2) ⇒ (1) follows Stacks 0H04: quasi-coherence gives a finite covering on whose
slices the module has a global presentation, a global presentation makes the module cartesian on a
slice, and the cartesian condition descends along a flat covering.

## References

* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry

/-! ### The sheaf conjunct of condition (2), from condition (1) -/

/-- A presheaf of `𝒪_affine`-modules on the small affine Zariski site of `S` all of whose
base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms is a sheaf. -/
@[stacks 0GZX "(1) ⇒ (2) at τ = Zariski, sheaf conjunct of (2)"]
theorem smallAffineZariski_isSheaf_of_baseChange_isIso
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O).obj)
    (h : ∀ ⦃X Y : (SmallAffineZariski B S hS)ᵒᵖ⦄ (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} F f)) :
    Presheaf.IsSheaf (smallAffineZariskiRingedSite B S hS).J F.presheaf :=
  SmallAffineZariski.isSheaf_of_cartesian_affineChart B S hS F (fun f => h f)

/-- A presheaf of `𝒪_affine`-modules on the small affine étale site of `S` all of whose base-change
maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms is a sheaf. -/
@[stacks 0GZX "(1) ⇒ (2) at τ = étale, sheaf conjunct of (2)"]
theorem smallAffineEtale_isSheaf_of_baseChange_isIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite B S hS).O).obj)
    (h : ∀ ⦃X Y : (SmallAffineEtale B S hS)ᵒᵖ⦄ (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} F f)) :
    Presheaf.IsSheaf (smallAffineEtaleRingedSite B S hS).J F.presheaf := by
  refine Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_covers'.{u, u + 1, u, u, u, u + 1}
    (SmallAffineEtale.toScheme B S hS) (SmallEtale.affineChartRings B S hS) ?_ ?_ F
    (fun f => h f)
    (SmallAffineEtale.precoverage B S hS) ?_
  · intro U E _ hE
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (SmallAffineEtale.toScheme B S hS))).mp hE
    exact SmallEtale.faithfullyFlat_pi_affineChartRings B S hS E.X E.f hcov hfl
  · intro _ _ _ _ _ _ _ _ hsq
    exact SmallEtale.isPushout_affineChartRings B S hS hsq
  · rintro U _ ⟨E, rfl, hE⟩
    refine ⟨E, rfl, hE.2, ?_⟩
    obtain ⟨hs, het⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (SmallAffineEtale.toScheme B S hS))).mp (BigEtaleSite.IsCovering.etale hE.1)
    exact (Scheme.presieve₀_mem_precoverage_iff _).mpr
      ⟨hs, fun i => by have := het i; infer_instance⟩

/-! ### Condition (2) in full, from condition (1) -/

/-- A presheaf of `𝒪_affine`-modules on the small affine Zariski site of `S` all of whose
base-change maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms is a sheaf, and the resulting sheaf
of modules is quasi-coherent on the ringed site `(S_{affine, Zar}, 𝒪_affine)`. -/
@[stacks 0GZX "(1) ⇒ (2) at τ = Zariski, for a presheaf of modules"]
theorem smallAffineZariski_isSheaf_and_isQuasicoherentOnSite_of_baseChange_isIso
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O).obj)
    (h : ∀ ⦃X Y : (SmallAffineZariski B S hS)ᵒᵖ⦄ (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} F f)) :
    ∃ hs : Presheaf.IsSheaf (smallAffineZariskiRingedSite B S hS).J F.presheaf,
      (⟨F, hs⟩ : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineZariskiRingedSite B S hS).O)).IsQuasicoherentOnSite :=
  ⟨smallAffineZariski_isSheaf_of_baseChange_isIso B S hS F h,
    smallAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS _ fun _ _ f => h f.op⟩

/-- A presheaf of `𝒪_affine`-modules on the small affine étale site of `S` all of whose base-change
maps `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms is a sheaf, and the resulting sheaf of modules
is quasi-coherent on the ringed site `(S_{affine, étale}, 𝒪_affine)`. -/
@[stacks 0GZX "(1) ⇒ (2) at τ = étale, for a presheaf of modules"]
theorem smallAffineEtale_isSheaf_and_isQuasicoherentOnSite_of_baseChange_isIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite B S hS).O).obj)
    (h : ∀ ⦃X Y : (SmallAffineEtale B S hS)ᵒᵖ⦄ (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u} F f)) :
    ∃ hs : Presheaf.IsSheaf (smallAffineEtaleRingedSite B S hS).J F.presheaf,
      (⟨F, hs⟩ : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineEtaleRingedSite B S hS).O)).IsQuasicoherentOnSite :=
  ⟨smallAffineEtale_isSheaf_of_baseChange_isIso B S hS F h,
    smallAffineEtale_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS _ fun _ _ f => h f.op⟩

/-! ### Condition (1), from condition (2) -/

/-- If a sheaf of modules on the small affine Zariski site of `S` is quasi-coherent on the ringed
site `(S_{affine, Zar}, 𝒪_affine)`, then its base-change map `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` along
every morphism is an isomorphism. -/
@[stacks 0GZX "(2) ⇒ (1) at τ = Zariski"]
theorem smallAffineZariski_canonicalMap_isIso_of_isQuasicoherentOnSite
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O))
    (hF : F.IsQuasicoherentOnSite)
    {U V : SmallAffineZariski B S hS} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineZariskiRingedSite B S hS) F f) := by
  have h₂ := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hF
  have h₃ :=
    SmallAffineZariski.isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
      B S hS _ h₂ f
  have h₄ := Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_uliftForPresentation
    (SmallAffineZariski.affineChartRings B S hS) _ F f.op h₃
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h₄

/-- If a sheaf of modules on the small affine étale site of `S` is quasi-coherent on the ringed
site `(S_{affine, étale}, 𝒪_affine)`, then its base-change map `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` along
every morphism is an isomorphism. -/
@[stacks 0GZX "(2) ⇒ (1) at τ = étale"]
theorem smallAffineEtale_canonicalMap_isIso_of_isQuasicoherentOnSite
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite B S hS).O))
    (hF : F.IsQuasicoherentOnSite)
    {U V : SmallAffineEtale B S hS} (f : U ⟶ V) :
    IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineEtaleRingedSite B S hS) F f) := by
  have h₂ := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hF
  have h₃ :=
    SmallEtale.isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite.{u, u}
      B S hS _ _ h₂ f
  have h₄ := Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_uliftForPresentation
    (smallAffineEtaleRingedSite B S hS).O.obj _ F f.op h₃
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h₄

/-! ### Conditions (1) and (2) are equivalent -/

/-- A sheaf of modules on the small affine Zariski site of `S` is quasi-coherent on the ringed site
`(S_{affine, Zar}, 𝒪_affine)` exactly when all of its base-change maps
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms. -/
@[stacks 0GZX "(1) ⇔ (2) at τ = Zariski, for a sheaf of modules"]
theorem smallAffineZariski_isQuasicoherentOnSite_iff_canonicalMap_isIso
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O)) :
    F.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : SmallAffineZariski B S hS⦄ (f : U ⟶ V),
        IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineZariskiRingedSite B S hS) F f) :=
  ⟨fun hF _ _ f =>
      smallAffineZariski_canonicalMap_isIso_of_isQuasicoherentOnSite B S hS F hF f,
    smallAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS F⟩

/-- A sheaf of modules on the small affine étale site of `S` is quasi-coherent on the ringed site
`(S_{affine, étale}, 𝒪_affine)` exactly when all of its base-change maps
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms. -/
@[stacks 0GZX "(1) ⇔ (2) at τ = étale, for a sheaf of modules"]
theorem smallAffineEtale_isQuasicoherentOnSite_iff_canonicalMap_isIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite B S hS).O)) :
    F.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : SmallAffineEtale B S hS⦄ (f : U ⟶ V),
        IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineEtaleRingedSite B S hS) F f) :=
  ⟨fun hF _ _ f => smallAffineEtale_canonicalMap_isIso_of_isQuasicoherentOnSite B S hS F hF f,
    smallAffineEtale_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS F⟩

end AlgebraicGeometry

end
