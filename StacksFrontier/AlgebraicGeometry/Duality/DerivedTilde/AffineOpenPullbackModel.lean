module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeAffineOpens
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CohomologyFiniteFreeLocus

/-!
# Affine models of a derived object and of its derived pullback

Let `X` be a scheme, `U ⊆ X` an affine open with `A = Γ(X, U)`, and `K` an object of `D(𝒪_X)`
whose restriction to `U` is the complex of quasi-coherent sheaves associated to a complex `P` of
`A`-modules. This file records three consequences.

* For a morphism `g : Y ⟶ X` and an affine open `V ⊆ Y` with `g(V) ⊆ U` and `B = Γ(Y, V)`, if
  `P` is K-flat then the restriction to `V` of `Lg^*K` is the complex associated to `P ⊗_A B`.
* The restriction to `U` of the cohomology sheaf `H^n(K)` is the sheaf associated to `H^n(P)`.
* For `x ∈ U`, the stalk `H^n(K)_x` is `𝒪_{X, x} ⊗_A H^n(P)`.

## Main definitions

* `AlgebraicGeometry.restrictPullbackTildeIsoOfLE`: the affine dictionary of Stacks tag 01I9
  transported to two affine opens `V ⊆ g⁻¹U`.
* `AlgebraicGeometry.restrictDerivedPullbackTildeModelIso`: the affine model of `Lg^*K` on `V`.
* `AlgebraicGeometry.restrictHomologyTildeModelIso`: the affine model of `H^n(K)` on `U`.
* `AlgebraicGeometry.stalkHomologyTildeModelIso` and `stalkHomologyTildeModelEquiv`: the stalk
  `H^n(K)_x ≅ 𝒪_{X, x} ⊗_A H^n(P)`, as an isomorphism of modules and as a linear equivalence for
  the module structure `AlgebraicGeometry.RingedSpace.moduleStalk`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

section

variable {X Y : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
  (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)

/-- The complex of `𝒪_U`-modules associated to a K-flat complex of `Γ(X, U)`-modules is K-flat:
the associated complex on `Spec Γ(X, U)` is K-flat (`Stacks.TildeStalk.kFlatTilde`) and pullback
along `U ≅ Spec Γ(X, U)` preserves K-flatness. -/
theorem kFlatComplex_tilde_restrict (P : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex U.toScheme.toRingedSpace
      (((tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  RingedSpace.KFlatDerivedPullback.kFlat_of_iso
    (Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional
      hU.isoSpec.hom.toLRSHom.toShHom _ (Stacks.TildeStalk.kFlatTilde Γ(X, U) P hP))
    (((NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom)
        (ComplexShape.up ℤ)).app _).symm ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom))
        (ComplexShape.up ℤ)).app P)

/-- **The affine model of a derived pullback.**  Let `K ∈ D(𝒪_X)` restrict on the affine open
`U` to the complex associated to a K-flat complex `P` of `Γ(X, U)`-modules. For a morphism
`g : Y ⟶ X` and an affine open `V ⊆ g⁻¹U`, the restriction to `V` of `Lg^*K` is the complex
associated to `P ⊗_{Γ(X, U)} Γ(Y, V)`. -/
def restrictDerivedPullbackTildeModelIso (K : DerivedCategory X.Modules)
    (P : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) :
    (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          g.toLRSHom.toShHom).obj K) ≅
      (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u}
          (g.appLE U V hVU).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  Scheme.Modules.openRestrictionDerivedPullbackIso V.ι g U.ι (g.resLE U V hVU)
      (Scheme.Hom.resLE_comp_ι g hVU).symm K ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (g.resLE U V hVU).toLRSHom.toShHom).mapIso
      (e ≪≫ (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategoryFactors.app P) ≪≫
    Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat (g.resLE U V hVU).toLRSHom.toShHom _
      (kFlatComplex_tilde_restrict hU P hP) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
          (Iso.refl ((tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ⋙
            Scheme.Modules.pullback (g.resLE U V hVU))) (ComplexShape.up ℤ)).app P ≪≫
        (NatIso.mapHomologicalComplex (restrictPullbackTildeIsoOfLE g hU hV hVU)
          (ComplexShape.up ℤ)).app P ≪≫
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (ModuleCat.extendScalars (g.appLE U V hVU).hom ⋙
            (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom)))
            (ComplexShape.up ℤ)).app P).symm) ≪≫
    ((tilde.functor Γ(Y, V) ⋙
      Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategoryFactors.app _).symm

end

section

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- **The affine model of a cohomology sheaf.**  If `K ∈ D(𝒪_X)` restricts on the affine open `U`
to the complex associated to a complex `P` of `Γ(X, U)`-modules, then `H^n(K)|_U` is the sheaf
associated to `H^n(P)`. -/
def restrictHomologyTildeModelIso (K : DerivedCategory X.Modules)
    (P : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ)
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) (n : ℤ) :
    (Scheme.Modules.restrictFunctor U.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj K) ≅
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj (P.homology n) :=
  (((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso n).app K).symm ≪≫
    (DerivedCategory.homologyFunctor U.toScheme.Modules n).mapIso e ≪≫
    ((tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategoryHomologyIso n).app
        (DerivedCategory.Q.obj P) ≪≫
    (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat Γ(X, U)) n).app P)

/-- **The affine model of a cohomology stalk.**  If `K ∈ D(𝒪_X)` restricts on the affine open `U`
to the complex associated to a complex `P` of `Γ(X, U)`-modules, then for `x ∈ U` the stalk
`H^n(K)_x` is `𝒪_{X, x} ⊗_{Γ(X, U)} H^n(P)`, the tensor product formed along the germ map. -/
def stalkHomologyTildeModelIso (K : DerivedCategory X.Modules)
    (P : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ)
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) (n : ℤ) (x : X) (hx : x ∈ U) :
    (Stacks.Duality.modulesStalkFunctor x).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj K) ≅
      (ModuleCat.extendScalars.{u, u, u} (Stacks.Duality.affineGermRingHom hU x hx)).obj
        (P.homology n) := by
  have e₁ := (Stacks.Duality.affineRestrictStalkNatIso x hx).app
    ((DerivedCategory.homologyFunctor X.Modules n).obj K)
  have e₂ := (Stacks.Duality.modulesStalkFunctor (⟨x, hx⟩ : U.toScheme) ⋙
    ModuleCat.restrictScalars.{u} (Stacks.Duality.affineStalkMap x hx).hom).mapIso
      (restrictHomologyTildeModelIso hU K P e n)
  have e₃ := (Stacks.Duality.affineStalkNatIso hU x hx).app (P.homology n)
  exact e₁.symm ≪≫ e₂ ≪≫ e₃

/-- `AlgebraicGeometry.stalkHomologyTildeModelIso` as a linear equivalence, with the stalk
`H^n(K)_x` carrying its `𝒪_{X, x}`-module structure `AlgebraicGeometry.RingedSpace.moduleStalk`:
`H^n(K)_x ≅ 𝒪_{X, x} ⊗_{Γ(X, U)} H^n(P)`. -/
def stalkHomologyTildeModelEquiv (K : DerivedCategory X.Modules)
    (P : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ)
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) (n : ℤ) (x : X) (hx : x ∈ U) :
    letI := (Stacks.Duality.affineGermRingHom hU x hx).toAlgebra
    @LinearEquiv (ToType (X.presheaf.stalk x)) (ToType (X.presheaf.stalk x)) _ _
      (RingHom.id _) (RingHom.id _) _ _
      (ToType (TopCat.Presheaf.stalk
        ((DerivedCategory.homologyFunctor X.Modules n).obj K).val.presheaf x))
      (TensorProduct Γ(X, U) (ToType (X.presheaf.stalk x)) (P.homology n)) _ _
      (RingedSpace.moduleStalk (X := X.toRingedSpace)
        ((DerivedCategory.homologyFunctor X.Modules n).obj K) x) _ := by
  letI := (Stacks.Duality.affineGermRingHom hU x hx).toAlgebra
  have hinst : ((Stacks.Duality.modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj K)).isModule =
        RingedSpace.moduleStalk (X := X.toRingedSpace)
          ((DerivedCategory.homologyFunctor X.Modules n).obj K) x := by
    refine Module.ext' _ _ fun r m ↦ ?_
    have h := SemilinearStalk.comm_smul_eq X.presheaf x
      ((DerivedCategory.homologyFunctor X.Modules n).obj K).val
      ((SemilinearStalk.commStalkIso X.presheaf x).inv.hom r) m
    rw [show SemilinearStalk.commStalkRingEquiv X.presheaf x
        ((SemilinearStalk.commStalkIso X.presheaf x).inv.hom r) = r from
      (SemilinearStalk.commStalkRingEquiv X.presheaf x).apply_symm_apply r] at h
    exact h.symm
  rw [← hinst]
  exact (stalkHomologyTildeModelIso hU K P e n x hx).toLinearEquiv

end

end AlgebraicGeometry

end
