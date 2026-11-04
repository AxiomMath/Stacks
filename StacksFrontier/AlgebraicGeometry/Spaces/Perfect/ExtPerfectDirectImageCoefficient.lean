module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion

/-!
# Stacks 08JN: `H^i(Y, K ⊗^L ℱ) = Ext^i(E, 𝒢^• ⊗ f^*ℱ)`

In the notation of Stacks 0DKK (`Y` Noetherian, `f : X ⟶ Y` locally of finite type and
quasi-separated, `E ∈ D(𝒪_X)` perfect, `𝒢^•` a bounded complex of coherent `𝒪_X`-modules flat over
`Y` with support proper over `Y`) and with `K = Rf_* RSheafHom(E, 𝒢^•)`, there are isomorphisms
`H^i(Y, K ⊗^L ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢^• ⊗ f^*ℱ)` for quasi-coherent `ℱ`, functorial in `ℱ` and
compatible with boundary maps.

This file supplies the coefficient data consumed by
`AlgebraicGeometry.Space.exists_extPerfectCohomologyIso_of_coefficient`: the comparison
`𝒢^• ⊗^L Lf^*ℱ ⟶ 𝒢^• ⊗ f^*ℱ` (`AlgebraicGeometry.Space.tensorPullbackComplexNatTrans`) is an
isomorphism for every `𝒪_Y`-module `ℱ` (the terms of `𝒢^•` being flat over `Y`), the sequence
`0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0` is short exact, and the comparison carries
boundary maps to boundary maps.

## Main results

* `AlgebraicGeometry.Space.isIso_extPerfectCoefficientComparison_tensorPullbackComplexNatTrans`.
* `AlgebraicGeometry.Space.exists_extPerfectCohomologyIso`: Stacks 08JN.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- The terms of a complex as in Stacks 08JN are flat over `Y` at every geometric point of `X`. -/
theorem FlatProperSupportComplex.isFlatOverAtGeometricPoint {f : X ⟶ Y}
    {hf : IsLocallyOfFiniteType B S hS f.hom}
    {G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (hG : FlatProperSupportComplex B S hS f hf G) (n : ℤ) (x : GeometricPoint B S hS X.1) :
    IsFlatOverAtGeometricPoint B S hS f (G.X n) x := by
  have := (hG.isCoherent n).toIsQuasicoherentOnSite
  exact (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS f (G.X n)).1 (hG.isFlatOver n) x

/-- **The coefficient comparison of Stacks 08JN is invertible**: for a bounded complex `𝒢^•` of
`𝒪_X`-modules flat over `Y`, `𝒢^• ⊗^L Lf^*ℱ ⟶ 𝒢^• ⊗ f^*ℱ` is an isomorphism for every
`𝒪_Y`-module `ℱ`. -/
theorem isIso_extPerfectCoefficientComparison_tensorPullbackComplexNatTrans (f : X ⟶ Y)
    {hf : IsLocallyOfFiniteType B S hS f.hom}
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    IsIso (extPerfectCoefficientComparison B S hS f G (tensorPullbackComplexNatTrans f G) F) := by
  obtain ⟨a, b, hGb⟩ := hG.bounded
  exact isIso_tensorPullbackComplexNatTrans_app_single (f := f) (G := G) a b hGb
    (hG.isFlatOverAtGeometricPoint B S hS) F

/-- **Stacks 08JN.**  Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism locally
of finite type and quasi-separated, let `E ∈ D(𝒪_X)` be perfect and `𝒢^•` a bounded complex of
coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y` (the notation of Stacks
0DKK), and let `K = Rf_* RSheafHom(E, 𝒢^•)`.  Then there are isomorphisms
`H^i(Y, K ⊗^L ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢^• ⊗ f^*ℱ)` for quasi-coherent `𝒪_Y`-modules `ℱ`,
functorial in `ℱ`, and compatible with the boundary maps: for a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of quasi-coherent `𝒪_Y`-modules the boundary map
`H^i(Y, K ⊗^L ℱ₃) → H^{i+1}(Y, K ⊗^L ℱ₁)` corresponds to the boundary map
`Ext^i(E, 𝒢^• ⊗ f^*ℱ₃) → Ext^{i+1}(E, 𝒢^• ⊗ f^*ℱ₁)` of the short exact sequence of complexes
`0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0`.

Here `K = Rf_* RSheafHom(E, 𝒢^•)` is formed with the internal hom
`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom` of `D(𝒪_X)` (the one adjoint to the derived
tensor product of the small étale site, Stacks 08J8); it is perfect by
`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_smallEtaleDerivedSheafHom`.  Stacks
0DKK itself is registered, on the internal hom of the ringed site, as
`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedSheafHom`.  `H^i(Y, -)` is the
`i`-th cohomology of derived global sections, and `Ext^i(E, -) = Hom(E, -[i])` in `D(𝒪_X)`. -/
@[stacks 08JN]
theorem exists_extPerfectCohomologyIso (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) :
    ∃ c : ∀ (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
        F.IsQuasicoherentOnSite → ∀ i : ℤ,
        extPerfectBaseCohomology B S hS f E G F i ≅ extPerfectExtGroup B S hS f E G F i,
      (∀ (F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ),
          (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
              AddCommGrpCat.{u + 1}).map (((DerivedCategory.homologyFunctor
                (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).shift i).map
              ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).map
                (((smallEtaleDerivedTensor B S hS Y).obj
                  (extPerfectDirectImageObj B S hS f E G)).map (extPerfectSingleMap B S hS q)))) ≫
            (c F' hF' i).hom =
          (c F hF i).hom ≫
            (preadditiveCoyoneda.obj (op E)).map ((extPerfectCoefficientMap B S hS f G q)⟦i⟧')) ∧
      (∀ (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
          (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite)
          (i j : ℤ) (h : i + 1 = j),
          extPerfectBaseDelta B S hS f E G T hT i j h ≫ (c T.X₁ h₁ j).hom =
          (c T.X₃ h₃ i).hom ≫ (preadditiveCoyoneda.obj (op E)).map
            ((DerivedCategory.triangleOfSESδ (shortExact_tensorPullbackComplex_map_single
                (hG.isFlatOverAtGeometricPoint B S hS) hT))⟦i⟧' ≫
              (shiftFunctorAdd' _ 1 i j (by omega)).inv.app
                (extPerfectCoefficientObj B S hS f G T.X₁))) :=
  exists_extPerfectCohomologyIso_of_coefficient B S hS hTop f hf hfqs hY E hE G hG
    (tensorPullbackComplexNatTrans f G)
    (isIso_extPerfectCoefficientComparison_tensorPullbackComplexNatTrans B S hS f G hG)
    (fun _ hT => shortExact_tensorPullbackComplex_map_single
      (hG.isFlatOverAtGeometricPoint B S hS) hT)
    (fun _ hT => tensorPullbackComplexNatTrans_triangleOfSESδ
      (hG.isFlatOverAtGeometricPoint B S hS) hT)

end AlgebraicGeometry.Space

end
