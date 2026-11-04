module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtRepresentingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareStep

/-!
# The base change of `Ext` out of the homotopy colimit of the tower of Stacks 08JR (B)

The tower of the proof of Stacks 08JR (B) lives on the quasi-compact neighbourhood `V` of the
support of `𝒢^•`: its stages are `Lₙ = (R(f|_V)_* RSheafHom(Pₙ, 𝒢^•|_V))^∨`
(`AlgebraicGeometry.Space.extPerfectDualObj`) for perfect approximations `Pₙ ⟶ E|_V`. This file
specializes `AlgebraicGeometry.Space.exists_baseChange_extAddEquiv_of_stages` to these stages:
`Lₙ ≅ (R(f|_V)_*(Pₙ^∨ ⊗^L 𝒢^•|_V))^∨`, and the direct images are perfect by Stacks 0DKK.

## Main results

* `AlgebraicGeometry.Space.exists_baseChange_extAddEquiv_of_extPerfectDualTower`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0DKL for the tower of Stacks 08JR (B).** Let `L` receive maps `ιₙ` from the stages
`Lₙ = (R(f|_V)_* RSheafHom(Pₙ, 𝒢^•|_V))^∨` of the tower, isomorphisms on `Hʲ` for `j > -(n + a)`.
Then for every cartesian square `X' = X ×_Y Y'` there are isomorphisms
`Ext^i_{Y'}(Lg^*L, ℱ') ≅ Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*ℱ')` for `ℱ'` quasi-coherent on
`Y'`, natural in `ℱ'`. -/
theorem exists_baseChange_extAddEquiv_of_extPerfectDualTower (hTop : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hY : IsNoetherian B S hS hTop Y.1)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (a₀ b₀ : ℤ) (hGb : ∀ q : ℤ, q < a₀ ∨ b₀ < q → IsZero (G.X q))
    (hGq : ∀ q, (G.X q).IsQuasicoherentOnSite) (hGfl : ∀ q, IsFlatOver B S hS X.2 f.hom (G.X q))
    (Z : Set (points B S hS X.1)) (hZ : IsClosed Z)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
    (V : Subfunctor X.1) (hV : IsOpenSubspace B S hS V)
    (hZV : Z ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι))
    (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
    (hfV : IsLocallyOfFiniteType B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hfqc : IsQuasiCompact B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hfqs : IsQuasiSeparated B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hGV : SmallEtaleFlatProperSupport B S hS (edsEtaleHom B S hS hsq ≫ f) hfV
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (P : ℕ → DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (hP : ∀ n, SmallEtaleIsPerfect B S hS (P n))
    (cE : ∀ n, P n ⟶ (edsEtaleRestrict B S hS hsq).obj E)
    (hcE : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + 2) < j →
      IsIso ((DerivedCategory.homologyFunctor _ j).map (cE n)))
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ι : ∀ n, extPerfectDualObj B S hS (edsEtaleHom B S hS hsq ≫ f) (P n)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) ⟶ L) (a : ℤ)
    (hι : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + a) < j →
      IsIso ((DerivedCategory.homologyFunctor _ j).map (ι n)))
    {X' Y' : AlgebraicSpaces B S hS} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) :
    ∃ Φ : ∀ (F' : Modules.{u, u} B S hS Y'.1 Y'.2) (_ : F'.IsQuasicoherentOnSite) (i : ℤ),
        (asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧) ≃+
        (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E) ⟶
          (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
            ((CochainComplex.singleFunctor _ 0).obj F'))⟦i⟧),
      ∀ {F' F'' : Modules.{u, u} B S hS Y'.1 Y'.2} (hF' : F'.IsQuasicoherentOnSite)
        (hF'' : F''.IsQuasicoherentOnSite) (q : F' ⟶ F'') (i : ℤ)
        (e : asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧),
        Φ F'' hF'' i (e ≫ ((DerivedCategory.singleFunctor _ 0).map q)⟦i⟧') =
          Φ F' hF' i e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f'
            ((pullbackComplexSmallEtale g').obj G)).map
              ((CochainComplex.singleFunctor _ 0).map q)))⟦i⟧' :=
  exists_baseChange_extAddEquiv_of_stages f G a₀ b₀ hGb hGq hGfl Z hZ hGZ V hV hZV hsq hfqc hfqs
    E P hP cE hcE
    (fun n => isPerfect_of_iso' B S hS
      (dualPushforwardTensorIsoExtPerfectDirectImageObj B S hS _ (P n) (hP n) _).symm
      (isPerfect_extPerfectDirectImageObj B S hS hTop _ hfV hfqs hY (P n) (hP n) _ hGV))
    (fun n => extPerfectDualObj B S hS (edsEtaleHom B S hS hsq ≫ f) (P n)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
    (fun n => extPerfectDualObjIsoDualPushforwardTensor B S hS _ (P n) (hP n) _)
    L ι a hι sq

end AlgebraicGeometry.Space

end
