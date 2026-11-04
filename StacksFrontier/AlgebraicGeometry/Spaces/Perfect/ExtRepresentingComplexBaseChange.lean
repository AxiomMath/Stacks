module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualTowerBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualTowerData

/-!
# Stacks 0DKL: the complex `L` of Stacks 08JR (B) is compatible with base change

Let `Y` be a Noetherian algebraic space, `f : X ⟶ Y` a morphism locally of finite type and
quasi-separated, `E ∈ D^-_{Coh}(𝒪_X)`, and `𝒢^•` a bounded complex of coherent `𝒪_X`-modules,
flat over `Y`, with support proper over `Y`. Part (B) of Stacks 08JR gives a pseudo-coherent
`L ∈ D(𝒪_Y)` with isomorphisms `Ext^i_Y(L, ℱ) ≅ Ext^i_X(E, 𝒢^• ⊗ f^*ℱ)` for `ℱ` quasi-coherent,
natural in `ℱ` and compatible with boundary maps. Stacks 0DKL: this `L` is compatible with base
change. For every cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of algebraic spaces there are isomorphisms

`Ext^i_{Y'}(Lg^*L, ℱ') ≅ Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*ℱ')`

for `ℱ'` quasi-coherent on `Y'`, natural in `ℱ'`. No derived pullback is taken of `𝒢^•`.

`L` is the homotopy colimit of the tower `Lₙ = (Rf_{V*} RSheafHom(Pₙ, 𝒢^•|_V))^∨` of the proof of
Stacks 08JR (`AlgebraicGeometry.Space.exists_extPerfectDualTower_data`).

## Main results

* `AlgebraicGeometry.Space.exists_isPseudoCoherent_extAddEquiv_baseChange`: Stacks 0DKL.

## References

* [Stacks Project, Tag 0DKL](https://stacks.math.columbia.edu/tag/0DKL)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 0A1K](https://stacks.math.columbia.edu/tag/0A1K)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 0A1M](https://stacks.math.columbia.edu/tag/0A1M)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- The base change part of Stacks 0DKL, for the data of the tower of Stacks 08JR (B)
(`AlgebraicGeometry.Space.exists_extPerfectDualTower_data`). -/
theorem exists_baseChange_extAddEquiv_of_extPerfectDualTower_data
    (hTop : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : SmallEtaleFlatProperSupport B S hS f hf G)
    (Z : Set (points B S hS X.1)) (hZ : IsClosed Z) (V : Subfunctor X.1)
    (hV : IsOpenSubspace B S hS V)
    (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
    (hZp : IsProperOver B S hS X.2 Y.2 f.hom hf Z hZ)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hcompl : edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ) = Z)
    (hZV : Z ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι))
    (hfqc : IsQuasiCompact B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (tE : ℕ ⥤ smallEtaleModulesDerived B S hS (edsEtale B S hS hsq))
    (htE : ∀ n, SmallEtaleIsPerfect B S hS (tE.obj n))
    (cE : ∀ n, tE.obj n ⟶ ((edsEtaleRestrict B S hS hsq).obj E :
      smallEtaleModulesDerived B S hS (edsEtale B S hS hsq)))
    (hcE : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + 2) < j →
      IsIso ((smallEtaleModulesHomology B S hS (edsEtale B S hS hsq) j).map (cE n)))
    (a : ℤ) (L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (ι : ∀ n, (extPerfectDualTower B S hS hTop (edsEtaleHom B S hS hsq ≫ f)
        (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
        (isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs) hY
        (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
        (flatProperSupport_edsRestrictComplex B S hS hTop f hf hfqs hY G hG hsq hVqc hGZ hcompl
          (fun _ => hZp)) tE htE).obj n ⟶ L)
    (hι : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + a) < j →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) j).map (ι n)))
    {X' Y' : AlgebraicSpaces B S hS} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) :
    ∃ Ψ : ∀ (F' : Modules.{u, u} B S hS Y'.1 Y'.2) (_ : F'.IsQuasicoherentOnSite) (i : ℤ),
        (asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧) ≃+
        (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E) ⟶
          (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
            ((CochainComplex.singleFunctor _ 0).obj F'))⟦i⟧),
      ∀ {F' F'' : Modules.{u, u} B S hS Y'.1 Y'.2} (hF' : F'.IsQuasicoherentOnSite)
        (hF'' : F''.IsQuasicoherentOnSite) (q : F' ⟶ F'') (i : ℤ)
        (e : asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧),
        Ψ F'' hF'' i (e ≫ ((DerivedCategory.singleFunctor _ 0).map q)⟦i⟧') =
          Ψ F' hF' i e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f'
            ((pullbackComplexSmallEtale g').obj G)).map
              ((CochainComplex.singleFunctor _ 0).map q)))⟦i⟧' := by
  obtain ⟨a₀, b₀, hGb⟩ := hG.bounded
  exact exists_baseChange_extAddEquiv_of_extPerfectDualTower hTop f hY G a₀ b₀ hGb
    (fun q => (hG.isCoherent q).toIsQuasicoherentOnSite) hG.isFlatOver Z hZ hGZ V hV hZV hsq
    (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf) hfqc
    (isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs)
    (flatProperSupport_edsRestrictComplex B S hS hTop f hf hfqs hY G hG hsq hVqc hGZ hcompl
      (fun _ => hZp))
    E tE.obj htE cE hcE L ι a hι sq

/-- **Stacks 0DKL.** Let `Y` be a Noetherian algebraic space, `f : X ⟶ Y` locally of finite type
and quasi-separated, `E ∈ D^-_{Coh}(𝒪_X)` and `𝒢^•` a bounded complex of coherent `𝒪_X`-modules,
flat over `Y`, with support proper over `Y`. The pseudo-coherent `L ∈ D(𝒪_Y)` of Stacks 08JR (B)
has isomorphisms `Ext^i_Y(L, ℱ) ≅ Ext^i_X(E, 𝒢^• ⊗ f^*ℱ)`, natural in the quasi-coherent `ℱ` and
compatible with boundary maps. It is compatible with base change: for every cartesian square
`X' = X ×_Y Y'` (with `g : Y' ⟶ Y` arbitrary) there are isomorphisms
`Ext^i_{Y'}(Lg^*L, ℱ') ≅ Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*ℱ')` for `ℱ'` quasi-coherent on
`Y'`, natural in `ℱ'`. Here `(g')^*𝒢^•` is the termwise, underived, pullback. -/
@[stacks 0DKL]
theorem exists_isPseudoCoherent_extAddEquiv_baseChange (hTop : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hEcoh : ∀ q : ℤ, IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ q).obj E))
    (hEb : DerivedCategoryB.IsBoundedAbove E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) :
    ∃ (L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (_ : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L)
      (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
        (L ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
          ShiftedHom E (tensorPullbackComplexDerived f G ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
              F)) i),
      (∀ {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
        (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
        (e : L ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧),
        Φ F' hF' i (e ≫ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).map
            q)⟦i⟧') =
          Φ F hF i e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f G).map
            ((HomologicalComplex.single
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
              (ComplexShape.up ℤ) 0).map q)))⟦i⟧') ∧
      (∀ (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
        (h₁ : T.X₁.IsQuasicoherentOnSite) (_h₂ : T.X₂.IsQuasicoherentOnSite)
        (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
        (e : ShiftedHom L ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj
          T.X₃) i),
        Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
          (Φ T.X₃ h₃ i e).comp (DerivedCategory.triangleOfSESδ (S := (ShortComplex.mk
            ((HomologicalComplex.single
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
              (ComplexShape.up ℤ) 0).map T.f)
            ((HomologicalComplex.single
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
              (ComplexShape.up ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map
                (tensorPullbackComplex f G))
              (shortExact_tensorPullbackComplex_map_single
                (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hT))
              (add_comm 1 i)) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
        (_ : IsPullback g' f' f g),
        ∃ Ψ : ∀ (F' : Modules.{u, u} B S hS Y'.1 Y'.2) (_ : F'.IsQuasicoherentOnSite) (i : ℤ),
            (asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
              ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧) ≃+
            (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E) ⟶
              (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
                ((CochainComplex.singleFunctor _ 0).obj F'))⟦i⟧),
          ∀ {F' F'' : Modules.{u, u} B S hS Y'.1 Y'.2} (hF' : F'.IsQuasicoherentOnSite)
            (hF'' : F''.IsQuasicoherentOnSite) (q : F' ⟶ F'') (i : ℤ)
            (e : asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
              ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧),
            Ψ F'' hF'' i (e ≫ ((DerivedCategory.singleFunctor _ 0).map q)⟦i⟧') =
              Ψ F' hF' i e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f'
                ((pullbackComplexSmallEtale g').obj G)).map
                  ((CochainComplex.singleFunctor _ 0).map q)))⟦i⟧' := by
  obtain ⟨Z, hZ, V, hV, hsq, hZp, hGZ, hVqc, hcompl, hZV, hfqc, tE, htE, cE, -, hcE, a, L, ι, -,
    hι, hL, Φ, hΦ, hδ⟩ := exists_extPerfectDualTower_data B S hS hTop f hf hfqs hY E hEcoh hEb G hG
  exact ⟨L, hL, Φ, hΦ, hδ, fun sq => exists_baseChange_extAddEquiv_of_extPerfectDualTower_data
    hTop f hf hfqs hY E G hG Z hZ V hV hsq hZp hGZ hVqc hcompl hZV hfqc tE htE cE hcE a L ι hι sq⟩

end AlgebraicGeometry.Space

end
