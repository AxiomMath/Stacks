module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtProjectionFormulaBaseChangeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PullbackModulesBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexSingle

/-!
# The base change of `Ext` out of a homotopy colimit of duals of perfect stages

This is the proof of Stacks 0DKL given the tower of perfect stages of the proof of Stacks 08JR (B).
Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒢^•` a bounded complex of quasi-coherent
`𝒪_X`-modules, flat over `Y`, whose terms are supported on a closed `Z ⊆ |X|` contained in a
quasi-compact open subspace `V`, with `V ⟶ Y` quasi-compact and quasi-separated. Suppose given

* perfect objects `Pₙ` of `D(𝒪_V)` with maps `cₙ : Pₙ ⟶ E|_V` which are isomorphisms on `Hʲ` for
  `j > -(n + 2)`,
* objects `Lₙ ≅ (Rf_{V*}(Pₙ^∨ ⊗^L 𝒢^•|_V))^∨` of `D(𝒪_Y)` (with the pushforwards perfect), and
* an object `L` of `D(𝒪_Y)` with maps `ιₙ : Lₙ ⟶ L` which are isomorphisms on `Hʲ` for
  `j > -(n + a)`.

This is the situation of the proof of Stacks 08JR (B), where `L` is the homotopy colimit of the
`Lₙ`. Then for every cartesian square `X' = X ×_Y Y'`, with `g : Y' ⟶ Y` arbitrary, there are
isomorphisms

`Ext^i_{Y'}(Lg^*L, ℱ') ≅ Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*ℱ')`

for `ℱ'` quasi-coherent on `Y'`, natural in `ℱ'`. In degree `i` the isomorphism is the one of the
stage `n` with `n ≥ i - a + 2` and `n ≥ i - a₀`, where `𝒢^•` vanishes below `a₀`
(`AlgebraicGeometry.Space.baseChangeStageExt`). The stage computes it with Stacks 0A1K, 08IN,
0A1M and 08GG, on the preimage `g'⁻¹V` of the neighbourhood.

## Main results

* `AlgebraicGeometry.Space.exists_baseChange_extAddEquiv_of_stages`.

## References

* [Stacks Project, Tag 0DKL](https://stacks.math.columbia.edu/tag/0DKL)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- The stage index used in degree `i`: the least `n ≥ 0` with `n ≥ i - a + 2` and `n ≥ i - a₀`. -/
def baseChangeStageIndex (a a₀ i : ℤ) : ℕ :=
  (max (i - a + 2) (i - a₀)).toNat

/-- The stage index used in degree `i` is at least `i - a + 2`. -/
theorem le_baseChangeStageIndex_left (a a₀ i : ℤ) :
    i - a + 2 ≤ (baseChangeStageIndex a a₀ i : ℤ) :=
  (le_max_left _ _).trans (Int.self_le_toNat _)

/-- The stage index used in degree `i` is at least `i - a₀`. -/
theorem le_baseChangeStageIndex_right (a a₀ i : ℤ) :
    i - a₀ ≤ (baseChangeStageIndex a a₀ i : ℤ) :=
  (le_max_right _ _).trans (Int.self_le_toNat _)

/-- **Stacks 0DKL, from the tower of perfect stages of Stacks 08JR (B).** See the module
documentation. For every cartesian square `X' = X ×_Y Y'` there are isomorphisms
`Ext^i_{Y'}(Lg^*L, ℱ') ≅ Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*ℱ')` for `ℱ'` quasi-coherent on
`Y'`, natural in `ℱ'`; the pullback of `𝒢^•` is the termwise (underived) one. -/
theorem exists_baseChange_extAddEquiv_of_stages (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (a₀ b₀ : ℤ) (hGb : ∀ q : ℤ, q < a₀ ∨ b₀ < q → IsZero (G.X q))
    (hGq : ∀ q, (G.X q).IsQuasicoherentOnSite) (hGfl : ∀ q, IsFlatOver B S hS X.2 f.hom (G.X q))
    (Z : Set (points B S hS X.1)) (hZ : IsClosed Z)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
    (V : Subfunctor X.1) (hV : IsOpenSubspace B S hS V)
    (hZV : Z ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι))
    (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
    (hfqc : IsQuasiCompact B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hfqs : IsQuasiSeparated B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (P : ℕ → DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (hP : ∀ n, RingedSite.IsPerfect (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2) (P n))
    (cE : ∀ n, P n ⟶ (edsEtaleRestrict B S hS hsq).obj E)
    (hcE : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + 2) < j →
      IsIso ((DerivedCategory.homologyFunctor _ j).map (cE n)))
    (hK : ∀ n, RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).obj
        (((smallEtaleDerivedTensor B S hS _).obj (smallEtaleDerivedDual B S hS _ (P n))).obj
          (DerivedCategory.Q.obj ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))))
    (Lt : ℕ → DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (eL : ∀ n, Lt n ≅ smallEtaleDerivedDual B S hS Y
      ((smallEtaleDerivedModulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).obj
        (((smallEtaleDerivedTensor B S hS _).obj (smallEtaleDerivedDual B S hS _ (P n))).obj
          (DerivedCategory.Q.obj ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))))
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ι : ∀ n, Lt n ⟶ L) (a : ℤ)
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
              ((CochainComplex.singleFunctor _ 0).map q)))⟦i⟧' := by
  have hsq' := isElementaryDistinguishedSquare_openSubspaceOfPoints_preimage g' Z hZ V hV hZV
  have hT' := edsComplementPoints_preimage (B := B) (S := S) (hS := hS) g' Z
  let GV := (pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G
  have hGbV : ∃ b : ℤ, ∀ i, b < i → IsZero (GV.X i) :=
    ⟨b₀, fun i hi => isZero_smallEtalePullbackModules_obj _ (hGb i (Or.inr hi))⟩
  have hqV : ∀ n, (GV.X n).IsQuasicoherentOnSite := fun n =>
    isQuasicoherentOnSite_smallEtalePullbackModules_obj _ _ (hGq n)
  have hflV : ∀ n, IsFlatOver B S hS (edsEtale B S hS hsq).2 (edsEtaleHom B S hS hsq ≫ f).hom
      (GV.X n) := fun n =>
    isFlatOver_smallEtalePullbackModules_obj_comp _ (isEtale_edsEtaleHom B S hS hsq) f _ (hGfl n)
  have hGab : ∀ q : ℤ, q < a₀ ∨ b₀ < q → IsZero (((pullbackComplexSmallEtale
      (edsEtalePreimageHom hsq g' hsq')).obj GV).X q) := fun q hq =>
    isZero_smallEtalePullbackModules_obj _ (isZero_smallEtalePullbackModules_obj _ (hGb q hq))
  have hGflV' : ∀ n x, IsFlatOverAtGeometricPoint B S hS (edsEtaleHom B S hS hsq' ≫ f')
      (((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj GV).X n) x :=
    fun n x => isFlatOverAtGeometricPoint_smallEtalePullbackModules_obj
      (isPullback_edsEtalePreimageHom_comp hsq g' hsq' sq) _ (hqV n) (hflV n) x
  have hN : ∀ F' : Modules.{u, u} B S hS Y'.1 Y'.2,
      CohomologySupportedOn B S hS X'.1 X'.2
        (edsComplementPoints B S hS (openSubspaceOfPoints B S hS X'.1
          (pointsMap B S hS X'.1 g'.hom ⁻¹' Z)ᶜ))
        (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
          ((CochainComplex.singleFunctor _ 0).obj F')) := by
    intro F'
    rw [hT']
    refine cohomologySupportedOn_Q_obj_tensorPullbackComplex_single f' _ _ (fun n => ?_) F'
    exact (supportOfSheaf_eq_of_iso B S hS X' ((pullbackModulesIsoModulePullback B S hS g').app
      (G.X n))).le.trans ((supportOfSheaf_modulePullback_subset_preimage B S hS g' (G.X n)).trans
        (Set.preimage_mono (hGZ n)))
  have ha : ∀ F' : Modules.{u, u} B S hS Y'.1 Y'.2,
      (show DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
        tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
        ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj GV)
          ((CochainComplex.singleFunctor _ 0).obj F')).IsGE a₀ := fun F' =>
    isGE_Q_obj_tensorPullbackComplex_single _ _ a₀ (fun n hn => hGab n (Or.inl hn)) F'
  have hiL : ∀ i : ℤ, i + -((baseChangeStageIndex a a₀ i : ℤ) + a) + 2 ≤ 0 := fun i => by
    have := le_baseChangeStageIndex_left a a₀ i
    omega
  have hiE : ∀ i : ℤ, i + -((baseChangeStageIndex a a₀ i : ℤ) + 2) + 2 ≤ a₀ := fun i => by
    have := le_baseChangeStageIndex_right a a₀ i
    omega
  refine ⟨fun F' hF' i => baseChangeStageExt hsq hsq' sq hfqc hfqs G hGbV hqV hflV a₀ b₀ hGab
      hGflV' E (P (baseChangeStageIndex a a₀ i)) (hP (baseChangeStageIndex a a₀ i))
      (cE (baseChangeStageIndex a a₀ i)) (-((baseChangeStageIndex a a₀ i : ℤ) + 2))
      (hcE (baseChangeStageIndex a a₀ i)) (hK (baseChangeStageIndex a a₀ i))
      (Lt (baseChangeStageIndex a a₀ i)) L (ι (baseChangeStageIndex a a₀ i))
      (-((baseChangeStageIndex a a₀ i : ℤ) + a)) (hι (baseChangeStageIndex a a₀ i))
      (eL (baseChangeStageIndex a a₀ i)) F' hF' (hN F') (ha F') i (hiL i) (hiE i), ?_⟩
  intro F' F'' hF' hF'' q i e
  exact baseChangeStageExt_naturality hsq hsq' sq hfqc hfqs G hGbV hqV hflV a₀ b₀ hGab
      hGflV' E (P (baseChangeStageIndex a a₀ i)) (hP (baseChangeStageIndex a a₀ i))
      (cE (baseChangeStageIndex a a₀ i)) (-((baseChangeStageIndex a a₀ i : ℤ) + 2))
      (hcE (baseChangeStageIndex a a₀ i)) (hK (baseChangeStageIndex a a₀ i))
      (Lt (baseChangeStageIndex a a₀ i)) L (ι (baseChangeStageIndex a a₀ i))
      (-((baseChangeStageIndex a a₀ i : ℤ) + a)) (hι (baseChangeStageIndex a a₀ i))
      (eL (baseChangeStageIndex a a₀ i)) hF' hF'' q (hN F') (ha F') (hN F'') (ha F'') i (hiL i)
      (hiE i) e

end AlgebraicGeometry.Space

end
