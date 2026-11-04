module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AnnihilationLocality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison

/-!
# The comparison map of [Stacks, Tag 07Q9] for a sheaf of modules

[Stacks, Tag 07Q9] is about the distinguished triangle

`Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}ℱ' ⟶ E ⟶ Ru_{X/S, *}ℱ[1]`,  `ℱ' = f_cris^*ℱ`,

for `ℱ` a crystal in quasi-coherent `𝒪_{X/S}`-modules and `f : X' ⟶ X` a morphism over `S₀`.
Here `f_cris^*` is the pullback of **modules** along the morphism of ringed topoi `f_cris`; it is
not the inverse image `f_cris^{-1}` of the underlying abelian sheaves, the two differing by the
tensor factor `f_cris^{-1}𝒪_{X/S} ⟶ 𝒪_{X'/S}`.  The library's comparison map
`...SmallSite.derivedZariskiComparison` is built from `f_cris^{-1}`.  This file builds the map of
[Stacks, Tag 07Q9] itself.

* `overSituation T f` is the crystalline situation `X'/S` of a scheme `X'` over the scheme `X`
  of a situation `T = X/S`, over the **same** divided power base, and `overSituation_compat`
  says that `f` is a morphism of situations over the identity of `S`.
* `crisModuleUnit` is the adjunction unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ`, read on underlying abelian
  sheaves.  Its three factors are the units of the three adjunctions out of which `f_cris` is
  built: the module-level `i_{X, !} ⊣ i_X^{-1}` of [Stacks, Tag 07IJ], and the abelian units of
  restriction along change of divided power base and along the inclusion of the small site.
* `crisModuleComparison` is the comparison `f_cris^{-1}ℱ ⟶ f_cris^*ℱ` of the underlying abelian
  sheaves, the transpose of `crisModuleUnit`.
* `moduleComparison07Q9` is the first arrow of the triangle of [Stacks, Tag 07Q9],
  `Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}f_cris^*ℱ` in `D⁺(Ab(X_Zar))`.
* `derivedModulePullbackMap` is the map `RΓ(Cris(X/S), ℱ) ⟶ RΓ(Cris(X'/S), f_cris^*ℱ)` in
  `D⁺(Ab)`, the global-sections form of the same map.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The situation `X'/S` of a scheme over `X` -/

/-- **The crystalline situation `X'/S` of a scheme `X'` over the scheme `X` of `T = X/S`**, over
the same divided power base `(S, I, γ)`: the structure morphism to `S₀` is `X' ⟶ X ⟶ S₀`.  The
prime is locally nilpotent on `X'` because it is on `X` and `f` induces maps of local rings. -/
@[reducible]
def overSituation (T : GlobalCrystallineSituation.{u}) {X' : Scheme.{u}} (f : X' ⟶ T.X) :
    GlobalCrystallineSituation.{u} where
  p := T.p
  prime := T.prime
  S := T.S
  algebraAtPrime := T.algebraAtPrime
  X := X'
  toClosedFiber := f ≫ T.toClosedFiber
  prime_locallyNilpotent x := by
    have hx := T.prime_locallyNilpotent (f.base x)
    simpa using hx.map (f.stalkMap x).hom

/-- **`f` is a morphism of crystalline situations `X'/S ⟶ X/S` over the identity of `S`.**  The
closed fibre of an identity is an identity. -/
theorem overSituation_compat (T : GlobalCrystallineSituation.{u}) {X' : Scheme.{u}}
    (f : X' ⟶ T.X) :
    (overSituation T f).toClosedFiber ≫ DividedPowerScheme.closedFiberMap (𝟙 T.S) =
      f ≫ T.toClosedFiber :=
  (congrArg (fun k ↦ (overSituation T f).toClosedFiber ≫ k)
      (DividedPowerScheme.closedFiberFunctor.map_id T.S)).trans
    (Category.comp_id (f ≫ T.toClosedFiber))

/-! ### The unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` and the comparison `f_cris^{-1}ℱ ⟶ f_cris^*ℱ` -/

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf in
/-- The abelian unit of restriction along change of divided power base followed by restriction to
the small site, `N ⟶ f_{CRIS, *}i_{X, *}i_X^{-1}f_CRIS^{-1}N`, for an abelian sheaf `N` on
`CRIS(X'/S')`.  Change of divided power base is continuous and cocontinuous, so its inverse image
is restriction along it, with the unit of Mathlib's
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`. -/
def changeBaseRestrictionUnit (N : Sheaf (topology S') AddCommGrpCat.{u + 1}) :
    N ⟶ (changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj ((smallRestriction S).obj
      (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (topology S) (topology S')).obj N))) :=
  ((changeBase S S' fS fX hf).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (topology S) (topology S')).unit.app N ≫
    (changeBaseDirectImage S S' fS fX hf).map ((bigDirectImageAdjunction S).unit.app _)

/-- **The unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` on underlying abelian sheaves.**  It is the
module-level unit `ℱ ⟶ i_X^{-1}i_{X, !}ℱ` of [Stacks, Tag 07IJ], followed by `i_X^{-1}` of the
unit `changeBaseRestrictionUnit` at `i_{X, !}ℱ`. -/
def crisModuleUnit (F : ModuleSheaf S') :
    (toAbelianSheaf S').obj F ⟶ (crisDirectImage S S' fS fX hf).obj
      ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) :=
  (toAbelianSheaf S').map ((moduleLowerShriekAdjunction S').unit.app F) ≫
    (smallRestriction S').map (changeBaseRestrictionUnit S S' fS fX hf
      ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S')).obj
        ((moduleLowerShriek S').obj F)))

/-- **The comparison `f_cris^{-1}ℱ ⟶ f_cris^*ℱ`** of the abelian inverse image of the underlying
abelian sheaf with the abelian sheaf underlying the module pullback: the transpose of
`crisModuleUnit` under `f_cris^{-1} ⊣ f_{cris, *}`. -/
def crisModuleComparison (F : ModuleSheaf S') :
    crisPullback S S' fS fX hf ((toAbelianSheaf S').obj F) ⟶
      (toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F) :=
  ((crisDirectImageAdjunction S S' fS fX hf).homEquiv _ _).symm
    (crisModuleUnit S S' fS fX hf F)

/-- **`crisModuleUnit` factors through the abelian unit**: it is the unit
`ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ` followed by `f_{cris, *}` of the comparison
`crisModuleComparison`. -/
theorem crisUnit_comp_crisModuleComparison (F : ModuleSheaf S') :
    crisUnit S S' fS fX hf ((toAbelianSheaf S').obj F) ≫
        (crisDirectImage S S' fS fX hf).map (crisModuleComparison S S' fS fX hf F) =
      crisModuleUnit S S' fS fX hf F := by
  simp [crisUnit, crisModuleComparison, Adjunction.homEquiv_counit]

/-! ### The comparison map of [Stacks, Tag 07Q9] -/

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- **The first arrow of the triangle of [Stacks, Tag 07Q9]**,
`Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'` with `ℱ' = f_cris^*ℱ`, in `D⁺(Ab(X_Zar))`.  It is the
comparison map of the underlying abelian sheaves, `...SmallSite.derivedZariskiComparison` along
the square of topoi `...SmallSite.crisZariskiSquare`, followed by `Rf_{Zar, *}Ru_{X'/S, *}` of
`crisModuleComparison`. -/
def moduleComparison07Q9 (F : ModuleSheaf S') :
    (derivedZariskiDirectImage S').obj ((toAbelianSheaf S').obj F) ⟶
      (derivedZariskiPushforwardFunctor S S' fX).obj ((derivedZariskiDirectImage S).obj
        ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F))) :=
  derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf)
      ((toAbelianSheaf S').obj F) ≫
    (derivedZariskiPushforwardFunctor S S' fX).map
      ((derivedZariskiDirectImage S).map (crisModuleComparison S S' fS fX hf F))

end Derived

section GlobalSections

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **The pullback `RΓ(Cris(X/S), ℱ) ⟶ RΓ(Cris(X'/S), f_cris^*ℱ)`** in `D⁺(Ab)`, the
global-sections form of `moduleComparison07Q9`: the pullback
`...SmallSite.derivedCrisPullbackMap` of the underlying abelian sheaf, followed by
`RΓ(Cris(X'/S), -)` of `crisModuleComparison`. -/
def derivedModulePullbackMap (F : ModuleSheaf S') :
    (derivedGlobalSections S').obj ((toAbelianSheaf S').obj F) ⟶
      (derivedGlobalSections S).obj
        ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) :=
  derivedCrisPullbackMap S S' fS fX hf ((toAbelianSheaf S').obj F) ≫
    (derivedGlobalSections S).map (crisModuleComparison S S' fS fX hf F)

end GlobalSections

/-! ### The chain-level form of the conclusion, over an open of `X` -/

/-- **The conclusion of [Stacks, Tag 07Q9] for a chain map of complexes of abelian groups
indexed by `ℕ`**: `q` annihilates every cohomology group of the mapping cone of the map, the
complexes being extended by zero to `ℤ` so that the mapping cone is formed.  This is the form in
which the conclusion is read over a single open of `X`, on sections. -/
def ChainConeAnnihilation (q : ℕ) {K L : CochainComplex AddCommGrpCat.{u + 1} ℕ} (φ : K ⟶ L) :
    Prop :=
  ∀ j : ℤ, (q : ℤ) • 𝟙 ((CochainComplex.mappingCone
    ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).map φ)).homology j) = 0

/-- **The sections over an open `W ⊆ X` of `u_{X/S, *}` of a morphism of complexes of abelian
sheaves on `Cris(X/S)`**, as a chain map of complexes of abelian groups.  For
`ψ : J ⟶ f_{cris, *}J'` a map of injective resolutions this is the map
`Γ(Cris(W/S), J) ⟶ Γ(Cris(W'/S), J')` whose cone [Stacks, Tag 07Q9] bounds, read on sections
over `W` of the Zariski direct image. -/
def sectionsChainMap (W : S'.X.Opens) {K L : CochainComplex (Sheaf (smallTopology S')
    AddCommGrpCat.{u + 1}) ℕ} (ψ : K ⟶ L) :
    ((((sheafSections (opensTopology S') AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex
      _).obj (((zariskiDirectImage S').mapHomologicalComplex _).obj K)) ⟶
      ((((sheafSections (opensTopology S') AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex
        _).obj (((zariskiDirectImage S').mapHomologicalComplex _).obj L)) :=
  (((sheafSections (opensTopology S') AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex
    _).map (((zariskiDirectImage S').mapHomologicalComplex _).map ψ)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
