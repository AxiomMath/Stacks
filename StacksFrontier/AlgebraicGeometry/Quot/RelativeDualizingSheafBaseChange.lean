module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDualizingSheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
import StacksCore.Tactic.StacksAttribute

/-!
# The base change isomorphism of the relative dualizing sheaf (Stacks 0E6R)

Let `f : X ⟶ S` be a family of curves with Cohen–Macaulay fibres equidimensional of dimension one,
`(ω^•_{X/S}, τ)` a relative dualizing complex and `ω_{X/S} = H^{-1}(ω^•_{X/S})` the relative
dualizing sheaf (Stacks 0E6Q). For a morphism of families of curves `X' ⟶ X` over `S' ⟶ S`
(a cartesian square) with projection `g' : X' ⟶ X` and a relative dualizing complex
`(ω^•_{X'/S'}, τ')` of `X'/S'`, this file constructs the canonical base change isomorphism
`ω_{X'/S'} ≅ (g')^* ω_{X/S}`. It is the composite of

* `H^{-1}` of the unique isomorphism of relative dualizing complexes
  `(ω^•_{X'/S'}, τ') ≅ (L(g')^* ω^•_{X/S}, Lg^* τ)` compatible with the traces (Stacks 0E5Z,
  Stacks 0E6C), and
* the canonical identification `H^{-1}(L(g')^* ω^•_{X/S}) ≅ (g')^* ω_{X/S}`: the truncation
  isomorphism `ω^•_{X/S} ≅ ω_{X/S}[1]` (the complex has cohomology only in degree `-1`), the
  commutation of `L(g')^*` with the shift, and the comparison `L(g')^*(ω_{X/S}[0]) ⟶
  ((g')^* ω_{X/S})[0]`, an isomorphism because `ω_{X/S}` is flat over `S` (Stacks 0DKD).

No choice enters beyond the trace-compatible isomorphism of Stacks 0E5Z, which is unique. With
this isomorphism Stacks 0E6R reads: for Gorenstein fibres, `ω_{X/S}` is invertible and the
canonical base change map is an isomorphism.

## Main definitions

* `AlgebraicGeometry.CurveFamily.relativeDualizingComplexBaseChangeIso`: the unique
  trace-compatible isomorphism `ω^•_{X'/S'} ≅ L(g')^* ω^•_{X/S}`.
* `AlgebraicGeometry.CurveFamily.relativeDualizingSheafPullbackComparison`: the canonical
  isomorphism `H^{-1}(L(g')^* ω^•_{X/S}) ≅ (g')^* ω_{X/S}`.
* `AlgebraicGeometry.CurveFamily.relativeDualizingSheafBaseChangeIso`: the base change
  isomorphism `ω_{X'/S'} ≅ (g')^* ω_{X/S}`.

## Main results

* `AlgebraicGeometry.CurveFamily.relativeDualizingComplexBaseChangeIso_spec`: the isomorphism of
  relative dualizing complexes is the unique one compatible with the traces.
* `AlgebraicGeometry.CurveFamily.isInvertibleModule_relativeDualizingSheaf_and_baseChangeIso`:
  Stacks 0E6R.

## References

* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E5Z](https://stacks.math.columbia.edu/tag/0E5Z)
* [Stacks Project, Tag 0E6C](https://stacks.math.columbia.edu/tag/0E6C)
* [Stacks Project, Tag 0E61](https://stacks.math.columbia.edu/tag/0E61)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

open Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- For a morphism of families of curves `X' ⟶ X` over `S' ⟶ S` and relative dualizing complexes
`(ω^•_{X/S}, τ)`, `(ω^•_{X'/S'}, τ')`, the isomorphism `ω^•_{X'/S'} ≅ L(g')^* ω^•_{X/S}` of
relative dualizing complexes of `X'/S'` (the base change `(L(g')^* ω^•_{X/S}, Lg^* τ)` is one,
Stacks 0E6C) compatible with the traces. It is unique (Stacks 0E5Z,
`AlgebraicGeometry.CurveFamily.relativeDualizingComplexBaseChangeIso_spec`). -/
def CurveFamily.relativeDualizingComplexBaseChangeIso {X X' : CurveFamily B hZ}
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) (φ : X' ⟶ X)
    (D' : RelativeDualizingComplex B.contains_terminal X'.toBase X'.proper X'.flat
      X'.finitePresentation) :
    D'.ω ≅ (D.baseChange φ.cartesian).ω :=
  (RelativeDualizingComplex.existsUnique_iso_of_relativeDualizingComplex D'
    (D.baseChange φ.cartesian)).exists.choose

/-- The isomorphism `ω^•_{X'/S'} ≅ L(g')^* ω^•_{X/S}` is compatible with the traces, and it is the
only isomorphism which is (Stacks 0E5Z). -/
theorem CurveFamily.relativeDualizingComplexBaseChangeIso_spec {X X' : CurveFamily B hZ}
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) (φ : X' ⟶ X)
    (D' : RelativeDualizingComplex B.contains_terminal X'.toBase X'.proper X'.flat
      X'.finitePresentation) (e : D'.ω ≅ (D.baseChange φ.cartesian).ω) :
    (derivedModulePushforward B integerBase hZ X'.toBase).map e.hom ≫
        (D.baseChange φ.cartesian).τ = D'.τ ↔
      e = relativeDualizingComplexBaseChangeIso D φ D' := by
  have h := RelativeDualizingComplex.existsUnique_iso_of_relativeDualizingComplex D'
    (D.baseChange φ.cartesian)
  refine ⟨fun he => h.unique he h.exists.choose_spec, ?_⟩
  rintro rfl
  exact h.exists.choose_spec

/-- The truncation isomorphism `E ≅ (H^{-1}(E)[0])[1]` of an object of the derived category with
cohomology only in degree `-1`: `E ≅ τ^{<0} E ≅ τ^{≥ -1} τ^{<0} E ≅ H^{-1}(E)[1]`. -/
def CurveFamily.isoSingleShiftOfIsGEOfIsLE {Z : AlgebraicSpaces B integerBase hZ}
    [HasDerivedCategory (Space.Modules.{u, u} B integerBase hZ Z.1 Z.2)]
    (E : DerivedCategory (Space.Modules.{u, u} B integerBase hZ Z.1 Z.2))
    [E.IsGE (-1)] [E.IsLE (-1)] :
    E ≅ ((DerivedCategory.singleFunctor _ 0).obj
      ((DerivedCategory.homologyFunctor _ (-1)).obj E))⟦(1 : ℤ)⟧ :=
  haveI : IsIso ((DerivedCategory.TStructure.t.truncLTι (-1 + 1)).app E) :=
    (DerivedCategory.TStructure.t.isLE_iff_isIso_truncLTι_app (-1) (-1 + 1) rfl E).1 inferInstance
  haveI : DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncLT (-1 + 1)).obj E) (-1) :=
    haveI : DerivedCategory.TStructure.t.IsGE
        ((𝟭 (DerivedCategory (Space.Modules.{u, u} B integerBase hZ Z.1 Z.2))).obj E) (-1) :=
      inferInstanceAs (E.IsGE (-1))
    DerivedCategory.TStructure.t.isGE_of_iso
      (asIso ((DerivedCategory.TStructure.t.truncLTι (-1 + 1)).app E)).symm (-1)
  haveI : IsIso ((DerivedCategory.TStructure.t.truncGEπ (-1)).app
      ((DerivedCategory.TStructure.t.truncLT (-1 + 1)).obj E)) :=
    (DerivedCategory.TStructure.t.isGE_iff_isIso_truncGEπ_app (-1) _).1 inferInstance
  (asIso ((DerivedCategory.TStructure.t.truncLTι (-1 + 1)).app E)).symm ≪≫
    asIso ((DerivedCategory.TStructure.t.truncGEπ (-1)).app
      ((DerivedCategory.TStructure.t.truncLT (-1 + 1)).obj E)) ≪≫
    (DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor (-1)).app E ≪≫
    (((DerivedCategory.singleFunctors _).shiftIso 1 (-1) 0 (by norm_num)).app _).symm

/-- The comparison `L(g')^*(𝓕[0]) ≅ ((g')^* 𝓕)[0]` for a quasi-coherent module `𝓕` on `X` flat
over `S` and a morphism of families of curves `X' ⟶ X` with projection `g'` (Stacks 0DKD): the
comparison map from the derived to the underived pullback, an isomorphism by flatness. -/
def CurveFamily.smallEtaleDerivedModulePullbackSingleIso {X X' : CurveFamily B hZ} (φ : X' ⟶ X)
    (F : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hFq : F.IsQuasicoherentOnSite)
    (hflat : Space.IsFlatOver B integerBase hZ X.total.2 X.toBase.hom F) :
    (smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B integerBase hZ X.total)) 0).obj F) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B integerBase hZ X'.total)) 0).obj
        ((modulePullback B integerBase hZ φ.totalMap).obj F) :=
  haveI : F.IsQuasicoherentOnSite := hFq
  let pb :=
    (Space.smallEtaleRingedToposHom B integerBase hZ φ.totalMap).toModulesHom.pullbackModules
  haveI hadd : pb.Additive := RingedToposHom.pullbackModules_additive
    (Space.smallEtaleRingedToposHom B integerBase hZ φ.totalMap)
  haveI : pb.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive pb
  let K₀ := (CochainComplex.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B integerBase hZ X.total)) 0).obj F
  haveI : IsIso ((smallEtaleDerivedModulePullbackComparison B integerBase hZ φ.totalMap).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₀)) :=
    isIso_smallEtaleDerivedModulePullbackComparison_of_isFlatOver φ.totalMap
      X'.toBase X.toBase (schemeSpaceMap φ.baseMap) φ.cartesian
      (torIndependent_of_isFlat_left X.toBase (schemeSpaceMap φ.baseMap) X.flat) F hflat
  have hpb : pb.obj F = (modulePullback B integerBase hZ φ.totalMap).obj F :=
    congrArg (fun h => h.pullbackModules.obj F)
      (smallEtaleRingedToposHom_toModulesHom_eq φ.totalMap)
  (smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F) ≪≫
    (smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).mapIso
      ((DerivedCategory.quotientCompQhIso _).app K₀).symm ≪≫
    asIso ((smallEtaleDerivedModulePullbackComparison B integerBase hZ φ.totalMap).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₀)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    (DerivedCategory.Q).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex pb (ComplexShape.up ℤ) 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (eqToIso hpb)

/-- The canonical isomorphism `H^{-1}(L(g')^* ω^•_{X/S}) ≅ (g')^* ω_{X/S}` for a family of curves
with Cohen–Macaulay fibres equidimensional of dimension one and a morphism of families of curves
`X' ⟶ X` with projection `g'`: `ω^•_{X/S} = ω_{X/S}[1]` by truncation, `L(g')^*` commutes with
the shift, and `L(g')^*(ω_{X/S}[0]) = ((g')^* ω_{X/S})[0]` because `ω_{X/S}` is flat over `S`. -/
def CurveFamily.relativeDualizingSheafPullbackComparison (X : CurveFamily B hZ)
    (hcm : Space.IsCohenMacaulay B integerBase hZ X.toBase.hom)
    (hdim : Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) {X' : CurveFamily B hZ} (φ : X' ⟶ X) :
    (DerivedCategory.homologyFunctor _ (-1)).obj
        ((smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap).obj D.ω) ≅
      (modulePullback B integerBase hZ φ.totalMap).obj (X.relativeDualizingSheaf D) :=
  haveI hvf := X.isZero_homology_and_isFlatOver_relativeDualizingComplex ⟨hcm, hdim⟩ D
  haveI : D.ω.IsGE (-1) := (DerivedCategory.isGE_iff _ _).2 fun i hi => hvf.1 i (by omega)
  haveI : D.ω.IsLE (-1) := (DerivedCategory.isLE_iff _ _).2 fun i hi => hvf.1 i (by omega)
  let L := smallEtaleDerivedModulePullback B integerBase hZ φ.totalMap
  (DerivedCategory.homologyFunctor _ (-1)).mapIso
      (L.mapIso (isoSingleShiftOfIsGEOfIsLE D.ω) ≪≫ (L.commShiftIso (1 : ℤ)).app _ ≪≫
        (shiftFunctor _ (1 : ℤ)).mapIso
          (smallEtaleDerivedModulePullbackSingleIso φ (X.relativeDualizingSheaf D)
            ((show QcohDerived B integerBase hZ X.total D.ω from
              derivedCategoryB_of_isPseudoCoherent_unconditional B integerBase hZ X.total.1
                X.total.2 D.ω D.isPerfectRelativeTo.1) (-1)) hvf.2)) ≪≫
    homologyNegOneSingleShiftIso _

/-- **The base change isomorphism of the relative dualizing sheaf.** For a family of curves
`X ⟶ S` with Cohen–Macaulay fibres equidimensional of dimension one, a morphism of families of
curves `X' ⟶ X` over `S' ⟶ S` with projection `g'`, and relative dualizing complexes
`(ω^•_{X/S}, τ)`, `(ω^•_{X'/S'}, τ')`, the isomorphism `ω_{X'/S'} ≅ (g')^* ω_{X/S}`: `H^{-1}` of
the unique trace-compatible isomorphism `ω^•_{X'/S'} ≅ L(g')^* ω^•_{X/S}` (Stacks 0E5Z, 0E6C),
followed by the canonical identification `H^{-1}(L(g')^* ω^•_{X/S}) ≅ (g')^* ω_{X/S}`. -/
def CurveFamily.relativeDualizingSheafBaseChangeIso (X : CurveFamily B hZ)
    (hcm : Space.IsCohenMacaulay B integerBase hZ X.toBase.hom)
    (hdim : Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) {X' : CurveFamily B hZ} (φ : X' ⟶ X)
    (D' : RelativeDualizingComplex B.contains_terminal X'.toBase X'.proper X'.flat
      X'.finitePresentation) :
    X'.relativeDualizingSheaf D' ≅
      (modulePullback B integerBase hZ φ.totalMap).obj (X.relativeDualizingSheaf D) :=
  (DerivedCategory.homologyFunctor _ (-1)).mapIso (relativeDualizingComplexBaseChangeIso D φ D') ≪≫
    X.relativeDualizingSheafPullbackComparison hcm hdim D φ

/-- Let `f : X ⟶ S` be a family of curves with Gorenstein fibres equidimensional of dimension
one (`Curves^{Gorenstein, 1}` of Stacks 0E6M), and `(ω^•_{X/S}, τ)` a relative dualizing complex
(Stacks 0E5X; one exists by Stacks 0E61, `AlgebraicGeometry.Space.RelativeDualizingComplex.nonempty`,
and any two are uniquely isomorphic by Stacks 0E5Z). Then the relative dualizing sheaf
`ω_{X/S} = H^{-1}(ω^•_{X/S})` (Stacks 0E6Q) is an invertible `𝒪_X`-module, and its formation
commutes with arbitrary base change: for every morphism of families of curves `X' ⟶ X` over
an arbitrary `S' ⟶ S` (a cartesian square, projection `g'`) and every relative dualizing complex
`(ω^•_{X'/S'}, τ')`, the canonical base change map
`AlgebraicGeometry.CurveFamily.relativeDualizingSheafBaseChangeIso : ω_{X'/S'} ≅ (g')^* ω_{X/S}`
is an isomorphism. That map is `H^{-1}(e)` followed by the canonical identification
`H^{-1}(L(g')^* ω^•_{X/S}) ≅ (g')^* ω_{X/S}`, where `e` is the unique isomorphism of relative
dualizing complexes `ω^•_{X'/S'} ≅ L(g')^* ω^•_{X/S}` compatible with the traces, as stated.

As in Stacks, `X` is an algebraic space, `S` an arbitrary scheme, and the Gorenstein and
dimension conditions are quantified over the points of `X`, so `f` need not be surjective. -/
@[stacks 0E6R]
theorem CurveFamily.isInvertibleModule_relativeDualizingSheaf_and_baseChangeIso
    (X : CurveFamily B hZ) (hX : IsGorensteinDimOneFamily B hZ X)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    Space.IsInvertibleModule X.total (X.relativeDualizingSheaf D) ∧
      ∀ {X' : CurveFamily B hZ} (φ : X' ⟶ X)
        (D' : RelativeDualizingComplex B.contains_terminal X'.toBase X'.proper X'.flat
          X'.finitePresentation),
        ∃ e : D'.ω ≅ (D.baseChange φ.cartesian).ω,
          (∀ e' : D'.ω ≅ (D.baseChange φ.cartesian).ω,
            (derivedModulePushforward B integerBase hZ X'.toBase).map e'.hom ≫
                (D.baseChange φ.cartesian).τ = D'.τ ↔ e' = e) ∧
          IsIso (X.relativeDualizingSheafBaseChangeIso
              (Space.isCohenMacaulay_of_isGorenstein B integerBase hZ hX.1) hX.2 D φ D').hom ∧
          (X.relativeDualizingSheafBaseChangeIso
              (Space.isCohenMacaulay_of_isGorenstein B integerBase hZ hX.1) hX.2 D φ D').hom =
            (DerivedCategory.homologyFunctor _ (-1)).map e.hom ≫
              (X.relativeDualizingSheafPullbackComparison
                (Space.isCohenMacaulay_of_isGorenstein B integerBase hZ hX.1) hX.2 D φ).hom :=
  ⟨(X.isInvertibleModule_relativeDualizingSheaf hX D).1, fun φ D' =>
    ⟨relativeDualizingComplexBaseChangeIso D φ D',
      relativeDualizingComplexBaseChangeIso_spec D φ D', inferInstance, rfl⟩⟩

end AlgebraicGeometry

end
