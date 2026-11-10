module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionSheafHomRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectAffineCriterion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIso
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChange
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagonal condition of a relative dualizing complex on an affine chart

Let `f : X ⟶ S` be a morphism of schemes, `W ⊆ X ×_S X` an open through which the relative
diagonal factors as a closed immersion `Δ : X ⟶ W`, and `(K, ξ)` a pair as in Stacks 0E2T. Let
`U ⊆ X` and `V ⊆ S` be affine opens with `U ⊆ f⁻¹(V)`. This file moves the second condition of
Stacks 0E2T from `W` to the affine scheme `U ×_V U`, which is the first step of the proof of
Stacks 0E2U.

By Stacks 0A77 the derived internal Hom `R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)` is
`Δ_* R ℰom(𝒪_X, L pr₁^*K|_W)`, with `R ℰom(𝒪_X, -)` derived sheaf Hom with exact support. So
if `ξ` defines an isomorphism, the cohomology sheaves of `R ℰom(𝒪_X, L pr₁^*K|_W)` are those of
`𝒪_X[0]` after `Δ_*`, which is fully faithful on modules, and therefore
`R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`. Derived sheaf Hom with exact support commutes with
restriction to an open of the ambient scheme, and only sees an open neighbourhood of the closed
subscheme; reading it on `W ∩ (U ×_V U)`, both as an open of `W` and as an open of `U ×_V U`,
transfers the statement to the diagonal `U ⟶ U ×_V U`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.chartSquare` is `U ×_V U`, with its open
  immersion `chartSquareι` into `X ×_S X` and the diagonal `chartDiagonal : U ⟶ U ×_V U`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.chartOpenIso` identifies `W ∩ (U ×_V U)` as an
  open of `W` with the same open of `U ×_V U`, and `chartDiagIso` the corresponding preimages,
  both of which are `U`.
* `AlgebraicGeometry.Scheme.structureSingle` is `𝒪_Y[0]` in `D(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_diagonalExactSupport_iso`: if `ξ`
  defines an isomorphism, then `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_chartExactSupport_iso`: the same on the
  chart `U ×_V U`, for any object agreeing with `L pr₁^*K|_W` on `W ∩ (U ×_V U)`.

## Implementation notes

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, the model at
which `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex` and the restriction and transport
isomorphisms of `Stacks.Duality.ClosedImmersionRestriction` are stated.

## References

* [Stacks Project, Lemma 48.28.2 (Tag 0E2U)](https://stacks.math.columbia.edu/tag/0E2U)
* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)

/-- `f|_U : U ⟶ V`. -/
abbrev chartMap : U.toScheme ⟶ V.toScheme := f.resLE V U hUV

/-- The fibre product `U ×_V U`. -/
abbrev chartSquare : Scheme.{u} := pullback (chartMap hUV) (chartMap hUV)

/-- The open immersion `U ×_V U ⟶ X ×_S X`. -/
abbrev chartSquareι : chartSquare hUV ⟶ pullback f f :=
  pullback.map (chartMap hUV) (chartMap hUV) f f U.ι U.ι V.ι
    (Scheme.Hom.resLE_comp_ι f hUV) (Scheme.Hom.resLE_comp_ι f hUV)

/-- The map `U ×_V U ⟶ X ×_S X` is an open immersion. -/
instance : IsOpenImmersion (chartSquareι hUV) :=
  Scheme.pullback_map_isOpenImmersion _ _ f f U.ι U.ι V.ι
    (Scheme.Hom.resLE_comp_ι f hUV) (Scheme.Hom.resLE_comp_ι f hUV)

/-- The relative diagonal `U ⟶ U ×_V U` of `f|_U`. -/
abbrev chartDiagonal : U.toScheme ⟶ chartSquare hUV := pullback.diagonal (chartMap hUV)

/-- The diagonal of `f|_U` is the diagonal of `f` restricted to `U`. -/
theorem chartDiagonal_comp_chartSquareι :
    chartDiagonal hUV ≫ chartSquareι hUV = U.ι ≫ pullback.diagonal f := by
  apply pullback.hom_ext <;> simp

include hU hV in
/-- `U ×_V U` is affine. -/
theorem isAffine_chartSquare : IsAffine (chartSquare hUV) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  infer_instance

include hU hV in
/-- The diagonal `U ⟶ U ×_V U` is a closed immersion, `f|_U` being a morphism of affine
schemes. -/
@[ega "IV 16.3.1" "special case"]
theorem isClosedImmersion_chartDiagonal : IsClosedImmersion (chartDiagonal hUV) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  infer_instance

/-! ### The chart of `W` over `U ×_V U` -/

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

variable (D : DiagonalOpen f)

/-- The open `W ∩ (U ×_V U)` of `W`. -/
abbrev chartOpen : D.W.Opens := D.ι ⁻¹ᵁ (chartSquareι hUV).opensRange

/-- The open `W ∩ (U ×_V U)` of `U ×_V U`. -/
abbrev chartOpen' : (chartSquare hUV).Opens := (chartSquareι hUV) ⁻¹ᵁ D.ι.opensRange

/-- `W ∩ (U ×_V U)` has the same image in `X ×_S X` from either side. -/
theorem range_chartOpen_ι_comp :
    Set.range ((D.chartOpen hUV).ι ≫ D.ι) =
      Set.range ((D.chartOpen' hUV).ι ≫ chartSquareι hUV) := by
  have h₁ : ((D.chartOpen hUV).ι ≫ D.ι).opensRange =
      D.ι.opensRange ⊓ (chartSquareι hUV).opensRange := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf]
  have h₂ : ((D.chartOpen' hUV).ι ≫ chartSquareι hUV).opensRange =
      (chartSquareι hUV).opensRange ⊓ D.ι.opensRange := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf]
  simpa using congrArg SetLike.coe (h₁.trans (inf_comm _ _ |>.trans h₂.symm))

/-- `W ∩ (U ×_V U)` read as an open of `W` and as an open of `U ×_V U`. -/
def chartOpenIso : (D.chartOpen hUV).toScheme ≅ (D.chartOpen' hUV).toScheme :=
  IsOpenImmersion.isoOfRangeEq _ _ (D.range_chartOpen_ι_comp hUV)

/-- `chartOpenIso` is compatible with the two open immersions into `X ×_S X`. -/
@[reassoc (attr := simp)]
theorem chartOpenIso_hom_fac :
    (D.chartOpenIso hUV).hom ≫ (D.chartOpen' hUV).ι ≫ chartSquareι hUV =
      (D.chartOpen hUV).ι ≫ D.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The diagonal of `U` lands in `W ∩ (U ×_V U)`. -/
theorem chartDiagonal_preimage_chartOpen' :
    chartDiagonal hUV ⁻¹ᵁ D.chartOpen' hUV = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  change (chartSquareι hUV) (chartDiagonal hUV x) ∈ Set.range D.ι
  have h := congrArg (fun k : U.toScheme ⟶ pullback f f => k x)
    (chartDiagonal_comp_chartSquareι hUV)
  simp only [Scheme.Hom.comp_apply] at h
  rw [h, ← D.fac, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

/-- The preimage of `W ∩ (U ×_V U)` under `Δ : X ⟶ W` is `U`. -/
theorem diag_preimage_chartOpen :
    D.diag ⁻¹ᵁ D.chartOpen hUV = U := by
  ext x
  change D.ι (D.diag x) ∈ Set.range (chartSquareι hUV) ↔ x ∈ U
  rw [← Scheme.Hom.comp_apply, D.fac]
  constructor
  · rintro ⟨p, hp⟩
    have h := congrArg (pullback.fst f f) hp
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_fst] at h
    simp only [pullback.lift_fst, Scheme.Hom.comp_apply] at h
    change U.ι _ = x at h
    rw [← h]
    exact ((pullback.fst (chartMap hUV) (chartMap hUV)) p).2
  · intro hx
    exact ⟨chartDiagonal hUV ⟨x, hx⟩, congrArg (fun k : U.toScheme ⟶ pullback f f => k ⟨x, hx⟩)
      (chartDiagonal_comp_chartSquareι hUV)⟩

/-- Both preimages of `W ∩ (U ×_V U)` have image `U` in `X`. -/
theorem range_diag_preimage_ι :
    Set.range (D.diag ⁻¹ᵁ D.chartOpen hUV).ι =
      Set.range ((chartDiagonal hUV ⁻¹ᵁ D.chartOpen' hUV).ι ≫ U.ι) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Opens.range_ι, D.chartDiagonal_preimage_chartOpen' hUV, D.diag_preimage_chartOpen hUV]
  simp

/-- `U` read as the preimage of `W ∩ (U ×_V U)` under `Δ : X ⟶ W` and under the diagonal
`U ⟶ U ×_V U`. -/
def chartDiagIso : (D.diag ⁻¹ᵁ D.chartOpen hUV).toScheme ≅
    (chartDiagonal hUV ⁻¹ᵁ D.chartOpen' hUV).toScheme :=
  IsOpenImmersion.isoOfRangeEq _ _ (D.range_diag_preimage_ι hUV)

/-- `chartDiagIso` is compatible with the two open immersions into `X`. -/
@[reassoc (attr := simp)]
theorem chartDiagIso_hom_fac :
    (D.chartDiagIso hUV).hom ≫ (chartDiagonal hUV ⁻¹ᵁ D.chartOpen' hUV).ι ≫ U.ι =
      (D.diag ⁻¹ᵁ D.chartOpen hUV).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The two restricted diagonals agree along the two identifications. -/
theorem diag_restrict_comp_chartOpenIso :
    (D.diag ∣_ D.chartOpen hUV) ≫ (D.chartOpenIso hUV).hom =
      (D.chartDiagIso hUV).hom ≫ (chartDiagonal hUV ∣_ D.chartOpen' hUV) := by
  rw [← cancel_mono ((D.chartOpen' hUV).ι ≫ chartSquareι hUV)]
  simp only [Category.assoc, chartOpenIso_hom_fac, morphismRestrict_ι_assoc]
  rw [chartDiagonal_comp_chartSquareι, chartDiagIso_hom_fac_assoc, D.fac]

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

/-! ### Objects isomorphic to the structure sheaf placed in degree zero -/

namespace AlgebraicGeometry.Scheme

/-- `𝒪_Y` placed in degree zero, as an object of `D(𝒪_Y)`. -/
abbrev structureSingle (Y : Scheme.{u}) : DerivedCategory Y.Modules :=
  (DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)

/-- Restriction along an open immersion carries `𝒪_Y[0]` to `𝒪_{Y'}[0]`. -/
def restrictStructureSingleIso {Y' Y : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j] :
    (Modules.restrictFunctor j).mapDerivedCategory.obj (structureSingle Y) ≅
      structureSingle Y' :=
  ((Modules.restrictFunctor j).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor Y'.Modules 0).mapIso (Modules.restrictUnitIso j)

/-- An object whose restriction along an isomorphism of schemes is `𝒪[0]` is itself `𝒪[0]`. -/
theorem nonempty_iso_structureSingle_of_restrict {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsIso g]
    (T : DerivedCategory Y.Modules)
    (h : Nonempty ((Modules.restrictFunctor g).mapDerivedCategory.obj T ≅ structureSingle Y')) :
    Nonempty (T ≅ structureSingle Y) := by
  obtain ⟨e⟩ := h
  refine ⟨(Stacks.Homology.mapDerivedCategoryIdIso.app T).symm ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Modules.restrictFunctorCompPushforwardIso g).symm).app T ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).app T ≪≫
    (Modules.pushforward g).mapDerivedCategory.mapIso e ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Modules.pushforwardIsoRestrictInv g)).app _ ≪≫ restrictStructureSingleIso (inv g)⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-! ### `R ℰom(𝒪_X, L pr₁^*K|_W)` -/

/-- The closed immersion `Δ : X ⟶ W`, read as a closed quotient morphism of ringed spaces. -/
abbrev diagQuotient : RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.{u} :=
  Stacks.ClosedImmersion.closedQuotientOfClosedImmersion D.diag

/-- `R ℰom(𝒪_X, L pr₁^*K|_W)`, derived sheaf Hom with exact support along `Δ : X ⟶ W`. -/
abbrev diagonalExactSupport (K : DerivedCategory X.Modules) : DerivedCategory X.Modules :=
  D.diagQuotient.derivedSheafHomExactSupport.obj (D.derivedPullbackProj K)

/-- `Δ_*𝒪_X` is the derived pushforward of `𝒪_X[0]` along `Δ`. -/
def diagonalObjectIso :
    D.diagonalObject ≅
      (RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i).mapDerivedCategory.obj
        (structureSingle X) :=
  ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm ≪≫
    (((RingedSpaceModuleAdjunction.modulePushforward
      D.diagQuotient.i).mapDerivedCategorySingleFunctor 0).app (SheafOfModules.unit _)).symm

/-- **`R ℰom(𝒪_X, L pr₁^*K|_W)` is `𝒪_X[0]`** when `ξ` defines an isomorphism
`Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`: by Stacks 0A77 the right-hand side is
`Δ_* R ℰom(𝒪_X, L pr₁^*K|_W)`, `Δ_*` commutes with cohomology and is fully faithful on modules,
so the cohomology of `R ℰom(𝒪_X, L pr₁^*K|_W)` is that of `𝒪_X[0]`. -/
theorem nonempty_diagonalExactSupport_iso (K : DerivedCategory X.Modules)
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) (h : IsIso (D.diagonalAction K ξ)) :
    Nonempty (D.diagonalExactSupport K ≅ structureSingle X) := by
  let F := RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i
  let E := D.diagonalExactSupport K
  have e : F.mapDerivedCategory.obj (structureSingle X) ≅ F.mapDerivedCategory.obj E :=
    D.diagonalObjectIso.symm ≪≫ @asIso _ _ _ _ (D.diagonalAction K ξ) h ≪≫
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).mapIso
        D.diagonalObjectIso.symm.op).app (D.derivedPullbackProj K) ≪≫
      (D.diagQuotient.derivedSheafHomExactSupportPushforwardNatIso.app
        (D.derivedPullbackProj K)).symm
  let hff := Stacks.ToposBridge.fullyFaithfulModulePushforward D.diag.toLRSHom.toShHom
    (IsClosedImmersion.isClosedEmbedding D.diag).isInducing
    (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom D.diag)
  have hH : ∀ n : ℤ, (DerivedCategory.homologyFunctor X.Modules n).obj (structureSingle X) ≅
      (DerivedCategory.homologyFunctor X.Modules n).obj E := fun n =>
    hff.preimageIso <|
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).app
        (structureSingle X)).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
        (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).app E
  obtain ⟨e'⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero E 0
    (fun j hj => by
      refine IsZero.of_iso ?_ (hH j).symm
      exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
        (SheafOfModules.unit X.ringCatSheaf) j hj).of_iso
        ((DerivedCategory.homologyFunctor _ j).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
            (SheafOfModules.unit X.ringCatSheaf)) ≪≫
          (DerivedCategory.homologyFunctorFactors _ j).app _))
  exact ⟨e' ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
    ((hH 0).symm ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _)⟩

variable {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hUV : U ≤ f ⁻¹ᵁ V)

open Stacks.Duality.ClosedImmersionRestriction in
include hU hV in
/-- **Reading `R ℰom(𝒪_X, L pr₁^*K|_W)` on the chart `U ×_V U`.** If `ξ` defines an
isomorphism, then for any object `L'` of `D(𝒪_{U ×_V U})` which agrees with `L pr₁^*K|_W` on
`W ∩ (U ×_V U)`, derived sheaf Hom with exact support along the diagonal `U ⟶ U ×_V U` carries
`L'` to `𝒪_U[0]`. -/
theorem nonempty_chartExactSupport_iso (K : DerivedCategory X.Modules)
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) (h : IsIso (D.diagonalAction K ξ))
    (L' : DerivedCategory (chartSquare hUV).Modules)
    (eL : (Modules.restrictFunctor (D.chartOpen hUV).ι).mapDerivedCategory.obj
        (D.derivedPullbackProj K) ≅
      (Modules.pushforward (D.chartOpenIso hUV).inv).mapDerivedCategory.obj
        ((Modules.restrictFunctor (D.chartOpen' hUV).ι).mapDerivedCategory.obj L')) :
    haveI := isClosedImmersion_chartDiagonal hU hV hUV
    Nonempty ((cq (chartDiagonal hUV)).derivedSheafHomExactSupport.obj L' ≅
      structureSingle U.toScheme) := by
  have := isClosedImmersion_chartDiagonal hU hV hUV
  obtain ⟨eE⟩ := D.nonempty_diagonalExactSupport_iso K ξ h
  let V₁ := D.chartOpen hUV
  let V₂ := D.chartOpen' hUV
  let d := chartDiagonal hUV
  let T := (cq d).derivedSheafHomExactSupport.obj L'
  -- `R ℰom(𝒪_X, L)` restricted to `Δ⁻¹(V₁)` is `𝒪[0]`.
  have e₁ : (Modules.restrictFunctor (D.diag ⁻¹ᵁ V₁).ι).mapDerivedCategory.obj
      (D.diagonalExactSupport K) ≅ structureSingle (D.diag ⁻¹ᵁ V₁).toScheme :=
    (Modules.restrictFunctor (D.diag ⁻¹ᵁ V₁).ι).mapDerivedCategory.mapIso eE ≪≫
      restrictStructureSingleIso _
  -- and it is `R ℰom(𝒪_U, -)` of `L'|_{V₂}`, transported.
  have e₂ : (Modules.restrictFunctor (D.diag ⁻¹ᵁ V₁).ι).mapDerivedCategory.obj
      (D.diagonalExactSupport K) ≅
      (Modules.pushforward (D.chartDiagIso hUV).inv).mapDerivedCategory.obj
        ((Modules.restrictFunctor (d ⁻¹ᵁ V₂).ι).mapDerivedCategory.obj T) :=
    (derivedSheafHomRestrictIso D.diag V₁).app (D.derivedPullbackProj K) ≪≫
      (cq (D.diag ∣_ V₁)).derivedSheafHomExactSupport.mapIso eL ≪≫
      (derivedSheafHomTransportIso (D.diag ∣_ V₁) (d ∣_ V₂) (D.chartDiagIso hUV)
        (D.chartOpenIso hUV) (D.diag_restrict_comp_chartOpenIso hUV)).app
          ((Modules.restrictFunctor V₂.ι).mapDerivedCategory.obj L') ≪≫
      (Modules.pushforward (D.chartDiagIso hUV).inv).mapDerivedCategory.mapIso
        ((derivedSheafHomRestrictIso d V₂).app L').symm
  let g := (D.chartDiagIso hUV).hom ≫ (d ⁻¹ᵁ V₂).ι
  have e₃ : (Modules.restrictFunctor g).mapDerivedCategory.obj T ≅
      structureSingle (D.diag ⁻¹ᵁ V₁).toScheme :=
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Modules.restrictFunctorComp (D.chartDiagIso hUV).hom (d ⁻¹ᵁ V₂).ι)).app T ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (Modules.restrictFunctor (d ⁻¹ᵁ V₂).ι)
        (Modules.restrictFunctor (D.chartDiagIso hUV).hom)).app T ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv
          (D.chartDiagIso hUV))).app _ ≪≫ e₂.symm ≪≫ e₁
  have htop : d ⁻¹ᵁ V₂ = ⊤ := D.chartDiagonal_preimage_chartOpen' hUV
  have hιiso : IsIso (d ⁻¹ᵁ V₂).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨inferInstance, ⟨fun x => ⟨⟨x, by simp [htop]⟩, rfl⟩⟩⟩
  exact nonempty_iso_structureSingle_of_restrict g T ⟨e₃⟩

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
