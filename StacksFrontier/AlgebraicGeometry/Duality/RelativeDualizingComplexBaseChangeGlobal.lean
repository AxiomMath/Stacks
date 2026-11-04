module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalGlueing
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRestrict
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChangeFull
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen

/-!
# Base change of relative dualizing complexes

Stacks 0E2Y.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect
open scoped TensorProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Dualizing.IsPostcompGenerator

variable {C E : Type*} [Category* C] [Category* E]

/-- Generators are unchanged by applying a functor to a postcomposite with an isomorphism. -/
theorem map_comp_iso_iff (F : C ⥤ E) {X Y Y' : C} (x : X ⟶ Y) (b : Y ≅ Y') :
    IsPostcompGenerator (F.map (x ≫ b.hom)) ↔ IsPostcompGenerator (F.map x) := by
  rw [F.map_comp]
  exact ⟨fun h => (h.of_conj (Iso.refl _) (F.mapIso b).symm (by simp)),
    fun h => h.comp_iso (F.mapIso b)⟩

end Dualizing.IsPostcompGenerator

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- `R ℰom(𝒪_X, L pr₁^*K|_W)` only depends on the first projection of the diagonal open. -/
def diagonalExactSupportReindexIso {V : Scheme.{u}} (D : DiagonalOpen f) (a : X ⟶ V)
    (j : V ⟶ S) [IsOpenImmersion j] (e : f = a ≫ j) (K : DerivedCategory X.Modules) :
    (D.reindex a j e).diagonalExactSupport K ≅ D.diagonalExactSupport K :=
  D.diagQuotient.derivedSheafHomExactSupport.mapIso
    (eqToIso (congrArg (fun p : D.W ⟶ X => (derivedPullback p.toLRSHom.toShHom).obj K)
      (D.reindex_proj a j e)))

/-- The derived pullback `L pr₁^*K` of `K` to the diagonal open is unchanged by reindexing it
along a factorisation `f = a ≫ j` through an open immersion `j`. -/
theorem derivedPullbackProj_reindex_eq {V : Scheme.{u}} (D : DiagonalOpen f) (a : X ⟶ V)
    (j : V ⟶ S) [IsOpenImmersion j] (e : f = a ≫ j) (K : DerivedCategory X.Modules) :
    D.derivedPullbackProj K = (D.reindex a j e).derivedPullbackProj K :=
  congrArg (fun p : D.W ⟶ X => (derivedPullback p.toLRSHom.toShHom).obj K)
    (D.reindex_proj a j e).symm

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

namespace AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

variable {X S V : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]

/-- **A relative dualizing complex over an open of the base.** If `f = a ≫ j` with `j : V ⟶ S`
an open immersion and `X` quasi-compact, a relative dualizing complex for `f` relative to `W`
is one for `a` relative to the same `W`. -/
theorem reindex [CompactSpace X] {D : DiagonalOpen f} {K : DerivedCategory X.Modules}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (a : X ⟶ V) (j : V ⟶ S) [IsOpenImmersion j] (e : f = a ≫ j) [Flat a]
    [LocallyOfFinitePresentation a] :
    IsRelativeDualizingComplex a
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage V.toRingedSpace a.base)) (D.reindex a j e) K
      (ξ ≫ eqToHom (D.derivedPullbackProj_reindex_eq a j e K)) := by
  have h₁ := hK.isPerfectRelativeTo
  have h₂ : a.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
      (RingedSpace.inverseImage V.toRingedSpace a.base)) K :=
    (isPerfectRelativeTo_baseOpen_iff a j e.symm K).1 h₁
  have h₃ := (D.isIso_diagonalAction_iff_of_proj_eq K (D.reindex a j e).proj (D.reindex_proj a j e)
    (ξ ≫ eqToHom (D.derivedPullbackProj_reindex_eq a j e K)) ξ
    (comp_eqToHom_heq _ _)).2 hK.isIso_diagonalAction
  constructor
  · exact h₂
  · unfold DiagonalOpen.diagonalAction
    convert h₃ using 2

end AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

/-! ### The charts -/

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (hpb : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f]
  (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
  (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb)
  {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
  {V' : S'.Opens} (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V)

/-- The chart `U' = g'⁻¹(U) ∩ f'⁻¹(V')` of `X'`, which is `U ×_V V'`. -/
abbrev chartBaseChange : X'.Opens := g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V'

/-- `g'|_{U'} : U' ⟶ U`. -/
abbrev chartBaseChangeHom : (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).toScheme ⟶
    U.toScheme :=
  g'.resLE U _ inf_le_left

/-- `g'|_{U'} ≫ (U ⊆ X) = (U' ⊆ X') ≫ g'`. -/
theorem chartBaseChangeHom_ι :
    chartBaseChangeHom (g' := g') (f' := f') (U := U) (V' := V') ≫ U.ι =
      (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι ≫ g' :=
  Scheme.Hom.resLE_comp_ι g' _

omit [Flat f] [LocallyOfFinitePresentation f] in
include hpb in
/-- `U' = U ×_V V'`. -/
theorem isPullback_chart :
    IsPullback (chartBaseChangeHom (g' := g') (f' := f') (U := U) (V' := V'))
      (f'.resLE V' (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')) inf_le_right)
      (f.resLE V U hUV) (g.resLE V V' hV'V) :=
  Scheme.Hom.isPullback_resLE hpb hV'V hUV rfl

/-- The restriction `w_U : W'_{U'} ⟶ W_U` of `w`. -/
abbrev chartBaseChangeW :
    (D'.restrict (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι).W ⟶
      (D.restrict U.ι).W :=
  restrictBaseChangeHom hpb D D' w hw U.ι _ _ chartBaseChangeHom_ι

/-- The diagonal open `W_U` of `f|_U : U ⟶ V`. -/
abbrev chartDiagonalOpen : DiagonalOpen (f.resLE V U hUV) :=
  (D.restrict U.ι).reindex (f.resLE V U hUV) V.ι (Scheme.Hom.resLE_comp_ι f hUV).symm

/-- The diagonal open `W'_{U'}` of `f'|_{U'} : U' ⟶ V'`. -/
abbrev chartDiagonalOpenBaseChange :
    DiagonalOpen (f'.resLE V' (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V'))
      inf_le_right) :=
  (D'.restrict (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι).reindex
    (f'.resLE V' _ inf_le_right) V'.ι (Scheme.Hom.resLE_comp_ι f' _).symm

/-- The diagonal open `W_U` of `f|_U : U ⟶ V`. -/
abbrev restrictChart : DiagonalOpen (f.resLE V U hUV) :=
  (D.restrict U.ι).reindex (f.resLE V U hUV) V.ι (Scheme.Hom.resLE_comp_ι f hUV).symm

/-- The diagonal open `W'_{U'}` of `f'|_{U'} : U' ⟶ V'`. -/
abbrev restrictChartBaseChange :
    DiagonalOpen (f'.resLE V' (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V'))
      inf_le_right) :=
  (D'.restrict (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι).reindex
    (f'.resLE V' _ inf_le_right) V'.ι (Scheme.Hom.resLE_comp_ι f' _).symm

omit [Flat f] [LocallyOfFinitePresentation f] in
include hw in
/-- `w_U` is the restriction of `g'|_{U'} × g'|_{U'}`. -/
theorem chartBaseChangeW_ι :
    chartBaseChangeW hpb D D' w hw (U := U) (V' := V') ≫ (restrictChart D hUV).ι =
      (restrictChartBaseChange D' (U := U) (V' := V')).ι ≫
        pullbackMapOfIsPullback (isPullback_chart hpb hUV hV'V) := by
  show chartBaseChangeW hpb D D' w hw ≫ (D.restrict U.ι).ι ≫ (pullbackFactorIso _ _ _).hom =
    ((D'.restrict _).ι ≫ (pullbackFactorIso _ _ _).hom) ≫ _
  rw [restrictBaseChangeHom_ι_assoc, Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackMapOfIsPullback_fst, pullbackFactorIso,
      pullback.lift_fst, restrictPullbackMap, pullback.lift_fst, pullbackFactorIso,
      pullback.lift_fst_assoc]
  · rw [Category.assoc, Category.assoc, pullbackMapOfIsPullback_snd, pullbackFactorIso,
      pullback.lift_snd, restrictPullbackMap, pullback.lift_snd, pullbackFactorIso,
      pullback.lift_snd_assoc]

include hU hV hV' hUV hV'V in
/-- **The base change of the restricted generator on a chart.** If `(K_U, ξ_U)` is a relative
dualizing complex for `U ⟶ S` on `W_U` and `ξ_U` is a generator, then the derived pullback of `ξ_U`
along `w_U : W'_{U'} ⟶ W_U` is a generator. -/
theorem isPostcompGenerator_chart (KU : DerivedCategory U.toScheme.Modules)
    (ξU : (D.restrict U.ι).diagonalObject ⟶ (D.restrict U.ι).derivedPullbackProj KU)
    (hKU : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.restrict U.ι) KU ξU)
    (hgen : Dualizing.IsPostcompGenerator ξU) :
    Dualizing.IsPostcompGenerator ((derivedPullback
      (chartBaseChangeW hpb D D' w hw (U := U) (V' := V')).toLRSHom.toShHom).map ξU) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have hKA := (hKU.reindex (f.resLE V U hUV) V.ι
    (Scheme.Hom.resLE_comp_ι f hUV).symm).isRelativeDualizingComplex_derivedSections
    (isAffineOpen_top U.toScheme) (isAffineOpen_top V.toScheme) le_top
  have hqc := isQuasicoherentDerived_of_isPseudoCoherent U.toScheme KU hKU.1.1
  let e := (D.restrict U.ι).derivedPullbackProj_reindex_eq (f.resLE V U hUV) V.ι
    (Scheme.Hom.resLE_comp_ι f hUV).symm KU
  have hsq := isPullback_chart hpb (g' := g') (f' := f') hUV hV'V
  have hw' := chartBaseChangeW_ι hpb D D' w hw hUV hV'V
  let φ₀ := (baseChangeDiagonalIso hsq (restrictChart D hUV)
    (restrictChartBaseChange D' (U := U) (V' := V')) _ hw').symm
  let ψ₀ := derivedPullbackProjBaseChangeIso (restrictChart D hUV)
    (restrictChartBaseChange D' (U := U) (V' := V')) _ _ (proj_baseChange hsq _ _ _ hw') KU
  have AC := isPostcompGenerator_baseChange_of_isAffine hsq (restrictChart D hUV)
    (restrictChartBaseChange D' (U := U) (V' := V')) _ hw' KU hqc hKA _
    (hgen.comp_iso (eqToIso e)) φ₀ ψ₀
  exact (Dualizing.IsPostcompGenerator.map_comp_iso_iff
    (derivedPullback (chartBaseChangeW hpb D D' w hw (U := U) (V' := V')).toLRSHom.toShHom)
    ξU (eqToIso e)).1 ((Dualizing.IsPostcompGenerator.conj_iff φ₀.symm ψ₀ _).1 AC)

include hpb hU hV hV' hUV hV'V in
/-- **`R ℰom(𝒪_{U'}, L pr₁^*L(g'|_{U'})^*K_U|_{W'_{U'}}) ≅ 𝒪_{U'}[0]`** on the chart, when
`(K_U, ξ_U)` is a relative dualizing complex for `U ⟶ S` on `W_U`. -/
theorem nonempty_diagonalExactSupport_chart (KU : DerivedCategory U.toScheme.Modules)
    (ξU : (D.restrict U.ι).diagonalObject ⟶ (D.restrict U.ι).derivedPullbackProj KU)
    (hKU : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.restrict U.ι) KU ξU) :
    Nonempty ((D'.restrict (chartBaseChange (g' := g') (f' := f') (U := U)
      (V' := V')).ι).diagonalExactSupport
      (baseChangeComplex (chartBaseChangeHom (g' := g') (f' := f') (U := U) (V' := V')) KU) ≅
        structureSingle (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).toScheme) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have hKA := (hKU.reindex (f.resLE V U hUV) V.ι
    (Scheme.Hom.resLE_comp_ι f hUV).symm).isRelativeDualizingComplex_derivedSections
    (isAffineOpen_top U.toScheme) (isAffineOpen_top V.toScheme) le_top
  have hqc := isQuasicoherentDerived_of_isPseudoCoherent U.toScheme KU hKU.1.1
  have hpc' : RingedSpace.IsPseudoCoherent
      (X := (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).toScheme.toRingedSpace)
      (baseChangeComplex (chartBaseChangeHom (g' := g') (f' := f') (U := U) (V' := V')) KU) :=
    isPseudoCoherent_derivedPullback _ KU hKU.1.1
  have hqc' := isQuasicoherentDerived_of_isPseudoCoherent
    (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).toScheme _ hpc'
  obtain ⟨e⟩ := nonempty_diagonalExactSupport_baseChange_iso
    (isPullback_chart hpb (g' := g') (f' := f') hUV hV'V)
    (restrictChartBaseChange D' (U := U) (V' := V')) KU hqc hqc' hKA
  exact ⟨(diagonalExactSupportReindexIso
    (D'.restrict (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι)
    (f'.resLE V' _ inf_le_right) V'.ι (Scheme.Hom.resLE_comp_ι f' _).symm
    (baseChangeComplex (chartBaseChangeHom (g' := g') (f' := f') (U := U) (V' := V')) KU)).symm ≪≫
      e⟩

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- `w_U ≫ (W_U ⊆ W) = (W'_{U'} ⊆ W') ≫ w`. -/
theorem chartBaseChangeW_restrictInclusion :
    chartBaseChangeW hpb D D' w hw (U := U) (V' := V') ≫ D.restrictInclusion U.ι =
      D'.restrictInclusion (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι ≫ w :=
  restrictBaseChangeHom_restrictInclusion hpb D D' w hw _ _ _ _

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
