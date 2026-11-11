module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBocksteinDerivedComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.DerivedTensorSingleTriangleDelta

/-!
# The derived tensor product with `O_X/I` of a complex of `I`-torsion-free modules

Let `X` be a ringed space and `ι : I ⟶ O_X` an invertible ideal subsheaf.  For a cochain complex
`G` of `I`-torsion-free `O_X`-modules the derived tensor product `G ⊗^L I^n/I^{n+1}` is computed
by the ordinary one: the canonical map `G ⊗^L I^n/I^{n+1} ⟶ Tot(G ⊗ (I^n/I^{n+1})[0])` of
Tag 06YU is an isomorphism.  Indeed `[I^{n+1} → I^n]` is a K-flat resolution of `I^n/I^{n+1}`,
and tensoring the augmentation with `G` gives a quasi-isomorphism, because the consecutive
ideal-power sequence stays short exact after tensoring with an `I`-torsion-free module.

Applied to the décalage this is the left-hand side of Tag 0GT9: in Situation 0GT4, on an object
of `D(O_X)` represented by a complex `F` of `I`-torsion-free modules,
`Lη_I F ⊗^L O_X/I ≅ η_I F ⊗ O_X/I`.

## Main definitions

* `Stacks.IdealTorsion.ReductionDerived.derivedTensorPowerQuotientGradedIso`:
  `G ⊗^L I^n/I^{n+1} ≅ Q(gradedComplex X I ι G n)` for `G` termwise `I`-torsion-free.
* `Stacks.IdealTorsion.ReductionDerived.torsionFreeLift`: a complex with `I`-torsion-free terms,
  read as a complex of the full subcategory of `I`-torsion-free modules.
* `Stacks.IdealTorsion.ReductionDerived.derivedEtaTensorModIdealIso`:
  `Lη_I (Q F) ⊗^L O_X/I ≅ Q(etaModIdealComplex X I ι F hF)` in Situation 0GT4.

## Main results

* `Stacks.IdealTorsion.ReductionDerived.isIso_toTensor_powerQuotient`: the canonical map
  `G ⊗^L I^n/I^{n+1} ⟶ Tot(G ⊗ (I^n/I^{n+1})[0])` is invertible for `G` termwise
  `I`-torsion-free.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.IdealTorsion.Eta (idealPowerTerm idealPowerIncl idealPowerMap)

open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)

universe u

namespace Stacks.IdealTorsion.ReductionDerived

open Stacks.IdealTorsion.Bockstein Stacks.IdealTorsion.Reduction

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### The derived tensor product with `I^n/I^{n+1}` -/

/-- **Tensoring the resolution `[I^{n+1} → I^n] ⟶ I^n/I^{n+1}` with a complex of
`I`-torsion-free modules gives a quasi-isomorphism.**  The augmentation is the projection of the
mapping cone of `I^{n+1} ⟶ I^n` onto the cokernel; after tensoring it is the cone comparison
followed by the projection of the cone of the tensored map onto the tensored cokernel, which is a
quasi-isomorphism because the tensored sequence is still short exact. -/
public theorem quasiIso_total_powerQuotientResolutionAug (I : SheafOfModules.{u} Oₓ)
    (ι : I ⟶ 𝒪) [Mono ι] [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ)
    (hG : ∀ k : ℤ, Mono (idealPowerIncl X I ι n (G.X k))) :
    QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj G).map
      (powerQuotientResolutionAug X I ι n)) := by
  have hS := totalPowerInclSequence_shortExact X I ι G n hG
  have : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf
      ).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G).Additive :=
    Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_obj_additive _ G
  have hq : QuasiIso (CochainComplex.mappingCone.descShortComplex
      ((powerInclSequenceSingle X I ι n).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf
          ).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj G))) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have h := map_descShortComplex_eq_bifunctorMappingConeIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G
    (powerInclSequenceSingle X I ι n)
  change QuasiIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf
    ).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj G |>.map (CochainComplex.mappingCone.descShortComplex
        (powerInclSequenceSingle X I ι n)))
  rw [h]
  exact quasiIso_comp _ _

section AnyModel

variable [HasDerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)]

/-- **The canonical map `G ⊗^L I^n/I^{n+1} ⟶ Tot(G ⊗ (I^n/I^{n+1})[0])` is invertible** for a
complex `G` on whose terms `I^{n+1} ⊗ - ⟶ I^n ⊗ -` is injective, e.g. a complex of
`I`-torsion-free modules.  By naturality of the canonical map it is conjugate to
the canonical map at the K-flat resolution `[I^{n+1} → I^n]`, which is invertible, by the image of
the augmentation under `G ⊗^L -`, invertible because the augmentation is a quasi-isomorphism, and
by the image in `D(O_X)` of the tensored augmentation, invertible by
`quasiIso_total_powerQuotientResolutionAug`. -/
public theorem isIso_toTensor_powerQuotient (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ)
    (hG : ∀ k : ℤ, Mono (idealPowerIncl X I ι n (G.X k))) :
    IsIso ((canonicalDerivedTensorProduct X.sheaf).toTensor G
      ((HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0).obj
        (powerQuotient X I ι n))) := by
  let T := canonicalDerivedTensorProduct X.sheaf
  have h := T.toTensor_naturality (𝟙 G) (powerQuotientResolutionAug X I ι n)
  have hR : IsIso (T.toTensor G (powerQuotientResolution X I ι n)) := by
    rw [T.toTensor_eq_comparisonRight G _ (kFlat_powerQuotientResolution X I ι n)]
    infer_instance
  have haug : IsIso (DerivedCategory.Q.map (powerQuotientResolutionAug X I ι n)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_powerQuotientResolutionAug X I ι n)
  have htot : IsIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMapReg (𝟙 G)
      (powerQuotientResolutionAug X I ι n)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) (ComplexShape.up ℤ))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_total_powerQuotientResolutionAug X I ι G n hG)
  have hRHS : IsIso (T.toTensor G (powerQuotientResolution X I ι n) ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMapReg (𝟙 G)
        (powerQuotientResolutionAug X I ι n)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) (ComplexShape.up ℤ))) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hR htot
  have hL : IsIso ((T.tensor.map (DerivedCategory.Q.map (𝟙 G))).app
        (DerivedCategory.Q.obj (powerQuotientResolution X I ι n)) ≫
      (T.tensor.obj (DerivedCategory.Q.obj G)).map
        (DerivedCategory.Q.map (powerQuotientResolutionAug X I ι n)) ≫
        T.toTensor G
          ((HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0).obj
            (powerQuotient X I ι n))) := h ▸ hRHS
  have h₁ : IsIso ((T.tensor.map (DerivedCategory.Q.map (𝟙 G))).app
      (DerivedCategory.Q.obj (powerQuotientResolution X I ι n))) := by
    have := Functor.map_isIso T.tensor (DerivedCategory.Q.map (𝟙 G))
    infer_instance
  have h₂ : IsIso ((T.tensor.obj (DerivedCategory.Q.obj G)).map
      (DerivedCategory.Q.map (powerQuotientResolutionAug X I ι n))) :=
    Functor.map_isIso _ _
  have h₃ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ hL
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₂ h₃

/-- **`G ⊗^L I^n/I^{n+1} ≅ G ⊗ I^n/I^{n+1}`** for a complex `G` on whose terms
`I^{n+1} ⊗ - ⟶ I^n ⊗ -` is injective (e.g. `I`-torsion-free terms), the right-hand side being
the complex `gradedComplex X I ι G n` whose degree-`k` term is the cokernel
of `I^{n+1} ⊗ G^k ⟶ I^n ⊗ G^k`.  It is the canonical map of Tag 06YU, invertible by
`isIso_toTensor_powerQuotient`, followed by the termwise description of the total complex. -/
public noncomputable def derivedTensorPowerQuotientGradedIso (I : SheafOfModules.{u} Oₓ)
    (ι : I ⟶ 𝒪) [Mono ι] [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ)
    (hG : ∀ k : ℤ, Mono (idealPowerIncl X I ι n (G.X k))) :
    ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj G)).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} Oₓ) 0).obj (powerQuotient X I ι n)) ≅
      DerivedCategory.Q.obj (gradedComplex X I ι G n) :=
  haveI := isIso_toTensor_powerQuotient X I ι G n hG
  asIso ((canonicalDerivedTensorProduct X.sheaf).toTensor G
      ((HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0).obj
        (powerQuotient X I ι n))) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G
        (powerQuotient X I ι n) ≪≫ rowPowerQuotientIso X I ι G n)

end AnyModel

attribute [local instance] HasDerivedCategory.standard

/-! ### The décalage reduced modulo the ideal -/

/-- A complex of `O_X`-modules with `I`-torsion-free terms, read as a complex of the full
subcategory of `I`-torsion-free modules. -/
public noncomputable def torsionFreeLift {I : SheafOfModules.{u} Oₓ} (ι : I ⟶ 𝒪)
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    CochainComplex (Stacks.IdealTorsion.Eta.TorsionFreeModule X ι) ℤ where
  X k := ⟨F.X k, hF k⟩
  d i j := ObjectProperty.homMk (F.d i j)
  shape i j h := ObjectProperty.hom_ext _ (F.shape i j h)
  d_comp_d' i j k _ _ := ObjectProperty.hom_ext _ (F.d_comp_d i j k)

/-- The décalage of `F` reduced modulo the ideal is the complex `gradedComplex` of the décalage in
degree `0`: both have degree-`k` term `(η_I F)^k / I (η_I F)^k` and the induced differential. -/
public noncomputable def etaModIdealComplexIsoGraded (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Mono ι] [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    gradedComplex X I ι (Stacks.IdealTorsion.Eta.etaObj X I ι F hF) 0 ≅
      etaModIdealComplex X I ι F hF :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by
      rintro k _ rfl
      refine (Category.id_comp _).trans ((Category.comp_id _).trans ?_).symm
      refine (gradedComplex_d X I ι _ 0 k).trans ?_
      refine Eq.trans ?_ (etaModIdealComplex_d X I ι F hF k).symm
      exact (cancel_epi (cokernel.π _)).1 ((cokernel_π_gradedD X I ι _ 0 k).trans
        (cokernel_π_modIdealMap X I ι _).symm))

/-- **The left-hand side of Tag 0GT9 on a complex of `I`-torsion-free modules**, in
Situation 0GT4: `Lη_I F ⊗^L O_X/I ≅ η_I F ⊗ O_X/I`, where `O_X/I = I^0/I^1` and the right-hand
side is the reduction `etaModIdealComplex X I ι F hF` of the décalage modulo the ideal.  The
derived décalage of `F` is the class of `η_I F` (Tag 0F8Q), whose terms are again
`I`-torsion-free, so its derived tensor product with `O_X/I` is the ordinary one
(`derivedTensorPowerQuotientGradedIso`). -/
public noncomputable def derivedEtaTensorModIdealIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Mono ι] (hregl : Stacks.IdealTorsion.IsLocallyGeneratedByRegular X ι)
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    haveI : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I :=
      Stacks.IdealTorsion.isInvertible_of_isLocallyGeneratedByRegular X ι hregl
    ((canonicalDerivedTensorProduct X.sheaf).tensor.obj
        ((Stacks.IdealTorsion.Eta.derivedEtaOfRegular X I ι hregl).obj
          (DerivedCategory.Q.obj F))).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} Oₓ) 0).obj (powerQuotient X I ι 0)) ≅
      DerivedCategory.Q.obj (etaModIdealComplex X I ι F hF) :=
  haveI : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I :=
    Stacks.IdealTorsion.isInvertible_of_isLocallyGeneratedByRegular X ι hregl
  ((canonicalDerivedTensorProduct X.sheaf).tensor.mapIso
      ((Stacks.IdealTorsion.Eta.derivedEtaOfRegular_iso X I ι hregl).app
        (torsionFreeLift X ι F hF))).app _ ≪≫
    derivedTensorPowerQuotientGradedIso X I ι (Stacks.IdealTorsion.Eta.etaObj X I ι F hF) 0
      (fun k => Stacks.IdealTorsion.Reduction.mono_idealPowerIncl_etaTerm X I ι F hF k) ≪≫
    DerivedCategory.Q.mapIso (etaModIdealComplexIsoGraded X I ι F hF)

/-! ### The Bockstein complex of a K-flat complex -/

/-- The degree-`n` term of the Bockstein complex of `Q P`, for `P` K-flat with `I`-torsion-free
terms, is the cohomology `H^n(P ⊗ I^n/I^{n+1})` of the chain-level complex
`gradedComplex X I ι P n`. -/
public noncomputable def bocksteinTermIsoChain (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hPk : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P) (n : ℤ) :
    bocksteinTerm X I ι (DerivedCategory.Q.obj P) n ≅ (gradedComplex X I ι P n).homology n :=
  derivedTensorSingleHomologyIso X P hPk (powerQuotient X I ι n) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (CochainComplex.KFlatBifunctor.totalSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) P
          (powerQuotient X I ι n) ≪≫ rowPowerQuotientIso X I ι P n)

/-- **The Bockstein complex `H^•(M/I)` of Tag 0GT8 at `M = Q P` is the chain-level Bockstein
complex of `P`**, for a K-flat complex `P` with `I`-torsion-free terms.  Degreewise this is
`bocksteinTermIsoChain`; it commutes with the differentials because the Bockstein operator, the
connecting map of the image of the successive-power triangle under `Q P ⊗^L -`, is the connecting
map of the sequence of total complexes (`homologySequenceδ_mapTriangle_singleTriangle`), and that
sequence is `gradedShortComplex X I ι P n`, whose connecting map is the chain-level Bockstein
operator. -/
public noncomputable def bocksteinComplexIsoChain (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Mono ι] [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hPk : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X P)
    (hP : ∀ k : ℤ, IsIdealTorsionFree X ι (P.X k)) :
    bocksteinComplex X I ι (DerivedCategory.Q.obj P) ≅ bocksteinChainComplex X I ι P hP :=
  HomologicalComplex.Hom.isoOfComponents (fun n => bocksteinTermIsoChain X I ι P hPk n)
    (by
      rintro n _ rfl
      rw [bocksteinComplex_d, bocksteinChainComplex_d]
      have hS' := totalPowerQuotientShortComplex_shortExact X I ι P hP n
      have hδ := homologySequenceδ_mapTriangle_singleTriangle X P hPk
        (powerQuotientShortExact X I ι n) hS' n (n + 1) rfl
      have hnat := HomologicalComplex.HomologySequence.δ_naturality
        (totalPowerQuotientShortComplexIso X I ι P n).hom hS'
        (gradedShortComplex_shortExact X I ι P hP n) n (n + 1) rfl
      let θ₀ := derivedTensorSingleHomologyIso X P hPk (powerQuotient X I ι n) n
      let θ₁ := derivedTensorSingleHomologyIso X P hPk (powerQuotient X I ι (n + 1)) (n + 1)
      let e := totalPowerQuotientShortComplexIso X I ι P n
      have h₀ : (bocksteinTermIsoChain X I ι P hPk n).hom =
          θ₀.hom ≫ HomologicalComplex.homologyMap e.hom.τ₃ n := rfl
      have h₁ : (bocksteinTermIsoChain X I ι P hPk (n + 1)).hom =
          θ₁.hom ≫ HomologicalComplex.homologyMap e.hom.τ₁ (n + 1) := rfl
      have hchain : bocksteinChainOperator X I ι P hP n =
          (gradedShortComplex_shortExact X I ι P hP n).δ n (n + 1) rfl := rfl
      rw [h₀, h₁, hchain]
      exact (Category.assoc _ _ _).trans ((congrArg (θ₀.hom ≫ ·) hnat.symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hδ.symm).trans
          (Category.assoc _ _ _)))))

end Stacks.IdealTorsion.ReductionDerived

end
