module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackChartInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnACoveringFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature

/-!
# Perfectness on an algebraic space is local on the étale charts

Let `X` be an algebraic space over a scheme `S` and `E` an object of `D(𝒪_X)`. If every étale
chart `U` of `X` admits an étale covering `{V → U}` such that the derived pullback of `E` to
each chart space `V` is isomorphic to a bounded complex of retracts of finite free
`𝒪_V`-modules, then `E` is perfect. This is the converse of
`AlgebraicGeometry.Space.exists_hasStrictlyPerfectModel_chart_of_isPerfect`.

## Main definitions

* `AlgebraicGeometry.Space.sliceToChartModules`: the module form of Stacks 04M0 at a chart `V`,
  from modules on the slice of the small étale site of `X` at `V` to modules on the small étale
  site of the chart space.

## Main results

* `AlgebraicGeometry.Space.isPerfect_of_hasStrictlyPerfectModel_chart`: the local-to-global
  direction.
* `AlgebraicGeometry.Space.exists_slice_model_of_chart_model`: a strictly perfect model on a
  chart space gives a strictly perfect model on the corresponding slice.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_chart_approximation`: the analogous criterion
  for `m`-pseudo-coherence.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- Sheafification of abelian presheaves exists on the slice at `V` of the small étale site
of `X`. -/
local instance chartLocalHasSheafifyOver (V : SmallEtale B S hS X.1) :
    HasSheafify ((SmallEtale.topology B S hS X.1).over V) AddCommGrpCat.{u} :=
  SmallEtale.instHasSheafifyOver B S hS X.1 _ V

/-- On the slice of the small étale site of `X` at `V`, the morphisms inverted by sheafification
of abelian presheaves are the locally bijective ones. -/
local instance chartLocalWEqualsLocallyBijectiveOver (V : SmallEtale B S hS X.1) :
    ((SmallEtale.topology B S hS X.1).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  SmallEtale.instWEqualsLocallyBijectiveOver B S hS X.1 _ V

/-- Restriction of `𝒪_X`-modules to the slice at `V` preserves finite limits. -/
local instance chartLocalPreservesFiniteLimitsOverFunctor (V : SmallEtale B S hS X.1) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) V) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V

/-- Restriction of `𝒪_X`-modules to the slice at `V` preserves finite colimits. -/
local instance chartLocalPreservesFiniteColimitsOverFunctor (V : SmallEtale B S hS X.1) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) V) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u, u} V

/-- Sheafification of abelian presheaves exists on the small étale site of the chart space of
`V`. -/
local instance chartLocalHasSheafifyChartSpace (V : SmallEtale B S hS X.1) :
    HasSheafify (SmallEtale.topology B S hS (chartSpace B S hS X V).1) AddCommGrpCat.{u} :=
  SmallEtale.instHasSheafify B S hS _ _

/-- On the small étale site of the chart space of `V`, the morphisms inverted by sheafification
of abelian presheaves are the locally bijective ones. -/
local instance chartLocalWEqualsLocallyBijectiveChartSpace (V : SmallEtale B S hS X.1) :
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  SmallEtale.instWEqualsLocallyBijective B S hS _ _

/-- The module form of Stacks 04M0 at a chart `V`,
`AlgebraicGeometry.Space.chartModuleSliceReindex`, with its target written through the structure
sheaf of the small étale ringed topos of the chart space. -/
noncomputable def sliceToChartModules (V : SmallEtale B S hS X.1) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over V) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V)) :=
  chartModuleSliceReindex B S hS X V

/-- `sliceToChartModules V` is an equivalence of categories. -/
instance sliceToChartModules_isEquivalence (V : SmallEtale B S hS X.1) :
    (sliceToChartModules (B := B) (S := S) (hS := hS) (X := X) V).IsEquivalence :=
  (chartLocalizationModuleEquivalence B S hS X
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C)).isEquivalence_functor

/-- `sliceToChartModules V` is an additive functor. -/
instance sliceToChartModules_additive (V : SmallEtale B S hS X.1) :
    (sliceToChartModules (B := B) (S := S) (hS := hS) (X := X) V).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The derived pullback of `E` to the chart space of `V` is the image under the module form
of Stacks 04M0 of a complex representing the restriction of `E` to the slice at `V`. -/
theorem exists_smallEtaleDerivedModulePullback_chartToSpace_iso_reindex
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (V : SmallEtale B S hS X.1) :
    ∃ K : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over V)) ℤ,
      Nonempty ((DerivedCategory.Q).obj K ≅
        (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) V).mapDerivedCategory.obj
          E) ∧
      Nonempty ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E ≅
        (DerivedCategory.Q).obj
          (((sliceToChartModules V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  let E₀ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
    DerivedCategory.Q.objPreimage E
  let eE₀ : (DerivedCategory.Q).obj E₀ ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let O : SheafOfModules.{u} (structureRingSheaf B S hS X) ⥤
      SheafOfModules.{u} ((structureRingSheaf B S hS X).over V) :=
    SheafOfModules.overFunctor (structureRingSheaf B S hS X) V
  let Fr := sliceToChartModules (B := B) (S := S) (hS := hS) (X := X) V
  have e1 : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E ≅
      (DerivedCategory.Q).obj
        (((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E₀) :=
    (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).mapIso eE₀.symm ≪≫
      smallEtaleDerivedModulePullbackObjQIsoOfIsEtale _ (isEtale_chartToSpace B S hS X V) E₀
  have e2 : ((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E₀ ≅
      (Fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (chartModuleRestrictionSliceIso B S hS X V).app (E₀.X i))
      (fun i j _ ↦ ((chartModuleRestrictionSliceIso B S hS X V).hom.naturality (E₀.d i j)).symm)
  exact ⟨(O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀,
    ⟨(O.mapDerivedCategoryFactors.app E₀).symm ≪≫ O.mapDerivedCategory.mapIso eE₀⟩,
    ⟨e1 ≪≫ (DerivedCategory.Q).mapIso e2⟩⟩

/-- A strictly perfect model on a chart space gives a strictly perfect model on the slice: given a
bounded complex `P` of retracts of finite free modules on the chart space of `V` and a morphism
`φ : P ⟶ Lp^*E` in `D(𝒪_V)`, the inverse of the module form of Stacks 04M0 produces a strictly
perfect complex `P'` on the slice at `V` and a morphism `P' ⟶ E|_V` which is invertible,
respectively epic, on every cohomology sheaf on which `φ` is. -/
theorem exists_slice_model_of_chart_model
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (V : SmallEtale B S hS X.1)
    (P : CochainComplex
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) (P.X j))
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (φ : (DerivedCategory.Q).obj P ⟶
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) :
    ∃ P' : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over V)) ℤ,
      IsStrictlyPerfect ((structureRingSheaf B S hS X).over V) P' ∧
      ∃ β : (DerivedCategory.Q).obj P' ⟶
          (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) V).mapDerivedCategory.obj
            E,
        (∀ j : ℤ, IsIso ((DerivedCategory.homologyFunctor _ j).map φ) →
          IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
        (∀ j : ℤ, Epi ((DerivedCategory.homologyFunctor _ j).map φ) →
          Epi ((DerivedCategory.homologyFunctor _ j).map β)) ∧
        (IsIso φ → IsIso β) := by
  obtain ⟨K, ⟨eK⟩, ⟨e'⟩⟩ := exists_smallEtaleDerivedModulePullback_chartToSpace_iso_reindex E V
  let Eqv := chartLocalizationModuleEquivalence B S hS X
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
  let G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V)) ⥤
      SheafOfModules.{u} ((structureRingSheaf B S hS X).over V) := Eqv.inverse
  have : G.IsEquivalence := Eqv.isEquivalence_inverse
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  let Gc := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let ηV : SheafOfModules.unit ((structureRingSheaf B S hS X).over V) ≅
      G.obj (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) :=
    Eqv.unitIso.app _ ≪≫ G.mapIso (Iso.refl _)
  have hGP : IsStrictlyPerfect ((structureRingSheaf B S hS X).over V) (Gc.obj P) := by
    refine ⟨?_, fun j => ?_⟩
    · refine (Set.finite_Icc a b).subset fun i hi => ?_
      simp only [Set.mem_setOf_eq] at hi
      by_contra hnot
      simp only [Set.mem_Icc, not_and_or, not_le] at hnot
      refine hi (G.map_isZero ?_)
      rcases hnot with hlt | hlt
      · exact P.isZero_of_isStrictlyGE a i hlt
      · exact P.isZero_of_isStrictlyLE b i hlt
    · obtain ⟨n, i, r, hir⟩ :=
        IsRetractOfFiniteFree.map (F := G) ηV.symm (hP j)
      let O₁ := SheafOfModules.unit ((structureRingSheaf B S hS X).over V)
      let eb : SheafOfModules.free (R := (structureRingSheaf B S hS X).over V)
          (ULift.{u} (Fin n)) ≅ ⨁ fun _ : Fin n => O₁ :=
        (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
          (biproduct.isoCoproduct _).symm
      exact (isDirectSummandOfFiniteFree_iff_free _ _).2
        ⟨n, i ≫ eb.inv, eb.hom ≫ r, by
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          exact hir⟩
  let Fr := sliceToChartModules (B := B) (S := S) (hS := hS) (X := X) V
  let Frc := Fr.mapHomologicalComplex (ComplexShape.up ℤ)
  let θ : Fr ⋙ G ≅ 𝟭 (SheafOfModules.{u} ((structureRingSheaf B S hS X).over V)) :=
    Eqv.unitIso.symm
  let cI : Gc.obj (Frc.obj K) ≅ K :=
    (Functor.mapHomologicalComplexCompIso θ (ComplexShape.up ℤ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K
  obtain ⟨eP, -⟩ : ∃ x : (DerivedCategory.Q).obj (Gc.obj P) ≅
      G.mapDerivedCategory.obj ((DerivedCategory.Q).obj P), x =
        (G.mapDerivedCategoryFactors.app P).symm := ⟨_, rfl⟩
  obtain ⟨eE, -⟩ : ∃ x : G.mapDerivedCategory.obj ((DerivedCategory.Q).obj (Frc.obj K)) ≅
      (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) V).mapDerivedCategory.obj E,
      x = G.mapDerivedCategoryFactors.app _ ≪≫ (DerivedCategory.Q).mapIso cI ≪≫ eK :=
    ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = φ ≫ e'.hom := ⟨_, rfl⟩
  have hH : ∀ j : ℤ, (DerivedCategory.homologyFunctor _ j).map
      (eP.hom ≫ G.mapDerivedCategory.map ψ ≫ eE.hom) =
      (DerivedCategory.homologyFunctor _ j).map eP.hom ≫
        (DerivedCategory.homologyFunctor _ j).map (G.mapDerivedCategory.map ψ) ≫
          (DerivedCategory.homologyFunctor _ j).map eE.hom := fun j => by
    rw [Functor.map_comp, Functor.map_comp]
  refine ⟨Gc.obj P, hGP, eP.hom ≫ G.mapDerivedCategory.map ψ ≫ eE.hom, ?_, ?_, ?_⟩
  · intro j hj
    have hψi : IsIso ((DerivedCategory.homologyFunctor _ j).map ψ) := by
      rw [hψ, Functor.map_comp]
      exact IsIso.comp_isIso
    have h2 : IsIso ((DerivedCategory.homologyFunctor _ j).map (G.mapDerivedCategory.map ψ)) :=
      (G.isIso_homologyFunctor_map_mapDerivedCategory_map_iff ψ j).2 (Functor.map_isIso G _)
    rw [hH]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h2 inferInstance)
  · intro j hj
    have hψe : Epi ((DerivedCategory.homologyFunctor _ j).map ψ) := by
      rw [hψ, Functor.map_comp]
      exact epi_comp' hj (IsIso.epi_of_iso _)
    have h2 : Epi ((DerivedCategory.homologyFunctor _ j).map (G.mapDerivedCategory.map ψ)) :=
      (RingedSite.epi_map_iff_of_natIso (G.mapDerivedCategoryHomologyIso j) ψ).2
        (G.map_epi _)
    rw [hH]
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' h2 (IsIso.epi_of_iso _))
  · intro hφ
    have : IsIso ψ := by rw [hψ]; exact IsIso.comp_isIso
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' (Functor.map_isIso _ _)
      inferInstance)

/-- If every étale chart `U` of `X` admits an étale covering `{V → U}` such that the derived
pullback of `E` to every chart space `V` has a strictly perfect model, then `E` is perfect. -/
theorem isPerfect_of_hasStrictlyPerfectModel_chart
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (h : ∀ U : SmallEtale B S hS X.1,
      ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧
        ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), R g →
          HasStrictlyPerfectModel B S hS
            ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E)) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E := by
  refine RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect_general
    (smallEtaleRingedSite B S hS X.1 X.2) E fun U => ?_
  obtain ⟨R, hR, hmod⟩ := h U
  refine ⟨R, hR, fun (V : SmallEtale B S hS X.1) g hg => ?_⟩
  obtain ⟨P, hP, ⟨a, b, ha, hb⟩, ⟨e⟩⟩ := hmod g hg
  obtain ⟨P', hP', β, -, -, hβ⟩ := exists_slice_model_of_chart_model E V P hP a b ha hb e.inv
  exact ⟨P', hP', ⟨@asIso _ _ _ _ β (hβ inferInstance)⟩⟩

/-- If every étale chart `U` of `X` admits an étale covering `{V → U}` such that on every chart
space `V` a bounded complex of retracts of finite free modules maps to the derived pullback of `E`,
isomorphically on cohomology in degrees `> m` and surjectively in degree `m`, then `E` is
`m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_chart_approximation
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (m : ℤ)
    (h : ∀ U : SmallEtale B S hS X.1,
      ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧
        ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), R g →
          ∃ P : CochainComplex (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ,
            (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
              (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) (P.X j)) ∧
            (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
            ∃ φ : (DerivedCategory.Q).obj P ⟶
                (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E,
              (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ)) ∧
              Epi ((DerivedCategory.homologyFunctor _ m).map φ)) :
    RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS X.1 X.2) E m := by
  refine RingedSite.isPseudoCoherentFrom_of_forall_coveringFamily_derived_approximation
    (smallEtaleRingedSite B S hS X.1 X.2) E m fun U => ?_
  obtain ⟨R, hR, hmod⟩ := h U
  refine ⟨R, hR, fun (V : SmallEtale B S hS X.1) g hg => ?_⟩
  obtain ⟨P, hP, ⟨a, b, ha, hb⟩, φ, hiso, hepi⟩ := hmod g hg
  obtain ⟨P', hP', β, hβi, hβe, -⟩ := exists_slice_model_of_chart_model E V P hP a b ha hb φ
  exact ⟨P', hP', β, fun j hj => hβi j (hiso j hj), hβe m hepi⟩

end AlgebraicGeometry.Space

end
