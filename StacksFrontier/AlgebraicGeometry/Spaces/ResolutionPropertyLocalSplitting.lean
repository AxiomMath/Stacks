module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSplitSection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDecompositionInsideEtaleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalizationOfDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertySurjectivityLocal

/-!
# The split section of `π_*𝒪_Y` near a point, through `π_*(ℐ^m)`

In the situation of [Stacks, Tag 0GUY], for a point `v` of `V` the proof of [Stacks, Tag 0GUZ]
chooses an étale neighbourhood `(U, u) ⟶ (X, φ(v))` with `U ×_X Y = W ⊔ W'`, `W ⟶ U` an
isomorphism and `W` mapping into `V`.  The indicator of `W` is a section `ε : 𝒪_U ⟶ (π_*𝒪_Y)|_U`
split by restriction to `W`, and since `ℐ|_W = 𝒪_W` it factors through `(π_*(ℐ^m))|_U` for every
`m`.  This file packages the decomposition of
`AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_factorsThrough_chart` (stated with
subfunctors of `U ×_X Y`) as algebraic spaces and feeds it to the explicit sections of
`StacksFrontier/AlgebraicGeometry/Spaces/ClopenSplitSection.lean`.

## Main results

* `AlgebraicGeometry.Space.exists_etale_split_section_factorsThrough_idealSheafPow`.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

/-- Reassociation of a four-fold composite followed by a fifth map. -/
theorem comp_four_assoc_eq {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ : C} (x : A₀ ⟶ A₁)
    (y : A₁ ⟶ A₂) (z : A₂ ⟶ A₃) (w : A₃ ⟶ A₄) (l : A₄ ⟶ A₅) {r : A₀ ⟶ A₅}
    (h : x ≫ y ≫ z ≫ w ≫ l = r) : (x ≫ y ≫ z ≫ w) ≫ l = r := by
  simpa only [Category.assoc] using h

/-- **A split section of `(π_*𝒪_Y)|_U` factoring through `(π_*(ℐ^m))|_U` for every `m`, from a
clopen piece of `U ×_X Y` isomorphic to `U`.**  In the situation of
`StacksFrontier/AlgebraicGeometry/Spaces/ClopenSplitSection.lean`, for a sheaf of ideals `ℐ` of
`𝒪_Y` whose powers restrict to the unit ideal on the piece `W`, the indicator of `W` and the
restriction to it are a section and its retraction, and the indicator factors through
`(π_*(ℐ^m))|_U`. -/
theorem exists_split_section_factorsThrough_idealSheafPow_of_clopen
    {X Y U V W W' : AlgebraicSpaces B S hS} (π : Y ⟶ X) (u : U ⟶ X)
    (hu : IsEtale B S hS u.hom) (iV : V ⟶ Y) (pV : V ⟶ U) (sqV : IsPullback iV pV π u)
    (a : W ⟶ V) (a' : W' ⟶ V)
    (ha : IsEtale B S hS a.hom) (ha' : IsEtale B S hS a'.hom)
    (hca : IsClosedImmersion B S hS a.hom) (hca' : IsClosedImmersion B S hS a'.hom)
    (hcov : Set.range (pointsMap B S hS W.1 a.hom) ∪
      Set.range (pointsMap B S hS W'.1 a'.hom) = Set.univ)
    (hdisj : Disjoint (Set.range (pointsMap B S hS W.1 a.hom))
      (Set.range (pointsMap B S hS W'.1 a'.hom)))
    [IsIso (a ≫ pV)]
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (hI : ∀ m : ℕ, IsIso ((modulePullback B S hS a).map ((etaleModulePullback B S hS iV
      (isEtale_of_isPullback B S hS pV iV u π sqV.flip hu)).map
        (SheafOfModules.idealSheafPow I m).ι))) :
    ∃ (ε : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
          (etaleModulePullback B S hS u hu).obj (directImageAlgebraUnitModule B S hS π))
        (pr : (etaleModulePullback B S hS u hu).obj (directImageAlgebraUnitModule B S hS π) ⟶
          SheafOfModules.unit (structureRingSheaf B S hS U)),
        ε ≫ pr = 𝟙 _ ∧
        ∀ m : ℕ, ∃ (εK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
          (etaleModulePullback B S hS u hu).obj
            ((modulePushforward B S hS π).obj
              (SheafOfModules.idealSheafPow I m).toSheafOfModules)),
        (εK ≫ (etaleModulePullback B S hS u hu).map
            ((modulePushforward B S hS π).map (SheafOfModules.idealSheafPow I m).ι) :
          SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
            (etaleModulePullback B S hS u hu).obj (pushforwardStructureModule B S hS π)) = ε := by
  have hε := clopenIndicator_comp_restriction B S hS π u hu iV pV sqV a a' ha ha' hca hca'
    hcov hdisj
  refine ⟨_, _, hε, fun m => ?_⟩
  have hfac := @clopenIndicatorIdeal_comp B S hS _ _ _ _ _ _ π u hu iV pV sqV a a' ha ha'
    hca hca' hcov hdisj inferInstance (SheafOfModules.idealSheafPow I m) (hI m)
  exact ⟨_, comp_four_assoc_eq _ _ _ _ _ hfac⟩

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- **Near every point of `V` there is an étale neighbourhood `g : U ⟶ X` and a split section
`ε : 𝒪_U ⟶ (π_*𝒪_Y)|_U` factoring through `(π_*(ℐ^m))|_U`**, for every `m`.  This is the
geometric input of the per-neighbourhood step of [Stacks, Tag 0GUZ],
`AlgebraicGeometry.Space.epi_etaleModulePullback_map_comp_counit_of_killed`. -/
theorem exists_etale_split_section_factorsThrough_idealSheafPow (m : ℕ)
    (v : points B S hS (yoneda.obj D.V)) :
    ∃ (U : AlgebraicSpaces B S hS) (g : U ⟶ X) (hg : IsEtale B S hS g.hom)
      (u : points B S hS U.1),
      pointsMap B S hS U.1 g.hom u = pointsMap B S hS (yoneda.obj D.V) D.φ v ∧
      ∃ (εK : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
          (etaleModulePullback B S hS g hg).obj
            ((modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).obj
              (SheafOfModules.idealSheafPow D.I m).toSheafOfModules))
        (ε : SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
          (etaleModulePullback B S hS g hg).obj
            (directImageAlgebraUnitModule B S hS (D.piHom B S hS hZ X hqc hqs)))
        (pr : (etaleModulePullback B S hS g hg).obj
            (directImageAlgebraUnitModule B S hS (D.piHom B S hS hZ X hqc hqs)) ⟶
          SheafOfModules.unit (structureRingSheaf B S hS U)),
        (εK ≫ (etaleModulePullback B S hS g hg).map
            ((modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).map
              (SheafOfModules.idealSheafPow D.I m).ι) :
          SheafOfModules.unit (structureRingSheaf B S hS U) ⟶
            (etaleModulePullback B S hS g hg).obj
              (pushforwardStructureModule B S hS (D.piHom B S hS hZ X hqc hqs))) = ε ∧
        ε ≫ pr = 𝟙 _ := by
  obtain ⟨U, hU, g, u, W, WV, hg, hgu, hWo, hWc, hWVo, hWVc, hsup, hinf, hiso, ⟨t, ht⟩, -⟩ :=
    exists_etale_decomposition_isIso_part_factorsThrough_chart B S hS hZ X hqc hqs D v
  let Usp : AlgebraicSpaces B S hS := ⟨U, hU⟩
  let gsp : Usp ⟶ X := ObjectProperty.homMk g
  let π := D.piHom B S hS hZ X hqc hqs
  let P : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS gsp π
  let pP : P ⟶ Usp := ObjectProperty.homMk (pullback.fst gsp.hom π.hom)
  let iP : P ⟶ D.Y := ObjectProperty.homMk (pullback.snd gsp.hom π.hom)
  have sqP : IsPullback iP pP π gsp := (AlgebraicSpaces.isPullback_fiberProduct B S hS gsp π).flip
  let Wsp : AlgebraicSpaces B S hS := ⟨W.toFunctor, hWo.1⟩
  let WVsp : AlgebraicSpaces B S hS := ⟨WV.toFunctor, hWVo.1⟩
  let a : WVsp ⟶ P := ObjectProperty.homMk WV.ι
  let a' : Wsp ⟶ P := ObjectProperty.homMk W.ι
  have hcov : Set.range (pointsMap B S hS WVsp.1 a.hom) ∪
      Set.range (pointsMap B S hS Wsp.1 a'.hom) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    rcases mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top B S hS W WV hsup z with hz | hz
    · exact Or.inr hz
    · exact Or.inl hz
  have hdisj : Disjoint (Set.range (pointsMap B S hS WVsp.1 a.hom))
      (Set.range (pointsMap B S hS Wsp.1 a'.hom)) :=
    disjoint_range_pointsMap_ι_of_inf_eq_sheafify_bot B S hS WV W (by rw [inf_comm]; exact hinf)
  have haE : IsEtale B S hS a.hom := isEtale_of_isOpenImmersion B S hS hWVo.2
  have ha'E : IsEtale B S hS a'.hom := isEtale_of_isOpenImmersion B S hS hWo.2
  have : IsIso (a ≫ pP) := by
    have h : IsIso ((ObjectProperty.ι _).map (a ≫ pP)) := hiso
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  have hiE : IsEtale B S hS iP.hom := isEtale_of_isPullback B S hS pP iP gsp π sqP.flip hg
  have hai : IsEtale B S hS (a ≫ iP).hom := fun T φ hφ => by
    have h := hiE T (φ ≫ a.hom) (haE T φ hφ)
    rwa [Category.assoc] at h
  have hK' : ∀ m : ℕ, IsIso ((modulePullback B S hS a).map ((etaleModulePullback B S hS iP
      (isEtale_of_isPullback B S hS pP iP gsp π sqP.flip hg)).map
        (SheafOfModules.idealSheafPow D.I m).ι)) := fun m =>
    isIso_modulePullback_map_etaleModulePullback_map B S hS a iP _ hai _
      (isIso_etaleModulePullback_map_idealSheafPow_ι_of_comp_eq_chart B S hS hZ X hqc hqs D
        (a ≫ iP) hai t ht m)
  have hsplit := exists_split_section_factorsThrough_idealSheafPow_of_clopen B S hS
    π gsp hg iP pP sqP a a' haE ha'E hWVc.2 hWc.2 hcov hdisj D.I hK'
  refine ⟨Usp, gsp, hg, u, ?_, (hsplit.choose_spec.choose_spec.2 m).choose, hsplit.choose,
    hsplit.choose_spec.choose, (hsplit.choose_spec.choose_spec.2 m).choose_spec,
    hsplit.choose_spec.choose_spec.1⟩
  refine hgu.trans ?_
  rw [← pointsMap_comp_apply, D.comp_eq]

end AlgebraicGeometry.Space

end
