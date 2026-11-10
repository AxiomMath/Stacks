module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCanonicalTwistGalois
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricSmoothModelInverseImageNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveExtensionByZeroSheafTraceNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGlobalSectionsTrivialEquivPullbackNatural

/-!
# `Ψ : H²_c(X_k̄, ℱ_ρ) ≅ Hom(μ_n(k̄), M_N)` is natural in `ρ`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure,
`Λ` a finite ring with `n = #Λ` invertible, and `ℱ_ρ` the sheaf on `X_étale` attached to a finite
`Λ`-module `M` with a continuous action `ρ` of `π₁(X, η̄)`. The canonical isomorphism of Tag 03VK,
`Ψ_ρ = AlgebraicGeometry.compactSupportCanonicalTwistEquiv : H²_c(X_k̄, ℱ_ρ) ≅ Hom(μ_n(k̄), M_N)`,
is natural in `ρ`: for a morphism `v : ρ ⟶ ρ'` it carries `H²_c(ℱ_v)` to composition with the
induced map `v_N : M_N ⟶ M'_N` on the coinvariants of the image `N` of `π₁(X_k̄, η̄)`.

## Main definitions

* `Stacks.EtaleCohomology.finiteTypeContinuousModuleNormalCoinvariantsMap`: the map
  `M_N ⟶ M'_N` induced by a morphism `M ⟶ M'`.
* `AlgebraicGeometry.geometricNormalCoinvariantsMap`: the map `v_N : ρ_N ⟶ ρ'_N` induced by
  `v : ρ ⟶ ρ'`.

## Main results

* `AlgebraicGeometry.compactSupportCanonicalTwistEquiv_naturality`: `Ψ` is natural in `ρ`.
* `AlgebraicGeometry.compactSupportTrivialTrace_naturality` and
  `AlgebraicGeometry.compactSupportTrivialTwistEquiv_naturality`: `Ξ_ζ` and its
  root-of-unity free form are natural in `ρ` trivial on `π₁(X_k̄)`.
* `AlgebraicGeometry.compactSupportNormalCoinvariantsEquiv_naturality`: the reduction
  `H²_c(X_k̄, ℱ_ρ) ≃ H²_c(X_k̄, ℱ_{ρ_N})` is natural in `ρ`.
* `AlgebraicGeometry.compactSupportTrivialTrace_comp_naturality` and
  `AlgebraicGeometry.geometricSmoothModelTrivialTrace_comp_naturality`: naturality of `Ξ_ζ` and
  of the trace on the smooth model, as equations of linear maps.

## Implementation notes

The sheaf `ℱ_ρ` carries category instances whose universe levels are spelled differently
(`max 1 (u + 2)` and `u + 2`) in the constituents of `Ξ_ζ`, so the naturality squares are stated
as equations of linear maps, and the pointwise statements are derived from them.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u v w

namespace Stacks.EtaleCohomology

section NormalCoinvariantsMap

variable (Λ : Type w) [Ring Λ] {G : Type v} [Group G] [TopologicalSpace G]
  (N : Subgroup G) [N.Normal]

omit [N.Normal] in
/-- A morphism of finite `Λ`-modules with continuous `G`-action carries the differences
`g x - x`, `g ∈ N`, into the differences. -/
theorem finiteTypeContinuousModule_normalCoinvariantsKer_le_comap
    {M M' : FiniteTypeContinuousModule.{w, v, v} Λ G} (u : M ⟶ M') :
    Stacks.Trace.coinvariantsKer ((finiteTypeContinuousModuleRepresentation Λ G M).comp N.subtype) ≤
      (Stacks.Trace.coinvariantsKer
        ((finiteTypeContinuousModuleRepresentation Λ G M').comp N.subtype)).comap
        u.hom.hom.hom.hom.hom := by
  rw [Stacks.Trace.coinvariantsKer, Submodule.span_le]
  rintro _ ⟨⟨g, x⟩, rfl⟩
  have h : u.hom.hom.hom.hom.hom
        (((finiteTypeContinuousModuleRepresentation Λ G M).comp N.subtype) g x) =
      ((finiteTypeContinuousModuleRepresentation Λ G M').comp N.subtype) g
        (u.hom.hom.hom.hom.hom x) :=
    finiteTypeContinuousModule_hom_comm u (N.subtype g) x
  rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, h]
  exact Submodule.subset_span ⟨(g, u.hom.hom.hom.hom.hom x), rfl⟩

/-- **The map `M_N ⟶ M'_N` induced by a morphism `M ⟶ M'`**, a morphism of finite `Λ`-modules
with continuous `G`-action. -/
def finiteTypeContinuousModuleNormalCoinvariantsMap
    {M M' : FiniteTypeContinuousModule.{w, v, v} Λ G} (u : M ⟶ M') :
    finiteTypeContinuousModuleNormalCoinvariants Λ N M ⟶
      finiteTypeContinuousModuleNormalCoinvariants Λ N M' :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (Submodule.mapQ _ _ u.hom.hom.hom.hom.hom
        (finiteTypeContinuousModule_normalCoinvariantsKer_le_comap Λ N u))
      comm := fun g => by
        apply ModuleCat.hom_ext
        apply Submodule.linearMap_qext
        ext m
        exact congrArg (Submodule.mkQ _) (finiteTypeContinuousModule_hom_comm u g m) }))

/-- `u_N` sends the class of `m` to the class of `u m`. -/
theorem finiteTypeContinuousModuleNormalCoinvariantsMap_apply_mk
    {M M' : FiniteTypeContinuousModule.{w, v, v} Λ G} (u : M ⟶ M') (m : M.obj.obj.obj.V) :
    (finiteTypeContinuousModuleNormalCoinvariantsMap Λ N u).hom.hom.hom.hom.hom
        (Stacks.Trace.coinvariantsMk
          ((finiteTypeContinuousModuleRepresentation Λ G M).comp N.subtype) m) =
      Stacks.Trace.coinvariantsMk
        ((finiteTypeContinuousModuleRepresentation Λ G M').comp N.subtype)
        (u.hom.hom.hom.hom.hom m) :=
  rfl

/-- **`M ⟶ M_N` is natural**: `q ≫ u_N = u ≫ q'`. -/
theorem finiteTypeContinuousModuleNormalCoinvariantsQuotient_comp_map
    {M M' : FiniteTypeContinuousModule.{w, v, v} Λ G} (u : M ⟶ M') :
    finiteTypeContinuousModuleNormalCoinvariantsQuotient Λ N M ≫
        finiteTypeContinuousModuleNormalCoinvariantsMap Λ N u =
      u ≫ finiteTypeContinuousModuleNormalCoinvariantsQuotient Λ N M' := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  ext m
  rfl

end NormalCoinvariantsMap

end Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace AlgebraicGeometry

section SmoothModel

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ]

/-- **`H^i_c(X_k̄, ℱ) ≅ H^i(C, q^{-1}(j_! ℱ))` is natural in `ℱ`.** -/
theorem galoisCompactSupportSmoothModelInverseImageEquiv_naturality {F F' : EtaleModules.{u, 0} Λ X}
    (g : F ⟶ F') (i : ℤ) (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i) :
    galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F' i
        (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g))).hom x) =
      (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).map ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g))).hom
        (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F i x) := by
  rw [galoisCompactSupportSmoothModelInverseImageEquiv_apply,
    galoisCompactSupportSmoothModelInverseImageEquiv_apply]
  have h₁ := congrArg (fun φ => φ.hom x)
    (galoisCompactSupportSmoothModelIso_hom_naturality f j kbar Λ g i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  rw [h₁]
  have h₂ := congrArg (fun φ => (((etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerivedPlus i).map φ).hom
        ((galoisCompactSupportSmoothModelIso f j kbar Λ F i).hom.hom x))
    (geometricSmoothModelInverseImageIso_inv_naturality f j kbar Λ g)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h₂
  exact h₂

/-- `AlgebraicGeometry.galoisCompactSupportSmoothModelInverseImageEquiv_naturality` as an equation
of linear maps. -/
theorem galoisCompactSupportSmoothModelInverseImageEquiv_comp_naturality
    {F F' : EtaleModules.{u, 0} Λ X} (g : F ⟶ F') (i : ℤ) :
    (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F' i).toLinearMap ∘ₗ
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g))).hom =
      (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).map ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g))).hom ∘ₗ
        (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F i).toLinearMap :=
  LinearMap.ext fun x =>
    galoisCompactSupportSmoothModelInverseImageEquiv_naturality f j kbar Λ g i x

end SmoothModel

section Trivial

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- **The trace on the smooth model is natural** in `ρ` trivial on `π₁(X_k̄)`, as an equation of
linear maps: it carries `H²(C, q^{-1}(j_! ℱ_w))` to `Γ(X_k̄, ℱ_w|_{X_k̄})`. -/
theorem geometricSmoothModelTrivialTrace_comp_naturality
    {ρ₁ ρ₂ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (w : ρ₁ ⟶ ρ₂)
    (hρ₁ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ₁)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (hρ₂ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ₂)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ)) :
    letI := connectedSpace_of_isCurve B X f
    (geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ₂ hρ₂ hζ).toLinearMap ∘ₗ
      (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
      ((2 : ℕ) : ℤ)).map ((etaleModuleInverseImage.{u, 0} Λ
      (geometricSmoothModelProj f j kbar)).map ((etaleModuleExtensionByZero.{u, 0} Λ
      j.immersion).map ((representationSheaf B X (y.map
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
      Λ).map w)))).hom =
      ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).map
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w))).hom ∘ₗ
        (geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ₁ hρ₁ hζ).toLinearMap := by
  let := connectedSpace_of_isCurve B X f
  have hgen : (curveExtensionByZeroRestrictionTrace (geometricSmoothModel f j kbar).q Λ hn hζ
    (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
    ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₂)))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₂))
    (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ
      ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₂))
    (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar Λ y ρ₂ hρ₂)
    (finite_geometricGlobalSectionsPullback B X f kbar Λ y ρ₂ hρ₂)).toLinearMap ∘ₗ
      (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
      ((2 : ℕ) : ℤ)).map ((etaleModuleInverseImage.{u, 0} Λ
      (geometricSmoothModelProj f j kbar)).map ((etaleModuleExtensionByZero.{u, 0} Λ
      j.immersion).map ((representationSheaf B X (y.map
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
      Λ).map w)))).hom =
      ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).map
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w))).hom ∘ₗ
        (curveExtensionByZeroRestrictionTrace (geometricSmoothModel f j kbar).q Λ hn hζ
    (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
    ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₁)))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₁))
    (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ
      ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₁))
    (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar Λ y ρ₁ hρ₁)
    (finite_geometricGlobalSectionsPullback B X f kbar Λ y ρ₁ hρ₁)).toLinearMap :=
      LinearMap.ext fun z => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
    exact curveExtensionByZeroRestrictionTrace_naturality (geometricSmoothModel f j kbar).q Λ hn hζ
      (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
      (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₁))
      (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₂))
      (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar Λ y ρ₁ hρ₁)
      (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar Λ y ρ₂ hρ₂)
      (finite_geometricGlobalSectionsPullback B X f kbar Λ y ρ₁ hρ₁)
      (finite_geometricGlobalSectionsPullback B X f kbar Λ y ρ₂ hρ₂)
        ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w)))
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w))
      (geometricSmoothModelInverseImageRestrictionIso_hom_naturality f j kbar Λ
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w)) z
  unfold geometricSmoothModelTrivialTrace
  exact hgen

/-- `Ξ_ζ` as a linear map is the composite of its three constituents. -/
theorem compactSupportTrivialTrace_toLinearMap
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ)) :
    letI := connectedSpace_of_isCurve B X f
    (compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ).toLinearMap =
      (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).toLinearMap ∘ₗ
        (geometricSmoothModelTrivialTrace B X f kbar Λ y j hn ρ hρ hζ).toLinearMap ∘ₗ
          (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)
            ((2 : ℕ) : ℤ)).toLinearMap := by
  let := connectedSpace_of_isCurve B X f
  unfold compactSupportTrivialTrace
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.comp_assoc]

/-- **`Ξ_ζ : H²_c(X_k̄, ℱ_ρ) ≅ M` is natural** in `ρ` trivial on `π₁(X_k̄)`, as an equation of
linear maps: it carries `H²_c(ℱ_w)` to the underlying linear map of `w`. -/
theorem compactSupportTrivialTrace_comp_naturality
    {ρ₁ ρ₂ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (w : ρ₁ ⟶ ρ₂)
    (hρ₁ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ₁)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (hρ₂ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ₂)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ)) :
    letI := connectedSpace_of_isCurve B X f
    (compactSupportTrivialTrace B X f kbar Λ y j hn ρ₂ hρ₂ hζ).toLinearMap ∘ₗ
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w)))).hom =
      w.hom.hom.hom.hom.hom ∘ₗ
        (compactSupportTrivialTrace B X f kbar Λ y j hn ρ₁ hρ₁ hζ).toLinearMap := by
  let := connectedSpace_of_isCurve B X f
  rw [compactSupportTrivialTrace_toLinearMap, compactSupportTrivialTrace_toLinearMap]
  exact linearMap_comp_three_squares
    (galoisCompactSupportSmoothModelInverseImageEquiv_comp_naturality f j kbar Λ
      ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w) ((2 : ℕ) : ℤ))
    (geometricSmoothModelTrivialTrace_comp_naturality B X f kbar Λ y j hn w hρ₁ hρ₂ hζ)
    (geometricGlobalSectionsTrivialEquivPullback_comp_naturality B X f kbar Λ y w hρ₁ hρ₂)

/-- **`Ξ_ζ : H²_c(X_k̄, ℱ_ρ) ≅ M` is natural** in `ρ` trivial on `π₁(X_k̄)`: it carries
`H²_c(ℱ_w)` to the underlying linear map of `w`. -/
theorem compactSupportTrivialTrace_naturality
    {ρ₁ ρ₂ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (w : ρ₁ ⟶ ρ₂)
    (hρ₁ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ₁)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (hρ₂ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ₂)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₁)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportTrivialTrace B X f kbar Λ y j hn ρ₂ hρ₂ hζ
        (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w)))).hom x) =
      w.hom.hom.hom.hom.hom (compactSupportTrivialTrace B X f kbar Λ y j hn ρ₁ hρ₁ hζ x) := by
  let := connectedSpace_of_isCurve B X f
  rw [← LinearEquiv.coe_coe, ← LinearEquiv.coe_coe
    (compactSupportTrivialTrace B X f kbar Λ y j hn ρ₁ hρ₁ hζ),
    ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    compactSupportTrivialTrace_comp_naturality B X f kbar Λ y j hn w hρ₁ hρ₂ hζ]

/-- **The root-of-unity free `Ξ : H²_c(X_k̄, ℱ_ρ) ≅ Hom(μ_n(k̄), M)` is natural** in `ρ` trivial
on `π₁(X_k̄)`: it carries `H²_c(ℱ_w)` to composition with `w`. -/
theorem compactSupportTrivialTwistEquiv_naturality
    {ρ₁ ρ₂ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (w : ρ₁ ⟶ ρ₂)
    (hρ₁ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ₁)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (hρ₂ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ₂)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ₁)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportTrivialTwistEquiv B X f kbar Λ y j hn ρ₂ hρ₂
        (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
                (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map w)))).hom x) =
      w.hom.hom.hom.hom.hom.toAddMonoidHom.comp
        (compactSupportTrivialTwistEquiv B X f kbar Λ y j hn ρ₁ hρ₁ x) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have h₀ := (exists_isPrimitiveRoot_of_isUnit hn).choose_spec
  refine addMonoidHom_rootsOfUnity_ext h₀ Λ (card_nsmul_eq_zero_of_module Λ) ?_
  rw [compactSupportTrivialTwistEquiv_apply_ofMul B X f kbar Λ y j hn ρ₂ hρ₂ h₀,
    AddMonoidHom.comp_apply,
    compactSupportTrivialTwistEquiv_apply_ofMul B X f kbar Λ y j hn ρ₁ hρ₁ h₀,
    compactSupportTrivialTrace_naturality B X f kbar Λ y j hn w hρ₁ hρ₂ h₀,
    LinearMap.toAddMonoidHom_coe]

/-- **`v_N : ρ_N ⟶ ρ'_N`**, the map on the coinvariants `M_N` of the image `N` of `π₁(X_k̄, η̄)`
induced by `v : ρ ⟶ ρ'`. -/
abbrev geometricNormalCoinvariantsMap
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ') :
    geometricNormalCoinvariants B X f kbar Λ y ρ ⟶ geometricNormalCoinvariants B X f kbar Λ y ρ' :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  finiteTypeContinuousModuleNormalCoinvariantsMap Λ
    (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range v

omit [Smooth f] [Fintype Λ] in
/-- `v_N` sends the class of `m` to the class of `v m`. -/
theorem geometricNormalCoinvariantsMap_apply_mk
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ')
    (m : ρ.obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricNormalCoinvariantsMap B X f kbar Λ y v).hom.hom.hom.hom.hom
        (Stacks.Trace.coinvariantsMk ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
          (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype) m) =
      Stacks.Trace.coinvariantsMk ((finiteTypeContinuousModuleRepresentation Λ _ ρ').comp
          (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)
        (v.hom.hom.hom.hom.hom m) :=
  rfl

omit [Smooth f] [Fintype Λ] in
/-- **`ρ ⟶ ρ_N` is natural**: `q ≫ v_N = v ≫ q'`. -/
theorem geometricNormalCoinvariantsQuotient_comp_map
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ') :
    geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ ≫
        geometricNormalCoinvariantsMap B X f kbar Λ y v =
      v ≫ geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ' :=
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  finiteTypeContinuousModuleNormalCoinvariantsQuotient_comp_map Λ _ v

set_option maxHeartbeats 400000 in
-- the kernel's check of the `Functor.map_comp` rewrites through the universe-mismatched category
-- instances of `ℱ_ρ` exceeds the default limit
/-- **`H²_c(X_k̄, ℱ_ρ) ≃ H²_c(X_k̄, ℱ_{ρ_N})` is natural in `ρ`.** -/
theorem compactSupportNormalCoinvariantsEquiv_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ')
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportNormalCoinvariantsEquiv B X f kbar Λ y j hn ρ'
        (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X _ Λ).map v)))).hom x) =
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X _ Λ).map
                (geometricNormalCoinvariantsMap B X f kbar Λ y v))))).hom
        (compactSupportNormalCoinvariantsEquiv B X f kbar Λ y j hn ρ x) := by
  let := connectedSpace_of_isCurve B X f
  rw [compactSupportNormalCoinvariantsEquiv_apply, compactSupportNormalCoinvariantsEquiv_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
    ← Functor.map_comp, ← Functor.map_comp]
  simp only [galoisCompactSupportCohomologyMap, ← Functor.map_comp,
    geometricNormalCoinvariantsQuotient_comp_map]

/-- **`Ψ : H²_c(X_k̄, ℱ_ρ) ≅ Hom(μ_n(k̄), M_N)` is natural in `ρ`.** For a morphism
`v : ρ ⟶ ρ'` of finite `Λ`-modules with continuous `π₁(X, η̄)`-action,
`Ψ_{ρ'} ∘ H²_c(ℱ_v) = (v_N ∘ -) ∘ Ψ_ρ`, with `v_N : M_N ⟶ M'_N` the induced map on the
coinvariants of the image `N` of `π₁(X_k̄, η̄)`
(`AlgebraicGeometry.geometricNormalCoinvariantsMap`, `[m] ↦ [v m]`). -/
theorem compactSupportCanonicalTwistEquiv_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ')
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ'
        (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X _ Λ).map v)))).hom x) =
      (geometricNormalCoinvariantsMap B X f kbar Λ y v).hom.hom.hom.hom.hom.toAddMonoidHom.comp
        (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ x) := by
  let := connectedSpace_of_isCurve B X f
  rw [compactSupportCanonicalTwistEquiv_apply, compactSupportCanonicalTwistEquiv_apply,
    compactSupportNormalCoinvariantsEquiv_naturality B X f kbar Λ y j hn v x]
  exact compactSupportTrivialTwistEquiv_naturality B X f kbar Λ y j hn
    (geometricNormalCoinvariantsMap B X f kbar Λ y v)
    (geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y ρ)
    (geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y ρ') _

end Trivial

end AlgebraicGeometry

end
