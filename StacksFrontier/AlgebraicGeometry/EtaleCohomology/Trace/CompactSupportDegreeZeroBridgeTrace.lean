module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportOpenRestrictionTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportOpenRestrictionNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsMapOfBarNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDegreeZeroDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationHomEquiv

/-!
# The trace of the map on `H²_c` induced by a map on `X̄_k̄`

Let `X` be a geometrically connected smooth curve over `k` with compactification `j : X ⟶ X̄`,
`k̄` an algebraic closure of `k` separable over `k`, `Λ` a finite ring with `n = #Λ` invertible in
`k̄`, `ψ : ℤ/n → Λ`, `ρ` a finite `Λ`-module `M` with a continuous action of `π₁(X, η̄)` and `ρ_μ`
the `ℤ/n`-module `μ_n(k̄)`. Let `N` be the image of `π₁(X_k̄, η̄)`.

A map `θ : res_ψ((j_! ℱ_ρ)|_{X̄_k̄}) ⟶ (j_! ℱ_μ)|_{X̄_k̄}` induces
`H²_c(X_k̄, ℱ_ρ) ⟶ H²_c(X_k̄, ℱ_μ)`
(`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar`),
and its restriction to `X_k̄` (`Stacks.EtaleCohomology.compactSupportOpenRestriction`) is an
element `b` of `Hom_N(M, μ_n)` (`AlgebraicGeometry.geometricCyclotomicDualHomEquiv`). The main
result is that the trace `tr : H²_c(X_k̄, ℱ_μ) → ℚ/ℤ`
(`AlgebraicGeometry.compactSupportCyclotomicTrace`) of the image of `α` is the degree-zero pairing
`tr(b_* α)` of `α` with `b` (`AlgebraicGeometry.compactSupportDegreeZeroPairing`).

The proof reduces to `ρ_N`: `θ` factors through `res_ψ((j_! ℱ_{ρ_N})|_{X̄_k̄})`
(`AlgebraicGeometry.exists_eq_normalCoinvariantsQuotient_comp`), because `b` factors through the
coinvariants `M_N` and maps on `X̄_k̄` are determined by their restrictions to `X_k̄`. For `ρ_N`
and `ρ_μ`, on which `π₁(X_k̄)` acts trivially, the twisted trace of the image is computed by
`AlgebraicGeometry.compactSupportTrivialTwistEquiv_restrictScalarsMapOfBar`.

## Main results

* `AlgebraicGeometry.exists_geometricCyclotomicDualInvariants_map_normalCoinvariantsQuotient`.
* `AlgebraicGeometry.exists_eq_normalCoinvariantsQuotient_comp`.
* `AlgebraicGeometry.cyclotomicNormalCoinvariantsAddHom_comp_compactSupportCanonicalTwistEquiv`.
* `AlgebraicGeometry.compactSupportCyclotomicTrace_restrictScalarsMapOfBar`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

section Descent

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ] (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- **`Hom_N(M_N, μ_n) → Hom_N(M, μ_n)` is surjective**: an `N`-equivariant `b : M → μ_n` is
`N`-invariant, `N` acting trivially on `μ_n`, hence factors through the coinvariants `M_N`. -/
theorem exists_geometricCyclotomicDualInvariants_map_normalCoinvariantsQuotient
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (b : (geometricCyclotomicDualInvariants B X f kbar Λ y).obj (op ρ)) :
    ∃ b', (geometricCyclotomicDualInvariants B X f kbar Λ y).map
      (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ).op b' = b := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  refine ⟨⟨Stacks.Trace.coinvariantsAddLift _
    (geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ b)
    (geometricCyclotomicDualInvariantsToHom_apply_eq B X f kbar Λ y ρ b), fun γ => ?_⟩, ?_⟩
  · refine AddMonoidHom.ext fun z => ?_
    obtain ⟨m, rfl⟩ := Stacks.Trace.coinvariantsMk_surjective _ z
    exact congrArg (fun φ : ρ.obj.obj.obj.V →+
      ULift.{u + 1} (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) => φ m) (b.2 γ)
  · exact Subtype.ext (AddMonoidHom.ext fun m => rfl)

variable [Algebra (ZMod (Fintype.card Λ)) Λ] (j : CompactificationOf (Over.mk f))

/-- **A map `res((j_! ℱ_ρ)|_{X̄_k̄}) ⟶ (j_! ℱ_μ)|_{X̄_k̄}` factors through `ℱ_{ρ_N}`**: its
restriction to `X_k̄` corresponds to `b ∈ Hom_N(M, μ_n)`
(`AlgebraicGeometry.geometricCyclotomicDualHomEquiv`), `b` comes from `Hom_N(M_N, μ_n)`, and maps
on `X̄_k̄` are determined by their restrictions
(`Stacks.EtaleCohomology.bijective_compactSupportOpenRestriction`). -/
theorem exists_eq_normalCoinvariantsQuotient_comp
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (θ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
          (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
          (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (Fintype.card Λ)) j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))) :
    letI := connectedSpace_of_isCurve B X f
    ∃ θ', θ = (etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
          (pullback j.toBase (specAlgebraMap k kbar))).map
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map
              (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ)))) ≫ θ' := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨b', hb'⟩ := exists_geometricCyclotomicDualInvariants_map_normalCoinvariantsQuotient
    B X f kbar Λ y ρ (geometricCyclotomicDualHomEquiv B X f kbar Λ y ρ
      (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _ θ))
  obtain ⟨θ', hθ'⟩ := (bijective_compactSupportOpenRestriction f j kbar
    (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _).2
    ((geometricCyclotomicDualHomEquiv B X f kbar Λ y
      (geometricNormalCoinvariants B X f kbar Λ y ρ)).symm b')
  refine ⟨θ', (bijective_compactSupportOpenRestriction f j kbar
    (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _).1 ?_⟩
  rw [compactSupportOpenRestriction_precomp, hθ']
  apply (geometricCyclotomicDualHomEquiv B X f kbar Λ y ρ).injective
  rw [geometricCyclotomicDualHomEquiv_naturality, AddEquiv.apply_symm_apply, hb']

end Descent

section Cyclotomic

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))

/-- **`π₁(X_k̄)` acts trivially on `μ_n(k̄)`**, in the form of the hypotheses of Tag 03VK. -/
theorem cyclotomicContinuousModule_representation_map_eq_one :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ∀ g, (finiteTypeContinuousModuleRepresentation (ZMod n) _
        (cyclotomicContinuousModule B X f kbar y n))
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1 := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  intro g
  have h := cyclotomicContinuousModule_ρ_eq_one_of_mem_range B X f kbar y n
    (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) ⟨g, rfl⟩
  exact LinearMap.ext fun z => congrArg (fun φ => φ.asHom.hom z) h

/-- **`Ψ` at `ρ_μ`, read in `μ_n`**: `(ρ_μ)_N = μ_n`
(`AlgebraicGeometry.cyclotomicNormalCoinvariantsAddHom`) after `Ψ(z)` is the twisted `Ξ` of `z`
itself (`ρ_μ` is trivial on `π₁(X_k̄)`). -/
theorem cyclotomicNormalCoinvariantsAddHom_comp_compactSupportCanonicalTwistEquiv
    (hn : IsUnit ((n : ℕ) : kbar))
    (z : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} (ZMod n) f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ (ZMod n)).obj
            (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    (cyclotomicNormalCoinvariantsAddHom B X f kbar y n).comp
        (compactSupportCanonicalTwistEquiv B X f kbar (ZMod n) y j (isUnit_card_zmod kbar n hn)
          (cyclotomicContinuousModule B X f kbar y n) z) =
      (AddEquiv.ulift :
          ULift.{u + 1} (Additive (_root_.rootsOfUnity n kbar)) ≃+ _).toAddMonoidHom.comp
        (compactSupportTrivialTwistEquiv B X f kbar (ZMod n) y j (isUnit_card_zmod kbar n hn)
          (cyclotomicContinuousModule B X f kbar y n)
          (cyclotomicContinuousModule_representation_map_eq_one B X f kbar y n) z) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  rw [compactSupportCanonicalTwistEquiv_apply, compactSupportNormalCoinvariantsEquiv_apply,
    compactSupportTrivialTwistEquiv_naturality B X f kbar (ZMod n) y j (isUnit_card_zmod kbar n hn)
      (geometricNormalCoinvariantsQuotient B X f kbar (ZMod n) y
        (cyclotomicContinuousModule B X f kbar y n))
      (cyclotomicContinuousModule_representation_map_eq_one B X f kbar y n),
    ← AddMonoidHom.comp_assoc]
  rfl

end Cyclotomic

section Final

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ] [Algebra (ZMod (Fintype.card Λ)) Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- `ULift.down ∘ e₂ ∘ G ∘ e₁⁻¹`, applied. -/
theorem addEquiv_ulift_comp_linearEquiv_comp_apply {S S' M N P : Type*} [Semiring S] [Semiring S']
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module S M] [Module S N] [Module S' P]
    {α : Type*} [AddCommMonoid α] [Module S' α]
    (e₁ : N ≃ₗ[S] M) (G : N →+ P) (e₂ : P ≃ₗ[S'] ULift.{u + 1} α) (z : M) :
    ((AddEquiv.ulift : ULift.{u + 1} α ≃+ α).toAddMonoidHom.comp
        (e₂.toLinearMap.toAddMonoidHom.comp (G.comp e₁.symm.toLinearMap.toAddMonoidHom))) z =
      (e₂ (G (e₁.symm z))).down :=
  rfl

omit [Algebra (ZMod (Fintype.card Λ)) Λ] in
/-- The image of `b ∈ Hom_N(M_N, μ_n)` in `Hom_N(M, μ_n)`, at `m`, is `b` at the class of `m`. -/
theorem geometricCyclotomicDualInvariantsToHom_map_normalCoinvariantsQuotient
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (b : (geometricCyclotomicDualInvariants B X f kbar Λ y).obj
      (op (geometricNormalCoinvariants B X f kbar Λ y ρ))) (m : ρ.obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ
        ((geometricCyclotomicDualInvariants B X f kbar Λ y).map
          (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ).op b) m =
      geometricCyclotomicDualInvariantsToHom B X f kbar Λ y
          (geometricNormalCoinvariants B X f kbar Λ y ρ) b
        (Stacks.Trace.coinvariantsMk ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
          (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)
          m) :=
  rfl

/-- The map `M → μ_n` of `AlgebraicGeometry.geometricCyclotomicDualHomEquiv` is that of
`AlgebraicGeometry.pullbackRepresentationHomEquiv`. -/
theorem geometricCyclotomicDualInvariantsToHom_geometricCyclotomicDualHomEquiv
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (φ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      ((etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
            (pullback f (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)))))
    (m : ρ.obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    geometricCyclotomicDualInvariantsToHom B X f kbar Λ y ρ
        (geometricCyclotomicDualHomEquiv B X f kbar Λ y ρ φ) m =
      pullbackRepresentationHomInvariantsToHom B X (Y := fieldBaseChange (Over.mk f) kbar)
        (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ
        (Fintype.card Λ) (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)) ρ
        (pullbackRepresentationHomEquiv B X (fieldBaseChange (Over.mk f) kbar)
          (contains_fieldBaseChange_of_isCurve B X f kbar)
          (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y Λ
          (Fintype.card Λ) (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)) ρ φ) m :=
  rfl

/-- **`b̄` for `b` coming from `ρ_N`**: for `φ' : res(ℱ_{ρ_N}|_{X_k̄}) ⟶ ℱ_μ|_{X_k̄}`, the map
`M_N → μ_n` of the image in `Hom_N(M, μ_n)` of `Φ_{ρ_N}(φ')` is `M_N ≅ Γ(X_k̄, ℱ_{ρ_N}|) ⟶
Γ(X_k̄, ℱ_μ|) ≅ μ_n`, the middle map being `Γ(X_k̄, φ')`. -/
theorem geometricCyclotomicDualInvariantsLift_map_normalCoinvariantsQuotient
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (φ' : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      ((etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
            (pullback f (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj
              (geometricNormalCoinvariants B X f kbar Λ y ρ))) ⟶
        (etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
            (pullback.fst f (specAlgebraMap k kbar))).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))))) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    geometricCyclotomicDualInvariantsLift B X f kbar Λ y ρ
        ((geometricCyclotomicDualInvariants B X f kbar Λ y).map
          (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ).op
          (geometricCyclotomicDualHomEquiv B X f kbar Λ y
            (geometricNormalCoinvariants B X f kbar Λ y ρ) φ')) =
      (AddEquiv.ulift : ULift.{u + 1} (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar)) ≃+
          _).toAddMonoidHom.comp
        ((geometricGlobalSectionsTrivialEquivPullback B X f kbar (ZMod (Fintype.card Λ)) y
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))
            (cyclotomicContinuousModule_representation_map_eq_one B X f kbar y
              (Fintype.card Λ))).toLinearMap.toAddMonoidHom.comp
          ((globalSectionsRestrictScalarsAddHom (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _ _
              φ').comp
            (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y
              (geometricNormalCoinvariants B X f kbar Λ y ρ)
              (geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y
                ρ)).symm.toLinearMap.toAddMonoidHom)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  refine AddMonoidHom.ext fun z => ?_
  have h := (pullbackRepresentationHomEquiv_apply_of_trivial B X f kbar Λ y (Fintype.card Λ)
    (geometricNormalCoinvariants B X f kbar Λ y ρ)
    (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))
    (geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y ρ)
    (cyclotomicContinuousModule_representation_map_eq_one B X f kbar y (Fintype.card Λ)) φ' z)
  obtain ⟨m, rfl⟩ := Stacks.Trace.coinvariantsMk_surjective _ z
  rw [geometricCyclotomicDualInvariantsLift_mk,
    geometricCyclotomicDualInvariantsToHom_map_normalCoinvariantsQuotient]
  erw [geometricCyclotomicDualInvariantsToHom_geometricCyclotomicDualHomEquiv]
  exact (congrArg ULift.down h).trans (addEquiv_ulift_comp_linearEquiv_comp_apply _ _ _ _).symm

/-- Cancelling `c ∘ d = id` inside `((A ∘ (B ∘ (T ∘ c))) ∘ d`. -/
theorem addMonoidHom_comp_comp_comp_cancel {M M' N P Q : Type*} [AddZeroClass M] [AddZeroClass M']
    [AddZeroClass N] [AddZeroClass P] [AddZeroClass Q] (A : P →+ Q) (B : N →+ P) (T : M →+ N)
    (c : M' →+ M) (d : M →+ M') (h : c.comp d = AddMonoidHom.id M) :
    (A.comp (B.comp (T.comp c))).comp d = (A.comp B).comp T :=
  AddMonoidHom.ext fun x => congrArg (fun z => A (B (T z))) (DFunLike.congr_fun h x)

omit [IsAlgClosed kbar] in
/-- `μ_n ≅ μ_{#ℤ/n} ≅ μ_n` is the identity. -/
theorem rootsOfUnityCardZModAddEquiv_symm_comp (n : ℕ) [NeZero n] :
    (rootsOfUnityCardZModAddEquiv kbar n).symm.toAddMonoidHom.comp
        (rootsOfUnityCardZModAddEquiv kbar n).toAddMonoidHom = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun w => (rootsOfUnityCardZModAddEquiv kbar n).symm_apply_apply w

/-- **The trace of the map on `H²_c` induced by `θ` is the degree-zero pairing with the class of
`θ`.** Let `n = #Λ`, `ψ : ℤ/n → Λ`, `θ : res_ψ((j_! ℱ_ρ)|_{X̄_k̄}) ⟶ (j_! ℱ_μ)|_{X̄_k̄}` and `α ∈
H²_c(X_k̄, ℱ_ρ)`. Then `tr : H²_c(X_k̄, ℱ_μ) → ℚ/ℤ`
(`AlgebraicGeometry.compactSupportCyclotomicTrace`) of the image of `α`
(`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar`) is the pairing
`AlgebraicGeometry.compactSupportDegreeZeroPairing` of `α` with the element of `Hom_N(M, μ_n)`
corresponding to the restriction of `θ` to `X_k̄`
(`AlgebraicGeometry.geometricCyclotomicDualHomEquiv`,
`Stacks.EtaleCohomology.compactSupportOpenRestriction`). -/
theorem compactSupportCyclotomicTrace_restrictScalarsMapOfBar
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (θ : letI := connectedSpace_of_isCurve B X f
      haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
      (etaleModuleRestrictScalars (algebraMap (ZMod (Fintype.card Λ)) Λ)
          (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod (Fintype.card Λ))
          (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (Fintype.card Λ)) j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) (ZMod (Fintype.card Λ))).obj
            (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ)))))
    (α : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportCyclotomicTrace B X f kbar y (Fintype.card Λ) j hn
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar
          (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _ θ α) =
      compactSupportDegreeZeroPairing B X f kbar Λ y j hn ρ
        ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).inv.hom α)
        (geometricCyclotomicDualHomEquiv B X f kbar Λ y ρ
          (compactSupportOpenRestriction f j kbar (algebraMap (ZMod (Fintype.card Λ)) Λ) _ _
            θ)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have hα : (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).hom.hom
      ((compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar ρ).inv.hom α) = α := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id,
      LinearMap.id_apply]
  obtain ⟨θ', rfl⟩ := exists_eq_normalCoinvariantsQuotient_comp B X f kbar Λ y j ρ θ
  rw [compactSupportCyclotomicTrace_apply, compactSupportDegreeZeroPairing_apply, hα,
    compactSupportOpenRestriction_precomp, geometricCyclotomicDualHomEquiv_naturality,
    geometricCyclotomicDualInvariantsLift_map_normalCoinvariantsQuotient,
    ← galoisCompactSupportRestrictScalarsMapOfBar_map_left,
    ← AddMonoidHom.comp_assoc (rootsOfUnityCardZModAddEquiv kbar (Fintype.card Λ)).toAddMonoidHom,
    cyclotomicNormalCoinvariantsAddHom_comp_compactSupportCanonicalTwistEquiv B X f kbar y
      (Fintype.card Λ) j hn,
    compactSupportTrivialTwistEquiv_restrictScalarsMapOfBar B X f kbar
      (algebraMap (ZMod (Fintype.card Λ)) Λ) y j hn
      (isUnit_card_zmod kbar _ hn) (ZMod.card _) (geometricNormalCoinvariants B X f kbar Λ y ρ)
      (geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y ρ)
      (cyclotomicContinuousModule B X f kbar y (Fintype.card Λ))
      (cyclotomicContinuousModule_representation_map_eq_one B X f kbar y (Fintype.card Λ)) θ' _
      (rootsOfUnityCardZModAddEquiv kbar (Fintype.card Λ)).symm.toAddMonoidHom (fun _ => rfl),
    compactSupportCanonicalTwistEquiv_apply, compactSupportNormalCoinvariantsEquiv_apply]
  refine congrArg (fun φ => Stacks.CharacterModule.zmodToRatCircle (Fintype.card Λ)
    (Stacks.CharacterModule.cyclicEndScalar (natCard_additive_rootsOfUnity_card kbar Λ hn) φ)) ?_
  refine (addMonoidHom_comp_comp_comp_cancel _ _ _ _ _
    (rootsOfUnityCardZModAddEquiv_symm_comp kbar (Fintype.card Λ))).trans ?_
  with_reducible rfl

end Final

end AlgebraicGeometry

end
