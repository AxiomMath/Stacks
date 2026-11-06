module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkPointEquiv

/-!
# The twisted cohomology side after a finite extension of the base field

Let `X` be separated of finite type over a finite field `k` with `q` elements, `k'` an extension
with `q ^ (m + 1)` elements, `X' = X ×_k k'`, `g : X' ⟶ X` and `F` an ℓ-adic sheaf on `X`. The
identification `Hⁱ_c(X_k̄, F) ≅ Hⁱ_c(X'_k̄, g⁻¹F)` of
`Stacks.EtaleCohomology.LAdicSheaf.fieldExtensionCohomologyIso` is natural in `F`. Hence for an
endomorphism `ψ` of `F`,

`Tr(g⁻¹ψ ∘ π_{X'}^* | Hⁱ_c(X'_k̄, g⁻¹F) ⊗ ℚ_ℓ) = Tr(ψ ∘ (π_X^*) ^ (m + 1) | Hⁱ_c(X_k̄, F) ⊗ ℚ_ℓ)`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `LAdicSheaf.fieldExtensionCohomologyIso_hom_naturality`: the identification is natural in `F`.
* `LAdicSheaf.trace_rationalMap_comp_rationalGeometricCompactlySupportedFrobenius_fieldExtension`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- Pasting two commutative squares; stated on variables. -/
theorem square_paste_twisted {D : Type*} [Category* D] {P Q P' Q' R S : D} {a : P ⟶ Q}
    {s₁ : P ⟶ P'} {s₂ : Q ⟶ Q'} {b : P' ⟶ Q'} {x₁ : P' ⟶ R} {x₂ : Q' ⟶ S} {d : R ⟶ S}
    (hn : a ≫ s₂ = s₁ ≫ b) (h : b ≫ x₂ = x₁ ≫ d) : a ≫ s₂ ≫ x₂ = (s₁ ≫ x₁) ≫ d := by
  rw [reassoc_of% hn, h, Category.assoc]

/-- A functor carries a commuting square to a commuting square. -/
private theorem map_square_twisted {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {P Q R S : C} {a : P ⟶ Q} {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S} (h : a ≫ b = c ≫ d) :
    G.map a ≫ G.map b = G.map c ≫ G.map d := by
  rw [← G.map_comp, ← G.map_comp, h]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

section Levels

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (k' : Type u) [Field k'] [Algebra k k']
  [Module.Finite k k'] [IsNoetherian X.1] [IsNoetherian (fieldExtensionScheme B X f k').1]

/-- **The identification of the levels of `g⁻¹F` with the inverse images of the levels of `F` is
natural in `F`.** -/
public theorem padicComplexFieldExtensionIso_hom_naturality {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (φ : F ⟶ G) (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.map
        ((padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicLevelMap φ n)) ≫
      (padicComplexFieldExtensionIso B X ℓ f k' G n).hom =
    (padicComplexFieldExtensionIso B X ℓ f k' F n).hom ≫
      (padicCoefficientComplex B (fieldExtensionScheme B X f k') ℓ).map
        (LAdicSheaf.padicLevelMap
          (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') φ) n) := by
  have h := padicLevelInverseImageIso_hom_naturality B (fieldExtensionProj B X f k') ℓ n (φ.app n)
  have hn := (HomologicalComplex.singleMapHomologicalComplex (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
    (pullback.fst f (specAlgebraMap k k'))) (ComplexShape.up ℤ) 0).hom.naturality
      ((padicSheafEquiv B ℓ X).map (LAdicSheaf.padicLevelMap φ n))
  dsimp only [Functor.comp_map] at hn
  ext1
  exact square_paste_twisted hn (map_square_twisted (HomologicalComplex.single _ _ 0) h)

end Levels

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]
  [IsNoetherian X.1] [IsNoetherian (fieldExtensionScheme B X f k').1] (i : ℤ)

omit [Fintype k] [Fintype k'] in
/-- The finite-level identification is natural in the sheaf. -/
public theorem geometricCompactSupportFieldExtensionIso_hom_naturality [Finite k]
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) (n : ℕ) :
    (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map (LAdicSheaf.padicLevelMap φ n) ≫
      (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar G i n).hom =
    (geometricCompactSupportFieldExtensionIso B X ℓ f j k' kbar F i n).hom ≫
      (geometricCompactSupportPadicCohomology B (fieldExtensionScheme B X f k') ℓ
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
          i).map
        (LAdicSheaf.padicLevelMap
          (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') φ) n) := by
  have := Fintype.ofFinite k
  have hE := compactSupportFieldExtensionIso_hom_naturality ℤ_[ℓ] f j k' kbar
    ((padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicLevelMap φ n))
  have hE' : (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar).map
        ((padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicLevelMap φ n)) ≫
      (compactSupportFieldExtensionIso ℤ_[ℓ] f j k' kbar
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ G n))).inv =
      (compactSupportFieldExtensionIso ℤ_[ℓ] f j k' kbar
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))).inv ≫
        (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] (pullback.snd f (specAlgebraMap k k'))
          (compactificationFieldBaseChange f j k') kbar).map
          ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
            (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.map
            ((padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicLevelMap φ n))) := by
    rw [Iso.comp_inv_eq, Category.assoc, hE, Iso.inv_hom_id_assoc]
  have hl := congrArg (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ]
    (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar).map
    (padicComplexFieldExtensionIso_hom_naturality B X ℓ f k' φ n)
  rw [Functor.map_comp, Functor.map_comp] at hl
  have h := square_paste_twisted hE' hl
  exact map_square_twisted (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i) h

/-- **The identification `Hⁱ_c(X_k̄, F) ≅ Hⁱ_c(X'_k̄, g⁻¹F)` is natural in `F`.** -/
public theorem LAdicSheaf.fieldExtensionCohomologyIso_hom_naturality
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i ≫
        (LAdicSheaf.fieldExtensionCohomologyIso B X ℓ f j k' kbar G i).hom =
      (LAdicSheaf.fieldExtensionCohomologyIso B X ℓ f j k' kbar F i).hom ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fieldExtensionScheme B X f k')
          (pullback.snd f (specAlgebraMap k k'))
          (compactificationFieldBaseChange f j k') kbar
          (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') φ) i := by
  refine limit.hom_ext fun n => ?_
  show _ ≫ LAdicSheaf.geometricCompactlySupportedCohomologyπ B (fieldExtensionScheme B X f k') ℓ
      (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
      (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') G) i n.unop = _ ≫
    LAdicSheaf.geometricCompactlySupportedCohomologyπ B (fieldExtensionScheme B X f k') ℓ
      (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
      (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') G) i n.unop
  have hG := LAdicSheaf.fieldExtensionCohomologyIso_hom_π B X ℓ f j k' kbar G i n.unop
  have hF := LAdicSheaf.fieldExtensionCohomologyIso_hom_π B X ℓ f j k' kbar F i n.unop
  have hM := LAdicSheaf.geometricCompactlySupportedCohomologyMap_π f j kbar φ i n.unop
  have hM' := LAdicSheaf.geometricCompactlySupportedCohomologyMap_π
    (X := fieldExtensionScheme B X f k')
    (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
    (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') φ) i n.unop
  have hN := geometricCompactSupportFieldExtensionIso_hom_naturality B X ℓ f j k' kbar i φ n.unop
  rw [Category.assoc, hG, ← Category.assoc, hM, Category.assoc, hN, ← Category.assoc, ← hF,
    Category.assoc, Category.assoc, hM']

/-- A functor carries the powers of an endomorphism to the powers of its image. -/
alias map_end_pow_twisted := map_end_pow

section Frobenius

variable (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
  (hcard : Fintype.card k = p ^ q) (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * (m + 1)))
  (F : LAdicSheaf.{u, u + 1} B X ℓ)

/-- **The twisted trace on `Hⁱ_c` after a finite extension of the base field**: for `k'` with
`q ^ (m + 1)` elements and `ψ : F ⟶ F`, `Tr(g⁻¹ψ ∘ π_{X'}^* | Hⁱ_c(X'_k̄, g⁻¹F) ⊗ ℚ_ℓ)` equals
`Tr(ψ ∘ (π_X^*) ^ (m + 1) | Hⁱ_c(X_k̄, F) ⊗ ℚ_ℓ)`. -/
public theorem
    LAdicSheaf.trace_rationalMap_comp_rationalGeometricCompactlySupportedFrobenius_fieldExtension
    (ψ : F ⟶ F) :
    LinearMap.trace ℚ_[ℓ] _
        (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
            (LAdicSheaf.geometricCompactlySupportedCohomologyMap
              (X := fieldExtensionScheme B X f k')
              (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
              (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') ψ) i)).hom ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
            (fieldExtensionScheme B X f k') ℓ
            (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p
            (q * (m + 1)) hcard' (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i).hom) =
      LinearMap.trace ℚ_[ℓ] _
        (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
            (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i)).hom ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom ^ (m + 1)) := by
  have hc := LAdicSheaf.fieldExtensionCohomologyIso_comm B X ℓ f j k' kbar F i p q hcard m hcard'
  have hn := LAdicSheaf.fieldExtensionCohomologyIso_hom_naturality B X ℓ f j k' kbar i ψ
  have hcomb : (((End.of (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
      F i)) ^ (m + 1)).asHom ≫ LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i) ≫
        (LAdicSheaf.fieldExtensionCohomologyIso B X ℓ f j k' kbar F i).hom =
      (LAdicSheaf.fieldExtensionCohomologyIso B X ℓ f j k' kbar F i).hom ≫
        (LAdicSheaf.geometricCompactlySupportedFrobenius B (fieldExtensionScheme B X f k') ℓ
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p
          (q * (m + 1)) hcard' (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i ≫
        LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fieldExtensionScheme B X f k')
          (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
          (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k') ψ) i) := by
    rw [Category.assoc, hn, reassoc_of% hc]
  have h := congrArg (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map hcomb
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    map_end_pow_twisted] at h
  have hl := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_comp] at hl
  have hp : ((End.of (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
      hcard F i)) ^ (m + 1)).asHom.hom =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom ^
        (m + 1) := by
    have h₀ := map_pow (ModuleCat.endRingEquiv
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i))
      (End.of (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i))
      (m + 1)
    simp only [ModuleCat.endRingEquiv_apply] at h₀
    exact h₀
  refine (trace_eq_of_linearEquiv_comm
    (LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F i).toLinearEquiv _ _
      ?_).symm
  rw [← hp]
  exact hl

end Frobenius

end Stacks.EtaleCohomology

end
