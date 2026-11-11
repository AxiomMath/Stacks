module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Extension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Transport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLinePointTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctorIsoOfIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationLiebermanBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationUntwistedIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealizationUnique

/-!
# A realization `(G, F[2] ≅ G(𝟏(1)))` is determined by its classical Weil cohomology theory

Let `R = (G, F[2] ≅ G(𝟏(1)))` and `R' = (G', F[2] ≅ G'(𝟏(1)))` be realizations of Chow motives as in
Stacks 0FH3 whose classical Weil cohomology theories (the first paragraph of the proof of Stacks
0FH3) are isomorphic. Then `R` and `R'` are isomorphic:

* the isomorphism of theories, given on varieties, extends to all smooth projective schemes and
  is an isomorphism of the data (D0)–(D3) of `G` and `G'` (Stacks 0FHK) preserving cycle classes
  and traces, the Tate lines being matched through `F[2] ≅ G(𝟏(1))` and `F[2] ≅ G'(𝟏(1))`;
* isomorphic data have isomorphic realizations of correspondences of degree zero (Stacks 0FHL),
  so `G` and `G'` restrict to isomorphic functors on correspondences, and by the uniqueness of
  Stacks 0FGH there is a monoidal isomorphism `θ : G ≅ G'` extending this isomorphism;
* `θ` carries `F[2] ≅ G(𝟏(1))` to `F[2] ≅ G'(𝟏(1))`: on `G(h(𝐏¹))²`, `θ` is the isomorphism of
  cohomology of the data, which matches the traces `x ↦ G([𝐏¹])(x ⊗ e₁)` of the two generators,
  and a generator `e₁` of the line `G'^{-2}(𝟏(1))` is determined by its trace on `𝐏¹`.

## Main results

* `Stacks.WeilCohomology.ClassicalMotiveRealization.nonempty_iso_of_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite CategoryTheory.GradedCategory
  Stacks.Chow
open Stacks.WeilCohomology.ChowMotiveCat (h tate)

universe u v

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]

variable [IsAlgClosed k]

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] WeilRealization.braidedTK WeilRealization.monoidalTK
  WeilData.corrFunctorBraided

namespace WeilRealization

attribute [local instance] GradedObject.koszulSymmetricCategory TwistedKaroubi.symmetricCategory

/-- **Stacks 0FGH, uniqueness, with the isomorphism.** If the restrictions of two realizations
`G` and `G'` along `X ↦ (X, 1, 0)` are monoidally isomorphic, by `φ` and `φ'`, to the same
symmetric monoidal functor `F₀` on correspondences of degree zero, there is a monoidal isomorphism
`θ : G ≅ G'` with `φ' ∘ θ = φ` on correspondences. -/
theorem exists_iso_of_untwisted (G G' : WeilRealization k F)
    (F₀ : DegreeZero ℚ (CorrespondenceCategory k) ⥤ GradedObject ℤ (ModuleCat.{v} F))
    [@Functor.Braided _ _ _ _ _ _ _ GradedObject.koszulBraidedCategory F₀]
    (φ : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G.functor ≅ F₀)
    (φ' : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G'.functor ≅ F₀)
    [NatTrans.IsMonoidal φ.hom] [NatTrans.IsMonoidal φ'.hom] :
    ∃ θ : G.functor ≅ G'.functor, NatTrans.IsMonoidal θ.hom ∧
      Functor.whiskerLeft (TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k)) θ.hom ≫
        φ'.hom = φ.hom := by
  obtain ⟨θ, hθ, -⟩ := TwistedKaroubi.existsUnique_iso_of_uniqueness
    (ChowMotiveCat.lefschetzKaroubi (ChowMotiveCat.projectiveLineZero k)
      ChowMotiveCat.projectiveLineZero_comp)
    (ChowMotiveCat.lefschetzKaroubiIso (ChowMotiveCat.projectiveLineZero k)
      ChowMotiveCat.projectiveLineZero_comp)
    (InvertingObject.uniqueness _ _ _ _) F₀ G.functorTK G'.functorTK φ φ'
  exact ⟨θ, hθ⟩

end WeilRealization

namespace ClassicalMotiveRealization

/-- The isomorphisms of cohomology on varieties of an isomorphism of the theories of two
realizations, as isomorphisms of the data (D0)–(D3) of the realizations given on varieties. -/
def varietyGradedIso {R R' : ClassicalMotiveRealization k F}
    (φ : ClassicalWeilCohomologyTheory.Iso R.toClassicalWeilCohomologyTheory
      R'.toClassicalWeilCohomologyTheory) :
    WeilData.VarietyGradedIso R.toWeilRealization.toWeilData R'.toWeilRealization.toWeilData where
  e V n := φ.equiv V n
  e_pull f n a := φ.equiv_pullback f n a
  e_mul V i j a b := congrArg Subtype.val (φ.equiv_mul V i j a b)
  e_one V := congrArg Subtype.val (φ.equiv_one V)

variable {R R' : ClassicalMotiveRealization k F}
  (φ : ClassicalWeilCohomologyTheory.Iso R.toClassicalWeilCohomologyTheory
    R'.toClassicalWeilCohomologyTheory)

/-- The ratio `κ = c / c'` of the coordinates of `e₁` and `e₁'`. -/
def coordRatio (R R' : ClassicalMotiveRealization k F) : Fˣ :=
  R.tateScalar * R'.tateScalar⁻¹

/-- The isomorphism of theories scales the cycle classes of the data by `κⁱ`. -/
theorem varietyGradedIso_cycleClassCoord (V : (SmoothProjective k).FullSubcategory) (i : ℕ)
    (β : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj V).obj.hom i) :
    (varietyGradedIso φ).e V (2 * (i : ℤ))
        (R.toWeilRealization.toWeilData.cycleClassCoord _ i β) =
      ((coordRatio R R' : Fˣ) : F) ^ i • R'.toWeilRealization.toWeilData.cycleClassCoord _ i β := by
  have h := φ.equiv_cycleClass V i β
  have h2 := (φ.equiv V (2 * (i : ℤ))).map_smul ((R.tateScalar ^ (-(i : ℤ)) : Fˣ) : F)
    (R.toWeilRealization.toWeilData.cycleClassCoord _ i β)
  have h3 : ((R.tateScalar ^ (-(i : ℤ)) : Fˣ) : F) •
      φ.equiv V (2 * (i : ℤ)) (R.toWeilRealization.toWeilData.cycleClassCoord _ i β) =
      ((R'.tateScalar ^ (-(i : ℤ)) : Fˣ) : F) •
        R'.toWeilRealization.toWeilData.cycleClassCoord _ i β :=
    h2.symm.trans h
  have h4 := congrArg (fun z ↦ ((R.tateScalar ^ (i : ℤ) : Fˣ) : F) • z) h3
  simp only [smul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
    one_smul] at h4
  have hu : ((R.tateScalar ^ (i : ℤ) * R'.tateScalar ^ (-(i : ℤ)) : Fˣ) : F) =
      ((coordRatio R R' : Fˣ) : F) ^ i := by
    rw [coordRatio, ← Units.val_pow_eq_pow_val, ← zpow_natCast, mul_zpow, inv_zpow, zpow_neg]
  have hu' : ((R.tateScalar ^ (i : ℤ) : Fˣ) : F) * ((R'.tateScalar ^ (-(i : ℤ)) : Fˣ) : F) =
      ((coordRatio R R' : Fˣ) : F) ^ i := by
    rw [← Units.val_mul]
    exact hu
  exact h4.trans ((smul_smul _ _ _).trans
    (congrArg (fun c : F ↦ c • R'.toWeilRealization.toWeilData.cycleClassCoord _ i β) hu'))

/-- The isomorphism of theories scales the traces of the data by `κ^d`. -/
theorem varietyGradedIso_traceCoord (V : (SmoothProjective k).FullSubcategory) (d : ℕ)
    (hV : IsNonemptyEquidimensional ((SmoothProjective.toSchemeCat k).obj V) d)
    (a : R.toWeilRealization.toWeilData.grade ((SmoothProjective.toSchemeCat k).obj V)
      (2 * (d : ℤ))) :
    R'.toWeilRealization.toWeilData.traceCoord _ d hV ((varietyGradedIso φ).e V _ a) =
      ((coordRatio R R' : Fˣ) : F) ^ d * R.toWeilRealization.toWeilData.traceCoord _ d hV a := by
  obtain rfl := hV.dim_eq (SmoothProjective.isNonemptyEquidimensional_dim V)
  have h := φ.integration_equiv V a
  change ((R'.tateScalar ^ (SmoothProjective.dim V : ℤ) : Fˣ) : F) *
      R'.toWeilRealization.toWeilData.traceCoord _ _ _ (φ.equiv V _ a) =
    ((R.tateScalar ^ (SmoothProjective.dim V : ℤ) : Fˣ) : F) *
      R.toWeilRealization.toWeilData.traceCoord _ _ _ a at h
  change R'.toWeilRealization.toWeilData.traceCoord _ _ _ (φ.equiv V _ a) = _
  have hu : ((coordRatio R R' : Fˣ) : F) ^ SmoothProjective.dim V =
      ((R'.tateScalar ^ (-(SmoothProjective.dim V : ℤ)) : Fˣ) : F) *
        ((R.tateScalar ^ (SmoothProjective.dim V : ℤ) : Fˣ) : F) := by
    rw [coordRatio, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, mul_zpow,
      inv_zpow, zpow_neg, mul_comm]
  rw [hu, mul_assoc, ← h, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
    Units.val_one, one_mul]

/-- **The isomorphism of data (D0)–(D3)** of `G` and `G'` extending the isomorphism of theories. -/
def dataIso : WeilData.Iso R.toWeilRealization.toWeilData R'.toWeilRealization.toWeilData :=
  (varietyGradedIso φ).toIso R.toWeilRealization.poincareDuality R.toWeilRealization.kunneth
    R.toWeilRealization.cycleClassAxiom R'.toWeilRealization.poincareDuality
    R'.toWeilRealization.kunneth R'.toWeilRealization.cycleClassAxiom (coordRatio R R')

theorem dataIso_preservesCycleClass : (dataIso φ).PreservesCycleClass :=
  (varietyGradedIso φ).toIso_preservesCycleClass _ _ _ _ _ _ _
    (varietyGradedIso_cycleClassCoord φ)

theorem dataIso_preservesTrace : (dataIso φ).PreservesTrace :=
  (varietyGradedIso φ).toIso_preservesTrace _ _ _ _ _ _ _ (varietyGradedIso_traceCoord φ)

/-- The scaled traces of the data extend to all schemes. -/
theorem traceCoord_dataIso (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d)
    (a : R.toWeilRealization.toWeilData.grade X (2 * (d : ℤ))) :
    R'.toWeilRealization.toWeilData.traceCoord X d hX ((dataIso φ).gradeEquiv X _ a) =
      ((coordRatio R R' : Fˣ) : F) ^ d * R.toWeilRealization.toWeilData.traceCoord X d hX a := by
  rw [dataIso, WeilData.VarietyGradedIso.gradeEquiv_toIso]
  exact WeilData.VarietyGradedIso.traceCoord_toGradedIso _ _ _ _ _ _ _
    (varietyGradedIso_traceCoord φ) X d hX a

/-- The monoidal isomorphism `G|_corr ≅ corrFunctor(W')` through the data of `G`. -/
def untwistedIsoData :
    TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ R.toWeilRealization.functor ≅
      WeilData.corrFunctor R'.toWeilRealization.poincareDuality R'.toWeilRealization.kunneth
        R'.toWeilRealization.cycleClassAxiom :=
  R.toWeilRealization.untwistedIso R.toWeilRealization.poincareDuality
      R.toWeilRealization.kunneth R.toWeilRealization.cycleClassAxiom
      (R.toWeilRealization.corrMapG_eq_corrHomMap _ _ _) ≪≫
    (dataIso φ).corrFunctorIso (dataIso_preservesCycleClass φ) (dataIso_preservesTrace φ)

instance untwistedIsoData_isMonoidal : NatTrans.IsMonoidal (untwistedIsoData φ).hom := by
  have h₁ := R.toWeilRealization.untwistedIso_isMonoidal R.toWeilRealization.poincareDuality
    R.toWeilRealization.kunneth R.toWeilRealization.cycleClassAxiom
    (R.toWeilRealization.corrMapG_eq_corrHomMap _ _ _)
  have h₂ := (dataIso φ).corrFunctorIso_isMonoidal (hA := R.toWeilRealization.poincareDuality)
    (hB := R.toWeilRealization.kunneth) (hC := R.toWeilRealization.cycleClassAxiom)
    (hA' := R'.toWeilRealization.poincareDuality) (hB' := R'.toWeilRealization.kunneth)
    (hC' := R'.toWeilRealization.cycleClassAxiom) (dataIso_preservesCycleClass φ)
    (dataIso_preservesTrace φ)
  exact NatTrans.IsMonoidal.comp _ _

/-- **The monoidal isomorphism `θ : G ≅ G'`** of Stacks 0FGH extending the isomorphism of data. -/
theorem exists_iso_of_iso :
    ∃ θ : R.toWeilRealization.functor ≅ R'.toWeilRealization.functor,
      NatTrans.IsMonoidal θ.hom ∧
      Functor.whiskerLeft (TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k)) θ.hom ≫
        (R'.toWeilRealization.untwistedIso R'.toWeilRealization.poincareDuality
          R'.toWeilRealization.kunneth R'.toWeilRealization.cycleClassAxiom
          (R'.toWeilRealization.corrMapG_eq_corrHomMap _ _ _)).hom = (untwistedIsoData φ).hom :=
  WeilRealization.exists_iso_of_untwisted R.toWeilRealization R'.toWeilRealization _
    (untwistedIsoData φ) _

/-- A vector of a Tate line is its coordinate times the basis vector. -/
theorem eq_coord_smul_tateBasis (G : WeilRealization k F) (v : G.tateLine) :
    v = tateLineCoordinate G.finrank_tateLine v • G.tateBasis := by
  apply (tateLineCoordinate G.finrank_tateLine).injective
  rw [map_smul, WeilRealization.tateBasis, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

/-- The trace of a realization in the basis `e₁⁰` of `WeilRealization.toWeilData` is the trace
of its data, in coordinates. -/
theorem gradedTrace_baseGen (G : WeilRealization k F)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (hX : IsNonemptyEquidimensional X 1)
    (a : G.toWeilData.grade X (2 * ((1 : ℕ) : ℤ))) :
    G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hX.relativeDimension)
      (G.baseGen ((1 : ℕ) : ℤ)) (2 * ((1 : ℕ) : ℤ)) (by ring) ((G.cohAlg X).gradeEquiv _ a) =
      G.toWeilData.traceCoord X 1 hX a := by
  rw [G.toWeilData_traceCoord]
  rfl

/-- **A monoidal isomorphism extending the isomorphism of data carries `e₁` to `e₁'`.** -/
theorem app_tateVec (θ : R.toWeilRealization.functor ≅ R'.toWeilRealization.functor)
    (hθm : NatTrans.IsMonoidal θ.hom)
    (hθ : Functor.whiskerLeft (TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k)) θ.hom ≫
        (R'.toWeilRealization.untwistedIso R'.toWeilRealization.poincareDuality
          R'.toWeilRealization.kunneth R'.toWeilRealization.cycleClassAxiom
          (R'.toWeilRealization.corrMapG_eq_corrHomMap _ _ _)).hom = (untwistedIsoData φ).hom) :
    θ.hom.app (tate k 1) (-2) R.tateVec = R'.tateVec := by
  have : NatTrans.IsMonoidal θ.hom := hθm
  have hP := isNonemptyEquidimensional_projectiveLineObj k
  -- `θ` on `G(h(𝐏¹))` is the isomorphism of cohomology of the data
  have hθP : ∀ (n : ℤ) (x : (R.toWeilRealization.functor.obj (TwistedKaroubi.ofObj (R := ℚ)
      (GradedCompositionData.Obj.mk (projectiveLineObj k) : CorrespondenceCategory k))) n),
      ((R'.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv n).symm
        (θ.hom.app _ n x) = (dataIso φ).gradeEquiv (projectiveLineObj k) n
          (((R.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv n).symm x) := by
    intro n x
    exact ConcreteCategory.congr_hom
      (congr($(NatTrans.congr_app hθ (WeilData.dz (projectiveLineObj k))) n)) x
  -- the test class: the class of `∞`, pulled back along the isomorphism of data
  set γ₀ := R'.toWeilRealization.toWeilData.cycleClassCoord (projectiveLineObj k) ((1 : ℕ) : ℤ)
    (infinityClass k) with hγ₀
  set a₀ := ((dataIso φ).gradeEquiv (projectiveLineObj k) _).symm γ₀ with ha₀
  have hγ₀1 : R'.toWeilRealization.toWeilData.traceCoord (projectiveLineObj k) 1 hP γ₀ = 1 :=
    WeilData.traceCoord_cycleClassCoord_infinityClass R'.toWeilRealization.poincareDuality
      R'.toWeilRealization.kunneth R'.toWeilRealization.cycleClassAxiom
  have hx₀ : θ.hom.app _ _ ((R.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _ a₀) =
      (R'.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _ γ₀ := by
    apply ((R'.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _).symm.injective
    refine (hθP _ _).trans ?_
    refine (congrArg ((dataIso φ).gradeEquiv (projectiveLineObj k) _)
      (LinearEquiv.symm_apply_apply
        ((R.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _) a₀)).trans ?_
    refine (((dataIso φ).gradeEquiv (projectiveLineObj k) _).apply_symm_apply γ₀).trans ?_
    exact (LinearEquiv.symm_apply_apply
      ((R'.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _) γ₀).symm
  have key := WeilRealization.gradedTrace_fundamentalClassMot_app θ.hom hP.relativeDimension
    (R.tateGen ((1 : ℕ) : ℤ)) ((R.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _ a₀)
  rw [hx₀] at key
  -- `θ(e₁) = μ e₁'⁰`, `e₁ = c e₁⁰`
  set μ := tateLineCoordinate R'.toWeilRealization.finrank_tateLine
    (θ.hom.app (TwistedKaroubi.tateTriple ℚ _ ((1 : ℕ) : ℤ)) _ (R.tateGen ((1 : ℕ) : ℤ))) with hμ
  have hb' : R'.toWeilRealization.baseGen ((1 : ℕ) : ℤ) = R'.toWeilRealization.tateBasis :=
    TwistedKaroubi.tateGen_one _ _
  have hθv : θ.hom.app (TwistedKaroubi.tateTriple ℚ _ ((1 : ℕ) : ℤ)) _ (R.tateGen ((1 : ℕ) : ℤ)) =
      μ • R'.toWeilRealization.baseGen ((1 : ℕ) : ℤ) :=
    (eq_coord_smul_tateBasis R'.toWeilRealization _).trans (congrArg (μ • ·) hb'.symm)
  rw [hθv] at key
  have hl : R'.toWeilRealization.functorTK.gradedTrace
      (ChowMotiveCat.fundamentalClassMot hP.relativeDimension)
      (μ • R'.toWeilRealization.baseGen ((1 : ℕ) : ℤ)) (2 * ((1 : ℕ) : ℤ)) (by ring)
      ((R'.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _ γ₀) = μ := by
    refine (Functor.gradedTrace_smul R'.toWeilRealization.functorTK _ μ _ _ _ _).trans ?_
    rw [gradedTrace_baseGen _ _ hP, hγ₀1, smul_eq_mul, mul_one]
  have hr : R.toWeilRealization.functorTK.gradedTrace
      (ChowMotiveCat.fundamentalClassMot hP.relativeDimension)
      (((R.tateScalar ^ ((1 : ℕ) : ℤ) : Fˣ) : F) • R.toWeilRealization.baseGen ((1 : ℕ) : ℤ))
      (2 * ((1 : ℕ) : ℤ)) (by ring)
      ((R.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _ a₀) =
      (R.tateScalar : F) * R.toWeilRealization.toWeilData.traceCoord _ 1 hP a₀ := by
    refine (Functor.gradedTrace_smul R.toWeilRealization.functorTK _ _ _ _ _ _).trans ?_
    rw [gradedTrace_baseGen _ _ hP, zpow_natCast, pow_one, smul_eq_mul]
  have key' : μ = (R.tateScalar : F) * R.toWeilRealization.toWeilData.traceCoord _ 1 hP a₀ :=
    hl.symm.trans (key.trans ((congrArg (fun e ↦ R.toWeilRealization.functorTK.gradedTrace
      (ChowMotiveCat.fundamentalClassMot hP.relativeDimension) e (2 * ((1 : ℕ) : ℤ)) (by ring)
      ((R.toWeilRealization.cohAlg (projectiveLineObj k)).gradeEquiv _ a₀))
        (R.tateGen_eq ((1 : ℕ) : ℤ))).trans hr))
  have hk := traceCoord_dataIso φ (projectiveLineObj k) 1 hP a₀
  rw [ha₀, LinearEquiv.apply_symm_apply, ← ha₀, hγ₀1, pow_one] at hk
  have hμc : μ = (R'.tateScalar : F) := by
    rw [key']
    have hu : ((R'.tateScalar⁻¹ : Fˣ) : F) * (R'.tateScalar : F) = 1 := Units.inv_mul _
    calc (R.tateScalar : F) * R.toWeilRealization.toWeilData.traceCoord _ 1 hP a₀
        = (R.tateScalar : F) * R.toWeilRealization.toWeilData.traceCoord _ 1 hP a₀ *
            (((R'.tateScalar⁻¹ : Fˣ) : F) * (R'.tateScalar : F)) := by rw [hu, mul_one]
      _ = ((R.tateScalar : F) * ((R'.tateScalar⁻¹ : Fˣ) : F) *
            R.toWeilRealization.toWeilData.traceCoord _ 1 hP a₀) * (R'.tateScalar : F) := by
          ring
      _ = (R'.tateScalar : F) := by
          rw [← Units.val_mul, ← coordRatio, ← hk, one_mul]
  have hmain : θ.hom.app (TwistedKaroubi.tateTriple ℚ _ ((1 : ℕ) : ℤ)) _
      (R.tateGen ((1 : ℕ) : ℤ)) = R'.tateGen ((1 : ℕ) : ℤ) := by
    have hc1 : (R'.tateScalar : F) = ((R'.tateScalar ^ ((1 : ℕ) : ℤ) : Fˣ) : F) := by
      rw [zpow_natCast, pow_one]
    exact hθv.trans ((congrArg (fun c : F ↦ c • R'.toWeilRealization.baseGen ((1 : ℕ) : ℤ))
      (hμc.trans hc1)).trans (R'.tateGen_eq _).symm)
  have h1 : R.tateGen ((1 : ℕ) : ℤ) = R.tateVec :=
    TwistedKaroubi.tateGen_one R.toWeilRealization.tate_degree R.tateVec_ne_zero
  have h1' : R'.tateGen ((1 : ℕ) : ℤ) = R'.tateVec :=
    TwistedKaroubi.tateGen_one R'.toWeilRealization.tate_degree R'.tateVec_ne_zero
  exact (congrArg (θ.hom.app (tate k 1) (-2)) h1.symm).trans (hmain.trans h1')

/-- A morphism of graded objects out of `F[2]` is determined by the image of `1`. -/
theorem tateIso_hom_comp_eq (θ : R.toWeilRealization.functor ≅ R'.toWeilRealization.functor)
    (hv : θ.hom.app (tate k 1) (-2) R.tateVec = R'.tateVec) :
    R.tateIso.hom ≫ θ.hom.app (tate k 1) = R'.tateIso.hom := by
  funext i
  by_cases hi : i = -2
  · subst hi
    change R.tateIso.hom (-2) ≫ θ.hom.app (tate k 1) (-2) = R'.tateIso.hom (-2)
    refine (Iso.cancel_iso_inv_left (GradedObject.singleObjApplyIso (-2) (ModuleCat.of F F))
      _ _).1 ?_
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    exact hv
  · exact ((GradedObject.isInitialSingleObjApply (-2) _ i hi).isZero).eq_of_src _ _

/-- **A realization is determined by its classical Weil cohomology theory.** If the theories of
`R` and `R'` are isomorphic, so are `R` and `R'`. -/
theorem nonempty_iso_of_iso (φ : ClassicalWeilCohomologyTheory.Iso R.toClassicalWeilCohomologyTheory
    R'.toClassicalWeilCohomologyTheory) : Nonempty (Iso R R') := by
  obtain ⟨θ, hθm, hθ⟩ := exists_iso_of_iso φ
  exact ⟨{ iso := θ, isMonoidal := hθm
           tateIso_hom_comp := tateIso_hom_comp_eq θ (app_tateVec φ θ hθm hθ) }⟩

end ClassicalMotiveRealization

end Stacks.WeilCohomology

end
