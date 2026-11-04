module

import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLinePointTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationAgreement
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctorTestClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataIsoOfGraded
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Data (D0)–(D3) with isomorphic realizations are isomorphic

Let `W` and `W'` be data (D0)–(D3) satisfying (A), (B), (C) (Section 0FHA), with coefficient field
`F` of characteristic zero, and let `G`, `G'` be their realizations of correspondences of degree
zero (the functor of the proof of Stacks 0FHL, `Stacks.WeilCohomology.WeilData.corrFunctor`).
This file shows that a monoidal isomorphism `θ : G ≅ G'` gives an isomorphism of data
`W ≅ W'` (`Stacks.WeilCohomology.WeilData.isIsomorphic_of_corrFunctorIso`), the step of the proof
of Stacks 0FHM recovering the data from the functor:

* `θ` in degree `n` on `G(X) = H^*(X)` gives isomorphisms `H^n(X) ≅ H'^n(X)`, which commute with
  pullbacks by naturality on the graphs `[Γ_f]` (acting by `f^*`), with cup products by
  compatibility with the Künneth tensorator `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b` followed by restriction to
  the diagonal, and send `1` to `1` by compatibility with the unit `F ≅ H^*(Spec k)`
  (`Stacks.WeilCohomology.WeilData.gradedIsoOfCorrFunctorIso`);
* naturality on the correspondences `pr₂^!β ∈ Corr⁰(X, Y)`, acting by `a ↦ (∫_X a) γ(β)`, is the
  compatibility with traces and cycle classes required by the criterion
  `Stacks.WeilCohomology.WeilData.GradedIso.isIsomorphic`, applied with the test curve `𝐏¹_k` and
  the class of the point `∞`.

## Main definitions

* `Stacks.WeilCohomology.WeilData.corrFunctorIsoEquiv`: `θ` in degree `n` on `H^n(X)`.
* `Stacks.WeilCohomology.WeilData.gradedIsoOfCorrFunctorIso`: the degreewise isomorphisms
  `H^n(X) ≅ H'^n(X)` of a monoidal `θ`.
* `Stacks.WeilCohomology.WeilData.pullbackCorrZero`: `pr₂^!β` as a morphism of correspondences of
  degree zero.

## Main results

* `Stacks.WeilCohomology.WeilData.corrCompatible_gradedIsoOfCorrFunctorIso`.
* `Stacks.WeilCohomology.WeilData.isIsomorphic_of_corrFunctorIso`.

## References

* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Stacks.Chow CategoryTheory.GradedCategory

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme GradedObject.Monoidal

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W W' : WeilData k F}
  {hA : W.PoincareDuality} {hB : W.Kunneth} {hC : W.CycleClassAxiom hA.perfectPairing}
  {hA' : W'.PoincareDuality} {hB' : W'.Kunneth} {hC' : W'.CycleClassAxiom hA'.perfectPairing}
  (θ : corrFunctor hA hB hC ≅ corrFunctor hA' hB' hC')

/-! ### Naturality on elements -/

/-- Naturality of `θ` on elements: `θ(G(f)(a)) = G'(f)(θ(a))`. -/
theorem corrFunctorIso_hom_corrHomMap {X Y : DegreeZero ℚ (CorrespondenceCategory k)}
    (f : X ⟶ Y) (n : ℤ) (a : W.grade X.as n) :
    (θ.hom.app Y n).hom (corrHomMap hA hB hC f n a) =
      corrHomMap hA' hB' hC' f n ((θ.hom.app X n).hom a) :=
  congrArg (fun φ ↦ (φ n).hom a) (θ.hom.naturality f)

/-- **`θ` in degree `n` on `H^n(X)`**, as an isomorphism `H^n(X) ≅ H'^n(X)`. -/
def corrFunctorIsoEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    W.grade X n ≃ₗ[F] W'.grade X n :=
  ((GradedObject.eval n).mapIso (θ.app (dz X))).toLinearEquiv

/-- `corrFunctorIsoEquiv θ X n` is the degree `n` component of `θ` at `X`. -/
theorem corrFunctorIsoEquiv_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a : W.grade X n) :
    corrFunctorIsoEquiv θ X n a = (θ.hom.app (dz X) n).hom a :=
  rfl

/-- `θ` commutes with pullbacks: naturality on the graph `[Γ_f]`, which acts by `f^*`. -/
theorem corrFunctorIsoEquiv_pullDeg {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (n : ℤ) (a : W.grade Y n) :
    corrFunctorIsoEquiv θ X n (W.pullDeg f n a) =
      W'.pullDeg f n (corrFunctorIsoEquiv θ Y n a) := by
  have h := corrFunctorIso_hom_corrHomMap θ (CorrAction.graphZero f) n a
  rwa [corrHomMap_of_val_eq_graphHom hA hB hC _ f (ChowMotiveCat.homOf_graphCorrespondenceSP f),
    corrHomMap_of_val_eq_graphHom hA' hB' hC' _ f
      (ChowMotiveCat.homOf_graphCorrespondenceSP f)] at h

/-! ### The correspondences `pr₂^!β` -/

/-- The correspondence `pr₂^!β ∈ Corr⁰(X, Y)` (`Stacks.WeilCohomology.pullbackCorr`), as a
morphism of correspondences of degree zero. -/
def pullbackCorrZero {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (m : ℕ)
    (β : codimensionChowGroup k Y.obj.hom d) : dz X ⟶ dz Y :=
  DegreeZero.homMk (ChowMotiveCat.homOf 0
    ((SmoothProjectiveCorr.toCorr X Y 0).symm (pullbackCorr (X := X) (m := m) β)))
    (ChowMotiveCat.homOf_mem_grade _)

/-- The realization of `pullbackCorrZero m β` in degree `n` is the action `corrMap` of the
correspondence `pr₂^!β`. -/
theorem corrHomMap_pullbackCorrZero {W₀ : WeilData k F} (hA₀ : W₀.PoincareDuality)
    (hB₀ : W₀.Kunneth) (hC₀ : W₀.CycleClassAxiom hA₀.perfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (m : ℕ)
    (β : codimensionChowGroup k Y.obj.hom d) (n : ℤ) :
    corrHomMap hA₀ hB₀ hC₀ (pullbackCorrZero (X := X) m β) n =
      corrMap hA₀ hB₀ hC₀ X Y 0 n (pullbackCorr (X := X) (m := m) β) := by
  rw [corrHomMap, pullbackCorrZero, DegreeZero.homMk_val, ChowMotiveCat.component_homOf,
    LinearEquiv.apply_symm_apply]

/-- The action of `pr₂^!β` on `H^{2d}(X)` is `a ↦ (∫_X a) γ(β)`, as an identity in `H^{2d}(Y)`. -/
theorem corrHomMap_pullbackCorrZero_apply {W₀ : WeilData k F} (hA₀ : W₀.PoincareDuality)
    (hB₀ : W₀.Kunneth) (hC₀ : W₀.CycleClassAxiom hA₀.perfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d m : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y m)
    (β : codimensionChowGroup k Y.obj.hom d) (a : W₀.grade X (2 * (d : ℤ))) :
    corrHomMap hA₀ hB₀ hC₀ (pullbackCorrZero (X := X) m β) (2 * d) a =
      W₀.traceCoord X d hX a • W₀.cycleClassCoord Y d β := by
  rw [corrHomMap_pullbackCorrZero]
  exact Subtype.ext (corrMap_pullbackCorr hA₀ hB₀ hC₀ hX hY β a)

/-! ### Monoidality -/

section Monoidal

attribute [local instance] corrFunctorMonoidal

variable [NatTrans.IsMonoidal θ.hom]

/-- `θ` commutes with the Künneth tensorators, on elements:
`θ(pr₁^*a ∪ pr₂^*b) = pr₁^*θ(a) ∪ pr₂^*θ(b)`. -/
theorem corrFunctorIso_hom_corrFunctorμIso (X Y : DegreeZero ℚ (CorrespondenceCategory k))
    (p q n : ℤ) (h : p + q = n) (a : (corrFunctor hA hB hC).obj X p)
    (b : (corrFunctor hA hB hC).obj Y q) :
    (θ.hom.app (X ⊗ Y) n).hom (((corrFunctorμIso hA hB hC X Y).hom n).hom
        ((ιTensorObj ((corrFunctor hA hB hC).obj X) ((corrFunctor hA hB hC).obj Y) p q n h).hom
          (a ⊗ₜ b))) =
      ((corrFunctorμIso hA' hB' hC' X Y).hom n).hom
        ((ιTensorObj ((corrFunctor hA' hB' hC').obj X) ((corrFunctor hA' hB' hC').obj Y) p q n
          h).hom ((θ.hom.app X p).hom a ⊗ₜ (θ.hom.app Y q).hom b)) := by
  have h' := congrArg (fun φ ↦ (φ n).hom ((ιTensorObj ((corrFunctor hA hB hC).obj X)
    ((corrFunctor hA hB hC).obj Y) p q n h).hom (a ⊗ₜ b)))
    (NatTrans.IsMonoidal.tensor (τ := θ.hom) X Y)
  simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h'
  rwa [tensorHom_apply_ιTensorObj] at h'

/-- `θ` commutes with the units `F ≅ H^*(Spec k)`, on elements. -/
theorem corrFunctorIso_hom_corrFunctorεIso :
    (θ.hom.app (𝟙_ _) 0).hom (((corrFunctorεIso hA hB hC).hom 0).hom unitOne) =
      ((corrFunctorεIso hA' hB' hC').hom 0).hom unitOne := by
  have h' := congrArg (fun φ ↦ (φ 0).hom unitOne) (NatTrans.IsMonoidal.unit (τ := θ.hom))
  simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h'
  exact h'

/-- `θ` sends `1 ∈ H^0(Spec k)` to `1`. -/
theorem coe_corrFunctorIsoEquiv_point_one :
    (corrFunctorIsoEquiv θ (point k) 0 ⟨1, SetLike.GradedOne.one_mem⟩ : W'.H (point k)) = 1 := by
  have h := corrFunctorIso_hom_corrFunctorεIso θ
  have e : ((corrFunctorεIso hA hB hC).hom 0).hom unitOne = ⟨1, SetLike.GradedOne.one_mem⟩ :=
    Subtype.ext (corrFunctorεIso_hom_unitOne hA hB hC)
  rw [e] at h
  exact (congrArg Subtype.val h).trans (corrFunctorεIso_hom_unitOne hA' hB' hC')

/-- **The degreewise isomorphisms `H^n(X) ≅ H'^n(X)` of a monoidal isomorphism of
realizations**, commuting with pullbacks, cup products and units. -/
def gradedIsoOfCorrFunctorIso : GradedIso W W' where
  e := corrFunctorIsoEquiv θ
  e_pull := corrFunctorIsoEquiv_pullDeg θ
  e_mul X i j a b := by
    let f : dz X ⊗ dz X ⟶ dz X := CorrAction.graphZero (diag X)
    have hf := fun (W₀ : WeilData k F) (hA₀ : W₀.PoincareDuality) (hB₀ : W₀.Kunneth)
        (hC₀ : W₀.CycleClassAxiom hA₀.perfectPairing) ↦ corrHomMap_of_val_eq_graphHom hA₀ hB₀ hC₀
      f (diag X) (ChowMotiveCat.homOf_graphCorrespondenceSP (diag X)) (i + j)
    let t := ((corrFunctorμIso hA hB hC (dz X) (dz X)).hom (i + j)).hom
      ((ιTensorObj ((corrFunctor hA hB hC).obj (dz X)) ((corrFunctor hA hB hC).obj (dz X)) i j
        (i + j) rfl).hom (a ⊗ₜ b))
    have h₁ : (⟨a * b, SetLike.GradedMul.mul_mem a.2 b.2⟩ : W.grade X (i + j)) =
        corrHomMap hA hB hC f (i + j) t := by
      rw [hf W hA hB hC]
      exact Subtype.ext ((W.pull_diag_mul X a b).symm.trans (congrArg (W.pull (diag X))
        (congrArg Subtype.val
          (corrFunctorμIso_hom_apply hA hB hC (dz X) (dz X) i j (i + j) rfl a b)).symm))
    have h₂ := ((congrArg (corrFunctorIsoEquiv θ X (i + j)) h₁).trans
      (corrFunctorIso_hom_corrHomMap θ f (i + j) t)).trans
      (congrArg (corrHomMap hA' hB' hC' f (i + j))
        (corrFunctorIso_hom_corrFunctorμIso θ (dz X) (dz X) i j (i + j) rfl a b))
    refine (congrArg Subtype.val h₂).trans ?_
    rw [hf W' hA' hB' hC']
    exact (congrArg (W'.pull (diag X)) (congrArg Subtype.val
      (corrFunctorμIso_hom_apply hA' hB' hC' (dz X) (dz X) i j (i + j) rfl
        ((θ.hom.app (dz X) i).hom a) ((θ.hom.app (dz X) j).hom b)))).trans
      (W'.pull_diag_mul X _ _)
  e_one X := by
    have h₁ : (⟨1, SetLike.GradedOne.one_mem⟩ : W.grade X 0) =
        W.pullDeg (toPoint X) 0 ⟨1, SetLike.GradedOne.one_mem⟩ :=
      Subtype.ext (map_one (W.pull (toPoint X))).symm
    rw [h₁, corrFunctorIsoEquiv_pullDeg, coe_pullDeg, coe_corrFunctorIsoEquiv_point_one θ, map_one]

/-- **`θ` is compatible with the operations `a ↦ (∫_X a) γ(β)`**: naturality on `pr₂^!β`. -/
theorem corrCompatible_gradedIsoOfCorrFunctorIso :
    (gradedIsoOfCorrFunctorIso θ).CorrCompatible := by
  intro X Y d m hX hY β a
  refine (map_smul (corrFunctorIsoEquiv θ Y _) _ _).symm.trans ?_
  exact (congrArg (corrFunctorIsoEquiv θ Y _)
    (corrHomMap_pullbackCorrZero_apply hA hB hC hX hY β a).symm).trans
    ((corrFunctorIso_hom_corrHomMap θ (pullbackCorrZero (X := X) m β) (2 * d) a).trans
      (corrHomMap_pullbackCorrZero_apply hA' hB' hC' hX hY β (corrFunctorIsoEquiv θ X _ a)))

include θ in
/-- **Data (D0)–(D3) with monoidally isomorphic realizations are isomorphic**: a monoidal
isomorphism `θ : G ≅ G'` between the realizations of correspondences of degree zero (Stacks 0FHL)
gives an isomorphism of data `W ≅ W'`, through the criterion `GradedIso.isIsomorphic` with the
test curve `𝐏¹_k` and the class of the point `∞`. -/
theorem isIsomorphic_of_corrFunctorIso : W.IsIsomorphic W' :=
  GradedIso.isIsomorphic (Θ := gradedIsoOfCorrFunctorIso θ) (P := projectiveLineObj k)
    (hP := isNonemptyEquidimensional_projectiveLineObj k) (p := infinityClass k)
    (corrCompatible_gradedIsoOfCorrFunctorIso θ)
    (traceCoord_cycleClassCoord_infinityClass hA hB hC)
    (traceCoord_cycleClassCoord_infinityClass hA' hB' hC')
    hB.kunnethIsomorphism hC.pullback hC.mul hC.point
    hB'.kunnethIsomorphism hC'.pullback hC'.mul hC'.point hB hB' hA' hC'

end Monoidal

end Stacks.WeilCohomology.WeilData

end
