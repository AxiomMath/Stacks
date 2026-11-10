module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.ComparisonDatum
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRestrict
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ToTensorModelComparison
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorPullCompatibility

/-!
# The diagonal object of a restricted diagonal open

Let `Δ : X ⟶ W` and `Δ' : X' ⟶ W'` be the closed immersions of two diagonal opens, and let
`g : W' ⟶ W` and `j : X' ⟶ X` be open immersions forming a cartesian square
`Δ' ≫ g = j ≫ Δ`. Then `Lg^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}` in `D(𝒪_{W'})`, compatibly with the derived
multiplications. For the restriction of a diagonal open along an open immersion `j : Y ⟶ X`
this is the input `eΔ`, `hmul` of `IsRelativeDualizingComplex.restrict_of`, which makes the
restriction of a relative dualizing complex to an open unconditional ("trivially the
restriction of a relative dualizing complex to an open is a relative dualizing complex", proof
of Stacks 0E2X).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalObjectPullIso`: `Lg^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictDiagonalObjectIso`:
  `Lj_W^*(Δ_*𝒪_X) ≅ Δ_{Y*}𝒪_Y`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictXi`: the restriction of `ξ`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalObjectPullIso_mul` and
  `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictDiagonalObjectIso_mul`: compatibility
  with the derived multiplications.
* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex.restrict`: the restriction of a
  relative dualizing complex along an open immersion is a relative dualizing complex.

## Implementation notes

On sheaves, `g^*(Δ_*𝒪_X) ⟶ Δ'_*𝒪_{X'}` is the adjoint transpose of the map of algebras
`Δ_*𝒪_X ⟶ g_*Δ'_*𝒪_{X'}` induced by `j`; it is invertible because on an open `V` of `W'` its
sections are `j^♯ : 𝒪_X(Δ⁻¹(gV)) ⟶ 𝒪_{X'}(Δ'⁻¹V)` and `Δ⁻¹(gV) = j(Δ'⁻¹V)` (Mathlib's
`Scheme.Modules.restrictAdjunction`). Multiplicativity is checked on pure tensors through the
canonical comparison of Stacks 01CD (`Stacks.RingedSpace.comparisonTranspose_unit_tmul`).

On complexes, the comparison of total complexes of Stacks 01CD at two complexes concentrated in
degree zero is computed on the summand `(0, 0)`, by a chase with every object a variable
(`Stacks.Duality.RelativeDualizingRestrictDiagonal.single_transport_mul`). In the derived
category, Stacks 0FP0 (`derivedPullbackTensorIso_toTensor_comm`), the comparison of the two
derived tensor products (`standardTensorIso_hom_app_app_toTensor`) and naturality of
`Lg^*(Q-) ⟶ Q(g^*-)` reduce the claim to the complex-level identity, again by a chase with every
object a variable (`derived_chase`).

The ingredients live in several spellings of the same categories (`X.ringCatSheaf`,
`Tensor.ringSheaf X.sheaf`, `RingedSite.Modules`, `KFlatDerivedPullback.Modules`) with
differently derived instances; conversions between them are expensive for the elaborator and
the kernel. Each library input is therefore restated, in one fixed spelling, in a declaration
of its own, and the chases are generic lemmas in which nothing can be unfolded.

## References

* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FP0](https://stacks.math.columbia.edu/tag/0FP0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality.RelativeDualizingRestrictDiagonal

section Single

variable {A B : Type*} [Category A] [Category B]
  (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B) (P : A ⥤ B)
  (ε : ∀ a b : A, P.obj ((F.obj a).obj b) ≅ (G.obj (P.obj a)).obj (P.obj b))
  (hε₁ : ∀ {a a' : A} (u : a ⟶ a') (b : A),
    P.map ((F.map u).app b) ≫ (ε a' b).hom = (ε a b).hom ≫ (G.map (P.map u)).app (P.obj b))
  (hε₂ : ∀ (a : A) {b b' : A} (v : b ⟶ b'),
    P.map ((F.obj a).map v) ≫ (ε a b').hom = (ε a b).hom ≫ (G.obj (P.obj a)).map (P.map v))

/-- For a bifunctor `G`, the composite `G(f, Y) ≫ G(X', g) ≫ G(f', Y') ≫ G(X'', g')` is
`G(f ≫ f', Y) ≫ G(X'', g ≫ g')`. -/
@[reassoc]
theorem bif_comp {X X' X'' Y Y' Y'' : B} (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y')
    (g' : Y' ⟶ Y'') :
    (G.map f).app Y ≫ (G.obj X').map g ≫ (G.map f').app Y' ≫ (G.obj X'').map g' =
      (G.map (f ≫ f')).app Y ≫ (G.obj X'').map (g ≫ g') := by
  rw [← NatTrans.naturality_assoc]
  simp

include hε₁ hε₂ in
/-- The degree-zero chase behind `single_transport_mul`, with every object and
morphism a variable. -/
theorem single_mul_chase {X₀ M T₀ : A} {X₀' M' T₀' T₀'' Y : B} (s : X₀ ≅ M) (s' : X₀' ≅ M')
    (sP : Y ≅ P.obj M) (μ : (F.obj M).obj M ⟶ M) (μ' : (G.obj M').obj M' ⟶ M')
    (e : P.obj M ≅ M') (sT : (F.obj M).obj M ⟶ (F.obj M).obj M)
    (sT' : (G.obj M').obj M' ⟶ (G.obj M').obj M') (hsT : sT = 𝟙 _) (hsT' : sT' = 𝟙 _)
    (ι : (F.obj X₀).obj X₀ ⟶ T₀) (Tf : P.obj T₀ ⟶ T₀') (ιP : (G.obj (P.obj X₀)).obj (P.obj X₀) ⟶
        T₀')
    (Mbf : T₀' ⟶ T₀'') (ι' : (G.obj X₀').obj X₀' ⟶ T₀'') (mf' : T₀'' ⟶ (G.obj M').obj M')
    (smf' : (G.obj M').obj M' ⟶ X₀') (mf : T₀ ⟶ (F.obj M).obj M) (smf : (F.obj M).obj M ⟶ X₀)
    (eCf : P.obj X₀ ⟶ X₀')
    (ha : P.map ι ≫ Tf = (ε X₀ X₀).hom ≫ ιP)
    (hb : ιP ≫ Mbf = (G.map eCf).app (P.obj X₀) ≫ (G.obj X₀').map eCf ≫ ι')
    (hc : ι' ≫ mf' = (G.map s'.hom).app X₀' ≫ (G.obj M').map s'.hom)
    (hd : smf' = sT' ≫ μ' ≫ s'.inv)
    (he : ι ≫ mf = (F.map s.hom).app X₀ ≫ (F.obj M).map s.hom)
    (hf : smf = sT ≫ μ ≫ s.inv)
    (hg : eCf = (P.map s.hom ≫ sP.inv) ≫ sP.hom ≫ e.hom ≫ s'.inv)
    (h : (ε M M).hom ≫ (G.map e.hom).app (P.obj M) ≫ (G.obj M').map e.hom ≫ μ' =
      P.map μ ≫ e.hom) :
    P.map ι ≫ Tf ≫ Mbf ≫ mf' ≫ smf' = P.map ι ≫ P.map (mf ≫ smf) ≫ eCf := by
  subst hsT hsT' hd hf
  have n₁ := hε₁ s.hom X₀
  have n₂ := hε₂ M s.hom
  have hu : eCf ≫ s'.hom = P.map s.hom ≫ e.hom := by rw [hg]; simp
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, ← P.map_comp_assoc, reassoc_of% he,
    bif_comp_assoc, hu, ← bif_comp_assoc, ← reassoc_of% n₁, ← reassoc_of% n₂]
  simp only [Category.id_comp, Category.assoc, Functor.map_comp]
  rw [reassoc_of% h, hg]
  simp

variable [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
  [F.Additive] [∀ Z, (F.obj Z).Additive] [G.Additive] [∀ Z, (G.obj Z).Additive] [P.Additive]

/-- The identification `P(M[0]) ≅ M'[0]` induced by `e : P M ≅ M'`. -/
abbrev singleTransportIso {M : A} {M' : B} (e : P.obj M ≅ M') :
    (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj M) ≅
      (CochainComplex.singleFunctor B 0).obj M' :=
  (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).app M ≪≫
    (CochainComplex.singleFunctor B 0).mapIso e

include hε₁ hε₂ in
/-- Let `e : P M ≅ M'` carry `P μ` to `μ'` through `ε`, and let `T` be a map of total complexes
that is `ε` on the summand `(0, 0)`. Then `T`, followed by `Tot(e ⊗ e)` and the multiplication of
`M'[0]`, is `P` of the multiplication of `M[0]` followed by `e`. -/
theorem single_transport_mul {M : A} {M' : B} (μ : (F.obj M).obj M ⟶ M)
    (μ' : (G.obj M').obj M' ⟶ M') (e : P.obj M ≅ M')
    [HomologicalComplex.HasMapBifunctor ((CochainComplex.singleFunctor A 0).obj M)
      ((CochainComplex.singleFunctor A 0).obj M) F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj M))
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj M))
      G (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor ((CochainComplex.singleFunctor B 0).obj M')
      ((CochainComplex.singleFunctor B 0).obj M') G (ComplexShape.up ℤ)]
    (T : (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor ((CochainComplex.singleFunctor A 0).obj M)
          ((CochainComplex.singleFunctor A 0).obj M) F (ComplexShape.up ℤ)) ⟶
      HomologicalComplex.mapBifunctor
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj
            M))
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj
            M))
        G (ComplexShape.up ℤ))
    (hT : P.map (HomologicalComplex.ιMapBifunctor ((CochainComplex.singleFunctor A 0).obj M)
        ((CochainComplex.singleFunctor A 0).obj M) F (ComplexShape.up ℤ) 0 0 0 (by simp)) ≫ T.f 0 =
      (ε (((CochainComplex.singleFunctor A 0).obj M).X 0)
        (((CochainComplex.singleFunctor A 0).obj M).X 0)).hom ≫
        HomologicalComplex.ιMapBifunctor
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor A
              0).obj M))
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor A
              0).obj M))
          G (ComplexShape.up ℤ) 0 0 0 (by simp))
    (h : (ε M M).hom ≫ (G.map e.hom).app (P.obj M) ≫ (G.obj M').map e.hom ≫ μ' =
      P.map μ ≫ e.hom) :
    T ≫ HomologicalComplex.mapBifunctorMap (singleTransportIso P e).hom
        (singleTransportIso P e).hom G (ComplexShape.up ℤ) ≫
      (HomologicalComplex.mapBifunctorSingleIso G M' M').hom ≫
        (CochainComplex.singleFunctor B 0).map μ' =
    (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.mapBifunctorSingleIso F M M).hom ≫
        (CochainComplex.singleFunctor A 0).map μ) ≫ (singleTransportIso P e).hom := by
  apply HomologicalComplex.to_single_hom_ext
  have hι := HomologicalComplex.ι_mapBifunctorSingleIso_hom F M M
  have hiso : IsIso (HomologicalComplex.ιMapBifunctor ((CochainComplex.singleFunctor A 0).obj M)
      ((CochainComplex.singleFunctor A 0).obj M) F (ComplexShape.up ℤ) 0 0 0 (by simp)) := by
    have : IsIso (HomologicalComplex.ιMapBifunctor ((CochainComplex.singleFunctor A 0).obj M)
      ((CochainComplex.singleFunctor A 0).obj M) F (ComplexShape.up ℤ) 0 0 0 (by simp) ≫
        (HomologicalComplex.mapBifunctorSingleIso F M M).hom.f 0) := by
      rw [hι]
      exact ((F.mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).app _ ≪≫
        (F.obj M).mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).isIso_hom
    exact IsIso.of_isIso_comp_right _ ((HomologicalComplex.mapBifunctorSingleIso F M M).hom.f 0)
  have hg : (singleTransportIso P e).hom.f 0 =
      (P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (P.obj M)).inv) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (P.obj M)).hom ≫ e.hom ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M').inv := by
    rw [Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom, Functor.mapIso_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    exact congrArg _ (HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 e.hom)
  refine (cancel_epi (P.map (HomologicalComplex.ιMapBifunctor
    ((CochainComplex.singleFunctor A 0).obj M) ((CochainComplex.singleFunctor A 0).obj M) F
      (ComplexShape.up ℤ) 0 0 0 (by simp)))).1 ?_
  exact single_mul_chase F G P ε hε₁ hε₂
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M')
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (P.obj M)) μ μ' e
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((F.obj M).obj M)).hom
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((G.obj M').obj M')).hom rfl rfl
    _ _ _ _ _ _ _ _ _ _ hT
    (HomologicalComplex.ι_mapBifunctorMap _ _ G _ 0 0 0 (by simp))
    (HomologicalComplex.ι_mapBifunctorSingleIso_hom G M' M')
    (HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 μ')
    hι
    (HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 μ)
    hg h

end Single

section DerivedChase

variable {C C' : Type*} [Category C] [Category C'] (pull : C' ⥤ C) (TR TA : C ⥤ C ⥤ C)
  (σ : TR ≅ TA)

/-- The derived-level chase: with every object and morphism a variable. -/
theorem derived_chase {P TPP TRPP QTotB : C'} {Δ' QPS QTot' QTotP QPTot : C}
    (a : TPP ⟶ TRPP) (b : pull.obj TRPP ⟶ (TR.obj (pull.obj P)).obj (pull.obj P))
    (pTIhom : pull.obj TPP ⟶ (TA.obj (pull.obj P)).obj (pull.obj P))
    (hpt : pTIhom = pull.map a ≫ b ≫ (σ.hom.app (pull.obj P)).app (pull.obj P))
    (eΔ : pull.obj P ⟶ Δ') (diagonalPullComparison : pull.obj P ⟶ QPS) (diagonalPullSingleMap : QPS
        ⟶ Δ') (heΔ : eΔ = diagonalPullComparison ≫ diagonalPullSingleMap)
    (μ' : (TA.obj Δ').obj Δ' ⟶ Δ') (t' : (TA.obj Δ').obj Δ' ⟶ QTot') (qm' : QTot' ⟶ Δ')
    (hμ' : μ' = t' ≫ qm') (tR' : (TR.obj Δ').obj Δ' ⟶ QTot')
    (hσt : (σ.hom.app Δ').app Δ' ≫ t' = tR')
    (tRPS : (TR.obj QPS).obj QPS ⟶ QTotP) (diagonalTotPullMap : QTotP ⟶ QTot')
    (htn : ((TR.map diagonalPullSingleMap).app QPS ≫ (TR.obj Δ').map diagonalPullSingleMap) ≫ tR' =
        tRPS ≫ diagonalTotPullMap)
    (tRB : TRPP ⟶ QTotB) (tB : TPP ⟶ QTotB) (ha : a ≫ tRB = tB)
    (diagonalPullTotComparison : pull.obj QTotB ⟶ QPTot) (qpT : QPTot ⟶ QTotP)
    (h0 : b ≫ ((TR.map diagonalPullComparison).app (pull.obj P) ≫ (TR.obj QPS).map
        diagonalPullComparison) ≫ tRPS =
      pull.map tRB ≫ diagonalPullTotComparison ≫ qpT)
    (μ : TPP ⟶ P) (qm : QTotB ⟶ P) (hμ : μ = tB ≫ qm)
    (qPm : QPTot ⟶ QPS) (hnat : pull.map qm ≫ diagonalPullComparison = diagonalPullTotComparison ≫
        qPm)
    (hstar : qpT ≫ diagonalTotPullMap ≫ qm' = qPm ≫ diagonalPullSingleMap) :
    pTIhom ≫ ((TA.map eΔ).app (pull.obj P) ≫ (TA.obj Δ').map eΔ) ≫ μ' = pull.map μ ≫ eΔ := by
  subst hpt heΔ hμ' hμ ha
  have n₁ := congrArg (fun φ => φ.app (pull.obj P)) (σ.hom.naturality (diagonalPullComparison ≫
      diagonalPullSingleMap))
  have n₂ := (σ.hom.app Δ').naturality (diagonalPullComparison ≫ diagonalPullSingleMap)
  dsimp only [NatTrans.comp_app] at n₁
  have hb := (bif_comp TR diagonalPullComparison diagonalPullSingleMap diagonalPullComparison
    diagonalPullSingleMap).symm
  simp only [Category.assoc] at h0 htn ⊢
  rw [← reassoc_of% n₁, ← reassoc_of% n₂, reassoc_of% hσt, reassoc_of% hb, reassoc_of% htn,
    reassoc_of% h0, hstar, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    reassoc_of% hnat]

/-- A functor carries an equality `a ≫ b ≫ c = d ≫ e` to the equality of the images. -/
theorem map_comp_comp_eq {K : Type*} [Category K] (Qf : K ⥤ C) {X₁ X₂ X₃ X₄ Y : K}
    {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄} {d : X₁ ⟶ Y} {e : Y ⟶ X₄}
    (h : a ≫ b ≫ c = d ≫ e) : Qf.map a ≫ Qf.map b ≫ Qf.map c = Qf.map d ≫ Qf.map e := by
  simp only [← Functor.map_comp, h]

omit [Category C'] in
/-- If `e : pP ≅ Δ'` carries `pμ` to `μ'` through `pTI`, then `μ' ≫ e⁻¹` is `T(e⁻¹, e⁻¹)`
followed by `pTI⁻¹` and `pμ`. -/
theorem hmul_of_key {Δ' pP X : C} (e : pP ≅ Δ') (μ' : (TA.obj Δ').obj Δ' ⟶ Δ')
    (pTI : X ≅ (TA.obj pP).obj pP) (pμ : X ⟶ pP)
    (h : pTI.hom ≫ ((TA.map e.hom).app pP ≫ (TA.obj Δ').map e.hom) ≫ μ' = pμ ≫ e.hom) :
    μ' ≫ e.inv = (TA.map e.inv).app Δ' ≫ (TA.obj pP).map e.inv ≫ pTI.inv ≫ pμ := by
  have h' : pTI.inv ≫ pμ = ((TA.map e.hom).app pP ≫ (TA.obj Δ').map e.hom) ≫ μ' ≫ e.inv := by
    rw [Iso.inv_comp_eq]
    simp only [Category.assoc] at h ⊢
    rw [reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
  have hE : ((TA.map e.inv).app Δ' ≫ (TA.obj pP).map e.inv) ≫
      (TA.map e.hom).app pP ≫ (TA.obj Δ').map e.hom = 𝟙 _ := by
    rw [Category.assoc, bif_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id]
  rw [h']
  simp only [Category.assoc] at hE ⊢
  rw [reassoc_of% hE]

end DerivedChase

end Stacks.Duality.RelativeDualizingRestrictDiagonal
namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec.AlgebraSheaf

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf TopCat.Sheaf

section

variable {X : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf X)

/-- The sections of the module underlying an algebra sheaf form a commutative ring. -/
local instance sectionsCommRing' (U : (X.Opens)ᵒᵖ) :
    CommRing ((moduleOfAlgebra A).val.obj U) :=
  inferInstanceAs (CommRing (A.right.obj.obj U))

/-- On sections, the multiplication of `A` sends the image of `a ⊗ₜ b` under the
sheafification unit to `a * b`. -/
theorem algebraSheaf_mul_unit_tmul (U : (X.Opens)ᵒᵖ) (a b : (moduleOfAlgebra A).val.obj U) :
    PresheafOfModules.Hom.app (mul A).val U
      (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
        (PresheafOfModules.tensorObj (moduleOfAlgebra A).val (moduleOfAlgebra A).val)) U
        (a ⊗ₜ b)) = a * b := by
  have h2 := (PresheafOfModules.hom_congr_apply' (sheafificationHomEquiv_mul A) U (a ⊗ₜ b)).trans
    (PresheafOfModules.ofBilinear_tmul _ U a b)
  refine Eq.trans ?_ (h2.trans ?_)
  · rfl
  · rfl

end

section Main

variable {X W X' W' : Scheme.{u}} {Δ : X ⟶ W} {Δ' : X' ⟶ W'} (g : W' ⟶ W) (j : X' ⟶ X)
  (w : Δ' ≫ g = j ≫ Δ)

/-- The map of `𝒪_W`-algebras `Δ_*𝒪_X ⟶ (Δ' ≫ g)_*𝒪_{X'}` induced by `j`, for a commutative
square `Δ' ≫ g = j ≫ Δ`. -/
def pushforwardAlgebraPullMap : pushforwardAlgebra Δ ⟶ pushforwardAlgebra (Δ' ≫ g) :=
  pushforwardAlgebraMapAux Δ j ≫ eqToHom (congrArg pushforwardAlgebra w.symm)

/-- `Δ_*𝒪_X ⟶ g_*Δ'_*𝒪_{X'}`, the underlying map of `𝒪_W`-modules of
`pushforwardAlgebraPullMap`. -/
def pushforwardModulePullMap : underlyingModule (pushforwardAlgebra Δ) ⟶
    (Scheme.Modules.pushforward g).obj (underlyingModule (pushforwardAlgebra Δ')) :=
  underlyingModuleMap (pushforwardAlgebraPullMap g j w)

include w in
/-- For a commutative square `Δ' ≫ g = j ≫ Δ`, `(Δ' ≫ g)⁻¹(U) ≤ j⁻¹(Δ⁻¹(U))`. -/
theorem preimage_comp_le_of_comm (U : W.Opens) : (Δ' ≫ g) ⁻¹ᵁ U ≤ j ⁻¹ᵁ Δ ⁻¹ᵁ U :=
  (congrArg (fun φ : X' ⟶ W => φ ⁻¹ᵁ U) w).le

/-- On sections over `U`, `pushforwardModulePullMap` is
`j.appLE : 𝒪_X(Δ⁻¹U) ⟶ 𝒪_{X'}((Δ' ≫ g)⁻¹U)`. -/
theorem pushforwardModulePullMap_app (U : W.Opens) (x) :
    (pushforwardModulePullMap g j w).app U x = (j.appLE (Δ ⁻¹ᵁ U) ((Δ' ≫ g) ⁻¹ᵁ U)
        (preimage_comp_le_of_comm g j w U)) x := by
  change ((pushforwardAlgebraPullMap g j w).right.hom.app (op U)) x = _
  rw [pushforwardAlgebraPullMap, pushforwardAlgebraMapAux_app Δ j _ w.symm U
      (preimage_comp_le_of_comm g j w U)]
  rfl

variable [IsOpenImmersion g]

/-- `g^*(Δ_*𝒪_X) ⟶ Δ'_*𝒪_{X'}`, the adjoint transpose of `pushforwardModulePullMap`. -/
def pullPushforwardModuleHom : (Scheme.Modules.pullback g).obj (underlyingModule
    (pushforwardAlgebra Δ)) ⟶
    underlyingModule (pushforwardAlgebra Δ') :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm (pushforwardModulePullMap g
      j w)

/-- `pullPushforwardModuleHom` is the comparison of the left adjoints of `g_*`, followed by the
transpose of `pushforwardModulePullMap` along `Scheme.Modules.restrictAdjunction g`. -/
theorem pullPushforwardModuleHom_eq : pullPushforwardModuleHom g j w =
    (Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.restrictAdjunction g)).hom.app _ ≫
      ((Scheme.Modules.restrictAdjunction g).homEquiv _ _).symm (pushforwardModulePullMap g j w) :=
          by
  unfold pullPushforwardModuleHom
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, ← Category.assoc,
    ← (Adjunction.leftAdjointUniq _ _).hom.naturality, Category.assoc,
    Adjunction.leftAdjointUniq_hom_app_counit]

/-- For an open immersion `j`, `j.appLE U V` is an isomorphism when `U` is the image of `V`. -/
theorem isIso_appLE_of_image_eq [IsOpenImmersion j] {U : X.Opens} {V : X'.Opens}
    (hU : j ''ᵁ V = U) (h : V ≤ j ⁻¹ᵁ U) : IsIso (j.appLE U V h) := by
  subst hU
  rw [← Scheme.Hom.appIso_hom']
  infer_instance

include w in
/-- For a commutative square `Δ' ≫ g = j ≫ Δ`, `Δ'⁻¹(V) ≤ j⁻¹(Δ⁻¹(g(V)))`. -/
theorem preimage_le_preimage_image_of_comm (V : W'.Opens) : Δ' ⁻¹ᵁ V ≤ j ⁻¹ᵁ Δ ⁻¹ᵁ (g ''ᵁ V) := by
  intro x hx
  change Δ.base (j.base x) ∈ g ''ᵁ V
  rw [← Scheme.Hom.comp_apply, ← w, Scheme.Hom.comp_apply]
  exact ⟨_, hx, rfl⟩

/-- On sections over `V`, the transpose of `pushforwardModulePullMap` along
`Scheme.Modules.restrictAdjunction g` is `j.appLE : 𝒪_X(Δ⁻¹(gV)) ⟶ 𝒪_{X'}(Δ'⁻¹V)`. -/
theorem pullPushforwardTranspose_app (V : W'.Opens) (x) : (((Scheme.Modules.restrictAdjunction
    g).homEquiv _ _).symm
    (pushforwardModulePullMap g j w)).app V x = (j.appLE (Δ ⁻¹ᵁ (g ''ᵁ V)) (Δ' ⁻¹ᵁ V)
        (preimage_le_preimage_image_of_comm g j w V)) x := by
  rw [Adjunction.homEquiv_counit, Scheme.Modules.Hom.comp_app]
  rw [ConcreteCategory.comp_apply, Scheme.Modules.restrictAdjunction_counit_app_app]
  exact (congrArg (fun y => (X'.presheaf.map ((TopologicalSpace.Opens.map Δ'.base).op.map
    (eqToHom (g.preimage_image_eq V).symm).op)) y) (pushforwardModulePullMap_app g j w (g ''ᵁ V)
        x)).trans
    ((ConcreteCategory.comp_apply (j.appLE _ _ _) (X'.presheaf.map _) x).symm.trans
      (ConcreteCategory.congr_hom (j.appLE_map _ _) x))

/-- For a cartesian square, the transpose of `pushforwardModulePullMap` along
`Scheme.Modules.restrictAdjunction g` is an isomorphism. -/
theorem isIso_pullPushforwardTranspose [IsOpenImmersion j] (hsq : IsPullback Δ' j g Δ) :
    IsIso (((Scheme.Modules.restrictAdjunction g).homEquiv _ _).symm (pushforwardModulePullMap g j
        hsq.w)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  have hU : j ''ᵁ (Δ' ⁻¹ᵁ V) = Δ ⁻¹ᵁ (g ''ᵁ V) :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback hsq V
  have := isIso_appLE_of_image_eq j hU (preimage_le_preimage_image_of_comm g j hsq.w V)
  have hb := ConcreteCategory.bijective_of_isIso (j.appLE _ _ (preimage_le_preimage_image_of_comm g
      j hsq.w V))
  rw [ConcreteCategory.isIso_iff_bijective]
  have hf : ⇑(ConcreteCategory.hom ((((Scheme.Modules.restrictAdjunction g).homEquiv _ _).symm
      (pushforwardModulePullMap g j hsq.w)).app V)) =
      ⇑(ConcreteCategory.hom (j.appLE _ _ (preimage_le_preimage_image_of_comm g j hsq.w V))) :=
    funext (pullPushforwardTranspose_app g j hsq.w V)
  rw [hf]
  exact hb

/-- **`g^*(Δ_*𝒪_X) ⟶ Δ'_*𝒪_{X'}` is an isomorphism** when the square is cartesian. -/
theorem isIso_pullPushforwardModuleHom [IsOpenImmersion j] (hsq : IsPullback Δ' j g Δ) : IsIso
    (pullPushforwardModuleHom g j hsq.w) := by
  rw [pullPushforwardModuleHom_eq]
  have := isIso_pullPushforwardTranspose g j hsq
  infer_instance

/-- The sections of the module underlying an algebra sheaf on `W'` form a commutative ring. -/
local instance sectionsCommRing'' (A : Stacks.RelativeSpec.AlgebraSheaf W') (U : (W'.Opens)ᵒᵖ) :
    CommRing ((moduleOfAlgebra A).val.obj U) :=
  inferInstanceAs (CommRing (A.right.obj.obj U))

omit [IsOpenImmersion g] in
/-- `pushforwardModulePullMap` is multiplicative on sections. -/
theorem pushforwardModulePullMap_mul (U : (W.Opens)ᵒᵖ) (x y : (moduleOfAlgebra (pushforwardAlgebra
    Δ)).val.obj U) :
    PresheafOfModules.Hom.app (pushforwardModulePullMap g j w).val U (x * y) =
      (show (moduleOfAlgebra (pushforwardAlgebra Δ')).val.obj (op (g ⁻¹ᵁ U.unop)) from
          PresheafOfModules.Hom.app (pushforwardModulePullMap g j w).val U x) *
        (show (moduleOfAlgebra (pushforwardAlgebra Δ')).val.obj (op (g ⁻¹ᵁ U.unop)) from
          PresheafOfModules.Hom.app (pushforwardModulePullMap g j w).val U y) :=
  map_mul ((ringSheafMap (pushforwardAlgebraPullMap g j w)).hom.app U).hom x y

omit [IsOpenImmersion g] in
/-- **The identification `g^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}` is multiplicative**: it carries the
pullback of the multiplication of `Δ_*𝒪_X`, read through the comparison of Stacks 01CD, to the
multiplication of `Δ'_*𝒪_{X'}`. -/
theorem pullPushforwardModuleHom_mul :
    Stacks.RingedSpace.comparison g.toLRSHom.toShHom (moduleOfAlgebra (pushforwardAlgebra Δ))
        (moduleOfAlgebra (pushforwardAlgebra Δ)) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨W'.toRingedSpace.presheaf, W'.toRingedSpace.IsSheaf⟩)).map
          ((pullPushforwardModuleHom g j w, pullPushforwardModuleHom g j w) : ((_, _) : _ × _) ⟶
              (_, _)) ≫
        mul (pushforwardAlgebra Δ') =
    (Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).map (mul (pushforwardAlgebra Δ)) ≫
      pullPushforwardModuleHom g j w := by
  apply ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Stacks.RingedSpace.homEquiv_comparison]
  have hψ : (Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv _ _
      (pullPushforwardModuleHom g j w) =
      pushforwardModulePullMap g j w :=
    Equiv.apply_symm_apply _ _
  refine Eq.trans ?_ ((Adjunction.homEquiv_naturality_left _ (mul (pushforwardAlgebra Δ))
    (pullPushforwardModuleHom g j w)).trans (congrArg (fun φ => mul (pushforwardAlgebra Δ) ≫ φ)
        hψ)).symm
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun U x y ↦ ?_)
  have h1 := Stacks.RingedSpace.comparisonTranspose_unit_tmul g.toLRSHom.toShHom
    (moduleOfAlgebra (pushforwardAlgebra Δ)) (moduleOfAlgebra (pushforwardAlgebra Δ)) U x y
  have h2 := Stacks.RingedSpace.tensorSheaf_map_unit_tmul W'.toRingedSpace
      (pullPushforwardModuleHom g j w) (pullPushforwardModuleHom g j w)
    (op (g ⁻¹ᵁ U.unop))
    (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (moduleOfAlgebra (pushforwardAlgebra Δ)) U
        x)
    (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (moduleOfAlgebra (pushforwardAlgebra Δ)) U
        y)
  have h4 : ∀ z, PresheafOfModules.Hom.app (pullPushforwardModuleHom g j w).val (op (g ⁻¹ᵁ U.unop))
      (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (moduleOfAlgebra (pushforwardAlgebra Δ))
        U z) = PresheafOfModules.Hom.app (pushforwardModulePullMap g j w).val U z := fun z =>
    (Stacks.RingedSpace.homEquiv_val_app g.toLRSHom.toShHom _ _ (pullPushforwardModuleHom g j w) U
        z).symm.trans
      (PresheafOfModules.hom_congr_apply' (congrArg SheafOfModules.Hom.val hψ) U z)
  have h3 := algebraSheaf_mul_unit_tmul (pushforwardAlgebra Δ') (op (g ⁻¹ᵁ U.unop))
    (PresheafOfModules.Hom.app (pushforwardModulePullMap g j w).val U x)
    (PresheafOfModules.Hom.app (pushforwardModulePullMap g j w).val U y)
  have h5 := algebraSheaf_mul_unit_tmul (pushforwardAlgebra Δ) U x y
  have h6 := pushforwardModulePullMap_mul g j w U x y
  exact (congrArg (fun t => PresheafOfModules.Hom.app (mul (pushforwardAlgebra Δ')).val
      (op (g ⁻¹ᵁ U.unop)) (PresheafOfModules.Hom.app ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨W'.toRingedSpace.presheaf, W'.toRingedSpace.IsSheaf⟩)).map
          ((pullPushforwardModuleHom g j w, pullPushforwardModuleHom g j w) : ((_, _) : _ × _) ⟶
              (_, _))).val (op (g ⁻¹ᵁ U.unop)) t)) h1).trans
    ((congrArg (PresheafOfModules.Hom.app (mul (pushforwardAlgebra Δ')).val
      (op (g ⁻¹ᵁ U.unop))) h2).trans
    ((congrArg (fun t => PresheafOfModules.Hom.app (mul (pushforwardAlgebra Δ')).val
      (op (g ⁻¹ᵁ U.unop)) (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf W'.toRingedSpace.sheaf)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf W'.toRingedSpace.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj (O := W'.toRingedSpace.sheaf.obj)
          (moduleOfAlgebra (pushforwardAlgebra Δ')).val
          (moduleOfAlgebra (pushforwardAlgebra Δ')).val)) (op (g ⁻¹ᵁ U.unop)) t))
      (congrArg₂ (· ⊗ₜ ·) (h4 x) (h4 y))).trans
    (h3.trans (h6.symm.trans (congrArg (PresheafOfModules.Hom.app (pushforwardModulePullMap g j
        w).val U) h5.symm)))))

section Complex

variable [IsOpenImmersion j] (hsq : IsPullback Δ' j g Δ)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- The pullback of sheaves of modules along `g`, between the categories of modules over
`Tensor.ringSheaf`. -/
abbrev pullModules : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf) ⥤
    SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf W'.sheaf) :=
  StacksDraft.KFlat.modulePullback g.toLRSHom.toShHom

/-- Pullback of sheaves of modules is additive. -/
instance pullModules_additive : (pullModules g).Additive :=
  RingedSpaceModuleAdjunction.modulePullback_additive g.toLRSHom.toShHom

/-- Degreewise pullback of complexes along `g`. -/
abbrev pullComplexes := (pullModules g).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `g^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}`. -/
def pullPushforwardModuleIso : (pullModules g).obj (moduleOfAlgebra (pushforwardAlgebra Δ)) ≅
    moduleOfAlgebra (pushforwardAlgebra Δ') :=
  @asIso _ _ _ _ (pullPushforwardModuleHom g j hsq.w) (isIso_pullPushforwardModuleHom g j hsq)

/-- `g^*(Δ_*𝒪_X[0]) ≅ Δ'_*𝒪_{X'}[0]`. -/
def pullSingleIso := Stacks.Duality.RelativeDualizingRestrictDiagonal.singleTransportIso
    (pullModules g) (pullPushforwardModuleIso g j hsq)

end Complex

end Main

section Derived

open Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

section One

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- The total complex `Tot(Δ_*𝒪_X[0] ⊗ Δ_*𝒪_X[0])`, as an object of `D(𝒪_W)`. -/
abbrev diagonalTotObject : Std D.W :=
  DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex D.W.sheaf).obj
    (single D.diagonalAlgebra)).obj (single D.diagonalAlgebra))

/-- The canonical map `Δ_*𝒪_X ⊗ᴸ Δ_*𝒪_X ⟶ Tot(Δ_*𝒪_X[0] ⊗ Δ_*𝒪_X[0])`. -/
def diagonalToTensor : ((tensor D.W).obj D.diagonalObject).obj D.diagonalObject ⟶
    D.diagonalTotObject :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct
    (Stacks.SheafOfModules.ringedSite D.W.sheaf)).toTensor (single D.diagonalAlgebra)
      (single D.diagonalAlgebra)

/-- The multiplication of complexes, in `D(𝒪_W)`. -/
def diagonalTotMul : D.diagonalTotObject ⟶ D.diagonalObject :=
  DerivedCategory.Q.map (singleMul D.diagonalAlgebra)

/-- The derived multiplication is `diagonalToTensor` followed by `diagonalTotMul`. -/
theorem diagonalMul_eq_toTensor_comp : D.diagonalMul = D.diagonalToTensor ≫ D.diagonalTotMul := rfl

/-- The canonical map of the ringed-site derived tensor product. -/
def diagonalToTensorRingedSite : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    D.W.sheaf).obj
      D.diagonalObject).obj D.diagonalObject ⟶ D.diagonalTotObject :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct D.W.sheaf).toTensor
    (single D.diagonalAlgebra) (single D.diagonalAlgebra)

/-- `standardTensorIso` followed by `diagonalToTensor` is `diagonalToTensorRingedSite`. -/
theorem standardTensorIso_hom_diagonalToTensor :
    ((Stacks.Duality.ProjectionFormulaLocallySmall.standardTensorIso D.W).hom.app
      D.diagonalObject).app D.diagonalObject ≫ D.diagonalToTensor = D.diagonalToTensorRingedSite :=
  Stacks.Duality.ProjectionFormulaLocallySmall.standardTensorIso_hom_app_app_toTensor D.W
    (single D.diagonalAlgebra) (single D.diagonalAlgebra)

/-- The inverse of `standardTensorIso` followed by `diagonalToTensorRingedSite` is
`diagonalToTensor`. -/
theorem standardTensorIso_inv_diagonalToTensorRingedSite :
    ((Stacks.Duality.ProjectionFormulaLocallySmall.standardTensorIso D.W).inv.app
      D.diagonalObject).app D.diagonalObject ≫ D.diagonalToTensorRingedSite = D.diagonalToTensor :=
  (Iso.inv_comp_eq (((Stacks.Duality.ProjectionFormulaLocallySmall.standardTensorIso
    D.W).app D.diagonalObject).app D.diagonalObject)).2
    D.standardTensorIso_hom_diagonalToTensor.symm

end One

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} (D : DiagonalOpen f)
  (D' : DiagonalOpen f') (g : D'.W ⟶ D.W) [IsOpenImmersion g] (j : X' ⟶ X) [IsOpenImmersion j]
  (hsq : IsPullback D'.diag j g D.diag)

/-- `g^*(Δ_*𝒪_X[0])`, the degreewise pullback. -/
abbrev diagonalPullSingle : CochainComplex
    (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D'.W.sheaf)) ℤ :=
  (pullComplexes g).obj ((CochainComplex.singleFunctor
    (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
      (moduleOfAlgebra D.diagonalAlgebra))

/-- `Lg^*(Δ_*𝒪_X) ⟶ g^*(Δ_*𝒪_X)`. -/
def diagonalPullComparison : (pull g).obj D.diagonalObject ⟶ (DerivedCategory.Q.obj
    (diagonalPullSingle D D' g) : Std D'.W) :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans g.toLRSHom.toShHom).app
    (single D.diagonalAlgebra)

/-- Along an open immersion the derived pullback of `Δ_*𝒪_X` is its degreewise pullback. -/
instance isIso_diagonalPullComparison : IsIso (diagonalPullComparison D D' g) :=
  Stacks.Cohomology.BaseChangeCover.isIso_derivedPullbackNatTrans_app_of_isOpenImmersion
    g.toLRSHom.toShHom (single D.diagonalAlgebra)

/-- `g^*(Δ_*𝒪_X) ⟶ Δ'_*𝒪_{X'}` in `D(𝒪_{W'})`. -/
def diagonalPullSingleMap : (DerivedCategory.Q.obj (diagonalPullSingle D D' g) : Std D'.W) ⟶
    D'.diagonalObject :=
  DerivedCategory.Q.map (pullSingleIso g j hsq).hom

/-- `diagonalPullSingleMap` is an isomorphism. -/
instance isIso_diagonalPullSingleMap : IsIso (diagonalPullSingleMap D D' g j hsq) := by
  unfold diagonalPullSingleMap; infer_instance

/-- **`Lg^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}`.** -/
def diagonalObjectPullIso : (pull g).obj D.diagonalObject ≅ D'.diagonalObject :=
  asIso (diagonalPullComparison D D' g) ≪≫ asIso (diagonalPullSingleMap D D' g j hsq)

/-- `Tot(g^*Δ_*𝒪_X[0] ⊗ g^*Δ_*𝒪_X[0])`. -/
abbrev diagonalTotPullObject : Std D'.W :=
  DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor (diagonalPullSingle D D' g)
      (diagonalPullSingle D D' g)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D'.W.sheaf) (ComplexShape.up ℤ))

/-- `g^*Tot(Δ_*𝒪_X[0] ⊗ Δ_*𝒪_X[0])`. -/
abbrev diagonalPullTotObject : Std D'.W :=
  DerivedCategory.Q.obj ((pullComplexes g).obj (HomologicalComplex.mapBifunctor
    ((CochainComplex.singleFunctor
      (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
        (moduleOfAlgebra D.diagonalAlgebra))
    ((CochainComplex.singleFunctor
      (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
        (moduleOfAlgebra D.diagonalAlgebra)) (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u,
            u} D.W.sheaf) (ComplexShape.up ℤ)))

/-- The canonical map of the ringed-site derived tensor product at `g^*Δ_*𝒪_X`. -/
def diagonalPullToTensorRingedSite : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    D'.W.sheaf).obj
      (DerivedCategory.Q.obj (diagonalPullSingle D D' g) : Std D'.W)).obj
      (DerivedCategory.Q.obj (diagonalPullSingle D D' g) : Std D'.W) ⟶ diagonalTotPullObject D D' g
          :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct D'.W.sheaf).toTensor
    (diagonalPullSingle D D' g) (diagonalPullSingle D D' g)

/-- `Tot(pullSingleIso ⊗ pullSingleIso)`. -/
def diagonalTotPullMap : diagonalTotPullObject D D' g ⟶ D'.diagonalTotObject :=
  DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (pullSingleIso g j hsq).hom
      (pullSingleIso g j hsq).hom
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D'.W.sheaf) (ComplexShape.up ℤ))

/-- Naturality of the canonical map of the ringed-site derived tensor product along
`diagonalPullSingleMap`: it is carried to `diagonalTotPullMap`. -/
theorem diagonalToTensorRingedSite_naturality :
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor D'.W.sheaf).map
        (diagonalPullSingleMap D D' g j hsq)).app (DerivedCategory.Q.obj (diagonalPullSingle D D'
            g) : Std D'.W) ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor D'.W.sheaf).obj
        D'.diagonalObject).map (diagonalPullSingleMap D D' g j hsq)) ≫
            D'.diagonalToTensorRingedSite =
      diagonalPullToTensorRingedSite D D' g ≫ diagonalTotPullMap D D' g j hsq := by
  rw [Category.assoc]
  exact (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    D'.W.sheaf).toTensor_naturality (pullSingleIso g j hsq).hom (pullSingleIso g j hsq).hom

/-- The comparison of Stacks 079U at `Δ_*𝒪_X`, for the ringed-site derived tensor product. -/
def diagonalPullTensorComparison : (pull g).obj
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor D.W.sheaf).obj
        D.diagonalObject).obj D.diagonalObject) ⟶
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor D'.W.sheaf).obj
      ((pull g).obj D.diagonalObject)).obj ((pull g).obj D.diagonalObject) :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g.toLRSHom.toShHom).hom.app
    (D.diagonalObject, D.diagonalObject)

omit [IsOpenImmersion g] in
/-- At `Δ_*𝒪_X`, `pullTensorIso` is `diagonalPullTensorComparison` conjugated by
`standardTensorIso`. -/
theorem pullTensorIso_hom_diagonal : (pullTensorIso g D.diagonalObject D.diagonalObject).hom =
    (pull g).map (((Stacks.Duality.ProjectionFormulaLocallySmall.standardTensorIso D.W).inv.app
      D.diagonalObject).app D.diagonalObject) ≫ diagonalPullTensorComparison D D' g ≫
      ((Stacks.Duality.ProjectionFormulaLocallySmall.standardTensorIso D'.W).hom.app
        ((pull g).obj D.diagonalObject)).app ((pull g).obj D.diagonalObject) := rfl

/-- `Lg^*Tot(Δ_*𝒪_X[0] ⊗ Δ_*𝒪_X[0]) ⟶ g^*Tot(Δ_*𝒪_X[0] ⊗ Δ_*𝒪_X[0])`. -/
def diagonalPullTotComparison : (pull g).obj D.diagonalTotObject ⟶ diagonalPullTotObject D D' g :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans g.toLRSHom.toShHom).app
    (((Stacks.SheafOfModules.Tensor.tensorComplex D.W.sheaf).obj (single D.diagonalAlgebra)).obj
      (single D.diagonalAlgebra))

/-- The comparison of total complexes of Stacks 01CD at `Δ_*𝒪_X[0]`. -/
def diagonalTotTransport : (pullComplexes g).obj (HomologicalComplex.mapBifunctor
      ((CochainComplex.singleFunctor
        (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
          (moduleOfAlgebra D.diagonalAlgebra))
      ((CochainComplex.singleFunctor
        (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
          (moduleOfAlgebra D.diagonalAlgebra)) (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u,
              u, u} D.W.sheaf) (ComplexShape.up ℤ)) ⟶
    HomologicalComplex.mapBifunctor (diagonalPullSingle D D' g) (diagonalPullSingle D D' g)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D'.W.sheaf) (ComplexShape.up ℤ) :=
  (Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso
    g.toLRSHom.toShHom).hom.app (single D.diagonalAlgebra, single D.diagonalAlgebra)

omit [IsOpenImmersion g] in
/-- Stacks 0FP0 at `Δ_*𝒪_X`: `diagonalPullTensorComparison` is compatible with the canonical maps
to total complexes through `diagonalPullTotComparison` and `diagonalTotTransport`. -/
theorem diagonalPullTensorComparison_toTensor :
    diagonalPullTensorComparison D D' g ≫
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor D'.W.sheaf).map
        (diagonalPullComparison D D' g)).app ((pull g).obj D.diagonalObject) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor D'.W.sheaf).obj
          (DerivedCategory.Q.obj (diagonalPullSingle D D' g) : Std D'.W)).map
              (diagonalPullComparison D D' g)) ≫
      diagonalPullToTensorRingedSite D D' g =
    (pull g).map D.diagonalToTensorRingedSite ≫ diagonalPullTotComparison D D' g ≫
        DerivedCategory.Q.map (diagonalTotTransport D D' g) :=
  Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_toTensor_comm
    g.toLRSHom.toShHom (single D.diagonalAlgebra) (single D.diagonalAlgebra)

/-- `g^*` of the multiplication of complexes. -/
def diagonalPullTotMul : diagonalPullTotObject D D' g ⟶ (DerivedCategory.Q.obj (diagonalPullSingle
    D D' g) : Std D'.W) :=
  DerivedCategory.Q.map ((pullComplexes g).map ((HomologicalComplex.mapBifunctorSingleIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.W.sheaf) (moduleOfAlgebra
        D.diagonalAlgebra) (moduleOfAlgebra D.diagonalAlgebra)).hom ≫
      (CochainComplex.singleFunctor
        (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).map
          (mul D.diagonalAlgebra)))

omit [IsOpenImmersion g] in
/-- Naturality of `Lg^*(Q-) ⟶ Q(g^*-)` along the multiplication of complexes. -/
theorem pull_diagonalTotMul_comparison : (pull g).map D.diagonalTotMul ≫ diagonalPullComparison D
    D' g = diagonalPullTotComparison D D' g ≫ diagonalPullTotMul D D' g :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans g.toLRSHom.toShHom).naturality
    (singleMul D.diagonalAlgebra)

omit [IsOpenImmersion g] in
/-- On the summand `(0, 0)`, `diagonalTotTransport` is the comparison `comparisonAppIso`. -/
theorem diagonalTotTransport_ι :
    (pullModules g).map (HomologicalComplex.ιMapBifunctor
        ((CochainComplex.singleFunctor
          (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
            (moduleOfAlgebra D.diagonalAlgebra))
        ((CochainComplex.singleFunctor
          (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
            (moduleOfAlgebra D.diagonalAlgebra)) (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u,
                u, u, u} D.W.sheaf) (ComplexShape.up ℤ) 0 0 0
          (by simp)) ≫ (diagonalTotTransport D D' g).f 0 =
      (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso g.toLRSHom.toShHom
        (((CochainComplex.singleFunctor
          (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
            (moduleOfAlgebra D.diagonalAlgebra)).X 0)
        (((CochainComplex.singleFunctor
          (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf D.W.sheaf)) 0).obj
            (moduleOfAlgebra D.diagonalAlgebra)).X 0)).hom ≫
        HomologicalComplex.ιMapBifunctor (diagonalPullSingle D D' g) (diagonalPullSingle D D' g)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D'.W.sheaf) (ComplexShape.up ℤ)
              0 0 0 (by simp) :=
  Functor.ι_mapBifunctorTotalIso_hom
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.W.toRingedSpace.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D'.W.toRingedSpace.sheaf)
    (StacksDraft.KFlat.modulePullback g.toLRSHom.toShHom)
    (StacksDraft.KFlat.modulePullback g.toLRSHom.toShHom)
    (StacksDraft.KFlat.modulePullback g.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso g.toLRSHom.toShHom) _ _
    (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso_naturality_left g.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso_naturality_right
      g.toLRSHom.toShHom) (single D.diagonalAlgebra) (single D.diagonalAlgebra) 0 0 0 _

/-- `diagonalTotTransport`, followed by `diagonalTotPullMap` and the multiplication of complexes
of `Δ'_*𝒪_{X'}`, is `diagonalPullTotMul` followed by `diagonalPullSingleMap`. -/
theorem diagonalTotTransport_mul :
    DerivedCategory.Q.map (diagonalTotTransport D D' g) ≫ diagonalTotPullMap D D' g j hsq ≫
        D'.diagonalTotMul =
      diagonalPullTotMul D D' g ≫ diagonalPullSingleMap D D' g j hsq :=
  Stacks.Duality.RelativeDualizingRestrictDiagonal.map_comp_comp_eq DerivedCategory.Q
    (Stacks.Duality.RelativeDualizingRestrictDiagonal.single_transport_mul
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.W.sheaf)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D'.W.sheaf) (pullModules g)
      (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso g.toLRSHom.toShHom)
      (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso_naturality_left
        g.toLRSHom.toShHom)
      (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso_naturality_right
        g.toLRSHom.toShHom)
      (mul D.diagonalAlgebra) (mul D'.diagonalAlgebra) (pullPushforwardModuleIso g j hsq)
          (diagonalTotTransport D D' g)
      (diagonalTotTransport_ι D D' g) (pullPushforwardModuleHom_mul g j hsq.w))

/-- The identification of the diagonal objects carries `Lg^*` of the derived multiplication
to the derived multiplication, read through Stacks 079U. -/
theorem diagonalObjectPullIso_key :
    (pullTensorIso g D.diagonalObject D.diagonalObject).hom ≫
      (((tensor D'.W).map (D.diagonalObjectPullIso D' g j hsq).hom).app
          ((pull g).obj D.diagonalObject) ≫
        ((tensor D'.W).obj D'.diagonalObject).map (D.diagonalObjectPullIso D' g j hsq).hom) ≫
        D'.diagonalMul =
    (pull g).map D.diagonalMul ≫ (D.diagonalObjectPullIso D' g j hsq).hom :=
  Stacks.Duality.RelativeDualizingRestrictDiagonal.derived_chase (pull g)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor D'.W.sheaf) (tensor D'.W)
    (Stacks.Duality.ProjectionFormulaLocallySmall.standardTensorIso D'.W)
    _ (diagonalPullTensorComparison D D' g) _ (pullTensorIso_hom_diagonal D D' g)
    _ (diagonalPullComparison D D' g) (diagonalPullSingleMap D D' g j hsq) rfl
    _ D'.diagonalToTensor D'.diagonalTotMul D'.diagonalMul_eq_toTensor_comp
        D'.diagonalToTensorRingedSite D'.standardTensorIso_hom_diagonalToTensor
    (diagonalPullToTensorRingedSite D D' g) (diagonalTotPullMap D D' g j hsq)
        (diagonalToTensorRingedSite_naturality D D' g j hsq)
    D.diagonalToTensorRingedSite D.diagonalToTensor
        D.standardTensorIso_inv_diagonalToTensorRingedSite
    (diagonalPullTotComparison D D' g) (DerivedCategory.Q.map (diagonalTotTransport D D' g))
        (diagonalPullTensorComparison_toTensor D D' g)
    _ D.diagonalTotMul D.diagonalMul_eq_toTensor_comp (diagonalPullTotMul D D' g)
        (pull_diagonalTotMul_comparison D D' g)
    (diagonalTotTransport_mul D D' g j hsq)

/-- **`Lg^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}` carries the derived multiplication of `Δ_*𝒪_X` to that of
`Δ'_*𝒪_{X'}`**, in the shape of the hypothesis `hmul` of `isIso_diagonalAction_transport`. -/
theorem diagonalObjectPullIso_mul :
    D'.diagonalMul ≫ (D.diagonalObjectPullIso D' g j hsq).inv =
      ((tensor D'.W).map (D.diagonalObjectPullIso D' g j hsq).inv).app D'.diagonalObject ≫
        ((tensor D'.W).obj ((pull g).obj D.diagonalObject)).map
          (D.diagonalObjectPullIso D' g j hsq).inv ≫
          (pullTensorIso g D.diagonalObject D.diagonalObject).inv ≫ (pull g).map D.diagonalMul :=
  Stacks.Duality.RelativeDualizingRestrictDiagonal.hmul_of_key (tensor D'.W)
    (D.diagonalObjectPullIso D' g j hsq) D'.diagonalMul
    (pullTensorIso g D.diagonalObject D.diagonalObject) ((pull g).map D.diagonalMul)
    (D.diagonalObjectPullIso_key D' g j hsq)

end Derived

section Restrict

open Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f) {Y : Scheme.{u}} (j : Y ⟶ X)
  [IsOpenImmersion j]

/-- **`Lj_W^*(Δ_*𝒪_X) ≅ Δ_{Y*}𝒪_Y`** for the restriction of a diagonal open along an open
immersion `j : Y ⟶ X`: `diagonalObjectPullIso` at the cartesian square
`isPullback_restrictDiag`. -/
def restrictDiagonalObjectIso :
    (pull (D.restrictInclusion j)).obj D.diagonalObject ≅ (D.restrict j).diagonalObject :=
  D.diagonalObjectPullIso (D.restrict j) (D.restrictInclusion j) j (D.isPullback_restrictDiag j)

/-- `restrictDiagonalObjectIso` is compatible with the derived multiplications, in the shape
of the hypothesis `hmul` of `IsRelativeDualizingComplex.restrict_of`. -/
theorem restrictDiagonalObjectIso_mul :
    (D.restrict j).diagonalMul ≫ (D.restrictDiagonalObjectIso j).inv =
      ((tensor (D.restrict j).W).map (D.restrictDiagonalObjectIso j).inv).app
          (D.restrict j).diagonalObject ≫
        ((tensor (D.restrict j).W).obj
          ((pull (D.restrictInclusion j)).obj D.diagonalObject)).map
            (D.restrictDiagonalObjectIso j).inv ≫
          (pullTensorIso (D.restrictInclusion j) D.diagonalObject D.diagonalObject).inv ≫
            (pull (D.restrictInclusion j)).map D.diagonalMul :=
  D.diagonalObjectPullIso_mul (D.restrict j) (D.restrictInclusion j) j
    (D.isPullback_restrictDiag j)

/-- **The restriction of `ξ`** along an open immersion `j`:
`Δ_{Y*}𝒪_Y ≅ Lj_W^*(Δ_*𝒪_X) ⟶ Lj_W^*(L pr₁^*K|_W) ≅ L pr₁^*(Lj^*K)|_{W_Y}`. -/
def restrictXi (K : Std X) (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) :
    ((D.restrict j).diagonalObject : Std (D.restrict j).W) ⟶
      (pull (D.restrict j).proj).obj ((pull j).obj K) :=
  D.restrictXiOf j (D.restrictDiagonalObjectIso j) K ξ

end Restrict

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

namespace AlgebraicGeometry.Scheme.Hom

open StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]
  {D : DiagonalOpen f} {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
  {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}

/-- **Stacks 0E2X, first step: the restriction of a relative dualizing complex to an open is a
relative dualizing complex.** For an open immersion `j : Y ⟶ X`, `(Lj^*K, ξ|_Y)` is a relative
dualizing complex for `j ≫ f` relative to the restricted diagonal open, with no further
hypothesis. Relative perfectness is read at the canonical families of certificates. -/
theorem IsRelativeDualizingComplex.restrict
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    IsRelativeDualizingComplex (j ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (j ≫ f).base)) (D.restrict j)
      ((derivedPullback j.toLRSHom.toShHom).obj K) (D.restrictXi j K ξ) :=
  hK.restrict_of j (D.restrictDiagonalObjectIso j) (D.restrictDiagonalObjectIso_mul j)

end AlgebraicGeometry.Scheme.Hom
