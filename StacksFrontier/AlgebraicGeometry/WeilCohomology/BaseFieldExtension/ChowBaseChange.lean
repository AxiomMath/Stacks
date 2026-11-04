module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FieldExtensionCodimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Kunneth
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassIntegral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIdempotent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDiagonal

/-!
# Chow groups of smooth projective schemes under a field extension

Let `k'/k` be an extension of fields and `X` a smooth projective scheme over `k`, with base change
`X' = X_{k'}` (`Stacks.WeilCohomology.SmoothProjectiveScheme.baseChange`). This file records, for
the proof of [Stacks, Tag 0FVT], the two facts about the base-change map
`g^* : CH^i(X) ⟶ CH^i(X')` of Chow Homology, Lemma 42.67.4 (Tag 0FVJ), that the proof uses:

* in `CH^*(-) ⊗ 𝐐 ≅ K_0(Vect(-)) ⊗ 𝐐` (Tags 0FEY, 0FEM), the class `α'` with `ch(α') ∩ [X] = α`
  base changes to the class of `g^*α`: base change commutes with capping with Chern classes
  (Tag 0FVN) and carries `[X]` to `[X']`;
* `Δ_{k'} = Δ'`: the base change of the class of the diagonal of `X` is the class of the diagonal
  of `X'`, read on `(X × X)_{k'}` through `(X × X)_{k'} ≅ X' × X'`.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.codimensionChowBaseChange` — `g^*`.

## Main results

* `symm_rationalChernCharacterAlgEquiv_codimensionChowBaseChange` — the class in
  `K_0(Vect(X_{k'})) ⊗ 𝐐` of `g^*a`.
* `codimensionChowBaseChange_diagonalClass` — `Δ_{k'} = Δ'`.

(both in `Stacks.WeilCohomology.SmoothProjectiveScheme`)

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 0FVN](https://stacks.math.columbia.edu/tag/0FVN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The structure morphism of `X_{k'}` is the second projection of `X ×_{Spec k} Spec k'`. -/
theorem baseChange_obj_hom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ((baseChange k k').obj X).obj.hom =
      pullback.snd X.obj.hom (fieldExtensionBaseChangeSituation k k').g :=
  rfl

/-- **The base-change map `g^* : CH^i(X) ⟶ CH^i(X_{k'})`** of Chow Homology, Lemma 42.67.4
(Tag 0FVJ), on the Chow groups of codimension `i` of a smooth projective scheme over `k`
(`Stacks.Chow.codimensionChowBaseChange`). -/
def codimensionChowBaseChange (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ) :
    codimensionChowGroup k X.obj.hom i →+
      codimensionChowGroup k' ((baseChange k k').obj X).obj.hom i :=
  Stacks.Chow.codimensionChowBaseChange k k' X.obj.hom i

/-- **The class in `K_0(Vect(X_{k'})) ⊗ 𝐐` of `g^*a`** (the computation in the proof of
Tag 0FVT): if `α' ∈ K_0(Vect(X)) ⊗ 𝐐` has `ch(α') ∩ [X] = a` in `CH^*(X) ⊗ 𝐐`, then
`ch((X_{k'} ⟶ X)^*α') ∩ [X_{k'}] = g^*a`. -/
theorem symm_rationalChernCharacterAlgEquiv_codimensionChowBaseChange
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (a : codimensionChowGroup k X.obj.hom i) :
    (rationalChernCharacterAlgEquiv
        (isRegular_of_smooth_over_field ((baseChange k k').obj X).obj.hom)
        (exists_bounds_relativeDimension_fieldChowSituation k'
          ((baseChange k k').obj X).obj.hom)).symm
      (smoothChowEquiv ((baseChange k k').obj X).obj.hom
        (codimensionToRationalChow k' ((baseChange k k').obj X).obj.hom i
          (codimensionChowBaseChange X i a))) =
      (VectorBundleKZero.pullback (baseChangeProj X)).toIntLinearMap.baseChange ℚ
        ((rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
          (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)).symm
          (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i a))) := by
  have := (isProjective X).isProper
  exact Stacks.Chow.symm_rationalChernCharacterAlgEquiv_codimensionChowBaseChange k k' X.obj.hom
    i a

/-- `Δ_{k'} ≫ ((X × X)_{k'} ≅ X' × X') = Δ'`: the base change of the diagonal is the diagonal. -/
theorem baseChange_map_diag_comp_baseChangeProdIso_hom
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (baseChange k k').map (diag X) ≫ (baseChangeProdIso X X).hom =
      diag ((baseChange k k').obj X) := by
  refine prod_hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeProdIso_hom_fst, ← CategoryTheory.Functor.map_comp, diag_fst,
      CategoryTheory.Functor.map_id,
      diag_fst]
  · rw [Category.assoc, baseChangeProdIso_hom_snd, ← CategoryTheory.Functor.map_comp, diag_snd,
      CategoryTheory.Functor.map_id,
      diag_snd]

/-- The Chow groups of a part of the wrong dimension of a smooth scheme of pure relative dimension
are trivial. -/
private theorem subsingleton_chowGroup_partBase_of_relativeDimension {K : Type u} [Field K]
    (Y : (SmoothProjectiveScheme K).FullSubcategory) {n m : ℕ} (h : RelativeDimension Y.obj.hom n)
    (hm : m ≠ n) (j : ℤ) :
    Subsingleton (chowGroup (fieldChowSituation K) (partBase Y.obj.hom m) j) := by
  have := isEmpty_dimPart_of_relativeDimension Y.obj.hom h hm
  exact subsingleton_chowGroup_of_isEmpty _ _ j

/-- Classes of cycles in two ways of writing one degree. -/
theorem mk_cycleAssociatedToClosedSubscheme_heq {C : ChowSituation.{u}} {Y Z : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (i : Z ⟶ Y) [IsClosedImmersion i] {a b : ℤ}
    (h : a = b) :
    QuotientAddGroup.mk' (rationalEquivalences C sY a) (cycleAssociatedToClosedSubscheme C sY i a) ≍
      QuotientAddGroup.mk' (rationalEquivalences C sY b)
        (cycleAssociatedToClosedSubscheme C sY i b) := by
  subst h
  rfl

/-- **`Δ_{k'} = Δ'`** (Tag 0FVT): for `X` nonempty and equidimensional of dimension `d`, the
base change of the class `[Δ] ∈ CH^d(X × X)` of the diagonal is the class of the diagonal of
`X' = X_{k'}`, carried to `(X × X)_{k'}` by the Gysin map of the isomorphism
`(X × X)_{k'} ≅ X' × X'`. -/
theorem codimensionChowBaseChange_diagonalClass (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ) (hX : IsNonemptyEquidimensional X d) :
    codimensionChowBaseChange (prod X X) d (diagonalClass X d) =
      codimensionGysin ((baseChange k k').obj (prod X X)).obj.hom
        (prod ((baseChange k k').obj X) ((baseChange k k').obj X)).obj.hom
        (w (baseChangeProdIso X X).hom) d (diagonalClass ((baseChange k k').obj X) d) := by
  set B := fieldExtensionBaseChangeSituation k k' with hB
  set X' := (baseChange k k').obj X with hX'
  set Y := prod X X with hY
  set Y' := (baseChange k k').obj Y with hY'
  set P := prod X' X' with hP
  set e := baseChangeProdIso (k' := k') X X with he
  have hcongr : ∀ {C : ChowSituation.{u}} {T : Scheme.{u}} {g h : T ⟶ C.S} [LocallyOfFiniteType g]
      [LocallyOfFiniteType h], g = h → schemeDeltaDimension C g = schemeDeltaDimension C h := by
    intro C T g h _ _ e
    subst e
    rfl
  -- dimensions
  have hXd : RelativeDimension X.obj.hom d := hX.relativeDimension
  have hX'd : RelativeDimension X'.obj.hom d := relativeDimension_pullbackSnd _ hXd _
  have hYd : RelativeDimension Y.obj.hom (d + d) :=
    (isNonemptyEquidimensional_prod hX hX).relativeDimension
  have hY'd : RelativeDimension Y'.obj.hom (d + d) := relativeDimension_pullbackSnd _ hYd _
  have hPd : RelativeDimension P.obj.hom (d + d) := by
    rw [Nat.add_comm]
    exact RelativeDimension.comp_of_flat (pullback.fst X'.obj.hom X'.obj.hom) X'.obj.hom
      (RelativeDimension.of_isPullback (IsPullback.of_hasPullback X'.obj.hom X'.obj.hom).flip
        hX'd) hX'd
  have he0 : RelativeDimension ((toScheme k').map e.hom) 0 :=
    relativeDimension_of_isIso _
  have hZ : schemeDeltaDimension (fieldChowSituation k') ((diag X').hom.left ≫ P.obj.hom) ≤
      ((((d + d : ℕ) : ℤ) - (d : ℕ) : ℤ) : EInt) := by
    rw [hcongr (w (diag X'))]
    have h := Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension _ hX'd
    simpa using h
  rw [SmoothProjectiveScheme.diagonalClass, SmoothProjectiveScheme.diagonalClass,
    codimensionGysin_closedSubschemeClass_of_flat Y'.obj.hom P.obj.hom (w e.hom) hY'd hPd he0
      (by simp) (diag X').hom.left d hZ]
  funext m
  show Stacks.Chow.codimensionChowBaseChange k k' Y.obj.hom d _ m = _
  rw [Stacks.Chow.codimensionChowBaseChange_apply, closedSubschemeClass_apply,
    closedSubschemeClass_apply]
  by_cases hm : m = d + d
  swap
  · exact (subsingleton_chowGroup_partBase_of_relativeDimension Y' hY'd hm _).elim _ _
  subst hm
  have hdeg : ((d + d : ℕ) : ℤ) - (d : ℕ) = (d : ℤ) := by push_cast; ring
  -- the part of `X × X` of dimension `2d` is all of it
  set α : chowGroup (fieldChowSituation k) Y.obj.hom (((d + d : ℕ) : ℤ) - (d : ℕ)) :=
    QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Y.obj.hom
      (diag X).hom.left (((d + d : ℕ) : ℤ) - (d : ℕ))) with hα
  have hincl : partPushforward Y.obj.hom (d + d) _
      (chowGroupRestrict (fieldChowSituation k) Y.obj.hom (partBase Y.obj.hom (d + d))
        (dimPart Y.obj.hom (d + d)).ι rfl _ α) = α := by
    have hsum := sum_properChowPushforward_chowGroupRestrict_dimPart k Y.obj.hom _ α
    by_cases hne : (d + d) ∈ nonemptyDimParts k Y.obj.hom
    · rw [Finset.sum_eq_single_of_mem _ hne fun d' _ hd' => by
        rw [(subsingleton_chowGroup_partBase_of_relativeDimension Y hYd hd' _).elim
          (chowGroupRestrict _ _ _ _ _ _ α) 0, map_zero]] at hsum
      exact hsum
    · exfalso
      obtain ⟨x⟩ := (isNonemptyEquidimensional_prod hX hX).nonempty
      exact hne ((mem_nonemptyDimParts k Y.obj.hom).2 ⟨x,
        mem_dimPart_of_relativeDimension Y.obj.hom (𝟙 _)
          (by simpa only [Category.id_comp] using hYd)
          (by rw [Scheme.Hom.opensRange_of_isIso]; trivial)⟩)
  rw [hincl]
  refine congrArg _ (eq_of_heq ?_)
  -- the base change of `[Δ]` is `[Δ']`, through `(X × X)_{k'} ≅ X' × X'`
  have hZΔ : schemeDeltaDimension B.base ((diag X).hom.left ≫ Y.obj.hom) ≤
      ((((d + d : ℕ) : ℤ) - (d : ℕ) : ℤ) : EInt) := by
    rw [hcongr (w (diag X)), hdeg]
    exact Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension _ hXd
  have h0 := baseChangeCyclePullback_cycleAssociatedToClosedSubscheme B Y.obj.hom
    (diag X).hom.left _ hZΔ
  have sq₁ := (isPullback_baseChange_map (k' := k') (diag X)).flip
  have hdiag : (toScheme k').map ((baseChange k k').map (diag X)) ≫ (toScheme k').map e.hom =
      (diag X').hom.left := by
    rw [← CategoryTheory.Functor.map_comp, baseChange_map_diag_comp_baseChangeProdIso_hom]
    rfl
  have hjB'' : pullback.fst ((toScheme k').map e.hom) (diag X').hom.left =
      pullback.snd ((toScheme k').map e.hom) (diag X').hom.left ≫
        (toScheme k').map ((baseChange k k').map (diag X)) := by
    rw [← cancel_mono ((toScheme k').map e.hom), pullback.condition, Category.assoc, hdiag]
  set jA := pullback.snd (diag X).hom.left (pullback.fst Y.obj.hom B.g) with hjA
  have hjAc : IsClosedImmersion jA :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (IsPullback.of_hasPullback _ _)
      inferInstance
  set jB := pullback.fst ((toScheme k').map e.hom) (diag X').hom.left with hjB'
  have hjBc : IsClosedImmersion jB := inferInstance
  have hcomp : (sq₁.isoPullback.symm ≪≫
      (asIso (pullback.snd ((toScheme k').map e.hom) (diag X').hom.left)).symm).hom ≫ jB = jA := by
    rw [Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, asIso_inv, Category.assoc, hjB'',
      IsIso.inv_hom_id_assoc]
    exact (Iso.inv_comp_eq _).2 (IsPullback.isoPullback_hom_snd sq₁).symm
  have hcyc := @cycleAssociatedToClosedSubscheme_eq_of_iso B.baseChange _ _ _
    (pullback.snd Y.obj.hom B.g) _ jA hjAc jB hjBc _ hcomp (((d + d : ℕ) : ℤ) - (d : ℕ) + B.c)
  refine (fieldBaseChangeChow_heq k k' Y.obj.hom _ _).trans ?_
  show baseChangeChowPullback B Y.obj.hom _ (QuotientAddGroup.mk' _ _) ≍ _
  rw [baseChangeChowPullback_mk, h0, hcyc]
  have hdeg' : ((d + d : ℕ) : ℤ) - (d : ℕ) + B.c = ((d + d : ℕ) : ℤ) - (d : ℕ) := by
    rw [hB, fieldExtensionBaseChangeSituation_c, add_zero]
  exact @mk_cycleAssociatedToClosedSubscheme_heq B.baseChange _ _ (pullback.snd Y.obj.hom B.g) _
    jB hjBc _ _ hdeg'

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
