module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapDimensionZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedFrobeniusTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedPointReduction

/-!
# Step 9: the trace of `φ^*` with compact support on the complement of a finite set

Let `Ω` be a separably closed field, `f : Y ⟶ Spec Ω` a morphism, `φ : Y ⟶ Y` an endomorphism over
`Ω`, `i : W ⟶ Y` a closed immersion with open complement `j : V ⟶ Y`, and `φ_W : W ⟶ W` with
`φ_W ≫ i = i ≫ φ`; assume `W` finite étale over `Ω`. For a bounded below complex `C` on `Spec Ω`
consider the short exact sequence

`0 → j_! j^{-1} f^{-1} C → f^{-1} C → i_* f_W^{-1} C → 0`

with the self-map twist on `f^{-1} C`, the twist `i_*(self-map twist) ≫ (i_* φ_{W,*} ⟶ φ_* i_*)` on
the third term, and any twist on the first term compatible with these. Then

`Tr(φ^* | RΓ_c(V, C)) = Tr(φ^* | RΓ(Y, f^{-1} C)) - #Fix(φ_W) · Tr(id | Γ(Ω, C))`.

If `φ` has no fixed points on `V`, every fixed point of `φ` lies on `W`, so when moreover
`Tr(φ^* | RΓ(Y, f^{-1} C)) = #Fix(φ) · Tr(id | Γ(Ω, C))` (Weil's formula for `C = Z/ℓ^n` and `Y` a
smooth projective curve, [Stacks, Tag 03U1]) the trace with compact support on `V` vanishes. This
is Step 9 of the proof of [Stacks, Tag 03UG], with `φ = g^{-1} π`.

## Main definitions

* `Stacks.EtaleCohomology.selfMapOpenClosedShortComplex`: the short exact sequence above.
* `Stacks.EtaleCohomology.selfMapOpenClosedTwist`: its twist, given one on the first term.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_selfMapOpenClosed_eq_sub`: the trace formula above.
* `Stacks.EtaleCohomology.natCard_fixedSections_eq`: the fixed points lie on `W`.
* `Stacks.EtaleCohomology.perfectDerivedTrace_selfMapOpenClosed_eq_zero`: Step 9.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Fixed points on a closed complement -/

section FixedPoints

variable {K : Type u} [Field K] {Y W V : Scheme.{u}} (f : Y ⟶ Spec (.of K)) (φ : Y ⟶ Y)
  (i : W ⟶ Y) [IsClosedImmersion i] (j : V ⟶ Y) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  (fW : W ⟶ Spec (.of K)) (hW : fW = i ≫ f) (φW : W ⟶ W) (hi : φW ≫ i = i ≫ φ)
  (φV : V ⟶ V) (hj : φV ≫ j = j ≫ φ)

/-- A point of `B` fixed by `b` lying in the image of a preimmersion `m` compatible with
endomorphisms `a` and `b` is the image of a point fixed by `a`. -/
private theorem exists_fixed_lift {K : Type u} [Field K] {A B : Scheme.{u}} (m : A ⟶ B)
    [IsPreimmersion m] (a : A ⟶ A) (b : B ⟶ B) (h : a ≫ m = m ≫ b) {x : Spec (.of K) ⟶ B}
    (hx : x ≫ b = x) (hmem : x default ∈ Set.range m.base) : ∃ g, g ≫ m = x ∧ g ≫ a = g := by
  obtain ⟨t, ht⟩ := hmem
  obtain ⟨g, hg⟩ := exists_lift_of_isPreimmersion m x t ht
  refine ⟨g, hg, (cancel_mono m).1 ?_⟩
  rw [Category.assoc, h, ← Category.assoc, hg, hx]

include hij hW hi hj in
/-- **The fixed points lie on the closed complement.** If `φ` has no fixed `K`-point on `V`, the
fixed `K`-points of `φ` over `K` are those of `φ_W`. -/
theorem natCard_fixedSections_eq
    (hV : ∀ y : Spec (.of K) ⟶ V, y ≫ j ≫ f = 𝟙 _ → y ≫ φV ≠ y) :
    Nat.card (fixedSections f φ) = Nat.card {y : EtaleSections fW // y.1 = y.1 ≫ φW} := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun y : {y : EtaleSections fW // y.1 = y.1 ≫ φW} =>
      (⟨y.1.1 ≫ i, by rw [Category.assoc, ← hW]; exact y.1.2,
        by rw [Category.assoc, ← hi, ← Category.assoc, ← y.2]⟩ : fixedSections f φ))
    ⟨fun a b h => ?_, fun x => ?_⟩)).symm
  · exact Subtype.ext (Subtype.ext ((cancel_mono i).1 (congrArg Subtype.val h)))
  · obtain ⟨g, hg, hga⟩ := exists_fixed_lift i φW φ hi x.2.2 (by
      by_contra h
      obtain ⟨g, hg, hga⟩ := exists_fixed_lift j φV φ hj x.2.2 (by rw [hij]; exact h)
      exact hV g (by rw [← Category.assoc, hg]; exact x.2.1) hga)
    exact ⟨⟨⟨g, by rw [hW, ← Category.assoc, hg]; exact x.2.1⟩, hga.symm⟩, Subtype.ext hg⟩

end FixedPoints

/-! ### The short exact sequence and its twist -/

section Sequence

variable (Λ : Type r) [Ring Λ] {S Y W V : Scheme.{u}} (f : Y ⟶ S) (φ : Y ⟶ Y) (w : φ ≫ f = f)
  (i : W ⟶ Y) [IsClosedImmersion i] (j : V ⟶ Y) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  (fW : W ⟶ S) (hW : fW = i ≫ f) (φW : W ⟶ W) (wW : φW ≫ fW = fW) (hi : φW ≫ i = i ≫ φ)
  (C : CochainComplex.Plus (EtaleModules.{u, r} Λ S))

include hij in
/-- **The open/closed short exact sequence** `j_! j^{-1} f^{-1} C → f^{-1} C → i_* f_W^{-1} C`, the
second map being the restriction map. -/
def selfMapOpenClosedShortComplex : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ Y) ℤ) :=
  ShortComplex.mk (openClosedCochainShortComplex Λ i j hij
      ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C).obj).f
    ((NatTrans.mapHomologicalComplex (selfMapRestriction.{u, r} Λ f i fW hW) _).app C.obj) (by
      ext n : 1
      change (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app _ ≫
        (selfMapRestriction.{u, r} Λ f i fW hW).app (C.obj.X n) = 0
      rw [selfMapRestriction_app, ← Category.assoc,
        etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ i j hij, zero_comp])

/-- The identification of the third terms with those of
`Stacks.EtaleCohomology.openClosedCochainShortComplex`. -/
def selfMapOpenClosedX₃Iso :
    ((etaleModuleDirectImage.{u, r} Λ i).mapHomologicalComplex _).obj
        (((etaleModuleInverseImage.{u, r} Λ i).mapHomologicalComplex _).obj
          ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C).obj) ≅
      ((etaleModuleDirectImage.{u, r} Λ i).mapHomologicalComplex _).obj
        (((etaleModuleInverseImage.{u, r} Λ fW).mapHomologicalComplex _).obj C.obj) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (etaleModuleDirectImage.{u, r} Λ i).mapIso
      ((selfMapRestrictionIso.{u, r} Λ f i fW hW).app (C.obj.X n)))
    (fun a b _ => by
      have h := (selfMapRestrictionIso.{u, r} Λ f i fW hW).hom.naturality (C.obj.d a b)
      have h' := congrArg (etaleModuleDirectImage.{u, r} Λ i).map h
      simp only [Functor.map_comp] at h'
      exact h'.symm)

include hij in
/-- The open/closed sequence `selfMapOpenClosedShortComplex` is short exact. -/
lemma selfMapOpenClosedShortComplex_shortExact :
    (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_
    (openClosedCochainShortComplex_shortExact Λ i j hij
      ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C).obj)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (selfMapOpenClosedX₃Iso Λ f i fW hW C) ?_ ?_
  · simp [selfMapOpenClosedShortComplex]
  · ext n : 1
    simp only [selfMapOpenClosedShortComplex, selfMapOpenClosedX₃Iso, openClosedCochainShortComplex,
      Iso.refl_hom, HomologicalComplex.comp_f]
    exact selfMapRestriction_app Λ f i fW hW (C.obj.X n)

/-- The twist of the third term: `i_*` of the self-map twist of `f_W^{-1} C` followed by the
comparison `i_* φ_{W,*} ⟶ φ_* i_*`. -/
abbrev selfMapClosedTwist :
    (etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ fW).mapCochainComplexPlus.obj C) ⟶
      (etaleModuleDirectImage.{u, r} Λ φ).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, r} Λ fW).mapCochainComplexPlus.obj C)) :=
  (etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.map
      (selfMapComplexTwist.{u, r} Λ fW φW wW C) ≫
    Functor.twistTransferMap (etaleModuleDirectImage.{u, r} Λ φ)
      (etaleModuleDirectImage.{u, r} Λ φW) (etaleModuleDirectImage.{u, r} Λ i)
      (directImageTwistTransfer Λ i φW φ hi)
      ((etaleModuleInverseImage.{u, r} Λ fW).mapCochainComplexPlus.obj C)

/-- **The twist of the open/closed sequence**, given a twist `τ₁` of the first term compatible with
the self-map twist of `f^{-1} C`. -/
def selfMapOpenClosedTwist
    (τ₁ : (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).X₁ ⟶
      ((etaleModuleDirectImage.{u, r} Λ φ).mapHomologicalComplex _).obj
        (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).X₁)
    (hτ₁ : τ₁ ≫ ((etaleModuleDirectImage.{u, r} Λ φ).mapHomologicalComplex _).map
        (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).f =
      (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).f ≫
        (NatTrans.mapHomologicalComplex (selfMapTwist.{u, r} Λ f φ w) _).app C.obj) :
    selfMapOpenClosedShortComplex Λ f i j hij fW hW C ⟶
      (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).map
        ((etaleModuleDirectImage.{u, r} Λ φ).mapHomologicalComplex _) where
  τ₁ := τ₁
  τ₂ := (NatTrans.mapHomologicalComplex (selfMapTwist.{u, r} Λ f φ w) _).app C.obj
  τ₃ := (selfMapClosedTwist Λ φ i fW φW wW hi C).hom
  comm₁₂ := hτ₁
  comm₂₃ := by
    ext n : 1
    exact selfMapTwist_comp_map_selfMapRestriction Λ f i fW hW φ w φW wW hi (C.obj.X n)

end Sequence

/-! ### The trace -/

section Trace

open CategoryTheory.FilteredDerived

variable (Λ : Type r) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] {Y W V : Scheme.{u}}
  (f : Y ⟶ Spec (.of Ω)) (φ : Y ⟶ Y) (w : φ ≫ f = f)
  (i : W ⟶ Y) [IsClosedImmersion i] (j : V ⟶ Y) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  (fW : W ⟶ Spec (.of Ω)) (hW : fW = i ≫ f) (φW : W ⟶ W) (wW : φW ≫ fW = fW)
  (hi : φW ≫ i = i ≫ φ) [Etale fW] [IsFinite fW]
  (C : CochainComplex.Plus (EtaleModules.{u, r} Λ (Spec (.of Ω))))

/-- The cohomology `RΓ(Ω, Rf_*(-))` of the first term of the open/closed sequence, the cohomology
with compact support of `V`. -/
abbrev selfMapOpenCohomology :
    DerivedCategory (ModuleCat.{max (u + 1) r} Λ) :=
  Functor.twistDerivedObj (etaleModuleDirectImage.{u, r} Λ f)
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)))
    (((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
      ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C))).property)

include hij hW wW hi in
/-- **Step 9 of [Stacks, Tag 03UG], the trace formula**: for a twist `τ₁` of `j_! j^{-1} f^{-1} C`
compatible with the self-map twist of `f^{-1} C`, `Tr(τ₁ | RΓ(Ω, Rf_* j_! j^{-1} f^{-1} C))` equals
`Tr(φ^* | RΓ(Y, f^{-1} C)) - #Fix(φ_W) · Tr(id | Γ(Ω, C))`. -/
theorem perfectDerivedTrace_selfMapOpenClosed_eq_sub
    (τ₁ : (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).X₁ ⟶
      ((etaleModuleDirectImage.{u, r} Λ φ).mapHomologicalComplex _).obj
        (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).X₁)
    (hτ₁ : τ₁ ≫ ((etaleModuleDirectImage.{u, r} Λ φ).mapHomologicalComplex _).map
        (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).f =
      (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).f ≫
        (NatTrans.mapHomologicalComplex (selfMapTwist.{u, r} Λ f φ w) _).app C.obj)
    (hp₁ : StacksDraft.Perfect.IsPerfect (selfMapOpenCohomology Λ f j C))
    (hp₂ : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ f C)))
    (hp₃ : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ fW C)))
    (hΓ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (baseSectionsComplex Λ C.obj))) :
    perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, r} Λ φ) (etaleModuleDirectImage.{u, r} Λ f)
        (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))) (selfMapDirectImageComp.{u, r} Λ f φ w)
        _ (Functor.plusTwist (etaleModuleDirectImage.{u, r} Λ φ)
          (((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
            ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C))).property) τ₁))) =
      perfectDerivedTrace Λ ⟨_, hp₂⟩
          (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, r} Λ f φ w C)) -
        Nat.card (SelfMapFixedSections fW φW) • perfectDerivedTrace Λ ⟨_, hΓ⟩ (𝟙 _) := by
  have hex := etaleModuleDirectImage_exact_of_isIntegralHom Λ i
  have : PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ i) :=
    ((exactFunctor_iff _).1 hex).1
  have : PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ i) :=
    ((exactFunctor_iff _).1 hex).2
  have hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, r} Λ f).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, r} Λ fW).mapCochainComplexPlus.obj C)))))) :=
    (Functor.isPerfect_rightDerived_map_iff (etaleModuleDirectImage.{u, r} Λ f)
      (etaleModuleDirectImage.{u, r} Λ fW) (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)))
      (etaleModuleDirectImage.{u, r} Λ i)
      (etaleModuleDirectImageComp.{u, r} Λ i f fW hW) _).2 hp₃
  have hadd := Functor.perfectDerivedTrace_derivedTwistEndo_X₂_eq_add
    (etaleModuleDirectImage.{u, r} Λ φ) (etaleModuleDirectImage.{u, r} Λ f)
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))) (selfMapDirectImageComp.{u, r} Λ f φ w)
    (selfMapOpenClosedShortComplex_shortExact Λ f i j hij fW hW C)
    (((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
      ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C))).property)
    ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C).property
    (((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, r} Λ fW).mapCochainComplexPlus.obj C)).property)
    (selfMapOpenClosedTwist Λ f φ w i j hij fW hW φW wW hi C τ₁ hτ₁) hp₁ hp₂ hK
  have hcl := perfectDerivedTrace_derivedTwistEndo_directImage_eq Λ i φW φ f fW hi hW w.symm
    wW.symm ((etaleModuleInverseImage.{u, r} Λ fW).mapCochainComplexPlus.obj C)
    (selfMapComplexTwist.{u, r} Λ fW φW wW C) hK hp₃
  have hcount := perfectDerivedTrace_selfMapCohomologyEndo_eq_card_smul Λ fW φW wW C hp₃ hΓ
  rw [eq_sub_iff_add_eq]
  refine (hadd.trans ?_).symm
  refine congrArg _ ?_
  exact hcl.trans hcount

include hij hW wW hi in
/-- **Step 9 of [Stacks, Tag 03UG].** If `φ` has no fixed `Ω`-point on `V` and the trace of `φ^*`
on `RΓ(Y, f^{-1} C)` is the number of fixed points of `φ` times `Tr(id | Γ(Ω, C))` (Weil's formula,
[Stacks, Tag 03U1], for `C = Z/ℓ^n` on a smooth projective curve), then the trace of any twist of
`j_! j^{-1} f^{-1} C` compatible with the self-map twist vanishes:
`Tr((g^{-1} π)^* | RΓ_c(V, Z/ℓ^n)) = 0`. -/
theorem perfectDerivedTrace_selfMapOpenClosed_eq_zero (φV : V ⟶ V) (hj : φV ≫ j = j ≫ φ)
    (hV : ∀ y : Spec (.of Ω) ⟶ V, y ≫ j ≫ f = 𝟙 _ → y ≫ φV ≠ y)
    (τ₁ : (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).X₁ ⟶
      ((etaleModuleDirectImage.{u, r} Λ φ).mapHomologicalComplex _).obj
        (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).X₁)
    (hτ₁ : τ₁ ≫ ((etaleModuleDirectImage.{u, r} Λ φ).mapHomologicalComplex _).map
        (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).f =
      (selfMapOpenClosedShortComplex Λ f i j hij fW hW C).f ≫
        (NatTrans.mapHomologicalComplex (selfMapTwist.{u, r} Λ f φ w) _).app C.obj)
    (hp₁ : StacksDraft.Perfect.IsPerfect (selfMapOpenCohomology Λ f j C))
    (hp₂ : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ f C)))
    (hp₃ : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ fW C)))
    (hΓ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (baseSectionsComplex Λ C.obj)))
    (hweil : perfectDerivedTrace Λ ⟨_, hp₂⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, r} Λ f φ w C)) =
      Nat.card (fixedSections f φ) • perfectDerivedTrace Λ ⟨_, hΓ⟩ (𝟙 _)) :
    perfectDerivedTrace Λ ⟨_, hp₁⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, r} Λ φ) (etaleModuleDirectImage.{u, r} Λ f)
        (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))) (selfMapDirectImageComp.{u, r} Λ f φ w)
        _ (Functor.plusTwist (etaleModuleDirectImage.{u, r} Λ φ)
          (((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj
            ((etaleModuleRestriction.{u, r} Λ j).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C))).property) τ₁))) =
      0 := by
  rw [perfectDerivedTrace_selfMapOpenClosed_eq_sub Λ f φ w i j hij fW hW φW wW hi C τ₁ hτ₁ hp₁ hp₂
    hp₃ hΓ, hweil, natCard_fixedSections_eq f φ i j hij fW hW φW hi φV hj hV, sub_self]

end Trace

end Stacks.EtaleCohomology

end
