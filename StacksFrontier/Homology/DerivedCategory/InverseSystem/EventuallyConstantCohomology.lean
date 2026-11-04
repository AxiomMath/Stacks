module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantDifference
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleShortExact

/-!
# Cohomology of the derived limit of an eventually constant tower

An inverse system `F : ℕᵒᵖ ⥤ C` is *eventually constant with value* `X` when its transition maps
into some stage `N` are isomorphisms and `F N` is identified with `X`. This file records that
datum as a structure, and proves the two facts about it that the bounded cohomological dimension
results of Stacks 0D6T rest on.

The first is elementary: finitely many eventually constant systems stabilise past one common
stage, in particular on the finite window of cohomological degrees that a bounded
hypercohomology spectral sequence sees.

The second is the main point. If `(Fₙ)` is an inverse system in `D(A)`, `L` is presented as a
derived limit of it by a distinguished triangle whose second map is the Milnor difference, and
the cohomology systems `(Hʲ(Fₙ))` and `(Hʲ⁻¹(Fₙ))` are eventually constant, then the canonical map
`Hʲ(L) ⟶ X` to the value of the degree-`j` system is an isomorphism. In the Milnor short exact
sequence
`0 ⟶ R¹lim Hʲ⁻¹(Fₙ) ⟶ Hʲ(L) ⟶ lim Hʲ(Fₙ) ⟶ 0`
the left-hand term vanishes because the degree-`j - 1` tower is eventually constant, so its
Milnor difference is a split epimorphism; and the right-hand term is computed by the
stabilising stage of the degree-`j` tower.

## Main definitions

* `Stacks.InverseSystem.EventuallyConstantValue`: an inverse system together with a stage past
  which it is constant and an identification of that stage with a specified value.

## Main results

* `Stacks.InverseSystem.exists_common_stage` and
  `Stacks.InverseSystem.exists_common_stage_window`: a finite family of eventually constant
  systems is constant past one common stage.
* `Stacks.InverseSystem.map_piLift_sub_comp_piComparison`: an additive functor commutes with the
  Milnor difference of a tower through the product comparison.
* `Stacks.InverseSystem.isIso_homologyMap_proj_of_eventuallyConstant`: the cohomology of a
  presented derived limit of an eventually constant tower is the value of the tower.

## Implementation notes

The value is carried by the structure rather than quantified existentially, so that the
comparison map `Hʲ(L) ⟶ X` can be written down and the conclusion can be about *that* map
rather than about the existence of an abstract isomorphism. The stage is likewise a field, which
is what makes the comparison a specified morphism.

A derived limit is supplied by its defining distinguished triangle rather than by a
`HasDerivedLimit` predicate, so that the structural map `p : L ⟶ ∏ Fₙ` — and hence the
comparison — is the one the caller already holds.

## References

* [Stacks Project, Tag 0D6T](https://stacks.math.columbia.edu/tag/0D6T)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.InverseSystem

/-- A specified value of an eventually constant inverse system: all transition maps into a
chosen stage are isomorphisms, and that stage is identified with the value.

This is the hypothesis shape of Stacks 0D6T, whose cohomology systems are eventually
constant with prescribed values. -/
structure EventuallyConstantValue {C : Type*} [Category C]
    (F : ℕᵒᵖ ⥤ C) (X : C) where
  /-- A stage from which the inverse system is constant. -/
  index : ℕ
  /-- Every transition map from a later stage into the chosen stage is an isomorphism. -/
  isEventuallyConstant : F.IsEventuallyConstantTo (.op index)
  /-- The identification of the chosen stage with the specified value. -/
  iso : F.obj (.op index) ≅ X

/-- After the specified stage, every transition map into it is invertible.

Used throughout the proof of Stacks 0D6T. -/
lemma EventuallyConstantValue.isIso_map {C : Type*} [Category C]
    {F : ℕᵒᵖ ⥤ C} {X : C} (e : EventuallyConstantValue F X)
    {n : ℕ} (hn : e.index ≤ n) : IsIso (F.map (homOfLE hn).op) :=
  e.isEventuallyConstant (homOfLE hn).op

/-- Every transition map far enough along an eventually constant tower is invertible.

This is the hypothesis of
`Stacks.InverseSystem.isZero_cokernel_milnorDifference_functor`, as Stacks 0D6T needs it. -/
lemma EventuallyConstantValue.isIso_map_succ {C : Type*} [Category C]
    {F : ℕᵒᵖ ⥤ C} {X : C} (e : EventuallyConstantValue F X)
    {n : ℕ} (hn : e.index ≤ n) :
    IsIso (F.map (homOfLE (Nat.le_succ n)).op) :=
  e.isEventuallyConstant.isIso_map (homOfLE (Nat.le_succ n)).op (homOfLE hn).op

/-- A finite set of eventually constant cohomology systems is constant past one common stage.

The finite set of degrees is the window inspected by the spectral sequence in the proof of
Stacks 0D6T. -/
lemma exists_common_stage {C : Type*} [Category C]
    (F : ℤ → ℕᵒᵖ ⥤ C) (X : ℤ → C)
    (e : ∀ j, EventuallyConstantValue (F j) (X j)) (J : Finset ℤ) :
    ∃ N : ℕ, ∀ j ∈ J, ∃ hn : (e j).index ≤ N,
      IsIso ((F j).map (homOfLE hn).op) := by
  refine ⟨∑ j ∈ J, (e j).index, fun j hj => ?_⟩
  have hn : (e j).index ≤ ∑ j ∈ J, (e j).index :=
    Finset.single_le_sum (f := fun q => (e q).index) (fun _ _ => Nat.zero_le _) hj
  exact ⟨hn, (e j).isIso_map hn⟩

/-- One stage works simultaneously in the finite cohomological window used by the
bounded hypercohomology spectral sequence.

The window is the one appearing in the proof of Stacks 0D6T, whose width is governed by the
cohomological bound of the covered object. -/
lemma exists_common_stage_window {C : Type*} [Category C]
    (F : ℤ → ℕᵒᵖ ⥤ C) (X : ℤ → C)
    (e : ∀ j, EventuallyConstantValue (F j) (X j)) (j d : ℤ) :
    ∃ N : ℕ, ∀ q : ℤ, j - d - 2 ≤ q → q ≤ j + 1 →
      ∃ hn : (e q).index ≤ N, IsIso ((F q).map (homOfLE hn).op) := by
  obtain ⟨N, hN⟩ := exists_common_stage F X e (Finset.Icc (j - d - 2) (j + 1))
  exact ⟨N, fun q hq₁ hq₂ => hN q (Finset.mem_Icc.mpr ⟨hq₁, hq₂⟩)⟩

/-- **An additive functor commutes with the Milnor difference of a tower.** The difference
endomorphism `(xₙ) ↦ (xₙ - τₙ(xₙ₊₁))` of a countable product is carried by an additive functor
`H` to the corresponding difference endomorphism of the product of the images, through the
canonical comparison `H(∏ Xₙ) ⟶ ∏ H(Xₙ)`.

This is what lets the Milnor sequence of Stacks 07KY be pushed along a functor, as the proof of
Stacks 0D6T does. -/
theorem map_piLift_sub_comp_piComparison
    {D : Type*} [Category D] [Preadditive D]
    {A : Type*} [Category A] [Preadditive A]
    (H : D ⥤ A) [H.Additive] (X : ℕ → D) [HasProduct X]
    [HasProduct fun n : ℕ ↦ H.obj (X n)]
    (τ : ∀ n : ℕ, X (n + 1) ⟶ X n) :
    H.map (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ τ n) ≫
      piComparison H X = piComparison H X ≫ Pi.lift (fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ H.obj (X n)) n -
          Pi.π (fun n : ℕ ↦ H.obj (X n)) (n + 1) ≫ H.map (τ n)) := by
  rw [map_piLift_comp_piComparison]
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Pi.lift_π, Category.assoc, Pi.lift_π, Preadditive.comp_sub,
    piComparison_comp_π, H.map_sub, H.map_comp, ← Category.assoc,
    piComparison_comp_π]
where
  map_piLift_comp_piComparison (H : D ⥤ A) (X : ℕ → D) [HasProduct X]
      [HasProduct fun n : ℕ ↦ H.obj (X n)] (w : ∀ n : ℕ, (∏ᶜ X) ⟶ X n) :
      H.map (Pi.lift w) ≫ piComparison H X = Pi.lift (fun n ↦ H.map (w n)) := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, piComparison_comp_π, ← H.map_comp, Pi.lift_π, Pi.lift_π]

/-- **An eventually constant tower computes the cohomology of its derived limit.** Let `(Fₙ)`
be an inverse system in `D(A)` presented as a derived limit by a distinguished triangle with
first map `p : L ⟶ ∏ Fₙ`, and suppose that the cohomology systems `(Hʲ(Fₙ))` and `(Hʲ⁻¹(Fₙ))`
are eventually constant with values `X` and `Xprev`. Then the comparison
`Hʲ(L) ⟶ Hʲ(F_N) ≅ X` given by the projection to the stabilizing stage `N` is an isomorphism.

The `R¹lim` term of the Milnor sequence vanishes because the degree-`j - 1` tower is eventually
constant, and the remaining term `lim Hʲ(Fₙ)` is computed by the stabilizing stage.

This is the derived-category heart of Stacks 0D6T. -/
theorem isIso_homologyMap_proj_of_eventuallyConstant
    {A : Type*} [Category A] [Abelian A]
    [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
    (F : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (L : DerivedCategory A)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (htri : Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang (DerivedCategory A))
    (j : ℤ) (Xprev : A)
    (eprev : EventuallyConstantValue
      (F ⋙ DerivedCategory.homologyFunctor A (j - 1)) Xprev)
    (X : A)
    (e : EventuallyConstantValue (F ⋙ DerivedCategory.homologyFunctor A j) X) :
    IsIso ((DerivedCategory.homologyFunctor A j).map
      (p ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) e.index) ≫ e.iso.hom) := by
  let Hprev := DerivedCategory.homologyFunctor A (j - 1)
  let Fprev := F ⋙ Hprev
  let dprev := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫ Fprev.map (homOfLE (Nat.le_succ n)).op
  obtain ⟨ePrev, i, q, w, hePrev, hi, hproj, hshort⟩ :=
    DerivedCategory.exists_milnor_shortExact_of_distTriang F L p δ htri j
  have hZero : IsZero (cokernel dprev) :=
    isZero_cokernel_milnorDifference_functor Fprev eprev.index
      fun _ hn => eprev.isIso_map_succ hn
  have hq : IsIso q := hshort.isIso_g_iff.2 (by
    simpa [dprev, Fprev, Hprev] using hZero)
  have hprojection : IsIso
      (limit.π (F ⋙ DerivedCategory.homologyFunctor A j) (.op e.index)) :=
    e.isEventuallyConstant.isIso_π_of_isLimit (limit.isLimit _)
  have hprojIndex : q ≫ limit.π (F ⋙ DerivedCategory.homologyFunctor A j) (.op e.index) =
      (DerivedCategory.homologyFunctor A j).map p ≫
        (DerivedCategory.homologyFunctor A j).map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) e.index) := by
    simpa using hproj e.index
  rw [Functor.map_comp, ← hprojIndex]
  infer_instance

end Stacks.InverseSystem

end
