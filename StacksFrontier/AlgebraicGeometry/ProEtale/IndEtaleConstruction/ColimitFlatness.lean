module

public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Colimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness along a filtered colimit presentation

A module which is a filtered colimit of flat modules is flat, and the same holds for faithful
flatness of a commutative algebra. Both statements are phrased for a
`CategoryTheory.Limits.ColimitPresentation`, that is, for a filtered diagram together with a
cocone exhibiting the object as its colimit; this is the form in which the sequential and
finite-subcoproduct colimits of the ind-étale constructions of Stacks chapter
"Pro-étale cohomology" arrive.

The faithfully flat statement is reduced to flatness plus nontriviality of
`(A ⧸ m) ⊗[A] S` for every maximal ideal `m`, and that nontriviality is read off the colimit
in `CommRingCat` after base change along `A → A ⧸ m`.

Two consequences for a sequential diagram of rings are recorded: every transition map of a
sequence of faithfully flat maps is faithfully flat, and each leg of a colimit cocone over a
sequential diagram all of whose transition maps are faithfully flat is faithfully flat.

## Main results

* `AlgebraicGeometry.ProEtale.flat_of_colimitPresentation`
* `AlgebraicGeometry.ProEtale.faithfullyFlat_of_colimitPresentation`
* `AlgebraicGeometry.ProEtale.sequence_map_faithfullyFlat`
* `AlgebraicGeometry.ProEtale.faithfullyFlat_colimit_leg`

## Implementation notes

The forgetful functors out of `CommAlgCat A` preserve filtered colimits, but Mathlib does not
carry those instances; they are supplied here, built from the corresponding statements for
`CommRingCat`, `AlgCat` and `ModuleCat`. Only the one for `forget₂ (CommAlgCat A) CommRingCat` is
exported, the others being needed in this file alone.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- The forgetful functor from commutative `A`-algebras to commutative rings preserves filtered
colimits: it is the composition of an equivalence with `Under.forget`, which preserves connected
colimits. -/
instance preservesFilteredColimits_forget₂_commAlgCat (A : Type u) [CommRing A] :
    PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}) where
  preserves_filtered_colimits J _ _ := by
    have : IsConnected J := IsFiltered.isConnected J
    change PreservesColimitsOfShape J
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
        Under.forget (CommRingCat.of A))
    infer_instance

private local instance (A : Type u) [CommRing A] :
    PreservesFilteredColimitsOfSize.{u, u}
      (forget (CommAlgCat.{u} A)) :=
  HasForget₂.forget_comp (C := CommAlgCat.{u} A) (D := CommRingCat.{u}) ▸
    (Limits.comp_preservesFilteredColimits
      (forget₂ (CommAlgCat.{u} A) CommRingCat.{u})
      (forget CommRingCat.{u}) : PreservesFilteredColimitsOfSize.{u, u} _)

private local instance (A : Type u) [CommRing A] :
    PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A)) where
  preserves_filtered_colimits J _ _ := by
    have h : forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙ forget (AlgCat.{u} A) =
        forget (CommAlgCat.{u} A) := HasForget₂.forget_comp
    have : HasColimitsOfShape J (AlgCat.{u} A) := inferInstance
    have : PreservesColimitsOfShape J (forget (AlgCat.{u} A)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : ReflectsColimitsOfShape J (forget (AlgCat.{u} A)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms (J := J) (G := forget (AlgCat.{u} A))
    have hpres : PreservesColimitsOfShape J (forget (CommAlgCat.{u} A)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : PreservesColimitsOfShape J
        (forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙ forget (AlgCat.{u} A)) := h.symm ▸ hpres
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A)) (forget (AlgCat.{u} A))

private local instance (A : Type u) [CommRing A] :
    PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)) where
  preserves_filtered_colimits J _ _ := by
    have h : forget₂ (AlgCat.{u} A) (ModuleCat.{u} A) ⋙ forget (ModuleCat.{u} A) =
        forget (AlgCat.{u} A) := HasForget₂.forget_comp
    have : PreservesColimitsOfShape J (forget (ModuleCat.{u} A)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : ReflectsColimitsOfShape J (forget (ModuleCat.{u} A)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms (J := J) (G := forget (ModuleCat.{u} A))
    have hpres : PreservesColimitsOfShape J (forget (AlgCat.{u} A)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : PreservesColimitsOfShape J
        (forget₂ (AlgCat.{u} A) (ModuleCat.{u} A) ⋙ forget (ModuleCat.{u} A)) := h.symm ▸ hpres
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)) (forget (ModuleCat.{u} A))

section Evaluation

universe v w

private local instance {J : Type v} [Category J] {C : Type w} [Category C]
    [Preadditive C] [HasLimitsOfShape WalkingParallelPair C]
    [HasColimitsOfShape WalkingParallelPair C] (j : J) :
    ((evaluation J C).obj j).PreservesHomology where

/-- A short complex of functors is exact if and only if it is exact at every object, that is,
after applying every evaluation functor. -/
private lemma shortComplex_exact_iff_evaluation {J : Type v} [Category J]
    {C : Type w} [Category C] [Preadditive C] [HasZeroObject C]
    [HasLimitsOfShape WalkingParallelPair C]
    [HasColimitsOfShape WalkingParallelPair C]
    (S : ShortComplex (J ⥤ C)) [S.HasHomology] :
    S.Exact ↔ ∀ j, (S.map ((evaluation J C).obj j)).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
  refine forall_congr' fun j ↦ ?_
  let e : S.homology.obj j ≅ _ :=
    (ShortComplex.mapHomologyIso S ((evaluation J C).obj j)).symm
  rw [e.isZero_iff, ShortComplex.exact_iff_isZero_homology]

end Evaluation

open MonoidalCategory in
/-- A filtered colimit of flat modules is flat. -/
lemma flat_of_colimitPresentation {A : Type u} [CommRing A]
    {M : ModuleCat.{u} A} {J : Type u} [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J M)
    (h : ∀ j, Module.Flat A (pres.diag.obj j)) : Module.Flat A M := by
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]
  intro C hC
  let S : ShortComplex (J ⥤ ModuleCat.{u} A) :=
    { X₁ := pres.diag ⋙ tensorRight C.X₁
      X₂ := pres.diag ⋙ tensorRight C.X₂
      X₃ := pres.diag ⋙ tensorRight C.X₃
      f := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} A)).flip.map C.f
      g := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} A)).flip.map C.g
      zero := by
        simp only [← CategoryTheory.Functor.whiskerLeft_comp,
          ← Functor.map_comp, C.zero, Functor.map_zero]
        ext j
        simp }
  apply colim.exact_mapShortComplex (S := S)
      (hc₁ := isColimitOfPreserves _ pres.isColimit)
      (hc₂ := isColimitOfPreserves _ pres.isColimit)
      (hc₃ := isColimitOfPreserves _ pres.isColimit)
  · rw [shortComplex_exact_iff_evaluation]
    intro j
    exact Module.Flat.lTensor_shortComplex_exact (pres.diag.obj j) C hC
  · simp [S, whisker_exchange]
  · simp [S, whisker_exchange]

/-- A flat module is faithfully flat as soon as `(A ⧸ m) ⊗[A] M` is nontrivial for every
maximal ideal `m`. -/
@[sga "1 IV 2.1" "(i ter) ⇒ (i)"]
private lemma faithfullyFlat_of_nontrivial_tensor_quotient
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Flat A M]
    (h : ∀ (m : Ideal A), m.IsMaximal → Nontrivial ((A ⧸ m) ⊗[A] M)) :
    Module.FaithfullyFlat A M where
  submodule_ne_top m hm := by
    rw [ne_eq, ← Submodule.Quotient.subsingleton_iff, not_subsingleton_iff_nontrivial,
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.nontrivial_congr]
    exact h m hm

/-- A filtered colimit of faithfully flat commutative algebras is faithfully flat. -/
lemma faithfullyFlat_of_colimitPresentation {A : Type u} [CommRing A]
    {S : CommAlgCat.{u} A} {J : Type u} [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J S)
    (h : ∀ j, Module.FaithfullyFlat A (pres.diag.obj j)) :
    Module.FaithfullyFlat A S := by
  have : Module.Flat A S := by
    let F := forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙
      forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)
    exact flat_of_colimitPresentation (pres.map F) (fun j ↦ (h j).toFlat)
  refine faithfullyFlat_of_nontrivial_tensor_quotient fun m hm ↦ ?_
  let g : A →+* A ⧸ m := algebraMap A (A ⧸ m)
  let BC := BaseChangeAux.BC g
  let qpres : ColimitPresentation J (BC.obj S) := pres.map BC
  have hq (j : J) :
      Nontrivial ((qpres.diag ⋙ forget₂ (CommAlgCat (A ⧸ m)) CommRingCat).obj j) := by
    have hj : Nontrivial ((A ⧸ m) ⊗[A] (pres.diag.obj j)) := by
      have := h j
      exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left A (A ⧸ m)).mpr
        inferInstance
    exact (CommAlgCat.algEquivOfIso
      (BaseChangeAux.objIso g rfl (pres.diag.obj j))).toEquiv.nontrivial_congr.mpr hj
  have hcol : Nontrivial ((forget₂ _ CommRingCat).mapCocone qpres.cocone).pt :=
    CommRingCat.FilteredColimits.nontrivial
      (isColimitOfPreserves _ qpres.isColimit)
  exact (CommAlgCat.algEquivOfIso (BaseChangeAux.objIso g rfl S)).toEquiv.nontrivial_congr.mp
    hcol

/-- If every one-step transition map of a sequential diagram of rings is faithfully flat, then
so is every transition map. -/
lemma sequence_map_faithfullyFlat (F : ℕ ⥤ CommRingCat.{u})
    (hstep : ∀ n, (F.map (homOfLE (Nat.le_add_right n 1))).hom.FaithfullyFlat)
    (i j : ℕ) (h : i ≤ j) :
    (F.map (homOfLE h)).hom.FaithfullyFlat := by
  induction j generalizing i with
  | zero =>
      obtain rfl := Nat.eq_zero_of_le_zero h
      have hid : (homOfLE h : (0 : ℕ) ⟶ 0) = 𝟙 _ := Subsingleton.elim _ _
      rw [hid, F.map_id]
      exact RingHom.FaithfullyFlat.of_bijective
        ⟨fun _ _ hab ↦ hab, fun a ↦ ⟨a, rfl⟩⟩
  | succ j ih =>
      by_cases hij : i ≤ j
      · have hcomp := RingHom.FaithfullyFlat.stableUnderComposition
          _ _ (ih i hij) (hstep j)
        convert hcomp using 1
        rw [← CommRingCat.hom_comp, ← Functor.map_comp]
        congr 1
      · obtain rfl : i = j + 1 := by omega
        have hid : (homOfLE h : (j + 1 : ℕ) ⟶ j + 1) = 𝟙 _ := Subsingleton.elim _ _
        rw [hid, F.map_id]
        exact RingHom.FaithfullyFlat.of_bijective
          ⟨fun _ _ hab ↦ hab, fun a ↦ ⟨a, rfl⟩⟩

/-- Each leg of a colimit cocone over a sequential diagram of rings is faithfully flat, provided
every transition map out of the corresponding index is. -/
lemma faithfullyFlat_colimit_leg (F : ℕ ⥤ CommRingCat.{u})
    (c : Cocone F) (hc : IsColimit c)
    (h : ∀ (n : ℕ) (j : Under n), (F.map j.hom).hom.FaithfullyFlat)
    (n : ℕ) : (c.ι.app n).hom.FaithfullyFlat := by
  let E := (commAlgCatEquivUnder (F.obj n)).inverse
  let D := Under.post (X := n) F
  let c' := c.underPost n
  let V : Under n ≌ AsSmall.{u} (Under n) := AsSmall.equiv
  let U : AsSmall.{u} (Under n) ⥤ Under n := V.inverse
  let p : ColimitPresentation (AsSmall.{u} (Under n)) (E.obj c'.pt) :=
    ⟨U ⋙ D ⋙ E, ((E.mapCocone c').whisker U).ι,
      (Functor.Final.isColimitWhiskerEquiv U _).symm
        (isColimitOfPreserves E (hc.underPost n))⟩
  have hp : Module.FaithfullyFlat (F.obj n) (E.obj c'.pt) :=
    faithfullyFlat_of_colimitPresentation p (fun j ↦ by
      change (F.map (ULift.down j).hom).hom.FaithfullyFlat
      exact h n (ULift.down j))
  exact (RingHom.faithfullyFlat_algebraMap_iff).mpr hp

end AlgebraicGeometry.ProEtale

end
