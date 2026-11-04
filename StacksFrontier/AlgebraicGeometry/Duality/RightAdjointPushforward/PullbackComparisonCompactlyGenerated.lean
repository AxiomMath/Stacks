module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonGeneral
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentPerfectDual
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorTriangulated
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonExactPairing
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSumsPerfectProper
public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTransAllShifts

/-!
# The comparison map with the pullback, by dévissage

Let `f : X ⟶ Y` be a morphism of schemes and `a` a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For a fixed `L`, the comparison map
`Lf^*K ⊗ᴸ a(L) ⟶ a(K ⊗ᴸ L)` is an isomorphism for every `K` once both sides are exact and
commute with direct sums as functors of `K`, and it is an isomorphism at every shift of every
member of a compact generating family of `D_QCoh(𝒪_Y)`. For a perfect proper morphism of
Noetherian schemes this gives the isomorphism `Lf^*K ⊗ᴸ f^×𝒪_Y ⟶ f^×K` of Equation 48.8.0.1.

## Main definitions

* `Stacks.Duality.twistedInverseImageTensorRightIso`: the right-hand side
  `K ↦ f^×(K ⊗ᴸ 𝒪_Y)` of the comparison map at `L = 𝒪_Y` is the twisted inverse image.

## Main results

* `Stacks.Duality.preservesColimitsOfShape_quasiCoherentDerivedTensorRight`,
  `Stacks.Duality.preservesColimitsOfShape_quasiCoherentDerivedPullback`: tensoring with a fixed
  object and derived pullback commute with direct sums on `D_QCoh`.
* `Stacks.Duality.isIso_compareWithPullbackTensor_of_forall_shift`: the comparison map is
  invertible at every `K` if it is at every shift of a compact generating family.
* `Stacks.Duality.isIso_compareWithPullbackTensor_of_isCompactlyGenerated`: the same, for a
  compact generating family all of whose shifts are dualizable.
* `Stacks.Duality.isIso_compareWithPullbackTensor_of_forall_isCompactObject`: the same over a
  quasi-compact quasi-separated base.
* `Stacks.Duality.isIso_twistedInverseImageCompareWithPullback_of_forall_isCompactObject`:
  Equation 48.8.0.1 for a perfect proper morphism of Noetherian schemes.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (α : quasiCoherentDerivedTensorSwap Y ⋙ quasiCoherentDerivedPullback' f ⟶
      (quasiCoherentDerivedPullback' f).prod (quasiCoherentDerivedPullback' f) ⋙
        quasiCoherentDerivedTensorSwap X)

/-! ### The two sides of the comparison map as functors of `K` -/

/-! ### Both sides of the comparison commute with direct sums in `K` -/

/-- **Tensoring with `L` commutes with direct sums on `D_QCoh(𝒪_Z)`**: on `D(𝒪_Z)` it is left
adjoint to `R𝓗om(L, -)`, and `D_QCoh(𝒪_Z)` is closed under direct sums in `D(𝒪_Z)`. -/
instance preservesColimitsOfShape_quasiCoherentDerivedTensorRight (Z : Scheme.{u})
    (L : quasiCoherentDerivedCategory Z) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (quasiCoherentDerivedTensorRight Z L) := by
  have := DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts Z J
  let ι := ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf))
  have : PreservesColimitsOfShape (Discrete J) ι := inferInstance
  have : PreservesColimitsOfShape (Discrete J) (InternalHom.derivedTensorRight L.obj) :=
    (InternalHom.derivedTensorSheafHomAdjunction L.obj).leftAdjoint_preservesColimits.1
  let e : ι ⋙ InternalHom.derivedTensorRight L.obj ≅ quasiCoherentDerivedTensorRight Z L ⋙ ι :=
    Functor.isoWhiskerLeft ι (ProjectionFormulaLocallySmall.derivedTensorRightIso Z L.obj).symm ≪≫
      NatIso.ofComponents (fun _ => Iso.refl _) (fun φ => by
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ ((derivedTensor Z).map φ.hom).app L.obj ≫
          ((derivedTensor Z).obj _).map (𝟙 L.obj)
        rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id, Category.id_comp]
        rfl)
  have : PreservesColimitsOfShape (Discrete J) (quasiCoherentDerivedTensorRight Z L ⋙ ι) :=
    preservesColimitsOfShape_of_natIso e
  exact preservesColimitsOfShape_of_reflects_of_preserves _ ι

/-- **Derived pullback commutes with direct sums on `D_QCoh`**: on `D(𝒪)` it is left adjoint to
`Rf_*`, and `D_QCoh` is closed under direct sums in `D(𝒪)` on both sides. -/
instance preservesColimitsOfShape_quasiCoherentDerivedPullback (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (quasiCoherentDerivedPullback' f) := by
  have := DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts X J
  have := DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts Y J
  let ιX := ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf))
  let ιY := ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf))
  have : PreservesColimitsOfShape (Discrete J) ιY := inferInstance
  have : PreservesColimitsOfShape (Discrete J) (derivedPullback f) :=
    (derivedAdjunction f).leftAdjoint_preservesColimits.1
  have : PreservesColimitsOfShape (Discrete J) (quasiCoherentDerivedPullback' f ⋙ ιX) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete J) (ιY ⋙ derivedPullback f))
  exact preservesColimitsOfShape_of_reflects_of_preserves _ ιX

section Comparison

variable [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush α E K)]
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

/-! ### The dévissage -/

section Devissage

variable (L : quasiCoherentDerivedCategory Y)
  [(quasiCoherentDerivedPullbackTensorRight f (a.obj L)).CommShift ℤ]
  [(quasiCoherentDerivedTensorRight Y L ⋙ a).CommShift ℤ]
  [(quasiCoherentDerivedPullbackTensorRight f (a.obj L)).IsTriangulated]
  [(quasiCoherentDerivedTensorRight Y L ⋙ a).IsTriangulated]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J)
    (quasiCoherentDerivedPullbackTensorRight f (a.obj L))]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J)
    (quasiCoherentDerivedTensorRight Y L ⋙ a)]
  [NatTrans.CommShift (compareWithPullbackTensorNatTrans f hpush α adj L) ℤ]

end Devissage

section DevissageDual

variable (L : quasiCoherentDerivedCategory Y)
  [(quasiCoherentDerivedPullbackTensorRight f (a.obj L)).CommShift ℤ]
  [(quasiCoherentDerivedTensorRight Y L ⋙ a).CommShift ℤ]
  [(quasiCoherentDerivedPullbackTensorRight f (a.obj L)).IsTriangulated]
  [(quasiCoherentDerivedTensorRight Y L ⋙ a).IsTriangulated]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J)
    (quasiCoherentDerivedPullbackTensorRight f (a.obj L))]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J)
    (quasiCoherentDerivedTensorRight Y L ⋙ a)]

/-- **The dévissage from the shifts of a compact generating family, with no compatibility with
the shift.** If the two sides of the comparison map are exact and commute with direct sums as
functors of `K`, and the comparison map is invertible at every shift of every member of a
compact generating family, then it is invertible at every `K`. -/
theorem isIso_compareWithPullbackTensor_of_forall_shift {ι : Type u}
    (E : ι → quasiCoherentDerivedCategory Y) (hEc : ∀ i, IsCompactObject.{u} (E i))
    (hE : ∀ Z : quasiCoherentDerivedCategory Y,
      ((ofObj E).shiftClosure ℤ).rightOrthogonal Z → IsZero Z)
    (hτ : ∀ (i : ι) (n : ℤ), IsIso (compareWithPullbackTensor f hpush α adj ((E i)⟦n⟧) L))
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullbackTensor f hpush α adj K L) := by
  have := hasCoproducts_quasiCoherentDerivedCategory Y
  exact StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated_of_forall_shift
    (compareWithPullbackTensorNatTrans f hpush α adj L) E hEc hE hτ K

/-- **The dévissage with dualizable generators and no compatibility with the shift.** If the
two sides of the comparison map are exact and commute with direct sums as functors of `K`, if
`α` is the oplax structure of the strong monoidal functor `Lf^*`, and if `D_QCoh(𝒪_Y)` is
compactly generated by a family `E` all of whose shifts are dualizable, then the comparison map
is invertible at every `K`. -/
theorem isIso_compareWithPullbackTensor_of_isCompactlyGenerated
    [(quasiCoherentDerivedPullback' f).Monoidal]
    (hα : ∀ P Q : quasiCoherentDerivedCategory Y, α.app (P, Q) =
      (quasiCoherentDerivedPullback' f).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P) ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) Q P ≫
        ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
          ((quasiCoherentDerivedPullback' f).obj Q)).app
          ((quasiCoherentDerivedPullback' f).obj P)) {ι : Type u}
    (E : ι → quasiCoherentDerivedCategory Y) (hEc : ∀ i, IsCompactObject.{u} (E i))
    (hE : ∀ Z : quasiCoherentDerivedCategory Y,
      ((ofObj E).shiftClosure ℤ).rightOrthogonal Z → IsZero Z)
    (hdual : ∀ (i : ι) (n : ℤ), Nonempty (HasRightDual ((E i)⟦n⟧)))
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullbackTensor f hpush α adj K L) := by
  have := hasCoproducts_quasiCoherentDerivedCategory Y
  exact StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated_of_forall_shift
    (compareWithPullbackTensorNatTrans f hpush α adj L) E hEc hE
    (fun i n => by
      obtain ⟨h⟩ := hdual i n
      exact isIso_compareWithPullbackTensor_of_exactPairing f hpush α hα adj _
        ((E i)⟦n⟧)ᘁ L) K

/-- `D_QCoh(𝒪_Y)` over a quasi-compact quasi-separated base has a compact generating family all
of whose shifts are dualizable. -/
private theorem exists_compactGenerating_family_hasRightDual (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] :
    ∃ (ι : Type u) (E : ι → quasiCoherentDerivedCategory Y), (∀ i, IsCompactObject.{u} (E i)) ∧
      (∀ Z : quasiCoherentDerivedCategory Y,
        ((ofObj E).shiftClosure ℤ).rightOrthogonal Z → IsZero Z) ∧
      ∀ (i : ι) (n : ℤ), Nonempty (HasRightDual ((E i)⟦n⟧)) := by
  obtain ⟨ι, E, hEc, hE⟩ := QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory Y
  have : ObjectProperty.IsTriangulated (IsCompactObject.{u, _, _}
      (C := quasiCoherentDerivedCategory Y)) :=
    (isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := quasiCoherentDerivedCategory Y)).2.1
  exact ⟨ι, E, hEc, hE, fun i n => nonempty_hasRightDual_subcategory_of_isCompactObject _
    (ObjectProperty.le_shift (IsCompactObject.{u, _, _}
      (C := quasiCoherentDerivedCategory Y)) n _ (hEc i))⟩

/-- **The dévissage over a quasi-compact quasi-separated base.** As
`isIso_compareWithPullbackTensor_of_isCompactlyGenerated`, with the generating family the one of
[Stacks, Tag 09IS], whose members and their shifts are compact, hence perfect and dualizable
(`Stacks.Duality.nonempty_hasRightDual_subcategory_of_isCompactObject`). -/
theorem isIso_compareWithPullbackTensor_of_forall_isCompactObject [CompactSpace Y]
    [QuasiSeparatedSpace Y] [(quasiCoherentDerivedPullback' f).Monoidal]
    (hα : ∀ P Q : quasiCoherentDerivedCategory Y, α.app (P, Q) =
      (quasiCoherentDerivedPullback' f).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P) ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) Q P ≫
        ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
          ((quasiCoherentDerivedPullback' f).obj Q)).app
          ((quasiCoherentDerivedPullback' f).obj P))
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullbackTensor f hpush α adj K L) := by
  obtain ⟨ι, E, hEc, hE, hdual⟩ := exists_compactGenerating_family_hasRightDual Y
  exact isIso_compareWithPullbackTensor_of_isCompactlyGenerated f hpush α adj L hα E hEc hE
    hdual K

end DevissageDual

/-! ### The map displayed in Equation 48.8.0.1 -/

section StructureSheaf

variable (ρ : (quasiCoherentDerivedTensor Y).flip.obj (derivedStructureSheaf Y) ≅ 𝟭 _)
  [(quasiCoherentDerivedPullbackTensorRight f
    (a.obj (derivedStructureSheaf Y))).CommShift ℤ]
  [(quasiCoherentDerivedTensorRight Y (derivedStructureSheaf Y) ⋙ a).CommShift ℤ]
  [(quasiCoherentDerivedPullbackTensorRight f
    (a.obj (derivedStructureSheaf Y))).IsTriangulated]
  [(quasiCoherentDerivedTensorRight Y (derivedStructureSheaf Y) ⋙ a).IsTriangulated]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J)
    (quasiCoherentDerivedPullbackTensorRight f (a.obj (derivedStructureSheaf Y)))]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J)
    (quasiCoherentDerivedTensorRight Y (derivedStructureSheaf Y) ⋙ a)]
  [NatTrans.CommShift
    (compareWithPullbackTensorNatTrans f hpush α adj (derivedStructureSheaf Y)) ℤ]

end StructureSheaf

end Comparison

/-! ### The displayed map for a perfect proper morphism of Noetherian schemes -/

section PerfectProper

variable [IsNoetherian X] [IsNoetherian Y] [Perfect f] [IsProper f]
  [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush α E K)]
  (ρ : (quasiCoherentDerivedTensor Y).flip.obj (derivedStructureSheaf Y) ≅ 𝟭 _)

/-- The right-hand side `K ↦ f^×(K ⊗ᴸ 𝒪_Y)` of the comparison map at `L = 𝒪_Y` is the twisted
inverse image, through the right unitor. -/
def twistedInverseImageTensorRightIso :
    quasiCoherentDerivedTensorRight Y (derivedStructureSheaf Y) ⋙ twistedInverseImage f hpush ≅
      twistedInverseImage f hpush :=
  Functor.isoWhiskerRight ρ _ ≪≫ Functor.leftUnitor _

/-- **Equation 48.8.0.1 for the twisted inverse image of a perfect proper morphism of
Noetherian schemes, from a compact generating family with dualizable shifts**: if `α` is the
oplax structure of the strong monoidal functor `Lf^*`, if the left-hand side
`K ↦ Lf^*K ⊗ᴸ f^×𝒪_Y` is exact, and if `D_QCoh(𝒪_Y)` is generated by a family `E` of compact
objects all of whose shifts are dualizable, then the map `Lf^*K ⊗ᴸ f^×𝒪_Y ⟶ f^×K` is an
isomorphism for every `K`. -/
theorem isIso_twistedInverseImageCompareWithPullback_of_isCompactlyGenerated
    [(quasiCoherentDerivedPullback' f).Monoidal]
    (hα : ∀ P Q : quasiCoherentDerivedCategory Y, α.app (P, Q) =
      (quasiCoherentDerivedPullback' f).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P) ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) Q P ≫
        ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
          ((quasiCoherentDerivedPullback' f).obj Q)).app
          ((quasiCoherentDerivedPullback' f).obj P))
    {ι : Type u} (E : ι → quasiCoherentDerivedCategory Y) (hEc : ∀ i, IsCompactObject.{u} (E i))
    (hE : ∀ Z : quasiCoherentDerivedCategory Y,
      ((ofObj E).shiftClosure ℤ).rightOrthogonal Z → IsZero Z)
    (hdual : ∀ (i : ι) (n : ℤ), Nonempty (HasRightDual ((E i)⟦n⟧)))
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (twistedInverseImageCompareWithPullback f hpush α ρ K) := by
  let adj := twistedInverseImageAdjunction f hpush
  let := adj.rightAdjointCommShift ℤ
  let := adj.commShift_of_leftAdjoint ℤ
  have : (twistedInverseImage f hpush).IsTriangulated := adj.isTriangulated_rightAdjoint
  have hsum : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) (twistedInverseImage f hpush) :=
    preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_hpush f hpush adj
  let e := (twistedInverseImageTensorRightIso f hpush ρ).symm
  let := Functor.CommShift.ofIso e ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have : (quasiCoherentDerivedTensorRight Y (derivedStructureSheaf Y) ⋙
      twistedInverseImage f hpush).IsTriangulated := Functor.isTriangulated_of_iso e
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (quasiCoherentDerivedTensorRight Y (derivedStructureSheaf Y) ⋙
        twistedInverseImage f hpush) := fun J =>
    have := hsum J
    preservesColimitsOfShape_of_natIso e
  have h₁ : IsIso (compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y)) :=
    isIso_compareWithPullbackTensor_of_isCompactlyGenerated f hpush α adj
      (derivedStructureSheaf Y) hα E hEc hE hdual K
  have h₂ : IsIso ((twistedInverseImage f hpush).map (ρ.hom.app K)) := inferInstance
  show IsIso (compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
    (twistedInverseImage f hpush).map (ρ.hom.app K))
  infer_instance

/-- **Equation 48.8.0.1 for the twisted inverse image of a perfect proper morphism of
Noetherian schemes**, from the structures it is built from: if `α` is the oplax structure of the
strong monoidal functor `Lf^*`, if the left-hand side `K ↦ Lf^*K ⊗ᴸ f^×𝒪_Y` is exact (it
commutes with direct sums by `preservesColimitsOfShape_quasiCoherentDerivedTensorRight`), then the
map `Lf^*K ⊗ᴸ f^×𝒪_Y ⟶ f^×K` is an isomorphism for every `K`. -/
theorem isIso_twistedInverseImageCompareWithPullback_of_forall_isCompactObject
    [(quasiCoherentDerivedPullback' f).Monoidal]
    (hα : ∀ P Q : quasiCoherentDerivedCategory Y, α.app (P, Q) =
      (quasiCoherentDerivedPullback' f).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P) ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) Q P ≫
        ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
          ((quasiCoherentDerivedPullback' f).obj Q)).app
          ((quasiCoherentDerivedPullback' f).obj P))
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (twistedInverseImageCompareWithPullback f hpush α ρ K) := by
  obtain ⟨ι, E, hEc, hE, hdual⟩ := exists_compactGenerating_family_hasRightDual Y
  exact isIso_twistedInverseImageCompareWithPullback_of_isCompactlyGenerated f hpush α ρ hα
    E hEc hE hdual K

end PerfectProper

end Stacks.Duality

end
