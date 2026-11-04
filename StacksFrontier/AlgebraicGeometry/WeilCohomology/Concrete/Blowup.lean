module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Projective
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreExceptionalSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.NoetherianFlatStratification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Blowing up a smooth projective scheme in a smooth centre

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over a field `k`. The blowing
up `b : X' = Bl_Z X ⟶ X` of `X` in `Z` (in the ideal sheaf of `i`) is smooth over `k` (More on
Morphisms, Tag 0FUT) and projective (Tag 02NS, the ideal being of finite type on the Noetherian
scheme `X`), so it is a morphism of smooth projective schemes over `k`. This is the morphism
of axiom (A7) of Section 45.14 (Tag 0FID) and of Lemma 0FIH.

The exceptional divisor `E = X' ×_X Z` is a smooth projective scheme over `k` too: `π : E ⟶ Z`
is smooth (the closed immersion `i` of smooth `k`-schemes is a regular immersion, Tag 067U, and
Tag 0FVA's computation of `E`), and `E` is a closed subscheme of the projective `X'`.

The blowup is the one of `StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData`, in the ideal sheaf
`i.ker`, and `E` is the fibre product with `i` itself: this is the form in which the blow up
formula of Tag 0FVA (`Stacks.Chow.completedBivariantRestriction_lciGysinMap_blowUpToBase`) is
stated. Smoothness and projectivity are transported from the blowup of
`StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp` along `AlgebraicGeometry.blowUpIso`.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.blowupObj`: `X' = Bl_Z X`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.blowupHom`: `b : X' ⟶ X`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.exceptionalObj`, `exceptionalHom`,
  `exceptionalProj`: `E`, `j : E ⟶ X'` and `π : E ⟶ Z`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The underlying scheme of a smooth projective scheme over a field `k` is locally Noetherian. -/
instance isLocallyNoetherian (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsLocallyNoetherian X.obj.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.obj.hom

variable {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left]

/-- A closed immersion of smooth projective schemes over `k` is a regular immersion (Tag 067U). -/
@[sga "6 VII 1.10" "special case", sga "6 VIII 2.4" "special case", sga "6 VIII 3.1" "special case"]
theorem isRegularImmersion_of_isClosedImmersion :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i.hom.left := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  exact Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth i.hom.left X.obj.hom

/-- **The blowing up `X' = Bl_Z X`** of a smooth projective scheme over `k` in a closed subscheme
`Z` smooth over `k`, as a smooth projective scheme over `k`: smooth by Tag 0FUT, projective by
Tag 02NS (the ideal sheaf is of finite type, `X` being Noetherian) and composition. -/
@[sga "7 II 2.1" "partial",
  sga "7 XVIII 2.1" "special case",
  sga "7 XVIII 2.2" "special case",
  sga "7 XVIII 3.1" "more general"]
def blowupObj : (SmoothProjectiveScheme k).FullSubcategory :=
  ⟨Over.mk (Stacks.Blowup.blowUpToBase i.hom.left.ker ≫ X.obj.hom),
    by
      have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
      have h := Stacks.AlgebraicGeometry.smooth_blowUpToBase_comp X.obj.hom i.hom.left
      rw [← AlgebraicGeometry.blowUpIso_hom_blowUpToBase, Category.assoc] at h
      have : Smooth ((AlgebraicGeometry.blowUpIso i.hom.left.ker).inv ≫
        (AlgebraicGeometry.blowUpIso i.hom.left.ker).hom ≫
          Stacks.Blowup.blowUpToBase i.hom.left.ker ≫ X.obj.hom) := inferInstance
      simpa using this,
    by
      have h := isProjective_blowUpToBase i.hom.left.ker
        (Scheme.IdealSheafData.isFiniteType_of_isLocallyNoetherian _)
      rw [← AlgebraicGeometry.blowUpIso_hom_blowUpToBase] at h
      have h' : IsProjective (Stacks.Blowup.blowUpToBase i.hom.left.ker) := by
        simpa using IsProjective.comp_iso (AlgebraicGeometry.blowUpIso i.hom.left.ker).symm h
      exact IsProjective.comp h' X.property.2⟩

/-- The underlying scheme of `blowupObj i` is the blowup of `X` in the ideal sheaf of `i`. -/
@[simp]
theorem blowupObj_left : (blowupObj i).obj.left = Stacks.Blowup.blowUp i.hom.left.ker := rfl

/-- **The blowing up morphism `b : X' ⟶ X`.** -/
@[sga "7 XVIII 2.1" "special case"]
def blowupHom : blowupObj i ⟶ X :=
  ObjectProperty.homMk (Over.homMk (Stacks.Blowup.blowUpToBase i.hom.left.ker) rfl)

/-- The underlying morphism of `blowupHom i` is the blowup morphism `Bl_Z X ⟶ X`. -/
@[simp]
theorem blowupHom_hom_left : (blowupHom i).hom.left = Stacks.Blowup.blowUpToBase i.hom.left.ker :=
  rfl

/-- The projection `π : E = X' ×_X Z ⟶ Z` of the exceptional divisor is smooth (Tag 0FVA's
description of `E`, the centre being regularly immersed). -/
instance smooth_exceptionalProj :
    Smooth (pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) :=
  Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i.hom.left
    (isRegularImmersion_of_isClosedImmersion i)

/-- **The exceptional divisor `E = X' ×_X Z`** as a smooth projective scheme over `k`: smooth over
`Z` (`smooth_exceptionalProj`), hence over `k`, and a closed subscheme of the projective `X'`. -/
def exceptionalObj : (SmoothProjectiveScheme k).FullSubcategory :=
  ⟨Over.mk (pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left ≫ Z.obj.hom),
    (inferInstance : Smooth (pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left ≫
      Z.obj.hom)),
    by
      rw [← Over.w i.hom, ← Category.assoc, ← pullback.condition, Category.assoc]
      exact Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion _ _
        inferInstance (blowupObj i).property.2⟩

/-- The underlying scheme of `exceptionalObj i` is the fibre product `X' ×_X Z`. -/
@[simp]
theorem exceptionalObj_left :
    (exceptionalObj i).obj.left =
      Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left :=
  rfl

/-- The inclusion `j : E ⟶ X'` of the exceptional divisor. -/
@[sga "7 XVIII 4.1" "the arrow i"]
def exceptionalHom : exceptionalObj i ⟶ blowupObj i :=
  ObjectProperty.homMk (Over.homMk (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker)
    i.hom.left) (by
      simp only [blowupObj, exceptionalObj, Over.mk_hom]
      rw [pullback.condition_assoc, Over.w i.hom]))

/-- The projection `π : E ⟶ Z` of the exceptional divisor onto the centre. -/
def exceptionalProj : exceptionalObj i ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker)
    i.hom.left) rfl)

/-- The underlying morphism of `exceptionalHom i` is the first projection `X' ×_X Z ⟶ X'`. -/
@[simp]
theorem exceptionalHom_hom_left :
    (exceptionalHom i).hom.left =
      pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left :=
  rfl

/-- The underlying morphism of `exceptionalProj i` is the second projection `X' ×_X Z ⟶ Z`. -/
@[simp]
theorem exceptionalProj_hom_left :
    (exceptionalProj i).hom.left =
      pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left :=
  rfl

/-- The exceptional square `j ≫ b = π ≫ i` commutes. -/
@[reassoc]
theorem exceptionalHom_comp_blowupHom :
    exceptionalHom i ≫ blowupHom i = exceptionalProj i ≫ i :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext pullback.condition)

/-- The exceptional square is cartesian on underlying schemes. -/
theorem isPullback_exceptional :
    IsPullback (exceptionalHom i).hom.left (exceptionalProj i).hom.left
      (blowupHom i).hom.left i.hom.left :=
  IsPullback.of_hasPullback _ _

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
