module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Independence

/-!
# Restricting a compactification to opens of the source and the target

Let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S` with a compactification
`X ⟶ X̄ ⟶ Y`, and let `j : U ⟶ X`, `i : V ⟶ Y` be open immersions with `j ≫ f = g ≫ i`. Then
`U ⟶ X̄ ×_Y V ⟶ V` is a compactification of `g : U ⟶ V`, and
`(f^!E)|_U ≅ g^!(E|_V)` computed there, wherever the map of [Stacks, Tag 0A9L] for the cartesian
square `X̄ ×_Y V ⟶ X̄` over `V ⟶ Y` is invertible at `E`. This is the first half of
[Stacks, Tag 0BV2]; the second is the independence of the compactification.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.restrictOpenPullback`: the compactification
  `U ⟶ X̄ ×_Y V ⟶ V` of `g`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {S : Scheme.{u}} {U X V Y : FTS S} (f : X ⟶ Y) (g : U ⟶ V) (j : U ⟶ X) (i : V ⟶ Y)
  [IsOpenImmersion j.left] [IsOpenImmersion i.left] (w : j ≫ f = g ≫ i)
  (c : CompactificationOf (Over.mk f.left))

omit [IsOpenImmersion j.left] [IsOpenImmersion i.left] in
include w in
/-- The composite `U ⟶ X ⟶ X̄ ⟶ Y` is equal to the composite `U ⟶ V ⟶ Y`. -/
theorem restrictOpen_condition :
    (j.left ≫ c.immersion) ≫ c.toBase = g.left ≫ i.left := by
  rw [Category.assoc, Stacks.Duality.immersion_comp_toBase]
  have := congrArg (fun φ => φ.left) w
  simpa using this

/-- The open immersion `U ⟶ X̄ ×_Y V`. -/
abbrev restrictOpenImmersion : U.left ⟶ pullback c.toBase i.left :=
  pullback.lift (j.left ≫ c.immersion) g.left (restrictOpen_condition f g j i w c)

/-- The morphism `U ⟶ X̄ ×_Y V` is an open immersion. -/
instance : IsOpenImmersion (restrictOpenImmersion f g j i w c) := by
  have : IsOpenImmersion (restrictOpenImmersion f g j i w c ≫ pullback.fst c.toBase i.left) := by
    rw [pullback.lift_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst c.toBase i.left)

/-- **The compactification of `g : U ⟶ V` obtained from one of `f` by restriction to opens**:
`U ⟶ X ⟶ X̄` factors through `X̄ ×_Y V` as an open immersion, and `X̄ ×_Y V ⟶ V` is proper as a
base change of `X̄ ⟶ Y`. -/
def restrictOpenPullback (c : CompactificationOf (Over.mk f.left)) :
    CompactificationOf (Over.mk g.left) :=
  ⟨StructuredArrow.mk (Y := Over.mk (pullback.snd c.toBase i.left))
      (Over.homMk (restrictOpenImmersion f g j i w c) (pullback.lift_snd _ _ _)),
    ⟨(inferInstance : IsOpenImmersion (restrictOpenImmersion f g j i w c)),
      (inferInstance : IsProper (pullback.snd c.toBase i.left))⟩⟩

/-- The space of the restricted compactification is `X̄ ×_Y V`. -/
@[simp]
theorem restrictOpenPullback_space :
    (c.restrictOpenPullback f g j i w).space = pullback c.toBase i.left :=
  rfl

/-- The immersion of the restricted compactification is `U ⟶ X̄ ×_Y V`. -/
@[simp]
theorem restrictOpenPullback_immersion :
    (c.restrictOpenPullback f g j i w).immersion = restrictOpenImmersion f g j i w c :=
  rfl

/-- The proper map of the restricted compactification is the projection `X̄ ×_Y V ⟶ V`. -/
@[simp]
theorem restrictOpenPullback_toBase :
    (c.restrictOpenPullback f g j i w).toBase = pullback.snd c.toBase i.left :=
  rfl

end AlgebraicGeometry.CompactificationOf

namespace Stacks.Duality

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  {U X V Y : FTS S} (f : X ⟶ Y) (g : U ⟶ V) (j : U ⟶ X) (i : V ⟶ Y)
  [IsOpenImmersion j.left] [IsOpenImmersion i.left] (w : j ≫ f = g ≫ i)
  (c : CompactificationOf (Over.mk f.left))

/-- The fibre product `X̄ ×_Y V` is quasi-compact. -/
instance : CompactSpace (pullback c.toBase i.left : Scheme.{u}) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd c.toBase i.left)

/-- The fibre product `X̄ ×_Y V` is quasi-separated. -/
instance : QuasiSeparatedSpace (pullback c.toBase i.left : Scheme.{u}) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd c.toBase i.left)

/-- The map of [Stacks, Tag 0A9L] for the cartesian square `X̄ ×_Y V ⟶ X̄` over `V ⟶ Y`. -/
abbrev restrictOpenRestrictionMap :=
  OpenImmersion.twistedInverseImageRestrictionMap (pullback.fst c.toBase i.left)
    (pullback.snd c.toBase i.left) c.toBase i.left
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict _)
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict _) (IsPullback.of_hasPullback _ _)

/-- **`(f^!E)|_U ≅ g^!(E|_V)` at the restricted compactification**, wherever the map of
[Stacks, Tag 0A9L] for the square `X̄ ×_Y V ⟶ X̄` over `V ⟶ Y` is invertible at `E`. -/
def upperShriekRestrictOpenObjIsoOfIsIso (E : quasiCoherentDerivedCategory Y.left)
    [IsIso ((restrictOpenRestrictionMap (f := f) (i := i) (c := c)).app E)] :
    (quasiCoherentDerivedPullback' j.left).obj ((upperShriek f c).obj E) ≅
      (upperShriek g (c.restrictOpenPullback f g j i w)).obj
        ((quasiCoherentDerivedPullback' i.left).obj E) :=
  let a := twistedInverseImage c.toBase
    (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)
  let a' := twistedInverseImage (pullback.snd c.toBase i.left)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.snd c.toBase i.left))
  let ι := CompactificationOf.restrictOpenImmersion f g j i w c
  let p₁ := pullback.fst c.toBase i.left
  let e₁ : (quasiCoherentDerivedPullback' p₁).obj (a.obj E) ≅
      (OpenImmersion.restrictedDerivedRestrict p₁).obj (a.obj E) :=
    ((restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback p₁).app _).symm
  let e₂ : (OpenImmersion.restrictedDerivedRestrict p₁).obj (a.obj E) ≅
      a'.obj ((OpenImmersion.restrictedDerivedRestrict i.left).obj E) :=
    asIso ((restrictOpenRestrictionMap (f := f) (i := i) (c := c)).app E)
  let e₃ : a'.obj ((OpenImmersion.restrictedDerivedRestrict i.left).obj E) ≅
      a'.obj ((quasiCoherentDerivedPullback' i.left).obj E) :=
    a'.mapIso ((restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback i.left).app E)
  have hι : j.left ≫ c.immersion = ι ≫ p₁ := (pullback.lift_fst _ _ _).symm
  (quasiCoherentDerivedPullbackCompIso j.left c.immersion).app (a.obj E) ≪≫
    eqToIso (congrArg (fun φ => (quasiCoherentDerivedPullback' φ).obj (a.obj E)) hι) ≪≫
    ((quasiCoherentDerivedPullbackCompIso ι p₁).app (a.obj E)).symm ≪≫
    (quasiCoherentDerivedPullback' ι).mapIso (e₁ ≪≫ e₂ ≪≫ e₃)

end Stacks.Duality
