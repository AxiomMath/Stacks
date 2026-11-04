module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsDoNotSeparatePoints
public import StacksFrontier.RingTheory.TwistedSquareZeroSystem

/-!
# The two systems of affine schemes behind the sharpness of representability

The counterexample of Stacks 0CBE — the second sense of the warning of Stacks 0AN7 — is a
representable morphism of affine formal algebraic spaces whose target is McQuillan and whose
source is not. Both spaces are directed colimits of affine schemes, and this file builds those
two systems of schemes, over the common base

`baseScheme I = Spec (Lam I)`,

out of the two systems of rings of `StacksFrontier.RingTheory.TwistedSquareZeroSystem`: the target's
stages are the spectra of the stage rings and the source's are the spectra of the dual numbers
over them. Both diagrams are covariant in the index, the ring maps running the other way, and
both have thickenings for transition morphisms because both systems of rings have square-zero
kernels.

The structure morphisms over the base are induced by `lamProj` on the target side and by
`lamProj` followed by `TrivSqZeroExt.inl` on the source side. Taking `Spec (Lam I)` rather than
`Spec ℚ` as the base is what makes their compatibility with the transitions a *computation* —
`stageRingMap_comp_lamProj` and `dualMap_inl` — rather than a statement about the uniqueness of a
`ℚ`-algebra structure.

## Main definitions

* `Stacks.Coherent.baseScheme`: the base, the spectrum of the fixed presenting ring.
* `Stacks.Coherent.targetSchemeDiagram` and `Stacks.Coherent.sourceSchemeDiagram`: the two
  directed systems of affine schemes.
* `Stacks.Coherent.targetStructureMap` and `Stacks.Coherent.sourceStructureMap`: their structure
  morphisms over the base.

## Main results

* `Stacks.Coherent.targetSchemeDiagram_isThickening` and
  `Stacks.Coherent.sourceSchemeDiagram_isThickening`: every transition morphism of either system
  is a thickening.
* `Stacks.Coherent.targetStructureMap_naturality` and
  `Stacks.Coherent.sourceStructureMap_naturality`: the structure morphisms are compatible with
  the transitions.

## Implementation notes

A transition is a thickening by `AlgebraicGeometry.FormalSpace.specMap_isThickening_of_sqZero'`,
whose kernel hypothesis is stated on elements; that is exactly the shape
`Stacks.Coherent.mul_eq_zero_of_stageRingMap_eq_zero` and
`Stacks.Coherent.mul_eq_zero_of_dualMap_eq_zero` have, so neither nilpotency of an ideal nor any
translation between the two formulations is needed.

Functoriality of both diagrams is the corresponding `_comp` lemma of the system of rings read
through the contravariance of `Spec`, and the identity law is the corresponding `_refl` lemma;
the proofs of the latter use proof irrelevance to replace `leOfHom (𝟙 b)` by `le_refl b`, since
the transition maps take the inequality as an argument.
-/

@[expose] public noncomputable section

namespace Stacks.Coherent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

/-! ### The base -/

/-- The base scheme: the spectrum of the fixed ring which surjects onto every stage. -/
abbrev baseScheme (I : Type u) [LinearOrder I] [WellFoundedLT I] : Scheme.{u} :=
  Spec (CommRingCat.of (Lam I))

/-- The spectra of two composable ring maps compose to the spectrum of a ring map `h` which agrees
with their composite pointwise. -/
private theorem spec_map_ofHom_comp_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (H : ∀ x, g (f x) = h x) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
      = Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (Spec.map ∘ CommRingCat.ofHom) (RingHom.ext H)

/-! ### The target's system of affine schemes -/

/-- The target's directed system of affine schemes: the spectra of the stage rings, covariant in
the index because the ring maps run the other way. -/
def targetSchemeDiagram (I : Type u) [LinearOrder I] [WellFoundedLT I] : I ⥤ Scheme.{u} where
  obj b := Spec (CommRingCat.of (StageRing b))
  map {b a} f := Spec.map (CommRingCat.ofHom (stageRingMap (leOfHom f)))
  map_id b := by
    rw [show stageRingMap (leOfHom (CategoryStruct.id b)) = RingHom.id (StageRing b) from
      RingHom.ext fun x ↦ stageRingMap_refl x, CommRingCat.ofHom_id, Spec.map_id]
  map_comp {b a c} f g := by
    rw [show stageRingMap (leOfHom (f ≫ g))
        = (stageRingMap (leOfHom f)).comp (stageRingMap (leOfHom g)) from
      RingHom.ext fun x ↦ (stageRingMap_comp (leOfHom g) (leOfHom f) x).symm,
      CommRingCat.ofHom_comp, Spec.map_comp]

/-- The target system at `b` is the spectrum of the stage ring `StageRing b`. -/
@[simp]
theorem targetSchemeDiagram_obj (b : I) :
    (targetSchemeDiagram I).obj b = Spec (CommRingCat.of (StageRing b)) := rfl

/-- The transition of the target system along `b ⟶ a` is the spectrum of the stage ring map
`stageRingMap`. -/
@[simp]
theorem targetSchemeDiagram_map {b a : I} (f : b ⟶ a) :
    (targetSchemeDiagram I).map f = Spec.map (CommRingCat.ofHom (stageRingMap (leOfHom f))) :=
  rfl

/-- **Every transition of the target system is a thickening**: the transition ring maps are
surjective with square-zero kernels. -/
theorem targetSchemeDiagram_isThickening {b a : I} (f : b ⟶ a) :
    Stacks.Thickenings.IsThickening ((targetSchemeDiagram I).map f) :=
  FormalSpace.specMap_isThickening_of_sqZero' _ (stageRingMap_surjective (leOfHom f))
    fun x y hx hy ↦ mul_eq_zero_of_stageRingMap_eq_zero (leOfHom f) x y hx hy

/-- The structure morphism of a target stage over the base, induced by the surjection of the
fixed presenting ring onto that stage. -/
def targetStructureMap (b : I) : (targetSchemeDiagram I).obj b ⟶ baseScheme I :=
  Spec.map (CommRingCat.ofHom (lamProj b))

/-- The structure morphisms of the target stages are compatible with the transitions. -/
theorem targetStructureMap_naturality {b a : I} (f : b ⟶ a) :
    (targetSchemeDiagram I).map f ≫ targetStructureMap a = targetStructureMap b := by
  exact spec_map_ofHom_comp_eq _ _ _ fun x ↦ stageRingMap_comp_lamProj (leOfHom f) x

/-! ### The source's system of affine schemes -/

/-- The source's directed system of affine schemes: the spectra of the dual numbers over the
stage rings, with the twisted transition maps. -/
def sourceSchemeDiagram (hcnt : ∀ a : I, (Set.Iio a).Countable) : I ⥤ Scheme.{u} where
  obj b := Spec (CommRingCat.of (DualStage b))
  map {b a} f := Spec.map (CommRingCat.ofHom (dualMap hcnt (leOfHom f)))
  map_id b := by
    rw [show dualMap hcnt (leOfHom (CategoryStruct.id b)) = RingHom.id (DualStage b) from
      RingHom.ext fun x ↦ dualMap_refl hcnt x, CommRingCat.ofHom_id, Spec.map_id]
  map_comp {b a c} f g := by
    rw [show dualMap hcnt (leOfHom (f ≫ g))
        = (dualMap hcnt (leOfHom f)).comp (dualMap hcnt (leOfHom g)) from
      RingHom.ext fun x ↦ (dualMap_comp hcnt (leOfHom g) (leOfHom f) x).symm,
      CommRingCat.ofHom_comp, Spec.map_comp]

/-- The source system at `b` is the spectrum of the dual numbers `DualStage b`. -/
@[simp]
theorem sourceSchemeDiagram_obj (hcnt : ∀ a : I, (Set.Iio a).Countable) (b : I) :
    (sourceSchemeDiagram hcnt).obj b = Spec (CommRingCat.of (DualStage b)) := rfl

/-- The transition of the source system along `b ⟶ a` is the spectrum of the twisted transition
ring map `dualMap hcnt`. -/
@[simp]
theorem sourceSchemeDiagram_map (hcnt : ∀ a : I, (Set.Iio a).Countable) {b a : I} (f : b ⟶ a) :
    (sourceSchemeDiagram hcnt).map f
      = Spec.map (CommRingCat.ofHom (dualMap hcnt (leOfHom f))) := rfl

/-- **Every transition of the source system is a thickening**: the twisted transition ring maps
are surjective with square-zero kernels, exactly as the untwisted ones are. -/
theorem sourceSchemeDiagram_isThickening (hcnt : ∀ a : I, (Set.Iio a).Countable) {b a : I}
    (f : b ⟶ a) :
    Stacks.Thickenings.IsThickening ((sourceSchemeDiagram hcnt).map f) :=
  FormalSpace.specMap_isThickening_of_sqZero' _ (dualMap_surjective hcnt (leOfHom f))
    fun x y hx hy ↦ mul_eq_zero_of_dualMap_eq_zero hcnt (leOfHom f) x y hx hy

/-- The ring map putting a target stage ring inside the corresponding source stage ring as the
ring component of the dual numbers. -/
def dualLamProj (b : I) : Lam I →+* DualStage b :=
  (TrivSqZeroExt.inlHom (StageRing b) (StageRing b)).comp (lamProj b)

/-- `dualLamProj b` sends `x` to the dual number with ring component `lamProj b x` and zero
square-zero component. -/
@[simp]
theorem dualLamProj_apply (b : I) (x : Lam I) :
    dualLamProj b x = TrivSqZeroExt.inl (lamProj b x) := rfl

/-- The structure morphism of a source stage over the base. -/
def sourceStructureMap (hcnt : ∀ a : I, (Set.Iio a).Countable) (b : I) :
    (sourceSchemeDiagram hcnt).obj b ⟶ baseScheme I :=
  Spec.map (CommRingCat.ofHom (dualLamProj b))

/-- The structure morphisms of the source stages are compatible with the transitions: a
transition of the source system carries the ring component to the ring component, so no twist
enters. -/
theorem sourceStructureMap_naturality (hcnt : ∀ a : I, (Set.Iio a).Countable) {b a : I}
    (f : b ⟶ a) :
    (sourceSchemeDiagram hcnt).map f ≫ sourceStructureMap hcnt a = sourceStructureMap hcnt b := by
  exact spec_map_ofHom_comp_eq _ _ _ fun x ↦ by
    rw [dualLamProj_apply, dualMap_inl, stageRingMap_comp_lamProj, dualLamProj_apply]

end Stacks.Coherent

end
