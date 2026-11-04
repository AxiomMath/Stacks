module

public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafEqToHom

/-!
# Lifting an integral closed subscheme along a completely decomposed morphism

Let `f : Y ⟶ X` be completely decomposed (Stacks 0GTI) and let `W ⊆ X` be an integral closed
subscheme with generic point `x`. Choosing a preimage `y` of `x` at which `f` induces an
isomorphism of residue fields and taking the integral closed subscheme `V ⊆ Y` with generic
point `y`, the morphism `V ⟶ X` factors through `W` by a morphism `V ⟶ W` which is dominant,
is proper as soon as `f` is, and induces an isomorphism of residue fields at the generic point
of `V`. In particular `V` and `W` have the same delta-dimension over the base.

## Main definitions

* `Stacks.Chow.envelopeSubschemeLift` — the integral closed subscheme of `Y` lifting an integral
  closed subscheme of `X`.
* `Stacks.Chow.envelopeSubschemeLiftMap` — the morphism from the lift to the original closed
  subscheme.

## Main results

* `Stacks.Chow.envelopeSubschemeLiftMap_fac` — the lift is a factorization of `V ⟶ Y ⟶ X`
  through `W ⟶ X`.
* `Stacks.Chow.mem_support_of_mem_support_envelopeSubschemeLift` — the lift lies above `W`.
* `Stacks.Chow.isProper_envelopeSubschemeLiftMap`,
  `Stacks.Chow.isDominant_envelopeSubschemeLiftMap` — the morphism is proper and dominant.
* `Stacks.Chow.envelopeSubschemeLiftMap_residueFieldMap_isIso` — it induces an isomorphism of
  residue fields at the generic point of the lift.
* `Stacks.Chow.schemeDeltaDimension_envelopeSubschemeLift` — the lift has the same
  delta-dimension over the base as the original closed subscheme.
* `Stacks.Chow.properPushforward_apply_congr` — proper pushforward along equal morphisms agrees.

## Implementation notes

The lift is `Stacks.Chow.integralComponentAt` of the chosen preimage `y`, so it is determined by
its generic point.

## References

* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Proper pushforward along equal morphisms -/

/-- Two equal proper morphisms over the base push cycles forward in the same way. -/
theorem properPushforward_apply_congr (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {p p' : X ⟶ Y} [IsProper p]
    [IsProper p'] (h : p = p') (hp : p ≫ sY = sX) (hp' : p' ≫ sY = sX) (k : ℤ)
    (c : CycleGroup C sX k) :
    properPushforward C sX sY p hp k c = properPushforward C sX sY p' hp' k c := by
  subst h; rfl

/-! ### Residue fields along a transport -/

/-- Transporting a scheme along an equality induces an isomorphism of residue fields. -/
theorem residueFieldMap_eqToHom_isIso {X Y : Scheme.{u}} (h : X = Y) (x : X) :
    IsIso ((eqToHom h).residueFieldMap x) := by
  subst h; infer_instance

/-! ### The lift of an integral closed subscheme -/

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f) (W : X.IdealSheafData)
  (hW : IsIntegral W.subscheme)

/-- The integral closed subscheme of `Y` lifting an integral closed subscheme `W` of `X` along a
completely decomposed morphism `f : Y ⟶ X`: the integral closed subscheme whose generic point is
the chosen preimage of the generic point of `W`. -/
def envelopeSubschemeLift : Y.IdealSheafData :=
  integralComponentAt (envelopePointLift f hcd (genericPointOf W hW))

/-- The lift of an integral closed subscheme is integral. -/
theorem isIntegral_envelopeSubschemeLift :
    IsIntegral (envelopeSubschemeLift f hcd W hW).subscheme :=
  isIntegral_integralComponentAt _

/-- The generic point of the lift is the chosen preimage of the generic point of `W`. -/
@[simp]
theorem genericPointOf_envelopeSubschemeLift :
    genericPointOf (envelopeSubschemeLift f hcd W hW)
        (isIntegral_envelopeSubschemeLift f hcd W hW) =
      envelopePointLift f hcd (genericPointOf W hW) :=
  genericPointOf_integralComponentAt _

/-- The lift is supported on the closure of the chosen preimage of the generic point of `W`. -/
@[simp]
theorem coe_support_envelopeSubschemeLift :
    ((envelopeSubschemeLift f hcd W hW).support : Set Y) =
      closure {envelopePointLift f hcd (genericPointOf W hW)} :=
  coe_support_integralComponentAt _

/-- The image of the lift is contained in `W`. -/
theorem range_subschemeι_envelopeSubschemeLift_comp_subset :
    Set.range ((envelopeSubschemeLift f hcd W hW).subschemeι ≫ f).base ⊆
      (W.support : Set X) := by
  have hrange : Set.range (envelopeSubschemeLift f hcd W hW).subschemeι.base =
      closure {envelopePointLift f hcd (genericPointOf W hW)} := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_envelopeSubschemeLift]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange,
    support_eq_closure_genericPointOf W hW]
  refine (image_closure_subset_closure_image f.continuous).trans ?_
  rw [Set.image_singleton, envelopePointLift_map]

/-- A point of the lift lies above a point of `W`. -/
theorem mem_support_of_mem_support_envelopeSubschemeLift {z : Y}
    (hz : z ∈ ((envelopeSubschemeLift f hcd W hW).support : Set Y)) :
    f.base z ∈ (W.support : Set X) := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hz
  obtain ⟨w, rfl⟩ := hz
  exact range_subschemeι_envelopeSubschemeLift_comp_subset f hcd W hW ⟨w, rfl⟩

/-- The ideal sheaf of `W` is contained in the kernel of the composite `V ⟶ Y ⟶ X`. -/
theorem ker_subschemeι_le_envelopeSubschemeLift :
    W.subschemeι.ker ≤ ((envelopeSubschemeLift f hcd W hW).subschemeι ≫ f).ker := by
  have := isIntegral_envelopeSubschemeLift f hcd W hW
  have hsupport : (W.comap ((envelopeSubschemeLift f hcd W hW).subschemeι ≫ f)).support = ⊤ := by
    apply SetLike.coe_injective
    ext z
    rw [Scheme.IdealSheafData.support_comap]
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    exact range_subschemeι_envelopeSubschemeLift_comp_subset f hcd W hW ⟨z, rfl⟩
  have hcomap : W.comap ((envelopeSubschemeLift f hcd W hW).subschemeι ≫ f) = ⊥ :=
    Scheme.IdealSheafData.support_eq_top_iff.mp hsupport
  rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_bot]
  exact Scheme.IdealSheafData.le_map_iff_comap_le.2 (by rw [hcomap])

/-- The morphism from the lift of `W` to `W` factoring `V ⟶ Y ⟶ X` through the closed immersion
of `W`. -/
def envelopeSubschemeLiftMap : (envelopeSubschemeLift f hcd W hW).subscheme ⟶ W.subscheme :=
  IsClosedImmersion.lift W.subschemeι ((envelopeSubschemeLift f hcd W hW).subschemeι ≫ f)
    (ker_subschemeι_le_envelopeSubschemeLift f hcd W hW)

/-- The morphism from the lift of `W` is a factorization of `V ⟶ Y ⟶ X`. -/
theorem envelopeSubschemeLiftMap_fac :
    envelopeSubschemeLiftMap f hcd W hW ≫ W.subschemeι =
      (envelopeSubschemeLift f hcd W hW).subschemeι ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism from the lift of `W` is proper when `f` is. -/
theorem isProper_envelopeSubschemeLiftMap [IsProper f] :
    IsProper (envelopeSubschemeLiftMap f hcd W hW) := by
  have : IsProper (envelopeSubschemeLiftMap f hcd W hW ≫ W.subschemeι) := by
    rw [envelopeSubschemeLiftMap_fac]
    infer_instance
  exact IsProper.of_comp _ W.subschemeι

/-- The morphism from the lift of `W` carries the generic point of the lift to the generic point
of `W`. -/
theorem envelopeSubschemeLiftMap_genericPoint :
    have := isIntegral_envelopeSubschemeLift f hcd W hW
    have := hW
    (envelopeSubschemeLiftMap f hcd W hW).base
        (genericPoint (envelopeSubschemeLift f hcd W hW).subscheme) =
      genericPoint W.subscheme := by
  have := isIntegral_envelopeSubschemeLift f hcd W hW
  have := hW
  apply W.subschemeι.isClosedEmbedding.injective
  have h := congrArg (fun g : (envelopeSubschemeLift f hcd W hW).subscheme ⟶ X ↦
    g.base (genericPoint (envelopeSubschemeLift f hcd W hW).subscheme))
    (envelopeSubschemeLiftMap_fac f hcd W hW)
  change W.subschemeι.base _ = _ at h
  refine h.trans ?_
  show f.base ((envelopeSubschemeLift f hcd W hW).subschemeι.base _) = _
  show f.base (genericPointOf (envelopeSubschemeLift f hcd W hW)
    (isIntegral_envelopeSubschemeLift f hcd W hW)) = _
  rw [genericPointOf_envelopeSubschemeLift, envelopePointLift_map]
  rfl

/-- The morphism from the lift of `W` is dominant. -/
theorem isDominant_envelopeSubschemeLiftMap : IsDominant (envelopeSubschemeLiftMap f hcd W hW) := by
  have := isIntegral_envelopeSubschemeLift f hcd W hW
  have := hW
  rw [isDominant_iff, denseRange_iff_closure_range]
  refine le_antisymm (Set.subset_univ _) ?_
  rw [← (genericPoint_spec W.subscheme).def]
  exact closure_mono (Set.singleton_subset_iff.mpr
    ⟨genericPoint (envelopeSubschemeLift f hcd W hW).subscheme,
      envelopeSubschemeLiftMap_genericPoint f hcd W hW⟩)

/-- The morphism from the lift of `W` induces an isomorphism of residue fields at the generic
point of the lift. -/
theorem envelopeSubschemeLiftMap_residueFieldMap_isIso :
    have := isIntegral_envelopeSubschemeLift f hcd W hW
    IsIso ((envelopeSubschemeLiftMap f hcd W hW).residueFieldMap
      (genericPoint (envelopeSubschemeLift f hcd W hW).subscheme)) := by
  have := isIntegral_envelopeSubschemeLift f hcd W hW
  have := hW
  set V := envelopeSubschemeLift f hcd W hW
  set η := genericPoint V.subscheme
  have hbase : V.subschemeι.base η = envelopePointLift f hcd (genericPointOf W hW) :=
    genericPointOf_envelopeSubschemeLift f hcd W hW
  have hfIso : IsIso (f.residueFieldMap (V.subschemeι.base η)) := by
    rw [hbase]
    exact envelopePointLift_residueFieldMap_isIso f hcd _
  have hVIso : IsIso (V.subschemeι.residueFieldMap η) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_isPreimmersion V.subschemeι η
  have hOrig : IsIso ((V.subschemeι ≫ f).residueFieldMap η) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hfIso hVIso
  have hcongr := Scheme.Hom.residueFieldMap_congr (envelopeSubschemeLiftMap_fac f hcd W hW) η
  have hcomp : IsIso ((envelopeSubschemeLiftMap f hcd W hW ≫ W.subschemeι).residueFieldMap η) := by
    rw [hcongr]
    infer_instance
  have hsplit : IsIso (W.subschemeι.residueFieldMap
      ((envelopeSubschemeLiftMap f hcd W hW).base η) ≫
      (envelopeSubschemeLiftMap f hcd W hW).residueFieldMap η) := by
    rw [← Scheme.residueFieldMap_comp]
    exact hcomp
  have : IsIso (W.subschemeι.residueFieldMap
      ((envelopeSubschemeLiftMap f hcd W hW).base η)) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_isPreimmersion W.subschemeι _
  exact IsIso.of_isIso_comp_left (W.subschemeι.residueFieldMap
      ((envelopeSubschemeLiftMap f hcd W hW).base η))
    ((envelopeSubschemeLiftMap f hcd W hW).residueFieldMap η)

/-- The lift of `W` has the same delta-dimension over the base as `W`. -/
theorem schemeDeltaDimension_envelopeSubschemeLift (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] [LocallyOfFiniteType f] :
    schemeDeltaDimension C ((envelopeSubschemeLift f hcd W hW).subschemeι ≫ f ≫ sX) =
      schemeDeltaDimension C (W.subschemeι ≫ sX) := by
  have := isIntegral_envelopeSubschemeLift f hcd W hW
  have := hW
  set V := envelopeSubschemeLift f hcd W hW
  have hreldim := relativeDimension_eq_of_residueFieldMap_isIso C (W.subschemeι ≫ sX)
    (envelopeSubschemeLiftMap f hcd W hW) (genericPoint V.subscheme)
    (envelopeSubschemeLiftMap_residueFieldMap_isIso f hcd W hW)
  rw [← Category.assoc, envelopeSubschemeLiftMap_fac, Category.assoc,
    envelopeSubschemeLiftMap_genericPoint f hcd W hW] at hreldim
  rw [schemeDeltaDimension_eq_genericPoint C (V.subschemeι ≫ f ≫ sX),
    schemeDeltaDimension_eq_genericPoint C (W.subschemeι ≫ sX), hreldim]

end Stacks.Chow

end
