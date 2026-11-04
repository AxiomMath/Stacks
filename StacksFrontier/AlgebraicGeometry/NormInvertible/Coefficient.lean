module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The coefficient of a map of modules in local frames, and its vanishing locus

Let `L` and `L'` be sheaves of modules on a ringed space and let `φ : L ⟶ L'`. Over an open `U`
carrying generators `s` of `L` and `t` of `L'` the section `φ(s)` is a unique multiple `a · t`:
the *coefficient* of `φ` in the frame `(s, t)`. This file constructs it, computes it under
restriction and under a change of frame, and uses it to define what it means for `φ` to vanish
at a point of a scheme — the coefficient lies in the maximal ideal there — showing that this is
independent of the frame.

This is the frame calculus of [Stacks, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ),
whose norm map is defined frame by frame and whose vanishing locus is read off from the
coefficient.

## Main definitions

* `Stacks.SheafOfModules.generatorCoefficient`: the coefficient of `φ` in a frame.
* `Stacks.SheafOfModules.zeroAt`: a map of modules on a scheme vanishes at a point.

## Main results

* `Stacks.SheafOfModules.generatorCoefficient_spec` and `_unique`: the coefficient is
  characterized by the equation `φ(s) = a · t`.
* `Stacks.SheafOfModules.generatorCoefficient_restrict`: the coefficient commutes with
  restriction.
* `Stacks.SheafOfModules.generatorCoefficient_change`: under a change of both frames the
  coefficient changes by the two generator ratios, `a' d = c a`.
* `Stacks.SheafOfModules.zeroAt_iff_evaluation_eq_zero`: vanishing at a point is computed in
  *any* frame around that point — this is what makes `zeroAt` well posed.

## Implementation notes

`generatorCoefficient` is produced from the surjectivity half of `t`'s defining bijection and
pinned down by the injectivity half, so the `∃!` is immediate; it is stated as a definition plus
`spec`/`unique` rather than as the `∃!` itself because every consumer needs the value.

Frame independence of `zeroAt` is where the units come in: changing frames multiplies the
coefficient by units `c` and `d`, and the residue field of a point is a field, so a unit has
nonzero image there — this is `generatorCoefficient_eval_eq_zero_iff`, which is pure
commutative algebra and is stated for an arbitrary ring map to a field. Two frames around the
same point are compared on the intersection of their opens, not directly, since neither need
contain the other.

No invertibility hypothesis appears: a frame is explicit data, and a module admitting one on an
open is trivial there by definition.

## References

* [Stacks Project, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

section Coefficient

variable {X : RingedSpace.{u, u}}
  (L L' : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)) (φ : L ⟶ L')

/-- Two scalars with the same multiple of a generator are equal. -/
private theorem eq_of_smul_generator_eq (U : Opens X.carrier) (t : GeneratorSections X L U)
    {a b : (structureSheaf X.sheaf).obj.obj (op U)} (h : a • t.val = b • t.val) : a = b :=
  (t.property U le_rfl).injective (by simpa only [generator_restrict_self] using h)

/-- A map of modules is multiplication by a unique coefficient once frames are chosen. -/
theorem existsUnique_generatorCoefficient (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U) :
    ∃! a : (structureSheaf X.sheaf).obj.obj (op U),
      φ.val.app (op U) s.val = a • t.val := by
  have ht := t.property U le_rfl
  obtain ⟨a, ha⟩ := ht.surjective (φ.val.app (op U) s.val)
  have h : φ.val.app (op U) s.val = a • t.val := by
    rw [← generator_restrict_self L' U t]
    exact ha.symm
  exact ⟨a, h, fun b hb => eq_of_smul_generator_eq L' U t (hb.symm.trans h)⟩

/-- The coefficient of a map of modules in the frame `(s, t)`. -/
noncomputable def generatorCoefficient (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U) :
    (structureSheaf X.sheaf).obj.obj (op U) :=
  (existsUnique_generatorCoefficient L L' φ U s t).choose

/-- The image of the generator `s` under `φ` is `generatorCoefficient L L' φ U s t • t`. -/
theorem generatorCoefficient_spec (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U) :
    φ.val.app (op U) s.val = generatorCoefficient L L' φ U s t • t.val :=
  (existsUnique_generatorCoefficient L L' φ U s t).choose_spec.1

/-- Any `a` with `φ(s) = a • t` is the coefficient of `φ` in the frame `(s, t)`. -/
theorem generatorCoefficient_unique (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U)
    (a : (structureSheaf X.sheaf).obj.obj (op U))
    (ha : φ.val.app (op U) s.val = a • t.val) :
    generatorCoefficient L L' φ U s t = a :=
  ((existsUnique_generatorCoefficient L L' φ U s t).choose_spec.2 a ha).symm

/-- The coefficient commutes with restriction. -/
theorem generatorCoefficient_restrict {U V : Opens X.carrier} (h : V ≤ U)
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U) :
    generatorCoefficient L L' φ V (generatorRestrict L h s) (generatorRestrict L' h t) =
      (structureSheaf X.sheaf).obj.map (homOfLE h).op (generatorCoefficient L L' φ U s t) := by
  refine generatorCoefficient_unique L L' φ V _ _ _ ?_
  have hn := PresheafOfModules.naturality_apply φ.val (homOfLE h).op s.val
  change φ.val.app (op V) (L.val.restrictₛₗ (homOfLE h).op s.val) =
    L'.val.restrictₛₗ (homOfLE h).op (φ.val.app (op U) s.val) at hn
  show φ.val.app (op V) (L.val.restrictₛₗ (homOfLE h).op s.val) = _
  rw [hn, generatorCoefficient_spec L L' φ U s t]
  show L'.val.map (homOfLE h).op (generatorCoefficient L L' φ U s t • t.val) = _
  rw [L'.val.map_smul]
  rfl

/-- Changing both frames transforms the coefficient by the two generator ratios. -/
theorem generatorCoefficient_change (U : Opens X.carrier)
    (s s' : GeneratorSections X L U) (t t' : GeneratorSections X L' U)
    (c d a a' : (structureSheaf X.sheaf).obj.obj (op U))
    (hs : s'.val = c • s.val) (ht : t'.val = d • t.val)
    (ha : φ.val.app (op U) s.val = a • t.val)
    (ha' : φ.val.app (op U) s'.val = a' • t'.val) :
    a' * d = c * a := by
  have hcoeff : (a' * d) • t.val = (c * a) • t.val := by
    rw [mul_smul, mul_smul, ← ht, ← ha', hs, ← ha]
    exact (φ.val.app (op U)).hom.map_smul c s.val
  exact eq_of_smul_generator_eq L' U t hcoeff

/-- A generator is a unit multiple of any other generator on the same open. -/
theorem exists_isUnit_smul_generator (U : Opens X.carrier) (s t : GeneratorSections X L U) :
    ∃ a : (structureSheaf X.sheaf).obj.obj (op U), t.val = a • s.val ∧ IsUnit a :=
  ⟨generatorRatio L U s t, generatorRatio_spec L U s t,
    isUnit_of_smul_eq_generator L U s t _ (generatorRatio_spec L U s t)⟩

end Coefficient

/-- Multiplying a coefficient by units from a frame change does not alter whether it vanishes
in a residue field. -/
theorem generatorCoefficient_eval_eq_zero_iff {R K : Type*} [CommRing R] [Field K]
    (e : R →+* K) (a a' c d : R) (hc : IsUnit c) (hd : IsUnit d) (h : a' * d = c * a) :
    e a = 0 ↔ e a' = 0 := by
  have h' : e a' * e d = e c * e a := by simpa using congrArg e h
  rw [← mul_eq_zero_iff_left (hc.map e).ne_zero, ← h', mul_eq_zero_iff_right (hd.map e).ne_zero]

section ZeroAt

variable {X : Scheme.{u}}

/-- A restricted section vanishes at a point of the smaller open if and only if the section
itself vanishes there. -/
theorem evaluation_map_eq_zero_iff {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V)
    (a : Γ(X, U)) :
    X.evaluation V x hx (X.presheaf.map (homOfLE h).op a) = 0 ↔
      X.evaluation U x (h hx) a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen,
    Scheme.evaluation_eq_zero_iff_notMem_basicOpen, Scheme.basicOpen_res]
  simp [hx]

/-- Evaluating the coefficient in a restricted frame vanishes at a point of the smaller open if and
only if the coefficient in the original frame does. -/
private theorem evaluation_generatorCoefficient_restrict_eq_zero_iff (L L' : X.Modules)
    (φ : L ⟶ L') {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V)
    (s : GeneratorSections X.toRingedSpace L U) (t : GeneratorSections X.toRingedSpace L' U) :
    X.evaluation V x hx
        (generatorCoefficient L L' φ V (generatorRestrict L h s) (generatorRestrict L' h t)) = 0 ↔
      X.evaluation U x (h hx) (generatorCoefficient L L' φ U s t) = 0 := by
  rw [generatorCoefficient_restrict (X := X.toRingedSpace) L L' φ h s t]
  exact evaluation_map_eq_zero_iff h x hx _

/-- A map of modules on a scheme *vanishes at* a point when its coefficient in some frame
around that point lies in the maximal ideal there, that is, evaluates to zero in the residue
field. By `zeroAt_iff_evaluation_eq_zero` the frame does not matter. -/
def zeroAt (L L' : X.Modules) (φ : L ⟶ L') (x : X) : Prop :=
  ∃ (U : X.Opens) (hx : x ∈ U) (s : GeneratorSections X.toRingedSpace L U)
    (t : GeneratorSections X.toRingedSpace L' U) (a : Γ(X, U)),
      φ.val.app (op U) s.val =
        @SMul.smul ((structureSheaf X.sheaf).obj.obj (op U)) (L'.val.obj (op U)) _ a t.val ∧
      X.evaluation U x hx a = 0

/-- **Vanishing at a point is computed in any frame around it.** -/
theorem zeroAt_iff_generatorCoefficient_eq_zero (L L' : X.Modules) (φ : L ⟶ L')
    (U : X.Opens) (x : X) (hx : x ∈ U) (s : GeneratorSections X.toRingedSpace L U)
    (t : GeneratorSections X.toRingedSpace L' U) :
    zeroAt L L' φ x ↔
      X.evaluation U x hx (generatorCoefficient L L' φ U s t) = 0 := by
  refine ⟨?_, fun h => ⟨U, hx, s, t, generatorCoefficient L L' φ U s t,
    generatorCoefficient_spec L L' φ U s t, h⟩⟩
  rintro ⟨V, hxV, s', t', b, hb, hb0⟩
  set W := U ⊓ V
  have hW : x ∈ W := ⟨hx, hxV⟩
  set sW := generatorRestrict (X := X.toRingedSpace) L (inf_le_left : W ≤ U) s
  set tW := generatorRestrict (X := X.toRingedSpace) L' (inf_le_left : W ≤ U) t
  set sW' := generatorRestrict (X := X.toRingedSpace) L (inf_le_right : W ≤ V) s'
  set tW' := generatorRestrict (X := X.toRingedSpace) L' (inf_le_right : W ≤ V) t'
  obtain ⟨c, hc, hcu⟩ := exists_isUnit_smul_generator L W sW sW'
  obtain ⟨e, he, heu⟩ := exists_isUnit_smul_generator L' W tW tW'
  have hchange := generatorCoefficient_change L L' φ W sW sW' tW tW' c e
    (generatorCoefficient L L' φ W sW tW) (generatorCoefficient L L' φ W sW' tW') hc he
    (generatorCoefficient_spec L L' φ W sW tW)
    (generatorCoefficient_spec L L' φ W sW' tW')
  have hV : X.evaluation V x hxV (generatorCoefficient L L' φ V s' t') = 0 := by
    rw [generatorCoefficient_unique L L' φ V s' t' b hb]
    exact hb0
  exact (evaluation_generatorCoefficient_restrict_eq_zero_iff L L' φ inf_le_left x hW s t).mp
    ((generatorCoefficient_eval_eq_zero_iff (X.evaluation W x hW).hom _ _ c e hcu heu hchange).mpr
      ((evaluation_generatorCoefficient_restrict_eq_zero_iff L L' φ inf_le_right x hW s' t').mpr
        hV))

/-- **Vanishing at a point is the vanishing of the coefficient in any frame around it.** -/
theorem zeroAt_iff_evaluation_eq_zero (L L' : X.Modules) (φ : L ⟶ L')
    (U : X.Opens) (x : X) (hx : x ∈ U) (s : GeneratorSections X.toRingedSpace L U)
    (t : GeneratorSections X.toRingedSpace L' U) (a : Γ(X, U))
    (ha : φ.val.app (op U) s.val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op U)) (L'.val.obj (op U)) _ a t.val) :
    zeroAt L L' φ x ↔ X.evaluation U x hx a = 0 := by
  rw [zeroAt_iff_generatorCoefficient_eq_zero L L' φ U x hx s t,
    generatorCoefficient_unique L L' φ U s t a ha]

end ZeroAt

end Stacks.SheafOfModules
