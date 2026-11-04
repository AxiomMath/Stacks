module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionOnCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.TensorPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The action on cycles of the family attached to a flat coherent module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be locally of
finite type over `S` and let `f : X ⟶ Y` be locally of finite type. Let `F` be a coherent
`𝒪_X`-module whose support on every scheme-theoretic fibre of `f` has dimension at most `r`, and
let `G` be a coherent `𝒪_Y`-module whose support has delta-dimension at most `e`. Write
`α = [F/X/Y]_r` for the associated family of `r`-cycles on the fibres of `f` and `β = [G]_e` for
the associated `e`-cycle on `Y`.

This file proves that when `F` is flat over `Y` the action `α ∩ β` is the cycle associated to the
coherent module `F ⊗_{𝒪_X} f^* G`.

## Main results

* `Stacks.Chow.relativeDimension_fiberToSpecResidueField` — the relative dimension of a point of
  a fibre over the residue field of its base point is the transcendence degree of the residue
  field extension of `f` at that point.
* `Stacks.Chow.schemeDeltaDimension_tensorPullback_le` — the support of `F ⊗_{𝒪_X} f^* G` has
  delta-dimension at most `r + e`, so that the cycle `[F ⊗_{𝒪_X} f^* G]_{r + e}` is defined.
* `Stacks.Chow.cap_familyAssociatedToModule` — the equality `α ∩ β = [F ⊗_{𝒪_X} f^* G]_{r + e}`.

## Implementation notes

The dimension bound on the support of the tensor product is the first paragraph of the source's
proof and does not use flatness, so it is proved separately and then used to form the right-hand
side of the main statement. It is a pointwise statement: a point of the support of
`F ⊗_{𝒪_X} f^* G` lies in `Supp(F) ∩ f^{-1}Supp(G)`, so its image has relative dimension at most
`e` over the base and it contributes at most `r` more in the fibre direction, transcendence degree
being additive in a tower.

Flatness enters only through the multiplicity: at a point of the support both sides are a product
of a multiplicity of `G` on the base with a multiplicity of `F` on the fibre, and
`AlgebraicGeometry.sheafMultiplicity_mul_sheafMultiplicity_pullback_fiberι` identifies that
product with the multiplicity of the tensor product. Both sides of the equality lie in
`Stacks.Chow.CycleGroup C (f ≫ sY) (r + e)`, so no cast appears.

`X` is locally Noetherian and the composite `f ≫ sY` is locally of finite type for free, so
neither is assumed; they are produced from the hypotheses, the first in the statement because the
coherence of `F ⊗_{𝒪_X} f^* G` — and hence the right-hand side — depends on it.

## References

* [Stacks Project, Tag 0H69](https://stacks.math.columbia.edu/tag/0H69)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f]

/-- On the scheme-theoretic fibre of `f` through `x`, taken over the spectrum of the residue
field of the base point, the relative dimension of the point corresponding to `x` is the
transcendence degree of the residue field extension that `f` induces at `x`. The dimension
function of the Chow situation on a field vanishes, so the relative dimension there is nothing
but that transcendence degree. -/
theorem relativeDimension_fiberToSpecResidueField (x : X) :
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    relativeDimension (fieldChowSituation (Y.residueField (f x))).dimensionFunction
        (f.fiberToSpecResidueField (f x)) (f.asFiber x) =
      (Cardinal.toNat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) : ℤ) := by
  unfold relativeDimension
  rw [fieldChowSituation_dimensionFunction_eq_zero, zero_add]
  exact congrArg Nat.cast (fiber_trdeg_eq f x).symm

/-- A point `x` of the support of `F ⊗_{𝒪_X} f^* G` gives a point of the support of the restriction
of `F` to the fibre through `x` and of `G`, with the relative dimension bounds on each. -/
private theorem supp_tensorPullback_relativeDimension_le (r : ℕ) (e : ℤ) (F : X.Modules)
    [F.IsCoherent]
    (hdim : ∀ y : Y, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι y)).obj F)) ≤ (r : WithBot ℕ∞))
    (G : Y.Modules) [G.IsCoherent]
    (hGe : schemeDeltaDimension C ((reducedSupport G).subschemeι ≫ sY) ≤ (e : EInt))
    (x : X) (hx : x ∈ SheafOfModules.supp (tensorPullback f F G)) :
    f.asFiber x ∈ SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) ∧
      f x ∈ SheafOfModules.supp G ∧ relativeDimension C.dimensionFunction sY (f x) ≤ e ∧
      relativeDimension (fieldChowSituation (Y.residueField (f x))).dimensionFunction
        (f.fiberToSpecResidueField (f x)) (f.asFiber x) ≤ (r : ℤ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let : G.IsFiniteType := isFiniteType_of_isCoherent G
  obtain ⟨hxF, hyG⟩ := supp_tensorPullback_subset f F G hx
  have hzF : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) := by
    rw [Stacks.Modules.supp_pullback]
    simpa [Scheme.Hom.fiberι_asFiber] using hxF
  exact ⟨hzF, hyG, relativeDimension_le_of_mem_supp C sY G hGe hyG,
    relativeDimension_le_of_mem_supp (fieldChowSituation (Y.residueField (f x)))
      (f.fiberToSpecResidueField (f x)) ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)
      (fiberModule_schemeDeltaDimension_le f F r hdim (f x)) hzF⟩

/-- The first paragraph of the proof of Stacks 0H69: since
`Supp(F ⊗ f^* G) ⊆ Supp(F) ∩ f^{-1}Supp(G)`, the support of `F ⊗_{𝒪_X} f^* G` has
delta-dimension at most `r + e`. This is what makes the cycle `[F ⊗_{𝒪_X} f^* G]_{r + e}` well
defined; it does not use flatness of `F`. -/
theorem schemeDeltaDimension_tensorPullback_le (r : ℕ) (e : ℤ) (F : X.Modules) [F.IsCoherent]
    (hdim : ∀ y : Y, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι y)).obj F)) ≤ (r : WithBot ℕ∞))
    (G : Y.Modules) [G.IsCoherent]
    (hGe : schemeDeltaDimension C ((reducedSupport G).subschemeι ≫ sY) ≤ (e : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
    schemeDeltaDimension C ((reducedSupport (tensorPullback f F G)).subschemeι ≫ (f ≫ sY)) ≤
      (((r : ℤ) + e : ℤ) : EInt) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  refine schemeDeltaDimension_reducedSupport_le C (f ≫ sY) (tensorPullback f F G) fun x hx => ?_
  obtain ⟨-, -, hbase, hfiber⟩ :=
    supp_tensorPullback_relativeDimension_le C sY f r e F hdim G hGe x hx
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [relativeDimension_fiberToSpecResidueField f x] at hfiber
  have hcomp := relativeDimension_comp_add_of_trdeg C.dimensionFunction f sY x
    (Cardinal.toNat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x))) rfl
  omega

/-- **Stacks Project, Tag 0H69.** Let `(S, δ)` and `f : X ⟶ Y` be as in Section 0H65, let `F` be
a coherent `𝒪_X`-module whose support on every fibre of `f` has dimension at most `r` and let `G`
be a coherent `𝒪_Y`-module whose support has delta-dimension at most `e`. Set `α = [F/X/Y]_r` and
`β = [G]_e`. If `F` is flat over `Y` then `α ∩ β = [F ⊗_{𝒪_X} f^* G]_{r + e}`. -/
@[stacks 0H69]
theorem cap_familyAssociatedToModule (r : ℕ) (e : ℤ) (F : X.Modules) [F.IsCoherent]
    (hdim : ∀ y : Y, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι y)).obj F)) ≤ (r : WithBot ℕ∞))
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (G : Y.Modules) [G.IsCoherent]
    (hGe : schemeDeltaDimension C ((reducedSupport G).subschemeι ≫ sY) ≤ (e : EInt)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
    letI : F.IsFiniteType := isFiniteType_of_isCoherent F
    letI : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
    cap C sY f (familyAssociatedToModule f F r hdim)
        (cycleAssociatedToCoherentSheaf C sY G e hGe) =
      cycleAssociatedToCoherentSheaf C (f ≫ sY) (tensorPullback f F G) ((r : ℤ) + e)
        (schemeDeltaDimension_tensorPullback_le C sY f r e F hdim G hGe) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let : G.IsFiniteType := isFiniteType_of_isCoherent G
  ext x
  simp only [cap_apply, capCoeff, familyAssociatedToModule_apply,
    cycleAssociatedToCoherentSheaf_apply]
  let y : Y := f x
  let z : f.fiber y := f.asFiber x
  let Fy : (f.fiber y).Modules := (Scheme.Modules.pullback (f.fiberι y)).obj F
  let q := f.fiberToSpecResidueField y
  let T : X.Modules := tensorPullback f F G
  let P : Prop :=
    f x ∈ SheafOfModules.supp G ∧ relativeDimension C.dimensionFunction sY (f x) = e
  let Q : Prop := z ∈ SheafOfModules.supp Fy ∧
    relativeDimension (fieldChowSituation (Y.residueField (f x))).dimensionFunction q z = (r : ℤ)
  let R : Prop := x ∈ SheafOfModules.supp T ∧
    relativeDimension C.dimensionFunction (f ≫ sY) x = (r : ℤ) + e
  change (if P then sheafMultiplicity G (f x) else 0) *
      (if Q then sheafMultiplicity Fy z else 0) =
    if R then sheafMultiplicity T x else 0
  let : Algebra (Y.residueField y) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let t := Cardinal.toNat (Algebra.trdeg (Y.residueField y) (X.residueField x))
  have hfieldRel :
      relativeDimension (fieldChowSituation (Y.residueField y)).dimensionFunction q z = (t : ℤ) :=
    relativeDimension_fiberToSpecResidueField f x
  have hcomp : relativeDimension C.dimensionFunction (f ≫ sY) x =
      relativeDimension C.dimensionFunction sY (f x) + (t : ℤ) :=
    relativeDimension_comp_add_of_trdeg C.dimensionFunction f sY x t rfl
  have hlenG (hp : P) : IsFiniteLength (Y.presheaf.stalk (f x)) (G.presheaf.stalk (f x)) :=
    isFiniteLength_stalk_of_relativeDimension_eq C sY G hGe hp.2
  have hlenF (hq : Q) : IsFiniteLength ((f.fiber y).presheaf.stalk z) (Fy.presheaf.stalk z) :=
    isFiniteLength_stalk_of_relativeDimension_eq (fieldChowSituation (Y.residueField y)) q Fy
      (fiberModule_schemeDeltaDimension_le f F r hdim y) hq.2
  have hmult (hp : P) :
      sheafMultiplicity G (f x) * sheafMultiplicity Fy z = sheafMultiplicity T x :=
    sheafMultiplicity_mul_sheafMultiplicity_pullback_fiberι f F G x (hflat x) (hlenG hp)
  have hconditions : P ∧ Q ↔ R := by
    constructor
    · rintro ⟨hp, hq⟩
      refine ⟨mem_supp_of_sheafMultiplicity_ne_zero T ?_, by
        rw [hcomp, hp.2, hfieldRel.symm.trans hq.2, add_comm]⟩
      rw [← hmult hp]
      exact (mul_pos (sheafMultiplicity_pos_of_mem_supp G (hlenG hp) hp.1)
        (sheafMultiplicity_pos_of_mem_supp Fy (hlenF hq) hq.1)).ne'
    · rintro ⟨hxT, htot⟩
      obtain ⟨hzF, hyG, hbase, hfib⟩ :=
        supp_tensorPullback_relativeDimension_le C sY f r e F hdim G hGe x hxT
      rw [hfieldRel] at hfib
      rw [hcomp] at htot
      exact ⟨⟨hyG, by omega⟩, ⟨hzF, by rw [hfieldRel]; omega⟩⟩
  by_cases hp : P <;> by_cases hq : Q
  · simp [hp, hq, hconditions.mp ⟨hp, hq⟩, hmult hp]
  · simp [hp, hq, show ¬R from fun hr => hq (hconditions.mpr hr).2]
  all_goals simp [hp, hq, show ¬R from fun hr => hp (hconditions.mpr hr).1]

end Stacks.Chow
