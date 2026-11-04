module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import Mathlib.CategoryTheory.Sites.CoverLifting
import StacksCore.Tactic.EgaSgaAttribute

/-! # Continuous functors which have a continuous left adjoint

Let `(C, J)` and `(D, K)` be sites and let `v : D ⥤ C` be a continuous functor admitting a left
adjoint `u : C ⥤ D`.  Stacks 09VR records that `u` is then automatically cocontinuous and that
`v` defines a morphism of sites `C → D` in the sense of Stacks 00X1.

## Main results

* `CategoryTheory.Adjunction.isCocontinuous_leftAdjoint_of_isContinuous`: the left adjoint of a
  continuous functor is cocontinuous (Stacks 09VR(1)).
* `CategoryTheory.Adjunction.isMorphismOfSites_of_isLeftAdjoint`: a continuous functor which is a
  right adjoint defines a morphism of sites (the "in particular" of Stacks 09VR, i.e. the
  conclusion of Stacks 00XY for the pair `(u, v)`).

Tags covered: 09VR.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open CategoryTheory

universe u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {u : C ⥤ D} {v : D ⥤ C}

/-- **Stacks 09VR(1).** Let `(C, J)` and `(D, K)` be sites, let `v : D ⥤ C` be a continuous
functor and assume `v` has a left adjoint `u : C ⥤ D`.  Then `u` is cocontinuous.

Cocontinuity of a left adjoint is equivalent to cover preservation of its right adjoint
(`Adjunction.isCocontinuous_iff_coverPreserving`), and a continuous functor preserves covering
sieves (`CoverPreserving.of_isContinuous`). -/
@[stacks 09VR, sga "4 III 2.5" "(i) ⇒ (ii)"]
theorem isCocontinuous_leftAdjoint_of_isContinuous (adj : u ⊣ v) [v.IsContinuous K J] :
    u.IsCocontinuous J K := by
  rw [adj.isCocontinuous_iff_coverPreserving]
  exact CoverPreserving.of_isContinuous v K J

/-- **Stacks 09VR, final assertion.** A continuous functor `v : D ⥤ C` which admits a left adjoint
defines a morphism of sites `f : C → D`, i.e. `v` is continuous and the induced pullback
`v_s = f⁻¹` on sheaves of sets is exact.

Indeed a right adjoint is representably flat (`RepresentablyFlat.of_isRightAdjoint`: the comma
category `StructuredArrow X v` has an initial object, namely the unit of the adjunction), so this
is the criterion of Stacks 00X5 recorded as
`CategoryTheory.Functor.isMorphismOfSites_of_representablyFlat`. -/
@[stacks 09VR, sga "4 III 2.5" "u^s left exact"]
theorem isMorphismOfSites_of_isLeftAdjoint (adj : u ⊣ v) [v.IsContinuous K J] :
    v.IsMorphismOfSites K J :=
  have : v.IsRightAdjoint := adj.isRightAdjoint
  Functor.isMorphismOfSites_of_representablyFlat v K J

end CategoryTheory.Adjunction
