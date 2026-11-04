module

public import StacksFrontier.Algebra.Homology.HomologyOfZeroDifferentials

/-!
# The homology of a complex with vanishing differentials, on classes

Let `K` be a complex in which the two differentials around the degree `j` vanish, so that the
homology in degree `j` is identified with the term `K.X j` by
`Stacks.HomologicalComplex.homologyIsoX`. This identification carries the class of a cycle to
that cycle, read inside the complex:

`homologyπ ≫ (homologyIsoX …).hom = iCycles`.

## Main results

* `Stacks.HomologicalComplex.homologyπ_comp_homologyIsoX_hom`: the statement above.
* `Stacks.CochainComplex.homologyπ_comp_intHomologyIsoX_hom`: the same for a `ℤ`-indexed cochain
  complex all of whose differentials vanish.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.HomologicalComplex

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {c : ComplexShape ι}

/-- The identification of the homology of a complex with vanishing differentials with its term
carries the class of a cycle to that cycle: precomposed with the projection onto homology, the
isomorphism `Stacks.HomologicalComplex.homologyIsoX` is the inclusion of the cycles into the
complex. -/
@[reassoc]
theorem homologyπ_comp_homologyIsoX_hom (K : _root_.HomologicalComplex C c) (i j k : ι)
    (hi : c.prev j = i) (hk : c.next j = k) (h₁ : K.d i j = 0) (h₂ : K.d j k = 0)
    [K.HasHomology j] :
    K.homologyπ j ≫ (homologyIsoX K i j k hi hk h₁ h₂).hom = K.iCycles j := by
  have hsc : (K.sc' i j k).HasHomology := by subst hi hk; assumption
  have hci : (ShortComplex.LeftHomologyData.ofZeros (K.sc' i j k) h₁ h₂).cyclesIso.hom ≫
        (ShortComplex.LeftHomologyData.ofZeros (K.sc' i j k) h₁ h₂).π =
      (K.sc' i j k).iCycles :=
    ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _
  show K.homologyπ j ≫ (K.homologyIsoSc' i j k hi hk ≪≫
    (ShortComplex.LeftHomologyData.ofZeros (K.sc' i j k) h₁ h₂).homologyIso).hom = K.iCycles j
  rw [Iso.trans_hom, ← Category.assoc, _root_.HomologicalComplex.π_homologyIsoSc'_hom,
    Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, hci]
  exact _root_.HomologicalComplex.cyclesIsoSc'_hom_iCycles K i j k hi hk

end Stacks.HomologicalComplex

namespace Stacks.CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- For a `ℤ`-indexed cochain complex all of whose differentials vanish, the identification
`Stacks.CochainComplex.intHomologyIsoX` of its homology with its term carries the class of a cycle
to that cycle. -/
@[reassoc]
theorem homologyπ_comp_intHomologyIsoX_hom (K : _root_.CochainComplex C ℤ)
    (hd : ∀ n : ℤ, K.d n (n + 1) = 0) (n : ℤ) [K.HasHomology n] :
    K.homologyπ n ≫ (intHomologyIsoX K hd n).hom = K.iCycles n :=
  Stacks.HomologicalComplex.homologyπ_comp_homologyIsoX_hom K (n - 1) n (n + 1) (by simp)
    (by simp) _ _

end Stacks.CochainComplex

end
