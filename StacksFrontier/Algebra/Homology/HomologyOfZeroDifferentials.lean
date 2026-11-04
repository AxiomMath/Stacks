module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The homology of a complex with vanishing differentials

If the two differentials adjacent to a degree of a homological complex vanish, the homology in
that degree is the term itself: the short complex computing it is `0 ⟶ X ⟶ 0`, whose homology is
`X`. For a `ℤ`-indexed cochain complex all of whose differentials vanish this applies in every
degree.

This is what turns a computation of cohomology sheaves into a closed formula once the complex
computing them has been shown to have zero differential.

## Main definitions

* `Stacks.HomologicalComplex.homologyIsoX`: the identification of the homology in a degree with
  the term in that degree, for a complex whose two adjacent differentials vanish.
* `Stacks.CochainComplex.intHomologyIsoX`: the same for a `ℤ`-indexed cochain complex with
  vanishing differentials, where the two hypotheses collapse into one.

## Implementation notes

The homology data used is `CategoryTheory.ShortComplex.LeftHomologyData.ofZeros`, whose
underlying object is the middle term of the short complex on the nose; the identification of the
homology of the complex with the homology of that short complex is
`HomologicalComplex.homologyIsoSc'`. The hypothesis that the short complex has homology is
obtained by substituting the two descriptions of the neighbouring degrees, which is why those are
taken as equations rather than as the values of `ComplexShape.prev` and `ComplexShape.next`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.HomologicalComplex

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {c : ComplexShape ι}

/-- **The homology of a complex in a degree whose two adjacent differentials vanish is the term
in that degree.** -/
noncomputable def homologyIsoX (K : _root_.HomologicalComplex C c) (i j k : ι)
    (hi : c.prev j = i) (hk : c.next j = k) (h₁ : K.d i j = 0) (h₂ : K.d j k = 0)
    [K.HasHomology j] : K.homology j ≅ K.X j :=
  have : (K.sc' i j k).HasHomology := by subst hi hk; assumption
  K.homologyIsoSc' i j k hi hk ≪≫
    (ShortComplex.LeftHomologyData.ofZeros (K.sc' i j k) h₁ h₂).homologyIso

end Stacks.HomologicalComplex

namespace Stacks.CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- **The cohomology of a `ℤ`-indexed cochain complex with vanishing differentials is the term**,
in every degree. The two hypotheses of
`Stacks.HomologicalComplex.homologyIsoX` collapse into one here, because the differential out of
the previous degree is the differential into the given one. -/
noncomputable def intHomologyIsoX (K : _root_.CochainComplex C ℤ)
    (hd : ∀ n : ℤ, K.d n (n + 1) = 0) (n : ℤ) [K.HasHomology n] :
    K.homology n ≅ K.X n :=
  Stacks.HomologicalComplex.homologyIsoX K (n - 1) n (n + 1) (by simp) (by simp)
    (by
      have h := hd (n - 1)
      rwa [show n - 1 + 1 = n from by omega] at h) (hd n)

end Stacks.CochainComplex

end
