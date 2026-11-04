module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsPushforwardPoint
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoFieldSupplement

/-!
# Further results on `ProperOverFieldDuality`

Results about the objects of `StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality` that
need imports beyond those of that module.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-! ### Instances over the base field

`CommRingCat.of k` does not reduce during instance search the way a variable `R : CommRingCat`
does, so the instances below are obtained at a variable and then applied. -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [QuasiCompact f] [QuasiSeparated f]

/-- **Part (1) of [Stacks, Tag 08D5] over a field**: derived direct image along a quasi-compact
quasi-separated morphism to `Spec k` preserves quasi-coherence of the cohomology sheaves. This is
the hypothesis `hpush` of `Stacks.Duality.quasiCoherentDerivedPushforward`, discharged. -/
abbrev isQuasicoherentPushforwardOverField :
    ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent :=
  isQuasicoherent_homology_derivedPushforward_of_qcqs f

end Stacks.Duality

end
