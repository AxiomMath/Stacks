module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentPerfectDual
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaQuasiCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Equation 48.8.0.1 is an isomorphism for a perfect complex

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y`
quasi-compact, and let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For
`K, L ∈ D_QCoh(𝒪_Y)` with `K` perfect the comparison map `Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)`
of [Stacks, Tag 0A9S] is an isomorphism, and so is Equation 48.8.0.1,
`Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)` ([Stacks, Tag 0A9T]).

The source's Yoneda argument uses the dual `K^∨` of `K`. Here `K^∨` is
`Stacks.Duality.perfectDual`, a left dual of `K` in the monoidal category `D_QCoh(𝒪_Y)`
(`Stacks.Duality.exactPairingPerfectDual`), and the argument is
`Stacks.Duality.isIso_compareWithPullbackTensor_of_exactPairing`: at a dualizable `K` the
comparison map of the monoidal adjunction `Lf^* ⊣ Rf_*`, whose projection maps are invertible
([Stacks, Tag 08EU]), is invertible.

## Main results

* `Stacks.Duality.isIso_compareWithPullbackTensor_and_compareWithPullback_of_isPerfect`:
  [Stacks, Tag 0A9T].

## References

* [Stacks Project, Tag 0A9T](https://stacks.math.columbia.edu/tag/0A9T)
* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⊣
    a)

/-- **[Stacks, Tag 0A9T] (Lemma 48.8.1).** Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of schemes with `Y` quasi-compact (for instance a morphism of
quasi-compact and quasi-separated schemes), and let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. If `K ∈ D_QCoh(𝒪_Y)` is perfect, then

* the map `Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)` of [Stacks, Tag 0A9S] is an isomorphism for
  every `L ∈ D_QCoh(𝒪_Y)`, and
* in particular Equation 48.8.0.1, `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`, is an isomorphism, for any
  identification `ρ` of `- ⊗ᴸ 𝒪_Y` with the identity (such as the right unitor). -/
@[stacks 0A9T]
theorem isIso_compareWithPullbackTensor_and_compareWithPullback_of_isPerfect
    {K : quasiCoherentDerivedCategory Y}
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) K.obj) :
    (∀ L : quasiCoherentDerivedCategory Y,
      IsIso (compareWithPullbackTensor f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom adj K L)) ∧
    ∀ ρ : (quasiCoherentDerivedTensor Y).flip.obj (DerivedPushforward.derivedStructureSheaf Y) ≅
        𝟭 _,
      IsIso (compareWithPullback f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom adj ρ K) := by
  let := exactPairingPerfectDual K hK
  have h : ∀ L : quasiCoherentDerivedCategory Y,
      IsIso (compareWithPullbackTensor f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom adj K L) := fun L =>
    isIso_compareWithPullbackTensor_of_exactPairing f _ _
      (quasiCoherentDerivedPullbackTensorIso_hom_app f) adj K (perfectDual K hK) L
  refine ⟨h, fun ρ => ?_⟩
  have h₁ := h (DerivedPushforward.derivedStructureSheaf Y)
  change IsIso (compareWithPullbackTensor f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (quasiCoherentDerivedPullbackTensorIso f).hom adj K
      (DerivedPushforward.derivedStructureSheaf Y) ≫
    a.map (ρ.hom.app K))
  infer_instance

end Stacks.Duality

end
