module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModulesSmall

/-!
# Quasi-coherent modules on an algebraic stack and on a pointwise groupoid presentation

Let `𝒳` be an algebraic stack and `(U, R, s, t, c)` the flat groupoid presentation of Stacks 04T5
(`AlgebraicGeometry.Stack.flatGroupoidPresentation`), with its fully faithful 1-morphism
`F : [U/_pR] ⥤ 𝒳` from the pointwise groupoid fibration covering `𝒳` by images.  The inverse image
along `F` is an equivalence `QCoh(𝒪_𝒳) ≌ QCoh(𝒪_{[U/_pR]})` of the categories of quasi-coherent
modules with sections in `Type u`.  This is the first step of the proof of Stacks 06WV (1) — the
reduction "`QCoh(𝒪_𝒳) ≅ QCoh(𝒪_{[U/R]})`" of the source, read on the pointwise presentation —
and is not itself a numbered result, so nothing here carries a `stacks` attribute.

## Main definitions

* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.quasicoherentPullback`: the inverse image
  `QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_{[U/_pR]})`.
* `AlgebraicGeometry.Stack.FlatGroupoidPresentation.quasicoherentEquivalence`: it is an
  equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack.FlatGroupoidPresentation

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- The inverse image of quasi-coherent modules along the 1-morphism of a flat groupoid
presentation, from `QCoh(𝒪_𝒳)` to the quasi-coherent modules on the pointwise groupoid
fibration. -/
abbrev quasicoherentPullback (P : FlatGroupoidPresentation 𝒳) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
        (presheafOfGroupoids (evaluationGroupoidFunctor P.G.toGroupoidInFunctors)).p
        (isFiberedInGroupoids_presheafOfGroupoids _) :=
  quasicoherentPullback'.{u, u + 1, u, u, u + 1, u} B S hS
    (presheafOfGroupoids (evaluationGroupoidFunctor P.G.toGroupoidInFunctors)).p
    𝒳.val.val.p (isFiberedInGroupoids_presheafOfGroupoids _) 𝒳.val.isFiberedInGroupoids P.F P.hF

/-- **The quasi-coherent modules on an algebraic stack are those on the pointwise groupoid
fibration of a flat groupoid presentation.** -/
theorem isEquivalence_quasicoherentPullback (P : FlatGroupoidPresentation 𝒳) :
    P.quasicoherentPullback.IsEquivalence := by
  have := P.full
  have := P.faithful
  exact isEquivalence_quasicoherentPullback'_of_full_of_faithful.{u, u + 1, u, u, u + 1, u}
    B S hS _ _ _ _ P.F P.hF P.hloc

/-- The equivalence `QCoh(𝒪_𝒳) ≌ QCoh(𝒪_{[U/_pR]})` of a flat groupoid presentation. -/
def quasicoherentEquivalence (P : FlatGroupoidPresentation 𝒳) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids ≌
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
        (presheafOfGroupoids (evaluationGroupoidFunctor P.G.toGroupoidInFunctors)).p
        (isFiberedInGroupoids_presheafOfGroupoids _) :=
  haveI := P.isEquivalence_quasicoherentPullback
  P.quasicoherentPullback.asEquivalence

end AlgebraicGeometry.Stack.FlatGroupoidPresentation

end
