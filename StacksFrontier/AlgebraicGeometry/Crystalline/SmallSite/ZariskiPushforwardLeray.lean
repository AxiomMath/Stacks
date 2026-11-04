module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverTriangle

/-!
# The Leray factorization of [Stacks, Tag 015M] for `f_{Zar}`

Let `f : X' ⟶ X` be the morphism of schemes underlying a morphism of the global crystalline
situations of [Stacks, Tag 07I5].  `SmallSite/AlphaPCoverTriangle.lean` builds the abelian
direct image `f_{Zar, *} : Ab(X'_Zar) ⥤ Ab(X_Zar)` along the induced map of small Zariski sites,
shows that it preserves injective abelian sheaves, and records the underived identity
`Γ(X, f_{Zar, *}G) = Γ(X', G)`.  This file turns those two into the factorization

`RΓ(X'_Zar, -) ≅ Rf_{Zar, *} ⋙ RΓ(X_Zar, -)`,

which is [Stacks, Tag 015M] for `f_{Zar}`, the Zariski-side companion of
`GlobalCrystallineSituation.SmallSite.derivedGlobalSectionsIsoDerivedZariskiDirectImage` (the
same statement for `u_{X/S}`) and of
`GlobalCrystallineSituation.SmallSite.derivedCrisGlobalSectionsIso` (for `f_cris`).

As everywhere in this chapter the orientation is that `S` is the *source* situation `X'/S` and
`S'` the *target* situation `X/S`, so `fX : S.X ⟶ S'.X` is `f : X' ⟶ X`.

## Main definitions

* `zariskiPushforwardGlobalSectionsIso` — the underived `Γ(X_Zar, f_{Zar, *} -) ≅ Γ(X'_Zar, -)`.
  Both global sections functors are Mathlib's `CategoryTheory.Sheaf.Γ`, the right adjoint of the
  constant sheaf functor; on a site with a terminal object that is the sections functor at the
  terminal object (`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), the terminal open is `⊤`, and
  `f^{-1}(⊤) = ⊤` definitionally, so the comparison is the identity read through those two
  identifications.
* `derivedZariskiGlobalSectionsIsoPushforward` — **[Stacks, Tag 015M] for `f_{Zar}`**:
  `RΓ(X'_Zar, -) ≅ Rf_{Zar, *} ⋙ RΓ(X_Zar, -)`.

Both are unconditional: the two inputs, preservation of injectives and the underived comparison,
are theorems of `SmallSite/AlphaPCoverTriangle.lean`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fX : S.X ⟶ S'.X)

/-- **`Γ(X_Zar, f_{Zar, *}G) ≅ Γ(X'_Zar, G)`**, naturally in the abelian sheaf `G` on `X'_Zar`.

Global sections on a site with a terminal object are sections at that object,
`CategoryTheory.Sheaf.ΓNatIsoSheafSections`; the terminal open of a scheme is `⊤`; and the
sections of `f_{Zar, *}G` over `⊤` are the sections of `G` over `f^{-1}(⊤) = ⊤`, which is the
definitional identity `zariskiPushforward_comp_topSections`.  So the comparison is the identity
read through the two identifications, and in particular it is the canonical map. -/
def zariskiPushforwardGlobalSectionsIso :
    zariskiPushforward S S' fX ⋙ zariskiGlobalSections S' ≅ zariskiGlobalSections S :=
  Functor.isoWhiskerLeft (zariskiPushforward S S' fX)
      (Sheaf.ΓNatIsoSheafSections (opensTopology S') AddCommGrpCat.{u + 1}
        (isTerminalTop (α := S'.X.Opens))) ≪≫
    (Sheaf.ΓNatIsoSheafSections (opensTopology S) AddCommGrpCat.{u + 1}
      (isTerminalTop (α := S.X.Opens))).symm

section Derived

variable [HasDerivedCategory.{w} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **[Stacks, Tag 015M] for `f_{Zar}`: `RΓ(X'_Zar, -) ≅ Rf_{Zar, *} ⋙ RΓ(X_Zar, -)`.**

The two inputs are theorems of `SmallSite/AlphaPCoverTriangle.lean`:
`preservesInjectiveObjects_zariskiPushforward`, which makes the comparison transformation of
[Stacks, Tag 05T2] invertible, and the underived
`zariskiPushforwardGlobalSectionsIso`, which identifies the functor being derived.
Unconditional. -/
def derivedZariskiGlobalSectionsIsoPushforward :
    derivedZariskiGlobalSectionsFunctor S ≅
      derivedZariskiPushforwardFunctor S S' fX ⋙ derivedZariskiGlobalSectionsFunctor S' :=
  (Functor.rightDerivedFunctorPlusNatIso
      (zariskiPushforwardGlobalSectionsIso S S' fX)).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIso (zariskiPushforward S S' fX)
      (zariskiGlobalSections S')

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
