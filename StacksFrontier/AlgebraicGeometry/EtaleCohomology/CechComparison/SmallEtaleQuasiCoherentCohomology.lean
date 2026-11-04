module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zariski and small étale cohomology of a quasi-coherent module agree

Let `S` be a scheme and `F` a quasi-coherent `𝒪_S`-module, and let `Fᵃ` be the associated module
read as an abelian sheaf on the small étale site of `S`. Then

  `H^p(V, ℱ) ≅ H^p(V_étale, Fᵃ)`

for every open `V` of `S` and every degree `p`, and in particular, at `V = ⊤`,

  `H^p(S, ℱ) ≅ H^p(S_étale, Fᵃ)`.

## Main definitions

* `AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIso`: the isomorphism over an arbitrary
  open of `S`.
* `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`: the same over the whole
  scheme.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- For a quasi-coherent module `F` on `S`, an open `V` of `S` and a degree `p`,

  `H^p(V, ℱ) ≅ H^p(V_étale, Fᵃ)`,

where the right-hand side is the cohomology on the small étale site of `S` of the associated
module `Fᵃ`, taken over the object `V.ι : V ⟶ S`. -/
@[sga "4 VII 4.3" "more general"]
public def smallEtaleQuasiCoherentCohomologyIso (p : ℕ) (V : S.Opens) :
    Sheaf.H' ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p V ≅
      Sheaf.H' (smallEtaleAssociatedSheaf S F) p ((opensToEtale S).obj V) :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology S) p).mapIso
      (smallEtaleSectionsUnitIso S F)).app (op V) ≪≫
    Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
      (Opens.grothendieckTopology S) (Scheme.smallEtaleTopology S) (opensToEtale S)
      (smallEtaleAssociatedSheaf S F) V p
      (fun q hq _ ↦ isZero_rightDerived_pushforward_opensToEtale S F q hq)

/-- For a quasi-coherent module `F` on a scheme `S` and a degree `p`, Zariski cohomology of `F`
agrees with small étale cohomology of its associated module:

  `H^p(S, ℱ) ≅ H^p(S_étale, Fᵃ)`.

The right-hand side is taken over `(opensToEtale S).obj ⊤`, a final object of the small étale
site, so it is étale cohomology of `S` itself. -/
@[stacks 03P2 "the case 𝒞 = S_étale.  The object the right-hand side is taken over, \
(opensToEtale S).obj ⊤, is a final object of the small étale site, so that side is étale \
cohomology of S itself.  The case 𝒞 = (Sch/S)_τ, for all five τ at once, is \
bigOverQuasiCoherentGlobalCohomologyIso",
  stacks 03DW "clause (2), the small étale half, in EVERY degree q — the same statement as \
Tag 03P2 at 𝒞 = S_étale, Descent Proposition 35.9.3 and Étale Cohomology Theorem 59.22.4 \
being the same assertion in two chapters.  In particular this is the POSITIVE-DEGREE case, \
which the q = 0 carrier BigFppfOver.hZeroBaseAssociatedModuleAddEquiv does not claim; the \
affine vanishing H^p(U, Fᵃ) = 0 that the source's proof passes through is \
isZero_sheafCohomology_succ_smallEtaleAffine.  NOT covered here: the small ZARISKI half of \
clause (2), which is smallZariskiQuasiCoherentGlobalCohomologyIso; clause (1) is \
bigOverQuasiCoherentGlobalCohomologyIso", sga "4 VII 4.3"]
public def smallEtaleQuasiCoherentGlobalCohomologyIso (p : ℕ) :
    Sheaf.H' ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ⊤ ≅
      Sheaf.H' (smallEtaleAssociatedSheaf S F) p ((opensToEtale S).obj ⊤) :=
  smallEtaleQuasiCoherentCohomologyIso S F p ⊤

end AlgebraicGeometry

end
