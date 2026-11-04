module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveNoetherian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveNoetherianReduction
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0GKV]: `Rᵠ f_* 𝐙/ℓ` for a proper smooth family of curves is constructible

Let `f : X ⟶ S` be a proper smooth morphism of schemes with geometrically connected fibres of
dimension at most one, and let `ℓ` be a prime number. Then for every `q` the higher direct image
`Rᵠ f_* 𝐙/ℓ` is a constructible sheaf of `𝔽_ℓ`-modules on `S_étale`.

The proof is the source's, in two steps:

* **Reduction to a Noetherian base** (first paragraph of the source's proof):
  `isConstructibleEtaleModule_rightDerivedConstantUnit_of_forall_isNoetherian`
  — Zariski localization, absolute Noetherian approximation ([Stacks, Tags 01ZM, 081F, 0C0C,
  0EY2]), the open locus of geometrically connected fibres ([Stacks, Tag 0E0N]) and proper base
  change ([Stacks, Tag 095T]).
* **The Noetherian case** (second paragraph and cases (a), (b)):
  `isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian`
  — the splitting `S = D(ℓ) ∪ V(ℓ)`, case (a) by [Stacks, Tags 0DDF, 03SC, 0GKD, 0GKC] and case (b)
  by the Artin–Schreier sequence ([Stacks, Tags 0A3H, 0A3J, 0GKA, 0GKU]).

## Main results

* `isConstructibleEtaleModule_rightDerivedConstantUnit_of_isProper_of_smooth`:
  [Stacks, Tag 0GKV].

## Implementation notes

The family is a morphism `f : X ⟶ S` of schemes of a big étale site `B` (any `B` containing `X` and
`S`), constructibility being defined on the small étale site of [Stacks, Tag 021B]
(`Stacks.EtaleCohomology.IsBigSiteConstructibleEtaleModule`). The coefficient sheaf is the constant
sheaf of `𝔽_ℓ`-modules `𝐙/ℓ𝐙`, and `Rᵠ f_*` is the right derived functor of direct image on sheaves
of `𝔽_ℓ`-modules (`Stacks.EtaleCohomology.rightDerivedConstantUnit`); its underlying abelian sheaf
is the higher direct image of the constant abelian sheaf
(`Stacks.EtaleCohomology.rightDerivedConstantUnitForgetIso`). The source asks for fibres of
dimension `1`; the statement below allows dimension at most one, which is more general.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Tag 0GKV.** Let `f : X ⟶ S` be a proper smooth morphism of schemes with
geometrically connected fibres of dimension at most `1` (the source: of dimension `1`), and let
`ℓ` be a prime number. Then `Rᵠ f_* 𝐙/ℓ𝐙` is a constructible sheaf of `𝔽_ℓ`-modules on `S_étale`
for every `q`.

The base `S` is arbitrary: the source's absolute Noetherian approximation
(`isConstructibleEtaleModule_rightDerivedConstantUnit_of_forall_isNoetherian`) reduces to a
Noetherian base, where the statement is
`isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian` (both cases `ℓ` invertible
and `ℓ = 0` on `S`). -/
@[stacks 0GKV, sga "4 XIV 1.11" "partial"]
theorem isConstructibleEtaleModule_rightDerivedConstantUnit_of_isProper_of_smooth
    (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
    [GeometricallyConnected f] (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ) :
    IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)) :=
  isConstructibleEtaleModule_rightDerivedConstantUnit_of_forall_isNoetherian B f hdim ℓ q
    fun X' S' f' _ _ _ hdim' hN => by
      have := hN
      exact isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian B f' hdim' ℓ q

end Stacks.EtaleCohomology

end
