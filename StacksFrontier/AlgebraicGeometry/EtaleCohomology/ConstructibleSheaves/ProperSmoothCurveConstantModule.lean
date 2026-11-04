module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveHigherDirectImage
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0GKW]: `Rᵠ f_* M` for a proper smooth family of curves is constructible

Let `f : X ⟶ S` be a proper smooth morphism of schemes with geometrically connected fibres of
dimension at most one, let `Λ` be a Noetherian ring and let `M` be a finite `Λ`-module annihilated
by an integer `n > 0`. Then for every `q` the higher direct image `Rᵠ f_* M` of the constant sheaf
is a constructible sheaf of `Λ`-modules on `S_étale`.

The proof is the source's:

* reduction to `M` annihilated by a prime `ℓ` (long exact sequence of `0 → M[ℓ] → M → M/M[ℓ] → 0`
  and the weak Serre property of constructible sheaves, [Stacks, Tag 03RZ]),
* replacing `Λ` by `Λ/ℓΛ` ([Stacks, Tag 0D6J]) and `M` by the rank one free modules over the
  quotients `(Λ/ℓΛ)/𝔭` (a filtration of the finite module `M`),
* `Rᵠ f_* A = Rᵠ f_* 𝐙/ℓ ⊗_{𝐙/ℓ} A` for an `𝔽_ℓ`-algebra `A` (the case of [Stacks, Tag 0F0G]
  that the source uses, proved by choosing an `𝔽_ℓ`-basis of `A`) and extension of scalars
  preserving constructibility ([Stacks, Tag 0GKB]);

all collected in `isConstructibleEtaleModule_rightDerived_constantSheaf_of_zmod`, whose input —
`Rᵠ f_* 𝐙/ℓ` constructible for every prime `ℓ` — is [Stacks, Tag 0GKV]
(`isConstructibleEtaleModule_rightDerivedConstantUnit_of_isProper_of_smooth`).

## Main results

* `isConstructibleEtaleModule_rightDerived_constantSheaf_of_isProper_of_smooth`:
  [Stacks, Tag 0GKW].

## Implementation notes

As in [Stacks, Tag 0GKV], the family is a morphism `f : X ⟶ S` between schemes of a big étale
site `B` (constructibility being defined on the small étale site of [Stacks, Tag 021B]), and
`Rᵠ f_*` is the right derived functor of the direct image on sheaves of `Λ`-modules on Mathlib's
small étale sites. The source asks for fibres of dimension `1`; the statement below allows
dimension at most one, which is more general.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Tag 0GKW.** Let `f : X ⟶ S` be a proper smooth morphism of schemes with
geometrically connected fibres of dimension at most `1` (the source: of dimension `1`), let `Λ`
be a Noetherian ring and let `M` be a finite `Λ`-module annihilated by an integer `n > 0`. Then
`Rᵠ f_* M` is a constructible sheaf of `Λ`-modules on `S_étale` for every `q`. -/
@[stacks 0GKW]
theorem isConstructibleEtaleModule_rightDerived_constantSheaf_of_isProper_of_smooth
    (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
    [GeometricallyConnected f] (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1)
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (M : ModuleCat.{u + 1} Λ)
    (hM : Module.Finite Λ M) (n : ℕ) (hn : 0 < n) (hnM : ∀ m : M, n • m = 0) (q : ℕ) :
    IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have : QuasiCompact f := instQuasiCompactOfUniversallyClosed f
  have : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  exact isConstructibleEtaleModule_rightDerived_constantSheaf_of_zmod B f Λ
    (fun ℓ hℓ q =>
      have : Fact ℓ.Prime := ⟨hℓ⟩
      isConstructibleEtaleModule_rightDerivedConstantUnit_of_isProper_of_smooth B f hdim ℓ q)
    n hn M hM hnM q

end Stacks.EtaleCohomology

end
