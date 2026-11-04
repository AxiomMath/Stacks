module

public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairDerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Homology.PseudoCoherent.Characterization
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence of an object of `D_QCoh(𝒪_X)` and of its derived sections

Let `X` be a scheme and let `E` be an object of the derived category of `𝒪_X`-modules all of
whose cohomology sheaves are quasi-coherent. Then `E` is a pseudo-coherent object of `D(𝒪_X)`,
in the sense of Stacks 08CB, exactly when the complex of `Γ(X, U)`-modules `RΓ(U, E)` is
pseudo-coherent for every affine open `U` of `X`, and it is enough to test this on an affine
open covering.

This is the first of the two clauses of relative perfectness, Stacks 0DI0, in the three
equivalent forms of Stacks 0DI2.

## Main results

* `AlgebraicGeometry.isPseudoCoherent_derivedRestrictModules_iff_derivedSections`: on an affine
  open `U`, pseudo-coherence of `E|_U` is pseudo-coherence of the complex of `Γ(X, U)`-modules
  `RΓ(U, E)`.
* `AlgebraicGeometry.pseudoCoherent_derivedSections_tfae`: the pseudo-coherence clause of
  Stacks 0DI2, in its three equivalent forms.

## Implementation notes

The two clauses of relative perfectness (Stacks 0DI0) are independent conditions, and the proof
of Stacks 0DI2 is their separate affine-locality statements: pseudo-coherence is local by
Stacks 08CC, and on an affine open it crosses to the module side by Stacks 08E7 and the
presentation of `E|_U` by `RΓ(U, E)` which is the remaining content of Stacks 06Z0. That
presentation is `AlgebraicGeometry.affineDerivedSectionsPresentation`, and the crossing of
Stacks 08E7 on a derived object is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_mapDerivedCategory_tilde_iff`. Only the
pseudo-coherence clause is treated here.

**The two spellings of restriction to an open.** Pseudo-coherence on a ringed space is phrased
through `AlgebraicGeometry.RingedSpace.restrictModules`, while the presentation of `E|_U` is
stated for Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctor` along `U.ι`. The two
induce the same functor on derived categories, by
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`.

**The Tor-dimension clause.** The second clause of Stacks 0DI0 is
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension`, part (3) of Stacks 08CG, on the
inverse-image ringed space `(X, f⁻¹𝒪_S)`. Its affine-locality statements, and the whole of
Stacks 0DI2, are in `StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectAffineCriterion.lean`
(`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae`).

## References

* [The Stacks Project, Lemma 36.35.3 (0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [The Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [The Stacks Project, Lemma 36.10.2 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}}

/-- **Stacks 08E7 and Stacks 06Z0 on an affine open.** Let `E` be an object of the derived
category of `𝒪_X`-modules with quasi-coherent cohomology sheaves and let `U` be an affine open
of `X`. Then `E|_U` is `m`-pseudo-coherent exactly when the complex of `Γ(X, U)`-modules
`RΓ(U, E)` is.

The restriction `E|_U` is the sheaf attached to `RΓ(U, E)`, transported from `Spec Γ(X, U)` along
`AlgebraicGeometry.IsAffineOpen.isoSpec`; pseudo-coherence is unchanged by that transport and
crosses to the module side by Stacks 08E7. -/
public theorem isPseudoCoherentFrom_derivedRestrictModules_iff_derivedSections
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {U : X.Opens} (hU : IsAffineOpen U) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom
        ((RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((derivedSectionsUnbounded X U).obj E) m := by
  obtain ⟨K, ⟨e₁⟩, ⟨e₂⟩⟩ := affineDerivedSectionsPresentation E hE U hU
  have e₀ : (RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E ≅
      (Scheme.Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.obj
        ((tilde.functor Γ(X, U)).mapDerivedCategory.obj K) :=
    (RingedSpace.derivedRestrictModulesIsoRestrictFunctor X U).app E ≪≫ e₁
  refine Iff.trans ⟨fun h => h.of_iso e₀, fun h => h.of_iso e₀.symm⟩ ?_
  refine Iff.trans (Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff
    hU.isoSpec.inv _ m) ?_
  refine Iff.trans (RingedSpace.isPseudoCoherentFrom_mapDerivedCategory_tilde_iff K m) ?_
  exact ⟨fun h => h.ofIso e₂, fun h => h.ofIso e₂.symm⟩

/-- Pseudo-coherence of `E|_U` is `m`-pseudo-coherence for every `m`. -/
private theorem isPseudoCoherent_derivedRestrictModules_iff_forall
    (E : DerivedCategory X.Modules) (U : X.Opens) :
    RingedSpace.IsPseudoCoherent
        ((RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) ↔
      ∀ m, RingedSpace.IsPseudoCoherentFrom
        ((RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) m :=
  RingedSpace.isPseudoCoherent_iff_forall (X := X.toRingedSpace.restrict U.isOpenEmbedding) _

/-- **Stacks 08E7 and Stacks 06Z0 on an affine open, in all degrees at once.** On an affine open
`U` of `X`, the restriction `E|_U` of an object with quasi-coherent cohomology sheaves is
pseudo-coherent exactly when the complex of `Γ(X, U)`-modules `RΓ(U, E)` is.

Both sides are `m`-pseudo-coherence in every degree, on the sheaf side by Stacks 08CC part (2)
and on the module side by Stacks 064W. -/
public theorem isPseudoCoherent_derivedRestrictModules_iff_derivedSections
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {U : X.Opens} (hU : IsAffineOpen U) :
    RingedSpace.IsPseudoCoherent
        ((RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedSectionsUnbounded X U).obj E) := by
  exact (isPseudoCoherent_derivedRestrictModules_iff_forall E U).trans <|
    Iff.trans
    (forall_congr' fun m =>
      isPseudoCoherentFrom_derivedRestrictModules_iff_derivedSections E hE hU m)
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all
      ((derivedSectionsUnbounded X U).obj E)).symm

/-- **Stacks 0DI2, the pseudo-coherence clause.** Let `f : X ⟶ S` be a morphism of schemes and
let `E` be an object of the derived category of `𝒪_X`-modules all of whose cohomology sheaves are
quasi-coherent. Then the following are equivalent:

1. `E` is a pseudo-coherent object of `D(𝒪_X)`;
2. for every affine open `U ⊆ X` whose image lies in an affine open `V ⊆ S`, the complex of
   `Γ(X, U)`-modules `RΓ(U, E)` is pseudo-coherent;
3. there are an affine open covering of `S` and, over each of its members `V i`, an affine open
   covering of `f ⁻¹ᵁ V i` such that `RΓ(U, E)` is pseudo-coherent for each member `U` of the
   latter.

This is the first of the two clauses of relative perfectness, with the part of the source's
proof that concerns it: pseudo-coherence of `E` is the pseudo-coherence over `Γ(X, U)` of
`RΓ(U, E)`, by Stacks 08E7 and the affine presentation of `E|_U` of Stacks 06Z0, and the
condition is local on `X`. Together with the second clause, locally finite Tor dimension over
`f^{-1}𝒪_S`, this is assembled into Stacks 0DI2 in
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae`. -/
@[stacks 0DI2 "the pseudo-coherence clause"]
public theorem pseudoCoherent_derivedSections_tfae (f : X ⟶ S)
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    List.TFAE
      [RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E,
        ∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V → U ≤ f ⁻¹ᵁ V →
          StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedSectionsUnbounded X U).obj E),
        ∃ (ι : Type u) (V : ι → S.affineOpens),
          (⨆ i, (V i : S.Opens)) = ⊤ ∧
            ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens),
              (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
                ∀ j, StacksDraft.PseudoCoherence.IsPseudoCoherent
                  ((derivedSectionsUnbounded X (U j).1).obj E)] := by
  tfae_have 1 → 2 := by
    intro h U hU _V _hV _e
    refine (isPseudoCoherent_derivedRestrictModules_iff_derivedSections E hE hU).1
      ((isPseudoCoherent_derivedRestrictModules_iff_forall E U).2 fun m => ?_)
    exact RingedSpace.isPseudoCoherentFrom_derivedRestrictModules E m
      ((RingedSpace.isPseudoCoherent_iff_forall (X := X.toRingedSpace) E).1 h m) U
  tfae_have 2 → 3 := by
    intro h
    refine ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V => ?_⟩
    exact ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)}, fun U => U.1,
      iSup_affineOpens_subtype_eq _, fun U => h _ U.1.2 _ V.2 U.2⟩
  tfae_have 3 → 1 := by
    rintro ⟨ι, V, hVtop, hcov⟩
    refine (RingedSpace.isPseudoCoherent_iff_forall (X := X.toRingedSpace) E).2 fun m =>
      RingedSpace.isPseudoCoherentFrom_of_local_restrict E m fun x => ?_
    have hx : f.base x ∈ (⨆ i, (V i : S.Opens)) := by rw [hVtop]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨κ, U, hUtop, hU⟩ := hcov i
    have hx' : x ∈ (⨆ j, (U j : X.Opens)) := by rw [hUtop]; exact hi
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx'
    refine ⟨(U j).1, hj, (isPseudoCoherent_derivedRestrictModules_iff_forall E (U j).1).1 ?_ m⟩
    exact (isPseudoCoherent_derivedRestrictModules_iff_derivedSections E hE (U j).2).2 (hU j)
  tfae_finish

end AlgebraicGeometry

end
