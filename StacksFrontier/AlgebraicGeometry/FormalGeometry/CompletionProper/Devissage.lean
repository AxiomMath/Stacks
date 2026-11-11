module

public import Mathlib.Order.OrderIsoNat
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksCore.Tactic.StacksAttribute

/-!
# Grothendieck's existence theorem for a proper morphism, by dévissage

**Stacks 088C.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, let
`f : X ⟶ Spec A` be a *proper* morphism and put `𝓘 = I · 𝒪_X`. Then the completion functor of
Stacks 0880

  `Coh(𝒪_X) ⥤ Coh(X, 𝓘)`,  `F ↦ (F / 𝓘ⁿ F)`

is an equivalence.

The source proves this in two halves. Full faithfulness is Stacks 0883, which holds for any
proper morphism. Essential surjectivity is a **Noetherian induction over the quasi-coherent
ideal sheaves of `X`**: one considers the family

  `Ξ = { K ⊆ 𝒪_X quasi-coherent ideal sheaf : every object of Coh(X, 𝓘) killed by K is
         in the essential image }`,

observes that `Ξ` is an up-set, and argues that if `⊥ ∉ Ξ` then — `X` being Noetherian — there is
a `K` maximal among the ideal sheaves outside `Ξ`, so that every strictly larger ideal sheaf lies
in `Ξ`, and derives a contradiction by proving `K ∈ Ξ`. Since every object of `Coh(X, 𝓘)` is
killed by `⊥`, the conclusion `⊥ ∈ Ξ` is exactly essential surjectivity.

**This file carries the induction and leaves the single inductive step as a named hypothesis.**
The two pieces the induction rests on are proved here with no hypotheses at all:

* the quasi-coherent ideal sheaves of a Noetherian scheme satisfy the ascending chain condition,
  `AlgebraicGeometry.Scheme.IdealSheafData.wellFoundedGT_of_isNoetherian`, which is what makes
  the well-founded induction legitimate (the source cites Stacks 01Y8 for it; the proof below is
  the affine-local one, from a finite affine cover and the Noetherianity of its coordinate
  rings), and
* every object of `Coh(X, 𝓘)` is killed by the zero ideal sheaf,
  `Stacks.Algebraization.isSystemAnnihilatedBy_bot`, which is what makes `⊥ ∈ Ξ` the whole of
  essential surjectivity.

The declaration `isEquivalence_completionFunctor_of_devissage` takes the source's inductive step
as the binder `hDev`, and `hFF`, the theorem on formal functions in degree zero that Stacks 0883
uses, as a second binder. Both are discharged in
`CompletionProper/GrothendieckExistenceProper.lean`: `hFF` by
`Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper` and `hDev` by
`Stacks.Coherent.essImage_completionFunctor_of_devissageStep`, which follows the source's step
through Chow's lemma (Stacks 0200), Stacks 087T, the projective case Stacks 0885, the coherence of
a proper direct image (Stacks 02O5) and Stacks 088A, 088B. The resulting statement, with exactly
the source's hypotheses, is `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper`,
which carries the tag 088C.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.wellFoundedGT_of_isNoetherian` — the quasi-coherent
  ideal sheaves of a Noetherian scheme have no infinite strictly ascending chain. Unconditional.
* `Stacks.Algebraization.IsSystemAnnihilatedBy` — an inverse system of sheaves of modules killed
  by a quasi-coherent ideal sheaf, and `Stacks.Algebraization.isSystemAnnihilatedBy_bot`: the
  zero ideal sheaf kills every system. Unconditional.
* `Stacks.Algebraization.essImage_completionFunctor_of_devissage` — the Noetherian induction:
  given the inductive step, every object of `Coh(X, 𝓘)` killed by any ideal sheaf is in the
  essential image of the completion functor. Unconditional.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage` — the completion functor
  of a proper morphism is an equivalence once `hFF` and the inductive step `hDev` are supplied;
  `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper` supplies both.

## Implementation notes

The ascending chain condition is proved from the monotone chain condition
(`wellFoundedGT_iff_monotone_chain_condition`): a monotone sequence of ideal sheaves is tested on
a finite affine cover, where each component chain lives in a Noetherian ring and therefore
stabilizes (`monotone_stabilizes_iff_noetherian`), and the finitely many stabilization indices
have a maximum; two ideal sheaves agreeing on an affine cover are equal, by
`AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top`. The finite affine cover is
`X.affineCover.finiteSubcover`, as in
`StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/AscendingChain.lean`.

Annihilation is `Stacks.Algebraization.idealPowerMultiple K 1 _ = ⊥`, that is `K · F_n = 0`, and
*not* annihilation by a power of `K`. The distinction matters: the family defined by annihilation
by a power of `K` is not the source's `Ξ`, and the inductive step for it would be a strictly
stronger obligation, since a power `(K')^t` of an ideal sheaf strictly larger than `K` need not
itself be strictly larger than `K`.

`hDev` is the source's step verbatim. It should not be called *logically* weaker than the
generation hypothesis `hGen` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_exists_epi`: granted `hFF`, each of the
two is equivalent to the conclusion, since an essentially surjective functor trivially satisfies
both. The difference is in the shape of the obligation, and that is the whole point. `hGen` asks
for an epimorphism onto *every* object of `Coh(X, 𝓘)` from the image of the functor with nothing
granted, and is not a step of the source's proof for a proper morphism at all — the source
establishes it only in the projective case, through Stacks 0884. `hDev` is to be discharged one
ideal sheaf at a time with the statement already available on every strictly larger ideal sheaf,
which is exactly the position the source is in when it applies Chow's lemma, 088A and 088B.

No statement here mentions `AlgebraicGeometry.Scheme.Modules` in the geometric vocabulary of the
tag: the categories are written as
`AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf` and
`Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f)`, which is what the completion
functor of Stacks 0880 is declared between. The annihilation predicate is stated for a diagram
`ℕᵒᵖ ⥤ X.Modules`, which is the type of `𝓕.obj` for an object `𝓕` of
`Stacks.Coherent.CoherentAdicSystems`, exactly as `Stacks.Algebraization.IsSystemPowerAnnihilated`
is.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 01Y8](https://stacks.math.columbia.edu/tag/01Y8)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-! ### The ascending chain condition for quasi-coherent ideal sheaves -/

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **The quasi-coherent ideal sheaves of a Noetherian scheme satisfy the ascending chain
condition.**

A monotone sequence `n ↦ I n` of ideal sheaves is tested on the finite affine cover
`X.affineCover.finiteSubcover`. Over each member `U` of that cover the ideals `(I n).ideal U` form
a monotone chain in the Noetherian ring `Γ(X, U)`, so they stabilize; the finitely many
stabilization indices have a maximum, and past it the sequence is constant because two ideal
sheaves agreeing on an affine cover are equal.

This is the input the Noetherian induction of Stacks 088C needs, for which the source cites
Stacks 01Y8. -/
@[sga "3 VIB 6.5.3" "partial", sga "3 XI 6.9" "partial"]
public theorem wellFoundedGT_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X] :
    WellFoundedGT X.IdealSheafData := by
  classical
  rw [wellFoundedGT_iff_monotone_chain_condition]
  intro a
  let 𝒰 := X.affineCover.finiteSubcover
  have hAff : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i => by dsimp [𝒰]; infer_instance
  let U : 𝒰.I₀ → X.affineOpens := fun i =>
    ⟨(𝒰.f i).opensRange, have := hAff i; isAffineOpen_opensRange (𝒰.f i)⟩
  have hU : ⨆ i, (U i).1 = ⊤ := 𝒰.iSup_opensRange
  have hstab : ∀ i : 𝒰.I₀, ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      (a n).ideal (U i) = (a m).ideal (U i) := by
    intro i
    have hN : IsNoetherianRing Γ(X, (U i).1) := IsLocallyNoetherian.component_noetherian (U i)
    exact monotone_stabilizes_iff_noetherian.mpr hN
      ⟨fun n => (a n).ideal (U i), fun p q hpq => le_def.mp (a.monotone hpq) (U i)⟩
  let start : 𝒰.I₀ → ℕ := fun i => Classical.choose (hstab i)
  have hstart : ∀ i : 𝒰.I₀, start i ≤ Finset.sup Finset.univ start :=
    fun i => Finset.le_sup (Finset.mem_univ i)
  refine ⟨Finset.sup Finset.univ start, fun m hm => ?_⟩
  refine ext_of_iSup_eq_top U hU fun i => ?_
  have h₁ := Classical.choose_spec (hstab i) _ (hstart i)
  have h₂ := Classical.choose_spec (hstab i) m ((hstart i).trans hm)
  exact h₁.symm.trans h₂

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Algebraization

/-! ### Systems killed by an ideal sheaf -/

variable {X : Scheme.{u}}

/-- An inverse system of sheaves of modules is **killed by** a quasi-coherent ideal sheaf `K` if
`K · F_n = 0` for every `n`.

This is annihilation by `K` itself, not by a power of `K`; for the latter see
`Stacks.Algebraization.IsSystemPowerAnnihilated`. The family of ideal sheaves `K` for which every
coherent adic system killed by `K` is algebraizable is the family `Ξ` of the proof of Stacks
088C. -/
public def IsSystemAnnihilatedBy (K : X.IdealSheafData) (F : ℕᵒᵖ ⥤ X.Modules) : Prop :=
  ∀ n : ℕ, idealPowerMultiple K 1 (F.obj (op n)) = ⊥

/-- **The zero ideal sheaf kills every system.** Affine-locally the condition asks that every
element of `(⊥ : X.IdealSheafData).ideal U ^ 1 = ⊥` kill every section, and the only such element
is `0`.

This is why `⊥ ∈ Ξ` is the whole of essential surjectivity in the proof of Stacks 088C. -/
public theorem isSystemAnnihilatedBy_bot (F : ℕᵒᵖ ⥤ X.Modules) :
    IsSystemAnnihilatedBy (⊥ : X.IdealSheafData) F := by
  intro n
  rw [idealPowerMultiple_eq_bot_iff_affine_sections_annihilated]
  intro U r hr x
  rw [pow_one, Scheme.IdealSheafData.ideal_bot] at hr
  rw [(Submodule.mem_bot _).mp hr, zero_smul]

/-! ### The Noetherian induction -/

open Stacks.Cohomology.FormalFunctions

/-- **The Noetherian induction of Stacks 088C.** Let `X` be a Noetherian scheme and `𝓘` a
quasi-coherent ideal sheaf on it. Suppose that for every quasi-coherent ideal sheaf `K` the
following inductive step holds: if every coherent `𝓘`-adic system killed by an ideal sheaf
strictly larger than `K` is in the essential image of the completion functor, then so is every
coherent `𝓘`-adic system killed by `K`. Then every coherent `𝓘`-adic system killed by any ideal
sheaf whatsoever is in the essential image.

This is well-founded induction along the strict-superset relation on `X.IdealSheafData`, which is
well-founded by `AlgebraicGeometry.Scheme.IdealSheafData.wellFoundedGT_of_isNoetherian`. The
source runs the same induction in contrapositive form, choosing an ideal sheaf maximal outside
the family `Ξ`. -/
public theorem essImage_completionFunctor_of_devissage (X : Scheme.{u}) [IsNoetherian X]
    (J : X.IdealSheafData)
    (hDev : ∀ K : X.IdealSheafData,
      (∀ K' : X.IdealSheafData, K < K' →
          ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems J,
            IsSystemAnnihilatedBy K' 𝓖.obj → (completionFunctor X J).essImage 𝓖) →
        ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems J,
          IsSystemAnnihilatedBy K 𝓕.obj → (completionFunctor X J).essImage 𝓕) :
    ∀ (K : X.IdealSheafData) (𝓕 : Stacks.Coherent.CoherentAdicSystems J),
      IsSystemAnnihilatedBy K 𝓕.obj → (completionFunctor X J).essImage 𝓕 := by
  let _ : WellFoundedGT X.IdealSheafData :=
    AlgebraicGeometry.Scheme.IdealSheafData.wellFoundedGT_of_isNoetherian X
  intro K
  induction K using WellFoundedGT.induction with
  | ind K ih => exact hDev K ih

/-! ### Grothendieck existence for a proper morphism -/

/-- **Grothendieck existence for a proper morphism, from the theorem on formal functions and the
inductive step.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, let
`f : X ⟶ Spec A` be a proper morphism of schemes and set `𝓘 = I · 𝒪_X`. Suppose

* `hFF`, the theorem on formal functions in degree zero (Stacks 087U), which is what Stacks 0883
  uses for full faithfulness, and
* `hDev`, the inductive step of the source's Noetherian induction: a coherent `𝓘`-adic system
  killed by a quasi-coherent ideal sheaf `K` is in the essential image of the completion functor
  as soon as every coherent `𝓘`-adic system killed by an ideal sheaf strictly larger than `K` is.

Then the completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880 is an equivalence. Full
faithfulness is Stacks 0883 read through `hFF`. Essential surjectivity is the Noetherian induction
`essImage_completionFunctor_of_devissage` applied at the zero ideal sheaf, which kills every
system by `isSystemAnnihilatedBy_bot`; the induction is legitimate because the quasi-coherent
ideal sheaves of the Noetherian scheme `X` satisfy the ascending chain condition. Noetherianity of
`X` is not an added hypothesis: local Noetherianity follows from `LocallyOfFiniteType f` over the
Noetherian base and quasi-compactness from the universal closedness of `f` and the
quasi-compactness of `Spec A`.

Both binders hold for every such `f`:
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper`
(`CompletionProper/GrothendieckExistenceProper.lean`), which carries Stacks 088C, discharges `hFF`
by `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper` and `hDev` by
`Stacks.Coherent.essImage_completionFunctor_of_devissageStep`. -/
public theorem isEquivalence_completionFunctor_of_devissage
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (hFF : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        IsIso (globalSectionsToLimit (baseIdealSheaf A I f) H))
    (hDev : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K : X.IdealSheafData,
        (∀ K' : X.IdealSheafData, K < K' →
            ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
              IsSystemAnnihilatedBy K' 𝓖.obj →
                (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) →
          ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
            IsSystemAnnihilatedBy K 𝓕.obj →
              (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓕) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := { }
  obtain ⟨hff⟩ := fullyFaithful_completionFunctor A I f hFF
  let _ := hff.full
  let _ := hff.faithful
  let _ : (completionFunctor X (baseIdealSheaf A I f)).EssSurj :=
    ⟨fun 𝓕 => essImage_completionFunctor_of_devissage X (baseIdealSheaf A I f) hDev ⊥ 𝓕
      (isSystemAnnihilatedBy_bot 𝓕.obj)⟩
  exact { }

end Stacks.Algebraization

end
