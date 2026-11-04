module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.AffineAvatar
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase

/-!
# Derived global sections of a pseudo-coherent complex along a flat proper morphism

Let `A` be a ring and let `f : X ⟶ Spec A` be flat, proper and of finite presentation. For a
pseudo-coherent object `F` of `D(𝒪_X)` the `A`-linear derived global sections `RΓ(X, F)` form a
pseudo-coherent object of `D(A)`. This is the pseudo-coherence half of [Stacks, Tag 0CSD] read
over the ring of the affine base, which is how the source uses that lemma in the proof of
[Stacks, Tag 0DID]: "by Lemma 0CSD we see that `M_n` is a pseudo-coherent object of `D(A_n)`".

## Main results

* `AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_id_of_isPseudoCoherent`: on
  `Spec A`, a pseudo-coherent object of `D(𝒪_{Spec A})` has pseudo-coherent derived global
  sections.
* `AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_of_flat_of_isProper`: the
  statement above.

## Implementation notes

The proof is the source's chain of identifications. `RΓ(X, F) = RΓ(Spec A, Rf_*F)` by
[Stacks, Tag 0D5W] (`AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso`); `Rf_*F` is
pseudo-coherent by [Stacks, Tag 0CSD]; a pseudo-coherent object of `D(𝒪_{Spec A})` is `M̃` for a
pseudo-coherent `M` in `D(A)` ([Stacks, Tag 08E5], [Stacks, Tag 06Z0] and [Stacks, Tag 08E7],
`AlgebraicGeometry.RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde`); and
`RΓ(Spec A, M̃) = M` is the unit of the derived Spec–Γ adjunction. Everything runs at
`HasDerivedCategory.standard`, the model of all the inputs.

## References

* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasDerivedCategory

/-- **Over an affine base, a pseudo-coherent object has pseudo-coherent derived global
sections.** A pseudo-coherent `E` in `D(𝒪_{Spec R})` is `M̃` for a pseudo-coherent `M` in `D(R)`,
and `RΓ(Spec R, M̃) ≅ M` is the unit of the derived Spec–Γ adjunction. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_id_of_isPseudoCoherent (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj E) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde R E hE
  have := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit R
  let eu : M ≅ (derivedGlobalSectionsOver (𝟙 (Spec R))).obj
      ((derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).obj M) :=
    asIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app M)
  exact hM.ofIso (eu ≪≫
    (derivedGlobalSectionsOver (𝟙 (Spec R))).mapIso ((derivedTildeCompι R).app M ≪≫ e))

/-- **The pseudo-coherence half of [Stacks, Tag 0CSD] over the ring of an affine base.** Let
`f : X ⟶ Spec A` be flat, proper and locally of finite presentation and let `F` be a
pseudo-coherent object of `D(𝒪_X)`. Then `RΓ(X, F)` is a pseudo-coherent object of `D(A)`. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_of_flat_of_isProper {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] (F : DerivedCategory X.Modules)
    (hF : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) F) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedGlobalSectionsOver f).obj F) :=
  (isPseudoCoherent_derivedGlobalSectionsOver_id_of_isPseudoCoherent (CommRingCat.of A)
      ((derivedPushforwardModules f).obj F)
      (isPseudoCoherent_derivedPushforward_of_flat_of_isProper f F hF)).ofIso
    ((derivedGlobalSectionsOverPushforwardIso f).app F).symm

end AlgebraicGeometry

end
