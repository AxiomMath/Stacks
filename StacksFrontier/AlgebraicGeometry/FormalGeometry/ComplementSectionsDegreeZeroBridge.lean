module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementAdicQuotientLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementSectionsAdicLimitBijective
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ComplementCohomologyZeroSections

/-!
# The two models of `Γ(Spec A ∖ V(J), Ñ)`, and the degree-zero comparison carried across

Let `A` be a commutative ring and `J ⊆ A` an ideal, and write `V = Spec A ∖ V(J)`. Two functors
on `A`-modules compute the `A`-module `Γ(V, Ñ)`:

* `Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor J 0`, the degree-zero right
  derived functor of sections over `V` evaluated at `Ñ`, which is the functor the long exact
  cohomology sequence of `V(J)` and the comparison of [Stacks, Tag 0DWR] are stated with;
* `Stacks.Algebraization.affineComplementSectionsFunctor A J`, honest global sections of the
  restriction of `Ñ` to the open subscheme `V`, which is the functor the four-term sequence of
  [Stacks, Tag 0BK0] and the degree-zero limit comparison of [Stacks, Tag 0DXQ] are stated with.

This file identifies the two as functors, and uses the identification to carry the degree-zero
bijectivity of [Stacks, Tag 0DXQ] from the second model to the first: the canonical map

`H⁰(V, M̃) ⟶ lim_n H⁰(V, (M/IⁿM)~)`

is an isomorphism under the hypotheses of
`Stacks.Algebraization.bijective_complementSectionsToLimit`.

## Main definitions

* `Stacks.Algebraization.complementCohomologyBaseZeroSectionsOnComplementNatIso` — degree-zero
  complement cohomology of `Ñ`, read over `A`, is sections of `Ñ` over the open `V` of `Spec A`.
* `Stacks.Algebraization.complementCohomologyBaseZeroSectionsNatIso` — **the natural
  isomorphism** of the two models above.

## Main results

* `Stacks.Algebraization.tildeComplementSections_zeroLocusSubset_eq` — the target of the first
  isomorphism is `Stacks.LocalCohomologyTilde.tildeComplementSections` at the closed subset
  `V(J)`, on the nose.
* `Stacks.Algebraization.complementSectionsToLimit_eq_lift_mapCone` — the degree-zero comparison
  map of [Stacks, Tag 0DXQ] on the affine complement is the limit comparison of the image of the
  cone of quotient maps `M ⟶ M/IⁿM` under `N ↦ Γ(V, Ñ)`.
* `Stacks.Algebraization.isIso_complementAdicQuotientToLimit_zero` — the canonical map
  `H⁰(V, M̃) ⟶ lim_n H⁰(V, (M/IⁿM)~)` is an isomorphism.

## Implementation notes

The natural isomorphism is built in two steps, and neither step chooses anything.

The first step is left exactness of sections over an open. Sections over the open complement of a
closed subset preserve finite limits, which is
`Stacks.LocalCohomologySequence.preservesFiniteLimits_sectionsOnComplement`, so Mathlib's
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` — the inverse of the canonical
`CategoryTheory.Functor.toRightDerivedZero`, which is invertible for a left exact functor —
identifies the zeroth right derived functor with the functor itself. That isomorphism is already
in the library as `Stacks.LocalCohomologySequence.complementCohomologyZeroIso`, and whiskering it
with `Stacks.LocalCohomologyTilde.tildeSheafFunctor` on the left and
`Stacks.LocalCohomologyTilde.globalToBase` on the right is the first factor. The target is
written as `Stacks.LocalCohomology.sectionsOnAffineComplement`, which it reaches definitionally:
the two opens `Stacks.Cohomology.SectionsWithSupport.openComplement (zeroLocusSubset J) _` and
`Stacks.LocalCohomology.complementZeroLocus A J` are the same open on the nose, both being the
complement of `PrimeSpectrum.zeroLocus (J : Set A)`, and the two `A`-module structures agree as
well, successive restriction of scalars along `A ≅ Γ(Spec A, 𝒪)` and along restriction to `V`
being restriction along the composite. That equality of functors is
`Stacks.LocalCohomologySequence.sectionsOnComplement_zeroLocus_eq`, a `rfl`; so the target is
also `Stacks.LocalCohomologyTilde.tildeComplementSections` at `V(J)`, which is
`Stacks.Algebraization.tildeComplementSections_zeroLocusSubset_eq` below.

The second step is the passage from the open `V` of `Spec A` to the open subscheme `V`, where the
sections are those over `ι ''ᵁ ⊤`. There the comparison is *not* definitional — `ι ''ᵁ ⊤ = V` is
`AlgebraicGeometry.Scheme.Opens.ι_image_top`, a propositional equality of opens — and the
transport along it, together with the agreement of the two restrictions of scalars (for which
`Stacks.LocalCohomology.appIsoScalars_eq_id` says the comparison of structure-sheaf sections is
the identity), is `Stacks.LocalCohomology.sectionsOnAffineComplementIso`. So the second factor is
that isomorphism, inverted and whiskered with `AlgebraicGeometry.tilde.functor` on the left.

For the transport of the degree-zero bijectivity, the comparison map has to be recognised as a
limit comparison of an image cone, because that is the shape
`CategoryTheory.Limits.isIso_limit_lift_mapCone_iff` transports along a natural isomorphism of
the two functors. As in
`Stacks.Algebraization.localCohomologyAdicQuotientToLimit_eq_lift_mapCone`, the two spellings of
the diagram of the limit are only definitionally equal, so the `π`-equation of the image cone is
closed with `exact (limit.lift_π _ _).symm` rather than by rewriting with it.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.LocalCohomologySequence Stacks.LocalCohomologyTilde

variable {A : Type u} [CommRing A]

/-! ### The two models of the sections on the affine complement -/

/-- The functor `N ↦ Γ(Spec A ∖ V(J), Ñ)` of
`Stacks.LocalCohomologyTilde.tildeComplementSections`, at the closed subset `V(J)`, is sections
of `Ñ` over the open `Spec A ∖ V(J)` of `Spec A`. The two differ only in how the `A`-module
structure is spelled — successively along `A ≅ Γ(Spec A, 𝒪)` and the restriction to the open,
versus along the composite — and so agree on the nose, by
`Stacks.LocalCohomologySequence.sectionsOnComplement_zeroLocus_eq`. -/
theorem tildeComplementSections_zeroLocusSubset_eq (J : Ideal A) :
    tildeComplementSections (zeroLocusSubset (A := CommRingCat.of A) J)
        (isClosed_zeroLocusSubset (A := CommRingCat.of A) J) =
      tilde.functor (CommRingCat.of A) ⋙ sectionsOnAffineComplement A J :=
  rfl

/-- **Degree-zero cohomology of `Ñ` on `V = Spec A ∖ V(J)` is the module of sections of `Ñ` over
the open `V` of `Spec A`, naturally in `N`.** Sections over an open are left exact, so their
zeroth right derived functor is the functor itself; this is that identification, whiskered with
`N ↦ Ñ` on the left and with the restriction of scalars to `A` on the right. -/
def complementCohomologyBaseZeroSectionsOnComplementNatIso (J : Ideal A) :
    complementCohomologyBaseFunctor (A := CommRingCat.of A) J 0 ≅
      tilde.functor (CommRingCat.of A) ⋙ sectionsOnAffineComplement A J :=
  Functor.isoWhiskerLeft (tildeSheafFunctor (CommRingCat.of A))
    (Functor.isoWhiskerRight (complementCohomologyZeroIso (A := CommRingCat.of A) J)
      (globalToBase (CommRingCat.of A)))

/-- **The two models of `N ↦ Γ(Spec A ∖ V(J), Ñ)` agree, naturally in `N`.** The degree-zero
right derived functor of sections over the open complement, evaluated at `Ñ` and read as an
`A`-module, is the functor `Stacks.Algebraization.affineComplementSectionsFunctor` of honest
global sections of the restriction of `Ñ` to the open subscheme `Spec A ∖ V(J)`.

The first factor is left exactness of sections over an open, the second is the transport along
`ι ''ᵁ ⊤ = Spec A ∖ V(J)` from the open of `Spec A` to the open subscheme. -/
def complementCohomologyBaseZeroSectionsNatIso (J : Ideal A) :
    complementCohomologyBaseFunctor (A := CommRingCat.of A) J 0 ≅
      affineComplementSectionsFunctor A J :=
  complementCohomologyBaseZeroSectionsOnComplementNatIso J ≪≫
    Functor.isoWhiskerLeft (tilde.functor (CommRingCat.of A))
      (sectionsOnAffineComplementIso J).symm

/-! ### The degree-zero comparison as a limit comparison of an image cone -/

/-- **The canonical map `Γ(V, M̃) ⟶ lim_n Γ(V, (M/IⁿM)~)` of [Stacks, Tag 0DXQ] at `i = 0` is the
limit comparison of the image of the cone of quotient maps under `N ↦ Γ(V, Ñ)`**, for
`V = Spec A ∖ V(J)`. Both maps are determined by their composites with the projections of the
limit, and those composites agree because the `n`-th leg of either cone is the functor applied to
the `n`-th quotient map. -/
theorem complementSectionsToLimit_eq_lift_mapCone (I J : Ideal A) (M : ModuleCat.{u} A) :
    complementSectionsToLimit A I J M =
      limit.lift (adicQuotientModuleSystem A I M ⋙ affineComplementSectionsFunctor A J)
        ((affineComplementSectionsFunctor A J).mapCone
          (Dualizing.adicQuotientModuleCone A I M)) := by
  refine limit.hom_ext fun j => ?_
  obtain ⟨n⟩ := j
  rw [complementSectionsToLimit_π]
  exact (limit.lift_π ((affineComplementSectionsFunctor A J).mapCone
    (Dualizing.adicQuotientModuleCone A I M)) (op n)).symm

/-! ### The degree-zero bijectivity, carried to the derived-functor model -/

/-- **The canonical map `H⁰(V, M̃) ⟶ lim_n H⁰(V, (M/IⁿM)~)` is an isomorphism**, for
`V = Spec A ∖ V(J)`, under the hypotheses of
`Stacks.Algebraization.bijective_complementSectionsToLimit`: `(A, 𝔪)` Noetherian local and
`I`-adically complete, `M` a finite `A`-module, `J₀` an ideal with the property of
[Stacks, Tag 0DXP] for a bound `1 ≤ s`, and `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}`.

This is the comparison clause of [Stacks, Tag 0DXQ] at `i = 0` in the derived-functor model: the
bijectivity is proved in the sections model, and
`Stacks.Algebraization.complementCohomologyBaseZeroSectionsNatIso` carries it across, which is
exactly what naturality in the module buys — both sides are limits over the tower `n ↦ M/IⁿM`, so
an isomorphism of the two models at each single module would not suffice. -/
theorem isIso_complementAdicQuotientToLimit_zero [IsLocalRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} [IsAdicComplete I A] {hI : I ≠ ⊤} {s : ℤ} {J₀ : Ideal A}
    (H : IsLocalAlgebraizationIdeal (M := M) I hI s J₀)
    (J : Ideal A) (hJJ₀ : J ≤ J₀) (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (hs : 1 ≤ s) :
    IsIso (complementAdicQuotientToLimit A I J (ModuleCat.of A M) 0) := by
  have hiso : IsIso (complementSectionsToLimit A I J (ModuleCat.of A M)) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_complementSectionsToLimit H J hJJ₀ hJ D hV hs)
  rw [complementSectionsToLimit_eq_lift_mapCone] at hiso
  exact (isIso_limit_lift_mapCone_iff
    (complementCohomologyBaseFunctor (A := CommRingCat.of A) J 0)
    (affineComplementSectionsFunctor A J)
    (complementCohomologyBaseZeroSectionsNatIso J)
    (Dualizing.adicQuotientModuleCone A I (ModuleCat.of A M))).2 hiso

end Stacks.Algebraization

end
