module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairZariskiScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.FiniteSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSectionsHenselianLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreGlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale global sections of a proper scheme over a henselian pair, unconditionally

Let `(A, I)` be a henselian pair, let `f : X ⟶ Spec A` be proper and let `i : Z ⟶ X` be the
closed immersion of the closed fibre `Z = X ×_{Spec A} Spec (A ⧸ I)`. For every sheaf of sets `ℱ`
on the small étale site of `X` the canonical comparison `Γ(X, ℱ) ⟶ Γ(Z, i_{small}^{-1}ℱ)` is
bijective. This is [Stacks, Tag 0A0C], and its special case for a henselian local ring and the
fibre over the closed point is [Stacks, Tag 0A3S].

The proof is the source's: Tag 0A0C is [Stacks, Tag 09ZF] applied to `i`, whose two Zariski
hypotheses are both instances of [Stacks, Tag 0A0B].

## Main results

* `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_closedFibre_of_henselianPair` —
  hypothesis (1) of Tag 09ZF for `i`: restriction of global sections of a Zariski sheaf of sets
  along `i` is bijective. This is Tag 0A0B, read on the Zariski site of `X`.
* `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_pullback_closedFibre`
  — hypothesis (2) of Tag 09ZF for `i`: the same along the base change of `i` by a finite
  morphism `Y ⟶ X`. This is Tag 0A0B for the proper morphism `Y ⟶ Spec A`.
* `Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper`
  — **[Stacks, Tag 0A0C]**, and its component at each sheaf,
  `bijective_globalSectionsComparison_app_closedFibre_of_henselianPair_of_isProper`.
* `Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_isProper` —
  **[Stacks, Tag 0A3S]**, and its component at each sheaf,
  `Stacks.EtaleCohomology.bijective_globalSectionsComparison_app_closedFibre_of_isProper`.

## Implementation notes

The conditional statements `isIso_globalSectionsComparison_closedFibre_of_henselianPair` and
`isIso_globalSectionsComparison_closedFibre_of_henselianLocalRing` of the files this one imports
carry the surjectivity half of Tag 09ZF as a hypothesis; Tag 09ZF is now available in full
(`isIso_globalSectionsSmallEtaleInverseImageComparison_of_zariskiBijective`), so the statements
here carry nothing.

The Zariski hypotheses of Tag 09ZF are asked of sheaves of sets in the universe of the schemes,
which is exactly the coefficient universe at which Tag 0A0B is stated.

## References

* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
* [Stacks Project, Tag 0A0B](https://stacks.math.columbia.edu/tag/0A0B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u v

namespace Stacks.EtaleCohomology

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- The closed fibre inclusion `Spec (A ⧸ I) ⟶ Spec A` is a closed immersion. -/
private theorem isClosedImmersion_spec_map_mk :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

include hI in
/-- **Hypothesis (1) of [Stacks, Tag 09ZF] for the closed fibre of a proper scheme over a
henselian pair.** Restriction of global sections of a sheaf of sets on the Zariski site of `X`
along the inclusion of the closed fibre `X ×_{Spec A} Spec (A ⧸ I)` is bijective. This is
[Stacks, Tag 0A0B] read on the Zariski site. -/
public theorem bijective_zariskiGlobalSectionsMapAt_closedFibre_of_henselianPair
    (F : Sheaf (Opens.grothendieckTopology X.carrier) (Type u)) :
    Function.Bijective (zariskiGlobalSectionsMapAt
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) F) := by
  have := isClosedImmersion_spec_map_mk I
  exact bijective_zariskiGlobalSectionsMapAt_of_globalSectionsRestriction _
    (Scheme.Hom.isClosedEmbedding _).isEmbedding F
    (bijective_globalSectionsRestriction_closedFibre_of_henselianPair_of_isProper A I hI f F)

include hI in
/-- **Hypothesis (2) of [Stacks, Tag 09ZF] for the closed fibre of a proper scheme over a
henselian pair.** For a finite morphism `g : Y ⟶ X`, restriction of global sections of a sheaf of
sets on the Zariski site of `Y` along the base change by `g` of the inclusion of the closed fibre
is bijective. The scheme `Y` is proper over `Spec A`, and the image of that base change is the
closed fibre of `Y`, so this is [Stacks, Tag 0A0B] for `g ≫ f`. -/
public theorem bijective_zariskiGlobalSectionsMapAt_pullback_closedFibre
    {Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g]
    (F : Sheaf (Opens.grothendieckTopology Y.carrier) (Type u)) :
    Function.Bijective (zariskiGlobalSectionsMapAt
      (pullback.fst g
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) F) := by
  have := isClosedImmersion_spec_map_mk I
  refine bijective_zariskiGlobalSectionsMapAt_of_globalSectionsRestriction _
    (Scheme.Hom.isClosedEmbedding _).isEmbedding F ?_
  have hrange : Set.range (pullback.fst g
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).base =
      Set.range (pullback.fst (g ≫ f)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, Scheme.Pullback.range_fst,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  rw [hrange]
  exact bijective_globalSectionsRestriction_closedFibre_of_henselianPair_of_isProper
    A I hI (g ≫ f) F

include hI in
/-- **[Stacks, Tag 0A0C].** Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be proper.
For every sheaf of sets `ℱ` on the small étale site of `X`, restriction of global sections to the
closed fibre `Z = X ×_{Spec A} Spec (A ⧸ I)` is bijective: the canonical comparison
`Γ(X, ℱ) ⟶ Γ(Z, i_{small}^{-1}ℱ)`, natural in `ℱ`, is an isomorphism.

This is [Stacks, Tag 09ZF] for the closed immersion `i : Z ⟶ X`, whose two hypotheses are
[Stacks, Tag 0A0B] for `f` and for `Y ⟶ X ⟶ Spec A`, `Y ⟶ X` finite. -/
@[stacks 0A0C, sga "4 XII 6.13" "partial, special case"]
public theorem isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper :
    IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).val := by
  have := isClosedImmersion_spec_map_mk I
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  exact isIso_globalSectionsSmallEtaleInverseImageComparison_of_zariskiBijective.{u, v} _
    (bijective_zariskiGlobalSectionsMapAt_closedFibre_of_henselianPair I hI f)
    (fun g _ F ↦ bijective_zariskiGlobalSectionsMapAt_pullback_closedFibre
      I hI f g F)

include hI in
/-- **[Stacks, Tag 0A0C], sheaf by sheaf.** Let `(A, I)` be a henselian pair and let
`f : X ⟶ Spec A` be proper. For every sheaf of sets `ℱ` on the small étale site of `X`, the
restriction map `Γ(X, ℱ) ⟶ Γ(Z, i_{small}^{-1}ℱ)` to the closed fibre
`Z = X ×_{Spec A} Spec (A ⧸ I)` is bijective. This is the component at `ℱ` of
`isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper`. -/
@[stacks 0A0C, sga "4 XII 6.13" "partial, special case"]
public theorem bijective_globalSectionsComparison_app_closedFibre_of_henselianPair_of_isProper
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    Function.Bijective ((globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).val.app F) := by
  have := isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper.{u, v} I hI f
  exact (isIso_iff_bijective _).mp inferInstance

variable (A) in
/-- **[Stacks, Tag 0A3S].** Let `A` be a henselian local ring, let `f : X ⟶ Spec A` be proper
and let `X₀ = X ×_{Spec A} Spec κ(A)` be the fibre of `f` over the closed point. For every sheaf of
sets `ℱ` on the small étale site of `X`, `Γ(X, ℱ) = Γ(X₀, ℱ|_{X₀})`: the canonical comparison of
global sections along the inclusion of `X₀`, natural in `ℱ`, is an isomorphism.

This is [Stacks, Tag 0A0C] for the henselian pair `(A, 𝔪)`. -/
@[stacks 0A3S, sga "4 XII 6.13" "special case"]
public theorem isIso_globalSectionsComparison_closedFibre_of_isProper [HenselianLocalRing A] :
    IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (closedFibreInclusion A f)).val :=
  isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper.{u, v}
    (IsLocalRing.maximalIdeal A) (henselianPair_maximalIdeal A) f

variable (A) in
/-- **[Stacks, Tag 0A3S], sheaf by sheaf.** Let `A` be a henselian local ring, let
`f : X ⟶ Spec A` be proper and let `X₀ = X ×_{Spec A} Spec κ(A)` be the fibre over the closed
point. For every sheaf of sets `ℱ` on the small étale site of `X`, restriction of global sections
`Γ(X, ℱ) ⟶ Γ(X₀, ℱ|_{X₀})` is bijective. This is the component at `ℱ` of
`isIso_globalSectionsComparison_closedFibre_of_isProper`. -/
@[stacks 0A3S]
public theorem bijective_globalSectionsComparison_app_closedFibre_of_isProper
    [HenselianLocalRing A] (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    Function.Bijective ((globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (closedFibreInclusion A f)).val.app F) := by
  have := isIso_globalSectionsComparison_closedFibre_of_isProper.{u, v} A f
  exact (isIso_iff_bijective _).mp inferInstance

end Stacks.EtaleCohomology

end
