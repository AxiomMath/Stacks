module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairZariskiScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.FiniteSurjectiveDescent
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale global sections over the closed subscheme of a henselian pair

Let `(A, I)` be a henselian pair, let `X = Spec A` and let `Z = Spec (A ⧸ I)`. This file proves
`Γ(X, ℱ) = Γ(Z, ℱ|_Z)` for every sheaf of sets `ℱ` on the small étale site of `X`, which is
[Stacks, Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH): the canonical comparison of global
sections along `Z ⟶ X` is an isomorphism. There is no hypothesis that `A` be local.

## Main results

* `Stacks.EtaleCohomology.isIso_globalSectionsComparison_quotient_of_henselianPair` —
  [Stacks, Tag 09ZH].
* `Stacks.EtaleCohomology.isIso_globalSectionsComparison_maximalIdeal` — the case of a henselian
  local ring and its maximal ideal.

## Implementation notes

Everything is deduced from Gabber's comparison,
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImageComparison_of_zariskiBijective`
([Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)), whose two Zariski hypotheses
hold at an arbitrary henselian pair:
`Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_quotient_of_henselianPair` is the
first, and `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_pullback_of_henselianPair`
the second. Its remaining hypotheses are read off the affine situation: `Spec A` is quasi-compact
and quasi-separated, and `Z ⟶ X` is a closed immersion because `A ⧸ I` is a quotient of `A`.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
* [Stacks Project, Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace Stacks.EtaleCohomology

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- **[Stacks, Tag 09ZH].** Let `(A, I)` be a henselian pair, let `X = Spec A` and let
`Z = Spec (A ⧸ I)`. Then `Γ(X, ℱ) = Γ(Z, ℱ|_Z)` for every sheaf of sets `ℱ` on the small étale
site of `X`: the canonical comparison of global sections along `Z ⟶ X` is an isomorphism.

There is no hypothesis that `A` be local. The two Zariski inputs are hypotheses (1) and (2) of
[Stacks, Tag 09ZF] for `Z ⟶ X`, and they hold at an arbitrary henselian pair:
`Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_quotient_of_henselianPair` is (1),
proved from [Stacks, Tag 09ZG] because `Spec A` is a spectral space in which `V(I)` meets the
closure of every point in a connected set, and
`Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_pullback_of_henselianPair` is (2),
because a scheme finite over `Spec A` is the spectrum of an integral `A`-algebra `B` and
`(B, IB)` is again a henselian pair. -/
@[stacks 09ZH "Γ(X, ℱ) = Γ(Z, ℱ|_Z) for every sheaf of sets ℱ on the small étale site of
X = Spec A, where (A, I) is a henselian pair and Z = Spec (A/I):  the canonical comparison of
global sections along Z ⟶ X is an isomorphism.  The ring A is not assumed local",
  sga "4 XII 6.13" "special case"]
public theorem isIso_globalSectionsComparison_quotient_of_henselianPair
    (h : HenselianPair A I) :
    IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).val := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact isIso_globalSectionsSmallEtaleInverseImageComparison_of_zariskiBijective.{u, v}
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (bijective_zariskiGlobalSectionsMapAt_quotient_of_henselianPair A I h)
    (fun f _ F ↦ bijective_zariskiGlobalSectionsMapAt_pullback_of_henselianPair A I h f F)

/-- **[Stacks, Tag 09ZH] for a henselian local ring and its maximal ideal.** A henselian local
ring and its maximal ideal form a henselian pair, so global sections of a sheaf of sets on the
small étale site of `Spec B` agree with global sections of its inverse image on
`Spec (B ⧸ 𝔪)`. -/
@[sga "4 XII 6.13" "special case"]
public theorem isIso_globalSectionsComparison_maximalIdeal
    (B : Type u) [CommRing B] [HenselianLocalRing B] :
    IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B))))).val :=
  isIso_globalSectionsComparison_quotient_of_henselianPair.{u, v} B _
    (henselianPair_maximalIdeal B)

end Stacks.EtaleCohomology

end
