module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomology
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing

/-!
# Étale global sections of a proper scheme over a henselian local ring

Let `A` be a henselian local ring, let `f : X ⟶ Spec A` be proper and let
`X₀ = X ×_{Spec A} Spec κ(A)` be the fibre of `f` over the closed point.  For every sheaf of sets
`F` on the small étale site of `X`, restriction to `X₀` is injective on global sections, and is
bijective — `Γ(X, F) = Γ(X₀, F|_{X₀})` — as soon as every global section of `F|_{X₀}` is presented
by a compatible family of sections of `F`.

A henselian local ring forms a henselian pair with its maximal ideal, by
`henselianPair_maximalIdeal`, and `Spec κ(A) ⟶ Spec A` is the quotient by that ideal, so the closed
fibre `Stacks.EtaleCohomology.closedFibre` is the closed fibre of that henselian pair and the
results of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSections`
apply with `I = 𝔪`.

## Main results

* `injective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianLocalRing` — restriction of
  global sections to the closed fibre is injective, with no hypothesis beyond henselianity of `A`
  and properness of `f`.
* `bijective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianLocalRing` and
  `Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_henselianLocalRing` —
  restriction is bijective, granted that every global section of the inverse image admits a
  compatible presenting family.  [Stacks, Tag 0A3S] without that hypothesis is
  `Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_isProper`.

## Implementation notes

Injectivity needs only that the sole open of `X` containing the closed fibre is `X` itself, which
over a henselian pair follows from `I` lying in the Jacobson radical together with closedness of
`f`;  it carries no hypothesis.

Surjectivity is carried as the named hypothesis `hcompat`: every global section `t` of `F|_{X₀}`
admits objects `W j` of the small étale site of `X` whose images cover `X`, together with sections
`s j` of `F` over them which agree on the pairwise fibre products and pull back to the restrictions
of `t`.  A presenting family with every property but agreement is produced for each `t` by
`Stacks.EtaleCohomology.exists_smallEtaleCover_sectionPullback_of_inverseImageSection`, so what
`hcompat` adds is agreement of the `s j` on `W j ×_X W j'`.  That is a statement about a family of
sections, strictly weaker than the surjectivity it yields:  agreement would follow from injectivity
of restriction to `(W j ×_X W j') ×_X X₀`, which is the étale analogue of the input the source
obtains not on `X` but after refining the family by a finite surjective morphism
([Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0)) and descending again
([Stacks, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3)).  Of those two, Tag 09Z0 is
available here only for a covering whose fibres all have one degree, and Tag 09Z3 only in its
injectivity halves, not the equalizer property that descent of sections needs.

[Stacks, Tag 0A3S] itself, with no hypothesis, is
`Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_isProper` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSectionsProper`:
it is [Stacks, Tag 0A0C] for the henselian pair `(A, 𝔪)`, through [Stacks, Tag 09ZF] in full and
[Stacks, Tag 0A0B].  It lives there and not here because Tag 0A0B rests on the theorem on formal
functions:  importing it into this file would enlarge the import closure of every module built on
this one.

## References

* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace Stacks.EtaleCohomology

variable (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- **The injectivity half of [Stacks, Tag 0A3S].**  For `A` a henselian local ring and
`f : X ⟶ Spec A` proper, the comparison from global sections of a sheaf of sets on the small étale
site of `X` to global sections of its inverse image on the closed fibre is injective.

This is the injectivity half of [Stacks, Tag 0A0C] for the henselian pair `(A, 𝔪)` of
`henselianPair_maximalIdeal`, the closed point of `Spec A` being the quotient by `𝔪`. -/
public theorem injective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianLocalRing
    (g : terminal (closedFibre A f).Etale ⟶
      (smallEtaleBaseChange (closedFibreInclusion A f)).obj (terminal X.Etale))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    Function.Injective (smallEtaleGlobalSectionsMapAt.{u, v} (closedFibreInclusion A f) g F) :=
  injective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianPair.{u, v}
    (IsLocalRing.maximalIdeal A) f (henselianPair_maximalIdeal A) g F

/-- **[Stacks, Tag 0A3S], granted compatible presenting families.**  For `A` a henselian local
ring and `f : X ⟶ Spec A` proper, restriction of global sections of a sheaf of sets on the small
étale site of `X` to the closed fibre is bijective, provided every global section of the inverse
image admits a compatible presenting family.

Injectivity is unconditional; surjectivity is
`Stacks.EtaleCohomology.surjective_smallEtaleGlobalSectionPullback_of_exists_compatible`. -/
public theorem bijective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianLocalRing
    (hcompat : ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
      (t : ((smallEtaleInverseImage.{u, v} (closedFibreInclusion A f)).obj F).obj.obj
        (op (terminal (closedFibre A f).Etale))),
      ∃ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
        (⨆ j, smallEtaleImage (W j)) = ⊤ ∧ SmallEtaleCompatible F W s ∧
          ∀ j, ((smallEtaleInverseImage.{u, v} (closedFibreInclusion A f)).obj F).obj.map
                (terminal.from ((smallEtaleBaseChange
                  (closedFibreInclusion A f)).obj (W j))).op t
              = smallEtaleSectionPullback.{u, v} (closedFibreInclusion A f) F (W j) (s j))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
    (g : terminal (closedFibre A f).Etale ⟶
      (smallEtaleBaseChange (closedFibreInclusion A f)).obj (terminal X.Etale)) :
    Function.Bijective (smallEtaleGlobalSectionsMapAt.{u, v} (closedFibreInclusion A f) g F) :=
  ⟨injective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianLocalRing.{u, v} A f g F,
    (surjective_smallEtaleGlobalSectionsMapAt_iff.{u, v} _ g F).mpr
      (surjective_smallEtaleGlobalSectionPullback_of_exists_compatible.{u, v} _ g F (hcompat F))⟩

/-- **[Stacks, Tag 0A3S], granted compatible presenting families.**  Let `A` be a henselian local
ring, let `f : X ⟶ Spec A` be proper and let `X₀ = X ×_{Spec A} Spec κ(A)` be the fibre over the
closed point.  Then the canonical comparison
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison` is an isomorphism:
`Γ(X, F) = Γ(X₀, F|_{X₀})` for every sheaf of sets `F` on the small étale site of `X`, naturally
in `F`.

Injectivity is proved from henselianity of `A` and closedness of `f` alone.  What `hcompat`
supplies is agreement, on the pairwise fibre products, of the sections in a family presenting a
global section of `F|_{X₀}`;  see the module documentation.  [Stacks, Tag 0A3S] with no
hypothesis, which carries the tag, is
`Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_isProper`. -/
public theorem isIso_globalSectionsComparison_closedFibre_of_henselianLocalRing
    (hcompat : ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
      (t : ((smallEtaleInverseImage.{u, v} (closedFibreInclusion A f)).obj F).obj.obj
        (op (terminal (closedFibre A f).Etale))),
      ∃ (α : Type (u + 1)) (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j))),
        (⨆ j, smallEtaleImage (W j)) = ⊤ ∧ SmallEtaleCompatible F W s ∧
          ∀ j, ((smallEtaleInverseImage.{u, v} (closedFibreInclusion A f)).obj F).obj.map
                (terminal.from ((smallEtaleBaseChange
                  (closedFibreInclusion A f)).obj (W j))).op t
              = smallEtaleSectionPullback.{u, v} (closedFibreInclusion A f) F (W j) (s j)) :
    IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (closedFibreInclusion A f)).val :=
  (isIso_globalSectionsSmallEtaleInverseImageComparison_iff.{u, v} _).mpr fun F g ↦
    bijective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianLocalRing.{u, v}
      A f hcompat F g

end Stacks.EtaleCohomology

end
