module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreStalkwise

/-!
# Stacks 0DJZ with its Tor clause reduced to a covering of the stalks

Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, write `S = Spec R` and
`S₀ = Spec (R/I)`, and let `f : X ⟶ S` be proper, flat and locally of finite presentation. Stacks
0DJZ says that a pseudo-coherent object `E` of `D(𝒪_X)` whose derived restriction to
`X₀ = S₀ ×_S X` is `S₀`-perfect is itself `S`-perfect.

`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreStalkwise` states that
lemma with its Tor clause carried as
`AlgebraicGeometry.Scheme.Hom.UniformStalkTorAmplitudeFromClosedFibre`, which asks for **one**
interval bounding the Tor amplitude of the stalk at *every* point of `X`. This module carries it
instead as a bound that is uniform only on each member of an open covering of `X`. That is a
weaker demand, so the lemma stated on top of it is stronger; and it is the shape the source's
proof produces, which reaches an interval one affine chart at a time.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.ChartwiseStalkTorAmplitudeFromClosedFibre`: **the residual of
  Stacks 0DJZ, at the stalks, chart by chart.** It asks for an open covering of `X` and, on each
  member, a single interval containing the Tor amplitude of the stalk at every point of that
  member of `E` read over `f^{-1}𝒪_S`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.chartwiseStalkTorAmplitudeFromClosedFibre_of_uniform`: the uniform
  residual implies the chartwise one, so the latter is the weaker hypothesis.
* `AlgebraicGeometry.Scheme.Hom.locallyFiniteTorDimensionFromClosedFibre_of_chartwiseStalkBound`:
  the chartwise residual implies the sheaf-level Tor clause, for every family of certificates
  pinned to the genuine tensor product of sheaves of modules.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_closedFibre_of_chartwiseStalkBound`:
  **Stacks 0DJZ carrying the chartwise residual.**

## Why the covering is not collapsed to one interval

The source does collapse it: its covering is finite, so the finitely many intervals
`[a_i - d_i, b_i]` combine into one and the bound it reaches is uniform on the whole of `X`. The
covering step that makes the covering finite is, in this namespace,
`exists_finset_affineOpens_mvPolynomial_surjective_chartHom_of_universallyClosed`, from
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonChart`.

Collapsing is nonetheless unnecessary here, and carrying the uncollapsed form is what makes the
statement stronger. The Tor conjunct of relative perfectness is
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension`, which is itself stated as an open
covering with the interval existentially quantified *per member*; and
`locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover`, in this namespace,
is an `Iff` at exactly that shape, with the index type an arbitrary `Type u` and no finiteness
asked for. So the passage to the sheaf-level clause consumes a per-member bound directly, and a
consumer that only ever establishes one interval per chart never has to produce the global
minimum and maximum.

The uniform form is not discarded: `chartwiseStalkTorAmplitudeFromClosedFibre_of_uniform` derives
the chartwise residual from it by the one-member covering of `X` by itself, which is the
measurement that the chartwise form is the weaker of the two.

## The lemma itself

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`.

## References

* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 20.48.8 (09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

/-- The stalk ring of the inverse-image ringed space of `f` is commutative, at every point.

The sibling module
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreStalkwise`
seats the same fact as a `local instance`, whose attribute does not reach this module, so it is
re-seated here under a name of its own. -/
local instance commRing_stalk_inverseImage_spec_chartwise (y : X) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base)).obj y)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-- **The residual of Stacks 0DJZ, at the stalks, chart by chart.** Given a pseudo-coherent `E`
whose derived restriction to the closed fibre is `S₀`-perfect, and given that every point of `X`
specializes into the closed fibre, there is an open covering of `X` and, on each member, a single
interval containing the Tor amplitude of the stalk at every point of that member of `E` read over
`f^{-1}𝒪_S`.

This is weaker than `AlgebraicGeometry.Scheme.Hom.UniformStalkTorAmplitudeFromClosedFibre`, which
asks for one interval on the whole of `X`; see
`chartwiseStalkTorAmplitudeFromClosedFibre_of_uniform`. It is the shape the source's proof of the
Tor clause produces, which bounds the amplitude one affine chart at a time. -/
public def ChartwiseStalkTorAmplitudeFromClosedFibre [Flat f] [LocallyOfFinitePresentation f]
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding)) : Prop :=
  ∀ E : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
      (closedFibreToBase f I).IsPerfectRelativeTo D₀
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (closedFibreToTotal f I).toLRSHom.toShHom).obj E) →
        (∀ x : X, ∃ x₀ : X, x ⤳ x₀ ∧ x₀ ∈ Set.range (closedFibreToTotal f I).base) →
          ∃ (J : Type u) (U : J → TopologicalSpace.Opens
              (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier),
            iSup U = ⊤ ∧ ∀ j : J, ∃ a b : ℤ, ∀ y : X, y ∈ U j →
              HasTorAmplitudeCanonical
                (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
                  (structureSheafOfRings.{u}
                    (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace
                      f.base)).obj y))
                ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                    (structureSheafOfRings.{u}
                      (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace
                        f.base)) y).mapDerivedCategory.obj
                  ((derivedScalarRestriction f).obj E)) a b

/-- **The uniform residual of Stacks 0DJZ implies the chartwise one.** The covering is the
one-member covering of `X` by itself, on which a bound holding at every point of `X` is in
particular a bound uniform on that member.

This is the measurement that `ChartwiseStalkTorAmplitudeFromClosedFibre` is the weaker of the two
residuals, and hence that the lemma carrying it is the stronger statement. -/
public theorem chartwiseStalkTorAmplitudeFromClosedFibre_of_uniform
    [Flat f] [LocallyOfFinitePresentation f]
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (h : UniformStalkTorAmplitudeFromClosedFibre f I D₀) :
    ChartwiseStalkTorAmplitudeFromClosedFibre f I D₀ := by
  intro E hE hE₀ hspec
  obtain ⟨a, b, hamp⟩ := h E hE hE₀ hspec
  exact ⟨PUnit.{u + 1}, fun _ => ⊤,
    le_antisymm le_top fun z _ =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨PUnit.unit, trivial⟩,
    fun _ => ⟨a, b, fun y _ => hamp y⟩⟩

/-- **The chartwise residual of Stacks 0DJZ implies the sheaf-level Tor clause**, for every family
of certificates pinned to the genuine tensor product of sheaves of modules.

This is Stacks 09U9 for the Tor clause of relative perfectness, namely
`locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover` in this namespace,
read from right to left at the covering the residual supplies. No finiteness of the covering is
used, and none is asked for. -/
public theorem locallyFiniteTorDimensionFromClosedFibre_of_chartwiseStalkBound
    [Flat f] [LocallyOfFinitePresentation f]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (h : ChartwiseStalkTorAmplitudeFromClosedFibre f I D₀) :
    LocallyFiniteTorDimensionFromClosedFibre f I D D₀ :=
  fun E hE hE₀ hspec =>
    (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f D hD E).mpr
      (h E hE hE₀ hspec)

/-- **Stacks 0DJZ carrying the chartwise residual.** Let `R` be a ring, let `I` be an ideal
contained in the Jacobson radical of `R`, let `f : X ⟶ Spec R` be proper, flat and locally of
finite presentation, and let `X₀ = Spec (R/I) ×_{Spec R} X`. If `E` is a pseudo-coherent object of
`D(𝒪_X)` whose derived restriction to `X₀` is `Spec (R/I)`-perfect, then `E` is `Spec R`-perfect.

This is `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_closedFibre_of_uniformStalkBound`
with its carried hypothesis weakened from one interval on the whole of `X` to one interval per
member of an open covering. The family of certificates on `Spec R` is pinned to the genuine tensor
product of sheaves of modules, as it is there.

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`. -/
public theorem isPerfectRelativeTo_of_closedFibre_of_chartwiseStalkBound [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (hI : I ≤ (⊥ : Ideal R).jacobson)
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (hTor : ChartwiseStalkTorAmplitudeFromClosedFibre f I D₀)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo D₀
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo D E :=
  isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre f I hI D D₀
    (locallyFiniteTorDimensionFromClosedFibre_of_chartwiseStalkBound f I D hD D₀ hTor) E hE hE₀

end AlgebraicGeometry.Scheme.Hom

end
