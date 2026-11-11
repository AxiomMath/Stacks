module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformOpenImmersion

/-!
# Dominating a proper modification of a Noetherian scheme by blowups at closed points

Let `X` be a Noetherian scheme, `T` a finite set of closed points of `X` whose local rings are
regular of dimension two, and `U` the complement of `T`. A proper morphism `f : Y ⟶ X` which is
an isomorphism over `U` is dominated by a sequence of blowups at closed points lying over `T`.
This is [Stacks, Tag 0AHI].

`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_factorization` proves this over two inputs:
the local splitting of [Stacks, Tag 0AGT], and a `U`-admissible blowup dominating the given
morphism, which is [Stacks, Tag 081T]. Both are supplied here. For the second, over a Noetherian
base [Stacks, Tag 080Y] holds for every open
(`AlgebraicGeometry.cartierBoundaryReduction`) and [Stacks, Tag 081S] holds for a proper
morphism, which is of finite presentation over such a base
(`AlgebraicGeometry.strictTransformOpenImmersion_of_isIso_morphismRestrict`); with these
[Stacks, Tag 081T] is `AlgebraicGeometry.exists_isAdmissibleBlowup_dominating`. The first is
`Stacks.ResolutionOfSurfaces.pointBlowupDescent`.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_isAdmissibleBlowup_dominating_of_isNoetherian`:
  [Stacks, Tag 081T] over a Noetherian base, unconditionally.
* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_factorization_of_isNoetherian`:
  [Stacks, Tag 0AHI] over the local splitting of [Stacks, Tag 0AGT] alone.
* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_factorization_of_isProper`:
  [Stacks, Tag 0AHI], unconditionally.

## References

* [Stacks Project, Tag 0AHI](https://stacks.math.columbia.edu/tag/0AHI)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **[Stacks, Tag 081T] over a Noetherian base.** A proper morphism `f : Y ⟶ X` to a Noetherian
scheme which is an isomorphism over an open `U` is dominated by a `U`-admissible blowup. -/
theorem exists_isAdmissibleBlowup_dominating_of_isNoetherian {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] (f : Y ⟶ X) [IsProper f] (U : X.Opens)
    [IsIso (f ∣_ U)] :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∃ h : X' ⟶ Y, h ≫ f = b := by
  have hU : IsCompact (U : Set X) := NoetherianSpace.isCompact _
  have : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  exact exists_isAdmissibleBlowup_dominating f U (cartierBoundaryReduction U hU)
    (strictTransformOpenImmersion_of_isIso_morphismRestrict f U hU)

/-- **[Stacks, Tag 0AHI] over the local splitting of [Stacks, Tag 0AGT].** Let `X` be a
Noetherian scheme, `T` a finite set of closed points of `X` whose local rings are regular of
dimension two, and `U` the complement of `T`. A proper morphism `f : Y ⟶ X` which is an
isomorphism over `U` is dominated by a sequence of blowups at closed points lying over `T`. The
hypothesis `descent` is the local splitting of [Stacks, Tag 0AGT]. -/
theorem exists_pointBlowupChain_factorization_of_isNoetherian
    (descent : ∀ (Y : Scheme.{u}) (S : Finset Y) (J : Y.IdealSheafData),
      (∀ y ∈ S, IsClosed ({y} : Set Y)) →
      (∀ y ∈ S, IsRegularLocalRing (Y.presheaf.stalk y)) →
      (∀ y ∈ S, ringKrullDim (Y.presheaf.stalk y) = 2) →
      (J.support : Set Y) ⊆ (S : Set Y) →
      ∀ y ∈ (J.support : Set Y), ∀ hy : IsClosed ({y} : Set Y),
      ∀ M : Y.IdealSheafData, M = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ →
        ∃ (d : ℕ) (S' : Finset (blowUp M)) (J' : (blowUp M).IdealSheafData),
          exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) ∧
          (∀ z ∈ S', IsClosed ({z} : Set (blowUp M))) ∧
          (∀ z ∈ S', IsRegularLocalRing ((blowUp M).presheaf.stalk z)) ∧
          (∀ z ∈ S', ringKrullDim ((blowUp M).presheaf.stalk z) = 2) ∧
          (J'.support : Set (blowUp M)) ⊆ (S' : Set (blowUp M)) ∧
          (∀ z ∈ S', (blowUpToBase M).base z ∈ S) ∧
          totalColength J' S' < totalColength J S)
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X] (T : Finset X) (U : X.Opens)
    (hU : (U : Set X) = (T : Set X)ᶜ)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hregular : ∀ x ∈ T, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2)
    (f : Y ⟶ X) [IsProper f] [IsIso (f ∣_ U)] :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X), PointBlowupChain X (T : Set X) Z p ∧
      ∃ g : Z ⟶ Y, g ≫ f = p :=
  exists_pointBlowupChain_factorization descent T U hU hclosed hregular hdim f
    (exists_isAdmissibleBlowup_dominating_of_isNoetherian f U)

/-- **Stacks Project, Tag 0AHI.** A proper morphism to a Noetherian scheme which is an
isomorphism away from a finite set `T` of closed points whose local rings are regular of dimension
two is dominated by a sequence of blowups at closed points lying over `T`: the composite of the
sequence factors through it.

The proof follows the source. By [Stacks, Tag 081T]
(`exists_isAdmissibleBlowup_dominating_of_isNoetherian`) a `U`-admissible blowup of `X` in an
ideal `𝓘` with `𝒪_X / 𝓘` supported on `T` dominates `f`. By [Stacks, Tag 0AHH]
(`exists_pointBlowupChain_isEffectiveCartierDivisor` with `pointBlowupDescent`) a sequence of
blowups at closed points over `T` makes `𝓘` invertible, and the universal property of blowing up
([Stacks, Tag 0806]) factors the composite through the blowup in `𝓘`, hence through `Y`. -/
@[stacks 0AHI "a proper morphism to a Noetherian scheme which is an isomorphism away from a \
finite set of closed points with regular two-dimensional local rings is dominated by a finite \
sequence of blowups at closed points lying over that set"]
theorem exists_pointBlowupChain_factorization_of_isProper {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] (T : Finset X) (U : X.Opens)
    (hU : (U : Set X) = (T : Set X)ᶜ)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hregular : ∀ x ∈ T, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2)
    (f : Y ⟶ X) [IsProper f] [IsIso (f ∣_ U)] :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X), PointBlowupChain X (T : Set X) Z p ∧
      ∃ g : Z ⟶ Y, g ≫ f = p :=
  exists_pointBlowupChain_factorization_of_isNoetherian pointBlowupDescent T U hU hclosed
    hregular hdim f

end Stacks.ResolutionOfSurfaces

end
