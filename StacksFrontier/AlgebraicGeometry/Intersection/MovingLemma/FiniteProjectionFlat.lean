module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization

/-!
# A dominant quasi-finite morphism of nonsingular varieties is flat

Let `π : X ⟶ Y` be a dominant locally quasi-finite morphism of varieties over a field, for
instance a finite surjective one, with `X` and `Y` nonsingular. Then `π` is flat. This is miracle
flatness (Tag 00R4) at each point: the local ring `𝒪_{X, x}` is regular, hence Cohen–Macaulay, the
stalk map is quasi-finite, and the two local rings have the same dimension by the dimension
formula (`AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite`).

This is the flatness the moving lemma uses for the finite projection `π : X ⟶ 𝐏^n` of the proof
of Tag 0B0E, and for its restriction to an open subset of the nonsingular locus (Remark 0B61): it
makes the flat pullback `π^*` of chapter 42 available along `π`.

## Main results

* `AlgebraicGeometry.relativeDimension_eq_of_locallyQuasiFinite`: a locally quasi-finite
  morphism over the base does not change the relative dimension of a point.
* `AlgebraicGeometry.flat_of_locallyQuasiFinite_of_isRegular`: the flatness.

## References

* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)

/-- **A locally quasi-finite morphism over the base does not change the relative dimension of a
point.** Its fibres have dimension zero, so the residue-field extensions have transcendence degree
zero. -/
public theorem relativeDimension_eq_of_locallyQuasiFinite [LocallyOfFiniteType sY] (π : X ⟶ Y)
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] (x : X) :
    relativeDimension (fieldChowSituation k).dimensionFunction (π ≫ sY) x =
      relativeDimension (fieldChowSituation k).dimensionFunction sY (π.base x) := by
  have h0 : Cardinal.toNat (residueTrdeg π x) ≤ 0 :=
    toNat_residueTrdeg_le_of_relativeDimension π 0
      ((locallyQuasiFinite_iff_relativeDimension_zero π).mp inferInstance) x
  rw [relativeDimension_comp_eq_add_trdeg (fieldChowSituation k).dimensionFunction sY π x]
  omega

/-- **A dominant locally quasi-finite morphism of nonsingular varieties is flat.** At every point
the stalk map is a quasi-finite local homomorphism of regular local rings, and the two local rings
have the same dimension (`AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite`, the
target being universally catenary), so it is flat by miracle flatness (Tag 00R4). -/
public theorem flat_of_locallyQuasiFinite_of_isRegular [LocallyOfFiniteType sY] [IsIntegral X]
    [IsIntegral Y] (π : X ⟶ Y) [LocallyOfFiniteType π] [LocallyQuasiFinite π] [IsDominant π]
    (hX : IsRegular X) (hY : IsRegular Y) : Flat π := by
  have hYn : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hcat := Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k sY
  refine Flat.of_stalkMap (f := π) fun x ↦ ?_
  have hXs : IsLocallyNoetherian X ∧ ∀ z : X, IsRegularLocalRing (X.presheaf.stalk z) :=
    ((isRegular_tfae X).out 1 2).mp hX
  have hYs : IsLocallyNoetherian Y ∧ ∀ z : Y, IsRegularLocalRing (Y.presheaf.stalk z) :=
    ((isRegular_tfae Y).out 1 2).mp hY
  have := hXs.2 x
  have := hYs.2 (π.base x)
  exact flat_stalkMap_of_quasiFiniteAt π x (π.quasiFiniteAt x)
    (ringKrullDim_stalk_eq_of_locallyQuasiFinite π hcat x)

end AlgebraicGeometry

end
