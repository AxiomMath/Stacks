module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.HenselianNonClosedPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteResidueFieldBound
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteTrdegBound

/-!
# The vanishing above `d_V` in Stacks 0DC6, reduced to two theorems of Gabber

Of the three inputs of `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_inputs`,
input (2) is proved for every `n` (`AlgebraicGeometry.Scheme.trdegVanishingBound`), and input (3)
is proved for every base of Stacks 0DC6 from Travaux de Gabber, Exposé XVIII-A, Corollary 1.2
(`AlgebraicGeometry.Scheme.FractionFieldVanishingBound`): at the closed point by
`AlgebraicGeometry.Scheme.isTorsionVanishingBound_residueField_closedPoint`, elsewhere by
`AlgebraicGeometry.Scheme.isTorsionVanishingBound_residueField_of_ne_closedPoint`. This file
assembles them: for every base `S` of Stacks 0DC6 and every `n` invertible on `S`, the vanishing
`GabberVanishing S n` follows from Exposé XVIII-A, Lemma 2.2
(`AlgebraicGeometry.Scheme.LocalToGlobalVanishingBound n`) and Corollary 1.2. Over a field neither
is needed (`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_field`).

Neither Lemma 2.2 nor Corollary 1.2 is proved in this library; both rest on Gabber's affine
Lefschetz theorem (Travaux de Gabber, Exposé XV, 1.2.4).

## Main results

* `AlgebraicGeometry.Scheme.residueFieldVanishingBound_of_fractionFieldVanishingBound`: input (3)
  for a henselian Noetherian local base with finite or separably closed residue field, from
  Corollary 1.2.
* `Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_localToGlobal_of_fractionField`:
  `GabberVanishing S n` from Lemma 2.2 and Corollary 1.2, for every base of Stacks 0DC6.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- An integer invertible on `S ≅ Spec A` is invertible in `A`. -/
lemma isUnit_natCast_of_iso_spec {S : Scheme.{u}} {A : Type u} [CommRing A]
    (e : S ≅ Spec (.of A)) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) : IsUnit (n : A) := by
  have h := (hn.map e.inv.appTop.hom).map (Scheme.ΓSpecIso (.of A)).hom.hom
  simpa only [map_natCast] using h

/-- A natural number that is a unit in a nontrivial ring is positive. -/
private lemma pos_of_isUnit_natCast {A : Type u} [CommRing A] [Nontrivial A] {n : ℕ}
    (h : IsUnit (n : A)) : 0 < n :=
  Nat.pos_of_ne_zero fun h0 => by simp [h0] at h

/-- **Input (3) of Stacks 0DC6 from Travaux de Gabber, Exposé XVIII-A, Corollary 1.2.** Let `A`
be a henselian Noetherian local ring whose residue field is finite or separably closed, `S ≅ Spec
A`, and `n` invertible in `A`. Granting Corollary 1.2, every residue field of `S` has étale
cohomology with coefficients killed by `n` bounded by `1 + 2 dim S`. -/
theorem residueFieldVanishingBound_of_fractionFieldVanishingBound {S : Scheme.{u}} (A : Type u)
    [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    (hk : Finite (IsLocalRing.ResidueField A) ∨ IsSepClosed (IsLocalRing.ResidueField A))
    (e : S ≅ Spec (.of A)) {n : ℕ} (hnA : IsUnit (n : A))
    (h : FractionFieldVanishingBound.{u} n) : ResidueFieldVanishingBound S n := by
  exact residueFieldVanishingBound_of_forall_ne A hk e (pos_of_isUnit_natCast hnA) fun s hs =>
    isTorsionVanishingBound_residueField_of_ne_closedPoint A hk e hnA h s hs

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

/-- **The vanishing above `d_V` from Gabber's theorems.** For every base `S` of Stacks 0DC6 and
every `n` invertible on `S`, Travaux de Gabber, Exposé XVIII-A, Lemma 2.2
(`LocalToGlobalVanishingBound n`) and Corollary 1.2 (`FractionFieldVanishingBound n`) give the
vanishing `GabberVanishing S n`: input (2) is `trdegVanishingBound`, input (3) is
`residueFieldVanishingBound_of_fractionFieldVanishingBound`. Over a field the vanishing holds
outright (`gabberVanishing_of_field`). -/
theorem gabberVanishing_of_localToGlobal_of_fractionField {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (h₁ : LocalToGlobalVanishingBound.{u} n) (h₃ : FractionFieldVanishingBound.{u} n) :
    GabberVanishing S n := by
  rcases id hS with ⟨k, _, hk, ⟨e⟩⟩ | ⟨k, _, hk, ⟨e⟩⟩ | ⟨A, _, _, _, hk, ⟨e⟩⟩ |
    ⟨A, _, _, _, hk, ⟨e⟩⟩
  · exact gabberVanishing_of_field k (Or.inl hk) e
      (pos_of_isUnit_natCast (isUnit_natCast_of_iso_spec e hn))
  · exact gabberVanishing_of_field k (Or.inr hk) e
      (pos_of_isUnit_natCast (isUnit_natCast_of_iso_spec e hn))
  · exact gabberVanishing_of_inputs hS hn h₁ (trdegVanishingBound n)
      (residueFieldVanishingBound_of_fractionFieldVanishingBound A (Or.inr hk) e
        (isUnit_natCast_of_iso_spec e hn) h₃)
  · exact gabberVanishing_of_inputs hS hn h₁ (trdegVanishingBound n)
      (residueFieldVanishingBound_of_fractionFieldVanishingBound A (Or.inl hk) e
        (isUnit_natCast_of_iso_spec e hn) h₃)

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
