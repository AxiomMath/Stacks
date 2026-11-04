module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteFieldVanishing

/-!
# Vanishing above `d_X` over a local ring of dimension zero

Let `A` be a local ring of Krull dimension zero whose residue field `κ` is finite or separably
closed, let `S ≅ Spec A`, and let `f : X ⟶ S` be locally of finite type with `X` quasi-compact.
With `d_X = 1 + 2 dim(S) + sup_x (trdeg_{κ(f(x))} κ(x) + 2 dim 𝒪_{X,x})` the number of
Stacks 0DC6, for every abelian torsion sheaf `𝓖` on `X_ét`,

`H^p_ét(X, 𝓖) = 0` for `p > d_X`.

Such an `A` is henselian (it is Artinian when Noetherian), so this is the dimension-zero case of
the bases of types (3) and (4) of Stacks 0DC6: the spectrum of a strictly henselian local ring,
or of a henselian local ring with finite residue field. In positive dimension the statement is
Gabber's theorem.

## The proof

As `A` has dimension zero and is local, `Spec A` is a single point, so the closed immersion
`Spec κ ⟶ Spec A` is surjective. Its base change `i : X₀ = X ×_S Spec κ ⟶ X` is then a surjective
closed immersion, hence a universal homeomorphism
(`Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective`), and restriction along
`i` is bijective on étale cohomology by Stacks 03SI
(`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism`).
The inverse image `i⁻¹𝓖` is again torsion
(`Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage`).

The scheme `X₀` is quasi-compact and locally of finite type over the field `κ`, and
`dim X₀ ≤ dim X`. Since `dim S = 0`, every term `1 + 2 dim 𝒪_{X,x}` is at most `d_X < p`, so
`2 dim X + 1 < p`. Finally `cd(κ) ≤ 1`, and
`AlgebraicGeometry.subsingleton_H_of_topologicalKrullDim_le` (`cd(X₀) ≤ 2 dim(X₀) + cd(κ)`) gives
the vanishing on `X₀`, hence on `X`.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.subsingleton_H_of_ringKrullDim_eq_zero`.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- A local ring of Krull dimension zero has a single prime ideal. -/
theorem subsingleton_primeSpectrum_of_ringKrullDim_eq_zero (A : Type*) [CommRing A]
    [IsLocalRing A] (hdim : ringKrullDim A = 0) : Subsingleton (PrimeSpectrum A) := by
  have : Ring.KrullDimLE 0 A := ⟨hdim.le⟩
  have hx : ∀ z : PrimeSpectrum A, z = IsLocalRing.closedPoint A := fun z =>
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal' z.2))
  exact ⟨fun x y => (hx x).trans (hx y).symm⟩

/-- Over a base of dimension zero, `1 + 2 dim 𝒪_{X,x} ≤ d_X` for every point `x`. -/
theorem one_add_two_mul_ringKrullDim_stalk_le_etaleCohomologyBound {X S : Scheme.{u}}
    (f : X ⟶ S) (hS : topologicalKrullDim S = 0) (x : X) :
    (1 : WithBot ℕ∞) + 2 * ringKrullDim (X.presheaf.stalk x) ≤ f.etaleCohomologyBound := by
  let tr : WithBot ℕ∞ := letI := (f.residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (S.residueField (f.base x))
      (X.residueField x)) : WithBot ℕ∞)
  have hterm : tr + 2 * ringKrullDim (X.presheaf.stalk x) ≤
      0 ⊔ ⨆ y : X, (letI := (f.residueFieldMap y).hom.toAlgebra
        (Cardinal.toENat (Algebra.trdeg (S.residueField (f.base y))
          (X.residueField y)) : WithBot ℕ∞) +
            2 * ringKrullDim (X.presheaf.stalk y)) :=
    le_sup_of_le_right (le_iSup_of_le x le_rfl)
  change _ ≤ 1 + 2 * topologicalKrullDim S + _
  rw [hS, mul_zero, add_zero]
  exact add_le_add le_rfl (le_trans (le_add_of_nonneg_left (by simp [tr])) hterm)

/-- Over a base of dimension zero, `1 ≤ d_X`. -/
theorem one_le_etaleCohomologyBound {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : topologicalKrullDim S = 0) : (1 : WithBot ℕ∞) ≤ f.etaleCohomologyBound := by
  change _ ≤ 1 + 2 * topologicalKrullDim S + _
  rw [hS, mul_zero, add_zero]
  exact le_add_of_nonneg_right le_sup_left

/-- Over a base of dimension zero, if `d_X < p` then every local ring of `X` has dimension at
most `(p - 2) / 2`. -/
theorem ringKrullDim_stalk_le_of_etaleCohomologyBound_lt {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : topologicalKrullDim S = 0) {p : ℕ} (hp : f.etaleCohomologyBound < p) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ ((p - 2) / 2 : ℕ) := by
  have hlt := lt_of_le_of_lt
    (one_add_two_mul_ringKrullDim_stalk_le_etaleCohomologyBound f hS x) hp
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
    ringKrullDim_nonneg_of_nontrivial
  have hrd : ringKrullDim (X.presheaf.stalk x) ≤ (p : WithBot ℕ∞) :=
    calc ringKrullDim (X.presheaf.stalk x)
        ≤ 2 * ringKrullDim (X.presheaf.stalk x) := by
          rw [two_mul]
          exact le_add_of_nonneg_left h0
      _ ≤ 1 + 2 * ringKrullDim (X.presheaf.stalk x) :=
          le_add_of_nonneg_left zero_le_one
      _ ≤ p := hlt.le
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ringKrullDim (X.presheaf.stalk x) = r := by
    induction hx : ringKrullDim (X.presheaf.stalk x) using WithBot.recBotCoe with
    | bot =>
      rw [hx] at h0
      exact absurd h0 (by simp)
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        rw [hx, ← WithBot.coe_natCast] at hrd
        exact absurd (top_le_iff.1 (WithBot.coe_le_coe.1 hrd)) (ENat.coe_ne_top p)
      | coe r => exact ⟨r, rfl⟩
  rw [hr] at hlt ⊢
  have : 1 + 2 * r < p := by exact_mod_cast hlt
  exact_mod_cast (by omega : r ≤ (p - 2) / 2)

/-- A finite or separably closed field has étale cohomological dimension at most one. -/
theorem etaleCohomologicalDimension_spec_le_one (K : Type u) [Field K]
    (hk : Finite K ∨ IsSepClosed K) : Scheme.etaleCohomologicalDimension (Spec (.of K)) ≤ 1 := by
  rcases hk with hk | hk
  · exact Scheme.etaleCohomologicalDimension_spec_le_one_of_finite K
  · exact (Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed K).trans zero_le_one

/-- **Vanishing above `d_X` over a local ring of dimension zero** (Stacks 0DC6, base types (3)
and (4) in dimension zero). Let `A` be a local ring of Krull dimension zero whose residue field is
finite or separably closed, `S ≅ Spec A`, and `f : X ⟶ S` locally of finite type with `X`
quasi-compact. Then `H^p_ét(X, 𝓖) = 0` for every abelian torsion sheaf `𝓖` on `X_ét` and every
`p > d_X`, the bound `AlgebraicGeometry.Scheme.Hom.etaleCohomologyBound f`. -/
theorem subsingleton_H_of_ringKrullDim_eq_zero {S : Scheme.{u}} (A : Type u) [CommRing A]
    [IsLocalRing A] (hdim : ringKrullDim A = 0)
    (hk : Finite (IsLocalRing.ResidueField A) ∨ IsSepClosed (IsLocalRing.ResidueField A))
    (e : S ≅ Spec (.of A)) (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X] (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (p : ℕ)
    (hp : f.etaleCohomologyBound < p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} G p) := by
  set κ := IsLocalRing.ResidueField A
  have hpt : Subsingleton (Spec (.of A)) :=
    subsingleton_primeSpectrum_of_ringKrullDim_eq_zero A hdim
  let ρ : Spec (.of κ) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  have : IsClosedImmersion ρ :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let g : Spec (.of κ) ⟶ S := ρ ≫ e.inv
  have : Surjective g := by
    have : Surjective ρ :=
      ⟨fun x => ⟨IsLocalRing.closedPoint κ, Subsingleton.elim _ _⟩⟩
    infer_instance
  let X₀ := pullback f g
  let i : X₀ ⟶ X := pullback.fst f g
  have : UniversalHomeomorphism i :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective i
      i.surjective
  have : CompactSpace X₀ := i.isClosedEmbedding.compactSpace
  have hdimS : topologicalKrullDim S = 0 := by
    have hhomeo : IsHomeomorph e.hom.base :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph
    rw [hhomeo.topologicalKrullDim_eq]
    change topologicalKrullDim (PrimeSpectrum A) = 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
  have hp2 : 2 ≤ p := by
    have h : (1 : WithBot ℕ∞) < p := lt_of_le_of_lt (one_le_etaleCohomologyBound f hdimS) hp
    exact_mod_cast h
  have hdimX₀ : topologicalKrullDim X₀ ≤ ((p - 2) / 2 : ℕ) := by
    refine i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans ?_
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact iSup_le (ringKrullDim_stalk_le_of_etaleCohomologyBound_lt f hdimS hp)
  have hcd := etaleCohomologicalDimension_spec_le_one κ hk
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hcd)
  rw [← hc] at hcd
  have hc1 : c ≤ 1 := by exact_mod_cast hcd
  have h₀ : Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, u + 1} i).obj G) p) := by
    refine subsingleton_H_of_topologicalKrullDim_le κ ((p - 2) / 2) X₀ (pullback.snd f g) hdimX₀
      _ (Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage.{u, u + 1} i G hG)
      p ?_
    rw [← hc]
    exact_mod_cast (by omega : 2 * ((p - 2) / 2) + c < p)
  exact (Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{
    u, u + 1, u + 1} i G p).1.subsingleton

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
