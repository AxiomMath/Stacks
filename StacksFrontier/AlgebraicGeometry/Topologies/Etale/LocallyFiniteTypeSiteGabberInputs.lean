module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberVanishing

/-!
# The three inputs of the vanishing above `d_V` in Stacks 0DC6

Stacks 0DC6 takes the vanishing `H^p_ét(V, 𝓖) = 0` for `p > d_V`
(`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.GabberVanishing`) from "[Travaux de Gabber,
Exposé XVIII-A, Corollary 1.2 and Lemma 2.2] and elementary arguments on cohomological dimensions
of fields". This file isolates the three inputs as statements and proves that together they give
the vanishing, for every base `S` of the example and every `n` invertible on `S`:

1. `LocalToGlobalVanishingBound n` — **Exposé XVIII-A, Lemma 2.2**, for sheaves killed by `n`: on a
   Noetherian scheme `X` on which `n` is invertible, if `c(x)` bounds the étale cohomology of
   `Spec κ(x)` with coefficients killed by `n` for every `x ∈ X`, then
   `sup_x (c(x) + 2 dim 𝒪_{X, x})` bounds the étale cohomology of `X` with such coefficients.
2. `TrdegVanishingBound n` — **Serre's bound** `cd_ℓ(L) ≤ cd_ℓ(K) + trdeg_K(L)` for a field
   extension `L/K` (Cohomologie galoisienne, Chapter II, §4.2), for coefficients killed by `n`
   with `n` invertible in `K`.
3. `ResidueFieldVanishingBound S n` — the bound `cd_ℓ(κ(s)) ≤ 1 + 2 dim(S)` at every point `s` of
   the base: at the closed point `κ(s)` is separably closed or finite, and at a non-closed point
   this is **Exposé XVIII-A, Corollary 1.2** (`cd_ℓ(K) ≤ 2d - 1` for the fraction field `K` of a
   strictly local Noetherian domain of dimension `d > 0`), plus one for a finite residue field.

The deduction (`gabberVanishing_of_inputs`) is the source's: by (2) and (3) the residue field of
a point `v ∈ V` over `s ∈ S` has cohomology bounded by `1 + 2 dim(S) + trdeg_{κ(s)} κ(v)`, and
then (1) bounds the cohomology of `V` by
`sup_v (1 + 2 dim(S) + trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v}) ≤ d_V`.

None of the three inputs is proved in this library for a base of positive dimension: input (1)
rests on Gabber's affine Lefschetz theorem (Exposé XV) and Gabber's formal base change theorem,
input (3) on Exposé XVIII-A, Theorem 1.1, and input (2) needs the `ℓ`-cohomological dimension of
fields, where the library has only the cohomological dimension for all torsion sheaves
(`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_add_trdeg`, Stacks 0F0T), which is
not the bound needed in mixed characteristic.

## Main definitions

* `AlgebraicGeometry.Scheme.LocalToGlobalVanishingBound`: input (1).
* `AlgebraicGeometry.Scheme.TrdegVanishingBound`: input (2).
* `AlgebraicGeometry.Scheme.ResidueFieldVanishingBound`: input (3).

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_inputs`: the three inputs
  give `GabberVanishing S n`.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Astérisque 363–364 (2014)
* J.-P. Serre, *Cohomologie galoisienne*, Chapter II, §4.2
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **Input (1): Travaux de Gabber, Exposé XVIII-A, Lemma 2.2**, for coefficients killed by `n`.
For every Noetherian scheme `X` on which `n` is invertible and every function `c` such that
`c(x)` bounds the étale cohomology of `Spec κ(x)` with coefficients killed by `n`, the étale
cohomology of `X` with coefficients killed by `n` vanishes above
`sup_{x ∈ X} (c(x) + 2 dim 𝒪_{X, x})`. -/
def LocalToGlobalVanishingBound (n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], IsUnit (n : Γ(X, ⊤)) →
    ∀ c : X → WithBot ℕ∞, (∀ x, IsTorsionVanishingBound (Spec (.of (X.residueField x))) n (c x)) →
      IsTorsionVanishingBound X n (⨆ x : X, (c x + 2 * ringKrullDim (X.presheaf.stalk x)))

/-- **Input (2): the cohomological dimension of a field extension** (Serre, Cohomologie
galoisienne, Chapter II, §4.2), for coefficients killed by `n`. For a field extension `L/K` with
`n` invertible in `K`, a bound `c` for the étale cohomology of `Spec K` with coefficients killed
by `n` gives the bound `c + trdeg_K(L)` for `Spec L`. -/
def TrdegVanishingBound (n : ℕ) : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L], IsUnit (n : K) → ∀ c : WithBot ℕ∞,
    IsTorsionVanishingBound (Spec (.of K)) n c →
      IsTorsionVanishingBound (Spec (.of L)) n
        (c + (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞))

/-- **Input (3): the cohomological dimension of the residue fields of the base**: for every point
`s` of `S`, `1 + 2 dim(S)` bounds the étale cohomology of `Spec κ(s)` with coefficients killed by
`n`. For the bases of Stacks 0DC6 this is Travaux de Gabber, Exposé XVIII-A, Corollary 1.2 at the
non-closed points. -/
def ResidueFieldVanishingBound (S : Scheme.{u}) (n : ℕ) : Prop :=
  ∀ s : S, IsTorsionVanishingBound (Spec (.of (S.residueField s))) n
    (1 + 2 * topologicalKrullDim S)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

variable {S : Scheme.{u}}

/-- An integer invertible on a scheme is invertible in each of its residue fields. -/
private lemma isUnit_natCast_residueField {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) (s : S) :
    IsUnit (n : S.residueField s) := by
  simpa only [map_natCast] using (hn.map (S.presheaf.germ ⊤ s trivial).hom).map (S.residue s).hom

/-- **The vanishing above `d_V` from its three inputs.** Let `S` be a base of one of the types of
Stacks 0DC6 and `n` an integer invertible on `S`. If Exposé XVIII-A, Lemma 2.2 holds for
coefficients killed by `n` (`LocalToGlobalVanishingBound`), the bound of the cohomological
dimension of a field extension holds (`TrdegVanishingBound`), and the residue fields of `S` have
cohomology bounded by `1 + 2 dim(S)` (`ResidueFieldVanishingBound`), then for every quasi-compact
`V` locally of finite type over `S` the cohomology of `V` with coefficients killed by `n` vanishes
above `d_V`. -/
theorem gabberVanishing_of_inputs (hS : IsUnboundedDescentEtaleBase S) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (h₁ : LocalToGlobalVanishingBound.{u} n)
    (h₂ : TrdegVanishingBound.{u} n) (h₃ : ResidueFieldVanishingBound S n) :
    GabberVanishing S n := by
  intro V hV G hG p hp
  have : IsLocallyNoetherian S := hS.isLocallyNoetherian_and_nonempty_and_ne_top.1
  have : LocallyOfFiniteType V.obj.hom := V.property
  have : IsLocallyNoetherian V.obj.left := LocallyOfFiniteType.isLocallyNoetherian V.obj.hom
  have : CompactSpace V.obj.left := hV
  have : IsNoetherian V.obj.left := ⟨⟩
  have hnV : IsUnit (n : Γ(V.obj.left, ⊤)) := by
    simpa only [map_natCast] using hn.map V.obj.hom.appTop.hom
  let f := V.obj.hom
  let c : V.obj.left → WithBot ℕ∞ := fun v ↦
    1 + 2 * topologicalKrullDim S + (letI := (f.residueFieldMap v).hom.toAlgebra
      (Cardinal.toENat (Algebra.trdeg (S.residueField (f.base v)) (V.obj.left.residueField v)) :
        WithBot ℕ∞))
  have hc : ∀ v, IsTorsionVanishingBound (Spec (.of (V.obj.left.residueField v))) n (c v) :=
    fun v ↦
      letI := (f.residueFieldMap v).hom.toAlgebra
      h₂ (S.residueField (f.base v)) (V.obj.left.residueField v)
        (isUnit_natCast_residueField hn (f.base v)) _ (h₃ (f.base v))
  refine (h₁ V.obj.left hnV c hc).mono (iSup_le fun v ↦ ?_) G hG p hp
  change c v + _ ≤ 1 + 2 * topologicalKrullDim S + _
  simp only [c, add_assoc]
  gcongr
  exact le_sup_of_le_right (le_iSup_of_le v le_rfl)

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
