module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeFieldLocalSerreFamily
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteArtinianVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteBoundComp

/-!
# Stacks 0DC6 from the vanishing of étale cohomology above `d_V`

Let `S` be a base of one of the four types of Stacks 0DC6 and `n` a natural number (the order of
the finite coefficient ring `Λ`). The cohomological input of the example is the following bound,
which the source takes from Gabber's theorem on cohomological dimension (Travaux de Gabber,
Exposé XVIII-A, Corollary 1.2 and Lemma 2.2): for every quasi-compact scheme `V` locally of
finite type over `S` and every abelian sheaf `𝓖` on `V_ét` killed by `n`,

`H^p_ét(V, 𝓖) = 0` for `p > d_V = 1 + 2 dim(S) + sup_{v ∈ V} (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})`.

This file states that bound, `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.GabberVanishing`,
and deduces Stacks 0DC6 from it. The deduction is the source's: a member `V_i` of a covering in
`Cov_V` is quasi-compact and étale over `V`, so `d_{V_i} ≤ d_V`
(`AlgebraicGeometry.Scheme.Hom.etaleCohomologyBound_comp_le`), and the bound for `V_i` is the
vanishing required on `V_i`. Over a finite or a separably closed field the bound holds for every
positive `n` (`gabberVanishing_of_field`).

## Main definitions

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.GabberVanishing`: the vanishing of
  `H^p_ét(V, 𝓖)` above `d_V`, for `V` quasi-compact and locally of finite type over `S` and `𝓖`
  killed by `n`.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.etaleVanishingAboveBound_of_gabberVanishing`:
  the bound on the objects of `C` gives the bound on the members of the coverings in `Cov_V`.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.localSerre_of_gabberVanishing`: the conditions
  of Stacks 0DC1 for the family of Stacks 0DC6, for every base of the example on which the bound
  holds.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_field`: the bound over a
  finite or separably closed field.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_ringKrullDim_eq_zero`: the
  bound over a local ring of dimension zero with finite or separably closed residue field.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.localSerre_of_ringKrullDim_eq_zero`: Stacks
  0DC6 for the bases of types (3) and (4) of dimension zero.

## Implementation notes

The sheaves are abelian sheaves killed by `n` rather than sheaves of `Λ`-modules: a sheaf of
`Λ`-modules is killed by the order of `Λ`, so this is the more general statement, and it is the
form in which `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.EtaleVanishingAboveBound` consumes
it.

For `S` the spectrum of a strictly henselian Noetherian local ring, or of a henselian Noetherian
local ring with finite residue field, of positive dimension, `GabberVanishing S n` (with `n`
invertible on `S`) is Gabber's theorem, proved in
`LocallyFiniteTypeSiteGabberUnconditional.lean`
(`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing`).

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 0DC1](https://stacks.math.columbia.edu/tag/0DC1)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

variable (S : Scheme.{u})

/-- **The vanishing of étale cohomology above `d_V`** (the cohomological input of Stacks 0DC6),
for a base `S` and an integer `n`: for every quasi-compact scheme `V` locally of finite type over
`S` and every abelian sheaf `𝓖` on `V_ét` killed by `n`, `H^p_ét(V, 𝓖) = 0` for every
`p > d_V = 1 + 2 dim(S) + sup_{v ∈ V} (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})`. With `n` the order of
a finite ring `Λ` invertible on `S` this is what the source takes from Gabber's theorem on
cohomological dimension. -/
def GabberVanishing (n : ℕ) : Prop :=
  ∀ (V : LocallyFiniteTypeEtale S), IsQuasiCompact V →
    ∀ G : Sheaf V.obj.left.smallEtaleTopology AddCommGrpCat.{u + 1},
      (∀ (T : V.obj.left.Etale) (x : G.obj.obj (op T)), n • x = 0) →
        ∀ p : ℕ, V.obj.hom.etaleCohomologyBound < p → Subsingleton (Sheaf.H.{u + 1} G p)

variable {S}

/-- **The bound does not grow along the members of a covering.** If the vanishing above `d_V`
holds on every quasi-compact object of `C`, then for every quasi-compact `W` étale over a
quasi-compact `V` the cohomology of `W` vanishes above `d_V`: by
`AlgebraicGeometry.Scheme.Hom.etaleCohomologyBound_comp_le`, `d_W ≤ d_V`. -/
theorem etaleVanishingAboveBound_of_gabberVanishing [IsLocallyNoetherian S] {n : ℕ}
    (h : GabberVanishing S n) : EtaleVanishingAboveBound S n := by
  intro V _ W hW g hg G hG p hp
  have : LocallyOfFiniteType V.obj.hom := V.property
  have : IsLocallyNoetherian V.obj.left := LocallyOfFiniteType.isLocallyNoetherian V.obj.hom
  let φ : W.obj.left ⟶ V.obj.left := (forget S).map g
  have : Etale φ := hg
  have hφ : φ ≫ V.obj.hom = W.obj.hom := Over.w g.hom
  have hle : W.obj.hom.etaleCohomologyBound ≤ V.obj.hom.etaleCohomologyBound := by
    rw [← hφ]
    exact Scheme.Hom.etaleCohomologyBound_comp_le φ V.obj.hom
  exact h W hW G hG p (hle.trans_lt hp)

/-- **Stacks 0DC6, from the vanishing above `d_V`.** For `S` of one of the types of Stacks 0DC6
and `Λ` a finite ring such that `GabberVanishing S |Λ|` holds, the family `A_U` of all sheaves of
`Λ`-modules on the slices of the ringed site `(C, Λ)` of schemes locally of finite type over `S`
satisfies conditions (1), (2), (3) of Stacks 0DC1, with `B` the quasi-compact objects, `d_V` the
bound of the example and `Cov_V` the étale coverings of `V` by quasi-compact objects. The bound
is proved for every base of the example
(`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing`),
and Stacks 0DC6 is `localSerre`. -/
theorem localSerre_of_gabberVanishing (Λ : Type u) [CommRing Λ] [Finite Λ]
    (hS : IsUnboundedDescentEtaleBase S) (h : GabberVanishing S (Nat.card Λ)) :
    (∀ U, (allModules S Λ U).IsWeakSerreClass) ∧
      IsStableUnderRestriction (ringedSite S Λ) (allModules S Λ) ∧
      IsLocalOnCoverings (ringedSite S Λ) (allModules S Λ) ∧
      ∃ b : LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ),
        b.B = {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)} ∧
        (∀ V hV, ∃ d : ℕ, b.degreeBound V hV = d ∧
          ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = d) ∧
        ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V),
          (b.coverings V hV).cov 𝒰 ↔ IsQuasiCompactEtaleCovering 𝒰 :=
  have : IsLocallyNoetherian S := hS.isLocallyNoetherian_and_nonempty_and_ne_top.1
  localSerre_of_etaleVanishingAboveBound Λ hS (etaleVanishingAboveBound_of_gabberVanishing h)

/-- **The vanishing above `d_V` over a finite or separably closed field**, for every positive
`n`: the case `W = V` of `etaleVanishingAboveBound_of_field`. -/
theorem gabberVanishing_of_field (k : Type u) [Field k] (hk : Finite k ∨ IsSepClosed k)
    (e : S ≅ Spec (.of k)) {n : ℕ} (hn : 0 < n) : GabberVanishing S n :=
  fun V hV G hG p hp ↦
    etaleVanishingAboveBound_of_field k hk e hn V hV V hV (𝟙 V)
      (by rw [CategoryTheory.Functor.map_id]; infer_instance) G hG p hp

/-- **The vanishing above `d_V` over a local ring of dimension zero** whose residue field is
finite or separably closed, for every positive `n`: a sheaf killed by `n` is a torsion sheaf, and
`subsingleton_H_of_ringKrullDim_eq_zero` bounds its cohomology. -/
theorem gabberVanishing_of_ringKrullDim_eq_zero (A : Type u) [CommRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 0)
    (hk : Finite (IsLocalRing.ResidueField A) ∨ IsSepClosed (IsLocalRing.ResidueField A))
    (e : S ≅ Spec (.of A)) {n : ℕ} (hn : 0 < n) : GabberVanishing S n := by
  intro V hV G hG p hp
  have : LocallyOfFiniteType V.obj.hom := V.property
  have : CompactSpace V.obj.left := hV
  exact subsingleton_H_of_ringKrullDim_eq_zero A hdim hk e V.obj.left V.obj.hom G
    (fun T _ ↦ ⟨⊤, V.obj.left.smallEtaleTopology.top_mem T, fun _ _ _ ↦ ⟨n, hn, hG _ _⟩⟩) p hp

variable (S) in
/-- **Stacks 0DC6, types (3) and (4), for a base of dimension zero.** Let `S ≅ Spec A` with `A` a
henselian Noetherian local ring of dimension zero whose residue field is separably closed or
finite, let `Λ` be a finite ring whose order is invertible on `S`, and let `A_U` be the category
of all sheaves of `Λ`-modules on the slices of the ringed site `(C, Λ)` of schemes locally of
finite type over `S` with the étale topology. Then the conditions (1), (2), (3) of Stacks 0DC1
hold, with `B` the quasi-compact objects, `d_V` the bound of the example and `Cov_V` the étale
coverings of `V` by quasi-compact objects. -/
theorem localSerre_of_ringKrullDim_eq_zero (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 0)
    (hk : IsSepClosed (IsLocalRing.ResidueField A) ∨ Finite (IsLocalRing.ResidueField A))
    (e : S ≅ Spec (.of A)) :
    ∀ (Λ : Type u) [CommRing Λ] [Finite Λ], IsUnit (Nat.card Λ : Γ(S, ⊤)) →
      (∀ U, (allModules S Λ U).IsWeakSerreClass) ∧
        IsStableUnderRestriction (ringedSite S Λ) (allModules S Λ) ∧
        IsLocalOnCoverings (ringedSite S Λ) (allModules S Λ) ∧
        ∃ b : LocalCohomologicalBound (ringedSite S Λ) (allModules S Λ),
          b.B = {V | IsQuasiCompact ((liftedEquiv S).inverse.obj V)} ∧
          (∀ V hV, ∃ d : ℕ, b.degreeBound V hV = d ∧
            ((liftedEquiv S).inverse.obj V).obj.hom.etaleCohomologyBound = d) ∧
          ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V),
            (b.coverings V hV).cov 𝒰 ↔ IsQuasiCompactEtaleCovering 𝒰 := by
  intro Λ _ _ _
  have hS : IsUnboundedDescentEtaleBase S := by
    rcases hk with hk | hk
    · exact Or.inr (Or.inr (Or.inl ⟨A, inferInstance, inferInstance, inferInstance, hk, ⟨e⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨A, inferInstance, inferInstance, inferInstance, hk, ⟨e⟩⟩))
  exact localSerre_of_gabberVanishing Λ hS
    (gabberVanishing_of_ringKrullDim_eq_zero A hdim hk.symm e Nat.card_pos)

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
