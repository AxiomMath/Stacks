module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ValuationGermDeath
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.StrictHenselizationGenericFibreBound

/-!
# Germ death at a valuation ring from vanishing on the limit of the models

Gabber's germ-killing step at a valuation ring `V` of `K = Frac B` dominating `B`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ValuationGermDeath`) has two halves.

* **Geometric half** (`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath`, a
  statement): every germ of `R^q j_* F` at the geometric point `v ≫ c_Y` over the center of `V`
  dies on some refinement, provided `H^q(Spec (S ⊗_V K), F|) = 0` for every strictly henselian
  local `V`-algebra `S`, ind-étale over `V` with local structure map. In the source: the stalks are
  `H^q(η ×_{Y'} Spec 𝒪^{sh}_{Y', c_{Y'}})` (Stacks 03Q9), the limit of these schemes over the
  refinements `Y'` is `Spec (K ⊗_V V^{sh})` (`V` is the colimit of the local rings at the centers
  and strict henselization commutes with filtered colimits), and cohomology commutes with the limit
  (Stacks 09YQ); `V^{sh}` is one such `S`.
* **Arithmetic half**: for such `S`, `H^p(Spec (S ⊗_V K), 𝓖) = 0` for `p > rat.rank Γ_V` and `𝓖`
  killed by `n`
  (`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_tensor_of_indEtale_valuationRing`).

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.tensorFractionRingToGeneric`: the projection
  `Spec (S ⊗_V K) ⟶ Spec K = η`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath`: the geometric half.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.valuationGermDeath_of_centerLimitGermDeath`:
  `CenterLimitGermDeath` implies `ValuationGermDeath n` for every `n`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

/-- The projection `Spec (S ⊗_V K) ⟶ Spec K` for a valuation subring `V` of a field `K` and a
`V`-algebra `S`: the spectrum of `x ↦ 1 ⊗ x`. -/
def tensorFractionRingToGeneric {K : Type u} [Field K] (V : ValuationSubring K) (S : Type u)
    [CommRing S] [Algebra V S] : Spec (.of (S ⊗[V] K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : K →ₐ[V] S ⊗[V] K).toRingHom)

/-- **Germ death at a valuation ring from vanishing on the limit of the models** (the geometric
half of `AlgebraicGeometry.Scheme.ZariskiRiemann.ValuationGermDeath`). Let `B` be a domain, `F`
an abelian sheaf on `η = Spec (Frac B)`, `M` a proper model, `q` a degree and `V` a valuation ring
of `K = Frac B` dominating `B`. Suppose `H^q(Spec (S ⊗_V K), F|) = 0` for every strictly henselian
local `V`-algebra `S`, ind-étale over `V` with local structure map. Then for a geometric point
`v : Spec Ω ⟶ Spec V` at the closed point, every germ of `R^q j_* F` at `v ≫ c_Y` dies at
`v ≫ c_{Y'}` on some refinement `Y' ⟶ Y`.

In the source: by Stacks 03Q9
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkRightDerivedIsoStrictHenselization`)
the stalks are `H^q(η ×_{Y'} Spec 𝒪^{sh}_{Y', c_{Y'}}, F|)`, compatibly with the transition maps
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition` becomes the
restriction along `η ×_{Y''} Spec 𝒪^{sh}_{Y''} ⟶ η ×_{Y'} Spec 𝒪^{sh}_{Y'}`); these affine
schemes form a cofiltered system over the refinements of `M` with limit `Spec (K ⊗_V V^{sh})`,
since `V` is the directed union of the images `A_{Y'}` of the local rings at the centers
(`AlgebraicGeometry.Scheme.ZariskiRiemann.iSup_centerRange`) and `V^{sh} = colim A_{Y'}^{sh}`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.exists_isStrictHenselization_colimit_centerRanges`);
a class vanishing on the limit vanishes on some level
(`Stacks.EtaleCohomology.LimitExt.exists_le_restriction_eq_zero_of_qcqs`, Stacks 09YQ), and
`V^{sh}` is a strictly henselian local `V`-algebra, ind-étale over `V` with local structure map. -/
def CenterLimitGermDeath : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B]
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1})
    (M : ProperModel B) (q : ℕ) (V : ValuationSubring (FractionRing B))
    (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
    IsLocalHom (valuationSubringBaseMap V hV) →
    (∀ (S : Type u) [CommRing S] [StrictlyHenselianLocalRing S] [Algebra V S]
        [IsLocalHom (algebraMap V S)], StacksDraft.IndEtale V S →
        Subsingleton (Sheaf.H.{u + 1}
          ((etaleAbelianInverseImage.{u, 0} (tensorFractionRingToGeneric V S)).obj F) q)) →
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ Spec (.of V)),
      v (default : Spec (.of Ω)) = IsLocalRing.closedPoint V →
      ∀ γ : (smallEtaleStalkAb (v ≫ M.center V hV)).obj
          (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F),
        ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
          (eqToHom (by rw [φ.center_eq hV, Category.assoc]) ≫
            φ.stalkTransition F q (v ≫ M'.center V hV)) γ = 0

/-- **Germ death at a valuation ring of small rank from vanishing on the limit.** If
`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath` holds then so does
`AlgebraicGeometry.Scheme.ZariskiRiemann.ValuationGermDeath n` for every `n`: for `V` of rational
rank `< q` and `n` invertible, `q ≥ 1` and every strictly henselian ind-étale local `V`-algebra `S`
has `H^q(Spec (S ⊗_V K), 𝓖) = 0` for `𝓖` killed by `n`
(`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_tensor_of_indEtale_valuationRing` with
bound `q - 1`), in particular for `𝓖 = F|`. -/
theorem valuationGermDeath_of_centerLimitGermDeath (h : CenterLimitGermDeath.{u}) (n : ℕ) :
    ValuationGermDeath.{u} n := by
  intro B _ _ hn F hF M q V hV hloc hrank Ω _ _ v hv γ
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 (hrank.trans Cardinal.natCast_lt_aleph0)
  have hmq : m < q := by
    rw [hm] at hrank
    exact_mod_cast hrank
  have hnV : IsUnit (n : V) := by
    simpa only [map_natCast] using hn.map (valuationSubringBaseMap V hV)
  refine h B F M q V hV hloc (fun S _ _ _ _ hS => ?_) Ω v hv γ
  have hb := isTorsionVanishingBound_spec_tensor_of_indEtale_valuationRing V (FractionRing B) S hS
    hnV (r := q - 1) (by rw [hm]; exact_mod_cast (show m ≤ q - 1 by omega))
  exact hb _ (forall_nsmul_eq_zero_etaleAbelianInverseImage _ hF) q
    (by exact_mod_cast (show q - 1 < q by omega))

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
