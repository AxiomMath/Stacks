module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.GermKillingSystem

/-!
# Pointwise germ death on refinements of proper models

Travaux de Gabber, Exposé XVIII-A, last remark of §2: on a proper model `Y` of
`η = Spec (Frac B)`, with `G = R^q j_* F` and `Y_Ω` the geometric closed fibre, the germ of a
section of `G` at a point of `Y_Ω` of large transcendence degree dies on some refinement of `Y`.
In the source this is the stalk computation through valuation rings: the Zariski–Riemann fibre
over the point is quasi-compact, and at each valuation ring `V` centred there the stalk of the
limit sheaf is `H^q(Frac V^{sh}, F) = 0` (Abhyankar's inequality and
`cd(Frac V^{sh}) ≤ rat.rank Γ_V`).

This file only states that pointwise form, `PointwiseGermDeath`, as the interface between the
stalk computation and the passage to finite families and killed-subsheaf systems
(`AlgebraicGeometry.Scheme.ZariskiRiemann.GermKilling`,
`AlgebraicGeometry.Scheme.ZariskiRiemann.KilledSubsheafSystemBound`). Its relation to
`GermKilling` is that it is the statement for one point at a time: `GermKilling n` implies it.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.PointwiseGermDeath` — for every étale `V ⟶ Y`, every
  section `g` of `R^q j_* F` over `V` and every point `z` of `V ×_Y Y_Ω` over a point of
  large transcendence degree, `g` dies on a refinement after restriction to an étale
  `W ⟶ V` whose base change to `Y_Ω` reaches `z`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.pointwiseGermDeath_of_germKilling` — `GermKilling n`
  implies `PointwiseGermDeath n`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

/-- **Germs of `R^q j_* F` die on refinements at the points of large transcendence degree.** For
`B` a strictly henselian Noetherian local domain of dimension `e ≥ 1` with `n` invertible, `F`
killed by `n` on `η = Spec (Frac B)`, a proper model `M` and a degree `q`, there is a geometric
point `x : Spec Ω ⟶ Spec B` over the closed point such that: for every étale `V ⟶ Y`, every
section `g` of `R^q j_* F` over `V` and every point `z` of `V ×_Y Y_Ω` whose image `y ∈ Y_Ω`
lies in no `E_a = {trdeg_Ω κ(y) ≤ a}` with `a + q ≤ e` and `a + 1 ≤ e`, there is an étale
`W ⟶ V`, a refinement of `M` killing the morphism `ℤ_W ⟶ R^q j_* F` of `g|W`, and a point of
`W ×_Y Y_Ω` over `z`.

This is the one-point form of `AlgebraicGeometry.Scheme.ZariskiRiemann.GermKilling`. -/
def PointwiseGermDeath (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [StrictlyHenselianLocalRing B]
    (e : ℕ), ringKrullDim B = e → 0 < e → IsUnit (n : B) →
    ∀ (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (T : (Spec (.of (FractionRing B))).Etale) (s : F.obj.obj (op T)), n • s = 0) →
      ∀ (M : ProperModel B) (q : ℕ),
        ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : Spec (.of Ω) ⟶ Spec (.of B)),
          x (default : Spec (.of Ω)) = IsLocalRing.closedPoint B ∧
          ∀ (V : M.Y.Etale)
            (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op V))
            (z : ↥(pullback V.hom (pullback.fst M.f x))),
            (¬ ∃ a : ℕ, a + q ≤ e ∧ a + 1 ≤ e ∧
                pullback.snd V.hom (pullback.fst M.f x) z ∈
                  Scheme.trdegLESet Ω (pullback.snd M.f x) a) →
            ∃ (W : M.Y.Etale) (h : W ⟶ V),
              (∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
                φ.Kills F q (ProperModel.germHom W
                  ((((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.map
                    h.op g))) ∧
              ∃ z' : ↥(pullback W.hom (pullback.fst M.f x)),
                pullback.map W.hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
                  h.left (𝟙 _) (𝟙 _)
                  (by rw [Category.comp_id]; exact (MorphismProperty.Over.w h).symm)
                  (by simp) z' = z

/-- **`GermKilling n` implies its one-point form**: the finite family of `GermKilling` reaches
every point of large transcendence degree, through one of its members. -/
theorem pointwiseGermDeath_of_germKilling {n : ℕ} (h : GermKilling.{u} n) :
    PointwiseGermDeath.{u} n := by
  intro B _ _ _ _ e he he0 hn F hF M q
  obtain ⟨Ω, _, _, x, hx, hcov⟩ := h B e he he0 hn F hF M q
  refine ⟨Ω, inferInstance, inferInstance, x, hx, fun V g z hz ↦ ?_⟩
  obtain ⟨m, W, hW, hkill, hcov'⟩ := hcov V g
  obtain ⟨k, z', hz'⟩ := hcov' z hz
  exact ⟨W k, hW k, hkill k, z', hz'⟩

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
