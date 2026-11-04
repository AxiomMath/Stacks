module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing
public import StacksFrontier.Algebra.Homology.RightDerivedDeltaOne

/-!
# Vanishing of a first higher direct image from local liftings of sections

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor of sites and `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` a short exact sequence
of abelian sheaves on `𝒞` with `I` injective. The presheaf `V ↦ H¹(u V, F)` of Stacks 072W is a
quotient of `V ↦ Q(u V)` by the degree-one connecting morphism, which kills the image of
`I(u V)`. So `R¹ f_* F = 0` as soon as every section of `Q` over `u V` lifts to `I` after
restriction to the members of a covering sieve of `V`.

## Main results

* `Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_rightDerived_one_pushforward_of_lift` —
  the statement above.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.SheafifiedHigherDirectImage

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{t})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{t})]

/-- **`R¹ f_* F = 0` from local liftings of sections of the quotient of an injective
presentation.** -/
theorem isZero_rightDerived_one_pushforward_of_lift
    {S : ShortComplex (Sheaf K AddCommGrpCat.{t})} (hS : S.ShortExact) [Injective S.X₂]
    (H : ∀ (V : D) (c : S.X₃.obj.obj (op (u.obj V))), ∃ R ∈ J V, ∀ ⦃V' : D⦄ (g : V' ⟶ V), R g →
      ∃ i : S.X₂.obj.obj (op (u.obj V')), S.g.hom.app (op (u.obj V')) i =
        S.X₃.obj.map (u.map g).op c) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived 1).obj S.X₁) := by
  let Q := pushforwardCohomologyPresheaf (K := K) AddCommGrpCat.{t} u
  have : PreservesFiniteLimits Q := by
    dsimp only [Q, pushforwardCohomologyPresheaf]
    infer_instance
  let δ := Stacks.Cohomology.RightDerivedDeltaOne.deltaOne Q hS
  have : Epi δ := Stacks.Cohomology.RightDerivedDeltaOne.epi_deltaOne hS Q
  refine isZero_rightDerived_pushforward_of_locallyZero u 1 S.X₁ fun V ξ => ?_
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1 (inferInstance : Epi (δ.app (op V))) ξ
  obtain ⟨R, hR, hlift⟩ := H V c
  refine J.superset_covering (fun V' g hg => ?_) hR
  obtain ⟨i, hi⟩ := hlift g hg
  have h0 := congrArg (fun φ => φ.app (op V') i)
    (Stacks.Cohomology.RightDerivedDeltaOne.map_g_comp_deltaOne hS Q)
  simp only [NatTrans.comp_app, NatTrans.app_zero] at h0
  show _ = _
  rw [map_zero, ← NatTrans.naturality_apply δ g.op c]
  show δ.app (op V') (S.X₃.obj.map (u.map g).op c) = 0
  rw [← hi]
  exact h0.trans (by rfl)

end Stacks.Cohomology.SheafifiedHigherDirectImage

end
