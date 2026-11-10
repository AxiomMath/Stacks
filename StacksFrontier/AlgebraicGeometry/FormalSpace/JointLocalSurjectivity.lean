module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty

/-!
# Joint local surjectivity of families of morphisms of fppf sheaves

Two facts about jointly locally surjective families of morphisms of sheaves, used to build the
coverings of Definition 0AIM in the proofs of Stacks 0ANG, 0AKX and 0GBD.

## Main results

* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_sigma_comp`: a jointly locally surjective
  family stays jointly locally surjective after composing it with a jointly locally surjective
  family over each of its sources.
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_isPullback`: joint local
  surjectivity passes to base changes along arbitrary cartesian squares.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Joint local surjectivity of a family of morphisms of fppf sheaves -/

universe u₁ v₁ w₁ in
/-- A family of morphisms of sheaves of types on a site obtained by composing a jointly locally
surjective family `(qⱼ : Gⱼ ⟶ X)` with a jointly locally surjective family over each of its
sources is again jointly locally surjective: each `Sigma.desc` is an epimorphism of sheaves of
sets, and the composite family cancels through the two of them in turn. -/
theorem _root_.CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_sigma_comp
    {C : Type u₁} [Category.{v₁} C] {K : GrothendieckTopology C} [HasSheafify K (Type w₁)]
    {X : Sheaf K (Type w₁)} {J : Type*} {G : J → Sheaf K (Type w₁)} (q : ∀ j, G j ⟶ X)
    {I : J → Type*} {U : ∀ j, I j → Sheaf K (Type w₁)} (w : ∀ j i, U j i ⟶ G j)
    [HasCoproduct G] [∀ j, HasCoproduct (U j)] [HasCoproduct fun p : Σ j, I j ↦ U p.1 p.2]
    (hq : Sheaf.IsLocallySurjective (Sigma.desc q))
    (hw : ∀ j, Sheaf.IsLocallySurjective (Sigma.desc (w j))) :
    Sheaf.IsLocallySurjective (Sigma.desc fun p : Σ j, I j ↦ w p.1 p.2 ≫ q p.1) := by
  have := hq
  rw [Sheaf.isLocallySurjective_iff_epi]
  refine ⟨fun g h hgh ↦ (cancel_epi (Sigma.desc q)).1 (Sigma.hom_ext _ _ fun j ↦ ?_)⟩
  have := hw j
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_comp_desc]
  refine (cancel_epi (Sigma.desc (w j))).1 (Sigma.hom_ext _ _ fun i ↦ ?_)
  simpa only [← Category.assoc, Sigma.ι_comp_desc] using
    Sigma.ι (fun p : Σ j, I j ↦ U p.1 p.2) ⟨j, i⟩ ≫= hgh

/-- Joint local surjectivity passes to a family of base changes presented by arbitrary
cartesian squares: if `(ψᵢ : Hᵢ ⟶ Y)` is jointly locally surjective and each `sᵢ : Aᵢ ⟶ X` is
the projection to `X` of a cartesian square over `ψᵢ` and `φ : X ⟶ Y`, then `(sᵢ)` is jointly
locally surjective. The case of the chosen fibre products is
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`, to which each square is
compared by the isomorphism of its vertex with the chosen one. -/
theorem isLocallySurjective_sigmaDesc_of_isPullback
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X Y : FppfSheaf B S hS} (φ : X ⟶ Y) {I : Type (u + 1)} {H A : I → FppfSheaf B S hS}
    {ψ : ∀ i, H i ⟶ Y} {p : ∀ i, A i ⟶ H i} {s : ∀ i, A i ⟶ X}
    (sq : ∀ i, IsPullback (p i) (s i) (ψ i) φ)
    (hψ : Sheaf.IsLocallySurjective (Sigma.desc ψ)) :
    Sheaf.IsLocallySurjective (Sigma.desc s) := by
  have hcan := Sheaf.isLocallySurjective_sigmaDesc_pullback_snd φ ψ hψ
  rw [Sheaf.isLocallySurjective_iff_epi] at hcan ⊢
  refine ⟨fun α β hab ↦ (cancel_epi (Sigma.desc fun i ↦ pullback.snd (ψ i) φ)).1
    (Sigma.hom_ext _ _ fun i ↦ ?_)⟩
  have h1 := Sigma.ι A i ≫= hab
  simp only [← Category.assoc, Sigma.ι_comp_desc] at h1 ⊢
  refine (cancel_epi (sq i).isoPullback.hom).1 ?_
  simpa only [← Category.assoc, (sq i).isoPullback_hom_snd] using h1

end AlgebraicGeometry.FormalSpace

end
