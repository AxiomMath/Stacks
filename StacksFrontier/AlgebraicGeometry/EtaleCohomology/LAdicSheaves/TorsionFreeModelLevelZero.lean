module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModel

/-!
# The level zero of the torsion-free model does not depend on the exponent

For an ℓ-adic sheaf `G` and `N` beyond its torsion bound, the level zero `ℓᴺ G_N` of the
torsion-free model `ℓᴺ G` and the level zero `ℓᴺ⁺¹ G_{N+1}` of `ℓᴺ⁺¹ G` are isomorphic. Write
`F = ℓᴺ G`, a flat ℓ-adic sheaf. Then `ℓᴺ⁺¹ G_{N+1} = ℓ F₁` is the image of multiplication by `ℓ`
on `F₁`. That map factors as the transition `F₁ ↠ F₀` followed by the Verschiebung `F₀ ⟶ F₁`,
and the Verschiebung is a monomorphism because `F₁` is flat over `ℤ/ℓ²`: a section killed by `ℓ`
is locally a multiple of `ℓ`, and such sections die in `F₀ = F₁ / ℓ`. So the image is `F₀`.

This is what makes the lisse locus of the `Rʳ g_! G` of the reduction of the Weil II weight bound
to curves ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) independent of the torsion bound
chosen on an open subscheme: the torsion bounds of `G` and of its restrictions are chosen
independently.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.mono_modelVerschiebung`: the
  Verschiebung `F₀ ⟶ F₁` of the model is a monomorphism.
* `Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelLevelZeroSuccIso`:
  `(ℓᴺ⁺¹ G)₀ ≅ (ℓᴺ G)₀` beyond the torsion bound.
* `Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelLevelZeroIsoOfLE`:
  `(ℓᴹ G)₀ ≅ (ℓᴺ G)₀` for `torsionBound G ≤ N ≤ M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

attribute [local instance] underlyingLevelFunctor_additive
  underlyingLevelFunctor_preservesMonomorphisms underlyingLevelFunctor_isLeftAdjoint
  underlyingLevelFunctor_preservesKernels underlyingLevelFunctor_full

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

attribute [local instance] underlyingTransitionLE_epi
attribute [local instance] underlyingLevelFunctor_full

variable (G : LAdicSheaf.{u, u + 1} B X ℓ) {N : ℕ}

/-- The transition `F₁ ⟶ F₀` of the underlying tower of the model `F = ℓᴺ G`. -/
abbrev modelTransition (N : ℕ) :
    (underlyingLevelFunctor B X ℓ 1).obj (torsionFreeModelLevel G N 1) ⟶
      (underlyingLevelFunctor B X ℓ 0).obj (torsionFreeModelLevel G N 0) :=
  underlyingLAdicTransition B X ℓ (torsionFreeModel G N) 0

/-- The Verschiebung `F₀ ⟶ F₁` of the underlying tower of the model `F = ℓᴺ G`. -/
abbrev modelVerschiebung (N : ℕ) :
    (underlyingLevelFunctor B X ℓ 0).obj (torsionFreeModelLevel G N 0) ⟶
      (underlyingLevelFunctor B X ℓ 1).obj (torsionFreeModelLevel G N 1) :=
  underlyingLAdicVerschiebung B X ℓ (torsionFreeModel G N) 0

/-- The transition followed by the Verschiebung of the model `F = ℓᴺ G` is multiplication by `ℓ`. -/
private theorem modelTransition_comp_modelVerschiebung :
    modelTransition G N ≫ modelVerschiebung G N = ℓ • 𝟙 _ :=
  underlyingLAdicTransition_verschiebung B X ℓ (torsionFreeModel G N) 0

/-- **The Verschiebung `F₀ ⟶ F₁` of the torsion-free model is a monomorphism**, beyond the torsion
bound: `F₁` is flat over `ℤ/ℓ²`, so a section of `F₁` killed by `ℓ` is locally a multiple of `ℓ`
and dies in `F₀ = F₁ / ℓ`. -/
theorem mono_modelVerschiebung (hN : torsionBound G ≤ N) : Mono (modelVerschiebung G N) := by
  have : Epi (torsionFreeModelπ G N 1) := epi_factorThruImage_comp_inv _ _
  have : Mono (torsionFreeModelι G N 1) := mono_hom_comp_image_ι _ _
  have hP : PowExact ℓ (1 + 1)
      ((underlyingLevelFunctor B X ℓ 1).obj (torsionFreeModelLevel G N 1)) :=
    powExact_of_image (torsionBound_divisible G hN 1) (torsionFreeModelπ G N 1)
      (torsionFreeModelι G N 1) (torsionFreeModelπ_ι G N 1)
  have hτ : Epi (modelTransition G N) :=
    Cofork.IsColimit.epi (underlyingTransition_isCokernel B X ℓ (torsionFreeModel G N) 0)
  have hcond : ((ℓ ^ (0 + 1)) • 𝟙 _) ≫ modelTransition G N = 0 :=
    underlyingTransition_condition B X ℓ (torsionFreeModel G N) 0
  refine Preadditive.mono_of_cancel_zero _ fun {T} x hx => ?_
  obtain ⟨T₁, π₁, hπ₁, y, hy⟩ := surjective_up_to_refinements_of_epi (modelTransition G N) x
  have hy0 : y ≫ ((ℓ ^ 1) • 𝟙 _) = 0 := by
    rw [pow_one, ← modelTransition_comp_modelVerschiebung, ← Category.assoc, ← hy,
      Category.assoc, hx, comp_zero]
  obtain ⟨T₂, π₂, hπ₂, z, hz⟩ := hP 1 (by omega) y hy0
  have hz' : (π₂ ≫ π₁) ≫ x = 0 := by
    rw [Category.assoc, hy, ← Category.assoc, hz, Category.assoc,
      show 1 + 1 - 1 = 0 + 1 from rfl, hcond, comp_zero]
  exact (cancel_epi (π₂ ≫ π₁)).1 (hz'.trans comp_zero.symm)

/-- `ℓᴺ⁺¹` on `G_{N+1}` is the transition `G_{N+1} ↠ F₁ ↠ F₀` followed by the Verschiebung and the
inclusion `F₀ ↪ F₁ ↪ G_{N+1}`, where `F = ℓᴺ G`. -/
theorem torsionFreeModelπ_transition_verschiebung_ι :
    (torsionFreeModelπ G N 1 ≫ modelTransition G N) ≫
        (modelVerschiebung G N ≫ torsionFreeModelι G N 1) =
      (ℓ ^ (N + 1)) • 𝟙 (underlyingLAdicLevel B X ℓ G (N + 1 + 0)) := by
  rw [Category.assoc, ← Category.assoc (modelTransition G N),
    modelTransition_comp_modelVerschiebung, Preadditive.nsmul_comp,
    Category.id_comp, Preadditive.comp_nsmul, torsionFreeModelπ_ι, smul_smul, pow_succ,
    mul_comm]

/-- **`(ℓᴺ⁺¹ G)₀ ≅ (ℓᴺ G)₀` beyond the torsion bound.** On underlying abelian sheaves, the image of
`ℓᴺ⁺¹` on `G_{N+1}` is `F₀` for `F = ℓᴺ G`: `ℓᴺ⁺¹` factors as an epimorphism onto `F₀`
followed by a monomorphism out of it. -/
def torsionFreeModelLevelZeroSuccIso (hN : torsionBound G ≤ N) :
    (torsionFreeModel G (N + 1)).level 0 ≅ (torsionFreeModel G N).level 0 :=
  haveI : Epi (torsionFreeModelπ G N 1) := epi_factorThruImage_comp_inv _ _
  haveI : Mono (torsionFreeModelι G N 1) := mono_hom_comp_image_ι _ _
  haveI : Epi (modelTransition G N) :=
    Cofork.IsColimit.epi (underlyingTransition_isCokernel B X ℓ (torsionFreeModel G N) 0)
  haveI := mono_modelVerschiebung G hN
  haveI : StrongEpi (torsionFreeModelπ G N 1 ≫ modelTransition G N) :=
    strongEpi_of_epi _
  haveI : Mono (modelVerschiebung G N ≫ torsionFreeModelι G N 1) := mono_comp _ _
  (underlyingLevelFunctor B X ℓ 0).preimageIso
    (torsionFreeModelLevelIso G (N + 1) 0 ≪≫ Abelian.imageIsoImage _ ≪≫
      (image.isoStrongEpiMono _ _ (torsionFreeModelπ_transition_verschiebung_ι G)).symm)

/-- **`(ℓᴹ G)₀ ≅ (ℓᴺ G)₀` for `torsionBound G ≤ N ≤ M`.** -/
def torsionFreeModelLevelZeroIsoOfLE (hN : torsionBound G ≤ N) :
    ∀ k : ℕ, (torsionFreeModel G (N + k)).level 0 ≅ (torsionFreeModel G N).level 0
  | 0 => Iso.refl _
  | k + 1 => torsionFreeModelLevelZeroSuccIso G (hN.trans (Nat.le_add_right N k)) ≪≫
      torsionFreeModelLevelZeroIsoOfLE hN k

end LAdicSheaf

end Stacks.EtaleCohomology
