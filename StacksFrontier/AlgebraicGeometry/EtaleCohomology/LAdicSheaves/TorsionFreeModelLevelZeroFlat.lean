module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Stabilisation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevelPowExact

/-!
# The level zero of the torsion-free model of a flat ℓ-adic sheaf

Let `F` be an ℓ-adic sheaf whose levels are flat, i.e. each `Fₙ` is a flat sheaf of
`ℤ/ℓⁿ⁺¹ℤ`-modules. Then for every `N` the level zero `ℓᴺ F_N` of the torsion-free model `ℓᴺ F` is
`F₀`, whatever `N` is (no torsion bound is needed). Multiplication by `ℓᴺ` on `F_N` is the
transition `F_N ↠ F₀` followed by the Verschiebung `F₀ ⟶ F_N` iterated `N` times
(`Stacks.EtaleCohomology.LAdicSheaf.initialVerschiebung_scalar`), and each step `Fₙ ⟶ Fₙ₊₁` of
the Verschiebung is a monomorphism, `Fₙ₊₁` being flat over `ℤ/ℓⁿ⁺²ℤ`: a section of `Fₙ₊₁` killed
by `ℓ` is locally a multiple of `ℓⁿ⁺¹` and dies in `Fₙ = Fₙ₊₁ / ℓⁿ⁺¹`. So the image of `ℓᴺ` is
`F₀`.

For the sheaf `ℱ_ρ` of a continuous `ρ : π₁ → GL_r(ℤ_ℓ)` this identifies the level zero of the
flat model with the lisse sheaf of `(ℤ/ℓ)^r` with the action of `π₁` through `ρ` modulo `ℓ`, the
form in which the bottom level of the flat model of the family sheaf of Laumon's argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) is analysed on the fibres.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.mono_underlyingLAdicVerschiebung_of_powExact`.
* `Stacks.EtaleCohomology.LAdicSheaf.mono_initialVerschiebung_of_powExact`.
* `Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelLevelZeroIsoOfPowExact`:
  `(ℓᴺ F)₀ ≅ F₀` for `F` with flat levels.
* `Stacks.EtaleCohomology.LAdicSheaf.powExact_underlyingLAdicLevel_representationLAdicSheaf`: the
  levels of `ℱ_ρ` are flat, on underlying abelian sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

attribute [local instance] moduleCat_hasLimitsOfSize underlyingLevelFunctor_additive
  underlyingLevelFunctor_preservesMonomorphisms underlyingLevelFunctor_isLeftAdjoint
  underlyingLevelFunctor_preservesKernels underlyingLevelFunctor_full

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

attribute [local instance] underlyingTransitionLE_epi

variable {B X ℓ} (F : LAdicSheaf.{u, u + 1} B X ℓ)

/-- **The Verschiebung `Fₙ ⟶ Fₙ₊₁` is a monomorphism when `Fₙ₊₁` is flat**: a section of `Fₙ₊₁`
killed by `ℓ` is locally a multiple of `ℓⁿ⁺¹`, and such sections die in `Fₙ = Fₙ₊₁ / ℓⁿ⁺¹`. -/
theorem mono_underlyingLAdicVerschiebung_of_powExact (n : ℕ)
    (hP : PowExact ℓ (n + 1 + 1) (underlyingLAdicLevel B X ℓ F (n + 1))) :
    Mono (underlyingLAdicVerschiebung B X ℓ F n) := by
  have hτ : Epi (underlyingLAdicTransition B X ℓ F n) :=
    Cofork.IsColimit.epi (underlyingTransition_isCokernel B X ℓ F n)
  have hτv := underlyingLAdicTransition_verschiebung B X ℓ F n
  have hcond := underlyingTransition_condition B X ℓ F n
  refine Preadditive.mono_of_cancel_zero _ fun {T} x hx => ?_
  obtain ⟨T₁, π₁, hπ₁, y, hy⟩ :=
    surjective_up_to_refinements_of_epi (underlyingLAdicTransition B X ℓ F n) x
  have hy0 : y ≫ ((ℓ ^ 1) • 𝟙 _) = 0 := by
    rw [pow_one, ← hτv, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
  obtain ⟨T₂, π₂, hπ₂, z, hz⟩ := hP 1 (by omega) y hy0
  have hz' : (π₂ ≫ π₁) ≫ x = 0 := by
    rw [Category.assoc, hy, ← Category.assoc, hz, Category.assoc,
      show n + 1 + 1 - 1 = n + 1 from rfl, hcond, comp_zero]
  exact (cancel_epi (π₂ ≫ π₁)).1 (hz'.trans comp_zero.symm)

/-- **The iterated Verschiebung `F₀ ⟶ F_N` is a monomorphism when the levels of `F` are
flat.** -/
theorem mono_initialVerschiebung_of_powExact
    (hF : ∀ n : ℕ, PowExact ℓ (n + 1) (underlyingLAdicLevel B X ℓ F n)) :
    ∀ N : ℕ, Mono (initialVerschiebung B X ℓ F N)
  | 0 => inferInstanceAs (Mono (𝟙 _))
  | N + 1 => by
    have := mono_initialVerschiebung_of_powExact hF N
    have := mono_underlyingLAdicVerschiebung_of_powExact F N (hF (N + 1))
    exact mono_comp (initialVerschiebung B X ℓ F N) (underlyingLAdicVerschiebung B X ℓ F N)

/-- **`(ℓᴺ F)₀ ≅ F₀` for an ℓ-adic sheaf `F` with flat levels**, for every `N`: on underlying
abelian sheaves, multiplication by `ℓᴺ` on `F_N` factors as the epimorphism `F_N ↠ F₀` followed
by the monomorphism `F₀ ⟶ F_N` of the iterated Verschiebung, so its image is `F₀`. -/
def torsionFreeModelLevelZeroIsoOfPowExact
    (hF : ∀ n : ℕ, PowExact ℓ (n + 1) (underlyingLAdicLevel B X ℓ F n)) (N : ℕ) :
    (torsionFreeModel F N).level 0 ≅ F.level 0 :=
  haveI := mono_initialVerschiebung_of_powExact F hF N
  haveI : StrongEpi (underlyingTransitionLE B X ℓ F (Nat.zero_le N)) := strongEpi_of_epi _
  (underlyingLevelFunctor B X ℓ 0).preimageIso
    (torsionFreeModelLevelIso F N 0 ≪≫ Abelian.imageIsoImage _ ≪≫
      (image.isoStrongEpiMono _ _ (initialVerschiebung_scalar B X ℓ F N)).symm)

variable (B X) in
/-- **The underlying abelian sheaves of the levels of `ℱ_ρ` are flat**, for a continuous
`ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)`: the levels are
(`Stacks.EtaleCohomology.powExact_representationLevelSheaf`), and forgetting the module structure
is exact. -/
theorem powExact_underlyingLAdicLevel_representationLAdicSheaf [ConnectedSpace X.1]
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ])
    (hρ : Continuous ρ) (n : ℕ) :
    PowExact ℓ (n + 1) (underlyingLAdicLevel B X ℓ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n) := by
  have : PreservesFiniteLimits (underlyingLevelFunctor B X ℓ n) :=
    Functor.preservesFiniteLimits_of_preservesKernels _
  exact (powExact_representationLevelSheaf B X x ρ hρ n).map (underlyingLevelFunctor B X ℓ n)
    (zmodSheaf_nsmul_id (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1)) _)

end LAdicSheaf

end Stacks.EtaleCohomology

end
