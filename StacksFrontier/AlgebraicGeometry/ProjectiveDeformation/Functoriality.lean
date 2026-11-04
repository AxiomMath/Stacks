module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.CanonicalIdentification
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.TailPullback

/-!
# Functoriality of the truncated section algebra in the deformation

A **morphism of admissible deformations** `D₁ ⟶ D₂` of a polarized family is a cartesian square

```
X'₁ --g'--> X'₂
|f'₁        |f'₂
v           v
S'₁ --g --> S'₂
```

compatible with the immersions of `X` and `S`, together with an isomorphism `g'^* ℒ'₂ ≅ ℒ'₁`.
For such a morphism, pulling sections back along `g'` gives a homomorphism of graded
`𝒪_{S'₁}`-algebras `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` (`algebraPullbackHom`); for the cut `d₀` of
[Stacks, Tag 0D4F] it is an isomorphism in every degree (`isIso_algebraPullbackHom_app`): in
degree zero it is `g^* 𝒪_{S'₂} ≅ 𝒪_{S'₁}`, in degrees `≥ d₀` the base-change morphism of
[Stacks, Tag 0D4E] (2), and in between both sides vanish.

## Main definitions

* `…AdmissibleDeformation.Hom`: morphisms of admissible deformations.
* `…AdmissibleDeformation.algebraPullbackHom`: the homomorphism `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)`.

## Main results

* `…AdmissibleDeformation.isIso_algebraPullbackHom_app`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 0D4E](https://stacks.math.columbia.edu/tag/0D4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

namespace PolarizedFamily.AdmissibleDeformation

attribute [local instance 10000] HasDerivedCategory.standard

variable {P : PolarizedFamily.{u}}

/-- **A morphism of admissible deformations** `D₁ ⟶ D₂` of a polarized family: a morphism of the
deformed bases and of the deformed total spaces forming a cartesian square with the structure
morphisms, compatible with the immersions of the family, together with an identification of the
pullback of the lifted polarization of `D₂` with that of `D₁`. -/
structure Hom (D₁ D₂ : P.AdmissibleDeformation) where
  /-- The morphism of deformed bases. -/
  base : D₁.S' ⟶ D₂.S'
  /-- The morphism of deformed total spaces. -/
  total : D₁.X' ⟶ D₂.X'
  /-- The square of structure morphisms is cartesian. -/
  isPullback : IsPullback total D₁.f' D₂.f' base
  /-- Compatibility with the thickenings of the base. -/
  base_comm : D₁.i ≫ base = D₂.i
  /-- Compatibility with the immersions of the total space. -/
  total_comm : D₁.i' ≫ total = D₂.i'
  /-- The lifted polarizations correspond. -/
  polarization : (Scheme.Modules.pullback total).obj D₂.L' ≅ D₁.L'

variable {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- **The homomorphism of graded algebras `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)`** attached to a morphism of
admissible deformations: the adjoint transpose of pulling sections back along `g'`. -/
def algebraPullbackHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.RingedSpace.pullbackGradedAlgebra
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom φ.base)
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
          (D₂.truncatedSectionAlgebra d₀ hd₀)))
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
        (D₁.truncatedSectionAlgebra d₀ hd₀)) :=
  haveI := D₁.finitePresentation.quasiCompact
  haveI := D₁.finitePresentation.quasiSeparated
  haveI := D₂.finitePresentation.quasiCompact
  haveI := D₂.finitePresentation.quasiSeparated
  Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPullbackHom φ.total D₂.f' D₁.f' φ.base
    φ.isPullback.w D₂.L' D₁.L' φ.polarization d₀ hd₀

/-- **`g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` is an isomorphism in every degree**, as soon as the higher direct
images of the powers `(ℒ'₂)^{⊗ d}`, `d ≥ d₀`, vanish — which is conclusion (1) of
[Stacks, Tag 0D4F] for `D₂`. -/
theorem isIso_algebraPullbackHom_app
    (hvan : ∀ d : ℕ, d₀ ≤ d → ∀ p : ℤ, 0 < p →
      IsZero (((Scheme.Modules.pushforward D₂.f').rightDerivedPlus p).obj
        (Stacks.Ample.tensorPowModule D₂.X' D₂.L' (d : ℤ)))) (n : ℤ) :
    IsIso ((algebraPullbackHom φ d₀ hd₀).app n) := by
  have := D₁.finitePresentation.quasiCompact
  have := D₁.finitePresentation.quasiSeparated
  have := D₂.finitePresentation.quasiCompact
  have := D₂.finitePresentation.quasiSeparated
  refine Stacks.AlgebraicGeometry.SectionRingBaseChange.isIso_tailPullbackHom_app φ.total D₂.f'
    D₁.f' φ.base φ.isPullback.w D₂.L' D₁.L' φ.polarization d₀ hd₀ (fun m hm => ?_) n
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, by omega⟩
  exact Stacks.AlgebraicGeometry.SectionRingBaseChange.isIso_baseChangePowHom φ.total D₂.f'
    D₁.f' φ.base D₂.L' D₁.L' φ.polarization φ.isPullback D₂.finitePresentation (k : ℤ)
    fun p hp => (hvan k (by omega) p hp).of_iso
      (((Scheme.Modules.pushforward D₂.f').rightDerivedPlus p).mapIso
        (Stacks.PowerFamilyBridge.tensorPowerModuleIso D₂.X' D₂.L' (k : ℤ)))

end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
