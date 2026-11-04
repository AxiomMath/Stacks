module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# The relative Čech spectral sequence for sheaves of modules, unconditionally

Let `f : 𝒰 ⥤ 𝒳` and `g : 𝒳 ⥤ 𝒴` be `1`-morphisms of categories fibred in groupoids over the big
fppf site of a scheme `S`, with `f` faithful, with equalizers in `𝒰`, and with the image of `f`
covering every object of `𝒳` locally for one of the five topologies `τ`. For a sheaf of
`𝒪_𝒳`-modules `𝓕` on `𝒳_τ` there is a first-quadrant spectral sequence of sheaves of
`𝒪_𝒴`-modules on `𝒴_τ` with first page `E₁^{i,j} = Rʲ(g ∘ fᵢ)_* fᵢ⁻¹𝓕` abutting to
`Rⁱ⁺ʲ g_* 𝓕`, all higher direct images being computed in the `τ`-topology.

The construction of the spectral sequence is
`Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData`, which takes as input the
existence statements its proof uses. This file proves every one of them, so that the spectral
sequence exists under the hypotheses of the source alone:

* abelian presheaves on each of the sites involved admit a sheafification, and the maps it
  inverts are exactly the locally bijective ones, because each site is essentially small in the
  universe of the coefficients;
* sheaves of modules on the target of `f` and on each term of its relative Čech nerve have enough
  injectives, being a Grothendieck abelian category;
* restriction of abelian presheaves along each projection `fₙ` of the Čech nerve has a pointwise
  left adjoint, the indexing categories of the colimits being small in the universe of the
  coefficients;
* restriction of presheaves of modules along `fₙ` has a left adjoint, the presheaf-level lower
  shriek of `AlgebraicGeometry.Stack.isRightAdjoint_presheafOfModules_pushforward`.

## Main results

* `Stacks.RelativeCech.nonempty_modulePushforwardSpectralSequenceData`: the spectral sequence of
  sheaves of modules exists.

## Implementation notes

The source works with a single universe of sets. Here the categories fibred in groupoids, the
schemes of the base and the module sections live in independent universes, and the sections are
taken in a universe containing all the others, which is what makes every site involved
essentially small in the universe of the coefficients.

## References

* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.RelativeCech

attribute [local instance] Stack.hasSheafify_associatedTopology_of_essentiallySmall
  Stack.wEqualsLocallyBijective_associatedTopology_of_essentiallySmall

universe u v₁ v₂ v₃ w₁ w₂ w₃ a

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type v₁} [Category.{w₁} 𝒰] {𝒳 : Type v₂} [Category.{w₂} 𝒳]
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (r : 𝒴 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (g : 𝒳 ⥤ 𝒴) (τ : AlgebraicGeometry.SiteKind)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (hf : p.IsFibredOneMorphism q f) (hg : q.IsFibredOneMorphism r g)

include hp hq hr hf hg in
/-- **Stacks 072E.** Let `f : 𝒰 ⥤ 𝒳` and `g : 𝒳 ⥤ 𝒴` be `1`-morphisms of categories fibred in
groupoids over the big fppf site of `S`, with `f` faithful, with equalizers in `𝒰` and with the
image of `f` covering `𝒳` locally for the topology `τ`. For a sheaf of `𝒪_𝒳`-modules `𝓕` on
`𝒳_τ` there is a first-quadrant spectral sequence of sheaves of `𝒪_𝒴`-modules on `𝒴_τ` with
first page `E₁^{i,j} = Rʲ(g ∘ fᵢ)_* fᵢ⁻¹𝓕` abutting to `Rⁱ⁺ʲ g_* 𝓕`, all higher direct images
being computed in the `τ`-topology. -/
@[stacks 072E]
public theorem nonempty_modulePushforwardSpectralSequenceData
    [f.Faithful] [HasEqualizers 𝒰]
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (k : y ⟶ x), R k → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    (𝓕 : SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS q hq τ)) :
    Nonempty (ModulePushforwardSpectralSequenceData.{u, v₁, v₂, v₃, w₁, w₂, w₃, a}
      B S hS p q r f g τ hp hq hr hf hg 𝓕) := by
  have hpn := tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf
  have hRightAdjoint : ∀ n : ℕ, (PresheafOfModules.pushforward.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCoreHom B S hS
        (Tuple.projection q f n ⋙ q) q (Tuple.projection q f n) (B.baseTopology τ)
        (hpn n) hq rfl (B.baseTopology_le_topology τ)).hom).IsRightAdjoint := fun n =>
    AlgebraicGeometry.Stack.isRightAdjoint_presheafOfModules_pushforward.{u, max v₁ v₂ w₂, v₂,
      max w₁ w₂, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) q
      (Tuple.projection q f n) (B.baseTopology τ) (hpn n) hq rfl (B.baseTopology_le_topology τ)
  have hEI : ∀ n : ℕ, EnoughInjectives (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      (moduleRingSheaf B S hS (Tuple.projection q f n ⋙ q) (hpn n) τ)) := fun n =>
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{max v₁ v₂ w₂, max w₁ w₂, u,
      max u v₁ w₁ v₂ w₂ v₃ w₃ a} _
  have : EnoughInjectives (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      (moduleRingSheaf B S hS q hq τ)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{v₂, w₂, u,
      max u v₁ w₁ v₂ w₂ v₃ w₃ a} _
  exact exists_modulePushforwardSpectralSequenceData.{u, v₁, v₂, v₃, w₁, w₂, w₃, a}
    B S hS p q r f g τ hp hq hr hf hg hcover hRightAdjoint 𝓕

end Stacks.RelativeCech

end
