module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerreFirstQuadrant
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveRepresentability

/-!
# Stacks 076Z and Stacks 0770 over an affine target

Let `M` be a rule for the modules on the `τ`-sites of algebraic stacks (**Stacks 076Z**,
**Stacks 0770**) satisfying clause (1) (a weak Serre subcategory everywhere), clause (2)
(stability under inverse image along smooth 1-morphisms) and clause (4) (preservation by the
higher direct images between algebraic stacks represented by affine schemes). Given the relative
Čech spectral sequences of **Stacks 072G**, `E₁^{p,q} = R^q (f ∘ gₚ)_* gₚ^*ℱ ⇒ R^{p+q} f_* ℱ`,
the higher direct images along every quasi-compact quasi-separated 1-morphism `f : 𝒳 ⟶ Y` into an
affine scheme preserve `M`.

## Main definitions

* `AlgebraicGeometry.Stack.StackModuleRule.HasCechSpectralSequence`: the relative Čech spectral
  sequence of **Stacks 072G** for the direct image `D` along a presentation `g` and a 1-morphism
  `h`, at a module `ℱ`.

## Main results

* `AlgebraicGeometry.Stack.StackModuleRule.preservedBy_of_hasCechSpectralSequence`: if the higher
  direct images along `h ∘ gₚ` preserve `M` for every term of the Čech nerve of a smooth
  presentation `g`, so do those along `h`.
* `AlgebraicGeometry.Stack.StackModuleRule.preservedBy_of_isAffine_of_hasCech`:
  the higher direct images along every quasi-compact quasi-separated 1-morphism into an affine
  scheme preserve `M`, given the Čech spectral sequences.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u t

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace StackModuleRule

open AlgebraicStacks

variable {τ : SiteKind} (D : StackModuleDirectImage.{u, t} B S hS τ)

/-- **The relative Čech spectral sequence of Stacks 072G for the direct image `D`.** For a
1-morphism `g : 𝒱 ⟶ 𝒵` (the presentation), a 1-morphism `h : 𝒵 ⟶ 𝒴` and a module `ℱ` on `𝒵_τ`:
a cohomological spectral sequence of modules on `𝒴_τ` starting at its first page, with
`E₁^{p,q} ≅ R^q (h ∘ gₚ)_* gₚ^*ℱ` where `gₚ` is the projection of the degree `p` term of the Čech
nerve of `g`, vanishing outside the first quadrant, and abutting to the higher direct images of
`ℱ` along `h`. -/
def HasCechSpectralSequence {𝒱 𝒵 𝒴 : AlgebraicStacks.{u, t} B S hS} (g : 𝒱 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒴)
    (F : StackModules B S hS τ 𝒵) : Prop :=
  ∃ E : CohomologicalSpectralSequence (StackModules B S hS τ 𝒴) 1,
    (∀ p q : ℕ, Nonempty ((E.page 1 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
      (D.higherDirectImage (cechNerveProjection B S hS g p ≫ h) q).obj
        ((stackModuleInverseImage B S hS τ (cechNerveProjection B S hS g p)).obj F))) ∧
    (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1 le_rfl).X (p, q))) ∧
    ∃ H : ℤ → StackModules B S hS τ 𝒴, SpectralSequence.AbutsTo E H ∧
      ∀ n : ℕ, Nonempty (H (n : ℤ) ≅ (D.higherDirectImage h n).obj F)

/-- Let `M` satisfy clauses (1) and (2) of Stacks 076Z and Stacks 0770, let `g : 𝒱 ⟶ 𝒵` be smooth
and let `h : 𝒵 ⟶ 𝒴`. If the higher direct images along `h ∘ gₚ` preserve `M` in every degree, for
every term `gₚ` of the Čech nerve of `g`, and the relative Čech spectral sequence of `g` and `h`
exists at a member `ℱ` of `M`, then `Rⁱh_* ℱ` is a member. -/
theorem preservedBy_of_hasCechSpectralSequence (M : StackModuleRule.{u, t} B S hS τ)
    (h1 : IsWeakSerre τ M) (h2 : IsStableUnderSmoothPullback τ M)
    {𝒱 𝒵 𝒴 : AlgebraicStacks.{u, t} B S hS} (g : 𝒱 ⟶ 𝒵) (hg : AlgebraicStacks.IsSmooth B S hS g)
    (h : 𝒵 ⟶ 𝒴) (hss : ∀ F, HasCechSpectralSequence D g h F)
    (hcase : ∀ p q : ℕ, PreservedBy D M (cechNerveProjection B S hS g p ≫ h) q) (i : ℕ) :
    PreservedBy D M h i := by
  intro F hF
  obtain ⟨E, hpage, hzero, H, habuts, hH⟩ := hss F
  have := h1 𝒴
  have hHi := habuts.prop_of_prop_page_firstQuadrant (M 𝒴) le_rfl hzero (fun p q =>
    (M 𝒴).prop_of_iso (hpage p q).some.symm (hcase p q _
      (h2 _ (isSmooth_cechNerveProjection B S hS g hg p) F hF))) (i : ℤ)
  exact (M 𝒴).prop_of_iso (hH i).some hHi

/-- A stack at level `0` is represented by an affine scheme in the sense of clause (4). -/
theorem isAffineRepresentable_of_cechLevel_zero {𝒵 : AlgebraicStacks.{u, t} B S hS}
    (h𝒵 : CechLevel B S hS 0 𝒵) : IsAffineRepresentable B S hS 𝒵 :=
  exists_equivalenceOver_schemeFibredCategory_of_cechLevel_zero B S hS h𝒵

/-- **Stacks 076Z and Stacks 0770 over an affine target, given the Čech spectral sequences.** Let
`M` satisfy clauses (1), (2) and (4), and suppose that the relative Čech spectral sequence of
**Stacks 072G** exists for the direct image `D` along every smooth surjective presentation
representable by algebraic spaces. Then for every quasi-compact quasi-separated 1-morphism
`f : 𝒳 ⟶ Y` into the stack of an affine scheme, the higher direct images along `f` preserve `M`
in every degree. -/
theorem preservedBy_of_isAffine_of_hasCech
    (M : StackModuleRule.{u, t} B S hS τ) (h1 : IsWeakSerre τ M)
    (h2 : IsStableUnderSmoothPullback τ M) (h4 : PreservesHigherDirectImagesOfAffine D M)
    (hss : ∀ {𝒱 𝒵 𝒴 : AlgebraicStacks.{u, t} B S hS} (g : 𝒱 ⟶ 𝒵),
      IsRepresentableByAlgebraicSpaces B S hS g.hom.hom → IsSurjective B S hS g →
      AlgebraicStacks.IsSmooth B S hS g → ∀ (h : 𝒵 ⟶ 𝒴) F, HasCechSpectralSequence D g h F)
    {𝒳 : AlgebraicStacks.{u, t} B S hS} {Y : BigFppfOver B S hS}
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (f : 𝒳 ⟶ schemeStack.{u, t} B S hS Y) (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) (i : ℕ) : PreservedBy D M f i :=
  cechLevel_induction_of_isQuasiCompact B S hS Y hY (fun h => ∀ i, PreservedBy D M h i)
    (fun h𝒵 h => h4 h (isAffineRepresentable_of_cechLevel_zero h𝒵)
      ⟨Y, hY, ⟨StacksRepresentableCFG.EquivalenceOver.refl _⟩⟩)
    (fun g hrep hsurj hsm h hcase => preservedBy_of_hasCechSpectralSequence D M h1 h2 g hsm h
      (hss g hrep hsurj hsm h) fun p q => hcase p q)
    f hqc hqs i

end StackModuleRule

end AlgebraicGeometry.Stack

end
