module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedActionLinearCochain

/-!
# Extending a null homotopy along a short exact sequence

Let `X` be a ringed site, let `A` be a sheaf of differential graded algebras on it and let `I`
be a graded injective right differential graded `A`-module. Given a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of right differential graded `A`-modules and a morphism `f : M₂ ⟶ I`,
a null homotopy of the restriction of `f` to `M₁` extends to a null homotopy of `f` as soon as
every morphism `M₃ ⟶ I` is null-homotopic.

This is the step that enlarges a partial null homotopy in the transfinite argument for
Tag 0FSY.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_actionLinear_extension_of_shortExact`:
  precomposition with the first arrow of a short exact sequence is surjective on action-linear
  cochains into a graded injective module.
* `SheafOfModules.DifferentialGradedModule.exists_actionLinear_delta_extension`: the extension
  of a null homotopy described above, which moreover restricts to the given one.

## Implementation notes

Surjectivity of precomposition is Tag 0FSQ's first display, which lives in the differential
graded category of right differential graded modules; it is transported to action-linear
cochains along `SheafOfModules.DifferentialGradedModule.underlyingCochain`, under which
composition of homogeneous morphisms becomes composition of cochains and the closed degree-zero
homogeneous morphism of a morphism of modules becomes its cochain.

The extension itself is the usual two-step argument. Extend the given degree `-1` cochain
arbitrarily to `M₂`; the difference between `f` and the commutator of the extension is a closed
action-linear cochain of degree zero, hence a morphism `M₂ ⟶ I`, and it kills `M₁`, so it
factors through `M₃`. A null homotopy of that factorisation, pulled back to `M₂`, corrects the
extension, and the correction restricts to zero on `M₁`.

## References

* [Stacks Project, Tag 0FSQ](https://stacks.math.columbia.edu/tag/0FSQ)
* [Stacks Project, Tag 0FSY](https://stacks.math.columbia.edu/tag/0FSY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

section Extension

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Precomposition is surjective on action-linear cochains into a graded injective module.**
For a short exact sequence of right differential graded modules, every action-linear cochain
out of the first term into a graded injective module is the restriction of one out of the
second term. -/
theorem exists_actionLinear_extension_of_shortExact
    {I : DifferentialGradedModule.{u, v, w} A}
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) (hS : S.ShortExact)
    (hI : GradedInjective I) (n : ℤ) (z : Cochain S.X₁.complex I.complex n)
    (hz : IsActionLinear A z) :
    ∃ z' : Cochain S.X₂.complex I.complex n, IsActionLinear A z' ∧
      (Cochain.ofHom S.f.toHomologicalComplex).comp z' (zero_add n) = z := by
  obtain ⟨-, -, hsurj⟩ :=
    homComplex_shortExact_of_gradedInjective A S.f S.g S.zero hS hI n
  set D := dgCategoryData.{u, v, w} A with hD
  obtain ⟨b, hb⟩ := hsurj ((moduleHomEquiv A D S.X₁ I n).symm ⟨z, hz⟩)
  refine ⟨underlyingCochain A D b, (moduleHomEquiv A D S.X₂ I n b).property, ?_⟩
  have hh := congrArg (underlyingCochain A D) hb
  change underlyingCochain A D
      (D.category.comp (add_zero n) b (cocycleOfHom A D S.f).val) = _ at hh
  rw [underlyingCochain_comp A D (add_zero n) b (cocycleOfHom A D S.f).val] at hh
  change (underlyingCochain A D (homogeneousOfHom A D S.f)).comp
    (underlyingCochain A D b) _ = _ at hh
  rw [homogeneousOfHom_underlying A D S.f] at hh
  refine hh.trans ?_
  exact congrArg Subtype.val ((moduleHomEquiv A D S.X₁ I n).apply_symm_apply ⟨z, hz⟩)

/-- **The extension of a null homotopy along a short exact sequence.** Let `I` be graded
injective, let `0 → M₁ → M₂ → M₃ → 0` be short exact and let `f : M₂ ⟶ I`. If every morphism
`M₃ ⟶ I` is the commutator of the differentials with an action-linear cochain of degree `-1`,
then so is `f`, by a cochain restricting on `M₁` to any prescribed such cochain for the
restriction of `f`. -/
theorem exists_actionLinear_delta_extension
    {I : DifferentialGradedModule.{u, v, w} A}
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) (hS : S.ShortExact)
    (hI : GradedInjective I) (f : S.X₂ ⟶ I)
    (z₁ : Cochain S.X₁.complex I.complex (-1)) (hz₁ : IsActionLinear A z₁)
    (hd₁ : δ (-1) 0 z₁ = Cochain.ofHom (S.f ≫ f).toHomologicalComplex)
    (hv : ∀ g : S.X₃ ⟶ I, ∃ z : Cochain S.X₃.complex I.complex (-1),
      IsActionLinear A z ∧ δ (-1) 0 z = Cochain.ofHom g.toHomologicalComplex) :
    ∃ z : Cochain S.X₂.complex I.complex (-1), IsActionLinear A z ∧
      δ (-1) 0 z = Cochain.ofHom f.toHomologicalComplex ∧
      (Cochain.ofHom S.f.toHomologicalComplex).comp z (zero_add (-1)) = z₁ := by
  classical
  obtain ⟨z, hz, hres⟩ :=
    exists_actionLinear_extension_of_shortExact A S hS hI (-1) z₁ hz₁
  set d := Cochain.ofHom f.toHomologicalComplex - δ (-1) 0 z with hdd
  have hd : IsActionLinear A d :=
    actionLinear_sub A _ _ (actionLinear_ofHom A f) (actionLinear_delta A z hz)
  have hdδ : δ 0 1 d = 0 := by
    rw [hdd, δ_sub, δ_ofHom, zero_sub, δ_δ (-1) 0 1 z, neg_zero]
  set g := homOfClosed A d hd hdδ with hgg
  have hg : Cochain.ofHom g.toHomologicalComplex = d := ofHom_homOfClosed A d hd hdδ
  have hfg : S.f ≫ g = 0 := by
    apply Hom.ext
    intro n
    have h : Cochain.ofHom (S.f ≫ g).toHomologicalComplex = 0 := by
      show Cochain.ofHom (S.f.toHomologicalComplex ≫ g.toHomologicalComplex) = 0
      rw [Cochain.ofHom_comp, hg, hdd, Cochain.comp_sub, ← Cochain.ofHom_comp,
        ← δ_ofHom_comp, hres, hd₁]
      exact sub_self _
    simpa only [Cochain.ofHom_v, Cochain.zero_v, zero_f] using
      Cochain.congr_v h n n (add_zero n)
  have : Epi S.g := hS.epi_g
  set l := hS.exact.desc g hfg with hll
  have hl : S.g ≫ l = g := hS.exact.g_desc g hfg
  obtain ⟨z₃, hz₃, hd₃⟩ := hv l
  set z' := (Cochain.ofHom S.g.toHomologicalComplex).comp z₃ (zero_add (-1)) with hz'd
  have hz' : IsActionLinear A z' :=
    actionLinear_comp A _ _ _ (actionLinear_ofHom A S.g) hz₃
  have hd' : δ (-1) 0 z' = Cochain.ofHom g.toHomologicalComplex := by
    rw [hz'd, δ_ofHom_comp, hd₃, ← Cochain.ofHom_comp]
    exact congrArg (fun h : S.X₂ ⟶ I => Cochain.ofHom h.toHomologicalComplex) hl
  refine ⟨z + z', actionLinear_add A _ _ hz hz', ?_, ?_⟩
  · rw [δ_add, hd', hg, hdd]
    abel
  · rw [Cochain.comp_add, hres]
    suffices h : (Cochain.ofHom S.f.toHomologicalComplex).comp z' (zero_add (-1)) = 0 by
      rw [h, add_zero]
    rw [hz'd, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
    have hzero : S.f.toHomologicalComplex ≫ S.g.toHomologicalComplex = 0 := by
      show (S.f ≫ S.g).toHomologicalComplex = 0
      rw [S.zero]
      rfl
    rw [hzero, Cochain.ofHom_zero, Cochain.zero_comp]

end Extension

end SheafOfModules.DifferentialGradedModule

end
