module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentCompletionExistence

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFormalPullbackCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionLeftExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections

/-!
# Algebraizing a map to a completion on an algebraic space: existence

Let `F` be a Noetherian algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a quasi-coherent
sheaf of ideals on its small étale site, let `G` be a coherent `𝒪_F`-module, let `E` be a
coherent `𝓘`-adic system and let `α : E ⟶ G^∧` be a map whose levelwise kernels and cokernels
are annihilated by a power of `𝓘`.  The **existence** half of Stacks 08BB says that there are a
coherent module `M`, a map `a : M ⟶ G` whose kernel and cokernel are annihilated by a power of
`𝓘`, and an isomorphism `β : E ≅ M^∧` with `α = a^∧ ∘ β`.  Together with the uniqueness half
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian` this is the whole
of Stacks 08BB.

This file registers the existence half on `AlgebraicGeometry.Space.C1573.exists_algebraization`,
where `M` is the formal pullback `G ×_{lim G / 𝓘 ⁿ⁺¹ G} lim E` of
`AlgebraicGeometry.Space.formalPullback` and `a` is its projection to `G`; on the affine étale
charts this is the module of the formal glueing of Stacks 0889.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/- The site-generic abelian structure on sheaves of modules, which the import of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections` brings into scope, is
universe polymorphic, as is its Grothendieck abelian structure, and both leave universe
constraints stuck when instance search tries them on
`AlgebraicGeometry.Space.Modules`; the instance of Mathlib is the one used throughout. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (G : Modules.{u, u} B S hS F hF) (hG : IsCoherent B S hS F hF G)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α)

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hE in
/-! ### The comparison of the completion of the formal pullback with `E` -/

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hG in
omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hG in
omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hG in
omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hG in
/-! ### Stacks 08BB, existence -/

add_to_stacks 08BB "existence of the algebraization (F, a, β), over the source's hypotheses with \
Noetherianity of the algebraic space weakened to local Noetherianity of its étale charts"
  AlgebraicGeometry.Space.C1573.exists_algebraization

end AlgebraicGeometry.Space

end
