module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonKernelGeneration

/-!
# Stacks 0D0X: `ε^*𝒦₀ ⟶ 𝒦` is an isomorphism

The adjunct `ε^*𝒦₀ ⟶ 𝒦` of the map `κ_{-1} : 𝒦₀ ⟶ ε_*𝒦` between the degree `-1` cohomology
sheaves of `NL_{X₀/Y₀}` and of `NL_{X/Y}` is an isomorphism.  By the local criterion for `ε`
(`AlgebraicGeometry.Space.isIso_representedEpsilonModuleAdjunction_homEquiv_symm`) it suffices
that the concrete model `𝒪_X ⊗ 𝒦₀ ⟶ 𝒦` of the adjunct is locally surjective
(`AlgebraicGeometry.Space.representedEpsilonKernelModel_isLocallySurjective`) and locally
injective.  Local injectivity is checked over the charts `ε Z` of the affine Zariski squares,
which cover the final object, where it is
`AlgebraicGeometry.Space.exists_covering_representedEpsilonKernelPullbackModel_map_eq_zero`.

## Main results

* `AlgebraicGeometry.Space.representedEpsilonKernelModel_isLocallyInjective`: local injectivity
  of the model.
* `AlgebraicGeometry.Space.isIso_representedEpsilonKernelHom_adjunct`: the adjunct of `κ_{-1}`
  is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w₂ v₂ u₂

namespace Stacks.PresheafOfModules

variable {C : Type u₂} [Category.{v₂} C] {R : Cᵒᵖ ⥤ RingCat.{w₂}}

/-- A morphism of a slice along which the difference of two sections restricts to `0` lies in
their equalizer sieve. -/
theorem equalizerSieve_over_arrows {M : _root_.PresheafOfModules.{w₂} R} {Y : C}
    {V : (Over Y)ᵒᵖ} {V' : Over Y} (g : V' ⟶ V.unop) (x y : ToType (M.obj (op V.unop.left)))
    (h : M.map g.left.op (x - y) = 0) :
    (Presheaf.equalizerSieve (F := (Over.forget Y).op ⋙
      (_root_.PresheafOfModules.toPresheaf R).obj M) (X := V) x y).arrows g :=
  sub_eq_zero.1 ((map_sub (M.map g.left.op).hom x y).symm.trans h)

/-- **Local injectivity of a morphism of presheaves of modules on a slice, from its kernel**: if
every section over an object of the slice that `c` kills restricts to `0` on a covering, the
restriction of `c` to the slice is locally injective. -/
theorem isLocallyInjective_whiskerLeft_over_of_forall_eq_zero
    {M N : _root_.PresheafOfModules.{w₂} R} (c : M ⟶ N) (J : GrothendieckTopology C) {Y : C}
    (h : ∀ (V : Over Y) (w : ToType (M.obj (op V.left))), c.app (op V.left) w = 0 →
      ∃ S : Sieve V, S ∈ J.over Y V ∧ ∀ ⦃V' : Over Y⦄ (g : V' ⟶ V), S g → M.map g.left.op w = 0) :
    Presheaf.IsLocallyInjective (J.over Y)
      (Functor.whiskerLeft (Over.forget Y).op ((_root_.PresheafOfModules.toPresheaf R).map c)) where
  equalizerSieve_mem {V} x y hxy := by
    obtain ⟨S, hS, hS'⟩ := h V.unop (x - y)
      ((map_sub (c.app (op V.unop.left)).hom x y).trans (sub_eq_zero.2 hxy))
    exact (J.over Y).superset_covering
      (fun V' g hg => equalizerSieve_over_arrows g x y (hS' g hg)) hS

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-- **Local injectivity of the model over the chart of an affine Zariski square.** -/
theorem isLocallyInjective_representedEpsilonKernelModel_over
    {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    {W : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (hZ : IsAffineOpen Z)
    (hW : IsAffineOpen W) :
    Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS
        (representedAlgebraicSpace B S hS U).1).over
          (representedEpsilonChartDiagram B S hS φ hZW).U)
      (Functor.whiskerLeft (Over.forget (representedEpsilonChartDiagram B S hS φ hZW).U).op
        ((PresheafOfModules.toPresheaf _).map (representedEpsilonKernelModel B S hS φ))) := by
  refine Stacks.PresheafOfModules.isLocallyInjective_whiskerLeft_over_of_forall_eq_zero
    (C := SmallEtale B S hS (representedAlgebraicSpace B S hS U).1)
    (representedEpsilonKernelModel B S hS φ) _ fun V' w hw => ?_
  with_reducible exact
    exists_covering_representedEpsilonKernelPullbackModel_map_eq_zero B S hS φ hZW hZ hW V' w hw

/-- **Local injectivity of the model of the adjunct of `κ_{-1}`.** -/
theorem representedEpsilonKernelModel_isLocallyInjective :
    PresheafOfModules.IsLocallyInjective
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
      (representedEpsilonKernelModel B S hS φ) :=
  Presheaf.isLocallyInjective_of_coversTop _ _
    (coversTop_representedEpsilonFunctor_affineSquare B S hS φ) fun ⟨⟨_, _⟩, hZ, hW, hZW⟩ =>
      isLocallyInjective_representedEpsilonKernelModel_over B S hS φ hZW hZ hW

/-- **The adjunct `ε^*𝒦₀ ⟶ 𝒦` of `κ_{-1}` is an isomorphism**: the model of the adjunct is
locally injective and locally surjective. -/
theorem isIso_representedEpsilonKernelHom_adjunct :
    IsIso (((representedEpsilonModuleAdjunction B S hS U).homEquiv _ _).symm
      (representedEpsilonKernelHom B S hS φ)) :=
  isIso_representedEpsilonModuleAdjunction_homEquiv_symm B S hS U _
    (representedEpsilonKernelModel_isLocallyInjective B S hS φ)
    (representedEpsilonKernelModel_isLocallySurjective B S hS φ)

end AlgebraicGeometry.Space

end
