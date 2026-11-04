module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetOverSitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetSiteSquare

/-!
# Clause (1) of [Stacks, Tag 0D2Z] at a scheme point, over the site of `s`

Let `s` be a relative Proj situation and `w : W ⟶ U(ψ)` a scheme point of the locus of a unital
graded map `ψ`. The inverse image along `w` of the `ψ_P` leg followed by the chart map `χ_w` equals
the inverse image of the `ψ` leg, given the target square over `s.site`; that square is read over
the equal site `s.shrink.site` leaf by leaf.

## Main results

All in the namespace `AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction`.

* `pointPsi_app_heq_of_site`: the degree-`n` components of `pointPsi` over two equal sites are
  heterogeneously equal for heterogeneously equal data.
* `quasicoherentHomMk_heq_of_site`: `ObjectProperty.homMk` of maps of quasi-coherent modules over
  two equal sites are heterogeneously equal for heterogeneously equal data.
* `clauseOnePoint_of_overSitePointSquare`: clause (1) at a scheme point, given the hypotheses of
  `clauseOneTarget_square_overSite_point`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

section Generic

/-- The degree-`n` components of `pointPsi` over sites `B₁` and `B₂ = B₁` are heterogeneously equal
for heterogeneously equal data. -/
theorem pointPsi_app_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {X₁ Y₁ : AlgebraicSpaces B₁ S₁ hS₁} {f₁ : X₁ ⟶ Y₁}
    {A₁ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B₁ S₁ hS₁ Y₁)}
    {L₁ : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B₁ S₁ hS₁ X₁).O)}
    {hL₁ : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B₁ S₁ hS₁ X₁).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B₁ S₁ hS₁ X₁).O).property L₁}
    {ψ₁ : SheafOfModules.GradedAlgebra.UnitalHom
      ((gradedPull (X := smallEtaleRingedTopos B₁ S₁ hS₁ X₁)
        (Y := smallEtaleRingedTopos B₁ S₁ hS₁ Y₁)
        (smallEtaleRingedToposHom B₁ S₁ hS₁ f₁)).obj A₁)
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra
        (smallEtaleRingedTopos B₁ S₁ hS₁ X₁).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B₁ S₁ hS₁ X₁).O).property L₁)}
    {T₁ : BigFppfOver B₁ S₁ hS₁} {x₁ : yoneda.obj T₁ ⟶ X₁.1}
    {X₂ Y₂ : AlgebraicSpaces B₂ S₂ hS₂} {f₂ : X₂ ⟶ Y₂}
    {A₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B₂ S₂ hS₂ Y₂)}
    {L₂ : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B₂ S₂ hS₂ X₂).O)}
    {hL₂ : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B₂ S₂ hS₂ X₂).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B₂ S₂ hS₂ X₂).O).property L₂}
    {ψ₂ : SheafOfModules.GradedAlgebra.UnitalHom
      ((gradedPull (X := smallEtaleRingedTopos B₂ S₂ hS₂ X₂)
        (Y := smallEtaleRingedTopos B₂ S₂ hS₂ Y₂)
        (smallEtaleRingedToposHom B₂ S₂ hS₂ f₂)).obj A₂)
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra
        (smallEtaleRingedTopos B₂ S₂ hS₂ X₂).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B₂ S₂ hS₂ X₂).O).property L₂)}
    {T₂ : BigFppfOver B₂ S₂ hS₂} {x₂ : yoneda.obj T₂ ⟶ X₂.1}
    (hX : HEq X₁ X₂) (hY : HEq Y₁ Y₂) (hf : HEq f₁ f₂) (hA : HEq A₁ A₂) (hLL : HEq L₁ L₂)
    (hψ : HEq ψ₁ ψ₂) (hT : HEq T₁ T₂) (hx : HEq x₁ x₂) (n : ℤ) :
    HEq ((pointPsi (hL := hL₁) f₁ A₁ L₁ ψ₁ T₁ x₁).app n)
      ((pointPsi (hL := hL₂) f₂ A₂ L₂ ψ₂ T₂ x₂).app n) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hX hY hT hf hA hLL hx hψ
  rfl

/-- For maps `g` of quasi-coherent modules on a represented scheme, `ObjectProperty.homMk g` over
sites `B₁` and `B₂ = B₁` are heterogeneously equal for heterogeneously equal object, source, target
and `g`. -/
theorem quasicoherentHomMk_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {T₁ : BigFppfOver B₁ S₁ hS₁} {T₂ : BigFppfOver B₂ S₂ hS₂}
    {M₁ N₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj T₁).ringCatSheaf).FullSubcategory}
    {M₂ N₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj T₂).ringCatSheaf).FullSubcategory}
    {g₁ : M₁.obj ⟶ N₁.obj} {g₂ : M₂.obj ⟶ N₂.obj}
    (hT : HEq T₁ T₂) (hM : HEq M₁ M₂) (hN : HEq N₁ N₂) (hg : HEq g₁ g₂) :
    HEq (ObjectProperty.homMk g₁ : M₁ ⟶ N₁) (ObjectProperty.homMk g₂ : M₂ ⟶ N₂) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hT hM hN hg
  rfl

end Generic

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

set_option maxHeartbeats 0 in
-- comparing the two readings of the target square leaf by leaf is expensive
/-- Clause (1) at a scheme point `w : W ⟶ U(ψ)`: given the hypotheses `hcomp`, `hsite`, `hTZ`,
`hτ₁`, `hχ`, `hT`, `hb` of `clauseOneTarget_square_overSite_point` and the target square `hsq`
over `s.site` (by default the one that theorem provides), the inverse image along `w` of the `ψ_P`
leg followed by the chart map `χ_w` is the inverse image of the `ψ` leg. -/
theorem clauseOnePoint_of_overSitePointSquare (hcomp : _) (hsite : _) (hTZ : _) (hτ₁ : _)
    (hχ : _) (hT : _) (hb : _)
    (hsq : type_of% (clauseOneTarget_square_overSite_point w d hcomp hsite hTZ hτ₁ hχ hT hb) :=
      clauseOneTarget_square_overSite_point w d hcomp hsite hTZ hτ₁ hχ hT hb) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (clauseOneProjLeg s f L ψ Px d) ≫ chartMap Px w (d : ℤ) =
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (clauseOnePsiLeg s f L ψ d) :=
  clauseOnePoint_of_targetSquare' Px w d
    (targetSquare_of_site_heq s.shrink_site.symm s.shrink_base.symm hsq HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl
      (modulePullbackCompTransportIso_hom_heq_of_site s.shrink_site.symm s.shrink_base.symm
        HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
      HEq.rfl HEq.rfl HEq.rfl
      (quasicoherentHomMk_heq_of_site s.shrink_site.symm s.shrink_base.symm HEq.rfl HEq.rfl HEq.rfl
        (pointPsi_app_heq_of_site (B₁ := s.site) (B₂ := s.shrink.site) (S₁ := s.base)
          (S₂ := s.shrink.base) (hS₁ := s.containsBase) (hS₂ := s.shrink.containsBase)
          s.shrink_site.symm s.shrink_base.symm (X₁ := X) (Y₁ := s.space) (f₁ := f)
          (A₁ := s.shrink.algebra) (L₁ := L) (hL₁ := hL) (ψ₁ := ψ) (T₁ := W)
          (x₁ := locusPoint w) (X₂ := X) (Y₂ := s.shrink.space) (f₂ := f)
          (A₂ := s.shrink.algebra) (L₂ := L) (hL₂ := hL) (ψ₂ := ψ) (T₂ := W)
          (x₂ := locusPoint w) HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
          (d : ℤ)))
      HEq.rfl HEq.rfl)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
