module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetOverSite

/-!
# The `ψ` leg of clause (1) of Stacks 0D2Z as the composite of its two factors, over the site of `s`

The target square of clause (1) of [Stacks, Tag 0D2Z] over the site of `s`
(`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`) takes as its
hypothesis `hb` the `ψ` leg `…InvertibleTwistingRestriction.clauseOnePsiLeg` as the inverse
comparison of Stacks 03LU for `ι : U(ψ) ⟶ X` and `f`, followed by `ι^*ψ_d`, with the inverse
images and the comparison over `s.site s.base s.containsBase`.  The leg is defined over the site
of `s.shrink`, which is the site of `s` by definition but not syntactically; its defining
equation is carried to the site of `s` by a lemma at variables over two sites `B₁ = B₂` with
heterogeneously equal leaves (`AlgebraicGeometry.Space.eq_compIso_inv_comp_map_of_site_heq`),
proved by `subst`, so that no factor is converted between the two spellings.

## Main results

* `AlgebraicGeometry.Space.eq_compIso_inv_comp_map_of_site_heq`: a morphism equal to the inverse
  comparison followed by an inverse image, read over a second spelling of the site.
* `…InvertibleTwistingRestriction.clauseOnePsiLeg_eq_overSite`: the hypothesis `hb` of the
  target square over the site of `s`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

namespace AlgebraicGeometry.Space

/-- **A morphism equal to the inverse comparison `(ι ≫ f)^*M ≅ ι^*f^*M` of Stacks 03LU followed
by the inverse image `ι^*ψ` of `ψ : f^*M ⟶ L`, read over a second spelling of the site**: the
equation over `B₁` gives the same equation over `B₂ = B₁`, for heterogeneously equal leaves. -/
theorem eq_compIso_inv_comp_map_of_site_heq {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {U₁ X₁ Y₁ : AlgebraicSpaces B₁ S₁ hS₁} {ι₁ : U₁ ⟶ X₁} {f₁ : X₁ ⟶ Y₁}
    {M₁ : Modules.{u, u} B₁ S₁ hS₁ Y₁.1 Y₁.2} {Lx₁ : Modules.{u, u} B₁ S₁ hS₁ X₁.1 X₁.2}
    {ψd₁ : (modulePullback B₁ S₁ hS₁ f₁).obj M₁ ⟶ Lx₁}
    {b₁ : (modulePullback B₁ S₁ hS₁ (ι₁ ≫ f₁)).obj M₁ ⟶ (modulePullback B₁ S₁ hS₁ ι₁).obj Lx₁}
    (h : b₁ = ((modulePullbackCompIso B₁ S₁ hS₁ ι₁ f₁).app M₁).inv ≫
      (modulePullback B₁ S₁ hS₁ ι₁).map ψd₁)
    {U₂ X₂ Y₂ : AlgebraicSpaces B₂ S₂ hS₂} {ι₂ : U₂ ⟶ X₂} {f₂ : X₂ ⟶ Y₂}
    {M₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2} {Lx₂ : Modules.{u, u} B₂ S₂ hS₂ X₂.1 X₂.2}
    {ψd₂ : (modulePullback B₂ S₂ hS₂ f₂).obj M₂ ⟶ Lx₂}
    {b₂ : (modulePullback B₂ S₂ hS₂ (ι₂ ≫ f₂)).obj M₂ ⟶ (modulePullback B₂ S₂ hS₂ ι₂).obj Lx₂}
    (hU : HEq U₁ U₂) (hX : HEq X₁ X₂) (hY : HEq Y₁ Y₂) (hι : HEq ι₁ ι₂) (hf : HEq f₁ f₂)
    (hM : HEq M₁ M₂) (hLx : HEq Lx₁ Lx₂) (hψ : HEq ψd₁ ψd₂) (hb : HEq b₁ b₂) :
    b₂ = ((modulePullbackCompIso B₂ S₂ hS₂ ι₂ f₂).app M₂).inv ≫
      (modulePullback B₂ S₂ hS₂ ι₂).map ψd₂ := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hU hX hY hι hf hM hLx hψ hb
  exact h

end AlgebraicGeometry.Space

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

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


set_option maxHeartbeats 0 in
-- The nine `HEq.rfl` leaves are checked by unfolding the site of `s.shrink` to that of `s`.
/-- **The `ψ` leg of clause (1) is the composite of its two factors, over the site of `s`**:
`…InvertibleTwistingRestriction.clauseOnePsiLeg` is the inverse comparison of Stacks 03LU for
`ι : U(ψ) ⟶ X` and `f`, followed by `ι^*ψ_d`, both over `s.site s.base s.containsBase`.  This is
the hypothesis `hb` of `…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`,
read off the defining equation of the leg through
`AlgebraicGeometry.Space.eq_compIso_inv_comp_map_of_site_heq`. -/
theorem clauseOnePsiLeg_eq_overSite :
    type_of% (eq_compIso_inv_comp_map_of_site_heq s.shrink_site s.shrink_base
      (clauseOnePsiLeg.eq_1 s f L ψ d)
      (B₂ := s.site) (S₂ := s.base) (hS₂ := s.containsBase)
      (U₂ := locusSpaceOfUnitalHom s f L ψ) (X₂ := X) (Y₂ := s.space)
      (ι₂ := locusInclusionOfUnitalHom s f L ψ) (f₂ := f)
      (M₂ := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ))
      (ψd₂ := ψ.app (d : ℤ)) (b₂ := clauseOnePsiLeg s f L ψ d)
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl) :=
  (eq_compIso_inv_comp_map_of_site_heq s.shrink_site s.shrink_base
      (clauseOnePsiLeg.eq_1 s f L ψ d)
      (B₂ := s.site) (S₂ := s.base) (hS₂ := s.containsBase)
      (U₂ := locusSpaceOfUnitalHom s f L ψ) (X₂ := X) (Y₂ := s.space)
      (ι₂ := locusInclusionOfUnitalHom s f L ψ) (f₂ := f)
      (M₂ := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ))
      (ψd₂ := ψ.app (d : ℤ)) (b₂ := clauseOnePsiLeg s f L ψ d)
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
