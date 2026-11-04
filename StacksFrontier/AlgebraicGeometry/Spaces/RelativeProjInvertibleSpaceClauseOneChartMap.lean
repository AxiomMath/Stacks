module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceSchemeHomBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSquareQcoh

/-!
# Clause (1) of Stacks 0D2Z at the scheme points of `U(ψ)`, for the chart maps

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space
`Y` of Situation 0849, clause (1) of [Stacks, Tag 0D2Z] for `θ` descended from the chart maps
`χ_w` is descended from the identity `w^*(ψ_P leg) ≫ χ_w = w^*(ψ leg)` at the scheme points
`w : W ⟶ U(ψ)` (`…InvertibleTwistingRestriction.clauseOneHom_thetaOfFamily`).  The chart map is
`χ_w = (chartTargetIso w) ∘ θ_w^a ∘ (chartSourceIso w)`, and the identity splits into three
squares: the source square
(`…InvertibleTwistingRestriction.clauseOneSource_square_of_chartSourceIso`), the middle square,
which is clause (1) of [Stacks, Tag 01O9] on the scheme `W`, and the target square.  This file
states the middle square, on the underlying morphisms of modules on `W`.

## Main results

* `…quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom_heq`:
  **the middle square of clause (1) at a scheme point**, on underlying morphisms: the inverse
  image along the section `c_w` of `ψ` of Tag 01NR, followed by `θ_w`, is the contraction
  `c_w^*(π_W^*((f ∘ w)^*𝒜)_d) ≅ ((f ∘ w)^*𝒜)_d` followed by `w^*ψ` in degree `d`.
* `…quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom`,
  `…InvertibleTwistingRestriction.quasicoherentPullbackMap_fibrePsiQcohHom_comp_chartSchemeTheta`:
  the same square as an equation of morphisms of modules on `W`, and of quasi-coherent modules.

## Implementation notes

The quasi-coherent modules of the two factors are spelled through
`…RelativeProjSituation.twistPieceQcoh` and `AlgebraicGeometry.Space.pointLaurentPieceQcoh`, the
scheme-level clause (1) through `GradedPowerMap.twD (s.relativeProjPoints.algebra …)` and the
tensor powers of `w^*ℒ`; the two spellings are equal by definition, but comparing them inside one
unification exhausts the budget.  The square is therefore stated as a heterogeneous equality, from
a generic lemma whose equation argument fixes the objects by unification and whose object
equalities are separate `rfl` hypotheses, and then read as an equation through the object
equalities `…pointLaurentPieceQcoh_obj_eq_tensorPowerModule` and
`…tensorPowerModule_line_eq_tensorPower`, each a separate `rfl`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

/-- **A composite heterogeneously equal to a composite of heterogeneously equal morphisms.**  If
`a' ≫ b' = g'` and `a`, `b` are heterogeneously equal to `a'`, `b'` (through objects `Y = Y'`,
`Z = Z'`), then `a ≫ b` is heterogeneously equal to `g'`.  The equation `h` comes first, so that
an instance takes `a'`, `b'`, `g'` and the objects `Y'`, `Z'` from it by unification. -/
theorem comp_heq_of_comp_eq_of_heq {C : Type*} [Category C] {X Y' Z' : C} {a' : X ⟶ Y'}
    {b' : Y' ⟶ Z'} {g' : X ⟶ Z'} (h : a' ≫ b' = g') {Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (hY : Y = Y') (hZ : Z = Z') (ha : HEq a a') (hb : HEq b b') : HEq (a ≫ b) g' := by
  subst hY hZ
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  exact heq_of_eq h

/-- An equation from a heterogeneous equality `a ≫ b ≍ g`, with `g` read between the source and
target of `a ≫ b` through equalities of objects. -/
theorem comp_eq_eqToHom_comp_comp_eqToHom_of_heq {C : Type*} [Category C] {X Y Z X' Z' : C}
    {a : X ⟶ Y} {b : Y ⟶ Z} {g : X' ⟶ Z'} (h : HEq (a ≫ b) g) (hX : X = X') (hZ : Z = Z') :
    a ≫ b = eqToHom hX ≫ g ≫ eqToHom hZ.symm := by
  subst hX hZ
  simpa using eq_of_heq h

/-- The contraction `q^*(g^*F) ≅ (q ≫ g)^*F = π^*F` followed by a morphism is the canonical
identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom` followed by it. -/
theorem pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_eq_canHom_comp {W Z X : Scheme.{u}}
    (q : W ⟶ Z) (g : Z ⟶ X) {π : W ⟶ X} (hπ : q ≫ g = π) (F : X.Modules) {N : W.Modules}
    (θ : (Scheme.Modules.pullback π).obj F ⟶ N) :
    (Scheme.Modules.pullbackComp q g).hom.app F ≫ (Scheme.Modules.pullbackCongr hπ).hom.app F ≫ θ =
      Stacks.AlgebraicGeometry.ModuleLimits.canHom q g π hπ F ≫ θ :=
  (Category.assoc _ _ _).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {W : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj W ⟶ X.1)
  (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤) (d : ℕ)

/-- **`θ_w` at a scheme point on underlying morphisms, as the canonical identification
followed by `θ`**: `…InvertibleTwistingRestriction.chartSchemeTheta_hom_heq`, with the relative
homogeneous spectrum read through `s.shrink.pointAlgebra` (the target of
`…RelativeProjSituation.toRelativeProj`) and the contraction and the transport combined into
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`: the spelling of
`…InvertibleTwistingRestriction.quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartTheta`. -/
theorem chartSchemeTheta_hom_heq_canHom_comp (d : ℤ) :
    type_of% ((chartSchemeTheta_hom_heq (s := s) (f := f) (L := L) (ψ := ψ) d x hx).trans
      ((pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_heq
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((ofUnitalHom s f L ψ).chartSection x hx))
        ((ofUnitalHom s f L ψ).toScheme_map_chartSection_comp_toRelativeProj x hx)
        (toScheme_map_chartSection_toRelativeProj s f L ψ x hx)
        ((ofUnitalHom s f L ψ).chartTheta x hx d)
        ((toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).thetaOnSection
          ((ofUnitalHom s f L ψ).chartLift x hx) ((ofUnitalHom s f L ψ).chartLift_ι x hx) d)
        rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl).trans (heq_of_eq
        (pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_eq_canHom_comp _ _ _ _ _)))) := by
  have h :=
    (chartSchemeTheta_hom_heq (s := s) (f := f) (L := L) (ψ := ψ) d x hx).trans
      ((pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_heq
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((ofUnitalHom s f L ψ).chartSection x hx))
        ((ofUnitalHom s f L ψ).toScheme_map_chartSection_comp_toRelativeProj x hx)
        (toScheme_map_chartSection_toRelativeProj s f L ψ x hx)
        ((ofUnitalHom s f L ψ).chartTheta x hx d)
        ((toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).thetaOnSection
          ((ofUnitalHom s f L ψ).chartLift x hx) ((ofUnitalHom s f L ψ).chartLift_ι x hx) d)
        rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl).trans (heq_of_eq
        (pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_eq_canHom_comp _ _ _ _ _)))
  exact h

set_option maxHeartbeats 400000 in
-- elaborating the instance compares the two spellings of the module objects (see the
-- implementation notes)
/-- **The middle square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w` of `U(ψ)`, on
underlying morphisms**: the inverse image along the section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)` of `ψ` of
Tag 01NR in adjoint form (`…RelativeProjSituation.fibrePsiQcohHom`), followed by `θ_w` of
Tag 01O9 (`…InvertibleTwistingRestriction.chartSchemeTheta`), is heterogeneously equal to the
contraction `c_w^*(π_W^*((f ∘ w)^*𝒜)_d) ≅ ((f ∘ w)^*𝒜)_d` followed by the adjoint transpose of
`w^*ψ` and the comparison of the iterated and integral tensor powers of `w^*ℒ`.

The instance of `AlgebraicGeometry.Space.comp_heq_of_comp_eq_of_heq` (`type_of%`) at
`…InvertibleTwistingRestriction.quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartTheta`,
with `θ_w` read through `…InvertibleTwistingRestriction.chartSchemeTheta_hom_heq_canHom_comp`. -/
theorem quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom_heq :
    type_of% (comp_heq_of_comp_eq_of_heq
      (quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartTheta s f L ψ x hx d)
      (quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.fibrePsiQcohHom W (x ≫ f.hom) d)).hom
      (chartSchemeTheta s f L ψ x hx (d : ℤ)).hom rfl rfl HEq.rfl
      (chartSchemeTheta_hom_heq_canHom_comp s f L ψ x hx (d : ℤ))) := by
  have h :=
    comp_heq_of_comp_eq_of_heq
      (quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartTheta s f L ψ x hx d)
      (quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.fibrePsiQcohHom W (x ≫ f.hom) d)).hom
      (chartSchemeTheta s f L ψ x hx (d : ℤ)).hom rfl rfl HEq.rfl
      (chartSchemeTheta_hom_heq_canHom_comp s f L ψ x hx (d : ℤ))
  exact h

/-- `(w^*ℒ)^{⊗ d}` as a quasi-coherent module, on its underlying module, is the integral tensor
power `tensorPowerModule` of `w^*ℒ`. -/
theorem pointLaurentPieceQcoh_obj_eq_tensorPowerModule (d : ℤ) :
    (pointLaurentPieceQcoh L W x d).obj =
      Stacks.AmpleProjectiveImmersion.tensorPowerModule _ ((ofUnitalHom s f L ψ).line W x) d :=
  rfl

/-- The integral tensor power `tensorPowerModule` of `w^*ℒ` is the tensor power of invertible
modules on the structure presheaf of `W`. -/
theorem tensorPowerModule_line_eq_tensorPower (d : ℤ) :
    Stacks.AmpleProjectiveImmersion.tensorPowerModule _ ((ofUnitalHom s f L ψ).line W x) d =
      Stacks.SheafOfModules.Invertible.tensorPower
        ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W).presheaf
        _ ((ofUnitalHom s f L ψ).line W x) d :=
  rfl

/-- **The middle square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w` of `U(ψ)`, as an
equation of morphisms of modules on `W`**: the inverse image along `c_w` of `ψ` of Tag 01NR
followed by `θ_w` is the contraction `c_w^*(π_W^*((f ∘ w)^*𝒜)_d) ≅ ((f ∘ w)^*𝒜)_d` followed by the
adjoint transpose of `w^*ψ` and the comparison of the iterated and integral tensor powers of
`w^*ℒ`, read into `(w^*ℒ)^{⊗ d}`.  The instance of
`AlgebraicGeometry.Space.comp_eq_eqToHom_comp_comp_eqToHom_of_heq` (`type_of%`) at
`…quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom_heq`. -/
theorem quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom :
    type_of% (comp_eq_eqToHom_comp_comp_eqToHom_of_heq
      (quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom_heq s f L ψ x hx d)
      rfl
      ((pointLaurentPieceQcoh_obj_eq_tensorPowerModule s f L ψ x (d : ℤ)).trans
        (tensorPowerModule_line_eq_tensorPower s f L ψ x (d : ℤ)))) := by
  have h := comp_eq_eqToHom_comp_comp_eqToHom_of_heq
    (quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom_heq s f L ψ x hx d)
    rfl
    ((pointLaurentPieceQcoh_obj_eq_tensorPowerModule s f L ψ x (d : ℤ)).trans
      (tensorPowerModule_line_eq_tensorPower s f L ψ x (d : ℤ)))
  exact h

/-- **The middle square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w` of `U(ψ)`, as an
equation of morphisms of quasi-coherent modules on `W`**:
`…quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom` in the full subcategory,
through `AlgebraicGeometry.Space.comp_eq_homMk_of_hom_comp_hom_eq`. -/
theorem quasicoherentPullbackMap_fibrePsiQcohHom_comp_chartSchemeTheta :
    type_of% (ObjectProperty.hom_ext _
        ((quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom
        s f L ψ x hx d))) := by
  have h := ObjectProperty.hom_ext _
      (quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom s f L ψ x hx d)
  exact h

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
