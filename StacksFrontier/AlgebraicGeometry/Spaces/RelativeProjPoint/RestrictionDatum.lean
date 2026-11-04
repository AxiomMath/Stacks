module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.RestrictionIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesRestrict

/-!
# The restriction datum of the functor of quadruples in Situation 0849

In Situation 0849 the restrictions `f^*𝒜` of the graded algebra `𝒜` to the scheme points
`f : T ⟶ X` (`AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra`) form the datum
`AlgebraicGeometry.Space.GradedAlgebraPoints` of Stacks 084A, and the inverses of the comparisons
`τ^*(f^*𝒜) ⟶ (f ∘ τ)^*𝒜` of `AlgebraicGeometry.Space.pointComparison` make it a restriction datum
`AlgebraicGeometry.Space.GradedAlgebraRestriction`: the comparisons are isomorphisms in every
degree (`AlgebraicGeometry.Space.isIso_pointComparison_app`), they satisfy the cocycle law
(`AlgebraicGeometry.Space.pointComparison_comp_app`), and the identity law is a consequence of the
cocycle law at the identity together with invertibility.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.gradedAlgebraPoints`: the datum `f ↦ f^*𝒜`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointRestrict`: the restriction map
  `(f ∘ τ)^*𝒜 ⟶ τ^*(f^*𝒜)`, the inverse of the comparison.
* `AlgebraicGeometry.Space.RelativeProjSituation.gradedAlgebraRestriction`: the restriction
  datum.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.pointRestrict_comp`: the cocycle law.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointComparisonUnital_id_app`: the comparison
  along an identity is the canonical identification `(𝟙 T)^*𝒜_f ≅ 𝒜_f`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointRestrict_id`: the identity law.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})

/-- **The restrictions `f^*𝒜` of the graded algebra of Situation 0849 to the scheme points of the
algebraic space**, as the datum of Stacks 084A. -/
def gradedAlgebraPoints : GradedAlgebraPoints s.site s.base s.containsBase s.space.1 where
  algebra T f := zariskiReading T (etalePointAlgebra s.algebra T f)

variable {s}

/-- The comparison of the restricted algebras along a morphism of test objects, as a unital
homomorphism. -/
def pointComparisonUnital {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ s.space.1) (f' : yoneda.obj T' ⟶ s.space.1) (hf : yoneda.map τ ≫ f = f') :
    SheafOfModules.GradedAlgebra.UnitalHom
      (baseAlgebra ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)
        (s.gradedAlgebraPoints.algebra T f))
      (s.gradedAlgebraPoints.algebra T' f') :=
  @SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
    (pointComparison s.algebra τ f f' hf)
    (isIso_pointComparison_app s.algebra s.isQuasicoherent τ f f' hf 0)

/-- The comparison `pointComparisonUnital` is an isomorphism in every degree. -/
instance isIso_pointComparisonUnital_app {T T' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (f : yoneda.obj T ⟶ s.space.1) (f' : yoneda.obj T' ⟶ s.space.1)
    (hf : yoneda.map τ ≫ f = f') (n : ℤ) : IsIso ((pointComparisonUnital τ f f' hf).app n) :=
  isIso_pointComparison_app s.algebra s.isQuasicoherent τ f f' hf n

/-- **The restriction map of the restriction datum** `(f ∘ τ)^*𝒜 ⟶ τ^*(f^*𝒜)`: the inverse of the
comparison `pointComparisonUnital`. -/
def pointRestrict {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ s.space.1) (f' : yoneda.obj T' ⟶ s.space.1) (hf : yoneda.map τ ≫ f = f') :
    SheafOfModules.GradedAlgebra.UnitalHom (s.gradedAlgebraPoints.algebra T' f')
      (baseAlgebra ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)
        (s.gradedAlgebraPoints.algebra T f)) :=
  (pointComparisonUnital τ f f' hf).inverse

/-- **The cocycle law of the comparisons**, degreewise. -/
theorem pointComparisonUnital_comp_app {T T' T'' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (τ' : T'' ⟶ T') (f : yoneda.obj T ⟶ s.space.1)
    (f' : yoneda.obj T' ⟶ s.space.1) (f'' : yoneda.obj T'' ⟶ s.space.1) (hf : yoneda.map τ ≫ f = f')
    (hf' : yoneda.map τ' ≫ f' = f'') (hf'' : yoneda.map (τ' ≫ τ) ≫ f = f'') (n : ℤ) :
    (pointComparisonUnital (τ' ≫ τ) f f'' hf'').app n =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ')
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)).inv.app _ ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ')).map
          ((pointComparisonUnital τ f f' hf).app n) ≫ (pointComparisonUnital τ' f' f'' hf').app n :=
  pointComparison_comp_app s.algebra τ τ' f f' f'' hf hf' hf'' n

/-- Cancellation of the two inverted comparisons in the cocycle law. -/
private theorem cancel_aux {X Y Z : Scheme.{u}} (g : X ⟶ Y) (g' : Y ⟶ Z) {M : Z.Modules}
    {N : Y.Modules} {P : X.Modules} (c : (Scheme.Modules.pullback g').obj M ⟶ N)
    (d : N ⟶ (Scheme.Modules.pullback g').obj M) (hcd : c ≫ d = 𝟙 _)
    (c' : (Scheme.Modules.pullback g).obj N ⟶ P) (d' : P ⟶ (Scheme.Modules.pullback g).obj N)
    (hcd' : c' ≫ d' = 𝟙 _) :
    ((Scheme.Modules.pullbackComp g g').inv.app M ≫
        (Scheme.Modules.pullback g).map c ≫ c') ≫ d' ≫ (Scheme.Modules.pullback g).map d ≫
        (Scheme.Modules.pullbackComp g g').hom.app M = 𝟙 _ := by
  simp only [Category.assoc, reassoc_of% hcd']
  rw [← Functor.map_comp_assoc, hcd]
  simp

/-- **The cocycle law of the restriction maps.** -/
theorem pointRestrict_comp {T T' T'' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (τ' : T'' ⟶ T') (f : yoneda.obj T ⟶ s.space.1)
    (f' : yoneda.obj T' ⟶ s.space.1) (f'' : yoneda.obj T'' ⟶ s.space.1) (hf : yoneda.map τ ≫ f = f')
    (hf' : yoneda.map τ' ≫ f' = f'') (hf'' : yoneda.map (τ' ≫ τ) ≫ f = f'') :
    pointRestrict (τ' ≫ τ) f f'' hf'' =
      (pointRestrict τ' f' f'' hf').comp
        ((baseAlgebraMapHom ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ')
            (pointRestrict τ f f' hf)).comp
          (baseAlgebraCompHomOf (s.gradedAlgebraPoints.algebra T f)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ')
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map (τ' ≫ τ))
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp τ' τ).symm)) := by
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  have h := pointComparisonUnital_comp_app τ τ' f f' f'' hf hf' hf'' n
  have hcan : Stacks.AlgebraicGeometry.ModuleLimits.canHom
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ')
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (τ' ≫ τ))
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp τ' τ).symm
      ((s.gradedAlgebraPoints.algebra T f).piece n) =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ')
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)).hom.app _ :=
    Stacks.AlgebraicGeometry.ModuleLimits.canHom_rfl _ _ _
  refine IsIso.inv_eq_of_hom_inv_id ?_
  simp only [SheafOfModules.GradedAlgebra.UnitalHom.comp_app,
    SheafOfModules.GradedAlgebra.UnitalHom.inverse_app, baseAlgebraMapHom_app,
    baseAlgebraCompHomOf_app, pointRestrict]
  rw [hcan, h]
  exact cancel_aux _ _ _ _
    (@IsIso.hom_inv_id _ _ _ _ _ (isIso_pointComparisonUnital_app τ f f' hf n)) _ _
    (@IsIso.hom_inv_id _ _ _ _ _ (isIso_pointComparisonUnital_app τ' f' f'' hf' n))

/-- A degreewise isomorphism `c : g^*M ⟶ M` along `g = 𝟙` which satisfies the cocycle law
`c ∘ g^*c ∘ (pullbackComp g g)⁻¹ = c` is the canonical identification of the inverse image along
the identity with the identity: the cocycle law at the identity forces `g^*c ≫ c = g^*c ≫ ε`, and
`g^*c` is invertible. -/
private theorem idem_aux {X : Scheme.{u}} (g : X ⟶ X) (hg : g = 𝟙 X) (hgg : g ≫ g = g)
    (M : X.Modules)
    (c : (Scheme.Modules.pullback g).obj M ⟶ M) [hc : IsIso c]
    (c₂ : (Scheme.Modules.pullback (g ≫ g)).obj M ⟶ M)
    (h₁ : HEq c₂ c)
    (h₂ : c₂ = (Scheme.Modules.pullbackComp g g).inv.app M ≫
      (Scheme.Modules.pullback g).map c ≫ c) :
    c = (Scheme.Modules.pullbackCongr hg).hom.app M ≫ (Scheme.Modules.pullbackId X).hom.app M := by
  subst hg
  have key : ∀ (g' : X ⟶ X) (e : g' = 𝟙 X) (d : (Scheme.Modules.pullback g').obj M ⟶ M),
      HEq d c → d = (Scheme.Modules.pullbackCongr e).hom.app M ≫ c := by
    rintro _ rfl d h
    cases eq_of_heq h
    simp [Scheme.Modules.pullbackCongr]
  replace h₁ := key _ hgg c₂ h₁
  have hcan : (Scheme.Modules.pullbackComp (𝟙 X) (𝟙 X)).hom.app M ≫ c₂ =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback (𝟙 X)).obj M) ≫ c := by
    rw [h₁, ← Category.assoc, AlgebraicGeometry.pullbackComp_hom_app_comp_pullbackCongr_hom_app]
  have hc : (Scheme.Modules.pullback (𝟙 X)).map c ≫ c =
      (Scheme.Modules.pullback (𝟙 X)).map c ≫ (Scheme.Modules.pullbackId X).hom.app M := by
    have nat : (Scheme.Modules.pullback (𝟙 X)).map c ≫ (Scheme.Modules.pullbackId X).hom.app M =
        (Scheme.Modules.pullbackId X).hom.app _ ≫ c := by
      simp
    rw [nat, ← hcan, h₂, Iso.hom_inv_id_app_assoc]
  have := (cancel_epi ((Scheme.Modules.pullback (𝟙 X)).map c)).1 hc
  rw [this]
  simp [Scheme.Modules.pullbackCongr]

/-- **The comparison along the identity is the canonical identification**, degreewise. -/
theorem pointComparisonUnital_id_app (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) (n : ℤ) :
    (pointComparisonUnital (𝟙 T) f f (by simp)).app n =
      (Scheme.Modules.pullbackCongr
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map_id T)).hom.app _ ≫
        (Scheme.Modules.pullbackId _).hom.app ((s.gradedAlgebraPoints.algebra T f).piece n) := by
  have hgg : (BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 T) ≫
      (BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 T) =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 T) := rfl
  refine idem_aux (hc := isIso_pointComparisonUnital_app (𝟙 T) f f (by simp) n) _ _ hgg _ _
    ((pointComparisonUnital (𝟙 T ≫ 𝟙 T) f f (by simp)).app n) ?_
    (pointComparisonUnital_comp_app (𝟙 T) (𝟙 T) f f f (by simp) (by simp) (by simp) n)
  exact HEq.rfl

private theorem inv_comp_aux {X : Scheme.{u}} {M N P : X.Modules} (d : N ⟶ M) (c : M ⟶ N)
    (hdc : d ≫ c = 𝟙 _) (a : M ⟶ P) (b : P ⟶ N) (h : c = a ≫ b) : d ≫ a ≫ b = 𝟙 _ := by
  rw [← h, hdc]

/-- **The identity law of the restriction maps.** -/
theorem pointRestrict_id (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    (pointRestrict (𝟙 T) f f (by simp)).comp
        ((baseAlgebraCongrHom (s.gradedAlgebraPoints.algebra T f)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map_id T)).comp
          (Stacks.Conormal.gradedPullbackId (s.gradedAlgebraPoints.algebra T f))) =
      SheafOfModules.GradedAlgebra.UnitalHom.id (s.gradedAlgebraPoints.algebra T f) := by
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  simp only [SheafOfModules.GradedAlgebra.UnitalHom.comp_app,
    SheafOfModules.GradedAlgebra.UnitalHom.inverse_app, pointRestrict]
  exact inv_comp_aux _ _
    (@IsIso.inv_hom_id _ _ _ _ _ (isIso_pointComparisonUnital_app (𝟙 T) f f (by simp) n)) _ _
    (pointComparisonUnital_id_app T f n)

variable (s) in
/-- **The restriction datum of Situation 0849**: the restrictions `f^*𝒜` of the graded algebra to
the scheme points of the algebraic space, with the restriction maps `pointRestrict`. -/
def gradedAlgebraRestriction : GradedAlgebraRestriction s.gradedAlgebraPoints where
  restrict τ f f' hf := pointRestrict τ f f' hf
  isIso_restrict_app τ f f' hf n :=
    @IsIso.inv_isIso _ _ _ _ _ (isIso_pointComparisonUnital_app τ f f' hf n)
  restrict_id T f := pointRestrict_id T f
  restrict_comp τ τ' f f' f'' hf hf' hf'' := pointRestrict_comp τ τ' f f' f'' hf hf' hf''

end RelativeProjSituation

end AlgebraicGeometry.Space
