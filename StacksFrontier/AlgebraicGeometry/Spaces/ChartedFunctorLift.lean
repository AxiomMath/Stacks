module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartedFunctorChartPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmooth
public import StacksFrontier.RingTheory.ChartedFunctor.LiftingTheorem

/-!
# Lifting for the functors attached to smooth morphisms to affine objects

Let `T'` be an affine object of the big fppf site and `p : X ⟶ h_{T'}` a smooth morphism from an
algebraic space. A section over `T` of `X` lying over a square-zero closed immersion `T ⟶ T'`
is, through `AlgebraicGeometry.Space.OverAffine.exists_extension_of_chartedFunctor`, a section of
the functor on bounded `Γ(T')`-algebras attached to `p` over `Γ(T') ⧸ J`, and extending it to a
section over `T'` is lifting that section along `Γ(T') ⟶ Γ(T') ⧸ J`. This file proves that the
lifting is always possible, by trivialising the torsor of lifts along a faithfully flat étale
extension (step (II) of the proof of Stacks 04AM). After base change along `T' ⟶ Y` this is the
implication (1) ⟹ (2) of Stacks 04AM, that a smooth morphism `X ⟶ Y` of algebraic spaces is
formally smooth, which is `AlgebraicGeometry.Space.formallySmooth_of_isSmooth_unconditional`.

## Main results

* `AlgebraicGeometry.Space.OverAffine.chartedFunctor_exists_lift`: the lifting property of the
  functors attached to smooth morphisms from algebraic spaces to affine objects.
* `AlgebraicGeometry.Space.OverAffine.faithfullyFlat_of_etale_of_surjective`: a ring map whose
  spectrum is étale and surjective is faithfully flat.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal Limits Stacks.ChartedFunctor

universe u

namespace AlgebraicGeometry.Space.OverAffine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A ring map whose spectrum is étale and surjective is faithfully flat. -/
lemma faithfullyFlat_of_etale_of_surjective {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (he : Etale (Spec.map φ)) (hs : Surjective (Spec.map φ)) : φ.hom.FaithfullyFlat :=
  (flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, hs⟩

/-- **Lifting for the functors attached to smooth morphisms to affine objects.** Let `T'` be an
affine object of the site, `X` an algebraic space and `p : X ⟶ h_{T'}` smooth. Every section of
the functor on bounded `Γ(T')`-algebras attached to `p` over `Γ(T') ⧸ J`, for an ideal `J` of
square zero, lifts to a section over `Γ(T')`.

After a faithfully flat étale extension `Γ(T') ⟶ P₁` the section passes through an étale chart
(`AlgebraicGeometry.Space.OverAffine.exists_isChartPoint_of_etale`), so it lifts over `P₁` by
formal smoothness of the chart; the functor satisfies descent and is separated along such
extensions because `X` is an fppf sheaf, and the torsor of lifts is trivialised by the exactness
of the Čech complex of the tangent (`Stacks.ChartedFunctor.exists_lift_of_faithfullyFlat`). -/
theorem chartedFunctor_exists_lift (T' : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (p : X ⟶ yoneda.obj T') (hp : IsSmooth B S hS p) (J : Ideal (baseAlg T').obj) (hJ : J ^ 2 = ⊥)
    (x : (chartedFunctor T' X p).obj (Stacks.ChartedFunctor.quot (baseAlg T') J)) :
    ∃ ξ : (chartedFunctor T' X p).obj (baseAlg T'),
      (chartedFunctor T' X p).map (Stacks.ChartedFunctor.quotMk (baseAlg T') J) ξ = x := by
  obtain ⟨P₁, φ, c, hE, hS', hEq, hSq, ⟨ρ₀, hρ₀⟩⟩ := exists_isChartPoint_of_etale X p hX hp J hJ x
  have hR : #(sectionsRing T') < B.cutoff := (baseAlg T').2
  have hφ : φ = BaseSection.toP hR P₁ :=
    BoundedAlg.hom_ext <| AlgHom.ext fun r => (BoundedAlg.toAlgHom φ).commutes r
  subst hφ
  have : Module.FaithfullyFlat (sectionsRing T') P₁.obj :=
    RingHom.faithfullyFlat_algebraMap_iff.1 (faithfullyFlat_of_etale_of_surjective _ hE hS')
  have : Algebra.Smooth (sectionsRing T') c.C := c.smooth
  let J₁ := BaseSection.ideal J P₁
  let ρ : c.C ⟶ P₁.obj := CommAlgCat.ofHom <| Algebra.FormallySmooth.liftOfSurjective ρ₀.hom
    (BoundedAlg.toAlgHom (Stacks.ChartedFunctor.quotMk P₁ J₁)) Ideal.Quotient.mk_surjective
    ⟨2, by
      have hk : RingHom.ker (BoundedAlg.toAlgHom (Stacks.ChartedFunctor.quotMk P₁ J₁) :
          P₁.obj →+* (Stacks.ChartedFunctor.quot P₁ J₁).obj) = J₁ := Ideal.mk_ker
      exact (congrArg (· ^ 2) hk).trans (BaseSection.ideal_sq J hJ P₁)⟩
  have hρ : ρ ≫ (Stacks.ChartedFunctor.quotMk P₁ J₁).hom = ρ₀ := by
    ext y
    exact Algebra.FormallySmooth.liftOfSurjective_apply ρ₀.hom
      (BoundedAlg.toAlgHom (Stacks.ChartedFunctor.quotMk P₁ J₁)) _ _ y
  refine exists_lift_of_faithfullyFlat (hR := hR) c hJ P₁ ?_ ?_ ρ ?_
  · exact fun z hz => (chartedFunctor_existsUnique_of_isPushout T' p hX.isSheaf
      (BaseSection.toP hR P₁) (BaseSection.inclL P₁ P₁) (BaseSection.inclR P₁ P₁)
      (CommRingCat.isPushout_tensorProduct (sectionsRing T') P₁.obj P₁.obj) hE hS' z
      hz.symm).exists
  · exact chartedFunctor_map_injective T' p hX.isSheaf _ hEq hSq
  · exact (congrArg _ hρ).trans hρ₀

end AlgebraicGeometry.Space.OverAffine

end
