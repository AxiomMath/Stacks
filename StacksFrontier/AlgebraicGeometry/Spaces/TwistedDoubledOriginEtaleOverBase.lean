module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginAlgebraicSpace

/-!
# The twisted doubled origin is étale over the base

The second assertion of the example is that the structure morphism `X ⟶ S` of the quotient
`X = U/R` is étale in the sense of Stacks 03FR: the composite of every étale morphism from a
scheme into `X` with `X ⟶ S` is étale.

The chart `U = Spec K[x]` is étale over `S = Spec k[x]`, because `K[x]` is the base change of
the finite separable extension `K/k` along `k → k[x]`.  Given an étale morphism `T ⟶ X` from
an object of the site, the fibre product `W = T ×_X U` is étale over `U`, hence étale over
`S`, and is surjective and étale over `T`; so `T ⟶ S` is étale by the étale case of Stacks
02KM.  Since the target of `X ⟶ S` is the terminal presheaf, that is exactly the assertion.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.etale_coverMap`: the chart is étale over the base,
  and `AlgebraicGeometry.TwistedDoubledOrigin.surjective_isFinite_etale_coverMap`: it is
  surjective, finite and étale over the base — the morphism `S' ⟶ S` of part (6) of the
  example. The remaining assertion of part (6), that `S' ×_S X` is a scheme, is in
  `StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange`, which is where the
  clause is tagged.
* `AlgebraicGeometry.TwistedDoubledOrigin.isEtale_quotientBaseMap`: **Stacks 03FN, part (2)**
  — the structure morphism of the quotient is an étale morphism of algebraic spaces.

## Implementation notes

The target of `AlgebraicGeometry.TwistedDoubledOrigin.quotientBaseMap` is the functor of
points of the base over itself, which is the terminal presheaf; the Yoneda presheaf of the
terminal object `Over.mk (𝟙 S)` of the site is terminal as well, and the unique isomorphism
between the two carries the structure morphism of an object `T` of the site to the morphism of
schemes `T ⟶ S`.  Étaleness of a morphism of representable presheaves is étaleness of the
underlying morphism of schemes, which is
`AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff`, so the assertion reduces to the
scheme-level statement.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.TwistedDoubledOrigin

attribute [local instance] Polynomial.algebra

/-! ### A presheaf whose values are singletons is terminal -/

/-- A presheaf of types all of whose values are inhabited and subsingleton is a terminal
object of the category of presheaves. -/
private def isTerminal_of_subsingleton {C : Type v} [Category.{w} C] (P : Cᵒᵖ ⥤ Type u)
    (hne : ∀ a, P.obj a) (hsub : ∀ a, Subsingleton (P.obj a)) : IsTerminal P := by
  refine IsTerminal.ofUniqueHom (fun Q =>
    { app := fun a => TypeCat.ofHom fun _ => hne a
      naturality := fun a b f => by ext x; exact (hsub b).elim _ _ }) ?_
  intro Q f
  ext a x
  exact (hsub a).elim _ _

/-! ### The chart is étale over the base -/

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The polynomial ring over a finite separable extension is étale over the polynomial ring
over the ground field: it is the base change of the extension along `k → k[x]`. -/
theorem etale_polynomial_of_isSeparable [FiniteDimensional k K] [Algebra.IsSeparable k K] :
    Algebra.Etale (Polynomial k) (Polynomial K) := by
  have : Algebra.Etale k K := ⟨Algebra.FormallyEtale.of_isSeparable k K,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have : Algebra.Etale (Polynomial k) (TensorProduct k (Polynomial k) K) :=
    Algebra.Etale.baseChange k K (Polynomial k)
  exact Algebra.Etale.of_equiv (polynomialCoefficientEquiv k K).symm

/-- **The chart of the twisted doubled origin is étale over the base.** The affine line over a
finite separable extension is étale over the affine line over the ground field. -/
theorem etale_coverMap [FiniteDimensional k K] [Algebra.IsSeparable k K] :
    Etale (coverMap k K) := by
  rw [coverMap, HasRingHomProperty.Spec_iff (P := @Etale)]
  show (algebraMap (Polynomial k) (Polynomial K)).Etale
  rw [RingHom.etale_algebraMap]
  exact etale_polynomial_of_isSeparable k K

/-- The chart is a finite morphism over the base: `K[x]` is a finite `k[x]`-module, being the
base change of the finite extension `K/k`. -/
theorem isFinite_coverMap [FiniteDimensional k K] : IsFinite (coverMap k K) := by
  have : Module.Finite (Polynomial k) (TensorProduct k (Polynomial k) K) :=
    Module.Finite.base_change k (Polynomial k) K
  rw [coverMap, IsFinite.SpecMap_iff]
  show (algebraMap (Polynomial k) (Polynomial K)).Finite
  rw [RingHom.finite_algebraMap]
  exact Module.Finite.equiv (polynomialCoefficientEquiv k K).symm.toLinearEquiv

/-- **The base change along which the twisted doubled origin becomes a scheme.** The chart
`S' = Spec K[x] ⟶ S = Spec k[x]` is surjective, finite and étale.

This is the morphism `S' ⟶ S` asked for by part (6) of Stacks 03FN. It carries no tag on its
own: asserting only this half of the clause would assert half of it, and the whole clause —
together with the identification of `X' = S' ×_S X` with two copies of the chart glued along the
puncture — is
`AlgebraicGeometry.TwistedDoubledOrigin.surjective_isFinite_etale_and_baseChange_isScheme`. -/
theorem surjective_isFinite_etale_coverMap [FiniteDimensional k K] [IsGalois k K] :
    Surjective (coverMap k K) ∧ IsFinite (coverMap k K) ∧ Etale (coverMap k K) :=
  ⟨(coverMap_fppf k K).2.2, isFinite_coverMap k K, etale_coverMap k K⟩

/-! ### The structure morphism of the quotient -/

variable (B : BigFppfSite.{u}) (hS : B.Contains (base k))

/-- The base, as the terminal object of the big fppf site over it. -/
abbrev baseSiteObject : BigFppfOver B (base k) hS := Over.mk (𝟙 (B.obj hS))

/-- The Yoneda presheaf of the terminal object of the site is terminal. -/
private def isTerminal_yoneda_baseSiteObject :
    IsTerminal (yoneda.obj (baseSiteObject k B hS)) :=
  isTerminal_of_subsingleton _ (fun a => Over.mkIdTerminal.from a.unop)
    (fun _ => ⟨fun _ _ => Over.mkIdTerminal.hom_ext _ _⟩)

/-- The functor of points of the base over itself is terminal. -/
private def isTerminal_points_baseOverBase :
    IsTerminal (Stacks.Groupoids.points
      (Over.post (X := B.obj hS) B.inclusion) (baseOverBase k)) :=
  isTerminal_of_subsingleton _
    (fun _ => (Over.mkIdTerminal (X := base k)).from _)
    (fun _ => ⟨fun _ _ => (Over.mkIdTerminal (X := base k)).hom_ext _ _⟩)

/-- The structure morphism of an object of the site, as a morphism of the site into the
terminal object. -/
private abbrev toBaseSiteObject (T : BigFppfOver B (base k) hS) :
    T ⟶ baseSiteObject k B hS :=
  Over.homMk T.hom (by simp)

/-- **Stacks 03FN, part (2).** The structure morphism of the Galois twist of the affine line
with zero doubled is an étale morphism of algebraic spaces over the base, in the sense of
Stacks 03FR: every étale morphism from a scheme into the quotient is étale over the base.

The chart `U ⟶ X` is surjective and étale, and `U ⟶ S` is étale; so for an étale morphism
`T ⟶ X` the fibre product `W = T ×_X U` is étale over `S` and surjective étale over `T`, and
the étale case of Stacks 02KM makes `T ⟶ S` étale. -/
@[stacks 03FN "part (2): the morphism X -> S is etale"]
theorem isEtale_quotientBaseMap [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    Space.IsEtale B (base k) hS (quotientBaseMap k K hdegree σ hσ B hS) := by
  classical
  set T₀ := BigFppfOver.toScheme B (base k) hS
  set P := MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) T₀
  have hPresp : P.presheaf.RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) P).respectsIso
  -- the chart of the quotient
  set U := coverSiteObject k K B hS
  set q := yonedaEquiv.symm
    ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (base k) hS)
      (Over.post B.inclusion) (twistedRelation k K σ)).app
      (Opposite.op (coverSiteObject k K B hS))
      (𝟙 ((Over.post B.inclusion).obj (coverSiteObject k K B hS))))
  have hq_surj := surjective_toQuotientSheaf_twistedRelation k K hdegree σ hσ B hS
  have hq_etale := etale_toQuotientSheaf_twistedRelation k K hdegree σ hσ B hS
  have hUetale : Etale (T₀.map (toBaseSiteObject k B hS U)) := etale_coverMap k K
  -- the terminal identification
  have hterm₁ := isTerminal_yoneda_baseSiteObject k B hS
  set e : Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (baseOverBase k) ≅
      yoneda.obj (baseSiteObject k B hS) :=
      (isTerminal_points_baseOverBase k B hS).uniqueUpToIso hterm₁
  intro T φ hφ
  -- the fibre product of the chart with the given étale morphism
  set W := hq_etale.rep.pullback φ
  set p₁ := hq_etale.rep.fst' φ
  set p₂ := hq_etale.rep.snd φ
  have hsq : IsPullback (yoneda.map p₁) (yoneda.map p₂) q φ := hq_etale.rep.isPullback' φ
  have h₂surj : Surjective (T₀.map p₂) := hq_surj.property φ (yoneda.map p₁) p₂ hsq
  have h₂etale : Etale (T₀.map p₂) := hq_etale.property φ (yoneda.map p₁) p₂ hsq
  have h₁etale : Etale (T₀.map p₁) := hφ.property q (yoneda.map p₂) p₁ hsq.flip
  -- structure morphisms are compatible with morphisms of the site
  have hw : ∀ {A C : BigFppfOver B (base k) hS} (f : A ⟶ C),
      f ≫ toBaseSiteObject k B hS C = toBaseSiteObject k B hS A :=
    fun f => Over.OverMorphism.ext (Over.w f)
  -- `W ⟶ S` is étale, being `W ⟶ U ⟶ S`; as `W ⟶ T` is surjective étale, so is `T ⟶ S`
  have hTetale : Etale (T₀.map (toBaseSiteObject k B hS T)) := by
    have : Etale (T₀.map p₂ ≫ T₀.map (toBaseSiteObject k B hS T)) := by
      rw [← T₀.map_comp, hw p₂, ← hw p₁, T₀.map_comp]
      exact MorphismProperty.comp_mem (@Etale.{u}) _ _ h₁etale hUetale
    exact Stacks.Etale.etale_of_comp_surjective_etale (T₀.map p₂)
      (T₀.map (toBaseSiteObject k B hS T))
  -- transport along the terminal identification
  have hyon : P.presheaf (yoneda.map (toBaseSiteObject k B hS T)) :=
    (Space.presheaf_yoneda_map_etale_iff B (base k) hS (toBaseSiteObject k B hS T)).2 hTetale
  have hkey : (φ ≫ quotientBaseMap k K hdegree σ hσ B hS) ≫ e.hom =
      yoneda.map (toBaseSiteObject k B hS T) := hterm₁.hom_ext _ _
  have hcomp' : P.presheaf ((φ ≫ quotientBaseMap k K hdegree σ hσ B hS) ≫ e.hom) := by
    rwa [hkey]
  exact (MorphismProperty.cancel_right_of_respectsIso P.presheaf _ e.hom).1 hcomp'

end AlgebraicGeometry.TwistedDoubledOrigin

end
