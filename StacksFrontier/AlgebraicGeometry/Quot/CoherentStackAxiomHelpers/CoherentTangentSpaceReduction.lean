module

public import
  StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAxiomHelpers.CoherentTangentLiftClasses
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.Deformation.TangentSpace.FiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverField

/-!
# The tangent spaces of `Coh_{X/Y}` through lifts of modules over `k[V]`

Let `x₀ = (Spec k, 𝒢₀)` be an object of `Coh_{X/Y}` over a field, with `Y` final. The proof of
Stacks 08W8 computes the tangent space `T𝓕_{x₀}` of `Coh_{X/Y}` at `x₀` as the group of lifts of
`𝒢₀` to `X_{k[ε]}`, and these as `Ext¹(𝒢₀, 𝒢₀)` by Stacks 08VW. This file carries out the first
half of that computation: the classes of lifts of `x₀` to `k[V]` are the classes of lifts of
`𝒢₀` to `X_{k[V]}`, naturally in `V` (`CoherentSituation.squareZeroLiftClassMap`), so that a
natural map of the latter to a finite dimensional linear functor, injective at `V = k`, bounds
the tangent space
(`CoherentSituation.hasFiniteDimensionalTangentSpaces_coherentCFG_of_liftClassInjection`, through
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`). It also records the
flatness of `X_{k[V]}` over `Spec k[V]` that Stacks 08VW asks for.

## Main results

* `CoherentSituation.squareZeroLiftClassMap_bijective`,
  `CoherentSituation.squareZeroLiftClassMap_pullback`.
* `CoherentSituation.isFlat_projection_squareZeroTestScheme`.
* `CoherentSituation.hasFiniteDimensionalTangentSpaces_coherentCFG_of_liftClassInjection`.

## References

* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe e u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
  (hY : IsTerminal D.Y) {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S)
  (hk : B.Contains (Spec (.of k))) (x₀ : CoherentObject D)
  (hx : (coherentCFG D).val.p.obj x₀ = Deformation.Artin.algebraOver k B S hS toS hk)

/-- **A class of lifts of `x₀` to `k[M]` gives a class of lifts of its module to `X_{k[M]}`.** -/
def squareZeroLiftClassMap (M : Deformation.Artin.SiteModule k B) :
    Deformation.Artin.squareZeroLiftClasses k B S hS toS hk (coherentCFG D).val.p x₀ hx M →
      D.ThickeningLiftClass x₀ (D.squareZeroTestMap hY toS hk x₀ hx M) :=
  D.fiberLiftClass hY (b := eqToHom hx ≫ Deformation.Artin.squareZeroArrow k B S hS toS hk M)

/-- The map on classes of lifts is injective. -/
theorem squareZeroLiftClassMap_injective (M : Deformation.Artin.SiteModule k B) :
    Function.Injective (D.squareZeroLiftClassMap hY toS hk x₀ hx M) :=
  fiberLiftClass_injective hY

/-- The map on classes of lifts is bijective. -/
theorem squareZeroLiftClassMap_bijective (M : Deformation.Artin.SiteModule k B) :
    Function.Bijective (D.squareZeroLiftClassMap hY toS hk x₀ hx M) :=
  ⟨fiberLiftClass_injective hY, fiberLiftClass_surjective hY⟩

/-- **Pullback of lifts of `x₀` along `Spec k[N] ⟶ Spec k[M]` is pullback of lifts of its
module.** -/
theorem squareZeroLiftClassMap_pullback {M N : Deformation.Artin.SiteModule k B} (f : M ⟶ N)
    (a : Deformation.Artin.squareZeroLiftClasses k B S hS toS hk (coherentCFG D).val.p x₀ hx M)
    (b : Deformation.Artin.squareZeroLiftClasses k B S hS toS hk (coherentCFG D).val.p x₀ hx N)
    (hab : Deformation.Artin.IsPullbackOfSquareZeroLift k B S hS toS hk (coherentCFG D).val.p x₀
      hx f a b) :
    D.squareZeroLiftClassMap hY toS hk x₀ hx N b =
      ThickeningLiftClass.pullback (D.squareZeroTestSchemeMap hY toS f)
        (D.squareZeroTestMap_comp_squareZeroTestSchemeMap hY toS hk x₀ hx f)
        (D.squareZeroLiftClassMap hY toS hk x₀ hx M a) := by
  obtain ⟨a', b', rfl, rfl, φ, hφ, hw⟩ := hab
  exact fiberLiftClass_naturality hY (Deformation.Artin.squareZeroOverMap k B S hS toS f)
    (by rw [Category.assoc, Deformation.Artin.squareZeroArrow_naturality]) a' b' φ
    hφ.toIsHomLift hw

variable {D} in
/-- Over a test scheme which is the spectrum of a field, the base change of `X` is flat over it. -/
theorem isFlat_projection_of_left_eq (T : SchemesOver D.Y)
    (hT : T.left = Deformation.Artin.algebraOver k B S hS toS hk) :
    IsFlat B S hS (D.projection T).hom := by
  obtain ⟨l, r, h⟩ := T
  change l = _ at hT
  subst hT
  exact isFlat_toFieldSpace B S hS k hk toS _

include hk x₀ hx in
/-- **`X_{k[M]}` is flat over `Spec k[M]`**: it is the base change of `X_k ⟶ Spec k`, which is flat
because its target is the spectrum of a field, along the retraction `Spec k[M] ⟶ Spec k`
(Stacks 03MO for flatness, `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`). -/
theorem isFlat_projection_squareZeroTestScheme (M : Deformation.Artin.SiteModule k B) :
    IsFlat B S hS (D.projection (D.squareZeroTestScheme hY toS M)).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_baseChangeMap D.f (D.squareZeroTestRetraction hY toS hk x₀ hx M))
    (isFlat_projection_of_left_eq toS hk x₀.T hx)

variable {D} in
/-- **Finiteness of the tangent spaces of `Coh_{X/Y}` from a natural injection of lifts of
modules.**  Over a final `Y`, suppose that for every field-valued point `x₀` of `Coh_{X/Y}` the
classes of lifts of its module to `X_{k[V]}` map to the values `G(V)` of an additive `k`-linear
functor `G` on finite dimensional vector spaces, naturally in `V` (pullback of lifts along
`Spec k[V'] ⟶ Spec k[V]`), injectively at `V = k`, with `G(k)` finite dimensional.  Then the
tangent spaces of `Coh_{X/Y}` (axiom [3] of Artin's criterion) are finite dimensional. -/
theorem hasFiniteDimensionalTangentSpaces_coherentCFG_of_liftClassInjection
    (H : ∀ (k : Type u) [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
      (x₀ : CoherentObject D)
      (hx : (coherentCFG D).val.p.obj x₀ = Deformation.Artin.algebraOver k B S hS toS hk),
      ∃ (G : FGModuleCat.{u} k ⥤ ModuleCat.{e} k) (_ : G.Additive) (_ : G.Linear k)
        (_ : FiniteDimensional k (G.obj (FGModuleCat.of k k)))
        (t : ∀ V : FGModuleCat.{u} k, D.ThickeningLiftClass x₀
          (D.squareZeroTestMap hY toS hk x₀ hx ((Deformation.Artin.fgSiteModule B hk).obj V)) →
            G.obj V),
        (∀ {V V' : FGModuleCat.{u} k} (f : V ⟶ V') (c : D.ThickeningLiftClass x₀
            (D.squareZeroTestMap hY toS hk x₀ hx ((Deformation.Artin.fgSiteModule B hk).obj V))),
          t V' (ThickeningLiftClass.pullback
            (D.squareZeroTestSchemeMap hY toS ((Deformation.Artin.fgSiteModule B hk).map f))
            (D.squareZeroTestMap_comp_squareZeroTestSchemeMap hY toS hk x₀ hx _) c) =
            G.map f (t V c)) ∧
        Function.Injective (t (FGModuleCat.of k k))) :
    Stack.HasFiniteDimensionalTangentSpaces B S hS (coherentCFG D) := by
  intro k _ i₀ x₀ hx₀ _ _ s _ Λ _ _ _ iΛ _ hbase hx Dd hD
  have hp := (coherentCFG D).property
  have hb : B.inclusion.obj ((coherentCFG D).val.p.obj x₀).left = Spec (.of k) :=
    congrArg Comma.left hx₀
  have hk : B.Contains (Spec (.of k)) := hb ▸ ((coherentCFG D).val.p.obj x₀).left.property
  have hxo : (coherentCFG D).val.p.obj x₀ = Deformation.Artin.algebraOver k B S hS i₀ hk :=
    BigFppfOver.obj_injective_post_inclusion B S hS hx₀
  obtain ⟨G, _, _, _, T, hT, hTinj⟩ := H k i₀ hk x₀ hxo
  obtain ⟨c, -, hc₂⟩ := Deformation.Artin.exists_deformationClassEquiv_squareZeroLiftClasses B S hS
    iΛ i₀ hk (coherentCFG D).val.p hp x₀ hx hxo hD.predeformation.cofibered
  let t : ∀ V : FGModuleCat.{u} k, (Deformation.isomorphismClasses (BasedCategory.ofFunctor
      Dd.projection) hD.predeformation.cofibered).obj
        ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj V) → G.obj V :=
    fun V z => T V (D.squareZeroLiftClassMap hY i₀ hk x₀ hxo _ (c V z))
  refine Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection
    (BasedCategory.ofFunctor Dd.projection) hD.predeformation
    (Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory _ hD)
    G t ?_ ?_
  · intro V V' f z
    obtain ⟨b, -, hpb⟩ :=
      Deformation.Artin.exists_isCanonicalLiftTransition_isPullbackOfSquareZeroLift
        k B S hS i₀ hk (coherentCFG D).val.p x₀ hxo hp ((Deformation.Artin.fgSiteModule B hk).map f)
        (c V z)
    have h1 := hc₂ f z b hpb
    have h2 := D.squareZeroLiftClassMap_pullback hY i₀ hk x₀ hxo
      ((Deformation.Artin.fgSiteModule B hk).map f) (c V z) b hpb
    show T V' (D.squareZeroLiftClassMap hY i₀ hk x₀ hxo _ (c V' ((Deformation.isomorphismClasses
      (BasedCategory.ofFunctor Dd.projection) hD.predeformation.cofibered).map
        ((Deformation.artinianSquareZeroExtensionFunctor Λ k).map f) z))) = G.map f (t V z)
    rw [h1, h2]
    exact hT f _
  · intro z z' hzz
    exact (c _).injective (D.squareZeroLiftClassMap_injective hY i₀ hk x₀ hxo _ (hTinj hzz))

end AlgebraicGeometry.Space.CoherentSituation
