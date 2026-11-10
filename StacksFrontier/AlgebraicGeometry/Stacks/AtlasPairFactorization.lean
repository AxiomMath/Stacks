module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedConnectedFactorizations
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveSmoothEtaleLocalLifts
import all StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedConnectedFactorizations

/-!
# Two morphisms to a smooth atlas factor locally through a common smooth refinement

Let `a : U₀ ⟶ 𝒜` be a smooth 1-morphism from the algebraic stack of a scheme to an algebraic stack,
and let `A₀ = a(𝟙_{U₀})` be the object it names. Two morphisms `γ₁, γ₂ : T ⟶ A₀` are an object of
the 2-fibre product `U₀ ×_{a, 𝒜, a} U₀` over the scheme `T` lies over. That 2-fibre product is an
algebraic stack (**Stacks 04T2**) both of whose projections are smooth (**Stacks 075W**), so
lifting the object to a smooth surjective scheme atlas of it (**Stacks 06XH**) produces, locally
on `T`, an object `E` of `𝒜` with two morphisms `β₁, β₂ : E ⟶ A₀` lying over smooth morphisms of
schemes, together with a morphism `T' ⟶ E` through which `γ₁` and `γ₂` both factor.

This is the *dominating* form of the middle step of
`AlgebraicGeometry.Stack.hasLocallyConnectedFactorizations_of_atlas`, recording in addition that
both legs lie over smooth morphisms; it is the geometric input of the step of Stacks 0778 which
compares two charts of an affine object (the source's `U ×_𝒳 U` is an algebraic space smooth
over each factor).

## Main results

* `AlgebraicGeometry.Stack.smooth_toScheme_obj_hom_of_isSmooth`: a smooth 1-morphism between
  represented algebraic stacks carries the terminal object to an object lying over a smooth
  morphism of schemes.
* `AlgebraicGeometry.Stack.exists_atlasPair_factorization`: the factorization described above.

## Implementation notes

The construction is the one of the private middle step of
`StacksFrontier.AlgebraicGeometry.Stacks.SubsitePrimedConnectedFactorizations`, whose auxiliary
declarations (the cartesian factorizations `kappaIso` and the object `squareObj` of the 2-fibre
product named by a pair of morphisms) are reused through `import all` rather than restated.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of the image of the terminal object under a smooth 1-morphism
between represented algebraic stacks is smooth. -/
theorem smooth_toScheme_obj_hom_of_isSmooth {V U : BigFppfOver B S hS}
    (h : schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U)
    (hsm : AlgebraicStacks.IsSmooth B S hS h) :
    Smooth ((BigFppfOver.toScheme B S hS).map
      ((CatFiberedInGroupoids.homFunctor h.hom).obj (Over.mk (𝟙 V))).hom) := by
  obtain ⟨q, hqsm, ⟨κ⟩⟩ := exists_schemeMap_of_isSmooth B S hS h hsm
  let c := κ.hom.hom.toNatTrans.app (Over.mk (𝟙 V))
  have hc : (Over.forget U).IsHomLift (𝟙 V) c := κ.hom.hom.isHomLift' (Over.mk (𝟙 V))
  have hfac : c.left = eqToHom ((IsHomLift.domain_eq (Over.forget U) (𝟙 V) c).trans
      (IsHomLift.codomain_eq (Over.forget U) (𝟙 V) c).symm) := by
    have := IsHomLift.fac' (Over.forget U) (𝟙 V) c
    simp only [Category.id_comp, eqToHom_trans] at this
    exact this
  change Smooth ((BigFppfOver.toScheme B S hS).map (h.hom.hom.obj (Over.mk (𝟙 V))).hom)
  rw [← Over.w c, hfac]
  have : Smooth ((BigFppfOver.toScheme B S hS).map
      ((schemeFibredCategoryMap B S hS q).hom.obj (Over.mk (𝟙 V))).hom) := by
    change Smooth ((BigFppfOver.toScheme B S hS).map (𝟙 V ≫ q))
    rwa [Category.id_comp]
  simp only [Functor.map_comp, eqToHom_map]
  infer_instance

variable {𝒜 : Stack.AlgebraicStacks.{u, w} B S hS} {U₀ : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒜) (τ : SiteKind)

/-- The image under the atlas of the canonical morphism out of an object `z` of the slice
lies over a smooth morphism of schemes if the structure morphism of `z` is smooth. -/
private theorem smooth_toScheme_map_atlasFunctor_toUnit (z : Over U₀)
    (hz : Smooth ((BigFppfOver.toScheme B S hS).map z.hom)) :
    Smooth ((BigFppfOver.toScheme B S hS).map
      (𝒜.val.val.p.map ((atlasFunctor B S hS a).map (toUnit B S hS z)))) :=
  smooth_toScheme_map_of_isHomLift B S hS 𝒜.val.val.p _ _
    (isHomLift_atlasFunctor_map B S hS a (toUnit B S hS z)) hz

/-- **Two morphisms to the object named by a smooth atlas factor locally through a common
object with two smooth legs.** Let `a : U₀ ⟶ 𝒜` be smooth and `γ₁, γ₂ : T ⟶ a(𝟙_{U₀})`. For a
topology `τ` in which a smooth surjective morphism of schemes generates a covering sieve, `T`
carries a `τ`-covering sieve along each arrow `h : T' ⟶ T` of which there are an object `E`, a
morphism `δ : T' ⟶ E` and two morphisms `β₁, β₂ : E ⟶ a(𝟙_{U₀})` lying over smooth morphisms of
schemes, with `δ ≫ β₁ = h ≫ γ₁` and `δ ≫ β₂ = h ≫ γ₂`. The object `E` is the image in `𝒜` of the
distinguished object of a smooth atlas of `U₀ ×_{a, 𝒜, a} U₀`. -/
theorem exists_atlasPair_factorization
    (hgen : ∀ {U : BigFppfOver B S hS} {W : B.Schemes} (m : W ⟶ U.left),
      Smooth (B.inclusion.map m) → Surjective (B.inclusion.map m) →
        Sieve.generate (Presieve.singleton
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U))
          ∈ BigFppfOver.baseOverTopology B S hS τ U)
    (hasm : AlgebraicStacks.IsSmooth B S hS a) (T : 𝒜.val.val.obj)
    (γ₁ γ₂ : T ⟶ (CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀))) :
    ∃ R ∈ BigFppfOver.associatedTopology B S hS 𝒜.val.val.p τ T,
      ∀ ⦃T' : 𝒜.val.val.obj⦄ ⦃h : T' ⟶ T⦄, R.arrows h →
        ∃ (E : 𝒜.val.val.obj) (δ : T' ⟶ E)
          (β₁ β₂ : E ⟶ (CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀))),
          δ ≫ β₁ = h ≫ γ₁ ∧ δ ≫ β₂ = h ≫ γ₂ ∧
            Smooth ((BigFppfOver.toScheme B S hS).map (𝒜.val.val.p.map β₁)) ∧
            Smooth ((BigFppfOver.toScheme B S hS).map (𝒜.val.val.p.map β₂)) := by
  have : 𝒜.val.val.p.IsFibered := 𝒜.val.isFiberedInGroupoids.isFibered
  obtain ⟨D₀, e, hesm, hesurj⟩ :=
    exists_smooth_surjective_schemeStack.{u, w} B S hS (atlasSquare B S hS a).pt
  obtain ⟨R, hR, hlift⟩ :=
    exists_covering_fibre_lift B S hS τ hgen e hesurj hesm (𝒜.val.val.p.obj T)
      (squareObj B S hS a γ₁ γ₂) (squareObj_base B S hS a γ₁ γ₂)
  refine ⟨_, Functor.functorPullback_mem_inheritedTopology 𝒜.val.val.p _ T hR, fun T' h hh => ?_⟩
  obtain ⟨xx, ζ, hζ⟩ := hlift hh
  have h1 : 𝒜.val.val.p.IsHomLift ζ.hbase ((atlasFunctor B S hS a).map ζ.a) :=
    PresheafOfCategories.isHomLift_map_of_comp a.hom.hom.w ζ.hbase ζ.a ζ.ha
  have h2 : 𝒜.val.val.p.IsHomLift (𝟙 (𝒜.val.val.p.obj T)) (kappaIso B S hS a γ₁).inv :=
    have := isHomLift_kappaIso_hom B S hS a γ₁
    IsHomLift.lift_id_inv 𝒜.val.val.p _ (kappaIso B S hS a γ₁)
  have h3 : 𝒜.val.val.p.IsHomLift ζ.hbase
      ((atlasFunctor B S hS a).map ζ.a ≫ (kappaIso B S hS a γ₁).inv) :=
    IsHomLift.comp_lift_id_right' 𝒜.val.val.p ζ.hbase _ (𝒜.val.val.p.obj T) _
  have h4 : 𝒜.val.val.p.IsHomLift (𝒜.val.val.p.map h)
      ((atlasFunctor B S hS a).map ζ.a ≫ (kappaIso B S hS a γ₁).inv) :=
    isHomLift_of_fac_eqToHom 𝒜.val.val.p ζ.hbase (𝒜.val.val.p.map h) _
      (IsHomLift.domain_eq (atlasSquare B S hS a).pt.val.val.p (𝒜.val.val.p.map h) ζ)
      (IsHomLift.codomain_eq (atlasSquare B S hS a).pt.val.val.p (𝒜.val.val.p.map h) ζ).symm
      (IsHomLift.fac' (atlasSquare B S hS a).pt.val.val.p (𝒜.val.val.p.map h) ζ) h3
  have hcart : 𝒜.val.val.p.IsStronglyCartesian (𝒜.val.val.p.map h)
      ((atlasFunctor B S hS a).map ζ.a ≫ (kappaIso B S hS a γ₁).inv) :=
    𝒜.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  obtain ⟨σ, ⟨-, hσ⟩, -⟩ := Functor.IsStronglyCartesian.universal_property 𝒜.val.val.p
    (𝒜.val.val.p.map h) ((atlasFunctor B S hS a).map ζ.a ≫ (kappaIso B S hS a γ₁).inv)
    (𝟙 _) (𝒜.val.val.p.map h) (Category.id_comp _).symm h
  let o := (CatFiberedInGroupoids.homFunctor e.hom).obj (Over.mk (𝟙 D₀))
  refine ⟨_, σ ≫ (atlasFunctor B S hS a).map
      ((CatFiberedInGroupoids.homFunctor e.hom).map (toUnit B S hS xx)).a,
    (atlasFunctor B S hS a).map (toUnit B S hS o.x),
    o.iso.hom ≫ (atlasFunctor B S hS a).map (toUnit B S hS o.y), ?_, ?_, ?_, ?_⟩
  · rw [← hσ]
    exact comp_map_eq_of_fac (atlasFunctor B S hS a)
      (toUnit B S hS ((CatFiberedInGroupoids.homFunctor e.hom).obj xx).x) _ _
      ((CatFiberedInGroupoids.homFunctor e.hom).map (toUnit B S hS xx)).a ζ.a
      (eq_toUnit B S hS _) (eq_toUnit B S hS _) σ (kappaIso B S hS a γ₁).inv γ₁
      (kappaIso_inv_comp_fst B S hS a γ₁ γ₂)
  · rw [← hσ]
    exact comp_map_eq_of_fac_comm (atlasFunctor B S hS a)
      (toUnit B S hS ((CatFiberedInGroupoids.homFunctor e.hom).obj xx).y) _ _
      ((CatFiberedInGroupoids.homFunctor e.hom).map (toUnit B S hS xx)).b ζ.b
      (eq_toUnit B S hS _) (eq_toUnit B S hS _)
      ((CatFiberedInGroupoids.homFunctor e.hom).map (toUnit B S hS xx)).a ζ.a
      ((CatFiberedInGroupoids.homFunctor e.hom).obj xx).iso.hom _ _
      ((CatFiberedInGroupoids.homFunctor e.hom).map (toUnit B S hS xx)).w ζ.w
      σ (kappaIso B S hS a γ₁).inv γ₂ (kappaIso_inv_comp_snd B S hS a γ₁ γ₂)
  · exact smooth_toScheme_map_atlasFunctor_toUnit B S hS a _ <|
      smooth_toScheme_obj_hom_of_isSmooth B S hS (e ≫ (atlasSquare B S hS a).fst)
        (AlgebraicStacks.isSmooth_comp B S hS e _ hesm (isSmooth_atlasSquare_fst B S hS a hasm))
  · rw [Functor.map_comp, Functor.map_comp]
    have := smooth_toScheme_map_atlasFunctor_toUnit B S hS a o.y <|
      smooth_toScheme_obj_hom_of_isSmooth B S hS (e ≫ (atlasSquare B S hS a).snd)
        (AlgebraicStacks.isSmooth_comp B S hS e _ hesm
          (AlgebraicStacks.isSmooth_baseChange B S hS a a (atlasSquare B S hS a).swap
            (Bicategory.isTwoFibreProduct_swap
              (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a a)) hasm))
    infer_instance

end AlgebraicGeometry.Stack

end
