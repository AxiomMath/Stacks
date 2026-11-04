module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionFibered

/-!
# The valuative criterion for the stack of coherent sheaves, reduced to an extension problem

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is of
finite presentation, the standing data of Stacks 08KB, and let `Coh_{X/Y} ⟶ 𝒮_Y` be the
1-morphism of Stacks 08LP which forgets the module.  Stacks 0DM0 asserts that, for `f` proper, it
satisfies the existence part of the valuative criterion of Stacks 0CLK.  The first step of the
source's proof is that "taking base change, this immediately reduces to" an extension problem:
given a valuation ring `R` with fraction field `K`, a test scheme `Spec R ⟶ Y` and an object of
`Coh_{X/Y}` over the generic point `Spec K ⟶ Spec R ⟶ Y`, extend its module to an object of
`Coh_{X/Y}` over `Spec R`, that is, to a module on `X_R = X ×_Y Spec R` which is quasi-coherent,
of finite presentation, flat over `Spec R` and of proper support, whose inverse image on
`X_K` is the given module.

This file carries out that reduction.  The extension problem is the property
`AlgebraicGeometry.Space.CoherentSituation.ExtendsOverValuationRings` of the standing datum, and
`CoherentSituation.fiberedValuativeExistence_toBaseCFG_of_extendsOverValuationRings` shows that
it implies the existence part of the valuative criterion for `Coh_{X/Y} ⟶ 𝒮_Y`, in the form
`AlgebraicGeometry.Stack.FiberedValuativeExistence` for 1-morphisms of categories fibred in
groupoids.  An extension over `R` itself is a dotted arrow after the trivial extension of the
valuation ring, by `AlgebraicGeometry.Stack.FiberedValuativeSquare.exists_lift_of_diagonal`.

## Main definitions

* `AlgebraicGeometry.Space.baseCFG`: `𝒮_Y` as a category fibred in groupoids.
* `AlgebraicGeometry.Space.CoherentSituation.toBaseCFG`: the projection `Coh_{X/Y} ⟶ 𝒮_Y` of
  Stacks 08LP as a 1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Space.CoherentSituation.ExtendsOverValuationRings`: the extension problem
  of the proof of Stacks 0DM0.

## Main results

* `CategoryTheory.Functor.isFiberedInGroupoids_uliftHomDown`: the forgetful functor of a
  universe lift of the hom-sets is fibred in groupoids.
* `CoherentSituation.fiberedValuativeExistence_toBaseCFG_of_extendsOverValuationRings`:
  the extension problem implies the existence part of the valuative criterion for
  `Coh_{X/Y} ⟶ 𝒮_Y`.

## Implementation notes

The category `Coh_{X/Y}` has its hom-sets in the universe above that of the site, so it is not
an object of the 2-category `AlgebraicGeometry.AlgebraicStacks` of Stacks 03YP, whose total
categories have their hom-sets in the universe of the site; nor is it known to be algebraic in
this development (Stacks 09DS).  The existence part of the valuative criterion is therefore
stated through `AlgebraicGeometry.Stack.FiberedValuativeExistence`, which
`AlgebraicGeometry.Stack.valuativeCriterionExistence_iff_fiberedValuativeExistence` identifies
with `AlgebraicGeometry.Stack.ValuativeCriterion.Existence` of Stacks 0CLK on algebraic stacks.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

/-- The forgetful functor of a universe lift of the hom-sets is fibred in groupoids: it is an
isomorphism of categories. -/
theorem isFiberedInGroupoids_uliftHomDown (C : Type*) [Category C] :
    (ULiftHom.down : ULiftHom C ⥤ C).IsFiberedInGroupoids where
  exists_lift {V U} f x hx := by
    subst hx
    exact ⟨ULiftHom.objUp V, ULift.up f, IsHomLift.map (p := ULiftHom.down) (ULift.up f)⟩
  unique_lift {x y z} φ ψ f hf :=
    ⟨ULift.up f, ⟨rfl, ULift.ext _ _ hf⟩, fun χ hχ => ULift.ext _ _ hχ.1⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `𝒮_Y`, the test schemes over an algebraic space `Y`, as an object of the 2-category of
categories fibred in groupoids over the big fppf site of `S`. -/
def baseCFG (Y : AlgebraicSpaces B S hS) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (baseBasedCategory Y)
    (Functor.IsFiberedInGroupoids.comp _ _
      (Functor.isFiberedInGroupoids_uliftHomDown (SchemesOver Y))
      (Functor.IsFiberedInGroupoids.costructuredArrow_proj (schemeSpaceFunctor B S hS) Y))

/-- The projection `Coh_{X/Y} ⟶ 𝒮_Y` of Stacks 08LP, as a 1-morphism of categories fibred in
groupoids. -/
def CoherentSituation.toBaseCFG (D : CoherentSituation B S hS) :
    coherentCFG D ⟶ baseCFG D.Y :=
  Bicategory.InducedBicategory.mkHom (coherentToBase D.categoryData)

attribute [local instance] pointTopology

/-- **The extension problem of the proof of Stacks 0DM0.**  For every valuation ring `R` with
fraction field `K`, every test scheme `T` over `Y` lying over `Spec R`, and every object `A` of
`Coh_{X/Y}` together with a morphism `h : A.T ⟶ T` of test schemes lying over the canonical map
`Spec K ⟶ Spec R`, the module of `A` extends along `h`: there is a quasi-coherent
`𝒪_{X_T}`-module of finite presentation, flat over `T` and of proper support over `T`, whose
inverse image along `X_h : X_{A.T} ⟶ X_T` is isomorphic to the module of `A`. -/
def CoherentSituation.ExtendsOverValuationRings (D : CoherentSituation B S hS) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K))) (b : Spec (.of R) ⟶ S)
    (A : CoherentObject D) (T : SchemesOver D.Y) (h : A.T ⟶ T),
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
        siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ⟶
          siteObject B S hS hR b) h →
    ∃ (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
      (_ : F.IsQuasicoherentOnSite) (_ : F.IsFinitePresentationOnSite)
      (_ : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F)
      (_ : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
        (hU : IsClosed (D.support T F)),
        IsProperOver B S hS (D.space T).2
          ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom hp (D.support T F) hU)
      (φ : (modulePullback B S hS (D.relativeMap h)).obj F ⟶ A.F), IsIso φ

/-- **The base-change step of the proof of Stacks 0DM0.**  If the module of every object of
`Coh_{X/Y}` over the generic point of a valuation ring extends over the valuation ring, then the
projection `Coh_{X/Y} ⟶ 𝒮_Y` satisfies the existence part of the valuative criterion, with the
dotted arrow already over the given valuation ring. -/
theorem CoherentSituation.fiberedValuativeExistence_toBaseCFG_of_extendsOverValuationRings
    (D : CoherentSituation B S hS) (hD : D.ExtendsOverValuationRings) :
    Stack.FiberedValuativeExistence.{u, u + 1, u + 1} B S hS D.toBaseCFG := by
  intro q
  let pb : SchemesOver D.Y ⥤ BigFppfOver B S hS := CostructuredArrow.proj _ D.Y
  let h := q.link.down
  have hl := q.link_lift
  have hf := IsHomLift.fac' (baseCFG D.Y).val.p q.genericMap q.link
  have hX := IsHomLift.domain_eq (baseCFG D.Y).val.p q.genericMap q.link
  have hY := IsHomLift.codomain_eq (baseCFG D.Y).val.p q.genericMap q.link
  have hh : pb.IsHomLift q.genericMap h := IsHomLift.of_fac' (p := pb) q.genericMap h hX hY hf
  obtain ⟨F, hqc, hfp, hfl, hpr, φ, hφ⟩ := hD q.R q.K q.ring_mem q.field_mem
    q.base q.x (ULiftHom.objDown.{u + 1, u + 1} q.y) h (by
      have e : q.genericMap = Over.homMk (ObjectProperty.homMk
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)))) :=
        Over.OverMorphism.ext (B.inclusion.map_injective q.genericMap_left)
      rwa [← e])
  let a : CoherentObject D := ⟨(ULiftHom.objDown.{u + 1, u + 1} q.y), F, hqc, hfp, hfl, hpr⟩
  let m : CoherentHom q.x a := ⟨h, φ, hφ⟩
  exact q.exists_lift_of_diagonal a m
    (IsHomLift.of_fac' (p := (coherentCFG D).val.p) q.genericMap m hX hY hf) (𝟙 q.y)
    (IsHomLift.eqToHom_codomain_lift_id (p := (baseCFG D.Y).val.p) (rfl : q.y = q.y) hY)
    (Category.comp_id _)

end AlgebraicGeometry.Space

end
