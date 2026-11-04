module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.InfAutBaseChange
public import StacksFrontier.Deformation.Artin.Obstruction.LiftSituationPullback

/-!
# The transition of Stacks 07YA on infinitesimal automorphisms, as a map

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `x` be an
object of `𝒳` over `Spec A`, let `A ⟶ C` be a ring map and let `y ⟶ x` be a morphism of `𝒳`
lying over `Spec C ⟶ Spec A`. Beside the map `T_x(M) ⟶ T_y(N)` on tangent modules,
**Stacks 07YA** produces a companion map `Inf_x(M) ⟶ Inf_y(N)` on infinitesimal automorphisms:
conjugation by a cartesian arrow over `Spec C[N] ⟶ Spec A[M]` from the trivial lift of `y` to
the trivial lift of `x`.

The relation that map realizes, `Deformation.Artin.IsInfinitesimalAutomorphismBaseChange`, and
its two properties — single-valuedness
(`Deformation.Artin.eq_of_isInfinitesimalAutomorphismBaseChange`) and bijectivity at a
bijective map of coefficients
(`Deformation.Artin.bijective_of_isInfinitesimalAutomorphismBaseChange`) — were already in this
development, but nothing produced a map realizing it, so both were conditional on a hypothesis
no theorem discharged. In particular the relation was not even known to be inhabited: it asks
for a cartesian arrow between the two *trivial* lifts, and the pullback of the trivial lift of
`x` along `Spec C[N] ⟶ Spec A[M]` is only isomorphic to the trivial lift of `y`, not equal
to it.

What supplies that arrow is the presentation of the trivial lift as a pullback along the
retraction `Spec A[M] ⟶ Spec A` (`Deformation.Artin.trivialRetract`). The retractions commute
with the morphism `Spec C[N] ⟶ Spec A[M]` of trivial square-zero extensions, so the composite
`y[N] ⟶ y ⟶ x` and the retraction `x[M] ⟶ x` are two cartesian arrows into `x` over the two
legs of a commuting triangle, and the universal property produces the comparison between the
trivial lifts directly.

## Main definitions

* `Deformation.Artin.trivialLiftComparison` — the cartesian arrow from the trivial lift of `y`
  over `Spec C[N]` to the trivial lift of `x` over `Spec A[M]`, with the two identities that
  determine it.
* `Deformation.Artin.infAutBaseChange` — the transition of Stacks 07YA on the infinitesimal
  automorphisms themselves: conjugation by that arrow.
* `Deformation.Artin.infAutBaseChangeFun` — the transition read through the two
  identifications of `Inf_x(M)`, `Inf_y(N)` with those automorphisms.
* `Deformation.Artin.infAutBaseChangeHom` — the same map, as an `f`-semilinear map
  `Inf_x(M) ⟶ Inf_y(N)`, which is the same datum as the source's `A`-linear map.

## Main results

* `Deformation.Artin.squareZeroOverBaseMap_comp_squareZeroRetraction_of_semilinear` — the
  retractions of the two trivial square-zero extensions commute with the morphism
  `Spec C[N] ⟶ Spec A[M]` and the morphism of spectra of the ring map.
* `Deformation.Artin.isInfinitesimalAutomorphismBaseChange_infAutBaseChange` — the transition
  realizes the relation of Stacks 07YA on infinitesimal automorphisms.
* `Deformation.Artin.trivialLiftComparison_natural`,
  `Deformation.Artin.infAutBaseChange_natural`,
  `Deformation.Artin.infAutBaseChangeFun_natural` — the transition is natural in the two
  coefficient modules, which is what makes the induced map additive and semilinear.
* `Deformation.Artin.existsUnique_infAutBaseChange`,
  `Deformation.Artin.existsUnique_infAutBaseChangeHom` — **the companion map of Stacks 07YA on
  infinitesimal automorphisms.** There is exactly one map `Inf_x(M) ⟶ Inf_y(N)` realizing the
  transition, and it is `A`-linear.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

/-! ### The retractions of the two trivial square-zero extensions -/

section Retraction

universe u

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A') (B : BigFppfSite.{u})
  (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (toS' : Spec (.of A') ⟶ S)
  (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toS')
  (M : SiteModule A B) (N : SiteModule A' B)
  (ψ : (M.obj : Type u) →+ (N.obj : Type u))
  (hψ : ∀ (a : A) (m : M.obj), ψ (a • m) = f a • ψ m)

include hf hψ in
/-- **The retractions of the trivial square-zero extensions commute with the transition of
Stacks 07YA on bases.** The morphism `Spec A'[N] ⟶ Spec A[M]` attached to a ring map
`A ⟶ A'` and an `f`-semilinear map of coefficients, followed by the retraction
`Spec A[M] ⟶ Spec A`, is the retraction `Spec A'[N] ⟶ Spec A'` followed by
`Spec A' ⟶ Spec A`.

On rings both composites send `a` to `(f a, 0)`. This is the companion of
`Deformation.Artin.algebraOverMap_comp_squareZeroArrow` for the retractions rather than the
square-zero immersions, and it is what presents the two trivial lifts as pullbacks along the
two legs of one commuting triangle. -/
public theorem squareZeroOverBaseMap_comp_squareZeroRetraction_of_semilinear :
    squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ ≫
        squareZeroRetraction A B S hS toS hA M =
      squareZeroRetraction A' B S hS toS' hA' N ≫
        algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ)) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A' N.obj)) ≫
      Spec.map (CommRingCat.ofHom f)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  · rfl
  · change ψ (TrivSqZeroExt.inl a).snd = (TrivSqZeroExt.inl (f a)).snd
    rw [TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inl, ψ.map_zero]

end Retraction

/-! ### The trivial lift and its retraction, for a charted object -/

namespace ChartedObject

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- The cartesian arrow exhibiting the trivial lift of a charted object over `Spec A[M]` as
the pullback of `x` along the retraction `Spec A[M] ⟶ Spec A`. -/
public abbrev trivialRetract (P : ChartedObject B S hS p c) (hp : p.IsFiberedInGroupoids)
    (M : SiteModule P.ring B) : (P.trivialLift hp M).1.right ⟶ P.point :=
  Deformation.Artin.trivialRetract P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
    P.obj.obj.2 hp M

/-- The retraction `Spec A[M] ⟶ Spec A` of a charted object. -/
public abbrev squareZeroRetract (P : ChartedObject B S hS p c) (M : SiteModule P.ring B) :
    P.squareZeroBase M ⟶ P.obj.alg.over :=
  Deformation.Artin.squareZeroRetraction P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M

/-- The transition arrow of the trivial lifts of a charted object along a map of
coefficients. -/
public abbrev trivialTransition (P : ChartedObject B S hS p c) (hp : p.IsFiberedInGroupoids)
    {M N : SiteModule P.ring B} (s : M ⟶ N) :
    (P.trivialLift hp N).1.right ⟶ (P.trivialLift hp M).1.right :=
  Deformation.Artin.trivialTransition P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p
    P.point P.obj.obj.2 hp s

/-- The transition arrow of the trivial lifts of a charted object, as a morphism of lifts. -/
public abbrev trivialTransitionHom (P : ChartedObject B S hS p c)
    (hp : p.IsFiberedInGroupoids) {M N : SiteModule P.ring B} (s : M ⟶ N) :
    (P.trivialLift hp N).1 ⟶ (P.trivialLift hp M).1 :=
  trivialTransitionUnder P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
    P.obj.obj.2 hp s

/-- The functor `Inf_x` of a charted object, with values in sets. -/
public abbrev infAutSet (P : ChartedObject B S hS p c) (hp : p.IsFiberedInGroupoids) :
    SiteModule P.ring B ⥤ Type w :=
  infinitesimalAutomorphismSetFunctor P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p
    P.point P.obj.obj.2 hp

/-- The transition of `Inf_x` along a map of coefficients is conjugation by the transition
arrow of the trivial lifts. -/
public theorem infAutSet_map_conj (P : ChartedObject B S hS p c)
    (hp : p.IsFiberedInGroupoids) {M N : SiteModule P.ring B} (s : M ⟶ N)
    (θ : P.trivialLift hp M ⟶ P.trivialLift hp M) :
    ((P.infAutSet hp).map s θ).1.right ≫ P.trivialTransition hp s =
      P.trivialTransition hp s ≫ θ.1.right := by
  rw [infAutSetFunctor_map_eq P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
    P.obj.obj.2 hp s θ]
  exact congrArg Under.Hom.right (fiberEndRestrict_fac (Under.post p)
    (underPost_isFiberedInGroupoids p hp P.point) (P.trivialTransitionHom hp s)
    (trivialTransitionUnder_isHomLift P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p
      P.point P.obj.obj.2 hp s) θ)

end ChartedObject

/-! ### The comparison of the two trivial lifts -/

section TrivialComparison

open CategoryTheory.Functor

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
  (hp : p.IsFiberedInGroupoids) {P Q : ChartedObject B S hS p c}
  (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring) (halg : f = h.alg.ringMap)

include halg in
/-- `Deformation.Artin.squareZeroOverBaseMap_comp_squareZeroRetraction_of_semilinear` for a
morphism of charted objects. -/
public theorem chartedSquareZeroBaseMap_comp_squareZeroRetract
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    chartedSquareZeroBaseMap h f halg ψ ≫ P.squareZeroRetract M =
      Q.squareZeroRetract N ≫ h.alg.specMap := by
  rw [specMap_eq_algebraOverMap h f halg]
  exact squareZeroOverBaseMap_comp_squareZeroRetraction_of_semilinear f B S hS P.obj.alg.toScheme
    Q.obj.alg.toScheme P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg) M N
    (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ)

include hp halg in
/-- **The comparison of the two trivial lifts of Stacks 07YA.** The trivial lift of `y` over
`Spec C[N]` carries a strongly cartesian arrow over `Spec C[N] ⟶ Spec A[M]` to the trivial
lift of `x` over `Spec A[M]`, compatible with `y ⟶ x` and with the two retractions.

Each trivial lift is a pullback of its object along the retraction of its base, the two
retractions commute with the morphism of bases
(`Deformation.Artin.chartedSquareZeroBaseMap_comp_squareZeroRetract`), and every arrow of a
category fibred in groupoids is strongly cartesian: so the universal property of the
retraction of the trivial lift of `x` applies to the composite `y[N] ⟶ y ⟶ x`. -/
public def trivialLiftComparison {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    { ρ : (Q.trivialLift hp N).1.right ⟶ (P.trivialLift hp M).1.right //
      p.IsStronglyCartesian (chartedSquareZeroBaseMap h f halg ψ) ρ ∧
        ρ ≫ P.trivialRetract hp M = Q.trivialRetract hp N ≫ h.objMap ∧
          (Q.trivialLift hp N).1.hom ≫ ρ = h.objMap ≫ (P.trivialLift hp M).1.hom } := by
  have hrP : p.IsHomLift (P.squareZeroRetract M) (P.trivialRetract hp M) :=
    trivialRetract_isHomLift P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
      P.obj.obj.2 hp M
  have hrQ : p.IsHomLift (Q.squareZeroRetract N) (Q.trivialRetract hp N) :=
    trivialRetract_isHomLift Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem p Q.point
      Q.obj.obj.2 hp N
  have hcartP : p.IsStronglyCartesian (P.squareZeroRetract M) (P.trivialRetract hp M) :=
    have := hrP
    hp.isStronglyCartesian_homLift _ _
  have hcomp : p.IsHomLift (Q.squareZeroRetract N ≫ h.alg.specMap)
      (Q.trivialRetract hp N ≫ h.objMap) :=
    isHomLift_comp p hrQ h.objMap_isHomLift
  have hg : Q.squareZeroRetract N ≫ h.alg.specMap =
      chartedSquareZeroBaseMap h f halg ψ ≫ P.squareZeroRetract M :=
    (chartedSquareZeroBaseMap_comp_squareZeroRetract h f halg ψ).symm
  have := hcartP
  have := hcomp
  refine ⟨IsStronglyCartesian.map p (P.squareZeroRetract M) (P.trivialRetract hp M) hg
    (Q.trivialRetract hp N ≫ h.objMap), ?_, ?_, ?_⟩
  · have : p.IsHomLift (chartedSquareZeroBaseMap h f halg ψ)
        (IsStronglyCartesian.map p (P.squareZeroRetract M) (P.trivialRetract hp M) hg
          (Q.trivialRetract hp N ≫ h.objMap)) :=
      IsStronglyCartesian.map_isHomLift p (P.squareZeroRetract M) (P.trivialRetract hp M) hg _
    exact hp.isStronglyCartesian_homLift _ _
  · exact IsStronglyCartesian.fac p (P.squareZeroRetract M) (P.trivialRetract hp M) hg _
  · have hρ : p.IsHomLift (chartedSquareZeroBaseMap h f halg ψ)
        (IsStronglyCartesian.map p (P.squareZeroRetract M) (P.trivialRetract hp M) hg
          (Q.trivialRetract hp N ≫ h.objMap)) :=
      IsStronglyCartesian.map_isHomLift p (P.squareZeroRetract M) (P.trivialRetract hp M) hg _
    have hsqQ : p.IsHomLift
        (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N)
        (Q.trivialLift hp N).1.hom :=
      isHomLift_fiberUnder_hom p _ Q.obj.obj (Q.trivialLift hp N)
    have hsqP : p.IsHomLift
        (squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M)
        (P.trivialLift hp M).1.hom :=
      isHomLift_fiberUnder_hom p _ P.obj.obj (P.trivialLift hp M)
    have hleft : p.IsHomLift
        (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫
          chartedSquareZeroBaseMap h f halg ψ)
        ((Q.trivialLift hp N).1.hom ≫
          IsStronglyCartesian.map p (P.squareZeroRetract M) (P.trivialRetract hp M) hg
            (Q.trivialRetract hp N ≫ h.objMap)) := isHomLift_comp p hsqQ hρ
    have hright : p.IsHomLift
        (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫
          chartedSquareZeroBaseMap h f halg ψ)
        (h.objMap ≫ (P.trivialLift hp M).1.hom) := by
      rw [← specMap_comp_squareZeroArrow_chartedSquareZeroBaseMap h f halg ψ]
      exact isHomLift_comp p h.objMap_isHomLift hsqP
    have := hleft
    have := hright
    refine IsStronglyCartesian.ext p (P.squareZeroRetract M) (P.trivialRetract hp M)
      (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N ≫
        chartedSquareZeroBaseMap h f halg ψ) ?_
    rw [Category.assoc, IsStronglyCartesian.fac p (P.squareZeroRetract M)
      (P.trivialRetract hp M) hg, ← Category.assoc,
      trivialRetract_fac Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem p Q.point
        Q.obj.obj.2 hp N, Category.id_comp, Category.assoc,
      trivialRetract_fac P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
        P.obj.obj.2 hp M, Category.comp_id]

/-- The composite of the comparison with a transition arrow lies over the composite of the
corresponding arrows of bases. -/
private theorem trivialLiftComparison_comp_trivialTransition_isHomLift
    {M₁ M₂ : SiteModule P.ring B} {N : SiteModule Q.ring B} (s : M₁ ⟶ M₂)
    (ψ : M₂.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    p.IsHomLift (chartedSquareZeroBaseMap h f halg ψ ≫
      squareZeroOverMap P.ring B S hS P.obj.alg.toScheme s)
      ((trivialLiftComparison hp h f halg ψ).1 ≫ P.trivialTransition hp s) :=
  isHomLift_comp p (trivialLiftComparison hp h f halg ψ).2.1.toIsHomLift
    (trivialTransition_isHomLift P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
      P.obj.obj.2 hp s)

include hp halg in
/-- **The comparison of the trivial lifts is natural in the two coefficient modules.** The
transition arrows of the trivial lifts along a map `s` of coefficients on the source side and
a map `t` on the target side, compatible with the two maps of coefficients across the ring
map, form a commutative square with the two comparisons.

Both composites are arrows over the same arrow of the base, by
`Deformation.Artin.chartedSquareZeroBaseMap_naturality`, and they agree after the cartesian
retraction of the trivial lift of `x` over `Spec A[M₁]`, because each transition arrow is
compatible with the two retractions it connects. -/
public theorem trivialLiftComparison_natural {M₁ M₂ : SiteModule P.ring B}
    {N₁ N₂ : SiteModule Q.ring B} (s : M₁ ⟶ M₂) (t : N₁ ⟶ N₂)
    (ψ₁ : M₁.obj ⟶ (ModuleCat.restrictScalars f).obj N₁.obj)
    (ψ₂ : M₂.obj ⟶ (ModuleCat.restrictScalars f).obj N₂.obj)
    (hcompat : s.hom ≫ ψ₂ = ψ₁ ≫ (ModuleCat.restrictScalars f).map t.hom) :
    (trivialLiftComparison hp h f halg ψ₂).1 ≫ P.trivialTransition hp s =
      Q.trivialTransition hp t ≫ (trivialLiftComparison hp h f halg ψ₁).1 := by
  have hsQ : p.IsHomLift (squareZeroOverMap Q.ring B S hS Q.obj.alg.toScheme t)
      (Q.trivialTransition hp t) :=
    trivialTransition_isHomLift Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem p Q.point
      Q.obj.obj.2 hp t
  have hleft := trivialLiftComparison_comp_trivialTransition_isHomLift hp h f halg s ψ₂
  have hright : p.IsHomLift (chartedSquareZeroBaseMap h f halg ψ₂ ≫
      squareZeroOverMap P.ring B S hS P.obj.alg.toScheme s)
      (Q.trivialTransition hp t ≫ (trivialLiftComparison hp h f halg ψ₁).1) := by
    rw [chartedSquareZeroBaseMap_naturality h f halg s t ψ₁ ψ₂ hcompat]
    exact isHomLift_comp p hsQ (trivialLiftComparison hp h f halg ψ₁).2.1.toIsHomLift
  have hrP : p.IsHomLift (P.squareZeroRetract M₁) (P.trivialRetract hp M₁) :=
    trivialRetract_isHomLift P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
      P.obj.obj.2 hp M₁
  have hcartP : p.IsStronglyCartesian (P.squareZeroRetract M₁) (P.trivialRetract hp M₁) :=
    have := hrP
    hp.isStronglyCartesian_homLift _ _
  have := hcartP
  have := hleft
  have := hright
  refine IsStronglyCartesian.ext p (P.squareZeroRetract M₁) (P.trivialRetract hp M₁)
    (chartedSquareZeroBaseMap h f halg ψ₂ ≫
      squareZeroOverMap P.ring B S hS P.obj.alg.toScheme s) ?_
  rw [Category.assoc, trivialTransition_comp_retract P.ring B S hS P.obj.alg.toScheme
      P.obj.alg.mem p P.point P.obj.obj.2 hp s,
    (trivialLiftComparison hp h f halg ψ₂).2.2.1, Category.assoc,
    (trivialLiftComparison hp h f halg ψ₁).2.2.1, ← Category.assoc,
    trivialTransition_comp_retract Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem p Q.point
      Q.obj.obj.2 hp t]

end TrivialComparison

/-! ### The transition on infinitesimal automorphisms -/

section InfAutMap

open CategoryTheory.Functor

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
  (hp : p.IsFiberedInGroupoids) {P Q : ChartedObject B S hS p c}
  (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring) (halg : f = h.alg.ringMap)

include hp halg in
/-- **The transition of Stacks 07YA on infinitesimal automorphisms.** The automorphism of the
trivial lift of `y` over `Spec C[N]` obtained by conjugating an automorphism `θ` of the trivial
lift of `x` over `Spec A[M]` with the comparison arrow
`Deformation.Artin.trivialLiftComparison`. -/
public def infAutBaseChange {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (θ : P.trivialLift hp M ⟶ P.trivialLift hp M) :
    Q.trivialLift hp N ⟶ Q.trivialLift hp N :=
  (underFiberConjugate p (chartedSquareZeroBaseMap h f halg ψ) h.objMap
    (trivialLiftComparison hp h f halg ψ).1 (trivialLiftComparison hp h f halg ψ).2.1
    (trivialLiftComparison hp h f halg ψ).2.2.2 θ).1

include hp halg in
/-- The defining conjugation identity of `Deformation.Artin.infAutBaseChange`. -/
public theorem infAutBaseChange_conj {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (θ : P.trivialLift hp M ⟶ P.trivialLift hp M) :
    (infAutBaseChange hp h f halg ψ θ).1.right ≫ (trivialLiftComparison hp h f halg ψ).1 =
      (trivialLiftComparison hp h f halg ψ).1 ≫ θ.1.right :=
  (underFiberConjugate p (chartedSquareZeroBaseMap h f halg ψ) h.objMap
    (trivialLiftComparison hp h f halg ψ).1 (trivialLiftComparison hp h f halg ψ).2.1
    (trivialLiftComparison hp h f halg ψ).2.2.2 θ).2

include hp halg in
/-- **The transition of Stacks 07YA on infinitesimal automorphisms is natural in the two
coefficient modules.** The map `s` of coefficients on the source side and the map `t` on the
target side are assumed compatible with the two maps of coefficients across the ring map, and
the two transitions of infinitesimal automorphisms are given by their defining conjugation
identities, which is how `Inf_x` presents them (`Deformation.Artin.fiberEndRestrict_fac`).

This is the companion of `Deformation.Artin.tangentBaseChangeFun_natural`, and it is what makes
the induced map on `Inf_x` additive and semilinear: the linear structure of `Inf_x` is built
from the transitions along the maps of coefficients alone. -/
public theorem infAutBaseChange_natural {M₁ M₂ : SiteModule P.ring B}
    {N₁ N₂ : SiteModule Q.ring B} (s : M₁ ⟶ M₂) (t : N₁ ⟶ N₂)
    (ψ₁ : M₁.obj ⟶ (ModuleCat.restrictScalars f).obj N₁.obj)
    (ψ₂ : M₂.obj ⟶ (ModuleCat.restrictScalars f).obj N₂.obj)
    (hcompat : s.hom ≫ ψ₂ = ψ₁ ≫ (ModuleCat.restrictScalars f).map t.hom)
    (θ : P.trivialLift hp M₁ ⟶ P.trivialLift hp M₁)
    (θ' : P.trivialLift hp M₂ ⟶ P.trivialLift hp M₂)
    (hθ : θ'.1.right ≫ P.trivialTransition hp s = P.trivialTransition hp s ≫ θ.1.right)
    (χ : Q.trivialLift hp N₂ ⟶ Q.trivialLift hp N₂)
    (hχ : χ.1.right ≫ Q.trivialTransition hp t =
      Q.trivialTransition hp t ≫ (infAutBaseChange hp h f halg ψ₁ θ).1.right) :
    infAutBaseChange hp h f halg ψ₂ θ' = χ := by
  have hσlift := trivialLiftComparison_comp_trivialTransition_isHomLift hp h f halg s ψ₂
  have hσ : p.IsStronglyCartesian (chartedSquareZeroBaseMap h f halg ψ₂ ≫
      squareZeroOverMap P.ring B S hS P.obj.alg.toScheme s)
      ((trivialLiftComparison hp h f halg ψ₂).1 ≫ P.trivialTransition hp s) :=
    have := hσlift
    hp.isStronglyCartesian_homLift _ _
  have hnat := trivialLiftComparison_natural hp h f halg s t ψ₁ ψ₂ hcompat
  refine eq_of_conj_underFiber p _ _ hσ (θ := θ) ?_ ?_
  · rw [← Category.assoc, infAutBaseChange_conj hp h f halg ψ₂ θ', Category.assoc, hθ,
      ← Category.assoc]
  · rw [hnat, ← Category.assoc, hχ, Category.assoc, infAutBaseChange_conj hp h f halg ψ₁ θ,
      ← Category.assoc]

include hp halg in
/-- **`Deformation.Artin.infAutBaseChange` realizes the transition of Stacks 07YA on
infinitesimal automorphisms.** With this the relation
`Deformation.Artin.IsInfinitesimalAutomorphismBaseChange` is known to be inhabited at every
`θ`, which is what its single-valuedness and its bijectivity at a bijective map of
coefficients were waiting for. -/
public theorem isInfinitesimalAutomorphismBaseChange_infAutBaseChange
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (θ : P.trivialLift hp M ⟶ P.trivialLift hp M) :
    IsInfinitesimalAutomorphismBaseChange hp h f ψ θ (infAutBaseChange hp h f halg ψ θ) :=
  ⟨chartedSquareZeroBaseMap h f halg ψ, isSquareZeroBaseMap_squareZeroOverBaseMap h f halg ψ,
    (trivialLiftComparison hp h f halg ψ).1, (trivialLiftComparison hp h f halg ψ).2.1,
    (trivialLiftComparison hp h f halg ψ).2.2.2, infAutBaseChange_conj hp h f halg ψ θ⟩

variable
  (F : InfinitesimalAutomorphismFunctorData P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p
    P.point P.obj.obj.2 hp)
  (G : InfinitesimalAutomorphismFunctorData Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem p
    Q.point Q.obj.obj.2 hp)

include hp halg in
/-- **The companion map of Stacks 07YA on infinitesimal automorphisms**, as a bare function:
the conjugation `Deformation.Artin.infAutBaseChange` read through the two identifications of
`Inf_x(M)`, `Inf_y(N)` with the automorphisms of the trivial lifts. -/
public def infAutBaseChangeFun {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    ↥(F.functor.obj M) → ↥(G.functor.obj N) :=
  fun θ => (G.autEquiv N).symm (infAutBaseChange hp h f halg ψ (F.autEquiv M θ))

include hp halg in
/-- The companion map realizes the transition of Stacks 07YA on infinitesimal
automorphisms. -/
public theorem isInfinitesimalAutomorphismBaseChange_infAutBaseChangeFun
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (θ : ↥(F.functor.obj M)) :
    IsInfinitesimalAutomorphismBaseChange hp h f ψ (F.autEquiv M θ)
      (G.autEquiv N (infAutBaseChangeFun hp h f halg F G ψ θ)) := by
  have heq : G.autEquiv N (infAutBaseChangeFun hp h f halg F G ψ θ) =
      infAutBaseChange hp h f halg ψ (F.autEquiv M θ) :=
    Equiv.apply_symm_apply (G.autEquiv N) _
  rw [heq]
  exact isInfinitesimalAutomorphismBaseChange_infAutBaseChange hp h f halg ψ (F.autEquiv M θ)

include hp halg in
/-- **The companion map of Stacks 07YA on infinitesimal automorphisms is natural in the two
coefficient modules.** -/
public theorem infAutBaseChangeFun_natural {M₁ M₂ : SiteModule P.ring B}
    {N₁ N₂ : SiteModule Q.ring B} (s : M₁ ⟶ M₂) (t : N₁ ⟶ N₂)
    (ψ₁ : M₁.obj ⟶ (ModuleCat.restrictScalars f).obj N₁.obj)
    (ψ₂ : M₂.obj ⟶ (ModuleCat.restrictScalars f).obj N₂.obj)
    (hcompat : s.hom ≫ ψ₂ = ψ₁ ≫ (ModuleCat.restrictScalars f).map t.hom)
    (z : ↥(F.functor.obj M₁)) :
    infAutBaseChangeFun hp h f halg F G ψ₂ (F.functor.map s z) =
      G.functor.map t (infAutBaseChangeFun hp h f halg F G ψ₁ z) := by
  apply (G.autEquiv N₂).injective
  have hL : G.autEquiv N₂ (infAutBaseChangeFun hp h f halg F G ψ₂ (F.functor.map s z)) =
      infAutBaseChange hp h f halg ψ₂ (F.autEquiv M₂ (F.functor.map s z)) :=
    Equiv.apply_symm_apply _ _
  have hR : G.autEquiv N₂ (G.functor.map t (infAutBaseChangeFun hp h f halg F G ψ₁ z)) =
      (Q.infAutSet hp).map t (G.autEquiv N₁ (infAutBaseChangeFun hp h f halg F G ψ₁ z)) :=
    G.autEquiv_natural t _
  have hR₁ : G.autEquiv N₁ (infAutBaseChangeFun hp h f halg F G ψ₁ z) =
      infAutBaseChange hp h f halg ψ₁ (F.autEquiv M₁ z) := Equiv.apply_symm_apply _ _
  rw [hL, hR, hR₁, F.autEquiv_natural s z]
  exact infAutBaseChange_natural hp h f halg s t ψ₁ ψ₂ hcompat (F.autEquiv M₁ z) _
    (P.infAutSet_map_conj hp s (F.autEquiv M₁ z)) _
    (Q.infAutSet_map_conj hp t (infAutBaseChange hp h f halg ψ₁ (F.autEquiv M₁ z)))

include hp halg in
/-- **The companion map of Stacks 07YA on infinitesimal automorphisms is additive.** -/
public theorem infAutBaseChangeFun_add {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (z₁ z₂ : ↥(F.functor.obj M)) :
    infAutBaseChangeFun hp h f halg F G ψ (z₁ + z₂) =
      infAutBaseChangeFun hp h f halg F G ψ z₁ +
        infAutBaseChangeFun hp h f halg F G ψ z₂ := by
  have := F.additive
  have := G.additive
  have := F.linear
  have := G.linear
  set i₁ := siteModuleInl P.ring B P.obj.alg.mem M M
  set i₂ := siteModuleInr P.ring B P.obj.alg.mem M M
  set q₁ := siteModuleFst P.ring B P.obj.alg.mem M M
  set q₂ := siteModuleSnd P.ring B P.obj.alg.mem M M
  set r₁ := siteModuleFst Q.ring B Q.obj.alg.mem N N
  set r₂ := siteModuleSnd Q.ring B Q.obj.alg.mem N N
  set Ψ := prodRestrictScalarsHom f P.obj.alg.mem Q.obj.alg.mem ψ
  have hc₁ : q₁.hom ≫ ψ = Ψ ≫ (ModuleCat.restrictScalars f).map r₁.hom := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    change ψ m.1 = (prodRestrictScalarsHom f P.obj.alg.mem Q.obj.alg.mem ψ m).1
    rw [prodRestrictScalarsHom_apply]
  have hc₂ : q₂.hom ≫ ψ = Ψ ≫ (ModuleCat.restrictScalars f).map r₂.hom := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    change ψ m.2 = (prodRestrictScalarsHom f P.obj.alg.mem Q.obj.alg.mem ψ m).2
    rw [prodRestrictScalarsHom_apply]
  have hcs : (q₁ + q₂).hom ≫ ψ =
      Ψ ≫ (ModuleCat.restrictScalars f).map (r₁ + r₂).hom := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    change ψ (m.1 + m.2) =
      (prodRestrictScalarsHom f P.obj.alg.mem Q.obj.alg.mem ψ m).1 +
        (prodRestrictScalarsHom f P.obj.alg.mem Q.obj.alg.mem ψ m).2
    rw [prodRestrictScalarsHom_apply]
    exact map_add ψ.hom m.1 m.2
  set z := F.functor.map i₁ z₁ + F.functor.map i₂ z₂ with hz
  have hproj (j : M ⟶ siteModuleProd P.ring B P.obj.alg.mem M M)
      (k : siteModuleProd P.ring B P.obj.alg.mem M M ⟶ M) (hjk : j ≫ k = 𝟙 M)
      (y : ↥(F.functor.obj M)) : F.functor.map k (F.functor.map j y) = y := by
    simpa using congrArg (fun e => e y) (congrArg F.functor.map hjk)
  have hzero (j : M ⟶ siteModuleProd P.ring B P.obj.alg.mem M M)
      (k : siteModuleProd P.ring B P.obj.alg.mem M M ⟶ M) (hjk : j ≫ k = 0)
      (y : ↥(F.functor.obj M)) : F.functor.map k (F.functor.map j y) = 0 := by
    simpa using congrArg (fun e => e y) (congrArg F.functor.map hjk)
  have hz₁ : F.functor.map q₁ z = z₁ := by
    rw [hz, _root_.map_add, hproj i₁ q₁ (siteModuleInl_comp_fst P.ring B P.obj.alg.mem M M) z₁,
      hzero i₂ q₁ (siteModuleInr_comp_fst P.ring B P.obj.alg.mem M M) z₂, add_zero]
  have hz₂ : F.functor.map q₂ z = z₂ := by
    rw [hz, _root_.map_add, hzero i₁ q₂ (siteModuleInl_comp_snd P.ring B P.obj.alg.mem M M) z₁,
      hproj i₂ q₂ (siteModuleInr_comp_snd P.ring B P.obj.alg.mem M M) z₂, zero_add]
  have hn₁ := infAutBaseChangeFun_natural hp h f halg F G q₁ r₁ Ψ ψ hc₁ z
  have hn₂ := infAutBaseChangeFun_natural hp h f halg F G q₂ r₂ Ψ ψ hc₂ z
  have hns := infAutBaseChangeFun_natural hp h f halg F G (q₁ + q₂) (r₁ + r₂) Ψ ψ hcs z
  rw [hz₁] at hn₁
  rw [hz₂] at hn₂
  have hsum : F.functor.map (q₁ + q₂) z = z₁ + z₂ := by
    rw [F.functor.map_add]
    change F.functor.map q₁ z + F.functor.map q₂ z = z₁ + z₂
    rw [hz₁, hz₂]
  rw [hsum, G.functor.map_add] at hns
  change infAutBaseChangeFun hp h f halg F G ψ (z₁ + z₂) =
    G.functor.map r₁ (infAutBaseChangeFun hp h f halg F G Ψ z) +
      G.functor.map r₂ (infAutBaseChangeFun hp h f halg F G Ψ z) at hns
  rw [hns, ← hn₁, ← hn₂]

include hp halg in
/-- **The companion map of Stacks 07YA on infinitesimal automorphisms is semilinear over the
ring map**, that is, `A`-linear into the restriction of scalars of `Inf_y(N)`. -/
public theorem infAutBaseChangeFun_smul {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (a : P.ring)
    (z : ↥(F.functor.obj M)) :
    infAutBaseChangeFun hp h f halg F G ψ (a • z) =
      f a • infAutBaseChangeFun hp h f halg F G ψ z := by
  have := F.additive
  have := G.additive
  have := F.linear
  have := G.linear
  have hcompat : (a • (𝟙 M)).hom ≫ ψ =
      ψ ≫ (ModuleCat.restrictScalars f).map ((f a • (𝟙 N)).hom) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    change ψ (a • m) = f a • ψ m
    exact restrictScalarsAddHom_smul f ψ a m
  have hn := infAutBaseChangeFun_natural hp h f halg F G (a • (𝟙 M)) (f a • (𝟙 N)) ψ ψ
    hcompat z
  have hF : F.functor.map (a • (𝟙 M)) z = a • z := by
    rw [Functor.map_smul, F.functor.map_id]
    rfl
  have hG : ∀ y : ↥(G.functor.obj N), G.functor.map (f a • (𝟙 N)) y = f a • y := by
    intro y
    rw [Functor.map_smul, G.functor.map_id]
    rfl
  rwa [hF, hG] at hn

include hp halg in
/-- **The companion map of Stacks 07YA on infinitesimal automorphisms**, as an `f`-semilinear
map — the `A`-linear map `Inf_x(M) ⟶ Inf_y(N)` of the source. -/
public def infAutBaseChangeHom {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    ↥(F.functor.obj M) →ₛₗ[f] ↥(G.functor.obj N) where
  toFun := infAutBaseChangeFun hp h f halg F G ψ
  map_add' := infAutBaseChangeFun_add hp h f halg F G ψ
  map_smul' := infAutBaseChangeFun_smul hp h f halg F G ψ

/-- The semilinear map `infAutBaseChangeHom` evaluates as the function
`infAutBaseChangeFun`. -/
@[simp]
public theorem infAutBaseChangeHom_apply {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (z : ↥(F.functor.obj M)) :
    infAutBaseChangeHom hp h f halg F G ψ z = infAutBaseChangeFun hp h f halg F G ψ z := rfl

/-- Any two maps on infinitesimal automorphisms realizing the transition of Stacks 07YA
agree. -/
public theorem eq_of_isInfinitesimalAutomorphismBaseChange_autEquiv
    (hRS : SatisfiesRSStar B S hS p hp) {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    {σ σ' : ↥(F.functor.obj M) → ↥(G.functor.obj N)}
    (hσ : ∀ θ, IsInfinitesimalAutomorphismBaseChange hp h f ψ (F.autEquiv M θ)
      (G.autEquiv N (σ θ)))
    (hσ' : ∀ θ, IsInfinitesimalAutomorphismBaseChange hp h f ψ (F.autEquiv M θ)
      (G.autEquiv N (σ' θ))) :
    σ = σ' :=
  funext fun θ => (G.autEquiv N).injective
    (eq_of_isInfinitesimalAutomorphismBaseChange hp hRS h f ψ (hσ θ) (hσ' θ))

include hp halg in
/-- **The companion map of Stacks 07YA on infinitesimal automorphisms.** Let `x` be an object
of a category fibred in groupoids over the big fppf site of `S` lying over `Spec A`, let
`A ⟶ C` be a ring map and let `y ⟶ x` be a morphism lying over `Spec C ⟶ Spec A`, so that
`y = x|_{Spec C}`. For `M ∈ Mod_A`, `N ∈ Mod_C` and an `A`-linear map `M ⟶ N` there is exactly
one map `Inf_x(M) ⟶ Inf_y(N)` carrying each infinitesimal automorphism of the trivial lift of
`x` over `Spec A[M]` to its conjugate along a cartesian arrow over `Spec C[N] ⟶ Spec A[M]`.

Uniqueness is `Deformation.Artin.eq_of_isInfinitesimalAutomorphismBaseChange`, which needs
(RS*): a cartesian arrow realizing the transition is unique only up to an automorphism of the
trivial lift of `y`, and it is the commutativity of the infinitesimal automorphisms — the
Eckmann–Hilton half of Stacks 06I6 — that makes the resulting conjugation trivial. Existence
does not need (RS*). -/
public theorem existsUnique_infAutBaseChange (hRS : SatisfiesRSStar B S hS p hp)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    ∃! σ : ↥(F.functor.obj M) → ↥(G.functor.obj N),
      ∀ θ, IsInfinitesimalAutomorphismBaseChange hp h f ψ (F.autEquiv M θ)
        (G.autEquiv N (σ θ)) :=
  ⟨infAutBaseChangeFun hp h f halg F G ψ,
    isInfinitesimalAutomorphismBaseChange_infAutBaseChangeFun hp h f halg F G ψ,
    fun _ hσ => eq_of_isInfinitesimalAutomorphismBaseChange_autEquiv hp h f F G hRS ψ hσ
      (isInfinitesimalAutomorphismBaseChange_infAutBaseChangeFun hp h f halg F G ψ)⟩

include hp halg in
/-- **Stacks 07YA on infinitesimal automorphisms.** Let `x` be an object of a category fibred
in groupoids over the big fppf site of `S` lying over `Spec A`, let `A ⟶ C` be a ring map and
let `y ⟶ x` be a morphism lying over `Spec C ⟶ Spec A`, so that `y = x|_{Spec C}`. For
`M ∈ Mod_A`, `N ∈ Mod_C` and an `A`-linear map `M ⟶ N` there is exactly one `A`-linear map
`Inf_x(M) ⟶ Inf_y(N)` carrying each infinitesimal automorphism of the trivial lift of `x` over
`Spec A[M]` to its conjugate along a cartesian arrow over `Spec C[N] ⟶ Spec A[M]`.

`x` and `y` are `Deformation.Artin.ChartedObject`s, so each of `Spec A ⟶ S`, `Spec C ⟶ S`
factors through a fixed affine open `Spec Λ ⊆ S`: that is an extra hypothesis, which the source
does not make. It is inherited from
`Deformation.Artin.IsInfinitesimalAutomorphismBaseChange`, the relation on infinitesimal
automorphisms that this theorem realizes, and it is what makes the result directly usable by
the Stacks 07YT statements that take a map realizing that relation as a hypothesis. The
geometric content is chart-free: the comparison of the trivial lifts and the conjugation along
it are `Deformation.Artin.underFiberConjugate`, stated for an arbitrary category fibred in
groupoids and an arbitrary commuting square of its base.

(RS*) is used only for the uniqueness half. The two functors enter as arbitrary members of
`Deformation.Artin.InfinitesimalAutomorphismFunctorData` rather than as the ones Stacks 07Y9
(1) produces from (RS*).

**NOT COVERED**: the two commuting squares of the source; see the note on
`Deformation.Artin.existsUnique_tangentBaseChange`. -/
@[stacks 07YA "the companion A-linear map Inf_x(M) -> Inf_y(N) along a ring map A -> C, and \
its uniqueness. The relation Deformation.Artin.IsInfinitesimalAutomorphismBaseChange, its \
single-valuedness and its bijectivity at a bijective map of coefficients are in the library, \
but without a map realizing it all of them would be conditional: the relation asks \
for a cartesian arrow between the two TRIVIAL lifts, and the pullback of the trivial lift of x \
along Spec C[N] -> Spec A[M] is only isomorphic to the trivial lift of y, not equal to it. \
What is added is that arrow -- Deformation.Artin.trivialLiftComparison, built from the \
presentation of each trivial lift as a pullback along the retraction Spec A[M] -> Spec A -- \
the conjugation by it, and the A-linearity of the resulting map, which is the remark's \
assertion. CARRIED, as an extra hypothesis the source does not make: x and y are \
Deformation.Artin.ChartedObjects, so Spec A -> S and Spec C -> S factor through a fixed affine \
open Spec L of S -- inherited from \
Deformation.Artin.IsInfinitesimalAutomorphismBaseChange, the relation this realizes; \
the geometric half is chart-free, as Deformation.Artin.underFiberConjugate. (RS*) is needed \
only for uniqueness, through the commutativity of the infinitesimal automorphisms; the two \
functors Inf_x, Inf_y are arbitrary members of \
Deformation.Artin.InfinitesimalAutomorphismFunctorData. NOT COVERED: the two commuting squares \
of the source, for which see the note on Deformation.Artin.existsUnique_tangentBaseChange"]
public theorem existsUnique_infAutBaseChangeHom (hRS : SatisfiesRSStar B S hS p hp)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    ∃! σ : ↥(F.functor.obj M) →ₛₗ[f] ↥(G.functor.obj N),
      ∀ θ, IsInfinitesimalAutomorphismBaseChange hp h f ψ (F.autEquiv M θ)
        (G.autEquiv N (σ θ)) := by
  refine ⟨infAutBaseChangeHom hp h f halg F G ψ,
    isInfinitesimalAutomorphismBaseChange_infAutBaseChangeFun hp h f halg F G ψ,
    fun σ hσ => LinearMap.ext (congrFun (eq_of_isInfinitesimalAutomorphismBaseChange_autEquiv
      hp h f F G hRS ψ hσ
      (isInfinitesimalAutomorphismBaseChange_infAutBaseChangeFun hp h f halg F G ψ)))⟩

end InfAutMap

end Deformation.Artin

end
