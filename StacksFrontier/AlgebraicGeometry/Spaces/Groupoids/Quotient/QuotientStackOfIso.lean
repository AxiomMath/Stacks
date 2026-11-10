module

public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimit
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaQuotientStackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.CategoryTheory.Sites.Stackification.TransportAlongEquivalenceOver
public import StacksFrontier.CategoryTheory.Sites.Stackification.Uniqueness
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased

/-!
# Isomorphic groupoids have equivalent quotient stacks

Let `G` and `H` be groupoids in algebraic spaces over an algebraic space `B` over a scheme `S` of a
big fppf site, and let `e : G ≅ H` be an isomorphism of groupoids over `B`. Then the 1-morphism
`[e] : [G] ⟶ [H]` of Stacks 046Q is an equivalence over the site, and it commutes with the two
structure arrows to `B` of Stacks 044R. So `[G]` and `[H]` are equivalent as stacks over `B`.

## Main results

* `AlgebraicGeometry.Stack.quotientPointwiseMap_comp_eq_id`: the maps of pointwise groupoid
  fibrations induced by two mutually inverse morphisms of groupoids compose to the identity.
* `AlgebraicGeometry.Stack.quotientStackMap_comp_quotientStackToBase`: the 1-morphism of
  Stacks 046Q commutes on the nose with the structure arrows of Stacks 044R.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_quotientStackToBase_of_iso`: an isomorphism of
  groupoids over `B` induces an equivalence of their quotient stacks over `B`.

## Implementation notes

The equivalence is the recognition criterion of Stacks 02ZN and 02ZP: the restriction of `[e]`
along the stackification map of `[G]` is, up to a vertical 2-isomorphism, the composite of an
isomorphism of the two pointwise groupoid fibrations with the stackification map of `[H]`, and the
two clauses of Stacks 02ZN transport along an equivalence over the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The arrow of the image of a morphism of the pointwise presentation under the map of
Stacks 046Q is the image of its arrow under the map on arrow spaces. -/
lemma presentationArrow_quotientPointwiseMap_map {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) {x y : (pointwisePresentation G).obj} (f : x ⟶ y) :
    presentationArrow H ((quotientPointwiseMap φ).toFunctor.map f) =
      φ.toGroupoidHom.mapArrows.app (op x.base) (presentationArrow G f) := by
  unfold presentationArrow
  rw [quotientPointwiseMap_map_fiber]
  refine Eq.trans (evaluationArrowEquiv_transport _ _ _ _ _) ?_
  exact φ.toGroupoidHom.evaluation_map_arrow _ f.fiber

/-- **Mutually inverse morphisms of groupoids induce mutually inverse maps of pointwise groupoid
fibrations**, on the nose. -/
theorem quotientPointwiseMap_comp_eq_id {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) (ψ : GroupoidInAlgebraicSpaces.Hom H G)
    (ho : φ.toGroupoidHom.mapObjects ≫ ψ.toGroupoidHom.mapObjects = 𝟙 G.objects.obj)
    (ha : φ.toGroupoidHom.mapArrows ≫ ψ.toGroupoidHom.mapArrows = 𝟙 G.arrows.obj) :
    (quotientPointwiseMap φ).toFunctor ⋙ (quotientPointwiseMap ψ).toFunctor =
      𝟭 (pointwisePresentation G).obj := by
  have hobj : ∀ x, ((quotientPointwiseMap φ).toFunctor ⋙
      (quotientPointwiseMap ψ).toFunctor).obj x = (𝟭 (pointwisePresentation G).obj).obj x := by
    intro x
    change (quotientPointwiseMap ψ).toFunctor.obj ((quotientPointwiseMap φ).toFunctor.obj x) = x
    refine (congrArg (quotientPointwiseMap ψ).toFunctor.obj (quotientPointwiseMap_obj φ x)).trans ?_
    refine (quotientPointwiseMap_obj ψ _).trans ?_
    have h := congrArg (fun m => m.app (op x.base) x.fiber) ho
    simp only [NatTrans.comp_app, NatTrans.id_app] at h
    exact congrArg (fun z => (⟨x.base, z⟩ : (pointwisePresentation G).obj)) h
  refine CategoryTheory.Functor.ext hobj ?_
  intro x y f
  refine presentationHom_ext G _ _ ?_ ?_
  · change (pointwisePresentation G).p.map
      ((quotientPointwiseMap ψ).toFunctor.map ((quotientPointwiseMap φ).toFunctor.map f)) =
      (pointwisePresentation G).p.map (eqToHom (hobj x) ≫ f ≫ eqToHom (hobj y).symm)
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    have h1 := Functor.congr_hom (quotientPointwiseMap ψ).w
      ((quotientPointwiseMap φ).toFunctor.map f)
    have h2 := Functor.congr_hom (quotientPointwiseMap φ).w f
    simp only [Functor.comp_map] at h1 h2
    rw [h1, h2]
    simp
  · refine Eq.trans ?_ (presentationArrow_transport G (hobj x) (hobj y).symm f).symm
    change presentationArrow G ((quotientPointwiseMap ψ).toFunctor.map
      ((quotientPointwiseMap φ).toFunctor.map f)) = _
    rw [presentationArrow_quotientPointwiseMap_map, presentationArrow_quotientPointwiseMap_map]
    have h := congrArg (fun m => m.app (op x.base) (presentationArrow G f)) ha
    simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app] at h
    refine h.trans ?_
    change presentationArrow G f = G.toGroupoidInFunctors.arrows.map (eqToHom rfl)
      (presentationArrow G f)
    simp

/-- The map of Stacks 046Q on the pointwise groupoid fibrations, read between their
universe-lifted forms, which are the presentations the two quotient stacks stackify. -/
noncomputable def quotientPrestackMap {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    (quotientPrestack G).obj ⥤ (quotientPrestack H).obj :=
  (quotientPrestackEquivalence G).inverse ⋙ (quotientPointwiseMap φ).toFunctor ⋙
    (quotientPrestackEquivalence H).functor

/-- The map of lifted presentations is strictly over the site. -/
theorem quotientPrestackMap_comp {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    quotientPrestackMap φ ⋙ (quotientPrestack H).p = (quotientPrestack G).p := by
  change (quotientPrestackEquivalence G).inverse ⋙ (quotientPointwiseMap φ).toFunctor ⋙
    (presheafOfGroupoids (evaluationGroupoidFunctor H.toGroupoidInFunctors)).p = _
  rw [(quotientPointwiseMap φ).w]
  rfl

/-- Mutually inverse morphisms of groupoids induce mutually inverse maps of the lifted
presentations. -/
theorem quotientPrestackMap_comp_eq_id {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) (ψ : GroupoidInAlgebraicSpaces.Hom H G)
    (ho : φ.toGroupoidHom.mapObjects ≫ ψ.toGroupoidHom.mapObjects = 𝟙 G.objects.obj)
    (ha : φ.toGroupoidHom.mapArrows ≫ ψ.toGroupoidHom.mapArrows = 𝟙 G.arrows.obj) :
    quotientPrestackMap φ ⋙ quotientPrestackMap ψ = 𝟭 (quotientPrestack G).obj := by
  change (quotientPrestackEquivalence G).inverse ⋙
      ((quotientPointwiseMap φ).toFunctor ⋙ (quotientPointwiseMap ψ).toFunctor) ⋙
        (quotientPrestackEquivalence G).functor = _
  rw [quotientPointwiseMap_comp_eq_id φ ψ ho ha]
  rfl

/-- **An isomorphism of groupoids induces an equivalence of the lifted presentations over the
site**, with the inverse induced by the inverse isomorphism and identities as unit and counit. -/
noncomputable def quotientPrestackMapIsEquivalenceOver {G H : GroupoidInAlgebraicSpaces C S hS B}
    (e : GroupoidInAlgebraicSpaces.Iso G H) :
    Functor.IsEquivalenceOver (quotientPrestack G).p (quotientPrestack H).p
      (quotientPrestackMap e.hom) where
  inv := quotientPrestackMap e.inv
  inv_over := quotientPrestackMap_comp e.inv
  unitIso := eqToIso (quotientPrestackMap_comp_eq_id e.hom e.inv e.mapObjects_hom_inv
    e.mapArrows_hom_inv)
  counitIso := eqToIso (quotientPrestackMap_comp_eq_id e.inv e.hom e.mapObjects_inv_hom
    e.mapArrows_inv_hom)
  unit_vertical X := by
    simp only [eqToIso.hom, eqToHom_app]
    exact IsHomLift.eqToHom_domain_lift_id _ rfl
  counit_vertical X := by
    simp only [eqToIso.hom, eqToHom_app]
    exact IsHomLift.eqToHom_domain_lift_id _ rfl

/-- The map of lifted presentations is a 1-morphism of fibred categories over the site. -/
theorem isFibredOneMorphism_quotientPrestackMap {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    (quotientPrestack G).p.IsFibredOneMorphism (quotientPrestack H).p (quotientPrestackMap φ) :=
  (isFiberedInGroupoids_quotientPrestack H).isFibredOneMorphism (quotientPrestackMap_comp φ)

/-- **The 1-morphism of Stacks 046Q induced by an isomorphism of groupoids is an equivalence over
the site.** Its restriction along the stackification map of `[G]` is vertically 2-isomorphic to
the composite of an equivalence of the lifted presentations with the stackification map of `[H]`,
so it satisfies the recognition criterion of Stacks 02ZN and 02ZP. -/
theorem nonempty_isEquivalenceOver_quotientMapExtension {G H : GroupoidInAlgebraicSpaces C S hS B}
    (e : GroupoidInAlgebraicSpaces.Iso G H) :
    Nonempty (Functor.IsEquivalenceOver (quotientStack G).p (quotientStack H).p
      (quotientMapExtension e.hom)) := by
  let J := BigFppfOver.topology C S hS
  have hE := isFibredOneMorphism_quotientPrestackMap e.hom
  have hK := isFibredOneMorphism_toQuotientStack H
  have hclauses :=
    Functor.Stackification.isLocallyBijective_morPresheafMap_comp_of_isEquivalenceOver
      hE (quotientPrestackMapIsEquivalenceOver e) hK J (isLocallyBijective_toQuotientStack H)
      (essImage_toQuotientStack H)
  have hH : (quotientStack G).p.IsFibredOneMorphism (quotientStack H).p
      (quotientMapExtension e.hom) :=
    (isFiberedInGroupoids_quotientStack H).isFibredOneMorphism (quotientMapExtension_comp e.hom)
  exact Functor.Stackification.nonempty_isEquivalenceOver_of_natIso
    (isFibredOneMorphism_toQuotientStack G) hH J (hE.comp hK) (quotientMapExtensionUnit e.hom)
    (quotientMapExtensionUnit_hom_isHomLift e.hom) (isLocallyBijective_toQuotientStack G)
    (essImage_toQuotientStack G) hclauses.1 hclauses.2 (isStack_quotientStack G)
    (isStack_quotientStack H)

/-- **The 1-morphism of Stacks 046Q commutes with the structure arrows of Stacks 044R**, on the
nose: both sides are 1-morphisms into the category fibred in sets of the base, which agree after
restriction along the projection `𝒮_U ⟶ [U/R]` because the map on object spaces is over the
base. -/
theorem quotientStackMap_comp_quotientStackToBase {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    BasedFunctor.comp (quotientStackMap φ) (quotientStackToBase H) = quotientStackToBase G := by
  refine restriction_injective G _ _ ?_
  refine (quotientStackProjection_comp_quotientStackMap φ (quotientStackToBase H)).trans ?_
  refine (congrArg (fun k => BasedFunctor.comp
    (associatedMap C S hS φ.toGroupoidHom.mapObjects).1.hom k)
      (quotientStackProjection_comp_toBase H)).trans ?_
  refine (congrArg (fun k => k.hom) (associatedMap_comp C S hS φ.toGroupoidHom.mapObjects
    H.objectsToBase.hom)).symm.trans ?_
  rw [φ.mapObjects_over]
  exact (quotientStackProjection_comp_toBase G).symm

/-- **Isomorphic groupoids have equivalent quotient stacks over the base.** An isomorphism of
groupoids in algebraic spaces over `B` induces an equivalence `[G] ≅ [H]` over the site which
identifies the two structure arrows to `B` of Stacks 044R. -/
theorem nonempty_equivalenceOver_quotientStackToBase_of_iso
    {G H : GroupoidInAlgebraicSpaces C S hS B} (e : GroupoidInAlgebraicSpaces.Iso G H) :
    Nonempty (BasedCategory.EquivalenceOver (quotientStackToBase G) (quotientStackToBase H)) := by
  obtain ⟨E⟩ := nonempty_isEquivalenceOver_quotientMapExtension e
  let eqv : BasedCategory.Equivalence (quotientStack G) (quotientStack H) :=
    (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (quotientMapExtension_comp e.hom) E).toBasedEquivalence
  exact ⟨{ equiv := eqv
           compIso := eqToIso (quotientStackMap_comp_quotientStackToBase e.hom) }⟩

end AlgebraicGeometry.Stack

end
