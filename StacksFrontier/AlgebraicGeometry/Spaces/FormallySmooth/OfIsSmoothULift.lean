module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmooth
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# A smooth morphism in a larger value universe is formally smooth

Let `a : F ⟶ G` be a morphism of presheaves on the big fppf site of `S` with values in
`Type (max w u)`, representable by algebraic spaces, whose base change along every scheme-valued
point of `G` is smooth (Stacks 03XZ for the property of Stacks 03ZC; this is how smoothness of a
morphism of formal algebraic spaces such as `V_{/Z} ⟶ W` is read). Then `a` is formally smooth
(Stacks 049S): it lifts across square-zero closed immersions of affine objects of the site.

The lifting problem along `T ⊆ T'` over a section `y` of `G` over `T'` is a lifting problem for the
base change `P = T' ×_G F ⟶ T'`, which is smooth. The algebraic space `P` is the universe lift of
an algebraic space of `Type u`
(`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`), over which the
morphism to `T'` is smooth, hence formally smooth by Stacks 04AM
(`AlgebraicGeometry.Space.formallySmooth_of_isSmooth'`).

## Main results

* `AlgebraicGeometry.Space.formallySmooth_of_hasPropertyULift_isSmoothULift`: the statement
  above.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A smooth morphism representable by algebraic spaces is formally smooth**, for presheaves with
values in `Type (max w u)`. -/
theorem formallySmooth_of_hasPropertyULift_isSmoothULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a)
    (hsm : HasPropertyULift.{w} B S hS (smoothPropertyULift.{w} B S hS) a ha) :
    FormallySmooth a := by
  intro T T' hT hT' i hi x y hxy
  let ξ : (uliftYoneda.{w}).obj T' ⟶ G := uliftYonedaEquiv.symm y
  have hsmP : IsSmoothULift.{w} B S hS (pullback.fst ξ a) := hsm T' ξ
  obtain ⟨P', hP', ⟨e⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS (ha T' ξ)
  obtain ⟨q', hq'⟩ := exists_whiskerRight_eq B S hS (F := P') (G := yoneda.obj T')
    (e.hom ≫ pullback.fst ξ a)
  have hq : IsSmoothULift.{w} B S hS (e.hom ≫ pullback.fst ξ a) :=
    holdsOnEveryEtaleChartULift_precomp B S hS _ e.hom _ hsmP
  have hsm' : IsSmooth B S hS q' :=
    (holdsOnEveryEtaleChartULift_whiskerRight_iff B S hS _ q').1 (hq' ▸ hq)
  have hFS := formallySmooth_of_isSmooth' hP' (isAlgebraicSpace_yoneda B S hS T') hsm'
  -- the section of the base change over `T`
  have hpb : ∀ U : BigFppfOver B S hS, IsPullback ((pullback.fst ξ a).app (op U))
      ((pullback.snd ξ a).app (op U)) (ξ.app (op U)) (a.app (op U)) := fun U =>
    (IsPullback.of_hasPullback ξ a).map ((evaluation _ (Type (max w u))).obj (op U))
  have hξ : ∀ (U : BigFppfOver B S hS) (f : U ⟶ T'),
      ξ.app (op U) (ULift.up f) = G.map f.op y := fun U f => rfl
  obtain ⟨pT, hpT₁, hpT₂⟩ := Types.exists_of_isPullback (hpb T) (ULift.up i) x
    (by rw [hξ]; exact hxy.symm)
  let x' : P'.obj (op T) := (e.inv.app (op T) pT).down
  have hex : e.hom.app (op T) (ULift.up x') = pT :=
    congrArg (fun m => m.app (op T) pT) e.inv_hom_id
  have hq'app : ∀ (U : BigFppfOver B S hS) (z : P'.obj (op U)),
      ULift.up (q'.app (op U) z) = (pullback.fst ξ a).app (op U) (e.hom.app (op U) (ULift.up z)) :=
    fun U z => congrArg (fun m => m.app (op U) (ULift.up z)) hq'
  have hqx : q'.app (op T) x' = (yoneda.obj T').map i.op (𝟙 T') := by
    have h := hq'app T x'
    rw [hex, hpT₁] at h
    change q'.app (op T) x' = i ≫ 𝟙 T'
    rw [Category.comp_id]
    exact congrArg ULift.down h
  obtain ⟨z', hz₁, hz₂⟩ := hFS T T' hT hT' i hi x' (𝟙 T') hqx
  refine ⟨(pullback.snd ξ a).app (op T') (e.hom.app (op T') (ULift.up z')), ?_, ?_⟩
  · have hn₁ := NatTrans.naturality_apply (pullback.snd ξ a) i.op
      (e.hom.app (op T') (ULift.up z'))
    have hn₂ := NatTrans.naturality_apply e.hom i.op
      (ULift.up z' : (P' ⋙ uliftFunctor.{w}).obj (op T'))
    have h3 : (P' ⋙ uliftFunctor.{w}).map i.op (ULift.up z') = ULift.up x' := by
      change ULift.up (P'.map i.op z') = _
      rw [hz₁]
    rw [← hn₁, ← hn₂, h3, hex, hpT₂]
  · have hw := ConcreteCategory.congr_hom (hpb T').w (e.hom.app (op T') (ULift.up z'))
    simp only [ConcreteCategory.comp_apply] at hw
    rw [← hw, ← hq'app, hz₂, hξ]
    simp

end AlgebraicGeometry.Space

end
