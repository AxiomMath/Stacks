module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# Étale morphisms out of an object of the site are representable by objects of the site

Let `S` be a scheme contained in a big fppf site `B`. A morphism `a : X ⟶ Y` of presheaves on
the big fppf site of `S` with values in `Type (u + 1)` whose source is the universe-lifted
Yoneda presheaf of an object of the site, and which is representable by algebraic spaces and
étale, is representable by *objects of the site*.

This is the form of **Stacks 0AHV** which the value universe of a formal algebraic space needs;
in the value universe of the site it is
`AlgebraicGeometry.Space.relativelyRepresentable_of_isLocallyQuasiFinite_of_schemeSource`.
It is the step that upgrades "representable by algebraic spaces" to "representable by schemes"
for a morphism out of an object of the site: a base change of such a morphism along a
scheme-valued point `T ⟶ Y` is an algebraic space, it is étale over `T`, and it sits inside the
product `U₀ ⨯ T` of the site by a monomorphism, the absolute diagonal of `Y` being a split
monomorphism and the base change one of its base changes. A monomorphism of algebraic spaces
locally of finite type is separated and locally quasi-finite (**Stacks 0463**), so **Stacks
03XX** represents the base change by an object of the site.

The implementation notes of `StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas` record
that a base change of a morphism representable by algebraic spaces and étale along a
scheme-valued point is an algebraic space étale over a scheme, which need not be a scheme, so
that the weaker hypothesis does not supply **Stacks 0BGR** with its atlas. What is proved here
is that it *is* a scheme once the source of the morphism is an object of the site: the extra
monomorphism into the product of the site is what the étale hypothesis alone does not give.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentableULift_of_isEtale_of_schemeSource`:
  **Stacks 0AHV**, the étale case, in the value universe of a formal algebraic space.

## Implementation notes

The argument is carried out after descending to the value universe of the site, where Stacks
0463 and 03XX live. The base change is an algebraic space, hence pointwise `u`-small
(`AlgebraicGeometry.Space.small_of_isAlgebraicSpaceULift`), so it is the universe lift of a
presheaf of `Type u`, and the three conditions transport along the lift: monomorphy because the
lifting functor is faithful, étaleness by
`AlgebraicGeometry.Space.isEtaleULift_whiskerRight_iff`, and the algebraic-space condition by
`AlgebraicGeometry.Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff`. The cancellation which
turns étaleness over `T` into local finiteness of type over `U₀ ⨯ T` is then
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp` taken in the value universe of the
site, so no cancellation statement is needed in the larger universe.

The source is taken as a presheaf together with an isomorphism from the universe-lifted Yoneda
presheaf of an object of the site rather than as that presheaf itself: the morphisms this is
applied to have a member of the atlas of a formal algebraic space for their source, which is
only isomorphic to a representable.

## References

* [Stacks Project, Tag 0AHV](https://stacks.math.columbia.edu/tag/0AHV)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of a fibre product with the product of its two factors, taken in the order
opposite to the one the fibre product is written in and with the first factor read through an
isomorphism, is a monomorphism: a pair of morphisms into the fibre product agreeing after both
projections agree. -/
private theorem mono_prodLift_pullback_comp_inv {C : Type*} [Category* C] {X Y Z W : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (e : W ≅ Y) [HasBinaryProduct W X] :
    Mono (prod.lift (pullback.snd f g ≫ e.inv) (pullback.fst f g)) :=
  ⟨fun _ _ h => pullback.hom_ext (by simpa using h =≫ prod.snd)
    ((cancel_mono e.inv).mp (by simpa using h =≫ prod.fst))⟩

/-- The base change of a morphism `a : X ⟶ Y` out of a presheaf isomorphic to the
universe-lifted Yoneda presheaf of `U₀` along a point `ξ` of `Y` at `T` embeds into the
universe-lifted Yoneda presheaf of `U₀ ⨯ T`, compatibly with the projection to `T`. -/
theorem exists_mono_pullback_uliftYoneda_prod {C : Type (u + 1)} [Category.{u} C]
    [HasBinaryProducts C] {X Y : Cᵒᵖ ⥤ Type (u + 1)} (a : X ⟶ Y) (U₀ : C)
    (e : (uliftYoneda.{u + 1, u, u + 1}).obj U₀ ≅ X) {T : C}
    (ξ : (uliftYoneda.{u + 1, u, u + 1}).obj T ⟶ Y) :
    ∃ m : pullback ξ a ⟶ (uliftYoneda.{u + 1, u, u + 1}).obj (U₀ ⨯ T),
      Mono m ∧ m ≫ (uliftYoneda.{u + 1, u, u + 1}).map prod.snd = pullback.fst ξ a := by
  refine ⟨prod.lift (pullback.snd ξ a ≫ e.inv) (pullback.fst ξ a) ≫
    (PreservesLimitPair.iso (uliftYoneda.{u + 1, u, u + 1}) U₀ T).inv, ?_, ?_⟩
  · exact mono_comp' (mono_prodLift_pullback_comp_inv ξ a e) inferInstance
  · rw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]

/-- **Stacks 0AHV, the étale case.** Let `Y` be a presheaf on the big fppf site of `S` with
values in `Type (u + 1)` and let `a : X ⟶ Y` be a morphism whose source is isomorphic to the
universe-lifted Yoneda presheaf of an object `U₀` of the site. If `a` is representable by
algebraic spaces and étale, then `a` is representable by objects of the site.

For a scheme-valued point `ξ` of `Y` the base change of `a` along `ξ` is an algebraic space,
étale over the point, and a monomorphism into the product `U₀ ⨯ T` of the site; a monomorphism
of algebraic spaces locally of finite type is separated and locally quasi-finite by
**Stacks 0463**, and **Stacks 03XX** then represents the base change by an object of the
site. -/
theorem relativelyRepresentableULift_of_isEtale_of_schemeSource
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : X ⟶ Y)
    (U₀ : BigFppfOver B S hS) (e : (uliftYoneda.{u + 1}).obj U₀ ≅ X)
    (ha : IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a)
    (het : HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ IsEtaleULift.{u + 1} B S hS g.hom) a ha) :
    (uliftYoneda.{u + 1}).relativelyRepresentable a := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  intro T ξ
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  -- the base change of `a` along the point `ξ`
  have hP : IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ a) := ha T ξ
  have hetfst : IsEtaleULift.{u + 1} B S hS (pullback.fst ξ a) := het T ξ
  -- it embeds into the product of the site
  obtain ⟨m, hmono, hmsnd⟩ := exists_mono_pullback_uliftYoneda_prod a U₀ e ξ
  -- descend to the value universe of the site
  obtain ⟨P', hP', ⟨eP⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hP
  let m' : P' ⟶ yoneda.obj (U₀ ⨯ T) := H.preimage (eP.hom ≫ m)
  have hm' : H.map m' = eP.hom ≫ m := H.map_preimage _
  have hmono' : Mono m' :=
    H.mono_of_mono_map (by rw [hm']; exact mono_comp' inferInstance hmono : Mono (H.map m'))
  -- étaleness of the projection, after the descent
  have hetP : IsEtaleULift.{u + 1} B S hS (eP.hom ≫ pullback.fst ξ a) := by
    intro V φ hφ
    simpa only [Category.assoc] using
      hetfst V (φ ≫ eP.hom) (MorphismProperty.RespectsIso.postcomp _ eP.hom φ hφ)
  have hyon : H.map (yoneda.map (prod.snd : U₀ ⨯ T ⟶ T))
      = (uliftYoneda.{u + 1}).map prod.snd := rfl
  have hcomp : H.map (m' ≫ yoneda.map prod.snd) = eP.hom ≫ pullback.fst ξ a := by
    rw [H.map_comp, hm', hyon]
    exact (Category.assoc _ _ _).trans (congrArg (fun k => eP.hom ≫ k) hmsnd)
  have hetm' : IsEtale B S hS (m' ≫ yoneda.map prod.snd) := by
    refine (isEtaleULift_whiskerRight_iff B S hS (m' ≫ yoneda.map prod.snd)).mp ?_
    have hwh : Functor.whiskerRight (m' ≫ yoneda.map prod.snd) uliftFunctor.{u + 1}
        = H.map (m' ≫ yoneda.map prod.snd) := rfl
    rwa [hwh, hcomp]
  -- Stacks 0463 and 03XX
  have hV : IsAlgebraicSpace B S hS (yoneda.obj (U₀ ⨯ T)) := isAlgebraicSpace_yoneda B S hS _
  have hT' : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hlft : IsLocallyOfFiniteType B S hS m' :=
    isLocallyOfFiniteType_of_comp B S hS hP' hV hT' m' (yoneda.map prod.snd)
      (isLocallyOfFiniteType_of_isEtale B S hS hT' hetm')
  have h0463 :=
    isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono B S hS m' ⟨hlft, hmono'⟩
  have hrep : P'.IsRepresentable :=
    isRepresentable_of_locallyQuasiFinite_separated B S hS P' (yoneda.obj (U₀ ⨯ T)) hP' hV m'
      inferInstance h0463.2 h0463.1
  -- read off the representing object of the site
  let iso : (uliftYoneda.{u + 1}).obj P'.reprX ≅ pullback ξ a := H.mapIso P'.reprW ≪≫ eP
  let σ : P'.reprX ⟶ T := (uliftYoneda.{u + 1}).preimage (iso.hom ≫ pullback.fst ξ a)
  have hσ : (uliftYoneda.{u + 1}).map σ = iso.hom ≫ pullback.fst ξ a := Functor.map_preimage _ _
  refine ⟨P'.reprX, σ, iso.hom ≫ pullback.snd ξ a, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ (iso ≪≫ pullbackSymmetry ξ a) ?_ ?_
  · rw [hσ, Category.assoc, Category.assoc, pullback.condition]
  · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
  · rw [hσ, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]

end AlgebraicGeometry.Space

end
