module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Properties of morphisms of presheaves representable by algebraic spaces

A morphism of presheaves on the big fppf site of a scheme `S` which is representable by
algebraic spaces *has* a property `P` of morphisms of algebraic spaces over `S` when every
base change of it along a scheme-valued point of its target has `P`.  This file shows that,
for a `P` which is stable under base change and local on the base for the fppf topology, the
test may be widened from scheme-valued points to algebraic-space-valued points, and deduces
that the class of morphisms representable by algebraic spaces with property `P` is stable
under base change and closed under composition and binary products.

## Main results

* `AlgebraicGeometry.Space.hasProperty_pullback_fst_of_isAlgebraicSpace`: the test defining
  `AlgebraicGeometry.Space.HasProperty` passes from scheme-valued points of the target to
  algebraic-space-valued ones.
* `AlgebraicGeometry.Space.hasProperty_of_isPullback`: **Stacks 046F**.
* `AlgebraicGeometry.Space.hasProperty_comp`: **Stacks 046G**.
* `AlgebraicGeometry.Space.hasProperty_prod_map`: **Stacks 046H**.

## Implementation notes

The widening of the test is where locality on the base is used, and it is the only place.
Given an algebraic-space-valued point `r : X ⟶ G`, a surjective étale scheme atlas
`h_V ⟶ X` of `X` is an fppf covering family of `X` in the sense of Stacks 03YH — surjective
because `AlgebraicGeometry.Space.surjective_iff_pointsMap_surjective` turns the
representable surjectivity of the atlas into surjectivity on points, and étale because
étaleness is stable under composition — so `P` may be checked after base change to `h_V`,
where the resulting square is the base change of `a` along `h_V ⟶ X ⟶ G` and the hypothesis
applies.

Stability under base change and the composition and product statements are then formal.  In
each case the representability witness of the conclusion is the corresponding statement from
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/Stability.lean`, and the
identification of the base change of the composite or the product with the composite or
product of the base changes is an isomorphism of algebraic spaces over the base, so
`CategoryTheory.MorphismProperty.RespectsIso` finishes.

Stacks 046F and 046G also assert the representability of the base change and of the
composite; those are Stacks 03Y0 and Stacks 03Y1, so the two tags are recorded on
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_isPullback` and
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_comp` rather than restated.

## References

* [Stacks Project, Tag 046F](https://stacks.math.columbia.edu/tag/046F)
* [Stacks Project, Tag 046G](https://stacks.math.columbia.edu/tag/046G)
* [Stacks Project, Tag 046H](https://stacks.math.columbia.edu/tag/046H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Binary products of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasBinaryProducts_presheaf :
    HasBinaryProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasBinaryProduct_presheaf
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : HasLimit (pair X Y) :=
  HasLimitsOfShape.has_limit _

/-- A property stable under isomorphisms transfers along an isomorphism of algebraic spaces
that commutes with the maps to a common target. -/
private theorem property_homMk_of_iso (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.RespectsIso] {A A' U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hA' : IsAlgebraicSpace B S hS A')
    (hU : IsAlgebraicSpace B S hS U) (e : A ≅ A') (f : A ⟶ U) (f' : A' ⟶ U)
    (h : e.hom ≫ f' = f) (hf : P (ObjectProperty.homMk f : (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨U, hU⟩ : AlgebraicSpaces B S hS))) :
    P (ObjectProperty.homMk f' : (⟨A', hA'⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨U, hU⟩ : AlgebraicSpaces B S hS)) := by
  subst h
  let eS : (⟨A, hA⟩ : AlgebraicSpaces B S hS) ≅ ⟨A', hA'⟩ := ObjectProperty.isoMk _ e
  exact (P.cancel_left_of_respectsIso eS.hom _).mp hf

/-! ### Base change -/

add_to_stacks 046F "representability" isRepresentableByAlgebraicSpaces_of_isPullback

/-- **Stacks 046F.** A property of morphisms of algebraic spaces over `S` which is stable
under base change is inherited, as a property of a morphism of presheaves representable by
algebraic spaces, by every cartesian base change of that morphism. -/
@[stacks 046F "property"]
lemma hasProperty_of_isPullback (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    {F G G' H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : H ⟶ F) (a' : H ⟶ G') (a : F ⟶ G) (g : G' ⟶ G) (h : IsPullback p a' a g)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hP : HasProperty B S hS P a ha) :
    HasProperty B S hS P a'
      (isRepresentableByAlgebraicSpaces_of_isPullback B S hS p a' a g h ha) := by
  intro U ξ
  have hpaste : IsPullback (pullback.fst ξ a') (pullback.snd ξ a' ≫ p) (ξ ≫ g) a := by
    simpa using (IsPullback.paste_horiz (IsPullback.of_hasPullback ξ a').flip h).flip
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact property_homMk_of_iso B S hS P _ _ _ hpaste.isoPullback.symm _ _
    (by rw [Iso.symm_hom, Iso.inv_comp_eq, hpaste.isoPullback_hom_fst]) (hP U (ξ ≫ g))

/-! ### Widening the test to algebraic-space-valued points -/

/-- A surjective étale scheme atlas of an algebraic space over `S` is a one-member fppf
covering family of that algebraic space in the sense of Stacks 03YH. -/
private theorem atlas_isFppfCovering {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (V : BigFppfOver B S hS) (f : yoneda.obj V ⟶ X)
    (hfs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hfe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f) :
    Topology.IsCovering .fppf B S hS
      (I := PUnit.{v + 1}) (Yi := fun _ => yoneda.obj V) (g := fun _ => f) := by
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) f) :=
    (surjective_iff_pointsMap_surjective B S hS hV hX f
      ((Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).mp
        hX.diagonal_representable f)).mp hfs
  have het : IsEtaleCovering B S hS (fun _ : PUnit.{v + 1} => yoneda.obj V)
      (fun _ : PUnit.{v + 1} => f) := by
    refine ⟨hX, (fun _ => hV), ?_, ?_⟩
    · intro i U φ hφ
      let Q := MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
      let _ : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
        MorphismProperty.IsMultiplicative.toIsStableUnderComposition
      let _ : Q.IsStableUnderComposition :=
        MorphismProperty.IsStableUnderComposition.inverseImage _
      let _ : Q.presheaf.IsStableUnderComposition :=
        MorphismProperty.relative_isStableUnderComposition Q
      exact MorphismProperty.comp_mem _ _ _ hφ hfe
    · exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨PUnit.unit, hsurj x⟩
  exact ⟨hX, (fun _ => hV), isFppfCovering_of_isEtaleCovering B S hS het⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- The test defining `AlgebraicGeometry.Space.HasProperty` may be applied at an
algebraic-space-valued point of the target, not merely a scheme-valued one: if `P` is local
on the base for the fppf topology and `a` has `P`, then for every algebraic space `X` over
`S` and every `r : X ⟶ G` the first projection of the fibre product of `r` and `a` has `P`
as a morphism of algebraic spaces over `S`.

This is where locality on the base enters: `P` is checked after base change along a
surjective étale scheme atlas of `X`, which is an fppf covering family of `X`, and there the
square is the base change of `a` along a scheme-valued point of `G`. -/
theorem hasProperty_pullback_fst_of_isAlgebraicSpace
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.fppf.precoverage.{u, v} B S hS)]
    {X G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (r : X ⟶ G) (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hP : HasProperty B S hS P a ha) :
    P (ObjectProperty.homMk (pullback.fst r a) :
      (⟨pullback r a,
          isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS a r ha hX⟩ :
        AlgebraicSpaces B S hS) ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS)) := by
  let XObj : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let A := pullback r a
  let AObj : AlgebraicSpaces B S hS :=
    ⟨A, isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS a r ha hX⟩
  let q : AObj ⟶ XObj := ObjectProperty.homMk (pullback.fst r a)
  obtain ⟨V, f, hfs, hfe⟩ := hX.exists_atlas
  let hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  let VObj : AlgebraicSpaces B S hS := ⟨yoneda.obj V, hV⟩
  let vAtlas : VObj ⟶ XObj := ObjectProperty.homMk f
  let R : Presieve XObj :=
    Presieve.ofArrows (ι := PUnit.{v + 1}) (fun _ => VObj) (fun _ => vAtlas)
  let K := Topology.fppf.precoverage.{u, v} B S hS
  have hR : R ∈ K XObj := ⟨PUnit.{v + 1}, fun _ => VObj, fun _ => vAtlas, rfl,
    atlas_isFppfCovering B S hS hX V f hfs hfe⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := P) (K := K) (f := q) (R := R) hR
  intro Z w _ hw
  obtain ⟨⟨⟩⟩ := hw
  let T := pullback (f ≫ r) a
  let TObj : AlgebraicSpaces B S hS := ⟨T, ha V (f ≫ r)⟩
  let z : TObj ⟶ VObj := ObjectProperty.homMk (pullback.fst (f ≫ r) a)
  let sRaw : T ⟶ A := pullback.lift (pullback.fst (f ≫ r) a ≫ f) (pullback.snd (f ≫ r) a)
    (by rw [Category.assoc, pullback.condition])
  let s : TObj ⟶ AObj := ObjectProperty.homMk sRaw
  have hsquare : IsPullback s z q vAtlas := by
    apply IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F => IsAlgebraicSpace B S hS F))
    have hbig : IsPullback (pullback.fst (f ≫ r) a) (sRaw ≫ pullback.snd r a) (f ≫ r) a := by
      simpa only [sRaw, pullback.lift_snd] using (IsPullback.of_hasPullback (f ≫ r) a)
    exact (hbig.of_bot (by dsimp [sRaw]; rw [pullback.lift_fst])
      (IsPullback.of_hasPullback r a)).flip
  have := hsquare.hasPullback
  exact (P.cancel_left_of_respectsIso hsquare.isoPullback.hom (pullback.snd q vAtlas)).mp
    (by rw [hsquare.isoPullback_hom_snd]; exact hP V (f ≫ r))

/-! ### Composition and products -/

add_to_stacks 046G "representability" isRepresentableByAlgebraicSpaces_comp

set_option synthInstance.maxHeartbeats 200000 in
/-- **Stacks 046G.** A composite of morphisms of presheaves on the big fppf site of `S`
representable by algebraic spaces has a property `P` of morphisms of algebraic spaces over
`S` as soon as both factors do, provided `P` is stable under base change, local on the base
for the fppf topology, and stable under composition. -/
@[stacks 046G "property of the composite"]
theorem hasProperty_comp (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (Topology.fppf.precoverage B S hS)]
    [P.IsStableUnderComposition]
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hb : IsRepresentableByAlgebraicSpaces B S hS b)
    (hPa : HasProperty B S hS P a ha) (hPb : HasProperty B S hS P b hb) :
    HasProperty B S hS P (a ≫ b)
      (isRepresentableByAlgebraicSpaces_comp B S hS a b ha hb) := by
  intro U ξ
  let X := pullback ξ b
  let hX : IsAlgebraicSpace B S hS X := hb U ξ
  let XObj : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let UObj : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let t : XObj ⟶ UObj := ObjectProperty.homMk (pullback.fst ξ b)
  let r : X ⟶ G := pullback.snd ξ b
  let A := pullback r a
  let AObj : AlgebraicSpaces B S hS :=
    ⟨A, isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS a r ha hX⟩
  let q : AObj ⟶ XObj := ObjectProperty.homMk (pullback.fst r a)
  have hq : P q := hasProperty_pullback_fst_of_isAlgebraicSpace B S hS P hX r a ha hPa
  have hcomp : P (q ≫ t) := P.comp_mem q t hq (hPb U ξ)
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact property_homMk_of_iso B S hS P _ _ _ (pullbackLeftPullbackSndIso ξ b a) _ _
    (by simp; rfl) hcomp

/-- **Stacks 046H.** The product of two morphisms of presheaves on the big fppf site of `S`
representable by algebraic spaces has a property `P` of morphisms of algebraic spaces over
`S` as soon as both factors do, provided `P` is stable under base change, local on the base
for the fppf topology, and stable under composition.

The product is the composite of two base changes of the two factors, so this follows from
Stacks 046F and Stacks 046G. -/
@[stacks 046H]
lemma hasProperty_prod_map (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (Topology.fppf.precoverage B S hS)]
    [P.IsStableUnderComposition]
    {F₁ F₂ G₁ G₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (h₁ : IsRepresentableByAlgebraicSpaces B S hS a₁)
    (h₂ : IsRepresentableByAlgebraicSpaces B S hS a₂)
    (ha₁ : HasProperty B S hS P a₁ h₁) (ha₂ : HasProperty B S hS P a₂ h₂) :
    HasProperty B S hS P (prod.map a₁ a₂)
      (isRepresentableByAlgebraicSpaces_prod_map B S hS a₁ a₂ h₁ h₂) := by
  simpa [prod.map_map] using
    (hasProperty_comp B S hS P (prod.map a₁ (𝟙 F₂)) (prod.map (𝟙 G₁) a₂)
      (isRepresentableByAlgebraicSpaces_of_isPullback B S hS
        prod.fst (prod.map a₁ (𝟙 F₂)) a₁ prod.fst
        (IsPullback.of_prod_fst_with_id a₁ F₂) h₁)
      (isRepresentableByAlgebraicSpaces_of_isPullback B S hS
        prod.snd (prod.map (𝟙 G₁) a₂) a₂ prod.snd
        (IsPullback.of_prod_snd_with_id a₂ G₁) h₂)
      (hasProperty_of_isPullback B S hS P
        prod.fst (prod.map a₁ (𝟙 F₂)) a₁ prod.fst
        (IsPullback.of_prod_fst_with_id a₁ F₂) h₁ ha₁)
      (hasProperty_of_isPullback B S hS P
        prod.snd (prod.map (𝟙 G₁) a₂) a₂ prod.snd
        (IsPullback.of_prod_snd_with_id a₂ G₁) h₂ ha₂))

end AlgebraicGeometry.Space

end
