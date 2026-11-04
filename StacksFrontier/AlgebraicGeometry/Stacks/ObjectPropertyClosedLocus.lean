module

public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenLocus

/-!
# A closed locus makes a 1-morphism of categories fibred in groupoids a closed immersion

This is the closed counterpart of
`StacksFrontier/AlgebraicGeometry/Stacks/ObjectPropertyOpenLocus.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/ObjectPropertyOpenImmersion.lean`.  Let `G : 𝒞 ⟶ 𝒟` be a
1-morphism of categories over the big fppf site of a scheme `S` whose underlying functor is
fully faithful.  Suppose that every scheme-valued point `y` of `𝒟` over an object `U` of the
big fppf site cuts out a *closed subscheme* `V ⊆ U` through which an object `T` of the big fppf
site of `U` maps exactly when `y(T)` is in the image of `G`.  Then `G` is representable by
algebraic spaces and a closed immersion in the sense of Stacks 04XB, the representing algebraic
space of each base change being that closed subscheme.

## Main definitions

* `AlgebraicGeometry.Stack.HasClosedLocus`: the one geometric input — the closed subscheme cut
  out on the base of a scheme-valued point by the image of `G`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_hasClosedLocus`: Stacks 02ZW for
  a fully faithful 1-morphism with a closed locus.
* `AlgebraicGeometry.Stack.isClosedImmersion_of_hasClosedLocus`: the closed-immersion condition
  of Stacks 04XB for it, written out.
* `Stack.isClosedImmersion_and_isRepresentableByAlgebraicSpaces_of_hasClosedLocus`:
  both conjuncts at once for a 1-morphism of categories fibred in groupoids, the second being the
  named predicate `AlgebraicGeometry.Stack.IsClosedImmersion`; together they are Stacks 04YL (2).

## Implementation notes

The proofs are those of the open case: the first projection of the 2-fibre product is fully
faithful because `G` is, the category of elements of the sheaf of points of `V` has fully
faithful projection because a closed immersion is a monomorphism, and the two have the same image
on objects.  The only inputs specific to the closed case are that a closed immersion of schemes
is a monomorphism and is stable under base change.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w v₁ u₁ v₂ u₂

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed subspace of a scheme is a closed subscheme.**  For a closed subspace `Z` of the
algebraic space of an object `W₀` of the big fppf site of `S`, there is a morphism `s : V ⟶ W₀`
of the site whose underlying morphism of schemes is a closed immersion and through which a
morphism `w : W ⟶ W₀` factors exactly when its point `yoneda w` of `W₀` factors through `Z`.
`V` is the base change of the representable inclusion of `Z` along the identity of `W₀`. -/
theorem exists_isClosedImmersion_factors_iff_of_isClosedSubspace (W₀ : BigFppfOver B S hS)
    (Z : Subfunctor (yoneda.obj W₀)) (hZ : IsClosedSubspace B S hS Z) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ W₀),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s) ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (w : W ⟶ W₀),
        (∃ k : yoneda.obj W ⟶ Z.toFunctor, k ≫ Z.ι = yoneda.map w) ↔ ∃ l : W ⟶ V, l ≫ s = w := by
  obtain ⟨hrep, hprop⟩ := hZ.2
  let g : yoneda.obj W₀ ⟶ yoneda.obj W₀ := 𝟙 _
  have hsq := hrep.isPullback g
  refine ⟨hrep.pullback g, hrep.snd g, hprop g (hrep.fst g) (hrep.snd g) hsq, fun W w => ?_⟩
  constructor
  · rintro ⟨k, hk⟩
    let lift := hsq.lift k (yoneda.map w) (by rw [hk, Category.comp_id])
    refine ⟨yoneda.preimage lift, yoneda.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage]
    exact hsq.lift_snd _ _ _
  · rintro ⟨l, rfl⟩
    exact ⟨yoneda.map l ≫ hrep.fst g, by rw [Category.assoc, hsq.w, Category.comp_id,
      Functor.map_comp]⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed subschemes of the base -/

/-- There is at most one morphism to an object of the big fppf site of `U` whose structure
morphism is a closed immersion, that morphism being a monomorphism. -/
theorem subsingleton_hom_of_isClosedImmersion (U : BigFppfOver B S hS)
    (V : BigFppfOver B U.left.1 U.left.2)
    (hV : _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom)
    (T : BigFppfOver B U.left.1 U.left.2) : Subsingleton (T ⟶ V) := by
  have : Mono V.hom := B.inclusion.mono_of_mono_map (by
    show Mono V.hom.hom
    infer_instance)
  exact ⟨fun a b ↦ Over.OverMorphism.ext <|
    (cancel_mono V.hom).mp <| (Over.w a).trans (Over.w b).symm⟩

/-- **An algebraic space over `U` isomorphic to a closed subscheme of `U` has closed immersion
structural morphism over `S`.**  This is the structural morphism of Stacks 04SG, the one the
closed-immersion condition of Stacks 04XB tests. -/
theorem isClosedImmersion_algebraicSpaceMap_of_iso_yoneda (U : BigFppfOver B S hS)
    (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hP : IsAlgebraicSpace B U.left.1 U.left.2 P)
    (V : BigFppfOver B U.left.1 U.left.2) (e : P ≅ yoneda.obj V)
    (hV : _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom) :
    Space.IsClosedImmersion B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom := by
  have : (Space.closedImmersionProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (prop_algebraicSpaceMap_iff B S hS (Space.closedImmersionProperty B S hS) U P hP).mpr ?_
  let k : (Over.map U.hom).obj V ⟶ Over.mk U.hom := Over.homMk V.hom rfl
  let j : (OverShriek.relocalizePresheafFunctor U.hom).obj P ≅
      yoneda.obj ((Over.map U.hom).obj V) :=
    (OverShriek.relocalizePresheafFunctor U.hom).mapIso e ≪≫
      (OverShriek.relocalizeYonedaIso U.hom).app V
  have hj : j.hom ≫ yoneda.map k = OverShriek.relocalizeToYoneda U.hom P := by
    dsimp only [j, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, relocalizeToYoneda_yoneda, relocalizeToYoneda_comp_map]
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have := MorphismProperty.isStableUnderBaseChange_inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (BigFppfOver.toScheme B S hS)
  have hk : Space.IsClosedImmersion B S hS (yoneda.map k) :=
    MorphismProperty.relative_map (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (BigFppfOver.toScheme B S hS)) hV
  show Space.IsClosedImmersion B S hS (OverShriek.relocalizeToYoneda U.hom P)
  rw [← hj]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS))) j.hom (yoneda.map k)).mpr hk

/-! ### The closed-locus mechanism -/

section ClosedLocus

/-- **The one geometric input of the closed-locus mechanism.**  A 1-morphism `G : 𝒞 ⟶ 𝒟` of
categories over the big fppf site of `S` *has a closed locus* when, for every scheme-valued point
`y` of `𝒟` over an object `U` of the big fppf site, there is a closed subscheme `V` of `U`
through which an object `T` of the big fppf site of `U` maps exactly when `T` is in the image of
the first projection of the 2-fibre product `(Sch/U)_{fppf} ×_{y, 𝒟} 𝒞`. -/
def HasClosedLocus {𝒞 : BasedCategory.{v₁, u₁} (BigFppfOver B S hS)}
    {𝒟 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)} (G : 𝒞 ⥤ᵇ 𝒟) : Prop :=
  ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj),
    y ⋙ 𝒟.p = Over.map U.hom →
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        Nonempty (T ⟶ V) ↔
          ∃ a, (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor).obj a = T

variable {B S hS} {𝒞 : BasedCategory.{v₁, u₁} (BigFppfOver B S hS)}
  {𝒟 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)}

/-- The first projection of the 2-fibre product with a fully faithful 1-morphism is fully
faithful. -/
private noncomputable def fullyFaithful_fst_of_fullyFaithful (G : 𝒞 ⥤ᵇ 𝒟)
    [G.toFunctor.Full] [G.toFunctor.Faithful] {U : BigFppfOver B S hS}
    {y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj} (hy : y ⋙ 𝒟.p = Over.map U.hom) :
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor).FullyFaithful :=
  fullyFaithfulTwoFibreProductFst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor hy G.w
    (Functor.FullyFaithful.ofFullyFaithful G.toFunctor)

variable (B S hS) in
/-- **Every 2-fibre product of a fully faithful 1-morphism with a closed locus is the closed
subscheme the locus cuts out.** -/
theorem exists_isClosedImmersion_equivalenceOver_of_hasClosedLocus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful)
    (hclosed : HasClosedLocus B S hS G) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj) (hy : y ⋙ 𝒟.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor)
        (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) := by
  obtain ⟨V, hV, hVlocus⟩ := hclosed U y hy
  refine ⟨V, hV, nonempty_equivalenceOver_of_range_obj_eq _ _
    (fullyFaithful_fst_of_fullyFaithful G hy)
    (fullyFaithfulElementsProjection (yoneda.obj V)
      (fun T ↦ subsingleton_hom_of_isClosedImmersion B S hS U V hV T.unop)) ?_⟩
  rw [range_elementsProjection_obj]
  ext T
  exact (hVlocus T).symm

variable (B S hS) in
/-- **A fully faithful 1-morphism with a closed locus is representable by algebraic spaces**,
the representing algebraic space of a base change being the closed subscheme of the base the
locus cuts out. -/
theorem isRepresentableByAlgebraicSpaces_of_hasClosedLocus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful)
    (hclosed : HasClosedLocus B S hS G) :
    IsRepresentableByAlgebraicSpaces B S hS G := by
  intro U
  dsimp only
  intro y hy
  obtain ⟨V, _, he⟩ := exists_isClosedImmersion_equivalenceOver_of_hasClosedLocus B S hS G
    hfull hfaithful hclosed U y hy
  exact ⟨yoneda.obj V, isAlgebraicSpace_yoneda B U.left.1 U.left.2 V, he⟩

variable (B S hS) in
/-- **Every algebraic space representing a base change of a fully faithful 1-morphism with a
closed locus is the closed subscheme the locus cuts out**: both presheaves take subsingleton
values and have the same support. -/
theorem exists_iso_yoneda_of_equivalenceOver_of_hasClosedLocus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful)
    (hclosed : HasClosedLocus B S hS G) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj) (hy : y ⋙ 𝒟.p = Over.map U.hom)
    (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor)
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom ∧ Nonempty (P ≅ yoneda.obj V) := by
  obtain ⟨V, hV, hVlocus⟩ := hclosed U y hy
  have hfst := (fullyFaithful_fst_of_fullyFaithful G hy).full
  obtain ⟨hrange, hfullP⟩ := range_obj_eq_and_full_of_equivalenceOver e hfst
  have hsubP : ∀ X, Subsingleton (P.obj X) := fun X ↦ by
    refine ⟨fun a b ↦ ?_⟩
    let A' : (presheafOfCategories (P ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk a⟩
    let D' : (presheafOfCategories (P ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk b⟩
    obtain ⟨m, hm⟩ := (presheafOfCategories (P ⋙ typeToCat)).p.map_surjective
      (X := A') (Y := D') (𝟙 X.unop)
    have he : a = P.map m.base.op b := Discrete.eq_of_hom m.fiber
    change m.base = 𝟙 X.unop at hm
    rw [hm] at he
    change a = P.map (𝟙 X) b at he
    simpa only [P.map_id, types_id_apply] using he
  refine ⟨V, hV, nonempty_iso_of_subsingleton P (yoneda.obj V) hsubP
    (fun T ↦ subsingleton_hom_of_isClosedImmersion B S hS U V hV T.unop) ?_⟩
  intro T
  have h1 := congrArg (T.unop ∈ ·) (range_elementsProjection_obj P)
  have h2 := congrArg (T.unop ∈ ·) hrange
  simp only [eq_iff_iff] at h1 h2
  exact h1.symm.trans (h2.symm.trans (hVlocus T.unop).symm)

variable (B S hS) in
/-- **A fully faithful 1-morphism with a closed locus is a closed immersion**: every algebraic
space representing a base change of it along a scheme-valued point of the target has closed
immersion structural morphism, read as a morphism of algebraic spaces over `S`.  This is the
condition of Stacks 04XB at `AlgebraicGeometry.Space.IsClosedImmersion` written out. -/
theorem isClosedImmersion_of_hasClosedLocus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful)
    (hclosed : HasClosedLocus B S hS G) :
    ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj),
      y ⋙ 𝒟.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor)
          (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsClosedImmersion B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom := by
  intro U y hy P hP he
  obtain ⟨V, hV, ⟨i⟩⟩ := exists_iso_yoneda_of_equivalenceOver_of_hasClosedLocus B S hS G hfull
    hfaithful hclosed U y hy P he.some
  exact isClosedImmersion_algebraicSpaceMap_of_iso_yoneda B S hS U P hP V i hV

end ClosedLocus

/-! ### Categories fibred in groupoids -/

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- **Both conjuncts of Stacks 04YL (2) from a closed locus.**  A fully faithful 1-morphism of
categories fibred in groupoids over the big fppf site of `S` whose image is cut out, on the base
of every scheme-valued point of the target, by a closed subscheme is representable by algebraic
spaces *and* a closed immersion. -/
theorem isClosedImmersion_and_isRepresentableByAlgebraicSpaces_of_hasClosedLocus (f : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor f).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor f).Faithful)
    (hclosed : HasClosedLocus B S hS f.hom) :
    IsClosedImmersion B S hS f ∧ IsRepresentableByAlgebraicSpaces B S hS f.hom :=
  ⟨isClosedImmersion_of_hasClosedLocus B S hS f.hom hfull hfaithful hclosed,
    isRepresentableByAlgebraicSpaces_of_hasClosedLocus B S hS f.hom hfull hfaithful hclosed⟩

end AlgebraicGeometry.Stack

end
