module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.ShrinkYoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableByAlgebraicSpaces

/-!
# Composition, base change and cancellation of morphisms representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism of presheaves on the big
fppf site of `S` is *representable by algebraic spaces* when each of its base changes along a
scheme-valued point of its target is an algebraic space over `S`. This file proves that the
class of such morphisms is stable under base change and closed under composition, and that a
first factor of a composite is representable by algebraic spaces as soon as the composite is
and the relative diagonal of the second factor is, in the value universe `max w u` with `w`
independent of the universe `u` of the schemes; that is the generality in which a formal
algebraic space, a sheaf of `Type (u + 1)`, lives.

The base change and composition statements have a companion assertion about morphisms
representable *by schemes*. That notion is relative representability of a morphism of presheaves
along the Yoneda embedding, `CategoryTheory.Functor.relativelyRepresentable`, a
`CategoryTheory.MorphismProperty` which is stable under base change and multiplicative.

## Main results

* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_of_isPullback`:
  **Stacks 0APZ**, stability under base change.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_comp`: **Stacks 0APY**,
  closure under composition.
* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift`:
  **Stacks 03XY**, a fibre product of an algebraic space with the source of a morphism
  representable by algebraic spaces is an algebraic space.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_of_comp`: **Stacks 0AMN**,
  cancellation of the second factor against its relative diagonal.
* `AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`: an
  algebraic space over `S` with values in a larger universe is the universe lift of an
  algebraic space over `S` with values in the value universe of the site.
* `CategoryTheory.Functor.relativelyRepresentable.isStableUnderBaseChange` and
  `CategoryTheory.Functor.relativelyRepresentable.isMultiplicative` are the corresponding
  assertions for morphisms representable by schemes.

## Implementation notes

Base change needs nothing but the pasting calculus for cartesian squares: a base change of a
base change of `a` along a scheme-valued point is a base change of `a` along the composite
point, and the algebraic-space condition transports along the resulting isomorphism by
`AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_iso`. The square is taken in the form
`CategoryTheory.IsPullback`, so no chosen pullback object is imposed on the caller.

Composition reduces to Stacks 02YS, which is
`AlgebraicGeometry.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces`: a base change of `a ≫ b`
along a point `ξ` of the target receives a morphism, itself a base change of `a`, from the base
change of `b` along `ξ`, which is an algebraic space; so the source is an algebraic space as soon
as 02YS applies. The obstruction is that 02YS is stated in the value universe `u` of the site,
where sheafification is available, while the morphism at hand lives in `Type (max w u)`. It is
removed by descending: a presheaf satisfying the algebraic-space condition is pointwise `u`-small,
because each of its sections is cut out of the sections of an étale atlas over a `u`-small object
of the site, and a morphism representable by algebraic spaces has a pointwise `u`-small source as
soon as its target is pointwise `u`-small, because its fibres are. Hence both presheaves are
universe lifts of presheaves of `Type u`, `CategoryTheory.FunctorToTypes.uliftFunctor` being fully
faithful and preserving fibre products, and the algebraic-space and representability conditions are
unchanged by the lift.

Cancellation is the same argument as in the value universe of the site: the base change of `a`
along a point `ξ` of `G` is the base change of the relative diagonal of `b` along the comparison
morphism from the base change of `a ≫ b` along `ξ ≫ b` to `pullback b b`, and that base change has
an algebraic space for its source, so Stacks 03XY applies; Stacks 03XY itself is the composite of
base change with the descent above.

## References

* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 0AMN](https://stacks.math.columbia.edu/tag/0AMN)
* [Stacks Project, Tag 0APY](https://stacks.math.columbia.edu/tag/0APY)
* [Stacks Project, Tag 0APZ](https://stacks.math.columbia.edu/tag/0APZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change -/

/-- A base change of a morphism representable by algebraic spaces is
representable by algebraic spaces: in a cartesian square of presheaves on the big fppf site
of `S` with values in `Type (max w u)` whose right-hand column `a` is representable by
algebraic spaces, the left-hand column `a'` is representable by algebraic spaces too. -/
@[stacks 0APZ "representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpacesULift_of_isPullback
    {F G G' H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (p : H ⟶ F) (a' : H ⟶ G') (a : F ⟶ G) (g : G' ⟶ G) (h : IsPullback p a' a g)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a) :
    IsRepresentableByAlgebraicSpacesULift.{w} B S hS a' := fun U ξ =>
  isAlgebraicSpaceULift_of_iso B S hS
    (((IsPullback.of_hasPullback ξ a').flip.paste_horiz h).isoIsPullback _ _
      (IsPullback.of_hasPullback (ξ ≫ g) a).flip).symm (ha U (ξ ≫ g))

add_to_stacks 0APZ "representable by schemes"
  CategoryTheory.Functor.relativelyRepresentable.isStableUnderBaseChange

/-! ### Smallness of the presheaves involved -/

/-- A sheaf on the big fppf site of `S` has injective restriction along a morphism of the
site whose underlying morphism of schemes is surjective and étale: such a morphism generates
a covering sieve, so a sheaf is separated for the presieve it generates. -/
theorem map_injective_of_surjective_etale
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {V T : BigFppfOver B S hS} (q : V ⟶ T)
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (he : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    Function.Injective (F.map q.op) := by
  have hc : Sieve.generate (Presieve.singleton q) ∈ BigFppfOver.topology B S hS T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    apply B.topology.superset_covering (Sieve.generate_mono ?_)
      (singleton_mem_bigFppf_topology B q.left hs he)
    exact (Presieve.singleton_le_iff q.left).2
      ⟨V, q, 𝟙 _, Presieve.singleton_self q, by simp⟩
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp hF _ hc).isSeparatedFor
  rw [← Presieve.isSeparatedFor_iff_generate] at hsep
  intro x y h
  exact hsep.ext (by intro W f hf; cases hf; exact h)

/-- A sheaf on the big fppf site of `S` with values in `Type (max w u)` receiving a morphism
which is representable by objects of the site, surjective and étale from a pointwise `u`-small
presheaf is itself pointwise `u`-small: a section over `T` is determined by an object of a
small model of the site, a morphism of the site to `T` and a section of the source, because
the section lifts along the morphism after an étale surjective base change, and restriction
along that base change is injective. -/
theorem small_of_relative_surjective_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (a : G ⟶ F)
    (hs : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) a)
    (he : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) a)
    [FunctorToTypes.Small.{u} G] : FunctorToTypes.Small.{u} F := by
  classical
  let C := BigFppfOver B S hS
  have hC : EssentiallySmall.{u} C := essentiallySmall_bigFppfOver B S hS
  let E := (equivSmallModel.{u} C).inverse
  intro T
  let Code := Σ V : SmallModel.{u} C, (E.obj V ⟶ T.unop) × G.obj (Opposite.op (E.obj V))
  have exists_code (x : F.obj T) : ∃ c : Code,
      Function.Injective (F.map c.2.1.op) ∧
      F.map c.2.1.op x = a.app _ c.2.2 := by
    let g : uliftYoneda.{w}.obj T.unop ⟶ F := uliftYonedaEquiv.symm x
    let V := hs.rep.pullback g
    let p : V ⟶ T.unop := hs.rep.snd g
    let y : G.obj (Opposite.op V) := (hs.rep.fst g).app (Opposite.op V) ⟨𝟙 V⟩
    let e : E.obj ((equivSmallModel.{u} C).functor.obj V) ≅ V :=
      ((equivSmallModel.{u} C).unitIso.app V).symm
    refine ⟨⟨_, e.hom ≫ p, G.map e.hom.op y⟩, ?_, ?_⟩
    · have hp := map_injective_of_surjective_etale B S hS hF p
        (hs.property_snd g) (he.property g _ _ (hs.rep.isPullback g))
      simpa only [op_comp, F.map_comp, types_comp] using
        (injective_of_mono (F.map e.hom.op)).comp hp
    · have hv := congrArg (fun k => k.app (Opposite.op V) ⟨𝟙 V⟩) (hs.rep.w g)
      have hv' : F.map p.op x = a.app (Opposite.op V) y := by
        change a.app (Opposite.op V) y = F.map (𝟙 V ≫ p).op x at hv
        simpa only [Category.id_comp] using hv.symm
      show F.map (p.op ≫ e.hom.op) x = _
      rw [F.map_comp]
      show F.map e.hom.op (F.map p.op x) = _
      rw [hv']
      exact (congrArg (fun k => k y) (a.naturality e.hom.op)).symm
  choose code hcode using exists_code
  apply small_of_injective (f := code)
  intro x y h
  exact (hcode x).1 (by rw [(hcode x).2, h, ← (hcode y).2])

/-- An algebraic space over `S` with values in `Type (max w u)` is pointwise `u`-small: a
section over `T` is determined by an object of a small model of the site, a morphism of the
site to `T` and a section of the atlas, because the section lifts along the atlas after an
étale surjective base change, and restriction along that base change is injective. -/
theorem small_of_isAlgebraicSpaceULift
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) : FunctorToTypes.Small.{u} F := by
  obtain ⟨U, f, hs, he⟩ := hF.exists_atlas
  have : FunctorToTypes.Small.{u} ((uliftYoneda.{w}).obj U) := fun _ ↦ small_map Equiv.ulift
  exact small_of_relative_surjective_etale B S hS hF.isSheaf f hs he

/-- The source of a morphism representable by algebraic spaces is pointwise `u`-small as
soon as its target is: the fibre of the morphism over a section of the target is a quotient
of the sections of the base change along the corresponding scheme-valued point, which is an
algebraic space and hence pointwise `u`-small. -/
private theorem small_source_of_isRepresentableByAlgebraicSpacesULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a)
    [FunctorToTypes.Small.{u} G] : FunctorToTypes.Small.{u} F := by
  intro T
  have hfiber (y : G.obj T) : Small.{u} {x : F.obj T // a.app T x = y} := by
    let g : uliftYoneda.{w}.obj T.unop ⟶ G := uliftYonedaEquiv.symm y
    have hQ := small_of_isAlgebraicSpaceULift B S hS (ha T.unop g)
    apply small_of_injective_of_exists
      (fun z : (pullback g a).obj T => (pullback.snd g a).app T z)
      (g := Subtype.val) Subtype.val_injective
    intro x
    have hp := (IsPullback.of_hasPullback g a).map ((evaluation _ (Type (max w u))).obj T)
    obtain ⟨z, hz, hx⟩ := Types.exists_of_isPullback hp (ULift.up (𝟙 T.unop)) x.val
      (by simpa [g, uliftYonedaEquiv] using x.property.symm)
    exact ⟨z, hx⟩
  have _ := hfiber
  apply small_of_injective
    (f := fun x : F.obj T => (⟨a.app T x, x, rfl⟩ : Σ y, {x : F.obj T // a.app T x = y}))
  exact fun _ _ h => congrArg (fun z => z.2.val) h

/-! ### Descent of the two conditions to the value universe of the site -/

/-- Shrinking a pointwise `u`-small presheaf with values in `Type (max w u)` and lifting the
result back to `Type (max w u)` returns the presheaf, up to isomorphism. -/
noncomputable def shrinkCompUliftFunctorIso
    {C : Type*} [Category* C] (F : C ⥤ Type (max w u)) [FunctorToTypes.Small.{u} F] :
    FunctorToTypes.shrink.{u} F ⋙ uliftFunctor.{w} ≅ F :=
  NatIso.ofComponents (fun X => (Equiv.ulift.trans (equivShrink (F.obj X)).symm).toIso)
    (by
      intro X Y f
      ext x
      change (equivShrink (F.obj Y)).symm
        ((equivShrink (F.obj Y)) (F.map f ((equivShrink (F.obj X)).symm x.down))) = _
      exact (equivShrink (F.obj Y)).symm_apply_apply _)

/-- Relative representability of a morphism along a functor `i` is unchanged by applying a
fully faithful functor preserving fibre products: the fibre products that have to exist and
the objects representing them correspond. -/
theorem relativelyRepresentable_comp_map_iff
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (i : C ⥤ D) (H : D ⥤ E) [H.Full] [H.Faithful]
    [PreservesLimitsOfShape WalkingCospan H] {X Y : D} (f : X ⟶ Y) :
    (i ⋙ H).relativelyRepresentable (H.map f) ↔ i.relativelyRepresentable f := by
  constructor
  · intro hf U g
    obtain ⟨V, p, q, hp⟩ := hf (H.map g)
    obtain ⟨q', rfl⟩ := H.map_surjective q
    exact ⟨V, p, q', hp.of_map_of_faithful H⟩
  · intro hf U g
    obtain ⟨g', rfl⟩ := H.map_surjective g
    obtain ⟨V, p, q, hp⟩ := hf g'
    exact ⟨V, p, H.map q, hp.map H⟩

/-- A relative morphism property along a functor `i` is unchanged by applying a fully
faithful functor preserving fibre products. -/
theorem relative_comp_map_iff
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (i : C ⥤ D) (H : D ⥤ E) [H.Full] [H.Faithful]
    [PreservesLimitsOfShape WalkingCospan H]
    (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y) :
    P.relative (i ⋙ H) (H.map f) ↔ P.relative i f := by
  constructor
  · intro hf
    refine ⟨(relativelyRepresentable_comp_map_iff i H f).mp hf.rep, ?_⟩
    intro U V g q p hp
    exact hf.property (H.map g) (H.map q) p (hp.map H)
  · intro hf
    refine ⟨(relativelyRepresentable_comp_map_iff i H f).mpr hf.rep, ?_⟩
    intro U V g q p hp
    obtain ⟨g', rfl⟩ := H.map_surjective g
    obtain ⟨q', rfl⟩ := H.map_surjective q
    exact hf.property g' q' p (hp.of_map_of_faithful H)

/-- The universe lift of a presheaf of `Type u` on the big fppf site of `S` is an algebraic
space over `S` in the value universe `max w u` exactly when the presheaf is an algebraic
space over `S`. -/
theorem isAlgebraicSpaceULift_comp_uliftFunctor_iff
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsAlgebraicSpaceULift.{w} B S hS (F ⋙ uliftFunctor.{w}) ↔
      IsAlgebraicSpace B S hS F := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max w u))).obj uliftFunctor.{w}
  have hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (F ⋙ uliftFunctor.{w}) ↔
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) F := by
    simp only [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff]
  have hdiag : (uliftYoneda.{w} (C := C)).relativelyRepresentable (diag (H.obj F)) ↔
      yoneda.relativelyRepresentable (diag F) := by
    have hd : H.map (diag F) ≫ prodComparison H F F = diag (H.obj F) := by
      apply prod.hom_ext <;> simp [← H.map_comp]
    rw [← hd]
    exact ((yoneda ⋙ H).relativelyRepresentable.cancel_right_of_respectsIso
      (H.map (diag F)) (prodComparison H F F)).trans
      (relativelyRepresentable_comp_map_iff yoneda H _)
  constructor
  · intro hF
    refine ⟨hsheaf.mp hF.isSheaf, hdiag.mp hF.diagonal_representable, ?_⟩
    obtain ⟨U, f, hs, he⟩ := hF.exists_atlas
    obtain ⟨f', rfl⟩ := H.map_surjective f
    exact ⟨U, f', (relative_comp_map_iff yoneda H _ _).mp hs,
      (relative_comp_map_iff yoneda H _ _).mp he⟩
  · intro hF
    refine ⟨hsheaf.mpr hF.isSheaf, hdiag.mpr hF.diagonal_representable, ?_⟩
    obtain ⟨U, f, hs, he⟩ := hF.exists_atlas
    exact ⟨U, H.map f, (relative_comp_map_iff yoneda H _ _).mpr hs,
      (relative_comp_map_iff yoneda H _ _).mpr he⟩

/-- **An algebraic space over `S` with values in `Type (max w u)` is the universe lift of an
algebraic space over `S` with values in the value universe of the site.** It is pointwise
`u`-small, so shrinking it pointwise and lifting the result back returns it up to isomorphism,
and the algebraic-space condition descends along that isomorphism. -/
theorem exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (hF : IsAlgebraicSpaceULift.{w} B S hS F) :
    ∃ F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B S hS F' ∧ Nonempty (F' ⋙ uliftFunctor.{w} ≅ F) := by
  have _ := small_of_isAlgebraicSpaceULift B S hS hF
  refine ⟨FunctorToTypes.shrink.{u} F, ?_, ⟨shrinkCompUliftFunctorIso F⟩⟩
  exact (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mp
    (isAlgebraicSpaceULift_of_iso B S hS (shrinkCompUliftFunctorIso F).symm hF)

/-- The universe lift of a morphism of presheaves of `Type u` on the big fppf site of `S` is
representable by algebraic spaces in the value universe `max w u` exactly when the morphism
is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpacesULift_whiskerRight_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    IsRepresentableByAlgebraicSpacesULift.{w} B S hS
      (Functor.whiskerRight a uliftFunctor.{w}) ↔
      IsRepresentableByAlgebraicSpaces B S hS a := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max w u))).obj uliftFunctor.{w}
  constructor
  · intro ha U g
    have hp := (IsPullback.of_hasPullback g a).map H
    apply (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mp
    exact isAlgebraicSpaceULift_of_iso B S hS hp.isoPullback.symm (ha U (H.map g))
  · intro ha U g
    obtain ⟨g', rfl⟩ := H.map_surjective g
    have hp := (IsPullback.of_hasPullback g' a).map H
    exact isAlgebraicSpaceULift_of_iso B S hS hp.isoPullback
      ((isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr (ha U g'))

/-- **Stacks 02YS** in an arbitrary value universe: the source of a morphism representable
by algebraic spaces whose target is an algebraic space over `S` is an algebraic space
over `S`. Both presheaves are pointwise `u`-small, so this is the statement in the value
universe of the site transported along the universe lift. -/
private theorem isAlgebraicSpaceULift_of_isRepresentableByAlgebraicSpacesULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a)
    (hG : IsAlgebraicSpaceULift.{w} B S hS G) :
    IsAlgebraicSpaceULift.{w} B S hS F := by
  have hGsmall := small_of_isAlgebraicSpaceULift B S hS hG
  have hFsmall := small_source_of_isRepresentableByAlgebraicSpacesULift B S hS a ha
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max w u))).obj uliftFunctor.{w}
  let F' := FunctorToTypes.shrink.{u} F
  let G' := FunctorToTypes.shrink.{u} G
  let eF : H.obj F' ≅ F := shrinkCompUliftFunctorIso F
  let eG : H.obj G' ≅ G := shrinkCompUliftFunctorIso G
  let a' : F' ⟶ G' := H.preimage (eF.hom ≫ a ≫ eG.inv)
  have hp : IsPullback eF.hom (H.map a') a eG.hom := by
    apply IsPullback.of_horiz_isIso
    simp [a', H.map_preimage]
  have ha' : IsRepresentableByAlgebraicSpaces B S hS a' :=
    (isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS a').mp
      (isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hp ha)
  have hG' : IsAlgebraicSpace B S hS G' :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS G').mp
      (isAlgebraicSpaceULift_of_iso B S hS eG.symm hG)
  exact isAlgebraicSpaceULift_of_iso B S hS eF
    ((isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F').mpr
      (_root_.AlgebraicGeometry.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces
        B S hS a' ha' hG'))

/-! ### Composition -/

/-- A composition of morphisms representable by algebraic spaces is
representable by algebraic spaces, for presheaves on the big fppf site of `S` with values in
`Type (max w u)`. -/
@[stacks 0APY "representable by algebraic spaces in an arbitrary value universe"]
theorem isRepresentableByAlgebraicSpacesULift_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G) (b : G ⟶ H)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a)
    (hb : IsRepresentableByAlgebraicSpacesULift.{w} B S hS b) :
    IsRepresentableByAlgebraicSpacesULift.{w} B S hS (a ≫ b) := by
  intro U ξ
  let g : pullback ξ b ⟶ G := pullback.snd ξ b
  have hY := isAlgebraicSpaceULift_of_isRepresentableByAlgebraicSpacesULift B S hS
    (pullback.fst g a)
    (isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      (IsPullback.of_hasPullback g a).flip ha) (hb U ξ)
  exact isAlgebraicSpaceULift_of_iso B S hS
    ((IsPullback.of_hasPullback g a).flip.paste_vert
      (IsPullback.of_hasPullback ξ b).flip).flip.isoPullback hY

add_to_stacks 0APY "representable by schemes"
  CategoryTheory.Functor.relativelyRepresentable.isMultiplicative

/-! ### Cancellation -/

/-- The fibre product of an algebraic space over `S` with the source of a
morphism representable by algebraic spaces, over the target of that morphism, is an algebraic
space over `S`, for presheaves on the big fppf site of `S` with values in `Type (max w u)`. -/
@[stacks 03XY "in an arbitrary value universe"]
theorem isAlgebraicSpaceULift_pullback_of_isRepresentableULift
    {F G X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G) (f : X ⟶ G)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a)
    (hX : IsAlgebraicSpaceULift.{w} B S hS X) :
    IsAlgebraicSpaceULift.{w} B S hS (pullback f a) :=
  isAlgebraicSpaceULift_of_isRepresentableByAlgebraicSpacesULift B S hS (pullback.fst f a)
    (isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS (pullback.snd f a)
      (pullback.fst f a) a f (IsPullback.of_hasPullback f a).flip ha) hX

/-- If the relative diagonal of `b` and the composite `a ≫ b` are
representable by algebraic spaces, then so is `a`, for presheaves on the big fppf site of `S`
with values in `Type (max w u)`. -/
@[stacks 0AMN "representable by algebraic spaces in an arbitrary value universe"]
theorem isRepresentableByAlgebraicSpacesULift_of_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G) (b : G ⟶ H)
    (hdiag : IsRepresentableByAlgebraicSpacesULift.{w} B S hS (pullback.diagonal b))
    (hcomp : IsRepresentableByAlgebraicSpacesULift.{w} B S hS (a ≫ b)) :
    IsRepresentableByAlgebraicSpacesULift.{w} B S hS a := by
  intro U ξ
  refine isAlgebraicSpaceULift_of_iso B S hS
    (pullbackSymmetry _ _ ≪≫ pullbackDiagonalMapIdIso ξ a b) ?_
  exact isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS (pullback.diagonal b)
    (pullback.map (ξ ≫ b) (a ≫ b) b b ξ a (𝟙 _) (by simp) (by simp)) hdiag
    (hcomp U (ξ ≫ b))

end AlgebraicGeometry.Space

end
