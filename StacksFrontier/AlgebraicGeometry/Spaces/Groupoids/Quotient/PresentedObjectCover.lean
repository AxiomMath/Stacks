module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.RestrictionCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.LocallySurjective

/-!
# Presenting an object of a quotient stack over one fppf cover

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site and let `x` be an object of the quotient stack `[U/R]` over a test
object `T`. By **Stacks 044X** `x` comes from a point of the object space over each member of
some fppf covering of `T`; gathering the members of a size-bounded refinement into one object of
the site makes it come from a point over a single surjective, flat, locally finitely presented
morphism `V ⟶ T`.

This is the input the converse half of **Stacks 06PJ** needs: a morphism `g : U' ⟶ U` of
algebraic spaces whose source is the algebraic space of a scheme and which presents the pullback
of a presentation of `[U/R]`.

## Main results

* `AlgebraicGeometry.Stack.exists_fppf_cover_presented_object`: an object of a fibre of `[U/R]`
  is presented by a point of the object space over one surjective, flat, locally finitely
  presented morphism to the test object.
* `AlgebraicGeometry.Stack.isPullback_restrictionSource`: the source of the restriction of
  **Stacks 044B** along `g` is a base change of the saturation map of `g`.
* `AlgebraicGeometry.Stack.restrictionSource_property_of_saturation`: consequently every property
  of morphisms of algebraic spaces stable under base change passes from the saturation map to
  that source, and
  `AlgebraicGeometry.Stack.restrictionTarget_property_of_restrictionSource` carries it on to the
  target of the restriction.
* `AlgebraicGeometry.Stack.isLocallySurjective_saturation_of_local_presented_iso`: condition (1)
  of **Stacks 06PJ** for `g`, from the local presentation of every point of the object space by a
  point of `U'`.
* `AlgebraicGeometry.Stack.isLocallySurjective_of_surjective_flat_lfp` and
  `AlgebraicGeometry.Stack.isLocallySurjective_yoneda_map_of_fppf`: a surjective, flat, locally
  finitely presented morphism is a surjection of fppf sheaves, for algebraic spaces and for
  objects of the site.

## Implementation notes

The gathering argument is the one of **Stacks 04TB** for the isomorphism sheaf: the covering
produced by Stacks 044X is refined to one indexed by a set of size at most that of the base
scheme (Stacks 000X), its members are gathered into one object of the site, and the summands are
monomorphisms with empty pairwise intersections, so that points of the object space over them
glue with no compatibility condition and the resulting isomorphisms of objects of `[U/R]` glue by
the descent of `[U/R]`. That argument is carried out for a *pair* of objects in
`AlgebraicGeometry.Stack.exists_single_cover_presented_pair`, and the statement for one object is
the diagonal case of it.

## References

* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v₀ v₁

open Opposite

/-- **An object of a quotient stack is presented by a point of the object space over a single
surjective, flat, locally finitely presented morphism to the test object.** This is **Stacks
044X** (1) with the covering it produces gathered into one morphism, as in the proof of
Stacks 04TB. -/
theorem exists_fppf_cover_presented_object
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x : (quotientStack G).p.Fiber T) :
    ∃ (V : BigFppfOver C S hS) (f : V ⟶ T),
      Flat (C.inclusion.map f.left) ∧
      LocallyOfFinitePresentation (C.inclusion.map f.left) ∧
      Surjective (C.inclusion.map f.left) ∧
      ∃ a : G.objects.obj.obj (Opposite.op V),
        Nonempty ((pointwiseToQuotientStackFiber G V).obj a ≅
          Functor.pullbackFiber (quotientStack G).p x f) := by
  obtain ⟨V, f, hfFlat, hfLfp, hfSurj, a, -, ha, -⟩ :=
    exists_single_cover_presented_pair C S hS G T x x
  exact ⟨V, f, hfFlat, hfLfp, hfSurj, a, ha⟩

/-- The Yoneda correspondence carries a composite with a map of presheaves to the image of the
section under that map. -/
theorem yonedaEquiv_comp_apply
    {D : Type v₀} [Category.{v₁} D] {X : D}
    {F G : Dᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (f : F ⟶ G) :
    yonedaEquiv (α ≫ f) = f.app (Opposite.op X) (yonedaEquiv α) := by
  simp [yonedaEquiv_apply]

/-- **Stacks 044V.** An isomorphism of two objects of a fibre of `[U/R]` presented by points of
the object space comes from an arrow of the arrow space with those source and target. -/
theorem exists_arrow_of_presented_iso
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    (x y : G.objects.obj.obj (op T))
    (e : (pointwiseToQuotientStackFiber G T).obj x ≅
      (pointwiseToQuotientStackFiber G T).obj y) :
    ∃ r : G.arrows.obj.obj (op T),
      G.source.hom.app (op T) r = x ∧ G.target.hom.app (op T) r = y := by
  let X := (pointwiseToQuotientStackFiber G T).obj x
  let Y := (pointwiseToQuotientStackFiber G T).obj y
  let e' := Functor.pullbackFiberIdIso X ≪≫ e ≪≫ (Functor.pullbackFiberIdIso Y).symm
  let a := ((isomPresheafPullbackIso G T x y X Y rfl rfl).inv.app
    (op (Over.mk (𝟙 T))) ⟨e'.hom, by change IsIso e'.hom; infer_instance⟩).down
  let q := prod.lift (yonedaEquiv.symm y) (yonedaEquiv.symm x)
  let p := prod.lift G.target.hom G.source.hom
  have ha : (pullback.fst q p).app (op T) a.1 = 𝟙 T := a.2
  have hs : pullback.snd q p ≫ G.source.hom =
      pullback.fst q p ≫ yonedaEquiv.symm x := by
    simpa only [p, q, Category.assoc, prod.lift_snd] using
      congrArg (fun k => k ≫ prod.snd) (pullback.condition (f := q) (g := p)).symm
  have ht : pullback.snd q p ≫ G.target.hom =
      pullback.fst q p ≫ yonedaEquiv.symm y := by
    simpa only [p, q, Category.assoc, prod.lift_fst] using
      congrArg (fun k => k ≫ prod.fst) (pullback.condition (f := q) (g := p)).symm
  refine ⟨(pullback.snd q p).app (op T) a.1, ?_, ?_⟩
  · show (pullback.snd q p ≫ G.source.hom).app (op T) a.1 = x
    rw [hs, NatTrans.comp_app_apply, ha]
    exact yonedaEquiv.apply_symm_apply x
  · show (pullback.snd q p ≫ G.target.hom).app (op T) a.1 = y
    rw [ht, NatTrans.comp_app_apply, ha]
    exact yonedaEquiv.apply_symm_apply y

/-- The saturation map of `g : U' ⟶ U` is a surjection of fppf sheaves as soon as every point of
the object space is, locally on its test object, presented by the same object of `[U/R]` as a
point of `U'`. -/
theorem isLocallySurjective_saturation_of_local_presented_iso
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hloc : ∀ (T : BigFppfOver C S hS) (x : G.objects.obj.obj (op T)),
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V⦄ (b : V ⟶ T), R b → ∃ a : U'.obj.obj (op V), Nonempty
          ((pointwiseToQuotientStackFiber G V).obj
              (G.objects.obj.map b.op x) ≅
            (pointwiseToQuotientStackFiber G V).obj (g.hom.app (op V) a))) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom) := by
  constructor
  intro T x
  obtain ⟨R, hR, hloc⟩ := hloc T x
  apply (BigFppfOver.topology C S hS).superset_covering _ hR
  intro V b hb
  obtain ⟨a, ⟨e⟩⟩ := hloc b hb
  obtain ⟨r, hs, ht⟩ := exists_arrow_of_presented_iso C S hS G V _ _ e
  let α : yoneda.obj V ⟶ U'.obj := yonedaEquiv.symm a
  let β : yoneda.obj V ⟶ G.arrows.obj := yonedaEquiv.symm r
  have hw : α ≫ g.hom = β ≫ G.target.hom := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp_apply, α, β, Equiv.apply_symm_apply] using ht.symm
  let q := pullback.lift α β hw
  refine ⟨yonedaEquiv q, ?_⟩
  show ((pullback.snd g.hom G.target.hom ≫ G.source.hom).app (op V))
    (yonedaEquiv q) = G.objects.obj.map b.op x
  rw [← yonedaEquiv_comp_apply]
  show yonedaEquiv (pullback.lift α β hw ≫
    pullback.snd g.hom G.target.hom ≫ G.source.hom) = _
  rw [pullback.lift_snd_assoc, yonedaEquiv_comp_apply]
  simpa only [β, Equiv.apply_symm_apply] using hs

/-- A surjective, flat, locally finitely presented morphism of algebraic spaces over `S` is a
surjection of fppf sheaves: its base change along any point of the target is such a morphism
again, so the point lifts locally. -/
theorem isLocallySurjective_of_surjective_flat_lfp
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {F H : AlgebraicSpaces C S hS} (f : F ⟶ H)
    (hflat : Space.IsFlat C S hS f.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS f.hom)
    (hsurj : Space.IsSurjective C S hS f.hom) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) f.hom := by
  have := Space.isFlat_isStableUnderBaseChange C S hS
  have := Space.isLocallyOfFinitePresentation_isStableUnderBaseChange C S hS
  have hrep : Space.IsRepresentableByAlgebraicSpaces C S hS f.hom := fun T t =>
    isAlgebraicSpace_pullback C S hS t f.hom
      (isAlgebraicSpace_yoneda C S hS T) F.property H.property
  apply Space.isLocallySurjective_of_isRepresentableByAlgebraicSpaces
    C S hS F.property.isSheaf H.property.isSheaf f.hom hrep
  all_goals
    intro T t
    have hpb := (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (ObjectProperty.homMk t : (⟨yoneda.obj T, isAlgebraicSpace_yoneda C S hS T⟩ :
        AlgebraicSpaces C S hS) ⟶ H) f).flip
  · exact MorphismProperty.of_isPullback
      (P := fun {A B : AlgebraicSpaces C S hS} (f : A ⟶ B) => Space.IsFlat C S hS f.hom) hpb hflat
  · exact MorphismProperty.of_isPullback
      (P := fun {A B : AlgebraicSpaces C S hS} (f : A ⟶ B) =>
        Space.IsLocallyOfFinitePresentation C S hS f.hom) hpb hlfp
  · exact Space.isSurjective_of_isPullback C S hS hpb hsurj


/-- The source of the restriction of **Stacks 044B** along `g` is the base change of the
saturation map `U' ×_{g, U, t} R ⟶ U` of `g` along `g`. -/
theorem isPullback_restrictionSource
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    IsPullback
      (GroupoidInAlgebraicSpaces.fiberProductFst
        (GroupoidInAlgebraicSpaces.fiberProductSnd g G.target)
        (GroupoidInAlgebraicSpaces.fiberProductFst G.source g))
      (GroupoidInAlgebraicSpaces.restrictionSource G g)
      (GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source) g :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS
    (GroupoidInAlgebraicSpaces.fiberProductSnd g G.target)
    (GroupoidInAlgebraicSpaces.fiberProductFst G.source g)).paste_vert
      (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g)

/-- Every property of morphisms of algebraic spaces stable under base change passes from the
saturation map of `g` to the source of the restriction of **Stacks 044B** along `g`. -/
theorem restrictionSource_property_of_saturation
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (h : P (GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source)) :
    P (GroupoidInAlgebraicSpaces.restrictionSource G g) :=
  P.of_isPullback (isPullback_restrictionSource C S hS G g) h

/-- Any property of morphisms of algebraic spaces respecting isomorphisms holds for the target of
the restriction of **Stacks 044B** along `g` as soon as it holds for its source: the inversion of
arrows of the restricted groupoid is an isomorphism exchanging the two. -/
theorem restrictionTarget_property_of_restrictionSource
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.RespectsIso]
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (h : P (GroupoidInAlgebraicSpaces.restrictionSource G g)) :
    P (GroupoidInAlgebraicSpaces.restrictionTarget G g) := by
  set D := GroupoidInAlgebraicSpaces.restrict G g with hD
  have hsrc : P D.groupoid.source := by
    rw [D.source_eq]
    exact MorphismProperty.RespectsIso.precomp P _ _
      (MorphismProperty.RespectsIso.postcomp P _ _ h)
  have htgt : P D.groupoid.target := by
    rw [← GroupoidInAlgebraicSpaces.inverseArrow_comp_source D.groupoid]
    exact MorphismProperty.RespectsIso.precomp P _ _ hsrc
  rw [D.target_eq] at htgt
  simpa only [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso] using htgt

/-- A morphism of the big fppf site over `S` which is surjective, flat and locally of finite
presentation induces a surjection of fppf sheaves on representable presheaves. -/
theorem isLocallySurjective_yoneda_map_of_fppf
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {V W : BigFppfOver C S hS} (b : V ⟶ W)
    (hflat : Flat (C.inclusion.map b.left))
    (hlfp : LocallyOfFinitePresentation (C.inclusion.map b.left))
    (hsurj : Surjective (C.inclusion.map b.left)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (yoneda.map b) := by
  let E : PreZeroHypercover.{u + 1} W := PreZeroHypercover.singleton b
  have hE : (E.map (BigFppfOver.toScheme C S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage (C.inclusion.obj W.left) := by
    show (PreZeroHypercover.singleton (C.inclusion.map b.left)).presieve₀ ∈ _
    simpa only [PreZeroHypercover.presieve₀_singleton] using
      (C.inclusion.map b.left).singleton_mem_fppfPrecoverage
  have hcover := sieve_mem_of_fppf C S hS E hE
  have hle : E.sieve₀ ≤ Presheaf.imageSieve (yoneda.map b) (𝟙 W) := by
    rw [Sieve.generate_le_iff]
    rintro Z _ ⟨i⟩
    exact ⟨𝟙 V, Category.id_comp b⟩
  have hId := (BigFppfOver.topology C S hS).superset_covering hle hcover
  constructor
  intro T k
  have ht := (BigFppfOver.topology C S hS).pullback_stable k hId
  rw [Presheaf.pullback_imageSieve] at ht
  change Presheaf.imageSieve (yoneda.map b) (k ≫ 𝟙 W) ∈ _ at ht
  simpa only [Category.comp_id] using ht


end AlgebraicGeometry.Stack

end
