module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension

/-!
# Transporting a groupoid in algebraic spaces along an isomorphism of its object space

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, in the sense of **Stacks 043W**, and let `e : G.objects ≅ U'` be an isomorphism of its
space of objects with another algebraic space over `S`. Then `U'` carries a groupoid in algebraic
spaces with the *same* space of arrows, whose source and target are those of `G` followed by `e`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.composablePairsObjectsIso`: the comparison of the
  two spaces of composable pairs. The composition law of a groupoid in algebraic spaces is a
  morphism out of the fibre product of the arrow space with itself along the source and the
  target, so changing the object space changes the *domain* of the composition law; this
  isomorphism is what carries it across, and it is the one piece of the transport which is not a
  renaming.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.transportObjects`: the transported groupoid.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.transportObjects_objects` and
  `transportObjects_arrows`: the transported groupoid has `U'` as its space of objects and the
  space of arrows of `G` as its space of arrows, both on the nose. The arrow space being
  unchanged is what makes the transport usable at a statement about the arrow space whose
  hypothesis prescribes a form for the object space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.transportObjects_source`,
  `transportObjects_target`, `transportObjects_objectsToBase`, `transportObjects_arrowsToBase`
  and `transportObjects_comp`: the remaining structure morphisms.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.fiberProductIsoOfIsoCospan`: two fibre products
  of isomorphic cospans of algebraic spaces over `S` are isomorphic.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerOverBaseTransportIso` and
  `dimension_stabilizerOverBase_transportObjects`: the stabilizer of **Stacks 0447** of the
  transported groupoid is isomorphic to that of `G`, and in particular has the dimension of
  **Stacks 04N6** of that of `G`. This is what lets a statement about the arrow space and the
  stabilizer be moved across the transport in both of its terms.

## Implementation notes

`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` is semireducible, so the only interface used
here to its two projections and to morphisms into it is
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` together with
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.fiberProductFst`, `fiberProductSnd` and
`fiberProduct_condition`; nothing unfolds the fibre product itself.

The pointwise groupoid of the transported groupoid is the pointwise groupoid of `G` carried along
the bijection of object sections that `e` induces at each test object, which is
`AlgebraicGeometry.Space.transportPointwise`. The arrow sections are left alone, so the bijection
on them is the identity. The compatibility of the two composition maps that
`transportPointwise` asks for is read off the comparison isomorphism of composable pairs through
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.pullbackAppEquiv`: a section of a pullback of
presheaves of types is determined by its two projections, and both composable-pair comparisons
have the same two projections.

`transportObjects` carries `@[implicit_reducible]`. Without it the object space and the square of
the object space of the transported groupoid are not type-correct against their explicit
descriptions at the `implicit` transparency level, and every `rw` whose motive mentions one of
them fails with an application type mismatch rather than with a missing pattern — the reason
recorded in `StacksFrontier.CategoryTheory.TwoFibreProduct.Swap` for the same attribute there.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### Sections of the presheaf of composable pairs -/

section Composable

variable {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}

/-- The canonical map from composable pairs to the pullback of the source and the target reads
off the first arrow of the pair along the first projection. -/
theorem composableToPullback_app_fst (s t : R ⟶ U) (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (Deformation.composableArrows U R s t).obj T) :
    (pullback.fst s t).app T ((composableToPullback s t).app T q) = q.1.1 := by
  change (composableToPullback s t ≫ pullback.fst s t).app T q = q.1.1
  rw [composableToPullback, pullback.lift_fst]
  rfl

/-- The canonical map from composable pairs to the pullback of the source and the target reads
off the second arrow of the pair along the second projection. -/
theorem composableToPullback_app_snd (s t : R ⟶ U) (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (Deformation.composableArrows U R s t).obj T) :
    (pullback.snd s t).app T ((composableToPullback s t).app T q) = q.1.2 := by
  change (composableToPullback s t ≫ pullback.snd s t).app T q = q.1.2
  rw [composableToPullback, pullback.lift_snd]
  rfl

end Composable

/-! ### The comparison of the two spaces of composable pairs -/

section Transport

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  {U' : AlgebraicSpaces C S hS} (e : G.objects ≅ U')

/-- The two projections of the space of composable pairs taken over the transported object space
satisfy the compatibility defining the space of composable pairs of `G` itself: the isomorphism
of object spaces may be cancelled on the right. -/
theorem fiberProduct_condition_comp_iso :
    fiberProductFst (G.source ≫ e.hom) (G.target ≫ e.hom) ≫ G.source =
      fiberProductSnd (G.source ≫ e.hom) (G.target ≫ e.hom) ≫ G.target := by
  refine (Iso.cancel_iso_hom_right _ _ e).mp ?_
  rw [Category.assoc, Category.assoc]
  exact fiberProduct_condition (G.source ≫ e.hom) (G.target ≫ e.hom)

/-- The two projections of the space of composable pairs of `G` satisfy the compatibility
defining the space of composable pairs taken over the transported object space. -/
theorem fiberProduct_condition_iso_comp :
    fiberProductFst G.source G.target ≫ (G.source ≫ e.hom) =
      fiberProductSnd G.source G.target ≫ (G.target ≫ e.hom) := by
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun k => k ≫ e.hom) (fiberProduct_condition G.source G.target)

/-- **The comparison of the two spaces of composable pairs.** The composition law of a groupoid
in algebraic spaces is given on the fibre product of the arrow space with itself along the source
and the target, so transporting the object space along an isomorphism `e` changes its domain.
Both fibre products are detected by the same pair of projections, since `e` may be cancelled, so
they are canonically isomorphic. -/
noncomputable def composablePairsObjectsIso :
    AlgebraicSpaces.fiberProduct C S hS (G.source ≫ e.hom) (G.target ≫ e.hom) ≅
      AlgebraicSpaces.fiberProduct C S hS G.source G.target where
  hom := (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift
    (fiberProductFst (G.source ≫ e.hom) (G.target ≫ e.hom))
    (fiberProductSnd (G.source ≫ e.hom) (G.target ≫ e.hom))
    (fiberProduct_condition_comp_iso G e)
  inv := (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (G.source ≫ e.hom) (G.target ≫ e.hom)).lift
    (fiberProductFst G.source G.target)
    (fiberProductSnd G.source G.target)
    (fiberProduct_condition_iso_comp G e)
  hom_inv_id := by
    refine (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (G.source ≫ e.hom) (G.target ≫ e.hom)).hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, IsPullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    refine (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, IsPullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd, Category.id_comp]

/-- The comparison of composable pairs commutes with the first projection. -/
theorem composablePairsObjectsIso_hom_comp_fst :
    (composablePairsObjectsIso G e).hom ≫ fiberProductFst G.source G.target =
      fiberProductFst (G.source ≫ e.hom) (G.target ≫ e.hom) :=
  IsPullback.lift_fst _ _ _ _

/-- The comparison of composable pairs commutes with the second projection. -/
theorem composablePairsObjectsIso_hom_comp_snd :
    (composablePairsObjectsIso G e).hom ≫ fiberProductSnd G.source G.target =
      fiberProductSnd (G.source ≫ e.hom) (G.target ≫ e.hom) :=
  IsPullback.lift_snd _ _ _ _

/-- The comparison of composable pairs, read on a section over a test object along the first
projection. -/
theorem composablePairsObjectsIso_hom_app_fst (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (AlgebraicSpaces.fiberProduct C S hS
      (G.source ≫ e.hom) (G.target ≫ e.hom)).obj.obj T) :
    (fiberProductFst G.source G.target).hom.app T
        ((composablePairsObjectsIso G e).hom.hom.app T x) =
      (fiberProductFst (G.source ≫ e.hom) (G.target ≫ e.hom)).hom.app T x :=
  congrArg
    (fun k : AlgebraicSpaces.fiberProduct C S hS (G.source ≫ e.hom) (G.target ≫ e.hom) ⟶
      G.arrows => k.hom.app T x) (composablePairsObjectsIso_hom_comp_fst G e)

/-- The comparison of composable pairs, read on a section over a test object along the second
projection. -/
theorem composablePairsObjectsIso_hom_app_snd (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (AlgebraicSpaces.fiberProduct C S hS
      (G.source ≫ e.hom) (G.target ≫ e.hom)).obj.obj T) :
    (fiberProductSnd G.source G.target).hom.app T
        ((composablePairsObjectsIso G e).hom.hom.app T x) =
      (fiberProductSnd (G.source ≫ e.hom) (G.target ≫ e.hom)).hom.app T x :=
  congrArg
    (fun k : AlgebraicSpaces.fiberProduct C S hS (G.source ≫ e.hom) (G.target ≫ e.hom) ⟶
      G.arrows => k.hom.app T x) (composablePairsObjectsIso_hom_comp_snd G e)

/-- **A composable pair for the transported source and target is the same composable pair for
the source and the target of `G`.** Both sides are sections of the pullback of the source and the
target of `G` with the same two projections, namely the two arrows of the given pair. -/
theorem composablePairsObjectsIso_hom_app_composableToPullback
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U'.obj G.arrows.obj
      (G.source ≫ e.hom).hom (G.target ≫ e.hom).hom).obj T)
    (h : G.source.hom.app T p.1.1 = G.target.hom.app T p.1.2) :
    (composablePairsObjectsIso G e).hom.hom.app T
        ((composableToPullback (G.source ≫ e.hom).hom (G.target ≫ e.hom).hom).app T p) =
      (composableToPullback G.source.hom G.target.hom).app T ⟨p.1, h⟩ := by
  refine (pullbackAppEquiv G.source.hom G.target.hom T).injective (Subtype.ext (Prod.ext ?_ ?_))
  · exact ((pullbackAppEquiv_fst G.source.hom G.target.hom T _).trans
      ((composablePairsObjectsIso_hom_app_fst G e T _).trans
        (composableToPullback_app_fst (G.source ≫ e.hom).hom
          (G.target ≫ e.hom).hom T p))).trans
      ((pullbackAppEquiv_fst G.source.hom G.target.hom T _).trans
        (composableToPullback_app_fst G.source.hom G.target.hom T ⟨p.1, h⟩)).symm
  · exact ((pullbackAppEquiv_snd G.source.hom G.target.hom T _).trans
      ((composablePairsObjectsIso_hom_app_snd G e T _).trans
        (composableToPullback_app_snd (G.source ≫ e.hom).hom
          (G.target ≫ e.hom).hom T p))).trans
      ((pullbackAppEquiv_snd G.source.hom G.target.hom T _).trans
        (composableToPullback_app_snd G.source.hom G.target.hom T ⟨p.1, h⟩)).symm

/-! ### The transported groupoid -/

/-- **A groupoid in algebraic spaces transported along an isomorphism of its object space.** For
`G` a groupoid in algebraic spaces over `B` in the sense of **Stacks 043W** and
`e : G.objects ≅ U'` an isomorphism of its space of objects, this is the groupoid in algebraic
spaces over `B` with space of objects `U'`, the *same* space of arrows as `G`, and source and
target those of `G` followed by `e`.

Its composition law is the composition law of `G` read through
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.composablePairsObjectsIso`, the composable pairs
over `U'` being the composable pairs over `G.objects`. -/
@[implicit_reducible]
noncomputable def transportObjects : GroupoidInAlgebraicSpaces C S hS B where
  objects := U'
  arrows := G.arrows
  objectsToBase := e.inv ≫ G.objectsToBase
  arrowsToBase := G.arrowsToBase
  source := G.source ≫ e.hom
  target := G.target ≫ e.hom
  source_over := by
    rw [Category.assoc, Iso.hom_inv_id_assoc]; exact G.source_over
  target_over := by
    rw [Category.assoc, Iso.hom_inv_id_assoc]; exact G.target_over
  comp := (composablePairsObjectsIso G e).hom ≫ G.comp
  comp_over := by
    rw [Category.assoc, G.comp_over, ← Category.assoc]
    exact congrArg (fun k => k ≫ G.arrowsToBase) (composablePairsObjectsIso_hom_comp_fst G e)
  pointwiseGroupoid := by
    intro T
    classical
    have hinv : ∀ x : G.objects.obj.obj T,
        e.inv.hom.app T (e.hom.hom.app T x) = x := fun x =>
      congrArg (fun k : G.objects ⟶ G.objects => k.hom.app T x) e.hom_inv_id
    have hinv' : ∀ y : U'.obj.obj T,
        e.hom.hom.app T (e.inv.hom.app T y) = y := fun y =>
      congrArg (fun k : U' ⟶ U' => k.hom.app T y) e.inv_hom_id
    let eU : U'.obj.obj T ≃ G.objects.obj.obj T :=
      { toFun := fun y => e.inv.hom.app T y
        invFun := fun x => e.hom.hom.app T x
        left_inv := hinv'
        right_inv := hinv }
    refine ⟨Space.transportPointwise eU (Equiv.refl (G.arrows.obj.obj T)) ?_ ?_ ?_
      (G.pointwiseGroupoid T).some⟩
    · intro a
      exact hinv _
    · intro a
      exact hinv _
    · intro p
      have hcond : G.source.hom.app T p.1.1 = G.target.hom.app T p.1.2 := by
        have h2 : e.hom.hom.app T (G.source.hom.app T p.1.1) =
            e.hom.hom.app T (G.target.hom.app T p.1.2) := p.2
        exact (hinv _).symm.trans ((congrArg (e.inv.hom.app T) h2).trans (hinv _))
      exact congrArg (G.comp.hom.app T)
        (composablePairsObjectsIso_hom_app_composableToPullback G e T p hcond)

/-- The space of objects of `transportObjects G e` is `U'`. -/
@[simp]
theorem transportObjects_objects : (transportObjects G e).objects = U' := rfl

/-- The space of arrows of `transportObjects G e` is the space of arrows of `G`. -/
@[simp]
theorem transportObjects_arrows : (transportObjects G e).arrows = G.arrows := rfl

/-- The source morphism of `transportObjects G e` is the source of `G` followed by `e`. -/
@[simp]
theorem transportObjects_source : (transportObjects G e).source = G.source ≫ e.hom := rfl

/-- The target morphism of `transportObjects G e` is the target of `G` followed by `e`. -/
@[simp]
theorem transportObjects_target : (transportObjects G e).target = G.target ≫ e.hom := rfl

/-- The structure morphism of the objects of `transportObjects G e` to `B` is `e⁻¹` followed by
that of `G`. -/
@[simp]
theorem transportObjects_objectsToBase :
    (transportObjects G e).objectsToBase = e.inv ≫ G.objectsToBase := rfl

/-- The structure morphism of the arrows of `transportObjects G e` to `B` is that of `G`. -/
@[simp]
theorem transportObjects_arrowsToBase :
    (transportObjects G e).arrowsToBase = G.arrowsToBase := rfl

/-- The composition law of `transportObjects G e` is that of `G` precomposed with
`composablePairsObjectsIso G e`. -/
theorem transportObjects_comp :
    (transportObjects G e).comp = (composablePairsObjectsIso G e).hom ≫ G.comp := rfl

end Transport

/-! ### Fibre products of isomorphic cospans -/

section Cospan

variable {X₁ X₂ Y X₁' X₂' Y' : AlgebraicSpaces C S hS}
  {f : X₁ ⟶ Y} {g : X₂ ⟶ Y} {f' : X₁' ⟶ Y'} {g' : X₂' ⟶ Y'}
  (a : X₁' ≅ X₁) (b : X₂' ≅ X₂) (c : Y' ≅ Y)
  (hf : f' ≫ c.hom = a.hom ≫ f) (hg : g' ≫ c.hom = b.hom ≫ g)

include hf hg

/-- **The chosen fibre product of a cospan, read as a fibre product of an isomorphic cospan.**
The three comparison isomorphisms turn the cartesian square of
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` for one cospan into a cartesian
square over the other. -/
theorem isPullback_fiberProduct_of_isoCospan :
    IsPullback (fiberProductFst f' g' ≫ a.hom) (fiberProductSnd f' g' ≫ b.hom) f g :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS f' g').of_iso
    (Iso.refl _) a b c (Category.id_comp _).symm (Category.id_comp _).symm hf hg

/-- **Two fibre products of isomorphic cospans are isomorphic.** Given isomorphisms of the three
objects of a cospan of algebraic spaces over `S` which commute with its two morphisms, the two
chosen fibre products are isomorphic: both are cartesian over the same cospan, and a fibre
product is unique up to isomorphism. -/
noncomputable def fiberProductIsoOfIsoCospan :
    AlgebraicSpaces.fiberProduct C S hS f' g' ≅ AlgebraicSpaces.fiberProduct C S hS f g :=
  (isPullback_fiberProduct_of_isoCospan a b c hf hg).isoIsPullback X₁ X₂
    (AlgebraicSpaces.isPullback_fiberProduct C S hS f g)

/-- The comparison of two fibre products of isomorphic cospans, along the first projection. -/
theorem fiberProductIsoOfIsoCospan_hom_comp_fst :
    (fiberProductIsoOfIsoCospan a b c hf hg).hom ≫ fiberProductFst f g =
      fiberProductFst f' g' ≫ a.hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The comparison of two fibre products of isomorphic cospans, along the second projection. -/
theorem fiberProductIsoOfIsoCospan_hom_comp_snd :
    (fiberProductIsoOfIsoCospan a b c hf hg).hom ≫ fiberProductSnd f g =
      fiberProductSnd f' g' ≫ b.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

end Cospan

/-! ### The projections of `(t, s)` and of the diagonal -/

section Projections

variable (H : GroupoidInAlgebraicSpaces C S hS B)

/-- `(t, s)` followed by the first projection of the square of the object space is the target. -/
theorem sourceTarget_comp_fiberProductFst :
    sourceTarget H ≫ fiberProductFst H.objectsToBase H.objectsToBase = H.target :=
  ObjectProperty.hom_ext _ (sourceTarget_target_projection H)

/-- `(t, s)` followed by the second projection of the square of the object space is the
source. -/
theorem sourceTarget_comp_fiberProductSnd :
    sourceTarget H ≫ fiberProductSnd H.objectsToBase H.objectsToBase = H.source :=
  ObjectProperty.hom_ext _ (sourceTarget_source_projection H)

/-- The diagonal followed by the first projection of the square of the object space is the
identity. -/
theorem diagonal_comp_fiberProductFst :
    diagonal H ≫ fiberProductFst H.objectsToBase H.objectsToBase = 𝟙 H.objects :=
  ObjectProperty.hom_ext _ (diagonal_target_projection H)

/-- The diagonal followed by the second projection of the square of the object space is the
identity. -/
theorem diagonal_comp_fiberProductSnd :
    diagonal H ≫ fiberProductSnd H.objectsToBase H.objectsToBase = 𝟙 H.objects :=
  ObjectProperty.hom_ext _ (diagonal_source_projection H)

end Projections

/-! ### The stabilizer of the transported groupoid -/

section Stabilizer

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  {U' : AlgebraicSpaces C S hS} (e : G.objects ≅ U')

/-- **The comparison of the squares of the two object spaces.** Both legs of the square of the
transported object space are the structure morphism of `G` precomposed with the inverse of `e`,
so the two squares are isomorphic. -/
noncomputable def objectPairsTransportIso :
    AlgebraicSpaces.fiberProduct C S hS (e.inv ≫ G.objectsToBase) (e.inv ≫ G.objectsToBase) ≅
      objectPairs G :=
  fiberProductIsoOfIsoCospan e.symm e.symm (Iso.refl B)
    (Category.comp_id _) (Category.comp_id _)

/-- The comparison of the squares of the object spaces, along the first projection. -/
theorem objectPairsTransportIso_hom_comp_fst :
    (objectPairsTransportIso G e).hom ≫ fiberProductFst G.objectsToBase G.objectsToBase =
      fiberProductFst (e.inv ≫ G.objectsToBase) (e.inv ≫ G.objectsToBase) ≫ e.inv :=
  fiberProductIsoOfIsoCospan_hom_comp_fst _ _ _ _ _

/-- The comparison of the squares of the object spaces, along the second projection. -/
theorem objectPairsTransportIso_hom_comp_snd :
    (objectPairsTransportIso G e).hom ≫ fiberProductSnd G.objectsToBase G.objectsToBase =
      fiberProductSnd (e.inv ≫ G.objectsToBase) (e.inv ≫ G.objectsToBase) ≫ e.inv :=
  fiberProductIsoOfIsoCospan_hom_comp_snd _ _ _ _ _

/-- `(t, s)` of the transported groupoid, followed by the first projection of the square of the
transported object space, is the target of `G` followed by `e`. -/
theorem sourceTarget_transportObjects_comp_fiberProductFst :
    sourceTarget (transportObjects G e) ≫
        fiberProductFst (e.inv ≫ G.objectsToBase) (e.inv ≫ G.objectsToBase) =
      G.target ≫ e.hom :=
  sourceTarget_comp_fiberProductFst (transportObjects G e)

/-- `(t, s)` of the transported groupoid, followed by the second projection of the square of the
transported object space, is the source of `G` followed by `e`. -/
theorem sourceTarget_transportObjects_comp_fiberProductSnd :
    sourceTarget (transportObjects G e) ≫
        fiberProductSnd (e.inv ≫ G.objectsToBase) (e.inv ≫ G.objectsToBase) =
      G.source ≫ e.hom :=
  sourceTarget_comp_fiberProductSnd (transportObjects G e)

/-- The diagonal of the transported object space, followed by the first projection of its
square, is the identity. -/
theorem diagonal_transportObjects_comp_fiberProductFst :
    diagonal (transportObjects G e) ≫
        fiberProductFst (e.inv ≫ G.objectsToBase) (e.inv ≫ G.objectsToBase) = 𝟙 U' :=
  diagonal_comp_fiberProductFst (transportObjects G e)

/-- The diagonal of the transported object space, followed by the second projection of its
square, is the identity. -/
theorem diagonal_transportObjects_comp_fiberProductSnd :
    diagonal (transportObjects G e) ≫
        fiberProductSnd (e.inv ≫ G.objectsToBase) (e.inv ≫ G.objectsToBase) = 𝟙 U' :=
  diagonal_comp_fiberProductSnd (transportObjects G e)

/-- The comparison of the squares of the object spaces carries `(t, s)` of the transported
groupoid to `(t, s)` of `G`: both are detected by the target and the source of `G`. -/
theorem sourceTarget_transportObjects :
    sourceTarget (transportObjects G e) ≫ (objectPairsTransportIso G e).hom = sourceTarget G := by
  refine (AlgebraicSpaces.isPullback_fiberProduct C S hS
    G.objectsToBase G.objectsToBase).hom_ext ?_ ?_
  · rw [Category.assoc, objectPairsTransportIso_hom_comp_fst, ← Category.assoc,
      sourceTarget_transportObjects_comp_fiberProductFst,
      sourceTarget_comp_fiberProductFst, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, objectPairsTransportIso_hom_comp_snd, ← Category.assoc,
      sourceTarget_transportObjects_comp_fiberProductSnd,
      sourceTarget_comp_fiberProductSnd, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Postcomposing with a section of `d` after a morphism `u` is the same as `u` itself. -/
private theorem comp_comp_eq_id_comp_of_comp_eq_id {X Y Z : AlgebraicSpaces C S hS}
    (u : Y ⟶ X) (d : X ⟶ Z) (p : Z ⟶ X) (h : d ≫ p = 𝟙 X) : (u ≫ d) ≫ p = 𝟙 Y ≫ u := by
  rw [Category.assoc, h, Category.comp_id, Category.id_comp]

/-- The comparison of the squares of the object spaces carries the diagonal of the transported
object space to the diagonal of `G`, read through `e`. -/
theorem diagonal_transportObjects :
    diagonal (transportObjects G e) ≫ (objectPairsTransportIso G e).hom =
      e.inv ≫ diagonal G := by
  refine (AlgebraicSpaces.isPullback_fiberProduct C S hS
    G.objectsToBase G.objectsToBase).hom_ext ?_ ?_
  · rw [Category.assoc, objectPairsTransportIso_hom_comp_fst, ← Category.assoc,
      diagonal_transportObjects_comp_fiberProductFst]
    exact (comp_comp_eq_id_comp_of_comp_eq_id _ _ _ (diagonal_comp_fiberProductFst G)).symm
  · rw [Category.assoc, objectPairsTransportIso_hom_comp_snd, ← Category.assoc,
      diagonal_transportObjects_comp_fiberProductSnd]
    exact (comp_comp_eq_id_comp_of_comp_eq_id _ _ _ (diagonal_comp_fiberProductSnd G)).symm

/-- Being locally of finite type is invariant under postcomposition with an isomorphism
(**Stacks 03XF**, part (1)). -/
private theorem isLocallyOfFiniteType_comp_iso_hom {X Y Z : AlgebraicSpaces C S hS}
    (f : X ⟶ Y) (e : Y ≅ Z) (hf : Space.IsLocallyOfFiniteType C S hS f.hom) :
    Space.IsLocallyOfFiniteType C S hS (f ≫ e.hom).hom :=
  have : MorphismProperty.RespectsIso
      (fun ⦃X Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (φ : X ⟶ Y) =>
        Space.IsLocallyOfFiniteType C S hS φ) :=
    Space.isLocallyOfFiniteType_respectsIso C S hS
  MorphismProperty.RespectsIso.postcomp
    (fun ⦃X Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (φ : X ⟶ Y) =>
      Space.IsLocallyOfFiniteType C S hS φ)
    ((ObjectProperty.ι (IsAlgebraicSpace C S hS)).mapIso e).hom f.hom hf

/-- **The source of the transported groupoid is locally of finite type when that of `G` is.**
It is the source of `G` followed by an isomorphism, and being locally of finite type is
invariant under that (**Stacks 03XF**, part (1)). -/
theorem isLocallyOfFiniteType_transportObjects_source
    (hs : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    Space.IsLocallyOfFiniteType C S hS (transportObjects G e).source.hom :=
  isLocallyOfFiniteType_comp_iso_hom G.source e hs

/-- The twin of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyOfFiniteType_transportObjects_source`
for the target. -/
theorem isLocallyOfFiniteType_transportObjects_target
    (ht : Space.IsLocallyOfFiniteType C S hS G.target.hom) :
    Space.IsLocallyOfFiniteType C S hS (transportObjects G e).target.hom :=
  isLocallyOfFiniteType_comp_iso_hom G.target e ht

/-- **The stabilizer of the transported groupoid is the stabilizer of `G`.** Both are the fibre
product of `(t, s)` with the diagonal of the object space, and the two cospans are isomorphic by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.objectPairsTransportIso`. -/
noncomputable def stabilizerOverBaseTransportIso :
    stabilizerOverBase (transportObjects G e) ≅ stabilizerOverBase G :=
  fiberProductIsoOfIsoCospan (Iso.refl G.arrows) e.symm (objectPairsTransportIso G e)
    ((sourceTarget_transportObjects G e).trans (Category.id_comp _).symm)
    (diagonal_transportObjects G e)

/-- **Transporting a groupoid along an isomorphism of its object space does not change the
dimension of its stabilizer.** -/
theorem dimension_stabilizerOverBase_transportObjects :
    Space.dimension C S hS (stabilizerOverBase (transportObjects G e)).obj
        (stabilizerOverBase (transportObjects G e)).property =
      Space.dimension C S hS (stabilizerOverBase G).obj (stabilizerOverBase G).property :=
  Space.dimension_eq_of_iso C S hS _ _
    ((ObjectProperty.ι (IsAlgebraicSpace C S hS)).mapIso (stabilizerOverBaseTransportIso G e))

end Stabilizer

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
