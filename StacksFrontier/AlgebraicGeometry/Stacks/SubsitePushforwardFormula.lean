module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSiteFunctor
public import StacksFrontier.CategoryTheory.Sites.PushforwardSections

/-!
# The pushforward formula on the lisse-étale and flat-fppf sites

Let `f : 𝒳 ⟶ 𝒴` be a smooth (respectively flat) 1-morphism of algebraic stacks. By
**Stacks 07AT** it restricts to a continuous and cocontinuous functor `f'` of the lisse-étale
(respectively flat-fppf) sites, hence induces a morphism of topoi whose direct image is
`CategoryTheory.Functor.sheafPushforwardCocontinuous`. For a sheaf `ℋ` on the subsite of `𝒳`
and an object `y` of the subsite of `𝒴`, lying over the scheme `V`, equation 103.15.1.1 of the
source — **Stacks 07AU** — computes its value:

`f'_*ℋ(y) = Γ((V ×_{y, 𝒴} 𝒳)', (pr')^{-1}ℋ)`,

where `(V ×_{y, 𝒴} 𝒳)'` is the full subcategory of the 2-fibre product `V ×_{y, 𝒴} 𝒳` whose
objects have their `𝒳`-component in the subsite, and `pr'` is the restriction of the projection
to `𝒳`. As in **Stacks 07AK** the inverse image along `pr'` is ordinary restriction, so
`(pr')^{-1}ℋ` is `pr'.op ⋙ ℋ`.

## Main definitions

* `CategoryTheory.SubsitePushforward.primedTwoFibreProduct`: the primed 2-fibre product
  `(V ×_{y, 𝒴} 𝒳)'`, the full subcategory of `V ×_{y, 𝒴} 𝒳` cut out by a property of the
  `𝒳`-component.
* `CategoryTheory.SubsitePushforward.primedProjection`: the projection `pr'`.
* `CategoryTheory.SubsitePushforward.subsiteFunctor`: the restriction `f' : 𝒳' ⥤ 𝒴'` of `f` to
  two full subcategories, the shape in which **Stacks 07AT** produces the site functor.
* `AlgebraicGeometry.Stack.LisseEtale.primedTwoFibreProduct`,
  `AlgebraicGeometry.Stack.LisseEtale.primedProjection` and their flat-fppf counterparts: the
  primed 2-fibre product and `pr'` for the two sites of the source.

## Main results

* `CategoryTheory.SubsitePushforward.subsitePushforwardSectionsEquiv`: **Stacks 07AU** for an
  arbitrary pair of full subcategories, at the level of presheaves: the value at `y` of the right
  Kan extension along `f'` is the global sections of `ℋ` restricted to `(V ×_{y, 𝒴} 𝒳)'`.
* `AlgebraicGeometry.Stack.LisseEtale.sheafPrimedPushforwardSectionsEquiv` and
  `AlgebraicGeometry.Stack.FlatFppf.sheafPrimedPushforwardSectionsEquiv`: **Stacks 07AU** for the
  lisse-étale and the flat-fppf site, for the direct image `f'_*` of a sheaf of sets.

## Implementation notes

The source proves 07AU "by the same argument as" the unprimed formula of Stacks 06W6, and the
two statements are not formally the same: the subsites `𝒳'` and `𝒴'` are *not* fibred in
groupoids over the base — they are closed only under the pullbacks appearing in their topology —
so 06W6 does not apply to `f' : 𝒳' ⥤ 𝒴'`. What does apply to 06W6 is the composite
`𝒳' ⥤ 𝒳 ⥤ 𝒴`, whose target is the ambient stack; the argument below therefore factors into two
independent steps.

The first step compares the two right Kan extensions. Because `𝒴'` is a *full* subcategory
containing `y`, the index categories `CostructuredArrow f' y` and `CostructuredArrow (ι ⋙ f) y`
are isomorphic, and the comparison functors
`CategoryTheory.SubsitePushforward.costructuredArrowPost` and
`CategoryTheory.SubsitePushforward.costructuredArrowPre` are mutually inverse on the nose; so
the two Kan extensions agree at `y`
(`CategoryTheory.SubsitePushforward.ranObjEquiv`). This is where fullness of the subsite of `𝒴`
enters, and it is the only place.

The second step is 06W6 for `𝒳' ⥤ 𝒴`, whose 2-fibre product is formed with `𝒳'` in place of
`𝒳`. That category and the primed full subcategory of the ambient 2-fibre product are
isomorphic — `CategoryTheory.SubsitePushforward.subToPrimed` and
`CategoryTheory.SubsitePushforward.primedToSub` are again mutually inverse on the nose — and the
isomorphism commutes strictly with the two projections to `𝒳'`, so compatible families of
sections correspond under `CategoryTheory.Functor.sectionsPrecomp` with no transport.

All three comparisons of sections are therefore `CategoryTheory.Functor.sectionsPrecomp` in both
directions with `rfl` round trips, and the identification of the statement is an `Equiv` rather
than an isomorphism of functors: the two sides are sets attached to `y`, and 06W6 itself is
stated as an `Equiv` for the same reason.

The chosen pullbacks used to represent `y` are those of the *ambient* stack `𝒴`, as in the
source: no stability of the subsite under arbitrary morphisms of schemes is asserted, and none
holds.

Existence of the two right Kan extensions is a hypothesis, written as the instance
`∀ G, L.op.HasPointwiseRightKanExtension G` for the two functors `L` involved. This is the
source's size condition, and it is the same condition
`CategoryTheory.Functor.sheafPushforwardCocontinuous` itself carries; it is a condition on the
sites, not a weakening of the content, and it appears in the same shape in
`AlgebraicGeometry.Space.restrictedDirectImageChartEquiv`. It is stated rather than inferred
because for the sites of **Stacks 06TP**, whose objects and morphisms live in unrelated
universes, inferring it costs more than the typeclass budget allows.

## References

* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AU](https://stacks.math.columbia.edu/tag/07AU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SubsitePushforward

attribute [local implicit_reducible] Functor.Fiber

universe u₁ u₂ u₃ v₁ v₂ v₃ w

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- **Stacks 07AT**, the site functor in the shape used here: the restriction `f' : 𝒳' ⥤ 𝒴'` of
a 1-morphism `f` which carries the objects of a full subcategory of `𝒳` into a full subcategory
of `𝒴`. Composing it with the inclusion of `𝒴'` gives back the inclusion of `𝒳'` followed by
`f`, definitionally. -/
def subsiteFunctor (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
    (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj)) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ f) hPQ

/-- The composite of the restriction with the inclusion of `𝒴'` is the inclusion of `𝒳'`
followed by `f`. -/
lemma subsiteFunctor_comp_ι (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
    (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj)) :
    subsiteFunctor f P hPQ ⋙ Q.ι = P.ι ⋙ f :=
  rfl

section TwoFibreProduct

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳)
  (c : p𝒴.ChoiceOfPullbacks) {Q : ObjectProperty 𝒴} (y : Q.FullSubcategory)

/-- The 2-fibre product `V ×_{y, 𝒴} 𝒳`, where `V` is the object of the base that `y` lies over
and `y` is represented by the chosen pullbacks of the ambient `p𝒴`. -/
abbrev ambientTwoFibreProduct :=
  TwoFibreProductOver (Over.forget (p𝒴.obj y.obj)) p𝒳 p𝒴
    (c.sliceFunctor ⟨y.obj, rfl⟩) f

/-- The property of an object of `V ×_{y, 𝒴} 𝒳` cutting out the primed 2-fibre product: its
`𝒳`-component lies in the subsite. In the source this reads "the induced morphism `W → 𝒳` is
smooth (respectively flat)". -/
abbrev primedProperty : ObjectProperty (ambientTwoFibreProduct p𝒳 p𝒴 f c y) :=
  fun T => P T.y

/-- **The primed 2-fibre product `(V ×_{y, 𝒴} 𝒳)'`.** The full subcategory of `V ×_{y, 𝒴} 𝒳`
whose objects have their `𝒳`-component in the subsite `𝒳'`. -/
abbrev primedTwoFibreProduct :=
  (primedProperty p𝒳 p𝒴 f P c y).FullSubcategory

/-- **The projection `pr' : (V ×_{y, 𝒴} 𝒳)' ⥤ 𝒳'`**, the restriction of the projection of the
2-fibre product to `𝒳`. -/
def primedProjection : primedTwoFibreProduct p𝒳 p𝒴 f P c y ⥤ P.FullSubcategory :=
  P.lift ((primedProperty p𝒳 p𝒴 f P c y).ι ⋙
    TwoFibreProductOver.snd (Over.forget (p𝒴.obj y.obj)) p𝒳 p𝒴
      (c.sliceFunctor ⟨y.obj, rfl⟩) f) (fun z => z.property)

/-- The 2-fibre product `V ×_{y, 𝒴} 𝒳'` formed with the subsite of `𝒳` in place of `𝒳`: the
category to which the unprimed formula of Stacks 06W6 applies, because the composite
`𝒳' ⥤ 𝒳 ⥤ 𝒴` is a 1-morphism over the base with target the ambient stack. -/
abbrev subTwoFibreProduct :=
  TwoFibreProductOver (Over.forget (p𝒴.obj y.obj)) (P.ι ⋙ p𝒳) p𝒴
    (c.sliceFunctor ⟨y.obj, rfl⟩) (P.ι ⋙ f)

/-- The projection `V ×_{y, 𝒴} 𝒳' ⥤ 𝒳'`. -/
abbrev subProjection : subTwoFibreProduct p𝒳 p𝒴 f P c y ⥤ P.FullSubcategory :=
  TwoFibreProductOver.snd (Over.forget (p𝒴.obj y.obj)) (P.ι ⋙ p𝒳) p𝒴
    (c.sliceFunctor ⟨y.obj, rfl⟩) (P.ι ⋙ f)

/-- The 2-fibre product formed with the subsite is the primed full subcategory of the ambient
2-fibre product: forget that the `𝒳`-component lies in the subsite and remember it as a
property. -/
def subToPrimed :
    subTwoFibreProduct p𝒳 p𝒴 f P c y ⥤ primedTwoFibreProduct p𝒳 p𝒴 f P c y where
  obj z :=
    ⟨{ base := z.base
       x := z.x
       y := z.y.obj
       hx := z.hx
       hy := z.hy
       iso := z.iso
       vertical := z.vertical }, z.y.property⟩
  map {z z'} φ :=
    ObjectProperty.homMk
      { hbase := φ.hbase
        a := φ.a
        b := φ.b.hom
        ha := φ.ha
        hb := IsHomLift.of_fac' p𝒳 φ.hbase φ.b.hom z.hy z'.hy (by
          have := φ.hb
          exact IsHomLift.fac' (P.ι ⋙ p𝒳) φ.hbase φ.b)
        w := φ.w }
  map_id z := by
    apply ObjectProperty.hom_ext
    apply TwoFibreProductOver.Hom.ext' <;> rfl
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    apply TwoFibreProductOver.Hom.ext' <;> rfl

/-- The inverse of `CategoryTheory.SubsitePushforward.subToPrimed`: read the property of the
`𝒳`-component as membership of the subsite. -/
def primedToSub :
    primedTwoFibreProduct p𝒳 p𝒴 f P c y ⥤ subTwoFibreProduct p𝒳 p𝒴 f P c y where
  obj z :=
    { base := z.obj.base
      x := z.obj.x
      y := ⟨z.obj.y, z.property⟩
      hx := z.obj.hx
      hy := z.obj.hy
      iso := z.obj.iso
      vertical := z.obj.vertical }
  map {z z'} φ :=
    { hbase := φ.hom.hbase
      a := φ.hom.a
      b := ObjectProperty.homMk (X := ⟨z.obj.y, z.property⟩) (Y := ⟨z'.obj.y, z'.property⟩)
        φ.hom.b
      ha := φ.hom.ha
      hb := IsHomLift.of_fac' (P.ι ⋙ p𝒳) φ.hom.hbase
        (ObjectProperty.homMk (X := ⟨z.obj.y, z.property⟩) (Y := ⟨z'.obj.y, z'.property⟩)
          φ.hom.b) z.obj.hy z'.obj.hy (by
          have := φ.hom.hb
          exact IsHomLift.fac' p𝒳 φ.hom.hbase φ.hom.b)
      w := φ.hom.w }
  map_id z := by apply TwoFibreProductOver.Hom.ext' <;> rfl
  map_comp φ ψ := by apply TwoFibreProductOver.Hom.ext' <;> rfl

/-- The comparison of 2-fibre products commutes strictly with the projections to `𝒳'`. -/
lemma primedToSub_comp_subProjection :
    primedToSub p𝒳 p𝒴 f P c y ⋙ subProjection p𝒳 p𝒴 f P c y =
      primedProjection p𝒳 p𝒴 f P c y :=
  rfl

/-- The inverse comparison also commutes strictly with the projections to `𝒳'`. -/
lemma subToPrimed_comp_primedProjection :
    subToPrimed p𝒳 p𝒴 f P c y ⋙ primedProjection p𝒳 p𝒴 f P c y =
      subProjection p𝒳 p𝒴 f P c y :=
  rfl

/-- Compatible families of sections over `V ×_{y, 𝒴} 𝒳'` are compatible families over the
primed 2-fibre product: the two categories are inverse to one another on the nose and project to
`𝒳'` in the same way. -/
def primedSectionsEquiv (ℋ : (P.FullSubcategory)ᵒᵖ ⥤ Type w) :
    ((subProjection p𝒳 p𝒴 f P c y).op ⋙ ℋ).sections ≃
      ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ ℋ).sections where
  toFun := Functor.sectionsPrecomp (primedToSub p𝒳 p𝒴 f P c y).op
  invFun := Functor.sectionsPrecomp (subToPrimed p𝒳 p𝒴 f P c y).op
  left_inv _ := Subtype.ext (funext fun _ => rfl)
  right_inv _ := Subtype.ext (funext fun _ => rfl)

end TwoFibreProduct

section Index

variable (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
  (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj)) (y : Q.FullSubcategory)

/-- The comparison of index categories: an arrow `f' x' ⟶ y` of the subsite of `𝒴` is an arrow
`f x' ⟶ y` of `𝒴`, because the subsite is a full subcategory. -/
abbrev costructuredArrowPost :
    CostructuredArrow (subsiteFunctor f P hPQ) y ⥤ CostructuredArrow (P.ι ⋙ f) y.obj :=
  CostructuredArrow.post (subsiteFunctor f P hPQ) Q.ι y

/-- The inverse comparison of index categories: an arrow `f x' ⟶ y` of `𝒴` between objects of
the subsite is an arrow of the subsite. -/
def costructuredArrowPre :
    CostructuredArrow (P.ι ⋙ f) y.obj ⥤ CostructuredArrow (subsiteFunctor f P hPQ) y where
  obj z := CostructuredArrow.mk (Y := z.left) (ObjectProperty.homMk (P := Q) z.hom)
  map {z z'} φ := CostructuredArrow.homMk φ.left (ObjectProperty.hom_ext _ (CostructuredArrow.w φ))

/-- Compatible families of sections over the two index categories correspond. -/
def indexSectionsEquiv (ℋ : (P.FullSubcategory)ᵒᵖ ⥤ Type w) :
    ((CostructuredArrow.proj (subsiteFunctor f P hPQ) y).op ⋙ ℋ).sections ≃
      ((CostructuredArrow.proj (P.ι ⋙ f) y.obj).op ⋙ ℋ).sections where
  toFun := Functor.sectionsPrecomp (costructuredArrowPre f P hPQ y).op
  invFun := Functor.sectionsPrecomp (costructuredArrowPost f P hPQ y).op
  left_inv _ := Subtype.ext (funext fun _ => rfl)
  right_inv _ := Subtype.ext (funext fun _ => rfl)

/-- The right Kan extension along the restriction `f' : 𝒳' ⥤ 𝒴'` and the one along the
composite `𝒳' ⥤ 𝒳 ⥤ 𝒴` have the same value at `y`: the index categories of the two pointwise
limits are isomorphic, because the subsite of `𝒴` is a full subcategory containing `y`. -/
def ranObjEquiv (ℋ : (P.FullSubcategory)ᵒᵖ ⥤ Type w)
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
      (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w, (P.ι ⋙ f).op.HasPointwiseRightKanExtension G] :
    ((subsiteFunctor f P hPQ).op.ran.obj ℋ).obj (op y) ≃
      ((P.ι ⋙ f).op.ran.obj ℋ).obj (op y.obj) :=
  ((subsiteFunctor f P hPQ).op.ranObjObjIsoLimit ℋ (op y)).toEquiv.trans
    ((Types.limitEquivSections _).trans
      ((Presheaf.pushforwardCostrSectionsEquiv (subsiteFunctor f P hPQ) y ℋ).trans
        ((indexSectionsEquiv f P hPQ y ℋ).trans
          ((Presheaf.pushforwardCostrSectionsEquiv (P.ι ⋙ f) y.obj ℋ).symm.trans
            ((Types.limitEquivSections _).symm.trans
              (((P.ι ⋙ f).op.ranObjObjIsoLimit ℋ (op y.obj)).symm.toEquiv))))))

end Index

/-- The composite `𝒳' ⥤ 𝒳 ⥤ 𝒴` is a 1-morphism over the base. -/
lemma ι_comp_comp_structure_eq (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳)
    (hf : f ⋙ p𝒴 = p𝒳) : (P.ι ⋙ f) ⋙ p𝒴 = P.ι ⋙ p𝒳 := by
  rw [Functor.assoc, hf]

/-- **Stacks 07AU**, equation 103.15.1.1. Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over a
base `𝒞` with `𝒴` fibred in groupoids, and let `𝒳' ⊆ 𝒳` and `𝒴' ⊆ 𝒴` be full subcategories such
that `f` carries `𝒳'` into `𝒴'`, so that it restricts to `f' : 𝒳' ⥤ 𝒴'`. Then for a presheaf
`ℋ` on `𝒳'` and an object `y` of `𝒴'` lying over `V : 𝒞`,

`f'_*ℋ(y) = Γ((V ×_{y, 𝒴} 𝒳)', (pr')^{-1}ℋ)`,

where `f'_*` is the right Kan extension along `f'.op`, the primed 2-fibre product is the full
subcategory of `V ×_{y, 𝒴} 𝒳` whose objects have their `𝒳`-component in `𝒳'`, and `(pr')^{-1}`
is restriction along the projection `pr'` to `𝒳'`.

This is the source's equation for the lisse-étale and the flat-fppf site: no property of the
subcategories beyond fullness is used, and neither the topologies nor their closure conditions
enter the identification. -/
@[stacks 07AU]
def subsitePushforwardSectionsEquiv (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳)
    {Q : ObjectProperty 𝒴} (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
    (y : Q.FullSubcategory) (ℋ : (P.FullSubcategory)ᵒᵖ ⥤ Type w)
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
      (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w, (P.ι ⋙ f).op.HasPointwiseRightKanExtension G] :
    ((subsiteFunctor f P hPQ).op.ran.obj ℋ).obj (op y) ≃
      Presheaf.globalSections ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ ℋ) :=
  (ranObjEquiv f P hPQ y ℋ).trans
    ((Presheaf.pushforwardSectionsEquiv (P.ι ⋙ p𝒳) p𝒴 (P.ι ⋙ f) h𝒴
        (ι_comp_comp_structure_eq p𝒳 p𝒴 f P hf) c ⟨y.obj, rfl⟩ ℋ).trans
      ((Presheaf.globalSectionsEquivSections
          ((subProjection p𝒳 p𝒴 f P c y).op ⋙ ℋ)).trans
        ((primedSectionsEquiv p𝒳 p𝒴 f P c y ℋ).trans
          (Presheaf.globalSectionsEquivSections
            ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ ℋ)).symm)))

end CategoryTheory.SubsitePushforward

namespace AlgebraicGeometry.Stack

universe u w a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The chosen pullbacks of an algebraic stack, supplied by its fibred-category structure. They
represent an object of the stack by a 1-morphism out of a slice of the base, which is what the
pushforward formula of **Stacks 06W6** needs. These are the pullbacks of the *ambient* stack: the
lisse-étale and flat-fppf subsites are not stable under arbitrary morphisms of schemes, and no
such stability is used below. -/
def ambientChoiceOfPullbacks (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS) :
    𝒴.val.val.p.ChoiceOfPullbacks :=
  letI : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  𝒴.val.val.p.chosenPullbacks

namespace FlatFppf

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

/-- The restriction `f'` of a flat 1-morphism to the flat-fppf sites, as the lift of
`𝒳' ⥤ 𝒳 ⥤ 𝒴` through the flat objects of `𝒴`. This is the functor of **Stacks 07AT**:
`AlgebraicGeometry.Stack.FlatFppf.siteFunctor_eq_primedSiteFunctor`. -/
abbrev primedSiteFunctor : FlatFppf B S hS 𝒳 ⥤ FlatFppf B S hS 𝒴 :=
  SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
    (flatObject_map B S hS f hf)

/-- The site functor of **Stacks 07AT** is the restriction of `f` to the flat objects. -/
lemma siteFunctor_eq_primedSiteFunctor :
    (siteFunctor B S hS f hf).1 = primedSiteFunctor B S hS f hf :=
  rfl

/-- **The primed 2-fibre product `(V ×_{y, 𝒴} 𝒳)'` of the flat-fppf site.** For a flat object
`y` of `𝒴` lying over the scheme `V`, this is the full subcategory of `V ×_{y, 𝒴} 𝒳` whose
objects have a flat `𝒳`-component, i.e. whose induced morphism to `𝒳` is flat. -/
abbrev primedTwoFibreProduct (y : FlatFppf B S hS 𝒴) :=
  SubsitePushforward.primedTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (flatObject B S hS 𝒳.val) (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- **The projection `pr'`** of the primed 2-fibre product to the flat-fppf site of `𝒳`. -/
abbrev primedProjection (y : FlatFppf B S hS 𝒴) :
    primedTwoFibreProduct B S hS f y ⥤ FlatFppf B S hS 𝒳 :=
  SubsitePushforward.primedProjection 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (flatObject B S hS 𝒳.val) (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- **Stacks 07AU, the flat-fppf case at the level of presheaves.** For a flat 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks, a presheaf `ℋ` on the flat-fppf site of `𝒳` and a flat object
`y` of `𝒴` lying over the scheme `V`, the pushforward of `ℋ` along the restriction `f'` of `f` to
the flat-fppf sites — the right Kan extension along `f'.op` — has value at `y` the global
sections of the restriction of `ℋ` to the primed 2-fibre product. -/
def primedPushforwardSectionsEquiv (y : FlatFppf B S hS 𝒴)
    (ℋ : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a)
    [∀ F : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (primedSiteFunctor B S hS f hf).op.HasPointwiseRightKanExtension F]
    [∀ F : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (inclusion B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension F] :
    (((primedSiteFunctor B S hS f hf).op.ran.obj ℋ).obj (op y)) ≃
      Presheaf.globalSections ((primedProjection B S hS f y).op ⋙ ℋ) :=
  SubsitePushforward.subsitePushforwardSectionsEquiv 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)
    𝒴.val.isFiberedInGroupoids f.hom.hom.w (ambientChoiceOfPullbacks B S hS 𝒴) y ℋ

/-- The presheaf underlying the direct image `f'_*ℋ` of a sheaf along the morphism of flat-fppf
topoi is the right Kan extension along `f'.op` of the presheaf underlying `ℋ`. This is what makes
`AlgebraicGeometry.Stack.FlatFppf.primedPushforwardSectionsEquiv` compute `f'_*`. -/
lemma sheafPushforward_obj (ℋ : Sheaf (topology B S hS 𝒳) (Type a))
    [∀ F : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (primedSiteFunctor B S hS f hf).op.HasPointwiseRightKanExtension F] :
    letI : (primedSiteFunctor B S hS f hf).IsCocontinuous
        (topology B S hS 𝒳) (topology B S hS 𝒴) :=
      siteFunctor_isCocontinuous B S hS f hf
    (((primedSiteFunctor B S hS f hf).sheafPushforwardCocontinuous (Type a)
        (topology B S hS 𝒳) (topology B S hS 𝒴)).obj ℋ).obj =
      (primedSiteFunctor B S hS f hf).op.ran.obj ℋ.obj :=
  rfl

/-- **Stacks 07AU, the flat-fppf case**, equation 103.15.1.1. Let `f : 𝒳 ⟶ 𝒴` be a flat
1-morphism of algebraic stacks, let `ℋ` be a sheaf of sets on the flat-fppf site of `𝒳` and let
`y` be a flat object of `𝒴` lying over the scheme `V`. The direct image of `ℋ` along the morphism
of flat-fppf topoi induced by `f` has

`f'_*ℋ(y) = Γ((V ×_{y, 𝒴} 𝒳)', (pr')^{-1}ℋ)`,

the global sections of `ℋ` restricted along the projection `pr'` of the primed 2-fibre product.
The direct image is `CategoryTheory.Functor.sheafPushforwardCocontinuous` along the site functor
of **Stacks 07AT**, whose cocontinuity is
`AlgebraicGeometry.Stack.FlatFppf.siteFunctor_isCocontinuous`. -/
@[stacks 07AU]
def sheafPrimedPushforwardSectionsEquiv (y : FlatFppf B S hS 𝒴)
    (ℋ : Sheaf (topology B S hS 𝒳) (Type a))
    [∀ F : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (primedSiteFunctor B S hS f hf).op.HasPointwiseRightKanExtension F]
    [∀ F : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (inclusion B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension F] :
    letI : (primedSiteFunctor B S hS f hf).IsCocontinuous
        (topology B S hS 𝒳) (topology B S hS 𝒴) :=
      siteFunctor_isCocontinuous B S hS f hf
    ((((primedSiteFunctor B S hS f hf).sheafPushforwardCocontinuous (Type a)
        (topology B S hS 𝒳) (topology B S hS 𝒴)).obj ℋ).obj.obj (op y)) ≃
      Presheaf.globalSections ((primedProjection B S hS f y).op ⋙ ℋ.obj) :=
  primedPushforwardSectionsEquiv B S hS f hf y ℋ.obj

end FlatFppf

namespace LisseEtale

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- The restriction `f'` of a smooth 1-morphism to the lisse-étale sites, as the lift of
`𝒳' ⥤ 𝒳 ⥤ 𝒴` through the smooth objects of `𝒴`. This is the functor of **Stacks 07AT**:
`AlgebraicGeometry.Stack.LisseEtale.siteFunctor_eq_primedSiteFunctor`. -/
abbrev primedSiteFunctor : LisseEtale.{u, w} B S hS 𝒳 ⥤ LisseEtale.{u, w} B S hS 𝒴 :=
  SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
    (smoothObject_map.{u, w} B S hS f hf)

/-- The site functor of **Stacks 07AT** is the restriction of `f` to the smooth objects. -/
lemma siteFunctor_eq_primedSiteFunctor :
    (siteFunctor.{u, w} B S hS f hf).1 = primedSiteFunctor.{u, w} B S hS f hf :=
  rfl

/-- **The primed 2-fibre product `(V ×_{y, 𝒴} 𝒳)'` of the lisse-étale site.** For a smooth object
`y` of `𝒴` lying over the scheme `V`, this is the full subcategory of `V ×_{y, 𝒴} 𝒳` whose
objects have a smooth `𝒳`-component, i.e. whose induced morphism to `𝒳` is smooth. -/
abbrev primedTwoFibreProduct (y : LisseEtale.{u, w} B S hS 𝒴) :=
  SubsitePushforward.primedTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (smoothObject.{u, w} B S hS 𝒳) (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- **The projection `pr'`** of the primed 2-fibre product to the lisse-étale site of `𝒳`. -/
abbrev primedProjection (y : LisseEtale.{u, w} B S hS 𝒴) :
    primedTwoFibreProduct B S hS f y ⥤ LisseEtale.{u, w} B S hS 𝒳 :=
  SubsitePushforward.primedProjection 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (smoothObject.{u, w} B S hS 𝒳) (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- **Stacks 07AU, the lisse-étale case at the level of presheaves.** For a smooth 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks, a presheaf `ℋ` on the lisse-étale site of `𝒳` and a smooth
object `y` of `𝒴` lying over the scheme `V`, the pushforward of `ℋ` along the restriction `f'` of
`f` to the lisse-étale sites — the right Kan extension along `f'.op` — has value at `y` the
global sections of the restriction of `ℋ` to the primed 2-fibre product. -/
def primedPushforwardSectionsEquiv (y : LisseEtale.{u, w} B S hS 𝒴)
    (ℋ : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a)
    [∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (primedSiteFunctor.{u, w} B S hS f hf).op.HasPointwiseRightKanExtension F]
    [∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (inclusion.{u, w} B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension F] :
    (((primedSiteFunctor.{u, w} B S hS f hf).op.ran.obj ℋ).obj (op y)) ≃
      Presheaf.globalSections ((primedProjection B S hS f y).op ⋙ ℋ) :=
  SubsitePushforward.subsitePushforwardSectionsEquiv 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)
    𝒴.val.isFiberedInGroupoids f.hom.hom.w (ambientChoiceOfPullbacks B S hS 𝒴) y ℋ

/-- The presheaf underlying the direct image `f'_*ℋ` of a sheaf along the morphism of lisse-étale
topoi is the right Kan extension along `f'.op` of the presheaf underlying `ℋ`. This is what makes
`AlgebraicGeometry.Stack.LisseEtale.primedPushforwardSectionsEquiv` compute `f'_*`. -/
lemma sheafPushforward_obj (ℋ : Sheaf (topology.{u, w} B S hS 𝒳) (Type a))
    [∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (primedSiteFunctor.{u, w} B S hS f hf).op.HasPointwiseRightKanExtension F] :
    letI : (primedSiteFunctor.{u, w} B S hS f hf).IsCocontinuous
        (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) :=
      siteFunctor_isCocontinuous.{u, w} B S hS f hf
    (((primedSiteFunctor.{u, w} B S hS f hf).sheafPushforwardCocontinuous (Type a)
        (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴)).obj ℋ).obj =
      (primedSiteFunctor.{u, w} B S hS f hf).op.ran.obj ℋ.obj :=
  rfl

/-- **Stacks 07AU, the lisse-étale case**, equation 103.15.1.1. Let `f : 𝒳 ⟶ 𝒴` be a smooth
1-morphism of algebraic stacks, let `ℋ` be a sheaf of sets on the lisse-étale site of `𝒳` and let
`y` be a smooth object of `𝒴` lying over the scheme `V`. The direct image of `ℋ` along the
morphism of lisse-étale topoi induced by `f` has

`f'_*ℋ(y) = Γ((V ×_{y, 𝒴} 𝒳)', (pr')^{-1}ℋ)`,

the global sections of `ℋ` restricted along the projection `pr'` of the primed 2-fibre product.
The direct image is `CategoryTheory.Functor.sheafPushforwardCocontinuous` along the site functor
of **Stacks 07AT**, whose cocontinuity is
`AlgebraicGeometry.Stack.LisseEtale.siteFunctor_isCocontinuous`. -/
@[stacks 07AU]
def sheafPrimedPushforwardSectionsEquiv (y : LisseEtale.{u, w} B S hS 𝒴)
    (ℋ : Sheaf (topology.{u, w} B S hS 𝒳) (Type a))
    [∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (primedSiteFunctor.{u, w} B S hS f hf).op.HasPointwiseRightKanExtension F]
    [∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (inclusion.{u, w} B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension F] :
    letI : (primedSiteFunctor.{u, w} B S hS f hf).IsCocontinuous
        (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) :=
      siteFunctor_isCocontinuous.{u, w} B S hS f hf
    ((((primedSiteFunctor.{u, w} B S hS f hf).sheafPushforwardCocontinuous (Type a)
        (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴)).obj ℋ).obj.obj (op y)) ≃
      Presheaf.globalSections ((primedProjection B S hS f y).op ⋙ ℋ.obj) :=
  primedPushforwardSectionsEquiv B S hS f hf y ℋ.obj

end LisseEtale

end AlgebraicGeometry.Stack
end
