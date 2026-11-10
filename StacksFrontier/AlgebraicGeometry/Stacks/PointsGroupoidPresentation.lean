module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.TwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory

/-!
# The points of a stack presented by a smooth groupoid (Stacks 04XJ)

Let `𝒳` be a category over the big fppf site of `S` which is fibred in groupoids, and let
`𝒳 = [U/R]` be a presentation of it by a smooth groupoid `(U, R, s, t, c)` in algebraic spaces
(Stacks 04TI). Writing `|·|` for the point set of Stacks 04XG, **Stacks 04XJ** says that the image
of `|R| ⟶ |U| × |U|` is an equivalence relation and that `|𝒳|` is the quotient of `|U|` by it.

Both halves are proved for the canonical 1-morphism `p : 𝒮_U ⟶ 𝒳` of the presentation — the
projection `π : 𝒮_U ⟶ [U/R]` of Stacks 044R followed by the presenting equivalence. The image of
`|R| ⟶ |U| × |U|` is exactly the graph of `Setoid.ker |p|`, hence an equivalence relation, and
`|𝒳|` is the quotient of `|U|` by that setoid.

## Main definitions

* `AlgebraicGeometry.Stack.objectSpacePoints` and `AlgebraicGeometry.Stack.arrowSpacePoints`:
  the point sets `|U|` and `|R|` of the two algebraic spaces of a groupoid, read through the
  fibred categories they present.
* `AlgebraicGeometry.Stack.sourcePointsMap`, `AlgebraicGeometry.Stack.targetPointsMap` and
  `AlgebraicGeometry.Stack.quotientStackPointsMap`: the maps `|s|`, `|t|` and `|π|`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.presentingMap`: the 1-morphism `𝒮_U ⟶ 𝒳` of a
  presentation, and `...presentingPointsMap` the map `|U| ⟶ |𝒳|` it induces.
* `AlgebraicGeometry.Stack.GroupoidPresentation.ofSmoothGroupoid`: the tautological presentation
  of the quotient stack of a smooth groupoid.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.range_pointsMap_source_target`: **Stacks 04XJ**,
  the image of `|R| ⟶ |U| × |U|` is the equivalence relation `Setoid.ker |p|`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.pointsQuotientEquivOfPresentation`:
  **Stacks 04XJ**, `|𝒳|` is
  the quotient of `|U|` by that equivalence relation.
* `AlgebraicGeometry.Stack.range_pointsMap_source_target_quotientStack`: the same first half for
  the quotient stack itself, before transport along the presenting equivalence.
* `AlgebraicGeometry.Stack.surjective_pointsMap_quotientStackProjection`: `|U| ⟶ |[U/R]|` is
  surjective.
* `AlgebraicGeometry.Stack.bijective_pointsMap_spacePointMap`: the point sets used for `|U|` and
  `|R|` are the point sets of Stacks 03BT of the object and arrow algebraic spaces.

## Implementation notes

**Nothing is assumed beyond the presentation.** Algebraicity of `𝒳` — which the source assumes,
since it states the lemma for an algebraic stack — is not used, and neither is the smoothness of
the presenting groupoid, which the structure of Stacks 04TI carries. The hypotheses are that bare
structure together with `𝒳` being fibred in groupoids, so the statements are more general than the
source's in the two ways its proof turns out not to need.

**Where the source's citations come from.** The source cites Stacks 04X0 (the projection
`π : 𝒮_U ⟶ [U/R]` is smooth and surjective) and Stacks 04XI (a 1-morphism representable by
algebraic spaces is surjective exactly when it is surjective on points) to get surjectivity of
`|U| ⟶ |[U/R]|`. That route needs representability of `π`, which is not available here; instead
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_quotientStackProjection_of_presentation`
reads the local essential
surjectivity of `π` (Stacks 044X, proved as
`AlgebraicGeometry.Stack.localEssSurj_quotientStackProjectionHom`) at a field spectrum, using
`AlgebraicGeometry.Stack.exists_isFieldObject_arrow_of_mem_topology` to find a field object in the
covering sieve. That is surjectivity on objects in the sense of Stacks 06D4, which gives
surjectivity on points with no representability and no smoothness. The other citation,
Stacks 04M9, is used as it stands: `AlgebraicGeometry.Stack.quotientStack_twoFibreProduct` says
the square of `π` with itself is 2-cartesian, and
`AlgebraicGeometry.Stack.exists_coneHom_quotientStackSelfSquare` extracts from it the comparison
1-morphism from the canonical 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U` to `𝒮_R`.

**Why three results are needed in universe-general form.** The quotient stack of Stacks 044Q
lives at morphism universe `u + 1`, being a stackification, and so does
`AlgebraicGeometry.Stack.liftedFibredCategory`, which exists precisely to put `𝒮_U` and `𝒮_R`
there too. The lemma `AlgebraicGeometry.Stack.pointsMap_surjective_of_isSurjectiveOnObjects` is
stated for `AlgebraicGeometry.Stack.AlgebraicStacks`, whose morphism universe is `u`, and the
equivalence `AlgebraicGeometry.Stack.pointsEquivOfBasedEquivalence` for
`CategoryTheory.BasedCategory.{u, u + 1}`; neither applies. Their universe-general counterparts
here are `AlgebraicGeometry.Stack.surjective_pointsMap_of_isSurjectiveOnObjects` and
`AlgebraicGeometry.Stack.bijective_pointsMap_of_basedEquivalence`. The third,
`AlgebraicGeometry.Stack.exists_point_of_coneHom'`, is the universe-general companion of
`AlgebraicGeometry.Stack.exists_point_of_coneHom`, which is its instance at
`.{u, u, u + 1}`.

**What the 2-cartesian square is used through.** The 2-fibre product of Stacks 04M9 is terminal in
the 2-category of *stacks* in groupoids, so the canonical 2-fibre product of `π` with itself has
to be presented as a square there: that is
`AlgebraicGeometry.Stack.quotientStackSelfSquareStack`, whose apex is a stack in groupoids by
`AlgebraicGeometry.Stack.relativeProjection_isStackInGroupoids`. Only a cone *out of* the
canonical square is wanted, so no transport of terminality between 2-categories is needed.

## References

* [Stacks Project, Tag 03BT](https://stacks.math.columbia.edu/tag/03BT)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XJ](https://stacks.math.columbia.edu/tag/04XJ)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t v' t'

/-! ### Two results about points, in universe-general form -/

/-- **Surjectivity on objects implies surjectivity on points.** A 1-morphism of categories over
the big fppf site of `S` which is surjective on objects in the sense of Stacks 06D4 induces a
surjection on the point sets of Stacks 04XG.

A representative of the given point is an object over a field spectrum; surjectivity on objects
lifts it after a field extension, and the lift is a field-valued point of the source whose image
dominates the chosen representative. -/
theorem surjective_pointsMap_of_isSurjectiveOnObjects
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)} (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ᵇ 𝒴)
    (h : IsSurjectiveOnObjects B S hS 𝒳.p 𝒴.p F.toFunctor) :
    Function.Surjective (pointsMap B S hS 𝒳 h𝒳 h𝒴 F) := by
  intro z
  obtain ⟨q, hq⟩ := Quotient.exists_rep z
  obtain ⟨V, hV, g, x, hx, α, hα⟩ := h q.base ⟨q.carrier, q.field, ⟨q.isSpec⟩⟩ q.obj q.over
  obtain ⟨k, hk, ⟨eV⟩⟩ := hV
  let _ : Field k := hk
  let p : FieldValuedPoint B S hS 𝒳 :=
    { carrier := k, field := hk, base := V, isSpec := eV, obj := x, «over» := hx }
  refine ⟨pointClass B S hS 𝒳 h𝒳 p, ?_⟩
  rw [pointsMap_class, ← hq]
  exact (class_eq_class_iff_hasCommonExtension B S hS 𝒴 h𝒴
    (fieldValuedPointMap B S hS 𝒳 F p) q).2
    ⟨fieldValuedPointMap B S hS 𝒳 F p, ⟨⟨𝟙 _⟩, ⟨by simpa [fieldValuedPointMap, p] using α⟩⟩⟩

/-- If a composite of 1-morphisms is 2-morphic to the identity, the composite of the induced maps
on points is the identity. -/
private theorem pointsMap_comp_eq_self_of_basedNatTrans
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)} (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴 ⥤ᵇ 𝒳} (η : BasedNatTrans (F.comp G) (BasedFunctor.id 𝒳))
    (z : points B S hS 𝒳 h𝒳) :
    pointsMap B S hS 𝒴 h𝒴 h𝒳 G (pointsMap B S hS 𝒳 h𝒳 h𝒴 F z) = z := by
  rw [pointsMap_comp, pointsMap_eq_of_basedNatTrans B S hS 𝒳 h𝒳 h𝒳 η]
  induction z using Quotient.inductionOn with
  | h q => rfl

/-- **An equivalence of categories over the big fppf site of `S` is a bijection on points.** The
two composites are 2-isomorphic to the identities, and 2-isomorphic 1-morphisms induce the same
map on points. -/
theorem bijective_pointsMap_of_basedEquivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)} (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (e : BasedCategory.Equivalence 𝒳 𝒴) :
    Function.Bijective (pointsMap B S hS 𝒳 h𝒳 h𝒴 e.functor) := by
  have hleft : ∀ z, pointsMap B S hS 𝒴 h𝒴 h𝒳 e.inverse
      (pointsMap B S hS 𝒳 h𝒳 h𝒴 e.functor z) = z :=
    pointsMap_comp_eq_self_of_basedNatTrans B S hS h𝒳 h𝒴 e.unitIso.hom
  exact ⟨fun x y hxy ↦ ((hleft x).symm.trans (congrArg _ hxy)).trans (hleft y),
    fun y ↦ ⟨_, pointsMap_comp_eq_self_of_basedNatTrans B S hS h𝒴 h𝒳 e.counitIso.hom y⟩⟩

/-! ### The points of a quotient stack -/

section Quotient

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- The lifted fibred category of an algebraic space is fibred in groupoids. -/
theorem isFiberedInGroupoids_liftedFibredCategory (X : AlgebraicSpaces C S hS) :
    (liftedFibredCategory X).p.IsFiberedInGroupoids :=
  (isStackInGroupoids_liftedFibredCategory.{u, u} X).isFiberedInGroupoids

/-- The points `|U|` of the object space of a groupoid in algebraic spaces, read as the points of
the fibred category it presents. -/
noncomputable abbrev objectSpacePoints (G : GroupoidInAlgebraicSpaces C S hS A) :=
  points C S hS (liftedFibredCategory G.objects)
    (isFiberedInGroupoids_liftedFibredCategory G.objects)

/-- The points `|R|` of the arrow space of a groupoid in algebraic spaces, read as the points of
the fibred category it presents. -/
noncomputable abbrev arrowSpacePoints (G : GroupoidInAlgebraicSpaces C S hS A) :=
  points C S hS (liftedFibredCategory G.arrows)
    (isFiberedInGroupoids_liftedFibredCategory G.arrows)

/-- The map `|s| : |R| ⟶ |U|` induced by the source morphism of a groupoid. -/
noncomputable abbrev sourcePointsMap (G : GroupoidInAlgebraicSpaces C S hS A) :
    arrowSpacePoints G → objectSpacePoints G :=
  pointsMap C S hS (liftedFibredCategory G.arrows) _ _ (liftedAssociatedMap G.source)

/-- The map `|t| : |R| ⟶ |U|` induced by the target morphism of a groupoid. -/
noncomputable abbrev targetPointsMap (G : GroupoidInAlgebraicSpaces C S hS A) :
    arrowSpacePoints G → objectSpacePoints G :=
  pointsMap C S hS (liftedFibredCategory G.arrows) _ _ (liftedAssociatedMap G.target)

/-- The map `|π| : |U| ⟶ |[U/R]|` induced by the canonical projection of Stacks 044R. -/
noncomputable abbrev quotientStackPointsMap (G : GroupoidInAlgebraicSpaces C S hS A) :
    objectSpacePoints G →
      points C S hS (quotientStack G) (isFiberedInGroupoids_quotientStack G) :=
  pointsMap C S hS (liftedFibredCategory G.objects) _ _ (liftedQuotientStackProjection G)

/-- The universe lift of the fibred category of an algebraic space is an equivalence over the
site: the two composites are the identity functor on the nose. -/
def liftedFibredCategoryEquivalence (X : AlgebraicSpaces C S hS) :
    BasedCategory.Equivalence (fibredCategory C S hS X.obj).val (liftedFibredCategory X) where
  functor := liftedFibredCategoryUp X
  inverse := liftedFibredCategoryDown X
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- **The point sets used for `|U|` and `|R|` are the point sets of the algebraic spaces.** The
points of an algebraic space in the sense of Stacks 03BT are the points of its category of
elements (Stacks 04XL, `AlgebraicGeometry.Stack.spacePointMap_id_bijective`), and the universe
lift that puts that category at the morphism universe of the quotient stack is an equivalence
over the site, hence bijective on points. -/
theorem bijective_pointsMap_spacePointMap (X : AlgebraicSpaces C S hS) :
    Function.Bijective (pointsMap C S hS (fibredCategory C S hS X.obj).val
        (fibredCategory C S hS X.obj).property
        (isFiberedInGroupoids_liftedFibredCategory X) (liftedFibredCategoryUp X) ∘
      spacePointMap C S hS X.obj (fibredCategory C S hS X.obj)
        (BasedFunctor.id (fibredCategory C S hS X.obj).val)) :=
  (bijective_pointsMap_of_basedEquivalence C S hS (fibredCategory C S hS X.obj).property
      (isFiberedInGroupoids_liftedFibredCategory X)
      (liftedFibredCategoryEquivalence X)).comp
    (spacePointMap_id_bijective C S hS X.obj)

/-- **The canonical projection `π : 𝒮_U ⟶ [U/R]` is surjective on objects**, in the sense of
Stacks 06D4: every object of `[U/R]` over the spectrum of a field acquires a lift to `𝒮_U` after a
field extension.

The projection is locally essentially surjective (Stacks 044X), because `[U/R]` is the
stackification of the pointwise groupoid fibration; a covering sieve of a field spectrum contains
an arrow out of another field spectrum, and the lift over that arrow is the required one. No
hypothesis on the groupoid is needed. -/
theorem isSurjectiveOnObjects_quotientStackProjection_of_presentation
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    IsSurjectiveOnObjects C S hS (liftedFibredCategory G.objects).p (quotientStack G).p
      (liftedQuotientStackProjection G).toFunctor := by
  intro U hU y hy
  obtain ⟨R, hR, hcov⟩ := localEssSurj_quotientStackProjectionHom G U ⟨y, hy⟩
  obtain ⟨V, g, hV, hgR⟩ := exists_isFieldObject_arrow_of_mem_topology C S hS hU hR
  obtain ⟨x, ψ, hψ⟩ := hcov hgR
  have hψ' : (quotientStack G).p.IsHomLift g ψ := hψ
  exact ⟨V, hV, g, x, (BasedFunctor.w_obj (liftedQuotientStackProjection G) x).symm.trans
    (@IsHomLift.domain_eq _ _ _ _ (quotientStack G).p _ _ _ _ g ψ hψ'), ψ, hψ'⟩

/-- **The map `|U| ⟶ |[U/R]|` is surjective.** This is the conclusion the source draws from
Stacks 04X0 and Stacks 04XI; here it comes from surjectivity on objects, so neither
representability of the projection nor smoothness of the groupoid is used. -/
theorem surjective_pointsMap_quotientStackProjection
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    Function.Surjective (quotientStackPointsMap G) :=
  surjective_pointsMap_of_isSurjectiveOnObjects C S hS _ _ _
    (isSurjectiveOnObjects_quotientStackProjection_of_presentation G)

/-- The canonical 2-fibre product square `𝒮_U ×_{[U/R]} 𝒮_U` of the quotient-stack projection
with itself, in the 2-category of categories fibred in groupoids. -/
noncomputable abbrev quotientStackSelfSquare (G : GroupoidInAlgebraicSpaces C S hS A) :
    Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
    (quotientStackProjectionHom G) (quotientStackProjectionHom G)

/-- The square `AlgebraicGeometry.Stack.quotientStackSelfSquare`, read in the 2-category of stacks
in groupoids: its apex is a stack in groupoids by
`AlgebraicGeometry.Stack.relativeProjection_isStackInGroupoids`, and its legs and filler are
those of the square of categories fibred in groupoids. -/
noncomputable def quotientStackSelfSquareStack (G : GroupoidInAlgebraicSpaces C S hS A) :
    let J := BigFppfOver.topology C S hS
    let U : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨liftedFibredCategory G.objects, isStackInGroupoids_liftedFibredCategory G.objects⟩
    let Q : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨quotientStack G, isStackInGroupoids_quotientStack G⟩
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G) : U ⟶ Q)
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G) : U ⟶ Q) := by
  let e : BasedFunctor.comp (quotientStackSelfSquare G).fst.hom
        (liftedQuotientStackProjection G) ≅
      BasedFunctor.comp (quotientStackSelfSquare G).snd.hom
        (liftedQuotientStackProjection G) :=
    Bicategory.InducedBicategory.isoHom (quotientStackSelfSquare G).iso
  exact
    { pt := ⟨(quotientStackSelfSquare G).pt.val, relativeProjection_isStackInGroupoids G⟩
      fst := Bicategory.InducedBicategory.mkHom (quotientStackSelfSquare G).fst.hom
      snd := Bicategory.InducedBicategory.mkHom (quotientStackSelfSquare G).snd.hom
      iso := Bicategory.InducedBicategory.isoMk e }

attribute [local implicit_reducible] StackInGroupoids.bicategory
  Bicategory.InducedBicategory Bicategory.InducedBicategory.forget
  BasedNatTrans.forgetful

/-- **Stacks 04M9 as a cone morphism.** The canonical 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U` receives
a 1-morphism to `𝒮_R` carrying the two projections to the source and target maps of the groupoid,
up to 2-isomorphism.

This is terminality of `AlgebraicGeometry.Stack.quotientStackSquare` in the 2-category of
2-commutative squares of stacks in groupoids, applied to
`AlgebraicGeometry.Stack.quotientStackSelfSquareStack`. -/
theorem exists_coneHom_quotientStackSelfSquare (G : GroupoidInAlgebraicSpaces C S hS A) :
    ∃ k : (quotientStackSelfSquare G).pt.val ⥤ᵇ liftedFibredCategory G.arrows,
      Nonempty (BasedNatTrans (quotientStackSelfSquare G).fst.hom
        (BasedFunctor.comp k (liftedAssociatedMap G.source))) ∧
      Nonempty (BasedNatTrans (quotientStackSelfSquare G).snd.hom
        (BasedFunctor.comp k (liftedAssociatedMap G.target))) := by
  classical
  obtain ⟨α, -⟩ := Quotient.exists_rep
    ((quotientStack_twoFibreProduct.{u, u} G).from (quotientStackSelfSquareStack.{u, u} G))
  exact ⟨α.hom.hom, ⟨α.isoFst.hom.hom⟩, ⟨α.isoSnd.hom.hom⟩⟩

/-- **Stacks 04XH for the canonical self-square of `π`.** Two points of `|U|` with the same image
in `|[U/R]|` lift to a point of the canonical 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U`. -/
theorem exists_point_quotientStackSelfSquare (G : GroupoidInAlgebraicSpaces C S hS A)
    (z x : objectSpacePoints G)
    (h : quotientStackPointsMap G z = quotientStackPointsMap G x) :
    ∃ q : points C S hS (quotientStackSelfSquare G).pt.val
        (quotientStackSelfSquare G).pt.property,
      pointsMap C S hS (quotientStackSelfSquare G).pt.val _ _
          (quotientStackSelfSquare G).fst.hom q = z ∧
        pointsMap C S hS (quotientStackSelfSquare G).pt.val _ _
          (quotientStackSelfSquare G).snd.hom q = x :=
  exists_point_of_coneHom'.{u, u + 1, u + 1} C S hS (quotientStackSelfSquare G) (𝟙 _)
    (Bicategory.leftUnitor (quotientStackSelfSquare G).fst).inv
    (Bicategory.leftUnitor (quotientStackSelfSquare G).snd).inv z x h

/-- **The image of `|R| ⟶ |U| × |U|` is the set of pairs of points of `|U|` with the same image in
`|[U/R]|`.** One inclusion is the 2-commutativity of the source-target square over the quotient
stack (Stacks 044S); the other combines Stacks 04XH for the canonical 2-fibre product with the
comparison 1-morphism of Stacks 04M9. -/
theorem range_pointsMap_source_target_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    Set.range (fun r : arrowSpacePoints G ↦ (sourcePointsMap G r, targetPointsMap G r)) =
      {q : objectSpacePoints G × objectSpacePoints G |
        quotientStackPointsMap G q.1 = quotientStackPointsMap G q.2} := by
  apply Set.eq_of_subset_of_subset
  · rintro q ⟨r, rfl⟩
    simp only [Set.mem_ofPred_eq, quotientStackPointsMap, sourcePointsMap, targetPointsMap]
    rw [pointsMap_comp, pointsMap_comp,
      pointsMap_eq_of_basedNatTrans C S hS (liftedFibredCategory G.arrows)
        (isFiberedInGroupoids_liftedFibredCategory G.arrows)
        (isFiberedInGroupoids_quotientStack G) (liftedQuotientStackTwoArrow G)]
  · rintro ⟨u₁, u₂⟩ h
    obtain ⟨q, hq₁, hq₂⟩ := exists_point_quotientStackSelfSquare G u₁ u₂ h
    obtain ⟨k, ⟨ηfst⟩, ⟨ηsnd⟩⟩ := exists_coneHom_quotientStackSelfSquare G
    have key : ∀ {f : liftedFibredCategory G.arrows ⥤ᵇ liftedFibredCategory G.objects}
        {a : (quotientStackSelfSquare G).pt.val ⥤ᵇ liftedFibredCategory G.objects} {u},
        BasedNatTrans a (BasedFunctor.comp k f) → pointsMap C S hS _ _ _ a q = u →
        pointsMap C S hS _ _ _ f
          (pointsMap C S hS _ _ (isFiberedInGroupoids_liftedFibredCategory G.arrows) k q) =
          u := fun η h => by
      rw [pointsMap_comp]
      exact (congrFun (pointsMap_eq_of_basedNatTrans C S hS
        (quotientStackSelfSquare G).pt.val (quotientStackSelfSquare G).pt.property
        (isFiberedInGroupoids_liftedFibredCategory G.objects) η).symm q).trans h
    exact ⟨_, Prod.ext (key ηfst hq₁) (key ηsnd hq₂)⟩

end Quotient

/-! ### The points of a stack with a presentation -/

namespace GroupoidPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}

/-- **The tautological presentation of the quotient stack of a smooth groupoid**, which exhibits
`AlgebraicGeometry.Stack.GroupoidPresentation` as a satisfiable hypothesis: the groupoid presents
its own quotient stack, through the identity equivalence. -/
noncomputable def ofSmoothGroupoid
    (G : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS))
    (hG : GroupoidInAlgebraicSpaces.IsSmooth B S hS G) :
    GroupoidPresentation B S hS (quotientStack G) where
  groupoid := G
  smooth := hG
  equivalence := StacksRepresentableCFG.EquivalenceOver.refl _

/-- The presenting 1-morphism `p : 𝒮_U ⟶ 𝒳` of a presentation: the canonical projection
`π : 𝒮_U ⟶ [U/R]` of Stacks 044R followed by the presenting equivalence `[U/R] ⟶ 𝒳`. -/
noncomputable def presentingMap (P : GroupoidPresentation B S hS 𝒳) :
    liftedFibredCategory P.groupoid.objects ⥤ᵇ 𝒳 :=
  BasedFunctor.comp (liftedQuotientStackProjection P.groupoid) P.basedFunctor

/-- The map `|p| : |U| ⟶ |𝒳|` induced by the presenting 1-morphism of a presentation. -/
noncomputable abbrev presentingPointsMap (P : GroupoidPresentation B S hS 𝒳)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) :
    objectSpacePoints P.groupoid → points B S hS 𝒳 h𝒳 :=
  pointsMap B S hS (liftedFibredCategory P.groupoid.objects) _ h𝒳 P.presentingMap

/-- The presenting equivalence of a presentation induces a bijection `|[U/R]| ⟶ |𝒳|`. -/
theorem bijective_pointsMap_basedFunctor (P : GroupoidPresentation B S hS 𝒳)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) :
    Function.Bijective (pointsMap B S hS (quotientStack P.groupoid)
      (isFiberedInGroupoids_quotientStack P.groupoid) h𝒳 P.basedFunctor) :=
  bijective_pointsMap_of_basedEquivalence B S hS
    (isFiberedInGroupoids_quotientStack P.groupoid) h𝒳 P.equivalence.toBasedEquivalence

/-- The map `|p| : |U| ⟶ |𝒳|` factors as `|π|` followed by the bijection `|[U/R]| ⟶ |𝒳|`. -/
theorem presentingPointsMap_eq (P : GroupoidPresentation B S hS 𝒳)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (z : objectSpacePoints P.groupoid) :
    P.presentingPointsMap h𝒳 z =
      pointsMap B S hS (quotientStack P.groupoid)
        (isFiberedInGroupoids_quotientStack P.groupoid) h𝒳 P.basedFunctor
        (quotientStackPointsMap P.groupoid z) :=
  (pointsMap_comp B S hS (liftedFibredCategory P.groupoid.objects)
    (isFiberedInGroupoids_liftedFibredCategory P.groupoid.objects)
    (isFiberedInGroupoids_quotientStack P.groupoid) h𝒳
    (liftedQuotientStackProjection P.groupoid) P.basedFunctor z).symm

/-- The map `|p| : |U| ⟶ |𝒳|` of a presentation is surjective. -/
theorem surjective_presentingPointsMap (P : GroupoidPresentation B S hS 𝒳)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) :
    Function.Surjective (P.presentingPointsMap h𝒳) := by
  intro y
  obtain ⟨w, hw⟩ := (P.bijective_pointsMap_basedFunctor h𝒳).2 y
  obtain ⟨z, hz⟩ := surjective_pointsMap_quotientStackProjection P.groupoid w
  exact ⟨z, by rw [P.presentingPointsMap_eq h𝒳, hz, hw]⟩

/-- **Stacks 04XJ, the equivalence relation.** Let `𝒳 = [U/R]` be a presentation of a category
`𝒳` over the big fppf site of `S` which is fibred in groupoids. Then the image of
`|R| ⟶ |U| × |U|` is an equivalence relation on `|U|`, namely the kernel of the map
`|p| : |U| ⟶ |𝒳|` induced by the presenting 1-morphism. -/
@[stacks 04XJ "part 1: the image of |R| → |U| × |U| is an equivalence relation"]
theorem range_pointsMap_source_target (P : GroupoidPresentation B S hS 𝒳)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) :
    Set.range (fun r : arrowSpacePoints P.groupoid ↦
        (sourcePointsMap P.groupoid r, targetPointsMap P.groupoid r)) =
      {q : objectSpacePoints P.groupoid × objectSpacePoints P.groupoid |
        (Setoid.ker (P.presentingPointsMap h𝒳)).r q.1 q.2} := by
  rw [range_pointsMap_source_target_quotientStack P.groupoid]
  ext ⟨u₁, u₂⟩
  change quotientStackPointsMap P.groupoid u₁ = quotientStackPointsMap P.groupoid u₂ ↔
    P.presentingPointsMap h𝒳 u₁ = P.presentingPointsMap h𝒳 u₂
  rw [P.presentingPointsMap_eq h𝒳, P.presentingPointsMap_eq h𝒳,
    (P.bijective_pointsMap_basedFunctor h𝒳).1.eq_iff]

/-- **Stacks 04XJ, the quotient.** Let `𝒳 = [U/R]` be a presentation of a category `𝒳` over the
big fppf site of `S` which is fibred in groupoids. Then `|𝒳|` is the quotient of `|U|` by the
equivalence relation of
`AlgebraicGeometry.Stack.GroupoidPresentation.range_pointsMap_source_target`, the image of
`|R| ⟶ |U| × |U|`. -/
@[stacks 04XJ "part 2: |X| is the quotient of |U| by that relation"]
noncomputable def pointsQuotientEquivOfPresentation (P : GroupoidPresentation B S hS 𝒳)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) :
    Quotient (Setoid.ker (P.presentingPointsMap h𝒳)) ≃ points B S hS 𝒳 h𝒳 :=
  Setoid.quotientKerEquivOfSurjective _ (P.surjective_presentingPointsMap h𝒳)

end GroupoidPresentation

end AlgebraicGeometry.Stack

end
