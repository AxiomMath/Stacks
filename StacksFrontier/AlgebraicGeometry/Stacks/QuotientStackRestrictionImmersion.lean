module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid

/-!
# The quotient stack of a restricted groupoid, and the immersion of Stacks 04YN

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, and let `Z` be an invariant subspace of its space of objects in the sense of
Stacks 044F. Stacks 04YN states that `[Z/R_Z] ⟶ [U/R]` is an immersion of algebraic stacks, open
respectively closed when `Z` is. This file reads the 1-morphism of quotient stacks of Stacks 046Q,
`AlgebraicGeometry.Stack.quotientStackMap`, as a 1-morphism of categories fibred in groupoids,
and proves the descent step of the source's proof: a relative property of the 1-morphism follows
from its representability and an identification of one of its base changes along the projection
`S_U ⟶ [U/R]`. For `[Z/R_Z] ⟶ [U/R]` those two inputs are Stacks 04ZP and Stacks 04ZN, and
`StacksFrontier.AlgebraicGeometry.Stacks.InvariantSubspaceQuotientImmersion` supplies them.

## Main definitions

* `CategoryTheory.strongTransOfNatTrans`, `CategoryTheory.presheafOfCategoriesMap` and
  `CategoryTheory.presheafOfGroupoidsMap`: functoriality of the constructions of Stacks 02XV and
  Stacks 0049 in the presheaf.
* `Deformation.GroupoidInFunctors.evaluationNatTrans`: a morphism of groupoids in functors
  (Stacks 06K3) induces a natural transformation of the groupoid-valued functors their
  evaluations assemble into.
* `AlgebraicGeometry.Stack.prestackToQuotientStack` and
  `AlgebraicGeometry.Stack.quotientStackMapFunctor`: the 1-morphism from the pointwise groupoid
  presentation of one groupoid into the quotient stack of another, and its extension across the
  stackification of the source (Stacks 0436), as bare functors.
* `AlgebraicGeometry.Stack.quotientStackMapHom`: the 1-morphism of quotient stacks induced by a
  morphism of groupoids, as a 1-morphism of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackMapHom_of_representingMap`: for a
  property of morphisms of algebraic spaces over `S` stable under base change and local on the
  target for the fppf precoverage, the induced 1-morphism of quotient stacks has the relative
  property of Stacks 03YK as soon as the base change of it along the projection of the target is
  represented by a morphism of algebraic spaces with that property.
* `AlgebraicGeometry.Stack.isImmersion_quotientStack_restrict_invariant`,
  `AlgebraicGeometry.Stack.isOpenImmersion_quotientStack_restrict_invariant` and
  `AlgebraicGeometry.Stack.isClosedImmersion_quotientStack_restrict_invariant`: the three
  conclusions of Stacks 04YN in the sense of Stacks 04XB, from an explicit identification of one
  base change of the 1-morphism and its representability. The forms with those inputs proved are
  in `StacksFrontier.AlgebraicGeometry.Stacks.InvariantSubspaceQuotientImmersion`.

## Implementation notes

The descent step is Stacks 045D (`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange`) and
not Stacks 04XD (`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap_of_fppf`),
although Stacks 04YN cites the latter. The reason is a universe pin rather than mathematics:
Stacks 04XD is stated for `CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, whereas a
quotient stack has its morphisms in `u + 1` — the reason
`AlgebraicGeometry.Stack.quotientStackProjectionHom` lifts the hom universe of the object space —
so Stacks 04XD does not apply to a 1-morphism of quotient stacks as it stands. Stacks 045D is
stated at independent universes and does, and
`AlgebraicGeometry.Stack.hasRelativeProperty_fst_of_isTwoFibreProduct_representingMap` supplies
its hypothesis on the leg from the represented square, which is the content Stacks 04XD would have
contributed.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04YN](https://stacks.math.columbia.edu/tag/04YN)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open CategoryTheory

universe u v w t v₁ u₁ u₂ v₂

section StrongTransOfNatTrans

open CategoryTheory.Pseudofunctor Bicategory
open scoped Pseudofunctor.StrongTrans

attribute [local implicit_reducible] Cat.category StrictBicategory.category
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc

namespace CategoryTheory

/-- A natural transformation of `Cat`-valued functors on a 1-category, read as a strong
transformation of the associated pseudofunctors on the locally discrete bicategory. The components
are those of the natural transformation, and the strong naturality constraint is the isomorphism
coming from its naturality square, which in `Cat` is an equality. -/
noncomputable def strongTransOfNatTrans {I : Type u₁} [Category.{v₁} I]
    {F G : I ⥤ Cat.{v₂, u₂}} (η : F ⟶ G) :
    F.toPseudofunctor' ⟶ G.toPseudofunctor' where
  app a := η.app a.as
  naturality {a b} f := eqToIso (by
    obtain ⟨f⟩ := f
    simp only [Functor.toPseudofunctor'_map]
    exact η.naturality f)
  naturality_naturality {a b f g} θ := by
    obtain rfl := CategoryTheory.obj_ext_of_isDiscrete θ
    obtain rfl : θ = 𝟙 f := Subsingleton.elim _ _
    simp
  naturality_id a := by
    simp [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
  naturality_comp {a b c} f g := by
    simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, whiskerLeft_eqToHom,
      eqToHom_whiskerRight, eqToHom_trans, Functor.toPseudofunctor'_mapComp]

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- **Functoriality of the construction of Stacks 02XV.** A natural transformation of presheaves
of categories induces a functor between the total categories they are attached to, by
functoriality of the CoGrothendieck construction. -/
noncomputable def presheafOfCategoriesMap {F G : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂}} (η : F ⟶ G) :
    (presheafOfCategories F).obj ⥤ (presheafOfCategories G).obj :=
  CoGrothendieck.map (strongTransOfNatTrans η)

/-- The induced functor of Stacks 02XV commutes strictly with the projections to the base, so it
is a 1-morphism of the 2-category of categories over the base. -/
theorem presheafOfCategoriesMap_comp {F G : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂}} (η : F ⟶ G) :
    presheafOfCategoriesMap η ⋙ (presheafOfCategories G).p = (presheafOfCategories F).p :=
  CoGrothendieck.map_comp_forget _

/-- **Functoriality of the construction of Stacks 0049.** A natural transformation of presheaves
of groupoids induces a functor between the total categories they are attached to: the case of
`CategoryTheory.presheafOfCategoriesMap` for the underlying presheaves of categories. -/
noncomputable def presheafOfGroupoidsMap {F G : 𝒞ᵒᵖ ⥤ Grpd.{v₂, u₂}} (η : F ⟶ G) :
    (presheafOfGroupoids F).obj ⥤ (presheafOfGroupoids G).obj :=
  presheafOfCategoriesMap (Functor.whiskerRight η Grpd.forgetToCat)

/-- The induced functor of Stacks 0049 commutes strictly with the projections to the base. -/
theorem presheafOfGroupoidsMap_comp {F G : 𝒞ᵒᵖ ⥤ Grpd.{v₂, u₂}} (η : F ⟶ G) :
    presheafOfGroupoidsMap η ⋙ (presheafOfGroupoids G).p = (presheafOfGroupoids F).p :=
  presheafOfCategoriesMap_comp _

end CategoryTheory

end StrongTransOfNatTrans

namespace Deformation.GroupoidInFunctors

/-- A morphism of groupoids in functors (**Stacks 06K3**) induces a natural transformation of the
groupoid-valued functors assembled from their evaluations. The naturality square is an equality:
on objects it is the naturality of the map on the object functor, and on arrows the naturality of
the map on the arrow functor, both read through the identification of the arrows of an evaluated
groupoid with elements of the arrow functor. -/
noncomputable def evaluationNatTrans {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (Φ : Hom G H) :
    AlgebraicGeometry.Stack.evaluationGroupoidFunctor G ⟶
      AlgebraicGeometry.Stack.evaluationGroupoidFunctor H where
  app T := Φ.evaluation T
  naturality {T S} f := by
    have hobj : ∀ x : G.Evaluation T,
        Φ.mapObjects.app S (G.objects.map f x) = H.objects.map f (Φ.mapObjects.app T x) :=
      fun x => (NatTrans.naturality_apply Φ.mapObjects f x)
    refine CategoryTheory.Functor.ext
      (F := evaluationMap G f ⋙ Φ.evaluation S)
      (G := Φ.evaluation T ⋙ evaluationMap H f) hobj ?_
    intro x y a
    refine hom_eq_transport H S (hobj x) (hobj y) _ _ ?_
    have h1 := Φ.evaluation_map_arrow S ((evaluationMap G f).map a)
    have h2 := evaluationMap_map_arrow G f a
    have h3 := evaluationMap_map_arrow H f ((Φ.evaluation T).map a)
    have h4 := Φ.evaluation_map_arrow T a
    exact h1.trans ((congrArg (Φ.mapArrows.app S) h2).trans
      ((NatTrans.naturality_apply Φ.mapArrows f _).trans
        ((congrArg (H.arrows.map f) h4).symm.trans h3.symm)))

end Deformation.GroupoidInFunctors

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The 1-morphism from the pointwise groupoid presentation of one groupoid in algebraic spaces
into the quotient stack of another, induced by a morphism of groupoids: the induced morphism of
pointwise presentations followed by the canonical map from the presentation to the quotient
stack. -/
noncomputable def prestackToQuotientStack {G' G : GroupoidInAlgebraicSpaces C S hS B}
    (Φ : GroupoidInAlgebraicSpaces.Hom G' G) :
    (quotientPrestack G').obj ⥤ (quotientStack G).obj :=
  (quotientPrestackEquivalence G').inverse ⋙
    CategoryTheory.presheafOfGroupoidsMap
      (Deformation.GroupoidInFunctors.evaluationNatTrans Φ.toGroupoidHom) ⋙
    pointwiseToQuotientStack G

/-- `AlgebraicGeometry.Stack.prestackToQuotientStack` is strictly over the site. -/
theorem prestackToQuotientStack_comp {G' G : GroupoidInAlgebraicSpaces C S hS B}
    (Φ : GroupoidInAlgebraicSpaces.Hom G' G) :
    prestackToQuotientStack Φ ⋙ (quotientStack G).p = (quotientPrestack G').p := by
  rw [prestackToQuotientStack, Functor.assoc, Functor.assoc,
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq,
    CategoryTheory.presheafOfGroupoidsMap_comp]
  rfl

/-- **The 1-morphism of quotient stacks induced by a morphism of groupoids in algebraic spaces,
as a bare functor.** The target's quotient stack is a stack and the source's quotient stack is
the stackification of its pointwise presentation, so the universal property of Stacks 0436
extends `AlgebraicGeometry.Stack.prestackToQuotientStack` across that stackification. This is
the 1-morphism `[Z/R_Z] ⟶ [U/R]` of Stacks 04YN when the morphism of groupoids is the
comparison morphism of a restriction (Stacks 044B).

The 1-morphism of quotient stacks of Stacks 046Q is `AlgebraicGeometry.Stack.quotientStackMap`,
a `CategoryTheory.BasedFunctor`, which `AlgebraicGeometry.Stack.quotientStackMapHom` bundles; the
functor here is accompanied by `AlgebraicGeometry.Stack.quotientStackMapFunctor_comp`. -/
noncomputable def quotientStackMapFunctor {G' G : GroupoidInAlgebraicSpaces C S hS B}
    (Φ : GroupoidInAlgebraicSpaces.Hom G' G) :
    (quotientStack G').obj ⥤ (quotientStack G).obj :=
  Functor.Stackification.extendGroupoid
    (isFiberedInGroupoids_quotientPrestack G')
    (isFiberedInGroupoids_quotientStack G')
    (isStack_quotientStack G')
    (isFiberedInGroupoids_quotientStack G)
    (isStack_quotientStack G)
    (isFibredOneMorphism_toQuotientStack G').comp_eq
    (prestackToQuotientStack_comp Φ)
    (isLocallyBijective_toQuotientStack G')
    (essImage_toQuotientStack G')

/-- `AlgebraicGeometry.Stack.quotientStackMapFunctor` is strictly over the site, which for
categories fibred in groupoids is what it is to be a 1-morphism of the 2-category of
Stacks 02XS. -/
theorem quotientStackMapFunctor_comp {G' G : GroupoidInAlgebraicSpaces C S hS B}
    (Φ : GroupoidInAlgebraicSpaces.Hom G' G) :
    quotientStackMapFunctor Φ ⋙ (quotientStack G).p = (quotientStack G').p :=
  Functor.Stackification.extendGroupoid_comp_eq _ _ _ _ _ _ _ _ _


/-- The 1-morphism `[Φ] : [U'/R'] ⟶ [U/R]` of Stacks 046Q induced by a morphism of groupoids in
algebraic spaces, `AlgebraicGeometry.Stack.quotientStackMap`, as a 1-morphism of categories fibred
in groupoids over the big fppf site. When `Φ` is the comparison morphism of a restriction
(Stacks 044B) this is the 1-morphism `[Z/R_Z] ⟶ [U/R]` of Stacks 04YN. -/
noncomputable def quotientStackMapHom {G' G : GroupoidInAlgebraicSpaces C S hS B}
    (Φ : GroupoidInAlgebraicSpaces.Hom G' G) :
    quotientStackCFG C S hS G' ⟶ quotientStackCFG C S hS G :=
  Bicategory.InducedBicategory.mkHom (quotientStackMap Φ)

variable (C S hS)

/-- **Stacks 045D for a 1-morphism of quotient stacks.** Let `P` be a property of morphisms of
algebraic spaces over `S` stable under base change and local on the target for the fppf
precoverage, and let `Φ` be a morphism of groupoids in algebraic spaces whose induced 1-morphism
of quotient stacks is representable by algebraic spaces. Suppose some 2-fibre product `Q` of that
1-morphism with the canonical projection `S_U ⟶ [U/R]` of the target has its first projection
carried by a pair of equivalences onto a 1-morphism `a` of categories represented by algebraic
spaces `F` and `G₀`, with the induced morphism `F ⟶ G₀` having `P`. Then the 1-morphism of
quotient stacks has the relative property `P` of Stacks 03YK.

Local essential surjectivity of the projection, which is what Stacks 045D asks of the 1-morphism
being descended along, is `AlgebraicGeometry.Stack.localEssSurj_quotientStackProjectionHom` and
needs no hypothesis; the square Stacks 045D descends along is the canonical one. So the inputs
left to supply are the representability of the 1-morphism and the identification of one base
change of it, which is what Stacks 04YN gets from Stacks 04ZP and Stacks 04ZN. -/
theorem hasRelativeProperty_quotientStackMapHom_of_representingMap
    {G' G : GroupoidInAlgebraicSpaces C S hS B} (Φ : GroupoidInAlgebraicSpaces.Hom G' G)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (hf : IsRepresentableByAlgebraicSpaces C S hS (quotientStackMapHom Φ).hom)
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackMapHom Φ))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces C S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (F G₀ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace C S hS F) (hG₀ : IsAlgebraicSpace C S hS G₀)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G₀ ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap C S hS 𝒜 𝒞 F G₀ eF eG₀ a) :
        (⟨F, hF⟩ : AlgebraicSpaces C S hS) ⟶ (⟨G₀, hG₀⟩ : AlgebraicSpaces C S hS))) :
    HasRelativeProperty C S hS P (quotientStackMapHom Φ) hf :=
  have hsq := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
    (quotientStackProjectionHom G) (quotientStackMapHom Φ)
  hasRelativeProperty_of_baseChange.{u, u + 1, u + 1, t} C S hS _ _ _ P
    (quotientStackMapHom Φ) (quotientStackProjectionHom G) _ hsq
    hf (localEssSurj_quotientStackProjectionHom G)
    (hasRelativeProperty_fst_of_isTwoFibreProduct_representingMap C S hS P hsq
      hQ _ hQfst a ha p q α F G₀ hF hG₀ eF eG₀ hprop)

variable {C S hS}

open GroupoidInAlgebraicSpaces

/-- **Stacks 04YN, first conclusion.** The 1-morphism `[Z/R_Z] ⟶ [U/R]` induced by the
restriction of a groupoid in algebraic spaces along an invariant locally closed subspace `Z` of
its object space (Stacks 044F, part (2)) is an immersion in the sense of Stacks 04XB.

The hypotheses are Stacks 04ZP (`hf`, and `hQfst` for the auxiliary square) and Stacks 04ZN
(`Q`, `hQ`, `a`, `p`, `q`, `α`, `eF`, `eG₀` and `hrep`, which together say that one base change
of `[Z/R_Z] ⟶ [U/R]` along `S_U ⟶ [U/R]` is the inclusion of `Z` in `U`), taken here as explicit
data; the locality instance is Stacks 042U. With those inputs proved, the statement is
`AlgebraicGeometry.Stack.isImmersion_quotientStackMap_of_invariantRestrictionBaseChange`. The
invariance of `Z` enters through the immersion clause of
`AlgebraicGeometry.Space.IsLocallyClosedSubspace`. -/
theorem isImmersion_quotientStack_restrict_invariant
    [(Space.immersionProperty C S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} C S hS)]
    {G : GroupoidInAlgebraicSpaces C S hS B} {Z : Subfunctor G.objects.obj}
    (hZ : IsInvariantLocallyClosed G Z)
    (hf : IsRepresentableByAlgebraicSpaces C S hS
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom).hom)
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G)
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces C S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (Z.toFunctor ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G.objects.obj ⋙ typeToCat)).p)
    (hrep : representingMap C S hS 𝒜 𝒞 Z.toFunctor G.objects.obj eF eG₀ a = Z.ι) :
    Stack.IsImmersion C S hS
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom) :=
  (isImmersion_iff_hasRelativeProperty C S hS _ hf).mpr
    (hasRelativeProperty_quotientStackMapHom_of_representingMap.{u, u + 1} C S hS _
      (Space.immersionProperty C S hS) hf Q hQ hQfst a ha p q α
      Z.toFunctor G.objects.obj hZ.1.1 G.objects.property eF eG₀
      (by simp only [hrep]; exact hZ.1.2))

/-- **Stacks 04YN, second conclusion.** The 1-morphism `[Z/R_Z] ⟶ [U/R]` induced by the
restriction of a groupoid in algebraic spaces along an invariant **open** subspace `Z` of its
object space (Stacks 044F, part (1)) is an open immersion in the sense of Stacks 04XB.

The hypotheses are those of
`AlgebraicGeometry.Stack.isImmersion_quotientStack_restrict_invariant`, with Stacks 041X for the
locality instance; the invariance of `Z` enters through the open immersion clause of
`AlgebraicGeometry.Space.IsOpenSubspace`. -/
theorem isOpenImmersion_quotientStack_restrict_invariant
    [(Space.openImmersionProperty C S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} C S hS)]
    {G : GroupoidInAlgebraicSpaces C S hS B} {Z : Subfunctor G.objects.obj}
    (hZ : IsInvariantOpen G Z)
    (hf : IsRepresentableByAlgebraicSpaces C S hS
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom).hom)
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G)
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces C S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (Z.toFunctor ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G.objects.obj ⋙ typeToCat)).p)
    (hrep : representingMap C S hS 𝒜 𝒞 Z.toFunctor G.objects.obj eF eG₀ a = Z.ι) :
    Stack.IsOpenImmersion C S hS
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom) :=
  (isOpenImmersion_iff_hasRelativeProperty C S hS _ hf).mpr
    (hasRelativeProperty_quotientStackMapHom_of_representingMap.{u, u + 1} C S hS _
      (Space.openImmersionProperty C S hS) hf Q hQ hQfst a ha p q α
      Z.toFunctor G.objects.obj hZ.1.1 G.objects.property eF eG₀
      (by simp only [hrep]; exact hZ.1.2))

/-- **Stacks 04YN, third conclusion.** The 1-morphism `[Z/R_Z] ⟶ [U/R]` induced by the
restriction of a groupoid in algebraic spaces along an invariant **closed** subspace `Z` of its
object space is a closed immersion in the sense of Stacks 04XB.

The hypotheses are those of
`AlgebraicGeometry.Stack.isImmersion_quotientStack_restrict_invariant`, with Stacks 0420 for the
locality instance; the invariance of `Z` enters through the closed immersion clause of
`AlgebraicGeometry.Space.IsClosedSubspace`. -/
theorem isClosedImmersion_quotientStack_restrict_invariant
    [(Space.closedImmersionProperty C S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} C S hS)]
    {G : GroupoidInAlgebraicSpaces C S hS B} {Z : Subfunctor G.objects.obj}
    (hZ : IsInvariantClosed G Z)
    (hf : IsRepresentableByAlgebraicSpaces C S hS
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom).hom)
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G)
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces C S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (Z.toFunctor ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G.objects.obj ⋙ typeToCat)).p)
    (hrep : representingMap C S hS 𝒜 𝒞 Z.toFunctor G.objects.obj eF eG₀ a = Z.ι) :
    Stack.IsClosedImmersion C S hS
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom) :=
  (isClosedImmersion_iff_hasRelativeProperty C S hS _ hf).mpr
    (hasRelativeProperty_quotientStackMapHom_of_representingMap.{u, u + 1} C S hS _
      (Space.closedImmersionProperty C S hS) hf Q hQ hQfst a ha p q α
      Z.toFunctor G.objects.obj hZ.1.1 G.objects.property eF eG₀
      (by simp only [hrep]; exact hZ.1.2))

end AlgebraicGeometry.Stack

end
