module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# Closedness on points of a representable 1-morphism of stacks

Stacks 0512 characterizes a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is
representable by algebraic spaces as universally closed exactly when, for every algebraic stack
`𝒵` over `𝒴`, the first projection of `𝒵 ×_𝒴 𝒳` is a closed map on points for the topology of
Tag 04XL. This file collects the three transfers that characterization is assembled from; each is
a statement about one side of it and none of them mentions the other.

The first is the translation between the two readings of universal closedness of `f`: the
definition of Tag 04XB tests the structural morphism of Tag 04SG of every algebraic space
representing a base change of `f` along a scheme-valued point of `𝒴`, and
`AlgebraicGeometry.Stack.universallyClosed_iff_forall_relocalize` reads that test on the explicit
structural morphism `CategoryTheory.OverShriek.relocalizeToYoneda` of the lower-shriek extension
of Tag 03I5. Only `AlgebraicGeometry.Space.universallyClosedProperty`'s respecting isomorphisms is
used, so this is available without locality of universal closedness for the fppf topology — which
is Tag 0421 and is not in the library.

The second is the translation between the two readings of closedness of a projection: a
1-morphism between two categories fibred in groupoids *representable by algebraic spaces* is
closed on points for Tag 04XL exactly when the morphism of representing presheaves it induces
(Tag 04SW) is closed on points for Tag 03BX. This is
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_iff_isClosedMorphism_representingMap`, and it is
where `AlgebraicGeometry.Stack.isHomeomorph_spacePointMap_representing` enters: the two
representing charts are homeomorphisms on points, and they identify the two maps.

The third is independence of the choice of 2-fibre product:
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_fst_congr` says that any two 2-fibre products of
one cospan have first projections which are closed on points together. The comparison 1-morphism
between two 2-fibre products is bijective on points because the two composites are 2-isomorphic
to the identities, and continuous in both directions, hence a homeomorphism. This is what lets a
projection of an *iterated* 2-fibre product — the shape the cancellation statements of Tag 02XD
produce, and the shape Tag 04SD identifies a representing presheaf of — be read as a projection
of the canonical square that Tag 04T2 builds.

## Main results

* `AlgebraicGeometry.Stack.universallyClosed_iff_forall_relocalize`
* `AlgebraicGeometry.Stack.isClosedMap_pointsMap_iff_isClosedMorphism_representingMap`
* `AlgebraicGeometry.Stack.isClosedMap_pointsMap_fst_congr`

## Implementation notes

`AlgebraicGeometry.Stack.pointsMap_basedFunctorId` was `private` in the file of Tag 04XL when
this file was written and was re-derived here; it is now public there and is used directly.

The 2-cell of a 2-commutative square of categories fibred in groupoids has to be unwrapped twice
to reach the `CategoryTheory.BasedNatTrans` that
`AlgebraicGeometry.Stack.pointsMap_eq_of_basedNatTrans` consumes, and the composite of two
pre-morphisms of squares has an underlying based functor which is only *definitionally* the
composite of theirs. A `rw` with `pointsMap_eq_of_basedNatTrans` therefore fails with "Did not
find an occurrence of the pattern" even as it prints the pattern inside the goal, the note being
that the target is not type-correct under the `implicit` transparency level; the chains below are
written in term mode with `Eq.trans` and `congrFun` instead, which closes them with no
transparency attribute.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Topological preliminaries -/

/-- Closedness of a map transfers across a commutative square whose two horizontal maps are
homeomorphisms. -/
private theorem isClosedMap_iff_of_isHomeomorph {A C A' C' : Type*} [TopologicalSpace A]
    [TopologicalSpace C] [TopologicalSpace A'] [TopologicalSpace C']
    {p : A → C} {q : A' → C'} {σ : A → A'} {τ : C → C'}
    (hσ : IsHomeomorph σ) (hτ : IsHomeomorph τ) (hcomm : ∀ x, τ (p x) = q (σ x)) :
    IsClosedMap p ↔ IsClosedMap q := by
  have himg : ∀ V : Set A, τ '' (p '' V) = q '' (σ '' V) := by
    intro V
    rw [← Set.image_comp, ← Set.image_comp]
    exact Set.image_congr' hcomm
  refine ⟨fun hp T hT => ?_, fun hq V hV => ?_⟩
  · rw [← Set.image_preimage_eq T hσ.bijective.surjective, ← himg]
    exact hτ.isClosedMap _ (hp _ (hT.preimage hσ.continuous))
  · rw [← Set.preimage_image_eq (p '' V) hτ.bijective.injective, himg]
    exact (hq _ (hσ.isClosedMap _ hV)).preimage hτ.continuous

/-- A continuous map with a continuous two-sided inverse is a homeomorphism: the image of a set
is the preimage of it along the inverse. -/
private theorem isHomeomorph_of_continuous_inverse {A C : Type*} [TopologicalSpace A]
    [TopologicalSpace C] {e : A → C} {d : C → A} (he : Continuous e) (hd : Continuous d)
    (h₁ : ∀ x, d (e x) = x) (h₂ : ∀ y, e (d y) = y) : IsHomeomorph e := by
  refine ⟨he, fun W hW => ?_, Function.bijective_iff_has_inverse.2 ⟨d, h₁, h₂⟩⟩
  rw [Set.image_eq_preimage_of_inverse h₁ h₂]
  exact hW.preimage hd

/-! ### Universal closedness read on the lower-shriek extension -/

/-- **Universal closedness of a representable 1-morphism, read on the lower-shriek extension.**
`AlgebraicGeometry.Stack.UniversallyClosed` tests the structural morphism of Stacks 04SG of each
algebraic space representing a base change along a scheme-valued point of the target; this reads
that test on `CategoryTheory.OverShriek.relocalizeToYoneda`, which is the explicit form of that
structural morphism. Only `AlgebraicGeometry.Space.universallyClosedProperty`'s respecting
isomorphisms is used, so this needs no locality of universal closedness for the fppf topology. -/
theorem universallyClosed_iff_forall_relocalize
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    UniversallyClosed B S hS f ↔
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (_hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (T ⋙ typeToCat)).p) →
        Space.UniversallyClosed B S hS (OverShriek.relocalizeToYoneda U.hom T) := by
  constructor <;> intro H U y hy T hT he
  · exact (prop_algebraicSpaceMap_iff B S hS (Space.universallyClosedProperty B S hS) U T hT).mp
      (H U y hy T hT he)
  · exact (prop_algebraicSpaceMap_iff B S hS (Space.universallyClosedProperty B S hS) U T hT).mpr
      (H U y hy T hT he)

/-! ### Closedness on points against closedness of the representing morphism -/

/-- **Closedness on points of a 1-morphism of represented stacks is closedness of the induced
morphism of representing presheaves.** Both ends of the 1-morphism are represented by algebraic
spaces, so the canonical maps on points of the two representing charts are homeomorphisms by
`AlgebraicGeometry.Stack.isHomeomorph_spacePointMap_representing`, and they identify the two maps
by `AlgebraicGeometry.Stack.spacePointMap_representing_naturality`. -/
theorem isClosedMap_pointsMap_iff_isClosedMorphism_representingMap
    (𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (a : 𝒜 ⟶ 𝒞) :
    @IsClosedMap _ _ (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
        (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property a.hom) ↔
      Space.IsClosedMorphism B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) :=
  (@isClosedMap_iff_of_isHomeomorph
      (Space.points B S hS F) (Space.points B S hS G)
      (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
      (Space.pointTopology B S hS F) (Space.pointTopology B S hS G)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
      (Space.pointsMap B S hS F (representingMap B S hS 𝒜 𝒞 F G eF eG a))
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property a.hom)
      (spacePointMap B S hS F 𝒜 (representingEquivalence B S hS F 𝒜 eF).functor)
      (spacePointMap B S hS G 𝒞 (representingEquivalence B S hS G 𝒞 eG).functor)
      (isHomeomorph_spacePointMap_representing B S hS F hF 𝒜 eF)
      (isHomeomorph_spacePointMap_representing B S hS G hG 𝒞 eG)
      (spacePointMap_representing_naturality B S hS F G 𝒜 𝒞 eF eG a)).symm

/-! ### Independence of the choice of 2-fibre product -/

/-- If two pre-morphisms between 2-fibre products compose to something 2-isomorphic to the
identity, their maps on points compose to the identity. -/
private theorem pointsMap_comp_eq_self
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {P Q : Bicategory.TwoCommSq g f}
    (hQ : Bicategory.IsTwoFibreProduct Q) (a : Bicategory.TwoCommSq.PreHom Q P)
    (c : Bicategory.TwoCommSq.PreHom P Q) (x : points B S hS Q.pt.val Q.pt.property) :
    pointsMap B S hS P.pt.val P.pt.property Q.pt.property c.hom.hom
      (pointsMap B S hS Q.pt.val Q.pt.property P.pt.property a.hom.hom x) = x := by
  obtain ⟨θ, -, -⟩ := Quotient.exact (hQ.hom_ext (Quotient.mk _ (a.comp c)) (𝟙 Q))
  exact (pointsMap_comp B S hS Q.pt.val Q.pt.property P.pt.property Q.pt.property
    a.hom.hom c.hom.hom x).trans
    ((congrFun (pointsMap_eq_of_basedNatTrans B S hS Q.pt.val Q.pt.property Q.pt.property
      θ.hom.hom) x).trans (pointsMap_basedFunctorId B S hS Q.pt.property x))

/-- The comparison 1-morphism between two 2-fibre products of one cospan of categories fibred in
groupoids is a homeomorphism on points for the topology of Tag 04XL: the two composites are
2-isomorphic to the identities, and 2-isomorphic 1-morphisms induce the same map on points. -/
private theorem isHomeomorph_pointsMap_preHom
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} {P Q : Bicategory.TwoCommSq g f}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (a : Bicategory.TwoCommSq.PreHom Q P) :
    @IsHomeomorph _ _ (pointTopology B S hS Q.pt) (pointTopology B S hS P.pt)
      (pointsMap B S hS Q.pt.val Q.pt.property P.pt.property a.hom.hom) := by
  let c := Quotient.out (hQ.from P)
  refine @isHomeomorph_of_continuous_inverse _ _ (pointTopology B S hS Q.pt)
    (pointTopology B S hS P.pt) _
    (pointsMap B S hS P.pt.val P.pt.property Q.pt.property c.hom.hom)
    (continuous_pointsMap B S hS Q.pt P.pt a.hom.hom)
    (continuous_pointsMap B S hS P.pt Q.pt c.hom.hom)
    (pointsMap_comp_eq_self B S hS hQ a c) (pointsMap_comp_eq_self B S hS hP c a)

/-- The identity is a homeomorphism of the points of an algebraic stack for the topology of
Tag 04XL. Stated separately because that topology is a `def` and not an instance. -/
private theorem isHomeomorph_id_points
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    @IsHomeomorph _ _ (pointTopology B S hS 𝒵) (pointTopology B S hS 𝒵) id := by
  let _ := pointTopology B S hS 𝒵
  exact ⟨continuous_id, IsOpenMap.id, Function.bijective_id⟩

/-- **Closedness on points of the first projection is a property of the cospan.** Any two
2-fibre products of one cospan of categories fibred in groupoids over the big fppf site of `S`
have first projections which are closed on points together: the comparison 1-morphism is a
homeomorphism on points for the topology of Tag 04XL, and it identifies the two projections. -/
theorem isClosedMap_pointsMap_fst_congr
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P Q : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : @IsClosedMap _ _ (pointTopology B S hS P.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom)) :
    @IsClosedMap _ _ (pointTopology B S hS Q.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS Q.pt.val Q.pt.property 𝒵.property Q.fst.hom) := by
  let a := Quotient.out (hP.from Q)
  refine (@isClosedMap_iff_of_isHomeomorph
      (points B S hS Q.pt.val Q.pt.property) (points B S hS 𝒵.val 𝒵.property)
      (points B S hS P.pt.val P.pt.property) (points B S hS 𝒵.val 𝒵.property)
      (pointTopology B S hS Q.pt) (pointTopology B S hS 𝒵)
      (pointTopology B S hS P.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS Q.pt.val Q.pt.property 𝒵.property Q.fst.hom)
      (pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom)
      (pointsMap B S hS Q.pt.val Q.pt.property P.pt.property a.hom.hom) id
      (isHomeomorph_pointsMap_preHom B S hS hP hQ a)
      (isHomeomorph_id_points B S hS 𝒵) (fun x => ?_)).mpr h
  exact (congrFun (pointsMap_eq_of_basedNatTrans B S hS Q.pt.val Q.pt.property 𝒵.property
      a.isoFst.hom.hom) x).trans
    (pointsMap_comp B S hS Q.pt.val Q.pt.property P.pt.property 𝒵.property
      a.hom.hom P.fst.hom x).symm

end AlgebraicGeometry.Stack

end
