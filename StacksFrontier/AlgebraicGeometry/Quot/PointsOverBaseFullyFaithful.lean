module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PointsOverBaseInverseLimit

/-!
# An algebraic space over a base is determined by its points on the test schemes

Let `Y` be an algebraic space over a scheme `S` of a big fppf site.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHomRepresentable.lean` assert that an algebraic
space over `Y` and its functor of points on the test schemes over `Y` are *equivalent data*.
This file proves the morphism half of that assertion: for algebraic spaces `p : H → Y` and
`p' : H' → Y` over `Y`,

`{k : H ⟶ H' // k ≫ p' = p} ≃ (spacePointsOver p ⟶ spacePointsOver p')`,

with `AlgebraicGeometry.Space.spacePointsOverMap` as the forward map.

The reason this is wanted is that `AlgebraicGeometry.Space.IsAffineAlgebraicSpaceOver` is an
existential statement, so a *family* of instances of it gives no inverse system of algebraic
spaces on its own: a transition morphism of the functors on the test schemes has to be promoted
to a morphism of the chosen algebraic spaces, and that is exactly fullness.  With the promotion
available, `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_isLimit` of
`StacksFrontier/AlgebraicGeometry/Quot/PointsOverBaseInverseLimit.lean` applies to a limit of
functors each of which merely *satisfies* the predicate.

## Main definitions

* `AlgebraicGeometry.Space.pointTest`: **the test scheme over `Y` that a section of `H` is**,
  namely its underlying scheme with the structure morphism the section of `Y` below it.
* `AlgebraicGeometry.Space.spacePointsOverInv`: **the morphism of algebraic spaces over `Y`
  that a morphism of the functors of points over `Y` is.**
* `AlgebraicGeometry.Space.spacePointsOverEquiv`: the resulting bijection.
* `AlgebraicGeometry.Space.stripUlift`: a morphism of universe lifts of functors, read as a
  morphism of the functors.
* `AlgebraicGeometry.Space.predicateSystem` and
  `AlgebraicGeometry.Space.predicateSystemProjection`: **the inverse system of algebraic spaces
  affine over `Y` attached to an inverse system of functors each of which is an algebraic space
  affine over `Y`.**

## Main results

* `AlgebraicGeometry.Space.spacePointsOverMap_injective`: the functor of points over `Y` is
  faithful on the algebraic spaces over `Y`.
* `AlgebraicGeometry.Space.spacePointsOverMap_spacePointsOverInv` and
  `AlgebraicGeometry.Space.spacePointsOverInv_spacePointsOverMap`: it is full, by the explicit
  inverse.
* `AlgebraicGeometry.Space.predicateSystemIso`: the system of functors of points over `Y` of
  the chosen algebraic spaces is the given system of functors.
* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_forall_isLimit`: **a cofiltered
  inverse limit of functors on the test schemes over `Y`, each of which is an algebraic space
  affine over `Y`, is an algebraic space affine over `Y`.**

## Implementation notes

**How a section becomes a test scheme.**  A section `x ∈ H(V)` over a scheme `V` of the site
determines the section `p(x) ∈ Y(V)`, hence by the Yoneda lemma a morphism `V → Y`, hence a test
scheme `AlgebraicGeometry.Space.pointTest p V x` over `Y` whose underlying scheme is `V`, and
`x` lies over the section of `Y` that this test scheme is, tautologically.  So a morphism `α` of
the functors of points over `Y` may be evaluated at it, and the result is a section of `H'` over
`V`; this is the promotion.  Naturality of the promotion in `V` comes from naturality of `α` at
the morphism of test schemes `AlgebraicGeometry.Space.pointTestMap`, whose underlying morphism
of schemes is the given one.

**That the promotion is a two-sided inverse.**  One direction is immediate: the test scheme
attached to a section and the value of `spacePointsOverMap` at it are the same by definition.
The other needs `AlgebraicGeometry.Space.pointTest_eq`: if `x` already lies over the section of
`Y` that a test scheme `T` is, then the test scheme attached to `x` *is* `T`, because
`AlgebraicGeometry.Space.yonedaEquiv_symm_testPoint` says the morphism `T.left → Y` which the
Yoneda lemma attaches to the section of `Y` that `T` is, is the structure morphism of `T`.  That
is an equality of objects of the index category, so it is used through
`AlgebraicGeometry.Space.spacePointsOver_app_congr`, which substitutes it.

**The universe lift is stripped by hand.**  `AlgebraicGeometry.Space.stripUlift` takes the
`ULift.down` of the value at a `ULift.up`, and
`AlgebraicGeometry.Space.whiskerRight_stripUlift` and
`AlgebraicGeometry.Space.stripUlift_whiskerRight` say the two operations are inverse.  This is
`CategoryTheory.uliftFunctor` being fully faithful, written out at the one place it is needed,
rather than through the full-faithfulness of the whiskering functor.

**The choices are made with `Classical.choice`.**  `IsAffineAlgebraicSpaceOver` is an
existential over data, so the system of algebraic spaces attached to a family of instances of it
depends on a choice of witnesses; `Exists.choose` and `Nonempty.some` make them.  Nothing below
depends on which witnesses are chosen.

## References

* [Stacks Project, Tag 07SE](https://stacks.math.columbia.edu/tag/07SE)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : AlgebraicSpaces B S hS}

/-! ### The test scheme that a section is -/

section PointTest

variable {H : AlgebraicSpaces B S hS} (p : H ⟶ Y)

/-- **The test scheme over `Y` that a section of `H` is**: the scheme the section lives over,
with the structure morphism to `Y` that the Yoneda lemma attaches to the section of `Y` below
it. -/
def pointTest (V : BigFppfOver B S hS) (x : H.1.obj (Opposite.op V)) : SchemesOver Y :=
  CostructuredArrow.mk
    (ObjectProperty.homMk (yonedaEquiv.symm (p.hom.app (Opposite.op V) x)))

attribute [local implicit_reducible] pointTest

/-- The underlying scheme of the test scheme that a section is, is the scheme the section lives
over. -/
theorem pointTest_left (V : BigFppfOver B S hS) (x : H.1.obj (Opposite.op V)) :
    (pointTest p V x).left = V :=
  rfl

/-- **A section lies over the section of `Y` that the test scheme it is lies over.** -/
theorem testPoint_pointTest (V : BigFppfOver B S hS) (x : H.1.obj (Opposite.op V)) :
    testPoint (pointTest p V x) = p.hom.app (Opposite.op V) x :=
  yonedaEquiv.apply_symm_apply _

/-- A section of `H`, read as a point of `H` over the section of `Y` that the test scheme it is
lies over. -/
def pointTestSection (V : BigFppfOver B S hS) (x : H.1.obj (Opposite.op V)) :
    spacePointsOverObj p (pointTest p V x) :=
  ⟨x, (testPoint_pointTest p V x).symm⟩

attribute [local implicit_reducible] pointTestSection

/-- **The test scheme that a section lying over the section of `Y` that a test scheme is, is
that test scheme itself.**  The structure morphism is recovered from the section of `Y` it is by
`AlgebraicGeometry.Space.yonedaEquiv_symm_testPoint`. -/
theorem pointTest_eq {T : SchemesOver Y} (x : spacePointsOverObj p T) :
    pointTest p T.left x.1 = T := by
  change CostructuredArrow.mk
    (ObjectProperty.homMk (yonedaEquiv.symm (p.hom.app (Opposite.op T.left) x.1))) = T
  rw [x.2, yonedaEquiv_symm_testPoint]
  rfl

/-- **The morphism of test schemes that a morphism of the underlying schemes is**, between the
test schemes attached to a section and to its restriction.  Its underlying morphism of schemes
is the given one, and the triangle commutes because the section of `Y` below a restricted
section is the restriction of the section of `Y` below it. -/
def pointTestMap {V V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (x : H.1.obj (Opposite.op V)) :
    pointTest p V' (H.1.map g.op x) ⟶ pointTest p V x :=
  CostructuredArrow.homMk g (by
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map g ≫ yonedaEquiv.symm (p.hom.app (Opposite.op V) x) =
      yonedaEquiv.symm (p.hom.app (Opposite.op V') (H.1.map g.op x))
    refine yonedaEquiv.injective ?_
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (NatTrans.naturality_apply p.hom g.op x).symm)

/-- The morphism of test schemes that a morphism of the underlying schemes is, has that
morphism as its underlying morphism of schemes. -/
theorem pointTestMap_left {V V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (x : H.1.obj (Opposite.op V)) : (pointTestMap p g x).left = g :=
  rfl

/-- **The test scheme that a section lying over the section of `Y` that a test scheme is, is
isomorphic to that test scheme**, by the identity of the underlying scheme.  This is
`AlgebraicGeometry.Space.pointTest_eq` as a morphism, which is what naturality consumes. -/
def pointTestIdMap {T : SchemesOver Y} (x : spacePointsOverObj p T) :
    pointTest p T.left x.1 ⟶ T :=
  CostructuredArrow.homMk (𝟙 T.left) (by
    refine ObjectProperty.hom_ext _ ?_
    change T.hom.hom = yonedaEquiv.symm (p.hom.app (Opposite.op T.left) x.1)
    rw [x.2, yonedaEquiv_symm_testPoint])

attribute [local implicit_reducible] pointTestIdMap

end PointTest

/-! ### Fullness and faithfulness -/

section FullyFaithful

variable {H H' H'' : AlgebraicSpaces B S hS} {p : H ⟶ Y} {p' : H' ⟶ Y} {p'' : H'' ⟶ Y}

/-- The section of `H'` that a morphism of the functors of points over `Y` attaches to a section
of `H`: the value of the morphism at the test scheme that the section is. -/
def spacePointsOverInvApp (α : spacePointsOver p ⟶ spacePointsOver p')
    (V : BigFppfOver B S hS) (x : H.1.obj (Opposite.op V)) : H'.1.obj (Opposite.op V) :=
  (α.app (Opposite.op (pointTest p V x)) (pointTestSection p V x)).1

/-- **The morphism of algebraic spaces that a morphism of the functors of points over `Y`
is.**  Naturality is naturality of the given morphism at
`AlgebraicGeometry.Space.pointTestMap`. -/
def spacePointsOverInvHom (α : spacePointsOver p ⟶ spacePointsOver p') : H.1 ⟶ H'.1 where
  app V := ↾spacePointsOverInvApp α V.unop
  naturality V V' g := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    exact congrArg Subtype.val
      (NatTrans.naturality_apply α (pointTestMap p g.unop x).op
        (pointTestSection p V.unop x))

/-- **The morphism of algebraic spaces over `Y` that a morphism of the functors of points over
`Y` is.** -/
def spacePointsOverInv (α : spacePointsOver p ⟶ spacePointsOver p') : H ⟶ H' :=
  ObjectProperty.homMk (spacePointsOverInvHom α)

/-- The morphism of algebraic spaces that a morphism of the functors of points over `Y` is, is a
morphism over `Y`: a section of `H'` attached to a section of `H` lies over the same section of
`Y`. -/
theorem spacePointsOverInv_comp (α : spacePointsOver p ⟶ spacePointsOver p') :
    spacePointsOverInv α ≫ p' = p := by
  refine ObjectProperty.hom_ext _
    (NatTrans.ext (funext fun V ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_))
  exact ((α.app (Opposite.op (pointTest p V.unop x))
    (pointTestSection p V.unop x)).2).trans (testPoint_pointTest p V.unop x)

/-- **The functor of points over `Y` is faithful**: the morphism attached to the map on points
induced by a morphism over `Y` is that morphism. -/
theorem spacePointsOverInv_spacePointsOverMap (k : H ⟶ H') (hk : k ≫ p' = p) :
    spacePointsOverInv (spacePointsOverMap k hk) = k := by
  refine ObjectProperty.hom_ext _
    (NatTrans.ext (funext fun V ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_))
  rfl

/-- **The section attached to a section already lying over the section of `Y` that a test
scheme is, is the value of the morphism at that test scheme.**  The test scheme attached to
such a section is the test scheme itself, and
`AlgebraicGeometry.Space.pointTestIdMap` is that identification as a morphism of test schemes,
at which the given morphism of functors is natural. -/
theorem spacePointsOverInvApp_eq (α : spacePointsOver p ⟶ spacePointsOver p')
    {T : SchemesOver Y} (x : spacePointsOverObj p T) :
    spacePointsOverInvApp α T.left x.1 = (α.app (Opposite.op T) x).1 := by
  have hres : (spacePointsOver p).map (pointTestIdMap p x).op x =
      pointTestSection p T.left x.1 :=
    Subtype.ext ((spacePointsOver_map_coe p (pointTestIdMap p x) x).trans
      (H.1.map_id_apply _ x.1))
  have hnat := congrArg Subtype.val
    (NatTrans.naturality_apply α (pointTestIdMap p x).op x)
  rw [hres] at hnat
  change (α.app (Opposite.op (pointTest p T.left x.1)) (pointTestSection p T.left x.1)).1 =
    (α.app (Opposite.op T) x).1
  exact hnat.trans
    ((spacePointsOver_map_coe p' (pointTestIdMap p x) (α.app (Opposite.op T) x)).trans
      (H'.1.map_id_apply _ _))

/-- **The functor of points over `Y` is full**: the map on points induced by the morphism
attached to a morphism of the functors of points is that morphism. -/
theorem spacePointsOverMap_spacePointsOverInv (α : spacePointsOver p ⟶ spacePointsOver p') :
    spacePointsOverMap (spacePointsOverInv α) (spacePointsOverInv_comp α) = α := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_)
  exact spacePointsOverInvApp_eq α x

/-- **The bijection between the morphisms of algebraic spaces over `Y` and the morphisms of
their functors of points over `Y`.** -/
def spacePointsOverEquiv (p : H ⟶ Y) (p' : H' ⟶ Y) :
    {k : H ⟶ H' // k ≫ p' = p} ≃ (spacePointsOver p ⟶ spacePointsOver p') where
  toFun k := spacePointsOverMap k.1 k.2
  invFun α := ⟨spacePointsOverInv α, spacePointsOverInv_comp α⟩
  left_inv k := Subtype.ext (spacePointsOverInv_spacePointsOverMap k.1 k.2)
  right_inv α := spacePointsOverMap_spacePointsOverInv α

/-- Two morphisms over `Y` inducing the same map on points over `Y` are equal. -/
theorem spacePointsOverMap_injective {k k' : H ⟶ H'} (hk : k ≫ p' = p) (hk' : k' ≫ p' = p)
    (h : spacePointsOverMap k hk = spacePointsOverMap k' hk') : k = k' := by
  rw [← spacePointsOverInv_spacePointsOverMap k hk,
    ← spacePointsOverInv_spacePointsOverMap k' hk', h]

/-- The morphism attached to an identity is an identity. -/
theorem spacePointsOverInv_id : spacePointsOverInv (𝟙 (spacePointsOver p)) = 𝟙 H := by
  refine spacePointsOverMap_injective (spacePointsOverInv_comp _) (Category.id_comp p) ?_
  rw [spacePointsOverMap_spacePointsOverInv, spacePointsOverMap_id]

/-- The morphism attached to a composite is the composite of the morphisms attached. -/
theorem spacePointsOverInv_comp_eq (α : spacePointsOver p ⟶ spacePointsOver p')
    (α' : spacePointsOver p' ⟶ spacePointsOver p'') :
    spacePointsOverInv (α ≫ α') = spacePointsOverInv α ≫ spacePointsOverInv α' := by
  have hcc : (spacePointsOverInv α ≫ spacePointsOverInv α') ≫ p'' = p := by
    rw [Category.assoc, spacePointsOverInv_comp, spacePointsOverInv_comp]
  refine spacePointsOverMap_injective (spacePointsOverInv_comp _) hcc ?_
  rw [spacePointsOverMap_spacePointsOverInv,
    spacePointsOverMap_comp _ _ (spacePointsOverInv_comp α) (spacePointsOverInv_comp α') hcc,
    spacePointsOverMap_spacePointsOverInv, spacePointsOverMap_spacePointsOverInv]

end FullyFaithful

/-! ### Stripping the universe lift -/

section Ulift

variable {C : Type*} [Category* C] {F G J : C ⥤ Type u}

/-- A morphism of the universe lifts of two functors, read as a morphism of the functors
themselves.  This is `CategoryTheory.uliftFunctor` being faithful and full, written out. -/
def stripUlift (β : F ⋙ uliftFunctor.{u + 1, u} ⟶ G ⋙ uliftFunctor.{u + 1, u}) : F ⟶ G where
  app T := ↾fun x ↦ (β.app T ⟨x⟩).down
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    exact congrArg ULift.down (NatTrans.naturality_apply β g ⟨x⟩)

/-- Stripping the universe lift of the universe lift of a morphism gives the morphism back. -/
theorem stripUlift_whiskerRight (α : F ⟶ G) :
    stripUlift (Functor.whiskerRight α uliftFunctor.{u + 1, u}) = α := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  rfl

/-- Stripping the universe lift is compatible with composition. -/
private theorem stripUlift_comp
    (β : F ⋙ uliftFunctor.{u + 1, u} ⟶ G ⋙ uliftFunctor.{u + 1, u})
    (γ : G ⋙ uliftFunctor.{u + 1, u} ⟶ J ⋙ uliftFunctor.{u + 1, u}) :
    stripUlift (β ≫ γ) = stripUlift β ≫ stripUlift γ :=
  rfl

/-- Two morphisms with the same universe lift are equal. -/
theorem whiskerRight_ulift_injective {α β : F ⟶ G}
    (h : Functor.whiskerRight α uliftFunctor.{u + 1, u} =
      Functor.whiskerRight β uliftFunctor.{u + 1, u}) : α = β := by
  rw [← stripUlift_whiskerRight α, ← stripUlift_whiskerRight β, h]

/-- The universe lift of the morphism a morphism of the universe lifts is, is that
morphism. -/
theorem whiskerRight_stripUlift
    (β : F ⋙ uliftFunctor.{u + 1, u} ⟶ G ⋙ uliftFunctor.{u + 1, u}) :
    Functor.whiskerRight (stripUlift β) uliftFunctor.{u + 1, u} = β := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  exact (ULift.up_down (β.app T x)).symm

end Ulift

/-! ### The inverse system attached to a family of representations -/

section DataSystem

variable {I : Type u} [Category.{u} I] (R : I ⥤ ((SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)))
variable (Hs : I → AlgebraicSpaces B S hS) (ps : ∀ i, Hs i ⟶ Y)
  (ψs : ∀ i, spacePointsOver (ps i) ⋙ uliftFunctor.{u + 1, u} ≅ R.obj i)

/-- The transition morphism of the representing algebraic spaces: the transition morphism of the
system, read as a morphism of the functors of points over `Y` through the given identifications
and the universe lift, promoted by fullness. -/
def dataTransition {i j : I} (φ : i ⟶ j) : Hs i ⟶ Hs j :=
  spacePointsOverInv (stripUlift ((ψs i).hom ≫ R.map φ ≫ (ψs j).inv))

/-- The transition morphism of the representing algebraic spaces is a morphism over `Y`. -/
theorem dataTransition_comp {i j : I} (φ : i ⟶ j) :
    dataTransition R Hs ps ψs φ ≫ ps j = ps i :=
  spacePointsOverInv_comp _

/-- The universe lift of the map on points over `Y` induced by the transition morphism is the
transition morphism of the system, read through the identifications. -/
theorem whiskerRight_dataTransition_eq {i j : I} (φ : i ⟶ j) :
    Functor.whiskerRight (spacePointsOverMap (dataTransition R Hs ps ψs φ)
        (dataTransition_comp R Hs ps ψs φ)) uliftFunctor.{u + 1, u} =
      (ψs i).hom ≫ R.map φ ≫ (ψs j).inv := by
  have h1 : spacePointsOverMap (dataTransition R Hs ps ψs φ) (dataTransition_comp R Hs ps ψs φ) =
      stripUlift ((ψs i).hom ≫ R.map φ ≫ (ψs j).inv) :=
    spacePointsOverMap_spacePointsOverInv _
  rw [h1, whiskerRight_stripUlift]

/-- The map on points over `Y` induced by the transition morphism, read through the
identifications and the universe lift, is the transition morphism of the system. -/
theorem whiskerRight_spacePointsOverMap_dataTransition {i j : I} (φ : i ⟶ j) :
    Functor.whiskerRight (spacePointsOverMap (dataTransition R Hs ps ψs φ)
          (dataTransition_comp R Hs ps ψs φ)) uliftFunctor.{u + 1, u} ≫ (ψs j).hom =
      (ψs i).hom ≫ R.map φ := by
  rw [whiskerRight_dataTransition_eq, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The transition morphism attached to an identity is the identity. -/
theorem dataTransition_id (i : I) : dataTransition R Hs ps ψs (𝟙 i) = 𝟙 (Hs i) := by
  rw [dataTransition, R.map_id, Category.id_comp, Iso.hom_inv_id]
  exact spacePointsOverInv_id

/-- The transition morphism attached to a composite is the composite. -/
theorem dataTransition_comp_eq {i j k : I} (φ : i ⟶ j) (ψ : j ⟶ k) :
    dataTransition R Hs ps ψs (φ ≫ ψ) =
      dataTransition R Hs ps ψs φ ≫ dataTransition R Hs ps ψs ψ := by
  rw [dataTransition, dataTransition, dataTransition, ← spacePointsOverInv_comp_eq]
  rw [← stripUlift_comp]
  simp

/-- **The inverse system of algebraic spaces over `Y` attached to a system of functors on the
test schemes over `Y` together with representations of its members.** -/
def dataSystem : I ⥤ AlgebraicSpaces B S hS where
  obj := Hs
  map φ := dataTransition R Hs ps ψs φ
  map_id := dataTransition_id R Hs ps ψs
  map_comp := dataTransition_comp_eq R Hs ps ψs

/-- The structure morphisms of the representing algebraic spaces, as a morphism of the system to
the constant system at `Y`. -/
def dataSystemProjection :
    dataSystem R Hs ps ψs ⋙ ObjectProperty.ι _ ⟶ (Functor.const I).obj Y.1 where
  app i := (ps i).hom
  naturality i j φ := by
    refine (congrArg InducedCategory.Hom.hom (dataTransition_comp R Hs ps ψs φ)).trans
      (Category.comp_id _).symm

/-- **The system of functors of points over `Y` of the representing algebraic spaces is the
given system of functors.** -/
def dataSystemPointsIso :
    spacePointsSystem B S hS (dataSystem R Hs ps ψs ⋙ ObjectProperty.ι _)
          (dataSystemProjection R Hs ps ψs) (fun i => (Hs i).2) ⋙
        (Functor.whiskeringRight _ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u} ≅ R :=
  NatIso.ofComponents (fun i ↦ ψs i)
    fun {_i _j} φ ↦ whiskerRight_spacePointsOverMap_dataTransition R Hs ps ψs φ

end DataSystem

/-! ### The inverse system attached to a family of instances of the predicate -/

section PredicateSystem

variable (B S hS)
variable {I : Type u} [Category.{u} I] (R : I ⥤ ((SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)))
variable (h : ∀ i, IsAffineAlgebraicSpaceOver Y (R.obj i))

/-- A chosen algebraic space representing a member of the system. -/
def chosenSpace (i : I) : AlgebraicSpaces B S hS := (h i).choose

/-- The structure morphism to `Y` of a chosen algebraic space representing a member of the
system. -/
def chosenProjection (i : I) : chosenSpace B S hS R h i ⟶ Y := (h i).choose_spec.choose

/-- The structure morphism of a chosen algebraic space is affine over `Y`. -/
theorem isAffineHom_chosenProjection (i : I) :
    IsAffineHom B S hS (chosenProjection B S hS R h i).hom :=
  (h i).choose_spec.choose_spec.1

/-- A chosen identification of a member of the system with the universe lift of the functor of
points over `Y` of the chosen algebraic space. -/
def chosenIso (i : I) :
    spacePointsOver (chosenProjection B S hS R h i) ⋙ uliftFunctor.{u + 1, u} ≅ R.obj i :=
  (h i).choose_spec.choose_spec.2.some

/-- **The inverse system of algebraic spaces attached to an inverse system of functors each of
which is an algebraic space affine over `Y`.** -/
def predicateSystem : I ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  dataSystem R (chosenSpace B S hS R h) (chosenProjection B S hS R h) (chosenIso B S hS R h) ⋙
    ObjectProperty.ι _

/-- The structure morphisms of the chosen algebraic spaces, as a morphism of the system to the
constant system at `Y`. -/
def predicateSystemProjection :
    predicateSystem B S hS R h ⟶ (Functor.const I).obj Y.1 :=
  dataSystemProjection R (chosenSpace B S hS R h) (chosenProjection B S hS R h)
    (chosenIso B S hS R h)

/-- The members of the system of algebraic spaces are algebraic spaces. -/
theorem isAlgebraicSpace_predicateSystem (i : I) :
    IsAlgebraicSpace B S hS ((predicateSystem B S hS R h).obj i) :=
  (chosenSpace B S hS R h i).2

/-- The structure morphisms of the system of algebraic spaces are affine over `Y`. -/
theorem isAffineHom_predicateSystemProjection (i : I) :
    IsAffineHom B S hS ((predicateSystemProjection B S hS R h).app i) :=
  isAffineHom_chosenProjection B S hS R h i

/-- **The system of functors of points over `Y` of the chosen algebraic spaces is the given
system of functors.** -/
def predicateSystemIso :
    spacePointsSystem B S hS (predicateSystem B S hS R h)
          (predicateSystemProjection B S hS R h)
          (isAlgebraicSpace_predicateSystem B S hS R h) ⋙
        (Functor.whiskeringRight _ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u} ≅ R :=
  dataSystemPointsIso R (chosenSpace B S hS R h) (chosenProjection B S hS R h)
    (chosenIso B S hS R h)

end PredicateSystem

end AlgebraicGeometry.Space

end
