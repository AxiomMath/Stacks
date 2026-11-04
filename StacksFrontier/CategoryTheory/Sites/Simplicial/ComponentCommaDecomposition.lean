module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition

/-!
# The comma categories of two component inclusions of a simplicial site

Stacks 09WG computes the restriction to simplicial degree `m` of lower shriek from degree `n` as
a coproduct, resp. a direct sum, indexed by the simplex maps `[n] ⟶ [m]`. Both sides of that
formula are left adjoints, so it is equivalent to the corresponding formula for the right
adjoints, which is a statement about right Kan extension along a component inclusion and
involves no sheafification at all. Pointwise, each of the two Kan extensions along a component
inclusion is a (co)limit over a comma category of the two inclusions, and this file computes
those comma categories.

In **case (A)** the right Kan extension along the degree-`m` inclusion, evaluated in degree `n`,
is a limit over `StructuredArrow (op (ι_n U)) ι_m.op`; that category is the disjoint union, over
the simplex maps `φ : [n] ⟶ [m]`, of pieces each of which has an *initial* object, namely
`(u φ (U), (φ, 𝟙))`. In **case (B)** the same holds one side over: the *left* Kan extension along
the degree-`n` inclusion, evaluated in degree `m`, is a colimit over
`CostructuredArrow ι_n.op (op (ι_m V))`, which is the disjoint union over the simplex maps of
pieces each of which has a *terminal* object, namely `(u φ (V), (φ, 𝟙))`. Consequently the
(co)limit is in each case a product, resp. a coproduct, of evaluations, one factor for each
simplex map. The two cases are genuinely one side over from each other: in case (A) the pieces
of the comma category on the *left* Kan extension side are the comma categories computing left
Kan extensions along the transition functors, and in case (B) the pieces on the right Kan
extension side are the comma categories computing right Kan extensions along the transitions.

## Main definitions

* `CategoryTheory.SimplicialSite.componentStructuredArrow` and
  `CategoryTheory.CocontinuousSimplicialSite.componentCostructuredArrow`: the distinguished
  object of the comma category attached to a simplex map, in the two cases.

## Main results

* `CategoryTheory.Limits.isLimitFanOfUniqueArrows` and
  `CategoryTheory.Limits.isColimitCofanOfUniqueArrows`: a limit over a category each of whose
  objects receives a morphism from exactly one member of a given family of objects, uniquely, is
  a product of the values of the diagram at that family; dually for colimits.
* `CategoryTheory.SimplicialSite.componentStructuredArrow_arrow`,
  `.componentStructuredArrow_subsingleton` and the case (B) counterparts
  `CategoryTheory.CocontinuousSimplicialSite.componentCostructuredArrow_arrow`,
  `.componentCostructuredArrow_subsingleton`: the comma category of two component inclusions is
  the disjoint union of its pieces, each with a distinguished object.
* `CategoryTheory.SimplicialSite.isLimitFanRanComponent`: in case (A), the right Kan extension
  along the degree-`m` component inclusion, evaluated at a degree-`n` object `U`, is the product
  over `φ : [n] ⟶ [m]` of the values at `u φ (U)`.
* `CategoryTheory.CocontinuousSimplicialSite.isColimitCofanLanComponent`: in case (B), the left
  Kan extension along the degree-`n` component inclusion, evaluated at a degree-`m` object `V`,
  is the coproduct over `φ : [n] ⟶ [m]` of the values at `u φ (V)`.

## Implementation notes

The decomposition is stated as the two hypotheses of
`CategoryTheory.Limits.isLimitFanOfUniqueArrows` — a function picking, for each object, an index
and a morphism from the distinguished object of that index, and the statement that such pairs
are unique — rather than as an equivalence with a disjoint union of categories. The hypotheses
are then a function and a subsingleton statement, so no dependent transport along the index
decomposition is needed anywhere.

The distinguished objects are the Cartesian lifts of the simplex maps: in case (A) the family
`CategoryTheory.SimplicialSiteSituation.continuousInclusionTransition`, and in case (B) Mathlib's
`CategoryTheory.Grothendieck.ιNatTrans`. Both are already available, so no new family of
cross-fibre arrows is introduced here, and the factorization lemma
`CategoryTheory.Pseudofunctor.CoGrothendieck.ι_map_comp_ιNatTrans_app` is what makes the
case (A) arrow a one-line term.

The total category of case (A) is Mathlib's contravariant Grothendieck construction
`CoGrothendieck` of the strict pseudofunctor
`CategoryTheory.SimplicialSite.totalPseudofunctor`. Goals mentioning both that pseudofunctor and
the underlying cosimplicial diagram of categories are not type-correct at `implicit`
transparency, because identifying the fibre `totalPseudofunctor.obj ⟨op (op n)⟩` with
`underlying.obj n` unfolds a semireducible definition; `simp` and `rw` then make no progress at
all, not even on a goal of the shape `𝟙 ≫ ψ = ψ ≫ 𝟙`. The declarations that compare the base
components of two cross-fibre arrows therefore avoid producing such goals altogether: each
obtains the whole comparison from a factorization lemma (`CoGrothendieck.ι_map_comp_ιNatTrans_app`
in case (A), Mathlib's `Grothendieck.ιNatTrans_app_comp_ι_map` in case (B)) applied as a *term*,
which is checked at default transparency, and then reads off the base and the fibre with
`congrArg` on the structure projections and `Hom.congr`. The residual casts are proof-irrelevant,
so `Category.comp_id` and `Category.id_comp` discharge them as terms too, and no transparency
option is required.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

namespace CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

variable {I : Type w} {K : Type u₁} [Category.{v₁} K] {A : Type u₂} [Category.{v₂} A]
variable (D : K ⥤ A) (j : I → K)

/-- The leg, at an object of `K`, of the cone comparing a limit of `D` with a product of the
values of `D` at a family `j`: it is given by an index together with a morphism from the
corresponding member of the family. -/
def fanLeg (t : Fan fun i => D.obj (j i)) {k : K} (p : Σ i : I, (j i ⟶ k)) :
    t.pt ⟶ D.obj k :=
  t.proj p.1 ≫ D.map p.2

/-- The cone on `D` attached to a fan on the values of `D` at the family `j`, using at each
object of `K` the chosen morphism from the family. -/
@[simps pt]
def coneOfFan (arr : ∀ k : K, Σ i : I, (j i ⟶ k))
    (harr : ∀ (k : K) (p q : Σ i : I, (j i ⟶ k)), p = q) (t : Fan fun i => D.obj (j i)) :
    Cone D where
  pt := t.pt
  π :=
    { app := fun k => fanLeg D j t (arr k)
      naturality := fun k k' f => by
        have h : fanLeg D j t (⟨(arr k).1, (arr k).2 ≫ f⟩ : Σ i : I, (j i ⟶ k')) =
            fanLeg D j t (arr k') := congrArg _ (harr _ _ _)
        simpa [fanLeg, Functor.map_comp] using h.symm }

/-- A limit over a category each of whose objects receives a morphism from exactly one member of
a family `j : I → K`, and from that member exactly one morphism, is the product of the values of
the diagram at the family.

The two hypotheses say precisely that for every object `k` the type of pairs consisting of an
index `i` and a morphism `j i ⟶ k` is a singleton: `arr` provides an element and `harr` its
uniqueness. Equivalently, `K` is the disjoint union of the full subcategories generated by the
members of the family, and `j i` is an initial object of its piece. -/
noncomputable def isLimitFanOfUniqueArrows (arr : ∀ k : K, Σ i : I, (j i ⟶ k))
    (harr : ∀ (k : K) (p q : Σ i : I, (j i ⟶ k)), p = q) {c : Cone D} (hc : IsLimit c) :
    IsLimit (Fan.mk c.pt fun i => c.π.app (j i)) := by
  refine Fan.IsLimit.mk _ (fun t => hc.lift (coneOfFan D j arr harr t)) (fun t i => ?_)
    (fun t s hs => ?_)
  · refine (hc.fac (coneOfFan D j arr harr t) (j i)).trans ?_
    change fanLeg D j t (arr (j i)) = t.proj i
    rw [harr (j i) (arr (j i)) ⟨i, 𝟙 (j i)⟩]
    simp [fanLeg]
  · refine hc.hom_ext fun k => ?_
    refine Eq.trans ?_ (hc.fac (coneOfFan D j arr harr t) k).symm
    change s ≫ c.π.app k = fanLeg D j t (arr k)
    rw [← c.w (arr k).2, ← Category.assoc,
      show s ≫ c.π.app (j (arr k).1) = t.proj (arr k).1 from hs _]
    rfl

/-- The leg, at an object of `K`, of the cocone comparing a colimit of `D` with a coproduct of
the values of `D` at a family `j`: it is given by an index together with a morphism to the
corresponding member of the family. -/
def cofanLeg (t : Cofan fun i => D.obj (j i)) {k : K} (p : Σ i : I, (k ⟶ j i)) :
    D.obj k ⟶ t.pt :=
  D.map p.2 ≫ t.inj p.1

/-- The cocone on `D` attached to a cofan on the values of `D` at the family `j`, using at each
object of `K` the chosen morphism to the family. -/
@[simps pt]
def coconeOfCofan (arr : ∀ k : K, Σ i : I, (k ⟶ j i))
    (harr : ∀ (k : K) (p q : Σ i : I, (k ⟶ j i)), p = q) (t : Cofan fun i => D.obj (j i)) :
    Cocone D where
  pt := t.pt
  ι :=
    { app := fun k => cofanLeg D j t (arr k)
      naturality := fun k k' f => by
        have h : cofanLeg D j t (⟨(arr k').1, f ≫ (arr k').2⟩ : Σ i : I, (k ⟶ j i)) =
            cofanLeg D j t (arr k) := congrArg _ (harr _ _ _)
        simpa [cofanLeg, Functor.map_comp] using h }

/-- A colimit over a category each of whose objects admits a morphism to exactly one member of a
family `j : I → K`, and to that member exactly one morphism, is the coproduct of the values of
the diagram at the family. This is the dual of `isLimitFanOfUniqueArrows`. -/
noncomputable def isColimitCofanOfUniqueArrows (arr : ∀ k : K, Σ i : I, (k ⟶ j i))
    (harr : ∀ (k : K) (p q : Σ i : I, (k ⟶ j i)), p = q) {c : Cocone D} (hc : IsColimit c) :
    IsColimit (Cofan.mk c.pt fun i => c.ι.app (j i)) := by
  refine Cofan.IsColimit.mk _ (fun t => hc.desc (coconeOfCofan D j arr harr t)) (fun t i => ?_)
    (fun t s hs => ?_)
  · refine (hc.fac (coconeOfCofan D j arr harr t) (j i)).trans ?_
    change cofanLeg D j t (arr (j i)) = t.inj i
    rw [harr (j i) (arr (j i)) ⟨i, 𝟙 (j i)⟩]
    simp [cofanLeg]
  · refine hc.hom_ext fun k => ?_
    refine Eq.trans ?_ (hc.fac (coconeOfCofan D j arr harr t) k).symm
    change c.ι.app k ≫ s = cofanLeg D j t (arr k)
    rw [← c.w (arr k).2, Category.assoc,
      show c.ι.app (j (arr k).1) ≫ s = t.inj (arr k).1 from hs _]
    rfl

end CategoryTheory.Limits

namespace CategoryTheory.SimplicialSite

universe u v₂ u₂

attribute [local implicit_reducible] CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

variable (C : SimplicialSite.{u}) {n m : SimplexCategory}

variable (U : C.underlying.obj n)

/-- The distinguished object of the comma category of the two component inclusions attached to a
simplex map `φ : [n] ⟶ [m]`, in case (A): the object `u φ (U)` of degree `m`, together with the
morphism `(φ, 𝟙)` of the total category from it to `U`. -/
def componentStructuredArrow (φ : n ⟶ m) :
    StructuredArrow (Opposite.op ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).obj U))
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op :=
  StructuredArrow.mk ((SimplicialSiteSituation.continuousInclusionTransition C φ).app U).op

/-- In case (A), every object of the comma category of the two component inclusions receives a
morphism from the distinguished object attached to the simplex map underlying it: the simplex map
is the base of the given morphism of the total category, and the morphism is its fibre. -/
def componentStructuredArrow_arrow (k : StructuredArrow
      (Opposite.op ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).obj U))
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op) :
    Σ φ : n ⟶ m, (componentStructuredArrow C U φ ⟶ k) := by
  refine ⟨k.hom.unop.base.unop, StructuredArrow.homMk (Opposite.op k.hom.unop.fiber) ?_⟩
  dsimp [componentStructuredArrow]
  rw [← op_comp]
  exact congrArg Quiver.Hom.op (CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor
    k.hom.unop.base.unop.op k.hom.unop.fiber)

/-- In case (A), an object of the comma category of the two component inclusions receives a
morphism from exactly one distinguished object, and from it exactly one morphism: the type of
pairs consisting of a simplex map and a morphism from the attached distinguished object is a
subsingleton.

Together with `componentStructuredArrow_arrow` this says that the comma category is the disjoint
union of pieces indexed by the simplex maps `[n] ⟶ [m]`, each with an initial object. -/
lemma componentStructuredArrow_subsingleton (k : StructuredArrow
      (Opposite.op ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).obj U))
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op)
    (p q : Σ φ : n ⟶ m, (componentStructuredArrow C U φ ⟶ k)) : p = q := by
  have key : ∀ (φ : n ⟶ m) (f : componentStructuredArrow C U φ ⟶ k),
      (⟨φ, f⟩ : Σ φ : n ⟶ m, (componentStructuredArrow C U φ ⟶ k)) =
        componentStructuredArrow_arrow C U k := by
    intro φ f
    have hmk := (CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor φ.op
      (StructuredArrow.Hom.right f).unop).symm.trans
        (congrArg Quiver.Hom.unop (StructuredArrow.w f))
    have hb : φ.op = k.hom.unop.base := congrArg CoGrothendieck.Hom.base hmk
    obtain rfl : φ = k.hom.unop.base.unop := congrArg Quiver.Hom.unop hb
    exact congrArg (Sigma.mk _) (StructuredArrow.hom_ext _ _ (congrArg Quiver.Hom.op
      ((CoGrothendieck.Hom.congr hmk).trans (Category.comp_id k.hom.unop.fiber))))
  exact (key _ p.2).trans (key _ q.2).symm

variable {A : Type u₂} [Category.{v₂} A]

/-- **Stacks 09WG**, the comma-category computation behind parts (3) and (6) in case (A). The
right Kan extension along the opposite of the degree-`m` component inclusion, evaluated at an
object `U` of degree `n`, is the product over the simplex maps `φ : [n] ⟶ [m]` of the values at
`u φ (U)`.

The projections are the legs of the pointwise limit cone at the distinguished objects, that is,
the composite of the transport along `(φ, 𝟙)` with the counit of the Kan extension. -/
noncomputable def isLimitFanRanComponent (H : (C.underlying.obj m)ᵒᵖ ⥤ A)
    [∀ G : (C.underlying.obj m)ᵒᵖ ⥤ A,
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op.HasRightKanExtension G]
    [(CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op.HasPointwiseRightKanExtension H] :
    IsLimit (Fan.mk
      (((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op.ran.obj H).obj
        (Opposite.op ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).obj U)))
      fun φ : n ⟶ m =>
        ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op.ran.obj H).map
            (componentStructuredArrow C U φ).hom ≫
          ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op.ranCounit.app H).app
            (componentStructuredArrow C U φ).right) :=
  isLimitFanOfUniqueArrows _ (componentStructuredArrow C U)
    (componentStructuredArrow_arrow C U) (componentStructuredArrow_subsingleton C U)
    (Functor.isPointwiseRightKanExtensionRanCounit
      (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op m)).op H
      (Opposite.op ((CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)).obj U)))

end CategoryTheory.SimplicialSite

namespace CategoryTheory.CocontinuousSimplicialSite

universe u v₂ u₂

attribute [local implicit_reducible] CategoryTheory.Grothendieck.ι

variable (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory}
  (V : C.underlying.obj (Opposite.op m))

/-- The distinguished object of the comma category of the two component inclusions attached to a
simplex map `φ : [n] ⟶ [m]`, in case (B): the object `u φ (V)` of degree `n`, together with the
morphism `(φ, 𝟙)` of the total category from `V` to it.

The morphism is the component of Mathlib's `CategoryTheory.Grothendieck.ιNatTrans`, the case (B)
counterpart of `CategoryTheory.SimplicialSiteSituation.continuousInclusionTransition`. -/
def componentCostructuredArrow (φ : n ⟶ m) :
    CostructuredArrow (Grothendieck.ι C.underlying (Opposite.op n)).op
      (Opposite.op ((Grothendieck.ι C.underlying (Opposite.op m)).obj V)) :=
  CostructuredArrow.mk ((Grothendieck.ιNatTrans φ.op).app V).op

/-- In case (B), every object of the comma category of the two component inclusions admits a
morphism to the distinguished object attached to the simplex map underlying it: the simplex map
is the base of the given morphism of the total category, and the morphism is its fibre. -/
def componentCostructuredArrow_arrow
    (k : CostructuredArrow (Grothendieck.ι C.underlying (Opposite.op n)).op
      (Opposite.op ((Grothendieck.ι C.underlying (Opposite.op m)).obj V))) :
    Σ φ : n ⟶ m, (k ⟶ componentCostructuredArrow C V φ) := by
  refine ⟨k.hom.unop.base.unop, CostructuredArrow.homMk (k.hom.unop.fiber).op ?_⟩
  dsimp [componentCostructuredArrow]
  simp only [← op_comp]
  exact congrArg Quiver.Hom.op
    (Grothendieck.ιNatTrans_app_comp_ι_map k.hom.unop.base k.hom.unop.fiber)

/-- In case (B), an object of the comma category of the two component inclusions admits a
morphism to exactly one distinguished object, and to it exactly one morphism: the type of pairs
consisting of a simplex map and a morphism to the attached distinguished object is a
subsingleton.

Together with `componentCostructuredArrow_arrow` this says that the comma category is the
disjoint union of pieces indexed by the simplex maps `[n] ⟶ [m]`, each with a terminal
object. -/
lemma componentCostructuredArrow_subsingleton
    (k : CostructuredArrow (Grothendieck.ι C.underlying (Opposite.op n)).op
      (Opposite.op ((Grothendieck.ι C.underlying (Opposite.op m)).obj V)))
    (p q : Σ φ : n ⟶ m, (k ⟶ componentCostructuredArrow C V φ)) : p = q := by
  have key : ∀ (φ : n ⟶ m) (f : k ⟶ componentCostructuredArrow C V φ),
      (⟨φ, f⟩ : Σ φ : n ⟶ m, (k ⟶ componentCostructuredArrow C V φ)) =
        componentCostructuredArrow_arrow C V k := by
    intro φ f
    have h := CostructuredArrow.w f
    have hmk : (⟨φ.op, f.left.unop⟩ : (Grothendieck.ι C.underlying (Opposite.op m)).obj V ⟶
          (Grothendieck.ι C.underlying (Opposite.op n)).obj (Opposite.unop k.left)) =
        k.hom.unop :=
      (Grothendieck.ιNatTrans_app_comp_ι_map φ.op f.left.unop).symm.trans
        (congrArg Quiver.Hom.unop h)
    have hb : φ.op = k.hom.unop.base := congrArg Grothendieck.Hom.base hmk
    obtain rfl : φ = k.hom.unop.base.unop := congrArg Quiver.Hom.unop hb
    exact congrArg (Sigma.mk _) (CostructuredArrow.hom_ext _ _ (congrArg Quiver.Hom.op
      ((Grothendieck.congr hmk).trans (Category.id_comp k.hom.unop.fiber))))
  exact (key _ p.2).trans (key _ q.2).symm

variable {A : Type u₂} [Category.{v₂} A]

/-- **Stacks 09WG**, the comma-category computation behind parts (3) and (6) in case (B). The
left Kan extension along the opposite of the degree-`n` component inclusion, evaluated at an
object `V` of degree `m`, is the coproduct over the simplex maps `φ : [n] ⟶ [m]` of the values at
`u φ (V)`.

The injections are the legs of the pointwise colimit cocone at the distinguished objects, that
is, the composite of the unit of the Kan extension with the transport along `(φ, 𝟙)`. -/
noncomputable def isColimitCofanLanComponent (Q : (C.underlying.obj (Opposite.op n))ᵒᵖ ⥤ A)
    [∀ G : (C.underlying.obj (Opposite.op n))ᵒᵖ ⥤ A,
      (Grothendieck.ι C.underlying (Opposite.op n)).op.HasLeftKanExtension G]
    [(Grothendieck.ι C.underlying (Opposite.op n)).op.HasPointwiseLeftKanExtension Q] :
    IsColimit (Cofan.mk
      (((Grothendieck.ι C.underlying (Opposite.op n)).op.lan.obj Q).obj
        (Opposite.op ((Grothendieck.ι C.underlying (Opposite.op m)).obj V)))
      fun φ : n ⟶ m =>
        ((Grothendieck.ι C.underlying (Opposite.op n)).op.lanUnit.app Q).app
            (componentCostructuredArrow C V φ).left ≫
          ((Grothendieck.ι C.underlying (Opposite.op n)).op.lan.obj Q).map
            (componentCostructuredArrow C V φ).hom) := by
  haveI : (Grothendieck.ι C.underlying (Opposite.op n)).op.HasPointwiseLeftKanExtension
      ((𝟭 ((C.underlying.obj (Opposite.op n))ᵒᵖ ⥤ A)).obj Q) :=
    inferInstanceAs (Functor.HasPointwiseLeftKanExtension
      (Grothendieck.ι C.underlying (Opposite.op n)).op Q)
  exact isColimitCofanOfUniqueArrows _ (componentCostructuredArrow C V)
    (componentCostructuredArrow_arrow C V) (componentCostructuredArrow_subsingleton C V)
    (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((Grothendieck.ι C.underlying (Opposite.op n)).op.lan.obj Q)
      ((Grothendieck.ι C.underlying (Opposite.op n)).op.lanUnit.app Q : Q ⟶ _)
      (Opposite.op ((Grothendieck.ι C.underlying (Opposite.op m)).obj V)))

end CategoryTheory.CocontinuousSimplicialSite

end
