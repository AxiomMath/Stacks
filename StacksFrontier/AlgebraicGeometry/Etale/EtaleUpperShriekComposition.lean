module

public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Composition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateOfNatIsoLeft

import StacksCore.Tactic.StacksAttribute

/-!
# Upper shriek and inverse image along a composite of étale morphisms

Let `j : U ⟶ X` and `j' : V ⟶ U` be étale morphisms. The inverse images satisfy
`(j ∘ j')^{-1} = (j')^{-1} ∘ j^{-1}`, through the associativity of composition of the small étale
sites, and the upper shriek functors satisfy `(j ∘ j')^! = (j')^! ∘ j^!` by Stacks 0F5B. Under
the identifications `j^! = j^{-1}` of Stacks 0F5A the two isomorphisms agree. This is Stacks 0F5C,
whose proof the source omits.

## Main definitions

* `AlgebraicGeometry.abelianRestrictionCompIso` — `(j ∘ j')^{-1} ≅ (j')^{-1} ∘ j^{-1}` on abelian
  étale sheaves.
* `AlgebraicGeometry.abelianExtensionByZeroCompIso` — `j_! ∘ j'_! ≅ (j ∘ j')_!` for extension by
  zero of abelian étale sheaves, the conjugate isomorphism of left adjoints.

## Main results

* `AlgebraicGeometry.SmallEtale.compFiberStalksMap_fiberStalkOf` — the regrouping of the
  geometric fibre of a composite carries the summand of a point `x̄` to the summand of `x̄` inside
  the summand of its image.
* `AlgebraicGeometry.pushStalkMap_comp_pushStalkMap` — the stalk maps induced along two
  composable étale morphisms compose to the stalk map induced along the composite.
* `AlgebraicGeometry.extensionStalk_hom_ext` — maps out of a stalk of an extension by zero are
  determined on the summands of the stalk decomposition.
* `AlgebraicGeometry.SmallEtale.conjugateEquiv_fShriekCompIso_inv` — for étale morphisms the
  composition isomorphism of Stacks 0F6T is conjugate to the composition isomorphism of the
  inverse images, under the adjunctions `j_! ⊣ j^{-1}` of Stacks 0F6Q and 03S3.
* `AlgebraicGeometry.SmallEtale.upperShriekCompIso_etaleUpperShriekIsoRestriction` —
  **Stacks 0F5C**.

## Implementation notes

All four isomorphisms of the statement are conjugates. The isomorphism of Stacks 0F5B is
conjugate to the inverse of the composition isomorphism `(j ∘ j')_! ≅ j_! ∘ j'_!` of Stacks
0F6T, and the isomorphism `j^! = j^{-1}` of Stacks 0F5A is conjugate to the identity of `j_!`,
under the two adjunctions `j_! ⊣ j^!` and `j_! ⊣ j^{-1}`. Mathlib's calculus of mates
(`CategoryTheory.conjugateEquiv_comp`, `CategoryTheory.conjugateEquiv_whiskerLeft`,
`CategoryTheory.conjugateEquiv_whiskerRight`) therefore reduces the statement to the single
geometric input that the composition isomorphism of the inverse images is the conjugate of the
composition isomorphism of Stacks 0F6T as well, which is
`AlgebraicGeometry.SmallEtale.conjugateEquiv_fShriekCompIso_inv`.

That input is checked on geometric stalks. The stalk of `j_! j'_! F` at a geometric point `s̄`
of `X` is the direct sum of the stalks of `F` at the points of `V` over `s̄`, by Stacks 0F5F
applied twice, and on the summand of such a point both sides are the summand inclusion: for the
composition isomorphism of Stacks 0F6T this is its property (3), and for the conjugate of the
composition isomorphism of the inverse images it is the fact that the summand inclusions are the
units of the extension-by-zero adjunctions read on stalks, with the composite of two such units
the unit along the composite.

## References

* [Stacks Project, Tag 0F5C](https://stacks.math.columbia.edu/tag/0F5C)
* [Stacks Project, Tag 0F5B](https://stacks.math.columbia.edu/tag/0F5B)
* [Stacks Project, Tag 0F5A](https://stacks.math.columbia.edu/tag/0F5A)
* [Stacks Project, Tag 0F6T](https://stacks.math.columbia.edu/tag/0F6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

open scoped DirectSum

universe u v

namespace AlgebraicGeometry

namespace SmallEtale

section Regrouping

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (s : GeometricPoint Z.obj)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The regrouping of the geometric fibre of `f ≫ g` over that of `g` carries the summand of the
point of the geometric fibre of `f ≫ g` determined by `y` over `g` and `x` over `y` to the summand
of `x` in the stalk of `f_! F` at `y`, read in the summand of `y`. -/
public theorem compFiberStalksMap_fiberStalkOf (y : GeometricFiberPoint B g s)
    (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    fiberStalkOf.{u, v} B (f ≫ g) s F (compFiberPointOf B f g s y x) ≫
        AddCommGrpCat.ofHom (compFiberStalksMap.{u, v} B f g s F) =
      fiberStalkOf.{u, v} B f (y.toGeometricPoint B g s) F x ≫
        (fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).inv ≫
          fiberStalkOf.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F) y := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨x, hx⟩ := x
  revert x
  refine fun (x : s.source ⟶ X.obj) (hx : x ≫ B.inclusion.map f = y) => ?_
  subst hx
  refine ConcreteCategory.hom_ext _ _ fun b => ?_
  let := Classical.decEq (GeometricFiberPoint B (f ≫ g) s)
  change compFiberStalksMap.{u, v} B f g s F
    (DirectSum.of (fun r : GeometricFiberPoint B (f ≫ g) s =>
      ↑(etaleStalk B X.obj X.property (r.toGeometricPoint B (f ≫ g) s) F.obj))
      (compFiberPointOf B f g s _ _) b) = _
  simp only [compFiberStalksMap, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
  rfl

end Regrouping

end SmallEtale

section Restriction

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX) (V : SmallEtale B U.obj.left.1 U.obj.left.property)

/-- **Inverse image of abelian étale sheaves composes.** Restricting from `X` to `U` and then from
`U` to `V` is restricting from `X` to the composite `V ⟶ X`: the identification
`(j ∘ j')^{-1} ≅ (j')^{-1} ∘ j^{-1}` induced by the associativity of composition of the small
étale sites. -/
public def abelianRestrictionCompIso :
    abelianRestriction B X hX U ⋙ abelianRestriction B U.obj.left.1 U.obj.left.property V ≅
      abelianRestriction B X hX (smallEtaleCompObject B X hX U V) :=
  Functor.sheafPushforwardContinuousComp' (smallEtalePostcomposeCompIso B X hX U V)
    AddCommGrpCat.{u + 1}
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- The composition isomorphism of the inverse images on sections: over an étale `N ⟶ V`, it is
the restriction along the identification of `N` viewed over `X` through `U` with `N` viewed over
`X` directly. -/
public theorem abelianRestrictionCompIso_hom_app_hom_app
    (H : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (N : SmallEtale B V.obj.left.1 V.obj.left.property) :
    ((abelianRestrictionCompIso B X hX U V).hom.app H).hom.app (op N) =
      H.obj.map ((smallEtalePostcomposeCompIso B X hX U V).inv.app N).op :=
  rfl

variable (s : GeometricPoint X) (x : geometricPointLifts B X hX U s)
  (y : geometricPointLifts B U.obj.left.1 U.obj.left.property V
    (geometricPointOfLift B X hX U s x))

/-- **The stalk maps along two composable étale morphisms compose.** For `α : F ⟶ j'^{-1} G` and
`β : G ⟶ j^{-1} H`, the stalk map induced by `α` at a lift `y` of a lift `x` of `s̄`, followed
by the stalk map induced by `β` at `x`, is the stalk map induced at the composite lift by the
composite `F ⟶ j'^{-1} j^{-1} H ≅ (j ∘ j')^{-1} H`. -/
public theorem pushStalkMap_comp_pushStalkMap
    (H : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (F : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) AddCommGrpCat.{u + 1})
    (α : F ⟶ (abelianRestriction B U.obj.left.1 U.obj.left.property V).obj G)
    (β : G ⟶ (abelianRestriction B X hX U).obj H) :
    pushStalkMap B U.obj.left.1 U.obj.left.property V (geometricPointOfLift B X hX U s x) y G F
        α ≫ pushStalkMap B X hX U s x H G β =
      pushStalkMap B X hX (smallEtaleCompObject B X hX U V) s
        (pushLift B X hX U s V x y) H F
        (α ≫ (abelianRestriction B U.obj.left.1 U.obj.left.property V).map β ≫
          (abelianRestrictionCompIso B X hX U V).hom.app H) := by
  refine colimit.hom_ext fun N => ?_
  have h1 := pushStalkMap_germ B U.obj.left.1 U.obj.left.property V
    (geometricPointOfLift B X hX U s x) y G F α N.unop.1 N.unop.2
  have h2 := pushStalkMap_germ B X hX U s x H G β
    ((smallEtalePostcompose B U.obj.left.1 U.obj.left.property V).obj N.unop.1)
    (pushLift B U.obj.left.1 U.obj.left.property V _ N.unop.1 y N.unop.2)
  have h3 := pushStalkMap_germ B X hX (smallEtaleCompObject B X hX U V) s
    (pushLift B X hX U s V x y) H F
    (α ≫ (abelianRestriction B U.obj.left.1 U.obj.left.property V).map β ≫
      (abelianRestrictionCompIso B X hX U V).hom.app H) N.unop.1 N.unop.2
  let A₁ : (geometricPointFiber B X hX s).Elements :=
    (geometricPointFiber B X hX s).elementsMk
      ((smallEtalePostcompose B X hX (smallEtaleCompObject B X hX U V)).obj N.unop.1)
      (pushLift B X hX (smallEtaleCompObject B X hX U V) s N.unop.1
        (pushLift B X hX U s V x y) N.unop.2)
  let A₂ : (geometricPointFiber B X hX s).Elements :=
    (geometricPointFiber B X hX s).elementsMk
      ((smallEtalePostcompose B X hX U).obj
        ((smallEtalePostcompose B U.obj.left.1 U.obj.left.property V).obj N.unop.1))
      (pushLift B X hX U s _ x
        (pushLift B U.obj.left.1 U.obj.left.property V _ N.unop.1 y N.unop.2))
  let m : A₁ ⟶ A₂ :=
    Functor.Elements.homMk ((smallEtalePostcomposeCompIso B X hX U V).inv.app N.unop.1)
      (Subtype.ext (Category.comp_id _))
  have hw := colimit.w (SmallEtale.etaleStalkDiagram B X hX s H.obj) m.op
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((congrArg (· ≫ pushStalkMap B X hX U s x H G β) h1).trans
    ((Category.assoc _ _ _).trans (congrArg (α.hom.app _ ≫ ·) h2))).trans ?_
  refine Eq.trans ?_ h3.symm
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (α.hom.app _ ≫ ·) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (β.hom.app _ ≫ ·) hw.symm

/-- **Extension by zero of abelian étale sheaves composes.** Extending by zero from `V` to `U`
and then from `U` to `X` is extending by zero from the composite `V ⟶ X`: the two functors are
left adjoint to the two sides of `AlgebraicGeometry.abelianRestrictionCompIso`, and this is the
isomorphism of left adjoints conjugate to it. -/
public def abelianExtensionByZeroCompIso :
    abelianExtensionByZero B U.obj.left.1 U.obj.left.property V ⋙
        abelianExtensionByZero B X hX U ≅
      abelianExtensionByZero B X hX (smallEtaleCompObject B X hX U V) :=
  Adjunction.leftAdjointCompIso
    (abelianExtensionByZeroAdjunction B U.obj.left.1 U.obj.left.property V)
    (abelianExtensionByZeroAdjunction B X hX U)
    (abelianExtensionByZeroAdjunction B X hX (smallEtaleCompObject B X hX U V))
    (abelianRestrictionCompIso B X hX U V)

/-- The composition isomorphism of extensions by zero is conjugate to the inverse of the
composition isomorphism of the inverse images. -/
public theorem conjugateEquiv_abelianExtensionByZeroCompIso_hom :
    conjugateEquiv (abelianExtensionByZeroAdjunction B X hX (smallEtaleCompObject B X hX U V))
        ((abelianExtensionByZeroAdjunction B U.obj.left.1 U.obj.left.property V).comp
          (abelianExtensionByZeroAdjunction B X hX U))
        (abelianExtensionByZeroCompIso B X hX U V).hom =
      (abelianRestrictionCompIso B X hX U V).inv :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply
    (abelianRestrictionCompIso B X hX U V).symm)

/-- The units of the extension-by-zero adjunctions are compatible with composition: the unit
along `V ⟶ U` followed by the restriction of the unit along `U ⟶ X` and the composition
isomorphism of the inverse images is the unit along `V ⟶ X`, followed by the restriction of the
composition isomorphism of the extensions by zero. -/
public theorem abelianExtensionByZeroAdjunction_unit_comp
    (F : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) AddCommGrpCat.{u + 1}) :
    (abelianExtensionByZeroAdjunction B U.obj.left.1 U.obj.left.property V).unit.app F ≫
        (abelianRestriction B U.obj.left.1 U.obj.left.property V).map
          ((abelianExtensionByZeroAdjunction B X hX U).unit.app
            ((abelianExtensionByZero B U.obj.left.1 U.obj.left.property V).obj F)) ≫
        (abelianRestrictionCompIso B X hX U V).hom.app _ ≫
        (abelianRestriction B X hX (smallEtaleCompObject B X hX U V)).map
          ((abelianExtensionByZeroCompIso B X hX U V).hom.app F) =
      (abelianExtensionByZeroAdjunction B X hX (smallEtaleCompObject B X hX U V)).unit.app F := by
  have h := unit_conjugateEquiv
    (abelianExtensionByZeroAdjunction B X hX (smallEtaleCompObject B X hX U V))
    ((abelianExtensionByZeroAdjunction B U.obj.left.1 U.obj.left.property V).comp
      (abelianExtensionByZeroAdjunction B X hX U))
    (abelianExtensionByZeroCompIso B X hX U V).hom F
  rw [conjugateEquiv_abelianExtensionByZeroCompIso_hom, Adjunction.comp_unit_app] at h
  rw [← (abelianRestrictionCompIso B X hX U V).hom.naturality]
  have h' := congrArg (· ≫ (abelianRestrictionCompIso B X hX U V).hom.app
    ((abelianExtensionByZero B X hX (smallEtaleCompObject B X hX U V)).obj F)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at h'
  exact h'.symm

/-- The stalk map induced by a morphism `G ⟶ j^{-1} H` is natural in `G`. -/
public theorem pushStalkMap_precomp
    (H : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    {G G' : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}}
    (α : G ⟶ G') (β : G' ⟶ (abelianRestriction B X hX U).obj H) :
    pushStalkMap B X hX U s x H G (α ≫ β) =
      colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber
          B U.obj.left.1 U.obj.left.property (geometricPointOfLift B X hX U s x))).op α.1) ≫
        pushStalkMap B X hX U s x H G' β := by
  refine colimit.hom_ext fun N => ?_
  refine (pushStalkMap_germ B X hX U s x H G (α ≫ β) N.unop.1 N.unop.2).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ pushStalkMap B X hX U s x H G' β)
    (colimit.ι_map _ N).symm)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact (Category.assoc _ _ _).trans (congrArg (α.hom.app _ ≫ ·)
    (pushStalkMap_germ B X hX U s x H G' β N.unop.1 N.unop.2).symm)

/-- The summand inclusion `G_x̄ ⟶ (j_! G)_s̄` of the stalk decomposition of extension by zero,
given by the unit of `j_! ⊣ j^{-1}`, is natural in the sheaf `G` on `U`. -/
public theorem extensionUnitStalkMap_naturality
    {G G' : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}} (α : G ⟶ G') :
    extensionUnitStalkMap B X hX U s x G ≫
        colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X hX s)).op
          ((abelianExtensionByZero B X hX U).map α).1) =
      colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber
          B U.obj.left.1 U.obj.left.property (geometricPointOfLift B X hX U s x))).op α.1) ≫
        extensionUnitStalkMap B X hX U s x G' := by
  refine (pushStalkMap_comp B X hX U s x G _ _).trans ?_
  rw [(abelianExtensionByZeroAdjunction B X hX U).unit_naturality]
  exact pushStalkMap_precomp B X hX U s x _ α _

/-- **The summand inclusions of a composite.** The summand inclusion of the stalk decomposition of
extension by zero along `V ⟶ U`, at a lift `y` of a lift `x` of `s̄`, followed by the summand
inclusion along `U ⟶ X` at `x` and the composition isomorphism of extensions by zero, is the
summand inclusion along the composite at the composite lift. -/
public theorem extensionUnitStalkMap_comp_extensionUnitStalkMap
    (F : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) AddCommGrpCat.{u + 1}) :
    extensionUnitStalkMap B U.obj.left.1 U.obj.left.property V
          (geometricPointOfLift B X hX U s x) y F ≫
        extensionUnitStalkMap B X hX U s x
          ((abelianExtensionByZero B U.obj.left.1 U.obj.left.property V).obj F) ≫
        colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X hX s)).op
          ((abelianExtensionByZeroCompIso B X hX U V).hom.app F).1) =
      extensionUnitStalkMap B X hX (smallEtaleCompObject B X hX U V) s
        (pushLift B X hX U s V x y) F := by
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (pushStalkMap_comp_pushStalkMap B X hX U V s x y _ _ F _ _))).trans ?_
  refine (pushStalkMap_comp B X hX (smallEtaleCompObject B X hX U V) s _ F _ _).trans ?_
  refine congrArg (pushStalkMap B X hX (smallEtaleCompObject B X hX U V) s
    (pushLift B X hX U s V x y) _ F) ?_
  simpa only [Category.assoc] using abelianExtensionByZeroAdjunction_unit_comp B X hX U V F

/-- The summand inclusion of the stalk decomposition of extension by zero, followed by the
comparison with `j_!`, is the summand of the geometric fibre of `j` read in the stalk of `j_! G`. -/
private theorem extensionUnitStalkMap_comp_fShriekStalkIso_inv
    (G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) :
    extensionUnitStalkMap B X hX U s x G ≫
        (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map
          ((sheafToPresheaf _ _).map
            ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).hom.app G)) =
      SmallEtale.fiberStalkOf.{u, u + 1} B U.obj.hom s G x ≫
        (SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G).inv :=
  (fShriekStalkSummand_eq_extensionUnitStalkMap B X hX U s x G).symm

/-- Two maps out of the stalk of an extension by zero `j_! G` at a geometric point `s̄` agree as
soon as they agree on the summand of every lift of `s̄`, the summand inclusions being given by the
unit of `j_! ⊣ j^{-1}`. -/
public theorem extensionStalk_hom_ext
    {G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}}
    {M : AddCommGrpCat.{u + 1}}
    {a b : etaleStalk B X hX s ((abelianExtensionByZero B X hX U).obj G).obj ⟶ M}
    (h : ∀ x : geometricPointLifts B X hX U s,
      extensionUnitStalkMap B X hX U s x G ≫ a = extensionUnitStalkMap B X hX U s x G ≫ b) :
    a = b := by
  let θ : etaleStalk B X hX s ((abelianExtensionByZero B X hX U).obj G).obj ≅
      AddCommGrpCat.of (SmallEtale.fiberStalks.{u, u + 1} B U.obj.hom s G) :=
    (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).mapIso
        ((sheafToPresheaf _ _).mapIso
          ((SmallEtale.abelianExtensionByZeroIsoFShriek B X hX U).app G)) ≪≫
      SmallEtale.fShriekStalkIso.{u, u + 1} B U.obj.hom s G
  have hθ : ∀ x : SmallEtale.GeometricFiberPoint B U.obj.hom s,
      SmallEtale.fiberStalkOf.{u, u + 1} B U.obj.hom s G x ≫ θ.inv =
        extensionUnitStalkMap B X hX U s x G := fun x =>
    (Iso.comp_inv_eq _).2 (extensionUnitStalkMap_comp_fShriekStalkIso B X hX U s G x).symm
  refine (cancel_epi θ.inv).1 (SmallEtale.fiberStalks_hom_ext.{u, u + 1} B U.obj.hom s
    fun x z => ?_)
  have hx := congrArg (· ≫ a) (hθ x)
  have hx' := congrArg (· ≫ b) (hθ x)
  simp only [Category.assoc] at hx hx'
  exact ConcreteCategory.congr_hom (hx.trans ((h x).trans hx'.symm)) z

end Restriction

namespace SmallEtale

section Etale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX) (V : SmallEtale B U.obj.left.1 U.obj.left.property)

/-- For étale morphisms, the composition isomorphism `(j ∘ j')_! ≅ j_! ∘ j'_!` of Stacks 0F6T
and the composition isomorphism of extensions by zero agree under the identifications of
Stacks 0F6Q of extension by zero with the direct image with compact support. -/
public theorem abelianExtensionByZeroCompIso_hom_comp_fShriekCompIso_hom :
    (abelianExtensionByZeroCompIso B X hX U V).hom ≫
        (abelianExtensionByZeroIsoFShriek B X hX (smallEtaleCompObject B X hX U V)).hom ≫
          (fShriekCompIso.{u, u + 1} B V.obj.hom U.obj.hom).hom =
      whiskerRight (abelianExtensionByZeroIsoFShriek B U.obj.left.1 U.obj.left.property V).hom
          (abelianExtensionByZero B X hX U) ≫
        whiskerLeft (fShriekFunctor.{u, u + 1} B V.obj.hom)
          (abelianExtensionByZeroIsoFShriek B X hX U).hom := by
  ext F : 2
  refine (jointlyFaithful_etaleStalkSheafFiber.{u, u + 1} B X hX).map_injective fun s => ?_
  refine extensionStalk_hom_ext B X hX U s fun x => ?_
  refine extensionStalk_hom_ext B U.obj.left.1 U.obj.left.property V
    (geometricPointOfLift B X hX U s x) fun y => ?_
  simp only [NatTrans.comp_app, Functor.map_comp, whiskerRight_app, whiskerLeft_app]
  let Φ := (geometricPointSitePoint B X hX s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let t := geometricPointOfLift B X hX U s x
  let Ψ := (geometricPointSitePoint B U.obj.left.1 U.obj.left.property t).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  let eU := abelianExtensionByZeroIsoFShriek B X hX U
  let eV := abelianExtensionByZeroIsoFShriek B U.obj.left.1 U.obj.left.property V
  let eW := abelianExtensionByZeroIsoFShriek B X hX (smallEtaleCompObject B X hX U V)
  have hR1 : extensionUnitStalkMap B X hX U s x
        ((abelianExtensionByZero B U.obj.left.1 U.obj.left.property V).obj F) ≫
        Φ.map ((abelianExtensionByZero B X hX U).map (eV.hom.app F)) =
      Ψ.map (eV.hom.app F) ≫
        extensionUnitStalkMap B X hX U s x ((fShriekFunctor.{u, u + 1} B V.obj.hom).obj F) :=
    extensionUnitStalkMap_naturality B X hX U s x _
  have hR2 := extensionUnitStalkMap_comp_fShriekStalkIso_inv B X hX U s x
    ((fShriekFunctor.{u, u + 1} B V.obj.hom).obj F)
  have hR3 := extensionUnitStalkMap_comp_fShriekStalkIso_inv B U.obj.left.1
    U.obj.left.property V t y F
  have hL1 : extensionUnitStalkMap B U.obj.left.1 U.obj.left.property V t y F ≫
        extensionUnitStalkMap B X hX U s x
          ((abelianExtensionByZero B U.obj.left.1 U.obj.left.property V).obj F) ≫
        Φ.map ((abelianExtensionByZeroCompIso B X hX U V).hom.app F) =
      extensionUnitStalkMap B X hX (smallEtaleCompObject B X hX U V) s
        (pushLift B X hX U s V x y) F :=
    extensionUnitStalkMap_comp_extensionUnitStalkMap B X hX U V s x y F
  have hL2 := extensionUnitStalkMap_comp_fShriekStalkIso_inv B X hX
    (smallEtaleCompObject B X hX U V) s (pushLift B X hX U s V x y) F
  have hL3 : (fShriekStalkIso.{u, u + 1} B (V.obj.hom ≫ U.obj.hom) s F).inv ≫
        Φ.map ((fShriekCompIso.{u, u + 1} B V.obj.hom U.obj.hom).hom.app F) =
      AddCommGrpCat.ofHom (compFiberStalksMap.{u, u + 1} B V.obj.hom U.obj.hom s F) ≫
        (fShriekStalkIso.{u, u + 1} B U.obj.hom s
          ((fShriekFunctor.{u, u + 1} B V.obj.hom).obj F)).inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2
      (fShriekCompIso_stalk.{u, u + 1} B V.obj.hom U.obj.hom s F)).trans (Category.assoc _ _ _))
  have hL4 := compFiberStalksMap_fiberStalkOf.{u, u + 1} B V.obj.hom U.obj.hom s F x y
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hL1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hL2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hL3).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hL4).trans ?_
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _))
  refine Eq.trans ?_ (congrArg (_ ≫ · ≫ _) hR1.symm)
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _)).symm
  refine Eq.trans ?_ (congrArg (_ ≫ _ ≫ ·) hR2.symm)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _) hR3.symm)
  simp only
  rfl

/-- **For étale morphisms the composition isomorphism of Stacks 0F6T is conjugate to the
composition isomorphism of the inverse images.** Under the adjunctions `j_! ⊣ j^{-1}` of Stacks
03S3 and 0F6Q, the inverse of `(j ∘ j')_! ≅ j_! ∘ j'_!` has as conjugate the inverse of
`(j ∘ j')^{-1} ≅ (j')^{-1} ∘ j^{-1}`. -/
public theorem conjugateEquiv_fShriekCompIso_inv :
    conjugateEquiv (fShriekAdjunctionRestriction B X hX (smallEtaleCompObject B X hX U V))
        ((fShriekAdjunctionRestriction B U.obj.left.1 U.obj.left.property V).comp
          (fShriekAdjunctionRestriction B X hX U))
        (fShriekCompIso.{u, u + 1} B V.obj.hom U.obj.hom).inv =
      (abelianRestrictionCompIso B X hX U V).inv := by
  have hc : (fShriekCompIso.{u, u + 1} B V.obj.hom U.obj.hom).inv =
      whiskerLeft (fShriekFunctor.{u, u + 1} B V.obj.hom)
          (abelianExtensionByZeroIsoFShriek B X hX U).inv ≫
        whiskerRight (abelianExtensionByZeroIsoFShriek B U.obj.left.1 U.obj.left.property V).inv
          (abelianExtensionByZero B X hX U) ≫
        (abelianExtensionByZeroCompIso B X hX U V).hom ≫
        (abelianExtensionByZeroIsoFShriek B X hX (smallEtaleCompObject B X hX U V)).hom := by
    rw [← cancel_mono (fShriekCompIso.{u, u + 1} B V.obj.hom U.obj.hom).hom, Iso.inv_hom_id]
    simp only [Category.assoc]
    rw [abelianExtensionByZeroCompIso_hom_comp_fShriekCompIso_hom]
    ext F : 2
    simp
  rw [hc]
  simp only [fShriekAdjunctionRestriction]
  rw [← conjugateEquiv_comp _ ((abelianExtensionByZeroAdjunction B U.obj.left.1
      U.obj.left.property V).ofNatIsoLeft (abelianExtensionByZeroIsoFShriek B U.obj.left.1
      U.obj.left.property V) |>.comp (abelianExtensionByZeroAdjunction B X hX U)),
    ← conjugateEquiv_comp _ ((abelianExtensionByZeroAdjunction B U.obj.left.1
      U.obj.left.property V).comp (abelianExtensionByZeroAdjunction B X hX U)),
    ← conjugateEquiv_comp _
      (abelianExtensionByZeroAdjunction B X hX (smallEtaleCompObject B X hX U V)),
    Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft_hom,
    conjugateEquiv_abelianExtensionByZeroCompIso_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft, Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft_right,
    Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft_right, Iso.hom_inv_id, Iso.hom_inv_id,
    conjugateEquiv_id, conjugateEquiv_id]
  simp

/-- **Stacks 0F5C.** Let `j : U ⟶ X` and `j' : V ⟶ U` be étale morphisms. The isomorphism
`(j ∘ j')^! ≅ (j')^! ∘ j^!` of Stacks 0F5B and the isomorphism
`(j ∘ j')^{-1} ≅ (j')^{-1} ∘ j^{-1}` of the inverse images agree via the isomorphisms
`j^! ≅ j^{-1}` of Stacks 0F5A: the square
`(j ∘ j')^! → (j')^! ∘ j^! → (j')^! ∘ j^{-1} → (j')^{-1} ∘ j^{-1}` equals
`(j ∘ j')^! → (j ∘ j')^{-1} → (j')^{-1} ∘ j^{-1}`. Here `j` is an object `U` of the small étale
site of `X`, `j'` an object `V` of the small étale site of `U`, and `j ∘ j'` is `V` viewed as an
object of the small étale site of `X`, `AlgebraicGeometry.smallEtaleCompObject`. -/
@[stacks 0F5C "(j ∘ j')^! = (j')^! ∘ j^! agrees with (j ∘ j')^{-1} = (j')^{-1} ∘ j^{-1}"]
public theorem upperShriekCompIso_etaleUpperShriekIsoRestriction :
    upperShriekCompIso.{u, u + 1} B V.obj.hom U.obj.hom ≪≫
        isoWhiskerRight (etaleUpperShriekIsoRestriction B X hX U)
          (fUpperShriekFunctor.{u, u + 1} B V.obj.hom) ≪≫
        isoWhiskerLeft (abelianRestriction B X hX U)
          (etaleUpperShriekIsoRestriction B U.obj.left.1 U.obj.left.property V) =
      etaleUpperShriekIsoRestriction B X hX (smallEtaleCompObject B X hX U V) ≪≫
        (abelianRestrictionCompIso B X hX U V).symm := by
  ext1
  change conjugateEquiv _ _ _ ≫ whiskerRight (conjugateEquiv _ _ (𝟙 _)) _ ≫
      whiskerLeft _ (conjugateEquiv _ _ (𝟙 _)) = conjugateEquiv _ _ (𝟙 _) ≫ _
  rw [← conjugateEquiv_whiskerLeft _ _ (fShriekAdjunction.{u, u + 1} B V.obj.hom),
    ← conjugateEquiv_whiskerRight _ _ (fShriekAdjunctionRestriction B X hX U),
    conjugateEquiv_comp, conjugateEquiv_comp]
  simp only [Iso.symm_hom]
  rw [← conjugateEquiv_fShriekCompIso_inv, conjugateEquiv_comp]
  simp

end Etale

end SmallEtale

end AlgebraicGeometry

end
