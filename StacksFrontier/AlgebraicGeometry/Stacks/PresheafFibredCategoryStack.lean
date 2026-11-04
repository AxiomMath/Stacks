module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.StackTransport

/-!
# The fibred category of an algebraic space is a stack, at the universe of a quotient stack

Let `X` be an algebraic space over a scheme `S` of a big fppf site. Regarding `X` as a presheaf of
sets makes it a category fibred in sets over the big fppf site of `S`
(`AlgebraicGeometry.Stack.fibredCategory`), and it is a stack exactly because `X` is a sheaf: this
is Stacks 0430 for the category of elements.

The morphisms of that category live in the hom universe of the site, one below those of a quotient
stack, which is a stackification and therefore has its morphisms raised. A statement comparing the
two — the 2-cartesian square of Stacks 04M9, or the extension of a 1-morphism along the
stackification — needs both in one bicategory. This file records the fibred category of an
algebraic space with its morphisms raised to the quotient stack's universe, and that the result is
still a stack.

## Main definitions

* `AlgebraicGeometry.Stack.liftedFibredCategory`: the category fibred in sets of an algebraic
  space, with its morphisms raised one universe.
* `AlgebraicGeometry.Stack.liftedFibredCategoryDown` and
  `AlgebraicGeometry.Stack.liftedFibredCategoryUp`: the canonical equivalence back down, and its
  inverse.

## Main results

* `AlgebraicGeometry.Stack.liftedFibredCategory_isStack`: it is a stack in the sense of
  Stacks 026F, which is the form the universal property of stackification (Stacks 0435, 0436)
  consumes.
* `AlgebraicGeometry.Stack.isStackInGroupoids_liftedFibredCategory`: it is a stack in groupoids in
  the sense of Stacks 02ZI, which is the form the 2-category of stacks in groupoids asks for.

## Implementation notes

Raising the hom universe is `CategoryTheory.ULiftHom`, which leaves the objects alone; the
alternative, `CategoryTheory.BasedCategory.ulift`, also lifts the objects and would make the
comparison with the quotient stack's object universe an extra step.

Only the sheaf property of the algebraic space is used. The route is Stacks 0430
(`CategoryTheory.Functor.isStackInSets_iff_isSheaf_objPresheaf`) applied twice: once to Mathlib's
category of elements `CategoryTheory.CategoryOfElements.π`, whose presheaf of objects is the
presheaf itself, and once to its universe-raised form, whose presheaf of objects is the same
because `CategoryTheory.ULiftHom` does not change the objects and the chosen pullback in a
category fibred in sets is unique. The fibred category of the presheaf is then identified with
that category of elements by an equivalence over the site, and the stack condition transports
along it (Stacks 042W).

This material was extracted from
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientStackSquares/TwoFibreProduct.lean`, where
it was developed for Stacks 04M9. It lives here because the universal property of stackification
needs it one module earlier than the 2-cartesian square does: the extension of an `R`-invariant
morphism to the quotient stack
(`AlgebraicGeometry.Stack.quotientStackOfInvariant`) is stated about
`AlgebraicGeometry.Stack.quotientStackProjection`, which the square is built on top of.

## References

* [Stacks Project, Tag 0430](https://stacks.math.columbia.edu/tag/0430)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : C.Contains S} {B : AlgebraicSpaces C S hS}

universe u₀ v₀ w₀ v₁ w₁

private theorem elementsOpp_isFiberedInSets
    {D : Type u₀} [Category.{v₀} D] (F : Dᵒᵖ ⥤ Type w₀) :
    (CategoryOfElements.π F).leftOp.IsFiberedInSets := by
  let : Category.{v₀} F.Elements := CategoryTheory.categoryOfElements F
  refine ⟨fun {U V} f x hx => ?_⟩
  cases x with
  | op a =>
    rcases a with ⟨aU, asec⟩
    change aU.unop = U at hx
    obtain rfl := Opposite.unop_eq_iff_eq_op.mp hx
    let b : F.Elements := ⟨Opposite.op V, F.map f.op asec⟩
    let g := CategoryOfElements.homMk
      (⟨Opposite.op U, asec⟩ : F.Elements) b f.op rfl
    let φ : Opposite.op b ⟶ Opposite.op (⟨Opposite.op U, asec⟩ : F.Elements) :=
      Quiver.Hom.op g
    let yφ : Σ y : F.Elementsᵒᵖ, y ⟶
        Opposite.op (⟨Opposite.op U, asec⟩ : F.Elements) := ⟨Opposite.op b, φ⟩
    have hy : (CategoryOfElements.π F).leftOp.obj yφ.1 = V := rfl
    have hfac : (CategoryOfElements.π F).leftOp.map yφ.2 =
        eqToHom hy ≫ f ≫ eqToHom hx.symm := by
      simp [yφ, φ, g, b]
      rfl
    refine ⟨yφ, ⟨hy, hfac⟩, ?_⟩
    rintro ⟨z, ψ⟩ ⟨hz, hψ⟩
    cases z with
    | op z₀ =>
      rcases z₀ with ⟨zU, zsec⟩
      obtain rfl := Opposite.unop_eq_iff_eq_op.mp (show zU.unop = V from hz)
      have hbase : ψ.unop.val = f.op := by
        have h := congrArg Quiver.Hom.op hψ
        simpa [yφ, φ, g, b, hy, hz, hx, Functor.leftOp] using h
      obtain rfl : zsec = F.map f.op asec := by
        have hp := ψ.unop.property
        rw [hbase] at hp
        exact hp.symm
      dsimp [yφ, b]
      congr 1
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      exact hbase

private def elementsFiberEquiv {D : Type u₀} [Category.{v₀} D]
    (F : Dᵒᵖ ⥤ Type w₀) (U : D) :
    (CategoryOfElements.π F).leftOp.Fiber U ≃ F.obj (Opposite.op U) where
  toFun x := by
    rcases x with ⟨⟨⟨⟨V⟩, s⟩⟩, h⟩
    change V = U at h
    subst U
    exact s
  invFun s := ⟨Opposite.op ⟨Opposite.op U, s⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨⟨V⟩, s⟩⟩, h⟩
    change V = U at h
    subst U
    rfl
  right_inv s := rfl

private theorem elementsFiberEquiv_natural {D : Type u₀} [Category.{v₀} D]
    (F : Dᵒᵖ ⥤ Type w₀) {U V : D} (f : V ⟶ U)
    (x : (CategoryOfElements.π F).leftOp.Fiber U) :
    letI := elementsOpp_isFiberedInSets F
    elementsFiberEquiv F V ((Functor.objPresheaf (CategoryOfElements.π F).leftOp).map f.op x) =
      F.map f.op (elementsFiberEquiv F U x) := by
  let := elementsOpp_isFiberedInSets F
  let p := (CategoryOfElements.π F).leftOp
  let := (Functor.IsFiberedInSets.isFiberedInGroupoids p).isFibered
  rcases x with ⟨⟨⟨⟨U⟩, s⟩⟩, rfl⟩
  let x : p.Fiber U := ⟨Opposite.op ⟨Opposite.op U, s⟩, rfl⟩
  let y : p.Fiber V := ⟨Opposite.op ⟨Opposite.op V, F.map f.op s⟩, rfl⟩
  let φ : y.1 ⟶ x.1 := (CategoryOfElements.homMk _ _ f.op rfl).op
  have : p.IsHomLift f φ := IsHomLift.of_fac' p f φ rfl rfl (by simp [p, φ]; rfl)
  have hy : Functor.pullbackFiber p x f = y := Subtype.ext
    (Functor.IsFiberedInSets.eq_of_isHomLift p f
      (Functor.IsPreFibered.pullbackMap x.2 f) φ).choose
  show elementsFiberEquiv F V (Functor.pullbackFiber p x f) = F.map f.op s
  rw [hy]
  rfl

/-- A category fibred in sets whose presheaf of objects is naturally equivalent to a sheaf is a
stack. -/
private theorem isStack_of_natEquiv_isSheaf {D : Type u₀} [Category.{v₀} D]
    {E : Type w₁} [Category.{v₁} E] (p : E ⥤ D) [p.IsFiberedInSets]
    (J : GrothendieckTopology D) (P : Dᵒᵖ ⥤ Type w₀) (hP : Presheaf.IsSheaf J P)
    (e : ∀ {U : D}, p.Fiber U ≃ P.obj (Opposite.op U))
    (he : ∀ {U V : D} (f : V ⟶ U) (x : p.Fiber U),
      e ((Functor.objPresheaf p).map f.op x) = P.map f.op (e x)) : p.IsStack J := by
  let := (Functor.IsFiberedInSets.isFiberedInGroupoids p).isFibered
  apply Functor.IsStackInSets.isStack
  apply (Functor.isStackInSets_iff_isSheaf_objPresheaf p J).mpr
  rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
  exact (Presieve.isSheaf_iff_of_nat_equiv (P₁ := Functor.objPresheaf p) (P₂ := P)
    (fun {U} => e) fun {U V} f x => he f x).mpr hP

private theorem elementsOpp_isStack {D : Type u₀} [Category.{v₀} D]
    (J : GrothendieckTopology D) (F : Dᵒᵖ ⥤ Type w₀)
    (hF : Presheaf.IsSheaf J F) : (CategoryOfElements.π F).leftOp.IsStack J := by
  let := elementsOpp_isFiberedInSets F
  exact isStack_of_natEquiv_isSheaf _ J F hF (fun {U} => elementsFiberEquiv F U)
    fun f x => elementsFiberEquiv_natural F f x

/-- Raising the universe of the morphisms of a category fibred in sets leaves it fibred in
sets. -/
theorem isFiberedInSets_uliftHom {D : Type u₀} [Category.{v₀} D]
    {E : Type w₀} [Category.{v₁} E] (p : E ⥤ D) [p.IsFiberedInSets] :
    ((ULiftHom.down : ULiftHom.{w₁} E ⥤ E) ⋙ p).IsFiberedInSets := by
  refine ⟨fun f x hx => ?_⟩
  obtain ⟨⟨y, φ⟩, ⟨hy, hφ⟩, huniq⟩ :=
    Functor.IsFiberedInSets.existsUnique_lift (p := p) f x.objDown hx
  refine ⟨⟨ULiftHom.objUp y, ⟨φ⟩⟩, ⟨hy, hφ⟩, ?_⟩
  rintro ⟨z, ψ⟩ ⟨hz, hψ⟩
  have he := huniq ⟨z.objDown, ψ.down⟩ ⟨hz, hψ⟩
  obtain ⟨hobj, hhom⟩ := Sigma.mk.inj_iff.mp he
  cases hobj
  have heq := eq_of_heq hhom
  cases ψ
  cases heq
  rfl

/-- The projection from the opposite of the category of elements of a presheaf is faithful. -/
private theorem faithful_categoryOfElements_π_leftOp {D : Type u₀} [Category.{v₀} D]
    (F : Dᵒᵖ ⥤ Type w₀) : (CategoryOfElements.π F).leftOp.Faithful := by
  refine ⟨fun h => ?_⟩
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg Quiver.Hom.op h

private theorem isStack_uliftHom {D : Type u₀} [Category.{v₀} D]
    {E : Type w₀} [Category.{v₁} E] (p : E ⥤ D) [p.IsFiberedInSets]
    (J : GrothendieckTopology D) (hp : p.IsStack J) :
    ((ULiftHom.down : ULiftHom.{w₁} E ⥤ E) ⋙ p).IsStack J := by
  let q := (ULiftHom.down : ULiftHom.{w₁} E ⥤ E) ⋙ p
  let : q.IsFiberedInSets := isFiberedInSets_uliftHom p
  let : p.IsFibered := (Functor.IsFiberedInSets.isFiberedInGroupoids p).isFibered
  let : q.IsFibered := (Functor.IsFiberedInSets.isFiberedInGroupoids q).isFibered
  have hsheaf := (Functor.isStackInSets_iff_isSheaf_objPresheaf p J).mp
    ⟨hp, fun U => inferInstance⟩
  refine isStack_of_natEquiv_isSheaf q J (Functor.objPresheaf p) hsheaf
    (fun {U} => Equiv.refl _) ?_
  intro V U f x
  have hxp : p.obj ((ULiftHom.down : ULiftHom.{w₁} E ⥤ E).obj x.1) = V := x.2
  have hdown : p.IsHomLift f
      ((ULiftHom.down : ULiftHom.{w₁} E ⥤ E).map
        (Functor.IsPreFibered.pullbackMap (p := q) x.2 f)) :=
    Functor.isHomLift_map_of_comp_eq
      (show (ULiftHom.down : ULiftHom.{w₁} E ⥤ E) ⋙ p = q from rfl) f _
  exact Subtype.ext (Functor.IsFiberedInSets.eq_of_isHomLift p f
    ((ULiftHom.down : ULiftHom.{w₁} E ⥤ E).map
      (Functor.IsPreFibered.pullbackMap (p := q) x.2 f))
    (Functor.IsPreFibered.pullbackMap (p := p) hxp f)).choose

private def pointsToElements
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    (fibredCategory C S hS F).val.obj ⥤ F.Elementsᵒᵖ where
  obj x := Opposite.op ⟨Opposite.op x.base, x.fiber.as⟩
  map f := (CategoryOfElements.homMk _ _ f.base.op
    (Discrete.eq_of_hom f.fiber).symm).op
  map_id x := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    rfl

private def elementsToPoints
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    F.Elementsᵒᵖ ⥤ (fibredCategory C S hS F).val.obj where
  obj x := ⟨x.unop.1.unop, Discrete.mk x.unop.2⟩
  map f := ⟨f.unop.val.unop, eqToHom (congrArg Discrete.mk f.unop.property.symm)⟩
  map_id x := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext
      (F := ((F ⋙ CategoryTheory.typeToGrpd) ⋙ Grpd.forgetToCat).toPseudofunctor') _ _ ?_ ?_
    · rfl
    · exact Discrete.hom_eq
  map_comp f g := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext
      (F := ((F ⋙ CategoryTheory.typeToGrpd) ⋙ Grpd.forgetToCat).toPseudofunctor') _ _ ?_ ?_
    · rfl
    · exact Discrete.hom_eq

private abbrev liftedPointsBasedCategory
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    BasedCategory.{u + 1, u + 1} (BigFppfOver C S hS) :=
  BasedCategory.ofFunctor
    ((ULiftHom.down : ULiftHom.{u + 1} (fibredCategory C S hS F).val.obj ⥤
      (fibredCategory C S hS F).val.obj) ⋙
      (fibredCategory C S hS F).val.p)

private abbrev liftedElementsBasedCategory
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    BasedCategory.{u + 1, u + 1} (BigFppfOver C S hS) :=
  BasedCategory.ofFunctor
    ((ULiftHom.down : ULiftHom.{u + 1} F.Elementsᵒᵖ ⥤ F.Elementsᵒᵖ) ⋙
      (CategoryOfElements.π F).leftOp)

/-- **The projection of the category fibred in sets of a presheaf is faithful.** A morphism of a
category of elements is determined by the morphism of the site it lies over, its fibre component
being a morphism of a discrete category. -/
theorem faithful_fibredCategory_projection
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    (fibredCategory C S hS F).val.p.Faithful :=
  ⟨fun h => Pseudofunctor.CoGrothendieck.Hom.ext _ _ h Discrete.hom_eq⟩

private noncomputable def liftedPointsEquivalenceOverElements
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    StacksRepresentableCFG.EquivalenceOver
      (liftedPointsBasedCategory F).p (liftedElementsBasedCategory F).p := by
  let hom := (ULiftHom.down : ULiftHom.{u + 1}
      (fibredCategory C S hS F).val.obj ⥤
      (fibredCategory C S hS F).val.obj) ⋙
    pointsToElements F ⋙ (ULiftHom.up : F.Elementsᵒᵖ ⥤ ULiftHom.{u + 1} F.Elementsᵒᵖ)
  let inv := (ULiftHom.down : ULiftHom.{u + 1} F.Elementsᵒᵖ ⥤ F.Elementsᵒᵖ) ⋙
    elementsToPoints F ⋙ (ULiftHom.up : (fibredCategory C S hS F).val.obj ⥤
      ULiftHom.{u + 1} (fibredCategory C S hS F).val.obj)
  letI : (fibredCategory C S hS F).val.p.Faithful :=
    faithful_fibredCategory_projection F
  letI : (liftedPointsBasedCategory F).p.Faithful :=
    ⟨fun h => ULift.ext _ _ ((fibredCategory C S hS F).val.p.map_injective h)⟩
  letI := faithful_categoryOfElements_π_leftOp F
  letI : (liftedElementsBasedCategory F).p.Faithful :=
    ⟨fun h => ULift.ext _ _ ((CategoryOfElements.π F).leftOp.map_injective h)⟩
  refine {
    hom := ⟨hom, rfl⟩
    inv := ⟨inv, rfl⟩
    unitIso := NatIso.ofComponents (fun x => ?_) ?_
    counitIso := NatIso.ofComponents (fun x => ?_) ?_
    unit_over := ?_
    counit_over := ?_ }
  · obtain ⟨x⟩ := x
    cases x
    rfl
  · rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ f
    apply Functor.map_injective (F := (liftedPointsBasedCategory F).p)
    cases f
    rfl
  · obtain ⟨x⟩ := x
    cases x
    rfl
  · rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ f
    apply Functor.map_injective (F := (liftedElementsBasedCategory F).p)
    cases f
    rfl
  all_goals
    ext ⟨x⟩
    rfl

private noncomputable def liftedPointsEquivalenceOfElements
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    BasedCategory.Equivalence (liftedPointsBasedCategory F)
      (liftedElementsBasedCategory F) := by
  let e := liftedPointsEquivalenceOverElements F
  exact ⟨BasedFunctor.mk e.hom.functor e.hom.w,
    BasedFunctor.mk e.inv.functor e.inv.w,
    BasedNatIso.mkNatIso e.unitIso.symm e.isHomLift_unitIso_inv_app,
    BasedNatIso.mkNatIso e.counitIso e.isHomLift_counitIso_hom_app⟩

private theorem liftedElements_isStack
    (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology C S hS) F) :
    (liftedElementsBasedCategory F).p.IsStack
      (BigFppfOver.topology C S hS) := by
  let := elementsOpp_isFiberedInSets F
  exact isStack_uliftHom _ _ (elementsOpp_isStack _ F hF)

/-- The discrete fibred category with its morphisms in the same universe as
those of the quotient stack. -/
def liftedFibredCategory
    (X : AlgebraicSpaces C S hS) :
    BasedCategory.{u + 1, u + 1} (BigFppfOver C S hS) :=
  BasedCategory.ofFunctor
    ((ULiftHom.down :
        ULiftHom.{u + 1} (fibredCategory C S hS X.obj).val.obj ⥤
          (fibredCategory C S hS X.obj).val.obj) ⋙
      (fibredCategory C S hS X.obj).val.p)

/-- **The universe-enlarged fibred category of an algebraic space is a stack** on the big fppf
site, in the sense of Stacks 026F.

This is the half of the statement that
`AlgebraicGeometry.Stack.isStackInGroupoids_liftedFibredCategory` drops: the latter concludes
`CategoryTheory.Functor.IsStackInGroupoids` (Stacks 02ZI), which spells
descent out for covering families with genuine overlaps, whereas the universal property of
stackification consumes the sieve-indexed condition `CategoryTheory.Functor.IsStack` (Stacks 026F)
and the implication 02ZI ⟹ 026F is not available. -/
theorem liftedFibredCategory_isStack
    (X : AlgebraicSpaces C S hS) :
    (liftedFibredCategory X).p.IsStack
      (BigFppfOver.topology C S hS) := by
  let := elementsOpp_isFiberedInSets X.obj
  let : ((ULiftHom.down : ULiftHom.{u + 1} X.obj.Elementsᵒᵖ ⥤ X.obj.Elementsᵒᵖ) ⋙
      (CategoryOfElements.π X.obj).leftOp).IsFiberedInSets :=
    isFiberedInSets_uliftHom _
  exact (liftedPointsEquivalenceOfElements X.obj).symm.isStack _
    (liftedElements_isStack X.obj X.property.isSheaf)

/-- An algebraic-space sheaf, viewed as a discrete fibred category and enlarged to the
universe of the ambient bicategory, is a stack in groupoids on the big fppf site. -/
theorem isStackInGroupoids_liftedFibredCategory
    (X : AlgebraicSpaces C S hS) :
    (liftedFibredCategory X).p.IsStackInGroupoids
      (BigFppfOver.topology C S hS) :=
  (liftedFibredCategory_isStack X).isStackInGroupoids
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS X.obj).property)

/-- The canonical equivalence from the enlarged fibred category to the
original one, over the site. -/
def liftedFibredCategoryDown
    (X : AlgebraicSpaces C S hS) :
    liftedFibredCategory X ⥤ᵇ (fibredCategory C S hS X.obj).val := by
  exact ⟨(ULiftHom.down :
    ULiftHom.{u + 1} (fibredCategory C S hS X.obj).val.obj ⥤
      (fibredCategory C S hS X.obj).val.obj), rfl⟩

/-- The canonical equivalence from the fibred category of an algebraic space into its
universe-enlarged form, over the site. It is inverse to
`AlgebraicGeometry.Stack.liftedFibredCategoryDown` on the nose, both composites being the
identity functor. -/
def liftedFibredCategoryUp
    (X : AlgebraicSpaces C S hS) :
    (fibredCategory C S hS X.obj).val ⥤ᵇ liftedFibredCategory X :=
  ⟨ULiftHom.up, rfl⟩

end AlgebraicGeometry.Stack

end
