module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftsAlong

/-!
# The presheaf of classes of lifts along a natural family of arrows

Let `p : X ⥤ C` be a fibered category, `R : D ⥤ X` a family of objects of `X` indexed by a
category `D`, `L : D ⥤ C` a family of objects of the base, and `α : R ⋙ p ⟶ L` a natural arrow
out of the image of `R`. Isomorphism classes of lifts of `R.obj W` along `α.app W` are the values
of a presheaf on `D`: the restriction along `h : W₂ ⟶ W₁` is base change along the naturality
square of `α` at `h`, taken at a cartesian lift of `L.map h`, and the unit and composition laws of
base change turn the functoriality of `R` and `L` into the functoriality of the presheaf.

The data `R`, `L`, `α` are supplied by a thickening in a base category with fibre products: for an
arrow `i : p(x) ⟶ U'`, an object `W` of the slice over `U'` goes to the fibre product
`W ×_{U'} p(x)`, to the chosen cartesian lift of `x` along its second projection, and to the first
projection `W ×_{U'} p(x) ⟶ W`. Those three assignments are a functor, a functor and a natural
transformation, the cocycle laws holding on the nose because each lift is chosen in one step at
the fixed object `x`; so the lifts form a presheaf on that slice. For a deformation situation this
is the functor sending an affine over the thickening to the isomorphism classes of lifts of the
restriction of `x` to its fibre product with the closed subscheme.

## Main definitions

* `Deformation.Artin.liftAlongRestrict`, base change of a lift along an arrow of `D`;
* `Deformation.Artin.liftAlongClassesRestrict`, its action on isomorphism classes;
* `Deformation.Artin.liftAlongPresheaf`, the presheaf of classes of lifts;
* `Deformation.Artin.liftAlongFibreMap`, the arrow of fibre products induced by an arrow of the
  slice over the target of `i`;
* `Deformation.Artin.liftAlongRestriction` and
  `Deformation.Artin.liftAlongRestrictionProj`, the restrictions of `x` to those fibre products
  and their first projections;
* `Deformation.Artin.liftAlongSlicePresheaf`, the resulting presheaf on the slice over the target
  of `i`.

## Main results

* `Deformation.Artin.liftAlongClassMk_baseChange_eq`, the class of a base change read off from
  any lift whose structure arrow has the same cartesian factorization.
* `Deformation.Artin.liftAlongClassMk_baseChange_congr`, independence of the class of a base
  change from the representing lift and from the chosen cartesian arrow.
-/

@[expose] public section

namespace Deformation.Artin

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]

section BaseChange

variable {p : X ⥤ C} {x x' : X} {V V' : C} {a : p.obj x ⟶ V} {a' : p.obj x' ⟶ V'}

/-- A lift of `x'` along `a'` whose structure arrow factors `ξ` followed by the structure arrow of
`t` through a strongly cartesian arrow over `g` has the class of the base change of `t`. -/
public lemma liftAlongClassMk_baseChange_eq {u : p.obj x' ⟶ p.obj x} {g : V' ⟶ V} {w : X}
    (hw : p.obj w = V') (t : LiftAlong p x a) (ξ : x' ⟶ x) (hξ : p.IsHomLift u ξ)
    (χ : w ⟶ t.1.right) (hχ : p.IsStronglyCartesian g χ) (hsq : u ≫ a = a' ≫ g)
    (s : LiftAlong p x' a') (χ' : s.1.right ⟶ t.1.right)
    (hχ' : p.IsStronglyCartesian g χ') (hs : s.1.hom ≫ χ' = ξ ≫ t.1.hom) :
    liftAlongClassMk (liftAlongBaseChange (a' := a') hw t ξ hξ χ hχ hsq) = liftAlongClassMk s :=
  liftAlongClassMk_eq_of_cartesian _ s χ χ' hχ hχ'
    ((liftAlongBaseChange_fac (a' := a') hw t ξ hξ χ hχ hsq).trans hs.symm)

/-- The isomorphism of targets underlying an isomorphism of lifts of `x` along `a`. -/
public def liftAlongIsoRight {s t : LiftAlong p x a} (e : s ≅ t) : s.1.right ≅ t.1.right :=
  (Under.forget x).mapIso (Functor.Fiber.fiberInclusion.mapIso e)

/-- The isomorphism of targets of an isomorphism of lifts carries the structure arrow of the
source to the structure arrow of the target. -/
public lemma liftAlongIsoRight_w {s t : LiftAlong p x a} (e : s ≅ t) :
    s.1.hom ≫ (liftAlongIsoRight e).hom = t.1.hom :=
  Under.w e.hom.1

/-- The class of a base change depends neither on the lift representing the class it is taken at
nor on the chosen strongly cartesian arrow: isomorphic lifts have base changes of equal class. -/
public lemma liftAlongClassMk_baseChange_congr {u : p.obj x' ⟶ p.obj x} {g : V' ⟶ V} {w w' : X}
    (hw : p.obj w = V') (hw' : p.obj w' = V') {t t' : LiftAlong p x a} (e : t ≅ t')
    (ξ : x' ⟶ x) (hξ : p.IsHomLift u ξ)
    (χ : w ⟶ t.1.right) (hχ : p.IsStronglyCartesian g χ)
    (χ' : w' ⟶ t'.1.right) (hχ' : p.IsStronglyCartesian g χ') (hsq : u ≫ a = a' ≫ g) :
    liftAlongClassMk (liftAlongBaseChange (a' := a') hw t ξ hξ χ hχ hsq) =
      liftAlongClassMk (liftAlongBaseChange (a' := a') hw' t' ξ hξ χ' hχ' hsq) := by
  have hE : p.IsHomLift (𝟙 V) (liftAlongIsoRight e.symm).hom :=
    liftAlong_morphism_isHomLift p x a e.inv
  have hcartE : p.IsStronglyCartesian (𝟙 V) (liftAlongIsoRight e.symm).hom :=
    have := hE
    inferInstance
  have hcomp : p.IsStronglyCartesian g (χ' ≫ (liftAlongIsoRight e.symm).hom) := by
    have := hχ'
    have := hcartE
    have h := Functor.IsStronglyCartesian.comp (p := p) (f := g) (g := 𝟙 V)
      (φ := χ') (ψ := (liftAlongIsoRight e.symm).hom)
    simpa using h
  have hfac := liftAlongBaseChange_fac (a' := a') hw' t' ξ hξ χ' hχ' hsq
  have key : ∀ ζ : x' ⟶ w', ζ ≫ χ' = ξ ≫ t'.1.hom →
      ζ ≫ χ' ≫ (liftAlongIsoRight e.symm).hom = ξ ≫ t.1.hom := by
    intro ζ hζ
    rw [← Category.assoc, hζ, Category.assoc, liftAlongIsoRight_w]
  exact liftAlongClassMk_baseChange_eq hw t ξ hξ χ hχ hsq _
    (χ' ≫ (liftAlongIsoRight e.symm).hom) hcomp (key _ hfac)

end BaseChange

section Presheaf

variable {D : Type u₃} [Category.{v₃} D] (p : X ⥤ C) [p.IsFibered] (R : D ⥤ X) (L : D ⥤ C)
  (α : R ⋙ p ⟶ L)

/-- Base change of a lift of `R.obj W₁` along `α.app W₁` to a lift of `R.obj W₂` along `α.app W₂`,
along the naturality square of `α` at `h` and at the chosen cartesian lift of `L.map h`. -/
public noncomputable def liftAlongRestrict {W₂ W₁ : D} (h : W₂ ⟶ W₁)
    (t : LiftAlong p (R.obj W₁) (α.app W₁)) : LiftAlong p (R.obj W₂) (α.app W₂) :=
  liftAlongBaseChange (p := p) (a' := α.app W₂)
    (Functor.IsPreFibered.pullbackObj_proj
      (liftAlong_base_obj p (R.obj W₁) (α.app W₁) t) (L.map h))
    t (R.map h) (IsHomLift.map p (R.map h))
    (Functor.IsPreFibered.pullbackMap
      (liftAlong_base_obj p (R.obj W₁) (α.app W₁) t) (L.map h))
    inferInstance (α.naturality h)

/-- Restriction of isomorphism classes of lifts along an arrow of `D`, that is base change of any
representing lift. -/
public noncomputable def liftAlongClassesRestrict {W₂ W₁ : D} (h : W₂ ⟶ W₁) :
    LiftAlongClasses p (R.obj W₁) (α.app W₁) → LiftAlongClasses p (R.obj W₂) (α.app W₂) :=
  Quotient.lift (fun t ↦ liftAlongClassMk (liftAlongRestrict p R L α h t)) (by
    rintro t t' ⟨e⟩
    unfold liftAlongRestrict
    exact liftAlongClassMk_baseChange_congr _ _ e _ _ _ _ _ _ _)

/-- Restriction of the class of a lift is the class of its base change. -/
@[simp]
public lemma liftAlongClassesRestrict_classMk {W₂ W₁ : D} (h : W₂ ⟶ W₁)
    (t : LiftAlong p (R.obj W₁) (α.app W₁)) :
    liftAlongClassesRestrict p R L α h (liftAlongClassMk t) =
      liftAlongClassMk (liftAlongRestrict p R L α h t) :=
  rfl

/-- The presheaf on `D` of isomorphism classes of lifts of `R.obj W` along `α.app W`, restriction
being base change along the naturality squares of `α`. -/
public noncomputable def liftAlongPresheaf : Dᵒᵖ ⥤ Type (max u₂ v₂) where
  obj W := LiftAlongClasses p (R.obj W.unop) (α.app W.unop)
  map {_ _} h := ↾fun c ↦ liftAlongClassesRestrict p R L α h.unop c
  map_id W := by
    ext c
    induction c using Quotient.ind with
    | _ t =>
    have hid : p.IsHomLift (𝟙 (L.obj W.unop)) (𝟙 t.1.right) :=
      IsHomLift.id (liftAlong_base_obj p (R.obj W.unop) (α.app W.unop) t)
    have hχ : p.IsStronglyCartesian (L.map (𝟙 W.unop)) (𝟙 t.1.right) := by
      have := hid
      rw [L.map_id]
      infer_instance
    exact liftAlongClassMk_baseChange_eq _ t _ _ _ _ _ t (𝟙 t.1.right) hχ (by simp)
  map_comp {W₁ W₂ W₃} f g := by
    ext c
    induction c using Quotient.ind with
    | _ t =>
    have hb := liftAlong_base_obj p (R.obj W₁.unop) (α.app W₁.unop) t
    have hχ : p.IsStronglyCartesian (L.map g.unop ≫ L.map f.unop)
        (Functor.IsPreFibered.pullbackMap hb (L.map (g.unop ≫ f.unop))) := by
      rw [← L.map_comp]
      infer_instance
    have hfac := liftAlongBaseChange_fac (p := p) (a' := α.app W₃.unop)
      (Functor.IsPreFibered.pullbackObj_proj hb (L.map (g.unop ≫ f.unop)))
      t (R.map (g.unop ≫ f.unop)) (IsHomLift.map p (R.map (g.unop ≫ f.unop)))
      (Functor.IsPreFibered.pullbackMap hb (L.map (g.unop ≫ f.unop))) inferInstance
      (α.naturality (g.unop ≫ f.unop))
    refine (liftAlongClassMk_baseChange_comp _ _ t _ _ _ _ _ _ _ _ _ _ _ _ hχ ?_).symm
    exact hfac.trans (by rw [R.map_comp])

end Presheaf

section Base

variable [HasPullbacks C] {U U' : C} (i : U ⟶ U')

/-- The arrow of fibre products with the source of `i` induced by an arrow of the slice over the
target of `i`. -/
public noncomputable def liftAlongFibreMap {W₂ W₁ : Over U'} (h : W₂ ⟶ W₁) :
    pullback W₂.hom i ⟶ pullback W₁.hom i :=
  pullback.lift (pullback.fst W₂.hom i ≫ h.left) (pullback.snd W₂.hom i)
    (by rw [Category.assoc, Over.w h, pullback.condition])

/-- The induced arrow of fibre products followed by the first projection is the first projection
followed by the given arrow of the slice. -/
@[reassoc (attr := simp)]
public lemma liftAlongFibreMap_fst {W₂ W₁ : Over U'} (h : W₂ ⟶ W₁) :
    liftAlongFibreMap i h ≫ pullback.fst W₁.hom i = pullback.fst W₂.hom i ≫ h.left :=
  pullback.lift_fst _ _ _

/-- The induced arrow of fibre products lies over the source of `i`. -/
@[reassoc (attr := simp)]
public lemma liftAlongFibreMap_snd {W₂ W₁ : Over U'} (h : W₂ ⟶ W₁) :
    liftAlongFibreMap i h ≫ pullback.snd W₁.hom i = pullback.snd W₂.hom i :=
  pullback.lift_snd _ _ _

/-- An identity of the slice induces the identity of the fibre product. -/
@[simp]
public lemma liftAlongFibreMap_id (W : Over U') :
    liftAlongFibreMap i (𝟙 W) = 𝟙 (pullback W.hom i) := by
  apply pullback.hom_ext <;> simp

/-- The arrow of fibre products induced by a composite is the composite of the induced arrows. -/
@[simp]
public lemma liftAlongFibreMap_comp {W₃ W₂ W₁ : Over U'} (h₂ : W₃ ⟶ W₂) (h₁ : W₂ ⟶ W₁) :
    liftAlongFibreMap i (h₂ ≫ h₁) = liftAlongFibreMap i h₂ ≫ liftAlongFibreMap i h₁ := by
  apply pullback.hom_ext <;> simp

end Base

section Site

variable [HasPullbacks C] (p : X ⥤ C) [p.IsFibered] (x : X) {U' : C} (i : p.obj x ⟶ U')

/-- The restriction of `x` to the fibre products with the source of `i`, as a functor on the slice
over the target of `i`: an object of the slice goes to the chosen cartesian lift of `x` along the
second projection of its fibre product, and an arrow to the arrow of lifts it induces. -/
public noncomputable def liftAlongRestriction : Over U' ⥤ X where
  obj W := Functor.IsPreFibered.pullbackObj (rfl : p.obj x = p.obj x) (pullback.snd W.hom i)
  map {W₂ W₁} h := Functor.IsStronglyCartesian.map p (pullback.snd W₁.hom i)
    (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (pullback.snd W₁.hom i))
    (liftAlongFibreMap_snd i h).symm
    (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (pullback.snd W₂.hom i))
  map_id W := by
    have hid : p.IsHomLift (liftAlongFibreMap i (𝟙 W)) (𝟙 (Functor.IsPreFibered.pullbackObj
        (rfl : p.obj x = p.obj x) (pullback.snd W.hom i))) := by
      rw [liftAlongFibreMap_id]
      exact IsHomLift.id (Functor.IsPreFibered.pullbackObj_proj _ _)
    have := hid
    exact (Functor.IsStronglyCartesian.map_uniq p (pullback.snd W.hom i) _
      (liftAlongFibreMap_snd i (𝟙 W)).symm _ (𝟙 _) (by simp)).symm
  map_comp := by
    intro W₃ W₂ W₁ h₂ h₁
    have h₂' := Functor.IsStronglyCartesian.map_isHomLift p (pullback.snd W₂.hom i)
      (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (pullback.snd W₂.hom i))
      (liftAlongFibreMap_snd i h₂).symm
      (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (pullback.snd W₃.hom i))
    have h₁' := Functor.IsStronglyCartesian.map_isHomLift p (pullback.snd W₁.hom i)
      (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (pullback.snd W₁.hom i))
      (liftAlongFibreMap_snd i h₁).symm
      (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (pullback.snd W₂.hom i))
    have hcomp : p.IsHomLift (liftAlongFibreMap i (h₂ ≫ h₁))
        (Functor.IsStronglyCartesian.map p (pullback.snd W₂.hom i)
            (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x)
              (pullback.snd W₂.hom i)) (liftAlongFibreMap_snd i h₂).symm
            (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x)
              (pullback.snd W₃.hom i)) ≫
          Functor.IsStronglyCartesian.map p (pullback.snd W₁.hom i)
            (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x)
              (pullback.snd W₁.hom i)) (liftAlongFibreMap_snd i h₁).symm
            (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x)
              (pullback.snd W₂.hom i))) := by
      rw [liftAlongFibreMap_comp]
      have := h₂'
      have := h₁'
      infer_instance
    have := hcomp
    refine (Functor.IsStronglyCartesian.map_uniq p (pullback.snd W₁.hom i) _
      (liftAlongFibreMap_snd i (h₂ ≫ h₁)).symm _ _ ?_).symm
    rw [Category.assoc, Functor.IsStronglyCartesian.fac, Functor.IsStronglyCartesian.fac]

/-- The restriction of `x` lies over the fibre product, and its first projection is a natural
arrow to the object of the slice. -/
public noncomputable def liftAlongRestrictionProj :
    liftAlongRestriction p x i ⋙ p ⟶ Over.forget U' where
  app W := eqToHom (Functor.IsPreFibered.pullbackObj_proj
      (rfl : p.obj x = p.obj x) (pullback.snd W.hom i)) ≫ pullback.fst W.hom i
  naturality {W₂ W₁} h := by
    have hlift : p.IsHomLift (liftAlongFibreMap i h) ((liftAlongRestriction p x i).map h) :=
      Functor.IsStronglyCartesian.map_isHomLift p (pullback.snd W₁.hom i)
        (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (pullback.snd W₁.hom i))
        (liftAlongFibreMap_snd i h).symm
        (Functor.IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (pullback.snd W₂.hom i))
    have := hlift
    have hfac := IsHomLift.fac' p (liftAlongFibreMap i h) ((liftAlongRestriction p x i).map h)
    have key : ∀ (y₂ y₁ : C) (e₂ : y₂ = pullback W₂.hom i) (e₁ : y₁ = pullback W₁.hom i)
        (m : y₂ ⟶ y₁), m = eqToHom e₂ ≫ liftAlongFibreMap i h ≫ eqToHom e₁.symm →
        m ≫ eqToHom e₁ ≫ pullback.fst W₁.hom i =
          (eqToHom e₂ ≫ pullback.fst W₂.hom i) ≫ h.left := by
      intro y₂ y₁ e₂ e₁ m hm
      subst e₂
      subst e₁
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm ⊢
      rw [hm, liftAlongFibreMap_fst]
    exact key _ _ _ _ _ hfac

/-- The presheaf of isomorphism classes of lifts of the restrictions of `x`: for an object `W` of
the slice over the target of `i`, the isomorphism classes of lifts of the restriction of `x` to
`W ×_{U'} p(x)` along the first projection `W ×_{U'} p(x) ⟶ W`. -/
public noncomputable def liftAlongSlicePresheaf : (Over U')ᵒᵖ ⥤ Type (max u₂ v₂) :=
  liftAlongPresheaf p (liftAlongRestriction p x i) (Over.forget U')
    (liftAlongRestrictionProj p x i)

end Site

end Deformation.Artin
