module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Reindex

/-!
# Peeling one square off a family of commutative squares

The induction which proves [Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) peels
one point off the family.  On the level of the commutative squares that carry the glueing data,
the step is this: the family is indexed by `Option J`, the square at `none` is a square over a
*smaller ambient scheme* `W` sitting between `U` and `T`, and the squares at `some j`, read over
`W` rather than over `U`, form the family of the subfamily.

This file carries out the categorical half of that step.  Glueing data for the whole family is
the same thing as glueing data for the subfamily whose component over `W` has itself been
decomposed by the square at `none`, which is `AlgebraicGeometry.nestedGlueingData`; the
decomposition is the canonical functor of the square at `none`, so it is an equivalence exactly
when [Stacks, Tag 0BPA] applies there.

## Main definitions

* `AlgebraicGeometry.optionObj` and `AlgebraicGeometry.optionHom`: assembling an object, resp. a
  morphism, of a product category indexed by `Option J` out of its component at `none` and its
  family of components at `some`.
* `AlgebraicGeometry.nestedGlueingData`: glueing data for the subfamily, read over `W`, whose
  comparison isomorphisms are taken over the overlaps of the *whole* family.
* `AlgebraicGeometry.assembleGlueingData`: the functor from nested glueing data to glueing data
  for the whole family, decomposing the component over `W` by the square at `none`.

## Main results

* `AlgebraicGeometry.assembleGlueingData_isEquivalence`: `assembleGlueingData` is an equivalence
  as soon as the canonical functor of the square at `none` is one.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Lemma 32.14.1 (0BPA)](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-! ### Assembling families indexed by `Option` -/

/-- An object of a product category indexed by `Option J`, from its component at `none` and its
family of components at `some`. -/
def optionObj {J : Type u} {C : Option J → Type*} (x : C none) (y : ∀ j, C (some j)) :
    ∀ i, C i
  | none => x
  | some j => y j

/-- A morphism of a product category indexed by `Option J`, from its component at `none` and its
family of components at `some`. -/
def optionHom {J : Type u} {C : Option J → Type*} [∀ i, Category.{v} (C i)] {X Y : ∀ i, C i}
    (f : X none ⟶ Y none) (g : ∀ j, X (some j) ⟶ Y (some j)) : X ⟶ Y
  | none => f
  | some j => g j

/-- The component at `none` of `optionHom f g` is `f`. -/
@[simp]
theorem optionHom_none {J : Type u} {C : Option J → Type*} [∀ i, Category.{v} (C i)]
    {X Y : ∀ i, C i} (f : X none ⟶ Y none) (g : ∀ j, X (some j) ⟶ Y (some j)) :
    optionHom f g none = f :=
  rfl

/-- The component at `some j` of `optionHom f g` is `g j`. -/
@[simp]
theorem optionHom_some {J : Type u} {C : Option J → Type*} [∀ i, Category.{v} (C i)]
    {X Y : ∀ i, C i} (f : X none ⟶ Y none) (g : ∀ j, X (some j) ⟶ Y (some j)) (j : J) :
    optionHom f g (some j) = g j :=
  rfl

/-- A family of isomorphisms of a product category indexed by `Option J`, from its component at
`none` and its family of components at `some`. -/
def optionIso {J : Type u} {C : Option J → Type*} [∀ i, Category.{v} (C i)] {X Y : ∀ i, C i}
    (f : X none ≅ Y none) (g : ∀ j, X (some j) ≅ Y (some j)) : ∀ i, X i ≅ Y i
  | none => f
  | some j => g j

/-- A morphism of a product category indexed by `Option J` is the assembly of its component at
`none` and its family of components at `some`. -/
theorem optionHom_eq {J : Type u} {C : Option J → Type*} [∀ i, Category.{v} (C i)]
    {X Y : ∀ i, C i} (f : X ⟶ Y) : optionHom (f none) (fun j ↦ f (some j)) = f := by
  refine funext fun i ↦ ?_
  cases i with
  | none => rfl
  | some j => rfl

/-! ### Nested glueing data -/

section Assemble

variable {U W : Scheme.{u}} {J : Type u} {L O : Option J → Scheme.{u}} (cUW : U ⟶ W)
  (d₀ : L none ⟶ W) (a : ∀ i, O i ⟶ U) (b : ∀ i, O i ⟶ L i)
  (h₀ : a none ≫ cUW = b none ≫ d₀)

/-- Glueing data for the subfamily of a family of commutative squares indexed by `Option J`, read
over the intermediate ambient scheme `W`: a scheme of finite presentation over `W`, a family of
schemes of finite presentation over the `L (some j)`, and an isomorphism of the two restrictions
to each overlap `O (some j)` of the *whole* family. -/
abbrev nestedGlueingData :=
  IsoComma (finitePresentationBaseChange cUW ⋙
      Functor.pi' fun j ↦ finitePresentationBaseChange (a (some j)))
    (Functor.pi fun j ↦ finitePresentationBaseChange (b (some j)))

/-- The assembly of nested glueing data into glueing data for the whole family: the component
over `W` is decomposed by the canonical functor of the square at `none`. -/
noncomputable def assembleGlueingDataComma :
    Comma (finitePresentationBaseChange cUW ⋙
        Functor.pi' fun j ↦ finitePresentationBaseChange (a (some j)))
      (Functor.pi fun j ↦ finitePresentationBaseChange (b (some j))) ⥤
    Comma (Functor.pi' fun i ↦ finitePresentationBaseChange (a i))
      (Functor.pi fun i ↦ finitePresentationBaseChange (b i)) where
  obj Z := ⟨(finitePresentationBaseChange cUW).obj Z.left,
    optionObj ((finitePresentationBaseChange d₀).obj Z.left) Z.right,
    optionHom ((finitePresentationPullbackSquareIso h₀).hom.app Z.left) Z.hom⟩
  map {_ _} f := ⟨(finitePresentationBaseChange cUW).map f.left,
    optionHom ((finitePresentationBaseChange d₀).map f.left) f.right, by
      refine funext fun i ↦ ?_
      cases i with
      | none => exact (finitePresentationPullbackSquareIso h₀).hom.naturality f.left
      | some j => exact congrFun f.w j⟩
  map_id _ := Comma.hom_ext _ _ (by simp) (by
    refine funext fun i ↦ ?_
    cases i with
    | none => exact (finitePresentationBaseChange d₀).map_id _
    | some j => rfl)
  map_comp _ _ := Comma.hom_ext _ _ (by simp) (by
    refine funext fun i ↦ ?_
    cases i with
    | none => exact (finitePresentationBaseChange d₀).map_comp _ _
    | some j => rfl)

/-- The assembly of nested glueing data into glueing data for the whole family. -/
noncomputable def assembleGlueingData :
    nestedGlueingData cUW a b ⥤ glueingDataOf a b :=
  (show ObjectProperty (Comma (Functor.pi' fun i ↦ finitePresentationBaseChange (a i))
      (Functor.pi fun i ↦ finitePresentationBaseChange (b i))) from fun X ↦ IsIso X.hom).lift
    ((show ObjectProperty (Comma (finitePresentationBaseChange cUW ⋙
        Functor.pi' fun j ↦ finitePresentationBaseChange (a (some j)))
        (Functor.pi fun j ↦ finitePresentationBaseChange (b (some j)))) from
      fun X ↦ IsIso X.hom).ι ⋙ assembleGlueingDataComma cUW d₀ a b h₀)
    (fun Z ↦ by
      refine (isIso_pi_iff _).mpr fun i ↦ ?_
      cases i with
      | none =>
        change IsIso ((finitePresentationPullbackSquareIso h₀).hom.app Z.obj.left)
        infer_instance
      | some j =>
        change IsIso (Z.obj.hom j)
        exact (isIso_pi_iff _).mp Z.property j)

/-- The scheme over `U` of assembled glueing data is the base change along `cUW` of the scheme
over `W` of the nested datum. -/
@[simp]
theorem assembleGlueingData_obj_left (Z : nestedGlueingData cUW a b) :
    ((assembleGlueingData cUW d₀ a b h₀).obj Z).obj.left =
      (finitePresentationBaseChange cUW).obj Z.obj.left :=
  rfl

/-- The morphism over `U` of an assembled morphism is the base change along `cUW` of the morphism
over `W`. -/
@[simp]
theorem assembleGlueingData_map_left {Z Z' : nestedGlueingData cUW a b} (f : Z ⟶ Z') :
    ((assembleGlueingData cUW d₀ a b h₀).map f).hom.left =
      (finitePresentationBaseChange cUW).map f.hom.left :=
  rfl

/-- The component at `none` of an assembled morphism is the base change along `d₀` of the
morphism over `W`. -/
@[simp]
theorem assembleGlueingData_map_right_none {Z Z' : nestedGlueingData cUW a b} (f : Z ⟶ Z') :
    ((assembleGlueingData cUW d₀ a b h₀).map f).hom.right none =
      (finitePresentationBaseChange d₀).map f.hom.left :=
  rfl

/-- The component at `some j` of an assembled morphism is the component at `j` of the nested
morphism. -/
@[simp]
theorem assembleGlueingData_map_right_some {Z Z' : nestedGlueingData cUW a b} (f : Z ⟶ Z')
    (j : J) :
    ((assembleGlueingData cUW d₀ a b h₀).map f).hom.right (some j) = f.hom.right j :=
  rfl

/-- The comparison isomorphism of assembled glueing data at `none` is the base-change
associativity isomorphism of the square at `none`. -/
@[simp]
theorem assembleGlueingData_obj_hom_none (Z : nestedGlueingData cUW a b) :
    ((assembleGlueingData cUW d₀ a b h₀).obj Z).obj.hom none =
      (finitePresentationPullbackSquareIso h₀).hom.app Z.obj.left :=
  rfl

/-- The comparison isomorphism of assembled glueing data at `some j` is the comparison
isomorphism of the nested datum at `j`. -/
@[simp]
theorem assembleGlueingData_obj_hom_some (Z : nestedGlueingData cUW a b) (j : J) :
    ((assembleGlueingData cUW d₀ a b h₀).obj Z).obj.hom (some j) = Z.obj.hom j :=
  rfl

variable (hH : (restrictionFunctorOfSquare cUW d₀ h₀).IsEquivalence)

include hH in
/-- Assembling nested glueing data into glueing data for the whole family is an equivalence as
soon as the canonical functor of the square at `none` is one: a glueing datum for the whole
family is the same data as a nested one, the component over `W` being traded for its
decomposition at `none`. -/
theorem assembleGlueingData_isEquivalence :
    (assembleGlueingData cUW d₀ a b h₀).IsEquivalence := by
  have := hH
  have : (assembleGlueingData cUW d₀ a b h₀).Faithful := by
    refine ⟨fun {Z Z'} f g hfg ↦ ?_⟩
    have hr := congrArg (fun k ↦ k.hom.right) hfg
    refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ (funext fun j ↦ congrFun hr (some j)))
    refine (restrictionFunctorOfSquare cUW d₀ h₀).map_injective
      (ObjectProperty.hom_ext _ (Comma.hom_ext _ _ (congrArg (fun k ↦ k.hom.left) hfg) ?_))
    exact congrFun hr none
  have : (assembleGlueingData cUW d₀ a b h₀).Full := by
    refine ⟨fun {Z Z'} φ ↦ ?_⟩
    obtain ⟨u, hu⟩ := (restrictionFunctorOfSquare cUW d₀ h₀).map_surjective
      (ObjectProperty.homMk
        (⟨φ.hom.left, φ.hom.right none, congrFun φ.hom.w none⟩ :
          ((restrictionFunctorOfSquare cUW d₀ h₀).obj Z.obj.left).obj ⟶
            ((restrictionFunctorOfSquare cUW d₀ h₀).obj Z'.obj.left).obj))
    have hleft : (finitePresentationBaseChange cUW).map u = φ.hom.left :=
      congrArg (fun k ↦ k.hom.left) hu
    have hright : (finitePresentationBaseChange d₀).map u = φ.hom.right none :=
      congrArg (fun k ↦ k.hom.right) hu
    refine ⟨ObjectProperty.homMk ⟨u, fun j ↦ φ.hom.right (some j), funext fun j ↦ ?_⟩, ?_⟩
    · show (finitePresentationBaseChange (a (some j))).map
          ((finitePresentationBaseChange cUW).map u) ≫ Z'.obj.hom j =
        Z.obj.hom j ≫
          (finitePresentationBaseChange (b (some j))).map (φ.hom.right (some j))
      rw [hleft]
      exact congrFun φ.hom.w (some j)
    · refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hleft (funext fun i ↦ ?_))
      cases i with
      | none => exact hright
      | some j => rfl
  have : (assembleGlueingData cUW d₀ a b h₀).EssSurj := by
    refine ⟨fun Z ↦ ?_⟩
    have : IsIso Z.obj.hom := Z.property
    have hnone : IsIso (Z.obj.hom none) := (isIso_pi_iff _).mp Z.property none
    obtain ⟨XW, ⟨κ⟩⟩ : ∃ XW : FinitePresentationOver W,
        Nonempty ((restrictionFunctorOfSquare cUW d₀ h₀).obj XW ≅
          (⟨⟨Z.obj.left, Z.obj.right none, Z.obj.hom none⟩, hnone⟩ :
            glueingDataOfSquare (a none) (b none))) :=
      ⟨_, ⟨(restrictionFunctorOfSquare cUW d₀ h₀).objObjPreimageIso _⟩⟩
    let κ₁ := (ObjectProperty.ι _ ⋙ Comma.fst _ _).mapIso κ
    let κ₂ := (ObjectProperty.ι _ ⋙ Comma.snd _ _).mapIso κ
    refine ⟨⟨⟨XW, fun j ↦ Z.obj.right (some j),
      fun j ↦ (finitePresentationBaseChange (a (some j))).map κ.hom.hom.left ≫
        Z.obj.hom (some j)⟩, ?_⟩, ⟨?_⟩⟩
    · refine (isIso_pi_iff _).mpr fun j ↦ ?_
      have : IsIso κ₁.hom := inferInstance
      show IsIso ((finitePresentationBaseChange (a (some j))).map κ.hom.hom.left ≫
        Z.obj.hom (some j))
      exact IsIso.comp_isIso' (CategoryTheory.Functor.map_isIso _ _)
        ((isIso_pi_iff _).mp Z.property (some j))
    · refine ObjectProperty.isoMk _ (Comma.isoMk
        κ₁ (Pi.isoMk (optionIso κ₂ fun j ↦ Iso.refl _))
        (funext fun i ↦ ?_))
      cases i with
      | none =>
        show (finitePresentationBaseChange (a none)).map κ.hom.hom.left ≫ Z.obj.hom none =
          (finitePresentationPullbackSquareIso h₀).hom.app XW ≫
            (finitePresentationBaseChange (b none)).map κ.hom.hom.right
        exact κ.hom.hom.w
      | some j =>
        show (finitePresentationBaseChange (a (some j))).map κ.hom.hom.left ≫
            Z.obj.hom (some j) =
          ((finitePresentationBaseChange (a (some j))).map κ.hom.hom.left ≫
            Z.obj.hom (some j)) ≫
            (finitePresentationBaseChange (b (some j))).map (𝟙 (Z.obj.right (some j)))
        rw [CategoryTheory.Functor.map_id]
        exact (Category.comp_id _).symm
  exact { }

end Assemble

end AlgebraicGeometry

end
