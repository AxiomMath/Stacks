module

public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The 2-fibre product of categories of elements of presheaves of sets

Fix a category `C` and presheaves of sets `G` and `F` on `C`. Their categories of elements
(`CategoryTheory.presheafOfCategories` of the associated presheaves of discrete categories,
Stacks 02XV) are fibred in setoids over `C` with discrete fibres. This file computes, for a
category `𝒯` over `C` with structure functor `pT`, the 2-fibre product over `C`

```text
𝒯 ×_{σ, El F, θ} El G
```

of a 1-morphism `σ : 𝒯 ⥤ El F` over `C`, i.e. a global section of the restriction of `F` along
`pT`, with a 1-morphism `θ : El G ⥤ El F` over `C`, i.e. a morphism of presheaves `G ⟶ F`: it
is the category of elements of the subpresheaf of the restriction of `G` along `pT` cut out by
the equation `θ g = σ`, which for `𝒯 = C` and `pT = 𝟭 C` is the fibre product `G ×_F 1` of
presheaves.

The case `𝒯 = C`, `pT = 𝟭 C` is the one in which the right-hand factor is a *section* of the
projection; the general `pT` is what a base change along a point of `C` needs, where `𝒯` is a
slice of `C` and the subpresheaf lives on that slice.

The two translations between 1-morphisms over `C` and morphisms of presheaves are
`CategoryTheory.PresheafOfCategories.natTransOfBasedFunctor` and
`CategoryTheory.PresheafOfCategories.sectionOfBasedFunctor`; the subpresheaf is
`CategoryTheory.PresheafOfCategories.fibrePresheaf`.

## Main definitions

* `CategoryTheory.PresheafOfCategories.natTransOfBasedFunctor`: the morphism of presheaves
  `G ⟶ F` underlying a 1-morphism `El G ⥤ El F` over `C`.
* `CategoryTheory.PresheafOfCategories.sectionOfBasedFunctor`: the global section of the
  restriction of `F` along `pT` underlying a 1-morphism `𝒯 ⥤ El F` over `C`.
* `CategoryTheory.PresheafOfCategories.fibrePresheaf`: the subpresheaf `{g | θ g = σ}` of `G`.
* `CategoryTheory.PresheafOfCategories.toTwoFibreProduct`: the comparison functor from the
  category of elements of the subpresheaf to the 2-fibre product.

## Main results

* `CategoryTheory.PresheafOfCategories.isEquivalence_toTwoFibreProduct`: the comparison is an
  equivalence of categories, and `toTwoFibreProduct_comp_fst` says it is strictly over `𝒯`.
* `CategoryTheory.PresheafOfCategories.isPullback_fibrePresheaf`: the subpresheaf is the fibre
  product of `G` and the presheaf represented by a final object over `F`, which is what
  identifies it with `G ×_F 1` and lets Stacks 02X2 be applied to it.

## Implementation notes

Everything rests on two facts about a category of elements: a morphism is determined by the
morphism of `C` it lies over (`CategoryTheory.PresheafOfCategories.elements_hom_ext`, because
the fibres are discrete), and the element of `F(V)` named by an object lying over `V` is
`CategoryTheory.PresheafOfCategories.discreteFiberEquiv` of it. The first makes every
functoriality and compatibility check a check on base morphisms; the second turns the two
1-morphisms into presheaf data.

`CategoryTheory.PresheafOfCategories.toElementsG` and
`CategoryTheory.PresheafOfCategories.toElementsGMap` are abbreviations, not definitions: the
comparison square of the 2-fibre product has `θ` applied to them on one side and to a term
written out in full on the other, and `CategoryTheory.Functor.IsHomLift` is a class, so a
non-reducible name for them would hide the verticality hypothesis from instance search at
exactly the place where it is needed.

The morphism universe of `𝒯` is the morphism universe of `C`, because a presheaf on `𝒯` whose
values are those of `G` has to be one `CategoryTheory.presheafOfCategories` accepts.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.PresheafOfCategories

universe vC uC uT

variable {C : Type uC} [Category.{vC} C]

section Basic

variable {P : Cᵒᵖ ⥤ Type vC}

/-- The projection to `C` reads off the base of an object. -/
@[simp] theorem discreteProjection_obj (X : (presheafOfCategories (P ⋙ typeToCat)).obj) :
    (discreteProjection P).obj X = X.base := rfl

/-- The projection to `C` reads off the base of a morphism. -/
@[simp] theorem discreteProjection_map {X Y : (presheafOfCategories (P ⋙ typeToCat)).obj}
    (u : X ⟶ Y) : (discreteProjection P).map u = u.base := rfl

/-- A morphism of the category of elements lies over the morphism of `C` recorded as its base;
the projection to `C` reads off that base. -/
theorem isHomLift_base {X Y : (presheafOfCategories (P ⋙ typeToCat)).obj} (u : X ⟶ Y) :
    (discreteProjection P).IsHomLift u.base u :=
  IsHomLift.map _ u

/-- The morphism of the category of elements of `P` over `f : V ⟶ W` from the restriction of an
element `p` of `P(W)` along `f` to `p`. -/
def homMk {V W : C} (f : V ⟶ W) (p : P.obj (op W)) :
    (⟨V, Discrete.mk (P.map f.op p)⟩ : (presheafOfCategories (P ⋙ typeToCat)).obj) ⟶
      ⟨W, Discrete.mk p⟩ :=
  ⟨f, ⟨rfl⟩⟩

/-- The element of `P(V)` named by an object of the category of elements lying over `V`. -/
def elementOf (P : Cᵒᵖ ⥤ Type vC) {X : (presheafOfCategories (P ⋙ typeToCat)).obj} {V : C}
    (h : X.base = V) : P.obj (op V) :=
  discreteFiberEquiv P V ⟨X, h⟩

/-- The element named by the canonical object attached to `p : P(V)` is `p`. -/
@[simp] theorem elementOf_mk (P : Cᵒᵖ ⥤ Type vC) (V : C) (p : P.obj (op V)) :
    elementOf P (X := ⟨V, Discrete.mk p⟩) rfl = p := rfl

/-- Two objects of the category of elements lying over one object of `C` and naming the same
element are equal. -/
theorem obj_eq_of_elementOf_eq {X Y : (presheafOfCategories (P ⋙ typeToCat)).obj} {V : C}
    (hX : X.base = V) (hY : Y.base = V) (h : elementOf P hX = elementOf P hY) : X = Y :=
  congrArg (fun z : (discreteProjection P).Fiber V => z.1)
    ((discreteFiberEquiv P V).injective h)

/-- A morphism of the category of elements lying over `f` identifies the element named by its
source with the restriction along `f` of the element named by its target. -/
theorem elementOf_eq_map {X Y : (presheafOfCategories (P ⋙ typeToCat)).obj} {V W : C}
    (hX : X.base = V) (hY : Y.base = W) (f : V ⟶ W) (u : X ⟶ Y)
    (hu : (discreteProjection P).IsHomLift f u) :
    elementOf P hX = P.map f.op (elementOf P hY) :=
  discreteFiberEquiv_eq_map_of_isHomLift P f ⟨Y, hY⟩ ⟨X, hX⟩ u hu

end Basic

section Translation

variable {G F : Cᵒᵖ ⥤ Type vC}

/-- The value of `natTransOfBasedFunctor` at an object of `C` and an element of `G` there. -/
def natTransAppOfBasedFunctor (θ : (presheafOfCategories (G ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hθ : θ ⋙ discreteProjection F = discreteProjection G) (V : C) (g : G.obj (op V)) :
    F.obj (op V) :=
  elementOf F (X := θ.obj (⟨V, Discrete.mk g⟩ :
      (presheafOfCategories (G ⋙ typeToCat)).obj)) (V := V)
    (Functor.congr_obj hθ (⟨V, Discrete.mk g⟩ :
      (presheafOfCategories (G ⋙ typeToCat)).obj))

/-- The morphism of presheaves `G ⟶ F` underlying a 1-morphism `El G ⥤ El F` over `C`: it sends
`g : G(V)` to the element named by the image of the canonical object attached to `g`. -/
def natTransOfBasedFunctor (θ : (presheafOfCategories (G ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hθ : θ ⋙ discreteProjection F = discreteProjection G) : G ⟶ F where
  app := fun U => ↾fun g => natTransAppOfBasedFunctor θ hθ U.unop g
  naturality {U U'} f := by
    ext g
    obtain ⟨W⟩ := U
    obtain ⟨V⟩ := U'
    dsimp [natTransAppOfBasedFunctor]
    have hu : (discreteProjection G).IsHomLift f.unop (homMk f.unop g) := by
      have h : (discreteProjection G).map (homMk f.unop g) = f.unop := rfl
      rw [← h]
      exact IsHomLift.map _ _
    exact elementOf_eq_map (P := F)
      (V := V) (W := W)
      (Functor.congr_obj hθ (⟨V, Discrete.mk (G.map f g)⟩ :
        (presheafOfCategories (G ⋙ typeToCat)).obj))
      (Functor.congr_obj hθ (⟨W, Discrete.mk g⟩ :
        (presheafOfCategories (G ⋙ typeToCat)).obj))
      f.unop (θ.map (homMk f.unop g))
      (Functor.isHomLift_map_of_comp_eq hθ f.unop (homMk f.unop g))

/-- The element of `F(p τ)` picked out by a 1-morphism `σ : 𝒯 ⥤ El F` over `C`, for `τ` an
object of `𝒯`. For `𝒯 = C` and `p = 𝟭 C` this is the global section of `F` named by a section of
the projection. -/
def sectionOfBasedFunctor {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C}
    (σ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hσ : σ ⋙ discreteProjection F = pT) (τ : 𝒯) : F.obj (op (pT.obj τ)) :=
  elementOf F (X := σ.obj τ) (V := pT.obj τ) (Functor.congr_obj hσ τ)

/-- The family of elements picked out by a 1-morphism `𝒯 ⥤ El F` over `C` is a global section of
the restriction of `F` along `pT`: it is compatible with restriction. -/
theorem sectionOfBasedFunctor_map {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C}
    (σ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hσ : σ ⋙ discreteProjection F = pT) {τ τ' : 𝒯} (f : τ ⟶ τ') :
    F.map (pT.map f).op (sectionOfBasedFunctor σ hσ τ') = sectionOfBasedFunctor σ hσ τ := by
  exact (elementOf_eq_map (P := F) (V := pT.obj τ) (W := pT.obj τ')
    (Functor.congr_obj hσ τ) (Functor.congr_obj hσ τ') (pT.map f) (σ.map f)
    (Functor.isHomLift_map_of_comp_eq hσ (pT.map f) f)).symm

end Translation

section FibrePresheaf

variable {G F : Cᵒᵖ ⥤ Type vC} (θ : G ⟶ F) (s : ∀ V : C, F.obj (op V))
  (hs : ∀ {V W : C} (f : V ⟶ W), F.map f.op (s W) = s V)

/-- The subpresheaf of `G` cut out by the equation `θ g = s`, for `θ : G ⟶ F` and `s` a global
section of `F`. It is the fibre product `G ×_F 1` of presheaves. -/
def fibrePresheaf : Cᵒᵖ ⥤ Type vC where
  obj U := { g : G.obj U // θ.app U g = s U.unop }
  -- the restriction of a section satisfying the equation satisfies it
  map {U U'} f := ↾fun g => ⟨G.map f g.1, by
    rw [NatTrans.naturality_apply θ f g.1, g.2]
    exact hs f.unop⟩
  map_id U := by
    ext g
    exact G.map_id_apply U g.1
  map_comp f g := by
    ext a
    exact G.map_comp_apply f g a.1

/-- The inclusion of the subpresheaf into `G`. -/
def fibrePresheafι : fibrePresheaf θ s hs ⟶ G where
  app _U := ↾fun g => g.1
  naturality _ _ _ := rfl

/-- The global section `s` of `F`, read as a morphism from the presheaf of points of an object
`T` of `C`. -/
def sectionHom (T : C) : yoneda.obj T ⟶ F where
  app U := ↾fun _ => s U.unop
  naturality {U U'} f := by
    ext _
    exact (hs f.unop).symm

/-- The unique morphism from the subpresheaf to the presheaf of points of a final object. -/
def fibrePresheafToTerminal {T : C} (hT : IsTerminal T) :
    fibrePresheaf θ s hs ⟶ yoneda.obj T where
  app U := ↾fun _ => hT.from U.unop
  naturality {U U'} f := by
    ext _
    exact hT.hom_ext _ _

/-- The morphism into the subpresheaf induced by a morphism into `G` whose composite with `θ` is
the constant section. -/
def fibrePresheafLift {T : C} {Z : Cᵒᵖ ⥤ Type vC} (a : Z ⟶ G) (b : Z ⟶ yoneda.obj T)
    (hab : a ≫ θ = b ≫ sectionHom s hs T) : Z ⟶ fibrePresheaf θ s hs where
  app U := ↾fun z => ⟨a.app U z, by
    have h := congrArg (fun (α : Z ⟶ F) => α.app U z) hab
    simpa [sectionHom] using h⟩
  naturality U U' f := by
    ext z
    refine Subtype.ext ?_
    exact NatTrans.naturality_apply a f z

/-- **The subpresheaf is the fibre product `G ×_F 1`.** The square formed by the inclusion into
`G` and the morphism to the presheaf of points of a final object `T` is cartesian over
`θ : G ⟶ F` and the section `s`. -/
theorem isPullback_fibrePresheaf {T : C} (hT : IsTerminal T) :
    IsPullback (fibrePresheafι θ s hs) (fibrePresheafToTerminal θ s hs hT) θ
      (sectionHom s hs T) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_
    (fun c => fibrePresheafLift θ s hs c.fst c.snd c.condition) (fun c => ?_) (fun c => ?_)
    (fun c l h₁ _ => ?_))
  · ext U z
    exact z.2
  · ext U z
    rfl
  · ext U z
    exact hT.hom_ext _ _
  · ext U z
    refine Subtype.ext ?_
    exact congrArg (fun (α : c.pt ⟶ G) => α.app U z) h₁

end FibrePresheaf

section Comparison

variable {G F : Cᵒᵖ ⥤ Type vC} {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C}
  (σ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
  (hσ : σ ⋙ discreteProjection F = pT)
  (θ : (presheafOfCategories (G ⋙ typeToCat)).obj ⥤
    (presheafOfCategories (F ⋙ typeToCat)).obj)
  (hθ : θ ⋙ discreteProjection F = discreteProjection G)

/-- The presheaf on `𝒯` whose category of elements is the 2-fibre product
`𝒯 ×_{σ, El F, θ} El G`: the subpresheaf of the restriction of `G` along `pT` cut out by the
equation `θ g = σ`. -/
abbrev twoFibreProductPresheaf : 𝒯ᵒᵖ ⥤ Type vC :=
  fibrePresheaf (Functor.whiskerLeft pT.op (natTransOfBasedFunctor θ hθ))
    (sectionOfBasedFunctor σ hσ) (fun f => sectionOfBasedFunctor_map σ hσ f)

/-- An object of the category of elements of the subpresheaf has the same image under the
1-morphism `σ` and under the 1-morphism `θ`: that is the equation the subpresheaf imposes. -/
theorem objEq (X : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj) :
    σ.obj X.base =
      θ.obj (⟨pT.obj X.base, Discrete.mk X.fiber.as.val⟩ :
        (presheafOfCategories (G ⋙ typeToCat)).obj) :=
  obj_eq_of_elementOf_eq (V := pT.obj X.base) (Functor.congr_obj hσ X.base)
    (Functor.congr_obj hθ (⟨pT.obj X.base, Discrete.mk X.fiber.as.val⟩ :
      (presheafOfCategories (G ⋙ typeToCat)).obj))
    X.fiber.as.property.symm

/-- The comparison isomorphism attached to an object of the category of elements of the
subpresheaf is vertical. -/
theorem isHomLift_eqToIso_objEq
    (X : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj) :
    (discreteProjection F).IsHomLift (𝟙 (pT.obj X.base)) (eqToIso (objEq σ hσ θ hθ X)).hom := by
  refine IsHomLift.of_fac' (discreteProjection F) (𝟙 (pT.obj X.base)) _
    (Functor.congr_obj hσ X.base)
    (Functor.congr_obj hθ (⟨pT.obj X.base, Discrete.mk X.fiber.as.val⟩ :
      (presheafOfCategories (G ⋙ typeToCat)).obj)) ?_
  rw [eqToIso.hom, eqToHom_map, Category.id_comp, eqToHom_trans]

/-- The object of the category of elements of `G` attached to an object of the category of
elements of the subpresheaf: it lies over the image under `pT` of the base and names the element
of `G` that the section carries. -/
abbrev toElementsG
    (X : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj) :
    (presheafOfCategories (G ⋙ typeToCat)).obj :=
  ⟨pT.obj X.base, Discrete.mk X.fiber.as.val⟩

/-- The morphism of the category of elements of `G` attached to a morphism of the category of
elements of the subpresheaf: it lies over the image under `pT` of the base morphism. -/
abbrev toElementsGMap
    {X Y : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj}
    (u : X ⟶ Y) : toElementsG σ hσ θ hθ X ⟶ toElementsG σ hσ θ hθ Y :=
  ⟨pT.map u.base, ⟨congrArg Subtype.val u.fiber.eq⟩⟩

/-- The morphism `toElementsGMap σ hσ θ hθ u` lies over the image under `pT` of the base
morphism of `u`. -/
@[simp] theorem toElementsGMap_base
    {X Y : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj}
    (u : X ⟶ Y) : (toElementsGMap σ hσ θ hθ u).base = pT.map u.base :=
  rfl

/-- The comparison functor from the category of elements of the subpresheaf to the 2-fibre
product `𝒯 ×_{σ, El F, θ} El G` taken in the categories over `C`. -/
noncomputable def toTwoFibreProduct :
    (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj ⥤
      TwoFibreProductOver pT (discreteProjection G) (discreteProjection F) σ θ where
  obj X :=
    { base := pT.obj X.base
      x := X.base
      y := toElementsG σ hσ θ hθ X
      hx := rfl
      hy := rfl
      iso := eqToIso (objEq σ hσ θ hθ X)
      vertical := isHomLift_eqToIso_objEq σ hσ θ hθ X }
  map {X Y} u :=
    { hbase := pT.map u.base
      a := u.base
      b := toElementsGMap σ hσ θ hθ u
      ha := IsHomLift.map pT u.base
      hb := isHomLift_base (P := G) (toElementsGMap σ hσ θ hθ u)
      w := by
        have h1 : pT.IsHomLift (pT.map u.base) u.base := IsHomLift.map pT u.base
        have hσm : (discreteProjection F).IsHomLift (pT.map u.base) (σ.map u.base) :=
          Functor.isHomLift_map_of_comp_eq hσ (pT.map u.base) u.base
        have hbg : (discreteProjection G).IsHomLift (pT.map u.base)
            (toElementsGMap σ hσ θ hθ u) :=
          isHomLift_base (P := G) (toElementsGMap σ hσ θ hθ u)
        have hθm : (discreteProjection F).IsHomLift (pT.map u.base)
            (θ.map (toElementsGMap σ hσ θ hθ u)) :=
          Functor.isHomLift_map_of_comp_eq hθ (pT.map u.base) (toElementsGMap σ hσ θ hθ u)
        have hY := isHomLift_eqToIso_objEq σ hσ θ hθ Y
        have hX := isHomLift_eqToIso_objEq σ hσ θ hθ X
        have hL : (discreteProjection F).IsHomLift (pT.map u.base)
            (σ.map u.base ≫ (eqToIso (objEq σ hσ θ hθ Y)).hom) := by
          simpa using IsHomLift.comp (discreteProjection F) (pT.map u.base) (𝟙 (pT.obj Y.base))
            (σ.map u.base) (eqToIso (objEq σ hσ θ hθ Y)).hom
        have hR : (discreteProjection F).IsHomLift (pT.map u.base)
            ((eqToIso (objEq σ hσ θ hθ X)).hom ≫ θ.map (toElementsGMap σ hσ θ hθ u)) := by
          simpa using IsHomLift.comp (discreteProjection F) (𝟙 (pT.obj X.base)) (pT.map u.base)
            (eqToIso (objEq σ hσ θ hθ X)).hom (θ.map (toElementsGMap σ hσ θ hθ u))
        have e1 := IsHomLift.fac' (discreteProjection F) (pT.map u.base)
          (σ.map u.base ≫ (eqToIso (objEq σ hσ θ hθ Y)).hom)
        have e2 := IsHomLift.fac' (discreteProjection F) (pT.map u.base)
          ((eqToIso (objEq σ hσ θ hθ X)).hom ≫ θ.map (toElementsGMap σ hσ θ hθ u))
        exact elements_hom_ext _ _ (e1.trans e2.symm) }
  map_id X := TwoFibreProductOver.Hom.ext' rfl (elements_hom_ext _ _ (pT.map_id X.base))
  map_comp u v :=
    TwoFibreProductOver.Hom.ext' rfl (elements_hom_ext _ _ (pT.map_comp u.base v.base))

/-- The comparison functor sends an object to one with the same base. -/
@[simp] theorem toTwoFibreProduct_obj_x
    (X : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj) :
    ((toTwoFibreProduct σ hσ θ hθ).obj X).x = X.base := rfl

/-- The comparison functor sends a morphism to one with the same base. -/
@[simp] theorem toTwoFibreProduct_map_a
    {X Y : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj}
    (u : X ⟶ Y) : ((toTwoFibreProduct σ hσ θ hθ).map u).a = u.base := rfl

/-- The comparison functor sends a morphism to one with the given `El G`-component. -/
@[simp] theorem toTwoFibreProduct_map_b
    {X Y : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj}
    (u : X ⟶ Y) : ((toTwoFibreProduct σ hσ θ hθ).map u).b.base = pT.map u.base := rfl

/-- The comparison functor is strictly over `𝒯`. -/
theorem toTwoFibreProduct_comp_fst :
    toTwoFibreProduct σ hσ θ hθ ⋙
        TwoFibreProductOver.fst pT (discreteProjection G) (discreteProjection F) σ θ =
      discreteProjection (twoFibreProductPresheaf σ hσ θ hθ) :=
  rfl

/-- **The 2-fibre product of a 1-morphism out of `𝒯` with a 1-morphism of categories of
elements.** The comparison functor from the category of elements of the subpresheaf
`{g | θ g = σ}` of the restriction of `G` along `pT` to the 2-fibre product
`𝒯 ×_{σ, El F, θ} El G`, taken in the categories over `C`, is an equivalence.

Faithfulness and fullness come from the fibres being discrete: a morphism of either side is
determined by the morphism of `𝒯` it lies over, and the equation the subpresheaf imposes is
exactly the one a morphism of the 2-fibre product carries. For essential surjectivity, the
comparison isomorphism of an object of the 2-fibre product is vertical, so the two objects of
`El F` it compares name the same element, which is the equation the subpresheaf imposes. -/
theorem isEquivalence_toTwoFibreProduct :
    (toTwoFibreProduct σ hσ θ hθ).IsEquivalence := by
  have : (toTwoFibreProduct σ hσ θ hθ).Faithful := by
    constructor
    intro X Y u v h
    exact elements_hom_ext _ _ (by simpa using congrArg TwoFibreProductOver.Hom.a h)
  have : (toTwoFibreProduct σ hσ θ hθ).Full := by
    constructor
    intro X Y φ
    have h1 := φ.ha
    have h2 := φ.hb
    have hφ : pT.map φ.a = φ.b.base :=
      (IsHomLift.fac' pT φ.hbase φ.a).trans
        (IsHomLift.fac' (discreteProjection G) φ.hbase φ.b).symm
    have hval : X.fiber.as.val = G.map (pT.map φ.a).op Y.fiber.as.val := by
      rw [hφ]
      exact φ.b.fiber.eq
    exact ⟨⟨φ.a, ⟨Subtype.ext hval⟩⟩, TwoFibreProductOver.Hom.ext' rfl (elements_hom_ext _ _ hφ)⟩
  have : (toTwoFibreProduct σ hσ θ hθ).EssSurj := by
    constructor
    intro Q
    obtain ⟨Qbase, Qx, ⟨Qyb, Qyf⟩, Qhx, Qhy, Qiso, Qvert⟩ := Q
    obtain rfl : pT.obj Qx = Qbase := Qhx
    obtain rfl : Qyb = pT.obj Qx := Qhy
    have h := elementOf_eq_map (P := F) (V := pT.obj Qx) (W := pT.obj Qx)
      (Functor.congr_obj hσ Qx)
      (Functor.congr_obj hθ (⟨pT.obj Qx, Qyf⟩ :
        (presheafOfCategories (G ⋙ typeToCat)).obj))
      (𝟙 (pT.obj Qx)) Qiso.hom Qvert
    rw [op_id, F.map_id_apply] at h
    let Xel : (presheafOfCategories (twoFibreProductPresheaf σ hσ θ hθ ⋙ typeToCat)).obj :=
      ⟨Qx, Discrete.mk ⟨Qyf.as, h.symm⟩⟩
    refine ⟨Xel, ⟨?_⟩⟩
    have hiso : eqToIso (objEq σ hσ θ hθ Xel) = Qiso := by
      refine Iso.ext (elements_hom_ext _ _ ?_)
      rw [← discreteProjection_map Qiso.hom,
        IsHomLift.fac' (discreteProjection F) (𝟙 (pT.obj Qx)) Qiso.hom,
        Category.id_comp, eqToHom_trans,
        ← discreteProjection_map (eqToIso (objEq σ hσ θ hθ Xel)).hom,
        eqToIso.hom, eqToHom_map]
      rfl
    exact eqToIso (TwoFibreProductOver.obj_ext hiso)
  exact Functor.IsEquivalence.mk

end Comparison

end CategoryTheory.PresheafOfCategories

end
