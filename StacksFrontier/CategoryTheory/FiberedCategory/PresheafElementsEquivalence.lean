module

public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements

/-!
# The category of elements of a presheaf of sets determines the presheaf

Let `C` be a category and let `G`, `F` be presheaves of sets on `C`, possibly with values in
different universes. Their categories of elements (Stacks 02XV applied to the presheaves of
discrete categories `G ⋙ typeToCat`, `F ⋙ typeToCat`) are equivalent in the 2-category of
categories over `C` exactly when `G` and `F` become isomorphic after both are lifted to a common
value universe.

This is the general-presheaf form of the comparison Stacks 0045 and 04SD make for a category
fibred in setoids: a category over `C` equivalent over `C` to the category of elements of a
presheaf of sets determines that presheaf, pointwise and compatibly with restriction. It is
stated here for two *presheaves* rather than for a general category fibred in setoids, which is
the only generality representability by an algebraic space (Stacks 04SV) and by algebraic spaces
(Stacks 02ZW) need: both are the existence of an equivalence over the site with the category of
elements of a presheaf, so comparing two representing presheaves is comparing two such
categories of elements.

## Main definitions

* `CategoryTheory.PresheafOfCategories.PointwiseEquiv`: a family of bijections `G U ≃ F U`
  compatible with restriction. Since the two presheaves may land in different universes they are
  not objects of one presheaf category, so this is the form the comparison takes;
  `CategoryTheory.PresheafOfCategories.PointwiseEquiv.toUliftIso` and
  `CategoryTheory.PresheafOfCategories.PointwiseEquiv.ofUliftIso` identify it with an isomorphism
  of the universe-lifted presheaves.
* `CategoryTheory.PresheafOfCategories.elementsFiberEquiv`: the fibre of the category of elements
  of `G` over `U` is `G(U)`.
* `CategoryTheory.PresheafOfCategories.fiberFunctorOfComp`: the functor on fibre categories
  induced by a functor strictly over `C`.
* `CategoryTheory.PresheafOfCategories.mapElements`: the functor of categories of elements
  attached to a `PointwiseEquiv`.

## Main results

* `CategoryTheory.PresheafOfCategories.equivalenceOverOfPointwiseEquiv` and
  `CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver`: the two directions of the
  comparison.
* `CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_iff`: the two directions combined,
  as a biconditional between the existence of an equivalence over `C` and the existence of an
  isomorphism of the universe-lifted presheaves.

## Implementation notes

`CategoryTheory.PresheafOfCategories.elementsFiberEquiv`,
`CategoryTheory.PresheafOfCategories.elementsFiberEquiv_map_of_isHomLift` and
`CategoryTheory.PresheafOfCategories.fiberFunctorOfComp` are the universe-general forms of
`CategoryTheory.PresheafOfCategories.discreteFiberEquiv`,
`CategoryTheory.PresheafOfCategories.discreteFiberEquiv_eq_map_of_isHomLift` and
`CategoryTheory.Functor.fiberFunctorOfCompEq`: the first two of those are stated only for a
presheaf with values in the morphism universe of `C`, and the third only for total categories
whose morphism universe is that of `C`, whereas the presheaf compared here with an algebraic
space is a presheaf of morphisms of a category fibred in groupoids whose morphism universe is
free. The proofs are the same.

The forward direction reads the bijection off the fibre categories: the fibres of a category of
elements are discrete, so a functor over `C` between two of them is a map of the presheaves, and
the unit and counit of an equivalence over `C` have vertical components, hence identify an object
of a fibre with its image under the round trip. The backward direction is the Grothendieck
construction applied to the family of bijections, whose unit and counit are the identity on bases.
-/

@[expose] public section

open CategoryTheory Opposite Pseudofunctor

universe v₁ u₁ a b v₂ u₂ v₃ u₃

namespace CategoryTheory.PresheafOfCategories


variable {C : Type u₁} [Category.{v₁} C]

/-- The fibre of the category of elements of `G` over `U` is `G(U)`. -/
def elementsFiberEquiv (G : Cᵒᵖ ⥤ Type a) (U : C) :
    (presheafOfCategories (G ⋙ typeToCat)).p.Fiber U ≃ G.obj (op U) where
  toFun x := cast (congrArg (fun V : C => G.obj (op V)) x.2) x.1.fiber.as
  invFun s := ⟨⟨U, Discrete.mk s⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨V, s⟩, hV⟩
    change V = U at hV
    subst hV
    cases s
    rfl
  right_inv _ := rfl

/-- A morphism of the category of elements lying over `f` identifies the element named by its
source with the restriction along `f` of the element named by its target. -/
lemma elementsFiberEquiv_map_of_isHomLift (G : Cᵒᵖ ⥤ Type a) {V U : C} (f : V ⟶ U)
    (x : (presheafOfCategories (G ⋙ typeToCat)).p.Fiber U)
    (y : (presheafOfCategories (G ⋙ typeToCat)).p.Fiber V) (φ : y.1 ⟶ x.1)
    (hφ : (presheafOfCategories (G ⋙ typeToCat)).p.IsHomLift f φ) :
    elementsFiberEquiv G V y = G.map f.op (elementsFiberEquiv G U x) := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases hx
  cases hy
  have := hφ
  have hbase : φ.base = f := by
    have h := IsHomLift.fac' (presheafOfCategories (G ⋙ typeToCat)).p f φ
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
    exact h
  have hval : y.fiber.as = G.map φ.base.op x.fiber.as := Discrete.eq_of_hom φ.fiber
  rwa [hbase] at hval

/-- Two objects of one fibre of the category of elements connected by a morphism of that fibre
name the same element. -/
lemma elementsFiberEquiv_eq_of_hom (G : Cᵒᵖ ⥤ Type a) {U : C}
    {x y : (presheafOfCategories (G ⋙ typeToCat)).p.Fiber U} (φ : x ⟶ y) :
    elementsFiberEquiv G U x = elementsFiberEquiv G U y := by
  have h := elementsFiberEquiv_map_of_isHomLift G (𝟙 U) y x
    (Functor.Fiber.fiberInclusion.map φ) φ.2
  rw [h, op_id, G.map_id]
  rfl

/-- A functor strictly over `C` transports `CategoryTheory.Functor.IsHomLift`. -/
lemma isHomLift_map_of_comp {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    {q : D ⥤ C} {r : E ⥤ C} {H : D ⥤ E} (hH : H ⋙ r = q) {U V : C} (f : V ⟶ U) {z w : D}
    (φ : z ⟶ w) (h : q.IsHomLift f φ) : r.IsHomLift f (H.map φ) := by
  have := h
  refine IsHomLift.of_fac' r _ _ ((Functor.congr_obj hH z).trans
    (IsHomLift.domain_eq q f φ)) ((Functor.congr_obj hH w).trans
    (IsHomLift.codomain_eq q f φ)) ?_
  have hmap : r.map (H.map φ) = eqToHom (Functor.congr_obj hH z) ≫ q.map φ ≫
      eqToHom (Functor.congr_obj hH w).symm := by
    have := Functor.congr_hom hH φ
    simp only [Functor.comp_map] at this
    rw [← this]
  rw [hmap, IsHomLift.fac' q f φ]
  simp

/-- The functor on fibres induced by a functor strictly over `C`. -/
def fiberFunctorOfComp {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    {q : D ⥤ C} {r : E ⥤ C} {H : D ⥤ E} (hH : H ⋙ r = q) (U : C) :
    q.Fiber U ⥤ r.Fiber U where
  obj z := ⟨H.obj z.1, (Functor.congr_obj hH z.1).trans z.2⟩
  map {_ _} φ := ⟨H.map (Functor.Fiber.fiberInclusion.map φ),
    isHomLift_map_of_comp hH (𝟙 U) _ φ.2⟩
  map_id _ := Functor.Fiber.hom_ext (H.map_id _)
  map_comp _ _ := Functor.Fiber.hom_ext (H.map_comp _ _)

/-- A pointwise family of bijections between two presheaves of sets, compatible with
restriction. The two presheaves may land in different universes, which is why this is a family
of bijections and not an isomorphism of presheaves. -/
structure PointwiseEquiv (G : Cᵒᵖ ⥤ Type a) (F : Cᵒᵖ ⥤ Type b) where
  /-- The bijection at an object. -/
  equiv : ∀ U : Cᵒᵖ, G.obj U ≃ F.obj U
  /-- Compatibility with restriction. -/
  naturality : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (s : G.obj U),
    equiv V (G.map f s) = F.map f (equiv U s)

namespace PointwiseEquiv

variable {G : Cᵒᵖ ⥤ Type a} {F : Cᵒᵖ ⥤ Type b}

/-- The inverse family of bijections. -/
def symm (pe : PointwiseEquiv G F) : PointwiseEquiv F G where
  equiv U := (pe.equiv U).symm
  naturality f t := by
    apply (pe.equiv _).injective
    rw [Equiv.apply_symm_apply, pe.naturality, Equiv.apply_symm_apply]

/-- The bijections of the inverse family are the inverses of the original bijections. -/
@[simp] lemma symm_equiv (pe : PointwiseEquiv G F) (U : Cᵒᵖ) :
    pe.symm.equiv U = (pe.equiv U).symm := rfl

/-- The isomorphism of universe-lifted presheaves attached to a pointwise family of
bijections. -/
def toUliftIso (pe : PointwiseEquiv G F) :
    G ⋙ uliftFunctor.{b, a} ≅ F ⋙ uliftFunctor.{a, b} :=
  NatIso.ofComponents
    (fun U => Equiv.toIso (Equiv.ulift.trans ((pe.equiv U).trans Equiv.ulift.symm)))
    (fun f => by
      ext s
      exact congrArg ULift.up (pe.naturality f s.down))

/-- The pointwise family of bijections attached to an isomorphism of universe-lifted
presheaves. -/
def ofUliftIso (e : G ⋙ uliftFunctor.{b, a} ≅ F ⋙ uliftFunctor.{a, b}) :
    PointwiseEquiv G F where
  equiv U := Equiv.ulift.symm.trans ((e.app U).toEquiv.trans Equiv.ulift)
  naturality {U V} f s := by
    have h := NatTrans.naturality_apply e.hom f (ULift.up s : (G ⋙ uliftFunctor.{b, a}).obj U)
    exact congrArg ULift.down h

end PointwiseEquiv

section Comparison

variable {G : Cᵒᵖ ⥤ Type a} {F : Cᵒᵖ ⥤ Type b}

/-- The functor between categories of elements attached to a pointwise family of bijections. -/
def mapElements (pe : PointwiseEquiv G F) :
    (presheafOfCategories (G ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (F ⋙ typeToCat)).obj where
  obj Z := ⟨Z.base, Discrete.mk (pe.equiv (op Z.base) Z.fiber.as)⟩
  map {Z W} u := ⟨u.base, Discrete.eqToHom (by
    have h : Z.fiber.as = G.map u.base.op W.fiber.as := Discrete.eq_of_hom u.fiber
    rw [h, pe.naturality]
    rfl)⟩
  map_id _ := elements_hom_ext _ _ rfl
  map_comp _ _ := elements_hom_ext _ _ rfl

/-- The functor `CategoryTheory.PresheafOfCategories.mapElements` keeps the base object. -/
@[simp] lemma mapElements_obj_base (pe : PointwiseEquiv G F)
    (Z : (presheafOfCategories (G ⋙ typeToCat)).obj) :
    ((mapElements pe).obj Z).base = Z.base := rfl

/-- The functor `CategoryTheory.PresheafOfCategories.mapElements` lies strictly over `C`: followed
by the projection of the target category of elements it is the projection of the source. -/
lemma mapElements_comp (pe : PointwiseEquiv G F) :
    mapElements pe ⋙ (presheafOfCategories (F ⋙ typeToCat)).p =
      (presheafOfCategories (G ⋙ typeToCat)).p := rfl

/-- **The category of elements of a presheaf of sets determines the presheaf.** A pointwise
family of bijections of two presheaves of sets gives an equivalence over the base between their
categories of elements. -/
def equivalenceOverOfPointwiseEquiv (pe : PointwiseEquiv G F) :
    StacksRepresentableCFG.EquivalenceOver (presheafOfCategories (G ⋙ typeToCat)).p
      (presheafOfCategories (F ⋙ typeToCat)).p where
  hom := ⟨mapElements pe, rfl⟩
  inv := ⟨mapElements pe.symm, rfl⟩
  unitIso := NatIso.ofComponents
    (fun Z => elementsIsoOfBaseIso (Iso.refl Z.base) (by
      change Z.fiber.as = G.map (𝟙 Z.base).op
        ((pe.equiv (op Z.base)).symm (pe.equiv (op Z.base) Z.fiber.as))
      rw [op_id, G.map_id_apply, Equiv.symm_apply_apply]))
    (by
      intro Z W u
      refine elements_hom_ext _ _ ?_
      change u.base ≫ 𝟙 W.base = 𝟙 Z.base ≫ u.base
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents
    (fun Z => elementsIsoOfBaseIso (Iso.refl Z.base) (by
      change pe.equiv (op Z.base) ((pe.equiv (op Z.base)).symm Z.fiber.as) =
        F.map (𝟙 Z.base).op Z.fiber.as
      rw [op_id, F.map_id_apply, Equiv.apply_symm_apply]))
    (by
      intro Z W u
      refine elements_hom_ext _ _ ?_
      change u.base ≫ 𝟙 W.base = 𝟙 Z.base ≫ u.base
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
    intro Z
    refine IsHomLift.of_fac' (presheafOfCategories (G ⋙ typeToCat)).p _ _ rfl rfl ?_
    change 𝟙 Z.base = _
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
    intro Z
    refine IsHomLift.of_fac' (presheafOfCategories (F ⋙ typeToCat)).p _ _ rfl rfl ?_
    change 𝟙 Z.base = _
    simp only [Category.id_comp, eqToHom_trans]
    rfl

/-- **The category of elements of a presheaf of sets determines the presheaf, converse
direction.** An equivalence over the base between the categories of elements of two presheaves
of sets gives a pointwise family of bijections of the presheaves. -/
noncomputable def pointwiseEquivOfEquivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver (presheafOfCategories (G ⋙ typeToCat)).p
      (presheafOfCategories (F ⋙ typeToCat)).p) : PointwiseEquiv G F where
  equiv U :=
    { toFun := fun s => elementsFiberEquiv F U.unop
        ((fiberFunctorOfComp e.hom.w U.unop).obj ((elementsFiberEquiv G U.unop).symm s))
      invFun := fun t => elementsFiberEquiv G U.unop
        ((fiberFunctorOfComp e.inv.w U.unop).obj ((elementsFiberEquiv F U.unop).symm t))
      left_inv := fun s => by
        dsimp only
        rw [Equiv.symm_apply_apply]
        have hiso : (elementsFiberEquiv G U.unop).symm s ≅
            (fiberFunctorOfComp e.inv.w U.unop).obj
              ((fiberFunctorOfComp e.hom.w U.unop).obj
                ((elementsFiberEquiv G U.unop).symm s)) :=
          Functor.Fiber.isoMk (e.unitIso.app ((elementsFiberEquiv G U.unop).symm s).1) (by
            have hl := e.isHomLift_unitIso_hom_app ((elementsFiberEquiv G U.unop).symm s).1
            rwa [((elementsFiberEquiv G U.unop).symm s).2] at hl)
        rw [← elementsFiberEquiv_eq_of_hom G hiso.hom]
        exact (elementsFiberEquiv G U.unop).apply_symm_apply s
      right_inv := fun t => by
        dsimp only
        rw [Equiv.symm_apply_apply]
        have hiso : (fiberFunctorOfComp e.hom.w U.unop).obj
              ((fiberFunctorOfComp e.inv.w U.unop).obj
                ((elementsFiberEquiv F U.unop).symm t)) ≅
            (elementsFiberEquiv F U.unop).symm t :=
          Functor.Fiber.isoMk (e.counitIso.app ((elementsFiberEquiv F U.unop).symm t).1) (by
            have hl := e.isHomLift_counitIso_hom_app ((elementsFiberEquiv F U.unop).symm t).1
            rwa [((elementsFiberEquiv F U.unop).symm t).2] at hl)
        rw [elementsFiberEquiv_eq_of_hom F hiso.hom]
        exact (elementsFiberEquiv F U.unop).apply_symm_apply t }
  naturality {U V} f s := by
    have hφlift : (presheafOfCategories (G ⋙ typeToCat)).p.IsHomLift f.unop
        (⟨f.unop, Discrete.eqToHom rfl⟩ :
          (⟨V.unop, Discrete.mk (G.map f s)⟩ :
            (presheafOfCategories (G ⋙ typeToCat)).obj) ⟶ ⟨U.unop, Discrete.mk s⟩) :=
      IsHomLift.map (presheafOfCategories (G ⋙ typeToCat)).p
        (⟨f.unop, Discrete.eqToHom rfl⟩ :
          (⟨V.unop, Discrete.mk (G.map f s)⟩ :
            (presheafOfCategories (G ⋙ typeToCat)).obj) ⟶ ⟨U.unop, Discrete.mk s⟩)
    exact elementsFiberEquiv_map_of_isHomLift F f.unop
      ((fiberFunctorOfComp e.hom.w U.unop).obj ⟨⟨U.unop, Discrete.mk s⟩, rfl⟩)
      ((fiberFunctorOfComp e.hom.w V.unop).obj ⟨⟨V.unop, Discrete.mk (G.map f s)⟩, rfl⟩)
      (e.hom.functor.map ⟨f.unop, Discrete.eqToHom rfl⟩)
      (isHomLift_map_of_comp e.hom.w f.unop _ hφlift)

/-- **The category of elements of a presheaf of sets determines the presheaf.** The categories
of elements of two presheaves of sets are equivalent over the base exactly when the presheaves
become isomorphic after lifting both to a common value universe. -/
theorem nonempty_equivalenceOver_iff (G : Cᵒᵖ ⥤ Type a) (F : Cᵒᵖ ⥤ Type b) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
        (presheafOfCategories (G ⋙ typeToCat)).p
        (presheafOfCategories (F ⋙ typeToCat)).p) ↔
      Nonempty (G ⋙ uliftFunctor.{b, a} ≅ F ⋙ uliftFunctor.{a, b}) :=
  ⟨fun ⟨e⟩ => ⟨(pointwiseEquivOfEquivalenceOver e).toUliftIso⟩,
    fun ⟨i⟩ => ⟨equivalenceOverOfPointwiseEquiv (PointwiseEquiv.ofUliftIso i)⟩⟩

end Comparison


section IsoClass

universe v₄ u₄

variable {𝒮 : Type u₄} [Category.{v₄} 𝒮]

/-- For a fibred category `p` equivalent over `C` to the category of elements of `F`, the
isomorphism classes of the fibre of `p` over `U` are the elements of `F(U)`: carry a fibre object
through the equivalence and read off the element it names.

This is the universe-general form of `CategoryTheory.PresheafOfCategories.isoClassEquiv`, which
is stated only for a total category whose morphism universe is that of `C`. The proof is the
same, with `CategoryTheory.PresheafOfCategories.fiberFunctorOfComp` and
`CategoryTheory.PresheafOfCategories.elementsFiberEquiv` in place of
`CategoryTheory.Functor.fiberFunctorOfCompEq` and
`CategoryTheory.PresheafOfCategories.discreteFiberEquiv`; well-definedness and the second round
trip are `CategoryTheory.PresheafOfCategories.elementsFiberEquiv_eq_of_hom`, so discreteness of
the fibres of the category of elements is not needed explicitly. -/
noncomputable def elementsIsoClassEquiv {p : 𝒮 ⥤ C} [p.IsFibered] (F : Cᵒᵖ ⥤ Type a)
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    (U : C) :
    p.isoClassPresheaf.obj (op U) ≃ F.obj (op U) where
  toFun c := Quotient.liftOn c
    (fun x => elementsFiberEquiv F U ((fiberFunctorOfComp e.hom.w U).obj x))
    (by
      intro x y h
      obtain ⟨i⟩ := (Functor.isIsomorphicSetoid_r_iff _ _).1 h
      exact elementsFiberEquiv_eq_of_hom F ((fiberFunctorOfComp e.hom.w U).mapIso i).hom)
  invFun s := Functor.isoClassMk p
    ((fiberFunctorOfComp e.inv.w U).obj ((elementsFiberEquiv F U).symm s))
  left_inv c := by
    induction c using Quotient.ind with
    | _ x =>
      change Functor.isoClassMk p
        ((fiberFunctorOfComp e.inv.w U).obj
          ((elementsFiberEquiv F U).symm
            (elementsFiberEquiv F U ((fiberFunctorOfComp e.hom.w U).obj x)))) = _
      rw [Equiv.symm_apply_apply]
      apply Functor.isoClassMk_eq_of_iso
      exact Functor.Fiber.isoMk (e.unitIso.app x.1).symm (by
        have hl := e.isHomLift_unitIso_inv_app x.1
        rwa [x.2] at hl)
  right_inv s := by
    have hIso : (fiberFunctorOfComp e.hom.w U).obj
        ((fiberFunctorOfComp e.inv.w U).obj ((elementsFiberEquiv F U).symm s))
        ≅ (elementsFiberEquiv F U).symm s :=
      Functor.Fiber.isoMk (e.counitIso.app ((elementsFiberEquiv F U).symm s).1) (by
        have hl := e.isHomLift_counitIso_hom_app ((elementsFiberEquiv F U).symm s).1
        rwa [((elementsFiberEquiv F U).symm s).2] at hl)
    exact (elementsFiberEquiv_eq_of_hom F hIso.hom).trans
      (Equiv.apply_symm_apply (elementsFiberEquiv F U) s)

/-- `CategoryTheory.PresheafOfCategories.elementsIsoClassEquiv` is compatible with restriction:
the class of a chosen pullback of `x` along `f` names the restriction along `f` of the element
named by the class of `x`. -/
theorem elementsIsoClassEquiv_naturality {p : 𝒮 ⥤ C} [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (F : Cᵒᵖ ⥤ Type a)
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    {U V : C} (f : V ⟶ U) (c : p.isoClassPresheaf.obj (op U)) :
    elementsIsoClassEquiv F e V (p.isoClassPresheaf.map f.op c) =
      F.map f.op (elementsIsoClassEquiv F e U c) := by
  let _ : p.IsPreFibered := hp.isFibered.toIsPreFibered
  induction c using Quotient.ind with
  | _ x =>
    change elementsIsoClassEquiv F e V
      (p.isoClassPresheaf.map f.op (Functor.isoClassMk p x)) = _
    rw [Functor.isoClassPresheaf_map_isoClassMk]
    change elementsFiberEquiv F V
      ((fiberFunctorOfComp e.hom.w V).obj (p.pullbackFiber x f)) =
        F.map f.op (elementsFiberEquiv F U ((fiberFunctorOfComp e.hom.w U).obj x))
    exact elementsFiberEquiv_map_of_isHomLift F f
      ((fiberFunctorOfComp e.hom.w U).obj x)
      ((fiberFunctorOfComp e.hom.w V).obj (p.pullbackFiber x f))
      (e.hom.functor.map (Functor.IsPreFibered.pullbackMap x.2 f))
      (isHomLift_map_of_comp e.hom.w f (Functor.IsPreFibered.pullbackMap x.2 f) inferInstance)

end IsoClass

end CategoryTheory.PresheafOfCategories

end
