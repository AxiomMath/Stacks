module

public import Mathlib.CategoryTheory.Yoneda
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiscretePresheaf
public import StacksFrontier.Deformation.Cofibered.TwoCategory
public import StacksFrontier.Deformation.Groupoid.Basic

/-!
# Categories cofibered in groupoids attached to functors

Remarks (9), (11) and (12) of Stacks 06GK.

* (9) A functor `F : C ⥤ Groupoids` gives a category cofibered in groupoids over `C`: its objects
  are the pairs `(U, x)` with `x` an object of `F(U)`, its morphisms `(U, x) ⟶ (V, y)` the pairs
  `(f, a)` with `f : U ⟶ V` and `a : F(f)(x) ⟶ y` in `F(V)`, and its projection sends `(U, x)` to
  `U`. This is Mathlib's Grothendieck construction `Grothendieck (F ⋙ Grpd.forgetToCat)`
  (`Deformation.ofGroupoidFunctor`, `Deformation.isCofiberedInGroupoids_ofGroupoidFunctor`).
* (11) A functor `F : C ⥤ Type` read as a functor to discrete groupoids gives, by (9), a category
  cofibered in sets, i.e. cofibered in groupoids with discrete fibres
  (`Deformation.ofSetFunctor`, `Deformation.isDiscrete_fiber_ofSetFunctor`). This is a fully
  faithful embedding of the category of functors `C ⥤ Type` into `Cof(C)`
  (`Deformation.ofSetFunctorFunctor`, `Deformation.ofSetFunctorFullyFaithful`), and the
  2-morphisms between 1-morphisms into its image are trivial
  (`Deformation.subsingleton_twoHom_ofSetFunctor`, `Deformation.eq_of_twoHom_ofSetFunctor`), so it
  is fully faithful as a functor into the `(2, 1)`-category `Cof(C)`.
* (12) For `U : C` the functor `Mor_C(U, -)` is `coyoneda.obj (op U)`, and `U ↦ Mor_C(U, -)` is a
  fully faithful embedding `Cᵒᵖ ⥤ (C ⥤ Type)` (`Deformation.underlineFullyFaithful`, which is
  Mathlib's `CategoryTheory.Coyoneda.fullyFaithful`).

## References

* [Stacks Project, Tag 06GK](https://stacks.math.columbia.edu/tag/06GK)
* [Stacks Project, Tag 06GN](https://stacks.math.columbia.edu/tag/06GN)
* [Stacks Project, Tag 06GP](https://stacks.math.columbia.edu/tag/06GP)
* [Stacks Project, Tag 06GQ](https://stacks.math.columbia.edu/tag/06GQ)
-/

@[expose] public section

namespace Deformation

open CategoryTheory Functor

universe v₁ u₁ w

variable {C : Type u₁} [Category.{v₁} C]

/-! ### (9) The category cofibered in groupoids of a functor to groupoids -/

/-- **Stacks 06GK (9).** The category over `C` attached to a functor `F : C ⥤ Groupoids`: objects
the pairs `(U, x)` with `x` an object of `F(U)`, morphisms `(U, x) ⟶ (V, y)` the pairs `(f, a)`
with `f : U ⟶ V` and `a : F(f)(x) ⟶ y` (`ofGroupoidFunctorHomEquiv`), and projection
`(U, x) ↦ U`. -/
@[stacks 06GK "(9) the category cofibered in groupoids associated to a functor C → Groupoids"]
abbrev ofGroupoidFunctor (F : C ⥤ Grpd.{w, w}) : BasedCategory C :=
  BasedCategory.ofFunctor (Grothendieck.forget (F ⋙ Grpd.forgetToCat))

/-- **Stacks 06GK (9).** A morphism `(U, x) ⟶ (V, y)` of the category attached to
`F : C ⥤ Groupoids` is a pair `(f, a)` with `f : U ⟶ V` and `a : F(f)(x) ⟶ y` in `F(V)`. -/
@[stacks 06GK "(9) morphisms (U, x) → (V, y) are pairs (f, a) with a : F(f)(x) → y"]
def ofGroupoidFunctorHomEquiv (F : C ⥤ Grpd.{w, w}) (X Y : (ofGroupoidFunctor F).obj) :
    (X ⟶ Y) ≃ Σ f : X.base ⟶ Y.base, ((F.map f).obj X.fiber ⟶ Y.fiber) where
  toFun g := ⟨g.base, g.fiber⟩
  invFun g := ⟨g.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stacks 06GK (9).** The category attached to a functor `C ⥤ Groupoids` is cofibered in
groupoids over `C`. -/
@[stacks 06GK "(9) the category associated to a functor C → Groupoids is cofibered in groupoids"]
theorem isCofiberedInGroupoids_ofGroupoidFunctor (F : C ⥤ Grpd.{w, w}) :
    IsCofiberedInGroupoids (ofGroupoidFunctor F).p :=
  isCofiberedInGroupoids_grothendieckForget _ (fun T ↦ inferInstanceAs (IsGroupoid (F.obj T)))

/-! ### (11) The category cofibered in sets of a functor to sets -/

/-- **Stacks 06GK (11).** The category cofibered in sets attached to a functor `F : C ⥤ Type`:
the construction (9) applied to `F`, each set being read as a discrete groupoid. -/
@[stacks 06GK "(11) the category cofibered in sets associated to a functor C → Sets"]
abbrev ofSetFunctor (F : C ⥤ Type w) : BasedCategory C :=
  ofGroupoidFunctor (F ⋙ typeToGrpd)

section Discrete

variable {G : C ⥤ Type w}

/-- Any two morphisms of a discrete category with the same source and target agree. -/
theorem discrete_hom_eq {X : Type w} {a b : Discrete X} (f g : a ⟶ b) : f = g :=
  Subsingleton.elim f g

/-- In the category attached to a functor to sets, two morphisms with the same image in `C`
agree: the fibre categories have no non-identity morphisms. -/
theorem ofSetFunctor_hom_ext {X Y : (ofSetFunctor G).obj} (f g : X ⟶ Y)
    (h : f.base = g.base) : f = g :=
  Grothendieck.ext f g h (discrete_hom_eq (X := G.obj Y.base) _ _)

instance faithful_ofSetFunctor_p : (ofSetFunctor G).p.Faithful where
  map_injective {_ _} {f g} h := ofSetFunctor_hom_ext f g h

/-- A morphism `(U, x) ⟶ (V, y)` of the category attached to a functor `G` to sets lying over
`f : U ⟶ V` carries `x` to `y`: `G(f)(x) = y`. -/
theorem ofSetFunctor_map_fiber {X Y : (ofSetFunctor G).obj} (f : X ⟶ Y) :
    G.map f.base X.fiber.as = Y.fiber.as :=
  Discrete.eq_of_hom f.fiber

/-- Two objects of the category attached to a functor to sets over equal objects of `C`, with
values matching along that equality, are equal. -/
theorem ofSetFunctor_obj_ext {X Y : (ofSetFunctor G).obj} (h : X.base = Y.base)
    (hf : G.map (eqToHom h) X.fiber.as = Y.fiber.as) : X = Y := by
  obtain ⟨U, ⟨x⟩⟩ := X
  obtain ⟨V, ⟨y⟩⟩ := Y
  dsimp only at h hf
  subst h
  simp only [eqToHom_refl, Functor.map_id_apply] at hf
  subst hf
  rfl

/-- A morphism of the category attached to a functor to sets lying over an identity of `C` is an
identity: its source and target are equal. -/
theorem ofSetFunctor_eq_of_isHomLift_id {U : C} {X Y : (ofSetFunctor G).obj} (m : X ⟶ Y)
    (hm : (ofSetFunctor G).p.IsHomLift (𝟙 U) m) : X = Y := by
  have := hm
  have hX : X.base = U := IsHomLift.domain_eq (ofSetFunctor G).p (𝟙 U) m
  have hY : Y.base = U := IsHomLift.codomain_eq (ofSetFunctor G).p (𝟙 U) m
  have hbase : m.base = eqToHom (hX.trans hY.symm) := by
    have h := IsHomLift.fac' (ofSetFunctor G).p (𝟙 U) m
    simp only [Category.id_comp, eqToHom_trans] at h
    exact h
  refine ofSetFunctor_obj_ext (hX.trans hY.symm) ?_
  rw [← hbase]
  exact ofSetFunctor_map_fiber m

end Discrete

/-- **Stacks 06GK (11).** The category attached to a functor to sets is cofibered in groupoids. -/
@[stacks 06GK "(11) the category associated to a functor C → Sets is cofibered in groupoids"]
theorem isCofiberedInGroupoids_ofSetFunctor (F : C ⥤ Type w) :
    IsCofiberedInGroupoids (ofSetFunctor F).p :=
  isCofiberedInGroupoids_ofGroupoidFunctor _

/-- **Stacks 06GK (11).** The fibre categories of the category attached to a functor to sets are
discrete, so it is a category cofibered in sets. -/
@[stacks 06GK "(11) the associated category is cofibered in sets: its fibre categories are \
discrete"]
theorem isDiscrete_fiber_ofSetFunctor (F : C ⥤ Type w) (U : C) :
    IsDiscrete ((ofSetFunctor F).p.Fiber U) where
  subsingleton x y := ⟨fun φ ψ ↦ Fiber.hom_ext (ofSetFunctor_hom_ext _ _ (by
    have h₁ := IsHomLift.fac' (ofSetFunctor F).p (𝟙 U) (Fiber.fiberInclusion.map φ)
    have h₂ := IsHomLift.fac' (ofSetFunctor F).p (𝟙 U) (Fiber.fiberInclusion.map ψ)
    exact h₁.trans h₂.symm))⟩
  eq_of_hom {x y} φ := Subtype.ext (ofSetFunctor_eq_of_isHomLift_id _ φ.2)

/-- The morphism of categories cofibered in sets induced by a morphism of functors `α : F ⟶ G`:
it sends `(U, x)` to `(U, α_U(x))`. -/
def ofSetFunctorMap {F G : C ⥤ Type w} (α : F ⟶ G) : ofSetFunctor F ⥤ᵇ ofSetFunctor G where
  toFunctor := Grothendieck.map (whiskerRight α (typeToGrpd ⋙ Grpd.forgetToCat))
  w := Grothendieck.functor_comp_forget

/-- The morphism induced by a morphism of functors sends `(U, x)` to `(U, α_U(x))`. -/
@[simp]
theorem ofSetFunctorMap_obj {F G : C ⥤ Type w} (α : F ⟶ G) (X : (ofSetFunctor F).obj) :
    (ofSetFunctorMap α).obj X = ⟨X.base, ⟨α.app X.base X.fiber.as⟩⟩ :=
  rfl

/-- A functor over `C` into a category over `C` with faithful projection is determined by its
values on objects. -/
theorem basedFunctor_ext_of_faithful {𝒳 𝒴 : BasedCategory C} [𝒴.p.Faithful] {φ ψ : 𝒳 ⥤ᵇ 𝒴}
    (h : ∀ X, φ.obj X = ψ.obj X) : φ = ψ := by
  apply BasedCategory.BasedFunctor.ext'
  refine CategoryTheory.Functor.ext h (fun X Y f ↦ 𝒴.p.map_injective ?_)
  have hφ := Functor.congr_hom φ.w f
  have hψ := Functor.congr_hom ψ.w f
  simp only [Functor.comp_map] at hφ hψ
  rw [hφ, Functor.map_comp, Functor.map_comp, hψ, eqToHom_map, eqToHom_map]
  simp

/-- **Stacks 06GK (11).** The functor from functors `C ⥤ Type` to the `(2, 1)`-category `Cof(C)`
sending `F` to its category cofibered in sets. -/
@[stacks 06GK "(11) the embedding of functors C → Sets into categories cofibered in groupoids"]
def ofSetFunctorFunctor : (C ⥤ Type w) ⥤
    Bicategory.InducedBicategory (BasedCategory.{max v₁ w, max u₁ w} C)
      (Subtype.val (p := IsCofiberedBased (C := C))) where
  obj F := CatCofiberedInGroupoids.mk (ofSetFunctor F) (isCofiberedInGroupoids_ofSetFunctor F)
  map α := Bicategory.InducedBicategory.mkHom (ofSetFunctorMap α)
  map_id _ := Bicategory.InducedBicategory.hom_ext
    (basedFunctor_ext_of_faithful (fun _ ↦ rfl))
  map_comp _ _ := Bicategory.InducedBicategory.hom_ext
    (basedFunctor_ext_of_faithful (fun _ ↦ rfl))

/-- The morphism of functors `F ⟶ G` underlying a morphism of the associated categories
cofibered in sets: `α_U(x)` is the value of the image of `(U, x)`, transported along the
identification of its base with `U`. -/
def natTransOfBasedFunctor {F G : C ⥤ Type w} (φ : ofSetFunctor F ⥤ᵇ ofSetFunctor G) : F ⟶ G where
  app U := ↾fun x ↦ G.map (eqToHom (φ.w_obj ⟨U, ⟨x⟩⟩) : _ ⟶ U) (φ.obj ⟨U, ⟨x⟩⟩).fiber.as
  naturality U V f := by
    ext x
    let A : (ofSetFunctor F).obj := ⟨U, ⟨x⟩⟩
    let B : (ofSetFunctor F).obj := ⟨V, ⟨F.map f x⟩⟩
    let m : A ⟶ B := ⟨f, 𝟙 _⟩
    have hm := Functor.congr_hom φ.w m
    simp only [Functor.comp_map] at hm
    have hbase : (φ.map m).base = eqToHom (φ.w_obj A) ≫ f ≫ eqToHom (φ.w_obj B).symm := hm
    have hfib := ofSetFunctor_map_fiber (φ.map m)
    change G.map (eqToHom (φ.w_obj B)) (φ.obj B).fiber.as =
      G.map f (G.map (eqToHom (φ.w_obj A)) (φ.obj A).fiber.as)
    have hA : (ofSetFunctor G).p.obj (φ.obj A) = U := φ.w_obj A
    have hB : (ofSetFunctor G).p.obj (φ.obj B) = V := φ.w_obj B
    have hcomp : G.map (eqToHom hA ≫ f ≫ eqToHom hB.symm) ≫
        G.map (eqToHom hB) = G.map (eqToHom hA) ≫ G.map f := by
      rw [← G.map_comp, ← G.map_comp]
      simp
    rw [← hfib, hbase]
    exact ConcreteCategory.congr_hom hcomp _

/-- A morphism of the associated categories cofibered in sets is induced by the morphism of
functors it determines. -/
theorem ofSetFunctorMap_natTransOfBasedFunctor {F G : C ⥤ Type w}
    (φ : ofSetFunctor F ⥤ᵇ ofSetFunctor G) : ofSetFunctorMap (natTransOfBasedFunctor φ) = φ := by
  refine basedFunctor_ext_of_faithful (fun X ↦ ?_)
  obtain ⟨U, ⟨x⟩⟩ := X
  exact (ofSetFunctor_obj_ext (φ.w_obj ⟨U, ⟨x⟩⟩) rfl).symm

/-- The morphism of functors determined by the morphism induced by `α` is `α`. -/
theorem natTransOfBasedFunctor_ofSetFunctorMap {F G : C ⥤ Type w} (α : F ⟶ G) :
    natTransOfBasedFunctor (ofSetFunctorMap α) = α := by
  ext U x
  exact Functor.map_id_apply G U (α.app U x)

/-- **Stacks 06GK (11).** The embedding of the category of functors `C ⥤ Type` into the category
of categories cofibered in groupoids over `C` is fully faithful. -/
@[stacks 06GK "(11) the embedding of functors C → Sets into Cof(C) is fully faithful"]
def ofSetFunctorFullyFaithful : (ofSetFunctorFunctor (C := C)).FullyFaithful where
  preimage φ := natTransOfBasedFunctor φ.hom
  map_preimage φ := Bicategory.InducedBicategory.hom_ext
    (ofSetFunctorMap_natTransOfBasedFunctor φ.hom)
  preimage_map α := natTransOfBasedFunctor_ofSetFunctorMap α

/-- **Stacks 06GK (11).** Between two morphisms into a category cofibered in sets there is at
most one 2-morphism. -/
@[stacks 06GK "(11) 2-morphisms into a category cofibered in sets are unique"]
instance subsingleton_twoHom_ofSetFunctor {𝒳 : Bicategory.InducedBicategory
    (BasedCategory.{max v₁ w, max u₁ w} C) (Subtype.val (p := IsCofiberedBased (C := C)))}
    {G : C ⥤ Type w} (φ ψ : 𝒳 ⟶ ofSetFunctorFunctor.obj G) : Subsingleton (φ ⟶ ψ) := by
  refine ⟨fun s t ↦ Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ ?_)⟩
  ext X
  apply ofSetFunctor_hom_ext
  have hs : (ofSetFunctor G).p.IsHomLift (𝟙 (𝒳.val.p.obj X)) (s.hom.toNatTrans.app X) :=
    s.hom.isHomLift' X
  have ht : (ofSetFunctor G).p.IsHomLift (𝟙 (𝒳.val.p.obj X)) (t.hom.toNatTrans.app X) :=
    t.hom.isHomLift' X
  have h₁ := IsHomLift.fac' (ofSetFunctor G).p (𝟙 (𝒳.val.p.obj X)) (s.hom.toNatTrans.app X)
  have h₂ := IsHomLift.fac' (ofSetFunctor G).p (𝟙 (𝒳.val.p.obj X)) (t.hom.toNatTrans.app X)
  exact h₁.trans h₂.symm

/-- **Stacks 06GK (11).** A 2-morphism between two morphisms into a category cofibered in sets
exists only when they are equal; together with `subsingleton_twoHom_ofSetFunctor` the
hom-categories into the image of the embedding are discrete. -/
@[stacks 06GK "(11) 2-morphisms into a category cofibered in sets are identities"]
theorem eq_of_twoHom_ofSetFunctor {𝒳 : Bicategory.InducedBicategory
    (BasedCategory.{max v₁ w, max u₁ w} C) (Subtype.val (p := IsCofiberedBased (C := C)))}
    {G : C ⥤ Type w} {φ ψ : 𝒳 ⟶ ofSetFunctorFunctor.obj G} (t : φ ⟶ ψ) : φ = ψ :=
  letI : (ofSetFunctorFunctor.obj G).val.p.Faithful :=
    inferInstanceAs ((ofSetFunctor G).p.Faithful)
  Bicategory.InducedBicategory.hom_ext (basedFunctor_ext_of_faithful (fun X ↦
    ofSetFunctor_eq_of_isHomLift_id _ (t.hom.isHomLift' X)))

/-! ### (12) Representable functors -/

/-- **Stacks 06GK (12).** For `U : C` the functor `Mor_C(U, -) : C ⥤ Type` (written `U` underlined
in Stacks) is `coyoneda.obj (op U)`, and `U ↦ Mor_C(U, -)` is a fully faithful embedding of `Cᵒᵖ`
into the category of functors `C ⥤ Type`: a morphism `f : U ⟶ V` induces
`coyoneda.map f.op : Mor_C(V, -) ⟶ Mor_C(U, -)`, and every morphism of functors arises so from a
unique `f`. This is Mathlib's `Coyoneda.fullyFaithful`. -/
@[stacks 06GK "(12) U ↦ Mor_C(U, -) is a fully faithful embedding of C^opp into functors \
C → Sets (Mathlib's Coyoneda.fullyFaithful)"]
def underlineFullyFaithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).FullyFaithful :=
  Coyoneda.fullyFaithful

end Deformation
