module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Based functors into a category of objects over a fixed target

Let `𝒳` be a category over `𝒞`, with structure functor `p : 𝒳 ⥤ 𝒞`, let `L : 𝒞 ⥤ 𝒟` be a functor
and `D` an object of `𝒟`. The costructured-arrow category `CostructuredArrow (p ⋙ L) D` consists
of the objects `x` of `𝒳` together with a morphism `L(p(x)) ⟶ D`, and it lies over the category
`CostructuredArrow L D` of objects of `𝒞` with a morphism to `D` through
`CostructuredArrow.pre p L D`. It is the base change of `𝒳` from `𝒞` to `CostructuredArrow L D`,
`CategoryTheory.CostructuredArrow.baseChangeBased`.

This file proves the corresponding universal property: for any category `𝒴` over
`CostructuredArrow L D`, the category of functors over `CostructuredArrow L D` from `𝒴` to
`CostructuredArrow (p ⋙ L) D` is equivalent to the category of functors over `𝒞` from `𝒴`, read
over `𝒞` by forgetting the morphisms to `D`, to `𝒳`. A functor of the first kind is turned into
one of the second kind by forgetting the morphism to `D`; conversely, the morphism to `D` of the
image of an object of `𝒴` is forced to be the one carried by the image of that object in
`CostructuredArrow L D`.

The case of interest is that of a base algebraic space `B` and the stack `B-Curves` of families of
curves over schemes over `B`: morphisms over `(Sch/B)` into `B-Curves` are the same as morphisms
into the stack of curves.

## Main definitions

* `CategoryTheory.CostructuredArrow.baseChangeBased`: the base change of a category over `𝒞` to
  `CostructuredArrow L D`, and `CategoryTheory.CostructuredArrow.forgetTargetBased` a category
  over `CostructuredArrow L D` read over `𝒞`.
* `CategoryTheory.CostructuredArrow.basedFunctorForgetTarget`: forgetting the morphism to `D`.
* `CategoryTheory.CostructuredArrow.basedFunctorAddTarget`: adding back the morphism to `D`.
* `CategoryTheory.CostructuredArrow.basedFunctorEquivalence`: the two are quasi-inverse
  equivalences of categories.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CostructuredArrow

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  (𝒳 : BasedCategory.{v₃, u₃} 𝒞) (L : 𝒞 ⥤ 𝒟) (D : 𝒟)
  (𝒴 : BasedCategory.{v₄, u₄} (CostructuredArrow L D))

/-- The base change of a category `𝒳` over `𝒞` to the category `CostructuredArrow L D` of objects
of `𝒞` with a morphism to `D`: the category of objects of `𝒳` with a morphism from the image of
their base to `D`. -/
abbrev baseChangeBased : BasedCategory (CostructuredArrow L D) where
  obj := CostructuredArrow (𝒳.p ⋙ L) D
  p := CostructuredArrow.pre 𝒳.p L D

/-- A category over `CostructuredArrow L D`, read over `𝒞` by forgetting the morphisms to `D`. -/
abbrev forgetTargetBased : BasedCategory 𝒞 where
  obj := 𝒴.obj
  p := 𝒴.p ⋙ CostructuredArrow.proj L D

/-- An object `L.map (eqToHom e) ≫ h` of a costructured-arrow category is the object `h`. -/
theorem mk_map_eqToHom_comp {a b : 𝒞} (e : a = b) (h : L.obj b ⟶ D) :
    CostructuredArrow.mk (L.map (eqToHom e) ≫ h) = CostructuredArrow.mk h := by
  subst e
  simp

/-- The structure morphism of an object of a costructured-arrow category, read through an
equality of objects. -/
theorem hom_eq_of_eq {c c' : CostructuredArrow L D} (e : c = c') :
    c.hom = L.map (eqToHom (congrArg Comma.left e)) ≫ c'.hom := by
  subst e
  simp

/-- The image of an arrow lying over `f` along `q` lies, for the composite `q ⋙ r`, over the
image of `f` along `r`. -/
theorem isHomLift_comp {ℰ : Type*} [Category ℰ] {ℱ : Type*} [Category ℱ] {𝒢 : Type*}
    [Category 𝒢] (q : ℰ ⥤ ℱ) (r : ℱ ⥤ 𝒢) {R S : ℱ} {a b : ℰ} (f : R ⟶ S) (φ : a ⟶ b)
    [q.IsHomLift f φ] : (q ⋙ r).IsHomLift (r.map f) φ := by
  have hdom := IsHomLift.domain_eq q f φ
  have hcod := IsHomLift.codomain_eq q f φ
  subst hdom hcod
  have hf : f = q.map φ := IsHomLift.eq_of_isHomLift q f φ
  subst hf
  exact IsHomLift.map (q ⋙ r) φ

/-- An arrow lying over `f` for a composite `q ⋙ r` has its image along `q` lying over `f` for
`r`. -/
theorem isHomLift_map_of_comp {ℰ : Type*} [Category ℰ] {ℱ : Type*} [Category ℱ] {𝒢 : Type*}
    [Category 𝒢] (q : ℰ ⥤ ℱ) (r : ℱ ⥤ 𝒢) {R S : 𝒢} {a b : ℰ} (f : R ⟶ S) (φ : a ⟶ b)
    (h : (q ⋙ r).IsHomLift f φ) : r.IsHomLift f (q.map φ) :=
  IsHomLift.of_fac' r f (q.map φ) (IsHomLift.domain_eq (q ⋙ r) f φ)
    (IsHomLift.codomain_eq (q ⋙ r) f φ) (IsHomLift.fac' (q ⋙ r) f φ)

/-- **Forgetting the morphism to `D`.** A functor over `CostructuredArrow L D` from `𝒴` to the base
change of `𝒳` gives, after forgetting the morphisms to `D`, a functor over `𝒞` from `𝒴` to
`𝒳`. -/
@[simps]
def basedFunctorForgetTarget :
    (𝒴 ⥤ᵇ baseChangeBased 𝒳 L D) ⥤ (forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳) where
  obj G :=
    { toFunctor := G.toFunctor ⋙ CostructuredArrow.proj (𝒳.p ⋙ L) D
      w := congrArg (· ⋙ CostructuredArrow.proj L D) G.w }
  map {G H} α :=
    { toNatTrans := Functor.whiskerRight α.toNatTrans (CostructuredArrow.proj (𝒳.p ⋙ L) D)
      isHomLift' := fun a => by
        have : (CostructuredArrow.pre 𝒳.p L D).IsHomLift (𝟙 (𝒴.p.obj a)) (α.app a) :=
          α.isHomLift' a
        have h := isHomLift_comp (CostructuredArrow.pre 𝒳.p L D) (CostructuredArrow.proj L D)
          (𝟙 (𝒴.p.obj a)) (α.app a)
        rw [Functor.map_id] at h
        exact isHomLift_map_of_comp (CostructuredArrow.proj (𝒳.p ⋙ L) D) 𝒳.p _ _ h }

variable {𝒳 L D 𝒴}

/-- An arrow of the base change of `𝒳` whose underlying arrow of `𝒳` lies over an identity lies
over the corresponding identity of `CostructuredArrow L D`. -/
theorem isHomLift_pre_of_left {X Y : CostructuredArrow (𝒳.p ⋙ L) D} {c : CostructuredArrow L D}
    (m : X ⟶ Y) (hX : (CostructuredArrow.pre 𝒳.p L D).obj X = c)
    (hY : (CostructuredArrow.pre 𝒳.p L D).obj Y = c) (h : 𝒳.p.IsHomLift (𝟙 c.left) m.left) :
    (CostructuredArrow.pre 𝒳.p L D).IsHomLift (𝟙 c) m := by
  subst hX
  refine IsHomLift.of_fac _ _ _ rfl hY ?_
  apply CostructuredArrow.hom_ext
  simp only [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
  exact IsHomLift.fac 𝒳.p _ m.left

/-- The morphism to `D` attached to the image of an object of `𝒴` under a functor over `𝒞`: the
morphism to `D` of its image in `CostructuredArrow L D`. -/
def addTargetHom (F : forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳) (y : 𝒴.obj) :
    (𝒳.p ⋙ L).obj (F.obj y) ⟶ D :=
  L.map (eqToHom (F.w_obj y)) ≫ (𝒴.p.obj y).hom

/-- The image of a morphism of `𝒴` under a functor over `𝒞`, read in `𝒞`. -/
theorem map_eq_of_forgetTarget (F : forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳) {y y' : 𝒴.obj}
    (φ : y ⟶ y') :
    𝒳.p.map (F.map φ) = eqToHom (F.w_obj y) ≫ (𝒴.p.map φ).left ≫ eqToHom (F.w_obj y').symm :=
  Functor.congr_hom F.w φ

/-- The morphism to `D` attached to the images of objects of `𝒴` is natural. -/
theorem map_addTargetHom (F : forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳) {y y' : 𝒴.obj} (φ : y ⟶ y') :
    (𝒳.p ⋙ L).map (F.map φ) ≫ addTargetHom F y' = addTargetHom F y := by
  rw [Functor.comp_map, map_eq_of_forgetTarget F φ, addTargetHom, addTargetHom]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [CostructuredArrow.w (𝒴.p.map φ)]

/-- An arrow of `𝒳` lying over an identity of `𝒞` intertwines the morphisms to `D` attached to
the images of an object of `𝒴` under two functors over `𝒞`. -/
theorem map_app_addTargetHom {F G : forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳} (β : F ⟶ G) (y : 𝒴.obj) :
    (𝒳.p ⋙ L).map (β.app y) ≫ addTargetHom G y = addTargetHom F y := by
  have : 𝒳.p.IsHomLift (𝟙 ((𝒴.p ⋙ CostructuredArrow.proj L D).obj y)) (β.app y) :=
    β.isHomLift' y
  have hβ := IsHomLift.fac' 𝒳.p (𝟙 ((𝒴.p ⋙ CostructuredArrow.proj L D).obj y)) (β.app y)
  rw [Functor.comp_map, hβ, addTargetHom, addTargetHom]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, Category.id_comp, eqToHom_trans_assoc]

/-- The underlying functor of the lift of a functor over `𝒞` to a functor over
`CostructuredArrow L D`. -/
@[simps]
def addTargetFunctor (F : forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳) :
    𝒴.obj ⥤ CostructuredArrow (𝒳.p ⋙ L) D where
  obj y := CostructuredArrow.mk (addTargetHom F y)
  map φ := CostructuredArrow.homMk (F.map φ) (map_addTargetHom F φ)
  map_id y := by
    apply CostructuredArrow.hom_ext
    simp
  map_comp φ ψ := by
    apply CostructuredArrow.hom_ext
    simp

/-- The lift of a functor over `𝒞` lies over `CostructuredArrow L D`. -/
theorem addTargetFunctor_comp_pre (F : forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳) :
    addTargetFunctor F ⋙ CostructuredArrow.pre 𝒳.p L D = 𝒴.p := by
  refine Functor.ext (fun y => ?_) (fun y y' φ => ?_)
  · change CostructuredArrow.mk (L.map (eqToHom (F.w_obj y)) ≫ (𝒴.p.obj y).hom) = _
    rw [mk_map_eqToHom_comp]
    exact (CostructuredArrow.eq_mk _).symm
  · apply CostructuredArrow.hom_ext
    simp only [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    exact map_eq_of_forgetTarget F φ

/-- The underlying natural transformation of the lift of a morphism of functors over `𝒞`. -/
@[simps]
def addTargetNatTrans {F G : forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳} (β : F ⟶ G) :
    addTargetFunctor F ⟶ addTargetFunctor G where
  app y := CostructuredArrow.homMk (β.app y) (map_app_addTargetHom β y)
  naturality _ _ φ := CostructuredArrow.hom_ext _ _ (β.naturality φ)

variable (𝒳 L D 𝒴)

/-- **Adding back the morphism to `D`.** A functor over `𝒞` from `𝒴`, read over `𝒞`, to `𝒳`
lifts to a functor over `CostructuredArrow L D` from `𝒴` to the base change of `𝒳`: the morphism
to `D` of the image of an object of `𝒴` is the one of its image in `CostructuredArrow L D`. -/
def basedFunctorAddTarget :
    (forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳) ⥤ (𝒴 ⥤ᵇ baseChangeBased 𝒳 L D) where
  obj F :=
    { toFunctor := addTargetFunctor F
      w := addTargetFunctor_comp_pre F }
  map {F G} β :=
    { toNatTrans := addTargetNatTrans β
      isHomLift' := fun y =>
        isHomLift_pre_of_left _ (Functor.congr_obj (addTargetFunctor_comp_pre F) y)
          (Functor.congr_obj (addTargetFunctor_comp_pre G) y) (β.isHomLift' y) }
  map_id F := by
    apply BasedNatTrans.ext
    ext y
    rfl
  map_comp β γ := by
    apply BasedNatTrans.ext
    ext y
    rfl

/-- The comparison of a functor over `CostructuredArrow L D` with the lift of its underlying
functor over `𝒞`: the two agree after forgetting the morphisms to `D`, and the morphisms to `D`
agree because both are read off the image in `CostructuredArrow L D`. -/
def basedFunctorAddTargetForgetIso (G : 𝒴 ⥤ᵇ baseChangeBased 𝒳 L D) :
    G ≅ (basedFunctorAddTarget 𝒳 L D 𝒴).obj ((basedFunctorForgetTarget 𝒳 L D 𝒴).obj G) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun y => CostructuredArrow.isoMk (Iso.refl (G.obj y).left) (by
        change L.map (𝒳.p.map (𝟙 _)) ≫ L.map (eqToHom _) ≫ (𝒴.p.obj y).hom = (G.obj y).hom
        rw [Functor.map_id, Functor.map_id, Category.id_comp]
        exact (hom_eq_of_eq L D (Functor.congr_obj G.w y)).symm))
      (fun φ => by
        apply CostructuredArrow.hom_ext
        change (G.map φ).left ≫ 𝟙 _ = 𝟙 _ ≫ (G.map φ).left
        rw [Category.comp_id, Category.id_comp]))
    (fun y => isHomLift_pre_of_left _ (Functor.congr_obj G.w y)
        (Functor.congr_obj (addTargetFunctor_comp_pre _) y)
        (IsHomLift.id (congrArg Comma.left (Functor.congr_obj G.w y))))

/-- **Based functors into the base change of `𝒳` to `CostructuredArrow L D`.** For a category `𝒴`
over `CostructuredArrow L D`, functors over `CostructuredArrow L D` from `𝒴` to the base change of
`𝒳` are equivalent, by forgetting the morphisms to `D`, to functors over `𝒞` from `𝒴`, read over
`𝒞`, to `𝒳`. -/
def basedFunctorEquivalence :
    (𝒴 ⥤ᵇ baseChangeBased 𝒳 L D) ≌ (forgetTargetBased L D 𝒴 ⥤ᵇ 𝒳) :=
  Equivalence.mk (basedFunctorForgetTarget 𝒳 L D 𝒴) (basedFunctorAddTarget 𝒳 L D 𝒴)
    (NatIso.ofComponents (basedFunctorAddTargetForgetIso 𝒳 L D 𝒴) (fun {G H} α => by
      apply BasedNatTrans.ext
      ext y
      have hc : ∀ {F₁ F₂ F₃ : 𝒴 ⥤ᵇ baseChangeBased 𝒳 L D} (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃),
          (a ≫ b).app y = a.app y ≫ b.app y := fun _ _ => rfl
      rw [hc, hc, CostructuredArrow.comp_left, CostructuredArrow.comp_left]
      change (α.app y).left ≫ 𝟙 _ = 𝟙 _ ≫ (α.app y).left
      rw [Category.comp_id, Category.id_comp]))
    (NatIso.ofComponents (fun F => Iso.refl _) (fun β => by
      apply BasedNatTrans.ext
      ext y
      change β.app y ≫ 𝟙 _ = 𝟙 _ ≫ β.app y
      rw [Category.comp_id, Category.id_comp]))

end CostructuredArrow

end CategoryTheory

end
