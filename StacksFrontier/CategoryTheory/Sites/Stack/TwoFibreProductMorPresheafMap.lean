module

public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack

/-!
# Fibre products of sheaves of types and functoriality of `Mor(x, y)`

This file proves the following facts about presheaves of types and about a single fibred
category:

* a fibre product of sheaves of types is a sheaf;
* a presheaf with a closed injective natural map into a sheaf is a sheaf;
* the presheaf `Mor(x, y)` of Stacks 02ZB is contravariantly functorial in `x` and covariantly
  functorial in `y`, for morphisms of the fibre;
* a 1-morphism of fibred categories over the base induces a map of presheaves
  `Mor(x, y) ⟶ Mor(F x, F y)`.

## Main definitions

* `CategoryTheory.Presheaf.eqPullback`, the presheaf of pairs of sections with the same image in a
  third presheaf, i.e. the fibre product of two presheaves of types;
* `CategoryTheory.Functor.morPresheafMap`, the map `Mor(x, y) ⟶ Mor(x', y')` induced by a pair of
  morphisms `x' ⟶ x` and `y ⟶ y'` of the fibre;
* `CategoryTheory.Functor.morPresheafFiberIso`, the isomorphism `Mor(x, y) ≅ Mor(x', y')` induced
  by a pair of isomorphisms of the fibre;
* `CategoryTheory.Functor.fiberFunctorOfCompEq`, the functor on fibres induced by a functor
  strictly over the base;
* `CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`, the comparison between the
  chosen pullback of `F x` and the image under `F` of the chosen pullback of `x`;
* `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`, the induced map
  `Mor(x, y) ⟶ Mor(F x, F y)`.

## Main results

* `CategoryTheory.Presheaf.isSheaf_eqPullback`, a fibre product of sheaves of types is a sheaf;
* `CategoryTheory.Presheaf.isSheaf_of_injective_natural`, a presheaf with a closed injective
  natural map into a sheaf is a sheaf;
* `CategoryTheory.Functor.pullbackFiberMap_pullbackFiberHom`, base change of a morphism of a fibre
  is natural in the object of `𝒞/U`, and
  `CategoryTheory.Functor.IsFibredOneMorphism.pullbackFiberMap_mapPullbackFiberIso_hom`, the same
  naturality for the comparison isomorphism above;
* `CategoryTheory.Functor.IsFibredOneMorphism.morRestrict_mapPullbackFiberIso_conj`, that
  naturality written out on sections, for total categories with independent hom universes.

## Implementation notes

*Universes.* The object universes and the hom universe of the base are independent, and so are the
hom universes of the two total categories `𝒳` and `𝒮`: the comparison
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` and everything proved from it
only compare morphisms of the fibres of one of them at a time. The single exception is
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`, whose source is valued in the hom
universe of `𝒳` and whose target is valued in that of `𝒮`; it is stated in a section that ties the
two together.
-/

@[expose] public section

universe vb

-- The endpoints of the chosen cartesian lifts compared below are spelled through
-- `Functor.pullbackFiber` and `Functor.Fiber.fiberInclusion`, so the instance arguments of
-- `IsHomLift` and `IsCartesian` are only found after unfolding those.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Opposite

/-! ### A fibre product of sheaves of types is a sheaf -/

namespace Presheaf

universe w v' u'

variable {D : Type u'} [Category.{v'} D] {A B C : Dᵒᵖ ⥤ Type w}

/-- The fibre product `A ×_C B` of presheaves of types: its sections over `d` are the pairs of a
section of `A` and a section of `B` with the same image in `C`. -/
@[implicit_reducible]
def eqPullback (u : A ⟶ C) (v : B ⟶ C) : Dᵒᵖ ⥤ Type w where
  obj d := {ab : A.obj d × B.obj d // u.app d ab.1 = v.app d ab.2}
  map {_ d'} h := ↾fun ab ↦ ⟨(A.map h ab.val.fst, B.map h ab.val.snd), by
    dsimp only
    rw [u.naturality_apply h, v.naturality_apply h, ab.2]⟩
  map_id _ := by ext ab <;> simp
  map_comp _ _ := by ext ab <;> simp

/-- Restriction in `CategoryTheory.Presheaf.eqPullback` is componentwise on the `A`-part. -/
@[simp]
lemma eqPullback_map_fst {u : A ⟶ C} {v : B ⟶ C} {d d' : Dᵒᵖ} (h : d ⟶ d')
    (ab : (eqPullback u v).obj d) :
    (((eqPullback u v).map h) ab).val.fst = A.map h ab.val.fst := rfl

/-- Restriction in `CategoryTheory.Presheaf.eqPullback` is componentwise on the `B`-part. -/
@[simp]
lemma eqPullback_map_snd {u : A ⟶ C} {v : B ⟶ C} {d d' : Dᵒᵖ} (h : d ⟶ d')
    (ab : (eqPullback u v).obj d) :
    (((eqPullback u v).map h) ab).val.snd = B.map h ab.val.snd := rfl

/-- A fibre product of sheaves of types is a sheaf. -/
theorem isSheaf_eqPullback (J : GrothendieckTopology D) (u : A ⟶ C) (v : B ⟶ C)
    (hA : IsSheaf J A) (hB : IsSheaf J B) (hC : IsSheaf J C) :
    IsSheaf J (eqPullback u v) := by
  rw [isSheaf_iff_isSheaf_of_type] at hA hB hC ⊢
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨fun t t₁ t₂ h₁ h₂ => ?_, fun t ht => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · refine (hA S hS).isSeparatedFor.ext fun Y f hf => ?_
      rw [← eqPullback_map_fst f.op t₁, ← eqPullback_map_fst f.op t₂, h₁ f hf, h₂ f hf]
    · refine (hB S hS).isSeparatedFor.ext fun Y f hf => ?_
      rw [← eqPullback_map_snd f.op t₁, ← eqPullback_map_snd f.op t₂, h₁ f hf, h₂ f hf]
  · obtain ⟨a, ha, -⟩ := (hA S hS) (fun _ f hf => (t f hf).val.fst)
      fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm => by
        rw [← eqPullback_map_fst g₁.op (t f₁ hf₁), ← eqPullback_map_fst g₂.op (t f₂ hf₂),
          ht g₁ g₂ hf₁ hf₂ hcomm]
    obtain ⟨b, hb, -⟩ := (hB S hS) (fun _ f hf => (t f hf).val.snd)
      fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm => by
        rw [← eqPullback_map_snd g₁.op (t f₁ hf₁), ← eqPullback_map_snd g₂.op (t f₂ hf₂),
          ht g₁ g₂ hf₁ hf₂ hcomm]
    have heq : u.app (op X) a = v.app (op X) b := by
      refine (hC S hS).isSeparatedFor.ext fun Y f hf => ?_
      rw [← u.naturality_apply f.op, ← v.naturality_apply f.op, ha f hf, hb f hf, (t f hf).2]
    refine ⟨⟨(a, b), heq⟩, fun Y f hf => Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact ha f hf
    · exact hb f hf

/-! ### A presheaf embedded in a sheaf with closed image is a sheaf

A presheaf of types carrying an injective natural family of functions into a sheaf inherits the
sheaf property as soon as its image is closed under local membership. The map is a family of
functions rather than a morphism of presheaves so that the two presheaves may be valued in
different type universes. -/

universe w₁ w₂

/-- A presheaf that maps injectively and naturally into a sheaf is itself a sheaf, provided its
image is *closed*: a section of the target that is locally in the image is in the image. -/
theorem isSheaf_of_injective_natural {K : GrothendieckTopology D} {P : Dᵒᵖ ⥤ Type w₁}
    {Q : Dᵒᵖ ⥤ Type w₂} (φ : ∀ X, P.obj X → Q.obj X)
    (hnat : ∀ {X Y : Dᵒᵖ} (f : X ⟶ Y) (s : P.obj X), φ Y (P.map f s) = Q.map f (φ X s))
    (hinj : ∀ X, Function.Injective (φ X)) (hQ : IsSheaf K Q)
    (hclosed : ∀ (X : D) (S : Sieve X), S ∈ K X → ∀ t : Q.obj (Opposite.op X),
      (∀ ⦃Y : D⦄ (f : Y ⟶ X), S f → ∃ s, φ (Opposite.op Y) s = Q.map f.op t) →
      ∃ s, φ (Opposite.op X) s = t) :
    IsSheaf K P := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS fam hcompat
  obtain ⟨t, ht, huniq⟩ := (isSheaf_iff_isSheaf_of_type K Q).1 hQ S hS
    (fun _ f hf ↦ φ _ (fam f hf)) fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm ↦ by
      rw [← hnat, ← hnat]
      exact congrArg _ (hcompat g₁ g₂ h₁ h₂ hcomm)
  obtain ⟨s, hs⟩ := hclosed X S hS t fun _ f hf ↦ ⟨fam f hf, (ht f hf).symm⟩
  refine ⟨s, fun Y f hf ↦ hinj _ ?_, fun s' hs' ↦ hinj _ ?_⟩
  · rw [hnat, hs]; exact ht f hf
  · rw [hs]
    exact huniq (φ _ s') fun Y f hf ↦ by rw [← hnat, hs' f hf]

end Presheaf

namespace Functor

universe v v' u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒮 : Type u₃} [Category.{v'} 𝒮]

/-! ### Base change of a morphism of a fibre, as the object of `𝒞/U` varies

`CategoryTheory.Functor.pullbackFiberHom` base changes a morphism of the fibre over `U` along a
single morphism `V ⟶ U`, and `CategoryTheory.Functor.pullbackFiberMap` restricts the chosen
pullbacks of a single object along a morphism of `𝒞/U`. The two commute. -/

/-- Two morphisms over `h.left`, each a composite with a morphism of a fibre, are equal if they
agree after composing with a strongly cartesian morphism over `g₂.hom`. -/
private lemma eq_of_comp_eq_of_isStronglyCartesian {𝒟 : Type*} [Category 𝒟] (p : 𝒟 ⥤ 𝒞)
    {U : 𝒞} {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) {A B C D E : 𝒟} (u : A ⟶ B) (χ : B ⟶ C)
    (χ' : A ⟶ D) (v : D ⟶ C) (φ : C ⟶ E) [p.IsHomLift h.left u] [p.IsHomLift (𝟙 g₂.left) χ]
    [p.IsHomLift (𝟙 g₁.left) χ'] [p.IsHomLift h.left v] [p.IsStronglyCartesian g₂.hom φ]
    (hφ : (u ≫ χ) ≫ φ = (χ' ≫ v) ≫ φ) : u ≫ χ = χ' ≫ v := by
  have hl : p.IsHomLift h.left (u ≫ χ) := by
    simpa using (inferInstance : p.IsHomLift (h.left ≫ 𝟙 g₂.left) (u ≫ χ))
  have hr : p.IsHomLift h.left (χ' ≫ v) := by
    simpa using (inferInstance : p.IsHomLift (𝟙 g₁.left ≫ h.left) (χ' ≫ v))
  exact IsStronglyCartesian.ext p g₂.hom φ h.left hφ

/-- Base change of a morphism of the fibre over `U` is natural in the object of `𝒞/U`: restricting
the chosen pullbacks along `h : g₁ ⟶ g₂` and then base changing agrees with base changing and then
restricting. -/
@[reassoc]
lemma pullbackFiberMap_pullbackFiberHom (p : 𝒳 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} {x x' : p.Fiber U}
    (α : x ⟶ x') {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map (pullbackFiberHom α g₂.hom) =
      Fiber.fiberInclusion.map (pullbackFiberHom α g₁.hom) ≫ pullbackFiberMap p x' h := by
  refine eq_of_comp_eq_of_isStronglyCartesian p h _ _ _ _
    (IsPreFibered.pullbackMap x'.2 g₂.hom) ?_
  rw [Category.assoc, pullbackFiberHom_fac, ← Category.assoc, pullbackFiberMap_fac,
    Category.assoc, pullbackFiberMap_fac, pullbackFiberHom_fac]

/-! ### Functoriality of `Mor(x, y)` in `x` and `y`

A morphism `x' ⟶ x` of the fibre over `U` and a morphism `y ⟶ y'` induce a map of presheaves
`Mor(x, y) ⟶ Mor(x', y')` by base changing them and composing. For isomorphisms this is an
isomorphism of presheaves. -/

section MorPresheafMap

variable (p : 𝒳 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} {x x' x'' y y' y'' : p.Fiber U}

/-- The map of presheaves `Mor(x, y) ⟶ Mor(x', y')` induced by `e : x' ⟶ x` and `e' : y ⟶ y'`:
over `g` it base changes `e` and `e'` along `g` and composes. -/
noncomputable def morPresheafMap (e : x' ⟶ x) (e' : y ⟶ y') :
    morPresheaf p x y ⟶ morPresheaf p x' y' where
  app g := ↾fun m ↦ pullbackFiberHom e g.unop.hom ≫ m ≫ pullbackFiberHom e' g.unop.hom
  naturality := by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m
    dsimp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, morPresheaf_map_apply,
        Quiver.Hom.unop_op', TypeCat.Fun.coe_mk]
    refine morRestrict_uniq p x' y' h _ _ ?_
    simp only [Functor.map_comp, Category.assoc, pullbackFiberHom_fac, morRestrict_fac_assoc]
    rw [pullbackFiberMap_pullbackFiberHom_assoc]

/-- A section of `Mor(x, y)` over `g` is carried by `CategoryTheory.Functor.morPresheafMap` to its
composite on either side with the base changes of `e` and `e'` along `g`. -/
@[simp]
lemma morPresheafMap_app (e : x' ⟶ x) (e' : y ⟶ y') (g : (Over U)ᵒᵖ)
    (m : (morPresheaf p x y).obj g) :
    (morPresheafMap p e e').app g m =
      pullbackFiberHom e g.unop.hom ≫ m ≫ pullbackFiberHom e' g.unop.hom := rfl

/-- `CategoryTheory.Functor.morPresheafMap` at the pair of identities is the identity. -/
@[simp]
lemma morPresheafMap_id : morPresheafMap p (𝟙 x) (𝟙 y) = 𝟙 (morPresheaf p x y) := by
  ext g m
  dsimp only [TypeCat.Fun.toFun_apply, morPresheafMap_app, NatTrans.id_app, types_id_apply]
  rw [pullbackFiberHom_id, pullbackFiberHom_id, Category.id_comp, Category.comp_id]

/-- `CategoryTheory.Functor.morPresheafMap` is functorial: composing the maps induced by two pairs
of morphisms gives the map induced by the composites, contravariantly in the source. -/
lemma morPresheafMap_comp (e₁ : x' ⟶ x) (e₁' : y ⟶ y') (e₂ : x'' ⟶ x') (e₂' : y' ⟶ y'') :
    morPresheafMap p e₁ e₁' ≫ morPresheafMap p e₂ e₂' =
      morPresheafMap p (e₂ ≫ e₁) (e₁' ≫ e₂') := by
  ext g m
  dsimp only [NatTrans.comp_app, TypeCat.Fun.toFun_apply, types_comp_apply, morPresheafMap_app]
  rw [pullbackFiberHom_comp, pullbackFiberHom_comp]
  simp [Category.assoc]

/-- The isomorphism of presheaves `Mor(x, y) ≅ Mor(x', y')` induced by isomorphisms `e : x ≅ x'`
and `e' : y ≅ y'` of the fibre. -/
@[simps]
noncomputable def morPresheafFiberIso (e : x ≅ x') (e' : y ≅ y') :
    morPresheaf p x y ≅ morPresheaf p x' y' where
  hom := morPresheafMap p e.inv e'.hom
  inv := morPresheafMap p e.hom e'.inv
  hom_inv_id := by rw [morPresheafMap_comp, e.hom_inv_id, e'.hom_inv_id, morPresheafMap_id]
  inv_hom_id := by rw [morPresheafMap_comp, e.inv_hom_id, e'.inv_hom_id, morPresheafMap_id]

end MorPresheafMap

/-! ### The fibre functor of a functor over the base, and `Mor(x, y)` along it -/

/-- A functor `F : 𝒳 ⥤ 𝒮` strictly over `𝒞` induces a functor on the fibres over each object of
`𝒞`. -/
@[implicit_reducible]
def fiberFunctorOfCompEq {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} (hF : F ⋙ r = p) (U : 𝒞) :
    p.Fiber U ⥤ r.Fiber U where
  obj a := ⟨F.obj a.1, by rw [← Functor.comp_obj, hF]; exact a.2⟩
  map φ := ⟨F.map (Fiber.fiberInclusion.map φ), isHomLift_map_of_comp_eq hF (𝟙 U) _⟩
  map_id _ := Fiber.hom_ext (F.map_id _)
  map_comp _ _ := Fiber.hom_ext (F.map_comp _ _)

/-- `CategoryTheory.Functor.fiberFunctorOfCompEq` acts on objects by applying `F` to the underlying
object of `𝒳`. -/
@[simp]
lemma fiberFunctorOfCompEq_obj_val {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮}
    (hF : F ⋙ r = p) (U : 𝒞) (a : p.Fiber U) :
    ((fiberFunctorOfCompEq hF U).obj a).1 = F.obj a.1 := rfl

/-- `CategoryTheory.Functor.fiberFunctorOfCompEq` acts on morphisms by applying `F` to the
underlying morphism of `𝒳`. -/
@[simp]
lemma fiberInclusion_map_fiberFunctorOfCompEq_map {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮}
    (hF : F ⋙ r = p) {U : 𝒞} {a b : p.Fiber U} (φ : a ⟶ b) :
    Fiber.fiberInclusion.map ((fiberFunctorOfCompEq hF U).map φ) =
      F.map (Fiber.fiberInclusion.map φ) := rfl

namespace IsFibredOneMorphism

variable {p : 𝒳 ⥤ 𝒞} {r : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} [p.IsFibered] [r.IsFibered]

omit [r.IsFibered] in
/-- The image under `F` of the chosen cartesian lift of `f` at `x` is a cartesian lift of `f` at
`F x`. -/
lemma isCartesian_map_pullbackMap (hF : IsFibredOneMorphism p r F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) : r.IsCartesian f (F.map (IsPreFibered.pullbackMap a.2 f)) :=
  have := hF.map_isStronglyCartesian f (IsPreFibered.pullbackMap a.2 f) inferInstance
  inferInstance

/-- The comparison isomorphism, in the fibre of `r` over `V`, between the chosen pullback of `F x`
along `f` and the image under `F` of the chosen pullback of `x` along `f`. -/
noncomputable def mapPullbackFiberIso (hF : IsFibredOneMorphism p r F) {U : 𝒞} (a : p.Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    pullbackFiber r ((fiberFunctorOfCompEq hF.comp_eq U).obj a) f ≅
      (fiberFunctorOfCompEq hF.comp_eq V).obj (pullbackFiber p a f) :=
  fiberIsoOfCartesian f
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj a).2 f)
    (F.map (IsPreFibered.pullbackMap a.2 f)) inferInstance (hF.isCartesian_map_pullbackMap a f)

/-- The forward direction of `IsFibredOneMorphism.mapPullbackFiberIso` composed with the image
under `F` of the chosen cartesian lift of `f` at `x` is the chosen cartesian lift of `f`
at `F x`. -/
@[reassoc (attr := simp)]
lemma mapPullbackFiberIso_hom_fac (hF : IsFibredOneMorphism p r F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    Fiber.fiberInclusion.map (hF.mapPullbackFiberIso a f).hom ≫
        F.map (IsPreFibered.pullbackMap a.2 f) =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj a).2 f :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse direction of `IsFibredOneMorphism.mapPullbackFiberIso` composed with the chosen
cartesian lift of `f` at `F x` is the image under `F` of the chosen cartesian lift of `f`
at `x`. -/
@[reassoc (attr := simp)]
lemma mapPullbackFiberIso_inv_fac (hF : IsFibredOneMorphism p r F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    Fiber.fiberInclusion.map (hF.mapPullbackFiberIso a f).inv ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj a).2 f =
      F.map (IsPreFibered.pullbackMap a.2 f) :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- `IsFibredOneMorphism.mapPullbackFiberIso` is natural in the object of `𝒞/U`: it turns the
restriction map of the chosen pullbacks of `F x` into the image under `F` of the restriction map of
the chosen pullbacks of `x`. -/
@[reassoc]
lemma pullbackFiberMap_mapPullbackFiberIso_hom (hF : IsFibredOneMorphism p r F) {U : 𝒞}
    (a : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    pullbackFiberMap r ((fiberFunctorOfCompEq hF.comp_eq U).obj a) h ≫
        Fiber.fiberInclusion.map (hF.mapPullbackFiberIso a g₂.hom).hom =
      Fiber.fiberInclusion.map (hF.mapPullbackFiberIso a g₁.hom).hom ≫
        F.map (pullbackFiberMap p a h) := by
  have hscart : r.IsStronglyCartesian g₂.hom (F.map (IsPreFibered.pullbackMap a.2 g₂.hom)) :=
    hF.map_isStronglyCartesian g₂.hom _ inferInstance
  have hFm : r.IsHomLift h.left (F.map (pullbackFiberMap p a h)) :=
    hF.map_isHomLift h.left (pullbackFiberMap p a h)
  refine eq_of_comp_eq_of_isStronglyCartesian r h _ _ _ _
    (F.map (IsPreFibered.pullbackMap a.2 g₂.hom)) ?_
  rw [Category.assoc, mapPullbackFiberIso_hom_fac, pullbackFiberMap_fac, Category.assoc,
    ← Functor.map_comp, pullbackFiberMap_fac, mapPullbackFiberIso_hom_fac]

/-- The conjugate of a section of `Mor(x, y)` by the comparison isomorphisms is natural in the
object of `𝒞/U`: restricting along `h : g₁ ⟶ g₂` the conjugate of a section `m` over `g₂` is the
conjugate of the restriction of `m`. -/
lemma morRestrict_mapPullbackFiberIso_conj (hF : IsFibredOneMorphism p r F) {U : 𝒞}
    (a b : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : pullbackFiber p a g₂.hom ⟶ pullbackFiber p b g₂.hom) :
    (hF.mapPullbackFiberIso a g₁.hom).hom ≫
        (fiberFunctorOfCompEq hF.comp_eq g₁.left).map (morRestrict p a b h m) ≫
        (hF.mapPullbackFiberIso b g₁.hom).inv =
      morRestrict r ((fiberFunctorOfCompEq hF.comp_eq U).obj a)
        ((fiberFunctorOfCompEq hF.comp_eq U).obj b) h
        ((hF.mapPullbackFiberIso a g₂.hom).hom ≫
          (fiberFunctorOfCompEq hF.comp_eq g₂.left).map m ≫
          (hF.mapPullbackFiberIso b g₂.hom).inv) := by
  refine morRestrict_uniq r _ _ h _ _ ?_
  simp only [Functor.map_comp, Category.assoc, mapPullbackFiberIso_inv_fac,
    fiberInclusion_map_fiberFunctorOfCompEq_map]
  rw [← Functor.map_comp, morRestrict_fac, Functor.map_comp, Functor.map_comp,
    ← pullbackFiberMap_mapPullbackFiberIso_hom_assoc hF a h]

section SharedHomUniverse

variable {𝒮₀ : Type u₃} [Category.{v} 𝒮₀] {r₀ : 𝒮₀ ⥤ 𝒞} {F₀ : 𝒳 ⥤ 𝒮₀} [r₀.IsFibered]

/-- The map of presheaves `Mor(x, y) ⟶ Mor(F x, F y)` induced by a 1-morphism of fibred categories
over `𝒞`: over `g` it applies `F` to a section and conjugates by the comparison isomorphisms
`IsFibredOneMorphism.mapPullbackFiberIso`. -/
@[stacks 042V]
noncomputable def morPresheafMap (hF : IsFibredOneMorphism p r₀ F₀) {U : 𝒞} (a b : p.Fiber U) :
    morPresheaf p a b ⟶ morPresheaf r₀ ((fiberFunctorOfCompEq hF.comp_eq U).obj a)
      ((fiberFunctorOfCompEq hF.comp_eq U).obj b) where
  app g := ↾fun m ↦ (hF.mapPullbackFiberIso a g.unop.hom).hom ≫
    (fiberFunctorOfCompEq hF.comp_eq g.unop.left).map m ≫
    (hF.mapPullbackFiberIso b g.unop.hom).inv
  naturality := by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m
    dsimp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, morPresheaf_map_apply,
        Quiver.Hom.unop_op', TypeCat.Fun.coe_mk]
    exact hF.morRestrict_mapPullbackFiberIso_conj a b h m

/-- A section of `Mor(x, y)` over `g` is carried by `IsFibredOneMorphism.morPresheafMap` to its
image under `F`, conjugated by the comparison isomorphisms
`IsFibredOneMorphism.mapPullbackFiberIso`. -/
@[simp]
lemma morPresheafMap_app (hF : IsFibredOneMorphism p r₀ F₀) {U : 𝒞} (a b : p.Fiber U)
    (g : (Over U)ᵒᵖ) (m : (morPresheaf p a b).obj g) :
    (hF.morPresheafMap a b).app g m = (hF.mapPullbackFiberIso a g.unop.hom).hom ≫
      (fiberFunctorOfCompEq hF.comp_eq g.unop.left).map m ≫
      (hF.mapPullbackFiberIso b g.unop.hom).inv := rfl

end SharedHomUniverse

end IsFibredOneMorphism

end Functor

end CategoryTheory
