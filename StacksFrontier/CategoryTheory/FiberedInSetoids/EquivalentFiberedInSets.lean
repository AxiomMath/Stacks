module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidTransport
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidToSets

/-!
# Categories fibred in setoids are exactly those equivalent to categories fibred in sets

Let `𝒞` be a category and let `𝒮` be a category over `𝒞`. This file proves the three clauses of
Stacks 0045.

If `𝒮` is equivalent over `𝒞` to a category `𝒮'` fibred in sets, then `𝒮` is fibred in setoids,
and for every object `U` of `𝒞` the induced map `Ob(𝒮_U) → Ob(𝒮'_U)` identifies its target with
the set `Ob(𝒮_U)/≅` of isomorphism classes of its source. Conversely, a category fibred in
setoids admits such an `𝒮'` together with an equivalence `can : 𝒮 ⥤ 𝒮'` over `𝒞`: one takes for
`𝒮'` the category of elements of the presheaf `U ↦ Ob(𝒮_U)/≅` of isomorphism classes.

## Main definitions

* `CategoryTheory.Functor.IsoClassElements`: the category `𝒮'` of the proof of Stacks 0045 (2) —
  its objects are the pairs `(U, ξ)` with `U` an object of `𝒞` and `ξ` an isomorphism class of
  objects of the fibre `𝒮_U`, and a morphism `(U, ξ) ⟶ (V, ψ)` is a morphism `f : U ⟶ V` of `𝒞`
  restricting `ψ` to `ξ`.
* `CategoryTheory.Functor.isoClassElementsProj`: its projection to `𝒞`.
* `CategoryTheory.Functor.toIsoClassElements`: the functor `can`, sending an object of `𝒮` to its
  base together with its isomorphism class.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.isFiberedInSetoids_of_isFiberedInSets`:
  **Stacks 0045 (1)(a)**.
* `CategoryTheory.BasedCategory.Equivalence.fiberMap_identifiesIsoClasses`:
  **Stacks 0045 (1)(b)**.
* `CategoryTheory.Functor.isFiberedInSets_isoClassElementsProj` and
  `CategoryTheory.Functor.basedEquivalenceIsoClassElements`: **Stacks 0045 (2)**, the two halves of
  the assertion — the category produced is fibred in sets, and `can` is an equivalence over `𝒞`.

## Implementation notes

"Equivalence over `𝒞`" is `CategoryTheory.BasedCategory.Equivalence`, the notion in which the
transports along an equivalence over the base are stated in this library (Stacks 042G, 042W, 042X,
0431). Clause (2) is assembled through
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver`, the notion the representability results
use, and converted with
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence`, so that both clauses
speak of the same kind of equivalence.

Clause (1) is the transport of the two fibre conditions backwards along the equivalence,
`CategoryTheory.BasedCategory.Equivalence.isFiberedInGroupoids` and
`CategoryTheory.BasedCategory.Equivalence.fiber_isThin`, together with the two halves of the
identification of the fibres,
`CategoryTheory.BasedCategory.Equivalence.fiberMap_surjective` and
`CategoryTheory.BasedCategory.Equivalence.fiberMap_eq_iff`; the same content packaged as a
bijection `Ob(𝒮_U)/≅ ≃ Ob(𝒮'_U)` is
`CategoryTheory.BasedCategory.Equivalence.fiberQuotientEquiv`. Only the *target* of the
equivalence is assumed fibred in sets, and nothing is assumed about `𝒮` beyond being a category
over `𝒞`, which is the source's hypothesis.

`CategoryTheory.Functor.IsoClassElements` is the category of elements of
`CategoryTheory.Functor.isoClassPresheaf` written out as a pair of a base object and a class,
with its morphisms a subtype of the morphisms of `𝒞`. The library's other two spellings of a
category of elements cannot be used here: `CategoryTheory.PresheafOfCategories.discreteProjection`
pins the presheaf's values to the morphism universe of `𝒞`, whereas the presheaf of isomorphism
classes takes its values in the universe of the objects of `𝒮`; and
`CategoryTheory.PresheafOfCategories.presheafOfCategories` has no statement identifying its
projection as fibred in sets outside that same pinned universe. With the present spelling the
fibred-in-sets property is the unique-lift condition read off directly — the lift of `f : V ⟶ U`
at `(U, ξ)` is `(V, f^*ξ)` — and `can` commutes with the projections by construction.

The construction is the source's with one difference of bookkeeping. The source describes the
morphisms of `𝒮'` as morphisms `x → y` of `𝒮` between representatives, identified when they
induce the same morphism of `𝒞` and agree after a change of representatives; here a morphism is
its induced morphism of `𝒞` together with the condition that it restricts the class of its target
to the class of its source. The two agree because in a category fibred in setoids a morphism of
`𝒮` is determined by its image in `𝒞` once its endpoints are fixed, and a morphism of `𝒞` with
that restriction property is realised by one of `𝒮`; those are exactly
`CategoryTheory.Functor.hom_unique_of_fiber_isThin` and
`CategoryTheory.Functor.exists_isHomLift_of_isoClassPresheaf_map_eq`, the faithfulness and the
fullness of `can`.

## References

* [Stacks Project, Tag 0045](https://stacks.math.columbia.edu/tag/0045)
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-! ## Clause (1): a category equivalent over `𝒞` to one fibred in sets -/

namespace BasedCategory.Equivalence

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}

/-- **Stacks 0045 (1)(a).** Let `𝒞` be a category and let `𝒳` be a category over `𝒞`. If `𝒳` is
equivalent over `𝒞` to a category `𝒴` fibred in sets over `𝒞`, then `𝒳` is fibred in setoids
over `𝒞`.

Both fibre conditions are transported backwards along the equivalence: a category fibred in sets
is fibred in groupoids with discrete, hence thin, fibres (Stacks 0043), and being fibred in
groupoids and having thin fibres each transport. -/
@[stacks 0045 "(1)(a)", sga "4 I 6.5.1" "more general"]
theorem isFiberedInSetoids_of_isFiberedInSets (e : BasedCategory.Equivalence 𝒳 𝒴)
    (h : 𝒴.p.IsFiberedInSets) : 𝒳.p.IsFiberedInSetoids := by
  have := h
  refine ⟨e.symm.isFiberedInGroupoids (Functor.IsFiberedInSets.isFiberedInGroupoids 𝒴.p), ?_⟩
  refine e.symm.fiber_isThin (fun V a b => ?_)
  exact (Functor.IsFiberedInSets.fiber_isDiscrete 𝒴.p V).subsingleton a b

/-- **Stacks 0045 (1)(b).** Let `𝒞` be a category, let `𝒳` be a category over `𝒞` and let `e` be
an equivalence over `𝒞` from `𝒳` to a category `𝒴` fibred in sets over `𝒞`. For every object `U`
of `𝒞` the induced map `Ob(𝒳_U) → Ob(𝒴_U)` on the objects of the fibres identifies its target
with the set of isomorphism classes of its source: it is surjective, and two objects of `𝒳_U`
have the same image exactly when they are isomorphic in `𝒳_U`.

The same content packaged as a bijection `Ob(𝒳_U)/≅ ≃ Ob(𝒴_U)` is
`CategoryTheory.BasedCategory.Equivalence.fiberQuotientEquiv`; as there, the two categories over
`𝒞` are taken in one pair of universes. -/
@[stacks 0045 "(1)(b)"]
theorem fiberMap_identifiesIsoClasses {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞}
    (e : BasedCategory.Equivalence 𝒳 𝒴)
    (h : 𝒴.p.IsFiberedInSets) (U : 𝒞) :
    Function.Surjective (e.fiberMap (U := U)) ∧
      ∀ x y : 𝒳.p.Fiber U, e.fiberMap x = e.fiberMap y ↔ IsIsomorphic x y := by
  have := h
  have hdisc : ∀ V : 𝒞, IsDiscrete (𝒴.p.Fiber V) := fun V =>
    Functor.IsFiberedInSets.fiber_isDiscrete 𝒴.p V
  have hsetoid : 𝒳.p.IsFiberedInSetoids := e.isFiberedInSetoids_of_isFiberedInSets h
  exact ⟨e.fiberMap_surjective,
    fun x y => e.fiberMap_eq_iff
      (fun V => hsetoid.isFiberedInGroupoids.fiber_isGroupoid V) x y⟩

end BasedCategory.Equivalence

/-! ## Clause (2): the category fibred in sets attached to a category fibred in setoids -/

namespace Functor

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- In a category fibred in groupoids, if `φ : b ⟶ a` lies over `f : V ⟶ U`, then restricting the
class of `a` along `f` gives the class of `b`, since `φ` is a cartesian lift of `f`. -/
private theorem isoClassPresheaf_map_isoClassMk_of_isHomLift {p : 𝒮 ⥤ 𝒞} [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) {U V : 𝒞} (f : V ⟶ U) (a : p.Fiber U) (b : p.Fiber V)
    (φ : b.1 ⟶ a.1) (hφ : p.IsHomLift f φ) :
    p.isoClassPresheaf.map f.op (isoClassMk p a) = isoClassMk p b := by
  have := hp.isStronglyCartesian_homLift f φ
  rw [isoClassPresheaf_map_isoClassMk]
  exact (isoClassMk_eq_pullbackFiber_of_isCartesian f a b φ hφ inferInstance).symm

/-- For a morphism `φ : x ⟶ y` of a category fibred in groupoids, the isomorphism class of `x` in
the fibre over `p x` is the restriction along `p φ` of the isomorphism class of `y` in the fibre
over `p y`. Every morphism of a category fibred in groupoids is strongly cartesian, so `φ` is a
cartesian lift of `p φ` at `y`. -/
theorem isoClassPresheaf_map_isoClassMk_of_hom {p : 𝒮 ⥤ 𝒞} [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) {x y : 𝒮} (φ : x ⟶ y) :
    p.isoClassPresheaf.map (p.map φ).op
        (isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y))) =
      isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x)) := by
  exact isoClassPresheaf_map_isoClassMk_of_isHomLift hp (p.map φ) ⟨y, rfl⟩ ⟨x, rfl⟩ φ
    (IsHomLift.map (p := p) φ)

/-- A morphism of the base is realised by a morphism of a category fibred in setoids as soon as it
is realised on isomorphism classes: if `a` lies over `U`, `b` lies over `V` and restricting the
class of `a` along `f : V ⟶ U` gives the class of `b`, then there is a morphism `b ⟶ a` of `𝒮`
lying over `f`.

A cartesian lift of `f` at `a` has a domain whose class is that restriction, hence the class of
`b`; so that domain is isomorphic to `b` in the fibre over `V`, and composing the isomorphism with
the lift gives the morphism. -/
theorem exists_isHomLift_of_isoClassPresheaf_map_eq {p : 𝒮 ⥤ 𝒞} [hp : p.IsFiberedInSetoids]
    {U V : 𝒞} (f : V ⟶ U) (a : p.Fiber U) (b : p.Fiber V)
    (h : p.isoClassPresheaf.map f.op (isoClassMk p a) = isoClassMk p b) :
    ∃ g : b.1 ⟶ a.1, p.IsHomLift f g := by
  obtain ⟨y, φ, hφ⟩ := hp.isFiberedInGroupoids.exists_lift f a.1 a.2
  have hy : p.obj y = V := IsHomLift.domain_eq p f φ
  have hpb := isoClassPresheaf_map_isoClassMk_of_isHomLift hp.isFiberedInGroupoids f a ⟨y, hy⟩ φ hφ
  obtain ⟨i⟩ := exists_iso_of_isoClassMk_eq (hpb.symm.trans h).symm
  have : p.IsHomLift (𝟙 V) i.hom.1 := i.hom.2
  exact ⟨i.hom.1 ≫ φ, by simpa using IsHomLift.comp (p := p) (f := 𝟙 V) (g := f) i.hom.1 φ⟩

/-- The category `𝒮'` of the proof of **Stacks 0045 (2)**: an object is a pair `(U, ξ)` of an
object `U` of `𝒞` and an isomorphism class `ξ` of objects of the fibre `𝒮_U`.

This is the category of elements of the presheaf
`CategoryTheory.Functor.isoClassPresheaf` of isomorphism classes. -/
structure IsoClassElements (p : 𝒮 ⥤ 𝒞) [p.IsFibered] where
  /-- The object of `𝒞` the pair lies over. -/
  base : 𝒞
  /-- An isomorphism class of objects of the fibre of `p` over `base`. -/
  cls : p.isoClassPresheaf.obj (op base)

namespace IsoClassElements

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered]

/-- A morphism `(U, ξ) ⟶ (V, ψ)` of `CategoryTheory.Functor.IsoClassElements` is a morphism
`f : U ⟶ V` of `𝒞` whose restriction map takes `ψ` to `ξ`. -/
noncomputable instance category : Category (IsoClassElements p) where
  Hom X Y := {f : X.base ⟶ Y.base // p.isoClassPresheaf.map f.op Y.cls = X.cls}
  id X := ⟨𝟙 X.base, by
    rw [op_id, _root_.CategoryTheory.Functor.map_id_apply]⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by
    rw [op_comp, _root_.CategoryTheory.Functor.map_comp_apply, g.property, f.property]⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- Two morphisms of `CategoryTheory.Functor.IsoClassElements` with the same underlying morphism
of `𝒞` are equal. -/
theorem hom_ext {X Y : IsoClassElements p} {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Subtype.ext h

/-- The underlying morphism of `𝒞` of the identity of `X` is the identity of `X.base`. -/
@[simp]
theorem id_val (X : IsoClassElements p) : (𝟙 X : X ⟶ X).val = 𝟙 X.base :=
  rfl

/-- The underlying morphism of `𝒞` of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem comp_val {X Y Z : IsoClassElements p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

end IsoClassElements

/-- The projection of `CategoryTheory.Functor.IsoClassElements` to `𝒞`, sending `(U, ξ)` to `U`
and a morphism to its underlying morphism of `𝒞`. -/
noncomputable def isoClassElementsProj (p : 𝒮 ⥤ 𝒞) [p.IsFibered] :
    IsoClassElements p ⥤ 𝒞 where
  obj X := X.base
  map f := f.val

/-- `CategoryTheory.Functor.isoClassElementsProj` sends `(U, ξ)` to `U`. -/
@[simp]
theorem isoClassElementsProj_obj (p : 𝒮 ⥤ 𝒞) [p.IsFibered] (X : IsoClassElements p) :
    (isoClassElementsProj p).obj X = X.base :=
  rfl

/-- `CategoryTheory.Functor.isoClassElementsProj` sends a morphism to its underlying morphism of
`𝒞`. -/
@[simp]
theorem isoClassElementsProj_map (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {X Y : IsoClassElements p}
    (f : X ⟶ Y) : (isoClassElementsProj p).map f = f.val :=
  rfl

/-- **Stacks 0045 (2)**, the category produced is fibred in sets. The lift of `f : V ⟶ U` at
`(U, ξ)` is `(V, f^*ξ)`, with the restriction map of the presheaf of isomorphism classes as the
morphism, and it is the only one: a lift of `f` with target `(U, ξ)` has its underlying morphism
of `𝒞` forced to be `f`, and then the class at its source is forced to be `f^*ξ`. -/
@[stacks 0045 "(2), the category fibred in sets"]
instance isFiberedInSets_isoClassElementsProj (p : 𝒮 ⥤ 𝒞) [p.IsFibered] :
    (isoClassElementsProj p).IsFiberedInSets where
  existsUnique_lift {U V} f x hx := by
    obtain ⟨xb, xc⟩ := x
    change xb = U at hx
    subst hx
    refine ⟨⟨⟨V, p.isoClassPresheaf.map f.op xc⟩, ⟨f, ?_⟩⟩, ⟨rfl, ?_⟩, ?_⟩
    · rfl
    · change f = 𝟙 V ≫ f ≫ 𝟙 xb
      simp
    rintro ⟨⟨yb, yc⟩, φ⟩ ⟨hy, hmap⟩
    change yb = V at hy
    subst hy
    have hφ : φ.val = f := by
      have hmap' : φ.val = 𝟙 yb ≫ f ≫ 𝟙 xb := hmap
      simpa using hmap'
    have hyc : yc = p.isoClassPresheaf.map f.op xc := by
      rw [← hφ]; exact φ.property.symm
    subst hyc
    exact congrArg
      (fun ψ => (⟨⟨yb, p.isoClassPresheaf.map f.op xc⟩, ψ⟩ :
        Σ z : IsoClassElements p, z ⟶ (⟨xb, xc⟩ : IsoClassElements p)))
      (IsoClassElements.hom_ext hφ)

/-- The functor `can` of **Stacks 0045 (2)**: an object `x` of `𝒮` is sent to the pair of the
object `p x` of `𝒞` and the isomorphism class of `x` in the fibre over `p x`, and a morphism to
its image in `𝒞`. -/
noncomputable def toIsoClassElements (p : 𝒮 ⥤ 𝒞) [hp : p.IsFiberedInSetoids] :
    𝒮 ⥤ IsoClassElements p where
  obj x := ⟨p.obj x, isoClassMk p ⟨x, rfl⟩⟩
  map φ := ⟨p.map φ, isoClassPresheaf_map_isoClassMk_of_hom hp.isFiberedInGroupoids φ⟩
  map_id x := IsoClassElements.hom_ext (p.map_id x)
  map_comp f g := IsoClassElements.hom_ext (p.map_comp f g)

/-- The underlying morphism of `𝒞` of the image of `φ` under
`CategoryTheory.Functor.toIsoClassElements` is `p.map φ`. -/
@[simp]
theorem toIsoClassElements_map (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSetoids] {x y : 𝒮} (φ : x ⟶ y) :
    ((toIsoClassElements p).map φ).val = p.map φ :=
  rfl

/-- `CategoryTheory.Functor.toIsoClassElements` is a functor over `𝒞`. -/
theorem toIsoClassElements_comp (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSetoids] :
    toIsoClassElements p ⋙ isoClassElementsProj p = p :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- `CategoryTheory.Functor.toIsoClassElements` is faithful: two morphisms of `𝒮` with the same
endpoints and the same image in `𝒞` are equal, the fibres being thin. -/
noncomputable instance faithful_toIsoClassElements (p : 𝒮 ⥤ 𝒞) [hp : p.IsFiberedInSetoids] :
    (toIsoClassElements p).Faithful where
  map_injective {x y} φ ψ h := by
    have hb : p.map φ = p.map ψ := congrArg Subtype.val h
    refine hom_unique_of_fiber_isThin p (p.map φ) (hp.fiber_isThin (p.obj x)) φ ψ
      (IsHomLift.map (p := p) φ) ?_
    rw [hb]
    exact IsHomLift.map (p := p) ψ

/-- `CategoryTheory.Functor.toIsoClassElements` is full: a morphism of `𝒞` restricting the class
of `y` to the class of `x` is the image of a morphism `x ⟶ y` of `𝒮`. -/
noncomputable instance full_toIsoClassElements (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSetoids] :
    (toIsoClassElements p).Full where
  map_surjective {x y} ψ := by
    set f : p.obj x ⟶ p.obj y := ψ.val with hf
    have hprop : p.isoClassPresheaf.map f.op
        (isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y))) =
        isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x)) := ψ.property
    obtain ⟨g, hg⟩ := exists_isHomLift_of_isoClassPresheaf_map_eq f
      (⟨y, rfl⟩ : p.Fiber (p.obj y)) (⟨x, rfl⟩ : p.Fiber (p.obj x)) hprop
    have hlift : p.IsHomLift f g := hg
    have hmap : p.map g = f := by
      rw [IsHomLift.fac' p f g]
      simp
    exact ⟨g, IsoClassElements.hom_ext hmap⟩

/-- `CategoryTheory.Functor.toIsoClassElements` is essentially surjective by vertical
isomorphisms: a pair `(U, ξ)` is the image of any representative `r` of `ξ`, up to the
isomorphism given by the equality `p r = U`. -/
theorem exists_vertical_iso_toIsoClassElements (p : 𝒮 ⥤ 𝒞) [hp : p.IsFiberedInSetoids]
    (Y : IsoClassElements p) :
    ∃ (x : 𝒮) (α : (toIsoClassElements p).obj x ≅ Y),
      (isoClassElementsProj p).IsHomLift
        (𝟙 ((isoClassElementsProj p).obj Y)) α.hom := by
  obtain ⟨r, hr⟩ := isoClassMk_surjective (p := p) (U := Y.base) Y.cls
  have hlift : p.IsHomLift (eqToHom r.2) (𝟙 r.1) :=
    IsHomLift.of_fac' p (eqToHom r.2) (𝟙 r.1) rfl r.2 (by simp)
  have hα : p.isoClassPresheaf.map (eqToHom r.2).op Y.cls =
      isoClassMk p (⟨r.1, rfl⟩ : p.Fiber (p.obj r.1)) := by
    rw [← hr]
    exact isoClassPresheaf_map_isoClassMk_of_isHomLift hp.isFiberedInGroupoids (eqToHom r.2) r
      ⟨r.1, rfl⟩ (𝟙 r.1) hlift
  have hround : (eqToHom r.2).op ≫ (eqToHom r.2.symm).op = 𝟙 (op Y.base) := by
    rw [← op_comp, eqToHom_trans, eqToHom_refl, op_id]
  have hβ : p.isoClassPresheaf.map (eqToHom r.2.symm).op
      (isoClassMk p (⟨r.1, rfl⟩ : p.Fiber (p.obj r.1))) = Y.cls := by
    rw [← hα, ← _root_.CategoryTheory.Functor.map_comp_apply, hround,
      _root_.CategoryTheory.Functor.map_id_apply]
  refine ⟨r.1, ⟨⟨eqToHom r.2, hα⟩, ⟨eqToHom r.2.symm, hβ⟩, ?_, ?_⟩, ?_⟩
  · refine IsoClassElements.hom_ext ?_
    change eqToHom r.2 ≫ eqToHom r.2.symm = 𝟙 (p.obj r.1)
    simp
  · refine IsoClassElements.hom_ext ?_
    change eqToHom r.2.symm ≫ eqToHom r.2 = 𝟙 Y.base
    simp
  · refine IsHomLift.of_fac' (isoClassElementsProj p) (𝟙 Y.base) _ r.2 rfl ?_
    change eqToHom r.2 = eqToHom r.2 ≫ 𝟙 Y.base ≫ eqToHom (rfl : Y.base = Y.base)
    simp

/-- `CategoryTheory.Functor.toIsoClassElements` is an equivalence in the 2-category of fibred
categories over `𝒞`: it is fully faithful and essentially surjective by vertical
isomorphisms. -/
theorem isFibredEquivalenceOver_toIsoClassElements (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSetoids] :
    IsFibredEquivalenceOver p (isoClassElementsProj p) (toIsoClassElements p) := by
  have h := isFibredEquivalenceOver_of_fullyFaithful (toIsoClassElements p)
    (exists_vertical_iso_toIsoClassElements p)
  rwa [toIsoClassElements_comp] at h

end Functor

/-- An equivalence in the 2-category of fibred categories over `𝒞`, read as a
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver`. The quasi-inverse and the two 2-cells
are chosen from the existence statement carried by
`CategoryTheory.Functor.IsFibredEquivalenceOver`, and their verticality is turned into the
whiskered form the structure records.

This is `AlgebraicGeometry.equivalenceOver_of_isFibredEquivalenceOver` with the universes of the
base left free; that one is stated for a base whose objects lie one universe above its morphisms,
which the base of a general category fibred in setoids need not. -/
noncomputable def StacksRepresentableCFG.equivalenceOverOfIsFibredEquivalenceOver
    {𝒮 : Type u₂} [Category.{v₂} 𝒮] {𝒯 : Type u₃} [Category.{v₃} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒯}
    (h : Functor.IsFibredEquivalenceOver p q G) :
    StacksRepresentableCFG.EquivalenceOver p q := by
  classical
  let H := Classical.choose h.exists_inverse
  have hpack₁ := Classical.choose_spec h.exists_inverse
  let hH : Functor.IsFibredOneMorphism q p H := Classical.choose hpack₁
  have hpack₂ := Classical.choose_spec hpack₁
  let η := Classical.choose hpack₂
  have hpack₃ := Classical.choose_spec hpack₂
  let hη : ∀ x : 𝒮, p.IsHomLift (𝟙 (p.obj x)) (η.hom.app x) := Classical.choose hpack₃
  have hpack₄ := Classical.choose_spec hpack₃
  let ε := Classical.choose hpack₄
  have hε : ∀ y : 𝒯, q.IsHomLift (𝟙 (q.obj y)) (ε.hom.app y) := Classical.choose_spec hpack₄
  refine ⟨⟨G, h.isFibredOneMorphism.comp_eq⟩, ⟨H, hH.comp_eq⟩, η, ε, ?_, ?_⟩
  · ext x
    simp only [Functor.whiskerRight_app, eqToHom_app]
    have hv : p.IsHomLift (𝟙 (p.obj x)) (η.hom.app x) := hη x
    rw [IsHomLift.fac' p (𝟙 (p.obj x)) (η.hom.app x)]
    simp
  · ext y
    simp only [Functor.whiskerRight_app, eqToHom_app]
    have hv : q.IsHomLift (𝟙 (q.obj y)) (ε.hom.app y) := hε y
    rw [IsHomLift.fac' q (𝟙 (q.obj y)) (ε.hom.app y)]
    simp

namespace Functor

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **Stacks 0045 (2)**, the equivalence. Let `𝒞` be a category and let `p : 𝒮 ⥤ 𝒞` be a category
fibred in setoids. Then `can : 𝒮 ⥤ 𝒮'` is an equivalence over `𝒞` onto the category of elements
of the presheaf of isomorphism classes, which is fibred in sets by
`CategoryTheory.Functor.isFiberedInSets_isoClassElementsProj`. -/
@[stacks 0045 "(2), the equivalence over the base"]
noncomputable def basedEquivalenceIsoClassElements (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSetoids] :
    BasedCategory.Equivalence (BasedCategory.ofFunctor p)
      (BasedCategory.ofFunctor (isoClassElementsProj p)) :=
  _root_.CategoryTheory.StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
    (StacksRepresentableCFG.equivalenceOverOfIsFibredEquivalenceOver
      (isFibredEquivalenceOver_toIsoClassElements p))

end Functor

end CategoryTheory

end
