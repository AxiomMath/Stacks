module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Center

/-!
# The shift-compatible centre of a category with a shift

The centre `CatCenter C = End (𝟭 C)` of a category carries no information about a shift, and
for a category such as a derived category it is too big to be the right invariant: over a
field `k`, every object of `D(k)` splits as a direct sum of shifts of `k`-vector spaces, so
`CatCenter (D(k))` is the product over `n : ℤ` of copies of `k` rather than `k` itself. The
subring cut out by compatibility with the shift is the invariant that matches the centre of a
ring; this file introduces it, transports it along an equivalence, and constructs the canonical
map to it from the centre of a ring.

An element `z : CatCenter C` is *shift-compatible* for a shift by an additive monoid `A` when
`(z.app X)⟦a⟧' = z.app (X⟦a⟧)` for every `a : A` and every object `X`. For the identity functor
this is exactly Mathlib's `CategoryTheory.NatTrans.CommShift z A`, which is the form used here;
`CategoryTheory.CatCenter.commShift_iff_app` identifies the two.

## Main definitions

* `CategoryTheory.CatCenter.shiftSubalgebra`: the shift-compatible elements of `CatCenter C`, as
  an `R`-subalgebra of `CatCenter C`.
* `CategoryTheory.CatCenter.transportShiftAlgEquiv`: a shift-commuting `R`-linear additive
  equivalence `C ≌ D` induces an isomorphism of the shift-compatible centres.
* `CategoryTheory.CatCenter.homologicalComplexAlgHom`: the degreewise action of the centre of
  `C` on homological complexes.
* `CategoryTheory.CatCenter.localizationAlgHom`: `CatCenter.localizationRingHom` as a morphism
  of `R`-algebras.
* `ModuleCat.centerToShiftCenterDerived`: the canonical map from the centre of a ring `A` to
  the shift-compatible centre of the derived category of `A`-modules.

## Main results

* `CategoryTheory.CatCenter.shift_app_image_iff`: for a shift-commuting functor `F`, an element
  of `CatCenter D` whose components along `F` come from `z : CatCenter C` is shift-compatible at
  `F.obj X` exactly when `F` identifies `(z.app X)⟦a⟧'` with `z.app (X⟦a⟧)`; this single
  computation drives both the transport and the localization statements.
* `CategoryTheory.CatCenter.commShift_transport_iff`: conjugation by an equivalence preserves
  and reflects shift-compatibility.
* `ModuleCat.centerToShiftCenterDerived_injective`: the canonical map is injective, because the
  single-complex functor into the derived category is fully faithful.

## Implementation notes

Shift-compatibility is checked on the image of a functor which is essentially surjective on
objects (`CategoryTheory.CatCenter.commShift_of_essSurj`); both the functor of an equivalence
and the localization functor `DerivedCategory.Q` are of that kind, so no separate argument for
localizations is needed.

Surjectivity of `ModuleCat.centerToShiftCenterDerived` is *not* proved: it is Rickard,
*Derived equivalences as derived functors*, Proposition 9.2 (equivalently König–Zimmermann,
Proposition 6.3.2), an external result. `StacksFrontier/CategoryTheory/Center/Devissage.lean`
reduces it to an extension principle for the complexes concentrated in a single degree —
`ModuleCat.app_single_derivedCenterValue` shows a shift-compatible central element of the derived
category agrees with the degreewise action of a central element of `A` at every module in every
degree — and explains why the remaining step cannot be supplied by a dévissage along the shifts
of the regular module.

## References

* [Stacks Project, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD), whose comparison of
  the centre of a ring with the centre of its derived category this file prepares.
* J. Rickard, *Derived equivalences as derived functors*, Proposition 9.2.
* S. König and A. Zimmermann, *Derived equivalences for group rings*, Proposition 6.3.2.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

universe t w v₁ v₂ u₁ u₂

namespace CatCenter

section Basic

variable {C : Type u₁} [Category.{v₁} C] {A : Type w} [AddMonoid A] [HasShift C A]

/-- Compatibility of a central element with the shift, in the sense of
`CategoryTheory.NatTrans.CommShift`, says that applying it to a shifted object is the shift of
applying it. -/
lemma commShift_iff_app (z : CatCenter C) :
    NatTrans.CommShift z A ↔ ∀ (a : A) (X : C), (z.app X)⟦a⟧' = z.app (X⟦a⟧) := by
  refine ⟨fun _ a X => by simpa using NatTrans.shift_app_comm z a X, fun h => ?_⟩
  exact ⟨fun a => by ext X; simpa using h a X⟩

/-- Shift-compatibility of a central element at a single object only depends on the isomorphism
class of that object. -/
lemma shift_app_of_iso (z : CatCenter C) {X Y : C} (e : X ≅ Y) (a : A)
    (h : (z.app X)⟦a⟧' = z.app (X⟦a⟧)) : (z.app Y)⟦a⟧' = z.app (Y⟦a⟧) := by
  rw [← cancel_epi ((shiftFunctor C a).map e.hom), ← Functor.map_comp,
    CatCenter.naturality z e.hom, Functor.map_comp, h, CatCenter.naturality]

/-- A central element is shift-compatible as soon as it is shift-compatible on the image of a
functor which is essentially surjective on objects. -/
lemma commShift_of_essSurj {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C) [F.EssSurj]
    (z : CatCenter C) (h : ∀ (a : A) (X : D), (z.app (F.obj X))⟦a⟧' = z.app ((F.obj X)⟦a⟧)) :
    NatTrans.CommShift z A :=
  (commShift_iff_app z).2 fun a Y =>
    shift_app_of_iso z (F.objObjPreimageIso Y) a (h a _)

end Basic

section Image

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type w} [AddMonoid A] [HasShift C A] [HasShift D A]

/-- Let `F : C ⥤ D` commute with the shift and let `w : CatCenter D` have components
`w.app (F.obj X) = F.map (z.app X)` along `F`. Then `w` is shift-compatible at `F.obj X`
precisely when `F` identifies `(z.app X)⟦a⟧'` with `z.app (X⟦a⟧)`. -/
lemma shift_app_image_iff (F : C ⥤ D) [F.CommShift A] {z : CatCenter C} {w : CatCenter D}
    (hw : ∀ X : C, w.app (F.obj X) = F.map (z.app X)) (a : A) (X : C) :
    (w.app (F.obj X))⟦a⟧' = w.app ((F.obj X)⟦a⟧) ↔
      F.map ((z.app X)⟦a⟧') = F.map (z.app (X⟦a⟧)) := by
  have h₁ : (F.commShiftIso a).hom.app X ≫ (w.app (F.obj X))⟦a⟧' =
      F.map ((z.app X)⟦a⟧') ≫ (F.commShiftIso a).hom.app X := by
    rw [hw]; exact (F.commShiftIso_hom_naturality (z.app X) a).symm
  have h₂ : (F.commShiftIso a).hom.app X ≫ w.app ((F.obj X)⟦a⟧) =
      F.map (z.app (X⟦a⟧)) ≫ (F.commShiftIso a).hom.app X := by
    rw [← hw]; exact w.naturality _
  rw [← cancel_epi ((F.commShiftIso a).hom.app X), h₁, h₂, cancel_mono]

/-- Two central elements of `C` with the same image under a faithful functor, in the sense that
both compute the components of one central element of `D`, are equal. -/
lemma ext_of_faithful (F : C ⥤ D) [F.Faithful] {z z' : CatCenter C} {w : CatCenter D}
    (hw : ∀ X : C, w.app (F.obj X) = F.map (z.app X))
    (hw' : ∀ X : C, w.app (F.obj X) = F.map (z'.app X)) : z = z' :=
  CatCenter.ext _ _ fun X => F.map_injective ((hw X).symm.trans (hw' X))

end Image

section Subalgebra

variable (R : Type t) [CommRing R] (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear R C]
  (A : Type w) [AddMonoid A] [HasShift C A] [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear R]

/-- **The shift-compatible centre of a category.** The central elements commuting with the shift
by `A` form an `R`-subalgebra of `CatCenter C`. -/
def shiftSubalgebra : Subalgebra R (CatCenter C) where
  carrier := {z | ∀ (a : A) (X : C), (z.app X)⟦a⟧' = z.app (X⟦a⟧)}
  mul_mem' hx hy := by
    intro a X
    rw [mul_app, Functor.map_comp, hx, hy, mul_app]
  one_mem' := by
    intro a X
    simp [End.one_def]
  add_mem' hx hy := by
    intro a X
    rw [app_add, Functor.map_add, hx, hy, app_add]
  zero_mem' := by
    intro a X
    simp
  algebraMap_mem' r := by
    intro a X
    rw [algebraMap_app, algebraMap_app, Functor.map_smul, Functor.map_id]

variable {R C A}

/-- A central element lies in `CategoryTheory.CatCenter.shiftSubalgebra R C A` exactly when, for
every `a` and every `X`, shifting its component at `X` by `a` gives its component at `X⟦a⟧`. -/
@[simp]
lemma mem_shiftSubalgebra (z : CatCenter C) :
    z ∈ shiftSubalgebra R C A ↔ ∀ (a : A) (X : C), (z.app X)⟦a⟧' = z.app (X⟦a⟧) := Iff.rfl

/-- Membership in the shift-compatible centre is Mathlib's compatibility of a natural
transformation with the shift. -/
lemma mem_shiftSubalgebra_iff_commShift (z : CatCenter C) :
    z ∈ shiftSubalgebra R C A ↔ NatTrans.CommShift z A :=
  (commShift_iff_app z).symm

variable (R C A)

open scoped IsMulCommutative in
/-- The shift-compatible centre is commutative, being a subring of the commutative ring
`CatCenter C`. -/
instance instIsMulCommutativeShiftSubalgebra : IsMulCommutative (shiftSubalgebra R C A) where
  is_comm.comm x y := Subtype.ext (mul_comm x.1 y.1)

end Subalgebra

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type w} [AddMonoid A] [HasShift C A] [HasShift D A]
  (E : C ≌ D) [E.functor.CommShift A]

/-- Conjugation by an equivalence preserves and reflects compatibility with the shift. -/
lemma commShift_transport_iff (z : CatCenter C) :
    NatTrans.CommShift (transport E z) A ↔ NatTrans.CommShift z A := by
  have hw := transport_app_functor E z
  rw [commShift_iff_app, commShift_iff_app]
  refine ⟨fun h a X =>
      E.functor.map_injective ((shift_app_image_iff E.functor hw a X).1 (h a _)), fun h => ?_⟩
  exact (commShift_iff_app _).1 (commShift_of_essSurj E.functor _ fun a X =>
    (shift_app_image_iff E.functor hw a X).2 (by rw [h]))

variable (R : Type t) [CommRing R] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  [∀ a : A, (shiftFunctor C a).Additive] [∀ a : A, (shiftFunctor C a).Linear R]
  [∀ a : A, (shiftFunctor D a).Additive] [∀ a : A, (shiftFunctor D a).Linear R]

/-- Transporting a central element along an equivalence compatible with the shift preserves and
reflects membership in the shift-compatible centre. -/
lemma transport_mem_shiftSubalgebra_iff (z : CatCenter C) :
    transport E z ∈ shiftSubalgebra R D A ↔ z ∈ shiftSubalgebra R C A := by
  rw [mem_shiftSubalgebra_iff_commShift, mem_shiftSubalgebra_iff_commShift]
  exact commShift_transport_iff E z

variable [E.functor.Additive] [E.functor.Linear R]

/-- **Transport of structure for the shift-compatible centre.** A shift-commuting `R`-linear
additive equivalence `E : C ≌ D` induces an isomorphism of `R`-algebras between the
shift-compatible centres of `C` and of `D`. -/
def transportShiftAlgEquiv : shiftSubalgebra R C A ≃ₐ[R] shiftSubalgebra R D A where
  toFun z := ⟨transport E z.1, (transport_mem_shiftSubalgebra_iff E R z.1).2 z.2⟩
  invFun w := ⟨transport E.symm w.1, by
    refine (mem_shiftSubalgebra_iff_commShift _).2 ((commShift_transport_iff E _).1 ?_)
    rw [transport_transport_symm]
    exact (mem_shiftSubalgebra_iff_commShift _).1 w.2⟩
  left_inv z := Subtype.ext (transport_transport_symm E.symm z.1)
  right_inv w := Subtype.ext (transport_transport_symm E w.1)
  map_mul' x y := Subtype.ext (transport_mul E x.1 y.1)
  map_add' x y := Subtype.ext (transport_add E x.1 y.1)
  commutes' r := Subtype.ext (transport_algebraMap E R r)

/-- The underlying central element of the image of `z` under
`CategoryTheory.CatCenter.transportShiftAlgEquiv E R` is the transport of `z` along `E`. -/
@[simp]
lemma transportShiftAlgEquiv_coe (z : shiftSubalgebra R C A) :
    (transportShiftAlgEquiv E R z : CatCenter D) = transport E z.1 := rfl

end Transport

section HomologicalComplex

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {ι : Type*} (c : ComplexShape ι)

/-- A central element of `C` acts degreewise on homological complexes, giving a central element
of `HomologicalComplex C c`. -/
def homologicalComplex (z : CatCenter C) : CatCenter (HomologicalComplex C c) where
  app K :=
    { f i := z.app (K.X i)
      comm' _ _ _ := (CatCenter.naturality z _).symm }
  naturality _ _ φ := by ext i; exact CatCenter.naturality z (φ.f i)

/-- The degree `i` component of `CategoryTheory.CatCenter.homologicalComplex c z` at a complex `K`
is the component of `z` at `K.X i`. -/
@[simp]
lemma homologicalComplex_app_f (z : CatCenter C) (K : HomologicalComplex C c) (i : ι) :
    ((z.homologicalComplex c).app K).f i = z.app (K.X i) := rfl

variable (R : Type t) [CommRing R] [Linear R C]

/-- **The centre of a category acts on its complexes.** The degreewise action of the centre of
an `R`-linear category `C` on `HomologicalComplex C c` is a morphism of `R`-algebras. -/
def homologicalComplexAlgHom : CatCenter C →ₐ[R] CatCenter (HomologicalComplex C c) where
  toFun z := z.homologicalComplex c
  map_one' := CatCenter.ext _ _ fun K => by ext i; simp [End.one_def]
  map_mul' x y := CatCenter.ext _ _ fun K => by ext i; simp
  map_zero' := CatCenter.ext _ _ fun K => by ext i; simp
  map_add' x y := CatCenter.ext _ _ fun K => by ext i; simp [app_add]
  commutes' r := CatCenter.ext _ _ fun K => by
    ext i
    rw [algebraMap_app, homologicalComplex_app_f, algebraMap_app,
      HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]

/-- The underlying function of `CategoryTheory.CatCenter.homologicalComplexAlgHom c R` is
`CategoryTheory.CatCenter.homologicalComplex c`. -/
@[simp]
lemma homologicalComplexAlgHom_apply (z : CatCenter C) :
    homologicalComplexAlgHom c R z = z.homologicalComplex c := rfl

variable [DecidableEq ι] [HasZeroObject C]

/-- On a complex concentrated in a single degree, the degreewise action of a central element is
the single-degree complex of its action. -/
lemma homologicalComplex_app_single (z : CatCenter C) (j : ι) (M : C) :
    (z.homologicalComplex c).app ((HomologicalComplex.single C c j).obj M) =
      (HomologicalComplex.single C c j).map (z.app M) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hij : i = j
  · subst hij
    have h := CatCenter.naturality z (HomologicalComplex.singleObjXSelf c i M).hom
    rw [HomologicalComplex.single_map_f_self, homologicalComplex_app_f, ← assoc, h, assoc,
      Iso.hom_inv_id, comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X c j M i hij).eq_of_src _ _

end HomologicalComplex

section CochainComplex

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- The degreewise action of a central element on cochain complexes commutes with the shift:
both sides have component `z.app (K.X (p + n))` in degree `p`. -/
lemma commShift_homologicalComplex_up (z : CatCenter C) :
    NatTrans.CommShift (z.homologicalComplex (ComplexShape.up ℤ)) ℤ :=
  (commShift_iff_app _).2 fun n K => by ext p; rfl

end CochainComplex

section Localization

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

variable {A : Type w} [AddMonoid A] [HasShift C A] [HasShift D A] [L.CommShift A] [L.EssSurj] in
/-- The localization of a shift-compatible central element is shift-compatible. -/
lemma commShift_localization (z : CatCenter C) (hz : NatTrans.CommShift z A) :
    NatTrans.CommShift (z.localization L W) A :=
  commShift_of_essSurj L _ fun a X =>
    (shift_app_image_iff L (fun X => localization_app z L W X) a X).2
      (congrArg L.map ((commShift_iff_app z).1 hz a X))

variable (R : Type t) [CommRing R] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  [L.Linear R]

/-- The localization of the central element given by the action of `r : R` is the central
element given by the action of `r` on the localized category. -/
lemma localization_algebraMap (r : R) :
    (algebraMap R (CatCenter C) r).localization L W = algebraMap R (CatCenter D) r :=
  ext_of_localization L W _ _ fun X => by
    rw [localization_app, algebraMap_app, algebraMap_app, L.map_smul, L.map_id]

variable [L.Additive]

/-- `CatCenter.localizationRingHom` for an `R`-linear localization functor, as a morphism of
`R`-algebras. -/
noncomputable def localizationAlgHom : CatCenter C →ₐ[R] CatCenter D where
  __ := localizationRingHom L W
  commutes' := localization_algebraMap L W R

/-- The underlying function of `CategoryTheory.CatCenter.localizationAlgHom L W R` is
`CategoryTheory.CatCenter.localization L W`. -/
@[simp]
lemma localizationAlgHom_apply (z : CatCenter C) :
    localizationAlgHom L W R z = z.localization L W := rfl

end Localization

end CatCenter

end CategoryTheory

namespace ModuleCat

open CategoryTheory Limits

open scoped ModuleCat.Algebra

universe w u t

variable (R : Type t) [CommRing R] (A : Type u) [Ring A] [Algebra R A]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The canonical map from the centre of a ring `A` to the centre of the derived category of
`A`-modules: a central element acts on each module, hence degreewise on each complex, and the
action descends to the localization. -/
noncomputable def centerToCatCenterDerived :
    Subalgebra.center R A →ₐ[R] CatCenter (DerivedCategory (ModuleCat.{u} A)) :=
  (CatCenter.localizationAlgHom (DerivedCategory.Q (C := ModuleCat.{u} A))
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) R).comp <|
    (CatCenter.homologicalComplexAlgHom (ComplexShape.up ℤ) R).comp
      (ModuleCat.centerAlgEquiv R A).toAlgHom

/-- The image of a central element of `A` is computed on the derived category of a complex
concentrated in degree `n` by the action on that module. -/
lemma centerToCatCenterDerived_app_single (a : Subalgebra.center R A) (n : ℤ)
    (M : ModuleCat.{u} A) :
    (centerToCatCenterDerived R A a).app ((DerivedCategory.singleFunctor _ n).obj M) =
      (DerivedCategory.singleFunctor _ n).map
        ((ModuleCat.centerToCatCenter R A a).app M) := by
  show (((ModuleCat.centerToCatCenter R A a).homologicalComplex
        (ComplexShape.up ℤ)).localization _ _).app
      (DerivedCategory.Q.obj ((HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) n).obj M)) =
    DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{u} A)
      (ComplexShape.up ℤ) n).map ((ModuleCat.centerToCatCenter R A a).app M))
  rw [CatCenter.localization_app, CatCenter.homologicalComplex_app_single]

/-- **The centre of a ring maps to the shift-compatible centre of its derived category.** The
image of `ModuleCat.centerToCatCenterDerived` consists of shift-compatible elements, because
the degreewise action on cochain complexes commutes with the shift. -/
noncomputable def centerToShiftCenterDerived :
    Subalgebra.center R A →ₐ[R]
      CatCenter.shiftSubalgebra R (DerivedCategory (ModuleCat.{u} A)) ℤ :=
  (centerToCatCenterDerived R A).codRestrict _ fun _ =>
    (CatCenter.mem_shiftSubalgebra_iff_commShift _).2
      (CatCenter.commShift_localization _ _ _
        (CatCenter.commShift_homologicalComplex_up _))

/-- The underlying central element of `ModuleCat.centerToShiftCenterDerived R A a` is
`ModuleCat.centerToCatCenterDerived R A a`. -/
@[simp]
lemma centerToShiftCenterDerived_coe (a : Subalgebra.center R A) :
    (centerToShiftCenterDerived R A a : CatCenter (DerivedCategory (ModuleCat.{u} A))) =
      centerToCatCenterDerived R A a := rfl

/-- **The canonical map is injective.** A complex concentrated in degree `0` embeds the category
of modules in the derived category fully faithfully, so the action of a central element on all
modules — hence the element itself — is recovered from its image. -/
lemma centerToShiftCenterDerived_injective :
    Function.Injective (centerToShiftCenterDerived R A) := by
  intro a b hab
  have h : centerToCatCenterDerived R A a = centerToCatCenterDerived R A b := by
    simpa using Subtype.ext_iff.1 hab
  refine (ModuleCat.centerAlgEquiv R A).injective
    (CatCenter.ext_of_faithful (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
      (w := centerToCatCenterDerived R A a) (fun M => ?_) fun M => ?_)
  · exact centerToCatCenterDerived_app_single R A a 0 M
  · rw [h]
    exact centerToCatCenterDerived_app_single R A b 0 M

end ModuleCat

end
