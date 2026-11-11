module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksFrontier.AlgebraicGeometry.Limits.FlatProjection

/-!
# Flatness and openness of an infinite product of schemes over a base

Let `f i : T i ⟶ S` be a family of affine morphisms of schemes, so that the objects
`Over.mk (f i)` have a product in `Over S` by `AlgebraicGeometry.hasProduct_of_isAffineHom`.
If every `f i` is flat, the structure morphism of the product is flat. If every `f i` is
universally open and every morphism from the spectrum of a field to `S` lifts along every `f i`,
the structure morphism of the product is an open map.

## Main results

* `AlgebraicGeometry.finiteProduct_hom_mem`: for a property of morphisms of schemes that is
  multiplicative and stable under base change, the structure morphism of a finite product in
  `Over K` of objects with that property again has it.
* `AlgebraicGeometry.liftToFinsetObj_map_left_mem`: under the same hypotheses, every transition
  morphism of the system of finite subproducts has that property.
* `AlgebraicGeometry.flat_product_hom`: the structure morphism of the product over `S` of flat
  affine morphisms is flat.
* `AlgebraicGeometry.isOpenMap_product_hom`: the structure morphism of the product over `S` of
  universally open affine morphisms along which every field-valued point of `S` lifts is an
  open map.

## Implementation notes

The product is the inverse limit of its finite subproducts. A transition morphism between two
finite subproducts, indexed by `K ⊆ J`, is identified with the first projection of the binary
product of the subproducts indexed by `K` and by `J \ K`
(`CategoryTheory.Limits.ProductsFromFiniteCofiltered.liftToFinsetObjSdiffIso`), so it is a base
change of the structure morphism of a finite subproduct. Flatness of the product then follows
from `AlgebraicGeometry.flat_π_app`, applied at the empty subproduct, which is `S` itself.

For openness, the projection of the product onto each finite subproduct is surjective: a point
of the finite subproduct gives a point with values in its residue field, and the missing
components are supplied by the lifting hypothesis. The preimages of affine opens of the finite
subproducts form a basis of the product (`AlgebraicGeometry.isBasis_preimage_isAffineOpen`),
and the image in `S` of such a preimage is the image of an open of a finite subproduct, which
is open because finite products of universally open morphisms are universally open.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.ProductsFromFiniteCofiltered

universe u v w u' v'

namespace CategoryTheory.Limits.ProductsFromFiniteCofiltered

variable {C : Type u'} [Category.{v'} C] [HasFiniteProducts C] {I : Type w} (X : I → C)

/-- The morphism into the subproduct of `X` indexed by a finite set `J` with components `h`. -/
noncomputable def finiteSubproductLift (J : (Finset (Discrete I))ᵒᵖ) {Z : C}
    (h : ∀ x : J.unop, Z ⟶ X x.1.as) : Z ⟶ (liftToFinsetObj (Discrete.functor X)).obj J :=
  Pi.lift h

/-- The components of `finiteSubproductLift X J h` are the morphisms `h`. -/
@[reassoc (attr := simp)]
lemma finiteSubproductLift_π (J : (Finset (Discrete I))ᵒᵖ) {Z : C}
    (h : ∀ x : J.unop, Z ⟶ X x.1.as) (x : J.unop) :
    finiteSubproductLift X J h ≫ finiteSubproductπ X J x = h x :=
  Pi.lift_comp_π _ _

open Classical in
/-- For finite sets of indices `K ⊆ J`, the subproduct of `X` indexed by `J` is the binary
product of the subproducts indexed by `K` and by `J \ K`; the first projection is the
transition morphism of the system of finite subproducts. -/
noncomputable def liftToFinsetObjSdiffIso {J K : (Finset (Discrete I))ᵒᵖ} (g : J ⟶ K) :
    (liftToFinsetObj (Discrete.functor X)).obj J ≅
      (liftToFinsetObj (Discrete.functor X)).obj K ⨯
        (liftToFinsetObj (Discrete.functor X)).obj (Opposite.op (J.unop \ K.unop)) where
  hom := prod.lift ((liftToFinsetObj (Discrete.functor X)).map g)
    ((liftToFinsetObj (Discrete.functor X)).map (homOfLE Finset.sdiff_subset).op)
  inv := finiteSubproductLift X J fun x => if hx : x.1 ∈ K.unop then
      prod.fst ≫ finiteSubproductπ X K ⟨x.1, hx⟩
    else prod.snd ≫ finiteSubproductπ X _ ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hx⟩⟩
  hom_inv_id := by
    refine finiteSubproduct_hom_ext X fun x => ?_
    rw [Category.assoc, Category.id_comp, finiteSubproductLift_π]
    split_ifs with hx
    · rw [prod.lift_fst_assoc, finiteSubproductπ_naturality]
    · rw [prod.lift_snd_assoc, finiteSubproductπ_naturality]
  inv_hom_id := by
    refine prod.hom_ext ?_ ?_
    · refine finiteSubproduct_hom_ext X fun y => ?_
      rw [Category.assoc, Category.assoc, prod.lift_fst_assoc, finiteSubproductπ_naturality,
        Category.id_comp, finiteSubproductLift_π, dite_eq_left y.2]
    · refine finiteSubproduct_hom_ext X fun y => ?_
      rw [Category.assoc, Category.assoc, prod.lift_snd_assoc, finiteSubproductπ_naturality,
        Category.id_comp, finiteSubproductLift_π, dite_eq_right (Finset.mem_sdiff.1 y.2).2]

/-- The transition morphism of the system of finite subproducts is the first projection of
`liftToFinsetObjSdiffIso`. -/
@[reassoc (attr := simp)]
lemma liftToFinsetObjSdiffIso_hom_fst {J K : (Finset (Discrete I))ᵒᵖ} (g : J ⟶ K) :
    (liftToFinsetObjSdiffIso X g).hom ≫ prod.fst = (liftToFinsetObj (Discrete.functor X)).map g :=
  prod.lift_fst _ _

/-- The morphism into the product of `X`, as the vertex of `finiteSubproductsCone X`, with
components `h`. -/
noncomputable def finiteSubproductsConeLiftOf [HasProduct X] {Z : C} (h : ∀ i, Z ⟶ X i) :
    Z ⟶ (finiteSubproductsCone X).pt :=
  Pi.lift h

/-- The components of `finiteSubproductsConeLiftOf X h` are the morphisms `h`. -/
@[reassoc (attr := simp)]
lemma finiteSubproductsConeLiftOf_π [HasProduct X] {Z : C} (h : ∀ i, Z ⟶ X i) (i : I) :
    finiteSubproductsConeLiftOf X h ≫ finiteSubproductsConeπ X i = h i :=
  Pi.lift_comp_π _ _

end CategoryTheory.Limits.ProductsFromFiniteCofiltered

namespace AlgebraicGeometry

variable (P : MorphismProperty Scheme.{u})

/-- For a multiplicative property `P` stable under base change, an object of `Over K` isomorphic
to one whose structure morphism has `P` has a structure morphism with `P`. -/
private lemma over_hom_mem_of_iso [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {K : Scheme.{u}} {Y Z : Over K} (e : Y ≅ Z) (h : P Z.hom) : P Y.hom := by
  have : IsIso e.hom.left := (Over.forget K).map_isIso e.hom
  rw [← Over.w e.hom]
  exact P.comp_mem _ _ (P.of_isIso _) h

/-- For a multiplicative property `P` stable under base change, the first projection of a binary
product in `Over K` has `P` when the structure morphism of the second factor has `P`: it is a
base change of that structure morphism. -/
lemma prod_fst_left_mem [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {K : Scheme.{u}} (Y Z : Over K) (h : P Z.hom) : P (prod.fst : Y ⨯ Z ⟶ Y).left := by
  rw [← Over.prodLeftIsoPullback_hom_fst]
  exact P.comp_mem _ _ (P.of_isIso _) (P.pullback_fst _ _ h)

/-- For a property of morphisms of schemes that is multiplicative and stable under base change,
the structure morphism of a finite product in `Over K` of objects whose structure morphisms
have that property again has it. -/
theorem finiteProduct_hom_mem [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {K : Scheme.{u}} {α : Type v} [Finite α] (Y : α → Over K) (hY : ∀ a, P (Y a).hom) :
    P (∏ᶜ Y).hom := by
  classical
  have := Fintype.ofFinite α
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ (Y : α → Over K), (∀ a, P (Y a).hom) → P (∏ᶜ Y).hom) ?_ ?_ ?_ α Y hY
  · intro α β _ e ih Z hZ
    have : HasProduct (fun a : α => Z (e a)) :=
      hasProduct_of_equiv_of_iso Z (fun a => Z (e a)) e (fun _ => Iso.refl _)
    let e' : (∏ᶜ fun a : α => Z (e a)) ≅ ∏ᶜ Z := Pi.whiskerEquiv e fun _ => Iso.refl _
    exact over_hom_mem_of_iso P e'.symm (ih (fun a => Z (e a)) (fun a => hZ (e a)))
  · intro Y _
    have hP : IsTerminal (∏ᶜ Y) := IsTerminal.ofUniqueHom
      (fun X => Pi.lift fun a => isEmptyElim a)
      (by intro X f; apply Pi.hom_ext; intro a; exact isEmptyElim a)
    let e : (∏ᶜ Y) ≅ Over.mk (𝟙 K) := hP.uniqueUpToIso Over.mkIdTerminal
    exact over_hom_mem_of_iso P e (P.id_mem K)
  · intro α _ ih Y hY
    let R : Over K := ∏ᶜ (fun a : α => Y (some a))
    have hR : P R.hom := ih (fun a => Y (some a)) (fun a => hY (some a))
    refine over_hom_mem_of_iso P (overOptionProductIso Y) ?_
    rw [← Over.w (prod.fst : Y none ⨯ R ⟶ Y none)]
    exact P.comp_mem _ _ (prod_fst_left_mem P _ _ hR) (hY none)

/-- Every object of the system of finite subproducts of a family of objects of `Over S` whose
structure morphisms have a property `P` as in `finiteProduct_hom_mem` has a structure morphism
with property `P`. -/
theorem liftToFinsetObj_obj_hom_mem [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : Scheme.{u}} {I : Type w} (X : I → Over S) (hX : ∀ i, P (X i).hom)
    (J : (Finset (Discrete I))ᵒᵖ) : P ((liftToFinsetObj (Discrete.functor X)).obj J).hom :=
  finiteProduct_hom_mem P (fun x : J.unop => X x.1.as) fun x => hX x.1.as

/-- Every transition morphism of the system of finite subproducts of a family of objects of
`Over S` whose structure morphisms have a property `P` as in `finiteProduct_hom_mem` has
property `P`. -/
theorem liftToFinsetObj_map_left_mem [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : Scheme.{u}} {I : Type w} (X : I → Over S) (hX : ∀ i, P (X i).hom)
    {J K : (Finset (Discrete I))ᵒᵖ} (g : J ⟶ K) :
    P ((liftToFinsetObj (Discrete.functor X)).map g).left := by
  have : IsIso (liftToFinsetObjSdiffIso X g).hom.left :=
    (Over.forget S).map_isIso (liftToFinsetObjSdiffIso X g).hom
  rw [← liftToFinsetObjSdiffIso_hom_fst, Over.comp_left]
  exact P.comp_mem _ _ (P.of_isIso _)
    (prod_fst_left_mem P _ _ (liftToFinsetObj_obj_hom_mem P X hX _))

/-- The structure morphism of the product over `S` of a family of flat affine morphisms is
flat. -/
theorem flat_product_hom {I : Type u} (S : Scheme.{u}) (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ S)
    [∀ i, IsAffineHom (f i)] [∀ i, Flat (f i)] :
    letI := hasProduct_of_isAffineHom S T f
    Flat (∏ᶜ fun i ↦ Over.mk (f i)).hom := by
  have := hasProduct_of_isAffineHom S T f
  set X : I → Over S := fun i ↦ Over.mk (f i)
  set D := liftToFinsetObj (Discrete.functor X)
  have hc := isLimitOfPreserves (Over.forget S) (finiteSubproductsConeIsLimit X)
  have hA : ∀ i, @IsAffineHom _ _ (X i).hom := fun i => inferInstanceAs (IsAffineHom (f i))
  have hF : ∀ i, @Flat _ _ (X i).hom := fun i => inferInstanceAs (Flat (f i))
  have hπ := flat_π_app (D ⋙ Over.forget S) _ hc
    (fun g => liftToFinsetObj_map_left_mem @IsAffineHom X hA g)
    (fun g => liftToFinsetObj_map_left_mem @Flat X hF g) (Opposite.op ∅)
  have h0 : Flat (D.obj (Opposite.op ∅)).hom := liftToFinsetObj_obj_hom_mem @Flat X hF _
  have hw : (∏ᶜ X).hom = ((finiteSubproductsCone X).π.app (Opposite.op ∅)).left ≫
      (D.obj (Opposite.op ∅)).hom := (Over.w _).symm
  rw [hw]
  exact @Flat.comp _ _ _ _ _ hπ h0

/-- The structure morphism of the product over `S` of a family of universally open affine
morphisms `f i` is an open map, provided every morphism from the spectrum of a field to `S`
lifts along every `f i`. -/
theorem isOpenMap_product_hom {I : Type u} (S : Scheme.{u}) (T : I → Scheme.{u})
    (f : ∀ i, T i ⟶ S) [∀ i, IsAffineHom (f i)] [∀ i, UniversallyOpen (f i)]
    (hlift : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ S) (i : I),
      ∃ y : Spec (.of K) ⟶ T i, y ≫ f i = x) :
    letI := hasProduct_of_isAffineHom S T f
    IsOpenMap (∏ᶜ fun i ↦ Over.mk (f i)).hom.base := by
  have := hasProduct_of_isAffineHom S T f
  classical
  set X : I → Over S := fun i ↦ Over.mk (f i)
  set D := liftToFinsetObj (Discrete.functor X)
  let c := (Over.forget S).mapCone (finiteSubproductsCone X)
  have hc : IsLimit c := isLimitOfPreserves (Over.forget S) (finiteSubproductsConeIsLimit X)
  have hA : ∀ i, @IsAffineHom _ _ (X i).hom := fun i => inferInstanceAs (IsAffineHom (f i))
  have hU : ∀ i, @UniversallyOpen _ _ (X i).hom :=
    fun i => inferInstanceAs (UniversallyOpen (f i))
  have : ∀ {J K : (Finset (Discrete I))ᵒᵖ} (g : J ⟶ K),
      IsAffineHom ((D ⋙ Over.forget S).map g) :=
    fun g => liftToFinsetObj_map_left_mem @IsAffineHom X hA g
  have hopen (J : (Finset (Discrete I))ᵒᵖ) : IsOpenMap (D.obj J).hom.base := by
    have : UniversallyOpen (D.obj J).hom := liftToFinsetObj_obj_hom_mem @UniversallyOpen X hU J
    exact (D.obj J).hom.isOpenMap
  have hsurj (J : (Finset (Discrete I))ᵒᵖ) :
      Function.Surjective ((finiteSubproductsCone X).π.app J).left.base := by
    intro y
    let κ := (D.obj J).left.residueField y
    let p : Spec (.of κ) ⟶ (D.obj J).left := (D.obj J).left.fromSpecResidueField y
    let x : Spec (.of κ) ⟶ S := p ≫ (D.obj J).hom
    choose z hz using fun i => hlift κ x i
    let w : ∀ i, Spec (.of κ) ⟶ T i := fun i =>
      if hi : Discrete.mk i ∈ J.unop then p ≫ (finiteSubproductπ X J ⟨_, hi⟩).left else z i
    have hw (i : I) : w i ≫ f i = x := by
      by_cases hi : Discrete.mk i ∈ J.unop
      · simp only [w, dite_eq_left hi, Category.assoc, x]
        exact congrArg (p ≫ ·) (Over.w (finiteSubproductπ X J ⟨_, hi⟩))
      · simp only [w, dite_eq_right hi, hz]
    let q : Over.mk x ⟶ (finiteSubproductsCone X).pt :=
      finiteSubproductsConeLiftOf X fun i => Over.homMk (w i) (hw i)
    have hq : q ≫ (finiteSubproductsCone X).π.app J = Over.homMk (U := Over.mk x) p rfl := by
      refine finiteSubproduct_hom_ext X fun a => ?_
      rw [Category.assoc, finiteSubproductsCone_π_app_finiteSubproductπ,
        finiteSubproductsConeLiftOf_π]
      ext
      simp [w, dite_eq_left a.2]
    have h1 : (q ≫ (finiteSubproductsCone X).π.app J).left = p := congrArg (·.left) hq
    obtain ⟨t⟩ : Nonempty (Spec (.of κ)) := inferInstance
    refine ⟨q.left t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
    exact (D.obj J).left.fromSpecResidueField_apply y t
  have hB := isBasis_preimage_isAffineOpen (D ⋙ Over.forget S) c hc
  refine (TopologicalSpace.IsTopologicalBasis.isOpenMap_iff hB).2 ?_
  rintro _ ⟨_, ⟨J, V, -, rfl⟩, rfl⟩
  have hw : (∏ᶜ X).hom = ((finiteSubproductsCone X).π.app J).left ≫ (D.obj J).hom :=
    (Over.w _).symm
  have himg : (∏ᶜ X).hom.base '' ((c.π.app J ⁻¹ᵁ V : c.pt.Opens) : Set c.pt) =
      (D.obj J).hom.base '' (V : Set ((D ⋙ Over.forget S).obj J)) := by
    rw [hw]
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, ht, (Scheme.Hom.comp_apply _ _ t).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨t, rfl⟩ := hsurj J v
      exact ⟨t, hv, Scheme.Hom.comp_apply _ _ t⟩
  convert hopen J _ V.isOpen using 1
  exact himg

end AlgebraicGeometry

end
