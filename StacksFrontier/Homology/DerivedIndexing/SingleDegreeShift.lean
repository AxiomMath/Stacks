module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The degree-`q` derived-functor unit is the degree-zero one, shifted

Let `P : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, with `𝒜` having enough
injectives. `Stacks.DerivedIndexing.singleDerivedUnit` attaches to every `q : ℤ` the canonical
map

`(Pℱ)[-q] ⟶ RP(ℱ[-q])`

in `D⁺(ℬ)`. An object placed in cohomological degree `q` is an object placed in degree `0`,
shifted by `-q`, so the family of these maps ought to be compatible with that shift. This file
proves it: `Stacks.DerivedIndexing.singleDerivedUnit_comm` is the commutation of the family
`q ↦ singleDerivedUnit P q` with the comparison isomorphisms
`(DerivedCategory.Plus.singleFunctors _).shiftIso` of the single functors with the shift. That
is the degree shift left open by [Stacks, Tag 0FMD], where the de Rham first Chern class is
taken in degree one and the identification `Pic(X) = H¹(X, 𝒪_X^*)` is natural in degree zero.

Four prerequisites are missing from the ambient library and are supplied here: the shift
compatibility of the three functors `CochainComplex.Plus 𝒜 ⥤ ⋯` that the unit is assembled
from, the family of single functors on *bounded-below* complexes, the shift compatibility of the
derived-functor unit on bounded-below complexes, and the cochain-level compatibility of
`HomologicalComplex.singleMapHomologicalComplex` with the shift.

## Main definitions

* `Stacks.DerivedIndexing.cplusSingleFunctors`: the family of single functors
  `𝒜 ⥤ CochainComplex.Plus 𝒜`, as a `CategoryTheory.SingleFunctors`. It is the lift along the
  inclusion of bounded-below complexes of `CochainComplex.singleFunctors`.
* `Stacks.DerivedIndexing.mapCochainComplexPlusQuotientIso`: the two readings of the termwise
  image of a bounded-below complex in the bounded-below homotopy category.

## Main results

* `Stacks.DerivedIndexing.commShiftQuotientPlus`,
  `Stacks.DerivedIndexing.commShiftMapCochainComplexPlus`,
  `Stacks.DerivedIndexing.commShiftPlusQ`: the quotient onto the bounded-below homotopy
  category, the functor induced on bounded-below complexes by an additive functor, and the
  localization onto the bounded-below derived category commute with the shift by `ℤ`.
* `Stacks.DerivedIndexing.natTransCommShift_mapCochainComplexPlusDerivedUnit`: **the
  derived-functor unit on bounded-below complexes commutes with the shift.**
* `Stacks.DerivedIndexing.singleMapHomologicalComplex_shiftIso`: **the comparison of an additive
  functor with the formation of a complex concentrated in one degree is compatible with the
  shift**, on cochain complexes.
* `Stacks.DerivedIndexing.mapSinglePlus_comm`: the same, read on bounded-below complexes.
* `Stacks.DerivedIndexing.plusSingleFunctors_shiftIso_hom_app`: **the comparison of the single
  functors into `D⁺(𝒜)` with the shift is the localization of the comparison on complexes.**
* `Stacks.DerivedIndexing.singleDerivedUnit_comm`: **the degree-`q` derived-functor unit is the
  degree-`a'` one shifted**, for `n + q = a'`.

## Implementation notes

Every functor appearing here is a lift along a fully faithful inclusion of a full subcategory,
so its commutation with the shift is `CategoryTheory.Functor.CommShift.ofComp` of
`CategoryTheory.ObjectProperty.liftCompιIso` and instance search finds it after the lift has
been exposed by `dsimp only`. The two comparison isomorphisms whose shift compatibility is not
instance search — the factorization of the localization through the bounded-below homotopy
category, and the junction of the two readings of a termwise image — are obtained with the
reduction lemmas of `StacksFrontier.CategoryTheory.Shift.DetectingCommShift`, exactly as in
`StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift`: whisker with the faithful
inclusion of the subcategory, write the result out as an explicit composite of associators and
whiskered `liftCompιIso`s, and identify the two by
`CategoryTheory.NatTrans.commShift_of_eq`. Each such identification has identity components, and
is discharged by a term-mode chain of unitors rather than by `simp`: the object arguments of the
identities are produced in a spelling which is only definitionally the source and target of the
morphism between them.

The same phenomenon governs the rest of the file, and is the reason for the private algebraic
helpers. The shift on a full subcategory is `CategoryTheory.ObjectProperty.hasShift`, which is
marked `irreducible`, and a complex concentrated in degree `q`, read as a bounded-below complex
and then localized, is the value of `DerivedCategory.Plus.singleFunctor` only definitionally. A
composite of two morphisms whose junction object carries those two spellings is therefore not
type-correct at `implicit` transparency, and `rw` and `simp` refuse to rewrite inside it. Each
such step is taken instead by an `exact` against an abstract lemma of the right shape — the
category-algebra content stated on variables, where no spelling can diverge — which elaborates
at default transparency.

For `singleMapHomologicalComplex_shiftIso` there is a genuine degreewise computation. Away from
the degree where the complexes are concentrated both sides vanish; in that degree both are
composites of `eqToHom`s, and the identity is proof irrelevance. The degree-`q` component of
`(CochainComplex.singleFunctors _).shiftIso` has no `simp` lemma in Mathlib — the definition
deliberately carries none — so it is read off by `singleFunctors_shiftIso_hom_app`, which holds
by `rfl` for any proof of the equality of the two objects.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w w' v v' u u'

namespace Stacks.DerivedIndexing

/-! ### Algebraic helpers -/

section Helpers

variable {V : Type u} [Category.{v} V]

/-- An equality whose two sides are post- respectively pre-composed with an identity. Stated on
variables because at the instances it is used at the identities occur in a spelling which is
only definitionally the source and target of the morphisms they are composed with. -/
private theorem eq_of_comp_id_eq_id_comp {x z : V} {p w : x ⟶ z} {u : z ⟶ z} {v : x ⟶ x}
    (hyp : p ≫ u = v ≫ w) (hu : u = 𝟙 z) (hv : v = 𝟙 x) : p = w := by
  subst hu; subst hv; simpa using hyp

/-- A morphism which is an identity in a spelling only definitionally equal to the one the
surrounding composite uses, inserted into a chain of three identities. -/
private theorem eq_of_id_chain {x : V} (e f g : x ⟶ x) (he : e = 𝟙 x) (hf : f = 𝟙 x)
    (hg : g = 𝟙 x) : e = 𝟙 x ≫ f ≫ 𝟙 x ≫ g ≫ 𝟙 x := by
  subst he; subst hf; subst hg; simp

/-- Cancelling an identity inserted in the middle of a composite. -/
private theorem eq_of_mid_id {w x y z : V} (a : w ⟶ x) (m : x ⟶ x) (hm : m = 𝟙 x) (b : x ⟶ y)
    (c : y ⟶ z) : a ≫ b ≫ c = a ≫ m ≫ b ≫ c := by
  subst hm; simp

/-- Cancelling two identities out of a four-fold composite. -/
private theorem eq_of_comp_id_comp_id {w x y : V} {a : w ⟶ x} {b : x ⟶ y} {u : x ⟶ x}
    {v : y ⟶ y} (hu : u = 𝟙 x) (hv : v = 𝟙 y) : a ≫ u ≫ b ≫ v = a ≫ b := by
  subst hu; subst hv; simp

/-- Transporting a square along a pair of mutually inverse morphisms. -/
private theorem comp_eq_of_cancel {U V' W W' T : V}
    {α : U ⟶ V'} {β : V' ⟶ W'} {γ : W' ⟶ T} {a : U ⟶ W} {g : W ⟶ T}
    {b : W ⟶ U} {d : W' ⟶ V'} {e : W ⟶ W'}
    (hab : a ≫ b = 𝟙 U) (h4 : b ≫ α = e ≫ d) (hdb : d ≫ β = 𝟙 W')
    (hg : g = e ≫ γ) : α ≫ β ≫ γ = a ≫ g := by
  have hkey : α ≫ β = a ≫ e := by
    rw [← Category.id_comp (α ≫ β), ← hab, Category.assoc, ← Category.assoc b, h4,
      Category.assoc, hdb, Category.comp_id]
  rw [hg, ← Category.assoc, ← Category.assoc, hkey]

/-- Reading a commuting square of isomorphisms in the opposite direction. -/
private theorem inv_comp_hom_eq {X Y Z W : V} {f : X ⟶ Y} {f' : Y ⟶ X} {g : Y ⟶ Z} {p : X ⟶ W}
    {q : W ⟶ Z} {q' : Z ⟶ W} (hf : f' ≫ f = 𝟙 Y) (hG : f ≫ g = p ≫ q) (hq : q ≫ q' = 𝟙 W) :
    g ≫ q' = f' ≫ p := by
  rw [← Category.id_comp (g ≫ q'), ← hf, Category.assoc, ← Category.assoc f, hG,
    Category.assoc, hq, Category.comp_id]

/-- Two composites of `eqToHom`s between the same objects agree, by proof irrelevance. The
right-hand side is the shape the degreewise computation of
`Stacks.DerivedIndexing.singleMapHomologicalComplex_shiftIso` reaches. -/
private theorem eqToHom_eq_eqToHom_comp_id_comp {x y z : V} (p : x = z) (q : x = y) (s : y = z) :
    eqToHom p = eqToHom q ≫ 𝟙 y ≫ eqToHom s := by
  subst q
  simp

end Helpers

/-- **Testing a square under a faithful functor commuting with the shift.** The two sides of the
square are morphisms between objects placed in a single degree, read in a full subcategory, and
`t₁`, `t₂` are the images of the two comparison isomorphisms in the ambient category. -/
private theorem comm_of_map {Dc : Type u} [Category.{v} Dc] {E : Type u'} [Category.{v'} E]
    [HasShift Dc ℤ] [HasShift E ℤ] (G : Dc ⥤ E) [G.Faithful] [G.CommShift ℤ] (n : ℤ)
    {Y' Y W' W : Dc} (s₁ : (shiftFunctor Dc n).obj Y' ⟶ Y) (φ : Y ⟶ W) (φ' : Y' ⟶ W')
    (s₂ : (shiftFunctor Dc n).obj W' ⟶ W)
    {t₁ : (shiftFunctor E n).obj (G.obj Y') ⟶ G.obj Y}
    {t₂ : (shiftFunctor E n).obj (G.obj W') ⟶ G.obj W}
    (ht₁ : G.map s₁ = (G.commShiftIso n).hom.app Y' ≫ t₁)
    (ht₂ : G.map s₂ = (G.commShiftIso n).hom.app W' ≫ t₂)
    (H : t₁ ≫ G.map φ = (shiftFunctor E n).map (G.map φ') ≫ t₂) :
    s₁ ≫ φ = (shiftFunctor Dc n).map φ' ≫ s₂ := by
  refine G.map_injective ?_
  rw [G.map_comp, G.map_comp, ht₁, ht₂, Category.assoc, H, ← Category.assoc,
    ← G.commShiftIso_hom_naturality φ' n, Category.assoc]

/-! ### The shift on bounded-below complexes -/

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

/-- **The quotient of bounded-below complexes onto the bounded-below homotopy category commutes
with the shift**: it is a lift along the inclusion of the bounded-below homotopy category. -/
instance commShiftQuotientPlus (A : Type u) [Category.{v} A] [Abelian A] :
    (HomotopyCategory.Plus.quotient A).CommShift ℤ := by
  dsimp only [HomotopyCategory.Plus.quotient]
  infer_instance

/-- **The functor induced on bounded-below complexes by an additive functor commutes with the
shift**: it is a lift along the inclusion of bounded-below complexes. -/
instance commShiftMapCochainComplexPlus (P : A ⥤ B) [P.Additive] :
    P.mapCochainComplexPlus.CommShift ℤ := by
  dsimp only [Functor.mapCochainComplexPlus]
  infer_instance

/-- **The localization of bounded-below complexes onto the bounded-below derived category
commutes with the shift**: it is a lift along the inclusion of the bounded-below derived
category. -/
instance commShiftPlusQ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] :
    (DerivedCategory.Plus.Q (C := A)).CommShift ℤ := by
  dsimp only [DerivedCategory.Plus.Q]
  infer_instance

/-- **The factorization of the localization of bounded-below complexes through the bounded-below
homotopy category commutes with the shift.** The inclusion of the bounded-below derived category
in the unbounded one is faithful and commutes with the shift, and after whiskering with it the
comparison is the unbounded one, transported across the three presentations of the functors
involved as lifts. -/
instance natTransCommShiftPlusQuotientCompQhIso :
    NatTrans.CommShift (DerivedCategory.Plus.quotientCompQhIso A).hom ℤ := by
  refine NatTrans.commShift_of_whiskerRight _ DerivedCategory.Plus.ι ?_
  let eQh : DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ≅
      HomotopyCategory.Plus.ι A ⋙ DerivedCategory.Qh := ObjectProperty.liftCompιIso ..
  let eQuot : HomotopyCategory.Plus.quotient A ⋙ HomotopyCategory.Plus.ι A ≅
      CochainComplex.Plus.ι A ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eQ : DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
      CochainComplex.Plus.ι A ⋙ DerivedCategory.Q := ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eQh.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eQuot.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eQ.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  refine NatTrans.commShift_of_eq (θ :=
    (Functor.associator (HomotopyCategory.Plus.quotient A) DerivedCategory.Plus.Qh
        DerivedCategory.Plus.ι).hom ≫
      Functor.whiskerLeft (HomotopyCategory.Plus.quotient A) eQh.hom ≫
      (Functor.associator (HomotopyCategory.Plus.quotient A) (HomotopyCategory.Plus.ι A)
        DerivedCategory.Qh).inv ≫
      Functor.whiskerRight eQuot.hom DerivedCategory.Qh ≫
      (Functor.associator (CochainComplex.Plus.ι A)
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)) DerivedCategory.Qh).hom ≫
      Functor.whiskerLeft (CochainComplex.Plus.ι A) (DerivedCategory.quotientCompQhIso A).hom ≫
      eQ.inv) ?_
  ext K
  simp only [NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
  rw [ι_map_quotientCompQhIso_hom_app]
  change _ = 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ ≫ 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

/-- **The two readings of the termwise image of a bounded-below complex in the bounded-below
homotopy category.** Applying an additive functor termwise and then passing to the homotopy
category is passing to the homotopy category and then applying the induced functor; the two
agree on the nose. -/
def mapCochainComplexPlusQuotientIso (P : A ⥤ B) [P.Additive] :
    P.mapCochainComplexPlus ⋙ HomotopyCategory.Plus.quotient B ≅
      HomotopyCategory.Plus.quotient A ⋙ P.mapHomotopyCategoryPlus := Iso.refl _

/-- **The two readings of a termwise image in the bounded-below homotopy category agree
compatibly with the shift.** The inclusion of the bounded-below homotopy category is faithful
and commutes with the shift, and after whiskering with it the comparison is the factorization
`CategoryTheory.Functor.mapHomotopyCategoryFactors` of the functor induced on homotopy
categories, transported across the four presentations of the functors involved as lifts. -/
instance natTransCommShift_mapCochainComplexPlusQuotientIso (P : A ⥤ B) [P.Additive] :
    NatTrans.CommShift (mapCochainComplexPlusQuotientIso P).hom ℤ := by
  refine NatTrans.commShift_of_whiskerRight _ (HomotopyCategory.Plus.ι B) ?_
  let eQuotB : HomotopyCategory.Plus.quotient B ⋙ HomotopyCategory.Plus.ι B ≅
      CochainComplex.Plus.ι B ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eMcp : P.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ≅
      CochainComplex.Plus.ι A ⋙ P.mapHomologicalComplex (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eQuotA : HomotopyCategory.Plus.quotient A ⋙ HomotopyCategory.Plus.ι A ≅
      CochainComplex.Plus.ι A ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  let eMapHCP : P.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ≅
      HomotopyCategory.Plus.ι A ⋙ P.mapHomotopyCategory (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eQuotB.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eMcp.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eQuotA.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift eMapHCP.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  refine NatTrans.commShift_of_eq (θ :=
    (Functor.associator P.mapCochainComplexPlus (HomotopyCategory.Plus.quotient B)
        (HomotopyCategory.Plus.ι B)).hom ≫
      Functor.whiskerLeft P.mapCochainComplexPlus eQuotB.hom ≫
      (Functor.associator P.mapCochainComplexPlus (CochainComplex.Plus.ι B)
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))).inv ≫
      Functor.whiskerRight eMcp.hom (HomotopyCategory.quotient B (ComplexShape.up ℤ)) ≫
      (Functor.associator (CochainComplex.Plus.ι A)
        (P.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))).hom ≫
      Functor.whiskerLeft (CochainComplex.Plus.ι A)
        (P.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv ≫
      (Functor.associator (CochainComplex.Plus.ι A)
        (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (P.mapHomotopyCategory (ComplexShape.up ℤ))).inv ≫
      Functor.whiskerRight eQuotA.inv (P.mapHomotopyCategory (ComplexShape.up ℤ)) ≫
      (Functor.associator (HomotopyCategory.Plus.quotient A) (HomotopyCategory.Plus.ι A)
        (P.mapHomotopyCategory (ComplexShape.up ℤ))).hom ≫
      Functor.whiskerLeft (HomotopyCategory.Plus.quotient A) eMapHCP.inv ≫
      (Functor.associator (HomotopyCategory.Plus.quotient A) P.mapHomotopyCategoryPlus
        (HomotopyCategory.Plus.ι B)).inv) ?_
  ext K
  simp only [NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp, Category.comp_id]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    ObjectProperty.liftCompιIso, eQuotB, eMcp, eQuotA, eMapHCP,
    mapCochainComplexPlusQuotientIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  exact eq_of_id_chain _ _ _ ((HomotopyCategory.Plus.ι B).map_id _)
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_id _)
    ((P.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _)

section Unit

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

/-- **The derived-functor unit on bounded-below complexes commutes with the shift.** It is the
composite of the factorization of the localization through the bounded-below homotopy category,
of the comparison of the two readings of a termwise image, and of the unit of `RP`, each of which
commutes with the shift; the composite is rebracketed by associators so that instance search can
put the three together. -/
lemma natTransCommShift_mapCochainComplexPlusDerivedUnit (P : A ⥤ B) [P.Additive]
    [EnoughInjectives A] :
    NatTrans.CommShift (Functor.mapCochainComplexPlusDerivedUnit P) ℤ := by
  refine NatTrans.commShift_of_eq (θ :=
    Functor.whiskerLeft P.mapCochainComplexPlus (DerivedCategory.Plus.quotientCompQhIso B).inv ≫
      (Functor.associator P.mapCochainComplexPlus (HomotopyCategory.Plus.quotient B)
        DerivedCategory.Plus.Qh).inv ≫
      Functor.whiskerRight (mapCochainComplexPlusQuotientIso P).hom DerivedCategory.Plus.Qh ≫
      (Functor.associator (HomotopyCategory.Plus.quotient A) P.mapHomotopyCategoryPlus
        DerivedCategory.Plus.Qh).hom ≫
      Functor.whiskerLeft (HomotopyCategory.Plus.quotient A) P.rightDerivedFunctorPlusUnit ≫
      (Functor.associator (HomotopyCategory.Plus.quotient A) DerivedCategory.Plus.Qh
        P.rightDerivedFunctorPlus).inv ≫
      Functor.whiskerRight (DerivedCategory.Plus.quotientCompQhIso A).hom
        P.rightDerivedFunctorPlus) ?_
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
  refine Eq.trans (Functor.mapCochainComplexPlusDerivedUnit_app P K) ?_
  exact eq_of_mid_id _ _ (DerivedCategory.Plus.Qh.map_id _) _ _

end Unit

/-! ### The comparison of a functor with a complex concentrated in one degree -/

section Single

variable {A₁ : Type u} {A₂ : Type u'} [Category.{v} A₁] [Category.{v'} A₂] [Preadditive A₁]
  [Preadditive A₂] [HasZeroObject A₁] [HasZeroObject A₂]

/-- **The degreewise components of the comparison of the single functors with the shift on
cochain complexes.** They are identifications of objects, so any proof of the equality of the
two objects gives the same morphism. -/
theorem singleFunctors_shiftIso_hom_app_f (A : Type u) [Category.{v} A] [Preadditive A]
    [HasZeroObject A] (n a a' : ℤ) (h : n + a = a') (X : A) (i : ℤ)
    (e : ((shiftFunctor (CochainComplex A ℤ) n).obj
        ((CochainComplex.singleFunctor A a').obj X)).X i =
      ((CochainComplex.singleFunctor A a).obj X).X i) :
    (((CochainComplex.singleFunctors A).shiftIso n a a' h).hom.app X).f i = eqToHom e := rfl

variable (T : A₁ ⥤ A₂) [T.Additive]

/-- **The comparison of an additive functor with the formation of a complex concentrated in one
degree is compatible with the shift.** Away from the degree where the complexes are concentrated
both sides vanish; in that degree both are composites of identifications of objects, and the
identity is proof irrelevance. -/
theorem singleMapHomologicalComplex_shiftIso (n a a' : ℤ) (h : n + a = a') (X : A₁) :
    ((CochainComplex.singleFunctors A₂).shiftIso n a a' h).hom.app (T.obj X) ≫
        (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) a).inv.app X =
      (shiftFunctor (CochainComplex A₂ ℤ) n).map
          ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) a').inv.app X) ≫
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).inv.app
            ((CochainComplex.singleFunctor A₁ a').obj X) ≫
          (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((CochainComplex.singleFunctors A₁).shiftIso n a a' h).hom.app X) := by
  obtain rfl : a' = a + n := by omega
  ext i
  rcases eq_or_ne i a with rfl | hi
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_commShiftIso_inv_app_f,
      Functor.mapHomologicalComplex_map_f,
      singleFunctors_shiftIso_hom_app_f A₂ n i (i + n) h (T.obj X) i
        ((HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (i + n) (T.obj X)).trans
          (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) i (T.obj X)).symm),
      singleFunctors_shiftIso_hom_app_f A₁ n i (i + n) h X i
        ((HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (i + n) X).trans
          (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) i X).symm),
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans]
    exact eqToHom_eq_eqToHom_comp_id_comp _ _ _
  · have hi' : i + n ≠ a + n := by omega
    simp only [CochainComplex.singleFunctors, HomologicalComplex.single, Functor.comp_obj,
      CochainComplex.shiftFunctor_obj_X', hi', Functor.mapHomologicalComplex, hi,
      HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents_inv_app,
      HomologicalComplex.comp_f, ↓reduceDIte, CochainComplex.shiftFunctor_obj_d',
      CochainComplex.singleFunctor_obj_d, CochainComplex.shiftFunctor_map_f']
    exact Limits.comp_zero.trans Limits.zero_comp.symm

end Single

/-! ### Single functors on bounded-below complexes -/

/-- **The family of single functors `𝒜 ⥤ CochainComplex.Plus 𝒜`**, together with its
compatibilities with the shift: the lift along the inclusion of bounded-below complexes of
`CochainComplex.singleFunctors`. -/
def cplusSingleFunctors (A : Type u) [Category.{v} A] [Abelian A] :
    SingleFunctors A (CochainComplex.Plus A) ℤ :=
  SingleFunctors.lift (CochainComplex.singleFunctors A) (CochainComplex.Plus.ι A)
    (fun q => singlePlusFunctor A q) (fun _ => Iso.refl _)

/-- The single functors into the bounded-below derived category, postcomposed with the inclusion
of the unbounded one, are the unbounded single functors. This is the defining property of
`DerivedCategory.Plus.singleFunctors` as a lift. -/
def plusLiftPostcompIso (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] :
    (DerivedCategory.Plus.singleFunctors A).postcomp DerivedCategory.Plus.ι ≅
      DerivedCategory.singleFunctors A :=
  SingleFunctors.liftPostcompIso _ _ _ _

/-- **The comparison of the single functors into `D⁺(𝒜)` with the shift, read through the
inclusion of the unbounded derived category**: it is the unbounded comparison, up to the
commutation of that inclusion with the shift. -/
theorem ι_map_plusSingleFunctors_shiftIso_hom_app (n a a' : ℤ) (h : n + a = a') (Z : A) :
    DerivedCategory.Plus.ι.map
        (((DerivedCategory.Plus.singleFunctors A).shiftIso n a a' h).hom.app Z) =
      (DerivedCategory.Plus.ι.commShiftIso n).hom.app
          ((DerivedCategory.Plus.singleFunctor A a').obj Z) ≫
        ((DerivedCategory.singleFunctors A).shiftIso n a a' h).hom.app Z := by
  have hc := congr_app ((plusLiftPostcompIso A).hom.comm n a a' h) Z
  simp only [SingleFunctors.postcomp_shiftIso_hom_app, NatTrans.comp_app,
    Functor.whiskerRight_app] at hc
  have key := eq_of_comp_id_eq_id_comp hc rfl
    ((shiftFunctor (DerivedCategory A) n).map_id _)
  exact Eq.trans
    (Iso.hom_inv_id_app_assoc (Functor.commShiftIso DerivedCategory.Plus.ι n) _ _).symm
    (congrArg (fun z => (Functor.commShiftIso DerivedCategory.Plus.ι n).hom.app
      ((DerivedCategory.Plus.singleFunctor A a').obj Z) ≫ z) key)

omit [HasDerivedCategory A] in
/-- **The comparison of the single functors on bounded-below complexes with the shift, read
through the inclusion of all complexes**: it is the comparison on all complexes, up to the
commutation of that inclusion with the shift. -/
theorem ι_map_cplusSingleFunctors_shiftIso_hom_app (n a a' : ℤ) (h : n + a = a') (Z : A) :
    (CochainComplex.Plus.ι A).map (((cplusSingleFunctors A).shiftIso n a a' h).hom.app Z) =
      ((CochainComplex.Plus.ι A).commShiftIso n).hom.app ((singlePlusFunctor A a').obj Z) ≫
        ((CochainComplex.singleFunctors A).shiftIso n a a' h).hom.app Z := by
  refine Eq.trans (SingleFunctors.map_lift_shiftIso_hom_app (CochainComplex.singleFunctors A)
    (CochainComplex.Plus.ι A) (fun q => singlePlusFunctor A q)
    (fun _ => Iso.refl _) n a a' h Z) ?_
  exact eq_of_comp_id_comp_id ((shiftFunctor (CochainComplex A ℤ) n).map_id _) rfl

/-- **The comparison of the single functors into `D⁺(𝒜)` with the shift is the localization of
the comparison of the single functors on bounded-below complexes**, up to the commutation of the
localization with the shift.

Both sides are preimages under the fully faithful inclusion of the bounded-below derived
category, and in the unbounded one both reduce to the comparison of the single functors on
complexes: the single functors on the unbounded derived category are by definition the
postcomposition of those on complexes with the localization. -/
theorem plusSingleFunctors_shiftIso_hom_app (n a a' : ℤ) (h : n + a = a') (Z : A) :
    ((DerivedCategory.Plus.singleFunctors A).shiftIso n a a' h).hom.app Z =
      (DerivedCategory.Plus.Q.commShiftIso n).inv.app ((singlePlusFunctor A a').obj Z) ≫
        DerivedCategory.Plus.Q.map (((cplusSingleFunctors A).shiftIso n a a' h).hom.app Z) := by
  let eQ : DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
      CochainComplex.Plus.ι A ⋙ DerivedCategory.Q := ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eQ.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have hq := NatTrans.shift_app_comm eQ.hom n ((singlePlusFunctor A a').obj Z)
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hq
  have F4 := eq_of_comp_id_eq_id_comp hq
    ((shiftFunctor (DerivedCategory A) n).map_id _) rfl
  have hab : DerivedCategory.Plus.ι.map
        ((DerivedCategory.Plus.Q.commShiftIso n).inv.app ((singlePlusFunctor A a').obj Z)) ≫
      DerivedCategory.Plus.ι.map
        ((DerivedCategory.Plus.Q.commShiftIso n).hom.app
          ((singlePlusFunctor A a').obj Z)) = 𝟙 _ := by
    simp
  have hg : DerivedCategory.Q.map
        ((CochainComplex.Plus.ι A).map
          (((cplusSingleFunctors A).shiftIso n a a' h).hom.app Z)) =
      DerivedCategory.Q.map
          ((Functor.commShiftIso (CochainComplex.Plus.ι A) n).hom.app
            ((singlePlusFunctor A a').obj Z)) ≫
        DerivedCategory.Q.map
          (((CochainComplex.singleFunctors A).shiftIso n a a' h).hom.app Z) :=
    by rw [ι_map_cplusSingleFunctors_shiftIso_hom_app n a a' h Z]; exact Functor.map_comp _ _ _
  refine DerivedCategory.Plus.ι.map_injective ?_
  refine (ι_map_plusSingleFunctors_shiftIso_hom_app n a a' h Z).trans ?_
  refine Eq.trans ?_ (DerivedCategory.Plus.ι.map_comp _ _).symm
  refine Eq.trans (congrArg (fun z =>
    (Functor.commShiftIso DerivedCategory.Plus.ι n).hom.app
      ((DerivedCategory.Plus.singleFunctor A a').obj Z) ≫ z)
    (SingleFunctors.postcomp_shiftIso_hom_app (CochainComplex.singleFunctors A)
      DerivedCategory.Q n a a' h Z)) ?_
  exact (comp_eq_of_cancel hab F4 (Iso.hom_inv_id_app _ _) hg).trans rfl

/-! ### The degree shift of the derived-functor unit -/

section Shift

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

variable (P : A ⥤ B) [P.Additive]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **The comparison `(Pℱ)[-q] ⟶ P(ℱ[-q])` of an additive functor with a complex concentrated in
one degree is compatible with the shift**, on bounded-below complexes. Both sides are morphisms
in a full subcategory, so the identity is tested under the inclusion, where it is
`Stacks.DerivedIndexing.singleMapHomologicalComplex_shiftIso`. -/
theorem mapSinglePlus_comm (n a a' : ℤ) (h : n + a = a') (Z : A) :
    ((cplusSingleFunctors B).shiftIso n a a' h).hom.app (P.obj Z) ≫
        (mapSinglePlus P a).app Z =
      (shiftFunctor (CochainComplex.Plus B) n).map ((mapSinglePlus P a').app Z) ≫
        (P.mapCochainComplexPlus.commShiftIso n).inv.app ((singlePlusFunctor A a').obj Z) ≫
        P.mapCochainComplexPlus.map
          (((cplusSingleFunctors A).shiftIso n a a' h).hom.app Z) := by
  let eMcp : P.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ≅
      CochainComplex.Plus.ι A ⋙ P.mapHomologicalComplex (ComplexShape.up ℤ) :=
    ObjectProperty.liftCompιIso ..
  have : NatTrans.CommShift eMcp.hom ℤ := Functor.CommShift.ofComp_compatibility _ _
  have hq := NatTrans.shift_app_comm eMcp.hom n ((singlePlusFunctor A a').obj Z)
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hq
  have G4 := eq_of_comp_id_eq_id_comp hq
    ((shiftFunctor (CochainComplex B ℤ) n).map_id _) rfl
  have hkey := inv_comp_hom_eq
    (show (CochainComplex.Plus.ι B).map
          ((P.mapCochainComplexPlus.commShiftIso n).inv.app
            ((singlePlusFunctor A a').obj Z)) ≫
        (CochainComplex.Plus.ι B).map
          ((P.mapCochainComplexPlus.commShiftIso n).hom.app
            ((singlePlusFunctor A a').obj Z)) = 𝟙 _ by
      simp)
    G4 (Iso.hom_inv_id_app _ _)
  have ht₂ : (CochainComplex.Plus.ι B).map
        ((P.mapCochainComplexPlus.commShiftIso n).inv.app
            ((singlePlusFunctor A a').obj Z) ≫
          P.mapCochainComplexPlus.map
            (((cplusSingleFunctors A).shiftIso n a a' h).hom.app Z)) =
      ((CochainComplex.Plus.ι B).commShiftIso n).hom.app
          (P.mapCochainComplexPlus.obj ((singlePlusFunctor A a').obj Z)) ≫
        (((P.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).inv.app
            ((CochainComplex.singleFunctor A a').obj Z) ≫
          (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((CochainComplex.singleFunctors A).shiftIso n a a' h).hom.app Z)) := by
    refine Eq.trans ((CochainComplex.Plus.ι B).map_comp _ _) ?_
    refine Eq.trans (congrArg (fun z => (CochainComplex.Plus.ι B).map
        ((P.mapCochainComplexPlus.commShiftIso n).inv.app
          ((singlePlusFunctor A a').obj Z)) ≫ z)
      ((congrArg (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (ι_map_cplusSingleFunctors_shiftIso_hom_app n a a' h Z)).trans
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map_comp _ _))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((CochainComplex.singleFunctors A).shiftIso n a a' h).hom.app Z)) hkey.symm) ?_
    exact Category.assoc _ _ _
  exact comm_of_map (CochainComplex.Plus.ι B) n _ _ _ _
    (ι_map_cplusSingleFunctors_shiftIso_hom_app n a a' h (P.obj Z)) ht₂
    (singleMapHomologicalComplex_shiftIso P n a a' h Z)

/-- Four-fold composites in the derived category, with the commuting squares the degree shift of
the derived-functor unit is assembled from as hypotheses. Stated on variables because several of
the junction objects carry two spellings which are only definitionally equal. -/
private theorem star_algebra {Dc : Type u} [Category.{v} Dc]
    {X X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ : Dc}
    {sB : X ⟶ Y₀} {α : X ⟶ X₁} {β : X₁ ⟶ Y₀} {Cm : Y₀ ⟶ Y₁} {Ua : Y₁ ⟶ Y₂}
    {β' : X₁ ⟶ X₂} {Em : X₂ ⟶ X₃} {Fm : X₃ ⟶ Y₁}
    {G : X ⟶ X₄} {Hm : X₄ ⟶ X₂} {K : X₄ ⟶ X₃}
    {L : X₃ ⟶ Y₃} {M : Y₃ ⟶ Y₂} {N : X₄ ⟶ Y₄} {O : Y₄ ⟶ Y₃}
    {V : X ⟶ Y₄} {RPi : Y₄ ⟶ Y₅} {R1 : Y₅ ⟶ Y₃} {R : Y₅ ⟶ Y₂}
    (hB : sB = α ≫ β) (hD : β ≫ Cm = β' ≫ Em ≫ Fm) (hnQ : α ≫ β' = G ≫ Hm)
    (hc1 : Hm ≫ Em = K) (hnU : Fm ≫ Ua = L ≫ M) (hCS : K ≫ L = N ≫ O)
    (hV : G ≫ N = V) (hc2 : O = RPi ≫ R1) (hR : R1 ≫ M = R) :
    sB ≫ Cm ≫ Ua = V ≫ RPi ≫ R := by
  subst hB; subst hc1; subst hV; subst hc2; subst hR
  simp only [Category.assoc] at hD hnQ hnU hCS ⊢
  rw [reassoc_of% hD, reassoc_of% hnQ, hnU, reassoc_of% hCS]

variable [EnoughInjectives A]

/-- **The degree-`a` derived-functor unit `(Pℱ)[-a] ⟶ RP(ℱ[-a])` is the degree-`a'` one,
shifted by `n`**, whenever `n + a = a'`. This is [Stacks, Tag 0FMD]'s degree shift: it carries a
statement about the pullback of first cohomology classes, which lives in degree zero, to the
degree-one hypercohomology the de Rham first Chern class of [Stacks, Tag 0FLE] is taken in.

The unit is the localization of the comparison `(Pℱ)[-a] ⟶ P(ℱ[-a])` of complexes followed by
the derived-functor unit on bounded-below complexes, and both factors are compatible with the
shift: the first by `Stacks.DerivedIndexing.mapSinglePlus_comm`, the second by
`Stacks.DerivedIndexing.natTransCommShift_mapCochainComplexPlusDerivedUnit`. The comparison of
the single functors into `D⁺` with the shift is the localization of the one on complexes by
`Stacks.DerivedIndexing.plusSingleFunctors_shiftIso_hom_app`, which is what lets the two be
composed. -/
theorem singleDerivedUnit_comm (n a a' : ℤ) (h : n + a = a') (Z : A) :
    ((DerivedCategory.Plus.singleFunctors B).shiftIso n a a' h).hom.app (P.obj Z) ≫
        singleDerivedUnit P a Z =
      (shiftFunctor (DerivedCategory.Plus B) n).map (singleDerivedUnit P a' Z) ≫
        (P.rightDerivedFunctorPlus.commShiftIso n).inv.app
          ((DerivedCategory.Plus.singleFunctor A a').obj Z) ≫
        P.rightDerivedFunctorPlus.map
          (((DerivedCategory.Plus.singleFunctors A).shiftIso n a a' h).hom.app Z) := by
  have hu : NatTrans.CommShift (Functor.mapCochainComplexPlusDerivedUnit P) ℤ :=
    natTransCommShift_mapCochainComplexPlusDerivedUnit P
  have hD : DerivedCategory.Plus.Q.map
          (((cplusSingleFunctors B).shiftIso n a a' h).hom.app (P.obj Z)) ≫
        DerivedCategory.Plus.Q.map ((mapSinglePlus P a).app Z) =
      DerivedCategory.Plus.Q.map ((shiftFunctor (CochainComplex.Plus B) n).map
          ((mapSinglePlus P a').app Z)) ≫
        DerivedCategory.Plus.Q.map ((P.mapCochainComplexPlus.commShiftIso n).inv.app
            ((singlePlusFunctor A a').obj Z)) ≫
          DerivedCategory.Plus.Q.map (P.mapCochainComplexPlus.map
            (((cplusSingleFunctors A).shiftIso n a a' h).hom.app Z)) :=
    ((DerivedCategory.Plus.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Plus.Q.map (mapSinglePlus_comm P n a a' h Z)).trans
          (DerivedCategory.Plus.Q.map_comp _ _))).trans
      (congrArg (fun z => DerivedCategory.Plus.Q.map
          ((shiftFunctor (CochainComplex.Plus B) n).map ((mapSinglePlus P a').app Z)) ≫ z)
        (DerivedCategory.Plus.Q.map_comp _ _))
  have hCS : ((P.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).commShiftIso n).inv.app
          ((singlePlusFunctor A a').obj Z) ≫
        (Functor.mapCochainComplexPlusDerivedUnit P).app
          ((shiftFunctor (CochainComplex.Plus A) n).obj ((singlePlusFunctor A a').obj Z)) =
      (shiftFunctor (DerivedCategory.Plus B) n).map
          ((Functor.mapCochainComplexPlusDerivedUnit P).app
            ((singlePlusFunctor A a').obj Z)) ≫
        ((DerivedCategory.Plus.Q ⋙ P.rightDerivedFunctorPlus).commShiftIso n).inv.app
          ((singlePlusFunctor A a').obj Z) := by
    rw [NatTrans.app_shift, Iso.inv_hom_id_app_assoc]
  have hR : P.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.Q.commShiftIso n).inv.app ((singlePlusFunctor A a').obj Z)) ≫
        P.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
          (((cplusSingleFunctors A).shiftIso n a a' h).hom.app Z)) =
      P.rightDerivedFunctorPlus.map
        (((DerivedCategory.Plus.singleFunctors A).shiftIso n a a' h).hom.app Z) :=
    (P.rightDerivedFunctorPlus.map_comp _ _).symm.trans
      (congrArg P.rightDerivedFunctorPlus.map
        (plusSingleFunctors_shiftIso_hom_app n a a' h Z).symm)
  exact star_algebra
    (plusSingleFunctors_shiftIso_hom_app n a a' h (P.obj Z))
    hD
    (Functor.commShiftIso_inv_naturality DerivedCategory.Plus.Q
      ((mapSinglePlus P a').app Z) n).symm
    (Functor.commShiftIso_comp_inv_app P.mapCochainComplexPlus DerivedCategory.Plus.Q n
      ((singlePlusFunctor A a').obj Z)).symm
    ((Functor.mapCochainComplexPlusDerivedUnit P).naturality
      (((cplusSingleFunctors A).shiftIso n a a' h).hom.app Z))
    hCS
    (((shiftFunctor (DerivedCategory.Plus B) n).map_comp _ _).symm)
    (Functor.commShiftIso_comp_inv_app DerivedCategory.Plus.Q P.rightDerivedFunctorPlus n
      ((singlePlusFunctor A a').obj Z))
    hR

end Shift

end Stacks.DerivedIndexing

end
