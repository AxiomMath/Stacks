module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# 2-fibre products of categories over a base from lifting data

Let `(𝒞)` be a category and let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` be 1-morphisms of categories over `𝒞`
(`CategoryTheory.BasedCategory`).  A 2-commutative square `P` over that cospan is a 2-fibre
product (Stacks 003Q) as soon as two lifting conditions hold:

* *arrow lifting*: a pair of morphisms of the two legs lying over one morphism of `𝒞` comes from
  a morphism of the apex; and
* *object lifting*: every object of every other 2-commutative square over the cospan is matched,
  compatibly with both legs and vertically, by an object of `P`'s apex.

Together with faithfulness of the first projection of `P` and of the structure functor of `𝒵`
they give the universal property: faithfulness of `P.fst` makes the lift of a pair of morphisms
unique, so the lifts assemble into a functor and a 1-morphism; faithfulness of the structure
functor of `𝒵` makes the compatibility 2-cell of a morphism of squares automatic, and makes the
comparison of two such morphisms unique.

## Main definitions

* `CategoryTheory.Bicategory.SquareLiftedObject`: the object-lifting datum.
* `CategoryTheory.Bicategory.squareLiftMap`, `CategoryTheory.Bicategory.squareLiftIso` and
  `CategoryTheory.Bicategory.squareLiftNatIso`: the morphism, the isomorphism and the 2-morphism
  to the apex that arrow lifting supplies.
* `CategoryTheory.Bicategory.squareLiftFunctor` and
  `CategoryTheory.Bicategory.squareLiftOneHom`: the functor and the 1-morphism to the apex that
  object and arrow lifting supply.

## Main results

* `CategoryTheory.Bicategory.twoHom_ext_of_faithful`: 2-morphisms into a category over `𝒞`
  whose structure functor is faithful are unique.
* `CategoryTheory.Bicategory.squareIsTerminal`: **object lifting and arrow lifting make a
  2-commutative square a 2-fibre product.**

## Implementation notes

The 2-category of categories over `𝒞` is strict: its associator and unitors are identity
2-morphisms (`CategoryTheory.BasedCategory.bicategory`).  That is why no associator appears
below, and why the compatibility square of a morphism of 2-commutative squares reduces to an
equation between two 2-morphisms into `𝒵`, which faithfulness of its structure functor settles
outright.

Everything is stated for the hom-universes of `CategoryTheory.BasedCategory` taken equal, which
is the generality in which the 2-category is a bicategory at all.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- 2-cells into a based category whose structure functor is faithful are unique. -/
theorem twoHom_ext_of_faithful {A Z : BasedCategory.{w, w} 𝒞} [Z.p.Faithful]
    {F G : A ⥤ᵇ Z} (α β : F ⟶ G) : α = β := by
  refine BasedNatTrans.ext α β ?_
  ext a
  refine Z.p.map_injective ?_
  rw [IsHomLift.fac' Z.p (𝟙 (A.p.obj a)) (α.toNatTrans.app a),
    IsHomLift.fac' Z.p (𝟙 (A.p.obj a)) (β.toNatTrans.app a)]

/-- The underlying natural isomorphism of a 2-isomorphism of based functors. -/
abbrev basedNatIso {A D : BasedCategory.{w, w} 𝒞} {F G : A ⥤ᵇ D} (e : F ≅ G) :
    F.toFunctor ≅ G.toFunctor :=
  (BasedNatTrans.forgetful A D).mapIso e

variable {X Y Z : BasedCategory.{w, w} 𝒞} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- A lift of an object of a 2-commutative square to the apex of another. -/
structure SquareLiftedObject (P : TwoCommSq f g) (T : TwoCommSq f g) (a : T.pt.obj) where
  /-- the lifted object -/
  obj : P.pt.obj
  /-- comparison of its first projection -/
  fstIso : P.fst.obj obj ≅ T.fst.obj a
  /-- comparison of its second projection -/
  sndIso : P.snd.obj obj ≅ T.snd.obj a
  /-- the first comparison is vertical -/
  fst_vertical : X.p.IsHomLift (𝟙 (T.pt.p.obj a)) fstIso.hom
  /-- the second comparison is vertical -/
  snd_vertical : Y.p.IsHomLift (𝟙 (T.pt.p.obj a)) sndIso.hom

variable (P : TwoCommSq f g)
  (hlift : ∀ {a b : P.pt.obj} (s : P.fst.obj a ⟶ P.fst.obj b) (t : P.snd.obj a ⟶ P.snd.obj b)
    {U V : 𝒞} (j : U ⟶ V), X.p.IsHomLift j s → Y.p.IsHomLift j t →
    ∃ k : a ⟶ b, P.fst.map k = s ∧ P.snd.map k = t)

/-- The morphism of the apex that arrow lifting supplies. -/
def squareLiftMap {a b : P.pt.obj} (s : P.fst.obj a ⟶ P.fst.obj b)
    (t : P.snd.obj a ⟶ P.snd.obj b) {U V : 𝒞} (j : U ⟶ V)
    (hs : X.p.IsHomLift j s) (ht : Y.p.IsHomLift j t) : a ⟶ b :=
  (hlift s t j hs ht).choose

/-- The first leg maps `squareLiftMap` to the given morphism `s`. -/
theorem squareLiftMap_fst {a b : P.pt.obj} (s : P.fst.obj a ⟶ P.fst.obj b)
    (t : P.snd.obj a ⟶ P.snd.obj b) {U V : 𝒞} (j : U ⟶ V)
    (hs : X.p.IsHomLift j s) (ht : Y.p.IsHomLift j t) :
    P.fst.map (squareLiftMap P hlift s t j hs ht) = s :=
  (hlift s t j hs ht).choose_spec.1

/-- The second leg maps `squareLiftMap` to the given morphism `t`. -/
theorem squareLiftMap_snd {a b : P.pt.obj} (s : P.fst.obj a ⟶ P.fst.obj b)
    (t : P.snd.obj a ⟶ P.snd.obj b) {U V : 𝒞} (j : U ⟶ V)
    (hs : X.p.IsHomLift j s) (ht : Y.p.IsHomLift j t) :
    P.snd.map (squareLiftMap P hlift s t j hs ht) = t :=
  (hlift s t j hs ht).choose_spec.2

variable [P.fst.toFunctor.Faithful]

/-- The isomorphism of the apex that arrow lifting supplies. -/
def squareLiftIso {a b : P.pt.obj} (s : P.fst.obj a ≅ P.fst.obj b)
    (t : P.snd.obj a ≅ P.snd.obj b) {U : 𝒞} (hs : X.p.IsHomLift (𝟙 U) s.hom)
    (ht : Y.p.IsHomLift (𝟙 U) t.hom) : a ≅ b := by
  have := hs
  have := ht
  refine ⟨squareLiftMap P hlift s.hom t.hom (𝟙 U) hs ht,
    squareLiftMap P hlift s.inv t.inv (𝟙 U) (by infer_instance) (by infer_instance), ?_, ?_⟩
  all_goals apply P.fst.toFunctor.map_injective
  all_goals simp only [Functor.map_comp, squareLiftMap_fst]
  · exact s.hom_inv_id.trans (P.fst.toFunctor.map_id a).symm
  · exact s.inv_hom_id.trans (P.fst.toFunctor.map_id b).symm

/-- **A 2-isomorphism into the apex from 2-isomorphisms of the two legs.** -/
def squareLiftNatIso {T : BasedCategory.{w, w} 𝒞} {F G : T ⥤ᵇ P.pt}
    (s : F ≫ P.fst ≅ G ≫ P.fst) (t : F ≫ P.snd ≅ G ≫ P.snd) : F ≅ G := by
  let e : F.toFunctor ≅ G.toFunctor := NatIso.ofComponents
    (fun a => squareLiftIso P hlift ((basedNatIso s).app a) ((basedNatIso t).app a)
      (s.hom.isHomLift' a) (t.hom.isHomLift' a))
    (by
      intro a b j
      apply P.fst.toFunctor.map_injective
      have h1 := squareLiftMap_fst P hlift ((basedNatIso s).app b).hom
        ((basedNatIso t).app b).hom (𝟙 (T.p.obj b)) (s.hom.isHomLift' b) (t.hom.isHomLift' b)
      have h2 := squareLiftMap_fst P hlift ((basedNatIso s).app a).hom
        ((basedNatIso t).app a).hom (𝟙 (T.p.obj a)) (s.hom.isHomLift' a) (t.hom.isHomLift' a)
      simp only [Functor.map_comp, squareLiftIso]
      rw [h1, h2]
      exact (basedNatIso s).hom.naturality j)
  refine BasedNatIso.mkNatIso e (fun a => ?_)
  apply (BasedFunctor.isHomLift_iff P.fst _ _).mp
  have h2 := squareLiftMap_fst P hlift ((basedNatIso s).app a).hom
    ((basedNatIso t).app a).hom (𝟙 (T.p.obj a)) (s.hom.isHomLift' a) (t.hom.isHomLift' a)
  rw [show e.hom.app a = squareLiftMap P hlift ((basedNatIso s).app a).hom
    ((basedNatIso t).app a).hom (𝟙 (T.p.obj a)) (s.hom.isHomLift' a)
    (t.hom.isHomLift' a) from rfl, h2]
  exact s.hom.isHomLift' a

/-- Whiskering `squareLiftNatIso` with the first leg recovers the 2-isomorphism `s`. -/
theorem squareLiftNatIso_fst {T : BasedCategory.{w, w} 𝒞} {F G : T ⥤ᵇ P.pt}
    (s : F ≫ P.fst ≅ G ≫ P.fst) (t : F ≫ P.snd ≅ G ≫ P.snd) :
    (squareLiftNatIso P hlift s t).hom ▷ P.fst = s.hom := by
  refine BasedNatTrans.ext _ _ ?_
  ext a
  exact squareLiftMap_fst P hlift ((basedNatIso s).app a).hom ((basedNatIso t).app a).hom
    (𝟙 (T.p.obj a)) (s.hom.isHomLift' a) (t.hom.isHomLift' a)

/-- Whiskering `squareLiftNatIso` with the second leg recovers the 2-isomorphism `t`. -/
theorem squareLiftNatIso_snd {T : BasedCategory.{w, w} 𝒞} {F G : T ⥤ᵇ P.pt}
    (s : F ≫ P.fst ≅ G ≫ P.fst) (t : F ≫ P.snd ≅ G ≫ P.snd) :
    (squareLiftNatIso P hlift s t).hom ▷ P.snd = t.hom := by
  refine BasedNatTrans.ext _ _ ?_
  ext a
  exact squareLiftMap_snd P hlift ((basedNatIso s).app a).hom ((basedNatIso t).app a).hom
    (𝟙 (T.p.obj a)) (s.hom.isHomLift' a) (t.hom.isHomLift' a)

variable (T : TwoCommSq f g) (O : (a : T.pt.obj) → SquareLiftedObject P T a)

/-- The comparison of the first legs over a morphism. -/
abbrev liftFstHom {a b : T.pt.obj} (j : a ⟶ b) :
    P.fst.obj (O a).obj ⟶ P.fst.obj (O b).obj :=
  (O a).fstIso.hom ≫ T.fst.map j ≫ (O b).fstIso.inv

/-- The comparison of the second legs over a morphism. -/
abbrev liftSndHom {a b : T.pt.obj} (j : a ⟶ b) :
    P.snd.obj (O a).obj ⟶ P.snd.obj (O b).obj :=
  (O a).sndIso.hom ≫ T.snd.map j ≫ (O b).sndIso.inv

/-- Conjugating the image of `j` by vertical isomorphisms gives a lift of the image of `j`. -/
private theorem isHomLift_vertical_conj {A R : BasedCategory.{w, w} 𝒞} (F : A ⥤ᵇ R)
    {a b : A.obj} (j : a ⟶ b) {x y : R.obj} (u : x ≅ F.obj a) (v : y ≅ F.obj b)
    (hu : R.p.IsHomLift (𝟙 (A.p.obj a)) u.hom) (hv : R.p.IsHomLift (𝟙 (A.p.obj b)) v.hom) :
    R.p.IsHomLift (A.p.map j) (u.hom ≫ F.map j ≫ v.inv) := by
  have := F.preserves_isHomLift (A.p.map j) j
  simpa using (inferInstance : R.p.IsHomLift (𝟙 _ ≫ A.p.map j ≫ 𝟙 _) (u.hom ≫ F.map j ≫ v.inv))

omit [P.fst.toFunctor.Faithful] in
/-- The comparison `liftFstHom` of the first legs over `j` lies over the image of `j` in `𝒞`. -/
theorem liftFstHom_isHomLift {a b : T.pt.obj} (j : a ⟶ b) :
    X.p.IsHomLift (T.pt.p.map j) (liftFstHom P T O j) :=
  isHomLift_vertical_conj T.fst j _ _ (O a).fst_vertical (O b).fst_vertical

omit [P.fst.toFunctor.Faithful] in
/-- The comparison `liftSndHom` of the second legs over `j` lies over the image of `j` in `𝒞`. -/
theorem liftSndHom_isHomLift {a b : T.pt.obj} (j : a ⟶ b) :
    Y.p.IsHomLift (T.pt.p.map j) (liftSndHom P T O j) :=
  isHomLift_vertical_conj T.snd j _ _ (O a).snd_vertical (O b).snd_vertical

/-- **The functor to the apex that object and arrow lifting supply.** -/
def squareLiftFunctor : T.pt.obj ⥤ P.pt.obj where
  obj a := (O a).obj
  map {a b} j := squareLiftMap P hlift (liftFstHom P T O j) (liftSndHom P T O j)
    (T.pt.p.map j) (liftFstHom_isHomLift P T O j) (liftSndHom_isHomLift P T O j)
  map_id a := by
    apply P.fst.toFunctor.map_injective
    rw [squareLiftMap_fst]
    simp [liftFstHom]
  map_comp {a b c} j k := by
    apply P.fst.toFunctor.map_injective
    rw [squareLiftMap_fst, P.fst.toFunctor.map_comp, squareLiftMap_fst, squareLiftMap_fst]
    simp [liftFstHom]

/-- **The functor to the apex lies over the base.** -/
theorem squareLiftFunctor_over : squareLiftFunctor P hlift T O ⋙ P.pt.p = T.pt.p := by
  have hobj : ∀ a, P.pt.p.obj ((O a).obj) = T.pt.p.obj a := fun a => by
    have := (O a).fst_vertical
    exact (P.fst.w_obj _).symm.trans (IsHomLift.domain_eq X.p (𝟙 _) (O a).fstIso.hom)
  refine CategoryTheory.Functor.ext hobj (fun a b j => ?_)
  have hs : X.p.IsHomLift (T.pt.p.map j) (P.fst.map ((squareLiftFunctor P hlift T O).map j)) := by
    show X.p.IsHomLift (T.pt.p.map j) (P.fst.map (squareLiftMap P hlift
      (liftFstHom P T O j) (liftSndHom P T O j) (T.pt.p.map j)
      (liftFstHom_isHomLift P T O j) (liftSndHom_isHomLift P T O j)))
    rw [squareLiftMap_fst]
    exact liftFstHom_isHomLift P T O j
  have := BasedFunctor.isHomLift_map P.fst (T.pt.p.map j) ((squareLiftFunctor P hlift T O).map j)
  simpa using IsHomLift.fac' P.pt.p (T.pt.p.map j) ((squareLiftFunctor P hlift T O).map j)

/-- **The 1-morphism to the apex that object and arrow lifting supply.** -/
def squareLiftOneHom : T.pt ⟶ P.pt where
  toFunctor := squareLiftFunctor P hlift T O
  w := squareLiftFunctor_over P hlift T O

/-- Its comparison with the first leg. -/
def squareLiftFstIso : squareLiftOneHom P hlift T O ≫ P.fst ≅ T.fst := by
  refine BasedNatIso.mkNatIso (NatIso.ofComponents (fun a => (O a).fstIso) (fun {a b} j => ?_))
    (fun a => (O a).fst_vertical)
  change P.fst.map (squareLiftMap P hlift (liftFstHom P T O j) (liftSndHom P T O j)
    (T.pt.p.map j) (liftFstHom_isHomLift P T O j) (liftSndHom_isHomLift P T O j)) ≫
      (O b).fstIso.hom = (O a).fstIso.hom ≫ T.fst.map j
  rw [squareLiftMap_fst]
  simp [liftFstHom]

/-- Its comparison with the second leg. -/
def squareLiftSndIso : squareLiftOneHom P hlift T O ≫ P.snd ≅ T.snd := by
  refine BasedNatIso.mkNatIso (NatIso.ofComponents (fun a => (O a).sndIso) (fun {a b} j => ?_))
    (fun a => (O a).snd_vertical)
  change P.snd.map (squareLiftMap P hlift (liftFstHom P T O j) (liftSndHom P T O j)
    (T.pt.p.map j) (liftFstHom_isHomLift P T O j) (liftSndHom_isHomLift P T O j)) ≫
      (O b).sndIso.hom = (O a).sndIso.hom ≫ T.snd.map j
  rw [squareLiftMap_snd]
  simp [liftSndHom]

/-- The resulting morphism of 2-commutative squares. -/
def squareLiftPreHom [Z.p.Faithful] : TwoCommSq.PreHom T P where
  hom := squareLiftOneHom P hlift T O
  isoFst := (squareLiftFstIso P hlift T O).symm
  isoSnd := (squareLiftSndIso P hlift T O).symm
  compat := twoHom_ext_of_faithful _ _

/-- **Object lifting and arrow lifting make a 2-commutative square a 2-fibre product.** -/
def squareIsTerminal [Z.p.Faithful]
    (objects : ∀ (T : TwoCommSq f g) (a : T.pt.obj), SquareLiftedObject P T a) :
    IsTwoFibreProduct P := by
  refine IsTerminal.ofUniqueHom
    (fun T => _root_.Quotient.mk (TwoCommSq.PreHom.setoid T P)
      (squareLiftPreHom P hlift T (objects T))) (fun T h => ?_)
  refine _root_.Quotient.inductionOn h (fun H => ?_)
  refine _root_.Quotient.sound (show TwoCommSq.PreHom.Rel H
    (squareLiftPreHom P hlift T (objects T)) from ⟨squareLiftNatIso P hlift
      (H.isoFst.symm ≪≫ (squareLiftPreHom P hlift T (objects T)).isoFst)
      (H.isoSnd.symm ≪≫ (squareLiftPreHom P hlift T (objects T)).isoSnd), ?_, ?_⟩)
  · rw [squareLiftNatIso_fst]
    simp
  · rw [squareLiftNatIso_snd]
    simp

end CategoryTheory.Bicategory

end
