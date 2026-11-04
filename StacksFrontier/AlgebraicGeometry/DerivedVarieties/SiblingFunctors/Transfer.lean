module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.EssentialImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Support.BoundedTriangle
public import StacksCore.Tactic.StacksAttribute

/-!
# Properties shared by sibling functors

Essential surjectivity and full faithfulness pass from one sibling exact functor out of a bounded
derived category to the other. Essential surjectivity is immediate from the objectwise
isomorphisms. Full faithfulness is not: the proof factors the second functor through the first,
obtaining a sibling of the identity, shows that such an endofunctor acts as the identity on every
Ext group of the heart by Yoneda extensions, and propagates that bijectivity to all bounded
objects by induction over distinguished triangles.

## Main results

* `AlgebraicGeometry.essSurj_of_areSiblings`: essential surjectivity transfers between siblings.
* `AlgebraicGeometry.fullyFaithful_of_areSiblings`: full faithfulness transfers between siblings.

## Implementation notes

The two independent conclusions of the source lemma are stated separately. Full faithfulness is
expressed as the inhabited standard `CategoryTheory.Functor.FullyFaithful` structure.

The Yoneda-extension argument cuts an extension of degree `n + 2` at its left end into a short
exact sequence and an extension of degree `n + 1`; the resulting induction is
`AlgebraicGeometry.ext_operation_eq_id`.

## References

* [Stacks Project, Tag 0FZV](https://stacks.math.columbia.edu/tag/0FZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v v' u u'

namespace AlgebraicGeometry

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
  {F F' : DerivedCategory.Bounded A ⥤ D}
  [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]

/-- The two restrictions to the heart have the same full-faithfulness behaviour. -/
private lemma boundedSingle_fullyFaithful :
    Nonempty (boundedSingleFunctor A).FullyFaithful := by
  have hsingle : (DerivedCategory.singleFunctor A 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  have hcomp :
      (boundedSingleFunctor A ⋙ DerivedCategory.Bounded.ι).FullyFaithful :=
    Functor.FullyFaithful.ofIso hsingle (boundedSingleFunctorCompιIso A)
  exact ⟨Functor.FullyFaithful.ofCompFaithful hcomp⟩

/-- The restriction of a sibling of a fully faithful functor to the heart is fully faithful. -/
private lemma boundedSingle_comp_fullyFaithful_of_areSiblings
    (h : AreSiblings F F') (hF : Nonempty F.FullyFaithful) :
    Nonempty (boundedSingleFunctor A ⋙ F').FullyFaithful := by
  obtain ⟨e⟩ := h.restrictionIso
  obtain ⟨hF⟩ := hF
  obtain ⟨hA⟩ := boundedSingle_fullyFaithful (A := A)
  exact ⟨Functor.FullyFaithful.ofIso (hA.comp hF) e⟩

/-- A sibling functor factors through the essential image of a fully faithful functor. -/
private noncomputable def liftSibling (h : AreSiblings F F')
    (hF : Nonempty F.FullyFaithful) : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A := by
  letI := (Classical.choice hF).full
  letI := (Classical.choice hF).faithful
  exact Functor.essImage.liftFunctor F' F fun K ↦ ⟨K, h.objIso K⟩

/-- The factorization of `F'` through `F` has the expected composite. -/
private noncomputable def liftSiblingCompIso (h : AreSiblings F F')
    (hF : Nonempty F.FullyFaithful) : liftSibling h hF ⋙ F ≅ F' := by
  letI := (Classical.choice hF).full
  letI := (Classical.choice hF).faithful
  exact Functor.essImage.liftFunctorCompIso F' F fun K ↦ ⟨K, h.objIso K⟩

/-- The lifted functor is objectwise isomorphic to the identity. -/
private noncomputable def liftSiblingObjIso (h : AreSiblings F F')
    (hF : Nonempty F.FullyFaithful) (K : DerivedCategory.Bounded A) :
    (liftSibling h hF).obj K ≅ K :=
  (Classical.choice hF).preimageIso
    ((liftSiblingCompIso h hF).app K ≪≫ (Classical.choice (h.objIso K)).symm)

@[instance_reducible]
private noncomputable def liftSiblingCommShift (h : AreSiblings F F')
    (hF : Nonempty F.FullyFaithful) : (liftSibling h hF).CommShift ℤ := by
  letI : F.Full := (Classical.choice hF).full
  letI : F.Faithful := (Classical.choice hF).faithful
  exact Functor.CommShift.ofComp (liftSiblingCompIso h hF) ℤ

/-- After lifting through a fully faithful sibling, the resulting endofunctor is a sibling of
the identity. -/
private lemma liftSibling_areSiblings (h : AreSiblings F F')
    (hF : Nonempty F.FullyFaithful)
    [((liftSibling h hF)).CommShift ℤ] [((liftSibling h hF)).IsTriangulated] :
    AreSiblings (𝟭 (DerivedCategory.Bounded A)) (liftSibling h hF) := by
  let : F.Full := (Classical.choice hF).full
  let : F.Faithful := (Classical.choice hF).faithful
  refine ⟨?_, fun K ↦ ⟨(liftSiblingObjIso h hF K).symm⟩⟩
  let b := boundedSingleFunctor A
  have eId : (b ⋙ 𝟭 (DerivedCategory.Bounded A)) ⋙ F ≅ b ⋙ F :=
    Functor.associator b (𝟭 (DerivedCategory.Bounded A)) F ≪≫
      Functor.isoWhiskerLeft b (Functor.leftUnitor F)
  have eLift : (b ⋙ liftSibling h hF) ⋙ F ≅ b ⋙ F' :=
    Functor.associator b (liftSibling h hF) F ≪≫
      Functor.isoWhiskerLeft b (liftSiblingCompIso h hF)
  obtain ⟨e⟩ := h.restrictionIso
  exact ⟨Functor.fullyFaithfulCancelRight F (eId ≪≫ e ≪≫ eLift.symm)⟩

/-- The lift of a sibling endofunctor to the abelian heart. -/
private noncomputable def liftSiblingHeart (H : DerivedCategory.Bounded A ⥤
    DerivedCategory.Bounded A) (e : boundedSingleFunctor A ⋙ H ≅
      boundedSingleFunctor A) : A ⥤ A := by
  let b := boundedSingleFunctor A
  let hB := Classical.choice (boundedSingle_fullyFaithful (A := A))
  letI : b.Full := hB.full
  letI : b.Faithful := hB.faithful
  exact Functor.essImage.liftFunctor (b ⋙ H) b fun X ↦ ⟨X, ⟨(e.app X).symm⟩⟩

/-- The heart lift followed by the bounded inclusion is the original restriction. -/
private noncomputable def liftSiblingHeartCompIso
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A) :
    liftSiblingHeart H e ⋙ boundedSingleFunctor A ≅
      boundedSingleFunctor A ⋙ H := by
  let b := boundedSingleFunctor A
  let hB := Classical.choice (boundedSingle_fullyFaithful (A := A))
  letI : b.Full := hB.full
  letI : b.Faithful := hB.faithful
  exact Functor.essImage.liftFunctorCompIso (b ⋙ H) b fun X ↦ ⟨X, ⟨(e.app X).symm⟩⟩

/-- The lifted endofunctor on the heart is naturally isomorphic to the identity. -/
private noncomputable def liftSiblingHeartIsoId
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A) :
    liftSiblingHeart H e ≅ 𝟭 A := by
  let b := boundedSingleFunctor A
  let hB := Classical.choice (boundedSingle_fullyFaithful (A := A))
  letI : b.Full := hB.full
  letI : b.Faithful := hB.faithful
  exact Functor.fullyFaithfulCancelRight b
    (liftSiblingHeartCompIso H e ≪≫ e ≪≫ (Functor.leftUnitor b).symm)

/-- Epimorphisms can be cancelled inside the image of a fully faithful functor. -/
private lemma cancel_map_epi {C E : Type*} [Category* C] [Category* E]
    (b : C ⥤ E) [b.Full] [b.Faithful] {X Y Z : C} (g : X ⟶ Y) [Epi g]
    {u v : b.obj Y ⟶ b.obj Z} (h : b.map g ≫ u = b.map g ≫ v) : u = v := by
  obtain ⟨u, rfl⟩ := b.map_surjective u
  obtain ⟨v, rfl⟩ := b.map_surjective v
  exact congrArg b.map ((cancel_epi g).1 (b.map_injective (by simpa using h)))

/-- The last square of a triangle on heart objects is forced by the first two squares. -/
private lemma triangle_mor₃_naturality
    {C E B : Type*} [Category* C] [Category* E] [Category* B]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (b : B ⥤ C) (b' : B ⥤ E) [b'.Full] [b'.Faithful]
    (G : C ⥤ E) [G.CommShift ℤ] [G.IsTriangulated]
    (e : b ⋙ G ≅ b') {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi g]
    (δ : b.obj Z ⟶ (b.obj X)⟦(1 : ℤ)⟧)
    (δ' : b'.obj Z ⟶ (b'.obj X)⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk (b.map f) (b.map g) δ ∈
      distTriang C)
    (hT' : Pretriangulated.Triangle.mk (b'.map f) (b'.map g) δ' ∈
      distTriang E) :
    G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app (b.obj X) ≫
      (e.hom.app X)⟦(1 : ℤ)⟧' = e.hom.app Z ≫ δ' := by
  obtain ⟨c, hc, hc'⟩ := Pretriangulated.complete_distinguished_triangle_morphism
    _ _ (G.map_distinguished _ hT) hT' (e.hom.app X) (e.hom.app Y)
    (e.hom.naturality f)
  dsimp only [Functor.mapTriangle, Triangle.mk_obj₁, Triangle.mk_obj₃,
    Triangle.mk_mor₂, Triangle.mk_mor₃] at c hc hc'
  have hc₀ : e.inv.app Z ≫ c = 𝟙 (b'.obj Z) := by
    apply cancel_map_epi b' g
    rw [Category.comp_id, ← Category.assoc, e.inv.naturality g, Category.assoc]
    show e.inv.app Y ≫ (G.map (b.map g) ≫ c) = _
    rw [hc]
    simp
  have hc₁ : c = e.hom.app Z := by
    simpa using congrArg (fun k => e.hom.app Z ≫ k) hc₀
  simpa only [Functor.mapTriangle, Pretriangulated.Triangle.mk_mor₃,
    Pretriangulated.Triangle.mk_obj₁, hc₁, Category.assoc] using hc'

/-- The connecting morphism of a short exact sequence in the bounded derived category. -/
public noncomputable def boundedSingleδ {S : ShortComplex A} (hS : S.ShortExact) :
    (boundedSingleFunctor A).obj S.X₃ ⟶
      ((boundedSingleFunctor A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk (hS.singleδ ≫
    (DerivedCategory.Bounded.ι.commShiftIso (1 : ℤ)).inv.app
      ((boundedSingleFunctor A).obj S.X₁))

/-- The triangle of degree-zero objects attached to a short exact sequence is distinguished in the
bounded derived category. -/
public lemma boundedSingleTriangle_distinguished {S : ShortComplex A} (hS : S.ShortExact) :
    Pretriangulated.Triangle.mk ((boundedSingleFunctor A).map S.f)
      ((boundedSingleFunctor A).map S.g) (boundedSingleδ hS) ∈
      distTriang (DerivedCategory.Bounded A) := by
  apply (DerivedCategory.Bounded.ι.map_distinguished_iff _).1
  convert hS.singleTriangle_distinguished using 1
  simp [Functor.mapTriangle, boundedSingleδ, ShortComplex.ShortExact.singleTriangle,
    boundedSingleFunctor, ObjectProperty.lift]

/-- An exact endofunctor agreeing with the identity on the heart respects the connecting morphism
of a short exact sequence. -/
private lemma map_boundedSingleδ
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    [H.CommShift ℤ] [H.IsTriangulated]
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A)
    {S : ShortComplex A} (hS : S.ShortExact) :
    H.map (boundedSingleδ hS) ≫
      (H.commShiftIso (1 : ℤ)).hom.app ((boundedSingleFunctor A).obj S.X₁) ≫
      (e.hom.app S.X₁)⟦(1 : ℤ)⟧' = e.hom.app S.X₃ ≫ boundedSingleδ hS := by
  have := hS.epi_g
  let hb := Classical.choice (boundedSingle_fullyFaithful (A := A))
  let := hb.full
  let := hb.faithful
  exact triangle_mor₃_naturality _ _ H e S.f S.g _ _
    (boundedSingleTriangle_distinguished hS) (boundedSingleTriangle_distinguished hS)

section YonedaComparison

open Abelian ComposableArrows

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- An operation on positive Ext groups fixing extension classes and their products is
the identity: it agrees with the class map of Yoneda extensions on the two properties which
pin that map down, hence equals it, and every positive Ext class is such a class. -/
private lemma ext_operation_eq_id [HasExt.{w} 𝒜]
    (φ : ∀ {X Y : 𝒜} {n : ℕ}, Ext.{w} X Y n → Ext.{w} X Y n)
    (hδ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact), φ hS.extClass = hS.extClass)
    (hcomp : ∀ {X Y Z : 𝒜} {n : ℕ} (α : Ext.{w} X Y n) (β : Ext.{w} Y Z 1),
      φ (α.comp β rfl) = (φ α).comp (φ β) rfl)
    {X Y : 𝒜} {n : ℕ} (α : Ext.{w} X Y (n + 1)) : φ α = α := by
  have hmap : IsExtClassMap
      (fun (_ _ : 𝒜) (m : ℕ) (E : YonedaExtension _ _ m) => φ (extClassMap.{w} m E)) := by
    refine ⟨fun B A E h hS => ?_, fun B A C m E E' p h hS ψ w₁ w₂ => ?_⟩
    · have h0 : extClassMap.{w} 0 E = hS.extClass :=
        isExtClassMap_extClassMap.1 B A E h hS
      show φ (extClassMap.{w} 0 E) = hS.extClass
      rw [h0, hδ]
    · have h1 : extClassMap.{w} (m + 1) E = (extClassMap.{w} m E').comp hS.extClass rfl :=
        isExtClassMap_extClassMap.2 B A C m E E' p h hS ψ w₁ w₂
      show φ (extClassMap.{w} (m + 1) E) =
        (φ (extClassMap.{w} m E')).comp hS.extClass rfl
      rw [h1, hcomp, hδ]
  have hφ := eq_extClassMap_of_isExtClassMap _ hmap
  obtain ⟨E, rfl⟩ := surjective_extClassMap X Y n α
  exact congrFun (congrFun (congrFun (congrFun hφ X) Y) n) E

end YonedaComparison

/-- Bijectivity transfers along equivalences intertwining two maps. -/
private lemma bijective_of_equiv_comm {α α' β β' : Sort*} (p : α ≃ α') (q : β ≃ β')
    (f : α → β) (f' : α' → β') (hc : ∀ a, f' (p a) = q (f a)) (h : Function.Bijective f) :
    Function.Bijective f' := by
  have : f' = q ∘ f ∘ p.symm := funext fun a => by simpa using hc (p.symm a)
  rw [this]
  exact q.bijective.comp (h.comp p.symm.bijective)

section ExtComparison


open Abelian

/-- The Ext group between two objects of the heart, identified with the corresponding shifted Hom
group in the bounded derived category. -/
private noncomputable def boundedExtEquiv [HasExt.{w} A] {X Y : A} {n : ℕ} :
    Ext.{w} X Y n ≃ ShiftedHom ((boundedSingleFunctor A).obj X)
      ((boundedSingleFunctor A).obj Y) (n : ℤ) where
  toFun α := ObjectProperty.homMk (α.hom ≫
    (DerivedCategory.Bounded.ι.commShiftIso (n : ℤ)).inv.app
      ((boundedSingleFunctor A).obj Y))
  invFun f := Ext.homEquiv.symm (f.hom ≫
    (DerivedCategory.Bounded.ι.commShiftIso (n : ℤ)).hom.app
      ((boundedSingleFunctor A).obj Y))
  left_inv α := by simp [boundedSingleFunctor, ObjectProperty.lift]
  right_inv f := by
    apply ObjectProperty.hom_ext
    simp

/-- Pushing a shifted Hom class forward along the inclusion of the bounded derived category
recovers the underlying map of the Ext class. -/
private lemma boundedExtEquiv_map [HasExt.{w} A] {X Y : A} {n : ℕ}
    (α : Ext.{w} X Y n) : (boundedExtEquiv α).map DerivedCategory.Bounded.ι = α.hom := by
  simp [boundedExtEquiv, ShiftedHom.map, boundedSingleFunctor, ObjectProperty.lift]

/-- A faithful functor commuting with the shift is injective on shifted Hom groups. -/
private lemma shiftedHom_map_injective {C E : Type*} [Category* C] [Category* E]
    [HasShift C ℤ] [HasShift E ℤ] (G : C ⥤ E) [G.CommShift ℤ] [G.Faithful]
    {X Y : C} {n : ℤ} : Function.Injective (ShiftedHom.map (X := X) (Y := Y) (a := n) · G) := by
  intro f g h
  apply G.map_injective
  exact (cancel_mono ((G.commShiftIso n).hom.app Y)).1 h

/-- The identification of Ext groups with shifted Hom groups is compatible with composition. -/
private lemma boundedExtEquiv_comp [HasExt.{w} A] {X Y Z : A} {a b c : ℕ}
    (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b) (h : a + b = c) :
    boundedExtEquiv (α.comp β h) =
      (boundedExtEquiv α).comp (boundedExtEquiv β) (by omega) := by
  apply shiftedHom_map_injective DerivedCategory.Bounded.ι
  dsimp only
  rw [boundedExtEquiv_map, ShiftedHom.map_comp, boundedExtEquiv_map, boundedExtEquiv_map]
  exact Ext.comp_hom α β h

/-- The identification of Ext groups with shifted Hom groups sends the class of a short exact
sequence to its connecting morphism. -/
private lemma boundedExtEquiv_extClass [HasExt.{w} A] {S : ShortComplex A}
    (hS : S.ShortExact) : boundedExtEquiv hS.extClass = boundedSingleδ hS := by
  apply ObjectProperty.hom_ext
  simp [boundedExtEquiv, boundedSingleδ]

/-- Conjugating two shifted morphisms by isomorphisms of their sources and targets is compatible
with their composition. -/
private lemma conjugate_shiftedHom_comp {C : Type*} [Category* C] [HasShift C ℤ]
    {X Y Z X' Y' Z' : C} (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z')
    {a b c : ℤ} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    ShiftedHom.comp (eX.inv ≫ α ≫ eY.hom⟦a⟧') (eY.inv ≫ β ≫ eZ.hom⟦b⟧') h =
      eX.inv ≫ (α.comp β h) ≫ eZ.hom⟦c⟧' := by
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, eY.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  congr 3
  exact (shiftFunctorAdd' C b a c h).inv.naturality eZ.hom

/-- The operation on Ext groups induced by a sibling of the identity. -/
private noncomputable def siblingExtMap [HasExt.{w} A]
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A) [H.CommShift ℤ]
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A)
    {X Y : A} {n : ℕ} (α : Ext.{w} X Y n) : Ext.{w} X Y n :=
  boundedExtEquiv.symm (e.inv.app X ≫ (boundedExtEquiv α).map H ≫ (e.hom.app Y)⟦(n : ℤ)⟧')

/-- The induced operation on Ext groups fixes the class of every short exact sequence. -/
private lemma siblingExtMap_extClass [HasExt.{w} A]
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    [H.CommShift ℤ] [H.IsTriangulated]
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A)
    {S : ShortComplex A} (hS : S.ShortExact) :
    siblingExtMap H e hS.extClass = hS.extClass := by
  apply boundedExtEquiv.injective
  simp only [siblingExtMap, Equiv.apply_symm_apply, boundedExtEquiv_extClass]
  dsimp only [ShiftedHom.map]
  have hh := congrArg (fun f => e.inv.app S.X₃ ≫ f) (map_boundedSingleδ H e hS)
  simp only [Iso.inv_hom_id_app_assoc] at hh
  convert! hh using 1
  simp [Category.assoc]

/-- The induced operation on Ext groups respects composition. -/
private lemma siblingExtMap_comp [HasExt.{w} A]
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A) [H.CommShift ℤ]
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A)
    {X Y Z : A} {a b c : ℕ} (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b)
    (h : a + b = c) : siblingExtMap H e (α.comp β h) =
      (siblingExtMap H e α).comp (siblingExtMap H e β) h := by
  apply boundedExtEquiv.injective
  simp only [siblingExtMap, Equiv.apply_symm_apply, boundedExtEquiv_comp, ShiftedHom.map_comp]
  exact (conjugate_shiftedHom_comp (e.app X) (e.app Y) (e.app Z) _ _ _).symm

/-- The induced operation on positive Ext groups is the identity. -/
private lemma siblingExtMap_eq_id [HasExt.{w} A]
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    [H.CommShift ℤ] [H.IsTriangulated]
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A)
    {X Y : A} {n : ℕ} (α : Ext.{w} X Y (n + 1)) : siblingExtMap H e α = α :=
  ext_operation_eq_id (fun α => siblingExtMap H e α)
    (fun _ hS => siblingExtMap_extClass H e hS) (fun α β => siblingExtMap_comp H e α β rfl) α

/-- A sibling of the identity induces a bijection on every positive Ext group. -/
private lemma bijective_shiftedHom_map_boundedSingle_pos
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    [H.CommShift ℤ] [H.IsTriangulated]
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A)
    (X Y : A) (n : ℕ) :
    Function.Bijective (fun f : ShiftedHom ((boundedSingleFunctor A).obj X)
      ((boundedSingleFunctor A).obj Y) ((n + 1 : ℕ) : ℤ) => f.map H) := by
  let : HasExt.{w} A := hasExt_of_hasDerivedCategory A
  let E := Iso.homCongr (e.app X) ((shiftFunctor _ ((n + 1 : ℕ) : ℤ)).mapIso (e.app Y))
  have hE : ∀ f : ShiftedHom ((boundedSingleFunctor A).obj X)
      ((boundedSingleFunctor A).obj Y) ((n + 1 : ℕ) : ℤ), E (f.map H) = f := by
    intro f
    obtain ⟨α, rfl⟩ := (boundedExtEquiv (A := A) (n := n + 1)).surjective f
    have hh := congrArg (boundedExtEquiv (A := A)) (siblingExtMap_eq_id H e α)
    simp only [siblingExtMap, Equiv.apply_symm_apply] at hh
    exact hh
  exact ⟨fun f g hfg => (hE f).symm.trans ((congrArg E hfg).trans (hE g)),
    fun f => ⟨E f, E.injective (hE (E f))⟩⟩

/-- A sibling of the identity induces a bijection on degree-zero shifted Hom groups between heart
objects. -/
private lemma bijective_shiftedHom_map_boundedSingle_zero
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    [H.CommShift ℤ] [H.IsTriangulated]
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A)
    (X Y : A) :
    Function.Bijective (fun f : ShiftedHom ((boundedSingleFunctor A).obj X)
      ((boundedSingleFunctor A).obj Y) (0 : ℤ) => f.map H) := by
  let b := boundedSingleFunctor A
  let hb := Classical.choice (boundedSingle_fullyFaithful (A := A))
  let hc := Functor.FullyFaithful.ofIso hb e.symm
  have h : Function.Bijective (H.map : (b.obj X ⟶ b.obj Y) → _) := by
    constructor
    · intro f g hfg
      obtain ⟨f, rfl⟩ := hb.map_surjective f
      obtain ⟨g, rfl⟩ := hb.map_surjective g
      exact congrArg b.map (hc.map_injective hfg)
    · intro f
      exact ⟨b.map (hc.preimage f), hc.map_preimage f⟩
  exact bijective_of_equiv_comm (ShiftedHom.homEquiv (X := b.obj X) (Y := b.obj Y) (0 : ℤ) rfl)
    (ShiftedHom.homEquiv (X := H.obj (b.obj X)) (Y := H.obj (b.obj Y)) (0 : ℤ) rfl) H.map _
    (fun f => ShiftedHom.map_mk₀ 0 rfl f H) h

/-- A sibling of the identity induces a bijection on every shifted Hom group between heart
objects. -/
private lemma bijective_shiftedHom_map_boundedSingle
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    [H.CommShift ℤ] [H.IsTriangulated]
    (e : boundedSingleFunctor A ⋙ H ≅ boundedSingleFunctor A)
    (X Y : A) (q : ℤ) :
    Function.Bijective (fun f : ShiftedHom ((boundedSingleFunctor A).obj X)
      ((boundedSingleFunctor A).obj Y) q => f.map H) := by
  by_cases hq : q < 0
  · have hzero : ∀ f : ShiftedHom ((boundedSingleFunctor A).obj X)
        ((boundedSingleFunctor A).obj Y) q, f = 0 := by
      intro f
      apply shiftedHom_map_injective DerivedCategory.Bounded.ι
      dsimp only
      rw [ShiftedHom.map_zero]
      have : DerivedCategory.TStructure.t.IsGE
          (((DerivedCategory.singleFunctor A 0).obj Y)⟦q⟧) (-q) :=
        DerivedCategory.TStructure.t.isGE_shift _ 0 q (-q) (by omega)
      have : DerivedCategory.TStructure.t.IsLE
          (DerivedCategory.Bounded.ι.obj ((boundedSingleFunctor A).obj X)) 0 := by
        show DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor A 0).obj X) 0
        infer_instance
      have : DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.Bounded.ι.obj ((boundedSingleFunctor A).obj Y))⟦q⟧) (-q) := by
        show DerivedCategory.TStructure.t.IsGE
          (((DerivedCategory.singleFunctor A 0).obj Y)⟦q⟧) (-q)
        infer_instance
      exact DerivedCategory.TStructure.t.zero (f.map DerivedCategory.Bounded.ι) 0 (-q) (by omega)
    let E := Iso.homCongr (e.app X) ((shiftFunctor _ q).mapIso (e.app Y))
    constructor
    · intro f g _
      exact (hzero f).trans (hzero g).symm
    · intro f
      refine ⟨0, E.injective ?_⟩
      rw [hzero (E f)]
      simp [E, Iso.homCongr]
  · lift q to ℕ using (le_of_not_gt hq)
    cases q with
    | zero => exact bijective_shiftedHom_map_boundedSingle_zero H e X Y
    | succ n => exact bijective_shiftedHom_map_boundedSingle_pos H e X Y n

end ExtComparison

/-- Bounded complexes are obtained from objects concentrated in one degree by extensions. -/
private lemma bounded_induction
    (P : DerivedCategory.Bounded A → Prop)
    (hzero : ∀ K, IsZero K → P K)
    (hsingle : ∀ (K : DerivedCategory.Bounded A) (n : ℤ),
      K.obj.IsGE n → K.obj.IsLE n → P K)
    (htriangle : ∀ (T : Triangle (DerivedCategory.Bounded A)),
      T ∈ distTriang (DerivedCategory.Bounded A) → P T.obj₁ → P T.obj₃ → P T.obj₂)
    (K : DerivedCategory.Bounded A) : P K := by
  have h : ∀ (n : ℕ) (a b : ℤ) (K : DerivedCategory.Bounded A),
      b ≤ a + n → K.obj.IsGE a → K.obj.IsLE b → P K := by
    intro n
    induction n with
    | zero =>
      intro a b K hn ha hb
      rcases lt_or_ge b a with hba | hba
      · exact hzero K (IsZero.of_full_of_faithful_of_isZero DerivedCategory.Bounded.ι K
          (DerivedCategory.TStructure.t.isZero K.obj b a hba))
      · obtain rfl : b = a := by omega
        exact hsingle K _ ha hb
    | succ n ih =>
      intro a b K hn ha hb
      let t := DerivedCategory.TStructure.t (C := A)
      let L : DerivedCategory.Bounded A := ⟨(t.truncLT b).obj K.obj,
        ⟨⟨a, inferInstance⟩, ⟨b - 1, inferInstance⟩⟩⟩
      let R : DerivedCategory.Bounded A := ⟨(t.truncGE b).obj K.obj,
        ⟨⟨b, inferInstance⟩, ⟨b, inferInstance⟩⟩⟩
      have hL : P L := ih a (b - 1) L (by omega) (by dsimp [L]; infer_instance)
        (by dsimp [L]; infer_instance)
      have hR : P R := hsingle R b (by dsimp [R]; infer_instance)
        (by dsimp [R]; infer_instance)
      exact htriangle (liftBoundedTriangle (t.triangleLTGE b |>.obj K.obj)
        L.property K.property R.property)
        (liftBoundedTriangle_distinguished _ _ _ _ (t.triangleLTGE_distinguished b K.obj)) hL hR
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property
  exact h (b - a).toNat a b K (by omega) ha hb

section HomComparison


/-- Bijectivity of the map induced by a functor on a Hom group is invariant under isomorphisms of
the source and the target. -/
private lemma bijective_map_of_iso
    {C E : Type*} [Category* C] [Category* E] (G : C ⥤ E)
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : Function.Bijective (G.map : (X ⟶ Y) → _)) :
    Function.Bijective (G.map : (X' ⟶ Y') → _) := by
  exact bijective_of_equiv_comm (Iso.homCongr eX eY) (Iso.homCongr (G.mapIso eX) (G.mapIso eY))
    _ _ (fun f => by simp [Iso.homCongr]) h

/-- The five-lemma step for comparison of representable functors. -/
private lemma bijective_map_triangle_middle
    {C E : Type*} [Category* C] [Category* E]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (G : C ⥤ E) [G.CommShift ℤ] [G.IsTriangulated]
    (X : C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : Function.Bijective (G.map : (X ⟶ T.obj₁) → _))
    (h₃ : Function.Bijective (G.map : (X ⟶ T.obj₃) → _))
    (h₁' : Function.Injective (G.map : (X ⟶ T.obj₁⟦(1 : ℤ)⟧) → _))
    (h₃' : Function.Surjective (G.map : (X ⟶ T.invRotate.obj₁) → _)) :
    Function.Bijective (G.map : (X ⟶ T.obj₂) → _) := by
  have hzero : ∀ f : X ⟶ T.obj₂, G.map f = 0 → f = 0 := by
    intro f hf
    have hf' : f ≫ T.mor₂ = 0 := h₃.1 (by simp [hf])
    obtain ⟨g, rfl⟩ := T.coyoneda_exact₂ hT f hf'
    obtain ⟨h, hh⟩ := (G.mapTriangle.obj T.invRotate).coyoneda_exact₂
      (G.map_distinguished _ (inv_rot_of_distTriang _ hT)) (G.map g)
      ((G.map_comp g T.invRotate.mor₂).symm.trans hf)
    obtain ⟨k, rfl⟩ := h₃' h
    have hg : g = k ≫ T.invRotate.mor₁ :=
      h₁.1 (hh.trans (G.map_comp k T.invRotate.mor₁).symm)
    have h0 : T.invRotate.mor₁ ≫ T.invRotate.mor₂ = 0 :=
      comp_distTriang_mor_zero₁₂ T.invRotate (inv_rot_of_distTriang _ hT)
    have h1 : k ≫ T.invRotate.mor₁ ≫ T.invRotate.mor₂ = 0 := by rw [h0, comp_zero]
    exact (congrArg (fun z => z ≫ T.invRotate.mor₂) hg).trans
      ((Category.assoc k T.invRotate.mor₁ T.invRotate.mor₂).trans h1)
  constructor
  · intro f g hfg
    apply sub_eq_zero.mp
    exact hzero (f - g) (by simp [hfg])
  · intro y₂
    obtain ⟨x₃, hx₃⟩ := h₃.2 (y₂ ≫ G.map T.mor₂)
    have hx₃' : x₃ ≫ T.mor₃ = 0 := h₁' (by
      rw [CategoryTheory.Functor.map_comp, hx₃, Category.assoc,
        ← CategoryTheory.Functor.map_comp, comp_distTriang_mor_zero₂₃ T hT,
        G.map_zero, comp_zero, G.map_zero])
    obtain ⟨x₂, hx₂⟩ := T.coyoneda_exact₃ hT x₃ hx₃'
    obtain ⟨y₁, hy₁⟩ := (G.mapTriangle.obj T).coyoneda_exact₂
      (G.map_distinguished _ hT) (y₂ - G.map x₂) (by
        show (y₂ - G.map x₂) ≫ G.map T.mor₂ = 0
        rw [Preadditive.sub_comp, ← CategoryTheory.Functor.map_comp, ← hx₂, hx₃, sub_self])
    dsimp only [Functor.mapTriangle, Triangle.mk_obj₁, Triangle.mk_mor₁] at y₁ hy₁
    obtain ⟨x₁, hx₁⟩ := h₁.2 y₁
    refine ⟨x₂ + x₁ ≫ T.mor₁, ?_⟩
    rw [G.map_add, CategoryTheory.Functor.map_comp, hx₁, ← hy₁, add_sub_cancel]

/-- A functor commuting with the shift is bijective on a Hom group between shifted objects as soon
as it is bijective on the unshifted one. -/
private lemma bijective_map_shift
    {C E : Type*} [Category* C] [Category* E] [HasShift C ℤ] [HasShift E ℤ]
    (G : C ⥤ E) [G.CommShift ℤ] {X Y : C} (n : ℤ)
    (h : Function.Bijective (G.map : (X ⟶ Y) → _)) :
    Function.Bijective (G.map : (X⟦n⟧ ⟶ Y⟦n⟧) → _) := by
  let p := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C n)).homEquiv
    (X := X) (Y := Y)
  let q := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor E n)).homEquiv
    (X := G.obj X) (Y := G.obj Y)
  let r := Iso.homCongr ((G.commShiftIso n).app X) ((G.commShiftIso n).app Y)
  have hc : ∀ f, r (G.map (p f)) = q (G.map f) := by
    intro f
    dsimp [r, p, q, Iso.homCongr, Functor.FullyFaithful.homEquiv]
    rw [G.commShiftIso_hom_naturality, Iso.inv_hom_id_app_assoc]
  exact bijective_of_equiv_comm p (q.trans r.symm) _ _ (fun f => r.eq_symm_apply.2 (hc f)) h

/-- A functor commuting with the shift and bijective on every Hom group out of `X` is bijective on
every Hom group out of a shift of `X`. -/
private lemma bijective_map_shift_source
    {C E : Type*} [Category* C] [Category* E] [HasShift C ℤ] [HasShift E ℤ]
    (G : C ⥤ E) [G.CommShift ℤ] {X : C}
    (h : ∀ Y, Function.Bijective (G.map : (X ⟶ Y) → _)) (n : ℤ) (Y : C) :
    Function.Bijective (G.map : (X⟦n⟧ ⟶ Y) → _) :=
  bijective_map_of_iso G (Iso.refl _)
    (((shiftFunctorAdd' C (-n) n 0 (by omega)).app Y).symm ≪≫
      (shiftFunctorZero C ℤ).app Y)
    (bijective_map_shift G n (h (Y⟦-n⟧)))

/-- The contravariant representable five-lemma step. -/
private lemma bijective_map_triangle_middle_left
    {C E : Type*} [Category* C] [Category* E]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (G : C ⥤ E) [G.CommShift ℤ] [G.IsTriangulated]
    (Y : C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : Function.Bijective (G.map : (T.obj₁ ⟶ Y) → _))
    (h₃ : Function.Bijective (G.map : (T.obj₃ ⟶ Y) → _))
    (h₁' : Function.Surjective (G.map : (T.obj₁⟦(1 : ℤ)⟧ ⟶ Y) → _))
    (h₃' : Function.Injective (G.map : (T.invRotate.obj₁ ⟶ Y) → _)) :
    Function.Bijective (G.map : (T.obj₂ ⟶ Y) → _) := by
  have hzero : ∀ f : T.obj₂ ⟶ Y, G.map f = 0 → f = 0 := by
    intro f hf
    have hf' : T.mor₁ ≫ f = 0 := h₁.1 (by simp [hf])
    obtain ⟨g, rfl⟩ := T.yoneda_exact₂ hT f hf'
    obtain ⟨k, hk⟩ := (G.mapTriangle.obj T.rotate).yoneda_exact₂
      (G.map_distinguished _ (rot_of_distTriang _ hT)) (G.map g)
      ((G.map_comp T.rotate.mor₁ g).symm.trans hf)
    obtain ⟨l, rfl⟩ := h₁' k
    have hg : g = T.mor₃ ≫ l := h₃.1 (hk.trans (G.map_comp T.mor₃ l).symm)
    rw [hg, ← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp]
  constructor
  · intro f g hfg
    apply sub_eq_zero.mp
    exact hzero (f - g) (by simp [hfg])
  · intro y₂
    obtain ⟨x₁, hx₁⟩ := h₁.2 (G.map T.mor₁ ≫ y₂)
    have h0 : T.invRotate.mor₁ ≫ T.invRotate.mor₂ = 0 :=
      comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hT)
    have key : G.map (T.invRotate.mor₁ ≫ x₁) = 0 :=
      calc G.map (T.invRotate.mor₁ ≫ x₁)
          = G.map T.invRotate.mor₁ ≫ G.map x₁ := G.map_comp _ _
        _ = G.map T.invRotate.mor₁ ≫ G.map T.mor₁ ≫ y₂ :=
              congrArg (fun z => G.map T.invRotate.mor₁ ≫ z) hx₁
        _ = (G.map T.invRotate.mor₁ ≫ G.map T.invRotate.mor₂) ≫ y₂ :=
              (Category.assoc _ _ _).symm
        _ = G.map (T.invRotate.mor₁ ≫ T.invRotate.mor₂) ≫ y₂ :=
              congrArg (fun z => z ≫ y₂) (G.map_comp _ _).symm
        _ = 0 := by
              rw [h0, G.map_zero]
              exact zero_comp
    have hx₁' : T.invRotate.mor₁ ≫ x₁ = 0 := h₃' (key.trans (G.map_zero _ _).symm)
    obtain ⟨x₂, hx₂⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang _ hT) x₁ hx₁'
    change T.obj₂ ⟶ Y at x₂
    change x₁ = T.mor₁ ≫ x₂ at hx₂
    obtain ⟨y₃, hy₃⟩ := (G.mapTriangle.obj T).yoneda_exact₂
      (G.map_distinguished _ hT) (y₂ - G.map x₂) (by
        show G.map T.mor₁ ≫ (y₂ - G.map x₂) = 0
        rw [Preadditive.comp_sub, ← CategoryTheory.Functor.map_comp, ← hx₂, hx₁, sub_self])
    dsimp only [Functor.mapTriangle, Triangle.mk_obj₃, Triangle.mk_mor₂] at y₃ hy₃
    obtain ⟨x₃, hx₃⟩ := h₃.2 y₃
    refine ⟨x₂ + T.mor₂ ≫ x₃, ?_⟩
    rw [G.map_add, CategoryTheory.Functor.map_comp, hx₃, ← hy₃, add_sub_cancel]

/-- A bounded object concentrated in degree `n` is isomorphic to a shift of a degree-zero
object. -/
private lemma exists_iso_boundedSingle_shift (K : DerivedCategory.Bounded A) (n : ℤ)
    [K.obj.IsGE n] [K.obj.IsLE n] :
    ∃ X : A, Nonempty (K ≅ ((boundedSingleFunctor A).obj X)⟦-n⟧) := by
  obtain ⟨X, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj n
  refine ⟨X, ⟨(Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Bounded.ι).preimageIso
    (e ≪≫ (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app X).symm ≪≫
      ((DerivedCategory.Bounded.ι.commShiftIso (-n)).app
        ((boundedSingleFunctor A).obj X)).symm)⟩⟩

/-- Comparison on shifts of heart objects extends to arbitrary bounded targets. -/
private lemma bijective_map_from_boundedSingle
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    [H.CommShift ℤ] [H.IsTriangulated]
    (h : ∀ (X Y : A) (n : ℤ), Function.Bijective
      (H.map : ((boundedSingleFunctor A).obj X ⟶
        ((boundedSingleFunctor A).obj Y)⟦n⟧) → _))
    (X : A) (Y : DerivedCategory.Bounded A) :
    Function.Bijective (H.map : ((boundedSingleFunctor A).obj X ⟶ Y) → _) := by
  have h' : ∀ K : DerivedCategory.Bounded A, ∀ (X : A) (n : ℤ), Function.Bijective
      (H.map : ((boundedSingleFunctor A).obj X ⟶ K⟦n⟧) → _) := by
    apply bounded_induction
    · intro K hK X n
      have hz := (shiftFunctor _ n).map_isZero hK
      exact ⟨fun _ _ _ => hz.eq_of_tgt _ _, fun f => ⟨0, (H.map_isZero hz).eq_of_tgt _ _⟩⟩
    · intro K n hGE hLE X q
      obtain ⟨Z, ⟨e⟩⟩ := exists_iso_boundedSingle_shift K n
      exact bijective_map_of_iso H (Iso.refl _)
        ((shiftFunctorAdd _ (-n) q).app ((boundedSingleFunctor A).obj Z) ≪≫
          (shiftFunctor _ q).mapIso e.symm) (h X Z (-n + q))
    · intro T hT h₁ h₃ X n
      refine bijective_map_triangle_middle H ((boundedSingleFunctor A).obj X)
        (T⟦n⟧) (T.shift_distinguished hT n) (h₁ X n) (h₃ X n) ?_ ?_
      · exact (bijective_map_of_iso H (Iso.refl _)
          ((shiftFunctorAdd _ n (1 : ℤ)).app T.obj₁) (h₁ X (n + 1))).1
      · exact (bijective_map_of_iso H (Iso.refl _)
          ((shiftFunctorAdd _ n (-1 : ℤ)).app T.obj₃) (h₃ X (n + -1))).2
  exact bijective_map_of_iso H (Iso.refl _) ((shiftFunctorZero _ ℤ).app Y) (h' Y X 0)

/-- An exact endofunctor is fully faithful once it is so on every shift of the heart. -/
private lemma fullyFaithful_of_bijective_map_boundedSingle
    (H : DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded A)
    [H.CommShift ℤ] [H.IsTriangulated]
    (h : ∀ (X Y : A) (n : ℤ), Function.Bijective
      (H.map : ((boundedSingleFunctor A).obj X ⟶
        ((boundedSingleFunctor A).obj Y)⟦n⟧) → _)) :
    Nonempty H.FullyFaithful := by
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective H).2
  apply bounded_induction
  · intro K hK Y
    exact ⟨fun _ _ _ => hK.eq_of_src _ _, fun f => ⟨0, (H.map_isZero hK).eq_of_src _ _⟩⟩
  · intro K n hGE hLE Y
    obtain ⟨X, ⟨e⟩⟩ := exists_iso_boundedSingle_shift K n
    exact bijective_map_of_iso H e.symm (Iso.refl _)
      (bijective_map_shift_source H (bijective_map_from_boundedSingle H h X) (-n) Y)
  · intro T hT h₁ h₃ Y
    exact bijective_map_triangle_middle_left H Y T hT (h₁ Y) (h₃ Y)
      (bijective_map_shift_source H h₁ 1 Y).2 (bijective_map_shift_source H h₃ (-1) Y).1

end HomComparison

/-- **Stacks Project, Tag 0FZV, part (1).** If two exact functors from a bounded
derived category are siblings and the first is essentially surjective, then the second is
essentially surjective. -/
@[stacks 0FZV "part (1)"]
public theorem essSurj_of_areSiblings (h : AreSiblings F F')
    (hF : F.EssSurj) : F'.EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨X, ⟨e⟩⟩ := hF.mem_essImage Y
  obtain ⟨e'⟩ := h.objIso X
  exact ⟨X, ⟨e'.symm ≪≫ e⟩⟩

/-- **Stacks Project, Tag 0FZV, part (2).** If two exact functors from a bounded
derived category are siblings and the first is fully faithful, then the second is fully
faithful. -/
@[stacks 0FZV "part (2)"]
public theorem fullyFaithful_of_areSiblings (h : AreSiblings F F')
    (hF : Nonempty F.FullyFaithful) : Nonempty F'.FullyFaithful := by
  let : F.Full := (Classical.choice hF).full
  let : F.Faithful := (Classical.choice hF).faithful
  let : (liftSibling h hF).CommShift ℤ := liftSiblingCommShift h hF
  have : (liftSibling h hF).IsTriangulated := by
    let : NatTrans.CommShift (liftSiblingCompIso h hF).hom ℤ :=
      Functor.CommShift.ofComp_compatibility (liftSiblingCompIso h hF) ℤ
    exact (Functor.isTriangulated_iff_comp_right (liftSiblingCompIso h hF)).mpr inferInstance
  obtain ⟨e⟩ := (liftSibling_areSiblings h hF).restrictionIso
  let eHeart := e.symm ≪≫ Functor.rightUnitor (boundedSingleFunctor A)
  have hExt := bijective_shiftedHom_map_boundedSingle (liftSibling h hF) eHeart
  have hH : Nonempty (liftSibling h hF).FullyFaithful := by
    apply fullyFaithful_of_bijective_map_boundedSingle
    intro X Y n
    constructor
    · intro f g hfg
      exact (hExt X Y n).1 (by simp only [ShiftedHom.map, hfg])
    · intro f
      obtain ⟨g, hg⟩ := (hExt X Y n).2
        (f ≫ ((liftSibling h hF).commShiftIso n).hom.app
          ((boundedSingleFunctor A).obj Y))
      exact ⟨g, (cancel_mono
        (((liftSibling h hF).commShiftIso n).hom.app
          ((boundedSingleFunctor A).obj Y))).1 hg⟩
  exact ⟨((Classical.choice hH).comp (Classical.choice hF)).ofIso (liftSiblingCompIso h hF)⟩

end AlgebraicGeometry

end
