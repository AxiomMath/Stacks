module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Basic

/-!
# Glueing data attached to a single commutative square

A commutative square
```
O --b--> L
|        |
a        d
↓        ↓
U --c--> T
```
of schemes gives a canonical functor from schemes of finite presentation over `T` to the
*glueing data* of the square: a scheme of finite presentation over `U`, one over `L`, and an
isomorphism between the two induced restrictions to `O`, as in
[Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA) and
[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q).

This file builds that functor, a transport of iso-comma categories along
`CategoryTheory.Comma.map`, and the statement that an isomorphism of squares over a fixed base
`T` carries the canonical functor of one square to the canonical functor of the other.

## Main definitions

* `AlgebraicGeometry.isoCommaMap`: the functor between iso-comma categories induced by
  `CategoryTheory.Comma.map`.
* `AlgebraicGeometry.glueingDataOfSquare`: the glueing data of a commutative square.
* `AlgebraicGeometry.restrictionFunctorOfSquare`: the canonical functor from schemes of finite
  presentation over `T` into the glueing data of the square.

## Main results

* `AlgebraicGeometry.isoCommaMap_isEquivalence`: the transport of iso-comma categories is an
  equivalence as soon as the two outer functors are equivalences and the middle one is full and
  faithful.
* `AlgebraicGeometry.restrictionFunctorOfSquare_isEquivalence_of_iso`: the canonical functor of
  a square is an equivalence as soon as the canonical functor of an isomorphic square is.

## References

* [Stacks Project, Lemma 32.14.1 (0BPA)](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u₁ u₂ u

namespace AlgebraicGeometry

/-! ### Iso-comma categories -/

/-- Invertibility of the comparison morphism of an object of a comma category is stable under
isomorphism. -/
theorem isIso_hom_of_comma_iso {A B T : Type u₁} [Category.{v} A] [Category.{v} B]
    [Category.{v} T] {L : A ⥤ T} {R : B ⥤ T} {X Y : Comma L R} (e : X ≅ Y)
    (hX : IsIso X.hom) : IsIso Y.hom := by
  have h : Y.hom = CategoryTheory.inv (L.map e.hom.left) ≫ X.hom ≫ R.map e.hom.right := by
    rw [← e.hom.w]
    simp
  rw [h]
  infer_instance

/-- If `G` is an equivalence and a property `Q` of objects of the target holds exactly on the
image of a property `P` of objects of the source, the induced functor between the two full
subcategories is an equivalence. -/
theorem isEquivalence_objectPropertyLift {C : Type u₁} {D : Type u₂} [Category.{v} C]
    [Category.{v'} D] (P : ObjectProperty C) (Q : ObjectProperty D) (G : C ⥤ D)
    [G.IsEquivalence] (hQ : ∀ {Y Y' : D}, (Y ≅ Y') → Q Y → Q Y')
    (h : ∀ X : C, P X ↔ Q (G.obj X)) (hPQ : ∀ X : P.FullSubcategory, Q ((P.ι ⋙ G).obj X)) :
    (Q.lift (P.ι ⋙ G) hPQ).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := ⟨fun Y ↦ ⟨⟨G.objPreimage Y.obj,
    (h _).mpr (hQ (G.objObjPreimageIso Y.obj).symm Y.property)⟩,
    ⟨ObjectProperty.isoMk _ (G.objObjPreimageIso Y.obj)⟩⟩⟩

section IsoCommaMap

variable {A B T A' B' T' : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Category.{u} T]
  [Category.{u} A'] [Category.{u} B'] [Category.{u} T']
  {L : A ⥤ T} {R : B ⥤ T} {L' : A' ⥤ T'} {R' : B' ⥤ T'}
  {F₁ : A ⥤ A'} {F₂ : B ⥤ B'} {F : T ⥤ T'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F) (β : R ⋙ F ⟶ F₂ ⋙ R') [IsIso α] [IsIso β]

/-- `CategoryTheory.Comma.map` along natural isomorphisms preserves invertibility of the
comparison morphism. -/
theorem isIso_comma_map_hom (X : Comma L R) (hX : IsIso X.hom) :
    IsIso ((Comma.map α β).obj X).hom := by
  have : IsIso X.hom := hX
  show IsIso (α.app X.left ≫ F.map X.hom ≫ β.app X.right)
  infer_instance

/-- `CategoryTheory.Comma.map` along natural isomorphisms reflects invertibility of the
comparison morphism, provided the functor on the common target is full and faithful. -/
theorem isIso_hom_of_isIso_comma_map_hom [F.Full] [F.Faithful] (X : Comma L R)
    (hX : IsIso ((Comma.map α β).obj X).hom) : IsIso X.hom := by
  have h : IsIso (α.app X.left ≫ F.map X.hom ≫ β.app X.right) := hX
  have h' : IsIso (F.map X.hom ≫ β.app X.right) :=
    IsIso.of_isIso_comp_left (α.app X.left) _
  have : IsIso (F.map X.hom) := IsIso.of_isIso_comp_right (F.map X.hom) (β.app X.right)
  exact isIso_of_reflects_iso X.hom F

/-- The functor between iso-comma categories induced by `CategoryTheory.Comma.map` along two
natural isomorphisms. -/
noncomputable def isoCommaMap : IsoComma L R ⥤ IsoComma L' R' :=
  (show ObjectProperty (Comma L' R') from fun X ↦ IsIso X.hom).lift
    ((show ObjectProperty (Comma L R) from fun X ↦ IsIso X.hom).ι ⋙ Comma.map α β)
    (fun X ↦ isIso_comma_map_hom α β X.obj X.property)

/-- The transport of iso-comma categories along two natural isomorphisms is an equivalence as
soon as the functors on the two source categories are equivalences and the functor on the common
target category is full and faithful. -/
theorem isoCommaMap_isEquivalence [F₁.IsEquivalence] [F₂.IsEquivalence] [F.Full] [F.Faithful] :
    (isoCommaMap α β).IsEquivalence :=
  isEquivalence_objectPropertyLift _ _ (Comma.map α β)
    (fun e hX ↦ isIso_hom_of_comma_iso e hX)
    (fun X ↦ ⟨fun hX ↦ isIso_comma_map_hom α β X hX,
      fun hX ↦ isIso_hom_of_isIso_comma_map_hom α β X hX⟩) _

end IsoCommaMap

/-! ### Base change along a composite -/

/-- The comparison isomorphism identifying base change along a composite with iterated base
change commutes with the projections to the object being pulled back. -/
theorem pullbackComp_hom_app_left_fst {C : Type*} [Category C] [HasPullbacks C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (X : Over D) :
    ((Over.pullbackComp f g).hom.app X).left ≫
        pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g =
      pullback.fst X.hom (f ≫ g) := by
  have h := conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapComp f g).inv X
  have hh := congrArg (fun k ↦ k.left) h
  simpa [Over.pullbackComp, conjugateIsoEquiv, Adjunction.comp_counit] using hh

/-- The inverse comparison isomorphism identifying iterated base change with base change along
a composite commutes with the projections to the object being pulled back. -/
theorem pullbackComp_inv_app_left_fst {C : Type*} [Category C] [HasPullbacks C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (X : Over D) :
    ((Over.pullbackComp f g).inv.app X).left ≫ pullback.fst X.hom (f ≫ g) =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g := by
  rw [← pullbackComp_hom_app_left_fst f g X, ← Category.assoc, ← Over.comp_left]
  simp

/-- Base change of schemes of finite presentation along a composite: restricting along the
second factor and then along the first is restricting along the composite. -/
noncomputable def finitePresentationBaseChangeComp {S T W : Scheme.{u}} (f : W ⟶ T)
    (g : T ⟶ S) :
    finitePresentationBaseChange g ⋙ finitePresentationBaseChange f ≅
      finitePresentationBaseChange (f ≫ g) :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ ((Over.pullbackComp f g).app X.obj).symm)
    (fun {_ _} φ ↦ ObjectProperty.hom_ext _ ((Over.pullbackComp f g).inv.naturality φ.hom))

/-- The comparison isomorphism for base change along a composite commutes with the projections
to the scheme being restricted. -/
@[reassoc]
theorem finitePresentationBaseChangeComp_hom_app_hom_left_fst {S T W : Scheme.{u}} (f : W ⟶ T)
    (g : T ⟶ S) (X : FinitePresentationOver S) :
    ((finitePresentationBaseChangeComp f g).hom.app X).hom.left ≫
        pullback.fst X.obj.hom (f ≫ g) =
      pullback.fst (pullback.snd X.obj.hom g) f ≫ pullback.fst X.obj.hom g :=
  pullbackComp_inv_app_left_fst f g X.obj

/-- Base change of schemes of finite presentation along a morphism commutes with the projections
to the scheme being restricted. -/
@[reassoc]
theorem finitePresentationBaseChange_map_hom_left_fst {T W : Scheme.{u}} (p : W ⟶ T)
    {X Y : FinitePresentationOver T} (φ : X ⟶ Y) :
    ((finitePresentationBaseChange p).map φ).hom.left ≫ pullback.fst Y.obj.hom p =
      pullback.fst X.obj.hom p ≫ φ.hom.left := by
  simp [finitePresentationBaseChange, Over.pullback, pullback.lift_fst]

/-- Composing the two underlying morphisms of an isomorphism of schemes of finite presentation
over `W` in the other order gives the identity. -/
theorem fp_iso_inv_hom_left_cancel {W : Scheme.{u}} {X Y : FinitePresentationOver W} (e : X ≅ Y) :
    e.inv.hom.left ≫ e.hom.hom.left = 𝟙 _ :=
  congrArg (fun k ↦ k.hom.left) e.inv_hom_id

/-- An isomorphism of schemes of finite presentation over `W` which is compatible with two maps
out of the underlying schemes is compatible with them the other way round. -/
theorem fp_iso_inv_hom_left_comp {W : Scheme.{u}} {X Y : FinitePresentationOver W} (e : X ≅ Y)
    {Z : Scheme.{u}} {k : X.obj.left ⟶ Z} {l : Y.obj.left ⟶ Z}
    (hk : e.hom.hom.left ≫ l = k) : e.inv.hom.left ≫ k = l := by
  rw [← hk, ← Category.assoc, fp_iso_inv_hom_left_cancel, Category.id_comp]

/-- The base-change associativity isomorphism of a commutative square commutes with the
projections to the scheme being restricted. -/
@[reassoc]
theorem finitePresentationPullbackSquareIso_hom_app_hom_left_fst {S U L V : Scheme.{u}}
    {u : U ⟶ S} {p : L ⟶ S} {v : V ⟶ L} {q : V ⟶ U} (w : q ≫ u = v ≫ p)
    (X : FinitePresentationOver S) :
    ((finitePresentationPullbackSquareIso w).hom.app X).hom.left ≫
        pullback.fst (pullback.snd X.obj.hom p) v ≫ pullback.fst X.obj.hom p =
      pullback.fst (pullback.snd X.obj.hom u) q ≫ pullback.fst X.obj.hom u :=
  Over.pullbackSquareObjIso_hom_left_fst w X.obj

/-- The inverse of the base-change associativity isomorphism of a commutative square commutes
with the projections to the scheme being restricted. -/
@[reassoc]
theorem finitePresentationPullbackSquareIso_inv_app_hom_left_fst {S U L V : Scheme.{u}}
    {u : U ⟶ S} {p : L ⟶ S} {v : V ⟶ L} {q : V ⟶ U} (w : q ≫ u = v ≫ p)
    (X : FinitePresentationOver S) :
    ((finitePresentationPullbackSquareIso w).inv.app X).hom.left ≫
        pullback.fst (pullback.snd X.obj.hom u) q ≫ pullback.fst X.obj.hom u =
      pullback.fst (pullback.snd X.obj.hom p) v ≫ pullback.fst X.obj.hom p :=
  fp_iso_inv_hom_left_comp ((finitePresentationPullbackSquareIso w).app X)
    (Over.pullbackSquareObjIso_hom_left_fst w X.obj)

/-! ### Glueing data for a commutative square -/

/-- Glueing data for a pair of maps `a : O ⟶ U` and `b : O ⟶ L`: a scheme of finite presentation
over `U`, one over `L`, and an isomorphism of their two restrictions to `O`. -/
abbrev glueingDataOfSquare {U L O : Scheme.{u}} (a : O ⟶ U) (b : O ⟶ L) :=
  IsoComma (finitePresentationBaseChange a) (finitePresentationBaseChange b)

/-- The canonical functor from schemes of finite presentation over `T` into the glueing data of a
commutative square `a ≫ c = b ≫ d`: a scheme over `T` is restricted along `c` and along `d`, and
its two restrictions to `O` are identified by the base-change associativity isomorphism of the
square. -/
noncomputable def restrictionFunctorOfSquare {T U L O : Scheme.{u}} (c : U ⟶ T) (d : L ⟶ T)
    {a : O ⟶ U} {b : O ⟶ L} (h : a ≫ c = b ≫ d) :
    FinitePresentationOver T ⥤ glueingDataOfSquare a b :=
  (show ObjectProperty (Comma (finitePresentationBaseChange a) (finitePresentationBaseChange b))
      from fun X ↦ IsIso X.hom).lift
    { obj := fun X ↦ ⟨(finitePresentationBaseChange c).obj X,
        (finitePresentationBaseChange d).obj X,
        (finitePresentationPullbackSquareIso h).hom.app X⟩
      map := fun f ↦ ⟨(finitePresentationBaseChange c).map f,
        (finitePresentationBaseChange d).map f,
        (finitePresentationPullbackSquareIso h).hom.naturality f⟩
      map_id := by intro X; ext <;> simp
      map_comp := by intro X Y Z f g; ext <;> simp } (fun X ↦ inferInstance)

/-! ### Transporting the canonical functor along an isomorphism of squares -/

/-- Two morphisms into the iterated base change attached to a commutative square agree as soon
as they agree after projecting to the scheme being restricted. -/
theorem over_hom_ext_of_pullbackSquare {S U L V : Scheme.{u}} {u : U ⟶ S} {p : L ⟶ S}
    {v : V ⟶ L} {q : V ⟶ U} (w : q ≫ u = v ≫ p) (X : Over S) {A : Over V}
    (f g : A ⟶ (Over.pullback p ⋙ Over.pullback v).obj X)
    (hfst : f.left ≫ pullback.fst (pullback.snd X.hom p) v ≫ pullback.fst X.hom p =
      g.left ≫ pullback.fst (pullback.snd X.hom p) v ≫ pullback.fst X.hom p) : f = g :=
  Over.OverMorphism.ext
    ((Over.isPullback_pullback_snd_pullback' w X).hom_ext hfst (f.w.trans g.w.symm))

section Transport

variable {T U L O U' L' O' : Scheme.{u}} {c : U ⟶ T} {d : L ⟶ T} {a : O ⟶ U} {b : O ⟶ L}
  {a' : O' ⟶ U'} {b' : O' ⟶ L'}

/-- The canonical functor of a commutative square over `T`, followed by the transport of glueing
data along an isomorphism of squares over `T`, is the canonical functor of the second square. -/
noncomputable def restrictionFunctorOfSquareTransportIso (γ : U ≅ U') (δ : L ≅ L') (ω : O ≅ O')
    (h : a ≫ c = b ≫ d) (h' : a' ≫ (γ.inv ≫ c) = b' ≫ (δ.inv ≫ d))
    (ha : a' ≫ γ.inv = ω.inv ≫ a) (hb : b' ≫ δ.inv = ω.inv ≫ b) :
    restrictionFunctorOfSquare c d h ⋙
        isoCommaMap (finitePresentationPullbackSquareIso ha).hom
          (finitePresentationPullbackSquareIso hb).inv ≅
      restrictionFunctorOfSquare (γ.inv ≫ c) (δ.inv ≫ d) h' := by
  refine NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (Comma.isoMk
    ((finitePresentationBaseChangeComp γ.inv c).app X)
    ((finitePresentationBaseChangeComp δ.inv d).app X) ?_)) ?_
  · change (finitePresentationBaseChange a').map
          ((finitePresentationBaseChangeComp γ.inv c).hom.app X) ≫
          (finitePresentationPullbackSquareIso h').hom.app X =
        ((finitePresentationPullbackSquareIso ha).hom.app
            ((finitePresentationBaseChange c).obj X) ≫
          (finitePresentationBaseChange ω.inv).map
            ((finitePresentationPullbackSquareIso h).hom.app X) ≫
          (finitePresentationPullbackSquareIso hb).inv.app
            ((finitePresentationBaseChange d).obj X)) ≫
        (finitePresentationBaseChange b').map
          ((finitePresentationBaseChangeComp δ.inv d).hom.app X)
    have hf : ((finitePresentationBaseChange a').map
          ((finitePresentationBaseChangeComp γ.inv c).hom.app X) ≫
          (finitePresentationPullbackSquareIso h').hom.app X).hom.left ≫
        pullback.fst (pullback.snd X.obj.hom (δ.inv ≫ d)) b' ≫
          pullback.fst X.obj.hom (δ.inv ≫ d) =
        pullback.fst (pullback.snd (pullback.snd X.obj.hom c) γ.inv) a' ≫
          pullback.fst (pullback.snd X.obj.hom c) γ.inv ≫ pullback.fst X.obj.hom c := by
      simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc,
        finitePresentationPullbackSquareIso_hom_app_hom_left_fst]
      exact (finitePresentationBaseChange_map_hom_left_fst_assoc a'
          ((finitePresentationBaseChangeComp γ.inv c).hom.app X)
          (pullback.fst X.obj.hom (γ.inv ≫ c))).trans
        (congrArg
          (fun k ↦ pullback.fst (pullback.snd (pullback.snd X.obj.hom c) γ.inv) a' ≫ k)
          (finitePresentationBaseChangeComp_hom_app_hom_left_fst γ.inv c X))
    have hg : (((finitePresentationPullbackSquareIso ha).hom.app
              ((finitePresentationBaseChange c).obj X) ≫
            (finitePresentationBaseChange ω.inv).map
              ((finitePresentationPullbackSquareIso h).hom.app X) ≫
            (finitePresentationPullbackSquareIso hb).inv.app
              ((finitePresentationBaseChange d).obj X)) ≫
          (finitePresentationBaseChange b').map
            ((finitePresentationBaseChangeComp δ.inv d).hom.app X)).hom.left ≫
        pullback.fst (pullback.snd X.obj.hom (δ.inv ≫ d)) b' ≫
          pullback.fst X.obj.hom (δ.inv ≫ d) =
        pullback.fst (pullback.snd (pullback.snd X.obj.hom c) γ.inv) a' ≫
          pullback.fst (pullback.snd X.obj.hom c) γ.inv ≫ pullback.fst X.obj.hom c := by
      simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
      have step1 := (finitePresentationBaseChange_map_hom_left_fst_assoc b'
          ((finitePresentationBaseChangeComp δ.inv d).hom.app X)
          (pullback.fst X.obj.hom (δ.inv ≫ d))).trans
        (whisker_eq (pullback.fst (pullback.snd (pullback.snd X.obj.hom d) δ.inv) b')
          (finitePresentationBaseChangeComp_hom_app_hom_left_fst δ.inv d X))
      have step2 := finitePresentationPullbackSquareIso_inv_app_hom_left_fst_assoc hb
        ((finitePresentationBaseChange d).obj X) (pullback.fst X.obj.hom d)
      have step3 := (finitePresentationBaseChange_map_hom_left_fst_assoc ω.inv
          ((finitePresentationPullbackSquareIso h).hom.app X)
          (pullback.fst (pullback.snd X.obj.hom d) b ≫ pullback.fst X.obj.hom d)).trans
        (whisker_eq (pullback.fst (pullback.snd (pullback.snd X.obj.hom c) a) ω.inv)
          (finitePresentationPullbackSquareIso_hom_app_hom_left_fst h X))
      have step4 := finitePresentationPullbackSquareIso_hom_app_hom_left_fst_assoc ha
        ((finitePresentationBaseChange c).obj X) (pullback.fst X.obj.hom c)
      exact (whisker_eq _ (whisker_eq _ (whisker_eq _ step1))).trans
        ((whisker_eq _ (whisker_eq _ step2)).trans ((whisker_eq _ step3).trans step4))
    exact ObjectProperty.hom_ext _
      (over_hom_ext_of_pullbackSquare h' X.obj _ _ (hf.trans hg.symm))
  · intro X Y f
    refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ ?_)
    · exact (finitePresentationBaseChangeComp γ.inv c).hom.naturality f
    · exact (finitePresentationBaseChangeComp δ.inv d).hom.naturality f

/-- **Stacks Project, Lemma 32.14.1 (0BPA)**, transported along an isomorphism of squares: if
the canonical functor of one commutative square over `T` is an equivalence, so is the canonical
functor of any square over `T` isomorphic to it. -/
theorem restrictionFunctorOfSquare_isEquivalence_of_iso (γ : U ≅ U') (δ : L ≅ L') (ω : O ≅ O')
    (h : a ≫ c = b ≫ d) {c' : U' ⟶ T} {d' : L' ⟶ T} (h' : a' ≫ c' = b' ≫ d')
    (hc : c' = γ.inv ≫ c) (hd : d' = δ.inv ≫ d)
    (ha : a' ≫ γ.inv = ω.inv ≫ a) (hb : b' ≫ δ.inv = ω.inv ≫ b)
    (hequiv : (restrictionFunctorOfSquare c' d' h').IsEquivalence) :
    (restrictionFunctorOfSquare c d h).IsEquivalence := by
  subst hc hd
  have := finitePresentationBaseChange_isEquivalence_of_isIso γ.inv
  have := finitePresentationBaseChange_isEquivalence_of_isIso δ.inv
  have := finitePresentationBaseChange_isEquivalence_of_isIso ω.inv
  have := isoCommaMap_isEquivalence (finitePresentationPullbackSquareIso ha).hom
    (finitePresentationPullbackSquareIso hb).inv
  have := hequiv
  have : (restrictionFunctorOfSquare c d h ⋙
      isoCommaMap (finitePresentationPullbackSquareIso ha).hom
        (finitePresentationPullbackSquareIso hb).inv).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (restrictionFunctorOfSquareTransportIso γ δ ω h h' ha hb).symm
  exact Functor.isEquivalence_of_comp_right (restrictionFunctorOfSquare c d h)
    (isoCommaMap (finitePresentationPullbackSquareIso ha).hom
      (finitePresentationPullbackSquareIso hb).inv)

end Transport

end AlgebraicGeometry

end
