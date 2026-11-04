module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# Cutting a 2-fibre product over a middle object into two

Fix a base category `𝒞` and categories `T`, `X`, `Y`, `Z` over `𝒞`, with 1-morphisms over `𝒞`

```text
t : T ⥤ X,   c : Y ⥤ X,   A : X ⥤ Z,   B : Y ⥤ Z
```

and a vertical 2-isomorphism `α : c ⋙ A ≅ B`, so that `c` is a 1-morphism from `B` to `A` in
the category of objects over `Z`. Write `𝒜 = T ×_{t ⋙ A, Z, A} X` and `ℬ = T ×_{t ⋙ A, Z, B} Y`
for the two base changes to `T` along the point `t ⋙ A` of `Z`; both are categories over `T`
through their first projections. There is a canonical section `T ⥤ 𝒜` of the first projection
of `𝒜`, namely `u ↦ (u, t u, id)`, and `c` together with `α` induces a 1-morphism `ℬ ⥤ 𝒜` over
`T`. The content of this file is that the 2-fibre product of those two 1-morphisms, formed in
the categories over `T`, is the 2-fibre product `T ×_{t, X, c} Y` over `𝒞`:

```text
T ×_X Y  ≃  ℬ ×_𝒜 T       over `T`.
```

This is the categorical form of the elementary identity `U ×_X Y = (U ×_Z Y) ×_{U ×_Z X} U` for
a point `U ⟶ X` and a morphism `Y ⟶ X` over `Z`. The comparison functor commutes with the
projections to `T` on the nose.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.baseChangeSection`: the section `T ⥤ 𝒜`, `u ↦ (u, t u, id)`.
* `CategoryTheory.TwoFibreProductOver.toBaseChange`: the comparison `T ×_X Y ⥤ ℬ` induced by `A`
  and `α`.
* `CategoryTheory.TwoFibreProductOver.middleComparison`: the comparison
  `T ×_X Y ⥤ ℬ ×_𝒜 T`, the 2-fibre product being taken over `T`.

## Main results

* `CategoryTheory.TwoFibreProductOver.isEquivalence_middleComparison`: the comparison is an
  equivalence of categories.
* `CategoryTheory.TwoFibreProductOver.middleComparison_comp_fst`: it is strictly over `T`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe vC vT vX vY vZ uC uT uX uY uZ

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {T : Type uT} [Category.{vT} T]
  {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
  {pT : T ⥤ 𝒞} {pX : X ⥤ 𝒞} {pY : Y ⥤ 𝒞} {pZ : Z ⥤ 𝒞}

section Section

variable (t : T ⥤ X) (A : X ⥤ Z)

/-- The canonical section `T ⥤ T ×_{t ⋙ A, Z, A} X` of the first projection of the base change
of `A : X ⥤ Z` along the point `t ⋙ A` of `Z`: an object `u` of `T` is sent to the triple
`(u, t u, id)`, whose comparison isomorphism is the identity of `A (t u) = (t ⋙ A) u`. -/
def baseChangeSection (ht : t ⋙ pX = pT) (hA : A ⋙ pZ = pX) :
    T ⥤ TwoFibreProductOver pT pX pZ (t ⋙ A) A where
  obj u :=
    { base := pT.obj u
      x := u
      y := t.obj u
      hx := rfl
      hy := Functor.congr_obj ht u
      iso := Iso.refl _
      vertical :=
        IsHomLift.id ((Functor.congr_obj hA (t.obj u)).trans (Functor.congr_obj ht u)) }
  map {u u'} f :=
    { hbase := pT.map f
      a := f
      b := t.map f
      ha := IsHomLift.map pT f
      hb := by
        have := IsHomLift.map pT f
        exact Functor.isHomLift_map_of_comp_eq ht (pT.map f) f
      w := by simp }
  map_id u := Hom.ext' rfl (t.map_id u)
  map_comp f g := Hom.ext' rfl (t.map_comp f g)

/-- The base of the image of `u` under the canonical section is `pT.obj u`. -/
@[simp] lemma baseChangeSection_obj_base (ht : t ⋙ pX = pT) (hA : A ⋙ pZ = pX) (u : T) :
    ((baseChangeSection (pT := pT) (pZ := pZ) t A ht hA).obj u).base = pT.obj u := rfl

/-- The `T`-component of the image of `u` under the canonical section is `u`. -/
@[simp] lemma baseChangeSection_obj_x (ht : t ⋙ pX = pT) (hA : A ⋙ pZ = pX) (u : T) :
    ((baseChangeSection (pT := pT) (pZ := pZ) t A ht hA).obj u).x = u := rfl

/-- The `X`-component of the image of `u` under the canonical section is `t.obj u`. -/
@[simp] lemma baseChangeSection_obj_y (ht : t ⋙ pX = pT) (hA : A ⋙ pZ = pX) (u : T) :
    ((baseChangeSection (pT := pT) (pZ := pZ) t A ht hA).obj u).y = t.obj u := rfl

/-- The comparison isomorphism of the image of `u` under the canonical section is the identity. -/
@[simp] lemma baseChangeSection_obj_iso (ht : t ⋙ pX = pT) (hA : A ⋙ pZ = pX) (u : T) :
    ((baseChangeSection (pT := pT) (pZ := pZ) t A ht hA).obj u).iso = Iso.refl _ := rfl

/-- The `T`-component of the image of `f` under the canonical section is `f`. -/
@[simp] lemma baseChangeSection_map_a (ht : t ⋙ pX = pT) (hA : A ⋙ pZ = pX) {u u' : T}
    (f : u ⟶ u') : ((baseChangeSection (pT := pT) (pZ := pZ) t A ht hA).map f).a = f := rfl

/-- The `X`-component of the image of `f` under the canonical section is `t.map f`. -/
@[simp] lemma baseChangeSection_map_b (ht : t ⋙ pX = pT) (hA : A ⋙ pZ = pX) {u u' : T}
    (f : u ⟶ u') : ((baseChangeSection (pT := pT) (pZ := pZ) t A ht hA).map f).b = t.map f := rfl

/-- The canonical section is a section of the first projection on the nose. -/
@[simp] lemma baseChangeSection_comp_fst (ht : t ⋙ pX = pT) (hA : A ⋙ pZ = pX) :
    baseChangeSection (pT := pT) (pZ := pZ) t A ht hA ⋙ fst pT pX pZ (t ⋙ A) A = 𝟭 T :=
  rfl

end Section

section ToBaseChange

variable (t : T ⥤ X) (c : Y ⥤ X) (A : X ⥤ Z) {B : Y ⥤ Z} (hA : A ⋙ pZ = pX)
  (α : c ⋙ A ≅ B) (hα : ∀ y : Y, pZ.IsHomLift (𝟙 (pY.obj y)) (α.hom.app y))

/-- The comparison `T ×_{t, X, c} Y ⥤ T ×_{t ⋙ A, Z, B} Y`: an object `(U, u, y, φ : t u ≅ c y)`
is sent to `(U, u, y, A φ ≫ α_y)`. This is the change of target along `A`, followed by the
reindexing of the second leg along `α`. -/
def toBaseChange :
    TwoFibreProductOver pT pY pX t c ⥤ TwoFibreProductOver pT pY pZ (t ⋙ A) B where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := A.mapIso P.iso ≪≫ α.app P.y
      vertical := by
        have h1 : pZ.IsHomLift (𝟙 P.base) (A.map P.iso.hom) := by
          have := P.vertical
          exact Functor.isHomLift_map_of_comp_eq hA (𝟙 P.base) P.iso.hom
        have h2 : pZ.IsHomLift (𝟙 P.base) (α.hom.app P.y) := by
          rw [← P.hy]
          exact hα P.y
        simpa using IsHomLift.comp pZ (𝟙 P.base) (𝟙 P.base) (A.map P.iso.hom) (α.hom.app P.y) }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.a
      b := f.b
      ha := f.ha
      hb := f.hb
      w := by
        have h1 : A.map (t.map f.a) ≫ A.map Q.iso.hom = A.map P.iso.hom ≫ A.map (c.map f.b) := by
          rw [← A.map_comp, ← A.map_comp, f.w]
        have h2 : A.map (c.map f.b) ≫ α.hom.app Q.y = α.hom.app P.y ≫ B.map f.b :=
          α.hom.naturality f.b
        change A.map (t.map f.a) ≫ A.map Q.iso.hom ≫ α.hom.app Q.y
            = (A.map P.iso.hom ≫ α.hom.app P.y) ≫ B.map f.b
        rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc] }
  map_id P := Hom.ext' rfl rfl
  map_comp f g := Hom.ext' rfl rfl

/-- `toBaseChange` preserves the base of an object. -/
@[simp] lemma toBaseChange_obj_base (P : TwoFibreProductOver pT pY pX t c) :
    ((toBaseChange (pT := pT) t c A hA α hα).obj P).base = P.base := rfl

/-- `toBaseChange` preserves the `T`-component of an object. -/
@[simp] lemma toBaseChange_obj_x (P : TwoFibreProductOver pT pY pX t c) :
    ((toBaseChange (pT := pT) t c A hA α hα).obj P).x = P.x := rfl

/-- `toBaseChange` preserves the `Y`-component of an object. -/
@[simp] lemma toBaseChange_obj_y (P : TwoFibreProductOver pT pY pX t c) :
    ((toBaseChange (pT := pT) t c A hA α hα).obj P).y = P.y := rfl

/-- The comparison isomorphism of the image of `P` under `toBaseChange` is
`A.mapIso P.iso ≪≫ α.app P.y`. -/
@[simp] lemma toBaseChange_obj_iso (P : TwoFibreProductOver pT pY pX t c) :
    ((toBaseChange (pT := pT) t c A hA α hα).obj P).iso = A.mapIso P.iso ≪≫ α.app P.y := rfl

/-- `toBaseChange` preserves the `T`-component of a morphism. -/
@[simp] lemma toBaseChange_map_a {P Q : TwoFibreProductOver pT pY pX t c} (f : P ⟶ Q) :
    ((toBaseChange (pT := pT) t c A hA α hα).map f).a = f.a := rfl

/-- `toBaseChange` preserves the `Y`-component of a morphism. -/
@[simp] lemma toBaseChange_map_b {P Q : TwoFibreProductOver pT pY pX t c} (f : P ⟶ Q) :
    ((toBaseChange (pT := pT) t c A hA α hα).map f).b = f.b := rfl

/-- `toBaseChange` preserves the base morphism of a morphism. -/
@[simp] lemma toBaseChange_map_hbase {P Q : TwoFibreProductOver pT pY pX t c} (f : P ⟶ Q) :
    ((toBaseChange (pT := pT) t c A hA α hα).map f).hbase = f.hbase := rfl

/-- The comparison `toBaseChange` commutes with the first projection on the nose. -/
@[simp] lemma toBaseChange_comp_fst :
    toBaseChange (pT := pT) t c A hA α hα ⋙ fst pT pY pZ (t ⋙ A) B = fst pT pY pX t c :=
  rfl

end ToBaseChange

section MiddleComparison

/-- If the components of `α` are vertical, so are the components of its inverse. -/
lemma isHomLift_inv_app_of_isHomLift_hom_app {c : Y ⥤ X} {A : X ⥤ Z} {B : Y ⥤ Z}
    (α : c ⋙ A ≅ B) (hα : ∀ y : Y, pZ.IsHomLift (𝟙 (pY.obj y)) (α.hom.app y)) (y : Y) :
    pZ.IsHomLift (𝟙 (pY.obj y)) (α.symm.hom.app y) := by
  have h : pZ.IsHomLift (𝟙 (pY.obj y)) (α.app y).hom := hα y
  exact IsHomLift.lift_id_inv pZ (pY.obj y) (α.app y)

/-- The 1-morphism `ℬ ⥤ 𝒜` over `T` induced by `c : Y ⥤ X` and the vertical comparison
`α : c ⋙ A ≅ B`; it is `CategoryTheory.TwoFibreProductOver.mapSnd` at those arguments. -/
abbrev middleMap (t : T ⥤ X) (c : Y ⥤ X) (A : X ⥤ Z) {B : Y ⥤ Z} (hc : c ⋙ pX = pY)
    (α : c ⋙ A ≅ B) (hα : ∀ y : Y, pZ.IsHomLift (𝟙 (pY.obj y)) (α.hom.app y)) :
    TwoFibreProductOver pT pY pZ (t ⋙ A) B ⥤ TwoFibreProductOver pT pX pZ (t ⋙ A) A :=
  mapSnd pT pY pX pZ (t ⋙ A) B A c hc α.symm (isHomLift_inv_app_of_isHomLift_hom_app α hα)

variable (t : T ⥤ X) (c : Y ⥤ X) (A : X ⥤ Z) {B : Y ⥤ Z}
  (ht : t ⋙ pX = pT) (hc : c ⋙ pX = pY) (hA : A ⋙ pZ = pX)
  (α : c ⋙ A ≅ B) (hα : ∀ y : Y, pZ.IsHomLift (𝟙 (pY.obj y)) (α.hom.app y))

/-- `middleMap` preserves the base of an object. -/
@[simp] lemma middleMap_obj_base (R : TwoFibreProductOver pT pY pZ (t ⋙ A) B) :
    ((middleMap t c A hc α hα).obj R).base = R.base := rfl

/-- `middleMap` preserves the `T`-component of an object. -/
@[simp] lemma middleMap_obj_x (R : TwoFibreProductOver pT pY pZ (t ⋙ A) B) :
    ((middleMap t c A hc α hα).obj R).x = R.x := rfl

/-- The `X`-component of the image of `R` under `middleMap` is `c.obj R.y`. -/
@[simp] lemma middleMap_obj_y (R : TwoFibreProductOver pT pY pZ (t ⋙ A) B) :
    ((middleMap t c A hc α hα).obj R).y = c.obj R.y := rfl

/-- The comparison isomorphism of the image of `R` under `middleMap` is
`R.iso ≪≫ (α.app R.y).symm`. -/
@[simp] lemma middleMap_obj_iso (R : TwoFibreProductOver pT pY pZ (t ⋙ A) B) :
    ((middleMap t c A hc α hα).obj R).iso = R.iso ≪≫ (α.app R.y).symm := rfl

/-- `middleMap` preserves the `T`-component of a morphism. -/
@[simp] lemma middleMap_map_a {R R' : TwoFibreProductOver pT pY pZ (t ⋙ A) B} (f : R ⟶ R') :
    ((middleMap t c A hc α hα).map f).a = f.a := rfl

/-- The `X`-component of the image of `f` under `middleMap` is `c.map f.b`. -/
@[simp] lemma middleMap_map_b {R R' : TwoFibreProductOver pT pY pZ (t ⋙ A) B} (f : R ⟶ R') :
    ((middleMap t c A hc α hα).map f).b = c.map f.b := rfl

/-- The comparison isomorphism of the object of `ℬ ×_𝒜 T` attached to an object
`(U, u, y, φ : t u ≅ c y)` of `T ×_{t, X, c} Y`: the isomorphism of `𝒜` with components
`(id_u, φ)`, between the section's value `(u, t u, id)` and the image of `(U, u, y, φ)` under
`ℬ ⥤ 𝒜`. -/
noncomputable def middleComparisonIso (D : TwoFibreProductOver pT pY pX t c) :
    (baseChangeSection t A ht hA).obj D.x ≅
      (middleMap t c A hc α hα).obj ((toBaseChange t c A hA α hα).obj D) :=
  isoMkVertical (U := pT.obj D.x) (Iso.refl D.x) D.iso (IsHomLift.id rfl)
    (by rw [D.hx]; exact D.vertical)
    (by simp [middleMap, mapSnd, toBaseChange, baseChangeSection])

/-- The `T`-component of the comparison isomorphism is an identity. -/
@[simp] lemma middleComparisonIso_hom_a (D : TwoFibreProductOver pT pY pX t c) :
    (middleComparisonIso t c A ht hc hA α hα D).hom.a = 𝟙 D.x := rfl

/-- The `X`-component of the comparison isomorphism is the comparison isomorphism of `D`. -/
@[simp] lemma middleComparisonIso_hom_b (D : TwoFibreProductOver pT pY pX t c) :
    (middleComparisonIso t c A ht hc hA α hα D).hom.b = D.iso.hom := rfl

/-- The comparison `T ×_{t, X, c} Y ⥤ ℬ ×_𝒜 T`, the right-hand 2-fibre product being taken in
the categories over `T`: an object `(U, u, y, φ : t u ≅ c y)` is sent to the object of the
2-fibre product over `T` with first component the image of `(U, u, y, φ)` in `ℬ`, second
component `u`, and comparison isomorphism `middleComparisonIso`. -/
noncomputable def middleComparison :
    TwoFibreProductOver pT pY pX t c ⥤
      TwoFibreProductOver (𝟭 T) (fst pT pY pZ (t ⋙ A) B) (fst pT pX pZ (t ⋙ A) A)
        (baseChangeSection t A ht hA) (middleMap t c A hc α hα) where
  obj D :=
    { base := D.x
      x := D.x
      y := (toBaseChange t c A hA α hα).obj D
      hx := rfl
      hy := rfl
      iso := middleComparisonIso t c A ht hc hA α hα D
      vertical := by
        have hmap : (fst pT pX pZ (t ⋙ A) A).map
            (middleComparisonIso t c A ht hc hA α hα D).hom = 𝟙 D.x := rfl
        rw [← hmap]
        exact IsHomLift.map _ _ }
  map {D D'} f :=
    { hbase := f.a
      a := f.a
      b := (toBaseChange t c A hA α hα).map f
      ha := IsHomLift.map (𝟭 T) f.a
      hb := by
        have hmap : (fst pT pY pZ (t ⋙ A) B).map ((toBaseChange t c A hA α hα).map f)
            = f.a := rfl
        rw [← hmap]
        exact IsHomLift.map _ _
      w := by
        refine Hom.ext' ?_ ?_
        · simp [baseChangeSection, middleMap, mapSnd, toBaseChange]
        · simpa [baseChangeSection, middleMap, mapSnd, toBaseChange] using f.w }
  map_id D := Hom.ext' rfl ((toBaseChange t c A hA α hα).map_id D)
  map_comp f g := Hom.ext' rfl ((toBaseChange t c A hA α hα).map_comp f g)

/-- The base of the image of `D` under `middleComparison` is `D.x`. -/
@[simp] lemma middleComparison_obj_base (D : TwoFibreProductOver pT pY pX t c) :
    ((middleComparison t c A ht hc hA α hα).obj D).base = D.x := rfl

/-- The first component of the image of `D` under `middleComparison` is `D.x`. -/
@[simp] lemma middleComparison_obj_x (D : TwoFibreProductOver pT pY pX t c) :
    ((middleComparison t c A ht hc hA α hα).obj D).x = D.x := rfl

/-- The second component of the image of `D` under `middleComparison` is its image under
`toBaseChange`. -/
@[simp] lemma middleComparison_obj_y (D : TwoFibreProductOver pT pY pX t c) :
    ((middleComparison t c A ht hc hA α hα).obj D).y =
      (toBaseChange t c A hA α hα).obj D := rfl

/-- The comparison isomorphism of the image of `D` under `middleComparison` is
`middleComparisonIso`. -/
@[simp] lemma middleComparison_obj_iso (D : TwoFibreProductOver pT pY pX t c) :
    ((middleComparison t c A ht hc hA α hα).obj D).iso =
      middleComparisonIso t c A ht hc hA α hα D := rfl

/-- The first component of the image of `f` under `middleComparison` is `f.a`. -/
@[simp] lemma middleComparison_map_a {D D' : TwoFibreProductOver pT pY pX t c} (f : D ⟶ D') :
    ((middleComparison t c A ht hc hA α hα).map f).a = f.a := rfl

/-- The second component of the image of `f` under `middleComparison` is its image under
`toBaseChange`. -/
@[simp] lemma middleComparison_map_b {D D' : TwoFibreProductOver pT pY pX t c} (f : D ⟶ D') :
    ((middleComparison t c A ht hc hA α hα).map f).b =
      (toBaseChange t c A hA α hα).map f := rfl

/-- The base morphism of the image of `f` under `middleComparison` is `f.a`. -/
@[simp] lemma middleComparison_map_hbase {D D' : TwoFibreProductOver pT pY pX t c} (f : D ⟶ D') :
    ((middleComparison t c A ht hc hA α hα).map f).hbase = f.a := rfl

/-- The comparison is strictly over `T`. -/
@[simp] lemma middleComparison_comp_fst :
    middleComparison t c A ht hc hA α hα ⋙
        fst (𝟭 T) (fst pT pY pZ (t ⋙ A) B) (fst pT pX pZ (t ⋙ A) A)
          (baseChangeSection t A ht hA) (middleMap t c A hc α hα) =
      fst pT pY pX t c :=
  rfl

/-- The comparison functor `T ×_X Y ⥤ ℬ ×_𝒜 T` is an equivalence of categories. -/
theorem isEquivalence_middleComparison :
    (middleComparison t c A ht hc hA α hα).IsEquivalence := by
  have hfaith : (middleComparison t c A ht hc hA α hα).Faithful := by
    constructor
    intro D D' f g h
    have ha : f.a = g.a := by simpa using congrArg Hom.a h
    have hb : f.b = g.b := by
      have h' : (toBaseChange t c A hA α hα).map f = (toBaseChange t c A hA α hα).map g := by
        simpa using congrArg Hom.b h
      simpa using congrArg Hom.b h'
    exact Hom.ext' ha hb
  have hfull : (middleComparison t c A ht hc hA α hα).Full := by
    constructor
    intro D D' φ
    have h1 := φ.ha
    have h2 := φ.hb
    have hφ : φ.a = φ.b.a :=
      (IsHomLift.fac' (𝟭 T) φ.hbase φ.a).trans
        (IsHomLift.fac' (fst pT pY pZ (t ⋙ A) B) φ.hbase φ.b).symm
    have hw : t.map φ.b.a ≫ D'.iso.hom = D.iso.hom ≫ c.map φ.b.b := by
      have h := congrArg Hom.b φ.w
      simp only [comp_b, middleComparison_obj_iso, middleComparisonIso_hom_b,
        baseChangeSection_map_b, middleMap_map_b] at h
      rwa [← hφ]
    refine ⟨⟨φ.b.hbase, φ.b.a, φ.b.b, φ.b.ha, φ.b.hb, hw⟩, ?_⟩
    refine Hom.ext' ?_ ?_
    · simpa using hφ.symm
    · exact Hom.ext' rfl rfl
  have hess : (middleComparison t c A ht hc hA α hα).EssSurj := by
    constructor
    intro P
    obtain ⟨Pbase, Px, Py, Phx, Phy, Piso, Pvert⟩ := P
    have e1 : Px = Pbase := Phx
    have e2 : Py.x = Pbase := Phy
    subst e1 e2
    have hPa : Piso.hom.a = 𝟙 Py.x := by
      have hv : (fst pT pX pZ (t ⋙ A) A).IsHomLift (𝟙 Py.x) Piso.hom := Pvert
      have h := IsHomLift.fac' (fst pT pX pZ (t ⋙ A) A) (𝟙 Py.x) Piso.hom
      simp only [fst_map, Category.id_comp, eqToHom_trans] at h
      exact h
    have hbi : Piso.hom.b ≫ Piso.inv.b = 𝟙 (t.obj Py.x) := congrArg Hom.b Piso.hom_inv_id
    have hbi' : Piso.inv.b ≫ Piso.hom.b = 𝟙 (c.obj Py.y) := congrArg Hom.b Piso.inv_hom_id
    let j : t.obj Py.x ≅ c.obj Py.y :=
      { hom := Piso.hom.b, inv := Piso.inv.b, hom_inv_id := hbi, inv_hom_id := hbi' }
    have hA1 : pT.IsHomLift (𝟙 Py.base) Piso.hom.a := hPa ▸ IsHomLift.id Py.hx
    have hS : (structureFunctor pT pX pZ (t ⋙ A) A).IsHomLift (𝟙 Py.base) Piso.hom :=
      structureFunctor_isHomLift Piso.hom (𝟙 Py.base) hA1
    have hjvert : pX.IsHomLift (𝟙 Py.base) j.hom :=
      isHomLift_b Piso.hom (𝟙 Py.base) hS
    let D : TwoFibreProductOver pT pY pX t c :=
      { base := Py.base, x := Py.x, y := Py.y, hx := Py.hx, hy := Py.hy,
        iso := j, vertical := hjvert }
    have hkey : A.map j.hom ≫ α.hom.app Py.y = Py.iso.hom := by
      have hw : A.map (t.map Piso.hom.a) ≫ Py.iso.hom ≫ (α.app Py.y).inv =
          𝟙 (A.obj (t.obj Py.x)) ≫ A.map j.hom := Piso.hom.w
      have h2 : A.map (t.map Piso.hom.a) = 𝟙 ((t ⋙ A).obj Py.x) := by simp [hPa]
      simp only [h2, Category.id_comp] at hw
      simp [← hw]
    let jB : (toBaseChange t c A hA α hα).obj D ≅ Py :=
      isoMkVertical (U := Py.base) (Iso.refl Py.x) (Iso.refl Py.y)
        (IsHomLift.id Py.hx) (IsHomLift.id Py.hy)
        (by simpa [D] using hkey.symm)
    refine ⟨D, ⟨?_⟩⟩
    refine isoMkVertical (U := Py.x) (Iso.refl Py.x) jB (IsHomLift.id rfl) ?_ ?_
    · have hmap : (fst pT pY pZ (t ⋙ A) B).map jB.hom = 𝟙 Py.x := rfl
      rw [← hmap]
      exact IsHomLift.map _ _
    · refine Hom.ext' ?_ ?_
      · simp only [middleComparison_obj_x, baseChangeSection_obj_x, middleMap_obj_x,
          Iso.refl_hom, Functor.map_id, Category.id_comp, hPa, middleComparison_obj_y,
          middleComparison_obj_iso, comp_a, toBaseChange_obj_x, middleComparisonIso_hom_a,
          middleMap_map_a, D, j, jB]
        exact (Category.comp_id (𝟙 Py.x)).symm
      · simp only [middleComparison_obj_x, baseChangeSection_obj_y, middleMap_obj_y,
          Iso.refl_hom, Functor.map_id, Category.id_comp, middleComparison_obj_y,
          middleComparison_obj_iso, comp_b, toBaseChange_obj_y, middleComparisonIso_hom_b,
          middleMap_map_b, D, j, jB]
        exact (Category.comp_id Piso.hom.b).symm.trans
          (congrArg (fun g => Piso.hom.b ≫ g) (CategoryTheory.Functor.map_id c Py.y).symm)
  exact Functor.IsEquivalence.mk

end MiddleComparison
end CategoryTheory.TwoFibreProductOver

end
