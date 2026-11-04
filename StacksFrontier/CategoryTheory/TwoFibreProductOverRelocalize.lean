module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# The 2-fibre product is unchanged by relocalizing the base

Let `g : Y ⟶ Y'` be a morphism of a category `T`, and let `𝒳`, `𝒴`, `𝒮` be categories over the
slice `T/Y` with functors `F : 𝒳 ⥤ 𝒮` and `G : 𝒴 ⥤ 𝒮` over `T/Y`. Composing the three structure
functors with the relocalization functor `CategoryTheory.Over.map g` views all three as categories
over `T/Y'`, and the 2-fibre product is *not changed* by doing so: the two 2-fibre products are
isomorphic as categories, compatibly with both projections and on the nose.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.relocalizeBase`: the comparison functor from the 2-fibre
  product over `T/Y` to the one over `T/Y'`.
* `CategoryTheory.TwoFibreProductOver.unrelocalizeBase`: its inverse.
* `CategoryTheory.TwoFibreProductOver.relocalizeBaseEquivalence`: the two as an equivalence, whose
  unit and counit are identities.
* `CategoryTheory.TwoFibreProductOver.fstEquivalenceOver` and
  `CategoryTheory.TwoFibreProductOver.unrelocalizeFstEquivalenceOver`: the same equivalence read as
  an equivalence *over the first factor*, in each direction.

## Main results

* `CategoryTheory.Functor.obj_eq_of_isHomLift_comp_map` and
  `CategoryTheory.Functor.isHomLift_of_comp_map`: an object of `T/Y` over which a morphism lies
  through `p ⋙ Over.map g` is already pinned down over `p`, and so is the lifting relation.
* `CategoryTheory.TwoFibreProductOver.relocalizeBase_comp_fst`,
  `CategoryTheory.TwoFibreProductOver.relocalizeBase_comp_snd` and their `unrelocalizeBase`
  companions: both comparison functors commute strictly with the two projections.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace Over

variable {T : Type u₁} [Category.{v₁} T]

/-- Two objects of a slice category joined by a morphism whose underlying morphism of the ambient
category is an `eqToHom` are equal. -/
lemma eq_of_hom_left_eq_eqToHom {Y : T} {A B : Over Y} (ψ : A ⟶ B) (e : A.left = B.left)
    (h : ψ.left = eqToHom e) : A = B :=
  CostructuredArrow.obj_ext _ _ e (by simp [← h, Over.w ψ])

end Over

namespace Functor

variable {T : Type u₁} [Category.{v₁} T] {Y Y' : T} {g : Y ⟶ Y'}
  {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ Over Y)

/-- `Functor.IsHomLift` for `p` gives `Functor.IsHomLift` for `p ⋙ Over.map g`. -/
lemma isHomLift_comp_map {a b : 𝒳} {A B : Over Y} (k : A ⟶ B) (φ : a ⟶ b)
    (h : p.IsHomLift k φ) :
    (p ⋙ Over.map g).IsHomLift ((Over.map g).map k) φ := by
  cases h
  exact ⟨_⟩

/-- If a morphism `φ` of `𝒳` lies over `(Over.map g) k` for the composite `p ⋙ Over.map g`, then
the source of `k` is `p a` on the nose. -/
lemma obj_eq_of_isHomLift_comp_map {a b : 𝒳} {A : Over Y} (k : A ⟶ p.obj b) (φ : a ⟶ b)
    (h : (p ⋙ Over.map g).IsHomLift ((Over.map g).map k) φ) : A = p.obj a := by
  have := h
  have hA : A.left = (p.obj a).left := by
    have h1 := IsHomLift.domain_eq (p ⋙ Over.map g) ((Over.map g).map k) φ
    exact (congrArg CostructuredArrow.left h1).symm
  have hfl : k.left = eqToHom hA ≫ (p.map φ).left := by
    have h2 := congrArg Over.Hom.left
      (IsHomLift.fac (p ⋙ Over.map g) ((Over.map g).map k) φ)
    simpa [Over.eqToHom_left] using h2
  refine CostructuredArrow.obj_ext _ _ hA ?_
  have h3 : A.hom = eqToHom hA ≫ (p.obj a).hom := by
    rw [← Over.w k, hfl, Category.assoc, Over.w (p.map φ)]
  simpa using h3.symm

/-- `Functor.IsHomLift` for `p ⋙ Over.map g` gives `Functor.IsHomLift` for `p`. -/
lemma isHomLift_of_comp_map {a b : 𝒳} {A : Over Y} (k : A ⟶ p.obj b) (φ : a ⟶ b)
    (h : (p ⋙ Over.map g).IsHomLift ((Over.map g).map k) φ) : p.IsHomLift k φ := by
  obtain rfl : A = p.obj a := obj_eq_of_isHomLift_comp_map p k φ h
  obtain rfl : p.map φ = k := by
    refine (Over.OverMorphism.ext ?_).symm
    have := congrArg Over.Hom.left
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (p ⋙ Over.map g) a b ((Over.map g).map k) φ h)
    simpa using this
  exact CategoryTheory.IsHomLift.map p φ

end Functor

namespace TwoFibreProductOver

variable {T : Type u₁} [Category.{v₁} T] {Y Y' : T} (g : Y ⟶ Y')
  {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ Over Y} {p𝒴 : 𝒴 ⥤ Over Y} {p𝒮 : 𝒮 ⥤ Over Y} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- The comparison functor from the 2-fibre product over `T/Y` to the 2-fibre product of the
relocalized structure functors over `T/Y'`: an object `(U, x, y, φ)` becomes
`(U ≫ g, x, y, φ)`. -/
def relocalizeBase : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤
    TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G where
  obj P :=
    { base := (Over.map g).obj P.base
      x := P.x
      y := P.y
      hx := congrArg (Over.map g).obj P.hx
      hy := congrArg (Over.map g).obj P.hy
      iso := P.iso
      vertical := by
        simpa using Functor.isHomLift_comp_map (g := g) p𝒮 (𝟙 P.base) P.iso.hom P.vertical }
  map f :=
    { hbase := (Over.map g).map f.hbase
      a := f.a
      b := f.b
      ha := Functor.isHomLift_comp_map (g := g) p𝒳 f.hbase f.a f.ha
      hb := Functor.isHomLift_comp_map (g := g) p𝒴 f.hbase f.b f.hb
      w := f.w }
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

/-- The `𝒳`-component of the image of an object under `relocalizeBase` is that of the object. -/
@[simp] lemma relocalizeBase_obj_x (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((relocalizeBase g).obj P).x = P.x := rfl

/-- The `𝒴`-component of the image of an object under `relocalizeBase` is that of the object. -/
@[simp] lemma relocalizeBase_obj_y (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((relocalizeBase g).obj P).y = P.y := rfl

/-- For an object of the relocalized 2-fibre product, the two components lie, through `F` and
`G`, over the same object of `T/Y` and not merely over objects with the same image in `T/Y'`. -/
lemma obj_eq_of_vertical
    (Q : TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) :
    p𝒮.obj (F.obj Q.x) = p𝒮.obj (G.obj Q.y) := by
  have := Q.vertical
  have d1 := IsHomLift.domain_eq (p𝒮 ⋙ Over.map g) (𝟙 Q.base) Q.iso.hom
  have d2 := IsHomLift.codomain_eq (p𝒮 ⋙ Over.map g) (𝟙 Q.base) Q.iso.hom
  have hfac := IsHomLift.fac' (p𝒮 ⋙ Over.map g) (𝟙 Q.base) Q.iso.hom
  have e : (p𝒮.obj (F.obj Q.x)).left = (p𝒮.obj (G.obj Q.y)).left :=
    congrArg (fun A : Over Y' => A.left) (d1.trans d2.symm)
  refine Over.eq_of_hom_left_eq_eqToHom (p𝒮.map Q.iso.hom) e ?_
  simpa [Over.eqToHom_left] using congrArg Over.Hom.left hfac

/-- The `𝒳`-component of the image of a morphism under `relocalizeBase` is that of the morphism. -/
@[simp] lemma relocalizeBase_map_a {P P' : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ P') :
    ((relocalizeBase g).map f).a = f.a := rfl

/-- The `𝒴`-component of the image of a morphism under `relocalizeBase` is that of the morphism. -/
@[simp] lemma relocalizeBase_map_b {P P' : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ P') :
    ((relocalizeBase g).map f).b = f.b := rfl

/-- The underlying morphism of `T/Y` of the comparison isomorphism of an object of the relocalized
2-fibre product is the `eqToHom` of `CategoryTheory.TwoFibreProductOver.obj_eq_of_vertical`. -/
lemma map_iso_hom_eq_eqToHom
    (Q : TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) :
    p𝒮.map Q.iso.hom = eqToHom (obj_eq_of_vertical g Q) := by
  have := Q.vertical
  have hfac := IsHomLift.fac' (p𝒮 ⋙ Over.map g) (𝟙 Q.base) Q.iso.hom
  refine Over.OverMorphism.ext ?_
  simpa [Over.eqToHom_left] using congrArg Over.Hom.left hfac

section Unrelocalize

variable (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)

include hF hG in
/-- When `F` and `G` are strictly over the base, the two components of an object of the
relocalized 2-fibre product lie over the same object of `T/Y`. -/
lemma obj_base_eq
    (Q : TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) :
    p𝒴.obj Q.y = p𝒳.obj Q.x :=
  (Functor.congr_obj hG Q.y).symm.trans
    ((obj_eq_of_vertical g Q).symm.trans (Functor.congr_obj hF Q.x))

/-- The inverse comparison functor: an object of the 2-fibre product over `T/Y'` built from the
relocalized structure functors is an object of the 2-fibre product over `T/Y`, with base object
the one its `𝒳`-component lies over. -/
def unrelocalizeBase :
    TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G ⥤
      TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G where
  obj Q :=
    { base := p𝒳.obj Q.x
      x := Q.x
      y := Q.y
      hx := rfl
      hy := obj_base_eq g hF hG Q
      iso := Q.iso
      vertical := by
        refine IsHomLift.of_fac' p𝒮 _ _ (Functor.congr_obj hF Q.x)
          ((obj_eq_of_vertical g Q).symm.trans (Functor.congr_obj hF Q.x)) ?_
        rw [map_iso_hom_eq_eqToHom]
        simp }
  map {Q₁ Q₂} f := Hom.mk' f.a f.b (by
      refine Over.OverMorphism.ext ?_
      have ha := f.ha
      have hb := f.hb
      have h1 := congrArg Over.Hom.left (IsHomLift.fac' (p𝒳 ⋙ Over.map g) f.hbase f.a)
      have h2 := congrArg Over.Hom.left (IsHomLift.fac' (p𝒴 ⋙ Over.map g) f.hbase f.b)
      simp only [Functor.comp_map, Over.map_map_left, Over.eqToHom_left, Over.comp_left] at h1 h2 ⊢
      rw [h1, h2]
      simp) f.w
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

/-- The `𝒳`-component of the image of an object under `unrelocalizeBase` is that of the object. -/
@[simp] lemma unrelocalizeBase_obj_x
    (Q : TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) :
    ((unrelocalizeBase g hF hG).obj Q).x = Q.x := rfl

/-- The `𝒴`-component of the image of an object under `unrelocalizeBase` is that of the object. -/
@[simp] lemma unrelocalizeBase_obj_y
    (Q : TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) :
    ((unrelocalizeBase g hF hG).obj Q).y = Q.y := rfl

/-- The `𝒳`-component of the image of a morphism under `unrelocalizeBase` is that of the
morphism. -/
@[simp] lemma unrelocalizeBase_map_a
    {Q Q' : TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G}
    (f : Q ⟶ Q') : ((unrelocalizeBase g hF hG).map f).a = f.a := rfl

/-- The `𝒴`-component of the image of a morphism under `unrelocalizeBase` is that of the
morphism. -/
@[simp] lemma unrelocalizeBase_map_b
    {Q Q' : TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G}
    (f : Q ⟶ Q') : ((unrelocalizeBase g hF hG).map f).b = f.b := rfl

include hF hG in
/-- The two comparison functors are inverse to each other, over `T/Y`. -/
lemma relocalizeBase_comp_unrelocalizeBase :
    relocalizeBase g ⋙ unrelocalizeBase g hF hG = 𝟭 (TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) := by
  have hobj : ∀ P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G,
      (relocalizeBase g ⋙ unrelocalizeBase g hF hG).obj P = (𝟭 _).obj P := by
    rintro ⟨base, x, y, hx, hy, iso, vert⟩
    subst hx
    rfl
  refine Functor.ext hobj (fun _ _ f => Hom.ext' ?_ ?_) <;>
    simp only [Functor.comp_obj, relocalizeBase_obj_x, unrelocalizeBase_obj_x, relocalizeBase_obj_y,
      unrelocalizeBase_obj_y, Functor.comp_map, relocalizeBase_map_a, unrelocalizeBase_map_a,
      relocalizeBase_map_b, unrelocalizeBase_map_b, Functor.id_obj, Functor.id_map, comp_a, comp_b,
      eqToHom_a, eqToHom_b, eqToHom_naturality, eqToHom_refl, Category.id_comp] <;>
    exact (Category.id_comp _).symm

include hF hG in
/-- The two comparison functors are inverse to each other, over `T/Y'`. -/
lemma unrelocalizeBase_comp_relocalizeBase :
    unrelocalizeBase g hF hG ⋙ relocalizeBase g =
      𝟭 (TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) := by
  have hobj : ∀ Q : TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g)
      (p𝒮 ⋙ Over.map g) F G,
      (unrelocalizeBase g hF hG ⋙ relocalizeBase g).obj Q = (𝟭 _).obj Q := by
    rintro ⟨base, x, y, hx, hy, iso, vert⟩
    subst hx
    rfl
  refine Functor.ext hobj (fun _ _ f => Hom.ext' ?_ ?_) <;>
    simp only [Functor.comp_obj, relocalizeBase_obj_x, unrelocalizeBase_obj_x, relocalizeBase_obj_y,
      unrelocalizeBase_obj_y, Functor.comp_map, relocalizeBase_map_a, unrelocalizeBase_map_a,
      relocalizeBase_map_b, unrelocalizeBase_map_b, Functor.id_obj, Functor.id_map, comp_a, comp_b,
      eqToHom_a, eqToHom_b, eqToHom_naturality, eqToHom_refl, Category.id_comp] <;>
    exact (Category.id_comp _).symm

/-- The forward comparison functor is strictly over the first projection. -/
lemma relocalizeBase_comp_fst :
    relocalizeBase g ⋙ fst (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G =
      fst p𝒳 p𝒴 p𝒮 F G := rfl

/-- The forward comparison functor is strictly over the second projection. -/
lemma relocalizeBase_comp_snd :
    relocalizeBase g ⋙ snd (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G =
      snd p𝒳 p𝒴 p𝒮 F G := rfl

/-- The backward comparison functor is strictly over the first projection. -/
lemma unrelocalizeBase_comp_fst :
    unrelocalizeBase g hF hG ⋙ fst p𝒳 p𝒴 p𝒮 F G =
      fst (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G := rfl

/-- The backward comparison functor is strictly over the second projection. -/
lemma unrelocalizeBase_comp_snd :
    unrelocalizeBase g hF hG ⋙ snd p𝒳 p𝒴 p𝒮 F G =
      snd (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G := rfl

include hF hG in
/-- The 2-fibre product of three categories over `T/Y` is isomorphic to the 2-fibre product of
the same three categories viewed over `T/Y'` along `Over.map g`, compatibly with both
projections; the unit and counit are identities. -/
def relocalizeBaseEquivalence :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ≌
      TwoFibreProductOver (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G where
  functor := relocalizeBase g
  inverse := unrelocalizeBase g hF hG
  unitIso := eqToIso (relocalizeBase_comp_unrelocalizeBase g hF hG).symm
  counitIso := eqToIso (unrelocalizeBase_comp_relocalizeBase g hF hG)
  functor_unitIso_comp X := by
    refine Hom.ext' ?_ ?_ <;> simp only [comp_a, comp_b, id_a, id_b, eqToIso.hom,
      eqToHom_app, eqToHom_a, eqToHom_b, relocalizeBase_map_a, relocalizeBase_map_b] <;>
      exact Category.comp_id _

include hF hG in
/-- The equivalence `CategoryTheory.TwoFibreProductOver.relocalizeBaseEquivalence` as an
equivalence over the first factor. -/
def fstEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (fst p𝒳 p𝒴 p𝒮 F G)
      (fst (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) where
  hom := ⟨relocalizeBase g, relocalizeBase_comp_fst g⟩
  inv := ⟨unrelocalizeBase g hF hG, unrelocalizeBase_comp_fst g hF hG⟩
  unitIso := eqToIso (relocalizeBase_comp_unrelocalizeBase g hF hG).symm
  counitIso := eqToIso (unrelocalizeBase_comp_relocalizeBase g hF hG)
  unit_over := by ext X; simp; rfl
  counit_over := by ext X; simp; rfl

include hF hG in
/-- `CategoryTheory.TwoFibreProductOver.fstEquivalenceOver` read backwards, as an equivalence over
the first factor from the relocalized 2-fibre product. -/
def unrelocalizeFstEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (fst (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G)
      (fst p𝒳 p𝒴 p𝒮 F G) where
  hom := ⟨unrelocalizeBase g hF hG, unrelocalizeBase_comp_fst g hF hG⟩
  inv := ⟨relocalizeBase g, relocalizeBase_comp_fst g⟩
  unitIso := eqToIso (unrelocalizeBase_comp_relocalizeBase g hF hG).symm
  counitIso := eqToIso (relocalizeBase_comp_unrelocalizeBase g hF hG)
  unit_over := by ext X; simp; rfl
  counit_over := by ext X; simp; rfl

include hF hG in
/-- `CategoryTheory.TwoFibreProductOver.unrelocalizeFstEquivalenceOver` composed with a further
equivalence over the first factor. -/
def unrelocalizeFstEquivalenceOver_trans {𝒯 : Type u₅} [Category.{v₅} 𝒯] {q : 𝒯 ⥤ 𝒳}
    (E : StacksRepresentableCFG.EquivalenceOver (fst p𝒳 p𝒴 p𝒮 F G) q) :
    StacksRepresentableCFG.EquivalenceOver
      (fst (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) q :=
  (unrelocalizeFstEquivalenceOver g hF hG).trans E

include hF hG in
/-- `CategoryTheory.TwoFibreProductOver.fstEquivalenceOver` composed with a further equivalence
over the first factor. -/
def fstEquivalenceOver_trans {𝒯 : Type u₅} [Category.{v₅} 𝒯] {q : 𝒯 ⥤ 𝒳}
    (E : StacksRepresentableCFG.EquivalenceOver
      (fst (p𝒳 ⋙ Over.map g) (p𝒴 ⋙ Over.map g) (p𝒮 ⋙ Over.map g) F G) q) :
    StacksRepresentableCFG.EquivalenceOver (fst p𝒳 p𝒴 p𝒮 F G) q :=
  (fstEquivalenceOver g hF hG).trans E

end Unrelocalize

end TwoFibreProductOver

end CategoryTheory

end
