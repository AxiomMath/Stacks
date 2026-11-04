module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProductTerminal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct

/-!
# The base change of a category fibred in groupoids along a point, as arrows to the point

Let `p𝒳 : 𝒳 ⥤ 𝒞/X` and `p𝒴 : 𝒴 ⥤ 𝒞/X` be categories fibred in groupoids over a slice, let
`F : 𝒳 ⥤ 𝒴` be a 1-morphism over `𝒞/X` and let `y : 𝒞/A ⥤ 𝒴` be a 1-morphism over `𝒞/X` lying
over the slice functor of `g : A ⟶ X`. The 2-fibre product `(𝒞/A) ×_{y, 𝒴, F} 𝒳` is equivalent,
over `𝒞/X`, to the category `CostructuredArrow F (y(A/A))` of arrows `F x ⟶ y(A/A)`, with the
structure functor `c ↦ p𝒳 c.left`: an object `(U, a, x, φ)` of the 2-fibre product is the arrow
`F x ≅ y(a) ⟶ y(A/A)`, and an arrow `F x ⟶ y(A/A)` determines, `p𝒴` being fibred in groupoids,
the object `a` of `𝒞/A` it lies over and a vertical comparison `y(a) ≅ F x`
(`CategoryTheory.TwoFibreProductOver.TerminalArrow.ofCostructuredArrow`).

This file makes that construction a functor which lies strictly over `𝒞/X`, and shows it is an
equivalence.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.TerminalArrow.ofCostructuredArrowFunctor`: the functor
  `CostructuredArrow F (y(A/A)) ⥤ (𝒞/A) ×_{y, 𝒴, F} 𝒳`.

## Main results

* `CategoryTheory.TwoFibreProductOver.TerminalArrow.ofCostructuredArrowFunctor_comp`: it lies over
  `𝒞/X`.
* `CategoryTheory.TwoFibreProductOver.TerminalArrow.isEquivalence_ofCostructuredArrowFunctor`: it
  is an equivalence.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
-/

@[expose] public noncomputable section

namespace CategoryTheory.TwoFibreProductOver.TerminalArrow

universe v₀ u₀ v₁ u₁ v₂ u₂

variable {𝒞 : Type u₀} [Category.{v₀} 𝒞] {X A : 𝒞} {g : A ⟶ X}
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {p𝒳 : 𝒳 ⥤ Over X} {p𝒴 : 𝒴 ⥤ Over X} {F : 𝒳 ⥤ 𝒴} {y : Over A ⥤ 𝒴}

/-- A morphism of the total category lies over at most one morphism of the base. -/
lemma isHomLift_unique {𝒮 : Type*} [Category* 𝒮] {𝒵 : Type*} [Category* 𝒵] (p : 𝒵 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒵} {f f' : R ⟶ S} {φ : a ⟶ b} (h : p.IsHomLift f φ)
    (h' : p.IsHomLift f' φ) : f = f' :=
  (cancel_mono _).1 ((cancel_epi _).1
    ((@IsHomLift.fac' _ _ _ _ p _ _ _ _ f φ h).symm.trans
      (@IsHomLift.fac' _ _ _ _ p _ _ _ _ f' φ h')))

/-- A morphism of the 2-fibre product `(𝒞/A) ×_𝒴 𝒳` is determined by its `𝒳`-component: the
base morphism is the one that component lies over, and the morphism of `𝒞/A` is determined by
its image in `𝒞/X`. -/
lemma hom_ext_of_b {P Q : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F} {f f' : P ⟶ Q}
    (h : f.b = f'.b) : f = f' := by
  have hb : f.hbase = f'.hbase := isHomLift_unique p𝒳 f.hb (h ▸ f'.hb)
  have e' : (Over.map g).map f.a = (Over.map g).map f'.a :=
    (@IsHomLift.fac' _ _ _ _ (Over.map g) _ _ _ _ f.hbase f.a f.ha).trans
      ((congrArg (fun k => eqToHom _ ≫ k ≫ eqToHom _) hb).trans
        (@IsHomLift.fac' _ _ _ _ (Over.map g) _ _ _ _ f'.hbase f'.a f'.ha).symm)
  exact Hom.ext hb (Over.OverMorphism.ext
    (congrArg (fun k : (Over.map g).obj P.x ⟶ (Over.map g).obj Q.x => k.left) e')) h

/-- A morphism is its conjugate by two `eqToHom`s from objects to themselves. Stated at a
variable category. -/
lemma eq_eqToHom_comp_comp_eqToHom {𝒟 : Type*} [Category* 𝒟] {P Q : 𝒟} (hP : P = P)
    (hQ : Q = Q) (k : P ⟶ Q) : k = eqToHom hP ≫ k ≫ eqToHom hQ := by
  simp

/-- Two nested conjugations by `eqToHom`s which cancel. Stated at a variable category. -/
lemma eqToHom_conj_eqToHom_conj {𝒟 : Type*} [Category* 𝒟] {P P' Q Q' : 𝒟} (h1 : P = P')
    (h2 : P' = P) (k : P ⟶ Q) (h3 : Q = Q') (h4 : Q' = Q) :
    eqToHom h1 ≫ (eqToHom h2 ≫ k ≫ eqToHom h3) ≫ eqToHom h4 = k := by
  subst h1 h3
  simp

/-- Two nested conjugations by `eqToHom`s of the image of an identity. Stated at variable
categories. -/
lemma eqToHom_conj_map_id_conj {𝒟 : Type*} [Category* 𝒟] {𝒵 : Type*} [Category* 𝒵]
    (p : 𝒵 ⥤ 𝒟) {Y : 𝒵} {P P' Q' R : 𝒟} (h1 : P = P') (h2 : P' = p.obj Y) (h3 : p.obj Y = Q')
    (h4 : Q' = R) (h : P = R) :
    eqToHom h1 ≫ (eqToHom h2 ≫ p.map (𝟙 Y) ≫ eqToHom h3) ≫ eqToHom h4 = eqToHom h := by
  simp

section Functor

variable (hF : F ⋙ p𝒴 = p𝒳) (hy : y ⋙ p𝒴 = Over.map g) (hp𝒴 : p𝒴.IsFiberedInGroupoids)

/-- The arrow of the object attached to an arrow `c`, written through its comparison
isomorphism. -/
lemma ofCostructuredArrow_iso_inv_comp (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))) :
    (ofCostructuredArrow hF hy hp𝒴 c).iso.inv ≫
        y.map (toTop (ofCostructuredArrow hF hy hp𝒴 c).x) = c.hom :=
  toCostructuredArrow_ofCostructuredArrow_hom hF hy hp𝒴 c

/-- The base morphism of the morphism of the 2-fibre product lying over `dl : c.left ⟶ z.y`
is the image of `dl` in `𝒞/X`, up to the identification of the base of `z`. -/
private lemma hbase_homOfLeft (c : CostructuredArrow F (y.obj (Over.mk (𝟙 A))))
    (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) (dl : c.left ⟶ z.y)
    (key : F.map dl ≫ z.iso.inv ≫ y.map (toTop z.x) = c.hom) :
    (homOfLeft hF hy hp𝒴 c z dl key).hbase = p𝒳.map dl ≫ eqToHom z.hy := by
  change eqToHom _ ≫ (eqToHom _ ≫ p𝒳.map dl ≫ eqToHom _) ≫ eqToHom _ = _
  simp only [Category.assoc]
  erw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]

/-- The morphism of the 2-fibre product attached to a morphism of arrows. -/
def ofCostructuredArrowMap {c c' : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))} (m : c ⟶ c') :
    ofCostructuredArrow hF hy hp𝒴 c ⟶ ofCostructuredArrow hF hy hp𝒴 c' :=
  homOfLeft hF hy hp𝒴 c (ofCostructuredArrow hF hy hp𝒴 c') m.left
    ((congrArg (fun k => F.map m.left ≫ k) (ofCostructuredArrow_iso_inv_comp hF hy hp𝒴 c')).trans
      (CostructuredArrow.w m))

/-- The `𝒳`-component of the morphism attached to a morphism of arrows `m` is `m.left`. -/
@[simp]
lemma ofCostructuredArrowMap_b {c c' : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))}
    (m : c ⟶ c') : (ofCostructuredArrowMap hF hy hp𝒴 m).b = m.left :=
  rfl

/-- **The functor from arrows into `y(A/A)` to the 2-fibre product `(𝒞/A) ×_𝒴 𝒳`.** -/
def ofCostructuredArrowFunctor :
    CostructuredArrow F (y.obj (Over.mk (𝟙 A))) ⥤ TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F where
  obj := ofCostructuredArrow hF hy hp𝒴
  map := ofCostructuredArrowMap hF hy hp𝒴
  map_id _ := hom_ext_of_b rfl
  map_comp _ _ := hom_ext_of_b rfl

/-- The base morphism of the morphism attached to a morphism of arrows is the morphism the
`𝒳`-component lies over. -/
lemma ofCostructuredArrowMap_hbase {c c' : CostructuredArrow F (y.obj (Over.mk (𝟙 A)))}
    (m : c ⟶ c') : (ofCostructuredArrowMap hF hy hp𝒴 m).hbase = p𝒳.map m.left :=
  (hbase_homOfLeft hF hy hp𝒴 c (ofCostructuredArrow hF hy hp𝒴 c') m.left _).trans
    (Category.comp_id _)

/-- **The functor from arrows into `y(A/A)` to the 2-fibre product lies over `𝒞/X`**, where the
arrows lie over `𝒞/X` through their source. -/
theorem ofCostructuredArrowFunctor_comp :
    ofCostructuredArrowFunctor hF hy hp𝒴 ⋙ structureFunctor (Over.map g) p𝒳 p𝒴 y F =
      CostructuredArrow.proj F (y.obj (Over.mk (𝟙 A))) ⋙ p𝒳 :=
  Functor.ext (fun _ => rfl) fun _ _ m =>
    (ofCostructuredArrowMap_hbase hF hy hp𝒴 m).trans (eq_eqToHom_comp_comp_eqToHom _ _ _)

/-- The functor from arrows into `y(A/A)` to the 2-fibre product is faithful. -/
instance faithful_ofCostructuredArrowFunctor : (ofCostructuredArrowFunctor hF hy hp𝒴).Faithful where
  map_injective {_ _} _ _ h := CostructuredArrow.hom_ext _ _ (congrArg Hom.b h)

/-- The functor from arrows into `y(A/A)` to the 2-fibre product is full. -/
instance full_ofCostructuredArrowFunctor : (ofCostructuredArrowFunctor hF hy hp𝒴).Full where
  map_surjective {c c'} h := by
    let t := ofCostructuredArrow hF hy hp𝒴 c'
    let ha : objOver hF hy c ⟶ t.x := h.a
    let hb : c.left ⟶ c'.left := h.b
    have hw : y.map ha ≫ t.iso.hom = (liftIso hF hy hp𝒴 c).hom ≫ F.map hb := h.w
    have e : F.map hb ≫ t.iso.inv = (liftIso hF hy hp𝒴 c).inv ≫ y.map ha :=
      (Iso.comp_inv_eq t.iso).2 (((Iso.eq_inv_comp (liftIso hF hy hp𝒴 c)).2 hw.symm).trans
        (Category.assoc _ _ _).symm)
    have e2 : y.map ha ≫ y.map (toTop t.x) = y.map (toTop (objOver hF hy c)) :=
      (y.map_comp _ _).symm.trans (congrArg y.map (toTop_eq (ha ≫ toTop t.x)))
    have key : F.map hb ≫ c'.hom = c.hom :=
      (congrArg (fun k => F.map hb ≫ k)
          (ofCostructuredArrow_iso_inv_comp hF hy hp𝒴 c').symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ y.map (toTop t.x)) e).trans
          ((Category.assoc _ _ _).trans ((congrArg (fun k => (liftIso hF hy hp𝒴 c).inv ≫ k)
            e2).trans (liftInv_spec hF hy hp𝒴 c).2))))
    exact ⟨CostructuredArrow.homMk hb key, hom_ext_of_b rfl⟩

variable (hp𝒳 : p𝒳.IsFiberedInGroupoids)

/-- The morphism from the object attached to the arrow of an object of the 2-fibre product to that
object. -/
def ofToCostructuredArrowHom (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) :
    ofCostructuredArrow hF hy hp𝒴 (toCostructuredArrow g p𝒳 p𝒴 F y z) ⟶ z :=
  homOfLeft hF hy hp𝒴 (toCostructuredArrow g p𝒳 p𝒴 F y z) z (𝟙 z.y)
    ((congrArg (fun k => k ≫ z.iso.inv ≫ y.map (toTop z.x)) (F.map_id z.y)).trans
      (Category.id_comp _))

include hp𝒳 in
/-- The morphism from the object attached to the arrow of an object of the 2-fibre product to that
object is an isomorphism: it lies over an isomorphism, and the 2-fibre product is fibred in
groupoids (Stacks 0041). -/
theorem isIso_ofToCostructuredArrowHom (z : TwoFibreProductOver (Over.map g) p𝒳 p𝒴 y F) :
    IsIso (ofToCostructuredArrowHom hF hy hp𝒴 z) := by
  have hT := TwoFibreProductOver.isFiberedInGroupoids (Over.map g) p𝒳 p𝒴 y F
    (Functor.IsFiberedInGroupoids.over_map g) hp𝒳 hp𝒴 hy hF
  let S := structureFunctor (Over.map g) p𝒳 p𝒴 y F
  let φ := ofToCostructuredArrowHom hF hy hp𝒴 z
  have hbase : S.map φ = eqToHom z.hy :=
    (hbase_homOfLeft hF hy hp𝒴 (toCostructuredArrow g p𝒳 p𝒴 F y z) z (𝟙 z.y) _).trans
      (by erw [Functor.map_id, Category.id_comp])
  have : IsIso (S.map φ) := (congrArg IsIso hbase).mpr (eqToIso z.hy).isIso_hom
  have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hT (S.map φ) φ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso S (S.map φ) φ

include hp𝒳 in
/-- **The functor from arrows into `y(A/A)` to the 2-fibre product is essentially surjective**:
every object of the 2-fibre product is isomorphic to the object attached to its arrow. -/
theorem essSurj_ofCostructuredArrowFunctor : (ofCostructuredArrowFunctor hF hy hp𝒴).EssSurj where
  mem_essImage z := ⟨toCostructuredArrow g p𝒳 p𝒴 F y z,
    ⟨@asIso _ _ _ _ (ofToCostructuredArrowHom hF hy hp𝒴 z)
      (isIso_ofToCostructuredArrowHom hF hy hp𝒴 hp𝒳 z)⟩⟩

include hp𝒳 in
/-- **The 2-fibre product `(𝒞/A) ×_{y, 𝒴, F} 𝒳` is equivalent to the category of arrows
`F x ⟶ y(A/A)`.** -/
theorem isEquivalence_ofCostructuredArrowFunctor :
    (ofCostructuredArrowFunctor hF hy hp𝒴).IsEquivalence :=
  have := essSurj_ofCostructuredArrowFunctor hF hy hp𝒴 hp𝒳
  { }

end Functor

end CategoryTheory.TwoFibreProductOver.TerminalArrow

end
