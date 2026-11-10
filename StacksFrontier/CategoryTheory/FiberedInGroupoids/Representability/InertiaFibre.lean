module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import StacksCore.CategoryTheory.Inertia

/-!
# The fibre of the relative inertia over a point is the presheaf of vertical automorphisms

Let `p : X ⥤ 𝒞` be fibred in groupoids, `F : X ⥤ 𝒴` a functor over `𝒞` (`F ⋙ q = p`) to a
category whose structure functor `q` is faithful, and `Y : 𝒯 ⥤ X` a point over `p𝒯 : 𝒯 ⥤ 𝒞`
(`Y ⋙ p = p𝒯`). The 2-fibre product `𝒯 ×_{Y, X, π} I_{X/𝒴}` of `Y` with the forgetful functor
`π` of the relative inertia is equivalent over `𝒯` to the category of elements of the presheaf
on `𝒯` of vertical automorphisms of `Y`: an object `(a, (x, α), Y a ≅ x)` corresponds to the
conjugate of `α` to `Y a`, and conversely a vertical automorphism `m` of `Y a` gives the object
`(a, (Y a, m), 𝟙)`. Faithfulness of `q` makes every vertical automorphism satisfy the condition
`F m = 𝟙` defining the relative inertia.

This is the categorical half of reading the base change of the inertia projection of an
algebraic stack along a scheme-valued point as the automorphism presheaf of that point.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.InertiaFibre.equivalenceOver`: the equivalence over `𝒯`.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver.InertiaFibre

open DiagonalFibre (VertHom isHomLift_eqToHom_of_id)

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴} {Y : 𝒯 ⥤ X}

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  RelativeInertia.π

/-- The 2-fibre product of the point `Y` with the forgetful functor of the relative inertia. -/
abbrev Fib (p : X ⥤ 𝒞) (p𝒯 : 𝒯 ⥤ 𝒞) (F : X ⥤ 𝒴) (Y : 𝒯 ⥤ X) :=
  TwoFibreProductOver p𝒯 (RelativeInertia.π F ⋙ p) p Y (RelativeInertia.π F)

/-- A vertical endomorphism is sent to an identity by a functor over `𝒞` to a category with
faithful structure functor. -/
lemma map_eq_id_of_isHomLift (hF : F ⋙ q = p) [q.Faithful] {x : X} {c : 𝒞} (φ : x ⟶ x)
    (hφ : p.IsHomLift (𝟙 c) φ) : F.map φ = 𝟙 (F.obj x) := by
  have := hφ
  apply q.map_injective
  have h := Functor.congr_hom hF φ
  rw [IsHomLift.fac' p (𝟙 c) φ] at h
  simp only [Functor.comp_map, Category.id_comp, eqToHom_trans] at h
  rw [h, q.map_id]
  simp

/-- An endomorphism `α` with `F α = 𝟙` lies over an identity. -/
lemma isHomLift_auto (hF : F ⋙ q = p) (A : RelativeInertia F) :
    p.IsHomLift (𝟙 (p.obj A.obj)) A.auto.asIso.hom := by
  refine IsHomLift.of_fac' p _ _ rfl rfl ?_
  have h := Functor.congr_hom hF A.auto.asIso.hom
  rw [Functor.comp_map, A.cond, q.map_id] at h
  simp only [eqToHom_refl, Category.comp_id]
  simpa [eqToHom_comp_iff, comp_eqToHom_iff] using h.symm

/-- The conjugate of the automorphism of an object of the 2-fibre product to `Y a`. -/
def conjOf (A : Fib p p𝒯 F Y) : Y.obj A.x ⟶ Y.obj A.x :=
  A.iso.hom ≫ A.y.auto.asIso.hom ≫ A.iso.inv

/-- The inverse of the structure isomorphism of an object of the 2-fibre product is vertical. -/
private lemma isHomLift_inv_iso (A : Fib p p𝒯 F Y) : p.IsHomLift (𝟙 A.base) A.iso.inv := by
  have hv := A.vertical
  simpa using IsHomLift.lift_id_inv_isIso p A.base A.iso.hom

lemma isHomLift_conjOf (hF : F ⋙ q = p) (A : Fib p p𝒯 F Y) :
    p.IsHomLift (𝟙 (p𝒯.obj A.x)) (conjOf A) := by
  have hv := A.vertical
  have hvi := isHomLift_inv_iso A
  have ha : p.IsHomLift (𝟙 A.base) A.y.auto.asIso.hom := by
    have h := isHomLift_auto hF A.y
    have hy : p.obj A.y.obj = A.base := A.hy
    rw [hy] at h
    exact h
  have h : p.IsHomLift (𝟙 A.base ≫ 𝟙 A.base ≫ 𝟙 A.base) (conjOf A) := by
    unfold conjOf; infer_instance
  simp only [Category.id_comp] at h
  rw [A.hx]
  exact h

/-- The section of the presheaf of vertical automorphisms attached to an object. -/
def sectOf (hF : F ⋙ q = p) (A : Fib p p𝒯 F Y) : VertHom p p𝒯 Y Y A.x :=
  ⟨conjOf A, isHomLift_conjOf hF A⟩

lemma inv_comp_map (A B : Fib p p𝒯 F Y) (u : A ⟶ B) :
    A.iso.inv ≫ Y.map u.a = u.b.hom ≫ B.iso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact u.w

lemma conjOf_naturality (A B : Fib p p𝒯 F Y) (u : A ⟶ B) :
    conjOf A ≫ Y.map u.a = Y.map u.a ≫ conjOf B := by
  have hw : A.iso.hom ≫ u.b.hom = Y.map u.a ≫ B.iso.hom := u.w.symm
  have hc : A.y.auto.asIso.hom ≫ u.b.hom = u.b.hom ≫ B.y.auto.asIso.hom := u.b.comm.symm
  unfold conjOf
  calc (A.iso.hom ≫ A.y.auto.asIso.hom ≫ A.iso.inv) ≫ Y.map u.a
      = A.iso.hom ≫ A.y.auto.asIso.hom ≫ (A.iso.inv ≫ Y.map u.a) := by simp only [Category.assoc]
    _ = A.iso.hom ≫ (A.y.auto.asIso.hom ≫ u.b.hom) ≫ B.iso.inv := by
        rw [inv_comp_map A B u]; simp only [Category.assoc]
    _ = (A.iso.hom ≫ u.b.hom) ≫ B.y.auto.asIso.hom ≫ B.iso.inv := by
        rw [hc]; simp only [Category.assoc]
    _ = Y.map u.a ≫ B.iso.hom ≫ B.y.auto.asIso.hom ≫ B.iso.inv := by
        rw [hw]; simp only [Category.assoc]

variable (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p) (hY : Y ⋙ p = p𝒯)

/-- The presheaf on `𝒯` of vertical automorphisms of the point `Y`. -/
noncomputable abbrev autPresheaf : 𝒯ᵒᵖ ⥤ Type v₃ := VertHom.presheaf hp hY hY

/-- The comparison functor from the 2-fibre product to the category of elements. -/
noncomputable def toElements :
    Fib p p𝒯 F Y ⥤ (presheafOfCategories (autPresheaf hp hY ⋙ typeToCat)).obj where
  obj A := ⟨A.x, Discrete.mk (sectOf hF A)⟩
  map {A B} u := ⟨u.a, Discrete.eqToHom
    (VertHom.restrict_uniq hp hY hY u.a (sectOf hF B) (sectOf hF A)
      (conjOf_naturality A B u))⟩
  map_id _ := PresheafOfCategories.elements_hom_ext _ _ rfl
  map_comp _ _ := PresheafOfCategories.elements_hom_ext _ _ rfl

variable [q.Faithful]

include hp in
lemma isIso_vertHom (a : 𝒯) (m : VertHom p p𝒯 Y Y a) : IsIso m.1 := by
  have hm := m.2
  have := hp.isStronglyCartesian_homLift (𝟙 (p𝒯.obj a)) m.1
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p𝒯.obj a)) m.1

/-- The object of the inertia attached to a vertical automorphism of `Y a`. -/
noncomputable def inertiaOf (a : 𝒯) (m : VertHom p p𝒯 Y Y a) : RelativeInertia F :=
  haveI := isIso_vertHom hp a m
  { obj := Y.obj a
    auto := Aut.of (asIso m.1)
    cond := map_eq_id_of_isHomLift hF m.1 m.2 }

/-- The object of the 2-fibre product attached to a vertical automorphism of `Y a`. -/
noncomputable def objOf (a : 𝒯) (m : VertHom p p𝒯 Y Y a) : Fib p p𝒯 F Y where
  base := p𝒯.obj a
  x := a
  y := inertiaOf hp hF a m
  hx := rfl
  hy := Functor.congr_obj hY a
  iso := Iso.refl _
  vertical := IsHomLift.id (Functor.congr_obj hY a)

lemma isHomLift_π_map {A B : RelativeInertia F} {c d : 𝒞} (f : c ⟶ d) (b : A ⟶ B)
    (h : p.IsHomLift f b.hom) : (RelativeInertia.π F ⋙ p).IsHomLift f b :=
  IsHomLift.of_fac' _ _ _ (IsHomLift.domain_eq p f b.hom) (IsHomLift.codomain_eq p f b.hom)
    (IsHomLift.fac' p f b.hom)

include hF in
/-- The comparison functor from the category of elements back to the 2-fibre product. -/
noncomputable def ofElements :
    (presheafOfCategories (autPresheaf hp hY ⋙ typeToCat)).obj ⥤ Fib p p𝒯 F Y where
  obj P := objOf hp hF hY P.base P.fiber.as
  map {P Q} u :=
    { hbase := p𝒯.map u.base
      a := u.base
      b :=
        { hom := Y.map u.base
          comm := by
            have hfib : P.fiber.as = VertHom.restrict hp hY hY u.base Q.fiber.as :=
              Discrete.eq_of_hom u.fiber
            change Y.map u.base ≫ Q.fiber.as.1 = P.fiber.as.1 ≫ Y.map u.base
            rw [hfib]
            exact (VertHom.restrict_fac hp hY hY u.base Q.fiber.as).symm }
      ha := IsHomLift.map p𝒯 u.base
      hb := isHomLift_π_map _ _ (VertHom.isHomLift_map hY u.base)
      w := by
        change Y.map u.base ≫ 𝟙 _ = 𝟙 _ ≫ Y.map u.base
        rw [Category.comp_id, Category.id_comp] }
  map_id P := Hom.ext' rfl (RelativeInertiaHom.ext (Y.map_id P.base))
  map_comp u v := Hom.ext' rfl (RelativeInertiaHom.ext (Y.map_comp u.base v.base))

lemma isHomLift_iso_inv (A : Fib p p𝒯 F Y) : p.IsHomLift (𝟙 A.base) A.iso.inv :=
  isHomLift_inv_iso A

lemma isHomLift_eqToHom_of_base (A : Fib p p𝒯 F Y) {Z W : X} (φ : Z ⟶ W) {R T : 𝒞}
    (e : R = T) (hR : A.base = R)
    (h : p.IsHomLift (𝟙 A.base) φ) : p.IsHomLift (eqToHom e) φ := by
  subst hR e
  exact h

/-- The unit of the equivalence. -/
noncomputable def unitIso : 𝟭 (Fib p p𝒯 F Y) ≅ toElements hp hF hY ⋙ ofElements hp hF hY :=
  NatIso.ofComponents
    (fun A =>
      { hom :=
          { hbase := eqToHom A.hx.symm
            a := 𝟙 A.x
            b :=
              { hom := A.iso.inv
                comm := by
                  change A.iso.inv ≫ conjOf A = A.y.auto.asIso.hom ≫ A.iso.inv
                  simp [conjOf] }
            ha := isHomLift_eqToHom_of_id p𝒯 (𝟙 A.x) A.hx rfl A.hx.symm (IsHomLift.id rfl)
            hb := isHomLift_π_map _ _
              (isHomLift_eqToHom_of_base A A.iso.inv A.hx.symm rfl (isHomLift_iso_inv A))
            w := by
              change Y.map (𝟙 A.x) ≫ 𝟙 _ = A.iso.hom ≫ A.iso.inv
              simp }
        inv :=
          { hbase := eqToHom A.hx
            a := 𝟙 A.x
            b :=
              { hom := A.iso.hom
                comm := by
                  change A.iso.hom ≫ A.y.auto.asIso.hom = conjOf A ≫ A.iso.hom
                  simp [conjOf] }
            ha := isHomLift_eqToHom_of_id p𝒯 (𝟙 A.x) rfl A.hx A.hx (IsHomLift.id rfl)
            hb := by
              have hv := A.vertical
              exact isHomLift_π_map _ _ (isHomLift_eqToHom_of_base A A.iso.hom A.hx A.hx.symm hv)
            w := by
              change Y.map (𝟙 A.x) ≫ A.iso.hom = 𝟙 _ ≫ A.iso.hom
              simp }
        hom_inv_id := Hom.ext' (Category.id_comp _) (RelativeInertiaHom.ext A.iso.inv_hom_id)
        inv_hom_id := Hom.ext' (Category.id_comp _) (RelativeInertiaHom.ext A.iso.hom_inv_id) })
    (by
      intro A B u
      refine Hom.ext' ?_ (RelativeInertiaHom.ext ?_)
      · change u.a ≫ 𝟙 B.x = 𝟙 A.x ≫ u.a
        rw [Category.comp_id, Category.id_comp]
      · change u.b.hom ≫ B.iso.inv = A.iso.inv ≫ Y.map u.a
        exact (inv_comp_map A B u).symm)

lemma sectOf_objOf (a : 𝒯) (m : VertHom p p𝒯 Y Y a) : sectOf hF (objOf hp hF hY a m) = m := by
  apply VertHom.ext
  change 𝟙 _ ≫ m.1 ≫ 𝟙 _ = m.1
  simp

/-- The counit of the equivalence. -/
noncomputable def counitIso :
    ofElements hp hF hY ⋙ toElements hp hF hY ≅
      𝟭 (presheafOfCategories (autPresheaf hp hY ⋙ typeToCat)).obj :=
  NatIso.ofComponents
    (fun P =>
      { hom := ⟨𝟙 P.base, Discrete.eqToHom
          ((sectOf_objOf hp hF hY P.base P.fiber.as).trans
            (VertHom.restrict_id hp hY hY P.fiber.as).symm)⟩
        inv := ⟨𝟙 P.base, Discrete.eqToHom
          ((sectOf_objOf hp hF hY P.base P.fiber.as).symm.trans
            (VertHom.restrict_id hp hY hY (sectOf hF (objOf hp hF hY P.base P.fiber.as))).symm)⟩
        hom_inv_id := PresheafOfCategories.elements_hom_ext _ _ (by
          change 𝟙 P.base ≫ 𝟙 P.base = 𝟙 P.base
          exact Category.id_comp _)
        inv_hom_id := PresheafOfCategories.elements_hom_ext _ _ (by
          change 𝟙 P.base ≫ 𝟙 P.base = 𝟙 P.base
          exact Category.id_comp _) })
    (by
      intro P Q u
      refine PresheafOfCategories.elements_hom_ext _ _ ?_
      change u.base ≫ 𝟙 Q.base = 𝟙 P.base ≫ u.base
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The fibre of the relative inertia over a point is the presheaf of vertical
automorphisms.** The first projection of `𝒯 ×_{Y, X, π} I_{X/𝒴}` is equivalent over `𝒯` to the
category of elements of the presheaf of vertical automorphisms of `Y`. -/
noncomputable def equivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (fst p𝒯 (RelativeInertia.π F ⋙ p) p Y (RelativeInertia.π F))
      (presheafOfCategories (autPresheaf hp hY ⋙ typeToCat)).p where
  hom := ⟨toElements hp hF hY, rfl⟩
  inv := ⟨ofElements hp hF hY, rfl⟩
  unitIso := unitIso hp hF hY
  counitIso := counitIso hp hF hY
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
    intro A
    refine IsHomLift.of_fac' (fst p𝒯 (RelativeInertia.π F ⋙ p) p Y (RelativeInertia.π F))
      _ _ rfl rfl ?_
    change 𝟙 A.x = _
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
    intro P
    refine IsHomLift.of_fac'
      (presheafOfCategories (autPresheaf hp hY ⋙ typeToCat)).p _ _ rfl rfl ?_
    change 𝟙 P.base = _
    simp only [Category.id_comp, eqToHom_trans]
    rfl

universe t in
include hF in
/-- **The inertia criterion as a comparison of presheaves.** The first projection of
`𝒯 ×_{Y, X, π} I_{X/𝒴}` is equivalent over `𝒯` to the category of elements of a presheaf of sets
`G` exactly when `G` and the presheaf of vertical automorphisms of `Y` become isomorphic after
both are lifted to a common value universe. -/
theorem nonempty_equivalenceOver_fst_iff (G : 𝒯ᵒᵖ ⥤ Type t) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
        (fst p𝒯 (RelativeInertia.π F ⋙ p) p Y (RelativeInertia.π F))
        (presheafOfCategories (G ⋙ typeToCat)).p) ↔
      Nonempty (autPresheaf hp hY ⋙ uliftFunctor.{t, v₃} ≅ G ⋙ uliftFunctor.{v₃, t}) := by
  constructor
  · rintro ⟨E⟩
    exact (PresheafOfCategories.nonempty_equivalenceOver_iff (autPresheaf hp hY) G).1
      ⟨(equivalenceOver hp hF hY).symm.trans E⟩
  · intro h
    obtain ⟨e⟩ := (PresheafOfCategories.nonempty_equivalenceOver_iff (autPresheaf hp hY) G).2 h
    exact ⟨(equivalenceOver hp hF hY).trans e⟩

end CategoryTheory.TwoFibreProductOver.InertiaFibre

end
