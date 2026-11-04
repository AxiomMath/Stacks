module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationStageColimit

/-!
# The equivalence out of the filtered `2`-colimit

For a cofiltered system of stages `Z i` under `U` and under `M`, with `N` mapping to `U` and to `M`
compatibly, base change out of the stages assembles into a functor
`AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit.glueingColimitFunctor` from the
filtered `2`-colimit of the categories `FP_{Z i}` to the `2`-fibre product `FP_U ×_{FP_N} FP_M`.
This functor is an equivalence of categories as soon as the three conditions of
`AlgebraicGeometry.FinitePresentationSpacesOver.IsGlueingColimitEquivalence` hold.

All names below are in the namespace `AlgebraicGeometry.FinitePresentationSpacesOver`.

## Main definitions

* `StageColimit.evalCone`: the image of a morphism over a stage under base change along a cone of
  morphisms into the stages.
* `StageColimit.glueingColimitFunctor`: the comparison functor out of the filtered `2`-colimit,
  which on an object over a stage is the comparison functor `FP_{Z i} ⥤ FP_U ×_{FP_N} FP_M` of that
  stage, and on a germ is the base change of a representing morphism.
* `StageColimit.germIso`: a germ whose representing morphism is invertible, as an isomorphism of
  the colimit.
* `StageColimit.stageIso`: the isomorphism between an object of the colimit and its base change to
  an earlier stage.

## Main results

* `StageColimit.essSurj_glueingColimitFunctor`, `StageColimit.faithful_glueingColimitFunctor`,
  `StageColimit.full_glueingColimitFunctor`: the comparison functor is essentially surjective,
  faithful and full.
* `StageColimit.isEquivalence_glueingColimitFunctor`: the comparison functor out of the filtered
  `2`-colimit is an equivalence of categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePresentationSpacesOver

/-- A morphism whose composite with the forward direction of an isomorphism is the identity is its
inverse. -/
theorem iso_inv_eq_of_hom_comp_eq_id {C : Type*} [Category C] {P Q : C} (α : P ≅ Q) {g : Q ⟶ P}
    (h : α.hom ≫ g = 𝟙 P) : g = α.inv := by
  rw [← Category.id_comp g, ← α.inv_hom_id, Category.assoc, h, Category.comp_id]

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The left component of the inverse of the comparison between the comparison functors of a square
read over two bases. -/
theorem glueingFunctorFactorIso_inv_app_hom_left {Zi Zj U' M' N' : BigFppfOver B S hS}
    {jUi : U' ⟶ Zi} {jMi : M' ⟶ Zi} {jUj : U' ⟶ Zj} {jMj : M' ⟶ Zj} {ez : Zj ⟶ Zi}
    {iu : N' ⟶ U'} {im : N' ⟶ M'} (wi : iu ≫ jUi = im ≫ jMi) (wj : iu ≫ jUj = im ≫ jMj)
    (hU : jUj ≫ ez = jUi) (hM : jMj ≫ ez = jMi)
    (A : FinitePresentationSpacesOver B S hS Zi) :
    ((glueingFunctorFactorIso B S hS wi wj hU hM).inv.app A).hom.left =
      (baseChangeFactorIso B S hS hU).inv.app A := by
  refine iso_inv_eq_of_hom_comp_eq_id (Iso.app (baseChangeFactorIso B S hS hU) A) ?_
  rw [Iso.app_hom, ← glueingFunctorFactorIso_hom_app_hom_left B S hS wi wj hU hM A]
  exact congrArg (fun m ↦ m.hom.left)
    ((glueingFunctorFactorIso B S hS wi wj hU hM).hom_inv_id_app A)

/-- The right component of the inverse of the comparison between the comparison functors of a
square read over two bases. -/
theorem glueingFunctorFactorIso_inv_app_hom_right {Zi Zj U' M' N' : BigFppfOver B S hS}
    {jUi : U' ⟶ Zi} {jMi : M' ⟶ Zi} {jUj : U' ⟶ Zj} {jMj : M' ⟶ Zj} {ez : Zj ⟶ Zi}
    {iu : N' ⟶ U'} {im : N' ⟶ M'} (wi : iu ≫ jUi = im ≫ jMi) (wj : iu ≫ jUj = im ≫ jMj)
    (hU : jUj ≫ ez = jUi) (hM : jMj ≫ ez = jMi)
    (A : FinitePresentationSpacesOver B S hS Zi) :
    ((glueingFunctorFactorIso B S hS wi wj hU hM).inv.app A).hom.right =
      (baseChangeFactorIso B S hS hM).inv.app A := by
  refine iso_inv_eq_of_hom_comp_eq_id (Iso.app (baseChangeFactorIso B S hS hM) A) ?_
  rw [Iso.app_hom, ← glueingFunctorFactorIso_hom_app_hom_right B S hS wi wj hU hM A]
  exact congrArg (fun m ↦ m.hom.right)
    ((glueingFunctorFactorIso B S hS wi wj hU hM).hom_inv_id_app A)

end

namespace StageColimit

/-! ### Evaluating a germ along a cone -/

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {I : Type u}
  [Category.{u} I] {Z : I ⥤ BigFppfOver B S hS}

/-- The image of a morphism over a stage under base change along a cone of morphisms into the
stages. -/
noncomputable def evalCone {P : BigFppfOver B S hS} (q : (i : I) → (P ⟶ Z.obj i))
    (hq : ∀ {i j : I} (e : j ⟶ i), q j ≫ Z.map e = q i) (X Y : StageColimit B S hS Z) {k : I}
    (A : k ⟶ X.idx) (Bb : k ⟶ Y.idx)
    (f : (baseChange B S hS (Z.map A)).obj X.obj ⟶ (baseChange B S hS (Z.map Bb)).obj Y.obj) :
    (baseChange B S hS (q X.idx)).obj X.obj ⟶ (baseChange B S hS (q Y.idx)).obj Y.obj :=
  shift B S hS X.obj Y.obj (q k) (hq A) (hq Bb) f

variable {P : BigFppfOver B S hS} (q : (i : I) → (P ⟶ Z.obj i))
  (hq : ∀ {i j : I} (e : j ⟶ i), q j ≫ Z.map e = q i)

/-- Evaluating along a cone does not depend on the stage a germ is represented at. -/
theorem evalCone_push (X Y : StageColimit B S hS Z) {k l : I} (A : k ⟶ X.idx) (Bb : k ⟶ Y.idx)
    (c : l ⟶ k) {a : l ⟶ X.idx} {b : l ⟶ Y.idx} (ha : c ≫ A = a) (hb : c ≫ Bb = b)
    (f : (baseChange B S hS (Z.map A)).obj X.obj ⟶ (baseChange B S hS (Z.map Bb)).obj Y.obj) :
    evalCone B S hS q hq X Y a b (push X Y A Bb c ha hb f) =
      evalCone B S hS q hq X Y A Bb f :=
  (shift_shift B S hS X.obj Y.obj (Z.map c) (q l) (map_comp_eq Z ha) (map_comp_eq Z hb)
    (hq a) (hq b) (by rw [hq c]; exact hq A) (by rw [hq c]; exact hq Bb) f).trans
    (shift_congr B S hS X.obj Y.obj _ _ (hq A) (hq Bb) (hq c) f)

/-- Evaluating along a cone is compatible with composition. -/
theorem evalCone_comp (X Y W : StageColimit B S hS Z) {k : I} (A : k ⟶ X.idx) (Mm : k ⟶ Y.idx)
    (C : k ⟶ W.idx)
    (f : (baseChange B S hS (Z.map A)).obj X.obj ⟶ (baseChange B S hS (Z.map Mm)).obj Y.obj)
    (g : (baseChange B S hS (Z.map Mm)).obj Y.obj ⟶ (baseChange B S hS (Z.map C)).obj W.obj) :
    evalCone B S hS q hq X W A C (f ≫ g) =
      evalCone B S hS q hq X Y A Mm f ≫ evalCone B S hS q hq Y W Mm C g :=
  shift_comp B S hS X.obj Y.obj W.obj (q k) (hq A) (hq Mm) (hq C) f g

/-- Evaluating the identity along a cone gives the identity. -/
theorem evalCone_id (X : StageColimit B S hS Z) {k : I} (A : k ⟶ X.idx) :
    evalCone B S hS q hq X X A A (𝟙 ((baseChange B S hS (Z.map A)).obj X.obj)) =
      𝟙 ((baseChange B S hS (q X.idx)).obj X.obj) :=
  shift_id B S hS X.obj (q k) (hq A)

end

/-! ### Germs that are isomorphisms -/

section Iso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {I : Type u}
  [Category.{u} I] [IsCofiltered I] {Z : I ⥤ BigFppfOver B S hS}

/-- A germ whose representing morphism is invertible, as an isomorphism of the colimit. -/
noncomputable def germIso {X Y : StageColimit B S hS Z} {k : I} (a : k ⟶ X.idx) (b : k ⟶ Y.idx)
    (φ : (baseChange B S hS (Z.map a)).obj X.obj ≅ (baseChange B S hS (Z.map b)).obj Y.obj) :
    X ≅ Y where
  hom := germ ⟨k, a, b, φ.hom⟩
  inv := germ ⟨k, b, a, φ.inv⟩
  hom_inv_id := by
    refine (germ_eq_germ_iff.2 (Rel.trans (rel_compRep_compRepAt (⟨k, a, b, φ.hom⟩ : Rep X Y)
      (⟨k, b, a, φ.inv⟩ : Rep Y X) (𝟙 k) (𝟙 k) (Category.id_comp a) (Category.id_comp b)
      (Category.id_comp b) (Category.id_comp a)) ?_)).trans (germ_idRep X)
    have key : compRepAt (⟨k, a, b, φ.hom⟩ : Rep X Y) (⟨k, b, a, φ.inv⟩ : Rep Y X) (𝟙 k) (𝟙 k)
          (Category.id_comp a) (Category.id_comp b) (Category.id_comp b) (Category.id_comp a) =
        (idRep X).pushTo a (Category.comp_id a) (Category.comp_id a) := by
      refine Rep.mk_eq_mk ?_
      change push X Y a b (𝟙 k) (Category.id_comp a) (Category.id_comp b) φ.hom ≫
          push Y X b a (𝟙 k) (Category.id_comp b) (Category.id_comp a) φ.inv =
        push X X (𝟙 X.idx) (𝟙 X.idx) a (Category.comp_id a) (Category.comp_id a)
          (𝟙 ((baseChange B S hS (Z.map (𝟙 X.idx))).obj X.obj))
      rw [← push_comp X Y X a b a (𝟙 k) (Category.id_comp a) (Category.id_comp b)
        (Category.id_comp a) φ.hom φ.inv, φ.hom_inv_id, push_id, push_id]
    rw [key]
    exact rel_push (idRep X) a (Category.comp_id a) (Category.comp_id a)
  inv_hom_id := by
    refine (germ_eq_germ_iff.2 (Rel.trans (rel_compRep_compRepAt (⟨k, b, a, φ.inv⟩ : Rep Y X)
      (⟨k, a, b, φ.hom⟩ : Rep X Y) (𝟙 k) (𝟙 k) (Category.id_comp b) (Category.id_comp a)
      (Category.id_comp a) (Category.id_comp b)) ?_)).trans (germ_idRep Y)
    have key : compRepAt (⟨k, b, a, φ.inv⟩ : Rep Y X) (⟨k, a, b, φ.hom⟩ : Rep X Y) (𝟙 k) (𝟙 k)
          (Category.id_comp b) (Category.id_comp a) (Category.id_comp a) (Category.id_comp b) =
        (idRep Y).pushTo b (Category.comp_id b) (Category.comp_id b) := by
      refine Rep.mk_eq_mk ?_
      change push Y X b a (𝟙 k) (Category.id_comp b) (Category.id_comp a) φ.inv ≫
          push X Y a b (𝟙 k) (Category.id_comp a) (Category.id_comp b) φ.hom =
        push Y Y (𝟙 Y.idx) (𝟙 Y.idx) b (Category.comp_id b) (Category.comp_id b)
          (𝟙 ((baseChange B S hS (Z.map (𝟙 Y.idx))).obj Y.obj))
      rw [← push_comp Y X Y b a b (𝟙 k) (Category.id_comp b) (Category.id_comp a)
        (Category.id_comp b) φ.inv φ.hom, φ.inv_hom_id, push_id, push_id]
    rw [key]
    exact rel_push (idRep Y) b (Category.comp_id b) (Category.comp_id b)

/-- The isomorphism between an object of the colimit and its base change to an earlier stage. -/
noncomputable def stageIso (X : StageColimit B S hS Z) {k : I} (a : k ⟶ X.idx) :
    X ≅ (⟨k, (baseChange B S hS (Z.map a)).obj X.obj⟩ : StageColimit B S hS Z) :=
  germIso a (𝟙 k)
    (Iso.app (baseChangeFactorIso B S hS (map_comp_eq Z (Category.id_comp a))) X.obj)

/-- Two representatives of germs between the same objects can be restricted to a common stage with
the same transitions. -/
theorem exists_common_stage {X Y : StageColimit B S hS Z} (r r' : Rep X Y) :
    ∃ (n : I) (p : n ⟶ r.idx) (q : n ⟶ r'.idx), p ≫ r.toSrc = q ≫ r'.toSrc ∧
      p ≫ r.toTgt = q ≫ r'.toTgt := by
  obtain ⟨n₀, p₀, q₀, -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) r.idx r'.idx
  obtain ⟨n, e, k₁, k₂, -, -⟩ := exists_eq_comp₄ (p₀ ≫ r.toSrc) (q₀ ≫ r'.toSrc)
    (p₀ ≫ r.toTgt) (q₀ ≫ r'.toTgt) (𝟙 n₀) (𝟙 n₀) (𝟙 n₀) (𝟙 n₀)
  exact ⟨n, e ≫ p₀, e ≫ q₀, by simpa only [Category.assoc] using k₁,
    by simpa only [Category.assoc] using k₂⟩

end Iso

/-! ### The comparison functor out of the colimit -/

section Functor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U M N : BigFppfOver B S hS} {iU : N ⟶ U} {iM : N ⟶ M} {I : Type u} [Category.{u} I]
  [IsCofiltered I] {Z : I ⥤ BigFppfOver B S hS} {jU : (i : I) → (U ⟶ Z.obj i)}
  {jM : (i : I) → (M ⟶ Z.obj i)} (w : ∀ i, iU ≫ jU i = iM ≫ jM i)
  (hjU : ∀ {i j : I} (e : j ⟶ i), jU j ≫ Z.map e = jU i)
  (hjM : ∀ {i j : I} (e : j ⟶ i), jM j ≫ Z.map e = jM i)

/-- Two morphisms of the `2`-fibre product with the same two components agree. -/
theorem isoComma_hom_ext {A₁ A₂ : IsoComma (baseChange B S hS iU) (baseChange B S hS iM)}
    (f g : A₁ ⟶ A₂) (hl : f.hom.left = g.hom.left) (hr : f.hom.right = g.hom.right) : f = g :=
  ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hl hr)

/-- The comparison morphism of the `2`-fibre product attached to a representative of a germ. -/
noncomputable def glueingColimitMapRep {X Y : StageColimit B S hS Z} (r : Rep X Y) :
    (glueingFunctor B S hS (w X.idx)).obj X.obj ⟶
      (glueingFunctor B S hS (w Y.idx)).obj Y.obj :=
  (glueingFunctorFactorIso B S hS (w X.idx) (w r.idx) (hjU r.toSrc)
      (hjM r.toSrc)).hom.app X.obj ≫
    (glueingFunctor B S hS (w r.idx)).map r.hom ≫
      (glueingFunctorFactorIso B S hS (w Y.idx) (w r.idx) (hjU r.toTgt)
        (hjM r.toTgt)).inv.app Y.obj

omit [IsCofiltered I] in
/-- The left component of the comparison morphism attached to a representative is its evaluation
along `jU`. -/
theorem glueingColimitMapRep_hom_left {X Y : StageColimit B S hS Z} (r : Rep X Y) :
    (glueingColimitMapRep B S hS w hjU hjM r).hom.left =
      evalCone B S hS jU hjU X Y r.toSrc r.toTgt r.hom := by
  show ((glueingFunctorFactorIso B S hS (w X.idx) (w r.idx) (hjU r.toSrc)
        (hjM r.toSrc)).hom.app X.obj).hom.left ≫
      ((glueingFunctor B S hS (w r.idx)).map r.hom).hom.left ≫
        ((glueingFunctorFactorIso B S hS (w Y.idx) (w r.idx) (hjU r.toTgt)
          (hjM r.toTgt)).inv.app Y.obj).hom.left = _
  rw [glueingFunctorFactorIso_hom_app_hom_left, glueingFunctorFactorIso_inv_app_hom_left]
  rfl

omit [IsCofiltered I] in
/-- The right component of the comparison morphism attached to a representative is its evaluation
along `jM`. -/
theorem glueingColimitMapRep_hom_right {X Y : StageColimit B S hS Z} (r : Rep X Y) :
    (glueingColimitMapRep B S hS w hjU hjM r).hom.right =
      evalCone B S hS jM hjM X Y r.toSrc r.toTgt r.hom := by
  show ((glueingFunctorFactorIso B S hS (w X.idx) (w r.idx) (hjU r.toSrc)
        (hjM r.toSrc)).hom.app X.obj).hom.right ≫
      ((glueingFunctor B S hS (w r.idx)).map r.hom).hom.right ≫
        ((glueingFunctorFactorIso B S hS (w Y.idx) (w r.idx) (hjU r.toTgt)
          (hjM r.toTgt)).inv.app Y.obj).hom.right = _
  rw [glueingFunctorFactorIso_hom_app_hom_right, glueingFunctorFactorIso_inv_app_hom_right]
  rfl

omit [IsCofiltered I] in
/-- The comparison morphism attached to a representative only depends on its germ. -/
theorem glueingColimitMapRep_congr {X Y : StageColimit B S hS Z} {r r' : Rep X Y}
    (h : Rel r r') : glueingColimitMapRep B S hS w hjU hjM r =
      glueingColimitMapRep B S hS w hjU hjM r' := by
  obtain ⟨l, u, v, a, b, hu, hv, hu', hv', he⟩ := h
  refine isoComma_hom_ext B S hS _ _ ?_ ?_
  · rw [glueingColimitMapRep_hom_left, glueingColimitMapRep_hom_left,
      ← evalCone_push B S hS jU hjU X Y r.toSrc r.toTgt u hu hv r.hom,
      ← evalCone_push B S hS jU hjU X Y r'.toSrc r'.toTgt v hu' hv' r'.hom, he]
  · rw [glueingColimitMapRep_hom_right, glueingColimitMapRep_hom_right,
      ← evalCone_push B S hS jM hjM X Y r.toSrc r.toTgt u hu hv r.hom,
      ← evalCone_push B S hS jM hjM X Y r'.toSrc r'.toTgt v hu' hv' r'.hom, he]

/-- The comparison functor out of the filtered `2`-colimit of the categories of algebraic spaces of
finite presentation over the stages, to the `2`-fibre product `FP_U ×_{FP_N} FP_M`. On an object
over a stage it is the comparison functor of that stage, and on a germ it is the base change of a
representing morphism. -/
noncomputable def glueingColimitFunctor :
    StageColimit B S hS Z ⥤ IsoComma (baseChange B S hS iU) (baseChange B S hS iM) where
  obj X := (glueingFunctor B S hS (w X.idx)).obj X.obj
  map {_ _} f := Quotient.liftOn f (glueingColimitMapRep B S hS w hjU hjM)
    fun _ _ h ↦ glueingColimitMapRep_congr B S hS w hjU hjM h
  map_id X := by
    change glueingColimitMapRep B S hS w hjU hjM (idRep X) = 𝟙 _
    refine isoComma_hom_ext B S hS _ _ ?_ ?_
    · rw [glueingColimitMapRep_hom_left]
      exact evalCone_id B S hS jU hjU X (𝟙 X.idx)
    · rw [glueingColimitMapRep_hom_right]
      exact evalCone_id B S hS jM hjM X (𝟙 X.idx)
  map_comp {X Y W} f g := by
    induction f using Quotient.ind with
    | _ r =>
    induction g using Quotient.ind with
    | _ r' =>
    change glueingColimitMapRep B S hS w hjU hjM (compRep r r') =
      glueingColimitMapRep B S hS w hjU hjM r ≫ glueingColimitMapRep B S hS w hjU hjM r'
    refine isoComma_hom_ext B S hS _ _ ?_ ?_
    · change (glueingColimitMapRep B S hS w hjU hjM (compRep r r')).hom.left =
        (glueingColimitMapRep B S hS w hjU hjM r).hom.left ≫
          (glueingColimitMapRep B S hS w hjU hjM r').hom.left
      rw [glueingColimitMapRep_hom_left, glueingColimitMapRep_hom_left,
        glueingColimitMapRep_hom_left]
      change evalCone B S hS jU hjU X W ((compStage r r').fst ≫ r.toSrc)
          ((compStage r r').snd ≫ r'.toTgt)
          (push X Y r.toSrc r.toTgt (compStage r r').fst rfl rfl r.hom ≫
            push Y W r'.toSrc r'.toTgt (compStage r r').snd (compStage r r').w.symm rfl r'.hom) =
        _
      rw [evalCone_comp B S hS jU hjU X Y W _ ((compStage r r').fst ≫ r.toTgt) _,
        evalCone_push B S hS jU hjU X Y r.toSrc r.toTgt (compStage r r').fst rfl rfl r.hom,
        evalCone_push B S hS jU hjU Y W r'.toSrc r'.toTgt (compStage r r').snd
          (compStage r r').w.symm rfl r'.hom]
      rfl
    · change (glueingColimitMapRep B S hS w hjU hjM (compRep r r')).hom.right =
        (glueingColimitMapRep B S hS w hjU hjM r).hom.right ≫
          (glueingColimitMapRep B S hS w hjU hjM r').hom.right
      rw [glueingColimitMapRep_hom_right, glueingColimitMapRep_hom_right,
        glueingColimitMapRep_hom_right]
      change evalCone B S hS jM hjM X W ((compStage r r').fst ≫ r.toSrc)
          ((compStage r r').snd ≫ r'.toTgt)
          (push X Y r.toSrc r.toTgt (compStage r r').fst rfl rfl r.hom ≫
            push Y W r'.toSrc r'.toTgt (compStage r r').snd (compStage r r').w.symm rfl r'.hom) =
        _
      rw [evalCone_comp B S hS jM hjM X Y W _ ((compStage r r').fst ≫ r.toTgt) _,
        evalCone_push B S hS jM hjM X Y r.toSrc r.toTgt (compStage r r').fst rfl rfl r.hom,
        evalCone_push B S hS jM hjM Y W r'.toSrc r'.toTgt (compStage r r').snd
          (compStage r r').w.symm rfl r'.hom]
      rfl

/-- The comparison functor sends an object over a stage to its image under the comparison functor
of that stage. -/
@[simp]
theorem glueingColimitFunctor_obj (X : StageColimit B S hS Z) :
    (glueingColimitFunctor B S hS w hjU hjM).obj X =
      (glueingFunctor B S hS (w X.idx)).obj X.obj :=
  rfl

/-- The comparison functor sends a germ to the comparison morphism of a representative. -/
@[simp]
theorem glueingColimitFunctor_map_germ {X Y : StageColimit B S hS Z} (r : Rep X Y) :
    (glueingColimitFunctor B S hS w hjU hjM).map (germ r) =
      glueingColimitMapRep B S hS w hjU hjM r :=
  rfl

/-! ### The equivalence -/

/-- The comparison functor out of the colimit is essentially surjective. -/
theorem essSurj_glueingColimitFunctor
    (h : IsGlueingColimitEquivalence B S hS Z jU jM w hjU hjM) :
    (glueingColimitFunctor B S hS w hjU hjM).EssSurj := by
  refine ⟨fun T => ?_⟩
  obtain ⟨i, Xo, hξ⟩ := h.essSurj T
  exact ⟨⟨i, Xo⟩, hξ⟩

/-- The comparison functor out of the colimit is faithful. -/
theorem faithful_glueingColimitFunctor
    (h : IsGlueingColimitEquivalence B S hS Z jU jM w hjU hjM) :
    (glueingColimitFunctor B S hS w hjU hjM).Faithful := by
  refine ⟨fun {X Y} f g hfg => ?_⟩
  obtain ⟨r, rfl⟩ := exists_germ_eq f
  obtain ⟨r', rfl⟩ := exists_germ_eq g
  obtain ⟨n, p, q, hs, ht⟩ := exists_common_stage r r'
  have key : ∀ {P : BigFppfOver B S hS} (c : (i : I) → P ⟶ Z.obj i)
      (hq : ∀ {i j : I} (e : j ⟶ i), c j ≫ Z.map e = c i),
      evalCone B S hS c hq X Y r.toSrc r.toTgt r.hom =
        evalCone B S hS c hq X Y r'.toSrc r'.toTgt r'.hom →
      (baseChange B S hS (c n)).map (push X Y r.toSrc r.toTgt p rfl rfl r.hom) =
        (baseChange B S hS (c n)).map
          (push X Y r'.toSrc r'.toTgt q hs.symm ht.symm r'.hom) := by
    intro P c hq hev
    refine baseChange_map_eq_of_shift_eq B S hS X.obj Y.obj (c n) (hq (p ≫ r.toSrc))
      (hq (p ≫ r.toTgt)) ?_
    show evalCone B S hS c hq X Y (p ≫ r.toSrc) (p ≫ r.toTgt) _ =
      evalCone B S hS c hq X Y (p ≫ r.toSrc) (p ≫ r.toTgt) _
    rw [evalCone_push B S hS c hq X Y r.toSrc r.toTgt p rfl rfl r.hom,
      evalCone_push B S hS c hq X Y r'.toSrc r'.toTgt q hs.symm ht.symm r'.hom, hev]
  obtain ⟨l, e, hle⟩ := h.faithful n _ _ _ _ (isoComma_hom_ext B S hS _ _
    (key jU hjU (by
      rw [← glueingColimitMapRep_hom_left B S hS w hjU hjM r,
        ← glueingColimitMapRep_hom_left B S hS w hjU hjM r']
      exact congrArg (fun m ↦ m.hom.left) hfg))
    (key jM hjM (by
      rw [← glueingColimitMapRep_hom_right B S hS w hjU hjM r,
        ← glueingColimitMapRep_hom_right B S hS w hjU hjM r']
      exact congrArg (fun m ↦ m.hom.right) hfg)))
  refine ((germ_eq_germ_iff.2 (rel_push r p rfl rfl).symm).trans
    (germ_eq_germ_iff.2 ?_)).trans (germ_eq_germ_iff.2 (rel_push r' q hs.symm ht.symm))
  refine ⟨l, e, e, e ≫ (p ≫ r.toSrc), e ≫ (p ≫ r.toTgt), rfl, rfl, rfl, rfl, ?_⟩
  exact shift_congr_hom B S hS X.obj Y.obj (Z.map e) (map_comp_eq Z rfl) (map_comp_eq Z rfl) hle

omit [IsCofiltered I] in
/-- A germ represented at a stage by a morphism `f` whose base changes along `jU` and `jM` are
compatible with the components `mL` and `mR` of a morphism `m` of the `2`-fibre product is sent to
`m` by the comparison functor. -/
theorem glueingColimitMapRep_eq_of_full {k l : I}
    {Xo Yo : FinitePresentationSpacesOver B S hS (Z.obj k)} (e : l ⟶ k)
    (f : (baseChange B S hS (Z.map e)).obj Xo ⟶ (baseChange B S hS (Z.map e)).obj Yo)
    (m : (glueingFunctor B S hS (w k)).obj Xo ⟶ (glueingFunctor B S hS (w k)).obj Yo)
    (mL : (baseChange B S hS (jU k)).obj Xo ⟶ (baseChange B S hS (jU k)).obj Yo)
    (mR : (baseChange B S hS (jM k)).obj Xo ⟶ (baseChange B S hS (jM k)).obj Yo)
    (hmL : m.hom.left = mL) (hmR : m.hom.right = mR)
    (hLe : mL ≫ (baseChangeFactorIso B S hS (hjU e)).hom.app Yo =
      (baseChangeFactorIso B S hS (hjU e)).hom.app Xo ≫ (baseChange B S hS (jU l)).map f)
    (hRe : mR ≫ (baseChangeFactorIso B S hS (hjM e)).hom.app Yo =
      (baseChangeFactorIso B S hS (hjM e)).hom.app Xo ≫ (baseChange B S hS (jM l)).map f) :
    glueingColimitMapRep B S hS w hjU hjM
        (⟨l, e, e, f⟩ : Rep (⟨k, Xo⟩ : StageColimit B S hS Z) ⟨k, Yo⟩) = m := by
  refine isoComma_hom_ext B S hS _ _ ?_ ?_
  · rw [glueingColimitMapRep_hom_left, hmL]
    show (baseChangeFactorIso B S hS (hjU e)).hom.app Xo ≫
        (baseChange B S hS (jU l)).map f ≫
          (baseChangeFactorIso B S hS (hjU e)).inv.app Yo = mL
    rw [← Category.assoc, ← hLe, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  · rw [glueingColimitMapRep_hom_right, hmR]
    show (baseChangeFactorIso B S hS (hjM e)).hom.app Xo ≫
        (baseChange B S hS (jM l)).map f ≫
          (baseChangeFactorIso B S hS (hjM e)).inv.app Yo = mR
    rw [← Category.assoc, ← hRe, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- The comparison functor out of the colimit is full. -/
theorem full_glueingColimitFunctor
    (h : IsGlueingColimitEquivalence B S hS Z jU jM w hjU hjM) :
    (glueingColimitFunctor B S hS w hjU hjM).Full := by
  refine ⟨fun {X Y} m => ?_⟩
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs (C := I) X.idx Y.idx
  obtain ⟨l, e, f, hLe, hRe⟩ := h.full k ((baseChange B S hS (Z.map a)).obj X.obj)
    ((baseChange B S hS (Z.map b)).obj Y.obj)
    ((glueingColimitFunctor B S hS w hjU hjM).map (stageIso X a).inv ≫ m ≫
      (glueingColimitFunctor B S hS w hjU hjM).map (stageIso Y b).hom)
  have hmid : (glueingColimitFunctor B S hS w hjU hjM).map (germ (⟨l, e, e, f⟩ :
        Rep (⟨k, (baseChange B S hS (Z.map a)).obj X.obj⟩ : StageColimit B S hS Z)
          ⟨k, (baseChange B S hS (Z.map b)).obj Y.obj⟩)) =
      (glueingColimitFunctor B S hS w hjU hjM).map (stageIso X a).inv ≫ m ≫
        (glueingColimitFunctor B S hS w hjU hjM).map (stageIso Y b).hom :=
    glueingColimitMapRep_eq_of_full B S hS w hjU hjM e f _ _ _ rfl rfl hLe hRe
  refine ⟨(stageIso X a).hom ≫ germ (⟨l, e, e, f⟩ :
      Rep (⟨k, (baseChange B S hS (Z.map a)).obj X.obj⟩ : StageColimit B S hS Z)
        ⟨k, (baseChange B S hS (Z.map b)).obj Y.obj⟩) ≫ (stageIso Y b).inv, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, hmid]
  simp only [Category.assoc, Iso.map_hom_inv_id_assoc, Iso.map_hom_inv_id, Category.comp_id]

/-- The comparison functor out of the filtered `2`-colimit of the categories of algebraic spaces of
finite presentation over the stages is an equivalence of categories onto the `2`-fibre product
`FP_U ×_{FP_N} FP_M`. -/
theorem isEquivalence_glueingColimitFunctor
    (h : IsGlueingColimitEquivalence B S hS Z jU jM w hjU hjM) :
    (glueingColimitFunctor B S hS w hjU hjM).IsEquivalence where
  faithful := faithful_glueingColimitFunctor B S hS w hjU hjM h
  full := full_glueingColimitFunctor B S hS w hjU hjM h
  essSurj := essSurj_glueingColimitFunctor B S hS w hjU hjM h

end Functor

end StageColimit

end AlgebraicGeometry.FinitePresentationSpacesOver

end
