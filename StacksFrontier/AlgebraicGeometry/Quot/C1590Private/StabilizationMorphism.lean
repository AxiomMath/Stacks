module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack

/-!
# A base-change compatible construction on families of curves is a 1-morphism of stacks

This is the mechanism of the proof of Stacks 0E8B, in the (abuse of) language of Properties of
Stacks, Section 04XA: a construction `X ↦ Y` on families of curves, given together with a morphism
`c : X → Y` over the base which pins `Y` down up to unique isomorphism and which is compatible
with base change, defines a 1-morphism between the substacks of `Curves` it relates.

The construction is encoded by a relation `R X Y b c`, read "`c : X → Y`, over the isomorphism of
bases `b`, is a model of `X`". `IsModelRelation R` records what the argument needs:

* `w`: a model lies over its morphism of bases;
* `exists_hom`, `hom_ext`: two models of the same family are related by a unique morphism of
  families compatible with the two contractions (uniqueness up to unique isomorphism);
* `baseChange`: the base change of a model along a morphism of families is a model.

From this and the existence of models of the families with a property `P`, landing in families with
a property `Q`, `modelFunctor` is the 1-morphism `Curves^P ⟶ Curves^Q` of categories fibred in
groupoids over the big fppf site of `Spec(ℤ)` sending a family to a model of it.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsModelRelation`: the three conditions on the relation.
* `AlgebraicGeometry.C1590Private.Model`: a model of a family over the same base.
* `AlgebraicGeometry.C1590Private.modelFunctor`: the 1-morphism `Curves^P ⟶ Curves^Q`.

## Main results

* `AlgebraicGeometry.C1590Private.exists_model_of_exists`: a model with a base isomorphic to that
  of `X` gives a model over the base of `X` itself.
* `AlgebraicGeometry.C1590Private.existsUnique_modelHom`: a morphism of families lifts uniquely to
  a morphism between any chosen models compatible with the contractions.
* `AlgebraicGeometry.C1590Private.modelFunctor_obj` and
  `AlgebraicGeometry.C1590Private.modelFunctor_map`: the 1-morphism sends a family to a model of
  it, and a morphism of families to the morphism of models compatible with the contractions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- `schemeSpaceMap` sends `eqToHom h` to the `eqToHom` of the induced equality of schemes. -/
theorem schemeSpaceMap_eqToHom {U V : BigFppfOver B integerBase hZ} (h : U = V) :
    schemeSpaceMap (eqToHom h) = eqToHom (congrArg schemeSpace h) := by
  subst h
  simp [schemeSpaceMap]
  rfl

/-- The base map of the identity of a family of curves is the identity of its base. -/
@[simp]
theorem curveFamily_id_baseMap (X : CurveFamily B hZ) : (𝟙 X : X ⟶ X).baseMap = 𝟙 X.base := rfl

/-- The total map of the identity of a family of curves is the identity of its total space. -/
@[simp]
theorem curveFamily_id_totalMap (X : CurveFamily B hZ) :
    (𝟙 X : X ⟶ X).totalMap = 𝟙 X.total := rfl

/-- The base map of a composite of morphisms of families is the composite of the base maps. -/
@[simp]
theorem curveFamily_comp_baseMap {X Y Z : CurveFamily B hZ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).baseMap = f.baseMap ≫ g.baseMap := rfl

/-- The total map of a composite of morphisms of families is the composite of the total maps. -/
@[simp]
theorem curveFamily_comp_totalMap {X Y Z : CurveFamily B hZ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).totalMap = f.totalMap ≫ g.totalMap := rfl

/-- The conditions on a relation `R X Y b c` ("`c : X → Y` over `b : X.base ⟶ Y.base` is a
model of `X`") making the formation of models a morphism of stacks: models lie over their base
map, are unique up to unique isomorphism, and are stable under base change. -/
structure IsModelRelation
    (R : ∀ X Y : CurveFamily B hZ, (X.base ⟶ Y.base) → (X.total ⟶ Y.total) → Prop) : Prop where
  /-- A model lies over its morphism of bases. -/
  w {X Y : CurveFamily B hZ} {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total} :
    R X Y b c → c ≫ Y.toBase = X.toBase ≫ schemeSpaceMap b
  /-- Two models of the same family are related by a morphism of families compatible with the
  base maps and with the contractions. -/
  exists_hom {X Y₁ Y₂ : CurveFamily B hZ} {b₁ : X.base ⟶ Y₁.base} {c₁ : X.total ⟶ Y₁.total}
    {b₂ : X.base ⟶ Y₂.base} {c₂ : X.total ⟶ Y₂.total} :
    R X Y₁ b₁ c₁ → R X Y₂ b₂ c₂ →
      ∃ e : Y₁ ⟶ Y₂, b₁ ≫ e.baseMap = b₂ ∧ c₁ ≫ e.totalMap = c₂
  /-- That morphism is unique. -/
  hom_ext {X Y₁ Y₂ : CurveFamily B hZ} {b₁ : X.base ⟶ Y₁.base} {c₁ : X.total ⟶ Y₁.total}
    {b₂ : X.base ⟶ Y₂.base} {c₂ : X.total ⟶ Y₂.total} :
    R X Y₁ b₁ c₁ → R X Y₂ b₂ c₂ → ∀ e e' : Y₁ ⟶ Y₂,
      b₁ ≫ e.baseMap = b₂ → c₁ ≫ e.totalMap = c₂ →
      b₁ ≫ e'.baseMap = b₂ → c₁ ≫ e'.totalMap = c₂ → e = e'
  /-- The base change of a model along a morphism of families is a model. -/
  baseChange {X' X Y' Y : CurveFamily B hZ} (φ : X' ⟶ X) (ψ : Y' ⟶ Y)
    {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total} (b' : X'.base ⟶ Y'.base)
    (c' : X'.total ⟶ Y'.total) :
    R X Y b c → IsIso b' → b' ≫ ψ.baseMap = φ.baseMap ≫ b →
      c' ≫ ψ.totalMap = φ.totalMap ≫ c → c' ≫ Y'.toBase = X'.toBase ≫ schemeSpaceMap b' →
      R X' Y' b' c'

variable {R : ∀ X Y : CurveFamily B hZ, (X.base ⟶ Y.base) → (X.total ⟶ Y.total) → Prop}

/-- A model of a family of curves `X` over the base of `X` itself. -/
structure Model (R : ∀ X Y : CurveFamily B hZ, (X.base ⟶ Y.base) → (X.total ⟶ Y.total) → Prop)
    (X : CurveFamily B hZ) where
  /-- The family of the model. -/
  family : CurveFamily B hZ
  /-- It lies over the base of `X`. -/
  base_eq : family.base = X.base
  /-- The contraction `X → Y`. -/
  contraction : X.total ⟶ family.total
  /-- It is a model of `X`. -/
  isModel : R X family (eqToHom base_eq.symm) contraction

/-- **Base change of a model.** Given a model `c : X → Y` over `b` and a morphism of families
`φ : X' ⟶ X`, the base change of `Y` along `φ.baseMap ≫ b` carries a contraction from `X'` which
is a model of `X'` over the base of `X'`, compatible with `φ` and with `c`. -/
theorem exists_pullback_model (hR : IsModelRelation R) {X' X Y : CurveFamily B hZ} (φ : X' ⟶ X)
    {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total} (hc : R X Y b c) :
    ∃ (Y' : CurveFamily B hZ) (ψ : Y' ⟶ Y) (h : Y'.base = X'.base) (c' : X'.total ⟶ Y'.total),
      ψ.baseMap = eqToHom h ≫ φ.baseMap ≫ b ∧ c' ≫ ψ.totalMap = φ.totalMap ≫ c ∧
        R X' Y' (eqToHom h.symm) c' := by
  obtain ⟨Y', ψ, h, hψ⟩ := CurveFamily.exists_hom_baseMap_eq Y (φ.baseMap ≫ b)
  have hw : (φ.totalMap ≫ c) ≫ Y.toBase =
      (X'.toBase ≫ schemeSpaceMap (eqToHom h.symm)) ≫ schemeSpaceMap ψ.baseMap := by
    rw [Category.assoc, hR.w hc, ← Category.assoc, φ.cartesian.w, Category.assoc,
      Category.assoc, ← schemeSpaceMap_comp, ← schemeSpaceMap_comp, hψ, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  refine ⟨Y', ψ, h, ψ.cartesian.lift _ _ hw, hψ, ψ.cartesian.lift_fst _ _ hw, ?_⟩
  refine hR.baseChange φ ψ _ _ hc inferInstance ?_ (ψ.cartesian.lift_fst _ _ hw)
    (ψ.cartesian.lift_snd _ _ hw)
  rw [hψ, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- A model of `X` over a base isomorphic to that of `X` yields a model over the base of `X`. -/
theorem exists_model_of_exists (hR : IsModelRelation R) {X Y : CurveFamily B hZ}
    {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total} (hc : R X Y b c) :
    ∃ (m : Model R X) (ψ : m.family ⟶ Y), m.contraction ≫ ψ.totalMap = c := by
  obtain ⟨Y', ψ, h, c', -, hc', hR'⟩ := exists_pullback_model hR (𝟙 X) hc
  exact ⟨⟨Y', h, c', hR'⟩, ψ, by simpa using hc'⟩

/-- **A morphism of families lifts uniquely to models.** For a morphism of families `φ : X' ⟶ X`
and models `m'` of `X'` and `m` of `X`, there is a unique morphism of families from `m'` to `m`
over the base map of `φ` compatible with the two contractions. -/
theorem existsUnique_modelHom (hR : IsModelRelation R) {X' X : CurveFamily B hZ} (φ : X' ⟶ X)
    (m' : Model R X') (m : Model R X) :
    ∃! ψ : m'.family ⟶ m.family,
      ψ.baseMap = eqToHom m'.base_eq ≫ φ.baseMap ≫ eqToHom m.base_eq.symm ∧
        m'.contraction ≫ ψ.totalMap = φ.totalMap ≫ m.contraction := by
  obtain ⟨Y'', ψ₀, h, c'', hψ₀, hc'', hR''⟩ := exists_pullback_model hR φ m.isModel
  have key : ∀ ψ : m'.family ⟶ m.family,
      ψ.baseMap = eqToHom m'.base_eq ≫ φ.baseMap ≫ eqToHom m.base_eq.symm →
        m'.contraction ≫ ψ.totalMap = φ.totalMap ≫ m.contraction →
        ∃ θ : m'.family ⟶ Y'', θ ≫ ψ₀ = ψ ∧
          eqToHom m'.base_eq.symm ≫ θ.baseMap = eqToHom h.symm ∧
            m'.contraction ≫ θ.totalMap = c'' := by
    intro ψ hψb hψc
    have hf : (eqToHom (m'.base_eq.trans h.symm) : m'.family.base ⟶ Y''.base) ≫ ψ₀.baseMap =
        ψ.baseMap := by
      rw [hψ₀, hψb, eqToHom_trans_assoc]
    obtain ⟨θ, ⟨hθb, hθ⟩, -⟩ :=
      (CurveDeformation.curvesProjectionOver_isFiberedInGroupoids (B := B)
        (hZ := hZ)).unique_lift ψ₀ ψ _ hf
    have hθb' : θ.baseMap = eqToHom (m'.base_eq.trans h.symm) := hθb
    refine ⟨θ, hθ, by rw [hθb', eqToHom_trans], ?_⟩
    apply ψ₀.cartesian.hom_ext
    · rw [Category.assoc, ← curveFamily_comp_totalMap, hθ, hψc, hc'']
    · rw [Category.assoc, θ.cartesian.w, ← Category.assoc, hR.w m'.isModel, hR.w hR'',
        Category.assoc, ← schemeSpaceMap_comp, hθb', eqToHom_trans]
  obtain ⟨e, he, hec⟩ := hR.exists_hom m'.isModel hR''
  refine ⟨e ≫ ψ₀, ⟨?_, ?_⟩, ?_⟩
  · change e.baseMap ≫ ψ₀.baseMap = _
    have he' : e.baseMap = eqToHom m'.base_eq ≫ eqToHom h.symm := by
      rw [← he]
      simp
    rw [he', hψ₀]
    simp
  · change m'.contraction ≫ e.totalMap ≫ ψ₀.totalMap = _
    rw [← Category.assoc, hec, hc'']
  · rintro ψ ⟨hψb, hψc⟩
    obtain ⟨θ, rfl, hθb, hθc⟩ := key ψ hψb hψc
    rw [hR.hom_ext m'.isModel hR'' θ e hθb hθc he hec]

/-- A model over a base isomorphic to that of `X` gives a model over the base of `X`. -/
theorem nonempty_model (hR : IsModelRelation R) {X Y : CurveFamily B hZ}
    {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total} (hc : R X Y b c) : Nonempty (Model R X) :=
  let ⟨m, _⟩ := exists_model_of_exists hR hc
  ⟨m⟩

/-- The morphism of models over a morphism of families, compatible with the contractions. -/
def modelHom (hR : IsModelRelation R) {X' X : CurveFamily B hZ} (φ : X' ⟶ X)
    (m' : Model R X') (m : Model R X) : m'.family ⟶ m.family :=
  (existsUnique_modelHom hR φ m' m).exists.choose

/-- The base map of `modelHom hR φ m' m` is the base map of `φ`, transported along the
identifications of the bases of the models with those of the families. -/
theorem modelHom_baseMap (hR : IsModelRelation R) {X' X : CurveFamily B hZ} (φ : X' ⟶ X)
    (m' : Model R X') (m : Model R X) :
    (modelHom hR φ m' m).baseMap =
      eqToHom m'.base_eq ≫ φ.baseMap ≫ eqToHom m.base_eq.symm :=
  (existsUnique_modelHom hR φ m' m).exists.choose_spec.1

/-- `modelHom hR φ m' m` is compatible with the contractions of `m'` and `m`. -/
theorem contraction_modelHom_totalMap (hR : IsModelRelation R) {X' X : CurveFamily B hZ}
    (φ : X' ⟶ X) (m' : Model R X') (m : Model R X) :
    m'.contraction ≫ (modelHom hR φ m' m).totalMap = φ.totalMap ≫ m.contraction :=
  (existsUnique_modelHom hR φ m' m).exists.choose_spec.2

/-- A morphism of models over the base map of `φ` and compatible with the contractions is
`modelHom hR φ m' m`. -/
theorem modelHom_unique (hR : IsModelRelation R) {X' X : CurveFamily B hZ} (φ : X' ⟶ X)
    (m' : Model R X') (m : Model R X) (ψ : m'.family ⟶ m.family)
    (hb : ψ.baseMap = eqToHom m'.base_eq ≫ φ.baseMap ≫ eqToHom m.base_eq.symm)
    (hc : m'.contraction ≫ ψ.totalMap = φ.totalMap ≫ m.contraction) :
    ψ = modelHom hR φ m' m :=
  (existsUnique_modelHom hR φ m' m).unique ⟨hb, hc⟩
    (existsUnique_modelHom hR φ m' m).exists.choose_spec

/-- The morphism of models over the identity of `X` is the identity. -/
theorem modelHom_id (hR : IsModelRelation R) {X : CurveFamily B hZ} (m : Model R X) :
    modelHom hR (𝟙 X) m m = 𝟙 m.family :=
  (modelHom_unique hR (𝟙 X) m m (𝟙 m.family) (by simp) (by simp)).symm

/-- The morphism of models over a composite is the composite of the morphisms of models. -/
theorem modelHom_comp (hR : IsModelRelation R) {X'' X' X : CurveFamily B hZ} (φ' : X'' ⟶ X')
    (φ : X' ⟶ X) (m'' : Model R X'') (m' : Model R X') (m : Model R X) :
    modelHom hR (φ' ≫ φ) m'' m = modelHom hR φ' m'' m' ≫ modelHom hR φ m' m := by
  refine (modelHom_unique hR (φ' ≫ φ) m'' m _ ?_ ?_).symm
  · simp [modelHom_baseMap]
  · rw [curveFamily_comp_totalMap, ← Category.assoc, contraction_modelHom_totalMap,
      Category.assoc, contraction_modelHom_totalMap, curveFamily_comp_totalMap, Category.assoc]

section Functor

variable {P Q : ObjectProperty (CurveFamily B hZ)}
  (hP : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → P G → P F)
  (hQ : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Q G → Q F)
  (hR : IsModelRelation R) (hex : ∀ X, P X → ∃ Y b c, R X Y b c)
  (hRQ : ∀ {X Y b c}, R X Y b c → Q Y)

/-- The model chosen for a family with `P`. -/
def chosenModel (X : P.FullSubcategory) : Model R X.obj :=
  Classical.choice (by
    obtain ⟨Y, b, c, hc⟩ := hex X.obj X.property
    exact nonempty_model hR hc)

/-- The functor `Curves^P ⥤ Curves^Q` sending a family to its chosen model. -/
def modelFunctorAux : P.FullSubcategory ⥤ Q.FullSubcategory where
  obj X := ⟨(chosenModel hR hex X).family, hRQ (chosenModel hR hex X).isModel⟩
  map φ := ObjectProperty.homMk (modelHom hR φ.hom _ _)
  map_id X := by
    ext1
    exact modelHom_id hR _
  map_comp φ ψ := by
    ext1
    exact modelHom_comp hR φ.hom ψ.hom _ _ _

/-- The functor `modelFunctorAux` lies over the big fppf site of `Spec(ℤ)`. -/
theorem modelFunctorAux_comp_projection :
    modelFunctorAux hR hex hRQ ⋙ Q.ι ⋙ curvesProjectionOver B hZ =
      P.ι ⋙ curvesProjectionOver B hZ := by
  refine CategoryTheory.Functor.ext (fun X => (chosenModel hR hex X).base_eq) ?_
  intro X Y φ
  change (modelHom hR φ.hom _ _).baseMap = _
  rw [modelHom_baseMap]
  rfl

/-- **The 1-morphism of stacks defined by a base-change compatible construction.** Given a model
relation `R` (unique models, stable under base change) for which every family with `P` has a model
and every model has `Q`, the 1-morphism `Curves^P ⟶ Curves^Q` of categories fibred in groupoids
over the big fppf site of `Spec(ℤ)` sending a family to a model of it. -/
def modelFunctor : curvesSubstack B hZ P hP ⟶ curvesSubstack B hZ Q hQ :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := modelFunctorAux hR hex hRQ
      w := modelFunctorAux_comp_projection hR hex hRQ }

/-- The 1-morphism `modelFunctor` sends a family `X` to a model of `X` over the base of `X`. -/
theorem modelFunctor_obj (X : P.FullSubcategory) :
    ∃ (h : ((modelFunctor hP hQ hR hex hRQ).hom.obj X).obj.base = X.obj.base)
      (c : X.obj.total ⟶ ((modelFunctor hP hQ hR hex hRQ).hom.obj X).obj.total),
      R X.obj ((modelFunctor hP hQ hR hex hRQ).hom.obj X).obj (eqToHom h.symm) c :=
  ⟨(chosenModel hR hex X).base_eq, (chosenModel hR hex X).contraction,
    (chosenModel hR hex X).isModel⟩

/-- The 1-morphism `modelFunctor` sends a morphism of families to the morphism of the chosen
models compatible with the two contractions. -/
theorem modelFunctor_map {X' X : P.FullSubcategory} (φ : X' ⟶ X) :
    (chosenModel hR hex X').contraction ≫ ((modelFunctor hP hQ hR hex hRQ).hom.map φ).hom.totalMap =
      φ.hom.totalMap ≫ (chosenModel hR hex X).contraction :=
  contraction_modelHom_totalMap hR φ.hom _ _

end Functor

end AlgebraicGeometry.C1590Private

end
