module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StabilizationMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelExistsHom
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStack
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-!
# Étale descent of stable models

The existence half of the proof of Stacks 0E8A ends with a descent: a stable model of a prestable
family `X ⟶ S` exists étale locally on `S`, stable models are unique up to unique isomorphism, so
the local models carry a descent datum, which is effective because `Curves` is a stack (Stacks
0D52), and the local contractions glue. This file carries out that descent.

## Main definitions

* `AlgebraicGeometry.C1590Private.restrictX`: a chosen restriction of a family of curves along a
  morphism of the site to its base.
* `AlgebraicGeometry.C1590Private.restrictedModel`: the model induced on a restriction of the
  target of a model.
* `AlgebraicGeometry.C1590Private.modelDescentDatum`: the descent datum (Stacks 026C) of the
  targets of a family of local models, glued by the unique morphisms of models.

## Main results

* `AlgebraicGeometry.C1590Private.IsStableModel.hom_ext_of_baseMap`: a morphism of families out of
  the target of a stable model is determined by its base map and its composite with the
  contraction.
* `AlgebraicGeometry.C1590Private.compTo_eq_modelHom`: the canonical comparison of two restrictions
  is the morphism of the induced models.
* `AlgebraicGeometry.C1590Private.exists_glue_out`: morphisms out of the members of a covering of a
  family, compatible on overlaps, glue.
* `AlgebraicGeometry.C1590Private.exists_descent_of_models`: local models over a covering descend
  to a family `x` over the base with a contraction `X ⟶ x` and compatible morphisms from the
  local targets; the effectivity is Stacks 0D52.

The relation `R` is arbitrary here, subject to `AlgebraicGeometry.C1590Private.IsModelRelation`;
that the descended pair is again a stable model is local on the base and is proved separately.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0D52](https://stacks.math.columbia.edu/tag/0D52)
* [Stacks Project, Tag 026C](https://stacks.math.columbia.edu/tag/026C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} {g : ℕ}

/-- **Morphisms out of a stable model are determined by the contraction.** Two morphisms of
families `ψ, ψ' : Y' ⟶ Y` out of the target of a stable model `c' : X' ⟶ Y'`, with the same base
map, which agree after composing with `c'`, are equal. -/
theorem IsStableModel.hom_ext_of_baseMap {X' Y' Y : CurveFamily B hZ} {b' : X'.base ⟶ Y'.base}
    {c' : X'.total ⟶ Y'.total} (h' : IsStableModel B hZ g b' c') {ψ ψ' : Y' ⟶ Y}
    (hb : ψ.baseMap = ψ'.baseMap) (hc : c' ≫ ψ.totalMap = c' ≫ ψ'.totalMap) : ψ = ψ' :=
  CurveFamily.Hom.ext hb (eq_of_comp_eq_of_isIso_structureSharp c' h'.isIso_structureSharp
    Y.toBase Y.proper.1 (by rw [ψ.cartesian.w, ψ'.cartesian.w, hb]) hc)

variable {R : ∀ X Y : CurveFamily B hZ, (X.base ⟶ Y.base) → (X.total ⟶ Y.total) → Prop}

/-- **A contraction onto a base change.** Given a model `c : X → Y` over `b`, a morphism of
families `φ : X' ⟶ X` and a morphism of families `ψ : Y' ⟶ Y` over `φ.baseMap ≫ b`, with `Y'` over
the base of `X'`, the base change of `c` is a contraction `X' → Y'` making `Y'` a model of `X'`. -/
theorem exists_contraction_of_hom (hR : IsModelRelation R) {X' X Y Y' : CurveFamily B hZ}
    (φ : X' ⟶ X) {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total} (hc : R X Y b c) (ψ : Y' ⟶ Y)
    (h : Y'.base = X'.base) (hψ : ψ.baseMap = eqToHom h ≫ φ.baseMap ≫ b) :
    ∃ c' : X'.total ⟶ Y'.total, c' ≫ ψ.totalMap = φ.totalMap ≫ c ∧
      R X' Y' (eqToHom h.symm) c' := by
  have hw : (φ.totalMap ≫ c) ≫ Y.toBase =
      (X'.toBase ≫ schemeSpaceMap (eqToHom h.symm)) ≫ schemeSpaceMap ψ.baseMap := by
    rw [Category.assoc, hR.w hc, ← Category.assoc, φ.cartesian.w, Category.assoc,
      Category.assoc, ← schemeSpaceMap_comp, ← schemeSpaceMap_comp, hψ, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  refine ⟨ψ.cartesian.lift _ _ hw, ψ.cartesian.lift_fst _ _ hw, ?_⟩
  refine hR.baseChange φ ψ _ _ hc inferInstance ?_ (ψ.cartesian.lift_fst _ _ hw)
    (ψ.cartesian.lift_snd _ _ hw)
  rw [hψ, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-! ### Restrictions of a family and of its models -/

section Restrict

variable (X : CurveFamily B hZ)

/-- A chosen restriction of a family of curves `X` along a morphism `w : W ⟶ X.base`. -/
def restrictX {W : BigFppfOver B integerBase hZ} (w : W ⟶ X.base) : CurveFamily B hZ :=
  (CurveFamily.exists_hom_baseMap_eq X w).choose

/-- The morphism from the chosen restriction. -/
def restrictXHom {W : BigFppfOver B integerBase hZ} (w : W ⟶ X.base) : restrictX X w ⟶ X :=
  (CurveFamily.exists_hom_baseMap_eq X w).choose_spec.choose

/-- The base of the chosen restriction of `X` along `w : W ⟶ X.base` is `W`. -/
theorem restrictX_base {W : BigFppfOver B integerBase hZ} (w : W ⟶ X.base) :
    (restrictX X w).base = W :=
  (CurveFamily.exists_hom_baseMap_eq X w).choose_spec.choose_spec.choose

/-- The base map of `restrictXHom X w` is `w`, up to the identification of bases. -/
theorem restrictXHom_baseMap {W : BigFppfOver B integerBase hZ} (w : W ⟶ X.base) :
    (restrictXHom X w).baseMap = eqToHom (restrictX_base X w) ≫ w :=
  (CurveFamily.exists_hom_baseMap_eq X w).choose_spec.choose_spec.choose_spec

variable {X}

/-- The factorization of the chosen restriction of `X` along `w` through a morphism of families
`φ : Xi ⟶ X`, over a factorization `gi` of `w` through the base map of `φ`. -/
theorem existsUnique_factorX {Xi : CurveFamily B hZ} (φ : Xi ⟶ X) {W : BigFppfOver B integerBase hZ}
    (w : W ⟶ X.base) (gi : W ⟶ Xi.base) (h : gi ≫ φ.baseMap = w) :
    ∃! κ : restrictX X w ⟶ Xi, κ.baseMap = eqToHom (restrictX_base X w) ≫ gi ∧
      κ ≫ φ = restrictXHom X w := by
  obtain ⟨κ, ⟨h₁, h₂⟩, h₃⟩ :=
    (CurveDeformation.curvesProjectionOver_isFiberedInGroupoids (B := B) (hZ := hZ)).unique_lift
      φ (restrictXHom X w) (eqToHom (restrictX_base X w) ≫ gi) (by
        show (eqToHom (restrictX_base X w) ≫ gi) ≫ φ.baseMap = (restrictXHom X w).baseMap
        rw [restrictXHom_baseMap, Category.assoc, h])
  exact ⟨κ, ⟨h₁, h₂⟩, fun κ' hκ' => h₃ κ' hκ'⟩

/-- The factorization of `existsUnique_factorX`. -/
def factorX {Xi : CurveFamily B hZ} (φ : Xi ⟶ X) {W : BigFppfOver B integerBase hZ}
    (w : W ⟶ X.base) (gi : W ⟶ Xi.base) (h : gi ≫ φ.baseMap = w) : restrictX X w ⟶ Xi :=
  (existsUnique_factorX φ w gi h).exists.choose

/-- The base map of `factorX φ w gi h` is `gi`, up to the identification of bases. -/
theorem factorX_baseMap {Xi : CurveFamily B hZ} (φ : Xi ⟶ X) {W : BigFppfOver B integerBase hZ}
    (w : W ⟶ X.base) (gi : W ⟶ Xi.base) (h : gi ≫ φ.baseMap = w) :
    (factorX φ w gi h).baseMap = eqToHom (restrictX_base X w) ≫ gi :=
  (existsUnique_factorX φ w gi h).exists.choose_spec.1

/-- The composite of `factorX φ w gi h` with `φ` is `restrictXHom X w`. -/
theorem factorX_comp {Xi : CurveFamily B hZ} (φ : Xi ⟶ X) {W : BigFppfOver B integerBase hZ}
    (w : W ⟶ X.base) (gi : W ⟶ Xi.base) (h : gi ≫ φ.baseMap = w) :
    factorX φ w gi h ≫ φ = restrictXHom X w :=
  (existsUnique_factorX φ w gi h).exists.choose_spec.2

/-- A morphism with the base map and composite with `φ` of `factorX φ w gi h` is equal to it. -/
theorem factorX_unique {Xi : CurveFamily B hZ} (φ : Xi ⟶ X) {W : BigFppfOver B integerBase hZ}
    (w : W ⟶ X.base) (gi : W ⟶ Xi.base) (h : gi ≫ φ.baseMap = w) (κ : restrictX X w ⟶ Xi)
    (h₁ : κ.baseMap = eqToHom (restrictX_base X w) ≫ gi) (h₂ : κ ≫ φ = restrictXHom X w) :
    κ = factorX φ w gi h :=
  (existsUnique_factorX φ w gi h).unique ⟨h₁, h₂⟩ (existsUnique_factorX φ w gi h).exists.choose_spec

end Restrict

/-! ### Models on restrictions -/

section RestrictModel

variable {X : CurveFamily B hZ}

/-- The base of a restriction, read as a family of curves. -/
theorem Restriction.hpt' {U V : BigFppfOver B integerBase hZ} {f : V ⟶ U}
    {x : CurveFamily B hZ} {hx : (curvesProjectionOver B hZ).obj x = U}
    (r : Functor.Restriction (curvesProjectionOver B hZ) f x hx) : r.pt.base = V :=
  r.hpt

/-- The base map of a restriction of an object over `U`. -/
theorem Restriction.baseMap_hom {U V : BigFppfOver B integerBase hZ} {f : V ⟶ U}
    {x : CurveFamily B hZ} {hx : (curvesProjectionOver B hZ).obj x = U}
    (r : Functor.Restriction (curvesProjectionOver B hZ) f x hx) (hx' : x.base = U) :
    r.hom.baseMap = eqToHom (Restriction.hpt' r) ≫ f ≫ eqToHom hx'.symm := by
  have := r.isHomLift
  have := IsHomLift.fac' (curvesProjectionOver B hZ) (eqToHom r.hpt ≫ f ≫ eqToHom hx.symm) r.hom
  exact this.trans (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)

/-- The base of the target of a model, read through the projection to the site. -/
theorem Model.base_eq' {Xi : CurveFamily B hZ} (mi : Model R Xi) :
    (curvesProjectionOver B hZ).obj mi.family = Xi.base :=
  mi.base_eq

/-- A restriction of the target of a model of `Xi`, along `gi : W ⟶ Xi.base`, is a model of the
chosen restriction of `X` along `w = gi ≫ φ.baseMap`. -/
theorem exists_restrictedContraction (hR : IsModelRelation R) {Xi : CurveFamily B hZ} (φ : Xi ⟶ X)
    (mi : Model R Xi)
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ X.base) (gi : W ⟶ Xi.base)
    (hgi : gi ≫ φ.baseMap = w)
    (r : Functor.Restriction (curvesProjectionOver B hZ) gi mi.family mi.base_eq') :
    ∃ c : (restrictX X w).total ⟶ r.pt.total,
      c ≫ r.hom.totalMap = (factorX φ w gi hgi).totalMap ≫ mi.contraction ∧
        R (restrictX X w) r.pt
          (eqToHom ((Restriction.hpt' r).trans (restrictX_base X w).symm).symm) c :=
  exists_contraction_of_hom hR (factorX φ w gi hgi) mi.isModel r.hom
    ((Restriction.hpt' r).trans (restrictX_base X w).symm) (by
      rw [Restriction.baseMap_hom r mi.base_eq, factorX_baseMap, Category.assoc,
          eqToHom_trans_assoc])

/-- The model of the chosen restriction of `X` on a restriction of the target of a model. -/
abbrev restrictedModel (hR : IsModelRelation R) {Xi : CurveFamily B hZ} (φ : Xi ⟶ X)
    (mi : Model R Xi)
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ X.base) (gi : W ⟶ Xi.base)
    (hgi : gi ≫ φ.baseMap = w)
    (r : Functor.Restriction (curvesProjectionOver B hZ) gi mi.family mi.base_eq') :
    Model R (restrictX X w) where
  family := r.pt
  base_eq := (Restriction.hpt' r).trans (restrictX_base X w).symm
  contraction := (exists_restrictedContraction hR φ mi w gi hgi r).choose
  isModel := (exists_restrictedContraction hR φ mi w gi hgi r).choose_spec.2

/-- The target of `restrictedModel hR φ mi w gi hgi r` is `r.pt`. -/
theorem restrictedModel_family (hR : IsModelRelation R) {Xi : CurveFamily B hZ} (φ : Xi ⟶ X)
    (mi : Model R Xi)
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ X.base) (gi : W ⟶ Xi.base)
    (hgi : gi ≫ φ.baseMap = w)
    (r : Functor.Restriction (curvesProjectionOver B hZ) gi mi.family mi.base_eq') :
    (restrictedModel hR φ mi w gi hgi r).family = r.pt := rfl

/-- The contraction of `restrictedModel hR φ mi w gi hgi r`, composed with the restriction
morphism, is the factorization through `φ` followed by the contraction of `mi`. -/
theorem restrictedModel_contraction (hR : IsModelRelation R) {Xi : CurveFamily B hZ} (φ : Xi ⟶ X)
    (mi : Model R Xi)
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ X.base) (gi : W ⟶ Xi.base)
    (hgi : gi ≫ φ.baseMap = w)
    (r : Functor.Restriction (curvesProjectionOver B hZ) gi mi.family mi.base_eq') :
    (restrictedModel hR φ mi w gi hgi r).contraction ≫ r.hom.totalMap =
      (factorX φ w gi hgi).totalMap ≫ mi.contraction :=
  (exists_restrictedContraction hR φ mi w gi hgi r).choose_spec.1

/-- The base map of the canonical comparison between two restrictions. -/
theorem Restriction.baseMap_compTo {W V U : BigFppfOver B integerBase hZ} (g : W ⟶ V) (f : V ⟶ U)
    {h : W ⟶ U} (hh : h = g ≫ f) {x : CurveFamily B hZ}
    {hx : (curvesProjectionOver B hZ).obj x = U}
    (xr : Functor.Restriction (curvesProjectionOver B hZ) f x hx)
    (xrW : Functor.Restriction (curvesProjectionOver B hZ) h x hx) :
    (Functor.Restriction.compTo (curvesProjectionOver B hZ) g f hh xr xrW).baseMap =
      eqToHom (Restriction.hpt' xrW) ≫ g ≫ eqToHom (Restriction.hpt' xr).symm := by
  have : (curvesProjectionOver B hZ).IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
      (Functor.Restriction.compTo (curvesProjectionOver B hZ) g f hh xr xrW) := by
    unfold Functor.Restriction.compTo
    infer_instance
  have := IsHomLift.fac' (curvesProjectionOver B hZ) (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
    (Functor.Restriction.compTo (curvesProjectionOver B hZ) g f hh xr xrW)
  exact this.trans (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)

/-- The morphism between chosen restrictions of `X` over a morphism `g` of their bases. -/
def restrictXMap (X : CurveFamily B hZ) {W V : BigFppfOver B integerBase hZ} {w : W ⟶ X.base}
    {w' : V ⟶ X.base} (g : W ⟶ V) (hg : g ≫ w' = w) : restrictX X w ⟶ restrictX X w' :=
  factorX (restrictXHom X w') w (g ≫ eqToHom (restrictX_base X w').symm) (by
    rw [restrictXHom_baseMap, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      hg])

/-- The base map of `restrictXMap X g hg` is `g`, up to the identification of bases. -/
theorem restrictXMap_baseMap (X : CurveFamily B hZ) {W V : BigFppfOver B integerBase hZ}
    {w : W ⟶ X.base} {w' : V ⟶ X.base} (g : W ⟶ V) (hg : g ≫ w' = w) :
    (restrictXMap X g hg).baseMap =
      eqToHom (restrictX_base X w) ≫ g ≫ eqToHom (restrictX_base X w').symm :=
  factorX_baseMap _ _ _ _

/-- The composite of `restrictXMap X g hg` with `restrictXHom X w'` is `restrictXHom X w`. -/
theorem restrictXMap_comp (X : CurveFamily B hZ) {W V : BigFppfOver B integerBase hZ}
    {w : W ⟶ X.base} {w' : V ⟶ X.base} (g : W ⟶ V) (hg : g ≫ w' = w) :
    restrictXMap X g hg ≫ restrictXHom X w' = restrictXHom X w :=
  factorX_comp _ _ _ _

/-- The factorizations through a morphism of families are compatible with the morphisms between
chosen restrictions. -/
theorem restrictXMap_comp_factorX {X Xi : CurveFamily B hZ} (φ : Xi ⟶ X)
    {W V : BigFppfOver B integerBase hZ} {w : W ⟶ X.base} {w' : V ⟶ X.base} (g : W ⟶ V)
    (hg : g ≫ w' = w) (g' : V ⟶ Xi.base) (hg' : g' ≫ φ.baseMap = w') (h : W ⟶ Xi.base)
    (hh : h = g ≫ g') (hh' : h ≫ φ.baseMap = w) :
    restrictXMap X g hg ≫ factorX φ w' g' hg' = factorX φ w h hh' := by
  refine factorX_unique φ w h hh' _ ?_ ?_
  · show (restrictXMap X g hg).baseMap ≫ (factorX φ w' g' hg').baseMap = _
    rw [restrictXMap_baseMap, factorX_baseMap, hh]
    simp
  · rw [Category.assoc, factorX_comp, restrictXMap_comp]

/-- **The canonical comparison of restrictions is the morphism of models.** Between the models
induced on two restrictions of the target of a model, the canonical comparison of the two
restrictions is the morphism of models over the morphism of chosen restrictions of `X`. -/
theorem compTo_eq_modelHom (hR : IsModelRelation R) {X Xi : CurveFamily B hZ} (φ : Xi ⟶ X)
    (mi : Model R Xi) {W V : BigFppfOver B integerBase hZ} {w : W ⟶ X.base} {w' : V ⟶ X.base}
    (g : W ⟶ V) (hg : g ≫ w' = w) (g' : V ⟶ Xi.base) (hg' : g' ≫ φ.baseMap = w')
    (h : W ⟶ Xi.base) (hh : h = g ≫ g') (hh' : h ≫ φ.baseMap = w)
    (r : Functor.Restriction (curvesProjectionOver B hZ) g' mi.family mi.base_eq')
    (rW : Functor.Restriction (curvesProjectionOver B hZ) h mi.family mi.base_eq') :
    Functor.Restriction.compTo (curvesProjectionOver B hZ) g g' hh r rW =
      modelHom hR (restrictXMap X g hg) (restrictedModel hR φ mi w h hh' rW)
        (restrictedModel hR φ mi w' g' hg' r) := by
  have hb : (Functor.Restriction.compTo (curvesProjectionOver B hZ) g g' hh r rW).baseMap =
      eqToHom (restrictedModel hR φ mi w h hh' rW).base_eq ≫ (restrictXMap X g hg).baseMap ≫
        eqToHom (restrictedModel hR φ mi w' g' hg' r).base_eq.symm := by
    rw [Restriction.baseMap_compTo, restrictXMap_baseMap]
    simp only [eqToHom_trans, eqToHom_trans_assoc, Category.assoc]
  refine (modelHom_unique hR (restrictXMap X g hg) (restrictedModel hR φ mi w h hh' rW)
    (restrictedModel hR φ mi w' g' hg' r) _ hb ?_)
  apply r.hom.cartesian.hom_ext
  · have h1 := congrArg CurveFamily.Hom.totalMap
      (Functor.Restriction.compTo_hom (curvesProjectionOver B hZ) g g' hh r rW)
    change _ ≫ r.hom.totalMap = rW.hom.totalMap at h1
    rw [Category.assoc, h1, Category.assoc, restrictedModel_contraction,
      restrictedModel_contraction, ← Category.assoc, ← curveFamily_comp_totalMap,
      restrictXMap_comp_factorX φ g hg g' hg' h hh hh']
  · rw [Category.assoc, (Functor.Restriction.compTo (curvesProjectionOver B hZ) g g' hh r
      rW).cartesian.w, ← Category.assoc, hR.w (restrictedModel hR φ mi w h hh' rW).isModel,
      Category.assoc, Category.assoc, hR.w (restrictedModel hR φ mi w' g' hg' r).isModel,
      ← Category.assoc (restrictXMap X g hg).totalMap, (restrictXMap X g hg).cartesian.w,
      Category.assoc, ← schemeSpaceMap_comp, ← schemeSpaceMap_comp, hb]
    simp

end RestrictModel

/-! ### Morphisms of models over identities -/

section ModelHomId

/-- A morphism of models over `𝟙 X'` followed by one over `σ` is the morphism of models over
`σ`. -/
theorem modelHom_id_comp (hR : IsModelRelation R) {X' X : CurveFamily B hZ} (σ : X' ⟶ X)
    (m₁ m₂ : Model R X') (n : Model R X) :
    modelHom hR (𝟙 X') m₁ m₂ ≫ modelHom hR σ m₂ n = modelHom hR σ m₁ n := by
  rw [← modelHom_comp, Category.id_comp]

/-- A morphism of models over `σ` followed by one over `𝟙 X` is the morphism of models over `σ`. -/
theorem modelHom_comp_id (hR : IsModelRelation R) {X' X : CurveFamily B hZ} (σ : X' ⟶ X)
    (m : Model R X') (n₁ n₂ : Model R X) :
    modelHom hR σ m n₁ ≫ modelHom hR (𝟙 X) n₁ n₂ = modelHom hR σ m n₂ := by
  rw [← modelHom_comp, Category.comp_id]

/-- A morphism of models over the identity is an isomorphism. -/
instance isIso_modelHom_id (hR : IsModelRelation R) {X : CurveFamily B hZ} (m m' : Model R X) :
    IsIso (modelHom hR (𝟙 X) m m') :=
  ⟨modelHom hR (𝟙 X) m' m, by rw [modelHom_id_comp, modelHom_id],
    by rw [modelHom_id_comp, modelHom_id]⟩

/-- A morphism of models over the identity is a morphism of the fibre over the base. -/
theorem fibreHom_modelHom_id (hR : IsModelRelation R) {X : CurveFamily B hZ} (m m' : Model R X)
    {U : BigFppfOver B integerBase hZ} (h : (curvesProjectionOver B hZ).obj m.family = U)
    (h' : (curvesProjectionOver B hZ).obj m'.family = U) :
    Functor.FibreHom (curvesProjectionOver B hZ) m.family m'.family h h'
      (modelHom hR (𝟙 X) m m') := by
  refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
  show (modelHom hR (𝟙 X) m m').baseMap = _
  rw [modelHom_baseMap]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl, Category.comp_id,
    curveFamily_id_baseMap]
  rfl

end ModelHomId

/-! ### The descent datum of a family of local models -/

section DescentDatum

variable (hR : IsModelRelation R) {X : CurveFamily B hZ} {ι : Type*} (Xi : ι → CurveFamily B hZ)
  (φ : ∀ i, Xi i ⟶ X) (m : ∀ i, Model R (Xi i))

local notation "𝓟" => curvesProjectionOver B hZ

/-- The overlap `Vᵢ ×_S Vⱼ`. -/
abbrev ovl (i j : ι) : BigFppfOver B integerBase hZ := pullback (φ i).baseMap (φ j).baseMap

/-- The triple overlap `(Vᵢ ×_S Vⱼ) ×_{Vⱼ} (Vⱼ ×_S Vₖ)`. -/
abbrev tri (i j k : ι) : BigFppfOver B integerBase hZ :=
  pullback (pullback.snd (φ i).baseMap (φ j).baseMap) (pullback.fst (φ j).baseMap (φ k).baseMap)

/-- The first projection of the triple overlap to `Vᵢ`. -/
abbrev q₁ (i j k : ι) : tri Xi φ i j k ⟶ (Xi i).base :=
  pullback.fst _ _ ≫ pullback.fst (φ i).baseMap (φ j).baseMap

/-- The projection of the triple overlap to `Vⱼ`. -/
abbrev q₂ (i j k : ι) : tri Xi φ i j k ⟶ (Xi j).base :=
  pullback.fst _ _ ≫ pullback.snd (φ i).baseMap (φ j).baseMap

/-- The projection of the triple overlap to `Vₖ`. -/
abbrev q₃ (i j k : ι) : tri Xi φ i j k ⟶ (Xi k).base :=
  pullback.snd _ _ ≫ pullback.snd (φ j).baseMap (φ k).baseMap

/-- The morphism from the overlap to `S`. -/
abbrev wOvl (i j : ι) : ovl Xi φ i j ⟶ X.base :=
  pullback.fst (φ i).baseMap (φ j).baseMap ≫ (φ i).baseMap

/-- The morphism from the triple overlap to `S`. -/
abbrev wTri (i j k : ι) : tri Xi φ i j k ⟶ X.base := q₁ Xi φ i j k ≫ (φ i).baseMap

/-- The projection `q₂` followed by `φⱼ` is the morphism from the triple overlap to `S`. -/
theorem q₂_comp (i j k : ι) : q₂ Xi φ i j k ≫ (φ j).baseMap = wTri Xi φ i j k := by
  simp only [q₂, wTri, q₁, Category.assoc]
  rw [pullback.condition]

/-- The projection `q₃` followed by `φₖ` is the morphism from the triple overlap to `S`. -/
theorem q₃_comp (i j k : ι) : q₃ Xi φ i j k ≫ (φ k).baseMap = wTri Xi φ i j k := by
  rw [← q₂_comp]
  simp only [q₃, q₂, Category.assoc]
  have e₁ : pullback.snd (φ j).baseMap (φ k).baseMap ≫ (φ k).baseMap =
      pullback.fst (φ j).baseMap (φ k).baseMap ≫ (φ j).baseMap := pullback.condition.symm
  have e₂ : pullback.snd (pullback.snd (φ i).baseMap (φ j).baseMap)
      (pullback.fst (φ j).baseMap (φ k).baseMap) ≫ pullback.fst (φ j).baseMap (φ k).baseMap =
      pullback.fst (pullback.snd (φ i).baseMap (φ j).baseMap)
        (pullback.fst (φ j).baseMap (φ k).baseMap) ≫ pullback.snd (φ i).baseMap (φ j).baseMap :=
    pullback.condition.symm
  rw [e₁, ← Category.assoc, e₂, Category.assoc]

/-- The second projection of the overlap followed by `φⱼ` is the morphism from the overlap to
`S`. -/
theorem snd_comp_ovl (i j : ι) :
    pullback.snd (φ i).baseMap (φ j).baseMap ≫ (φ j).baseMap = wOvl Xi φ i j :=
  pullback.condition.symm

/-- The first projection of the triple overlap to `Vᵢ ×_S Vⱼ` commutes with the morphisms to
`S`. -/
theorem fst_comp_wOvl (i j k : ι) :
    pullback.fst (pullback.snd (φ i).baseMap (φ j).baseMap)
      (pullback.fst (φ j).baseMap (φ k).baseMap) ≫ wOvl Xi φ i j = wTri Xi φ i j k := by
  simp only [wOvl, wTri, q₁, Category.assoc]

/-- The second projection of the triple overlap to `Vⱼ ×_S Vₖ` commutes with the morphisms to
`S`. -/
theorem snd_comp_wOvl (i j k : ι) :
    pullback.snd (pullback.snd (φ i).baseMap (φ j).baseMap)
      (pullback.fst (φ j).baseMap (φ k).baseMap) ≫ wOvl Xi φ j k = wTri Xi φ i j k := by
  rw [← q₂_comp]
  simp only [wOvl, q₂, Category.assoc]
  rw [← Category.assoc, ← pullback.condition, Category.assoc]

/-- The projections `q₁` and `q₃` of the triple overlap agree over `S`. -/
theorem s₁₃_cond (i j k : ι) : q₁ Xi φ i j k ≫ (φ i).baseMap = q₃ Xi φ i j k ≫ (φ k).baseMap :=
  (q₃_comp Xi φ i j k).symm

/-- The comparison from the triple overlap to the overlap of the first and the last members. -/
abbrev s₁₃ (i j k : ι) : tri Xi φ i j k ⟶ ovl Xi φ i k :=
  pullback.lift (q₁ Xi φ i j k) (q₃ Xi φ i j k) (s₁₃_cond Xi φ i j k)

/-- The comparison `s₁₃` commutes with the morphisms to `S`. -/
theorem s₁₃_comp_wOvl (i j k : ι) : s₁₃ Xi φ i j k ≫ wOvl Xi φ i k = wTri Xi φ i j k := by
  rw [wOvl, ← Category.assoc, pullback.lift_fst]

variable (hp : (curvesProjectionOver B hZ).IsFiberedInGroupoids)

/-- The restriction of `Yᵢ` to the overlap. -/
abbrev resA (i j : ι) := Functor.Restriction.ofIsFiberedInGroupoids 𝓟 hp
  (pullback.fst (φ i).baseMap (φ j).baseMap) (m i).family (m i).base_eq'

/-- The restriction of `Yⱼ` to the overlap. -/
abbrev resB (i j : ι) := Functor.Restriction.ofIsFiberedInGroupoids 𝓟 hp
  (pullback.snd (φ i).baseMap (φ j).baseMap) (m j).family (m j).base_eq'

/-- The restriction of `Yᵢ` to the triple overlap. -/
abbrev res₁ (i j k : ι) := Functor.Restriction.ofIsFiberedInGroupoids 𝓟 hp
  (q₁ Xi φ i j k) (m i).family (m i).base_eq'

/-- The restriction of `Yⱼ` to the triple overlap. -/
abbrev res₂ (i j k : ι) := Functor.Restriction.ofIsFiberedInGroupoids 𝓟 hp
  (q₂ Xi φ i j k) (m j).family (m j).base_eq'

/-- The restriction of `Yₖ` to the triple overlap. -/
abbrev res₃ (i j k : ι) := Functor.Restriction.ofIsFiberedInGroupoids 𝓟 hp
  (q₃ Xi φ i j k) (m k).family (m k).base_eq'

/-- The model on the restriction of `Yᵢ` to the overlap. -/
abbrev MA (i j : ι) := restrictedModel hR (φ i) (m i) (wOvl Xi φ i j) _ rfl (resA Xi φ m hp i j)

/-- The model on the restriction of `Yⱼ` to the overlap. -/
abbrev MB (i j : ι) :=
  restrictedModel hR (φ j) (m j) (wOvl Xi φ i j) _ (snd_comp_ovl Xi φ i j) (resB Xi φ m hp i j)

/-- The model on the restriction of `Yᵢ` to the triple overlap. -/
abbrev M₁ (i j k : ι) :=
  restrictedModel hR (φ i) (m i) (wTri Xi φ i j k) _ rfl (res₁ Xi φ m hp i j k)

/-- The model on the restriction of `Yⱼ` to the triple overlap. -/
abbrev M₂ (i j k : ι) :=
  restrictedModel hR (φ j) (m j) (wTri Xi φ i j k) _ (q₂_comp Xi φ i j k) (res₂ Xi φ m hp i j k)

/-- The model on the restriction of `Yₖ` to the triple overlap. -/
abbrev M₃ (i j k : ι) :=
  restrictedModel hR (φ k) (m k) (wTri Xi φ i j k) _ (q₃_comp Xi φ i j k) (res₃ Xi φ m hp i j k)

/-- The morphism of models from `Yᵢ` to `Yⱼ` on the triple overlap is the restriction of the one on
`Vᵢ ×_S Vⱼ`. -/
theorem restr₁₂ (i j k : ι) :
    modelHom hR (𝟙 _) (M₁ hR Xi φ m hp i j k) (M₂ hR Xi φ m hp i j k) ≫
        Functor.Restriction.compTo 𝓟 (pullback.fst _ _)
          (pullback.snd (φ i).baseMap (φ j).baseMap) rfl (resB Xi φ m hp i j)
          (res₂ Xi φ m hp i j k) =
      Functor.Restriction.compTo 𝓟 (pullback.fst _ _)
          (pullback.fst (φ i).baseMap (φ j).baseMap) rfl (resA Xi φ m hp i j)
          (res₁ Xi φ m hp i j k) ≫
        modelHom hR (𝟙 _) (MA hR Xi φ m hp i j) (MB hR Xi φ m hp i j) := by
  rw [compTo_eq_modelHom hR (φ j) (m j) _ (fst_comp_wOvl Xi φ i j k) _ (snd_comp_ovl Xi φ i j)
      (q₂ Xi φ i j k) rfl (q₂_comp Xi φ i j k),
    compTo_eq_modelHom hR (φ i) (m i) _ (fst_comp_wOvl Xi φ i j k) _ rfl (q₁ Xi φ i j k) rfl rfl,
    modelHom_id_comp, modelHom_comp_id]

/-- The morphism of models from `Yⱼ` to `Yₖ` on the triple overlap is the restriction of the one on
`Vⱼ ×_S Vₖ`. -/
theorem restr₂₃ (i j k : ι) (h₁ : q₂ Xi φ i j k = pullback.snd _ _ ≫
      pullback.fst (φ j).baseMap (φ k).baseMap) :
    modelHom hR (𝟙 _) (M₂ hR Xi φ m hp i j k) (M₃ hR Xi φ m hp i j k) ≫
        Functor.Restriction.compTo 𝓟 (pullback.snd _ _)
          (pullback.snd (φ j).baseMap (φ k).baseMap) rfl (resB Xi φ m hp j k)
          (res₃ Xi φ m hp i j k) =
      Functor.Restriction.compTo 𝓟 (pullback.snd _ _)
          (pullback.fst (φ j).baseMap (φ k).baseMap) h₁ (resA Xi φ m hp j k)
          (res₂ Xi φ m hp i j k) ≫
        modelHom hR (𝟙 _) (MA hR Xi φ m hp j k) (MB hR Xi φ m hp j k) := by
  rw [compTo_eq_modelHom hR (φ k) (m k) _ (snd_comp_wOvl Xi φ i j k) _ (snd_comp_ovl Xi φ j k)
      (q₃ Xi φ i j k) rfl (q₃_comp Xi φ i j k),
    compTo_eq_modelHom hR (φ j) (m j) _ (snd_comp_wOvl Xi φ i j k) _ rfl (q₂ Xi φ i j k) h₁
      (q₂_comp Xi φ i j k),
    modelHom_id_comp, modelHom_comp_id]

/-- The morphism of models from `Yᵢ` to `Yₖ` on the triple overlap is the restriction of the one on
`Vᵢ ×_S Vₖ`. -/
theorem restr₁₃ (i j k : ι) (h₁ : q₁ Xi φ i j k = s₁₃ Xi φ i j k ≫ pullback.fst _ _)
    (h₃ : q₃ Xi φ i j k = s₁₃ Xi φ i j k ≫ pullback.snd _ _) :
    modelHom hR (𝟙 _) (M₁ hR Xi φ m hp i j k) (M₃ hR Xi φ m hp i j k) ≫
        Functor.Restriction.compTo 𝓟 (s₁₃ Xi φ i j k)
          (pullback.snd (φ i).baseMap (φ k).baseMap) h₃ (resB Xi φ m hp i k)
          (res₃ Xi φ m hp i j k) =
      Functor.Restriction.compTo 𝓟 (s₁₃ Xi φ i j k)
          (pullback.fst (φ i).baseMap (φ k).baseMap) h₁ (resA Xi φ m hp i k)
          (res₁ Xi φ m hp i j k) ≫
        modelHom hR (𝟙 _) (MA hR Xi φ m hp i k) (MB hR Xi φ m hp i k) := by
  rw [compTo_eq_modelHom hR (φ k) (m k) _ (s₁₃_comp_wOvl Xi φ i j k) _ (snd_comp_ovl Xi φ i k)
      (q₃ Xi φ i j k) h₃ (q₃_comp Xi φ i j k),
    compTo_eq_modelHom hR (φ i) (m i) _ (s₁₃_comp_wOvl Xi φ i j k) _ rfl (q₁ Xi φ i j k) h₁ rfl,
    modelHom_id_comp, modelHom_comp_id]

/-- **The descent datum of a family of local models.** The targets of the local models, glued over
the overlaps by the unique morphisms of models. -/
def modelDescentDatum :
    Functor.DescentDatum 𝓟 (fun i => (Xi i).base) (fun i => (φ i).baseMap) (ovl Xi φ)
      (fun _ _ => pullback.fst _ _) (fun _ _ => pullback.snd _ _)
      (fun _ _ => IsPullback.of_hasPullback _ _) (tri Xi φ)
      (fun _ _ _ => pullback.fst _ _) (fun _ _ _ => pullback.snd _ _)
      (fun _ _ _ => IsPullback.of_hasPullback _ _) (q₁ Xi φ) (q₂ Xi φ) (q₃ Xi φ)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) where
  x i := (m i).family
  hx i := (m i).base_eq'
  xrij i j := resA Xi φ m hp i j
  xrji i j := resB Xi φ m hp i j
  φ i j := modelHom hR (𝟙 _) (MA hR Xi φ m hp i j) (MB hR Xi φ m hp i j)
  φ_fibreHom i j :=
    fibreHom_modelHom_id hR (MA hR Xi φ m hp i j) (MB hR Xi φ m hp i j) _ _
  φ_iso i j := isIso_modelHom_id hR (MA hR Xi φ m hp i j) (MB hR Xi φ m hp i j)
  wi i j k := res₁ Xi φ m hp i j k
  wj i j k := res₂ Xi φ m hp i j k
  wk i j k := res₃ Xi φ m hp i j k
  αij i j k := modelHom hR (𝟙 _) (M₁ hR Xi φ m hp i j k) (M₂ hR Xi φ m hp i j k)
  αjk i j k := modelHom hR (𝟙 _) (M₂ hR Xi φ m hp i j k) (M₃ hR Xi φ m hp i j k)
  αik i j k := modelHom hR (𝟙 _) (M₁ hR Xi φ m hp i j k) (M₃ hR Xi φ m hp i j k)
  αij_restr i j k := restr₁₂ hR Xi φ m hp i j k
  αjk_restr i j k := restr₂₃ hR Xi φ m hp i j k _
  s₁₃ i j k := s₁₃ Xi φ i j k
  hs₁₃₁ _ _ _ := pullback.lift_fst _ _ _
  hs₁₃₂ _ _ _ := pullback.lift_snd _ _ _
  αik_restr i j k := restr₁₃ hR Xi φ m hp i j k _ _
  cocycle i j k := (modelHom_id_comp hR (𝟙 _) (M₁ hR Xi φ m hp i j k) (M₂ hR Xi φ m hp i j k)
    (M₃ hR Xi φ m hp i j k)).symm

/-- The canonical comparison into the trivial restriction is the restriction morphism. -/
theorem compTo_id_eq {W U : BigFppfOver B integerBase hZ} (g : W ⟶ U) {x : CurveFamily B hZ}
    (hx : (curvesProjectionOver B hZ).obj x = U) (xrW : Functor.Restriction 𝓟 g x hx)
    (hg : g = g ≫ 𝟙 U) :
    Functor.Restriction.compTo 𝓟 g (𝟙 U) hg (Functor.Restriction.id 𝓟 x hx) xrW = xrW.hom := by
  have := Functor.Restriction.compTo_hom 𝓟 g (𝟙 U) hg (Functor.Restriction.id 𝓟 x hx) xrW
  exact (Category.comp_id _).symm.trans this

/-- **The local contractions agree on overlaps**, given the compatibility of an effective
descent datum with the gluing morphisms. -/
theorem localContraction_compat {x : CurveFamily B hZ}
    (hx : (curvesProjectionOver B hZ).obj x = X.base)
    (xr : ∀ i, Functor.Restriction 𝓟 (φ i).baseMap x hx) (ψ : ∀ i, (xr i).pt ⟶ (m i).family)
    [hψ : ∀ i, IsIso (ψ i)] (i j : ι)
    (xrij : Functor.Restriction 𝓟 (pullback.fst (φ i).baseMap (φ j).baseMap ≫ (φ i).baseMap)
      x hx)
    (ψir : xrij.pt ⟶ (resA Xi φ m hp i j).pt) (ψjr : xrij.pt ⟶ (resB Xi φ m hp i j).pt)
    [hir : IsIso ψir] [hjr : IsIso ψjr]
    (hi : ψir ≫ Functor.Restriction.compTo 𝓟 (pullback.fst (φ i).baseMap (φ j).baseMap) (𝟙 _)
        (by simp) (Functor.Restriction.id 𝓟 (m i).family (m i).base_eq') (resA Xi φ m hp i j) =
      Functor.Restriction.compTo 𝓟 (pullback.fst (φ i).baseMap (φ j).baseMap) (φ i).baseMap rfl
        (xr i) xrij ≫ ψ i)
    (hj : ψjr ≫ Functor.Restriction.compTo 𝓟 (pullback.snd (φ i).baseMap (φ j).baseMap) (𝟙 _)
        (by simp) (Functor.Restriction.id 𝓟 (m j).family (m j).base_eq') (resB Xi φ m hp i j) =
      Functor.Restriction.compTo 𝓟 (pullback.snd (φ i).baseMap (φ j).baseMap) (φ j).baseMap
        pullback.condition (xr j) xrij ≫ ψ j)
    (hφ : ψir ≫ modelHom hR (𝟙 _) (MA hR Xi φ m hp i j) (MB hR Xi φ m hp i j) = ψjr) :
    (factorX (φ i) (wOvl Xi φ i j) _ rfl).totalMap ≫ (m i).contraction ≫
        (inv (ψ i)).totalMap ≫ (xr i).hom.totalMap =
      (factorX (φ j) (wOvl Xi φ i j) _ (snd_comp_ovl Xi φ i j)).totalMap ≫ (m j).contraction ≫
        (inv (ψ j)).totalMap ≫ (xr j).hom.totalMap := by
  rw [compTo_id_eq] at hi hj
  have ei : (resA Xi φ m hp i j).hom ≫ inv (ψ i) ≫ (xr i).hom = inv ψir ≫ xrij.hom := by
    rw [← cancel_epi ψir, IsIso.hom_inv_id_assoc, ← Category.assoc, hi, Category.assoc,
      IsIso.hom_inv_id_assoc, Functor.Restriction.compTo_hom]
  have ej : (resB Xi φ m hp i j).hom ≫ inv (ψ j) ≫ (xr j).hom = inv ψjr ≫ xrij.hom := by
    rw [← cancel_epi ψjr, IsIso.hom_inv_id_assoc, ← Category.assoc, hj, Category.assoc,
      IsIso.hom_inv_id_assoc, Functor.Restriction.compTo_hom]
  have eA := restrictedModel_contraction hR (φ i) (m i) (wOvl Xi φ i j) _ rfl (resA Xi φ m hp i j)
  have eB := restrictedModel_contraction hR (φ j) (m j) (wOvl Xi φ i j) _ (snd_comp_ovl Xi φ i j)
    (resB Xi φ m hp i j)
  have eφ := contraction_modelHom_totalMap hR (𝟙 _) (MA hR Xi φ m hp i j) (MB hR Xi φ m hp i j)
  rw [curveFamily_id_totalMap, Category.id_comp] at eφ
  have hψ : inv ψir = modelHom hR (𝟙 _) (MA hR Xi φ m hp i j) (MB hR Xi φ m hp i j) ≫ inv ψjr := by
    rw [IsIso.eq_comp_inv, IsIso.inv_comp_eq, hφ]
  have ei' := congrArg CurveFamily.Hom.totalMap ei
  have ej' := congrArg CurveFamily.Hom.totalMap ej
  have hψ' := congrArg CurveFamily.Hom.totalMap hψ
  simp only [curveFamily_comp_totalMap] at ei' ej' hψ'
  rw [← reassoc_of% eA, ei', hψ', Category.assoc, reassoc_of% eφ, ← ej', reassoc_of% eB]

end DescentDatum

/-- The commuting square of a morphism of families, read through Yoneda. -/
theorem CurveFamily.Hom.w_yoneda {Y Z : CurveFamily B hZ} (f : Y ⟶ Z) :
    f.totalMap.hom ≫ yonedaToBase Z = yonedaToBase Y ≫ yoneda.map f.baseMap :=
  congrArg (fun k => k.hom) f.cartesian.w

/-- The total map of a composite, through `ObjectProperty.hom`. -/
theorem CurveFamily.Hom.totalMap_hom_comp {Y Z T : CurveFamily B hZ} (f : Y ⟶ Z) (g : Z ⟶ T) :
    (f ≫ g).totalMap.hom = f.totalMap.hom ≫ g.totalMap.hom := rfl

/-! ### Gluing morphisms out of a family along a covering of its base -/

section GlueOut

variable {X : CurveFamily B hZ} {ι : Type*} (Xi : ι → CurveFamily B hZ) (φ : ∀ i, Xi i ⟶ X)

/-- The base change of `X` to the base of `Xᵢ`, read as a presheaf fibre product, maps to the total
space of `Xᵢ`. -/
def toPiece (i : ι) :
    pullback (yoneda.map (φ i).baseMap) (yonedaToBase X) ⟶ (Xi i).total.obj :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ (φ i).cartesian).lift (pullback.snd _ _)
    (pullback.fst _ _) pullback.condition.symm

/-- The composite of `toPiece Xi φ i` with the total map of `φ i` is the second projection. -/
theorem toPiece_totalMap (i : ι) :
    toPiece Xi φ i ≫ (φ i).totalMap.hom = pullback.snd _ _ :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ (φ i).cartesian).lift_fst _ _ _

/-- The composite of `toPiece Xi φ i` with the structure map of `Xᵢ` is the first projection. -/
theorem toPiece_toBase (i : ι) :
    toPiece Xi φ i ≫ yonedaToBase (Xi i) = pullback.fst _ _ :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ (φ i).cartesian).lift_snd _ _ _

/-- The inverse of `toPiece`. -/
def ofPiece (i : ι) :
    (Xi i).total.obj ⟶ pullback (yoneda.map (φ i).baseMap) (yonedaToBase X) :=
  pullback.lift (Xi i).toBase.hom (φ i).totalMap.hom
    (congrArg (fun k => k.hom) (φ i).cartesian.w).symm

/-- `ofPiece Xi φ i` is a section of `toPiece Xi φ i`. -/
theorem ofPiece_toPiece (i : ι) : ofPiece Xi φ i ≫ toPiece Xi φ i = 𝟙 _ := by
  apply (AlgebraicSpaces.isPullback_hom B integerBase hZ (φ i).cartesian).hom_ext
  · rw [Category.assoc, toPiece_totalMap, Category.id_comp]
    exact pullback.lift_snd _ _ _
  · show _ ≫ toPiece Xi φ i ≫ yonedaToBase (Xi i) = 𝟙 _ ≫ yonedaToBase (Xi i)
    rw [toPiece_toBase, Category.id_comp]
    exact pullback.lift_fst _ _ _

/-- The square defining `toOvl` commutes. -/
theorem toOvl_cond {i j : ι} {W : BigFppfOver B integerBase hZ} {gi : W ⟶ (Xi i).base}
    (gij : W ⟶ ovl Xi φ i j) (hgi : gij ≫ pullback.fst _ _ = gi) :
    pullback.snd (yoneda.map gi ≫ yoneda.map (φ i).baseMap)
        (yonedaToBase X) ≫ yonedaToBase X =
      (pullback.fst (yoneda.map gi ≫ yoneda.map (φ i).baseMap)
          (yonedaToBase X) ≫
        yoneda.map (gij ≫ eqToHom (restrictX_base X (wOvl Xi φ i j)).symm)) ≫
        yoneda.map (restrictXHom X (wOvl Xi φ i j)).baseMap := by
  have e : yoneda.map gi ≫ yoneda.map (φ i).baseMap =
      yoneda.map (gij ≫ eqToHom (restrictX_base X (wOvl Xi φ i j)).symm) ≫
        yoneda.map (restrictXHom X (wOvl Xi φ i j)).baseMap := by
    rw [restrictXHom_baseMap, ← Functor.map_comp, ← Functor.map_comp, ← hgi]
    congr 1
    simp [wOvl]
  exact pullback.condition.symm.trans ((congrArg (pullback.fst _ _ ≫ ·) e).trans
    (Category.assoc _ _ _).symm)

/-- The comparison from a base change of `X` along `W ⟶ Vᵢ ×_S Vⱼ` to the chosen restriction of `X`
to the overlap. -/
def toOvl {i j : ι} {W : BigFppfOver B integerBase hZ} {gi : W ⟶ (Xi i).base}
    (gij : W ⟶ ovl Xi φ i j) (hgi : gij ≫ pullback.fst _ _ = gi) :
    pullback (yoneda.map gi ≫ yoneda.map (φ i).baseMap) (yonedaToBase X) ⟶
      (restrictX X (wOvl Xi φ i j)).total.obj :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ
    (restrictXHom X (wOvl Xi φ i j)).cartesian).lift (pullback.snd _ _)
    (pullback.fst _ _ ≫ yoneda.map (gij ≫ eqToHom (restrictX_base X (wOvl Xi φ i j)).symm))
    (toOvl_cond Xi φ gij hgi)

/-- The composite of `toOvl` with the restriction morphism to `X` is the second projection. -/
theorem toOvl_snd {i j : ι} {W : BigFppfOver B integerBase hZ} {gi : W ⟶ (Xi i).base}
    (gij : W ⟶ ovl Xi φ i j) (hgi : gij ≫ pullback.fst _ _ = gi) :
    toOvl Xi φ gij hgi ≫ (restrictXHom X (wOvl Xi φ i j)).totalMap.hom = pullback.snd _ _ :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ
    (restrictXHom X (wOvl Xi φ i j)).cartesian).lift_fst _ _ _

/-- The composite of `toOvl` with the structure map of the chosen restriction is the first
projection followed by `gij`. -/
theorem toOvl_base {i j : ι} {W : BigFppfOver B integerBase hZ} {gi : W ⟶ (Xi i).base}
    (gij : W ⟶ ovl Xi φ i j) (hgi : gij ≫ pullback.fst _ _ = gi) :
    toOvl Xi φ gij hgi ≫ yonedaToBase (restrictX X (wOvl Xi φ i j)) =
      pullback.fst _ _ ≫ yoneda.map (gij ≫ eqToHom (restrictX_base X (wOvl Xi φ i j)).symm) :=
  (AlgebraicSpaces.isPullback_hom B integerBase hZ
    (restrictXHom X (wOvl Xi φ i j)).cartesian).lift_snd _ _ _

/-- The lift to the base change of `X` along `W ⟶ (Xi i).base`, followed by `toPiece Xi φ k`, is
`toOvl` followed by the factorization through `φ k` of the chosen restriction of `X` to the
overlap, where `gk` is the composite of `gij` with a map `gi'` from the overlap to `Vₖ`. -/
private theorem lift_toPiece_eq_toOvl_comp {i j : ι} {W : BigFppfOver B integerBase hZ}
    {gi : W ⟶ (Xi i).base} (gij : W ⟶ ovl Xi φ i j) (hgi : gij ≫ pullback.fst _ _ = gi) (k : ι)
    (gi' : ovl Xi φ i j ⟶ (Xi k).base) (hk : gi' ≫ (φ k).baseMap = wOvl Xi φ i j)
    {gk : W ⟶ (Xi k).base} (hgk : gij ≫ gi' = gk)
    (hw : (pullback.fst (yoneda.map gi ≫ yoneda.map (φ i).baseMap) (yonedaToBase X) ≫
      yoneda.map gk) ≫ yoneda.map (φ k).baseMap = pullback.snd _ _ ≫ yonedaToBase X) :
    pullback.lift (pullback.fst (yoneda.map gi ≫ yoneda.map (φ i).baseMap) (yonedaToBase X) ≫
        yoneda.map gk) (pullback.snd _ _) hw ≫ toPiece Xi φ k =
      toOvl Xi φ gij hgi ≫ (factorX (φ k) (wOvl Xi φ i j) gi' hk).totalMap.hom := by
  apply (AlgebraicSpaces.isPullback_hom B integerBase hZ (φ k).cartesian).hom_ext
  · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (toPiece_totalMap Xi φ k)).trans
      (pullback.lift_snd _ _ _))).trans ?_
    refine (toOvl_snd Xi φ gij hgi).symm.trans ?_
    rw [Category.assoc, ← CurveFamily.Hom.totalMap_hom_comp, factorX_comp]
  · show _ ≫ yonedaToBase (Xi k) = _ ≫ yonedaToBase (Xi k)
    rw [Category.assoc, toPiece_toBase, pullback.lift_fst, Category.assoc,
      CurveFamily.Hom.w_yoneda, ← Category.assoc, toOvl_base, Category.assoc]
    exact congrArg (pullback.fst _ _ ≫ ·) (by rw [← Functor.map_comp, factorX_baseMap, ← hgk]; simp)

/-- The lift to the base change of `X` along `W ⟶ (Xi i).base`, followed by `toPiece Xi φ i`, is
`toOvl` followed by the factorization through `φ i` of the chosen restriction of `X` to the
overlap `Vᵢ ×_S Vⱼ`. -/
theorem lift_toPiece_fst {i j : ι} {W : BigFppfOver B integerBase hZ} {gi : W ⟶ (Xi i).base}
    (gij : W ⟶ ovl Xi φ i j) (hgi : gij ≫ pullback.fst _ _ = gi)
    (hw : (pullback.fst (yoneda.map gi ≫ yoneda.map (φ i).baseMap) (yonedaToBase X) ≫
      yoneda.map gi) ≫ yoneda.map (φ i).baseMap = pullback.snd _ _ ≫ yonedaToBase X) :
    pullback.lift (pullback.fst (yoneda.map gi ≫ yoneda.map (φ i).baseMap) (yonedaToBase X) ≫
        yoneda.map gi) (pullback.snd _ _) hw ≫ toPiece Xi φ i =
      toOvl Xi φ gij hgi ≫ (factorX (φ i) (wOvl Xi φ i j) _ rfl).totalMap.hom :=
  lift_toPiece_eq_toOvl_comp Xi φ gij hgi i _ rfl hgi hw

/-- The lift to the base change of `X` along `W ⟶ (Xi j).base`, followed by `toPiece Xi φ j`, is
`toOvl` followed by the factorization through `φ j` of the chosen restriction of `X` to the
overlap `Vᵢ ×_S Vⱼ`. -/
theorem lift_toPiece_snd {i j : ι} {W : BigFppfOver B integerBase hZ} {gi : W ⟶ (Xi i).base}
    {gj : W ⟶ (Xi j).base} (gij : W ⟶ ovl Xi φ i j) (hgi : gij ≫ pullback.fst _ _ = gi)
    (hgj : gij ≫ pullback.snd _ _ = gj)
    (hw : (pullback.fst (yoneda.map gi ≫ yoneda.map (φ i).baseMap) (yonedaToBase X) ≫
      yoneda.map gj) ≫ yoneda.map (φ j).baseMap = pullback.snd _ _ ≫ yonedaToBase X) :
    pullback.lift (pullback.fst (yoneda.map gi ≫ yoneda.map (φ i).baseMap) (yonedaToBase X) ≫
        yoneda.map gj) (pullback.snd _ _) hw ≫ toPiece Xi φ j =
      toOvl Xi φ gij hgi ≫
        (factorX (φ j) (wOvl Xi φ i j) _ (snd_comp_ovl Xi φ i j)).totalMap.hom :=
  lift_toPiece_eq_toOvl_comp Xi φ gij hgi j _ (snd_comp_ovl Xi φ i j) hgj hw

/-- **Gluing a morphism out of `X` along a covering of its base.** Morphisms `nᵢ : Xᵢ ⟶ x` out of
the members of a covering of `X` by morphisms of families, lying over the morphisms of bases and
agreeing on the overlaps, glue to a morphism `X ⟶ x` over the base. -/
theorem exists_glue_out {x : CurveFamily B hZ} (hx : x.base = X.base)
    (hcov : Sieve.ofArrows (fun i => (Xi i).base) (fun i => (φ i).baseMap) ∈
      BigFppfOver.topology B integerBase hZ X.base)
    (n : ∀ i, (Xi i).total ⟶ x.total)
    (hn : ∀ i, (n i).hom ≫ yonedaToBase x ≫ yoneda.map (eqToHom hx) =
      yonedaToBase (Xi i) ≫ yoneda.map (φ i).baseMap)
    (hc : ∀ i j, (factorX (φ i) (wOvl Xi φ i j) _ rfl).totalMap ≫ n i =
      (factorX (φ j) (wOvl Xi φ i j) _ (snd_comp_ovl Xi φ i j)).totalMap ≫ n j) :
    ∃ c : X.total ⟶ x.total, c.hom ≫ yonedaToBase x ≫ yoneda.map (eqToHom hx) = yonedaToBase X ∧
      ∀ i, (φ i).totalMap ≫ c = n i := by
  have hglue := exists_hom_of_local X.total.2 x.total.2 (yonedaToBase X)
    (yonedaToBase x ≫ yoneda.map (eqToHom hx)) (fun i => (Xi i).base) (fun i => (φ i).baseMap)
    hcov (fun i => toPiece Xi φ i ≫ (n i).hom) (fun i => by
      rw [Category.assoc, hn, ← Category.assoc, toPiece_toBase, pullback.condition])
  obtain ⟨m₀, hm₀, hm₀μ⟩ := hglue (fun i j W gi gj h => by
    have hij : gi ≫ (φ i).baseMap = gj ≫ (φ j).baseMap :=
      Yoneda.fullyFaithful.map_injective (by rwa [Functor.map_comp, Functor.map_comp])
    rw [← Category.assoc, lift_toPiece_fst Xi φ (pullback.lift gi gj hij) (pullback.lift_fst _ _ _),
      ← Category.assoc, lift_toPiece_snd Xi φ (pullback.lift gi gj hij) (pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _), Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (congrArg (fun k => k.hom) (hc i j)))
  refine ⟨ObjectProperty.homMk m₀, hm₀, fun i => ?_⟩
  apply ObjectProperty.hom_ext
  show (φ i).totalMap.hom ≫ m₀ = (n i).hom
  have hl : (φ i).totalMap.hom = ofPiece Xi φ i ≫ pullback.snd _ _ := (pullback.lift_snd _ _ _).symm
  rw [hl, Category.assoc, hm₀μ i, ← Category.assoc, ofPiece_toPiece, Category.id_comp]

end GlueOut

/-! ### Descent of local models -/

section Descent

variable {X : CurveFamily B hZ} {ι : Type u} (Xi : ι → CurveFamily B hZ)
  (φ : ∀ i, Xi i ⟶ X) (m : ∀ i, Model R (Xi i))

/-- The base map of a fibre morphism of families of curves. -/
theorem baseMap_of_fibreHom {a b : CurveFamily B hZ} {U : BigFppfOver B integerBase hZ}
    {ha : (curvesProjectionOver B hZ).obj a = U} {hb : (curvesProjectionOver B hZ).obj b = U}
    {ψ : a ⟶ b} (h : Functor.FibreHom (curvesProjectionOver B hZ) a b ha hb ψ)
    (hab : a.base = b.base) : ψ.baseMap = eqToHom hab := by
  have := h
  have := IsHomLift.fac' (curvesProjectionOver B hZ) (eqToHom ha ≫ eqToHom hb.symm) ψ
  refine this.trans ?_
  simp only [eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- **Descent of local models.** A family of models `mᵢ` of the members `Xᵢ` of a covering of
`X` descends: there is a family `x` over the base of `X`, a morphism `c : X ⟶ x` over the base,
and morphisms from the targets of the `mᵢ` to `x` over the `φᵢ`, compatible with the
contractions. -/
theorem exists_descent_of_models (hR : IsModelRelation R)
    (hcov : Sieve.ofArrows (fun i => (Xi i).base) (fun i => (φ i).baseMap) ∈
      BigFppfOver.topology B integerBase hZ X.base) :
    ∃ (x : CurveFamily B hZ) (hx : x.base = X.base) (c : X.total ⟶ x.total)
      (ψ : ∀ i, (m i).family ⟶ x),
      c ≫ x.toBase = X.toBase ≫ schemeSpaceMap (eqToHom hx.symm) ∧
      ∀ i, (ψ i).baseMap = eqToHom (m i).base_eq ≫ (φ i).baseMap ≫ eqToHom hx.symm ∧
        (m i).contraction ≫ (ψ i).totalMap = (φ i).totalMap ≫ c := by
  have hp := CurveDeformation.curvesProjectionOver_isFiberedInGroupoids (B := B) (hZ := hZ)
  have hst : (curvesProjectionOver B hZ).IsStackInGroupoids.{u}
      (BigFppfOver.topology B integerBase hZ) :=
    (curvesProjectionOver_isStack B hZ).isStackInGroupoids hp
  obtain ⟨x, hx, xr, ψ, hψf, hψi, hcomp⟩ := hst.effective_descent _ _ hcov _ _ _ _ _ _ _ _ _ _ _
    _ _ _ (modelDescentDatum hR Xi φ m hp)
  have hx' : x.base = X.base := hx
  let ψ' : ∀ i, (m i).family ⟶ x := fun i => @inv _ _ _ _ (ψ i) (hψi i) ≫ (xr i).hom
  have hψ'b : ∀ i, (ψ' i).baseMap = eqToHom (m i).base_eq ≫ (φ i).baseMap ≫ eqToHom hx'.symm := by
    intro i
    have := hψi i
    have : IsIso (ψ i).baseMap := Functor.map_isIso (curvesProjectionOver B hZ) (ψ i)
    have h₁ := baseMap_of_fibreHom (hψf i) (((Restriction.hpt' (xr i)).trans (m i).base_eq.symm))
    have h₂ : (inv (ψ i)).baseMap = inv (ψ i).baseMap :=
      (curvesProjectionOver B hZ).map_inv (ψ i)
    show (inv (ψ i) ≫ (xr i).hom).baseMap = _
    rw [curveFamily_comp_baseMap, h₂]
    simp only [h₁, inv_eqToHom, Restriction.baseMap_hom (xr i) hx', eqToHom_trans_assoc]
    rfl
  let n : ∀ i, (Xi i).total ⟶ x.total := fun i => (m i).contraction ≫ (ψ' i).totalMap
  have hn : ∀ i, (n i).hom ≫ yonedaToBase x ≫ yoneda.map (eqToHom hx') =
      yonedaToBase (Xi i) ≫ yoneda.map (φ i).baseMap := by
    intro i
    have e : n i ≫ x.toBase ≫ schemeSpaceMap (eqToHom hx') =
        (Xi i).toBase ≫ schemeSpaceMap (φ i).baseMap := by
      show (m i).contraction ≫ (ψ' i).totalMap ≫ x.toBase ≫ schemeSpaceMap (eqToHom hx') = _
      rw [← Category.assoc (ψ' i).totalMap, (ψ' i).cartesian.w, ← Category.assoc, ← Category.assoc,
        hR.w (m i).isModel, Category.assoc, Category.assoc, ← schemeSpaceMap_comp,
        ← schemeSpaceMap_comp, hψ'b]
      simp
    exact congrArg (fun k => k.hom) e
  have hc : ∀ i j, (factorX (φ i) (wOvl Xi φ i j) _ rfl).totalMap ≫ n i =
      (factorX (φ j) (wOvl Xi φ i j) _ (snd_comp_ovl Xi φ i j)).totalMap ≫ n j := by
    intro i j
    obtain ⟨xrij, ψir, ψjr, -, -, hir, hjr, hri, hrj, hφ⟩ := hcomp i j
    have := localContraction_compat hR Xi φ m hp hx xr ψ (hψ := hψi) i j xrij ψir ψjr
      (hir := hir) (hjr := hjr) hri hrj hφ
    simpa only [n, ψ', curveFamily_comp_totalMap] using this
  obtain ⟨c, hc₁, hc₂⟩ := exists_glue_out Xi φ hx' hcov n hn hc
  refine ⟨x, hx', c, ψ', ?_, fun i => ⟨hψ'b i, (hc₂ i).symm⟩⟩
  apply ObjectProperty.hom_ext
  have : IsIso (yoneda.map (eqToHom hx')) := Functor.map_isIso _ _
  refine (cancel_mono (yoneda.map (eqToHom hx'))).1 ?_
  have e₁ : (c ≫ x.toBase).hom ≫ yoneda.map (eqToHom hx') = yonedaToBase X :=
    (Category.assoc _ _ _).trans hc₁
  have e₂ : (X.toBase ≫ schemeSpaceMap (eqToHom hx'.symm)).hom ≫ yoneda.map (eqToHom hx') =
      yonedaToBase X := by
    show (yonedaToBase X ≫ yoneda.map _) ≫ _ = _
    rw [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id, Category.comp_id]
  exact e₁.trans e₂.symm

end Descent

end AlgebraicGeometry.C1590Private

end
