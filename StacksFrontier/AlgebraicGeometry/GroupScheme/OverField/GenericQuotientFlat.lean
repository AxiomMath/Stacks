/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatAtPullbackMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Open.OverField
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Multiplication
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StalkIdentityLocalCartier
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of a rational quotient map of a group scheme, by translation

Let `G` be a group scheme over a field `k`, let `π : V ⟶ X` be a morphism from an open `V` of
`G` to a `k`-scheme `X`, and suppose that left translation descends along `π` to a rational map
`F : G × X ⇢ X`, that is `F (a, π b) = π (a b)` on an open `D''` of `G × G`.  Then `π` is flat at
`v = w₁ w₂` as soon as `id × π` is flat at `w = (w₁, w₂) ∈ D''` and injective on local rings at
`(w₁, w₁ w₂)`, provided `(w₁⁻¹, w₁ w₂) ∈ D''` as well (`flatAt_of_translation`).

When `G` and `X` are integral, `k` is algebraically closed and `π` is dominant, `π` is flat at
every point of `μ (D'' ∩ (w ↦ (w₁⁻¹, w₁ w₂))⁻¹ D'')` (`flatAt_of_rationalAction`), which is a
nonempty open of `V` when `D''` is nonempty.

## Main definitions

* `AlgebraicGeometry.GenericQuotientFlat.FlatAt`: flatness of a morphism at a point, that is
  flatness of its map on local rings.

## Main results

* `AlgebraicGeometry.GenericQuotientFlat.flatAt_of_translation`: `π` is flat at `w₁ w₂`.
* `AlgebraicGeometry.GenericQuotientFlat.flatAt_of_rationalAction`: `π` is flat at every point
  of `μ (D'' ∩ (w ↦ (w₁⁻¹, w₁ w₂))⁻¹ D'')`.
* `AlgebraicGeometry.GenericQuotientFlat.exists_open_flatAt_of_rationalAction` and
  `AlgebraicGeometry.GenericQuotientFlat.exists_open_flatAt_of_localRationalAction`: `π` is flat
  on a nonempty open of `V`.
* `AlgebraicGeometry.GenericQuotientFlat.isIso_stalkMap_of_local_inverse`: a partially defined
  morphism with a local inverse, tested against morphisms injective on local rings, is an
  isomorphism on local rings.
* `RingHom.Flat.of_comp_faithfullyFlat`: flatness descends along a faithfully flat second
  factor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace RingHom

/-- If `g ∘ f` is flat and `g` is faithfully flat then `f` is flat. -/
@[ega "IV 2.2.11" "special case", ega "IV 2.2.13" "(iii)", ega "IV 6.6.1" "(ii), special case"]
theorem Flat.of_comp_faithfullyFlat {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hg : g.FaithfullyFlat) (hgf : (g.comp f).Flat) : f.Flat := by
  algebraize [f, g, g.comp f]
  have : Module.FaithfullyFlat S T := hg
  have : Module.Flat R T := hgf
  rw [RingHom.Flat, Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ φ hφ
  show Function.Injective (LinearMap.baseChange S φ)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective S T]
  let eP := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N
  have e : LinearMap.lTensor T (LinearMap.baseChange S φ) =
      (eP.symm.toLinearMap.restrictScalars S) ∘ₗ ((LinearMap.baseChange T φ).restrictScalars S) ∘ₗ
        (eN.toLinearMap.restrictScalars S) := by
    ext t n
    simp [eP, eN]
  rw [e]
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  exact (LinearEquiv.injective _).comp
    ((Module.Flat.lTensor_preserves_injective_linearMap φ hφ).comp (LinearEquiv.injective _))

end RingHom

namespace AlgebraicGeometry.GenericQuotientFlat

/-- A morphism of schemes is flat at a point if its map on local rings there is flat. -/
def FlatAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop := (f.stalkMap x).hom.Flat

/-- A flat morphism is flat at every point. -/
lemma flatAt_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) : FlatAt f x :=
  Flat.stalkMap f x

/-- A morphism inducing an isomorphism on local rings at `x` is flat at `x`. -/
lemma flatAt_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] : FlatAt f x :=
  RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

/-- If `f` is flat at `x` and `g` is flat at `f x`, then `f ≫ g` is flat at `x`. -/
lemma flatAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (hf : FlatAt f x)
    (hg : FlatAt g (f x)) : FlatAt (f ≫ g) x := by
  rw [FlatAt, Scheme.Hom.stalkMap_comp]
  exact RingHom.Flat.comp hg hf

/-- Flatness at a point only depends on the morphism. -/
lemma flatAt_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (x : X) :
    FlatAt f x ↔ FlatAt g x := by
  subst hfg; rfl

/-- A stalk map that is flat at `x` is faithfully flat. -/
private lemma faithfullyFlat_stalkMap_of_flatAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : FlatAt f x) : (f.stalkMap x).hom.FaithfullyFlat := by
  unfold FlatAt at hf
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Flatness at a point descends along a morphism that is flat at that point. -/
lemma flatAt_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (hf : FlatAt f x)
    (hfg : FlatAt (f ≫ g) x) : FlatAt g (f x) := by
  rw [FlatAt, Scheme.Hom.stalkMap_comp] at hfg
  exact RingHom.Flat.of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flatAt f x hf) hfg

/-- An isomorphism on local rings followed by a flat map is flat. -/
lemma flatAt_comp_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [IsIso (g.stalkMap (f x))] (hf : FlatAt f x) : FlatAt (f ≫ g) x :=
  flatAt_comp f g x hf (flatAt_of_isIso_stalkMap g (f x))

/-- **The translation argument on local rings.**  If `m ≫ π = e ≫ Φ ≫ s` with `m` and `e` flat
at `a`, `Φ` an isomorphism on local rings at `e a` and `s` flat at `Φ (e a)`, then `π` is flat at
`m a`. -/
theorem flatAt_of_factorization {E V X D Z : Scheme.{u}} (m : E ⟶ V) (π : V ⟶ X) (e : E ⟶ D)
    (Φ : D ⟶ Z) (s : Z ⟶ X) (h : m ≫ π = e ≫ Φ ≫ s) (a : E) (hm : FlatAt m a)
    (he : FlatAt e a) [IsIso (Φ.stalkMap (e a))] (hs : FlatAt s (Φ (e a))) :
    FlatAt π (m a) := by
  refine flatAt_of_comp m π a hm ?_
  rw [flatAt_congr h, ← Category.assoc]
  exact flatAt_comp (e ≫ Φ) s a (flatAt_comp_of_isIso e Φ a he) hs

/-- Flatness at a point is unchanged by restricting to open subschemes. -/
lemma flatAt_resLE_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : V) : FlatAt (f.resLE U V e) x ↔ FlatAt f x.1 := by
  let α := Scheme.Hom.resLEStalkMap f e x
  have hw : (f.resLE U V e).stalkMap x ≫ α.hom.right = α.hom.left ≫ f.stalkMap x.1 :=
    α.hom.w.symm
  have hl : Function.Bijective α.hom.left.hom :=
    ConcreteCategory.bijective_of_isIso _
  have hr : Function.Bijective α.hom.right.hom :=
    ConcreteCategory.bijective_of_isIso _
  unfold FlatAt
  rw [← RingHom.Flat.comp_iff_of_bijective_left hr,
    ← CommRingCat.hom_comp, hw, CommRingCat.hom_comp,
    RingHom.Flat.comp_iff_of_bijective_right hl]


/-- If `f` induces an isomorphism on local rings at `x`, so does `f.stalkMapOfEq x y h`. -/
lemma isIso_stalkMapOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y)
    [IsIso (f.stalkMap x)] : IsIso (f.stalkMapOfEq x y h) := by
  rw [Scheme.Hom.stalkMapOfEq]; infer_instance

/-- If `f.stalkMapOfEq x y h` is an isomorphism, so is `f.stalkMap x`. -/
lemma isIso_stalkMap_of_isIso_stalkMapOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) [IsIso (f.stalkMapOfEq x y h)] : IsIso (f.stalkMap x) := by
  have e : f.stalkMap x = inv (Y.presheaf.stalkCongr (.of_eq h.symm)).hom ≫
      f.stalkMapOfEq x y h := by
    rw [Scheme.Hom.stalkMapOfEq, IsIso.inv_hom_id_assoc]
  rw [e]; infer_instance

/-- If `f.stalkMap x` is injective, so is `f.stalkMapOfEq x y h`. -/
lemma injective_stalkMapOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y)
    (hf : Function.Injective (f.stalkMap x).hom) :
    Function.Injective (f.stalkMapOfEq x y h).hom := by
  rw [Scheme.Hom.stalkMapOfEq, CommRingCat.hom_comp]
  exact hf.comp (ConcreteCategory.bijective_of_isIso _).1

/-- A morphism `φ₁ : D ⟶ Q` defined on an open `D` of `Q` induces an isomorphism on local rings
at `z` once it has a local inverse `φ₂` defined on an open `D'`, tested against two morphisms
`a₁`, `a₂` with injective maps on local rings: `φ₂ ∘ φ₁ = id` after `a₁` and `φ₁ ∘ φ₂ = id`
after `a₂`. -/
theorem isIso_stalkMap_of_local_inverse {Q T₁ T₂ : Scheme.{u}} {D D' : Q.Opens}
    (φ₁ : D.toScheme ⟶ Q) (φ₂ : D'.toScheme ⟶ Q) (z : D.toScheme) (z' : D'.toScheme)
    (hz' : φ₁ z = D'.ι z')
    (a₁ : T₁ ⟶ D.toScheme) (c₁ : T₁ ⟶ D'.toScheme) (t₁ : T₁) (ht₁ : a₁ t₁ = z)
    (hc₁ : c₁ ≫ D'.ι = a₁ ≫ φ₁) (hc₁' : c₁ ≫ φ₂ = a₁ ≫ D.ι)
    (ha₁ : Function.Injective (a₁.stalkMap t₁).hom)
    (a₂ : T₂ ⟶ D'.toScheme) (c₂ : T₂ ⟶ D.toScheme) (t₂ : T₂) (ht₂ : a₂ t₂ = z')
    (hc₂ : c₂ ≫ D.ι = a₂ ≫ φ₂) (hc₂' : c₂ ≫ φ₁ = a₂ ≫ D'.ι)
    (ha₂ : Function.Injective (a₂.stalkMap t₂).hom) :
    IsIso (φ₁.stalkMap z) := by
  have hct₁ : c₁ t₁ = z' := by
    apply D'.ι.isOpenEmbedding.injective
    show (c₁ ≫ D'.ι) t₁ = _
    rw [hc₁, Scheme.Hom.comp_apply, ht₁, hz']
  have hφ₂z' : φ₂ z' = D.ι z := by
    rw [← hct₁, ← Scheme.Hom.comp_apply, hc₁', Scheme.Hom.comp_apply, ht₁]
  have hct₂ : c₂ t₂ = z := by
    apply D.ι.isOpenEmbedding.injective
    show (c₂ ≫ D.ι) t₂ = _
    rw [hc₂, Scheme.Hom.comp_apply, ht₂, hφ₂z']
  let I₀ := D.ι.stalkMapOfEq z (D.ι z) rfl
  let I₁ := D'.ι.stalkMapOfEq z' (D'.ι z') rfl
  let S₁ := φ₁.stalkMapOfEq z (D'.ι z') hz'
  let S₂ := φ₂.stalkMapOfEq z' (D.ι z) hφ₂z'
  let A₁ := a₁.stalkMapOfEq t₁ z ht₁
  let A₂ := a₂.stalkMapOfEq t₂ z' ht₂
  let C₁ := c₁.stalkMapOfEq t₁ z' hct₁
  let C₂ := c₂.stalkMapOfEq t₂ z hct₂
  have : IsIso I₀ := isIso_stalkMapOfEq _ _ _ _
  have : IsIso I₁ := isIso_stalkMapOfEq _ _ _ _
  have hA₁ : Mono A₁ := ConcreteCategory.mono_of_injective _ (injective_stalkMapOfEq _ _ _ _ ha₁)
  have hA₂ : Mono A₂ := ConcreteCategory.mono_of_injective _ (injective_stalkMapOfEq _ _ _ _ ha₂)
  have k₁ : I₁ ≫ C₁ = S₁ ≫ A₁ := by
    rw [← Scheme.Hom.stalkMapOfEq_comp c₁ D'.ι t₁ z' (D'.ι z') hct₁ rfl
      (by rw [Scheme.Hom.comp_apply, hct₁]),
      ← Scheme.Hom.stalkMapOfEq_comp a₁ φ₁ t₁ z (D'.ι z') ht₁ hz'
      (by rw [Scheme.Hom.comp_apply, ht₁, hz'])]
    exact Scheme.Hom.stalkMapOfEq_congr hc₁ _ _ _ _
  have k₂ : S₂ ≫ C₁ = I₀ ≫ A₁ := by
    rw [← Scheme.Hom.stalkMapOfEq_comp c₁ φ₂ t₁ z' (D.ι z) hct₁ hφ₂z'
      (by rw [Scheme.Hom.comp_apply, hct₁, hφ₂z']),
      ← Scheme.Hom.stalkMapOfEq_comp a₁ D.ι t₁ z (D.ι z) ht₁ rfl
      (by rw [Scheme.Hom.comp_apply, ht₁])]
    exact Scheme.Hom.stalkMapOfEq_congr hc₁' _ _ _ _
  have k₃ : I₀ ≫ C₂ = S₂ ≫ A₂ := by
    rw [← Scheme.Hom.stalkMapOfEq_comp c₂ D.ι t₂ z (D.ι z) hct₂ rfl
      (by rw [Scheme.Hom.comp_apply, hct₂]),
      ← Scheme.Hom.stalkMapOfEq_comp a₂ φ₂ t₂ z' (D.ι z) ht₂ hφ₂z'
      (by rw [Scheme.Hom.comp_apply, ht₂, hφ₂z'])]
    exact Scheme.Hom.stalkMapOfEq_congr hc₂ _ _ _ _
  have k₄ : S₁ ≫ C₂ = I₁ ≫ A₂ := by
    rw [← Scheme.Hom.stalkMapOfEq_comp c₂ φ₁ t₂ z (D'.ι z') hct₂ hz'
      (by rw [Scheme.Hom.comp_apply, hct₂, hz']),
      ← Scheme.Hom.stalkMapOfEq_comp a₂ D'.ι t₂ z' (D'.ι z') ht₂ rfl
      (by rw [Scheme.Hom.comp_apply, ht₂])]
    exact Scheme.Hom.stalkMapOfEq_congr hc₂' _ _ _ _
  have l₁ : S₂ ≫ inv I₁ ≫ S₁ = I₀ := by
    rw [← cancel_mono A₁, Category.assoc, Category.assoc, ← k₁, IsIso.inv_hom_id_assoc, k₂]
  have l₂ : S₁ ≫ inv I₀ ≫ S₂ = I₁ := by
    rw [← cancel_mono A₂, Category.assoc, Category.assoc, ← k₃, IsIso.inv_hom_id_assoc, k₄]
  have : IsIso S₁ := by
    refine ⟨inv I₀ ≫ S₂ ≫ inv I₁, ?_, ?_⟩
    · rw [← Category.assoc, ← Category.assoc, Category.assoc S₁, l₂, IsIso.hom_inv_id]
    · rw [Category.assoc, Category.assoc, l₁, IsIso.inv_hom_id]
  exact isIso_stalkMap_of_isIso_stalkMapOfEq φ₁ z _ hz'


/-! ### Generic points -/

/-- For a dominant morphism of integral schemes, the maps on local rings are injective. -/
lemma injective_stalkMap_of_isDominant {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) : Function.Injective (f.stalkMap x).hom := by
  have hsp : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have key := f.stalkSpecializes_stalkMap (genericPoint X) x hsp
  have hgen := map_genericPoint_of_isDominant f
  have hY : genericPoint Y ⤳ f (genericPoint X) := hgen ▸ specializes_refl _
  have h₁ : Function.Injective
      (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes hsp)).hom := by
    have hinj : Function.Injective
        (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial :
          genericPoint Y ⤳ f x)).hom :=
      IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
    rw [← TopCat.Presheaf.stalkSpecializes_comp (h := hY) (h' := f.base.hom.map_specializes hsp),
      CommRingCat.hom_comp, RingHom.coe_comp] at hinj
    exact Function.Injective.of_comp hinj
  have h₂ : Function.Injective (f.stalkMap (genericPoint X)).hom := by
    have : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
      rw [hgen]; exact Field.toIsField (Y.functionField)
    let := this.toField
    exact RingHom.injective _
  have h₃ : Function.Injective
      (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes hsp) ≫
        f.stalkMap (genericPoint X)).hom := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact h₂.comp h₁
  rw [key, CommRingCat.hom_comp, RingHom.coe_comp] at h₃
  exact Function.Injective.of_comp h₃

/-- The stalk of an integral scheme at its generic point is a field, so every morphism into an
integral scheme is flat at points mapping to the generic point. -/
lemma flatAt_of_apply_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) (x : X)
    (hx : f x = genericPoint Y) : FlatAt f x := by
  have : IsField (Y.presheaf.stalk (f x)) := by
    rw [hx]; exact Field.toIsField (Y.functionField)
  exact RingHom.Flat.of_isField this _

/-- A point lying in every nonempty open subset of an irreducible scheme is its generic
point. -/
lemma eq_genericPoint_of_forall_mem {X : Scheme.{u}} [IrreducibleSpace X] (x : X)
    (hx : ∀ U : X.Opens, (U : Set X).Nonempty → x ∈ U) : x = genericPoint X := by
  have hgen : IsGenericPoint x ⊤ := by
    rw [isGenericPoint_def, Set.top_eq_univ, ← Set.compl_empty_iff, ← Set.not_nonempty_iff_eq_empty]
    exact fun hne ↦ hx ⟨_, isClosed_closure.isOpen_compl⟩ hne (subset_closure rfl)
  exact hgen.eq (genericPoint_spec X)

/-- Over a separably closed field `k`, let `A` and `B` be `k`-schemes with `B` irreducible.  For a
point `x` of `A` there is a point `p` of `A ×_k B` over `x`, with second coordinate the generic
point of `B`, lying in every open subset that meets the fibre over `x`. -/
lemma exists_fiberGenericPoint {k : Type u} [Field k] [IsSepClosed k] {A B : Scheme.{u}}
    (a : A ⟶ Spec (.of k)) (b : B ⟶ Spec (.of k)) [IrreducibleSpace B] (x : A) :
    ∃ p : ↑(pullback a b), pullback.fst a b p = x ∧ pullback.snd a b p = genericPoint B ∧
      ∀ O : (pullback a b).Opens, (∃ q ∈ O, pullback.fst a b q = x) → p ∈ O := by
  have : GeometricallyIrreducible b :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k B b
  let f := pullback.fst a b
  let g : f.fiber x := genericPoint (f.fiber x)
  let p := f.fiberι x g
  have hp : f p = x := by
    show (f.fiberι x ≫ f) g = x
    rw [Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hO : ∀ O : (pullback a b).Opens, (∃ q ∈ O, f q = x) → p ∈ O := by
    rintro O ⟨q, hqO, hqx⟩
    obtain ⟨y, rfl⟩ : q ∈ Set.range (f.fiberι x) := by
      rw [Scheme.Hom.range_fiberι]; exact hqx
    have hne : ((f.fiberι x ⁻¹ᵁ O : (f.fiber x).Opens) : Set (f.fiber x)).Nonempty :=
      ⟨y, hqO⟩
    exact ((genericPoint_spec (f.fiber x)).mem_open_set_iff (f.fiberι x ⁻¹ᵁ O).isOpen).mpr
      (by simpa using hne)
  refine ⟨p, hp, ?_, hO⟩
  apply eq_genericPoint_of_forall_mem
  rintro U ⟨u, hu⟩
  have hsub : Subsingleton (Spec (.of k)) := by
    show Subsingleton (PrimeSpectrum k); infer_instance
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := b) x u
    (Subsingleton.elim (α := Spec (.of k)) _ _)
  exact hO (pullback.snd a b ⁻¹ᵁ U) ⟨q, by simpa [hq₂] using hu, hq₁⟩

/-! ### The shearing maps of a group scheme -/

section Shear

open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- The multiplication of `G` is the product of the two projections `G × G ⟶ G`. -/
lemma mu_eq_fst_mul_snd : μ[G] = fst G G * snd G G := by
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp]

/-- `(a, b) ↦ (a, a b)`. -/
noncomputable abbrev shearO : G ⊗ G ⟶ G ⊗ G := lift (fst G G) μ[G]

/-- `(a, c) ↦ (a, a⁻¹ c)`. -/
noncomputable abbrev unshearO : G ⊗ G ⟶ G ⊗ G := lift (fst G G) ((fst G G)⁻¹ * snd G G)

/-- `(a, b) ↦ (a⁻¹, b)`. -/
noncomputable abbrev invFstO : G ⊗ G ⟶ G ⊗ G := lift (fst G G)⁻¹ (snd G G)

/-- `(a, c) ↦ (a, a⁻¹ c)` is a left inverse of `(a, b) ↦ (a, a b)`. -/
lemma shearO_unshearO : shearO G ≫ unshearO G = 𝟙 _ := by
  apply hom_ext
  · simp
  · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd,
      mu_eq_fst_mul_snd, inv_mul_cancel_left, Category.id_comp]

/-- The second coordinate of `(a, c) ↦ (a, a⁻¹ c)` is `a⁻¹ c`. -/
lemma unshearO_snd : unshearO G ≫ snd G G = invFstO G ≫ μ[G] := by
  rw [lift_snd, mu_eq_fst_mul_snd, MonObj.comp_mul, lift_fst, lift_snd]

/-- `a (a⁻¹ c) = c`. -/
lemma unshearO_mu : unshearO G ≫ μ[G] = snd G G := by
  rw [mu_eq_fst_mul_snd, MonObj.comp_mul, lift_fst, lift_snd, mul_inv_cancel_left]

/-- `a⁻¹ (a b) = b`. -/
lemma shearO_invFstO_mu : shearO G ≫ invFstO G ≫ μ[G] = snd G G := by
  rw [← unshearO_snd, ← Category.assoc, shearO_unshearO, Category.id_comp]

/-- The first coordinate of `(a, b) ↦ (a⁻¹, b)` is `a⁻¹`. -/
lemma invFstO_fst : invFstO G ≫ fst G G = (fst G G)⁻¹ := lift_fst _ _

/-- The second coordinate of `(a, b) ↦ (a⁻¹, b)` is `b`. -/
lemma invFstO_snd : invFstO G ≫ snd G G = snd G G := lift_snd _ _

/-- The first coordinate of `(a, b) ↦ (a, a b)` is `a`. -/
lemma shearO_fst : shearO G ≫ fst G G = fst G G := lift_fst _ _

/-- The second coordinate of `(a, b) ↦ (a, a b)` is `a b`. -/
lemma shearO_snd : shearO G ≫ snd G G = μ[G] := lift_snd _ _

/-- The first coordinate of `(a, c) ↦ (a, a⁻¹ c)` is `a`. -/
lemma unshearO_fst : unshearO G ≫ fst G G = fst G G := lift_fst _ _

/-- The first coordinate of `(a, b) ↦ (a⁻¹, a b)` is `a⁻¹`. -/
lemma shearO_invFstO_fst : shearO G ≫ invFstO G ≫ fst G G = (fst G G)⁻¹ := by
  rw [invFstO_fst, GrpObj.comp_inv, shearO_fst]

end Shear


/-! ### Open immersions and local rings -/

/-- Following a morphism by an open immersion does not change flatness at a point. -/
lemma flatAt_iff_of_comp_openImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] (x : X) : FlatAt (f ≫ j) x ↔ FlatAt f x := by
  unfold FlatAt
  rw [Scheme.Hom.stalkMap_comp]
  show ((f.stalkMap x).hom.comp (j.stalkMap (f x)).hom).Flat ↔ _
  exact RingHom.Flat.comp_iff_of_bijective_right (ConcreteCategory.bijective_of_isIso _)

/-- Precomposing a morphism with an open immersion does not change flatness at a point. -/
lemma flatAt_iff_of_openImmersion_comp {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z)
    [IsOpenImmersion j] (x : X) : FlatAt (j ≫ f) x ↔ FlatAt f (j x) := by
  unfold FlatAt
  rw [Scheme.Hom.stalkMap_comp]
  show ((j.stalkMap x).hom.comp (f.stalkMap (j x)).hom).Flat ↔ _
  exact RingHom.Flat.comp_iff_of_bijective_left (ConcreteCategory.bijective_of_isIso _)

/-- Following a morphism by an open immersion does not change injectivity on local rings. -/
lemma injective_iff_of_comp_openImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] (x : X) :
    Function.Injective ((f ≫ j).stalkMap x).hom ↔ Function.Injective (f.stalkMap x).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  show Function.Injective ((f.stalkMap x).hom ∘ (j.stalkMap (f x)).hom) ↔ _
  exact Function.Injective.of_comp_iff' _ (ConcreteCategory.bijective_of_isIso _)

/-- Precomposing a morphism with an open immersion does not change injectivity on local rings. -/
lemma injective_iff_of_openImmersion_comp {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z)
    [IsOpenImmersion j] (x : X) :
    Function.Injective ((j ≫ f).stalkMap x).hom ↔ Function.Injective (f.stalkMap (j x)).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  show Function.Injective ((j.stalkMap x).hom ∘ (f.stalkMap (j x)).hom) ↔ _
  exact Function.Injective.of_comp_iff (ConcreteCategory.bijective_of_isIso _).1 _

/-- Injectivity on local rings at a point only depends on the morphism. -/
lemma injective_stalkMap_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (x : X) :
    Function.Injective (f.stalkMap x).hom ↔ Function.Injective (g.stalkMap x).hom := by
  subst h; rfl

/-- A morphism flat at `x` is injective on local rings at `x`. -/
lemma injective_of_flatAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (hf : FlatAt f x) :
    Function.Injective (f.stalkMap x).hom := by
  exact (faithfullyFlat_stalkMap_of_flatAt f x hf).injective

/-! ### The translation argument for a group scheme acting rationally -/

section Translation

open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] (X : Over (Spec (.of k)))

/-- The open `G × V` of `G × G`. -/
noncomputable abbrev EV (V : G.left.Opens) : (G ⊗ G).left.Opens := (snd G G).left ⁻¹ᵁ V

/-- `id × π : G × V ⟶ G × X`. -/
noncomputable def onePi (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) : (EV G V).toScheme ⟶ (G ⊗ X).left :=
  pullback.lift ((EV G V).ι ≫ (fst G G).left) ((snd G G).left.resLE V (EV G V) le_rfl ≫ π)
    (by
      rw [Category.assoc, Category.assoc, hπ, ← Category.assoc (Scheme.Hom.resLE _ _ _ _),
        Scheme.Hom.resLE_comp_ι, Category.assoc]
      exact congrArg ((EV G V).ι ≫ ·) pullback.condition)

omit [GrpObj G] in
/-- The first coordinate of `id × π` is the first projection. -/
@[reassoc]
lemma onePi_fst (V : G.left.Opens) (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom) :
    onePi G X V π hπ ≫ (fst G X).left = (EV G V).ι ≫ (fst G G).left :=
  pullback.lift_fst _ _ _

omit [GrpObj G] in
/-- The second coordinate of `id × π` is `π` of the second projection. -/
@[reassoc]
lemma onePi_snd (V : G.left.Opens) (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom) :
    onePi G X V π hπ ≫ (snd G X).left = (snd G G).left.resLE V (EV G V) le_rfl ≫ π :=
  pullback.lift_snd _ _ _

/-- `(a, x) ↦ (a, F(a, x))`, on the domain `D` of `F`. -/
noncomputable def sigma (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) : D.toScheme ⟶ (G ⊗ X).left :=
  pullback.lift (D.ι ≫ (fst G X).left) F (by rw [hF, Category.assoc]; rfl)

omit [GrpObj G] in
/-- The first coordinate of `(a, x) ↦ (a, F(a, x))` is `a`. -/
@[reassoc]
lemma sigma_fst (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) :
    sigma G X D F hF ≫ (fst G X).left = D.ι ≫ (fst G X).left :=
  pullback.lift_fst _ _ _

omit [GrpObj G] in
/-- The second coordinate of `(a, x) ↦ (a, F(a, x))` is `F(a, x)`. -/
@[reassoc]
lemma sigma_snd (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) : sigma G X D F hF ≫ (snd G X).left = F :=
  pullback.lift_snd _ _ _


/-- `(a, x) ↦ (a⁻¹, x)` on `G × X`. -/
noncomputable abbrev invL : (G ⊗ X).left ⟶ (G ⊗ X).left := (lift (fst G X)⁻¹ (snd G X)).left

/-- The first coordinate of `(a, x) ↦ (a⁻¹, x)` is `a⁻¹`. -/
@[reassoc]
lemma invL_fst : invL G X ≫ (fst G X).left = ((fst G X)⁻¹).left := by
  rw [← Over.comp_left, lift_fst]

/-- The second coordinate of `(a, x) ↦ (a⁻¹, x)` is `x`. -/
@[reassoc]
lemma invL_snd : invL G X ≫ (snd G X).left = (snd G X).left := by
  rw [← Over.comp_left, lift_snd]

/-- The domain of `(a, x) ↦ F(a⁻¹, x)`. -/
noncomputable abbrev D' (D : (G ⊗ X).left.Opens) : (G ⊗ X).left.Opens := invL G X ⁻¹ᵁ D

/-- `(a, x) ↦ (a, F(a⁻¹, x))`. -/
noncomputable def sigma' (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) : (D' G X D).toScheme ⟶ (G ⊗ X).left :=
  pullback.lift ((D' G X D).ι ≫ (fst G X).left) ((invL G X).resLE D (D' G X D) le_rfl ≫ F)
    (by
      rw [Category.assoc, Category.assoc, hF, ← Category.assoc (Scheme.Hom.resLE _ _ _ _),
        Scheme.Hom.resLE_comp_ι, Category.assoc]
      congr 1
      rw [Over.w (fst G X)]
      exact (Over.w (lift (fst G X)⁻¹ (snd G X))).symm)

/-- The first coordinate of `(a, x) ↦ (a, F(a⁻¹, x))` is `a`. -/
@[reassoc]
lemma sigma'_fst (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) :
    sigma' G X D F hF ≫ (fst G X).left = (D' G X D).ι ≫ (fst G X).left :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `(a, x) ↦ (a, F(a⁻¹, x))` is `F(a⁻¹, x)`. -/
@[reassoc]
lemma sigma'_snd (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) :
    sigma' G X D F hF ≫ (snd G X).left = (invL G X).resLE D (D' G X D) le_rfl ≫ F :=
  pullback.lift_snd _ _ _

/-- `(a, b) ↦ (a, a b)` on `G × G`. -/
noncomputable abbrev shearL : (G ⊗ G).left ⟶ (G ⊗ G).left := (shearO G).left

/-- `(a, c) ↦ (a, a⁻¹ c)` on `G × G`. -/
noncomputable abbrev unshearL : (G ⊗ G).left ⟶ (G ⊗ G).left := (unshearO G).left

/-- `(a, b) ↦ (a⁻¹, b)` on `G × G`. -/
noncomputable abbrev invFstL : (G ⊗ G).left ⟶ (G ⊗ G).left := (invFstO G).left

/-- The first coordinate of `(a, b) ↦ (a, a b)` on `G × G` is `a`. -/
@[reassoc]
lemma shearL_fst : shearL G ≫ (fst G G).left = (fst G G).left := by
  rw [← Over.comp_left, shearO_fst]

/-- The second coordinate of `(a, b) ↦ (a, a b)` on `G × G` is `a b`. -/
@[reassoc]
lemma shearL_snd : shearL G ≫ (snd G G).left = μ[G].left := by
  rw [← Over.comp_left, shearO_snd]

/-- The first coordinate of `(a, c) ↦ (a, a⁻¹ c)` on `G × G` is `a`. -/
@[reassoc]
lemma unshearL_fst : unshearL G ≫ (fst G G).left = (fst G G).left := by
  rw [← Over.comp_left, unshearO_fst]

/-- The second coordinate of `(a, c) ↦ (a, a⁻¹ c)` on `G × G` is `a⁻¹ c`. -/
@[reassoc]
lemma unshearL_snd : unshearL G ≫ (snd G G).left = invFstL G ≫ μ[G].left := by
  rw [← Over.comp_left, unshearO_snd, Over.comp_left]

/-- `a (a⁻¹ c) = c` on `G × G`. -/
@[reassoc]
lemma unshearL_mu : unshearL G ≫ μ[G].left = (snd G G).left := by
  rw [← Over.comp_left, unshearO_mu]

/-- The second coordinate of `(a, b) ↦ (a⁻¹, b)` on `G × G` is `b`. -/
@[reassoc]
lemma invFstL_snd : invFstL G ≫ (snd G G).left = (snd G G).left := by
  rw [← Over.comp_left, invFstO_snd]

/-- The first coordinate of `(a, b) ↦ (a⁻¹, b)` on `G × G` is `a⁻¹`. -/
@[reassoc]
lemma invFstL_fst : invFstL G ≫ (fst G G).left = (fst G G).left ≫ ι[G].left := by
  rw [← Over.comp_left, invFstO_fst, Hom.inv_def, Over.comp_left]

/-- `a⁻¹ (a b) = b` on `G × G`. -/
@[reassoc]
lemma shearL_invFstL_mu : shearL G ≫ invFstL G ≫ μ[G].left = (snd G G).left := by
  rw [← Over.comp_left, ← Over.comp_left, shearO_invFstO_mu]

/-- The first coordinate of `(a, b) ↦ (a⁻¹, a b)` on `G × G` is `a⁻¹`. -/
@[reassoc]
lemma shearL_invFstL_fst :
    shearL G ≫ invFstL G ≫ (fst G G).left = (fst G G).left ≫ ι[G].left := by
  rw [← Over.comp_left, ← Over.comp_left, shearO_invFstO_fst, Hom.inv_def, Over.comp_left]

/-- `(a, c) ↦ (a, a⁻¹ c)` is a left inverse of `(a, b) ↦ (a, a b)` on `G × G`. -/
@[reassoc]
lemma shearL_unshearL : shearL G ≫ unshearL G = 𝟙 _ := by
  rw [← Over.comp_left, shearO_unshearO, Over.id_left]

/-- The first coordinate of `(a, x) ↦ (a⁻¹, x)` is the inverse of the first projection. -/
@[reassoc]
lemma invL_fst' : invL G X ≫ (fst G X).left = (fst G X).left ≫ ι[G].left := by
  rw [invL_fst, Hom.inv_def, Over.comp_left]

/-- The multiplication of a group scheme over a field is flat. -/
instance flat_mu : Flat μ[G].left := by
  have e : IsIso (shearL G) := ⟨⟨unshearL G, shearL_unshearL G, by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply hom_ext
    · rw [Category.assoc, lift_fst, unshearO_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, unshearO_mu, Category.id_comp]⟩⟩
  rw [← shearL_snd]
  change Flat (shearL G ≫ pullback.snd G.hom G.hom)
  infer_instance


/-- If `U ≤ f ⁻¹ᵁ W`, then `U.ι ≫ f` lands in `W`. -/
lemma range_ι_comp_subset {Y Z : Scheme.{u}} {U : Y.Opens} {W : Z.Opens} (f : Y ⟶ Z)
    (h : U ≤ f ⁻¹ᵁ W) : Set.range (U.ι ≫ f) ⊆ Set.range W.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h x.2

omit [GrpObj G] in
/-- Two morphisms into `G × X` agree when both of their coordinates do. -/
lemma homExtGX {T : Scheme.{u}} {f g : T ⟶ (G ⊗ X).left}
    (h₁ : f ≫ (fst G X).left = g ≫ (fst G X).left)
    (h₂ : f ≫ (snd G X).left = g ≫ (snd G X).left) : f = g :=
  pullback.hom_ext h₁ h₂

/-- If `a b ∈ V` then `(a, a b) ∈ G × V`. -/
lemma shearL_mem_EV {V : G.left.Opens} {w : (G ⊗ G).left} (h : μ[G].left w ∈ V) :
    shearL G w ∈ EV G V := by
  show (snd G G).left (shearL G w) ∈ V
  rwa [← Scheme.Hom.comp_apply, shearL_snd]

/-- The second projection `G × X ⟶ X` is flat. -/
instance flat_snd_left : Flat (snd G X).left := by
  change Flat (pullback.snd G.hom X.hom)
  infer_instance

/-- **The translation argument.**  Let `π : V ⟶ X` be defined on an open `V` of a group scheme
`G` over a field, and let `F` be a rational map `G × X ⇢ X` (defined on the open `D`) such that
`F (a, π b) = π (a b)` on an open `D''` of `G × G`.  If `w ∈ D''` with `(w₁⁻¹, w₁ w₂) ∈ D''`,
if `id × π` is flat at `w` and injective on local rings at `(w₁, w₁ w₂)`, then `π` is flat at
`w₁ w₂`. -/
theorem flatAt_of_translation (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) (D'' : (G ⊗ G).left.Opens)
    (hD''V : D'' ≤ EV G V) (hD''μ : D'' ≤ μ[G].left ⁻¹ᵁ V)
    (hD''D : Set.range ((G ⊗ G).left.homOfLE hD''V ≫ onePi G X V π hπ) ⊆ Set.range D.ι)
    (hR : IsOpenImmersion.lift D.ι _ hD''D ≫ F =
      IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left) (range_ι_comp_subset _ hD''μ) ≫ π)
    (w : (G ⊗ G).left) (hw : w ∈ D'') (hw' : invFstL G (shearL G w) ∈ D'')
    (h1 : FlatAt (onePi G X V π hπ) ⟨w, hD''V hw⟩)
    (h2 : Function.Injective
      ((onePi G X V π hπ).stalkMap ⟨shearL G w, shearL_mem_EV G (hD''μ hw)⟩).hom) :
    FlatAt π ⟨μ[G].left w, hD''μ hw⟩ := by
  obtain ⟨d₁, hd₁⟩ : ∃ d₁ : D''.toScheme ⟶ D.toScheme,
      d₁ ≫ D.ι = (G ⊗ G).left.homOfLE hD''V ≫ onePi G X V π hπ ∧
      d₁ ≫ F = IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left)
        (range_ι_comp_subset _ hD''μ) ≫ π :=
    ⟨_, IsOpenImmersion.lift_fac _ _ _, hR⟩
  obtain ⟨d₂, hd₂, hR'⟩ : ∃ d₂ : D''.toScheme ⟶ V.toScheme, d₂ ≫ V.ι = D''.ι ≫ μ[G].left ∧
      d₁ ≫ F = d₂ ≫ π := ⟨_, IsOpenImmersion.lift_fac _ _ _, hd₁.2⟩
  replace hd₁ := hd₁.1
  clear hR
  let N₁ : (G ⊗ G).left.Opens := D'' ⊓ shearL G ⁻¹ᵁ (invFstL G ⁻¹ᵁ D'')
  let N₂ : (G ⊗ G).left.Opens := EV G V ⊓ invFstL G ⁻¹ᵁ D'' ⊓ unshearL G ⁻¹ᵁ D''
  have hN₁ : N₁ ≤ D'' := inf_le_left
  have hN₂E : N₂ ≤ EV G V := inf_le_left.trans inf_le_left
  have ho₁ := onePi_fst G X V π hπ
  have ho₂ := onePi_snd G X V π hπ
  have hσ₁ := sigma_fst G X D F hF
  have hσ₂ := sigma_snd G X D F hF
  have hσ'₁ := sigma'_fst G X D F hF
  have hσ'₂ := sigma'_snd G X D F hF
  have hq₂ : (snd G G).left.resLE V (EV G V) le_rfl ≫ V.ι = (EV G V).ι ≫ (snd G G).left :=
    Scheme.Hom.resLE_comp_ι _ _
  let k₀ : N₁.toScheme ⟶ D''.toScheme := (G ⊗ G).left.homOfLE hN₁
  let e₁ : N₁.toScheme ⟶ (EV G V).toScheme := (G ⊗ G).left.homOfLE (hN₁.trans hD''V)
  have he₁ : k₀ ≫ (G ⊗ G).left.homOfLE hD''V = e₁ := Scheme.homOfLE_homOfLE _ _ _
  obtain ⟨a₁, ha₁, hFa₁⟩ : ∃ a₁ : N₁.toScheme ⟶ D.toScheme,
      a₁ ≫ D.ι = e₁ ≫ onePi G X V π hπ ∧ a₁ ≫ F = k₀ ≫ d₂ ≫ π :=
    ⟨k₀ ≫ d₁, by rw [Category.assoc, hd₁, ← Category.assoc, he₁], by rw [Category.assoc, hR']⟩
  have hk₁r : Set.range (N₁.ι ≫ shearL G ≫ invFstL G) ⊆ Set.range D''.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2.2
  let k₁ : N₁.toScheme ⟶ D''.toScheme := IsOpenImmersion.lift D''.ι _ hk₁r
  have hk₁ : k₁ ≫ D''.ι = N₁.ι ≫ shearL G ≫ invFstL G := IsOpenImmersion.lift_fac _ _ _
  have hg₁r : Set.range (N₁.ι ≫ shearL G) ⊆ Set.range (EV G V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact shearL_mem_EV G (hD''μ (hN₁ x.2))
  let g₁ : N₁.toScheme ⟶ (EV G V).toScheme := IsOpenImmersion.lift (EV G V).ι _ hg₁r
  have hg₁ : g₁ ≫ (EV G V).ι = N₁.ι ≫ shearL G := IsOpenImmersion.lift_fac _ _ _
  have hk₀d₂ : (k₀ ≫ d₂) ≫ V.ι = N₁.ι ≫ μ[G].left := by
    rw [Category.assoc, hd₂, ← Category.assoc, Scheme.homOfLE_ι]
  have ha₁f : a₁ ≫ D.ι ≫ (fst G X).left = N₁.ι ≫ (fst G G).left := by
    rw [← Category.assoc, ha₁, Category.assoc, ho₁, ← Category.assoc, Scheme.homOfLE_ι]
  have hg₁f : g₁ ≫ onePi G X V π hπ ≫ (fst G X).left = N₁.ι ≫ (fst G G).left := by
    rw [ho₁, ← Category.assoc, hg₁, Category.assoc, shearL_fst]
  have hg₁s : g₁ ≫ (snd G G).left.resLE V (EV G V) le_rfl = k₀ ≫ d₂ := by
    rw [← cancel_mono V.ι, Category.assoc, hq₂, ← Category.assoc, hg₁, Category.assoc,
      shearL_snd, hk₀d₂]
  have K₄ : a₁ ≫ sigma G X D F hF = g₁ ≫ onePi G X V π hπ := by
    apply homExtGX
    · rw [Category.assoc, hσ₁, ha₁f, Category.assoc, hg₁f]
    · rw [Category.assoc, hσ₂, hFa₁, Category.assoc, ho₂, ← Category.assoc g₁, hg₁s,
        Category.assoc]
  obtain ⟨t₁, ht₁D, ht₁F⟩ : ∃ t₁ : N₁.toScheme ⟶ D.toScheme,
      t₁ ≫ D.ι = k₁ ≫ (G ⊗ G).left.homOfLE hD''V ≫ onePi G X V π hπ ∧
      t₁ ≫ F = k₁ ≫ d₂ ≫ π :=
    ⟨k₁ ≫ d₁, by rw [Category.assoc, hd₁], by rw [Category.assoc, hR']⟩
  have hk₁s : k₁ ≫ d₂ = e₁ ≫ (snd G G).left.resLE V (EV G V) le_rfl := by
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, hd₂, hq₂, reassoc_of% hk₁, shearL_invFstL_mu, e₁,
      Scheme.homOfLE_ι_assoc]
  have hk₁e : k₁ ≫ (G ⊗ G).left.homOfLE hD''V ≫ (EV G V).ι = N₁.ι ≫ shearL G ≫ invFstL G := by
    rw [Scheme.homOfLE_ι, hk₁]
  have hV₁ : (k₁ ≫ (G ⊗ G).left.homOfLE hD''V) ≫ (snd G G).left.resLE V (EV G V) le_rfl =
      k₀ ≫ d₂ := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hq₂, reassoc_of% hk₁e,
      invFstL_snd, shearL_snd, hk₀d₂]
  have ht₁ : (g₁ ≫ onePi G X V π hπ) ≫ invL G X = t₁ ≫ D.ι := by
    apply homExtGX
    · simp only [Category.assoc, invL_fst', onePi_fst_assoc, onePi_fst, reassoc_of% hg₁,
        shearL_fst_assoc, reassoc_of% ht₁D, reassoc_of% hk₁e]
    · simp only [Category.assoc, invL_snd, onePi_snd, reassoc_of% hg₁s, reassoc_of% ht₁D]
      rw [← Category.assoc k₁, ← Category.assoc (k₁ ≫ _), hV₁, Category.assoc]
  have hc₁r : Set.range (a₁ ≫ sigma G X D F hF) ⊆ Set.range (D' G X D).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (invL G X) ((a₁ ≫ sigma G X D F hF) x) ∈ D
    rw [← Scheme.Hom.comp_apply, K₄, ht₁, Scheme.Hom.comp_apply]
    exact (t₁ x).2
  let c₁ : N₁.toScheme ⟶ (D' G X D).toScheme := IsOpenImmersion.lift _ _ hc₁r
  have hc₁ : c₁ ≫ (D' G X D).ι = a₁ ≫ sigma G X D F hF := IsOpenImmersion.lift_fac _ _ _
  have hc₁t : c₁ ≫ (invL G X).resLE D (D' G X D) le_rfl = t₁ := by
    rw [← cancel_mono D.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hc₁, K₄,
      ht₁]
  have hc₁' : c₁ ≫ sigma' G X D F hF = a₁ ≫ D.ι := by
    apply homExtGX
    · rw [Category.assoc, sigma'_fst, ← Category.assoc, hc₁, Category.assoc, sigma_fst,
        Category.assoc]
    · rw [Category.assoc, sigma'_snd, ← Category.assoc, hc₁t, ht₁F, reassoc_of% hk₁s, ha₁,
        Category.assoc, onePi_snd]
  let e₂ : N₂.toScheme ⟶ (EV G V).toScheme := (G ⊗ G).left.homOfLE hN₂E
  have hk₂r : Set.range (N₂.ι ≫ invFstL G) ⊆ Set.range D''.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2.1.2
  let k₂ : N₂.toScheme ⟶ D''.toScheme := IsOpenImmersion.lift D''.ι _ hk₂r
  have hk₂ : k₂ ≫ D''.ι = N₂.ι ≫ invFstL G := IsOpenImmersion.lift_fac _ _ _
  have hk₃r : Set.range (N₂.ι ≫ unshearL G) ⊆ Set.range D''.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2.2
  let k₃ : N₂.toScheme ⟶ D''.toScheme := IsOpenImmersion.lift D''.ι _ hk₃r
  have hk₃ : k₃ ≫ D''.ι = N₂.ι ≫ unshearL G := IsOpenImmersion.lift_fac _ _ _
  have hk₂e : k₂ ≫ (G ⊗ G).left.homOfLE hD''V ≫ (EV G V).ι = N₂.ι ≫ invFstL G := by
    rw [Scheme.homOfLE_ι, hk₂]
  have hk₃e : k₃ ≫ (G ⊗ G).left.homOfLE hD''V ≫ (EV G V).ι = N₂.ι ≫ unshearL G := by
    rw [Scheme.homOfLE_ι, hk₃]
  have he₂ : e₂ ≫ (EV G V).ι = N₂.ι := Scheme.homOfLE_ι _ _
  have hV₂ : (k₂ ≫ (G ⊗ G).left.homOfLE hD''V) ≫ (snd G G).left.resLE V (EV G V) le_rfl =
      e₂ ≫ (snd G G).left.resLE V (EV G V) le_rfl := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hq₂, reassoc_of% hk₂e, invFstL_snd,
      Category.assoc, hq₂, reassoc_of% he₂]
  have hV₃ : k₂ ≫ d₂ = (k₃ ≫ (G ⊗ G).left.homOfLE hD''V) ≫
      (snd G G).left.resLE V (EV G V) le_rfl := by
    rw [← cancel_mono V.ι, Category.assoc, hd₂, reassoc_of% hk₂, Category.assoc, Category.assoc,
      hq₂, reassoc_of% hk₃e, unshearL_snd]
  have hV₄ : k₃ ≫ d₂ = e₂ ≫ (snd G G).left.resLE V (EV G V) le_rfl := by
    rw [← cancel_mono V.ι, Category.assoc, hd₂, reassoc_of% hk₃, unshearL_mu, Category.assoc,
      hq₂, reassoc_of% he₂]
  have H2a : (e₂ ≫ onePi G X V π hπ) ≫ invL G X = (k₂ ≫ d₁) ≫ D.ι := by
    apply homExtGX
    · simp only [Category.assoc, invL_fst', onePi_fst_assoc, onePi_fst, reassoc_of% hd₁,
        reassoc_of% hk₂e, reassoc_of% he₂]
    · simp only [Category.assoc, invL_snd, onePi_snd, reassoc_of% hd₁]
      rw [← Category.assoc k₂, ← Category.assoc (k₂ ≫ _), hV₂, Category.assoc]
  have ha₂r : Set.range (e₂ ≫ onePi G X V π hπ) ⊆ Set.range (D' G X D).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (invL G X) ((e₂ ≫ onePi G X V π hπ) x) ∈ D
    rw [← Scheme.Hom.comp_apply, H2a, Scheme.Hom.comp_apply]
    exact ((k₂ ≫ d₁) x).2
  let a₂ : N₂.toScheme ⟶ (D' G X D).toScheme := IsOpenImmersion.lift _ _ ha₂r
  have ha₂ : a₂ ≫ (D' G X D).ι = e₂ ≫ onePi G X V π hπ := IsOpenImmersion.lift_fac _ _ _
  have ha₂t : a₂ ≫ (invL G X).resLE D (D' G X D) le_rfl = k₂ ≫ d₁ := by
    rw [← cancel_mono D.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ha₂, H2a]
  obtain ⟨c₂, hc₂D, hc₂F⟩ : ∃ c₂ : N₂.toScheme ⟶ D.toScheme,
      c₂ ≫ D.ι = k₃ ≫ (G ⊗ G).left.homOfLE hD''V ≫ onePi G X V π hπ ∧
      c₂ ≫ F = k₃ ≫ d₂ ≫ π :=
    ⟨k₃ ≫ d₁, by rw [Category.assoc, hd₁], by rw [Category.assoc, hR']⟩
  have hc₂ : c₂ ≫ D.ι = a₂ ≫ sigma' G X D F hF := by
    apply homExtGX
    · simp only [Category.assoc, reassoc_of% hc₂D, onePi_fst, reassoc_of% hk₃e, sigma'_fst,
        reassoc_of% ha₂, unshearL_fst, reassoc_of% he₂]
    · simp only [Category.assoc, reassoc_of% hc₂D, onePi_snd, sigma'_snd, reassoc_of% ha₂t,
        hR', reassoc_of% hV₃]
  have hc₂' : c₂ ≫ sigma G X D F hF = a₂ ≫ (D' G X D).ι := by
    apply homExtGX
    · simp only [Category.assoc, sigma_fst, reassoc_of% hc₂D, onePi_fst, reassoc_of% hk₃e,
        reassoc_of% ha₂, unshearL_fst, reassoc_of% he₂]
    · simp only [Category.assoc, sigma_snd, hc₂F, reassoc_of% hV₄, reassoc_of% ha₂, onePi_snd]
  have hsw : shearL G w ∈ EV G V := shearL_mem_EV G (hD''μ hw)
  have hus : unshearL G (shearL G w) ∈ D'' := by
    rw [← Scheme.Hom.comp_apply, shearL_unshearL]; exact hw
  let p₁ : N₁.toScheme := ⟨w, hw, hw'⟩
  let p₂ : N₂.toScheme := ⟨shearL G w, ⟨hsw, hw'⟩, hus⟩
  have he₁p : e₁ p₁ = ⟨w, hD''V hw⟩ := Scheme.homOfLE_apply' _ _ _
  have he₂p : e₂ p₂ = ⟨shearL G w, hsw⟩ := Scheme.homOfLE_apply' _ _ _
  have hg₁p : g₁ p₁ = ⟨shearL G w, hsw⟩ := by
    apply Subtype.ext
    show (g₁ ≫ (EV G V).ι) p₁ = _
    rw [hg₁]; rfl
  have hz' : sigma G X D F hF (a₁ p₁) = (D' G X D).ι (a₂ p₂) := by
    rw [← Scheme.Hom.comp_apply, K₄, ← Scheme.Hom.comp_apply, ha₂, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, hg₁p, he₂p]
  have hinj₁ : Function.Injective (a₁.stalkMap p₁).hom := by
    rw [← injective_iff_of_comp_openImmersion a₁ D.ι, injective_stalkMap_congr ha₁,
      injective_iff_of_openImmersion_comp, he₁p]
    exact injective_of_flatAt _ _ h1
  have hinj₂ : Function.Injective (a₂.stalkMap p₂).hom := by
    rw [← injective_iff_of_comp_openImmersion a₂ (D' G X D).ι, injective_stalkMap_congr ha₂,
      injective_iff_of_openImmersion_comp, he₂p]
    exact h2
  have hiso : IsIso ((sigma G X D F hF).stalkMap (a₁ p₁)) :=
    isIso_stalkMap_of_local_inverse (sigma G X D F hF) (sigma' G X D F hF) (a₁ p₁) (a₂ p₂) hz'
      a₁ c₁ p₁ rfl hc₁ hc₁' hinj₁ a₂ c₂ p₂ rfl hc₂ hc₂' hinj₂
  have hfac : (k₀ ≫ d₂) ≫ π = a₁ ≫ sigma G X D F hF ≫ (snd G X).left := by
    rw [sigma_snd, hFa₁, Category.assoc]
  have hm : FlatAt (k₀ ≫ d₂) p₁ := by
    rw [← flatAt_iff_of_comp_openImmersion (k₀ ≫ d₂) V.ι, flatAt_congr hk₀d₂,
      flatAt_iff_of_openImmersion_comp]
    exact flatAt_of_flat _ _
  have he : FlatAt a₁ p₁ := by
    rw [← flatAt_iff_of_comp_openImmersion a₁ D.ι, flatAt_congr ha₁,
      flatAt_iff_of_openImmersion_comp, he₁p]
    exact h1
  have key := flatAt_of_factorization (k₀ ≫ d₂) π a₁ (sigma G X D F hF) (snd G X).left hfac p₁
    hm he (flatAt_of_flat _ _)
  have hpt : (k₀ ≫ d₂) p₁ = ⟨μ[G].left w, hD''μ hw⟩ := by
    apply Subtype.ext
    show ((k₀ ≫ d₂) ≫ V.ι) p₁ = _
    rw [hk₀d₂]; rfl
  rwa [hpt] at key


/-- `id × π` as a map of fibre products over the base. -/
noncomputable abbrev prodMap (V : G.left.Opens) (π : V.toScheme ⟶ X.left) :
    pullback G.hom (π ≫ X.hom) ⟶ (G ⊗ X).left :=
  pullback.map G.hom (π ≫ X.hom) G.hom X.hom (𝟙 _) π (𝟙 _) (by simp) (by simp)

/-- `G ×_k V ⟶ G ×_k G`. -/
noncomputable abbrev prodι (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) : pullback G.hom (π ≫ X.hom) ⟶ (G ⊗ G).left :=
  pullback.map G.hom (π ≫ X.hom) G.hom G.hom (𝟙 _) V.ι (𝟙 _) (by simp) (by simp [hπ])

omit [GrpObj G] in
/-- The range of `G ×_k V ⟶ G ×_k G` is the open `G × V`. -/
lemma range_prodι (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) :
    Set.range (prodι G X V π hπ) = Set.range (EV G V).ι := by
  rw [Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  have : Set.range (𝟙 G.left : G.left ⟶ G.left) = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [this, Set.preimage_univ, Set.univ_inter]
  rfl

/-- `G ×_k V ≅ G × V ⊆ G ×_k G`. -/
noncomputable def prodIso (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) : pullback G.hom (π ≫ X.hom) ≅ (EV G V).toScheme :=
  IsOpenImmersion.isoOfRangeEq _ _ (range_prodι G X V π hπ)

omit [GrpObj G] in
/-- The isomorphism `G ×_k V ≅ G × V` composed with the inclusion of `G × V` is the map
`G ×_k V ⟶ G ×_k G`. -/
lemma prodIso_hom_ι (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) :
    (prodIso G X V π hπ).hom ≫ (EV G V).ι = prodι G X V π hπ :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

omit [GrpObj G] in
/-- Under `G ×_k V ≅ G × V`, the second projection to `V` is the second projection of `G ×_k V`. -/
lemma prodIso_resLE (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) :
    (prodIso G X V π hπ).hom ≫ (snd G G).left.resLE V (EV G V) le_rfl =
      pullback.snd G.hom (π ≫ X.hom) := by
  rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
    reassoc_of% (prodIso_hom_ι G X V π hπ)]
  exact pullback.lift_snd _ _ _

omit [GrpObj G] in
/-- Under `G ×_k V ≅ G × V`, the map `id × π` is `prodMap`. -/
lemma prodIso_onePi (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) :
    (prodIso G X V π hπ).hom ≫ onePi G X V π hπ = prodMap G X V π := by
  have h := prodIso_hom_ι G X V π hπ
  apply pullback.hom_ext
  · show _ ≫ _ ≫ (fst G X).left = _
    rw [onePi_fst, reassoc_of% h]
    exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · show _ ≫ _ ≫ (snd G X).left = _
    rw [onePi_snd]
    rw [reassoc_of% (prodIso_resLE G X V π hπ)]
    exact (pullback.lift_snd _ _ _).symm

omit [GrpObj G] in
/-- The range of `id × π` is the preimage of the range of `π`. -/
lemma range_prodMap (V : G.left.Opens) (π : V.toScheme ⟶ X.left) :
    Set.range (prodMap G X V π) = pullback.snd G.hom X.hom ⁻¹' Set.range π := by
  rw [Scheme.Pullback.range_map]
  have : Set.range (𝟙 G.left : G.left ⟶ G.left) = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [this, Set.preimage_univ, Set.univ_inter]


/-- `(c, b) ↦ (c b⁻¹, b)`. -/
noncomputable abbrev divL : (G ⊗ G).left ⟶ (G ⊗ G).left :=
  (lift (fst G G * (snd G G)⁻¹) (snd G G)).left

/-- `(c b⁻¹) b = c`. -/
lemma divL_mu : divL G ≫ μ[G].left = (fst G G).left := by
  rw [← Over.comp_left, mu_eq_fst_mul_snd, MonObj.comp_mul, lift_fst, lift_snd,
    inv_mul_cancel_right]

/-- The second coordinate of `(c, b) ↦ (c b⁻¹, b)` is `b`. -/
lemma divL_snd : divL G ≫ (snd G G).left = (snd G G).left := by
  rw [← Over.comp_left, lift_snd]

/-- `(c, b) ↦ (c b⁻¹, b)` is a left inverse of `(a, b) ↦ (a b, b)`. -/
lemma mulSnd_divL : (lift μ[G] (snd G G)).left ≫ divL G = 𝟙 _ := by
  rw [← Over.comp_left, ← Over.id_left]
  congr 1
  apply hom_ext
  · rw [Category.assoc, lift_fst, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd,
      mu_eq_fst_mul_snd, mul_inv_cancel_right, Category.id_comp]
  · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]

/-- The first coordinate of `(a, b) ↦ (a b, b)` is `a b`. -/
lemma mulSnd_fst : (lift μ[G] (snd G G)).left ≫ (fst G G).left = μ[G].left := by
  rw [← Over.comp_left, lift_fst]

/-- Over an algebraically closed field, the fibre product of two integral schemes is integral. -/
lemma isIntegral_pullback_of_isAlgClosed [IsAlgClosed k] {A B : Scheme.{u}}
    (a : A ⟶ Spec (.of k)) (b : B ⟶ Spec (.of k)) [IsIntegral A] [IsIntegral B] :
    IsIntegral (Limits.pullback a b) := by
  have : GeometricallyIrreducible a :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k A a
  have : UniversallyOpen a := universallyOpen_of_field k a
  have : IrreducibleSpace ↑(Limits.pullback a b : Scheme.{u}) := inferInstance
  have : IsReduced (Limits.pullback a b : Scheme.{u}) := isReduced_pullback_over_perfectField a b
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **Flatness of a rational quotient map.**  Let `G` be an integral group scheme over an
algebraically closed field `k`, `π : V ⟶ X` a dominant morphism from an open of `G` to an
integral `k`-scheme, and `F` a rational map `G × X ⇢ X` with `F (a, π b) = π (a b)` on an open
`D''` of `G × G`.  Then `π` is flat at every point of `μ (D'' ∩ (shear ≫ invFst)⁻¹ D'')`. -/
theorem flatAt_of_rationalAction [IsAlgClosed k] [IsIntegral G.left] [IsIntegral X.left]
    (V : G.left.Opens) (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom)
    [IsDominant π] (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) (D'' : (G ⊗ G).left.Opens)
    (hD''V : D'' ≤ EV G V) (hD''μ : D'' ≤ μ[G].left ⁻¹ᵁ V)
    (hD''D : Set.range ((G ⊗ G).left.homOfLE hD''V ≫ onePi G X V π hπ) ⊆ Set.range D.ι)
    (hR : IsOpenImmersion.lift D.ι _ hD''D ≫ F =
      IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left) (range_ι_comp_subset _ hD''μ) ≫ π)
    (u : (G ⊗ G).left) (hu : u ∈ D'') (hu' : invFstL G (shearL G u) ∈ D'') :
    FlatAt π ⟨μ[G].left u, hD''μ hu⟩ := by
  have : Nonempty V := ⟨⟨μ[G].left u, hD''μ hu⟩⟩
  have : IsIntegral V.toScheme := inferInstance
  set v := μ[G].left u with hv
  obtain ⟨p, hp₁, hp₂, hpO⟩ := exists_fiberGenericPoint G.hom G.hom v
  set w := divL G p with hwdef
  have hwμ : μ[G].left w = v := by
    rw [hwdef, ← Scheme.Hom.comp_apply, divL_mu]; exact hp₁
  have hw₂ : (snd G G).left w = genericPoint G.left := by
    rw [hwdef, ← Scheme.Hom.comp_apply, divL_snd]; exact hp₂
  have hwO : w ∈ D'' ⊓ shearL G ⁻¹ᵁ (invFstL G ⁻¹ᵁ D'') := by
    have hmem : (lift μ[G] (snd G G)).left u ∈
        divL G ⁻¹ᵁ (D'' ⊓ shearL G ⁻¹ᵁ (invFstL G ⁻¹ᵁ D'')) := by
      show ((lift μ[G] (snd G G)).left ≫ divL G) u ∈
        (D'' ⊓ shearL G ⁻¹ᵁ (invFstL G ⁻¹ᵁ D'') : (G ⊗ G).left.Opens)
      rw [mulSnd_divL]; exact ⟨hu, hu'⟩
    have hfst : pullback.fst G.hom G.hom ((lift μ[G] (snd G G)).left u) = v := by
      show ((lift μ[G] (snd G G)).left ≫ (fst G G).left) u = v
      rw [mulSnd_fst]
    exact hpO (divL G ⁻¹ᵁ (D'' ⊓ shearL G ⁻¹ᵁ (invFstL G ⁻¹ᵁ D''))) ⟨_, hmem, hfst⟩
  have hwD'' : w ∈ D'' := hwO.1
  have hw' : invFstL G (shearL G w) ∈ D'' := hwO.2
  have hsw : shearL G w ∈ EV G V := shearL_mem_EV G (hD''μ hwD'')
  have hgenV : V.ι (genericPoint V) = genericPoint G.left := genericPoint_eq_of_isOpenImmersion V.ι
  have hπgen : π (genericPoint V) = genericPoint X.left :=
    map_genericPoint_of_isDominant π
  have hπflat : FlatAt π (genericPoint V) := flatAt_of_apply_eq_genericPoint π _ hπgen
  let e := prodIso G X V π hπ
  have hinv : ∀ y, e.hom (e.inv y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have h1 : FlatAt (onePi G X V π hπ) ⟨w, hD''V hwD''⟩ := by
    set y : (EV G V).toScheme := ⟨w, hD''V hwD''⟩ with hy
    rw [← hinv y, ← flatAt_iff_of_openImmersion_comp e.hom,
      flatAt_congr (prodIso_onePi G X V π hπ)]
    refine flat_stalkMap_pullbackMap_of_flat_stalkMap (A := k) G.hom (π ≫ X.hom) X.hom π rfl _ ?_
    have hs : pullback.snd G.hom (π ≫ X.hom) (e.inv y) = genericPoint V := by
      rw [← prodIso_resLE G X V π hπ, Scheme.Hom.comp_apply]
      show ((snd G G).left.resLE V (EV G V) le_rfl) (e.hom (e.inv y)) = _
      rw [hinv]
      apply V.ι.isOpenEmbedding.injective
      rwa [hgenV, ← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    rwa [hs]
  have : IsIntegral ↑(pullback G.hom (π ≫ X.hom) : Scheme.{u}) :=
    isIntegral_pullback_of_isAlgClosed _ _
  have : IsIntegral ↑(pullback G.hom X.hom : Scheme.{u}) :=
    isIntegral_pullback_of_isAlgClosed G.hom X.hom
  have : IsIntegral (G ⊗ X).left := this
  have : IrreducibleSpace ↑(pullback G.hom X.hom : Scheme.{u}) := inferInstance
  have : IsDominant (prodMap G X V π) := by
    refine ⟨?_⟩
    have hmem : genericPoint (G ⊗ X).left ∈ Set.range (prodMap G X V π) := by
      rw [range_prodMap]
      have : Surjective (pullback.snd G.hom X.hom) := inferInstance
      refine ⟨genericPoint V, ?_⟩
      rw [hπgen]
      exact (map_genericPoint_of_isDominant (pullback.snd G.hom X.hom)).symm
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
    have hg : closure {genericPoint (G ⊗ X).left} = (Set.univ : Set (G ⊗ X).left) :=
      (genericPoint_spec (G ⊗ X).left).def
    rw [← hg]
    exact closure_mono (Set.singleton_subset_iff.mpr hmem)
  have h2 : Function.Injective
      ((onePi G X V π hπ).stalkMap ⟨shearL G w, shearL_mem_EV G (hD''μ hwD'')⟩).hom := by
    set y : (EV G V).toScheme := ⟨shearL G w, shearL_mem_EV G (hD''μ hwD'')⟩ with hy
    rw [← hinv y, ← injective_iff_of_openImmersion_comp e.hom,
      injective_stalkMap_congr (prodIso_onePi G X V π hπ)]
    exact injective_stalkMap_of_isDominant _ _
  have key := flatAt_of_translation G X V π hπ D F hF D'' hD''V hD''μ hD''D hR w hwD'' hw' h1 h2
  have hpt : (⟨μ[G].left w, hD''μ hwD''⟩ : V) = ⟨v, hD''μ hu⟩ := Subtype.ext hwμ
  rwa [hpt] at key


/-- `(a, b) ↦ (a⁻¹, a b)` is an isomorphism of `G × G`. -/
lemma isIso_invFstL_shearL : IsIso (shearL G ≫ invFstL G) := by
  have hinv : IsIso (invFstL G) := ⟨⟨invFstL G, by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply hom_ext <;> simp [GrpObj.comp_inv], by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply hom_ext <;> simp [GrpObj.comp_inv]⟩⟩
  have hsh : IsIso (shearL G) := ⟨⟨unshearL G, shearL_unshearL G, by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply hom_ext
    · rw [Category.assoc, lift_fst, unshearO_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, unshearO_mu, Category.id_comp]⟩⟩
  infer_instance

/-- **Flatness of a rational quotient map on a nonempty open.**  In the situation of
`flatAt_of_rationalAction`, if `D''` is nonempty then `π` is flat on a nonempty open of `V`,
namely on `μ (D'' ∩ (shear ≫ invFst)⁻¹ D'')`. -/
theorem exists_open_flatAt_of_rationalAction [IsAlgClosed k] [IsIntegral G.left]
    [IsIntegral X.left]
    (V : G.left.Opens) (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom)
    [IsDominant π] (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) (D'' : (G ⊗ G).left.Opens)
    (hD''V : D'' ≤ EV G V) (hD''μ : D'' ≤ μ[G].left ⁻¹ᵁ V)
    (hD''D : Set.range ((G ⊗ G).left.homOfLE hD''V ≫ onePi G X V π hπ) ⊆ Set.range D.ι)
    (hR : IsOpenImmersion.lift D.ι _ hD''D ≫ F =
      IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left) (range_ι_comp_subset _ hD''μ) ≫ π)
    (hne : (D'' : Set (G ⊗ G).left).Nonempty) :
    ∃ V' : G.left.Opens, ∃ hV' : V' ≤ V, (V' : Set G.left).Nonempty ∧
      ∀ v (hv : v ∈ V'), FlatAt π ⟨v, hV' hv⟩ := by
  have : IsIso (shearL G ≫ invFstL G) := isIso_invFstL_shearL G
  have : IsIntegral (G ⊗ G).left := isIntegral_pullback_of_isAlgClosed G.hom G.hom
  let O : (G ⊗ G).left.Opens := D'' ⊓ (shearL G ≫ invFstL G) ⁻¹ᵁ D''
  let V' : G.left.Opens := ⟨μ[G].left '' O, isOpenMap_mul G _ O.2⟩
  have hV' : V' ≤ V := by
    rintro _ ⟨u, hu, rfl⟩
    exact hD''μ hu.1
  refine ⟨V', hV', ?_, ?_⟩
  · have hne' : ((shearL G ≫ invFstL G) ⁻¹ᵁ D'' : Set (G ⊗ G).left).Nonempty := by
      obtain ⟨d, hd⟩ := hne
      obtain ⟨u, hu⟩ := (ConcreteCategory.bijective_of_isIso
        (shearL G ≫ invFstL G).base).2 d
      exact ⟨u, show (shearL G ≫ invFstL G) u ∈ D'' by rw [show _ = _ from hu]; exact hd⟩
    obtain ⟨u, hu⟩ := nonempty_preirreducible_inter D''.2 ((shearL G ≫ invFstL G) ⁻¹ᵁ D'').2
      hne hne'
    exact ⟨_, u, hu, rfl⟩
  · rintro _ ⟨u, ⟨hu, hu'⟩, rfl⟩
    exact flatAt_of_rationalAction G X V π hπ D F hF D'' hD''V hD''μ hD''D hR u hu hu'


/-- The canonical domain `{w ∈ G × V : (id × π) w ∈ D, μ w ∈ V}`. -/
noncomputable abbrev canonicalDomain (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens) : (G ⊗ G).left.Opens :=
  (EV G V).ι ''ᵁ (onePi G X V π hπ ⁻¹ᵁ D) ⊓ μ[G].left ⁻¹ᵁ V

/-- The canonical domain is contained in `G × V`. -/
lemma canonicalDomain_le_EV (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens) :
    canonicalDomain G X V π hπ D ≤ EV G V := by
  rintro _ ⟨⟨y, -, rfl⟩, -⟩
  exact y.2

/-- The canonical domain is contained in `μ⁻¹ V`. -/
lemma canonicalDomain_le_mu (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens) :
    canonicalDomain G X V π hπ D ≤ μ[G].left ⁻¹ᵁ V := inf_le_right

/-- `id × π` maps the canonical domain into `D`. -/
lemma canonicalDomain_range (V : G.left.Opens) (π : V.toScheme ⟶ X.left)
    (hπ : π ≫ X.hom = V.ι ≫ G.hom) (D : (G ⊗ X).left.Opens) :
    Set.range ((G ⊗ G).left.homOfLE (canonicalDomain_le_EV G X V π hπ D) ≫
      onePi G X V π hπ) ⊆ Set.range D.ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨⟨y, hy, hyz⟩, -⟩ := z.2
  have : (G ⊗ G).left.homOfLE (canonicalDomain_le_EV G X V π hπ D) z = y :=
    Subtype.ext ((Scheme.homOfLE_apply _ z).trans hyz.symm)
  show onePi G X V π hπ ((G ⊗ G).left.homOfLE (canonicalDomain_le_EV G X V π hπ D) z) ∈ D
  rwa [this]

/-- **Flatness of a rational quotient map, from a local action datum.**  If `F (a, π b) = π (a b)`
holds on a nonempty open `U` of the canonical domain, then `π` is flat on a nonempty open of `V`.
-/
theorem exists_open_flatAt_of_localRationalAction [IsAlgClosed k] [IsIntegral G.left]
    [IsIntegral X.left] [IsSeparated X.hom]
    (V : G.left.Opens) (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom)
    [IsDominant π] (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
    (hF : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) (U : (G ⊗ G).left.Opens)
    (hU : U ≤ canonicalDomain G X V π hπ D) (hUne : (U : Set (G ⊗ G).left).Nonempty)
    (hRU : (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift D.ι _
        (canonicalDomain_range G X V π hπ D) ≫ F =
      (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift V.ι
        ((canonicalDomain G X V π hπ D).ι ≫ μ[G].left)
        (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) ≫ π) :
    ∃ V' : G.left.Opens, ∃ hV' : V' ≤ V, (V' : Set G.left).Nonempty ∧
      ∀ v (hv : v ∈ V'), FlatAt π ⟨v, hV' hv⟩ := by
  have : IsIntegral (G ⊗ G).left := isIntegral_pullback_of_isAlgClosed G.hom G.hom
  set D'' := canonicalDomain G X V π hπ D
  have : Nonempty U := ⟨⟨_, hUne.some_mem⟩⟩
  have : Nonempty D'' := ⟨⟨_, hU hUne.some_mem⟩⟩
  have : IsIntegral D''.toScheme := inferInstance
  have hdom : IsDominant ((G ⊗ G).left.homOfLE hU) :=
    Opens.isDominant_homOfLE (U.2.dense hUne) hU
  have hR : IsOpenImmersion.lift D.ι _ (canonicalDomain_range G X V π hπ D) ≫ F =
      IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left)
        (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) ≫ π := by
    refine ext_of_isDominant_of_isSeparated X.hom ?_ ((G ⊗ G).left.homOfLE hU) hRU
    rw [Category.assoc, Category.assoc, hF, hπ, IsOpenImmersion.lift_fac_assoc,
      IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc]
    have h1 : onePi G X V π hπ ≫ (G ⊗ X).hom = (EV G V).ι ≫ (G ⊗ G).hom := by
      show _ ≫ (fst G X).left ≫ G.hom = _
      rw [onePi_fst_assoc]
      rfl
    have h2 : μ[G].left ≫ G.hom = (G ⊗ G).hom := Over.w μ[G]
    rw [h1, h2, Scheme.homOfLE_ι_assoc]
  exact exists_open_flatAt_of_rationalAction G X V π hπ D F hF D''
    (canonicalDomain_le_EV G X V π hπ D) (canonicalDomain_le_mu G X V π hπ D)
    (canonicalDomain_range G X V π hπ D) hR ⟨_, hU hUne.some_mem⟩

end Translation

end AlgebraicGeometry.GenericQuotientFlat
