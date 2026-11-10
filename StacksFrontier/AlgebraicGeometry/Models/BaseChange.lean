module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

/-!
# Morphisms of models and base change of models

Let `R` be a discrete valuation ring with fraction field `K` and let `V` be a `K`-scheme. Section
0C2R of the Stacks project ([Stacks, Tag 0C2R]) introduces, besides the notion of a model of `V`
(`Stacks.Models.IsModel`), the following notions:

* a *morphism of models* `X ⟶ X'` for `V` is a morphism of schemes over `R` inducing the identity
  on `V`;
* a *proper model* is a model whose structure morphism is proper, and a *regular model* is a model
  whose total space is regular;
* for an extension of discrete valuation rings `R ⊆ R'` with induced extension `K'/K` of fraction
  fields, base change `X ↦ X ×_{Spec R} Spec R'` is a functor from models of `V` over `R` to
  models of `V' = V ×_{Spec K} Spec K'` over `R'`.

This file states these notions and proves the last assertion.

## Main definitions

* `Stacks.Models.IsModelHom` — a morphism of models.
* `Stacks.Models.IsProperModel`, `Stacks.Models.IsRegularModel` — proper and regular models.
* `Stacks.Models.baseChangeGenericFiberIso` — the identification of the generic fibre of the base
  change of a model with `V'`.
* `Stacks.Models.Model` — the category of models of `V`, and `Stacks.Models.Model.baseChange` the
  base change functor.

## Main results

* `Stacks.Models.IsModel.baseChange` — the base change of a model of `V` along an extension of
  discrete valuation rings is a model of `V'`.
* `Stacks.Models.IsModelHom.baseChange` — the base change of a morphism of models is a morphism
  of models.

## Implementation notes

The extension `K'/K` of fraction fields is given by an algebra structure together with the two
scalar towers `R → K → K'` and `R → R' → K'`; since `R → K'` is injective these determine
`K → K'`, so nothing beyond the extension `R ⊆ R'` is assumed.

A model carries its chosen identification of the generic fibre (`Stacks.Models.IsModel`), so a
morphism of models is required to intertwine the two identifications through the induced map of
generic fibres `Stacks.Models.genericFiberMapOfHomOver`.

## References

* [Stacks Project, Section 0C2R](https://stacks.math.columbia.edu/tag/0C2R)
* [Stacks Project, Tag 09E4](https://stacks.math.columbia.edu/tag/09E4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Models

universe u

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

add_to_stacks 0C2R "a model for V: a flat finite type morphism X ⟶ Spec R endowed with an \
  isomorphism V ⟶ X_K" Stacks.Models.IsModel

section Morphisms

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]

/-- The inclusion `Spec K ⟶ Spec R` of the generic point. -/
abbrev genericPointInclusion : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

variable {R K}

/-- The morphism of generic fibres `X_K ⟶ X'_K` induced by a morphism `φ : X ⟶ X'` over `R`. -/
abbrev genericFiberMapOfHomOver {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (p' : X' ⟶ Spec (CommRingCat.of R)) (φ : X ⟶ X') (h : φ ≫ p' = p) :
    pullback p (genericPointInclusion R K) ⟶ pullback p' (genericPointInclusion R K) :=
  pullback.map _ _ _ _ φ (𝟙 _) (𝟙 _) (by simp [h]) (by simp)

/-- **A morphism of models** `X ⟶ X'` for `V` (Section 0C2R): a morphism of schemes over `R`
which induces the identity on `V`, i.e. carries the identification `V ≅ X_K` to `V ≅ X'_K`. -/
@[stacks 0C2R "a morphism of models X ⟶ X' for V: a morphism of schemes over R which induces \
the identity on V"]
def IsModelHom {V X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (p' : X' ⟶ Spec (CommRingCat.of R))
    (e : V ≅ pullback p (genericPointInclusion R K))
    (e' : V ≅ pullback p' (genericPointInclusion R K)) (φ : X ⟶ X') : Prop :=
  ∃ h : φ ≫ p' = p, e.hom ≫ genericFiberMapOfHomOver p p' φ h = e'.hom

/-- The identity is a morphism of models. -/
theorem isModelHom_id {V X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (e : V ≅ pullback p (genericPointInclusion R K)) : IsModelHom p p e e (𝟙 X) :=
  ⟨Category.id_comp p, by
    have : genericFiberMapOfHomOver (K := K) p p (𝟙 X) (Category.id_comp p) = 𝟙 _ := by
      apply pullback.hom_ext <;> simp [genericFiberMapOfHomOver, pullback.map]
    rw [this, Category.comp_id]⟩

/-- A composite of morphisms of models is a morphism of models. -/
theorem IsModelHom.comp {V X X' X'' : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of R)}
    {p' : X' ⟶ Spec (CommRingCat.of R)} {p'' : X'' ⟶ Spec (CommRingCat.of R)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)}
    {e'' : V ≅ pullback p'' (genericPointInclusion R K)} {φ : X ⟶ X'} {ψ : X' ⟶ X''}
    (hφ : IsModelHom p p' e e' φ) (hψ : IsModelHom p' p'' e' e'' ψ) :
    IsModelHom p p'' e e'' (φ ≫ ψ) := by
  obtain ⟨h₁, h₂⟩ := hφ
  obtain ⟨h₃, h₄⟩ := hψ
  have h : (φ ≫ ψ) ≫ p'' = p := by rw [Category.assoc, h₃, h₁]
  refine ⟨h, ?_⟩
  have : genericFiberMapOfHomOver (K := K) p p'' (φ ≫ ψ) h =
      genericFiberMapOfHomOver p p' φ h₁ ≫ genericFiberMapOfHomOver p' p'' ψ h₃ := by
    apply pullback.hom_ext <;> simp [genericFiberMapOfHomOver, pullback.map]
  rw [this, ← Category.assoc, h₂, h₄]

/-- **A proper model** of `V` (Section 0C2R): a model whose structure morphism is proper. -/
@[stacks 0C2R "a proper model: a model whose structure morphism X ⟶ Spec R is proper"]
def IsProperModel [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {V X : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of K)) (p : X ⟶ Spec (CommRingCat.of R))
    (e : V ≅ pullback p (genericPointInclusion R K)) : Prop :=
  IsModel v p e ∧ IsProper p

/-- **A regular model** of `V` (Section 0C2R): a model whose total space is a regular scheme. -/
@[stacks 0C2R "a regular model: a model which is a regular scheme"]
def IsRegularModel [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {V X : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of K)) (p : X ⟶ Spec (CommRingCat.of R))
    (e : V ≅ pullback p (genericPointInclusion R K)) : Prop :=
  IsModel v p e ∧ IsRegular X

end Morphisms

section Category

variable (R : Type u) {K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The category of models** of a `K`-scheme `V` over `R` (Section 0C2R): a model of `V`,
bundled with its total space, structure morphism and identification of its generic fibre. -/
structure Model {V : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of K)) where
  /-- The total space of the model. -/
  X : Scheme.{u}
  /-- The structure morphism to `Spec R`. -/
  p : X ⟶ Spec (CommRingCat.of R)
  /-- The identification of `V` with the generic fibre. -/
  e : V ≅ pullback p (genericPointInclusion R K)
  /-- The triple is a model of `V`. -/
  isModel : IsModel v p e

variable {R} {V : Scheme.{u}} {v : V ⟶ Spec (CommRingCat.of K)}

/-- A morphism of models, bundled. -/
@[ext]
structure Model.Hom (M N : Model R v) where
  /-- The underlying morphism of schemes. -/
  hom : M.X ⟶ N.X
  /-- It is a morphism of models. -/
  isModelHom : IsModelHom M.p N.p M.e N.e hom

/-- Models of `V` and morphisms of models form a category. -/
instance : Category (Model R v) where
  Hom := Model.Hom
  id M := ⟨𝟙 M.X, isModelHom_id M.p M.e⟩
  comp f g := ⟨f.hom ≫ g.hom, f.isModelHom.comp g.isModelHom⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The underlying morphism of schemes of the identity of a model is the identity. -/
@[simp]
theorem Model.id_hom (M : Model R v) : Model.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The underlying morphism of schemes of a composite of morphisms of models is the composite of
the underlying morphisms. -/
@[simp]
theorem Model.comp_hom {M N P : Model R v} (f : M ⟶ N) (g : N ⟶ P) :
    Model.Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Two morphisms of models are equal if their underlying morphisms of schemes are equal. -/
@[ext]
theorem Model.hom_ext {M N : Model R v} {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Model.Hom.ext h

end Category

section BaseChange

variable {R K R' K' : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
  [IsFractionRing R' K'] [Algebra R R'] [IsDiscreteValuationRing.IsExtension R R']
  [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R']
  [IsDiscreteValuationRing R'] [IsFractionRing R' K'] [IsDiscreteValuationRing.IsExtension R R'] in
variable (R K R' K') in
/-- The square of spectra of the extension `R ⊆ R'` and of its fraction fields commutes. -/
theorem genericPointInclusion_comp_specMap :
    genericPointInclusion R' K' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ genericPointInclusion R K := by
  simp only [genericPointInclusion, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- The morphism `V' ⟶ X ×_{Spec R} Spec R'` from `V' = V ×_{Spec K} Spec K'` to the base change
of a model, through `V ≅ X_K ⟶ X` and `Spec K' ⟶ Spec R'`. -/
def baseChangeGenericFiberHom {V X : Scheme.{u}} {v : V ⟶ Spec (CommRingCat.of K)}
    (p : X ⟶ Spec (CommRingCat.of R)) (e : V ≅ pullback p (genericPointInclusion R K))
    (hv : e.hom ≫ pullback.snd p (genericPointInclusion R K) = v) :
    pullback v (Spec.map (CommRingCat.ofHom (algebraMap K K'))) ⟶
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  pullback.lift (pullback.fst _ _ ≫ e.hom ≫ pullback.fst p (genericPointInclusion R K))
    (pullback.snd _ _ ≫ genericPointInclusion R' K') (by
      rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hv,
        pullback.condition_assoc, Category.assoc, genericPointInclusion_comp_specMap R K R' K'])

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R']
  [IsDiscreteValuationRing R'] [IsFractionRing R' K'] [IsDiscreteValuationRing.IsExtension R R'] in
/-- `V' = V ×_{Spec K} Spec K'` is the generic fibre of the base change `X ×_{Spec R} Spec R'` of
a model of `V`. -/
theorem isPullback_baseChangeGenericFiberHom {V X : Scheme.{u}}
    {v : V ⟶ Spec (CommRingCat.of K)}
    (p : X ⟶ Spec (CommRingCat.of R)) (e : V ≅ pullback p (genericPointInclusion R K))
    (hv : e.hom ≫ pullback.snd p (genericPointInclusion R K) = v) :
    IsPullback (baseChangeGenericFiberHom (R' := R') (K' := K') p e hv)
      (pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      (genericPointInclusion R' K') := by
  have hV : IsPullback (e.hom ≫ pullback.fst p (genericPointInclusion R K)) v p
      (genericPointInclusion R K) :=
    (IsPullback.of_hasPullback p (genericPointInclusion R K)).of_iso e.symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp [← hv]) (by simp) (by simp)
  have houter := (IsPullback.of_hasPullback v
    (Spec.map (CommRingCat.ofHom (algebraMap K K')))).paste_horiz hV
  rw [← genericPointInclusion_comp_specMap R K R' K'] at houter
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  simpa [baseChangeGenericFiberHom] using houter

/-- **The generic fibre of the base change of a model.** For a morphism `p : X ⟶ Spec R` and an
identification `e : V ≅ X_K` over `K`, the generic fibre of `X ×_{Spec R} Spec R'` over `R'` is
identified with `V' = V ×_{Spec K} Spec K'`. -/
def baseChangeGenericFiberIso {V X : Scheme.{u}} {v : V ⟶ Spec (CommRingCat.of K)}
    (p : X ⟶ Spec (CommRingCat.of R)) (e : V ≅ pullback p (genericPointInclusion R K))
    (hv : e.hom ≫ pullback.snd p (genericPointInclusion R K) = v) :
    pullback v (Spec.map (CommRingCat.ofHom (algebraMap K K'))) ≅
      pullback (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
        (genericPointInclusion R' K') :=
  (isPullback_baseChangeGenericFiberHom p e hv).isoPullback

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R']
  [IsDiscreteValuationRing R'] [IsFractionRing R' K'] [IsDiscreteValuationRing.IsExtension R R'] in
/-- The identification `baseChangeGenericFiberIso` lies over `Spec K'`. -/
@[simp]
theorem baseChangeGenericFiberIso_hom_snd {V X : Scheme.{u}} {v : V ⟶ Spec (CommRingCat.of K)}
    (p : X ⟶ Spec (CommRingCat.of R)) (e : V ≅ pullback p (genericPointInclusion R K))
    (hv : e.hom ≫ pullback.snd p (genericPointInclusion R K) = v) :
    (baseChangeGenericFiberIso (R' := R') (K' := K') p e hv).hom ≫
        pullback.snd _ (genericPointInclusion R' K') =
      pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap K K'))) :=
  IsPullback.isoPullback_hom_snd _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R']
  [IsDiscreteValuationRing R'] [IsFractionRing R' K'] [IsDiscreteValuationRing.IsExtension R R'] in
/-- The identification `baseChangeGenericFiberIso` followed by the projection to the base change
is `baseChangeGenericFiberHom`. -/
@[simp]
theorem baseChangeGenericFiberIso_hom_fst {V X : Scheme.{u}} {v : V ⟶ Spec (CommRingCat.of K)}
    (p : X ⟶ Spec (CommRingCat.of R)) (e : V ≅ pullback p (genericPointInclusion R K))
    (hv : e.hom ≫ pullback.snd p (genericPointInclusion R K) = v) :
    (baseChangeGenericFiberIso (R' := R') (K' := K') p e hv).hom ≫
        pullback.fst _ (genericPointInclusion R' K') =
      baseChangeGenericFiberHom (R' := R') (K' := K') p e hv :=
  IsPullback.isoPullback_hom_fst _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R']
  [IsDiscreteValuationRing R'] [IsFractionRing R' K'] [IsDiscreteValuationRing.IsExtension R R'] in
/-- **Base change of a model** (Section 0C2R). Let `R ⊆ R'` be an extension of discrete
valuation rings with induced extension `K'/K` of fraction fields. If `X` is a model of the
`K`-scheme `V` over `R`, then `X ×_{Spec R} Spec R'` is a model of `V' = V ×_{Spec K} Spec K'`
over `R'`. -/
@[stacks 0C2R "base change X ↦ X ×_{Spec R} Spec R' along an extension of discrete valuation \
rings sends models of V over R to models of V' = V ×_{Spec K} Spec K' over R'"]
theorem IsModel.baseChange {V X : Scheme.{u}} {v : V ⟶ Spec (CommRingCat.of K)}
    {p : X ⟶ Spec (CommRingCat.of R)} {e : V ≅ pullback p (genericPointInclusion R K)}
    (h : IsModel v p e) :
    IsModel (pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      (baseChangeGenericFiberIso (R' := R') (K' := K') p e h.2.2.2) := by
  obtain ⟨hflat, hlft, hqc, hv⟩ := h
  refine ⟨?_, ?_, ?_, baseChangeGenericFiberIso_hom_snd p e hv⟩
  · have : Flat p := hflat
    infer_instance
  · have : LocallyOfFiniteType p := hlft
    infer_instance
  · have : QuasiCompact p := hqc
    infer_instance

/-- The base change `X ×_{Spec R} Spec R' ⟶ X' ×_{Spec R} Spec R'` of a morphism `φ : X ⟶ X'`
over `R`. -/
abbrev baseChangeMap {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    (p' : X' ⟶ Spec (CommRingCat.of R)) (φ : X ⟶ X') (h : φ ≫ p' = p) :
    pullback p (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ⟶
      pullback p' (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  pullback.map _ _ _ _ φ (𝟙 _) (𝟙 _) (by simp [h]) (by simp)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain R']
  [IsDiscreteValuationRing R'] [IsFractionRing R' K'] [IsDiscreteValuationRing.IsExtension R R'] in
/-- **Base change of a morphism of models** (Section 0C2R): the base change of a morphism of
models of `V` over `R` is a morphism of models of `V'` over `R'`. -/
@[stacks 0C2R "base change sends morphisms of models of V over R to morphisms of models of V' \
over R'"]
theorem IsModelHom.baseChange {V X X' : Scheme.{u}} {v : V ⟶ Spec (CommRingCat.of K)}
    {p : X ⟶ Spec (CommRingCat.of R)} {p' : X' ⟶ Spec (CommRingCat.of R)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)}
    (hv : e.hom ≫ pullback.snd p (genericPointInclusion R K) = v)
    (hv' : e'.hom ≫ pullback.snd p' (genericPointInclusion R K) = v) {φ : X ⟶ X'}
    (hφ : IsModelHom p p' e e' φ) :
    IsModelHom (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      (pullback.snd p' (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      (baseChangeGenericFiberIso (R' := R') (K' := K') p e hv)
      (baseChangeGenericFiberIso (R' := R') (K' := K') p' e' hv')
      (baseChangeMap (R' := R') p p' φ hφ.1) := by
  obtain ⟨h, he⟩ := hφ
  have he' : e.hom ≫ pullback.fst p (genericPointInclusion R K) ≫ φ =
      e'.hom ≫ pullback.fst p' (genericPointInclusion R K) := by
    rw [← he]; simp [genericFiberMapOfHomOver, pullback.map]
  refine ⟨by simp [baseChangeMap, pullback.map], ?_⟩
  apply pullback.hom_ext
  · simp only [genericFiberMapOfHomOver, baseChangeMap, pullback.map, Category.assoc,
      pullback.lift_fst,
      reassoc_of% baseChangeGenericFiberIso_hom_fst, baseChangeGenericFiberIso_hom_fst]
    apply pullback.hom_ext
    · simp [baseChangeGenericFiberHom, he']
    · simp [baseChangeGenericFiberHom]
  · simp [genericFiberMapOfHomOver, pullback.map]

/-- **The base change functor** (Section 0C2R): for an extension of discrete valuation rings
`R ⊆ R'` with induced extension `K'/K` of fraction fields, `X ↦ X ×_{Spec R} Spec R'` is a
functor from models of `V` over `R` to models of `V' = V ×_{Spec K} Spec K'` over `R'`. -/
@[stacks 0C2R "the functor from models for V over R to models for V' over R' sending X to \
X ×_{Spec R} Spec R'"]
def Model.baseChange (V : Scheme.{u}) (v : V ⟶ Spec (CommRingCat.of K)) :
    Model R v ⥤ Model R' (pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap K K')))) where
  obj M :=
    { X := pullback M.p (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      p := pullback.snd M.p (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      e := baseChangeGenericFiberIso (R' := R') (K' := K') M.p M.e M.isModel.2.2.2
      isModel := M.isModel.baseChange }
  map {M N} f :=
    ⟨baseChangeMap (R' := R') M.p N.p f.hom f.isModelHom.1,
      IsModelHom.baseChange M.isModel.2.2.2 N.isModel.2.2.2 f.isModelHom⟩
  map_id M := by
    ext : 1
    apply pullback.hom_ext <;> simp [baseChangeMap, pullback.map]
  map_comp f g := by
    ext : 1
    apply pullback.hom_ext <;> simp [baseChangeMap, pullback.map]

end BaseChange

end Stacks.Models

end
