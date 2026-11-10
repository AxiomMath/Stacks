module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Homology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The two-step filtration attached to a short exact sequence

Let `0 → X₁ → X₂ → X₃ → 0` be a short exact sequence in an abelian category. The middle term
carries the filtration `F^q X₂ = X₂` for `q ≤ 0`, `F^1 X₂ = X₁` and `F^q X₂ = 0` for `q ≥ 2`, whose
graded pieces are `gr^1 = X₁`, `gr^0 = X₃` and zero otherwise. The same construction, degreewise,
gives a filtered complex attached to a short exact sequence of cochain complexes.

## Main definitions

* `CategoryTheory.FilteredObject.twoStep`: the filtered object `(X₂, F)` attached to a short
  complex whose first map is a monomorphism.
* `CategoryTheory.FilteredObject.twoStepMap`: its functoriality in morphisms of short complexes.
* `CategoryTheory.FilteredObject.twoStepGrOneIso`: `gr^1 ≅ X₁`, natural in the short complex.
* `CategoryTheory.FilteredObject.twoStepGrZeroIso`: `gr^0 ≅ X₃` for a short exact sequence,
  natural in it.
* `CochainComplex.twoStepComplex`: the degreewise two-step filtered complex of a short complex of
  cochain complexes whose first map is degreewise a monomorphism.

## Main results

* `CategoryTheory.FilteredObject.twoStepMap_twoStepUnmap`: every morphism of two-step filtered
  objects, the source coming from a short exact sequence, comes from a morphism of short
  complexes.
* `CochainComplex.isZero_twoStepComplex_grP`: `gr^p` of the two-step filtered complex vanishes
  for `p ∉ {0, 1}`.
* `CochainComplex.twoStepComplexMap_twoStepComplexUnmap`: every morphism of two-step filtered
  complexes, the source coming from a short exact sequence, comes from a morphism of short
  complexes.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.FilteredObject

variable {C : Type*} [Category* C] [Abelian C]

section TwoStep

variable (S : ShortComplex C) [Mono S.f]

/-- The steps of the two-step filtration of `S.X₂`: the whole object in indices `q ≤ 0`, the
image of `S.f` in index `1`, and zero in indices `q ≥ 2`. -/
def twoStepSubobject (q : ℤ) : Subobject S.X₂ :=
  if q ≤ 0 then ⊤ else if q ≤ 1 then Subobject.mk S.f else ⊥

/-- The filtration step in an index `q ≤ 0` is the whole object. -/
lemma twoStepSubobject_of_le_zero {q : ℤ} (h : q ≤ 0) : twoStepSubobject S q = ⊤ :=
  ite_eq_left h

/-- The filtration step in index `1` is the image of `S.f`. -/
lemma twoStepSubobject_one : twoStepSubobject S 1 = Subobject.mk S.f := by
  simp [twoStepSubobject]

/-- The filtration step in an index `q ≥ 2` is zero. -/
lemma twoStepSubobject_of_two_le {q : ℤ} (h : 2 ≤ q) : twoStepSubobject S q = ⊥ := by
  simp only [twoStepSubobject]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The steps of the two-step filtration decrease with the index. -/
lemma antitone_twoStepSubobject : Antitone (twoStepSubobject S) := by
  intro a b hab
  rcases le_or_gt b 0 with hb | hb
  · rw [twoStepSubobject_of_le_zero S hb, twoStepSubobject_of_le_zero S (hab.trans hb)]
  rcases le_or_gt 2 b with hb2 | hb2
  · rw [twoStepSubobject_of_two_le S hb2]
    exact bot_le
  obtain rfl : b = 1 := by omega
  rcases le_or_gt a 0 with ha | ha
  · rw [twoStepSubobject_of_le_zero S ha]
    exact le_top
  · obtain rfl : a = 1 := by omega
    exact le_rfl

/-- **The two-step filtration** of the middle term of a short complex `S` with `S.f` a
monomorphism: `F^q = S.X₂` for `q ≤ 0`, `F^1 = S.X₁` and `F^q = 0` for `q ≥ 2`. -/
abbrev twoStep : FilteredObject C ℤᵒᵖ :=
  ⟨S.X₂, Filtration.ofAntitone (twoStepSubobject S) (antitone_twoStepSubobject S)⟩

/-- The underlying object of the two-step filtration is `S.X₂`. -/
lemma twoStep_X : (twoStep S).X = S.X₂ := rfl

/-- The inclusion of the `q`-th step of the two-step filtration is the arrow of
`twoStepSubobject S q`. -/
lemma twoStep_ι_app (q : ℤ) :
    (twoStep S).filtration.ι.app (op q) = (twoStepSubobject S q).arrow := rfl

/-- The inclusion of the step `F^0` into `S.X₂` is an isomorphism. -/
instance isIso_twoStep_ι_app_zero : IsIso ((twoStep S).filtration.ι.app (op 0)) := by
  rw [twoStep_ι_app]
  exact (Subobject.isIso_arrow_iff_eq_top _).2 (twoStepSubobject_of_le_zero S le_rfl)

/-- The step `F^q` of the two-step filtration is zero for `q ≥ 2`. -/
lemma isZero_twoStep_obj_of_two_le {q : ℤ} (h : 2 ≤ q) :
    IsZero ((twoStep S).filtration.obj (op q)) := by
  change IsZero ((twoStepSubobject S q : Subobject S.X₂) : C)
  rw [twoStepSubobject_of_two_le S h]
  exact (Limits.isZero_zero C).of_iso Subobject.botCoeIsoZero

/-- The step `F^1 = S.X₁`, as an isomorphism. -/
def twoStepObjOneIso : (twoStep S).filtration.obj (op 1) ≅ S.X₁ :=
  Subobject.isoOfEq _ _ (twoStepSubobject_one S) ≪≫ Subobject.underlyingIso S.f

/-- Composing `F^1 ≅ S.X₁` with `S.f` gives the inclusion of `F^1` into `S.X₂`. -/
@[reassoc (attr := simp)]
lemma twoStepObjOneIso_hom_comp_f :
    (twoStepObjOneIso S).hom ≫ S.f = (twoStepSubobject S 1).arrow := by
  simp [twoStepObjOneIso]

/-- `gr^p` of the two-step filtration vanishes for `p ≥ 2`. -/
lemma isZero_gr_twoStep_of_two_le {p : ℤ} (h : 2 ≤ p) : IsZero ((gr p).obj (twoStep S)) :=
  isZero_gr_obj_of_isZero _ h (isZero_twoStep_obj_of_two_le S le_rfl)

/-- `gr^p` of the two-step filtration vanishes for `p < 0`. -/
lemma isZero_gr_twoStep_of_neg {p : ℤ} (h : p < 0) : IsZero ((gr p).obj (twoStep S)) :=
  isZero_gr_obj_of_isIso_ι_app _ (n := 0) (by omega) inferInstance

/-- The inclusion `F^2 ⟶ F^1` of the two-step filtration is zero. -/
lemma twoStep_step_one_eq_zero :
    (twoStep S).filtration.step (succHom 1) = 0 :=
  (isZero_twoStep_obj_of_two_le S (le_refl 2)).eq_of_src _ _

/-- **`gr^1` of the two-step filtration is `S.X₁`.** -/
def twoStepGrOneIso : (gr 1).obj (twoStep S) ≅ S.X₁ :=
  cokernelIsoOfEq (twoStep_step_one_eq_zero S) ≪≫ cokernelZeroIsoTarget ≪≫ twoStepObjOneIso S

/-- The projection `F^1 ⟶ gr^1` followed by `gr^1 ≅ S.X₁` is `F^1 ≅ S.X₁`. -/
@[reassoc (attr := simp)]
lemma grMapπ_twoStepGrOneIso_hom :
    grMapπ (succHom 1) (twoStep S) ≫ (twoStepGrOneIso S).hom = (twoStepObjOneIso S).hom := by
  simp [twoStepGrOneIso, grMapπ, cokernelZeroIsoTarget]

end TwoStep

section Map

variable {S S' : ShortComplex C} [Mono S.f] [Mono S'.f] (φ : S ⟶ S')

/-- The image under `φ.τ₂` of each filtration step of `S.X₂` lies in the corresponding step of
`S'.X₂`. -/
lemma twoStepSubobject_factors (q : ℤ) :
    (twoStepSubobject S' q).Factors ((twoStepSubobject S q).arrow ≫ φ.τ₂) := by
  rcases le_or_gt q 0 with h | h
  · rw [twoStepSubobject_of_le_zero S' h]
    exact Subobject.top_factors _
  rcases le_or_gt 2 q with h2 | h2
  · rw [(isZero_twoStep_obj_of_two_le S h2).eq_of_src
      ((twoStepSubobject S q).arrow ≫ φ.τ₂) 0]
    exact Subobject.factors_zero
  obtain rfl : q = 1 := by omega
  rw [twoStepSubobject_one S', Subobject.mk_factors_iff]
  refine ⟨(twoStepObjOneIso S).hom ≫ φ.τ₁, ?_⟩
  change ((twoStepObjOneIso S).hom ≫ φ.τ₁) ≫ S'.f = _
  rw [Category.assoc, φ.comm₁₂, ← Category.assoc, twoStepObjOneIso_hom_comp_f]

/-- **Functoriality of the two-step filtration** in morphisms of short complexes: the
underlying morphism is `φ.τ₂`. -/
def twoStepMap : twoStep S ⟶ twoStep S' :=
  homMk φ.τ₂ (fun q => (twoStepSubobject S' q.unop).factorThru _
    (twoStepSubobject_factors φ q.unop))
    (fun q => Subobject.factorThru_arrow _ _ (twoStepSubobject_factors φ q.unop))

/-- The underlying morphism of `twoStepMap φ` is `φ.τ₂`. -/
@[simp]
lemma twoStepMap_hom : (twoStepMap φ).hom = φ.τ₂ := rfl

/-- The component of `twoStepMap φ` on the `q`-th step is the restriction of `φ.τ₂`. -/
@[reassoc]
lemma twoStepMap_natTrans_app_arrow (q : ℤ) :
    ((twoStepMap φ).natTrans.app (op q) : (twoStepSubobject S q : C) ⟶
        (twoStepSubobject S' q : C)) ≫ (twoStepSubobject S' q).arrow =
      (twoStepSubobject S q).arrow ≫ φ.τ₂ :=
  Subobject.factorThru_arrow _ _ (twoStepSubobject_factors φ q)

/-- `twoStepMap` sends the identity to the identity. -/
@[simp]
lemma twoStepMap_id : twoStepMap (𝟙 S) = 𝟙 (twoStep S) := hom_ext rfl

/-- `twoStepMap` sends a composite to the composite. -/
@[simp]
lemma twoStepMap_comp {S'' : ShortComplex C} [Mono S''.f] (ψ : S' ⟶ S'') :
    twoStepMap (φ ≫ ψ) = twoStepMap φ ≫ twoStepMap ψ := hom_ext rfl

/-- Under `F^1 ≅ S.X₁`, the component of `twoStepMap φ` on `F^1` is `φ.τ₁`. -/
@[reassoc]
lemma twoStepMap_natTrans_app_one :
    (twoStepMap φ).natTrans.app (op 1) ≫ (twoStepObjOneIso S').hom =
      (twoStepObjOneIso S).hom ≫ φ.τ₁ := by
  rw [← cancel_mono S'.f, Category.assoc, twoStepObjOneIso_hom_comp_f,
    twoStepMap_natTrans_app_arrow, Category.assoc, φ.comm₁₂, ← Category.assoc,
    twoStepObjOneIso_hom_comp_f]

/-- Naturality of `gr^1 ≅ S.X₁`. -/
@[reassoc]
lemma gr_one_map_twoStepMap :
    (gr 1).map (twoStepMap φ) ≫ (twoStepGrOneIso S').hom =
      (twoStepGrOneIso S).hom ≫ φ.τ₁ := by
  apply grMap_hom_ext
  rw [grMapπ_map_assoc, grMapπ_twoStepGrOneIso_hom, grMapπ_twoStepGrOneIso_hom_assoc,
    twoStepMap_natTrans_app_one]

end Map

section GrZero

variable (S : ShortComplex C) [Mono S.f] (hS : S.ShortExact)

/-- The inclusion `F^1 ⟶ F^0` followed by the inclusion of `F^0` into `S.X₂` is the inclusion
of `F^1`. -/
lemma twoStep_step_zero_comp_arrow :
    ((twoStep S).filtration.step (succHom 0) : (twoStepSubobject S 1 : C) ⟶
        (twoStepSubobject S 0 : C)) ≫ (twoStepSubobject S 0).arrow =
      (twoStepSubobject S 1).arrow :=
  Filtration.step_comp_ι_app _ _

/-- The inclusion `F^0 ⟶ S.X₂`, an isomorphism. -/
def twoStepObjZeroIso : (twoStep S).filtration.obj (op 0) ≅ S.X₂ :=
  @asIso _ _ _ _ (twoStepSubobject S 0).arrow
    ((Subobject.isIso_arrow_iff_eq_top _).2 (twoStepSubobject_of_le_zero S le_rfl))

/-- The isomorphism `F^0 ≅ S.X₂` is the inclusion of `F^0`. -/
@[simp]
lemma twoStepObjZeroIso_hom : (twoStepObjZeroIso S).hom = (twoStepSubobject S 0).arrow := rfl

/-- **`gr^0` of the two-step filtration of a short exact sequence is `S.X₃`.** -/
def twoStepGrZeroIso : (gr 0).obj (twoStep S) ≅ S.X₃ :=
  cokernel.mapIso ((twoStep S).filtration.step (succHom 0)) S.f (twoStepObjOneIso S)
      (twoStepObjZeroIso S)
      (by rw [twoStepObjZeroIso_hom, twoStep_step_zero_comp_arrow,
        twoStepObjOneIso_hom_comp_f]) ≪≫
    (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel

/-- The projection `F^0 ⟶ gr^0` followed by `gr^0 ≅ S.X₃` is the inclusion of `F^0` followed
by `S.g`. -/
@[reassoc (attr := simp)]
lemma grMapπ_twoStepGrZeroIso_hom :
    grMapπ (succHom 0) (twoStep S) ≫ (twoStepGrZeroIso S hS).hom =
      (twoStepSubobject S 0).arrow ≫ S.g := by
  simp only [twoStepGrZeroIso, Iso.trans_hom, cokernel.mapIso_hom, grMapπ]
  rw [cokernel.π_desc_assoc, Category.assoc, twoStepObjZeroIso_hom]
  congr 1
  exact (cokernelIsCokernel S.f).comp_coconePointUniqueUpToIso_hom hS.gIsCokernel
    WalkingParallelPair.one

/-- Naturality of `gr^0 ≅ S.X₃`. -/
@[reassoc]
lemma gr_zero_map_twoStepMap {S' : ShortComplex C} [Mono S'.f] (hS' : S'.ShortExact)
    (φ : S ⟶ S') :
    (gr 0).map (twoStepMap φ) ≫ (twoStepGrZeroIso S' hS').hom =
      (twoStepGrZeroIso S hS).hom ≫ φ.τ₃ := by
  apply grMap_hom_ext
  rw [grMapπ_map_assoc, grMapπ_twoStepGrZeroIso_hom, grMapπ_twoStepGrZeroIso_hom_assoc,
    twoStepMap_natTrans_app_arrow_assoc, φ.comm₂₃]

end GrZero

section Lift

variable {S S' : ShortComplex C} [Mono S.f] [Mono S'.f] (hS : S.ShortExact)
  (m : twoStep S ⟶ twoStep S')

/-- The first component of the morphism of short complexes underlying a morphism of two-step
filtered objects: its restriction to `F^1`. -/
def twoStepUnmapτ₁ : S.X₁ ⟶ S'.X₁ :=
  (twoStepObjOneIso S).inv ≫ m.natTrans.app (op 1) ≫ (twoStepObjOneIso S').hom

/-- The restriction `twoStepUnmapτ₁ m` is compatible with `S.f`, `S'.f` and the underlying
morphism of `m`. -/
lemma twoStepUnmapτ₁_comp_f : twoStepUnmapτ₁ m ≫ S'.f = S.f ≫ m.hom := by
  rw [twoStepUnmapτ₁, Category.assoc, Category.assoc, twoStepObjOneIso_hom_comp_f]
  have h := m.comm (op 1)
  rw [twoStep_ι_app, twoStep_ι_app] at h
  rw [h, ← Category.assoc, ← twoStepObjOneIso_hom_comp_f S, Iso.inv_hom_id_assoc]

/-- The morphism of short complexes underlying a morphism of two-step filtered objects, the source
being short exact: the restriction to `F^1`, the underlying morphism, and the induced morphism
of cokernels. -/
def twoStepUnmap : S ⟶ S' where
  τ₁ := twoStepUnmapτ₁ m
  τ₂ := m.hom
  τ₃ := haveI := hS.epi_g
    hS.exact.desc (m.hom ≫ S'.g) (by
      rw [← Category.assoc, ← twoStepUnmapτ₁_comp_f, Category.assoc, S'.zero, comp_zero])
  comm₁₂ := twoStepUnmapτ₁_comp_f m
  comm₂₃ := by
    have := hS.epi_g
    exact (hS.exact.g_desc _ _).symm

/-- The middle component of `twoStepUnmap hS m` is the underlying morphism of `m`. -/
@[simp]
lemma twoStepUnmap_τ₂ : (twoStepUnmap hS m).τ₂ = m.hom := rfl

/-- **Every morphism of two-step filtered objects comes from a morphism of short complexes.** -/
lemma twoStepMap_twoStepUnmap : twoStepMap (twoStepUnmap hS m) = m := hom_ext rfl

end Lift

/-- The two-step filtration is finite. -/
lemma twoStep_isFinite (S : ShortComplex C) [Mono S.f] : (twoStep S).filtration.IsFinite :=
  .of_exists ⟨0, inferInstance⟩ ⟨2, isZero_twoStep_obj_of_two_le S le_rfl⟩

end CategoryTheory.FilteredObject

namespace CochainComplex

open CategoryTheory.FilteredObject

variable {C : Type*} [Category* C] [Abelian C]

section TwoStepComplex

variable (S : ShortComplex (CochainComplex C ℤ)) [∀ n, Mono (S.f.f n)]

/-- The short complex of degree `n` terms of a short complex of cochain complexes. -/
abbrev degreeShortComplex (n : ℤ) : ShortComplex C :=
  S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)

/-- The first map of the degree `n` short complex is a monomorphism. -/
instance (n : ℤ) : Mono (degreeShortComplex S n).f := inferInstanceAs (Mono (S.f.f n))

/-- The morphism of degree `n` and degree `m` short complexes given by the differentials. -/
@[simps]
def degreeShortComplexD (n m : ℤ) : degreeShortComplex S n ⟶ degreeShortComplex S m where
  τ₁ := S.X₁.d n m
  τ₂ := S.X₂.d n m
  τ₃ := S.X₃.d n m
  comm₁₂ := (S.f.comm n m).symm
  comm₂₃ := (S.g.comm n m).symm

variable {S} in
/-- The morphism of degree `n` short complexes induced by a morphism of short complexes of
cochain complexes. -/
@[simps]
def degreeShortComplexMap {S' : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ S') (n : ℤ) :
    degreeShortComplex S n ⟶ degreeShortComplex S' n where
  τ₁ := φ.τ₁.f n
  τ₂ := φ.τ₂.f n
  τ₃ := φ.τ₃.f n
  comm₁₂ := HomologicalComplex.congr_hom φ.comm₁₂ n
  comm₂₃ := HomologicalComplex.congr_hom φ.comm₂₃ n

/-- The degree `n` finite filtered object of the two-step filtration. -/
def twoStepX (n : ℤ) : FiniteFilteredObject C :=
  ⟨twoStep (degreeShortComplex S n), twoStep_isFinite _⟩

/-- **The two-step filtered complex** of a short complex of cochain complexes whose first map is
degreewise a monomorphism: in each degree the filtration `F^0 = X₂ ⊇ F^1 = X₁ ⊇ F^2 = 0`. -/
def twoStepComplex : CochainComplex (FiniteFilteredObject C) ℤ where
  X n := twoStepX S n
  d n m := ObjectProperty.homMk (twoStepMap (degreeShortComplexD S n m))
  shape n m h := by
    ext1
    refine hom_ext ?_
    exact S.X₂.shape n m h
  d_comp_d' n m l _ _ := by
    ext1
    refine hom_ext ?_
    exact S.X₂.d_comp_d n m l

variable {S} in
/-- The morphism of two-step filtered complexes induced by a morphism of short complexes. -/
def twoStepComplexMap {S' : ShortComplex (CochainComplex C ℤ)} [∀ n, Mono (S'.f.f n)]
    (φ : S ⟶ S') : twoStepComplex S ⟶ twoStepComplex S' where
  f n := ObjectProperty.homMk (twoStepMap (degreeShortComplexMap φ n))
  comm' n m _ := by
    ext1
    refine hom_ext ?_
    exact φ.τ₂.comm n m

/-- `twoStepComplexMap` sends a composite to the composite. -/
@[simp]
lemma twoStepComplexMap_comp {S' S'' : ShortComplex (CochainComplex C ℤ)} [∀ n, Mono (S'.f.f n)]
    [∀ n, Mono (S''.f.f n)] (φ : S ⟶ S') (ψ : S' ⟶ S'') :
    twoStepComplexMap (φ ≫ ψ) = twoStepComplexMap φ ≫ twoStepComplexMap ψ := by
  ext n : 2
  exact hom_ext rfl

/-- The underlying complex of the two-step filtered complex is `S.X₂`. -/
def twoStepComplexForgetIso :
    (FiniteFilteredObject.forget.mapHomologicalComplex _).obj (twoStepComplex S) ≅ S.X₂ :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun n m _ =>
    (Category.id_comp _).trans ((twoStepMap_hom (degreeShortComplexD S n m)).symm.trans
      (Category.comp_id _).symm))

/-- Naturality of the identification of the underlying complex of the two-step filtered complex
with `S.X₂`. -/
lemma twoStepComplexForgetIso_hom_naturality {S' : ShortComplex (CochainComplex C ℤ)}
    [∀ n, Mono (S'.f.f n)] (φ : S ⟶ S') :
    (FiniteFilteredObject.forget.mapHomologicalComplex _).map (twoStepComplexMap φ) ≫
        (twoStepComplexForgetIso S').hom = (twoStepComplexForgetIso S).hom ≫ φ.τ₂ := by
  ext n
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- `gr^1` of the two-step filtered complex is `S.X₁`. -/
def twoStepComplexGrOneIso :
    ((FiniteFilteredObject.grP 1).mapHomologicalComplex _).obj (twoStepComplex S) ≅ S.X₁ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => twoStepGrOneIso (degreeShortComplex S n))
    (fun n m _ => (gr_one_map_twoStepMap (degreeShortComplexD S n m)).symm)

/-- Naturality of `gr^1 ≅ S.X₁` for two-step filtered complexes. -/
lemma twoStepComplexGrOneIso_hom_naturality {S' : ShortComplex (CochainComplex C ℤ)}
    [∀ n, Mono (S'.f.f n)] (φ : S ⟶ S') :
    ((FiniteFilteredObject.grP 1).mapHomologicalComplex _).map (twoStepComplexMap φ) ≫
        (twoStepComplexGrOneIso S').hom = (twoStepComplexGrOneIso S).hom ≫ φ.τ₁ := by
  ext n
  exact gr_one_map_twoStepMap (degreeShortComplexMap φ n)

variable (hS : S.ShortExact)

include hS in
omit [∀ (n : ℤ), Mono (S.f.f n)] in
/-- The degree `n` short complex of a short exact sequence of cochain complexes is short
exact. -/
lemma degreeShortComplex_shortExact (n : ℤ) : (degreeShortComplex S n).ShortExact :=
  hS.map_of_exact _

/-- `gr^0` of the two-step filtered complex of a short exact sequence is `S.X₃`. -/
def twoStepComplexGrZeroIso :
    ((FiniteFilteredObject.grP 0).mapHomologicalComplex _).obj (twoStepComplex S) ≅ S.X₃ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => twoStepGrZeroIso (degreeShortComplex S n) (degreeShortComplex_shortExact S hS n))
    (fun n m _ => (gr_zero_map_twoStepMap _ (degreeShortComplex_shortExact S hS n)
      (degreeShortComplex_shortExact S hS m) (degreeShortComplexD S n m)).symm)

/-- Naturality of `gr^0 ≅ S.X₃` for two-step filtered complexes of short exact sequences. -/
lemma twoStepComplexGrZeroIso_hom_naturality {S' : ShortComplex (CochainComplex C ℤ)}
    [∀ n, Mono (S'.f.f n)] (hS' : S'.ShortExact) (φ : S ⟶ S') :
    ((FiniteFilteredObject.grP 0).mapHomologicalComplex _).map (twoStepComplexMap φ) ≫
        (twoStepComplexGrZeroIso S' hS').hom = (twoStepComplexGrZeroIso S hS).hom ≫ φ.τ₃ := by
  ext n
  exact gr_zero_map_twoStepMap _ (degreeShortComplex_shortExact S hS n)
    (degreeShortComplex_shortExact S' hS' n) (degreeShortComplexMap φ n)

/-- `gr^p` of the two-step filtered complex vanishes for `p ∉ {0, 1}`. -/
lemma isZero_twoStepComplex_grP {p : ℤ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    IsZero (((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj (twoStepComplex S)) := by
  rw [IsZero.iff_id_eq_zero]
  ext n
  refine IsZero.eq_of_src ?_ _ _
  rcases lt_or_gt_of_ne hp0 with h | h
  · exact isZero_gr_twoStep_of_neg _ h
  · exact isZero_gr_twoStep_of_two_le _ (by omega)

section Unmap

variable {S S' : ShortComplex (CochainComplex C ℤ)} [∀ n, Mono (S.f.f n)] [∀ n, Mono (S'.f.f n)]
  (hS : S.ShortExact) (M : twoStepComplex S ⟶ twoStepComplex S')

/-- The degree `n` component of a morphism of two-step filtered complexes, as a morphism of short
complexes. -/
def twoStepComplexUnmapDegree (n : ℤ) : degreeShortComplex S n ⟶ degreeShortComplex S' n :=
  twoStepUnmap (degreeShortComplex_shortExact S hS n) (M.f n).hom

/-- The underlying degree `n` component of a morphism of two-step filtered complexes. -/
abbrev twoStepComplexHom (n : ℤ) : S.X₂.X n ⟶ S'.X₂.X n := (M.f n).hom.hom

/-- The degree `n` first square of `twoStepComplexUnmapDegree hS M n` commutes. -/
lemma twoStepComplexUnmapDegree_comm₁₂ (n : ℤ) :
    (twoStepComplexUnmapDegree hS M n).τ₁ ≫ S'.f.f n = S.f.f n ≫ twoStepComplexHom M n :=
  (twoStepComplexUnmapDegree hS M n).comm₁₂

/-- The degree `n` second square of `twoStepComplexUnmapDegree hS M n` commutes. -/
lemma twoStepComplexUnmapDegree_comm₂₃ (n : ℤ) :
    twoStepComplexHom M n ≫ S'.g.f n = S.g.f n ≫ (twoStepComplexUnmapDegree hS M n).τ₃ :=
  (twoStepComplexUnmapDegree hS M n).comm₂₃

/-- The underlying components of a morphism of two-step filtered complexes commute with the
differentials of `S.X₂` and `S'.X₂`. -/
lemma twoStepComplex_comm_hom (n m : ℤ) :
    twoStepComplexHom M n ≫ S'.X₂.d n m = S.X₂.d n m ≫ twoStepComplexHom M m :=
  congrArg (fun x => x.hom.hom) (M.comm n m)

/-- **Every morphism of two-step filtered complexes of a short exact sequence comes from a
morphism of short complexes.** -/
def twoStepComplexUnmap : S ⟶ S' where
  τ₁ :=
    { f n := (twoStepComplexUnmapDegree hS M n).τ₁
      comm' n m _ := by
        rw [← cancel_mono (S'.f.f m), Category.assoc, ← S'.f.comm, ← Category.assoc,
          twoStepComplexUnmapDegree_comm₁₂, Category.assoc, twoStepComplex_comm_hom,
          Category.assoc, twoStepComplexUnmapDegree_comm₁₂, ← Category.assoc, ← Category.assoc,
          S.f.comm] }
  τ₂ :=
    { f n := twoStepComplexHom M n
      comm' n m _ := twoStepComplex_comm_hom M n m }
  τ₃ :=
    { f n := (twoStepComplexUnmapDegree hS M n).τ₃
      comm' n m _ := by
        have : Epi (S.g.f n) := (degreeShortComplex_shortExact S hS n).epi_g
        rw [← cancel_epi (S.g.f n), ← Category.assoc, ← twoStepComplexUnmapDegree_comm₂₃,
          Category.assoc, S'.g.comm, ← Category.assoc, twoStepComplex_comm_hom,
          Category.assoc, twoStepComplexUnmapDegree_comm₂₃, ← Category.assoc, ← S.g.comm,
          Category.assoc] }
  comm₁₂ := HomologicalComplex.hom_ext _ _ fun n => twoStepComplexUnmapDegree_comm₁₂ hS M n
  comm₂₃ := HomologicalComplex.hom_ext _ _ fun n => twoStepComplexUnmapDegree_comm₂₃ hS M n

/-- `twoStepComplexMap` sends `twoStepComplexUnmap hS M` back to `M`. -/
lemma twoStepComplexMap_twoStepComplexUnmap : twoStepComplexMap (twoStepComplexUnmap hS M) = M := by
  ext n : 2
  exact twoStepMap_twoStepUnmap (degreeShortComplex_shortExact S hS n) (M.f n).hom

end Unmap

end TwoStepComplex

end CochainComplex
