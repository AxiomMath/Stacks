module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Glueing along a modification, abstractly

Consider four adjunctions `f^* ⊣ f_*` between `𝒳` and `𝒴`, `i^* ⊣ i_*` between `𝒳` and `𝒵`,
`j^* ⊣ j_*` between `𝒴` and `ℰ` and `g^* ⊣ g_*` between `𝒵` and `ℰ`, and a natural isomorphism
`c : j_* ⋙ f_* ≅ g_* ⋙ i_*`. This is the shape of the small étale topoi of a commutative square
`f ∘ j = i ∘ g` with `i : Z → X` a closed immersion and `f : Y → X` a modification which is an
isomorphism over `X ∖ Z`, as in Stacks, Tag 0GFY.

The *restriction* functor sends `F` to `(f^* F, i^* F)` with the identification
`j^* f^* F ≅ g^* i^* F` conjugate to `c`, an object of the categorical pullback of `j^*` and
`g^*`. It has a right adjoint, the *glueing* functor, which sends `(G', G, α)` to the fibre
product `f_* G' ×_{i_* g_* j^* G'} i_* G`.

The restriction functor is an equivalence as soon as
* the base change map `i^* f_* ⟶ g_* j^*` (the mate of `c`) is invertible,
* the counit of `i^* ⊣ i_*` is invertible (`i_*` is fully faithful),
* `i^*` and the restriction `u^*` to the open complement preserve pullbacks,
* `u^* (i_* M)` is terminal for every `M`,
* `f` is an isomorphism over the open complement: there is an isomorphism
  `f^* ⋙ w^* ≅ u^* ⋙ f_U^*` with `f_U^*` reflecting isomorphisms, where `w^*` is the restriction
  to the preimage of the open complement, and `w^*` inverts the counit of `f^* ⊣ f_*`,
* `u^*` and `i^*` jointly reflect isomorphisms, and so do `w^*` and `j^*`.

## Main definitions

* `CategoryTheory.Adjunction.ModificationGlueing.inverseImageIso`: the identification
  `f^* ⋙ j^* ≅ i^* ⋙ g^*` conjugate to `c`.
* `CategoryTheory.Adjunction.ModificationGlueing.restriction`: the restriction functor.
* `CategoryTheory.Adjunction.ModificationGlueing.glue`: the glueing functor.
* `CategoryTheory.Adjunction.ModificationGlueing.adjunction`: restriction is left adjoint to
  glueing.

## Main results

* `CategoryTheory.Adjunction.ModificationGlueing.isEquivalence_restriction`: the restriction
  functor is an equivalence.

## References

* [Stacks Project, Tag 0GFY](https://stacks.math.columbia.edu/tag/0GFY)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Functor

namespace CategoryTheory.Adjunction

section Conjugate

variable {C D : Type*} [Category* C] [Category* D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- Transposing along `L₁ ⊣ R₁` and composing with the conjugate of `α : L₂ ⟶ L₁` is
transposing along `L₂ ⊣ R₂` after precomposing with `α`. -/
theorem homEquiv_comp_conjugateEquiv_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (X : C) (Y : D) (h : L₁.obj X ⟶ Y) :
    adj₁.homEquiv X Y h ≫ (conjugateEquiv adj₁ adj₂ α).app Y =
      adj₂.homEquiv X Y (α.app X ≫ h) := by
  rw [homEquiv_unit, homEquiv_unit, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality h, ← Category.assoc, unit_conjugateEquiv,
    Category.assoc, Functor.map_comp]

end Conjugate

namespace ModificationGlueing

variable {𝒳 𝒴 𝒵 ℰ : Type*} [Category* 𝒳] [Category* 𝒴] [Category* 𝒵] [Category* ℰ]
  {fu : 𝒳 ⥤ 𝒴} {fl : 𝒴 ⥤ 𝒳} {iu : 𝒳 ⥤ 𝒵} {il : 𝒵 ⥤ 𝒳}
  {ju : 𝒴 ⥤ ℰ} {jl : ℰ ⥤ 𝒴} {gu : 𝒵 ⥤ ℰ} {gl : ℰ ⥤ 𝒵}
  (adjF : fu ⊣ fl) (adjI : iu ⊣ il) (adjJ : ju ⊣ jl) (adjG : gu ⊣ gl)
  (c : jl ⋙ fl ≅ gl ⋙ il)

/-- The identification `f^* ⋙ j^* ≅ i^* ⋙ g^*` of the two composite left adjoints, conjugate to
`c : j_* ⋙ f_* ≅ g_* ⋙ i_*`. -/
def inverseImageIso : fu ⋙ ju ≅ iu ⋙ gu :=
  ((conjugateIsoEquiv (adjF.comp adjJ) (adjI.comp adjG)).symm c).symm

/-- Transposing along `f` and `j`, then composing with `c`, is transposing along `i` and `g`
after precomposing with the inverse of `inverseImageIso`. -/
theorem homEquiv_homEquiv_comp_app (F : 𝒳) (K : ℰ) (h : ju.obj (fu.obj F) ⟶ K) :
    adjF.homEquiv F _ (adjJ.homEquiv _ K h) ≫ c.hom.app K =
      adjI.homEquiv F _ (adjG.homEquiv _ K
        ((inverseImageIso adjF adjI adjJ adjG c).inv.app F ≫ h)) := by
  have h₁ := homEquiv_comp_conjugateEquiv_app (adjF.comp adjJ) (adjI.comp adjG)
    ((conjugateIsoEquiv (adjF.comp adjJ) (adjI.comp adjG)).symm c).hom F K h
  have hc : conjugateEquiv (adjF.comp adjJ) (adjI.comp adjG)
      ((conjugateIsoEquiv (adjF.comp adjJ) (adjI.comp adjG)).symm c).hom = c.hom := by
    simpa only [conjugateIsoEquiv_apply_hom] using
      congrArg Iso.hom ((conjugateIsoEquiv (adjF.comp adjJ) (adjI.comp adjG)).apply_symm_apply c)
  rwa [hc, comp_homEquiv, comp_homEquiv] at h₁

/-- The restriction functor `F ↦ (f^* F, i^* F)` to the categorical pullback of `j^*` and
`g^*`. -/
abbrev restriction : 𝒳 ⥤ CategoricalPullback ju gu where
  obj F :=
    { fst := fu.obj F
      snd := iu.obj F
      iso := (inverseImageIso adjF adjI adjJ adjG c).app F }
  map φ :=
    { fst := fu.map φ
      snd := iu.map φ
      w := (inverseImageIso adjF adjI adjJ adjG c).hom.naturality φ }
  map_id F := by apply CategoricalPullback.hom_ext <;> simp
  map_comp φ ψ := by apply CategoricalPullback.hom_ext <;> simp

/-- The first component of the restriction of `F` is `f^* F`. -/
theorem restriction_obj_fst (F : 𝒳) :
    ((restriction adjF adjI adjJ adjG c).obj F).fst = fu.obj F := rfl

/-- The second component of the restriction of `F` is `i^* F`. -/
theorem restriction_obj_snd (F : 𝒳) :
    ((restriction adjF adjI adjJ adjG c).obj F).snd = iu.obj F := rfl

/-- The identification in the restriction of `F` is `inverseImageIso` at `F`. -/
theorem restriction_obj_iso (F : 𝒳) :
    ((restriction adjF adjI adjJ adjG c).obj F).iso =
      (inverseImageIso adjF adjI adjJ adjG c).app F := rfl

/-- The first component of the restriction of `φ` is `f^* φ`. -/
theorem restriction_map_fst {F F' : 𝒳} (φ : F ⟶ F') :
    ((restriction adjF adjI adjJ adjG c).map φ).fst = fu.map φ := rfl

/-- The second component of the restriction of `φ` is `i^* φ`. -/
theorem restriction_map_snd {F F' : 𝒳} (φ : F ⟶ F') :
    ((restriction adjF adjI adjJ adjG c).map φ).snd = iu.map φ := rfl

/-- The map `f_* G' ⟶ i_* g_* j^* G'`: the unit of `j`, followed by `c`. -/
def toOverlapFst (A : CategoricalPullback ju gu) :
    fl.obj A.fst ⟶ il.obj (gl.obj (ju.obj A.fst)) :=
  fl.map (adjJ.unit.app A.fst) ≫ c.hom.app (ju.obj A.fst)

/-- The map `i_* G ⟶ i_* g_* j^* G'`: the unit of `g`, followed by the identification
`g^* G ≅ j^* G'`. -/
def toOverlapSnd (A : CategoricalPullback ju gu) :
    il.obj A.snd ⟶ il.obj (gl.obj (ju.obj A.fst)) :=
  il.map (adjG.unit.app A.snd ≫ gl.map A.iso.inv)

/-- The map `toOverlapFst` is natural in the object of the categorical pullback. -/
theorem toOverlapFst_naturality {A A' : CategoricalPullback ju gu} (a : A ⟶ A') :
    fl.map a.fst ≫ toOverlapFst adjJ c A' =
      toOverlapFst adjJ c A ≫ il.map (gl.map (ju.map a.fst)) := by
  have hu := adjJ.unit.naturality a.fst
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  dsimp only [toOverlapFst]
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc,
    Category.assoc]
  congr 1
  exact c.hom.naturality (ju.map a.fst)

/-- The map `toOverlapSnd` is natural in the object of the categorical pullback. -/
theorem toOverlapSnd_naturality {A A' : CategoricalPullback ju gu} (a : A ⟶ A') :
    il.map a.snd ≫ toOverlapSnd adjG A' =
      toOverlapSnd adjG A ≫ il.map (gl.map (ju.map a.fst)) := by
  have ha : gu.map a.snd ≫ A'.iso.inv = A.iso.inv ≫ ju.map a.fst := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact a.w.symm
  have hu := adjG.unit.naturality a.snd
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  dsimp only [toOverlapSnd]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, hu]
  simp only [Category.assoc, ← Functor.map_comp, ha]

/-- The base change map `f_* ⋙ i^* ⟶ j^* ⋙ g_*`, the mate of `c`. -/
def baseChange : fl ⋙ iu ⟶ ju ⋙ gl :=
  (mateEquiv adjJ adjI).symm c.hom

/-- `i^*` of the leg `f_* G' ⟶ i_* g_* j^* G'`, followed by the counit of `i`, is the base
change map. -/
theorem map_toOverlapFst_comp_counit (A : CategoricalPullback ju gu) :
    iu.map (toOverlapFst adjJ c A) ≫ adjI.counit.app _ =
      (baseChange adjI adjJ c).app A.fst := by
  simp [baseChange, toOverlapFst, mateEquiv]

/-- The base change map at `G'` is the transpose along `i^* ⊣ i_*` of the unit of `j` followed
by `c`. -/
theorem baseChange_app (G' : 𝒴) :
    (baseChange adjI adjJ c).app G' =
      (adjI.homEquiv _ _).symm (fl.map (adjJ.unit.app G') ≫ c.hom.app (ju.obj G')) := by
  rw [Adjunction.homEquiv_counit]
  simp [baseChange, mateEquiv]

/-- `g^*` of the base change map at `G'`, followed by the counit of `g`, is the inverse of the
identification `j^* f^* ≅ g^* i^*` at `f_* G'`, followed by the image under `j^*` of the counit
of `f`. -/
theorem map_baseChange_app_comp_counit (G' : 𝒴) :
    gu.map ((baseChange adjI adjJ c).app G') ≫ adjG.counit.app (ju.obj G') =
      (inverseImageIso adjF adjI adjJ adjG c).inv.app (fl.obj G') ≫
        ju.map (adjF.counit.app G') := by
  have hβ : adjG.homEquiv (iu.obj (fl.obj G')) (ju.obj G')
      (gu.map ((baseChange adjI adjJ c).app G') ≫ adjG.counit.app (ju.obj G')) =
        (baseChange adjI adjJ c).app G' := by
    rw [← Equiv.eq_symm_apply, Adjunction.homEquiv_counit]
  have hβ' : adjI.homEquiv (fl.obj G') (gl.obj (ju.obj G')) ((baseChange adjI adjJ c).app G') =
      fl.map (adjJ.unit.app G') ≫ c.hom.app (ju.obj G') :=
    (congrArg (adjI.homEquiv _ _) (baseChange_app adjI adjJ c G')).trans
      (Equiv.apply_symm_apply _ _)
  apply (adjG.homEquiv (iu.obj (fl.obj G')) (ju.obj G')).injective
  apply (adjI.homEquiv (fl.obj G') (gl.obj (ju.obj G'))).injective
  rw [← homEquiv_homEquiv_comp_app adjF adjI adjJ adjG c (fl.obj G') (ju.obj G'), hβ, hβ',
    Adjunction.homEquiv_unit (adj := adjJ)]
  have hu : adjJ.unit.app (fu.obj (fl.obj G')) ≫ jl.map (ju.map (adjF.counit.app G')) =
      adjF.counit.app G' ≫ adjJ.unit.app G' :=
    (adjJ.unit.naturality (adjF.counit.app G')).symm
  have ht : adjF.homEquiv (fl.obj G') ((𝟭 𝒴).obj G') (adjF.counit.app G') = 𝟙 _ := by
    simp [Adjunction.homEquiv_unit]
  rw [hu, Adjunction.homEquiv_naturality_right, ht, Category.id_comp]

/-- **The counit of `f` through base change.** The image under `j^*` of the counit of `f` at
`G'` is the identification `j^* f^* ≅ g^* i^*` at `f_* G'`, followed by `g^*` of the base change
map and the counit of `g`. -/
theorem inverseImageIso_hom_app_comp_baseChange (G' : 𝒴) :
    (inverseImageIso adjF adjI adjJ adjG c).hom.app (fl.obj G') ≫
        gu.map ((baseChange adjI adjJ c).app G') ≫ adjG.counit.app (ju.obj G') =
      ju.map (adjF.counit.app G') := by
  rw [map_baseChange_app_comp_counit, Iso.hom_inv_id_app_assoc]

/-- If the base change map is invertible and the counit of `g` is, then `j^*` inverts the counit
of `f`. -/
theorem isIso_map_counit_of_isIso_baseChange (hbc : IsIso (baseChange adjI adjJ c))
    [IsIso adjG.counit] (G' : 𝒴) : IsIso (ju.map (adjF.counit.app G')) := by
  rw [← inverseImageIso_hom_app_comp_baseChange adjF adjI adjJ adjG c G']
  infer_instance

/-- A morphism of the categorical pullback is an isomorphism once both components are. -/
theorem isIso_of_isIso_fst_of_isIso_snd {A B : CategoricalPullback ju gu} (a : A ⟶ B)
    [IsIso a.fst] [IsIso a.snd] : IsIso a := by
  refine ⟨⟨{ fst := inv a.fst, snd := inv a.snd, w := ?_ }, ?_, ?_⟩⟩
  · rw [Functor.map_inv, Functor.map_inv, IsIso.inv_comp_eq, ← Category.assoc, a.w,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · apply CategoricalPullback.hom_ext <;> simp
  · apply CategoricalPullback.hom_ext <;> simp

/-- If the second component of a morphism of the categorical pullback is invertible, then so
is the image under `j^*` of the first. -/
theorem isIso_map_fst_of_isIso_snd {A B : CategoricalPullback ju gu} (a : A ⟶ B)
    [IsIso a.snd] : IsIso (ju.map a.fst) := by
  have h : IsIso (ju.map a.fst ≫ B.iso.hom) := by
    rw [a.w]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

variable [HasPullbacks 𝒳]

/-- The glued object `f_* G' ×_{i_* g_* j^* G'} i_* G`. -/
abbrev glueObj (A : CategoricalPullback ju gu) : 𝒳 :=
  pullback (toOverlapFst adjJ c A) (toOverlapSnd adjG A)

/-- The glueing functor `(G', G, α) ↦ f_* G' ×_{i_* g_* j^* G'} i_* G`. -/
abbrev glue : CategoricalPullback ju gu ⥤ 𝒳 where
  obj := glueObj adjJ adjG c
  map a := pullback.map _ _ _ _ (fl.map a.fst) (il.map a.snd) (il.map (gl.map (ju.map a.fst)))
    (toOverlapFst_naturality adjJ c a).symm (toOverlapSnd_naturality adjG a).symm
  map_id A := by
    dsimp only [glueObj]
    apply pullback.hom_ext <;> simp
  map_comp a b := by
    dsimp only [glueObj]
    simp only [CategoricalPullback.comp_fst, CategoricalPullback.comp_snd, Functor.map_comp,
      pullback.map_comp]

/-- The glueing of a morphism `a`, followed by the projection to `f_* G'`, is that projection
followed by `f_*` of the first component of `a`. -/
@[reassoc (attr := simp)]
theorem glue_map_fst {A A' : CategoricalPullback ju gu} (a : A ⟶ A') :
    (glue adjJ adjG c).map a ≫ pullback.fst (toOverlapFst adjJ c A') (toOverlapSnd adjG A') =
      pullback.fst (toOverlapFst adjJ c A) (toOverlapSnd adjG A) ≫ fl.map a.fst := by
  simp [glue, pullback.map]

/-- The glueing of a morphism `a`, followed by the projection to `i_* G`, is that projection
followed by `i_*` of the second component of `a`. -/
@[reassoc (attr := simp)]
theorem glue_map_snd {A A' : CategoricalPullback ju gu} (a : A ⟶ A') :
    (glue adjJ adjG c).map a ≫ pullback.snd (toOverlapFst adjJ c A') (toOverlapSnd adjG A') =
      pullback.snd (toOverlapFst adjJ c A) (toOverlapSnd adjG A) ≫ il.map a.snd := by
  simp [glue, pullback.map]

omit [HasPullbacks 𝒳] in
/-- The transposes of `a : f^* F ⟶ G'` and `b : i^* F ⟶ G` agree in `i_* g_* j^* G'` if and only
if `(a, b)` is compatible with the identifications `j^* f^* F ≅ g^* i^* F` and `j^* G' ≅ g^* G`.
-/
theorem compatibility_iff (F : 𝒳) (A : CategoricalPullback ju gu)
    (a : fu.obj F ⟶ A.fst) (b : iu.obj F ⟶ A.snd) :
    adjF.homEquiv _ _ a ≫ toOverlapFst adjJ c A = adjI.homEquiv _ _ b ≫ toOverlapSnd adjG A ↔
      ju.map a ≫ A.iso.hom = (inverseImageIso adjF adjI adjJ adjG c).hom.app F ≫ gu.map b := by
  have hl : adjF.homEquiv _ _ a ≫ toOverlapFst adjJ c A =
      adjI.homEquiv _ _ (adjG.homEquiv _ _
        ((inverseImageIso adjF adjI adjJ adjG c).inv.app F ≫ ju.map a)) := by
    rw [← homEquiv_homEquiv_comp_app, toOverlapFst, ← Category.assoc,
      ← Adjunction.homEquiv_naturality_right]
    simp [Adjunction.homEquiv_unit]
  have hr : adjI.homEquiv _ _ b ≫ toOverlapSnd adjG A =
      adjI.homEquiv _ _ (adjG.homEquiv _ _ (gu.map b ≫ A.iso.inv)) := by
    rw [toOverlapSnd, ← adjI.homEquiv_naturality_right]
    simp [Adjunction.homEquiv_unit]
  rw [hl, hr, Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq, ← Iso.app_inv, Iso.inv_comp_eq,
    ← Category.assoc, Iso.eq_comp_inv, Iso.app_hom]

/-- The bijection `(restriction F ⟶ A) ≃ (F ⟶ glue A)`. -/
def homEquiv (F : 𝒳) (A : CategoricalPullback ju gu) :
    ((restriction adjF adjI adjJ adjG c).obj F ⟶ A) ≃ (F ⟶ (glue adjJ adjG c).obj A) where
  toFun a := pullback.lift (adjF.homEquiv _ _ a.fst) (adjI.homEquiv _ _ a.snd)
    ((compatibility_iff adjF adjI adjJ adjG c F A a.fst a.snd).mpr a.w)
  invFun a :=
    { fst := (adjF.homEquiv _ _).symm (a ≫ pullback.fst _ _)
      snd := (adjI.homEquiv _ _).symm (a ≫ pullback.snd _ _)
      w := (compatibility_iff adjF adjI adjJ adjG c F A _ _).mp
        (by simp only [Equiv.apply_symm_apply, Category.assoc, pullback.condition]) }
  left_inv a := by
    apply CategoricalPullback.hom_ext
    · dsimp only
      rw [pullback.lift_fst, Equiv.symm_apply_apply]
    · dsimp only
      rw [pullback.lift_snd, Equiv.symm_apply_apply]
  right_inv a := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Equiv.apply_symm_apply]
    · rw [pullback.lift_snd, Equiv.apply_symm_apply]

/-- The image of `a` under `homEquiv`, followed by the projection to `f_* G'`, is the transpose
along `f^* ⊣ f_*` of the first component of `a`. -/
@[reassoc]
theorem homEquiv_apply_fst (F : 𝒳) (A : CategoricalPullback ju gu)
    (a : (restriction adjF adjI adjJ adjG c).obj F ⟶ A) :
    homEquiv adjF adjI adjJ adjG c F A a ≫
        pullback.fst (toOverlapFst adjJ c A) (toOverlapSnd adjG A) =
      adjF.homEquiv _ _ a.fst :=
  pullback.lift_fst _ _ _

/-- The image of `a` under `homEquiv`, followed by the projection to `i_* G`, is the transpose
along `i^* ⊣ i_*` of the second component of `a`. -/
@[reassoc]
theorem homEquiv_apply_snd (F : 𝒳) (A : CategoricalPullback ju gu)
    (a : (restriction adjF adjI adjJ adjG c).obj F ⟶ A) :
    homEquiv adjF adjI adjJ adjG c F A a ≫
        pullback.snd (toOverlapFst adjJ c A) (toOverlapSnd adjG A) =
      adjI.homEquiv _ _ a.snd :=
  pullback.lift_snd _ _ _

/-- The first component of the inverse image of `a` under `homEquiv` is the transpose along
`f^* ⊣ f_*` of `a` followed by the projection to `f_* G'`. -/
theorem homEquiv_symm_apply_fst (F : 𝒳) (A : CategoricalPullback ju gu)
    (a : F ⟶ (glue adjJ adjG c).obj A) :
    ((homEquiv adjF adjI adjJ adjG c F A).symm a).fst =
      (adjF.homEquiv _ _).symm (a ≫ pullback.fst _ _) := rfl

/-- The second component of the inverse image of `a` under `homEquiv` is the transpose along
`i^* ⊣ i_*` of `a` followed by the projection to `i_* G`. -/
theorem homEquiv_symm_apply_snd (F : 𝒳) (A : CategoricalPullback ju gu)
    (a : F ⟶ (glue adjJ adjG c).obj A) :
    ((homEquiv adjF adjI adjJ adjG c F A).symm a).snd =
      (adjI.homEquiv _ _).symm (a ≫ pullback.snd _ _) := rfl

/-- **The glueing adjunction.** Restriction to the modification and the closed part is left
adjoint to glueing. -/
def adjunction : restriction adjF adjI adjJ adjG c ⊣ glue adjJ adjG c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv adjF adjI adjJ adjG c
      homEquiv_naturality_left_symm := by
        intro F F' A a b
        apply CategoricalPullback.hom_ext
        · rw [homEquiv_symm_apply_fst, CategoricalPullback.comp_fst, homEquiv_symm_apply_fst,
            Category.assoc, Adjunction.homEquiv_naturality_left_symm]
        · rw [homEquiv_symm_apply_snd, CategoricalPullback.comp_snd, homEquiv_symm_apply_snd,
            Category.assoc, Adjunction.homEquiv_naturality_left_symm]
      homEquiv_naturality_right := by
        intro F A A' a b
        apply pullback.hom_ext
        · rw [homEquiv_apply_fst, Category.assoc, glue_map_fst, homEquiv_apply_fst_assoc,
            CategoricalPullback.comp_fst, Adjunction.homEquiv_naturality_right]
        · rw [homEquiv_apply_snd, Category.assoc, glue_map_snd, homEquiv_apply_snd_assoc,
            CategoricalPullback.comp_snd, Adjunction.homEquiv_naturality_right] }

/-- The unit of the glueing adjunction at `F`, followed by the projection to `f_* f^* F`, is the
unit of `f^* ⊣ f_*` at `F`. -/
theorem adjunction_unit_app_fst (F : 𝒳) :
    (adjunction adjF adjI adjJ adjG c).unit.app F ≫
        pullback.fst (toOverlapFst adjJ c _) (toOverlapSnd adjG _) = adjF.unit.app F := by
  change homEquiv adjF adjI adjJ adjG c F _ (𝟙 _) ≫ _ = _
  rw [homEquiv_apply_fst, CategoricalPullback.id_fst, Adjunction.homEquiv_unit]
  change adjF.unit.app F ≫ fl.map (𝟙 (fu.obj F)) = _
  rw [Functor.map_id]
  exact Category.comp_id _

/-- The first component of the counit of the glueing adjunction at `A` is `f^*` of the
projection to `f_* G'`, followed by the counit of `f^* ⊣ f_*`. -/
theorem adjunction_counit_app_fst (A : CategoricalPullback ju gu) :
    ((adjunction adjF adjI adjJ adjG c).counit.app A).fst =
      fu.map (pullback.fst (toOverlapFst adjJ c A) (toOverlapSnd adjG A)) ≫
        adjF.counit.app A.fst := by
  change ((homEquiv adjF adjI adjJ adjG c _ A).symm (𝟙 _)).fst = _
  rw [homEquiv_symm_apply_fst, Category.id_comp, Adjunction.homEquiv_counit]

/-- The second component of the counit of the glueing adjunction at `A` is `i^*` of the
projection to `i_* G`, followed by the counit of `i^* ⊣ i_*`. -/
theorem adjunction_counit_app_snd (A : CategoricalPullback ju gu) :
    ((adjunction adjF adjI adjJ adjG c).counit.app A).snd =
      iu.map (pullback.snd (toOverlapFst adjJ c A) (toOverlapSnd adjG A)) ≫
        adjI.counit.app A.snd := by
  change ((homEquiv adjF adjI adjJ adjG c _ A).symm (𝟙 _)).snd = _
  rw [homEquiv_symm_apply_snd, Category.id_comp, Adjunction.homEquiv_counit]

section Equivalence

variable {𝒰 𝒱 : Type*} [Category* 𝒰] [Category* 𝒱]

/-- When the base change map is invertible and `i_*` is fully faithful, `i^*` inverts the
projection of the glued object to `i_* G`. -/
theorem isIso_map_pullback_snd [IsIso adjI.counit] [PreservesLimitsOfShape WalkingCospan iu]
    (hbc : IsIso (baseChange adjI adjJ c)) (A : CategoricalPullback ju gu) :
    IsIso (iu.map (pullback.snd (toOverlapFst adjJ c A) (toOverlapSnd adjG A))) := by
  have h : IsIso (iu.map (toOverlapFst adjJ c A) ≫ adjI.counit.app _) := by
    rw [map_toOverlapFst_comp_counit]
    infer_instance
  have : IsIso (iu.map (toOverlapFst adjJ c A)) := (isIso_comp_right_iff _ _).mp h
  exact ((IsPullback.of_hasPullback _ _).map iu).isIso_snd_of_isIso

/-- When `u^*` kills every `i_* M`, it inverts the projection of the glued object to
`f_* G'`. -/
theorem isIso_map_pullback_fst (uu : 𝒳 ⥤ 𝒰) [PreservesLimitsOfShape WalkingCospan uu]
    (hterm : ∀ M, IsTerminal (uu.obj (il.obj M))) (A : CategoricalPullback ju gu) :
    IsIso (uu.map (pullback.fst (toOverlapFst adjJ c A) (toOverlapSnd adjG A))) := by
  have : IsIso (uu.map (toOverlapSnd adjG A)) := isIso_of_isTerminal (hterm _) (hterm _) _
  exact ((IsPullback.of_hasPullback _ _).map uu).isIso_fst_of_isIso

omit [HasPullbacks 𝒳] in
/-- Over the open complement `f` is an isomorphism, so `u^*` inverts the unit of `f`. -/
theorem isIso_map_unit (uu : 𝒳 ⥤ 𝒰) (wu : 𝒴 ⥤ 𝒱) (fUu : 𝒰 ⥤ 𝒱) [fUu.ReflectsIsomorphisms]
    (e : fu ⋙ wu ≅ uu ⋙ fUu) (hw : ∀ G', IsIso (wu.map (adjF.counit.app G'))) (F : 𝒳) :
    IsIso (uu.map (adjF.unit.app F)) := by
  have h := congrArg wu.map (adjF.left_triangle_components F)
  rw [Functor.map_comp, Functor.map_id] at h
  have := hw (fu.obj F)
  have : IsIso (wu.map (fu.map (adjF.unit.app F))) := isIso_of_comp_hom_eq_id _ h
  have : IsIso (fUu.map (uu.map (adjF.unit.app F))) :=
    (NatIso.isIso_map_iff e (adjF.unit.app F)).mp this
  exact isIso_of_reflects_iso _ fUu

/-- **Glueing along a modification** (abstract form of Stacks, Tag 0GFY). Under the hypotheses
listed in the module docstring, restriction to the modification and the closed part is an
equivalence onto the categorical pullback of `j^*` and `g^*`; its inverse is `glue`. -/
theorem isEquivalence_restriction [IsIso adjI.counit] [PreservesLimitsOfShape WalkingCospan iu]
    (hbc : IsIso (baseChange adjI adjJ c))
    (uu : 𝒳 ⥤ 𝒰) [PreservesLimitsOfShape WalkingCospan uu]
    (hterm : ∀ M, IsTerminal (uu.obj (il.obj M)))
    (wu : 𝒴 ⥤ 𝒱) (fUu : 𝒰 ⥤ 𝒱) [fUu.ReflectsIsomorphisms] (e : fu ⋙ wu ≅ uu ⋙ fUu)
    (hw : ∀ G', IsIso (wu.map (adjF.counit.app G')))
    (hX : ∀ {F F' : 𝒳} (φ : F ⟶ F'), IsIso (uu.map φ) → IsIso (iu.map φ) → IsIso φ)
    (hY : ∀ {G G' : 𝒴} (ψ : G ⟶ G'), IsIso (wu.map ψ) → IsIso (ju.map ψ) → IsIso ψ) :
    (restriction adjF adjI adjJ adjG c).IsEquivalence := by
  have hsnd : ∀ A, IsIso ((adjunction adjF adjI adjJ adjG c).counit.app A).snd := fun A => by
    rw [adjunction_counit_app_snd]
    exact IsIso.comp_isIso' (isIso_map_pullback_snd adjI adjJ adjG c hbc A) inferInstance
  have hcounit : ∀ A, IsIso ((adjunction adjF adjI adjJ adjG c).counit.app A) := fun A => by
    have := hsnd A
    have hfst : IsIso ((adjunction adjF adjI adjJ adjG c).counit.app A).fst := by
      apply hY
      · rw [adjunction_counit_app_fst, Functor.map_comp]
        have := isIso_map_pullback_fst adjJ adjG c uu hterm A
        exact IsIso.comp_isIso' ((NatIso.isIso_map_iff e _).mpr
          (Functor.map_isIso fUu (uu.map _))) (hw A.fst)
      · exact isIso_map_fst_of_isIso_snd ((adjunction adjF adjI adjJ adjG c).counit.app A)
    exact isIso_of_isIso_fst_of_isIso_snd _
  have hunit : ∀ F, IsIso ((adjunction adjF adjI adjJ adjG c).unit.app F) := fun F => by
    apply hX
    · have := isIso_map_pullback_fst adjJ adjG c uu hterm
        ((restriction adjF adjI adjJ adjG c).obj F)
      have : IsIso (uu.map ((adjunction adjF adjI adjJ adjG c).unit.app F) ≫
          uu.map (pullback.fst (toOverlapFst adjJ c ((restriction adjF adjI adjJ adjG c).obj F))
            (toOverlapSnd adjG ((restriction adjF adjI adjJ adjG c).obj F)))) := by
        rw [← Functor.map_comp, adjunction_unit_app_fst]
        exact isIso_map_unit adjF uu wu fUu e hw F
      exact IsIso.of_isIso_comp_right _ (uu.map (pullback.fst _ _))
    · have h := congrArg CategoricalPullback.Hom.snd
        ((adjunction adjF adjI adjJ adjG c).left_triangle_components F)
      rw [CategoricalPullback.comp_snd, CategoricalPullback.id_snd] at h
      exact @isIso_of_comp_hom_eq_id _ _ _ _ _ (hsnd _) _ h
  exact (adjunction adjF adjI adjJ adjG c).toEquivalence.isEquivalence_functor

end Equivalence

end ModificationGlueing

end CategoryTheory.Adjunction
