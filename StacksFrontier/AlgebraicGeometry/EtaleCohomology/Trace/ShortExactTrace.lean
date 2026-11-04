module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LefschetzTraceFormula
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ShortExactFiltration
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Homology.Perfect.LargeUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additivity of the trace along a short exact sequence of complexes

Let `0 → N → M → Q → 0` be a short exact sequence of cochain complexes of modules over a ring
`R`, with `N` and `Q` perfect, and let `φ` be an endomorphism of the sequence. Then `M` is
perfect and

`Tr(φ | M) = Tr(φ | N) + Tr(φ | Q)`

in `R^natural`. This is how Step 1 of the proof of [Stacks, Tag 03UG] uses the filtered derived
category: the filtration `F^0 M = M ⊇ F^1 M = N ⊇ F^2 M = 0` makes `M` an object of `DF(R)`
whose graded pieces are `Q` and `N`, the endomorphism is a filtered endomorphism, and the
additivity of the trace along a filtration ([Stacks, Tag 03TK]) gives the identity.

## Main results

* `CategoryTheory.FilteredDerived.perfectDerivedTrace_congr`: the trace is invariant under
  conjugation by an isomorphism.
* `CategoryTheory.FilteredDerived.isPerfect_X₂_of_shortExact`: the middle term of a short exact
  sequence with perfect ends is perfect.
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_X₂_eq_add`: additivity of the trace.

## Implementation notes

To apply [Stacks, Tag 03TK] the filtered complex must have a bounded representative by
filtered finite projective modules. It is produced from finite projective representatives
`P_N → N` and `P_Q → Q`: the morphism `P_Q⟦-1⟧ ⟶ N` classifying the extension lifts, up to
homotopy, to `P_Q⟦-1⟧ ⟶ P_N`, whose mapping cone `P_N → C → P_Q` maps to `N → M → Q` by a
morphism of short exact sequences which is a quasi-isomorphism on both ends, hence a filtered
quasi-isomorphism of the two-step filtered complexes.

## References

* [Stacks Project, Tag 03TK](https://stacks.math.columbia.edu/tag/03TK)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

/-! ### Invariance of the trace under conjugation -/

section Conj

variable (R : Type u) [Ring R]

/-- A morphism `Q P ⟶ Q L` out of a K-projective complex is the image of a morphism of
complexes. -/
lemma exists_map_eq_of_isKProjective {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P L : CochainComplex C ℤ) [P.IsKProjective]
    (φ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :
    ∃ g : P ⟶ L, DerivedCategory.Q.map g = φ := by
  obtain ⟨gh, hgh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj L)).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ φ ≫
        (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective gh
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P),
    ← DerivedCategory.quotientCompQhIso_hom_naturality, hgh]
  simp

/-- A bounded complex of finite projective modules is K-projective. -/
lemma isKProjective_of_finiteProjectiveComplex {P : CochainComplex (ModuleCat.{v} R) ℤ}
    (hP : finiteProjectiveComplex R P) : P.IsKProjective := by
  obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
  let : P.IsStrictlyLE d := hd
  let (i : ℤ) : Module.Projective R (P.X i) := (hproj i).1
  let (i : ℤ) : Projective (P.X i) := inferInstance
  exact CochainComplex.isKProjective_of_projective P d

/-- **The trace is invariant under conjugation.** If `e : K ≅ K'` intertwines `f` and `f'`, then
`Tr(f | K) = Tr(f' | K')`. -/
@[sga "6 I 8.4" "special case", sga "6 I 8.5" "special case"]
theorem perfectDerivedTrace_congr (K K' : PerfectDerivedCategory.{u, v} R) (e : K.obj ≅ K'.obj)
    (f : K.obj ⟶ K.obj) (f' : K'.obj ⟶ K'.obj) (h : f ≫ e.hom = e.hom ≫ f') :
    perfectDerivedTrace R K f = perfectDerivedTrace R K' f' := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := (isPerfect_iff R K.obj).mp K.property
  have := isKProjective_of_finiteProjectiveComplex R hP
  obtain ⟨g, hg⟩ := exists_map_eq_of_isKProjective P P (eP.hom ≫ f ≫ eP.inv)
  rw [perfectDerivedTrace_eq_alternatingTrace R K f P hP eP g hg,
    perfectDerivedTrace_eq_alternatingTrace R K' f' P hP (eP ≪≫ e) g]
  rw [hg]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← reassoc_of% h]
  simp

/-- A morphism into the target of a quasi-isomorphism, out of a K-projective complex, lifts up to
homotopy. -/
lemma exists_homotopy_lift {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K A B : CochainComplex C ℤ} [K.IsKProjective] (p : A ⟶ B) [QuasiIso p] (f : K ⟶ B) :
    ∃ g : K ⟶ A, Nonempty (Homotopy (g ≫ p) f) := by
  obtain ⟨g, hg⟩ := exists_map_eq_of_isKProjective K A
    (DerivedCategory.Q.map f ≫ inv (DerivedCategory.Q.map p))
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient _ _).obj B)).injective
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app B),
    DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, Functor.map_comp, hg]
  simp

end Conj

/-! ### A filtered finite projective representative -/

section Representative

open CochainComplex HomComplex

variable {R : Type u} [Ring R] {S : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ)}
  (hS : S.ShortExact) {P₁ P₃ : CochainComplex (ModuleCat.{max u v} R) ℤ}
  [P₃.IsKProjective] [∀ n, Projective (P₃.X n)] (p₁ : P₁ ⟶ S.X₁) [QuasiIso p₁]
  (q₃ : P₃ ⟶ S.X₃)

/-- The morphism `q₃ : P₃ ⟶ X₃`, as a `(-1)`-cochain from `P₃⟦-1⟧`. -/
def repQ : Cochain (P₃⟦(-1 : ℤ)⟧) S.X₃ (-1) :=
  -(Cochain.ofHom q₃).leftShift (-1) (-1) (by omega)

omit [P₃.IsKProjective] [∀ n, Projective (P₃.X n)] in
/-- `repQ` is a cocycle. -/
lemma δ_repQ : δ (-1) 0 (repQ q₃) = 0 := by
  rw [repQ, δ_neg, Cochain.δ_leftShift _ (-1) (-1) 0 (by omega) 1 (by omega), δ_ofHom,
    Cochain.leftShift_zero, smul_zero, neg_zero]

include hS in
/-- Each component of `S.g` is an epimorphism. -/
lemma epi_g_f (n : ℤ) : Epi (S.g.f n) :=
  (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).epi_g

/-- A degreewise lift of `repQ` along `S.g`, using that the terms of `P₃` are projective. -/
def repL : Cochain (P₃⟦(-1 : ℤ)⟧) S.X₂ (-1) :=
  Cochain.mk fun p q hpq =>
    haveI := epi_g_f hS q
    haveI : Projective ((P₃⟦(-1 : ℤ)⟧).X p) := inferInstanceAs (Projective (P₃.X (p + -1)))
    Projective.factorThru ((repQ q₃).v p q hpq) (S.g.f q)

omit [P₃.IsKProjective] in
/-- `repL` lifts `repQ` along `S.g`. -/
lemma repL_comp_g : (repL hS q₃).comp (Cochain.ofHom S.g) (add_zero _) = repQ q₃ := by
  ext p q hpq
  simp [repL, Cochain.comp_zero_cochain_v]

omit [P₃.IsKProjective] in
/-- The image of `δ (repL)` in `X₃` vanishes. -/
lemma δ_repL_comp_g :
    (δ (-1) 0 (repL hS q₃)).comp (Cochain.ofHom S.g) (add_zero _) = 0 := by
  rw [← δ_comp_ofHom, repL_comp_g, δ_repQ]

/-- The `0`-cocycle `δ (repL)`, whose image in `X₃` vanishes. -/
def repM : P₃⟦(-1 : ℤ)⟧ ⟶ S.X₂ :=
  Cocycle.homOf (Cocycle.mk (δ (-1) 0 (repL hS q₃)) 1 (by omega) (δ_δ _ _ _ _))

omit [P₃.IsKProjective] in
/-- `repM ≫ S.g = 0`. -/
lemma repM_comp_g : repM hS q₃ ≫ S.g = 0 := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp, repM, Cocycle.cochain_ofHom_homOf_eq_coe, Cochain.ofHom_zero]
  exact δ_repL_comp_g hS q₃

/-- The morphism `P₃⟦-1⟧ ⟶ X₁` classifying the extension: `δ (repL)` lands in `X₁`. -/
def repE : P₃⟦(-1 : ℤ)⟧ ⟶ S.X₁ :=
  haveI := hS.mono_f
  hS.exact.lift (repM hS q₃) (repM_comp_g hS q₃)

omit [P₃.IsKProjective] in
/-- `repE ≫ S.f` is the cochain `δ (repL)`. -/
lemma ofHom_repE_comp_f : Cochain.ofHom (repE hS q₃ ≫ S.f) = δ (-1) 0 (repL hS q₃) := by
  have := hS.mono_f
  rw [repE, ShortComplex.Exact.lift_f, repM, Cocycle.cochain_ofHom_homOf_eq_coe]
  rfl

/-- A lift of `repE` along the quasi-isomorphism `p₁`, up to homotopy. -/
def repδ : P₃⟦(-1 : ℤ)⟧ ⟶ P₁ :=
  (exists_homotopy_lift p₁ (repE hS q₃)).choose

/-- The homotopy `repδ ≫ p₁ ∼ repE`. -/
def repH : Homotopy (repδ hS p₁ q₃ ≫ p₁) (repE hS q₃) :=
  (exists_homotopy_lift p₁ (repE hS q₃)).choose_spec.some

/-- The `(-1)`-cochain from which the morphism out of the mapping cone is built. -/
def repα : Cochain (P₃⟦(-1 : ℤ)⟧) S.X₂ (-1) :=
  repL hS q₃ + (Cochain.equivHomotopy _ _ (repH hS p₁ q₃)).1.comp (Cochain.ofHom S.f)
    (add_zero _)

/-- `δ (repα)` is the cochain of `repδ ≫ p₁ ≫ S.f`. -/
lemma δ_repα : δ (-1) 0 (repα hS p₁ q₃) = Cochain.ofHom (repδ hS p₁ q₃ ≫ p₁ ≫ S.f) := by
  have h := (Cochain.equivHomotopy _ _ (repH hS p₁ q₃)).2
  rw [repα, δ_add, δ_comp_ofHom, ← ofHom_repE_comp_f hS q₃,
    eq_sub_of_add_eq h.symm, Cochain.sub_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    ← Category.assoc]
  abel

/-- **The comparison morphism** `C ⟶ X₂` from the mapping cone of `repδ`. -/
def repΦ : mappingCone (repδ hS p₁ q₃) ⟶ S.X₂ :=
  mappingCone.desc _ (repα hS p₁ q₃) (p₁ ≫ S.f) (δ_repα hS p₁ q₃)

/-- The short exact sequence `P₁ ⟶ C ⟶ P₃⟦-1⟧⟦1⟧` of the mapping cone. -/
abbrev repShortComplex : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ) :=
  mappingCone.triangleRotateShortComplex (repδ hS p₁ q₃)

/-- The mapping-cone sequence `P₁ ⟶ C ⟶ P₃⟦-1⟧⟦1⟧` is short exact. -/
lemma repShortComplex_shortExact : (repShortComplex hS p₁ q₃).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    (mappingCone.triangleRotateShortComplexSplitting (repδ hS p₁ q₃) n).shortExact

/-- The third component of the comparison: `P₃⟦-1⟧⟦1⟧ ≅ P₃ ⟶ X₃`. -/
def repτ₃ : (P₃⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ⟶ S.X₃ :=
  (shiftFunctorCompIsoId (CochainComplex (ModuleCat.{max u v} R) ℤ) (-1 : ℤ) 1
    (by omega)).hom.app P₃ ≫ q₃

/-- The comparison morphism commutes with the second maps of the two sequences. -/
lemma repΦ_comp_g :
    repΦ hS p₁ q₃ ≫ S.g = (repShortComplex hS p₁ q₃).g ≫ repτ₃ q₃ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have e : ((repShortComplex hS p₁ q₃).g ≫ repτ₃ q₃).f n =
      (mappingCone.triangle (repδ hS p₁ q₃)).mor₃.f n ≫ (repτ₃ q₃).f n := rfl
  rw [e, HomologicalComplex.comp_f]
  refine mappingCone.ext_from (repδ hS p₁ q₃) (n + 1) n rfl ?_ ?_
  · have h1 : (repα hS p₁ q₃).v (n + 1) n (by omega) ≫ S.g.f n = (repQ q₃).v (n + 1) n
        (by omega) := by
      have h := Cochain.congr_v (repL_comp_g hS q₃) (n + 1) n (by omega)
      simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h
      rw [repα, Cochain.add_v, Preadditive.add_comp, h, Cochain.comp_zero_cochain_v,
        Cochain.ofHom_v, Category.assoc, ← HomologicalComplex.comp_f, S.zero,
        HomologicalComplex.zero_f, comp_zero, add_zero]
    rw [repΦ, mappingCone.inl_v_desc_f_assoc, h1]
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (fun x => x ≫ (repτ₃ q₃).f n)
      (mappingCone.inl_v_triangle_mor₃_f (repδ hS p₁ q₃) (n + 1) n (by omega))).symm
    rw [repQ, Cochain.neg_v, Cochain.leftShift_v _ (-1) (-1) (by omega) (n + 1) n (by omega) n
      (by omega), Cochain.ofHom_v]
    simp [repτ₃, shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f,
      show Int.negOnePow 2 = 1 from rfl]
  · refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (fun x => x ≫ (repτ₃ q₃).f n)
      (mappingCone.inr_f_triangle_mor₃_f (repδ hS p₁ q₃) n))).symm
    refine Eq.trans ?_ zero_comp.symm
    rw [repΦ, mappingCone.inr_f_desc_f_assoc,
      HomologicalComplex.comp_f, Category.assoc, ← HomologicalComplex.comp_f, S.zero,
      HomologicalComplex.zero_f, comp_zero]

/-- **The comparison morphism of short exact sequences**, from the mapping-cone sequence
`P₁ ⟶ C ⟶ P₃⟦-1⟧⟦1⟧` to `S`. -/
@[simps]
def repMap : repShortComplex hS p₁ q₃ ⟶ S where
  τ₁ := p₁
  τ₂ := repΦ hS p₁ q₃
  τ₃ := repτ₃ q₃
  comm₁₂ := (mappingCone.inr_desc (repδ hS p₁ q₃) (repα hS p₁ q₃) (p₁ ≫ S.f)
    (δ_repα hS p₁ q₃)).symm
  comm₂₃ := repΦ_comp_g hS p₁ q₃

/-- `repτ₃` is a quasi-isomorphism when `q₃` is. -/
instance [QuasiIso q₃] : QuasiIso (repτ₃ q₃) := by
  unfold repτ₃
  infer_instance

/-- The first map of the mapping-cone sequence is a monomorphism in each degree. -/
instance (n : ℤ) : Mono ((repShortComplex hS p₁ q₃).f.f n) :=
  ((repShortComplex_shortExact hS p₁ q₃).map_of_exact
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).mono_f

omit [P₃.IsKProjective] [∀ n, Projective (P₃.X n)] in
/-- A morphism between zero complexes is a quasi-isomorphism. -/
lemma quasiIso_of_isZero {K L : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : K ⟶ L)
    (hK : IsZero K) (hL : IsZero L) : QuasiIso f := by
  have := isIso_of_source_target_iso_zero f hK.isoZero hL.isoZero
  infer_instance

variable [∀ n, Mono (S.f.f n)]

/-- The comparison is a **filtered quasi-isomorphism** of the two-step filtered complexes. -/
lemma filteredQuasiIsoC_twoStepComplexMap_repMap [QuasiIso q₃] :
    filteredQuasiIsoC (twoStepComplexMap (repMap hS p₁ q₃)) := by
  intro p
  by_cases hp1 : p = 1
  · subst hp1
    have h := twoStepComplexGrOneIso_hom_naturality (repShortComplex hS p₁ q₃) (repMap hS p₁ q₃)
    rw [repMap_τ₁] at h
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (twoStepComplexGrOneIso (repShortComplex hS p₁ q₃))
        (twoStepComplexGrOneIso S) h.symm)).2 (inferInstanceAs (QuasiIso p₁))
  by_cases hp0 : p = 0
  · subst hp0
    have h := twoStepComplexGrZeroIso_hom_naturality (repShortComplex hS p₁ q₃)
      (repShortComplex_shortExact hS p₁ q₃) hS (repMap hS p₁ q₃)
    rw [repMap_τ₃] at h
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (twoStepComplexGrZeroIso _ (repShortComplex_shortExact hS p₁ q₃))
        (twoStepComplexGrZeroIso S hS) h.symm)).2 (inferInstanceAs (QuasiIso (repτ₃ q₃)))
  · exact quasiIso_of_isZero _ (isZero_twoStepComplex_grP _ hp0 hp1)
      (isZero_twoStepComplex_grP S hp0 hp1)

end Representative

/-! ### Boundedness and finite projectivity of the representative -/

section Bounds

open CochainComplex

variable {R : Type u} [Ring R]

/-- The two-step filtered object of `S` in degree `i` is zero when `X₂` is zero in degree `i`. -/
lemma isZero_twoStepX (S : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ))
    [∀ n, Mono (S.f.f n)] (i : ℤ) (h : IsZero (S.X₂.X i)) : IsZero (twoStepX S i) := by
  rw [IsZero.iff_id_eq_zero]
  ext1
  exact FilteredObject.hom_ext (h.eq_of_src _ _)

/-- The two-step filtered complex of `S` is bounded when `X₂` vanishes outside `[a, b]`. -/
lemma twoStepComplex_bounded (S : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ))
    [∀ n, Mono (S.f.f n)] (a b : ℤ) (ha : ∀ i < a, IsZero (S.X₂.X i))
    (hb : ∀ i > b, IsZero (S.X₂.X i)) :
    CochainComplex.plus _ (twoStepComplex S) ∧ CochainComplex.minus _ (twoStepComplex S) :=
  ⟨⟨a, (isStrictlyGE_iff _ _).2 fun i hi => isZero_twoStepX S i (ha i hi)⟩,
    ⟨b, (isStrictlyLE_iff _ _).2 fun i hi => isZero_twoStepX S i (hb i hi)⟩⟩

end Bounds

/-! ### Additivity -/

section Additivity

open CochainComplex Stacks.EtaleCohomology

variable (R : Type u) [Ring R]

/-- The image of `Qh(X)` under the functor `DF ⥤ D` induced by an additive functor
`G : Fil^f ⥤ 𝒜` is `Q(G(X))`, naturally in the complex of finite filtered objects `X`. -/
def liftDFQIso (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive] (hG : (HomotopyCategory.filteredQuasiIso _).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)) :
    HomotopyCategory.quotient _ _ ⋙ FilteredDerivedCategory.Qh ⋙
        FilteredDerivedCategory.liftDF G hG ≅
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft _ (Localization.fac _ hG FilteredDerivedCategory.Qh) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)

/-- The component of `liftDFQIso` at a complex `X`. -/
def liftDFQIsoApp (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive] (hG : (HomotopyCategory.filteredQuasiIso _).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh))
    (X : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ) :
    (FilteredDerivedCategory.liftDF G hG).obj
        (FilteredDerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj X)) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
  (liftDFQIso R G hG).app X

/-- Naturality of `liftDFQIsoApp`. -/
lemma liftDFQIsoApp_naturality
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive] (hG : (HomotopyCategory.filteredQuasiIso _).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh))
    {X Y : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ} (x : X ⟶ Y) :
    (FilteredDerivedCategory.liftDF G hG).map
        (FilteredDerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map x)) ≫
      (liftDFQIsoApp R G hG Y).hom =
    (liftDFQIsoApp R G hG X).hom ≫
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map x) :=
  (liftDFQIso R G hG).hom.naturality x

variable {R}

/-- A complex quasi-isomorphic to a perfect one admits a bounded finite projective resolution. -/
lemma exists_finiteProjective_quasiIso {X : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (h : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj X)) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (_ : finiteProjectiveComplex R P)
      (p : P ⟶ X), QuasiIso p := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff R _).mp h
  have := isKProjective_of_finiteProjectiveComplex R hP
  obtain ⟨p, hp⟩ := exists_map_eq_of_isKProjective P X e.hom
  refine ⟨P, hP, p, ?_⟩
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hp]
  infer_instance

section Data

variable {S : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ)} (hS : S.ShortExact)
  [∀ n, Mono (S.f.f n)] {P₁ P₃ : CochainComplex (ModuleCat.{max u v} R) ℤ}
  (hP₁ : finiteProjectiveComplex R P₁) (hP₃ : finiteProjectiveComplex R P₃)
  [P₃.IsKProjective] [∀ n, Projective (P₃.X n)]
  (p₁ : P₁ ⟶ S.X₁) [QuasiIso p₁] (q₃ : P₃ ⟶ S.X₃) [QuasiIso q₃]

omit [∀ n, Mono (S.f.f n)] [QuasiIso q₃] in
include hP₁ hP₃ in
/-- The two-step filtered complex of the mapping-cone sequence is bounded. -/
lemma repShortComplex_bounded :
    CochainComplex.plus _ (twoStepComplex (repShortComplex hS p₁ q₃)) ∧
      CochainComplex.minus _ (twoStepComplex (repShortComplex hS p₁ q₃)) := by
  obtain ⟨⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩⟩, -⟩ := hP₁
  obtain ⟨⟨⟨a₃, ha₃⟩, ⟨b₃, hb₃⟩⟩, -⟩ := hP₃
  refine twoStepComplex_bounded _ (min a₁ a₃) (max b₁ b₃) (fun i hi => ?_) (fun i hi => ?_)
  · exact (mappingCone.isZero_X_iff _ i).2
      ⟨CochainComplex.isZero_of_isStrictlyGE P₃ a₃ (i + 1 + -1) (by omega),
        CochainComplex.isZero_of_isStrictlyGE P₁ a₁ i (by omega)⟩
  · exact (mappingCone.isZero_X_iff _ i).2
      ⟨CochainComplex.isZero_of_isStrictlyLE P₃ b₃ (i + 1 + -1) (by omega),
        CochainComplex.isZero_of_isStrictlyLE P₁ b₁ i (by omega)⟩

omit [∀ n, Mono (S.f.f n)] [QuasiIso q₃] in
include hP₁ hP₃ in
/-- The two-step filtered complex of the mapping-cone sequence is filtered finite projective in
each degree. -/
lemma repShortComplex_finiteProjective (i : ℤ) :
    IsFilteredFiniteProjective ((twoStepComplex (repShortComplex hS p₁ q₃)).X i) := by
  intro p
  by_cases hp1 : p = 1
  · subst hp1
    have := (hP₁.2 i).1
    exact GradedWitness.finiteProjective_of_iso.{u, v} R
      (FilteredObject.twoStepGrOneIso _).symm
      ⟨(hP₁.2 i).2, inferInstanceAs (Projective (P₁.X i))⟩
  by_cases hp0 : p = 0
  · subst hp0
    have := (hP₃.2 (i + 1 + -1)).1
    exact GradedWitness.finiteProjective_of_iso.{u, v} R
      (FilteredObject.twoStepGrZeroIso _
        (degreeShortComplex_shortExact _ (repShortComplex_shortExact hS p₁ q₃) i)).symm
      ⟨(hP₃.2 (i + 1 + -1)).2, inferInstanceAs (Projective (P₃.X (i + 1 + -1)))⟩
  · refine GradedWitness.finiteProjective_of_isZero.{u, v} R ?_
    rcases lt_or_gt_of_ne hp0 with h | h
    · exact FilteredObject.isZero_gr_twoStep_of_neg _ h
    · exact FilteredObject.isZero_gr_twoStep_of_two_le _ (by omega)

/-- The comparison morphism becomes an isomorphism in the filtered derived category. -/
lemma isIso_Qh_map_repMap :
    IsIso (FilteredDerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      (twoStepComplexMap (repMap hS p₁ q₃)))) := by
  have hf : HomotopyCategory.filteredQuasiIso (ModuleCat.{max u v} R)
      ((HomotopyCategory.quotient _ _).map (twoStepComplexMap (repMap hS p₁ q₃))) :=
    (filteredQuasiIso_quotient_map_iff _).2 (filteredQuasiIsoC_twoStepComplexMap_repMap hS p₁ q₃)
  exact Localization.inverts _ _ _ hf

/-- **The filtered perfect complex** attached to a short exact sequence with perfect ends: the
two-step filtered complex of `S` in `DF(R)`, with the representative built from the mapping
cone. -/
def repFilteredPerfectData : FilteredPerfectData.{u, v} R where
  obj := FilteredDerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (twoStepComplex S))
  representative := twoStepComplex (repShortComplex hS p₁ q₃)
  bounded := repShortComplex_bounded hS hP₁ hP₃ p₁ q₃
  finiteProjective := repShortComplex_finiteProjective hS hP₁ hP₃ p₁ q₃
  iso := ⟨haveI := isIso_Qh_map_repMap hS p₁ q₃
    asIso (FilteredDerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      (twoStepComplexMap (repMap hS p₁ q₃))))⟩

end Data

section Main

variable {S : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ)}

/-- The comparison `G(Qh X) ≅ Q(Y)` intertwining the image of an endomorphism `x` of a complex
of finite filtered objects `X` with an endomorphism `y` of `Y`, given an isomorphism
`G(X) ≅ Y` intertwining `G(x)` and `y`. -/
lemma liftDF_map_comm (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive] (hG : (HomotopyCategory.filteredQuasiIso _).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh))
    {X : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ} (x : X ⟶ X)
    {Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (y : Y ⟶ Y)
    (e : (G.mapHomologicalComplex _).obj X ≅ Y)
    (he : (G.mapHomologicalComplex _).map x ≫ e.hom = e.hom ≫ y) :
    (FilteredDerivedCategory.liftDF G hG).map
        (FilteredDerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map x)) ≫
      (liftDFQIsoApp R G hG X ≪≫ DerivedCategory.Q.mapIso e).hom =
    (liftDFQIsoApp R G hG X ≪≫ DerivedCategory.Q.mapIso e).hom ≫ DerivedCategory.Q.map y := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [reassoc_of% liftDFQIsoApp_naturality R G hG x, ← Functor.map_comp, he, Functor.map_comp,
    Category.assoc]

/-- The trace of the image under `G : DF ⥤ D` of an endomorphism `Qh(x)` of `Qh(X)` is the
trace of `y` on `Q(Y)`, for an isomorphism `G(X) ≅ Y` intertwining `G(x)` and `y`. -/
lemma perfectDerivedTrace_liftDF_eq
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive] (hG : (HomotopyCategory.filteredQuasiIso _).IsInvertedBy
      (G.mapHomotopyCategory _ ⋙ DerivedCategory.Qh))
    {X : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ} (x : X ⟶ X)
    {Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (y : Y ⟶ Y)
    (e : (G.mapHomologicalComplex _).obj X ≅ Y)
    (he : (G.mapHomologicalComplex _).map x ≫ e.hom = e.hom ≫ y)
    (hX : StacksDraft.Perfect.IsPerfect ((FilteredDerivedCategory.liftDF G hG).obj
      (FilteredDerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj X))))
    (hY : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Y)) :
    perfectDerivedTrace R ⟨_, hX⟩ ((FilteredDerivedCategory.liftDF G hG).map
        (FilteredDerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map x))) =
      perfectDerivedTrace R ⟨_, hY⟩ (DerivedCategory.Q.map y) :=
  perfectDerivedTrace_congr R _ _ _ _ _ (liftDF_map_comm G hG x y e he)

/-- A short exact sequence with perfect ends has finite projective resolutions of the ends, with
the first map monomorphic in each degree and the resolution of `X₃` K-projective. -/
private lemma exists_representatives (hS : S.ShortExact)
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₁))
    (h₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₃)) :
    ∃ (P₁ P₃ : CochainComplex (ModuleCat.{max u v} R) ℤ) (_ : finiteProjectiveComplex R P₁)
      (_ : finiteProjectiveComplex R P₃) (p₁ : P₁ ⟶ S.X₁) (q₃ : P₃ ⟶ S.X₃),
      QuasiIso p₁ ∧ QuasiIso q₃ ∧ (∀ n, Mono (S.f.f n)) ∧ P₃.IsKProjective ∧
        ∀ n, Projective (P₃.X n) := by
  obtain ⟨P₁, hP₁, p₁, hp₁⟩ := exists_finiteProjective_quasiIso h₁
  obtain ⟨P₃, hP₃, q₃, hq₃⟩ := exists_finiteProjective_quasiIso h₃
  exact ⟨P₁, P₃, hP₁, hP₃, p₁, q₃, hp₁, hq₃,
    fun n => (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).mono_f,
    isKProjective_of_finiteProjectiveComplex R hP₃, fun n => by
      have := (hP₃.2 n).1
      infer_instance⟩

/-- **Additivity along a two-step filtration, abstractly.** Let `F` be a filtered perfect complex
whose underlying object is `Qh(X)` for a complex of finite filtered modules `X`, and `x` an
endomorphism of `X`. Given identifications of the underlying complex of `X` and of its graded
pieces in indices `1` and `0` with complexes `Y₂`, `Y₁`, `Y₀` intertwining `x` with `y₂`, `y₁`,
`y₀`, and vanishing of the other graded pieces, `Tr(y₂) = Tr(y₁) + Tr(y₀)`. -/
@[sga "5 IIIB 5.6" "special case"]
lemma perfectDerivedTrace_eq_add_of_twoStep
    {X : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ}
    (F : FilteredPerfectData.{u, v} R)
    (hF : F.obj = FilteredDerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj X))
    (x : X ⟶ X) {Y₂ Y₁ Y₀ : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (y₂ : Y₂ ⟶ Y₂) (y₁ : Y₁ ⟶ Y₁) (y₀ : Y₀ ⟶ Y₀)
    (e₂ : (FiniteFilteredObject.forget.mapHomologicalComplex _).obj X ≅ Y₂)
    (he₂ : (FiniteFilteredObject.forget.mapHomologicalComplex _).map x ≫ e₂.hom = e₂.hom ≫ y₂)
    (e₁ : ((FiniteFilteredObject.grP 1).mapHomologicalComplex _).obj X ≅ Y₁)
    (he₁ : ((FiniteFilteredObject.grP 1).mapHomologicalComplex _).map x ≫ e₁.hom = e₁.hom ≫ y₁)
    (e₀ : ((FiniteFilteredObject.grP 0).mapHomologicalComplex _).obj X ≅ Y₀)
    (he₀ : ((FiniteFilteredObject.grP 0).mapHomologicalComplex _).map x ≫ e₀.hom = e₀.hom ≫ y₀)
    (hz : ∀ p : ℤ, p ≠ 0 → p ≠ 1 →
      IsZero (((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj X))
    (h₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Y₂))
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Y₁))
    (h₀ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Y₀)) :
    perfectDerivedTrace R ⟨_, h₂⟩ (DerivedCategory.Q.map y₂) =
      perfectDerivedTrace R ⟨_, h₁⟩ (DerivedCategory.Q.map y₁) +
        perfectDerivedTrace R ⟨_, h₀⟩ (DerivedCategory.Q.map y₀) := by
  obtain ⟨obj, representative, bounded, finiteProjective, iso⟩ := F
  subst hF
  let F : FilteredPerfectData.{u, v} R := ⟨_, representative, bounded, finiteProjective, iso⟩
  let f : F.obj ⟶ F.obj :=
    FilteredDerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map x)
  have key := perfectDerivedTrace_eq_sum_grDF.{u, v} R F f
  have hL := perfectDerivedTrace_liftDF_eq.{u, v} FiniteFilteredObject.forget
    FilteredDerivedCategory.forget_inverts x y₂ e₂ he₂ (F.forgetPerfect R) h₂
  have k1 := perfectDerivedTrace_liftDF_eq.{u, v} (FiniteFilteredObject.grP 1)
    (FilteredDerivedCategory.grP_inverts 1)
    x y₁ e₁ he₁ (F.gradedPerfect R 1) h₁
  have k0 := perfectDerivedTrace_liftDF_eq.{u, v} (FiniteFilteredObject.grP 0)
    (FilteredDerivedCategory.grP_inverts 0)
    x y₀ e₀ he₀ (F.gradedPerfect R 0) h₀
  have kz : ∀ p : ℤ, p ≠ 0 → p ≠ 1 → perfectDerivedTrace R ⟨_, F.gradedPerfect R p⟩
      ((CochainComplex.FilteredDerivedCategory.grDF p).map f) = 0 := fun p hp0 hp1 =>
    perfectDerivedTrace_eq_zero_of_isZero R _
      ((DerivedCategory.Q.map_isZero (hz p hp0 hp1)).of_iso
        (liftDFQIsoApp.{u, v} R (FiniteFilteredObject.grP p) (FilteredDerivedCategory.grP_inverts p)
          X)) _
  rw [← hL, key, finsum_eq_sum_of_support_subset (s := {0, 1}), Finset.sum_pair (by norm_num),
    ← k1, ← k0, add_comm]
  intro p hp
  by_contra hmem
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hmem
  exact hp (kz p hmem.1 hmem.2)

/-- **Additivity of the trace along a short exact sequence** (Step 1 of [Stacks, Tag 03UG],
from [Stacks, Tag 03TK]). For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of complexes of
`R`-modules whose terms are perfect and an endomorphism `φ` of it,
`Tr(φ | X₂) = Tr(φ | X₁) + Tr(φ | X₃)`. -/
theorem perfectDerivedTrace_X₂_eq_add (hS : S.ShortExact) (φ : S ⟶ S)
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₁))
    (h₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₂))
    (h₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₃)) :
    perfectDerivedTrace R ⟨_, h₂⟩ (DerivedCategory.Q.map φ.τ₂) =
      perfectDerivedTrace R ⟨_, h₁⟩ (DerivedCategory.Q.map φ.τ₁) +
        perfectDerivedTrace R ⟨_, h₃⟩ (DerivedCategory.Q.map φ.τ₃) := by
  obtain ⟨P₁, P₃, hP₁, hP₃, p₁, q₃, hp₁, hq₃, _, _, _⟩ := exists_representatives hS h₁ h₃
  exact perfectDerivedTrace_eq_add_of_twoStep.{u, v} (repFilteredPerfectData hS hP₁ hP₃ p₁ q₃) rfl
    (twoStepComplexMap φ) φ.τ₂ φ.τ₁ φ.τ₃
    (twoStepComplexForgetIso S) (twoStepComplexForgetIso_hom_naturality S φ)
    (twoStepComplexGrOneIso S) (twoStepComplexGrOneIso_hom_naturality S φ)
    (twoStepComplexGrZeroIso S hS) (twoStepComplexGrZeroIso_hom_naturality S hS hS φ)
    (fun _ hp0 hp1 => isZero_twoStepComplex_grP S hp0 hp1) h₂ h₁ h₃

/-- **The middle term of a short exact sequence with perfect ends is perfect.** -/
theorem isPerfect_X₂_of_shortExact (hS : S.ShortExact)
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₁))
    (h₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₃)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj S.X₂) := by
  obtain ⟨P₁, P₃, hP₁, hP₃, p₁, q₃, hp₁, hq₃, _, _, _⟩ := exists_representatives hS h₁ h₃
  exact StacksDraft.Perfect.isPerfect_of_iso
    (liftDFQIsoApp.{u, v} R FiniteFilteredObject.forget FilteredDerivedCategory.forget_inverts
      (twoStepComplex S) ≪≫ DerivedCategory.Q.mapIso (twoStepComplexForgetIso S)).symm
    ((repFilteredPerfectData.{u, v} hS hP₁ hP₃ p₁ q₃).forgetPerfect R)

end Main

end Additivity

end CategoryTheory.FilteredDerived
