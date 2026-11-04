module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.TermwiseSplit
public import StacksFrontier.Homology.Injectives.FilteredComplex.MappingCone
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms into a bounded below complex of filtered injective objects

Let `𝒜` be an abelian category, `Filf` the class of filtered cochain complexes whose filtration is
finite in each degree — so that `Filf.FullSubcategory` is `K(Fil^f(𝒜))` — and `Q` a localisation of
it at the filtered quasi-isomorphisms, i.e. the filtered derived category `DF(𝒜)`. For a bounded
below `I^•` consisting of filtered injective objects, precomposition with a filtered
quasi-isomorphism is bijective on filtered homotopy classes of morphisms into `I^•`, and
`Hom_{K(Fil^f(𝒜))}(-, I^•)` already computes `Hom_{DF(𝒜)}(-, I^•)`.

Part (1) is the mapping cone argument. The cone `C(α)^•` of a filtered quasi-isomorphism, filtered
by the cones of the steps of `α` (`coneFiltered`), is filtered acyclic, so
`Hom_{K(Fil^f(𝒜))}(C(α)^•, I^•)` and `Hom_{K(Fil^f(𝒜))}(C(α)^•[-1], I^•)` both vanish by
`CochainComplex.exists_homotopy_zero_of_filteredAcyclic_of_injective_gradedPiece`, which is the
surjectivity and the injectivity half respectively. Part (2) is part (1) read in the localisation:
the `←` direction of its last clause is the cylinder of a filtered complex, whose projection is a
filtered quasi-isomorphism with two sections, and the rest is part (1) together with the
description of the morphisms of a localisation as paths in the quiver of the category and the
formal inverses.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredInjectiveHom

universe v' u'

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject CochainComplex

namespace CochainComplex.FilteredInjective.Hom

open CochainComplex.FilteredInjective.Degreewise
open CochainComplex.FilteredInjective.TermwiseSplit (biprod_map_comp_map)

/-! ### Filtered components and filtered homotopies -/

/-- A homotopy between morphisms of the underlying complexes of two filtered complexes is a
*filtered homotopy* if all its components are filtered, i.e. if it is a homotopy in the category
of complexes of filtered objects. -/
private def IsFilteredHomotopy {K I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    {f g : K.X ⟶ I.X} (h : Homotopy f g) : Prop :=
  ∀ i j : ℤ, IsFilteredComponent K I i j (h.hom i j)

/-! ### Two tools of homological algebra -/

/-- A short complex whose identity is a sum of endomorphisms factoring through exact short
complexes is exact. This is how exactness of a short complex of biproducts is deduced from
exactness of its two summands: `𝟙` acts as zero on homology. -/
private lemma exact_of_id_eq_add {S T U : ShortComplex 𝒜} (hT : T.Exact) (hU : U.Exact)
    (a : T ⟶ S) (b : S ⟶ T) (c : U ⟶ S) (d : S ⟶ U) (hid : b ≫ a + d ≫ c = 𝟙 S) :
    S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology] at hT hU ⊢
  rw [IsZero.iff_id_eq_zero]
  have h1 : ShortComplex.homologyMap b = 0 := hT.eq_of_tgt _ _
  have h2 : ShortComplex.homologyMap d = 0 := hU.eq_of_tgt _ _
  calc 𝟙 S.homology = ShortComplex.homologyMap (𝟙 S) := (ShortComplex.homologyMap_id S).symm
    _ = ShortComplex.homologyMap (b ≫ a) + ShortComplex.homologyMap (d ≫ c) := by
        rw [← hid, ShortComplex.homologyMap_add]
    _ = 0 := by rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp, h1, h2]; simp

/-- The mapping cone of a quasi-isomorphism is acyclic: it is the third object of the
distinguished triangle of `φ` in the homotopy category, and the acyclic complexes are the
triangulated subcategory whose associated class of morphisms is the quasi-isomorphisms. -/
@[sga "6 I 1.4.2" "(ii) ⇒ (i), special case"]
private lemma acyclic_mappingCone {A B : CochainComplex 𝒜 ℤ} (φ : A ⟶ B) (h : QuasiIso φ) :
    (mappingCone φ).Acyclic := by
  have h1 : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map φ) := by
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at h1
  have h2 := (ObjectProperty.trW_iff_of_distinguished _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)).1 h1
  rwa [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]

/-! ### Mapping cones of morphisms of filtered complexes -/

/-- A filtration on `X` built from a diagram over `X` all of whose structure maps are
monomorphisms; the inverse construction to `CategoryTheory.Filtration.diagram` together with
`CategoryTheory.Filtration.ι`. -/
private def filtrationOfDiagram {C : Type u} [Category.{v} C] {Y : C} {J : Type*} [Category J]
    (D : J ⥤ C) (η : D ⟶ (Functor.const J).obj Y) [∀ i, Mono (η.app i)] : Filtration Y J where
  toMonoOver :=
    { obj i := MonoOver.mk (η.app i)
      map {i j} f := MonoOver.homMk (D.map f) (by simp)
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }

section MappingConeMap

variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- A morphism of mapping cones induced by a square whose vertical maps are isomorphisms in the
relevant degrees is an isomorphism in that degree. -/
private lemma isIso_map_f (n : ℤ) (ha : IsIso (a.f (n + 1))) (hb : IsIso (b.f n)) :
    IsIso ((mappingCone.map φ₁ φ₂ a b comm).f n) := by
  have := ha
  have := hb
  have := mappingCone.mono_map_f φ₁ φ₂ a b comm n inferInstance inferInstance
  have := mappingCone.epi_map_f φ₁ φ₂ a b comm n inferInstance inferInstance
  exact isIso_of_mono_of_epi _

/-- A composition of two morphisms of mapping cones vanishes as soon as both squares' vertical
maps compose to zero. -/
private lemma map_comp_map_eq_zero {K₃ L₃ : CochainComplex 𝒜 ℤ} (φ₃ : K₃ ⟶ L₃)
    (a₂ : K₂ ⟶ K₃) (b₂ : L₂ ⟶ L₃) (comm₂ : φ₂ ≫ b₂ = a₂ ≫ φ₃)
    (ha : a ≫ a₂ = 0) (hb : b ≫ b₂ = 0) :
    mappingCone.map φ₁ φ₂ a b comm ≫ mappingCone.map φ₂ φ₃ a₂ b₂ comm₂ = 0 := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    mappingCone.ext_from_iff _ (n + 1) n rfl]
  refine ⟨?_, ?_⟩
  · rw [comp_zero, ← Category.assoc, mappingCone.inl_v_map_f, Category.assoc,
      mappingCone.inl_v_map_f, ← Category.assoc, ← HomologicalComplex.comp_f, ha]
    simp
  · rw [comp_zero, ← Category.assoc, mappingCone.inr_f_map_f, Category.assoc,
      mappingCone.inr_f_map_f, ← Category.assoc, ← HomologicalComplex.comp_f, hb]
    simp

/-- A morphism of mapping cones is compatible with the projections `C(φ)^• ⟶ K^•[1]` of the
standard triangles. -/
private lemma map_comp_mor₃ :
    mappingCone.map φ₁ φ₂ a b comm ≫ (mappingCone.triangle φ₂).mor₃
      = (mappingCone.triangle φ₁).mor₃ ≫
        (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (1 : ℤ)).map a := by
  rw [mappingCone.map_eq_mapOfHomotopy, mappingCone.triangleMapOfHomotopy_comm₃]

end MappingConeMap

/-! ### Descending along the shifted projection of a mapping cone

The surjectivity half rests on the following purely homological computation: a null homotopy of the
composition `C(φ)^• ⟶ A^•[1] ⟶ T^•[1]` of the projection of the standard triangle of `φ` with the
shift of `g : A^• ⟶ T^•` is the same thing as a factorisation of `g` through `φ` up to homotopy.
Indeed such a null homotopy is a degree `-1` cochain `C(φ)^• ⟶ T^•[1]`, i.e. a degree `0` cochain
`u : C(φ)^• ⟶ T^•`, whose `δ` is the projection cocycle; restricting `u` along
`inr : B^• ⟶ C(φ)^•` gives a `0`-cocycle, i.e. a morphism `B^• ⟶ T^•`, and restricting it along
`inl : A^• ⟶ C(φ)^•` gives the homotopy. -/

section ConeShift

open HomComplex

variable {A B T : CochainComplex 𝒜 ℤ} (φ : A ⟶ B) (g : A ⟶ T)

/-- The projection `C(φ)^• ⟶ A^•[1]` of the standard triangle of `φ`. -/
private noncomputable def coneProj :
    mappingCone φ ⟶ (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (1 : ℤ)).obj A :=
  (mappingCone.triangle φ).mor₃

/-- A morphism of mapping cones is compatible with the projections onto the shifts. -/
private lemma map_comp_coneProj {A' B' : CochainComplex 𝒜 ℤ} (φ' : A' ⟶ B') (a : A ⟶ A')
    (b : B ⟶ B') (comm : φ ≫ b = a ≫ φ') :
    mappingCone.map φ φ' a b comm ≫ coneProj φ'
      = coneProj φ ≫ (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (1 : ℤ)).map a :=
  map_comp_mor₃ φ φ' a b comm

/-- The composition `C(φ)^• ⟶ A^•[1] ⟶ T^•[1]` of the projection of the standard triangle of `φ`
with the shift of `g`. -/
private noncomputable def coneShiftHom :
    mappingCone φ ⟶ (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (1 : ℤ)).obj T :=
  coneProj φ ≫ (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (1 : ℤ)).map g

/-- Read as a degree `1` cochain `C(φ)^• ⟶ T^•`, the morphism `C(φ)^• ⟶ T^•[1]` is minus the
composition of the projection cocycle of the cone with `g`. -/
private lemma ofHom_coneShiftHom_rightUnshift :
    (Cochain.ofHom (coneShiftHom φ g)).rightUnshift 1 (by omega)
      = -((mappingCone.fst φ).1.comp (Cochain.ofHom g) (add_zero 1)) := by
  ext p q hpq
  subst hpq
  rw [Cochain.rightUnshift_v _ 1 (by omega) p (p + 1) rfl p (add_zero p)]
  simp [coneShiftHom, coneProj, mappingCone.triangle,
    Cochain.rightShift_v _ 1 0 (zero_add 1) p p (add_zero p) (p + 1) rfl]

/-- The degree `0` cochain `C(φ)^• ⟶ T^•` attached to a null homotopy of `C(φ)^• ⟶ T^•[1]`: a
homotopy is a degree `-1` cochain with values in the shift, which is the same thing as a degree
`0` cochain with values in `T^•`. -/
private noncomputable def unshiftCochain (h : Homotopy (coneShiftHom φ g) 0) :
    Cochain (mappingCone φ) T 0 :=
  -((Cochain.ofHomotopy h).rightUnshift 0 (by omega))

private lemma unshiftCochain_v (h : Homotopy (coneShiftHom φ g) 0) (n : ℤ) :
    (unshiftCochain φ g h).v n n (add_zero n)
      = -(h.hom n (n - 1) ≫ (T.XIsoOfEq (show n - 1 + 1 = n by omega)).hom) := by
  rw [unshiftCochain, Cochain.neg_v,
    Cochain.rightUnshift_v _ 0 (by omega) n n (add_zero n) (n - 1) (by omega)]
  rfl

/-- The `δ` of the cochain of a null homotopy is the projection cocycle of the cone composed with
`g`; this single identity carries both the fact that the descended morphism is a morphism of
complexes and the homotopy identity. -/
private lemma δ_unshiftCochain (h : Homotopy (coneShiftHom φ g) 0) :
    δ 0 1 (unshiftCochain φ g h)
      = -((mappingCone.fst φ).1.comp (Cochain.ofHom g) (add_zero 1)) := by
  rw [unshiftCochain, δ_neg, Cochain.δ_rightUnshift _ 0 (by omega) 1 0 (by omega),
    δ_ofHomotopy]
  simp [ofHom_coneShiftHom_rightUnshift]

/-- **The morphism `B^• ⟶ T^•` descended from a null homotopy.** It is the restriction of the
degree `0` cochain of the homotopy along `inr : B^• ⟶ C(φ)^•`, a cocycle because `inr` kills the
projection cocycle of the cone. -/
private noncomputable def descShiftHom (h : Homotopy (coneShiftHom φ g) 0) : B ⟶ T :=
  Cocycle.homOf (Cocycle.mk
    ((Cochain.ofHom (mappingCone.inr φ)).comp (unshiftCochain φ g h) (zero_add 0)) 1
    (zero_add 1) (by
      rw [δ_ofHom_comp, δ_unshiftCochain, Cochain.comp_neg,
        ← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
      simp))

private lemma descShiftHom_f (h : Homotopy (coneShiftHom φ g) 0) (n : ℤ) :
    (descShiftHom φ g h).f n
      = (mappingCone.inr φ).f n ≫ (unshiftCochain φ g h).v n n (add_zero n) := by
  simp [descShiftHom]

private lemma ofHom_descShiftHom (h : Homotopy (coneShiftHom φ g) 0) :
    Cochain.ofHom (descShiftHom φ g h)
    = (Cochain.ofHom (mappingCone.inr φ)).comp (unshiftCochain φ g h) (zero_add 0) := by
  simp [descShiftHom]

/-- **The homotopy from `φ ≫ descShiftHom` to `g`.** It is the restriction of the degree `0`
cochain of the null homotopy along `inl : A^• ⟶ C(φ)^•`; the homotopy identity is
`δ (inl ≫ u) = (δ inl) ≫ u - inl ≫ (fst ≫ g)`, whose two terms are `φ ≫ descShiftHom` and `g`. -/
private noncomputable def descShiftHomotopy (h : Homotopy (coneShiftHom φ g) 0) :
    Homotopy (φ ≫ descShiftHom φ g h) g :=
  (Cochain.equivHomotopy _ _).symm
    ⟨(mappingCone.inl φ).comp (unshiftCochain φ g h) (add_zero (-1)), by
      rw [δ_comp_zero_cochain _ _ 0 (by omega), δ_unshiftCochain, mappingCone.δ_inl,
        Cochain.comp_neg]
      have h1 : (mappingCone.inl φ).comp
            ((mappingCone.fst φ).1.comp (Cochain.ofHom g) (add_zero 1)) (by omega)
          = Cochain.ofHom g := by
        rw [← Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ (neg_add_cancel 1),
          mappingCone.inl_fst, ← Cochain.ofHom_comp, Category.id_comp]
      have h2 : (Cochain.ofHom (φ ≫ mappingCone.inr φ)).comp
            (unshiftCochain φ g h) (zero_add 0)
          = Cochain.ofHom (φ ≫ descShiftHom φ g h) := by
        rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
          ← ofHom_descShiftHom, ← Cochain.ofHom_comp]
      rw [h1, h2]
      abel⟩

private lemma descShiftHomotopy_hom (h : Homotopy (coneShiftHom φ g) 0) (j : ℤ) :
    (descShiftHomotopy φ g h).hom (j + 1) j
      = (mappingCone.inl φ).v (j + 1) j (by omega) ≫
        (unshiftCochain φ g h).v j j (add_zero j) := by
  rw [descShiftHomotopy, Cochain.equivHomotopy_symm_apply_hom,
    dite_eq_left (show j + 1 + (-1) = j by omega),
    Cochain.comp_v _ _ (add_zero (-1)) (j + 1) j j (by omega) (add_zero j)]

end ConeShift

section FilteredCone

variable {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}

/-- The diagram `p ↦ C(F^p α)^•` of mapping cones of the steps of `α`. -/
private noncomputable def coneDiagram (α : K ⟶ L) : ℤᵒᵖ ⥤ CochainComplex 𝒜 ℤ where
  obj p := mappingCone (α.natTrans.app p)
  map {p q} f := mappingCone.map (α.natTrans.app p) (α.natTrans.app q)
    (K.filtration.step f) (L.filtration.step f) (step_natTrans_app α f).symm
  map_id p := by
    refine Eq.trans ?_ (mappingCone.map_id (α.natTrans.app p))
    congr 1 <;> simp
  map_comp {p q r} f g := by
    refine Eq.trans ?_ (mappingCone.map_comp (α.natTrans.app p) (α.natTrans.app q)
      (α.natTrans.app r) (K.filtration.step f) (L.filtration.step f)
      (step_natTrans_app α f).symm (K.filtration.step g) (L.filtration.step g)
      (step_natTrans_app α g).symm)
    congr 1 <;> simp

/-- The transformation `C(F^p α)^• ⟶ C(α)^•`. -/
private noncomputable def coneι (α : K ⟶ L) :
    coneDiagram α ⟶ (Functor.const ℤᵒᵖ).obj (mappingCone α.hom) where
  app p := mappingCone.map (α.natTrans.app p) α.hom (K.filtration.ι.app p) (L.filtration.ι.app p)
    (α.comm p)
  naturality {p q} f := by
    dsimp [coneDiagram]
    rw [Category.comp_id, ← mappingCone.map_comp]
    congr 1
    all_goals simp

private instance mono_coneι_app (α : K ⟶ L) (p : ℤᵒᵖ) : Mono ((coneι α).app p) :=
  HomologicalComplex.mono_of_mono_f _ fun n => mappingCone.mono_map_f (α.natTrans.app p) α.hom
    (K.filtration.ι.app p) (L.filtration.ι.app p) (α.comm p) n inferInstance inferInstance

/-- The mapping cone `C(α)^•` of a morphism of filtered complexes, filtered by the mapping cones
`C(F^p α)^•` of the steps of `α`. This is the object `C(α)^•` of `K(Fil(𝒜))` of the source. -/
private noncomputable def coneFiltered (α : K ⟶ L) :
    FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  X := mappingCone α.hom
  filtration := filtrationOfDiagram (coneDiagram α) (coneι α)

private lemma coneFiltered_X (α : K ⟶ L) : (coneFiltered α).X = mappingCone α.hom := rfl

private lemma coneFiltered_fil_obj (α : K ⟶ L) (p : ℤᵒᵖ) :
    (coneFiltered α).filtration.obj p = mappingCone (α.natTrans.app p) := rfl

private lemma coneFiltered_ι_app (α : K ⟶ L) (p : ℤᵒᵖ) :
    (coneFiltered α).filtration.ι.app p = mappingCone.map (α.natTrans.app p) α.hom
      (K.filtration.ι.app p) (L.filtration.ι.app p) (α.comm p) := rfl

/-- If the filtration of `X^•` vanishes in degree `n` at some step, it vanishes in degree `n` at
every later step. -/
private lemma isZero_fil_X_of_le (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) {p q n : ℤ}
    (hpq : p ≤ q) (hp : IsZero ((X.filtration.obj (op p)).X n)) :
    IsZero ((X.filtration.obj (op q)).X n) := by
  have hmono' : Mono ((X.filtration.diagram.map (homOfLE hpq : p ⟶ q).op).f n) := inferInstance
  have hepi : Epi ((X.filtration.diagram.map (homOfLE hpq : p ⟶ q).op).f n) :=
    ⟨fun g₁ g₂ _ => hp.eq_of_src g₁ g₂⟩
  have : IsIso ((X.filtration.diagram.map (homOfLE hpq : p ⟶ q).op).f n) :=
    isIso_of_mono_of_epi _
  exact hp.of_iso (asIso ((X.filtration.diagram.map (homOfLE hpq : p ⟶ q).op).f n))

/-- The terms of the mapping cone of `α` have finite filtrations as soon as those of `K^•` and
`L^•` do: `C(α)^n = K^{n + 1} ⊕ L^n`, with the filtration induced by those of `K^{n + 1}` and
`L^n`. -/
private lemma fin_coneFiltered (α : K ⟶ L)
    (hKfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n))
    (hLfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((L.filtration.ι.app (op p)).f n) ∧
      IsZero ((L.filtration.obj (op q)).X n)) (n : ℤ) :
    ∃ p q : ℤ, IsIso (((coneFiltered α).filtration.ι.app (op p)).f n) ∧
      IsZero (((coneFiltered α).filtration.obj (op q)).X n) := by
  obtain ⟨pK, qK, hpK, hqK⟩ := hKfin (n + 1)
  obtain ⟨pL, qL, hpL, hqL⟩ := hLfin n
  refine ⟨min pK pL, max qK qL, ?_, ?_⟩
  · rw [coneFiltered_ι_app]
    exact isIso_map_f _ _ _ _ _ n (isIso_ι_f_of_le K (min_le_left _ _) hpK)
      (isIso_ι_f_of_le L (min_le_right _ _) hpL)
  · rw [coneFiltered_fil_obj, mappingCone.isZero_X_iff]
    exact ⟨isZero_fil_X_of_le K (le_max_left _ _) hqK,
      isZero_fil_X_of_le L (le_max_right _ _) hqL⟩

/-- The inclusion `L^• ⟶ C(α)^•` of filtered complexes. -/
private noncomputable def inrCone (α : K ⟶ L) : L ⟶ coneFiltered α :=
  FilteredObject.homMk (mappingCone.inr α.hom)
    (fun p => mappingCone.inr (α.natTrans.app p))
    (fun p => mappingCone.inr_map (α.natTrans.app p) α.hom (K.filtration.ι.app p)
      (L.filtration.ι.app p)
      (α.comm p))

private lemma inrCone_hom (α : K ⟶ L) : (inrCone α).hom = mappingCone.inr α.hom := rfl

/-- Two consecutive steps of the filtration of `X^•` and the `p`-th graded piece form a short
exact sequence of complexes. -/
private lemma shortExact_gradedPiece (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p : ℤ) :
    (ShortComplex.mk
      (X.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
      (cokernel.π _) (cokernel.condition _)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- The square expressing that the `p`-th step of `α` induces `gr^p α` on the graded pieces. -/
private lemma gradedPiece_comm (α : K ⟶ L) (p : ℤ) :
    α.natTrans.app (op p) ≫ cokernel.π (L.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
      = cokernel.π (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) ≫
        (gr p).map α :=
  (grMapπ_map _ α).symm

/-- The comparison morphism `C(F^p α)^• ⟶ C(gr^p α)^•`, induced by the quotient maps of the
`p`-th graded pieces of `K^•` and `L^•`. -/
private noncomputable def coneGr (α : K ⟶ L) (p : ℤ) :
    mappingCone (α.natTrans.app (op p)) ⟶
      mappingCone ((gr p).map α) :=
  mappingCone.map _ _ (cokernel.π _) (cokernel.π _) (gradedPiece_comm α p)

private lemma coneDiagram_map_comp_coneGr (α : K ⟶ L) (p : ℤ) :
    (coneDiagram α).map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op ≫ coneGr α p
      = 0 :=
  map_comp_map_eq_zero _ _ _ _ ((α.natTrans.naturality _).symm) _ _ _
    (gradedPiece_comm α p) (cokernel.condition _) (cokernel.condition _)

/-- **The graded pieces of the mapping cone are the mapping cones of the graded pieces.** The
comparison morphism `C(F^p α)^• ⟶ C(gr^p α)^•` exhibits `C(gr^p α)^•` as the cokernel of the
inclusion `C(F^{p + 1} α)^• ⟶ C(F^p α)^•`: in each degree the sequence is the biproduct of the two
short exact sequences `F^{p + 1} K^{n + 1} → F^p K^{n + 1} → gr^p K^{n + 1}` and
`F^{p + 1} L^n → F^p L^n → gr^p L^n`. -/
private lemma shortExact_coneGr (α : K ⟶ L) (p : ℤ) :
    (ShortComplex.mk
      ((coneDiagram α).map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
      (coneGr α p) (coneDiagram_map_comp_coneGr α p)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hK := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (shortExact_gradedPiece K p) (n + 1)
  have hL := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (shortExact_gradedPiece L p) n
  have hmono : Mono (((coneDiagram α).map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op).f n) :=
    mappingCone.mono_map_f _ _ _ _ ((α.natTrans.naturality _).symm) n inferInstance inferInstance
  have hepi : Epi ((coneGr α p).f n) :=
    mappingCone.epi_map_f _ _ _ _ (gradedPiece_comm α p) n hK.epi_g hL.epi_g
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  refine exact_of_id_eq_add hK.exact hL.exact
    { τ₁ := (mappingCone.inl (α.natTrans.app (op (p + 1)))).v (n + 1) n (by omega)
      τ₂ := (mappingCone.inl (α.natTrans.app (op p))).v (n + 1) n (by omega)
      τ₃ := (mappingCone.inl ((gr p).map α)).v (n + 1) n (by omega)
      comm₁₂ := mappingCone.inl_v_map_f _ _ _ _ ((α.natTrans.naturality _).symm) n
      comm₂₃ := mappingCone.inl_v_map_f _ _ _ _ (gradedPiece_comm α p) n }
    { τ₁ := (mappingCone.fst (α.natTrans.app (op (p + 1)))).1.v n (n + 1) rfl
      τ₂ := (mappingCone.fst (α.natTrans.app (op p))).1.v n (n + 1) rfl
      τ₃ := (mappingCone.fst ((gr p).map α)).1.v n (n + 1) rfl
      comm₁₂ := (mappingCone.map_f_fst_v _ _ _ _ ((α.natTrans.naturality _).symm) n).symm
      comm₂₃ := (mappingCone.map_f_fst_v _ _ _ _ (gradedPiece_comm α p) n).symm }
    { τ₁ := (mappingCone.inr (α.natTrans.app (op (p + 1)))).f n
      τ₂ := (mappingCone.inr (α.natTrans.app (op p))).f n
      τ₃ := (mappingCone.inr ((gr p).map α)).f n
      comm₁₂ := mappingCone.inr_f_map_f _ _ _ _ ((α.natTrans.naturality _).symm) n
      comm₂₃ := mappingCone.inr_f_map_f _ _ _ _ (gradedPiece_comm α p) n }
    { τ₁ := (mappingCone.snd (α.natTrans.app (op (p + 1)))).v n n (add_zero n)
      τ₂ := (mappingCone.snd (α.natTrans.app (op p))).v n n (add_zero n)
      τ₃ := (mappingCone.snd ((gr p).map α)).v n n (add_zero n)
      comm₁₂ := (mappingCone.map_f_snd_v _ _ _ _ ((α.natTrans.naturality _).symm) n).symm
      comm₂₃ := (mappingCone.map_f_snd_v _ _ _ _ (gradedPiece_comm α p) n).symm }
    ?_
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_ <;>
    · dsimp
      apply mappingCone.id_X

/-- **Filtered acyclicity of the mapping cone.** If `α` is a filtered quasi-isomorphism then
`C(α)^•` is filtered acyclic: the graded pieces of the filtration of `C(α)^•` are the mapping cones
`gr^p C(α)^• = C(gr^p α)^•`, and the mapping cone of a quasi-isomorphism is acyclic. -/
private lemma filteredAcyclic_coneFiltered (α : K ⟶ L)
    (hα : CochainComplex.filteredQuasiIso 𝒜 α) :
    CochainComplex.filteredAcyclic 𝒜 (coneFiltered α) := by
  intro p
  have e : ((gr p).obj (coneFiltered α)) ≅
      mappingCone ((gr p).map α) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) (shortExact_coneGr α p).gIsCokernel
  have hac := acyclic_mappingCone _ (hα p)
  intro n
  have h1 := hac n
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h1 ⊢
  exact h1.of_iso ((HomologicalComplex.homologyFunctor 𝒜 (ComplexShape.up ℤ) n).mapIso e)

/-- A commuting square of morphisms of complexes commutes in each degree. -/
private lemma comp_f_eq_of_comp_eq {A B C D : CochainComplex 𝒜 ℤ} {u : A ⟶ B} {v : C ⟶ D}
    {a : A ⟶ C} {b : B ⟶ D} (h : u ≫ b = a ≫ v) (n : ℤ) : u.f n ≫ b.f n = a.f n ≫ v.f n := by
  rw [← HomologicalComplex.comp_f, h, HomologicalComplex.comp_f]

/-- A filtered homotopy between two morphisms which restrict to the steps of the filtrations
restricts to a homotopy on each step: its components factor uniquely through the steps, since
`F^p I^j ⟶ I^j` is a monomorphism, and the homotopy identity for the factors follows from the one
for the components. -/
private noncomputable def homotopyApp {M I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    {f g : M.X ⟶ I.X} (h : Homotopy f g) (hh : IsFilteredHomotopy h) (p : ℤ)
    {fp gp : M.filtration.obj (op p) ⟶ I.filtration.obj (op p)}
    (hf : fp ≫ I.filtration.ι.app (op p) = M.filtration.ι.app (op p) ≫ f)
    (hg : gp ≫ I.filtration.ι.app (op p) = M.filtration.ι.app (op p) ≫ g) :
    Homotopy fp gp where
  hom i j := (hh i j p).choose
  zero i j hij := zero_of_comp_mono ((I.filtration.ι.app (op p)).f j)
    (by rw [(hh i j p).choose_spec, h.zero i j hij, comp_zero])
  comm i := by
    have e1 := (hh (i + 1) i p).choose_spec
    have e2 := (hh i (i - 1) p).choose_spec
    have ef := comp_f_eq_of_comp_eq hf i
    have eg := comp_f_eq_of_comp_eq hg i
    have hcomm := h.comm i
    rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)] at hcomm
    have hmono : Mono ((I.filtration.ι.app (op p)).f i) := inferInstance
    rw [← cancel_mono ((I.filtration.ι.app (op p)).f i), ef, hcomm,
      dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc, eg, e1,
      reassoc_of% e2, ← HomologicalComplex.Hom.comm,
      ← HomologicalComplex.Hom.comm_assoc, Functor.const_obj_obj]

/-- The `p`-th step `C(F^p α)^• ⟶ F^p I^•` of the morphism of the injectivity half: the step of
the filtered homotopy descends along the mapping cone of the step of `α`. -/
private noncomputable def descCone {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (β β' : L ⟶ I) (h : Homotopy (α.hom ≫ β.hom) (α.hom ≫ β'.hom)) (hh : IsFilteredHomotopy h)
    (p : ℤ) : mappingCone (α.natTrans.app (op p)) ⟶ I.filtration.obj (op p) :=
  mappingCone.desc _ (HomComplex.Cochain.ofHomotopy
      (homotopyApp h hh p (fp := α.natTrans.app (op p) ≫ β.natTrans.app (op p))
        (gp := α.natTrans.app (op p) ≫ β'.natTrans.app (op p)) (by simp) (by simp)))
    (β.natTrans.app (op p) - β'.natTrans.app (op p)) (by simp [Preadditive.comp_sub])

/-- The morphism `C(α)^• ⟶ I^•` of the injectivity half, on the underlying complexes: the
filtered homotopy is a degree `-1` cochain `K^• ⟶ I^•` whose `δ` is `α ≫ (β - β')`, so it descends
along the mapping cone to a morphism restricting to `β - β'` on `L^•`. -/
private noncomputable def descConeHom {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (β β' : L ⟶ I) (h : Homotopy (α.hom ≫ β.hom) (α.hom ≫ β'.hom)) :
    mappingCone α.hom ⟶ I.X :=
  mappingCone.desc _ (HomComplex.Cochain.ofHomotopy h) (β.hom - β'.hom)
    (by simp [Preadditive.comp_sub])

/-- The steps `C(F^p α)^• ⟶ F^p I^•` are compatible with `C(α)^• ⟶ I^•`, i.e. the morphism of the
injectivity half is a morphism of filtered complexes. -/
private lemma descCone_comp_ι {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (β β' : L ⟶ I) (h : Homotopy (α.hom ≫ β.hom) (α.hom ≫ β'.hom)) (hh : IsFilteredHomotopy h)
    (p : ℤ) :
    descCone α β β' h hh p ≫ I.filtration.ι.app (op p)
      = mappingCone.map (α.natTrans.app (op p)) α.hom (K.filtration.ι.app (op p))
          (L.filtration.ι.app (op p)) (α.comm (op p)) ≫ descConeHom α β β' h := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    mappingCone.ext_from_iff _ (n + 1) n rfl]
  constructor
  · rw [← Category.assoc, ← Category.assoc, descCone, mappingCone.inl_v_desc_f,
      mappingCone.inl_v_map_f,
      Category.assoc, descConeHom, mappingCone.inl_v_desc_f]
    exact (hh (n + 1) n p).choose_spec
  · have hβ := comp_f_eq_of_comp_eq (β.comm (op p)) n
    have hβ' := comp_f_eq_of_comp_eq (β'.comm (op p)) n
    rw [← Category.assoc, ← Category.assoc, descCone, mappingCone.inr_f_desc_f,
      mappingCone.inr_f_map_f,
      Category.assoc, descConeHom, mappingCone.inr_f_desc_f]
    simp [Preadditive.sub_comp, Preadditive.comp_sub, hβ, hβ']

/-- **The morphism `C(α)^• ⟶ I^•` of the injectivity half.** A filtered homotopy between
`α ≫ β` and `α ≫ β'` is a degree `-1` cochain `K^• ⟶ I^•` whose `δ` is
`α ≫ β' - α ≫ β`, hence descends along the mapping cone to a morphism `C(α)^• ⟶ I^•`
restricting to `β - β'` on `L^•`; it is filtered because the homotopy and `β`, `β'` are. -/
private lemma exists_hom_coneFiltered {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (β β' : L ⟶ I) (h : Homotopy (α.hom ≫ β.hom) (α.hom ≫ β'.hom)) (hh : IsFilteredHomotopy h) :
    ∃ φ : coneFiltered α ⟶ I, mappingCone.inr α.hom ≫ φ.hom = β.hom - β'.hom :=
  ⟨FilteredObject.homMk (descConeHom α β β' h) (fun p => descCone α β β' h hh p.unop)
    (fun p => descCone_comp_ι α β β' h hh p.unop), by
      show mappingCone.inr α.hom ≫ descConeHom α β β' h = β.hom - β'.hom
      simp [descConeHom]⟩

/-- **The injectivity half.** Two morphisms `L^• ⟶ I^•` which become filtered homotopic after
composition with `α` are filtered homotopic: their difference descends to `C(α)^• ⟶ I^•`, which is
filtered null homotopic by Lemma 05TX since `C(α)^•` is filtered acyclic, and restricting that null
homotopy along `L^• ⟶ C(α)^•` is a filtered null homotopy of the difference. -/
private lemma exists_filtered_homotopy {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (hα : CochainComplex.filteredQuasiIso 𝒜 α) (n₀ : ℤ) [I.X.IsStrictlyGE n₀]
    (hKfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n))
    (hLfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((L.filtration.ι.app (op p)).f n) ∧
      IsZero ((L.filtration.obj (op q)).X n))
    (hIfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hI : ∀ p n : ℤ, Injective (((gr p).obj I).X n))
    (β β' : L ⟶ I) (h : Homotopy (α.hom ≫ β.hom) (α.hom ≫ β'.hom)) (hh : IsFilteredHomotopy h) :
    ∃ H : Homotopy β.hom β'.hom, IsFilteredHomotopy H := by
  obtain ⟨φ, hφ⟩ := exists_hom_coneFiltered α β β' h hh
  obtain ⟨H, hH⟩ :=
    CochainComplex.exists_homotopy_zero_of_filteredAcyclic_of_injective_gradedPiece φ n₀
      (filteredAcyclic_coneFiltered α hα) (fin_coneFiltered α hKfin hLfin)
      (fun n => (isFilteredInjective_evalFil_iff I n).2 ⟨hIfin n, fun p => hI p n⟩)
  have hcomp : ∀ i j : ℤ,
      IsFilteredComponent L I i j ((inrCone α).hom.f i ≫ H.hom i j) := fun i j =>
    IsFilteredComponent.comp_left (inrCone α) (fun p => hH i j p)
  refine ⟨Homotopy.equivSubZero.symm ((Homotopy.ofEq hφ.symm).trans
    ((H.compLeft (inrCone α).hom).trans (Homotopy.ofEq comp_zero))), fun i j p => ?_⟩
  obtain ⟨hp, hhp⟩ := hcomp i j p
  exact ⟨hp, by simpa [Homotopy.trans, Homotopy.ofEq, Homotopy.equivSubZero] using hhp⟩

/-! ### The shift of a filtered complex -/

/-- The transformation `F^p X^•[m] ⟶ X^•[m]` obtained by shifting the steps of the filtration of
`X^•`; its components are monomorphisms because the shift functor is an equivalence. -/
private noncomputable def shiftIota (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (m : ℤ) :
    X.filtration.diagram ⋙ CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) m ⟶
      (Functor.const ℤᵒᵖ).obj
        ((CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) m).obj X.X) where
  app p := (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) m).map (X.filtration.ι.app p)
  naturality {p q} f := by
    dsimp
    rw [Category.comp_id, ← Functor.map_comp]
    congr 1
    simp

private instance mono_shiftIota (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (m : ℤ) (p : ℤᵒᵖ) :
    Mono ((shiftIota X m).app p) := by
  dsimp [shiftIota]
  infer_instance

/-- **The shift of a filtered complex**: the shift `X^•[m]` of the underlying complex, filtered by
the shifts `F^p X^•[m]` of the steps. In each degree this is pure reindexing:
`(F^p X^•[m])^n = (F^p X^•)^{n + m}`. -/
private noncomputable def shiftFiltered (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (m : ℤ) :
    FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  X := (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) m).obj X.X
  filtration := filtrationOfDiagram
    (X.filtration.diagram ⋙ CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) m)
    (shiftIota X m)

/-- Shifting a bounded below complex shifts the bound. -/
private lemma isStrictlyGE_shiftFiltered (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n₀ : ℤ)
    [X.X.IsStrictlyGE n₀] : (shiftFiltered X 1).X.IsStrictlyGE (n₀ - 1) :=
  CochainComplex.isStrictlyGE_shift X.X n₀ 1 (n₀ - 1) (by omega)

/-- The terms of a shifted filtered complex have finite filtrations as soon as those of the
original do: the filtration in degree `n` of the shift is the filtration in degree `n + m`. -/
private lemma fin_shiftFiltered (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (m : ℤ)
    (hfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((X.filtration.ι.app (op p)).f n) ∧
      IsZero ((X.filtration.obj (op q)).X n)) (n : ℤ) :
    ∃ p q : ℤ, IsIso (((shiftFiltered X m).filtration.ι.app (op p)).f n) ∧
      IsZero (((shiftFiltered X m).filtration.obj (op q)).X n) :=
  hfin (n + m)

/-- The graded pieces of a shifted filtered complex are the shifts of the graded pieces: in degree
`n` both are the cokernel of the same morphism `F^{p + 1} X^{n + m} ⟶ F^p X^{n + m}`, cokernels of
complexes being computed degreewise. -/
private noncomputable def gradedPieceShiftXIso (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (m p n : ℤ) :
    ((gr p).obj (shiftFiltered X m)).X n ≅
      ((gr p).obj X).X (n + m) :=
  (PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
      ((shiftFiltered X m).filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)).trans
    (PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) (n + m))
      (X.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)).symm

/-- A shifted filtered complex is filtered injective as soon as the original is. -/
private lemma injective_gradedPiece_shiftFiltered (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (m : ℤ) (hX : ∀ p n : ℤ, Injective (((gr p).obj X).X n))
    (p n : ℤ) :
    Injective (((gr p).obj (shiftFiltered X m)).X n) :=
  Injective.of_iso (gradedPieceShiftXIso X m p n).symm (hX p (n + m))

/-- The steps of the morphism `C(α)^• ⟶ I^•[1]` are compatible with it, i.e. it is a morphism of
filtered complexes: the projections of the standard triangles are compatible with the morphism of
mapping cones induced by the steps of `α`. -/
private lemma coneShiftHom_comm {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (γ : K ⟶ I) (p : ℤᵒᵖ) :
    coneShiftHom (α.natTrans.app p) (γ.natTrans.app p) ≫
        (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (1 : ℤ)).map
          (I.filtration.ι.app p)
      = mappingCone.map (α.natTrans.app p) α.hom (K.filtration.ι.app p)
          (L.filtration.ι.app p) (α.comm p) ≫ coneShiftHom α.hom γ.hom := by
  rw [coneShiftHom, coneShiftHom, Category.assoc, ← Functor.map_comp, γ.comm p,
    Functor.map_comp, ← Category.assoc, ← Category.assoc,
    map_comp_coneProj (α.natTrans.app p) α.hom (K.filtration.ι.app p) (L.filtration.ι.app p)
      (α.comm p)]

/-- **The morphism `C(α)^• ⟶ I^•[1]` of the surjectivity half**, of filtered complexes: project
the mapping cone onto `K^•[1]` and apply `γ`. -/
private noncomputable def coneToShift {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (γ : K ⟶ I) : coneFiltered α ⟶ shiftFiltered I 1 :=
  FilteredObject.homMk (coneShiftHom α.hom γ.hom)
    (fun p => coneShiftHom (α.natTrans.app p) (γ.natTrans.app p))
    (fun p => coneShiftHom_comm α γ p)

/-- The `p`-th step of a morphism of complexes all of whose terms are filtered: the factorisations
of the terms through the steps of the filtrations, which form a morphism of complexes because
`F^p I^j ⟶ I^j` is a monomorphism. -/
private noncomputable def filteredStepOfComponents
    {M I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (f : M.X ⟶ I.X)
    (hf : ∀ n : ℤ, IsFilteredComponent M I n n (f.f n)) (p : ℤ) :
    M.filtration.obj (op p) ⟶ I.filtration.obj (op p) where
  f n := (hf n p).choose
  comm' i j _ := by
    have e1 := (hf i p).choose_spec
    have e2 := (hf j p).choose_spec
    have hI : (I.filtration.obj (op p)).d i j ≫ (I.filtration.ι.app (op p)).f j
        = (I.filtration.ι.app (op p)).f i ≫ I.X.d i j :=
      (HomologicalComplex.Hom.comm (I.filtration.ι.app (op p)) i j).symm
    have hM : (M.filtration.ι.app (op p)).f i ≫ M.X.d i j
        = (M.filtration.obj (op p)).d i j ≫ (M.filtration.ι.app (op p)).f j :=
      HomologicalComplex.Hom.comm (M.filtration.ι.app (op p)) i j
    have hmono : Mono ((I.filtration.ι.app (op p)).f j) := inferInstance
    rw [← cancel_mono ((I.filtration.ι.app (op p)).f j)]
    simp only [Category.assoc]
    rw [hI, e2, ← Category.assoc, e1, Category.assoc,
      HomologicalComplex.Hom.comm f i j, ← Category.assoc, hM, Category.assoc]

/-- A morphism of complexes all of whose terms are filtered is a morphism of filtered
complexes. -/
private noncomputable def homOfFilteredComponents
    {M I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (f : M.X ⟶ I.X)
    (hf : ∀ n : ℤ, IsFilteredComponent M I n n (f.f n)) : M ⟶ I :=
  FilteredObject.homMk f (fun p => filteredStepOfComponents f hf p.unop)
    (fun p => by
      ext n
      exact (hf n p.unop).choose_spec)

/-- **The surjectivity half.** Every morphism `γ : K^• ⟶ I^•` is, up to filtered homotopy, the
composition of `α` with a morphism `L^• ⟶ I^•`: the composition `C(α)^•[-1] ⟶ K^• ⟶ I^•` of `γ`
with the projection of the shifted mapping cone is filtered null homotopic by Lemma 05TX, since
`C(α)^•[-1]` is filtered acyclic, and the two components of that null homotopy are the morphism
`β : L^• ⟶ I^•` and a filtered homotopy from `α ≫ β` to `γ`. -/
private lemma exists_filtered_factorization {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : K ⟶ L) (hα : CochainComplex.filteredQuasiIso 𝒜 α) (n₀ : ℤ) [I.X.IsStrictlyGE n₀]
    (hKfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n))
    (hLfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((L.filtration.ι.app (op p)).f n) ∧
      IsZero ((L.filtration.obj (op q)).X n))
    (hIfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hI : ∀ p n : ℤ, Injective (((gr p).obj I).X n))
    (γ : K ⟶ I) :
    ∃ (β : L ⟶ I) (H : Homotopy (α.hom ≫ β.hom) γ.hom), IsFilteredHomotopy H := by
  have : (shiftFiltered I 1).X.IsStrictlyGE (n₀ - 1) := isStrictlyGE_shiftFiltered I n₀
  obtain ⟨h, hh⟩ :=
    CochainComplex.exists_homotopy_zero_of_filteredAcyclic_of_injective_gradedPiece
      (coneToShift α γ) (n₀ - 1) (filteredAcyclic_coneFiltered α hα)
      (fin_coneFiltered α hKfin hLfin) (fun n => (isFilteredInjective_evalFil_iff _ n).2
        ⟨fin_shiftFiltered I 1 hIfin n, fun p => injective_gradedPiece_shiftFiltered I 1 hI p n⟩)
  have hu : ∀ n : ℤ, IsFilteredComponent (coneFiltered α) I n n
      ((unshiftCochain α.hom γ.hom h).v n n (add_zero n)) := fun n =>
    IsFilteredComponent.of_eq (unshiftCochain_v α.hom γ.hom h n).symm
      (IsFilteredComponent.neg (IsFilteredComponent.congr_tgt
        (show n - 1 + 1 = n by omega) (fun p => hh n (n - 1) p)))
  have hβ : ∀ n : ℤ, IsFilteredComponent L I n n ((descShiftHom α.hom γ.hom h).f n) := fun n =>
    IsFilteredComponent.of_eq (descShiftHom_f α.hom γ.hom h n).symm
      (IsFilteredComponent.comp_left (inrCone α) (hu n))
  refine ⟨homOfFilteredComponents (descShiftHom α.hom γ.hom h) hβ,
    descShiftHomotopy α.hom γ.hom h, fun i j => ?_⟩
  by_cases hij : i + (-1) = j
  · obtain rfl : i = j + 1 := by omega
    exact IsFilteredComponent.of_eq (descShiftHomotopy_hom α.hom γ.hom h j).symm
      (IsFilteredComponent.comp_left_component _
        (fun p => (mappingCone.inl (α.natTrans.app (op p))).v (j + 1) j (by omega))
        (fun p => mappingCone.inl_v_map_f (α.natTrans.app (op p)) α.hom (K.filtration.ι.app (op p))
          (L.filtration.ι.app (op p)) (α.comm (op p)) j) (hu j))
  · have hz : (descShiftHomotopy α.hom γ.hom h).hom i j = 0 := by
      apply Homotopy.zero
      simp only [ComplexShape.up_Rel]
      omega
    exact IsFilteredComponent.of_eq hz.symm (IsFilteredComponent.zero _ _ _ _)

end FilteredCone

/-! ### The cylinder of a filtered complex

Part (2) asserts in particular that filtered homotopic morphisms have the same image in the filtered
derived category. Since the filtered derived category is formed from filtered complexes and not from
the homotopy category `K(Fil^f(𝒜))`, there is no homotopy category to factor through, so the
identification has to be made inside the localisation itself, and the mechanism is the cylinder: the
cylinder `Cyl(M)^•` of a complex is the mapping cone of `(𝟙, -𝟙) : M^• ⟶ M^• ⊕ M^•`, so filtering
`M^• ⊕ M^•` by the `F^p M^• ⊕ F^p M^•` exhibits it as the mapping cone of a morphism of filtered
complexes whose steps are the cylinders of the steps of `M^•`. Its projection `Cyl(M)^• ⟶ M^•` is a
filtered quasi-isomorphism, because each of its steps is the projection of a cylinder, hence a
homotopy equivalence, and a morphism of filtered complexes all of whose steps are quasi-isomorphisms
is a filtered quasi-isomorphism. The two inclusions `M^• ⟶ Cyl(M)^•` are sections of that
projection, so they have the same image in the localisation, and a filtered homotopy from `f` to `g`
is precisely a morphism `Cyl(M)^• ⟶ I^•` restricting to `f` along one inclusion and to `g` along the
other. -/

section Cylinder

/-! #### Biproducts of complexes -/

/-- The biproduct of two identity morphisms is the identity of the biproduct. -/
public lemma biprod_map_id {C : Type*} [Category C] [HasZeroMorphisms C] (X Y : C)
    [HasBinaryBiproduct X Y] : biprod.map (𝟙 X) (𝟙 Y) = 𝟙 (X ⊞ Y) :=
  biprod.hom_ext _ _ (by simp) (by simp)

private lemma isIso_biprod_map {C : Type*} [Category C] [HasZeroMorphisms C] {A B : C}
    [HasBinaryBiproduct A A] [HasBinaryBiproduct B B] (a : A ⟶ B) [IsIso a] :
    IsIso (biprod.map a a) :=
  ⟨biprod.map (inv a) (inv a),
    by rw [biprod_map_comp_map, IsIso.hom_inv_id, biprod_map_id],
    by rw [biprod_map_comp_map, IsIso.inv_hom_id, biprod_map_id]⟩

/-- The degreewise description of the biproduct of a morphism of complexes with itself. -/
private lemma biprod_map_f {A B : CochainComplex 𝒜 ℤ} (u : A ⟶ B) (n : ℤ) :
    (biprod.map u u).f n = (HomologicalComplex.biprodXIso A A n).hom ≫
      biprod.map (u.f n) (u.f n) ≫ (HomologicalComplex.biprodXIso B B n).inv := by
  rw [← Iso.inv_comp_eq]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv, ← HomologicalComplex.comp_f,
      biprod.inl_map, HomologicalComplex.comp_f, biprod.inl_map_assoc,
      HomologicalComplex.inl_biprodXIso_inv]
  · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv, ← HomologicalComplex.comp_f,
      biprod.inr_map, HomologicalComplex.comp_f, biprod.inr_map_assoc,
      HomologicalComplex.inr_biprodXIso_inv]

private lemma isIso_biprod_map_f {A B : CochainComplex 𝒜 ℤ} (u : A ⟶ B) (n : ℤ)
    (hu : IsIso (u.f n)) : IsIso ((biprod.map u u).f n) := by
  have h1 := hu
  have h2 : IsIso (biprod.map (u.f n) (u.f n)) := isIso_biprod_map _
  rw [biprod_map_f]
  infer_instance

private lemma isZero_biprod_X {A : CochainComplex 𝒜 ℤ} (n : ℤ) (hA : IsZero (A.X n)) :
    IsZero ((A ⊞ A).X n) := by
  rw [(HomologicalComplex.biprodXIso A A n).isZero_iff, biprod_isZero_iff]
  exact ⟨hA, hA⟩

/-- Every degree of a cochain complex is the target of a differential; this is what Mathlib's
cylinder API asks of the complex shape. -/
private lemma exists_up_rel (j : ℤ) : ∃ i : ℤ, (ComplexShape.up ℤ).Rel i j :=
  ⟨j - 1, by simp only [ComplexShape.up_Rel]; omega⟩

private lemma up_rel_succ (n : ℤ) : (ComplexShape.up ℤ).Rel n (n + 1) := by
  simp only [ComplexShape.up_Rel]

/-! #### The cylinder of a morphism of complexes -/

section CylinderMap

variable {A B : CochainComplex 𝒜 ℤ}

/-- The morphism `(𝟙, -𝟙)` whose mapping cone is the cylinder is natural in the complex. -/
private lemma biprod_lift_comp_biprod_map (u : A ⟶ B) :
    biprod.lift (𝟙 A) (-𝟙 A) ≫ biprod.map u u = u ≫ biprod.lift (𝟙 B) (-𝟙 B) :=
  biprod.hom_ext _ _ (by simp) (by simp)

/-- The cylinder of a morphism of complexes, as a morphism of the mapping cones of `(𝟙, -𝟙)`. -/
private noncomputable def cylMap (u : A ⟶ B) : A.cylinder ⟶ B.cylinder :=
  mappingCone.map (biprod.lift (𝟙 A) (-𝟙 A)) (biprod.lift (𝟙 B) (-𝟙 B)) u (biprod.map u u)
    (biprod_lift_comp_biprod_map u)

private lemma inlX_cylMap_f (u : A ⟶ B) (n : ℤ) :
    HomologicalComplex.homotopyCofiber.inlX (biprod.lift (𝟙 A) (-𝟙 A)) (n + 1) n
          (up_rel_succ n) ≫ (cylMap u).f n
      = u.f (n + 1) ≫ HomologicalComplex.homotopyCofiber.inlX (biprod.lift (𝟙 B) (-𝟙 B))
          (n + 1) n (up_rel_succ n) :=
  mappingCone.inl_v_map_f _ _ u (biprod.map u u) (biprod_lift_comp_biprod_map u) n

private lemma inrX_cylMap_f (u : A ⟶ B) (n : ℤ) :
    HomologicalComplex.homotopyCofiber.inrX (biprod.lift (𝟙 A) (-𝟙 A)) n ≫ (cylMap u).f n
      = (biprod.map u u).f n ≫
        HomologicalComplex.homotopyCofiber.inrX (biprod.lift (𝟙 B) (-𝟙 B)) n :=
  mappingCone.inr_f_map_f _ _ u (biprod.map u u) (biprod_lift_comp_biprod_map u) n

/-- The projection of the cylinder is natural. -/
private lemma cylinder_π_naturality (u : A ⟶ B) :
    HomologicalComplex.cylinder.π A ≫ u = cylMap u ≫ HomologicalComplex.cylinder.π B := by
  ext n
  refine HomologicalComplex.homotopyCofiber.ext_from_X (biprod.lift (𝟙 A) (-𝟙 A)) (n + 1) n
    (up_rel_succ n) ?_ ?_
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
      HomologicalComplex.cylinder.inlX_π, ← Category.assoc, inlX_cylMap_f, Category.assoc,
      HomologicalComplex.cylinder.inlX_π, zero_comp, comp_zero]
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
      HomologicalComplex.cylinder.inrX_π, ← Category.assoc, inrX_cylMap_f, Category.assoc,
      HomologicalComplex.cylinder.inrX_π, ← HomologicalComplex.comp_f,
      ← HomologicalComplex.comp_f]
    congr 1
    exact biprod.hom_ext' _ _ (by simp) (by simp)

private lemma inr_cylMap (u : A ⟶ B) :
    HomologicalComplex.homotopyCofiber.inr (biprod.lift (𝟙 A) (-𝟙 A)) ≫ cylMap u
      = biprod.map u u ≫
        HomologicalComplex.homotopyCofiber.inr (biprod.lift (𝟙 B) (-𝟙 B)) :=
  mappingCone.inr_map _ _ u (biprod.map u u) (biprod_lift_comp_biprod_map u)

/-- The first inclusion of the cylinder is natural. -/
private lemma cylinder_ι₀_naturality (u : A ⟶ B) :
    HomologicalComplex.cylinder.ι₀ A ≫ cylMap u = u ≫ HomologicalComplex.cylinder.ι₀ B := by
  simp only [HomologicalComplex.cylinder.ι₀, Category.assoc, inr_cylMap]
  rw [← Category.assoc, biprod.inl_map, Category.assoc]

/-- The second inclusion of the cylinder is natural. -/
private lemma cylinder_ι₁_naturality (u : A ⟶ B) :
    HomologicalComplex.cylinder.ι₁ A ≫ cylMap u = u ≫ HomologicalComplex.cylinder.ι₁ B := by
  simp only [HomologicalComplex.cylinder.ι₁, Category.assoc, inr_cylMap]
  rw [← Category.assoc, biprod.inr_map, Category.assoc]

private lemma inlX_cylinder_desc_f {J : CochainComplex 𝒜 ℤ} {f₀ f₁ : A ⟶ J}
    (h : Homotopy f₀ f₁) (n : ℤ) :
    HomologicalComplex.homotopyCofiber.inlX (biprod.lift (𝟙 A) (-𝟙 A)) (n + 1) n (up_rel_succ n) ≫
        (HomologicalComplex.cylinder.desc f₀ f₁ h).f n = h.hom (n + 1) n := by
  simp [HomologicalComplex.cylinder.desc, Homotopy.trans, Homotopy.ofEq, Homotopy.equivSubZero]

private lemma inrX_cylinder_desc_f {J : CochainComplex 𝒜 ℤ} {f₀ f₁ : A ⟶ J}
    (h : Homotopy f₀ f₁) (n : ℤ) :
    HomologicalComplex.homotopyCofiber.inrX (biprod.lift (𝟙 A) (-𝟙 A)) n ≫
        (HomologicalComplex.cylinder.desc f₀ f₁ h).f n = (biprod.desc f₀ f₁).f n := by
  simp [HomologicalComplex.cylinder.desc]

/-- The morphism out of the cylinder attached to two morphisms and a homotopy is natural: a
morphism `v` of targets which intertwines both pairs of morphisms and both homotopies also
intertwines the two morphisms out of the cylinders. -/
private lemma cylinder_desc_naturality {J₁ J₂ : CochainComplex 𝒜 ℤ} (u : A ⟶ B) (v : J₁ ⟶ J₂)
    {f₀ f₁ : A ⟶ J₁} {g₀ g₁ : B ⟶ J₂} (h₁ : Homotopy f₀ f₁) (h₂ : Homotopy g₀ g₁)
    (e₀ : f₀ ≫ v = u ≫ g₀) (e₁ : f₁ ≫ v = u ≫ g₁)
    (eh : ∀ i j : ℤ, h₁.hom i j ≫ v.f j = u.f i ≫ h₂.hom i j) :
    HomologicalComplex.cylinder.desc f₀ f₁ h₁ ≫ v
      = cylMap u ≫ HomologicalComplex.cylinder.desc g₀ g₁ h₂ := by
  ext n
  refine HomologicalComplex.homotopyCofiber.ext_from_X (biprod.lift (𝟙 A) (-𝟙 A)) (n + 1) n
    (up_rel_succ n) ?_ ?_
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
      inlX_cylinder_desc_f, ← Category.assoc, inlX_cylMap_f, Category.assoc,
      inlX_cylinder_desc_f]
    exact eh (n + 1) n
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
      inrX_cylinder_desc_f, ← Category.assoc, inrX_cylMap_f, Category.assoc,
      inrX_cylinder_desc_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    congr 1
    exact biprod.hom_ext' _ _ (by simpa using e₀) (by simpa using e₁)

end CylinderMap

/-! #### The filtered cylinder -/

variable (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)

/-- The diagram `p ↦ F^p M^• ⊕ F^p M^•` of biproducts of the steps of the filtration. -/
private noncomputable def biprodDiagram : ℤᵒᵖ ⥤ CochainComplex 𝒜 ℤ where
  obj p := M.filtration.obj p ⊞ M.filtration.obj p
  map f := biprod.map (M.filtration.diagram.map f) (M.filtration.diagram.map f)
  map_id p := by rw [M.filtration.diagram.map_id, biprod_map_id]
  map_comp f g := by rw [M.filtration.diagram.map_comp, biprod_map_comp_map]

/-- The transformation `F^p M^• ⊕ F^p M^• ⟶ M^• ⊕ M^•`. -/
private noncomputable def biprodι :
    biprodDiagram M ⟶ (Functor.const ℤᵒᵖ).obj (M.X ⊞ M.X) where
  app p := biprod.map (M.filtration.ι.app p) (M.filtration.ι.app p)
  naturality {p q} f := by
    have hnat : M.filtration.diagram.map f ≫ M.filtration.ι.app q = M.filtration.ι.app p :=
      M.filtration.diagram_map_comp_ι_app f
    change biprod.map (M.filtration.diagram.map f) (M.filtration.diagram.map f) ≫
        biprod.map (M.filtration.ι.app q) (M.filtration.ι.app q)
      = biprod.map (M.filtration.ι.app p) (M.filtration.ι.app p) ≫ 𝟙 _
    rw [Category.comp_id, biprod_map_comp_map, hnat]
    exact rfl

private instance mono_biprodι_app (p : ℤᵒᵖ) : Mono ((biprodι M).app p) := by
  change Mono (biprod.map (M.filtration.ι.app p) (M.filtration.ι.app p))
  infer_instance

/-- `M^• ⊕ M^•`, filtered by the biproducts `F^p M^• ⊕ F^p M^•` of the steps of `M^•`. -/
private noncomputable def biprodFiltered : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  X := M.X ⊞ M.X
  filtration := filtrationOfDiagram (biprodDiagram M) (biprodι M)

private lemma biprodFiltered_ι_app (p : ℤᵒᵖ) :
    (biprodFiltered M).filtration.ι.app p =
      biprod.map (M.filtration.ι.app p) (M.filtration.ι.app p) := rfl

private lemma biprodFiltered_fil_obj (p : ℤᵒᵖ) :
    (biprodFiltered M).filtration.obj p = (M.filtration.obj p ⊞ M.filtration.obj p) := rfl

/-- The terms of `M^• ⊕ M^•` have finite filtrations as soon as those of `M^•` do. -/
private lemma fin_biprodFiltered
    (hMfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((M.filtration.ι.app (op p)).f n) ∧
      IsZero ((M.filtration.obj (op q)).X n)) (n : ℤ) :
    ∃ p q : ℤ, IsIso (((biprodFiltered M).filtration.ι.app (op p)).f n) ∧
      IsZero (((biprodFiltered M).filtration.obj (op q)).X n) := by
  obtain ⟨p, q, hp, hq⟩ := hMfin n
  exact ⟨p, q, isIso_biprod_map_f _ n hp, isZero_biprod_X n hq⟩

/-- The morphism `(𝟙, -𝟙) : M^• ⟶ M^• ⊕ M^•` of filtered complexes, whose mapping cone is the
cylinder. -/
private noncomputable def diagFiltered : M ⟶ biprodFiltered M :=
  FilteredObject.homMk (biprod.lift (𝟙 M.X) (-𝟙 M.X))
    (fun p => biprod.lift (𝟙 (M.filtration.obj p)) (-𝟙 (M.filtration.obj p)))
    (fun p => biprod_lift_comp_biprod_map (M.filtration.ι.app p))

/-- **The cylinder of a filtered complex**, the mapping cone of `(𝟙, -𝟙)`: the cylinder of the
underlying complex, filtered by the cylinders of the steps. -/
private noncomputable def cylFiltered : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ :=
  coneFiltered (diagFiltered M)

private lemma cylFiltered_X : (cylFiltered M).X = M.X.cylinder := rfl

private lemma cylFiltered_fil_obj (p : ℤᵒᵖ) :
    (cylFiltered M).filtration.obj p = (M.filtration.obj p).cylinder := rfl

private lemma cylFiltered_ι_app (p : ℤᵒᵖ) :
    (cylFiltered M).filtration.ι.app p = cylMap (M.filtration.ι.app p) := rfl

/-- The terms of the cylinder have finite filtrations as soon as those of `M^•` do. -/
private lemma fin_cylFiltered
    (hMfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((M.filtration.ι.app (op p)).f n) ∧
      IsZero ((M.filtration.obj (op q)).X n)) (n : ℤ) :
    ∃ p q : ℤ, IsIso (((cylFiltered M).filtration.ι.app (op p)).f n) ∧
      IsZero (((cylFiltered M).filtration.obj (op q)).X n) :=
  fin_coneFiltered (diagFiltered M) hMfin (fin_biprodFiltered M hMfin) n

/-- **The projection of the cylinder** `Cyl(M)^• ⟶ M^•` of filtered complexes: on each step it is
the projection of the cylinder of that step. -/
private noncomputable def cylπ : cylFiltered M ⟶ M :=
  FilteredObject.homMk (HomologicalComplex.cylinder.π M.X)
    (fun p => HomologicalComplex.cylinder.π (M.filtration.obj p))
    (fun p => cylinder_π_naturality (M.filtration.ι.app p))

/-- **The first inclusion** `M^• ⟶ Cyl(M)^•` of filtered complexes. -/
private noncomputable def cylι₀ : M ⟶ cylFiltered M :=
  FilteredObject.homMk (HomologicalComplex.cylinder.ι₀ M.X)
    (fun p => HomologicalComplex.cylinder.ι₀ (M.filtration.obj p))
    (fun p => cylinder_ι₀_naturality (M.filtration.ι.app p))

/-- **The second inclusion** `M^• ⟶ Cyl(M)^•` of filtered complexes. -/
private noncomputable def cylι₁ : M ⟶ cylFiltered M :=
  FilteredObject.homMk (HomologicalComplex.cylinder.ι₁ M.X)
    (fun p => HomologicalComplex.cylinder.ι₁ (M.filtration.obj p))
    (fun p => cylinder_ι₁_naturality (M.filtration.ι.app p))

private lemma cylι₀_comp_cylπ : cylι₀ M ≫ cylπ M = 𝟙 M :=
  FilteredObject.hom_ext (HomologicalComplex.cylinder.ι₀_π M.X)

private lemma cylι₁_comp_cylπ : cylι₁ M ≫ cylπ M = 𝟙 M :=
  FilteredObject.hom_ext (HomologicalComplex.cylinder.ι₁_π M.X)

/-- **The projection of the cylinder is a filtered quasi-isomorphism**: each of its steps is the
projection of a cylinder, hence a homotopy equivalence. -/
private lemma filteredQuasiIso_cylπ : CochainComplex.filteredQuasiIso 𝒜 (cylπ M) :=
  filteredQuasiIso_of_natTrans _ fun p => by
    show QuasiIso (HomologicalComplex.cylinder.π (M.filtration.obj (op p)))
    rw [show HomologicalComplex.cylinder.π (M.filtration.obj (op p))
        = (HomologicalComplex.cylinder.homotopyEquiv (M.filtration.obj (op p))
          exists_up_rel).hom from rfl]
    infer_instance

/-- **The morphism `Cyl(M)^• ⟶ I^•` attached to a filtered homotopy** from `f` to `g`: on each
step it is the morphism attached to the restricted homotopy of that step. -/
private noncomputable def cylDesc {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (f g : M ⟶ I)
    (h : Homotopy f.hom g.hom) (hh : IsFilteredHomotopy h) : cylFiltered M ⟶ I :=
  FilteredObject.homMk (HomologicalComplex.cylinder.desc f.hom g.hom h)
    (fun p => HomologicalComplex.cylinder.desc (f.natTrans.app p) (g.natTrans.app p)
      (homotopyApp h hh p.unop (f.comm p) (g.comm p)))
    (fun p => cylinder_desc_naturality (M.filtration.ι.app p) (I.filtration.ι.app p) _ h
      (f.comm p) (g.comm p) (fun i j => (hh i j p.unop).choose_spec))

private lemma cylι₀_comp_cylDesc {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (f g : M ⟶ I)
    (h : Homotopy f.hom g.hom) (hh : IsFilteredHomotopy h) :
    cylι₀ M ≫ cylDesc M f g h hh = f :=
  FilteredObject.hom_ext (HomologicalComplex.cylinder.ι₀_desc f.hom g.hom h)

private lemma cylι₁_comp_cylDesc {I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (f g : M ⟶ I)
    (h : Homotopy f.hom g.hom) (hh : IsFilteredHomotopy h) :
    cylι₁ M ≫ cylDesc M f g h hh = g :=
  FilteredObject.hom_ext (HomologicalComplex.cylinder.ι₁_desc f.hom g.hom h)

end Cylinder


/-! ### Morphisms into a bounded below filtered injective complex in the filtered derived category

Part (2) is part (1) read in the localisation. Two general facts about localisations do the
reading, both for an object `I^•` which is *local* for the inverted class in the sense that
precomposition with a morphism of the class is bijective on the filtered homotopy classes of
morphisms into `I^•`, which is exactly part (1).

The first is that every morphism `Q.obj M^• ⟶ Q.obj I^•` is `Q.map` of a morphism `M^• ⟶ I^•`. It
is proved on the standard model of the localisation, the quotient of the path category of the
quiver of `K(Fil^f(𝒜))` and the formal inverses, by induction on the length of a path: a path
followed by a morphism `g` into `I^•` is `Q.map` of a single morphism, since an edge which is a
morphism `u` can be absorbed into `g` as `u ≫ g`, and an edge which is the formal inverse of a
morphism `w` of the class can be absorbed by writing `g` as `w ≫ g'`, which is what locality
provides. It transfers to an arbitrary localisation `Q` along the canonical bijection between the
hom sets of two localisations of the same class.

The second is that `Q.map` is injective on filtered homotopy classes: the presheaf
`X^• ↦ Hom_{K(Fil^f(𝒜))}(X^•, I^•)` of filtered homotopy classes inverts the class by part (1), so
it factors through `Q` up to isomorphism, and applying that factorisation to `f` and `g` and
evaluating at the class of `𝟙_{I^•}` turns `Q.map f = Q.map g` into the equality of the classes of
`f` and `g`.

Between the two lies the fact that filtered homotopic morphisms *do* have the same image, which is
what the cylinder above provides, and which the locality hypothesis of the first fact needs as
well. -/

section Localization


/-! #### Two general facts about localisations -/

section General

variable {C : Type*} [Category C] {E : Type*} [Category E]

open CategoryTheory.Localization.Construction

/-- The image in `W.Localization` of a path of the quiver of `C` and the formal inverses of the
morphisms of `W`, stated with source and target of the form `W.Q.obj _` so that it is syntactically
well-typed without unfolding the path category. -/
private def pathMap (W : MorphismProperty C) {a b : LocQuiver W} (p : Quiver.Path a b) :
    W.Q.obj a.obj ⟶ W.Q.obj b.obj :=
  (CategoryTheory.Quotient.functor (relations W)).map p

private lemma pathMap_nil (W : MorphismProperty C) (a : LocQuiver W) :
    pathMap W (Quiver.Path.nil : Quiver.Path a a) = 𝟙 _ :=
  (CategoryTheory.Quotient.functor (relations W)).map_id _

private lemma pathMap_cons (W : MorphismProperty C) {a b c : LocQuiver W} (p : Quiver.Path a b)
    (e : b ⟶ c) : pathMap W (p.cons e) = pathMap W p ≫ pathMap W e.toPath :=
  (CategoryTheory.Quotient.functor (relations W)).map_comp p e.toPath

private lemma pathMap_inl (W : MorphismProperty C) {a b : LocQuiver W} (u : a.obj ⟶ b.obj) :
    pathMap W (Quiver.Hom.toPath (Sum.inl u : a ⟶ b)) = W.Q.map u := rfl

private lemma pathMap_inr (W : MorphismProperty C) {a b : LocQuiver W} (w : b.obj ⟶ a.obj)
    (hw : W w) : pathMap W (Quiver.Hom.toPath (Sum.inr ⟨w, hw⟩ : a ⟶ b)) = (wIso w hw).inv := rfl

/-- The induction step: a path into `b` followed by a morphism `b.obj ⟶ I` is `W.Q.map` of a
single morphism out of the source of the path. -/
private lemma exists_map_eq_aux (W : MorphismProperty C) (I : C)
    (hloc : ∀ ⦃A B : C⦄ (w : A ⟶ B), W w → ∀ g : A ⟶ I,
      ∃ g' : B ⟶ I, W.Q.map (w ≫ g') = W.Q.map g)
    {a b : LocQuiver W} (p : Quiver.Path a b) :
    ∀ g : b.obj ⟶ I, ∃ f : a.obj ⟶ I, W.Q.map f = pathMap W p ≫ W.Q.map g := by
  induction p with
  | nil => exact fun g => ⟨g, by rw [pathMap_nil, Category.id_comp]⟩
  | @cons b' c q e ih =>
    obtain (u | ⟨w, hw⟩) := e
    · intro g
      obtain ⟨f, hf⟩ := ih (u ≫ g)
      refine ⟨f, ?_⟩
      rw [hf, pathMap_cons, pathMap_inl, W.Q.map_comp, Category.assoc]
    · intro g
      obtain ⟨g', hg'⟩ := hloc w hw g
      obtain ⟨f, hf⟩ := ih g'
      refine ⟨f, ?_⟩
      rw [hf, pathMap_cons, pathMap_inr, ← hg', W.Q.map_comp, Category.assoc]
      congr 1
      rw [show W.Q.map w = (wIso w hw).hom from rfl, Iso.inv_hom_id_assoc]

/-- **Every morphism into a local object in the localisation comes from the category.** If every
`g : A ⟶ I` factors through every `w : A ⟶ B` of `W` after applying `L`, then every morphism
`L.obj M ⟶ L.obj I` is `L.map` of a morphism `M ⟶ I`. -/
private lemma exists_map_eq_of_local (W : MorphismProperty C) (L : C ⥤ E) [L.IsLocalization W]
    (I : C)
    (hloc : ∀ ⦃A B : C⦄ (w : A ⟶ B), W w → ∀ g : A ⟶ I, ∃ g' : B ⟶ I, L.map (w ≫ g') = L.map g)
    (M : C) (φ : L.obj M ⟶ L.obj I) : ∃ f : M ⟶ I, L.map f = φ := by
  have hQ : ∀ ⦃A B : C⦄ (w : A ⟶ B), W w → ∀ g : A ⟶ I,
      ∃ g' : B ⟶ I, W.Q.map (w ≫ g') = W.Q.map g := by
    intro A B w hw g
    obtain ⟨g', hg'⟩ := hloc w hw g
    refine ⟨g', ?_⟩
    rw [← Localization.homEquiv_map W L W.Q (w ≫ g'), ← Localization.homEquiv_map W L W.Q g, hg']
  obtain ⟨p, hp⟩ : ∃ p : Quiver.Path (⟨M⟩ : LocQuiver W) ⟨I⟩,
      pathMap W p = Localization.homEquiv W L W.Q φ :=
    (CategoryTheory.Quotient.functor (relations W)).map_surjective _
  obtain ⟨f, hf⟩ := exists_map_eq_aux W I hQ p (𝟙 I)
  have key : pathMap W p ≫ W.Q.map (𝟙 I) = Localization.homEquiv W L W.Q φ := by
    rwa [W.Q.map_id, Category.comp_id]
  exact ⟨f, (Localization.homEquiv W L W.Q).injective
    ((Localization.homEquiv_map W L W.Q f).trans (hf.trans key))⟩

/-- The presheaf of classes of morphisms into `I` for a family of equivalence relations compatible
with precomposition. -/
private def relPresheaf (I : C) (r : ∀ X : C, Setoid (X ⟶ I))
    (hcomp : ∀ {X Y : C} (u : X ⟶ Y) {f g : Y ⟶ I}, (r Y).r f g → (r X).r (u ≫ f) (u ≫ g)) :
    Cᵒᵖ ⥤ Type _ where
  obj X := Quotient (r X.unop)
  map {X Y} u :=
    TypeCat.ofHom (Quotient.map (fun f => u.unop ≫ f) (fun _ _ h => hcomp u.unop h))
  map_id X := by
    ext q
    induction q using Quotient.ind with
    | _ f =>
      change Quotient.mk (r X.unop) (𝟙 X.unop ≫ f) = Quotient.mk (r X.unop) f
      rw [Category.id_comp]
  map_comp {X Y Z} u v := by
    ext q
    induction q using Quotient.ind with
    | _ f =>
      change Quotient.mk (r Z.unop) ((v.unop ≫ u.unop) ≫ f)
        = Quotient.mk (r Z.unop) (v.unop ≫ u.unop ≫ f)
      rw [Category.assoc]

private lemma relPresheaf_map_mk (I : C) (r : ∀ X : C, Setoid (X ⟶ I))
    (hcomp : ∀ {X Y : C} (u : X ⟶ Y) {f g : Y ⟶ I}, (r Y).r f g → (r X).r (u ≫ f) (u ≫ g))
    {X Y : Cᵒᵖ} (u : X ⟶ Y) (f : X.unop ⟶ I) :
    (relPresheaf I r hcomp).map u (Quotient.mk (r X.unop) f)
      = Quotient.mk (r Y.unop) (u.unop ≫ f) :=
  rfl

private lemma isInvertedBy_relPresheaf (W : MorphismProperty C) (I : C)
    (r : ∀ X : C, Setoid (X ⟶ I))
    (hcomp : ∀ {X Y : C} (u : X ⟶ Y) {f g : Y ⟶ I}, (r Y).r f g → (r X).r (u ≫ f) (u ≫ g))
    (hsurj : ∀ ⦃A B : C⦄ (w : A ⟶ B), W w → ∀ g : A ⟶ I, ∃ g' : B ⟶ I, (r A).r (w ≫ g') g)
    (hinj : ∀ ⦃A B : C⦄ (w : A ⟶ B), W w → ∀ g g' : B ⟶ I,
      (r A).r (w ≫ g) (w ≫ g') → (r B).r g g') :
    W.op.IsInvertedBy (relPresheaf I r hcomp) := by
  intro X Y u hu
  rw [CategoryTheory.isIso_iff_bijective]
  refine ⟨fun a b hab => ?_, fun q => ?_⟩
  · obtain ⟨ga⟩ := a
    obtain ⟨gb⟩ := b
    have hab' : Quotient.mk (r Y.unop) (u.unop ≫ ga)
        = Quotient.mk (r Y.unop) (u.unop ≫ gb) := hab
    exact Quotient.sound (hinj u.unop hu ga gb (Quotient.exact hab'))
  · obtain ⟨g⟩ := q
    obtain ⟨g', hg'⟩ := hsurj u.unop hu g
    exact ⟨Quotient.mk (r X.unop) g', Quotient.sound hg'⟩

/-- **The localisation is injective on classes of morphisms into a local object.** For a family of
equivalence relations on the morphisms into `I`, compatible with precomposition and turned into
bijections by the morphisms of `W`, two morphisms with the same image in the localisation are
related. -/
private lemma rel_of_map_eq_of_local (W : MorphismProperty C) (L : C ⥤ E) [L.IsLocalization W]
    (I : C) (r : ∀ X : C, Setoid (X ⟶ I))
    (hcomp : ∀ {X Y : C} (u : X ⟶ Y) {f g : Y ⟶ I}, (r Y).r f g → (r X).r (u ≫ f) (u ≫ g))
    (hsurj : ∀ ⦃A B : C⦄ (w : A ⟶ B), W w → ∀ g : A ⟶ I, ∃ g' : B ⟶ I, (r A).r (w ≫ g') g)
    (hinj : ∀ ⦃A B : C⦄ (w : A ⟶ B), W w → ∀ g g' : B ⟶ I,
      (r A).r (w ≫ g) (w ≫ g') → (r B).r g g')
    {M : C} {f g : M ⟶ I} (h : L.map f = L.map g) : (r M).r f g := by
  have hH : W.op.IsInvertedBy (relPresheaf I r hcomp) :=
    isInvertedBy_relPresheaf W I r hcomp hsurj hinj
  have e := Localization.fac (relPresheaf I r hcomp) hH L.op
  have hfg : (L.op ⋙ Localization.lift (relPresheaf I r hcomp) hH L.op).map f.op
      = (L.op ⋙ Localization.lift (relPresheaf I r hcomp) hH L.op).map g.op := by
    have hop : L.op.map f.op = L.op.map g.op := congrArg Quiver.Hom.op h
    rw [Functor.comp_map, Functor.comp_map, hop]
  have key : (relPresheaf I r hcomp).map f.op = (relPresheaf I r hcomp).map g.op := by
    have hcan : e.hom.app (Opposite.op I) ≫ (relPresheaf I r hcomp).map f.op
        = e.hom.app (Opposite.op I) ≫ (relPresheaf I r hcomp).map g.op := by
      rw [← e.hom.naturality f.op, ← e.hom.naturality g.op, hfg]
    exact (cancel_epi _).mp hcan
  have hval : (relPresheaf I r hcomp).map f.op (Quotient.mk (r I) (𝟙 I))
      = (relPresheaf I r hcomp).map g.op (Quotient.mk (r I) (𝟙 I)) := by rw [key]
  rw [relPresheaf_map_mk, relPresheaf_map_mk] at hval
  simp only [Quiver.Hom.unop_op, Category.comp_id] at hval
  exact Quotient.exact hval

end General

/-! #### Filtered homotopy as an equivalence relation -/


variable (Filf : ObjectProperty (FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ))
  (hFilf : ∀ K, Filf K ↔ ∀ n : ℤ, ∃ p q : ℤ,
    IsIso ((K.filtration.ι.app (op p)).f n) ∧ IsZero ((K.filtration.obj (op q)).X n))
  {D : Type u'} [Category.{v'} D] (Q : Filf.FullSubcategory ⥤ D)
  [Q.IsLocalization ((filteredQuasiIso 𝒜).inverseImage Filf.ι)]
  (I : Filf.FullSubcategory) (n₀ : ℤ) [I.obj.X.IsStrictlyGE n₀]
  (hI : ∀ p n : ℤ, Injective (((gr p).obj I.obj).X n))

/-- **Filtered homotopy is an equivalence relation** on the morphisms into a fixed filtered
complex: the zero homotopy, the negative of a filtered homotopy and the sum of two filtered
homotopies are filtered. -/
private def filteredHomotopySetoid (X : Filf.FullSubcategory) : Setoid (X ⟶ I) where
  r f g := ∃ h : Homotopy (Filf.ι.map f).hom (Filf.ι.map g).hom, IsFilteredHomotopy h
  iseqv :=
    { refl := fun f => ⟨Homotopy.refl _, fun i j =>
        IsFilteredComponent.of_eq (by simp [Homotopy.refl])
          (IsFilteredComponent.zero X.obj I.obj i j)⟩
      symm := fun ⟨h, hh⟩ => ⟨h.symm, fun i j =>
        IsFilteredComponent.of_eq (by simp [Homotopy.symm]) (IsFilteredComponent.neg (hh i j))⟩
      trans := fun ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩ => ⟨h₁.trans h₂, fun i j =>
        IsFilteredComponent.of_eq (by simp [Homotopy.trans])
          (IsFilteredComponent.add (hh₁ i j) (hh₂ i j))⟩ }

/-! #### Part (2) -/

include hFilf in
/-- **Filtered homotopic morphisms have the same image in the filtered derived category.** The
cylinder `Cyl(M)^•` is an object of `K(Fil^f(𝒜))`, its projection to `M^•` is a filtered
quasi-isomorphism, hence invertible in the localisation, so the two inclusions `M^• ⟶ Cyl(M)^•`,
being sections of it, have the same image; a filtered homotopy from `f` to `g` is a morphism
`Cyl(M)^• ⟶ J^•` restricting to `f` along one inclusion and to `g` along the other. -/
private lemma map_eq_of_filteredHomotopy {M J : Filf.FullSubcategory} (f g : M ⟶ J)
    (h : Homotopy (Filf.ι.map f).hom (Filf.ι.map g).hom) (hh : IsFilteredHomotopy h) :
    Q.map f = Q.map g := by
  have hMfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((M.obj.filtration.ι.app (op p)).f n) ∧
      IsZero ((M.obj.filtration.obj (op q)).X n) := (hFilf M.obj).1 M.property
  let Cyl : Filf.FullSubcategory :=
    ⟨cylFiltered M.obj, (hFilf _).2 (fin_cylFiltered M.obj hMfin)⟩
  let π : Cyl ⟶ M := ObjectProperty.homMk (cylπ M.obj)
  let i₀ : M ⟶ Cyl := ObjectProperty.homMk (cylι₀ M.obj)
  let i₁ : M ⟶ Cyl := ObjectProperty.homMk (cylι₁ M.obj)
  let H : Cyl ⟶ J := ObjectProperty.homMk (cylDesc M.obj (Filf.ι.map f) (Filf.ι.map g) h hh)
  have hπ : IsIso (Q.map π) :=
    Localization.inverts Q ((filteredQuasiIso 𝒜).inverseImage Filf.ι) π
      (filteredQuasiIso_cylπ M.obj)
  have e₀ : i₀ ≫ π = 𝟙 M := Filf.ι.map_injective (cylι₀_comp_cylπ M.obj)
  have e₁ : i₁ ≫ π = 𝟙 M := Filf.ι.map_injective (cylι₁_comp_cylπ M.obj)
  have hf : i₀ ≫ H = f :=
    Filf.ι.map_injective (cylι₀_comp_cylDesc M.obj (Filf.ι.map f) (Filf.ι.map g) h hh)
  have hg : i₁ ≫ H = g :=
    Filf.ι.map_injective (cylι₁_comp_cylDesc M.obj (Filf.ι.map f) (Filf.ι.map g) h hh)
  have key : Q.map i₀ = Q.map i₁ :=
    (cancel_mono (Q.map π)).1 (by rw [← Q.map_comp, ← Q.map_comp, e₀, e₁])
  rw [← hf, ← hg, Q.map_comp, Q.map_comp, key]

include hFilf n₀ hI in
/-- **Part (1), the surjectivity half**, for the objects of `K(Fil^f(𝒜))`: every `γ : K^• ⟶ I^•` is
filtered homotopic to `α ≫ β` for some `β : L^• ⟶ I^•`. -/
private lemma exists_comp_filteredHomotopy {K L : Filf.FullSubcategory} (α : K ⟶ L)
    (hα : (filteredQuasiIso 𝒜).inverseImage Filf.ι α) (γ : K ⟶ I) :
    ∃ β : L ⟶ I, ∃ h : Homotopy (Filf.ι.map (α ≫ β)).hom (Filf.ι.map γ).hom,
      IsFilteredHomotopy h := by
  obtain ⟨β, H, hH⟩ := exists_filtered_factorization (Filf.ι.map α) hα n₀
    ((hFilf K.obj).1 K.property) ((hFilf L.obj).1 L.property) ((hFilf I.obj).1 I.property) hI
    (Filf.ι.map γ)
  exact ⟨ObjectProperty.homMk β, H, hH⟩

include hFilf n₀ hI in
/-- **Part (1), the injectivity half**, for the objects of `K(Fil^f(𝒜))`: two morphisms which
become filtered homotopic after composition with `α` are filtered homotopic. -/
private lemma filteredHomotopy_of_comp {K L : Filf.FullSubcategory} (α : K ⟶ L)
    (hα : (filteredQuasiIso 𝒜).inverseImage Filf.ι α) (β β' : L ⟶ I)
    (hβ : ∃ h : Homotopy (Filf.ι.map (α ≫ β)).hom (Filf.ι.map (α ≫ β')).hom,
      IsFilteredHomotopy h) :
    ∃ h : Homotopy (Filf.ι.map β).hom (Filf.ι.map β').hom, IsFilteredHomotopy h := by
  obtain ⟨h, hh⟩ := hβ
  exact exists_filtered_homotopy (Filf.ι.map α) hα n₀
    ((hFilf K.obj).1 K.property) ((hFilf L.obj).1 L.property) ((hFilf I.obj).1 I.property) hI
    (Filf.ι.map β) (Filf.ι.map β') h hh

include hFilf n₀ hI in
/-- **Part (2).** For every `M^•` in `K(Fil^f(𝒜))` the localisation functor is a bijection from the
filtered homotopy classes of morphisms `M^• ⟶ I^•` onto `Hom_{DF(𝒜)}(M^•, I^•)`. -/
private lemma full_and_map_eq_iff_filteredHomotopy (M : Filf.FullSubcategory) :
    (∀ φ : Q.obj M ⟶ Q.obj I, ∃ f : M ⟶ I, Q.map f = φ) ∧
      ∀ f g : M ⟶ I, Q.map f = Q.map g ↔
        ∃ h : Homotopy (Filf.ι.map f).hom (Filf.ι.map g).hom, IsFilteredHomotopy h := by
  have hcomp : ∀ {X Y : Filf.FullSubcategory} (u : X ⟶ Y) {f g : Y ⟶ I},
      (filteredHomotopySetoid Filf I Y).r f g →
      (filteredHomotopySetoid Filf I X).r (u ≫ f) (u ≫ g) := by
    rintro X Y u f g ⟨h, hh⟩
    exact ⟨h.compLeft (Filf.ι.map u).hom, fun i j =>
      IsFilteredComponent.of_eq (by simp [Homotopy.compLeft])
        (IsFilteredComponent.comp_left (Filf.ι.map u) (hh i j))⟩
  have hsurj : ∀ ⦃A B : Filf.FullSubcategory⦄ (w : A ⟶ B),
      (filteredQuasiIso 𝒜).inverseImage Filf.ι w → ∀ g : A ⟶ I,
      ∃ g' : B ⟶ I, (filteredHomotopySetoid Filf I A).r (w ≫ g') g :=
    fun A B w hw g => exists_comp_filteredHomotopy Filf hFilf I n₀ hI w hw g
  have hinj : ∀ ⦃A B : Filf.FullSubcategory⦄ (w : A ⟶ B),
      (filteredQuasiIso 𝒜).inverseImage Filf.ι w → ∀ g g' : B ⟶ I,
      (filteredHomotopySetoid Filf I A).r (w ≫ g) (w ≫ g') →
      (filteredHomotopySetoid Filf I B).r g g' :=
    fun A B w hw g g' hgg' => filteredHomotopy_of_comp Filf hFilf I n₀ hI w hw g g' hgg'
  refine ⟨fun φ => exists_map_eq_of_local ((filteredQuasiIso 𝒜).inverseImage Filf.ι) Q I
      (fun A B w hw g => ?_) M φ,
    fun f g => ⟨fun hfg => rel_of_map_eq_of_local _ Q I (filteredHomotopySetoid Filf I) hcomp
      hsurj hinj hfg, fun ⟨h, hh⟩ => map_eq_of_filteredHomotopy Filf hFilf Q f g h hh⟩⟩
  obtain ⟨g', h, hh⟩ := hsurj w hw g
  exact ⟨g', map_eq_of_filteredHomotopy Filf hFilf Q (w ≫ g') g h hh⟩

end Localization

section Solution


variable {K L I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}

/-- **Part (1) for filtered complexes**, before the passage to `K(Fil^f(𝒜))` and its localisation:
for a filtered quasi-isomorphism `α : K^• ⟶ L^•` of filtered complexes with degreewise finite
filtrations and a bounded below `I^•` with injective graded pieces, precomposition with `α` is
bijective on filtered homotopy classes of morphisms into `I^•`. This is the source's statement of
part (1); part (1) of
`CochainComplex.bijective_precomp_full_and_map_eq_iff_filteredHomotopy_of_injective_gradedPiece`
is this one read in the full subcategory `Filf.FullSubcategory` of `K(Fil^f(𝒜))`. -/
private lemma bijective_precomp_of_injective_gradedPiece
    {K L I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : K ⟶ L)
    (hα : CochainComplex.filteredQuasiIso 𝒜 α) (n₀ : ℤ) [I.X.IsStrictlyGE n₀]
    (hKfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n))
    (hLfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((L.filtration.ι.app (op p)).f n) ∧
      IsZero ((L.filtration.obj (op q)).X n))
    (hIfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hI : ∀ p n : ℤ, Injective (((gr p).obj I).X n)) :
    (∀ γ : K ⟶ I, ∃ (β : L ⟶ I) (h : Homotopy (α.hom ≫ β.hom) γ.hom), ∀ i j p : ℤ,
        ∃ hp : (K.filtration.obj (op p)).X i ⟶ (I.filtration.obj (op p)).X j,
          hp ≫ (I.filtration.ι.app (op p)).f j
            = (K.filtration.ι.app (op p)).f i ≫ h.hom i j) ∧
      ∀ β β' : L ⟶ I, (∃ h : Homotopy (α.hom ≫ β.hom) (α.hom ≫ β'.hom), ∀ i j p : ℤ,
          ∃ hp : (K.filtration.obj (op p)).X i ⟶ (I.filtration.obj (op p)).X j,
            hp ≫ (I.filtration.ι.app (op p)).f j
              = (K.filtration.ι.app (op p)).f i ≫ h.hom i j) →
        ∃ h : Homotopy β.hom β'.hom, ∀ i j p : ℤ,
          ∃ hp : (L.filtration.obj (op p)).X i ⟶ (I.filtration.obj (op p)).X j,
            hp ≫ (I.filtration.ι.app (op p)).f j
              = (L.filtration.ι.app (op p)).f i ≫ h.hom i j :=
  ⟨fun γ => exists_filtered_factorization α hα n₀ hKfin hLfin hIfin hI γ,
    fun β β' ⟨h, hh⟩ => exists_filtered_homotopy α hα n₀ hKfin hLfin hIfin hI β β' h hh⟩

/-- **Homotopies out of a complex concentrated in degree `0` are degenerate**: if `X^•` vanishes
outside degree `0` and `Y^•` vanishes in negative degrees, then homotopic morphisms `X^• ⟶ Y^•`
are equal. In degree `0` the two components of the homotopy factor through `X^1` and through
`Y^{-1}`, both zero; in the other degrees the source is zero. -/
private lemma eq_of_homotopy_of_degreeZero {X Y : CochainComplex 𝒜 ℤ}
    [X.IsStrictlyGE 0] [X.IsStrictlyLE 0] [Y.IsStrictlyGE 0] {φ ψ : X ⟶ Y}
    (h : Homotopy φ ψ) : φ = ψ := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · have hd : X.d 0 1 = 0 := (X.isZero_of_isStrictlyLE 0 1 (by norm_num)).eq_of_tgt _ _
    have hh : h.hom 0 (-1) = 0 := (Y.isZero_of_isStrictlyGE 0 (-1) (by norm_num)).eq_of_tgt _ _
    have hcomm := h.comm 0
    rwa [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp), hd, hh, zero_comp,
      zero_comp, zero_add, zero_add] at hcomm
  · rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact (X.isZero_of_isStrictlyGE 0 n hlt).eq_of_src _ _
    · exact (X.isZero_of_isStrictlyLE 0 n hgt).eq_of_src _ _

end Solution

end CochainComplex.FilteredInjective.Hom

namespace CochainComplex

open FilteredInjective.Hom in
/-- **Stacks 05TY.** Let `𝒜` be an abelian category, let `Filf` be the class of filtered cochain
complexes of `𝒜` whose filtration is finite in each degree — so that `Filf.FullSubcategory` is
`K(Fil^f(𝒜))` — and let `Q` be a localisation of it at the filtered quasi-isomorphisms, that is,
the filtered derived category `DF(𝒜)` (Definition 05S2). Let `I^•` be a bounded below complex,
`I^n = 0` for `n < n₀`, consisting of filtered injective objects, that is with every `gr^p(I^n)`
an injective object of `𝒜`. Then:

1. for every filtered quasi-isomorphism `α : K^• ⟶ L^•` in `K(Fil^f(𝒜))`, precomposition with `α`
   is a bijection `Hom_{K(Fil^f(𝒜))}(L^•, I^•) ⟶ Hom_{K(Fil^f(𝒜))}(K^•, I^•)`: every
   `γ : K^• ⟶ I^•` is filtered homotopic to `α ≫ β` for some `β : L^• ⟶ I^•`, and if `α ≫ β` and
   `α ≫ β'` are filtered homotopic then so are `β` and `β'`;
2. for every `M^•` in `K(Fil^f(𝒜))`, `Hom_{K(Fil^f(𝒜))}(M^•, I^•) = Hom_{DF(𝒜)}(M^•, I^•)`: every
   `φ : Q.obj M^• ⟶ Q.obj I^•` is `Q.map f` for a morphism of filtered complexes `f : M^• ⟶ I^•`,
   and `Q.map f = Q.map g` exactly when `f` and `g` are filtered homotopic.

Here a *filtered homotopy* between morphisms of filtered complexes is a homotopy `h` of the
underlying complexes of `𝒜` each of whose components `h^{i,j}` carries `F^p` into `F^p`. -/
@[stacks 05TY]
public theorem bijective_precomp_full_and_map_eq_iff_filteredHomotopy_of_injective_gradedPiece
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {D : Type u'} [Category.{v'} D]
    (Filf : ObjectProperty (FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ))
    (hFilf : ∀ K, Filf K ↔ ∀ n : ℤ, ∃ p q : ℤ,
      IsIso ((K.filtration.ι.app (op p)).f n) ∧ IsZero ((K.filtration.obj (op q)).X n))
    (Q : Filf.FullSubcategory ⥤ D)
    [Q.IsLocalization ((filteredQuasiIso 𝒜).inverseImage Filf.ι)]
    (I : Filf.FullSubcategory) (n₀ : ℤ) [I.obj.X.IsStrictlyGE n₀]
    (hI : ∀ p n : ℤ, Injective (((gr p).obj I.obj).X n)) :
    (∀ (K L : Filf.FullSubcategory) (α : K ⟶ L),
        (filteredQuasiIso 𝒜).inverseImage Filf.ι α →
        (∀ γ : K ⟶ I, ∃ β : L ⟶ I,
          ∃ h : Homotopy (Filf.ι.map (α ≫ β)).hom (Filf.ι.map γ).hom, ∀ i j p : ℤ,
            ∃ hp : (K.obj.filtration.obj (op p)).X i ⟶ (I.obj.filtration.obj (op p)).X j,
              hp ≫ (I.obj.filtration.ι.app (op p)).f j
                = (K.obj.filtration.ι.app (op p)).f i ≫ h.hom i j) ∧
        ∀ β β' : L ⟶ I,
          (∃ h : Homotopy (Filf.ι.map (α ≫ β)).hom (Filf.ι.map (α ≫ β')).hom, ∀ i j p : ℤ,
            ∃ hp : (K.obj.filtration.obj (op p)).X i ⟶ (I.obj.filtration.obj (op p)).X j,
              hp ≫ (I.obj.filtration.ι.app (op p)).f j
                = (K.obj.filtration.ι.app (op p)).f i ≫ h.hom i j) →
          ∃ h : Homotopy (Filf.ι.map β).hom (Filf.ι.map β').hom, ∀ i j p : ℤ,
            ∃ hp : (L.obj.filtration.obj (op p)).X i ⟶ (I.obj.filtration.obj (op p)).X j,
              hp ≫ (I.obj.filtration.ι.app (op p)).f j
                = (L.obj.filtration.ι.app (op p)).f i ≫ h.hom i j) ∧
      ∀ M : Filf.FullSubcategory,
        (∀ φ : Q.obj M ⟶ Q.obj I, ∃ f : M ⟶ I, Q.map f = φ) ∧
        ∀ f g : M ⟶ I, Q.map f = Q.map g ↔
          ∃ h : Homotopy (Filf.ι.map f).hom (Filf.ι.map g).hom, ∀ i j p : ℤ,
            ∃ hp : (M.obj.filtration.obj (op p)).X i ⟶ (I.obj.filtration.obj (op p)).X j,
              hp ≫ (I.obj.filtration.ι.app (op p)).f j
                = (M.obj.filtration.ι.app (op p)).f i ≫ h.hom i j :=
  ⟨fun _ _ α hα =>
      ⟨fun γ => exists_comp_filteredHomotopy Filf hFilf I n₀ hI α hα γ,
        fun β β' hβ => filteredHomotopy_of_comp Filf hFilf I n₀ hI α hα β β' hβ⟩,
    fun M => full_and_map_eq_iff_filteredHomotopy Filf hFilf Q I n₀ hI M⟩

open FilteredInjective.Hom in
/-- **Stacks 05TU.** Let `𝒜` be an abelian category, let `f : A ⟶ B` be a morphism of filtered
objects, placed in degree `0` by taking the filtered complexes `A` and `B` to be concentrated in
degree `0`, and let `a : A[0] ⟶ I^•` and `b : B[0] ⟶ J^•` be morphisms into filtered complexes with
degreewise finite filtrations, where `a` is a filtered quasi-isomorphism and `J^•` vanishes in
negative degrees and consists of filtered injective objects, i.e. every term `(J^n, F^• J^n)` is a
filtered injective object of `Fil^f(𝒜)`. Then `f` lifts to a morphism `g : I^• ⟶ J^•` with
`a ≫ g = f ≫ b` on the nose.

This is the lift that `CochainComplex.FilteredInjectiveResolution.exists_resolutionSystem` needs.

Three of the source's hypotheses are unused here and dropped: that `b` be a filtered
quasi-isomorphism, and that `I^•` vanish in negative degrees and have filtered injective graded
pieces. The lift comes from the surjectivity half of [Stacks, Tag 05TY], which asks only that `a`
be a filtered quasi-isomorphism into a complex of `K(Fil^f(𝒜))` and that the target `J^•` be
bounded below and filtered injective; the homotopy it produces is degenerate because `A` is
concentrated in degree `0`, which turns the commutation in `K(Fil^f(𝒜))` into an equality of
morphisms of filtered complexes. -/
@[stacks 05TU, ega "0 13.6.3" "special case"]
public theorem exists_hom_comp_eq_of_filteredQuasiIso_of_injective_gradedPiece
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B I J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [A.X.IsStrictlyGE 0] [A.X.IsStrictlyLE 0] [J.X.IsStrictlyGE 0]
    (f : A ⟶ B) (a : A ⟶ I) (b : B ⟶ J) (ha : filteredQuasiIso 𝒜 a)
    (hAfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((A.filtration.ι.app (op p)).f n) ∧
      IsZero ((A.filtration.obj (op q)).X n))
    (hIfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hJ : ∀ n : ℤ, (evalFil J n).IsFilteredInjective) :
    ∃ g : I ⟶ J, a ≫ g = f ≫ b := by
  obtain ⟨g, H, -⟩ := exists_filtered_factorization a ha 0 hAfin hIfin
    (fun n => ((isFilteredInjective_evalFil_iff J n).1 (hJ n)).1)
    (fun p n => ((isFilteredInjective_evalFil_iff J n).1 (hJ n)).2 p) (f ≫ b)
  exact ⟨g, FilteredObject.hom_ext (eq_of_homotopy_of_degreeZero H)⟩

end CochainComplex

end FilteredInjectiveHom

end
