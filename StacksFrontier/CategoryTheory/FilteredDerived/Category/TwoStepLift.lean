module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ShortExactFiltration
public import StacksFrontier.Homology.FilteredDerivedCategory.Triangulated
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.MorphismsIntoBoundedBelowInjectives
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Lifting morphisms of short exact sequences into filtered injective ones

Let `ι : S ⟶ T` be a morphism of short exact sequences of cochain complexes which is a filtered
quasi-isomorphism of the two-step filtered complexes, and let `T'` be a short exact sequence whose
two-step filtered complex is a bounded below complex of filtered injective objects. Then every
morphism `c : S ⟶ T'` factors, in the filtered derived category, through `ι` by a morphism of
short exact sequences `g : T ⟶ T'`. This is how a morphism of short exact sequences, such as the
Frobenius `0 → j_!j^{-1}K → K → i_*i^{-1}K → 0 ⟶ π_*(…)` of Step 1 of the proof of
[Stacks, Tag 03UG], is realised on an injective resolution compatibly with the filtration.

## Main results

* `CochainComplex.exists_twoStepComplexMap_comp_eq`: the factorisation.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1.
* [Stacks Project, Tag 05TX](https://stacks.math.columbia.edu/tag/05TX).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
  {S T T' : ShortComplex (CochainComplex 𝒜 ℤ)} [∀ n, Mono (S.f.f n)] [∀ n, Mono (T.f.f n)]
  [∀ n, Mono (T'.f.f n)]

/-- A morphism commuting with isomorphisms to a quasi-isomorphism is a quasi-isomorphism. -/
private theorem quasiIso_of_comp_iso_hom_eq {K L K' L' : CochainComplex 𝒜 ℤ} {f : K ⟶ L}
    {g : K' ⟶ L'} (eK : K ≅ K') (eL : L ≅ L') (h : f ≫ eL.hom = eK.hom ≫ g) [QuasiIso g] :
    QuasiIso f :=
  (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk eK eL h.symm)).2 ‹_›

/-- Two morphisms with equal image in the derived category are equal there after transport along
isomorphisms. -/
private theorem Q_map_eq_of_comp_iso_hom_eq [HasDerivedCategory 𝒜] {K L K' L' : CochainComplex 𝒜 ℤ}
    {f f' : K ⟶ L} {g g' : K' ⟶ L'} (eK : K ≅ K') (eL : L ≅ L') (hf : f ≫ eL.hom = eK.hom ≫ g)
    (hf' : f' ≫ eL.hom = eK.hom ≫ g')
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map f') :
    DerivedCategory.Q.map g = DerivedCategory.Q.map g' := by
  rw [← cancel_epi (DerivedCategory.Q.map eK.hom), ← Functor.map_comp, ← Functor.map_comp, ← hf,
    ← hf', Functor.map_comp, Functor.map_comp, h]

/-- **A morphism into a filtered injective short exact sequence factors through a filtered
quasi-isomorphism**, in the filtered derived category: for `ι : S ⟶ T` with
`twoStepComplexMap ι` a filtered quasi-isomorphism, `T` short exact, and `twoStepComplex T'` a
bounded below complex of filtered injectives, every `c : S ⟶ T'` is `ι ≫ g` up to filtered
homotopy, for some morphism of short complexes `g : T ⟶ T'`. -/
theorem exists_twoStepComplexMap_comp_eq (hT : T.ShortExact) (ι : S ⟶ T)
    (hι : filteredQuasiIsoC (twoStepComplexMap ι))
    (hT' : FilteredDerivedCategory.filteredInjectivePlusC 𝒜 (twoStepComplex T')) (c : S ⟶ T') :
    ∃ g : T ⟶ T', FilteredDerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map (twoStepComplexMap (ι ≫ g))) =
      FilteredDerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map (twoStepComplexMap c)) := by
  have hf : HomotopyCategory.filteredQuasiIso 𝒜
      ((HomotopyCategory.quotient _ _).map (twoStepComplexMap ι)) :=
    (filteredQuasiIso_quotient_map_iff _).2 hι
  have : IsIso (FilteredDerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (twoStepComplexMap ι))) :=
    Localization.inverts _ _ _ hf
  have hI : FilteredDerivedCategory.filteredInjectivePlus 𝒜
      ((HomotopyCategory.quotient _ _).obj (twoStepComplex T')) :=
    (ObjectProperty.strictMap_iff _ _ _).2 ⟨_, hT', rfl⟩
  obtain ⟨h, hh⟩ := (FilteredDerivedCategory.map_bijective_Qh_of_filteredInjectivePlus
    ((HomotopyCategory.quotient _ _).obj (twoStepComplex T)) hI).2
      (inv (FilteredDerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map (twoStepComplexMap ι))) ≫
        FilteredDerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ _).map (twoStepComplexMap c)))
  obtain ⟨h', rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective h
  refine ⟨twoStepComplexUnmap hT h', ?_⟩
  rw [twoStepComplexMap_comp, twoStepComplexMap_twoStepComplexUnmap, Functor.map_comp,
    Functor.map_comp, hh, IsIso.hom_inv_id_assoc]

/-- **Morphisms of short exact sequences into a filtered injective one that agree in the filtered
derived category agree componentwise in the derived category.** -/
theorem Q_map_τ_eq_of_Qh_map_twoStepComplexMap_eq [HasDerivedCategory 𝒜]
    (hS : S.ShortExact) (hT' : T'.ShortExact)
    (hI : FilteredDerivedCategory.filteredInjectivePlusC 𝒜 (twoStepComplex T')) (x y : S ⟶ T')
    (h : FilteredDerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map (twoStepComplexMap x)) =
      FilteredDerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map (twoStepComplexMap y))) :
    DerivedCategory.Q.map x.τ₁ = DerivedCategory.Q.map y.τ₁ ∧
      DerivedCategory.Q.map x.τ₂ = DerivedCategory.Q.map y.τ₂ ∧
      DerivedCategory.Q.map x.τ₃ = DerivedCategory.Q.map y.τ₃ := by
  have hI' : FilteredDerivedCategory.filteredInjectivePlus 𝒜
      ((HomotopyCategory.quotient _ _).obj (twoStepComplex T')) :=
    (ObjectProperty.strictMap_iff _ _ _).2 ⟨_, hI, rfl⟩
  have hq := (FilteredDerivedCategory.map_bijective_Qh_of_filteredInjectivePlus
    ((HomotopyCategory.quotient _ _).obj (twoStepComplex S)) hI').1 h
  have H := HomotopyCategory.homotopyOfEq _ _ hq
  have key : ∀ (G : FiniteFilteredObject 𝒜 ⥤ 𝒜) [G.Additive],
      DerivedCategory.Q.map ((G.mapHomologicalComplex _).map (twoStepComplexMap x)) =
        DerivedCategory.Q.map ((G.mapHomologicalComplex _).map (twoStepComplexMap y)) :=
    fun G _ => DerivedCategory.Q_map_eq_of_homotopy (h := G.mapHomotopy H)
  exact ⟨Q_map_eq_of_comp_iso_hom_eq _ _ (twoStepComplexGrOneIso_hom_naturality S x)
      (twoStepComplexGrOneIso_hom_naturality S y) (key (FiniteFilteredObject.grP 1)),
    Q_map_eq_of_comp_iso_hom_eq _ _ (twoStepComplexForgetIso_hom_naturality S x)
      (twoStepComplexForgetIso_hom_naturality S y) (key FiniteFilteredObject.forget),
    Q_map_eq_of_comp_iso_hom_eq _ _ (twoStepComplexGrZeroIso_hom_naturality S hS hT' x)
      (twoStepComplexGrZeroIso_hom_naturality S hS hT' y) (key (FiniteFilteredObject.grP 0))⟩

/-! ### Injective resolutions of short exact sequences -/

section Resolution

open HomComplex

variable {S : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact)
  {I₁ : CochainComplex 𝒜 ℤ} [∀ n, Injective (I₁.X n)] (α : S.X₁ ⟶ I₁)

include hS in
/-- In a short exact sequence of cochain complexes, each component of the first morphism is a
monomorphism. -/
lemma mono_f_f_of_shortExact (n : ℤ) : Mono (S.f.f n) :=
  (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).mono_f

include hS in
/-- In a short exact sequence of cochain complexes, each component of the second morphism is an
epimorphism. -/
lemma epi_g_f_of_shortExact (n : ℤ) : Epi (S.g.f n) :=
  (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).epi_g

/-- A degreewise extension of `α : X₁ ⟶ I₁` along `X₁ ⟶ X₂` to a `0`-cochain `X₂ ⟶ I₁`, which
exists since the terms of `I₁` are injective. -/
def resβ₀ : Cochain S.X₂ I₁ 0 :=
  Cochain.ofHoms fun n =>
    haveI := mono_f_f_of_shortExact hS n
    Injective.factorThru (α.f n) (S.f.f n)

/-- The composite of `S.f` with `resβ₀ hS α` is `α`. -/
lemma ofHom_f_comp_resβ₀ : (Cochain.ofHom S.f).comp (resβ₀ hS α) (zero_add 0) =
    Cochain.ofHom α := by
  ext p
  simp [resβ₀]

/-- The `1`-cochain on `X₃` through which `δ (resβ₀ hS α)` factors along `X₂ ⟶ X₃`. -/
def resC : Cochain S.X₃ I₁ 1 :=
  Cochain.mk fun p q hpq =>
    haveI := (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) p)).epi_g
    (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) p)).exact.desc
      ((δ 0 1 (resβ₀ hS α)).v p q hpq) (by
        have h := Cochain.congr_v (congrArg (δ 0 1) (ofHom_f_comp_resβ₀ hS α)) p q hpq
        rw [δ_ofHom_comp, δ_ofHom, Cochain.zero_v, Cochain.zero_cochain_comp_v,
          Cochain.ofHom_v] at h
        exact h)

/-- The composite of `S.g` with `resC hS α` is `δ (resβ₀ hS α)`. -/
lemma ofHom_g_comp_resC : (Cochain.ofHom S.g).comp (resC hS α) (zero_add 1) =
    δ 0 1 (resβ₀ hS α) := by
  ext p q hpq
  have := (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) p)).epi_g
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) p)).exact.g_desc _ _

/-- The cochain `resC hS α` is a cocycle. -/
lemma δ_resC : δ 1 2 (resC hS α) = 0 := by
  ext p q hpq
  have := epi_g_f_of_shortExact hS p
  rw [← cancel_epi (S.g.f p)]
  have h := Cochain.congr_v (congrArg (δ 1 2) (ofHom_g_comp_resC hS α)) p q hpq
  rw [δ_ofHom_comp, δ_δ, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h
  rw [h, Cochain.zero_v, Cochain.zero_v, comp_zero]

/-- `resC` as a `1`-cocycle. -/
def resCocycle : Cocycle S.X₃ I₁ 1 := Cocycle.mk (resC hS α) 2 (by omega) (δ_resC hS α)

/-- The chain map `X₃⟦-1⟧ ⟶ I₁` classifying the extension, up to sign. -/
def resCMap : S.X₃⟦(-1 : ℤ)⟧ ⟶ I₁ :=
  -Cocycle.homOf ((resCocycle hS α).leftShift (-1) 0 (by omega))

variable [HasDerivedCategory 𝒜]

/-- A morphism into a bounded below complex of injectives extends along a quasi-isomorphism,
up to homotopy. -/
lemma exists_homotopy_extend {K K' I : CochainComplex 𝒜 ℤ} (hI : CochainComplex.plus 𝒜 I)
    [∀ n, Injective (I.X n)] (q : K ⟶ K') [QuasiIso q] (f : K ⟶ I) :
    ∃ g : K' ⟶ I, Nonempty (Homotopy (q ≫ g) f) := by
  obtain ⟨gh, hgh⟩ := (Qh_map_bijective_of_injective_of_plus
    ((HomotopyCategory.quotient _ _).obj K') I hI).2
      ((DerivedCategory.quotientCompQhIso 𝒜).hom.app K' ≫ inv (DerivedCategory.Q.map q) ≫
        DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso 𝒜).inv.app I)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective gh
  have hg : DerivedCategory.Q.map g = inv (DerivedCategory.Q.map q) ≫ DerivedCategory.Q.map f := by
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso 𝒜).hom.app K'),
      ← DerivedCategory.quotientCompQhIso_hom_naturality, hgh]
    simp
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (Qh_map_bijective_of_injective_of_plus ((HomotopyCategory.quotient _ _).obj K) I hI).1
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso 𝒜).hom.app I),
    DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, Functor.map_comp, hg]
  simp

variable {I₃ : CochainComplex 𝒜 ℤ} (hI₁ : CochainComplex.plus 𝒜 I₁) (γ : S.X₃ ⟶ I₃)
  [QuasiIso γ]

/-- The morphism `I₃⟦-1⟧ ⟶ I₁` classifying the resolved extension: an extension of
`resCMap` along `γ⟦-1⟧`. -/
def resφ : I₃⟦(-1 : ℤ)⟧ ⟶ I₁ :=
  (exists_homotopy_extend hI₁ (γ⟦(-1 : ℤ)⟧') (resCMap hS α)).choose

/-- The homotopy `γ⟦-1⟧ ≫ resφ ∼ resCMap`. -/
def resH : Homotopy (γ⟦(-1 : ℤ)⟧' ≫ resφ hS α hI₁ γ) (resCMap hS α) :=
  (exists_homotopy_extend hI₁ (γ⟦(-1 : ℤ)⟧') (resCMap hS α)).choose_spec.some

/-- The corrected degree `0` component of the comparison into the mapping cone. -/
def resβ : Cochain S.X₂ I₁ 0 :=
  resβ₀ hS α + (Cochain.ofHom S.g).comp
    ((Cochain.equivHomotopy _ _ (resH hS α hI₁ γ)).1.leftUnshift 0 (by omega)) (zero_add 0)

/-- The degree `1` component of the comparison into the mapping cone. -/
def resα : Cocycle S.X₂ (I₃⟦(-1 : ℤ)⟧) 1 :=
  -(Cocycle.ofHom (S.g ≫ γ)).rightShift (-1) 1 (by omega)

/-- The relation `δ resβ + resα ≫ resφ = 0` between the components of a morphism into the
mapping cone of `resφ hS α hI₁ γ`. -/
lemma resEq : δ 0 1 (resβ hS α hI₁ γ) +
    (resα γ).1.comp (Cochain.ofHom (resφ hS α hI₁ γ)) (add_zero 1) = 0 := by
  set z := (Cochain.equivHomotopy _ _ (resH hS α hI₁ γ)).1 with hz
  have h : δ (-1) 0 z = Cochain.ofHom (γ⟦(-1 : ℤ)⟧' ≫ resφ hS α hI₁ γ) -
      Cochain.ofHom (resCMap hS α) :=
    eq_sub_of_add_eq (Cochain.equivHomotopy _ _ (resH hS α hI₁ γ)).2.symm
  have hη : δ 0 1 (z.leftUnshift 0 (by omega)) =
      -((Cochain.ofHom (γ⟦(-1 : ℤ)⟧' ≫ resφ hS α hI₁ γ)).leftUnshift 1 (by omega)) -
        resC hS α := by
    rw [Cochain.δ_leftUnshift _ 0 _ 1 0 (by omega), h]
    simp [resCMap, resCocycle, Cochain.leftUnshift_add, sub_eq_add_neg,
      Cochain.leftUnshift_leftShift]
  rw [resβ, δ_add, ← ofHom_g_comp_resC hS α, δ_ofHom_comp, hη]
  ext p q hpq
  simp only [resα, Cochain.add_v, Cochain.neg_v, Cochain.sub_v, Cochain.comp_zero_cochain_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cocycle.coe_neg, Cocycle.rightShift_coe,
    Cocycle.ofHom_coe, Cochain.zero_v]
  rw [Cochain.rightShift_v _ (-1) 1 (by omega) p q hpq p (by omega),
    Cochain.leftUnshift_v _ 1 (by omega) p q hpq (p + 1) (by omega)]
  obtain rfl : q = p + 1 := hpq.symm
  rw [show (-1 * 0 + -1 * (-1 - 1) / 2 : ℤ).negOnePow = -1 from rfl]
  simp only [Cochain.ofHom_v, HomologicalComplex.comp_f, Preadditive.comp_sub,
    Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc,
    CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso]
  simp [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc]

/-- The comparison morphism `X₂ ⟶ C` into the mapping cone of `resφ`. -/
def resΨ : S.X₂ ⟶ mappingCone (resφ hS α hI₁ γ) :=
  mappingCone.lift _ (resα γ) (resβ hS α hI₁ γ) (resEq hS α hI₁ γ)

/-- The degreewise split short exact sequence `I₁ ⟶ C ⟶ I₃⟦-1⟧⟦1⟧` of the mapping cone. -/
abbrev resShortComplex : ShortComplex (CochainComplex 𝒜 ℤ) :=
  mappingCone.triangleRotateShortComplex (resφ hS α hI₁ γ)

/-- The third component of the comparison: `X₃ ⟶ I₃ ≅ I₃⟦-1⟧⟦1⟧`. -/
def resτ₃ : S.X₃ ⟶ (I₃⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ :=
  γ ≫ (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (-1 : ℤ) 1 (by omega)).inv.app I₃

/-- The composite of `S.f` with `resΨ hS α hI₁ γ` is `α` followed by the inclusion of `I₁`
into the mapping cone. -/
lemma f_comp_resΨ : S.f ≫ resΨ hS α hI₁ γ = α ≫ mappingCone.inr _ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  refine mappingCone.ext_to _ p (p + 1) rfl ?_ ?_
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      resΨ, mappingCone.lift_f_fst_v, mappingCone.inr_f_fst_v, comp_zero]
    simp only [resα, Cocycle.coe_neg, Cochain.neg_v, Cocycle.rightShift_coe, Cocycle.ofHom_coe,
      Preadditive.comp_neg, neg_eq_zero]
    rw [Cochain.rightShift_v _ (-1) 1 (by omega) p (p + 1) rfl p (by omega), Cochain.ofHom_v,
      ← Category.assoc, ← HomologicalComplex.comp_f, ← Category.assoc, S.zero, zero_comp,
      HomologicalComplex.zero_f, zero_comp]
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      resΨ, mappingCone.lift_f_snd_v, mappingCone.inr_f_snd_v, Category.comp_id]
    have h := Cochain.congr_v (ofHom_f_comp_resβ₀ hS α) p p (add_zero p)
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h
    simp only [resβ, Cochain.add_v, Preadditive.comp_add, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, h, ← Category.assoc, ← HomologicalComplex.comp_f, S.zero,
      HomologicalComplex.zero_f, zero_comp, add_zero]

/-- The composite of `resΨ hS α hI₁ γ` with the projection of the mapping cone sequence is
`S.g ≫ resτ₃ γ`. -/
lemma resΨ_comp_g :
    resΨ hS α hI₁ γ ≫ (resShortComplex hS α hI₁ γ).g = S.g ≫ resτ₃ γ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  have e : (resΨ hS α hI₁ γ ≫ (resShortComplex hS α hI₁ γ).g).f p =
      (resΨ hS α hI₁ γ).f p ≫ (mappingCone.triangle (resφ hS α hI₁ γ)).mor₃.f p := rfl
  have k1 := mappingCone.inl_v_triangle_mor₃_f (resφ hS α hI₁ γ) (p + 1) p (by omega)
  have k2 := mappingCone.inr_f_triangle_mor₃_f (resφ hS α hI₁ γ) p
  have hf : (resΨ hS α hI₁ γ).f p = (resα γ).1.v p (p + 1) rfl ≫
      (mappingCone.inl (resφ hS α hI₁ γ)).v (p + 1) p (by omega) +
      (resβ hS α hI₁ γ).v p p (add_zero p) ≫ (mappingCone.inr (resφ hS α hI₁ γ)).f p :=
    mappingCone.lift_f _ _ _ _ p (p + 1) rfl
  rw [e, hf]
  refine ((Preadditive.add_comp _ _ _ _ _ _).trans (congrArg₂ (· + ·)
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) k1))
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) k2)))).trans ?_
  rw [comp_zero, add_zero]
  simp only [resα, Cocycle.coe_neg, Cochain.neg_v, Cocycle.rightShift_coe, Cocycle.ofHom_coe]
  rw [Cochain.rightShift_v _ (-1) 1 (by omega) p (p + 1) rfl p (by omega), Cochain.ofHom_v]
  simp only [resτ₃, shiftFunctorCompIsoId, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    HomologicalComplex.comp_f, CochainComplex.shiftFunctorAdd'_hom_app_f',
    CochainComplex.shiftFunctorZero_inv_app_f]
  simp only [Int.reduceNeg, shiftFunctor_obj_X', shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq, eqToIso.inv, Category.assoc, add_neg_cancel_right,
    eqToHom_naturality, eqToHom_naturality_assoc, eqToIso_refl, Iso.refl_inv, eqToIso.hom,
    eqToHom_trans]
  exact (Preadditive.comp_neg _ _).trans
    ((congrArg Neg.neg (Category.comp_id _)).trans (neg_neg _))

/-- **The injective resolution of a short exact sequence**: the comparison morphism from `S` to the
mapping cone sequence, which is `α` on the subobject and `γ` on the quotient. -/
@[simps]
def resMap : S ⟶ resShortComplex hS α hI₁ γ where
  τ₁ := α
  τ₂ := resΨ hS α hI₁ γ
  τ₃ := resτ₃ γ
  comm₁₂ := (f_comp_resΨ hS α hI₁ γ).symm
  comm₂₃ := resΨ_comp_g hS α hI₁ γ

/-- The mapping cone sequence `resShortComplex hS α hI₁ γ` is short exact. -/
lemma resShortComplex_shortExact : (resShortComplex hS α hI₁ γ).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    (mappingCone.triangleRotateShortComplexSplitting (resφ hS α hI₁ γ) n).shortExact

/-- Each component of the first morphism of `resShortComplex hS α hI₁ γ` is a monomorphism. -/
instance (n : ℤ) : Mono ((resShortComplex hS α hI₁ γ).f.f n) :=
  ((resShortComplex_shortExact hS α hI₁ γ).map_of_exact
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).mono_f

omit [HasDerivedCategory 𝒜] in
/-- A morphism between zero complexes is a quasi-isomorphism. -/
lemma quasiIso_of_isZero' {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) (hK : IsZero K)
    (hL : IsZero L) : QuasiIso f := by
  have := isIso_of_source_target_iso_zero f hK.isoZero hL.isoZero
  infer_instance

/-- **The cone resolution is a filtered quasi-isomorphism** on the two-step filtered complexes. -/
lemma filteredQuasiIsoC_twoStepComplexMap_resMap [∀ n, Mono (S.f.f n)] [QuasiIso α] :
    filteredQuasiIsoC (twoStepComplexMap (resMap hS α hI₁ γ)) := by
  intro p
  by_cases hp1 : p = 1
  · subst hp1
    have h := twoStepComplexGrOneIso_hom_naturality S (resMap hS α hI₁ γ)
    rw [resMap_τ₁] at h
    exact quasiIso_of_comp_iso_hom_eq (g := α) (twoStepComplexGrOneIso S)
      (twoStepComplexGrOneIso (resShortComplex hS α hI₁ γ)) h
  by_cases hp0 : p = 0
  · subst hp0
    have h := twoStepComplexGrZeroIso_hom_naturality S hS
      (resShortComplex_shortExact hS α hI₁ γ) (resMap hS α hI₁ γ)
    rw [resMap_τ₃] at h
    have : QuasiIso (resτ₃ γ) := by unfold resτ₃; infer_instance
    exact quasiIso_of_comp_iso_hom_eq (g := resτ₃ γ) (twoStepComplexGrZeroIso S hS)
      (twoStepComplexGrZeroIso _ (resShortComplex_shortExact hS α hI₁ γ)) h
  · exact quasiIso_of_isZero' _ (isZero_twoStepComplex_grP S hp0 hp1)
      (isZero_twoStepComplex_grP _ hp0 hp1)

/-- **The cone resolution is a bounded below complex of filtered injectives.** -/
lemma filteredInjectivePlusC_twoStepComplex_res (hI₃ : CochainComplex.plus 𝒜 I₃)
    [∀ n, Injective (I₃.X n)] :
    FilteredDerivedCategory.filteredInjectivePlusC 𝒜
      (twoStepComplex (resShortComplex hS α hI₁ γ)) := by
  have ha₁ := hI₁.choose_spec
  have ha₃ := hI₃.choose_spec
  refine ⟨⟨min hI₁.choose hI₃.choose, (isStrictlyGE_iff _ _).2 fun i hi => ?_⟩, fun n p => ?_⟩
  · rw [IsZero.iff_id_eq_zero]
    ext1
    refine FilteredObject.hom_ext (IsZero.eq_of_src ?_ _ _)
    exact (mappingCone.isZero_X_iff (resφ hS α hI₁ γ) i).2
      ⟨CochainComplex.isZero_of_isStrictlyGE I₃ hI₃.choose (i + 1 + -1) (by omega),
        CochainComplex.isZero_of_isStrictlyGE I₁ hI₁.choose i (by omega)⟩
  by_cases hp1 : p = 1
  · subst hp1
    exact Injective.of_iso (FilteredObject.twoStepGrOneIso _).symm
      (inferInstanceAs (Injective (I₁.X n)))
  by_cases hp0 : p = 0
  · subst hp0
    exact Injective.of_iso (FilteredObject.twoStepGrZeroIso _
      (degreeShortComplex_shortExact _ (resShortComplex_shortExact hS α hI₁ γ) n)).symm
      (inferInstanceAs (Injective (I₃.X (n + 1 + -1))))
  · refine IsZero.injective ?_
    rcases lt_or_gt_of_ne hp0 with h | h
    · exact FilteredObject.isZero_gr_twoStep_of_neg _ h
    · exact FilteredObject.isZero_gr_twoStep_of_two_le _ (by omega)

end Resolution

end CochainComplex
