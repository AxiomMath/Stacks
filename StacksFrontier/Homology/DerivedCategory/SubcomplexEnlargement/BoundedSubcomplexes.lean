module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration
public import StacksFrontier.Algebra.Module.ProjResComplexFlat
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TorAmplitude.ProjResKFlat

@[expose] public noncomputable section

/-!
# Bounded subcomplexes and filtered colimits of modules

Auxiliary results for enlarging subcomplexes compatibly with derived base change: cohomology of
complexes of modules commutes with filtered colimits, degreewise sets of bounded size generate
subcomplexes of bounded size, and compatible pairs of subcomplexes can be enlarged with controlled
cardinality.

## Implementation notes

Subcomplexes are represented by complexes equipped with monomorphisms into the ambient complexes.
The cardinality of a complex is represented by the cardinality of the disjoint union of its terms.

## References

* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
-/

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SubcomplexEnlargement

universe u v w t

attribute [local instance] HasDerivedCategory.standard

/-- Filtered colimits of modules are exact when the module universe is larger
than the universe of the coefficient ring. -/
private lemma exactFilteredColimitsOfModules
    {R : Type u} [Ring R] {J : Type (max u v)}
    [SmallCategory J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{max u v} R) := by
  let F := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}
  have : PreservesFiniteLimits F := inferInstance
  have : ReflectsFiniteLimits F := inferInstance
  have : PreservesColimitsOfShape J F := inferInstance
  have : HasExactColimitsOfShape J AddCommGrpCat.{max u v} := inferInstance
  exact HasExactColimitsOfShape.domain_of_functor J F

/-- Termwise extension of scalars preserves colimits of small diagrams of complexes. -/
private lemma extendScalarsComplex_preservesColimitsOfShape
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    {J : Type (max u v t)} [SmallCategory J] :
    PreservesColimitsOfShape J
      ((ModuleCat.extendScalars.{u, v, max v (max u t)} f).mapHomologicalComplex
        (ComplexShape.up ℤ)) := by
  let E := ModuleCat.extendScalars.{u, v, max v (max u t)} f
  let : E.IsLeftAdjoint := ModuleCat.instIsLeftAdjointExtendScalars.{u, v, max u t} f
  have hcolim : PreservesColimitsOfShape J E := inferInstance
  have hzero : E.PreservesZeroMorphisms := inferInstance
  let := hcolim
  let := hzero
  infer_instance

/-- The short complex around a fixed degree commutes with degreewise colimits. -/
private lemma shortComplexFunctor_preservesColimitsOfShape
    {R : Type u} [CommRing R] {J : Type (max u v)} [SmallCategory J]
    (i : ℤ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) i) := by
  constructor
  intro K
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
  · exact isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
        ((ComplexShape.up ℤ).prev i)) (colimit.isColimit K)
  · exact isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i)
      (colimit.isColimit K)
  · exact isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
        ((ComplexShape.up ℤ).next i)) (colimit.isColimit K)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def shortComplexHomologyFunctorIso
    {R : Type u} [CommRing R] {J : Type (max u v)} [SmallCategory J]
    (K : J ⥤ ShortComplex (ModuleCat.{max u v} R)) :
    K ⋙ ShortComplex.homologyFunctor (ModuleCat.{max u v} R) ≅
      ((ShortComplex.functorEquivalence J (ModuleCat.{max u v} R)).inverse.obj K).homology :=
  NatIso.ofComponents
    (fun j => ((ShortComplex.functorEquivalence J (ModuleCat.{max u v} R)).inverse.obj K)
      |>.mapHomologyIso ((evaluation J (ModuleCat.{max u v} R)).obj j))
    (by
      intro i j f
      have hK : ShortComplex.homologyMap (K.map f) =
          ShortComplex.homologyMap
            (((ShortComplex.functorEquivalence J (ModuleCat.{max u v} R)).inverse.obj K)
              |>.mapNatTrans ((evaluation J (ModuleCat.{max u v} R)).map f)) := rfl
      simp only [Functor.comp_map, ShortComplex.homologyFunctor_map]
      rw [hK, ((ShortComplex.functorEquivalence J (ModuleCat.{max u v} R)).inverse.obj
        K).homologyMap_mapNatTrans ((evaluation J (ModuleCat.{max u v} R)).map f)]
      simp)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def shortComplexColimCocone
    {R : Type u} [CommRing R] {J : Type (max u v)} [SmallCategory J]
    (K : J ⥤ ShortComplex (ModuleCat.{max u v} R)) : Cocone K where
  pt := (ShortComplex.functorEquivalence J (ModuleCat.{max u v} R)).inverse.obj K |>.map
    (colim (J := J) (C := ModuleCat.{max u v} R))
  ι :=
    { app := fun j => ShortComplex.homMk (colimit.ι (K ⋙ ShortComplex.π₁) j)
        (colimit.ι (K ⋙ ShortComplex.π₂) j) (colimit.ι (K ⋙ ShortComplex.π₃) j)
        (by dsimp [ShortComplex.map]; rw [ι_colimMap]; rfl)
        (by dsimp [ShortComplex.map]; rw [ι_colimMap]; rfl)
      naturality := by
        intro i j f
        refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
        · simpa using colimit.w (K ⋙ ShortComplex.π₁) f
        · simpa using colimit.w (K ⋙ ShortComplex.π₂) f
        · simpa using colimit.w (K ⋙ ShortComplex.π₃) f }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def shortComplexColimIsColimit
    {R : Type u} [CommRing R] {J : Type (max u v)} [SmallCategory J]
    (K : J ⥤ ShortComplex (ModuleCat.{max u v} R)) :
    IsColimit (shortComplexColimCocone K) :=
  ShortComplex.isColimitOfIsColimitπ _
    (colimit.isColimit (K ⋙ ShortComplex.π₁))
    (colimit.isColimit (K ⋙ ShortComplex.π₂))
    (colimit.isColimit (K ⋙ ShortComplex.π₃))

set_option backward.isDefEq.respectTransparency false in
private lemma shortComplexHomology_preservesFilteredColimits
    {R : Type u} [CommRing R] {J : Type (max u v)}
    [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (ShortComplex.homologyFunctor (ModuleCat.{max u v} R)) := by
  let := exactFilteredColimitsOfModules (R := R) (J := J)
  have hPFL : PreservesFiniteLimits (colim (J := J) (C := ModuleCat.{max u v} R)) :=
    inferInstance
  have hPC : PreservesColimitsOfSize (colim (J := J) (C := ModuleCat.{max u v} R)) :=
    inferInstance
  have hPH : (colim (J := J) (C := ModuleCat.{max u v} R)).PreservesHomology :=
    { preservesKernels := fun {X Y} f => inferInstance
      preservesCokernels := fun {X Y} f => inferInstance }
  constructor
  intro K
  apply preservesColimit_of_preserves_colimit_cocone
    (t := shortComplexColimCocone K) (shortComplexColimIsColimit K)
  refine IsColimit.ofIsoColimit
    (colimit.isColimit (K ⋙ ShortComplex.homologyFunctor (ModuleCat.{max u v} R)))
    (Cocone.ext
      (HasColimit.isoOfNatIso (shortComplexHomologyFunctorIso K) ≪≫
        (((ShortComplex.functorEquivalence J (ModuleCat.{max u v} R)).inverse.obj K)
          |>.mapHomologyIso (colim (J := J) (C := ModuleCat.{max u v} R))).symm) ?_)
  intro j
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, Iso.trans_hom,
    HasColimit.isoOfNatIso_ι_hom_assoc]
  simp only [shortComplexHomologyFunctorIso, NatIso.ofComponents_hom_app]
  set S := (ShortComplex.functorEquivalence J (ModuleCat.{max u v} R)).inverse.obj K with hS
  let α : ((evaluation J (ModuleCat.{max u v} R)).obj j) ⟶
      (colim (J := J) (C := ModuleCat.{max u v} R)) :=
    { app := fun F => colimit.ι F j, naturality := by intro F G η; simp }
  rw [ShortComplex.homologyFunctor_map, Iso.symm_hom,
    ← ShortComplex.homologyMap_mapNatTrans S α]
  have hmaps : S.mapNatTrans α = (shortComplexColimCocone K).ι.app j := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ ?_ <;>
      simp only [shortComplexColimCocone, S, ShortComplex.functorEquivalence,
        ShortComplex.mapNatTrans, α, ShortComplex.homMk_τ₁,
        ShortComplex.homMk_τ₂, ShortComplex.homMk_τ₃] <;> rfl
  rw [hmaps]

lemma homology_preservesFilteredColimits
    {R : Type u} [CommRing R] {J : Type (max u v)}
    [SmallCategory J] [IsFiltered J] (i : ℤ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) i) := by
  have h : PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) i ⋙
          ShortComplex.homologyFunctor (ModuleCat.{max u v} R)) := by
    let := shortComplexFunctor_preservesColimitsOfShape (R := R) (J := J) i
    let := shortComplexHomology_preservesFilteredColimits (R := R) (J := J)
    infer_instance
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{max u v} R)
      (ComplexShape.up ℤ) i).symm

private lemma kernel_comp_eq_zero_of_square
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasKernels C]
    {X Y Z W : C} (p : X ⟶ Y) (q : X ⟶ Z) (n : Y ⟶ W) (r : Z ⟶ W)
    [Mono r] (h : p ≫ n = q ≫ r) : kernel.ι p ≫ q = 0 := by
  rw [← cancel_mono r, Category.assoc, ← h, ← Category.assoc, kernel.condition,
    zero_comp, zero_comp]

private lemma imageSubobject_le_of_isIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasImages C] [HasEqualizers C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g] :
    imageSubobject f ≤ imageSubobject g := by
  rw [imageSubobject_mono g, Subobject.mk_eq_top_of_isIso]
  exact le_top

open Cardinal

/-- A type that is a surjective image of lists of a bounded type has the same infinite bound. -/
private lemma mk_le_of_surjective_list
    {α β : Type u} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (g : List α → β) (hg : Function.Surjective g) (hα : #α ≤ κ) : #β ≤ κ :=
  (mk_le_of_surjective hg).trans ((mk_list_le_max _).trans (max_le hκ hα))

/-- Countably many copies of an infinite cardinal bound fit in the same bound. -/
private lemma sum_const_int_le {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    Cardinal.sum (fun _ : ℤ => κ) ≤ κ := by
  rw [sum_const, lift_uzero, mk_int, lift_aleph0]
  exact mul_le_of_le hκ hκ le_rfl

/-- Finitely supported functions satisfy the usual infinite cardinal bound. -/
lemma mk_finsupp_le_of_le
    {α : Type u} {β : Type v} [Zero β] {κ : Cardinal.{max u v}}
    (hκ : ℵ₀ ≤ κ) (hα : lift.{v} #α ≤ κ) (hβ : lift.{u} #β ≤ κ) :
    #(α →₀ β) ≤ κ := by
  classical
  refine (mk_le_of_injective (Finsupp.graph_injective α β)).trans
    (mk_le_of_surjective_list hκ List.toFinset (fun s => ⟨s.toList, by simp⟩) ?_)
  rw [mk_prod]
  exact mul_le_of_le hκ hα hβ

/-- A span is bounded by any infinite cardinal bounding its scalars and generators. -/
private lemma mk_span_le_of_le
    {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (s : Set M) {κ : Cardinal.{max u v}}
    (hκ : ℵ₀ ≤ κ) (hR : lift.{v} #R ≤ κ) (hs : lift.{u} #s ≤ κ) :
    lift.{u} #(Submodule.span R s) ≤ κ := by
  rw [Finsupp.span_eq_range_linearCombination]
  calc
    _ ≤ #(s →₀ R) := by
      have h := lift_mk_le_lift_mk_of_surjective
        (Finsupp.linearCombination R (Subtype.val : s → M)).surjective_rangeRestrict
      rw [lift_umax.{v, u}, lift_id'.{v, u}] at h
      exact h
    _ ≤ κ := mk_finsupp_le_of_le hκ hs hR


/-- The degreewise span of generators and all their differential images. -/
private abbrev differentialSpan
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (M : HomologicalComplex (ModuleCat.{v} R) c) (s : ∀ i, Set (M.X i))
    (i : ι) : Submodule R (M.X i) :=
  Submodule.span R (s i ∪ ⋃ j, (M.d j i) '' s j)

/-- Every generator belongs to its differential span. -/
private lemma subset_differentialSpan
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (M : HomologicalComplex (ModuleCat.{v} R) c) (s : ∀ i, Set (M.X i))
    (i : ι) : s i ⊆ differentialSpan M s i :=
  fun _ hx => Submodule.subset_span (Or.inl hx)

/-- The square-zero identity makes the differential span closed under the differential. -/
private lemma differentialSpan_d_mem
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (M : HomologicalComplex (ModuleCat.{v} R) c) (s : ∀ i, Set (M.X i))
    (i j : ι) (x : M.X i) (hx : x ∈ differentialSpan M s i) :
    (M.d i j) x ∈ differentialSpan M s j := by
  show x ∈ (differentialSpan M s j).comap (M.d i j).hom
  apply (Submodule.span_le.mpr ?_) hx
  rintro y (hy | hy)
  · exact Submodule.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, y, hy, rfl⟩))
  · rcases Set.mem_iUnion.mp hy with ⟨k, z, hz, rfl⟩
    show (M.d i j) ((M.d k i) z) ∈ differentialSpan M s j
    have he : (M.d i j) ((M.d k i) z) = 0 :=
      congrArg (fun f : M.X k ⟶ M.X j => f z) (M.d_comp_d k i j)
    rw [he]
    exact Submodule.zero_mem _

/-- The differential span is contained in every subcomplex containing its generators. -/
private lemma differentialSpan_le
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (M : HomologicalComplex (ModuleCat.{v} R) c) (s : ∀ i, Set (M.X i))
    (P : ∀ i, Submodule R (M.X i))
    (hP : ∀ i j x, x ∈ P i → (M.d i j) x ∈ P j)
    (hs : ∀ i, s i ⊆ P i) (i : ι) : differentialSpan M s i ≤ P i := by
  apply Submodule.span_le.mpr
  rintro x (hx | hx)
  · exact hs i hx
  · rcases Set.mem_iUnion.mp hx with ⟨j, y, hy, rfl⟩
    exact hP j i y (hs j hy)

/-- Restrict a complex to a family of submodules closed under its differentials. -/
public def complexOfSubmodules
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (M : HomologicalComplex (ModuleCat.{v} R) c)
    (P : ∀ i, Submodule R (M.X i))
    (hP : ∀ i j x, x ∈ P i → (M.d i j) x ∈ P j) :
    HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (P i)
  d i j := ModuleCat.ofHom ((M.d i j).hom.restrict (hP i j))
  shape i j hij := by
    ext x
    exact congrArg (fun f : M.X i ⟶ M.X j => f x) (M.shape i j hij)
  d_comp_d' i j k _ _ := by
    ext x
    exact congrArg (fun f : M.X i ⟶ M.X k => f x) (M.d_comp_d i j k)

/-- The canonical inclusion of a complex restricted to submodules. -/
public def complexOfSubmodulesι
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (M : HomologicalComplex (ModuleCat.{v} R) c)
    (P : ∀ i, Submodule R (M.X i))
    (hP : ∀ i j x, x ∈ P i → (M.d i j) x ∈ P j) :
    complexOfSubmodules M P hP ⟶ M where
  f i := ModuleCat.ofHom (P i).subtype
  comm' _ _ _ := rfl

/-- The inclusion of the restricted complex is a monomorphism. -/
public lemma complexOfSubmodulesι_mono
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (M : HomologicalComplex (ModuleCat.{v} R) c)
    (P : ∀ i, Submodule R (M.X i))
    (hP : ∀ i j x, x ∈ P i → (M.d i j) x ∈ P j) :
    Mono (complexOfSubmodulesι M P hP) := by
  have : ∀ i, Mono ((complexOfSubmodulesι M P hP).f i) := fun i =>
    (ModuleCat.mono_iff_injective ((complexOfSubmodulesι M P hP).f i)).mpr
      Subtype.val_injective
  exact HomologicalComplex.mono_of_mono_f (complexOfSubmodulesι M P hP) this

/-- Closing generators under the differential preserves an infinite cardinal bound. -/
private lemma mk_differentialSpan_le
    {R : Type u} [Ring R]
    (M : CochainComplex (ModuleCat.{max u v} R) ℤ) (s : ∀ i, Set (M.X i))
    {κ : Cardinal.{max u v}} (hκ : ℵ₀ ≤ κ) (hR : lift.{v} #R ≤ κ)
    (hs : ∀ i, #(s i) ≤ κ) (i : ℤ) : #(differentialSpan M s i) ≤ κ := by
  have hgen : #((s i ∪ ⋃ j, (M.d j i) '' s j) : Set (M.X i)) ≤ κ := by
    apply (mk_union_le _ _).trans
    apply add_le_of_le hκ (hs i)
    have hu := mk_iUnion_le_sum_mk_lift (f := fun j => (M.d j i) '' s j)
    rw [lift_uzero] at hu
    exact hu.trans ((sum_le_sum _ _ (fun j =>
      (mk_image_le (f := M.d j i)).trans (hs j))).trans (sum_const_int_le hκ))
  have h := mk_span_le_of_le (R := R) (s i ∪ ⋃ j, (M.d j i) '' s j)
    (κ := κ) hκ (by rwa [lift_umax.{u, v}]) (by rwa [lift_id'.{u, v}])
  rwa [lift_id'.{u, v}] at h

/-- The union of the terms of the generated complex satisfies the same cardinal bound. -/
private lemma mk_sigma_differentialSpan_le
    {R : Type u} [Ring R]
    (M : CochainComplex (ModuleCat.{max u v} R) ℤ) (s : ∀ i, Set (M.X i))
    {κ : Cardinal.{max u v}} (hκ : ℵ₀ ≤ κ) (hR : lift.{v} #R ≤ κ)
    (hs : ∀ i, #(s i) ≤ κ) : #(Σ i, differentialSpan M s i) ≤ κ := by
  rw [mk_sigma]
  exact (sum_le_sum _ _ (mk_differentialSpan_le M s hκ hR hs)).trans (sum_const_int_le hκ)

/-- Degreewise sets of bounded size lie in a subcomplex with bounded total size. -/
private lemma exists_subcomplex_cardinal_le
    {R : Type u} [Ring R]
    (M : CochainComplex (ModuleCat.{max u v} R) ℤ) (s : ∀ i, Set (M.X i))
    {κ : Cardinal.{max u v}} (hκ : ℵ₀ ≤ κ) (hR : lift.{v} #R ≤ κ)
    (hs : ∀ i, #(s i) ≤ κ) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (ι : P ⟶ M),
      Mono ι ∧ (∀ i, s i ⊆ Set.range (ι.f i)) ∧ #(Σ i, P.X i) ≤ κ := by
  refine ⟨complexOfSubmodules M (differentialSpan M s) (differentialSpan_d_mem M s),
    complexOfSubmodulesι M (differentialSpan M s) (differentialSpan_d_mem M s),
    complexOfSubmodulesι_mono _ _ _, ?_, ?_⟩
  · intro i x hx
    exact ⟨⟨x, subset_differentialSpan M s i hx⟩, rfl⟩
  · exact mk_sigma_differentialSpan_le M s hκ hR hs

/-- A morphism whose components land in a subcomplex factors through its inclusion. -/
private lemma exists_lift_complexOfSubmodules
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {K M : HomologicalComplex (ModuleCat.{v} R) c}
    (P : ∀ i, Submodule R (M.X i))
    (hP : ∀ i j x, x ∈ P i → (M.d i j) x ∈ P j)
    (φ : K ⟶ M) (hφ : ∀ i x, (φ.f i) x ∈ P i) :
    ∃ ψ : K ⟶ complexOfSubmodules M P hP,
      ψ ≫ complexOfSubmodulesι M P hP = φ := by
  refine ⟨{
    f := fun i => ModuleCat.ofHom ((φ.f i).hom.codRestrict (P i) (hφ i))
    comm' := fun i j _ => ?_ }, ?_⟩
  · ext x
    exact Subtype.ext (congrArg (fun f : K.X i ⟶ M.X j => f x) (φ.comm i j))
  · ext i x
    rfl

/-- An existing subcomplex and additional generators fit in a bounded enlargement. -/
private lemma exists_enlargement_cardinal_le
    {R : Type u} [Ring R]
    {K M : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (φ : K ⟶ M) [Mono φ] (s : ∀ i, Set (M.X i))
    (hφ : ∀ i x, (φ.f i) x ∈ s i)
    {κ : Cardinal.{max u v}} (hκ : ℵ₀ ≤ κ) (hR : lift.{v} #R ≤ κ)
    (hs : ∀ i, #(s i) ≤ κ) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (ι : P ⟶ M) (ψ : K ⟶ P),
      Mono ι ∧ Mono ψ ∧ ψ ≫ ι = φ ∧
      (∀ i, s i ⊆ Set.range (ι.f i)) ∧ #(Σ i, P.X i) ≤ κ := by
  obtain ⟨ψ, hψ⟩ := exists_lift_complexOfSubmodules
    (differentialSpan M s) (differentialSpan_d_mem M s) φ
    (fun i x => subset_differentialSpan M s i (hφ i x))
  refine ⟨_, complexOfSubmodulesι M (differentialSpan M s)
    (differentialSpan_d_mem M s), ψ, complexOfSubmodulesι_mono _ _ _,
    mono_of_mono_fac hψ, hψ, ?_, ?_⟩
  · intro i x hx
    exact ⟨⟨x, subset_differentialSpan M s i hx⟩, rfl⟩
  · exact mk_sigma_differentialSpan_le M s hκ hR hs

/-- A natural comparison carries a compatible square to the target category. This is what makes
the comparison maps of an increasing chain of subcomplexes into a natural transformation of
diagrams, so it is needed wherever those diagrams are formed. -/
public lemma comparison_square
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {T : C ⥤ E} {Q : D ⥤ E} (α : T ⟶ F ⋙ Q)
    {M₁ M : C} {N₁ N : D} (m : M₁ ⟶ M) (n : N₁ ⟶ N)
    (b₁ : F.obj M₁ ⟶ N₁) (b : F.obj M ⟶ N)
    (h : F.map m ≫ b = b₁ ≫ n) :
    T.map m ≫ (α.app M ≫ Q.map b) = (α.app M₁ ≫ Q.map b₁) ≫ Q.map n := by
  rw [← Category.assoc, α.naturality]
  show (α.app M₁ ≫ Q.map (F.map m)) ≫ Q.map b = _
  rw [Category.assoc, ← Q.map_comp, h, Q.map_comp, ← Category.assoc]

/-- Pure tensors additively generate the tensor product, giving its infinite cardinal bound. -/
private lemma mk_tensorProduct_le_of_le
    {R : Type u} {M : Type v} {N : Type w}
    [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {κ : Cardinal.{max v w}} (hκ : ℵ₀ ≤ κ)
    (hM : lift.{w} #M ≤ κ) (hN : lift.{v} #N ≤ κ) :
    #(TensorProduct R M N) ≤ κ := by
  let g : List (M × N) → TensorProduct R M N :=
    fun l => (l.map (fun p => TensorProduct.tmul R p.1 p.2)).sum
  have hg : Function.Surjective g := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨[], rfl⟩
    | tmul m n => exact ⟨[(m, n)], by simp [g]⟩
    | add x y hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := hy
      exact ⟨l ++ k, by simp [g]⟩
  refine mk_le_of_surjective_list hκ g hg ?_
  rw [mk_prod]
  exact mul_le_of_le hκ hM hN

/-- Extension of scalars preserves an infinite bound on the size of the terms. -/
private lemma mk_extendScalars_obj_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P : ModuleCat.{max u v w} A) {κ : Cardinal.{max u v w}}
    (hκ : ℵ₀ ≤ κ) (hB : lift.{max u w} #B ≤ κ) (hP : #P ≤ κ) :
    #((ModuleCat.extendScalars f).obj P) ≤ κ := by
  show #(TensorProduct A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) P) ≤ κ
  apply mk_tensorProduct_le_of_le hκ
  · show lift.{max u v w} #B ≤ κ
    rwa [lift_umax.{v, max u w}]
  · rwa [lift_id'.{v, max u w}]

/-- A map of complexes lifts through a monomorphism when its components do. The factorization is
built degreewise by `LinearMap.codLift`, available because a monomorphism of modules is injective,
and it commutes with the differentials because the monomorphism can be cancelled.

This is the factorization input of the enlargement of Stacks 0GYZ: the subcomplex Stacks 0GYI
produces for one morphism of the site has to be mapped into the stage of the iteration that
follows it, and all that is known of that stage is that it contains the sections of the
subcomplex. -/
public lemma exists_lift_of_range_subset
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {K L M : HomologicalComplex (ModuleCat.{v} R) c}
    (φ : K ⟶ M) (ψ : L ⟶ M) [Mono ψ]
    (h : ∀ i, Set.range (φ.f i) ⊆ Set.range (ψ.f i)) :
    ∃ χ : K ⟶ L, χ ≫ ψ = φ := by
  classical
  have hψ : ∀ i, Function.Injective (ψ.f i) := fun i =>
    (ModuleCat.mono_iff_injective (ψ.f i)).mp inferInstance
  let g (i : ι) : K.X i ⟶ L.X i := ModuleCat.ofHom
    ((φ.f i).hom.codLift (ψ.f i).hom (hψ i) (fun x => h i ⟨x, rfl⟩))
  have hg (i : ι) : g i ≫ ψ.f i = φ.f i :=
    ModuleCat.hom_ext (LinearMap.comp_codLift (φ.f i).hom (ψ.f i).hom (hψ i)
      (fun x => h i ⟨x, rfl⟩))
  refine ⟨{ f := g, comm' := fun i j _ => ?_ }, ?_⟩
  · rw [← cancel_mono (ψ.f j), Category.assoc, ← ψ.comm,
      ← Category.assoc, hg, φ.comm, Category.assoc, hg]
  · exact HomologicalComplex.Hom.ext (funext hg)

/-- The cardinality of one term is bounded by that of the disjoint union of all terms. -/
lemma mk_term_le_mk_sigma
    {ι : Type} {X : ι → Type v} (i : ι) : #(X i) ≤ #(Σ j, X j) :=
  mk_le_of_injective (f := Sigma.mk i) (by intro x y h; simpa using h)

/-- Extension of scalars carries the zero map to the zero map. -/
private lemma extendScalars_preservesZeroMorphisms
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars.{u, v, w} f).PreservesZeroMorphisms := by
  constructor
  intro M N
  apply ModuleCat.hom_ext
  dsimp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map']
  let := ((algebraMap B B).comp f).toAlgebra
  exact LinearMap.baseChange_zero

attribute [local instance] extendScalars_preservesZeroMorphisms

/-- Small sets of generators fit in a compatible pair of small subcomplexes. -/
lemma exists_compatible_enlargement_cardinal_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (M M₁ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
    (N N₁ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
    (m₁ : M₁ ⟶ M) (n₁ : N₁ ⟶ N) [Mono m₁] [Mono n₁]
    (b : ((ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M ⟶ N)
    (s : ∀ i, Set (M.X i)) (t : ∀ i, Set (N.X i))
    (hm₁ : ∀ i x, (m₁.f i) x ∈ s i) (hn₁ : ∀ i x, (n₁.f i) x ∈ t i)
    {κ : Cardinal.{max u v w}} (hκ : ℵ₀ ≤ κ)
    (hA : lift.{max v w} #A ≤ κ) (hB : lift.{max u w} #B ≤ κ)
    (hs : ∀ i, #(s i) ≤ κ) (ht : ∀ i, #(t i) ≤ κ) :
    let E := (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ (M₂ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
      (N₂ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
      (m₂ : M₂ ⟶ M) (n₂ : N₂ ⟶ N)
      (_ : Mono m₂) (_ : Mono n₂)
      (m₁₂ : M₁ ⟶ M₂) (n₁₂ : N₁ ⟶ N₂) (_ : Mono m₁₂) (_ : Mono n₁₂)
      (b₂ : E.obj M₂ ⟶ N₂),
      m₁₂ ≫ m₂ = m₁ ∧ n₁₂ ≫ n₂ = n₁ ∧ E.map m₂ ≫ b = b₂ ≫ n₂ ∧
      (∀ i, s i ⊆ Set.range (m₂.f i)) ∧ (∀ i, t i ⊆ Set.range (n₂.f i)) ∧
      #((Σ i, M₂.X i) ⊕ (Σ i, N₂.X i)) ≤ κ := by
  classical
  let E := (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  obtain ⟨M₂, m₂, m₁₂, hm₂, hm₁₂, hmf, hms, hMc⟩ :=
    exists_enlargement_cardinal_le m₁ s hm₁ hκ hA hs
  let φ : E.obj M₂ ⟶ N := E.map m₂ ≫ b
  let t' (i : ℤ) : Set (N.X i) := t i ∪ Set.range (φ.f i)
  have ht' (i : ℤ) : #(t' i) ≤ κ := by
    exact (mk_union_le _ _).trans (add_le_of_le hκ (ht i) ((mk_range_le (f := φ.f i)).trans
      (mk_extendScalars_obj_le f (M₂.X i) hκ hB ((mk_term_le_mk_sigma i).trans hMc))))
  obtain ⟨N₂, n₂, n₁₂, hn₂, hn₁₂, hnf, hns, hNc⟩ :=
    exists_enlargement_cardinal_le n₁ t' (fun i x => Or.inl (hn₁ i x)) hκ hB ht'
  let := hn₂
  obtain ⟨b₂, hb₂⟩ := exists_lift_of_range_subset φ n₂
    (fun i x hx => hns i (Or.inr hx))
  refine ⟨M₂, N₂, m₂, n₂, hm₂, hn₂, m₁₂, n₁₂, hm₁₂, hn₁₂, b₂,
    hmf, hnf, hb₂.symm, hms, fun i x hx => hns i (Or.inl hx), ?_⟩
  rw [mk_sum, lift_id, lift_id]
  exact add_le_of_le hκ hMc hNc

/-- A direct sum has at most the cardinality of the finite lists of its summands. -/
private lemma mk_directSum_le_of_le
    {ι : Type v} {X : ι → Type w} [∀ i, AddCommMonoid (X i)]
    {κ : Cardinal.{max v w}} (hκ : ℵ₀ ≤ κ) (hX : #(Σ i, X i) ≤ κ) :
    #(DirectSum ι X) ≤ κ := by
  classical
  let g : List (Σ i, X i) → DirectSum ι X :=
    fun l => (l.map (fun p => DirectSum.of X p.1 p.2)).sum
  have hg : Function.Surjective g := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨[], rfl⟩
    | of i x => exact ⟨[⟨i, x⟩], by simp [g]⟩
    | add x y hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := hy
      exact ⟨l ++ k, by simp [g]⟩
  exact mk_le_of_surjective_list hκ g hg hX

/-- Countable coproducts preserve an infinite bound on the cardinality of their terms. -/
private lemma mk_countable_coproduct_le
    {R : Type u} [Ring R] {ι : Type} [Countable ι]
    (X : ι → ModuleCat.{v} R) [HasCoproduct X]
    {κ : Cardinal.{v}} (hκ : ℵ₀ ≤ κ) (hX : ∀ i, #(X i) ≤ κ) :
    #(∐ X : ModuleCat.{v} R) ≤ κ := by
  classical
  rw [mk_congr (ModuleCat.coprodIsoDirectSum X).toLinearEquiv.toEquiv]
  apply mk_directSum_le_of_le hκ
  rw [mk_sigma]
  calc
    _ ≤ Cardinal.sum (fun _ : ι => κ) := sum_le_sum _ _ hX
    _ ≤ κ := by
      rw [sum_const, lift_uzero]
      exact mul_le_of_le hκ ((lift_le.mpr mk_le_aleph0).trans (by simpa using hκ)) le_rfl

/-- Cohomology has cardinality at most that of the corresponding term. -/
lemma mk_homology_le_mk_term
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι) :
    #(K.homology i) ≤ #(K.X i) := by
  calc
    _ ≤ #(K.cycles i) := mk_le_of_surjective
      ((ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance)
    _ ≤ #(K.X i) := mk_le_of_injective
      ((ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance)

/-- The tensor-total construction preserves infinite cardinal bounds on both complexes. -/
lemma mk_tensorRight_term_le
    {R : Type u} [CommRing R] (K P : CochainComplex (ModuleCat.{u} R) ℤ)
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hK : ∀ i, #(K.X i) ≤ κ) (hP : ∀ i, #(P.X i) ≤ κ) (i : ℤ) :
    #(((CategoryTheory.MonoidalCategory.tensorRight P).obj K).X i) ≤ κ := by
  show #(∐ (fun p : {p : ℤ × ℤ // p.1 + p.2 = i} =>
    ModuleCat.of R (TensorProduct R (K.X p.1.1) (P.X p.1.2))) : ModuleCat.{u} R) ≤ κ
  exact mk_countable_coproduct_le _ hκ fun p =>
    mk_tensorProduct_le_of_le hκ (by simpa using hK p.1.1) (by simpa using hP p.1.2)

/-- Countable unions preserve an infinite cardinal bound. -/
private lemma countable_union_cardinal_bound
    {α : Type u} (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (S : ℤ → Set α) (hS : ∀ i, #(S i) ≤ κ) :
    #(⋃ i, S i) ≤ κ := by
  calc
    _ ≤ Cardinal.sum (fun i => #(S i)) := by
      simpa only [lift_uzero] using (mk_iUnion_le_sum_mk_lift (f := S))
    _ ≤ κ := (sum_le_sum _ _ hS).trans (sum_const_int_le hκ)

/-- Countably many persistent conditions hold together at a sufficiently directed stage. -/
private lemma stage_all_degrees
    {J : Type u} [Preorder J] (κ : Cardinal.{u})
    (hκ : Cardinal.lift.{u} #(ℤ) ≤ κ)
    (hdir : ∀ s : Set J, #s ≤ κ → ∃ k, ∀ j ∈ s, j ≤ k)
    (F : ℤ → J → Prop)
    (hF : ∀ i j, ∃ k, j ≤ k ∧ F i k)
    (hmono : ∀ i j k, j ≤ k → F i j → F i k) :
    ∀ j, ∃ k, j ≤ k ∧ ∀ i : ℤ, F i k := by
  classical
  intro j
  choose k hk hFk using fun i => hF i j
  have hs : #(Set.range k) ≤ κ := by
    have hr : #(Set.range k) ≤ lift.{u} #ℤ := by
      simpa only [lift_uzero] using (mk_range_le_lift (f := k))
    exact hr.trans hκ
  obtain ⟨l, hl⟩ := hdir (Set.range k) hs
  exact ⟨l, (hk 0).trans (hl _ ⟨0, rfl⟩),
    fun i => hmono i (k i) l (hl _ ⟨i, rfl⟩) (hFk i)⟩

end Stacks.SubcomplexEnlargement

end
