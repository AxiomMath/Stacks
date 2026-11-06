module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimitHomologySequence
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantDifference
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# K-injective resolutions through the tower of truncations, and acyclic functors

Let `F : C ⥤ D` be an additive functor between abelian categories, with `C` having enough
injectives and `D` exact countable products, and let `K` be an unbounded complex of objects of
`C` all of whose canonical truncations `τ_{≥ n} K` have `F`-acyclic terms.  Resolving the
truncations by bounded below complexes of injectives (Stacks 070F) and passing to the limit of
the resulting tower (Stacks 070G) gives a K-injective resolution `K ⟶ I` which `F` carries to a
quasi-isomorphism: on each truncation this is Leray's acyclicity lemma, and the passage to the
limit is the Milnor sequence of the tower, whose `lim¹`-term vanishes because the transition maps
of the tower are degreewise split.  Consequently the comparison map `F(K) ⟶ RF(K)` of any total
right derived functor of `F` is invertible at `K`.

This is the argument which computes an unbounded total right derived functor on a complex whose
truncations have acyclic terms, with no bound on cohomological dimension.  It is used for the
base change complexes of Stacks 0H0U and of Stacks 0H0J.

## Main results

* `Stacks.TruncationTower.exists_quasiIso_isKInjective_map_quasiIso`: the K-injective
  resolution carried to a quasi-isomorphism.
* `Stacks.TruncationTower.isIso_derivedUnit_of_quasiIso_map`: invertibility of the comparison
  map of a total right derived functor at such a complex.
* `Stacks.TruncationTower.quasiIso_limitLift_of_eventually_quasiIsoAt`: the Milnor-sequence
  engine for towers with degreewise split transition maps.
* `Stacks.TruncationTower.property_truncGE_map`: the terms of the truncations of a complex in
  the image of a cokernel-preserving functor lie in its image.
* `Stacks.TruncationTower.quasiIso_of_forget_map_quasiIso`: forgetting the sheaf condition
  reflects quasi-isomorphisms of complexes of sheaves of modules.

## References

* [Stacks Project, Tag 070F](https://stacks.math.columbia.edu/tag/070F)
* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
* [Stacks Project, Tag 0H0U](https://stacks.math.columbia.edu/tag/0H0U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.TruncationTower

universe uC vC uD vD wC wD

section Truncation

/-- Above the truncation degree, the canonical map `K ⟶ τ_{≥ n} K` is an isomorphism in each
degree. -/
lemma isIso_πTruncGE_f_of_lt
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    (K : CochainComplex C ℤ) [∀ j, K.HasHomology j]
    (n i : ℤ) (hi : n < i) : IsIso ((K.πTruncGE n).f i) := by
  let e := ComplexShape.embeddingUpIntGE n
  have he : e.f (i - n).natAbs = i := by
    show n + ((i - n).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  show IsIso ((HomologicalComplex.πTruncGE K e).f i)
  dsimp only [HomologicalComplex.πTruncGE]
  apply (e.isIso_liftExtend_f_iff _ _ he).mpr
  apply K.isIso_restrictionToTruncGE'
  intro h
  rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero] at h
  omega

/-- An additive functor applied degreewise to the canonical map `K ⟶ τ_{≥ n} K` gives a map which
is a quasi-isomorphism in every degree `i` with `n < i - 1`, the map being an isomorphism in the
three degrees around `i`. -/
lemma quasiIsoAt_map_πTruncGE
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ)
    (n i : ℤ) (hi : n < i - 1) :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map (K.πTruncGE n)) i := by
  let f := (F.mapHomologicalComplex (.up ℤ)).map (K.πTruncGE n)
  have hc (j : ℤ) (hj : n < j) : IsIso (f.f j) := by
    have := isIso_πTruncGE_f_of_lt K n j hj
    show IsIso (F.map ((K.πTruncGE n).f j))
    infer_instance
  rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
  let τ := (HomologicalComplex.shortComplexFunctor' D (.up ℤ) (i - 1) i (i + 1)).map f
  have : IsIso τ.τ₁ := hc _ hi
  have : IsIso τ.τ₂ := hc _ (by omega)
  have : IsIso τ.τ₃ := hc _ (by omega)
  have : IsIso τ := ShortComplex.isIso_of_isIso τ
  show ShortComplex.QuasiIso τ
  infer_instance

end Truncation

section DerivedUnit

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- A morphism of complexes is a quasi-isomorphism iff its image in the derived category, taken
through the homotopy category, is an isomorphism. -/
private lemma isIso_Qh_map_quotient_map_iff {E : Type uC} [Category.{vC} E] [Abelian E]
    [HasDerivedCategory.{wC} E] {K L : CochainComplex E ℤ} (f : K ⟶ L) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient E (.up ℤ)).map f)) ↔
      QuasiIso f := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso E) f

/-- A quasi-isomorphism between bounded-below complexes with termwise right acyclic terms is
carried to a quasi-isomorphism. -/
lemma quasiIso_map_of_boundedBelow_acyclic
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L)
    (hKa : ∀ n, F.rightAcyclic (K.X n)) (hLa : ∀ n, F.rightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let α := (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
  let q := HomotopyCategory.Plus.quotient C
  let φ : (⟨K, hK⟩ : CochainComplex.Plus C) ⟶ ⟨L, hL⟩ := ObjectProperty.homMk f
  have hαK : IsIso (α.app (q.obj ⟨K, hK⟩)) :=
    F.isIso_totalRightDerivedUnit_app_of_rightAcyclic K hK hKa
  have hαL : IsIso (α.app (q.obj ⟨L, hL⟩)) :=
    F.isIso_totalRightDerivedUnit_app_of_rightAcyclic L hL hLa
  have hφ : HomotopyCategory.Plus.quasiIso C (q.map φ) := by
    rw [HomotopyCategory.Plus.quasiIso_iff, HomotopyCategory.Plus.quotient_map_hom]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2
      (show HomologicalComplex.quasiIso C (.up ℤ) f from inferInstanceAs (QuasiIso f))
  have : IsIso (DerivedCategory.Plus.Qh.map (q.map φ)) :=
    Localization.inverts _ (HomotopyCategory.Plus.quasiIso C) _ hφ
  have : IsIso ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map φ)) := by
    have : IsIso (α.app (q.obj ⟨K, hK⟩) ≫
        (DerivedCategory.Plus.Qh ⋙ _).map (q.map φ)) := by
      dsimp only [Functor.comp_map]
      infer_instance
    exact IsIso.of_isIso_fac_right (α.naturality (q.map φ))
  have : IsIso ((DerivedCategory.Plus.ι (C := D)).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map φ))) :=
    inferInstance
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
    ((F.mapHomologicalComplex (.up ℤ)).map f))) at this
  exact (isIso_Qh_map_quotient_map_iff _).1 this

/-- Invertibility of the unit of a total right derived functor at a complex, from a
quasi-isomorphism into a K-injective complex that the functor also carries to a
quasi-isomorphism. -/
lemma isIso_derivedUnit_of_quasiIso_map
    (F : C ⥤ D) [F.Additive]
    (hC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ))]
    {K I : CochainComplex C ℤ} (f : K ⟶ I) [QuasiIso f]
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)] (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hαI : IsIso (α.app (q.obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) hC).2
      DerivedCategory.Qh RF α I hI
  have hqf : IsIso (DerivedCategory.Qh.map (q.map f)) :=
    (isIso_Qh_map_quotient_map_iff f).2 inferInstance
  have hFf : IsIso ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map (q.map f)) := by
    show IsIso (((q ⋙ F.mapHomotopyCategory (.up ℤ)) ⋙ DerivedCategory.Qh).map f)
    rw [NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh)]
    show IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map f)))
    exact (isIso_Qh_map_quotient_map_iff _).2 inferInstance
  have : IsIso ((DerivedCategory.Qh ⋙ RF).map (q.map f)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_fac_right (α.naturality (q.map f)).symm

end DerivedUnit

section DerivedLimit

open CategoryTheory.Pretriangulated Stacks.DerivedLimit

variable {E : Type uC} [Category.{vC} E] [Abelian E]
  [HasProductsOfShape ℕ E] [HasLimitsOfShape ℕᵒᵖ E]
  [HasExactLimitsOfShape (Discrete ℕ) E] [HasDerivedCategory.{wC} E]

omit [Abelian E] [HasProductsOfShape ℕ E] [HasExactLimitsOfShape (Discrete ℕ) E]
  [HasDerivedCategory E] in
/-- A cone over an `ℕᵒᵖ`-indexed system whose legs are eventually isomorphisms induces an
isomorphism to the limit: the system is then eventually constant. -/
lemma isIso_limitLift_of_eventually_isIso
    (F : ℕᵒᵖ ⥤ E) (c : Cone F) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → IsIso (c.π.app ⟨n⟩)) :
    IsIso (limit.lift F c) := by
  have he : F.IsEventuallyConstantTo ⟨N⟩ := by
    intro j φ
    have := h j.unop (leOfHom φ.unop)
    have := h N le_rfl
    exact IsIso.of_isIso_fac_left (c.w φ)
  have hp : IsIso (limit.π F ⟨N⟩) := he.isIso_π_of_isLimit (limit.isLimit F)
  have := h N le_rfl
  exact IsIso.of_isIso_fac_right (limit.lift_π c ⟨N⟩)

/-- If the difference map of the image of a countable system under an additive functor is a split
epimorphism and the product comparison is invertible, the image of the difference map is an
epimorphism. -/
private lemma epi_map_inverseSystemDifference {A : Type uC} [Category.{vC} A] [Preadditive A]
    {B : Type uD} [Category.{vD} B] [Preadditive B] (G : A ⥤ B) [G.Additive]
    (F : ℕᵒᵖ ⥤ A) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] [HasProductsOfShape ℕ B]
    [IsIso (piComparison G fun n : ℕ ↦ F.obj ⟨n⟩)]
    (hs : IsSplitEpi (inverseSystemDifference (F ⋙ G))) :
    Epi (G.map (inverseSystemDifference F)) := by
  have : Epi (G.map (inverseSystemDifference F) ≫
      piComparison G (fun n : ℕ ↦ F.obj ⟨n⟩)) := by
    rw [map_inverseSystemDifference_comp_piComparison G F]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (piComparison G (fun n : ℕ ↦ F.obj ⟨n⟩))).1 this

/-- The Milnor-sequence criterion: a map into the vertex of a cone over an inverse system in
the derived category which is an isomorphism on homology far enough along the system, with the
Milnor triangle of the system available, is an isomorphism. -/
lemma isIso_of_eventually_isIso_homology
    (F : ℕᵒᵖ ⥤ DerivedCategory E) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (c : Cone F) {L : DerivedCategory E} (f : c.pt ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Stacks.DerivedLimit.inverseSystemDifference F) δ ∈
      distTriang (DerivedCategory E))
    (hf : ∀ n : ℕ, f ≫ p ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n = c.π.app ⟨n⟩)
    (h : ∀ r : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor E r).map (c.π.app ⟨n⟩))) : IsIso f := by
  have := Stacks.DerivedProducts.hasProductsOfShape_nat (A := E)
  let d := Stacks.DerivedLimit.inverseSystemDifference F
  have hcomp (r : ℤ) : IsIso (piComparison (DerivedCategory.homologyFunctor E r)
      (fun n : ℕ ↦ F.obj ⟨n⟩)) :=
    Stacks.DerivedProducts.isIso_piComparison_homologyFunctor _ r
  have hepi (r : ℤ) : Epi ((DerivedCategory.homologyFunctor E r).map d) := by
    let H := DerivedCategory.homologyFunctor E r
    obtain ⟨N, hN⟩ := h r
    have hiso (n : ℕ) (hn : N ≤ n) :
        IsIso ((F ⋙ H).map (homOfLE (Nat.le_succ n)).op) := by
      have := hN n hn
      have := hN (n + 1) (by omega)
      exact IsIso.of_isIso_fac_left (f := H.map (c.π.app ⟨n + 1⟩))
        (h := H.map (c.π.app ⟨n⟩)) (by rw [Functor.comp_map, ← H.map_comp, c.w])
    have : IsSplitEpi (Stacks.DerivedLimit.inverseSystemDifference (F ⋙ H)) :=
      Stacks.InverseSystem.isSplitEpi_milnorDifference_functor (F ⋙ H) N hiso
    have := hcomp r
    exact epi_map_inverseSystemDifference H F ‹_›
  rw [DerivedCategory.isIso_iff]
  intro r
  let H := DerivedCategory.homologyFunctor E r
  have := hcomp r
  obtain ⟨N, hN⟩ := h r
  have hi : IsIso (limit.lift (F ⋙ H) (H.mapCone c)) :=
    isIso_limitLift_of_eventually_isIso (F ⋙ H) (H.mapCone c) N hN
  have hmraw := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (r - 1) r).mpr
    ((DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT (r - 1) r).mp
      (hepi (r - 1)))
  have hm : Mono (H.map p) := hmraw
  let e := asIso (piComparison H (fun n : ℕ ↦ F.obj ⟨n⟩))
  let k : H.obj L ⟶ limit (F ⋙ H) := limit.lift (F ⋙ H)
    { pt := H.obj L
      π := NatTrans.ofOpSequence (fun n ↦ H.map (p ≫ Pi.π _ n)) (fun n ↦ by
        dsimp only [Functor.const_obj_map, Functor.comp_map]
        refine (Category.id_comp _).trans ?_
        rw [← H.map_comp, Category.assoc]
        have ht := comp_distTriang_mor_zero₁₂ _ hT
        have ht' := congrArg (fun x ↦ x ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) ht
        dsimp at ht'
        simp only [Category.assoc, Stacks.DerivedLimit.inverseSystemDifference_comp_π,
          Preadditive.comp_sub, zero_comp] at ht'
        exact congrArg H.map (sub_eq_zero.mp ht')) }
  have hk (n : ℕ) : k ≫ limit.π (F ⋙ H) ⟨n⟩ = H.map (p ≫ Pi.π _ n) := limit.lift_π _ _
  have hfk : H.map f ≫ k = limit.lift (F ⋙ H) (H.mapCone c) := by
    apply limit.hom_ext
    intro n
    rw [Category.assoc, hk n.unop, ← H.map_comp, hf n.unop, limit.lift_π]
    rfl
  have : IsIso k := by
    let a : limit (F ⋙ H) ⟶ ∏ᶜ fun n : ℕ ↦ (F ⋙ H).obj ⟨n⟩ :=
      (inverseSystemLimitKernelFork (F ⋙ H)).ι
    have : Mono a := mono_of_isLimit_fork (inverseSystemLimitKernelForkIsLimit (F ⋙ H))
    have hka : k ≫ a = H.map p ≫ e.hom := by
      apply Pi.hom_ext
      intro n
      show (k ≫ Pi.lift (fun n : ℕ ↦ limit.π (F ⋙ H) ⟨n⟩)) ≫ Pi.π _ n = _
      rw [Category.assoc, Pi.lift_comp_π, hk, Category.assoc]
      show H.map (p ≫ Pi.π _ n) =
        H.map p ≫ piComparison H (fun n : ℕ ↦ F.obj ⟨n⟩) ≫ Pi.π _ n
      rw [piComparison_comp_π, H.map_comp]
    have hker := (DerivedCategory.HomologySequence.exact₂ _ hT r).fIsKernel
    have he : H.map d ≫ e.hom = e.hom ≫
        Stacks.DerivedLimit.inverseSystemDifference (F ⋙ H) :=
      Stacks.DerivedLimit.map_inverseSystemDifference_comp_piComparison H F
    have hzero : (a ≫ e.inv) ≫ H.map d = 0 := by
      apply (cancel_mono e.hom).1
      rw [Category.assoc, Category.assoc, he,
        ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp, zero_comp]
      exact (inverseSystemLimitKernelFork (F ⋙ H)).condition
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hker (a ≫ e.inv) hzero
    change limit (F ⋙ H) ⟶ H.obj L at l
    change l ≫ H.map p = a ≫ e.inv at hl
    refine ⟨l, ?_, ?_⟩
    · apply (cancel_mono (H.map p)).1
      rw [Category.assoc, hl, ← Category.assoc, hka, Category.assoc, e.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · apply (cancel_mono a).1
      rw [Category.assoc, hka, ← Category.assoc, hl, Category.assoc, e.inv_hom_id]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact IsIso.of_isIso_fac_right hfk

/-- For a tower with split epimorphic transition maps the difference map
`(xₙ) ↦ (xₙ - t(xₙ₊₁))` on the product is a split epimorphism. -/
lemma isSplitEpi_difference_of_isSplitEpi
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (ht : ∀ n : ℕ, IsSplitEpi (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsSplitEpi (inverseSystemDifference F) := by
  classical
  let σ (n : ℕ) := @section_ _ _ _ _ (F.map (homOfLE (Nat.le_succ n)).op) (ht n)
  let k : ∀ n : ℕ, (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ F.obj ⟨n⟩ :=
    Nat.rec (0 : _ ⟶ F.obj ⟨0⟩)
      (fun n k ↦ (k - Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) ≫ σ n)
  refine IsSplitEpi.mk' ⟨Pi.lift k, ?_⟩
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, inverseSystemDifference_comp_π, Preadditive.comp_sub,
    Pi.lift_comp_π, ← Category.assoc, Pi.lift_comp_π]
  show k n - (((k n - Pi.π _ n) ≫ σ n) ≫ F.map (homOfLE (Nat.le_succ n)).op) = _
  rw [Category.assoc, show σ n ≫ F.map (homOfLE (Nat.le_succ n)).op = 𝟙 _ from
    @IsSplitEpi.id _ _ _ _ _ (ht n), Category.comp_id, sub_sub_cancel, Category.id_comp]

omit [HasLimitsOfShape ℕᵒᵖ E] [HasExactLimitsOfShape (Discrete ℕ) E]
  [HasDerivedCategory E] in
/-- For a tower of complexes with degreewise split epimorphic transition maps the difference map
on the product is an epimorphism of complexes. -/
lemma epi_difference_of_degreewise_isSplitEpi
    (F : ℕᵒᵖ ⥤ CochainComplex E ℤ)
    (ht : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((F.map (homOfLE (Nat.le_succ n)).op).f i)) :
    Epi (inverseSystemDifference F) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  let G := HomologicalComplex.eval E (.up ℤ) i
  have hs : IsSplitEpi (inverseSystemDifference (F ⋙ G)) :=
    isSplitEpi_difference_of_isSplitEpi (F ⋙ G) (fun n ↦ ht n i)
  exact epi_map_inverseSystemDifference G F hs

/-- For a tower of complexes with degreewise split epimorphic transition maps the limit sits in
the Milnor triangle `lim Fₙ ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ (lim Fₙ)[1]` of the derived category: the short
exact sequence `0 ⟶ lim ⟶ ∏ ⟶ ∏ ⟶ 0` of complexes gives a distinguished triangle. -/
lemma exists_distTriang_limit_of_degreewise_isSplitEpi
    (F : ℕᵒᵖ ⥤ CochainComplex E ℤ)
    [HasProductsOfShape ℕ (DerivedCategory E)]
    (ht : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((F.map (homOfLE (Nat.le_succ n)).op).f i)) :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (F ⋙ DerivedCategory.Q).obj ⟨n⟩) ⟶
        (DerivedCategory.Q.obj (limit F))⟦(1 : ℤ)⟧,
      Triangle.mk (Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map (limit.π F ⟨n⟩))
        (inverseSystemDifference (F ⋙ DerivedCategory.Q)) δ ∈
          distTriang (DerivedCategory E) := by
  let Q := DerivedCategory.Q (C := E)
  let S : ShortComplex (CochainComplex E ℤ) := {
    X₁ := limit F
    X₂ := ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩
    X₃ := ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩
    f := Pi.lift fun n : ℕ ↦ limit.π F ⟨n⟩
    g := inverseSystemDifference F
    zero := (inverseSystemLimitKernelFork F).condition }
  have hmono : Mono S.f := mono_of_isLimit_fork (inverseSystemLimitKernelForkIsLimit F)
  have hepi : Epi S.g := epi_difference_of_degreewise_isSplitEpi F ht
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_of_f_is_kernel _ (inverseSystemLimitKernelForkIsLimit F) }
  have hdist := DerivedCategory.triangleOfSES_distinguished hS
  have : PreservesLimitsOfShape (Discrete ℕ) Q :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let e := asIso (piComparison Q (fun n : ℕ ↦ F.obj ⟨n⟩))
  let p := Pi.lift fun n : ℕ ↦ Q.map (limit.π F ⟨n⟩)
  have h1 : p ≫ e.inv = Q.map S.f := by
    have hp : Q.map S.f ≫ e.hom = p := by
      apply Pi.hom_ext
      intro n
      rw [Category.assoc]
      show Q.map (Pi.lift (fun n : ℕ ↦ limit.π F ⟨n⟩)) ≫
        e.hom ≫ Pi.π _ n = p ≫ Pi.π _ n
      have he := piComparison_comp_π Q (fun n : ℕ ↦ F.obj ⟨n⟩) n
      change e.hom ≫ Pi.π _ n = Q.map (Pi.π _ n) at he
      rw [he, ← Q.map_comp]
      show Q.map ((Pi.lift (fun n : ℕ ↦ limit.π F ⟨n⟩)) ≫ Pi.π _ n) = _
      rw [Pi.lift_comp_π, Pi.lift_comp_π]
    rw [← hp, Category.assoc, e.hom_inv_id, Category.comp_id]
  have h2 : inverseSystemDifference (F ⋙ Q) ≫ e.inv = e.inv ≫ Q.map S.g := by
    have he : Q.map S.g ≫ e.hom = e.hom ≫ inverseSystemDifference (F ⋙ Q) :=
      map_inverseSystemDifference_comp_piComparison Q F
    rw [Iso.comp_inv_eq, Category.assoc, he, Iso.inv_hom_id_assoc]
  refine ⟨e.inv ≫ DerivedCategory.triangleOfSESδ hS, ?_⟩
  refine isomorphic_distinguished _ hdist _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ h2 ?_)
  · exact h1.trans (Category.id_comp _).symm
  · show (e.inv ≫ DerivedCategory.triangleOfSESδ hS) ≫
        (shiftFunctor (DerivedCategory E) (1 : ℤ)).map
          (𝟙 (DerivedCategory.Q.obj (limit F))) =
      e.inv ≫ DerivedCategory.triangleOfSESδ hS
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The Milnor-sequence engine.** A cone over a tower of complexes whose transition maps are
degreewise split epimorphisms, which is a quasi-isomorphism in each fixed degree far enough
along the tower, induces a quasi-isomorphism to the limit. -/
lemma quasiIso_limitLift_of_eventually_quasiIsoAt
    (F : ℕᵒᵖ ⥤ CochainComplex E ℤ) (c : Cone F)
    (ht : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((F.map (homOfLE (Nat.le_succ n)).op).f i))
    (h : ∀ i : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → QuasiIsoAt (c.π.app ⟨n⟩) i) :
    QuasiIso (limit.lift F c) := by
  have := Stacks.DerivedProducts.hasProductsOfShape_nat (A := E)
  obtain ⟨δ, hδ⟩ := exists_distTriang_limit_of_degreewise_isSplitEpi F ht
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  apply isIso_of_eventually_isIso_homology (F ⋙ DerivedCategory.Q)
    (DerivedCategory.Q.mapCone c) (DerivedCategory.Q.map (limit.lift F c))
    (Pi.lift fun n : ℕ ↦ DerivedCategory.Q.map (limit.π F ⟨n⟩)) δ hδ
  · intro n
    rw [Pi.lift_comp_π, ← Functor.map_comp, limit.lift_π]
    rfl
  · intro i
    obtain ⟨N, hN⟩ := h i
    refine ⟨N, fun n hn ↦ ?_⟩
    show IsIso
      ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor E i).map (c.π.app ⟨n⟩))
    rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors E i)]
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 (hN n hn)

end DerivedLimit

section KInjectiveTower

open ZeroObject

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
  [HasProductsOfShape ℕ C] [HasLimitsOfShape ℕᵒᵖ C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasProductsOfShape ℕ D] [HasLimitsOfShape ℕᵒᵖ D]
  [HasExactLimitsOfShape (Discrete ℕ) D] [HasDerivedCategory.{wD} D]

/-- **The tower of injective resolutions of the truncations.** For a functor reflecting
quasi-isomorphisms and a complex whose truncations have termwise right acyclic terms, there is
a quasi-isomorphism into a K-injective complex which the functor also carries to a
quasi-isomorphism. -/
lemma exists_quasiIso_isKInjective_map_quasiIso
    (F : C ⥤ D) [F.Additive] [PreservesLimitsOfSize.{0, 0} F]
    (hF : ∀ {K L : CochainComplex C ℤ} (f : K ⟶ L),
      QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) → QuasiIso f)
    (K : CochainComplex C ℤ)
    (hacyclic : ∀ (n i : ℤ), F.rightAcyclic ((K.truncGE n).X i)) :
    ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f ∧ QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let T := F.mapHomologicalComplex (.up ℤ)
  have : PreservesLimitsOfShape ℕᵒᵖ T := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro i
    show PreservesLimitsOfShape ℕᵒᵖ ((HomologicalComplex.eval C (.up ℤ) i) ⋙ F)
    infer_instance
  have : ObjectProperty.ContainsZero (C := C) (fun X ↦ Injective X) :=
    ⟨⟨0, isZero_zero _, inferInstance⟩⟩
  obtain ⟨I, f, g, hf, -, hGE, hinj, hsplit, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncGE (fun X : C ↦ Injective X)
      (fun X Y hX hY ↦ by have := hX; have := hY; infer_instance)
      (fun X ↦ ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩) K
  let tower := Functor.ofOpSequence g
  have hg (n : ℕ) (i : ℤ) : IsSplitEpi ((tower.map (homOfLE (Nat.le_succ n)).op).f i) := by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    obtain ⟨W, _, e, he⟩ := hsplit n i
    exact IsSplitEpi.mk' ⟨biprod.inl ≫ e.inv,
      (Category.assoc _ _ _).trans ((congrArg _ he).trans biprod.inl_fst)⟩
  have hKI (n : ℕ) : (tower.obj ⟨n⟩).IsKInjective := by
    have := hGE n
    have : ∀ i : ℤ, Injective ((I n).X i) := hinj n
    exact CochainComplex.isKInjective_of_injective (I n) (-(n : ℤ))
  obtain ⟨_, _, hlimKI, _, _⟩ :=
    CochainComplex.isKInjective_limit_and_isDerivedLimit_of_isSplitEpi tower hKI hg
  let c : Cone tower := {
    pt := K
    π := NatTrans.ofOpSequence (fun n ↦ K.πTruncGE (-(n : ℤ)) ≫ f n)
      (fun n ↦ by
        dsimp only [Functor.const_obj_map]
        refine (Category.id_comp _).trans ?_
        rw [show tower.map (homOfLE (Nat.le_succ n)).op = g n from
          Functor.ofOpSequence_map_homOfLE_succ g n]
        show K.πTruncGE (-(n : ℤ)) ≫ f n =
          (K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1)) ≫ g n
        exact (hladder n).symm.trans (Category.assoc _ _ _).symm) }
  have hTf (n : ℕ) : QuasiIso (T.map (f n)) := by
    have := hf n
    have := hGE n
    apply quasiIso_map_of_boundedBelow_acyclic F (f n)
      ⟨-(n : ℤ), inferInstance⟩ ⟨-(n : ℤ), inferInstance⟩ (hacyclic _)
    intro i
    have := hinj n i
    apply ((F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus ((I n).X i)).2
      inferInstance).2
    intro p hp
    exact F.isZero_rightDerivedPlus_obj_injective p (by omega) _
  have hγT : QuasiIso (limit.lift (tower ⋙ T) (T.mapCone c)) := by
    apply quasiIso_limitLift_of_eventually_quasiIsoAt
    · intro n i
      have := hg n i
      exact inferInstanceAs
        (IsSplitEpi (F.map ((tower.map (homOfLE (Nat.le_succ n)).op).f i)))
    · intro i
      refine ⟨(2 - i).toNat, fun n hn ↦ ?_⟩
      have : QuasiIsoAt (T.map (K.πTruncGE (-(n : ℤ)))) i :=
        quasiIsoAt_map_πTruncGE F K _ i (by omega)
      have := hTf n
      show QuasiIsoAt (T.map (K.πTruncGE (-(n : ℤ)) ≫ f n)) i
      rw [T.map_comp]
      infer_instance
  let γ := limit.lift tower c
  have heq : T.map γ ≫ (preservesLimitIso T tower).hom =
      limit.lift (tower ⋙ T) (T.mapCone c) := by
    apply limit.hom_ext
    intro n
    rw [Category.assoc, preservesLimitIso_hom_π, ← T.map_comp, limit.lift_π, limit.lift_π]
    rfl
  have hγ : QuasiIso (T.map γ) := by
    have : QuasiIso (T.map γ ≫ (preservesLimitIso T tower).hom) := by rw [heq]; exact hγT
    exact quasiIso_of_comp_right (T.map γ) ((preservesLimitIso T tower).hom)
  exact ⟨limit tower, γ, hlimKI, hF γ hγ, hγ⟩

end KInjectiveTower

/-- Forgetting the module structure reflects quasi-isomorphisms of complexes of sheaves of
modules, sheafification being exact and the counit of sheafification an isomorphism on
sheaves. -/
lemma quasiIso_of_forget_map_quasiIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{uD})
    [HasSheafify J AddCommGrpCat.{wC}] [J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
    {K L : CochainComplex (SheafOfModules.{wC} O) ℤ} (f : K ⟶ L)
    (hf : QuasiIso (((SheafOfModules.forget O).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  let G := SheafOfModules.forget.{wC} O
  let S := PresheafOfModules.sheafification.{wC} (𝟙 O.obj)
  let adj : S ⊣ _ := PresheafOfModules.sheafificationAdjunction.{wC} (𝟙 O.obj)
  have : S.Additive := adj.left_adjoint_additive
  have : S.PreservesHomology := Functor.preservesHomologyOfExact S
  have hcounit : IsIso adj.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    exact Adjunction.instIsIsoAppCounitOfFullOfFaithful _ N
  let e : G ⋙ S ≅ 𝟭 _ := @asIso _ _ _ _ adj.counit hcounit
  let eC := Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (SheafOfModules.{wC} O) (.up ℤ)
  have : QuasiIso (((G.mapHomologicalComplex (.up ℤ)) ⋙
      S.mapHomologicalComplex (.up ℤ)).map f) :=
    inferInstanceAs (QuasiIso ((S.mapHomologicalComplex (.up ℤ)).map
      ((G.mapHomologicalComplex (.up ℤ)).map f)))
  exact quasiIso_of_arrow_mk_iso _ f (Arrow.isoMk (eC.app K) (eC.app L)
    (eC.hom.naturality f).symm)

open ZeroObject in
/-- The terms of the truncations of a complex in the image of a cokernel-preserving additive
functor are again in its image, up to isomorphism. -/
lemma property_truncGE_map
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (L : C ⥤ D) [L.Additive] [PreservesColimitsOfShape WalkingParallelPair L]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ X, P (L.obj X)) (K : CochainComplex C ℤ) (n i : ℤ) :
    P ((CochainComplex.truncGE ((L.mapHomologicalComplex (.up ℤ)).obj K) n).X i) := by
  let T : CochainComplex D ℤ := (L.mapHomologicalComplex (.up ℤ)).obj K
  rcases lt_trichotomy i n with h | rfl | h
  · exact P.prop_of_iso
      (((Functor.map_isZero L (Limits.isZero_zero C)).iso
        ((T.truncGE n).isZero_of_isStrictlyGE n i h)))
      (hP 0)
  · let e : (T.truncGE i).X i ≅ L.obj (K.opcycles i) :=
      T.truncGEXIsoOpcycles i ≪≫ (T.sc i).opcyclesIsoCokernel ≪≫
        (PreservesCokernel.iso L (K.sc i).f).symm ≪≫
        L.mapIso (K.sc i).opcyclesIsoCokernel.symm
    exact P.prop_of_iso e.symm (hP _)
  · exact P.prop_of_iso (T.truncGEXIso n i h).symm (hP (K.X i))


/-- Countable products of presheaves of modules are exact: they are computed objectwise in
abelian groups. -/
lemma presheafModules_hasExactCountableProducts
    {C : Type uC} [Category.{vC} C] (O : Cᵒᵖ ⥤ RingCat.{uD}) :
    HasExactLimitsOfShape (Discrete ℕ) (PresheafOfModules.{wC} O) := by
  have : HasLimitsOfShape (Discrete ℕ) AddCommGrpCat.{wC} := AddCommGrpCat.hasLimitsOfShape
  have : HasLimitsOfShape (Discrete ℕ) (Cᵒᵖ ⥤ AddCommGrpCat.{wC}) := inferInstance
  have : HasProducts.{wC} (Cᵒᵖ ⥤ AddCommGrpCat.{wC}) := fun _ =>
    @functorCategoryHasLimitsOfShape _ _ _ _ _ _ AddCommGrpCat.hasLimitsOfShape
  have : HasExactLimitsOfShape (Discrete ℕ) (Cᵒᵖ ⥤ AddCommGrpCat.{wC}) := inferInstance
  exact HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) (PresheafOfModules.toPresheaf O)

end Stacks.TruncationTower

end
