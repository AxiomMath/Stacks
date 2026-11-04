module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsPseudoCoherenceStep
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedRestrictionMonoidal

/-!
# An invertible object of the derived category of a ringed site is pseudo-coherent

Let `(C, O)` be a ringed site and let `M` be an invertible object of `D(O)`. If `M` is
`m`-pseudo-coherent then it is `(m - 1)`-pseudo-coherent; since an object concentrated in
degrees `≤ b` is `(b + 1)`-pseudo-coherent, an invertible object concentrated in degrees `≤ b` is
pseudo-coherent. This is the descending induction of the last paragraph of the source's proof of
the first assertion of Stacks 0FPV, for an invertible object.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.isPseudoCoherentFrom_sub_one`: the inductive
  step.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.isPseudoCoherentFrom_of_isLE`: the induction.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite Stacks.SheafOfModules.DerivedMonoidal ZeroObject

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The brutal truncation `σ^{≥a}` of a strictly perfect complex is strictly perfect, and
vanishes below `a`.** -/
theorem isStrictlyPerfect_and_isStrictlyGE_stupidTruncGE {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) (a : ℤ) (hK : IsStrictlyPerfect R K) :
    IsStrictlyPerfect R (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)) ∧
      CochainComplex.IsStrictlyGE (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)) a := by
  have hz : ∀ i, i < a → IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X i) :=
    fun i hi => K.isZero_stupidTrunc_X _ i (fun j => by
      rw [ComplexShape.embeddingUpIntGE_f]; omega)
  refine ⟨⟨hK.bounded.subset ?_, fun i => ?_⟩, ⟨fun i hi => hz i (by
    by_contra h
    exact hi ((i - a).toNat) (by rw [ComplexShape.embeddingUpIntGE_f]; omega))⟩⟩
  · intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    by_cases hai : a ≤ i
    · have := K.isIso_ιStupidTrunc_embeddingUpIntGE_f a i hai
      exact fun h => hi (h.of_iso (asIso ((K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)).f i)))
    · exact absurd (hz i (by omega)) hi
  · by_cases hai : a ≤ i
    · have := K.isIso_ιStupidTrunc_embeddingUpIntGE_f a i hai
      exact IsDirectSummandOfFiniteFree.of_iso R
        (asIso ((K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)).f i))
        (hK.termDirectSummand i)
    · exact IsDirectSummandOfFiniteFree.of_isZero_general R (hz i (by omega))

variable {X : RingedSite.{u, u, u}} [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **An invertible object restricts to an invertible object.** Derived restriction to the
localized site `C/V` is strongly monoidal
(`Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal`), so `M ⊗ N ≅ 𝟙` restricts to
`M|_V ⊗ N|_V ≅ 𝟙`. -/
def restrictTensorIsoUnit (V : X.C) (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (e : letI := derivedMonoidal X.O; M ⊗ N ≅ 𝟙_ _) :
    letI := derivedMonoidal (X.over V).O
    (ovF X V).mapDerivedCategory.obj M ⊗ (ovF X V).mapDerivedCategory.obj N ≅
      𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules (X.over V).O) :=
  letI := derivedMonoidal X.O
  letI := derivedMonoidal (X.over V).O
  letI := Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X V
  Functor.Monoidal.μIso _ M N ≪≫ (ovF X V).mapDerivedCategory.mapIso e ≪≫
    (Functor.Monoidal.εIso _).symm

/-- A morphism of the derived category induced by a map of complexes is invertible on cohomology
in a degree as soon as the map of complexes is. -/
theorem isIso_homologyFunctor_map_Q_map_comp {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {K L : CochainComplex A ℤ} {M : DerivedCategory A} (f : K ⟶ L)
    (e : DerivedCategory.Q.obj L ≅ M) (i : ℤ) (h : IsIso (HomologicalComplex.homologyMap f i)) :
    IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map f ≫ e.hom)) := by
  rw [Functor.map_comp]
  have : IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map f)) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A i) f).2 h
  infer_instance

/-- A morphism of the derived category induced by a map of complexes is onto on cohomology in a
degree as soon as the map of complexes is. -/
theorem epi_homologyFunctor_map_Q_map_comp {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {K L : CochainComplex A ℤ} {M : DerivedCategory A} (f : K ⟶ L)
    (e : DerivedCategory.Q.obj L ≅ M) (i : ℤ) (h : Epi (HomologicalComplex.homologyMap f i)) :
    Epi ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map f ≫ e.hom)) := by
  rw [Functor.map_comp]
  have : Epi ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map f)) :=
    (epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors A i) f).2 h
  infer_instance

/-- **The inductive step.** If an invertible object `M` of `D(O)` is `m`-pseudo-coherent, it is
`(m - 1)`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_sub_one
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (e : letI := derivedMonoidal X.O; M ⊗ N ≅ 𝟙_ _) (m : ℤ) (h : X.IsPseudoCoherentFrom M m) :
    X.IsPseudoCoherentFrom M (m - 1) := by
  obtain ⟨K₀, hK₀, ⟨eK₀⟩⟩ := h
  refine isPseudoCoherentFrom_of_locally_general X M (m - 1) (fun U => ?_)
  obtain ⟨S, hS, hdata⟩ := hK₀ U
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨P, hP, α₀, hiso, hepi⟩ := hdata f hf
  let P' : Complexes (X.over V).O := P
  obtain ⟨hEP, hEGE⟩ := isStrictlyPerfect_and_isStrictlyGE_stupidTruncGE P' m hP
  let K₀' : Complexes (X.over V).O := X.restrictComplex K₀ V
  let α₀' : P' ⟶ K₀' := α₀
  have hiso' : ∀ i, m < i → IsIso (HomologicalComplex.homologyMap α₀' i) := hiso
  have hepi' : Epi (HomologicalComplex.homologyMap α₀' m) := hepi
  let eR : DerivedCategory.Q.obj K₀' ≅ (ovF X V).mapDerivedCategory.obj M :=
    ((ovF X V).mapDerivedCategoryFactors.app K₀).symm ≪≫ (ovF X V).mapDerivedCategory.mapIso eK₀
  let β : P'.stupidTrunc (ComplexShape.embeddingUpIntGE m) ⟶ K₀' :=
    P'.ιStupidTrunc (ComplexShape.embeddingUpIntGE m) ≫ α₀'
  refine isPseudoCoherentFrom_sub_one_of_approximation (X := X.over V) _ _
    (restrictTensorIsoUnit V M N e) m _ hEP (DerivedCategory.Q.map β ≫ eR.hom) (fun i hi => ?_) ?_
  · refine isIso_homologyFunctor_map_Q_map_comp β eR i ?_
    rw [HomologicalComplex.homologyMap_comp]
    have := StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE P' m i hi
    have := hiso' i hi
    infer_instance
  · refine epi_homologyFunctor_map_Q_map_comp β eR m ?_
    rw [HomologicalComplex.homologyMap_comp]
    have := P'.epi_homologyMap_ιStupidTrunc_embeddingUpIntGE m
    exact epi_comp _ _

/-- An object of `D(O)` concentrated in degrees `≤ b` is `(b + 1)`-pseudo-coherent: the zero
complex approximates it. -/
theorem isPseudoCoherentFrom_add_one_of_isLE
    (M : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O) (b : ℤ) (hb : M.IsLE b) :
    X.IsPseudoCoherentFrom M (b + 1) := by
  let K := DerivedCategory.Q.objPreimage M
  let eK : DerivedCategory.Q.obj K ≅ M := DerivedCategory.Q.objObjPreimageIso M
  have hz : ∀ j, b < j → IsZero (K.homology j) := fun j hj =>
    ((DerivedCategory.isLE_iff M b).1 hb j hj).of_iso
      (((DerivedCategory.homologyFunctorFactors _ j).app K).symm ≪≫
        (DerivedCategory.homologyFunctor _ j).mapIso eK)
  let P : Complexes X.O := 0
  have hP0 : ∀ i, IsZero (P.X i) := fun i =>
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i).map_isZero (isZero_zero _)
  have hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P :=
    ⟨Set.finite_empty.subset fun i hi => hi (hP0 i),
      fun i => IsDirectSummandOfFiniteFree.of_isZero_general _ (hP0 i)⟩
  refine ⟨K, isPseudoCoherentComplexFrom_of_approximation X K P (b + 1) hP 0 (fun j hj => ?_)
    ((hz (b + 1) (by omega)).epi _), ⟨eK⟩⟩
  exact ⟨⟨0, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map_isZero
    (isZero_zero _)).eq_of_src _ _, (hz j (by omega)).eq_of_src _ _⟩⟩

/-- **An invertible object concentrated in degrees `≤ b` is `n`-pseudo-coherent for every
`n`.** Descending induction from `b + 1` by `isPseudoCoherentFrom_sub_one`. -/
theorem isPseudoCoherentFrom_of_isLE
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (e : letI := derivedMonoidal X.O; M ⊗ N ≅ 𝟙_ _) (b : ℤ) (hb : M.IsLE b) (n : ℤ) :
    X.IsPseudoCoherentFrom M n := by
  have key : ∀ k : ℕ, X.IsPseudoCoherentFrom M (b + 1 - k) := by
    intro k
    induction k with
    | zero => simpa using isPseudoCoherentFrom_add_one_of_isLE M b hb
    | succ k ih =>
      have := isPseudoCoherentFrom_sub_one M N e _ ih
      rwa [show b + 1 - (k : ℤ) - 1 = b + 1 - ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
  rcases le_or_gt n (b + 1) with h | h
  · have := key (b + 1 - n).toNat
    rwa [Int.toNat_of_nonneg (by omega), show b + 1 - (b + 1 - n) = n by ring] at this
  · have hb' : M.IsLE (n - 1) := by
      rw [DerivedCategory.isLE_iff] at hb ⊢
      exact fun i hi => hb i (by omega)
    simpa using isPseudoCoherentFrom_add_one_of_isLE M (n - 1) hb'

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
