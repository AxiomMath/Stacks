module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicDualDegreeZero
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.StupidTruncationNaturality

/-!
# The transitions of the Koszul tower, and the bottom step of its stupid filtration

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `Kᵐ` be the
Koszul complex on `f_1^{m+1}, …, f_r^{m+1}`, in the grading of [Stacks, Tag 0913] in which its
degree-`p` term is the product of copies of `𝒪` indexed by the subsets `S ⊆ {1, …, r}` of
cardinality `p`. This file supplies two facts about these complexes which the brutal
filtration `σ^{≥p}Kᵐ` of the Koszul tower consumes.

* **The transitions.** For `m ≤ m'` the transition `Kᵐ ⟶ Kᵐ'` of the tower
  `AlgebraicGeometry.RingedSite.koszulPowerSystem` is, in the factor indexed by `S`,
  multiplication by `f_S^{m' - m}`. The tower is defined by its successive transitions, so this
  is the composite of `m' - m` of them, computed once.
* **The bottom step.** The degree-zero term of `Kᵐ` is a single copy of `𝒪`, and the map
  `Kᵐ ⟶ 𝒪[0]` which the comparison with the extended Čech complex followed by the Čech
  augmentation induces is the projection onto it. Hence
  `0 ⟶ σ^{≥1}Kᵐ ⟶ Kᵐ ⟶ 𝒪[0] ⟶ 0` is a short exact sequence which is split in every degree, whose
  second map is **exactly** that composite.

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulPowerTransLE`: the morphism of systems from the
  `(m+1)`-st to the `(m'+1)`-st Koszul powers, multiplication by `f_S^{m' - m}` at `S`.
* `AlgebraicGeometry.RingedSite.koszulAugmentationShortComplex`: the short complex
  `σ^{≥1}Kᵐ ⟶ Kᵐ ⟶ 𝒪[0]`.

## Main results

* `AlgebraicGeometry.RingedSite.koszulPowerSystem_map_eq`: the transitions of the Koszul tower.
* `AlgebraicGeometry.RingedSite.isIso_koszulCechComplexMap_comp_cechAugmentation_f_zero`: in
  degree zero the augmentation of a Koszul complex is invertible.
* `AlgebraicGeometry.RingedSite.nonempty_splitting_koszulAugmentationShortComplex`: the short
  complex `σ^{≥1}Kᵐ ⟶ Kᵐ ⟶ 𝒪[0]` is split in every degree.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

namespace AlgebraicGeometry.RingedSite

universe u

section Transitions

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The exponent vector of the transition of the Koszul tower across `d` steps at the subset
`S`: the exponent `d` at the indices of `S`. -/
def koszulPowerTransExp (d : ℕ) (S : Finset (Fin r)) : Fin r → ℕ :=
  fun i => if i ∈ S then d else 0

/-- **The morphism of systems from the `(m+1)`-st to the `(m'+1)`-st Koszul powers**: at the
subset `S` it is multiplication by `f_S^{m' - m}`. Its naturality is the identity
`f_{T ∖ S}^{m+1} · f_T^{m'-m} = f_S^{m'-m} · f_{T ∖ S}^{m'+1}` for `S ⊆ T`. -/
def koszulPowerTransLE {m m' : ℕ} (h : m ≤ m') :
    koszulPowerFunctor X f m ⟶ koszulPowerFunctor X f m' where
  app S := koszulScalar X f (koszulPowerTransExp (m' - m) S)
  naturality {S T} g := by
    change koszulScalar X f (koszulExp m S T) ≫ koszulScalar X f _ =
      koszulScalar X f _ ≫ koszulScalar X f (koszulExp m' S T)
    rw [koszulScalar_comp, koszulScalar_comp]
    refine koszulScalar_congr X f fun i => ?_
    have hST : S ⊆ T := leOfHom g
    by_cases hiT : i ∈ T
    · by_cases hiS : i ∈ S
      · simp [koszulExp, koszulPowerTransExp, hiT, hiS, Finset.mem_sdiff]
      · simp only [koszulExp, koszulPowerTransExp, hiT, hiS, Finset.mem_sdiff, Pi.add_apply,
          not_false_eq_true, and_self, if_true, if_false]
        omega
    · simp [koszulExp, koszulPowerTransExp, hiT, Finset.mem_sdiff,
        show i ∉ S from fun hiS => hiT (hST hiS)]

/-- The component of `AlgebraicGeometry.RingedSite.koszulPowerTransLE` at `S` is multiplication
by `f_S^{m' - m}`. -/
@[simp]
theorem koszulPowerTransLE_app {m m' : ℕ} (h : m ≤ m') (S : Finset (Fin r)) :
    (koszulPowerTransLE X f h).app S = koszulScalar X f (koszulPowerTransExp (m' - m) S) :=
  rfl

/-- **The transitions of the Koszul tower**: for `m ≤ m'` the map `Kᵐ ⟶ Kᵐ'` is the map of
alternating Čech complexes induced by multiplication by `f_S^{m' - m}` at every subset `S`. -/
theorem koszulPowerSystem_map_eq {m m' : ℕ} (h : m ≤ m') :
    (koszulPowerSystem X f).map (homOfLE h) =
      CategoryTheory.AlternatingCech.map (koszulPowerTransLE X f h) := by
  induction m', h using Nat.le_induction with
  | base =>
    have h0 : koszulPowerTransLE X f (le_refl m) = 𝟙 _ := by
      refine NatTrans.ext (funext fun S => ?_)
      rw [koszulPowerTransLE_app, NatTrans.id_app,
        koszulScalar_congr X f (e' := 0) fun i => by simp [koszulPowerTransExp]]
      exact koszulScalar_zero X f
    rw [h0, CategoryTheory.AlternatingCech.map_id]
    exact (congrArg (koszulPowerSystem X f).map (Subsingleton.elim _ (𝟙 m))).trans
      ((koszulPowerSystem X f).map_id m)
  | succ m' hm ih =>
    have hα : koszulPowerTransLE X f hm ≫ koszulPowerTrans X f m' =
        koszulPowerTransLE X f (hm.trans (m'.le_add_right 1)) := by
      refine NatTrans.ext (funext fun S => ?_)
      rw [NatTrans.comp_app, koszulPowerTransLE_app, koszulPowerTransLE_app]
      show koszulScalar X f _ ≫ koszulScalar X f _ = _
      rw [koszulScalar_comp]
      refine koszulScalar_congr X f fun i => ?_
      by_cases hiS : i ∈ S
      · simp only [koszulPowerTransExp, hiS, Pi.add_apply, if_true]
        omega
      · simp [koszulPowerTransExp, hiS]
    rw [show homOfLE (hm.trans (m'.le_add_right 1)) = homOfLE hm ≫ homOfLE (m'.le_add_right 1)
        from rfl, CategoryTheory.Functor.map_comp, ih, koszulPowerSystem_map_succ,
      koszulPowerComplexMap]
    exact (CategoryTheory.AlternatingCech.map_comp _ _).symm.trans (congrArg _ hα)

/-- The degree-`p` component of a transition of the Koszul tower. -/
theorem koszulPowerSystem_map_f {m m' : ℕ} (h : m ≤ m') (p : ℤ) :
    ((koszulPowerSystem X f).map (homOfLE h)).f p =
      CategoryTheory.AlternatingCech.mapX (koszulPowerTransLE X f h) p := by
  rw [koszulPowerSystem_map_eq]
  rfl

end Transitions

section Augmentation

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

open CategoryTheory.AlternatingCech

attribute [local instance] hasFiniteBiproducts_sheafOfModules

/-- **In degree zero the augmentation of a Koszul complex is invertible.** The degree-zero term
is the product of copies of `𝒪` over the subsets of cardinality zero, of which there is only
the empty one, and the augmentation is the projection onto it. -/
theorem isIso_koszulCechComplexMap_comp_cechAugmentation_f_zero
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] (n : ℕ) :
    IsIso ((koszulCechComplexMap X f n ≫ cechAugmentation X f).f 0) := by
  have hι : IsIso (termι (koszulPowerFunctor X f n) (default : Idx r (0 : ℤ))) := by
    refine ⟨⟨Pi.π (fun T : Idx r (0 : ℤ) => (koszulPowerFunctor X f n).obj T.1) default,
      termι_comp_π_self _ _, ?_⟩⟩
    have h := π_comp_termι_sum (koszulPowerFunctor X f n) (p := (0 : ℤ))
    rwa [Fintype.sum_unique] at h
  have hw : IsIso ((koszulCechComplexMap X f n).f 0 ≫ cechAugmentationZero X f) := by
    have h := termι_comp_koszulCechComplexMap_f_zero_comp_cechAugmentationZero X f n default
    have : IsIso (termι (koszulPowerFunctor X f n) (default : Idx r (0 : ℤ)) ≫
        (koszulCechComplexMap X f n).f 0 ≫ cechAugmentationZero X f) := by
      rw [h]; exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
    exact IsIso.of_isIso_comp_left
      (termι (koszulPowerFunctor X f n) (default : Idx r (0 : ℤ))) _
  rw [comp_f, cechAugmentation_f_zero, ← Category.assoc]
  infer_instance

/-- The inclusion of the first brutal truncation of a Koszul complex is killed by its
augmentation, the truncation vanishing in degree zero. -/
theorem ιStupidTrunc_comp_koszulCechComplexMap_comp_cechAugmentation (n : ℕ) :
    (koszulPowerComplex X f n).ιStupidTrunc (embeddingUpIntGE (1 : ℤ)) ≫
        koszulCechComplexMap X f n ≫ cechAugmentation X f = 0 := by
  apply to_single_hom_ext
  exact (CochainComplex.isZero_of_isStrictlyGE
    ((koszulPowerComplex X f n).stupidTrunc (embeddingUpIntGE (1 : ℤ))) 1 0
    (by omega)).eq_of_src _ _

/-- **The bottom step of the stupid filtration of a Koszul complex**: the short complex
`σ^{≥1}Kⁿ ⟶ Kⁿ ⟶ 𝒪[0]` whose first map is the inclusion of the first brutal truncation and whose
second map is the comparison with the extended Čech complex followed by the Čech augmentation. -/
def koszulAugmentationShortComplex (n : ℕ) :
    ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  ShortComplex.mk ((koszulPowerComplex X f n).ιStupidTrunc (embeddingUpIntGE (1 : ℤ)))
    (koszulCechComplexMap X f n ≫ cechAugmentation X f)
    (ιStupidTrunc_comp_koszulCechComplexMap_comp_cechAugmentation X f n)

/-- The first map of `AlgebraicGeometry.RingedSite.koszulAugmentationShortComplex` is the
inclusion of the first brutal truncation. -/
@[simp]
theorem koszulAugmentationShortComplex_f (n : ℕ) :
    (koszulAugmentationShortComplex X f n).f =
      (koszulPowerComplex X f n).ιStupidTrunc (embeddingUpIntGE (1 : ℤ)) :=
  rfl

/-- The second map of `AlgebraicGeometry.RingedSite.koszulAugmentationShortComplex` is the
augmentation. -/
@[simp]
theorem koszulAugmentationShortComplex_g (n : ℕ) :
    (koszulAugmentationShortComplex X f n).g = koszulCechComplexMap X f n ≫ cechAugmentation X f :=
  rfl

/-- **The short complex `σ^{≥1}Kⁿ ⟶ Kⁿ ⟶ 𝒪[0]` is split in every degree.** In degree zero the
truncation vanishes and the augmentation is invertible; in a positive degree the inclusion of
the truncation is invertible; in a negative degree all three terms vanish; and `𝒪[0]` vanishes
outside degree zero. -/
theorem nonempty_splitting_koszulAugmentationShortComplex
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (n : ℕ) (d : ℤ) :
    Nonempty (((koszulAugmentationShortComplex X f n).map
      (eval (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (.up ℤ) d)).Splitting) := by
  by_cases hd : d = 0
  · subst d
    refine ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _ ?_ ?_⟩
    · exact CochainComplex.isZero_of_isStrictlyGE
        ((koszulPowerComplex X f n).stupidTrunc (embeddingUpIntGE (1 : ℤ))) 1 0 (by omega)
    · exact isIso_koszulCechComplexMap_comp_cechAugmentation_f_zero X f n
  · refine ⟨ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_ ?_⟩
    · show IsIso (((koszulPowerComplex X f n).ιStupidTrunc (embeddingUpIntGE (1 : ℤ))).f d)
      by_cases hpd : 1 ≤ d
      · rw [StacksDraft.StupidTruncation.ιStupidTruncGE_f _ 1 d hpd]
        infer_instance
      · exact IsZero.isIso
          (CochainComplex.isZero_of_isStrictlyGE
            ((koszulPowerComplex X f n).stupidTrunc (embeddingUpIntGE (1 : ℤ))) 1 d (by omega))
          (isZero_koszulPowerComplex_X_of_neg X f n (by omega)) _
    · exact isZero_single_obj_X (.up ℤ) 0 _ d hd

end Augmentation

end AlgebraicGeometry.RingedSite

end
