module

public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.SpectralSequenceFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.PageTwo
import all StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.SpectralSequenceFunctor
import all StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.PageTwo

/-!
# The first-quadrant abutment of the functorial Grothendieck spectral sequence

The abutment filtration of a first-quadrant spectral object by the images of its `H`-terms,
built once in the functor category, and the resulting functorial filtered abutment
`natAbutment` of the Grothendieck spectral sequence of a single object of `𝒜` to `R^n(G ∘ F)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Grothendieck

open Stacks.Cohomology.HigherDirectImagePresheaf (derivedPlusToStandard)

attribute [local instance] HasDerivedCategory.standard

section Construction

open CategoryTheory.ComposableArrows

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section FirstQuadrant

open Opposite


/-- Over an interval whose two outer terms contribute nothing, the `E`-term of a spectral
object agrees with the `E`-term of the whole interval. -/
private noncomputable def spectralObjectEIsoPageInfinity
    {A : Type*} [Category A] [Abelian A]
    (S : CategoryTheory.Abelian.SpectralObject A EInt)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i₀ i₁ i₂ i₃ : EInt)
    (hbot : (⊥ : EInt) ≤ i₀)
    (hi₀₁ : i₀ ≤ i₁) (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃)
    (htop : i₃ ≤ ⊤)
    (hzero₀ : IsZero ((S.H n₂).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))))
    (hzero₃ : IsZero ((S.H n₀).obj
      (mk₁ (homOfLE (show i₃ ≤ ⊤ by simp))))) :
    S.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) n₀ n₁ n₂ hn₁ hn₂ ≅
      S.E (homOfLE (show (⊥ : EInt) ≤ i₁ by simp)) (homOfLE hi₁₂)
        (homOfLE (show i₂ ≤ ⊤ by simp)) n₀ n₁ n₂ hn₁ hn₂ := by
  let e₁ := S.isoMapFourδ₁Toδ₀' ⊥ i₀ i₁ i₂ i₃
    hbot hi₀₁ hi₁₂ hi₂₃ n₀ n₁ n₂ hzero₀ hn₁ hn₂
  let e₃ := S.isoMapFourδ₄Toδ₃' ⊥ i₁ i₂ i₃ ⊤
    bot_le hi₁₂ hi₂₃ htop n₀ n₁ n₂ hzero₃ hn₁ hn₂
  exact e₁.symm ≪≫ e₃

/-! ### A butterfly lemma for images and the whole-interval `E`-term -/

/-- Two factorisation conditions, through the image of a biproduct map and through the
image of a composite, agree along an exact sequence. -/
private lemma imageRelation_factors_iff
    {C : Type*} [Category C] [Abelian C] {A J D H T : C}
    (j : J ⟶ D) (k : A ⟶ D) (u : D ⟶ H)
    (hku : k ≫ u = 0) (hExact : (ShortComplex.mk k u hku).Exact)
    (g : T ⟶ D) :
    (imageSubobject (biprod.desc j k)).Factors g ↔
      (imageSubobject (j ≫ u)).Factors (g ≫ u) := by
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨T', z, hz, x, hx⟩ :=
      (Subobject.imageSubobject_factors_iff (biprod.desc j k) g).1 hg
    apply (Subobject.imageSubobject_factors_iff (j ≫ u) (g ≫ u)).2
    have hdu : biprod.desc j k ≫ u = biprod.fst ≫ j ≫ u := by
      rw [biprod.desc_eq, Preadditive.add_comp]
      simp only [Category.assoc, hku, comp_zero, add_zero]
    refine ⟨T', z, hz, x ≫ biprod.fst, ?_⟩
    simp only [Category.assoc, reassoc_of% hx, hdu]
  · obtain ⟨T₁, z₁, hz₁, x₁, hx₁⟩ :=
      (Subobject.imageSubobject_factors_iff (j ≫ u) (g ≫ u)).1 hg
    have hzero : (z₁ ≫ g - x₁ ≫ j) ≫ u = 0 := by
      rw [Preadditive.sub_comp]
      have hx₁' : z₁ ≫ g ≫ u = x₁ ≫ j ≫ u := by
        simpa only [Category.assoc] using hx₁
      simpa only [Category.assoc] using (sub_eq_zero.mpr hx₁')
    have hkernel : (kernelSubobject u).Factors (z₁ ≫ g - x₁ ≫ j) :=
      (kernelSubobject_factors_iff u _).2 hzero
    let S : ShortComplex C := ShortComplex.mk k u hku
    have heq : imageSubobject k = kernelSubobject u :=
      S.exact_iff_image_eq_kernel.1 hExact
    rw [← heq] at hkernel
    obtain ⟨T₂, z₂, hz₂, x₂, hx₂⟩ :=
      (Subobject.imageSubobject_factors_iff k (z₁ ≫ g - x₁ ≫ j)).1 hkernel
    apply (Subobject.imageSubobject_factors_iff (biprod.desc j k) g).2
    refine ⟨T₂, z₂ ≫ z₁, epi_comp _ _, biprod.lift (z₂ ≫ x₁) x₂, ?_⟩
    have hdiff : z₂ ≫ z₁ ≫ g - z₂ ≫ x₁ ≫ j = x₂ ≫ k := by
      simpa only [Preadditive.comp_sub, Category.assoc] using hx₂
    have hsum : z₂ ≫ z₁ ≫ g = z₂ ≫ x₁ ≫ j + x₂ ≫ k := by
      rw [← sub_add_cancel (z₂ ≫ z₁ ≫ g) (z₂ ≫ x₁ ≫ j), hdiff, add_comm]
    simpa only [Category.assoc, biprod.lift_desc] using hsum

/-- The image of a map out of a biproduct is the join of the images of its components. -/
private lemma image_biprod_desc
    {C : Type*} [Category C] [Abelian C] {J A D : C}
    (j : J ⟶ D) (k : A ⟶ D) :
    imageSubobject (biprod.desc j k) = imageSubobject j ⊔ imageSubobject k := by
  let Q : Subobject D := imageSubobject j ⊔ imageSubobject k
  have hj : Q.Factors j := Subobject.factors_of_le j le_sup_left
    ((Subobject.imageSubobject_factors_iff j j).2
      ⟨J, 𝟙 _, inferInstance, 𝟙 _, by simp⟩)
  have hk : Q.Factors k := Subobject.factors_of_le k le_sup_right
    ((Subobject.imageSubobject_factors_iff k k).2
      ⟨A, 𝟙 _, inferInstance, 𝟙 _, by simp⟩)
  have hdesc : Q.Factors (biprod.desc j k) := by
    apply (Subobject.factors_iff Q _).2
    refine ⟨biprod.desc (Q.factorThru j hj) (Q.factorThru k hk), ?_⟩
    ext <;> simp [Q.factorThru_arrow]
  apply le_antisymm
  · exact imageSubobject_le (biprod.desc j k) (Q.factorThru _ hdesc)
      (Subobject.factorThru_arrow Q _ hdesc)
  · apply sup_le
    · simpa only [biprod.inl_desc] using imageSubobject_comp_le biprod.inl (biprod.desc j k)
    · simpa only [biprod.inr_desc] using imageSubobject_comp_le biprod.inr (biprod.desc j k)

section Butterfly

section ExactSequenceIso

-- `exactSequenceIsoData` composes `hS.homologyIso` with `cokernelIsoOfEq hlift`, where
-- `hS.H` is the cokernel the latter is about. That identification is a projection of
-- `LeftHomologyData.ofHasKernelOfHasCokernel`, which is semireducible, so the composite
-- is not type-correct at the `implicit` transparency level and the `simp only
-- [π_comp_cokernelIsoOfEq_hom_assoc]` below reports `simp made no progress`. Making that
-- one definition implicit-reducible is what the proof needs; the attribute is section
-- scoped so that it stays attached to the declaration that justifies it.
attribute [local implicit_reducible]
  CategoryTheory.ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel

/-- In a diagram of three exact sequences the homology of the middle short complex is a
quotient of two images, compatibly with the canonical projections. -/
private noncomputable def exactSequenceIsoData
    {C : Type*} [Category C] [Abelian C]
    {A B G D J H : C}
    (k : A ⟶ B) (u : B ⟶ G) (v : G ⟶ D)
    (j : J ⟶ B) (g : B ⟶ H)
    (hku : k ≫ u = 0) (huv : u ≫ v = 0) (hjg : j ≫ g = 0)
    (hExactKu : (ShortComplex.mk k u hku).Exact)
    (hExactUv : (ShortComplex.mk u v huv).Exact)
    (hExactJg : (ShortComplex.mk j g hjg).Exact) :
    let S := ShortComplex.mk (j ≫ u) v (by rw [Category.assoc, huv, comp_zero])
    let m := Subobject.ofLE (imageSubobject (k ≫ g)) (imageSubobject g)
      (imageSubobject_comp_le k g)
    { e : S.homology ≅ cokernel m //
      S.liftCycles u huv ≫ S.homologyπ ≫ e.hom =
        factorThruImageSubobject g ≫ cokernel.π m } := by
  classical
  let S : ShortComplex C :=
    ShortComplex.mk (j ≫ u) v (by rw [Category.assoc, huv, comp_zero])
  let b : B ⟶ kernel v := kernel.lift v u huv
  have hbi : b ≫ kernel.ι v = u := kernel.lift_ι v u huv
  have hbEpi : Epi b := (ShortComplex.exact_iff_epi_kernel_lift
    (ShortComplex.mk u v huv)).1 hExactUv
  have hkb : k ≫ b = 0 := by
    apply (cancel_mono (kernel.ι v)).1
    rw [Category.assoc, hbi, hku]
    simp
  have hExactKb : (ShortComplex.mk k b hkb).Exact := by
    have hbKer : kernelSubobject b = kernelSubobject u := by
      rw [← hbi, kernelSubobject_comp_mono b (kernel.ι v)]
    apply (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk k b hkb)).2
    rw [hbKer]
    exact (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk k u hku)).1 hExactKu
  let leftP : Subobject (kernel v) := imageSubobject (j ≫ b)
  have hleftLE : leftP ≤ ⊤ := le_top
  let leftM := Subobject.ofLE leftP (⊤ : Subobject (kernel v)) hleftLE
  letI : IsIso (⊤ : Subobject (kernel v)).arrow := by infer_instance
  let topIso := asIso (⊤ : Subobject (kernel v)).arrow
  let leftU : B ⟶ (⊤ : Subobject (kernel v)) := b ≫ topIso.inv
  have hleftU : leftU ≫ (⊤ : Subobject (kernel v)).arrow = b := by
    simp [leftU, topIso]
  let rightP : Subobject H := imageSubobject (k ≫ g)
  let rightQ : Subobject H := imageSubobject g
  let rightM := Subobject.ofLE rightP rightQ (imageSubobject_comp_le k g)
  let rightU : B ⟶ (rightQ : C) := factorThruImageSubobject g
  have hrightU : rightU ≫ rightQ.arrow = g := imageSubobject_arrow_comp g
  have hleftEpi : Epi (leftU ≫ cokernel.π leftM) := by
    let : Epi leftU := by
      dsimp [leftU]
      infer_instance
    infer_instance
  have hrightEpi : Epi (rightU ≫ cokernel.π rightM) := by infer_instance
  have hfactorIff : ∀ {T' : C} (z : T' ⟶ B),
      leftP.Factors (z ≫ leftU ≫ (⊤ : Subobject (kernel v)).arrow) ↔
        rightP.Factors (z ≫ rightU ≫ rightQ.arrow) := by
    intro T' z
    rw [hleftU, hrightU]
    have hleft := imageRelation_factors_iff j k b hkb hExactKb z
    have hright := imageRelation_factors_iff k j g hjg hExactJg z
    rw [image_biprod_desc j k, sup_comm] at hleft
    rw [image_biprod_desc k j] at hright
    exact hleft.symm.trans hright
  have hquot := Subobject.exists_iso_cokernel_of_factors_iff
    leftM (Subobject.ofLE_arrow hleftLE)
    rightM (Subobject.ofLE_arrow (imageSubobject_comp_le k g))
    leftU rightU hfactorIff
  let eQ := Classical.choose hquot
  have heQ := Classical.choose_spec hquot
  let hS : S.LeftHomologyData := ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
  have hleftMArrow : leftM ≫ (⊤ : Subobject (kernel v)).arrow = leftP.arrow :=
    Subobject.ofLE_arrow hleftLE
  have hcomp : factorThruImageSubobject (j ≫ b) ≫ leftM ≫
      (⊤ : Subobject (kernel v)).arrow = j ≫ b := by
    rw [hleftMArrow]
    exact imageSubobject_arrow_comp (j ≫ b)
  let hleftCoker : cokernel (j ≫ b) ≅ cokernel leftM := by
    let h₁ : (j ≫ b) ≫ (topIso.inv ≫ cokernel.π leftM) = 0 := by
      rw [← hcomp]
      simp [Category.assoc, topIso]
    let h₂ : leftM ≫ ((⊤ : Subobject (kernel v)).arrow ≫ cokernel.π (j ≫ b)) = 0 := by
      apply (cancel_epi (factorThruImageSubobject (j ≫ b))).1
      rw [← Category.assoc, ← Category.assoc,
        Category.assoc (factorThruImageSubobject (j ≫ b)) leftM _, hcomp]
      simp
    refine ⟨cokernel.desc _ _ h₁, cokernel.desc _ _ h₂, ?_, ?_⟩
    · apply (cancel_epi (cokernel.π (j ≫ b))).1
      simp [Category.assoc, topIso]
    · apply (cancel_epi (cokernel.π leftM)).1
      simp [Category.assoc, topIso]
  have hlift : kernel.lift S.g S.f S.zero = j ≫ b := by
    apply (cancel_mono (kernel.ι v)).1
    change kernel.lift v (j ≫ u) S.zero ≫ kernel.ι v =
      (j ≫ b) ≫ kernel.ι v
    rw [kernel.lift_ι, Category.assoc, hbi]
  refine ⟨hS.homologyIso ≪≫ cokernelIsoOfEq hlift ≪≫ hleftCoker ≪≫ eQ, ?_⟩
  dsimp only [Iso.trans_hom]
  rw [hS.homologyπ_comp_homologyIso_hom_assoc,
    hS.liftCycles_comp_cyclesIso_hom_assoc]
  change b ≫ cokernel.π (kernel.lift S.g S.f S.zero) ≫ _ = _
  simp only [π_comp_cokernelIsoOfEq_hom_assoc]
  dsimp only [hleftCoker]
  simp only [cokernel.π_desc_assoc]
  simpa only [eQ, leftU, rightU, rightM, rightP, rightQ, Category.assoc] using heQ

end ExactSequenceIso

/-- The homology of the middle short complex of three exact sequences, as a quotient of
two images. -/
private noncomputable def exactSequenceIso
    {C : Type*} [Category C] [Abelian C]
    {A B G D J H : C}
    (k : A ⟶ B) (u : B ⟶ G) (v : G ⟶ D)
    (j : J ⟶ B) (g : B ⟶ H)
    (hku : k ≫ u = 0) (huv : u ≫ v = 0) (hjg : j ≫ g = 0)
    (hExactKu : (ShortComplex.mk k u hku).Exact)
    (hExactUv : (ShortComplex.mk u v huv).Exact)
    (hExactJg : (ShortComplex.mk j g hjg).Exact) :
    (ShortComplex.mk (j ≫ u) v (by rw [Category.assoc, huv, comp_zero])).homology ≅
      cokernel (Subobject.ofLE (imageSubobject (k ≫ g)) (imageSubobject g)
        (imageSubobject_comp_le k g)) :=
  (exactSequenceIsoData k u v j g hku huv hjg hExactKu hExactUv hExactJg).val

/-- The `E`-term of a spectral object over the whole interval `⊥ ≤ q ≤ q + 1 ≤ ⊤` is the
quotient of the two images coming from the inclusions of `H`-terms. -/
private noncomputable def wholeIntervalE_cokernel
    {A : Type*} [Category A] [Abelian A]
    (S : CategoryTheory.Abelian.SpectralObject A EInt) (n q : ℤ) :
    let f₁ : (⊥ : EInt) ⟶ (q : EInt) := homOfLE (by simp)
    let f₂ : (q : EInt) ⟶ ((q + 1 : ℤ) : EInt) := homOfLE (by simp)
    let f₃ : ((q + 1 : ℤ) : EInt) ⟶ ⊤ := homOfLE (by simp)
    let f₁₂ : (⊥ : EInt) ⟶ ((q + 1 : ℤ) : EInt) := homOfLE (by simp)
    let f₁₂₃ : (⊥ : EInt) ⟶ ⊤ := homOfLE (by simp)
    let k := (S.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ (by apply Subsingleton.elim))
    let g := (S.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ (by apply Subsingleton.elim))
    S.E f₁ f₂ f₃ (n - 1) n (n + 1) (by omega) (by omega) ≅
      cokernel (Subobject.ofLE (imageSubobject (k ≫ g)) (imageSubobject g)
        (imageSubobject_comp_le k g)) := by
  let i₀ : EInt := ⊥
  let i₁ : EInt := q
  let i₂ : EInt := ((q + 1 : ℤ) : EInt)
  let i₃ : EInt := ⊤
  let f₁ : i₀ ⟶ i₁ := homOfLE (by dsimp [i₀, i₁]; simp)
  let f₂ : i₁ ⟶ i₂ := homOfLE (by
    dsimp [i₁, i₂]
    exact WithBotTop.coe_le_coe.mpr (by omega))
  let f₃ : i₂ ⟶ i₃ := homOfLE (by dsimp [i₂, i₃]; simp)
  let f₁₂ : i₀ ⟶ i₂ := homOfLE (by dsimp [i₀, i₂]; simp)
  let f₂₃ : i₁ ⟶ i₃ := homOfLE (by dsimp [i₁, i₃]; simp)
  let f₁₂₃ : i₀ ⟶ i₃ := homOfLE (by dsimp [i₀, i₃]; simp)
  let k := (S.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ (by apply Subsingleton.elim))
  let u := (S.H n).map (twoδ₁Toδ₀ f₁ f₂ f₁₂ (by apply Subsingleton.elim))
  let v := S.δ f₁ f₂ n (n + 1) (by omega)
  let j := S.δ f₁₂ f₃ (n - 1) n (by omega)
  let g := (S.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ (by apply Subsingleton.elim))
  have hku : k ≫ u = 0 := by dsimp [k, u]; simp
  have huv : u ≫ v = 0 := by dsimp [u, v]; simp
  have hjg : j ≫ g = 0 := by dsimp [j, g]; simp
  have hExactKu : (ShortComplex.mk k u hku).Exact :=
    (S.composableArrows₅_exact f₁ f₂ f₁₂ (by apply Subsingleton.elim)
      n (n + 1) (by omega)).exact 0 (by decide)
  have hExactUv : (ShortComplex.mk u v huv).Exact :=
    (S.composableArrows₅_exact f₁ f₂ f₁₂ (by apply Subsingleton.elim)
      n (n + 1) (by omega)).exact 1 (by decide)
  have hExactJg : (ShortComplex.mk j g hjg).Exact :=
    S.exact₁ f₁₂ f₃ f₁₂₃ (by apply Subsingleton.elim) (n - 1) n (by omega)
  have hju : j ≫ u = S.δ f₂ f₃ (n - 1) n (by omega) := by
    have h := S.δ_naturality f₁₂ f₃ f₂ f₃
      (twoδ₁Toδ₀ f₁ f₂ f₁₂ (by apply Subsingleton.elim)) (𝟙 _) (n - 1) n
      (by apply Subsingleton.elim) (by omega)
    dsimp [j, u] at h ⊢
    simpa using h.symm
  let e := exactSequenceIso k u v j g hku huv hjg
    hExactKu hExactUv hExactJg
  change (S.shortComplex f₁ f₂ f₃ (n - 1) n (n + 1) (by omega) (by omega)).homology ≅ _
  let eS : S.shortComplex f₁ f₂ f₃ (n - 1) n (n + 1) (by omega) (by omega) ≅
      ShortComplex.mk (j ≫ u) v (by rw [hju]; simp [v]) :=
    ShortComplex.isoMk
      (S₁ := S.shortComplex f₁ f₂ f₃ (n - 1) n (n + 1) (by omega) (by omega))
      (S₂ := ShortComplex.mk (j ≫ u) v (by rw [hju]; simp [v]))
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (comm₁₂ := by
        simpa [CategoryTheory.Abelian.SpectralObject.shortComplex] using hju)
      (comm₂₃ := by
        simp [CategoryTheory.Abelian.SpectralObject.shortComplex, v])
  exact (ShortComplex.homologyFunctor A).mapIso eS ≪≫ e

/-! ### The abutment filtration of a first-quadrant spectral object -/

/-- A filtered object of a functor category is a functor to filtered objects. -/
private noncomputable def filteredUncurry {D C I : Type*} [Category D] [Category C] [Abelian C]
    [Category I] (F : FilteredObject (D ⥤ C) I) : D ⥤ FilteredObject C I where
  obj K :=
    { X := F.X.obj K
      filtration.toMonoOver :=
        { obj i := MonoOver.mk ((F.filtration.ι.app i).app K)
          map f := MonoOver.homMk ((F.filtration.step f).app K)
            (congrArg (fun η => η.app K) (F.filtration.step_comp_ι_app f))
          map_id _ := Subsingleton.elim _ _
          map_comp _ _ := Subsingleton.elim _ _ } }
  map f := FilteredObject.homMk (F.X.map f)
    (fun i => (F.filtration.obj i).map f)
    (fun i => ((F.filtration.ι.app i).naturality f))
  map_id _ := FilteredObject.hom_ext (F.X.map_id _)
  map_comp _ _ := FilteredObject.hom_ext (F.X.map_comp _ _)

/-- The graded pieces of a filtered object of a functor category are computed objectwise. -/
private noncomputable def filteredUncurryGrIso {D C : Type*} [Category D] [Category C] [Abelian C]
    (F : FilteredObject (D ⥤ C) ℤᵒᵖ) (p : ℤ) :
    (FilteredObject.gr p).obj F ≅ filteredUncurry F ⋙ FilteredObject.gr p := by
  refine NatIso.ofComponents (fun K =>
    PreservesCokernel.iso ((evaluation D C).obj K)
      (F.filtration.step (FilteredObject.succHom p))) ?_
  intro K L φ
  let t := F.filtration.step (FilteredObject.succHom p)
  change (cokernel t).map φ ≫ (PreservesCokernel.iso ((evaluation D C).obj L) t).hom =
    (PreservesCokernel.iso ((evaluation D C).obj K) t).hom ≫
      cokernel.map (t.app K) (t.app L)
        ((F.filtration.obj (op (p + 1))).map φ) ((F.filtration.obj (op p)).map φ)
        (t.naturality φ).symm
  apply (cancel_epi ((cokernel.π t).app K)).1
  rw [← Category.assoc, ← (cokernel.π t).naturality φ, Category.assoc]
  have hK := PreservesCokernel.π_iso_hom ((evaluation D C).obj K) t
  have hL := PreservesCokernel.π_iso_hom ((evaluation D C).obj L) t
  dsimp only [evaluation_obj_map] at hK hL
  rw [hL, ← Category.assoc, hK]
  exact (cokernel.π_desc _ _ _).symm

/-- The inclusion of the `H`-term over `⊥ ≤ q` into the `H`-term over the whole interval. -/
private noncomputable def spectralObjectInclusion {C : Type*} [Category C] [Abelian C]
    (S : Abelian.SpectralObject C EInt) (n q : ℤ) :
    (S.H n).obj (mk₁ (homOfLE (show (⊥ : EInt) ≤ (q : EInt) from bot_le))) ⟶
      (S.H n).obj (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) :=
  (S.H n).map (homMk₁ (𝟙 _) (homOfLE (show (q : EInt) ≤ ⊤ from le_top)))

/-- The image of `spectralObjectInclusion`, a subobject of the whole-interval `H`-term. -/
private noncomputable def spectralObjectImage {C : Type*} [Category C] [Abelian C]
    (S : Abelian.SpectralObject C EInt) (n q : ℤ) :
    Subobject ((S.H n).obj (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le)))) :=
  imageSubobject (spectralObjectInclusion S n q)

/-- The images of the `H`-terms over `⊥ ≤ n - p + 1` decrease as `p` increases.

Stated with the conclusion spelled `Antitone` rather than its unfolding, so that the
proof term stored inside `spectralObjectFiltration` below is type-correct at the
`implicit` transparency level: `Antitone` is semireducible, so a proof whose inferred
type is the unfolded `∀ ⦃p p'⦄, p ≤ p' → …` makes every later `rw` against
`Filtration.ofAntitone` fail to build a motive. -/
private theorem spectralObjectImage_antitone {C : Type*} [Category C] [Abelian C]
    (S : Abelian.SpectralObject C EInt) (n : ℤ) :
    Antitone fun p : ℤ => spectralObjectImage S n (n - p + 1) := by
  intro p p' h
  let η (p : ℤ) := spectralObjectInclusion S n (n - p + 1)
  let k := (S.H n).map (homMk₁ (F := mk₁
    (homOfLE (show (⊥ : EInt) ≤ ((n - p' + 1 : ℤ) : EInt) by simp)))
    (G := mk₁ (homOfLE (show (⊥ : EInt) ≤ ((n - p + 1 : ℤ) : EInt) by simp)))
    (𝟙 _) (homOfLE (show ((n - p' + 1 : ℤ) : EInt) ≤ ((n - p + 1 : ℤ) : EInt) by
      exact WithBotTop.coe_le_coe.mpr (by omega))))
  have hk : k ≫ η p = η p' := by
    dsimp [k, η, spectralObjectInclusion]
    rw [← Functor.map_comp]
    congr 1
  show imageSubobject (η p') ≤ imageSubobject (η p)
  rw [← hk]
  exact imageSubobject_comp_le _ _

/-- The decreasing filtration of the whole-interval `H`-term of a spectral object by the
images of the `H`-terms over `⊥ ≤ n - p + 1`. -/
private noncomputable def spectralObjectFiltration {C : Type*} [Category C] [Abelian C]
    (S : Abelian.SpectralObject C EInt) (n : ℤ) : FilteredObject C ℤᵒᵖ :=
  ⟨(S.H n).obj (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ by simp))),
    Filtration.ofAntitone (fun p => spectralObjectImage S n (n - p + 1))
      (spectralObjectImage_antitone S n)⟩

section FiltrationSubobject

-- The three declarations below compare `(spectralObjectFiltration S n).X` with the
-- `H`-term it is built from. That object indexes a `Subobject`, so a semireducible
-- wrapper there does not merely slow the comparisons down: they fail outright at the
-- `implicit` transparency level (`simp made no progress` on `hcomm`, then `ht` and
-- `⊥ = ⊥` at the wrong `Subobject` type). Removing the attribute reproduces exactly
-- those three errors and nothing else, which is why it is scoped to these three
-- declarations rather than set for the file.
attribute [local implicit_reducible] spectralObjectFiltration

/-- The `p`-th step of the abutment filtration is the image of the `H`-term over
`⊥ ≤ n - p + 1`. -/
private lemma spectralObjectFiltration_subobject {C : Type*} [Category C] [Abelian C]
    (S : Abelian.SpectralObject C EInt) (n p : ℤ) :
    (spectralObjectFiltration S n).filtration.subobject (op p) =
      spectralObjectImage S n (n - p + 1) := by
  dsimp only [spectralObjectFiltration]
  rw [Filtration.subobject_ofAntitone]

/-- The whole-interval `E`-term of a spectral object is the graded piece of the abutment
filtration. -/
private noncomputable def spectralObjectFiltrationGrIso {C : Type*} [Category C] [Abelian C]
    (S : Abelian.SpectralObject C EInt) (n q : ℤ) :
    S.E (homOfLE (show (⊥ : EInt) ≤ (q : EInt) by simp))
      (homOfLE (show (q : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))
      (homOfLE (show ((q + 1 : ℤ) : EInt) ≤ ⊤ by simp))
      (n - 1) n (n + 1) (by omega) (by omega) ≅
    (FilteredObject.gr (n - q)).obj (spectralObjectFiltration S n) := by
  let i₀ : EInt := ⊥
  let i₁ : EInt := q
  let i₂ : EInt := ((q + 1 : ℤ) : EInt)
  let i₃ : EInt := ⊤
  let f₁ : i₀ ⟶ i₁ := homOfLE (by dsimp [i₀, i₁]; simp)
  let f₂ : i₁ ⟶ i₂ := homOfLE (by
    dsimp [i₁, i₂]
    exact WithBotTop.coe_le_coe.mpr (by omega))
  let f₃ : i₂ ⟶ i₃ := homOfLE (by dsimp [i₂, i₃]; simp)
  let f₁₂ : i₀ ⟶ i₂ := homOfLE (by dsimp [i₀, i₂]; simp)
  let f₁₂₃ : i₀ ⟶ i₃ := homOfLE (by dsimp [i₀, i₃]; simp)
  let k := (S.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ (by apply Subsingleton.elim))
  let g₀ := (S.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ (by apply Subsingleton.elim))
  let Fil := spectralObjectFiltration S n
  have hlow : imageSubobject (k ≫ g₀) = Fil.filtration.subobject (op (n - q + 1)) := by
    rw [spectralObjectFiltration_subobject]
    dsimp [k, g₀]
    rw [← Functor.map_comp]
    rw [show n - (n - q + 1) + 1 = q by omega]
    unfold spectralObjectImage spectralObjectInclusion
    congr 2
  have hup : imageSubobject g₀ = Fil.filtration.subobject (op (n - q)) := by
    rw [spectralObjectFiltration_subobject]
    rw [show n - (n - q) + 1 = q + 1 by omega]
    unfold spectralObjectImage spectralObjectInclusion
    congr 2
  let low := imageSubobject (k ≫ g₀)
  let high := imageSubobject g₀
  let low' := Fil.filtration.subobject (op (n - q + 1))
  let high' := Fil.filtration.subobject (op (n - q))
  let eLow : Subobject.underlying.obj low ≅ Subobject.underlying.obj low' :=
    Subobject.isoOfEq low low' hlow
  let eHigh : Subobject.underlying.obj high ≅ Subobject.underlying.obj high' :=
    Subobject.isoOfEq high high' hup
  have hcomm : Subobject.ofLE low high (imageSubobject_comp_le k g₀) ≫
        eHigh.hom = eLow.hom ≫
          (Subobject.ofLE low' high'
            (Fil.filtration.subobject_le_of_hom (FilteredObject.succHom (n - q)))) := by
    apply (cancel_mono high'.arrow).1
    change (Subobject.ofLE low high (imageSubobject_comp_le k g₀) ≫
          Subobject.ofLE high high' hup.le) ≫ high'.arrow =
        (Subobject.ofLE low low' hlow.le ≫
          Subobject.ofLE low' high'
            (Fil.filtration.subobject_le_of_hom (FilteredObject.succHom (n - q)))) ≫
          high'.arrow
    simp only [Category.assoc, Subobject.ofLE_arrow]
  let eC := cokernel.mapIso
    (Subobject.ofLE low high (imageSubobject_comp_le k g₀))
    (Subobject.ofLE low' high'
      (Fil.filtration.subobject_le_of_hom (FilteredObject.succHom (n - q))))
    eLow eHigh hcomm
  change S.E f₁ f₂ f₃ (n - 1) n (n + 1) (by omega) (by omega) ≅ _
  let eP := (Subobject.underlyingIso (Fil.filtration.ι.app (op (n - q)))).symm
  let eQ := (Subobject.underlyingIso (Fil.filtration.ι.app (op (n - q + 1)))).symm
  have hStep : Fil.filtration.step (FilteredObject.succHom (n - q)) ≫ eP.hom =
      eQ.hom ≫ Subobject.ofLE low' high'
        (Fil.filtration.subobject_le_of_hom (FilteredObject.succHom (n - q))) := by
    apply (cancel_mono high'.arrow).1
    simp [low', high', eP, eQ, Subobject.underlyingIso_arrow]
  exact wholeIntervalE_cokernel S n q ≪≫ eC ≪≫
    (cokernel.mapIso _ _ eQ eP hStep).symm

/-- In total degree `n`, the zeroth step of the abutment filtration is everything, as soon as
the `H`-term over `n + 1 ≤ ⊤` vanishes. Only this vanishing — the `isZero₂` half of
`IsFirstQuadrant` — is used, and it is uniform over the bounded below derived category, which
is why the hypothesis is taken rather than the instance. -/
private lemma spectralObjectFiltration_isTop {C : Type*} [Category C] [Abelian C]
    (S : Abelian.SpectralObject C EInt) (n : ℤ)
    (hzero : IsZero ((S.H n).obj
      (mk₁ (homOfLE (show ((n + 1 : ℤ) : EInt) ≤ ⊤ from le_top))))) :
    (spectralObjectFiltration S n).filtration.subobject (op 0) = ⊤ := by
  let f : (⊥ : EInt) ⟶ ((n + 1 : ℤ) : EInt) := homOfLE bot_le
  let g : ((n + 1 : ℤ) : EInt) ⟶ ⊤ := homOfLE le_top
  let fg : (⊥ : EInt) ⟶ ⊤ := homOfLE bot_le
  let η := (S.H n).map (twoδ₂Toδ₁ f g fg (by subsingleton))
  have : Epi η := (S.exact₂ f g fg (by subsingleton) n).epi_f (hzero.eq_of_tgt _ _)
  have heq : (spectralObjectFiltration S n).filtration.subobject (op 0) =
      imageSubobject η := by
    rw [spectralObjectFiltration_subobject, sub_zero]
    unfold spectralObjectImage spectralObjectInclusion
    congr 2
  rw [heq]
  have : Epi (imageSubobject η).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp η)
  have ht := (Subobject.epi_iff_mk_eq_top (imageSubobject η).arrow).mp (inferInstance : Epi _)
  simpa using ht

/-- In total degree `n`, the `p`-th step of the abutment filtration is zero as soon as the
`H`-term over `⊥ ≤ n - p + 1` vanishes. For a first-quadrant spectral object that happens at
`p = n + 1`; in the bounded below derived category the step depends on the object. -/
private lemma spectralObjectFiltration_isBot {C : Type*} [Category C] [Abelian C]
    (S : Abelian.SpectralObject C EInt) (n p : ℤ)
    (hzero : IsZero ((S.H n).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ((n - p + 1 : ℤ) : EInt) from bot_le))))) :
    (spectralObjectFiltration S n).filtration.subobject (op p) = ⊥ := by
  rw [spectralObjectFiltration_subobject]
  unfold spectralObjectImage
  have hz : spectralObjectInclusion S n (n - p + 1) = 0 := hzero.eq_of_src _ _
  exact (congrArg (fun h : _ ⟶ _ => imageSubobject h) hz).trans (by simp)

end FiltrationSubobject

/-- A filtration step that is everything stays everything after evaluation. -/
private lemma filteredUncurry_isTop {D C : Type*} [Category D] [Category C] [Abelian C]
    (F : FilteredObject (D ⥤ C) ℤᵒᵖ) (K : D) (p : ℤ)
    (h : F.filtration.subobject (op p) = ⊤) :
    ((filteredUncurry F).obj K).filtration.subobject (op p) = ⊤ := by
  have := (F.filtration.subobject_eq_top_iff _).mp h
  apply (Filtration.subobject_eq_top_iff _ _).mpr
  show IsIso ((F.filtration.ι.app (op p)).app K)
  infer_instance

/-- A filtration step that is zero stays zero after evaluation. -/
private lemma filteredUncurry_isBot {D C : Type*} [Category D] [Category C] [Abelian C]
    (F : FilteredObject (D ⥤ C) ℤᵒᵖ) (K : D) (p : ℤ)
    (h : F.filtration.subobject (op p) = ⊥) :
    ((filteredUncurry F).obj K).filtration.subobject (op p) = ⊥ := by
  obtain ⟨hzero⟩ := (F.filtration.subobject_eq_bot_iff _).mp h
  exact (Filtration.subobject_eq_bot_iff _ _).mpr
    ⟨(((evaluation D C).obj K).map_isZero hzero.isZero).isInitial⟩

/-- Beyond the edge of the first quadrant, the page of the spectral sequence of a
first-quadrant spectral object is the graded piece of the abutment filtration. -/
private noncomputable def spectralObjectFirstQuadrantPageGrIso
    {D C : Type*} [Category D] [Category C] [Abelian C]
    (S : Abelian.SpectralObject (D ⥤ C) EInt) [S.IsFirstQuadrant]
    (p q : ℕ) (r : ℤ) (hr : 2 ≤ r) (hp : (p : ℤ) + 1 ≤ r)
    (hq : (q : ℤ) + 2 ≤ r) :
    ((S.spectralSequence Abelian.SpectralObject.coreE₂CohomologicalNat).page r hr).X (p, q) ≅
      filteredUncurry (spectralObjectFiltration S ((p + q : ℕ) : ℤ)) ⋙
        FilteredObject.gr (p : ℤ) := by
  let n : ℤ := p + q
  let i₀ : EInt := ((q : ℤ) - r + 2 : ℤ)
  let i₁ : EInt := (q : ℤ)
  let i₂ : EInt := ((q : ℤ) + 1 : ℤ)
  let i₃ : EInt := ((q : ℤ) + r - 1 : ℤ)
  have hi₀₁ : i₀ ≤ i₁ := WithBotTop.coe_le_coe.mpr (by omega)
  have hi₁₂ : i₁ ≤ i₂ := WithBotTop.coe_le_coe.mpr (by omega)
  have hi₂₃ : i₂ ≤ i₃ := WithBotTop.coe_le_coe.mpr (by omega)
  let e := S.spectralSequencePageXIso Abelian.SpectralObject.coreE₂CohomologicalNat
    r hr (p, q) i₀ i₁ i₂ i₃ rfl rfl rfl rfl (n - 1) n (n + 1) rfl
    (by omega) (by omega)
  have hz₀ : IsZero ((S.H (n + 1)).obj (mk₁ (homOfLE (show (⊥ : EInt) ≤ i₀ from bot_le)))) :=
    S.isZero₁_of_isFirstQuadrant ⊥ i₀ bot_le
      (WithBotTop.coe_le_coe.mpr (by omega)) _
  have hz₃ : IsZero ((S.H (n - 1)).obj (mk₁ (homOfLE (show i₃ ≤ ⊤ from le_top)))) :=
    S.isZero₂_of_isFirstQuadrant i₃ ⊤ le_top _
      (WithBotTop.coe_lt_coe.mpr (by dsimp [i₃, n]; omega))
  let e' := spectralObjectEIsoPageInfinity S (n - 1) n (n + 1) (by omega) (by omega)
    i₀ i₁ i₂ i₃ bot_le hi₀₁ hi₁₂ hi₂₃ le_top hz₀ hz₃
  have hn : n - q = p := by dsimp [n]; omega
  simpa only [Nat.cast_add, hn] using e ≪≫ e' ≪≫ (spectralObjectFiltrationGrIso S n q) ≪≫
    filteredUncurryGrIso (spectralObjectFiltration S n) (n - q)

/-- A first-quadrant spectral object of a functor category gives a functorial finite
filtered abutment for the associated spectral sequence. -/
private noncomputable def spectralObjectFirstQuadrantAbutment
    {D C : Type*} [Category D] [Category C] [Abelian C]
    (S : Abelian.SpectralObject (D ⥤ C) EInt) [S.IsFirstQuadrant] :
    Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo
      (spectralSequenceAsFunctor
        (S.spectralSequence Abelian.SpectralObject.coreE₂CohomologicalNat))
      (fun n : ℕ => (S.H n).obj (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le)))) := by
  let E := spectralSequenceAsFunctor
    (S.spectralSequence Abelian.SpectralObject.coreE₂CohomologicalNat)
  let r (p q : ℕ) : ℤ := max 2 (max ((p : ℤ) + 1) ((q : ℤ) + 2))
  have hm (K : D) (p q : ℕ) : (E.obj K).HasEdgeMonoAtFrom (p, q) (r p q) :=
    CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ _ _
      (by dsimp [r]; omega) (by dsimp [r]; omega)
  have he (K : D) (p q : ℕ) : (E.obj K).HasEdgeEpiAtFrom (p, q) (r p q) :=
    CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ _ _
      (by dsimp [r]; omega) (by dsimp [r]; omega)
  let e (p q : ℕ) := spectralObjectFirstQuadrantPageGrIso S p q (r p q)
    (by dsimp [r]; omega) (by dsimp [r]; omega) (by dsimp [r]; omega)
  have htop (n : ℕ) : (spectralObjectFiltration S (n : ℤ)).filtration.subobject (op 0) = ⊤ :=
    spectralObjectFiltration_isTop S _
      (S.isZero₂_of_isFirstQuadrant _ ⊤ le_top (n : ℤ) (by simp))
  have hbot (n : ℕ) :
      (spectralObjectFiltration S (n : ℤ)).filtration.subobject (op ((n : ℤ) + 1)) = ⊥ :=
    spectralObjectFiltration_isBot S _ _
      (S.isZero₁_of_isFirstQuadrant ⊥ _ bot_le
        (WithBotTop.coe_le_coe.mpr (by omega)) (n : ℤ))
  refine
    { filtration := fun n => filteredUncurry (spectralObjectFiltration S n)
      abutmentIso := fun n => Iso.refl _
      isTop := fun K n => filteredUncurry_isTop _ K 0 (htop n)
      isBot := fun K n => filteredUncurry_isBot _ K ((n : ℤ) + 1) (hbot n)
      isFinite := ?_
      gradedIso := fun K p q => by
        have := hm K p q
        have := he K p q
        exact (E.obj K).pageInfinityIso (p, q) (r p q) ≪≫
          (e p q).app K
      gradedIso_naturality := ?_ }
  · intro K n
    apply (Filtration.isFinite_iff_subobject _).mpr
    exact ⟨⟨op 0, filteredUncurry_isTop _ K 0 (htop n)⟩,
      ⟨op ((n : ℤ) + 1), filteredUncurry_isBot _ K ((n : ℤ) + 1) (hbot n)⟩⟩
  · intro K L φ p q
    have := hm K p q
    have := hm L p q
    have := he K p q
    have := he L p q
    dsimp only [Iso.trans_hom]
    rw [SpectralSequence.Hom.mapPageInfinity_eq (E.map φ) (p, q) (r p q)]
    simp only [Category.assoc]
    -- Term-level from here, as in `spectralSequenceEvaluateMap` above: `simp only
    -- [Iso.inv_hom_id_assoc]` silently fails to fire, because the source of
    -- `(e p q).hom.app L` and the target of `((E.obj L).pageInfinityIso …)` agree only at
    -- semireducible transparency, so there is no type-correct motive to rewrite under.
    -- Stating the cancellation as a `have` forces that identification once, at default
    -- transparency, where it is immediate.
    have hcancel : ((E.obj L).pageInfinityIso (p, q) (r p q)).inv ≫
        ((E.obj L).pageInfinityIso (p, q) (r p q)).hom ≫ (e p q).hom.app L =
          (e p q).hom.app L := Iso.inv_hom_id_assoc _ _
    exact (congrArg (fun t => ((E.obj K).pageInfinityIso (p, q) (r p q)).hom ≫ t)
      ((congrArg (fun t => ((E.map φ).hom (r p q) (by dsimp [r]; omega)).f (p, q) ≫ t)
        hcancel).trans ((e p q).hom.naturality φ))).trans (Category.assoc _ _ _).symm

end Butterfly
/-- Under the acyclicity criterion of [Stacks, Tag 015M], `RG ∘ RF` is `R(G ∘ F)` on the
bounded below derived categories. This is
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic`, read in the direction
the abutment comparisons below use. -/
private noncomputable def compDerivedIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅
      (F ⋙ G).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic F G hFG).symm

/-- The abutment of the functorial Grothendieck spectral sequence of a single object is
the right derived functor of the composite. -/
private noncomputable def natAbutmentIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) (n : ℕ) :
    ((spectralObjectInFunctorCategory (DerivedCategory.Plus.singleFunctor A 0 ⋙
          derivedTruncationSpectralObjectFunctor F G)).H n).obj
        (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      (F ⋙ G).rightDerived n := by
  let M := DerivedCategory.Plus.singleFunctor A 0
  let H := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  change M ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙ H ≅ _
  exact Functor.isoWhiskerLeft M
      (Functor.isoWhiskerRight (compDerivedIso F G hFG) H) ≪≫
    (by simpa only [add_zero] using shiftedRightDerivedIso (F ⋙ G) (n : ℤ) 0) ≪≫
    derivedPlusToStandard (F ⋙ G) n

/-- The functorial filtered abutment of the Grothendieck spectral sequence of a single
object. -/
@[no_expose] noncomputable def natAbutment
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) :
    Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo
      (derivedTruncationSpectralSequenceNatFunctor F G)
      (fun n : ℕ => (F ⋙ G).rightDerived n) := by
  let S := DerivedCategory.Plus.singleFunctor A 0 ⋙ derivedTruncationSpectralObjectFunctor F G
  haveI := spectralObjectInFunctorCategory_isFirstQuadrant S
    (fun X => derivedTruncationSpectralObject_isFirstQuadrant F G _)
  let b := spectralObjectFirstQuadrantAbutment (spectralObjectInFunctorCategory S)
  exact
    { filtration := b.filtration
      abutmentIso := fun n => b.abutmentIso n ≪≫ natAbutmentIso F G hFG n
      isFinite := b.isFinite
      isTop := b.isTop
      isBot := b.isBot
      gradedIso := b.gradedIso
      gradedIso_naturality := b.gradedIso_naturality }

end FirstQuadrant

end Construction

end Stacks.Cohomology.Grothendieck

end
