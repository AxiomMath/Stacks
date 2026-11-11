module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletionAlgebra
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletionChart
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Completion.VectorBundle
public import StacksFrontier.AlgebraicGeometry.RelativeProj.DataIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.GradedBaseChange

/-!
# The graded ring of the exceptional divisor over an affine open

Let `i : Z ⟶ X` be a closed immersion and `U = Spec A` an affine open of `X`, with `I ⊆ A` the
ideal of `Z ∩ U`. The part of the exceptional divisor `E` of the blowup at infinity over `U` is
`Proj B`, with `B = Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥(V) t]` the base change of the Rees algebra of the
centre over the chart at infinity `V = Spec A[s]` (`Stacks.Chow.centreChartRing`). This file
identifies `B` with the graded ring `Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` of the projective completion of the
conormal sheaf when `i` is a regular immersion:

  `Sym_{A/I}(I/I² ⊕ A/I) ≅ Gr_{(I, s)}(A[s]) ≅ A/I ⊗_{A[s]} A[s][(I, s) t]`.

## Main definitions

* `Stacks.Chow.centreChartToGraded`: the ring map `B ⟶ Gr_I(A)[T]`, which is
  `B ⟶ Gr_{(I, s)}(A[s]) ≅ Gr_I(A)[T]`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AssociatedGraded Stacks.AlgebraicGeometry.ReflexiveModules
open scoped Stacks.ProjectiveCompletion

universe u

/-! ### `Proj.map` and the structure morphisms to the degree-zero parts -/

/-- `Proj.map` is compatible with structure maps into the degree-zero parts. -/
theorem _root_.AlgebraicGeometry.Proj.map_toSpecZero_specMap {A B σ τ : Type u} [CommRing A]
    [CommRing B] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {R : CommRingCat.{u}} (a : R ⟶ CommRingCat.of (𝒜 0)) (b : R ⟶ CommRingCat.of (ℬ 0))
    (hab : a ≫ CommRingCat.ofHom f.gradedZeroRingHom = b) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 ≫ Spec.map a = Proj.toSpecZero ℬ ≫ Spec.map b := by
  rw [AlgebraicGeometry.Proj.map_toSpecZero_assoc, ← Spec.map_comp, hab]

/-- A ring map into the degree-zero part followed by the degree-zero part of `f` is determined
elementwise. -/
theorem _root_.GradedRingHom.comp_gradedZeroRingHom_eq {A B σ τ : Type u} [CommRing A]
    [CommRing B] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    {R : CommRingCat.{u}} (a : R ⟶ CommRingCat.of (𝒜 0)) (b : R ⟶ CommRingCat.of (ℬ 0))
    (h : ∀ r, f ((a.hom r : 𝒜 0) : A) = ((b.hom r : ℬ 0) : B)) :
    a ≫ CommRingCat.ofHom f.gradedZeroRingHom = b :=
  CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext (h r))


namespace Stacks.Chow

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (U : X.affineOpens)

/-! ### The ring map `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` -/

section RingHom

/-- The identification `Γ(X, U)[s] ≅ Γ(𝐏¹_X, V)` of `Stacks.Chow.infinityChartSectionsEquiv`, as
an isomorphism of commutative rings. -/
abbrev infinityChartSectionsIso :
    CommRingCat.of (Polynomial Γ(X, U.1)) ≅
      Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1) :=
  (Scheme.ΓSpecIso _).symm ≪≫ ((infinityChartOver U).appIso ⊤).symm

/-- `infinityChartSectionsIso` is `infinityChartSectionsEquiv`. -/
theorem infinityChartSectionsIso_hom_apply (p : Polynomial Γ(X, U.1)) :
    (infinityChartSectionsIso U).hom.hom p = infinityChartSectionsEquiv U p := rfl

/-- `Spec` of `Γ(𝐏¹_X, V) ≅ Γ(X, U)[s]`, followed by the chart at infinity, is the affine
identification of `V`. -/
theorem specMap_infinityChartSectionsIso_infinityChartOver :
    Spec.map (infinityChartSectionsIso U).hom ≫ infinityChartOver U =
      (infinityChartAffineOpen U).2.fromSpec := by
  have h := SpecMap_appIso_ΓSpecIso_fromSpec (infinityChartOver U)
  refine (congrArg (Spec.map (infinityChartSectionsIso U).hom ≫ ·) h.symm).trans ?_
  change Spec.map (infinityChartSectionsIso U).hom ≫ (Spec.map (infinityChartSectionsIso U).inv ≫
    (infinityChartAffineOpen U).2.fromSpec) = _
  rw [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- **`Γ(X, U)[s] ⟶ Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` is `s ↦ 0` followed by `i`.** -/
theorem centreChartRingHom_comp_infinityChartSectionsEquiv :
    (infinityChartSectionsIso U).hom ≫ centreChartRingHom i U =
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X, U.1))) ≫
        i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl := by
  apply Spec.map_injective
  rw [← cancel_mono (infinityChartOver U), Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc, specMap_infinityChartSectionsIso_infinityChartOver,
    specMap_centreChartRingHom_fromSpec, specMap_evalZero_infinityChartOver]
  have h2 := IsAffineOpen.SpecMap_appLE_fromSpec i U.2 (isAffineOpen_centrePreimage i U) le_rfl
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ lineInfinitySection X) h2).symm.trans (Category.assoc _ _ _))

/-- `Γ(X, U)[s] ⟶ Γ(Z, Z ∩ U)` is `p ↦ i(p(0))`. -/
theorem centreChartRingHom_infinityChartSectionsEquiv (p : Polynomial Γ(X, U.1)) :
    (centreChartRingHom i U).hom (infinityChartSectionsEquiv U p) =
      (i.app U.1).hom (p.eval 0) := by
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ p)
    (centreChartRingHom_comp_infinityChartSectionsEquiv i U)
  simp only [Scheme.Hom.appLE_eq_app, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, Polynomial.coe_evalRingHom] at h
  exact h

/-- `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` is surjective. -/
theorem centreChartRingHom_surjective : Function.Surjective (centreChartRingHom i U).hom := by
  intro s
  obtain ⟨r, rfl⟩ := Scheme.Hom.app_surjective i U.1 U.2 s
  exact ⟨infinityChartSectionsEquiv U (Polynomial.C r),
    (centreChartRingHom_infinityChartSectionsEquiv i U _).trans (by simp)⟩

/-- The ideal `J = (I, s)` of the centre on the chart at infinity, with `I` the kernel of
`Γ(X, U) ⟶ Γ(Z, Z ∩ U)`. -/
theorem ideal_infinityCentreIdeal_eq_map :
    (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) =
      (infinityChartIdeal (Stacks.Conormal.chartIdeal i U)).map
        (infinityChartSectionsEquiv U) := by
  rw [ideal_infinityCentreIdeal_infinityChartAffineOpen, Scheme.Hom.ker_apply]

/-- The kernel of `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` lies in the ideal of the centre. -/
theorem ker_centreChartRingHom_le :
    RingHom.ker (centreChartRingHom i U).hom ≤
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) := by
  intro r hr
  obtain ⟨p, rfl⟩ := (infinityChartSectionsEquiv U).surjective r
  rw [RingHom.mem_ker, centreChartRingHom_infinityChartSectionsEquiv] at hr
  rw [ideal_infinityCentreIdeal_eq_map]
  refine Ideal.mem_map_of_mem _ ?_
  have hp : p ∈ infinityChartIdeal (Stacks.Conormal.chartIdeal i U) ^ 1 := by
    rw [mem_pow_infinityChartIdeal_iff]
    intro j
    rcases j with _ | j
    · rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa using hr
    · simp
  simpa using hp

end RingHom


/-! ### The ring map `B ⟶ Gr_I(A)[T]` -/

section ToGraded

/-- The ideal of the centre on `Γ(𝐏¹_X, V)` goes into `J = (I, s)`. -/
theorem map_infinityCentreIdeal_le :
    ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U)).map
        (infinityChartSectionsEquiv U).symm.toRingHom ≤
      infinityChartIdeal (Stacks.Conormal.chartIdeal i U) := by
  rw [ideal_infinityCentreIdeal_eq_map, Ideal.map_le_iff_le_comap]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv _ y).1 hy
  change (infinityChartSectionsEquiv U).symm (infinityChartSectionsEquiv U x) ∈
    infinityChartIdeal (Stacks.Conormal.chartIdeal i U)
  rwa [RingEquiv.symm_apply_apply]

/-- `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` is surjective. -/
theorem algebraMap_centreChart_surjective :
    Function.Surjective (algebraMap Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)
      Γ(Z, i ⁻¹ᵁ U.1)) :=
  centreChartRingHom_surjective i U

/-- The kernel of `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)` lies in the ideal of the centre. -/
theorem ker_algebraMap_centreChart_le :
    RingHom.ker (algebraMap Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)
        Γ(Z, i ⁻¹ᵁ U.1)) ≤
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) :=
  ker_centreChartRingHom_le i U

/-- The transport `Gr_𝒥(Γ(V)) ≅ Gr_J(A[s]) ≅ Gr_I(A)[T]`. -/
def centreGradedTransport :
    gradedRing ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U)) →+*
      Polynomial (gradedRing (Stacks.Conormal.chartIdeal i U)) :=
  (infinityChartGradedEquiv (Stacks.Conormal.chartIdeal i U)).symm.toRingHom.comp
    (gradedRingMapOfRingHom (infinityChartSectionsEquiv U).symm.toRingHom
      (map_infinityCentreIdeal_le i U))

/-- `C x ∈ J` for `x ∈ I`, transported to `Γ(V)`. -/
theorem infinityChartSectionsEquiv_C_mem {x : Γ(X, U.1)} (hx : x ∈ Stacks.Conormal.chartIdeal i U) :
    infinityChartSectionsEquiv U (Polynomial.C x) ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) := by
  rw [ideal_infinityCentreIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (map_C_le_infinityChartIdeal _ (Ideal.mem_map_of_mem _ hx))

/-- `s ∈ J`, transported to `Γ(V)`. -/
theorem infinityChartSectionsEquiv_X_mem :
    infinityChartSectionsEquiv U Polynomial.X ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) := by
  rw [ideal_infinityCentreIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (X_mem_infinityChartIdeal _)

/-- `centreGradedTransport` on a class `[e p]` in degree `n` is the class `[p]` read in
`Gr_{(I, s)}(A[s])`, transported to `Gr_I(A)[T]`. -/
theorem centreGradedTransport_classOfPow (n : ℕ) (p : Polynomial Γ(X, U.1))
    (hp : infinityChartSectionsEquiv U p ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ n)
    (hp' : p ∈ infinityChartIdeal (Stacks.Conormal.chartIdeal i U) ^ n) :
    centreGradedTransport i U (classOfPow _ n ⟨infinityChartSectionsEquiv U p, hp⟩) =
      (infinityChartGradedEquiv (Stacks.Conormal.chartIdeal i U)).symm
        (classOfPow _ n ⟨p, hp'⟩) := by
  rw [centreGradedTransport, RingHom.comp_apply, gradedRingMapOfRingHom_classOfPow]
  exact congrArg _ (classOfPow_congr _ rfl (by simp))

/-- `centreGradedTransport` on the class of a constant `x ∈ I ^ n` in degree `n`. -/
theorem centreGradedTransport_classOfPow_C (n : ℕ) {x : Γ(X, U.1)}
    (hx : x ∈ Stacks.Conormal.chartIdeal i U ^ n)
    (hx' : infinityChartSectionsEquiv U (Polynomial.C x) ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ n) :
    centreGradedTransport i U
        (classOfPow _ n ⟨infinityChartSectionsEquiv U (Polynomial.C x), hx'⟩) =
      Polynomial.C (classOfPow _ n ⟨x, hx⟩) := by
  rw [centreGradedTransport_classOfPow i U n _ hx' (C_mem_pow_infinityChartIdeal hx),
    RingEquiv.symm_apply_eq]
  have h2 := infinityChartGradedMap_monomial_classOfPow (Stacks.Conormal.chartIdeal i U) 0 n ⟨x, hx⟩
  rw [Polynomial.monomial_zero_left] at h2
  rw [infinityChartGradedEquiv_apply, h2]
  exact classOfPow_congr _ rfl (by simp)

/-- `Gr_𝒥(Γ(V)) ≅ Gr_I(A)[T]` on the class of a constant `x ∈ I`. -/
theorem centreGradedTransport_C {x : Γ(X, U.1)} (hx : x ∈ Stacks.Conormal.chartIdeal i U) :
    centreGradedTransport i U (classOfPow _ 1 ⟨infinityChartSectionsEquiv U (Polynomial.C x),
        by simpa using infinityChartSectionsEquiv_C_mem i U hx⟩) =
      Polynomial.C (classOfPow _ 1 ⟨x, by simpa using hx⟩) :=
  centreGradedTransport_classOfPow_C i U 1 _ _

/-- `Gr_𝒥(Γ(V)) ≅ Gr_I(A)[T]` on the class of `s`. -/
theorem centreGradedTransport_X :
    centreGradedTransport i U (classOfPow _ 1 ⟨infinityChartSectionsEquiv U Polynomial.X,
        by simpa using infinityChartSectionsEquiv_X_mem i U⟩) = Polynomial.X := by
  rw [centreGradedTransport_classOfPow i U 1 _ _ (X_mem_infinityChartIdeal_pow_one _),
    RingEquiv.symm_apply_eq, infinityChartGradedEquiv_apply, infinityChartGradedMap,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

/-- `Gr_𝒥(Γ(V)) ≅ Gr_I(A)[T]` on the degree-zero class of a constant. -/
theorem centreGradedTransport_gradeZero (r : Γ(X, U.1)) :
    centreGradedTransport i U (Stacks.Blowup.gradeZeroRingHom _
        (infinityChartSectionsEquiv U (Polynomial.C r))) =
      Polynomial.C (Stacks.Blowup.gradeZeroRingHom _ r) :=
  centreGradedTransport_classOfPow_C i U 0 (by simp) (by simp)

/-- **The ring map `B = Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥 t] ⟶ Gr_I(A)[T]`**: the quotient map of the
Rees algebra onto `Gr_𝒥(Γ(V))`, followed by `Gr_{(I, s)}(A[s]) ≅ Gr_I(A)[T]`. -/
def centreChartToGraded :
    centreChartRing i U →+* Polynomial (gradedRing (Stacks.Conormal.chartIdeal i U)) :=
  Stacks.Blowup.baseChangeReesToGraded _ (centreGradedTransport i U)
    (algebraMap_centreChart_surjective i U) (ker_algebraMap_centreChart_le i U)

/-- `B ⟶ Gr_I(A)[T]` on `1 ⊗ x t`, `x ∈ I`. -/
theorem centreChartToGraded_tmul_C {x : Γ(X, U.1)} (hx : x ∈ Stacks.Conormal.chartIdeal i U) :
    centreChartToGraded i U ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_C_mem i U hx)) =
      Polynomial.C (classOfPow _ 1 ⟨x, by simpa using hx⟩) := by
  rw [centreChartToGraded, Stacks.Blowup.baseChangeReesToGraded_tmul, map_one, map_one, one_mul,
    Stacks.Blowup.reesDegOne, Stacks.Blowup.reesToGraded_monomial _ 1 ⟨_, by
      simpa using infinityChartSectionsEquiv_C_mem i U hx⟩, centreGradedTransport_C i U hx]

/-- `B ⟶ Gr_I(A)[T]` on `1 ⊗ s t`. -/
theorem centreChartToGraded_tmul_X :
    centreChartToGraded i U ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i U)) = Polynomial.X := by
  rw [centreChartToGraded, Stacks.Blowup.baseChangeReesToGraded_tmul, map_one, map_one, one_mul,
    Stacks.Blowup.reesDegOne, Stacks.Blowup.reesToGraded_monomial _ 1 ⟨_, by
      simpa using infinityChartSectionsEquiv_X_mem i U⟩, centreGradedTransport_X]

/-- `B ⟶ Gr_I(A)[T]` on scalars. -/
theorem centreChartToGraded_algebraMap (r : Γ(X, U.1)) :
    centreChartToGraded i U (algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U) ((i.app U.1).hom r)) =
      Polynomial.C (Stacks.Blowup.gradeZeroRingHom _ r) := by
  have hr : (i.app U.1).hom r = (centreChartRingHom i U).hom
      (infinityChartSectionsEquiv U (Polynomial.C r)) := by
    rw [centreChartRingHom_infinityChartSectionsEquiv, Polynomial.eval_C]
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    centreChartToGraded, Stacks.Blowup.baseChangeReesToGraded_tmul, map_one, map_one, mul_one, hr]
  change centreGradedTransport i U (Stacks.Blowup.quotientToGraded _ _ _
    (algebraMap _ Γ(Z, i ⁻¹ᵁ U.1) _)) = _
  rw [Stacks.Blowup.quotientToGraded_algebraMap, centreGradedTransport_gradeZero]

end ToGraded


/-! ### `Sym_{A/I}(I/I²) ≅ Gr_I(A)` for a regular immersion -/

section Sigma

/-- The sections of an isomorphism of algebra sheaves over an open are an isomorphism. -/
theorem isIso_algebraSheaf_app {Y : Scheme.{u}} {A B : Stacks.RelativeSpec.AlgebraSheaf Y}
    (f : A ⟶ B) [IsIso f] (W : Y.Opensᵒᵖ) : IsIso (f.right.hom.app W) := by
  have h1 : IsIso ((Under.forget Y.sheaf).map f) := Functor.map_isIso _ f
  have h2 : IsIso f.right := h1
  have h3 : IsIso ((sheafToPresheaf _ _).map f.right) := Functor.map_isIso _ f.right
  have h4 : IsIso f.right.hom := h3
  exact NatIso.isIso_app_of_isIso f.right.hom W

/-- The ring isomorphism of sections of an isomorphism of algebra sheaves. -/
def algebraSheafAppEquiv {Y : Scheme.{u}} {A B : Stacks.RelativeSpec.AlgebraSheaf Y}
    (f : A ⟶ B) [IsIso f] (W : Y.Opensᵒᵖ) : A.right.obj.obj W ≃+* B.right.obj.obj W :=
  haveI := isIso_algebraSheaf_app f W
  (asIso (f.right.hom.app W)).commRingCatIsoToRingEquiv

/-- `algebraSheafAppEquiv` is the map on sections. -/
@[simp]
theorem algebraSheafAppEquiv_apply {Y : Scheme.{u}} {A B : Stacks.RelativeSpec.AlgebraSheaf Y}
    (f : A ⟶ B) [IsIso f] (W : Y.Opensᵒᵖ) (x : A.right.obj.obj W) :
    algebraSheafAppEquiv f W x = (f.right.hom.app W).hom x := rfl

variable [IsLocallyNoetherian Z]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

/-- For a regular immersion, `𝒩^∨ ⟶ 𝒞_{Z/X,1}` is an isomorphism. -/
theorem isIso_conormalDegreeOneSurjection_ofIsRegularImmersion :
    IsIso (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection := by
  have h := VirtualNormalBundle.isIso_ofIsRegularImmersion_surjection (i := i) hi
  unfold VirtualNormalBundle.conormalDegreeOneSurjection
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h (Iso.isIso_hom _)

/-- For a regular immersion, `Sym(𝒩^∨) ⟶ Sym(𝒞_{Z/X,1})` is an isomorphism. -/
theorem isIso_symmetricAlgebraSheafMap_conormalDegreeOneSurjection :
    IsIso (Scheme.Modules.symmetricAlgebraSheafMap Z
      (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection) := by
  have h := isIso_conormalDegreeOneSurjection_ofIsRegularImmersion i hi
  exact Iso.isIso_hom ((Scheme.Modules.symmetricAlgebraSheafFunctor Z).mapIso
    (@asIso _ _ _ _ (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection h))

omit [IsLocallyNoetherian Z] in
include hi in
/-- For a regular immersion, `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is an isomorphism (Stacks 063M). -/
theorem isIso_conormalSymmetricAlgebraSheafHom_of_isRegularImmersion :
    IsIso (Stacks.Conormal.conormalSymmetricAlgebraSheafHom i) :=
  Stacks.Conormal.isIso_conormalSymmetricAlgebraSheafHom i
    ((Stacks.Conormal.isQuasiRegularImmersion_iff i).mp
      (Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isRegularImmersion i hi)).2.2

/-- **`Sym_{Γ(Z ∩ U)}(Γ(Z ∩ U, 𝒞)) ≅ Gr_I(A)` for a regular immersion**: the sections over `Z ∩ U`
of the isomorphism `Sym(𝒞_{Z/X}) ≅ 𝒞_{Z/X,*}` (Stacks 063M), read through the identification of
the sections of a symmetric algebra over an affine open and of the sections of the conormal
algebra with the associated graded ring (Stacks 0633). Here `𝒞 = 𝒩^∨` is the dual of the normal
bundle `𝒩` of `i`. -/
def conormalSymmetricSectionsEquiv :
    SymmetricAlgebra Γ(Z, i ⁻¹ᵁ U.1)
        Γ(dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle, i ⁻¹ᵁ U.1) ≃+*
      gradedRing (Stacks.Conormal.chartIdeal i U) :=
  haveI := isIso_symmetricAlgebraSheafMap_conormalDegreeOneSurjection i hi
  haveI := isIso_conormalSymmetricAlgebraSheafHom_of_isRegularImmersion i hi
  (Stacks.SymAlgSections.symSectionsRingEquiv _ (isAffineOpen_centrePreimage i U)).trans
    ((algebraSheafAppEquiv (Scheme.Modules.symmetricAlgebraSheafMap Z
        (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection)
          (op (i ⁻¹ᵁ U.1))).trans
      ((algebraSheafAppEquiv (Stacks.Conormal.conormalSymmetricAlgebraSheafHom i)
          (op (i ⁻¹ᵁ U.1))).trans
        (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance).symm))

omit [IsLocallyNoetherian Z] in
/-- On a homogeneous class of degree `n`, the identification of the associated graded ring with
the sections of the conormal algebra is the degreewise identification of Stacks 0633. -/
theorem conormalAlgebraSheafSectionsEquiv_of (n : ℕ)
    (y : AssociatedGraded.piece (M := Γ(X, U.1)) (Stacks.Conormal.chartIdeal i U) n) :
    Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
        (DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U.1))
          (Stacks.Conormal.chartIdeal i U) k) n y) =
      (Stacks.Conormal.conormalAlgebra i).algebra.ungradedIncl (n : ℤ)
        ((affineSectionsEquiv i U inferInstance).equiv n y) := by
  induction y using Submodule.Quotient.induction_on with
  | _ a =>
    have ha : (a : Γ(X, U.1)) ∈ Stacks.Conormal.chartIdeal i U ^ n := by simpa using a.2
    refine (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_of_mk i U inferInstance n a ha).trans
      ?_
    exact congrArg _ ((affineSectionsEquiv i U inferInstance).map_mk n a).symm


/-- **The identification `Sym(Γ(𝒞)) ≅ Gr_I(A)` on a degree-one generator**, read in the sections
of the conormal algebra: a section `m` of `𝒞` goes to its image in `𝒞_{Z/X}` in degree one. -/
theorem conormalAlgebraSheafSectionsEquiv_conormalSymmetricSectionsEquiv_ι
    (m : Γ(dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle, i ⁻¹ᵁ U.1)) :
    Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
        (conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _ m)) =
      (Stacks.Conormal.conormalAlgebra i).algebra.ungradedIncl 1
        ((VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection.app
          (i ⁻¹ᵁ U.1) m) := by
  have := isIso_symmetricAlgebraSheafMap_conormalDegreeOneSurjection i hi
  have := isIso_conormalSymmetricAlgebraSheafHom_of_isRegularImmersion i hi
  set φ := (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection
  change Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
    ((Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance).symm
    ((algebraSheafAppEquiv (Stacks.Conormal.conormalSymmetricAlgebraSheafHom i)
        (op (i ⁻¹ᵁ U.1)))
      ((algebraSheafAppEquiv (Scheme.Modules.symmetricAlgebraSheafMap Z φ) (op (i ⁻¹ᵁ U.1)))
        (Stacks.SymAlgSections.symSectionsRingEquiv _ (isAffineOpen_centrePreimage i U)
          (SymmetricAlgebra.ι _ _ m))))) = _
  rw [RingEquiv.apply_symm_apply, algebraSheafAppEquiv_apply, algebraSheafAppEquiv_apply]
  have hgen : ((Scheme.Modules.symmetricAlgebraUnitalHom Z φ).app 1).val.app (op (i ⁻¹ᵁ U.1))
      ((Scheme.Modules.symmetricAlgebraGen Z _).val.app (op (i ⁻¹ᵁ U.1)) m) =
      (Scheme.Modules.symmetricAlgebraGen Z (Stacks.Conormal.conormalSheafDegreeOne i)).val.app
        (op (i ⁻¹ᵁ U.1)) (φ.val.app (op (i ⁻¹ᵁ U.1)) m) :=
    congrArg (fun ψ => ψ.val.app (op (i ⁻¹ᵁ U.1)) m)
      (Scheme.Modules.symmetricAlgebraGen_comp_symmetricAlgebraUnitalHom Z φ)
  have h1 := Stacks.ProjectiveCompletion.symSectionsRingEquiv_ι
    (isAffineOpen_centrePreimage i U) m
  have h2 : ((Scheme.Modules.symmetricAlgebraSheafMap Z φ).right.hom.app
      (op (i ⁻¹ᵁ U.1))).hom (Stacks.ProjectiveCompletion.symGenSection _ (i ⁻¹ᵁ U.1) m) =
      (Scheme.Modules.symmetricAlgebra Z (Stacks.Conormal.conormalSheafDegreeOne i)).ungradedIncl 1
        ((Scheme.Modules.symmetricAlgebraGen Z (Stacks.Conormal.conormalSheafDegreeOne i)).val.app
          (op (i ⁻¹ᵁ U.1)) (φ.val.app (op (i ⁻¹ᵁ U.1)) m)) :=
    (Scheme.Modules.symmetricAlgebraSheafMap_ungradedIncl Z φ (op (i ⁻¹ᵁ U.1)) 1 _).trans
      (congrArg _ hgen)
  have h3 : ((Stacks.Conormal.conormalSymmetricAlgebraSheafHom i).right.hom.app
      (op (i ⁻¹ᵁ U.1))).hom
      ((Scheme.Modules.symmetricAlgebra Z (Stacks.Conormal.conormalSheafDegreeOne i)).ungradedIncl 1
        ((Scheme.Modules.symmetricAlgebraGen Z (Stacks.Conormal.conormalSheafDegreeOne i)).val.app
          (op (i ⁻¹ᵁ U.1)) (φ.val.app (op (i ⁻¹ᵁ U.1)) m))) =
      (Stacks.Conormal.conormalAlgebra i).algebra.ungradedIncl 1 (φ.val.app (op (i ⁻¹ᵁ U.1)) m) :=
    (SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap _ 1 _).trans
      (congrArg _ (congrArg (fun ψ => ψ.val.app (op (i ⁻¹ᵁ U.1)) (φ.val.app (op (i ⁻¹ᵁ U.1)) m))
        (Stacks.Conormal.conormalSymmetricHom_gen i)))
  exact (congrArg _ ((congrArg _ h1).trans h2)).trans h3

/-- **The identification `Sym(Γ(𝒞)) ≅ Gr_I(A)` on a degree-one generator**: a section `m` of `𝒞`
goes to its class in `I/I²`. -/
theorem conormalSymmetricSectionsEquiv_ι
    (m : Γ(dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle, i ⁻¹ᵁ U.1)) :
    conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _ m) =
      DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U.1))
        (Stacks.Conormal.chartIdeal i U) k) 1
        (((affineSectionsEquiv i U inferInstance).equiv 1).symm
          ((VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection.app
            (i ⁻¹ᵁ U.1) m)) := by
  refine (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance).injective ?_
  rw [conormalAlgebraSheafSectionsEquiv_conormalSymmetricSectionsEquiv_ι,
    conormalAlgebraSheafSectionsEquiv_of]
  exact congrArg ((Stacks.Conormal.conormalAlgebra i).algebra.ungradedIncl ((1 : ℕ) : ℤ))
    (AddEquiv.apply_symm_apply _ _).symm

/-- A degree-one generator of `Sym(Γ(𝒞))` goes to the class in `I/I²` of some `x ∈ I`. -/
theorem exists_conormalSymmetricSectionsEquiv_ι_eq
    (m : Γ(dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle, i ⁻¹ᵁ U.1)) :
    ∃ (x : Γ(X, U.1)) (hx : x ∈ Stacks.Conormal.chartIdeal i U),
      conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _ m) =
        classOfPow _ 1 ⟨x, by simpa using hx⟩ := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (((affineSectionsEquiv i U inferInstance).equiv 1).symm
      ((VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection.app
        (i ⁻¹ᵁ U.1) m))
  refine ⟨(y : Γ(X, U.1)), by simpa using y.2, ?_⟩
  rw [conormalSymmetricSectionsEquiv_ι, ← hy]
  rfl

/-- A morphism of algebra sheaves commutes with the structure maps, on sections. -/
theorem algebraSheaf_app_structure {Y : Scheme.{u}} {A B : Stacks.RelativeSpec.AlgebraSheaf Y}
    (f : A ⟶ B) (W : Y.Opensᵒᵖ) (r : Γ(Y, W.unop)) :
    (f.right.hom.app W).hom ((A.hom.hom.app W).hom r) = (B.hom.hom.app W).hom r :=
  congrArg (fun g : Y.sheaf ⟶ B.right => (g.hom.app W).hom r) (Under.w f)

/-- **The identification `Sym(Γ(𝒞)) ≅ Gr_I(A)` on scalars**: the image of `a ∈ A` in
`Γ(Z, Z ∩ U)` goes to the class of `a` in degree zero. -/
theorem conormalSymmetricSectionsEquiv_algebraMap (r : Γ(X, U.1)) :
    conormalSymmetricSectionsEquiv i U hi (algebraMap Γ(Z, i ⁻¹ᵁ U.1) _ ((i.app U.1).hom r)) =
      Stacks.Blowup.gradeZeroRingHom _ r := by
  have := isIso_symmetricAlgebraSheafMap_conormalDegreeOneSurjection i hi
  have := isIso_conormalSymmetricAlgebraSheafHom_of_isRegularImmersion i hi
  set φ := (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection
  change (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance).symm
    ((algebraSheafAppEquiv (Stacks.Conormal.conormalSymmetricAlgebraSheafHom i)
        (op (i ⁻¹ᵁ U.1)))
      ((algebraSheafAppEquiv (Scheme.Modules.symmetricAlgebraSheafMap Z φ) (op (i ⁻¹ᵁ U.1)))
        (Stacks.SymAlgSections.symSectionsRingEquiv _ (isAffineOpen_centrePreimage i U)
          (algebraMap _ _ ((i.app U.1).hom r))))) = _
  rw [RingEquiv.symm_apply_eq, Stacks.Blowup.gradeZeroRingHom_apply,
    Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_of_gradeZeroMk,
    algebraSheafAppEquiv_apply, algebraSheafAppEquiv_apply,
    Stacks.SymAlgSections.symSectionsRingEquiv_algebraMap]
  exact (congrArg _ (algebraSheaf_app_structure _ _ _)).trans (algebraSheaf_app_structure _ _ _)

end Sigma


/-! ### The ring of the chart of `E` is the ring of the chart of `𝐏(𝒞 ⊕ 𝒪_Z)` -/

section ChartEquiv

attribute [instance] VirtualNormalBundle.isFiniteLocallyFree_dualSheaf

/-- The ideal of the centre on `Γ(𝐏¹_X, V)` lies in the kernel of `Γ(𝐏¹_X, V) ⟶ Γ(Z, Z ∩ U)`. -/
theorem le_ker_algebraMap_centreChart :
    (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ≤
      RingHom.ker (algebraMap Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)
        Γ(Z, i ⁻¹ᵁ U.1)) := by
  rw [ideal_infinityCentreIdeal_eq_map]
  intro r hr
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_of_equiv _ r).1 hr
  rw [RingHom.mem_ker]
  change (centreChartRingHom i U).hom (infinityChartSectionsEquiv U p) = 0
  rw [centreChartRingHom_infinityChartSectionsEquiv, ← Polynomial.coeff_zero_eq_eval_zero]
  have h := coeff_mem_pow_sub _ (show p ∈ infinityChartIdeal (Stacks.Conormal.chartIdeal i U) ^ 1
    by rwa [pow_one]) 0
  simpa using h

/-- The map of associated graded rings induced by the identity is the identity. -/
theorem gradedRingMapOfRingHom_id_apply {A : Type*} [CommRing A] {I : Ideal A}
    (h : I.map (RingHom.id A) ≤ I) (z : gradedRing I) :
    gradedRingMapOfRingHom (RingHom.id A) h z = z :=
  (AssociatedGraded.gradedRingEquivOfEq_apply rfl z).symm

/-- `Gr_𝒥(Γ(V)) ⟶ Gr_I(A)[T]` is bijective. -/
theorem bijective_centreGradedTransport : Function.Bijective (centreGradedTransport i U) := by
  have h' : (infinityChartIdeal (Stacks.Conormal.chartIdeal i U)).map
      (infinityChartSectionsEquiv U).toRingHom ≤
        (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) := by
    rw [ideal_infinityCentreIdeal_eq_map]
    rfl
  have hinv : Function.Bijective (gradedRingMapOfRingHom
      (infinityChartSectionsEquiv U).symm.toRingHom (map_infinityCentreIdeal_le i U)) := by
    refine ⟨Function.LeftInverse.injective
      (g := gradedRingMapOfRingHom (infinityChartSectionsEquiv U).toRingHom h') fun z => ?_,
      Function.RightInverse.surjective
      (g := gradedRingMapOfRingHom (infinityChartSectionsEquiv U).toRingHom h') fun z => ?_⟩
    · rw [AssociatedGraded.gradedRingMapOfRingHom_comp_apply _ _ _ _ (by
        rw [show ((infinityChartSectionsEquiv U).toRingHom.comp
          (infinityChartSectionsEquiv U).symm.toRingHom) = RingHom.id _ from
            RingHom.ext fun x => (infinityChartSectionsEquiv U).apply_symm_apply x, Ideal.map_id])]
      convert gradedRingMapOfRingHom_id_apply (by rw [Ideal.map_id]) z
      exact RingHom.ext fun x => (infinityChartSectionsEquiv U).apply_symm_apply x
    · rw [AssociatedGraded.gradedRingMapOfRingHom_comp_apply _ _ _ _ (by
        rw [show ((infinityChartSectionsEquiv U).symm.toRingHom.comp
          (infinityChartSectionsEquiv U).toRingHom) = RingHom.id _ from
            RingHom.ext fun x => (infinityChartSectionsEquiv U).symm_apply_apply x, Ideal.map_id])]
      convert gradedRingMapOfRingHom_id_apply (by rw [Ideal.map_id]) z
      exact RingHom.ext fun x => (infinityChartSectionsEquiv U).symm_apply_apply x
  exact (infinityChartGradedEquiv _).symm.bijective.comp hinv

/-- **`B ⟶ Gr_I(A)[T]` is bijective**: `Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥 t] = Gr_𝒥(Γ(V))`, because
`Γ(Z ∩ U) = Γ(V)/𝒥`, and `Gr_𝒥(Γ(V)) = Gr_{(I, s)}(A[s]) = Gr_I(A)[T]`. -/
theorem bijective_centreChartToGraded : Function.Bijective (centreChartToGraded i U) := by
  rw [centreChartToGraded, Stacks.Blowup.baseChangeReesToGraded_eq_comp, RingHom.coe_comp]
  exact (bijective_centreGradedTransport i U).comp
    (Stacks.Blowup.bijective_baseChangeReesToGraded _ _ _ (le_ker_algebraMap_centreChart i U))

/-- `B ≅ Gr_I(A)[T]` as rings. -/
def centreChartToGradedEquiv :
    centreChartRing i U ≃+* Polynomial (gradedRing (Stacks.Conormal.chartIdeal i U)) :=
  RingEquiv.ofBijective (centreChartToGraded i U) (bijective_centreChartToGraded i U)

/-- `centreChartToGradedEquiv` is `centreChartToGraded`. -/
theorem centreChartToGradedEquiv_apply (x : centreChartRing i U) :
    centreChartToGradedEquiv i U x = centreChartToGraded i U x := rfl

variable [IsLocallyNoetherian Z]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

/-- The ring isomorphism `Sym_{Γ(Z ∩ U)}(Γ(𝒞 ⊕ 𝒪_Z)) ≅ Sym(Γ(𝒞))[T] ≅ Gr_I(A)[T] ≅ B`. -/
def exceptionalChartSymEquiv :
    SymmetricAlgebra Γ(Z, i ⁻¹ᵁ U.1) Γ(Stacks.ProjectiveCompletion.completionModule
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle), i ⁻¹ᵁ U.1) ≃+*
      centreChartRing i U :=
  (Stacks.ProjectiveCompletion.sectionsSplitting
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
      (i ⁻¹ᵁ U.1)).symPolynomialEquiv.toRingEquiv.trans
    ((Polynomial.mapEquiv (conormalSymmetricSectionsEquiv i U hi)).trans
      (centreChartToGradedEquiv i U).symm)

/-- **The graded ring of the chart of `𝐏(𝒞 ⊕ 𝒪_Z)` over `Z ∩ U` is that of the chart of `E`**:

  `Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z)) ≅ Sym(Γ(𝒞))[T] ≅ Gr_I(A)[T] ≅ Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥 t]`. -/
def exceptionalChartRingEquiv :
    (completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).sectionRing (i ⁻¹ᵁ U.1) ≃+*
      centreChartRing i U :=
  (Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U)).trans
    (exceptionalChartSymEquiv i U hi)

/-- `exceptionalChartSymEquiv` written out. -/
theorem exceptionalChartSymEquiv_apply (x : SymmetricAlgebra Γ(Z, i ⁻¹ᵁ U.1)
    Γ(Stacks.ProjectiveCompletion.completionModule
      (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle), i ⁻¹ᵁ U.1)) :
    exceptionalChartSymEquiv i U hi x = (centreChartToGradedEquiv i U).symm
      (Polynomial.map (conormalSymmetricSectionsEquiv i U hi).toRingHom
        ((Stacks.ProjectiveCompletion.sectionsSplitting
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
          (i ⁻¹ᵁ U.1)).toPolynomial x)) := rfl

/-- **The isomorphism on scalars.** -/
theorem exceptionalChartSymEquiv_algebraMap (s : Γ(Z, i ⁻¹ᵁ U.1)) :
    exceptionalChartSymEquiv i U hi (algebraMap _ _ s) =
      algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U) s := by
  obtain ⟨r, rfl⟩ := Scheme.Hom.app_surjective i U.1 U.2 s
  rw [exceptionalChartSymEquiv_apply, AlgHom.commutes, Polynomial.algebraMap_apply,
    Polynomial.map_C, RingEquiv.symm_apply_eq, centreChartToGradedEquiv_apply,
    centreChartToGraded_algebraMap]
  exact congrArg _ (conormalSymmetricSectionsEquiv_algebraMap i U hi r)

/-- `B ⟶ Gr_I(A)[T]` on `1 ⊗ x t + q ⊗ s t`. -/
theorem centreChartToGraded_degreeOne {x : Γ(X, U.1)} (hx : x ∈ Stacks.Conormal.chartIdeal i U)
    (q : Γ(Z, i ⁻¹ᵁ U.1)) :
    centreChartToGraded i U ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_C_mem i U hx) +
      algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U) q *
        ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
          Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i U))) =
      Polynomial.C (classOfPow _ 1 ⟨x, by simpa using hx⟩) +
        Polynomial.C (conormalSymmetricSectionsEquiv i U hi (algebraMap _ _ q)) * Polynomial.X := by
  obtain ⟨r, rfl⟩ := Scheme.Hom.app_surjective i U.1 U.2 q
  rw [map_add, map_mul]
  have h3 := centreChartToGraded_algebraMap i U r
  have h4 := conormalSymmetricSectionsEquiv_algebraMap i U hi r
  exact congrArg₂ (· + ·) (centreChartToGraded_tmul_C i U hx)
    (congrArg₂ (· * ·) (h3.trans (congrArg Polynomial.C h4.symm)) (centreChartToGraded_tmul_X i U))

/-- **The isomorphism on a degree-one generator** `n = j(m) + q(n) t₀` of `Γ(𝒞 ⊕ 𝒪_Z)`: it is
`1 ⊗ x t + q(n) ⊗ s t`, for any `x ∈ I` representing the class of `m` in `I/I²`. -/
theorem exceptionalChartSymEquiv_ι_of
    (n : Γ(Stacks.ProjectiveCompletion.completionModule
      (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle), i ⁻¹ᵁ U.1))
    {x : Γ(X, U.1)} (hx : x ∈ Stacks.Conormal.chartIdeal i U)
    (hκ : conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _
        ((Stacks.ProjectiveCompletion.sectionsSplitting
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).p n)) =
      classOfPow _ 1 ⟨x, by simpa using hx⟩) :
    exceptionalChartSymEquiv i U hi (SymmetricAlgebra.ι _ _ n) =
      (1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
          Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_C_mem i U hx) +
        algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U)
            ((Stacks.ProjectiveCompletion.sectionsSplitting
              (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
              (i ⁻¹ᵁ U.1)).q n) *
          ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
            Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i U)) := by
  set S' := Stacks.ProjectiveCompletion.sectionsSplitting
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)
  rw [exceptionalChartSymEquiv_apply, RingEquiv.symm_apply_eq, centreChartToGradedEquiv_apply]
  have hL : Polynomial.map (conormalSymmetricSectionsEquiv i U hi).toRingHom
      (S'.toPolynomial (SymmetricAlgebra.ι _ _ n)) =
      Polynomial.C (conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _ (S'.p n))) +
        Polynomial.C (conormalSymmetricSectionsEquiv i U hi (algebraMap _ _ (S'.q n))) *
          Polynomial.X := by
    rw [Stacks.SymmetricAway.LineSplitting.toPolynomial_ι']
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    rfl
  rw [hL, hκ]
  exact (centreChartToGraded_degreeOne i U hi hx (S'.q n)).symm

/-- **The isomorphism on a degree-one generator** `n = j(m) + q(n) t₀` of `Γ(𝒞 ⊕ 𝒪_Z)`: it is
`1 ⊗ x t + q(n) ⊗ s t`, where `x ∈ I` represents the class of `m` in `I/I²`. -/
theorem exceptionalChartSymEquiv_ι
    (n : Γ(Stacks.ProjectiveCompletion.completionModule
      (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle), i ⁻¹ᵁ U.1)) :
    ∃ (x : Γ(X, U.1)) (hx : x ∈ Stacks.Conormal.chartIdeal i U),
      exceptionalChartSymEquiv i U hi (SymmetricAlgebra.ι _ _ n) =
        (1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
            Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_C_mem i U hx) +
          algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U)
              ((Stacks.ProjectiveCompletion.sectionsSplitting
                (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
                (i ⁻¹ᵁ U.1)).q n) *
            ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
              Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i U)) := by
  obtain ⟨x, hx, hκ⟩ := exists_conormalSymmetricSectionsEquiv_ι_eq i U hi
    ((Stacks.ProjectiveCompletion.sectionsSplitting
      (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).p n)
  exact ⟨x, hx, exceptionalChartSymEquiv_ι_of i U hi n hx hκ⟩


/-- The image of a degree-one generator has degree one. -/
theorem exceptionalChartSymEquiv_ι_mem
    (n : Γ(Stacks.ProjectiveCompletion.completionModule
      (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle), i ⁻¹ᵁ U.1)) :
    exceptionalChartSymEquiv i U hi (SymmetricAlgebra.ι _ _ n) ∈ centreChartGrading i U 1 := by
  obtain ⟨x, hx, h⟩ := exceptionalChartSymEquiv_ι i U hi n
  rw [h]
  refine add_mem (Submodule.tmul_mem_baseChange_of_mem _
    (Stacks.Blowup.reesDegOne_mem_reesGrading _ _)) ?_
  have hm := Submodule.smul_mem (centreChartGrading i U 1)
    ((Stacks.ProjectiveCompletion.sectionsSplitting
      (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).q n)
    (Submodule.tmul_mem_baseChange_of_mem (1 : Γ(Z, i ⁻¹ᵁ U.1))
      (Stacks.Blowup.reesDegOne_mem_reesGrading _ (infinityChartSectionsEquiv_X_mem i U)))
  rwa [Algebra.smul_def] at hm

/-- **The isomorphism `Sym(Γ(𝒞 ⊕ 𝒪_Z)) ≅ B` is graded.** -/
theorem exceptionalChartSymEquiv_mem {n : ℕ}
    {y : SymmetricAlgebra Γ(Z, i ⁻¹ᵁ U.1) Γ(Stacks.ProjectiveCompletion.completionModule
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle), i ⁻¹ᵁ U.1)}
    (hy : y ∈ SymPow.symmetricPower n _ _) :
    exceptionalChartSymEquiv i U hi y ∈ centreChartGrading i U n := by
  rw [SymmetricAlgebra.symmetricPower_eq_span_prod_ι] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, rfl⟩ := hy
    rw [map_prod]
    have h := SetLike.prod_mem_graded (A := centreChartGrading i U) (fun _ : Fin n => 1)
      (fun j => exceptionalChartSymEquiv i U hi (SymmetricAlgebra.ι _ _ (f j)))
      (F := Finset.univ) (fun j _ => exceptionalChartSymEquiv_ι_mem i U hi (f j))
    simpa using h
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx =>
    rw [Algebra.smul_def, map_mul, exceptionalChartSymEquiv_algebraMap, ← Algebra.smul_def]
    exact Submodule.smul_mem _ s hx

/-- `exceptionalChartRingEquiv` preserves the gradings. -/
theorem exceptionalChartRingEquiv_mem {n : ℕ}
    {x : (completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).sectionRing (i ⁻¹ᵁ U.1)}
    (hx : x ∈ (completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1) n) :
    exceptionalChartRingEquiv i U hi x ∈ centreChartGrading i U n :=
  exceptionalChartSymEquiv_mem i U hi
    ((Stacks.ProjectiveCompletion.sectionRingEquiv_mem_iff _ n x).2 hx)

/-- `Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z)) ≅ B` as a homomorphism of graded rings. -/
def exceptionalChartGradedHom :
    (completionAlgebra (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading
        (i ⁻¹ᵁ U.1) →+*ᵍ centreChartGrading i U where
  toRingHom := (exceptionalChartRingEquiv i U hi).toRingHom
  map_mem hx := exceptionalChartRingEquiv_mem i U hi hx

/-- The inverse `B ≅ Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` as a homomorphism of graded rings. -/
def exceptionalChartGradedInv :
    centreChartGrading i U →+*ᵍ
      (completionAlgebra (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading
        (i ⁻¹ᵁ U.1) where
  toRingHom := (exceptionalChartRingEquiv i U hi).symm.toRingHom
  map_mem hx := Stacks.GradedTransport.symm_mem ((completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1))
    (centreChartGrading i U) (exceptionalChartRingEquiv i U hi)
    (fun _ _ h => exceptionalChartRingEquiv_mem i U hi h) hx

/-- `exceptionalChartGradedHom` is a left inverse of `exceptionalChartGradedInv`. -/
theorem exceptionalChartGradedHom_comp_inv :
    (exceptionalChartGradedHom i U hi).comp (exceptionalChartGradedInv i U hi) =
      GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (exceptionalChartRingEquiv i U hi).apply_symm_apply x

/-- `exceptionalChartGradedInv` is a left inverse of `exceptionalChartGradedHom`. -/
theorem exceptionalChartGradedInv_comp_hom :
    (exceptionalChartGradedInv i U hi).comp (exceptionalChartGradedHom i U hi) =
      GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (exceptionalChartRingEquiv i U hi).symm_apply_apply x

/-- The irrelevant ideal of `Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` is contained in the image of the irrelevant
ideal of `B` under `exceptionalChartGradedInv`. -/
theorem irrelevant_le_map_exceptionalChartGradedInv :
    HomogeneousIdeal.irrelevant ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1)) ≤
      (HomogeneousIdeal.irrelevant (centreChartGrading i U)).map
        (exceptionalChartGradedInv i U hi) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _
    (exceptionalChartGradedInv_comp_hom i U hi)

/-- The irrelevant ideal of `B` is contained in the image of the irrelevant ideal of
`Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` under `exceptionalChartGradedHom`. -/
theorem irrelevant_le_map_exceptionalChartGradedHom :
    HomogeneousIdeal.irrelevant (centreChartGrading i U) ≤
      (HomogeneousIdeal.irrelevant ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1))).map
        (exceptionalChartGradedHom i U hi) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _
    (exceptionalChartGradedHom_comp_inv i U hi)

/-- **`Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z)) ≅ Proj B`.** -/
def exceptionalChartProjMap :
    AlgebraicGeometry.Proj ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1)) ⟶
      AlgebraicGeometry.Proj (centreChartGrading i U) :=
  Proj.map (exceptionalChartGradedInv i U hi) (irrelevant_le_map_exceptionalChartGradedInv i U hi)

/-- The morphism `exceptionalChartProjMap` is an isomorphism. -/
instance : IsIso (exceptionalChartProjMap i U hi) :=
  AlgebraicGeometry.Proj.isIso_map _ (irrelevant_le_map_exceptionalChartGradedHom i U hi)
    (exceptionalChartGradedHom_comp_inv i U hi) (exceptionalChartGradedInv_comp_hom i U hi)


/-- **The isomorphism on the structure map**: `Γ(Z ∩ U) ⟶ Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z)) ≅ B` is the
structure map of `B`. -/
theorem exceptionalChartRingEquiv_strHom (s : Γ(Z, i ⁻¹ᵁ U.1)) :
    exceptionalChartRingEquiv i U hi ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).strHom (i ⁻¹ᵁ U.1) s) =
      algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U) s := by
  have h1 : (completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).strHom (i ⁻¹ᵁ U.1) s =
      (Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U)).symm
        (algebraMap _ _ s) :=
    (Stacks.SymTwistChart.symSectionRingEquiv_symm_algebraMap _ _
      (isAffineOpen_centrePreimage i U) s).symm
  rw [h1]
  change exceptionalChartSymEquiv i U hi
    ((Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U))
      ((Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U)).symm
        (algebraMap _ _ s))) = _
  rw [RingEquiv.apply_symm_apply, exceptionalChartSymEquiv_algebraMap]

/-- The inverse `Proj B ⟶ Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` of `exceptionalChartProjMap`. -/
def exceptionalChartProjInv :
    AlgebraicGeometry.Proj (centreChartGrading i U) ⟶
      AlgebraicGeometry.Proj ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1)) :=
  Proj.map (exceptionalChartGradedHom i U hi) (irrelevant_le_map_exceptionalChartGradedHom i U hi)

/-- The morphism `exceptionalChartProjInv` is an isomorphism. -/
instance : IsIso (exceptionalChartProjInv i U hi) :=
  AlgebraicGeometry.Proj.isIso_map _ (irrelevant_le_map_exceptionalChartGradedInv i U hi)
    (exceptionalChartGradedInv_comp_hom i U hi) (exceptionalChartGradedHom_comp_inv i U hi)


/-- **`Proj B ≅ Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` lies over `Z ∩ U`.** -/
theorem exceptionalChartProjInv_toSpecZero :
    exceptionalChartProjInv i U hi ≫ Proj.toSpecZero ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1)) ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1))).comp
          ((completionAlgebra (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).strHom (i ⁻¹ᵁ U.1)))) =
      centreChartToSpec i U :=
  AlgebraicGeometry.Proj.map_toSpecZero_specMap _ _ _ _
    (GradedRingHom.comp_gradedZeroRingHom_eq _ _ _ fun s =>
      (congrArg (exceptionalChartGradedHom i U hi)
        (Stacks.AlgebraicGeometry.RelativeProj.projZeroRingHom'_coe_of_mem _
          ((completionAlgebra (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).strHom_mem _ s))).trans
        (exceptionalChartRingEquiv_strHom i U hi s))


/-! ### Compatibility with restriction -/

/-- `Γ(X, U)[s] ≅ Γ(𝐏¹_X, V_U)` is compatible with restriction to `V ⊆ U`. -/
theorem lineChartRestrict_infinityChartSectionsEquiv {V : X.affineOpens} (h : V.1 ≤ U.1)
    (p : Polynomial Γ(X, U.1)) :
    (lineChartRestrict h).hom (infinityChartSectionsEquiv U p) =
      infinityChartSectionsEquiv V (p.map (affineRestrict h)) := by
  have key : (infinityChartSectionsIso U).hom ≫ lineChartRestrict h =
      CommRingCat.ofHom (Polynomial.mapRingHom (affineRestrict h)) ≫
        (infinityChartSectionsIso V).hom := by
    apply Spec.map_injective
    rw [← cancel_mono (infinityChartOver U), Spec.map_comp, Spec.map_comp, Category.assoc,
      Category.assoc, specMap_infinityChartSectionsIso_infinityChartOver,
      specMap_map_infinityChartOver, specMap_infinityChartSectionsIso_infinityChartOver]
    exact IsAffineOpen.map_fromSpec _ _ _
  exact congrArg (fun φ => CommRingCat.Hom.hom φ p) key

omit [IsLocallyNoetherian Z] [IsClosedImmersion i] in
/-- The restriction of the graded rings of the charts of `E` on `1 ⊗ j t`. -/
theorem centreChartRestrict_tmul_reesDegOne {V : X.affineOpens} (h : V.1 ≤ U.1)
    {j : Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)}
    {j' : Γ(relativeProjectiveLine X, (infinityChartAffineOpen V).1)}
    (hj : j ∈ (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U))
    (hj' : j' ∈ (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen V))
    (hjj : (lineChartRestrict h).hom j = j') :
    centreChartRestrict i h ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ Stacks.Blowup.reesDegOne _ hj) =
      (1 : Γ(Z, i ⁻¹ᵁ V.1)) ⊗ₜ Stacks.Blowup.reesDegOne _ hj' := by
  change centreChartRestrictRingHom i h _ = _
  rw [centreChartRestrictRingHom_tmul, map_one]
  congr 1
  refine Subtype.ext ?_
  rw [Stacks.Blowup.coe_reesRestrict, Stacks.Blowup.coe_reesDegOne,
    Stacks.Blowup.coe_reesDegOne, Polynomial.map_monomial]
  exact congrArg _ hjj

omit [IsLocallyNoetherian Z] in
/-- The restriction of the graded rings of the charts of `E` on a degree-one element
`1 ⊗ x t + q ⊗ s t`. -/
theorem centreChartRestrict_degreeOne {V : X.affineOpens} (h : V.1 ≤ U.1) {x : Γ(X, U.1)}
    (hx : x ∈ Stacks.Conormal.chartIdeal i U) (q : Γ(Z, i ⁻¹ᵁ U.1)) :
    centreChartRestrict i h ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_C_mem i U hx) +
      algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U) q *
        ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
          Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i U))) =
      (1 : Γ(Z, i ⁻¹ᵁ V.1)) ⊗ₜ Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_C_mem i V
          (Stacks.Conormal.map_mem_chartIdeal i h hx)) +
        algebraMap Γ(Z, i ⁻¹ᵁ V.1) (centreChartRing i V) ((centreRestrict i h).hom q) *
          ((1 : Γ(Z, i ⁻¹ᵁ V.1)) ⊗ₜ
            Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i V)) := by
  rw [map_add, map_mul, centreChartRestrict_algebraMap]
  have h1 := centreChartRestrict_tmul_reesDegOne i U h (infinityChartSectionsEquiv_C_mem i U hx)
    (infinityChartSectionsEquiv_C_mem i V (Stacks.Conormal.map_mem_chartIdeal i h hx))
    ((lineChartRestrict_infinityChartSectionsEquiv U h _).trans (by rw [Polynomial.map_C]))
  have h2 := centreChartRestrict_tmul_reesDegOne i U h (infinityChartSectionsEquiv_X_mem i U)
    (infinityChartSectionsEquiv_X_mem i V)
    ((lineChartRestrict_infinityChartSectionsEquiv U h _).trans (by rw [Polynomial.map_X]))
  exact congrArg₂ (· + ·) h1 (congrArg₂ (· * ·) rfl h2)

/-- **`Sym(Γ(𝒞)) ≅ Gr_I(A)` is compatible with restriction**, on degree-one generators. -/
theorem gradedRingMapOfRingHom_conormalSymmetricSectionsEquiv_ι {V : X.affineOpens}
    (h : V.1 ≤ U.1)
    (m : Γ(dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle, i ⁻¹ᵁ U.1)) :
    AssociatedGraded.gradedRingMapOfRingHom (X.presheaf.map (homOfLE h).op).hom
        (Stacks.Conormal.map_chartIdeal_le i h)
        (conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _ m)) =
      conormalSymmetricSectionsEquiv i V hi (SymmetricAlgebra.ι _ _
        ((dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle).presheaf.map
          (homOfLE (i.preimage_mono h)).op m)) := by
  refine (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i V inferInstance).injective ?_
  refine (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_restrict i U inferInstance V
    inferInstance h _).symm.trans ?_
  refine (congrArg _ (conormalAlgebraSheafSectionsEquiv_conormalSymmetricSectionsEquiv_ι i U hi
    m)).trans ?_
  refine ((Stacks.Conormal.conormalAlgebra i).algebra.ungradedIncl_naturality _ 1 _).trans ?_
  refine Eq.trans ?_
    (conormalAlgebraSheafSectionsEquiv_conormalSymmetricSectionsEquiv_ι i V hi _).symm
  exact congrArg _ (PresheafOfModules.naturality_apply
    (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection.val
      (homOfLE (i.preimage_mono h)).op m).symm

/-- **The identification of the charts is compatible with restriction.** -/
theorem centreChartRestrict_comp_exceptionalChartGradedHom {V : X.affineOpens} (h : V.1 ≤ U.1) :
    (centreChartRestrict i h).comp (exceptionalChartGradedHom i U hi) =
      (exceptionalChartGradedHom i V hi).comp ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).res
          (i.preimage_mono h)) := by
  have key : (centreChartRestrictRingHom i h).comp (exceptionalChartSymEquiv i U hi).toRingHom =
      ((exceptionalChartRingEquiv i V hi).toRingHom.comp ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).resRingHom
          (i.preimage_mono h))).comp
        (Stacks.ProjectiveCompletion.sectionRingEquiv
          (isAffineOpen_centrePreimage i U)).symm.toRingHom := by
    refine SymmetricAlgebra.ringHom_ext (fun s => ?_) (fun n => ?_)
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [exceptionalChartSymEquiv_algebraMap,
        Stacks.SymTwistChart.symSectionRingEquiv_symm_algebraMap _ _
          (isAffineOpen_centrePreimage i U) s,
        (completionAlgebra (dualSheaf
          (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).resRingHom_strHom,
        exceptionalChartRingEquiv_strHom]
      exact centreChartRestrict_algebraMap i h s
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      obtain ⟨x, hx, hκ⟩ := exists_conormalSymmetricSectionsEquiv_ι_eq i U hi
        ((Stacks.ProjectiveCompletion.sectionsSplitting
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).p n)
      rw [exceptionalChartSymEquiv_ι_of i U hi n hx hκ]
      refine (centreChartRestrict_degreeOne i U h hx _).trans ?_
      have hn : (Stacks.ProjectiveCompletion.sectionRingEquiv
          (isAffineOpen_centrePreimage i U)).symm (SymmetricAlgebra.ι _ _ n) =
          DirectSum.of ((completionAlgebra (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).sectionPieces (i ⁻¹ᵁ U.1)) 1
            ((Scheme.Modules.symmetricAlgebraGen Z (Stacks.ProjectiveCompletion.completionModule
              (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).val.app
                (op (i ⁻¹ᵁ U.1)) n) :=
        (RingEquiv.symm_apply_eq _).2
          (Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen _
            (isAffineOpen_centrePreimage i U) _ n).symm
      have e1 : (completionAlgebra (dualSheaf
          (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).resRingHom (i.preimage_mono h)
          (DirectSum.of ((completionAlgebra (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).sectionPieces (i ⁻¹ᵁ U.1)) 1
            ((Scheme.Modules.symmetricAlgebraGen Z (Stacks.ProjectiveCompletion.completionModule
              (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).val.app
                (op (i ⁻¹ᵁ U.1)) n)) =
          DirectSum.of ((completionAlgebra (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).sectionPieces (i ⁻¹ᵁ V.1)) 1
            ((Scheme.Modules.symmetricAlgebraGen Z (Stacks.ProjectiveCompletion.completionModule
              (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).val.app
                (op (i ⁻¹ᵁ V.1))
              ((Stacks.ProjectiveCompletion.completionModule (dualSheaf
                (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).presheaf.map
                  (homOfLE (i.preimage_mono h)).op n)) :=
        ((completionAlgebra (dualSheaf
          (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).resRingHom_of _ _).trans
          (congrArg (DirectSum.of ((completionAlgebra (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).sectionPieces
              (i ⁻¹ᵁ V.1)) 1)
            (PresheafOfModules.naturality_apply
              (Scheme.Modules.symmetricAlgebraGen Z (Stacks.ProjectiveCompletion.completionModule
                (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).val
                  (homOfLE (i.preimage_mono h)).op n).symm)
      have e2 := congrArg (exceptionalChartSymEquiv i V hi)
        (Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen _
          (isAffineOpen_centrePreimage i V)
          (Stacks.Chow.bundlePieces (Stacks.ProjectiveCompletion.completionModule (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)))
          ((Stacks.ProjectiveCompletion.completionModule (dualSheaf
            (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).presheaf.map
              (homOfLE (i.preimage_mono h)).op n))
      have hκ' : conormalSymmetricSectionsEquiv i V hi (SymmetricAlgebra.ι _ _
          ((Stacks.ProjectiveCompletion.sectionsSplitting
            (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ V.1)).p
            ((Stacks.ProjectiveCompletion.completionModule (dualSheaf
              (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).presheaf.map
                (homOfLE (i.preimage_mono h)).op n))) =
          classOfPow _ 1 ⟨(X.presheaf.map (homOfLE h).op).hom x, by
            rw [pow_one]; exact Stacks.Conormal.map_mem_chartIdeal i h hx⟩ := by
        rw [Stacks.ProjectiveCompletion.sectionsSplitting_p_restrict (i.preimage_mono h) n,
          ← gradedRingMapOfRingHom_conormalSymmetricSectionsEquiv_ι i U hi h, hκ,
          gradedRingMapOfRingHom_classOfPow]
      rw [hn, e1]
      refine Eq.trans ?_ e2.symm
      rw [exceptionalChartSymEquiv_ι_of i V hi _ (Stacks.Conormal.map_mem_chartIdeal i h hx) hκ',
        Stacks.ProjectiveCompletion.sectionsSplitting_q_restrict (i.preimage_mono h) n]
  refine GradedRingHom.ext fun y => ?_
  have hk := RingHom.congr_fun key
    (Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U) y)
  refine hk.trans ?_
  change (exceptionalChartRingEquiv i V hi) ((completionAlgebra (dualSheaf
    (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).resRingHom
      (i.preimage_mono h) ((Stacks.ProjectiveCompletion.sectionRingEquiv
        (isAffineOpen_centrePreimage i U)).symm (Stacks.ProjectiveCompletion.sectionRingEquiv
          (isAffineOpen_centrePreimage i U) y))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

end ChartEquiv

end Stacks.Chow

end
