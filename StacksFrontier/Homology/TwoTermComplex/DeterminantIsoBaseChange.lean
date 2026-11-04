module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.TwoTermComplex.DeterminantObjectBaseChange
import all StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
import all StacksFrontier.Homology.TwoTermComplex.DeterminantLine
import all StacksFrontier.Homology.TwoTermComplex.DeterminantLine.Homotopy

/-!
# The determinant of an isomorphism, and its compatibility with base change

Let `R` be a commutative ring. The determinant of More on Algebra, Section 0FJI compares the
determinant lines of two two-term finite-projective presentations along an isomorphism of the
presented objects, and that comparison is defined through a span of degreewise-surjective
quasi-isomorphisms, hence computed by nothing in particular. This file computes it in the one
case where it has a closed form, namely along a degreewise *isomorphism* of the presenting
complexes, and records how the determinant of an isomorphism behaves under extension of scalars.

## Main definitions

* `TwoTermDeterminant.degreeEquivOfIso`: the linear equivalence in one degree underlying an
  isomorphism of cochain complexes of modules.
* `TwoTermDeterminant.detIsoEquiv`: **the determinant of an isomorphism of perfect objects of
  Tor-amplitude in `[-1, 0]`**, as a linear equivalence of determinant modules.
* `TwoTermDeterminant.PerfectTwoTermComplex.baseChangeIso`: the base change of an isomorphism of
  perfect two-term objects, with its source and target written as base changes.
* `TwoTermDeterminant.PerfectTwoTermComplex.baseChangeCompIso`: **the base change of a perfect
  two-term object composes**, along a composite of two ring homomorphisms.

## Main results

* `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_eq_arrowCongr` and
  `TwoTermDeterminant.determinantTransport_Q_mapIso`: **the determinant equivalence of a
  degreewise isomorphism of two-term complexes is conjugation by the determinant equivalences of
  its two components**, over a ring and for two-term presentations respectively.
* `TwoTermDeterminant.detIsoEquiv_refl` and `TwoTermDeterminant.detIsoEquiv_trans`: the
  determinant of an isomorphism is functorial.
* `TwoTermDeterminant.PerfectTwoTermComplex.baseChangeCompIso_assoc`: the cocycle condition for
  the composition of base changes.
* `TwoTermDeterminant.detBaseChange_one_tmul_detIsoEquiv` and
  `TwoTermDeterminant.detBaseChange_detIsoEquiv`: **the determinant of an isomorphism commutes
  with flat base change**: the comparison `TwoTermDeterminant.detBaseChange` intertwines the
  determinant of an isomorphism with the determinant of its derived extension of scalars, on the
  elements `1 ⊗ₜ x` and as a commuting square of `A`-linear maps.

## Implementation notes

The determinant line of a two-term complex `K₁ → K₀` is the module of homomorphisms from
`det K₁` to `det K₀`, so conjugation by two determinant equivalences is `LinearEquiv.arrowCongr`
of `ProjectiveDeterminant.mapEquiv` in the two degrees. The components of a degreewise
isomorphism are carried as linear equivalences `α` and `β` together with the hypotheses that they
agree with the two components of the morphism of two-term complexes.

Base change is taken along a ring homomorphism `φ : R →+* A` with the algebra structure
`φ.toAlgebra`, and flatness is a hypothesis stated under that `letI`, as for
`TwoTermDeterminant.detBaseChange`: the statements mention `A ⊗[R] -` and so depend on it.

## References

* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
* [Stacks Project, Tag 0FJM](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

/-! ### The determinant equivalence of a degreewise isomorphism, over a ring -/

namespace TwoTermComplex

section

variable {R : Type*} [CommRing R]

/-- **The exterior algebra of the kernel of an injective map lands in the scalars**: the map
induced by the inclusion of the kernel carries every element into the image of `algebraMap`. -/
theorem exists_algebraMap_map_subtype_of_injective
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f)
    (z : ExteriorAlgebra R (LinearMap.ker f)) :
    ∃ c : R, ExteriorAlgebra.map (LinearMap.ker f).subtype z =
      algebraMap R (ExteriorAlgebra R M) c := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap r => exact ⟨r, AlgHom.commutes _ r⟩
  | ι v =>
      refine ⟨0, ?_⟩
      have hv : (LinearMap.ker f).subtype v = 0 := hf (by rw [map_zero]; exact v.2)
      rw [ExteriorAlgebra.map_apply_ι, hv, map_zero, map_zero]
  | mul a b ha hb =>
      obtain ⟨ca, hca⟩ := ha
      obtain ⟨cb, hcb⟩ := hb
      exact ⟨ca * cb, by rw [map_mul, hca, hcb, map_mul]⟩
  | add a b ha hb =>
      obtain ⟨ca, hca⟩ := ha
      obtain ⟨cb, hcb⟩ := hb
      exact ⟨ca + cb, by rw [map_add, hca, hcb, map_add]⟩

/-- **The determinant equivalence of a surjection that is also an isomorphism.** If the surjection
`f` agrees with a linear equivalence `ε`, and if the determinant of its kernel is described by the
scalar `c` in the sense that the inclusion of the kernel carries it to `algebraMap c`, then the
determinant equivalence of the short exact sequence of the kernel multiplies by `c` after the
determinant of `ε` is undone. -/
theorem kernelDeterminantEquiv_tmul_mapEquiv
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (ε : M ≃ₗ[R] N) (hε : ∀ v, ε v = f v)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
    (w : ProjectiveDeterminant.module (R := R) (M := M)) (c : R)
    (hc : ExteriorAlgebra.map (LinearMap.ker f).subtype
        (x : ExteriorAlgebra R (LinearMap.ker f)) = algebraMap R (ExteriorAlgebra R M) c) :
    kernelDeterminantEquiv f hf (x ⊗ₜ[R] ProjectiveDeterminant.mapEquiv ε w) = c • w := by
  have hεf : ε.toLinearMap = f := LinearMap.ext hε
  have hlift : ExteriorAlgebra.map f (w : ExteriorAlgebra R M) =
      ((determinantAnnihilatorEquiv (ProjectiveDeterminant.mapEquiv ε w) :
          ↥(⨅ n : N, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R n)))) :
        ExteriorAlgebra R N) := by
    rw [determinantAnnihilatorEquiv_val]
    show _ = ExteriorAlgebra.map ε.toLinearMap (w : ExteriorAlgebra R M)
    rw [hεf]
  have hprop := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
      (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
      f.exact_subtype_ker_map hf).property
    (determinantAnnihilatorEquiv x)
    (determinantAnnihilatorEquiv (ProjectiveDeterminant.mapEquiv ε w))
    (w : ExteriorAlgebra R M) hlift
  have hval : ((kernelDeterminantEquiv f hf
          (x ⊗ₜ[R] ProjectiveDeterminant.mapEquiv ε w) :
        ProjectiveDeterminant.module (R := R) (M := M)) : ExteriorAlgebra R M) =
      (((ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
              (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
              f.exact_subtype_ker_map hf).val
            (determinantAnnihilatorEquiv x ⊗ₜ[R]
              determinantAnnihilatorEquiv (ProjectiveDeterminant.mapEquiv ε w)) :
          ↥(⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)))) :
        ExteriorAlgebra R M) :=
    kernelDeterminantEquiv_val f hf x (ProjectiveDeterminant.mapEquiv ε w)
  have hsmul : ((c • w : ProjectiveDeterminant.module (R := R) (M := M)) :
      ExteriorAlgebra R M) = c • (w : ExteriorAlgebra R M) := rfl
  apply Subtype.ext
  rw [hval, hprop, determinantAnnihilatorEquiv_val, hc, hsmul, Algebra.smul_def]

/-- **The determinant equivalence of a degreewise isomorphism of two-term complexes is conjugation
by the determinant equivalences of its two terms.** -/
theorem determinantEquivOfSurjectiveQuasiIso_eq_arrowCongr
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : Hom K L)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (α : K₁ ≃ₗ[R] L₁) (β : K₀ ≃ₗ[R] L₀)
    (hα : ∀ v, α v = a.neg v) (hβ : ∀ v, β v = a.zero v) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    (determinantEquivOfSurjectiveQuasiIso K L a ha hqa).equiv =
      LinearEquiv.arrowCongr (ProjectiveDeterminant.mapEquiv α)
        (ProjectiveDeterminant.mapEquiv β) := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  have hninj : Function.Injective a.neg := by
    intro u v huv
    exact α.injective (by rw [hα u, hα v]; exact huv)
  refine ((determinantEquivOfSurjectiveQuasiIso K L a ha hqa).unique _ ?_).symm
  intro φ x y
  obtain ⟨c, hc⟩ :=
    exists_algebraMap_map_subtype_of_injective a.neg hninj (x : ExteriorAlgebra R _)
  have hsub : (LinearMap.ker a.zero).subtype.comp a.kernelDifferential =
      K.comp (LinearMap.ker a.neg).subtype := LinearMap.ext fun _ => rfl
  have hcz : ∀ hr : IsRankZero a.kernelDifferential,
      ExteriorAlgebra.map (LinearMap.ker a.zero).subtype
          ((delta a.kernelDifferential hr x :
            ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero)) :
            ExteriorAlgebra R (LinearMap.ker a.zero)) =
        algebraMap R (ExteriorAlgebra R K₀) c := by
    intro hr
    have hδ : ((delta a.kernelDifferential hr x :
          ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero)) :
          ExteriorAlgebra R (LinearMap.ker a.zero)) =
        ExteriorAlgebra.map a.kernelDifferential
          (x : ExteriorAlgebra R (LinearMap.ker a.neg)) := rfl
    rw [hδ, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hsub,
      ← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply, hc, AlgHom.commutes]
  obtain ⟨y, rfl⟩ := (ProjectiveDeterminant.mapEquiv α).surjective y
  rw [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply,
    kernelDeterminantEquiv_tmul_mapEquiv a.zero ha.2 β hβ _ (φ y) c (hcz _),
    kernelDeterminantEquiv_tmul_mapEquiv a.neg ha.1 α hα x y c hc, map_smul]

end

end TwoTermComplex

/-! ### The determinant of an isomorphism -/

namespace TwoTermDeterminant

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R]

/-- The linear equivalence in degree `i` underlying an isomorphism of cochain complexes of
modules. -/
abbrev degreeEquivOfIso {C D : CochainComplex (ModuleCat.{u} R) ℤ} (e : C ≅ D) (i : ℤ) :
    C.X i ≃ₗ[R] D.X i :=
  ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso e).toLinearEquiv

/-- **Transport between the determinant lines of two two-term presentations along an isomorphism
represented by a degreewise isomorphism of the presenting complexes is conjugation by the
determinant equivalences of the two terms.** -/
theorem determinantTransport_Q_mapIso {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (e : P.complex ≅ Q.complex) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    letI := Q.finite (-1)
    letI := Q.projective (-1)
    letI := Q.finite 0
    letI := Q.projective 0
    determinantTransport P Q (DerivedCategory.Q.mapIso e) =
      LinearEquiv.arrowCongr
        (ProjectiveDeterminant.mapEquiv (degreeEquivOfIso e (-1)))
        (ProjectiveDeterminant.mapEquiv (degreeEquivOfIso e 0)) := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  let := Q.finite (-1)
  let := Q.projective (-1)
  let := Q.finite 0
  let := Q.projective 0
  have : IsIso (DerivedCategory.Q.map e.hom) := inferInstance
  have hs : (P.hom Q e.hom).IsDegreewiseSurjective :=
    ⟨(degreeEquivOfIso e (-1)).surjective, (degreeEquivOfIso e 0).surjective⟩
  have hiso : DerivedCategory.Q.mapIso e = asIso (DerivedCategory.Q.map e.hom) := Iso.ext rfl
  rw [hiso, determinantTransport_eq_of_surjective P Q e.hom hs]
  exact TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_eq_arrowCongr
    (P.complex.d (-1) 0).hom (Q.complex.d (-1) 0).hom (P.hom Q e.hom) hs
    (twoTerm_quasiIso_of_isIso_Q_map P Q e.hom)
    (degreeEquivOfIso e (-1)) (degreeEquivOfIso e 0) (fun _ => rfl) (fun _ => rfl)

/-- **The determinant of an isomorphism of perfect objects of Tor-amplitude in `[-1, 0]`**, as a
linear equivalence of determinant modules: the value of `TwoTermDeterminant.det` at the
isomorphism, read through the inclusion of the full subcategory of invertible modules. -/
def detIsoEquiv {K K' : PerfectTwoTermComplex R} (e : K.obj ≅ K'.obj) :
    ((det R).obj ⟨K⟩).of.obj ≃ₗ[R] ((det R).obj ⟨K'⟩).of.obj :=
  ((invertibleModuleProperty R).ι.mapIso
    ((det R).map (⟨ObjectProperty.isoMk (perfectTwoTermComplexProperty R) e⟩ :
      (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨K'⟩)).iso).toLinearEquiv

/-- An isomorphism of perfect objects of Tor-amplitude in `[-1, 0]`, promoted to the full
subcategory and read back in the derived category, is itself. -/
theorem ι_mapIso_isoMk {K K' : PerfectTwoTermComplex R} (e : K.obj ≅ K'.obj) :
    (perfectTwoTermComplexProperty R).ι.mapIso
      (ObjectProperty.isoMk (perfectTwoTermComplexProperty R) e) = e :=
  Iso.ext rfl

/-- The determinant of an isomorphism is the transport between the determinant lines of the
chosen presentations of its source and target. -/
theorem detIsoEquiv_eq {K K' : PerfectTwoTermComplex R} (e : K.obj ≅ K'.obj) :
    detIsoEquiv e = presentationTransport (presentation R K) (presentation R K') e := by
  show presentationTransport (presentation R K) (presentation R K')
    ((perfectTwoTermComplexProperty R).ι.mapIso
      (ObjectProperty.isoMk (perfectTwoTermComplexProperty R) e)) = _
  rw [ι_mapIso_isoMk]

/-- **The determinant of the identity isomorphism is the identity.** -/
theorem detIsoEquiv_refl {K : PerfectTwoTermComplex R} :
    detIsoEquiv (Iso.refl K.obj) = LinearEquiv.refl R ((det R).obj ⟨K⟩).of.obj :=
  (detIsoEquiv_eq (Iso.refl K.obj)).trans (presentationTransport_id (presentation R K))

/-- **The determinant of a composite of isomorphisms is the composite of the determinants.** -/
theorem detIsoEquiv_trans {K K' K'' : PerfectTwoTermComplex R} (e : K.obj ≅ K'.obj)
    (e' : K'.obj ≅ K''.obj) :
    detIsoEquiv (e ≪≫ e') = (detIsoEquiv e).trans (detIsoEquiv e') := by
  refine LinearEquiv.ext fun x => ?_
  show detIsoEquiv (e ≪≫ e') x = detIsoEquiv e' (detIsoEquiv e x)
  refine (DFunLike.congr_fun (detIsoEquiv_eq (e ≪≫ e')) x).trans ?_
  refine (DFunLike.congr_fun (presentationTransport_comp (presentation R K)
    (presentation R K') (presentation R K'') e e') x).symm.trans ?_
  refine (congrArg (fun z => presentationTransport (presentation R K')
    (presentation R K'') e' z) (DFunLike.congr_fun (detIsoEquiv_eq e) x).symm).trans ?_
  exact (DFunLike.congr_fun (detIsoEquiv_eq e') (detIsoEquiv e x)).symm

end

/-! ### The base change of a perfect two-term object composes -/

section

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] {B : Type u} [CommRing B]
variable {C : Type u} [CommRing C]

/-- **The base change of an isomorphism of perfect objects of Tor-amplitude in `[-1, 0]`**: its
derived extension of scalars, with source and target written as the base changes of the source and
the target. -/
def PerfectTwoTermComplex.baseChangeIso (φ : R →+* A) {K K' : PerfectTwoTermComplex R}
    (e : K.obj ≅ K'.obj) :
    (PerfectTwoTermComplex.baseChange φ K).obj ≅ (PerfectTwoTermComplex.baseChange φ K').obj :=
  (totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso e

/-- **The base change of a perfect object of Tor-amplitude in `[-1, 0]` composes.** Extending
scalars along `φ : R →+* A` and then along `ψ : A →+* B` is extending scalars along `ψ.comp φ`:
this is `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` at the
underlying derived object. -/
def PerfectTwoTermComplex.baseChangeCompIso (φ : R →+* A) (ψ : A →+* B)
    (K : PerfectTwoTermComplex R) :
    (PerfectTwoTermComplex.baseChange ψ (PerfectTwoTermComplex.baseChange φ K)).obj ≅
      (PerfectTwoTermComplex.baseChange (ψ.comp φ) K).obj :=
  (totalDerivedExtensionScalarsComp.{u, u} φ ψ).app K.obj

/-- **The cocycle condition for the composition of base changes.** The two ways of comparing a
threefold base change with the base change along the composite of the three ring homomorphisms
agree. -/
theorem PerfectTwoTermComplex.baseChangeCompIso_assoc (φ : R →+* A) (ψ : A →+* B) (χ : B →+* C)
    (K : PerfectTwoTermComplex R) :
    (totalDerivedExtensionScalars.{u, u, u} χ).functor.map
          (PerfectTwoTermComplex.baseChangeCompIso φ ψ K).hom ≫
        (PerfectTwoTermComplex.baseChangeCompIso (ψ.comp φ) χ K).hom =
      (PerfectTwoTermComplex.baseChangeCompIso ψ χ
            (PerfectTwoTermComplex.baseChange φ K)).hom ≫
        (PerfectTwoTermComplex.baseChangeCompIso φ (χ.comp ψ) K).hom :=
  totalDerivedExtensionScalarsComp_assoc.{u, u} φ ψ χ K.obj

end

/-! ### The determinant of an isomorphism commutes with base change -/

section

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] (φ : R →+* A)

/-- **The determinant of an isomorphism commutes with flat base change, on the elements
`1 ⊗ₜ x`.** -/
theorem detBaseChange_one_tmul_detIsoEquiv
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    {K K' : PerfectTwoTermComplex R} (e : K.obj ≅ K'.obj)
    (x : presentationDeterminant (presentation R K)) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    detIsoEquiv (PerfectTwoTermComplex.baseChangeIso φ e)
        (detBaseChange φ hφ K (1 ⊗ₜ[R] x)) =
      detBaseChange φ hφ K'
        (LinearMap.baseChange A (detIsoEquiv e).toLinearMap (1 ⊗ₜ[R] x)) := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  have hdb : ∀ (M : PerfectTwoTermComplex R) (z : A ⊗[R] presentationDeterminant
        (presentation R M)),
      detBaseChange φ hφ M z = presentationTransport ((presentation R M).baseChange φ)
        (presentation A (PerfectTwoTermComplex.baseChange φ M)) (Iso.refl _)
        (presentationDeterminantBaseChange φ hφ (presentation R M) z) := fun _ _ => rfl
  have hkey := LinearMap.congr_fun
    (presentationTransport_baseChange φ hφ (presentation R K) (presentation R K') e)
    (1 ⊗ₜ[R] x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul] at hkey
  have hleft := (presentationTransport_comp ((presentation R K).baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K))
      (presentation A (PerfectTwoTermComplex.baseChange φ K')) (Iso.refl _)
      (PerfectTwoTermComplex.baseChangeIso φ e)).trans
    (congrArg (fun c => presentationTransport ((presentation R K).baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K')) c)
      (Iso.refl_trans (PerfectTwoTermComplex.baseChangeIso φ e)))
  have hright := (presentationTransport_comp ((presentation R K).baseChange φ)
      ((presentation R K').baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K'))
      ((totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso e) (Iso.refl _)).trans
    (congrArg (fun c => presentationTransport ((presentation R K).baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K')) c)
      (Iso.trans_refl ((totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso e)))
  have htmul : LinearMap.baseChange A (detIsoEquiv e).toLinearMap (1 ⊗ₜ[R] x) =
      (1 : A) ⊗ₜ[R] presentationTransport (presentation R K) (presentation R K') e x :=
    congrArg (fun z => (1 : A) ⊗ₜ[R] z) (DFunLike.congr_fun (detIsoEquiv_eq e) x)
  have hL : detIsoEquiv (PerfectTwoTermComplex.baseChangeIso φ e)
        (detBaseChange φ hφ K (1 ⊗ₜ[R] x)) =
      presentationTransport ((presentation R K).baseChange φ)
        (presentation A (PerfectTwoTermComplex.baseChange φ K'))
        (PerfectTwoTermComplex.baseChangeIso φ e)
        (presentationDeterminantBaseChange φ hφ (presentation R K) (1 ⊗ₜ[R] x)) := by
    refine (DFunLike.congr_fun (detIsoEquiv_eq (PerfectTwoTermComplex.baseChangeIso φ e))
      (detBaseChange φ hφ K (1 ⊗ₜ[R] x))).trans ?_
    refine (congrArg (fun z => presentationTransport
      (presentation A (PerfectTwoTermComplex.baseChange φ K))
      (presentation A (PerfectTwoTermComplex.baseChange φ K'))
      (PerfectTwoTermComplex.baseChangeIso φ e) z) (hdb K (1 ⊗ₜ[R] x))).trans ?_
    exact DFunLike.congr_fun hleft _
  have hR : detBaseChange φ hφ K'
        (LinearMap.baseChange A (detIsoEquiv e).toLinearMap (1 ⊗ₜ[R] x)) =
      presentationTransport ((presentation R K).baseChange φ)
        (presentation A (PerfectTwoTermComplex.baseChange φ K'))
        (PerfectTwoTermComplex.baseChangeIso φ e)
        (presentationDeterminantBaseChange φ hφ (presentation R K) (1 ⊗ₜ[R] x)) := by
    refine (congrArg (fun z => detBaseChange φ hφ K' z) htmul).trans ?_
    refine (hdb K' (1 ⊗ₜ[R]
      presentationTransport (presentation R K) (presentation R K') e x)).trans ?_
    refine (congrArg (fun z => presentationTransport ((presentation R K').baseChange φ)
      (presentation A (PerfectTwoTermComplex.baseChange φ K')) (Iso.refl _) z) hkey.symm).trans ?_
    exact DFunLike.congr_fun hright _
  exact hL.trans hR.symm

/-- **The determinant of an isomorphism commutes with flat base change.** For a flat
`φ : R →+* A` and an isomorphism `e` of perfect objects of Tor-amplitude in `[-1, 0]` over `R`,
the comparison `TwoTermDeterminant.detBaseChange` intertwines the determinant of `e` with the
determinant of the derived extension of scalars of `e`. -/
theorem detBaseChange_detIsoEquiv (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    {K K' : PerfectTwoTermComplex R} (e : K.obj ≅ K'.obj) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    (detIsoEquiv (PerfectTwoTermComplex.baseChangeIso φ e)).toLinearMap ∘ₗ
        (detBaseChange φ hφ K).toLinearMap =
      (detBaseChange φ hφ K').toLinearMap ∘ₗ
        LinearMap.baseChange A (detIsoEquiv e).toLinearMap := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  refine LinearMap.ext fun t => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b x =>
      have hsm : (b ⊗ₜ[R] x : A ⊗[R] ((det R).obj ⟨K⟩).of.obj) = b • (1 ⊗ₜ[R] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [hsm, map_smul]
      exact congrArg (fun z => b • z) (detBaseChange_one_tmul_detIsoEquiv φ hφ e x)
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end

end TwoTermDeterminant

end
