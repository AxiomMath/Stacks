module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelianVarietyOfRationalSurjection
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.FamilyOfRationalPoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RepresentedPicardZero
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.HilbertChart

/-!
# The Abel morphism from a fibre power of a curve

Let `f : X ⟶ S` be a proper smooth relative curve with a section `σ`. On `X ×_S X^n` the
divisor `Γ_{pr₁} + ⋯ + Γ_{prₙ} - n σ` has degree zero on every fibre; rigidified along `σ` its
class lies in `Pic⁰_{X/S,σ}(X^n)`, so a group scheme `A` representing `Pic⁰_{X/S,σ}` receives
the Abel morphism `X^n ⟶ A`. Over an algebraically closed field and for `n` the genus this
morphism hits every rational point of `A`.

## Main definitions

* `Stacks.RigidifiedPicard.abelPowerClass`: the rigidified class of the divisor above.
* `Stacks.RigidifiedPicard.abelPowerHom`: the Abel morphism `X^n ⟶ A`.

## Main results

* `Stacks.RigidifiedPicard.representedClass_comp_abelPowerHom`: on a rational point
  `(x₁, …, xₙ)` the Abel morphism is the class of `𝒪(x₁ + ⋯ + xₙ - n σ)`.
* `Stacks.RigidifiedPicard.exists_comp_abelPowerHom_eq`: every rational point of `A` is the
  image of a rational point of `X^g`.
* `Stacks.RigidifiedPicard.isProper_fibrePower_hom`: fibre powers of proper schemes are proper.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.RigidifiedPicard

/-- Pullback of Picard classes along `g` preserves subtraction. -/
theorem schemePullbackClass_sub' {Y Z : Scheme.{u}} (g : Y ⟶ Z) (a b : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass g (a - b) =
      Stacks.Picard.schemePullbackClass g a - Stacks.Picard.schemePullbackClass g b :=
  map_sub (Stacks.Picard.schemePullbackClassHom g) a b

/-- Pullback of Picard classes along `g` commutes with integer multiples. -/
theorem schemePullbackClass_zsmul' {Y Z : Scheme.{u}} (g : Y ⟶ Z) (n : ℤ)
    (a : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass g (n • a) = n • Stacks.Picard.schemePullbackClass g a :=
  map_zsmul (Stacks.Picard.schemePullbackClassHom g) n a

/-- Pullback of Picard classes along `g` preserves zero. -/
private theorem schemePullbackClass_zero_aux {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    Stacks.Picard.schemePullbackClass g (0 : Stacks.Picard.ofScheme Z) = 0 :=
  map_zero (Stacks.Picard.schemePullbackClassHom g)

/-- A Picard class pulled back from the base `T` has degree zero on every fibre of `π`. -/
theorem relativeInvertibleDegreeHomAt_schemePullbackClass_self {Y T : Scheme.{u}} (π : Y ⟶ T)
    [IsProper π] (hdim : ∀ t : T, topologicalKrullDim ↥(π.fiber t) ≤ 1) (t : T)
    (c : Stacks.Picard.ofScheme T) :
    relativeInvertibleDegreeHomAt π hdim t (Stacks.Picard.schemePullbackClass π c) = 0 := by
  rw [relativeInvertibleDegreeHomAt_apply, Stacks.Picard.schemePullbackClass_comp]
  have hc : π.fiberι t ≫ π = π.fiberToSpecResidueField t ≫ T.fromSpecResidueField t :=
    pullback.condition
  rw [hc, ← Stacks.Picard.schemePullbackClass_comp,
    eq_zero_of_subsingleton (Stacks.Picard.schemePullbackClass (T.fromSpecResidueField t) c),
    schemePullbackClass_zero_aux]
  exact map_zero _

section Classes

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The section `σ`, as a relative point `T ⟶ X` of an `S`-scheme `T`. -/
abbrev sectionPoint (T : Over S) : T ⟶ Over.mk f :=
  Over.homMk (T.hom ≫ σ) (by simp [hσ])

variable [IsProper f] [LocallyOfFiniteType f]
  (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1)

/-- Normalizing a class along the section `σ` does not change its degree on any fibre. -/
theorem relativeInvertibleDegreeHomAt_normalize (T : Over S) (c : Stacks.Picard.ofScheme (bc f T))
    (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
        (normalize f σ hσ T c) =
      relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
        c := by
  rw [normalize, map_sub, relativeInvertibleDegreeHomAt_schemePullbackClass_self, sub_zero]

end Classes

/-! ### The Abel morphism from a fibre power -/

section Abel

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The structure morphism of `Over.mk f` is smooth of relative dimension `1`. -/
instance smoothOfRelativeDimension_overMk : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
  inferInstanceAs (SmoothOfRelativeDimension 1 f)

/-- The structure morphism of `Over.mk f` is separated. -/
instance isSeparated_overMk : IsSeparated (Over.mk f).hom :=
  inferInstanceAs (IsSeparated f)

/-- The fibre power `X^n = X ×_S ⋯ ×_S X`. -/
abbrev fibrePower (n : ℕ) : Over S := ∏ᶜ fun _ : Fin n => Over.mk f

/-- **The Abel class of the fibre power**: the rigidified class of
`𝒪(Γ_{pr₁} + ⋯ + Γ_{prₙ}) ⊗ 𝒪(n · σ)⁻¹` on `X ×_S X^n`. -/
def abelPowerClass (n : ℕ) : Stacks.Picard.ofScheme (bc f (fibrePower f n)) :=
  normalize f σ hσ (fibrePower f n)
    (Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) (fibrePower f n)
        fun i => Pi.π (fun _ : Fin n => Over.mk f) i) -
      Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) (fibrePower f n)
        fun _ : Fin n => sectionPoint f σ hσ (fibrePower f n)))

include hdim in
/-- The Abel class `𝒪(Γ_{x₁} + ⋯ + Γ_{xₙ})` of `n` relative points has degree `n` on every
fibre. -/
theorem relativeInvertibleDegreeHomAt_abelClass_familyOfPoints (T : Over S) {n : ℕ}
    (x : Fin n → (T ⟶ Over.mk f)) (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
      (Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) T x)) = n := by
  have : IsProper ((Over.pullback T.hom).obj (Over.mk f)).hom := isProper_bcProj f T
  exact @Stacks.Hilbert.relativeInvertibleDegreeHomAt_abelClass S (Over.mk f)
    (smoothOfRelativeDimension_overMk f) n T (Stacks.Hilbert.familyOfPoints (Over.mk f) T x) this
    (topologicalKrullDim_fiber_bcProj_le f hdim T) t

/-- The Abel class of the fibre power is rigidified along `σ`. -/
theorem abelPowerClass_mem_group (n : ℕ) :
    (smallEquiv (bc f (fibrePower f n))).symm (abelPowerClass f σ hσ n) ∈
      group f σ hσ (fibrePower f n) := by
  rw [mem_group_iff, AddEquiv.apply_symm_apply, abelPowerClass, normalize,
    schemePullbackClass_sub', schemePullbackClass_bcSection_bcProj, sub_self]

/-- The Abel class of the fibre power has degree zero on every fibre. -/
theorem abelPowerClass_mem_groupZero (n : ℕ) :
    (⟨_, abelPowerClass_mem_group f σ hσ n⟩ : group f σ hσ (fibrePower f n)) ∈
      groupZero f hdim σ hσ (fibrePower f n) := by
  rw [mem_groupZero_iff]
  intro t
  rw [degree_apply]
  show relativeInvertibleDegreeHomAt _ _ t
    ((smallEquiv (bc f (fibrePower f n)))
      ((smallEquiv (bc f (fibrePower f n))).symm (abelPowerClass f σ hσ n))) = 0
  rw [AddEquiv.apply_symm_apply, abelPowerClass,
    relativeInvertibleDegreeHomAt_normalize f σ hσ hdim, map_sub,
    relativeInvertibleDegreeHomAt_abelClass_familyOfPoints f hdim,
    relativeInvertibleDegreeHomAt_abelClass_familyOfPoints f hdim, sub_self]

omit [IsProper f] [SmoothOfRelativeDimension 1 f] in
/-- The section point is compatible with morphisms of `S`-schemes: `y ≫ σ_T = σ_{T'}`. -/
theorem comp_sectionPoint {T' T : Over S} (y : T' ⟶ T) :
    y ≫ sectionPoint f σ hσ T = sectionPoint f σ hσ T' := by
  ext
  simp [Over.w_assoc y]

/-- Base change of the Abel class of `n` relative points along `g` is the Abel class of the
composed points. -/
private theorem schemePullbackClass_abelClass_familyOfPoints {T' T : Over S} (g : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ Over.mk f)) :
    Stacks.Picard.schemePullbackClass (bcMap f g)
        (Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) T x)) =
      Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) T' fun i => g ≫ x i) := by
  have := Stacks.Hilbert.abelClass_baseChange g (Stacks.Hilbert.familyOfPoints (Over.mk f) T x)
  rwa [Stacks.Hilbert.baseChange_familyOfPoints] at this

/-- **The Abel class at a point with trivial Picard group.** If the Picard group of `T` is
trivial, the pullback of the Abel class along `y = (x₁, …, xₙ) : T ⟶ X^n` is
`[𝒪(Γ_{x₁} + ⋯ + Γ_{xₙ})] - [𝒪(n · σ_T)]`. -/
theorem schemePullbackClass_bcMap_abelPowerClass {T : Over S} [Subsingleton T.left]
    [Nonempty T.left] (n : ℕ) (y : T ⟶ fibrePower f n) :
    Stacks.Picard.schemePullbackClass (bcMap f y) (abelPowerClass f σ hσ n) =
      Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) T
          fun i => y ≫ Pi.π (fun _ : Fin n => Over.mk f) i) -
        Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) T
          fun _ : Fin n => sectionPoint f σ hσ T) := by
  rw [abelPowerClass, normalize, schemePullbackClass_sub', schemePullbackClass_sub',
    schemePullbackClass_bcProj_natural,
    eq_zero_of_subsingleton (Stacks.Picard.schemePullbackClass y.left _),
    schemePullbackClass_zero_aux, sub_zero]
  have h1 := schemePullbackClass_abelClass_familyOfPoints f y
    fun i => Pi.π (fun _ : Fin n => Over.mk f) i
  have h2 := schemePullbackClass_abelClass_familyOfPoints f y
    fun _ : Fin n => sectionPoint f σ hσ (fibrePower f n)
  simp only [comp_sectionPoint] at h2
  exact congrArg₂ (· - ·) h1 h2

end Abel

/-! ### The fibre power -/

/-- The fibre power of a proper `S`-scheme is proper over `S`. -/
theorem isProper_fibrePower_hom {S : Scheme.{u}} (Y : Over S) [IsProper Y.hom] (n : ℕ) :
    IsProper (∏ᶜ fun _ : Fin n => Y).hom := by
  induction n with
  | zero =>
    have := Stacks.Scheme.isIso_fibrePower_zero_hom Y
    infer_instance
  | succ n ih =>
    have h : (∏ᶜ fun _ : Fin (n + 1) => Y).hom = (Stacks.Scheme.fibrePowerSuccIso Y n).hom.left ≫
        ((∏ᶜ fun _ : Fin n => Y) ⨯ Y).hom := (Over.w _).symm
    have : IsIso (Stacks.Scheme.fibrePowerSuccIso Y n).hom.left := (Over.forget S).map_isIso _
    rw [h, Stacks.Scheme.prod_hom_eq]
    infer_instance

/-! ### Over an algebraically closed field -/

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
  [IsProper f] [SmoothOfRelativeDimension 1 f]
  (hdim : ∀ s : Spec (.of K), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  {A : Grp (Over (Spec (.of K)))} (e : CategoryTheory.yonedaGrp.obj A ≅ functorZero f hdim σ hσ)

/-- The spectrum of a field has at most one point. -/
instance : Subsingleton (Stacks.Hilbert.fieldPoint K).left :=
  inferInstanceAs (Subsingleton (Spec (.of K)))

/-- The spectrum of a field is nonempty. -/
instance : Nonempty (Stacks.Hilbert.fieldPoint K).left :=
  inferInstanceAs (Nonempty (Spec (.of K)))

/-- **The Abel morphism `X^n ⟶ A`**: the morphism classifying the Abel class of the fibre
power. On a rational point `(x₁, …, xₙ)` it is the class of `𝒪(x₁ + ⋯ + xₙ - n σ)`. -/
def abelPowerHom (n : ℕ) : fibrePower f n ⟶ A.X :=
  classifyingHom f hdim σ hσ e _ (abelPowerClass_mem_groupZero f hdim σ hσ n)

omit [IsAlgClosed K] in
/-- On a rational point `y = (x₁, …, xₙ)` of `X^n`, the class represented by the Abel morphism is
`[𝒪(x₁ + ⋯ + xₙ)] - [𝒪(n · σ)]`. -/
theorem representedClass_comp_abelPowerHom (n : ℕ)
    (y : Stacks.Hilbert.fieldPoint K ⟶ fibrePower f n) :
    representedClass f hdim σ hσ e (y ≫ abelPowerHom f hdim σ hσ e n) =
      Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) _
          fun i => y ≫ Pi.π (fun _ : Fin n => Over.mk f) i) -
        Stacks.Hilbert.abelClass (Stacks.Hilbert.familyOfPoints (Over.mk f) _
          fun _ : Fin n => sectionPoint f σ hσ (Stacks.Hilbert.fieldPoint K)) := by
  rw [representedClass_comp, abelPowerHom, representedClass_classifyingHom,
    AddEquiv.apply_symm_apply]
  exact schemePullbackClass_bcMap_abelPowerClass f σ hσ n y

/-- **The Abel morphism of large degree hits every rational point.** If `n` is the genus of `X`
(read on the base change `X_k = X ×_k k`), every rational point of `A` is the image of a rational
point of `X^n` under the Abel morphism. -/
theorem exists_comp_abelPowerHom_eq [IsIntegral (bc f (Stacks.Hilbert.fieldPoint K))]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (bcProj f (Stacks.Hilbert.fieldPoint K)).appTop)]
    (hdim₀ : topologicalKrullDim (bc f (Stacks.Hilbert.fieldPoint K)) ≤ 1)
    (a : Stacks.Hilbert.fieldPoint K ⟶ A.X) :
    ∃ y : Stacks.Hilbert.fieldPoint K ⟶
        fibrePower f (genus (bcProj f (Stacks.Hilbert.fieldPoint K))),
      y ≫ abelPowerHom f hdim σ hσ e _ = a := by
  set π₀ : bc f (Stacks.Hilbert.fieldPoint K) ⟶ Spec (.of K) :=
    bcProj f (Stacks.Hilbert.fieldPoint K)
  set n := genus π₀
  have hdim' := topologicalKrullDim_fiber_bcProj_le f hdim (Stacks.Hilbert.fieldPoint K)
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (.of K)))
  set c := representedClass f hdim σ hσ e a
  have hc : invertibleCurveDegreeHom K π₀ hdim₀ c = 0 := by
    obtain ⟨x, hx, hxc⟩ := representedClass_mem_groupZero f hdim σ hσ e a
    have h := (mem_groupZero_iff f hdim σ hσ (Stacks.Hilbert.fieldPoint K) x).1 hx t
    rw [degree_apply, hxc] at h
    rwa [relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom π₀ hdim' hdim₀] at h
  set E : Stacks.Picard.ofScheme (bc f (Stacks.Hilbert.fieldPoint K)) :=
    Stacks.Hilbert.abelClass
      (Stacks.Hilbert.familyOfPoints (Over.mk f) (Stacks.Hilbert.fieldPoint K)
      fun _ : Fin n => sectionPoint f σ hσ (Stacks.Hilbert.fieldPoint K))
  have hE : invertibleCurveDegreeHom K π₀ hdim₀ E = n := by
    rw [← relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom π₀ hdim' hdim₀ t]
    exact relativeInvertibleDegreeHomAt_abelClass_familyOfPoints f hdim
      (Stacks.Hilbert.fieldPoint K) _ t
  have hdeg : (genus π₀ : ℤ) ≤ invertibleCurveDegreeHom K π₀ hdim₀ (c + E) := by
    rw [map_add, hc, hE, zero_add]
  obtain ⟨D, hD, d, hrank, hd, hclass⟩ :=
    exists_isEffectiveCartierDivisor_picardClass_eq K π₀ hdim₀ (c + E) hdeg
  have hdn : d = n := by
    rw [map_add, hc, hE, zero_add] at hd
    exact_mod_cast hd
  let Z : Stacks.Hilbert.HilbertFamily (Over.mk f) (Stacks.Hilbert.fieldPoint K) n :=
    ⟨D, hdn ▸ hrank⟩
  obtain ⟨x, hx⟩ := Stacks.Hilbert.exists_familyOfPoints_eq (Over.mk f) n Z
  refine ⟨Pi.lift x, (representedClass_injective f hdim σ hσ e (Stacks.Hilbert.fieldPoint K)) ?_⟩
  rw [representedClass_comp_abelPowerHom]
  simp only [Pi.lift_π]
  rw [hx, show Stacks.Hilbert.abelClass Z = c + E from hclass]
  exact add_sub_cancel_right c E

end AlgClosed

end Stacks.RigidifiedPicard
