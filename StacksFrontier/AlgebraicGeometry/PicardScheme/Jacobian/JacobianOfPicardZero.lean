module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.JacobianParametrization
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsCurveJacobian
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Jacobian of a curve over an algebraically closed field, from a representation of `Pic⁰`

Let `X` be a proper smooth geometrically irreducible curve over an algebraically closed field
`K` with a rational point `σ`, and let `A` be a smooth group scheme over `K` representing the
degree-zero rigidified Picard functor `Pic⁰_{X/K,σ}`. Then `A` is an abelian variety and its
rational points parametrize the degree-zero Picard classes of `X`, compatibly with
multiplication by every integer. This is the input
`Stacks.WeilCohomology.JacobianParametrization` of the curve case of [Stacks, Tag 0FH7].

## Main results

* `Stacks.RigidifiedPicard.isAbelianVariety_of_iso_functorZero`: `A` is an abelian variety.
* `Stacks.RigidifiedPicard.exists_pointClass_eq`: every degree-zero class is the class of a
  rational point of `A`.
* `Stacks.RigidifiedPicard.pointClass_eq_zsmul`: multiplication by `n` on `A` is
  multiplication by `n` on classes.
* `Stacks.WeilCohomology.jacobianParametrization_of_iso_functorZero`: the Jacobian input.

## Implementation notes

The representation of `Pic⁰_{X/K,σ}` (Stacks Tags 0B9Z and 0BA0 (3)) is the hypothesis `e`; it
is what [Stacks, Tag 0B9Q] produces from the open subfunctor of [Stacks, Tag 0B9X]. Properness
and connectedness of `A` are not assumed: they follow because the Abel morphism from the proper
connected scheme `X^g` hits every rational point of `A`, by Riemann-Roch.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.RigidifiedPicard

-- The Stacks 0682, 0695 and 068A instances (pseudo-coherent and perfect morphisms) reach this file
-- through the derived direct image of a proper flat family; they are not needed here and are
-- erased so that instance search over `f` resolves as it does without them.
attribute [-instance] AlgebraicGeometry.locallyOfFinitePresentation_of_pseudoCoherent
  AlgebraicGeometry.pseudoCoherent_of_flat_of_locallyOfFinitePresentation
  AlgebraicGeometry.perfect_of_flat_of_locallyOfFinitePresentation

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
  [IsProper f] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
  (hdimX : topologicalKrullDim X ≤ 1)
  (hdim : ∀ s : Spec (.of K), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  {A : Grp (Over (Spec (.of K)))} (e : CategoryTheory.yonedaGrp.obj A ≅ functorZero f hdim σ hσ)

omit [IsAlgClosed K] [IsProper f] [SmoothOfRelativeDimension 1 f] in
/-- A smooth geometrically irreducible morphism to the spectrum of a field is geometrically
integral, being geometrically reduced. -/
theorem geometricallyIntegral_of_smooth : GeometricallyIntegral f :=
  have := geometricallyReduced_of_smooth f
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

/-- The base change `X ×_K K` of `X` along `Stacks.Hilbert.fieldPoint K` is an integral
scheme. -/
instance isIntegral_bc_fieldPoint : IsIntegral (bc f (Stacks.Hilbert.fieldPoint K)) := by
  have := geometricallyIntegral_of_smooth f
  have : GeometricallyIntegral (bcProj f (Stacks.Hilbert.fieldPoint K)) :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd f (𝟙 _)))
  have : Subsingleton (Stacks.Hilbert.fieldPoint K).left :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  have : IsIntegral (Stacks.Hilbert.fieldPoint K).left :=
    inferInstanceAs (IsIntegral (Spec (.of K)))
  exact GeometricallyIntegral.isIntegral_of_subsingleton (bcProj f (Stacks.Hilbert.fieldPoint K))

/-- The base change `X ×_K K` of `X` along `Stacks.Hilbert.fieldPoint K` has global sections
`K`: the structure map `K ⟶ Γ(X ×_K K)` is an isomorphism. -/
instance isIso_globalSections_bc_fieldPoint :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (bcProj f (Stacks.Hilbert.fieldPoint K)).appTop) := by
  have := geometricallyIntegral_of_smooth f
  have : GeometricallyIntegral (bcProj f (Stacks.Hilbert.fieldPoint K)) :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd f (𝟙 _)))
  exact isIso_globalSections_of_geometricallyIntegral K _

omit [IsAlgClosed K] [IsProper f] [Smooth f] [GeometricallyIrreducible f]
  [SmoothOfRelativeDimension 1 f] in
include hdimX in
/-- The base change `X ×_K K` of `X` along `Stacks.Hilbert.fieldPoint K` has dimension at most
one, being isomorphic to `X`. -/
theorem topologicalKrullDim_bc_fieldPoint_le :
    topologicalKrullDim (bc f (Stacks.Hilbert.fieldPoint K)) ≤ 1 := by
  have : IsIso (pullback.fst f (𝟙 (Spec (.of K)))) := inferInstance
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (asIso (pullback.fst f (𝟙 (Spec (.of K))))).hom.homeomorph.isHomeomorph).trans_le hdimX

include e hdimX in
/-- **`Pic⁰` of a smooth proper curve over an algebraically closed field is an abelian
variety.** Let `X` be a proper smooth geometrically irreducible curve over an algebraically
closed field `K` with a rational point `σ`, and let `A` be a group scheme over `K`, smooth over
`K`, representing the degree-zero rigidified Picard functor `Pic⁰_{X/K,σ}`. Then `A` is an
abelian variety.

The Abel morphism `X^g ⟶ A`, `(x₁, …, x_g) ↦ 𝒪(x₁ + ⋯ + x_g - g σ)` with `g` the genus, hits
every rational point of `A` (`exists_comp_abelPowerHom_eq`, by Riemann-Roch and the
decomposition of a divisor into rational points), and `X^g` is proper and connected, so `A` is
proper and connected; it is geometrically reduced because it is smooth. -/
@[sga "6 XII 1.2" "special case"]
theorem isAbelianVariety_of_iso_functorZero [Smooth A.X.hom] :
    AlgebraicGeometry.IsAbelianVariety K A.X := by
  set n := genus (bcProj f (Stacks.Hilbert.fieldPoint K))
  have : IsProper (fibrePower f n).hom :=
    @isProper_fibrePower_hom _ _ (inferInstanceAs (IsProper f)) n
  have : Smooth (Over.mk f).hom := inferInstanceAs (Smooth f)
  have : GeometricallyIrreducible (Over.mk f).hom := inferInstanceAs (GeometricallyIrreducible f)
  have : IsIntegral (fibrePower f n).left := Stacks.Scheme.isIntegral_fibrePower (Over.mk f) n
  refine isAbelianVariety_of_forall_rationalPoint_lift A (fibrePower f n).hom
    (abelPowerHom f hdim σ hσ e n).left (Over.w _) fun a ha => ?_
  obtain ⟨y, hy⟩ := exists_comp_abelPowerHom_eq f hdim σ hσ e
    (topologicalKrullDim_bc_fieldPoint_le f hdimX) (Over.homMk a ha)
  exact ⟨y.left, congrArg Over.Hom.left hy⟩

/-- The identification `X ≅ X ×_K K`, as the morphism `X ⟶ X_K`. -/
abbrev toBcFieldPoint : X ⟶ bc f (Stacks.Hilbert.fieldPoint K) :=
  pullback.lift (𝟙 X) f (by simp)

open Classical in
/-- **The Picard class of a rational point of `A`**, through the representation `e`: the class
on `X` of the invertible module classified by the point. -/
def pointClass (g : Spec (.of K) ⟶ A.X.left) : Stacks.Picard.ofScheme X :=
  if h : g ≫ A.X.hom = 𝟙 _ then
    Stacks.Picard.schemePullbackClass (toBcFieldPoint f)
      (representedClass f hdim σ hσ e (Over.homMk g h : Stacks.Hilbert.fieldPoint K ⟶ A.X))
  else 0

omit [IsAlgClosed K] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
include hdimX in
/-- Every Picard class of degree zero on `X` is the class of a rational point of `A`. -/
theorem exists_pointClass_eq (c : Stacks.Picard.ofScheme X)
    (hc : invertibleCurveDegreeHom K f hdimX c = 0) :
    ∃ g : Spec (.of K) ⟶ A.X.left, g ≫ A.X.hom = 𝟙 _ ∧ pointClass f hdim σ hσ e g = c := by
  set p := pullback.fst f (𝟙 (Spec (.of K)))
  have hdim₀ := topologicalKrullDim_bc_fieldPoint_le f hdimX
  set c' : Stacks.Picard.ofScheme (bc f (Stacks.Hilbert.fieldPoint K)) :=
    Stacks.Picard.schemePullbackClass p c
  have hmem : (smallEquiv (bc f (Stacks.Hilbert.fieldPoint K))).symm c' ∈
      group f σ hσ (Stacks.Hilbert.fieldPoint K) := by
    rw [mem_group_iff]
    exact eq_zero_of_subsingleton _
  have hmem0 : (⟨_, hmem⟩ : group f σ hσ (Stacks.Hilbert.fieldPoint K)) ∈
      groupZero f hdim σ hσ (Stacks.Hilbert.fieldPoint K) := by
    rw [mem_groupZero_iff]
    intro t
    rw [degree_apply]
    show relativeInvertibleDegreeHomAt _ _ t ((smallEquiv (bc f (Stacks.Hilbert.fieldPoint K)))
      ((smallEquiv (bc f (Stacks.Hilbert.fieldPoint K))).symm c')) = 0
    rw [AddEquiv.apply_symm_apply,
      relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom _ _ hdim₀]
    have hw : p ≫ f = bcProj f (Stacks.Hilbert.fieldPoint K) := by
      rw [pullback.condition, Category.comp_id]
      rfl
    have : IsIso p := inferInstance
    rw [invertibleCurveDegreeHom_schemePullbackClass_of_isIso K p hw hdimX hdim₀]
    exact hc
  set a := classifyingHom f hdim σ hσ e _ hmem0
  have hwa : a.left ≫ A.X.hom = 𝟙 (Spec (.of K)) := Over.w a
  refine ⟨a.left, hwa, ?_⟩
  rw [pointClass, dite_eq_left hwa]
  have ha : (Over.homMk a.left hwa : Stacks.Hilbert.fieldPoint K ⟶ A.X) = a := rfl
  rw [ha, representedClass_classifyingHom]
  show Stacks.Picard.schemePullbackClass (toBcFieldPoint f)
    ((smallEquiv (bc f (Stacks.Hilbert.fieldPoint K)))
      ((smallEquiv (bc f (Stacks.Hilbert.fieldPoint K))).symm c')) = c
  rw [AddEquiv.apply_symm_apply, Stacks.Picard.schemePullbackClass_comp]
  have hι : toBcFieldPoint f ≫ p = 𝟙 X := pullback.lift_fst _ _ _
  rw [hι, Stacks.Picard.schemePullbackClass_id]

omit [IsAlgClosed K] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- The class of a rational point turns multiplication by `n` into multiplication by `n`. -/
theorem pointClass_eq_zsmul (n : ℤ) (g g' : Spec (.of K) ⟶ A.X.left) (hg : g ≫ A.X.hom = 𝟙 _)
    (hg' : g' ≫ A.X.hom = 𝟙 _) (h : g' ≫ ((𝟙 A.X : A.X ⟶ A.X) ^ n).left = g) :
    pointClass f hdim σ hσ e g = n • pointClass f hdim σ hσ e g' := by
  rw [pointClass, dite_eq_left hg, pointClass, dite_eq_left hg']
  have hhom : (Over.homMk g hg : Stacks.Hilbert.fieldPoint K ⟶ A.X) =
      (Over.homMk g' hg' : Stacks.Hilbert.fieldPoint K ⟶ A.X) ^ n := by
    rw [← Category.comp_id (Over.homMk g' hg' : Stacks.Hilbert.fieldPoint K ⟶ A.X),
      ← GrpObj.comp_zpow]
    ext
    simp [h]
  rw [hhom, representedClass_zpow, schemePullbackClass_zsmul']

end Stacks.RigidifiedPicard

namespace Stacks.WeilCohomology

/-- **The Jacobian input of the curve case of [Stacks, Tag 0FH7], from a representation of
`Pic⁰`.** Let `X` be a proper smooth geometrically irreducible curve over an algebraically
closed field `K` with a rational point `σ`, and let `A` be a group scheme over `K`, smooth over
`K`, with an isomorphism of group-valued functors between its functor of points and the
degree-zero rigidified Picard functor `Pic⁰_{X/K,σ}`. Then
`Stacks.WeilCohomology.JacobianParametrization K n f hdimX` holds, for every integer `n`: `A` is
an abelian variety, and the classes of its rational points are exactly the degree-zero Picard
classes of `X`, with multiplication by `n` on `A` becoming multiplication by `n`. -/
theorem jacobianParametrization_of_iso_functorZero {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] [Smooth f] [GeometricallyIrreducible f]
    [SmoothOfRelativeDimension 1 f] (hdimX : topologicalKrullDim X ≤ 1)
    (hdim : ∀ s : Spec (.of K), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (A : Grp (Over (Spec (.of K)))) [Smooth A.X.hom]
    (e : CategoryTheory.yonedaGrp.obj A ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ)
    (n : ℤ) :
    JacobianParametrization K n f hdimX :=
  ⟨A, Stacks.RigidifiedPicard.isAbelianVariety_of_iso_functorZero f hdimX hdim σ hσ e,
    Stacks.RigidifiedPicard.pointClass f hdim σ hσ e,
    fun c hc => Stacks.RigidifiedPicard.exists_pointClass_eq f hdimX hdim σ hσ e c hc,
    fun g g' hg hg' h => Stacks.RigidifiedPicard.pointClass_eq_zsmul f hdim σ hσ e n g g' hg hg' h⟩

end Stacks.WeilCohomology
