module

public import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Smooth.NilpotentLifting
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints

/-!
# Refining a smooth cover by an étale neighbourhood of a closed point

Let `t : T ⟶ Z` be a morphism of affine schemes, let `c : Spec K ⟶ Z` be a closed point of `Z`
with residue field `K`, and suppose that `c` factors through `T` by a finite-order thickening
`p : Spec K ⟶ T`; this is the situation of a point of an Artinian local scheme `T` over `Z`
inducing an isomorphism on residue fields. Let `m : T̃ ⟶ T` be a smooth surjective morphism.
Then there is an étale morphism `τ : Z₁ ⟶ Z` from an affine scheme whose fibre over `c` is the
spectrum `Spec K₁` of a finite separable extension of `K`, and `m` has a section over the base
change `T ×_Z Z₁ ⟶ T`.

The fibre of `m` over `p` is a nonempty smooth `K`-scheme, so it has a closed point with
residue field finite and separable over `K` (Stacks 056U). That residue field is étale over `K`,
so its spectrum lifts to an étale `Z`-scheme across the closed immersion `c` (Stacks 057R), and
the point extends across the finite-order thickening `Spec K₁ ⟶ T ×_Z Z₁` because `m` is
smooth.

## Main results

* `AlgebraicGeometry.exists_etale_section_of_smooth_of_closedPoint`.
* `AlgebraicGeometry.exists_finite_separable_point_of_smooth`: a smooth surjective scheme over a
  field `K` has a point with values in a finite separable extension of `K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A smooth surjective scheme over a field has a point over a finite separable extension. -/
private theorem exists_finite_separable_point_aux {T₀ : Scheme.{u}} {K : Type u} [Field K]
    (m : T₀ ⟶ Spec (.of K)) [Smooth m] [Surjective m] :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁), Module.Finite K K₁ ∧
      Algebra.IsSeparable K K₁ ∧
      ∃ g : Spec (.of K₁) ⟶ T₀, g ≫ m = Spec.map (CommRingCat.ofHom (algebraMap K K₁)) := by
  have : Nonempty T₀ := by
    obtain ⟨y, -⟩ := m.surjective (IsLocalRing.closedPoint K)
    exact ⟨y⟩
  obtain ⟨x, -, hxfin, hxsep⟩ := (dense_closedPoints_with_finite_separable_residueField_of_smooth
    m).nonempty
  let alg : Algebra K (T₀.residueField x) := ((Scheme.ΓSpecIso (.of K)).inv ≫ m.appTop ≫
    T₀.Γevaluation x).hom.toAlgebra
  exact ⟨T₀.residueField x, inferInstance, alg, hxfin, hxsep, T₀.fromSpecResidueField x,
    (SpecMap_algebraMap_residueField m x).symm⟩

/-- **A smooth surjective morphism has a section after an étale base change through a closed
point.** -/
theorem exists_etale_section_of_smooth_of_closedPoint {Z T T₀ : Scheme.{u}} (t : T ⟶ Z)
    (m : T₀ ⟶ T) [IsAffine T] [IsAffine Z] [Smooth m] [Surjective m]
    {K : Type u} [Field K] (c : Spec (.of K) ⟶ Z) [IsClosedImmersion c]
    (p : Spec (.of K) ⟶ T) (hp : Stacks.Thickenings.IsFiniteOrderThickening p)
    (hpt : p ≫ t = c) :
    ∃ (K₁ : Type u) (_ : Field K₁) (Z₁ : Scheme.{u}) (τ : Z₁ ⟶ Z)
      (c₁ : Spec (.of K₁) ⟶ Z₁) (e₁ : Spec (.of K₁) ⟶ Spec (.of K)),
      (∃ _ : Algebra K K₁, Module.Finite K K₁ ∧ Algebra.IsSeparable K K₁ ∧
        e₁ = Spec.map (CommRingCat.ofHom (algebraMap K K₁))) ∧
      IsAffine Z₁ ∧ Etale τ ∧ IsPullback e₁ c₁ c τ ∧
      ∃ r : pullback t τ ⟶ T₀, r ≫ m = pullback.fst t τ := by
  classical
  -- a point of the fibre of `m` over `p` with finite separable residue field
  let F := pullback m p
  let Fm : F ⟶ Spec (.of K) := pullback.snd m p
  obtain ⟨K₁, _, alg, hfin, hsep, g₁, hg₁⟩ := exists_finite_separable_point_aux Fm
  let e₁ : Spec (.of K₁) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K₁))
  have : Algebra.FormallyEtale K K₁ := Algebra.FormallyEtale.of_isSeparable K K₁
  have : Algebra.FinitePresentation K K₁ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K K₁ := ⟨inferInstance, inferInstance⟩
  have he₁et : Etale e₁ := by
    have : (algebraMap K K₁).Etale := (RingHom.etale_algebraMap (R := K) (S := K₁)).2 inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr this
  -- lift the residue field across the closed point
  obtain ⟨Z₁, τ, hZ₁, hτ, iso, hiso⟩ := Stacks.Etale.exists_etale_lift_of_isClosedImmersion c e₁
  have := hZ₁
  have := hτ
  let c₁ : Spec (.of K₁) ⟶ Z₁ := iso.hom ≫ pullback.snd c τ
  have hpb : IsPullback e₁ c₁ c τ := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback c τ) iso.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [← hiso]
    · simp [c₁]
    · simp
    · simp
  refine ⟨K₁, inferInstance, Z₁, τ, c₁, e₁, ⟨alg, hfin, hsep, rfl⟩, hZ₁, hτ,
    hpb, ?_⟩
  -- the closed point of `T ×_Z Z₁` and the extension of the point across it
  let q₁ : Spec (.of K₁) ⟶ pullback t τ := pullback.lift (e₁ ≫ p) c₁
    (by rw [Category.assoc, hpt, hpb.w])
  have hq₁pb : IsPullback q₁ e₁ (pullback.fst t τ) p := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback t τ).flip
    rw [pullback.lift_snd, hpt]
    exact hpb.flip
  let g : Spec (.of K₁) ⟶ T₀ := g₁ ≫ pullback.fst m p
  have hg : g ≫ m = q₁ ≫ pullback.fst t τ := by
    simp only [g, q₁, Category.assoc, pullback.condition, pullback.lift_fst]
    exact congrArg (· ≫ p) hg₁
  obtain ⟨r, hr, -⟩ := Stacks.Smooth.exists_lift_of_isFiniteOrderThickening m q₁
    (Stacks.Thickenings.isFiniteOrderThickening_of_isPullback hq₁pb hp) g (pullback.fst t τ) hg
  exact ⟨r, hr⟩

/-- **A smooth surjective scheme over a field has a point over a finite separable extension**
(Tag 056U). -/
theorem exists_finite_separable_point_of_smooth {T₀ : Scheme.{u}} {K : Type u} [Field K]
    (m : T₀ ⟶ Spec (.of K)) [Smooth m] [Surjective m] :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁), Module.Finite K K₁ ∧
      Algebra.IsSeparable K K₁ ∧
      ∃ g : Spec (.of K₁) ⟶ T₀, g ≫ m = Spec.map (CommRingCat.ofHom (algebraMap K K₁)) := by
  exact exists_finite_separable_point_aux m

end AlgebraicGeometry

end
