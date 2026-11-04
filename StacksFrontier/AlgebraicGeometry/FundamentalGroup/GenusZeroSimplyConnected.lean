module

public import StacksFrontier.AlgebraicGeometry.Curves.EtaleCoverGenus
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteCochains
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.QuotientCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A curve of genus zero over an algebraically closed field is simply connected

Let `X` be a smooth, proper, geometrically irreducible curve of genus `0` over an algebraically
closed field `k`. Then `π₁(X, x)` is trivial: a proper open normal subgroup would give a connected
Galois finite étale cover `Z ⟶ X` of degree `d ≥ 2`, which is again a smooth proper geometrically
irreducible curve over `k` (its field of constants is a finite extension of `k`, hence `k`), and
the Riemann–Hurwitz formula `g_Z - 1 = d (g_X - 1) = -d ≤ -2` is impossible. This covers the case
`X_k̄ ≅ 𝐏¹` excluded in [Stacks, Tag 03VM].

## Main results

* `AlgebraicGeometry.isCurve_comp_of_isAlgClosed`: a connected finite étale cover of a smooth
  proper curve over an algebraically closed field is a smooth proper geometrically irreducible
  curve.
* `AlgebraicGeometry.subsingleton_etaleFundamentalGroup_of_genus_eq_zero`: `π₁` of a genus-zero
  curve over an algebraically closed field is trivial.
* `Stacks.GroupCohomology.vanishesTwo_of_subsingleton`: the trivial group has no `2`-cocycles but
  coboundaries.
-/

@[expose] public noncomputable section

open CategoryTheory Limits PreGaloisCategory

universe u v w

namespace AlgebraicGeometry

/-- **A connected finite étale cover of a smooth proper curve over an algebraically closed field
is a smooth proper geometrically irreducible curve over the same field**: its field of
constants is a finite extension of `k`, hence `k` itself. -/
theorem isCurve_comp_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] [IsCurve k f] [ConnectedSpace X]
    (Z : FiniteEtaleOver X) [ConnectedSpace Z.left] :
    IsProper (Z.hom ≫ f) ∧ Smooth (Z.hom ≫ f) ∧ GeometricallyIrreducible (Z.hom ≫ f) ∧
      IsCurve k (Z.hom ≫ f) := by
  obtain ⟨κ, _, _, _, r, hr, hP, hS, hG, hC⟩ := exists_constantField_of_finiteEtale k f Z
  have hbij : Function.Bijective (algebraMap k κ) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  set e := Spec.map (CommRingCat.ofHom (algebraMap k κ))
  have : IsIso (CommRingCat.ofHom (algebraMap k κ)) :=
    (RingEquiv.ofBijective (algebraMap k κ) hbij).toCommRingCatIso.isIso_hom
  have : IsIso e := inferInstance
  have hsq : IsPullback (𝟙 Z.left) (r ≫ e) r (inv e) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [← hr]
  have hP' : IsProper (r ≫ e) := MorphismProperty.of_isPullback hsq hP
  have hS' : Smooth (r ≫ e) := MorphismProperty.of_isPullback hsq hS
  have hG' : GeometricallyIrreducible (r ≫ e) := MorphismProperty.of_isPullback hsq hG
  refine ⟨hP', hS', hG', ?_⟩
  exact { toIsIntegral := hC.toIsIntegral
          topologicalKrullDim_eq_one := hC.topologicalKrullDim_eq_one }

/-- **A smooth proper geometrically irreducible curve of genus zero over an algebraically closed
field is simply connected**: every open normal subgroup of `π₁(X, x)` is everything, by the
Riemann–Hurwitz formula, and `π₁(X, x)` is profinite. -/
@[sga "1 X 3.10" "special case", sga "1 XI 1.1" "partial", sga "7 II 2.3.1" "more general"]
theorem subsingleton_etaleFundamentalGroup_of_genus_eq_zero (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
    [GeometricallyIrreducible f] [Smooth f] [ConnectedSpace X] (hg : genus f = 0)
    (base : GeometricPoint X) : Subsingleton (EtaleFundamentalGroup X base) := by
  have := compactSpace_etaleFundamentalGroup X base
  have := t2Space_etaleFundamentalGroup X base
  have := totallyDisconnectedSpace_etaleFundamentalGroup X base
  have htop : ∀ U : Subgroup (EtaleFundamentalGroup X base), U.Normal →
      IsOpen (U : Set (EtaleFundamentalGroup X base)) → U = ⊤ := by
    intro U hUn hUo
    by_contra hne
    obtain ⟨Z, hZc, hZgal, -, hZd⟩ := exists_connected_cover_of_isOpen_normal U hUn hUo hne
    have := hZc
    have := hZgal
    obtain ⟨hP, hS, hG, hC⟩ := isCurve_comp_of_isAlgClosed k f Z
    have := hP
    have := hS
    have := hG
    have := hC
    have hRH := genus_sub_one_eq_of_isGalois Z k f base
    rw [hg] at hRH
    push_cast at hRH
    omega
  refine ⟨fun a b => ?_⟩
  by_contra hab
  have hne : a * b⁻¹ ≠ 1 := fun h => hab (mul_inv_eq_one.1 h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := a * b⁻¹)) (Ne.symm hne)
  have hHtop := htop H.toSubgroup H.isNormal' H.isOpen
  have hmem : a * b⁻¹ ∈ ((H.toSubgroup : Subgroup _) : Set (EtaleFundamentalGroup X base)) := by
    rw [hHtop]
    trivial
  exact hH hmem rfl

end AlgebraicGeometry

namespace Stacks.GroupCohomology

/-- **The trivial group has no `2`-cocycles but coboundaries**: on a subsingleton group a cochain
`f` is `dOne` of the constant cochain at `f(1, 1)`. -/
theorem vanishesTwo_of_subsingleton (G : Type u) [Group G] [TopologicalSpace G] [Subsingleton G]
    (M : Type v) [AddCommGroup M] [DistribMulAction G M] : VanishesTwo G M := by
  intro f _ _
  refine ⟨fun _ => f (1, 1), IsLocallyConstant.const _, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  rw [Subsingleton.elim g 1, Subsingleton.elim h 1, dOne_apply, one_smul, sub_add_cancel]

end Stacks.GroupCohomology

end
