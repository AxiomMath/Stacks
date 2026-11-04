module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalTail
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFiniteDominant
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.Topology.Connected.ContractedLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degrees of pulled-back invertible modules on contracted and non-contracted curves

Let `g : C ⟶ Y` be a morphism of schemes and `L` an invertible `𝒪_Y`-module.

* If `g` maps `C` to a single point, then `g^* L ≅ 𝒪_C`: `L` is trivial on an open neighbourhood
  of that point, through which `g` factors. When `C` is a proper curve over a field `k` the
  degree of `g^* L` is therefore zero.
* If `C` is irreducible of dimension at most one and `g` is proper with image not a point, then
  `g` is finite: each of its fibres is a finite set of closed points. When `L` is ample and `C` is
  a proper curve, `g^* L` then has positive degree
  (`AlgebraicGeometry.invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom`).

Applied to the irreducible components of a curve `X` and a contraction `c : X ⟶ Y` with
`c^* L ≅ ω_X`, these say that the components contracted by `c` are exactly those on which `ω_X`
has degree zero (and degree is positive on the others), which describes the contracted locus of
`c` intrinsically in terms of `X`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_unit_of_forall_eq`: the pullback along
  a morphism with one-point image is trivial.
* `AlgebraicGeometry.invertibleCurveDegree_pullback_eq_zero_of_forall_eq`: its degree is zero.
* `AlgebraicGeometry.Scheme.Hom.isFinite_of_not_subsingleton_range`: a proper morphism from an
  irreducible scheme of dimension at most one is finite unless its image is a point.
* `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_not_subsingleton_range`: the pullback
  of an ample invertible module along a proper morphism out of an integral proper curve whose image
  is not a point has positive degree.
* `AlgebraicGeometry.degreeOver_pos_of_not_constant`: the degree `[R(C) : R(D)]` of a non-constant
  morphism of proper curves is positive.
* `AlgebraicGeometry.invertibleCurveDegree_neg_iff_of_not_constant`: the sign of a negative degree
  is detected on the image.
* `AlgebraicGeometry.invertibleCurveDegree_pullback_eq_degreeOver_mul`: along a non-constant
  morphism `h : C ⟶ D` of proper curves, `deg(h^* L) = [R(C) : R(D)] · deg(L)` for every
  invertible `L` ([Stacks, Tag 0AYZ] in rank one). In particular the degree of a non-contracted
  component's restriction is computed on its image.

## References

* [Stacks Project, Tag 0BUT](https://stacks.math.columbia.edu/tag/0BUT)
* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 0E3Q](https://stacks.math.columbia.edu/tag/0E3Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

section Trivial

/-- **The pullback along a morphism with one-point image is trivial.** If `g : C ⟶ Y` maps every
point to `y`, then for every invertible `𝒪_Y`-module `L`, `g^* L ≅ 𝒪_C`. -/
theorem Scheme.Modules.nonempty_pullback_iso_unit_of_forall_eq {C Y : Scheme.{u}} (g : C ⟶ Y)
    (L : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L]
    (y : Y) (hg : ∀ z, g.base z = y) :
    Nonempty ((Scheme.Modules.pullback g).obj L ≅ Scheme.unitModule C) := by
  obtain ⟨V, hyV, ⟨eV⟩⟩ := Stacks.Divisors.hasTrivializingTargetCover_of_isFinite (𝟙 Y) L y
  let W : Y.Opens := 𝟙 Y ⁻¹ᵁ V
  have hrange : Set.range g.base ⊆ (W.ι.opensRange : Set Y) := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    exact (hg z).symm ▸ hyV
  let g' : C ⟶ W := IsOpenImmersion.lift W.ι g hrange
  have hg' : g' ≫ W.ι = g := IsOpenImmersion.lift_fac _ _ _
  let eW : (Scheme.Modules.pullback W.ι).obj L ≅ Scheme.unitModule W :=
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app L).symm ≪≫ eV
  exact ⟨((Scheme.Modules.pullbackCongr hg').app L).symm ≪≫
    ((Scheme.Modules.pullbackComp g' W.ι).app L).symm ≪≫
    (Scheme.Modules.pullback g').mapIso eW ≪≫ Scheme.Modules.pullbackUnitIso g'⟩

/-- **The degree of a module pulled back along a morphism with one-point image is zero.** Let
`C` be proper of dimension at most one over a field `k` and `g : C ⟶ Y` map every point to `y`.
For every invertible `𝒪_Y`-module `L`, `deg(g^* L) = 0`. -/
theorem invertibleCurveDegree_pullback_eq_zero_of_forall_eq (k : Type u) [Field k]
    {C Y : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim C ≤ 1)
    (g : C ⟶ Y) (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (y : Y) (hg : ∀ z, g.base z = y) :
    invertibleCurveDegree k f hdim ((Scheme.Modules.pullback g).obj L) = 0 := by
  obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_iso_unit_of_forall_eq g L y hg
  exact invertibleCurveDegree_eq_zero_of_iso_unit k f hdim _ e

end Trivial

section Finite

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The fibres of a non-constant closed map out of an irreducible curve are finite sets of
closed points.** Let `X` be an irreducible Noetherian sober `T₀` space of dimension at most one
and `g : X → Y` a continuous closed map whose image has more than one point. Then every fibre
of `g` is discrete. -/
theorem isDiscrete_preimage_singleton_of_not_subsingleton_range [IrreducibleSpace X]
    [NoetherianSpace X] [QuasiSober X] [T0Space X] (hdim : topologicalKrullDim X ≤ 1)
    {g : X → Y} (hg : Continuous g) (hcl : IsClosedMap g) (hne : ¬ (Set.range g).Subsingleton)
    (y : Y) : IsDiscrete (g ⁻¹' {y}) := by
  set η := genericPoint X
  have hη : closure ({η} : Set X) = Set.univ := (genericPoint_spec X).def
  have himg : ∀ x : X, IsClosed ({x} : Set X) → IsClosed ({g x} : Set Y) := fun x hx ↦ by
    simpa using hcl _ hx
  have hclosed : ∀ x : X, x ≠ η → IsClosed ({x} : Set X) := by
    intro x hx
    refine (isClosed_singleton_or_closure_mem_irreducibleComponents hdim x).resolve_right ?_
    intro hc
    have hcu : closure ({x} : Set X) = Set.univ := by
      rwa [irreducibleComponents_eq_singleton] at hc
    exact hx (((genericPoint_spec X).eq ((isGenericPoint_def).2 hcu)).symm)
  have hηnot : ¬ IsClosed ({g η} : Set Y) := by
    intro hc
    refine hne ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hsub : ∀ z : X, g z = g η := fun z ↦
      (hc.preimage hg).closure_subset_iff.2 (Set.singleton_subset_iff.2 rfl)
        (hη.symm ▸ Set.mem_univ z)
    rw [hsub a, hsub b]
  by_cases hyη : g η = y
  · have hF : (g ⁻¹' {y}).Subsingleton := by
      intro a ha b hb
      have key : ∀ x ∈ g ⁻¹' {y}, x = η := fun x hx ↦ by
        by_contra hxη
        exact hηnot (by rw [hyη, ← Set.mem_singleton_iff.1 hx]; exact himg x (hclosed x hxη))
      rw [key a ha, key b hb]
    have : Subsingleton (g ⁻¹' {y}) := hF.coe_sort
    exact ⟨inferInstance⟩
  · have hne' : ∀ x ∈ g ⁻¹' {y}, x ≠ η := fun x hx h ↦ hyη (h ▸ hx)
    by_cases hF : (g ⁻¹' {y}).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hF
      have hyc : IsClosed ({y} : Set Y) := by
        rw [← Set.mem_singleton_iff.1 hx₀]
        exact himg x₀ (hclosed x₀ (hne' x₀ hx₀))
      obtain ⟨S, hSfin, hSc, hSirr, hFS⟩ :=
        NoetherianSpace.exists_finite_set_isClosed_irreducible (hyc.preimage hg)
      have hfin : (g ⁻¹' {y}).Finite := by
        rw [hFS]
        refine hSfin.sUnion fun T hT ↦ ?_
        have hgen := (hSirr T hT).isGenericPoint_genericPoint_closure
        rw [(hSc T hT).closure_eq] at hgen
        have htF : (hSirr T hT).genericPoint ∈ g ⁻¹' {y} :=
          hFS ▸ Set.subset_sUnion_of_mem hT hgen.mem
        rw [← hgen.def, (hclosed _ (hne' _ htF)).closure_eq]
        exact Set.finite_singleton _
      exact hfin.isDiscrete_of_subset_closedPoints fun x hx ↦ hclosed x (hne' x hx)
    · rw [Set.not_nonempty_iff_eq_empty.1 hF]
      exact Set.finite_empty.isDiscrete_of_subset_closedPoints (Set.empty_subset _)

/-- **A non-constant proper morphism out of an irreducible curve is finite.** Let `C` be an
irreducible Noetherian scheme of dimension at most one and `g : C ⟶ Y` a proper morphism whose
image is not a point. Then `g` is finite. -/
@[sga "1 VIII 6.1" "special case"]
theorem Scheme.Hom.isFinite_of_not_subsingleton_range {C Y : Scheme.{u}} (g : C ⟶ Y) [IsProper g]
    [IrreducibleSpace C] [NoetherianSpace C] (hdim : topologicalKrullDim C ≤ 1)
    (hne : ¬ (Set.range g.base).Subsingleton) : IsFinite g := by
  have : LocallyQuasiFinite g := locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
    fun y ↦ isDiscrete_preimage_singleton_of_not_subsingleton_range hdim g.continuous
      g.isClosedMap hne y
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

end Finite

section Positive

/-- **The pullback of an ample invertible module along a proper morphism out of an integral
proper curve whose image is not a point has positive degree.** -/
theorem invertibleCurveDegree_pos_of_isAmple_of_not_subsingleton_range (k : Type u) [Field k]
    {C Y : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] [IsIntegral C] [NoetherianSpace C]
    (hdim : topologicalKrullDim C = 1) (g : C ⟶ Y) [IsProper g]
    (hne : ¬ (Set.range g.base).Subsingleton) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple Y L) :
    0 < invertibleCurveDegree k f hdim.le ((Scheme.Modules.pullback g).obj L) :=
  have := g.isFinite_of_not_subsingleton_range hdim.le hne
  invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom k f hdim g L hL

end Positive

section NonContracted

/-- **The degree of an invertible module on the image of a non-contracted curve.** Let
`h : C ⟶ D` be a non-constant morphism of proper curves over `k`. For every invertible
`𝒪_D`-module `L`, `deg(h^* L) = [R(C) : R(D)] · deg(L)`. This is [Stacks, Tag 0AYZ] in rank
one. -/
theorem invertibleCurveDegree_pullback_eq_degreeOver_mul (k : Type u) [Field k]
    {C D : Scheme.{u}} (πC : C ⟶ Spec (.of k)) (πD : D ⟶ Spec (.of k)) [IsCurve k πC]
    [IsCurve k πD] [IsProper πC] [IsProper πD] (h : C ⟶ D) (hh : h ≫ πD = πC)
    (hnc : ¬ ∃ y : D, ∀ x : C, h.base x = y) (L : D.Modules)
    [SheafOfModules.IsInvertible D.presheaf D.ringCatSheaf.2 L] :
    invertibleCurveDegree k πC (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πC)))
        ((Scheme.Modules.pullback h).obj L) =
      (@degreeOver C D h _ _ (locallyOfFiniteType_of_isCurve_comp k πC πD h hh)
          (isDominant_of_not_constant k πC πD h hnc) : ℤ) *
        invertibleCurveDegree k πD (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πD))) L := by
  rw [invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact curveDegree_pullback_eq_degreeOver_mul k πC πD h hh hnc L 1

/-- **The degree of a non-constant morphism of proper curves is positive.** For a non-constant
morphism `h : C ⟶ D` of proper curves over `k`, the degree `[R(C) : R(D)]` is positive. -/
theorem degreeOver_pos_of_not_constant (k : Type u) [Field k]
    {C D : Scheme.{u}} (πC : C ⟶ Spec (.of k)) (πD : D ⟶ Spec (.of k)) [IsCurve k πC]
    [IsCurve k πD] [IsProper πC] [IsProper πD] (h : C ⟶ D) (hh : h ≫ πD = πC)
    (hnc : ¬ ∃ y : D, ∀ x : C, h.base x = y) :
    0 < @degreeOver C D h _ _ (locallyOfFiniteType_of_isCurve_comp k πC πD h hh)
      (isDominant_of_not_constant k πC πD h hnc) := by
  have := locallyOfFiniteType_of_isCurve_comp k πC πD h hh
  have := isDominant_of_not_constant k πC πD h hnc
  have hfib := preimage_genericPoint_of_not_constant k πC πD h hh hnc
  have htr := trdeg_functionField_eq_zero_of_eq_genericPoint h fun x hx ↦ by
    have : x ∈ h.base ⁻¹' ({genericPoint (D : Type u)} : Set D) := hx
    rwa [hfib] at this
  exact degreeOver_pos h ((trdeg_functionField_eq_zero_iff_finite h).mp htr)

/-- **The sign of a negative degree is detected on the image of a non-contracted curve.** For a
non-constant morphism `h : C ⟶ D` of proper curves and an invertible `𝒪_D`-module `L`,
`deg(h^* L) < 0` if and only if `deg(L) < 0`. -/
theorem invertibleCurveDegree_neg_iff_of_not_constant (k : Type u) [Field k]
    {C D : Scheme.{u}} (πC : C ⟶ Spec (.of k)) (πD : D ⟶ Spec (.of k)) [IsCurve k πC]
    [IsCurve k πD] [IsProper πC] [IsProper πD] (h : C ⟶ D) (hh : h ≫ πD = πC)
    (hnc : ¬ ∃ y : D, ∀ x : C, h.base x = y) (L : D.Modules)
    [SheafOfModules.IsInvertible D.presheaf D.ringCatSheaf.2 L] :
    invertibleCurveDegree k πC (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πC)))
        ((Scheme.Modules.pullback h).obj L) < 0 ↔
      invertibleCurveDegree k πD
        (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πD))) L < 0 := by
  rw [invertibleCurveDegree_pullback_eq_degreeOver_mul k πC πD h hh hnc L]
  have hpos : (0 : ℤ) < (@degreeOver C D h _ _ (locallyOfFiniteType_of_isCurve_comp k πC πD h hh)
      (isDominant_of_not_constant k πC πD h hnc) : ℤ) :=
    Int.natCast_pos.mpr (degreeOver_pos_of_not_constant k πC πD h hh hnc)
  simpa only [not_le] using (mul_nonneg_iff_of_pos_left hpos).not

end NonContracted

end AlgebraicGeometry
