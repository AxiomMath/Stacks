module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedStalksOfClosedPoints
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# A complex with upper shriek charts over a local base

Let `S` be an affine scheme whose ring of global sections `A = Γ(S, ⊤)` is a Noetherian local
ring, let `ω_S` be a complex on `S` which is the associated sheaf of a normalized dualizing
complex `ω_A` over `A`, and let `f : X ⟶ S` be proper. This is the situation of
[Stacks, Tag 0AWI]. A complex `L` on `X` which over every affine chart of `f` is the associated
sheaf of the algebraic upper shriek of the model of `ω_S` — as `f^! ω_S` is, by
[Stacks, Tag 0BV2] — is a dualizing complex whose associated dimension function vanishes at the
closed points: a closed point of `X` maps to the closed point of `S` because `f` is closed, and
there [Stacks, Tag 0E9N] applies.

## Main results

* `Stacks.Duality.isDualizingComplex_of_isTildeModelOn_top` — a complex modelled on all of an
  affine scheme by a dualizing complex is a dualizing complex.
* `Stacks.Duality.HasTopCharts` — the chart description of `L` over the affine open `⊤` of `S`.
* `Stacks.Duality.isDualizingComplex_of_hasTopCharts` and
  `Stacks.Duality.associatedShiftFunction_eq_zero_of_hasTopCharts` — the two properties of `L`,
  and `Stacks.Duality.vanishing_and_support_of_hasTopCharts`,
  `Stacks.Duality.exists_nontrivial_iff_depth_le_of_hasTopCharts` — the conclusions of
  [Stacks, Tag 0AWN] and the depth criterion at closed points.

## References

* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0E9N](https://stacks.math.columbia.edu/tag/0E9N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe w w' u

namespace Stacks.Duality

/-- **A complex with a dualizing model on all of an affine scheme is a dualizing complex**: the
single affine open `⊤` covers, and [Stacks, Tag 0A86] applies. -/
theorem isDualizingComplex_of_isTildeModelOn_top {S : Scheme.{u}} [IsAffine S]
    [IsLocallyNoetherian S] [HasDerivedCategory.{w} S.Modules] {K : DerivedCategory S.Modules}
    {ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤))}
    (hω : letI : IsNoetherianRing Γ(S, ⊤) :=
        IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
      Dualizing.IsDualizingComplex ω)
    (hmodel : IsTildeModelOnAnyModel K ⊤ (isAffineOpen_top S) ω) : IsDualizingComplex K :=
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  isDualizingComplex_iff_exists_affineOpenCover.mpr
    ⟨PUnit, fun _ => ⊤, fun _ => isAffineOpen_top S, iSup_const,
      fun _ => hasDualizingModelOn_of_isTildeModelOnAnyModel hω hmodel⟩

section LocalBase

variable {X S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] [IsNoetherianRing Γ(S, ⊤)]
  [IsLocalRing Γ(S, ⊤)]
  [IsLocallyNoetherian X] (f : X ⟶ S) [IsProper f]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} S.Modules]
  {L : DerivedCategory X.Modules}
  {ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤))}

omit [IsLocallyNoetherian S] [IsNoetherianRing Γ(S, ⊤)] [IsLocallyNoetherian X]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} S.Modules] in
/-- A closed point of a scheme proper over an affine scheme with local ring of global sections
lies over the closed point. -/
theorem primeIdealOf_eq_maximalIdeal_of_isClosed {x : X} (hx : IsClosed ({x} : Set X)) :
    ((isAffineOpen_top S).primeIdealOf ⟨f x, trivial⟩).asIdeal =
      IsLocalRing.maximalIdeal Γ(S, ⊤) := by
  have hcl : IsClosed ({f x} : Set S) := by simpa using f.isClosedMap _ hx
  exact IsLocalRing.eq_maximalIdeal
    (isMaximal_primeIdealOf_of_isClosed (isAffineOpen_top S) (x := f x) trivial hcl)

/-- **Upper shriek charts over the whole base.** `L` is, over every affine `U ⊆ X` and for every
polynomial presentation of `Γ(S, ⊤) → Γ(X, U)`, the associated sheaf of the algebraic upper
shriek of `ω`. This is the chart description of [Stacks, Tag 0BV2] for `L = f^!ω_S` over the
single affine open `⊤` of `S`, `ω` being the model of `ω_S` there. -/
def HasTopCharts (f : X ⟶ S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (L : DerivedCategory X.Modules) : Prop :=
  ∀ (U : X.Opens) (hU : IsAffineOpen U)
    (p : Dualizing.PolynomialPresentation (f.appLE ⊤ U (by simp)).hom),
    IsTildeModelOnAnyModel L U hU (p.upperShriekFunctor.{u, u}.obj ω)

omit [IsLocallyNoetherian S] [IsLocalRing Γ(S, ⊤)] [IsProper f]
  [HasDerivedCategory.{w'} S.Modules] in
/-- **The complex of upper shriek charts is dualizing.** -/
theorem isDualizingComplex_of_hasTopCharts [LocallyOfFiniteType f]
    (hω : Dualizing.IsDualizingComplex ω) (hchart : HasTopCharts f ω L) :
    IsDualizingComplex L := by
  have hpt : ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U),
      x ∈ U ∧ HasDualizingModelOn L U hU := fun x => by
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
    have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation _
      (f.finiteType_appLE (isAffineOpen_top S) hU (by simp))
    exact ⟨U, hU, hxU, hasDualizingModelOn_of_isTildeModelOnAnyModel
      (Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex p ω hω)
      (hchart U hU p)⟩
  choose U hU hxU hmod using hpt
  refine isDualizingComplex_iff_exists_affineOpenCover.mpr ⟨X, U, hU, ?_, hmod⟩
  exact top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩

omit [IsLocallyNoetherian S] [HasDerivedCategory.{w'} S.Modules] in
/-- **The complex of upper shriek charts is normalized at the closed points.** -/
theorem associatedShiftFunction_eq_zero_of_hasTopCharts [LocallyOfFiniteType f]
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) (hchart : HasTopCharts f ω L)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    associatedShiftFunction L x = 0 := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  have hUV : U ≤ f ⁻¹ᵁ ⊤ := by simp
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation _
    (f.finiteType_appLE (isAffineOpen_top S) hU hUV)
  refine associatedShiftFunction_eq_zero_of_isTildeModelOn_upperShriekFunctor hU p ω hω
    (hchart U hU p) hxU hx ?_
  exact (congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE ⊤ (isAffineOpen_top S) U hU hUV hxU)).trans
    (primeIdealOf_eq_maximalIdeal_of_isClosed f hx)

omit [IsLocallyNoetherian S] [HasDerivedCategory.{w'} S.Modules] in
/-- **The conclusions of [Stacks, Tag 0AWN] for a complex with upper shriek charts over a local
base**: cohomology only in degrees `-dim X, …, 0`, supports of dimension at most `-i`, and the
first cohomology sheaf `H^{-dim X}(L)` coherent with property `(S₂)`, supported on the union of
the irreducible components of dimension `dim X`. -/
theorem vanishing_and_support_of_hasTopCharts [AlgebraicGeometry.IsNoetherian X]
    [LocallyOfFiniteType f] (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hchart : HasTopCharts f ω L) :
    (∀ i : ℤ, ¬ Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L) →
      i ≤ 0 ∧ (((-i).toNat : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) ∧
    (∀ i : ℤ, topologicalKrullDim (_root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules i).obj L)) ≤
      if i ≤ 0 then (((-i).toNat : ℕ) : WithBot ℕ∞) else ⊥) ∧
    ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj L).IsCoherent ∧
    SheafHasPropertySk X ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj L)
      2 ∧
    _root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj L) =
      ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = topologicalKrullDim X} := by
  have hK := isDualizingComplex_of_hasTopCharts f hω.1 hchart
  have h0 := associatedShiftFunction_eq_zero_of_hasTopCharts f hω hchart
  obtain ⟨hcoh, hS2, hsupp⟩ := homology_natDim_of_associatedShiftFunction_eq_zero hK h0
  refine ⟨fun i hi => ?_,
    topologicalKrullDim_supp_homology_le_of_associatedShiftFunction_eq_zero hK h0, hcoh, hS2,
    hsupp⟩
  have hmem := mem_Icc_of_not_isZero_homology_of_associatedShiftFunction_eq_zero hK h0 i hi
  have hX : Nonempty X := not_isEmpty_iff.mp fun _ => hi (isZero_of_isEmpty _)
  rw [(hasNormalizedStalks_natDim hK h0).1]
  have h1 := hmem.1
  exact ⟨hmem.2, by exact_mod_cast (show (-i).toNat ≤ natDim X by omega)⟩

omit [IsLocallyNoetherian S] [HasDerivedCategory.{w'} S.Modules] in
/-- **The depth criterion at a closed point** for a complex with upper shriek charts over a local
base: one of the stalks of `H^i(L), …, H^0(L)` at a closed point `x` is nonzero exactly when
`depth(𝒪_{X,x}) ≤ -i`. -/
theorem exists_nontrivial_iff_depth_le_of_hasTopCharts
    [AlgebraicGeometry.IsNoetherian X]
    [LocallyOfFiniteType f] (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hchart : HasTopCharts f ω L) {x : X} (hx : IsClosed ({x} : Set X)) (i : ℤ) :
    (∃ j : ℤ, i ≤ j ∧ j ≤ 0 ∧ Nontrivial (moduleStalkAtPoint
        ((DerivedCategory.homologyFunctor X.Modules j).obj L) x)) ↔
      i ≤ 0 ∧ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≤ ((-i).toNat : ℕ∞) := by
  have hK := isDualizingComplex_of_hasTopCharts f hω.1 hchart
  have h0 := associatedShiftFunction_eq_zero_of_hasTopCharts f hω hchart
  have : Nonempty X := ⟨x⟩
  exact exists_nontrivial_stalk_homology_iff_depth_le (hasNormalizedStalks_natDim hK h0).2 hx i

end LocalBase

end Stacks.Duality

end
