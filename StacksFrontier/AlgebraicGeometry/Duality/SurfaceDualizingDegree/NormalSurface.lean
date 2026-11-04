module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedStalksOfClosedPoints
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization

/-!
# The dualizing complex of a normal surface is its dualizing module in degree `-2`

Let `X` be a connected Noetherian normal scheme of dimension at most two and let `ω_X^•` be a
dualizing complex on `X` which is normalized at the closed points of `X`, in the sense that its
associated shift function of [Stacks, Tag 0AWF] vanishes there. Then

`ω_X^• ≅ ω_X[d]`, `ω_X = H^{-d}(ω_X^•)`, `d = dim X`,

and `ω_X` is a coherent Cohen–Macaulay `𝒪_X`-module. For a surface, `d = 2`.

Two facts combine. A locally Noetherian normal scheme of dimension at most two is
Cohen–Macaulay ([Stacks, Tag 0B3D]), and on a connected Cohen–Macaulay scheme a dualizing
complex is concentrated in a single degree ([Stacks, Tag 0AWT]). That degree is *not* determined
by `ω_X^•` being a dualizing complex: a shift of a dualizing complex is again one, so the
concentration degree moves with it. What pins it is the normalization. For a dualizing complex
normalized at the closed points, `H^{-dim X}` has support the union of the irreducible components
of dimension `dim X` ([Stacks, Tag 0AWN]); a connected Noetherian normal scheme is irreducible,
so that support is all of `X` and `H^{-dim X}(ω_X^•)` is nonzero. Since the complex has
cohomology in one degree only, that degree is `-dim X`.

## Main results

All in the namespace `Stacks.Duality`.

* `not_isZero_homology_neg_natDim_of_isNormal` — on a connected Noetherian normal scheme a
  dualizing complex normalized at the closed points has nonzero cohomology in degree `-dim X`.
* `exists_coherent_cohenMacaulay_iso_single_of_isNormal_of_topologicalKrullDim_le_two` — on a
  connected locally Noetherian normal scheme of dimension at most two, a dualizing complex is a
  coherent Cohen–Macaulay module placed in some single degree.
* `iso_single_of_not_isZero_homology` — on a connected Cohen–Macaulay scheme that degree is the
  one in which the cohomology does not vanish.
* `coherent_cohenMacaulay_iso_single_neg_natDim_of_isNormal` — the two combined: the degree is
  `-dim X`.
* `dualizingComplexIsoShiftNatDimOfIsNormal` — the same isomorphism written as a shift,
  `ω_X^• ≅ ω_X[dim X]`.
* `dualizingComplexIsoShiftTwoOfIsNormalSurface` — **`ω_X^• ≅ ω_X[2]`** for a normal surface.

## Implementation notes

The derived category is taken at a free binder `[HasDerivedCategory.{w} X.Modules]`, so every
statement below holds at either model of `D(𝒪_X)`. All of the inputs are already stated that
way: `Stacks.Duality.IsDualizingComplex`,
`Stacks.Duality.exists_coherent_cohenMacaulay_iso_single_of_connected` and the results of
[Stacks, Tag 0AWN] carry the same binder, and
`AlgebraicGeometry.isCohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two` mentions no derived
category at all.

The dimension enters as `Stacks.Duality.natDim X`, the dimension of `X` as a natural number,
which is the convention in which the degree `-dim X` of the dualizing module is written. For a
scheme of dimension exactly `d` it is `d`.

The shift spelling `ω_X[d]` is obtained from the degree spelling by
`CategoryTheory.SingleFunctors.shiftIso`, as in
`Stacks.Duality.relativeDualizingComplexIsoShiftOfIsProper`.

## References

* [Stacks Project, Tag 0B3D](https://stacks.math.columbia.edu/tag/0B3D)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u w

namespace Stacks.Duality

/-- Cohomology of an object placed in a single degree vanishes in every other degree. -/
private theorem isZero_homologyFunctor_singleFunctor_of_ne {C : Type u} [Category C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : C) {i n : ℤ} (h : i ≠ n) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.singleFunctor C n).obj M)) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) n M i h).of_iso
    ((DerivedCategory.homologyFunctorFactors C i).app ((CochainComplex.singleFunctor C n).obj M))

/-- A point in the support of a sheaf of modules witnesses that the sheaf is nonzero. -/
private theorem not_isZero_of_mem_supp {X : Scheme.{u}} (F : X.Modules) {x : X}
    (hx : x ∈ _root_.SheafOfModules.supp F) : ¬ IsZero F := fun h =>
  not_nontrivial_iff_subsingleton.mpr
      ((stalkLinearEquivSchemeStalk _ x).toEquiv.subsingleton_congr.mpr
        (ModuleCat.isZero_iff_subsingleton.mp ((schemeStalkModuleFunctor x).map_isZero h)))
    ((_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mp hx)

/-! ### The degree `-dim X` carries cohomology -/

/-- **A dualizing complex normalized at the closed points of a connected Noetherian normal scheme
has nonzero cohomology in degree `-dim X`.**

Such a scheme is irreducible, so its generic point `ξ` has `closure {ξ} = X` and a
zero-dimensional local ring; the support of `H^{-dim X}` is the locus where the dimension of the
closure of a point and the dimension of its local ring add up to `dim X` ([Stacks, Tag 0AWN]),
and `ξ` lies there. -/
theorem not_isZero_homology_neg_natDim_of_isNormal {X : Scheme.{u}} [IsNoetherian X]
    [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules] (hnormal : IsNormal X)
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) :
    ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj K) := by
  have : IrreducibleSpace X := irreducibleSpace_of_isNormal_of_connectedSpace X hnormal
  obtain ⟨hdim, hloc⟩ := hasNormalizedStalks_natDim hK h0
  refine not_isZero_of_mem_supp _ (x := genericPoint X) ?_
  rw [supp_homology_neg_eq_setOf hloc]
  have hclosure : topologicalKrullDim (closure ({genericPoint X} : Set X)) =
      (natDim X : WithBot ℕ∞) := by
    rw [genericPoint_spec X, topologicalKrullDim_univ, hdim]
  have hstalk : ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    simpa only [WithBot.coe_zero] using
      congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞))
        (Order.coheight_eq_zero.mpr (fun b _ => genericPoint_specializes b))
  show topologicalKrullDim (closure ({genericPoint X} : Set X)) +
    ringKrullDim (X.presheaf.stalk (genericPoint X)) = (natDim X : WithBot ℕ∞)
  rw [hclosure, hstalk, add_zero]

/-! ### The concentration degree -/

/-- **A dualizing complex on a connected locally Noetherian normal scheme of dimension at most
two is a coherent Cohen–Macaulay module placed in a single degree.** Such a scheme is
Cohen–Macaulay ([Stacks, Tag 0B3D]), which is the hypothesis of [Stacks, Tag 0AWT]. -/
theorem exists_coherent_cohenMacaulay_iso_single_of_isNormal_of_topologicalKrullDim_le_two
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [ConnectedSpace X]
    [HasDerivedCategory.{w} X.Modules] (hX : topologicalKrullDim X ≤ 2)
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) :
    ∃ n : ℤ, _root_.SheafOfModules.IsCoherent
        ((DerivedCategory.homologyFunctor X.Modules n).obj K) ∧
      AlgebraicGeometry.SheafIsCohenMacaulay X
        ((DerivedCategory.homologyFunctor X.Modules n).obj K) ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules n).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj K)) :=
  exists_coherent_cohenMacaulay_iso_single_of_connected K hK
    (AlgebraicGeometry.isCohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two X hX)

/-- **The single degree in which a dualizing complex on a connected Cohen–Macaulay scheme is
concentrated is the one where its cohomology does not vanish.** The complex is concentrated in
*some* degree by [Stacks, Tag 0AWT]; cohomology of an object placed in one degree vanishes in
every other, so a degree carrying cohomology is that one. -/
theorem iso_single_of_not_isZero_homology {X : Scheme.{u}} [IsLocallyNoetherian X]
    [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) (hX : AlgebraicGeometry.IsCohenMacaulay X) (m : ℤ)
    (hm : ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules m).obj K)) :
    _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules m).obj K) ∧
      AlgebraicGeometry.SheafIsCohenMacaulay X
        ((DerivedCategory.homologyFunctor X.Modules m).obj K) ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules m).obj
        ((DerivedCategory.homologyFunctor X.Modules m).obj K)) := by
  obtain ⟨n, hcoh, hcm, ⟨e⟩⟩ := exists_coherent_cohenMacaulay_iso_single_of_connected K hK hX
  obtain rfl : n = m := by
    by_contra hne
    exact hm ((isZero_homologyFunctor_singleFunctor_of_ne
      ((DerivedCategory.homologyFunctor X.Modules n).obj K) (Ne.symm hne)).of_iso
        ((DerivedCategory.homologyFunctor X.Modules m).mapIso e))
  exact ⟨hcoh, hcm, ⟨e⟩⟩

/-! ### `ω_X^• = ω_X[dim X]` -/

/-- **The dualizing complex of a connected Noetherian normal scheme of dimension at most two is
its dualizing module in degree `-dim X`.** The module `ω_X = H^{-dim X}(ω_X^•)` is coherent and
Cohen–Macaulay, and `ω_X^• ≅ ω_X` placed in degree `-dim X`.

The hypothesis `h0` is the normalization of `ω_X^•` at the closed points of `X`
([Stacks, Tag 0AWF]); it cannot be dropped, since a shift of a dualizing complex is again a
dualizing complex and shifts the degree of concentration with it. -/
theorem coherent_cohenMacaulay_iso_single_neg_natDim_of_isNormal {X : Scheme.{u}}
    [IsNoetherian X] [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules] (hnormal : IsNormal X)
    (hX : topologicalKrullDim X ≤ 2) (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) :
    _root_.SheafOfModules.IsCoherent
        ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj K) ∧
      AlgebraicGeometry.SheafIsCohenMacaulay X
        ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj K) ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules (-(natDim X : ℤ))).obj
        ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj K)) :=
  have : IsNormal X := hnormal
  iso_single_of_not_isZero_homology K hK
    (AlgebraicGeometry.isCohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two X hX) _
    (not_isZero_homology_neg_natDim_of_isNormal hnormal hK h0)

/-- **`ω_X^• ≅ ω_X[dim X]`** on a connected Noetherian normal scheme of dimension at most two
carrying a dualizing complex normalized at its closed points: the dualizing complex is the
dualizing module `ω_X = H^{-dim X}(ω_X^•)` shifted by `dim X`. -/
def dualizingComplexIsoShiftNatDimOfIsNormal {X : Scheme.{u}} [IsNoetherian X] [ConnectedSpace X]
    [HasDerivedCategory.{w} X.Modules] (hnormal : IsNormal X) (hX : topologicalKrullDim X ≤ 2)
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) :
    K ≅ ((DerivedCategory.singleFunctor X.Modules 0).obj
      ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj K))⟦(natDim X : ℤ)⟧ :=
  (coherent_cohenMacaulay_iso_single_neg_natDim_of_isNormal hnormal hX K hK h0).2.2.some ≪≫
    ((DerivedCategory.singleFunctors X.Modules).shiftIso (natDim X : ℤ) (-(natDim X : ℤ)) 0
      (by omega)).symm.app _

/-- **`ω_X^• ≅ ω_X[2]` for a normal surface.** Let `X` be a connected Noetherian normal scheme of
dimension two and `ω_X^•` a dualizing complex on `X` normalized at the closed points. Then
`ω_X^•` is the dualizing module `ω_X = H^{-2}(ω_X^•)` shifted by two. -/
def dualizingComplexIsoShiftTwoOfIsNormalSurface {X : Scheme.{u}} [IsNoetherian X]
    [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules] (hnormal : IsNormal X)
    (hX : topologicalKrullDim X = 2) (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) :
    K ≅ ((DerivedCategory.singleFunctor X.Modules 0).obj
      ((DerivedCategory.homologyFunctor X.Modules (-2 : ℤ)).obj K))⟦(2 : ℤ)⟧ :=
  have hnat : natDim X = 2 := by rw [natDim, hX]; rfl
  dualizingComplexIsoShiftNatDimOfIsNormal hnormal hX.le K hK h0 ≪≫
    eqToIso (by rw [hnat, Nat.cast_ofNat])

/-- **`H^{-2}(ω_X^•)` is a coherent Cohen–Macaulay module on a normal surface**, the dualizing
module `ω_X` of [Stacks, Tag 0AWI] with respect to a dualizing complex normalized at the closed
points. -/
theorem coherent_cohenMacaulay_homology_neg_two_of_isNormalSurface {X : Scheme.{u}}
    [IsNoetherian X] [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules] (hnormal : IsNormal X)
    (hX : topologicalKrullDim X = 2) (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) :
    _root_.SheafOfModules.IsCoherent
        ((DerivedCategory.homologyFunctor X.Modules (-2 : ℤ)).obj K) ∧
      AlgebraicGeometry.SheafIsCohenMacaulay X
        ((DerivedCategory.homologyFunctor X.Modules (-2 : ℤ)).obj K) := by
  have hnat : natDim X = 2 := by rw [natDim, hX]; rfl
  have h := coherent_cohenMacaulay_iso_single_neg_natDim_of_isNormal hnormal hX.le K hK h0
  rw [hnat] at h
  exact ⟨h.1, h.2.1⟩

end Stacks.Duality

end
