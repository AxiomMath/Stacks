module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RegularPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory

/-!
# Bounded objects with coherent cohomology on a regular scheme are perfect

Let `X` be a regular scheme. Then every object of `D^b_{Coh}(𝒪_X)` is a perfect object of the
derived category of `𝒪_X`-modules. Together with the converse
`Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular` this is
[Stacks, Tag 0FDC].

## Main results

* `AlgebraicGeometry.isPerfect_of_isCoherentHomology_of_isGE_of_isLE`: a bounded object whose
  cohomology sheaves are coherent is perfect, stated with the bounds of the canonical
  t-structure.
* `Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular`: the
  forward half of [Stacks, Tag 0FDC].
* `Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_iff_isBoundedCoherent_of_isRegular`:
  the equivalence of [Stacks, Tag 0FDC] on a quasi-compact regular scheme.

## Implementation notes

The proof is an induction on the length of the interval in which the cohomology of the object is
concentrated, the base case being the degree-zero statement
`AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`: a coherent module placed in
degree zero is perfect. No affine-local argument appears here; all of the geometry is in that
base case, and in particular quasi-compactness of `X` is needed for neither.

An object which is both `≤ c` and `≥ c` for the canonical t-structure of
`Mathlib.Algebra.Homology.DerivedCategory.TStructure` is isomorphic to a single module placed in
degree `c`, by `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`, and that module
is identified with the `c`-th cohomology sheaf by
`DerivedCategory.singleFunctorCompHomologyFunctorIso`, so it is coherent. Comparing
`DerivedCategory.singleFunctor _ c` with `DerivedCategory.singleFunctor _ 0` through
`CochainComplex.SingleFunctors.shiftIso` and using stability of perfectness under shifts
(`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift`) reduces this case to the base
case.

For the induction step one truncates at `d`, the top of the interval. The truncation triangle
`τ^{<d}K ⟶ K ⟶ τ^{≥d}K ⟶ (τ^{<d}K)[1]` of
`CategoryTheory.Triangulated.TStructure.triangleLTGE` has its outer vertices in the two cases
already treated — `τ^{≥d}K` is concentrated in the single degree `d`, and `τ^{<d}K` is
concentrated in an interval one shorter — so the two-out-of-three property of [Stacks, Tag 08CR]
(`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished`) gives perfectness
of `K`.

Feeding the induction hypothesis requires knowing that the cohomology sheaves of the truncations
are again coherent. This is the comparison
`AlgebraicGeometry.isIso_homologyMap_truncLTι` and
`AlgebraicGeometry.isIso_homologyMap_truncGEπ` of the cohomology of an object with that of its
truncations, read off from the long exact cohomology sequence of the truncation triangle; outside
the range where the comparison applies the cohomology of a truncation vanishes, and a zero sheaf
is coherent.

Boundedness in the sense of `DerivedCategoryB.derivedCategoryBBounded` — vanishing of the
cohomology sheaves in all sufficiently large and all sufficiently small degrees — is converted
into the bounds `DerivedCategory.IsGE` and `DerivedCategory.IsLE` of the canonical t-structure by
`DerivedCategory.isGE_iff` and `DerivedCategory.isLE_iff`. The degenerate case in which the two
bounds are in the wrong order is the one where all cohomology vanishes, so the object is zero and
perfect.

## References

* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect

universe w v z u d

namespace AlgebraicGeometry

/-! ### Cohomology of the canonical truncations

The cohomology sheaves of an object and of its truncations agree in the range where the
truncation is an isomorphism on cohomology. Both statements are read off from the long exact
cohomology sequence of the truncation triangle. -/

/-- **Cohomology below the truncation degree is unchanged by `τ^{<c}`.** For `i < c` the map
`H^i(τ^{<c}K) ⟶ H^i(K)` induced by the inclusion of the truncation is an isomorphism, because the
two neighbouring cohomology sheaves of `τ^{≥c}K` in the long exact sequence vanish. -/
theorem isIso_homologyMap_truncLTι {C : Type w} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{z} C] (c i : ℤ) (hi : i < c) (K : DerivedCategory C) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLTι c).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE c).obj K
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished c K
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (DerivedCategory.isZero_of_isGE _ c i hi).eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)]
    exact (DerivedCategory.isZero_of_isGE _ c (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C i).map T.mor₁)

/-- **Cohomology above the truncation degree is unchanged by `τ^{≥c}`.** For `c ≤ i` the map
`H^i(K) ⟶ H^i(τ^{≥c}K)` induced by the projection to the truncation is an isomorphism, because
the two neighbouring cohomology sheaves of `τ^{<c}K` in the long exact sequence vanish. -/
theorem isIso_homologyMap_truncGEπ {C : Type w} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{z} C] (c i : ℤ) (hi : c ≤ i) (K : DerivedCategory C) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ c).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE c).obj K
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished c K
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (c - 1) (i + 1) (by omega)).eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (c - 1) i (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C i).map T.mor₂)

/-! ### Perfectness by induction on the length of the cohomological interval -/

/-- Coherence of modules on a ringed space transfers along an isomorphism. -/
private theorem isCoherent_of_iso_oxMod {X : Scheme.{u}} {M N : OXMod.{u, u} X.toRingedSpace}
    (e : M ≅ N) (h : M.IsCoherent) : N.IsCoherent :=
  ObjectProperty.prop_of_iso (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent) e h

/-- **An object concentrated in a single degree with coherent cohomology is perfect.** On a
regular scheme an object `K` of the derived category of `𝒪_X`-modules which is both `≤ c` and
`≥ c` for the canonical t-structure, and whose `c`-th cohomology sheaf is coherent, is perfect.

Such a `K` is isomorphic to its `c`-th cohomology sheaf placed in degree `c`, which is the `-c`
shift of that sheaf placed in degree `0`; the latter is perfect by
`AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`, and perfectness is stable under
shifts and isomorphisms. -/
theorem isPerfect_of_isCoherentHomology_of_isGE_of_isLE_self {X : Scheme.{u}} (hX : IsRegular X)
    [i : HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (c : ℤ) [K.IsGE c] [K.IsLE c]
    (hcoh : ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} X.toRingedSpace) c).obj K).IsCoherent) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) K := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K c
  have hY : Y.IsCoherent :=
    isCoherent_of_iso_oxMod
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) c).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (OXMod.{u, u} X.toRingedSpace) c).app Y) hcoh
  have hbase : RingedSpace.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj Y) :=
    @isPerfect_single_of_isCoherent_of_isRegular.{u, d} X hX i Y hY
  exact RingedSpace.IsPerfect.of_iso (X := X.toRingedSpace)
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hbase (-c))
    (((DerivedCategory.singleFunctors (OXMod.{u, u} X.toRingedSpace)).shiftIso
      (-c) c 0 (by omega)).app Y ≪≫ e.symm)

/-- **The induction on the length of the cohomological interval.** On a regular scheme an object
`K` of the derived category of `𝒪_X`-modules whose cohomology sheaves are all coherent and which
is `≥ c` and `≤ c + n` for the canonical t-structure is perfect.

The step truncates at the top of the interval: `τ^{≥(c+n+1)}K` is concentrated in the single
degree `c + n + 1`, `τ^{<(c+n+1)}K` is `≥ c` and `≤ c + n`, and both have coherent cohomology by
the comparison of cohomology with that of `K`. -/
theorem isPerfect_of_isCoherentHomology_of_isGE_of_isLE_add_natCast {X : Scheme.{u}}
    (hX : IsRegular X) [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)] (c : ℤ)
    (n : ℕ) (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    [K.IsGE c] [hle : K.IsLE (c + n)]
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} X.toRingedSpace) j).obj K).IsCoherent) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) K := by
  induction n generalizing K with
  | zero =>
      have : K.IsLE c := by simpa only [Nat.cast_zero, add_zero] using hle
      exact isPerfect_of_isCoherentHomology_of_isGE_of_isLE_self hX K c (hcoh c)
  | succ n ih =>
      set d : ℤ := c + n + 1
      have hLT : RingedSpace.IsPerfect (X := X.toRingedSpace)
          ((DerivedCategory.TStructure.t.truncLT d).obj K) := by
        have : ((DerivedCategory.TStructure.t.truncLT d).obj K).IsLE (c + (n : ℤ)) :=
          DerivedCategory.TStructure.t.isLE_of_le _ (d - 1) _ (by omega)
        refine ih _ fun j => ?_
        by_cases hj : j < d
        · have := isIso_homologyMap_truncLTι d j hj K
          exact isCoherent_of_iso_oxMod
            (asIso ((DerivedCategory.homologyFunctor
              (OXMod.{u, u} X.toRingedSpace) j).map
                ((DerivedCategory.TStructure.t.truncLTι d).app K))).symm (hcoh j)
        · exact ObjectProperty.prop_of_isZero
            (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
            (DerivedCategory.isZero_of_isLE _ (d - 1) j (by omega))
      have : K.IsLE d :=
        DerivedCategory.TStructure.t.isLE_of_le _ (c + ((n + 1 : ℕ) : ℤ)) d (by push_cast; omega)
      have hGE : RingedSpace.IsPerfect (X := X.toRingedSpace)
          ((DerivedCategory.TStructure.t.truncGE d).obj K) := by
        have := isIso_homologyMap_truncGEπ d d (le_refl d) K
        exact isPerfect_of_isCoherentHomology_of_isGE_of_isLE_self hX _ d
          (isCoherent_of_iso_oxMod
            (asIso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) d).map
              ((DerivedCategory.TStructure.t.truncGEπ d).app K))) (hcoh d))
      exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished
        ((DerivedCategory.TStructure.t.triangleLTGE d).obj K)
        (DerivedCategory.TStructure.t.triangleLTGE_distinguished d K) hLT hGE

/-- **A bounded object with coherent cohomology on a regular scheme is perfect.** Stated with the
bounds of the canonical t-structure: if `K` is `≥ a` and `≤ b` and all of its cohomology sheaves
are coherent, then `K` is perfect.

No relation between `a` and `b` is assumed; when `b < a` all cohomology of `K` vanishes, so `K`
is a zero object and perfect. -/
theorem isPerfect_of_isCoherentHomology_of_isGE_of_isLE {X : Scheme.{u}} (hX : IsRegular X)
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} X.toRingedSpace) j).obj K).IsCoherent) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) K := by
  by_cases hab : a ≤ b
  · have : K.IsLE (a + ((b - a).toNat : ℤ)) :=
      DerivedCategory.TStructure.t.isLE_of_le _ b _ (by omega)
    exact isPerfect_of_isCoherentHomology_of_isGE_of_isLE_add_natCast hX a (b - a).toNat K hcoh
  · exact RingedSpace.isPerfect_of_isZero
      (DerivedCategory.TStructure.t.isZero K b a (by omega))

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-- **The forward half of [Stacks, Tag 0FDC].** Let `X` be a regular scheme. Then every object of
`D^b_{Coh}(𝒪_X)` — every object of the derived category of `𝒪_X`-modules which is bounded and all
of whose cohomology sheaves are coherent — is perfect.

Quasi-compactness of `X` is not assumed. The proof is an induction on the length of the interval
carrying the cohomology of the object, with
`AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular` as its base case; that statement
needs no quasi-compactness either. -/
@[stacks 0FDC "forward direction: a bounded object with coherent cohomology on a regular scheme \
is perfect"]
theorem isPerfect_of_isBoundedCoherent_of_isRegular {X : Scheme.{u}} (hX : IsRegular X)
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) K) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hcoh⟩ := hK
  have : K.IsGE a := (DerivedCategory.isGE_iff K a).2 ha
  have : K.IsLE b := (DerivedCategory.isLE_iff K b).2 hb
  exact isPerfect_of_isCoherentHomology_of_isGE_of_isLE hX K a b hcoh

/-- **[Stacks, Tag 0FDC].** Let `X` be a quasi-compact regular scheme — equivalently, a
Noetherian regular scheme. Then the perfect objects of the derived category of `𝒪_X`-modules are
exactly the objects of `D^b_{Coh}(𝒪_X)`.

The forward implication is
`Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular`, which
does not use quasi-compactness; the converse is
`Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular`, which
does. -/
@[stacks 0FDC "the equivalence, on a quasi-compact regular scheme"]
theorem isPerfect_iff_isBoundedCoherent_of_isRegular {X : Scheme.{u}} (hX : IsRegular X)
    [CompactSpace X]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) K ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) K :=
  ⟨isBoundedCoherent_of_isPerfect_of_isRegular X hX K,
    isPerfect_of_isBoundedCoherent_of_isRegular hX K⟩

end Stacks.AlgebraicGeometry.PerfectCohomology

end
