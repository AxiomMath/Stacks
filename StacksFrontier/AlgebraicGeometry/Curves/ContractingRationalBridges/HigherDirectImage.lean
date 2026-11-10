module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionAffine
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.UnionStructureSquare
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusZeroVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact
public import StacksFrontier.AlgebraicGeometry.PointImageHigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison

/-!
# The higher direct images of the structure sheaf along a contraction of a rational bridge vanish

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, let `C ⊆ X` be a rational bridge (Tag 0E3M), write `X'` for the
scheme-theoretic closure of `X \ C` and `k' = Γ(C, 𝒪_C)`, and let `c : X ⟶ Y` be a contraction of
`C`. Then

`R ⁿ c_* 𝒪_X = 0` for every `n > 0`,

whose degree-one case is the vanishing asserted by [Stacks, Tag 0E3M].

## Main results

* `Stacks.Curves.isZero_Hgroup_unit_bridge` — `H ⁿ(C, 𝒪_C) = 0` for `n > 0`, for a rational
  bridge.
* `Stacks.Curves.isZero_rightDerived_pushforward_ambientStructureSheaf_bridge` — `R ⁿ c_* 𝒪_X = 0`
  for every `n > 0`.
* `Stacks.Curves.isZero_rightDerived_one_pushforward_ambientStructureSheaf_bridge` — its
  degree-one case, which is the vanishing [Stacks, Tag 0E3M] asserts.

## The argument

It is the argument the source gives, and the one carried out for a rational tail in
`Curves/DirectImage/RationalTailHigherDirectImage.lean`, run on the union sequence
`0 ⟶ 𝒪_X ⟶ 𝒪_C ⊞ 𝒪_{X'} ⟶ 𝒪_{C ∩ X'} ⟶ 0` of [Stacks, Tag 0C4J]:

* `R ⁿ c_* 𝒪_C = 0`, because the contraction factors `C ⟶ X ⟶ Y` through `Spec k'`, a one-point
  scheme — `k'` is a field, `Stacks.Curves.isField_globalSections_bridge` — so the higher direct
  image is the cohomology of `C`, and `H ⁿ(C, 𝒪_C) = 0` for `n > 0`: in degree one by the
  genus-zero clause of the rational bridge, read over `k'` as the definition has it, and above it
  by Grothendieck vanishing.
* `R ⁿ c_* 𝒪_{X'} = 0` and `R ⁿ c_* 𝒪_{C ∩ X'} = 0`, because `c|_{X'}` is affine
  (`Stacks.Curves.isAffineHom_complementaryCurveι_comp_contraction`) — this is where the bridge
  differs from the tail, whose contraction restricts to the identity on `X'`.
* in degree one the connecting map is killed by the surjectivity of
  `c_* 𝒪_{X'} ⟶ c_* 𝒪_{C ∩ X'}`, which is the source's reason: `𝒪_{X'} ⟶ 𝒪_{C ∩ X'}` is
  surjective and `c|_{X'}` is affine, so the direct image stays surjective. For a tail the same
  step went through the *first* summand, functions restricted from `X`; that route is not
  available here, since `c_* 𝒪_X = 𝒪_Y` does not surject onto `c_* 𝒪_{C ∩ X'}` — the local ring
  of `Y` at the image point maps into `k'` inside `k''`.

Identifying the scheme-theoretic union of `C` and `X'` with `X` is the first clause of
`AlgebraicGeometry.IsContractionOfRationalBridge` and needs nothing further.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-! ### The cohomology of a rational bridge -/

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **A rational bridge has `H ¹(C, 𝒪_C) = 0`.** The bridge has genus zero over the field
`k' = Γ(C, 𝒪_C)` of its own global functions, which is how
`AlgebraicGeometry.IsRationalBridge` states the condition, and it is proper over `Spec k'`; so
`AlgebraicGeometry.isZero_Hgroup_unit_one_of_genus_eq_zero` applies over `k'`. -/
theorem isZero_Hgroup_unit_one_bridge {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    Limits.IsZero (Hgroup C.subscheme.ringCatSheaf ⊤ 1
      (SheafOfModules.unit C.subscheme.ringCatSheaf)) := by
  have := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  have : IsProper C.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
  exact isZero_Hgroup_unit_one_of_genus_eq_zero Γ(C.subscheme, ⊤) C.subscheme.toSpecΓ
    hC.genus_eq_zero

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **A rational bridge of a proper one-dimensional curve has `H ⁿ(C, 𝒪_C) = 0` for every
`n > 0`.** In degree one this is the genus-zero clause, through
`Stacks.Curves.isZero_Hgroup_unit_one_bridge`. In the higher degrees it is Grothendieck
vanishing, [Stacks, Tag 02UZ]: the bridge is a closed subscheme of `X`, hence proper over `k` and
of dimension at most that of `X`, which is one. -/
theorem isZero_Hgroup_unit_bridge (hdim : topologicalKrullDim X = 1)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (Hgroup C.subscheme.ringCatSheaf ⊤ n
      (SheafOfModules.unit C.subscheme.ringCatSheaf)) := by
  match n, hn with
  | 1, _ => exact isZero_Hgroup_unit_one_bridge hC
  | (m + 2), _ =>
    refine (isZero_cohomologyOverField_iff_isZero_hgroup k
      (C.subschemeι ≫ (X ↘ Spec (.of k))) _ (m + 2)).1 ?_
    refine isZero_cohomologyOverField_of_topologicalKrullDim_le k
      (C.subschemeι ≫ (X ↘ Spec (.of k))) _ (d := 1) ?_ (by omega)
    have hle := C.subschemeι.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    rw [hdim] at hle
    exact_mod_cast hle

/-! ### The three terms of the union sequence -/

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **A contraction of a rational bridge has constant underlying map on the bridge.** The second
restriction clause of `AlgebraicGeometry.IsContractionOfRationalBridge` factors `C ⟶ X ⟶ Y`
through `Spec k'`, and `k'` is a field
(`Stacks.Curves.isField_globalSections_bridge`), so that spectrum is a single point. -/
theorem base_const_of_isContractionOfRationalBridge
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (u v : C.subscheme) :
    (C.subschemeι ≫ c).base u = (C.subschemeι ≫ c).base v := by
  have := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  obtain ⟨-, a, b, -, -, hbc⟩ := hc
  rw [hbc]
  have : Unique (PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)) := PrimeSpectrum.instUnique
  change b.base (C.subscheme.toSpecΓ.base u) = b.base (C.subscheme.toSpecΓ.base v)
  congr 1
  exact Subsingleton.elim (α := PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)) _ _

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **`R ⁿ c_* 𝒪_C = 0` in every positive degree, for a contraction `c` of a rational bridge
`C`.** The contraction carries all of `C` to one point, so the higher direct image is the
cohomology of `C`, and that vanishes above degree zero by
`Stacks.Curves.isZero_Hgroup_unit_bridge`. -/
theorem isZero_rightDerived_pushforward_structureSheaf_bridge
    (hdim : topologicalKrullDim X = 1)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (pushedForwardStructureSheaf C.subschemeι)) :=
  Stacks.PointImageHigherDirectImage.isZero_rightDerived_pushforward_pushforward_of_const
    C.subschemeι c (structureSheafModule C.subscheme)
    (base_const_of_isContractionOfRationalBridge hc) n hn
    (isZero_Hgroup_unit_bridge hdim hC n hn)

/-- `R ⁿ c_*` vanishes on the pushforward of the structure sheaf along `j` when `j` and `j ≫ c`
are affine. -/
private theorem isZero_rightDerived_pushforward_structureSheaf_of_isAffineHom {Z W Y : Scheme.{u}}
    (j : Z ⟶ W) (c : W ⟶ Y) [IsAffineHom j] [IsAffineHom (j ≫ c)] (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (pushedForwardStructureSheaf j)) :=
  have : (structureSheafModule Z).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp j c
    (structureSheafModule Z) n hn

/-- **`R ⁿ c_* 𝒪_{X'} = 0` in every positive degree, for a contraction `c` of a rational
bridge**, where `X'` is the scheme-theoretic closure of the complement of the bridge. The
contraction restricts to an affine morphism on `X'`
(`Stacks.Curves.isAffineHom_complementaryCurveι_comp_contraction`), so both legs of
`X' ⟶ X ⟶ Y` are affine and
`Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp` applies with
[Stacks, Tag 01XC] at each. No cohomological input about `X'` is needed. -/
theorem isZero_rightDerived_pushforward_structureSheaf_complementaryCurve_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (pushedForwardStructureSheaf (complementaryCurveIdeal C).subschemeι)) := by
  have : IsAffineHom ((complementaryCurveIdeal C).subschemeι ≫ c) :=
    isAffineHom_complementaryCurveι_comp_contraction hdim hnodal hc
  exact isZero_rightDerived_pushforward_structureSheaf_of_isAffineHom
    (complementaryCurveIdeal C).subschemeι c n hn

/-- **`R ⁿ c_* 𝒪_{C ∩ X'} = 0` in every positive degree, for a contraction `c` of a rational
bridge.** The intersection is a closed subscheme of `X'`, which the contraction carries into `Y`
by an affine morphism, so both legs of `C ∩ X' ⟶ X ⟶ Y` are affine. -/
theorem isZero_rightDerived_pushforward_structureSheaf_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (pushedForwardStructureSheaf (Scheme.IdealSheafData.inclusion
        (I := complementaryCurveIdeal C) (J := intersectionWithComplementaryCurveIdeal C)
        le_sup_right ≫ (complementaryCurveIdeal C).subschemeι))) := by
  have hint := isAffineHom_intersection_subschemeι_comp_contraction hdim hnodal hc
  rw [← Scheme.IdealSheafData.inclusion_subschemeι (I := complementaryCurveIdeal C)
    (J := intersectionWithComplementaryCurveIdeal C) le_sup_right] at hint
  exact isZero_rightDerived_pushforward_structureSheaf_of_isAffineHom _ c n hn

/-- **`R ⁿ c_*(𝒪_{X'} ⊞ 𝒪_C) = 0` in every positive degree, for a contraction `c` of a rational
bridge.** The biproduct is split, so the vanishing transfers from the two summands by
`Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂`. -/
theorem isZero_rightDerived_pushforward_biprod_structureSheaves_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (pushedForwardStructureSheaf (complementaryCurveIdeal C).subschemeι ⊞
        pushedForwardStructureSheaf C.subschemeι)) :=
  Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂
    (ShortComplex.Splitting.ofHasBinaryBiproduct
      (pushedForwardStructureSheaf (complementaryCurveIdeal C).subschemeι)
      (pushedForwardStructureSheaf C.subschemeι)).shortExact
    (Scheme.Modules.pushforward c) n
    (isZero_rightDerived_pushforward_structureSheaf_complementaryCurve_bridge hdim hnodal hc n hn)
    (isZero_rightDerived_pushforward_structureSheaf_bridge hdim hc n hn)

/-! ### The degree-zero surjectivity -/

/-- **A contraction of a rational bridge carries the second arrow of the union sequence of
[Stacks, Tag 0C4J] to an epimorphism.** This is the source's reason: `𝒪_{X'} ⟶ 𝒪_{C ∩ X'}` is
surjective and the contraction is affine on `X'`. -/
theorem epi_pushforward_map_unionBiprodToIntersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    Epi ((Scheme.Modules.pushforward c).map
      (unionBiprodToIntersection C (complementaryCurveIdeal C) hc.1)) :=
  have := isAffineHom_complementaryCurveι_comp_contraction hdim hnodal hc
  epi_pushforward_map_unionBiprodToIntersection C (complementaryCurveIdeal C) hc.1 c

/-- The same in the shape the long exact sequence of higher direct images consumes it: the zeroth
right derived functor of a direct image is the direct image itself. -/
theorem epi_rightDerived_zero_pushforward_map_unionBiprodToIntersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    Epi (((Scheme.Modules.pushforward c).rightDerived 0).map
      (unionBiprodToIntersection C (complementaryCurveIdeal C) hc.1)) := by
  have := epi_pushforward_map_unionBiprodToIntersection_bridge hdim hnodal hc
  rw [← NatIso.naturality_2
    (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso c)
    (unionBiprodToIntersection C (complementaryCurveIdeal C) hc.1)]
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.app
      (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso c) _).isIso_hom)
    (epi_comp' this (@IsIso.epi_of_iso _ _ _ _ _ (Iso.app
      (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso c) _).isIso_inv))

/-! ### The vanishing -/

/-- **`R ⁿ c_* 𝒪_X = 0` in every positive degree, for a contraction `c` of a rational bridge.**
The union sequence of [Stacks, Tag 0C4J] is applied to the bridge and the closure of its
complement, which cover `X` scheme-theoretically — the first clause of
`AlgebraicGeometry.IsContractionOfRationalBridge`. In degree one the connecting map is killed by
`Stacks.Curves.epi_rightDerived_zero_pushforward_map_unionBiprodToIntersection_bridge`; from
degree two on the term it leaves already vanishes. -/
theorem isZero_rightDerived_pushforward_ambientStructureSheaf_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (structureSheafModule X)) := by
  obtain ⟨hz, hSE⟩ :=
    unionStructureSheafShortComplex_shortExact C (complementaryCurveIdeal C) hc.1
  match n, hn with
  | (m + 1), _ =>
    refine Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁_of_epi hSE
      (Scheme.Modules.pushforward c) m ?_
      (isZero_rightDerived_pushforward_biprod_structureSheaves_bridge hdim hnodal hc (m + 1)
        m.succ_pos)
    match m with
    | 0 =>
      exact epi_rightDerived_zero_pushforward_map_unionBiprodToIntersection_bridge hdim hnodal hc
    | (p + 1) =>
      exact ⟨fun g h _ =>
        (isZero_rightDerived_pushforward_structureSheaf_intersection_bridge hdim hnodal hc
          (p + 1) p.succ_pos).eq_of_src g h⟩

/-- **`R ¹ c_* 𝒪_X = 0` for a contraction `c` of a rational bridge**, the degree in which
[Stacks, Tag 0E3M] asserts the vanishing. -/
theorem isZero_rightDerived_one_pushforward_ambientStructureSheaf_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (structureSheafModule X)) :=
  isZero_rightDerived_pushforward_ambientStructureSheaf_bridge hdim hnodal hc 1 Nat.one_pos

/-- The structure sheaf of `X` is acyclic for the direct image along a contraction of a rational
bridge, which is the shape the collapse isomorphism `Stacks.AcyclicCollapse.objIso` consumes. -/
theorem rightAcyclic_pushforward_ambientStructureSheaf_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
  isZero_rightDerived_pushforward_ambientStructureSheaf_bridge hdim hnodal hc n hn

end Stacks.Curves

end
