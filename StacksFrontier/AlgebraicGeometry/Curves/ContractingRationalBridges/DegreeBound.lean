module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionLocalStructure
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
import all StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChange

/-!
# The degree of the dualizing sheaf on a component, and rational bridges

Let `X` be a proper scheme of dimension one over a field `k`, let `C ⊆ X` be an integral
one-dimensional closed subscheme whose global functions form a field `k' ⊇ k`, and let `X'` be
the closure of the complement of `C`. For an invertible extension `ℒ` of `𝒪_{C ∩ X'}` by `ω_C`
(for instance `ℒ = ω_X|_C`, by [Stacks, Tag 0E34]) one has
`deg ℒ = deg(C ∩ X') - 2 χ(C, 𝒪_C)`, and both `deg(C ∩ X')` and `χ(C, 𝒪_C)` are multiples of
`[k' : k]`. Hence if `deg ℒ ≤ 0` and `C ∩ X'` is nonempty, then `C` has genus zero and `C ∩ X'`
has degree one or two over `k'`: `C` is a rational tail or a rational bridge. This is the
numerical core of the proof of [Stacks, Tag 0E3P].

## Main results

* `AlgebraicGeometry.isRationalBridge_of_finrank_globalSections_intersection_eq_two`: an integral
  subcurve meeting the rest in a subscheme of degree two over `k'`, of genus zero, is a rational
  bridge.
* `AlgebraicGeometry.genus_eq_zero_and_finrank_le_two_of_invertibleCurveDegree_nonpos`: if
  `deg ℒ ≤ 0` and `C ∩ X'` is nonempty, then `g' = 0` and `Γ(C ∩ X', 𝒪)` has dimension one or
  two over `k'`.
* `AlgebraicGeometry.invertibleCurveDegree_pos_of_not_isRationalTail_of_not_isRationalBridge`:
  on a component that is neither a rational tail nor a rational bridge, `deg ℒ > 0`; its
  `_toSpecΓ` form takes `k' = Γ(C, 𝒪_C)`.
* `AlgebraicGeometry.invertibleCurveDegree_pullback_dualizingSheafOverField_pos_of_eq_univ`: on an
  irreducible reduced curve of genus `g ≥ 2`, `deg(ω_X|_C) = 2g - 2 > 0`.
* `AlgebraicGeometry.invertibleCurveDegree_pullback_reducedComponent_dualizingSheafOverField_pos`:
  `deg(ω_X|_C) > 0` on every one-dimensional component of a curve without rational tails or
  bridges, of genus at least two, given the sequence of [Stacks, Tag 0E34] and the invertibility
  of `ω_C`.
* `AlgebraicGeometry.isGorenstein_reducedComponent_of_hasAtWorstNodalSingularities`: a
  one-dimensional component of a nodal curve is Gorenstein ([Stacks, Tag 0E38] part (1) and
  [Stacks, Tag 0E37]).

## References

* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **An integral one-dimensional closed subcurve meeting the rest of the curve in a subscheme of
degree two over `k'`, with genus zero, is a rational bridge.** Let `C ⊊ X` be integral of
dimension one in a proper curve of dimension at most one over `k`, with `C ⟶ Spec k` factoring
through `Spec k'` and inducing `k' ≅ Γ(C, 𝒪_C)`. If `Γ(C ∩ X', 𝒪)` is two-dimensional over `k'`
and `C` has genus zero over `k'`, then `C` is a rational bridge: both `[k' : k]` and
`[Γ(C, 𝒪_C) : k]` are the dimension of `Γ(C, 𝒪_C)` over `k`, so the tower law over `k` turns the
dimension over `k'` into the dimension over `Γ(C, 𝒪_C)`. -/
theorem isRationalBridge_of_finrank_globalSections_intersection_eq_two
    [IsProper (X ↘ Spec (.of k))] (hX : topologicalKrullDim X ≤ 1)
    (C : X.IdealSheafData) [IsIntegral C.subscheme] (hCdim : topologicalKrullDim C.subscheme = 1)
    (hne : Nonempty (complementaryCurve C))
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = C.subschemeι ≫ (X ↘ Spec (.of k)))
    [IsProper f'] [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    (h2 :
      letI : Algebra k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k')).inv ≫ (Scheme.IdealSheafData.inclusion
          (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ f').appTop).hom.toAlgebra
      Module.finrank k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) = 2)
    (hg : genus f' = 0) :
    IsRationalBridge k X C := by
  let I := intersectionWithComplementaryCurveIdeal C
  let iC := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I)
  let fC := C.subschemeι ≫ (X ↘ Spec (.of k))
  refine ⟨inferInstance, ?_⟩
  let : Field Γ(C.subscheme, ⊤) := (isField_of_universallyClosed k fC).toField
  refine ⟨support_mem_irreducibleComponents_of_dimension_one C hX hCdim, hne, ?_,
    genus_eq_zero_of_genus_eq_zero f' _ hg⟩
  let algI : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let algC : Algebra k Γ(C.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop).hom.toAlgebra
  let algCI : Algebra Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := iC.appTop.hom.toAlgebra
  have hI : iC ≫ C.subschemeι = I.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι _
  have : IsScalarTower k Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom r =
      iC.appTop.hom (((Scheme.ΓSpecIso (.of k)).inv ≫
        (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom r)
    rw [← hI]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
  have : Module.Free Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := Module.Free.of_divisionRing _ _
  have htower := (Module.finrank_mul_finrank k Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤)).symm
  have hmul := finrank_globalSections_intersection_eq_mul C k' f' hf
  have hΓ := finrank_globalSections_eq_finrank_of_factor k' fC f' hf
  -- `Γ(C, 𝒪_C)` is a nonzero finite-dimensional `k`-vector space
  have : FiniteDimensional k Γ(C.subscheme, ⊤) := by
    have := forall_finiteDimensional_cohomologyOverField_unit k fC 0
    exact Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k fC
      (SheafOfModules.unit C.subscheme.ringCatSheaf)).toLinearEquiv
  have hpos : 0 < Module.finrank k Γ(C.subscheme, ⊤) := Module.finrank_pos
  change Module.finrank Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) = 2
  have h2' : Module.finrank k Γ(C.subscheme, ⊤) * Module.finrank Γ(C.subscheme, ⊤)
      Γ(I.subscheme, ⊤) = Module.finrank k Γ(C.subscheme, ⊤) * 2 := by
    rw [← htower, hmul, h2, hΓ]
  exact Nat.eq_of_mul_eq_mul_left hpos h2'

/-- **If `deg ℒ ≤ 0`, then `C` has genus zero and `C ∩ X'` has degree one or two over `k'`.** Let
`ℒ` be an invertible extension of `𝒪_{C ∩ X'}` by `ω_C` on a closed subscheme `C` of a proper
curve over `k`, where `C ⟶ Spec k` factors through `Spec k'` inducing `k' ≅ Γ(C, 𝒪_C)` and `ω_C`
is invertible over `k'`, and suppose `C ∩ X'` is nonempty. Writing `d = [k' : k]`,
`a = dim_{k'} Γ(C ∩ X', 𝒪)` and `g'` for the genus over `k'`, the degree is `d a - 2 d (1 - g')`,
so `deg ℒ ≤ 0` forces `a + 2 g' ≤ 2`, while `a ≥ 1` as `C ∩ X'` is nonempty. This is the
numerical step of [Stacks, Tag 0E3P]. -/
theorem genus_eq_zero_and_finrank_le_two_of_invertibleCurveDegree_nonpos
    [IsProper (X ↘ Spec (.of k))]
    (C : X.IdealSheafData) (hCdim : topologicalKrullDim C.subscheme ≤ 1)
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = C.subschemeι ≫ (X ↘ Spec (.of k)))
    [IsProper f'] [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f')]
    {S : ShortComplex C.subscheme.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2 S.X₂]
    (e₁ : S.X₁ ≅ Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ (X ↘ Spec (.of k))))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
        (SheafOfModules.unit _))
    (hX : topologicalKrullDim X ≤ 1)
    (hne : Nonempty (intersectionWithComplementaryCurveIdeal C).subscheme)
    (hle : invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim S.X₂ ≤ 0) :
    letI : Algebra k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k')).inv ≫ (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ f').appTop).hom.toAlgebra
    genus f' = 0 ∧
      (Module.finrank k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) = 1 ∨
        Module.finrank k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) = 2) := by
  let I := intersectionWithComplementaryCurveIdeal C
  let : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let : Algebra k' Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ I) ≫ f').appTop).hom.toAlgebra
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hdeg := invertibleCurveDegree_eq_sub_two_mul_of_shortExact C hCdim k' f' hf hS e₁ e₃
  have hP := finsum_alternating_finrank_unit_eq_finrank_of_topologicalKrullDim_le_zero
    (I.subschemeι ≫ (X ↘ Spec (.of k)))
    (topologicalKrullDim_intersectionWithComplementaryCurve_le_zero hX C)
  have hO := finsum_finrank_unit_eq_mul_one_sub_genus k' _ hCdim f' hf
  have hmul := finrank_globalSections_intersection_eq_mul C k' f' hf
  -- `Γ(C ∩ X', 𝒪)` is a nonzero finite-dimensional `k`-vector space
  obtain ⟨pt⟩ := hne
  have : Nontrivial Γ(I.subscheme, ⊤) :=
    Stacks.EmptyLimitCounterexample.nontrivial_Γ_of_nonempty I.subscheme pt
  have : FiniteDimensional k Γ(I.subscheme, ⊤) := by
    have := forall_finiteDimensional_cohomologyOverField_unit k
      (I.subschemeι ≫ (X ↘ Spec (.of k))) 0
    exact Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k
      (I.subschemeι ≫ (X ↘ Spec (.of k)))
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).toLinearEquiv
  have hpos : 0 < Module.finrank k Γ(I.subscheme, ⊤) := Module.finrank_pos
  rw [hmul] at hpos
  have hd : 0 < Module.finrank k k' := Nat.pos_of_mul_pos_right hpos
  have ha : 0 < Module.finrank k' Γ(I.subscheme, ⊤) := Nat.pos_of_mul_pos_left hpos
  rw [hdeg, hP, hO, hmul] at hle
  push_cast at hle
  have hd' : (0 : ℤ) < Module.finrank k k' := by exact_mod_cast hd
  have hsum : (Module.finrank k' Γ(I.subscheme, ⊤) : ℤ) + 2 * genus f' ≤ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h12 : Module.finrank k' Γ(I.subscheme, ⊤) = 1 ∨
      Module.finrank k' Γ(I.subscheme, ⊤) = 2 := by omega
  exact ⟨by omega, h12⟩

/-- **On a component that is neither a rational tail nor a rational bridge, `deg ℒ > 0`.** Let
`C ⊊ X` be an integral one-dimensional closed subscheme of a proper curve of dimension at most one
over `k`, meeting the closure `X'` of its complement, with `C ⟶ Spec k` factoring through
`Spec k'` and inducing `k' ≅ Γ(C, 𝒪_C)` and with `ω_C` invertible over `k'`, and let `ℒ` be an
invertible extension of `𝒪_{C ∩ X'}` by `ω_C`. If `deg ℒ ≤ 0`, then `C` has genus zero and
`C ∩ X'` has degree one or two over `k'`, so `C` is a rational tail or a rational bridge. For
`ℒ = ω_X|_C` and the sequence of [Stacks, Tag 0E34] this is the case analysis of the proof of
[Stacks, Tag 0E3P]. -/
theorem invertibleCurveDegree_pos_of_not_isRationalTail_of_not_isRationalBridge
    [IsProper (X ↘ Spec (.of k))] (hX : topologicalKrullDim X ≤ 1)
    (C : X.IdealSheafData) [IsIntegral C.subscheme] (hCdim : topologicalKrullDim C.subscheme = 1)
    (hcompl : Nonempty (complementaryCurve C))
    (hne : Nonempty (intersectionWithComplementaryCurveIdeal C).subscheme)
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = C.subschemeι ≫ (X ↘ Spec (.of k)))
    [IsProper f'] [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f')]
    {S : ShortComplex C.subscheme.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2 S.X₂]
    (e₁ : S.X₁ ≅ Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ (X ↘ Spec (.of k))))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
        (SheafOfModules.unit _))
    (htail : ¬ IsRationalTail k X C) (hbridge : ¬ IsRationalBridge k X C) :
    0 < invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim.le S.X₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hg, h1 | h2⟩ := genus_eq_zero_and_finrank_le_two_of_invertibleCurveDegree_nonpos C
    hCdim.le k' f' hf hS e₁ e₃ hX hne hcon
  · exact htail (isRationalTail_of_finrank_globalSections_intersection_eq_one hX C hCdim hcompl
      k' f' h1 hg)
  · exact hbridge (isRationalBridge_of_finrank_globalSections_intersection_eq_two hX C hCdim
      hcompl k' f' hf h2 hg)

/-- **A closed subscheme whose support is not everything has a nonempty complementary curve**:
a point off the support lies in the open complement, which maps into the scheme-theoretic
closure of the complement. -/
theorem nonempty_complementaryCurve_of_support_ne_univ (C : X.IdealSheafData)
    (hC : (C.support : Set X) ≠ Set.univ) : Nonempty (complementaryCurve C) := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hC
  exact ⟨(Scheme.Opens.ι C.support.compl).toImage ⟨x, hx⟩⟩

/-- **On an irreducible reduced curve, the degree of `ω_X` restricted to its only component is
`2g - 2`.** Let `X` be reduced, proper of dimension at most one over `k` with `H⁰(X, 𝒪_X) = k`
and invertible dualizing sheaf, and let `C` be the reduced closed subscheme on a closed subset
`Z` which is all of `X`. Then `C ⟶ X` is an isomorphism, so `deg(ω_X|_C) = deg(ω_X) = 2g - 2`
([Stacks, Tag 0C19]), which is positive for `g ≥ 2`. This is the irreducible case of the proof
of [Stacks, Tag 0E3P]. -/
theorem invertibleCurveDegree_pullback_dualizingSheafOverField_pos_of_eq_univ
    (k : Type u) [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] [IsReduced Y]
    (hdim : topologicalKrullDim Y ≤ 1)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f)]
    (hg : 2 ≤ genus f) (Z : TopologicalSpace.Closeds Y) (hZ : (Z : Set Y) = Set.univ)
    (hCdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ 1) :
    0 < invertibleCurveDegree k ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f) hCdim
      ((Scheme.Modules.pullback (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField f)) := by
  have hZ' : Z = ⊤ := TopologicalSpace.Closeds.ext hZ
  have hbot : Scheme.IdealSheafData.vanishingIdeal Z = ⊥ := by
    rw [hZ', Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
  have : IsIso (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr hbot
  rw [invertibleCurveDegree_pullback_of_isIso _ f hCdim hdim,
    invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k f hdim]
  omega

/-- **`deg(ω_X|_C) > 0` on a component that is neither a rational tail nor a rational bridge, over
the field of global functions of the component.** This is
`AlgebraicGeometry.invertibleCurveDegree_pos_of_not_isRationalTail_of_not_isRationalBridge` at
`k' = Γ(C, 𝒪_C)` and the canonical morphism `C ⟶ Spec Γ(C, 𝒪_C)`, which is the choice the proof
of [Stacks, Tag 0E3P] makes; only the invertibility of `ω_C` over `Γ(C, 𝒪_C)` remains as an
input. -/
theorem invertibleCurveDegree_pos_of_not_isRationalTail_of_not_isRationalBridge_toSpecΓ
    [IsProper (X ↘ Spec (.of k))] (hX : topologicalKrullDim X ≤ 1)
    (C : X.IdealSheafData) [IsIntegral C.subscheme] (hCdim : topologicalKrullDim C.subscheme = 1)
    (hcompl : Nonempty (complementaryCurve C))
    (hne : Nonempty (intersectionWithComplementaryCurveIdeal C).subscheme)
    (hωC : letI : Field Γ(C.subscheme, ⊤) :=
        (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
      haveI : IsProper C.subscheme.toSpecΓ :=
        Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ
          (C.subschemeι ≫ (X ↘ Spec (.of k)))
      SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField C.subscheme.toSpecΓ))
    {S : ShortComplex C.subscheme.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2 S.X₂]
    (e₁ : S.X₁ ≅ Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ (X ↘ Spec (.of k))))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
        (SheafOfModules.unit _))
    (htail : ¬ IsRationalTail k X C) (hbridge : ¬ IsRationalBridge k X C) :
    0 < invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim.le S.X₂ := by
  let fC := C.subschemeι ≫ (X ↘ Spec (.of k))
  let : Field Γ(C.subscheme, ⊤) := (isField_of_universallyClosed k fC).toField
  let : Algebra k Γ(C.subscheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop).hom.toAlgebra
  have : IsProper C.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fC
  have := hωC
  have : IsIso ((Scheme.ΓSpecIso (.of Γ(C.subscheme, ⊤))).inv ≫
      C.subscheme.toSpecΓ.appTop) := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have hf : C.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.subscheme, ⊤))) =
      fC := by
    change C.subscheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop) = fC
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  exact invertibleCurveDegree_pos_of_not_isRationalTail_of_not_isRationalBridge hX C hCdim hcompl
    hne Γ(C.subscheme, ⊤) C.subscheme.toSpecΓ hf hS e₁ e₃ htail hbridge

/-- **`deg(ω_X|_C) > 0` on every one-dimensional component, when `X` has no rational tails and no
rational bridges and genus at least two.** Let `X` be reduced, proper of dimension one over `k`
with `H⁰(X, 𝒪_X) = k` and invertible dualizing sheaf, without rational tails or rational bridges
and of genus `g ≥ 2`, and let `C` be a one-dimensional irreducible component with its reduced
induced structure. If `C = X`, then `deg(ω_X|_C) = 2g - 2 > 0`. Otherwise `C` meets the closure
`X'` of its complement, `X` being connected, and given that `ω_C` is invertible over
`Γ(C, 𝒪_C)` and the exact sequence `0 ⟶ ω_C ⟶ ω_X|_C ⟶ 𝒪_{C ∩ X'} ⟶ 0` of
[Stacks, Tag 0E34], the degree is positive because `C` is neither a rational tail nor a rational
bridge. This is the component-wise statement in the proof of [Stacks, Tag 0E3P]. -/
theorem invertibleCurveDegree_pullback_reducedComponent_dualizingSheafOverField_pos
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] [IsReduced X]
    (hdim : topologicalKrullDim X = 1)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))]
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C)
    (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (ζ : Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne X)
    (hωC : letI := Stacks.AlgebraicGeometry.ComponentDegrees.isIntegral_reducedComponent X ζ
      letI : Field Γ(Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ζ, ⊤) :=
        (isField_of_universallyClosed k
          (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι X ζ ≫
            (X ↘ Spec (.of k)))).toField
      haveI : IsProper (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ζ).toSpecΓ :=
        Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ
          (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι X ζ ≫ (X ↘ Spec (.of k)))
      SheafOfModules.IsInvertible
        (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ζ).presheaf
        (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ζ).ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField
          (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ζ).toSpecΓ))
    (hseq : ∃ (a : Stacks.Duality.dualizingSheafOverField
          (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι X ζ ≫ (X ↘ Spec (.of k))) ⟶
        (Scheme.Modules.pullback
          (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι X ζ)).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
      (b : (Scheme.Modules.pullback
          (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι X ζ)).obj
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
          (le_sup_left : Scheme.IdealSheafData.vanishingIdeal
              ⟨closure ({ζ.1} : Set X), isClosed_closure⟩ ≤
            intersectionWithComplementaryCurveIdeal (Scheme.IdealSheafData.vanishingIdeal
              ⟨closure ({ζ.1} : Set X), isClosed_closure⟩)))).obj (SheafOfModules.unit _))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact) :
    0 < invertibleCurveDegree k
      (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι X ζ ≫ (X ↘ Spec (.of k)))
      (Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_reducedComponent_le X
        hdim.le ζ)
      ((Scheme.Modules.pullback
        (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι X ζ)).obj
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) := by
  let Z : TopologicalSpace.Closeds X := ⟨closure ({ζ.1} : Set X), isClosed_closure⟩
  let C := Scheme.IdealSheafData.vanishingIdeal Z
  have : IsIntegral C.subscheme :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isIntegral_reducedComponent X ζ
  have hCdim : topologicalKrullDim C.subscheme = 1 :=
    Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_reducedComponent X ζ
  have hsupp : (C.support : Set X) = closure ({ζ.1} : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  by_cases hZ : (Z : Set X) = Set.univ
  · exact invertibleCurveDegree_pullback_dualizingSheafOverField_pos_of_eq_univ k
      (X ↘ Spec (.of k)) hdim.le hg Z hZ _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have hne : Nonempty (intersectionWithComplementaryCurveIdeal C).subscheme :=
    nonempty_intersectionWithComplementaryCurve_of_connectedSpace C
      ⟨ζ.1, hsupp ▸ subset_closure (Set.mem_singleton _)⟩ (hsupp ▸ hZ)
  obtain ⟨a, b, w, hS⟩ := hseq
  exact invertibleCurveDegree_pos_of_not_isRationalTail_of_not_isRationalBridge_toSpecΓ hdim.le C
    hCdim (nonempty_complementaryCurve_of_support_ne_univ C (hsupp ▸ hZ)) hne hωC hS
    (Iso.refl _) (Iso.refl _) (htail C) (hbridge C)

/-- **A one-dimensional irreducible component of a nodal curve is Gorenstein.** With its reduced
induced structure it is at-worst-nodal by [Stacks, Tag 0E38] part (1), and irreducible of
dimension one, so [Stacks, Tag 0E37] applies. This is what makes `ω_C` invertible in the proof of
[Stacks, Tag 0E3P]. -/
theorem isGorenstein_reducedComponent_of_hasAtWorstNodalSingularities
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hequidim : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (ζ : Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne X) :
    IsGorenstein (Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ζ) := by
  let C := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({ζ.1} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)
  have : IsIntegral C.subscheme :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isIntegral_reducedComponent X ζ
  have hCdim : topologicalKrullDim C.subscheme = 1 :=
    Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_reducedComponent X ζ
  have hCeq : TopologicalSpace.Equidimensional C.subscheme :=
    TopologicalSpace.Equidimensional.of_preirreducibleSpace C.subscheme
  let : C.subscheme.Over (Spec (.of k)) := ⟨C.subschemeι ≫ (X ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (C.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (C.subschemeι ≫ (X ↘ Spec (.of k))))
  exact Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities k C.subscheme hCeq hCdim
    (Stacks.Curves.hasAtWorstNodalSingularities_subscheme hequidim hdim hnodal C hCeq hCdim)

end AlgebraicGeometry

end
