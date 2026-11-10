module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceCrystallineComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamDegreeZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamTopDegree
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamTopPadic
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairUnitForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothPresentationCohomology07LH

public import StacksFrontier.Homology.CochainComplexDegreeZeroHomology

/-!
# The crystalline cohomology of `𝐀^r_{𝐅_p}` over `Spec(𝐙_p)`: [Stacks, Tag 07LK]

Let `A = 𝐙_p` with its divided power ideal `(p)` and its unique divided powers `γ`, let
`C = 𝐅_p[x_1, …, x_r]` with the presentation `C = P/J = P/pP`, `P = 𝐙_p[x_1, …, x_r]`, and let
`X = Spec(C)`, `S = Spec(A)`.  The example of [Stacks, Tag 07LK] notes that `pP` has divided
powers ([Stacks, Tag 07H1]), so that `D = P^∧` with its divided power ideal `(p)` is a situation as
in [Stacks, Section 60.17, Tag 07J7], and concludes that `RΓ(Cris(X/S), 𝒪_{X/S})` is represented by
the complex `D → Ω¹_D → Ω²_D → ⋯ → Ω^r_D`, see [Stacks, Proposition 60.21.3, Tag 07LG].  For
`r > 0` it draws four conclusions:

1. `H^j(Cris(X/S), 𝒪_{X/S})` is zero except in degrees `0, …, r`;
2. `H⁰(Cris(X/S), 𝒪_{X/S}) = 𝐙_p`;
3. `H^r(Cris(X/S), 𝒪_{X/S})` is infinite and is not a torsion abelian group;
4. `H^r(Cris(X/S), 𝒪_{X/S})` is not separated for the `p`-adic topology.

This module proves all of it for crystalline cohomology itself.  The comparison with the complex is
[Stacks, Lemma 60.21.4, Tag 07LH] — [Stacks, Tag 07LG] for an arbitrary smooth presentation —
applied to the crystal `𝒪_{X/S}` and to the example's presentation `P → Γ(X, 𝒪_X)`: the pair of
`𝒪_{X/S}` is `(D, d)` (`...SmallSite.pairUnitEquiv`,
`...SmallSite.crystalPairFormsConnection_unit_horizontal`), its base change to the completed
envelope of the presentation is the structure module of that envelope
(`Crystalline.FormsData.baseChangeUnitHom`), whose complex is the completed de Rham complex of the
envelope (`Crystalline.FormsData.unitComplexIso`), which is the example's complex
(`Crystalline.AffineSpaceCrystallineSetup.deRhamComplexNatIsoEnvelope`): the envelope of
`P → P/pP` is `P` itself.  The four conclusions are then read off the complex
(`...AffineSpaceDeRhamVanishing`, `...AffineSpaceDeRhamDegreeZero`,
`...AffineSpaceDeRhamTopDegree`).

Crystalline cohomology is `H^j(Cris(X/S), -) = Ext^j(ℤ, -)` on the small crystalline site
(`...SmallSite.cohomologyFunctor`), valued in abelian groups of the next universe; "represented by
the complex" is accordingly stated degreewise, `H^j(Cris(X/S), 𝒪_{X/S}) ≅ H^j(D → Ω¹_D → ⋯)` for
every `j`, the form in which [Stacks, Tag 07LG] and [Stacks, Tag 07LH] are available.

## Main results

* `Crystalline.AffineSpaceCrystallineSetup.crisCohomologyIso` — `RΓ(Cris(X/S), 𝒪_{X/S})` is
  computed by `D → Ω¹_D → ⋯ → Ω^r_D`.
* `Crystalline.AffineSpaceCrystallineSetup.isZero_crisCohomology` — conclusion (1).
* `Crystalline.AffineSpaceCrystallineSetup.crisCohomologyZeroIso` — conclusion (2).
* `Crystalline.AffineSpaceCrystallineSetup.infinite_and_not_isAddTorsion_crisCohomology_top` —
  conclusion (3).
* `Crystalline.AffineSpaceCrystallineSetup.not_isHausdorff_crisCohomology_top` — conclusion (4).

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DividedPowers
open Crystalline.GlobalCrystallineSituation.SmallSite

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

/-- **The crystalline structure sheaf `𝒪_{X/S}`** of the example, as a sheaf of modules over itself
on `Cris(X/S)`. -/
abbrev structureModule : SheafOfModules.{0} (structureSheaf T.situation) :=
  SheafOfModules.unit _

/-- **`H^j(Cris(X/S), 𝒪_{X/S})`**, for `X = Spec(𝐅_p[x_1, …, x_r])` over
`S = Spec(𝐙_p, (p), γ)`. -/
abbrev crisCohomology (j : ℕ) : AddCommGrpCat.{1} :=
  (cohomologyFunctor T.situation j).obj (abelianSheaf T.structureModule)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

/-- **The pair of `𝒪_{X/S}` is the structure module `(D, d)`**: `r ↦ r · 1` is a horizontal map
from the structure module of the completed envelope `D` of the canonical presentation to the pair
of [Stacks, Lemma 60.17.3, Tag 07JG] attached to the crystal `𝒪_{X/S}`
(`...SmallSite.crystalPairFormsConnection_unit_horizontal`), and it is bijective
(`...SmallSite.pairUnitLinear_bijective`). -/
def structureModulePairHom :
    FormsData.ConnModule.Hom
      (T.canonicalData.unitConnModule (FormsData.isPAdicallyComplete_ofDividedPowers _ _ _))
      (crystalPairConnModule T.isNilpotent_prime_sections
        (quasiCoherentCrystalUnit T.situation)) where
  toLinearMap := pairUnitLinear T.isNilpotent_prime_sections
  horizontal r := crystalPairFormsConnection_unit_horizontal T.isNilpotent_prime_sections r

/-- **`RΓ(Cris(X/S), 𝒪_{X/S})` is represented by the complex `D → Ω¹_D → Ω²_D → ⋯ → Ω^r_D`**, for
`X = Spec(𝐅_p[x_1, …, x_r])` over `S = Spec(𝐙_p, (p), γ)` and `D = P^∧`,
`P = 𝐙_p[x_1, …, x_r]`: in every degree `j`, `H^j(Cris(X/S), 𝒪_{X/S})` is the `j`-th cohomology
of the completed divided power de Rham complex of `D`
(`Crystalline.AffineSpaceCrystallineSetup.deRhamComplexNat`, whose terms vanish above `r`).

This is [Stacks, Lemma 60.21.4, Tag 07LH]
(`...SmallSite.smoothPresentationPair_computesCohomology`) for the crystal `𝒪_{X/S}` and the
example's presentation `P → Γ(X, 𝒪_X)`, which is smooth with
kernel `pP` (`Crystalline.AffineSpaceCrystallineSetup.presentation`), through any divided power
map of envelopes compatible with the augmentations (`Crystalline.exists_smoothPresentationMap`):
the pair of `𝒪_{X/S}` is `(D, d)` (`structureModulePairHom`), its base change to the completed
envelope of `P → P/pP` is the structure module of that envelope
(`Crystalline.FormsData.baseChangeUnitHom`), and the envelope of `P → P/pP` is `P`, `pP` having
divided powers by [Stacks, Tag 07H1] (`Crystalline.AffineSpaceCrystallineSetup.envelopeEquiv`), so
that the complex is the example's
(`Crystalline.AffineSpaceCrystallineSetup.unitBaseChangeComplexIso`).
-/
@[stacks 07LK "RΓ(Cris(X/S), O_{X/S}) is represented by the complex D -> Omega^1_D -> ... -> \
Omega^r_D, D = Z_p[x_1, ..., x_r]^wedge, degreewise: H^j(Cris(X/S), O_{X/S}) is the j-th \
cohomology of that complex for every j, by 07LG/07LH for the presentation C = P/pP"]
theorem crisCohomologyIso (j : ℕ) :
    Nonempty (T.crisCohomology j ≅
      AddCommGrpCat.uliftFunctor.{1, 0}.obj (T.deRhamComplexNat.homology j)) := by
  obtain ⟨a, ha, haug⟩ := exists_smoothPresentationMap T.affineSit T.presentation
    T.presentation_surjective
  obtain ⟨e⟩ := smoothPresentationPair_computesCohomology T.isNilpotent_prime_sections
    (quasiCoherentCrystalUnit T.situation) T.presentation T.presentation_surjective a ha haug j
  let g : FormsData.Hom T.canonicalData T.presentationData :=
    FormsData.Hom.ofCompletion T.affineSit.p T.affineSit.A _
      (canonicalPrime_nilpotent T.affineSit 0) _
      (presentationEnvelope_prime_nilpotent T.affineSit T.presentation T.presentation_surjective)
      a ha
  have := FormsData.ConnModule.isIso_complexMap _
    (FormsData.ConnModule.baseChangeMap_bijective g T.structureModulePairHom
      (pairUnitLinear_bijective T.isNilpotent_prime_sections))
  exact ⟨e.symm ≪≫ AddCommGrpCat.uliftFunctor.{1, 0}.mapIso
    (HomologicalComplex.homologyMapIso ((asIso (FormsData.ConnModule.complexMap
      (FormsData.ConnModule.baseChangeMap g T.structureModulePairHom))).symm ≪≫
      T.unitBaseChangeComplexIso g) j)⟩

/-- The kernel of the degree zero differential of the displayed complex, read as a subgroup of
its degree zero term. -/
theorem ker_completedDifferential_zero_eq :
    (LinearMap.ker (T.completedDifferential 0)).toAddSubgroup =
      AddMonoidHom.ker (T.deRhamComplexNat.d 0 1).hom := by
  ext x
  change T.completedDifferential 0 x = 0 ↔ T.deRhamComplexNat.d 0 1 x = 0
  exact (iff_of_eq (congrArg (fun y : T.completedForms 1 ↦ y = 0) (T.deRhamComplexNat_d 0 x))).symm

/-- The degree zero homology of the displayed complex is `𝐙_p`: it is the kernel of the degree zero
differential, `Crystalline.AffineSpaceCrystallineSetup.kerCompletedDifferentialZeroEquiv`. -/
def homologyZeroIsoBase : T.deRhamComplexNat.homology 0 ≅ AddCommGrpCat.of T.A :=
  CochainComplex.homologyZeroIsoOfKerEq T.deRhamComplexNat
      (LinearMap.ker (T.completedDifferential 0)).toAddSubgroup
      T.ker_completedDifferential_zero_eq ≪≫
    (T.kerCompletedDifferentialZeroEquiv.toAddEquiv).toAddCommGrpIso

/-- The top crystalline cohomology `H^r(Cris(X/S), 𝒪_{X/S})` is, as an abelian group, the top
cohomology of the displayed complex. -/
def crisCohomologyEquivHomology (j : ℕ)
    (e : T.crisCohomology j ≅ AddCommGrpCat.uliftFunctor.{1, 0}.obj
      (T.deRhamComplexNat.homology j)) :
    T.crisCohomology j ≃+ T.deRhamComplexNat.homology j :=
  e.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift

/-- **Conclusion (1) of [Stacks, Tag 07LK]: the crystalline cohomology of the crystalline
structure sheaf of `X = 𝐀^r_{𝐅_p}` over `S = Spec(𝐙_p)` is zero except in degrees `0, …, r`.**
Cohomology is indexed by `ℕ`, so this is the vanishing above `r`; it holds for every `r` (the
source states its conclusions under `r > 0`).  The term `Ω^i_D` of the complex itself vanishes for
`i > r`. -/
@[stacks 07LK "conclusion (1): H^j(Cris(X/S), O_{X/S}) = 0 for j > r, X = A^r_{F_p}, \
S = Spec(Z_p)"]
theorem isZero_crisCohomology {j : ℕ} (hj : T.r < j) : IsZero (T.crisCohomology j) := by
  obtain ⟨e⟩ := T.crisCohomologyIso j
  have : Subsingleton (T.deRhamComplexNat.homology j) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp (T.isZero_homology_deRhamComplexNat hj)
  exact (AddCommGrpCat.isZero_iff_subsingleton.mpr
    (inferInstanceAs (Subsingleton (ULift.{1, 0} (T.deRhamComplexNat.homology j))))).of_iso e

/-- **Conclusion (2) of [Stacks, Tag 07LK]: `H⁰(Cris(X/S), 𝒪_{X/S}) = 𝐙_p`**, for every `r` (the
source states its conclusions under `r > 0`): the kernel of `d : D → Ω¹_D` consists of the
constants, an element of `𝐙_p[x_1, …, x_r]^∧` all of whose partial derivatives vanish being a
constant.  The universe lift is the one `H^j(Cris(X/S), -)` is valued in. -/
@[stacks 07LK "conclusion (2): H^0(Cris(X/S), O_{X/S}) = Z_p"]
theorem crisCohomologyZeroIso :
    Nonempty (T.crisCohomology 0 ≅ AddCommGrpCat.of (ULift.{1, 0} T.A)) := by
  obtain ⟨e⟩ := T.crisCohomologyIso 0
  exact ⟨e ≪≫ AddCommGrpCat.uliftFunctor.{1, 0}.mapIso T.homologyZeroIsoBase⟩

/-- The top crystalline cohomology is, as an abelian group, the top cohomology of the complex. -/
private theorem nonempty_addEquiv_crisCohomology_top :
    Nonempty (T.crisCohomology T.r ≃+ T.deRhamComplexNat.homology T.r) :=
  (T.crisCohomologyIso T.r).map (T.crisCohomologyEquivHomology T.r)

/-- **Conclusion (3) of [Stacks, Tag 07LK]: for `r > 0` the cohomology group
`H^r(Cris(X/S), 𝒪_{X/S})` is infinite and is not a torsion abelian group.** -/
@[stacks 07LK "conclusion (3): for r > 0, H^r(Cris(X/S), O_{X/S}) is infinite and is not a \
torsion abelian group"]
theorem infinite_and_not_isAddTorsion_crisCohomology_top (hr : 0 < T.r) :
    Infinite (T.crisCohomology T.r) ∧ ¬ IsAddTorsion (T.crisCohomology T.r) := by
  obtain ⟨φ⟩ := T.nonempty_addEquiv_crisCohomology_top
  refine ⟨?_, fun h ↦ T.not_isTorsion_homology_top hr fun x ↦ ?_⟩
  · have := T.infinite_homology_top hr
    exact Infinite.of_injective φ.symm φ.symm.injective
  · obtain ⟨n, hn, hzero⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
      (show IsOfFinAddOrder (φ.symm x) from h _)
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
    rw [← φ.apply_symm_apply x, ← map_nsmul, hzero, map_zero]

/-- **Conclusion (4) of [Stacks, Tag 07LK]: for `r > 0` the cohomology group
`H^r(Cris(X/S), 𝒪_{X/S})` is not separated for the `p`-adic topology.** -/
@[stacks 07LK "conclusion (4): for r > 0, H^r(Cris(X/S), O_{X/S}) is not separated for the \
p-adic topology"]
theorem not_isHausdorff_crisCohomology_top (hr : 0 < T.r) :
    ¬ IsHausdorff (Ideal.span {(T.p : ℤ)}) (T.crisCohomology T.r) := by
  obtain ⟨φ⟩ := T.nonempty_addEquiv_crisCohomology_top
  intro h
  refine T.not_isHausdorff_homology_top hr ⟨fun x hx ↦ ?_⟩
  simpa using congrArg φ (h.haus (φ.symm x) fun n ↦ SModEq.zero.mpr
    (Submodule.smul_top_le_comap_smul_top _ φ.symm.toIntLinearEquiv.toLinearMap
      (SModEq.zero.mp (hx n))))

/-- **The closing remark of [Stacks, Tag 07LK] on `η`, in the sense its argument shows.**  For
`r > 0` the class of `η = ∑_{e > 0} p^e x_1^{p^e - 1} ⋯ x_r^{p^e - 1} dx_1 ∧ ⋯ ∧ dx_r` in
`H^r(Cris(X/S), 𝒪_{X/S})` generates a copy of `𝐙_p` (no nonzero `𝐙_p`-multiple of `η`, in
particular no `p^N η`, is exact), and it is divisible by every power of `p`; but no additive map
`𝐐_p → H^r(Cris(X/S), 𝒪_{X/S})` sends `1` to it.  The source says that `η` "generates" a copy of
`𝐐_p`, in quotation marks, and this theorem formalizes that remark in the sense its argument
shows: an injective `𝐙_p → H^r` through `[η]`, with `[η] ∈ ⋂_t p^t H^r`.  The third clause records
that the quotation marks are needed: there is no additive `𝐐_p → H^r` extending it, because the
elements `x` with `p x = [η]` cannot themselves be divisible by every power of `p`
(`Crystalline.AffineSpaceCrystallineSetup.not_exists_pow_smul_eq_etaTop`). -/
@[stacks 07LK "closing remark on eta, the quoted 'generates a copy of Q_p' in the sense its \
argument shows: for r > 0 an injective Z_p -> H^r(Cris(X/S), O_{X/S}) through the class of eta, \
with [eta] in p^t H^r for every t, and no additive Q_p -> H^r extending it"]
theorem exists_padicInt_crisCohomology_top (hr : 0 < T.r) :
    ∃ f : ℤ_[T.p] →+ T.crisCohomology T.r, Function.Injective f ∧
      (∀ t : ℕ, ∃ y, f 1 = (T.p ^ t) • y) ∧
      ¬ ∃ g : ℚ_[T.p] →+ T.crisCohomology T.r, g 1 = f 1 := by
  obtain ⟨s, hs⟩ : ∃ s, T.r = s + 1 := ⟨T.r - 1, by omega⟩
  obtain ⟨φ⟩ := T.nonempty_addEquiv_crisCohomology_top
  let c : ℤ_[T.p] →+ T.deRhamComplexNat.homology T.r :=
    (T.homologyClassTop hs).comp
      ((smulAddHom ℤ_[T.p] (T.completedForms (s + 1))).flip (T.etaTop hs))
  have hc : ∀ a, c a = T.homologyClassTop hs (a • T.etaTop hs) := fun _ ↦ rfl
  refine ⟨φ.symm.toAddMonoidHom.comp c, ?_, fun t ↦ ?_, ?_⟩
  · exact φ.symm.injective.comp (T.injective_homologyClassTop_smul_etaTop hs)
  · obtain ⟨x, ⟨w, hw⟩, ξ, hξ⟩ := T.exists_series_eta_eq_add hs t
    refine ⟨φ.symm (T.homologyClassTop hs ξ), ?_⟩
    change φ.symm (c 1) = _
    rw [hc, one_smul, ← map_nsmul, ← map_nsmul]
    congr 1
    have hx : T.homologyClassTop hs x = 0 := (T.homologyClassTop_eq_zero_iff hs x).mpr ⟨w, hw⟩
    rw [show T.etaTop hs = T.series hs (fun e ↦ T.p ^ e - 1) from rfl, hξ, map_add, hx, zero_add]
  · rintro ⟨g, hg⟩
    refine T.not_exists_padic_homology_top hs ⟨φ.toAddMonoidHom.comp g, ?_⟩
    change φ (g 1) = _
    rw [hg]
    change φ (φ.symm (c 1)) = _
    rw [AddEquiv.apply_symm_apply, hc, one_smul]

end AffineSpaceCrystallineSetup

end Crystalline

end
