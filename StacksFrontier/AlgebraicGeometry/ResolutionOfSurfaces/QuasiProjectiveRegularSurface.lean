module

public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Projective
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TowerProjective
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.NoetherianFlatStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveCategoryClosure
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.QuasiProjectiveContraction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMapNoetherian
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular surfaces are quasi-projective

Let `S` be a Noetherian scheme and `f : X ⟶ S` a separated morphism of finite type with `X`
regular of dimension at most two. Then `f` is quasi-projective ([Stacks, Tag 0C5N]); if `f` is
proper, it is projective ([Stacks, Tag 0C5P]).

The proof is the source's. Chow's lemma ([Stacks, Tag 0200]) gives a proper modification
`π : X' ⟶ X`, an isomorphism over a dense open `U`, with `X'` immersed in a projective space over
`S`. The inverse of `π` over `U` is an `X`-rational map from `X` to `X'`, which is proper over
`X`; a sequence `Xₙ → ⋯ → X₀ = X` of blowups at closed points resolves it ([Stacks, Tag 0C5H]),
so `Xₙ ⟶ X` factors through `X'`. Each blowup is projective ([Stacks, Tag 02NS]), hence so is
`Xₙ ⟶ X` ([Stacks, Tag 0C4P]) and so is `Xₙ ⟶ X'` ([Stacks, Tag 0C4Q]); as `X' ⟶ S` is
H-quasi-projective, `Xₙ ⟶ S` is quasi-projective ([Stacks, Tag 0C4M]). Finally each blowup at a
closed point with regular two-dimensional local ring is the contraction of its exceptional curve,
which is an exceptional curve of the first kind; a contraction of an exceptional curve of the first
kind on a quasi-projective scheme is quasi-projective ([Stacks, Tag 0C2N]) and contractions are
unique ([Stacks, Tag 0C5K]), so quasi-projectivity descends along the sequence.

## Main results

* `AlgebraicGeometry.isQuasiProjective_of_isRegular_of_topologicalKrullDim_le_two` — [Stacks,
  Tag 0C5N].
* `AlgebraicGeometry.isProjective_of_isRegular_of_topologicalKrullDim_le_two` — [Stacks,
  Tag 0C5P].
* `AlgebraicGeometry.isQuasiProjective_of_isQuasiProjective_blowUpToBase_comp` — quasi-projectivity
  descends along a blowup at a closed point with regular two-dimensional local ring.
* `Stacks.ResolutionOfSurfaces.PointBlowupChain.isNoetherian_and_regular` — the invariants of a
  sequence of blowups at closed points of a regular surface.
* `Stacks.ResolutionOfSurfaces.PointBlowupChain.isProjective` — such a sequence is projective.

## References

* [Stacks Project, Tag 0C5N](https://stacks.math.columbia.edu/tag/0C5N)
* [Stacks Project, Tag 0C5P](https://stacks.math.columbia.edu/tag/0C5P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme of finite type over a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_finiteType {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- **Quasi-projectivity descends along a blowup at a closed point with regular two-dimensional
local ring.** The exceptional divisor of that blowup is an exceptional curve of the first kind
(`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal`, the
remark of [Stacks, Section 0C2I]). It lies over a single point of the base, so
by [Stacks, Tag 0C2N] (2) it has a contraction which is quasi-projective over the base; the blowup
itself is a contraction of it, and by [Stacks, Tag 0C5K] and [Stacks, Tag 0C5J] the two
contractions are the same scheme over the base. -/
theorem isQuasiProjective_of_isQuasiProjective_blowUpToBase_comp {W S : Scheme.{u}}
    [IsNoetherian S] (g : W ⟶ S) [LocallyOfFiniteType g] [QuasiCompact g] (w : W)
    (hw : IsClosed ({w} : Set W)) (hreg : IsRegularLocalRing (W.presheaf.stalk w))
    (hdim : ringKrullDim (W.presheaf.stalk w) = 2)
    (h : IsQuasiProjective
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ g)) :
    IsQuasiProjective g := by
  have : IsNoetherian W := isNoetherian_of_finiteType g
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
  obtain ⟨e, hEk⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal
      w hw hreg hdim
  have : LocallyOfFiniteType (blowUpToBase M ≫ g) := h.1.1
  have : QuasiCompact (blowUpToBase M ≫ g) := h.1.2
  have hb : IsContractionOfExceptionalCurve (exceptionalIdeal M) (blowUpToBase M) :=
    isContractionOfExceptionalCurve_blowUpToBase w hw hreg hdim
  -- the exceptional curve lies over the image of `w`
  have hfib : ∀ x ∈ ((exceptionalIdeal M).support : Set (blowUp M)),
      (blowUpToBase M ≫ g).base x = g.base w := by
    intro x hx
    change g.base ((blowUpToBase M).base x) = g.base w
    rw [IsContractionOfExceptionalCurve.eq_centre_of_mem_support (hx := hw) rfl hx]
  obtain ⟨X', b, g', hb', hbg, hg'⟩ :=
    exists_isContractionOfExceptionalCurve_isQuasiProjective (blowUpToBase M ≫ g) hEk (g.base w)
      hfib h
  -- the two contractions agree
  let φ := contractionIso hb' hb
  have hconst : ∃ y : S, ∀ z : (exceptionalIdeal M).subscheme,
      (blowUpToBase M ≫ g) ((exceptionalIdeal M).subschemeι z) = y := by
    obtain ⟨y, hy⟩ := hb.exists_const_on_subscheme
    exact ⟨g y, fun z => by rw [Scheme.Hom.comp_apply, hy z]⟩
  obtain ⟨ψ, -, hψu⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve
    (exceptionalIdeal M) (blowUpToBase M) hb (blowUpToBase M ≫ g) hconst
  have e1 : blowUpToBase M ≫ φ.inv ≫ g' = blowUpToBase M ≫ g := by
    rw [← Category.assoc, contractionIso_inv_comp, hbg]
  have h1 : φ.inv ≫ g' = g := by
    rw [hψu (φ.inv ≫ g') e1, hψu g rfl]
  rw [← h1]
  exact IsQuasiProjective.comp φ.inv g' (isQuasiProjective_of_isImmersion φ.inv) hg'

end AlgebraicGeometry

namespace Stacks.ResolutionOfSurfaces

/-- **The invariants of a sequence of blowups at closed points of a regular surface.** Let `X`
be a Noetherian scheme all of whose local rings are regular, and `T` a set of closed points of
`X` whose local rings have dimension two. For a sequence `p : Z ⟶ X` of blowups at closed points
lying over `T`, the scheme `Z` is Noetherian with regular local rings, `p` is proper, and the
local ring of `Z` at a closed point lying over `T` has dimension two. -/
theorem PointBlowupChain.isNoetherian_and_regular {X : Scheme.{u}} [IsNoetherian X] {T : Set X}
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hT : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2)
    {Z : Scheme.{u}} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p) :
    IsNoetherian Z ∧ IsProper p ∧ (∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) ∧
      ∀ z : Z, IsClosed ({z} : Set Z) → p.base z ∈ T →
        ringKrullDim (Z.presheaf.stalk z) = 2 := by
  induction hp with
  | refl =>
    exact ⟨inferInstance, inferInstance, hreg, fun z _ hz => hT z hz⟩
  | @step W q hh w hw hwT ih =>
    obtain ⟨hWN, hhp, hWreg, hWdim⟩ := ih
    set M := Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩
    have hwdim : ringKrullDim (W.presheaf.stalk w) = 2 := hWdim w hw hwT
    refine ⟨isNoetherian_of_finiteType (blowUpToBase M), inferInstance, fun z => ?_,
      fun z hz hzT => ?_⟩
    · exact isRegularLocalRing_stalk_blowUp_of_isRegularLocalRing_stalk_blowUpToBase M w hw rfl
        (hWreg w) hwdim z (hWreg _)
    · have hbz : IsClosed ({(blowUpToBase M).base z} : Set _) := by
        rw [← Set.image_singleton]
        exact (blowUpToBase M).isClosedMap _ hz
      exact ringKrullDim_stalk_blowUp_eq_two_of_isClosed M w hw rfl (hWreg w) hwdim z hz
        (hWdim _ hbz (by simpa [Scheme.Hom.comp_base] using hzT))

/-- **A sequence of blowups at closed points of a Noetherian scheme is projective** ([Stacks,
Tag 02NS] for each blowup and [Stacks, Tag 0C4P] for the composite). -/
theorem PointBlowupChain.isProjective {X : Scheme.{u}} [IsNoetherian X] {T : Set X}
    {Z : Scheme.{u}} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p) : IsProjective p := by
  induction hp with
  | refl => exact isProjective_id X
  | @step W q hh w hw hwT ih =>
    have : IsNoetherian W := by
      have := ih.isProper
      exact isNoetherian_of_finiteType q
    exact IsProjective.comp (isProjective_blowUpToBase _
      (Scheme.IdealSheafData.isFiniteType_of_isLocallyNoetherian _)) ih

/-- **Quasi-projectivity descends along a sequence of blowups at closed points of a regular
surface**: if `p : Z ⟶ X` is a sequence of blowups at closed points lying over a set of points
with two-dimensional local rings and `p ≫ f` is quasi-projective, then so is `f`. -/
theorem PointBlowupChain.isQuasiProjective_of_comp {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] {T : Set X}
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hT : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2)
    {Z : Scheme.{u}} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p)
    (hZ : IsQuasiProjective (p ≫ f)) : IsQuasiProjective f := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  induction hp with
  | refl => simpa using hZ
  | @step W q hh w hw hwT ih =>
    obtain ⟨hWN, hhp, hWreg, hWdim⟩ := hh.isNoetherian_and_regular hreg hT
    exact ih (isQuasiProjective_of_isQuasiProjective_blowUpToBase_comp (q ≫ f) w hw (hWreg w)
      (hWdim w hw hwT) (by simpa using hZ))

end Stacks.ResolutionOfSurfaces

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0C5N.** Let `S` be a Noetherian scheme and `f : X ⟶ S` a separated
morphism of finite type with `X` regular of dimension (at most) two. Then `f` is quasi-projective.

The source assumes `dim X = 2`; the argument only uses `dim X ≤ 2`, which is what is assumed. -/
@[stacks 0C5N]
theorem isQuasiProjective_of_isRegular_of_topologicalKrullDim_le_two
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X ≤ 2) : IsQuasiProjective f := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have hstalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    (((isRegular_tfae X).out 1 2 rfl rfl).mp hreg).2
  -- Chow's lemma
  obtain ⟨n, X', π, i, U, hπ, -, hi, hcomm, hU, hiso⟩ := hasDenseChowModification f
  let : X.Over X := ⟨𝟙 X⟩
  let : X'.Over X := ⟨π⟩
  have : IsProper (X' ↘ X) := hπ
  -- the inverse of `π` over `U`, as an `X`-rational map
  let φ : X.PartialMap X' := ⟨U, hU, inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι⟩
  have : φ.IsOver X := Scheme.PartialMap.isOver_iff.mpr (by
    change (inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι) ≫ π = U.ι ≫ 𝟙 X
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Category.comp_id])
  -- resolve it by a sequence of blowups at closed points ([Stacks, Tag 0C5H])
  obtain ⟨T, Z, p, h, -, hTdim, -, hchain, hS, -⟩ :=
    Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_isNoetherian
      (S := X) hstalk (fun x => (ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim)
      φ
  have hS' : h ≫ π = p := by
    have := hS
    change h ≫ π = p ≫ 𝟙 X at this
    simpa using this
  have : IsNoetherian X' := isNoetherian_of_finiteType π
  have hh : IsProjective h := IsProjective.of_comp h π (by rw [hS']; exact hchain.isProjective)
  have hX' : IsQuasiProjective (π ≫ f) := by
    rw [hcomm]
    exact isQuasiProjective_of_isHQuasiProjective _
      ⟨n, i, hi, quasiCompact_of_noetherianSpace_source i, rfl⟩
  have hZ : IsQuasiProjective (p ≫ f) := by
    rw [← hS', Category.assoc]
    exact IsQuasiProjective.comp h (π ≫ f) (isQuasiProjective_of_isProjective hh) hX'
  exact Stacks.ResolutionOfSurfaces.PointBlowupChain.isQuasiProjective_of_comp f hstalk hTdim
    hchain hZ

/-- **Stacks Project, Tag 0C5P.** Let `S` be a Noetherian scheme and `f : X ⟶ S` a proper morphism
with `X` regular of dimension (at most) two. Then `f` is projective.

This is [Stacks, Tag 0C5N] together with [Stacks, Tag 0BCL]: a proper quasi-projective morphism
to a quasi-compact quasi-separated scheme is projective. The source assumes `dim X = 2`; the
argument only uses `dim X ≤ 2`. -/
@[stacks 0C5P, sga "7 X 1.10" "more general"]
theorem isProjective_of_isRegular_of_topologicalKrullDim_le_two {X S : Scheme.{u}}
    [IsNoetherian S] (f : X ⟶ S) [IsProper f] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X ≤ 2) : IsProjective f :=
  (isProjective_iff_isQuasiProjective_and_isProper f).mpr
    ⟨isQuasiProjective_of_isRegular_of_topologicalKrullDim_le_two f hreg hdim, inferInstance⟩

end AlgebraicGeometry

end
