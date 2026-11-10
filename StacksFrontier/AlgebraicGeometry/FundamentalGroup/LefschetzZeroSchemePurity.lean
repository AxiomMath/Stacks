module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzFiniteLocallyFreeFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreConditionSpecialCases
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Chain
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeFiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.CoverEquivalenceInvariance
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lefschetz for the fundamental group: the zero scheme of an ample section, with purity

Let `k` be a field, let `X` be a proper scheme over `k`, let `L` be an ample invertible
`𝒪_X`-module, let `s ∈ Γ(X, L)` and let `Y = Z(s)` be the zero scheme of `s`. Assume

* `depth(𝒪_{X, x}) + dim({x}‾) > 2` for every `x ∈ X ∖ Y`, and
* purity holds for `𝒪_{X, x}` at every **closed** `x ∈ X ∖ Y`.

[Stacks, Tag 0ELE] asserts that the restriction functor `FÉt_X ⟶ FÉt_Y` is an equivalence, and
that if `X` — or equivalently `Y` — is connected then `π₁(Y, y‾) ⟶ π₁(X, y‾)` is an isomorphism
for every geometric point `y‾` of `Y`.

This file carries out that argument.

## Full faithfulness: [Stacks, Tag 0ELC], first statement, with nothing carried

`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_depthAddDim` is the
first statement of [Stacks, Tag 0ELC] — `FÉt_X ⟶ FÉt_Y` is fully faithful under
`depth(𝒪_{X, x}) + dim({x}‾) > 1` outside `Y` — proved with no statement of the source taken as a
hypothesis. It is the full faithfulness that the source uses in Tag 0ELE, and it is also
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_isProper`, which reaches
it through the formalized form of [Stacks, Tag 0EL2] instead. The module documentation of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeRestriction` lists four
reasons
why the formalized [Stacks, Tag 0EL1] cannot be consumed there directly; the chain used here goes
around all four:

`depth + dim > 1` outside `Y`
`⟹` the same bound for every power `L^{⊗ m}`, since `depth(𝒪_{X, x}) ≤ depth((L^{⊗ m})_x)`
    (`Stacks.Algebraization.depth_stalk_le_sheafDepthAt`), the stalks of an invertible module
    being free of rank one
`⟹` the degree-zero comparison of [Stacks, Tag 0EL1] at `σ = 1` is invertible for `L^{⊗ m}`
    (`Stacks.Algebraization.isIso_zeroSchemeComparison_of_isProper`)
`⟹` condition (2) of [Stacks, Tag 0EKP] for the closed immersion `Y ⟶ X`, by
    `Stacks.Algebraization.isInfinitesimalSectionsComplete_of_isIso_comparison`
`⟹` condition (4) of Tag 0EKP, by `Stacks.Algebraization.sectionsComplete_chain`,
    whose implications `(2) ⇒ (3) ⇒ (4)` are unconditional
`⟹` full faithfulness, by [Stacks, Tag 0EL8].

## The purity step

The complement of an open neighbourhood `V` of `Y` consists of **closed** points of `X`: the
closure of a point outside `V` misses `Y`, hence lies in the nonvanishing open `X_s`, which is
affine because `L` is ample, and a closed subscheme of `X` that is proper over `k` and affine is
finite over `k`, hence discrete. That is the footnote of the source, proved as
`Stacks.Algebraization.closure_singleton_eq_of_notMem_of_support_zeroScheme_subset`. So the purity
hypothesis, which speaks only of closed points, applies at every point outside `V`, and
[Stacks, Tag 0EY7] extends every finite étale cover of `V` to one of `X`
(`Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_opens_of_hasPurity`). This is the step for
which the source quotes Limits, Lemma [Stacks, Tag 0BQ5] once for each of the finitely many points
of `X ∖ V`.

## The essential image over a neighbourhood

Essential surjectivity of `FÉt_X ⟶ FÉt_Y` needs, by the source's argument, that **every finite
étale cover of `Y` be the restriction of a finite étale cover of some open neighbourhood of `Y`**.
That is the essential-image half of [Stacks, Tag 0ELD], and it is exactly the second half of
`Stacks.FundamentalGroup.finiteEtaleColimitEquivalence_zeroScheme_of_depth`
(`StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeFiniteEtaleEquivalence`),
which proves Tag 0ELD at the bound `depth(𝒪_{X, x}) + dim({x}‾) > 2` — the very bound Tag 0ELE
assumes. Underneath it are the algebraization of [Stacks, Tag 0EL7]
(`Stacks.Algebraization.completionEquivalence_finiteLocallyFree_of_two_lt_depth_add_dimClosure`)
and the construction in the proof of [Stacks, Tag 0EK1]
(`Stacks.FundamentalGroup.exists_finiteEtale_neighbourhood_extension_of_completion`): lift the
cover `A ⟶ Y` to the infinitesimal neighbourhoods `Y_n` by [Stacks, Tag 0BQB], push the structure
sheaves forward to obtain a finite locally free object of `Coh(X, I)`, algebraize it, transport
the algebra structure by full faithfulness of completion, and take the relative spectrum, which
is étale near `Y` by [Stacks, Tag 0A43].

The three theorems named `*_of_hasPurity` below take that statement as a hypothesis
`halgebraize`, and the three that follow them supply it from Tag 0ELD and so state Tag 0ELE at
the source's own hypotheses.

## Main results

* `Stacks.FundamentalGroup.sectionsCompleteAmplePowers_zeroScheme_of_depthAddDim` — condition (2)
  of [Stacks, Tag 0EKP] for `Y ⟶ X`, from the depth hypothesis.
* `Stacks.FundamentalGroup.completionFullyFaithfulOnFiniteLocallyFree_zeroScheme_of_depthAddDim` —
  condition (4) of [Stacks, Tag 0EKP]: completion along the ideal of `Y` is fully faithful on the
  finite locally free coherent modules.
* `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_depthAddDim` —
  **[Stacks, Tag 0ELC], first statement**, with nothing carried.
* `Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_opens_of_hasPurity` — the purity step.
* `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity` — the
  first conclusion of [Stacks, Tag 0ELE], granted `halgebraize`.
* `Stacks.FundamentalGroup.connectedSpace_zeroScheme_iff_of_hasPurity` and
  `Stacks.FundamentalGroup.fundamentalGroupEquiv_zeroScheme_of_hasPurity` — the "or equivalently"
  and the second conclusion of [Stacks, Tag 0ELE], granted `halgebraize`.
* `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity_of_depth`,
  `Stacks.FundamentalGroup.connectedSpace_zeroScheme_iff_of_hasPurity_of_depth` and
  `Stacks.FundamentalGroup.fundamentalGroupEquiv_zeroScheme_of_hasPurity_of_depth` —
  **[Stacks, Tag 0ELE]**: the same three statements at the source's own hypotheses.

## References

* [Stacks Project, Tag 0ELE](https://stacks.math.columbia.edu/tag/0ELE)
* [Stacks Project, Tag 0ELC](https://stacks.math.columbia.edu/tag/0ELC)
* [Stacks Project, Tag 0ELD](https://stacks.math.columbia.edu/tag/0ELD)
* [Stacks Project, Tag 0EY7](https://stacks.math.columbia.edu/tag/0EY7)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0BQA](https://stacks.math.columbia.edu/tag/0BQA)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

/-! ### The depth and dimension hypothesis -/

/-- Raising the depth keeps the bound `depth + dim > 1`: the inclusion of the extended naturals
into the extended integers is monotone, and so is addition there. -/
private theorem one_lt_enatToEInt_add_of_le {d d' : ℕ∞} {c : WithBot ℕ∞} (hd : d ≤ d')
    (h : Stacks.Algebraization.enatToEInt d + Stacks.Algebraization.krullDimToEInt c >
      ((1 : ℤ) : EInt)) :
    Stacks.Algebraization.enatToEInt d' + Stacks.Algebraization.krullDimToEInt c >
      ((1 : ℤ) : EInt) :=
  lt_of_lt_of_le h (add_le_add (Stacks.Algebraization.enatToEInt_mono hd) le_rfl)

/-- **The hypothesis of [Stacks, Tag 0ELE] implies the hypothesis of [Stacks, Tag 0ELC].** The
bound `depth(𝒪_{X, x}) + dim({x}‾) > 2` of Tag 0ELE, spelled in the `WithBot ℕ∞` arithmetic of
`Stacks.Algebraization.localDepthAddDimClosure` in which the formalized [Stacks, Tag 0EL7] states
it, gives the bound `> 1` of Tag 0ELC, spelled in the `EInt` arithmetic of
`Stacks.FundamentalGroup.DepthAddDimGtOneOutsideSupport`. -/
public theorem depthAddDimGtOneOutsideSupport_of_two_lt_localDepthAddDimClosure
    {X : Scheme.{u}} {Y : X.IdealSheafData}
    (h : ∀ x : X, x ∉ (Y.support : Set X) →
      ((2 : ℕ) : WithBot ℕ∞) < Stacks.Algebraization.localDepthAddDimClosure X x) :
    DepthAddDimGtOneOutsideSupport X Y :=
  fun x hx => Stacks.Algebraization.one_lt_enatToEInt_add_of_two_lt le_rfl (h x hx)

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [IsProper f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))

/-! ### Full faithfulness of restriction, with nothing carried -/

include f hL in
/-- **The sections of a power of `L` are the inverse limit of their restrictions to the
infinitesimal neighbourhoods of `Y = Z(s)`.** The depth hypothesis is on `𝒪_X`, while
[Stacks, Tag 0EL1] wants it on the module whose sections are compared; the two agree because the
stalks of `L^{⊗ m}` are free of rank one over `𝒪_{X, x}`, so
`Stacks.Algebraization.depth_stalk_le_sheafDepthAt` transports the bound. Tag 0EL1 in degree zero
at `σ = 1` then makes the comparison invertible, and
`Stacks.Algebraization.isInfinitesimalSectionsComplete_of_isIso_comparison` reads that as
completeness of the sections. -/
public theorem isInfinitesimalSectionsComplete_tensorPowerModules_zeroScheme_of_depthAddDim
    (hdepth : DepthAddDimGtOneOutsideSupport X (zeroScheme X L s)) (m : ℕ) :
    Stacks.Algebraization.IsInfinitesimalSectionsComplete (zeroScheme X L s).subschemeι
      (Scheme.Modules.tensorPowerModules L (m : ℤ)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := Stacks.Algebraization.isCoherent_tensorPowerModules X L (m : ℤ)
  have : (Scheme.Modules.tensorPowerModules L (m : ℤ)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hd := fun x => @Stacks.Algebraization.depth_stalk_le_sheafDepthAt X _
    (Scheme.Modules.tensorPowerModules L (m : ℤ))
    (Stacks.Algebraization.isFiniteLocallyFree_tensorPowerModules X L m) x
  have hdep : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      Stacks.Algebraization.enatToEInt
          (Stacks.Algebraization.sheafDepthAt
            (Scheme.Modules.tensorPowerModules L (m : ℤ)) x) +
        Stacks.Algebraization.krullDimToEInt (Stacks.Algebraization.dimClosureAt X x) >
          ((1 : ℤ) : EInt) :=
    fun x hx => one_lt_enatToEInt_add_of_le (hd x) (hdepth x hx)
  exact Stacks.Algebraization.isInfinitesimalSectionsComplete_of_isIso_comparison _ _
    (zeroScheme X L s) (Stacks.Algebraization.zeroSchemeTowerIdeal_succ_le X L s)
    (Scheme.IdealSheafData.ker_subschemeι _).symm
    (Stacks.Algebraization.isIso_zeroSchemeComparison_of_isProper k f L hL s _ 1 hdep 0
      (by norm_num))

include f hL in
/-- **Condition (2) of [Stacks, Tag 0EKP] for the zero scheme of an ample section.** The ample
module is `L` itself, and every one of its powers has complete sections by
`isInfinitesimalSectionsComplete_tensorPowerModules_zeroScheme_of_depthAddDim` above, so the
bound `N` may be taken to be `0`. -/
public theorem sectionsCompleteAmplePowers_zeroScheme_of_depthAddDim
    (hdepth : DepthAddDimGtOneOutsideSupport X (zeroScheme X L s)) :
    SectionsCompleteAmplePowers (zeroScheme X L s).subschemeι :=
  ⟨L, inferInstance, (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mpr hL, 0,
    fun m _ =>
      isInfinitesimalSectionsComplete_tensorPowerModules_zeroScheme_of_depthAddDim
        k f L hL s hdepth m⟩

include f hL in
/-- **Condition (4) of [Stacks, Tag 0EKP] for the zero scheme of an ample section:** completion
along the ideal sheaf of `Y = Z(s)` is fully faithful on the finite locally free coherent
`𝒪_X`-modules. This is condition (2) above followed by the implications `(2) ⇒ (3) ⇒ (4)` of
`Stacks.Algebraization.sectionsComplete_chain`, both of which are unconditional.

`IsNoetherian X` is an instance argument rather than a derived fact only because the statement of
`Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree` needs it; it follows from the
other hypotheses by `Stacks.FundamentalGroup.isNoetherian_of_isProper_of_isAmple`, as the next
theorem shows. -/
@[sga "2 X 2.2" "Example 2.2(i)"]
public theorem completionFullyFaithfulOnFiniteLocallyFree_zeroScheme_of_depthAddDim
    [IsNoetherian X] (hdepth : DepthAddDimGtOneOutsideSupport X (zeroScheme X L s)) :
    Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X
      (zeroScheme X L s).subschemeι.ker := by
  have hchain := Stacks.Algebraization.sectionsComplete_chain (zeroScheme X L s).subschemeι
  exact hchain.2.2.1
    (hchain.2.1 (sectionsCompleteAmplePowers_zeroScheme_of_depthAddDim k f L hL s hdepth))

/-- A proper scheme over a field with an ample invertible module in the sense of
`Stacks.Ample.IsAmple` is Noetherian. -/
private theorem isNoetherian_of_isProper_of_isAmple' (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) : IsNoetherian X :=
  isNoetherian_of_isProper_of_isAmple k f L
    ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mpr hL)

include f hL in
/-- **[Stacks, Tag 0ELC], first statement.** Let `k` be a field, `X` a proper scheme over `k`,
`L` an ample invertible `𝒪_X`-module, `s ∈ Γ(X, L)` and `Y = Z(s)` the zero scheme of `s`. If
`depth(𝒪_{X, x}) + dim({x}‾) > 1` at every point `x` of `X` outside `Y`, then the restriction
functor `FÉt_X ⟶ FÉt_Y` is fully faithful.

The statement is that of
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_isProper`, and
**nothing is carried here**: the source's appeal to
Algebraic and Formal Geometry, Proposition [Stacks, Tag 0EL1] is
`Stacks.Algebraization.isIso_zeroSchemeComparison_of_isProper`, and the route from there to full
faithfulness runs through conditions (2) and (4) of [Stacks, Tag 0EKP] rather than through
[Stacks, Tag 0EJZ]; see the module documentation for the chain. This is the full faithfulness that
the source uses in [Stacks, Tag 0ELE].

`CategoryTheory.Functor.FullyFaithful` carries the inverse map on hom sets as data, so full
faithfulness is recorded as `Nonempty _.FullyFaithful`. `X` is
Noetherian by `Stacks.FundamentalGroup.isNoetherian_of_isProper_of_isAmple`. -/
@[stacks 0ELC "first statement: restriction FÉt_X → FÉt_Y to the zero scheme of a section of an \
ample invertible module is fully faithful. Nothing is carried: Stacks 0EL1 is \
isIso_zeroSchemeComparison_of_isProper, and the passage from it to full faithfulness is the \
formalized Stacks 0EKP chain followed by Stacks 0EL8", sga "1 X 2.13" "partial"]
public theorem fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_depthAddDim
    (hdepth : DepthAddDimGtOneOutsideSupport X (zeroScheme X L s)) :
    Nonempty (finiteEtaleBaseChange (zeroScheme X L s).subschemeι).FullyFaithful := by
  have := isNoetherian_of_isProper_of_isAmple' k f L hL
  exact fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithfulOnFiniteLocallyFree _
    (completionFullyFaithfulOnFiniteLocallyFree_zeroScheme_of_depthAddDim k f L hL s hdepth)

/-! ### The purity step -/

include f hL in
/-- **Purity at the closed points off `Y` is purity at every point off a neighbourhood of `Y`.**
The closure of a point outside an open `V ⊇ Y` misses `Y`, hence lies in the nonvanishing open
`X_s`, which is affine because `L` is ample; a closed subscheme of `X` that is proper over `k` and
affine is finite over `k`, hence discrete. This is the footnote of [Stacks, Tag 0ELE], proved as
`Stacks.Algebraization.closure_singleton_eq_of_notMem_of_support_zeroScheme_subset`. -/
public theorem hasPurity_of_notMem_opens_of_hasPurity_of_isClosed
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x))
    {V : X.Opens} (hV : ((zeroScheme X L s).support : Set X) ⊆ (V : Set X)) {x : X}
    (hx : x ∉ (V : Set X)) :
    AlgebraicGeometry.HasPurity (X.presheaf.stalk x) :=
  hpurity x (fun hY => hx (hV hY))
    (closure_eq_iff_isClosed.mp
      (Stacks.Algebraization.closure_singleton_eq_of_notMem_of_support_zeroScheme_subset
        k f L hL s hV hx))

include f hL in
/-- **Every finite étale cover of an open neighbourhood of `Y = Z(s)` extends to `X`.** Every
point outside the neighbourhood is a closed point off `Y`, so purity holds there by
`Stacks.FundamentalGroup.hasPurity_of_notMem_opens_of_hasPurity_of_isClosed`, and
[Stacks, Tag 0EY7] extends the cover. -/
public theorem essSurj_finiteEtaleBaseChange_opens_of_hasPurity
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x))
    (V : X.Opens) (hV : ((zeroScheme X L s).support : Set X) ⊆ (V : Set X)) :
    (finiteEtaleBaseChange V.ι).EssSurj := by
  have := isNoetherian_of_isProper_of_isAmple' k f L hL
  refine AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_hasPurity V.ι fun x hx => ?_
  rw [Scheme.Opens.opensRange_ι] at hx
  exact hasPurity_of_notMem_opens_of_hasPurity_of_isClosed k f L hL s hpurity hV hx

/-! ### Tag 0ELE, granted the essential image over a neighbourhood -/

include f hL in
/-- **Essential surjectivity of `FÉt_X ⟶ FÉt_Y`.** A finite étale cover of `Y` is, by
`halgebraize`, the restriction of a finite étale cover of some open neighbourhood `V` of `Y`, and
that cover extends to `X` by the purity step; the extension restricts to the given cover because
restriction to `Y` factors through restriction to `V`. -/
public theorem essSurj_finiteEtaleBaseChange_zeroScheme_of_hasPurity
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x))
    (halgebraize : ∀ A : FiniteEtaleOver (zeroScheme X L s).subscheme,
      ∃ (W : Neighborhood X (zeroScheme X L s))
        (U : FiniteEtaleOver (Neighborhood.open X (zeroScheme X L s) W).toScheme),
        Nonempty ((finiteEtaleBaseChange
          (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).obj U ≅ A)) :
    (finiteEtaleBaseChange (zeroScheme X L s).subschemeι).EssSurj := by
  apply Functor.EssSurj.mk
  intro A
  obtain ⟨W, U, ⟨e⟩⟩ := halgebraize A
  have hess := essSurj_finiteEtaleBaseChange_opens_of_hasPurity k f L hL s hpurity
    (Neighborhood.open X (zeroScheme X L s) W)
    (Neighborhood.support_subset_open X (zeroScheme X L s) W)
  obtain ⟨U', hU'⟩ := hess.mem_essImage U
  obtain ⟨e'⟩ := hU'
  refine ⟨U', ⟨?_⟩⟩
  exact (finiteEtaleBaseChangeComp (Neighborhood.toSchemeHom X (zeroScheme X L s) W)
      (Neighborhood.open X (zeroScheme X L s) W).ι (zeroScheme X L s).subschemeι
      (Neighborhood.toSchemeHom_fac X (zeroScheme X L s) W).symm).app U' ≪≫
    (finiteEtaleBaseChange
      (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).mapIso e' ≪≫ e

include f hL in
/-- **[Stacks, Tag 0ELE], the first conclusion, granted the essential image over a
neighbourhood.** Let `k` be a field, `X` a proper scheme over `k`, `L` an ample invertible
`𝒪_X`-module, `s ∈ Γ(X, L)` and `Y = Z(s)`. If `depth(𝒪_{X, x}) + dim({x}‾) > 2` for every
`x ∈ X ∖ Y` and purity holds for `𝒪_{X, x}` at every closed `x ∈ X ∖ Y`, then the restriction
functor `FÉt_X ⟶ FÉt_Y` is an equivalence.

Full faithfulness is
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_depthAddDim`, proved
with nothing carried; essential surjectivity is the purity step applied to the neighbourhood
supplied by `halgebraize`, the essential-image half of [Stacks, Tag 0ELD] described in the module
documentation. For the same conclusion with `halgebraize` discharged from the depth hypothesis,
see `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity_of_depth`
below. -/
public theorem isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      ((2 : ℕ) : WithBot ℕ∞) < Stacks.Algebraization.localDepthAddDimClosure X x)
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x))
    (halgebraize : ∀ A : FiniteEtaleOver (zeroScheme X L s).subscheme,
      ∃ (W : Neighborhood X (zeroScheme X L s))
        (U : FiniteEtaleOver (Neighborhood.open X (zeroScheme X L s) W).toScheme),
        Nonempty ((finiteEtaleBaseChange
          (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).obj U ≅ A)) :
    (finiteEtaleBaseChange (zeroScheme X L s).subschemeι).IsEquivalence := by
  obtain ⟨hff⟩ := fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_depthAddDim k f L hL s
    (depthAddDimGtOneOutsideSupport_of_two_lt_localDepthAddDimClosure hdepth)
  let _ : (finiteEtaleBaseChange (zeroScheme X L s).subschemeι).Faithful := hff.faithful
  let _ : (finiteEtaleBaseChange (zeroScheme X L s).subschemeι).Full := hff.full
  exact ⟨inferInstance, inferInstance,
    essSurj_finiteEtaleBaseChange_zeroScheme_of_hasPurity k f L hL s hpurity halgebraize⟩

include f hL in
/-- **[Stacks, Tag 0ELE], the "or equivalently".** In the situation of
`Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity` the zero
scheme is connected exactly when `X` is, by [Stacks, Tag 0BQA] part (2). `X` is quasi-compact and
quasi-separated because it is Noetherian, and so is `Y`, which is proper over `k` as well. -/
public theorem connectedSpace_zeroScheme_iff_of_hasPurity
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      ((2 : ℕ) : WithBot ℕ∞) < Stacks.Algebraization.localDepthAddDimClosure X x)
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x))
    (halgebraize : ∀ A : FiniteEtaleOver (zeroScheme X L s).subscheme,
      ∃ (W : Neighborhood X (zeroScheme X L s))
        (U : FiniteEtaleOver (Neighborhood.open X (zeroScheme X L s) W).toScheme),
        Nonempty ((finiteEtaleBaseChange
          (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).obj U ≅ A)) :
    ConnectedSpace (zeroScheme X L s).subscheme ↔ ConnectedSpace X := by
  have := isNoetherian_of_isProper_of_isAmple' k f L hL
  have : CompactSpace (zeroScheme X L s).subscheme :=
    AlgebraicGeometry.compactSpace_of_universallyClosed ((zeroScheme X L s).subschemeι ≫ f)
  have : IsLocallyNoetherian (zeroScheme X L s).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((zeroScheme X L s).subschemeι ≫ f)
  have : IsNoetherian (zeroScheme X L s).subscheme := ⟨⟩
  exact AlgebraicGeometry.connectedSpace_iff_of_finiteEtaleBaseChange
    (zeroScheme X L s).subschemeι
    (isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity k f L hL s hdepth hpurity
      halgebraize)

include f hL in
/-- **[Stacks, Tag 0ELE], the second conclusion.** In the situation of
`Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity`, with `X`
and `Y = Z(s)` connected, restriction induces an isomorphism of topological groups
`π₁(Y, y‾) ⟶ π₁(X, y‾)` at every geometric point `y‾` of `Y`, and that isomorphism is the
canonical induced map `AlgebraicGeometry.etaleFundamentalGroupMap`. This is [Stacks, Tag 0BQA]
part (2), the lemma the source's proof quotes for the `π₁` statement. -/
public theorem fundamentalGroupEquiv_zeroScheme_of_hasPurity
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      ((2 : ℕ) : WithBot ℕ∞) < Stacks.Algebraization.localDepthAddDimClosure X x)
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x))
    (halgebraize : ∀ A : FiniteEtaleOver (zeroScheme X L s).subscheme,
      ∃ (W : Neighborhood X (zeroScheme X L s))
        (U : FiniteEtaleOver (Neighborhood.open X (zeroScheme X L s) W).toScheme),
        Nonempty ((finiteEtaleBaseChange
          (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).obj U ≅ A))
    [ConnectedSpace (zeroScheme X L s).subscheme] [ConnectedSpace X]
    (y : AlgebraicGeometry.GeometricPoint (zeroScheme X L s).subscheme) :
    ∃ e : AlgebraicGeometry.EtaleFundamentalGroup (zeroScheme X L s).subscheme y ≃ₜ*
        AlgebraicGeometry.EtaleFundamentalGroup X (y.map (zeroScheme X L s).subschemeι),
      ∀ σ : AlgebraicGeometry.EtaleFundamentalGroup (zeroScheme X L s).subscheme y,
        e σ = AlgebraicGeometry.etaleFundamentalGroupMap
          (zeroScheme X L s).subschemeι y σ :=
  ⟨_, (AlgebraicGeometry.fundamentalGroupContinuousMulEquivOfFiniteEtaleBaseChange
      (zeroScheme X L s).subschemeι
      (isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity k f L hL s hdepth hpurity
        halgebraize) y).2⟩

/-! ### Tag 0ELE -/

include f hL in
/-- **Every finite étale cover of `Y = Z(s)` is the restriction of a finite étale cover of an open
neighbourhood of `Y`.** This is the essential-image half of [Stacks, Tag 0ELD], read off the
second half of `Stacks.FundamentalGroup.finiteEtaleColimitEquivalence_zeroScheme_of_depth`. It is
the input the source's proof of [Stacks, Tag 0ELE] takes from Tag 0ELD, and it holds at the bound
`depth(𝒪_{X, x}) + dim({x}‾) > 2` that Tag 0ELE assumes. -/
public theorem exists_finiteEtale_neighbourhood_zeroScheme_of_depth
    (hdepth : DepthAddDimGtTwoOutsideSupport X (zeroScheme X L s))
    (A : FiniteEtaleOver (zeroScheme X L s).subscheme) :
    ∃ (W : Neighborhood X (zeroScheme X L s))
      (U : FiniteEtaleOver (Neighborhood.open X (zeroScheme X L s) W).toScheme),
      Nonempty ((finiteEtaleBaseChange
        (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).obj U ≅ A) :=
  (finiteEtaleColimitEquivalence_zeroScheme_of_depth k f L
    ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mpr hL) s hdepth).2 A

include f hL in
/-- **[Stacks, Tag 0ELE], the first conclusion.** Let `k` be a field, `X` a proper scheme over
`k`, `L` an ample invertible `𝒪_X`-module, `s ∈ Γ(X, L)` and `Y = Z(s)` the zero scheme of `s`.
Assume that `depth(𝒪_{X, x}) + dim({x}‾) > 2` for every `x ∈ X ∖ Y`, and that purity holds for
`𝒪_{X, x}` at every closed `x ∈ X ∖ Y`. Then the restriction functor `FÉt_X ⟶ FÉt_Y` is an
equivalence.

The proof is the source's. Full faithfulness is
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_depthAddDim`
([Stacks, Tag 0ELC]), whose bound `> 1` follows from the bound `> 2` assumed here. For essential
surjectivity, [Stacks, Tag 0ELD] writes a given finite étale cover of `Y` as the restriction of a
finite étale cover of an open neighbourhood `V` of `Y`; every point of `X ∖ V` is a closed point
off `Y`, because its closure misses `Y` and so lies in the affine open where `s` does not vanish,
and purity therefore holds there, so [Stacks, Tag 0EY7] extends the cover from `V` to all of `X`.

The depth hypothesis is `Stacks.FundamentalGroup.DepthAddDimGtTwoOutsideSupport`, which unfolds
to the displayed inequality in the extended integers. -/
@[stacks 0ELE "first conclusion: restriction FÉt_X → FÉt_Y to the zero scheme of a section of an \
ample invertible module is an equivalence",
  sga "1 X 2.13" "more general",
  sga "2 XII 3.5" "special case"]
public theorem isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity_of_depth
    (hdepth : DepthAddDimGtTwoOutsideSupport X (zeroScheme X L s))
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x)) :
    (finiteEtaleBaseChange (zeroScheme X L s).subschemeι).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity k f L hL s
    (two_lt_localDepthAddDimClosure_of_depthAddDimGtTwoOutsideSupport hdepth) hpurity
    (exists_finiteEtale_neighbourhood_zeroScheme_of_depth k f L hL s hdepth)

include f hL in
/-- **[Stacks, Tag 0ELE], the "or equivalently".** In the situation of
`Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity_of_depth` the
zero scheme `Y = Z(s)` is connected exactly when `X` is. This is [Stacks, Tag 0BQA] part (2)
applied to the equivalence `FÉt_X ⟶ FÉt_Y`. -/
@[stacks 0ELE "the \"or equivalently\": X is connected if and only if its zero scheme Y = Z(s) is"]
public theorem connectedSpace_zeroScheme_iff_of_hasPurity_of_depth
    (hdepth : DepthAddDimGtTwoOutsideSupport X (zeroScheme X L s))
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x)) :
    ConnectedSpace (zeroScheme X L s).subscheme ↔ ConnectedSpace X :=
  connectedSpace_zeroScheme_iff_of_hasPurity k f L hL s
    (two_lt_localDepthAddDimClosure_of_depthAddDimGtTwoOutsideSupport hdepth) hpurity
    (exists_finiteEtale_neighbourhood_zeroScheme_of_depth k f L hL s hdepth)

include f hL in
/-- **[Stacks, Tag 0ELE], the second conclusion.** In the situation of
`Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_zeroScheme_of_hasPurity_of_depth`,
with `X` and `Y = Z(s)` connected, the map `π₁(Y, y‾) ⟶ π₁(X, y‾)` induced by the closed immersion
is an isomorphism of topological groups for every geometric point `y‾` of `Y`. The isomorphism
produced is the canonical induced map `AlgebraicGeometry.etaleFundamentalGroupMap`. This is
[Stacks, Tag 0BQA] part (2), the lemma the source's proof quotes for the `π₁` statement. -/
@[stacks 0ELE "second conclusion: for X, equivalently Y, connected, the induced map \
π₁(Y, y‾) → π₁(X, y‾) is an isomorphism of topological groups at every geometric point of Y",
  sga "1 X 2.13" "more general",
  sga "2 X 3.10" "special case",
  sga "2 XII 4.9" "4.9 a), special case"]
public theorem fundamentalGroupEquiv_zeroScheme_of_hasPurity_of_depth
    (hdepth : DepthAddDimGtTwoOutsideSupport X (zeroScheme X L s))
    (hpurity : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) → IsClosed ({x} : Set X) →
      AlgebraicGeometry.HasPurity (X.presheaf.stalk x))
    [ConnectedSpace (zeroScheme X L s).subscheme] [ConnectedSpace X]
    (y : AlgebraicGeometry.GeometricPoint (zeroScheme X L s).subscheme) :
    ∃ e : AlgebraicGeometry.EtaleFundamentalGroup (zeroScheme X L s).subscheme y ≃ₜ*
        AlgebraicGeometry.EtaleFundamentalGroup X (y.map (zeroScheme X L s).subschemeι),
      ∀ σ : AlgebraicGeometry.EtaleFundamentalGroup (zeroScheme X L s).subscheme y,
        e σ = AlgebraicGeometry.etaleFundamentalGroupMap
          (zeroScheme X L s).subschemeι y σ :=
  fundamentalGroupEquiv_zeroScheme_of_hasPurity k f L hL s
    (two_lt_localDepthAddDimClosure_of_depthAddDimGtTwoOutsideSupport hdepth) hpurity
    (exists_finiteEtale_neighbourhood_zeroScheme_of_depth k f L hL s hdepth) y

end Stacks.FundamentalGroup

end

end
